import LSBA.Loop.ProjField
import LSBA.Loop.WardRow
import LSBA.Kernel.Restore
import LSBA.Loop.SourceTail
import LSBA.Flow.MomentIter
import LSBA.Prop.SampleMoment
import LSBA.Prop.Increment
import LSBA.Prop.Domination
import LSBA.Flow.Comparison
import LSBA.Prop.ConeRates
import LSBA.Prop.ConeBracket
import LSBA.Prop.ConeCrude

/-!
# One node of the Step 3 cone

The right side of the recurrence (C.36) [gc:eq:recurrence] for deterministic envelopes, and the
estimate of the projected loop error at one node of the cone (C.41) [fo:eq:finite-improvement],
first as a moment bound at fixed time and then as a bound on the maximum over all words.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The right side of the recurrence (C.36) [gc:eq:recurrence] at length `n` for deterministic
envelopes: `1 + Σ_{1 ≤ j < n} E_j + ζ Σ_{2 ≤ p ≤ n} E_p E_{n+2-p} + E_1 B_{n+1} + √B_{2n+2}`,
with `E_j` the error envelopes (`|D_j| ≤ E_j ζ^j`) and `B_j` the loop envelopes
(`|ℒ_j| ≤ B_j ζ^{j-1}`). -/
def nodeEnv (n : ℕ) (Ed Bl : ℕ → ℝ) (ζ : ℝ) : ℝ :=
  1 + ∑ j ∈ Finset.Ico 1 n, Ed j + ζ * ∑ p ∈ Finset.Icc 2 n, Ed p * Ed (n + 2 - p) +
    Ed 1 * Bl (n + 1) + Real.sqrt (Bl (2 * n + 2))

/-! ### Scales -/

private lemma coneNode_gamma_pos (g : ℝ) : 0 < gammaG g := by
  unfold gammaG
  have : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  positivity

private lemma coneNode_ell_ge_one {g : ℝ} (hg : 0 ≤ g) {L : ℕ} (hL : 1 ≤ L) (u : ℝ) :
    1 ≤ ellProp g L u := by
  unfold ellProp
  refine le_min (by exact_mod_cast hL) ?_
  have : 0 ≤ g / Real.sqrt (gammaG g * (1 - u)) := div_nonneg hg (Real.sqrt_nonneg _)
  linarith

private lemma coneNode_ell_le {g : ℝ} {L : ℕ} (u : ℝ) : ellProp g L u ≤ L := min_le_left _ _

private lemma coneNode_ell_mono {g : ℝ} (hg : 0 ≤ g) (L : ℕ) {r v : ℝ} (hrv : r ≤ v)
    (hv : v < 1) : ellProp g L r ≤ ellProp g L v := by
  unfold ellProp
  refine min_le_min le_rfl ?_
  have hγ := coneNode_gamma_pos g
  have h1 : 0 < Real.sqrt (gammaG g * (1 - v)) := Real.sqrt_pos.2 (by nlinarith)
  have h2 : Real.sqrt (gammaG g * (1 - v)) ≤ Real.sqrt (gammaG g * (1 - r)) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have : g / Real.sqrt (gammaG g * (1 - r)) ≤ g / Real.sqrt (gammaG g * (1 - v)) :=
    div_le_div_of_nonneg_left hg h1 h2
  linarith

/-- `(1 - v)ℓ_v ≤ (1 - r)ℓ_r` for `r ≤ v < 1`, i.e. `ρℓ_r/ℓ_v ≥ 1`. -/
private lemma coneNode_rho_ell {g : ℝ} (hg : 0 ≤ g) {L : ℕ} (hL : 1 ≤ L) {r v : ℝ} (hrv : r ≤ v)
    (hv : v < 1) :
    1 ≤ (1 - r) / (1 - v) * ellProp g L r / ellProp g L v := by
  have hγ := coneNode_gamma_pos g
  have hℓv := coneNode_ell_ge_one hg hL v
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

/-- `γ_g Wℓ_r ζ_r = (1 - r)⁻¹`. -/
private lemma coneNode_zeta_mul {g : ℝ} (hg : 0 ≤ g) {W L : ℕ} (hW : 1 ≤ W) (hL : 1 ≤ L) {r : ℝ}
    (hr : r < 1) :
    gammaG g * W * ellProp g L r * zetaProp g W L r = (1 - r)⁻¹ := by
  have hγ := coneNode_gamma_pos g
  have hℓ := coneNode_ell_ge_one hg hL r
  have hW' : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have h1r : 0 < 1 - r := by linarith
  unfold zetaProp
  field_simp

/-- `(ρℓ_r/ℓ_v)ζ_r = ζ_v`. -/
private lemma coneNode_zeta_rho {g : ℝ} (hg : 0 ≤ g) {W L : ℕ} (hW : 1 ≤ W) (hL : 1 ≤ L)
    {r v : ℝ} (hrv : r ≤ v) (hv : v < 1) :
    (1 - r) / (1 - v) * ellProp g L r / ellProp g L v * zetaProp g W L r = zetaProp g W L v := by
  have hγ := coneNode_gamma_pos g
  have hℓr := coneNode_ell_ge_one hg hL r
  have hℓv := coneNode_ell_ge_one hg hL v
  have hW' : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have h1v : 0 < 1 - v := by linarith
  have h1r : 0 < 1 - r := by linarith
  unfold zetaProp
  field_simp

private lemma coneNode_zeta_pos {g : ℝ} (hg : 0 ≤ g) {W L : ℕ} (hW : 1 ≤ W) (hL : 1 ≤ L) {r : ℝ}
    (hr : r < 1) : 0 < zetaProp g W L r := by
  have hγ := coneNode_gamma_pos g
  have hℓ := coneNode_ell_ge_one hg hL r
  have hW' : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have h1r : 0 < 1 - r := by linarith
  unfold zetaProp
  have : 0 < (W : ℝ) * ellProp g L r * (1 - r) * gammaG g := by positivity
  positivity

/-- `ζ` is nondecreasing in time. -/
private lemma coneNode_zeta_mono {g : ℝ} (hg : 0 ≤ g) {W L : ℕ} (hW : 1 ≤ W) (hL : 1 ≤ L)
    {r v : ℝ} (hrv : r ≤ v) (hv : v < 1) : zetaProp g W L r ≤ zetaProp g W L v := by
  rw [← coneNode_zeta_rho hg hW hL hrv hv]
  have h0 := (coneNode_zeta_pos hg hW hL (lt_of_le_of_lt hrv hv)).le
  have h1 := coneNode_rho_ell hg hL hrv hv
  nlinarith

/-- `(Wη_rℓ_r)⁻¹ = ζ_r / Im m`. -/
private lemma coneNode_eta {g : ℝ} (hg : 0 ≤ g) {W L : ℕ} (hW : 1 ≤ W) (hL : 1 ≤ L) {r : ℝ}
    (hr : r < 1) (m : ℂ) (hm : 0 < m.im) :
    ((W : ℝ) * etaChar g m r * ellProp g L r)⁻¹ = zetaProp g W L r / m.im := by
  have hγ := coneNode_gamma_pos g
  have hℓ := coneNode_ell_ge_one hg hL r
  have hW' : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have h1r : 0 < 1 - r := by linarith
  unfold zetaProp etaChar
  field_simp

/-- `ζ_v ≥ (2W)⁻¹` for `L ≥ 1`, `g ≥ 0`, `v < 1`. -/
private lemma coneNode_zeta_lower {g : ℝ} (hg : 0 ≤ g) {W L : ℕ} (hW : 1 ≤ W) (hL : 1 ≤ L)
    {v : ℝ} (hv0 : 0 ≤ v) (hv : v < 1) : (2 * (W : ℝ))⁻¹ ≤ zetaProp g W L v := by
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have h1v : 0 < 1 - v := by linarith
  have h1v' : 1 - v ≤ 1 := by linarith
  have hγ := coneNode_gamma_pos g
  have hsq : 0 < Real.sqrt (gammaG g * (1 - v)) := Real.sqrt_pos.mpr (by positivity)
  have hℓ1 := coneNode_ell_ge_one hg hL v
  have hprod : ellProp g L v * (1 - v) * gammaG g ≤ 2 := by
    have hle : ellProp g L v ≤ 1 + g / Real.sqrt (gammaG g * (1 - v)) := min_le_right _ _
    have hγ1 : gammaG g ≤ 1 := by
      unfold gammaG
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_max_left _ _))
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
        (1 + g / Real.sqrt (gammaG g * (1 - v))) * (1 - v) * gammaG g := by gcongr
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

/-! ### The envelope -/

private lemma coneNode_env_parts (n : ℕ) (Ed Bl : ℕ → ℝ) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (hEd0 : ∀ j, 0 ≤ Ed j) (hBl0 : ∀ j, 0 ≤ Bl j) :
    1 ≤ nodeEnv n Ed Bl ζ ∧ (∀ j ∈ Finset.Ico 1 n, Ed j ≤ nodeEnv n Ed Bl ζ) ∧
    (∀ p ∈ Finset.Icc 2 n, ζ * (Ed p * Ed (n + 2 - p)) ≤ nodeEnv n Ed Bl ζ) ∧
    Ed 1 * Bl (n + 1) ≤ nodeEnv n Ed Bl ζ ∧ Real.sqrt (Bl (2 * n + 2)) ≤ nodeEnv n Ed Bl ζ := by
  have h1 : 0 ≤ ∑ j ∈ Finset.Ico 1 n, Ed j := Finset.sum_nonneg fun j _ => hEd0 j
  have h2 : 0 ≤ ∑ p ∈ Finset.Icc 2 n, Ed p * Ed (n + 2 - p) :=
    Finset.sum_nonneg fun p _ => mul_nonneg (hEd0 p) (hEd0 _)
  have h3 : 0 ≤ Ed 1 * Bl (n + 1) := mul_nonneg (hEd0 1) (hBl0 _)
  have h4 : 0 ≤ Real.sqrt (Bl (2 * n + 2)) := Real.sqrt_nonneg _
  have h5 := mul_nonneg hζ h2
  unfold nodeEnv
  refine ⟨by linarith, fun j hj => ?_, fun p hp => ?_, by linarith, by linarith⟩
  · have := Finset.single_le_sum (fun i _ => hEd0 i) hj
    linarith
  · have := Finset.single_le_sum (f := fun p => Ed p * Ed (n + 2 - p))
      (fun i _ => mul_nonneg (hEd0 i) (hEd0 _)) hp
    have := mul_le_mul_of_nonneg_left this hζ
    linarith


/-! ### The moment comparison with rates `K/(1 - r)` -/

private lemma coneNode_sqrt3 {a X Y : ℝ} (ha : 0 ≤ a) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    Real.sqrt (a ^ 2 + X + Y) ≤ a + Real.sqrt X + Real.sqrt Y := by
  have hsX := Real.sq_sqrt hX
  have hsY := Real.sq_sqrt hY
  have h1 := Real.sqrt_nonneg X
  have h2 := Real.sqrt_nonneg Y
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [mul_nonneg ha h1, mul_nonneg ha h2, mul_nonneg h1 h2]

private lemma coneNode_integral_inv {s u : ℝ} (hsu : s ≤ u) (hu : u < 1) :
    ∫ r in s..u, (1 - r)⁻¹ = Real.log ((1 - s) / (1 - u)) := by
  have h := intervalIntegral.integral_comp_sub_left (fun x : ℝ => x⁻¹) (a := s) (b := u) 1
  rw [h, integral_inv_of_pos (by linarith) (by linarith)]

/-- The moment comparison on `[s, u]` with the rates `β = K_β/(1 - r)` and `b₀ = K_b/(1 - r)`. -/
private lemma coneNode_engine {ι : Type*} [Fintype ι] (σ2 : ℝ) (hσ2 : 0 ≤ σ2)
    (Y : ℝ → (ι → ℝ) → ℂ) {s u : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) (hu : u < 1)
    (hY : HeatClass Y (-1 / 2) ((u + 1) / 2)) (p : ℕ) (hp : 1 ≤ p) {K δb Kβ Kb : ℝ} (hK : 0 ≤ K)
    (hδb : 0 ≤ δb) (hKβ : 0 ≤ Kβ) (hKb : 0 ≤ Kb) (Bad : ℝ → Set (ι → ℝ))
    (hbad : ∀ r ∈ Set.Ioo s u,
      stdGauss ι {x | Real.sqrt (r * σ2) • x ∈ Bad r} ≤ ENNReal.ofReal δb)
    (hrate : ∀ r ∈ Set.Ioo s u, ∀ y, y ∉ Bad r →
      ‖coordGen σ2 Y r y‖ ≤ Kβ / (1 - r) ∧ ‖coordGamma σ2 (Y r) (Y r) y‖ ≤ Kb / (1 - r))
    (hcrude : ∀ r ∈ Set.Ioo s u,
      ∫ x, ‖coordGen σ2 Y r (Real.sqrt (r * σ2) • x)‖ ^ (4 * p) ∂(stdGauss ι) ≤ K ^ (4 * p) ∧
      ∫ x, ‖coordGamma σ2 (Y r) (Y r) (Real.sqrt (r * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι) ≤
        K ^ (2 * p)) :
    (∫ x, ‖Y u (Real.sqrt (u * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι)) ^ (1 / (2 * (p : ℝ))) ≤
      (∫ x, ‖Y s (Real.sqrt (s * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι)) ^ (1 / (2 * (p : ℝ))) +
        Real.sqrt ((2 * p - 1) * (Kb * Real.log ((1 - s) / (1 - u)))) +
        Real.sqrt ((2 * p - 1) * (K * δb ^ (1 / (2 * (p : ℝ))))) +
        Kβ * Real.log ((1 - s) / (1 - u)) + K * δb ^ (1 / (4 * (p : ℝ))) := by
  have hcont : ∀ c : ℝ, ContinuousOn (fun r : ℝ => c / (1 - r)) (Set.Icc s u) := by
    intro c
    refine continuousOn_const.div (continuousOn_const.sub continuousOn_id) fun r hr => ?_
    have : r ≤ u := hr.2
    linarith
  have hnn : ∀ c : ℝ, 0 ≤ c → ∀ r ∈ Set.Icc s u, 0 ≤ c / (1 - r) := fun c hc r hr =>
    div_nonneg hc (by linarith [hr.2])
  have hM := momentIter_step' σ2 hσ2 Y (a := -1 / 2) (b := (u + 1) / 2) (by norm_num) hs hsu
    (by linarith) hY p hp hK hδb (fun r => Kβ / (1 - r)) (fun r => Kb / (1 - r)) (hcont Kβ)
    (hcont Kb) (hnn Kβ hKβ) (hnn Kb hKb) Bad hbad hrate hcrude
  set Lg := Real.log ((1 - s) / (1 - u)) with hLg
  have hLg0 : 0 ≤ Lg := Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  have hint : ∀ (c d : ℝ), ∫ r in s..u, (c / (1 - r) + d) = c * Lg + d * (u - s) := by
    intro c d
    have hi1 : IntervalIntegrable (fun r : ℝ => c / (1 - r)) MeasureTheory.volume s u :=
      (hcont c).intervalIntegrable_of_Icc hsu
    rw [intervalIntegral.integral_add hi1 intervalIntegrable_const, intervalIntegral.integral_const,
      smul_eq_mul]
    have : ∫ r in s..u, c / (1 - r) = c * ∫ r in s..u, (1 - r)⁻¹ := by
      rw [← intervalIntegral.integral_const_mul]
      rfl
    rw [this, coneNode_integral_inv hsu hu]
    ring
  rw [hint, hint] at hM
  set Is := ∫ x, ‖Y s (Real.sqrt (s * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι) with hIs
  have hIs0 : 0 ≤ Is := integral_nonneg fun x => by positivity
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hsq : Is ^ (1 / (p : ℝ)) = (Is ^ (1 / (2 * (p : ℝ)))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hIs0]
    congr 1
    push_cast
    field_simp
  rw [hsq] at hM
  have hd2 : 0 ≤ K * δb ^ (1 / (2 * (p : ℝ))) := mul_nonneg hK (Real.rpow_nonneg hδb _)
  have hd4 : 0 ≤ K * δb ^ (1 / (4 * (p : ℝ))) := mul_nonneg hK (Real.rpow_nonneg hδb _)
  have h2p : (0 : ℝ) ≤ 2 * p - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hus : u - s ≤ 1 := by linarith
  have hus0 : 0 ≤ u - s := by linarith
  refine hM.trans ?_
  have e1 : (2 * (p : ℝ) - 1) * (Kb * Lg + K * δb ^ (1 / (2 * (p : ℝ))) * (u - s)) ≤
      (2 * p - 1) * (Kb * Lg) + (2 * p - 1) * (K * δb ^ (1 / (2 * (p : ℝ)))) := by
    have : K * δb ^ (1 / (2 * (p : ℝ))) * (u - s) ≤ K * δb ^ (1 / (2 * (p : ℝ))) :=
      mul_le_of_le_one_right hd2 hus
    nlinarith
  have hs1 : Real.sqrt ((Is ^ (1 / (2 * (p : ℝ)))) ^ 2 +
      (2 * p - 1) * (Kb * Lg + K * δb ^ (1 / (2 * (p : ℝ))) * (u - s))) ≤
      Is ^ (1 / (2 * (p : ℝ))) + Real.sqrt ((2 * p - 1) * (Kb * Lg)) +
        Real.sqrt ((2 * p - 1) * (K * δb ^ (1 / (2 * (p : ℝ))))) := by
    refine (Real.sqrt_le_sqrt (show _ ≤ (Is ^ (1 / (2 * (p : ℝ)))) ^ 2 +
      (2 * p - 1) * (Kb * Lg) + (2 * p - 1) * (K * δb ^ (1 / (2 * (p : ℝ)))) by linarith)).trans ?_
    exact coneNode_sqrt3 (Real.rpow_nonneg hIs0 _) (mul_nonneg h2p (mul_nonneg hKb hLg0))
      (mul_nonneg h2p hd2)
  have hs2 : Kβ * Lg + K * δb ^ (1 / (4 * (p : ℝ))) * (u - s) ≤
      Kβ * Lg + K * δb ^ (1 / (4 * (p : ℝ))) := by
    have : K * δb ^ (1 / (4 * (p : ℝ))) * (u - s) ≤ K * δb ^ (1 / (4 * (p : ℝ))) :=
      mul_le_of_le_one_right hd4 hus
    linarith
  linarith


/-! ### Normalization of the rates -/

/-- The source part of the rates of the propagated fields at a good sample: with
`X_j ≤ PE_jζ^j`, `κ_j ≤ Pζ^{j-1}`, `Y ≤ PB_{n+2}ζ^{n+1}` and `γWℓζ = (1 - r)⁻¹`, the sources are
at most `(1 - r)⁻¹ζ^{n+1}P²(2(n + 1) + 1)` times the envelope. -/
private lemma coneNode_src_le (n : ℕ) (hn : 1 ≤ n) (Ed Bl X κ : ℕ → ℝ) (γWℓ ζ ζt P Y r : ℝ)
    (_hr : r < 1) (hγ : γWℓ * ζ = (1 - r)⁻¹) (hγ0 : 0 ≤ γWℓ) (hζ : 0 ≤ ζ) (hζt : ζ ≤ ζt)
    (hP : 1 ≤ P) (hEd0 : ∀ j, 0 ≤ Ed j) (hBl0 : ∀ j, 0 ≤ Bl j)
    (hX0 : ∀ j, 0 ≤ X j) (hX : ∀ j, 1 ≤ j → j ≤ n + 1 → X j ≤ P * (Ed j * ζ ^ j))
    (_hκ0 : ∀ j, 0 ≤ κ j) (hκ : ∀ j, 3 ≤ j → j ≤ n + 1 → κ j ≤ P * ζ ^ (j - 1))
    (hY0 : 0 ≤ Y) (hY : Y ≤ P * (Bl (n + 1 + 1) * ζ ^ (n + 1))) :
    γWℓ * (X 1 * Y + ∑ p ∈ Finset.Icc 3 (n + 1), κ p * X (n + 3 - p) +
        ∑ p ∈ Finset.Icc 2 (n + 1), X p * X (n + 3 - p)) ≤
      (1 - r)⁻¹ * ζ ^ (n + 1) * P ^ 2 * ((2 * (n + 1) + 1) * nodeEnv (n + 1) Ed Bl ζt) := by
  have hζt0 : 0 ≤ ζt := hζ.trans hζt
  obtain ⟨-, hlin, hquad, hlight, -⟩ := coneNode_env_parts (n + 1) Ed Bl ζt hζt0 hEd0 hBl0
  set Env := nodeEnv (n + 1) Ed Bl ζt with hEnv
  have hP0 : 0 ≤ P := by linarith
  have hZ : 0 ≤ P ^ 2 * ζ ^ (n + 2) := by positivity
  -- each term is at most `P²ζ^{n+2} Env`
  have ha : X 1 * Y ≤ P ^ 2 * ζ ^ (n + 2) * Env := by
    have h1 := hX 1 le_rfl (by omega)
    calc X 1 * Y ≤ (P * (Ed 1 * ζ ^ 1)) * (P * (Bl (n + 1 + 1) * ζ ^ (n + 1))) :=
          mul_le_mul h1 hY hY0 (mul_nonneg hP0 (mul_nonneg (hEd0 _) (pow_nonneg hζ _)))
      _ = P ^ 2 * ζ ^ (n + 2) * (Ed 1 * Bl (n + 1 + 1)) := by ring
      _ ≤ P ^ 2 * ζ ^ (n + 2) * Env := mul_le_mul_of_nonneg_left hlight hZ
  have hb : ∀ p ∈ Finset.Icc 3 (n + 1), κ p * X (n + 3 - p) ≤ P ^ 2 * ζ ^ (n + 2) * Env := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_Icc.1 hp
    have h1 := hκ p hp1 hp2
    have h2 := hX (n + 3 - p) (by omega) (by omega)
    have hq : n + 3 - p ∈ Finset.Ico 1 (n + 1) := Finset.mem_Ico.2 ⟨by omega, by omega⟩
    calc κ p * X (n + 3 - p) ≤ (P * ζ ^ (p - 1)) * (P * (Ed (n + 3 - p) * ζ ^ (n + 3 - p))) :=
          mul_le_mul h1 h2 (hX0 _) (mul_nonneg hP0 (pow_nonneg hζ _))
      _ = P ^ 2 * (ζ ^ (p - 1) * ζ ^ (n + 3 - p)) * Ed (n + 3 - p) := by ring
      _ = P ^ 2 * ζ ^ (n + 2) * Ed (n + 3 - p) := by
          rw [← pow_add, show p - 1 + (n + 3 - p) = n + 2 by omega]
      _ ≤ P ^ 2 * ζ ^ (n + 2) * Env := mul_le_mul_of_nonneg_left (hlin _ hq) hZ
  have hc : ∀ p ∈ Finset.Icc 2 (n + 1), X p * X (n + 3 - p) ≤ P ^ 2 * ζ ^ (n + 2) * Env := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_Icc.1 hp
    have h1 := hX p (by omega) hp2
    have h2 := hX (n + 3 - p) (by omega) (by omega)
    have hq := hquad p hp
    rw [show n + 1 + 2 - p = n + 3 - p by omega] at hq
    calc X p * X (n + 3 - p) ≤ (P * (Ed p * ζ ^ p)) * (P * (Ed (n + 3 - p) * ζ ^ (n + 3 - p))) :=
          mul_le_mul h1 h2 (hX0 _) (mul_nonneg hP0 (mul_nonneg (hEd0 _) (pow_nonneg hζ _)))
      _ = P ^ 2 * (ζ ^ p * ζ ^ (n + 3 - p)) * (Ed p * Ed (n + 3 - p)) := by ring
      _ = P ^ 2 * ζ ^ (n + 2) * (ζ * (Ed p * Ed (n + 3 - p))) := by
          rw [← pow_add, show p + (n + 3 - p) = n + 2 + 1 by omega, pow_succ]; ring
      _ ≤ P ^ 2 * ζ ^ (n + 2) * (ζt * (Ed p * Ed (n + 3 - p))) := by
          gcongr
          exact mul_nonneg (hEd0 _) (hEd0 _)
      _ ≤ P ^ 2 * ζ ^ (n + 2) * Env := mul_le_mul_of_nonneg_left hq hZ
  have hsb := Finset.sum_le_sum hb
  have hsc := Finset.sum_le_sum hc
  rw [Finset.sum_const, nsmul_eq_mul] at hsb hsc
  have hcb : ((Finset.Icc 3 (n + 1)).card : ℝ) ≤ n + 1 := by
    rw [Nat.card_Icc]; push_cast
    have : ((n + 1 + 1 - 3 : ℕ) : ℝ) ≤ n + 1 := by exact_mod_cast (by omega : n + 1 + 1 - 3 ≤ n + 1)
    exact this
  have hcc : ((Finset.Icc 2 (n + 1)).card : ℝ) ≤ n + 1 := by
    rw [Nat.card_Icc]
    exact_mod_cast (by omega : n + 1 + 1 - 2 ≤ n + 1)
  have hEnv0 : 0 ≤ P ^ 2 * ζ ^ (n + 2) * Env := by
    have := (coneNode_env_parts (n + 1) Ed Bl ζt hζt0 hEd0 hBl0).1
    positivity
  have hsum : X 1 * Y + ∑ p ∈ Finset.Icc 3 (n + 1), κ p * X (n + 3 - p) +
      ∑ p ∈ Finset.Icc 2 (n + 1), X p * X (n + 3 - p) ≤
      (2 * (n + 1) + 1) * (P ^ 2 * ζ ^ (n + 2) * Env) := by
    have e1 := mul_le_mul_of_nonneg_right hcb hEnv0
    have e2 := mul_le_mul_of_nonneg_right hcc hEnv0
    nlinarith
  calc γWℓ * (X 1 * Y + ∑ p ∈ Finset.Icc 3 (n + 1), κ p * X (n + 3 - p) +
        ∑ p ∈ Finset.Icc 2 (n + 1), X p * X (n + 3 - p)) ≤
      γWℓ * ((2 * (n + 1) + 1) * (P ^ 2 * ζ ^ (n + 2) * Env)) :=
        mul_le_mul_of_nonneg_left hsum hγ0
    _ = (γWℓ * ζ) * ζ ^ (n + 1) * P ^ 2 * ((2 * (n + 1) + 1) * Env) := by ring
    _ = _ := by rw [hγ]

/-- The commutator part of the rate of the projected field: `X_n ζ/((1 - r) Im m)`. -/
private lemma coneNode_comm_le (n : ℕ) (hn : 1 ≤ n) (Ed Bl : ℕ → ℝ) (Xn ζ ζt P r im RC : ℝ)
    (hr : r < 1) (hζ : 0 ≤ ζ) (hζt : ζ ≤ ζt) (hP : 1 ≤ P) (him : 0 < im) (hRC : im⁻¹ ≤ RC)
    (hEd0 : ∀ j, 0 ≤ Ed j) (hBl0 : ∀ j, 0 ≤ Bl j) (_hX0 : 0 ≤ Xn) (hX : Xn ≤ P * (Ed n * ζ ^ n)) :
    Xn * (ζ / im) * (1 - r)⁻¹ ≤
      (1 - r)⁻¹ * ζ ^ (n + 1) * P ^ 2 * (RC * nodeEnv (n + 1) Ed Bl ζt) := by
  have hζt0 : 0 ≤ ζt := hζ.trans hζt
  obtain ⟨-, hlin, -, -, -⟩ := coneNode_env_parts (n + 1) Ed Bl ζt hζt0 hEd0 hBl0
  have hEn := hlin n (Finset.mem_Ico.2 ⟨hn, by omega⟩)
  have h1r : 0 < (1 - r)⁻¹ := inv_pos.2 (by linarith)
  have hP0 : 0 ≤ P := by linarith
  have hRC0 : 0 ≤ RC := (inv_pos.2 him).le.trans hRC
  have hEdn := hEd0 n
  have hζim : ζ / im ≤ ζ * RC := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hRC hζ
  have hB0 : 0 ≤ P * (Ed n * ζ ^ n) := by positivity
  calc Xn * (ζ / im) * (1 - r)⁻¹ ≤ (P * (Ed n * ζ ^ n)) * (ζ * RC) * (1 - r)⁻¹ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul hX hζim (div_nonneg hζ him.le) hB0) h1r.le
    _ = (1 - r)⁻¹ * ζ ^ (n + 1) * P * (RC * Ed n) := by ring
    _ ≤ (1 - r)⁻¹ * ζ ^ (n + 1) * P ^ 2 * (RC * nodeEnv (n + 1) Ed Bl ζt) := by
        have h1 : P ≤ P ^ 2 := by nlinarith
        have h2 : RC * Ed n ≤ RC * nodeEnv (n + 1) Ed Bl ζt := mul_le_mul_of_nonneg_left hEn hRC0
        have h3 : 0 ≤ (1 - r)⁻¹ * ζ ^ (n + 1) := by positivity
        have h4 : 0 ≤ RC * Ed n := mul_nonneg hRC0 hEdn
        calc (1 - r)⁻¹ * ζ ^ (n + 1) * P * (RC * Ed n) ≤
            (1 - r)⁻¹ * ζ ^ (n + 1) * P ^ 2 * (RC * Ed n) := by gcongr
          _ ≤ _ := by gcongr

/-- The tail part of the rates: `γWLτ(Σ_j X_j + Σ_j κ_j) + τζ/((1 - r) Im m) ≤
(1 - r)⁻¹τ T_c`. -/
private lemma coneNode_tail_le (n : ℕ) (X κ : ℕ → ℝ) (γWL ζ Zc Xc P r im RC τ : ℝ)
    (hr0 : 0 ≤ r) (hr : r < 1) (hζ : 0 ≤ ζ) (hZc : ζ ≤ Zc) (hZ1 : 1 ≤ Zc) (hP : 1 ≤ P)
    (him : 0 < im) (hRC : im⁻¹ ≤ RC) (hτ : 0 ≤ τ) (hγ : 0 ≤ γWL)
    (hX0 : ∀ j, 0 ≤ X j) (hX : ∀ j, 1 ≤ j → j ≤ n + 1 → X j ≤ Xc)
    (_hκ0 : ∀ j, 0 ≤ κ j) (hκ : ∀ j, 3 ≤ j → j ≤ n + 1 → κ j ≤ P * ζ ^ (j - 1)) :
    γWL * τ * (∑ j ∈ Finset.Icc 1 (n + 1), X j + ∑ j ∈ Finset.Icc 3 (n + 1), κ j) +
        τ * (ζ / im) * (1 - r)⁻¹ ≤
      (1 - r)⁻¹ * τ * (γWL * ((n + 1) * (Xc + P * Zc ^ (n + 1))) + RC * Zc) := by
  have h1r : 1 ≤ (1 - r)⁻¹ := one_le_inv₀ (by linarith) |>.2 (by linarith)
  have hRC0 : 0 ≤ RC := (inv_pos.2 him).le.trans hRC
  have hP0 : 0 ≤ P := by linarith
  have hXc0 : 0 ≤ Xc := (hX0 1).trans (hX 1 le_rfl (by omega))
  have hs1 : ∑ j ∈ Finset.Icc 1 (n + 1), X j ≤ (n + 1) * Xc := by
    have := Finset.sum_le_sum fun j (hj : j ∈ Finset.Icc 1 (n + 1)) =>
      hX j (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc] at this
    simpa using this
  have hs2 : ∑ j ∈ Finset.Icc 3 (n + 1), κ j ≤ (n + 1) * (P * Zc ^ (n + 1)) := by
    have : ∀ j ∈ Finset.Icc 3 (n + 1), κ j ≤ P * Zc ^ (n + 1) := by
      intro j hj
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
      refine (hκ j h1 h2).trans (mul_le_mul_of_nonneg_left ?_ hP0)
      calc ζ ^ (j - 1) ≤ Zc ^ (j - 1) := pow_le_pow_left₀ hζ hZc _
        _ ≤ Zc ^ (n + 1) := pow_le_pow_right₀ hZ1 (by omega)
    have h := Finset.sum_le_sum this
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact_mod_cast (by omega : n + 1 + 1 - 3 ≤ n + 1)
  have hζim : ζ / im ≤ RC * Zc := by
    rw [div_eq_mul_inv, mul_comm]
    exact mul_le_mul hRC hZc hζ hRC0
  have hA : 0 ≤ γWL * ((n + 1) * (Xc + P * Zc ^ (n + 1))) := by positivity
  calc γWL * τ * (∑ j ∈ Finset.Icc 1 (n + 1), X j + ∑ j ∈ Finset.Icc 3 (n + 1), κ j) +
        τ * (ζ / im) * (1 - r)⁻¹ ≤
      γWL * τ * ((n + 1) * Xc + (n + 1) * (P * Zc ^ (n + 1))) + τ * (RC * Zc) * (1 - r)⁻¹ := by
        gcongr
    _ = τ * (γWL * ((n + 1) * (Xc + P * Zc ^ (n + 1)))) + τ * (RC * Zc) * (1 - r)⁻¹ := by ring
    _ ≤ τ * (γWL * ((n + 1) * (Xc + P * Zc ^ (n + 1)))) * (1 - r)⁻¹ +
        τ * (RC * Zc) * (1 - r)⁻¹ := by
        have := mul_le_mul_of_nonneg_left h1r (mul_nonneg hτ hA)
        linarith
    _ = _ := by ring


/-! ### Kernel premises of the rates -/

/-- Bulk bound of the kernel from the profile (6.3) [fo:eq:kernel-bounds]. -/
private lemma coneNode_ker_bulk {C c A K r ℓ δ : ℝ} {W : ℕ} (hW : 1 ≤ W) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hr0 : 0 ≤ r) (hr : r < 1) (hℓ : 1 ≤ ℓ) (hcδ : 0 ≤ c * δ)
    (hK : K ≤ C / ((1 - r) * ℓ) * Real.exp (-(c * δ / ℓ)) + ℓ⁻¹ * (W : ℝ) ^ (-A)) :
    K ≤ (C + 1) / ((1 - r) * ℓ) := by
  have h1r : 0 < 1 - r := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have he : Real.exp (-(c * δ / ℓ)) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : 0 ≤ c * δ / ℓ := div_nonneg hcδ hℓ0.le
    linarith)
  have hWA : (W : ℝ) ^ (-A) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hW) (by linarith)
  have h2 : ℓ⁻¹ * (W : ℝ) ^ (-A) ≤ 1 / ((1 - r) * ℓ) := by
    rw [inv_mul_eq_div, div_le_div_iff₀ hℓ0 (by positivity)]
    have : 0 ≤ (W : ℝ) ^ (-A) := Real.rpow_nonneg (by positivity) _
    have h' : (1 - r) * ℓ ≤ ℓ := by nlinarith
    calc (W : ℝ) ^ (-A) * ((1 - r) * ℓ) ≤ 1 * ℓ :=
          mul_le_mul hWA h' (by positivity) (by norm_num)
      _ = 1 * ℓ := rfl
  have h3 : C / ((1 - r) * ℓ) * Real.exp (-(c * δ / ℓ)) ≤ C / ((1 - r) * ℓ) :=
    mul_le_of_le_one_right (by positivity) he
  calc K ≤ _ := hK
    _ ≤ C / ((1 - r) * ℓ) + 1 / ((1 - r) * ℓ) := add_le_add h3 h2
    _ = (C + 1) / ((1 - r) * ℓ) := by ring

/-- Far bound of the kernel from the profile (6.3) [fo:eq:kernel-bounds]. -/
private lemma coneNode_ker_far {C c A K r ℓ δ H : ℝ} {W : ℕ} (hW : 1 ≤ W) (hC : 0 ≤ C) (hc : 0 < c)
    (hr0 : 0 ≤ r) (hr : r < 1) (hℓ : 1 ≤ ℓ) (hfar : H * ℓ / 4 < δ)
    (hK : K ≤ C / ((1 - r) * ℓ) * Real.exp (-(c * δ / ℓ)) + ℓ⁻¹ * (W : ℝ) ^ (-A)) :
    K ≤ (C * Real.exp (-(c * H / 4)) + (W : ℝ) ^ (-A)) / ((1 - r) * ℓ) := by
  have h1r : 0 < 1 - r := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have he : Real.exp (-(c * δ / ℓ)) ≤ Real.exp (-(c * H / 4)) := by
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    rw [le_div_iff₀ hℓ0]
    have : H * ℓ / 4 ≤ δ := hfar.le
    nlinarith
  have hWA : 0 ≤ (W : ℝ) ^ (-A) := Real.rpow_nonneg (by positivity) _
  have h2 : ℓ⁻¹ * (W : ℝ) ^ (-A) ≤ (W : ℝ) ^ (-A) / ((1 - r) * ℓ) := by
    rw [inv_mul_eq_div, div_le_div_iff₀ hℓ0 (by positivity)]
    have h' : (1 - r) * ℓ ≤ ℓ := by nlinarith
    exact mul_le_mul_of_nonneg_left h' hWA
  calc K ≤ _ := hK
    _ ≤ C / ((1 - r) * ℓ) * Real.exp (-(c * H / 4)) + (W : ℝ) ^ (-A) / ((1 - r) * ℓ) :=
        add_le_add (mul_le_mul_of_nonneg_left he (by positivity)) h2
    _ = _ := by ring

/-- `Ξ = (v - r)K_v ≤ (C + 1)ρ/ℓ_v` from the profile (6.3) [fo:eq:kernel-bounds] at `v`. -/
private lemma coneNode_xi {C c A K r v ℓ δ : ℝ} {W : ℕ} (hW : 1 ≤ W) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hrv : r ≤ v) (hv : v < 1) (hr : 0 ≤ r) (hℓ : 1 ≤ ℓ) (hcδ : 0 ≤ c * δ)
    (hK : K ≤ C / ((1 - v) * ℓ) * Real.exp (-(c * δ / ℓ)) + ℓ⁻¹ * (W : ℝ) ^ (-A)) :
    (v - r) * K ≤ (C + 1) * ((1 - r) / (1 - v)) / ℓ := by
  have h1v : 0 < 1 - v := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hb := coneNode_ker_bulk (r := v) hW hA hC (by linarith) hv hℓ hcδ hK
  have hvr : 0 ≤ v - r := by linarith
  calc (v - r) * K ≤ (v - r) * ((C + 1) / ((1 - v) * ℓ)) := mul_le_mul_of_nonneg_left hb hvr
    _ ≤ (1 - r) * ((C + 1) / ((1 - v) * ℓ)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (C + 1) * ((1 - r) / (1 - v)) / ℓ := by field_simp

/-- The increment premise of the restoration for `Ξ = (v - r)K_v`. -/
private lemma coneNode_xi_inc {Ci A K K' r v ℓu ℓv δ : ℝ} {W : ℕ} (hW : 1 ≤ W) (hA : 0 ≤ A)
    (hCi : 0 ≤ Ci) (hrv : r ≤ v) (hv : v < 1) (hr : 0 ≤ r) (hℓu : 1 ≤ ℓu) (hℓv : 1 ≤ ℓv)
    (hρℓ : 1 ≤ (1 - r) / (1 - v) * ℓu / ℓv) (hδ : 0 ≤ δ)
    (hK : |K - K'| ≤ Ci / ((1 - v) * ℓv) * (δ / ℓv) + ℓv⁻¹ * (W : ℝ) ^ (-A)) :
    |(v - r) * K - (v - r) * K'| ≤ (Ci + 1) * ((1 - r) / (1 - v)) / ℓv * ((δ + ℓu) / ℓv) := by
  have h1v : 0 < 1 - v := by linarith
  have hℓv0 : 0 < ℓv := by linarith
  have hvr : 0 ≤ v - r := by linarith
  have hWA : (W : ℝ) ^ (-A) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hW) (by linarith)
  have hWA0 : 0 ≤ (W : ℝ) ^ (-A) := Real.rpow_nonneg (by positivity) _
  set ρ := (1 - r) / (1 - v) with hρ
  have hρ1 : 1 ≤ ρ := by rw [hρ, le_div_iff₀ h1v]; linarith
  have hvrρ : v - r ≤ ρ * (1 - v) := by rw [hρ, div_mul_cancel₀ _ h1v.ne']; linarith
  have hℓvρ : ℓv ≤ ρ * ℓu := by
    have := hρℓ; rw [le_div_iff₀ hℓv0, one_mul] at this; linarith
  rw [← mul_sub, abs_mul, abs_of_nonneg hvr]
  calc (v - r) * |K - K'| ≤ (v - r) * (Ci / ((1 - v) * ℓv) * (δ / ℓv) + ℓv⁻¹ * (W : ℝ) ^ (-A)) :=
        mul_le_mul_of_nonneg_left hK hvr
    _ ≤ Ci * ρ * δ / ℓv ^ 2 + ρ * ℓu / ℓv ^ 2 := by
        have e1 : (v - r) * (Ci / ((1 - v) * ℓv) * (δ / ℓv)) =
            Ci * ((v - r) / (1 - v)) * δ / ℓv ^ 2 := by
          field_simp
        have e2 : (v - r) / (1 - v) ≤ ρ := by
          rw [div_le_iff₀ h1v]; linarith
        have t1 : Ci * ((v - r) / (1 - v)) * δ / ℓv ^ 2 ≤ Ci * ρ * δ / ℓv ^ 2 := by
          gcongr
        have t2 : (v - r) * (ℓv⁻¹ * (W : ℝ) ^ (-A)) ≤ ρ * ℓu / ℓv ^ 2 := by
          have : (v - r) * (ℓv⁻¹ * (W : ℝ) ^ (-A)) ≤ 1 * ℓv⁻¹ :=
            mul_le_mul (by linarith : v - r ≤ 1) (mul_le_of_le_one_right (by positivity) hWA)
              (by positivity) (by norm_num)
          calc _ ≤ 1 * ℓv⁻¹ := this
            _ = ℓv / ℓv ^ 2 := by field_simp
            _ ≤ ρ * ℓu / ℓv ^ 2 := by gcongr
        rw [mul_add, e1]; exact add_le_add t1 t2
    _ ≤ (Ci + 1) * ρ / ℓv * ((δ + ℓu) / ℓv) := by
        rw [show (Ci + 1) * ρ / ℓv * ((δ + ℓu) / ℓv) =
          ((Ci + 1) * ρ * δ + (Ci + 1) * ρ * ℓu) / ℓv ^ 2 by field_simp]
        rw [← add_div]
        have hρ0 : 0 ≤ ρ := by linarith
        gcongr
        · nlinarith [mul_nonneg hρ0 hδ, mul_nonneg hCi hρ0]
        · nlinarith

local notation "𝐦[" q "]" => mRoot (StepPt.g q) (StepPt.L q) (StepPt.E q)
local notation "𝐌[" q "]" =>
  dysonMat (hopB (StepPt.g q)) (gammaG (StepPt.g q)) (StepPt.L q) (StepPt.E q) (𝐦[q])
local notation "𝐏[" q "]" => pairP (gammaG (StepPt.g q)) (𝐌[q])

/-- The kernel premises of the deterministic rates at one `W`: from the kernel profile (6.3)
[fo:eq:kernel-bounds] at `q.at r` and `q.at v` and the increment bound of `IncrementInput` at
`q.at v`. -/
private lemma coneNode_kernel_premises (R : PropRegime) (Ci : ℝ) (hCi : 0 < Ci) (W : ℕ) (q : StepPt)
    (r v A H : ℝ) (hW : 1 ≤ W) (hA : 0 < A) (hr : 1 / 2 ≤ r) (hrv : r ≤ v) (hv1 : v < 1)
    (hL : 3 ≤ q.L) (hg : 0 ≤ q.g)
    (hKr : ∀ x y, 0 ≤ mixedKer 𝐏[q] r x y ∧ mixedKer 𝐏[q] r x y ≤
      R.C / ((1 - r) * ellProp q.g q.L r) * Real.exp (-(R.c * cycDist x y / ellProp q.g q.L r)) +
        (ellProp q.g q.L r)⁻¹ * (W : ℝ) ^ (-A))
    (hKv : ∀ x y, 0 ≤ mixedKer 𝐏[q] v x y ∧ mixedKer 𝐏[q] v x y ≤
      R.C / ((1 - v) * ellProp q.g q.L v) * Real.exp (-(R.c * cycDist x y / ellProp q.g q.L v)) +
        (ellProp q.g q.L v)⁻¹ * (W : ℝ) ^ (-A))
    (hIv : ∀ x y y', |mixedKer 𝐏[q] v x y - mixedKer 𝐏[q] v x y'| ≤
      Ci / ((1 - v) * ellProp q.g q.L v) * ((cycDist y y' : ℝ) / ellProp q.g q.L v) +
        (ellProp q.g q.L v)⁻¹ * (W : ℝ) ^ (-A)) :
    (∀ x y, mixedKer 𝐏[q] r x y ≤ (R.C + 1) / ((1 - r) * ellProp q.g q.L r)) ∧
    (∀ x y, H * ellProp q.g q.L r / 4 < cycDist x y → mixedKer 𝐏[q] r x y ≤
      (R.C * Real.exp (-(R.c * H / 4)) + (W : ℝ) ^ (-A)) / ((1 - r) * ellProp q.g q.L r)) ∧
    (∀ x y, (v - r) * mixedKer 𝐏[q] v x y ≤
      (R.C + Ci + 1) * ((1 - r) / (1 - v)) / ellProp q.g q.L v) ∧
    (∀ x y y', |(v - r) * mixedKer 𝐏[q] v x y - (v - r) * mixedKer 𝐏[q] v x y'| ≤
      (R.C + Ci + 1) * ((1 - r) / (1 - v)) / ellProp q.g q.L v *
        (((cycDist y y' : ℝ) + ellProp q.g q.L r) / ellProp q.g q.L v)) := by
  have hr0 : 0 ≤ r := by linarith
  have hL1 : 1 ≤ q.L := by omega
  have hℓr := coneNode_ell_ge_one hg hL1 r
  have hℓv := coneNode_ell_ge_one hg hL1 v
  have hC0 : 0 ≤ R.C := by linarith [R.one_le_C]
  have hc := R.c_pos
  have h1v : 0 < 1 - v := by linarith
  have hρ0 : 0 ≤ (1 - r) / (1 - v) := div_nonneg (by linarith) h1v.le
  refine ⟨fun x y => ?_, fun x y hxy => ?_, fun x y => ?_, fun x y y' => ?_⟩
  · exact coneNode_ker_bulk hW hA.le hC0 hr0 (by linarith) hℓr
      (mul_nonneg hc.le (Nat.cast_nonneg _)) (hKr x y).2
  · exact coneNode_ker_far hW hC0 hc hr0 (by linarith) hℓr hxy (hKr x y).2
  · refine (coneNode_xi hW hA.le hC0 hrv hv1 hr0 hℓv (mul_nonneg hc.le (Nat.cast_nonneg _))
      (hKv x y).2).trans ?_
    gcongr
    linarith
  · refine (coneNode_xi_inc hW hA.le hCi.le hrv hv1 hr0 hℓr hℓv
      (coneNode_rho_ell hg hL1 hrv hv1) (Nat.cast_nonneg _) (hIv x y y')).trans ?_
    gcongr
    linarith [R.one_le_C]


/-! ### Rates at a good sample -/

/-- The bound `K_β` of the generator rates, `β = K_β/(1 - r)`. -/
private def coneNode_Kβ (n : ℕ) (Cn RC H P Pm ζu Env Tc τ : ℝ) : ℝ :=
  Cn * ((H ^ (2 * (n + 1)) + 1) * ζu ^ (n + 1) * P ^ 2 * ((2 * (n + 1) + 1 + RC) * Env)) +
    Cn * Pm ^ (4 * (n + 1)) * (τ * Tc)

/-- The bound `K_b` of the bracket rates, `b₀ = K_b/(1 - r)`. -/
private def coneNode_Kb (n : ℕ) (Cn H P Pm ζu B₂ γWL τ : ℝ) : ℝ :=
  Cn * ((H ^ (4 * (n + 1)) + 1) * ζu ^ (2 * (n + 1)) * (P * B₂)) +
    Cn * Pm ^ (8 * (n + 1)) * (γWL * τ)

private lemma coneNode_pref (m a b : ℕ) (H x P τθ ζ ζu : ℝ) (hx : x * ζ = ζu) (hζ : 0 ≤ ζ)
    (hζu : ζ ≤ ζu) (_hP : 0 ≤ P) (_hτθ : 0 ≤ τθ) (hPm : P ^ b * τθ ≤ 1) :
    (H ^ a * x ^ m + P ^ b * τθ) * ζ ^ m ≤ (H ^ a + 1) * ζu ^ m := by
  have h1 : x ^ m * ζ ^ m = ζu ^ m := by rw [← mul_pow, hx]
  have h2 : ζ ^ m ≤ ζu ^ m := pow_le_pow_left₀ hζ hζu m
  have h3 : P ^ b * τθ * ζ ^ m ≤ ζu ^ m := by
    have := mul_le_mul_of_nonneg_right hPm (pow_nonneg hζ m)
    linarith
  calc (H ^ a * x ^ m + P ^ b * τθ) * ζ ^ m = H ^ a * (x ^ m * ζ ^ m) + P ^ b * τθ * ζ ^ m := by
        ring
    _ ≤ H ^ a * ζu ^ m + ζu ^ m := by rw [h1]; linarith
    _ = (H ^ a + 1) * ζu ^ m := by ring

private lemma coneNode_pref_stable (k : ℕ) (hk : 1 ≤ k) (x ζ ζu : ℝ) (hx : x * ζ = ζu)
    (hζ : 0 ≤ ζ) (hζu : ζ ≤ ζu) : x ^ (k - 1) * ζ ^ k ≤ ζu ^ k := by
  obtain ⟨k, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ ζ, ← mul_assoc, ← mul_pow, hx, pow_succ]
  exact mul_le_mul_of_nonneg_left hζu (pow_nonneg (hζ.trans hζu) _)

set_option maxHeartbeats 1000000 in -- one long composed estimate per word type
/-- The rates of `momentIter_step'` for the propagated projected field (C.35)
[fo:eq:projected-error-equation] of a cyclically alternating word of length `n + 1` at a good
sample at time `r`: the generator is at most `K_β/(1 - r)` and the bracket at most `K_b/(1 - r)`. -/
private lemma coneNode_rate_proj (R : PropRegime) (n : ℕ) (hn : 1 ≤ n) (Ci : ℝ) (hCi : 0 < Ci) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (W : ℕ) (q : StepPt) (r Ak ν τ Xc Zc Pm : ℝ) (ω : Ω W q.L)
      (σ : Fin (n + 1) → Bool) (a : Fin (n + 1) → Fin q.L) (Ed Bl : ℕ → ℝ),
      1 ≤ W → 0 < Ak → 0 < ν → 0 ≤ τ → 1 / 2 ≤ r → r ≤ q.u → q.u ≤ q.t → q.t < 1 →
      (∀ j, σ (finRotate (n + 1) j) = !σ j) →
      3 ≤ q.L → 0 ≤ q.g → IsDysonRootV (hopB q.g) (gammaG q.g) q.L q.E 𝐦[q] →
      R.C⁻¹ ≤ (𝐦[q]).im →
      (∀ x y, 0 ≤ mixedKer 𝐏[q] r x y ∧ mixedKer 𝐏[q] r x y ≤
        R.C / ((1 - r) * ellProp q.g q.L r) * Real.exp (-(R.c * cycDist x y / ellProp q.g q.L r)) +
          (ellProp q.g q.L r)⁻¹ * (W : ℝ) ^ (-Ak)) →
      (∀ x y, 0 ≤ mixedKer 𝐏[q] q.u x y ∧ mixedKer 𝐏[q] q.u x y ≤
        R.C / ((1 - q.u) * ellProp q.g q.L q.u) *
          Real.exp (-(R.c * cycDist x y / ellProp q.g q.L q.u)) +
          (ellProp q.g q.L q.u)⁻¹ * (W : ℝ) ^ (-Ak)) →
      (∀ x y y', |mixedKer 𝐏[q] q.u x y - mixedKer 𝐏[q] q.u x y'| ≤
        Ci / ((1 - q.u) * ellProp q.g q.L q.u) * ((cycDist y y' : ℝ) / ellProp q.g q.L q.u) +
          (ellProp q.g q.L q.u)⁻¹ * (W : ℝ) ^ (-Ak)) →
      (4 * (W : ℝ) ^ ν + 2) * (1 + (1 - r) / (1 - q.u)) * (q.L / ellProp q.g q.L r) ≤ Pm →
      1 ≤ Pm →
      Pm ^ (8 * (n + 1)) * (R.C * Real.exp (-(R.c * (4 * (W : ℝ) ^ ν + 2) / 4)) +
        (W : ℝ) ^ (-Ak)) ≤ 1 →
      zetaProp q.g W q.L r ≤ Zc → 1 ≤ Zc → 0 ≤ Xc →
      (∀ j, 0 ≤ Ed j) → (∀ j, 0 ≤ Bl j) →
      (∀ j, 1 ≤ j → j ≤ n + 1 → ∀ w : Word j q.L,
        ‖flowErr W (q.at r) w.1 w.2 ω‖ ≤ (W : ℝ) ^ ν * (Ed j * zetaProp q.g W q.L r ^ j)) →
      (∀ j, 1 ≤ j → j ≤ n + 1 → ∀ w : Word j q.L, ‖flowErr W (q.at r) w.1 w.2 ω‖ ≤ Xc) →
      (∀ w : Word (n + 1 + 1) q.L, ‖loopTr (flowG W (q.at r) ω) w.1 w.2‖ ≤
        (W : ℝ) ^ ν * (Bl (n + 1 + 1) * zetaProp q.g W q.L r ^ (n + 1 + 1 - 1))) →
      (∀ w : Word (2 * (n + 1) + 2) q.L, ‖loopTr (flowG W (q.at r) ω) w.1 w.2‖ ≤
        (W : ℝ) ^ ν * (Bl (2 * (n + 1) + 2) * zetaProp q.g W q.L r ^ (2 * (n + 1) + 2 - 1))) →
      (∀ k, 2 ≤ k → k ≤ 2 * (n + 1) + 2 → ∀ w : Word k q.L,
        (W : ℝ) ^ ν * ellProp q.g q.L r < wordDiam w.1 →
          ‖loopTr (flowG W (q.at r) ω) w.1 w.2‖ + ‖flowErr W (q.at r) w.1 w.2 ω‖ ≤ τ) →
      (∀ j, 2 ≤ j → j ≤ 2 * (n + 1) + 2 → ∀ (b : Fin j → Fin q.L) (s : Fin j → Bool),
        ‖primLoop q.g W q.L q.E 𝐦[q] r b s‖ ≤ (W : ℝ) ^ ν * zetaProp q.g W q.L r ^ (j - 1)) →
      (∀ j, 2 ≤ j → j ≤ 2 * (n + 1) + 2 → ∀ (b : Fin j → Fin q.L) (s : Fin j → Bool),
        (W : ℝ) ^ ν * ellProp q.g q.L r < wordDiam b → ‖primLoop q.g W q.L q.E 𝐦[q] r b s‖ ≤ τ) →
      ‖blockGen W q.L (gammaG q.g) (fun r' N => ∑ b, projCoef 𝐏[q] q.u r' a b *
          (resLoop q.g q.E 𝐦[q] b σ r' N - primLoop q.g W q.L q.E 𝐦[q] r' b σ)) r
          (flowH q.g W q.L r ω)‖ ≤
        coneNode_Kβ n Cn R.C (4 * (W : ℝ) ^ ν + 2) ((W : ℝ) ^ ν) Pm (zetaProp q.g W q.L q.u)
          (nodeEnv (n + 1) Ed Bl (zetaProp q.g W q.L q.t))
          (gammaG q.g * W * q.L * ((n + 1) * (Xc + (W : ℝ) ^ ν * Zc ^ (n + 1))) + R.C * Zc) τ /
          (1 - r) ∧
      ‖blockGamma W q.L (gammaG q.g)
          (fun N => ∑ b, projCoef 𝐏[q] q.u r a b *
            (resLoop q.g q.E 𝐦[q] b σ r N - primLoop q.g W q.L q.E 𝐦[q] r b σ))
          (fun N => ∑ b, projCoef 𝐏[q] q.u r a b *
            (resLoop q.g q.E 𝐦[q] b σ r N - primLoop q.g W q.L q.E 𝐦[q] r b σ))
          (flowH q.g W q.L r ω)‖ ≤
        coneNode_Kb n Cn (4 * (W : ℝ) ^ ν + 2) ((W : ℝ) ^ ν) Pm (zetaProp q.g W q.L q.u)
          (Bl (2 * (n + 1) + 2)) (gammaG q.g * W * q.L) τ / (1 - r) := by
  obtain ⟨Cn₁, hCn₁, h₁⟩ := coneRates_genProj n hn (R.C + Ci + 1) (R.C + 1)
    (by linarith [R.one_le_C]) (by linarith [R.one_le_C])
  obtain ⟨Cn₂, hCn₂, h₂⟩ := coneBracket_proj n hn (R.C + Ci + 1) (R.C + 1)
    (by linarith [R.one_le_C]) (by linarith [R.one_le_C])
  refine ⟨max Cn₁ Cn₂, lt_max_of_lt_left hCn₁, ?_⟩
  intro W q r Ak ν τ Xc Zc Pm ω σ a Ed Bl hW hAk hν hτ hr hru hut ht1 hσ hL hg hm hmim hKr hKv
    hIv hPm hPm1 hτθ hZc hZc1 hXc0 hEd0 hBl0 hX hXc hY hY2 hT hκ hκτ
  have hu1 : q.u < 1 := lt_of_le_of_lt hut ht1
  have hr1 : r < 1 := lt_of_le_of_lt hru hu1
  have hr0 : 0 ≤ r := by linarith
  have hL1 : 1 ≤ q.L := by omega
  have hRC := R.one_le_C
  have hmpos : 0 < (𝐦[q]).im := lt_of_lt_of_le (by positivity) hmim
  have him : ((𝐦[q]).im)⁻¹ ≤ R.C := by
    rw [inv_le_comm₀ hmpos (by positivity)]; exact hmim
  set ℓr := ellProp q.g q.L r with hℓr
  set ℓu := ellProp q.g q.L q.u with hℓu
  set ζr := zetaProp q.g W q.L r with hζr
  set ζu := zetaProp q.g W q.L q.u with hζu
  set ζt := zetaProp q.g W q.L q.t with hζt
  set P := (W : ℝ) ^ ν with hP
  set H := 4 * P + 2 with hH
  set ρ := (1 - r) / (1 - q.u) with hρ
  set τθ := R.C * Real.exp (-(R.c * H / 4)) + (W : ℝ) ^ (-Ak) with hτθdef
  have hℓr1 := coneNode_ell_ge_one hg hL1 r
  have hP1 : 1 ≤ P := Real.one_le_rpow (by exact_mod_cast hW) hν.le
  have hH1 : 1 ≤ H := by linarith
  have hζr0 : 0 ≤ ζr := (coneNode_zeta_pos hg hW hL1 hr1).le
  have hζru : ζr ≤ ζu := coneNode_zeta_mono hg hW hL1 hru hu1
  have hζrt : ζr ≤ ζt := coneNode_zeta_mono hg hW hL1 (hru.trans hut) ht1
  have hρℓ := coneNode_rho_ell hg hL1 hru hu1
  have hxζ : ρ * ℓr / ℓu * ζr = ζu := coneNode_zeta_rho hg hW hL1 hru hu1
  have hγζ : gammaG q.g * W * ℓr * ζr = (1 - r)⁻¹ := coneNode_zeta_mul hg hW hL1 hr1
  have hη : ((W : ℝ) * etaChar q.g 𝐦[q] r * ℓr)⁻¹ = ζr / (𝐦[q]).im :=
    coneNode_eta hg hW hL1 hr1 _ hmpos
  have hτθ0 : 0 ≤ τθ := by
    have := Real.exp_pos (-(R.c * H / 4))
    have := Real.rpow_nonneg (Nat.cast_nonneg W) (-Ak)
    positivity
  have h𝔓0 : 0 ≤ H * (1 + ρ) * (q.L / ℓr) := by
    have : 0 ≤ ρ := div_nonneg (by linarith) (by linarith)
    positivity
  have hPm0 : 0 ≤ Pm := by linarith
  have h𝔓 : ∀ e : ℕ, (H * (1 + ρ) * (q.L / ℓr)) ^ e ≤ Pm ^ e := fun e =>
    pow_le_pow_left₀ h𝔓0 hPm _
  have hPme : ∀ e e' : ℕ, e ≤ e' → Pm ^ e ≤ Pm ^ e' := fun e e' h => pow_le_pow_right₀ hPm1 h
  have hτθ8 : (H * (1 + ρ) * (q.L / ℓr)) ^ (8 * (n + 1)) * τθ ≤ 1 :=
    (mul_le_mul_of_nonneg_right (h𝔓 _) hτθ0).trans hτθ
  have hτθ4 : (H * (1 + ρ) * (q.L / ℓr)) ^ (4 * (n + 1)) * τθ ≤ 1 :=
    (mul_le_mul_of_nonneg_right ((h𝔓 _).trans (hPme _ _ (by omega))) hτθ0).trans hτθ
  have hτθ1 : τθ ≤ 1 := by
    have : 1 ≤ Pm ^ (8 * (n + 1)) := one_le_pow₀ hPm1
    nlinarith
  obtain ⟨k1, k2, k3, k4⟩ := coneNode_kernel_premises R Ci hCi W q r q.u Ak H hW hAk hr hru hu1
    hL hg hKr hKv hIv
  -- the sample sizes
  set X : ℕ → ℝ := fun j => min (P * (Ed j * ζr ^ j)) Xc with hXdef
  set κ : ℕ → ℝ := fun j => P * ζr ^ (j - 1) with hκdef
  have hX0 : ∀ j, 0 ≤ X j := fun j =>
    le_min (mul_nonneg (by linarith) (mul_nonneg (hEd0 j) (pow_nonneg hζr0 _))) hXc0
  have hκ0 : ∀ j, 0 ≤ κ j := fun j => mul_nonneg (by linarith) (pow_nonneg hζr0 _)
  have hXs : ∀ j, 1 ≤ j → j ≤ n + 1 → ∀ (b : Fin j → Fin q.L) (s : Fin j → Bool),
      ‖loopTr (resolventMat (flowH q.g W q.L r ω) (zChar q.g q.E 𝐦[q] r)) b s -
        primLoop q.g W q.L q.E 𝐦[q] r b s‖ ≤ X j :=
    fun j h1 h2 b s => le_min (hX j h1 h2 (b, s)) (hXc j h1 h2 (b, s))
  have hd0 : 0 ≤ P * ℓr := by positivity
  have h4d : 4 * (P * ℓr) + 2 ≤ H * ℓr := by nlinarith
  have hYn := fun b s => hY (b, s)
  simp only [Nat.add_sub_cancel] at hYn
  -- generator
  have hG := h₁ q.g q.E 𝐦[q] W q.L hW hL hm r q.u (flowH q.g W q.L r ω)
    (flowH_isHermitian _ _ _ _ _) σ hσ a X κ (P * (Bl (n + 1 + 1) * ζr ^ (n + 1))) ρ ℓr ℓu H
    (P * ℓr) τ τθ hr0 hru hu1 le_rfl hℓr1 (coneNode_ell_mono hg q.L hru hu1) (coneNode_ell_le r)
    hH1 hρℓ hd0 h4d hτ hτθ0 hτθ1 k1 k2 k3 k4 hXs
    (fun j h1 h2 b s hb => (le_add_of_nonneg_left (norm_nonneg _)).trans
      (hT j h1 (by omega) (b, s) hb))
    (fun j h1 h2 b s => hκ j (by omega) (by omega) b s)
    (fun j h1 h2 b s hb => hκτ j (by omega) (by omega) b s hb)
    hYn
    (fun b s hb => (le_add_of_nonneg_right (norm_nonneg _)).trans
      (hT (n + 1 + 1) (by omega) (by omega) (b, s) hb))
  -- bracket
  have hB := h₂ q.g q.E 𝐦[q] W q.L hW hL hm r q.u (flowH q.g W q.L r ω)
    (flowH_isHermitian _ _ _ _ _) σ a
    (P * (Bl (2 * (n + 1) + 2) * ζr ^ (2 * (n + 1) + 2 - 1))) ρ ℓr ℓu H (P * ℓr) τ τθ hr0 hru hu1
    le_rfl hℓr1 (coneNode_ell_mono hg q.L hru hu1) (coneNode_ell_le r) hH1 hρℓ hd0 h4d hτ hτθ0
    hτθ1 k1 k2 k3 k4 (fun b s => hY2 (b, s))
    (fun b s hb => (le_add_of_nonneg_right (norm_nonneg _)).trans
      (hT (2 * (n + 1) + 2) (by omega) le_rfl (b, s) hb))
  have h1r : 0 < 1 - r := by linarith
  have h1r' : 0 < (1 - r)⁻¹ := inv_pos.2 h1r
  have hγWℓ0 : 0 ≤ gammaG q.g * W * ℓr := by
    have := coneNode_gamma_pos q.g
    positivity
  have hζu0 : 0 ≤ ζu := hζr0.trans hζru
  have hEnv1 := (coneNode_env_parts (n + 1) Ed Bl ζt (hζr0.trans hζrt) hEd0 hBl0).1
  have hCnm : 0 ≤ max Cn₁ Cn₂ := le_trans hCn₁.le (le_max_left _ _)
  have hcomm : X n / ((1 - r) * (W * etaChar q.g 𝐦[q] r) * ℓr) =
      X n * (ζr / (𝐦[q]).im) * (1 - r)⁻¹ := by
    rw [← hη]; field_simp
  have hcommτ : τ / ((1 - r) * (W * etaChar q.g 𝐦[q] r) * ℓr) =
      τ * (ζr / (𝐦[q]).im) * (1 - r)⁻¹ := by
    rw [← hη]; field_simp
  rw [hcomm, hcommτ] at hG
  refine ⟨?_, ?_⟩
  · refine hG.trans ?_
    -- the source and commutator part
    have hS1 := coneNode_src_le n hn Ed Bl X κ (gammaG q.g * W * ℓr) ζr ζt P
      (P * (Bl (n + 1 + 1) * ζr ^ (n + 1))) r hr1 hγζ hγWℓ0 hζr0 hζrt hP1 hEd0 hBl0 hX0
      (fun j _ _ => min_le_left _ _) hκ0 (fun j _ _ => le_rfl)
      (mul_nonneg (by linarith) (mul_nonneg (hBl0 _) (pow_nonneg hζr0 _))) le_rfl
    have hS2 := coneNode_comm_le n hn Ed Bl (X n) ζr ζt P r (𝐦[q]).im R.C hr1 hζr0 hζrt hP1
      hmpos him hEd0 hBl0 (hX0 n) (min_le_left _ _)
    set E := (2 * (n + 1) + 1 + R.C) * nodeEnv (n + 1) Ed Bl ζt with hE
    have hS : gammaG q.g * W * ℓr * (X 1 * (P * (Bl (n + 1 + 1) * ζr ^ (n + 1))) +
          ∑ p ∈ Finset.Icc 3 (n + 1), κ p * X (n + 3 - p) +
          ∑ p ∈ Finset.Icc 2 (n + 1), X p * X (n + 3 - p)) +
          X n * (ζr / (𝐦[q]).im) * (1 - r)⁻¹ ≤ (1 - r)⁻¹ * ζr ^ (n + 1) * P ^ 2 * E := by
      have : (1 - r)⁻¹ * ζr ^ (n + 1) * P ^ 2 * E =
          (1 - r)⁻¹ * ζr ^ (n + 1) * P ^ 2 * ((2 * (n + 1) + 1) * nodeEnv (n + 1) Ed Bl ζt) +
          (1 - r)⁻¹ * ζr ^ (n + 1) * P ^ 2 * (R.C * nodeEnv (n + 1) Ed Bl ζt) := by
        rw [hE]; ring
      rw [this]
      exact add_le_add hS1 hS2
    -- the tail part
    have hγWL0 : 0 ≤ gammaG q.g * W * q.L := by
      have := coneNode_gamma_pos q.g
      positivity
    have hXc' : ∀ j, 1 ≤ j → j ≤ n + 1 → X j ≤ Xc := fun j _ _ => min_le_right _ _
    have hκ' : ∀ j, 3 ≤ j → j ≤ n + 1 → κ j ≤ P * ζr ^ (j - 1) := fun j _ _ => le_rfl
    have hT1 := coneNode_tail_le n X κ (gammaG q.g * W * q.L) ζr Zc Xc P r (𝐦[q]).im R.C τ hr0
      hr1 hζr0 hZc hZc1 hP1 hmpos him hτ hγWL0 hX0 hXc' hκ0 hκ'
    have hpre := coneNode_pref (n + 1) (2 * (n + 1)) (4 * (n + 1)) H (ρ * ℓr / ℓu)
      (H * (1 + ρ) * (q.L / ℓr)) τθ ζr ζu hxζ hζr0 hζru h𝔓0 hτθ0 hτθ4
    set Tc := gammaG q.g * W * q.L * ((n + 1) * (Xc + P * Zc ^ (n + 1))) + R.C * Zc with hTc
    have hE0 : 0 ≤ E := by positivity
    have hpf0 : 0 ≤ H ^ (2 * (n + 1)) * (ρ * ℓr / ℓu) ^ (n + 1) +
        (H * (1 + ρ) * (q.L / ℓr)) ^ (4 * (n + 1)) * τθ := by
      have : 0 ≤ ρ * ℓr / ℓu := by linarith
      positivity
    have hTc0 : 0 ≤ Tc := by
      have : 0 ≤ Zc := by linarith
      positivity
    have hmain := calc Cn₁ * (H ^ (2 * (n + 1)) * (ρ * ℓr / ℓu) ^ (n + 1) +
          (H * (1 + ρ) * (q.L / ℓr)) ^ (4 * (n + 1)) * τθ) *
          (gammaG q.g * W * ℓr * (X 1 * (P * (Bl (n + 1 + 1) * ζr ^ (n + 1))) +
          ∑ p ∈ Finset.Icc 3 (n + 1), κ p * X (n + 3 - p) +
          ∑ p ∈ Finset.Icc 2 (n + 1), X p * X (n + 3 - p)) +
          X n * (ζr / (𝐦[q]).im) * (1 - r)⁻¹) ≤
        Cn₁ * (H ^ (2 * (n + 1)) * (ρ * ℓr / ℓu) ^ (n + 1) +
          (H * (1 + ρ) * (q.L / ℓr)) ^ (4 * (n + 1)) * τθ) *
          ((1 - r)⁻¹ * ζr ^ (n + 1) * P ^ 2 * E) :=
          mul_le_mul_of_nonneg_left hS (mul_nonneg hCn₁.le hpf0)
      _ = Cn₁ * ((H ^ (2 * (n + 1)) * (ρ * ℓr / ℓu) ^ (n + 1) +
          (H * (1 + ρ) * (q.L / ℓr)) ^ (4 * (n + 1)) * τθ) * ζr ^ (n + 1)) *
          (P ^ 2 * E * (1 - r)⁻¹) := by ring
      _ ≤ Cn₁ * ((H ^ (2 * (n + 1)) + 1) * ζu ^ (n + 1)) * (P ^ 2 * E * (1 - r)⁻¹) := by
          gcongr
      _ ≤ max Cn₁ Cn₂ * ((H ^ (2 * (n + 1)) + 1) * ζu ^ (n + 1)) * (P ^ 2 * E * (1 - r)⁻¹) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
            (mul_nonneg (by positivity) (pow_nonneg hζu0 _))) (by positivity)
    have htail := calc Cn₁ * (H * (1 + ρ) * (q.L / ℓr)) ^ (4 * (n + 1)) *
          (gammaG q.g * W * q.L * τ *
          (∑ j ∈ Finset.Icc 1 (n + 1), X j + ∑ j ∈ Finset.Icc 3 (n + 1), κ j) +
          τ * (ζr / (𝐦[q]).im) * (1 - r)⁻¹) ≤
        Cn₁ * (H * (1 + ρ) * (q.L / ℓr)) ^ (4 * (n + 1)) * ((1 - r)⁻¹ * τ * Tc) :=
          mul_le_mul_of_nonneg_left hT1 (mul_nonneg hCn₁.le (pow_nonneg h𝔓0 _))
      _ ≤ max Cn₁ Cn₂ * Pm ^ (4 * (n + 1)) * ((1 - r)⁻¹ * τ * Tc) :=
          mul_le_mul_of_nonneg_right (mul_le_mul (le_max_left _ _) (h𝔓 _) (pow_nonneg h𝔓0 _)
            hCnm) (by positivity)
    unfold coneNode_Kβ
    have e1 : (max Cn₁ Cn₂ * ((H ^ (2 * (n + 1)) + 1) * ζu ^ (n + 1) * P ^ 2 * E) +
        max Cn₁ Cn₂ * Pm ^ (4 * (n + 1)) * (τ * Tc)) / (1 - r) =
        max Cn₁ Cn₂ * ((H ^ (2 * (n + 1)) + 1) * ζu ^ (n + 1)) * (P ^ 2 * E * (1 - r)⁻¹) +
        max Cn₁ Cn₂ * Pm ^ (4 * (n + 1)) * ((1 - r)⁻¹ * τ * Tc) := by ring
    rw [e1]
    exact add_le_add hmain htail
  · refine hB.trans ?_
    have hY₂ : gammaG q.g * W * ℓr * (P * (Bl (2 * (n + 1) + 2) * ζr ^ (2 * (n + 1) + 2 - 1))) =
        (1 - r)⁻¹ * (P * Bl (2 * (n + 1) + 2)) * ζr ^ (2 * (n + 1)) := by
      rw [show 2 * (n + 1) + 2 - 1 = 2 * (n + 1) + 1 by omega, pow_succ, ← hγζ]; ring
    rw [hY₂]
    have hpre := coneNode_pref (2 * (n + 1)) (4 * (n + 1)) (8 * (n + 1)) H (ρ * ℓr / ℓu)
      (H * (1 + ρ) * (q.L / ℓr)) τθ ζr ζu hxζ hζr0 hζru h𝔓0 hτθ0 hτθ8
    have hB0 : 0 ≤ P * Bl (2 * (n + 1) + 2) := mul_nonneg (by linarith) (hBl0 _)
    have hγWL : 0 ≤ gammaG q.g * W * q.L * τ := by
      have := coneNode_gamma_pos q.g
      positivity
    have h1r1 : 1 ≤ (1 - r)⁻¹ := (one_le_inv₀ h1r).2 (by linarith)
    unfold coneNode_Kb
    have hb1 := calc Cn₂ * (H ^ (4 * (n + 1)) * (ρ * ℓr / ℓu) ^ (2 * (n + 1)) +
            (H * (1 + ρ) * (q.L / ℓr)) ^ (8 * (n + 1)) * τθ) *
            ((1 - r)⁻¹ * (P * Bl (2 * (n + 1) + 2)) * ζr ^ (2 * (n + 1))) =
          Cn₂ * ((H ^ (4 * (n + 1)) * (ρ * ℓr / ℓu) ^ (2 * (n + 1)) +
            (H * (1 + ρ) * (q.L / ℓr)) ^ (8 * (n + 1)) * τθ) * ζr ^ (2 * (n + 1))) *
            ((1 - r)⁻¹ * (P * Bl (2 * (n + 1) + 2))) := by ring
        _ ≤ Cn₂ * ((H ^ (4 * (n + 1)) + 1) * ζu ^ (2 * (n + 1))) *
            ((1 - r)⁻¹ * (P * Bl (2 * (n + 1) + 2))) := by gcongr
        _ ≤ max Cn₁ Cn₂ * ((H ^ (4 * (n + 1)) + 1) * ζu ^ (2 * (n + 1))) *
            ((1 - r)⁻¹ * (P * Bl (2 * (n + 1) + 2))) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _)
              (mul_nonneg (by positivity) (pow_nonneg hζu0 _))) (mul_nonneg h1r'.le hB0)
    have hb2a : Cn₂ * (H * (1 + ρ) * ((q.L : ℝ) / ℓr)) ^ (8 * (n + 1)) *
        (gammaG q.g * (W : ℝ) * (q.L : ℝ) * τ) ≤
        max Cn₁ Cn₂ * Pm ^ (8 * (n + 1)) * (gammaG q.g * (W : ℝ) * (q.L : ℝ) * τ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul (le_max_right _ _) (h𝔓 _) (pow_nonneg h𝔓0 _)
        hCnm) hγWL
    have hb2b : max Cn₁ Cn₂ * Pm ^ (8 * (n + 1)) * (gammaG q.g * (W : ℝ) * (q.L : ℝ) * τ) ≤
        max Cn₁ Cn₂ * Pm ^ (8 * (n + 1)) * (gammaG q.g * (W : ℝ) * (q.L : ℝ) * τ) * (1 - r)⁻¹ :=
      le_mul_of_one_le_right (by positivity) h1r1
    have e1 : (max Cn₁ Cn₂ * ((H ^ (4 * (n + 1)) + 1) * ζu ^ (2 * (n + 1)) *
        (P * Bl (2 * (n + 1) + 2))) +
        max Cn₁ Cn₂ * Pm ^ (8 * (n + 1)) * (gammaG q.g * W * q.L * τ)) / (1 - r) =
        max Cn₁ Cn₂ * ((H ^ (4 * (n + 1)) + 1) * ζu ^ (2 * (n + 1))) *
            ((1 - r)⁻¹ * (P * Bl (2 * (n + 1) + 2))) +
        max Cn₁ Cn₂ * Pm ^ (8 * (n + 1)) * (gammaG q.g * W * q.L * τ) * (1 - r)⁻¹ := by ring
    rw [e1]
    exact add_le_add hb1 (hb2a.trans hb2b)


set_option maxHeartbeats 1000000 in -- one long composed estimate per word type
/-- The rates of `momentIter_step'` for the propagated field of a word of length `n + 1` with a
stable leg at a good sample at time `r`: the generator is at most `K_β/(1 - r)` and the bracket at
most `K_b/(1 - r)`. -/
private lemma coneNode_rate_stable (R : PropRegime) (n : ℕ) (hn : 1 ≤ n) (Ci : ℝ) (hCi : 0 < Ci) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (W : ℕ) (q : StepPt) (r Ak ν τ Xc Zc Pm : ℝ) (ω : Ω W q.L)
      (σ : Fin (n + 1) → Bool) (a : Fin (n + 1) → Fin q.L) (Ed Bl : ℕ → ℝ),
      1 ≤ W → 0 < Ak → 0 < ν → 0 ≤ τ → 1 / 2 ≤ r → r ≤ q.u → q.u ≤ q.t → q.t < 1 →
      (∃ j, σ (finRotate (n + 1) j) = σ j) →
      3 ≤ q.L → 0 ≤ q.g → IsDysonRootV (hopB q.g) (gammaG q.g) q.L q.E 𝐦[q] →
      R.C⁻¹ ≤ (𝐦[q]).im →
      (∀ a, gammaG q.g * ∑ b, (‖𝐌[q] a b‖ + ‖𝐌[q] a b‖ ^ 2) ≤ R.C) →
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ a, ∑ b, ‖(1 - (u : ℂ) • pairQ (gammaG q.g) 𝐌[q])⁻¹ a b‖ ≤ R.C) →
      (∀ x y, 0 ≤ mixedKer 𝐏[q] r x y ∧ mixedKer 𝐏[q] r x y ≤
        R.C / ((1 - r) * ellProp q.g q.L r) * Real.exp (-(R.c * cycDist x y / ellProp q.g q.L r)) +
          (ellProp q.g q.L r)⁻¹ * (W : ℝ) ^ (-Ak)) →
      (∀ x y, 0 ≤ mixedKer 𝐏[q] q.u x y ∧ mixedKer 𝐏[q] q.u x y ≤
        R.C / ((1 - q.u) * ellProp q.g q.L q.u) *
          Real.exp (-(R.c * cycDist x y / ellProp q.g q.L q.u)) +
          (ellProp q.g q.L q.u)⁻¹ * (W : ℝ) ^ (-Ak)) →
      (∀ x y y', |mixedKer 𝐏[q] q.u x y - mixedKer 𝐏[q] q.u x y'| ≤
        Ci / ((1 - q.u) * ellProp q.g q.L q.u) * ((cycDist y y' : ℝ) / ellProp q.g q.L q.u) +
          (ellProp q.g q.L q.u)⁻¹ * (W : ℝ) ^ (-Ak)) →
      (4 * (W : ℝ) ^ ν + 2) * (1 + (1 - r) / (1 - q.u)) * (q.L / ellProp q.g q.L r) ≤ Pm →
      1 ≤ Pm →
      zetaProp q.g W q.L r ≤ Zc → 1 ≤ Zc → 0 ≤ Xc →
      (∀ j, 0 ≤ Ed j) → (∀ j, 0 ≤ Bl j) →
      (∀ j, 1 ≤ j → j ≤ n + 1 → ∀ w : Word j q.L,
        ‖flowErr W (q.at r) w.1 w.2 ω‖ ≤ (W : ℝ) ^ ν * (Ed j * zetaProp q.g W q.L r ^ j)) →
      (∀ j, 1 ≤ j → j ≤ n + 1 → ∀ w : Word j q.L, ‖flowErr W (q.at r) w.1 w.2 ω‖ ≤ Xc) →
      (∀ w : Word (n + 1 + 1) q.L, ‖loopTr (flowG W (q.at r) ω) w.1 w.2‖ ≤
        (W : ℝ) ^ ν * (Bl (n + 1 + 1) * zetaProp q.g W q.L r ^ (n + 1 + 1 - 1))) →
      (∀ w : Word (2 * (n + 1) + 2) q.L, ‖loopTr (flowG W (q.at r) ω) w.1 w.2‖ ≤
        (W : ℝ) ^ ν * (Bl (2 * (n + 1) + 2) * zetaProp q.g W q.L r ^ (2 * (n + 1) + 2 - 1))) →
      (∀ k, 2 ≤ k → k ≤ 2 * (n + 1) + 2 → ∀ w : Word k q.L,
        (W : ℝ) ^ ν * ellProp q.g q.L r < wordDiam w.1 →
          ‖loopTr (flowG W (q.at r) ω) w.1 w.2‖ + ‖flowErr W (q.at r) w.1 w.2 ω‖ ≤ τ) →
      (∀ j, 2 ≤ j → j ≤ 2 * (n + 1) + 2 → ∀ (b : Fin j → Fin q.L) (s : Fin j → Bool),
        ‖primLoop q.g W q.L q.E 𝐦[q] r b s‖ ≤ (W : ℝ) ^ ν * zetaProp q.g W q.L r ^ (j - 1)) →
      (∀ j, 2 ≤ j → j ≤ 2 * (n + 1) + 2 → ∀ (b : Fin j → Fin q.L) (s : Fin j → Bool),
        (W : ℝ) ^ ν * ellProp q.g q.L r < wordDiam b → ‖primLoop q.g W q.L q.E 𝐦[q] r b s‖ ≤ τ) →
      ‖blockGen W q.L (gammaG q.g) (fun r' N => ∑ b : Fin (n + 1) → Fin q.L,
          (∏ j, pairU (gammaG q.g) 𝐌[q] r' q.u (σ j) (σ (finRotate (n + 1) j)) (a j) (b j)) *
          (resLoop q.g q.E 𝐦[q] b σ r' N - primLoop q.g W q.L q.E 𝐦[q] r' b σ)) r
          (flowH q.g W q.L r ω)‖ ≤
        coneNode_Kβ n Cn R.C (4 * (W : ℝ) ^ ν + 2) ((W : ℝ) ^ ν) Pm (zetaProp q.g W q.L q.u)
          (nodeEnv (n + 1) Ed Bl (zetaProp q.g W q.L q.t))
          (gammaG q.g * W * q.L * ((n + 1) * (Xc + (W : ℝ) ^ ν * Zc ^ (n + 1))) + R.C * Zc) τ /
          (1 - r) ∧
      ‖blockGamma W q.L (gammaG q.g)
          (fun N => ∑ b : Fin (n + 1) → Fin q.L,
            (∏ j, pairU (gammaG q.g) 𝐌[q] r q.u (σ j) (σ (finRotate (n + 1) j)) (a j) (b j)) *
            (resLoop q.g q.E 𝐦[q] b σ r N - primLoop q.g W q.L q.E 𝐦[q] r b σ))
          (fun N => ∑ b : Fin (n + 1) → Fin q.L,
            (∏ j, pairU (gammaG q.g) 𝐌[q] r q.u (σ j) (σ (finRotate (n + 1) j)) (a j) (b j)) *
            (resLoop q.g q.E 𝐦[q] b σ r N - primLoop q.g W q.L q.E 𝐦[q] r b σ))
          (flowH q.g W q.L r ω)‖ ≤
        coneNode_Kb n Cn (4 * (W : ℝ) ^ ν + 2) ((W : ℝ) ^ ν) Pm (zetaProp q.g W q.L q.u)
          (Bl (2 * (n + 1) + 2)) (gammaG q.g * W * q.L) τ / (1 - r) := by
  obtain ⟨Cn₁, hCn₁, h₁⟩ := coneRates_genStable (n + 1) (by omega) (R.C + Ci + 1)
    (by linarith [R.one_le_C])
  obtain ⟨Cn₂, hCn₂, h₂⟩ := coneBracket_stable (n + 1) (by omega) (R.C + Ci + 1)
    (by linarith [R.one_le_C])
  refine ⟨max Cn₁ Cn₂, lt_max_of_lt_left hCn₁, ?_⟩
  intro W q r Ak ν τ Xc Zc Pm ω σ a Ed Bl hW hAk hν hτ hr hru hut ht1 hσ hL hg hm hmim hdy1 hdy2
    hKr hKv hIv hPm hPm1 hZc hZc1 hXc0 hEd0 hBl0 hX hXc hY hY2 hT hκ hκτ
  have hu1 : q.u < 1 := lt_of_le_of_lt hut ht1
  have hr1 : r < 1 := lt_of_le_of_lt hru hu1
  have hr0 : 0 ≤ r := by linarith
  have hL1 : 1 ≤ q.L := by omega
  have hRC := R.one_le_C
  have hmpos : 0 < (𝐦[q]).im := lt_of_lt_of_le (by positivity) hmim
  have him : ((𝐦[q]).im)⁻¹ ≤ R.C := by
    rw [inv_le_comm₀ hmpos (by positivity)]; exact hmim
  set ℓr := ellProp q.g q.L r with hℓr
  set ℓu := ellProp q.g q.L q.u with hℓu
  set ζr := zetaProp q.g W q.L r with hζr
  set ζu := zetaProp q.g W q.L q.u with hζu
  set ζt := zetaProp q.g W q.L q.t with hζt
  set P := (W : ℝ) ^ ν with hP
  set H := 4 * P + 2 with hH
  set ρ := (1 - r) / (1 - q.u) with hρ
  have hℓr1 := coneNode_ell_ge_one hg hL1 r
  have hP1 : 1 ≤ P := Real.one_le_rpow (by exact_mod_cast hW) hν.le
  have hH1 : 1 ≤ H := by linarith
  have hζr0 : 0 ≤ ζr := (coneNode_zeta_pos hg hW hL1 hr1).le
  have hζru : ζr ≤ ζu := coneNode_zeta_mono hg hW hL1 hru hu1
  have hζu0 : 0 ≤ ζu := hζr0.trans hζru
  have hζrt : ζr ≤ ζt := coneNode_zeta_mono hg hW hL1 (hru.trans hut) ht1
  have hρℓ := coneNode_rho_ell hg hL1 hru hu1
  have hxζ : ρ * ℓr / ℓu * ζr = ζu := coneNode_zeta_rho hg hW hL1 hru hu1
  have hγζ : gammaG q.g * W * ℓr * ζr = (1 - r)⁻¹ := coneNode_zeta_mul hg hW hL1 hr1
  have h𝔓0 : 0 ≤ H * (1 + ρ) * (q.L / ℓr) := by
    have : 0 ≤ ρ := div_nonneg (by linarith) (by linarith)
    positivity
  have hPm0 : 0 ≤ Pm := by linarith
  have h𝔓 : ∀ e : ℕ, (H * (1 + ρ) * (q.L / ℓr)) ^ e ≤ Pm ^ e := fun e =>
    pow_le_pow_left₀ h𝔓0 hPm _
  have hPme : ∀ e e' : ℕ, e ≤ e' → Pm ^ e ≤ Pm ^ e' := fun e e' h => pow_le_pow_right₀ hPm1 h
  have hk3 : ∀ x y, (q.u - r) * mixedKer 𝐏[q] q.u x y ≤
      (R.C + Ci + 1) * ((1 - r) / (1 - q.u)) / ellProp q.g q.L q.u :=
    (coneNode_kernel_premises R Ci hCi W q r q.u Ak H hW hAk hr hru hu1 hL hg hKr hKv hIv).2.2.1
  have hdy1' : ∀ x, gammaG q.g * ∑ y, ‖𝐌[q] x y‖ ^ 2 ≤ R.C + Ci + 1 := by
    intro x
    refine le_trans ?_ ((hdy1 x).trans (by linarith))
    have hγ := coneNode_gamma_pos q.g
    gcongr with y
    exact le_add_of_nonneg_left (norm_nonneg _)
  have hdy2' : ∀ x, ∑ y, ‖(1 - (q.u : ℂ) • pairQ (gammaG q.g) 𝐌[q])⁻¹ x y‖ ≤ R.C + Ci + 1 :=
    fun x => (hdy2 q.u (by linarith) hu1.le x).trans (by linarith)
  set X : ℕ → ℝ := fun j => min (P * (Ed j * ζr ^ j)) Xc with hXdef
  set κ : ℕ → ℝ := fun j => P * ζr ^ (j - 1) with hκdef
  have hX0 : ∀ j, 0 ≤ X j := fun j =>
    le_min (mul_nonneg (by linarith) (mul_nonneg (hEd0 j) (pow_nonneg hζr0 _))) hXc0
  have hκ0 : ∀ j, 0 ≤ κ j := fun j => mul_nonneg (by linarith) (pow_nonneg hζr0 _)
  have hXs : ∀ j, 1 ≤ j → j ≤ n + 1 → ∀ (b : Fin j → Fin q.L) (s : Fin j → Bool),
      ‖loopTr (resolventMat (flowH q.g W q.L r ω) (zChar q.g q.E 𝐦[q] r)) b s -
        primLoop q.g W q.L q.E 𝐦[q] r b s‖ ≤ X j :=
    fun j h1 h2 b s => le_min (hX j h1 h2 (b, s)) (hXc j h1 h2 (b, s))
  have hd0 : 0 ≤ P * ℓr := by positivity
  have h4d : 4 * (P * ℓr) + 2 ≤ H * ℓr := by nlinarith
  have hYn := fun b s => hY (b, s)
  simp only [Nat.add_sub_cancel] at hYn
  have hG := h₁ q.g q.E 𝐦[q] W q.L hW hL hm r q.u (flowH q.g W q.L r ω)
    (flowH_isHermitian _ _ _ _ _) σ hσ a X κ (P * (Bl (n + 1 + 1) * ζr ^ (n + 1))) ρ ℓr ℓu H
    (P * ℓr) τ hr0 hru hu1 le_rfl hℓr1 (coneNode_ell_mono hg q.L hru hu1) (coneNode_ell_le r)
    hH1 hρℓ hd0 h4d hτ hk3 hdy1' hdy2' hXs
    (fun j h1 h2 b s hb => (le_add_of_nonneg_left (norm_nonneg _)).trans
      (hT j h1 (by omega) (b, s) hb))
    (fun j h1 h2 b s => hκ j (by omega) (by omega) b s)
    (fun j h1 h2 b s hb => hκτ j (by omega) (by omega) b s hb)
    hYn
    (fun b s hb => (le_add_of_nonneg_right (norm_nonneg _)).trans
      (hT (n + 1 + 1) (by omega) (by omega) (b, s) hb))
  have hB := h₂ q.g q.E 𝐦[q] W q.L hW hL hm r q.u (flowH q.g W q.L r ω)
    (flowH_isHermitian _ _ _ _ _) σ hσ a
    (P * (Bl (2 * (n + 1) + 2) * ζr ^ (2 * (n + 1) + 2 - 1))) ρ ℓr ℓu H (P * ℓr) τ hr0 hru hu1
    le_rfl hℓr1 (coneNode_ell_mono hg q.L hru hu1) (coneNode_ell_le r) hH1 hρℓ hd0 h4d hτ hk3
    hdy1' hdy2' (fun b s => hY2 (b, s))
    (fun b s hb => (le_add_of_nonneg_right (norm_nonneg _)).trans
      (hT (2 * (n + 1) + 2) (by omega) le_rfl (b, s) hb))
  have h1r : 0 < 1 - r := by linarith
  have h1r' : 0 < (1 - r)⁻¹ := inv_pos.2 h1r
  have h1r1 : 1 ≤ (1 - r)⁻¹ := (one_le_inv₀ h1r).2 (by linarith)
  have hγWℓ0 : 0 ≤ gammaG q.g * W * ℓr := by
    have := coneNode_gamma_pos q.g
    positivity
  have hEnv1 := (coneNode_env_parts (n + 1) Ed Bl ζt (hζr0.trans hζrt) hEd0 hBl0).1
  have hCnm : 0 ≤ max Cn₁ Cn₂ := le_trans hCn₁.le (le_max_left _ _)
  have hγWL0 : 0 ≤ gammaG q.g * (W : ℝ) * (q.L : ℝ) := by
    have := coneNode_gamma_pos q.g
    positivity
  have hsum : ∀ (f : ℕ → ℝ), ∑ p ∈ Finset.Icc 3 (n + 1), f (n + 1 + 2 - p) =
      ∑ p ∈ Finset.Icc 3 (n + 1), f (n + 3 - p) := fun f =>
    Finset.sum_congr rfl fun p _ => by rw [show n + 1 + 2 - p = n + 3 - p by omega]
  have hsum2 : ∑ p ∈ Finset.Icc 3 (n + 1), κ p * X (n + 1 + 2 - p) =
      ∑ p ∈ Finset.Icc 3 (n + 1), κ p * X (n + 3 - p) :=
    Finset.sum_congr rfl fun p _ => by rw [show n + 1 + 2 - p = n + 3 - p by omega]
  have hsum3 : ∑ p ∈ Finset.Icc 2 (n + 1), X p * X (n + 1 + 2 - p) =
      ∑ p ∈ Finset.Icc 2 (n + 1), X p * X (n + 3 - p) :=
    Finset.sum_congr rfl fun p _ => by rw [show n + 1 + 2 - p = n + 3 - p by omega]
  rw [hsum2, hsum3] at hG
  refine ⟨?_, ?_⟩
  · refine hG.trans ?_
    have hS1 := coneNode_src_le n hn Ed Bl X κ (gammaG q.g * W * ℓr) ζr ζt P
      (P * (Bl (n + 1 + 1) * ζr ^ (n + 1))) r hr1 hγζ hγWℓ0 hζr0 hζrt hP1 hEd0 hBl0 hX0
      (fun j _ _ => min_le_left _ _) hκ0 (fun j _ _ => le_rfl)
      (mul_nonneg (by linarith) (mul_nonneg (hBl0 _) (pow_nonneg hζr0 _))) le_rfl
    have hXc' : ∀ j, 1 ≤ j → j ≤ n + 1 → X j ≤ Xc := fun j _ _ => min_le_right _ _
    have hκ' : ∀ j, 3 ≤ j → j ≤ n + 1 → κ j ≤ P * ζr ^ (j - 1) := fun j _ _ => le_rfl
    have hT1 := coneNode_tail_le n X κ (gammaG q.g * W * q.L) ζr Zc Xc P r (𝐦[q]).im R.C τ hr0
      hr1 hζr0 hZc hZc1 hP1 hmpos him hτ hγWL0 hX0 hXc' hκ0 hκ'
    have hcomm0 : 0 ≤ τ * (ζr / (𝐦[q]).im) * (1 - r)⁻¹ :=
      mul_nonneg (mul_nonneg hτ (div_nonneg hζr0 hmpos.le)) h1r'.le
    set Tc := gammaG q.g * W * q.L * ((n + 1) * (Xc + P * Zc ^ (n + 1))) + R.C * Zc with hTc
    have hTc0 : 0 ≤ Tc := by
      have : 0 ≤ Zc := by linarith
      positivity
    set E := (2 * (n + 1) + 1 + R.C) * nodeEnv (n + 1) Ed Bl ζt with hE
    have hE' : (2 * (n + 1) + 1) * nodeEnv (n + 1) Ed Bl ζt ≤ E := by
      rw [hE]; nlinarith
    have hpre := coneNode_pref_stable (n + 1) (by omega) (ρ * ℓr / ℓu) ζr ζu hxζ hζr0 hζru
    simp only [Nat.add_sub_cancel] at hpre
    have hH2 : H ^ (n + 1) ≤ H ^ (2 * (n + 1)) + 1 := by
      have := pow_le_pow_right₀ hH1 (show n + 1 ≤ 2 * (n + 1) by omega)
      linarith
    have hmain : max Cn₁ Cn₂ * H ^ (n + 1) * (ρ * ℓr / ℓu) ^ n *
        (gammaG q.g * W * ℓr * (X 1 * (P * (Bl (n + 1 + 1) * ζr ^ (n + 1))) +
          ∑ p ∈ Finset.Icc 3 (n + 1), κ p * X (n + 3 - p) +
          ∑ p ∈ Finset.Icc 2 (n + 1), X p * X (n + 3 - p))) ≤
        max Cn₁ Cn₂ * ((H ^ (2 * (n + 1)) + 1) * ζu ^ (n + 1) * P ^ 2 * E) * (1 - r)⁻¹ := by
      have hx0 : 0 ≤ (ρ * ℓr / ℓu) := by linarith
      calc max Cn₁ Cn₂ * H ^ (n + 1) * (ρ * ℓr / ℓu) ^ n *
          (gammaG q.g * W * ℓr * (X 1 * (P * (Bl (n + 1 + 1) * ζr ^ (n + 1))) +
            ∑ p ∈ Finset.Icc 3 (n + 1), κ p * X (n + 3 - p) +
            ∑ p ∈ Finset.Icc 2 (n + 1), X p * X (n + 3 - p))) ≤
          max Cn₁ Cn₂ * H ^ (n + 1) * (ρ * ℓr / ℓu) ^ n *
            ((1 - r)⁻¹ * ζr ^ (n + 1) * P ^ 2 * ((2 * (n + 1) + 1) * nodeEnv (n + 1) Ed Bl ζt)) :=
            mul_le_mul_of_nonneg_left hS1 (by positivity)
        _ = max Cn₁ Cn₂ * H ^ (n + 1) * ((ρ * ℓr / ℓu) ^ n * ζr ^ (n + 1)) *
            (P ^ 2 * ((2 * (n + 1) + 1) * nodeEnv (n + 1) Ed Bl ζt) * (1 - r)⁻¹) := by ring
        _ ≤ max Cn₁ Cn₂ * (H ^ (2 * (n + 1)) + 1) * ζu ^ (n + 1) * (P ^ 2 * E * (1 - r)⁻¹) := by
            gcongr
        _ = _ := by ring
    have htail : Cn₁ * (H * (1 + ρ) * (q.L / ℓr)) ^ (2 * (n + 1)) *
        (gammaG q.g * W * q.L * τ *
          (∑ j ∈ Finset.Icc 1 (n + 1), X j + ∑ j ∈ Finset.Icc 3 (n + 1), κ j)) ≤
        max Cn₁ Cn₂ * Pm ^ (4 * (n + 1)) * (τ * Tc) * (1 - r)⁻¹ := by
      have h1 : gammaG q.g * W * q.L * τ *
          (∑ j ∈ Finset.Icc 1 (n + 1), X j + ∑ j ∈ Finset.Icc 3 (n + 1), κ j) ≤
          (1 - r)⁻¹ * τ * Tc := by linarith
      have h2 : (H * (1 + ρ) * (q.L / ℓr)) ^ (2 * (n + 1)) ≤ Pm ^ (4 * (n + 1)) :=
        (h𝔓 _).trans (hPme _ _ (by omega))
      calc Cn₁ * (H * (1 + ρ) * (q.L / ℓr)) ^ (2 * (n + 1)) *
          (gammaG q.g * W * q.L * τ *
            (∑ j ∈ Finset.Icc 1 (n + 1), X j + ∑ j ∈ Finset.Icc 3 (n + 1), κ j)) ≤
          max Cn₁ Cn₂ * Pm ^ (4 * (n + 1)) * ((1 - r)⁻¹ * τ * Tc) :=
            mul_le_mul (mul_le_mul (le_max_left _ _) h2 (pow_nonneg h𝔓0 _) hCnm) h1
              (mul_nonneg (mul_nonneg hγWL0 hτ) (add_nonneg (Finset.sum_nonneg fun j _ => hX0 j)
                (Finset.sum_nonneg fun j _ => hκ0 j))) (by positivity)
        _ = _ := by ring
    have hG' : Cn₁ * H ^ (n + 1) * (ρ * ℓr / ℓu) ^ (n + 1 - 1) *
        (gammaG q.g * W * ℓr * (X 1 * (P * (Bl (n + 1 + 1) * ζr ^ (n + 1))) +
          ∑ p ∈ Finset.Icc 3 (n + 1), κ p * X (n + 3 - p) +
          ∑ p ∈ Finset.Icc 2 (n + 1), X p * X (n + 3 - p))) ≤
        max Cn₁ Cn₂ * H ^ (n + 1) * (ρ * ℓr / ℓu) ^ n *
        (gammaG q.g * W * ℓr * (X 1 * (P * (Bl (n + 1 + 1) * ζr ^ (n + 1))) +
          ∑ p ∈ Finset.Icc 3 (n + 1), κ p * X (n + 3 - p) +
          ∑ p ∈ Finset.Icc 2 (n + 1), X p * X (n + 3 - p))) := by
      rw [Nat.add_sub_cancel]
      have hx0 : 0 ≤ (ρ * ℓr / ℓu) := by linarith
      have hS0 : 0 ≤ gammaG q.g * W * ℓr * (X 1 * (P * (Bl (n + 1 + 1) * ζr ^ (n + 1))) +
          ∑ p ∈ Finset.Icc 3 (n + 1), κ p * X (n + 3 - p) +
          ∑ p ∈ Finset.Icc 2 (n + 1), X p * X (n + 3 - p)) := by
        refine mul_nonneg hγWℓ0 (add_nonneg (add_nonneg (mul_nonneg (hX0 1)
          (mul_nonneg (by linarith) (mul_nonneg (hBl0 _) (pow_nonneg hζr0 _))))
          (Finset.sum_nonneg fun p _ => mul_nonneg (hκ0 p) (hX0 _)))
          (Finset.sum_nonneg fun p _ => mul_nonneg (hX0 p) (hX0 _)))
      refine mul_le_mul_of_nonneg_right ?_ hS0
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hx0 _)
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    unfold coneNode_Kβ
    have e1 : (max Cn₁ Cn₂ * ((H ^ (2 * (n + 1)) + 1) * ζu ^ (n + 1) * P ^ 2 * E) +
        max Cn₁ Cn₂ * Pm ^ (4 * (n + 1)) * (τ * Tc)) / (1 - r) =
        max Cn₁ Cn₂ * ((H ^ (2 * (n + 1)) + 1) * ζu ^ (n + 1) * P ^ 2 * E) * (1 - r)⁻¹ +
        max Cn₁ Cn₂ * Pm ^ (4 * (n + 1)) * (τ * Tc) * (1 - r)⁻¹ := by ring
    rw [e1]
    exact add_le_add (hG'.trans hmain) htail
  · refine hB.trans ?_
    have hY₂ : gammaG q.g * W * ℓr * (P * (Bl (2 * (n + 1) + 2) * ζr ^ (2 * (n + 1) + 2 - 1))) =
        (1 - r)⁻¹ * (P * Bl (2 * (n + 1) + 2)) * ζr ^ (2 * (n + 1)) := by
      rw [show 2 * (n + 1) + 2 - 1 = 2 * (n + 1) + 1 by omega, pow_succ, ← hγζ]; ring
    rw [hY₂]
    have hpre := coneNode_pref_stable (2 * (n + 1)) (by omega) (ρ * ℓr / ℓu) ζr ζu hxζ hζr0 hζru
    have hB0 : 0 ≤ P * Bl (2 * (n + 1) + 2) := mul_nonneg (by linarith) (hBl0 _)
    have hγWL : 0 ≤ gammaG q.g * (W : ℝ) * (q.L : ℝ) * τ := mul_nonneg hγWL0 hτ
    have hH2 : H ^ (2 * (n + 1)) ≤ H ^ (4 * (n + 1)) + 1 := by
      have := pow_le_pow_right₀ hH1 (show 2 * (n + 1) ≤ 4 * (n + 1) by omega)
      linarith
    have hb1 : Cn₂ * H ^ (2 * (n + 1)) * (ρ * ℓr / ℓu) ^ (2 * (n + 1) - 1) *
        ((1 - r)⁻¹ * (P * Bl (2 * (n + 1) + 2)) * ζr ^ (2 * (n + 1))) ≤
        max Cn₁ Cn₂ * ((H ^ (4 * (n + 1)) + 1) * ζu ^ (2 * (n + 1)) *
          (P * Bl (2 * (n + 1) + 2))) * (1 - r)⁻¹ := by
      calc Cn₂ * H ^ (2 * (n + 1)) * (ρ * ℓr / ℓu) ^ (2 * (n + 1) - 1) *
          ((1 - r)⁻¹ * (P * Bl (2 * (n + 1) + 2)) * ζr ^ (2 * (n + 1))) =
          Cn₂ * H ^ (2 * (n + 1)) * ((ρ * ℓr / ℓu) ^ (2 * (n + 1) - 1) * ζr ^ (2 * (n + 1))) *
            ((1 - r)⁻¹ * (P * Bl (2 * (n + 1) + 2))) := by ring
        _ ≤ max Cn₁ Cn₂ * (H ^ (4 * (n + 1)) + 1) * ζu ^ (2 * (n + 1)) *
            ((1 - r)⁻¹ * (P * Bl (2 * (n + 1) + 2))) := by
            refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg h1r'.le hB0)
            refine mul_le_mul (mul_le_mul (le_max_right _ _) hH2 (by positivity) hCnm) hpre
              (by have : 0 ≤ ρ * ℓr / ℓu := by linarith
                  positivity) (by positivity)
        _ = _ := by ring
    have hb2 : Cn₂ * (H * (1 + ρ) * ((q.L : ℝ) / ℓr)) ^ (4 * (n + 1)) *
        (gammaG q.g * (W : ℝ) * (q.L : ℝ) * τ) ≤
        max Cn₁ Cn₂ * Pm ^ (8 * (n + 1)) * (gammaG q.g * (W : ℝ) * (q.L : ℝ) * τ) * (1 - r)⁻¹ := by
      have h2 : (H * (1 + ρ) * ((q.L : ℝ) / ℓr)) ^ (4 * (n + 1)) ≤ Pm ^ (8 * (n + 1)) :=
        (h𝔓 _).trans (hPme _ _ (by omega))
      refine (mul_le_mul_of_nonneg_right (mul_le_mul (le_max_right _ _) h2
        (pow_nonneg h𝔓0 _) hCnm) hγWL).trans ?_
      exact le_mul_of_one_le_right (by positivity) h1r1
    unfold coneNode_Kb
    have e1 : (max Cn₁ Cn₂ * ((H ^ (4 * (n + 1)) + 1) * ζu ^ (2 * (n + 1)) *
        (P * Bl (2 * (n + 1) + 2))) +
        max Cn₁ Cn₂ * Pm ^ (8 * (n + 1)) * (gammaG q.g * W * q.L * τ)) / (1 - r) =
        max Cn₁ Cn₂ * ((H ^ (4 * (n + 1)) + 1) * ζu ^ (2 * (n + 1)) *
          (P * Bl (2 * (n + 1) + 2))) * (1 - r)⁻¹ +
        max Cn₁ Cn₂ * Pm ^ (8 * (n + 1)) * (gammaG q.g * W * q.L * τ) * (1 - r)⁻¹ := by ring
    rw [e1]
    exact add_le_add hb1 hb2


/-! ### The moment comparison for a propagated loop-error field -/

/-- The moment comparison on `[s, u]` for a field `Σ_b c_r(b) D(r; b)` of loop errors at the
Gaussian coordinates of (5.1) [fo:eq:flow], with the rates `K_β/(1 - r)` and `K_b/(1 - r)` off a set
`Bad r` of probability at most `δ_b` and the crude moments `K` of the generator and the bracket. -/
private lemma coneNode_flowEngine (g E : ℝ) {W L k : ℕ} (hW : 1 ≤ W) (σ : Fin k → Bool)
    (c : ℝ → (Fin k → Fin L) → ℂ) {s u : ℝ} (hs : 0 < s) (hsu : s ≤ u) (hu : u < 1)
    (hY : HeatClass (fun r y => ∑ b, c r b * loopErrField g E (mRoot g L E) W L b σ r y)
      (-1 / 2) ((u + 1) / 2))
    (p : ℕ) (hp : 1 ≤ p) {K δb Kβ Kb : ℝ} (hK : 0 ≤ K) (hδb : 0 ≤ δb) (hKβ : 0 ≤ Kβ)
    (hKb : 0 ≤ Kb) (Bad : ℝ → Set (Ω W L))
    (hbad : ∀ r ∈ Set.Ioo s u, μ W L (Bad r) ≤ ENNReal.ofReal δb)
    (hrate : ∀ r ∈ Set.Ioo s u, ∀ ω, ω ∉ Bad r →
      ‖blockGen W L (gammaG g) (fun r' N => ∑ b, c r' b *
          (resLoop g E (mRoot g L E) b σ r' N - primLoop g W L E (mRoot g L E) r' b σ)) r
          (flowH g W L r ω)‖ ≤ Kβ / (1 - r) ∧
      ‖blockGamma W L (gammaG g)
          (fun N => ∑ b, c r b * (resLoop g E (mRoot g L E) b σ r N -
            primLoop g W L E (mRoot g L E) r b σ))
          (fun N => ∑ b, c r b * (resLoop g E (mRoot g L E) b σ r N -
            primLoop g W L E (mRoot g L E) r b σ)) (flowH g W L r ω)‖ ≤ Kb / (1 - r))
    (hcrude : ∀ r ∈ Set.Ioo s u,
      ∫ ω, ‖blockGen W L (gammaG g) (fun r' N => ∑ b, c r' b *
          (resLoop g E (mRoot g L E) b σ r' N - primLoop g W L E (mRoot g L E) r' b σ)) r
          (flowH g W L r ω)‖ ^ (4 * p) ∂(μ W L) ≤ K ^ (4 * p) ∧
      ∫ ω, ‖blockGamma W L (gammaG g)
          (fun N => ∑ b, c r b * (resLoop g E (mRoot g L E) b σ r N -
            primLoop g W L E (mRoot g L E) r b σ))
          (fun N => ∑ b, c r b * (resLoop g E (mRoot g L E) b σ r N -
            primLoop g W L E (mRoot g L E) r b σ)) (flowH g W L r ω)‖ ^ (2 * p) ∂(μ W L) ≤
        K ^ (2 * p)) :
    (∫ ω, ‖∑ b, c u b * flowErr W ⟨g, E, L, u⟩ b σ ω‖ ^ (2 * p) ∂(μ W L)) ^ (1 / (2 * (p : ℝ))) ≤
      (∫ ω, ‖∑ b, c s b * flowErr W ⟨g, E, L, s⟩ b σ ω‖ ^ (2 * p) ∂(μ W L)) ^
          (1 / (2 * (p : ℝ))) +
        Real.sqrt ((2 * p - 1) * (Kb * Real.log ((1 - s) / (1 - u)))) +
        Real.sqrt ((2 * p - 1) * (K * δb ^ (1 / (2 * (p : ℝ))))) +
        Kβ * Real.log ((1 - s) / (1 - u)) + K * δb ^ (1 / (4 * (p : ℝ))) := by
  set σ2 : ℝ := gammaG g / W with hσ2
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hσ2pos : 0 < σ2 := div_pos (coneNode_gamma_pos g) hWpos
  have hsq : ∀ r : ℝ, 0 < r → Real.sqrt (r * σ2) ≠ 0 := fun r hr =>
    (Real.sqrt_pos.2 (mul_pos hr hσ2pos)).ne'
  have key : ∀ v : ℝ, 0 ≤ v → ∀ x : Ω W L,
      ∑ b, c v b * loopErrField g E (mRoot g L E) W L b σ v (Real.sqrt (v * σ2) • x) =
        ∑ b, c v b * flowErr W ⟨g, E, L, v⟩ b σ x := by
    intro v hv x
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [flowErr_eq_loopErrField W ⟨g, E, L, v⟩ hv b σ x]
  set BadY : ℝ → Set (Ω W L) := fun r => {y | (Real.sqrt (r * σ2))⁻¹ • y ∈ Bad r} with hBadY
  have hset : ∀ r : ℝ, 0 < r → {x : Ω W L | Real.sqrt (r * σ2) • x ∈ BadY r} = Bad r := by
    intro r hr
    ext x
    simp only [hBadY, Set.mem_ofPred_eq, smul_smul, inv_mul_cancel₀ (hsq r hr), one_smul]
  have hpos : ∀ r ∈ Set.Ioo s u, 0 < r := fun r hr => hs.trans hr.1
  have h := coneNode_engine (ι := Fin L × Fin W × Fin W) σ2 hσ2pos.le
    (fun r y => ∑ b, c r b * loopErrField g E (mRoot g L E) W L b σ r y) hs.le hsu hu hY p hp
    hK hδb hKβ hKb BadY
    (fun r hr => by rw [hset r (hpos r hr)]; exact hbad r hr)
    (fun r hr y hy => by
      have hx : y = Real.sqrt (r * σ2) • ((Real.sqrt (r * σ2))⁻¹ • y) := by
        rw [smul_smul, mul_inv_cancel₀ (hsq r (hpos r hr)), one_smul]
      rw [hx, coneCrude_coordGen_eq g E (mRoot g L E) c σ (hpos r hr).le,
        coneCrude_coordGamma_eq g E (mRoot g L E) (c r) σ (hpos r hr).le]
      exact hrate r hr _ hy)
    (fun r hr => by
      refine ⟨le_of_eq_of_le (integral_congr_ae (ae_of_all _ fun x => ?_)) (hcrude r hr).1,
        le_of_eq_of_le (integral_congr_ae (ae_of_all _ fun x => ?_)) (hcrude r hr).2⟩
      · simp only
        rw [coneCrude_coordGen_eq g E (mRoot g L E) c σ (hpos r hr).le]
      · simp only
        rw [coneCrude_coordGamma_eq g E (mRoot g L E) (c r) σ (hpos r hr).le])
  have e : ∀ v : ℝ, 0 ≤ v →
      ∫ x, ‖(fun r y => ∑ b, c r b * loopErrField g E (mRoot g L E) W L b σ r y) v
          (Real.sqrt (v * σ2) • x)‖ ^ (2 * p) ∂(stdGauss (Fin L × Fin W × Fin W)) =
        ∫ ω, ‖∑ b, c v b * flowErr W ⟨g, E, L, v⟩ b σ ω‖ ^ (2 * p) ∂(μ W L) := by
    intro v hv
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [key v hv x]
  rw [e u (hs.le.trans hsu), e s hs.le] at h
  exact h


/-! ### Moments -/

/-- The loop error at a fixed time is continuous in the Gaussian coordinates. -/
private lemma coneNode_flowErr_cont {W : ℕ} (hW : 1 ≤ W) (x : FlowPt) (hL : 3 ≤ x.L)
    (hm : IsDysonRootV (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E)) (hu0 : 0 ≤ x.u)
    (hu1 : x.u < 1) {k : ℕ} (b : Fin k → Fin x.L) (σ : Fin k → Bool) :
    Continuous (fun ω => flowErr W x b σ ω) := by
  have hH := heatClass_loopErrField x.g x.E (mRoot x.g x.L x.E) W x.L hW hL hm b σ
    (a' := -1 / 2) (b' := (x.u + 1) / 2) (by norm_num) (by linarith)
  have hmem : ∀ y : Ω W x.L, ((x.u, y) : ℝ × Ω W x.L) ∈ Set.Ioo (-1 / 2 : ℝ) ((x.u + 1) / 2) ×ˢ
      (Set.univ : Set (Ω W x.L)) := fun y => Set.mk_mem_prod ⟨by linarith, by linarith⟩ trivial
  have h1 := hH.cont.comp_continuous (continuous_const.prodMk continuous_id) hmem
  have h2 := h1.comp (continuous_const_smul (Real.sqrt (x.u * (gammaG x.g / W))))
  have e : (fun ω => flowErr W x b σ ω) =
      (Function.uncurry (fun r y => loopErrField x.g x.E (mRoot x.g x.L x.E) W x.L b σ r y) ∘
        fun y => (x.u, y)) ∘ fun ω => Real.sqrt (x.u * (gammaG x.g / W)) • ω := by
    funext ω
    exact flowErr_eq_loopErrField W x hu0 b σ ω
  rw [e]
  exact h2

/-- The moment-from-tail bound (`moment_of_tail`) at order `2p` for a continuous complex field. -/
private lemma coneNode_moment {W L : ℕ} (X : Ω W L → ℂ) (hX : Continuous X) (p : ℕ) (hp : 1 ≤ p)
    {K Ψ δ : ℝ} (hK : 0 ≤ K) (hΨ : 0 ≤ Ψ) (hδ : 0 ≤ δ)
    (hint : Integrable (fun ω => ‖X ω‖ ^ (4 * p)) (μ W L))
    (hKm : ∫ ω, ‖X ω‖ ^ (4 * p) ∂(μ W L) ≤ K ^ (4 * p)) (Bad : Set (Ω W L))
    (hBad : μ W L Bad ≤ ENNReal.ofReal δ) (hgood : ∀ ω, ω ∉ Bad → ‖X ω‖ ≤ Ψ) :
    (∫ ω, ‖X ω‖ ^ (2 * p) ∂(μ W L)) ^ (1 / (2 * (p : ℝ))) ≤ Ψ + K * δ ^ (1 / (4 * (p : ℝ))) := by
  have h4 : 2 * (2 * p) = 4 * p := by ring
  have hc : (((2 * p : ℕ) : ℝ)) = 2 * (p : ℝ) := by push_cast; ring
  have hc4 : 2 * (((2 * p : ℕ) : ℝ)) = 4 * (p : ℝ) := by push_cast; ring
  have h := moment_of_tail (μ W L) (fun ω => ‖X ω‖) (fun ω => norm_nonneg _)
    (hX.norm.aestronglyMeasurable) (2 * p) (by omega) K Ψ δ hK hΨ hδ
    (by rw [h4]; exact hint) (by rw [h4]; exact hKm) (by
      have hsub : {ω | Ψ < ‖X ω‖} ⊆ Bad := fun ω hω => by
        by_contra hb
        exact absurd (hgood ω hb) (not_le.2 hω)
      have := (measure_mono hsub).trans hBad
      exact ENNReal.toReal_le_of_le_ofReal hδ this)
  rw [hc4, hc] at h
  exact h

/-- From a bound on the `L^{2p}` norm to a bound on the `2p`-th moment. -/
private lemma coneNode_pow_of_rpow {I M : ℝ} (p : ℕ) (hp : 1 ≤ p) (hI : 0 ≤ I) (_hM : 0 ≤ M)
    (h : I ^ (1 / (2 * (p : ℝ))) ≤ M) : I ≤ M ^ (2 * p) := by
  have hp0 : (0 : ℝ) < 2 * p := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  calc I = (I ^ (1 / (2 * (p : ℝ)))) ^ (2 * p) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hI]
        push_cast
        rw [one_div, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
    _ ≤ M ^ (2 * p) := pow_le_pow_left₀ (Real.rpow_nonneg hI _) h _

/-- `|y + z|^m ≤ 2^m(|y|^m + |z|^m)`. -/
private lemma coneNode_add_pow (y z : ℂ) (m : ℕ) :
    ‖y + z‖ ^ m ≤ 2 ^ m * (‖y‖ ^ m + ‖z‖ ^ m) := by
  have h1 : ‖y + z‖ ≤ 2 * max ‖y‖ ‖z‖ := by
    refine (norm_add_le _ _).trans ?_
    linarith [le_max_left ‖y‖ ‖z‖, le_max_right ‖y‖ ‖z‖]
  have h2 : (max ‖y‖ ‖z‖) ^ m ≤ ‖y‖ ^ m + ‖z‖ ^ m := by
    rcases le_total ‖y‖ ‖z‖ with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg (norm_nonneg y) m]
    · rw [max_eq_left h]; linarith [pow_nonneg (norm_nonneg z) m]
  calc ‖y + z‖ ^ m ≤ (2 * max ‖y‖ ‖z‖) ^ m := pow_le_pow_left₀ (norm_nonneg _) h1 m
    _ = 2 ^ m * (max ‖y‖ ‖z‖) ^ m := mul_pow _ _ _
    _ ≤ 2 ^ m * (‖y‖ ^ m + ‖z‖ ^ m) := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- `E|Y + Z|^{2p} ≤ (2(M₁ + M₂))^{2p}` from `‖Y‖_{2p} ≤ M₁` and `‖Z‖_{2p} ≤ M₂`. -/
private lemma coneNode_sum_moment {W L : ℕ} (Y Z : Ω W L → ℂ) (p : ℕ) (hp : 1 ≤ p) {M₁ M₂ : ℝ}
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hYi : Integrable (fun ω => ‖Y ω‖ ^ (2 * p)) (μ W L))
    (hZi : Integrable (fun ω => ‖Z ω‖ ^ (2 * p)) (μ W L))
    (hY : (∫ ω, ‖Y ω‖ ^ (2 * p) ∂(μ W L)) ^ (1 / (2 * (p : ℝ))) ≤ M₁)
    (hZ : (∫ ω, ‖Z ω‖ ^ (2 * p) ∂(μ W L)) ^ (1 / (2 * (p : ℝ))) ≤ M₂) :
    ∫ ω, ‖Y ω + Z ω‖ ^ (2 * p) ∂(μ W L) ≤ (2 * (M₁ + M₂)) ^ (2 * p) := by
  have hY' := coneNode_pow_of_rpow p hp (integral_nonneg fun ω => by positivity) hM₁ hY
  have hZ' := coneNode_pow_of_rpow p hp (integral_nonneg fun ω => by positivity) hM₂ hZ
  calc ∫ ω, ‖Y ω + Z ω‖ ^ (2 * p) ∂(μ W L) ≤
      ∫ ω, 2 ^ (2 * p) * (‖Y ω‖ ^ (2 * p) + ‖Z ω‖ ^ (2 * p)) ∂(μ W L) := by
        refine integral_mono_of_nonneg (ae_of_all _ fun ω => by positivity)
          ((hYi.add hZi).const_mul _) (ae_of_all _ fun ω => coneNode_add_pow _ _ _)
    _ = 2 ^ (2 * p) * (∫ ω, ‖Y ω‖ ^ (2 * p) ∂(μ W L) + ∫ ω, ‖Z ω‖ ^ (2 * p) ∂(μ W L)) := by
        rw [integral_const_mul, integral_add hYi hZi]
    _ ≤ 2 ^ (2 * p) * (M₁ ^ (2 * p) + M₂ ^ (2 * p)) := by gcongr
    _ ≤ 2 ^ (2 * p) * (M₁ + M₂) ^ (2 * p) := by
        gcongr
        exact pow_add_pow_le hM₁ hM₂ (by omega)
    _ = (2 * (M₁ + M₂)) ^ (2 * p) := (mul_pow _ _ _).symm

/-- `E|X|^r ≤ (1 + c^{2r}) B^r` from `E|X|^{2r} ≤ (cB)^{2r}`. -/
private lemma coneNode_lower_moment {W L : ℕ} (X : Ω W L → ℂ) (r : ℕ) {B c : ℝ} (hB : 0 < B)
    (_hc : 0 ≤ c) (hX1 : Integrable (fun ω => ‖X ω‖ ^ r) (μ W L))
    (hX2 : Integrable (fun ω => ‖X ω‖ ^ (2 * r)) (μ W L))
    (h : ∫ ω, ‖X ω‖ ^ (2 * r) ∂(μ W L) ≤ (c * B) ^ (2 * r)) :
    ∫ ω, ‖X ω‖ ^ r ∂(μ W L) ≤ (1 + c ^ (2 * r)) * B ^ r := by
  have hBr : 0 < B ^ r := pow_pos hB r
  have hpt : ∀ ω, ‖X ω‖ ^ r ≤ B ^ r + ‖X ω‖ ^ (2 * r) / B ^ r := by
    intro ω
    rcases le_total ‖X ω‖ B with h1 | h1
    · have := pow_le_pow_left₀ (norm_nonneg _) h1 r
      have : 0 ≤ ‖X ω‖ ^ (2 * r) / B ^ r := by positivity
      linarith
    · have h2 : B ^ r ≤ ‖X ω‖ ^ r := pow_le_pow_left₀ hB.le h1 r
      have e : ‖X ω‖ ^ (2 * r) = ‖X ω‖ ^ r * ‖X ω‖ ^ r := by rw [two_mul, pow_add]
      have : ‖X ω‖ ^ r ≤ ‖X ω‖ ^ r * ‖X ω‖ ^ r / B ^ r := by
        rw [le_div_iff₀ hBr]
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
      rw [e]
      linarith
  calc ∫ ω, ‖X ω‖ ^ r ∂(μ W L) ≤ ∫ ω, (B ^ r + ‖X ω‖ ^ (2 * r) / B ^ r) ∂(μ W L) :=
        integral_mono hX1 ((integrable_const _).add (hX2.div_const _)) hpt
    _ = B ^ r + (∫ ω, ‖X ω‖ ^ (2 * r) ∂(μ W L)) / B ^ r := by
        rw [integral_add (integrable_const _) (hX2.div_const _), integral_const, integral_div]
        simp
    _ ≤ B ^ r + (c * B) ^ (2 * r) / B ^ r := by gcongr
    _ = (1 + c ^ (2 * r)) * B ^ r := by
        rw [mul_pow, pow_mul B 2 r]
        field_simp
        ring


/-! ### The initial and the terminal terms at a good sample -/

/-- The initial term of a cyclically alternating word: the propagated projected field at `r = s`
of the loop error `D_{n+1}(s)`, bounded by `|D_{n+1}(s)| ≤ W^νζ_s^{n+1}` and its tails. -/
private lemma coneNode_init_proj (R : PropRegime) (n : ℕ) (hn : 1 ≤ n) (Ci : ℝ) (hCi : 0 < Ci) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (W : ℕ) (q : StepPt) (Ak ν τ Pm : ℝ) (ω : Ω W q.L)
      (σ : Fin (n + 1) → Bool) (a : Fin (n + 1) → Fin q.L),
      1 ≤ W → 0 < Ak → 0 < ν → 0 ≤ τ → 1 / 2 ≤ q.s → q.s ≤ q.u → q.u < 1 →
      3 ≤ q.L → 0 ≤ q.g → IsDysonRootV (hopB q.g) (gammaG q.g) q.L q.E 𝐦[q] →
      (∀ x y, 0 ≤ mixedKer 𝐏[q] q.s x y ∧ mixedKer 𝐏[q] q.s x y ≤
        R.C / ((1 - q.s) * ellProp q.g q.L q.s) *
          Real.exp (-(R.c * cycDist x y / ellProp q.g q.L q.s)) +
          (ellProp q.g q.L q.s)⁻¹ * (W : ℝ) ^ (-Ak)) →
      (∀ x y, 0 ≤ mixedKer 𝐏[q] q.u x y ∧ mixedKer 𝐏[q] q.u x y ≤
        R.C / ((1 - q.u) * ellProp q.g q.L q.u) *
          Real.exp (-(R.c * cycDist x y / ellProp q.g q.L q.u)) +
          (ellProp q.g q.L q.u)⁻¹ * (W : ℝ) ^ (-Ak)) →
      (∀ x y y', |mixedKer 𝐏[q] q.u x y - mixedKer 𝐏[q] q.u x y'| ≤
        Ci / ((1 - q.u) * ellProp q.g q.L q.u) * ((cycDist y y' : ℝ) / ellProp q.g q.L q.u) +
          (ellProp q.g q.L q.u)⁻¹ * (W : ℝ) ^ (-Ak)) →
      (4 * (W : ℝ) ^ ν + 2) * (1 + (1 - q.s) / (1 - q.u)) * (q.L / ellProp q.g q.L q.s) ≤ Pm →
      1 ≤ Pm →
      Pm ^ (8 * (n + 1)) * (R.C * Real.exp (-(R.c * (4 * (W : ℝ) ^ ν + 2) / 4)) +
        (W : ℝ) ^ (-Ak)) ≤ 1 →
      (∀ w : Word (n + 1) q.L, ‖flowErr W (q.at q.s) w.1 w.2 ω‖ ≤
        (W : ℝ) ^ ν * zetaProp q.g W q.L q.s ^ (n + 1)) →
      (∀ w : Word (n + 1) q.L, (W : ℝ) ^ ν * ellProp q.g q.L q.s < wordDiam w.1 →
        ‖loopTr (flowG W (q.at q.s) ω) w.1 w.2‖ + ‖flowErr W (q.at q.s) w.1 w.2 ω‖ ≤ τ) →
      ‖∑ b, projCoef 𝐏[q] q.u q.s a b * flowErr W (q.at q.s) b σ ω‖ ≤
        Cn * ((4 * (W : ℝ) ^ ν + 2) ^ (2 * (n + 1)) + 1) * zetaProp q.g W q.L q.u ^ (n + 1) *
          (W : ℝ) ^ ν + Cn * Pm ^ (4 * (n + 1)) * τ := by
  obtain ⟨Cn, hCn, h⟩ := coneRates_fieldProj n hn (R.C + Ci + 1) (R.C + 1)
    (by linarith [R.one_le_C]) (by linarith [R.one_le_C])
  refine ⟨Cn, hCn, ?_⟩
  intro W q Ak ν τ Pm ω σ a hW hAk hν hτ hs hsu hu1 hL hg hm hKs hKv hIv hPm hPm1 hτθ hX hXτ
  have hs0 : 0 ≤ q.s := by linarith
  have hs1 : q.s < 1 := lt_of_le_of_lt hsu hu1
  have hL1 : 1 ≤ q.L := by omega
  have hℓs := coneNode_ell_ge_one hg hL1 q.s
  set P := (W : ℝ) ^ ν with hP
  set H := 4 * P + 2 with hH
  set ρ := (1 - q.s) / (1 - q.u) with hρ
  set τθ := R.C * Real.exp (-(R.c * H / 4)) + (W : ℝ) ^ (-Ak) with hτθdef
  have hP1 : 1 ≤ P := Real.one_le_rpow (by exact_mod_cast hW) hν.le
  have hτθ0 : 0 ≤ τθ := by
    have := Real.exp_pos (-(R.c * H / 4))
    have := Real.rpow_nonneg (Nat.cast_nonneg W) (-Ak)
    have := R.one_le_C
    positivity
  have h𝔓0 : 0 ≤ H * (1 + ρ) * (q.L / ellProp q.g q.L q.s) := by
    have : 0 ≤ ρ := div_nonneg (by linarith) (by linarith)
    positivity
  have h𝔓 : ∀ e : ℕ, (H * (1 + ρ) * (q.L / ellProp q.g q.L q.s)) ^ e ≤ Pm ^ e := fun e =>
    pow_le_pow_left₀ h𝔓0 hPm _
  have hτθ4 : (H * (1 + ρ) * (q.L / ellProp q.g q.L q.s)) ^ (4 * (n + 1)) * τθ ≤ 1 :=
    (mul_le_mul_of_nonneg_right ((h𝔓 _).trans (pow_le_pow_right₀ hPm1 (by omega))) hτθ0).trans
      hτθ
  have hτθ1 : τθ ≤ 1 := by
    have : 1 ≤ Pm ^ (8 * (n + 1)) := one_le_pow₀ hPm1
    nlinarith
  obtain ⟨k1, k2, k3, k4⟩ := coneNode_kernel_premises R Ci hCi W q q.s q.u Ak H hW hAk hs hsu hu1
    hL hg hKs hKv hIv
  have hζs0 : 0 ≤ zetaProp q.g W q.L q.s := (coneNode_zeta_pos hg hW hL1 hs1).le
  have hb := h q.g q.E 𝐦[q] q.L hL hm q.s q.u ρ (ellProp q.g q.L q.s) (ellProp q.g q.L q.u) H
    (P * ellProp q.g q.L q.s) τ τθ (P * zetaProp q.g W q.L q.s ^ (n + 1))
    (fun b => flowErr W (q.at q.s) b σ ω) a hs0 hsu hu1 le_rfl hℓs
    (coneNode_ell_mono hg q.L hsu hu1) (coneNode_ell_le q.s) (by linarith)
    (coneNode_rho_ell hg hL1 hsu hu1) (by positivity) (by nlinarith) hτ hτθ0 hτθ1 k1 k2 k3 k4
    (fun b => hX (b, σ))
    (fun b hb => (le_add_of_nonneg_left (norm_nonneg _)).trans (hXτ (b, σ) hb))
  refine hb.trans ?_
  have hpre := coneNode_pref (n + 1) (2 * (n + 1)) (4 * (n + 1)) H
    (ρ * ellProp q.g q.L q.s / ellProp q.g q.L q.u) (H * (1 + ρ) * (q.L / ellProp q.g q.L q.s))
    τθ (zetaProp q.g W q.L q.s) (zetaProp q.g W q.L q.u) (coneNode_zeta_rho hg hW hL1 hsu hu1)
    hζs0 (coneNode_zeta_mono hg hW hL1 hsu hu1) h𝔓0 hτθ0 hτθ4
  have e : Cn * (H ^ (2 * (n + 1)) * (ρ * ellProp q.g q.L q.s / ellProp q.g q.L q.u) ^ (n + 1) +
      (H * (1 + ρ) * (q.L / ellProp q.g q.L q.s)) ^ (4 * (n + 1)) * τθ) *
      (P * zetaProp q.g W q.L q.s ^ (n + 1)) =
      Cn * P * ((H ^ (2 * (n + 1)) * (ρ * ellProp q.g q.L q.s / ellProp q.g q.L q.u) ^ (n + 1) +
      (H * (1 + ρ) * (q.L / ellProp q.g q.L q.s)) ^ (4 * (n + 1)) * τθ) *
      zetaProp q.g W q.L q.s ^ (n + 1)) := by ring
  rw [e]
  have h1 : Cn * P * ((H ^ (2 * (n + 1)) *
      (ρ * ellProp q.g q.L q.s / ellProp q.g q.L q.u) ^ (n + 1) +
      (H * (1 + ρ) * (q.L / ellProp q.g q.L q.s)) ^ (4 * (n + 1)) * τθ) *
      zetaProp q.g W q.L q.s ^ (n + 1)) ≤
      Cn * P * ((H ^ (2 * (n + 1)) + 1) * zetaProp q.g W q.L q.u ^ (n + 1)) :=
    mul_le_mul_of_nonneg_left hpre (by positivity)
  have h2 : Cn * (H * (1 + ρ) * (q.L / ellProp q.g q.L q.s)) ^ (4 * (n + 1)) * τ ≤
      Cn * Pm ^ (4 * (n + 1)) * τ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h𝔓 _) hCn.le) hτ
  have e2 : Cn * P * ((H ^ (2 * (n + 1)) + 1) * zetaProp q.g W q.L q.u ^ (n + 1)) =
      Cn * (H ^ (2 * (n + 1)) + 1) * zetaProp q.g W q.L q.u ^ (n + 1) * P := by ring
  linarith

/-- The initial term of a word with a stable leg: the propagated field at `r = s` of
`D_{n+1}(s)`. -/
private lemma coneNode_init_stable (R : PropRegime) (n : ℕ) (hn : 1 ≤ n) (Ci : ℝ)
    (hCi : 0 < Ci) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (W : ℕ) (q : StepPt) (Ak ν τ Pm : ℝ) (ω : Ω W q.L)
      (σ : Fin (n + 1) → Bool) (a : Fin (n + 1) → Fin q.L),
      (∃ j, σ (finRotate (n + 1) j) = σ j) →
      1 ≤ W → 0 < Ak → 0 < ν → 0 ≤ τ → 1 / 2 ≤ q.s → q.s ≤ q.u → q.u < 1 →
      3 ≤ q.L → 0 ≤ q.g → IsDysonRootV (hopB q.g) (gammaG q.g) q.L q.E 𝐦[q] →
      (∀ a, gammaG q.g * ∑ b, (‖𝐌[q] a b‖ + ‖𝐌[q] a b‖ ^ 2) ≤ R.C) →
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ a, ∑ b, ‖(1 - (u : ℂ) • pairQ (gammaG q.g) 𝐌[q])⁻¹ a b‖ ≤ R.C) →
      (∀ x y, 0 ≤ mixedKer 𝐏[q] q.s x y ∧ mixedKer 𝐏[q] q.s x y ≤
        R.C / ((1 - q.s) * ellProp q.g q.L q.s) *
          Real.exp (-(R.c * cycDist x y / ellProp q.g q.L q.s)) +
          (ellProp q.g q.L q.s)⁻¹ * (W : ℝ) ^ (-Ak)) →
      (∀ x y, 0 ≤ mixedKer 𝐏[q] q.u x y ∧ mixedKer 𝐏[q] q.u x y ≤
        R.C / ((1 - q.u) * ellProp q.g q.L q.u) *
          Real.exp (-(R.c * cycDist x y / ellProp q.g q.L q.u)) +
          (ellProp q.g q.L q.u)⁻¹ * (W : ℝ) ^ (-Ak)) →
      (∀ x y y', |mixedKer 𝐏[q] q.u x y - mixedKer 𝐏[q] q.u x y'| ≤
        Ci / ((1 - q.u) * ellProp q.g q.L q.u) * ((cycDist y y' : ℝ) / ellProp q.g q.L q.u) +
          (ellProp q.g q.L q.u)⁻¹ * (W : ℝ) ^ (-Ak)) →
      (4 * (W : ℝ) ^ ν + 2) * (1 + (1 - q.s) / (1 - q.u)) * (q.L / ellProp q.g q.L q.s) ≤ Pm →
      1 ≤ Pm →
      (∀ w : Word (n + 1) q.L, ‖flowErr W (q.at q.s) w.1 w.2 ω‖ ≤
        (W : ℝ) ^ ν * zetaProp q.g W q.L q.s ^ (n + 1)) →
      (∀ w : Word (n + 1) q.L, (W : ℝ) ^ ν * ellProp q.g q.L q.s < wordDiam w.1 →
        ‖loopTr (flowG W (q.at q.s) ω) w.1 w.2‖ + ‖flowErr W (q.at q.s) w.1 w.2 ω‖ ≤ τ) →
      ‖∑ b : Fin (n + 1) → Fin q.L, (∏ j, pairU (gammaG q.g) 𝐌[q] q.s q.u (σ j)
          (σ (finRotate (n + 1) j)) (a j) (b j)) * flowErr W (q.at q.s) b σ ω‖ ≤
        Cn * ((4 * (W : ℝ) ^ ν + 2) ^ (2 * (n + 1)) + 1) * zetaProp q.g W q.L q.u ^ (n + 1) *
          (W : ℝ) ^ ν + Cn * Pm ^ (4 * (n + 1)) * τ := by
  obtain ⟨Cn, hCn, h⟩ := coneRates_fieldStable (n + 1) (by omega) (R.C + Ci + 1)
    (by linarith [R.one_le_C])
  refine ⟨Cn, hCn, ?_⟩
  intro W q Ak ν τ Pm ω σ a hσ hW hAk hν hτ hs hsu hu1 hL hg hm hdy1 hdy2 hKs hKv hIv hPm hPm1
    hX hXτ
  have hs0 : 0 ≤ q.s := by linarith
  have hs1 : q.s < 1 := lt_of_le_of_lt hsu hu1
  have hL1 : 1 ≤ q.L := by omega
  have hℓs := coneNode_ell_ge_one hg hL1 q.s
  set P := (W : ℝ) ^ ν with hP
  set H := 4 * P + 2 with hH
  set ρ := (1 - q.s) / (1 - q.u) with hρ
  have hP1 : 1 ≤ P := Real.one_le_rpow (by exact_mod_cast hW) hν.le
  have hH1 : 1 ≤ H := by linarith
  have hρ0 : 0 ≤ ρ := div_nonneg (by linarith) (by linarith)
  have hk3 := (coneNode_kernel_premises R Ci hCi W q q.s q.u Ak H hW hAk hs hsu hu1 hL hg hKs hKv
    hIv).2.2.1
  have hdy1' : ∀ x, gammaG q.g * ∑ y, ‖𝐌[q] x y‖ ^ 2 ≤ R.C + Ci + 1 := by
    intro x
    refine le_trans ?_ ((hdy1 x).trans (by linarith))
    have hγ := coneNode_gamma_pos q.g
    gcongr with y
    exact le_add_of_nonneg_left (norm_nonneg _)
  have hζs0 : 0 ≤ zetaProp q.g W q.L q.s := (coneNode_zeta_pos hg hW hL1 hs1).le
  have hb := h q.g q.E 𝐦[q] q.L hL hm q.s q.u ρ (ellProp q.g q.L q.s) (ellProp q.g q.L q.u) H
    (P * ellProp q.g q.L q.s) τ (P * zetaProp q.g W q.L q.s ^ (n + 1)) σ
    (fun b => flowErr W (q.at q.s) b σ ω) a hσ hs0 hsu hu1 le_rfl hℓs
    (coneNode_ell_mono hg q.L hsu hu1) (coneNode_ell_le q.s) hH1
    (coneNode_rho_ell hg hL1 hsu hu1) (by positivity) (by nlinarith) hτ hk3 hdy1'
    (fun x => (hdy2 q.u (by linarith) hu1.le x).trans (by linarith)) (fun b => hX (b, σ))
    (fun b hb => (le_add_of_nonneg_left (norm_nonneg _)).trans (hXτ (b, σ) hb))
  refine hb.trans ?_
  have hpre := coneNode_pref_stable (n + 1) (by omega)
    (ρ * ellProp q.g q.L q.s / ellProp q.g q.L q.u) (zetaProp q.g W q.L q.s)
    (zetaProp q.g W q.L q.u) (coneNode_zeta_rho hg hW hL1 hsu hu1) hζs0
    (coneNode_zeta_mono hg hW hL1 hsu hu1)
  have hH2 : H ^ (n + 1 - 1) ≤ H ^ (2 * (n + 1)) + 1 := by
    have := pow_le_pow_right₀ hH1 (show n + 1 - 1 ≤ 2 * (n + 1) by omega)
    linarith
  have hx0 : 0 ≤ ρ * ellProp q.g q.L q.s / ellProp q.g q.L q.u := by
    have := coneNode_rho_ell hg hL1 hsu hu1
    linarith
  have h1 : Cn * H ^ (n + 1 - 1) * (ρ * ellProp q.g q.L q.s / ellProp q.g q.L q.u) ^ (n + 1 - 1) *
      (P * zetaProp q.g W q.L q.s ^ (n + 1)) ≤
      Cn * (H ^ (2 * (n + 1)) + 1) * zetaProp q.g W q.L q.u ^ (n + 1) * P := by
    calc Cn * H ^ (n + 1 - 1) * (ρ * ellProp q.g q.L q.s / ellProp q.g q.L q.u) ^ (n + 1 - 1) *
        (P * zetaProp q.g W q.L q.s ^ (n + 1)) =
        Cn * H ^ (n + 1 - 1) * ((ρ * ellProp q.g q.L q.s / ellProp q.g q.L q.u) ^ (n + 1 - 1) *
          zetaProp q.g W q.L q.s ^ (n + 1)) * P := by ring
      _ ≤ Cn * (H ^ (2 * (n + 1)) + 1) * zetaProp q.g W q.L q.u ^ (n + 1) * P := by
        gcongr
  have h𝔓 : (1 + ρ) * (q.L / ellProp q.g q.L q.s) ≤ Pm := by
    refine le_trans ?_ hPm
    have : 0 ≤ (1 + ρ) * (q.L / ellProp q.g q.L q.s) := by positivity
    nlinarith
  have h2 : Cn * ((1 + ρ) * (q.L / ellProp q.g q.L q.s)) ^ (n + 1) * τ ≤
      Cn * Pm ^ (4 * (n + 1)) * τ := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hCn.le) hτ
    exact (pow_le_pow_left₀ (by positivity) h𝔓 _).trans
      (pow_le_pow_right₀ hPm1 (by omega))
  linarith

/-- The restored Ward row of a cyclically alternating word at the terminal time `u`:
`|h_u(a₀) Π_j θ_u(a₀ - a_j)|`, with the row (C.34) [gc:eq:row] bounded through the loop errors of
length `n` and their tails. -/
private lemma coneNode_row (R : PropRegime) (n : ℕ) (hn : 1 ≤ n) (W : ℕ) (q : StepPt)
    (A ν τ Lb Zc : ℝ) (ω : Ω W q.L) (σ : Fin (n + 1) → Bool) (a : Fin (n + 1) → Fin q.L)
    (Ed : ℕ → ℝ) (hW : 1 ≤ W) (hA : 0 < A) (hν : 0 < ν) (hτ : 0 ≤ τ) (hu : 1 / 2 ≤ q.u)
    (hu1 : q.u < 1) (hσ : ∀ j, σ (finRotate (n + 1) j) = !σ j) (hL : 3 ≤ q.L) (hg : 0 ≤ q.g)
    (hm : IsDysonRootV (hopB q.g) (gammaG q.g) q.L q.E 𝐦[q]) (hmim : R.C⁻¹ ≤ (𝐦[q]).im)
    (hKu : ∀ x y, 0 ≤ mixedKer 𝐏[q] q.u x y ∧ mixedKer 𝐏[q] q.u x y ≤
      R.C / ((1 - q.u) * ellProp q.g q.L q.u) *
        Real.exp (-(R.c * cycDist x y / ellProp q.g q.L q.u)) +
        (ellProp q.g q.L q.u)⁻¹ * (W : ℝ) ^ (-A))
    (hLb : q.L / ellProp q.g q.L q.u ≤ Lb) (hZc : zetaProp q.g W q.L q.u ≤ Zc) (hEd : 0 ≤ Ed n)
    (hX : ∀ w : Word n q.L, ‖flowErr W (q.at q.u) w.1 w.2 ω‖ ≤
      (W : ℝ) ^ ν * (Ed n * zetaProp q.g W q.L q.u ^ n))
    (hXτ : ∀ w : Word n q.L, (W : ℝ) ^ ν * ellProp q.g q.L q.u < wordDiam w.1 →
      ‖loopTr (flowG W (q.at q.u) ω) w.1 w.2‖ + ‖flowErr W (q.at q.u) w.1 w.2 ω‖ ≤ τ) :
    ‖rowSum (fun b => flowErr W (q.at q.u) b σ ω) (a 0) *
        ∏ j : Fin n, ((wardProfile 𝐏[q] q.u (a 0 - a j.succ) : ℝ) : ℂ)‖ ≤
      R.C * (R.C + 1) ^ n * 3 ^ (n - 1) * ((W : ℝ) ^ ν) ^ n * Ed n *
          zetaProp q.g W q.L q.u ^ (n + 1) +
        R.C * (R.C + 1) ^ n * Zc * Lb ^ (n - 1) * τ := by
  have hu0 : 0 ≤ q.u := by linarith
  have hL1 : 1 ≤ q.L := by omega
  have hRC := R.one_le_C
  set ℓ := ellProp q.g q.L q.u with hℓ
  set ζ := zetaProp q.g W q.L q.u with hζ
  set P := (W : ℝ) ^ ν with hP
  have hℓ1 : 1 ≤ ℓ := coneNode_ell_ge_one hg hL1 q.u
  have hℓ0 : 0 < ℓ := by linarith
  have hP1 : 1 ≤ P := Real.one_le_rpow (by exact_mod_cast hW) hν.le
  have hζ0 : 0 ≤ ζ := (coneNode_zeta_pos hg hW hL1 hu1).le
  have hmpos : 0 < (𝐦[q]).im := lt_of_lt_of_le (by positivity) hmim
  have him : ((𝐦[q]).im)⁻¹ ≤ R.C := by
    rw [inv_le_comm₀ hmpos (by positivity)]; exact hmim
  have hσl : σ (Fin.last n) = !σ 0 := by
    have := hσ (Fin.last n)
    rw [show finRotate (n + 1) (Fin.last n) = 0 from finRotate_last] at this
    rw [this, Bool.not_not]
  have hrow := coneRates_rowWard q.g q.E 𝐦[q] hW hL hn hm (flowH_isHermitian _ _ _ _ _) hu0 hu1
    (P * (Ed n * ζ ^ n)) (P * ℓ) τ (by positivity) hτ (fun b s => hX (b, s))
    (fun b s hb => (le_add_of_nonneg_left (norm_nonneg _)).trans (hXτ (b, s) hb)) σ hσl (a 0)
  -- the profile factors
  have hθ : ∀ x y : Fin q.L, 0 ≤ wardProfile 𝐏[q] q.u (x - y) ∧
      wardProfile 𝐏[q] q.u (x - y) ≤ (R.C + 1) / ℓ := by
    intro x y
    have hf := ((wardProfile_facts q.g q.L hL q.E 𝐦[q] hm).1 q.u ⟨by linarith, hu1⟩ x y).2.1
    rw [hf]
    have hb := coneNode_ker_bulk hW hA.le (by linarith) hu0 hu1 hℓ1
      (mul_nonneg R.c_pos.le (Nat.cast_nonneg _)) (hKu y x).2
    have h1u : 0 < 1 - q.u := by linarith
    refine ⟨mul_nonneg h1u.le (hKu y x).1, ?_⟩
    calc (1 - q.u) * mixedKer 𝐏[q] q.u y x ≤ (1 - q.u) * ((R.C + 1) / ((1 - q.u) * ℓ)) :=
          mul_le_mul_of_nonneg_left hb h1u.le
      _ = (R.C + 1) / ℓ := by field_simp
  have hprod : ‖∏ j : Fin n, ((wardProfile 𝐏[q] q.u (a 0 - a j.succ) : ℝ) : ℂ)‖ ≤
      ((R.C + 1) / ℓ) ^ n := by
    rw [norm_prod]
    calc ∏ j : Fin n, ‖((wardProfile 𝐏[q] q.u (a 0 - a j.succ) : ℝ) : ℂ)‖ ≤
        ∏ _j : Fin n, (R.C + 1) / ℓ := by
          refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ => ?_
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hθ _ _).1]
          exact (hθ _ _).2
      _ = ((R.C + 1) / ℓ) ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hη : ((W : ℝ) * etaChar q.g 𝐦[q] q.u)⁻¹ ≤ R.C * ζ * ℓ := by
    have e := coneNode_eta hg hW hL1 hu1 _ hmpos
    have : ((W : ℝ) * etaChar q.g 𝐦[q] q.u)⁻¹ = ((W : ℝ) * etaChar q.g 𝐦[q] q.u * ℓ)⁻¹ * ℓ := by
      field_simp
    rw [this, e, div_eq_mul_inv]
    have := mul_le_mul_of_nonneg_left him hζ0
    nlinarith
  have hd : 2 * (P * ℓ) + 1 ≤ 3 * (P * ℓ) := by nlinarith
  rw [norm_mul]
  have hrow0 : 0 ≤ ‖rowSum (fun b => flowErr W (q.at q.u) b σ ω) (a 0)‖ := norm_nonneg _
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hrow ⊢
  have hη0 : 0 ≤ ((W : ℝ) * etaChar q.g 𝐦[q] q.u)⁻¹ := by
    have : 0 ≤ etaChar q.g 𝐦[q] q.u := by
      unfold etaChar
      have := coneNode_gamma_pos q.g
      have : 0 ≤ 1 - q.u := by linarith
      positivity
    positivity
  have hLq : (q.L : ℝ) ≤ Lb * ℓ := by
    have := hLb
    rwa [div_le_iff₀ hℓ0] at this
  have hrow' : ‖rowSum (fun b => flowErr W (q.at q.u) b σ ω) (a 0)‖ ≤
      R.C * ζ * ℓ * ((3 * (P * ℓ)) ^ m * (P * (Ed (m + 1) * ζ ^ (m + 1))) +
        (Lb * ℓ) ^ m * τ) := by
    refine hrow.trans (mul_le_mul hη ?_ (by positivity) (by positivity))
    have h1 : (2 * (P * ℓ) + 1) ^ m ≤ (3 * (P * ℓ)) ^ m := pow_le_pow_left₀ (by positivity) hd m
    have h2 : (q.L : ℝ) ^ m ≤ (Lb * ℓ) ^ m := pow_le_pow_left₀ (by positivity) hLq m
    have h3 : 0 ≤ P * (Ed (m + 1) * ζ ^ (m + 1)) := by positivity
    nlinarith
  have hθ0 : 0 ≤ ((R.C + 1) / ℓ) ^ (m + 1) := by positivity
  calc ‖rowSum (fun b => flowErr W (q.at q.u) b σ ω) (a 0)‖ *
      ‖∏ j : Fin (m + 1), ((wardProfile 𝐏[q] q.u (a 0 - a j.succ) : ℝ) : ℂ)‖ ≤
      R.C * ζ * ℓ * ((3 * (P * ℓ)) ^ m * (P * (Ed (m + 1) * ζ ^ (m + 1))) +
        (Lb * ℓ) ^ m * τ) * ((R.C + 1) / ℓ) ^ (m + 1) :=
        mul_le_mul hrow' hprod (norm_nonneg _) (mul_nonneg (by positivity)
          (add_nonneg (mul_nonneg (by positivity) (mul_nonneg (by positivity)
            (mul_nonneg hEd (by positivity))))
            (mul_nonneg (pow_nonneg (mul_nonneg (le_trans (by positivity) hLb) hℓ0.le) _) hτ)))
    _ = R.C * ζ * (3 ^ m * P ^ (m + 1) * Ed (m + 1) * ζ ^ (m + 1) + Lb ^ m * τ) *
          (((R.C + 1) / ℓ) ^ (m + 1) * ℓ ^ (m + 1)) := by ring
    _ = R.C * ζ * (3 ^ m * P ^ (m + 1) * Ed (m + 1) * ζ ^ (m + 1) + Lb ^ m * τ) *
          (R.C + 1) ^ (m + 1) := by
        rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hℓ0.ne')]
    _ = R.C * (R.C + 1) ^ (m + 1) * 3 ^ m * P ^ (m + 1) * Ed (m + 1) * ζ ^ (m + 1 + 1) +
        R.C * (R.C + 1) ^ (m + 1) * ζ * Lb ^ m * τ := by ring
    _ ≤ R.C * (R.C + 1) ^ (m + 1) * 3 ^ m * P ^ (m + 1) * Ed (m + 1) * ζ ^ (m + 1 + 1) +
        R.C * (R.C + 1) ^ (m + 1) * Zc * Lb ^ m * τ := by
        have hLb0 : 0 ≤ Lb := le_trans (by positivity) hLb
        gcongr


/-! ### Polynomial growth in `W` -/

/-- `f(W)` is at most polynomial in `W` for large `W`. -/
private def coneNode_Poly (f : ℕ → ℝ) : Prop :=
  ∃ c e : ℝ, ∀ᶠ W : ℕ in atTop, |f W| ≤ c * (W : ℝ) ^ e

private lemma coneNode_poly_const (a : ℝ) : coneNode_Poly fun _ => a :=
  ⟨|a|, 0, Filter.Eventually.of_forall fun W => by simp⟩

private lemma coneNode_poly_rpow (e : ℝ) : coneNode_Poly fun W => (W : ℝ) ^ e :=
  ⟨1, e, Filter.Eventually.of_forall fun W => by
    rw [one_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg W) e)]⟩

private lemma coneNode_poly_add {f g : ℕ → ℝ} (hf : coneNode_Poly f) (hg : coneNode_Poly g) :
    coneNode_Poly fun W => f W + g W := by
  obtain ⟨c₁, e₁, h₁⟩ := hf
  obtain ⟨c₂, e₂, h₂⟩ := hg
  refine ⟨|c₁| + |c₂|, max e₁ e₂, ?_⟩
  filter_upwards [h₁, h₂, Filter.eventually_ge_atTop 1] with W hW₁ hW₂ hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have a1 : (W : ℝ) ^ e₁ ≤ (W : ℝ) ^ max e₁ e₂ :=
    Real.rpow_le_rpow_of_exponent_le hW1 (le_max_left _ _)
  have a2 : (W : ℝ) ^ e₂ ≤ (W : ℝ) ^ max e₁ e₂ :=
    Real.rpow_le_rpow_of_exponent_le hW1 (le_max_right _ _)
  have p1 : 0 ≤ (W : ℝ) ^ e₁ := Real.rpow_nonneg (Nat.cast_nonneg W) _
  have p2 : 0 ≤ (W : ℝ) ^ e₂ := Real.rpow_nonneg (Nat.cast_nonneg W) _
  have b1 : c₁ * (W : ℝ) ^ e₁ ≤ |c₁| * (W : ℝ) ^ max e₁ e₂ :=
    (mul_le_mul_of_nonneg_right (le_abs_self c₁) p1).trans
      (mul_le_mul_of_nonneg_left a1 (abs_nonneg _))
  have b2 : c₂ * (W : ℝ) ^ e₂ ≤ |c₂| * (W : ℝ) ^ max e₁ e₂ :=
    (mul_le_mul_of_nonneg_right (le_abs_self c₂) p2).trans
      (mul_le_mul_of_nonneg_left a2 (abs_nonneg _))
  calc |f W + g W| ≤ |f W| + |g W| := abs_add_le _ _
    _ ≤ _ := by linarith

private lemma coneNode_poly_mul {f g : ℕ → ℝ} (hf : coneNode_Poly f) (hg : coneNode_Poly g) :
    coneNode_Poly fun W => f W * g W := by
  obtain ⟨c₁, e₁, h₁⟩ := hf
  obtain ⟨c₂, e₂, h₂⟩ := hg
  refine ⟨c₁ * c₂, e₁ + e₂, ?_⟩
  filter_upwards [h₁, h₂, Filter.eventually_ge_atTop 1] with W hW₁ hW₂ hW
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  rw [abs_mul, Real.rpow_add hW0]
  calc |f W| * |g W| ≤ (c₁ * (W : ℝ) ^ e₁) * (c₂ * (W : ℝ) ^ e₂) :=
        mul_le_mul hW₁ hW₂ (abs_nonneg _) ((abs_nonneg _).trans hW₁)
    _ = c₁ * c₂ * ((W : ℝ) ^ e₁ * (W : ℝ) ^ e₂) := by ring

private lemma coneNode_poly_pow {f : ℕ → ℝ} (hf : coneNode_Poly f) (k : ℕ) :
    coneNode_Poly fun W => f W ^ k := by
  induction k with
  | zero => simpa using coneNode_poly_const 1
  | succ k ih => simpa [pow_succ] using coneNode_poly_mul ih hf

private lemma coneNode_poly_log : coneNode_Poly fun W => Real.log W :=
  ⟨1, 1, by
    filter_upwards [Filter.eventually_ge_atTop 1] with W hW
    have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
    rw [abs_of_nonneg (Real.log_nonneg hW1), one_mul, Real.rpow_one]
    exact (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)⟩

/-- A polynomial in `W` times `W^{-A}` is at most `W^{-m}` for large `W` once `A` is large. -/
private lemma coneNode_poly_tail {f : ℕ → ℝ} (hf : coneNode_Poly f) (m : ℝ) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
      ∀ᶠ W : ℕ in atTop, |f W| * (W : ℝ) ^ (-A) ≤ (W : ℝ) ^ (-m) := by
  obtain ⟨c, e, h⟩ := hf
  refine ⟨|e| + |m| + 1, by positivity, fun A hA => ?_⟩
  filter_upwards [h, Filter.eventually_ge_atTop ⌈max c 1⌉₊] with W hW hWc
  have hWc' : max c 1 ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hWc)
  have hW1 : (1 : ℝ) ≤ W := (le_max_right c 1).trans hWc'
  have hW0 : (0 : ℝ) < W := by linarith
  have hcW : c ≤ (W : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]; exact (le_max_left c 1).trans hWc'
  have hWA : 0 ≤ (W : ℝ) ^ (-A) := Real.rpow_nonneg hW0.le _
  calc |f W| * (W : ℝ) ^ (-A) ≤ c * (W : ℝ) ^ e * (W : ℝ) ^ (-A) :=
        mul_le_mul_of_nonneg_right hW hWA
    _ ≤ (W : ℝ) ^ (1 : ℝ) * (W : ℝ) ^ e * (W : ℝ) ^ (-A) := by
        gcongr
    _ = (W : ℝ) ^ (1 + e + -A) := by rw [Real.rpow_add hW0, Real.rpow_add hW0]
    _ ≤ (W : ℝ) ^ (-m) := by
        apply Real.rpow_le_rpow_of_exponent_le hW1
        have := le_abs_self e
        have := le_abs_self m
        linarith

/-- A polynomial in `W` times `e^{-bW^ν}` is at most `1/2` for large `W`. -/
private lemma coneNode_poly_exp {f : ℕ → ℝ} (hf : coneNode_Poly f) {b ν : ℝ} (hb : 0 < b)
    (hν : 0 < ν) : ∀ᶠ W : ℕ in atTop, |f W| * Real.exp (-(b * (W : ℝ) ^ ν)) ≤ 1 / 2 := by
  obtain ⟨c, e, h⟩ := hf
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (e / ν) b hb).comp
    ((tendsto_rpow_atTop hν).comp tendsto_natCast_atTop_atTop)
  have hpos : (0 : ℝ) < 1 / (2 * (|c| + 1)) := by positivity
  have hev := ht.eventually (gt_mem_nhds hpos)
  filter_upwards [h, hev, Filter.eventually_ge_atTop 1] with W hW hW' hW1
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  simp only [Function.comp] at hW'
  have he : ((W : ℝ) ^ ν) ^ (e / ν) = (W : ℝ) ^ e := by
    rw [← Real.rpow_mul hW0, mul_div_cancel₀ _ hν.ne']
  rw [he] at hW'
  have hx : 0 ≤ (W : ℝ) ^ e * Real.exp (-b * (W : ℝ) ^ ν) :=
    mul_nonneg (Real.rpow_nonneg hW0 _) (Real.exp_pos _).le
  have hc1 : c ≤ |c| + 1 := by linarith [le_abs_self c]
  calc |f W| * Real.exp (-(b * (W : ℝ) ^ ν)) ≤ c * (W : ℝ) ^ e * Real.exp (-b * (W : ℝ) ^ ν) := by
        rw [neg_mul]
        exact mul_le_mul_of_nonneg_right hW (Real.exp_pos _).le
    _ = c * ((W : ℝ) ^ e * Real.exp (-b * (W : ℝ) ^ ν)) := by ring
    _ ≤ (|c| + 1) * (1 / (2 * (|c| + 1))) := by
        apply mul_le_mul hc1 hW'.le hx (by positivity)
    _ = 1 / 2 := by field_simp


/-! ### The final normalization -/

private lemma coneNode_sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  nlinarith [mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- The constant of the final normalization. -/
private def coneNode_Cfin (n p : ℕ) (ν Ci Cβ RC : ℝ) : ℝ :=
  2 * (Ci * (2 * 6 ^ (2 * (n + 1))) + 2 +
    Real.sqrt ((2 * p - 1) * (Cβ * (2 * 6 ^ (4 * (n + 1))) * (3 / ν))) + 2 +
    Cβ * (2 * 6 ^ (2 * (n + 1))) * (3 / ν) * (2 * (n + 1) + 1 + RC) + 2 +
    RC * (RC + 1) ^ n * 3 ^ (n - 1) + 2)

/-- The terms of the moment bound of `D_{n+1}(u)` are at most `C W^δ ζ_u^{n+1}` times the
envelope once the tails are at most `ζ_u^{n+1}` (or `ζ_u^{2(n+1)}` under a square root). -/
private lemma coneNode_final (n p : ℕ) (hp : 1 ≤ p) (W : ℕ) (hW : 1 ≤ W) (δ ν : ℝ) (hν : 0 < ν)
    (hνδ : (2 * n + 5) * ν ≤ δ)
    (Ci Cβ RC ζ Env B₂ Edn Lg Pm τ Tc γWL K K0 δb δ0 δr Zc Lb : ℝ)
    (hCi : 0 ≤ Ci) (hCβ : 0 ≤ Cβ) (hRC : 1 ≤ RC) (hζ : 0 ≤ ζ) (hEnv : 1 ≤ Env) (hB₂ : 0 ≤ B₂)
    (hsB : Real.sqrt B₂ ≤ Env) (hEdn0 : 0 ≤ Edn) (hEdn : Edn ≤ Env) (hLg : 0 ≤ Lg)
    (hLg3 : Lg ≤ 3 * Real.log W) (hPm : 0 ≤ Pm) (hτ : 0 ≤ τ) (_hTc : 0 ≤ Tc) (hγWL : 0 ≤ γWL)
    (_hK : 0 ≤ K) (_hδb : 0 ≤ δb)
    (F1 : Ci * Pm ^ (4 * (n + 1)) * τ ≤ ζ ^ (n + 1))
    (F2 : K0 * δ0 ^ (1 / (4 * (p : ℝ))) ≤ ζ ^ (n + 1))
    (F3 : (2 * p - 1) * (Cβ * Pm ^ (8 * (n + 1)) * (γWL * τ) * Lg) ≤ (ζ ^ (n + 1)) ^ 2)
    (F4 : (2 * p - 1) * (K * δb ^ (1 / (2 * (p : ℝ)))) ≤ (ζ ^ (n + 1)) ^ 2)
    (F5 : Cβ * Pm ^ (4 * (n + 1)) * (τ * Tc) * Lg ≤ ζ ^ (n + 1))
    (F6 : K * δb ^ (1 / (4 * (p : ℝ))) ≤ ζ ^ (n + 1))
    (F7 : RC * (RC + 1) ^ n * Zc * Lb ^ (n - 1) * τ ≤ ζ ^ (n + 1))
    (F8 : K0 * δr ^ (1 / (4 * (p : ℝ))) ≤ ζ ^ (n + 1)) :
    2 * ((Ci * ((4 * (W : ℝ) ^ ν + 2) ^ (2 * (n + 1)) + 1) * ζ ^ (n + 1) * (W : ℝ) ^ ν +
          Ci * Pm ^ (4 * (n + 1)) * τ + K0 * δ0 ^ (1 / (4 * (p : ℝ))) +
        Real.sqrt ((2 * p - 1) * (coneNode_Kb n Cβ (4 * (W : ℝ) ^ ν + 2) ((W : ℝ) ^ ν) Pm
          ζ B₂ γWL τ * Lg)) +
        Real.sqrt ((2 * p - 1) * (K * δb ^ (1 / (2 * (p : ℝ))))) +
        coneNode_Kβ n Cβ RC (4 * (W : ℝ) ^ ν + 2) ((W : ℝ) ^ ν) Pm ζ Env Tc τ * Lg +
        K * δb ^ (1 / (4 * (p : ℝ)))) +
      (RC * (RC + 1) ^ n * 3 ^ (n - 1) * ((W : ℝ) ^ ν) ^ n * Edn * ζ ^ (n + 1) +
        RC * (RC + 1) ^ n * Zc * Lb ^ (n - 1) * τ + K0 * δr ^ (1 / (4 * (p : ℝ))))) ≤
      coneNode_Cfin n p ν Ci Cβ RC * ((W : ℝ) ^ δ * (ζ ^ (n + 1) * Env)) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) ≤ W := by linarith
  have hP1 : 1 ≤ (W : ℝ) ^ ν := Real.one_le_rpow hW1 hν.le
  have hδ0 : 0 ≤ δ := le_trans (by positivity) hνδ
  have hWδ1 : 1 ≤ (W : ℝ) ^ δ := Real.one_le_rpow hW1 hδ0
  have hPk : ∀ k : ℕ, (k : ℝ) * ν ≤ δ → ((W : ℝ) ^ ν) ^ k ≤ (W : ℝ) ^ δ := by
    intro k hk
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0]
    exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hLgP : Lg ≤ 3 / ν * (W : ℝ) ^ ν := by
    have := Real.log_le_rpow_div hW0 hν
    calc Lg ≤ 3 * Real.log W := hLg3
      _ ≤ 3 * ((W : ℝ) ^ ν / ν) := by gcongr
      _ = 3 / ν * (W : ℝ) ^ ν := by ring
  have hζ2 : ζ ^ (2 * (n + 1)) = (ζ ^ (n + 1)) ^ 2 := by rw [← pow_mul]; ring_nf
  unfold coneNode_Kb coneNode_Kβ coneNode_Cfin
  rw [hζ2]
  have hPk1 := hPk (2 * n + 3) (by push_cast; nlinarith)
  have hPk2 := hPk (2 * n + 5) (by push_cast; nlinarith)
  have hPk3 := hPk n (by nlinarith)
  have hZ0 : 0 ≤ ζ ^ (n + 1) := pow_nonneg hζ _
  generalize (W : ℝ) ^ ν = P at *
  generalize (W : ℝ) ^ δ = Wδ at *
  generalize ζ ^ (n + 1) = Z at *
  have hHk : ∀ k : ℕ, (4 * P + 2) ^ k + 1 ≤ 2 * 6 ^ k * P ^ k := by
    intro k
    have h1 : (4 * P + 2) ^ k ≤ (6 * P) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
    have h2 : (1 : ℝ) ≤ 6 ^ k * P ^ k := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
      (one_le_pow₀ hP1)
    rw [mul_pow] at h1
    linarith
  have hH0 : 0 ≤ 4 * P + 2 := by linarith
  generalize 4 * P + 2 = H at *
  have hWδ0 : 0 ≤ Wδ := by linarith
  have hB : Z ≤ Wδ * (Z * Env) :=
    (le_mul_of_one_le_right hZ0 hEnv).trans (le_mul_of_one_le_left (mul_nonneg hZ0
      (by linarith)) hWδ1)
  have h2p : (0 : ℝ) ≤ 2 * p - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hP0 : 0 ≤ P := by linarith
  -- the initial term
  have t1 : Ci * (H ^ (2 * (n + 1)) + 1) * Z * P ≤
      Ci * (2 * 6 ^ (2 * (n + 1))) * (Wδ * (Z * Env)) := by
    have h1 : (H ^ (2 * (n + 1)) + 1) * P ≤ 2 * 6 ^ (2 * (n + 1)) * Wδ := by
      calc (H ^ (2 * (n + 1)) + 1) * P ≤ 2 * 6 ^ (2 * (n + 1)) * P ^ (2 * (n + 1)) * P :=
            mul_le_mul_of_nonneg_right (hHk _) hP0
        _ = 2 * 6 ^ (2 * (n + 1)) * P ^ (2 * n + 3) := by ring
        _ ≤ 2 * 6 ^ (2 * (n + 1)) * Wδ := mul_le_mul_of_nonneg_left hPk1 (by positivity)
    have h2 : Z ≤ Z * Env := le_mul_of_one_le_right hZ0 hEnv
    calc Ci * (H ^ (2 * (n + 1)) + 1) * Z * P = Ci * ((H ^ (2 * (n + 1)) + 1) * P) * Z := by ring
      _ ≤ Ci * (2 * 6 ^ (2 * (n + 1)) * Wδ) * (Z * Env) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hCi) h2 hZ0 (by positivity)
      _ = _ := by ring
  -- the bracket term
  set c2 := (2 * (p : ℝ) - 1) * (Cβ * (2 * 6 ^ (4 * (n + 1))) * (3 / ν)) with hc2
  have hc20 : 0 ≤ c2 := by positivity
  have hHk4 := hHk (4 * (n + 1))
  have hH40 : 0 ≤ H ^ (4 * (n + 1)) + 1 := by positivity
  have ha : (2 * (p : ℝ) - 1) * (Cβ * (H ^ (4 * (n + 1)) + 1) * Z ^ 2 * (P * B₂) * Lg) ≤
      c2 * (Wδ * Z) ^ 2 * B₂ := by
    have h1 : (H ^ (4 * (n + 1)) + 1) * P * Lg ≤ 2 * 6 ^ (4 * (n + 1)) * (3 / ν) * Wδ ^ 2 := by
      calc (H ^ (4 * (n + 1)) + 1) * P * Lg ≤
          2 * 6 ^ (4 * (n + 1)) * P ^ (4 * (n + 1)) * P * (3 / ν * P) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hHk4 hP0) hLgP hLg (by positivity)
        _ = 2 * 6 ^ (4 * (n + 1)) * (3 / ν) * (P ^ (2 * n + 3)) ^ 2 := by ring
        _ ≤ 2 * 6 ^ (4 * (n + 1)) * (3 / ν) * Wδ ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hPk1 2) (by positivity)
    calc (2 * (p : ℝ) - 1) * (Cβ * (H ^ (4 * (n + 1)) + 1) * Z ^ 2 * (P * B₂) * Lg) =
        (2 * p - 1) * Cβ * ((H ^ (4 * (n + 1)) + 1) * P * Lg) * (Z ^ 2 * B₂) := by ring
      _ ≤ (2 * p - 1) * Cβ * (2 * 6 ^ (4 * (n + 1)) * (3 / ν) * Wδ ^ 2) * (Z ^ 2 * B₂) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (mul_nonneg h2p hCβ))
            (by positivity)
      _ = c2 * (Wδ * Z) ^ 2 * B₂ := by rw [hc2]; ring
  have ha0 : 0 ≤ (2 * (p : ℝ) - 1) * (Cβ * (H ^ (4 * (n + 1)) + 1) * Z ^ 2 * (P * B₂) * Lg) :=
    mul_nonneg h2p (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCβ hH40) (sq_nonneg Z))
      (mul_nonneg hP0 hB₂)) hLg)
  have hb0 : 0 ≤ (2 * (p : ℝ) - 1) * (Cβ * Pm ^ (8 * (n + 1)) * (γWL * τ) * Lg) := by positivity
  have t2 : Real.sqrt ((2 * p - 1) * ((Cβ * ((H ^ (4 * (n + 1)) + 1) * Z ^ 2 * (P * B₂)) +
      Cβ * Pm ^ (8 * (n + 1)) * (γWL * τ)) * Lg)) ≤ Real.sqrt c2 * (Wδ * (Z * Env)) + Z := by
    have e : (2 * (p : ℝ) - 1) * ((Cβ * ((H ^ (4 * (n + 1)) + 1) * Z ^ 2 * (P * B₂)) +
        Cβ * Pm ^ (8 * (n + 1)) * (γWL * τ)) * Lg) =
        (2 * p - 1) * (Cβ * (H ^ (4 * (n + 1)) + 1) * Z ^ 2 * (P * B₂) * Lg) +
        (2 * p - 1) * (Cβ * Pm ^ (8 * (n + 1)) * (γWL * τ) * Lg) := by ring
    rw [e]
    refine (coneNode_sqrt_add_le ha0 hb0).trans (add_le_add ?_ ?_)
    · calc Real.sqrt ((2 * (p : ℝ) - 1) * (Cβ * (H ^ (4 * (n + 1)) + 1) * Z ^ 2 * (P * B₂) * Lg)) ≤
          Real.sqrt (c2 * (Wδ * Z) ^ 2 * B₂) := Real.sqrt_le_sqrt ha
        _ = Real.sqrt c2 * (Wδ * Z) * Real.sqrt B₂ := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hc20, Real.sqrt_sq (by positivity)]
        _ ≤ Real.sqrt c2 * (Wδ * Z) * Env :=
            mul_le_mul_of_nonneg_left hsB (by positivity)
        _ = Real.sqrt c2 * (Wδ * (Z * Env)) := by ring
    · exact (Real.sqrt_le_sqrt F3).trans (Real.sqrt_sq hZ0).le
  have t3 : Real.sqrt ((2 * p - 1) * (K * δb ^ (1 / (2 * (p : ℝ))))) ≤ Z :=
    (Real.sqrt_le_sqrt F4).trans (Real.sqrt_sq hZ0).le
  -- the drift term
  have hHk2 := hHk (2 * (n + 1))
  have t4 : (Cβ * ((H ^ (2 * (n + 1)) + 1) * Z * P ^ 2 * ((2 * (n + 1) + 1 + RC) * Env)) +
        Cβ * Pm ^ (4 * (n + 1)) * (τ * Tc)) * Lg ≤
      Cβ * (2 * 6 ^ (2 * (n + 1))) * (3 / ν) * (2 * (n + 1) + 1 + RC) * (Wδ * (Z * Env)) + Z := by
    have h1 : (H ^ (2 * (n + 1)) + 1) * P ^ 2 * Lg ≤ 2 * 6 ^ (2 * (n + 1)) * (3 / ν) * Wδ := by
      calc (H ^ (2 * (n + 1)) + 1) * P ^ 2 * Lg ≤
          2 * 6 ^ (2 * (n + 1)) * P ^ (2 * (n + 1)) * P ^ 2 * (3 / ν * P) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hHk2 (by positivity)) hLgP hLg (by positivity)
        _ = 2 * 6 ^ (2 * (n + 1)) * (3 / ν) * P ^ (2 * n + 5) := by ring
        _ ≤ 2 * 6 ^ (2 * (n + 1)) * (3 / ν) * Wδ :=
            mul_le_mul_of_nonneg_left hPk2 (by positivity)
    have hR : 0 ≤ (2 * ((n : ℝ) + 1) + 1 + RC) * Env := by positivity
    have e : (Cβ * ((H ^ (2 * (n + 1)) + 1) * Z * P ^ 2 * ((2 * (n + 1) + 1 + RC) * Env)) +
        Cβ * Pm ^ (4 * (n + 1)) * (τ * Tc)) * Lg =
        Cβ * ((H ^ (2 * (n + 1)) + 1) * P ^ 2 * Lg) * (Z * ((2 * (n + 1) + 1 + RC) * Env)) +
          Cβ * Pm ^ (4 * (n + 1)) * (τ * Tc) * Lg := by ring
    rw [e]
    have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hCβ)
      (mul_nonneg hZ0 hR)
    have e2 : Cβ * (2 * 6 ^ (2 * (n + 1)) * (3 / ν) * Wδ) * (Z * ((2 * (n + 1) + 1 + RC) * Env)) =
        Cβ * (2 * 6 ^ (2 * (n + 1))) * (3 / ν) * (2 * (n + 1) + 1 + RC) * (Wδ * (Z * Env)) := by
      ring
    linarith
  -- the restored row
  have t5 : RC * (RC + 1) ^ n * 3 ^ (n - 1) * P ^ n * Edn * Z ≤
      RC * (RC + 1) ^ n * 3 ^ (n - 1) * (Wδ * (Z * Env)) := by
    have hc : 0 ≤ RC * (RC + 1) ^ n * 3 ^ (n - 1) := by positivity
    calc RC * (RC + 1) ^ n * 3 ^ (n - 1) * P ^ n * Edn * Z =
        RC * (RC + 1) ^ n * 3 ^ (n - 1) * (P ^ n * Edn * Z) := by ring
      _ ≤ RC * (RC + 1) ^ n * 3 ^ (n - 1) * (Wδ * Env * Z) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul hPk3 hEdn hEdn0 hWδ0)
            le_rfl hZ0 (by positivity)) hc
      _ = _ := by ring
  have hBZ : 0 ≤ Wδ * (Z * Env) := by positivity
  linarith [t1, t2, t3, t4, t5, F1, F2, F6, F7, F8, hB]

/-! ### Bookkeeping for the assembly -/

private lemma coneNode_wordDiam_one {L : ℕ} (y : Fin 1 → Fin L) : wordDiam y = 0 := by
  refine Nat.eq_zero_of_le_zero (Finset.sup_le fun p _ => ?_)
  rw [Subsingleton.elim p.1 p.2]
  simp [cycDist]

/-- On an admissible step point, `1 ≤ (1 - s)/(1 - v) ≤ W³` for `s ≤ v ≤ t` and
`ζ_v ≤ W^{|c| + 3|N|}`. -/
private lemma coneNode_adm (R : PropRegime) (c N : ℝ) {W : ℕ} (hW : 1 ≤ W) {q : StepPt}
    (hq : StepAdm R c N W q) (hg : 0 ≤ q.g) (hL : 1 ≤ q.L) {v : ℝ} (hsv : q.s ≤ v)
    (hvt : v ≤ q.t) :
    1 ≤ (1 - q.s) / (1 - v) ∧ (1 - q.s) / (1 - v) ≤ (W : ℝ) ^ (3 : ℝ) ∧
      zetaProp q.g W q.L v ≤ (W : ℝ) ^ (|c| + 3 * |N|) := by
  obtain ⟨-, hs, hsu, hut, hst, hWt, hRN⟩ := hq
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hW3 : 0 < (W : ℝ) ^ (-3 : ℝ) := Real.rpow_pos_of_pos hW0 _
  have ht1 : q.t < 1 := by linarith
  have h1t : 0 < 1 - q.t := by linarith
  have h1v : 0 < 1 - v := by linarith
  have hWW : (W : ℝ) ^ (3 : ℝ) * (W : ℝ) ^ (-3 : ℝ) = 1 := by
    rw [← Real.rpow_add hW0]; simp
  have hinv : (1 - q.t)⁻¹ ≤ (W : ℝ) ^ (3 : ℝ) := by
    rw [inv_le_iff_one_le_mul₀ h1t]
    calc (1 : ℝ) = (W : ℝ) ^ (3 : ℝ) * (W : ℝ) ^ (-3 : ℝ) := hWW.symm
      _ ≤ (W : ℝ) ^ (3 : ℝ) * (1 - q.t) := by gcongr
  have hR1 : ∀ x, q.s ≤ x → x ≤ q.t →
      1 ≤ (1 - q.s) / (1 - x) ∧ (1 - q.s) / (1 - x) ≤ (W : ℝ) ^ (3 : ℝ) := by
    intro x hsx hxt
    have h1x : 0 < 1 - x := by linarith
    refine ⟨by rw [le_div_iff₀ h1x]; linarith, ?_⟩
    calc (1 - q.s) / (1 - x) ≤ 1 / (1 - q.t) := by
          rw [div_le_div_iff₀ h1x h1t]; nlinarith
      _ = (1 - q.t)⁻¹ := one_div _
      _ ≤ _ := hinv
  refine ⟨(hR1 v hsv hvt).1, (hR1 v hsv hvt).2, ?_⟩
  have hζv := coneNode_zeta_mono hg hW hL hvt ht1
  refine hζv.trans ?_
  obtain ⟨hR1t, hRWt⟩ := hR1 q.t hst.le le_rfl
  have hRpos : 0 < q.ratio := lt_of_lt_of_le one_pos hR1t
  have hRN0 : 0 < q.ratio ^ N := Real.rpow_pos_of_pos hRpos _
  have hζt : zetaProp q.g W q.L q.t ≤ (W : ℝ) ^ (-c) * (q.ratio ^ N)⁻¹ := by
    rw [le_mul_inv_iff₀ hRN0, mul_comm]; exact hRN
  have hRinv : (q.ratio ^ N)⁻¹ ≤ (W : ℝ) ^ (3 * |N|) := by
    rw [← Real.rpow_neg hRpos.le]
    calc q.ratio ^ (-N) ≤ q.ratio ^ |N| :=
          Real.rpow_le_rpow_of_exponent_le hR1t (neg_le_abs N)
      _ ≤ ((W : ℝ) ^ (3 : ℝ)) ^ |N| := Real.rpow_le_rpow hRpos.le hRWt (abs_nonneg N)
      _ = (W : ℝ) ^ (3 * |N|) := by rw [← Real.rpow_mul hW0.le]
  have hc : (W : ℝ) ^ (-c) ≤ (W : ℝ) ^ |c| :=
    Real.rpow_le_rpow_of_exponent_le hW1 (neg_le_abs c)
  calc zetaProp q.g W q.L q.t ≤ (W : ℝ) ^ (-c) * (q.ratio ^ N)⁻¹ := hζt
    _ ≤ (W : ℝ) ^ |c| * (W : ℝ) ^ (3 * |N|) :=
        mul_le_mul hc hRinv (inv_pos.2 hRN0).le (Real.rpow_nonneg hW0.le _)
    _ = (W : ℝ) ^ (|c| + 3 * |N|) := by rw [Real.rpow_add hW0]

/-- `C W^{C_K m} ≤ (K_c W^{C_m})^m` for `C ≤ K_c`, `1 ≤ K_c`, `C_K ≤ C_m`. -/
private lemma coneNode_crude_le {C CK Kc CKm : ℝ} {W m : ℕ} (hW : 1 ≤ W) (hm : 1 ≤ m)
    (hC : C ≤ Kc) (hKc : 1 ≤ Kc) (hCK : CK ≤ CKm) :
    C * (W : ℝ) ^ (CK * m) ≤ (Kc * (W : ℝ) ^ CKm) ^ m := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) ≤ W := by linarith
  rw [mul_pow, ← Real.rpow_natCast ((W : ℝ) ^ CKm), ← Real.rpow_mul hW0]
  have h1 : (W : ℝ) ^ (CK * m) ≤ (W : ℝ) ^ (CKm * m) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by gcongr)
  have h2 : C ≤ Kc ^ m := hC.trans (le_self_pow₀ hKc (by omega))
  calc C * (W : ℝ) ^ (CK * m) ≤ Kc ^ m * (W : ℝ) ^ (CK * m) :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hW0 _)
    _ ≤ Kc ^ m * (W : ℝ) ^ (CKm * m) :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg (by linarith) _)

private lemma coneNode_Kβ_mono {n : ℕ} {Cn Cn' RC H P Pm ζu Env Tc Tc' τ : ℝ} (hCn : Cn ≤ Cn')
    (hCn0 : 0 ≤ Cn) (hTc : Tc ≤ Tc') (hH : 0 ≤ H) (_hP : 0 ≤ P) (hPm : 0 ≤ Pm) (hζ : 0 ≤ ζu)
    (hRC : 0 ≤ RC) (hEnv : 0 ≤ Env) (hTc0 : 0 ≤ Tc) (hτ : 0 ≤ τ) :
    coneNode_Kβ n Cn RC H P Pm ζu Env Tc τ ≤ coneNode_Kβ n Cn' RC H P Pm ζu Env Tc' τ := by
  unfold coneNode_Kβ
  have h1 : 0 ≤ (H ^ (2 * (n + 1)) + 1) * ζu ^ (n + 1) * P ^ 2 *
      ((2 * (n + 1) + 1 + RC) * Env) := by
    positivity
  have h2 : Pm ^ (4 * (n + 1)) * (τ * Tc) ≤ Pm ^ (4 * (n + 1)) * (τ * Tc') := by gcongr
  have h3 : 0 ≤ Pm ^ (4 * (n + 1)) * (τ * Tc) := by positivity
  nlinarith

private lemma coneNode_Kb_mono {n : ℕ} {Cn Cn' H P Pm ζu B₂ γWL γWL' τ : ℝ} (hCn : Cn ≤ Cn')
    (hCn0 : 0 ≤ Cn) (hγ : γWL ≤ γWL') (hH : 0 ≤ H) (hP : 0 ≤ P) (hPm : 0 ≤ Pm) (hζ : 0 ≤ ζu)
    (hB : 0 ≤ B₂) (hγ0 : 0 ≤ γWL) (hτ : 0 ≤ τ) :
    coneNode_Kb n Cn H P Pm ζu B₂ γWL τ ≤ coneNode_Kb n Cn' H P Pm ζu B₂ γWL' τ := by
  unfold coneNode_Kb
  have h1 : 0 ≤ (H ^ (4 * (n + 1)) + 1) * ζu ^ (2 * (n + 1)) * (P * B₂) := by positivity
  have h2 : Pm ^ (8 * (n + 1)) * (γWL * τ) ≤ Pm ^ (8 * (n + 1)) * (γWL' * τ) := by gcongr
  have h3 : 0 ≤ Pm ^ (8 * (n + 1)) * (γWL * τ) := by positivity
  nlinarith

/-- The union of `|s|` events of probability at most `x` each. -/
private lemma coneNode_union_le {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') (s : Finset ℕ)
    (E : ℕ → Set Ω') (x : ℝ) (_hx : 0 ≤ x) (h : ∀ j ∈ s, P (E j) ≤ ENNReal.ofReal x) :
    P (⋃ j ∈ s, E j) ≤ ENNReal.ofReal (s.card * x) := by
  refine (measure_biUnion_finset_le s E).trans ?_
  refine (Finset.sum_le_sum h).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_natCast]

/-- `W^{-(2n + 3)} ≤ ((2W)⁻¹)^{2(n+1)}` for `W ≥ 4^{n+1}`. -/
private lemma coneNode_target (n W : ℕ) (hW : 4 ^ (n + 1) ≤ W) :
    (W : ℝ) ^ (-((2 * n + 3 : ℕ) : ℝ)) ≤ ((2 * (W : ℝ))⁻¹) ^ (2 * (n + 1)) := by
  have hW1 : (1 : ℝ) ≤ W := by
    have : 1 ≤ 4 ^ (n + 1) := Nat.one_le_pow _ _ (by norm_num)
    exact_mod_cast this.trans hW
  have hW0 : (0 : ℝ) < W := by linarith
  have h4 : (4 : ℝ) ^ (n + 1) ≤ W := by exact_mod_cast hW
  rw [Real.rpow_neg hW0.le, Real.rpow_natCast, inv_pow]
  rw [inv_le_inv₀ (by positivity) (by positivity)]
  calc (2 * (W : ℝ)) ^ (2 * (n + 1)) = (4 : ℝ) ^ (n + 1) * (W : ℝ) ^ (2 * n + 2) := by
        rw [mul_pow, pow_mul]; norm_num; ring
    _ ≤ (W : ℝ) * (W : ℝ) ^ (2 * n + 2) := by gcongr
    _ = (W : ℝ) ^ (2 * n + 3) := by ring


/-- A quantity at most `W^{-(2n+3)}` is at most `ζ^{n+1}` and `(ζ^{n+1})²` when `ζ ≥ (2W)⁻¹` and
`W ≥ 4^{n+1}`. -/
private lemma coneNode_small (n W : ℕ) (hW : 4 ^ (n + 1) ≤ W) {ζ x : ℝ}
    (hζ : (2 * (W : ℝ))⁻¹ ≤ ζ) (hx : x ≤ (W : ℝ) ^ (-((2 * n + 3 : ℕ) : ℝ))) :
    x ≤ ζ ^ (n + 1) ∧ x ≤ (ζ ^ (n + 1)) ^ 2 := by
  have h := hx.trans (coneNode_target n W hW)
  have hW1 : (1 : ℝ) ≤ W := by
    have : 1 ≤ 4 ^ (n + 1) := Nat.one_le_pow _ _ (by norm_num)
    exact_mod_cast this.trans hW
  have h0 : 0 ≤ (2 * (W : ℝ))⁻¹ := by positivity
  have h1 : (2 * (W : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have e : ((2 * (W : ℝ))⁻¹) ^ (2 * (n + 1)) = (((2 * (W : ℝ))⁻¹) ^ (n + 1)) ^ 2 := by
    rw [← pow_mul, mul_comm (n + 1) 2]
  refine ⟨h.trans ?_, h.trans ?_⟩
  · calc ((2 * (W : ℝ))⁻¹) ^ (2 * (n + 1)) ≤ ((2 * (W : ℝ))⁻¹) ^ (n + 1) :=
          pow_le_pow_of_le_one h0 h1 (by omega)
      _ ≤ ζ ^ (n + 1) := pow_le_pow_left₀ h0 hζ _
  · rw [e]
    exact pow_le_pow_left₀ (pow_nonneg h0 _) (pow_le_pow_left₀ h0 hζ _) 2

/-- `((k W^{-4rA})^{1/(4r)} ≤ kW^{-A}` and `(kW^{-4rA})^{1/(2r)} ≤ kW^{-A}` for `k ≥ 1`. -/
private lemma coneNode_delta (k A : ℝ) (hk : 1 ≤ k) (hA : 0 ≤ A) (W r : ℕ) (hW : 1 ≤ W)
    (hr : 1 ≤ r) :
    (k * (W : ℝ) ^ (-(4 * r * A))) ^ (1 / (4 * (r : ℝ))) ≤ k * (W : ℝ) ^ (-A) ∧
    (k * (W : ℝ) ^ (-(4 * r * A))) ^ (1 / (2 * (r : ℝ))) ≤ k * (W : ℝ) ^ (-A) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) ≤ W := by linarith
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hk0 : 0 ≤ k := by linarith
  have key : ∀ m : ℝ, 2 ≤ m → m ≤ 4 →
      (k * (W : ℝ) ^ (-(4 * r * A))) ^ (1 / (m * (r : ℝ))) ≤ k * (W : ℝ) ^ (-A) := by
    intro m hm2 hm4
    have hmr : 0 < m * r := by positivity
    rw [Real.mul_rpow hk0 (Real.rpow_nonneg hW0 _), ← Real.rpow_mul hW0]
    refine mul_le_mul ?_ ?_ (Real.rpow_nonneg hW0 _) hk0
    · calc k ^ (1 / (m * (r : ℝ))) ≤ k ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hk (by
              rw [div_le_one hmr]; nlinarith)
        _ = k := Real.rpow_one k
    · refine Real.rpow_le_rpow_of_exponent_le hW1 ?_
      rw [show -(4 * (r : ℝ) * A) * (1 / (m * r)) = -(4 / m * A) by field_simp]
      have : A ≤ 4 / m * A := by
        have : 1 ≤ 4 / m := by rw [le_div_iff₀ (by linarith)]; linarith
        nlinarith
      linarith
  exact ⟨key 4 (by norm_num) le_rfl, key 2 le_rfl (by norm_num)⟩


/-! ### The good samples of Step 3 at one time -/

/-- The bad set at time `v`: some loop error of length `j ≤ n + 1` exceeds `W^νE_jζ_v^j` or the
cap `W^νW^{C_j}`, some loop of length `n + 2` or `2n + 4` exceeds `W^νB_jζ_v^{j-1}`, or some loop
or loop error of length `2 ≤ k ≤ 2n + 4` above the diameter `W^νℓ_v` exceeds `W^νW^{-A}`. -/
private def coneNode_Bad (W : ℕ) (q : StepPt) (n : ℕ) (ν A : ℝ) (Ed Bl CK : ℕ → ℝ) (v : ℝ) :
    Set (Ω W q.L) :=
  (⋃ j ∈ Finset.Icc 1 (n + 1), {ω | ∃ l : Word j q.L,
    (W : ℝ) ^ ν * (Ed j * zetaProp q.g W q.L v ^ j) < ‖flowErr W (q.at v) l.1 l.2 ω‖}) ∪
  (⋃ j ∈ Finset.Icc 1 (n + 1), {ω | ∃ l : Word j q.L,
    (W : ℝ) ^ ν * (W : ℝ) ^ CK j < ‖flowErr W (q.at v) l.1 l.2 ω‖}) ∪
  {ω | ∃ l : Word (n + 1 + 1) q.L, (W : ℝ) ^ ν * (Bl (n + 1 + 1) *
    zetaProp q.g W q.L v ^ (n + 1 + 1 - 1)) < ‖loopTr (flowG W (q.at v) ω) l.1 l.2‖} ∪
  {ω | ∃ l : Word (2 * (n + 1) + 2) q.L, (W : ℝ) ^ ν * (Bl (2 * (n + 1) + 2) *
    zetaProp q.g W q.L v ^ (2 * (n + 1) + 2 - 1)) < ‖loopTr (flowG W (q.at v) ω) l.1 l.2‖} ∪
  (⋃ k ∈ Finset.Icc 2 (2 * (n + 1) + 2), {ω | ∃ l : {w : Word k q.L //
    (W : ℝ) ^ ν * ellProp q.g q.L v < wordDiam w.1}, (W : ℝ) ^ ν * (W : ℝ) ^ (-A) <
      ‖((‖loopTr (flowG W (q.at v) ω) l.1.1 l.1.2‖ + ‖flowErr W (q.at v) l.1.1 l.1.2 ω‖ : ℝ) :
        ℂ)‖})

private lemma coneNode_Bad_measure (W : ℕ) (q : StepPt) (n : ℕ) (ν A : ℝ) (Ed Bl CK : ℕ → ℝ)
    (v x : ℝ) (hx : 0 ≤ x)
    (h1 : ∀ j ∈ Finset.Icc 1 (n + 1), μ W q.L {ω | ∃ l : Word j q.L,
      (W : ℝ) ^ ν * (Ed j * zetaProp q.g W q.L v ^ j) < ‖flowErr W (q.at v) l.1 l.2 ω‖} ≤
        ENNReal.ofReal x)
    (h2 : ∀ j ∈ Finset.Icc 1 (n + 1), μ W q.L {ω | ∃ l : Word j q.L,
      (W : ℝ) ^ ν * (W : ℝ) ^ CK j < ‖flowErr W (q.at v) l.1 l.2 ω‖} ≤ ENNReal.ofReal x)
    (h3 : μ W q.L {ω | ∃ l : Word (n + 1 + 1) q.L, (W : ℝ) ^ ν * (Bl (n + 1 + 1) *
      zetaProp q.g W q.L v ^ (n + 1 + 1 - 1)) < ‖loopTr (flowG W (q.at v) ω) l.1 l.2‖} ≤
        ENNReal.ofReal x)
    (h4 : μ W q.L {ω | ∃ l : Word (2 * (n + 1) + 2) q.L, (W : ℝ) ^ ν * (Bl (2 * (n + 1) + 2) *
      zetaProp q.g W q.L v ^ (2 * (n + 1) + 2 - 1)) < ‖loopTr (flowG W (q.at v) ω) l.1 l.2‖} ≤
        ENNReal.ofReal x)
    (h5 : ∀ k ∈ Finset.Icc 2 (2 * (n + 1) + 2), μ W q.L {ω | ∃ l : {w : Word k q.L //
      (W : ℝ) ^ ν * ellProp q.g q.L v < wordDiam w.1}, (W : ℝ) ^ ν * (W : ℝ) ^ (-A) <
        ‖((‖loopTr (flowG W (q.at v) ω) l.1.1 l.1.2‖ + ‖flowErr W (q.at v) l.1.1 l.1.2 ω‖ : ℝ) :
          ℂ)‖} ≤ ENNReal.ofReal x) :
    μ W q.L (coneNode_Bad W q n ν A Ed Bl CK v) ≤ ENNReal.ofReal ((4 * n + 7) * x) := by
  have e1 := coneNode_union_le (μ W q.L) (Finset.Icc 1 (n + 1)) _ x hx h1
  have e2 := coneNode_union_le (μ W q.L) (Finset.Icc 1 (n + 1)) _ x hx h2
  have e5 := coneNode_union_le (μ W q.L) (Finset.Icc 2 (2 * (n + 1) + 2)) _ x hx h5
  rw [Nat.card_Icc, Nat.add_sub_cancel] at e1 e2
  rw [Nat.card_Icc, show 2 * (n + 1) + 2 + 1 - 2 = 2 * n + 3 by omega] at e5
  unfold coneNode_Bad
  calc _ ≤ ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * x) + ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * x) +
        ENNReal.ofReal x + ENNReal.ofReal x + ENNReal.ofReal (((2 * n + 3 : ℕ) : ℝ) * x) := by
        refine (measure_union_le _ _).trans (add_le_add ?_ e5)
        refine (measure_union_le _ _).trans (add_le_add ?_ h4)
        refine (measure_union_le _ _).trans (add_le_add ?_ h3)
        exact (measure_union_le _ _).trans (add_le_add e1 e2)
    _ = ENNReal.ofReal ((4 * n + 7) * x) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) hx, ← ENNReal.ofReal_add (by positivity) hx,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        push_cast
        ring

private lemma coneNode_Bad_good (W : ℕ) (hW : 1 ≤ W) (q : StepPt) (n : ℕ) (ν A CKs : ℝ)
    (Ed Bl CK : ℕ → ℝ) (hCK : ∀ j ∈ Finset.Icc 1 (n + 1), CK j ≤ CKs) (v : ℝ) (ω : Ω W q.L)
    (hω : ω ∉ coneNode_Bad W q n ν A Ed Bl CK v) :
    (∀ j, 1 ≤ j → j ≤ n + 1 → ∀ w : Word j q.L, ‖flowErr W (q.at v) w.1 w.2 ω‖ ≤
      (W : ℝ) ^ ν * (Ed j * zetaProp q.g W q.L v ^ j)) ∧
    (∀ j, 1 ≤ j → j ≤ n + 1 → ∀ w : Word j q.L, ‖flowErr W (q.at v) w.1 w.2 ω‖ ≤
      (W : ℝ) ^ ν * (W : ℝ) ^ CKs) ∧
    (∀ w : Word (n + 1 + 1) q.L, ‖loopTr (flowG W (q.at v) ω) w.1 w.2‖ ≤
      (W : ℝ) ^ ν * (Bl (n + 1 + 1) * zetaProp q.g W q.L v ^ (n + 1 + 1 - 1))) ∧
    (∀ w : Word (2 * (n + 1) + 2) q.L, ‖loopTr (flowG W (q.at v) ω) w.1 w.2‖ ≤
      (W : ℝ) ^ ν * (Bl (2 * (n + 1) + 2) * zetaProp q.g W q.L v ^ (2 * (n + 1) + 2 - 1))) ∧
    (∀ k, 2 ≤ k → k ≤ 2 * (n + 1) + 2 → ∀ w : Word k q.L,
      (W : ℝ) ^ ν * ellProp q.g q.L v < wordDiam w.1 →
        ‖loopTr (flowG W (q.at v) ω) w.1 w.2‖ + ‖flowErr W (q.at v) w.1 w.2 ω‖ ≤
          (W : ℝ) ^ ν * (W : ℝ) ^ (-A)) := by
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  unfold coneNode_Bad at hω
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hω
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hω
  refine ⟨fun j hj1 hj2 w => h1 j (Finset.mem_Icc.2 ⟨hj1, hj2⟩) w,
    fun j hj1 hj2 w => (h2 j (Finset.mem_Icc.2 ⟨hj1, hj2⟩) w).trans ?_, h3, h4,
    fun k hk1 hk2 w hw => ?_⟩
  · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hWr
      (hCK j (Finset.mem_Icc.2 ⟨hj1, hj2⟩))) (by positivity)
  · have := h5 k (Finset.mem_Icc.2 ⟨hk1, hk2⟩) ⟨w, hw⟩
    rwa [Complex.norm_real, Real.norm_of_nonneg (by positivity)] at this

/-! ### Assembly of the moment bound -/

/-- The moment comparison for the field, the moment-from-tail bound for the initial term and for the
restored row, and the passage from the `2r`-th to the `r`-th moment: if `D = Y_u + Z` and the terms
of the bound sum to at most `C B`, then `E|D|^r ≤ (1 + C^{2r})B^r`. -/
private lemma coneNode_assemble (g E : ℝ) {W L k : ℕ} (hW : 1 ≤ W) (hL : 3 ≤ L)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E (mRoot g L E)) (σ : Fin k → Bool)
    (c : ℝ → (Fin k → Fin L) → ℂ) {s u : ℝ} (hs : 1 / 2 ≤ s) (hsu : s ≤ u) (hu : u < 1)
    (hY : HeatClass (fun r y => ∑ b, c r b * loopErrField g E (mRoot g L E) W L b σ r y)
      (-1 / 2) ((u + 1) / 2))
    (r : ℕ) (hr : 1 ≤ r) {K δb Kβ Kb K0 δ0 δr Ψs Ψr Cfin B : ℝ} (hK : 0 ≤ K) (hδb : 0 ≤ δb)
    (hKβ : 0 ≤ Kβ) (hKb : 0 ≤ Kb) (hK0 : 0 ≤ K0) (hδ0 : 0 ≤ δ0) (hδr : 0 ≤ δr) (hΨs : 0 ≤ Ψs)
    (hΨr : 0 ≤ Ψr) (hB : 0 < B) (hCfin : 0 ≤ Cfin) (Bad : ℝ → Set (Ω W L))
    (hbad : ∀ v ∈ Set.Ioo s u, μ W L (Bad v) ≤ ENNReal.ofReal δb)
    (hrate : ∀ v ∈ Set.Ioo s u, ∀ ω, ω ∉ Bad v →
      ‖blockGen W L (gammaG g) (fun r' N => ∑ b, c r' b *
          (resLoop g E (mRoot g L E) b σ r' N - primLoop g W L E (mRoot g L E) r' b σ)) v
          (flowH g W L v ω)‖ ≤ Kβ / (1 - v) ∧
      ‖blockGamma W L (gammaG g)
          (fun N => ∑ b, c v b * (resLoop g E (mRoot g L E) b σ v N -
            primLoop g W L E (mRoot g L E) v b σ))
          (fun N => ∑ b, c v b * (resLoop g E (mRoot g L E) b σ v N -
            primLoop g W L E (mRoot g L E) v b σ)) (flowH g W L v ω)‖ ≤ Kb / (1 - v))
    (hcrude : ∀ v ∈ Set.Ioo s u,
      ∫ ω, ‖blockGen W L (gammaG g) (fun r' N => ∑ b, c r' b *
          (resLoop g E (mRoot g L E) b σ r' N - primLoop g W L E (mRoot g L E) r' b σ)) v
          (flowH g W L v ω)‖ ^ (4 * r) ∂(μ W L) ≤ K ^ (4 * r) ∧
      ∫ ω, ‖blockGamma W L (gammaG g)
          (fun N => ∑ b, c v b * (resLoop g E (mRoot g L E) b σ v N -
            primLoop g W L E (mRoot g L E) v b σ))
          (fun N => ∑ b, c v b * (resLoop g E (mRoot g L E) b σ v N -
            primLoop g W L E (mRoot g L E) v b σ)) (flowH g W L v ω)‖ ^ (2 * r) ∂(μ W L) ≤
        K ^ (2 * r))
    (Bin : Set (Ω W L)) (hBin : μ W L Bin ≤ ENNReal.ofReal δ0)
    (hinit : ∀ ω, ω ∉ Bin → ‖∑ b, c s b * flowErr W ⟨g, E, L, s⟩ b σ ω‖ ≤ Ψs)
    (hint_s : Integrable (fun ω => ‖∑ b, c s b * flowErr W ⟨g, E, L, s⟩ b σ ω‖ ^ (4 * r)) (μ W L))
    (hK_s : ∫ ω, ‖∑ b, c s b * flowErr W ⟨g, E, L, s⟩ b σ ω‖ ^ (4 * r) ∂(μ W L) ≤ K0 ^ (4 * r))
    (hint_u : Integrable (fun ω => ‖∑ b, c u b * flowErr W ⟨g, E, L, u⟩ b σ ω‖ ^ (2 * r)) (μ W L))
    (Z : Ω W L → ℂ) (hZ : Continuous Z) (Br : Set (Ω W L)) (hBr : μ W L Br ≤ ENNReal.ofReal δr)
    (hrow : ∀ ω, ω ∉ Br → ‖Z ω‖ ≤ Ψr)
    (hint_Z4 : Integrable (fun ω => ‖Z ω‖ ^ (4 * r)) (μ W L))
    (hK_Z : ∫ ω, ‖Z ω‖ ^ (4 * r) ∂(μ W L) ≤ K0 ^ (4 * r))
    (hint_Z2 : Integrable (fun ω => ‖Z ω‖ ^ (2 * r)) (μ W L))
    (D : Ω W L → ℂ) (hdec : ∀ ω, D ω = (∑ b, c u b * flowErr W ⟨g, E, L, u⟩ b σ ω) + Z ω)
    (hD1 : Integrable (fun ω => ‖D ω‖ ^ r) (μ W L))
    (hD2 : Integrable (fun ω => ‖D ω‖ ^ (2 * r)) (μ W L))
    (hfin : 2 * ((Ψs + K0 * δ0 ^ (1 / (4 * (r : ℝ))) +
        Real.sqrt ((2 * r - 1) * (Kb * Real.log ((1 - s) / (1 - u)))) +
        Real.sqrt ((2 * r - 1) * (K * δb ^ (1 / (2 * (r : ℝ))))) +
        Kβ * Real.log ((1 - s) / (1 - u)) + K * δb ^ (1 / (4 * (r : ℝ)))) +
      (Ψr + K0 * δr ^ (1 / (4 * (r : ℝ))))) ≤ Cfin * B) :
    ∫ ω, ‖D ω‖ ^ r ∂(μ W L) ≤ (1 + Cfin ^ (2 * r)) * B ^ r := by
  have hs0 : 0 < s := by linarith
  have hE := coneNode_flowEngine g E hW σ c hs0 hsu hu hY r hr hK hδb hKβ hKb Bad hbad hrate
    hcrude
  have hcs : Continuous fun ω => ∑ b, c s b * flowErr W ⟨g, E, L, s⟩ b σ ω :=
    continuous_finsetSum _ fun b _ => continuous_const.mul
      (coneNode_flowErr_cont hW ⟨g, E, L, s⟩ hL hm hs0.le (by change s < 1; linarith) b σ)
  have hI0 := coneNode_moment _ hcs r hr hK0 hΨs hδ0 hint_s hK_s Bin hBin hinit
  have hR0 := coneNode_moment Z hZ r hr hK0 hΨr hδr hint_Z4 hK_Z Br hBr hrow
  set M₁ := Ψs + K0 * δ0 ^ (1 / (4 * (r : ℝ))) +
    Real.sqrt ((2 * r - 1) * (Kb * Real.log ((1 - s) / (1 - u)))) +
    Real.sqrt ((2 * r - 1) * (K * δb ^ (1 / (2 * (r : ℝ))))) +
    Kβ * Real.log ((1 - s) / (1 - u)) + K * δb ^ (1 / (4 * (r : ℝ))) with hM₁
  have hY1 : (∫ ω, ‖∑ b, c u b * flowErr W ⟨g, E, L, u⟩ b σ ω‖ ^ (2 * r) ∂(μ W L)) ^
      (1 / (2 * (r : ℝ))) ≤ M₁ := by
    rw [hM₁]; linarith only [hE, hI0]
  have hM₁0 : 0 ≤ M₁ := le_trans (Real.rpow_nonneg (integral_nonneg fun ω => by positivity) _) hY1
  have hM₂0 : 0 ≤ Ψr + K0 * δr ^ (1 / (4 * (r : ℝ))) := by positivity
  have hsum := coneNode_sum_moment _ Z r hr hM₁0 hM₂0 hint_u hint_Z2 hY1 hR0
  have h2 : ∫ ω, ‖D ω‖ ^ (2 * r) ∂(μ W L) ≤ (Cfin * B) ^ (2 * r) := by
    simp_rw [hdec]
    exact hsum.trans (pow_le_pow_left₀ (by positivity) hfin _)
  exact coneNode_lower_moment D r hB hCfin hD1 hD2 h2


/-- `coneNode_final` with the tails bounded through the polynomial bounds of the regime: every
tail is at most `W^{-(2n+3)}`, hence at most `ζ_u^{n+1}` (and `ζ_u^{2(n+1)}` under a square
root) since `ζ_u ≥ (2W)⁻¹`. -/
private lemma coneNode_final' (n r : ℕ) (hr : 1 ≤ r) (W : ℕ) (hW4 : 4 ^ (n + 1) ≤ W) (δ ν : ℝ)
    (hν : 0 < ν) (hνδ : (2 * n + 5) * ν ≤ δ)
    (Ci Cβ RC ζ Env B₂ Edn Lg Pm A Tc Tc' γWL γWL' Kc CKm Kf CKf Aδ Zc : ℝ)
    (hCi : 0 ≤ Ci) (hCβ : 0 ≤ Cβ) (hRC : 1 ≤ RC) (hζ : (2 * (W : ℝ))⁻¹ ≤ ζ) (hEnv : 1 ≤ Env)
    (hB₂ : 0 ≤ B₂) (hsB : Real.sqrt B₂ ≤ Env) (hEdn0 : 0 ≤ Edn) (hEdn : Edn ≤ Env) (hLg : 0 ≤ Lg)
    (hLg3 : Lg ≤ 3 * Real.log W) (hPm : 0 ≤ Pm) (hTc0 : 0 ≤ Tc) (hTc : Tc ≤ Tc')
    (hγ0 : 0 ≤ γWL) (hγ : γWL ≤ γWL') (hKc : 1 ≤ Kc) (hKf : 1 ≤ Kf) (hAδ : 0 ≤ Aδ) (hZc : 0 ≤ Zc)
    (hF1 : |Ci * Pm ^ (4 * (n + 1)) * (W : ℝ) ^ ν| * (W : ℝ) ^ (-A) ≤
      (W : ℝ) ^ (-((2 * n + 3 : ℕ) : ℝ)))
    (hF3 : |(2 * (r : ℝ) - 1) * (Cβ * Pm ^ (8 * (n + 1)) * (γWL' * (W : ℝ) ^ ν) *
      (3 * Real.log W))| * (W : ℝ) ^ (-A) ≤ (W : ℝ) ^ (-((2 * n + 3 : ℕ) : ℝ)))
    (hF5 : |Cβ * Pm ^ (4 * (n + 1)) * ((W : ℝ) ^ ν * Tc') * (3 * Real.log W)| * (W : ℝ) ^ (-A) ≤
      (W : ℝ) ^ (-((2 * n + 3 : ℕ) : ℝ)))
    (hF7 : |RC * (RC + 1) ^ n * Zc * ((W : ℝ) ^ RC) ^ (n - 1) * (W : ℝ) ^ ν| * (W : ℝ) ^ (-A) ≤
      (W : ℝ) ^ (-((2 * n + 3 : ℕ) : ℝ)))
    (hδ2 : |Kf * 2 * (W : ℝ) ^ (|CKf|)| * (W : ℝ) ^ (-Aδ) ≤ (W : ℝ) ^ (-((2 * n + 3 : ℕ) : ℝ)))
    (hδ4 : |(2 * (r : ℝ) - 1) * (Kc * (4 * n + 7)) * (W : ℝ) ^ CKm| * (W : ℝ) ^ (-Aδ) ≤
      (W : ℝ) ^ (-((2 * n + 3 : ℕ) : ℝ)))
    (hδ6 : |Kc * (4 * n + 7) * (W : ℝ) ^ CKm| * (W : ℝ) ^ (-Aδ) ≤
      (W : ℝ) ^ (-((2 * n + 3 : ℕ) : ℝ))) :
    2 * ((Ci * ((4 * (W : ℝ) ^ ν + 2) ^ (2 * (n + 1)) + 1) * ζ ^ (n + 1) * (W : ℝ) ^ ν +
          Ci * Pm ^ (4 * (n + 1)) * ((W : ℝ) ^ ν * (W : ℝ) ^ (-A)) +
          Kf * (W : ℝ) ^ |CKf| * (2 * (W : ℝ) ^ (-(4 * r * Aδ))) ^ (1 / (4 * (r : ℝ))) +
        Real.sqrt ((2 * r - 1) * (coneNode_Kb n Cβ (4 * (W : ℝ) ^ ν + 2) ((W : ℝ) ^ ν) Pm
          ζ B₂ γWL ((W : ℝ) ^ ν * (W : ℝ) ^ (-A)) * Lg)) +
        Real.sqrt ((2 * r - 1) * (Kc * (W : ℝ) ^ CKm *
          ((4 * n + 7) * (W : ℝ) ^ (-(4 * r * Aδ))) ^ (1 / (2 * (r : ℝ))))) +
        coneNode_Kβ n Cβ RC (4 * (W : ℝ) ^ ν + 2) ((W : ℝ) ^ ν) Pm ζ Env Tc
          ((W : ℝ) ^ ν * (W : ℝ) ^ (-A)) * Lg +
        Kc * (W : ℝ) ^ CKm * ((4 * n + 7) * (W : ℝ) ^ (-(4 * r * Aδ))) ^ (1 / (4 * (r : ℝ)))) +
      (RC * (RC + 1) ^ n * 3 ^ (n - 1) * ((W : ℝ) ^ ν) ^ n * Edn * ζ ^ (n + 1) +
        RC * (RC + 1) ^ n * Zc * ((W : ℝ) ^ RC) ^ (n - 1) * ((W : ℝ) ^ ν * (W : ℝ) ^ (-A)) +
        Kf * (W : ℝ) ^ |CKf| * (2 * (W : ℝ) ^ (-(4 * r * Aδ))) ^ (1 / (4 * (r : ℝ))))) ≤
      coneNode_Cfin n r ν Ci Cβ RC * ((W : ℝ) ^ δ * (ζ ^ (n + 1) * Env)) := by
  have hW1 : 1 ≤ W := le_trans (Nat.one_le_pow _ _ (by norm_num)) hW4
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hζ0 : 0 ≤ ζ := le_trans (by positivity) hζ
  have hτ0 : 0 ≤ (W : ℝ) ^ ν * (W : ℝ) ^ (-A) := by positivity
  have h2r : (0 : ℝ) ≤ 2 * r - 1 := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hlogW : 0 ≤ Real.log W := Real.log_nonneg hWr
  obtain ⟨hd02, -⟩ := coneNode_delta 2 Aδ (by norm_num) hAδ W r hW1 hr
  obtain ⟨hdb4, hdb2⟩ := coneNode_delta (4 * n + 7) Aδ (by linarith) hAδ W r hW1 hr
  have hK0' : 0 ≤ Kc * (W : ℝ) ^ CKm := by positivity
  have hK00 : 0 ≤ Kf * (W : ℝ) ^ |CKf| := by positivity
  have hPm4 : 0 ≤ Pm ^ (4 * (n + 1)) := pow_nonneg hPm _
  have hPm8 : 0 ≤ Pm ^ (8 * (n + 1)) := pow_nonneg hPm _
  have F1 : Ci * Pm ^ (4 * (n + 1)) * ((W : ℝ) ^ ν * (W : ℝ) ^ (-A)) ≤ ζ ^ (n + 1) := by
    refine (coneNode_small n W hW4 hζ ?_).1
    rw [abs_of_nonneg (by positivity)] at hF1
    linarith only [hF1, show Ci * Pm ^ (4 * (n + 1)) * ((W : ℝ) ^ ν * (W : ℝ) ^ (-A)) =
      Ci * Pm ^ (4 * (n + 1)) * (W : ℝ) ^ ν * (W : ℝ) ^ (-A) by ring]
  have F2 : Kf * (W : ℝ) ^ |CKf| * (2 * (W : ℝ) ^ (-(4 * r * Aδ))) ^ (1 / (4 * (r : ℝ))) ≤
      ζ ^ (n + 1) := by
    refine (coneNode_small n W hW4 hζ ?_).1
    rw [abs_of_nonneg (by positivity)] at hδ2
    calc Kf * (W : ℝ) ^ |CKf| * (2 * (W : ℝ) ^ (-(4 * r * Aδ))) ^ (1 / (4 * (r : ℝ))) ≤
        Kf * (W : ℝ) ^ |CKf| * (2 * (W : ℝ) ^ (-Aδ)) := mul_le_mul_of_nonneg_left hd02 hK00
      _ = Kf * 2 * (W : ℝ) ^ |CKf| * (W : ℝ) ^ (-Aδ) := by ring
      _ ≤ _ := hδ2
  have F3 : (2 * r - 1) * (Cβ * Pm ^ (8 * (n + 1)) * (γWL * ((W : ℝ) ^ ν * (W : ℝ) ^ (-A))) *
      Lg) ≤ (ζ ^ (n + 1)) ^ 2 := by
    refine (coneNode_small n W hW4 hζ ?_).2
    have hγ'0 : 0 ≤ γWL' := hγ0.trans hγ
    rw [abs_of_nonneg (by positivity)] at hF3
    calc (2 * (r : ℝ) - 1) * (Cβ * Pm ^ (8 * (n + 1)) * (γWL * ((W : ℝ) ^ ν * (W : ℝ) ^ (-A))) *
        Lg) ≤ (2 * r - 1) * (Cβ * Pm ^ (8 * (n + 1)) * (γWL' * ((W : ℝ) ^ ν * (W : ℝ) ^ (-A))) *
          (3 * Real.log W)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hγ hτ0) (mul_nonneg hCβ hPm8)) hLg3 hLg
            (by positivity)) h2r
      _ = _ := by ring
      _ ≤ _ := hF3
  have F4 : (2 * r - 1) * (Kc * (W : ℝ) ^ CKm *
      ((4 * n + 7) * (W : ℝ) ^ (-(4 * r * Aδ))) ^ (1 / (2 * (r : ℝ)))) ≤ (ζ ^ (n + 1)) ^ 2 := by
    refine (coneNode_small n W hW4 hζ ?_).2
    rw [abs_of_nonneg (by positivity)] at hδ4
    calc (2 * (r : ℝ) - 1) * (Kc * (W : ℝ) ^ CKm *
        ((4 * n + 7) * (W : ℝ) ^ (-(4 * r * Aδ))) ^ (1 / (2 * (r : ℝ)))) ≤
        (2 * r - 1) * (Kc * (W : ℝ) ^ CKm * ((4 * n + 7) * (W : ℝ) ^ (-Aδ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdb2 hK0') h2r
      _ = (2 * r - 1) * (Kc * (4 * n + 7)) * (W : ℝ) ^ CKm * (W : ℝ) ^ (-Aδ) := by ring
      _ ≤ _ := hδ4
  have F5 : Cβ * Pm ^ (4 * (n + 1)) * ((W : ℝ) ^ ν * (W : ℝ) ^ (-A) * Tc) * Lg ≤
      ζ ^ (n + 1) := by
    refine (coneNode_small n W hW4 hζ ?_).1
    have hTc'0 : 0 ≤ Tc' := hTc0.trans hTc
    rw [abs_of_nonneg (by positivity)] at hF5
    calc Cβ * Pm ^ (4 * (n + 1)) * ((W : ℝ) ^ ν * (W : ℝ) ^ (-A) * Tc) * Lg ≤
        Cβ * Pm ^ (4 * (n + 1)) * ((W : ℝ) ^ ν * (W : ℝ) ^ (-A) * Tc') * (3 * Real.log W) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hTc hτ0)
            (mul_nonneg hCβ hPm4)) hLg3 hLg (by positivity)
      _ = _ := by ring
      _ ≤ _ := hF5
  have F6 : Kc * (W : ℝ) ^ CKm * ((4 * n + 7) * (W : ℝ) ^ (-(4 * r * Aδ))) ^ (1 / (4 * (r : ℝ))) ≤
      ζ ^ (n + 1) := by
    refine (coneNode_small n W hW4 hζ ?_).1
    rw [abs_of_nonneg (by positivity)] at hδ6
    calc Kc * (W : ℝ) ^ CKm * ((4 * n + 7) * (W : ℝ) ^ (-(4 * r * Aδ))) ^ (1 / (4 * (r : ℝ))) ≤
        Kc * (W : ℝ) ^ CKm * ((4 * n + 7) * (W : ℝ) ^ (-Aδ)) :=
          mul_le_mul_of_nonneg_left hdb4 hK0'
      _ = Kc * (4 * n + 7) * (W : ℝ) ^ CKm * (W : ℝ) ^ (-Aδ) := by ring
      _ ≤ _ := hδ6
  have F7 : RC * (RC + 1) ^ n * Zc * ((W : ℝ) ^ RC) ^ (n - 1) * ((W : ℝ) ^ ν * (W : ℝ) ^ (-A)) ≤
      ζ ^ (n + 1) := by
    refine (coneNode_small n W hW4 hζ ?_).1
    have : 0 ≤ RC := by linarith
    rw [abs_of_nonneg (by positivity)] at hF7
    linarith only [hF7, show RC * (RC + 1) ^ n * Zc * ((W : ℝ) ^ RC) ^ (n - 1) *
      ((W : ℝ) ^ ν * (W : ℝ) ^ (-A)) = RC * (RC + 1) ^ n * Zc * ((W : ℝ) ^ RC) ^ (n - 1) *
      (W : ℝ) ^ ν * (W : ℝ) ^ (-A) by ring]
  exact coneNode_final n r hr W hW1 δ ν hν hνδ Ci Cβ RC ζ Env B₂ Edn Lg Pm
    ((W : ℝ) ^ ν * (W : ℝ) ^ (-A)) Tc γWL (Kc * (W : ℝ) ^ CKm) (Kf * (W : ℝ) ^ |CKf|)
    ((4 * n + 7) * (W : ℝ) ^ (-(4 * r * Aδ))) (2 * (W : ℝ) ^ (-(4 * r * Aδ)))
    (2 * (W : ℝ) ^ (-(4 * r * Aδ))) Zc ((W : ℝ) ^ RC) hCi hCβ hRC hζ0 hEnv hB₂ hsB hEdn0 hEdn
    hLg hLg3 hPm hτ0 hTc0 hγ0 hK0' (by positivity) F1 F2 F3 F4 F5 F6 F7 F2


set_option maxHeartbeats 4000000 in -- the assembly of all choices of parameters
/-- (C.36) [gc:eq:recurrence] in moment form at one node of the cone, for word lengths `n ≥ 2`. -/
private lemma coneNode_main (R : PropRegime) (I : PropInputs R.base R.J) (c N cp θ : ℝ)
    (hinc : IncrementInput R.base R.J)
    (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q})
    (hSu : ∀ W, ∀ q ∈ S W, ∀ v : ℝ, q.s ≤ v → v ≤ q.u →
      (⟨q.g, q.E, q.L, q.s, q.t, v⟩ : StepPt) ∈ S W)
    (hin : OneStepInput cp θ (fun q : StepPt => q.at q.s) S)
    (htail : ∀ k : ℕ, 2 ≤ k → ∀ ε A : ℝ, 0 < ε → 0 < A → PrecMax StepPt.L S
      (Λ := fun W q => {w : Word k q.L // (W : ℝ) ^ ε * ellProp q.g q.L q.u < wordDiam w.1})
      (fun W q w ω => ((‖loopTr (flowG W (q.at q.u) ω) w.1.1 w.1.2‖ +
        ‖flowErr W (q.at q.u) w.1.1 w.1.2 ω‖ : ℝ) : ℂ))
      (fun W _ _ => (W : ℝ) ^ (-A)))
    (n : ℕ) (hn : 2 ≤ n) (Ed Bl : ℕ → ℕ → StepPt → ℝ)
    (hEd0 : ∀ j W q, 0 ≤ Ed j W q) (hBl0 : ∀ j W q, 0 ≤ Bl j W q)
    (hEdu : ∀ j W (q : StepPt) (v : ℝ), Ed j W ⟨q.g, q.E, q.L, q.s, q.t, v⟩ = Ed j W q)
    (hBlu : ∀ j W (q : StepPt) (v : ℝ), Bl j W ⟨q.g, q.E, q.L, q.s, q.t, v⟩ = Bl j W q)
    (hD : ∀ j : ℕ, 1 ≤ j → j ≤ n → PrecMax StepPt.L S (Λ := fun _ q => Word j q.L)
      (fun W q w ω => flowErr W (q.at q.u) w.1 w.2 ω)
      (fun W q _ => Ed j W q * zetaProp q.g W q.L q.u ^ j))
    (hL : ∀ j : ℕ, j = n + 1 ∨ j = 2 * n + 2 → PrecMax StepPt.L S (Λ := fun _ q => Word j q.L)
      (fun W q w ω => loopTr (flowG W (q.at q.u) ω) w.1 w.2)
      (fun W q _ => Bl j W q * zetaProp q.g W q.L q.u ^ (j - 1))) :
    ∀ r : ℕ, 1 ≤ r → ∀ δ : ℝ, 0 < δ → ∃ Cr : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ q ∈ S W, ∀ w : Word n q.L,
        Integrable (fun ω => ‖flowErr W (q.at q.u) w.1 w.2 ω‖ ^ r) (μ W q.L) ∧
        ∫ ω, ‖flowErr W (q.at q.u) w.1 w.2 ω‖ ^ r ∂(μ W q.L) ≤
          Cr * ((W : ℝ) ^ δ * (zetaProp q.g W q.L q.u ^ n *
            nodeEnv n (fun j => Ed j W q) (fun j => Bl j W q) (zetaProp q.g W q.L q.t))) ^ r := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hn1 : 1 ≤ n := by omega
  intro r hr δ hδ
  -- constants fixed before `W`
  obtain ⟨Ci, hCi, hincA⟩ := hinc
  obtain ⟨Cnp, hCnp, hrp⟩ := coneNode_rate_proj R n hn1 Ci hCi
  obtain ⟨Cns, hCns, hrs⟩ := coneNode_rate_stable R n hn1 Ci hCi
  obtain ⟨Cip, hCip, hip⟩ := coneNode_init_proj R n hn1 Ci hCi
  obtain ⟨Cis, hCis, his⟩ := coneNode_init_stable R n hn1 Ci hCi
  have hRC := R.one_le_C
  have hRC0 : 0 ≤ R.C := by linarith
  set Cβ : ℝ := max Cnp Cns with hCβ
  set Cι : ℝ := max Cip Cis with hCι
  have hCβ0 : 0 ≤ Cβ := le_trans hCnp.le (le_max_left _ _)
  have hCι0 : 0 ≤ Cι := le_trans hCip.le (le_max_left _ _)
  set Cζ : ℝ := |c| + 3 * |N| with hCζ
  have hCζ0 : 0 ≤ Cζ := by positivity
  set ν : ℝ := δ / (4 * n + 8) with hνdef
  have hν : 0 < ν := by positivity
  have hνδ : (2 * (n : ℝ) + 5) * ν ≤ δ := by
    rw [hνdef, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  -- crude moments
  obtain ⟨CKg, hCKg⟩ := coneCrude_gen R I n hn1 Cζ
  obtain ⟨Cg, Wg, hg⟩ := hCKg (4 * r) (by omega)
  obtain ⟨CKγ, hCKγ⟩ := coneCrude_gamma R I n hn1 Cζ
  obtain ⟨Cγ, Wγ, hγ⟩ := hCKγ (2 * r) (by omega)
  obtain ⟨CKf, hCKf⟩ := coneCrude_field R I n Cζ
  obtain ⟨Cf4, Wf4, hf4⟩ := hCKf (4 * r) (by omega)
  obtain ⟨Cf2, Wf2, hf2⟩ := hCKf (2 * r) (by omega)
  obtain ⟨Cfr, Wfr, hfr⟩ := hCKf r hr
  set Kc : ℝ := max Cg 1 + max Cγ 1 with hKc
  set CKm : ℝ := |CKg| + |CKγ| with hCKm
  set Kf : ℝ := max Cf4 1 with hKf
  have hKc1 : 1 ≤ Kc := by have := le_max_right Cg 1; have := le_max_right Cγ 1; linarith
  have hKf1 : 1 ≤ Kf := le_max_right _ _
  -- the cap `max_b |D_j| ≤ W^{C_K}` from the crude moments and the sampling
  obtain ⟨Wd, hWd⟩ := R.dyson
  have hcap : ∀ j : ℕ, ∃ CK : ℝ, 1 ≤ j → PrecMax StepPt.L S (Λ := fun _ q => Word j q.L)
      (fun W q w ω => flowErr W (q.at q.u) w.1 w.2 ω) (fun W _ _ => (W : ℝ) ^ CK) := by
    intro j
    rcases Nat.eq_zero_or_pos j with hj | hj
    · exact ⟨0, fun h => absurd h (by omega)⟩
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    obtain ⟨CK, hCK⟩ := coneCrude_field R I j' Cζ
    refine ⟨CK, fun _ => precMax_of_sampleMoment R I c N S hS (j' + 1) (by omega)
      (fun W _ => (W : ℝ) ^ CK) (|CK| + 1) (fun W q _ => ?_) (fun r' hr' δ' hδ' => ?_)⟩
    · rcases Nat.eq_zero_or_pos W with hW | hW
      · subst hW
        simp only [Nat.cast_zero]
        rw [Real.zero_rpow (by have := abs_nonneg CK; linarith : -(|CK| + 1) ≠ 0)]
        exact Real.rpow_nonneg le_rfl _
      · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hW)
          (by linarith [neg_abs_le CK])
    · obtain ⟨Cp, W₀, h⟩ := hCK r' hr'
      refine ⟨max Cp 0, max W₀ (max Wd 1), fun W hW q hq w => ?_⟩
      have hW1 : 1 ≤ W := le_trans ((le_max_right _ _).trans (le_max_right _ _)) hW
      have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
      obtain ⟨⟨d, hdJ, hreach⟩, hs, hsu, hut, hst, hWt, -⟩ := hS W hq
      obtain ⟨hL3, hg0, -⟩ := hWd W (le_trans ((le_max_left _ _).trans (le_max_right _ _)) hW) d
        (q.at q.t) hdJ.le hreach
      have hreu : CmpReach R.base W d (q.at q.u) := CmpReach.earlier q.u hreach (by linarith) hut
      have hζ := (coneNode_adm R c N hW1 (hS W hq) hg0 (by have : 3 ≤ q.L := hL3; omega) hsu
        hut).2.2
      have hh := (h W (le_trans (le_max_left _ _) hW) d (q.at q.u) q.u hdJ.le hreu
        (by change (1 : ℝ) / 2 ≤ q.u; linarith) le_rfl
        (by linarith)
        hζ w.2 w.1).2.2.2
      refine ⟨hh.1, hh.2.trans ?_⟩
      have hW0 : (0 : ℝ) ≤ W := by linarith
      calc Cp * (W : ℝ) ^ (CK * r') ≤ max Cp 0 * (W : ℝ) ^ (CK * r') :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hW0 _)
        _ = max Cp 0 * ((W : ℝ) ^ CK) ^ r' := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hW0]
        _ ≤ max Cp 0 * ((W : ℝ) ^ δ' * (W : ℝ) ^ CK) ^ r' :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.rpow_nonneg hW0 _)
              (le_mul_of_one_le_left (Real.rpow_nonneg hW0 _) (Real.one_le_rpow hWr hδ'.le)) r')
              (le_max_right _ _)
  choose CKc hCKc using hcap
  set CKs : ℝ := ∑ j ∈ Finset.Icc 1 (n + 1), |CKc j| with hCKs
  have hCKsj : ∀ j ∈ Finset.Icc 1 (n + 1), CKc j ≤ CKs := fun j hj =>
    (le_abs_self _).trans (Finset.single_le_sum (fun i _ => abs_nonneg (CKc i)) hj)
  have hCKs0 : 0 ≤ CKs := Finset.sum_nonneg fun i _ => abs_nonneg _
  -- the polynomial scales in `W`
  set fPm : ℕ → ℝ := fun W => (4 * (W : ℝ) ^ ν + 2) * (1 + (W : ℝ) ^ (3 : ℝ)) * (W : ℝ) ^ R.C
    with hfPm
  set fZc : ℕ → ℝ := fun W => (W : ℝ) ^ Cζ with hfZc
  set fXc : ℕ → ℝ := fun W => (W : ℝ) ^ ν * (W : ℝ) ^ CKs with hfXc
  set fγ : ℕ → ℝ := fun W => (W : ℝ) ^ R.C * W with hfγ
  set fTc : ℕ → ℝ := fun W => fγ W * ((n + 1) * (fXc W + (W : ℝ) ^ ν * fZc W ^ (n + 1))) +
    R.C * fZc W with hfTc
  have pPm : coneNode_Poly fPm :=
    coneNode_poly_mul (coneNode_poly_mul (coneNode_poly_add (coneNode_poly_mul
      (coneNode_poly_const 4) (coneNode_poly_rpow ν)) (coneNode_poly_const 2))
      (coneNode_poly_add (coneNode_poly_const 1) (coneNode_poly_rpow 3))) (coneNode_poly_rpow R.C)
  have pZc : coneNode_Poly fZc := coneNode_poly_rpow Cζ
  have pγ : coneNode_Poly fγ := coneNode_poly_mul (coneNode_poly_rpow R.C)
    (by simpa using coneNode_poly_rpow 1)
  have pTc : coneNode_Poly fTc :=
    coneNode_poly_add (coneNode_poly_mul pγ (coneNode_poly_mul (coneNode_poly_const _)
      (coneNode_poly_add (coneNode_poly_mul (coneNode_poly_rpow ν) (coneNode_poly_rpow CKs))
        (coneNode_poly_mul (coneNode_poly_rpow ν) (coneNode_poly_pow pZc _)))))
      (coneNode_poly_mul (coneNode_poly_const _) pZc)
  have pL := coneNode_poly_log
  -- tail accuracy `A`
  obtain ⟨A1, hA1, hA1'⟩ := coneNode_poly_tail (coneNode_poly_mul (coneNode_poly_mul
    (coneNode_poly_const Cι) (coneNode_poly_pow pPm (4 * (n + 1)))) (coneNode_poly_rpow ν))
    ((2 * n + 3 : ℕ) : ℝ)
  obtain ⟨A3, hA3, hA3'⟩ := coneNode_poly_tail (coneNode_poly_mul (coneNode_poly_const
    (2 * (r : ℝ) - 1)) (coneNode_poly_mul (coneNode_poly_mul (coneNode_poly_mul
    (coneNode_poly_const Cβ) (coneNode_poly_pow pPm (8 * (n + 1))))
    (coneNode_poly_mul pγ (coneNode_poly_rpow ν))) (coneNode_poly_mul (coneNode_poly_const 3) pL)))
    ((2 * n + 3 : ℕ) : ℝ)
  obtain ⟨A5, hA5, hA5'⟩ := coneNode_poly_tail (coneNode_poly_mul (coneNode_poly_mul
    (coneNode_poly_mul (coneNode_poly_const Cβ) (coneNode_poly_pow pPm (4 * (n + 1))))
    (coneNode_poly_mul (coneNode_poly_rpow ν) pTc)) (coneNode_poly_mul (coneNode_poly_const 3) pL))
    ((2 * n + 3 : ℕ) : ℝ)
  obtain ⟨A7, hA7, hA7'⟩ := coneNode_poly_tail (coneNode_poly_mul (coneNode_poly_mul
    (coneNode_poly_mul (coneNode_poly_const (R.C * (R.C + 1) ^ n)) pZc)
    (coneNode_poly_pow (coneNode_poly_rpow R.C) (n - 1))) (coneNode_poly_rpow ν))
    ((2 * n + 3 : ℕ) : ℝ)
  set A : ℝ := max (max A1 A3) (max A5 A7) + ν with hAdef
  have hA0 : 0 < A := by
    have : A1 ≤ max (max A1 A3) (max A5 A7) := (le_max_left _ _).trans (le_max_left _ _)
    linarith
  have hAν : 0 < A - ν := by
    have : A1 ≤ max (max A1 A3) (max A5 A7) := (le_max_left _ _).trans (le_max_left _ _)
    linarith
  have hA1A : A1 ≤ A := by
    have : A1 ≤ max (max A1 A3) (max A5 A7) := (le_max_left _ _).trans (le_max_left _ _)
    linarith
  have hA3A : A3 ≤ A := by
    have : A3 ≤ max (max A1 A3) (max A5 A7) := (le_max_right _ _).trans (le_max_left _ _)
    linarith
  have hA5A : A5 ≤ A := by
    have : A5 ≤ max (max A1 A3) (max A5 A7) := (le_max_left _ _).trans (le_max_right _ _)
    linarith
  have hA7A : A7 ≤ A := by
    have : A7 ≤ max (max A1 A3) (max A5 A7) := (le_max_right _ _).trans (le_max_right _ _)
    linarith
  -- kernel accuracy `A_k`
  obtain ⟨Ak, hAk, hAk'⟩ := coneNode_poly_tail (coneNode_poly_pow pPm (8 * (n + 1))) 1
  -- failure exponent `D' = 4rA_δ`
  obtain ⟨Aδ2, hAδ2, hAδ2'⟩ := coneNode_poly_tail (coneNode_poly_mul (coneNode_poly_const (Kf * 2))
    (coneNode_poly_rpow |CKf|)) ((2 * n + 3 : ℕ) : ℝ)
  obtain ⟨Aδ4, hAδ4, hAδ4'⟩ := coneNode_poly_tail (coneNode_poly_mul (coneNode_poly_const
    ((2 * r - 1) * (Kc * (4 * n + 7)))) (coneNode_poly_rpow CKm)) ((2 * n + 3 : ℕ) : ℝ)
  obtain ⟨Aδ6, hAδ6, hAδ6'⟩ := coneNode_poly_tail (coneNode_poly_mul (coneNode_poly_const
    (Kc * (4 * n + 7))) (coneNode_poly_rpow CKm)) ((2 * n + 3 : ℕ) : ℝ)
  set Aδ : ℝ := max (max Aδ2 Aδ4) Aδ6 with hAδ
  have hAδ0 : 0 < Aδ := lt_of_lt_of_le hAδ6 (le_max_right _ _)
  have hD'0 : 0 < 4 * (r : ℝ) * Aδ := by positivity
  -- the order of the moment bound
  set Cr : ℝ := 1 + coneNode_Cfin n r ν Cι Cβ R.C ^ (2 * r) with hCr
  suffices hev : ∀ᶠ W : ℕ in atTop, ∀ q ∈ S W, ∀ w : Word (n + 1) q.L,
      Integrable (fun ω => ‖flowErr W (q.at q.u) w.1 w.2 ω‖ ^ r) (μ W q.L) ∧
      ∫ ω, ‖flowErr W (q.at q.u) w.1 w.2 ω‖ ^ r ∂(μ W q.L) ≤
        Cr * ((W : ℝ) ^ δ * (zetaProp q.g W q.L q.u ^ (n + 1) *
          nodeEnv (n + 1) (fun j => Ed j W q) (fun j => Bl j W q) (zetaProp q.g W q.L q.t))) ^ r by
    obtain ⟨W₀, hW₀⟩ := Filter.eventually_atTop.1 hev
    exact ⟨Cr, W₀, hW₀⟩
  obtain ⟨Wk, hWk⟩ := R.kernel Ak hAk
  obtain ⟨Wi, hWi⟩ := hincA Ak hAk
  obtain ⟨Wb, hWb⟩ := R.budget
  obtain ⟨Wp, hWp⟩ := R.prim (2 * (n + 1) + 2) ν hν
  have evPT : ∀ᶠ W : ℕ in atTop, ∀ k ∈ Finset.Icc 2 (2 * (n + 1) + 2), ∀ d p, d ≤ R.J →
      CmpReach R.base W d p → ∀ (a : Fin k → Fin p.L) (σ : Fin k → Bool),
        (W : ℝ) ^ ν * ellProp p.g p.L p.u < wordDiam a →
          ‖primLoop p.g W p.L p.E (mRoot p.g p.L p.E) p.u a σ‖ ≤ (W : ℝ) ^ (-(A - ν)) :=
    (Filter.eventually_all_finset _).2 fun k hk =>
      Filter.eventually_atTop.2 (R.primTail k (Finset.mem_Icc.1 hk).1 ν (A - ν) hν hAν)
  have evD : ∀ᶠ W : ℕ in atTop, ∀ j ∈ Finset.Icc 1 (n + 1), ∀ q ∈ S W,
      μ W q.L {ω | ∃ l : Word j q.L, (W : ℝ) ^ ν * (Ed j W q * zetaProp q.g W q.L q.u ^ j) <
        ‖flowErr W (q.at q.u) l.1 l.2 ω‖} ≤ ENNReal.ofReal ((W : ℝ) ^ (-(4 * r * Aδ))) :=
    (Filter.eventually_all_finset _).2 fun j hj => Filter.eventually_atTop.2
      (hD j (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2 ν (4 * r * Aδ) hν hD'0)
  have evC : ∀ᶠ W : ℕ in atTop, ∀ j ∈ Finset.Icc 1 (n + 1), ∀ q ∈ S W,
      μ W q.L {ω | ∃ l : Word j q.L, (W : ℝ) ^ ν * (W : ℝ) ^ CKc j <
        ‖flowErr W (q.at q.u) l.1 l.2 ω‖} ≤ ENNReal.ofReal ((W : ℝ) ^ (-(4 * r * Aδ))) :=
    (Filter.eventually_all_finset _).2 fun j hj => Filter.eventually_atTop.2
      (hCKc j (Finset.mem_Icc.1 hj).1 ν (4 * r * Aδ) hν hD'0)
  have evL1 := Filter.eventually_atTop.2 (hL (n + 1 + 1) (Or.inl rfl) ν (4 * r * Aδ) hν hD'0)
  have evL2 := Filter.eventually_atTop.2 (hL (2 * (n + 1) + 2) (Or.inr rfl) ν (4 * r * Aδ) hν hD'0)
  have evT : ∀ᶠ W : ℕ in atTop, ∀ k ∈ Finset.Icc 2 (2 * (n + 1) + 2), ∀ q ∈ S W,
      μ W q.L {ω | ∃ l : {w : Word k q.L // (W : ℝ) ^ ν * ellProp q.g q.L q.u < wordDiam w.1},
        (W : ℝ) ^ ν * (W : ℝ) ^ (-A) < ‖((‖loopTr (flowG W (q.at q.u) ω) l.1.1 l.1.2‖ +
          ‖flowErr W (q.at q.u) l.1.1 l.1.2 ω‖ : ℝ) : ℂ)‖} ≤
        ENNReal.ofReal ((W : ℝ) ^ (-(4 * r * Aδ))) :=
    (Filter.eventually_all_finset _).2 fun k hk => Filter.eventually_atTop.2
      (htail k (Finset.mem_Icc.1 hk).1 ν A hν hA0 ν (4 * r * Aδ) hν hD'0)
  have evIe := Filter.eventually_atTop.2 (hin.err (n + 1) (by omega) ν (4 * r * Aδ) hν hD'0)
  have evIt := Filter.eventually_atTop.2
    (hin.tail (n + 1) (by omega) ν A hν hA0 ν (4 * r * Aδ) hν hD'0)
  have evF1 := hA1' A hA1A
  have evF3 := hA3' A hA3A
  have evF5 := hA5' A hA5A
  have evF7 := hA7' A hA7A
  have evθ1 := hAk' Ak le_rfl
  have evθ2 := coneNode_poly_exp (coneNode_poly_mul (coneNode_poly_const R.C)
    (coneNode_poly_pow pPm (8 * (n + 1)))) R.c_pos hν
  have evδ2 := hAδ2' Aδ ((le_max_left _ _).trans (le_max_left _ _))
  have evδ4 := hAδ4' Aδ ((le_max_right _ _).trans (le_max_left _ _))
  have evδ6 := hAδ6' Aδ (le_max_right _ _)
  filter_upwards [Filter.eventually_ge_atTop (4 ^ (n + 1)), Filter.eventually_ge_atTop 2,
    Filter.eventually_ge_atTop Wd, Filter.eventually_ge_atTop Wk, Filter.eventually_ge_atTop Wi,
    Filter.eventually_ge_atTop Wb, Filter.eventually_ge_atTop Wp, Filter.eventually_ge_atTop Wg,
    Filter.eventually_ge_atTop Wγ, Filter.eventually_ge_atTop Wf4, Filter.eventually_ge_atTop Wf2,
    Filter.eventually_ge_atTop Wfr, evPT, evD, evC, evL1, evL2, evT, evIe, evIt, evF1, evF3, evF5,
    evF7, evθ1, evθ2, evδ2, evδ4, evδ6] with W hW4 hW2 hWdW hWkW hWiW hWbW hWpW hWgW hWγW hWf4W
    hWf2W hWfrW hPTW hDW hCW hL1W hL2W hTW hIeW hItW hF1 hF3 hF5 hF7 hθ1 hθ2 hδ2 hδ4 hδ6
  intro q hq w
  obtain ⟨a, σ⟩ := w
  have hW1 : 1 ≤ W := by omega
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  obtain ⟨⟨d, hdJ, hreach⟩, hs, hsu, hut, hst, hWt, -⟩ := hS W hq
  obtain ⟨hL3, hg0, hm, hmim, -, -, hdy1, hdy2⟩ := hWd W hWdW d (q.at q.t) hdJ.le hreach
  change 3 ≤ q.L at hL3
  change 0 ≤ q.g at hg0
  have hL1 : 1 ≤ q.L := by omega
  have hW3 : 0 < (W : ℝ) ^ (-3 : ℝ) := Real.rpow_pos_of_pos hW0 _
  have ht1 : q.t < 1 := by linarith
  have hu1 : q.u < 1 := lt_of_le_of_lt hut ht1
  have hs0 : 0 < q.s := by linarith
  have hreachv : ∀ v : ℝ, 1 / 2 ≤ v → v ≤ q.t → CmpReach R.base W d (q.at v) :=
    fun v h1 h2 => CmpReach.earlier v hreach h1 h2
  -- deterministic facts at the times `v ∈ [s, t]`
  have hK : ∀ v, q.s ≤ v → v ≤ q.t → ∀ x y, 0 ≤ mixedKer 𝐏[q] v x y ∧ mixedKer 𝐏[q] v x y ≤
      R.C / ((1 - v) * ellProp q.g q.L v) * Real.exp (-(R.c * cycDist x y / ellProp q.g q.L v)) +
        (ellProp q.g q.L v)⁻¹ * (W : ℝ) ^ (-Ak) :=
    fun v h1 h2 x y => hWk W hWkW d (q.at v) hdJ.le (hreachv v (by linarith) h2) x y
  have hI : ∀ x y y', |mixedKer 𝐏[q] q.u x y - mixedKer 𝐏[q] q.u x y'| ≤
      Ci / ((1 - q.u) * ellProp q.g q.L q.u) * ((cycDist y y' : ℝ) / ellProp q.g q.L q.u) +
        (ellProp q.g q.L q.u)⁻¹ * (W : ℝ) ^ (-Ak) :=
    fun x y y' => hWi W hWiW d (q.at q.u) hdJ.le (hreachv q.u (by linarith) hut) x y y'
  have hbud : ∀ v, q.s ≤ v → v ≤ q.t →
      gammaG q.g * q.L + q.L / ellProp q.g q.L v ≤ (W : ℝ) ^ R.C :=
    fun v h1 h2 => hWb W hWbW d (q.at v) hdJ.le (hreachv v (by linarith) h2)
  have hprim : ∀ v, q.s ≤ v → v ≤ q.t → ∀ k : ℕ, 2 ≤ k → k ≤ 2 * (n + 1) + 2 →
      ∀ (b : Fin k → Fin q.L) (s : Fin k → Bool),
        ‖primLoop q.g W q.L q.E 𝐦[q] v b s‖ ≤ (W : ℝ) ^ ν * zetaProp q.g W q.L v ^ (k - 1) :=
    fun v h1 h2 => hWp W hWpW d (q.at v) hdJ.le (hreachv v (by linarith) h2)
  have hWνA : (W : ℝ) ^ (-(A - ν)) = (W : ℝ) ^ ν * (W : ℝ) ^ (-A) := by
    rw [← Real.rpow_add hW0]; ring_nf
  have hptail : ∀ v, q.s ≤ v → v ≤ q.t → ∀ k : ℕ, 2 ≤ k → k ≤ 2 * (n + 1) + 2 →
      ∀ (b : Fin k → Fin q.L) (s : Fin k → Bool), (W : ℝ) ^ ν * ellProp q.g q.L v < wordDiam b →
        ‖primLoop q.g W q.L q.E 𝐦[q] v b s‖ ≤ (W : ℝ) ^ ν * (W : ℝ) ^ (-A) := by
    intro v h1 h2 k hk1 hk2 b s hb
    rw [← hWνA]
    exact hPTW k (Finset.mem_Icc.2 ⟨hk1, hk2⟩) d (q.at v) hdJ.le (hreachv v (by linarith) h2) b s hb
  have hadmv : ∀ v, q.s ≤ v → v ≤ q.t → 1 ≤ (1 - q.s) / (1 - v) ∧
      (1 - q.s) / (1 - v) ≤ (W : ℝ) ^ (3 : ℝ) ∧ zetaProp q.g W q.L v ≤ (W : ℝ) ^ Cζ :=
    fun v h1 h2 => coneNode_adm R c N hW1 (hS W hq) hg0 hL1 h1 h2
  -- the scales
  have hP1 : 1 ≤ (W : ℝ) ^ ν := Real.one_le_rpow hWr hν.le
  have hτ0 : 0 ≤ (W : ℝ) ^ ν * (W : ℝ) ^ (-A) := by positivity
  have hPm1 : 1 ≤ fPm W := by
    simp only [hfPm]
    have h1 : 1 ≤ 4 * (W : ℝ) ^ ν + 2 := by linarith
    have h2 : 1 ≤ 1 + (W : ℝ) ^ (3 : ℝ) := by have := Real.rpow_nonneg hW0.le (3 : ℝ); linarith
    have h3 : 1 ≤ (W : ℝ) ^ R.C := Real.one_le_rpow hWr hRC0
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  have hPm : ∀ v, q.s ≤ v → v ≤ q.u → (4 * (W : ℝ) ^ ν + 2) * (1 + (1 - v) / (1 - q.u)) *
      (q.L / ellProp q.g q.L v) ≤ fPm W := by
    intro v h1 h2
    have hρ : (1 - v) / (1 - q.u) ≤ (W : ℝ) ^ (3 : ℝ) := by
      refine le_trans ?_ (hadmv q.u hsu hut).2.1
      exact div_le_div_of_nonneg_right (by linarith) (by linarith)
    have hLℓ : (q.L : ℝ) / ellProp q.g q.L v ≤ (W : ℝ) ^ R.C := by
      have := hbud v h1 (h2.trans hut)
      have : 0 ≤ gammaG q.g * q.L := by have := coneNode_gamma_pos q.g; positivity
      linarith
    have hρ0 : 0 ≤ (1 - v) / (1 - q.u) := div_nonneg (by linarith) (by linarith)
    have hLℓ0 : 0 ≤ (q.L : ℝ) / ellProp q.g q.L v :=
      div_nonneg (Nat.cast_nonneg _) (by linarith [coneNode_ell_ge_one hg0 hL1 v])
    simp only [hfPm]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hLℓ hLℓ0
      (by positivity)
  have hZc1 : 1 ≤ fZc W := Real.one_le_rpow hWr hCζ0
  have hXc0 : 0 ≤ fXc W := by simp only [hfXc]; positivity
  have hτθ : fPm W ^ (8 * (n + 1)) * (R.C * Real.exp (-(R.c * (4 * (W : ℝ) ^ ν + 2) / 4)) +
      (W : ℝ) ^ (-Ak)) ≤ 1 := by
    have he : Real.exp (-(R.c * (4 * (W : ℝ) ^ ν + 2) / 4)) ≤ Real.exp (-(R.c * (W : ℝ) ^ ν)) := by
      apply Real.exp_le_exp.2
      have hc := R.c_pos
      have : R.c * (W : ℝ) ^ ν ≤ R.c * (4 * (W : ℝ) ^ ν + 2) / 4 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
        nlinarith only [hc, hP1]
      linarith only [this]
    have hP8 : 0 ≤ fPm W ^ (8 * (n + 1)) := pow_nonneg (by linarith) _
    rw [abs_of_nonneg (mul_nonneg hRC0 hP8)] at hθ2
    rw [abs_of_nonneg hP8] at hθ1
    have hW1' : (W : ℝ) ^ (-1 : ℝ) ≤ 1 / 2 := by
      rw [Real.rpow_neg_one, one_div]
      exact inv_anti₀ (by norm_num) (by exact_mod_cast hW2)
    have : fPm W ^ (8 * (n + 1)) * (R.C * Real.exp (-(R.c * (4 * (W : ℝ) ^ ν + 2) / 4))) ≤
        R.C * fPm W ^ (8 * (n + 1)) * Real.exp (-(R.c * (W : ℝ) ^ ν)) := by
      rw [show fPm W ^ (8 * (n + 1)) * (R.C * Real.exp (-(R.c * (4 * (W : ℝ) ^ ν + 2) / 4))) =
        R.C * fPm W ^ (8 * (n + 1)) * Real.exp (-(R.c * (4 * (W : ℝ) ^ ν + 2) / 4)) by ring]
      exact mul_le_mul_of_nonneg_left he (mul_nonneg hRC0 hP8)
    have h2 : fPm W ^ (8 * (n + 1)) * (W : ℝ) ^ (-Ak) ≤ 1 / 2 := hθ1.trans hW1'
    linarith [mul_add (fPm W ^ (8 * (n + 1))) (R.C * Real.exp (-(R.c * (4 * (W : ℝ) ^ ν + 2) / 4)))
      ((W : ℝ) ^ (-Ak))]
  clear hWk hWi hWb hWp hPTW evPT evD evC evL1 evL2 evT evIe evIt evF1 evF3 evF5 evF7 evθ1 evθ2
    evδ2 evδ4 evδ6 hA1' hA3' hA5' hA7' hAk' hAδ2' hAδ4' hAδ6' pPm pZc pγ pTc pL hθ1 hθ2
  -- the bad sets at the times `v ∈ (s, u)`
  have hxD : 0 ≤ (W : ℝ) ^ (-(4 * r * Aδ)) := Real.rpow_nonneg hW0.le _
  have hbad : ∀ v ∈ Set.Ioo q.s q.u,
      μ W q.L (coneNode_Bad W q n ν A (fun j => Ed j W q) (fun j => Bl j W q) CKc v) ≤
        ENNReal.ofReal ((4 * n + 7) * (W : ℝ) ^ (-(4 * r * Aδ))) := by
    intro v hv
    have hqv := hSu W q hq v hv.1.le hv.2.le
    refine coneNode_Bad_measure W q n ν A _ _ CKc v _ hxD (fun j hj => ?_)
      (fun j hj => hCW j hj _ hqv) ?_ ?_ (fun k hk => hTW k hk _ hqv)
    · have := hDW j hj _ hqv
      rw [hEdu] at this
      exact this
    · have := hL1W _ hqv
      rw [hBlu] at this
      exact this
    · have := hL2W _ hqv
      rw [hBlu] at this
      exact this
  -- scales at `u` and `t`, the envelope and the time integral
  have hζu := coneNode_zeta_lower hg0 hW1 hL1 (by linarith : (0 : ℝ) ≤ q.u) hu1
  have hζu0 : 0 ≤ zetaProp q.g W q.L q.u := le_trans (by positivity) hζu
  have hζt0 : 0 ≤ zetaProp q.g W q.L q.t := (coneNode_zeta_pos hg0 hW1 hL1 ht1).le
  have hEd0' : ∀ j, 0 ≤ Ed j W q := fun j => hEd0 j W q
  have hBl0' : ∀ j, 0 ≤ Bl j W q := fun j => hBl0 j W q
  obtain ⟨hEnv1, hEnvlin, -, -, hEnvB⟩ := coneNode_env_parts (n + 1) (fun j => Ed j W q)
    (fun j => Bl j W q) (zetaProp q.g W q.L q.t) hζt0 hEd0' hBl0'
  have hEnvn : Ed n W q ≤ nodeEnv (n + 1) (fun j => Ed j W q) (fun j => Bl j W q)
      (zetaProp q.g W q.L q.t) := hEnvlin n (Finset.mem_Ico.2 ⟨hn1, by omega⟩)
  obtain ⟨hR1, hRW, -⟩ := hadmv q.u hsu hut
  have hLg0 : 0 ≤ Real.log ((1 - q.s) / (1 - q.u)) := Real.log_nonneg hR1
  have hLg3 : Real.log ((1 - q.s) / (1 - q.u)) ≤ 3 * Real.log W := by
    calc Real.log ((1 - q.s) / (1 - q.u)) ≤ Real.log ((W : ℝ) ^ (3 : ℝ)) :=
          Real.log_le_log (by linarith) hRW
      _ = 3 * Real.log W := Real.log_rpow hW0 _
  have hγL : gammaG q.g * W * q.L ≤ fγ W := by
    have h := hbud q.u hsu hut
    have h2 : 0 ≤ (q.L : ℝ) / ellProp q.g q.L q.u :=
      div_nonneg (Nat.cast_nonneg _) (by linarith [coneNode_ell_ge_one hg0 hL1 q.u])
    simp only [hfγ]
    nlinarith only [h, h2, hW0]
  have hγL0 : 0 ≤ gammaG q.g * W * q.L := by have := coneNode_gamma_pos q.g; positivity
  have hZc0 : 0 ≤ fZc W := by linarith
  have hTc : gammaG q.g * W * q.L * ((n + 1) * (fXc W + (W : ℝ) ^ ν * fZc W ^ (n + 1))) +
      R.C * fZc W ≤ fTc W := by
    simp only [hfTc]
    have : 0 ≤ (n + 1 : ℝ) * (fXc W + (W : ℝ) ^ ν * fZc W ^ (n + 1)) := by positivity
    nlinarith only [hγL, this]
  have hTc0 : 0 ≤ gammaG q.g * W * q.L * ((n + 1) * (fXc W + (W : ℝ) ^ ν * fZc W ^ (n + 1))) +
      R.C * fZc W := by positivity
  have hCKgm : CKg ≤ CKm := by
    have := le_abs_self CKg; have := abs_nonneg CKγ; simp only [hCKm]; linarith
  have hCKγm : CKγ ≤ CKm := by
    have := le_abs_self CKγ; have := abs_nonneg CKg; simp only [hCKm]; linarith
  have hCgK : Cg ≤ Kc := by
    have := le_max_left Cg 1; have := le_max_right Cγ 1; simp only [hKc]; linarith
  have hCγK : Cγ ≤ Kc := by
    have := le_max_left Cγ 1; have := le_max_right Cg 1; simp only [hKc]; linarith
  have hPmp : ∀ k : ℕ, 0 ≤ fPm W ^ k := fun k => pow_nonneg (by linarith) k
  -- the final normalization
  have hfin := coneNode_final' n r hr W hW4 δ ν hν hνδ Cι Cβ R.C (zetaProp q.g W q.L q.u)
    (nodeEnv (n + 1) (fun j => Ed j W q) (fun j => Bl j W q) (zetaProp q.g W q.L q.t))
    (Bl (2 * (n + 1) + 2) W q) (Ed n W q) (Real.log ((1 - q.s) / (1 - q.u))) (fPm W) A
    (gammaG q.g * W * q.L * ((n + 1) * (fXc W + (W : ℝ) ^ ν * fZc W ^ (n + 1))) + R.C * fZc W)
    (fTc W) (gammaG q.g * W * q.L) (fγ W) Kc CKm Kf CKf Aδ (fZc W) hCι0 hCβ0 hRC hζu hEnv1
    (hBl0' _) hEnvB (hEd0' n) hEnvn hLg0 hLg3 (by linarith) hTc0 hTc hγL0 hγL hKc1 hKf1 hAδ0.le
    hZc0 hF1 hF3 hF5 hF7 hδ2 hδ4 hδ6
  have hKβ0 : 0 ≤ coneNode_Kβ n Cβ R.C (4 * (W : ℝ) ^ ν + 2) ((W : ℝ) ^ ν) (fPm W)
      (zetaProp q.g W q.L q.u) (nodeEnv (n + 1) (fun j => Ed j W q) (fun j => Bl j W q)
        (zetaProp q.g W q.L q.t))
      (gammaG q.g * W * q.L * ((n + 1) * (fXc W + (W : ℝ) ^ ν * fZc W ^ (n + 1))) + R.C * fZc W)
      ((W : ℝ) ^ ν * (W : ℝ) ^ (-A)) := by
    unfold coneNode_Kβ
    have := hPmp (4 * (n + 1))
    positivity
  have hKb0 : 0 ≤ coneNode_Kb n Cβ (4 * (W : ℝ) ^ ν + 2) ((W : ℝ) ^ ν) (fPm W)
      (zetaProp q.g W q.L q.u) (Bl (2 * (n + 1) + 2) W q) (gammaG q.g * W * q.L)
      ((W : ℝ) ^ ν * (W : ℝ) ^ (-A)) := by
    unfold coneNode_Kb
    have := hPmp (8 * (n + 1))
    have := hBl0' (2 * (n + 1) + 2)
    positivity
  have hCfin0 : 0 ≤ coneNode_Cfin n r ν Cι Cβ R.C := by
    unfold coneNode_Cfin
    positivity
  have hB0 : 0 < (W : ℝ) ^ δ * (zetaProp q.g W q.L q.u ^ (n + 1) *
      nodeEnv (n + 1) (fun j => Ed j W q) (fun j => Bl j W q) (zetaProp q.g W q.L q.t)) := by
    have : 0 < zetaProp q.g W q.L q.u := coneNode_zeta_pos hg0 hW1 hL1 hu1
    have : 0 < (W : ℝ) ^ δ := Real.rpow_pos_of_pos hW0 _
    have : 0 < nodeEnv (n + 1) (fun j => Ed j W q) (fun j => Bl j W q)
      (zetaProp q.g W q.L q.t) := by linarith
    positivity
  -- the reached points at `s` and `u`, and the crude moments
  have hreach_s := hreachv q.s hs (hsu.trans hut)
  have hreach_u := hreachv q.u (by linarith) hut
  have hzs := (hadmv q.s le_rfl (hsu.trans hut)).2.2
  have hzu := (hadmv q.u hsu hut).2.2
  have hWu : (W : ℝ) ^ (-3 : ℝ) ≤ 1 - q.u := by linarith
  have hfru := hfr W hWfrW d (q.at q.u) q.u hdJ.le hreach_u (by change (1 : ℝ) / 2 ≤ q.u; linarith)
    le_rfl hWu hzu σ a
  have hf2u := hf2 W hWf2W d (q.at q.u) q.u hdJ.le hreach_u (by change (1 : ℝ) / 2 ≤ q.u; linarith)
    le_rfl hWu hzu σ a
  have hf4u := hf4 W hWf4W d (q.at q.u) q.u hdJ.le hreach_u (by change (1 : ℝ) / 2 ≤ q.u; linarith)
    le_rfl hWu hzu σ a
  have hf4s := hf4 W hWf4W d (q.at q.s) q.u hdJ.le hreach_s hs hsu hWu hzs σ a
  have hcr : ∀ v ∈ Set.Ioo q.s q.u, _ := fun v hv =>
    And.intro (hg W hWgW d (q.at v) q.u hdJ.le (hreachv v (by linarith [hv.1])
      (hv.2.le.trans hut)) (by change (1 : ℝ) / 2 ≤ v; linarith [hv.1]) hv.2.le hWu
      (hadmv v hv.1.le (hv.2.le.trans hut)).2.2 σ a)
    (hγ W hWγW d (q.at v) q.u hdJ.le (hreachv v (by linarith [hv.1])
      (hv.2.le.trans hut)) (by change (1 : ℝ) / 2 ≤ v; linarith [hv.1]) hv.2.le hWu
      (hadmv v hv.1.le (hv.2.le.trans hut)).2.2 σ a)
  have hKs := hf4s.1.2.trans (coneNode_crude_le hW1 (by omega) (le_max_left _ _) hKf1
    (le_abs_self CKf))
  -- the initial bad set
  have hBinμ : μ W q.L ({ω | ∃ l : Word (n + 1) q.L, (W : ℝ) ^ ν *
      flowZeta W (q.at q.s) ^ (n + 1) < ‖flowErr W (q.at q.s) l.1 l.2 ω‖} ∪
      {ω | ∃ l : {w : Word (n + 1) q.L // (W : ℝ) ^ ν * flowEll (q.at q.s) < wordDiam w.1},
        (W : ℝ) ^ ν * (W : ℝ) ^ (-A) < ‖((‖loopTr (flowG W (q.at q.s) ω) l.1.1 l.1.2‖ +
          ‖flowErr W (q.at q.s) l.1.1 l.1.2 ω‖ : ℝ) : ℂ)‖}) ≤
      ENNReal.ofReal (2 * (W : ℝ) ^ (-(4 * r * Aδ))) := by
    refine (measure_union_le _ _).trans ?_
    rw [two_mul, ENNReal.ofReal_add hxD hxD]
    exact add_le_add (hIeW q hq) (hItW q hq)
  have hgood_s : ∀ ω, ω ∉ ({ω | ∃ l : Word (n + 1) q.L, (W : ℝ) ^ ν *
      flowZeta W (q.at q.s) ^ (n + 1) < ‖flowErr W (q.at q.s) l.1 l.2 ω‖} ∪
      {ω | ∃ l : {w : Word (n + 1) q.L // (W : ℝ) ^ ν * flowEll (q.at q.s) < wordDiam w.1},
        (W : ℝ) ^ ν * (W : ℝ) ^ (-A) < ‖((‖loopTr (flowG W (q.at q.s) ω) l.1.1 l.1.2‖ +
          ‖flowErr W (q.at q.s) l.1.1 l.1.2 ω‖ : ℝ) : ℂ)‖}) →
      (∀ w : Word (n + 1) q.L, ‖flowErr W (q.at q.s) w.1 w.2 ω‖ ≤
        (W : ℝ) ^ ν * zetaProp q.g W q.L q.s ^ (n + 1)) ∧
      (∀ w : Word (n + 1) q.L, (W : ℝ) ^ ν * ellProp q.g q.L q.s < wordDiam w.1 →
        ‖loopTr (flowG W (q.at q.s) ω) w.1 w.2‖ + ‖flowErr W (q.at q.s) w.1 w.2 ω‖ ≤
          (W : ℝ) ^ ν * (W : ℝ) ^ (-A)) := by
    intro ω hω
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hω
    refine ⟨fun w => hω.1 w, fun w hw => ?_⟩
    have := hω.2 ⟨w, hw⟩
    rwa [Complex.norm_real, Real.norm_of_nonneg (by positivity)] at this
  have hΨs : 0 ≤ Cι * ((4 * (W : ℝ) ^ ν + 2) ^ (2 * (n + 1)) + 1) *
      zetaProp q.g W q.L q.u ^ (n + 1) * (W : ℝ) ^ ν +
      Cι * fPm W ^ (4 * (n + 1)) * ((W : ℝ) ^ ν * (W : ℝ) ^ (-A)) := by
    have := hPmp (4 * (n + 1)); positivity
  have hΨr : 0 ≤ R.C * (R.C + 1) ^ n * 3 ^ (n - 1) * ((W : ℝ) ^ ν) ^ n * Ed n W q *
      zetaProp q.g W q.L q.u ^ (n + 1) +
      R.C * (R.C + 1) ^ n * fZc W * ((W : ℝ) ^ R.C) ^ (n - 1) * ((W : ℝ) ^ ν * (W : ℝ) ^ (-A)) := by
    have := hEd0' n; positivity
  have hcont_s : ∀ b : Fin (n + 1) → Fin q.L, Continuous fun ω => flowErr W (q.at q.s) b σ ω :=
    fun b => coneNode_flowErr_cont hW1 (q.at q.s) hL3 hm (by change (0 : ℝ) ≤ q.s; linarith)
      (by change q.s < 1; linarith) b σ
  by_cases hσ : ∀ j, σ (finRotate (n + 1) j) = !σ j
  · -- cyclically alternating words: the propagated projected field (C.35)
    -- [fo:eq:projected-error-equation]
    have hrate : ∀ v ∈ Set.Ioo q.s q.u, ∀ ω,
        ω ∉ coneNode_Bad W q n ν A (fun j => Ed j W q) (fun j => Bl j W q) CKc v →
        ‖blockGen W q.L (gammaG q.g) (fun r' N => ∑ b, projCoef 𝐏[q] q.u r' a b *
          (resLoop q.g q.E (mRoot q.g q.L q.E) b σ r' N -
            primLoop q.g W q.L q.E (mRoot q.g q.L q.E) r' b σ)) v (flowH q.g W q.L v ω)‖ ≤
          coneNode_Kβ n Cβ R.C (4 * (W : ℝ) ^ ν + 2) ((W : ℝ) ^ ν) (fPm W)
            (zetaProp q.g W q.L q.u) (nodeEnv (n + 1) (fun j => Ed j W q) (fun j => Bl j W q)
              (zetaProp q.g W q.L q.t))
            (gammaG q.g * W * q.L * ((n + 1) * (fXc W + (W : ℝ) ^ ν * fZc W ^ (n + 1))) +
              R.C * fZc W) ((W : ℝ) ^ ν * (W : ℝ) ^ (-A)) / (1 - v) ∧
        ‖blockGamma W q.L (gammaG q.g)
          (fun N => ∑ b, projCoef 𝐏[q] q.u v a b * (resLoop q.g q.E (mRoot q.g q.L q.E) b σ v N -
            primLoop q.g W q.L q.E (mRoot q.g q.L q.E) v b σ))
          (fun N => ∑ b, projCoef 𝐏[q] q.u v a b * (resLoop q.g q.E (mRoot q.g q.L q.E) b σ v N -
            primLoop q.g W q.L q.E (mRoot q.g q.L q.E) v b σ)) (flowH q.g W q.L v ω)‖ ≤
          coneNode_Kb n Cβ (4 * (W : ℝ) ^ ν + 2) ((W : ℝ) ^ ν) (fPm W) (zetaProp q.g W q.L q.u)
            (Bl (2 * (n + 1) + 2) W q) (gammaG q.g * W * q.L) ((W : ℝ) ^ ν * (W : ℝ) ^ (-A)) /
            (1 - v) := by
      intro v hv ω hω
      obtain ⟨g1, g2, g3, g4, g5⟩ := coneNode_Bad_good W hW1 q n ν A CKs (fun j => Ed j W q)
        (fun j => Bl j W q) CKc hCKsj v ω hω
      have hv1 : q.s ≤ v := hv.1.le
      have hv2 : v ≤ q.u := hv.2.le
      have h1v : 0 < 1 - v := by linarith
      have h := hrp W q v Ak ν ((W : ℝ) ^ ν * (W : ℝ) ^ (-A)) (fXc W) (fZc W) (fPm W) ω σ a
        (fun j => Ed j W q) (fun j => Bl j W q) hW1 hAk hν hτ0 (by linarith) hv2 hut ht1 hσ hL3
        hg0 hm hmim (hK v hv1 (hv2.trans hut)) (hK q.u hsu hut) hI (hPm v hv1 hv2) hPm1 hτθ
        (hadmv v hv1 (hv2.trans hut)).2.2 hZc1 hXc0 hEd0' hBl0' g1 g2 g3 g4 g5
        (hprim v hv1 (hv2.trans hut)) (hptail v hv1 (hv2.trans hut))
      refine ⟨h.1.trans (div_le_div_of_nonneg_right (coneNode_Kβ_mono (le_max_left _ _) hCnp.le
        le_rfl (by positivity) (by positivity) (by linarith) hζu0 hRC0 (by linarith) hTc0 hτ0)
        h1v.le), h.2.trans (div_le_div_of_nonneg_right (coneNode_Kb_mono (le_max_left _ _)
        hCnp.le le_rfl (by positivity) (by positivity) (by linarith) hζu0 (hBl0' _) hγL0 hτ0)
        h1v.le)⟩
    have hY := heatClass_projField q.g q.E (mRoot q.g q.L q.E) W q.L hW1 hL3 hm σ a (v := q.u)
      ⟨by linarith, hu1⟩ (a' := -1 / 2) (b' := (q.u + 1) / 2) (by norm_num) (by linarith)
    -- the restored row at `u`
    have hcont_u : ∀ b : Fin (n + 1) → Fin q.L, Continuous fun ω => flowErr W (q.at q.u) b σ ω :=
      fun b => coneNode_flowErr_cont hW1 (q.at q.u) hL3 hm (by change (0 : ℝ) ≤ q.u; linarith)
        hu1 b σ
    have hZeq : ∀ ω, flowErr W (q.at q.u) a σ ω - ∑ b, projCoef 𝐏[q] q.u q.u a b *
        flowErr W (q.at q.u) b σ ω = rowSum (fun b => flowErr W (q.at q.u) b σ ω) (a 0) *
          ∏ j : Fin n, ((wardProfile 𝐏[q] q.u (a 0 - a j.succ) : ℝ) : ℂ) := by
      intro ω
      have h := (coneRates_fieldSelf q.g q.E 𝐦[q] hL3 hm (by linarith) hu1).1 n
        (fun b => flowErr W (q.at q.u) b σ ω) a
      beta_reduce at h
      rw [h]
      simp only [projQ]
      exact sub_sub_cancel _ _
    have hZc : Continuous fun ω => flowErr W (q.at q.u) a σ ω - ∑ b, projCoef 𝐏[q] q.u q.u a b *
        flowErr W (q.at q.u) b σ ω :=
      (hcont_u a).sub (continuous_finsetSum _ fun b _ => continuous_const.mul (hcont_u b))
    have hBrμ : μ W q.L ({ω | ∃ l : Word n q.L, (W : ℝ) ^ ν * (Ed n W q *
        zetaProp q.g W q.L q.u ^ n) < ‖flowErr W (q.at q.u) l.1 l.2 ω‖} ∪
        {ω | ∃ l : {w : Word n q.L // (W : ℝ) ^ ν * ellProp q.g q.L q.u < wordDiam w.1},
          (W : ℝ) ^ ν * (W : ℝ) ^ (-A) < ‖((‖loopTr (flowG W (q.at q.u) ω) l.1.1 l.1.2‖ +
            ‖flowErr W (q.at q.u) l.1.1 l.1.2 ω‖ : ℝ) : ℂ)‖}) ≤
        ENNReal.ofReal (2 * (W : ℝ) ^ (-(4 * r * Aδ))) := by
      refine (measure_union_le _ _).trans ?_
      rw [two_mul, ENNReal.ofReal_add hxD hxD]
      refine add_le_add (hDW n (Finset.mem_Icc.2 ⟨hn1, by omega⟩) q hq) ?_
      rcases Nat.lt_or_ge n 2 with hn2 | hn2
      · have hn : n = 1 := by omega
        subst hn
        refine le_of_eq_of_le (b := 0) ?_ (by positivity)
        refine measure_eq_zero_iff_ae_notMem.2 (ae_of_all _ fun ω hω => ?_)
        obtain ⟨l, -⟩ := hω
        have h1 := l.2
        rw [coneNode_wordDiam_one] at h1
        have h2 : 0 ≤ (W : ℝ) ^ ν * ellProp q.g q.L q.u := by
          have := coneNode_ell_ge_one hg0 hL1 q.u
          positivity
        push_cast at h1
        linarith
      · exact hTW n (Finset.mem_Icc.2 ⟨hn2, by omega⟩) q hq
    refine ⟨hfru.2.2.2.1, coneNode_assemble q.g q.E hW1 hL3 hm σ
      (fun v b => projCoef 𝐏[q] q.u v a b) hs hsu hu1 hY r hr
      (by positivity) (by positivity) hKβ0 hKb0 (by positivity) (by positivity) (by positivity)
      hΨs hΨr hB0 hCfin0 _ hbad hrate (fun v hv =>
        ⟨((hcr v hv).1.1 hσ).2.trans (coneNode_crude_le hW1 (by omega) hCgK hKc1 hCKgm),
          (hcr v hv).2.1.2.trans (coneNode_crude_le hW1 (by omega) hCγK hKc1 hCKγm)⟩)
      _ hBinμ (fun ω hω => (hip W q Ak ν ((W : ℝ) ^ ν * (W : ℝ) ^ (-A)) (fPm W) ω σ a hW1 hAk hν
        hτ0 hs hsu hu1 hL3 hg0 hm (hK q.s le_rfl (hsu.trans hut)) (hK q.u hsu hut) hI
        (hPm q.s le_rfl hsu) hPm1 hτθ (hgood_s ω hω).1 (hgood_s ω hω).2).trans (by
          have h1 := le_max_left Cip Cis
          have h2 : 0 ≤ ((4 * (W : ℝ) ^ ν + 2) ^ (2 * (n + 1)) + 1) *
              zetaProp q.g W q.L q.u ^ (n + 1) * (W : ℝ) ^ ν := by positivity
          have h3 : 0 ≤ fPm W ^ (4 * (n + 1)) * ((W : ℝ) ^ ν * (W : ℝ) ^ (-A)) := by
            have := hPmp (4 * (n + 1)); positivity
          nlinarith only [h1, h2, h3]))
      hf4s.1.1 hKs hf2u.1.1 _ hZc _ hBrμ (fun ω hω => by
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hω
        rw [hZeq ω]
        refine coneNode_row R n hn1 W q Ak ν ((W : ℝ) ^ ν * (W : ℝ) ^ (-A)) ((W : ℝ) ^ R.C)
          (fZc W) ω σ a (fun j => Ed j W q) hW1 hAk hν hτ0 (by linarith) hu1 hσ hL3 hg0 hm hmim
          (hK q.u hsu hut) ?_ hzu (hEd0' n) (fun w => hω.1 w) fun w hw => ?_
        · have h := hbud q.u hsu hut
          have : 0 ≤ gammaG q.g * q.L := by have := coneNode_gamma_pos q.g; positivity
          linarith
        · have := hω.2 ⟨w, hw⟩
          rwa [Complex.norm_real, Real.norm_of_nonneg (by positivity)] at this)
      (hf4u.2.2.1.1.congr (ae_of_all _ fun ω => by simp only [hZeq ω]; rfl))
      (le_of_eq_of_le (integral_congr_ae (ae_of_all _ fun ω => by simp only [hZeq ω]; rfl))
        (hf4u.2.2.1.2.trans (coneNode_crude_le hW1 (by omega) (le_max_left _ _) hKf1
        (le_abs_self CKf))))
      (hf2u.2.2.1.1.congr (ae_of_all _ fun ω => by simp only [hZeq ω]; rfl))
      (fun ω => flowErr W (q.at q.u) a σ ω) (fun ω => (add_sub_cancel _ _).symm) hfru.2.2.2.1
      hf2u.2.2.2.1 hfin⟩
  · -- words with a stable leg: the propagated field
    have hσ' : ∃ j, σ (finRotate (n + 1) j) = σ j := by
      obtain ⟨j, hj⟩ := not_forall.mp hσ
      refine ⟨j, ?_⟩
      revert hj
      cases σ (finRotate (n + 1) j) <;> cases σ j <;> simp
    have hrate : ∀ v ∈ Set.Ioo q.s q.u, ∀ ω,
        ω ∉ coneNode_Bad W q n ν A (fun j => Ed j W q) (fun j => Bl j W q) CKc v →
        ‖blockGen W q.L (gammaG q.g) (fun r' N => ∑ b : Fin (n + 1) → Fin q.L,
          (∏ j, pairU (gammaG q.g) 𝐌[q] r' q.u (σ j) (σ (finRotate (n + 1) j)) (a j) (b j)) *
          (resLoop q.g q.E (mRoot q.g q.L q.E) b σ r' N -
            primLoop q.g W q.L q.E (mRoot q.g q.L q.E) r' b σ)) v (flowH q.g W q.L v ω)‖ ≤
          coneNode_Kβ n Cβ R.C (4 * (W : ℝ) ^ ν + 2) ((W : ℝ) ^ ν) (fPm W)
            (zetaProp q.g W q.L q.u) (nodeEnv (n + 1) (fun j => Ed j W q) (fun j => Bl j W q)
              (zetaProp q.g W q.L q.t))
            (gammaG q.g * W * q.L * ((n + 1) * (fXc W + (W : ℝ) ^ ν * fZc W ^ (n + 1))) +
              R.C * fZc W) ((W : ℝ) ^ ν * (W : ℝ) ^ (-A)) / (1 - v) ∧
        ‖blockGamma W q.L (gammaG q.g)
          (fun N => ∑ b : Fin (n + 1) → Fin q.L,
            (∏ j, pairU (gammaG q.g) 𝐌[q] v q.u (σ j) (σ (finRotate (n + 1) j)) (a j) (b j)) *
            (resLoop q.g q.E (mRoot q.g q.L q.E) b σ v N -
              primLoop q.g W q.L q.E (mRoot q.g q.L q.E) v b σ))
          (fun N => ∑ b : Fin (n + 1) → Fin q.L,
            (∏ j, pairU (gammaG q.g) 𝐌[q] v q.u (σ j) (σ (finRotate (n + 1) j)) (a j) (b j)) *
            (resLoop q.g q.E (mRoot q.g q.L q.E) b σ v N -
              primLoop q.g W q.L q.E (mRoot q.g q.L q.E) v b σ)) (flowH q.g W q.L v ω)‖ ≤
          coneNode_Kb n Cβ (4 * (W : ℝ) ^ ν + 2) ((W : ℝ) ^ ν) (fPm W) (zetaProp q.g W q.L q.u)
            (Bl (2 * (n + 1) + 2) W q) (gammaG q.g * W * q.L) ((W : ℝ) ^ ν * (W : ℝ) ^ (-A)) /
            (1 - v) := by
      intro v hv ω hω
      obtain ⟨g1, g2, g3, g4, g5⟩ := coneNode_Bad_good W hW1 q n ν A CKs (fun j => Ed j W q)
        (fun j => Bl j W q) CKc hCKsj v ω hω
      have hv1 : q.s ≤ v := hv.1.le
      have hv2 : v ≤ q.u := hv.2.le
      have h1v : 0 < 1 - v := by linarith
      have h := hrs W q v Ak ν ((W : ℝ) ^ ν * (W : ℝ) ^ (-A)) (fXc W) (fZc W) (fPm W) ω σ a
        (fun j => Ed j W q) (fun j => Bl j W q) hW1 hAk hν hτ0 (by linarith) hv2 hut ht1 hσ' hL3
        hg0 hm hmim hdy1 hdy2 (hK v hv1 (hv2.trans hut)) (hK q.u hsu hut) hI (hPm v hv1 hv2)
        hPm1 (hadmv v hv1 (hv2.trans hut)).2.2 hZc1 hXc0 hEd0' hBl0' g1 g2 g3 g4 g5
        (hprim v hv1 (hv2.trans hut)) (hptail v hv1 (hv2.trans hut))
      refine ⟨h.1.trans (div_le_div_of_nonneg_right (coneNode_Kβ_mono (le_max_right _ _) hCns.le
        le_rfl (by positivity) (by positivity) (by linarith) hζu0 hRC0 (by linarith) hTc0 hτ0)
        h1v.le), h.2.trans (div_le_div_of_nonneg_right (coneNode_Kb_mono (le_max_right _ _)
        hCns.le le_rfl (by positivity) (by positivity) (by linarith) hζu0 (hBl0' _) hγL0 hτ0)
        h1v.le)⟩
    have hY := heatClass_propField q.g q.E (mRoot q.g q.L q.E) W q.L hW1 hL3 hm σ a (v := q.u)
      ⟨by linarith, hu1⟩ (a' := -1 / 2) (b' := (q.u + 1) / 2) (by norm_num) (by linarith)
    refine ⟨hfru.2.2.2.1, coneNode_assemble q.g q.E hW1 hL3 hm σ
      (fun v b => ∏ j, pairU (gammaG q.g) 𝐌[q] v q.u (σ j) (σ (finRotate (n + 1) j)) (a j) (b j))
      hs hsu hu1 hY r hr
      (by positivity) (by positivity) hKβ0 hKb0 (by positivity) (by positivity) (by positivity)
      hΨs hΨr hB0 hCfin0 _ hbad hrate (fun v hv =>
        ⟨(hcr v hv).1.2.2.trans (coneNode_crude_le hW1 (by omega) hCgK hKc1 hCKgm),
          (hcr v hv).2.2.2.trans (coneNode_crude_le hW1 (by omega) hCγK hKc1 hCKγm)⟩)
      _ hBinμ (fun ω hω => (his W q Ak ν ((W : ℝ) ^ ν * (W : ℝ) ^ (-A)) (fPm W) ω σ a hσ' hW1
        hAk hν hτ0 hs hsu hu1 hL3 hg0 hm hdy1 hdy2 (hK q.s le_rfl (hsu.trans hut))
        (hK q.u hsu hut) hI (hPm q.s le_rfl hsu) hPm1 (hgood_s ω hω).1 (hgood_s ω hω).2).trans (by
          have h1 := le_max_right Cip Cis
          have h2 : 0 ≤ ((4 * (W : ℝ) ^ ν + 2) ^ (2 * (n + 1)) + 1) *
              zetaProp q.g W q.L q.u ^ (n + 1) * (W : ℝ) ^ ν := by positivity
          have h3 : 0 ≤ fPm W ^ (4 * (n + 1)) * ((W : ℝ) ^ ν * (W : ℝ) ^ (-A)) := by
            have := hPmp (4 * (n + 1)); positivity
          nlinarith only [h1, h2, h3]))
      hf4s.2.1.1 (hf4s.2.1.2.trans (coneNode_crude_le hW1 (by omega) (le_max_left _ _) hKf1
        (le_abs_self CKf))) hf2u.2.1.1 (fun _ => 0) continuous_const ∅ (by simp)
      (fun ω _ => by simpa using hΨr) (by simp) (by
        simp only [norm_zero]
        rw [zero_pow (by omega), integral_zero]
        positivity) (by simp) (fun ω => flowErr W (q.at q.u) a σ ω) (fun ω => by
          have h := (coneRates_fieldSelf q.g q.E 𝐦[q] hL3 hm (by linarith) hu1).2 (n + 1) σ
            (fun b => flowErr W (q.at q.u) b σ ω) a
          beta_reduce at h
          change flowErr W (q.at q.u) a σ ω = (∑ b : Fin (n + 1) → Fin q.L, (∏ j, pairU (gammaG q.g)
            𝐌[q] q.u q.u (σ j) (σ (finRotate (n + 1) j)) (a j) (b j)) *
              flowErr W (q.at q.u) b σ ω) + 0
          rw [h, add_zero]) hfru.2.2.2.1 hf2u.2.2.2.1 hfin⟩


/-- One node of the cone (C.41) [fo:eq:finite-improvement] of Step 3 of Appendix C.3
[sec:gc-one-step], in moment form at each word. The envelopes are deterministic and do not depend
on the time `u` of the step point: `E_j` for the loop errors of lengths `1 ≤ j ≤ n` (the length
`n` from the preceding round) and `B_j` for the loops of lengths `n + 1` and `2n + 2`. The moment
comparison along `[s, u]`, applied to the propagated projected field (C.35)
[fo:eq:projected-error-equation] for cyclically alternating words and to the stable-leg hierarchy
for the other words, gives the recurrence (C.36) [gc:eq:recurrence]:
`E|D_n(u; w)|^r ≤ C_r (W^δ ζ_u^n Ψ)^r` with `Ψ` the value of `nodeEnv` at `ζ_t`. -/
theorem step3_nodeMoment (R : PropRegime) (I : PropInputs R.base R.J) (c N cp θ : ℝ)
    (hinc : IncrementInput R.base R.J)
    (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q})
    (hSu : ∀ W, ∀ q ∈ S W, ∀ v : ℝ, q.s ≤ v → v ≤ q.u →
      (⟨q.g, q.E, q.L, q.s, q.t, v⟩ : StepPt) ∈ S W)
    (hin : OneStepInput cp θ (fun q : StepPt => q.at q.s) S)
    (htail : ∀ k : ℕ, 2 ≤ k → ∀ ε A : ℝ, 0 < ε → 0 < A → PrecMax StepPt.L S
      (Λ := fun W q => {w : Word k q.L // (W : ℝ) ^ ε * ellProp q.g q.L q.u < wordDiam w.1})
      (fun W q w ω => ((‖loopTr (flowG W (q.at q.u) ω) w.1.1 w.1.2‖ +
        ‖flowErr W (q.at q.u) w.1.1 w.1.2 ω‖ : ℝ) : ℂ))
      (fun W _ _ => (W : ℝ) ^ (-A)))
    (n : ℕ) (hn : 2 ≤ n) (Ed Bl : ℕ → ℕ → StepPt → ℝ)
    (hEd0 : ∀ j W q, 0 ≤ Ed j W q) (hBl0 : ∀ j W q, 0 ≤ Bl j W q)
    (hEdu : ∀ j W (q : StepPt) (v : ℝ), Ed j W ⟨q.g, q.E, q.L, q.s, q.t, v⟩ = Ed j W q)
    (hBlu : ∀ j W (q : StepPt) (v : ℝ), Bl j W ⟨q.g, q.E, q.L, q.s, q.t, v⟩ = Bl j W q)
    (hD : ∀ j : ℕ, 1 ≤ j → j ≤ n → PrecMax StepPt.L S (Λ := fun _ q => Word j q.L)
      (fun W q w ω => flowErr W (q.at q.u) w.1 w.2 ω)
      (fun W q _ => Ed j W q * zetaProp q.g W q.L q.u ^ j))
    (hL : ∀ j : ℕ, j = n + 1 ∨ j = 2 * n + 2 → PrecMax StepPt.L S (Λ := fun _ q => Word j q.L)
      (fun W q w ω => loopTr (flowG W (q.at q.u) ω) w.1 w.2)
      (fun W q _ => Bl j W q * zetaProp q.g W q.L q.u ^ (j - 1))) :
    ∀ r : ℕ, 1 ≤ r → ∀ δ : ℝ, 0 < δ → ∃ Cr : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ q ∈ S W, ∀ w : Word n q.L,
        Integrable (fun ω => ‖flowErr W (q.at q.u) w.1 w.2 ω‖ ^ r) (μ W q.L) ∧
        ∫ ω, ‖flowErr W (q.at q.u) w.1 w.2 ω‖ ^ r ∂(μ W q.L) ≤
          Cr * ((W : ℝ) ^ δ * (zetaProp q.g W q.L q.u ^ n *
            nodeEnv n (fun j => Ed j W q) (fun j => Bl j W q) (zetaProp q.g W q.L q.t))) ^ r := by
  exact coneNode_main R I c N cp θ hinc S hS hSu hin htail n hn Ed Bl hEd0 hBl0 hEdu hBlu hD hL


/-- One node of the cone (C.41) [fo:eq:finite-improvement] of Step 3 of Appendix C.3
[sec:gc-one-step]: under the hypotheses of `step3_nodeMoment`, the recurrence (C.36)
[gc:eq:recurrence] `max_w |D_n(u; w)| ≺ ζ_u^n Ψ` with the maximum over all words inside the
probability, by the sampling of Lemma 5.10(b) [fo:lem:sampling-continuity]. -/
theorem step3_node (R : PropRegime) (I : PropInputs R.base R.J) (c N cp θ : ℝ)
    (hinc : IncrementInput R.base R.J)
    (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q})
    (hSu : ∀ W, ∀ q ∈ S W, ∀ v : ℝ, q.s ≤ v → v ≤ q.u →
      (⟨q.g, q.E, q.L, q.s, q.t, v⟩ : StepPt) ∈ S W)
    (hin : OneStepInput cp θ (fun q : StepPt => q.at q.s) S)
    (htail : ∀ k : ℕ, 2 ≤ k → ∀ ε A : ℝ, 0 < ε → 0 < A → PrecMax StepPt.L S
      (Λ := fun W q => {w : Word k q.L // (W : ℝ) ^ ε * ellProp q.g q.L q.u < wordDiam w.1})
      (fun W q w ω => ((‖loopTr (flowG W (q.at q.u) ω) w.1.1 w.1.2‖ +
        ‖flowErr W (q.at q.u) w.1.1 w.1.2 ω‖ : ℝ) : ℂ))
      (fun W _ _ => (W : ℝ) ^ (-A)))
    (n : ℕ) (hn : 2 ≤ n) (Ed Bl : ℕ → ℕ → StepPt → ℝ)
    (hEd0 : ∀ j W q, 0 ≤ Ed j W q) (hBl0 : ∀ j W q, 0 ≤ Bl j W q)
    (hEdu : ∀ j W (q : StepPt) (v : ℝ), Ed j W ⟨q.g, q.E, q.L, q.s, q.t, v⟩ = Ed j W q)
    (hBlu : ∀ j W (q : StepPt) (v : ℝ), Bl j W ⟨q.g, q.E, q.L, q.s, q.t, v⟩ = Bl j W q)
    (hD : ∀ j : ℕ, 1 ≤ j → j ≤ n → PrecMax StepPt.L S (Λ := fun _ q => Word j q.L)
      (fun W q w ω => flowErr W (q.at q.u) w.1 w.2 ω)
      (fun W q _ => Ed j W q * zetaProp q.g W q.L q.u ^ j))
    (hL : ∀ j : ℕ, j = n + 1 ∨ j = 2 * n + 2 → PrecMax StepPt.L S (Λ := fun _ q => Word j q.L)
      (fun W q w ω => loopTr (flowG W (q.at q.u) ω) w.1 w.2)
      (fun W q _ => Bl j W q * zetaProp q.g W q.L q.u ^ (j - 1))) :
    PrecMax StepPt.L S (Λ := fun _ q => Word n q.L)
      (fun W q w ω => flowErr W (q.at q.u) w.1 w.2 ω)
      (fun W q _ => zetaProp q.g W q.L q.u ^ n *
        nodeEnv n (fun j => Ed j W q) (fun j => Bl j W q) (zetaProp q.g W q.L q.t)) := by
  classical
  obtain ⟨W₁, hW₁⟩ := R.dyson
  set S' : ℕ → Set StepPt := fun W => if max W₁ 2 ≤ W then S W else ∅ with hS'def
  have hS'S : ∀ W, S' W ⊆ S W := by
    intro W q hq
    simp only [hS'def] at hq
    split_ifs at hq with h
    · exact hq
    · exact absurd hq (Set.notMem_empty q)
  have hmom := step3_nodeMoment R I c N cp θ hinc S hS hSu hin htail n hn Ed Bl hEd0 hBl0 hEdu
    hBlu hD hL
  have hY : ∀ W, ∀ q ∈ S' W, (W : ℝ) ^ (-((2 * n : ℕ) : ℝ)) ≤ zetaProp q.g W q.L q.u ^ n *
      nodeEnv n (fun j => Ed j W q) (fun j => Bl j W q) (zetaProp q.g W q.L q.t) := by
    intro W q hq
    simp only [hS'def] at hq
    split_ifs at hq with hW
    swap
    · exact absurd hq (Set.notMem_empty q)
    have hW2 : 2 ≤ W := le_trans (le_max_right _ _) hW
    have hWr : (2 : ℝ) ≤ W := by exact_mod_cast hW2
    have hWpos : (0 : ℝ) < W := by linarith
    obtain ⟨⟨d, hdJ, hreach⟩, hs1, hsu, hut, hst, hWt, -⟩ := hS W hq
    obtain ⟨hL3, hg0, -⟩ := hW₁ W (le_trans (le_max_left _ _) hW) d (q.at q.t) hdJ.le hreach
    change 3 ≤ q.L at hL3
    change 0 ≤ q.g at hg0
    have hγ : 0 < gammaG q.g := by
      unfold gammaG
      have : (1 : ℝ) ≤ max 1 q.g := le_max_left _ _
      positivity
    have hγ1 : gammaG q.g ≤ 1 := by
      unfold gammaG
      have : (1 : ℝ) ≤ max 1 q.g := le_max_left _ _
      exact inv_le_one_of_one_le₀ (one_le_pow₀ this)
    have hW3 : 0 < (W : ℝ) ^ (-3 : ℝ) := Real.rpow_pos_of_pos hWpos _
    -- `ζ_v ≥ (2W)⁻¹` and `ζ_v ≥ 0` for `v ∈ [u, t]`
    have hzeta : ∀ v : ℝ, 1 / 2 ≤ v → v ≤ q.t →
        (2 * (W : ℝ))⁻¹ ≤ zetaProp q.g W q.L v := by
      intro v hv1 hvt
      have h1v : 0 < 1 - v := by linarith
      have h1v' : 1 - v ≤ 1 := by linarith
      have hsq : 0 < Real.sqrt (gammaG q.g * (1 - v)) := Real.sqrt_pos.mpr (by positivity)
      have hℓ1 : 1 ≤ ellProp q.g q.L v := by
        unfold ellProp
        refine le_min ?_ ?_
        · have : (3 : ℝ) ≤ q.L := by exact_mod_cast hL3
          linarith
        · have : 0 ≤ q.g / Real.sqrt (gammaG q.g * (1 - v)) := div_nonneg hg0 hsq.le
          linarith
      have hprod : ellProp q.g q.L v * (1 - v) * gammaG q.g ≤ 2 := by
        have hle : ellProp q.g q.L v ≤ 1 + q.g / Real.sqrt (gammaG q.g * (1 - v)) :=
          min_le_right _ _
        have hgm : q.g * Real.sqrt (gammaG q.g * (1 - v)) ≤ 1 := by
          have hmx : 0 < max 1 q.g := lt_of_lt_of_le one_pos (le_max_left _ _)
          have hsq1 : Real.sqrt (gammaG q.g * (1 - v)) ≤ Real.sqrt (gammaG q.g) :=
            Real.sqrt_le_sqrt (by nlinarith)
          have hsγ : Real.sqrt (gammaG q.g) = (max 1 q.g)⁻¹ := by
            unfold gammaG
            rw [Real.sqrt_inv, Real.sqrt_sq hmx.le]
          calc q.g * Real.sqrt (gammaG q.g * (1 - v)) ≤ q.g * (max 1 q.g)⁻¹ := by
                rw [← hsγ]; exact mul_le_mul_of_nonneg_left hsq1 hg0
            _ ≤ 1 := by
                rw [← div_eq_mul_inv, div_le_one hmx]; exact le_max_right _ _
        have hkey : (1 + q.g / Real.sqrt (gammaG q.g * (1 - v))) * (1 - v) * gammaG q.g =
            (1 - v) * gammaG q.g + q.g * Real.sqrt (gammaG q.g * (1 - v)) := by
          have hss : Real.sqrt (gammaG q.g * (1 - v)) ^ 2 = gammaG q.g * (1 - v) :=
            Real.sq_sqrt (by positivity)
          field_simp
          nlinarith [hss]
        calc ellProp q.g q.L v * (1 - v) * gammaG q.g ≤
            (1 + q.g / Real.sqrt (gammaG q.g * (1 - v))) * (1 - v) * gammaG q.g := by
              gcongr
          _ = (1 - v) * gammaG q.g + q.g * Real.sqrt (gammaG q.g * (1 - v)) := hkey
          _ ≤ 1 * 1 + 1 := by gcongr
          _ = 2 := by norm_num
      have hpos : 0 < (W : ℝ) * ellProp q.g q.L v * (1 - v) * gammaG q.g := by
        have : 0 < ellProp q.g q.L v := by linarith
        positivity
      unfold zetaProp
      rw [inv_le_inv₀ (by positivity) hpos]
      calc (W : ℝ) * ellProp q.g q.L v * (1 - v) * gammaG q.g =
          (W : ℝ) * (ellProp q.g q.L v * (1 - v) * gammaG q.g) := by ring
        _ ≤ (W : ℝ) * 2 := by gcongr
        _ = 2 * W := by ring
    have hzu := hzeta q.u (by linarith) hut
    have hzt := hzeta q.t (by linarith) le_rfl
    have hzt0 : 0 ≤ zetaProp q.g W q.L q.t := le_trans (by positivity) hzt
    have henv : 1 ≤ nodeEnv n (fun j => Ed j W q) (fun j => Bl j W q) (zetaProp q.g W q.L q.t) := by
      unfold nodeEnv
      have h1 : 0 ≤ ∑ j ∈ Finset.Ico 1 n, Ed j W q :=
        Finset.sum_nonneg fun j _ => hEd0 j W q
      have h2 : 0 ≤ ∑ p ∈ Finset.Icc 2 n, Ed p W q * Ed (n + 2 - p) W q :=
        Finset.sum_nonneg fun p _ => mul_nonneg (hEd0 p W q) (hEd0 _ W q)
      have h3 : 0 ≤ Ed 1 W q * Bl (n + 1) W q := mul_nonneg (hEd0 1 W q) (hBl0 _ W q)
      have h4 : 0 ≤ Real.sqrt (Bl (2 * n + 2) W q) := Real.sqrt_nonneg _
      have h5 := mul_nonneg hzt0 h2
      linarith
    have hW2' : (W : ℝ)⁻¹ ^ 2 ≤ (2 * (W : ℝ))⁻¹ := by
      rw [inv_pow, inv_le_inv₀ (by positivity) (by positivity)]
      nlinarith
    have hpow : (W : ℝ) ^ (-((2 * n : ℕ) : ℝ)) = ((W : ℝ)⁻¹ ^ 2) ^ n := by
      rw [Real.rpow_neg hWpos.le, Real.rpow_natCast, ← pow_mul, inv_pow, mul_comm]
    rw [hpow]
    calc ((W : ℝ)⁻¹ ^ 2) ^ n ≤ zetaProp q.g W q.L q.u ^ n :=
          pow_le_pow_left₀ (by positivity) (hW2'.trans hzu) n
      _ = zetaProp q.g W q.L q.u ^ n * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left henv (pow_nonneg (le_trans (by positivity) hzu) n)
  have hmom' : ∀ r : ℕ, 1 ≤ r → ∀ δ : ℝ, 0 < δ → ∃ Cr : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ q ∈ S' W, ∀ w : Word n q.L,
        Integrable (fun ω => ‖flowErr W (q.at q.u) w.1 w.2 ω‖ ^ r) (μ W q.L) ∧
        ∫ ω, ‖flowErr W (q.at q.u) w.1 w.2 ω‖ ^ r ∂(μ W q.L) ≤
          Cr * ((W : ℝ) ^ δ * (zetaProp q.g W q.L q.u ^ n *
            nodeEnv n (fun j => Ed j W q) (fun j => Bl j W q) (zetaProp q.g W q.L q.t))) ^ r := by
    intro r hr δ hδ
    obtain ⟨Cr, W₀, h⟩ := hmom r hr δ hδ
    exact ⟨Cr, W₀, fun W hW q hq w => h W hW q (hS'S W hq) w⟩
  have hP := precMax_of_sampleMoment R I c N S' (fun W => (hS'S W).trans (hS W)) n
    (by omega) _ _ hY hmom'
  intro ε D hε hD'
  obtain ⟨W₀, hW₀⟩ := hP ε D hε hD'
  refine ⟨max W₀ (max W₁ 2), fun W hW q hq => ?_⟩
  have hq' : q ∈ S' W := by
    simp only [hS'def]
    rw [ite_eq_left_iff.mpr (fun h => absurd (le_trans (le_max_right _ _) hW) h)]
    exact hq
  exact hW₀ W (le_trans (le_max_left _ _) hW) q hq'

end LSBA
