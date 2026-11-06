import LSBA.Upper.AngularPairing
import LSBA.Upper.OperatorSemigroup
import LSBA.Upper.OperatorIteration

/-!
# Lemma 8.11 [up:lem:angular]: from Gaussian divergence to contraction

Lemma 8.11 [up:lem:angular]: cutoffs and fields satisfying (8.34) [up:eq:angular-geometry] and
(8.35) [up:eq:field] at every incoming flag give the contraction (8.30) [up:eq:P-contraction]
with factor `1 - c/𝔟`, `c = min{1, 1/(9C)}/128`, for bounded nonnegative measurable `h`
satisfying (8.25) [up:eq:invariant-function], and for every bounded measurable `h` when `K_out = 0`;
and the passage from the local length `q` to a multiple `q m` (proof of Theorems 3.2
[thm:sharp-small-upper] and 3.3 [thm:compact-upper]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The angular `L⁴` norm bound is monotone in the bound. -/
private lemma angular_L4Le_mono {W : ℕ} {h : IsoFlag W → ℝ} {M M' : ℝ} (hM : M ≤ M')
    (hL : AngL4Le h M) : AngL4Le h M' := fun x =>
  (hL x).trans (by gcongr)

/-- The angular `L⁴` norm bound is monotone in the absolute value of the function. -/
private lemma angular_L4Le_of_abs_le {W : ℕ} {f f' : IsoFlag W → ℝ} {M : ℝ}
    (hle : ∀ y, |f y| ≤ |f' y|) (hL : AngL4Le f' M) : AngL4Le f M := fun x =>
  (lintegral_mono fun y => by
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
    exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal (hle y)) 4).trans (hL x)

/-- The angular `L⁴` norm bound is homogeneous. -/
private lemma angular_L4Le_smul {W : ℕ} {h : IsoFlag W → ℝ} {M : ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hL : AngL4Le h M) : AngL4Le (r • h) (r * M) := fun x => by
  have h1 : ∀ y, ‖(r • h) y‖ₑ ^ 4 = ENNReal.ofReal r ^ 4 * ‖h y‖ₑ ^ 4 := fun y => by
    rw [Pi.smul_apply, smul_eq_mul, enorm_mul, Real.enorm_of_nonneg hr, mul_pow]
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),
    ENNReal.ofReal_mul hr, mul_pow]
  gcongr
  exact hL x

/-- `P_{1/2}` maps nonnegative functions to nonnegative functions. -/
private lemma angular_halfOp_nonneg {W : ℕ} (g E : ℝ) (q : ℕ) {h : IsoFlag W → ℝ}
    (hh : 0 ≤ h) : 0 ≤ halfOp W g E q h := fun _ =>
  integral_nonneg fun _ => mul_nonneg (Real.exp_pos _).le (hh _)

/-- Fourth roots in `ℝ≥0∞`: `X^{1/4} ≤ Y ↔ X ≤ Y⁴`. -/
private lemma angular_quarter_le_iff (X Y : ℝ≥0∞) : X ^ (1 / 4 : ℝ) ≤ Y ↔ X ≤ Y ^ 4 := by
  rw [one_div, ENNReal.rpow_inv_le_iff (by norm_num)]
  norm_cast

/-- Minkowski step of the proof of Lemma 8.11 [up:lem:angular] (positivity removal): adding the
constant `ε` to a nonnegative measurable function of angular `L⁴` norm at most `M` gives angular
`L⁴` norm at most `M + ε`. -/
private lemma angular_L4Le_add_const {W : ℕ} {h : IsoFlag W → ℝ} (hm : Measurable h)
    (hnn : 0 ≤ h) {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε) (hL : AngL4Le h M) :
    AngL4Le (fun z => h z + ε) (M + ε) := by
  intro x
  have := isProbabilityMeasure_circleMeasure x
  have hmin := ENNReal.lintegral_Lp_add_le (μ := circleMeasure x) (p := 4)
    (f := fun y => ‖h y‖ₑ) (g := fun _ => ENNReal.ofReal ε) hm.enorm.aemeasurable
    aemeasurable_const (by norm_num)
  simp only [ENNReal.rpow_ofNat, Pi.add_apply] at hmin
  have h1 : (∫⁻ y, ‖h y‖ₑ ^ 4 ∂(circleMeasure x)) ^ (1 / 4 : ℝ) ≤ ENNReal.ofReal M :=
    (angular_quarter_le_iff _ _).mpr (hL x)
  have h2 : (∫⁻ _y, ENNReal.ofReal ε ^ 4 ∂(circleMeasure x)) ^ (1 / 4 : ℝ) ≤ ENNReal.ofReal ε :=
    (angular_quarter_le_iff _ _).mpr (by simp)
  have h3 := (hmin.trans (add_le_add h1 h2))
  rw [← ENNReal.ofReal_add hM hε, angular_quarter_le_iff] at h3
  refine le_trans (le_of_eq (lintegral_congr fun y => ?_)) h3
  rw [Real.enorm_of_nonneg (add_nonneg (hnn y) hε), ENNReal.ofReal_add (hnn y) hε,
    Real.enorm_of_nonneg (hnn y)]

/-- Duality step of the proof of Lemma 8.11 [up:lem:angular]: if the pairing
`∫ ρ^{3/4} P_{1/2} h dm_U ≤ ρ₀` holds for every probability density `ρ` on the circle through
`x`, then the angular `L⁴` norm of the nonnegative bounded measurable function `P_{1/2} h` is at
most `ρ₀` (take `ρ = (P_{1/2} h)⁴ / ‖P_{1/2} h‖_{L⁴}⁴`). -/
private lemma angular_duality {W : ℕ} {g E : ℝ} {q : ℕ} {ρ₀ : ℝ} (hρ0 : 0 ≤ ρ₀)
    {h : IsoFlag W → ℝ} (hh : IsBddMeas h) (hnn : 0 ≤ h)
    (hpair : ∀ (x : IsoFlag W) (ρ : IsoFlag W → ℝ), Measurable ρ → (∀ y, 0 ≤ ρ y) →
      ∫⁻ y, ENNReal.ofReal (ρ y) ∂(circleMeasure x) = 1 →
      ∫⁻ y, ENNReal.ofReal (ρ y ^ (3 / 4 : ℝ) * halfOp W g E q h y) ∂(circleMeasure x) ≤
        ENNReal.ofReal ρ₀) :
    AngL4Le (halfOp W g E q h) ρ₀ := by
  intro x
  have hP := halfOp_isBddMeas g E q hh
  have hG0 : ∀ y, 0 ≤ halfOp W g E q h y := angular_halfOp_nonneg g E q hnn
  set G := halfOp W g E q h with hG
  have := isProbabilityMeasure_circleMeasure x
  obtain ⟨hGm, B, hB⟩ := hP
  have hen : ∀ y, ‖G y‖ₑ ^ 4 = ENNReal.ofReal (G y ^ 4) := fun y => by
    rw [Real.enorm_of_nonneg (hG0 y), ENNReal.ofReal_pow (hG0 y)]
  simp_rw [hen]
  set a := ∫⁻ y, ENNReal.ofReal (G y ^ 4) ∂(circleMeasure x) with ha
  have ha_top : a ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal (B ^ 4)) ENNReal.ofReal_ne_top ?_
    calc a ≤ ∫⁻ _y, ENNReal.ofReal (B ^ 4) ∂(circleMeasure x) := lintegral_mono fun y => by
            refine ENNReal.ofReal_le_ofReal ?_
            calc G y ^ 4 = |G y| ^ 4 := by rw [abs_of_nonneg (hG0 y)]
              _ ≤ B ^ 4 := pow_le_pow_left₀ (abs_nonneg _) (hB y) 4
      _ = ENNReal.ofReal (B ^ 4) := by simp
  rcases eq_or_ne a 0 with h0 | h0
  · rw [h0]; exact bot_le
  obtain ⟨I, hI⟩ : ∃ I : ℝ, a = ENNReal.ofReal I :=
    ⟨a.toReal, (ENNReal.ofReal_toReal ha_top).symm⟩
  have hIpos : 0 < I := by
    have : 0 < a := pos_iff_ne_zero.mpr h0
    rw [hI] at this
    exact ENNReal.ofReal_pos.mp this
  set J : ℝ := I ^ (1 / 4 : ℝ) with hJ
  have hJpos : 0 < J := Real.rpow_pos_of_pos hIpos _
  have hJ4 : J ^ 4 = I := by
    rw [hJ, ← Real.rpow_natCast, ← Real.rpow_mul hIpos.le]
    norm_num
  set ρ : IsoFlag W → ℝ := fun y => (G y / J) ^ 4 with hρ
  have hρm : Measurable ρ := (hGm.div_const J).pow_const 4
  have hρnn : ∀ y, 0 ≤ ρ y := fun y => pow_nonneg (div_nonneg (hG0 y) hJpos.le) 4
  have hρ_eq : ∀ y, ENNReal.ofReal (ρ y) = ENNReal.ofReal I⁻¹ * ENNReal.ofReal (G y ^ 4) :=
    fun y => by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hIpos.le)]
      congr 1
      simp only [hρ, div_pow, hJ4]
      ring
  have hρ1 : ∫⁻ y, ENNReal.ofReal (ρ y) ∂(circleMeasure x) = 1 := by
    simp_rw [hρ_eq]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← ha, hI,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hIpos.le), inv_mul_cancel₀ hIpos.ne']
    exact ENNReal.ofReal_one
  have key : ∀ u : ℝ, 0 ≤ u → (u ^ 4) ^ (3 / 4 : ℝ) = u ^ 3 := fun u hu => by
    rw [← Real.rpow_natCast u 4, ← Real.rpow_mul hu]
    norm_num
  have hid : ∀ y, ρ y ^ (3 / 4 : ℝ) * G y = J * ρ y := fun y => by
    have hu : 0 ≤ G y / J := div_nonneg (hG0 y) hJpos.le
    have hGy : G y = J * (G y / J) := by field_simp
    simp only [hρ]
    rw [key _ hu]
    nth_rewrite 2 [hGy]
    ring
  have hpr := hpair x ρ hρm hρnn hρ1
  simp_rw [hid] at hpr
  simp_rw [show ∀ y, ENNReal.ofReal (J * ρ y) = ENNReal.ofReal J * ENNReal.ofReal (ρ y) from
    fun y => ENNReal.ofReal_mul hJpos.le] at hpr
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hρ1, mul_one,
    ENNReal.ofReal_le_ofReal_iff hρ0] at hpr
  rw [hI, ← hJ4, ← ENNReal.ofReal_pow hρ0]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hJpos.le hpr 4)

/-- Scalar multiples of bounded measurable functions are bounded measurable. -/
private lemma angular_isBddMeas_smul {W : ℕ} {h : IsoFlag W → ℝ} (hh : IsBddMeas h) (r : ℝ) :
    IsBddMeas (r • h) := by
  obtain ⟨hm, M, hM⟩ := hh
  refine ⟨hm.const_smul r, |r| * M, fun z => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, abs_mul]
  gcongr
  exact hM z

/-- Adding a constant preserves bounded measurable functions. -/
private lemma angular_isBddMeas_add_const {W : ℕ} {h : IsoFlag W → ℝ} (hh : IsBddMeas h) (a : ℝ) :
    IsBddMeas (fun z => h z + a) := by
  obtain ⟨hm, M, hM⟩ := hh
  exact ⟨hm.add_const a, M + |a|, fun z => (abs_add_le _ _).trans (by gcongr; exact hM z)⟩

/-- Limit `ε → 0` in the proof of Lemma 8.11 [up:lem:angular]: an angular `L⁴` bound
`c (M + ε)` for every `ε > 0` gives the bound `c M`. -/
private lemma angular_L4Le_of_forall_pos {W : ℕ} {f : IsoFlag W → ℝ} {c M : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → AngL4Le f (c * (M + ε))) : AngL4Le f (c * M) := by
  intro x
  have hcont : Continuous fun ε : ℝ => ENNReal.ofReal (c * (M + ε)) ^ 4 :=
    (ENNReal.continuous_pow 4).comp (ENNReal.continuous_ofReal.comp (by fun_prop))
  have hlim : Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal (c * (M + ε)) ^ 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (c * M) ^ 4)) := by
    have := hcont.tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => h ε hε x)

/-- Positivity removal, normalization and the limit `ε → 0` in the proof of Lemma 8.11
[up:lem:angular]: if the pairing bound `ρ₀` holds for every bounded
measurable `h' ≥ ε > 0` with angular `L⁴` norm `1` in a class `S` closed under `h ↦ r (h + a)`,
then `P_{1/2}` maps nonnegative functions of `S` with angular `L⁴` norm at most `M` to angular
`L⁴` norm at most `ρ₀ M`. -/
private lemma angular_core {W : ℕ} {g E : ℝ} {q : ℕ} {ρ₀ : ℝ} (hρ0 : 0 ≤ ρ₀)
    (S : (IsoFlag W → ℝ) → Prop)
    (hS : ∀ (h : IsoFlag W → ℝ) (a r : ℝ), S h → S (r • fun z => h z + a))
    (hpair : ∀ h' : IsoFlag W → ℝ, IsBddMeas h' → ∀ ε : ℝ, 0 < ε → (∀ z, ε ≤ h' z) →
      AngL4Le h' 1 → S h' → ∀ (x : IsoFlag W) (ρ : IsoFlag W → ℝ), Measurable ρ →
      (∀ y, 0 ≤ ρ y) → ∫⁻ y, ENNReal.ofReal (ρ y) ∂(circleMeasure x) = 1 →
      ∫⁻ y, ENNReal.ofReal (ρ y ^ (3 / 4 : ℝ) * halfOp W g E q h' y) ∂(circleMeasure x) ≤
        ENNReal.ofReal ρ₀)
    {h : IsoFlag W → ℝ} (hh : IsBddMeas h) (hnn : 0 ≤ h) (hSh : S h) {M : ℝ} (hM : 0 ≤ M)
    (hL : AngL4Le h M) : AngL4Le (halfOp W g E q h) (ρ₀ * M) := by
  refine angular_L4Le_of_forall_pos fun ε hε => ?_
  have hnn' : ∀ z, 0 ≤ h z := fun z => hnn z
  have hMε : 0 < M + ε := by linarith
  set he : IsoFlag W → ℝ := fun z => h z + ε with hhe
  have hbe : IsBddMeas he := angular_isBddMeas_add_const hh ε
  have hLe : AngL4Le he (M + ε) := angular_L4Le_add_const hh.1 hnn hM hε.le hL
  set r : ℝ := (M + ε)⁻¹ with hr
  have hr0 : 0 < r := inv_pos.mpr hMε
  have hb' : IsBddMeas (r • he) := angular_isBddMeas_smul hbe r
  have hlow : ∀ z, r * ε ≤ (r • he) z := fun z => by
    rw [Pi.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (by simp only [hhe]; linarith [hnn' z]) hr0.le
  have hL1 : AngL4Le (r • he) 1 := by
    have := angular_L4Le_smul hr0.le hLe
    rwa [hr, inv_mul_cancel₀ hMε.ne'] at this
  have hdual : AngL4Le (halfOp W g E q (r • he)) ρ₀ :=
    angular_duality hρ0 hb' (fun z => (mul_pos hr0 hε).le.trans (hlow z))
      fun x ρ hρm hρ0' hρ1 =>
        hpair (r • he) hb' (r * ε) (mul_pos hr0 hε) hlow hL1 (hS h ε r hSh) x ρ hρm hρ0' hρ1
  rw [halfOp_smul] at hdual
  have hLP := angular_L4Le_smul hMε.le hdual
  rw [smul_smul, hr, mul_inv_cancel₀ hMε.ne', one_smul] at hLP
  refine angular_L4Le_of_abs_le (fun y => ?_) (angular_L4Le_mono (le_of_eq (mul_comm _ _)) hLP)
  have h0 : 0 ≤ halfOp W g E q h y := angular_halfOp_nonneg g E q hnn y
  have h1 : halfOp W g E q h y ≤ halfOp W g E q he y :=
    halfOp_mono g E q hh hbe (fun z => by simp only [hhe]; linarith) y
  rw [abs_of_nonneg h0, abs_of_nonneg (h0.trans h1)]
  exact h1

/-- (8.30) [up:eq:P-contraction] at one point with factor `ρ`, for every bounded measurable `h`
(no sign or invariance condition). -/
def AngContractionAllAt (W : ℕ) (g E : ℝ) (q : ℕ) (ρ : ℝ) : Prop :=
  ∀ h : IsoFlag W → ℝ, IsBddMeas h → ∀ M : ℝ, 0 ≤ M → AngL4Le h M →
    AngL4Le (halfOp W g E q h) (ρ * M)

/-- `0 < c ≤ ¼` for `c = angularConst C`, `C > 0`, as Lemma 8.10 [up:lem:operator-iteration]
requires. -/
theorem angularConst_pos_le {C : ℝ} (hC : 0 < C) :
    0 < angularConst C ∧ angularConst C ≤ 1 / 4 := by
  unfold angularConst
  have h1 : 0 < min 1 (1 / (9 * C)) := lt_min one_pos (by positivity)
  have h2 : min 1 (1 / (9 * C)) ≤ 1 := min_le_left _ _
  exact ⟨by positivity, by linarith⟩

theorem AngContractionAllAt.angContractionAt {W : ℕ} {g E : ℝ} {q : ℕ} {ρ : ℝ}
    (h : AngContractionAllAt W g E q ρ) : AngContractionAt W g E q ρ := by
  exact fun f hf _ _ M hM hL => h f hf M hM hL

/-- Lemma 8.11 [up:lem:angular] at one energy: if every incoming flag carries a cutoff and a
field with (8.34) [up:eq:angular-geometry] and (8.35) [up:eq:field], then (8.30)
[up:eq:P-contraction] holds with factor `1 - c/𝔟`, `c = angularConst C`. -/
theorem angContractionAt_of_field {W : ℕ} {g E : ℝ} {q : ℕ} {b C : ℝ} (hb : 1 ≤ b) (hC : 0 < C)
    (hfield : ∀ x : IsoFlag W, ∃ χ Y, AngularFieldAt W g E q b C x χ Y) :
    AngContractionAt W g E q (1 - angularConst C / b) := by
  have hc := angularConst_pos_le hC
  have hcb : angularConst C / b ≤ 1 / 4 := (div_le_self hc.1.le hb).trans hc.2
  have hρ0 : 0 ≤ 1 - angularConst C / b := by linarith
  intro f hf hnn hinv M hM hL
  refine angular_core hρ0 IsSimulInvariant ?_ ?_ hf hnn hinv hM hL
  · intro f' a r hinv' V hV x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hinv' V hV x]
  · intro f' hf' ε hε hlow hL1 hinv' x ρ hρm hρ0' hρ1
    exact lintegral_rpow_mul_halfOp_le hfield hb hC hf' hε hlow hinv' hL1 x hρm hρ0' hρ1

/-- Lemma 8.11 [up:lem:angular] with `K_out = 0`: (8.30) [up:eq:P-contraction] holds with factor
`1 - c/𝔟` for every bounded measurable `h`. -/
theorem angContractionAllAt_of_field_zero {W : ℕ} {g E : ℝ} {q : ℕ} {b C : ℝ} (hb : 1 ≤ b)
    (hC : 0 < C) (hfield : ∀ x : IsoFlag W, ∃ χ Y, AngularFieldZeroAt W g E q b C x χ Y) :
    AngContractionAllAt W g E q (1 - angularConst C / b) := by
  have hc := angularConst_pos_le hC
  have hcb : angularConst C / b ≤ 1 / 4 := (div_le_self hc.1.le hb).trans hc.2
  have hρ0 : 0 ≤ 1 - angularConst C / b := by linarith
  have key : ∀ f : IsoFlag W → ℝ, IsBddMeas f → 0 ≤ f → ∀ M : ℝ, 0 ≤ M → AngL4Le f M →
      AngL4Le (halfOp W g E q f) ((1 - angularConst C / b) * M) :=
    fun f hf hnn M hM hL =>
      angular_core hρ0 (fun _ => True) (fun _ _ _ _ => trivial)
        (fun f' hf' ε hε hlow hL1 _ x ρ hρm hρ0' hρ1 =>
          lintegral_rpow_mul_halfOp_le_of_zero hfield hb hC hf' hε hlow hL1 x hρm hρ0' hρ1)
        hf hnn trivial hM hL
  intro f hf M hM hL
  obtain ⟨hfm, B, hB⟩ := hf
  have hbabs : IsBddMeas fun y => |f y| :=
    ⟨continuous_abs.measurable.comp hfm, B, fun z => by rw [abs_abs]; exact hB z⟩
  have hLabs : AngL4Le (fun y => |f y|) M :=
    angular_L4Le_of_abs_le (fun y => (abs_abs _).le) hL
  have hres := key _ hbabs (fun y => abs_nonneg _) M hM hLabs
  exact angular_L4Le_of_abs_le (fun y => (abs_halfOp_le g E q ⟨hfm, B, hB⟩ y).trans
    (le_abs_self _)) hres

/-- From the local length `q` to `q m` (proof of Theorems 3.2 [thm:sharp-small-upper] and 3.3
[thm:compact-upper]): (8.30) [up:eq:P-contraction] with `0 ≤ ρ ≤ 1` at length `q` gives it at
length `q m`, `m ≥ 1`, since the operator of `q m` blocks is `P_{1/2}^m` and `P_{1/2}`
preserves (8.25) [up:eq:invariant-function]. -/
theorem angContractionAt_mul {W : ℕ} {g E : ℝ} {q : ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (h : AngContractionAt W g E q ρ) {m : ℕ} (hm : 1 ≤ m) :
    AngContractionAt W g E (q * m) ρ := by
  intro f hf hnn hinv M hM hL
  rw [halfOp_mul_eq_iterate g E q m hf]
  have key : ∀ k : ℕ, IsBddMeas ((halfOp W g E q)^[k] f) ∧ 0 ≤ (halfOp W g E q)^[k] f ∧
      IsSimulInvariant ((halfOp W g E q)^[k] f) ∧
      AngL4Le ((halfOp W g E q)^[k] f) (ρ ^ k * M) := by
    intro k
    induction k with
    | zero => exact ⟨hf, hnn, hinv, by simpa using hL⟩
    | succ k ih =>
      obtain ⟨hb, hn, hi, hl⟩ := ih
      rw [Function.iterate_succ_apply']
      refine ⟨halfOp_isBddMeas g E q hb, angular_halfOp_nonneg g E q hn,
        halfOp_isSimulInvariant g E q hi, ?_⟩
      have := h _ hb hn hi (ρ ^ k * M) (mul_nonneg (pow_nonneg hρ0 k) hM) hl
      rwa [← mul_assoc, ← pow_succ'] at this
  exact angular_L4Le_mono (mul_le_mul_of_nonneg_right
    (pow_le_of_le_one hρ0 hρ1 (by omega)) hM) (key m).2.2.2

end LSBA
