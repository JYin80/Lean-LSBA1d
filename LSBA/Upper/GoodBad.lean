import LSBA.Upper.GoodOperator
import LSBA.Upper.BatchBadMass
import LSBA.Upper.OperatorIteration

/-!
# Lemma 8.9 [up:lem:good-bad]: the good and bad components

Lemma 8.9 [up:lem:good-bad] in operator form, with the batch cutoff `χ_q` of Appendix G.5
[sec:c-component-proof] in place of the density decomposition (8.26) [cc:eq:decomp]:
`B_{1/2} h = 𝔼[(1 - χ_q) e^{-c/2} h(TU, TY)]` and `G_{1/2} = P_{1/2} - B_{1/2}` ((8.28)
[eq:c-good-bad-operators]). `B_{1/2}` is linear on bounded measurable functions with
`‖B_{1/2} h‖_∞ ≤ ½ ‖h‖_∞` by the bad mass of (8.27) [up:eq:coarse-density] and (F.2)
[cc:eq:boundc] ((F.7) [eq:c-bad-operator]); `G_{1/2}` satisfies (8.29) [up:eq:GB-bounds] by the
lift form of Lemma F.3 [lem:c-operators], with the cutoff of Lemma G.4 [lem:c-gaussian] on the
first `1000` inputs and the lift of `√2 K_U` of Lemma 10.1 [lem:c-gaussian-lift]; all constants
are powers of `W` for `W^{-B} ≤ g ≤ W^B`, `|E| ≤ E₀` and fixed `q`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Helpers -/

/-- On a batch in `𝒢`, `e^{-c/2} ≤ ‖T‖^{1/2}` ((F.2) [cc:eq:boundc]). -/
private theorem gb_exp_le {W : ℕ} (hW : 1 ≤ W)
    {T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hT : T ∈ isoGroup W) (x : IsoFlag W) :
    Real.exp (-volCocycle T x / 2) ≤ Real.sqrt ‖T‖ := by
  have hne : T ≠ 0 := by
    rintro rfl
    have h := hT.2
    have : Nonempty (Fin 2 × Fin W) := ⟨(0, ⟨0, hW⟩)⟩
    rw [Matrix.det_zero] at h
    exact zero_ne_one h
  have hpos : 0 < ‖T‖ := norm_pos_iff.2 hne
  have hc := abs_volCocycle_le hT.1 x
  have h1 : -volCocycle T x / 2 ≤ Real.log ‖T‖ / 2 := by
    have := neg_abs_le (volCocycle T x)
    linarith
  calc Real.exp (-volCocycle T x / 2) ≤ Real.exp (Real.log ‖T‖ / 2) := Real.exp_le_exp.2 h1
    _ = Real.sqrt ‖T‖ := by rw [Real.exp_half, Real.exp_log hpos]

/-- The integrand of `B_{1/2}` is jointly measurable in the sample and the flag. -/
private theorem gb_measurable_integrand {W n : ℕ} (g E : ℝ) {χ : Ω W 1000 → ℝ}
    (hχm : Measurable (batchCut W n χ)) {h : IsoFlag W → ℝ} (hh : Measurable h) :
    Measurable fun p : Ω W (1000 + n) × IsoFlag W =>
      (1 - batchCut W n χ p.1) *
        (Real.exp (-volCocycle (batchMat W g E (1000 + n) p.1) p.2 / 2) *
          h (flagAct (batchMat W g E (1000 + n) p.1) p.2)) := by
  have hB : Measurable fun p : Ω W (1000 + n) × IsoFlag W =>
      (batchMat W g E (1000 + n) p.1, p.2) :=
    ((measurable_batchMat W g E (1000 + n)).comp measurable_fst).prodMk measurable_snd
  have h1 := (measurable_volCocycle W).comp hB
  have h2 := (measurable_flagAct W).comp hB
  exact (measurable_const.sub (hχm.comp measurable_fst)).mul
    ((Real.measurable_exp.comp (h1.neg.div_const 2)).mul (hh.comp h2))

/-- The integrand of `B_{1/2}` is dominated by `M (1 - χ_q) ‖T‖^{1/2}` when `|h| ≤ M`
((F.2) [cc:eq:boundc]). -/
private theorem gb_integrand_le {W n : ℕ} (hW : 1 ≤ W) (g E : ℝ) {χ : Ω W 1000 → ℝ}
    (hq01 : ∀ ω, 0 ≤ batchCut W n χ ω ∧ batchCut W n χ ω ≤ 1) {h : IsoFlag W → ℝ} {M : ℝ}
    (hM : ∀ y, |h y| ≤ M) (ω : Ω W (1000 + n)) (x : IsoFlag W) :
    ‖(1 - batchCut W n χ ω) * (Real.exp (-volCocycle (batchMat W g E (1000 + n) ω) x / 2) *
        h (flagAct (batchMat W g E (1000 + n) ω) x))‖ ≤
      M * ((1 - batchCut W n χ ω) * Real.sqrt ‖batchMat W g E (1000 + n) ω‖) := by
  have h0 : 0 ≤ 1 - batchCut W n χ ω := by linarith [(hq01 ω).2]
  have he := gb_exp_le hW (batchMat_mem_isoGroup W g E (1000 + n) ω) x
  have hy := hM (flagAct (batchMat W g E (1000 + n) ω) x)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg (Real.exp_pos _).le]
  calc (1 - batchCut W n χ ω) * (Real.exp (-volCocycle (batchMat W g E (1000 + n) ω) x / 2) *
        |h (flagAct (batchMat W g E (1000 + n) ω) x)|)
      ≤ (1 - batchCut W n χ ω) * (Real.sqrt ‖batchMat W g E (1000 + n) ω‖ * M) :=
        mul_le_mul_of_nonneg_left (mul_le_mul he hy (abs_nonneg _) (Real.sqrt_nonneg _)) h0
    _ = _ := by ring

/-- Monotonicity of (8.29) [up:eq:GB-bounds] in the constant of the good part. -/
private theorem gb_mono {W : ℕ} {g E : ℝ} {q : ℕ} {K K' : ℝ} (hs : GoodBadSplitAt W g E q K)
    (hKK : K ≤ K') : GoodBadSplitAt W g E q K' := by
  obtain ⟨Bop, h1, h2, h3, h4, h5⟩ := hs
  exact ⟨Bop, h1, h2, h3, h4, fun h M hh hM h4' x =>
    (h5 h M hh hM h4' x).trans (mul_le_mul_of_nonneg_right hKK hM)⟩

/-- For `w ≥ 1`, `W^{-B} ≤ g`, `|E| ≤ E₀` and `1 + E₀ + K₁ + √3 ≤ w`, the support bound of
(8.27) [up:eq:coarse-density] is at most `w^{(B + 3/2) N}`. -/
private theorem gb_K_le {w B E₀ K₁ g E : ℝ} (N : ℕ) (hw : 1 ≤ w) (hB : 0 < B) (hE₀ : 0 < E₀)
    (hK₁ : 0 < K₁) (ha : 1 + E₀ + K₁ + Real.sqrt 3 ≤ w) (hgl : w ^ (-B) ≤ g) (hE : |E| ≤ E₀) :
    (max 1 g⁻¹ * (1 + |E| + max K₁ (Real.sqrt (3 * w)))) ^ N ≤ w ^ ((B + 3 / 2) * N) := by
  have hw0 : 0 < w := by linarith
  have hh : max 1 g⁻¹ ≤ w ^ B := by
    refine max_le (Real.one_le_rpow hw hB.le) ?_
    calc g⁻¹ ≤ (w ^ (-B))⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hw0 _) hgl
      _ = w ^ B := by rw [Real.rpow_neg hw0.le, inv_inv]
  have hs1 : 1 ≤ Real.sqrt w := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hw
  have h3w : Real.sqrt (3 * w) = Real.sqrt 3 * Real.sqrt w := Real.sqrt_mul (by norm_num) w
  have hs3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hmax : max K₁ (Real.sqrt (3 * w)) ≤ K₁ * Real.sqrt w + Real.sqrt 3 * Real.sqrt w := by
    rw [h3w]
    refine max_le ?_ ?_
    · nlinarith
    · nlinarith [Real.sqrt_nonneg w]
  have hE' : |E| ≤ E₀ * Real.sqrt w := hE.trans (by nlinarith)
  have hsum : 1 + |E| + max K₁ (Real.sqrt (3 * w)) ≤ w ^ ((3 : ℝ) / 2) := by
    have e : w ^ ((3 : ℝ) / 2) = w * Real.sqrt w := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hw0.le (by norm_num)]
      norm_num
    rw [e]
    calc 1 + |E| + max K₁ (Real.sqrt (3 * w))
        ≤ (1 + E₀ + K₁ + Real.sqrt 3) * Real.sqrt w := by nlinarith
      _ ≤ w * Real.sqrt w := mul_le_mul_of_nonneg_right ha (Real.sqrt_nonneg _)
  have hprod : max 1 g⁻¹ * (1 + |E| + max K₁ (Real.sqrt (3 * w))) ≤ w ^ (B + 3 / 2) := by
    rw [Real.rpow_add hw0]
    exact mul_le_mul hh hsum (by positivity) (Real.rpow_nonneg hw0.le _)
  have hnn : 0 ≤ max 1 g⁻¹ * (1 + |E| + max K₁ (Real.sqrt (3 * w))) :=
    mul_nonneg (zero_le_one.trans (le_max_left _ _))
      (by have := le_max_left K₁ (Real.sqrt (3 * w)); positivity)
  rw [Real.rpow_mul_natCast hw0.le]
  exact pow_le_pow_left₀ hnn hprod N

/-- For `w ≥ 1`, `W^{-B} ≤ g ≤ W^B` and `C_L ≤ w`, the lift bound `C_L w max{g⁻², g⁴}` of
Lemma 10.1 [lem:c-gaussian-lift] is at most `w^{2 + 4B}`. -/
private theorem gb_b_le {w B CL g : ℝ} (hw : 1 ≤ w) (hB : 0 < B) (hCLw : CL ≤ w)
    (hgl : w ^ (-B) ≤ g) (hgu : g ≤ w ^ B) :
    CL * (w * max (g⁻¹ ^ 2) (g ^ 4)) ≤ w ^ (2 + 4 * B) := by
  have hw0 : 0 < w := by linarith
  have hg : 0 < g := lt_of_lt_of_le (Real.rpow_pos_of_pos hw0 _) hgl
  have hu1 : 1 ≤ w ^ B := Real.one_le_rpow hw hB.le
  have hgi : g⁻¹ ≤ w ^ B :=
    calc g⁻¹ ≤ (w ^ (-B))⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hw0 _) hgl
      _ = w ^ B := by rw [Real.rpow_neg hw0.le, inv_inv]
  have hm : max (g⁻¹ ^ 2) (g ^ 4) ≤ (w ^ B) ^ 4 := by
    refine max_le ?_ (pow_le_pow_left₀ hg.le hgu 4)
    calc g⁻¹ ^ 2 ≤ (w ^ B) ^ 2 := pow_le_pow_left₀ (inv_nonneg.2 hg.le) hgi 2
      _ ≤ (w ^ B) ^ 4 := pow_le_pow_right₀ hu1 (by norm_num)
  have e : w ^ (2 + 4 * B) = w * (w * (w ^ B) ^ 4) := by
    rw [Real.rpow_add hw0, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      show 4 * B = B * ((4 : ℕ) : ℝ) by push_cast; ring, Real.rpow_mul_natCast hw0.le]
    ring
  rw [e]
  have hm0 : 0 ≤ max (g⁻¹ ^ 2) (g ^ 4) := (sq_nonneg _).trans (le_max_left _ _)
  calc CL * (w * max (g⁻¹ ^ 2) (g ^ 4)) ≤ w * (w * max (g⁻¹ ^ 2) (g ^ 4)) :=
        mul_le_mul_of_nonneg_right hCLw (by positivity)
    _ ≤ w * (w * (w ^ B) ^ 4) := by gcongr

/-- For `w ≥ 2`, `0 ≤ K ≤ w^D` and `b ≤ w^{2 + 4B}`, the constant of
(8.29) [up:eq:GB-bounds] is at most `w^{(5/2) D + 2B + 5}`. -/
private theorem gb_const_le {w B D K b : ℝ} (hw : 2 ≤ w) (hB : 0 < B) (hD : 0 ≤ D)
    (hK0 : 0 ≤ K) (hK : K ≤ w ^ D) (hb : b ≤ w ^ (2 + 4 * B)) :
    4 / 3 * Real.sqrt K * (1 + 2 * π * (K ^ 2 * (Real.sqrt b + 2) / 2)) ≤
      w ^ (5 / 2 * D + 2 * B + 5) := by
  have hw0 : 0 < w := by linarith
  have hw1 : 1 ≤ w := by linarith
  have hX : Real.sqrt K ≤ w ^ (D / 2) := by
    calc Real.sqrt K ≤ Real.sqrt (w ^ D) := Real.sqrt_le_sqrt hK
      _ = w ^ (D / 2) := by rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hw0.le]; ring_nf
  have hY : K ^ 2 ≤ w ^ (2 * D) := by
    calc K ^ 2 ≤ (w ^ D) ^ 2 := pow_le_pow_left₀ hK0 hK 2
      _ = w ^ (2 * D) := by
        rw [← Real.rpow_mul_natCast hw0.le]; push_cast; ring_nf
  have hZ : Real.sqrt b ≤ w ^ (1 + 2 * B) := by
    calc Real.sqrt b ≤ Real.sqrt (w ^ (2 + 4 * B)) := Real.sqrt_le_sqrt hb
      _ = w ^ (1 + 2 * B) := by rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hw0.le]; ring_nf
  have hX0 : 0 ≤ w ^ (D / 2) := Real.rpow_nonneg hw0.le _
  have hY1 : 1 ≤ w ^ (2 * D) := Real.one_le_rpow hw1 (by linarith)
  have hZ1 : 1 ≤ w ^ (1 + 2 * B) := Real.one_le_rpow hw1 (by linarith)
  have h16 : (16 : ℝ) ≤ w ^ (4 : ℝ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ w ^ 4 := pow_le_pow_left₀ (by norm_num) hw 4
  have hsplit : w ^ (5 / 2 * D + 2 * B + 5) =
      w ^ (4 : ℝ) * (w ^ (D / 2) * (w ^ (2 * D) * w ^ (1 + 2 * B))) := by
    rw [← Real.rpow_add hw0, ← Real.rpow_add hw0, ← Real.rpow_add hw0]
    ring_nf
  rw [hsplit]
  set X := w ^ (D / 2)
  set Y := w ^ (2 * D)
  set Z := w ^ (1 + 2 * B)
  have hYZ : 1 ≤ Y * Z := one_le_mul_of_one_le_of_one_le hY1 hZ1
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hb2 : Real.sqrt b + 2 ≤ 3 * Z := by linarith
  have h1 : 1 + 2 * π * (K ^ 2 * (Real.sqrt b + 2) / 2) ≤ 1 + 2 * π * (Y * (3 * Z) / 2) := by
    gcongr
  have h2 : 1 + 2 * π * (Y * (3 * Z) / 2) ≤ 12 * (Y * Z) := by
    have := mul_le_mul_of_nonneg_right hpi.le (show 0 ≤ Y * Z by linarith)
    nlinarith
  calc 4 / 3 * Real.sqrt K * (1 + 2 * π * (K ^ 2 * (Real.sqrt b + 2) / 2))
      ≤ 4 / 3 * X * (12 * (Y * Z)) := by
        gcongr
        exact h1.trans h2
    _ = 16 * (X * (Y * Z)) := by ring
    _ ≤ w ^ (4 : ℝ) * (X * (Y * Z)) := mul_le_mul_of_nonneg_right h16 (by positivity)

/-- The bad operator `B_{1/2} h = 𝔼[(1 - χ_q) e^{-c/2} h(TU, TY)]` of (8.28)
[eq:c-good-bad-operators] for a batch of `1000 + n` inputs with the batch cutoff `χ_q`. -/
def badOp (W n : ℕ) (g E : ℝ) (χ : Ω W 1000 → ℝ) (h : IsoFlag W → ℝ) (x : IsoFlag W) : ℝ :=
  ∫ ω, (1 - batchCut W n χ ω) * (Real.exp (-volCocycle (batchMat W g E (1000 + n) ω) x / 2) *
    h (flagAct (batchMat W g E (1000 + n) ω) x)) ∂(μ W (1000 + n))

/-- (8.28) [eq:c-good-bad-operators] and (8.29) [up:eq:GB-bounds] at one point, from a cutoff
of the first `1000` inputs with bad mass at most `½`, the support bound `‖T‖ ≤ K` and a cut lift
of `√2 K_U` at every flag with `𝔼 |δ_G(χ X)|² ≤ b`: `P_{1/2} = G_{1/2} + B_{1/2}` with
`B_{1/2} = badOp` and `‖G_{1/2} h‖_∞ ≤ (4/3) K^{1/2} (1 + π K² (b^{1/2} + 2)) M`. -/
theorem goodBadSplitAt_of_cutoff {W n : ℕ} (hW : 1 ≤ W) {g E K b : ℝ} {χ : Ω W 1000 → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) (hχ01 : ∀ ω, 0 ≤ χ ω ∧ χ ω ≤ 1)
    (hbad : ∫⁻ ω, ENNReal.ofReal ((1 - batchCut W n χ ω) *
        Real.sqrt ‖batchMat W g E (1000 + n) ω‖) ∂(μ W (1000 + n)) ≤ ENNReal.ofReal (1 / 2))
    (hK : ∀ ω ∈ tsupport (batchCut W n χ), ‖batchMat W g E (1000 + n) ω‖ ≤ K)
    (hlift : ∀ x : IsoFlag W, ∃ Y : Ω W 1000 → Ω W 1000,
      IsCutLift W 1000 (batchMat W g E 1000) (((Real.sqrt 2 : ℝ) : ℂ) • circleGen x.1.1) b χ Y) :
    GoodBadSplitAt W g E (1000 + n)
      (4 / 3 * Real.sqrt K * (1 + 2 * π * (K ^ 2 * (Real.sqrt b + 2) / 2))) := by
  have hqs := batchCut_spec (n := n) hχ hχc hχ01
  have hqm : Measurable (batchCut W n χ) := hqs.1.continuous.measurable
  have hf0 : ∀ ω, 0 ≤ (1 - batchCut W n χ ω) * Real.sqrt ‖batchMat W g E (1000 + n) ω‖ :=
    fun ω => mul_nonneg (by linarith [(hqs.2.2 ω).2]) (Real.sqrt_nonneg _)
  have hfm : Measurable fun ω =>
      (1 - batchCut W n χ ω) * Real.sqrt ‖batchMat W g E (1000 + n) ω‖ :=
    (measurable_const.sub hqm).mul
      (Real.continuous_sqrt.measurable.comp (measurable_batchMat W g E (1000 + n)).norm)
  have hfi : Integrable (fun ω =>
      (1 - batchCut W n χ ω) * Real.sqrt ‖batchMat W g E (1000 + n) ω‖) (μ W (1000 + n)) :=
    ⟨hfm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hf0)).2
      (hbad.trans_lt ENNReal.ofReal_lt_top)⟩
  have hf2 : ∫ ω, (1 - batchCut W n χ ω) * Real.sqrt ‖batchMat W g E (1000 + n) ω‖
      ∂(μ W (1000 + n)) ≤ 1 / 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hfm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) hbad
  have hint : ∀ (h : IsoFlag W → ℝ) (M : ℝ), Measurable h → (∀ y, |h y| ≤ M) → ∀ x,
      Integrable (fun ω => (1 - batchCut W n χ ω) *
        (Real.exp (-volCocycle (batchMat W g E (1000 + n) ω) x / 2) *
          h (flagAct (batchMat W g E (1000 + n) ω) x))) (μ W (1000 + n)) :=
    fun h M hm hM x => Integrable.mono' (hfi.const_mul M)
      ((gb_measurable_integrand g E hqm hm).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (ae_of_all _ fun ω => gb_integrand_le hW g E hqs.2.2 hM ω x)
  have hB4 : ∀ (h : IsoFlag W → ℝ) (M : ℝ), (∀ y, |h y| ≤ M) → ∀ x,
      |badOp W n g E χ h x| ≤ M / 2 := by
    intro h M hM x
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x)
    rw [← Real.norm_eq_abs]
    calc ‖badOp W n g E χ h x‖
        ≤ ∫ ω, M * ((1 - batchCut W n χ ω) * Real.sqrt ‖batchMat W g E (1000 + n) ω‖)
          ∂(μ W (1000 + n)) :=
          norm_integral_le_of_norm_le (hfi.const_mul M)
            (ae_of_all _ fun ω => gb_integrand_le hW g E hqs.2.2 hM ω x)
      _ = M * ∫ ω, (1 - batchCut W n χ ω) * Real.sqrt ‖batchMat W g E (1000 + n) ω‖
          ∂(μ W (1000 + n)) := integral_const_mul _ _
      _ ≤ M * (1 / 2) := mul_le_mul_of_nonneg_left hf2 hM0
      _ = M / 2 := by ring
  refine ⟨badOp W n g E χ, ?_, ?_, ?_, ?_, ?_⟩
  · rintro h ⟨hm, M, hM⟩
    refine ⟨?_, M / 2, hB4 h M hM⟩
    exact ((gb_measurable_integrand g E hqm hm).stronglyMeasurable.integral_prod_left'
      (μ := μ W (1000 + n))).measurable
  · rintro h h' ⟨hm, M, hM⟩ ⟨hm', M', hM'⟩
    funext x
    simp only [badOp, Pi.add_apply]
    rw [← integral_add (hint h M hm hM x) (hint h' M' hm' hM' x)]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only
    ring
  · intro r h _
    funext x
    simp only [badOp, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only
    ring
  · intro h M _ hM x
    exact hB4 h M hM x
  · rintro h M ⟨hm, M', hM'⟩ hM0 h4 x
    obtain ⟨Y, hY⟩ := hlift x
    have hsub : halfOp W g E (1000 + n) h x - badOp W n g E χ h x =
        ∫ ω, batchCut W n χ ω * (Real.exp (-volCocycle (batchMat W g E (1000 + n) ω) x / 2) *
          h (flagAct (batchMat W g E (1000 + n) ω) x)) ∂(μ W (1000 + n)) := by
      unfold halfOp badOp
      rw [← integral_sub (integrable_halfOp g E (1000 + n) ⟨hm, M', hM'⟩ x)
        (hint h M' hm hM' x)]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      simp only
      ring
    rw [hsub]
    exact abs_integral_goodPart_le hW hχ hχc hχ01 hY hK ⟨hm, M', hM'⟩ hM0 h4

/-- Lemma 8.9 [up:lem:good-bad] in operator form: the interface `GoodBadSplit` holds. -/
theorem good_bad_split : GoodBadSplit := by
  intro B E₀ hB hE₀ q hq _
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = 1000 + n := ⟨q - 1000, by omega⟩
  obtain ⟨c₁, ρ, K₁, L, hc₁, -, hK₁, hL, hcut⟩ := coercivity_cutoff
  obtain ⟨c, C', hc, hC', W₁, hW₁⟩ := hcut 1000
  obtain ⟨CL, -, hlift⟩ := gaussian_lift_general_batch E₀ c₁ ρ K₁ L hE₀ hc₁ hK₁ hL
  obtain ⟨W₂, hbad⟩ := lintegral_badMass_le B E₀ c C' hB hE₀ hc hC' n
  have hlay : batchLayout * batchLayoutᵀ = 1 :=
    pairLayout_mul_transpose
      (fun a b h => by simp [Fin.ext_iff, liftPairI, Fin.val_rev] at h; omega)
      (fun a b h => by simp [Fin.ext_iff, liftPairK, Fin.val_rev] at h; omega)
      (fun a b h => by simp [Fin.ext_iff, liftPairI, liftPairK, Fin.val_rev] at h; omega)
  refine ⟨5 / 2 * ((B + 3 / 2) * ((1000 + n : ℕ) : ℝ)) + 2 * B + 5,
    max (max W₁ W₂) (max 2 (max ⌈1 + E₀ + K₁ + Real.sqrt 3⌉₊ ⌈CL⌉₊)), ?_⟩
  intro W hW g E hgl hgu hE
  have hW1 : 1 ≤ W := by omega
  have hw2 : (2 : ℝ) ≤ W := by exact_mod_cast (show 2 ≤ W by omega)
  have hw1 : (1 : ℝ) ≤ W := by linarith
  have hw0 : (0 : ℝ) < W := by linarith
  have hWa : 1 + E₀ + K₁ + Real.sqrt 3 ≤ (W : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈1 + E₀ + K₁ + Real.sqrt 3⌉₊ ≤ W by omega))
  have hWC : CL ≤ (W : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈CL⌉₊ ≤ W by omega))
  have hg : 0 < g := lt_of_lt_of_le (Real.rpow_pos_of_pos hw0 _) hgl
  obtain ⟨χ, hχ⟩ := hW₁ batchLayout hlay W (by omega)
  have hb := hbad W (by omega) χ hχ.1.continuous.measurable hχ.2.2.1 hχ.2.2.2.1 g E hgl hgu hE
  have hK : ∀ ω ∈ tsupport (batchCut W n χ), ‖batchMat W g E (1000 + n) ω‖ ≤
      (max 1 g⁻¹ * (1 + |E| + max K₁ (Real.sqrt (3 * W)))) ^ (1000 + n) :=
    fun ω hω => norm_batchMat_le_of_mem_tsupport hg
      (fun ω' hω' i => (hχ.2.2.2.2.2 ω' hω' ω' (by simp; positivity)).2 i) hω
  have hY : ∀ x : IsoFlag W, ∃ Y, IsCutLift W 1000 (batchMat W g E 1000)
      (((Real.sqrt 2 : ℝ) : ℂ) • circleGen x.1.1) (CL * (W * max (g⁻¹ ^ 2) (g ^ 4))) χ Y :=
    fun x => hlift W c C' χ hχ g E hg hE _ (circleGen_mem_lieJ hW1 x.2.1).1
      (circleGen_mem_lieJ hW1 x.2.1).2.1
  have hK0 : 0 ≤ (max 1 g⁻¹ * (1 + |E| + max K₁ (Real.sqrt (3 * W)))) ^ (1000 + n) :=
    pow_nonneg (mul_nonneg (zero_le_one.trans (le_max_left _ _))
      (by have := le_max_left K₁ (Real.sqrt (3 * (W : ℝ))); positivity)) _
  exact gb_mono (goodBadSplitAt_of_cutoff hW1 hχ.1 hχ.2.1 hχ.2.2.1 hb hK hY)
    (gb_const_le hw2 hB (by positivity) hK0
      (gb_K_le (1000 + n) hw1 hB hE₀ hK₁ hWa hgl hE) (gb_b_le hw1 hB hWC hgl hgu))

end LSBA
