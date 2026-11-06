import LSBA.Transfer.Coarse
import LSBA.Volume.Poisson
import LSBA.Main.CountMono

/-!
# Seed tails

The tail bounds (7.7) [uv:eq:seed-exponential-tail] for `X_a(E) = ‖G_aa(E + iη)‖` at the seed
height, and the deterministic step of the proof of Lemma 2.4 [uv:lem:short-spreading]: eigenvectors
with `ℓ < r` carry heavy-block mass, which (4.3) [uv:eq:matrix-poisson] bounds by Poisson integrals
of `‖G_aa‖` (proof of Lemma 2.4 [uv:lem:short-spreading], Section 7.2 [sec:uniform-resolvent-seed]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Window and arc facts -/

private lemma seed_val_finRotate {L : ℕ} (x : Fin L) :
    (finRotate L x).val = (x.val + 1) % L := by
  cases L with
  | zero => exact x.elim0
  | succ n =>
    rw [coe_finRotate]
    by_cases h : x = Fin.last n
    · subst h
      simp
    · simp only [h, ↓reduceIte]
      have : x.val < n := by
        have h1 := x.isLt
        have h2 : x.val ≠ n := fun h' => h (Fin.ext (by simpa using h'))
        omega
      rw [Nat.mod_eq_of_lt (by omega)]

private lemma seed_pow_val {L : ℕ} (a : Fin L) (j : ℕ) :
    ((finRotate L ^ j) a).val = (a.val + j) % L := by
  induction j with
  | zero => simp [Nat.mod_eq_of_lt a.isLt]
  | succ j ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, seed_val_finRotate, ih, Nat.mod_add_mod]
    rfl

/-- A forward arc from `a` does not return to `a` before `L` steps. -/
private lemma seed_arcDir_self {L : ℕ} (a : Fin L) {n : ℕ} (hn : n ≤ L) :
    arcDir a a n = true := by
  simp only [arcDir, decide_eq_true_eq, Finset.mem_Ico, and_imp]
  intro i hi1 hin h
  have h1 : ((finRotate L ^ i) a).val = a.val := congrArg Fin.val h
  rw [seed_pow_val] at h1
  have h2 := a.isLt
  by_cases h3 : a.val + i < L
  · rw [Nat.mod_eq_of_lt h3] at h1
    omega
  · rw [Nat.mod_eq_sub_mod (not_lt.mp h3), Nat.mod_eq_of_lt (by omega)] at h1
    omega

private lemma seed_one_le_g {κ g : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) (hg : 2 / Real.sqrt κ ≤ g) :
    1 ≤ g := by
  have h1 : Real.sqrt κ ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have h2 : 1 ≤ 2 / Real.sqrt κ := (one_le_div (Real.sqrt_pos.mpr hκ)).mpr h1
  exact h2.trans hg

/-- The window `n = coarseN g L` of (7.4) [uvs:eq:window-length] satisfies `1 ≤ n`, `2n + 1 ≤ L`,
`n ≤ g²` for `L ≥ 3`, `g ≥ 2 κ^{-1/2}` and `κ ≤ 2`. -/
private lemma seed_window {κ g : ℝ} {L : ℕ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) (hL : 3 ≤ L)
    (hg : 2 / Real.sqrt κ ≤ g) :
    1 ≤ g ∧ 1 ≤ coarseN g L ∧ 2 * coarseN g L + 1 ≤ L ∧ (coarseN g L : ℝ) ≤ g ^ 2 := by
  have hg1 : 1 ≤ g := seed_one_le_g hκ hκ2 hg
  have hg2 : (1 : ℝ) ≤ g ^ 2 := one_le_pow₀ hg1
  have hn1 : 1 ≤ coarseN g L := le_min (by omega) (Nat.le_floor (by simpa using hg2))
  have hn2 : 2 * coarseN g L + 1 ≤ L := by
    have : coarseN g L ≤ (L - 1) / 2 := min_le_left _ _
    omega
  have hng : (coarseN g L : ℝ) ≤ g ^ 2 :=
    le_trans (Nat.cast_le.mpr (min_le_right _ _)) (Nat.floor_le (sq_nonneg g))
  exact ⟨hg1, hn1, hn2, hng⟩

/-! ### Continuity of resolvents -/

/-- The resolvent of a continuous family of Hermitian matrices at a continuously varying point off
the real axis is continuous. -/
private lemma seed_continuous_resolvent {T : Type*} [TopologicalSpace T] {m : Type*} [Fintype m]
    [DecidableEq m] (M : T → Matrix m m ℂ) (z : T → ℂ) (hM : Continuous M) (hz : Continuous z)
    (hH : ∀ t, (M t).IsHermitian) (hzi : ∀ t, (z t).im ≠ 0) :
    Continuous fun t => resolventMat (M t) (z t) := by
  have hc : Continuous fun t => M t - z t • (1 : Matrix m m ℂ) :=
    hM.sub (hz.smul continuous_const)
  refine continuous_iff_continuousAt.2 fun t => ?_
  have hu := isUnit_sub_smul_one (hH t) (hzi t)
  have hdet : (M t - z t • (1 : Matrix m m ℂ)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  refine (continuousAt_matrix_inv _ ?_).comp hc.continuousAt
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ hdet

private lemma seed_continuous_Hmat (g : ℝ) (W L : ℕ) : Continuous (Hmat g W L) := by
  refine continuous_matrix fun p q => ?_
  simp only [Hmat, Hdet, gueBlock, blockDiagOp, Matrix.smul_apply, Matrix.add_apply,
    Matrix.of_apply, smul_eq_mul]
  split_ifs <;> fun_prop

private lemma seed_continuous_norm_block {T : Type*} [TopologicalSpace T] {W L : ℕ}
    (G : T → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (hG : Continuous G) (a b : Fin L) :
    Continuous fun t => ‖blockOf (G t) a b‖ := by
  refine continuous_norm.comp (continuous_matrix fun α β => ?_)
  exact (hG.matrix_elem (a, α) (b, β))

/-! ### The truncated mean from a tail bound -/

/-- Layer-cake step of (7.7) [uv:eq:seed-exponential-tail], second line: if
`P{X > v} ≤ (B/v)^s` for all `v > 0`, with `s ≥ 2`, then `E[X 1{X > A}] ≤ 2 A (B/A)^s`. -/
private lemma seed_truncated_le {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    (X : Ω' → ℝ) (hXm : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω) {B s A : ℝ} (hB : 0 < B)
    (hs : 2 ≤ s) (hA : 0 < A)
    (htail : ∀ v : ℝ, 0 < v → P {ω | v < X ω} ≤ ENNReal.ofReal ((B / v) ^ s)) :
    Integrable (fun ω => Set.indicator {x : ℝ | A < x} (fun x => x) (X ω)) P ∧
      ∫ ω, Set.indicator {x : ℝ | A < x} (fun x => x) (X ω) ∂P ≤ 2 * A * (B / A) ^ s := by
  set f : Ω' → ℝ := fun ω => Set.indicator {x : ℝ | A < x} (fun x => x) (X ω) with hf
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω =>
    Set.indicator_nonneg (fun x hx => (hA.trans hx).le) _
  have hfm : Measurable f :=
    (measurable_id.indicator (measurableSet_lt measurable_const measurable_id)).comp hXm
  have hsub1 : ∀ t : ℝ, 0 ≤ t → {ω | t < f ω} ⊆ {ω | A < X ω} := by
    intro t ht ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    by_contra hcon
    have : f ω = 0 := by
      simp only [hf]
      exact Set.indicator_of_notMem (by simpa using hcon) _
    linarith
  have hsub2 : ∀ t : ℝ, {ω | t < f ω} ⊆ {ω | t < X ω} := by
    intro t ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have : f ω ≤ X ω := by
      by_cases h : A < X ω
      · simp only [hf]
        rw [Set.indicator_of_mem (show X ω ∈ {x : ℝ | A < x} from h)]
      · simp only [hf]
        rw [Set.indicator_of_notMem (show X ω ∉ {x : ℝ | A < x} from h)]
        exact hX0 ω
    linarith
  have hs1 : 1 < s := by linarith
  have hQ0 : 0 ≤ (B / A) ^ s := Real.rpow_nonneg (by positivity) _
  suffices hmain : ∫⁻ ω, ENNReal.ofReal (f ω) ∂P ≤ ENNReal.ofReal (2 * A * (B / A) ^ s) by
    refine ⟨⟨hfm.aestronglyMeasurable, ?_⟩, ?_⟩
    · have : ∫⁻ ω, ‖f ω‖ₑ ∂P = ∫⁻ ω, ENNReal.ofReal (f ω) ∂P :=
        lintegral_congr fun ω => Real.enorm_of_nonneg (hf0 ω)
      change ∫⁻ ω, ‖f ω‖ₑ ∂P < ⊤
      rw [this]
      exact lt_of_le_of_lt hmain ENNReal.ofReal_lt_top
    · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hfm.aestronglyMeasurable]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) hmain
  rw [lintegral_eq_lintegral_meas_lt P (ae_of_all _ hf0) hfm.aemeasurable,
    ← Set.Ioc_union_Ioi_eq_Ioi hA.le,
    lintegral_union measurableSet_Ioi (Set.disjoint_left.mpr fun t ht ht' => by
      exact absurd ht'.out (not_lt.mpr ht.2))]
  -- the part `t ∈ (0, A]`
  have hpart1 : ∫⁻ t in Set.Ioc 0 A, P {ω | t < f ω} ≤ ENNReal.ofReal (A * (B / A) ^ s) := by
    calc ∫⁻ t in Set.Ioc 0 A, P {ω | t < f ω} ≤
          ∫⁻ t in Set.Ioc 0 A, ENNReal.ofReal ((B / A) ^ s) := by
          refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
          exact (measure_mono (hsub1 t ht.1.le)).trans (htail A hA)
      _ = ENNReal.ofReal ((B / A) ^ s) * ENNReal.ofReal A := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
      _ = ENNReal.ofReal (A * (B / A) ^ s) := by
          rw [← ENNReal.ofReal_mul hQ0, mul_comm]
  -- the part `t ∈ (A, ∞)`
  have hq' : ∀ t : ℝ, 0 < t → (B / t) ^ s = B ^ s * t ^ (-s) := by
    intro t ht0
    rw [Real.div_rpow hB.le ht0.le, Real.rpow_neg ht0.le, div_eq_mul_inv]
  have hq : ∀ t ∈ Set.Ioi A, (B / t) ^ s = B ^ s * t ^ (-s) := fun t ht => hq' t (hA.trans ht)
  have hint : IntegrableOn (fun t : ℝ => (B / t) ^ s) (Set.Ioi A) := by
    have h1 : IntegrableOn (fun t : ℝ => B ^ s * t ^ (-s)) (Set.Ioi A) :=
      (integrableOn_Ioi_rpow_of_lt (a := -s) (by linarith) hA).const_mul (B ^ s)
    exact IntegrableOn.congr_fun h1 (fun t ht => (hq t ht).symm) measurableSet_Ioi
  have hval : ∫ t in Set.Ioi A, (B / t) ^ s = A * (B / A) ^ s / (s - 1) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hq, integral_const_mul,
      integral_Ioi_rpow_of_lt (by linarith) hA, hq' A hA, Real.rpow_add hA, Real.rpow_one]
    have hs' : -s + 1 ≠ 0 := by linarith
    have hs'' : s - 1 ≠ 0 := by linarith
    field_simp
    ring
  have hpart2 : ∫⁻ t in Set.Ioi A, P {ω | t < f ω} ≤
      ENNReal.ofReal (A * (B / A) ^ s / (s - 1)) := by
    rw [← hval, ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht =>
        Real.rpow_nonneg (div_nonneg hB.le (hA.trans ht).le) _))]
    refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
    exact (measure_mono (hsub2 t)).trans (htail t (hA.trans ht))
  calc _ ≤ ENNReal.ofReal (A * (B / A) ^ s) + ENNReal.ofReal (A * (B / A) ^ s / (s - 1)) :=
        add_le_add hpart1 hpart2
    _ = ENNReal.ofReal (A * (B / A) ^ s + A * (B / A) ^ s / (s - 1)) :=
        (ENNReal.ofReal_add (by positivity) (div_nonneg (by positivity) (by linarith))).symm
    _ ≤ ENNReal.ofReal (2 * A * (B / A) ^ s) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : A * (B / A) ^ s / (s - 1) ≤ A * (B / A) ^ s :=
          div_le_self (by positivity) (by linarith)
        linarith

/-! ### Seed tails -/

private lemma seed_Hmat_eq (g : ℝ) (W L : ℕ) (ω : Ω W L) :
    Hmat g W L ω = Hdet g (fun b => ((Real.sqrt 1 : ℝ) : ℂ) • gueBlock W L ω b) := by
  simp [Hmat]

/-- (7.7) [uv:eq:seed-exponential-tail], first line: at the seed height `η = c₀/n`,
`X_a(E) = ‖G_{aa}(E + iη)‖` has the tail `min{1, (C/(c₀ v))^{W/2}}`. -/
theorem seed_tail (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W L : ℕ), 3 ≤ L → ∀ g : ℝ, 2 / Real.sqrt κ ≤ g → ∀ c₀ : ℝ, 0 < c₀ →
      c₀ ≤ 1 → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ (a : Fin L) (v : ℝ), 0 < v →
      μ W L {ω | v < ‖blockOf (resolventMat (Hmat g W L ω)
          (↑E + ↑(c₀ / (coarseN g L : ℝ)) * Complex.I)) a a‖} ≤
        ENNReal.ofReal (min 1 ((C / (c₀ * v)) ^ ((W : ℝ) / 2))) := by
  obtain ⟨C, hC0, h⟩ := arcK_tail κ 1 hκ zero_le_one
  refine ⟨2 * C ^ 2, by positivity, ?_⟩
  intro W L hL g hg c₀ hc₀ hc₁ E hE a v hv
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  obtain ⟨hg1, hn1, hn2, hng⟩ := seed_window hκ hκ2 hL hg
  set n := coarseN g L with hn
  have hnL : n ≤ L := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  set η : ℝ := c₀ / (n : ℝ) with hη
  have hη0 : 0 < η := div_pos hc₀ hnR
  have hnη : (n : ℝ) * η = c₀ := by rw [hη]; field_simp
  have hη1 : η ≤ 1 := by
    rw [hη, div_le_iff₀ hnR]
    nlinarith
  set u : ℝ := Real.sqrt (c₀ * v / 2) with hu
  have hu0 : 0 < u := Real.sqrt_pos.mpr (by positivity)
  have hu2 : u ^ 2 = c₀ * v / 2 := Real.sq_sqrt (by positivity)
  have hsub : {ω | v < ‖blockOf (resolventMat (Hmat g W L ω) (↑E + ↑η * Complex.I)) a a‖} ⊆
      {ω | u < arcK g (↑E + ↑η * Complex.I)
        (fun b => ((Real.sqrt 1 : ℝ) : ℂ) • gueBlock W L ω b) a true n} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    set V : Fin L → Matrix (Fin W) (Fin W) ℂ :=
      fun b => ((Real.sqrt 1 : ℝ) : ℂ) • gueBlock W L ω b with hV
    have hVH : ∀ b, (V b).IsHermitian := fun b => by
      simp only [hV, Real.sqrt_one, Complex.ofReal_one, one_smul]
      exact gueBlock_isHermitian W L ω b
    rw [seed_Hmat_eq] at hω
    have h1 := norm_blockOf_resolvent_le (W := W) hL hg1 V hVH E hη0 hn1 hn2 a a
    rw [seed_arcDir_self a hnL, hnη] at h1
    set K := arcK g (↑E + ↑η * Complex.I) V a true n with hK
    have hK0 : 0 ≤ K := Real.iSup_nonneg fun _ => norm_nonneg _
    have h2 : c₀ * v / 2 < K ^ 2 := by
      have h3 : v < 2 * K * K / c₀ := lt_of_lt_of_le hω h1
      rw [lt_div_iff₀ hc₀] at h3
      nlinarith
    have hKpos : 0 < K := by
      rcases hK0.lt_or_eq with h | h
      · exact h
      · rw [← h] at h2
        have : 0 < c₀ * v / 2 := by positivity
        nlinarith
    exact (Real.sqrt_lt' hKpos).mpr h2
  have hb := h W L g hg n hnL hng E η 1 hE (by rw [abs_of_pos hη0]; exact hη1)
    (by rw [abs_of_pos hη0, hnη]; exact hc₁) zero_le_one le_rfl a true u hu0
  have heq : (C / u) ^ W = ((2 * C ^ 2) / (c₀ * v)) ^ ((W : ℝ) / 2) := by
    have h4 : (2 * C ^ 2) / (c₀ * v) = (C / u) ^ 2 := by
      rw [div_pow, hu2]
      field_simp
    rw [h4, ← Real.rpow_natCast (C / u) 2, ← Real.rpow_mul (div_pos hC0 hu0).le,
      ← Real.rpow_natCast (C / u) W]
    congr 1
    push_cast
    ring
  rw [heq] at hb
  exact le_trans (measure_mono hsub) hb

/-- (7.7) [uv:eq:seed-exponential-tail], second line:
`E[X_a 1{X_a > A}] ≤ 2A (C/(c₀ A))^{W/2}` for `A ≥ C/c₀` and `W ≥ 4`. -/
theorem seed_truncated_mean (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W L : ℕ), 4 ≤ W → 3 ≤ L → ∀ g : ℝ, 2 / Real.sqrt κ ≤ g → ∀ c₀ : ℝ,
      0 < c₀ → c₀ ≤ 1 → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ (a : Fin L) (A : ℝ), C / c₀ ≤ A →
      Integrable (fun ω => Set.indicator {x : ℝ | A < x} (fun x => x)
          ‖blockOf (resolventMat (Hmat g W L ω)
            (↑E + ↑(c₀ / (coarseN g L : ℝ)) * Complex.I)) a a‖) (μ W L) ∧
      ∫ ω, Set.indicator {x : ℝ | A < x} (fun x => x)
          ‖blockOf (resolventMat (Hmat g W L ω)
            (↑E + ↑(c₀ / (coarseN g L : ℝ)) * Complex.I)) a a‖ ∂(μ W L) ≤
        2 * A * (C / (c₀ * A)) ^ ((W : ℝ) / 2) := by
  obtain ⟨C, hC0, h⟩ := seed_tail κ hκ
  refine ⟨C, hC0, ?_⟩
  intro W L hW hL g hg c₀ hc₀ hc₁ E hE a A hA
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  obtain ⟨hg1, hn1, hn2, hng⟩ := seed_window hκ hκ2 hL hg
  have hnR : (0 : ℝ) < coarseN g L := by exact_mod_cast hn1
  have hη0 : 0 < c₀ / (coarseN g L : ℝ) := div_pos hc₀ hnR
  have hA0 : 0 < A := lt_of_lt_of_le (div_pos hC0 hc₀) hA
  have him : (↑E + ↑(c₀ / (coarseN g L : ℝ)) * Complex.I : ℂ).im ≠ 0 := by
    simpa using hη0.ne'
  have hG : Continuous fun ω : Ω W L => resolventMat (Hmat g W L ω)
      (↑E + ↑(c₀ / (coarseN g L : ℝ)) * Complex.I) := by
    have := seed_continuous_resolvent (Hmat g W L)
      (fun _ => ↑E + ↑(c₀ / (coarseN g L : ℝ)) * Complex.I) (seed_continuous_Hmat g W L)
      continuous_const (Hmat_isHermitian g W L) (fun _ => him)
    exact this
  have hX : Continuous fun ω : Ω W L => ‖blockOf (resolventMat (Hmat g W L ω)
      (↑E + ↑(c₀ / (coarseN g L : ℝ)) * Complex.I)) a a‖ :=
    seed_continuous_norm_block _ hG a a
  have hs : (2 : ℝ) ≤ (W : ℝ) / 2 := by
    have : (4 : ℝ) ≤ W := by exact_mod_cast hW
    linarith
  have key := seed_truncated_le (μ W L) _ hX.measurable (fun ω => norm_nonneg _)
    (B := C / c₀) (s := (W : ℝ) / 2) (A := A) (div_pos hC0 hc₀) hs hA0 fun v hv => by
      have := h W L hL g hg c₀ hc₀ hc₁ E hE a v hv
      rw [div_div]
      exact this.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))
  rw [div_div] at key
  exact key

/-! ### Heavy blocks and Poisson integrals -/

/-- A cyclic interval of `ℓ ≥ 1` coordinates of `ℤ_{LW}` meets at most `(ℓ - 1) / W + 2` of the
`L` blocks of `W` consecutive coordinates. -/
private lemma seed_card_blocks {W L : ℕ} (hW : 0 < W) (x : Fin (L * W)) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    ((cycInterval (L * W) x ℓ).image fun i => (finProdFinEquiv.symm i).1).card ≤
      (ℓ - 1) / W + 2 := by
  have hmem : ∀ i ∈ cycInterval (L * W) x ℓ, ∃ j, j < ℓ ∧ i.val = (x.val + j) % (L * W) := by
    intro i hi
    simp only [cycInterval, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    refine ⟨(i.val + L * W - x.val) % (L * W), hi, ?_⟩
    have hx := x.isLt
    have hi' := i.isLt
    have h1 : (i.val + L * W - x.val) % (L * W) ≡ i.val + L * W - x.val [MOD L * W] :=
      Nat.mod_modEq _ _
    have h2 := h1.add_left x.val
    have h3 : x.val + (i.val + L * W - x.val) = i.val + L * W := by omega
    rw [h3] at h2
    have h4 : (x.val + (i.val + L * W - x.val) % (L * W)) % (L * W) = (i.val + L * W) % (L * W) :=
      h2
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt hi'] at h4
    exact h4.symm
  have hsub : ((cycInterval (L * W) x ℓ).image
      fun i => (((finProdFinEquiv.symm i).1 : Fin L) : ℕ)) ⊆
      (Finset.Icc (x.val / W) ((x.val + (ℓ - 1)) / W)).image fun b => b % L := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨j, hj, hij⟩ := hmem i hi
    refine Finset.mem_image.mpr ⟨(x.val + j) / W, Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Nat.div_le_div_right (by omega)
    · exact Nat.div_le_div_right (by omega)
    · simp only [finProdFinEquiv_symm_apply, Fin.coe_divNat]
      rw [hij, Nat.mod_mul_left_div_self]
  have hcard : ((cycInterval (L * W) x ℓ).image fun i => (finProdFinEquiv.symm i).1).card =
      ((cycInterval (L * W) x ℓ).image
        fun i => (((finProdFinEquiv.symm i).1 : Fin L) : ℕ)).card := by
    rw [← Finset.card_image_of_injective _ Fin.val_injective, Finset.image_image]
    rfl
  rw [hcard]
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  rw [Nat.card_Icc]
  have hadd := Nat.add_div (a := x.val) (b := ℓ - 1) hW
  have hite : (if W ≤ x.val % W + (ℓ - 1) % W then 1 else 0) ≤ 1 := by split_ifs <;> omega
  generalize (if W ≤ x.val % W + (ℓ - 1) % W then 1 else 0) = e at hadd hite
  generalize (x.val + (ℓ - 1)) / W = p at hadd ⊢
  generalize x.val / W = q at hadd ⊢
  generalize (ℓ - 1) / W = r at hadd ⊢
  omega

/-- A unit vector with localization length `ℓ(ψ) < r` has total mass at least `1/4` on the blocks
of mass `> h`, when `(r/W + 2) h ≤ 1/4`: a cyclic interval of `ℓ(ψ)` coordinates carries mass
`≥ 1/2` and meets at most `r/W + 2` blocks, of which the blocks of mass `≤ h` carry at most
`1/4`. -/
private lemma seed_block_heavy {W L : ℕ} (ψ : Fin L × Fin W → ℂ) (hψ : ∑ x, ‖ψ x‖ ^ 2 = 1)
    {r h : ℝ} (hh : 0 < h) (hl : (ell W L ψ : ℝ) < r) (hrh : (r / W + 2) * h ≤ 1 / 4) :
    1 ≤ 4 * ∑ a : Fin L, Set.indicator {t : ℝ | h < t} (fun t => t) (∑ α, ‖ψ (a, α)‖ ^ 2) := by
  have hne : Nonempty (Fin L × Fin W) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    simp at hψ
  obtain ⟨x0⟩ := hne
  have hW : 0 < W := Fin.pos x0.2
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  have hN : 0 < L * W := (finProdFinEquiv x0).pos
  set p : Fin (L * W) → ℝ := fun i => ‖ψ (finProdFinEquiv.symm i)‖ ^ 2 with hp
  have hell : ell W L ψ = ellMass (L * W) p := rfl
  have hsum : ∑ i, p i = 1 := by
    rw [← hψ]
    exact Equiv.sum_comp finProdFinEquiv.symm (fun x => ‖ψ x‖ ^ 2)
  obtain ⟨x, hx⟩ := exists_mass_ellMass hN p (by rw [hsum]; norm_num)
  have hℓ1 : 1 ≤ ellMass (L * W) p := one_le_ellMass hN p
  set ℓ := ellMass (L * W) p with hℓ
  set I := cycInterval (L * W) x ℓ with hI
  set I' : Finset (Fin L × Fin W) := I.image finProdFinEquiv.symm with hI'
  have hI'sum : ∑ i ∈ I, p i = ∑ q ∈ I', ‖ψ q‖ ^ 2 := by
    rw [hI', Finset.sum_image (fun i _ j _ h => finProdFinEquiv.symm.injective h)]
  set S : Finset (Fin L) := I'.image Prod.fst with hS
  have hScard : S.card ≤ (ℓ - 1) / W + 2 := by
    have h1 := seed_card_blocks hW x hℓ1
    have h2 : S = I.image fun i => (finProdFinEquiv.symm i).1 := by
      rw [hS, hI', Finset.image_image]
      rfl
    rw [h2]
    exact h1
  have hScardR : (S.card : ℝ) * h ≤ 1 / 4 := by
    have h1 : (S.card : ℝ) ≤ r / W + 2 := by
      have h2 : (S.card : ℝ) ≤ (((ℓ - 1) / W + 2 : ℕ) : ℝ) := by exact_mod_cast hScard
      refine h2.trans ?_
      push_cast
      have h3 : (((ℓ - 1) / W : ℕ) : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) / W := Nat.cast_div_le
      have h4 : ((ℓ - 1 : ℕ) : ℝ) ≤ ℓ := by exact_mod_cast Nat.sub_le ℓ 1
      have h5 : (ℓ : ℝ) / W ≤ r / W := by
        rw [hell] at hl
        exact div_le_div_of_nonneg_right hl.le hWR.le
      have h6 : ((ℓ - 1 : ℕ) : ℝ) / W ≤ (ℓ : ℝ) / W := div_le_div_of_nonneg_right h4 hWR.le
      linarith
    exact (mul_le_mul_of_nonneg_right h1 hh.le).trans hrh
  have hfib : ∀ a : Fin L, ∑ q ∈ I'.filter (fun q => q.1 = a), ‖ψ q‖ ^ 2 ≤
      Set.indicator {t : ℝ | h < t} (fun t => t) (∑ α, ‖ψ (a, α)‖ ^ 2) + h := by
    intro a
    have h1 : ∑ q ∈ I'.filter (fun q => q.1 = a), ‖ψ q‖ ^ 2 ≤ ∑ α, ‖ψ (a, α)‖ ^ 2 := by
      have h2 : ∑ q ∈ (univ : Finset (Fin L × Fin W)).filter (fun q => q.1 = a), ‖ψ q‖ ^ 2 =
          ∑ α, ‖ψ (a, α)‖ ^ 2 := by
        rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single a]
        · simp
        · intro b _ hb
          simp [hb]
        · simp
      rw [← h2]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun q _ _ => by positivity
      intro q hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ q, (Finset.mem_filter.mp hq).2⟩
    by_cases hm : h < ∑ α, ‖ψ (a, α)‖ ^ 2
    · rw [Set.indicator_of_mem (show (∑ α, ‖ψ (a, α)‖ ^ 2) ∈ {t : ℝ | h < t} from hm)]
      linarith
    · rw [Set.indicator_of_notMem (show (∑ α, ‖ψ (a, α)‖ ^ 2) ∉ {t : ℝ | h < t} from hm)]
      linarith [not_lt.mp hm]
  have hmaps : ∀ q ∈ I', q.1 ∈ S := fun q hq => Finset.mem_image_of_mem _ hq
  have h1 : (1 : ℝ) / 2 ≤ ∑ q ∈ I', ‖ψ q‖ ^ 2 := by rw [← hI'sum]; exact hx
  rw [← Finset.sum_fiberwise_of_maps_to hmaps] at h1
  have h2 : ∑ a ∈ S, ∑ q ∈ I'.filter (fun q => q.1 = a), ‖ψ q‖ ^ 2 ≤
      ∑ a ∈ S, (Set.indicator {t : ℝ | h < t} (fun t => t) (∑ α, ‖ψ (a, α)‖ ^ 2) + h) :=
    Finset.sum_le_sum fun a _ => hfib a
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h2
  have h3 : ∑ a ∈ S, Set.indicator {t : ℝ | h < t} (fun t => t) (∑ α, ‖ψ (a, α)‖ ^ 2) ≤
      ∑ a : Fin L, Set.indicator {t : ℝ | h < t} (fun t => t) (∑ α, ‖ψ (a, α)‖ ^ 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun a _ _ =>
      Set.indicator_nonneg (fun t (ht : h < t) => (hh.trans ht).le) _
  linarith

private lemma seed_scalar (lam E η : ℝ) (hη : 0 < η) :
    ((poissonKer η lam E : ℝ) : ℂ) = (2 * Complex.I)⁻¹ *
      (((lam : ℂ) - (↑E + ↑η * Complex.I))⁻¹ - ((lam : ℂ) - (↑E - ↑η * Complex.I))⁻¹) := by
  have h1 : (lam : ℂ) - (↑E + ↑η * Complex.I) ≠ 0 := by
    intro h
    apply hη.ne'
    simpa using congrArg Complex.im h
  have h2 : (lam : ℂ) - (↑E - ↑η * Complex.I) ≠ 0 := by
    intro h
    apply hη.ne'
    simpa using congrArg Complex.im h
  have h3 : ((lam : ℂ) - E) ^ 2 + (η : ℂ) ^ 2 ≠ 0 := by
    have : (0 : ℝ) < (lam - E) ^ 2 + η ^ 2 := by positivity
    exact_mod_cast this.ne'
  unfold poissonKer
  push_cast
  field_simp
  ring_nf
  simp

/-- The Poisson-smoothed atoms `Σ_k η/((λ_k - E)² + η²) ψ_k(a,·) ψ_k(a,·)*` form the imaginary
part `(G_aa - G_aa*)/(2i)` of the diagonal block of the resolvent at `E + iη`. -/
private lemma seed_F_eq {W L : ℕ} {A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hA : A.IsHermitian) (a : Fin L) (E : ℝ) {η : ℝ} (hη : 0 < η) :
    ∑ k, ((poissonKer η (hA.eigenvalues k) E : ℝ) : ℂ) •
        Matrix.vecMulVec (fun α => hA.eigenvectorBasis k (a, α))
          (star fun α => hA.eigenvectorBasis k (a, α)) =
      (2 * Complex.I)⁻¹ • (blockOf (resolventMat A (↑E + ↑η * Complex.I)) a a -
        (blockOf (resolventMat A (↑E + ↑η * Complex.I)) a a)ᴴ) := by
  have hz : (↑E + ↑η * Complex.I : ℂ).im ≠ 0 := by simpa using hη.ne'
  ext α β
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.sub_apply,
    Matrix.conjTranspose_apply, blockOf, Matrix.of_apply, Pi.star_apply, smul_eq_mul]
  rw [resolventMat_apply hA hz, resolventMat_apply hA hz, star_sum, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hsc := seed_scalar (hA.eigenvalues k) E η hη
  have hstar : star (hA.eigenvectorBasis k (a, β) * star (hA.eigenvectorBasis k (a, α)) /
      ((hA.eigenvalues k : ℂ) - (↑E + ↑η * Complex.I))) =
      star (hA.eigenvectorBasis k (a, β)) * hA.eigenvectorBasis k (a, α) /
        ((hA.eigenvalues k : ℂ) - (↑E - ↑η * Complex.I)) := by
    simp [sub_eq_add_neg]
  rw [hstar, hsc]
  ring

private lemma seed_entry_le {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (i j : n) :
    ‖M i j‖ ≤ ‖M‖ := by
  have h := Matrix.l2_opNorm_mulVec M (EuclideanSpace.single j (1 : ℂ))
  have h1 : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  rw [h1, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le
    ((EuclideanSpace.equiv n ℂ).symm (M *ᵥ ⇑(EuclideanSpace.single j (1 : ℂ)))) i
  refine le_trans (le_of_eq ?_) this
  simp

private lemma seed_norm_im_le {m : Type*} [Fintype m] [DecidableEq m] (B : Matrix m m ℂ) :
    ‖(2 * Complex.I)⁻¹ • (B - Bᴴ)‖ ≤ ‖B‖ := by
  rw [norm_smul]
  have h1 : ‖(2 * Complex.I)⁻¹‖ = 1 / 2 := by simp
  have h2 := norm_sub_le B Bᴴ
  rw [Matrix.l2_opNorm_conjTranspose] at h2
  rw [h1]
  linarith [norm_nonneg B]

private lemma seed_trace_re_le {W : ℕ} (F : Matrix (Fin W) (Fin W) ℂ) :
    F.trace.re ≤ W * ‖F‖ := by
  rw [Matrix.trace, Complex.re_sum]
  calc ∑ i, (F.diag i).re ≤ ∑ _i : Fin W, ‖F‖ :=
        Finset.sum_le_sum fun i _ => (Complex.re_le_norm _).trans (seed_entry_le F i i)
    _ = W * ‖F‖ := by simp

/-- (4.3) [uv:eq:matrix-poisson] at the block `a` of the eigenvectors of `A`: the heavy mass in the
block is bounded by a Poisson integral of `W ‖G_aa‖`. -/
private lemma seed_block_poisson {W L : ℕ} {A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hA : A.IsHermitian) (a : Fin L) {η h : ℝ} (hη : 0 < η) (hh : 0 < h) (c d : ℝ) :
    ∑ k ∈ univ.filter (fun k => hA.eigenvalues k ∈ Set.Icc c d ∧
        h < ∑ α, ‖hA.eigenvectorBasis k (a, α)‖ ^ 2),
        ∑ α, ‖hA.eigenvectorBasis k (a, α)‖ ^ 2 ≤
      2 / π * (W * ∫ E in Set.Icc (c - η) (d + η),
        Set.indicator {E | h / (2 * η) <
            ‖blockOf (resolventMat A (↑E + ↑η * Complex.I)) a a‖}
          (fun E => ‖blockOf (resolventMat A (↑E + ↑η * Complex.I)) a a‖) E) := by
  have hz : (↑η * Complex.I : ℂ).im ≠ 0 := by simpa using hη.ne'
  have hP := poisson_smoothing_matrix (ι := Fin L × Fin W) (m := Fin W) hA.eigenvalues
    (fun k α => hA.eigenvectorBasis k (a, α)) hη hh c d
  refine hP.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← integral_const_mul]
  -- the smoothed atoms and the diagonal block of the resolvent
  have hFeq := fun E : ℝ => seed_F_eq hA a E hη
  have hnorm : ∀ E : ℝ, ‖∑ k, ((poissonKer η (hA.eigenvalues k) E : ℝ) : ℂ) •
      Matrix.vecMulVec (fun α => hA.eigenvectorBasis k (a, α))
        (star fun α => hA.eigenvectorBasis k (a, α))‖ ≤
      ‖blockOf (resolventMat A (↑E + ↑η * Complex.I)) a a‖ := fun E => by
    rw [hFeq E]
    exact seed_norm_im_le _
  have htr : ∀ E : ℝ, (∑ k, ((poissonKer η (hA.eigenvalues k) E : ℝ) : ℂ) •
      Matrix.vecMulVec (fun α => hA.eigenvectorBasis k (a, α))
        (star fun α => hA.eigenvectorBasis k (a, α))).trace.re =
      ∑ k, (∑ α, ‖hA.eigenvectorBasis k (a, α)‖ ^ 2) * poissonKer η (hA.eigenvalues k) E := by
    intro E
    rw [Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.trace_smul, Matrix.trace_vecMulVec]
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, Complex.re_sum, smul_eq_mul, Complex.re_ofReal_mul,
      Complex.ofReal_re]
    rw [mul_comm]
  have htr0 : ∀ E : ℝ, 0 ≤ (∑ k, ((poissonKer η (hA.eigenvalues k) E : ℝ) : ℂ) •
      Matrix.vecMulVec (fun α => hA.eigenvectorBasis k (a, α))
        (star fun α => hA.eigenvectorBasis k (a, α))).trace.re := fun E => by
    rw [htr E]
    refine Finset.sum_nonneg fun k _ => mul_nonneg (Finset.sum_nonneg fun α _ => by positivity) ?_
    unfold poissonKer
    positivity
  have hcont : Continuous fun E : ℝ => ‖blockOf (resolventMat A (↑E + ↑η * Complex.I)) a a‖ := by
    have hzc : Continuous fun E : ℝ => (↑E + ↑η * Complex.I : ℂ) :=
      Complex.continuous_ofReal.add continuous_const
    have hzi : ∀ E : ℝ, (↑E + ↑η * Complex.I : ℂ).im ≠ 0 := fun E => by simpa using hη.ne'
    have hG0 := seed_continuous_resolvent (fun _ : ℝ => A) (fun E : ℝ => (↑E + ↑η * Complex.I : ℂ))
        continuous_const hzc (fun _ => hA) hzi
    have hG : Continuous fun E : ℝ => resolventMat A (↑E + ↑η * Complex.I) := hG0
    exact seed_continuous_norm_block _ hG a a
  refine integral_mono_of_nonneg (ae_of_all _ fun E => ?_) ?_ (ae_of_all _ fun E => ?_)
  · exact Set.indicator_nonneg (fun E _ => htr0 E) E
  · exact ((hcont.integrableOn_Icc (a := c - η) (b := d + η) (μ := volume)).indicator
      (measurableSet_lt measurable_const hcont.measurable)).const_mul _
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
    split_ifs with h1 h2 h2
    · exact (seed_trace_re_le _).trans (mul_le_mul_of_nonneg_left (hnorm E) hW0)
    · exact absurd (lt_of_lt_of_le h1 (hnorm E)) h2
    · exact mul_nonneg hW0 (norm_nonneg _)
    · simp

/-- Deterministic step of the proof of Lemma 2.4 [uv:lem:short-spreading]: on simple spectrum,
eigenvectors with `ℓ < r` carry heavy-block mass `> 1/8` when `(r/W + 2) h ≤ 1/4`, and (4.3)
[uv:eq:matrix-poisson] bounds the heavy-block mass by Poisson integrals of `‖G_{aa}‖`. -/
theorem badCount_le_heavy_integral {W L : ℕ} {A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hA : A.IsHermitian) (hinj : Function.Injective hA.eigenvalues) (c d r h η : ℝ)
    (hh : 0 < h) (hη : 0 < η) (hrh : (r / W + 2) * h ≤ 1 / 4) :
    (badCount W L A (Set.Icc c d) r : ℝ) ≤
      16 / π * W * ∑ a : Fin L, ∫ E in Set.Icc (c - η) (d + η),
        Set.indicator {E | h / (2 * η) < ‖blockOf (resolventMat A (↑E + ↑η * Complex.I)) a a‖}
          (fun E => ‖blockOf (resolventMat A (↑E + ↑η * Complex.I)) a a‖) E := by
  have hn : ∀ k, ∑ x, ‖(⇑(hA.eigenvectorBasis k) : Fin L × Fin W → ℂ) x‖ ^ 2 = 1 := fun k => by
    rw [← EuclideanSpace.norm_sq_eq, OrthonormalBasis.norm_eq_one, one_pow]
  rw [badCount_eq_of_injective hA hinj (fun k => ⇑(hA.eigenvectorBasis k))
    (fun k => hA.mulVec_eigenvectorBasis k) hn (Set.Icc c d) r]
  set m : Fin L × Fin W → Fin L → ℝ := fun k a => ∑ α, ‖hA.eigenvectorBasis k (a, α)‖ ^ 2
    with hm
  set ind : ℝ → ℝ := Set.indicator {t : ℝ | h < t} (fun t => t) with hind
  have hind0 : ∀ t, 0 ≤ ind t := fun t =>
    Set.indicator_nonneg (fun t (ht : h < t) => (hh.trans ht).le) t
  set J : Finset (Fin L × Fin W) := univ.filter (fun k => hA.eigenvalues k ∈ Set.Icc c d)
    with hJ
  set Ia : Fin L → ℝ := fun a => ∫ E : ℝ in Set.Icc (c - η) (d + η),
    Set.indicator {E : ℝ | h / (2 * η) < ‖blockOf (resolventMat A (↑E + ↑η * Complex.I)) a a‖}
      (fun E : ℝ => ‖blockOf (resolventMat A (↑E + ↑η * Complex.I)) a a‖) E with hIa
  have hIa0 : ∀ a, 0 ≤ Ia a := fun a =>
    integral_nonneg fun E => Set.indicator_nonneg (fun E _ => norm_nonneg _) E
  have hfilt : ∀ a, ∑ k ∈ J, ind (m k a) =
      ∑ k ∈ univ.filter (fun k => hA.eigenvalues k ∈ Set.Icc c d ∧ h < m k a), m k a := by
    intro a
    rw [hJ, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h1 : hA.eigenvalues k ∈ Set.Icc c d <;> by_cases h2 : h < m k a <;>
      simp [hind, h1, h2]
  calc _
      = ∑ k ∈ univ.filter (fun k => hA.eigenvalues k ∈ Set.Icc c d ∧
          (ell W L ⇑(hA.eigenvectorBasis k) : ℝ) < r), (1 : ℝ) := by simp
    _ ≤ ∑ k ∈ univ.filter (fun k => hA.eigenvalues k ∈ Set.Icc c d ∧
          (ell W L ⇑(hA.eigenvectorBasis k) : ℝ) < r), 4 * ∑ a, ind (m k a) :=
        Finset.sum_le_sum fun k hk =>
          seed_block_heavy _ (hn k) hh (Finset.mem_filter.mp hk).2.2 hrh
    _ ≤ ∑ k ∈ J, 4 * ∑ a, ind (m k a) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => ?_
        · intro k hk
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, (Finset.mem_filter.mp hk).2.1⟩
        · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun a _ => hind0 _)
    _ = 4 * ∑ a, ∑ k ∈ J, ind (m k a) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ = 4 * ∑ a, ∑ k ∈ univ.filter (fun k => hA.eigenvalues k ∈ Set.Icc c d ∧ h < m k a),
          m k a := by
        simp only [hfilt]
    _ ≤ 4 * ∑ a, (2 / π * (W * Ia a)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ =>
          seed_block_poisson hA a hη hh c d) (by norm_num)
    _ = 8 / π * W * ∑ a, Ia a := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ring
    _ ≤ 16 / π * W * ∑ a, Ia a := by
        have h1 : 0 ≤ ∑ a, Ia a := Finset.sum_nonneg fun a _ => hIa0 a
        have h2 : 0 ≤ 8 / π * W * ∑ a, Ia a := by positivity
        have h3 : 16 / π * W * ∑ a, Ia a = 8 / π * W * ∑ a, Ia a + 8 / π * W * ∑ a, Ia a := by
          ring
        linarith

end LSBA
