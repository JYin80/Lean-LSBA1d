import LSBA.Transfer.Seed
import LSBA.Model.Bulk
import LSBA.Main.SimpleRanges
import LSBA.Spectral.Measurability
import LSBA.Dyson.Distribution

/-!
# Spreading on the scale `g²`

Lemma 2.4 [uv:lem:short-spreading], (2.10) [uv:eq:constant-scattering-outline], in count form
with the energy set `bulkSet g κ L₀ L` of (1.16) [eq:bulk-sampling], for every fixed threshold
`L₀`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Continuity of the diagonal resolvent blocks -/

private lemma shortSpreading_continuous_Hmat (g : ℝ) (W L : ℕ) : Continuous (Hmat g W L) := by
  refine continuous_matrix fun p q => ?_
  simp only [Hmat, Hdet, gueBlock, blockDiagOp, Matrix.smul_apply, Matrix.add_apply,
    Matrix.of_apply, smul_eq_mul]
  split_ifs <;> fun_prop

/-- `(ω, E) ↦ ‖G_{aa}(E + iη)‖` is jointly continuous for `η > 0`. -/
private lemma shortSpreading_continuous_block (g η : ℝ) (hη : 0 < η) (W L : ℕ) (a : Fin L) :
    Continuous fun p : Ω W L × ℝ =>
      ‖blockOf (resolventMat (Hmat g W L p.1) (↑p.2 + ↑η * Complex.I)) a a‖ := by
  have hc : Continuous fun p : Ω W L × ℝ =>
      Hmat g W L p.1 - (↑p.2 + ↑η * Complex.I : ℂ) •
        (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :=
    ((shortSpreading_continuous_Hmat g W L).comp continuous_fst).sub
      (((Complex.continuous_ofReal.comp continuous_snd).add continuous_const).smul
        continuous_const)
  have hG : Continuous fun p : Ω W L × ℝ =>
      resolventMat (Hmat g W L p.1) (↑p.2 + ↑η * Complex.I) := by
    refine continuous_iff_continuousAt.2 fun p => ?_
    have hu := isUnit_sub_smul_one (Hmat_isHermitian g W L p.1)
      (z := ↑p.2 + ↑η * Complex.I) (by simpa using hη.ne')
    have hdet : (Hmat g W L p.1 - (↑p.2 + ↑η * Complex.I : ℂ) •
        (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
    refine (continuousAt_matrix_inv _ ?_).comp hc.continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  refine continuous_norm.comp (continuous_matrix fun α β => ?_)
  exact hG.matrix_elem (a, α) (a, β)

/-! ### The expectation of the bad count through heavy blocks -/

/-- Expectation form of the deterministic step of the proof of Lemma 2.4 [uv:lem:short-spreading]:
if
`J ⊆ [c, d]` and the truncated means `E[X_a 1{X_a > h/(2η)}]`, `X_a = ‖G_{aa}(E + iη)‖`, are at
most `B` on `[c - η, d + η]`, then `E badCount ≤ (16/π) W L B (d - c + 2η)`. -/
private lemma shortSpreading_heavy_mean {W L : ℕ} (g : ℝ) {J : Set ℝ}
    {c d r h η B : ℝ} (hJ : J ⊆ Set.Icc c d) (hh : 0 < h) (hη : 0 < η)
    (hrh : (r / W + 2) * h ≤ 1 / 4) (hB : 0 ≤ B)
    (hE : ∀ (a : Fin L), ∀ E ∈ Set.Icc (c - η) (d + η),
      Integrable (fun ω => Set.indicator {x : ℝ | h / (2 * η) < x} (fun x => x)
          ‖blockOf (resolventMat (Hmat g W L ω) (↑E + ↑η * Complex.I)) a a‖) (μ W L) ∧
      ∫ ω, Set.indicator {x : ℝ | h / (2 * η) < x} (fun x => x)
          ‖blockOf (resolventMat (Hmat g W L ω) (↑E + ↑η * Complex.I)) a a‖ ∂(μ W L) ≤ B)
    (hJm : MeasurableSet J) (hcd : c - η ≤ d + η) :
    ∫ ω, (badCount W L (Hmat g W L ω) J r : ℝ) ∂(μ W L) ≤
      16 / π * W * (L * (B * ((d + η) - (c - η)))) := by
  set S := Set.Icc (c - η) (d + η) with hS
  set G : Fin L → Ω W L × ℝ → ℝ := fun a p =>
    Set.indicator {x : ℝ | h / (2 * η) < x} (fun x => x)
      ‖blockOf (resolventMat (Hmat g W L p.1) (↑p.2 + ↑η * Complex.I)) a a‖ with hG
  have hGm : ∀ a, Measurable (G a) := fun a =>
    (measurable_id.indicator (measurableSet_lt measurable_const measurable_id)).comp
      (shortSpreading_continuous_block g η hη W L a).measurable
  have hthr : 0 < h / (2 * η) := by positivity
  have hG0 : ∀ a p, 0 ≤ G a p := fun a p =>
    Set.indicator_nonneg (fun x (hx : h / (2 * η) < x) => (hthr.trans hx).le) _
  have hFm : ∀ a, Measurable fun p : Ω W L × ℝ => ENNReal.ofReal (G a p) := fun a =>
    ENNReal.measurable_ofReal.comp (hGm a)
  set K : ℝ := 16 / π * W with hK
  have hK0 : 0 ≤ K := by positivity
  -- the pointwise bound on simple spectrum
  have hpt : ∀ᵐ ω ∂(μ W L), ENNReal.ofReal (badCount W L (Hmat g W L ω) J r : ℝ) ≤
      ∑ a : Fin L, ENNReal.ofReal K * ∫⁻ E in S, ENNReal.ofReal (G a (ω, E)) := by
    filter_upwards [ae_injective_eigenvalues g W L] with ω hω
    have h1 := badCount_le_heavy_integral (Hmat_isHermitian g W L ω) hω c d r h η hh hη hrh
    have h2 : (badCount W L (Hmat g W L ω) J r : ℝ) ≤
        badCount W L (Hmat g W L ω) (Set.Icc c d) r := by
      exact_mod_cast badCount_mono W L _ hJ le_rfl
    have h3 : ∀ a : Fin L, ∫ E in S, Set.indicator
        {E | h / (2 * η) < ‖blockOf (resolventMat (Hmat g W L ω) (↑E + ↑η * Complex.I)) a a‖}
        (fun E => ‖blockOf (resolventMat (Hmat g W L ω) (↑E + ↑η * Complex.I)) a a‖) E =
        ∫ E in S, G a (ω, E) := by
      intro a
      refine integral_congr_ae (ae_of_all _ fun E => ?_)
      simp only [hG, Set.indicator_apply, Set.mem_ofPred_eq]
    have h4 : ∀ a : Fin L, ENNReal.ofReal (∫ E in S, G a (ω, E)) ≤
        ∫⁻ E in S, ENNReal.ofReal (G a (ω, E)) := by
      intro a
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun E => hG0 a _)
        ((hGm a).comp measurable_prodMk_left).aestronglyMeasurable]
      exact ENNReal.ofReal_toReal_le
    calc ENNReal.ofReal (badCount W L (Hmat g W L ω) J r : ℝ)
        ≤ ENNReal.ofReal (K * ∑ a : Fin L, ∫ E in S, G a (ω, E)) := by
          refine ENNReal.ofReal_le_ofReal (h2.trans (h1.trans (le_of_eq ?_)))
          exact congrArg (fun t => 16 / π * (W : ℝ) * t) (Finset.sum_congr rfl fun a _ => h3 a)
      _ = ∑ a : Fin L, ENNReal.ofReal K * ENNReal.ofReal (∫ E in S, G a (ω, E)) := by
          rw [ENNReal.ofReal_mul hK0, ENNReal.ofReal_sum_of_nonneg
            (fun a _ => integral_nonneg fun E => hG0 a _), Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum fun a _ => by gcongr; exact h4 a
  -- integrate and swap
  have hinner : ∀ a : Fin L, ∫⁻ ω, (∫⁻ E in S, ENNReal.ofReal (G a (ω, E))) ∂(μ W L) ≤
      ENNReal.ofReal B * ENNReal.ofReal ((d + η) - (c - η)) := by
    intro a
    rw [lintegral_lintegral_swap ((hFm a).aemeasurable)]
    calc ∫⁻ E in S, (∫⁻ ω, ENNReal.ofReal (G a (ω, E)) ∂(μ W L))
        ≤ ∫⁻ _E in S, ENNReal.ofReal B := by
          refine setLIntegral_mono' measurableSet_Icc fun E hE' => ?_
          obtain ⟨hi, hb⟩ := hE a E hE'
          rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun ω => hG0 a (ω, E))]
          exact ENNReal.ofReal_le_ofReal hb
      _ = ENNReal.ofReal B * ENNReal.ofReal ((d + η) - (c - η)) := by
          rw [setLIntegral_const, hS, Real.volume_Icc]
  have hlin : ∫⁻ ω, ENNReal.ofReal (badCount W L (Hmat g W L ω) J r : ℝ) ∂(μ W L) ≤
      ENNReal.ofReal (16 / π * W * (L * (B * ((d + η) - (c - η))))) := by
    calc ∫⁻ ω, ENNReal.ofReal (badCount W L (Hmat g W L ω) J r : ℝ) ∂(μ W L)
        ≤ ∫⁻ ω, (∑ a : Fin L, ENNReal.ofReal K * ∫⁻ E in S, ENNReal.ofReal (G a (ω, E)))
            ∂(μ W L) := lintegral_mono_ae hpt
      _ = ∑ a : Fin L, ENNReal.ofReal K *
            ∫⁻ ω, (∫⁻ E in S, ENNReal.ofReal (G a (ω, E))) ∂(μ W L) := by
          rw [lintegral_finsetSum _ fun a _ =>
            ((hFm a).lintegral_prod_right').const_mul _]
          refine Finset.sum_congr rfl fun a _ => ?_
          exact lintegral_const_mul _ (hFm a).lintegral_prod_right'
      _ ≤ ∑ _a : Fin L, ENNReal.ofReal K *
            (ENNReal.ofReal B * ENNReal.ofReal ((d + η) - (c - η))) :=
          Finset.sum_le_sum fun a _ => by gcongr; exact hinner a
      _ = ENNReal.ofReal (16 / π * W * (L * (B * ((d + η) - (c - η))))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← hK, ENNReal.ofReal_mul hK0, ENNReal.ofReal_mul (Nat.cast_nonneg L),
            ENNReal.ofReal_mul hB, ENNReal.ofReal_natCast]
          ring
  have hnn : 0 ≤ 16 / π * W * (L * (B * ((d + η) - (c - η)))) := by
    have : 0 ≤ (d + η) - (c - η) := by linarith
    positivity
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => Nat.cast_nonneg _)
    (aemeasurable_badCount_Hmat g W L hJm r).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hnn hlin

/-! ### Exponential rates -/

/-- `4x e^{-x/25} ≤ 200 e^{-x/50}`. -/

private lemma shortSpreading_haar_rate (x : ℝ) :
    4 * x * Real.exp (-x / 25) ≤ 200 * Real.exp (-(1 / 50) * x) := by
  have h1 : x / 50 + 1 ≤ Real.exp (x / 50) := Real.add_one_le_exp _
  have h2 : Real.exp (-x / 25) = Real.exp (-(1 / 50) * x) * Real.exp (-(1 / 50) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : Real.exp (x / 50) * Real.exp (-(1 / 50) * x) = 1 := by
    rw [← Real.exp_add, show x / 50 + -(1 / 50) * x = 0 by ring, Real.exp_zero]
  have h4 : 0 < Real.exp (-(1 / 50) * x) := Real.exp_pos _
  have h5 : x * Real.exp (-(1 / 50) * x) ≤ 50 := by
    have : x ≤ 50 * Real.exp (x / 50) := by linarith
    calc x * Real.exp (-(1 / 50) * x) ≤ 50 * Real.exp (x / 50) * Real.exp (-(1 / 50) * x) :=
          mul_le_mul_of_nonneg_right this h4.le
      _ = 50 := by rw [mul_assoc, h3, mul_one]
  rw [h2]
  nlinarith

/-- `2^{-x/2} ≤ e^{-x/50}` for `x ≥ 0`. -/
private lemma shortSpreading_seed_rate (x : ℝ) (hx : 0 ≤ x) :
    (1 / 2 : ℝ) ^ (x / 2) ≤ Real.exp (-(1 / 50) * x) := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  refine Real.exp_le_exp.mpr ?_
  have e : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
  rw [e]
  have := Real.log_two_gt_d9
  nlinarith

/-! ### Arithmetic of the constants -/

/-- The window `n = coarseN g L` of (7.4) [uvs:eq:window-length] satisfies
`min{L, g²} ≤ 4n` for `L ≥ 3` and `g² ≥ 2`. -/
private lemma shortSpreading_window {g : ℝ} {L : ℕ} (hL : 3 ≤ L) (hg : 2 ≤ g ^ 2) :
    min (L : ℝ) (g ^ 2) ≤ 4 * (coarseN g L : ℝ) := by
  have hnR : ((coarseN g L : ℕ) : ℝ) =
      min (((L - 1) / 2 : ℕ) : ℝ) ((⌊g ^ 2⌋₊ : ℕ) : ℝ) := by
    rw [coarseN, Nat.cast_min]
  have ha : (L : ℝ) ≤ 4 * (((L - 1) / 2 : ℕ) : ℝ) := by
    have : L ≤ 4 * ((L - 1) / 2) := by omega
    exact_mod_cast this
  have hb : g ^ 2 ≤ 4 * ((⌊g ^ 2⌋₊ : ℕ) : ℝ) := by
    have h1 := Nat.lt_floor_add_one (g ^ 2)
    linarith
  rw [hnR]
  rcases le_total (((L - 1) / 2 : ℕ) : ℝ) ((⌊g ^ 2⌋₊ : ℕ) : ℝ) with h | h
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans ha
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans hb

/-- The heavy-block condition `(r/W + 2) h ≤ 1/4` of the proof of Lemma 2.4 [uv:lem:short-spreading]
for
`r = W m / (16 M)`, `h = 4 C_s / n`, when `256 C_s ≤ M < m ≤ 4n`. -/
private lemma shortSpreading_heavy_le {W M m n Cs : ℝ} (hW : 0 < W) (hM : 1 ≤ M)
    (hMC : 256 * Cs ≤ M) (hmM : M < m) (hmn : m ≤ 4 * n) :
    (1 / (16 * M) * W * m / W + 2) * (4 * Cs / n) ≤ 1 / 4 := by
  have hm0 : 0 < m := by linarith
  have hn0 : 0 < n := by linarith
  have e1 : 1 / (16 * M) * W * m / W = m / (16 * M) := by
    field_simp
  rw [e1]
  have key : (m / (16 * M) + 2) * (4 * Cs) ≤ n / 4 := by
    have e : m / (16 * M) * (4 * Cs) = m * Cs / (4 * M) := by
      field_simp
      ring
    have q1 : m * Cs / (4 * M) ≤ m / 1024 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [mul_le_mul_of_nonneg_left hMC hm0.le]
    have q2 : 8 * Cs ≤ m / 32 := by linarith
    rw [add_mul, e]
    linarith
  calc (m / (16 * M) + 2) * (4 * Cs / n)
      = (m / (16 * M) + 2) * (4 * Cs) / n := by ring
    _ ≤ n / 4 / n := div_le_div_of_nonneg_right key hn0.le
    _ = 1 / 4 := by field_simp

/-- Normalization of the transfer bound: `(WL)⁻¹ I ≤ C e^{-W/50}` from
`I ≤ (16/π) W L · 2A 2^{-W/2} ℓ` with `ℓ ≤ 6`. -/
private lemma shortSpreading_final {W L I A ℓ : ℝ} (hW : 0 < W) (hL : 0 < L) (hA : 0 < A)
    (hℓ : ℓ ≤ 6) (hI : I ≤ 16 / π * W * (L * (2 * A * (1 / 2 : ℝ) ^ (W / 2) * ℓ))) :
    (W * L)⁻¹ * I ≤ max (16 / π * (2 * A) * 6) 200 * Real.exp (-(1 / 50) * W) := by
  have hq : 0 ≤ (1 / 2 : ℝ) ^ (W / 2) := by positivity
  calc (W * L)⁻¹ * I
      ≤ (W * L)⁻¹ * (16 / π * W * (L * (2 * A * (1 / 2 : ℝ) ^ (W / 2) * ℓ))) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = 16 / π * (2 * A * (1 / 2 : ℝ) ^ (W / 2)) * ℓ := by
        field_simp
    _ ≤ 16 / π * (2 * A * (1 / 2 : ℝ) ^ (W / 2)) * 6 :=
        mul_le_mul_of_nonneg_left hℓ (by positivity)
    _ = 16 / π * (2 * A) * 6 * (1 / 2 : ℝ) ^ (W / 2) := by ring
    _ ≤ max (16 / π * (2 * A) * 6) 200 * Real.exp (-(1 / 50) * W) :=
        mul_le_mul (le_max_left _ _) (shortSpreading_seed_rate W hW.le) hq
          (le_trans (by norm_num) (le_max_right _ _))

/-! ### Lemma 2.4 [uv:lem:short-spreading] -/

/-- Lemma 2.4 [uv:lem:short-spreading], (2.10) [uv:eq:constant-scattering-outline], in count
form with the energy set `bulkSet g κ L₀ L` of (1.16) [eq:bulk-sampling]. -/
theorem short_spreading (κ : ℝ) (hκ : 0 < κ ∧ κ < 1 / 2) :
    ∃ Cκ : ℝ, ∀ L₀ : ℕ, ∃ (W₀ : ℕ) (cκ C c : ℝ), 0 < cκ ∧ 0 < c ∧
      ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g : ℝ, Cκ ≤ g →
      ((W : ℝ) * L)⁻¹ * ∫ ω, (badCount W L (Hmat g W L ω) (bulkSet g κ L₀ L)
          (cκ * W * min (L : ℝ) (g ^ 2)) : ℝ) ∂(μ W L) ≤ C * Real.exp (-c * W) := by
  obtain ⟨hκ0, hκ1⟩ := hκ
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = (κ / 2) ^ 2 / 4 := ⟨_, rfl⟩
  have hk0 : 0 < k := by rw [hk]; positivity
  have hk1 : k < 1 / 64 := by rw [hk]; nlinarith
  obtain ⟨Cs, hCs0, hseed⟩ := seed_truncated_mean (k / 2) (by positivity)
  refine ⟨8 / (κ / 2) ^ 2, fun L₀ => ?_⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = max (256 * Cs) (max (L₀ : ℝ) 1) := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := hM ▸ le_trans (le_max_right _ _) (le_max_right _ _)
  have hMC : 256 * Cs ≤ M := hM ▸ le_max_left _ _
  have hML : (L₀ : ℝ) ≤ M := hM ▸ le_trans (le_max_left _ _) (le_max_right _ _)
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = k / 4 := ⟨_, rfl⟩
  have hc₀0 : 0 < c₀ := by rw [hc₀]; positivity
  have hc₀1 : c₀ ≤ 1 := by rw [hc₀]; linarith
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 2 * Cs / c₀ := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; positivity
  refine ⟨4, 1 / (16 * M), max (16 / π * (2 * A) * 6) 200, 1 / 50, by positivity, by norm_num,
    ?_⟩
  intro W hW L hL g hg
  have hW4 : (4 : ℝ) ≤ W := by exact_mod_cast hW
  have hWpos : (0 : ℝ) < W := by linarith
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hCκ : 128 < 8 / (κ / 2) ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  have hg1 : 1 ≤ g := by linarith
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = min (L : ℝ) (g ^ 2) := ⟨_, rfl⟩
  rw [← hm]
  have hm0 : 0 < m := by rw [hm]; exact lt_min (by linarith) (by positivity)
  have hexp0 : 0 < Real.exp (-(1 / 50) * (W : ℝ)) := Real.exp_pos _
  rcases le_or_gt m M with hmM | hmM
  · -- `m ≤ M`: Lemma 2.1 [thm:orbital], (2.2) [eq:haar-count], with `r ≤ W/8`
    have hr : 1 / (16 * M) * W * m ≤ (W : ℝ) / 8 := by
      have h1 : 1 / (16 * M) * m ≤ 1 / 16 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
        linarith
      nlinarith
    refine (haar_count_le W L g (measurableSet_bulkSet g κ L₀ L) hr).trans ?_
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) hexp0.le)
    exact shortSpreading_haar_rate W
  · -- `m > M`: the bulk window (1.14) [eq:bulk-bridge] and the seed tails
    have hLL₀ : ¬ L < L₀ := by
      intro h
      have h1 : (L : ℝ) < L₀ := by exact_mod_cast h
      have h2 : m ≤ L := hm ▸ min_le_left _ _
      linarith
    have hJ : bulkSet g κ L₀ L ⊆ Set.Icc (-(2 - k)) (2 - k) := by
      intro E hE
      simp only [bulkSet, hLL₀, ite_false] at hE
      have h1 := bulk_window_explicit (κ / 2) ⟨by positivity, by linarith⟩ g (by linarith)
        (Or.inr hg) E hE
      rw [← hk] at h1
      exact abs_le.mp h1
    have hmn : m ≤ 4 * (coarseN g L : ℝ) :=
      hm ▸ shortSpreading_window hL (by nlinarith)
    have hn0 : (0 : ℝ) < coarseN g L := by linarith
    have hn1 : (1 : ℝ) ≤ coarseN g L := by
      have : 0 < coarseN g L := by exact_mod_cast hn0
      exact_mod_cast this
    have hη0 : 0 < c₀ / (coarseN g L : ℝ) := div_pos hc₀0 hn0
    have hηc : c₀ / (coarseN g L : ℝ) ≤ c₀ := div_le_self hc₀0.le hn1
    -- the heavy threshold `h = 2ηA = 4 C_s / n`
    have hh0 : 0 < 2 * (c₀ / (coarseN g L : ℝ)) * A := by positivity
    have hhA : 2 * (c₀ / (coarseN g L : ℝ)) * A / (2 * (c₀ / (coarseN g L : ℝ))) = A := by
      field_simp
    have hh4 : 2 * (c₀ / (coarseN g L : ℝ)) * A = 4 * Cs / coarseN g L := by
      rw [hA]
      field_simp
      ring
    have hrh : (1 / (16 * M) * W * m / W + 2) * (2 * (c₀ / (coarseN g L : ℝ)) * A) ≤ 1 / 4 := by
      rw [hh4]
      exact shortSpreading_heavy_le hWpos hM1 hMC hmM hmn
    -- the seed tails (7.7) [uv:eq:seed-exponential-tail] on `[c - η, d + η]`
    have hgs : 2 / Real.sqrt (k / 2) ≤ g := by
      have h1 : k ≤ Real.sqrt (k / 2) := by
        calc k = Real.sqrt (k ^ 2) := (Real.sqrt_sq hk0.le).symm
          _ ≤ Real.sqrt (k / 2) := Real.sqrt_le_sqrt (by nlinarith)
      have h2 : 2 / Real.sqrt (k / 2) ≤ 2 / k := div_le_div_of_nonneg_left (by norm_num) hk0 h1
      have h3 : 2 / k = 8 / (κ / 2) ^ 2 := by
        rw [hk]
        field_simp
        ring
      linarith
    have hAge : Cs / c₀ ≤ A := by
      rw [hA]
      exact div_le_div_of_nonneg_right (by linarith) hc₀0.le
    have hhalf : Cs / (c₀ * A) = 1 / 2 := by
      rw [hA]
      field_simp
    have hseedE : ∀ (a : Fin L), ∀ E ∈ Set.Icc (-(2 - k) - c₀ / (coarseN g L : ℝ))
        ((2 - k) + c₀ / (coarseN g L : ℝ)),
        Integrable (fun ω => Set.indicator
          {x : ℝ | 2 * (c₀ / (coarseN g L : ℝ)) * A / (2 * (c₀ / (coarseN g L : ℝ))) < x}
          (fun x => x) ‖blockOf (resolventMat (Hmat g W L ω)
            (↑E + ↑(c₀ / (coarseN g L : ℝ)) * Complex.I)) a a‖) (μ W L) ∧
        ∫ ω, Set.indicator
          {x : ℝ | 2 * (c₀ / (coarseN g L : ℝ)) * A / (2 * (c₀ / (coarseN g L : ℝ))) < x}
          (fun x => x) ‖blockOf (resolventMat (Hmat g W L ω)
            (↑E + ↑(c₀ / (coarseN g L : ℝ)) * Complex.I)) a a‖ ∂(μ W L) ≤
          2 * A * (1 / 2) ^ ((W : ℝ) / 2) := by
      intro a E hE
      have habs : |E| ≤ 2 - k / 2 := by
        rw [abs_le]
        constructor <;> linarith [hE.1, hE.2]
      have hs := hseed W L hW hL g hgs c₀ hc₀0 hc₀1 E habs a A hAge
      rw [hhalf] at hs
      rw [hhA]
      exact hs
    have hB : 0 ≤ 2 * A * (1 / 2 : ℝ) ^ ((W : ℝ) / 2) := by positivity
    have hmain := shortSpreading_heavy_mean (W := W) (L := L) g (J := bulkSet g κ L₀ L)
      (c := -(2 - k)) (d := 2 - k) (r := 1 / (16 * M) * W * m)
      (h := 2 * (c₀ / (coarseN g L : ℝ)) * A) (η := c₀ / (coarseN g L : ℝ))
      (B := 2 * A * (1 / 2 : ℝ) ^ ((W : ℝ) / 2)) hJ hh0 hη0 hrh hB hseedE
      (measurableSet_bulkSet g κ L₀ L) (by linarith only [hk1, hη0])
    have hlen : (2 - k + c₀ / (coarseN g L : ℝ)) - (-(2 - k) - c₀ / (coarseN g L : ℝ)) ≤ 6 := by
      linarith only [hk0, hηc, hc₀1]
    exact shortSpreading_final hWpos (by linarith) hA0 hlen hmain

end LSBA
