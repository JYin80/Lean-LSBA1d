import LSBA.Final.MatchLarge
import LSBA.Prop.Theorem412

/-!
# Large-coupling resolvent moments

Theorem 2.5 [uvu:thm:terminal] in uniform fixed-rate form: for `g ≥ C_κ`,
`ρ(W) g² log W ≤ L ≤ g² W²` and `|E| ≤ 2 − κ`, the moments (2.11) [uvu:eq:local-moments] of
`Im G_xx` at the height `η_L`, with no upper bound on `g`, from Theorem 5.12 [gc:thm:common](ii)
at large coupling, the terminal matching and the seed moments of Lemma 5.5
[fo:lem:resolvent-moments] at `t = 1`.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- `1 ≤ log W` for `W ≥ 3`. -/
private lemma large_one_le_log {W : ℕ} (hW : 3 ≤ W) : 1 ≤ Real.log W := by
  have h3 : (3 : ℝ) ≤ W := by exact_mod_cast hW
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

open scoped Matrix.Norms.L2Operator in
/-- An entry of a matrix is bounded by its `L²` operator norm. -/
private lemma large_norm_entry_le {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (i j : n) : ‖X i j‖ ≤ ‖X‖ := by
  have h := Matrix.l2_opNorm_mulVec X ((EuclideanSpace.equiv n ℂ).symm (Pi.single j 1))
  have hx : ‖(EuclideanSpace.equiv n ℂ).symm (Pi.single j (1 : ℂ))‖ = 1 := by simp
  rw [hx, mul_one] at h
  refine le_trans (le_of_eq ?_) ((PiLp.norm_apply_le _ i).trans h)
  simp [Matrix.mulVec_single]

open scoped Matrix.Norms.L2Operator in
/-- The seed moments in the proof of Theorem 2.5 [uvu:thm:terminal]: Lemma 5.5
[fo:lem:resolvent-moments] at `t = 1`, `η₀ = g^{-2}`, `C₀ = 1` and moment order `2p` dominates
`Im G_xx(E + iη₀)` by a nonnegative variable `Z` with `E Z^{2p} ≤ C_s`. -/
private lemma large_seed (κ p : ℝ) (hκ : 0 < κ) (hp : 0 < p) :
    ∃ Cs : ℝ, 0 < Cs ∧ ∀ W : ℕ, 8 * p ≤ W → ∀ L : ℕ, ∀ g : ℝ, 2 / Real.sqrt κ ≤ g →
      4 * g ^ 2 ≤ L → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ x : Fin L × Fin W,
      ∃ Z : Ω W L → ℝ, (∀ ω, 0 ≤ Z ω) ∧
        (∀ ω, (resolventMat (Hmat g W L ω) (E + (1 / g ^ 2 : ℝ) * Complex.I) x x).im ≤ Z ω) ∧
        Integrable (fun ω => Z ω ^ (2 * p)) (μ W L) ∧ ∫ ω, Z ω ^ (2 * p) ∂(μ W L) ≤ Cs := by
  obtain ⟨Cs, hCs, H⟩ := resolvent_moments_Hmat κ (2 * p) 1 hκ (by positivity) one_pos
  refine ⟨Cs, hCs, fun W hW L g hg hL E hE ⟨a, α⟩ => ?_⟩
  have hκs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hg0 : 0 < g := lt_of_lt_of_le (by positivity) hg
  have hg2 : 0 < g ^ 2 := by positivity
  obtain ⟨hi, hint⟩ :=
    H W (by linarith) L g hg hL E (1 / g ^ 2) hE (by positivity) le_rfl a a
  refine ⟨fun ω => ‖blockOf (resolventMat (Hmat g W L ω)
    ((E : ℂ) + ((1 / g ^ 2 : ℝ) : ℂ) * Complex.I)) a a‖, fun ω => norm_nonneg _, fun ω => ?_,
    hi, ?_⟩
  · have h1 := large_norm_entry_le (blockOf (resolventMat (Hmat g W L ω)
      ((E : ℂ) + ((1 / g ^ 2 : ℝ) : ℂ) * Complex.I)) a a) α α
    simp only [blockOf, Matrix.of_apply] at h1
    exact (Complex.im_le_norm _).trans h1
  · have h1 : g ^ 2 * (1 / g ^ 2) = 1 := by field_simp
    rw [h1, Real.one_rpow, mul_one] at hint
    exact hint

/-- Theorem 2.5 [uvu:thm:terminal], (2.11) [uvu:eq:local-moments], uniform fixed-rate form: for
`g ≥ C_κ`, `ρ(W) g² log W ≤ L ≤ g² W²` (`ρ → ∞`) and `|E| ≤ 2 - κ`, the moments of
`Im G_xx(E + iη_L)` are at most `C_p`; no upper bound on `g`. -/
theorem large_lower (κ ν p : ℝ) (hκ : 0 < κ ∧ κ < 2) (hν : 0 < ν ∧ ν < 1) (hp : 0 < p) :
    ∃ Cκ Cp : ℝ, 1 < Cκ ∧ 0 < Cp ∧ ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, Cκ ≤ g → ∀ L : ℕ, ρ W * g ^ 2 * Real.log W ≤ L →
      (L : ℝ) ≤ g ^ 2 * (W : ℝ) ^ 2 → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ x : Fin L × Fin W,
        Integrable (fun ω' => ((resolventMat (Hmat g W L ω') (E + etaL W L g ν * Complex.I) x x).im)
          ^ p) (μ W L) ∧
        ∫ ω', ((resolventMat (Hmat g W L ω') (E + etaL W L g ν * Complex.I) x x).im) ^ p
          ∂(μ W L) ≤ Cp := by
  obtain ⟨hκ0, hκ2⟩ := hκ
  obtain ⟨Cm, c, C₁, hCm, hc, hC₁, Hm⟩ := terminal_match_large κ hκ0 hκ2
  obtain ⟨W₁, Hb⟩ := endBudget_large ν hν
  obtain ⟨hν0, hν1⟩ := hν
  obtain ⟨C0, hC0, H412⟩ := theorem412_large κ 2 hκ0 hκ2 two_pos (ν / 3) (by positivity)
  obtain ⟨Cs, hCs, Hs⟩ := large_seed κ p hκ0 hp
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  set Cκ : ℝ := max (max (Real.sqrt 2 * C0) Cm) (max (2 / Real.sqrt κ) 2) with hCκ
  have hCκ2 : 2 ≤ Cκ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hCκ0 : Real.sqrt 2 * C0 ≤ Cκ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCκm : Cm ≤ Cκ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCκκ : 2 / Real.sqrt κ ≤ Cκ := le_trans (le_max_left _ _) (le_max_right _ _)
  set K : ℝ := max (1 / c) C₁ with hK
  have hK0 : 0 < K := lt_of_lt_of_le hC₁ (le_max_right _ _)
  have hK1 : 0 < K * (C₁ + 1) := mul_pos hK0 (by linarith)
  refine ⟨Cκ, (K * (C₁ + 1)) ^ p + Real.sqrt Cs, by linarith,
    add_pos_of_pos_of_nonneg (Real.rpow_pos_of_pos hK1 p) (Real.sqrt_nonneg _), fun ρ hρ => ?_⟩
  have hC0' : C0 ≤ Cκ / Real.sqrt 2 := by
    rw [le_div_iff₀ hs2]; linarith [mul_comm (Real.sqrt 2) C0]
  obtain ⟨θs, cps, -, -, hI⟩ := H412 (Cκ / Real.sqrt 2) hC0' ρ hρ
  obtain ⟨W₂, HW₂⟩ := hI.entry (ν / 12) (4 * p) (by positivity) (by positivity)
  obtain ⟨Wρ, HWρ⟩ := Filter.eventually_atTop.1 (hρ.eventually_ge_atTop (max Cm 4))
  refine ⟨max (max W₁ W₂) (max ⌈8 * p⌉₊ (max 3 Wρ)), ?_⟩
  intro W hW g hg L hL1 hL2 E hE x
  obtain ⟨a, α⟩ := x
  -- the threshold `W ≥ W₀`
  have hW1' : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hW2' : W₂ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hW8 : ⌈8 * p⌉₊ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hW3 : 3 ≤ W :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hW
  have hWρ : Wρ ≤ W :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hW
  have hW8r : 8 * p ≤ (W : ℝ) := Nat.ceil_le.1 hW8
  have hW3r : (3 : ℝ) ≤ W := by exact_mod_cast hW3
  have hW0 : (0 : ℝ) < W := by linarith
  have hW1r : (1 : ℝ) ≤ W := by linarith
  have hlog : 1 ≤ Real.log W := large_one_le_log hW3
  have hρW : max Cm 4 ≤ ρ W := HWρ W hWρ
  have hρ0 : 0 ≤ ρ W := le_trans (le_trans (by norm_num) (le_max_right Cm 4)) hρW
  have hg2 : 2 ≤ g := hCκ2.trans hg
  have hg0 : 0 < g := by linarith
  have hgsq : 0 < g ^ 2 := by positivity
  -- `L ≥ max{C, 4} g²` from `ρ(W) ≥ max{C, 4}` and `log W ≥ 1`
  have hLlow : max Cm 4 * g ^ 2 ≤ (L : ℝ) :=
    calc max Cm 4 * g ^ 2 ≤ ρ W * g ^ 2 := mul_le_mul_of_nonneg_right hρW hgsq.le
      _ ≤ ρ W * g ^ 2 * Real.log W := le_mul_of_one_le_right (mul_nonneg hρ0 hgsq.le) hlog
      _ ≤ L := hL1
  have hLm : Cm * g ^ 2 ≤ (L : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hgsq.le) hLlow
  have hL4 : 4 * g ^ 2 ≤ (L : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hgsq.le) hLlow
  have hL1g : g ^ 2 ≤ (L : ℝ) := by linarith
  -- `δ_* = g² η_L` and `ζ_{t_*}(g̃) ≤ W^{-ν/3}`
  obtain ⟨hδlo, hδhi, hδ2, hδ3, hζ⟩ := Hb W hW1' g hg2 L hL1g
  set δ : ℝ := g ^ 2 * etaL W L g ν with hδ
  have hδ0 : 0 < δ := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) hδlo
  have hηL : etaL W L g ν = δ / g ^ 2 := by rw [hδ]; field_simp
  have hηL0 : 0 < etaL W L g ν := by rw [hηL]; positivity
  have ht0 : 0 < 1 - δ := by linarith
  -- the matching (A.75) [fo:eq:large-matching] at `t_* = 1 - δ_*`
  obtain ⟨E₀, hE₀, hroot, -, hCm1, hre, hlo, hhi, hmatch⟩ :=
    Hm g (hCκm.trans hg) L hLm (1 - δ) (by linarith) (by linarith) E hE
  rw [sub_sub_cancel] at hlo hhi
  set s : ℝ := Real.sqrt (1 - δ) * g with hs
  set m₀ : ℂ := mRoot s L E₀ with hm₀
  set z : ℂ := zChar s E₀ m₀ (1 - δ) with hz
  obtain ⟨ηE, hηE⟩ : ∃ η : ℝ, z.im = η := ⟨_, rfl⟩
  rw [hηE] at hlo hhi
  have hz' : z = (E : ℂ) + (ηE : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre, hηE]
  have hηE0 : 0 < ηE := lt_of_lt_of_le (by positivity) hlo
  have hsq : s ^ 2 = (1 - δ) * g ^ 2 := by rw [hs, mul_pow, Real.sq_sqrt ht0.le]
  have hs0 : 0 ≤ s := by positivity
  -- the point `(g̃, E₀, L, t_*)` of Theorem 5.12 [gc:thm:common](ii)
  set q : FlowPt := ⟨s, E₀, L, 1 - δ⟩ with hq
  have hsC : Cκ / Real.sqrt 2 ≤ s := by
    have hCκ0' : 0 ≤ Cκ := by linarith
    have h1 : (Cκ / Real.sqrt 2) ^ 2 ≤ s ^ 2 := by
      rw [div_pow, Real.sq_sqrt zero_le_two, hsq]
      have : Cκ ^ 2 ≤ g ^ 2 := pow_le_pow_left₀ hCκ0' hg 2
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) hs0 two_ne_zero).1 h1
  have hmem : q ∈ {p : FlowPt | ∃ q ∈ baseLarge κ (Cκ / Real.sqrt 2) 2 ρ W,
      zetaProp q.g W q.L q.u ≤ (W : ℝ) ^ (-(ν / 3)) ∧ 1 / 2 ≤ p.u ∧ p.u ≤ q.u ∧
      p = ⟨q.g, q.E, q.L, p.u⟩} := by
    refine ⟨q, ⟨hsC, hE₀, ?_, ?_, ?_, ?_⟩, hζ, ?_, le_rfl, rfl⟩
    · change ρ W * s ^ 2 * Real.log W ≤ L
      have hs2le : s ^ 2 ≤ g ^ 2 := by
        rw [hsq]; exact mul_le_of_le_one_left hgsq.le (by linarith)
      calc ρ W * s ^ 2 * Real.log W ≤ ρ W * g ^ 2 * Real.log W :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs2le hρ0) (by linarith)
        _ ≤ L := hL1
    · change (L : ℝ) ≤ 2 * s ^ 2 * (W : ℝ) ^ 2
      have e : 2 * ((1 - δ) * g ^ 2) * (W : ℝ) ^ 2 = (2 * (1 - δ)) * (g ^ 2 * (W : ℝ) ^ 2) := by
        ring
      rw [hsq, e]
      exact hL2.trans (le_mul_of_one_le_left (by positivity) (by linarith))
    · change (1 : ℝ) / 2 ≤ 1 - δ
      linarith
    · change (W : ℝ) ^ (-3 : ℝ) ≤ 1 - (1 - δ)
      rw [sub_sub_cancel]; exact hδ3
    · change (1 : ℝ) / 2 ≤ 1 - δ
      linarith
  have hS := HW₂ W hW2' q hmem
  -- the entry bound `W^{ν/12} ζ^{1/2} ≤ 1`
  have hζ1 : (W : ℝ) ^ (ν / 12) * Real.sqrt (flowZeta W q) ≤ 1 := by
    have hζ' : flowZeta W q ≤ (W : ℝ) ^ (-(ν / 3)) := hζ
    have h1 : Real.sqrt (flowZeta W q) ≤ (W : ℝ) ^ (-(ν / 12)) := by
      have he : (W : ℝ) ^ (-(ν / 12)) = Real.sqrt ((W : ℝ) ^ (-(ν / 6))) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hW0.le]
        congr 1; ring
      rw [he]
      exact Real.sqrt_le_sqrt (hζ'.trans (Real.rpow_le_rpow_of_exponent_le hW1r (by linarith)))
    calc (W : ℝ) ^ (ν / 12) * Real.sqrt (flowZeta W q)
        ≤ (W : ℝ) ^ (ν / 12) * (W : ℝ) ^ (-(ν / 12)) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hW0.le _)
      _ = 1 := by
          rw [Real.rpow_neg hW0.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hW0 _).ne']
  -- the resolvent and the Dyson matrix at the point
  have hG : ∀ ω : Ω W L, flowG W q ω = resolventMat (Hmat g W L ω) (E + ηE * Complex.I) := by
    intro ω
    change resolventMat (flowH s W L (1 - δ) ω) z = _
    rw [hmatch W ω, hz']
  have hL1' : 1 ≤ L := a.pos
  have hγ : 0 < gammaG s := by unfold gammaG; positivity
  have hM : flowM W q (a, α) (a, α) = m₀ := by
    change (dysonMat (hopB s) (gammaG s) L E₀ m₀ ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) (a, α) (a, α)
      = m₀
    have hw : 0 < ((E₀ : ℂ) + (gammaG s : ℂ) * m₀).im := by
      simpa using mul_pos hγ hroot.1
    rw [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, mul_one,
      dysonMat_diag _ _ L hL1' _ _ hw a]
    exact hroot.2.symm
  -- the seed moments at `η₀ = g^{-2}`
  obtain ⟨Z, hZ0, hYZ0, hZi, hZ⟩ := Hs W hW8r L g (hCκκ.trans hg) hL4 E hE (a, α)
  -- comparison of Poisson kernels: `η(E) ≍ η_L` and `η_L = δ_* η₀`
  have hmaxE : max (etaL W L g ν / ηE) (ηE / etaL W L g ν) ≤ K := by
    refine max_le ?_ ?_
    · refine le_trans ?_ (le_max_left _ _)
      rw [div_le_iff₀ hηE0, hηL]
      calc δ / g ^ 2 = 1 / c * (c * δ / g ^ 2) := by field_simp
        _ ≤ 1 / c * ηE := mul_le_mul_of_nonneg_left hlo (one_div_pos.2 hc).le
    · refine le_trans ?_ (le_max_right _ _)
      rw [div_le_iff₀ hηL0, hηL]
      calc ηE ≤ C₁ * δ / g ^ 2 := hhi
        _ = C₁ * (δ / g ^ 2) := by ring
  have hmax0 : max (etaL W L g ν / (1 / g ^ 2)) ((1 / g ^ 2) / etaL W L g ν) ≤ δ⁻¹ := by
    have e1 : etaL W L g ν / (1 / g ^ 2) = δ := by rw [hηL]; field_simp
    have e2 : (1 / g ^ 2) / etaL W L g ν = δ⁻¹ := by rw [hηL]; field_simp
    rw [e1, e2]
    refine max_le ?_ le_rfl
    have : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ0).2 (by linarith)
    linarith
  -- `Im G_xx(E + iη(E)) ≤ C` off the exceptional event of (5.51) [uvu:eq:terminal-law]
  have hYm : Measurable fun ω : Ω W L =>
      (resolventMat (Hmat g W L ω) (E + etaL W L g ν * Complex.I) (a, α) (a, α)).im :=
    (continuous_im_resolvent_Hmat g W L E hηL0.ne' (a, α)).measurable
  have hY0 : ∀ ω : Ω W L,
      0 ≤ (resolventMat (Hmat g W L ω) (E + etaL W L g ν * Complex.I) (a, α) (a, α)).im :=
    fun ω => (im_resolvent_bounds (Hmat_isHermitian g W L ω) E hηL0 (a, α)).1
  have hYZ : ∀ ω : Ω W L,
      (resolventMat (Hmat g W L ω) (E + etaL W L g ν * Complex.I) (a, α) (a, α)).im ≤
        δ⁻¹ * Z ω := by
    intro ω
    have hP := im_resolvent_height_le (Hmat_isHermitian g W L ω) E hηL0
      (by positivity : (0 : ℝ) < 1 / g ^ 2) (a, α)
    have h0 := (im_resolvent_bounds (Hmat_isHermitian g W L ω) E
      (by positivity : (0 : ℝ) < 1 / g ^ 2) (a, α)).1
    calc _ ≤ _ := hP
      _ ≤ δ⁻¹ * (resolventMat (Hmat g W L ω) (E + (1 / g ^ 2 : ℝ) * Complex.I) (a, α) (a, α)).im :=
          mul_le_mul_of_nonneg_right hmax0 h0
      _ ≤ δ⁻¹ * Z ω := mul_le_mul_of_nonneg_left (hYZ0 ω) (inv_nonneg.2 hδ0.le)
  have hZpow : ∀ ω, (δ⁻¹ * Z ω) ^ (2 * p) = δ⁻¹ ^ (2 * p) * Z ω ^ (2 * p) := fun ω =>
    Real.mul_rpow (inv_nonneg.2 hδ0.le) (hZ0 ω)
  have hZi' : Integrable (fun ω => (δ⁻¹ * Z ω) ^ (2 * p)) (μ W L) := by
    simp_rw [hZpow]; exact hZi.const_mul _
  have hZ' : ∫ ω, (δ⁻¹ * Z ω) ^ (2 * p) ∂(μ W L) ≤ δ⁻¹ ^ (2 * p) * Cs := by
    simp_rw [hZpow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hZ (Real.rpow_nonneg (inv_nonneg.2 hδ0.le) _)
  have hgood : ∀ ω ∉ {ω : Ω W L | ∃ l : (Fin L × Fin W) × (Fin L × Fin W),
      (W : ℝ) ^ (ν / 12) * Real.sqrt (flowZeta W q) < ‖(flowG W q ω - flowM W q) l.1 l.2‖},
      (resolventMat (Hmat g W L ω) (E + etaL W L g ν * Complex.I) (a, α) (a, α)).im ≤
        K * (C₁ + 1) := by
    intro ω hω
    have hl : ‖(flowG W q ω - flowM W q) (a, α) (a, α)‖ ≤ 1 :=
      le_trans (not_lt.1 fun h => hω ⟨((a, α), (a, α)), h⟩) hζ1
    rw [Matrix.sub_apply, hG ω, hM] at hl
    have h1 : (resolventMat (Hmat g W L ω) (E + ηE * Complex.I) (a, α) (a, α)).im ≤ C₁ + 1 := by
      have e1 := Complex.im_le_norm
        (resolventMat (Hmat g W L ω) (E + ηE * Complex.I) (a, α) (a, α) - m₀)
      have e2 := (Complex.im_le_norm m₀).trans hCm1
      rw [Complex.sub_im] at e1
      linarith
    have hP := im_resolvent_height_le (Hmat_isHermitian g W L ω) E hηL0 hηE0 (a, α)
    have h0 := (im_resolvent_bounds (Hmat_isHermitian g W L ω) E hηE0 (a, α)).1
    calc _ ≤ _ := hP
      _ ≤ K * (resolventMat (Hmat g W L ω) (E + ηE * Complex.I) (a, α) (a, α)).im :=
          mul_le_mul_of_nonneg_right hmaxE h0
      _ ≤ K * (C₁ + 1) := mul_le_mul_of_nonneg_left h1 hK0.le
  have hmain := moment_good_bad (P := μ W L) hYm hY0 hYZ hp hK1.le hZi' hZ' _ hS hgood
  refine ⟨hmain.1, hmain.2.trans ?_⟩
  -- the exceptional event: `δ^{-2p} W^{-4p} ≤ 1` since `δ ≥ W^{ν-2} ≥ W^{-2}`
  have hδW : δ⁻¹ ≤ (W : ℝ) ^ (2 : ℝ) := by
    have h1 : (W : ℝ) ^ (-2 : ℝ) ≤ δ :=
      (Real.rpow_le_rpow_of_exponent_le hW1r (by linarith)).trans hδlo
    have h2 := inv_anti₀ (Real.rpow_pos_of_pos hW0 _) h1
    rwa [Real.rpow_neg hW0.le, inv_inv] at h2
  have hAB : δ⁻¹ ^ (2 * p) * (W : ℝ) ^ (-(4 * p)) ≤ 1 := by
    have h1 : δ⁻¹ ^ (2 * p) ≤ (W : ℝ) ^ (2 * (2 * p)) := by
      rw [Real.rpow_mul hW0.le]
      exact Real.rpow_le_rpow (inv_nonneg.2 hδ0.le) hδW (by positivity)
    calc δ⁻¹ ^ (2 * p) * (W : ℝ) ^ (-(4 * p)) ≤ (W : ℝ) ^ (2 * (2 * p)) * (W : ℝ) ^ (-(4 * p)) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hW0.le _)
      _ = 1 := by
          rw [← Real.rpow_add hW0, show 2 * (2 * p) + -(4 * p) = 0 by ring, Real.rpow_zero]
  have hA0 : 0 ≤ δ⁻¹ ^ (2 * p) * Cs :=
    mul_nonneg (Real.rpow_nonneg (inv_nonneg.2 hδ0.le) _) hCs.le
  rw [← Real.sqrt_mul hA0]
  refine add_le_add le_rfl (Real.sqrt_le_sqrt ?_)
  calc δ⁻¹ ^ (2 * p) * Cs * (W : ℝ) ^ (-(4 * p)) = Cs * (δ⁻¹ ^ (2 * p) * (W : ℝ) ^ (-(4 * p))) := by
        ring
    _ ≤ Cs * 1 := mul_le_mul_of_nonneg_left hAB hCs.le
    _ = Cs := mul_one Cs

end LSBA
