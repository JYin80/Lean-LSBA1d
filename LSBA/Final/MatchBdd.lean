import LSBA.Final.Moments
import LSBA.Final.Terminal
import LSBA.Prop.Objects

/-!
# Terminal matching at bounded coupling

Lemma 5.14 [fo:lem:bounded-terminal-matching]: the terminal time, coupling and point (5.45)
[bl:eq:terminal], the parameter bounds (5.46) [fo:eq:bounded-terminal-parameters], the resolvent
identity in law (5.47) [fo:eq:bounded-terminal-resolvent], and the end budget (5.49)
[bl:eq:endbudget] `ζ_{t_*}(g_*) ≤ W^{-c₀}` used in the proof of Theorem 2.3 [thm:bounded-lower].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The terminal time `t_* = γ_g Im m / (γ_g Im m + η)`, `m = m_{g,L}(E + iη)`, of (5.45)
[bl:eq:terminal]. -/
def termTime (g : ℝ) (L : ℕ) (E η : ℝ) : ℝ :=
  gammaG g * (mDysonL g L (E + η * Complex.I)).im /
    (gammaG g * (mDysonL g L (E + η * Complex.I)).im + η)

/-- `c_* = (t_* γ_{g_*} / γ_g)^{1/2}` with `g_* = t_*^{1/2} g`, (5.45) [bl:eq:terminal]. -/
def termScale (g : ℝ) (L : ℕ) (E η : ℝ) : ℝ :=
  Real.sqrt (termTime g L E η * gammaG (Real.sqrt (termTime g L E η) * g) / gammaG g)

/-- The terminal point `(g_*, E_*, L, t_*)` of (5.45) [bl:eq:terminal], with
`E_* = c_*(E - η Re m / Im m)`. -/
def termPt (g : ℝ) (L : ℕ) (E η : ℝ) : FlowPt :=
  ⟨Real.sqrt (termTime g L E η) * g,
    termScale g L E η * (E - η * (mDysonL g L (E + η * Complex.I)).re /
      (mDysonL g L (E + η * Complex.I)).im),
    L, termTime g L E η⟩

private lemma matchBdd_max_pos (g : ℝ) : 0 < max 1 g :=
  lt_of_lt_of_le one_pos (le_max_left _ _)

private lemma matchBdd_gammaG_pos (g : ℝ) : 0 < gammaG g := by
  unfold gammaG
  have := matchBdd_max_pos g
  positivity

private lemma matchBdd_hopB_nonneg {g : ℝ} (hg : 0 ≤ g) : 0 ≤ hopB g :=
  div_nonneg hg (matchBdd_max_pos g).le

/-- Scaling `freeTL (c b) L (c w) = c⁻¹ freeTL b L w` for real `c ≠ 0`. -/
private lemma matchBdd_freeTL_scale (b : ℝ) (L : ℕ) (w : ℂ) {c : ℝ} (hc : c ≠ 0) :
    freeTL (c * b) L ((c : ℂ) * w) = (c : ℂ)⁻¹ * freeTL b L w := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  unfold freeTL
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : ((2 * (c * b) * Real.cos (2 * π * k / L) : ℝ) : ℂ) - c * w =
      (c : ℂ) * (((2 * b * Real.cos (2 * π * k / L) : ℝ) : ℂ) - w) := by
    push_cast; ring
  rw [e, mul_inv]
  ring

/-- The scale `c_*` as `t^{1/2} max{1,g} / max{1,t^{1/2} g}`. -/
private lemma matchBdd_scale_eq {t : ℝ} (g : ℝ) (ht : 0 ≤ t) :
    Real.sqrt (t * gammaG (Real.sqrt t * g) / gammaG g) =
      Real.sqrt t * (max 1 g / max 1 (Real.sqrt t * g)) := by
  have h1 := matchBdd_max_pos g
  have h2 := matchBdd_max_pos (Real.sqrt t * g)
  have h : t * gammaG (Real.sqrt t * g) / gammaG g =
      t * (max 1 g / max 1 (Real.sqrt t * g)) ^ 2 := by
    unfold gammaG
    field_simp
  rw [h, Real.sqrt_mul ht, Real.sqrt_sq (by positivity)]

/-- The bounds on `c_*`, the hopping and variance relations of the matching. -/
private lemma matchBdd_scale_facts {g t c : ℝ} (hg : 0 ≤ g) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hc : c = Real.sqrt (t * gammaG (Real.sqrt t * g) / gammaG g)) :
    0 < c ∧ Real.sqrt t ≤ c ∧ c ≤ 1 ∧ hopB (Real.sqrt t * g) = c * hopB g ∧
      t * gammaG (Real.sqrt t * g) = c ^ 2 * gammaG g := by
  rw [matchBdd_scale_eq g ht0.le] at hc
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hs1 : Real.sqrt t ≤ 1 := by
    simpa using Real.sqrt_le_sqrt ht1
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
  have h1 := matchBdd_max_pos g
  have h2 := matchBdd_max_pos (Real.sqrt t * g)
  have hM'M : max 1 (Real.sqrt t * g) ≤ max 1 g :=
    max_le (le_max_left _ _) ((mul_le_of_le_one_left hg hs1).trans (le_max_right _ _))
  have hsM : Real.sqrt t * max 1 g ≤ max 1 (Real.sqrt t * g) := by
    calc Real.sqrt t * max 1 g = max (Real.sqrt t * 1) (Real.sqrt t * g) :=
          mul_max_of_nonneg _ _ hs0.le
      _ ≤ max 1 (Real.sqrt t * g) := max_le_max (by simpa using hs1) le_rfl
  have hr : 1 ≤ max 1 g / max 1 (Real.sqrt t * g) := (one_le_div h2).2 hM'M
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hc]; positivity
  · rw [hc]; exact le_mul_of_one_le_right hs0.le hr
  · rw [hc, ← mul_div_assoc, div_le_one h2]; exact hsM
  · rw [hc]; unfold hopB; field_simp
  · rw [hc]; unfold gammaG; rw [mul_pow, div_pow, hsq]; field_simp

/-- The characteristic at the terminal point is `c (E + iη)`: (5.45) [bl:eq:terminal] with
`m = Re m + i y`. -/
private lemma matchBdd_zChar_eq {c t γ γ' y r E η : ℝ} (hc : 0 < c) (ht : 0 < t) (hy : 0 < y)
    (h1 : t * γ' = c ^ 2 * γ) (h2 : (1 - t) * (γ * y) = t * η) (m : ℂ)
    (hm : m = (r : ℂ) + (y : ℂ) * Complex.I) :
    ((c * (E - η * r / y) : ℝ) : ℂ) + (((1 - t) * γ' : ℝ) : ℂ) * (m / (c : ℂ)) =
      (c : ℂ) * ((E : ℂ) + (η : ℂ) * Complex.I) := by
  have h3 : (1 - t) * γ' * y = c ^ 2 * η := by
    have : t * ((1 - t) * γ' * y - c ^ 2 * η) = 0 := by
      linear_combination (1 - t) * y * h1 + c ^ 2 * h2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h ht.ne'
    · linarith
  have h3c : (((1 - t) * γ' : ℝ) : ℂ) * (y : ℂ) = (c : ℂ) ^ 2 * (η : ℂ) := by
    exact_mod_cast h3
  have hcc : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  subst hm
  push_cast at h3c ⊢
  field_simp
  linear_combination (↑r + ↑y * Complex.I) * h3c

/-- Transfer of a root of (5.2) [fo:eq:dyson-family] under the scaling of the matching. -/
private lemma matchBdd_root_scale (L : ℕ) {b b' c : ℝ} (hc : 0 < c) (hb : b' = c * b)
    (β β' : ℝ) (z m w : ℂ) (hm : m = freeTL b L (z + β * m))
    (hw : w + β' * (m / c) = c * (z + β * m)) :
    m / c = freeTL b' L (w + β' * (m / c)) := by
  have hcc : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  rw [hw, hb, matchBdd_freeTL_scale b L _ hc.ne', ← hm]
  field_simp

/-- `resolventMat (c H) (c z) = c⁻¹ resolventMat H z` for a Hermitian `H`, `Im z ≠ 0`, `c > 0`. -/
private lemma matchBdd_resolvent_smul {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) {c : ℝ} (hc : 0 < c) :
    resolventMat ((c : ℂ) • H) ((c : ℂ) * z) = (c : ℂ)⁻¹ • resolventMat H z := by
  have hcc : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  unfold resolventMat
  refine Matrix.inv_eq_right_inv ?_
  have h1 := sub_smul_mul_resolventMat hH hz
  unfold resolventMat at h1
  have e : (c : ℂ) • H - ((c : ℂ) * z) • (1 : Matrix n n ℂ) =
      (c : ℂ) • (H - z • (1 : Matrix n n ℂ)) := by
    rw [smul_sub, mul_smul]
  rw [e, smul_mul_smul_comm, h1, mul_inv_cancel₀ hcc, one_smul]

/-- Lemma 5.14 [fo:lem:bounded-terminal-matching]: the parameters (5.46)
[fo:eq:bounded-terminal-parameters], with `η/2 ≤ 1 - t_* ≤ Kη` and `t_*^{1/2} ≤ c_* ≤ 1`, the anchor
`m_{g_*,L}(E_*) = m/c_*`, and (5.47) [fo:eq:bounded-terminal-resolvent] for every sample:
`G(E + iη) = c_* G_{t_*}(g_*, E_*)`. -/
theorem terminal_match_bdd (C κ : ℝ) (hC : 0 < C) (hκ : 0 < κ ∧ κ < 1 / 2) :
    ∃ B c' η₀ K : ℝ, ∃ L₀ : ℕ, 0 < B ∧ 0 < c' ∧ 0 < η₀ ∧ 0 < K ∧ 3 ≤ L₀ ∧
      ∀ g : ℝ, 0 ≤ g → g ≤ C → ∀ L : ℕ, L₀ ≤ L → ∀ E : ℝ, κ ≤ Fdist g (-|E|) →
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
        1 / 2 ≤ (termPt g L E η).u ∧ η / 2 ≤ 1 - (termPt g L E η).u ∧
        1 - (termPt g L E η).u ≤ K * η ∧
        Real.sqrt (termPt g L E η).u ≤ termScale g L E η ∧ termScale g L E η ≤ 1 ∧
        RegBdd C B c' L (termPt g L E η).g (termPt g L E η).E ∧
        mRoot (termPt g L E η).g L (termPt g L E η).E =
          mDysonL g L (E + η * Complex.I) / (termScale g L E η : ℂ) ∧
        ∀ (W : ℕ) (ω : Ω W L), resolventMat (Hmat g W L ω) (E + η * Complex.I) =
          (termScale g L E η : ℂ) • flowG W (termPt g L E η) ω := by
  obtain ⟨C', c₁, L₁, hC', hc₁, hL₁, H⟩ := terminal_bdd_regular C κ hC hκ
  set M : ℝ := max 1 C with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0 : 0 < M := by linarith
  refine ⟨C' + M / c₁, c₁, min 1 (c₁ / M ^ 2), M ^ 2 / c₁, L₁, by positivity, hc₁,
    lt_min one_pos (by positivity), by positivity, hL₁, ?_⟩
  intro g hg hgC L hL E hE η hη hηη₀
  have hL3 : 3 ≤ L := hL₁.trans hL
  obtain ⟨hEC, -, -, -, hIm⟩ := H g hg hgC L hL E hE
  have hη1 : η ≤ 1 := hηη₀.trans (min_le_left _ _)
  have hηc : η ≤ c₁ / M ^ 2 := hηη₀.trans (min_le_right _ _)
  have hzim : 0 < ((E : ℂ) + η * Complex.I).im := by simpa using hη
  have hy : c₁ ≤ (mDysonL g L ((E : ℂ) + η * Complex.I)).im := hIm η hη hη1
  have hnorm : ‖mDysonL g L ((E : ℂ) + η * Complex.I)‖ ≤ max 1 g :=
    mDysonL_norm_le_max g hg L (by omega) _ hzim
  have hmeq := (mDysonL_spec g hg L (by omega) _ hzim).2
  set z : ℂ := (E : ℂ) + η * Complex.I with hz
  set m : ℂ := mDysonL g L z with hm
  have hy_pos : 0 < m.im := lt_of_lt_of_le hc₁ hy
  have hMg : max 1 g ≤ M := max_le_max le_rfl hgC
  have hMg1 : 1 ≤ max 1 g := le_max_left _ _
  have hγdef : gammaG g = ((max 1 g) ^ 2)⁻¹ := rfl
  have hγpos := matchBdd_gammaG_pos g
  have hγM : (M ^ 2)⁻¹ ≤ gammaG g := by
    rw [hγdef]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hMg 2)
  have hγy1 : gammaG g * m.im ≤ 1 := by
    calc gammaG g * m.im ≤ gammaG g * max 1 g := by
          gcongr; exact (Complex.im_le_norm m).trans hnorm
      _ = (max 1 g)⁻¹ := by rw [hγdef]; field_simp
      _ ≤ 1 := inv_le_one_of_one_le₀ hMg1
  have hγy2 : c₁ / M ^ 2 ≤ gammaG g * m.im := by
    calc c₁ / M ^ 2 = (M ^ 2)⁻¹ * c₁ := by rw [div_eq_inv_mul]
      _ ≤ gammaG g * m.im := mul_le_mul hγM hy hc₁.le hγpos.le
  have hYpos : 0 < gammaG g * m.im := lt_of_lt_of_le (by positivity) hγy2
  have hηY : η ≤ gammaG g * m.im := hηc.trans hγy2
  have ht_def : termTime g L E η = gammaG g * m.im / (gammaG g * m.im + η) := rfl
  set t := termTime g L E η with ht
  have ht_pos : 0 < t := by rw [ht_def]; positivity
  have h1t : 1 - t = η / (gammaG g * m.im + η) := by
    rw [ht_def]; field_simp; ring
  have hden : 0 < gammaG g * m.im + η := by positivity
  have ht_lt : t < 1 := by
    have : 0 < 1 - t := by rw [h1t]; positivity
    linarith
  have ht_half : 1 / 2 ≤ t := by
    rw [ht_def, le_div_iff₀ hden]; linarith
  have h_low : η / 2 ≤ 1 - t := by
    rw [h1t]
    exact div_le_div_of_nonneg_left hη.le hden (by linarith)
  have h_up : 1 - t ≤ M ^ 2 / c₁ * η := by
    rw [h1t]
    calc η / (gammaG g * m.im + η) ≤ η / (c₁ / M ^ 2) :=
          div_le_div_of_nonneg_left hη.le (by positivity) (by linarith)
      _ = M ^ 2 / c₁ * η := by field_simp
  have h_key : (1 - t) * (gammaG g * m.im) = t * η := by
    rw [h1t, ht_def]; field_simp
  obtain ⟨hc_pos, hsc, hc1, hb, hγt⟩ := matchBdd_scale_facts (g := g) (t := t) hg ht_pos
    ht_lt.le (c := termScale g L E η) rfl
  set c := termScale g L E η with hcdef
  have hcc : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc_pos.ne'
  have hs1 : Real.sqrt t ≤ 1 := by simpa using Real.sqrt_le_sqrt ht_lt.le
  have hzchar : zChar (termPt g L E η).g (termPt g L E η).E (m / (c : ℂ)) (termPt g L E η).u =
      (c : ℂ) * z :=
    matchBdd_zChar_eq hc_pos ht_pos hy_pos hγt h_key m (Complex.re_add_im m).symm
  have hw : ((termPt g L E η).E : ℂ) + (gammaG (termPt g L E η).g : ℂ) * (m / (c : ℂ)) =
      (c : ℂ) * (z + (gammaG g : ℂ) * m) := by
    have hz' := hzchar
    unfold zChar at hz'
    have hγtc : (t : ℂ) * (gammaG (Real.sqrt t * g) : ℂ) = (c : ℂ) ^ 2 * (gammaG g : ℂ) := by
      exact_mod_cast hγt
    change ((termPt g L E η).E : ℂ) + (((1 - t) * gammaG (Real.sqrt t * g) : ℝ) : ℂ) * (m / (c : ℂ))
      = (c : ℂ) * z at hz'
    change ((termPt g L E η).E : ℂ) + (gammaG (Real.sqrt t * g) : ℂ) * (m / (c : ℂ)) = _
    push_cast at hz' ⊢
    field_simp at hz' ⊢
    linear_combination hz' + m * hγtc
  have hroot : IsDysonRootV (hopB (termPt g L E η).g) (gammaG (termPt g L E η).g) L
      (termPt g L E η).E (m / (c : ℂ)) := by
    refine ⟨?_, ?_⟩
    · rw [Complex.div_ofReal_im]; exact div_pos hy_pos hc_pos
    · exact matchBdd_root_scale L hc_pos hb (gammaG g) _ z m _ hmeq hw
  have hmroot : mRoot (termPt g L E η).g L (termPt g L E η).E = m / (c : ℂ) :=
    (mRootV_spec (hopB (Real.sqrt t * g)) (gammaG (Real.sqrt t * g))
      (matchBdd_hopB_nonneg (mul_nonneg (Real.sqrt_nonneg _) hg)) (matchBdd_gammaG_pos _) L hL3
      _ (by simp)).2 _ hroot
  have hre : |m.re| ≤ M := (Complex.abs_re_le_norm m).trans (hnorm.trans hMg)
  have hterm : |η * m.re / m.im| ≤ M / c₁ := by
    rw [abs_div, abs_mul, abs_of_pos hη, abs_of_pos hy_pos]
    calc η * |m.re| / m.im ≤ 1 * M / c₁ := by gcongr
      _ = M / c₁ := by rw [one_mul]
  have hEstar : |(termPt g L E η).E| ≤ C' + M / c₁ := by
    change |c * (E - η * m.re / m.im)| ≤ C' + M / c₁
    rw [abs_mul, abs_of_pos hc_pos]
    calc c * |E - η * m.re / m.im| ≤ 1 * (|E| + |η * m.re / m.im|) :=
          mul_le_mul hc1 (abs_sub _ _) (abs_nonneg _) zero_le_one
      _ ≤ C' + M / c₁ := by rw [one_mul]; exact add_le_add hEC hterm
  have hgs_nonneg : 0 ≤ (termPt g L E η).g := mul_nonneg (Real.sqrt_nonneg _) hg
  have hgs_le : (termPt g L E η).g ≤ g := mul_le_of_le_one_left hg hs1
  have himstar : c₁ ≤ (mRoot (termPt g L E η).g L (termPt g L E η).E).im := by
    rw [hmroot, Complex.div_ofReal_im]
    exact hy.trans (le_div_self hy_pos.le hc_pos hc1)
  refine ⟨ht_half, h_low, h_up, hsc, hc1, ⟨hgs_nonneg, hgs_le.trans hgC, hEstar, ?_, himstar⟩,
    hmroot, ?_⟩
  · rw [hmroot]; exact hroot
  · intro W ω
    have hA : Ag (termPt g L E η).g L = (c : ℂ) • Ag g L := by
      change ((hopB (Real.sqrt t * g) : ℝ) : ℂ) • cycleAdj L =
        (c : ℂ) • ((hopB g : ℝ) : ℂ) • cycleAdj L
      rw [hb, ← smul_assoc]
      push_cast
      rfl
    have hH : flowH (termPt g L E η).g W L (termPt g L E η).u ω = (c : ℂ) • Hmat g W L ω := by
      rw [← flowH_one g W L ω]
      refine flowH_scaling g (termPt g L E η).g W L hc_pos.le zero_le_one hA ?_ ω
      change t * gammaG (Real.sqrt t * g) = c ^ 2 * (1 * gammaG g)
      rw [one_mul]; exact hγt
    have hflow : flowG W (termPt g L E η) ω =
        resolventMat ((c : ℂ) • Hmat g W L ω) ((c : ℂ) * z) := by
      change resolventMat (flowH (termPt g L E η).g W L (termPt g L E η).u ω)
        (zChar (termPt g L E η).g (termPt g L E η).E (mRoot (termPt g L E η).g L
          (termPt g L E η).E) (termPt g L E η).u) = _
      rw [hH, hmroot, hzchar]
    rw [hflow, matchBdd_resolvent_smul (Hmat_isHermitian g W L ω) (by simpa [hz] using hη.ne')
      hc_pos]
    exact (smul_inv_smul₀ hcc _).symm

/-- Lower bound for the denominator of `ζ_t(g')` of (5.18) [fo:eq:scale] at the terminal point:
the two regimes `ℓ_t = L` and `ℓ_t = 1 + g'/√(γ'(1-t))`, in terms of `u = W^{ν/6}`. -/
private lemma matchBdd_zeta_core {W L : ℕ} {g' t γ' η u M : ℝ} (hW : 0 < (W : ℝ))
    (hg' : 0 ≤ g') (ht : t < 1) (hγ : 0 < γ') (hM : 1 ≤ M) (hu : 3 * M ≤ u)
    (hP : η / (2 * M ^ 2) ≤ (1 - t) * γ')
    (hA : u ^ 6 ≤ (W : ℝ) * L * η) (hB : u ^ 6 ≤ (W : ℝ) ^ 2 * (2 * g') ^ 2 * η) :
    u ^ 2 ≤ (W : ℝ) * min (L : ℝ) (1 + g' / Real.sqrt (γ' * (1 - t))) * (1 - t) * γ' := by
  have h1t : 0 < 1 - t := by linarith
  have hγt : 0 < γ' * (1 - t) := mul_pos hγ h1t
  have hP0 : 0 < (1 - t) * γ' := mul_pos h1t hγ
  have hs : 0 < Real.sqrt (γ' * (1 - t)) := Real.sqrt_pos.2 hγt
  have hs2 : Real.sqrt (γ' * (1 - t)) ^ 2 = (1 - t) * γ' := by
    rw [Real.sq_sqrt hγt.le]; ring
  set s := Real.sqrt (γ' * (1 - t)) with hsdef
  set P := (1 - t) * γ' with hPdef
  have hu3 : 3 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hM2 : 1 ≤ M ^ 2 := one_le_pow₀ hM
  have hu2 : 9 * M ^ 2 ≤ u ^ 2 := by nlinarith
  have hM0 : 0 < 2 * M ^ 2 := by positivity
  have hLW : (0 : ℝ) ≤ (W : ℝ) * L := by positivity
  have hPη : η ≤ 2 * M ^ 2 * P := by
    rw [div_le_iff₀ hM0] at hP; linarith
  have hT1 : u ^ 2 ≤ (W : ℝ) * L * P := by
    have h4 : 2 * M ^ 2 ≤ u ^ 4 := by nlinarith [pow_pos hu0 2]
    have e1 : u ^ 2 * (2 * M ^ 2) ≤ (W : ℝ) * L * η :=
      calc u ^ 2 * (2 * M ^ 2) ≤ u ^ 2 * u ^ 4 := by gcongr
        _ = u ^ 6 := by ring
        _ ≤ _ := hA
    have e2 : (W : ℝ) * L * η ≤ (W : ℝ) * L * (2 * M ^ 2 * P) := by gcongr
    have e3 : u ^ 2 * (2 * M ^ 2) ≤ (W : ℝ) * L * P * (2 * M ^ 2) := by nlinarith
    exact le_of_mul_le_mul_right e3 hM0
  have hT2 : u ^ 2 ≤ (W : ℝ) * g' * s := by
    have hX : 0 ≤ (W : ℝ) ^ 2 * g' ^ 2 := by positivity
    have hXη : (W : ℝ) ^ 2 * g' ^ 2 * η ≤ 2 * M ^ 2 * ((W : ℝ) ^ 2 * g' ^ 2 * P) :=
      calc (W : ℝ) ^ 2 * g' ^ 2 * η ≤ (W : ℝ) ^ 2 * g' ^ 2 * (2 * M ^ 2 * P) := by gcongr
        _ = _ := by ring
    have h6 : u ^ 6 ≤ 4 * ((W : ℝ) ^ 2 * g' ^ 2 * η) := by nlinarith [hB]
    have h7 : 8 * M ^ 2 * u ^ 4 ≤ u ^ 6 := by nlinarith [pow_pos hu0 4]
    have h8 : 8 * M ^ 2 * u ^ 4 ≤ 8 * M ^ 2 * ((W : ℝ) ^ 2 * g' ^ 2 * P) := by nlinarith
    have h9 : u ^ 4 ≤ (W : ℝ) ^ 2 * g' ^ 2 * P :=
      le_of_mul_le_mul_left h8 (by positivity)
    have hsq : (u ^ 2) ^ 2 ≤ ((W : ℝ) * g' * s) ^ 2 := by
      have : ((W : ℝ) * g' * s) ^ 2 = (W : ℝ) ^ 2 * g' ^ 2 * P := by
        rw [mul_pow, mul_pow, hs2]
      rw [this, ← pow_mul]; exact h9
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq
  rcases le_total (L : ℝ) (1 + g' / s) with h | h
  · rw [min_eq_left h]
    calc u ^ 2 ≤ (W : ℝ) * L * P := hT1
      _ = _ := by ring
  · rw [min_eq_right h]
    calc u ^ 2 ≤ (W : ℝ) * g' * s := hT2
      _ = (W : ℝ) * (g' / s) * P := by rw [← hs2]; field_simp
      _ ≤ (W : ℝ) * (1 + g' / s) * P := by gcongr; linarith
      _ = _ := by ring

/-- The end budget (5.49) [bl:eq:endbudget] at `η = η_L` ((5.48) [fo:eq:proof-parameters],
`c₀ = ν/3`): `ζ_{t_*}(g_*) ≤ W^{-ν/3}` and `1 - t_* ≥ W^{-3}`, for `W^{-1/2} ≤ g ≤ C`. -/
theorem endBudget_bdd (C κ ν : ℝ) (hC : 0 < C) (hκ : 0 < κ ∧ κ < 1 / 2) (hν : 0 < ν ∧ ν < 1) :
    ∃ L₀ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, L₀ ≤ L → ∀ g : ℝ, (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ g →
      g ≤ C → ∀ E : ℝ, κ ≤ Fdist g (-|E|) →
        zetaProp (termPt g L E (etaL W L g ν)).g W L (termPt g L E (etaL W L g ν)).u ≤
          (W : ℝ) ^ (-(ν / 3)) ∧
        (W : ℝ) ^ (-3 : ℝ) ≤ 1 - (termPt g L E (etaL W L g ν)).u := by
  obtain ⟨B, c', η₀, K, L₀, hB, hc', hη₀, hK, hL₀, H⟩ := terminal_match_bdd C κ hC hκ
  set M : ℝ := max 1 C with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hν0 := hν.1
  have hev : ∀ᶠ W : ℕ in atTop, 1 ≤ W ∧ η₀⁻¹ ≤ (W : ℝ) ^ (1 - ν) ∧
      3 * M ≤ (W : ℝ) ^ (ν / 6) ∧ 2 * M ^ 2 ≤ (W : ℝ) := by
    have hlim : ∀ y : ℝ, 0 < y → ∀ a : ℝ, ∀ᶠ W : ℕ in atTop, a ≤ (W : ℝ) ^ y := fun y hy a =>
      ((tendsto_rpow_atTop hy).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop a
    refine (eventually_ge_atTop 1).and ((hlim _ (by linarith [hν.2]) _).and
      ((hlim _ (by positivity) _).and ?_))
    exact tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.1 hev
  refine ⟨L₀, W₀, ?_⟩
  intro W hW L hL g hgW hgC E hE
  obtain ⟨hW1, hW2, hW3, hW4⟩ := hW₀ W hW
  have hWr1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWr0 : (0 : ℝ) < W := by linarith
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL₀.trans hL
  have hg0 : 0 ≤ g := (Real.rpow_nonneg hWr0.le _).trans hgW
  have hW2g : (W : ℝ) ≤ (W : ℝ) ^ 2 * g ^ 2 := by
    have h1 : ((W : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (W : ℝ)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hWr0.le]
      norm_num [Real.rpow_neg_one]
    have h2 : (W : ℝ)⁻¹ ≤ g ^ 2 :=
      h1 ▸ pow_le_pow_left₀ (Real.rpow_nonneg hWr0.le _) hgW 2
    calc (W : ℝ) = (W : ℝ) ^ 2 * (W : ℝ)⁻¹ := by field_simp
      _ ≤ _ := by gcongr
  have hℓdef : ellStar W L g = min ((W : ℝ) * L) (max (W : ℝ) ((W : ℝ) ^ 2 * g ^ 2)) := rfl
  set ℓ := ellStar W L g with hℓ
  have hℓ_ge : (W : ℝ) ≤ ℓ := by
    rw [hℓdef]
    exact le_min (le_mul_of_one_le_right hWr0.le (by linarith)) (le_max_left _ _)
  have hℓ_le1 : ℓ ≤ (W : ℝ) * L := by rw [hℓdef]; exact min_le_left _ _
  have hℓ_le2 : ℓ ≤ (W : ℝ) ^ 2 * g ^ 2 := by
    rw [hℓdef]; exact (min_le_right _ _).trans (max_le hW2g le_rfl)
  have hM2 : 1 ≤ M ^ 2 := one_le_pow₀ hM1
  have hℓ_le3 : ℓ ≤ M ^ 2 * (W : ℝ) ^ 2 := by
    rw [hℓdef]
    refine (min_le_right _ _).trans (max_le ?_ ?_)
    · calc (W : ℝ) ≤ (W : ℝ) ^ 2 := le_self_pow₀ hWr1 two_ne_zero
        _ ≤ M ^ 2 * (W : ℝ) ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hM2
    · have hgM : g ≤ M := hgC.trans (le_max_right _ _)
      calc (W : ℝ) ^ 2 * g ^ 2 ≤ (W : ℝ) ^ 2 * M ^ 2 := by
            gcongr
        _ = M ^ 2 * (W : ℝ) ^ 2 := mul_comm _ _
  have hV0 : 0 < (W : ℝ) ^ ν := Real.rpow_pos_of_pos hWr0 ν
  have hV1 : 1 ≤ (W : ℝ) ^ ν := Real.one_le_rpow hWr1 hν0.le
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le hWr0 hℓ_ge
  have hηdef : etaL W L g ν = (W : ℝ) ^ ν / ℓ := rfl
  set η := etaL W L g ν with hη
  have hη0 : 0 < η := div_pos hV0 hℓ0
  have hηη₀ : η ≤ η₀ := by
    rw [hηdef, div_le_iff₀ hℓ0]
    have hWe : (W : ℝ) = (W : ℝ) ^ ν * (W : ℝ) ^ (1 - ν) := by
      rw [← Real.rpow_add hWr0]; simp
    have h1 : 1 ≤ η₀ * (W : ℝ) ^ (1 - ν) := by
      have := mul_le_mul_of_nonneg_left hW2 hη₀.le
      rwa [mul_inv_cancel₀ hη₀.ne'] at this
    have h2 : (W : ℝ) ^ ν ≤ η₀ * (W : ℝ) := by
      calc (W : ℝ) ^ ν = (W : ℝ) ^ ν * 1 := (mul_one _).symm
        _ ≤ (W : ℝ) ^ ν * (η₀ * (W : ℝ) ^ (1 - ν)) := by gcongr
        _ = η₀ * ((W : ℝ) ^ ν * (W : ℝ) ^ (1 - ν)) := by ring
        _ = η₀ * (W : ℝ) := by rw [← hWe]
    calc (W : ℝ) ^ ν ≤ η₀ * (W : ℝ) := h2
      _ ≤ η₀ * ℓ := by gcongr
  obtain ⟨ht_half, h_low, -, -, -, -, -, -⟩ := H g hg0 hgC L hL E hE η hη0 hηη₀
  set p := termPt g L E η with hp
  have hgs : p.g = Real.sqrt p.u * g := rfl
  have hu_lt : p.u < 1 := by linarith
  have hsqrt : 1 / 2 ≤ Real.sqrt p.u := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hs1 : Real.sqrt p.u ≤ 1 := by simpa using Real.sqrt_le_sqrt hu_lt.le
  have hg'_ge : g / 2 ≤ p.g := by
    rw [hgs]
    calc g / 2 = 1 / 2 * g := by ring
      _ ≤ Real.sqrt p.u * g := mul_le_mul_of_nonneg_right hsqrt hg0
  have hg'_le : p.g ≤ g := by rw [hgs]; exact mul_le_of_le_one_left hg0 hs1
  have hg'_0 : 0 ≤ p.g := by rw [hgs]; exact mul_nonneg (Real.sqrt_nonneg _) hg0
  have hγ' : (M ^ 2)⁻¹ ≤ gammaG p.g := by
    unfold gammaG
    exact inv_anti₀ (by positivity)
      (pow_le_pow_left₀ (by positivity) (max_le_max le_rfl (hg'_le.trans hgC)) 2)
  have hP : η / (2 * M ^ 2) ≤ (1 - p.u) * gammaG p.g :=
    calc η / (2 * M ^ 2) = η / 2 * (M ^ 2)⁻¹ := by field_simp
      _ ≤ (1 - p.u) * gammaG p.g := mul_le_mul h_low hγ' (by positivity) (by linarith)
  set r : ℝ := (W : ℝ) ^ (ν / 6) with hr
  have hrpow : ∀ n : ℕ, r ^ n = (W : ℝ) ^ (ν / 6 * n) := fun n => by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hWr0.le]
  have hr2 : r ^ 2 = (W : ℝ) ^ (ν / 3) := by rw [hrpow]; congr 1; push_cast; ring
  have hr6 : r ^ 6 = (W : ℝ) ^ ν := by rw [hrpow]; congr 1; push_cast; ring
  have hA : r ^ 6 ≤ (W : ℝ) * L * η := by
    rw [hr6, hηdef, mul_div_assoc', le_div_iff₀ hℓ0]
    calc (W : ℝ) ^ ν * ℓ ≤ (W : ℝ) ^ ν * ((W : ℝ) * L) :=
          mul_le_mul_of_nonneg_left hℓ_le1 hV0.le
      _ = _ := by ring
  have hB : r ^ 6 ≤ (W : ℝ) ^ 2 * (2 * p.g) ^ 2 * η := by
    have h1 : g ^ 2 ≤ (2 * p.g) ^ 2 := pow_le_pow_left₀ hg0 (by linarith) 2
    have h2 : (W : ℝ) ^ ν ≤ (W : ℝ) ^ 2 * g ^ 2 * η := by
      rw [hηdef, mul_div_assoc', le_div_iff₀ hℓ0]
      calc (W : ℝ) ^ ν * ℓ ≤ (W : ℝ) ^ ν * ((W : ℝ) ^ 2 * g ^ 2) :=
            mul_le_mul_of_nonneg_left hℓ_le2 hV0.le
        _ = _ := by ring
    rw [hr6]
    calc (W : ℝ) ^ ν ≤ (W : ℝ) ^ 2 * g ^ 2 * η := h2
      _ ≤ (W : ℝ) ^ 2 * (2 * p.g) ^ 2 * η := by gcongr
  have hcore := matchBdd_zeta_core (W := W) (L := L) hWr0 hg'_0 hu_lt
    (matchBdd_gammaG_pos p.g) hM1 hW3 hP hA hB
  refine ⟨?_, ?_⟩
  · unfold zetaProp ellProp
    rw [Real.rpow_neg hWr0.le, ← hr2]
    exact inv_anti₀ (by positivity) hcore
  · have hkey : 2 * ℓ ≤ (W : ℝ) ^ ν * (W : ℝ) ^ 3 := by
      have h1 : 2 * M ^ 2 * (W : ℝ) ^ 2 ≤ (W : ℝ) * (W : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hW4 (by positivity)
      have h2 : (W : ℝ) * (W : ℝ) ^ 2 ≤ (W : ℝ) ^ ν * (W : ℝ) ^ 3 := by
        calc (W : ℝ) * (W : ℝ) ^ 2 = 1 * (W : ℝ) ^ 3 := by ring
          _ ≤ _ := by gcongr
      linarith
    have h3 : (W : ℝ) ^ (-3 : ℝ) = ((W : ℝ) ^ 3)⁻¹ := by
      rw [Real.rpow_neg hWr0.le]
      norm_cast
    have h4 : ((W : ℝ) ^ 3)⁻¹ ≤ η / 2 := by
      rw [hηdef, inv_eq_one_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    rw [h3]
    linarith

end LSBA
