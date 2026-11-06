import LSBA.Small.Propagation
import LSBA.Dyson.Regular
import LSBA.Final.MatchBdd

/-!
# Resolvent moments at small coupling

The moment bound in the form of Theorem 2.3 [thm:bounded-lower] on `W^{-1/2} ≤ g ≤ C` with an
`F_g`-window, from the propagation at small coupling, the terminal matching of Lemma 5.14
[fo:lem:bounded-terminal-matching] and the end budget (5.49) [bl:eq:endbudget].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- `W ≤ ℓ_{W,g,L} ≤ max{1, C}² W²`, (1.7) [eq:scales], for `W ≥ 1`, `L ≥ 1` and `0 ≤ g ≤ C`. -/
private lemma lower_ellStar_bounds {W L : ℕ} {g C : ℝ} (hW : (1 : ℝ) ≤ W) (hL : 1 ≤ L)
    (hg : 0 ≤ g) (hgC : g ≤ C) :
    (W : ℝ) ≤ ellStar W L g ∧ ellStar W L g ≤ (max 1 C) ^ 2 * (W : ℝ) ^ 2 := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hM : 1 ≤ max 1 C := le_max_left _ _
  have hgM : g ^ 2 ≤ (max 1 C) ^ 2 := pow_le_pow_left₀ hg (hgC.trans (le_max_right _ _)) 2
  have hM2 : 1 ≤ (max 1 C) ^ 2 := one_le_pow₀ hM
  have hW2 : (W : ℝ) ≤ (W : ℝ) ^ 2 := by nlinarith
  unfold ellStar ellScale
  refine ⟨le_min (by nlinarith) (le_max_left _ _), (min_le_right _ _).trans (max_le ?_ ?_)⟩
  · nlinarith
  · nlinarith [sq_nonneg (W : ℝ)]

/-- The diagonal of the deterministic matrix `M_B(g, E) ⊗ I_W` of (5.3) [fo:eq:characteristic]
at a point whose anchor is a root of (5.2) [fo:eq:dyson-family] is the anchor `m`. -/
private lemma lower_flowM_diag (W : ℕ) (q : FlowPt) (hL : 1 ≤ q.L)
    (hroot : IsDysonRootV (hopB q.g) (gammaG q.g) q.L q.E (mRoot q.g q.L q.E))
    (x : Fin q.L × Fin W) : flowM W q x x = mRoot q.g q.L q.E := by
  have hγ : 0 < gammaG q.g := inv_pos.mpr (pow_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) 2)
  have hw : 0 < ((q.E : ℂ) + (gammaG q.g : ℂ) * mRoot q.g q.L q.E).im := by
    simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.im_ofReal_mul]
    exact mul_pos hγ hroot.1
  unfold flowM
  rw [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, mul_one,
    dysonMat_diag _ _ _ hL _ _ hw x.1]
  exact hroot.2.symm

/-- Resolvent moments on `W^{-1/2} ≤ g ≤ C` in the form of Theorem 2.3 [thm:bounded-lower]
(uniform fixed-rate form): for `ρ(W) log W ≤ L ≤ W²` (`ρ → ∞`) and `F_g(-|E|) ≥ κ`, the moments
of `Im G_xx(E + iη_L)` are at most `C_p`; `C_p` depends on `C, κ, ν, p` only. -/
theorem small_lower_fdist (C κ ν p : ℝ) (hC : 0 < C) (hκ : 0 < κ ∧ κ < 1 / 2)
    (hν : 0 < ν ∧ ν < 1) (hp : 0 < p) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, ρ W * Real.log W ≤ L → (L : ℝ) ≤ (W : ℝ) ^ 2 →
      ∀ g : ℝ, (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ g → g ≤ C → ∀ E : ℝ, κ ≤ Fdist g (-|E|) →
      ∀ x : Fin L × Fin W,
        Integrable (fun ω' => ((resolventMat (Hmat g W L ω') (E + etaL W L g ν * Complex.I) x x).im)
          ^ p) (μ W L) ∧
        ∫ ω', ((resolventMat (Hmat g W L ω') (E + etaL W L g ν * Complex.I) x x).im) ^ p
          ∂(μ W L) ≤ Cp := by
  obtain ⟨B, c', η₀, K, L₀, hB, hc', hη₀, -, hL₀3, Hm⟩ := terminal_match_bdd C κ hC hκ
  obtain ⟨L₁, W₁, He⟩ := endBudget_bdd C κ ν hC hκ hν
  set M : ℝ := max 1 C with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  refine ⟨(M + 1) ^ p + 1, by positivity, fun ρ hρ => ?_⟩
  have hgmin : ∀ W : ℕ, 0 < (fun W : ℕ => (max (W : ℝ) 1) ^ (-(1 / 2 : ℝ)) / 2) W := fun W =>
    div_pos (Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) _) two_pos
  obtain ⟨θs, cps, -, -, HI⟩ := theorem412_small C B c' hC hB hc' _ ρ hgmin hρ (ν / 3)
    (by linarith [hν.1])
  obtain ⟨W₂, HW₂⟩ := HI.entry (ν / 12) (4 * p + 2) (by linarith [hν.1]) (by linarith)
  have hlim : ∀ y : ℝ, 0 < y → ∀ a : ℝ, ∀ᶠ W : ℕ in atTop, a ≤ (W : ℝ) ^ y := fun y hy a =>
    ((tendsto_rpow_atTop hy).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop a
  have hρlog : Tendsto (fun W : ℕ => ρ W * Real.log W) atTop atTop :=
    hρ.atTop_mul_atTop₀ (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hev : ∀ᶠ W : ℕ in atTop, 1 ≤ W ∧ W₁ ≤ W ∧ W₂ ≤ W ∧ η₀⁻¹ ≤ (W : ℝ) ^ (1 - ν) ∧
      M ^ 2 ≤ (W : ℝ) ^ ν ∧ ((max L₀ L₁ : ℕ) : ℝ) ≤ ρ W * Real.log W :=
    (eventually_ge_atTop 1).and ((eventually_ge_atTop W₁).and ((eventually_ge_atTop W₂).and
      ((hlim _ (by linarith [hν.2]) _).and ((hlim _ hν.1 _).and
        (hρlog.eventually_ge_atTop _)))))
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.1 hev
  refine ⟨W₀, fun W hW L hL1 hL2 g hg1 hg2 E hE x => ?_⟩
  obtain ⟨hW1, hWW₁, hWW₂, hWη, hWM, hWL⟩ := hW₀ W hW
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hLmax : max L₀ L₁ ≤ L := by exact_mod_cast hWL.trans hL1
  have hL₀ : L₀ ≤ L := (le_max_left _ _).trans hLmax
  have hL₁ : L₁ ≤ L := (le_max_right _ _).trans hLmax
  have hL3 : 3 ≤ L := hL₀3.trans hL₀
  have hg0 : 0 < g := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) hg1
  obtain ⟨hℓ1, hℓ2⟩ := lower_ellStar_bounds hW1' (by omega : 1 ≤ L) hg0.le hg2
  have hℓ0 : 0 < ellStar W L g := lt_of_lt_of_le hW0 hℓ1
  have hWν : 0 < (W : ℝ) ^ ν := Real.rpow_pos_of_pos hW0 _
  obtain ⟨hzeta, hu3⟩ := He W hWW₁ L hL₁ g hg1 hg2 E hE
  set η : ℝ := etaL W L g ν with hη_def
  have hη0 : 0 < η := div_pos hWν hℓ0
  have hηη₀ : η ≤ η₀ := by
    rw [hη_def, etaL, div_le_iff₀ hℓ0]
    have h1 : (W : ℝ) ^ ν * (W : ℝ) ^ (1 - ν) = W := by
      rw [← Real.rpow_add hW0]; simp
    have h2 : (W : ℝ) ^ ν * η₀⁻¹ ≤ W := by
      have := mul_le_mul_of_nonneg_left hWη hWν.le
      rwa [h1] at this
    calc (W : ℝ) ^ ν = η₀ * ((W : ℝ) ^ ν * η₀⁻¹) := by field_simp
      _ ≤ η₀ * W := mul_le_mul_of_nonneg_left h2 hη₀.le
      _ ≤ η₀ * ellStar W L g := mul_le_mul_of_nonneg_left hℓ1 hη₀.le
  have hηinv : 1 / η ≤ (W : ℝ) ^ 2 := by
    rw [hη_def, etaL, one_div, inv_div, div_le_iff₀ hWν]
    calc ellStar W L g ≤ M ^ 2 * (W : ℝ) ^ 2 := hℓ2
      _ ≤ (W : ℝ) ^ ν * (W : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hWM (sq_nonneg _)
      _ = (W : ℝ) ^ 2 * (W : ℝ) ^ ν := mul_comm _ _
  obtain ⟨hu12, -, -, hsc, hc1, hreg, hroot, hres⟩ := Hm g hg0.le hg2 L hL₀ E hE η hη0 hηη₀
  set q : FlowPt := termPt g L E η with hq
  set c : ℝ := termScale g L E η with hc
  set m : ℂ := mDysonL g L (E + η * Complex.I) with hm
  have hc0 : 0 < c := lt_of_lt_of_le (Real.sqrt_pos.2 (by linarith)) hsc
  have hgmin_q : (max (W : ℝ) 1) ^ (-(1 / 2 : ℝ)) / 2 ≤ q.g := by
    rw [max_eq_left hW1']
    have hs : 1 / 2 ≤ Real.sqrt q.u := (Real.le_sqrt (by norm_num) (by linarith)).2 (by linarith)
    change (W : ℝ) ^ (-(1 / 2 : ℝ)) / 2 ≤ Real.sqrt q.u * g
    nlinarith
  have hmem : q ∈ {p : FlowPt | ∃ q ∈ baseBdd C B c'
      (fun W : ℕ => (max (W : ℝ) 1) ^ (-(1 / 2 : ℝ)) / 2) ρ W,
      zetaProp q.g W q.L q.u ≤ (W : ℝ) ^ (-(ν / 3)) ∧ 1 / 2 ≤ p.u ∧ p.u ≤ q.u ∧
        p = ⟨q.g, q.E, q.L, p.u⟩} :=
    ⟨q, ⟨hgmin_q, hreg, hL1, hL2, hu12, hu3⟩, hzeta, hu12, le_rfl, rfl⟩
  have hS := HW₂ W hWW₂ q hmem
  have hentry : (W : ℝ) ^ (ν / 12) * Real.sqrt (zetaProp q.g W L q.u) ≤ 1 := by
    have hs : Real.sqrt (zetaProp q.g W L q.u) ≤ (W : ℝ) ^ (-(ν / 6)) := by
      have h6 : ((W : ℝ) ^ (-(ν / 6))) ^ 2 = (W : ℝ) ^ (-(ν / 3)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; ring_nf
      rw [← Real.sqrt_sq (Real.rpow_nonneg hW0.le (-(ν / 6))), h6]
      exact Real.sqrt_le_sqrt hzeta
    calc (W : ℝ) ^ (ν / 12) * Real.sqrt (zetaProp q.g W L q.u)
        ≤ (W : ℝ) ^ (ν / 12) * (W : ℝ) ^ (-(ν / 6)) :=
          mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hW0.le _)
      _ = (W : ℝ) ^ (-(ν / 12)) := by rw [← Real.rpow_add hW0]; ring_nf
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1' (by linarith [hν.1])
  have hmnorm : ‖m‖ ≤ max 1 g :=
    mDysonL_norm_le_max g hg0.le L (by omega) _ (by simpa using hη0)
  have hgood : ∀ ω ∉ {ω : Ω W L | ∃ l : (Fin L × Fin W) × (Fin L × Fin W),
      (W : ℝ) ^ (ν / 12) * Real.sqrt (flowZeta W (id q)) <
        ‖(flowG W (id q) ω - flowM W (id q)) l.1 l.2‖},
      (resolventMat (Hmat g W L ω) (E + η * Complex.I) x x).im ≤ M + 1 := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, not_exists, not_lt] at hω
    have hx : ‖flowG W q ω x x - flowM W q x x‖ ≤ 1 := (hω (x, x)).trans hentry
    have hdiag : flowM W q x x = m / (c : ℂ) := by
      rw [← hroot]
      exact lower_flowM_diag W q (by change 1 ≤ L; omega) hreg.2.2.2.1 x
    have him : (flowG W q ω x x).im ≤ m.im / c + 1 := by
      have h1 := (Complex.abs_im_le_norm (flowG W q ω x x - flowM W q x x)).trans hx
      rw [Complex.sub_im, hdiag, Complex.div_ofReal_im] at h1
      linarith [le_abs_self ((flowG W q ω x x).im - m.im / c)]
    have hGx : resolventMat (Hmat g W L ω) (E + η * Complex.I) x x =
        (c : ℂ) * flowG W q ω x x := by
      rw [hres W ω]; rfl
    rw [hGx, Complex.im_ofReal_mul]
    calc c * (flowG W q ω x x).im ≤ c * (m.im / c + 1) := mul_le_mul_of_nonneg_left him hc0.le
      _ = m.im + c := by field_simp
      _ ≤ M + 1 := add_le_add ((Complex.im_le_norm m).trans
          (hmnorm.trans (max_le_max le_rfl hg2))) hc1
  have hHerm := Hmat_isHermitian g W L
  obtain ⟨hint, hbound⟩ := moment_good_bad (P := μ W L)
    (Y := fun ω => (resolventMat (Hmat g W L ω) (E + η * Complex.I) x x).im)
    (Z := fun _ => 1 / η) (Cs := (1 / η) ^ (2 * p))
    (continuous_im_resolvent_Hmat g W L E hη0.ne' x).measurable
    (fun ω => (im_resolvent_bounds (hHerm ω) E hη0 x).1)
    (fun ω => (im_resolvent_bounds (hHerm ω) E hη0 x).2) hp (by linarith)
    (integrable_const _) (le_of_eq (by simp)) _ hS hgood
  refine ⟨hint, hbound.trans ?_⟩
  have hη1 : 0 ≤ 1 / η := by positivity
  suffices hsq : Real.sqrt ((1 / η) ^ (2 * p)) * Real.sqrt ((W : ℝ) ^ (-(4 * p + 2))) ≤ 1 by
    linarith
  rw [← Real.sqrt_mul (Real.rpow_nonneg hη1 _), Real.sqrt_le_one]
  calc (1 / η) ^ (2 * p) * (W : ℝ) ^ (-(4 * p + 2))
      ≤ ((W : ℝ) ^ 2) ^ (2 * p) * (W : ℝ) ^ (-(4 * p + 2)) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hη1 hηinv (by linarith))
          (Real.rpow_nonneg hW0.le _)
    _ = (W : ℝ) ^ (-2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le, ← Real.rpow_add hW0]
        ring_nf
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1' (by norm_num)

end LSBA
