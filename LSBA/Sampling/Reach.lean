import LSBA.Prop.Inputs

/-!
# Points reached by comparison chains

Every point reached from a base family by at most `J` comparisons of Lemma 6.3(b)
[da:lem:comparison-parameters] comes from a base point by an explicit chain; at bounded coupling
it stays in the regular domain with `3 ≤ L ≤ W²`, at large coupling it keeps `g ≥ C_κ/√2`,
`|E| ≤ 2 − κ/2` and the anchor root bounds; the characteristic point (5.3)
[fo:eq:characteristic] and the admissible
heights of Lemma 5.9 [gc:lem:residual] and Lemma 5.10 [fo:lem:sampling-continuity] at such points.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- For `ρ → ∞` and any reals `a`, `M`, eventually `a ≤ ρ(W)`, `M ≤ log W` and `1 ≤ W`. -/
private lemma reach_threshold (ρ : ℕ → ℝ) (hρ : Tendsto ρ atTop atTop) (a M : ℝ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → a ≤ ρ W ∧ M ≤ Real.log W ∧ 1 ≤ W := by
  have h1 : ∀ᶠ W : ℕ in atTop, a ≤ ρ W := hρ.eventually_ge_atTop a
  have h2 : ∀ᶠ W : ℕ in atTop, M ≤ Real.log W :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop M
  have h3 : ∀ᶠ W : ℕ in atTop, 1 ≤ W := eventually_ge_atTop 1
  exact Filter.eventually_atTop.mp ((h1.and h2).and h3) |>.imp fun W₀ h W hW =>
    ⟨(h W hW).1.1, (h W hW).1.2, (h W hW).2⟩

/-- The time of a base point is below `1` when `W ≥ 1`. -/
private lemma reach_time_lt_one {W : ℕ} (hW : 1 ≤ W) {u : ℝ}
    (h : (W : ℝ) ^ (-3 : ℝ) ≤ 1 - u) : u < 1 := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have := Real.rpow_pos_of_pos hW0 (-3 : ℝ)
  linarith

/-- `γ_g > 0`. -/
private lemma reach_gammaG_pos (g : ℝ) : 0 < gammaG g := by unfold gammaG; positivity

/-- `γ_g = g⁻²` for `g ≥ 1`. -/
private lemma reach_gammaG_of_one_le {g : ℝ} (hg : 1 ≤ g) : gammaG g = (g ^ 2)⁻¹ := by
  unfold gammaG; rw [max_eq_right hg]

/-- A point reached from `base` by at most `d` comparisons is the image of a base point under a
nested chain of at most `d` comparisons of Lemma 6.3(b) [da:lem:comparison-parameters], each acting
at a time not later than the previous comparison time, with the same `L` and an earlier time. -/
theorem cmpReach_chain (base : ℕ → Set FlowPt) (W d : ℕ) (p : FlowPt)
    (h : CmpReach base W d p) :
    ∃ q ∈ base W, ∃ steps : List (ℝ × ℝ), steps.length ≤ d ∧
      (∀ x ∈ steps, 1 / 2 ≤ x.1 ∧ x.1 ≤ x.2 ∧ x.2 ≤ q.u) ∧
      steps.IsChain (fun x y => y.2 ≤ x.1) ∧
      (p.g, p.E) = cmpChain q.L (q.g, q.E) steps ∧ p.L = q.L ∧ p.u ≤ q.u ∧
      (1 / 2 ≤ q.u → 1 / 2 ≤ p.u) ∧ ∀ x ∈ steps.getLast?, p.u ≤ x.1 := by
  induction h with
  | @base p hp =>
    exact ⟨_, hp, [], by simp, by simp, List.IsChain.nil, rfl, rfl, le_rfl, id, by simp⟩
  | @earlier d p v _ hv1 hvu ih =>
    obtain ⟨q, hq, steps, hlen, hadm, hchain, hpc, hL, hu, h12, hlast⟩ := ih
    exact ⟨q, hq, steps, hlen, hadm, hchain, hpc, hL, hvu.trans hu, fun h => hv1,
      fun x hx => hvu.trans (hlast x hx)⟩
  | @cmp d p s _ hs1 hsu ih =>
    obtain ⟨q, hq, steps, hlen, hadm, hchain, hpc, hL, hu, h12, hlast⟩ := ih
    refine ⟨q, hq, steps ++ [(s, p.u)], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton]; omega
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hadm x hx
      · rw [List.mem_singleton.mp hx]
        exact ⟨hs1, hsu, hu⟩
    · refine hchain.append (List.isChain_singleton _) ?_
      intro x hx y hy
      rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      exact hlast x hx
    · have hpL : p.L = q.L := hL
      change ((cmpPt p s).g, (cmpPt p s).E) = cmpChain q.L (q.g, q.E) (steps ++ [(s, p.u)])
      unfold cmpChain at hpc ⊢
      rw [List.foldl_append, ← hpc]
      simp only [List.foldl_cons, List.foldl_nil, cmpStep, cmpPt, hpL]
    · exact hL
    · exact hsu.trans hu
    · exact fun h => hs1
    · intro x hx
      rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)] at hx
      simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hx
      subst hx
      exact le_rfl
  | @lift d p _ ih =>
    obtain ⟨q, hq, steps, hlen, hadm, hchain, hpc, hL, hu, h12, hlast⟩ := ih
    exact ⟨q, hq, steps, hlen.trans (Nat.le_succ _), hadm, hchain, hpc, hL, hu, h12, hlast⟩

/-- Bounded coupling: for a base family inside the bounded-coupling range, every point reached with
depth at most `J` is regular (Lemma 6.3(b) [da:lem:comparison-parameters]), has `0 < g`,
`3 ≤ L ≤ W²` and a time in `[1/2, 1 - W^{-3}]`. -/
theorem cmpReach_bdd (C B c' : ℝ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c') (gmin ρ : ℕ → ℝ)
    (hgmin : ∀ W, 0 < gmin W) (hρ : Tendsto ρ atTop atTop) (J : ℕ) :
    ∃ BJ cJ : ℝ, 0 < cJ ∧ ∃ W₀ : ℕ, ∀ base : ℕ → Set FlowPt,
      (∀ W p, p ∈ base W → gmin W ≤ p.g ∧ RegBdd C B c' p.L p.g p.E ∧
        ρ W * Real.log W ≤ p.L ∧ (p.L : ℝ) ≤ (W : ℝ) ^ 2 ∧ 1 / 2 ≤ p.u ∧
        (W : ℝ) ^ (-3 : ℝ) ≤ 1 - p.u) →
      ∀ W : ℕ, W₀ ≤ W → ∀ d p, d ≤ J → CmpReach base W d p →
        RegBdd C BJ cJ p.L p.g p.E ∧ 0 < p.g ∧ 3 ≤ p.L ∧ (p.L : ℝ) ≤ (W : ℝ) ^ 2 ∧
        1 / 2 ≤ p.u ∧ (W : ℝ) ^ (-3 : ℝ) ≤ 1 - p.u := by
  obtain ⟨BJ, cJ, L₀, hcJ, H⟩ := cmpChain_bdd C B c' J hC hB hc'
  obtain ⟨W₀, hW₀⟩ := reach_threshold ρ hρ 1 (max 3 (L₀ : ℝ))
  refine ⟨BJ, cJ, hcJ, W₀, fun base hbase W hW d p hd hreach => ?_⟩
  obtain ⟨hρ1, hlog, hW1⟩ := hW₀ W hW
  obtain ⟨q, hq, steps, hlen, hadm, hchain, hpc, hL, hu, h12, -⟩ := cmpReach_chain base W d p hreach
  obtain ⟨hgq, hreg, hLlog, hLW, hq12, hqt⟩ := hbase W q hq
  have hqlt : q.u < 1 := reach_time_lt_one hW1 hqt
  have hlog0 : 0 ≤ Real.log W := le_trans (by positivity) hlog
  have hLge : max 3 (L₀ : ℝ) ≤ q.L :=
    hlog.trans ((le_mul_of_one_le_left hlog0 hρ1).trans hLlog)
  have hL3 : 3 ≤ q.L := by exact_mod_cast (le_max_left _ _).trans hLge
  have hLL₀ : L₀ ≤ q.L := by exact_mod_cast (le_max_right _ _).trans hLge
  obtain ⟨hcg, hregp⟩ := H q.g q.L hL3 hLL₀ q.E hreg steps (hlen.trans hd)
    (fun x hx => ⟨(hadm x hx).1, (hadm x hx).2.1, (hadm x hx).2.2.trans_lt hqlt⟩)
  have hg : p.g = (cmpChain q.L (q.g, q.E) steps).1 := congrArg Prod.fst hpc
  have hE : p.E = (cmpChain q.L (q.g, q.E) steps).2 := congrArg Prod.snd hpc
  have hgq0 : 0 < q.g := (hgmin W).trans_le hgq
  refine ⟨?_, ?_, ?_, ?_, h12 hq12, ?_⟩
  · rw [hL, hg, hE]; exact hregp
  · rw [hg]; exact lt_of_lt_of_le (by positivity) hcg
  · rw [hL]; exact hL3
  · rw [hL]; exact hLW
  · linarith

/-- Large coupling: for a base family inside the large-coupling range, every point reached with
depth at most `J` satisfies `g ≥ C_κ/√2`, `|E| ≤ 2 - κ/2`, the anchor is a root with `C''⁻¹ ≤ Im m`
and `|m| ≤ C''` ((6.11) [fo:eq:large-input-domain], (6.2) [fo:eq:propagation-dyson]),
`ρ(W) g² log W ≤ L ≤ 2C_V g² W²`, and a time in `[1/2, 1 - W^{-3}]`. -/
theorem cmpReach_large (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) (J : ℕ) :
    ∃ Cκ₀ C'' : ℝ, 1 ≤ Cκ₀ ∧ 1 ≤ C'' ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ,
      Tendsto ρ atTop atTop → ∃ W₀ : ℕ, ∀ base : ℕ → Set FlowPt,
        (∀ W p, p ∈ base W → Cκ ≤ p.g ∧ |p.E| ≤ 2 - 3 * κ / 4 ∧
          ρ W * p.g ^ 2 * Real.log W ≤ p.L ∧ (p.L : ℝ) ≤ CV * p.g ^ 2 * (W : ℝ) ^ 2 ∧
          1 / 2 ≤ p.u ∧ (W : ℝ) ^ (-3 : ℝ) ≤ 1 - p.u) →
        ∀ W : ℕ, W₀ ≤ W → ∀ d p, d ≤ J → CmpReach base W d p →
          Cκ / Real.sqrt 2 ≤ p.g ∧ |p.E| ≤ 2 - κ / 2 ∧
          IsDysonRootV (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E) ∧
          C''⁻¹ ≤ (mRoot p.g p.L p.E).im ∧ ‖mRoot p.g p.L p.E‖ ≤ C'' ∧
          ρ W * p.g ^ 2 * Real.log W ≤ p.L ∧ (p.L : ℝ) ≤ 2 * CV * p.g ^ 2 * (W : ℝ) ^ 2 ∧
          1 / 2 ≤ p.u ∧ (W : ℝ) ^ (-3 : ℝ) ≤ 1 - p.u := by
  obtain ⟨Cκ₁, R₁, C₁, hCκ₁, hR₁, hC₁, H1⟩ := cmpChain_large κ hκ hκ2 J
  obtain ⟨Cκ₂, c₂, C₂, hCκ₂, hc₂, hC₂, H2⟩ := scalesProp_large (κ / 2) (by linarith) (by linarith)
  obtain ⟨CA, W₁, hCA, H2'⟩ := H2 1 one_pos
  refine ⟨max Cκ₁ (Real.sqrt 2 * Cκ₂), max C₁ C₂, hCκ₁.trans (le_max_left _ _),
    hC₁.trans (le_max_left _ _), fun Cκ hCκ ρ hρ => ?_⟩
  obtain ⟨W₂, hW₂⟩ := reach_threshold ρ hρ (max CA 1) R₁
  refine ⟨max W₂ W₁, fun base hbase W hW d p hd hreach => ?_⟩
  obtain ⟨hρA, hlog, hW1⟩ := hW₂ W ((le_max_left _ _).trans hW)
  have hρ1 : 1 ≤ ρ W := (le_max_right _ _).trans hρA
  have hρCA : CA ≤ ρ W := (le_max_left _ _).trans hρA
  have hWW₁ : W₁ ≤ W := (le_max_right _ _).trans hW
  obtain ⟨q, hq, steps, hlen, hadm, hchain, hpc, hL, hu, h12, hlast⟩ :=
    cmpReach_chain base W d p hreach
  obtain ⟨hgq, hEq, hLlog, hLV, hq12, hqt⟩ := hbase W q hq
  have hqlt : q.u < 1 := reach_time_lt_one hW1 hqt
  have hlog0 : 0 ≤ Real.log W := le_trans (by linarith [hR₁]) hlog
  have hCκ₁q : Cκ₁ ≤ q.g := ((le_max_left _ _).trans hCκ).trans hgq
  have hq0 : 0 < q.g := by linarith
  have hRL : R₁ * q.g ^ 2 ≤ q.L := by
    have h1 : R₁ ≤ ρ W * Real.log W := hlog.trans (le_mul_of_one_le_left hlog0 hρ1)
    calc R₁ * q.g ^ 2 ≤ (ρ W * Real.log W) * q.g ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = ρ W * q.g ^ 2 * Real.log W := by ring
      _ ≤ q.L := hLlog
  obtain ⟨-, -, hg1, hg2, hE', hroot, hIm⟩ := H1 q.g hCκ₁q q.L hRL q.E hEq steps (hlen.trans hd)
    (fun x hx => ⟨(hadm x hx).1, (hadm x hx).2.1, (hadm x hx).2.2.trans_lt hqlt⟩) hchain
  have hg : p.g = (cmpChain q.L (q.g, q.E) steps).1 := congrArg Prod.fst hpc
  have hE : p.E = (cmpChain q.L (q.g, q.E) steps).2 := congrArg Prod.snd hpc
  rw [← hg] at hg1 hg2
  rw [← hE] at hE'
  rw [← hg, ← hE, ← hL] at hroot
  rw [← hg, ← hE, ← hL] at hIm
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hCκp : Cκ / Real.sqrt 2 ≤ p.g :=
    (div_le_div_of_nonneg_right hgq hs2.le).trans hg1
  have hCκ0 : 0 < Cκ := by
    have := (le_max_left Cκ₁ (Real.sqrt 2 * Cκ₂)).trans hCκ
    linarith
  have hp0 : 0 < p.g := lt_of_lt_of_le (by positivity) hCκp
  have hCκ₂p : Cκ₂ ≤ p.g := by
    have h1 : Real.sqrt 2 * Cκ₂ ≤ Cκ := (le_max_right _ _).trans hCκ
    rw [div_eq_inv_mul] at hCκp
    have h2 : Cκ₂ ≤ (Real.sqrt 2)⁻¹ * Cκ := by
      rw [inv_mul_eq_div, le_div_iff₀ hs2]; linarith
    linarith
  have hLA : CA * p.g ^ 2 * Real.log W ≤ p.L := by
    have h1 : p.g ^ 2 ≤ q.g ^ 2 := pow_le_pow_left₀ hp0.le hg2 2
    calc CA * p.g ^ 2 * Real.log W ≤ ρ W * q.g ^ 2 * Real.log W := by gcongr
      _ ≤ (q.L : ℝ) := hLlog
      _ = (p.L : ℝ) := by rw [hL]
  obtain ⟨-, hM, -⟩ := H2' W hWW₁ p.g hCκ₂p p.L hLA p.E hE' _ hroot
  have hL1 : 1 ≤ p.L := by
    have : (0 : ℝ) < q.L := lt_of_lt_of_le (by positivity) hRL
    rw [hL]; exact_mod_cast this
  have hβ : 0 < gammaG p.g := reach_gammaG_pos _
  have hw : 0 < ((p.E : ℂ) + (gammaG p.g : ℂ) * mRoot p.g p.L p.E).im := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_mul,
      add_zero, zero_add]
    exact mul_pos hβ hroot.1
  have hdiag := dysonMat_diag (hopB p.g) (gammaG p.g) p.L hL1 (p.E : ℂ) (mRoot p.g p.L p.E) hw
    ⟨0, hL1⟩
  have hm : ‖mRoot p.g p.L p.E‖ ≤ max C₁ C₂ :=
    calc ‖mRoot p.g p.L p.E‖ = ‖dysonMat (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E)
          ⟨0, hL1⟩ ⟨0, hL1⟩‖ := by rw [hdiag]; exact congrArg _ hroot.2
      _ ≤ C₂ := hM _ _
      _ ≤ max C₁ C₂ := le_max_right _ _
  have hgg : q.g ^ 2 ≤ 2 * p.g ^ 2 := by
    have h1 : (q.g / Real.sqrt 2) ^ 2 ≤ p.g ^ 2 :=
      pow_le_pow_left₀ (by positivity) hg1 2
    rw [div_pow, Real.sq_sqrt (by norm_num)] at h1
    linarith
  refine ⟨hCκp, hE', hroot, (inv_anti₀ (by positivity) (le_max_left _ _)).trans hIm, hm, ?_, ?_,
    h12 hq12, by linarith⟩
  · calc ρ W * p.g ^ 2 * Real.log W ≤ ρ W * q.g ^ 2 * Real.log W := by
          have h1 : p.g ^ 2 ≤ q.g ^ 2 := pow_le_pow_left₀ hp0.le hg2 2
          have h2 : 0 ≤ ρ W := by linarith
          gcongr
      _ ≤ (q.L : ℝ) := hLlog
      _ = (p.L : ℝ) := by rw [hL]
  · calc (p.L : ℝ) = (q.L : ℝ) := by rw [hL]
      _ ≤ CV * q.g ^ 2 * (W : ℝ) ^ 2 := hLV
      _ ≤ CV * (2 * p.g ^ 2) * (W : ℝ) ^ 2 := by gcongr
      _ = 2 * CV * p.g ^ 2 * (W : ℝ) ^ 2 := by ring

/-- The characteristic (5.3) [fo:eq:characteristic] at large coupling, at every time
`0 ≤ u < 1`: `|Re z_u| ≤ 2 - κ/2`, `|z_u - E| ≤ C'/g²`, `0 < η_u ≤ C'/g²` and
`(1 - u)/C' ≤ g² η_u`. -/
theorem char_large (κ C : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hC : 1 ≤ C) :
    ∃ Cκ C' : ℝ, 1 ≤ Cκ ∧ 1 ≤ C' ∧ ∀ g : ℝ, Cκ ≤ g → ∀ (E : ℝ) (m : ℂ), |E| ≤ 2 - κ →
      ‖m‖ ≤ C → C⁻¹ ≤ m.im → ∀ u : ℝ, 0 ≤ u → u < 1 →
        |(zChar g E m u).re| ≤ 2 - κ / 2 ∧ ‖zChar g E m u - E‖ ≤ C' / g ^ 2 ∧
        0 < etaChar g m u ∧ etaChar g m u ≤ C' / g ^ 2 ∧
        (1 - u) / C' ≤ g ^ 2 * etaChar g m u := by
  refine ⟨max 1 (2 * C / κ), C, le_max_left _ _, hC, ?_⟩
  intro g hg E m hE hm hmi u hu0 hu1
  have hg1 : 1 ≤ g := (le_max_left _ _).trans hg
  have hg0 : 0 < g := by linarith
  have hg2 : 0 < g ^ 2 := by positivity
  have hgC : 2 * C / κ ≤ g := (le_max_right _ _).trans hg
  have hC0 : 0 < C := by linarith
  have hCg : C / g ^ 2 ≤ κ / 2 := by
    rw [div_le_iff₀ hg2]
    rw [div_le_iff₀ hκ] at hgC
    nlinarith
  have ht0 : 0 < 1 - u := by linarith
  set δ : ℝ := (1 - u) * (g ^ 2)⁻¹ with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ (g ^ 2)⁻¹ := by
    rw [hδ]; exact mul_le_of_le_one_left (by positivity) (by linarith)
  have hz : zChar g E m u = (E : ℂ) + (δ : ℂ) * m := by
    simp only [zChar, reach_gammaG_of_one_le hg1, hδ]
  have hη : etaChar g m u = δ * m.im := by
    simp only [etaChar, reach_gammaG_of_one_le hg1, hδ]
  have hmi0 : 0 < m.im := lt_of_lt_of_le (inv_pos.mpr hC0) hmi
  have hδm : δ * ‖m‖ ≤ C / g ^ 2 := by
    calc δ * ‖m‖ ≤ (g ^ 2)⁻¹ * C := mul_le_mul hδ1 hm (norm_nonneg _) (by positivity)
      _ = C / g ^ 2 := by rw [inv_mul_eq_div]
  have hzE : ‖zChar g E m u - E‖ = δ * ‖m‖ := by
    rw [hz, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hδ0.le]
  have hre : (zChar g E m u).re = E + δ * m.re := by
    rw [hz]; simp
  refine ⟨?_, hzE ▸ hδm, ?_, ?_, ?_⟩
  · rw [hre]
    have h1 : |E + δ * m.re| ≤ |E| + δ * ‖m‖ := by
      calc |E + δ * m.re| ≤ |E| + |δ * m.re| := abs_add_le _ _
        _ = |E| + δ * |m.re| := by rw [abs_mul, abs_of_pos hδ0]
        _ ≤ |E| + δ * ‖m‖ := by
          gcongr; exact Complex.abs_re_le_norm m
    linarith
  · rw [hη]; exact mul_pos hδ0 hmi0
  · rw [hη]
    exact (mul_le_mul_of_nonneg_left (Complex.im_le_norm m) hδ0.le).trans hδm
  · rw [hη]
    have : g ^ 2 * (δ * m.im) = (1 - u) * m.im := by
      rw [hδ]; field_simp
    rw [this]
    calc (1 - u) / C = (1 - u) * C⁻¹ := div_eq_mul_inv _ _
      _ ≤ (1 - u) * m.im := mul_le_mul_of_nonneg_left hmi ht0.le

/-- Large coupling: for a base family inside the large-coupling range, every admissible height of
Lemma 5.10 [fo:lem:sampling-continuity] lies in `[η_u, C'/g²]` (Lemma 6.3(a)
[da:lem:comparison-parameters] bounds `Im w`). -/
theorem segAdm_large (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) (J : ℕ) :
    ∃ Cκ₀ C' : ℝ, 1 ≤ Cκ₀ ∧ 1 ≤ C' ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ,
      Tendsto ρ atTop atTop → ∃ W₀ : ℕ, ∀ base : ℕ → Set FlowPt,
        (∀ W p, p ∈ base W → Cκ ≤ p.g ∧ |p.E| ≤ 2 - 3 * κ / 4 ∧
          ρ W * p.g ^ 2 * Real.log W ≤ p.L ∧ (p.L : ℝ) ≤ CV * p.g ^ 2 * (W : ℝ) ^ 2 ∧
          1 / 2 ≤ p.u ∧ (W : ℝ) ^ (-3 : ℝ) ≤ 1 - p.u) →
        ∀ W : ℕ, W₀ ≤ W → ∀ x : FlowPt × ℝ, SegAdm base J W x →
          etaChar x.1.g (mRoot x.1.g x.1.L x.1.E) x.1.u ≤ x.2 ∧ x.2 ≤ C' / x.1.g ^ 2 := by
  obtain ⟨Cκ₀', C'', hCκ₀', hC'', HR⟩ := cmpReach_large κ CV hκ hκ2 hCV J
  obtain ⟨Cκc, Rc, Cc, hCκc, hRc, hCc, HC⟩ := cmpParams_large (κ / 2) (by linarith) (by linarith)
  refine ⟨max Cκ₀' (Real.sqrt 2 * Cκc), max C'' (Cc * C'' / 2), hCκ₀'.trans (le_max_left _ _),
    hC''.trans (le_max_left _ _), fun Cκ hCκ ρ hρ => ?_⟩
  obtain ⟨W₁, hW₁⟩ := HR Cκ ((le_max_left _ _).trans hCκ) ρ hρ
  obtain ⟨W₂, hW₂⟩ := reach_threshold ρ hρ 1 Rc
  refine ⟨max W₁ W₂, fun base hbase W hW x hx => ?_⟩
  obtain ⟨d, hd, hreach, hseg⟩ := hx
  obtain ⟨hρ1, hlog, hW1⟩ := hW₂ W ((le_max_right _ _).trans hW)
  obtain ⟨hCκp, hE', hroot, hIm, hm, hvol, -, hu12, hut⟩ :=
    hW₁ base hbase W ((le_max_left _ _).trans hW) d x.1 hd hreach
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hCκcp : Cκc ≤ x.1.g := by
    have h1 : Real.sqrt 2 * Cκc ≤ Cκ := (le_max_right _ _).trans hCκ
    refine le_trans ?_ hCκp
    rw [le_div_iff₀ hs2]; linarith
  have hg1 : 1 ≤ x.1.g := hCκc.trans hCκcp
  have hg0 : 0 < x.1.g := by linarith
  have hg2 : 0 < x.1.g ^ 2 := by positivity
  have hu1 : x.1.u < 1 := reach_time_lt_one hW1 hut
  have ht0 : 0 < 1 - x.1.u := by linarith
  set δ : ℝ := (1 - x.1.u) * (x.1.g ^ 2)⁻¹ with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ (x.1.g ^ 2)⁻¹ := by
    rw [hδ]; exact mul_le_of_le_one_left (by positivity) (by linarith)
  have hη : etaChar x.1.g (mRoot x.1.g x.1.L x.1.E) x.1.u = δ * (mRoot x.1.g x.1.L x.1.E).im := by
    simp only [etaChar, reach_gammaG_of_one_le hg1, hδ]
  have hη' : etaChar x.1.g (mRoot x.1.g x.1.L x.1.E) x.1.u ≤ C'' / x.1.g ^ 2 := by
    rw [hη]
    calc δ * (mRoot x.1.g x.1.L x.1.E).im ≤ δ * ‖mRoot x.1.g x.1.L x.1.E‖ :=
          mul_le_mul_of_nonneg_left (Complex.im_le_norm _) hδ0.le
      _ ≤ (x.1.g ^ 2)⁻¹ * C'' := mul_le_mul hδ1 hm (norm_nonneg _) (by positivity)
      _ = C'' / x.1.g ^ 2 := by rw [inv_mul_eq_div]
  have hdiv : ∀ {a b : ℝ}, a ≤ b → a / x.1.g ^ 2 ≤ b / x.1.g ^ 2 := fun h =>
    div_le_div_of_nonneg_right h hg2.le
  rcases hseg with h | ⟨hdJ, s, hs1, hsu, hηy, hyw⟩
  · exact ⟨h.ge, h ▸ hη'.trans (hdiv (le_max_left _ _))⟩
  · refine ⟨hηy, ?_⟩
    have hR : Rc * x.1.g ^ 2 ≤ x.1.L := by
      have hlog0 : 0 ≤ Real.log W := le_trans hRc.le hlog
      have h1 : Rc ≤ ρ W * Real.log W := hlog.trans (le_mul_of_one_le_left hlog0 hρ1)
      calc Rc * x.1.g ^ 2 ≤ (ρ W * Real.log W) * x.1.g ^ 2 :=
            mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
        _ = ρ W * x.1.g ^ 2 * Real.log W := by ring
        _ ≤ x.1.L := hvol
    have hwim := (HC x.1.g hCκcp x.1.L hR x.1.E hE' _ hroot s x.1.u hs1 hsu hu1).2.2.2.2.2.2.2.2.1
    have h1 : (1 - s) ≤ 1 / 2 := by linarith
    have him : (mRoot x.1.g x.1.L x.1.E).im ≤ C'' := (Complex.im_le_norm _).trans hm
    calc x.2 ≤ (wCmp x.1.g x.1.L x.1.E (mRoot x.1.g x.1.L x.1.E) s x.1.u).im := hyw
      _ ≤ Cc * ((1 - s) / (1 - x.1.u)) * etaChar x.1.g (mRoot x.1.g x.1.L x.1.E) x.1.u := hwim
      _ = Cc * (1 - s) * ((x.1.g ^ 2)⁻¹ * (mRoot x.1.g x.1.L x.1.E).im) := by
          rw [hη, hδ]; field_simp
      _ ≤ Cc * (1 / 2) * ((x.1.g ^ 2)⁻¹ * C'') := by
          have : 0 ≤ (x.1.g ^ 2)⁻¹ := by positivity
          have h2 : 0 ≤ 1 - s := by linarith
          have h3 : 0 ≤ (x.1.g ^ 2)⁻¹ * (mRoot x.1.g x.1.L x.1.E).im := by
            have := hroot.1; positivity
          gcongr
      _ = (Cc * C'' / 2) / x.1.g ^ 2 := by ring
      _ ≤ max C'' (Cc * C'' / 2) / x.1.g ^ 2 := hdiv (le_max_right _ _)

end LSBA
