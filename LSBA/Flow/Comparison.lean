import Mathlib

/-!
# Comparison lemmas for the moment method

The moment ODE comparison, the cooperative `2 × 2` comparison with the Perron root and left
eigenvector, and the moment-from-tail bound. They are used in place of the stochastic estimates of
Appendix C.3 [sec:gc-one-step] at fixed times.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The primitive `x ↦ ∫ t in s..x, g t` of a function continuous on `[s, v]` is continuous
there. -/
private lemma comparison_continuousOn_primitive {g : ℝ → ℝ} {s v : ℝ} (hsv : s ≤ v)
    (hg : ContinuousOn g (Set.Icc s v)) :
    ContinuousOn (fun x => ∫ t in s..x, g t) (Set.Icc s v) := by
  have h : IntervalIntegrable g volume s v := hg.intervalIntegrable_of_Icc hsv
  have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := s) (b := v)
    (f := g) (by rwa [Set.uIcc_of_le hsv, ← intervalIntegrable_iff_integrableOn_Icc_of_le hsv])
  rwa [Set.uIcc_of_le hsv] at this

/-- The primitive of a function continuous on `[s, v]` has derivative `g u` at interior points. -/
private lemma comparison_hasDerivAt_primitive {g : ℝ → ℝ} {s v : ℝ}
    (hg : ContinuousOn g (Set.Icc s v)) {u : ℝ} (hu : u ∈ Set.Ioo s v) :
    HasDerivAt (fun x => ∫ t in s..x, g t) (g u) u := by
  have hint : IntervalIntegrable g volume s u :=
    (hg.mono (Set.Icc_subset_Icc_right hu.2.le)).intervalIntegrable_of_Icc hu.1.le
  have hgo : ContinuousOn g (Set.Ioo s v) := hg.mono Set.Ioo_subset_Icc_self
  exact intervalIntegral.integral_hasDerivAt_right hint
    (hgo.stronglyMeasurableAtFilter isOpen_Ioo u hu)
    (hg.continuousAt (Icc_mem_nhds hu.1 hu.2))

/-- A continuous function that starts `≤ 0` and is differentiable inside with nonpositive
derivative wherever it is positive stays `≤ 0`. -/
private lemma comparison_nonpos_of_deriv_nonpos {φ φ' : ℝ → ℝ} {s v : ℝ}
    (hc : ContinuousOn φ (Set.Icc s v)) (hd : ∀ u ∈ Set.Ioo s v, HasDerivAt φ (φ' u) u)
    (hs : φ s ≤ 0) (hneg : ∀ u ∈ Set.Ioo s v, 0 < φ u → φ' u ≤ 0) :
    ∀ u ∈ Set.Icc s v, φ u ≤ 0 := by
  intro u1 hu1
  by_contra hpos
  replace hpos := not_le.mp hpos
  have hcl : IsClosed (Set.Icc s u1 ∩ φ ⁻¹' Set.Iic 0) :=
    (hc.mono (Set.Icc_subset_Icc_right hu1.2)).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_Iic
  have hne : (Set.Icc s u1 ∩ φ ⁻¹' Set.Iic 0).Nonempty :=
    ⟨s, ⟨le_rfl, hu1.1⟩, hs⟩
  have hbdd : BddAbove (Set.Icc s u1 ∩ φ ⁻¹' Set.Iic 0) := ⟨u1, fun x hx => hx.1.2⟩
  have hmem := hcl.csSup_mem hne hbdd
  set u0 := sSup (Set.Icc s u1 ∩ φ ⁻¹' Set.Iic 0) with hu0
  have hu0le : u0 ≤ u1 := csSup_le hne fun x hx => hx.1.2
  have hu0lt : u0 < u1 := by
    refine lt_of_le_of_ne hu0le fun h => ?_
    have := hmem.2
    simp only [Set.mem_preimage, Set.mem_Iic] at this
    rw [h] at this
    linarith
  have hpos' : ∀ u ∈ Set.Ioc u0 u1, 0 < φ u := by
    intro u hu
    by_contra hle
    replace hle := not_lt.mp hle
    have : u ≤ u0 := le_csSup hbdd ⟨⟨hmem.1.1.trans hu.1.le, hu.2⟩, hle⟩
    linarith [hu.1]
  have hsub : Set.Icc u0 u1 ⊆ Set.Icc s v := Set.Icc_subset_Icc hmem.1.1 hu1.2
  have hanti : AntitoneOn φ (Set.Icc u0 u1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc u0 u1) (hc.mono hsub) ?_ ?_
    · rw [interior_Icc]
      intro x hx
      have hx' : x ∈ Set.Ioo s v := ⟨lt_of_le_of_lt hmem.1.1 hx.1, lt_of_lt_of_le hx.2 hu1.2⟩
      exact (hd x hx').differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      have hx' : x ∈ Set.Ioo s v := ⟨lt_of_le_of_lt hmem.1.1 hx.1, lt_of_lt_of_le hx.2 hu1.2⟩
      rw [(hd x hx').deriv]
      exact hneg x hx' (hpos' x ⟨hx.1, hx.2.le⟩)
  have h1 := hanti ⟨le_rfl, hu0lt.le⟩ ⟨hu0lt.le, le_rfl⟩ hu0lt.le
  have h2 := hmem.2
  simp only [Set.mem_preimage, Set.mem_Iic] at h2
  linarith


/-- Integrating-factor comparison: `Y' ≤ ρ Y / (1 - u) + S` with `S ≥ 0` gives
`Y(v) ≤ ((1 - s) / (1 - v)) ^ ρ * (Y(s) + ∫ S)`. -/
private lemma comparison_weighted {Y Y' S : ℝ → ℝ} {s v ρ : ℝ} (hsv : s ≤ v) (hv : v < 1)
    (hρ : 0 ≤ ρ) (hY : ContinuousOn Y (Set.Icc s v)) (hS : ContinuousOn S (Set.Icc s v))
    (hS0 : ∀ u ∈ Set.Icc s v, 0 ≤ S u)
    (hd : ∀ u ∈ Set.Ioo s v, HasDerivAt Y (Y' u) u)
    (hi : ∀ u ∈ Set.Ioo s v, Y' u ≤ ρ * Y u / (1 - u) + S u) :
    Y v ≤ ((1 - s) / (1 - v)) ^ ρ * (Y s + ∫ u in s..v, S u) := by
  have hpos : ∀ u ∈ Set.Icc s v, 0 < 1 - u := fun u hu => by linarith [hu.2]
  have hwc : ContinuousOn (fun u : ℝ => (1 - u) ^ ρ) (Set.Icc s v) :=
    ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id)
      (fun u hu => Or.inl (hpos u hu).ne')
  have hIg : ContinuousOn (fun t => (1 - t) ^ ρ * S t) (Set.Icc s v) := hwc.mul hS
  set I : ℝ → ℝ := fun x => ∫ t in s..x, (1 - t) ^ ρ * S t with hI
  set Z : ℝ → ℝ := fun u => (1 - u) ^ ρ * Y u - I u with hZ
  have hZc : ContinuousOn Z (Set.Icc s v) :=
    (hwc.mul hY).sub (comparison_continuousOn_primitive hsv hIg)
  have hZd : ∀ u ∈ Set.Ioo s v, HasDerivAt Z
      ((-1 * ρ * (1 - u) ^ (ρ - 1)) * Y u + (1 - u) ^ ρ * Y' u - (1 - u) ^ ρ * S u) u := by
    intro u hu
    have hu' : 0 < 1 - u := hpos u (Set.Ioo_subset_Icc_self hu)
    have hw : HasDerivAt (fun x : ℝ => (1 - x) ^ ρ) (-1 * ρ * (1 - u) ^ (ρ - 1)) u :=
      ((hasDerivAt_id u).const_sub 1).rpow_const (Or.inl hu'.ne')
    exact (hw.mul (hd u hu)).sub (comparison_hasDerivAt_primitive hIg hu)
  have hanti : AntitoneOn Z (Set.Icc s v) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc s v) hZc ?_ ?_
    · rw [interior_Icc]
      exact fun u hu => (hZd u hu).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro u hu
      rw [(hZd u hu).deriv]
      have hu' : 0 < 1 - u := hpos u (Set.Ioo_subset_Icc_self hu)
      have hwp : 0 ≤ (1 - u) ^ ρ := (Real.rpow_pos_of_pos hu' ρ).le
      have key : (1 - u) ^ ρ * (ρ * Y u / (1 - u)) = ρ * (1 - u) ^ (ρ - 1) * Y u := by
        rw [Real.rpow_sub_one hu'.ne']
        field_simp
      have := mul_le_mul_of_nonneg_left (hi u hu) hwp
      rw [mul_add, key] at this
      linarith
  have h1 : Z v ≤ Z s := hanti ⟨le_rfl, hsv⟩ ⟨hsv, le_rfl⟩ hsv
  have hIs : I s = 0 := by simp [hI]
  simp only [hZ, hIs, sub_zero] at h1
  have hws : (0 : ℝ) < 1 - s := hpos s ⟨le_rfl, hsv⟩
  have hwv : (0 : ℝ) < 1 - v := by linarith
  have hIv : I v ≤ (1 - s) ^ ρ * ∫ u in s..v, S u := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hsv ?_ ?_ ?_
    · exact (hIg.intervalIntegrable_of_Icc hsv)
    · exact ((hS.intervalIntegrable_of_Icc hsv).const_mul _)
    · intro t ht
      have ht' : 0 < 1 - t := hpos t ht
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow ht'.le (by linarith [ht.1]) hρ) (hS0 t ht)
  have h2 : (1 - v) ^ ρ * Y v ≤ (1 - s) ^ ρ * (Y s + ∫ u in s..v, S u) := by
    simp only [hI] at hIv ⊢
    nlinarith [h1, hIv]
  rw [Real.div_rpow hws.le hwv.le, div_mul_eq_mul_div, le_div_iff₀ (Real.rpow_pos_of_pos hwv ρ)]
  linarith


/-- Shifted moment comparison: if `2 p q = 1`, `δ > 0` and `f' ≤ 2p f^{1-q} a + (2p²-p) f^{1-2q} b`
with `f, a, b ≥ 0`, then `(f v + δ)^q ≤ √((f s + δ)^{2q} + (2p-1) ∫ b) + ∫ a`. -/
private lemma comparison_moment_pos {f f' a b : ℝ → ℝ} {s v : ℝ} (p : ℕ) (hp : 1 ≤ p)
    (hsv : s ≤ v) {q δ : ℝ} (hq : 2 * (p : ℝ) * q = 1) (hq0 : 0 < q) (hδ : 0 < δ)
    (hf0 : ∀ u ∈ Set.Icc s v, 0 ≤ f u) (ha : ∀ u ∈ Set.Icc s v, 0 ≤ a u)
    (hb : ∀ u ∈ Set.Icc s v, 0 ≤ b u)
    (hfc : ContinuousOn f (Set.Icc s v)) (hac : ContinuousOn a (Set.Icc s v))
    (hbc : ContinuousOn b (Set.Icc s v))
    (hderiv : ∀ u ∈ Set.Ioo s v, HasDerivAt f (f' u) u)
    (hbound : ∀ u ∈ Set.Ioo s v, f' u ≤ 2 * p * f u ^ (1 - q) * a u
        + (2 * (p : ℝ) ^ 2 - p) * f u ^ (1 - 2 * q) * b u) :
    (f v + δ) ^ q ≤
      Real.sqrt ((f s + δ) ^ (2 * q) + (2 * p - 1) * ∫ u in s..v, b u) + ∫ u in s..v, a u := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hq12 : 2 * q ≤ 1 := by nlinarith
  have hqp : q * p = 1 / 2 := by linarith
  have hIb : ∀ u ∈ Set.Icc s v, 0 ≤ ∫ t in s..u, b t := fun u hu =>
    intervalIntegral.integral_nonneg hu.1 fun t ht => hb t ⟨ht.1, ht.2.trans hu.2⟩
  have hIa : ∀ u ∈ Set.Icc s v, 0 ≤ ∫ t in s..u, a t := fun u hu =>
    intervalIntegral.integral_nonneg hu.1 fun t ht => ha t ⟨ht.1, ht.2.trans hu.2⟩
  have hm : ∀ u ∈ Set.Icc s v, 0 < f u + δ := fun u hu => by linarith [hf0 u hu]
  have hfs : (0 : ℝ) < f s + δ := hm s ⟨le_rfl, hsv⟩
  have hGpos : ∀ u ∈ Set.Icc s v, 0 < (f s + δ) ^ (2 * q) + (2 * p - 1) * ∫ t in s..u, b t :=
    fun u hu => by
      have := Real.rpow_pos_of_pos hfs (2 * q)
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * p - 1) (hIb u hu)
      linarith
  -- the comparison function `φ = w - z`
  have hwc : ContinuousOn (fun u => (f u + δ) ^ q) (Set.Icc s v) :=
    ContinuousOn.rpow_const (hfc.add continuousOn_const) fun u hu => Or.inl (hm u hu).ne'
  have hGc : ContinuousOn (fun u => (f s + δ) ^ (2 * q) + (2 * p - 1) * ∫ t in s..u, b t)
      (Set.Icc s v) :=
    continuousOn_const.add (continuousOn_const.mul (comparison_continuousOn_primitive hsv hbc))
  have hzc : ContinuousOn
      (fun u => Real.sqrt ((f s + δ) ^ (2 * q) + (2 * p - 1) * ∫ t in s..u, b t) +
        ∫ t in s..u, a t) (Set.Icc s v) :=
    hGc.sqrt.add (comparison_continuousOn_primitive hsv hac)
  have hwd : ∀ u ∈ Set.Ioo s v, HasDerivAt (fun u => (f u + δ) ^ q)
      (f' u * q * (f u + δ) ^ (q - 1)) u := fun u hu =>
    ((hderiv u hu).add_const δ).rpow_const (Or.inl (hm u (Set.Ioo_subset_Icc_self hu)).ne')
  have hzd : ∀ u ∈ Set.Ioo s v, HasDerivAt
      (fun u => Real.sqrt ((f s + δ) ^ (2 * q) + (2 * p - 1) * ∫ t in s..u, b t) +
        ∫ t in s..u, a t)
      ((2 * p - 1) * b u / (2 * Real.sqrt ((f s + δ) ^ (2 * q) +
        (2 * p - 1) * ∫ t in s..u, b t)) + a u) u := by
    intro u hu
    have hG : HasDerivAt (fun u => (f s + δ) ^ (2 * q) + (2 * p - 1) * ∫ t in s..u, b t)
        ((2 * p - 1) * b u) u :=
      ((comparison_hasDerivAt_primitive hbc hu).const_mul (2 * (p : ℝ) - 1)).const_add _
    exact (hG.sqrt (hGpos u (Set.Ioo_subset_Icc_self hu)).ne').add
      (comparison_hasDerivAt_primitive hac hu)
  have hφ := comparison_nonpos_of_deriv_nonpos
    (φ := fun u => (f u + δ) ^ q - (Real.sqrt ((f s + δ) ^ (2 * q) +
      (2 * p - 1) * ∫ t in s..u, b t) + ∫ t in s..u, a t))
    (φ' := fun u => f' u * q * (f u + δ) ^ (q - 1) -
      ((2 * p - 1) * b u / (2 * Real.sqrt ((f s + δ) ^ (2 * q) +
        (2 * p - 1) * ∫ t in s..u, b t)) + a u))
    (s := s) (v := v) (hwc.sub hzc) (fun u hu => (hwd u hu).sub (hzd u hu)) ?_ ?_
  · have := hφ v ⟨hsv, le_rfl⟩
    linarith
  · -- initial value
    simp only [intervalIntegral.integral_same, mul_zero, add_zero]
    have h2 : (f s + δ) ^ (2 * q) = ((f s + δ) ^ q) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hfs.le]
      push_cast; ring_nf
    rw [h2, Real.sqrt_sq (Real.rpow_nonneg hfs.le _)]
    linarith
  · -- the derivative is nonpositive where `φ > 0`
    intro u hu hφu
    have huI : u ∈ Set.Icc s v := Set.Ioo_subset_Icc_self hu
    have hmu := hm u huI
    have hW : 0 < (f u + δ) ^ q := Real.rpow_pos_of_pos hmu q
    set m := f u + δ with hmdef
    have hfu := hf0 u huI
    have hau := ha u huI
    have hbu := hb u huI
    have hb1 : f u ^ (1 - q) ≤ m ^ (1 - q) :=
      Real.rpow_le_rpow hfu (by linarith) (by linarith)
    have hb2 : f u ^ (1 - 2 * q) ≤ m ^ (1 - 2 * q) :=
      Real.rpow_le_rpow hfu (by linarith) (by linarith)
    have hc1 : (0 : ℝ) ≤ 2 * p := by positivity
    have hc2 : (0 : ℝ) ≤ 2 * (p : ℝ) ^ 2 - p := by nlinarith
    have hB : f' u ≤ 2 * p * m ^ (1 - q) * a u + (2 * (p : ℝ) ^ 2 - p) * m ^ (1 - 2 * q) * b u :=
      (hbound u hu).trans (add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb1 hc1) hau)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb2 hc2) hbu))
    have e1 : m ^ (q - 1) * m ^ (1 - q) = 1 := by
      rw [← Real.rpow_add hmu]; simp
    have e2 : m ^ (q - 1) * m ^ (1 - 2 * q) = (m ^ q)⁻¹ := by
      rw [← Real.rpow_add hmu, ← Real.rpow_neg hmu.le]; congr 1; ring
    have hnn : 0 ≤ q * m ^ (q - 1) := mul_nonneg hq0.le (Real.rpow_nonneg hmu.le _)
    have key : f' u * q * m ^ (q - 1) ≤ a u + (2 * p - 1) * b u / (2 * m ^ q) := by
      calc f' u * q * m ^ (q - 1) = q * m ^ (q - 1) * f' u := by ring
        _ ≤ q * m ^ (q - 1) * (2 * p * m ^ (1 - q) * a u +
              (2 * (p : ℝ) ^ 2 - p) * m ^ (1 - 2 * q) * b u) :=
            mul_le_mul_of_nonneg_left hB hnn
        _ = (2 * p * q) * (m ^ (q - 1) * m ^ (1 - q)) * a u +
              (q * p * (2 * p - 1)) * (m ^ (q - 1) * m ^ (1 - 2 * q)) * b u := by ring
        _ = a u + (2 * p - 1) * b u / (2 * m ^ q) := by
            rw [e1, e2, hq, hqp]; field_simp
    set G := (f s + δ) ^ (2 * q) + (2 * p - 1) * ∫ t in s..u, b t with hGdef
    have hGp : 0 < G := hGpos u huI
    have hsG : 0 < Real.sqrt G := Real.sqrt_pos.mpr hGp
    have hlt : Real.sqrt G < m ^ q := by linarith [hIa u huI]
    have hdiv : (2 * p - 1) * b u / (2 * m ^ q) ≤ (2 * p - 1) * b u / (2 * Real.sqrt G) :=
      div_le_div_of_nonneg_left (mul_nonneg (by linarith) hbu) (by positivity)
        (by linarith)
    linarith

/-- Moment ODE comparison. -/
theorem moment_ode_comparison {f f' a b : ℝ → ℝ} {s v : ℝ} (p : ℕ) (hp : 1 ≤ p) (hsv : s ≤ v)
    (hf0 : ∀ u ∈ Set.Icc s v, 0 ≤ f u) (ha : ∀ u ∈ Set.Icc s v, 0 ≤ a u)
    (hb : ∀ u ∈ Set.Icc s v, 0 ≤ b u)
    (hfc : ContinuousOn f (Set.Icc s v)) (hac : ContinuousOn a (Set.Icc s v))
    (hbc : ContinuousOn b (Set.Icc s v))
    (hderiv : ∀ u ∈ Set.Ioo s v, HasDerivAt f (f' u) u)
    (hbound : ∀ u ∈ Set.Ioo s v, f' u ≤ 2 * p * f u ^ (1 - 1 / (2 * (p : ℝ))) * a u
        + (2 * (p : ℝ) ^ 2 - p) * f u ^ (1 - 1 / (p : ℝ)) * b u) :
    f v ^ (1 / (2 * (p : ℝ))) ≤
      Real.sqrt (f s ^ (1 / (p : ℝ)) + (2 * p - 1) * ∫ u in s..v, b u)
        + ∫ u in s..v, a u := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = 1 / (2 * (p : ℝ)) := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hqdef]; positivity
  have hq : 2 * (p : ℝ) * q = 1 := by rw [hqdef]; field_simp
  have hq2 : 1 / (p : ℝ) = 2 * q := by rw [hqdef]; field_simp
  rw [← hqdef, hq2] at hbound ⊢
  have hlim : ∀ δ : ℝ, 0 < δ → (f v + δ) ^ q ≤
      Real.sqrt ((f s + δ) ^ (2 * q) + (2 * p - 1) * ∫ u in s..v, b u) + ∫ u in s..v, a u :=
    fun δ hδ => comparison_moment_pos p hp hsv hq hq0 hδ hf0 ha hb hfc hac hbc hderiv hbound
  have ht1 : Tendsto (fun δ : ℝ => (f v + δ) ^ q) (𝓝[>] 0) (𝓝 (f v ^ q)) := by
    have : ContinuousAt (fun δ : ℝ => (f v + δ) ^ q) 0 :=
      (continuousAt_const.add continuousAt_id).rpow_const (Or.inr hq0.le)
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  have ht2 : Tendsto (fun δ : ℝ => Real.sqrt ((f s + δ) ^ (2 * q) +
      (2 * p - 1) * ∫ u in s..v, b u) + ∫ u in s..v, a u) (𝓝[>] 0)
      (𝓝 (Real.sqrt (f s ^ (2 * q) + (2 * p - 1) * ∫ u in s..v, b u) + ∫ u in s..v, a u)) := by
    have : ContinuousAt (fun δ : ℝ => Real.sqrt ((f s + δ) ^ (2 * q) +
        (2 * p - 1) * ∫ u in s..v, b u) + ∫ u in s..v, a u) 0 := by
      refine ((ContinuousAt.rpow_const (continuousAt_const.add continuousAt_id)
        (Or.inr (by linarith))).add continuousAt_const).sqrt.add continuousAt_const
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto ht1 ht2 (eventually_nhdsWithin_of_forall fun δ hδ => hlim δ hδ)

/-- Cooperative `2 × 2` comparison: with the Perron root `ρ` and the left eigenvector `(1, λ₂)`,
`F(v) + λ₂ e(v) ≤ R^ρ (F(s) + λ₂ e(s) + ∫ (s_F + λ₂ s_e))`, `R = (1-s)/(1-v)`. -/
theorem coop2_comparison {F e F' e' sF se : ℝ → ℝ} {s v a11 a12 a21 a22 : ℝ} (hsv : s ≤ v)
    (hv : v < 1) (h11 : 0 ≤ a11) (h12 : 0 < a12) (h21 : 0 < a21) (h22 : 0 ≤ a22)
    (hF : ContinuousOn F (Set.Icc s v)) (he : ContinuousOn e (Set.Icc s v))
    (hsF : ContinuousOn sF (Set.Icc s v)) (hse : ContinuousOn se (Set.Icc s v))
    (hsF0 : ∀ u ∈ Set.Icc s v, 0 ≤ sF u) (hse0 : ∀ u ∈ Set.Icc s v, 0 ≤ se u)
    (hFd : ∀ u ∈ Set.Ioo s v, HasDerivAt F (F' u) u) (hed : ∀ u ∈ Set.Ioo s v, HasDerivAt e (e' u) u)
    (hFi : ∀ u ∈ Set.Ioo s v, F' u ≤ (a11 * F u + a12 * e u) / (1 - u) + sF u)
    (hei : ∀ u ∈ Set.Ioo s v, e' u ≤ (a21 * F u + a22 * e u) / (1 - u) + se u) :
    F v + a12 / ((a11 + a22) / 2 + Real.sqrt (((a11 - a22) / 2) ^ 2 + a12 * a21) - a22) * e v ≤
      ((1 - s) / (1 - v)) ^ ((a11 + a22) / 2 + Real.sqrt (((a11 - a22) / 2) ^ 2 + a12 * a21)) *
        (F s + a12 / ((a11 + a22) / 2 + Real.sqrt (((a11 - a22) / 2) ^ 2 + a12 * a21) - a22) * e s +
          ∫ u in s..v, (sF u + a12 / ((a11 + a22) / 2 +
            Real.sqrt (((a11 - a22) / 2) ^ 2 + a12 * a21) - a22) * se u)) := by
  set q := Real.sqrt (((a11 - a22) / 2) ^ 2 + a12 * a21) with hq
  set ρ := (a11 + a22) / 2 + q with hρ
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = ((a11 - a22) / 2) ^ 2 + a12 * a21 :=
    Real.sq_sqrt (by positivity)
  have hρa : 0 < ρ - a22 := by
    by_contra hle
    have hle' : ρ - a22 ≤ 0 := not_lt.mp hle
    have : q ≤ -((a11 - a22) / 2) := by simp only [hρ] at hle'; linarith
    nlinarith [mul_pos h12 h21]
  have hρ0 : 0 ≤ ρ := by linarith
  set l := a12 / (ρ - a22) with hl
  have hl0 : 0 < l := div_pos h12 hρa
  have heig2 : a12 + l * a22 = ρ * l := by
    rw [hl]; field_simp; ring
  have heig1 : a11 + l * a21 = ρ := by
    have hprod : (ρ - a11) * (ρ - a22) = a12 * a21 := by
      simp only [hρ]; nlinarith [hq2]
    have : l * a21 = ρ - a11 := by
      rw [hl, div_mul_eq_mul_div, div_eq_iff hρa.ne']
      linarith
    linarith
  clear_value l ρ q
  have hmain := comparison_weighted (Y := fun u => F u + l * e u)
    (Y' := fun u => F' u + l * e' u) (S := fun u => sF u + l * se u) (s := s) (v := v) (ρ := ρ)
    hsv hv hρ0 (hF.add (continuousOn_const.mul he)) (hsF.add (continuousOn_const.mul hse))
    (fun u hu => add_nonneg (hsF0 u hu) (mul_nonneg hl0.le (hse0 u hu)))
    (fun u hu => (hFd u hu).add ((hed u hu).const_mul l))
    (fun u hu => by
      have h1u : (0 : ℝ) < 1 - u := by linarith [hu.2]
      have hsum := add_le_add (hFi u hu) (mul_le_mul_of_nonneg_left (hei u hu) hl0.le)
      refine hsum.trans (le_of_eq ?_)
      field_simp
      linear_combination (F u) * heig1 + (e u) * heig2)
  exact hmain

/-- The moment-from-tail bound: `X ≥ 0`, `E X^{2r} ≤ K^{2r}`, `ℙ(X > Ψ) ≤ δ` give
`‖X‖_r ≤ Ψ + K δ^{1/(2r)}`. -/
theorem moment_of_tail {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    (X : Ω' → ℝ) (hX0 : ∀ ω, 0 ≤ X ω) (hXm : AEStronglyMeasurable X P) (r : ℕ) (hr : 1 ≤ r)
    (K Ψ δ : ℝ) (hK : 0 ≤ K) (hΨ : 0 ≤ Ψ) (hδ : 0 ≤ δ)
    (hint : Integrable (fun ω => X ω ^ (2 * r)) P) (hKm : ∫ ω, X ω ^ (2 * r) ∂P ≤ K ^ (2 * r))
    (htail : (P {ω | Ψ < X ω}).toReal ≤ δ) :
    (∫ ω, X ω ^ r ∂P) ^ (1 / (r : ℝ)) ≤ Ψ + K * δ ^ (1 / (2 * (r : ℝ))) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hrne : r ≠ 0 := by omega
  -- the tail event is null-measurable; take a measurable superset of the same measure
  obtain ⟨t, hAt, ht, htA⟩ : ∃ t : Set Ω', {ω | Ψ < X ω} ⊆ t ∧ MeasurableSet t ∧
      t =ᵐ[P] {ω | Ψ < X ω} :=
    (nullMeasurableSet_lt aemeasurable_const hXm.aemeasurable).exists_measurable_superset_ae_eq
  have hPt : P t = P {ω | Ψ < X ω} := measure_congr htA
  set f : Ω' → ℝ := fun ω => X ω ^ r with hf
  set g : Ω' → ℝ := t.indicator (fun _ => (1 : ℝ)) with hg
  have hfm : AEStronglyMeasurable f P := hXm.pow r
  have hgm : AEStronglyMeasurable g P := (aestronglyMeasurable_const.indicator ht)
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω => pow_nonneg (hX0 ω) r
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω => by
    simp only [hg, Set.indicator]; split_ifs <;> norm_num
  have hf2 : ∀ ω, f ω ^ 2 = X ω ^ (2 * r) := fun ω => by
    simp only [hf]; rw [← pow_mul, mul_comm]
  have hfL2 : MemLp f 2 P := by
    rw [memLp_two_iff_integrable_sq hfm]
    simpa [hf2] using hint
  have hgL2 : MemLp g 2 P := by
    refine MemLp.of_bound hgm 1 (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hg, Set.indicator]; split_ifs <;> norm_num
  have hfint : Integrable f P := hfL2.integrable one_le_two
  have hfgint : Integrable (fun ω => f ω * g ω) P := hfL2.integrable_mul hgL2
  -- pointwise: X^r ≤ Ψ^r + X^r 1_t
  have hpt : ∀ ω, f ω ≤ Ψ ^ r + f ω * g ω := by
    intro ω
    by_cases h : ω ∈ t
    · simp only [hg, Set.indicator_of_mem h, mul_one]
      have : 0 ≤ Ψ ^ r := pow_nonneg hΨ r
      linarith
    · have hle : X ω ≤ Ψ := by
        by_contra hlt
        exact h (hAt (not_le.mp hlt))
      simp only [hg, Set.indicator_of_notMem h, mul_zero, add_zero]
      exact pow_le_pow_left₀ (hX0 ω) hle r
  have h1 : ∫ ω, f ω ∂P ≤ Ψ ^ r + ∫ ω, f ω * g ω ∂P := by
    calc ∫ ω, f ω ∂P ≤ ∫ ω, (Ψ ^ r + f ω * g ω) ∂P :=
          integral_mono hfint ((integrable_const _).add hfgint) hpt
      _ = Ψ ^ r + ∫ ω, f ω * g ω ∂P := by
          rw [integral_add (integrable_const _) hfgint]; simp
  -- Cauchy–Schwarz
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := P) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0)
    (by simpa using hfL2) (by simpa using hgL2)
  have hfq : ∫ ω, f ω ^ (2 : ℝ) ∂P = ∫ ω, X ω ^ (2 * r) ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Real.rpow_two]; exact hf2 ω
  have hgq : ∫ ω, g ω ^ (2 : ℝ) ∂P = (P {ω | Ψ < X ω}).toReal := by
    have : (fun ω => g ω ^ (2 : ℝ)) = t.indicator 1 := by
      funext ω
      simp only [hg, Set.indicator, Pi.one_apply]
      split_ifs <;> norm_num
    rw [this, integral_indicator_one ht, measureReal_def, hPt]
  rw [hfq, hgq] at hCS
  have hKr : 0 ≤ K ^ r := pow_nonneg hK r
  have h2 : ∫ ω, f ω * g ω ∂P ≤ K ^ r * δ ^ (1 / 2 : ℝ) := by
    refine hCS.trans ?_
    have hA : (∫ ω, X ω ^ (2 * r) ∂P) ^ (1 / 2 : ℝ) ≤ K ^ r := by
      calc (∫ ω, X ω ^ (2 * r) ∂P) ^ (1 / 2 : ℝ) ≤ (K ^ (2 * r)) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (integral_nonneg fun ω => pow_nonneg (hX0 ω) _) hKm (by norm_num)
        _ = K ^ r := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hK]
            push_cast
            rw [show (2 * (r : ℝ)) * (1 / 2) = r by ring, Real.rpow_natCast]
    have hB : (P {ω | Ψ < X ω}).toReal ^ (1 / 2 : ℝ) ≤ δ ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow ENNReal.toReal_nonneg htail (by norm_num)
    simpa using mul_le_mul hA hB (Real.rpow_nonneg ENNReal.toReal_nonneg _) hKr
  -- assemble
  have hβ : 0 ≤ K * δ ^ (1 / (2 * (r : ℝ))) := mul_nonneg hK (Real.rpow_nonneg hδ _)
  have hβr : (K * δ ^ (1 / (2 * (r : ℝ)))) ^ r = K ^ r * δ ^ (1 / 2 : ℝ) := by
    rw [mul_pow, ← Real.rpow_natCast (δ ^ (1 / (2 * (r : ℝ)))) r,
      ← Real.rpow_mul hδ]
    congr 2
    field_simp
  have h3 : ∫ ω, f ω ∂P ≤ (Ψ + K * δ ^ (1 / (2 * (r : ℝ)))) ^ r := by
    calc ∫ ω, f ω ∂P ≤ Ψ ^ r + K ^ r * δ ^ (1 / 2 : ℝ) := h1.trans (by linarith)
      _ = Ψ ^ r + (K * δ ^ (1 / (2 * (r : ℝ)))) ^ r := by rw [hβr]
      _ ≤ (Ψ + K * δ ^ (1 / (2 * (r : ℝ)))) ^ r := pow_add_pow_le hΨ hβ hrne
  have hnn : 0 ≤ ∫ ω, f ω ∂P := integral_nonneg hf0
  calc (∫ ω, X ω ^ r ∂P) ^ (1 / (r : ℝ)) ≤ ((Ψ + K * δ ^ (1 / (2 * (r : ℝ)))) ^ r) ^ (1 / (r : ℝ)) :=
        Real.rpow_le_rpow hnn h3 (by positivity)
    _ = Ψ + K * δ ^ (1 / (2 * (r : ℝ))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        rw [mul_one_div_cancel hr0.ne', Real.rpow_one]

end LSBA
