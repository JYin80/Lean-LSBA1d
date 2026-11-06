import LSBA.Dyson.Boundary
import LSBA.Dyson.Distribution

/-!
# The band of `ν_g`

The band edge `e_g = inf_{x > 2b}(x + γ_g (x² − 4b²)^{-1/2})`, `b = √γ_g g`, with its minimizer;
`2 ≤ e_g ≤ (2g + 2)/max{1, g}`; the quartic form of (1.9) [eq:dyson] at real `z`; the single band
`Im m_g(E + i0) > 0 ⇔ |E| < e_g`; and inside the band the boundary value solves (1.9) [eq:dyson] at
`z = E` (Section 1.1 [sec:model] after (1.10) [eq:distribution]; Lemma A.2 [bl:lem:regular]).
-/

open MeasureTheory Real Filter Topology Complex
open scoped ENNReal

noncomputable section

open scoped Classical

namespace LSBA

/-- Band edge `e_g = inf_{x > 2b} (x + γ_g (x² - 4b²)^{-1/2})`, `b = √γ_g g`: the edge of the
single band of `ν_g` (Section 1.1 [sec:model] after (1.10) [eq:distribution]; Lemma A.2
[bl:lem:regular]). -/
def bandEdge (g : ℝ) : ℝ :=
  ⨅ x : Set.Ioi (2 * hopB g),
    ((x : ℝ) + gammaG g / Real.sqrt ((x : ℝ) ^ 2 - 4 * hopB g ^ 2))

/-! ### The parameters and the infimand -/

private lemma band_gamma_pos (g : ℝ) : 0 < gammaG g := by
  unfold gammaG
  have : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  positivity

private lemma band_gamma_le_one (g : ℝ) : gammaG g ≤ 1 := by
  unfold gammaG
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_max_left _ _))

private lemma band_hopB_nonneg {g : ℝ} (hg : 0 ≤ g) : 0 ≤ hopB g := by
  unfold hopB
  exact div_nonneg hg (lt_of_lt_of_le one_pos (le_max_left _ _)).le

private lemma band_hopB_le_one (g : ℝ) : hopB g ≤ 1 := by
  unfold hopB
  exact div_le_one_of_le₀ (le_max_right _ _) (lt_of_lt_of_le one_pos (le_max_left _ _)).le

/-- For `g ≤ 1`: `b = g` and `γ_g = 1`. -/
private lemma band_small {g : ℝ} (h1 : g ≤ 1) : hopB g = g ∧ gammaG g = 1 := by
  unfold hopB gammaG
  rw [max_eq_left h1]
  norm_num

/-- For `g ≥ 1`: `b = 1` and `γ_g = g⁻²`. -/
private lemma band_large {g : ℝ} (h1 : 1 ≤ g) : hopB g = 1 ∧ gammaG g = (g ^ 2)⁻¹ := by
  unfold hopB gammaG
  rw [max_eq_right h1]
  exact ⟨div_self (by linarith), rfl⟩

/-- The infimand `H(x) = x + γ_g (x² - 4b²)^{-1/2}`. -/
private def bandH (g x : ℝ) : ℝ := x + gammaG g / Real.sqrt (x ^ 2 - 4 * hopB g ^ 2)

private lemma band_sq_pos {g x : ℝ} (hg : 0 ≤ g) (hx : 2 * hopB g < x) :
    0 < x ^ 2 - 4 * hopB g ^ 2 := by
  have := band_hopB_nonneg hg
  nlinarith

private lemma bandH_nonneg {g x : ℝ} (hg : 0 ≤ g) (hx : 2 * hopB g < x) : 0 ≤ bandH g x := by
  have := band_hopB_nonneg hg
  have := band_gamma_pos g
  unfold bandH
  have : 0 ≤ gammaG g / Real.sqrt (x ^ 2 - 4 * hopB g ^ 2) := by positivity
  linarith

private lemma bandEdge_le_bandH {g x : ℝ} (hg : 0 ≤ g) (hx : 2 * hopB g < x) :
    bandEdge g ≤ bandH g x :=
  ciInf_le (f := fun y : Set.Ioi (2 * hopB g) => bandH g y)
    ⟨0, by rintro _ ⟨y, rfl⟩; exact bandH_nonneg hg y.2⟩ ⟨x, hx⟩

/-- At a critical point `γ_g β = (β² - 4b²)^{3/2}`, `H(β) ≤ H(x)` for every `x > 2b`. -/
private lemma bandH_ge {g x β : ℝ} (hg : 0 ≤ g) (hx : 2 * hopB g < x) (hβ : 2 * hopB g < β)
    (hcrit : gammaG g * β = Real.sqrt (β ^ 2 - 4 * hopB g ^ 2) ^ 3) :
    bandH g β ≤ bandH g x := by
  have hb := band_hopB_nonneg hg
  set b := hopB g
  set γ := gammaG g
  set s := Real.sqrt (x ^ 2 - 4 * b ^ 2) with hsdef
  set t := Real.sqrt (β ^ 2 - 4 * b ^ 2) with htdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr (band_sq_pos hg hx)
  have ht0 : 0 < t := Real.sqrt_pos.mpr (band_sq_pos hg hβ)
  have hs2 : x ^ 2 = s ^ 2 + 4 * b ^ 2 := by
    rw [hsdef, Real.sq_sqrt (band_sq_pos hg hx).le]; ring
  have ht2 : β ^ 2 = t ^ 2 + 4 * b ^ 2 := by
    rw [htdef, Real.sq_sqrt (band_sq_pos hg hβ).le]; ring
  have hx0 : 0 < x := by linarith
  have hβ0 : 0 < β := by linarith
  have hγ : γ = t ^ 3 / β := by rw [eq_div_iff hβ0.ne']; exact hcrit
  set D := bandH g x - bandH g β with hD
  have key1 : D * (β * s) = β * s * (x - β) - t ^ 2 * (s - t) := by
    rw [hD]
    change (x + γ / s - (β + γ / t)) * (β * s) = _
    rw [hγ]
    field_simp
    ring
  have key2 : (β * s * (x - β) - t ^ 2 * (s - t)) * ((x + β) * (β * s + t * x)) =
      (s - t) ^ 2 * (s + t) * (β * (β * s + t * x) + 4 * b ^ 2 * t) := by
    linear_combination (β * s * (β * s + t * x) - (s - t) * t * t ^ 2) * hs2 +
      (-(β * s * (β * s + t * x)) + (s - t) * t * s ^ 2) * ht2
  have hP : 0 < β * s * ((x + β) * (β * s + t * x)) := by positivity
  have hR : 0 ≤ (s - t) ^ 2 * (s + t) * (β * (β * s + t * x) + 4 * b ^ 2 * t) := by positivity
  have hDP : D * (β * s * ((x + β) * (β * s + t * x))) =
      (s - t) ^ 2 * (s + t) * (β * (β * s + t * x) + 4 * b ^ 2 * t) := by
    rw [← key2, ← key1]; ring
  have : 0 ≤ D := by
    by_contra hneg
    have := mul_neg_of_neg_of_pos (not_le.mp hneg) hP
    linarith
  linarith

/-- If `β > 2b` is critical, `e_g = H(β)`. -/
private lemma bandEdge_eq_bandH {g β : ℝ} (hg : 0 ≤ g) (hβ : 2 * hopB g < β)
    (hcrit : gammaG g * β = Real.sqrt (β ^ 2 - 4 * hopB g ^ 2) ^ 3) :
    bandEdge g = bandH g β := by
  have : Nonempty (Set.Ioi (2 * hopB g)) := ⟨⟨β, hβ⟩⟩
  refine le_antisymm (bandEdge_le_bandH hg hβ) ?_
  exact le_ciInf (f := fun y : Set.Ioi (2 * hopB g) => bandH g y)
    fun y => bandH_ge hg y.2 hβ hcrit

/-- The minimizer `β > 2b` solves `γ_g β = (β² - 4b²)^{3/2}`, and `e_g = 2β - 4b²/β`. -/
theorem bandEdge_spec (g : ℝ) (hg : 0 ≤ g) :
    ∃ β : ℝ, 2 * hopB g < β ∧ gammaG g * β = Real.sqrt (β ^ 2 - 4 * hopB g ^ 2) ^ 3 ∧
      bandEdge g = β + gammaG g / Real.sqrt (β ^ 2 - 4 * hopB g ^ 2) ∧
      bandEdge g = 2 * β - 4 * hopB g ^ 2 / β := by
  have hb := band_hopB_nonneg hg
  have hb1 := band_hopB_le_one g
  have hγ := band_gamma_pos g
  have hγ1 := band_gamma_le_one g
  obtain ⟨T, ⟨hT1, hT2⟩, hT⟩ : ∃ T ∈ Set.Icc (gammaG g / 2) (2 + 4 * hopB g ^ 2),
      T ^ 3 - gammaG g ^ 2 * T - 4 * gammaG g ^ 2 * hopB g ^ 2 = 0 := by
    have hc : ContinuousOn (fun T : ℝ => T ^ 3 - gammaG g ^ 2 * T - 4 * gammaG g ^ 2 * hopB g ^ 2)
        (Set.Icc (gammaG g / 2) (2 + 4 * hopB g ^ 2)) := by fun_prop
    refine intermediate_value_Icc (by nlinarith) hc ⟨?_, ?_⟩
    · have : 0 ≤ gammaG g ^ 2 * hopB g ^ 2 := by positivity
      nlinarith [pow_pos hγ 3]
    · have h1 : gammaG g ^ 2 ≤ 1 := by nlinarith
      have h2 : 0 ≤ hopB g ^ 2 := sq_nonneg _
      set T := 2 + 4 * hopB g ^ 2 with hTdef
      have hT2 : 2 ≤ T := by linarith
      have hT4 : 4 ≤ T ^ 2 := by nlinarith
      have hT3 : 4 * T ≤ T ^ 3 := by
        nlinarith [mul_le_mul_of_nonneg_left hT4 (by linarith : (0 : ℝ) ≤ T)]
      have h3 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ T)
      have h4 := mul_le_mul_of_nonneg_right h1 h2
      nlinarith
  have hT0 : 0 < T := by linarith
  set β := Real.sqrt (T + 4 * hopB g ^ 2) with hβdef
  have hβ2 : β ^ 2 = T + 4 * hopB g ^ 2 := Real.sq_sqrt (by positivity)
  have hβ0 : 0 ≤ β := Real.sqrt_nonneg _
  have hβ : 2 * hopB g < β := by nlinarith
  have ht : Real.sqrt (β ^ 2 - 4 * hopB g ^ 2) = Real.sqrt T := by
    rw [hβ2]; ring_nf
  have hsT := Real.sq_sqrt hT0.le
  have hcrit : gammaG g * β = Real.sqrt (β ^ 2 - 4 * hopB g ^ 2) ^ 3 := by
    rw [ht]
    refine (sq_eq_sq₀ (by positivity) (by positivity)).1 ?_
    rw [mul_pow, hβ2, ← pow_mul, show 3 * 2 = 2 * 3 by rfl, pow_mul, hsT]
    linear_combination -hT
  refine ⟨β, hβ, hcrit, bandEdge_eq_bandH hg hβ hcrit, ?_⟩
  rw [bandEdge_eq_bandH hg hβ hcrit]
  unfold bandH
  have hβp : 0 < β := by linarith
  have ht0 : 0 < Real.sqrt (β ^ 2 - 4 * hopB g ^ 2) := Real.sqrt_pos.mpr (band_sq_pos hg hβ)
  have ht2 := Real.sq_sqrt (band_sq_pos hg hβ).le
  have e : gammaG g / Real.sqrt (β ^ 2 - 4 * hopB g ^ 2) = (β ^ 2 - 4 * hopB g ^ 2) / β := by
    rw [div_eq_div_iff ht0.ne' hβp.ne', hcrit]
    nth_rewrite 2 [← ht2]
    ring
  rw [e]
  field_simp
  ring

/-- `e_g ≥ 2`, strictly for `g > 0`. -/
theorem bandEdge_ge_two (g : ℝ) (hg : 0 ≤ g) : 2 ≤ bandEdge g ∧ (0 < g → 2 < bandEdge g) := by
  obtain ⟨β, hβ, -, he, -⟩ := bandEdge_spec g hg
  have hb := band_hopB_nonneg hg
  have hβ0 : 0 < β := by linarith
  have ht0 : 0 < Real.sqrt (β ^ 2 - 4 * hopB g ^ 2) := Real.sqrt_pos.mpr (band_sq_pos hg hβ)
  rw [he]
  rcases le_total g 1 with h1 | h1
  · obtain ⟨hbg, hγg⟩ := band_small h1
    rw [hγg]
    have hβ1 : 2 ≤ β + 1 / β := by
      have e : β + 1 / β - 2 = (β - 1) ^ 2 / β := by field_simp; ring
      have : 0 ≤ (β - 1) ^ 2 / β := by positivity
      linarith
    have htβ : Real.sqrt (β ^ 2 - 4 * hopB g ^ 2) ≤ β := by
      calc Real.sqrt (β ^ 2 - 4 * hopB g ^ 2) ≤ Real.sqrt (β ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith)
        _ = β := Real.sqrt_sq hβ0.le
    have h2 : 1 / β ≤ 1 / Real.sqrt (β ^ 2 - 4 * hopB g ^ 2) :=
      one_div_le_one_div_of_le ht0 htβ
    refine ⟨by linarith, fun hg0 => ?_⟩
    have htβ' : Real.sqrt (β ^ 2 - 4 * hopB g ^ 2) < β := by
      calc Real.sqrt (β ^ 2 - 4 * hopB g ^ 2) < Real.sqrt (β ^ 2) :=
            Real.sqrt_lt_sqrt (band_sq_pos hg hβ).le (by rw [hbg]; nlinarith)
        _ = β := Real.sqrt_sq hβ0.le
    have h3 : 1 / β < 1 / Real.sqrt (β ^ 2 - 4 * hopB g ^ 2) :=
      one_div_lt_one_div_of_lt ht0 htβ'
    linarith
  · obtain ⟨hbg, -⟩ := band_large h1
    have hγ := band_gamma_pos g
    have : 0 < gammaG g / Real.sqrt (β ^ 2 - 4 * hopB g ^ 2) := by positivity
    rw [hbg] at hβ
    exact ⟨by linarith, fun _ => by linarith⟩

/-- `e_g` lies within the support bound (1.12) [eq:bounded-physical-bulk]. -/
theorem bandEdge_le (g : ℝ) (hg : 0 ≤ g) : bandEdge g ≤ (2 * g + 2) / max 1 g := by
  have hM : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hx : 2 * hopB g < (2 * g + 1) / max 1 g := by
    unfold hopB
    rw [mul_div_assoc', div_lt_div_iff_of_pos_right hM]
    linarith
  refine (bandEdge_le_bandH hg hx).trans ?_
  unfold bandH
  have e : ((2 * g + 1) / max 1 g) ^ 2 - 4 * hopB g ^ 2 = (4 * g + 1) / max 1 g ^ 2 := by
    unfold hopB
    field_simp
    ring
  rw [e]
  have hs : 1 / max 1 g ≤ Real.sqrt ((4 * g + 1) / max 1 g ^ 2) := by
    calc 1 / max 1 g = Real.sqrt ((1 / max 1 g) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt ((4 * g + 1) / max 1 g ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [div_pow, one_pow]
          exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have h2 : gammaG g / Real.sqrt ((4 * g + 1) / max 1 g ^ 2) ≤ gammaG g / (1 / max 1 g) :=
    div_le_div_of_nonneg_left (band_gamma_pos g).le (by positivity) hs
  have h3 : gammaG g / (1 / max 1 g) = 1 / max 1 g := by
    unfold gammaG
    field_simp
  rw [h3] at h2
  have h4 : (2 * g + 1) / max 1 g + 1 / max 1 g = (2 * g + 2) / max 1 g := by
    field_simp; ring
  linarith

set_option linter.unusedVariables false in
/-- (1.9) [eq:dyson] is the quartic in `ℂ_+` also at real `z`. -/
theorem dyson_iff_quartic' (g : ℝ) (hg : 0 ≤ g) (z : ℂ) (hz : 0 ≤ z.im) (u : ℂ) (hu : 0 < u.im) :
    u = dysonRHS g z u ↔ u ^ 2 * ((z + gammaG g * u) ^ 2 - 4 * (hopB g : ℂ) ^ 2) = 1 := by
  have hγ := band_gamma_pos g
  have hwim : 0 < (z + (gammaG g : ℂ) * u).im := by
    rw [Complex.add_im, Complex.im_ofReal_mul]
    positivity
  rw [dysonRHS_eq_freeT, freeT_eq _ _ hwim, ← freeS_sq (hopB g) (z + (gammaG g : ℂ) * u)]
  set s := freeS (hopB g) (z + (gammaG g : ℂ) * u) with hs
  have hsim : 0 < s.im := freeS_im_pos _ _ hwim
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_im] at hsim; exact lt_irrefl _ hsim
  constructor
  · intro h
    rw [h]
    field_simp
  · intro h
    have h2 : (u * s - 1) * (u * s + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exfalso
      have h4 : s = u⁻¹ := by
        have : u * s = 1 := by linear_combination h3
        exact eq_inv_of_mul_eq_one_right this
      have h5 : s.im = -u.im / Complex.normSq u := by rw [h4, Complex.inv_im]
      have h6 : 0 < Complex.normSq u := Complex.normSq_pos.mpr (fun h => by simp [h] at hu)
      have : s.im < 0 := by rw [h5]; exact div_neg_of_neg_of_pos (by linarith) h6
      linarith
    · have : u * s = -1 := by linear_combination h3
      have h4 : u * (-s) = 1 := by linear_combination -this
      rw [← inv_neg]
      exact eq_inv_of_mul_eq_one_left h4

/-! ### Roots of the quartic at a real energy

The single band of Section 1.1 [sec:model] after (1.10) [eq:distribution] and Lemma 1.2
[da:lem:distribution]: the quartic has two real roots at every real `E`, and a third for
`|E| ≥ e_g`. -/

/-- The quartic form `u²((E + γ_g u)² - 4b²) - 1` of (1.9) [eq:dyson] at real `z = E`. -/
private def bandQ (g E : ℝ) (u : ℂ) : ℂ :=
  u ^ 2 * (((E : ℂ) + gammaG g * u) ^ 2 - 4 * (hopB g : ℂ) ^ 2) - 1

open Polynomial in
/-- Distinct roots of `bandQ g E` are at most four. -/
private lemma bandQ_card (g E : ℝ) (l : List ℂ) (hl : l.Nodup) (hr : ∀ x ∈ l, bandQ g E x = 0) :
    l.length ≤ 4 := by
  set p : ℂ[X] := C ((gammaG g : ℂ) ^ 2) * X ^ 4 + C (2 * (gammaG g : ℂ) * E) * X ^ 3 +
    C ((E : ℂ) ^ 2 - 4 * (hopB g : ℂ) ^ 2) * X ^ 2 - C 1 with hp
  have heval : ∀ x, p.eval x = bandQ g E x := by
    intro x
    simp only [hp, bandQ, eval_sub, eval_add, eval_mul, eval_C, eval_pow, eval_X]
    ring
  have hdeg : p.natDegree ≤ 4 := by rw [hp]; compute_degree
  have hp0 : p ≠ 0 := by
    intro h
    have h4 : p.coeff 4 = (gammaG g : ℂ) ^ 2 := by
      rw [hp]
      simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C]
      norm_num
    rw [h, coeff_zero] at h4
    exact pow_ne_zero 2 (by exact_mod_cast (band_gamma_pos g).ne') h4.symm
  have hle : (l : Multiset ℂ) ≤ p.roots := (Multiset.le_iff_subset (Multiset.coe_nodup.2 hl)).2
    fun x hx => (mem_roots hp0).2 (by rw [IsRoot, heval]; exact hr x hx)
  have := (Multiset.card_le_card hle).trans ((card_roots' p).trans hdeg)
  simpa using this

private lemma bandQ_conj (g E : ℝ) (u : ℂ) :
    bandQ g E ((starRingEnd ℂ) u) = (starRingEnd ℂ) (bandQ g E u) := by
  unfold bandQ
  simp only [map_sub, map_mul, map_pow, map_add, Complex.conj_ofReal, map_one, map_ofNat]

private lemma bandQ_real {g E r : ℝ} (h : r ^ 2 * ((E + gammaG g * r) ^ 2 - 4 * hopB g ^ 2) = 1) :
    bandQ g E r = 0 := by
  unfold bandQ
  have : ((r ^ 2 * ((E + gammaG g * r) ^ 2 - 4 * hopB g ^ 2) : ℝ) : ℂ) = 1 := by
    rw [h]; simp
  push_cast at this
  rw [this]
  ring

private lemma band_sqrt_cont {g : ℝ} (hg : 0 ≤ g) {a c : ℝ} (ha : 2 * hopB g < a) :
    ContinuousOn (fun x => gammaG g / Real.sqrt (x ^ 2 - 4 * hopB g ^ 2)) (Set.Icc a c) := by
  refine continuousOn_const.div (by fun_prop) fun x hx => ?_
  exact (Real.sqrt_pos.mpr (band_sq_pos hg (lt_of_lt_of_le ha hx.1))).ne'

/-- The second branch `K(x) = x - γ_g (x² - 4b²)^{-1/2}` takes every real value on `x > 2b`. -/
private lemma band_K_root {g : ℝ} (hg : 0 ≤ g) (E : ℝ) :
    ∃ x, 2 * hopB g < x ∧ x - gammaG g / Real.sqrt (x ^ 2 - 4 * hopB g ^ 2) = E := by
  have hb := band_hopB_nonneg hg
  have hb1 := band_hopB_le_one g
  have hγ := band_gamma_pos g
  have hE0 := abs_nonneg E
  set δ := gammaG g / (|E| + 3) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one (by positivity)]
    linarith [band_gamma_le_one g]
  set a := Real.sqrt (4 * hopB g ^ 2 + δ ^ 2) with ha
  have ha2 : a ^ 2 = 4 * hopB g ^ 2 + δ ^ 2 := Real.sq_sqrt (by positivity)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hab : 2 * hopB g < a := by nlinarith
  have haup : a ≤ 2 * hopB g + δ := by nlinarith
  set c := 2 * hopB g + |E| + 2 with hc
  have hac : a ≤ c := by linarith
  have hcont : ContinuousOn (fun x => x - gammaG g / Real.sqrt (x ^ 2 - 4 * hopB g ^ 2))
      (Set.Icc a c) := continuousOn_id.sub (band_sqrt_cont hg hab)
  have hlo : a - gammaG g / Real.sqrt (a ^ 2 - 4 * hopB g ^ 2) ≤ E := by
    have : Real.sqrt (a ^ 2 - 4 * hopB g ^ 2) = δ := by
      rw [ha2, show 4 * hopB g ^ 2 + δ ^ 2 - 4 * hopB g ^ 2 = δ ^ 2 by ring,
        Real.sqrt_sq hδ0.le]
    rw [this, show gammaG g / δ = |E| + 3 by rw [hδ]; field_simp]
    have := neg_abs_le E
    linarith
  have hhi : E ≤ c - gammaG g / Real.sqrt (c ^ 2 - 4 * hopB g ^ 2) := by
    have h1 : 1 ≤ Real.sqrt (c ^ 2 - 4 * hopB g ^ 2) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have h2 : gammaG g / Real.sqrt (c ^ 2 - 4 * hopB g ^ 2) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith [band_gamma_le_one g]
    have := le_abs_self E
    linarith
  obtain ⟨x, hx, hxE⟩ := intermediate_value_Icc hac hcont ⟨hlo, hhi⟩
  exact ⟨x, lt_of_lt_of_le hab hx.1, hxE⟩

/-- `H` takes every value `≥ e_g` on `x > 2b`. -/
private lemma band_H_root {g : ℝ} (hg : 0 ≤ g) {y : ℝ} (hy : bandEdge g ≤ y) :
    ∃ x, 2 * hopB g < x ∧ bandH g x = y := by
  obtain ⟨β, hβ, hcrit, -, -⟩ := bandEdge_spec g hg
  have he := bandEdge_eq_bandH hg hβ hcrit
  have hb := band_hopB_nonneg hg
  have hγ := band_gamma_pos g
  have hge : ∀ x, 2 * hopB g < x → x ≤ bandH g x := fun x hx => by
    unfold bandH
    have : 0 ≤ gammaG g / Real.sqrt (x ^ 2 - 4 * hopB g ^ 2) := by positivity
    linarith
  set c := 2 * hopB g + |y| + 2 with hc
  have hy' := le_abs_self y
  have hβc : β ≤ c := by
    have := hge β hβ
    linarith
  have hcont : ContinuousOn (bandH g) (Set.Icc β c) :=
    continuousOn_id.add (band_sqrt_cont hg hβ)
  have hhi : y ≤ bandH g c := by
    have := hge c (by linarith [abs_nonneg y])
    linarith
  obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc hβc hcont ⟨he ▸ hy, hhi⟩
  exact ⟨x, lt_of_lt_of_le hβ hx.1, hxy⟩

/-- Two real roots of `bandQ g E` for every `E`, on the second branch `E = ±K(±w)`. -/
private lemma band_two_roots {g : ℝ} (hg : 0 ≤ g) (E : ℝ) :
    ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ r₂ < 0 ∧ 2 * hopB g < E + gammaG g * r₁ ∧
      E + gammaG g * r₂ < -(2 * hopB g) ∧ bandQ g E r₁ = 0 ∧ bandQ g E r₂ = 0 := by
  obtain ⟨x₁, hx₁, h₁⟩ := band_K_root hg E
  obtain ⟨x₂, hx₂, h₂⟩ := band_K_root hg (-E)
  have ht₁ := Real.sqrt_pos.mpr (band_sq_pos hg hx₁)
  have ht₂ := Real.sqrt_pos.mpr (band_sq_pos hg hx₂)
  have hs₁ := Real.sq_sqrt (band_sq_pos hg hx₁).le
  have hs₂ := Real.sq_sqrt (band_sq_pos hg hx₂).le
  set t₁ := Real.sqrt (x₁ ^ 2 - 4 * hopB g ^ 2)
  set t₂ := Real.sqrt (x₂ ^ 2 - 4 * hopB g ^ 2)
  have e₁ : E + gammaG g * (1 / t₁) = x₁ := by rw [← h₁]; ring
  have e₂ : E + gammaG g * (-(1 / t₂)) = -x₂ := by linear_combination h₂
  refine ⟨1 / t₁, -(1 / t₂), by positivity, by
    have : 0 < 1 / t₂ := by positivity
    linarith, by rw [e₁]; exact hx₁, by rw [e₂]; linarith, bandQ_real ?_, bandQ_real ?_⟩
  · rw [e₁, ← hs₁]; field_simp
  · rw [e₂, neg_sq, neg_sq, ← hs₂]; field_simp

/-- For `|E| ≥ e_g` a third real root, on the first branch `|E| = H(|w|)`. -/
private lemma band_third_root {g : ℝ} (hg : 0 ≤ g) {E : ℝ} (hE : bandEdge g ≤ |E|) :
    ∃ r : ℝ, bandQ g E r = 0 ∧
      ((r < 0 ∧ 2 * hopB g < E + gammaG g * r) ∨ (0 < r ∧ E + gammaG g * r < -(2 * hopB g))) := by
  obtain ⟨x, hx, hxE⟩ := band_H_root hg hE
  have ht := Real.sqrt_pos.mpr (band_sq_pos hg hx)
  have hs := Real.sq_sqrt (band_sq_pos hg hx).le
  unfold bandH at hxE
  set t := Real.sqrt (x ^ 2 - 4 * hopB g ^ 2)
  have hb := band_hopB_nonneg hg
  rcases le_total 0 E with h0 | h0
  · rw [abs_of_nonneg h0] at hxE
    have e : E + gammaG g * (-(1 / t)) = x := by rw [← hxE]; ring
    refine ⟨-(1 / t), bandQ_real ?_, Or.inl ⟨by
      have : 0 < 1 / t := by positivity
      linarith, by rw [e]; exact hx⟩⟩
    rw [e, neg_sq, ← hs]; field_simp
  · rw [abs_of_nonpos h0] at hxE
    have e : E + gammaG g * (1 / t) = -x := by linear_combination hxE
    refine ⟨1 / t, bandQ_real ?_, Or.inr ⟨by positivity, by rw [e]; linarith⟩⟩
    rw [e, neg_sq, ← hs]; field_simp

/-- For `|E| ≥ e_g`, `bandQ g E` has no root in `ℂ_+`. -/
private lemma bandQ_no_upper {g : ℝ} (hg : 0 ≤ g) {E : ℝ} (hE : bandEdge g ≤ |E|) {u : ℂ}
    (hu : 0 < u.im) (hq : bandQ g E u = 0) : False := by
  obtain ⟨r₁, r₂, hr₁, hr₂, hw₁, hw₂, hq₁, hq₂⟩ := band_two_roots hg E
  obtain ⟨r₃, hq₃, hr₃⟩ := band_third_root hg hE
  have hγ := band_gamma_pos g
  have hb := band_hopB_nonneg hg
  have h12 : r₁ ≠ r₂ := by intro h; linarith
  have h13 : r₁ ≠ r₃ := by
    rintro rfl
    rcases hr₃ with ⟨h, -⟩ | ⟨-, h⟩ <;> linarith
  have h23 : r₂ ≠ r₃ := by
    rintro rfl
    rcases hr₃ with ⟨-, h⟩ | ⟨h, -⟩ <;> linarith
  have hlen := bandQ_card g E [u, (starRingEnd ℂ) u, (r₁ : ℂ), (r₂ : ℂ), (r₃ : ℂ)] ?_ ?_
  · simp at hlen
  · simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
      List.nodup_nil, and_true, not_false_eq_true]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    all_goals intro h
    all_goals first
      | exact h12 (by exact_mod_cast h)
      | exact h13 (by exact_mod_cast h)
      | exact h23 (by exact_mod_cast h)
      | (have := congrArg Complex.im h; simp at this; linarith)
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact hq
    · rw [bandQ_conj, hq, map_zero]
    · exact hq₁
    · exact hq₂
    · exact hq₃

/-! ### The sign rule at the boundary -/

/-- `s² = w² - 4b²` with `Im s, Im w > 0` forces `Re s · Re w ≥ 0`. -/
private lemma band_sign_of {s w : ℂ} {b : ℝ} (h : s ^ 2 = w ^ 2 - 4 * (b : ℂ) ^ 2)
    (hs : 0 < s.im) (hw : 0 < w.im) : 0 ≤ s.re * w.re := by
  have him : (s ^ 2).im = (w ^ 2 - 4 * (b : ℂ) ^ 2).im := by rw [h]
  simp only [sq, Complex.mul_im, Complex.sub_im, Complex.re_ofNat, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, add_zero, Complex.im_ofNat, Complex.mul_re,
    sub_zero] at him
  have key : (s.re * w.re) * s.im = w.re ^ 2 * w.im := by
    have : s.re * s.im = w.re * w.im := by linarith
    linear_combination w.re * this
  by_contra hn
  have := mul_neg_of_neg_of_pos (not_le.mp hn) hs
  have : 0 ≤ w.re ^ 2 * w.im := by positivity
  linarith

private lemma band_bdry_root {g : ℝ} (hg : 0 ≤ g) (E : ℝ) : bandQ g E (mDysonBdry g E) = 0 := by
  unfold bandQ
  rw [mDysonBdry_quartic g hg E, sub_self]

/-- The sign rule passes to the boundary value: `Re(-1/m) · Re(E + γ_g m) ≥ 0`. -/
private lemma band_bdry_sign {g : ℝ} (hg : 0 ≤ g) (E : ℝ) :
    0 ≤ (-(mDysonBdry g E)⁻¹).re * ((E : ℂ) + gammaG g * mDysonBdry g E).re := by
  have hq := mDysonBdry_quartic g hg E
  have hne : mDysonBdry g E ≠ 0 := by intro h; rw [h] at hq; simp at hq
  have hT := mDysonBdry_tendsto g hg E
  have hz : Tendsto (fun η : ℝ => (E : ℂ) + η * I) (𝓝[>] 0) (𝓝 (E : ℂ)) := by
    have : Continuous fun η : ℝ => (E : ℂ) + η * I := by fun_prop
    have h := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using h
  have hlim : Tendsto (fun η : ℝ => (-(mDyson g (E + η * I))⁻¹).re *
      (((E : ℂ) + η * I) + gammaG g * mDyson g (E + η * I)).re) (𝓝[>] 0)
      (𝓝 ((-(mDysonBdry g E)⁻¹).re * ((E : ℂ) + gammaG g * mDysonBdry g E).re)) := by
    refine Tendsto.mul ?_ ?_
    · exact (Complex.continuous_re.tendsto _).comp ((hT.inv₀ hne).neg)
    · exact (Complex.continuous_re.tendsto _).comp (hz.add (tendsto_const_nhds.mul hT))
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hzim : 0 < ((E : ℂ) + η * I).im := by simpa using hη
  obtain ⟨hm, hfix⟩ := mDyson_spec g hg _ hzim
  have hq' := (dyson_iff_quartic g hg _ hzim _ hm).1 hfix
  set u := mDyson g (E + η * I)
  have hu0 : u ≠ 0 := fun h => by rw [h] at hm; simp at hm
  apply band_sign_of (b := hopB g)
  · rw [neg_sq, inv_pow]
    have : u ^ 2 ≠ 0 := pow_ne_zero 2 hu0
    field_simp
    linear_combination -hq'
  · rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    have := Complex.normSq_pos.2 hu0
    positivity
  · have hγ := band_gamma_pos g
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, mul_zero, mul_one, zero_add, zero_mul, add_zero]
    have : 0 < η := hη
    positivity

/-- A real root on the first branch (sign rule) lies at `|E| ≥ e_g`. -/
private lemma band_edge_le_of_real {g : ℝ} (hg : 0 ≤ g) {E v : ℝ}
    (hq : v ^ 2 * ((E + gammaG g * v) ^ 2 - 4 * hopB g ^ 2) = 1)
    (hs : 0 ≤ -v⁻¹ * (E + gammaG g * v)) : bandEdge g ≤ |E| := by
  have hb := band_hopB_nonneg hg
  have hv0 : v ≠ 0 := by rintro rfl; simp at hq
  have hT : (E + gammaG g * v) ^ 2 - 4 * hopB g ^ 2 = (v⁻¹) ^ 2 := by
    field_simp; linear_combination hq
  have hTpos : 0 < (E + gammaG g * v) ^ 2 - 4 * hopB g ^ 2 := by rw [hT]; positivity
  rcases lt_trichotomy (E + gammaG g * v) 0 with hw0 | hw0 | hw0
  · have hvpos : 0 < v := by
      by_contra hn
      have hvn : v < 0 := lt_of_le_of_ne (not_lt.mp hn) hv0
      have : 0 < -v⁻¹ := neg_pos.mpr (inv_lt_zero.mpr hvn)
      have := mul_neg_of_pos_of_neg this hw0
      linarith
    have hx : 2 * hopB g < -(E + gammaG g * v) := by nlinarith
    have hsq : Real.sqrt ((-(E + gammaG g * v)) ^ 2 - 4 * hopB g ^ 2) = v⁻¹ := by
      rw [neg_sq, hT]; exact Real.sqrt_sq (by positivity)
    have h := bandEdge_le_bandH hg hx
    unfold bandH at h
    rw [hsq, div_inv_eq_mul] at h
    have := neg_le_abs E
    linarith
  · rw [hw0] at hTpos; nlinarith
  · have hvneg : v < 0 := by
      by_contra hn
      have hvp : 0 < v := lt_of_le_of_ne (not_lt.mp hn) (Ne.symm hv0)
      have : -v⁻¹ < 0 := neg_neg_of_pos (inv_pos.mpr hvp)
      have := mul_neg_of_neg_of_pos this hw0
      linarith
    have hx : 2 * hopB g < E + gammaG g * v := by nlinarith
    have hsq : Real.sqrt ((E + gammaG g * v) ^ 2 - 4 * hopB g ^ 2) = -v⁻¹ := by
      rw [hT, ← neg_sq]; exact Real.sqrt_sq (neg_nonneg.mpr (inv_nonpos.mpr hvneg.le))
    have h := bandEdge_le_bandH hg hx
    unfold bandH at h
    rw [hsq, div_neg, div_inv_eq_mul] at h
    have := le_abs_self E
    linarith

/-- Single band: `Im m_g(E + i0) > 0` exactly on `(-e_g, e_g)`. -/
theorem mDysonBdry_im_pos_iff (g : ℝ) (hg : 0 ≤ g) (E : ℝ) :
    0 < (mDysonBdry g E).im ↔ |E| < bandEdge g := by
  constructor
  · intro h
    by_contra hE
    exact bandQ_no_upper hg (not_lt.mp hE) h (band_bdry_root hg E)
  · intro hE
    by_contra h
    have h0 : (mDysonBdry g E).im = 0 := le_antisymm (not_lt.mp h) (mDysonBdry_norm_le g hg E).2
    have hv : mDysonBdry g E = ((mDysonBdry g E).re : ℂ) :=
      Complex.ext (by simp) (by simp [h0])
    have hq := mDysonBdry_quartic g hg E
    have hs := band_bdry_sign hg E
    rw [hv] at hq hs
    set v := (mDysonBdry g E).re
    have hq' : v ^ 2 * ((E + gammaG g * v) ^ 2 - 4 * hopB g ^ 2) = 1 := by exact_mod_cast hq
    rw [← Complex.ofReal_inv, ← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_add,
      Complex.ofReal_re, Complex.ofReal_re] at hs
    exact absurd (band_edge_le_of_real hg hq' hs) (not_le.mpr hE)

/-- Inside the band the boundary value solves (1.9) [eq:dyson] at `z = E`. -/
theorem mDysonBdry_spec (g : ℝ) (hg : 0 ≤ g) (E : ℝ) (hE : |E| < bandEdge g) :
    0 < (mDysonBdry g E).im ∧ mDysonBdry g E = dysonRHS g E (mDysonBdry g E) := by
  have h0 := (mDysonBdry_im_pos_iff g hg E).2 hE
  exact ⟨h0, (dyson_iff_quartic' g hg E (by simp) _ h0).2 (mDysonBdry_quartic g hg E)⟩

end LSBA
