import LSBA.Sampling.Reach
import LSBA.Transfer.Coarse

/-!
# Crude moments at large coupling

The first bound of (5.33) [fo:eq:coarse-time-input] at every admissible point reached from a
large-coupling base family: `E‖G_ab‖^p ≤ C_p W^{3p}`, from Lemma 5.5 [fo:lem:resolvent-moments].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- For `ρ → ∞` and `a`, eventually `a ≤ ρ(W)`, `1 ≤ log W` and `1 ≤ W`. -/
private lemma crudeLarge_threshold (ρ : ℕ → ℝ) (hρ : Tendsto ρ atTop atTop) (a : ℝ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → a ≤ ρ W ∧ 1 ≤ Real.log W ∧ 1 ≤ W := by
  have h1 : ∀ᶠ W : ℕ in atTop, a ≤ ρ W := hρ.eventually_ge_atTop a
  have h2 : ∀ᶠ W : ℕ in atTop, 1 ≤ Real.log W :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have h3 : ∀ᶠ W : ℕ in atTop, 1 ≤ W := eventually_ge_atTop 1
  exact Filter.eventually_atTop.mp ((h1.and h2).and h3) |>.imp fun W₀ h W hW =>
    ⟨(h W hW).1.1, (h W hW).1.2, (h W hW).2⟩

/-- `W^{-3} ≤ 1 - u` as `(W³)⁻¹ ≤ 1 - u`. -/
private lemma crudeLarge_inv_cube {W : ℕ} (hW : 1 ≤ W) {u : ℝ}
    (h : (W : ℝ) ^ (-3 : ℝ) ≤ 1 - u) : ((W : ℝ) ^ 3)⁻¹ ≤ 1 - u := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  rwa [Real.rpow_neg hW0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h

/-- The crude moments (first bound of (5.33) [fo:eq:coarse-time-input]) at large coupling, for
every base family inside the large-coupling range, from Lemma 5.5 [fo:lem:resolvent-moments]. -/
theorem crudeInput_of_large (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) (J : ℕ) :
    ∃ Cκ₀ : ℝ, 1 ≤ Cκ₀ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      ∀ base : ℕ → Set FlowPt,
        (∀ W p, p ∈ base W → Cκ ≤ p.g ∧ |p.E| ≤ 2 - 3 * κ / 4 ∧
          ρ W * p.g ^ 2 * Real.log W ≤ p.L ∧ (p.L : ℝ) ≤ CV * p.g ^ 2 * (W : ℝ) ^ 2 ∧
          1 / 2 ≤ p.u ∧ (W : ℝ) ^ (-3 : ℝ) ≤ 1 - p.u) →
        CrudeInput base J := by
  obtain ⟨CκR, C'', hCκR, hC'', HR⟩ := cmpReach_large κ CV hκ hκ2 hCV J
  obtain ⟨CκS, CA, hCκS, hCA, HS⟩ := segAdm_large κ CV hκ hκ2 hCV J
  obtain ⟨Cκc, Cch, hCκc, hCch, HC⟩ := char_large (κ / 2) C'' (by linarith) (by linarith) hC''
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  set T : ℝ := 2 / Real.sqrt (κ / 4) with hT
  refine ⟨max (max CκR CκS) (max (Real.sqrt 2 * Cκc) (Real.sqrt 2 * T)),
    hCκR.trans ((le_max_left _ _).trans (le_max_left _ _)), fun Cκ hCκ ρ hρ base hbase => ?_⟩
  have hCκR' : CκR ≤ Cκ := ((le_max_left _ _).trans (le_max_left _ _)).trans hCκ
  have hCκS' : CκS ≤ Cκ := ((le_max_right _ _).trans (le_max_left _ _)).trans hCκ
  have hCκc' : Real.sqrt 2 * Cκc ≤ Cκ := ((le_max_left _ _).trans (le_max_right _ _)).trans hCκ
  have hCκT' : Real.sqrt 2 * T ≤ Cκ := ((le_max_right _ _).trans (le_max_right _ _)).trans hCκ
  obtain ⟨W₁, hW₁⟩ := HR Cκ hCκR' ρ hρ
  obtain ⟨W₂, hW₂⟩ := HS Cκ hCκS' ρ hρ
  obtain ⟨W₃, hW₃⟩ := crudeLarge_threshold ρ hρ 4
  refine ⟨3, fun p hp => ?_⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  obtain ⟨C, hC0, hC⟩ := resolvent_moments (κ / 4) p CA (by linarith) hp0 (by linarith)
  refine ⟨C * Cch ^ p, max (max W₁ W₂) (max W₃ (4 * p)), fun W hW x hx => ?_⟩
  have hW1 : W₁ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hW2 : W₂ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hW3 : W₃ ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
  have hW4 : 4 * p ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans hW)
  obtain ⟨hρ4, hlog1, hWpos⟩ := hW₃ W hW3
  obtain ⟨d, hd, hreach, hseg⟩ := hx
  obtain ⟨hCκp, hE', hroot, hIm, hm, hvol, -, hu12, hut⟩ :=
    hW₁ base hbase W hW1 d x.1 hd hreach
  obtain ⟨hηy, hyC⟩ := hW₂ base hbase W hW2 x ⟨d, hd, hreach, hseg⟩
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hWpos
  have hu1 : x.1.u < 1 := by
    have := Real.rpow_pos_of_pos hW0 (-3 : ℝ)
    linarith
  have hu0 : 0 ≤ x.1.u := by linarith
  -- the coupling clears the thresholds of `char_large` and `resolvent_moments`
  have hgc : Cκc ≤ x.1.g := by
    refine le_trans ?_ hCκp
    rw [le_div_iff₀ hs2]; linarith
  have hgT : T ≤ x.1.g := by
    refine le_trans ?_ hCκp
    rw [le_div_iff₀ hs2]; linarith
  obtain ⟨hzre, -, hη0, -, hηlow⟩ := HC x.1.g hgc x.1.E (mRoot x.1.g x.1.L x.1.E) hE' hm hIm
    x.1.u hu0 hu1
  have hg1 : 1 ≤ x.1.g := hCκc.trans hgc
  have hg2 : (0 : ℝ) < x.1.g ^ 2 := by positivity
  have hy0 : 0 < x.2 := lt_of_lt_of_le hη0 hηy
  -- `g² y ≥ W^{-3}/C_ch`
  have hCch0 : 0 < Cch := by linarith
  have hgy : ((W : ℝ) ^ 3)⁻¹ / Cch ≤ x.1.g ^ 2 * x.2 := by
    calc ((W : ℝ) ^ 3)⁻¹ / Cch ≤ (1 - x.1.u) / Cch :=
          div_le_div_of_nonneg_right (crudeLarge_inv_cube hWpos hut) hCch0.le
      _ ≤ x.1.g ^ 2 * etaChar x.1.g (mRoot x.1.g x.1.L x.1.E) x.1.u := hηlow
      _ ≤ x.1.g ^ 2 * x.2 := mul_le_mul_of_nonneg_left hηy hg2.le
  have hgy0 : 0 < x.1.g ^ 2 * x.2 := mul_pos hg2 hy0
  -- `4 g² ≤ L`
  have h4 : 4 * x.1.g ^ 2 ≤ x.1.L := by
    have h1 : 4 ≤ ρ W * Real.log W := by nlinarith
    calc 4 * x.1.g ^ 2 ≤ (ρ W * Real.log W) * x.1.g ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = ρ W * x.1.g ^ 2 * Real.log W := by ring
      _ ≤ x.1.L := hvol
  have hgT' : 2 / Real.sqrt (κ / 4) ≤ x.1.g := hgT
  have hE'' : |(zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re| ≤ 2 - κ / 4 := by
    linarith
  have hyC' : x.2 ≤ CA / x.1.g ^ 2 := hyC
  intro a b
  have key := hC W (by exact_mod_cast hW4) x.1.L x.1.g hgT' h4 _ x.2 x.1.u hE'' hy0 hyC' hu0
    hu1.le a b
  simp only [Real.rpow_natCast] at key
  refine ⟨key.1, key.2.trans ?_⟩
  -- `(g² y)^{-p} ≤ (C_ch W³)^p = C_ch^p W^{3p}`
  have hinv : (x.1.g ^ 2 * x.2)⁻¹ ≤ Cch * (W : ℝ) ^ 3 := by
    rw [inv_le_comm₀ hgy0 (by positivity)]
    calc (Cch * (W : ℝ) ^ 3)⁻¹ = ((W : ℝ) ^ 3)⁻¹ / Cch := by
          rw [mul_inv, mul_comm, div_eq_mul_inv]
      _ ≤ _ := hgy
  have hneg : (x.1.g ^ 2 * x.2) ^ (-(p : ℝ)) ≤ Cch ^ p * (W : ℝ) ^ (3 * (p : ℝ)) := by
    rw [Real.rpow_neg hgy0.le, Real.rpow_natCast, ← inv_pow,
      show (3 * (p : ℝ)) = ((3 * p : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, pow_mul,
      ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hinv p
  calc C * (x.1.g ^ 2 * x.2) ^ (-(p : ℝ)) ≤ C * (Cch ^ p * (W : ℝ) ^ (3 * (p : ℝ))) :=
        mul_le_mul_of_nonneg_left hneg hC0.le
    _ = C * Cch ^ p * (W : ℝ) ^ (3 * (p : ℝ)) := by ring

end LSBA
