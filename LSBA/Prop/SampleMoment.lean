import LSBA.Prop.StepDefs
import LSBA.Prop.Inputs
import LSBA.Prop.Domination
import LSBA.Flow.Comparison

/-!
# From moments at every word to the maximum over all words

Markov at the sampled words of the sampling input of Lemma 5.8 [uvc:thm:ordinary-sampling] and a
union over the samples and the signs.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- Markov for a complex random variable: `P(‖X‖ > a) ≤ E‖X‖^r / a^r`. -/
private lemma sampleMoment_markov {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsProbabilityMeasure P] (X : α → ℂ) (r : ℕ) (a : ℝ) (ha : 0 < a)
    (hint : Integrable (fun ω => ‖X ω‖ ^ r) P) :
    P {ω | a < ‖X ω‖} ≤ ENNReal.ofReal ((∫ ω, ‖X ω‖ ^ r ∂P) / a ^ r) := by
  have hsub : {ω | a < ‖X ω‖} ⊆ {ω | a ^ r ≤ ‖X ω‖ ^ r} := fun ω hω =>
    pow_le_pow_left₀ ha.le (le_of_lt hω) r
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := fun ω => ‖X ω‖ ^ r)
    (Filter.Eventually.of_forall fun ω => pow_nonneg (norm_nonneg _) r) hint (a ^ r)
  have hρ : P.real {ω | a < ‖X ω‖} ≤ P.real {ω | a ^ r ≤ ‖X ω‖ ^ r} := measureReal_mono hsub
  have h1 : a ^ r * P.real {ω | a < ‖X ω‖} ≤ ∫ ω, ‖X ω‖ ^ r ∂P :=
    (mul_le_mul_of_nonneg_left hρ (pow_nonneg ha.le r)).trans hmark
  have h2 : P.real {ω | a < ‖X ω‖} ≤ (∫ ω, ‖X ω‖ ^ r ∂P) / a ^ r := by
    rw [le_div_iff₀ (pow_pos ha r)]; linarith
  rw [← ofReal_measureReal (measure_ne_top P _)]
  exact ENNReal.ofReal_le_ofReal h2

/-- A union bound over the sample set and the signs: if the sampling event fails with
probability at most `η` for each sign, and each sampled word exceeds `mY` with probability at most
`ρ`, then some word exceeds `T ≥ max(C_s, 0) mY + δ` with probability at most
`#signs · η + #S · #signs · ρ`. -/
private lemma sampleMoment_union {α : Type*} [MeasurableSpace α] (P : Measure α) {A Sg : Type*}
    [Fintype Sg] (X : A → Sg → α → ℂ) (S : Finset A) (Cs δ m Y T η ρ : ℝ) (hY : 0 ≤ Y)
    (hm : 0 ≤ m) (hT : max Cs 0 * (m * Y) + δ ≤ T)
    (hE : ∀ σ, P {ω | ∃ a, Cs * (⨆ s : S, ‖X s σ ω‖ / 1) + δ < ‖X a σ ω‖ / 1} ≤
      ENNReal.ofReal η)
    (hM : ∀ s ∈ S, ∀ σ, P {ω | m * Y < ‖X s σ ω‖} ≤ ENNReal.ofReal ρ) :
    P {ω | ∃ a σ, T < ‖X a σ ω‖} ≤ (Fintype.card Sg : ℝ≥0∞) * ENNReal.ofReal η +
      ((S.card * Fintype.card Sg : ℕ) : ℝ≥0∞) * ENNReal.ofReal ρ := by
  set E : Sg → Set α := fun σ =>
    {ω | ∃ a, Cs * (⨆ s : S, ‖X s σ ω‖ / 1) + δ < ‖X a σ ω‖ / 1} with hEdef
  set M : A → Sg → Set α := fun s σ => {ω | m * Y < ‖X s σ ω‖} with hMdef
  have hsub : {ω | ∃ a σ, T < ‖X a σ ω‖} ⊆ (⋃ σ, E σ) ∪ ⋃ s ∈ S, ⋃ σ, M s σ := by
    rintro ω ⟨a, σ, h⟩
    by_contra hB
    have h1 : ω ∉ E σ := fun hex => hB (Or.inl (Set.mem_iUnion.2 ⟨σ, hex⟩))
    have h2 : ∀ s ∈ S, ‖X s σ ω‖ ≤ m * Y := fun s hs => not_lt.1 fun hlt =>
      hB (Or.inr (Set.mem_iUnion₂.2 ⟨s, hs, Set.mem_iUnion.2 ⟨σ, hlt⟩⟩))
    have h3 : ‖X a σ ω‖ / 1 ≤ Cs * (⨆ s : S, ‖X s σ ω‖ / 1) + δ := by
      by_contra h4
      exact h1 ⟨a, not_le.1 h4⟩
    have hsup : (⨆ s : S, ‖X s σ ω‖ / 1) ≤ m * Y :=
      Real.iSup_le (fun s => by simpa using h2 s s.2) (mul_nonneg hm hY)
    have hsup0 : 0 ≤ ⨆ s : S, ‖X s σ ω‖ / 1 := Real.iSup_nonneg fun s => by positivity
    have h5 : Cs * (⨆ s : S, ‖X s σ ω‖ / 1) ≤ max Cs 0 * (m * Y) :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hsup0).trans
        (mul_le_mul_of_nonneg_left hsup (le_max_right _ _))
    rw [div_one] at h3
    linarith
  have hE' : ∑ σ, P (E σ) ≤ ∑ _σ : Sg, ENNReal.ofReal η := Finset.sum_le_sum fun σ _ => hE σ
  have hM' : ∑ s ∈ S, ∑ σ, P (M s σ) ≤ ∑ _s ∈ S, ∑ _σ : Sg, ENNReal.ofReal ρ :=
    Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun σ _ => hM s hs σ
  calc P {ω | ∃ a σ, T < ‖X a σ ω‖} ≤ P ((⋃ σ, E σ) ∪ ⋃ s ∈ S, ⋃ σ, M s σ) := measure_mono hsub
    _ ≤ P (⋃ σ, E σ) + P (⋃ s ∈ S, ⋃ σ, M s σ) := measure_union_le _ _
    _ ≤ ∑ σ, P (E σ) + ∑ s ∈ S, P (⋃ σ, M s σ) :=
        add_le_add (measure_iUnion_fintype_le _ _) (measure_biUnion_finset_le _ _)
    _ ≤ ∑ σ, P (E σ) + ∑ s ∈ S, ∑ σ, P (M s σ) :=
        add_le_add le_rfl (Finset.sum_le_sum fun s _ => measure_iUnion_fintype_le _ _)
    _ ≤ ∑ _σ : Sg, ENNReal.ofReal η + ∑ _s ∈ S, ∑ _σ : Sg, ENNReal.ofReal ρ := add_le_add hE' hM'
    _ = (Fintype.card Sg : ℝ≥0∞) * ENNReal.ofReal η +
        ((S.card * Fintype.card Sg : ℕ) : ℝ≥0∞) * ENNReal.ofReal ρ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        push_cast
        ring

/-- From moments at every word to the maximum over all words: Markov at the sampled words of
Lemma 5.10(b) [fo:lem:sampling-continuity] and the sampling inequality (5.34)
[fo:eq:weighted-sampling-input] at the time `u`, with a union over the signs. Moments
`E|D_n(u; w)|^r ≤ C_r (W^δ Y)^r` for every order `r`, every `δ > 0` and every word, with
`Y ≥ W^{-C₁}`, give `max_w |D_n(u; w)| ≺ Y` on the family. -/
theorem precMax_of_sampleMoment (R : PropRegime) (I : PropInputs R.base R.J) (c N : ℝ)
    (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q}) (n : ℕ) (hn : 1 ≤ n)
    (Y : ℕ → StepPt → ℝ) (C₁ : ℝ) (hY : ∀ W, ∀ q ∈ S W, (W : ℝ) ^ (-C₁) ≤ Y W q)
    (hmom : ∀ r : ℕ, 1 ≤ r → ∀ δ : ℝ, 0 < δ → ∃ Cr : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ q ∈ S W, ∀ w : Word n q.L,
        Integrable (fun ω => ‖flowErr W (q.at q.u) w.1 w.2 ω‖ ^ r) (μ W q.L) ∧
        ∫ ω, ‖flowErr W (q.at q.u) w.1 w.2 ω‖ ^ r ∂(μ W q.L) ≤ Cr * ((W : ℝ) ^ δ * Y W q) ^ r) :
    PrecMax StepPt.L S (Λ := fun _ q => Word n q.L)
      (fun W q w ω => flowErr W (q.at q.u) w.1 w.2 ω) (fun W q _ => Y W q) := by
  intro ε D hε hD
  set Ds : ℝ := max D C₁ with hDs
  have hDs0 : 0 < Ds := lt_max_of_lt_left hD
  obtain ⟨CS, Cs, W₁, hsamp⟩ := I.sampling.1 n hn 1 (1 / 2) 1 one_pos (by norm_num) le_rfl
    one_pos Ds (D + 1) hDs0 (by linarith)
  set r : ℕ := ⌈4 * (CS + D + 1) / ε⌉₊ + 1 with hr
  have hr1 : 1 ≤ r := Nat.le_add_left 1 _
  have hrε : CS + D + 1 ≤ ε / 4 * (r : ℝ) := by
    have h1 : 4 * (CS + D + 1) / ε ≤ (⌈4 * (CS + D + 1) / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (r : ℝ) = (⌈4 * (CS + D + 1) / ε⌉₊ : ℝ) + 1 := by simp [hr]
    have h3 : 4 * (CS + D + 1) ≤ (⌈4 * (CS + D + 1) / ε⌉₊ : ℝ) * ε := (div_le_iff₀ hε).mp h1
    nlinarith
  obtain ⟨Cr, W₂, hW₂⟩ := hmom r hr1 (ε / 4) (by positivity)
  obtain ⟨N1, hN1⟩ := exists_nat_ge (2 ^ n * (1 + max Cr 0))
  obtain ⟨N2, hN2⟩ := exists_nat_ge ((max Cs 0 + 1) ^ (2 / ε))
  refine ⟨max (max (max W₁ W₂) 2) (max N1 N2), fun W hW q hq => ?_⟩
  have hW1 : W₁ ≤ W :=
    (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hW))
  have hW2 : W₂ ≤ W :=
    (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hW))
  have hW3 : 2 ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hW4 : N1 ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
  have hW5 : N2 ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans hW)
  have hWr : (2 : ℝ) ≤ W := by exact_mod_cast hW3
  have hWpos : (0 : ℝ) < W := by linarith
  have hWge : (1 : ℝ) ≤ W := by linarith
  obtain ⟨⟨d, hdJ, hreach⟩, hs1, hsu, hut, -, -, -⟩ := hS W hq
  have h0 : ∃ Sq : Finset (Fin n → Fin q.L), (Sq.card : ℝ) ≤ (W : ℝ) ^ CS ∧
      ∀ (σ : Fin n → Bool) (u : ℝ), 0 ≤ u → u ≤ q.t →
        SampleBound (μ W q.L) (fun (a : Fin n → Fin q.L) ω => flowErr W (q.at u) a σ ω)
          (fun _ => 1) Sq Cs ((W : ℝ) ^ (-Ds)) ((W : ℝ) ^ (-(D + 1))) := by
    obtain ⟨Sq, hcard, hsb⟩ := hsamp W hW1 d (q.at q.t) hdJ.le hreach
    exact ⟨Sq, hcard, fun σ u h1 h2 => (hsb σ u h1 h2).2.1⟩
  obtain ⟨Sq, hcard, hsb⟩ := h0
  have hu0 : 0 ≤ q.u := by linarith
  have hYpos : 0 < Y W q := lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) (hY W q hq)
  -- the scale `t = W^{ε/4}` and the amplitude `W^{ε/2} = t²`
  set t : ℝ := (W : ℝ) ^ (ε / 4) with ht
  have htpos : 0 < t := Real.rpow_pos_of_pos hWpos _
  have ht2 : t ^ 2 = (W : ℝ) ^ (ε / 2) := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hWpos.le]; congr 1; push_cast; ring
  have htε : (W : ℝ) ^ ε = t ^ 2 * t ^ 2 := by
    rw [ht2, ← Real.rpow_add hWpos]; congr 1; ring
  have htr : (W : ℝ) ^ (CS + D + 1) ≤ t ^ r := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hWpos.le]
    exact Real.rpow_le_rpow_of_exponent_le hWge hrε
  have hCs : max Cs 0 + 1 ≤ t ^ 2 := by
    rw [ht2]
    have h1 : (max Cs 0 + 1) ^ (2 / ε) ≤ (W : ℝ) := hN2.trans (by exact_mod_cast hW5)
    have h2 := Real.rpow_le_rpow (by positivity) h1 (by positivity : 0 ≤ ε / 2)
    rw [← Real.rpow_mul (by positivity)] at h2
    have h3 : 2 / ε * (ε / 2) = 1 := by field_simp
    rwa [h3, Real.rpow_one] at h2
  have hCs0 : 0 ≤ max Cs 0 := le_max_right _ _
  have hδY : (W : ℝ) ^ (-Ds) ≤ Y W q :=
    (Real.rpow_le_rpow_of_exponent_le hWge (by linarith [le_max_right D C₁])).trans (hY W q hq)
  -- the amplitude
  have hT : max Cs 0 * (t ^ 2 * Y W q) + (W : ℝ) ^ (-Ds) ≤ (W : ℝ) ^ ε * Y W q := by
    rw [htε]
    have h1 : max Cs 0 * t ^ 2 + 1 ≤ t ^ 2 * t ^ 2 := by nlinarith
    nlinarith
  -- the Markov bound at a sampled word
  have hM : ∀ s ∈ Sq, ∀ σ : Fin n → Bool,
      μ W q.L {ω | t ^ 2 * Y W q < ‖flowErr W (q.at q.u) s σ ω‖} ≤
        ENNReal.ofReal (max Cr 0 / t ^ r) := by
    intro s _ σ
    obtain ⟨hint, hmo⟩ := hW₂ W hW2 q hq (s, σ)
    refine (sampleMoment_markov (μ W q.L) (fun ω => flowErr W (q.at q.u) s σ ω) r
      (t ^ 2 * Y W q) (by positivity) hint).trans (ENNReal.ofReal_le_ofReal ?_)
    have htr0 : 0 < t ^ r := pow_pos htpos r
    have hmo' : (∫ ω, ‖flowErr W (q.at q.u) s σ ω‖ ^ r ∂(μ W q.L)) ≤
        max Cr 0 * (t * Y W q) ^ r :=
      hmo.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    rw [div_le_div_iff₀ (by positivity) htr0]
    calc (∫ ω, ‖flowErr W (q.at q.u) s σ ω‖ ^ r ∂(μ W q.L)) * t ^ r
        ≤ max Cr 0 * (t * Y W q) ^ r * t ^ r :=
          mul_le_mul_of_nonneg_right hmo' htr0.le
      _ = max Cr 0 * (t ^ 2 * Y W q) ^ r := by rw [mul_assoc, ← mul_pow]; congr 2; ring
  have hE : ∀ σ : Fin n → Bool, μ W q.L {ω | ∃ a : Fin n → Fin q.L,
      Cs * (⨆ s : Sq, ‖flowErr W (q.at q.u) s.1 σ ω‖ / 1) + (W : ℝ) ^ (-Ds) <
        ‖flowErr W (q.at q.u) a σ ω‖ / 1} ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) :=
    fun σ => by
      have h := hsb σ q.u hu0 hut
      unfold SampleBound at h
      exact h
  have key := sampleMoment_union (μ W q.L)
    (fun (a : Fin n → Fin q.L) (σ : Fin n → Bool) ω => flowErr W (q.at q.u) a σ ω) Sq Cs
    ((W : ℝ) ^ (-Ds)) (t ^ 2) (Y W q) ((W : ℝ) ^ ε * Y W q) ((W : ℝ) ^ (-(D + 1)))
    (max Cr 0 / t ^ r) hYpos.le (by positivity) hT hE hM
  -- the arithmetic
  have hcard2 : Fintype.card (Fin n → Bool) = 2 ^ n := by simp
  have hη : 0 ≤ (W : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg hWpos.le _
  have hρ : 0 ≤ max Cr 0 / t ^ r := by positivity
  have hWD1 : (W : ℝ) ^ (-D) = (W : ℝ) ^ (-(D + 1)) * W := by
    rw [show -(D + 1) = -D + (-1) by ring, Real.rpow_add hWpos, Real.rpow_neg_one,
      mul_assoc, inv_mul_cancel₀ hWpos.ne', mul_one]
  have hWCS : (W : ℝ) ^ (CS + D + 1) = (W : ℝ) ^ CS * (W : ℝ) ^ (D + 1) := by
    rw [show CS + D + 1 = CS + (D + 1) by ring, Real.rpow_add hWpos]
  have hWinv : (W : ℝ) ^ (-(D + 1)) = ((W : ℝ) ^ (D + 1))⁻¹ := Real.rpow_neg hWpos.le _
  have hWD1pos : 0 < (W : ℝ) ^ (D + 1) := Real.rpow_pos_of_pos hWpos _
  have hWCSpos : 0 < (W : ℝ) ^ CS := Real.rpow_pos_of_pos hWpos _
  -- `W^{C_S} ρ ≤ max(C_r,0) W^{-(D+1)}`
  have hρW : (W : ℝ) ^ CS * (max Cr 0 / t ^ r) ≤ max Cr 0 * (W : ℝ) ^ (-(D + 1)) := by
    have h1 : (W : ℝ) ^ CS / t ^ r ≤ (W : ℝ) ^ (-(D + 1)) := by
      rw [div_le_iff₀ (pow_pos htpos r), hWinv]
      calc (W : ℝ) ^ CS = ((W : ℝ) ^ (D + 1))⁻¹ * ((W : ℝ) ^ CS * (W : ℝ) ^ (D + 1)) := by
            field_simp
        _ ≤ ((W : ℝ) ^ (D + 1))⁻¹ * t ^ r :=
            mul_le_mul_of_nonneg_left (hWCS ▸ htr) (inv_nonneg.2 hWD1pos.le)
    calc (W : ℝ) ^ CS * (max Cr 0 / t ^ r) = max Cr 0 * ((W : ℝ) ^ CS / t ^ r) := by ring
      _ ≤ max Cr 0 * (W : ℝ) ^ (-(D + 1)) :=
          mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
  set κ : ℕ := Fintype.card (Fin n → Bool) with hκdef
  have hκ : (κ : ℝ) = 2 ^ n := by simp [hκdef]
  have hreal : (κ : ℝ) * (W : ℝ) ^ (-(D + 1)) + ((Sq.card * κ : ℕ) : ℝ) * (max Cr 0 / t ^ r) ≤
      (W : ℝ) ^ (-D) := by
    have hκ0 : (0 : ℝ) ≤ κ := Nat.cast_nonneg _
    have e1 : ((Sq.card * κ : ℕ) : ℝ) * (max Cr 0 / t ^ r) ≤
        κ * (max Cr 0 * (W : ℝ) ^ (-(D + 1))) := by
      push_cast
      calc (Sq.card : ℝ) * κ * (max Cr 0 / t ^ r) = κ * ((Sq.card : ℝ) * (max Cr 0 / t ^ r)) := by
            ring
        _ ≤ κ * ((W : ℝ) ^ CS * (max Cr 0 / t ^ r)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hρ) hκ0
        _ ≤ κ * (max Cr 0 * (W : ℝ) ^ (-(D + 1))) := mul_le_mul_of_nonneg_left hρW hκ0
    have e2 : (κ : ℝ) * (1 + max Cr 0) ≤ W := by
      rw [hκ]; exact hN1.trans (by exact_mod_cast hW4)
    calc (κ : ℝ) * (W : ℝ) ^ (-(D + 1)) + ((Sq.card * κ : ℕ) : ℝ) * (max Cr 0 / t ^ r)
        ≤ (κ : ℝ) * (W : ℝ) ^ (-(D + 1)) + κ * (max Cr 0 * (W : ℝ) ^ (-(D + 1))) :=
          add_le_add le_rfl e1
      _ = (κ * (1 + max Cr 0)) * (W : ℝ) ^ (-(D + 1)) := by ring
      _ ≤ (W : ℝ) * (W : ℝ) ^ (-(D + 1)) := mul_le_mul_of_nonneg_right e2 hη
      _ = (W : ℝ) ^ (-D) := by rw [hWD1, mul_comm]
  refine (measure_mono ?_).trans (key.trans ?_)
  · rintro ω ⟨l, hl⟩
    exact ⟨l.1, l.2, hl⟩
  · rw [← ENNReal.ofReal_natCast κ, ← ENNReal.ofReal_natCast (Sq.card * κ), ← ENNReal.ofReal_mul
      (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _) hη)
        (mul_nonneg (Nat.cast_nonneg _) hρ)]
    exact ENNReal.ofReal_le_ofReal hreal

end LSBA
