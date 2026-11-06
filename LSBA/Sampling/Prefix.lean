import LSBA.Sampling.Transfer

/-!
# Prefix moments and close cells

Lemma 7.7 [uvc:lem:cells] at a fixed time: the moments (7.14) [uvc:eq:prefix-moments] of the
prefixes of an in-cell transfer product with Gaussian blocks of variance `s`, at complex `z` near
the real energy, and the bound on the probability that some cell product is not close to the
free one, uniformly in `g`, `L`, `E` and `s` with `s g² ≤ 1`.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA


/-- The even and odd parts of `(A ± B)^p` when `B² ≤ 4RA`. -/
private theorem prefix_sym (A B R c : ℝ) (hA : 0 ≤ A) (hR : 0 ≤ R) (hB : B ^ 2 ≤ 4 * R * A) :
    ∀ p : ℕ, 4 * (p : ℝ) ≤ c →
      ((A + B) ^ p + (A - B) ^ p) / 2 ≤ (A + c * R) ^ p ∧
      |((A + B) ^ p - (A - B) ^ p) / 2| ≤ p * |B| * (A + c * R) ^ (p - 1) ∧
      0 ≤ ((A + B) ^ p + (A - B) ^ p) / 2 ∧ 0 ≤ B * (((A + B) ^ p - (A - B) ^ p) / 2) := by
  intro p
  induction p with
  | zero => intro _; simp
  | succ p ih =>
    intro hc
    have hc' : 4 * (p : ℝ) ≤ c := by push_cast at hc; linarith
    obtain ⟨h1, h2, h3, h4⟩ := ih hc'
    have hc0 : 0 ≤ c := le_trans (by positivity) hc'
    set S := ((A + B) ^ p + (A - B) ^ p) / 2 with hS
    set D := ((A + B) ^ p - (A - B) ^ p) / 2 with hD
    set P := A + c * R with hPdef
    have hcR : 0 ≤ c * R := mul_nonneg hc0 hR
    have hAP : A ≤ P := by linarith
    have hP0 : 0 ≤ P := by linarith
    have eS : ((A + B) ^ (p + 1) + (A - B) ^ (p + 1)) / 2 = A * S + B * D := by
      simp only [hS, hD]; ring
    have eD : ((A + B) ^ (p + 1) - (A - B) ^ (p + 1)) / 2 = A * D + B * S := by
      simp only [hS, hD]; ring
    rw [eS, eD]
    have hBD : |B| * |D| ≤ p * B ^ 2 * P ^ (p - 1) := by
      calc |B| * |D| ≤ |B| * (p * |B| * P ^ (p - 1)) := by gcongr
        _ = p * |B| ^ 2 * P ^ (p - 1) := by ring
        _ = p * B ^ 2 * P ^ (p - 1) := by rw [sq_abs]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos p with hp | hp
      · subst hp
        simp [hS, hD]
        linarith
      · have hpow : P ^ p = P ^ (p - 1) * P := by
          rw [← pow_succ]; congr 1; omega
        have hpow2 : P ^ (p + 1) = P ^ (p - 1) * P ^ 2 := by
          rw [← pow_add]; congr 1; omega
        have hq0 : 0 ≤ P ^ (p - 1) := pow_nonneg hP0 _
        have hkey : A * P + p * (4 * R * A) ≤ P ^ 2 := by
          have e : P ^ 2 = A * P + c * R * P := by rw [hPdef]; ring
          rw [e]
          have h5 : (p : ℝ) * (4 * R * A) ≤ c * R * A := by
            have := mul_le_mul_of_nonneg_right hc' (mul_nonneg hR hA)
            nlinarith
          have h6 : c * R * A ≤ c * R * P := mul_le_mul_of_nonneg_left hAP hcR
          linarith
        calc A * S + B * D ≤ A * P ^ p + |B| * |D| := by
              have := mul_le_mul_of_nonneg_left h1 hA
              have h5 : B * D ≤ |B| * |D| := by rw [← abs_mul]; exact le_abs_self _
              linarith
          _ ≤ A * P ^ p + p * (4 * R * A) * P ^ (p - 1) := by
              have : (p : ℝ) * B ^ 2 * P ^ (p - 1) ≤ p * (4 * R * A) * P ^ (p - 1) := by
                gcongr
              linarith
          _ = P ^ (p - 1) * (A * P + p * (4 * R * A)) := by rw [hpow]; ring
          _ ≤ P ^ (p - 1) * P ^ 2 := mul_le_mul_of_nonneg_left hkey hq0
          _ = P ^ (p + 1) := hpow2.symm
    · have hpow : P ^ (p + 1 - 1) = P ^ p := by congr 1
      rw [hpow]
      calc |A * D + B * S| ≤ A * |D| + |B| * S := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_of_nonneg hA, abs_of_nonneg h3]
        _ ≤ A * (p * |B| * P ^ (p - 1)) + |B| * P ^ p := by gcongr
        _ ≤ P * (p * |B| * P ^ (p - 1)) + |B| * P ^ p := by gcongr
        _ = ((p : ℝ) + 1) * |B| * P ^ p := by
            rcases Nat.eq_zero_or_pos p with hp | hp
            · subst hp; simp
            · have hpow' : P * P ^ (p - 1) = P ^ p := by
                rw [← pow_succ']; congr 1; omega
              calc P * (p * |B| * P ^ (p - 1)) + |B| * P ^ p
                  = p * |B| * (P * P ^ (p - 1)) + |B| * P ^ p := by ring
                _ = _ := by rw [hpow']; ring
        _ = ((p + 1 : ℕ) : ℝ) * |B| * P ^ p := by push_cast; ring
    · have := mul_nonneg hA h3
      linarith
    · have e : B * (A * D + B * S) = A * (B * D) + B ^ 2 * S := by ring
      rw [e]
      exact add_nonneg (mul_nonneg hA h4) (mul_nonneg (sq_nonneg _) h3)

/-- Polynomial moments of the standard Gaussian on `ℝ` are finite. -/
private theorem prefix_integrable_pow (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) := by
  have hm : MemLp id (k : ℝ≥0∞) (gaussianReal (0 : ℝ) 1) :=
    memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := 1) k (ENNReal.natCast_ne_top k)
  have hm' : MemLp id (k : ℕ) (gaussianReal (0 : ℝ) 1) := by simpa using hm
  have h1 : Integrable (fun x : ℝ => ‖id x‖ ^ k) (gaussianReal 0 1) := hm'.integrable_norm_pow'
  refine h1.mono' (by fun_prop : Continuous fun x : ℝ => x ^ k).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x => by simp [norm_pow]

/-- The even moment `E x^{2l}` of the standard Gaussian. -/
private def prefixMom (l : ℕ) : ℝ := ∫ x, x ^ (2 * l) ∂(gaussianReal 0 1)

private theorem prefix_mom_nonneg (l : ℕ) : 0 ≤ prefixMom l :=
  integral_nonneg fun x => by rw [pow_mul]; positivity

private theorem prefix_mom_zero : prefixMom 0 = 1 := by simp [prefixMom]

/-- The constant of the Gaussian moment bound at order `q`. -/
private def prefixK (q : ℕ) : ℝ :=
  (1 + 4 * q) * (1 + ∑ l ∈ Finset.range (q + 1), prefixMom l)

private theorem prefix_K_nonneg (q : ℕ) : 0 ≤ prefixK q := by
  unfold prefixK
  have := Finset.sum_nonneg fun l (_ : l ∈ Finset.range (q + 1)) => prefix_mom_nonneg l
  positivity

private theorem prefix_K_pow (q l : ℕ) (hl : l ≤ q) :
    (1 + 4 * (q : ℝ)) ^ l * prefixMom l ≤ prefixK q ^ l := by
  have hS := Finset.sum_nonneg fun l (_ : l ∈ Finset.range (q + 1)) => prefix_mom_nonneg l
  set S := ∑ l ∈ Finset.range (q + 1), prefixMom l
  have hm : prefixMom l ≤ (1 + S) ^ l := by
    rcases Nat.eq_zero_or_pos l with h | h
    · subst h; simp [prefix_mom_zero]
    · have h1 : prefixMom l ≤ S :=
        Finset.single_le_sum (fun l _ => prefix_mom_nonneg l)
          (Finset.mem_range.mpr (by omega))
      have h2 : 1 + S ≤ (1 + S) ^ l := le_self_pow₀ (by linarith) (by omega)
      linarith
  rw [prefixK, mul_pow]
  exact mul_le_mul_of_nonneg_left hm (by positivity)

/-- One Gaussian coordinate: `E (‖Y + τ D‖² + λ)^p ≤ (‖Y‖² + λ + K ‖D‖²)^p`, with no first-order
term. -/
private theorem prefix_gauss_one (q p : ℕ) (hp : p ≤ q) {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (Y D : H) (lam : ℝ) (hlam : 0 ≤ lam) :
    ∫⁻ τ, ENNReal.ofReal ((‖Y + τ • D‖ ^ 2 + lam) ^ p) ∂(gaussianReal 0 1) ≤
      ENNReal.ofReal ((‖Y‖ ^ 2 + lam + prefixK q * ‖D‖ ^ 2) ^ p) := by
  set a := ‖Y‖ ^ 2 + lam with ha
  set β := inner ℝ Y D with hβdef
  set σ2 := ‖D‖ ^ 2 with hσ2
  set M : ℝ := 1 + 4 * q with hM
  have hσ0 : 0 ≤ σ2 := sq_nonneg _
  have ha0 : 0 ≤ a := by positivity
  have hYa : ‖Y‖ ^ 2 ≤ a := by rw [ha]; linarith
  have hexp : ∀ τ : ℝ, ‖Y + τ • D‖ ^ 2 + lam = a + 2 * τ * β + τ ^ 2 * σ2 := by
    intro τ
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have hβ : β ^ 2 ≤ ‖Y‖ ^ 2 * σ2 := by
    have h := abs_real_inner_le_norm Y D
    calc β ^ 2 = |β| ^ 2 := (sq_abs _).symm
      _ ≤ (‖Y‖ * ‖D‖) ^ 2 := by gcongr
      _ = _ := by ring
  have hpt : ∀ τ : ℝ, (‖Y + τ • D‖ ^ 2 + lam) ^ p + (‖Y + (-τ) • D‖ ^ 2 + lam) ^ p ≤
      2 * (a + M * τ ^ 2 * σ2) ^ p := by
    intro τ
    rw [hexp, hexp]
    have hA : 0 ≤ a + τ ^ 2 * σ2 := by positivity
    have hR : 0 ≤ τ ^ 2 * σ2 := by positivity
    have hB : (2 * τ * β) ^ 2 ≤ 4 * (τ ^ 2 * σ2) * (a + τ ^ 2 * σ2) := by
      have h1 : τ ^ 2 * β ^ 2 ≤ τ ^ 2 * (‖Y‖ ^ 2 * σ2) :=
        mul_le_mul_of_nonneg_left hβ (sq_nonneg τ)
      have h2 : τ ^ 2 * σ2 * ‖Y‖ ^ 2 ≤ τ ^ 2 * σ2 * (a + τ ^ 2 * σ2) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hR
      nlinarith
    have hc : 4 * (p : ℝ) ≤ 4 * q := by
      have : (p : ℝ) ≤ q := by exact_mod_cast hp
      linarith
    obtain ⟨h1, -⟩ := prefix_sym (a + τ ^ 2 * σ2) (2 * τ * β) (τ ^ 2 * σ2) (4 * q) hA hR hB p hc
    have e1 : a + 2 * τ * β + τ ^ 2 * σ2 = (a + τ ^ 2 * σ2) + 2 * τ * β := by ring
    have e2 : a + 2 * (-τ) * β + (-τ) ^ 2 * σ2 = (a + τ ^ 2 * σ2) - 2 * τ * β := by ring
    have e3 : a + τ ^ 2 * σ2 + 4 * q * (τ ^ 2 * σ2) = a + M * τ ^ 2 * σ2 := by rw [hM]; ring
    rw [e1, e2]
    rw [e3] at h1
    linarith
  have hcont : Continuous fun τ : ℝ => (‖Y + τ • D‖ ^ 2 + lam) ^ p := by fun_prop
  have hmeas : Measurable fun τ : ℝ => ENNReal.ofReal ((‖Y + τ • D‖ ^ 2 + lam) ^ p) :=
    ENNReal.measurable_ofReal.comp hcont.measurable
  set f : ℝ → ℝ≥0∞ := fun τ => ENNReal.ofReal ((‖Y + τ • D‖ ^ 2 + lam) ^ p) with hf
  have hneg : ∫⁻ τ, f (-τ) ∂(gaussianReal 0 1) = ∫⁻ τ, f τ ∂(gaussianReal 0 1) := by
    have hmap : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
      simpa using gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1)
    conv_rhs => rw [← hmap]
    rw [lintegral_map hmeas measurable_neg]
  -- the polynomial bound
  set h : ℝ → ℝ := fun τ => (a + M * τ ^ 2 * σ2) ^ p with hh
  have hexpand : ∀ τ : ℝ, h τ = ∑ l ∈ Finset.range (p + 1),
      ((M * σ2) ^ l * a ^ (p - l) * (p.choose l : ℝ)) * τ ^ (2 * l) := by
    intro τ
    rw [hh]
    simp only
    rw [show a + M * τ ^ 2 * σ2 = M * σ2 * τ ^ 2 + a by ring, add_pow]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_pow, ← pow_mul]
    ring
  have hint : ∀ l, Integrable (fun τ : ℝ => ((M * σ2) ^ l * a ^ (p - l) * (p.choose l : ℝ)) *
      τ ^ (2 * l)) (gaussianReal 0 1) := fun l => (prefix_integrable_pow (2 * l)).const_mul _
  have hhint : Integrable h (gaussianReal 0 1) := by
    have : h = fun τ => ∑ l ∈ Finset.range (p + 1),
        ((M * σ2) ^ l * a ^ (p - l) * (p.choose l : ℝ)) * τ ^ (2 * l) := funext hexpand
    rw [this]
    exact integrable_finsetSum _ fun l _ => hint l
  have hh0 : ∀ τ, 0 ≤ h τ := fun τ => by rw [hh]; positivity
  have hhint_val : ∫ τ, h τ ∂(gaussianReal 0 1) ≤ (a + prefixK q * σ2) ^ p := by
    have : h = fun τ => ∑ l ∈ Finset.range (p + 1),
        ((M * σ2) ^ l * a ^ (p - l) * (p.choose l : ℝ)) * τ ^ (2 * l) := funext hexpand
    rw [this, integral_finsetSum _ fun l _ => hint l]
    rw [show a + prefixK q * σ2 = prefixK q * σ2 + a by ring, add_pow]
    refine Finset.sum_le_sum fun l hl => ?_
    have hlp : l ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    rw [integral_const_mul]
    have hK := prefix_K_pow q l (hlp.trans hp)
    have e : (M * σ2) ^ l * a ^ (p - l) * (p.choose l : ℝ) * prefixMom l =
        (σ2 ^ l * a ^ (p - l) * (p.choose l : ℝ)) * ((1 + 4 * (q : ℝ)) ^ l * prefixMom l) := by
      rw [hM, mul_pow]; ring
    have e2 : (prefixK q * σ2) ^ l * a ^ (p - l) * (p.choose l : ℝ) =
        (σ2 ^ l * a ^ (p - l) * (p.choose l : ℝ)) * prefixK q ^ l := by
      rw [mul_pow]; ring
    rw [show ∫ τ, τ ^ (2 * l) ∂(gaussianReal 0 1) = prefixMom l from rfl, e, e2]
    exact mul_le_mul_of_nonneg_left hK (by positivity)
  have hlin : ∫⁻ τ, ENNReal.ofReal (h τ) ∂(gaussianReal 0 1) ≤
      ENNReal.ofReal ((a + prefixK q * σ2) ^ p) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hhint (Filter.Eventually.of_forall hh0)]
    exact ENNReal.ofReal_le_ofReal hhint_val
  -- combine
  have h2 : 2 * ∫⁻ τ, f τ ∂(gaussianReal 0 1) ≤
      2 * ∫⁻ τ, ENNReal.ofReal (h τ) ∂(gaussianReal 0 1) := by
    calc 2 * ∫⁻ τ, f τ ∂(gaussianReal 0 1)
        = ∫⁻ τ, f τ ∂(gaussianReal 0 1) + ∫⁻ τ, f (-τ) ∂(gaussianReal 0 1) := by
          rw [hneg, two_mul]
      _ = ∫⁻ τ, (f τ + f (-τ)) ∂(gaussianReal 0 1) := (lintegral_add_left hmeas _).symm
      _ ≤ ∫⁻ τ, 2 * ENNReal.ofReal (h τ) ∂(gaussianReal 0 1) := by
          refine lintegral_mono fun τ => ?_
          simp only [hf]
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          have : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
          rw [this, ← ENNReal.ofReal_mul (by norm_num)]
          exact ENNReal.ofReal_le_ofReal (hpt τ)
      _ = 2 * ∫⁻ τ, ENNReal.ofReal (h τ) ∂(gaussianReal 0 1) :=
          lintegral_const_mul _ (ENNReal.measurable_ofReal.comp (by fun_prop))
  have h3 := (ENNReal.mul_le_mul_iff_right (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)).mp h2
  exact h3.trans hlin

/-- Resampling the coordinates in `P`: `(ω, t) ↦ (t on P, ω off P)` preserves the standard
Gaussian product measure. -/
private theorem prefix_mp_piecewise {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P] :
    MeasurePreserving (fun z : (ι → ℝ) × (ι → ℝ) => fun i => if P i then z.2 i else z.1 i)
      ((Measure.pi fun _ : ι => gaussianReal 0 1).prod (Measure.pi fun _ : ι => gaussianReal 0 1))
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hmeas : Measurable
      (fun z : (ι → ℝ) × (ι → ℝ) => fun i => if P i then z.2 i else z.1 i) := by
    refine measurable_pi_iff.mpr fun i => ?_
    by_cases h : P i
    · simp only [h, ↓reduceIte]; exact (measurable_pi_apply i).comp measurable_snd
    · simp only [h, ↓reduceIte]; exact (measurable_pi_apply i).comp measurable_fst
  refine ⟨hmeas, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun z : (ι → ℝ) × (ι → ℝ) => fun i => if P i then z.2 i else z.1 i) ⁻¹'
      (Set.univ.pi s) = (Set.univ.pi fun i => if P i then Set.univ else s i) ×ˢ
        (Set.univ.pi fun i => if P i then s i else Set.univ) := by
    ext ⟨ω, t⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun i => ?_⟩
      · have := h i; by_cases hi : P i <;> simp [hi] at this ⊢; exact this
      · have := h i; by_cases hi : P i <;> simp [hi] at this ⊢; exact this
    · rintro ⟨h1, h2⟩ i
      have a1 := h1 i; have a2 := h2 i
      by_cases hi : P i <;> simp [hi] at a1 a2 ⊢
      · exact a2
      · exact a1
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : P i <;> simp [hi]

/-- A Gaussian vector `Σ t_i D_i` in a real inner product space added to `X`:
`E (‖X + Σ t_i D_i‖² + λ)^p ≤ (‖X‖² + λ + K Σ ‖D_i‖²)^p` for `p ≤ q`, uniformly in the
dimension. -/
private theorem prefix_gauss_vec (q : ℕ) {ι : Type*} [Fintype ι] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (D : ι → H) (lam : ℝ) (hlam : 0 ≤ lam)
    (s : Finset ι) :
    ∀ p ≤ q, ∀ X : H,
      ∫⁻ t, ENNReal.ofReal ((‖X + ∑ i ∈ s, t i • D i‖ ^ 2 + lam) ^ p)
          ∂(Measure.pi fun _ : ι => gaussianReal 0 1) ≤
        ENNReal.ofReal ((‖X‖ ^ 2 + lam + prefixK q * ∑ i ∈ s, ‖D i‖ ^ 2) ^ p) := by
  induction s using Finset.induction_on with
  | empty =>
    intro p hp X
    simp
  | insert a s ha ih =>
    intro p hp X
    set ν := Measure.pi fun _ : ι => gaussianReal (0 : ℝ) 1 with hν
    have hmp := prefix_mp_piecewise (ι := ι) (fun i => i = a)
    set pw := (fun z : (ι → ℝ) × (ι → ℝ) => fun i => if i = a then z.2 i else z.1 i) with hpwdef
    set F := fun t : ι → ℝ =>
      ENNReal.ofReal ((‖X + ∑ i ∈ insert a s, t i • D i‖ ^ 2 + lam) ^ p) with hF
    have step1 : ∫⁻ t, F t ∂ν ≤ ∫⁻ ω, ∫⁻ t, F (pw (ω, t)) ∂ν ∂ν := by
      calc ∫⁻ t, F t ∂ν = ∫⁻ t, F t ∂((ν.prod ν).map pw) := by rw [hmp.map_eq]
        _ ≤ ∫⁻ z, F (pw z) ∂(ν.prod ν) := lintegral_map_le _ hmp.measurable.aemeasurable
        _ ≤ _ := lintegral_prod_le _
    set u : (ι → ℝ) → ℝ := fun ω => ‖X + ∑ i ∈ s, ω i • D i‖ ^ 2 + lam with hu
    set v : ℝ := prefixK q * ‖D a‖ ^ 2 with hv
    have hpw : ∀ ω t, F (pw (ω, t)) =
        ENNReal.ofReal ((‖(X + ∑ i ∈ s, ω i • D i) + t a • D a‖ ^ 2 + lam) ^ p) := by
      intro ω t
      simp only [hF, hpwdef]
      rw [Finset.sum_insert ha]
      have : ∑ i ∈ s, (if i = a then t i else ω i) • D i = ∑ i ∈ s, ω i • D i :=
        Finset.sum_congr rfl fun i hi => by
          have hia : i ≠ a := fun h => ha (h ▸ hi)
          simp [hia]
      simp only [↓reduceIte] at *
      rw [this, add_comm (t a • D a), ← add_assoc]
    have step2 : ∀ ω, ∫⁻ t, F (pw (ω, t)) ∂ν ≤ ENNReal.ofReal ((u ω + v) ^ p) := by
      intro ω
      simp_rw [hpw]
      have hev := measurePreserving_eval (fun _ : ι => gaussianReal (0 : ℝ) 1) a
      have hg : Measurable fun τ : ℝ =>
          ENNReal.ofReal ((‖(X + ∑ i ∈ s, ω i • D i) + τ • D a‖ ^ 2 + lam) ^ p) :=
        ENNReal.measurable_ofReal.comp (by fun_prop : Continuous _).measurable
      have := hev.lintegral_comp hg
      simp only [Function.eval] at this
      rw [this]
      have h1 := prefix_gauss_one q p hp (X + ∑ i ∈ s, ω i • D i) (D a) lam hlam
      simpa [hu, hv, add_assoc] using h1
    have hmeasu : ∀ l, Measurable fun ω : ι → ℝ => ENNReal.ofReal (u ω ^ l) := fun l =>
      ENNReal.measurable_ofReal.comp (by fun_prop : Continuous fun ω : ι → ℝ => u ω ^ l).measurable
    have hu0 : ∀ ω, 0 ≤ u ω := fun ω => by simp only [hu]; positivity
    have hv0 : 0 ≤ v := mul_nonneg (prefix_K_nonneg q) (sq_nonneg _)
    set x : ℝ := ‖X‖ ^ 2 + lam + prefixK q * ∑ i ∈ s, ‖D i‖ ^ 2 with hx
    have hx0 : 0 ≤ x := by
      have := prefix_K_nonneg q
      have : 0 ≤ ∑ i ∈ s, ‖D i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      positivity
    have step3 : ∫⁻ ω, ENNReal.ofReal ((u ω + v) ^ p) ∂ν ≤ ENNReal.ofReal ((x + v) ^ p) := by
      have hexp : ∀ y : ℝ, 0 ≤ y → ENNReal.ofReal ((y + v) ^ p) = ∑ l ∈ Finset.range (p + 1),
          ENNReal.ofReal (y ^ l) * ENNReal.ofReal (v ^ (p - l) * (p.choose l : ℝ)) := by
        intro y hy
        rw [add_pow, ENNReal.ofReal_sum_of_nonneg (fun l _ => by positivity)]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [← ENNReal.ofReal_mul (by positivity), mul_assoc]
      calc ∫⁻ ω, ENNReal.ofReal ((u ω + v) ^ p) ∂ν
          = ∫⁻ ω, ∑ l ∈ Finset.range (p + 1),
              ENNReal.ofReal (u ω ^ l) * ENNReal.ofReal (v ^ (p - l) * (p.choose l : ℝ)) ∂ν :=
            lintegral_congr fun ω => hexp _ (hu0 ω)
        _ = ∑ l ∈ Finset.range (p + 1),
              ∫⁻ ω, ENNReal.ofReal (u ω ^ l) * ENNReal.ofReal (v ^ (p - l) * (p.choose l : ℝ)) ∂ν :=
            lintegral_finsetSum _ fun l _ => (hmeasu l).mul_const _
        _ = ∑ l ∈ Finset.range (p + 1),
              (∫⁻ ω, ENNReal.ofReal (u ω ^ l) ∂ν) *
                ENNReal.ofReal (v ^ (p - l) * (p.choose l : ℝ)) :=
            Finset.sum_congr rfl fun l _ => lintegral_mul_const _ (hmeasu l)
        _ ≤ ∑ l ∈ Finset.range (p + 1),
              ENNReal.ofReal (x ^ l) * ENNReal.ofReal (v ^ (p - l) * (p.choose l : ℝ)) := by
            refine Finset.sum_le_sum fun l hl => ?_
            have hlp : l ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
            gcongr
            exact ih l (hlp.trans hp) X
        _ = ENNReal.ofReal ((x + v) ^ p) := (hexp x hx0).symm
    calc ∫⁻ t, F t ∂ν ≤ ∫⁻ ω, ∫⁻ t, F (pw (ω, t)) ∂ν ∂ν := step1
      _ ≤ ∫⁻ ω, ENNReal.ofReal ((u ω + v) ^ p) ∂ν := lintegral_mono step2
      _ ≤ ENNReal.ofReal ((x + v) ^ p) := step3
      _ = _ := by
          rw [Finset.sum_insert ha, hx, hv]
          congr 2
          ring

/-! ### Hilbert–Schmidt norms and the free transfer matrices -/

/-- The squared Hilbert–Schmidt norm `Σ |X_{xy}|²`. -/
private def prefixHS {m : Type*} [Fintype m] (X : Matrix m m ℂ) : ℝ := ∑ i, ∑ j, ‖X i j‖ ^ 2

/-- The entries of a matrix as a vector of `EuclideanSpace`. -/
private def prefixFlat {m : Type*} [Fintype m] (X : Matrix m m ℂ) : EuclideanSpace ℂ (m × m) :=
  WithLp.toLp 2 (fun p => X p.1 p.2)

private theorem prefix_flat_sq {m : Type*} [Fintype m] (X : Matrix m m ℂ) :
    ‖prefixFlat X‖ ^ 2 = prefixHS X := by
  rw [EuclideanSpace.norm_sq_eq, prefixHS, ← Finset.univ_product_univ, Finset.sum_product]
  rfl

private theorem prefix_hs_nonneg {m : Type*} [Fintype m] (X : Matrix m m ℂ) : 0 ≤ prefixHS X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem prefix_flat_norm {m : Type*} [Fintype m] (X : Matrix m m ℂ) :
    ‖prefixFlat X‖ = Real.sqrt (prefixHS X) := by
  rw [← prefix_flat_sq, Real.sqrt_sq (norm_nonneg _)]

private theorem prefix_flat_add {m : Type*} [Fintype m] (X Y : Matrix m m ℂ) :
    prefixFlat (X + Y) = prefixFlat X + prefixFlat Y := by
  ext p; simp [prefixFlat]

private theorem prefix_flat_sub {m : Type*} [Fintype m] (X Y : Matrix m m ℂ) :
    prefixFlat (X - Y) = prefixFlat X - prefixFlat Y := by
  ext p; simp [prefixFlat]

private theorem prefix_flat_smul {m : Type*} [Fintype m] (c : ℝ) (X : Matrix m m ℂ) :
    prefixFlat (c • X) = c • prefixFlat X := by
  ext p; simp [prefixFlat]

private theorem prefix_flat_sum {m ι : Type*} [Fintype m] (s : Finset ι) (f : ι → Matrix m m ℂ) :
    prefixFlat (∑ i ∈ s, f i) = ∑ i ∈ s, prefixFlat (f i) := by
  ext p; simp [prefixFlat, Matrix.sum_apply]

/-- `[[M₀₀, M₀₁], [M₁₀, M₁₁]] ⊗ I_W` in the block form of the transfer matrices. -/
private def prefixLift (W : ℕ) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ :=
  Matrix.fromBlocks ((M 0 0 : ℂ) • 1) ((M 0 1 : ℂ) • 1) ((M 1 0 : ℂ) • 1) ((M 1 1 : ℂ) • 1)

private theorem prefix_lift_mul_apply_inl {W : ℕ} (M : Matrix (Fin 2) (Fin 2) ℝ)
    (Z : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) (α : Fin W) (y : Fin W ⊕ Fin W) :
    (prefixLift W M * Z) (Sum.inl α) y = M 0 0 * Z (Sum.inl α) y + M 0 1 * Z (Sum.inr α) y := by
  simp [prefixLift, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

private theorem prefix_lift_mul_apply_inr {W : ℕ} (M : Matrix (Fin 2) (Fin 2) ℝ)
    (Z : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) (α : Fin W) (y : Fin W ⊕ Fin W) :
    (prefixLift W M * Z) (Sum.inr α) y = M 1 0 * Z (Sum.inl α) y + M 1 1 * Z (Sum.inr α) y := by
  simp [prefixLift, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

private theorem prefix_mul_lift_apply_inl {W : ℕ} (M : Matrix (Fin 2) (Fin 2) ℝ)
    (Z : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) (x : Fin W ⊕ Fin W) (α : Fin W) :
    (Z * prefixLift W M) x (Sum.inl α) = Z x (Sum.inl α) * M 0 0 + Z x (Sum.inr α) * M 1 0 := by
  simp [prefixLift, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

private theorem prefix_mul_lift_apply_inr {W : ℕ} (M : Matrix (Fin 2) (Fin 2) ℝ)
    (Z : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) (x : Fin W ⊕ Fin W) (α : Fin W) :
    (Z * prefixLift W M) x (Sum.inr α) = Z x (Sum.inl α) * M 0 1 + Z x (Sum.inr α) * M 1 1 := by
  simp [prefixLift, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

private theorem prefix_lift_mul {W : ℕ} (M N : Matrix (Fin 2) (Fin 2) ℝ) :
    prefixLift W M * prefixLift W N = prefixLift W (M * N) := by
  ext (i | i) (j | j) <;>
  simp [prefixLift, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> split_ifs <;> ring

private theorem prefix_lift_one {W : ℕ} : prefixLift W 1 = 1 := by
  simp [prefixLift, Matrix.fromBlocks_one]

private theorem prefix_lift_pow {W : ℕ} (M : Matrix (Fin 2) (Fin 2) ℝ) (m : ℕ) :
    prefixLift W M ^ m = prefixLift W (M ^ m) := by
  induction m with
  | zero => simp [prefix_lift_one]
  | succ m ih => rw [pow_succ, ih, prefix_lift_mul, ← pow_succ]

private theorem prefix_blockT_eq {W : ℕ} (E : ℝ) :
    blockT (E : ℂ) (0 : Matrix (Fin W) (Fin W) ℂ) = prefixLift W (transferT E) := by
  simp [blockT, prefixLift, transferT]

/-- `‖a u + b v‖² ≤ (a² + b²)(‖u‖² + ‖v‖²)`. -/
private theorem prefix_two_sq (a b : ℝ) (u v : ℂ) :
    ‖(a : ℂ) * u + (b : ℂ) * v‖ ^ 2 ≤ (a ^ 2 + b ^ 2) * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  have h1 : ‖(a : ℂ) * u + (b : ℂ) * v‖ ≤ |a| * ‖u‖ + |b| * ‖v‖ := by
    refine (norm_add_le _ _).trans ?_
    simp [Complex.norm_real]
  have h0 : 0 ≤ ‖(a : ℂ) * u + (b : ℂ) * v‖ := norm_nonneg _
  have h2 : (|a| * ‖u‖ + |b| * ‖v‖) ^ 2 ≤ (a ^ 2 + b ^ 2) * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    have := sq_nonneg (|a| * ‖v‖ - |b| * ‖u‖)
    have ha := sq_abs a
    have hb := sq_abs b
    nlinarith
  calc _ ≤ (|a| * ‖u‖ + |b| * ‖v‖) ^ 2 := by gcongr
    _ ≤ _ := h2

private theorem prefix_two_sq' (a b : ℝ) (u v : ℂ) :
    ‖u * (a : ℂ) + v * (b : ℂ)‖ ^ 2 ≤ (a ^ 2 + b ^ 2) * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  rw [mul_comm u, mul_comm v]; exact prefix_two_sq a b u v

/-- The squared Frobenius norm of a real `2 × 2` matrix. -/
private def prefixFrob (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := ∑ i, ∑ j, M i j ^ 2

private theorem prefix_hs_lift_mul {W : ℕ} (M : Matrix (Fin 2) (Fin 2) ℝ)
    (Z : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    prefixHS (prefixLift W M * Z) ≤ prefixFrob M * prefixHS Z := by
  unfold prefixHS prefixFrob
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [prefix_lift_mul_apply_inl, prefix_lift_mul_apply_inr, Fin.sum_univ_two]
  have h1 : ∀ α y, ‖(M 0 0 : ℂ) * Z (Sum.inl α) y + (M 0 1 : ℂ) * Z (Sum.inr α) y‖ ^ 2 ≤
      (M 0 0 ^ 2 + M 0 1 ^ 2) * (‖Z (Sum.inl α) y‖ ^ 2 + ‖Z (Sum.inr α) y‖ ^ 2) :=
    fun α y => prefix_two_sq _ _ _ _
  have h2 : ∀ α y, ‖(M 1 0 : ℂ) * Z (Sum.inl α) y + (M 1 1 : ℂ) * Z (Sum.inr α) y‖ ^ 2 ≤
      (M 1 0 ^ 2 + M 1 1 ^ 2) * (‖Z (Sum.inl α) y‖ ^ 2 + ‖Z (Sum.inr α) y‖ ^ 2) :=
    fun α y => prefix_two_sq _ _ _ _
  have s1 := Finset.sum_le_sum fun α (_ : α ∈ Finset.univ) =>
    Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) => h1 α y
  have s2 := Finset.sum_le_sum fun α (_ : α ∈ Finset.univ) =>
    Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) => h2 α y
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at s1 s2
  have e : (M 0 0 ^ 2 + M 0 1 ^ 2 + (M 1 0 ^ 2 + M 1 1 ^ 2)) *
      (∑ α, ∑ y, ‖Z (Sum.inl α) y‖ ^ 2 + ∑ α, ∑ y, ‖Z (Sum.inr α) y‖ ^ 2) =
      (M 0 0 ^ 2 + M 0 1 ^ 2) * (∑ α, ∑ y, ‖Z (Sum.inl α) y‖ ^ 2 +
        ∑ α, ∑ y, ‖Z (Sum.inr α) y‖ ^ 2) +
      (M 1 0 ^ 2 + M 1 1 ^ 2) * (∑ α, ∑ y, ‖Z (Sum.inl α) y‖ ^ 2 +
        ∑ α, ∑ y, ‖Z (Sum.inr α) y‖ ^ 2) := by ring
  rw [e]
  linarith

private theorem prefix_hs_mul_lift {W : ℕ} (M : Matrix (Fin 2) (Fin 2) ℝ)
    (Z : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    prefixHS (Z * prefixLift W M) ≤ prefixFrob M * prefixHS Z := by
  unfold prefixHS prefixFrob
  simp only [Fintype.sum_sum_type, prefix_mul_lift_apply_inl, prefix_mul_lift_apply_inr,
    Fin.sum_univ_two]
  have h1 : ∀ x α, ‖Z x (Sum.inl α) * (M 0 0 : ℂ) + Z x (Sum.inr α) * (M 1 0 : ℂ)‖ ^ 2 ≤
      (M 0 0 ^ 2 + M 1 0 ^ 2) * (‖Z x (Sum.inl α)‖ ^ 2 + ‖Z x (Sum.inr α)‖ ^ 2) :=
    fun x α => prefix_two_sq' _ _ _ _
  have h2 : ∀ x α, ‖Z x (Sum.inl α) * (M 0 1 : ℂ) + Z x (Sum.inr α) * (M 1 1 : ℂ)‖ ^ 2 ≤
      (M 0 1 ^ 2 + M 1 1 ^ 2) * (‖Z x (Sum.inl α)‖ ^ 2 + ‖Z x (Sum.inr α)‖ ^ 2) :=
    fun x α => prefix_two_sq' _ _ _ _
  set c1 := M 0 0 ^ 2 + M 1 0 ^ 2
  set c2 := M 0 1 ^ 2 + M 1 1 ^ 2
  have key : ∀ x, (∑ α, ‖Z x (Sum.inl α) * (M 0 0 : ℂ) + Z x (Sum.inr α) * (M 1 0 : ℂ)‖ ^ 2 +
      ∑ α, ‖Z x (Sum.inl α) * (M 0 1 : ℂ) + Z x (Sum.inr α) * (M 1 1 : ℂ)‖ ^ 2) ≤
      (c1 + c2) * (∑ α, ‖Z x (Sum.inl α)‖ ^ 2 + ∑ α, ‖Z x (Sum.inr α)‖ ^ 2) := by
    intro x
    have s1 := Finset.sum_le_sum fun α (_ : α ∈ Finset.univ) => h1 x α
    have s2 := Finset.sum_le_sum fun α (_ : α ∈ Finset.univ) => h2 x α
    simp only [← Finset.mul_sum, Finset.sum_add_distrib] at s1 s2
    nlinarith
  have k1 := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => key (Sum.inl x)
  have k2 := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => key (Sum.inr x)
  simp only [← Finset.mul_sum] at k1 k2
  have e : M 0 0 ^ 2 + M 0 1 ^ 2 + (M 1 0 ^ 2 + M 1 1 ^ 2) = c1 + c2 := by ring
  rw [e]
  nlinarith

/-- `sin ϑ ≥ κ/2` for `2 cos ϑ = E` in the bulk. -/
private theorem prefix_sin_ge {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ) :
    κ / 2 ≤ Real.sin (Real.arccos (E / 2)) := by
  have hS := Real.sin_arccos (E / 2)
  set S := Real.sin (Real.arccos (E / 2))
  have hE2 : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hE 2
  have hpos : 0 ≤ 1 - (E / 2) ^ 2 := by nlinarith
  have hS2 : S ^ 2 = 1 - (E / 2) ^ 2 := by rw [hS, Real.sq_sqrt hpos]
  have hS1 : S ≤ 1 := Real.sin_le_one _
  have hS0 : 0 ≤ S := by rw [hS]; exact Real.sqrt_nonneg _
  nlinarith

/-- The entries of `T(E)^m` are at most `2/κ` in the bulk. -/
private theorem prefix_T2_entry {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (m : ℕ) (i j : Fin 2) : |(transferT E ^ m) i j| ≤ 2 / κ := by
  have hE' : |E / 2| ≤ 1 := by rw [abs_div]; norm_num; linarith
  have h1 : -1 ≤ E / 2 := (abs_le.mp hE').1
  have h2 : E / 2 ≤ 1 := (abs_le.mp hE').2
  have hlt1 : E / 2 < 1 := by have := (abs_le.mp hE).2; linarith
  have hgt1 : -1 < E / 2 := by have := (abs_le.mp hE).1; linarith
  set ϑ := Real.arccos (E / 2)
  have hcos : 2 * Real.cos ϑ = E := by rw [Real.cos_arccos h1 h2]; ring
  have h0 : 0 < ϑ := Real.arccos_pos.mpr hlt1
  have hπ : ϑ < Real.pi := Real.arccos_lt_pi.mpr hgt1
  have hb := transferT_pow_le ϑ h0 hπ m i j
  rw [hcos] at hb
  have hs := prefix_sin_ge hκ hκ2 hE
  have hs0 : 0 < Real.sin ϑ := by linarith
  refine hb.trans ?_
  rw [inv_eq_one_div, div_le_div_iff₀ hs0 hκ]
  linarith

/-- The inverse free transfer matrix `T(E)^{-1} = [[0, 1], [-1, E]]`. -/
private def prefixTi2 (E : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, E]

private def prefixSwap : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

private theorem prefix_swap_sq : prefixSwap * prefixSwap = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [prefixSwap, Matrix.mul_apply, Fin.sum_univ_two]

private theorem prefix_Ti2_eq (E : ℝ) : prefixTi2 E = prefixSwap * transferT E * prefixSwap := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [prefixSwap, prefixTi2, transferT, Matrix.mul_apply, Fin.sum_univ_two]

private theorem prefix_Ti2_pow (E : ℝ) (m : ℕ) :
    prefixTi2 E ^ m = prefixSwap * transferT E ^ m * prefixSwap := by
  induction m with
  | zero => simp [prefix_swap_sq]
  | succ m ih =>
    rw [pow_succ, ih, prefix_Ti2_eq, pow_succ]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc prefixSwap prefixSwap, prefix_swap_sq, Matrix.one_mul]

private theorem prefix_T2_Ti2 (E : ℝ) : transferT E * prefixTi2 E = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [prefixTi2, transferT, Matrix.mul_apply, Fin.sum_univ_two]

private theorem prefix_Ti2_T2 (E : ℝ) : prefixTi2 E * transferT E = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [prefixTi2, transferT, Matrix.mul_apply, Fin.sum_univ_two]

private theorem prefix_frob_le {M : Matrix (Fin 2) (Fin 2) ℝ} {c : ℝ}
    (h : ∀ i j, |M i j| ≤ c) : prefixFrob M ≤ 4 * c ^ 2 := by
  have hc : ∀ i j, M i j ^ 2 ≤ c ^ 2 := fun i j => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h i j) 2
  unfold prefixFrob
  simp only [Fin.sum_univ_two]
  linarith [hc 0 0, hc 0 1, hc 1 0, hc 1 1]

private theorem prefix_frob_T {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (m : ℕ) : prefixFrob (transferT E ^ m) ≤ 16 / κ ^ 2 := by
  refine (prefix_frob_le (prefix_T2_entry hκ hκ2 hE m)).trans (le_of_eq ?_)
  field_simp; ring

private theorem prefix_frob_Ti {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (m : ℕ) : prefixFrob (prefixTi2 E ^ m) ≤ 16 / κ ^ 2 := by
  refine (prefix_frob_le (c := 2 / κ) fun i j => ?_).trans (le_of_eq ?_)
  · rw [prefix_Ti2_pow]
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
      simp [prefixSwap] <;>
      exact prefix_T2_entry hκ hκ2 hE m _ _
  · field_simp; ring

private theorem prefix_T_Ti {W : ℕ} (E : ℝ) :
    prefixLift W (transferT E) * prefixLift W (prefixTi2 E) = 1 := by
  rw [prefix_lift_mul, prefix_T2_Ti2, prefix_lift_one]

private theorem prefix_Ti_T {W : ℕ} (E : ℝ) :
    prefixLift W (prefixTi2 E) * prefixLift W (transferT E) = 1 := by
  rw [prefix_lift_mul, prefix_Ti2_T2, prefix_lift_one]

private theorem prefix_pow_Ti_pow {W : ℕ} (E : ℝ) (m : ℕ) :
    blockT (E : ℂ) (0 : Matrix (Fin W) (Fin W) ℂ) ^ m * prefixLift W (prefixTi2 E) ^ m = 1 := by
  rw [prefix_blockT_eq]
  have hc : Commute (prefixLift W (transferT E)) (prefixLift W (prefixTi2 E)) := by
    unfold Commute SemiconjBy; rw [prefix_T_Ti, prefix_Ti_T]
  rw [← hc.mul_pow, prefix_T_Ti, one_pow]

private theorem prefix_hs_split {W : ℕ} (Y : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    prefixHS Y = ∑ α, ∑ y, ‖Y (Sum.inl α) y‖ ^ 2 + ∑ α, ∑ y, ‖Y (Sum.inr α) y‖ ^ 2 := by
  unfold prefixHS; rw [Fintype.sum_sum_type]

private theorem prefix_hs_top_le {W : ℕ} (Y : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    ∑ α, ∑ y, ‖Y (Sum.inl α) y‖ ^ 2 ≤ prefixHS Y := by
  rw [prefix_hs_split]
  have : 0 ≤ ∑ α, ∑ y, ‖Y (Sum.inr α) y‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

private theorem prefix_hs_iota {W : ℕ} (H : Matrix (Fin W) (Fin W) ℂ)
    (Y : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    prefixHS (Matrix.fromBlocks H 0 0 0 * Y) =
      ∑ α, ∑ y, ‖∑ β, H α β * Y (Sum.inl β) y‖ ^ 2 := by
  rw [prefix_hs_split]
  simp [Matrix.mul_apply, Fintype.sum_sum_type]

private theorem prefix_hs_iota_smul_one {W : ℕ} (c : ℂ)
    (Y : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    prefixHS (Matrix.fromBlocks (c • (1 : Matrix (Fin W) (Fin W) ℂ)) 0 0 0 * Y) ≤
      ‖c‖ ^ 2 * prefixHS Y := by
  rw [prefix_hs_iota]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, norm_mul, mul_pow]
  simp_rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (prefix_hs_top_le Y) (sq_nonneg _)

/-- Completeness of the Hermitian basis: `Σ_k |Σ_β (T_k)_{αβ} z_β|² = Σ_β |z_β|²`. -/
private theorem prefix_herm_complete_one {W : ℕ} (α : Fin W) (z : Fin W → ℂ) :
    ∑ k : Fin W × Fin W, ‖∑ β, hermBasis W k α β * z β‖ ^ 2 = ∑ β, ‖z β‖ ^ 2 := by
  have hn : ∀ w : ℂ, ‖w‖ ^ 2 = (w * (starRingEnd ℂ) w).re := fun w => by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  simp_rw [hn]
  rw [← Complex.re_sum, ← Complex.re_sum]
  congr 1
  have hc : ∀ k β', (starRingEnd ℂ) (hermBasis W k α β') = hermBasis W k β' α := fun k β' =>
    (hermBasis_isHermitian W k).apply β' α
  have e1 : ∀ k, (∑ β, hermBasis W k α β * z β) * (starRingEnd ℂ) (∑ β, hermBasis W k α β * z β) =
      ∑ β, ∑ β', (hermBasis W k α β * hermBasis W k β' α) * (z β * (starRingEnd ℂ) (z β')) := by
    intro k
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun β' _ => ?_
    rw [map_mul, hc]; ring
  simp_rw [e1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, sum_hermBasis_apply_mul_apply]
  simp

private theorem prefix_herm_complete {W : ℕ} (Y : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    ∑ k : Fin W × Fin W, prefixHS (Matrix.fromBlocks (hermBasis W k) 0 0 0 * Y) ≤
      W * prefixHS Y := by
  simp_rw [prefix_hs_iota]
  rw [Finset.sum_comm]
  have : ∀ α : Fin W, ∑ k : Fin W × Fin W, ∑ y, ‖∑ β, hermBasis W k α β * Y (Sum.inl β) y‖ ^ 2 =
      ∑ y, ∑ β, ‖Y (Sum.inl β) y‖ ^ 2 := by
    intro α
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => prefix_herm_complete_one α (fun β => Y (Sum.inl β) y)
  simp_rw [this]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_comm]
  exact mul_le_mul_of_nonneg_left (prefix_hs_top_le Y) (Nat.cast_nonneg _)

private theorem prefix_hs_mul_le {m : Type*} [Fintype m] (A B : Matrix m m ℂ) :
    prefixHS (A * B) ≤ prefixHS A * prefixHS B := by
  unfold prefixHS
  have h : ∀ i j, ‖(A * B) i j‖ ^ 2 ≤ (∑ k, ‖A i k‖ ^ 2) * (∑ k, ‖B k j‖ ^ 2) := by
    intro i j
    rw [Matrix.mul_apply]
    have h1 : ‖∑ k, A i k * B k j‖ ≤ ∑ k, ‖A i k‖ * ‖B k j‖ :=
      (norm_sum_le _ _).trans (by simp)
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖A i k‖) (fun k => ‖B k j‖)
    calc _ ≤ (∑ k, ‖A i k‖ * ‖B k j‖) ^ 2 := by gcongr
      _ ≤ _ := h2
  calc ∑ i, ∑ j, ‖(A * B) i j‖ ^ 2 ≤ ∑ i, ∑ j, (∑ k, ‖A i k‖ ^ 2) * (∑ k, ‖B k j‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = (∑ i, ∑ k, ‖A i k‖ ^ 2) * (∑ j, ∑ k, ‖B k j‖ ^ 2) := by
        rw [Finset.sum_mul_sum]
    _ = (∑ i, ∑ j, ‖A i j‖ ^ 2) * (∑ i, ∑ j, ‖B i j‖ ^ 2) := by
        rw [Finset.sum_comm (f := fun j k => ‖B k j‖ ^ 2)]

/-- The operator norm is at most the Hilbert–Schmidt norm. -/
private theorem prefix_op_le_hs {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) :
    ‖A‖ ≤ Real.sqrt (prefixHS A) := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [mul_pow, Real.sq_sqrt (prefix_hs_nonneg A), EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  simp only [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct]
  rw [prefixHS, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖∑ j, A i j * x.ofLp j‖ ≤ ∑ j, ‖A i j‖ * ‖x.ofLp j‖ :=
    (norm_sum_le _ _).trans (by simp)
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖A i j‖) (fun j => ‖x.ofLp j‖)
  calc _ ≤ (∑ j, ‖A i j‖ * ‖x.ofLp j‖) ^ 2 := by gcongr
    _ ≤ _ := h2

private theorem prefix_hs_one (W : ℕ) :
    prefixHS (1 : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) = 2 * W := by
  have h : ∀ i j : Fin W ⊕ Fin W,
      ‖(1 : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) i j‖ ^ 2 = if i = j then 1 else 0 := by
    intro i j; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  simp only [prefixHS, h, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const,
    Finset.card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast; ring

/-! ### The rescaled prefixes `Q_j - I` of the proof of Lemma 7.7 [uvc:lem:cells] -/

/-- The increment `T(E)^{-(i+1)} (T_r(z) - T(E)) T(E)^i (I + X)` of the rescaled prefix. -/
private def prefixInc {W L : ℕ} (E s : ℝ) (z : ℂ) (r : Fin L) (i : ℕ)
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (X : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ :=
  prefixLift W (prefixTi2 E) ^ (i + 1) *
    (blockT z (((Real.sqrt s : ℝ) : ℂ) • V r) - blockT (E : ℂ) 0) * blockT (E : ℂ) 0 ^ i *
      (1 + X)

/-- The rescaled prefix `Q_i - I = T(E)^{-i} T_{b+i-1}(z) ⋯ T_b(z) - I`, stopped at the first step
where the predicate `G` fails. -/
private def prefixProc {W L : ℕ} (G : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ → Prop)
    (E s : ℝ) (z : ℂ) (b : Fin L) (ω : Ω W L) : ℕ → Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ
  | 0 => 0
  | i + 1 =>
    if G (prefixProc G E s z b ω i) then
      prefixProc G E s z b ω i +
        prefixInc E s z ((finRotate L ^ i) b) i (gueBlock W L ω) (prefixProc G E s z b ω i)
    else prefixProc G E s z b ω i

/-- With the trivial predicate, `Q_i - I = T(E)^{-i} P_i(z) - I`. -/
private theorem prefix_proc_plain {W L : ℕ} (E s : ℝ) (z : ℂ) (b : Fin L) (ω : Ω W L) (i : ℕ) :
    prefixProc (fun _ => True) E s z b ω i = prefixLift W (prefixTi2 E) ^ i *
      cellProd z (fun r => ((Real.sqrt s : ℝ) : ℂ) • gueBlock W L ω r) b i - 1 := by
  induction i with
  | zero => simp [prefixProc, cellProd]
  | succ i ih =>
    simp only [prefixProc, ↓reduceIte, prefixInc]
    rw [ih]
    set Ti := prefixLift W (prefixTi2 E)
    set T := blockT (E : ℂ) (0 : Matrix (Fin W) (Fin W) ℂ)
    set P := cellProd z (fun r => ((Real.sqrt s : ℝ) : ℂ) • gueBlock W L ω r) b i
    set Bz := blockT z (((Real.sqrt s : ℝ) : ℂ) • gueBlock W L ω ((finRotate L ^ i) b))
    have hP1 : cellProd z (fun r => ((Real.sqrt s : ℝ) : ℂ) • gueBlock W L ω r) b (i + 1) =
        Bz * P := rfl
    have hTT : T ^ i * Ti ^ i = 1 := prefix_pow_Ti_pow E i
    have hTiT : Ti ^ (i + 1) * T = Ti ^ i := by
      have : Ti * T = 1 := by
        simp only [Ti, T]; rw [prefix_blockT_eq]; exact prefix_Ti_T E
      rw [pow_succ, Matrix.mul_assoc, this, Matrix.mul_one]
    have h1 : 1 + (Ti ^ i * P - 1) = Ti ^ i * P := by abel
    rw [hP1, h1]
    have h2 : Ti ^ (i + 1) * (Bz - T) * T ^ i * (Ti ^ i * P) =
        Ti ^ (i + 1) * (Bz * P) - Ti ^ i * P := by
      calc Ti ^ (i + 1) * (Bz - T) * T ^ i * (Ti ^ i * P)
          = Ti ^ (i + 1) * (Bz - T) * ((T ^ i * Ti ^ i) * P) := by
            simp only [Matrix.mul_assoc]
        _ = Ti ^ (i + 1) * (Bz * P) - (Ti ^ (i + 1) * T) * P := by
            rw [hTT, Matrix.one_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
              Matrix.mul_assoc]
        _ = _ := by rw [hTiT]
    rw [h2]
    abel

private theorem prefix_rot_val {L : ℕ} (r : Fin L) : (finRotate L r).val = (r.val + 1) % L := by
  cases L with
  | zero => exact r.elim0
  | succ L =>
    rw [coe_finRotate]
    split_ifs with h
    · subst h; simp
    · have := Fin.val_lt_last h
      rw [Nat.mod_eq_of_lt (by omega)]

private theorem prefix_rotPow_val {L : ℕ} (r : Fin L) (m : ℕ) :
    ((finRotate L ^ m) r).val = (r.val + m) % L := by
  induction m with
  | zero => simp [Nat.mod_eq_of_lt r.isLt]
  | succ m ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, prefix_rot_val, ih, Nat.mod_add_mod, add_assoc]

/-- The blocks `b, b + 1, …, b + i` are distinct for `i < L`. -/
private theorem prefix_rot_ne {L : ℕ} (b : Fin L) {i i' : ℕ} (h : i' < i) (hi : i < L) :
    (finRotate L ^ i') b ≠ (finRotate L ^ i) b := by
  intro heq
  have := congrArg Fin.val heq
  rw [prefix_rotPow_val, prefix_rotPow_val] at this
  have hb := b.isLt
  rcases Nat.lt_or_ge (b.val + i) L with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega)] at this; omega
  · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega : b.val + i - L < L)] at this
    rcases Nat.lt_or_ge (b.val + i') L with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at this; omega
    · rw [Nat.mod_eq_sub_mod h2, Nat.mod_eq_of_lt (by omega)] at this; omega

/-- The rescaled prefix after `i` steps depends only on the blocks `b, …, b + i - 1`. -/
private theorem prefix_proc_local {W L : ℕ} (G : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ → Prop)
    (E s : ℝ) (z : ℂ) (b : Fin L) (ω ω' : Ω W L) :
    ∀ i, (∀ i' < i, ∀ k : Fin W × Fin W,
      ω ((finRotate L ^ i') b, k) = ω' ((finRotate L ^ i') b, k)) →
      prefixProc G E s z b ω i = prefixProc G E s z b ω' i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro h
    have hi := ih (fun i' hi' k => h i' (by omega) k)
    have hk := h i (by omega)
    have hg : gueBlock W L ω ((finRotate L ^ i) b) = gueBlock W L ω' ((finRotate L ^ i) b) := by
      ext α β
      simp only [gueBlock, Matrix.of_apply, hk]
    simp only [prefixProc, prefixInc, hi, hg]

/-- The deterministic part `T(E)^{-(i+1)} [[(z - E) I, 0], [0, 0]] T(E)^i (I + X)` of the
increment. -/
private def prefixDrift {W : ℕ} (E : ℝ) (z : ℂ) (i : ℕ)
    (X : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ :=
  prefixLift W (prefixTi2 E) ^ (i + 1) *
    Matrix.fromBlocks (((z - E) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)) 0 0 0 *
      blockT (E : ℂ) 0 ^ i * (1 + X)

/-- The Gaussian part of the increment, as the coefficient of the coordinate `x` of the sample. -/
private def prefixDx {W L : ℕ} (E s : ℝ) (r : Fin L) (i : ℕ)
    (X : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) (x : Fin L × Fin W × Fin W) :
    Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ :=
  if x.1 = r then
    -(prefixLift W (prefixTi2 E) ^ (i + 1) *
      Matrix.fromBlocks (((Real.sqrt s / Real.sqrt W : ℝ) : ℂ) • hermBasis W x.2) 0 0 0 *
        blockT (E : ℂ) 0 ^ i * (1 + X))
  else 0

private theorem prefix_fromBlocks_sum {W : ℕ} {ι : Type*} (t : Finset ι)
    (f : ι → Matrix (Fin W) (Fin W) ℂ) :
    Matrix.fromBlocks (∑ k ∈ t, f k) 0 0 (0 : Matrix (Fin W) (Fin W) ℂ) =
      ∑ k ∈ t, Matrix.fromBlocks (f k) 0 0 (0 : Matrix (Fin W) (Fin W) ℂ) := by
  ext (i | i) (j | j) <;> simp [Matrix.sum_apply]

private theorem prefix_fromBlocks_smul {W : ℕ} (c : ℂ) (M : Matrix (Fin W) (Fin W) ℂ) :
    Matrix.fromBlocks (c • M) 0 0 (0 : Matrix (Fin W) (Fin W) ℂ) =
      c • Matrix.fromBlocks M 0 0 (0 : Matrix (Fin W) (Fin W) ℂ) := by
  ext (i | i) (j | j) <;> simp

private theorem prefix_blockT_sub {W : ℕ} (z : ℂ) (E : ℝ) (V : Matrix (Fin W) (Fin W) ℂ) :
    blockT z V - blockT (E : ℂ) 0 =
      Matrix.fromBlocks (((z - E) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)) 0 0 0 -
        Matrix.fromBlocks V 0 0 0 := by
  ext (i | i) (j | j) <;> simp [blockT, Matrix.one_apply]
  split_ifs <;> ring

/-- The increment splits into the drift and a linear combination of the Gaussian coordinates. -/
private theorem prefix_inc_eq {W L : ℕ} (E s : ℝ) (z : ℂ) (r : Fin L) (i : ℕ) (ω : Ω W L)
    (X : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    prefixInc E s z r i (gueBlock W L ω) X =
      prefixDrift E z i X + ∑ x, (ω x : ℂ) • prefixDx E s r i X x := by
  set Ti := prefixLift W (prefixTi2 E)
  set T := blockT (E : ℂ) (0 : Matrix (Fin W) (Fin W) ℂ)
  set c : ℂ := ((Real.sqrt s / Real.sqrt W : ℝ) : ℂ)
  have hV : ((Real.sqrt s : ℝ) : ℂ) • gueBlock W L ω r =
      ∑ k : Fin W × Fin W, (ω (r, k) : ℂ) • (c • hermBasis W k) := by
    rw [gueBlock_eq_sum_hermBasis, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [smul_smul, c]
    congr 1
    push_cast
    ring
  have hsum : ∑ x, (ω x : ℂ) • prefixDx E s r i X x =
      -∑ k : Fin W × Fin W, (ω (r, k) : ℂ) •
        (Ti ^ (i + 1) * Matrix.fromBlocks (c • hermBasis W k) 0 0 0 * T ^ i * (1 + X)) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single r]
    · simp only [prefixDx, ↓reduceIte, smul_neg, Finset.sum_neg_distrib]
      rfl
    · intro a _ ha
      simp [prefixDx, ha]
    · intro h; exact absurd (Finset.mem_univ r) h
  rw [hsum]
  unfold prefixInc prefixDrift
  rw [prefix_blockT_sub, hV, prefix_fromBlocks_sum]
  simp only [prefix_fromBlocks_smul, Matrix.mul_sub, Matrix.sub_mul, Finset.mul_sum,
    Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  abel

/-! ### Measurability -/

private theorem prefix_meas_gue {W L : ℕ} (r : Fin L) (α β : Fin W) :
    Measurable fun ω : Ω W L => gueBlock W L ω r α β := by
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

private theorem prefix_meas_mul {W L : ℕ} {n : Type*} [Fintype n] {f g : Ω W L → Matrix n n ℂ}
    (hf : ∀ p q, Measurable fun ω => f ω p q) (hg : ∀ p q, Measurable fun ω => g ω p q) :
    ∀ p q, Measurable fun ω => (f ω * g ω) p q := fun p q => by
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => (hf p k).mul (hg k q)

private theorem prefix_meas_add {W L : ℕ} {n : Type*} {f g : Ω W L → Matrix n n ℂ}
    (hf : ∀ p q, Measurable fun ω => f ω p q) (hg : ∀ p q, Measurable fun ω => g ω p q) :
    ∀ p q, Measurable fun ω => (f ω + g ω) p q := fun p q => by
  simp only [Matrix.add_apply]
  exact (hf p q).add (hg p q)

private theorem prefix_meas_sub {W L : ℕ} {n : Type*} {f g : Ω W L → Matrix n n ℂ}
    (hf : ∀ p q, Measurable fun ω => f ω p q) (hg : ∀ p q, Measurable fun ω => g ω p q) :
    ∀ p q, Measurable fun ω => (f ω - g ω) p q := fun p q => by
  simp only [Matrix.sub_apply]
  exact (hf p q).sub (hg p q)

private theorem prefix_meas_const {W L : ℕ} {n : Type*} (M : Matrix n n ℂ) :
    ∀ p q, Measurable fun _ : Ω W L => M p q := fun _ _ => measurable_const

private theorem prefix_meas_blockT {W L : ℕ} (z : ℂ) (c : ℂ) (r : Fin L) :
    ∀ p q, Measurable fun ω : Ω W L => blockT z (c • gueBlock W L ω r) p q := by
  intro p q
  rcases p with p | p <;> rcases q with q | q <;>
    simp only [blockT, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul]
  · exact measurable_const.sub (measurable_const.mul (prefix_meas_gue r p q))
  all_goals exact measurable_const

private theorem prefix_meas_hs {W L : ℕ} {n : Type*} [Fintype n] {f : Ω W L → Matrix n n ℂ}
    (hf : ∀ p q, Measurable fun ω => f ω p q) : Measurable fun ω => prefixHS (f ω) := by
  unfold prefixHS
  exact Finset.measurable_sum _ fun p _ => Finset.measurable_sum _ fun q _ =>
    ((hf p q).norm).pow_const 2

private theorem prefix_meas_proc {W L : ℕ} (G : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ → Prop)
    (hG : ∀ f : Ω W L → Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ,
      (∀ p q, Measurable fun ω => f ω p q) → MeasurableSet {ω | G (f ω)})
    (E s : ℝ) (z : ℂ) (b : Fin L) :
    ∀ i p q, Measurable fun ω => prefixProc G E s z b ω i p q := by
  intro i
  induction i with
  | zero => intro p q; simp only [prefixProc]; exact measurable_const
  | succ i ih =>
    have hinc : ∀ p q, Measurable fun ω => (prefixProc G E s z b ω i +
        prefixInc E s z ((finRotate L ^ i) b) i (gueBlock W L ω)
          (prefixProc G E s z b ω i)) p q := by
      refine prefix_meas_add ih ?_
      unfold prefixInc
      refine prefix_meas_mul (prefix_meas_mul (prefix_meas_mul (prefix_meas_const _)
        (prefix_meas_sub (prefix_meas_blockT _ _ _) (prefix_meas_const _))) (prefix_meas_const _))
        (prefix_meas_add (prefix_meas_const _) ih)
    intro p q
    simp only [prefixProc]
    have e : (fun ω => (if G (prefixProc G E s z b ω i) then prefixProc G E s z b ω i +
        prefixInc E s z ((finRotate L ^ i) b) i (gueBlock W L ω) (prefixProc G E s z b ω i)
        else prefixProc G E s z b ω i) p q) = fun ω => if G (prefixProc G E s z b ω i) then
        (prefixProc G E s z b ω i + prefixInc E s z ((finRotate L ^ i) b) i (gueBlock W L ω)
          (prefixProc G E s z b ω i)) p q else prefixProc G E s z b ω i p q := by
      funext ω; split_ifs <;> rfl
    rw [e]
    exact Measurable.ite (hG _ ih) (hinc p q) (ih p q)

/-! ### One step of the moment recursion -/

/-- The bound `16/κ²` on the squared Frobenius norms of `T(E)^{±m}` in the bulk. -/
private def prefixF (κ : ℝ) : ℝ := 16 / κ ^ 2

/-- The growth rate of the moment recursion. -/
private def prefixA (κ : ℝ) (q : ℕ) : ℝ :=
  3 * prefixF κ + 2 * prefixF κ ^ 2 + 2 * prefixK q * prefixF κ ^ 2

private theorem prefix_F_pos {κ : ℝ} (hκ : 0 < κ) : 0 < prefixF κ := by
  unfold prefixF; positivity

private theorem prefix_A_nonneg {κ : ℝ} (hκ : 0 < κ) (q : ℕ) : 0 ≤ prefixA κ q := by
  unfold prefixA
  have := prefix_F_pos hκ
  have := prefix_K_nonneg q
  positivity

/-- The scalar inequality behind one step: with `δ = d/n`, `s = σ/n`, `d, σ ≤ 1`. -/
private theorem prefix_real_bound (x w F K d σ n : ℝ) (hF : 0 ≤ F)
    (hK : 0 ≤ K) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hn : 1 ≤ n) :
    (x + F * (d / n) * (w + x)) ^ 2 + w ^ 2 * (d ^ 2 + σ) +
        K * (F ^ 2 * ((σ / n) * (w + x) ^ 2)) ≤
      (x ^ 2 + w ^ 2 * (d ^ 2 + σ)) * (1 + (3 * F + 2 * F ^ 2 + 2 * K * F ^ 2) / n) := by
  have hn0 : 0 < n := by linarith
  set a := 1 / n with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by rw [ha, div_le_one hn0]; exact hn
  have e1 : d / n = d * a := by rw [ha]; ring
  have e2 : σ / n = σ * a := by rw [ha]; ring
  have e3 : (3 * F + 2 * F ^ 2 + 2 * K * F ^ 2) / n = (3 * F + 2 * F ^ 2 + 2 * K * F ^ 2) * a := by
    rw [ha]; ring
  rw [e1, e2, e3]
  have hwx : (w + x) ^ 2 ≤ 2 * (w ^ 2 + x ^ 2) := by nlinarith [sq_nonneg (w - x)]
  have hFa : 0 ≤ F * a := by positivity
  have t1 : 2 * x * (F * (d * a)) * x ≤ 2 * F * a * x ^ 2 := by
    have : 2 * F * a * x ^ 2 * d ≤ 2 * F * a * x ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hd1 (by positivity)
    nlinarith
  have t2 : 2 * x * (F * (d * a)) * w ≤ F * a * (x ^ 2 + d ^ 2 * w ^ 2) := by
    have h := sq_nonneg (x - d * w)
    have : F * a * (2 * x * (d * w)) ≤ F * a * (x ^ 2 + d ^ 2 * w ^ 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hFa
    nlinarith
  have t3 : (F * (d * a)) ^ 2 * (w + x) ^ 2 ≤ 2 * F ^ 2 * a * (d ^ 2 * w ^ 2 + x ^ 2) := by
    have hd2 : d ^ 2 ≤ 1 := by nlinarith
    have ha2 : a ^ 2 ≤ a := by nlinarith
    have h1 : (F * (d * a)) ^ 2 * (w + x) ^ 2 ≤ F ^ 2 * d ^ 2 * a ^ 2 * (2 * (w ^ 2 + x ^ 2)) := by
      have : (F * (d * a)) ^ 2 = F ^ 2 * d ^ 2 * a ^ 2 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hwx (by positivity)
    have h2 : F ^ 2 * d ^ 2 * a ^ 2 * (2 * (w ^ 2 + x ^ 2)) ≤
        F ^ 2 * d ^ 2 * a * (2 * (w ^ 2 + x ^ 2)) := by
      have := mul_le_mul_of_nonneg_left ha2 (by positivity : (0 : ℝ) ≤ F ^ 2 * d ^ 2)
      have h0 : (0 : ℝ) ≤ 2 * (w ^ 2 + x ^ 2) := by positivity
      nlinarith
    have h3 : F ^ 2 * d ^ 2 * a * (2 * x ^ 2) ≤ F ^ 2 * 1 * a * (2 * x ^ 2) := by
      have h0 : (0 : ℝ) ≤ F ^ 2 * a * (2 * x ^ 2) := by positivity
      nlinarith
    nlinarith
  have t4 : K * (F ^ 2 * ((σ * a) * (w + x) ^ 2)) ≤ 2 * K * F ^ 2 * a * (σ * w ^ 2 + x ^ 2) := by
    have h1 : K * (F ^ 2 * ((σ * a) * (w + x) ^ 2)) ≤
        K * F ^ 2 * σ * a * (2 * (w ^ 2 + x ^ 2)) := by
      have : K * (F ^ 2 * ((σ * a) * (w + x) ^ 2)) = K * F ^ 2 * σ * a * (w + x) ^ 2 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hwx (by positivity)
    have h2 : K * F ^ 2 * σ * a * (2 * x ^ 2) ≤ K * F ^ 2 * 1 * a * (2 * x ^ 2) := by
      have h0 : (0 : ℝ) ≤ K * F ^ 2 * a * (2 * x ^ 2) := by positivity
      nlinarith
    nlinarith
  have hlam : 0 ≤ w ^ 2 * d ^ 2 := by positivity
  have hlam2 : 0 ≤ w ^ 2 * σ := by positivity
  have c1 : (F * a + 2 * F ^ 2 * a) * (w ^ 2 * d ^ 2) ≤
      (3 * F * a + 2 * F ^ 2 * a + 2 * K * F ^ 2 * a) * (w ^ 2 * d ^ 2) := by
    apply mul_le_mul_of_nonneg_right _ hlam
    have : 0 ≤ 2 * F * a + 2 * K * F ^ 2 * a := by positivity
    linarith
  have c2 : (2 * K * F ^ 2 * a) * (w ^ 2 * σ) ≤
      (3 * F * a + 2 * F ^ 2 * a + 2 * K * F ^ 2 * a) * (w ^ 2 * σ) := by
    apply mul_le_mul_of_nonneg_right _ hlam2
    have : 0 ≤ 3 * F * a + 2 * F ^ 2 * a := by positivity
    linarith
  linear_combination t1 + t2 + t3 + t4 + c1 + c2

private theorem prefix_hs_smul {m : Type*} [Fintype m] (c : ℂ) (M : Matrix m m ℂ) :
    prefixHS (c • M) = ‖c‖ ^ 2 * prefixHS M := by
  unfold prefixHS
  simp [Matrix.smul_apply, mul_pow, Finset.mul_sum]

private theorem prefix_hs_neg {m : Type*} [Fintype m] (M : Matrix m m ℂ) :
    prefixHS (-M) = prefixHS M := by
  unfold prefixHS; simp

private theorem prefix_hs_zero {m : Type*} [Fintype m] : prefixHS (0 : Matrix m m ℂ) = 0 := by
  simp [prefixHS]

private theorem prefix_hs_one_add {W : ℕ} (X : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    prefixHS (1 + X) ≤ (Real.sqrt (2 * W) + ‖prefixFlat X‖) ^ 2 := by
  rw [← prefix_flat_sq, prefix_flat_add]
  have h1 : ‖prefixFlat (1 : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)‖ = Real.sqrt (2 * W) := by
    rw [prefix_flat_norm, prefix_hs_one]
  have h2 := norm_add_le (prefixFlat (1 : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)) (prefixFlat X)
  rw [h1] at h2
  exact pow_le_pow_left₀ (norm_nonneg _) h2 2

private theorem prefix_hs_drift {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) {W : ℕ} {E : ℝ}
    (hE : |E| ≤ 2 - κ) (z : ℂ) (i : ℕ) (X : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    prefixHS (prefixDrift E z i X) ≤ prefixF κ ^ 2 * ‖z - E‖ ^ 2 * prefixHS (1 + X) := by
  unfold prefixDrift
  rw [prefix_lift_pow, prefix_blockT_eq, prefix_lift_pow]
  simp only [Matrix.mul_assoc]
  have hF := prefix_F_pos hκ
  calc _ ≤ prefixFrob (prefixTi2 E ^ (i + 1)) * prefixHS (Matrix.fromBlocks
        (((z - E) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)) 0 0 0 *
          (prefixLift W (transferT E ^ i) * (1 + X))) := prefix_hs_lift_mul _ _
    _ ≤ prefixF κ * (‖z - E‖ ^ 2 * (prefixF κ * prefixHS (1 + X))) := by
        gcongr
        · exact prefix_hs_nonneg _
        · exact prefix_frob_Ti hκ hκ2 hE _
        · refine (prefix_hs_iota_smul_one _ _).trans ?_
          gcongr
          exact (prefix_hs_lift_mul _ _).trans (mul_le_mul_of_nonneg_right
            (prefix_frob_T hκ hκ2 hE _) (prefix_hs_nonneg _))
    _ = _ := by ring

private theorem prefix_hs_Dx {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) {W L : ℕ} {E s : ℝ}
    (hE : |E| ≤ 2 - κ) (hs : 0 ≤ s) (r : Fin L) (i : ℕ)
    (X : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    ∑ x, prefixHS (prefixDx E s r i X x) ≤ prefixF κ ^ 2 * s * prefixHS (1 + X) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single r
    (fun a _ ha => by simp [prefixDx, ha, prefix_hs_zero]) (by simp)]
  simp only [prefixDx, ↓reduceIte, prefix_hs_neg]
  set c : ℝ := Real.sqrt s / Real.sqrt W with hc
  set Y := prefixLift W (transferT E ^ i) * (1 + X) with hY
  have hF := prefix_F_pos hκ
  have hterm : ∀ k : Fin W × Fin W, prefixHS (prefixLift W (prefixTi2 E) ^ (i + 1) *
      Matrix.fromBlocks ((c : ℂ) • hermBasis W k) 0 0 0 * blockT (E : ℂ) 0 ^ i * (1 + X)) ≤
      prefixF κ * (c ^ 2 * prefixHS (Matrix.fromBlocks (hermBasis W k) 0 0 0 * Y)) := by
    intro k
    rw [prefix_lift_pow, prefix_blockT_eq, prefix_lift_pow]
    simp only [Matrix.mul_assoc]
    refine (prefix_hs_lift_mul _ _).trans ?_
    rw [prefix_fromBlocks_smul, Matrix.smul_mul, prefix_hs_smul, Complex.norm_real,
      Real.norm_eq_abs, sq_abs, ← hY]
    exact mul_le_mul_of_nonneg_right (prefix_frob_Ti hκ hκ2 hE _)
      (mul_nonneg (sq_nonneg _) (prefix_hs_nonneg _))
  have hcW : c ^ 2 * W ≤ s := by
    rcases Nat.eq_zero_or_pos W with h | h
    · subst h; simp [hc]; exact hs
    · have hW : (0 : ℝ) < W := by exact_mod_cast h
      rw [hc, div_pow, Real.sq_sqrt hs, Real.sq_sqrt hW.le, div_mul_cancel₀ _ hW.ne']
  have hYb : prefixHS Y ≤ prefixF κ * prefixHS (1 + X) :=
    (prefix_hs_lift_mul _ _).trans (mul_le_mul_of_nonneg_right (prefix_frob_T hκ hκ2 hE _)
      (prefix_hs_nonneg _))
  calc _ ≤ ∑ k : Fin W × Fin W,
        prefixF κ * (c ^ 2 * prefixHS (Matrix.fromBlocks (hermBasis W k) 0 0 0 * Y)) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = prefixF κ * c ^ 2 *
        ∑ k : Fin W × Fin W, prefixHS (Matrix.fromBlocks (hermBasis W k) 0 0 0 * Y) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
    _ ≤ prefixF κ * c ^ 2 * (W * prefixHS Y) := by
        gcongr; exact prefix_herm_complete Y
    _ ≤ prefixF κ * c ^ 2 * (W * (prefixF κ * prefixHS (1 + X))) := by gcongr
    _ = prefixF κ ^ 2 * (c ^ 2 * W) * prefixHS (1 + X) := by ring
    _ ≤ prefixF κ ^ 2 * s * prefixHS (1 + X) := by
        gcongr
        exact prefix_hs_nonneg _

/-- One step on the potential `‖X‖² + λ` with `λ = 2W((n|z - E|)² + ns)`. -/
private theorem prefix_det_bound {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (q : ℕ) {W L : ℕ} {E s : ℝ}
    {z : ℂ} (r : Fin L) (i n : ℕ) (hE : |E| ≤ 2 - κ) (hs : 0 ≤ s) (hn : 1 ≤ n)
    (hns : (n : ℝ) * s ≤ 1) (hnz : (n : ℝ) * ‖z - E‖ ≤ 1)
    (X : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    ‖prefixFlat (X + prefixDrift E z i X)‖ ^ 2 + 2 * W * (((n : ℝ) * ‖z - E‖) ^ 2 + n * s) +
        prefixK q * ∑ x, ‖prefixFlat (prefixDx E s r i X x)‖ ^ 2 ≤
      (prefixHS X + 2 * W * (((n : ℝ) * ‖z - E‖) ^ 2 + n * s)) * (1 + prefixA κ q / n) := by
  set F := prefixF κ with hFdef
  set x := ‖prefixFlat X‖ with hxdef
  set w := Real.sqrt (2 * W) with hwdef
  set δ := ‖z - (E : ℂ)‖ with hδ
  have hF := prefix_F_pos hκ
  have hK := prefix_K_nonneg q
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hx0 : 0 ≤ x := norm_nonneg _
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hw2 : w ^ 2 = 2 * W := Real.sq_sqrt (by positivity)
  have hx2 : x ^ 2 = prefixHS X := prefix_flat_sq X
  have h1 : prefixHS (1 + X) ≤ (w + x) ^ 2 := prefix_hs_one_add X
  have hdrift : ‖prefixFlat (prefixDrift E z i X)‖ ≤ F * δ * (w + x) := by
    rw [prefix_flat_norm]
    have h2 := prefix_hs_drift hκ hκ2 hE z i X
    have h3 : prefixHS (prefixDrift E z i X) ≤ (F * δ * (w + x)) ^ 2 := by
      calc _ ≤ F ^ 2 * δ ^ 2 * prefixHS (1 + X) := h2
        _ ≤ F ^ 2 * δ ^ 2 * (w + x) ^ 2 := by gcongr
        _ = _ := by ring
    calc Real.sqrt (prefixHS (prefixDrift E z i X)) ≤ Real.sqrt ((F * δ * (w + x)) ^ 2) :=
          Real.sqrt_le_sqrt h3
      _ = F * δ * (w + x) := Real.sqrt_sq (by positivity)
  have hZ : ‖prefixFlat (X + prefixDrift E z i X)‖ ≤ x + F * δ * (w + x) := by
    rw [prefix_flat_add]
    exact (norm_add_le _ _).trans (by linarith)
  have hZ2 : ‖prefixFlat (X + prefixDrift E z i X)‖ ^ 2 ≤ (x + F * δ * (w + x)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hZ 2
  have hD : ∑ x, ‖prefixFlat (prefixDx E s r i X x)‖ ^ 2 ≤ F ^ 2 * s * (w + x) ^ 2 := by
    simp_rw [prefix_flat_sq]
    refine (prefix_hs_Dx hκ hκ2 hE hs r i X).trans ?_
    gcongr
  have hKD : prefixK q * ∑ x, ‖prefixFlat (prefixDx E s r i X x)‖ ^ 2 ≤
      prefixK q * (F ^ 2 * ((((n : ℝ) * s) / n) * (w + x) ^ 2)) := by
    have e : ((n : ℝ) * s) / n = s := by field_simp
    rw [e]
    have : F ^ 2 * s * (w + x) ^ 2 = F ^ 2 * (s * (w + x) ^ 2) := by ring
    rw [← this]
    exact mul_le_mul_of_nonneg_left hD hK
  have hR := prefix_real_bound x w F (prefixK q) ((n : ℝ) * δ) ((n : ℝ) * s) n hF.le hK
    (by positivity) hnz (by positivity) hns hn1
  have e1 : F * (((n : ℝ) * δ) / n) * (w + x) = F * δ * (w + x) := by field_simp
  rw [e1] at hR
  have e2 : 2 * (W : ℝ) * (((n : ℝ) * δ) ^ 2 + n * s) = w ^ 2 * (((n : ℝ) * δ) ^ 2 + n * s) := by
    rw [hw2]
  rw [e2, ← hx2]
  have e3 : prefixA κ q = 3 * F + 2 * F ^ 2 + 2 * prefixK q * F ^ 2 := rfl
  rw [e3]
  linarith

/-- One step of the moment recursion: integrating out the block `b + i`,
`E (‖X_{i+1}‖² + λ)^q ≤ (1 + A/n)^q E (‖X_i‖² + λ)^q`. -/
private theorem prefix_step {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (q : ℕ) {W L : ℕ}
    (G : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ → Prop) {E s : ℝ} {z : ℂ} (b : Fin L)
    (n i : ℕ) (hE : |E| ≤ 2 - κ) (hs : 0 ≤ s) (hn : 1 ≤ n) (hns : (n : ℝ) * s ≤ 1)
    (hnz : (n : ℝ) * ‖z - E‖ ≤ 1) (hiL : i + 1 ≤ L) :
    ∫⁻ ω, ENNReal.ofReal ((prefixHS (prefixProc G E s z b ω (i + 1)) +
        2 * W * (((n : ℝ) * ‖z - E‖) ^ 2 + n * s)) ^ q) ∂(μ W L) ≤
      ENNReal.ofReal ((1 + prefixA κ q / n) ^ q) *
        ∫⁻ ω, ENNReal.ofReal ((prefixHS (prefixProc G E s z b ω i) +
          2 * W * (((n : ℝ) * ‖z - E‖) ^ 2 + n * s)) ^ q) ∂(μ W L) := by
  set lam : ℝ := 2 * W * (((n : ℝ) * ‖z - E‖) ^ 2 + n * s) with hlamdef
  have hlam : 0 ≤ lam := by positivity
  set r := (finRotate L ^ i) b with hr
  set ν := Measure.pi fun _ : Fin L × Fin W × Fin W => gaussianReal (0 : ℝ) 1 with hν
  have hμ : μ W L = ν := rfl
  have hmp := prefix_mp_piecewise (ι := Fin L × Fin W × Fin W) (fun x => x.1 = r)
  set pw := fun zz : Ω W L × Ω W L => fun x : Fin L × Fin W × Fin W =>
    if x.1 = r then zz.2 x else zz.1 x with hpw
  set Fω := fun ω : Ω W L =>
    ENNReal.ofReal ((prefixHS (prefixProc G E s z b ω (i + 1)) + lam) ^ q) with hFω
  set A := prefixA κ q
  have hA := prefix_A_nonneg hκ q
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hgrow : (1 : ℝ) ≤ 1 + A / n := by
    have : 0 ≤ A / n := by positivity
    linarith
  rw [hμ]
  have step1 : ∫⁻ ω, Fω ω ∂ν ≤ ∫⁻ ω, ∫⁻ t, Fω (pw (ω, t)) ∂ν ∂ν := by
    calc ∫⁻ ω, Fω ω ∂ν = ∫⁻ ω, Fω ω ∂((ν.prod ν).map pw) := by rw [hmp.map_eq]
      _ ≤ ∫⁻ zz, Fω (pw zz) ∂(ν.prod ν) := lintegral_map_le _ hmp.measurable.aemeasurable
      _ ≤ _ := lintegral_prod_le _
  have hloc : ∀ ω t, prefixProc G E s z b (pw (ω, t)) i = prefixProc G E s z b ω i := by
    intro ω t
    refine prefix_proc_local G E s z b (pw (ω, t)) ω i fun i' hi' k => ?_
    have hne : (finRotate L ^ i') b ≠ r := prefix_rot_ne b hi' (by omega)
    simp [hpw, hne]
  have hsum : ∀ ω t (X : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ),
      ∑ x, ((pw (ω, t)) x : ℂ) • prefixDx E s r i X x = ∑ x, (t x : ℂ) • prefixDx E s r i X x := by
    intro ω t X
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x.1 = r
    · simp [hpw, hx]
    · simp [prefixDx, hx]
  have hstep : ∀ ω t, prefixProc G E s z b (pw (ω, t)) (i + 1) =
      if G (prefixProc G E s z b ω i) then
        prefixProc G E s z b ω i + (prefixDrift E z i (prefixProc G E s z b ω i) +
          ∑ x, (t x : ℂ) • prefixDx E s r i (prefixProc G E s z b ω i) x)
      else prefixProc G E s z b ω i := by
    intro ω t
    simp only [prefixProc]
    rw [hloc, prefix_inc_eq, ← hr, hsum]
  have inner : ∀ ω, ∫⁻ t, Fω (pw (ω, t)) ∂ν ≤
      ENNReal.ofReal ((1 + A / n) ^ q) *
        ENNReal.ofReal ((prefixHS (prefixProc G E s z b ω i) + lam) ^ q) := by
    intro ω
    have hst := fun t => hstep ω t
    generalize prefixProc G E s z b ω i = X at hst ⊢
    have hX0 : 0 ≤ prefixHS X + lam := add_nonneg (prefix_hs_nonneg _) hlam
    rw [← ENNReal.ofReal_mul (pow_nonneg (by linarith) _), ← mul_pow]
    by_cases hG : G X
    · have e : ∀ t, Fω (pw (ω, t)) = ENNReal.ofReal ((‖prefixFlat (X + prefixDrift E z i X) +
          ∑ x, t x • prefixFlat (prefixDx E s r i X x)‖ ^ 2 + lam) ^ q) := by
        intro t
        simp only [hFω, hst, hG, ↓reduceIte]
        rw [← prefix_flat_sq, ← add_assoc, prefix_flat_add _ (∑ x, _), prefix_flat_sum]
        simp_rw [Complex.coe_smul, prefix_flat_smul]
      simp_rw [e]
      have hg := prefix_gauss_vec q (fun x => prefixFlat (prefixDx E s r i X x)) lam hlam
        Finset.univ q le_rfl (prefixFlat (X + prefixDrift E z i X))
      refine hg.trans (ENNReal.ofReal_le_ofReal ?_)
      apply pow_le_pow_left₀ (add_nonneg (add_nonneg (sq_nonneg _) hlam)
        (mul_nonneg (prefix_K_nonneg q) (Finset.sum_nonneg fun _ _ => sq_nonneg _)))
      have hdb := prefix_det_bound hκ hκ2 q r i n hE hs hn hns hnz X
      rw [mul_comm (1 + A / n)]
      linarith
    · have e : ∀ t, Fω (pw (ω, t)) = ENNReal.ofReal ((prefixHS X + lam) ^ q) := by
        intro t
        simp only [hFω, hst, hG, ↓reduceIte]
      simp_rw [e]
      rw [lintegral_const, measure_univ, mul_one]
      refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hX0 ?_ q)
      nlinarith
  calc ∫⁻ ω, Fω ω ∂ν ≤ ∫⁻ ω, ∫⁻ t, Fω (pw (ω, t)) ∂ν ∂ν := step1
    _ ≤ ∫⁻ ω, ENNReal.ofReal ((1 + A / n) ^ q) *
        ENNReal.ofReal ((prefixHS (prefixProc G E s z b ω i) + lam) ^ q) ∂ν :=
        lintegral_mono inner
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The moment recursion over `m ≤ L` steps. -/
private theorem prefix_iter {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (q : ℕ) {W L : ℕ}
    (G : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ → Prop) {E s : ℝ} {z : ℂ} (b : Fin L)
    (n : ℕ) (hE : |E| ≤ 2 - κ) (hs : 0 ≤ s) (hn : 1 ≤ n) (hns : (n : ℝ) * s ≤ 1)
    (hnz : (n : ℝ) * ‖z - E‖ ≤ 1) :
    ∀ m, m ≤ L → ∫⁻ ω, ENNReal.ofReal ((prefixHS (prefixProc G E s z b ω m) +
        2 * W * (((n : ℝ) * ‖z - E‖) ^ 2 + n * s)) ^ q) ∂(μ W L) ≤
      ENNReal.ofReal ((1 + prefixA κ q / n) ^ (q * m)) *
        ENNReal.ofReal ((2 * W * (((n : ℝ) * ‖z - E‖) ^ 2 + n * s)) ^ q) := by
  intro m
  induction m with
  | zero =>
    intro _
    simp [prefixProc, prefix_hs_zero]
  | succ m ih =>
    intro hm
    have hA := prefix_A_nonneg hκ q
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    refine (prefix_step hκ hκ2 q G b n m hE hs hn hns hnz hm).trans ?_
    calc _ ≤ ENNReal.ofReal ((1 + prefixA κ q / n) ^ q) *
          (ENNReal.ofReal ((1 + prefixA κ q / n) ^ (q * m)) *
            ENNReal.ofReal ((2 * W * (((n : ℝ) * ‖z - E‖) ^ 2 + n * s)) ^ q)) := by
          gcongr; exact ih (by omega)
      _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← pow_add]
          congr 3
          ring

/-- The potential bound: `E (‖X_m‖² + λ)^q ≤ e^{Aq} λ^q` for `m ≤ n` and `m ≤ L`. -/
private theorem prefix_potential {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (q : ℕ) {W L : ℕ}
    (G : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ → Prop) {E s : ℝ} {z : ℂ} (b : Fin L)
    (n m : ℕ) (hE : |E| ≤ 2 - κ) (hs : 0 ≤ s) (hn : 1 ≤ n) (hns : (n : ℝ) * s ≤ 1)
    (hnz : (n : ℝ) * ‖z - E‖ ≤ 1) (hmn : m ≤ n) (hmL : m ≤ L) :
    ∫⁻ ω, ENNReal.ofReal ((prefixHS (prefixProc G E s z b ω m) +
        2 * W * (((n : ℝ) * ‖z - E‖) ^ 2 + n * s)) ^ q) ∂(μ W L) ≤
      ENNReal.ofReal (Real.exp (prefixA κ q * q) *
        (2 * W * (((n : ℝ) * ‖z - E‖) ^ 2 + n * s)) ^ q) := by
  refine (prefix_iter hκ hκ2 q G b n hE hs hn hns hnz m hmL).trans ?_
  have hA := prefix_A_nonneg hκ q
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  gcongr
  calc (1 + prefixA κ q / n) ^ (q * m) ≤ Real.exp (prefixA κ q / n) ^ (q * m) := by
        gcongr
        linarith [Real.add_one_le_exp (prefixA κ q / n)]
    _ = Real.exp (prefixA κ q / n * (q * m : ℕ)) := by
        rw [← Real.exp_nat_mul, mul_comm]
    _ ≤ Real.exp (prefixA κ q * q) := by
        apply Real.exp_le_exp.mpr
        have hm : ((q * m : ℕ) : ℝ) ≤ q * n := by
          push_cast; gcongr
        calc prefixA κ q / n * ((q * m : ℕ) : ℝ) ≤ prefixA κ q / n * (q * n) := by gcongr
          _ = prefixA κ q * q := by field_simp

/-! ### Products, stopping and the cell event -/

private theorem prefix_meas_cellProd {W L : ℕ} (z c : ℂ) (b : Fin L) :
    ∀ j p q, Measurable fun ω : Ω W L =>
      cellProd z (fun r => c • gueBlock W L ω r) b j p q := by
  intro j
  induction j with
  | zero => intro p q; exact measurable_const
  | succ j ih => exact prefix_meas_mul (prefix_meas_blockT z c _) ih

/-- `T_{b+k+j-1} ⋯ T_b = (T_{b+k+j-1} ⋯ T_{b+k}) (T_{b+k-1} ⋯ T_b)`. -/
private theorem prefix_cellProd_add {W L : ℕ} (z : ℂ) (V : Fin L → Matrix (Fin W) (Fin W) ℂ)
    (a : Fin L) (k j : ℕ) :
    cellProd z V a (k + j) = cellProd z V ((finRotate L ^ k) a) j * cellProd z V a k := by
  induction j with
  | zero => simp [cellProd]
  | succ j ih =>
    have hrot : (finRotate L ^ j) ((finRotate L ^ k) a) = (finRotate L ^ (k + j)) a := by
      rw [← Equiv.Perm.mul_apply, ← pow_add, add_comm]
    rw [← add_assoc]
    change blockT z (V ((finRotate L ^ (k + j)) a)) * cellProd z V a (k + j) =
      blockT z (V ((finRotate L ^ j) ((finRotate L ^ k) a))) *
        cellProd z V ((finRotate L ^ k) a) j * cellProd z V a k
    rw [ih, hrot, Matrix.mul_assoc]

/-- `P_i = T(E)^i (I + X_i)` for the process with the trivial predicate. -/
private theorem prefix_cellProd_eq {W L : ℕ} (E s : ℝ) (z : ℂ) (b : Fin L) (ω : Ω W L) (i : ℕ) :
    cellProd z (fun r => ((Real.sqrt s : ℝ) : ℂ) • gueBlock W L ω r) b i =
      blockT (E : ℂ) 0 ^ i * (1 + prefixProc (fun _ => True) E s z b ω i) := by
  rw [prefix_proc_plain, add_sub_cancel, ← Matrix.mul_assoc, prefix_pow_Ti_pow, Matrix.one_mul]

/-- The process stopped at the threshold `θ` agrees with the process with the trivial predicate up
to the first exit. -/
private theorem prefix_stop_eq {W L : ℕ} (θ E s : ℝ) (z : ℂ) (b : Fin L) (ω : Ω W L) :
    ∀ i, (∀ i' < i, prefixHS (prefixProc (fun _ => True) E s z b ω i') ≤ θ) →
      prefixProc (fun X => prefixHS X ≤ θ) E s z b ω i =
        prefixProc (fun _ => True) E s z b ω i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro h
    have hi := ih (fun i' hi' => h i' (by omega))
    have hle := h i (by omega)
    simp only [prefixProc, hi, hle, ↓reduceIte]

/-- After the first exit the stopped process is constant. -/
private theorem prefix_stop_frozen {W L : ℕ} (θ E s : ℝ) (z : ℂ) (b : Fin L) (ω : Ω W L) (i : ℕ)
    (h : θ < prefixHS (prefixProc (fun X => prefixHS X ≤ θ) E s z b ω i)) :
    ∀ d, prefixProc (fun X => prefixHS X ≤ θ) E s z b ω (i + d) =
      prefixProc (fun X => prefixHS X ≤ θ) E s z b ω i := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← add_assoc]
    have hn : ¬ prefixHS (prefixProc (fun X => prefixHS X ≤ θ) E s z b ω (i + d)) ≤ θ := by
      rw [ih]; exact not_le.mpr h
    simp only [prefixProc, hn, ↓reduceIte]
    exact ih

/-- If the stopped process ends below `θ`, every prefix up to that time stays below `θ`. -/
private theorem prefix_stop_all {W L : ℕ} (θ E s : ℝ) (z : ℂ) (b : Fin L) (ω : Ω W L) (m : ℕ)
    (h : prefixHS (prefixProc (fun X => prefixHS X ≤ θ) E s z b ω m) ≤ θ) :
    ∀ i ≤ m, prefixHS (prefixProc (fun _ => True) E s z b ω i) ≤ θ := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro him
    have heq := prefix_stop_eq θ E s z b ω i (fun i' hi' => ih i' hi' (by omega))
    by_contra hc
    rw [not_le, ← heq] at hc
    have hfr := prefix_stop_frozen θ E s z b ω i hc (m - i)
    rw [Nat.add_sub_cancel' him] at hfr
    rw [hfr] at h
    exact absurd h (not_le.mpr hc)

private theorem prefix_flat_lift_mul {W : ℕ} {M : Matrix (Fin 2) (Fin 2) ℝ} {F : ℝ}
    (hM : prefixFrob M ≤ F) (Z : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    ‖prefixFlat (prefixLift W M * Z)‖ ≤ Real.sqrt F * ‖prefixFlat Z‖ := by
  rw [prefix_flat_norm, prefix_flat_norm, ← Real.sqrt_mul' _ (prefix_hs_nonneg _)]
  exact Real.sqrt_le_sqrt ((prefix_hs_lift_mul M Z).trans
    (mul_le_mul_of_nonneg_right hM (prefix_hs_nonneg _)))

private theorem prefix_flat_mul_lift {W : ℕ} {M : Matrix (Fin 2) (Fin 2) ℝ} {F : ℝ}
    (hM : prefixFrob M ≤ F) (Z : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    ‖prefixFlat (Z * prefixLift W M)‖ ≤ Real.sqrt F * ‖prefixFlat Z‖ := by
  rw [prefix_flat_norm, prefix_flat_norm, ← Real.sqrt_mul' _ (prefix_hs_nonneg _)]
  exact Real.sqrt_le_sqrt ((prefix_hs_mul_lift M Z).trans
    (mul_le_mul_of_nonneg_right hM (prefix_hs_nonneg _)))

private theorem prefix_flat_mul {m : Type*} [Fintype m] (A B : Matrix m m ℂ) :
    ‖prefixFlat (A * B)‖ ≤ ‖prefixFlat A‖ * ‖prefixFlat B‖ := by
  rw [prefix_flat_norm, prefix_flat_norm, prefix_flat_norm,
    ← Real.sqrt_mul (prefix_hs_nonneg _)]
  exact Real.sqrt_le_sqrt (prefix_hs_mul_le A B)

/-- An internal product of a cell is close to the free one when the two rescaled prefixes at its
ends are: `‖Y - T^j‖_HS ≤ 4 F δ` if `Y P_k = P_{k+j}`, `P_i = T^i (I + X_i)` and
`‖X_k‖_HS, ‖X_{k+j}‖_HS ≤ δ ≤ 1/2`. -/
private theorem prefix_internal {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) {W : ℕ} {E δ : ℝ}
    (hE : |E| ≤ 2 - κ) (hδ : δ ≤ 1 / 2) (k j : ℕ)
    (Y Xk Xkj : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)
    (hY : Y * (blockT (E : ℂ) 0 ^ k * (1 + Xk)) = blockT (E : ℂ) 0 ^ (k + j) * (1 + Xkj))
    (hk : ‖prefixFlat Xk‖ ≤ δ) (hkj : ‖prefixFlat Xkj‖ ≤ δ) :
    ‖prefixFlat (Y - blockT (E : ℂ) 0 ^ j)‖ ≤ 4 * prefixF κ * δ := by
  set T := blockT (E : ℂ) (0 : Matrix (Fin W) (Fin W) ℂ) with hT
  set U := (Y - T ^ j) * T ^ k with hU
  have hF := prefix_F_pos hκ
  have hsF : Real.sqrt (prefixF κ) * Real.sqrt (prefixF κ) = prefixF κ :=
    Real.mul_self_sqrt hF.le
  have hU1 : U = T ^ (k + j) * (Xkj - Xk) - U * Xk := by
    have h1 : U * (1 + Xk) = T ^ (k + j) * (Xkj - Xk) := by
      rw [hU, Matrix.mul_assoc, Matrix.sub_mul, hY, ← Matrix.mul_assoc (T ^ j),
        ← pow_add, add_comm j k, ← Matrix.mul_sub]
      congr 1; abel
    rw [← h1, Matrix.mul_add, Matrix.mul_one]; abel
  have hTk : ∀ m, ‖prefixFlat (T ^ m * Xkj - T ^ m * Xk)‖ ≤ Real.sqrt (prefixF κ) * (2 * δ) := by
    intro m
    rw [← Matrix.mul_sub, hT, prefix_blockT_eq, prefix_lift_pow]
    refine (prefix_flat_lift_mul (F := prefixF κ) (prefix_frob_T hκ hκ2 hE m) _).trans ?_
    gcongr
    rw [prefix_flat_sub]
    exact (norm_sub_le _ _).trans (by linarith)
  have hUb : ‖prefixFlat U‖ ≤ 4 * Real.sqrt (prefixF κ) * δ := by
    have h2 : ‖prefixFlat U‖ ≤ Real.sqrt (prefixF κ) * (2 * δ) + ‖prefixFlat U‖ * δ := by
      conv_lhs => rw [hU1]
      rw [prefix_flat_sub, Matrix.mul_sub]
      refine (norm_sub_le _ _).trans (add_le_add (hTk _) ?_)
      exact (prefix_flat_mul U Xk).trans (mul_le_mul_of_nonneg_left hk (norm_nonneg _))
    have hU0 := norm_nonneg (prefixFlat U)
    have hs0 := Real.sqrt_nonneg (prefixF κ)
    nlinarith
  have hY2 : Y - T ^ j = U * prefixLift W (prefixTi2 E) ^ k := by
    rw [hU, Matrix.mul_assoc, prefix_pow_Ti_pow, Matrix.mul_one]
  rw [hY2, prefix_lift_pow]
  refine (prefix_flat_mul_lift (F := prefixF κ) (prefix_frob_Ti hκ hκ2 hE k) U).trans ?_
  calc Real.sqrt (prefixF κ) * ‖prefixFlat U‖ ≤
      Real.sqrt (prefixF κ) * (4 * Real.sqrt (prefixF κ) * δ) := by gcongr
    _ = 4 * prefixF κ * δ := by linear_combination (4 * δ) * hsF

private theorem prefix_add_pow_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (q : ℕ) :
    (a + b) ^ q ≤ 2 ^ q * (a ^ q + b ^ q) := by
  have h1 : a + b ≤ 2 * max a b := by
    have := le_max_left a b; have := le_max_right a b; linarith
  have h2 : max a b ^ q ≤ a ^ q + b ^ q := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; have := pow_nonneg ha q; linarith
    · rw [max_eq_left h]; have := pow_nonneg hb q; linarith
  calc (a + b) ^ q ≤ (2 * max a b) ^ q := pow_le_pow_left₀ (by positivity) h1 q
    _ = 2 ^ q * max a b ^ q := mul_pow _ _ _
    _ ≤ _ := by gcongr

/-! ## Statements -/

/-- (7.14) [uvc:eq:prefix-moments] at a fixed time and a spectral parameter `z` near the real
energy `E`: for `j ≤ n ≤ L`, `ns ≤ c` and `n|z - E| ≤ c`, the Hilbert–Schmidt moments of
`T_{b+j-1}(z) ⋯ T_b(z) - T(E)^j` for the blocks `√s V_r` are at most
`C W^q ((ns)^q + (n|z - E|)^{2q})`. -/
theorem prefix_moments (κ : ℝ) (q : ℕ) (hκ : 0 < κ) (hκ2 : κ < 2) (hq : 1 ≤ q) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (W L : ℕ) (E s : ℝ) (z : ℂ) (b : Fin L) (n j : ℕ),
      |E| ≤ 2 - κ → 0 ≤ s → n ≤ L → j ≤ n → (n : ℝ) * s ≤ c → (n : ℝ) * ‖z - E‖ ≤ c →
      Integrable (fun ω => (∑ x, ∑ y, ‖(cellProd z (fun r => ((Real.sqrt s : ℝ) : ℂ) •
          gueBlock W L ω r) b j - blockT (E : ℂ) 0 ^ j :
            Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) x y‖ ^ 2) ^ q) (μ W L) ∧
      ∫ ω, (∑ x, ∑ y, ‖(cellProd z (fun r => ((Real.sqrt s : ℝ) : ℂ) • gueBlock W L ω r) b j -
          blockT (E : ℂ) 0 ^ j : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) x y‖ ^ 2) ^ q
          ∂(μ W L) ≤
        C * (W : ℝ) ^ q * (((n : ℝ) * s) ^ q + ((n : ℝ) * ‖z - E‖) ^ (2 * q)) := by
  have hF := prefix_F_pos hκ
  have hA := prefix_A_nonneg hκ q
  refine ⟨prefixF κ ^ q * Real.exp (prefixA κ q * q) * 4 ^ q, 1, by positivity, one_pos, ?_⟩
  intro W L E s z b n j hE hs hnL hjn hns hnz
  set f : Ω W L → ℝ := fun ω => (∑ x, ∑ y, ‖(cellProd z (fun r => ((Real.sqrt s : ℝ) : ℂ) •
      gueBlock W L ω r) b j - blockT (E : ℂ) 0 ^ j :
        Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) x y‖ ^ 2) ^ q with hf
  have hfeq : ∀ ω, f ω = prefixHS (cellProd z (fun r => ((Real.sqrt s : ℝ) : ℂ) •
      gueBlock W L ω r) b j - blockT (E : ℂ) 0 ^ j) ^ q := fun ω => rfl
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω => by rw [hfeq]; exact pow_nonneg (prefix_hs_nonneg _) _
  have hfm : Measurable f := by
    have : Measurable fun ω : Ω W L => prefixHS (cellProd z (fun r => ((Real.sqrt s : ℝ) : ℂ) •
        gueBlock W L ω r) b j - blockT (E : ℂ) 0 ^ j) :=
      prefix_meas_hs (prefix_meas_sub (prefix_meas_cellProd z _ b j) (prefix_meas_const _))
    exact this.pow_const q
  set R : ℝ := prefixF κ ^ q * Real.exp (prefixA κ q * q) * 4 ^ q * (W : ℝ) ^ q *
    (((n : ℝ) * s) ^ q + ((n : ℝ) * ‖z - E‖) ^ (2 * q)) with hR
  have hR0 : 0 ≤ R := by positivity
  have hlint : ∫⁻ ω, ENNReal.ofReal (f ω) ∂(μ W L) ≤ ENNReal.ofReal R := by
    rcases Nat.eq_zero_or_pos n with hn0 | hn1
    · have hj0 : j = 0 := by omega
      have h0 : ∀ ω, f ω = 0 := fun ω => by
        rw [hfeq, hj0]
        simp [cellProd, prefix_hs_zero, zero_pow (by omega : q ≠ 0)]
      simp only [h0, ENNReal.ofReal_zero, lintegral_zero]
      exact bot_le
    · have hn : 1 ≤ n := hn1
      set lam : ℝ := 2 * W * (((n : ℝ) * ‖z - E‖) ^ 2 + n * s) with hlam
      have hlam0 : 0 ≤ lam := by positivity
      have hpt : ∀ ω, ENNReal.ofReal (f ω) ≤ ENNReal.ofReal (prefixF κ ^ q) *
          ENNReal.ofReal ((prefixHS (prefixProc (fun _ => True) E s z b ω j) + lam) ^ q) := by
        intro ω
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [hfeq, ← mul_pow]
        apply pow_le_pow_left₀ (prefix_hs_nonneg _)
        rw [prefix_cellProd_eq E s z b ω j]
        set X := prefixProc (fun _ => True) E s z b ω j
        have e : blockT (E : ℂ) 0 ^ j * (1 + X) - blockT (E : ℂ) 0 ^ j =
            blockT (E : ℂ) 0 ^ j * X := by
          rw [Matrix.mul_add, Matrix.mul_one]; abel
        rw [e, prefix_blockT_eq, prefix_lift_pow]
        calc _ ≤ prefixFrob (transferT E ^ j) * prefixHS X := prefix_hs_lift_mul _ _
          _ ≤ prefixF κ * prefixHS X :=
              mul_le_mul_of_nonneg_right (prefix_frob_T hκ hκ2 hE j) (prefix_hs_nonneg _)
          _ ≤ prefixF κ * (prefixHS X + lam) := by gcongr; linarith
      have hpot := prefix_potential hκ hκ2 q (W := W)
        (fun _ : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ => True) b n j hE hs hn
        hns hnz hjn (hjn.trans hnL)
      calc ∫⁻ ω, ENNReal.ofReal (f ω) ∂(μ W L)
          ≤ ∫⁻ ω, ENNReal.ofReal (prefixF κ ^ q) *
              ENNReal.ofReal ((prefixHS (prefixProc (fun _ => True) E s z b ω j) + lam) ^ q)
                ∂(μ W L) := lintegral_mono hpt
        _ = ENNReal.ofReal (prefixF κ ^ q) * ∫⁻ ω,
              ENNReal.ofReal ((prefixHS (prefixProc (fun _ => True) E s z b ω j) + lam) ^ q)
                ∂(μ W L) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (prefixF κ ^ q) *
              ENNReal.ofReal (Real.exp (prefixA κ q * q) * lam ^ q) := by gcongr
        _ = ENNReal.ofReal (prefixF κ ^ q * (Real.exp (prefixA κ q * q) * lam ^ q)) :=
              (ENNReal.ofReal_mul (by positivity)).symm
        _ ≤ ENNReal.ofReal R := by
            apply ENNReal.ofReal_le_ofReal
            have h1 : lam ^ q ≤ 4 ^ q * (W : ℝ) ^ q *
                (((n : ℝ) * s) ^ q + ((n : ℝ) * ‖z - E‖) ^ (2 * q)) := by
              have h2 := prefix_add_pow_le (((n : ℝ) * ‖z - E‖) ^ 2) ((n : ℝ) * s)
                (by positivity) (by positivity) q
              rw [← pow_mul] at h2
              calc lam ^ q = 2 ^ q * (W : ℝ) ^ q *
                    (((n : ℝ) * ‖z - E‖) ^ 2 + n * s) ^ q := by
                    rw [hlam, mul_pow, mul_pow]
                _ ≤ 2 ^ q * (W : ℝ) ^ q * (2 ^ q *
                    (((n : ℝ) * ‖z - E‖) ^ (2 * q) + ((n : ℝ) * s) ^ q)) := by gcongr
                _ = _ := by rw [show (4 : ℝ) ^ q = 2 ^ q * 2 ^ q by
                      rw [← mul_pow]; norm_num]; ring
            calc prefixF κ ^ q * (Real.exp (prefixA κ q * q) * lam ^ q)
                ≤ prefixF κ ^ q * (Real.exp (prefixA κ q * q) * (4 ^ q * (W : ℝ) ^ q *
                  (((n : ℝ) * s) ^ q + ((n : ℝ) * ‖z - E‖) ^ (2 * q)))) := by gcongr
              _ = R := by rw [hR]; ring
  refine ⟨⟨hfm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall hf0)).mpr (hlint.trans_lt ENNReal.ofReal_lt_top)⟩, ?_⟩
  change ∫ ω, f ω ∂(μ W L) ≤ R
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0)
    hfm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hR0 hlint

/-- Lemma 7.7 [uvc:lem:cells] at a fixed time: for `g² ≥ W^B`, `L ≤ g² W^C` and block
variance `s ≤ g^{-2}`, the transfer products in every cell of length `n = ⌊g² W^{-B}⌋` are
within `W^{-B/4}` of the free ones, with probability at least `1 - W^{-D}`. -/
theorem cells_prefix (κ B C D : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hB : 2 < B) (hC : 0 < C)
    (hD : 0 < D) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ (g : ℝ) (L : ℕ) (E s : ℝ), (W : ℝ) ^ B ≤ g ^ 2 →
      (L : ℝ) ≤ g ^ 2 * (W : ℝ) ^ C → |E| ≤ 2 - κ → 0 ≤ s → s * g ^ 2 ≤ 1 →
      μ W L {ω | ¬ CellClose (cellLen g W B) E (E : ℂ)
          (fun r => ((Real.sqrt s : ℝ) : ℂ) • gueBlock W L ω r) ((W : ℝ) ^ (-(B / 4)))} ≤
        ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  have hB2 : 0 < B / 2 - 1 := by linarith
  set q : ℕ := ⌈(B + C + D + 2) / (B / 2 - 1)⌉₊ with hqdef
  have hq : B + C + D + 2 ≤ (q : ℝ) * (B / 2 - 1) := by
    have h := Nat.le_ceil ((B + C + D + 2) / (B / 2 - 1))
    rw [div_le_iff₀ hB2] at h
    exact h
  have hF := prefix_F_pos hκ
  have hA := prefix_A_nonneg hκ q
  have hF1 : 1 ≤ prefixF κ := by
    unfold prefixF
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  set C₁ : ℝ := 3 * Real.exp (prefixA κ q * q) * (32 * prefixF κ ^ 2) ^ q with hC₁
  refine ⟨max 1 ⌈C₁⌉₊, ?_⟩
  intro W hW g L E s hg hL hE hs hsg
  have hW1 : 1 ≤ W := le_trans (le_max_left _ _) hW
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hWC : C₁ ≤ W := (Nat.le_ceil C₁).trans (by exact_mod_cast le_trans (le_max_right _ _) hW)
  set n := cellLen g W B with hndef
  have hn1 : 1 ≤ n := le_max_left _ _
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  obtain ⟨-, hnle⟩ := cellLen_bounds g B W hW1 hg
  have hWB0 : 0 ≤ (W : ℝ) ^ (-B) := (Real.rpow_pos_of_pos hW0 _).le
  have hns : (n : ℝ) * s ≤ (W : ℝ) ^ (-B) := by
    calc (n : ℝ) * s ≤ g ^ 2 * (W : ℝ) ^ (-B) * s := mul_le_mul_of_nonneg_right hnle hs
      _ = (s * g ^ 2) * (W : ℝ) ^ (-B) := by ring
      _ ≤ 1 * (W : ℝ) ^ (-B) := mul_le_mul_of_nonneg_right hsg hWB0
      _ = _ := one_mul _
  have hWB1 : (W : ℝ) ^ (-B) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hWr (by linarith)
  have hns1 : (n : ℝ) * s ≤ 1 := hns.trans hWB1
  have hnz : (n : ℝ) * ‖(E : ℂ) - E‖ ≤ 1 := by simp
  set ε := (W : ℝ) ^ (-(B / 4)) with hε
  have hε0 : 0 < ε := Real.rpow_pos_of_pos hW0 _
  have hε1 : ε ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hWr (by linarith)
  set δ := ε / (4 * prefixF κ) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδ, div_le_iff₀ (by positivity)]
    nlinarith
  set θ := δ ^ 2 with hθ
  have hθ0 : 0 < θ := by positivity
  set G : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ → Prop := fun X => prefixHS X ≤ θ with hG
  have hGm : ∀ f : Ω W L → Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ,
      (∀ p q, Measurable fun ω => f ω p q) → MeasurableSet {ω | G (f ω)} :=
    fun f hf => measurableSet_le (prefix_meas_hs hf) measurable_const
  set starts := Finset.univ.filter fun c : Fin L => c.val % n = 0 with hstarts
  set S : Fin L → Set (Ω W L) := fun c =>
    {ω | θ < prefixHS (prefixProc G E s (E : ℂ) c ω (min n (L - c.val)))} with hS
  -- the deterministic inclusion
  have hsub : {ω | ¬ CellClose n E (E : ℂ)
      (fun r => ((Real.sqrt s : ℝ) : ℂ) • gueBlock W L ω r) ε} ⊆ ⋃ c ∈ starts, S c := by
    intro ω hω
    by_contra hc
    apply hω
    simp only [Set.mem_iUnion, not_exists] at hc
    intro b j hbj hbL
    set c := cellStart n b with hcdef
    have hcs : c ∈ starts := by
      simp only [hstarts, Finset.mem_filter, Finset.mem_univ, true_and, hcdef, cellStart]
      exact Nat.mul_mod_left _ _
    have hcS : prefixHS (prefixProc G E s (E : ℂ) c ω (min n (L - c.val))) ≤ θ := by
      have := hc c hcs
      simp only [hS, Set.mem_ofPred_eq, not_lt] at this
      exact this
    have hall := prefix_stop_all θ E s (E : ℂ) c ω _ hcS
    set k := b.val % n with hk
    have hck : c.val + k = b.val := by
      simp only [hcdef, cellStart, hk]; exact Nat.div_add_mod' b.val n
    have hkj : k + j ≤ min n (L - c.val) := le_min hbj (by omega)
    have hrot : (finRotate L ^ k) c = b := by
      apply Fin.ext
      rw [prefix_rotPow_val, hck, Nat.mod_eq_of_lt b.isLt]
    set V := fun r => ((Real.sqrt s : ℝ) : ℂ) • gueBlock W L ω r with hV
    have hsplit := prefix_cellProd_add (E : ℂ) V c k j
    rw [hrot] at hsplit
    have hY : cellProd (E : ℂ) V b j * (blockT (E : ℂ) 0 ^ k *
        (1 + prefixProc (fun _ => True) E s (E : ℂ) c ω k)) =
        blockT (E : ℂ) 0 ^ (k + j) * (1 + prefixProc (fun _ => True) E s (E : ℂ) c ω (k + j)) := by
      rw [← prefix_cellProd_eq, ← prefix_cellProd_eq, hsplit]
    have hnorm : ∀ i ≤ min n (L - c.val),
        ‖prefixFlat (prefixProc (fun _ => True) E s (E : ℂ) c ω i)‖ ≤ δ := by
      intro i hi
      rw [prefix_flat_norm]
      calc Real.sqrt (prefixHS (prefixProc (fun _ => True) E s (E : ℂ) c ω i))
          ≤ Real.sqrt θ := Real.sqrt_le_sqrt (hall i hi)
        _ = δ := Real.sqrt_sq hδ0.le
    have hint := prefix_internal hκ hκ2 hE hδ2 k j _ _ _ hY (hnorm k (by omega)) (hnorm _ hkj)
    unfold prodErr
    calc ‖cellProd (E : ℂ) V b j - blockT (E : ℂ) 0 ^ j‖
        ≤ Real.sqrt (prefixHS (cellProd (E : ℂ) V b j - blockT (E : ℂ) 0 ^ j)) :=
          prefix_op_le_hs _
      _ = ‖prefixFlat (cellProd (E : ℂ) V b j - blockT (E : ℂ) 0 ^ j)‖ :=
          (prefix_flat_norm _).symm
      _ ≤ 4 * prefixF κ * δ := hint
      _ = ε := by rw [hδ]; field_simp
  -- the bound for one cell
  set lam : ℝ := 2 * W * (((n : ℝ) * ‖(E : ℂ) - E‖) ^ 2 + n * s) with hlam
  have hlam0 : 0 ≤ lam := by positivity
  set K₀ : ℝ := Real.exp (prefixA κ q * q) * lam ^ q / θ ^ q with hK₀
  have hcell : ∀ c : Fin L, μ W L (S c) ≤ ENNReal.ofReal K₀ := by
    intro c
    set m := min n (L - c.val)
    have hmeas : Measurable fun ω : Ω W L =>
        ENNReal.ofReal ((prefixHS (prefixProc G E s (E : ℂ) c ω m) + lam) ^ q) :=
      ENNReal.measurable_ofReal.comp
        (((prefix_meas_hs (prefix_meas_proc G hGm E s (E : ℂ) c m)).add_const lam).pow_const q)
    have hθq : (0 : ℝ) < θ ^ q := pow_pos hθ0 q
    have hsubS : S c ⊆ {ω | ENNReal.ofReal (θ ^ q) ≤
        ENNReal.ofReal ((prefixHS (prefixProc G E s (E : ℂ) c ω m) + lam) ^ q)} := by
      intro ω hω
      simp only [hS, Set.mem_ofPred_eq] at hω ⊢
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hθ0.le (by linarith) q)
    have hpot := prefix_potential hκ hκ2 q G c n m hE hs hn1 hns1 hnz (min_le_left _ _)
      ((min_le_right _ _).trans (Nat.sub_le _ _))
    calc μ W L (S c) ≤ μ W L {ω | ENNReal.ofReal (θ ^ q) ≤
          ENNReal.ofReal ((prefixHS (prefixProc G E s (E : ℂ) c ω m) + lam) ^ q)} :=
          measure_mono hsubS
      _ ≤ (∫⁻ ω, ENNReal.ofReal ((prefixHS (prefixProc G E s (E : ℂ) c ω m) + lam) ^ q)
            ∂(μ W L)) / ENNReal.ofReal (θ ^ q) :=
          meas_ge_le_lintegral_div hmeas.aemeasurable (by simpa using hθq) ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Real.exp (prefixA κ q * q) * lam ^ q) / ENNReal.ofReal (θ ^ q) := by
          gcongr
      _ = ENNReal.ofReal K₀ := by rw [hK₀, ENNReal.ofReal_div_of_pos hθq]
  -- the real inequality
  have hcard := (card_cells_le_pow g B C W L hW1 (by linarith) hC.le hg hL).1
  have hK₀0 : 0 ≤ K₀ := by positivity
  have hfinal : (starts.card : ℝ) * K₀ ≤ (W : ℝ) ^ (-D) := by
    have hlamθ : lam / θ ≤ 32 * prefixF κ ^ 2 * (W : ℝ) ^ (1 - B / 2) := by
      have hlam' : lam ≤ 2 * W * (W : ℝ) ^ (-B) := by
        rw [hlam]; simp only [sub_self, norm_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, zero_pow, zero_add]
        gcongr
      have hθ' : θ = (W : ℝ) ^ (-(B / 2)) / (16 * prefixF κ ^ 2) := by
        rw [hθ, hδ, hε, div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
        congr 1
        · congr 1; push_cast; ring
        · ring
      rw [hθ', div_div_eq_mul_div, div_le_iff₀ (Real.rpow_pos_of_pos hW0 _)]
      have e : (W : ℝ) ^ (1 - B / 2) * (W : ℝ) ^ (-(B / 2)) = (W : ℝ) * (W : ℝ) ^ (-B) := by
        rw [← Real.rpow_add hW0, ← Real.rpow_one_add' hW0.le (by linarith)]
        congr 1; ring
      calc lam * (16 * prefixF κ ^ 2) ≤ 2 * W * (W : ℝ) ^ (-B) * (16 * prefixF κ ^ 2) := by
            gcongr
        _ = 32 * prefixF κ ^ 2 * ((W : ℝ) ^ (1 - B / 2) * (W : ℝ) ^ (-(B / 2))) := by
            rw [e]; ring
        _ = _ := by ring
    have hK : K₀ ≤ Real.exp (prefixA κ q * q) * (32 * prefixF κ ^ 2) ^ q *
        (W : ℝ) ^ ((1 - B / 2) * q) := by
      rw [hK₀, mul_div_assoc, ← div_pow, Real.rpow_mul hW0.le, Real.rpow_natCast,
        mul_assoc, ← mul_pow]
      gcongr
    have hexp : B + C + (1 - B / 2) * q ≤ -D - 1 := by nlinarith
    have hpow : (W : ℝ) ^ (B + C) * (W : ℝ) ^ ((1 - B / 2) * q) ≤ (W : ℝ) ^ (-D - 1) := by
      rw [← Real.rpow_add hW0]
      exact Real.rpow_le_rpow_of_exponent_le hWr hexp
    have hWD : (W : ℝ) * (W : ℝ) ^ (-D - 1) = (W : ℝ) ^ (-D) := by
      rw [← Real.rpow_one_add' hW0.le (by linarith)]; congr 1; ring
    have hC₁0 : 0 ≤ C₁ := by positivity
    calc (starts.card : ℝ) * K₀ ≤ 3 * (W : ℝ) ^ (B + C) * (Real.exp (prefixA κ q * q) *
          (32 * prefixF κ ^ 2) ^ q * (W : ℝ) ^ ((1 - B / 2) * q)) := by
          gcongr
      _ = C₁ * ((W : ℝ) ^ (B + C) * (W : ℝ) ^ ((1 - B / 2) * q)) := by rw [hC₁]; ring
      _ ≤ C₁ * (W : ℝ) ^ (-D - 1) := by gcongr
      _ ≤ (W : ℝ) * (W : ℝ) ^ (-D - 1) := by gcongr
      _ = (W : ℝ) ^ (-D) := hWD
  calc μ W L {ω | ¬ CellClose n E (E : ℂ)
        (fun r => ((Real.sqrt s : ℝ) : ℂ) • gueBlock W L ω r) ε}
      ≤ μ W L (⋃ c ∈ starts, S c) := measure_mono hsub
    _ ≤ ∑ c ∈ starts, μ W L (S c) := measure_biUnion_finset_le _ _
    _ ≤ ∑ c ∈ starts, ENNReal.ofReal K₀ := Finset.sum_le_sum fun c _ => hcell c
    _ = ENNReal.ofReal ((starts.card : ℝ) * K₀) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal hfinal

end LSBA
