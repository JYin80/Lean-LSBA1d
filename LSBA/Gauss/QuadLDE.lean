import LSBA.Gauss.RowSplit
import LSBA.Gauss.HaarMoment

/-!
# Quadratic and linear large deviations

Tail bounds for `h*Ah − n⁻¹Tr A` and for `Σ_k V_{j,e k} a_k` with `A`, `a` independent of the column
(rescaled `haarMoment_gauss_quadForm`).
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

noncomputable section
open scoped Classical

namespace LSBA

/-- A standard real Gaussian is sub-Gaussian with parameter `1`. -/
private lemma quadLDE_subgauss :
    HasSubgaussianMGF (fun y : ℝ => y) 1 (gaussianReal 0 1) := by
  refine ⟨fun t => integrable_exp_mul_gaussianReal t, fun t => ?_⟩
  have h := congrFun (mgf_id_gaussianReal (μ := (0 : ℝ)) (v := 1)) t
  have h' : mgf (fun y : ℝ => y) (gaussianReal 0 1) t = Real.exp (0 * t + 1 * t ^ 2 / 2) := by
    simp only [NNReal.coe_one] at h
    exact h
  rw [h']
  simp

/-- Gaussian tail of a real linear form `∑ q, u q * x q` in a standard Gaussian vector, at scale
`(∑ q, u q ^ 2)^{1/2}` (Chernoff bound, Appendix G.1 [app:relative-local-law-proof]). -/
private lemma quadLDE_linear_tail {ι : Type*} [Fintype ι] (u : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    stdGauss ι {x | t * Real.sqrt (∑ q, u q ^ 2) < |∑ q, u q * x q|} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2)) := by
  by_cases hS : ∑ q, u q ^ 2 = 0
  · have hu : ∀ q, u q = 0 := fun q => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => sq_nonneg (u q))).mp hS q
        (Finset.mem_univ q)
      simpa using this
    have : {x : ι → ℝ | t * Real.sqrt (∑ q, u q ^ 2) < |∑ q, u q * x q|} = ∅ := by
      ext x
      simp [hu]
    rw [this]
    simp
  · have hS' : 0 < ∑ q, u q ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg fun q _ => sq_nonneg (u q)) (Ne.symm hS)
    let X : ι → (ι → ℝ) → ℝ := fun q x => u q * x q
    have hind : iIndepFun X (stdGauss ι) :=
      iIndepFun_pi (X := fun q (y : ℝ) => u q * y) (μ := fun _ => gaussianReal 0 1)
        (fun q => (measurable_const.mul measurable_id).aemeasurable)
    have hsub : ∀ q ∈ (Finset.univ : Finset ι),
        HasSubgaussianMGF (X q) (Real.toNNReal (u q ^ 2)) (stdGauss ι) := by
      intro q _
      have h1 : HasSubgaussianMGF (fun y : ℝ => u q * y) (Real.toNNReal (u q ^ 2))
          (gaussianReal 0 1) := by
        have := quadLDE_subgauss.const_mul (u q)
        convert this using 1
        ext
        rw [Real.coe_toNNReal _ (sq_nonneg _)]
        change u q ^ 2 = u q ^ 2 * 1
        ring
      have h2 : HasSubgaussianMGF ((fun y : ℝ => u q * y) ∘ (fun x : ι → ℝ => x q))
          (Real.toNNReal (u q ^ 2)) (stdGauss ι) := by
        refine HasSubgaussianMGF.of_map (measurable_pi_apply q).aemeasurable ?_
        have := (measurePreserving_eval (fun _ : ι => gaussianReal (0 : ℝ) 1) q).map_eq
        unfold stdGauss
        rw [this]
        exact h1
      exact h2
    have hsum := HasSubgaussianMGF.sum_of_iIndepFun hind hsub
    have hc : (((∑ q ∈ (Finset.univ : Finset ι), (Real.toNNReal (u q ^ 2))) : NNReal) : ℝ) =
        ∑ q, u q ^ 2 := by
      rw [NNReal.coe_sum]
      simp [Real.coe_toNNReal _ (sq_nonneg _)]
    have hex : -(t * Real.sqrt (∑ q, u q ^ 2)) ^ 2 / (2 * ∑ q, u q ^ 2) = -t ^ 2 / 2 := by
      rw [mul_pow, Real.sq_sqrt hS'.le]
      field_simp
    have h1 := hsum.measure_ge_le (ε := t * Real.sqrt (∑ q, u q ^ 2)) (by positivity)
    have h2 := hsum.neg.measure_ge_le (ε := t * Real.sqrt (∑ q, u q ^ 2)) (by positivity)
    rw [hc, hex] at h1 h2
    have hsubset : {x : ι → ℝ | t * Real.sqrt (∑ q, u q ^ 2) < |∑ q, u q * x q|} ⊆
        {x | t * Real.sqrt (∑ q, u q ^ 2) ≤ ∑ i ∈ (Finset.univ : Finset ι), X i x} ∪
        {x | t * Real.sqrt (∑ q, u q ^ 2) ≤
          (-fun x => ∑ i ∈ (Finset.univ : Finset ι), X i x) x} := by
      intro x hx
      simp only [Set.mem_ofPred_eq, Set.mem_union, Pi.neg_apply] at hx ⊢
      rcases le_total 0 (∑ q, u q * x q) with h | h
      · left; rw [abs_of_nonneg h] at hx; exact hx.le
      · right; rw [abs_of_nonpos h] at hx; simp only [X]; linarith
    refine (measure_mono hsubset).trans ((measure_union_le _ _).trans ?_)
    rw [← ofReal_measureReal (μ := stdGauss ι), ← ofReal_measureReal (μ := stdGauss ι),
      ← ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith

/-- The entries of the GUE matrix are measurable in the sample. -/
private lemma quadLDE_measurable_entry (n : ℕ) (a b : Fin n) :
    Measurable fun ω : Ω n 1 => gueMat n ω a b := by
  unfold gueMat gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

/-- The complex coordinate `x (k, 0) + i x (k, 1)` is measurable in `x`. -/
private lemma quadLDE_measurable_mk {κ : Type*} (k : κ) :
    Measurable fun x : κ × Fin 2 → ℝ => (⟨x (k, 0), x (k, 1)⟩ : ℂ) := by
  have h : (fun x : κ × Fin 2 → ℝ => (⟨x (k, 0), x (k, 1)⟩ : ℂ)) =
      fun x => ((x (k, 0) : ℝ) : ℂ) + ((x (k, 1) : ℝ) : ℂ) * Complex.I := by
    funext x; apply Complex.ext <;> simp
  rw [h]
  fun_prop

/-- Conditional tail bound: if the Gaussian probability of the section of a measurable set `S` at
each fixed `a` is at most `B`, the same holds for the column `(V_{e k, j})_k` and a function `A`
of the other coordinates. -/
private lemma quadLDE_cond {α : Type*} [MeasurableSpace α] (n : ℕ) (j : Fin n) {κ : Type*}
    [Fintype κ] (e : κ → Fin n) (he : Function.Injective e) (hej : ∀ k, e k ≠ j)
    {A : Ω n 1 → α} (hA : Measurable A) (hoff : OffRow n j A)
    {S : Set ((κ → ℂ) × α)} (hS : MeasurableSet S) {B : ENNReal}
    (hB : ∀ a : α, stdGauss (κ × Fin 2)
        {x | (fun k => ((Real.sqrt (2 * n))⁻¹ : ℝ) * (⟨x (k, 0), x (k, 1)⟩ : ℂ), a) ∈ S} ≤ B) :
    μ n 1 {ω | (fun k => gueMat n ω (e k) j, A ω) ∈ S} ≤ B := by
  have hcol : Measurable fun ω : Ω n 1 => (fun k => gueMat n ω (e k) j) :=
    measurable_pi_iff.mpr fun k => quadLDE_measurable_entry n (e k) j
  have hF : Measurable fun ω : Ω n 1 => ((fun k => gueMat n ω (e k) j), A ω) :=
    hcol.prodMk hA
  have hmeas : MeasurableSet {ω : Ω n 1 | (fun k => gueMat n ω (e k) j, A ω) ∈ S} := hF hS
  have h1 := lintegral_col_offRow n j e he hej hA hoff (Φ := S.indicator 1)
    (measurable_one.indicator hS)
  have h2 : μ n 1 {ω | (fun k => gueMat n ω (e k) j, A ω) ∈ S} =
      ∫⁻ ω, S.indicator 1 (fun k => gueMat n ω (e k) j, A ω) ∂(μ n 1) := by
    rw [← lintegral_indicator_one hmeas]
    refine lintegral_congr fun ω => ?_
    simp [Set.indicator]
  rw [h2, h1]
  calc ∫⁻ ω, ∫⁻ x, S.indicator 1
        (fun k => ((Real.sqrt (2 * n))⁻¹ : ℝ) * (⟨x (k, 0), x (k, 1)⟩ : ℂ), A ω)
        ∂(stdGauss (κ × Fin 2)) ∂(μ n 1)
      ≤ ∫⁻ ω, B ∂(μ n 1) := by
        refine lintegral_mono fun ω => ?_
        have hx : Measurable fun x : κ × Fin 2 → ℝ =>
            ((fun k => ((Real.sqrt (2 * n))⁻¹ : ℝ) * (⟨x (k, 0), x (k, 1)⟩ : ℂ)), A ω) := by
          refine Measurable.prodMk ?_ measurable_const
          exact measurable_pi_iff.mpr fun k => measurable_const.mul (quadLDE_measurable_mk k)
        have h3 : ∫⁻ x, S.indicator 1
            (fun k => ((Real.sqrt (2 * n))⁻¹ : ℝ) * (⟨x (k, 0), x (k, 1)⟩ : ℂ), A ω)
            ∂(stdGauss (κ × Fin 2)) =
            stdGauss (κ × Fin 2) {x | (fun k => ((Real.sqrt (2 * n))⁻¹ : ℝ) *
              (⟨x (k, 0), x (k, 1)⟩ : ℂ), A ω) ∈ S} := by
          refine Eq.trans (lintegral_congr fun x => ?_) (lintegral_indicator_one (hx hS))
          simp [Set.indicator]
        rw [h3]
        exact hB (A ω)
    _ = B := by simp

/-- Real and imaginary parts of `∑ k, conj (c g_k) b_k` for the Gaussian vector
`g_k = x_{k0} + i x_{k1}` are `c` times real linear forms in `x`. -/
private lemma quadLDE_lin_parts {κ : Type*} [Fintype κ] (b : κ → ℂ) (c : ℝ) (x : κ × Fin 2 → ℝ) :
    (∑ k, star ((c : ℂ) * (⟨x (k, 0), x (k, 1)⟩ : ℂ)) * b k).re =
        c * ∑ q : κ × Fin 2, ![(b q.1).re, (b q.1).im] q.2 * x q ∧
      (∑ k, star ((c : ℂ) * (⟨x (k, 0), x (k, 1)⟩ : ℂ)) * b k).im =
        c * ∑ q : κ × Fin 2, ![(b q.1).im, -(b q.1).re] q.2 * x q := by
  rw [Complex.re_sum, Complex.im_sum, Fintype.sum_prod_type, Fintype.sum_prod_type,
    Finset.mul_sum, Finset.mul_sum]
  constructor
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp [Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]
    ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp [Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]
    ring

/-- The two coefficient vectors of `quadLDE_lin_parts` have squared norm `∑ k, |b_k|²`. -/
private lemma quadLDE_sumsq_re_im {κ : Type*} [Fintype κ] (b : κ → ℂ) :
    (∑ q : κ × Fin 2, (![(b q.1).re, (b q.1).im] q.2) ^ 2 = ∑ k, ‖b k‖ ^ 2) ∧
      ∑ q : κ × Fin 2, (![(b q.1).im, -(b q.1).re] q.2) ^ 2 = ∑ k, ‖b k‖ ^ 2 := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  constructor
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply]
    simp [sq]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply]
    simp [sq]
    ring

/-- Gaussian tail of `∑ k, conj (c g_k) b_k`, `c = (2n)^{-1/2}`, at scale `(n⁻¹ ∑ |b_k|²)^{1/2}`. -/
private lemma quadLDE_lin_inner (n : ℕ) (hn : 0 < n) {κ : Type*} [Fintype κ] (b : κ → ℂ)
    {t : ℝ} (ht : 0 ≤ t) :
    stdGauss (κ × Fin 2)
      {x | t * Real.sqrt ((n : ℝ)⁻¹ * ∑ k, ‖b k‖ ^ 2) <
        ‖∑ k, star (((Real.sqrt (2 * n))⁻¹ : ℝ) * (⟨x (k, 0), x (k, 1)⟩ : ℂ)) * b k‖} ≤
      ENNReal.ofReal (4 * Real.exp (-t ^ 2 / 2)) := by
  set c : ℝ := (Real.sqrt (2 * n))⁻¹ with hc
  set u : κ × Fin 2 → ℝ := fun q => ![(b q.1).re, (b q.1).im] q.2 with hu
  set w : κ × Fin 2 → ℝ := fun q => ![(b q.1).im, -(b q.1).re] q.2 with hw
  obtain ⟨hu2, hw2⟩ := quadLDE_sumsq_re_im b
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc2 : c ^ 2 = (2 * (n : ℝ))⁻¹ := by
    rw [hc, inv_pow, Real.sq_sqrt (by positivity)]
  set B : ℝ := ∑ k, ‖b k‖ ^ 2 with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun k _ => by positivity
  have hsub : {x : κ × Fin 2 → ℝ | t * Real.sqrt ((n : ℝ)⁻¹ * B) <
        ‖∑ k, star (c * (⟨x (k, 0), x (k, 1)⟩ : ℂ)) * b k‖} ⊆
      {x | t * Real.sqrt (∑ q, u q ^ 2) < |∑ q, u q * x q|} ∪
      {x | t * Real.sqrt (∑ q, w q ^ 2) < |∑ q, w q * x q|} := by
    intro x hx
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hcon hx
    obtain ⟨h1, h2⟩ := hcon
    rw [hu2] at h1
    rw [hw2] at h2
    obtain ⟨hre, him⟩ := quadLDE_lin_parts b c x
    set Z : ℂ := ∑ k, star ((c : ℂ) * (⟨x (k, 0), x (k, 1)⟩ : ℂ)) * b k with hZ
    have hsq1 : (∑ q, u q * x q) ^ 2 ≤ (t * Real.sqrt B) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hsq2 : (∑ q, w q * x q) ^ 2 ≤ (t * Real.sqrt B) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    have hZsq : ‖Z‖ ^ 2 ≤ (t * Real.sqrt ((n : ℝ)⁻¹ * B)) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, mul_pow, Real.sq_sqrt (by positivity)]
      have e1 : Z.re * Z.re = c ^ 2 * (∑ q, u q * x q) ^ 2 := by rw [hre]; ring
      have e2 : Z.im * Z.im = c ^ 2 * (∑ q, w q * x q) ^ 2 := by rw [him]; ring
      rw [e1, e2, hc2]
      have e3 : (t * Real.sqrt B) ^ 2 = t ^ 2 * B := by
        rw [mul_pow, Real.sq_sqrt hB0]
      have : (2 * (n : ℝ))⁻¹ * ((t * Real.sqrt B) ^ 2 + (t * Real.sqrt B) ^ 2) =
          t ^ 2 * ((n : ℝ)⁻¹ * B) := by
        rw [e3]; field_simp; ring
      calc (2 * (n : ℝ))⁻¹ * (∑ q, u q * x q) ^ 2 + (2 * (n : ℝ))⁻¹ * (∑ q, w q * x q) ^ 2
          = (2 * (n : ℝ))⁻¹ * ((∑ q, u q * x q) ^ 2 + (∑ q, w q * x q) ^ 2) := by ring
        _ ≤ (2 * (n : ℝ))⁻¹ * ((t * Real.sqrt B) ^ 2 + (t * Real.sqrt B) ^ 2) := by
            gcongr
        _ = _ := this
    have hr : 0 ≤ t * Real.sqrt ((n : ℝ)⁻¹ * B) := by positivity
    have := abs_le_of_sq_le_sq' hZsq hr
    linarith [this.2, norm_nonneg Z, hx]
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have hu_t := quadLDE_linear_tail u ht
  have hw_t := quadLDE_linear_tail w ht
  calc _ ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2)) +
        ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2)) := add_le_add hu_t hw_t
    _ = ENNReal.ofReal (4 * Real.exp (-t ^ 2 / 2)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- Rescaling of the Gaussian quadratic form: with `h = c g`, `c = (2n)^{-1/2}`,
`h* M h - n⁻¹ Tr M = (2n)⁻¹ (g* M g - 2 Tr M)`. -/
private lemma quadLDE_rescale (n : ℕ) (hn : 0 < n) {W : ℕ} (M : Matrix (Fin W) (Fin W) ℂ)
    (x : Fin W × Fin 2 → ℝ) :
    ‖star (fun k => ((Real.sqrt (2 * n))⁻¹ : ℝ) * (⟨x (k, 0), x (k, 1)⟩ : ℂ)) ⬝ᵥ
        (M *ᵥ fun k => ((Real.sqrt (2 * n))⁻¹ : ℝ) * (⟨x (k, 0), x (k, 1)⟩ : ℂ)) -
        (n : ℂ)⁻¹ * M.trace‖ =
      (2 * (n : ℝ))⁻¹ *
        ‖star (cplxVec W x) ⬝ᵥ (M *ᵥ cplxVec W x) - 2 * M.trace‖ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set c : ℝ := (Real.sqrt (2 * n))⁻¹ with hc
  have hc2 : c ^ 2 = (2 * (n : ℝ))⁻¹ := by
    rw [hc, inv_pow, Real.sq_sqrt (by positivity)]
  have hh : (fun k => ((c : ℝ) : ℂ) * (⟨x (k, 0), x (k, 1)⟩ : ℂ)) = (c : ℂ) • cplxVec W x := rfl
  have h1 : star ((c : ℂ) • cplxVec W x) ⬝ᵥ (M *ᵥ ((c : ℂ) • cplxVec W x)) =
      ((2 * (n : ℝ))⁻¹ : ℝ) * (star (cplxVec W x) ⬝ᵥ (M *ᵥ cplxVec W x)) := by
    rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    rw [← mul_assoc, ← Complex.ofReal_mul, ← sq, hc2]
  have h2 : ((n : ℂ))⁻¹ * M.trace = (((2 * (n : ℝ))⁻¹ : ℝ) : ℂ) * (2 * M.trace) := by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    field_simp
  rw [hh, h1, h2, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-- Gaussian tail of the rescaled quadratic form for a fixed matrix on `Fin W`: Markov's inequality
at order `2p` with the moment bound of `haarMoment_gauss_quadForm`. -/
private lemma quadLDE_quad_inner (p : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (W n : ℕ), 0 < n → ∀ (M : Matrix (Fin W) (Fin W) ℂ) (t : ℝ), 0 < t →
      stdGauss (Fin W × Fin 2)
        {x | t / n * Real.sqrt (∑ k, ∑ l, ‖M k l‖ ^ 2) <
          ‖star (fun k => ((Real.sqrt (2 * n))⁻¹ : ℝ) * (⟨x (k, 0), x (k, 1)⟩ : ℂ)) ⬝ᵥ
            (M *ᵥ fun k => ((Real.sqrt (2 * n))⁻¹ : ℝ) * (⟨x (k, 0), x (k, 1)⟩ : ℂ)) -
            (n : ℂ)⁻¹ * M.trace‖} ≤ ENNReal.ofReal (K * t ^ (-(2 * (p : ℝ)))) := by
  obtain ⟨K', hK', hQ⟩ := haarMoment_gauss_quadForm p
  refine ⟨K' / 4 ^ p, by positivity, fun W n hn M t ht => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set HS : ℝ := ∑ k, ∑ l, ‖M k l‖ ^ 2 with hHS
  have hHS0 : 0 ≤ HS := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => by positivity
  set Q : (Fin W × Fin 2 → ℝ) → ℂ := fun x =>
    star (cplxVec W x) ⬝ᵥ (M *ᵥ cplxVec W x) - 2 * M.trace with hQdef
  -- the event is contained in `2 t √HS < ‖Q‖`
  have hsub : {x : Fin W × Fin 2 → ℝ |
      t / n * Real.sqrt HS < ‖star (fun k => ((Real.sqrt (2 * n))⁻¹ : ℝ) *
          (⟨x (k, 0), x (k, 1)⟩ : ℂ)) ⬝ᵥ
        (M *ᵥ fun k => ((Real.sqrt (2 * n))⁻¹ : ℝ) * (⟨x (k, 0), x (k, 1)⟩ : ℂ)) -
        (n : ℂ)⁻¹ * M.trace‖} ⊆ {x | 2 * t * Real.sqrt HS < ‖Q x‖} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [quadLDE_rescale n hn M x] at hx
    have h2n : (0 : ℝ) < 2 * n := by positivity
    have : 2 * t * Real.sqrt HS = (2 * n) * (t / n * Real.sqrt HS) := by
      field_simp
    rw [this]
    calc (2 * (n : ℝ)) * (t / n * Real.sqrt HS)
        < (2 * (n : ℝ)) * ((2 * (n : ℝ))⁻¹ * ‖Q x‖) := by gcongr
      _ = ‖Q x‖ := by field_simp
  refine (measure_mono hsub).trans ?_
  have hrpow : t ^ (-(2 * (p : ℝ))) = (t ^ (2 * p))⁻¹ := by
    rw [Real.rpow_neg ht.le]
    congr 1
    rw [← Real.rpow_natCast]
    push_cast
    rfl
  rw [hrpow]
  by_cases hHS' : HS = 0
  · have hM : M = 0 := by
      ext k l
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg ‖M k l‖)).mp hHS' k (Finset.mem_univ k)
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => sq_nonneg ‖M k l‖)).mp h1 l
        (Finset.mem_univ l)
      simpa using h2
    have hempty : {x : Fin W × Fin 2 → ℝ | 2 * t * Real.sqrt HS < ‖Q x‖} = ∅ := by
      ext x
      simp [hQdef, hM, hHS']
    rw [hempty]
    simp
  · have hHSpos : 0 < HS := lt_of_le_of_ne hHS0 (Ne.symm hHS')
    set c0 : ℝ := 2 * t * Real.sqrt HS with hc0
    have hc0pos : 0 < c0 := by positivity
    have hc0p : c0 ^ (2 * p) = 4 ^ p * t ^ (2 * p) * HS ^ p := by
      rw [hc0, mul_pow, mul_pow, pow_mul, pow_mul, pow_mul, Real.sq_sqrt hHS0]
      norm_num
    have hmk := mul_meas_ge_le_integral_of_nonneg (μ := stdGauss (Fin W × Fin 2))
      (f := fun x => ‖Q x‖ ^ (2 * p)) (Filter.Eventually.of_forall fun x => by positivity)
      (hQ W M).1 (c0 ^ (2 * p))
    have hsub2 : {x : Fin W × Fin 2 → ℝ | c0 < ‖Q x‖} ⊆
        {x | c0 ^ (2 * p) ≤ ‖Q x‖ ^ (2 * p)} := fun x hx =>
      pow_le_pow_left₀ hc0pos.le (le_of_lt hx) _
    have hmom := (hQ W M).2
    have hreal : (stdGauss (Fin W × Fin 2)).real {x | c0 < ‖Q x‖} ≤
        K' / 4 ^ p * (t ^ (2 * p))⁻¹ := by
      have h1 : (stdGauss (Fin W × Fin 2)).real {x | c0 < ‖Q x‖} ≤
          (stdGauss (Fin W × Fin 2)).real {x | c0 ^ (2 * p) ≤ ‖Q x‖ ^ (2 * p)} :=
        measureReal_mono hsub2
      refine h1.trans ?_
      have hpos : 0 < c0 ^ (2 * p) := by positivity
      have h2 : c0 ^ (2 * p) * (stdGauss (Fin W × Fin 2)).real
          {x | c0 ^ (2 * p) ≤ ‖Q x‖ ^ (2 * p)} ≤ K' * HS ^ p := hmk.trans hmom
      rw [← le_div_iff₀' hpos] at h2
      refine h2.trans (le_of_eq ?_)
      rw [hc0p]
      have : (0 : ℝ) < HS ^ p := by positivity
      field_simp
    rw [← ofReal_measureReal (μ := stdGauss (Fin W × Fin 2))]
    exact ENNReal.ofReal_le_ofReal hreal

/-- The quadratic-form tail for the index set `Fin W`. -/
private lemma quadLDE_quad_fin (p : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (j : Fin n) (W : ℕ) (e : Fin W → Fin n), Function.Injective e →
      (∀ k, e k ≠ j) → ∀ A : Ω n 1 → Matrix (Fin W) (Fin W) ℂ, Measurable A → OffRow n j A →
        ∀ t : ℝ, 0 < t →
        μ n 1 {ω | t / n * Real.sqrt (∑ k, ∑ l, ‖A ω k l‖ ^ 2) <
            ‖star (fun k => gueMat n ω (e k) j) ⬝ᵥ (A ω *ᵥ fun k => gueMat n ω (e k) j) -
              (n : ℂ)⁻¹ * (A ω).trace‖} ≤
          ENNReal.ofReal (K * t ^ (-(2 * (p : ℝ)))) := by
  obtain ⟨K, hK, h⟩ := quadLDE_quad_inner p
  refine ⟨K, hK, fun n j W e he hej A hA hoff t ht => ?_⟩
  have hn : 0 < n := Fin.pos j
  have hS : MeasurableSet {q : (Fin W → ℂ) × Matrix (Fin W) (Fin W) ℂ |
      t / n * Real.sqrt (∑ k, ∑ l, ‖q.2 k l‖ ^ 2) <
        ‖star q.1 ⬝ᵥ (q.2 *ᵥ q.1) - (n : ℂ)⁻¹ * q.2.trace‖} :=
    measurableSet_lt (by fun_prop) (by fun_prop)
  exact quadLDE_cond n j e he hej hA hoff hS fun M => h W n hn M t ht

/-- Conditional Gaussian quadratic-form estimate of Appendix G.1 [app:relative-local-law-proof]:
for `A` independent of row `j`, `P(|h^* A h - n⁻¹ Tr A| > t n⁻¹ ‖A‖_HS) ≤ K t^{-2p}`,
`h = (V_{e k, j})_k`. -/
theorem gue_quadForm_tail (p : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (j : Fin n) {κ : Type} [Fintype κ] [DecidableEq κ]
      (e : κ → Fin n), Function.Injective e → (∀ k, e k ≠ j) →
      ∀ A : Ω n 1 → Matrix κ κ ℂ, Measurable A → OffRow n j A → ∀ t : ℝ, 0 < t →
        μ n 1 {ω | t / n * Real.sqrt (∑ k, ∑ l, ‖A ω k l‖ ^ 2) <
            ‖star (fun k => gueMat n ω (e k) j) ⬝ᵥ (A ω *ᵥ fun k => gueMat n ω (e k) j) -
              (n : ℂ)⁻¹ * (A ω).trace‖} ≤
          ENNReal.ofReal (K * t ^ (-(2 * (p : ℝ)))) := by
  obtain ⟨K, hK, h⟩ := quadLDE_quad_fin p
  refine ⟨K, hK, fun n j κ _ _ e he hej A hA hoff t ht => ?_⟩
  set σ : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ with hσ
  have hmeas : Measurable fun ω : Ω n 1 => (A ω).submatrix σ.symm σ.symm := by
    refine measurable_pi_iff.mpr fun k => measurable_pi_iff.mpr fun l => ?_
    change Measurable fun ω => A ω (σ.symm k) (σ.symm l)
    exact (measurable_pi_apply (σ.symm l)).comp ((measurable_pi_apply (σ.symm k)).comp hA)
  have hoff' : OffRow n j fun ω : Ω n 1 => (A ω).submatrix σ.symm σ.symm := by
    intro ω ω' hω
    simp only [hoff ω ω' hω]
  have key := h n j (Fintype.card κ) (e ∘ σ.symm) (he.comp σ.symm.injective)
    (fun k => hej _) (fun ω => (A ω).submatrix σ.symm σ.symm) hmeas hoff' t ht
  have hset : {ω : Ω n 1 | t / n * Real.sqrt (∑ k, ∑ l, ‖A ω k l‖ ^ 2) <
      ‖star (fun k => gueMat n ω (e k) j) ⬝ᵥ (A ω *ᵥ fun k => gueMat n ω (e k) j) -
        (n : ℂ)⁻¹ * (A ω).trace‖} =
      {ω | t / n * Real.sqrt (∑ k, ∑ l, ‖((A ω).submatrix σ.symm σ.symm) k l‖ ^ 2) <
        ‖star (fun k => gueMat n ω ((e ∘ σ.symm) k) j) ⬝ᵥ
          (((A ω).submatrix σ.symm σ.symm) *ᵥ fun k => gueMat n ω ((e ∘ σ.symm) k) j) -
          (n : ℂ)⁻¹ * ((A ω).submatrix σ.symm σ.symm).trace‖} := by
    ext ω
    have e1 : ∑ k, ∑ l, ‖((A ω).submatrix σ.symm σ.symm) k l‖ ^ 2 =
        ∑ k, ∑ l, ‖A ω k l‖ ^ 2 := by
      simp only [Matrix.submatrix_apply]
      rw [Equiv.sum_comp σ.symm (fun k => ∑ l, ‖A ω k (σ.symm l)‖ ^ 2)]
      exact Finset.sum_congr rfl fun k _ =>
        Equiv.sum_comp σ.symm (fun l => ‖A ω k l‖ ^ 2)
    have e2 : star (fun k => gueMat n ω ((e ∘ σ.symm) k) j) ⬝ᵥ
          (((A ω).submatrix σ.symm σ.symm) *ᵥ fun k => gueMat n ω ((e ∘ σ.symm) k) j) =
        star (fun k => gueMat n ω (e k) j) ⬝ᵥ (A ω *ᵥ fun k => gueMat n ω (e k) j) := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.submatrix_apply,
        Function.comp_apply]
      rw [← Equiv.sum_comp σ.symm (fun k => star (gueMat n ω (e k) j) *
        ∑ l, A ω k l * gueMat n ω (e l) j)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Equiv.sum_comp σ.symm (fun l => A ω (σ.symm i) l * gueMat n ω (e l) j)]
    have e3 : ((A ω).submatrix σ.symm σ.symm).trace = (A ω).trace := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
      exact Equiv.sum_comp σ.symm (fun k => A ω k k)
    simp only [Set.mem_ofPred_eq, e1, e2, e3]
  rw [hset]
  exact key

/-- Conditional Gaussian linear-form estimate of Appendix G.1 [app:relative-local-law-proof]:
for `a` independent of row `j`, `P(|Σ_k V_{j, e k} a_k| > t (n⁻¹ Σ_k |a_k|²)^{1/2}) ≤
4 exp(-t²/2)`. -/
theorem gue_linForm_tail (n : ℕ) (j : Fin n) {κ : Type*} [Fintype κ] (e : κ → Fin n)
    (he : Function.Injective e) (hej : ∀ k, e k ≠ j) {a : Ω n 1 → κ → ℂ} (ha : Measurable a)
    (hoff : OffRow n j a) {t : ℝ} (ht : 0 ≤ t) :
    μ n 1 {ω | t * Real.sqrt ((n : ℝ)⁻¹ * ∑ k, ‖a ω k‖ ^ 2) <
        ‖∑ k, gueMat n ω j (e k) * a ω k‖} ≤
      ENNReal.ofReal (4 * Real.exp (-t ^ 2 / 2)) := by
  have hn : 0 < n := Fin.pos j
  have hS : MeasurableSet {p : (κ → ℂ) × (κ → ℂ) |
      t * Real.sqrt ((n : ℝ)⁻¹ * ∑ k, ‖p.2 k‖ ^ 2) < ‖∑ k, star (p.1 k) * p.2 k‖} :=
    measurableSet_lt (by fun_prop) (by fun_prop)
  have hset : {ω : Ω n 1 | t * Real.sqrt ((n : ℝ)⁻¹ * ∑ k, ‖a ω k‖ ^ 2) <
        ‖∑ k, gueMat n ω j (e k) * a ω k‖} =
      {ω | (fun k => gueMat n ω (e k) j, a ω) ∈
        {p : (κ → ℂ) × (κ → ℂ) |
          t * Real.sqrt ((n : ℝ)⁻¹ * ∑ k, ‖p.2 k‖ ^ 2) < ‖∑ k, star (p.1 k) * p.2 k‖}} := by
    ext ω
    have hh : ∀ k, gueMat n ω j (e k) = star (gueMat n ω (e k) j) := fun k =>
      ((gueBlock_isHermitian n 1 ω 0).apply j (e k)).symm
    simp only [Set.mem_ofPred_eq, hh]
  rw [hset]
  exact quadLDE_cond n j e he hej ha hoff hS fun b => quadLDE_lin_inner n hn b ht

end LSBA
