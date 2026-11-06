import LSBA.Gauss.SudakovFernique
import LSBA.Gauss.SphereNet
import LSBA.Gauss.GUELaw

/-!
# The top of the spectrum of a GUE block

`topRe A = sup_{‖x‖ = 1} Re ⟨x, A x⟩` (the largest eigenvalue for Hermitian `A`), and
`𝔼 λ_max(G) ≤ 2` for one normalized GUE block (1.2) [eq:covariance] at every width, by the
Sudakov–Fernique comparison of `x ↦ ⟨x, G x⟩` with `x ↦ √(2/W) Re ⟨g, x⟩` on finite nets.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- `sup_{‖x‖ = 1} Re ⟨x, A x⟩`, the largest eigenvalue of a Hermitian `A` (and `0` on `ℂ⁰`). -/
def topRe {n : Type*} [Fintype n] (A : Matrix n n ℂ) : ℝ :=
  ⨆ x : {x : n → ℂ // ∑ i, ‖x i‖ ^ 2 = 1}, (star x.1 ⬝ᵥ (A *ᵥ x.1)).re

/-! ### Deterministic estimates on the unit sphere -/

/-- `⟨v, M v⟩` as a double sum over the entries of `M`. -/
private theorem GUETop_quad_eq {n : Type*} [Fintype n] (M : Matrix n n ℂ) (v : n → ℂ) :
    star v ⬝ᵥ (M *ᵥ v) = ∑ i, ∑ j, star (v i) * M i j * v j := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/-- A coordinate of a vector of squared length at most `r²` has modulus at most `r`. -/
private theorem GUETop_norm_le {n : Type*} [Fintype n] (x : n → ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hx : ∑ i, ‖x i‖ ^ 2 ≤ r ^ 2) (i : n) : ‖x i‖ ≤ r := by
  have h : ‖x i‖ ^ 2 ≤ r ^ 2 :=
    (Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)).trans hx
  nlinarith [norm_nonneg (x i)]

/-- Moving a unit vector by `δ` changes `Re ⟨x, M x⟩` by at most `2δ Σ_{ij} |M_{ij}|`. -/
private theorem GUETop_re_le_near {n : Type*} [Fintype n] (M : Matrix n n ℂ) {δ : ℝ}
    (hδ : 0 < δ) (y v : n → ℂ) (hy : ∑ i, ‖y i‖ ^ 2 = 1) (hv : ∑ i, ‖v i‖ ^ 2 = 1)
    (hyv : ∑ i, ‖y i - v i‖ ^ 2 ≤ δ ^ 2) :
    (star y ⬝ᵥ (M *ᵥ y)).re ≤ (star v ⬝ᵥ (M *ᵥ v)).re + 2 * δ * ∑ i, ∑ j, ‖M i j‖ := by
  have hy1 := GUETop_norm_le y zero_le_one (by rw [hy]; norm_num)
  have hv1 := GUETop_norm_le v zero_le_one (by rw [hv]; norm_num)
  have hd := GUETop_norm_le (fun i => y i - v i) hδ.le hyv
  rw [GUETop_quad_eq, GUETop_quad_eq, Complex.re_sum, Complex.re_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Complex.re_sum, Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have key : star (y i) * M i j * y j = star (v i) * M i j * v j +
      M i j * (star (y i - v i) * y j + star (v i) * (y j - v j)) := by
    rw [star_sub]; ring
  rw [key, Complex.add_re]
  refine add_le_add le_rfl ((Complex.re_le_norm _).trans ?_)
  rw [norm_mul]
  have h2 : ‖star (y i - v i) * y j + star (v i) * (y j - v j)‖ ≤ 2 * δ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_star, norm_star]
    have := hd i
    have := hd j
    have := hy1 j
    have := hv1 i
    nlinarith [norm_nonneg (y i - v i), norm_nonneg (y j), norm_nonneg (v i),
      norm_nonneg (y j - v j)]
  calc ‖M i j‖ * ‖star (y i - v i) * y j + star (v i) * (y j - v j)‖ ≤ ‖M i j‖ * (2 * δ) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = 2 * δ * ‖M i j‖ := by ring

/-- `topRe M` is at most the maximum of `Re ⟨v, M v⟩` over a `δ`-net plus `2δ Σ_{ij} |M_{ij}|`. -/
private theorem GUETop_topRe_le_net {n : Type*} [Fintype n] (M : Matrix n n ℂ) {δ : ℝ}
    (hδ : 0 < δ) (N : Finset (n → ℂ)) [Nonempty N] (hN : ∀ v ∈ N, ∑ i, ‖v i‖ ^ 2 = 1)
    (hcov : ∀ y : n → ℂ, ∑ i, ‖y i‖ ^ 2 = 1 → ∃ v ∈ N, ∑ i, ‖y i - v i‖ ^ 2 ≤ δ ^ 2) :
    topRe M ≤ (⨆ t : N, (star t.1 ⬝ᵥ (M *ᵥ t.1)).re) + 2 * δ * ∑ i, ∑ j, ‖M i j‖ := by
  obtain ⟨⟨v0, hv0⟩⟩ := ‹Nonempty N›
  have : Nonempty {x : n → ℂ // ∑ i, ‖x i‖ ^ 2 = 1} := ⟨⟨v0, hN v0 hv0⟩⟩
  unfold topRe
  refine ciSup_le fun y => ?_
  obtain ⟨v, hv, hyv⟩ := hcov y.1 y.2
  refine (GUETop_re_le_near M hδ y.1 v y.2 (hN v hv) hyv).trans (add_le_add ?_ le_rfl)
  exact le_ciSup (Finite.bddAbove_range fun t : N => (star t.1 ⬝ᵥ (M *ᵥ t.1)).re) ⟨v, hv⟩

/-- `|max_t f_t| ≤ Σ_t |f_t|` over a finite nonempty index set. -/
private theorem GUETop_abs_iSup_le {T : Type*} [Fintype T] [Nonempty T] (f : T → ℝ) :
    |⨆ t, f t| ≤ ∑ t, |f t| := by
  obtain ⟨t0⟩ := ‹Nonempty T›
  have hs : ∀ t, |f t| ≤ ∑ s, |f s| := fun t =>
    Finset.single_le_sum (f := fun s => |f s|) (fun s _ => abs_nonneg _) (Finset.mem_univ t)
  refine abs_le.2 ⟨?_, ciSup_le fun t => (le_abs_self _).trans (hs t)⟩
  have h1 : f t0 ≤ ⨆ t, f t := le_ciSup (Finite.bddAbove_range f) t0
  have h2 := neg_abs_le (f t0)
  linarith [hs t0]

/-! ### Standard Gaussian coordinates -/

private theorem GUETop_memLp_coord {ι : Type*} [Fintype ι] (k : ι) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (fun x : ι → ℝ => x k) p (stdGauss ι) := by
  have h : MemLp id p (gaussianReal (0 : ℝ) 1) := memLp_id_gaussianReal' p hp
  exact h.comp_measurePreserving (measurePreserving_eval (fun _ : ι => gaussianReal (0 : ℝ) 1) k)

private theorem GUETop_integrable_coord {ι : Type*} [Fintype ι] (k : ι) :
    Integrable (fun x : ι → ℝ => x k) (stdGauss ι) :=
  (GUETop_memLp_coord k ENNReal.one_ne_top).integrable le_rfl

private theorem GUETop_integrable_sq {ι : Type*} [Fintype ι] (k : ι) :
    Integrable (fun x : ι → ℝ => x k ^ 2) (stdGauss ι) :=
  (GUETop_memLp_coord k ENNReal.ofNat_ne_top).integrable_sq

/-- `𝔼 x_k² = 1` under the standard Gaussian measure. -/
private theorem GUETop_integral_sq {ι : Type*} [Fintype ι] (k : ι) :
    ∫ x, x k ^ 2 ∂(stdGauss ι) = 1 := by
  have h := measurePreserving_eval (fun _ : ι => gaussianReal (0 : ℝ) 1) k
  have h2 := integral_map h.measurable.aemeasurable (f := fun t : ℝ => t ^ 2)
    (by rw [h.map_eq]; exact (by fun_prop : Continuous fun t : ℝ => t ^ 2).aestronglyMeasurable)
  rw [h.map_eq] at h2
  have h3 : ∫ t : ℝ, t ^ 2 ∂(gaussianReal 0 1) = 1 := by
    have hv := variance_id_gaussianReal (μ := (0 : ℝ)) (v := 1)
    have h0 : (gaussianReal (0 : ℝ) 1)[id] = 0 := integral_id_gaussianReal
    rw [variance_of_integral_eq_zero aemeasurable_id h0] at hv
    simpa using hv
  rw [h3] at h2
  exact h2.symm

/-- A finite maximum of linear forms in standard Gaussian coordinates is integrable. -/
private theorem GUETop_integrable_iSup {T ι : Type*} [Fintype T] [Nonempty T] [Fintype ι]
    (A : T → ι → ℝ) : Integrable (fun x : ι → ℝ => ⨆ t, ∑ i, A t i * x i) (stdGauss ι) := by
  have hlin : ∀ t, Integrable (fun x : ι → ℝ => ∑ i, A t i * x i) (stdGauss ι) := fun t =>
    integrable_finsetSum _ fun i _ => (GUETop_integrable_coord i).const_mul _
  have hm : Measurable fun x : ι → ℝ => ⨆ t, ∑ i, A t i * x i :=
    Measurable.iSup fun t => (continuous_finsetSum _ fun i _ =>
      continuous_const.mul (continuous_apply i)).measurable
  refine (integrable_finsetSum Finset.univ fun t _ => (hlin t).abs).mono'
    hm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  simpa using GUETop_abs_iSup_le fun t => ∑ i, A t i * x i

/-! ### The two Gaussian processes -/

/-- Coefficients of `Re ⟨v, G v⟩` in the coordinates of one GUE block. -/
private def GUETop_coefA (W : ℕ) (v : Fin W → ℂ) (i : Fin 1 × Fin W × Fin W) : ℝ :=
  (Real.sqrt W)⁻¹ * (star v ⬝ᵥ (hermBasis W (i.2.1, i.2.2) *ᵥ v)).re

/-- Coefficients of `√(2/W) Re ⟨g, v⟩` in the real coordinates of `g ∈ ℂ^W`. -/
private def GUETop_coefB (W : ℕ) (v : Fin W → ℂ) (k : Fin W × Fin 2) : ℝ :=
  Real.sqrt 2 * (Real.sqrt W)⁻¹ * (if k.2 = 0 then (v k.1).re else (v k.1).im)

/-- `Re ⟨v, G v⟩ = Σ_i A_v(i) ω_i` for `G = gueBlock W 1 ω 0`. -/
private theorem GUETop_re_gueBlock (W : ℕ) (ω : Ω W 1) (v : Fin W → ℂ) :
    (star v ⬝ᵥ (gueBlock W 1 ω 0 *ᵥ v)).re = ∑ i, GUETop_coefA W v i * ω i := by
  conv_rhs => rw [Fintype.sum_prod_type, Fin.sum_univ_one]
  rw [gueBlock_eq_sum_hermBasis, Matrix.smul_mulVec, Matrix.sum_mulVec, dotProduct_smul,
    dotProduct_sum]
  simp_rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.re_ofReal_mul, GUETop_coefA]
  ring

/-- `Σ_k ⟨s, H_k s⟩ ⟨t, H_k t⟩ = ⟨s, t⟩ conj ⟨s, t⟩` (completeness of `hermBasis`). -/
private theorem GUETop_sum_herm_mul_complex (W : ℕ) (s t : Fin W → ℂ) :
    ∑ k, (star s ⬝ᵥ (hermBasis W k *ᵥ s)) * (star t ⬝ᵥ (hermBasis W k *ᵥ t)) =
      (star s ⬝ᵥ t) * starRingEnd ℂ (star s ⬝ᵥ t) := by
  simp_rw [GUETop_quad_eq]
  have hL : ∑ k : Fin W × Fin W, (∑ i, ∑ j, star (s i) * hermBasis W k i j * s j) *
      (∑ l, ∑ m, star (t l) * hermBasis W k l m * t m) =
      ∑ i, ∑ j, ∑ l, ∑ m, star (s i) * s j * (star (t l) * t m) *
        ∑ k : Fin W × Fin W, hermBasis W k i j * hermBasis W k l m := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hL]
  simp_rw [sum_hermBasis_apply_mul_apply, ite_and, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [dotProduct, Pi.star_apply, map_sum, map_mul, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.star_def, Complex.conj_conj, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- `Σ_k Re⟨s, H_k s⟩ Re⟨t, H_k t⟩ = |⟨s, t⟩|²` (completeness of `hermBasis`). -/
private theorem GUETop_sum_herm_mul (W : ℕ) (s t : Fin W → ℂ) :
    ∑ k, (star s ⬝ᵥ (hermBasis W k *ᵥ s)).re * (star t ⬝ᵥ (hermBasis W k *ᵥ t)).re =
      Complex.normSq (star s ⬝ᵥ t) := by
  have him : ∀ (k : Fin W × Fin W) (x : Fin W → ℂ), (star x ⬝ᵥ (hermBasis W k *ᵥ x)).im = 0 :=
    fun k x => (hermBasis_isHermitian W k).im_star_dotProduct_mulVec_self x
  have h := congrArg Complex.re (GUETop_sum_herm_mul_complex W s t)
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.re_sum] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.mul_re, him, him, mul_zero, sub_zero]

/-- `⟨s, s⟩ = Σ_i |s_i|²`. -/
private theorem GUETop_dot_self {n : Type*} [Fintype n] (s : n → ℂ) :
    star s ⬝ᵥ s = ((∑ i, ‖s i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq]
  push_cast
  rfl

/-- `Σ_a |s_a - t_a|² = Σ_a |s_a|² + Σ_a |t_a|² - 2 Re ⟨s, t⟩`, in real coordinates. -/
private theorem GUETop_sum_sub_sq {n : Type*} [Fintype n] (s t : n → ℂ) :
    ∑ a, (((s a).re - (t a).re) ^ 2 + ((s a).im - (t a).im) ^ 2) =
      ∑ a, ‖s a‖ ^ 2 + ∑ a, ‖t a‖ ^ 2 - 2 * (star s ⬝ᵥ t).re := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- The increments of `Re ⟨v, G v⟩` are dominated by those of `√(2/W) Re ⟨g, v⟩` on the unit
sphere: `(2/W)(1 - |⟨s,t⟩|²) ≤ (2/W) · 2(1 - Re ⟨s,t⟩)`. -/
private theorem GUETop_increment (W : ℕ) (s t : Fin W → ℂ) (hs : ∑ i, ‖s i‖ ^ 2 = 1)
    (ht : ∑ i, ‖t i‖ ^ 2 = 1) :
    ∑ i, (GUETop_coefA W s i - GUETop_coefA W t i) ^ 2 ≤
      ∑ k, (GUETop_coefB W s k - GUETop_coefB W t k) ^ 2 := by
  set c : ℝ := (Real.sqrt W)⁻¹ with hc
  set z : ℂ := star s ⬝ᵥ t with hz
  have hss : Complex.normSq (star s ⬝ᵥ s) = 1 := by
    rw [GUETop_dot_self, hs, Complex.ofReal_one, map_one]
  have htt : Complex.normSq (star t ⬝ᵥ t) = 1 := by
    rw [GUETop_dot_self, ht, Complex.ofReal_one, map_one]
  have hL : ∑ i, (GUETop_coefA W s i - GUETop_coefA W t i) ^ 2 =
      c ^ 2 * (2 - 2 * Complex.normSq z) := by
    rw [Fintype.sum_prod_type, Fin.sum_univ_one]
    simp only [GUETop_coefA]
    have h1 := GUETop_sum_herm_mul W s s
    have h2 := GUETop_sum_herm_mul W s t
    have h3 := GUETop_sum_herm_mul W t t
    rw [hss] at h1
    rw [htt] at h3
    rw [← hz] at h2
    have hexp : ∀ k : Fin W × Fin W,
        (c * (star s ⬝ᵥ (hermBasis W (k.1, k.2) *ᵥ s)).re -
          c * (star t ⬝ᵥ (hermBasis W (k.1, k.2) *ᵥ t)).re) ^ 2 =
        c ^ 2 * ((star s ⬝ᵥ (hermBasis W k *ᵥ s)).re * (star s ⬝ᵥ (hermBasis W k *ᵥ s)).re) -
          2 * c ^ 2 * ((star s ⬝ᵥ (hermBasis W k *ᵥ s)).re *
            (star t ⬝ᵥ (hermBasis W k *ᵥ t)).re) +
          c ^ 2 * ((star t ⬝ᵥ (hermBasis W k *ᵥ t)).re *
            (star t ⬝ᵥ (hermBasis W k *ᵥ t)).re) := by
      intro k; ring
    rw [Finset.sum_congr rfl fun k _ => hexp k, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, h1, h2, h3]
    ring
  have hR : ∑ k, (GUETop_coefB W s k - GUETop_coefB W t k) ^ 2 = 2 * c ^ 2 * (2 - 2 * z.re) := by
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two, GUETop_coefB, ← hc, Fin.isValue, ite_true, Fin.one_eq_zero_iff,
      OfNat.ofNat_ne_one, ite_false]
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hexp : ∀ a : Fin W,
        (Real.sqrt 2 * c * (s a).re - Real.sqrt 2 * c * (t a).re) ^ 2 +
          (Real.sqrt 2 * c * (s a).im - Real.sqrt 2 * c * (t a).im) ^ 2 =
        2 * c ^ 2 * (((s a).re - (t a).re) ^ 2 + ((s a).im - (t a).im) ^ 2) := by
      intro a
      have : (Real.sqrt 2 * c * (s a).re - Real.sqrt 2 * c * (t a).re) ^ 2 +
          (Real.sqrt 2 * c * (s a).im - Real.sqrt 2 * c * (t a).im) ^ 2 =
          Real.sqrt 2 ^ 2 * c ^ 2 * (((s a).re - (t a).re) ^ 2 + ((s a).im - (t a).im) ^ 2) := by
        ring
      rw [this, h2]
    rw [Finset.sum_congr rfl fun a _ => hexp a, ← Finset.mul_sum, GUETop_sum_sub_sq, hs, ht]
    ring
  have hN : z.re ^ 2 ≤ Complex.normSq z := by
    rw [Complex.normSq_apply]; nlinarith [sq_nonneg z.im]
  rw [hL, hR]
  nlinarith [sq_nonneg c, sq_nonneg (1 - z.re), mul_nonneg (sq_nonneg c) (sq_nonneg (1 - z.re)),
    mul_nonneg (sq_nonneg c) (sub_nonneg.2 hN)]

/-- `𝔼 max_t √(2/W) Re ⟨g, v_t⟩ ≤ √(2/W) 𝔼 |g| ≤ 2` over unit vectors `v_t`. -/
private theorem GUETop_integral_B_le (W : ℕ) (hW : 0 < W) {T : Type*} [Fintype T] [Nonempty T]
    (V : T → Fin W → ℂ) (hV : ∀ t, ∑ i, ‖V t i‖ ^ 2 = 1) :
    ∫ y, (⨆ t, ∑ k, GUETop_coefB W (V t) k * y k) ∂(stdGauss (Fin W × Fin 2)) ≤ 2 := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  by_cases hI : Integrable (fun y : Fin W × Fin 2 → ℝ => ⨆ t, ∑ k, GUETop_coefB W (V t) k * y k)
    (stdGauss (Fin W × Fin 2))
  swap
  · rw [integral_undef hI]; norm_num
  have hc2 : ((Real.sqrt W)⁻¹) ^ 2 = (W : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hW'.le]
  have hB2 : ∀ t, ∑ k, GUETop_coefB W (V t) k ^ 2 = 2 / W := by
    intro t
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two, GUETop_coefB, Fin.isValue, ite_true, Fin.one_eq_zero_iff,
      OfNat.ofNat_ne_one, ite_false]
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hexp : ∀ a : Fin W, (Real.sqrt 2 * (Real.sqrt W)⁻¹ * (V t a).re) ^ 2 +
        (Real.sqrt 2 * (Real.sqrt W)⁻¹ * (V t a).im) ^ 2 =
        2 * (W : ℝ)⁻¹ * ‖V t a‖ ^ 2 := by
      intro a
      rw [Complex.sq_norm, Complex.normSq_apply, ← hc2]
      have : (Real.sqrt 2 * (Real.sqrt W)⁻¹ * (V t a).re) ^ 2 +
          (Real.sqrt 2 * (Real.sqrt W)⁻¹ * (V t a).im) ^ 2 =
          Real.sqrt 2 ^ 2 * (Real.sqrt W)⁻¹ ^ 2 * ((V t a).re * (V t a).re +
            (V t a).im * (V t a).im) := by ring
      rw [this, h2]
    rw [Finset.sum_congr rfl fun a _ => hexp a, ← Finset.mul_sum, hV t]
    field_simp
  have hpt : ∀ y : Fin W × Fin 2 → ℝ,
      (⨆ t, ∑ k, GUETop_coefB W (V t) k * y k) ≤ 1 + (∑ k, y k ^ 2) / (2 * W) := by
    intro y
    refine ciSup_le fun t => ?_
    have hterm : ∀ k, GUETop_coefB W (V t) k * y k ≤
        W / 2 * GUETop_coefB W (V t) k ^ 2 + y k ^ 2 / (2 * W) := by
      intro k
      have h : W / 2 * GUETop_coefB W (V t) k ^ 2 + y k ^ 2 / (2 * W) -
          GUETop_coefB W (V t) k * y k = (W * GUETop_coefB W (V t) k - y k) ^ 2 / (2 * W) := by
        field_simp
        ring
      have : 0 ≤ (W * GUETop_coefB W (V t) k - y k) ^ 2 / (2 * W) := by positivity
      linarith
    refine (Finset.sum_le_sum fun k _ => hterm k).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hB2, ← Finset.sum_div]
    field_simp
  have hsq : Integrable (fun y : Fin W × Fin 2 → ℝ => ∑ k, y k ^ 2) (stdGauss (Fin W × Fin 2)) :=
    integrable_finsetSum _ fun k _ => GUETop_integrable_sq k
  refine (integral_mono hI ((integrable_const 1).add (hsq.div_const _)) hpt).trans (le_of_eq ?_)
  simp only [Pi.add_apply]
  rw [integral_add (integrable_const 1) (hsq.div_const _), integral_const, integral_div,
    integral_finsetSum _ fun k _ => GUETop_integrable_sq k]
  simp only [GUETop_integral_sq, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, probReal_univ, smul_eq_mul, mul_one, nsmul_eq_mul]
  push_cast
  field_simp
  ring

/-- `𝔼 λ_max(G) ≤ 2` for one GUE block of (1.2) [eq:covariance], at every width `W`. -/
theorem integral_topRe_gueBlock_le (W : ℕ) : ∫ ω, topRe (gueBlock W 1 ω 0) ∂(μ W 1) ≤ 2 := by
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · have : IsEmpty {x : Fin 0 → ℂ // ∑ i, ‖x i‖ ^ 2 = 1} := ⟨fun x => by simpa using x.2⟩
    simp [topRe]
  by_cases hint : Integrable (fun ω => topRe (gueBlock W 1 ω 0)) (μ W 1)
  swap
  · rw [integral_undef hint]; norm_num
  set S : Ω W 1 → ℝ := fun ω => ∑ i, ∑ j, ‖gueBlock W 1 ω 0 i j‖ with hS
  have hSint : Integrable S (μ W 1) := integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => (integrable_gueBlock W 1 0 i j).norm
  have hS0 : 0 ≤ ∫ ω, S ω ∂(μ W 1) := integral_nonneg fun ω => by positivity
  have hsphere : ∑ i, ‖(Pi.single (⟨0, hW⟩ : Fin W) 1 : Fin W → ℂ) i‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single (⟨0, hW⟩ : Fin W) (fun b _ hb => by simp [hb])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
  have key : ∀ δ > 0,
      ∫ ω, topRe (gueBlock W 1 ω 0) ∂(μ W 1) ≤ 2 + 2 * δ * ∫ ω, S ω ∂(μ W 1) := by
    intro δ hδ
    obtain ⟨N, -, hN, hcov⟩ := exists_sphere_net (Fin W) hδ
    obtain ⟨v0, hv0, -⟩ := hcov _ hsphere
    have : Nonempty N := ⟨⟨v0, hv0⟩⟩
    set A : N → Fin 1 × Fin W × Fin W → ℝ := fun t => GUETop_coefA W t.1 with hA
    set B : N → Fin W × Fin 2 → ℝ := fun t => GUETop_coefB W t.1 with hB
    have hpt : ∀ ω, topRe (gueBlock W 1 ω 0) ≤ (⨆ t, ∑ i, A t i * ω i) + 2 * δ * S ω := by
      intro ω
      have h := GUETop_topRe_le_net (gueBlock W 1 ω 0) hδ N hN hcov
      simp only [GUETop_re_gueBlock] at h
      exact h
    have hmaxint : Integrable (fun ω : Ω W 1 => ⨆ t, ∑ i, A t i * ω i) (μ W 1) :=
      GUETop_integrable_iSup A
    have hSF := sudakov_fernique A B fun s t =>
      GUETop_increment W s.1 t.1 (hN _ s.2) (hN _ t.2)
    have hBle := GUETop_integral_B_le W hW (fun t : N => t.1) fun t => hN _ t.2
    calc ∫ ω, topRe (gueBlock W 1 ω 0) ∂(μ W 1)
        ≤ ∫ ω, ((⨆ t, ∑ i, A t i * ω i) + 2 * δ * S ω) ∂(μ W 1) :=
          integral_mono hint (hmaxint.add (hSint.const_mul _)) hpt
      _ = ∫ ω, (⨆ t, ∑ i, A t i * ω i) ∂(μ W 1) + 2 * δ * ∫ ω, S ω ∂(μ W 1) := by
          rw [integral_add hmaxint (hSint.const_mul _), integral_const_mul]
      _ ≤ 2 + 2 * δ * ∫ ω, S ω ∂(μ W 1) := by
          gcongr
          rw [μ_eq_stdGauss]
          exact hSF.trans hBle
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set E := ∫ ω, S ω ∂(μ W 1) with hE
  have hδ : 0 < ε / (2 * (E + 1)) := by positivity
  refine (key _ hδ).trans ?_
  have h1 : 2 * (ε / (2 * (E + 1))) * E = ε * (E / (E + 1)) := by
    field_simp
  have h2 : E / (E + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
  have h3 : 2 * (ε / (2 * (E + 1))) * E ≤ ε := by
    rw [h1]; exact mul_le_of_le_one_right hε.le h2
  linarith

end LSBA
