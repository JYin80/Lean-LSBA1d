import LSBA.Gauss.GUETop
import LSBA.Gauss.LipschitzConc
import LSBA.Gauss.GUENormMoment

/-!
# Sharp operator-norm tail and moments of a GUE block

For one normalized GUE block (1.2) [eq:covariance] and every width `W ≥ 1`:
`P(‖G‖ > 2 + t) ≤ 4 exp(-2Wt²/π²)` (from `𝔼 λ_max(G) ≤ 2` and Gaussian concentration, `λ_max`
being `W^{-1/2}`-Lipschitz in the standard coordinates), and the moment bound
`(𝔼‖G‖^{2p})^{1/(2p)} ≤ 2 + (4 p!)^{1/(2p)} π / √(2W)`. These are the GUE norm inputs of
Appendix G.4 [app:compact-gaussian].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `Re ⟨x, M x⟩ ≤ (Σ_{ij} |M_{ij}|²)^{1/2}` on the unit sphere. -/
private theorem GUENormSharp_re_quad_le {n : Type*} [Fintype n] (M : Matrix n n ℂ)
    (x : n → ℂ) (hx : ∑ i, ‖x i‖ ^ 2 = 1) :
    (star x ⬝ᵥ (M *ᵥ x)).re ≤ Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2) := by
  have h1 : (star x ⬝ᵥ (M *ᵥ x)).re ≤ ∑ i, ∑ j, ‖M i j‖ * (‖x i‖ * ‖x j‖) := by
    have : star x ⬝ᵥ (M *ᵥ x) = ∑ i, ∑ j, star (x i) * M i j * x j := by
      simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    rw [this, Complex.re_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    refine (Complex.re_le_norm _).trans (le_of_eq ?_)
    rw [norm_mul, norm_mul, norm_star]
    ring
  have h2 : ∑ i, ∑ j, ‖M i j‖ * (‖x i‖ * ‖x j‖) =
      ∑ p : n × n, ‖M p.1 p.2‖ * (‖x p.1‖ * ‖x p.2‖) := by
    rw [Fintype.sum_prod_type]
  have h3 : (∑ p : n × n, ‖M p.1 p.2‖ * (‖x p.1‖ * ‖x p.2‖)) ^ 2 ≤
      (∑ p : n × n, ‖M p.1 p.2‖ ^ 2) * ∑ p : n × n, (‖x p.1‖ * ‖x p.2‖) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h4 : ∑ p : n × n, (‖x p.1‖ * ‖x p.2‖) ^ 2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [mul_pow, ← Finset.mul_sum, ← Finset.sum_mul, hx]
    simp
  have h5 : ∑ p : n × n, ‖M p.1 p.2‖ ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
  rw [h4, mul_one, h5] at h3
  rw [h2] at h1
  exact h1.trans (Real.le_sqrt_of_sq_le h3)

/-- The unit sphere of `ℂ^n` is nonempty when `n` is. -/
private theorem GUENormSharp_sphere_nonempty {n : Type*} [Fintype n] [Nonempty n] :
    Nonempty {x : n → ℂ // ∑ i, ‖x i‖ ^ 2 = 1} := by
  classical
  obtain ⟨i0⟩ := ‹Nonempty n›
  refine ⟨⟨Pi.single i0 1, ?_⟩⟩
  rw [Finset.sum_eq_single i0 (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ _) h)]
  simp

/-- The values `Re ⟨x, A x⟩` over the unit sphere are bounded above. -/
private theorem GUENormSharp_bddAbove {n : Type*} [Fintype n] (A : Matrix n n ℂ) :
    BddAbove (Set.range fun x : {x : n → ℂ // ∑ i, ‖x i‖ ^ 2 = 1} =>
      (star x.1 ⬝ᵥ (A *ᵥ x.1)).re) :=
  ⟨Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2), by
    rintro _ ⟨x, rfl⟩
    exact GUENormSharp_re_quad_le A x.1 x.2⟩

/-- `Re ⟨x, A x⟩ ≤ topRe A` for a unit vector `x`. -/
private theorem GUENormSharp_le_topRe {n : Type*} [Fintype n] (A : Matrix n n ℂ) (x : n → ℂ)
    (hx : ∑ i, ‖x i‖ ^ 2 = 1) : (star x ⬝ᵥ (A *ᵥ x)).re ≤ topRe A :=
  le_ciSup (f := fun x : {x : n → ℂ // ∑ i, ‖x i‖ ^ 2 = 1} => (star x.1 ⬝ᵥ (A *ᵥ x.1)).re)
    (GUENormSharp_bddAbove A) ⟨x, hx⟩

/-- `topRe` is `1`-Lipschitz in the Frobenius norm (one direction). -/
private theorem GUENormSharp_topRe_le_add {n : Type*} [Fintype n] [Nonempty n]
    (A B : Matrix n n ℂ) :
    topRe A ≤ topRe B + Real.sqrt (∑ i, ∑ j, ‖(A - B) i j‖ ^ 2) := by
  have := GUENormSharp_sphere_nonempty (n := n)
  unfold topRe
  refine ciSup_le fun x => ?_
  have h1 : (star x.1 ⬝ᵥ (A *ᵥ x.1)).re =
      (star x.1 ⬝ᵥ (B *ᵥ x.1)).re + (star x.1 ⬝ᵥ ((A - B) *ᵥ x.1)).re := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]
    ring
  rw [h1]
  refine add_le_add ?_ (GUENormSharp_re_quad_le _ x.1 x.2)
  exact le_ciSup (f := fun x : {x : n → ℂ // ∑ i, ‖x i‖ ^ 2 = 1} => (star x.1 ⬝ᵥ (B *ᵥ x.1)).re)
    (GUENormSharp_bddAbove B) x

/-- `|topRe A - topRe B| ≤ (Σ_{ij} |(A-B)_{ij}|²)^{1/2}`. -/
private theorem GUENormSharp_abs_topRe_sub_le {n : Type*} [Fintype n] [Nonempty n]
    (A B : Matrix n n ℂ) :
    |topRe A - topRe B| ≤ Real.sqrt (∑ i, ∑ j, ‖(A - B) i j‖ ^ 2) := by
  have h1 := GUENormSharp_topRe_le_add A B
  have h2 := GUENormSharp_topRe_le_add B A
  have h3 : ∑ i, ∑ j, ‖(B - A) i j‖ ^ 2 = ∑ i, ∑ j, ‖(A - B) i j‖ ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.sub_apply, Matrix.sub_apply, norm_sub_rev]
  rw [h3] at h2
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-- A Hermitian matrix has operator norm at most `max (topRe G) (topRe (-G))`. -/
private theorem GUENormSharp_norm_le_max {W : ℕ} (hW : 1 ≤ W) (G : Matrix (Fin W) (Fin W) ℂ)
    (hG : G.IsHermitian) : ‖G‖ ≤ max (topRe G) (topRe (-G)) := by
  have : NeZero W := ⟨by omega⟩
  have hsa : IsSelfAdjoint G := hG
  have key : ∀ j, (hG.eigenvalues j) ≤ topRe G ∧ -(hG.eigenvalues j) ≤ topRe (-G) := by
    intro j
    set v : Fin W → ℂ := ⇑(hG.eigenvectorBasis j) with hv
    have hv1 : ∑ i, ‖v i‖ ^ 2 = 1 := by
      have h := (hG.eigenvectorBasis).norm_eq_one j
      rw [EuclideanSpace.norm_eq] at h
      have h2 := congrArg (· ^ 2) h
      simp only [one_pow] at h2
      rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)] at h2
      exact h2
    have hGv : G *ᵥ v = (hG.eigenvalues j : ℂ) • v := by
      have := hG.mulVec_eigenvectorBasis j
      simpa [hv] using this
    have hre : (star v ⬝ᵥ (G *ᵥ v)).re = hG.eigenvalues j := by
      rw [hGv, dotProduct_smul, smul_eq_mul]
      have : star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
        simp only [dotProduct, Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
          Complex.normSq_eq_norm_sq]
        push_cast
        rfl
      rw [this, hv1]
      simp
    refine ⟨hre ▸ GUENormSharp_le_topRe G v hv1, ?_⟩
    have := GUENormSharp_le_topRe (-G) v hv1
    rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re, hre] at this
    exact this
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum G hsa with h | h
  · rw [hG.spectrum_real_eq_range_eigenvalues] at h
    obtain ⟨j, hj⟩ := h
    exact (hj ▸ (key j).1).trans (le_max_left _ _)
  · rw [hG.spectrum_real_eq_range_eigenvalues] at h
    obtain ⟨j, hj⟩ := h
    have : ‖G‖ = -(hG.eigenvalues j) := by rw [hj]; ring
    exact (this ▸ (key j).2).trans (le_max_right _ _)

/-- The block of (1.2) [eq:covariance] is additive in the coordinates. -/
private theorem GUENormSharp_gueBlock_sub (W : ℕ) (ω ω' : Ω W 1) :
    gueBlock W 1 (ω - ω') 0 = gueBlock W 1 ω 0 - gueBlock W 1 ω' 0 := by
  ext α β
  simp only [gueBlock, Matrix.of_apply, Matrix.sub_apply, Pi.sub_apply]
  split_ifs <;> push_cast <;> ring

/-- The block of (1.2) [eq:covariance] is odd in the coordinates. -/
private theorem GUENormSharp_gueBlock_neg (W : ℕ) (ω : Ω W 1) :
    gueBlock W 1 (-ω) 0 = -gueBlock W 1 ω 0 := by
  ext α β
  simp only [gueBlock, Matrix.of_apply, Pi.neg_apply, Matrix.neg_apply]
  split_ifs <;> push_cast <;> ring

/-- The Frobenius norm of a block of (1.2) [eq:covariance]: `Σ_{ij} |G_{ij}|² = W⁻¹ Σ_k ω_k²`. -/
private theorem GUENormSharp_frob (W : ℕ) (η : Ω W 1) :
    ∑ i, ∑ j, ‖gueBlock W 1 η 0 i j‖ ^ 2 = (W : ℝ)⁻¹ * ∑ k, η k ^ 2 := by
  have h := sum_norm_sq_blockV W 1 η
  simp only [Fintype.sum_prod_type, Fin.sum_univ_one, blockV, blockDiagOp, Matrix.of_apply,
    ite_true] at h ⊢
  exact h

/-- The top eigenvalue `ω ↦ topRe (G ω)` of (1.2) [eq:covariance] is `W^{-1/2}`-Lipschitz in the
standard coordinates. -/
private theorem GUENormSharp_lipschitz {W : ℕ} (hW : 1 ≤ W) (x y : Ω W 1) :
    |topRe (gueBlock W 1 x 0) - topRe (gueBlock W 1 y 0)| ≤
      (Real.sqrt W)⁻¹ * Real.sqrt (∑ k, (x k - y k) ^ 2) := by
  have : NeZero W := ⟨by omega⟩
  refine (GUENormSharp_abs_topRe_sub_le _ _).trans (le_of_eq ?_)
  rw [← GUENormSharp_gueBlock_sub, GUENormSharp_frob, Real.sqrt_mul (by positivity),
    Real.sqrt_inv]
  have : (fun k => (x - y) k) = fun k => x k - y k := rfl
  simp [Pi.sub_apply]

/-- Gaussian concentration for a `W^{-1/2}`-Lipschitz `f` with `𝔼 f ≤ 2`:
`P(f > 2 + t) ≤ 2 exp(-2Wt²/π²)`. -/
private theorem GUENormSharp_tail_of_lipschitz {W : ℕ} (hW : 1 ≤ W) (f : Ω W 1 → ℝ)
    (hf : ∀ x y : Ω W 1, |f x - f y| ≤ (Real.sqrt W)⁻¹ * Real.sqrt (∑ k, (x k - y k) ^ 2))
    (hint : ∫ ω, f ω ∂(μ W 1) ≤ 2) {t : ℝ} (ht : 0 ≤ t) :
    μ W 1 {ω | 2 + t < f ω} ≤ ENNReal.ofReal (2 * Real.exp (-(2 * W * t ^ 2) / π ^ 2)) := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  set K : ℝ≥0 := ⟨(Real.sqrt W)⁻¹, by positivity⟩ with hKdef
  have hK : LipschitzWith K (fun x : EuclideanSpace ℝ (Fin 1 × Fin W × Fin W) => f x.ofLp) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, EuclideanSpace.dist_eq]
    have := hf x.ofLp y.ofLp
    have hKc : (K : ℝ) = (Real.sqrt W)⁻¹ := rfl
    simpa [Real.dist_eq, sq_abs, hKc] using this
  have h := concentration_lipschitz f K hK t ht
  have hKsq : (K : ℝ) ^ 2 = (W : ℝ)⁻¹ := by
    have hKc : (K : ℝ) = (Real.sqrt W)⁻¹ := rfl
    rw [hKc, inv_pow, Real.sq_sqrt hWr.le]
  rw [hKsq] at h
  refine le_trans (measure_mono ?_) (h.trans (le_of_eq ?_))
  · intro ω hω
    have hω' : 2 + t < f ω := hω
    change t < |f ω - ∫ y, f y ∂(stdGauss (Fin 1 × Fin W × Fin W))|
    have h2 : ∫ y, f y ∂(stdGauss (Fin 1 × Fin W × Fin W)) ≤ 2 := hint
    rw [abs_of_pos (by linarith)]
    linarith
  · congr 3
    field_simp

/-- `∫_0^∞ t^{2p-1} e^{-a t²} dt = a^{-p} (p-1)! / 2`. -/
private theorem GUENormSharp_gauss_integral {p : ℕ} (hp : 1 ≤ p) {a : ℝ} (ha : 0 < a) :
    ∫ t in Set.Ioi (0 : ℝ), t ^ ((2 * p : ℝ) - 1) * Real.exp (-a * t ^ (2 : ℝ)) =
      a ^ (-(p : ℝ)) / 2 * ((p - 1).factorial : ℝ) := by
  have hpr : (1 : ℝ) ≤ p := by exact_mod_cast hp
  rw [integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by linarith) ha]
  have h1 : (-((2 * p : ℝ) - 1 + 1) / 2) = -(p : ℝ) := by ring
  have h2 : (((2 * p : ℝ) - 1 + 1) / 2) = ((p - 1 : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub hp]; push_cast; ring
  rw [h1, h2, Real.Gamma_nat_eq_factorial]
  ring

/-- The measurability of `ω ↦ ‖G(ω)‖`. -/
private theorem GUENormSharp_measurable_norm (W : ℕ) :
    Measurable fun ω : Ω W 1 => ‖gueBlock W 1 ω 0‖ := by
  refine Measurable.norm ?_
  refine measurable_pi_iff.2 fun α => measurable_pi_iff.2 fun β => ?_
  simp only [gueBlock, Matrix.of_apply]
  split_ifs <;> fun_prop

/-- Layer-cake bound on the `2p`-th moment of the excess `(‖G‖ - 2)₊`:
`𝔼 (‖G‖ - 2)₊^{2p} ≤ 4 p! (π²/(2W))^p`. -/
private theorem GUENormSharp_lintegral_excess_le {W : ℕ} (hW : 1 ≤ W) {p : ℕ} (hp : 1 ≤ p)
    (htail : ∀ t : ℝ, 0 ≤ t → μ W 1 {ω | 2 + t < ‖gueBlock W 1 ω 0‖} ≤
      ENNReal.ofReal (4 * Real.exp (-(2 * W * t ^ 2) / π ^ 2))) :
    ∫⁻ ω, ENNReal.ofReal (max (‖gueBlock W 1 ω 0‖ - 2) 0 ^ (2 * p : ℝ)) ∂(μ W 1) ≤
      ENNReal.ofReal (4 * (p.factorial : ℝ) * (π ^ 2 / (2 * W)) ^ p) := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hpr : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hq : (0 : ℝ) < 2 * p := by linarith
  set a : ℝ := 2 * W / π ^ 2 with ha_def
  have ha : 0 < a := by positivity
  have hmeas : Measurable fun ω : Ω W 1 => max (‖gueBlock W 1 ω 0‖ - 2) 0 :=
    ((GUENormSharp_measurable_norm W).sub_const 2).max measurable_const
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul (μ := μ W 1)
    (f := fun ω => max (‖gueBlock W 1 ω 0‖ - 2) 0)
    (Filter.Eventually.of_forall fun ω => le_max_right _ _) hmeas.aemeasurable hq]
  have hint : IntegrableOn (fun t : ℝ => 4 * (t ^ ((2 * p : ℝ) - 1) *
      Real.exp (-a * t ^ (2 : ℝ)))) (Set.Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) (by norm_num) ha).const_mul 4
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] fun t : ℝ => 4 * (t ^ ((2 * p : ℝ) - 1) *
      Real.exp (-a * t ^ (2 : ℝ))) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have : 0 < t := ht
    positivity
  have hstep : ∫⁻ t in Set.Ioi (0 : ℝ), μ W 1 {ω | t < max (‖gueBlock W 1 ω 0‖ - 2) 0} *
      ENNReal.ofReal (t ^ ((2 * p : ℝ) - 1)) ≤
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (4 * (t ^ ((2 * p : ℝ) - 1) *
        Real.exp (-a * t ^ (2 : ℝ)))) := by
    refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    have hsub : {ω : Ω W 1 | t < max (‖gueBlock W 1 ω 0‖ - 2) 0} ⊆
        {ω | 2 + t < ‖gueBlock W 1 ω 0‖} := by
      intro ω hω
      have hω' : t < max (‖gueBlock W 1 ω 0‖ - 2) 0 := hω
      rcases lt_max_iff.1 hω' with h | h
      · change 2 + t < ‖gueBlock W 1 ω 0‖
        linarith
      · exact absurd h (not_lt.2 ht0.le)
    have h1 := (measure_mono hsub).trans (htail t ht0.le)
    have h2 : -(2 * (W : ℝ) * t ^ 2) / π ^ 2 = -a * t ^ (2 : ℝ) := by
      rw [Real.rpow_two, ha_def]; ring
    rw [h2] at h1
    calc μ W 1 {ω | t < max (‖gueBlock W 1 ω 0‖ - 2) 0} * ENNReal.ofReal (t ^ ((2 * p : ℝ) - 1))
        ≤ ENNReal.ofReal (4 * Real.exp (-a * t ^ (2 : ℝ))) *
            ENNReal.ofReal (t ^ ((2 * p : ℝ) - 1)) := by gcongr
      _ = ENNReal.ofReal (4 * (t ^ ((2 * p : ℝ) - 1) * Real.exp (-a * t ^ (2 : ℝ)))) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  have hval : ENNReal.ofReal (2 * p) * ∫⁻ t in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (4 * (t ^ ((2 * p : ℝ) - 1) * Real.exp (-a * t ^ (2 : ℝ)))) =
      ENNReal.ofReal (4 * (p.factorial : ℝ) * (π ^ 2 / (2 * W)) ^ p) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_const_mul,
      GUENormSharp_gauss_integral hp ha, ← ENNReal.ofReal_mul hq.le]
    congr 1
    have hf : (p.factorial : ℝ) = p * ((p - 1).factorial : ℝ) := by
      rw [← Nat.cast_mul, Nat.mul_factorial_pred (by omega)]
    have hr : a ^ (-(p : ℝ)) = (π ^ 2 / (2 * W)) ^ p := by
      rw [Real.rpow_neg ha.le, Real.rpow_natCast, ha_def, ← inv_pow, inv_div]
    rw [hf, hr]
    ring
  rw [← hval]
  exact mul_le_mul_right hstep _

/-- Sharp norm tail of one GUE block of (1.2) [eq:covariance]:
`P(‖G‖ > 2 + t) ≤ 4 exp(-2Wt²/π²)` for `W ≥ 1`, `t ≥ 0`. -/
theorem gueBlock_norm_tail_sharp {W : ℕ} (hW : 1 ≤ W) {t : ℝ} (ht : 0 ≤ t) :
    μ W 1 {ω | 2 + t < ‖gueBlock W 1 ω 0‖} ≤
      ENNReal.ofReal (4 * Real.exp (-(2 * W * t ^ 2) / π ^ 2)) := by
  have : NeZero W := ⟨by omega⟩
  set A : Set (Ω W 1) := {ω | 2 + t < topRe (gueBlock W 1 ω 0)} with hA
  have hmp : MeasurePreserving (fun ω : Ω W 1 => -ω) (μ W 1) (μ W 1) :=
    measurePreserving_stdGauss_linearIsometry (ι := Fin 1 × Fin W × Fin W)
      (LinearIsometryEquiv.neg ℝ)
  have hmp' : MeasurePreserving (MeasurableEquiv.neg (Ω W 1)) (μ W 1) (μ W 1) :=
    ⟨(MeasurableEquiv.neg (Ω W 1)).measurable, hmp.map_eq⟩
  have hsub : {ω : Ω W 1 | 2 + t < ‖gueBlock W 1 ω 0‖} ⊆
      A ∪ (MeasurableEquiv.neg (Ω W 1)) ⁻¹' A := by
    intro ω hω
    have hω' : 2 + t < ‖gueBlock W 1 ω 0‖ := hω
    have hle := GUENormSharp_norm_le_max hW _ (gueBlock_isHermitian W 1 ω 0)
    rcases lt_max_iff.1 (lt_of_lt_of_le hω' hle) with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      change 2 + t < topRe (gueBlock W 1 (-ω) 0)
      rw [GUENormSharp_gueBlock_neg]
      exact h
  have hA1 : μ W 1 A ≤ ENNReal.ofReal (2 * Real.exp (-(2 * W * t ^ 2) / π ^ 2)) :=
    GUENormSharp_tail_of_lipschitz hW (fun ω => topRe (gueBlock W 1 ω 0))
      (GUENormSharp_lipschitz hW) (integral_topRe_gueBlock_le W) ht
  calc μ W 1 {ω | 2 + t < ‖gueBlock W 1 ω 0‖}
      ≤ μ W 1 (A ∪ (MeasurableEquiv.neg (Ω W 1)) ⁻¹' A) := measure_mono hsub
    _ ≤ μ W 1 A + μ W 1 ((MeasurableEquiv.neg (Ω W 1)) ⁻¹' A) := measure_union_le _ _
    _ = μ W 1 A + μ W 1 A := by rw [hmp'.measure_preimage_equiv]
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(2 * W * t ^ 2) / π ^ 2)) +
          ENNReal.ofReal (2 * Real.exp (-(2 * W * t ^ 2) / π ^ 2)) := add_le_add hA1 hA1
    _ = ENNReal.ofReal (4 * Real.exp (-(2 * W * t ^ 2) / π ^ 2)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- Norm moments of one GUE block of (1.2) [eq:covariance]:
`(𝔼‖G‖^{2p})^{1/(2p)} ≤ 2 + (4 p!)^{1/(2p)} π / √(2W)` for `W ≥ 1`, `p ≥ 1`. -/
theorem gueBlock_norm_moment_le {W : ℕ} (hW : 1 ≤ W) {p : ℕ} (hp : 1 ≤ p) :
    (∫ ω, ‖gueBlock W 1 ω 0‖ ^ (2 * p) ∂(μ W 1)) ^ ((2 * p : ℝ)⁻¹) ≤
      2 + (4 * (p.factorial : ℝ)) ^ ((2 * p : ℝ)⁻¹) * π / Real.sqrt (2 * W) := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hpr : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hq : (0 : ℝ) < 2 * p := by linarith
  have hq1 : (1 : ℝ) ≤ 2 * p := by linarith
  have hq' : (0 : ℝ) ≤ 1 / (2 * p) := by positivity
  set I : ℝ := ∫ ω, ‖gueBlock W 1 ω 0‖ ^ (2 * p) ∂(μ W 1) with hI
  have hI0 : 0 ≤ I := integral_nonneg fun ω => by positivity
  have hXm : Measurable fun ω : Ω W 1 => ‖gueBlock W 1 ω 0‖ := GUENormSharp_measurable_norm W
  have hTm : Measurable fun ω : Ω W 1 => max (‖gueBlock W 1 ω 0‖ - 2) 0 :=
    (hXm.sub_const 2).max measurable_const
  have hIl : ENNReal.ofReal I = ∫⁻ ω, ENNReal.ofReal ‖gueBlock W 1 ω 0‖ ^ (2 * p : ℝ) ∂(μ W 1) := by
    rw [hI, ofReal_integral_eq_lintegral_ofReal (integrable_norm_gueBlock_pow W (2 * p))
      (Filter.Eventually.of_forall fun ω => by positivity)]
    refine lintegral_congr fun ω => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq.le]
    congr 1
    rw [← Real.rpow_natCast]
    push_cast
    rfl
  set f : Ω W 1 → ℝ≥0∞ := fun _ => ENNReal.ofReal 2 with hf
  set g : Ω W 1 → ℝ≥0∞ := fun ω => ENNReal.ofReal (max (‖gueBlock W 1 ω 0‖ - 2) 0) with hg
  have hMink := ENNReal.lintegral_Lp_add_le (μ := μ W 1) (p := 2 * p) (f := f) (g := g)
    aemeasurable_const hTm.ennreal_ofReal.aemeasurable hq1
  have hpt : ∀ ω : Ω W 1, ENNReal.ofReal ‖gueBlock W 1 ω 0‖ ≤ (f + g) ω := by
    intro ω
    simp only [hf, hg, Pi.add_apply]
    rw [← ENNReal.ofReal_add (by norm_num) (le_max_right _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := le_max_left (‖gueBlock W 1 ω 0‖ - 2) 0
    linarith
  have h1 : ∫⁻ ω, ENNReal.ofReal ‖gueBlock W 1 ω 0‖ ^ (2 * p : ℝ) ∂(μ W 1) ≤
      ∫⁻ ω, (f + g) ω ^ (2 * p : ℝ) ∂(μ W 1) :=
    lintegral_mono fun ω => ENNReal.rpow_le_rpow (hpt ω) hq.le
  have h2 : ∫⁻ ω, f ω ^ (2 * p : ℝ) ∂(μ W 1) = ENNReal.ofReal 2 ^ (2 * p : ℝ) := by
    simp [hf]
  have h3 : ∫⁻ ω, g ω ^ (2 * p : ℝ) ∂(μ W 1) ≤
      ENNReal.ofReal (4 * (p.factorial : ℝ) * (π ^ 2 / (2 * W)) ^ p) := by
    refine le_trans (le_of_eq (lintegral_congr fun ω => ?_))
      (GUENormSharp_lintegral_excess_le hW hp fun t ht => gueBlock_norm_tail_sharp hW ht)
    exact ENNReal.ofReal_rpow_of_nonneg (le_max_right _ _) hq.le
  have hB : (4 * (p.factorial : ℝ) * (π ^ 2 / (2 * W)) ^ p) ^ (1 / (2 * p : ℝ)) =
      (4 * (p.factorial : ℝ)) ^ ((2 * p : ℝ)⁻¹) * π / Real.sqrt (2 * W) := by
    have hπ : 0 < π := Real.pi_pos
    have h2W : (0 : ℝ) < 2 * W := by positivity
    rw [Real.mul_rpow (by positivity) (by positivity), one_div]
    have e1 : ((π ^ 2 / (2 * W)) ^ p) ^ ((2 * p : ℝ)⁻¹) = π / Real.sqrt (2 * W) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      have : (p : ℝ) * (2 * p : ℝ)⁻¹ = 1 / 2 := by field_simp
      rw [this, ← Real.sqrt_eq_rpow, Real.sqrt_div (by positivity), Real.sqrt_sq hπ.le]
    rw [e1, mul_div_assoc]
  have hC0 : 0 ≤ (4 * (p.factorial : ℝ)) ^ ((2 * p : ℝ)⁻¹) * π / Real.sqrt (2 * W) := by
    positivity
  have hfinal : ENNReal.ofReal (I ^ ((2 * p : ℝ)⁻¹)) ≤
      ENNReal.ofReal (2 + (4 * (p.factorial : ℝ)) ^ ((2 * p : ℝ)⁻¹) * π / Real.sqrt (2 * W)) := by
    calc ENNReal.ofReal (I ^ ((2 * p : ℝ)⁻¹)) = ENNReal.ofReal I ^ (1 / (2 * p : ℝ)) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hI0 (by positivity), one_div]
      _ = (∫⁻ ω, ENNReal.ofReal ‖gueBlock W 1 ω 0‖ ^ (2 * p : ℝ) ∂(μ W 1)) ^ (1 / (2 * p : ℝ)) := by
          rw [hIl]
      _ ≤ (∫⁻ ω, (f + g) ω ^ (2 * p : ℝ) ∂(μ W 1)) ^ (1 / (2 * p : ℝ)) :=
          ENNReal.rpow_le_rpow h1 hq'
      _ ≤ (∫⁻ ω, f ω ^ (2 * p : ℝ) ∂(μ W 1)) ^ (1 / (2 * p : ℝ)) +
            (∫⁻ ω, g ω ^ (2 * p : ℝ) ∂(μ W 1)) ^ (1 / (2 * p : ℝ)) := hMink
      _ ≤ ENNReal.ofReal 2 + ENNReal.ofReal
            ((4 * (p.factorial : ℝ) * (π ^ 2 / (2 * W)) ^ p) ^ (1 / (2 * p : ℝ))) := by
          refine add_le_add (le_of_eq ?_) ?_
          · rw [h2, ← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one]
          · rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) hq']
            exact ENNReal.rpow_le_rpow h3 hq'
      _ = ENNReal.ofReal (2 + (4 * (p.factorial : ℝ)) ^ ((2 * p : ℝ)⁻¹) * π /
            Real.sqrt (2 * W)) := by
          rw [hB, ← ENNReal.ofReal_add (by norm_num) hC0]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hfinal

end LSBA
