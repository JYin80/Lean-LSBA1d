import LSBA.Spectral.Resolvent
import LSBA.Spectral.Counts

/-!
# Poisson smoothing of heavy spectral atoms

Lemma 4.2 [uv:lem:poisson]: the mass of the heavy atoms of a finite measure is controlled by the
Poisson smoothing of the measure at height `η`, in the scalar form (4.2) [uv:eq:poisson] and the
matrix form (4.3) [uv:eq:matrix-poisson]. Two consequences for a Hermitian matrix: the spectral
form at a coordinate, and the first step of the proof of Theorem 2.2 [uv:lem:lower-volume],
which bounds the number of eigenvectors with short localization length by heavy coordinates.
-/

open MeasureTheory Real Finset
open scoped ENNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Poisson kernel `η / ((λ - E)² + η²)`. -/
def poissonKer (η lam E : ℝ) : ℝ := η / ((lam - E) ^ 2 + η ^ 2)

private lemma poissonKer_nonneg {η : ℝ} (hη : 0 < η) (lam E : ℝ) : 0 ≤ poissonKer η lam E := by
  unfold poissonKer
  positivity

private lemma continuous_poissonKer {η : ℝ} (hη : 0 < η) (lam : ℝ) :
    Continuous (poissonKer η lam) := by
  unfold poissonKer
  refine continuous_const.div (by fun_prop) fun E => ?_
  positivity

/-- On `[λ - η, λ + η]` the kernel is at least `1 / (2η)`. -/
private lemma poissonKer_ge {η lam E : ℝ} (hη : 0 < η) (hE : E ∈ Set.Icc (lam - η) (lam + η)) :
    1 / (2 * η) ≤ poissonKer η lam E := by
  obtain ⟨h1, h2⟩ := hE
  unfold poissonKer
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

/-- The kernel has mass `π / 2` on `[λ - η, λ + η]`. -/
private lemma integral_poissonKer {η : ℝ} (hη : 0 < η) (lam : ℝ) :
    ∫ E in Set.Icc (lam - η) (lam + η), poissonKer η lam E = π / 2 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  have hderiv : ∀ E ∈ Set.uIcc (lam - η) (lam + η),
      HasDerivAt (fun E => Real.arctan ((E - lam) / η)) (poissonKer η lam E) E := by
    intro E _
    have h := (((hasDerivAt_id E).sub_const lam).div_const η).arctan
    refine h.congr_deriv ?_
    unfold poissonKer
    have : (lam - E) ^ 2 + η ^ 2 ≠ 0 := by positivity
    have : η ^ 2 + (E - lam) ^ 2 ≠ 0 := by positivity
    simp only [id]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_poissonKer hη lam).intervalIntegrable _ _)]
  have h1 : (lam + η - lam) / η = 1 := by field_simp; ring
  have h2 : (lam - η - lam) / η = -1 := by field_simp; ring
  rw [h1, h2, Real.arctan_one, Real.arctan_neg, Real.arctan_one]
  ring

/-- Core of (4.2) [uv:eq:poisson] and (4.3) [uv:eq:matrix-poisson]: atoms of masses `m k ≥ 0` at
`lam k`, and any measurable set `P`
containing `[λ_k - η, λ_k + η]` for each `k` in a finite set `S` of atoms with `λ_k ∈ [c, d]`. -/
private lemma poisson_core {ι : Type*} [Fintype ι] (lam m : ι → ℝ) (hm : ∀ k, 0 ≤ m k)
    {η : ℝ} (hη : 0 < η) (c d : ℝ) (S : Finset ι) (hS : ∀ k ∈ S, lam k ∈ Set.Icc c d)
    (P : Set ℝ) (hP : MeasurableSet P)
    (hPk : ∀ k ∈ S, ∀ E ∈ Set.Icc (lam k - η) (lam k + η), E ∈ P) :
    ∑ k ∈ S, m k ≤ 2 / π * ∫ E in Set.Icc (c - η) (d + η),
      P.indicator (fun E => ∑ k, m k * poissonKer η (lam k) E) E := by
  set f : ℝ → ℝ := fun E => ∑ k, m k * poissonKer η (lam k) E with hf
  have hfc : Continuous f :=
    continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_poissonKer hη _)
  set T := Set.Icc (c - η) (d + η) with hT
  have hIsub : ∀ k ∈ S, Set.Icc (lam k - η) (lam k + η) ⊆ T := by
    intro k hk E hE
    have := hS k hk
    exact ⟨by linarith [hE.1, this.1], by linarith [hE.2, this.2]⟩
  set g : ι → ℝ → ℝ := fun k => (Set.Icc (lam k - η) (lam k + η)).indicator
    (fun E => m k * poissonKer η (lam k) E) with hg
  have hgint : ∀ k, Integrable (g k) (volume.restrict T) := fun k =>
    Integrable.indicator
      ((continuous_const.mul (continuous_poissonKer hη (lam k))).integrableOn_Icc
        (a := c - η) (b := d + η) (μ := volume)) measurableSet_Icc
  have h1 : ∀ k ∈ S, m k * (π / 2) = ∫ E in T, g k E := by
    intro k hk
    change _ = ∫ E in T, (Set.Icc (lam k - η) (lam k + η)).indicator
      (fun E => m k * poissonKer η (lam k) E) E
    rw [setIntegral_indicator measurableSet_Icc, Set.inter_eq_right.mpr (hIsub k hk),
      integral_const_mul, integral_poissonKer hη]
  have h2 : ∑ k ∈ S, ∫ E in T, g k E = ∫ E in T, ∑ k ∈ S, g k E :=
    (integral_finsetSum S fun k _ => hgint k).symm
  have h3 : ∫ E in T, ∑ k ∈ S, g k E ≤ ∫ E in T, P.indicator f E := by
    refine setIntegral_mono_on (integrable_finsetSum S fun k _ => hgint k)
      (Integrable.indicator (hfc.integrableOn_Icc (a := c - η) (b := d + η) (μ := volume)) hP)
      measurableSet_Icc fun E _ => ?_
    by_cases hE : E ∈ P
    · rw [Set.indicator_of_mem hE]
      calc ∑ k ∈ S, g k E ≤ ∑ k ∈ S, m k * poissonKer η (lam k) E :=
            Finset.sum_le_sum fun k _ => Set.indicator_le_self'
              (fun E _ => mul_nonneg (hm k) (poissonKer_nonneg hη _ _)) E
        _ ≤ ∑ k, m k * poissonKer η (lam k) E :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
              fun k _ _ => mul_nonneg (hm k) (poissonKer_nonneg hη _ _)
    · rw [Set.indicator_of_notMem hE]
      refine le_of_eq (Finset.sum_eq_zero fun k hk => ?_)
      exact Set.indicator_of_notMem (fun hEk => hE (hPk k hk E hEk)) _
  have h4 : ∑ k ∈ S, m k * (π / 2) = ∫ E in T, ∑ k ∈ S, g k E := by
    rw [← h2]
    exact Finset.sum_congr rfl h1
  have h5 : ∑ k ∈ S, m k = 2 / π * ∑ k ∈ S, m k * (π / 2) := by
    rw [← Finset.sum_mul]
    field_simp
  rw [h5, h4]
  exact mul_le_mul_of_nonneg_left h3 (by positivity)

/-- The Gram-type matrix `Σ_j K_j v_j v_j*` with `K_j ≥ 0` has operator norm at least
`K_k ‖v_k‖²` for each `k`. -/
private lemma poisson_norm_ge {ι m : Type*} [Fintype ι] [Fintype m] [DecidableEq m]
    (K : ι → ℝ) (hK : ∀ k, 0 ≤ K k) (v : ι → m → ℂ) (k : ι) :
    K k * ∑ i, ‖v k i‖ ^ 2 ≤
      ‖∑ j, ((K j : ℝ) : ℂ) • Matrix.vecMulVec (v j) (star (v j))‖ := by
  set B : Matrix m ι ℂ := Matrix.of fun i j => ((Real.sqrt (K j) : ℝ) : ℂ) * v j i with hB
  have hF : ∑ j, ((K j : ℝ) : ℂ) • Matrix.vecMulVec (v j) (star (v j)) = B * Bᴴ := by
    ext i a
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, hB, Matrix.of_apply, Pi.star_apply, star_mul', smul_eq_mul,
      Complex.star_def, Complex.conj_ofReal]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hs : ((Real.sqrt (K j) : ℝ) : ℂ) * ((Real.sqrt (K j) : ℝ) : ℂ) = (K j : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hK j)]
    linear_combination (-(v j i * (starRingEnd ℂ) (v j a))) * hs
  have hnorm : ‖B * Bᴴ‖ = ‖B‖ * ‖B‖ := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self Bᴴ
    rwa [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] at h
  have hcol :
      ‖(EuclideanSpace.equiv m ℂ).symm (B *ᵥ ⇑(EuclideanSpace.single k (1 : ℂ)))‖ ≤ ‖B‖ := by
    have h := Matrix.l2_opNorm_mulVec B (EuclideanSpace.single k (1 : ℂ))
    have h1 : ‖EuclideanSpace.single k (1 : ℂ)‖ = 1 := by simp
    rwa [h1, mul_one] at h
  have hsq : ‖(EuclideanSpace.equiv m ℂ).symm (B *ᵥ ⇑(EuclideanSpace.single k (1 : ℂ)))‖ ^ 2 =
      K k * ∑ i, ‖v k i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hB, mul_pow, Real.sq_sqrt (hK k)]
  rw [hF, hnorm, ← hsq, sq]
  exact mul_self_le_mul_self (norm_nonneg _) hcol

/-- Lemma 4.2 [uv:lem:poisson], (4.2) [uv:eq:poisson]: heavy atoms of `Σ_k p_k δ_{λ_k}` with
`λ_k ∈ J = [c, d]`, against the smoothing `f(E) = Σ_k p_k η/((λ_k - E)² + η²)` on
`J + [-η, η]`. -/
theorem poisson_smoothing {ι : Type*} [Fintype ι] (lam p : ι → ℝ) (hp : ∀ k, 0 ≤ p k)
    {η h : ℝ} (hη : 0 < η) (hh : 0 < h) (c d : ℝ) :
    ∑ k ∈ univ.filter (fun k => lam k ∈ Set.Icc c d ∧ h < p k), p k ≤
      2 / π * ∫ E in Set.Icc (c - η) (d + η),
        Set.indicator {E | h / (2 * η) < ∑ k, p k * poissonKer η (lam k) E}
          (fun E => ∑ k, p k * poissonKer η (lam k) E) E := by
  have _ := hh
  refine poisson_core lam p hp hη c d _ (fun k hk => (Finset.mem_filter.mp hk).2.1) _ ?_ ?_
  · exact measurableSet_lt measurable_const
      (continuous_finsetSum _ fun k _ =>
        continuous_const.mul (continuous_poissonKer hη _)).measurable
  · intro k hk E hE
    have hk' := (Finset.mem_filter.mp hk).2.2
    have hK := poissonKer_ge hη hE
    change h / (2 * η) < ∑ j, p j * poissonKer η (lam j) E
    calc h / (2 * η) < p k * (1 / (2 * η)) := by
          rw [mul_one_div]
          exact div_lt_div_of_pos_right hk' (by positivity)
      _ ≤ p k * poissonKer η (lam k) E := mul_le_mul_of_nonneg_left hK (hp k)
      _ ≤ ∑ j, p j * poissonKer η (lam j) E :=
          Finset.single_le_sum (f := fun j => p j * poissonKer η (lam j) E)
            (fun j _ => mul_nonneg (hp j) (poissonKer_nonneg hη _ _)) (Finset.mem_univ k)

/-- Lemma 4.2 [uv:lem:poisson], matrix form (4.3) [uv:eq:matrix-poisson]: atoms `v_k v_k*` of
mass `‖v_k‖²`, against `F(E) = Σ_k η/((λ_k - E)² + η²) v_k v_k*` in the operator norm. -/
theorem poisson_smoothing_matrix {ι m : Type*} [Fintype ι] [Fintype m] [DecidableEq m]
    (lam : ι → ℝ) (v : ι → m → ℂ) {η h : ℝ} (hη : 0 < η) (hh : 0 < h) (c d : ℝ) :
    ∑ k ∈ univ.filter (fun k => lam k ∈ Set.Icc c d ∧ h < ∑ i, ‖v k i‖ ^ 2),
        ∑ i, ‖v k i‖ ^ 2 ≤
      2 / π * ∫ E in Set.Icc (c - η) (d + η),
        Set.indicator
          {E | h / (2 * η) <
            ‖∑ k, ((poissonKer η (lam k) E : ℝ) : ℂ) • Matrix.vecMulVec (v k) (star (v k))‖}
          (fun E => (∑ k, ((poissonKer η (lam k) E : ℝ) : ℂ) •
            Matrix.vecMulVec (v k) (star (v k))).trace.re) E := by
  have htr : ∀ E : ℝ, (∑ k, ((poissonKer η (lam k) E : ℝ) : ℂ) •
      Matrix.vecMulVec (v k) (star (v k))).trace.re =
        ∑ k, (∑ i, ‖v k i‖ ^ 2) * poissonKer η (lam k) E := by
    intro E
    rw [Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.trace_smul, Matrix.trace_vecMulVec]
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, Complex.re_sum, smul_eq_mul, Complex.re_ofReal_mul,
      Complex.ofReal_re]
    rw [mul_comm]
  have hcont : Continuous fun E : ℝ =>
      ‖∑ k, ((poissonKer η (lam k) E : ℝ) : ℂ) • Matrix.vecMulVec (v k) (star (v k))‖ :=
    continuous_norm.comp (continuous_finsetSum _ fun k _ =>
      (Complex.continuous_ofReal.comp (continuous_poissonKer hη _)).smul continuous_const)
  have _ := hh
  have hm0 : ∀ k, 0 ≤ ∑ i, ‖v k i‖ ^ 2 := fun k => Finset.sum_nonneg fun i _ => by positivity
  rw [show (fun E : ℝ => (∑ k, ((poissonKer η (lam k) E : ℝ) : ℂ) •
      Matrix.vecMulVec (v k) (star (v k))).trace.re) =
      fun E => ∑ k, (∑ i, ‖v k i‖ ^ 2) * poissonKer η (lam k) E from funext htr]
  refine poisson_core lam (fun k => ∑ i, ‖v k i‖ ^ 2) hm0 hη c d _
    (fun k hk => (Finset.mem_filter.mp hk).2.1) _ ?_ ?_
  · exact measurableSet_lt measurable_const hcont.measurable
  · intro k hk E hE
    have hk' := (Finset.mem_filter.mp hk).2.2
    have hK := poissonKer_ge hη hE
    change h / (2 * η) <
      ‖∑ j, ((poissonKer η (lam j) E : ℝ) : ℂ) • Matrix.vecMulVec (v j) (star (v j))‖
    calc h / (2 * η) < (∑ i, ‖v k i‖ ^ 2) * (1 / (2 * η)) := by
          rw [mul_one_div]
          exact div_lt_div_of_pos_right hk' (by positivity)
      _ ≤ (∑ i, ‖v k i‖ ^ 2) * poissonKer η (lam k) E :=
          mul_le_mul_of_nonneg_left hK (hm0 k)
      _ = poissonKer η (lam k) E * ∑ i, ‖v k i‖ ^ 2 := mul_comm _ _
      _ ≤ _ := poisson_norm_ge (fun j => poissonKer η (lam j) E)
          (fun j => poissonKer_nonneg hη _ _) v k

/-- (4.2) [uv:eq:poisson] for the spectral measure `Σ_k |ψ_k(x)|² δ_{λ_k}` of a coordinate `x`,
whose Poisson smoothing is `Im G_xx(E + iη)`. -/
theorem sum_heavy_le_integral_im_resolventMat {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : n) {η h : ℝ} (hη : 0 < η) (hh : 0 < h)
    (c d : ℝ) :
    ∑ k ∈ univ.filter (fun k => hA.eigenvalues k ∈ Set.Icc c d ∧
        h < ‖hA.eigenvectorBasis k x‖ ^ 2), ‖hA.eigenvectorBasis k x‖ ^ 2 ≤
      2 / π * ∫ E in Set.Icc (c - η) (d + η),
        Set.indicator {E | h / (2 * η) < (resolventMat A (E + η * Complex.I) x x).im}
          (fun E => (resolventMat A (E + η * Complex.I) x x).im) E := by
  have hfun : ∀ E : ℝ, (resolventMat A (E + η * Complex.I) x x).im =
      ∑ k, ‖hA.eigenvectorBasis k x‖ ^ 2 * poissonKer η (hA.eigenvalues k) E := by
    intro E
    rw [im_resolventMat_diag hA E hη.ne' x]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold poissonKer
    ring
  refine le_of_le_of_eq (poisson_smoothing hA.eigenvalues
    (fun k => ‖hA.eigenvectorBasis k x‖ ^ 2) (fun k => by positivity) hη hh c d) ?_
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun E _ => ?_
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, hfun]

/-- A unit vector with localization length `ℓ(ψ) < r` has total mass `> 1/4` on the coordinates
of mass `> 1/(4r)`: a cyclic interval of length `ℓ(ψ)` carries mass `≥ 1/2`, and its coordinates
of mass `≤ 1/(4r)` carry at most `ℓ(ψ) / (4r) < 1/4`. -/
private lemma poisson_heavy_mass {W L : ℕ} (ψ : Fin L × Fin W → ℂ) (hψ : ∑ x, ‖ψ x‖ ^ 2 = 1)
    {r : ℝ} (hr : 0 < r) (hl : (ell W L ψ : ℝ) < r) :
    1 ≤ 4 * ∑ x, Set.indicator {t : ℝ | 1 / (4 * r) < t} (fun t => t) (‖ψ x‖ ^ 2) := by
  have hne : Nonempty (Fin L × Fin W) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    simp at hψ
  obtain ⟨x0⟩ := hne
  set N := L * W with hNdef
  have hN : 0 < N := (finProdFinEquiv x0).pos
  set p : Fin N → ℝ := fun i => ‖ψ (finProdFinEquiv.symm i)‖ ^ 2 with hp
  have hell : ell W L ψ = ellMass N p := rfl
  have hsum : ∑ i, p i = 1 := by
    rw [← hψ]
    exact Equiv.sum_comp finProdFinEquiv.symm (fun x => ‖ψ x‖ ^ 2)
  obtain ⟨x, hx⟩ := exists_mass_ellMass hN p (by rw [hsum]; norm_num)
  have hcard : (cycInterval N x (ellMass N p)).card = ellMass N p :=
    card_cycInterval N x _ (ellMass_le N p)
  have hpt : ∀ i, p i ≤
      Set.indicator {t : ℝ | 1 / (4 * r) < t} (fun t => t) (p i) + 1 / (4 * r) := by
    intro i
    by_cases hi : 1 / (4 * r) < p i
    · rw [Set.indicator_of_mem (show p i ∈ {t : ℝ | 1 / (4 * r) < t} from hi)]
      have : (0 : ℝ) < 1 / (4 * r) := by positivity
      linarith
    · rw [Set.indicator_of_notMem (show p i ∉ {t : ℝ | 1 / (4 * r) < t} from hi)]
      linarith [not_lt.mp hi]
  have h1 : 1 / 2 ≤ ∑ i ∈ cycInterval N x (ellMass N p),
      (Set.indicator {t : ℝ | 1 / (4 * r) < t} (fun t => t) (p i) + 1 / (4 * r)) :=
    hx.trans (Finset.sum_le_sum fun i _ => hpt i)
  rw [Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul] at h1
  have h2 : ∑ i ∈ cycInterval N x (ellMass N p),
      Set.indicator {t : ℝ | 1 / (4 * r) < t} (fun t => t) (p i) ≤
      ∑ i, Set.indicator {t : ℝ | 1 / (4 * r) < t} (fun t => t) (p i) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ =>
      Set.indicator_nonneg (fun t ht => le_trans (by positivity) (le_of_lt ht)) _
  have h3 : ∑ i, Set.indicator {t : ℝ | 1 / (4 * r) < t} (fun t => t) (p i) =
      ∑ x, Set.indicator {t : ℝ | 1 / (4 * r) < t} (fun t => t) (‖ψ x‖ ^ 2) :=
    Equiv.sum_comp finProdFinEquiv.symm
      (fun x => Set.indicator {t : ℝ | 1 / (4 * r) < t} (fun t => t) (‖ψ x‖ ^ 2))
  have h4 : (ellMass N p : ℝ) * (1 / (4 * r)) < 1 / 4 := by
    rw [hell] at hl
    rw [mul_one_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- First step of the proof of Theorem 2.2 [uv:lem:lower-volume]: on simple spectrum, an
eigenvector with `ℓ(ψ_k) < r` carries mass at least `1/4` on coordinates of mass `> 1/(4r)`. -/
theorem badCount_le_four_mul_heavy {W L : ℕ} {A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hA : A.IsHermitian) (hinj : Function.Injective hA.eigenvalues) (J : Set ℝ) {r : ℝ}
    (hr : 0 < r) :
    (badCount W L A J r : ℝ) ≤
      4 * ∑ k ∈ univ.filter (fun k => hA.eigenvalues k ∈ J), ∑ x,
        Set.indicator {t : ℝ | 1 / (4 * r) < t} (fun t => t) (‖hA.eigenvectorBasis k x‖ ^ 2) := by
  have hn : ∀ k, ∑ x, ‖(⇑(hA.eigenvectorBasis k) : Fin L × Fin W → ℂ) x‖ ^ 2 = 1 := fun k => by
    rw [← EuclideanSpace.norm_sq_eq, OrthonormalBasis.norm_eq_one, one_pow]
  rw [badCount_eq_of_injective hA hinj (fun k => ⇑(hA.eigenvectorBasis k))
    (fun k => hA.mulVec_eigenvectorBasis k) hn J r, Finset.mul_sum]
  calc ((#(univ.filter fun k => hA.eigenvalues k ∈ J ∧
          (ell W L ⇑(hA.eigenvectorBasis k) : ℝ) < r) : ℕ) : ℝ)
      = ∑ k ∈ univ.filter (fun k => hA.eigenvalues k ∈ J ∧
          (ell W L ⇑(hA.eigenvectorBasis k) : ℝ) < r), (1 : ℝ) := by simp
    _ ≤ ∑ k ∈ univ.filter (fun k => hA.eigenvalues k ∈ J ∧
          (ell W L ⇑(hA.eigenvectorBasis k) : ℝ) < r),
          4 * ∑ x, Set.indicator {t : ℝ | 1 / (4 * r) < t} (fun t => t)
            (‖hA.eigenvectorBasis k x‖ ^ 2) :=
        Finset.sum_le_sum fun k hk =>
          poisson_heavy_mass _ (hn k) hr (Finset.mem_filter.mp hk).2.2
    _ ≤ ∑ k ∈ univ.filter (fun k => hA.eigenvalues k ∈ J),
          4 * ∑ x, Set.indicator {t : ℝ | 1 / (4 * r) < t} (fun t => t)
            (‖hA.eigenvectorBasis k x‖ ^ 2) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => ?_
        · intro k hk
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, (Finset.mem_filter.mp hk).2.1⟩
        · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ =>
            Set.indicator_nonneg (fun t ht => le_trans (by positivity) (le_of_lt ht)) _)

end LSBA
