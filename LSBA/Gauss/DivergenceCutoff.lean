import LSBA.Gauss.DivergenceMoment

/-!
# Gaussian divergence of a cut field

For a `C^∞` cutoff `0 ≤ χ ≤ 1` of compact support with `Σ_i (∂_i χ)² ≤ l` and a field `Y`
that is `C^∞` on an open set containing the support of `χ`, the cut field `χ Y` is `C^∞`,
allows Gaussian integration by parts, and
`𝔼 |δ_G(χ Y)|² ≤ (1 + 2l) a + 2b` whenever `Σ_i Y_i² ≤ a` and `Σ_{i,j} (∂_j Y_i)² ≤ b` on the
support: the product rule absorbs the cutoff derivative into the size term, as in (10.9)
[eq:c-input-divergence], through (10.4) [up:eq:lift-divergence-reduction].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

noncomputable section

namespace LSBA

/-- (10.9) [eq:c-input-divergence] in standard coordinates. -/
theorem cutField_divergence_le {ι : Type*} [Fintype ι] [DecidableEq ι] {χ : (ι → ℝ) → ℝ}
    {Y : (ι → ℝ) → ι → ℝ} {N : Set (ι → ℝ)} {l a b : ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hgrad : ∀ x, ∑ i, (fderiv ℝ χ x (Pi.single i 1)) ^ 2 ≤ l) (hN : IsOpen N)
    (hsub : tsupport χ ⊆ N) (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y N)
    (ha : ∀ x ∈ tsupport χ, ∑ i, Y x i ^ 2 ≤ a)
    (hb : ∀ x ∈ tsupport χ, ∑ i, ∑ j, (fderiv ℝ Y x (Pi.single j 1) i) ^ 2 ≤ b) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x • Y x) ∧ IBPAdmissible (fun x => χ x • Y x) ∧
      ∫⁻ x, ‖gaussDiv (fun y => χ y • Y y) x‖ₑ ^ 2 ∂(stdGauss ι) ≤
        ENNReal.ofReal ((1 + 2 * l) * a + 2 * b) := by
  classical
  have hle1 : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hle2 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
  -- the cut field vanishes near every point outside the support of `χ`
  have hzero : ∀ x, x ∉ tsupport χ →
      (fun y => χ y • Y y) =ᶠ[nhds x] fun _ => (0 : ι → ℝ) := by
    intro x hx
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
    have : χ y = 0 := image_eq_zero_of_notMem_tsupport hy
    simp [this]
  have hZ : ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x • Y x) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport χ
    · exact hχ.contDiffAt.smul (hY.contDiffAt (hN.mem_nhds (hsub hx)))
    · exact (contDiffAt_const (c := (0 : ι → ℝ))).congr_of_eventuallyEq (hzero x hx)
  have hZ1 : ContDiff ℝ 1 (fun x => χ x • Y x) := hZ.of_le hle1
  have hZ2 : ContDiff ℝ 2 (fun x => χ x • Y x) := hZ.of_le hle2
  have hcs : HasCompactSupport (fun x => χ x • Y x) := hχc.smul_right
  -- the cut field and its first two derivatives are bounded, hence of polynomial growth
  have hpg0 : PolyGrowth (fun x => χ x • Y x) := by
    obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hZ.continuous
    exact ⟨C, 0, fun x => by simpa using hC x⟩
  have hpg1 : PolyGrowth (fderiv ℝ (fun x => χ x • Y x)) := by
    obtain ⟨C, hC⟩ := (hcs.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
      (hZ1.continuous_fderiv one_ne_zero)
    exact ⟨C, 0, fun x => by simpa using hC x⟩
  have hpg2 : PolyGrowth (fderiv ℝ (fderiv ℝ (fun x => χ x • Y x))) := by
    obtain ⟨C, hC⟩ := (hcs.iteratedFDeriv (𝕜 := ℝ) 2).exists_bound_of_continuous
      (hZ.continuous_iteratedFDeriv (m := 2) (by simp))
    refine ⟨C, 0, fun x => ?_⟩
    have h1 : ‖iteratedFDeriv ℝ 1 (fderiv ℝ (fun x => χ x • Y x)) x‖ =
        ‖iteratedFDeriv ℝ 2 (fun x => χ x • Y x) x‖ := norm_iteratedFDeriv_fderiv
    rw [norm_iteratedFDeriv_one] at h1
    simpa [h1] using hC x
  refine ⟨hZ, ibpAdmissible_of_contDiff hZ1 hpg0 hpg1, ?_⟩
  refine (lintegral_gaussDiv_sq_le hZ2 hpg0 hpg1 hpg2).trans ?_
  calc ∫⁻ x, ENNReal.ofReal (∑ i, (fun y => χ y • Y y) x i ^ 2 + ∑ i, ∑ j,
          (fderiv ℝ (fun y => χ y • Y y) x (Pi.single j 1) i) ^ 2) ∂(stdGauss ι)
      ≤ ∫⁻ _, ENNReal.ofReal ((1 + 2 * l) * a + 2 * b) ∂(stdGauss ι) := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ tsupport χ
        · refine ENNReal.ofReal_le_ofReal ?_
          have hYd : DifferentiableAt ℝ Y x :=
            (hY.contDiffAt (hN.mem_nhds (hsub hx))).differentiableAt (by simp)
          have hχd : DifferentiableAt ℝ χ x := hχ.differentiable (by simp) x
          have hd : ∀ i j, fderiv ℝ (fun y => χ y • Y y) x (Pi.single j 1) i =
              χ x * fderiv ℝ Y x (Pi.single j 1) i + fderiv ℝ χ x (Pi.single j 1) * Y x i := by
            intro i j
            rw [fderiv_fun_smul hχd hYd]
            simp
          obtain ⟨hχ0, hχ1⟩ := hχ01 x
          have hχ2 : χ x ^ 2 ≤ 1 := by nlinarith
          have hA0 : 0 ≤ ∑ j, (fderiv ℝ χ x (Pi.single j 1)) ^ 2 :=
            Finset.sum_nonneg fun j _ => sq_nonneg _
          have hB0 : 0 ≤ ∑ i, Y x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
          have hD0 : 0 ≤ ∑ i, ∑ j, (fderiv ℝ Y x (Pi.single j 1) i) ^ 2 :=
            Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
          have hA := hgrad x
          have hB := ha x hx
          have hD := hb x hx
          have hl0 : 0 ≤ l := hA0.trans hA
          have hsize : ∑ i, (fun y => χ y • Y y) x i ^ 2 = χ x ^ 2 * ∑ i, Y x i ^ 2 := by
            simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
          have hder : ∑ i, ∑ j, (fderiv ℝ (fun y => χ y • Y y) x (Pi.single j 1) i) ^ 2 ≤
              2 * χ x ^ 2 * ∑ i, ∑ j, (fderiv ℝ Y x (Pi.single j 1) i) ^ 2 +
                2 * ((∑ j, (fderiv ℝ χ x (Pi.single j 1)) ^ 2) * ∑ i, Y x i ^ 2) := by
            have h1 : ∑ i, ∑ j, (fderiv ℝ (fun y => χ y • Y y) x (Pi.single j 1) i) ^ 2 ≤
                ∑ i, ∑ j, (2 * (χ x ^ 2 * (fderiv ℝ Y x (Pi.single j 1) i) ^ 2) +
                  2 * ((fderiv ℝ χ x (Pi.single j 1)) ^ 2 * Y x i ^ 2)) := by
              refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
              rw [hd i j]
              nlinarith [sq_nonneg (χ x * fderiv ℝ Y x (Pi.single j 1) i -
                fderiv ℝ χ x (Pi.single j 1) * Y x i)]
            refine h1.trans (le_of_eq ?_)
            have hprod : ∑ i, ∑ j, (fderiv ℝ χ x (Pi.single j 1)) ^ 2 * Y x i ^ 2 =
                (∑ j, (fderiv ℝ χ x (Pi.single j 1)) ^ 2) * ∑ i, Y x i ^ 2 := by
              rw [Finset.sum_mul_sum]
              exact Finset.sum_comm
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
            rw [hprod]
            ring
          have hAB : (∑ j, (fderiv ℝ χ x (Pi.single j 1)) ^ 2) * ∑ i, Y x i ^ 2 ≤ l * a :=
            mul_le_mul hA hB hB0 hl0
          rw [hsize]
          nlinarith [mul_le_mul_of_nonneg_right hχ2 hB0, mul_le_mul_of_nonneg_right hχ2 hD0]
        · have h0 : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
          have h1 : fderiv ℝ (fun y => χ y • Y y) x = 0 := by
            rw [(hzero x hx).fderiv_eq]; simp
          simp [h0, h1]
    _ = ENNReal.ofReal ((1 + 2 * l) * a + 2 * b) := by simp

end LSBA
