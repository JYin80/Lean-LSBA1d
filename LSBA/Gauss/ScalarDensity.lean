import LSBA.Gauss.LineDecomp
import LSBA.Spectral.Resolvent

/-!
# Scalar density bounds and almost-sure invertibility

The scalar Gaussian density bound for `‖(tc − A)⁻¹‖`, almost-sure invertibility of
`K₀ + c · diag V − z` for GUE blocks, and measurability of the resolvent, used in (8.7)
[eq:c-apriori] and throughout Section 8.2 [sec:upper-conversion].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `s - A` is diagonalized by the unitary of eigenvectors, with diagonal `s - λ_k`. -/
private lemma scalarDensity_sub_eq {k : Type*} [Fintype k] [DecidableEq k] {A : Matrix k k ℂ}
    (hA : A.IsHermitian) (s : ℂ) :
    s • (1 : Matrix k k ℂ) - A =
      (hA.eigenvectorUnitary : Matrix k k ℂ) *
        Matrix.diagonal (fun i => s - (hA.eigenvalues i : ℂ)) *
        (star (hA.eigenvectorUnitary : Matrix k k ℂ)) := by
  have h := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  have hU : (hA.eigenvectorUnitary : Matrix k k ℂ) * (star (hA.eigenvectorUnitary : Matrix k k ℂ))
      = 1 := Unitary.coe_mul_star_self _
  have hD : Matrix.diagonal (fun i => s - (hA.eigenvalues i : ℂ)) =
      s • (1 : Matrix k k ℂ) - Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    rw [Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_sub]
    rfl
  rw [hD, Matrix.mul_sub, Matrix.sub_mul, ← h]
  congr 1
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU]

/-- The inverse of `s - A` is the spectral expression when no eigenvalue equals `s`. -/
private lemma scalarDensity_inv_eq {k : Type*} [Fintype k] [DecidableEq k] {A : Matrix k k ℂ}
    (hA : A.IsHermitian) {s : ℂ} (hs : ∀ i, s - (hA.eigenvalues i : ℂ) ≠ 0) :
    (s • (1 : Matrix k k ℂ) - A)⁻¹ =
      (hA.eigenvectorUnitary : Matrix k k ℂ) *
        Matrix.diagonal (fun i => (s - (hA.eigenvalues i : ℂ))⁻¹) *
        (star (hA.eigenvectorUnitary : Matrix k k ℂ)) := by
  have hU : (hA.eigenvectorUnitary : Matrix k k ℂ) * (star (hA.eigenvectorUnitary : Matrix k k ℂ))
      = 1 := Unitary.coe_mul_star_self _
  have hU' : (star (hA.eigenvectorUnitary : Matrix k k ℂ)) * (hA.eigenvectorUnitary : Matrix k k ℂ)
      = 1 := Unitary.coe_star_mul_self _
  refine Matrix.inv_eq_right_inv ?_
  rw [scalarDensity_sub_eq hA s]
  calc _ = (hA.eigenvectorUnitary : Matrix k k ℂ) *
          (Matrix.diagonal (fun i => s - (hA.eigenvalues i : ℂ)) *
            Matrix.diagonal (fun i => (s - (hA.eigenvalues i : ℂ))⁻¹)) *
          (star (hA.eigenvectorUnitary : Matrix k k ℂ)) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (star (hA.eigenvectorUnitary : Matrix k k ℂ)), hU', Matrix.one_mul]
    _ = 1 := by
        rw [Matrix.diagonal_mul_diagonal]
        have : (fun i => (s - (hA.eigenvalues i : ℂ)) * (s - (hA.eigenvalues i : ℂ))⁻¹) =
            fun _ => (1 : ℂ) := by
          funext i
          exact mul_inv_cancel₀ (hs i)
        rw [this, Matrix.diagonal_one, Matrix.mul_one, hU]

/-- If `s` stays at distance at least `1/h` from every eigenvalue, then `‖(s - A)⁻¹‖ ≤ h`. -/
private lemma scalarDensity_norm_inv_le {k : Type*} [Fintype k] [DecidableEq k] {A : Matrix k k ℂ}
    (hA : A.IsHermitian) (s : ℝ) {h : ℝ} (hh : 0 < h)
    (hs : ∀ i, 1 / h ≤ |s - hA.eigenvalues i|) :
    ‖((s : ℂ) • (1 : Matrix k k ℂ) - A)⁻¹‖ ≤ h := by
  have hne : ∀ i, (s : ℂ) - (hA.eigenvalues i : ℂ) ≠ 0 := by
    intro i hi
    have h1 : s - hA.eigenvalues i = 0 := by exact_mod_cast hi
    have h2 := hs i
    rw [h1, abs_zero] at h2
    have : 0 < 1 / h := by positivity
    linarith
  rw [scalarDensity_inv_eq hA hne]
  rw [Matrix.mul_assoc, CStarRing.norm_coe_unitary_mul,
    show star (hA.eigenvectorUnitary : Matrix k k ℂ) = ((star hA.eigenvectorUnitary : unitary _) :
      Matrix k k ℂ) from Unitary.coe_star.symm,
    CStarRing.norm_mul_coe_unitary, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg hh.le).mpr fun i => ?_
  have hpos : 0 < |s - hA.eigenvalues i| := lt_of_lt_of_le (by positivity) (hs i)
  have : ‖((s : ℂ) - (hA.eigenvalues i : ℂ))⁻¹‖ = (|s - hA.eigenvalues i|)⁻¹ := by
    rw [norm_inv, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [this]
  calc (|s - hA.eigenvalues i|)⁻¹ ≤ (1 / h)⁻¹ := inv_anti₀ (by positivity) (hs i)
    _ = h := by rw [one_div, inv_inv]

/-- The standard Gaussian measure of an interval of length `2r` is at most `2r / √(2π)`. -/
private lemma scalarDensity_gaussianReal_Ioo_le (x r : ℝ) :
    gaussianReal 0 1 (Set.Ioo (x - r) (x + r)) ≤ ENNReal.ofReal (2 * r / Real.sqrt (2 * π)) := by
  rw [gaussianReal_apply 0 one_ne_zero]
  have hpdf : ∀ y : ℝ, gaussianPDF 0 1 y ≤ ENNReal.ofReal ((Real.sqrt (2 * π))⁻¹) := by
    intro y
    rw [gaussianPDF_def]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one]
    have : Real.exp (-(y - 0) ^ 2 / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ (y - 0) ^ 2 := sq_nonneg _
      linarith
    have hp : 0 ≤ (Real.sqrt (2 * π))⁻¹ := by positivity
    calc (Real.sqrt (2 * π))⁻¹ * Real.exp (-(y - 0) ^ 2 / 2)
        ≤ (Real.sqrt (2 * π))⁻¹ * 1 := mul_le_mul_of_nonneg_left this hp
      _ = _ := mul_one _
  calc ∫⁻ y in Set.Ioo (x - r) (x + r), gaussianPDF 0 1 y
      ≤ ∫⁻ y in Set.Ioo (x - r) (x + r), ENNReal.ofReal ((Real.sqrt (2 * π))⁻¹) :=
        lintegral_mono hpdf
    _ = ENNReal.ofReal ((Real.sqrt (2 * π))⁻¹) * volume (Set.Ioo (x - r) (x + r)) :=
        setLIntegral_const _ _
    _ = ENNReal.ofReal (2 * r / Real.sqrt (2 * π)) := by
        rw [Real.volume_Ioo, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [show x + r - (x - r) = 2 * r by ring]
        field_simp

/-- Scalar density bound: for Hermitian `A` and `t ~ N(0, 1)`,
`P(‖(t c - A)^{-1}‖ > h) ≤ 2 |k| / (h |c| √(2π))`. -/
theorem gaussianReal_norm_inv_gt_le {k : Type*} [Fintype k] [DecidableEq k] (A : Matrix k k ℂ)
    (hA : A.IsHermitian) {c h : ℝ} (hc : c ≠ 0) (hh : 0 < h) :
    gaussianReal 0 1 {t | h < ‖(((t * c : ℝ) : ℂ) • (1 : Matrix k k ℂ) - A)⁻¹‖} ≤
      ENNReal.ofReal (2 * Fintype.card k / (h * |c| * Real.sqrt (2 * π))) := by
  set r : ℝ := 1 / (h * |c|) with hr
  have hcpos : 0 < |c| := abs_pos.mpr hc
  have hsub : {t : ℝ | h < ‖(((t * c : ℝ) : ℂ) • (1 : Matrix k k ℂ) - A)⁻¹‖} ⊆
      ⋃ i : k, Set.Ioo (hA.eigenvalues i / c - r) (hA.eigenvalues i / c + r) := by
    intro t ht
    by_contra hnot
    have hall : ∀ i : k, 1 / h ≤ |t * c - hA.eigenvalues i| := by
      intro i
      by_contra hlt
      rw [not_le] at hlt
      apply hnot
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      have habs : |t - hA.eigenvalues i / c| = |t * c - hA.eigenvalues i| / |c| := by
        rw [← abs_div]
        congr 1
        field_simp
      have hlt' : |t - hA.eigenvalues i / c| < r := by
        rw [habs, hr, div_lt_iff₀ hcpos]
        calc |t * c - hA.eigenvalues i| < 1 / h := hlt
          _ = 1 / (h * |c|) * |c| := by field_simp
      rw [abs_lt] at hlt'
      exact ⟨by linarith [hlt'.1], by linarith [hlt'.2]⟩
    have hle := scalarDensity_norm_inv_le hA (t * c) hh hall
    exact absurd ht (not_lt.mpr hle)
  calc gaussianReal 0 1 {t : ℝ | h < ‖(((t * c : ℝ) : ℂ) • (1 : Matrix k k ℂ) - A)⁻¹‖}
      ≤ gaussianReal 0 1 (⋃ i : k, Set.Ioo (hA.eigenvalues i / c - r) (hA.eigenvalues i / c + r)) :=
        measure_mono hsub
    _ ≤ ∑ i : k, gaussianReal 0 1 (Set.Ioo (hA.eigenvalues i / c - r) (hA.eigenvalues i / c + r)) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : k, ENNReal.ofReal (2 * r / Real.sqrt (2 * π)) :=
        Finset.sum_le_sum fun i _ => scalarDensity_gaussianReal_Ioo_le _ _
    _ = ENNReal.ofReal (2 * Fintype.card k / (h * |c| * Real.sqrt (2 * π))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hr]
        field_simp

/-- Each entry of a GUE block is a measurable function of the sample. -/
private lemma scalarDensity_measurable_gueBlock_apply {W n : ℕ} (a : Fin n) (α β : Fin W) :
    Measurable fun ω : Ω W n => gueBlock W n ω a α β := by
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs
  · fun_prop
  · fun_prop
  · fun_prop

/-- The matrix `K₀ + c · diag V(ω) - z` is a measurable function of the sample. -/
private lemma scalarDensity_measurable_mat {W n : ℕ}
    (K₀ : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) (c : ℝ) (z : ℂ) :
    Measurable fun ω : Ω W n => K₀ + (c : ℂ) • blockDiagOp (gueBlock W n ω) -
      z • (1 : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) := by
  refine Measurable.of_eval_matrix _ fun p q => ?_
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, blockDiagOp, Matrix.of_apply,
    smul_eq_mul]
  by_cases h : p.1 = q.1
  · simp only [h, ite_true]
    have := scalarDensity_measurable_gueBlock_apply (W := W) (n := n) q.1 p.2 q.2
    fun_prop
  · simp only [h, ite_false]
    fun_prop

/-- Adding `s` times the identity to every block adds `s` times the identity to `diag V`. -/
private lemma scalarDensity_blockDiagOp_add {W n : ℕ} (V : Fin n → Matrix (Fin W) (Fin W) ℂ)
    (s : ℂ) :
    blockDiagOp (fun a => V a + s • (1 : Matrix (Fin W) (Fin W) ℂ)) =
      blockDiagOp V + s • (1 : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) := by
  ext ⟨a, α⟩ ⟨b, β⟩
  by_cases hab : a = b
  · subst hab
    by_cases hαβ : α = β
    · subst hαβ
      simp [blockDiagOp]
    · simp [blockDiagOp, hαβ]
  · simp [blockDiagOp, hab]

/-- Along the line `ω + t • scalarDir W n univ`, the determinant is almost surely nonzero in `t`:
it is a monic polynomial in an affine function of `t`. -/
private lemma scalarDensity_det_line_ae {W n : ℕ} (hW : 1 ≤ W) (hn : 1 ≤ n)
    (K₀ : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) {c : ℝ} (hc : c ≠ 0) (z : ℂ)
    (ω : Ω W n) :
    ∀ᵐ t ∂(gaussianReal 0 1),
      (K₀ + (c : ℂ) • blockDiagOp (gueBlock W n (ω + t • scalarDir W n Finset.univ)) -
        z • (1 : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ)).det ≠ 0 := by
  set M : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ :=
    K₀ + (c : ℂ) • blockDiagOp (gueBlock W n ω) -
      z • (1 : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) with hM
  set a : ℝ := (W : ℝ) * Real.sqrt n with ha
  have hWp : (0 : ℝ) < W := by exact_mod_cast hW
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hap : a ≠ 0 := by positivity
  have hexpr : ∀ t : ℝ,
      K₀ + (c : ℂ) • blockDiagOp (gueBlock W n (ω + t • scalarDir W n Finset.univ)) -
        z • (1 : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) =
      M + (((c * (t / a) : ℝ)) : ℂ) • (1 : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) := by
    intro t
    have h1 : gueBlock W n (ω + t • scalarDir W n Finset.univ) =
        fun b => gueBlock W n ω b + (((t / a : ℝ)) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) := by
      funext b
      rw [gueBlock_add_smul_scalarDir]
      simp [ha]
    rw [h1, scalarDensity_blockDiagOp_add, hM, smul_add, smul_smul]
    push_cast
    abel
  have hpoly : (-M).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hfin : {x : ℂ | (-M).charpoly.IsRoot x}.Finite := Polynomial.finite_setOfPred_isRoot hpoly
  let f : ℝ → ℂ := fun t => (((c * (t / a) : ℝ)) : ℂ)
  have hf : Function.Injective f := by
    intro t t' h
    have h' : c * (t / a) = c * (t' / a) := Complex.ofReal_injective h
    have := mul_left_cancel₀ hc h'
    exact (div_left_inj' hap).mp this
  have hfin' : (f ⁻¹' {x : ℂ | (-M).charpoly.IsRoot x}).Finite := hfin.preimage hf.injOn
  have hnull : gaussianReal 0 1 (f ⁻¹' {x : ℂ | (-M).charpoly.IsRoot x}) = 0 :=
    gaussianReal_absolutelyContinuous 0 one_ne_zero (hfin'.measure_zero volume)
  rw [measure_eq_zero_iff_ae_notMem] at hnull
  filter_upwards [hnull] with t ht
  rw [hexpr t]
  intro h0
  apply ht
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Polynomial.IsRoot.def]
  rw [Matrix.eval_charpoly]
  rw [← h0]
  congr 1
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, sub_neg_eq_add, add_comm]

/-- A fixed `z` is almost surely not an eigenvalue of `K₀ + c · diag(V_a)`. -/
theorem ae_det_ne_zero_gueBlock {W n : ℕ} (K₀ : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ)
    {c : ℝ} (hc : c ≠ 0) (z : ℂ) :
    ∀ᵐ ω ∂(μ W n), (K₀ + (c : ℂ) • blockDiagOp (gueBlock W n ω) -
      z • (1 : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ)).det ≠ 0 := by
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · exact ae_of_all _ fun ω => by simp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ae_of_all _ fun ω => by simp
  have he : ∑ p, scalarDir W n Finset.univ p ^ 2 = 1 :=
    sum_sq_scalarDir hW (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
  set Bad : Set (Ω W n) := {ω | (K₀ + (c : ℂ) • blockDiagOp (gueBlock W n ω) -
      z • (1 : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ)).det = 0} with hBad_def
  have hBad : MeasurableSet Bad :=
    ((continuous_id.matrix_det).measurable.comp (scalarDensity_measurable_mat K₀ c z))
      (measurableSet_singleton 0)
  have hline := lintegral_stdGauss_line (scalarDir W n Finset.univ) he
    (F := Bad.indicator 1) (measurable_one.indicator hBad)
  rw [ae_iff]
  have hset : {ω | ¬ (K₀ + (c : ℂ) • blockDiagOp (gueBlock W n ω) -
      z • (1 : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ)).det ≠ 0} = Bad := by
    simp [hBad_def]
  rw [hset, ← lintegral_indicator_one hBad]
  change ∫⁻ ω, Bad.indicator 1 ω ∂(stdGauss (Fin n × Fin W × Fin W)) = 0
  rw [hline]
  have hinner : ∀ ω : Ω W n, ∫⁻ t, Bad.indicator 1
      (ω - (∑ i, ω i * scalarDir W n Finset.univ i) • scalarDir W n Finset.univ +
        t • scalarDir W n Finset.univ) ∂(gaussianReal 0 1) = 0 := fun ω => by
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [scalarDensity_det_line_ae hW hn K₀ hc z
      (ω - (∑ i, ω i * scalarDir W n Finset.univ i) • scalarDir W n Finset.univ)] with t ht
    exact Set.indicator_of_notMem (by simpa [hBad_def] using ht) _
  simp [hinner]

/-- The matrix inverse is measurable. -/
private lemma scalarDensity_measurable_inv {m : Type*} [Fintype m] [DecidableEq m] :
    Measurable fun A : Matrix m m ℂ => A⁻¹ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  have hd : Measurable fun A : Matrix m m ℂ => A.det :=
    (continuous_id.matrix_det).measurable
  have ha : Measurable fun A : Matrix m m ℂ => A.adjugate i j :=
    (continuous_id.matrix_adjugate).measurable.eval_matrix
  exact (hd.inv).mul ha

theorem measurable_resolventMat_gueBlock {W n : ℕ}
    (K₀ : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) (c : ℝ) (z : ℂ) :
    Measurable fun ω : Ω W n => resolventMat (K₀ + (c : ℂ) • blockDiagOp (gueBlock W n ω)) z := by
  have h := scalarDensity_measurable_inv.comp (scalarDensity_measurable_mat K₀ c z)
  exact h

end LSBA
