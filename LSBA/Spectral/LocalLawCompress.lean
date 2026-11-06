import LSBA.Spectral.DeformedLocalLaw
import LSBA.Gauss.Compress

/-!
# The averaged local law for compressions

`Im⟨(Q*VQ − E − B − iη)⁻¹⟩ ≍ 1` with high probability for an isometry `Q` into `W` coordinates, the
form used by (9.48) [us:eq:complement-spectrum] (Appendix G.2 [app:inverse-image-inputs]).
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal Matrix.Norms.L2Operator

noncomputable section
open scoped Classical

namespace LSBA

/-- The imaginary part of the averaged resolvent trace is a measurable function of the matrix. -/
private lemma localLawCompress_measurable_im {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    Measurable fun M : Matrix (Fin n) (Fin n) ℂ => (ntr (resolventMat (M - B) z)).im := by
  have hinv : Measurable fun A : Matrix (Fin n) (Fin n) ℂ => A⁻¹ := by
    refine Measurable.of_eval_matrix _ fun i j => ?_
    simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
    have hd : Measurable fun A : Matrix (Fin n) (Fin n) ℂ => A.det :=
      (continuous_id.matrix_det).measurable
    have ha : Measurable fun A : Matrix (Fin n) (Fin n) ℂ => A.adjugate i j :=
      (continuous_id.matrix_adjugate).measurable.eval_matrix
    exact (hd.inv).mul ha
  have h1 : Measurable fun M : Matrix (Fin n) (Fin n) ℂ => resolventMat (M - B) z := by
    unfold resolventMat
    exact hinv.comp (by fun_prop)
  have h2 : Measurable fun M : Matrix (Fin n) (Fin n) ℂ => ntr (resolventMat (M - B) z) := by
    unfold ntr
    exact measurable_const.mul ((continuous_id.matrix_trace).measurable.comp h1)
  exact Complex.measurable_im.comp h2

/-- Rescaling the two-sided bound `C⁻¹ ≤ t ≤ C` by a factor `c ∈ [1, 2]`. -/
private lemma localLawCompress_real {C c t : ℝ} (hC : 0 < C) (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (h : C⁻¹ ≤ t ∧ t ≤ C) : (2 * C)⁻¹ ≤ c * t ∧ c * t ≤ 2 * C := by
  obtain ⟨hl, hu⟩ := h
  have hCi : 0 < C⁻¹ := inv_pos.2 hC
  have ht : 0 < t := lt_of_lt_of_le hCi hl
  have h1 : (2 * C)⁻¹ ≤ C⁻¹ := by
    rw [mul_inv]; nlinarith
  exact ⟨by nlinarith, by nlinarith⟩

/-- The entries of the GUE matrix are measurable in the sample. -/
private lemma localLawCompress_measurable_entry (n : ℕ) (a b : Fin n) :
    Measurable fun ω : Ω n 1 => gueMat n ω a b := by
  unfold gueMat gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

/-- Rescaling the argument of a resolvent by a positive real `s`. -/
private lemma localLawCompress_resolvent_smul {n : ℕ} {s : ℝ} (hs : 0 < s)
    (V B : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    resolventMat (((s : ℝ) : ℂ) • V - B) z =
      (((s⁻¹ : ℝ) : ℂ)) • resolventMat (V - (((s⁻¹ : ℝ) : ℂ)) • B) ((((s⁻¹ : ℝ) : ℂ)) * z) := by
  have hs' : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hinv : (((s⁻¹ : ℝ) : ℂ)) = ((s : ℝ) : ℂ)⁻¹ := by push_cast; rfl
  unfold resolventMat
  have h : ((s : ℂ) • V - B) - z • (1 : Matrix (Fin n) (Fin n) ℂ) =
      ((s : ℝ) : ℂ) • ((V - (((s⁻¹ : ℝ) : ℂ)) • B) -
        ((((s⁻¹ : ℝ) : ℂ)) * z) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [hinv]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp
  rw [h]
  have hu : IsUnit (((s : ℝ) : ℂ)) := hs'.isUnit
  by_cases hd : IsUnit ((V - (((s⁻¹ : ℝ) : ℂ)) • B -
        ((((s⁻¹ : ℝ) : ℂ)) * z) • (1 : Matrix (Fin n) (Fin n) ℂ))).det
  · have := Matrix.inv_smul' (A := V - (((s⁻¹ : ℝ) : ℂ)) • B -
        ((((s⁻¹ : ℝ) : ℂ)) * z) • (1 : Matrix (Fin n) (Fin n) ℂ)) hu.unit hd
    simp only [Units.smul_def, Units.val_inv_eq_inv_val, IsUnit.unit_spec] at this
    rw [hinv] at this ⊢
    exact this
  · have hd' : ¬ IsUnit ((((s : ℝ) : ℂ)) • (V - (((s⁻¹ : ℝ) : ℂ)) • B -
        ((((s⁻¹ : ℝ) : ℂ)) * z) • (1 : Matrix (Fin n) (Fin n) ℂ))).det := by
      rw [Matrix.det_smul, IsUnit.mul_iff]
      tauto
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hd, Matrix.nonsing_inv_apply_not_isUnit _ hd']
    simp

/-- The class `𝓑(ε)` is stable under rescaling by a real `c` with `1 ≤ c ≤ 2`, at the price of
`ε ↦ 2 ε`. -/
private lemma localLawCompress_deformClass_smul {n : ℕ} {ε c : ℝ} {B : Matrix (Fin n) (Fin n) ℂ}
    (hB : DeformClass ε B) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) :
    DeformClass (2 * ε) ((c : ℂ) • B) := by
  obtain ⟨hh, Bs, Bb, hsum, hs, hb⟩ := hB
  have hε : 0 ≤ ε := (norm_nonneg _).trans hs
  refine ⟨?_, (c : ℂ) • Bs, (c : ℂ) • Bb, by rw [hsum, smul_add], ?_, ?_⟩
  · have : ((c : ℂ) • B)ᴴ = (c : ℂ) • B := by
      rw [Matrix.conjTranspose_smul, hh.eq]
      simp
    exact this
  · calc ‖(c : ℂ) • Bs‖ = ‖(c : ℂ)‖ * ‖Bs‖ := norm_smul _ _
      _ ≤ 2 * ε := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
        exact mul_le_mul hc2 hs (norm_nonneg _) (by norm_num)
  · have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast (by linarith : c ≠ 0)
    have hrk : ((c : ℂ) • Bb).rank = Bb.rank :=
      Matrix.rank_smul_of_mem_nonZeroDivisors Bb (mem_nonZeroDivisors_of_ne_zero hc0)
    rw [hrk]
    have hcard : (0 : ℝ) ≤ Fintype.card (Fin n) := Nat.cast_nonneg _
    nlinarith

/-- Bounds on the compression scale `s = √(n/W)`: `s ≥ n/W`, `1/2 ≤ s ≤ 1`. -/
private lemma localLawCompress_scale {W n : ℕ} {κ₀ : ℝ} (hκ₀' : κ₀ < 2) (hnW : n ≤ W)
    (hW : 0 < W) (hcomp : ((W - n : ℕ) : ℝ) ≤ κ₀ * W / 4) :
    1 - κ₀ / 4 ≤ (n : ℝ) / W ∧ (n : ℝ) / W ≤ Real.sqrt ((n : ℝ) / W) ∧
      Real.sqrt ((n : ℝ) / W) ≤ 1 ∧ 1 / 2 ≤ Real.sqrt ((n : ℝ) / W) := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hsub : ((W - n : ℕ) : ℝ) = (W : ℝ) - n := by rw [Nat.cast_sub hnW]
  have h1 : 1 - κ₀ / 4 ≤ (n : ℝ) / W := by
    rw [hsub] at hcomp
    rw [le_div_iff₀ hW']
    nlinarith
  have hq0 : 0 ≤ (n : ℝ) / W := by positivity
  have hq1 : (n : ℝ) / W ≤ 1 := by
    rw [div_le_one hW']; exact_mod_cast hnW
  have h2 : (n : ℝ) / W ≤ Real.sqrt ((n : ℝ) / W) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  refine ⟨h1, h2, ?_, ?_⟩
  · calc Real.sqrt ((n : ℝ) / W) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hq1
      _ = 1 := Real.sqrt_one
  · have : (1 : ℝ) / 2 ≤ (n : ℝ) / W := by linarith
    linarith

/-- The dimension adapter of Appendix G.2.2 [app:inverse-image-spectrum] for
(9.48) [us:eq:complement-spectrum]: for the compression `Q^* V Q` of the `W × W` GUE matrix to
an `n`-dimensional isometry with `W - n ≤ κ₀ W / 4`, a deformation in the class of Lemma G.1
[us:lem:local-law], `|E| ≤ 2 - κ₀` and `W^{-1+δ} ≤ η ≤ 1`, the averaged comparison
`C⁻¹ ≤ Im ⟨(Q^* V Q - E - B - iη)⁻¹⟩ ≤ C` holds with probability `≥ 1 - W^{-D}`. -/
theorem localLaw_avg_asymp_compress (κ₀ : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 1 ≤ C ∧ ∀ ε δ D : ℝ, 0 < ε → ε ≤ ε₀ → 0 < δ → 0 < D →
      ∃ W₀ : ℕ, ∀ W n : ℕ, W₀ ≤ W → n ≤ W → ((W - n : ℕ) : ℝ) ≤ κ₀ * W / 4 →
        ∀ (Q : Matrix (Fin W) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) (E η : ℝ),
        Qᴴ * Q = 1 → DeformClass ε B → |E| ≤ 2 - κ₀ → (W : ℝ) ^ (-1 + δ) ≤ η → η ≤ 1 →
        μ W 1 {ω | ¬ (C⁻¹ ≤
              (ntr (resolventMat (Qᴴ * gueMat W ω * Q - B) (E + η * Complex.I))).im ∧
            (ntr (resolventMat (Qᴴ * gueMat W ω * Q - B) (E + η * Complex.I))).im ≤ C)} ≤
          ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  obtain ⟨ε₁, C₁, hε₁, hC₁, hcore⟩ := localLaw_avg_asymp (κ₀ / 2) 2 (by linarith) (by linarith)
    (by norm_num)
  have hC₁0 : 0 < C₁ := by linarith
  refine ⟨ε₁ / 2, 2 * C₁, by positivity, by linarith, ?_⟩
  intro ε δ D hε hεε₀ hδ hD
  set δ₁ : ℝ := min δ 1 with hδ₁
  have hδ₁0 : 0 < δ₁ := lt_min hδ one_pos
  have hδ₁1 : δ₁ ≤ 1 := min_le_right _ _
  have hδ₁δ : δ₁ ≤ δ := min_le_left _ _
  obtain ⟨n₀, hn₀⟩ := hcore (2 * ε) (δ₁ / 2) (D + 1) (by positivity) (by linarith) (by positivity)
    (by linarith)
  have hev1 : ∀ᶠ W : ℕ in Filter.atTop, (2 : ℝ) ≤ (W : ℝ) ^ (δ₁ / 2) := by
    have := (tendsto_rpow_atTop (show 0 < δ₁ / 2 by positivity)).comp tendsto_natCast_atTop_atTop
    exact this.eventually (Filter.eventually_ge_atTop 2)
  obtain ⟨W₁, hW₁⟩ := Filter.eventually_atTop.mp hev1
  obtain ⟨W₂, hW₂⟩ := Filter.eventually_atTop.mp
    (tendsto_natCast_atTop_atTop.eventually (Filter.eventually_ge_atTop ((2 : ℝ) ^ (D + 1))))
  refine ⟨max (max (2 * n₀) 2) (max W₁ W₂), ?_⟩
  intro W n hWW hnW hcomp Q B E η hQ hB hE hηlow hη1
  have hW2 : 2 ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hWW
  have hn₀W : 2 * n₀ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hWW
  have hW₁W : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hWW
  have hW₂W : W₂ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hWW
  have hW0 : 0 < W := by omega
  have hWr : (1 : ℝ) < W := by exact_mod_cast (by omega : 1 < W)
  have hWr0 : (0 : ℝ) < W := by linarith
  obtain ⟨hs1, hs2, hs3, hs4⟩ := localLawCompress_scale hκ₀' hnW hW0 hcomp
  set s : ℝ := Real.sqrt ((n : ℝ) / W) with hs
  have hs0 : 0 < s := by linarith
  have hnhalf : (W : ℝ) / 2 ≤ n := by
    have : (1 : ℝ) / 2 ≤ (n : ℝ) / W := by linarith
    rw [div_le_div_iff₀ (by norm_num) hWr0] at this
    linarith
  have hnr0 : (0 : ℝ) < n := by linarith
  have hn0 : 0 < n := by exact_mod_cast hnr0
  have hn₀n : n₀ ≤ n := by
    have : (2 * n₀ : ℝ) ≤ W := by exact_mod_cast hn₀W
    have : (n₀ : ℝ) ≤ n := by linarith
    exact_mod_cast this
  -- parameters of the rescaled problem
  set c : ℝ := s⁻¹ with hc
  have hc1 : 1 ≤ c := by rw [hc]; exact (one_le_inv₀ hs0).2 hs3
  have hc2 : c ≤ 2 := by
    rw [hc, inv_le_comm₀ hs0 (by norm_num)]; linarith
  have hc0 : 0 < c := by linarith
  have hB' : DeformClass (2 * ε) ((c : ℂ) • B) := localLawCompress_deformClass_smul hB hc1 hc2
  have hE' : |c * E| ≤ 2 - κ₀ / 2 := by
    rw [abs_mul, abs_of_pos hc0, hc, ← div_eq_inv_mul, div_le_iff₀ hs0]
    have h3 : (2 - κ₀ / 2) * (1 - κ₀ / 4) ≤ (2 - κ₀ / 2) * s := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  have hη0 : 0 < η := lt_of_lt_of_le (Real.rpow_pos_of_pos hWr0 _) hηlow
  have hηlow' : (n : ℝ) ^ (-1 + δ₁ / 2) ≤ c * η := by
    have h1 : (W : ℝ) ^ (-1 + δ₁) ≤ η := by
      refine le_trans ?_ hηlow
      exact Real.rpow_le_rpow_of_exponent_le hWr.le (by linarith)
    have h2 : (n : ℝ) ^ (-1 + δ₁ / 2) ≤ ((W : ℝ) / 2) ^ (-1 + δ₁ / 2) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hnhalf (by linarith)
    have h3 : ((W : ℝ) / 2) ^ (-1 + δ₁ / 2) ≤ (W : ℝ) ^ (-1 + δ₁ / 2) * 2 := by
      rw [Real.div_rpow hWr0.le (by norm_num), div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have h2a : (2 : ℝ) ^ (-1 : ℝ) ≤ 2 ^ (-1 + δ₁ / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      rw [Real.rpow_neg_one] at h2a
      have := inv_anti₀ (by norm_num : (0 : ℝ) < 2⁻¹) h2a
      simpa using this
    have h4 : (W : ℝ) ^ (-1 + δ₁) = (W : ℝ) ^ (-1 + δ₁ / 2) * (W : ℝ) ^ (δ₁ / 2) := by
      rw [← Real.rpow_add hWr0]; ring_nf
    have h5 : (W : ℝ) ^ (-1 + δ₁ / 2) * 2 ≤ (W : ℝ) ^ (-1 + δ₁) := by
      rw [h4]
      exact mul_le_mul_of_nonneg_left (hW₁ W hW₁W) (Real.rpow_nonneg hWr0.le _)
    calc (n : ℝ) ^ (-1 + δ₁ / 2) ≤ η := h2.trans (h3.trans (h5.trans h1))
      _ ≤ c * η := by nlinarith
  have hηhi' : c * η ≤ 2 := by nlinarith
  have hrate : ((n : ℝ) ^ (-(D + 1))) ≤ (W : ℝ) ^ (-D) := by
    have h1 : (n : ℝ) ^ (D + 1) ≥ ((W : ℝ) / 2) ^ (D + 1) :=
      Real.rpow_le_rpow (by positivity) hnhalf (by linarith)
    have h2 : ((W : ℝ) / 2) ^ (D + 1) = (W : ℝ) ^ (D + 1) / 2 ^ (D + 1) :=
      Real.div_rpow hWr0.le (by norm_num) _
    have h3 : (W : ℝ) ^ (D + 1) = (W : ℝ) ^ D * W := Real.rpow_add_one hWr0.ne' D
    have hp0 : 0 < (W : ℝ) ^ D := Real.rpow_pos_of_pos hWr0 _
    have h4 : (2 : ℝ) ^ (D + 1) ≤ W := hW₂ W hW₂W
    have hp1 : 0 < (2 : ℝ) ^ (D + 1) := by positivity
    rw [Real.rpow_neg hnr0.le, Real.rpow_neg hWr0.le]
    apply inv_anti₀ hp0
    rw [ge_iff_le, h2, h3, div_le_iff₀ hp1] at h1
    nlinarith
  have hmain := hn₀ n hn₀n ((c : ℂ) • B) (c * E) (c * η) hB' hE' hηlow' hηhi'
  have hF : Measurable fun ω : Ω W 1 => Qᴴ * gueMat W ω * Q := by
    have hgm : Measurable fun ω : Ω W 1 => gueMat W ω :=
      Matrix.measurable_iff.2 fun a b => localLawCompress_measurable_entry W a b
    exact ((continuous_const.matrix_mul continuous_id).matrix_mul
      continuous_const).measurable.comp hgm
  have hg : Measurable fun ω : Ω n 1 => ((s : ℝ) : ℂ) • gueMat n ω := by
    have hgm : Measurable fun ω : Ω n 1 => gueMat n ω :=
      Matrix.measurable_iff.2 fun a b => localLawCompress_measurable_entry n a b
    exact (continuous_const_smul ((s : ℝ) : ℂ)).measurable.comp hgm
  have hS : MeasurableSet {M : Matrix (Fin n) (Fin n) ℂ | ¬ (((2 * C₁)⁻¹ ≤
      (ntr (resolventMat (M - B) (E + η * Complex.I))).im) ∧
      (ntr (resolventMat (M - B) (E + η * Complex.I))).im ≤ 2 * C₁)} := by
    have hm := localLawCompress_measurable_im B ((E : ℂ) + η * Complex.I)
    exact (((measurableSet_le measurable_const hm).inter
      (measurableSet_le hm measurable_const))).compl
  calc μ W 1 {ω | ¬ ((2 * C₁)⁻¹ ≤
              (ntr (resolventMat (Qᴴ * gueMat W ω * Q - B) (E + η * Complex.I))).im ∧
            (ntr (resolventMat (Qᴴ * gueMat W ω * Q - B) (E + η * Complex.I))).im ≤ 2 * C₁)}
      = (μ W 1).map (fun ω => Qᴴ * gueMat W ω * Q)
          {M : Matrix (Fin n) (Fin n) ℂ | ¬ (((2 * C₁)⁻¹ ≤
            (ntr (resolventMat (M - B) (E + η * Complex.I))).im) ∧
            (ntr (resolventMat (M - B) (E + η * Complex.I))).im ≤ 2 * C₁)} :=
        (Measure.map_apply hF hS).symm
    _ = (μ n 1).map (fun ω => ((s : ℝ) : ℂ) • gueMat n ω)
          {M : Matrix (Fin n) (Fin n) ℂ | ¬ (((2 * C₁)⁻¹ ≤
            (ntr (resolventMat (M - B) (E + η * Complex.I))).im) ∧
            (ntr (resolventMat (M - B) (E + η * Complex.I))).im ≤ 2 * C₁)} := by
        rw [map_compress_gueMat W n Q hQ]
    _ = μ n 1 ((fun ω => ((s : ℝ) : ℂ) • gueMat n ω) ⁻¹'
          {M : Matrix (Fin n) (Fin n) ℂ | ¬ (((2 * C₁)⁻¹ ≤
            (ntr (resolventMat (M - B) (E + η * Complex.I))).im) ∧
            (ntr (resolventMat (M - B) (E + η * Complex.I))).im ≤ 2 * C₁)}) :=
        Measure.map_apply hg hS
    _ ≤ μ n 1 {ω | ¬ (C₁⁻¹ ≤ (ntr (resolventMat (gueMat n ω - (c : ℂ) • B)
            (((c * E : ℝ) : ℂ) + ((c * η : ℝ) : ℂ) * Complex.I))).im ∧
          (ntr (resolventMat (gueMat n ω - (c : ℂ) • B)
            (((c * E : ℝ) : ℂ) + ((c * η : ℝ) : ℂ) * Complex.I))).im ≤ C₁)} := by
        refine measure_mono ?_
        intro ω hω hcon
        apply hω
        have hid := localLawCompress_resolvent_smul hs0 (gueMat n ω) B ((E : ℂ) + η * Complex.I)
        have hz : ((s⁻¹ : ℝ) : ℂ) * ((E : ℂ) + η * Complex.I) =
            ((s⁻¹ * E : ℝ) : ℂ) + ((s⁻¹ * η : ℝ) : ℂ) * Complex.I := by push_cast; ring
        have him : (ntr (resolventMat (((s : ℝ) : ℂ) • gueMat n ω - B)
              ((E : ℂ) + η * Complex.I))).im
            = c * (ntr (resolventMat (gueMat n ω - (c : ℂ) • B)
              (((c * E : ℝ) : ℂ) + ((c * η : ℝ) : ℂ) * Complex.I))).im := by
          rw [hid, hz]
          unfold ntr
          rw [Matrix.trace_smul, smul_eq_mul]
          rw [← mul_assoc, mul_comm (Fintype.card (Fin n) : ℂ)⁻¹, mul_assoc, Complex.im_ofReal_mul]
        show (2 * C₁)⁻¹ ≤ (ntr (resolventMat (((s : ℝ) : ℂ) • gueMat n ω - B)
            ((E : ℂ) + η * Complex.I))).im ∧
          (ntr (resolventMat (((s : ℝ) : ℂ) • gueMat n ω - B) ((E : ℂ) + η * Complex.I))).im ≤
            2 * C₁
        rw [him]
        exact localLawCompress_real hC₁0 hc1 hc2 hcon
    _ ≤ ENNReal.ofReal ((n : ℝ) ^ (-(D + 1))) := hmain
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal hrate

end LSBA
