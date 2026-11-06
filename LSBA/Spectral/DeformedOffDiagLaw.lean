import LSBA.Spectral.DeformedMinorLaw

/-!
# Off-diagonal entries

The off-diagonal law (G.4) [us:eq:weighted-offdiagonal-law]: `|G_ij| ≤ n^ξ(nη)^{−1/2}|M_ii||M_jj|`
with high probability for diagonal `B`.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal Matrix.Norms.L2Operator

noncomputable section
open scoped Classical

namespace LSBA

/-! ### Deterministic estimates -/

/-- An entry is bounded by the operator norm. -/
private lemma offDiagLaw_norm_entry_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℂ) (i j : ι) : ‖X i j‖ ≤ ‖X‖ := by
  have h := Matrix.l2_opNorm_mulVec X ((EuclideanSpace.equiv ι ℂ).symm (Pi.single j 1))
  have hx : ‖(EuclideanSpace.equiv ι ℂ).symm (Pi.single j (1 : ℂ))‖ = 1 := by simp
  rw [hx, mul_one] at h
  refine le_trans (le_of_eq ?_) ((PiLp.norm_apply_le _ i).trans h)
  simp [Matrix.mulVec_single]

/-- Ward's identity in column form: `Σ_y |G_yx|² = Im G_xx / η`. -/
private lemma offDiagLaw_ward_col {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (E : ℝ) {η : ℝ} (hη : η ≠ 0) (x : ι) :
    ∑ y, ‖resolventMat A (E + η * Complex.I) y x‖ ^ 2 =
      (resolventMat A (E + η * Complex.I) x x).im / η := by
  have hz : (E + η * Complex.I).im ≠ 0 := by simpa using hη
  have hx := congrFun (congrFun (ward_matrix hA hz) x) x
  rw [Matrix.mul_apply] at hx
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply] at hx
  have e : ∑ y, star (resolventMat A (E + η * Complex.I) y x) *
        resolventMat A (E + η * Complex.I) y x
      = ((∑ y, ‖resolventMat A (E + η * Complex.I) y x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  rw [e, smul_eq_mul] at hx
  have him : (E + η * Complex.I).im = η := by simp
  have hw : ∀ w : ℂ, w - star w = ((2 * w.im : ℝ) : ℂ) * Complex.I := fun w => by
    apply Complex.ext <;> simp [two_mul]
  rw [hw, him] at hx
  apply Complex.ofReal_injective
  rw [hx]
  push_cast
  have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη
  field_simp

/-- The real-number estimate behind the off-diagonal bound: with `|G_ii| ≤ |M_ii| + s |M_ii|²`,
`s |M_ii| ≤ 1`, `|Σ| ≤ t (Y / (nη))^{1/2}`, `Y ≤ C |M_jj|²` and `2 √C ≤ t`, the product of `|G_ii|`
and `|Σ|` is at most `t² (nη)^{-1/2} |M_ii| |M_jj|`. -/
private lemma offDiagLaw_real {n η t s C CM Mi Mj gn Y Sn : ℝ} (hn : 0 < n) (hη : 0 < η)
    (hMi : 0 ≤ Mi) (hMj : 0 ≤ Mj) (hs : 0 ≤ s) (hsC : s * CM ≤ 1) (hMiC : Mi ≤ CM)
    (hgn : gn ≤ Mi + s * Mi ^ 2) (hSn : Sn ≤ t * Real.sqrt (n⁻¹ * (Y / η))) (hY : Y ≤ C * Mj ^ 2)
    (ht : 0 ≤ t) (hC : 0 ≤ C) (h2C : 2 * Real.sqrt C ≤ t) (hSn0 : 0 ≤ Sn) :
    gn * Sn ≤ t * t / Real.sqrt (n * η) * Mi * Mj := by
  have hnη : 0 < n * η := mul_pos hn hη
  have hq : 0 < Real.sqrt (n * η) := Real.sqrt_pos.mpr hnη
  have hg : gn ≤ 2 * Mi := by
    have h1 : s * Mi ^ 2 ≤ Mi := by
      calc s * Mi ^ 2 = (s * Mi) * Mi := by ring
        _ ≤ 1 * Mi := by
          refine mul_le_mul_of_nonneg_right ?_ hMi
          calc s * Mi ≤ s * CM := mul_le_mul_of_nonneg_left hMiC hs
            _ ≤ 1 := hsC
        _ = Mi := one_mul _
    linarith
  have hroot : Real.sqrt (n⁻¹ * (Y / η)) ≤ Real.sqrt C * Mj / Real.sqrt (n * η) := by
    have e : Real.sqrt C * Mj / Real.sqrt (n * η) = Real.sqrt (C * Mj ^ 2 / (n * η)) := by
      rw [Real.sqrt_div' _ hnη.le, Real.sqrt_mul hC, Real.sqrt_sq hMj]
    rw [e]
    apply Real.sqrt_le_sqrt
    have : n⁻¹ * (Y / η) = Y / (n * η) := by field_simp
    rw [this]
    exact div_le_div_of_nonneg_right hY hnη.le
  have hS : Sn ≤ t * (Real.sqrt C * Mj / Real.sqrt (n * η)) :=
    hSn.trans (mul_le_mul_of_nonneg_left hroot ht)
  have hsq : 0 ≤ Real.sqrt C := Real.sqrt_nonneg _
  calc gn * Sn ≤ (2 * Mi) * (t * (Real.sqrt C * Mj / Real.sqrt (n * η))) := by
        apply mul_le_mul hg hS hSn0 (by positivity)
    _ = (2 * Real.sqrt C) * t * Mi * Mj / Real.sqrt (n * η) := by ring
    _ ≤ t * t * Mi * Mj / Real.sqrt (n * η) := by
        apply div_le_div_of_nonneg_right _ hq.le
        have : 0 ≤ Mi * Mj := mul_nonneg hMi hMj
        calc (2 * Real.sqrt C) * t * Mi * Mj = ((2 * Real.sqrt C) * t) * (Mi * Mj) := by ring
          _ ≤ (t * t) * (Mi * Mj) := by gcongr
          _ = t * t * Mi * Mj := by ring
    _ = t * t / Real.sqrt (n * η) * Mi * Mj := by ring

/-! ### Measurability and independence -/

/-- The entries of the GUE matrix are measurable in the sample. -/
private lemma offDiagLaw_measurable_entry (n : ℕ) (a b : Fin n) :
    Measurable fun ω : Ω n 1 => gueMat n ω a b := by
  unfold gueMat gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

/-- The matrix inverse is measurable. -/
private lemma offDiagLaw_measurable_inv {m : Type*} [Fintype m] [DecidableEq m] :
    Measurable fun A : Matrix m m ℂ => A⁻¹ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  have hd : Measurable fun A : Matrix m m ℂ => A.det :=
    (continuous_id.matrix_det).measurable
  have ha : Measurable fun A : Matrix m m ℂ => A.adjugate i j :=
    (continuous_id.matrix_adjugate).measurable.eval_matrix
  exact (hd.inv).mul ha

/-- The minor resolvent of the deformed GUE matrix is measurable in the sample. -/
private lemma offDiagLaw_measurable_resolvent (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) (i : Fin n) :
    Measurable fun ω : Ω n 1 => resolventMat (minorMat (gueMat n ω - B) i) z := by
  unfold resolventMat
  refine offDiagLaw_measurable_inv.comp ?_
  refine Measurable.of_eval_matrix _ fun k l => ?_
  by_cases h : k = l
  · subst h
    simp only [minorMat, Matrix.sub_apply, Matrix.submatrix_apply, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul]
    exact ((offDiagLaw_measurable_entry n _ _).sub measurable_const).sub measurable_const
  · simp only [minorMat, Matrix.sub_apply, Matrix.submatrix_apply, Matrix.smul_apply,
      Matrix.one_apply_ne h, smul_zero, sub_zero]
    exact (offDiagLaw_measurable_entry n _ _).sub measurable_const

/-- The minor resolvent does not depend on row and column `i` of the GUE matrix. -/
private lemma offDiagLaw_offRow (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (i : Fin n) :
    OffRow n i fun ω : Ω n 1 => resolventMat (minorMat (gueMat n ω - B) i) z := by
  intro ω ω' h
  have hM : minorMat (gueMat n ω - B) i = minorMat (gueMat n ω' - B) i := by
    ext k l
    have hk : k.1 ≠ i := k.2
    have hl : l.1 ≠ i := l.2
    have hkl : gueMat n ω k.1 l.1 = gueMat n ω' k.1 l.1 := by
      have h1 := h (0, k.1, l.1) hk hl
      have h2 := h (0, l.1, k.1) hl hk
      have h3 := h (0, k.1, k.1) hk hk
      simp only [gueMat, gueBlock, Matrix.of_apply]
      simp [h1, h2, h3]
    simp [minorMat, hkl]
  simp only [resolventMat, hM]

/-! ### Asymptotics -/

/-- `n^ξ' / √(nη) ≤ n^{ξ' - δ/2}` for `η ≥ n^{-1+δ}`. -/
private lemma offDiagLaw_rate_le {n : ℕ} (hn : 1 ≤ n) {δ ξ' η : ℝ}
    (hη : (n : ℝ) ^ (-1 + δ) ≤ η) :
    (n : ℝ) ^ ξ' / Real.sqrt (n * η) ≤ (n : ℝ) ^ (ξ' - δ / 2) := by
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have h1 : (n : ℝ) ^ δ ≤ n * η := by
    calc (n : ℝ) ^ δ = (n : ℝ) * (n : ℝ) ^ (-1 + δ) := by
          conv_lhs => rw [show δ = 1 + (-1 + δ) by ring, Real.rpow_add hN0, Real.rpow_one]
      _ ≤ n * η := by gcongr
  have h2 : (n : ℝ) ^ (δ / 2) ≤ Real.sqrt (n * η) := by
    rw [Real.sqrt_eq_rpow]
    calc (n : ℝ) ^ (δ / 2) = ((n : ℝ) ^ δ) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_mul hN0.le]; congr 1; ring
      _ ≤ (n * η) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  calc (n : ℝ) ^ ξ' / Real.sqrt (n * η) ≤ (n : ℝ) ^ ξ' / (n : ℝ) ^ (δ / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) h2
    _ = (n : ℝ) ^ (ξ' - δ / 2) := (Real.rpow_sub hN0 _ _).symm

/-- `n^{-θ} ≤ c` for large `n`, `θ > 0`, `c > 0`. -/
private lemma offDiagLaw_rpow_neg_le_eventually {θ : ℝ} (hθ : 0 < θ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ (-θ) ≤ c :=
  (((tendsto_rpow_neg_atTop hθ).comp tendsto_natCast_atTop_atTop).eventually
    (gt_mem_nhds hc)).mono fun _ h => h.le

/-- The three failure probabilities of the proof of the off-diagonal bound add up to at most
`n^{-D}` for large `n`. -/
private lemma offDiagLaw_union_eventually {ξ : ℝ} (D : ℝ) (hξ : 0 < ξ) :
    ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ (-(D + 1)) + (n : ℝ) ^ (-(D + 1)) +
      ((n : ℝ) * n) * (4 * Real.exp (-((n : ℝ) ^ (ξ / 2)) ^ 2 / 2)) ≤ (n : ℝ) ^ (-D) := by
  have hT : Filter.Tendsto (fun x : ℝ => x ^ ((D + 2) / ξ) * Real.exp (-(1 / 2) * x))
      Filter.atTop (nhds 0) := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ (by norm_num)
  have hx : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ ξ) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hξ).comp tendsto_natCast_atTop_atTop
  have hG := (hT.comp hx).eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num))
  filter_upwards [hG, Filter.eventually_ge_atTop 4] with n hG hn4
  simp only [Function.comp_apply] at hG
  set N : ℝ := (n : ℝ) with hNdef
  have hN4 : 4 ≤ N := by rw [hNdef]; exact_mod_cast hn4
  have hN0 : 0 < N := by linarith
  set X : ℝ := N ^ (-D) with hX
  have hX0 : 0 < X := Real.rpow_pos_of_pos hN0 _
  have hXD : N ^ D * X = 1 := by
    rw [hX, ← Real.rpow_add hN0]; simp
  have h1 : N ^ (-(D + 1)) = X / N := by
    rw [hX, show -(D + 1) = -D + -1 by ring, Real.rpow_add hN0, Real.rpow_neg_one,
      div_eq_mul_inv]
  have h1' : N ^ (-(D + 1)) ≤ X / 4 := by
    rw [h1]
    exact div_le_div_of_nonneg_left hX0.le (by norm_num) hN4
  have e1 : (N ^ (ξ / 2)) ^ 2 = N ^ ξ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have e2 : (N ^ ξ) ^ ((D + 2) / ξ) = N * N * N ^ D := by
    rw [← Real.rpow_mul hN0.le, mul_div_cancel₀ _ hξ.ne', Real.rpow_add hN0]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  rw [e2] at hG
  have hgauss : N * N * (4 * Real.exp (-(N ^ (ξ / 2)) ^ 2 / 2)) ≤ X / 2 := by
    rw [e1]
    have e4 : -N ^ ξ / 2 = -(1 / 2) * N ^ ξ := by ring
    rw [e4]
    have h5 := mul_lt_mul_of_pos_right hG hX0
    calc N * N * (4 * Real.exp (-(1 / 2) * N ^ ξ))
        = 4 * (N * N * N ^ D * Real.exp (-(1 / 2) * N ^ ξ) * X) := by
          have : N * N * (4 * Real.exp (-(1 / 2) * N ^ ξ)) =
              N * N * (4 * Real.exp (-(1 / 2) * N ^ ξ)) * (N ^ D * X) := by
            rw [hXD, mul_one]
          rw [this]; ring
      _ ≤ 4 * (1 / 8 * X) := by gcongr
      _ = X / 2 := by ring
  linarith

/-- A union over a finite index type of sets of measure at most `ofReal c` has measure at most
`ofReal (card ι * c)`. -/
private lemma offDiagLaw_union_le {n : ℕ} {ι : Type*} [Fintype ι] {S : ι → Set (Ω n 1)} {c : ℝ}
    (h : ∀ x, μ n 1 (S x) ≤ ENNReal.ofReal c) :
    μ n 1 (⋃ x, S x) ≤ ENNReal.ofReal (Fintype.card ι * c) := by
  refine (measure_iUnion_fintype_le _ _).trans ?_
  refine (Finset.sum_le_sum fun x _ => h x).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- Off-diagonal law (G.4) [us:eq:weighted-offdiagonal-law] for diagonal `B`:
`|G_ij| ≤ n^ξ (nη)^{-1/2} |(M_B)_ii| |(M_B)_jj|` for all `i ≠ j`, with probability
`≥ 1 - n^{-D}`. -/
theorem localLaw_offdiag (κ₀ Cstar : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hC : 0 < Cstar) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε δ ξ D : ℝ, 0 < ε → ε ≤ ε₀ → 0 < δ → 0 < ξ → 0 < D →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (B : Matrix (Fin n) (Fin n) ℂ) (E η : ℝ),
        DeformClass ε B → B.IsDiag → |E| ≤ 2 - κ₀ → (n : ℝ) ^ (-1 + δ) ≤ η → η ≤ Cstar →
        μ n 1 {ω | ∃ i j : Fin n, i ≠ j ∧
            (n : ℝ) ^ ξ / Real.sqrt (n * η) * ‖MB B (E + η * Complex.I) i i‖ *
                ‖MB B (E + η * Complex.I) j j‖ <
              ‖resolventMat (gueMat n ω - B) (E + η * Complex.I) i j‖} ≤
          ENNReal.ofReal ((n : ℝ) ^ (-D)) := by
  obtain ⟨ε₁, hε₁, hentry⟩ := localLaw_entry κ₀ Cstar hκ₀ hκ₀' hC
  obtain ⟨ε₂, C, hε₂, hC1, hminor⟩ := localLaw_minor_diag κ₀ Cstar hκ₀ hκ₀' hC
  obtain ⟨ε₃, CM, hε₃, hCM, hvw⟩ := deformed_vector_weight κ₀ Cstar hκ₀ hκ₀' hC
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃), ?_⟩
  intro ε δ ξ D hε hεε₀ hδ hξ hD
  have hεε₁ : ε ≤ ε₁ := hεε₀.trans (min_le_left _ _)
  have hεε₂ : ε ≤ ε₂ := hεε₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεε₃ : ε ≤ ε₃ := hεε₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨n₁, hn₁⟩ := hentry ε δ (δ / 4) (D + 1) hε hεε₁ hδ (by positivity) (by linarith)
  obtain ⟨n₂, hn₂⟩ := hminor ε δ (D + 1) hε hεε₂ hδ (by linarith)
  have hCM0 : 0 < CM := by linarith
  have e1 : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ (-(δ / 4)) ≤ CM⁻¹ :=
    offDiagLaw_rpow_neg_le_eventually (by positivity) (inv_pos.mpr hCM0)
  have e2 : ∀ᶠ n : ℕ in Filter.atTop, 2 * Real.sqrt C ≤ (n : ℝ) ^ (ξ / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < ξ / 2)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have e3 := offDiagLaw_union_eventually D hξ
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp
    ((Filter.eventually_ge_atTop 4).and (e1.and (e2.and e3)))
  refine ⟨max n₀ (max n₁ n₂), ?_⟩
  intro n hn B E η hcl hBd hE hηlow hηC
  obtain ⟨hn4, he1, he2, he3⟩ := hn₀ n (by omega)
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < n := hn1
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hN0 : (0 : ℝ) < n := by linarith
  have hη0 : 0 < η := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hηlow
  have hz : 0 < (E + η * Complex.I).im := by simpa using hη0
  set z : ℂ := E + η * Complex.I with hzdef
  set t : ℝ := (n : ℝ) ^ (ξ / 2) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hN0 _
  have htt : t * t = (n : ℝ) ^ ξ := by
    rw [ht, ← Real.rpow_add hN0]; congr 1; ring
  have hBh : B.IsHermitian := hcl.1
  have : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  obtain ⟨hMB, -, -⟩ := hvw (Fin n) B ε E η hε.le hεε₃ hcl hE hη0 hηC
  have hMBn : ‖MB B z‖ ≤ CM := le_trans (le_add_of_nonneg_right (norm_nonneg _)) hMB
  -- the three exceptional events
  set SA : Set (Ω n 1) := {ω | ∃ i, (n : ℝ) ^ (δ / 4) / Real.sqrt (n * η) * ‖MB B z i i‖ ^ 2 <
    ‖resolventMat (gueMat n ω - B) z i i - MB B z i i‖} with hSA
  set SM : Set (Ω n 1) := {ω | ∃ i j : Fin n, ∃ h : j ≠ i, C * ‖MB B z j j‖ ^ 2 <
    (resolventMat (minorMat (gueMat n ω - B) i) z ⟨j, h⟩ ⟨j, h⟩).im} with hSM
  set SL : Fin n × Fin n → Set (Ω n 1) := fun x => {ω | ∃ h : x.2 ≠ x.1,
    t * Real.sqrt ((n : ℝ)⁻¹ * ∑ k : {k // k ≠ x.1},
      ‖resolventMat (minorMat (gueMat n ω - B) x.1) z k ⟨x.2, h⟩‖ ^ 2) <
      ‖∑ k : {k // k ≠ x.1}, gueMat n ω x.1 k.1 *
        resolventMat (minorMat (gueMat n ω - B) x.1) z k ⟨x.2, h⟩‖} with hSL
  have hSAm : μ n 1 SA ≤ ENNReal.ofReal ((n : ℝ) ^ (-(D + 1))) :=
    hn₁ n (by omega) B E η hcl hBd hE hηlow hηC
  have hSMm : μ n 1 SM ≤ ENNReal.ofReal ((n : ℝ) ^ (-(D + 1))) :=
    hn₂ n (by omega) B E η hcl hBd hE hηlow hηC
  have hSLm : ∀ x : Fin n × Fin n, μ n 1 (SL x) ≤ ENNReal.ofReal (4 * Real.exp (-t ^ 2 / 2)) := by
    intro x
    by_cases h : x.2 ≠ x.1
    · refine le_trans (measure_mono ?_) (gue_linForm_tail n x.1 (κ := {k // k ≠ x.1})
        (fun k => k.1) Subtype.val_injective (fun k => k.2)
        (a := fun ω k => resolventMat (minorMat (gueMat n ω - B) x.1) z k ⟨x.2, h⟩) ?_ ?_ ht0.le)
      · rintro ω ⟨h', hω⟩
        exact hω
      · exact Measurable.of_eval fun k =>
          (measurable_pi_apply _).comp ((measurable_pi_apply k).comp
            (offDiagLaw_measurable_resolvent n B z x.1))
      · intro ω ω' hh
        funext k
        exact congrFun (congrFun (offDiagLaw_offRow n B z x.1 ω ω' hh) k) ⟨x.2, h⟩
    · have : SL x = ∅ := by
        ext ω
        simp only [hSL, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h', -⟩
        exact h h'
      rw [this]
      simp
  have hbad : {ω : Ω n 1 | ∃ i j : Fin n, i ≠ j ∧
      (n : ℝ) ^ ξ / Real.sqrt (n * η) * ‖MB B z i i‖ * ‖MB B z j j‖ <
        ‖resolventMat (gueMat n ω - B) z i j‖} ⊆ (SA ∪ SM) ∪ ⋃ x, SL x := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hnot
    obtain ⟨⟨hA, hMn⟩, hLn⟩ := hnot
    obtain ⟨i, j, hij, hlt⟩ := hω
    apply absurd hlt
    rw [not_lt]
    have hji : j ≠ i := hij.symm
    have hHh : (gueMat n ω - B).IsHermitian := (gueBlock_isHermitian n 1 ω 0).sub hBh
    have hH'h : (minorMat (gueMat n ω - B) i).IsHermitian := hHh.submatrix _
    have hEnt : ‖resolventMat (gueMat n ω - B) z i i - MB B z i i‖ ≤
        (n : ℝ) ^ (δ / 4) / Real.sqrt (n * η) * ‖MB B z i i‖ ^ 2 :=
      not_lt.mp (fun h' => hA ⟨i, h'⟩)
    have hMin : (resolventMat (minorMat (gueMat n ω - B) i) z ⟨j, hji⟩ ⟨j, hji⟩).im ≤
        C * ‖MB B z j j‖ ^ 2 := not_lt.mp (fun h' => hMn ⟨i, j, hji, h'⟩)
    have hLin : ‖∑ k : {k // k ≠ i}, gueMat n ω i k.1 *
        resolventMat (minorMat (gueMat n ω - B) i) z k ⟨j, hji⟩‖ ≤
        t * Real.sqrt ((n : ℝ)⁻¹ * ∑ k : {k // k ≠ i},
          ‖resolventMat (minorMat (gueMat n ω - B) i) z k ⟨j, hji⟩‖ ^ 2) :=
      not_lt.mp (fun h' => hLn (i, j) ⟨hji, h'⟩)
    have hward := offDiagLaw_ward_col hH'h E hη0.ne' (⟨j, hji⟩ : {k // k ≠ i})
    have hsch := resolventMat_offdiag_schur hHh hz hji
    have hsum : ∑ k : {k // k ≠ i}, (gueMat n ω - B) i k.1 *
        resolventMat (minorMat (gueMat n ω - B) i) z k ⟨j, hji⟩ =
        ∑ k : {k // k ≠ i}, gueMat n ω i k.1 *
        resolventMat (minorMat (gueMat n ω - B) i) z k ⟨j, hji⟩ := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.sub_apply, hBd k.2.symm, sub_zero]
    have hnorm : ‖resolventMat (gueMat n ω - B) z i j‖ =
        ‖resolventMat (gueMat n ω - B) z i i‖ *
          ‖∑ k : {k // k ≠ i}, gueMat n ω i k.1 *
            resolventMat (minorMat (gueMat n ω - B) i) z k ⟨j, hji⟩‖ := by
      rw [hsch, hsum, norm_neg, norm_mul]
    rw [hnorm, ← htt]
    have hs0 : 0 ≤ (n : ℝ) ^ (δ / 4) / Real.sqrt (n * η) := by positivity
    have hsC : (n : ℝ) ^ (δ / 4) / Real.sqrt (n * η) * CM ≤ 1 := by
      have h1 := offDiagLaw_rate_le hn1 (δ := δ) (ξ' := δ / 4) hηlow
      have e : δ / 4 - δ / 2 = -(δ / 4) := by ring
      rw [e] at h1
      calc (n : ℝ) ^ (δ / 4) / Real.sqrt (n * η) * CM ≤ CM⁻¹ * CM :=
            mul_le_mul_of_nonneg_right (h1.trans he1) hCM0.le
        _ = 1 := inv_mul_cancel₀ hCM0.ne'
    have hgn : ‖resolventMat (gueMat n ω - B) z i i‖ ≤ ‖MB B z i i‖ +
        (n : ℝ) ^ (δ / 4) / Real.sqrt (n * η) * ‖MB B z i i‖ ^ 2 :=
      (norm_le_norm_add_norm_sub' _ _).trans (add_le_add_right hEnt _)
    refine offDiagLaw_real (Y := (resolventMat (minorMat (gueMat n ω - B) i) z ⟨j, hji⟩
      ⟨j, hji⟩).im) (CM := CM) (C := C) hN0 hη0 (norm_nonneg _) (norm_nonneg _) hs0 hsC
      ((offDiagLaw_norm_entry_le _ _ _).trans hMBn) hgn ?_ hMin ht0.le (by linarith) he2
      (norm_nonneg _)
    rw [← hward]
    exact hLin
  calc μ n 1 {ω : Ω n 1 | ∃ i j : Fin n, i ≠ j ∧
        (n : ℝ) ^ ξ / Real.sqrt (n * η) * ‖MB B z i i‖ * ‖MB B z j j‖ <
          ‖resolventMat (gueMat n ω - B) z i j‖}
      ≤ μ n 1 ((SA ∪ SM) ∪ ⋃ x, SL x) := measure_mono hbad
    _ ≤ μ n 1 (SA ∪ SM) + μ n 1 (⋃ x, SL x) := measure_union_le _ _
    _ ≤ (μ n 1 SA + μ n 1 SM) + μ n 1 (⋃ x, SL x) := by
        gcongr; exact measure_union_le _ _
    _ ≤ (ENNReal.ofReal ((n : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((n : ℝ) ^ (-(D + 1)))) +
        ENNReal.ofReal (Fintype.card (Fin n × Fin n) * (4 * Real.exp (-t ^ 2 / 2))) := by
        gcongr
        exact offDiagLaw_union_le hSLm
    _ = ENNReal.ofReal ((n : ℝ) ^ (-(D + 1)) + (n : ℝ) ^ (-(D + 1)) +
          ((n : ℝ) * n) * (4 * Real.exp (-t ^ 2 / 2))) := by
        rw [Fintype.card_prod, Fintype.card_fin]
        push_cast
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((n : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal he3

end LSBA
