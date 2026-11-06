import LSBA.Dyson.Deformed

/-!
# Stability of the deformed equation

Lemma A.22 [da:lem:deformed-stability]: the residual stability (A.83)
[da:eq:deformed-residual-stability], the vector weight (A.84) [da:eq:deformed-vector-weight], and
stability for every Hermitian `B` at `η ≥ 2`.
-/

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section
open scoped Classical

namespace LSBA

section Helpers

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every entry of a matrix is bounded by its operator norm. -/
private lemma deformedStability_norm_entry_le (X : Matrix ι ι ℂ) (i j : ι) : ‖X i j‖ ≤ ‖X‖ := by
  have h := Matrix.l2_opNorm_mulVec X (WithLp.toLp 2 (Pi.single j (1 : ℂ)))
  have h1 : ‖(WithLp.toLp 2 (Pi.single j (1 : ℂ)) : EuclideanSpace ℂ ι)‖ = 1 := by
    simp
  rw [h1, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le ((EuclideanSpace.equiv ι ℂ).symm (X *ᵥ Pi.single j (1 : ℂ))) i
  simpa [Matrix.mulVec_single_one] using this

/-- The normalized trace is bounded by the operator norm: `‖⟨X⟩‖ ≤ ‖X‖`. -/
private lemma deformedStability_norm_ntr_le [Nonempty ι] (X : Matrix ι ι ℂ) : ‖ntr X‖ ≤ ‖X‖ := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have h1 : ‖X.trace‖ ≤ (Fintype.card ι : ℝ) * ‖X‖ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖X.diag i‖ ≤ ∑ _i : ι, ‖X‖ :=
          Finset.sum_le_sum fun i _ => deformedStability_norm_entry_le X i i
      _ = _ := by simp
  simp only [ntr, norm_mul, norm_inv, Complex.norm_natCast]
  rw [inv_mul_le_iff₀ hn]
  exact h1

omit [DecidableEq ι] in
private lemma deformedStability_ntr_sub (X Y : Matrix ι ι ℂ) : ntr (X - Y) = ntr X - ntr Y := by
  simp only [ntr, Matrix.trace_sub]; ring

omit [DecidableEq ι] in
private lemma deformedStability_ntr_smul (c : ℂ) (X : Matrix ι ι ℂ) : ntr (c • X) = c * ntr X := by
  simp only [ntr, Matrix.trace_smul, smul_eq_mul]; ring

/-- `‖M_q‖ ≤ τ⁻¹` once `Im(z + q) ≥ τ > 0`, for Hermitian `B`. -/
private lemma deformedStability_norm_le {B : Matrix ι ι ℂ} (hB : B.IsHermitian) {z q : ℂ}
    {τ : ℝ} (hτ : 0 < τ) (h : τ ≤ (z + q).im) : ‖deformedMat B z q‖ ≤ τ⁻¹ :=
  norm_resolventMat_le hB.neg hτ (h.trans (le_abs_self _))

/-- The resolvent identity `M_q - M_m = (q - m) M_m M_q`. -/
private lemma deformedStability_diff {B : Matrix ι ι ℂ} (hB : B.IsHermitian) {z m q : ℂ}
    (hm : 0 < (z + m).im) (hq : 0 < (z + q).im) :
    deformedMat B z q - deformedMat B z m = (q - m) • (deformedMat B z m * deformedMat B z q) := by
  set G := deformedMat B z m with hG
  set G' := deformedMat B z q with hG'
  have hX : (-B - (z + m) • (1 : Matrix ι ι ℂ)) * G = 1 :=
    sub_smul_mul_resolventMat hB.neg hm.ne'
  have hX' : (-B - (z + q) • (1 : Matrix ι ι ℂ)) * G' = 1 :=
    sub_smul_mul_resolventMat hB.neg hq.ne'
  have hGX : G * (-B - (z + m) • (1 : Matrix ι ι ℂ)) = 1 := mul_eq_one_comm.mp hX
  have e : (-B - (z + q) • (1 : Matrix ι ι ℂ)) - (-B - (z + m) • (1 : Matrix ι ι ℂ)) =
      (m - q) • (1 : Matrix ι ι ℂ) := by
    rw [sub_smul, add_smul, add_smul]; abel_nf
  have h1 : G * (-B - (z + q) • (1 : Matrix ι ι ℂ)) * G' = G := by
    rw [Matrix.mul_assoc, hX', Matrix.mul_one]
  have h2 : G * (-B - (z + m) • (1 : Matrix ι ι ℂ)) * G' = G' := by
    rw [hGX, Matrix.one_mul]
  have hdiff : G - G' = (m - q) • (G * G') := by
    calc G - G' = G * (-B - (z + q) • (1 : Matrix ι ι ℂ)) * G'
          - G * (-B - (z + m) • (1 : Matrix ι ι ℂ)) * G' := by rw [h1, h2]
      _ = G * ((-B - (z + q) • (1 : Matrix ι ι ℂ)) -
            (-B - (z + m) • (1 : Matrix ι ι ℂ))) * G' := by
          rw [← Matrix.sub_mul, ← Matrix.mul_sub]
      _ = (m - q) • (G * G') := by rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  rw [show q - m = -(m - q) by ring, neg_smul, ← hdiff]
  abel

/-- The exact identity `q - ⟨M_q⟩ = (q - m)(1 - ⟨M_m M_q⟩)` for a Herglotz root `m`. -/
private lemma deformedStability_residual {B : Matrix ι ι ℂ} (hB : B.IsHermitian) {z m q : ℂ}
    (hz : 0 < z.im) (hm : IsDeformedRoot B z m) (hq : 0 < (z + q).im) :
    q - deformedMap B z q = (q - m) * (1 - ntr (deformedMat B z m * deformedMat B z q)) := by
  have hmz : 0 < (z + m).im := by rw [Complex.add_im]; linarith [hm.1]
  have hd := congrArg ntr (deformedStability_diff hB hmz hq)
  rw [deformedStability_ntr_sub, deformedStability_ntr_smul] at hd
  have hfix : ntr (deformedMat B z m) = m := hm.2.symm
  have hΦ : deformedMap B z q = ntr (deformedMat B z q) := rfl
  rw [hΦ]
  linear_combination (-1 : ℂ) * hd + (-1 : ℂ) * hfix

/-- `|⟨M_m M_q⟩ - ⟨M_m²⟩| ≤ |q - m| ‖M_m‖² ‖M_q‖`. -/
private lemma deformedStability_gap [Nonempty ι] {B : Matrix ι ι ℂ} (hB : B.IsHermitian)
    {z m q : ℂ} (hm : 0 < (z + m).im) (hq : 0 < (z + q).im) :
    ‖ntr (deformedMat B z m * deformedMat B z q) - ntr (deformedMat B z m * deformedMat B z m)‖ ≤
      ‖q - m‖ * (‖deformedMat B z m‖ * (‖deformedMat B z m‖ * ‖deformedMat B z q‖)) := by
  set G := deformedMat B z m with hG
  set G' := deformedMat B z q with hG'
  have e : G * G' - G * G = (q - m) • (G * (G * G')) := by
    rw [← Matrix.mul_sub, deformedStability_diff hB hm hq, Matrix.mul_smul]
  rw [← deformedStability_ntr_sub, e, deformedStability_ntr_smul, norm_mul]
  gcongr
  refine (deformedStability_norm_ntr_le _).trans ?_
  refine (Matrix.l2_opNorm_mul _ _).trans ?_
  gcongr
  exact Matrix.l2_opNorm_mul _ _

end Helpers

/-- (A.83) [da:eq:deformed-residual-stability], Lemma A.22 [da:lem:deformed-stability]:
`|q - m_B| ≤ r₀` implies `|q - m_B| ≤ C |q - ⟨M_q⟩|`. -/
theorem deformed_residual_stability (κ₀ Cstar : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2)
    (hC : 0 < Cstar) :
    ∃ ε₀ r₀ C : ℝ, 0 < ε₀ ∧ 0 < r₀ ∧ 0 < C ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (B : Matrix ι ι ℂ) (ε E η : ℝ),
        0 ≤ ε → ε ≤ ε₀ → DeformClass ε B → |E| ≤ 2 - κ₀ → 0 < η → η ≤ Cstar →
        ∀ q : ℂ, ‖q - mB B (E + η * Complex.I)‖ ≤ r₀ →
          ‖q - mB B (E + η * Complex.I)‖ ≤
            C * ‖q - deformedMap B (E + η * Complex.I) q‖ := by
  obtain ⟨ε₁, Cp, hε₁, hCp, h1⟩ := deformed_profile κ₀ Cstar hκ₀ hκ₀' hC
  obtain ⟨ε₂, c, hε₂, hc, h2⟩ := deformed_scalar_stability κ₀ Cstar hκ₀ hκ₀' hC
  have hCp0 : 0 < Cp := by linarith
  have hr1 : 0 < 1 / (2 * Cp) := by positivity
  have hr2 : 0 < c / (4 * Cp ^ 3) := by positivity
  refine ⟨min ε₁ ε₂, min (1 / (2 * Cp)) (c / (4 * Cp ^ 3)), 2 / c, lt_min hε₁ hε₂,
    lt_min hr1 hr2, by positivity, ?_⟩
  intro ι _ _ _ B ε E η hε hεε₀ hBc hE hη hηC q hq
  have hε1 : ε ≤ ε₁ := hεε₀.trans (min_le_left _ _)
  have hε2 : ε ≤ ε₂ := hεε₀.trans (min_le_right _ _)
  obtain ⟨hmlo, -, -⟩ := h1 ι B ε E η hε hε1 hBc hE hη hηC
  obtain ⟨-, hgap⟩ := h2 ι B ε E η hε hε2 hBc hE hη hηC
  have hB : B.IsHermitian := hBc.1
  have hzim : (E + η * Complex.I).im = η := by simp
  have hz : 0 < (E + η * Complex.I).im := by rw [hzim]; exact hη
  have hm := isDeformedRoot_mB hB hz
  set z : ℂ := E + η * Complex.I with hzdef
  set m : ℂ := mB B z with hmdef
  have hr₀1 : min (1 / (2 * Cp)) (c / (4 * Cp ^ 3)) ≤ 1 / (2 * Cp) := min_le_left _ _
  have hr₀2 : min (1 / (2 * Cp)) (c / (4 * Cp ^ 3)) ≤ c / (4 * Cp ^ 3) := min_le_right _ _
  set r₀ := min (1 / (2 * Cp)) (c / (4 * Cp ^ 3)) with hr₀
  have hCpinv : 1 / (2 * Cp) = Cp⁻¹ / 2 := by field_simp
  -- `Im q` is bounded below
  have himq : Cp⁻¹ / 2 ≤ q.im := by
    have h3 : |q.im - m.im| ≤ ‖q - m‖ := by
      have := Complex.abs_im_le_norm (q - m)
      simpa using this
    have h4 : m.im - q.im ≤ ‖q - m‖ := by
      have := neg_abs_le (q.im - m.im)
      linarith
    linarith
  have hqz : Cp⁻¹ / 2 ≤ (z + q).im := by
    rw [Complex.add_im, hzim]; linarith
  have hqpos : 0 < (z + q).im := lt_of_lt_of_le (by positivity) hqz
  have hmz : Cp⁻¹ ≤ (z + m).im := by
    rw [Complex.add_im, hzim]; linarith
  have hmpos : 0 < (z + m).im := lt_of_lt_of_le (by positivity) hmz
  have hGq : ‖deformedMat B z q‖ ≤ 2 * Cp := by
    have := deformedStability_norm_le hB (by positivity : 0 < Cp⁻¹ / 2) hqz
    refine this.trans (le_of_eq ?_)
    field_simp
  have hG : ‖deformedMat B z m‖ ≤ Cp := by
    have := deformedStability_norm_le hB (inv_pos.mpr hCp0) hmz
    simpa using this
  have hGap := deformedStability_gap hB hmpos hqpos
  have hnum : ‖q - m‖ * (‖deformedMat B z m‖ * (‖deformedMat B z m‖ * ‖deformedMat B z q‖)) ≤
      c / 2 := by
    have hn1 : ‖deformedMat B z m‖ * (‖deformedMat B z m‖ * ‖deformedMat B z q‖) ≤
        Cp * (Cp * (2 * Cp)) := by gcongr
    calc _ ≤ r₀ * (Cp * (Cp * (2 * Cp))) := by gcongr
      _ ≤ c / (4 * Cp ^ 3) * (Cp * (Cp * (2 * Cp))) := by gcongr
      _ = c / 2 := by field_simp; ring
  have hlow : c / 2 ≤ ‖1 - ntr (deformedMat B z m * deformedMat B z q)‖ := by
    have hgap' : c ≤ ‖1 - ntr (deformedMat B z m * deformedMat B z m)‖ := hgap
    have h5 := norm_sub_norm_le (1 - ntr (deformedMat B z m * deformedMat B z m))
      (1 - ntr (deformedMat B z m * deformedMat B z q))
    have h6 : (1 - ntr (deformedMat B z m * deformedMat B z m)) -
        (1 - ntr (deformedMat B z m * deformedMat B z q)) =
        ntr (deformedMat B z m * deformedMat B z q) - ntr (deformedMat B z m * deformedMat B z m) :=
      by ring
    rw [h6] at h5
    linarith
  have hres := deformedStability_residual hB hz hm hqpos
  have hnorm : ‖q - deformedMap B z q‖ =
      ‖q - m‖ * ‖1 - ntr (deformedMat B z m * deformedMat B z q)‖ := by
    rw [hres, norm_mul]
  rw [hnorm]
  have hqm : 0 ≤ ‖q - m‖ := norm_nonneg _
  have : ‖q - m‖ * (c / 2) ≤ ‖q - m‖ * ‖1 - ntr (deformedMat B z m * deformedMat B z q)‖ :=
    mul_le_mul_of_nonneg_left hlow hqm
  have e : 2 / c * (‖q - m‖ * ‖1 - ntr (deformedMat B z m * deformedMat B z q)‖) ≥
      2 / c * (‖q - m‖ * (c / 2)) := by gcongr
  have e2 : 2 / c * (‖q - m‖ * (c / 2)) = ‖q - m‖ := by field_simp
  linarith

/-- (A.84) [da:eq:deformed-vector-weight], Lemma A.22 [da:lem:deformed-stability]:
`‖M‖ + ‖Im M‖ ≤ C`, `η ≤ C Im m`, and `v^* Im M v = (η + Im m) ‖M v‖² ≍ ‖M v‖²`. -/
theorem deformed_vector_weight (κ₀ Cstar : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hC : 0 < Cstar) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 1 ≤ C ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (B : Matrix ι ι ℂ) (ε E η : ℝ),
        0 ≤ ε → ε ≤ ε₀ → DeformClass ε B → |E| ≤ 2 - κ₀ → 0 < η → η ≤ Cstar →
        ‖MB B (E + η * Complex.I)‖ +
            ‖(2 * Complex.I)⁻¹ • (MB B (E + η * Complex.I) - (MB B (E + η * Complex.I))ᴴ)‖ ≤ C ∧
          η ≤ C * (mB B (E + η * Complex.I)).im ∧
          ∀ v : ι → ℂ,
            (star v ⬝ᵥ (MB B (E + η * Complex.I) *ᵥ v)).im =
                (η + (mB B (E + η * Complex.I)).im) *
                  ∑ i, ‖(MB B (E + η * Complex.I) *ᵥ v) i‖ ^ 2 ∧
              C⁻¹ * ∑ i, ‖(MB B (E + η * Complex.I) *ᵥ v) i‖ ^ 2 ≤
                (star v ⬝ᵥ (MB B (E + η * Complex.I) *ᵥ v)).im ∧
              (star v ⬝ᵥ (MB B (E + η * Complex.I) *ᵥ v)).im ≤
                C * ∑ i, ‖(MB B (E + η * Complex.I) *ᵥ v) i‖ ^ 2 := by
  obtain ⟨ε₀, Cp, hε₀, hCp, h1⟩ := deformed_profile κ₀ Cstar hκ₀ hκ₀' hC
  have hCp0 : 0 < Cp := by linarith
  have hCs : 0 < Cstar := hC
  have hCle1 : Cp ≤ max (max (2 * Cp) (Cstar * Cp)) (Cstar + 1) :=
    (by linarith : Cp ≤ 2 * Cp).trans ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨ε₀, max (max (2 * Cp) (Cstar * Cp)) (Cstar + 1), hε₀, hCp.trans hCle1, ?_⟩
  intro ι _ _ _ B ε E η hε hεε₀ hBc hE hη hηC
  obtain ⟨hmlo, -, -⟩ := h1 ι B ε E η hε hεε₀ hBc hE hη hηC
  have hB : B.IsHermitian := hBc.1
  have hzim : (E + η * Complex.I).im = η := by simp
  have hz : 0 < (E + η * Complex.I).im := by rw [hzim]; exact hη
  have hm := isDeformedRoot_mB hB hz
  have hm1 := IsDeformedRoot.norm_lt_one hB hz hm
  set z : ℂ := E + η * Complex.I with hzdef
  set m : ℂ := mB B z with hmdef
  set C : ℝ := max (max (2 * Cp) (Cstar * Cp)) (Cstar + 1) with hCdef
  have hC1 : 2 * Cp ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hC2 : Cstar * Cp ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hC3 : Cstar + 1 ≤ C := le_max_right _ _
  have hC0 : 0 < C := by linarith
  have hmim1 : m.im ≤ 1 := (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans hm1.le)
  have hmim0 : 0 < m.im := hm.1
  have hmz : 0 < (z + m).im := by rw [Complex.add_im, hzim]; linarith
  have hCpm : 1 ≤ Cp * m.im := by
    have := mul_le_mul_of_nonneg_left hmlo hCp0.le
    rwa [mul_inv_cancel₀ hCp0.ne'] at this
  have hMn : ‖MB B z‖ ≤ Cp := by
    have hle : m.im ≤ (z + m).im := by rw [Complex.add_im, hzim]; linarith
    have := deformedStability_norm_le hB hmim0 hle
    have h2 : (m.im)⁻¹ ≤ Cp := by
      rw [inv_le_comm₀ hmim0 hCp0]; exact hmlo
    exact this.trans h2
  have hMd : ‖(2 * Complex.I)⁻¹ • (MB B z - (MB B z)ᴴ)‖ ≤ Cp := by
    rw [norm_smul]
    have h3 : ‖(2 * Complex.I)⁻¹‖ = 1 / 2 := by simp
    have h4 : ‖MB B z - (MB B z)ᴴ‖ ≤ ‖MB B z‖ + ‖MB B z‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [Matrix.l2_opNorm_conjTranspose]
    rw [h3]
    linarith
  refine ⟨by linarith, ?_, fun v => ?_⟩
  · have : η ≤ Cstar * (Cp * m.im) := by
      calc η ≤ Cstar := hηC
        _ = Cstar * 1 := by ring
        _ ≤ Cstar * (Cp * m.im) := by gcongr
    calc η ≤ Cstar * (Cp * m.im) := this
      _ = (Cstar * Cp) * m.im := by ring
      _ ≤ C * m.im := by gcongr
  · have hid : (star v ⬝ᵥ (MB B z *ᵥ v)).im = (η + m.im) * ∑ i, ‖(MB B z *ᵥ v) i‖ ^ 2 := by
      have := im_dotProduct_deformedMat hB hmz v
      rw [Complex.add_im, hzim] at this
      exact this
    have hS : 0 ≤ ∑ i, ‖(MB B z *ᵥ v) i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
    have hCinv : C⁻¹ ≤ η + m.im := by
      have : C⁻¹ ≤ Cp⁻¹ := inv_anti₀ hCp0 (by linarith)
      linarith
    refine ⟨hid, ?_, ?_⟩
    · rw [hid]; exact mul_le_mul_of_nonneg_right hCinv hS
    · rw [hid]; exact mul_le_mul_of_nonneg_right (by linarith) hS

/-- Global form of (A.83) [da:eq:deformed-residual-stability] at heights `η ≥ 2`, for every
Hermitian `B` and every `Im q ≥ 0`: `|q - m_B| ≤ (4/3) |q - ⟨M_q⟩|`. -/
theorem deformed_stability_high {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {B : Matrix ι ι ℂ} (hB : B.IsHermitian) (E : ℝ) {η : ℝ} (hη : 2 ≤ η) {q : ℂ}
    (hq : 0 ≤ q.im) :
    ‖q - mB B (E + η * Complex.I)‖ ≤
      4 / 3 * ‖q - deformedMap B (E + η * Complex.I) q‖ := by
  have hzim : (E + η * Complex.I).im = η := by simp
  have hz : 0 < (E + η * Complex.I).im := by rw [hzim]; linarith
  have hm := isDeformedRoot_mB hB hz
  set z : ℂ := E + η * Complex.I with hzdef
  set m : ℂ := mB B z with hmdef
  have hqz : 2 ≤ (z + q).im := by rw [Complex.add_im, hzim]; linarith
  have hmz : 2 ≤ (z + m).im := by rw [Complex.add_im, hzim]; linarith [hm.1]
  have hqpos : 0 < (z + q).im := by linarith
  have hmpos : 0 < (z + m).im := by linarith
  have hGq : ‖deformedMat B z q‖ ≤ 2⁻¹ := deformedStability_norm_le hB two_pos hqz
  have hG : ‖deformedMat B z m‖ ≤ 2⁻¹ := deformedStability_norm_le hB two_pos hmz
  have hprod : ‖deformedMat B z m * deformedMat B z q‖ ≤ 1 / 4 := by
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    calc _ ≤ (2⁻¹ : ℝ) * 2⁻¹ := by gcongr
      _ = 1 / 4 := by norm_num
  have hn : ‖ntr (deformedMat B z m * deformedMat B z q)‖ ≤ 1 / 4 :=
    (deformedStability_norm_ntr_le _).trans hprod
  have hlow : 3 / 4 ≤ ‖1 - ntr (deformedMat B z m * deformedMat B z q)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (ntr (deformedMat B z m * deformedMat B z q))
    rw [norm_one] at this
    linarith
  have hres := deformedStability_residual hB hz hm hqpos
  have hnorm : ‖q - deformedMap B z q‖ =
      ‖q - m‖ * ‖1 - ntr (deformedMat B z m * deformedMat B z q)‖ := by
    rw [hres, norm_mul]
  rw [hnorm]
  have hqm : 0 ≤ ‖q - m‖ := norm_nonneg _
  have := mul_le_mul_of_nonneg_left hlow hqm
  nlinarith

end LSBA
