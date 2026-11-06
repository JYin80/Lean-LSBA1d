import LSBA.Spectral.Resolvent

/-!
# Resolvent bounds

For Hermitian `A` and `|Im z| ≥ η > 0`: invertibility of `A - z`, the operator-norm bound
`‖(A - z)⁻¹‖ ≤ η⁻¹`, the resolvent identity, the Hilbert–Schmidt bound for `G X G'`, and the
derivative of `s ↦ (M + s A - z)⁻¹` along a Hermitian line. These are the resolvent inputs of the
Lipschitz constants in Appendix D.2 [sec:rough-density-proof] and of the generator identity behind
(5.4) [fo:eq:ito]. The matrix norm is the `ℓ² → ℓ²` operator norm (scope `Matrix.Norms.L2Operator`).
-/

open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

open scoped Classical

namespace LSBA

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem isUnit_sub_smul_one {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    IsUnit (A - z • (1 : Matrix n n ℂ)) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hAv : A *ᵥ v = z • v := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
    exact hv
  have him := hA.im_star_dotProduct_mulVec_self v
  rw [hAv, dotProduct_smul, smul_eq_mul] at him
  have hd : star v ⬝ᵥ v = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, Complex.mul_conj]
  have hpos : (∑ i, Complex.normSq (v i) : ℝ) ≠ 0 := by
    intro h0
    apply hv0
    funext i
    exact Complex.normSq_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Complex.normSq_nonneg (v j))).mp h0 i (Finset.mem_univ i))
  rw [hd, RCLike.im_to_complex, Complex.im_mul_ofReal] at him
  exact hz ((mul_eq_zero.mp him).resolve_right hpos)

/-- The imaginary part of `⟪v, A v⟫` vanishes for a Hermitian matrix `A`. -/
private lemma resolventBounds_im_inner_self {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (v : EuclideanSpace ℂ n) :
    (⟪v, Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A v⟫_ℂ).im = 0 := by
  have := hA.im_star_dotProduct_mulVec_self (WithLp.ofLp v)
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simpa [dotProduct_comm] using this

/-- The lower bound `|Im z| ‖v‖ ≤ ‖(A - z) v‖` for Hermitian `A`. -/
private lemma resolventBounds_abs_im_mul_norm_le {A : Matrix n n ℂ} (hA : A.IsHermitian) (z : ℂ)
    (v : EuclideanSpace ℂ n) :
    |z.im| * ‖v‖ ≤ ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (A - z • (1 : Matrix n n ℂ)) v‖ := by
  set T := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (A - z • (1 : Matrix n n ℂ)) with hT
  have hTv : T v = Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A v - z • v := by
    simp [hT, map_sub, map_smul]
  have hinner : ⟪v, T v⟫_ℂ
      = ⟪v, Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A v⟫_ℂ - z * ⟪v, v⟫_ℂ := by
    rw [hTv, inner_sub_right, inner_smul_right]
  have hvv_im : (⟪v, v⟫_ℂ).im = 0 := by
    simpa [RCLike.im_to_complex] using inner_self_im (𝕜 := ℂ) v
  have hvv_re : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := by
    simpa [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜 := ℂ) v
  have him : (⟪v, T v⟫_ℂ).im = -(z.im * ‖v‖ ^ 2) := by
    rw [hinner, Complex.sub_im, Complex.mul_im, hvv_im, hvv_re,
      resolventBounds_im_inner_self hA v]
    ring
  have hcs : ‖⟪v, T v⟫_ℂ‖ ≤ ‖v‖ * ‖T v‖ := norm_inner_le_norm v (T v)
  have h1 : |z.im| * ‖v‖ ^ 2 ≤ ‖v‖ * ‖T v‖ := by
    refine le_trans ?_ hcs
    have hle := Complex.abs_im_le_norm ⟪v, T v⟫_ℂ
    rw [him] at hle
    calc |z.im| * ‖v‖ ^ 2 = |(-(z.im * ‖v‖ ^ 2))| := by
          rw [abs_neg, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖v‖ ^ 2)]
      _ ≤ _ := hle
  rcases eq_or_lt_of_le (norm_nonneg v) with hv | hv
  · simp [← hv]
  · exact (mul_le_mul_iff_of_pos_left hv).mp
      (by linarith [h1] : ‖v‖ * (|z.im| * ‖v‖) ≤ ‖v‖ * ‖T v‖)

/-- `‖(A - z)⁻¹‖ ≤ η⁻¹` for Hermitian `A` and `|Im z| ≥ η > 0`. -/
theorem norm_resolventMat_le {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ} {η : ℝ}
    (hη : 0 < η) (hz : η ≤ |z.im|) : ‖resolventMat A z‖ ≤ η⁻¹ := by
  have hzim : z.im ≠ 0 := fun h => absurd hz (by rw [h]; simpa using hη)
  set B : Matrix n n ℂ := A - z • (1 : Matrix n n ℂ) with hB
  have hBu : IsUnit B := isUnit_sub_smul_one hA hzim
  have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hBu
  change ‖B⁻¹‖ ≤ η⁻¹
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  set w := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) B⁻¹ v with hw
  have hBw : Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) B w = v := by
    have hmul : Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) B
        * Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) B⁻¹ = 1 := by
      rw [← map_mul, Matrix.mul_nonsing_inv B hdet, map_one]
    calc Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) B w
        = (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) B
            * Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) B⁻¹) v := rfl
      _ = v := by rw [hmul]; rfl
  have hkey := resolventBounds_abs_im_mul_norm_le hA z w
  rw [hBw] at hkey
  have hfin : η * ‖w‖ ≤ ‖v‖ := le_trans (by nlinarith [norm_nonneg w]) hkey
  rw [inv_mul_eq_div, le_div_iff₀ hη]
  linarith [hfin]

/-- Resolvent identity `G(A) - G(B) = G(A) (B - A) G(B)`. -/
theorem resolventMat_sub_resolventMat {A B : Matrix n n ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    resolventMat A z - resolventMat B z = resolventMat A z * (B - A) * resolventMat B z := by
  have hAr := sub_smul_mul_resolventMat hA hz
  have hBr := sub_smul_mul_resolventMat hB hz
  have hAl := mul_eq_one_comm.mp hAr
  have hBdiff : B - A = (B - z • (1 : Matrix n n ℂ)) - (A - z • (1 : Matrix n n ℂ)) := by abel
  rw [hBdiff, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc (resolventMat A z) (B - z • (1 : Matrix n n ℂ)) (resolventMat B z), hBr,
    Matrix.mul_one, hAl, Matrix.one_mul]

/-- Columnwise Hilbert–Schmidt bound `‖Y X‖_HS ≤ ‖Y‖ ‖X‖_HS`, with the column index outside. -/
private lemma resolventBounds_hs_mul_left (Y X : Matrix n n ℂ) :
    ∑ j, ∑ i, ‖(Y * X) i j‖ ^ 2 ≤ ‖Y‖ ^ 2 * ∑ j, ∑ i, ‖X i j‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  set x : EuclideanSpace ℂ n := (EuclideanSpace.equiv n ℂ).symm (fun i => X i j) with hx
  have h := Matrix.l2_opNorm_mulVec Y x
  have hxx : (EuclideanSpace.equiv n ℂ).symm (Y *ᵥ (fun i => X i j))
      = (EuclideanSpace.equiv n ℂ).symm (fun i => (Y * X) i j) := by
    congr 1
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  simpa [hx, Matrix.mul_apply, Matrix.mulVec, dotProduct] using h2

/-- Hilbert–Schmidt bound `‖Y X‖_HS ≤ ‖Y‖ ‖X‖_HS` with entry sums. -/
private lemma resolventBounds_hs_mul_left' (Y X : Matrix n n ℂ) :
    ∑ i, ∑ j, ‖(Y * X) i j‖ ^ 2 ≤ ‖Y‖ ^ 2 * ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => ‖X i j‖ ^ 2)]
  exact resolventBounds_hs_mul_left Y X

/-- Hilbert–Schmidt bound `‖X Y‖_HS ≤ ‖X‖_HS ‖Y‖`, via the conjugate transpose. -/
private lemma resolventBounds_hs_mul_right (X Y : Matrix n n ℂ) :
    ∑ i, ∑ j, ‖(X * Y) i j‖ ^ 2 ≤ ‖Y‖ ^ 2 * ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  have h := resolventBounds_hs_mul_left' Yᴴ Xᴴ
  rw [← Matrix.conjTranspose_mul, Matrix.l2_opNorm_conjTranspose] at h
  have e1 : ∑ i, ∑ j, ‖(X * Y)ᴴ i j‖ ^ 2 = ∑ i, ∑ j, ‖(X * Y) i j‖ ^ 2 := by
    rw [Finset.sum_comm]; simp [Matrix.conjTranspose_apply]
  have e2 : ∑ i, ∑ j, ‖Xᴴ i j‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
    rw [Finset.sum_comm]; simp [Matrix.conjTranspose_apply]
  rw [e1, e2] at h
  exact h

/-- Hilbert–Schmidt bound `‖G(A) X G(B)‖_HS ≤ η⁻² ‖X‖_HS`, written with entry sums. -/
theorem sum_norm_sq_resolventMat_mul_mul_le {A B : Matrix n n ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) (X : Matrix n n ℂ) :
    ∑ i, ∑ j, ‖(resolventMat A z * X * resolventMat B z) i j‖ ^ 2 ≤
      η⁻¹ ^ 4 * ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  have hGA := norm_resolventMat_le hA hη hz
  have hGB := norm_resolventMat_le hB hη hz
  have h1 := resolventBounds_hs_mul_right (resolventMat A z * X) (resolventMat B z)
  have h2 := resolventBounds_hs_mul_left' (resolventMat A z) X
  have hS : 0 ≤ ∑ i, ∑ j, ‖X i j‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hsq : ‖resolventMat B z‖ ^ 2 ≤ (η⁻¹) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hGB 2
  have hsqA : ‖resolventMat A z‖ ^ 2 ≤ (η⁻¹) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hGA 2
  have hT : 0 ≤ ∑ i, ∑ j, ‖(resolventMat A z * X) i j‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  calc _ ≤ ‖resolventMat B z‖ ^ 2 * ∑ i, ∑ j, ‖(resolventMat A z * X) i j‖ ^ 2 := h1
    _ ≤ (η⁻¹) ^ 2 * (‖resolventMat A z‖ ^ 2 * ∑ i, ∑ j, ‖X i j‖ ^ 2) := by
        refine mul_le_mul hsq h2 hT (by positivity)
    _ ≤ (η⁻¹) ^ 2 * ((η⁻¹) ^ 2 * ∑ i, ∑ j, ‖X i j‖ ^ 2) := by
        gcongr
    _ = η⁻¹ ^ 4 * ∑ i, ∑ j, ‖X i j‖ ^ 2 := by ring

/-- The affine line `s ↦ M + s • A` has derivative `A`. -/
private lemma resolventBounds_hasDerivAt_line (M A : Matrix n n ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => M + (s : ℂ) • A) A t := by
  have h : HasDerivAt (fun s : ℝ => (s : ℂ) • A) A t := by
    simpa using (hasDerivAt_id t).smul_const A
  simpa using h.const_add M

omit [Fintype n] [DecidableEq n] in
/-- A real multiple of a Hermitian matrix added to a Hermitian matrix is Hermitian. -/
private lemma resolventBounds_isHermitian_add_realSmul {M A : Matrix n n ℂ} (hM : M.IsHermitian)
    (hA : A.IsHermitian) (s : ℝ) : (M + (s : ℂ) • A).IsHermitian := by
  refine hM.add ?_
  change Matrix.conjTranspose ((s : ℂ) • A) = (s : ℂ) • A
  rw [Matrix.conjTranspose_smul, hA, Complex.star_def, Complex.conj_ofReal]

/-- Along the line `t ↦ M + t • A` of invertible matrices, the inverse has derivative `-R A R`. -/
private lemma resolventBounds_hasDerivAt_lineInverse {M A : Matrix n n ℂ}
    (hU : ∀ t : ℝ, IsUnit (M + (t : ℂ) • A)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Ring.inverse (M + (s : ℂ) • A))
      (-(Ring.inverse (M + (t : ℂ) • A) * A * Ring.inverse (M + (t : ℂ) • A))) t := by
  set u : (Matrix n n ℂ)ˣ := (hU t).unit
  have hus : (u : Matrix n n ℂ) = M + (t : ℂ) • A := IsUnit.unit_spec _
  have hinv : ((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ)
      = Ring.inverse (M + (t : ℂ) • A) := by
    rw [← hus, Ring.inverse_unit]
  have hF : HasFDerivAt (Ring.inverse (M₀ := Matrix n n ℂ))
      (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) ↑u⁻¹) ↑u⁻¹)
      (M + (t : ℂ) • A) := by
    rw [← hus]; exact hasFDerivAt_ringInverse u
  have hcomp := hF.comp_hasDerivAt t (resolventBounds_hasDerivAt_line M A t)
  simpa [Function.comp_def, ContinuousLinearMap.mulLeftRight_apply, hinv] using hcomp

/-- The resolvent along the line is the inverse of the shifted line. -/
private lemma resolventBounds_resolventMat_line_eq {M A : Matrix n n ℂ} (z : ℂ) :
    (fun s : ℝ => resolventMat (M + (s : ℂ) • A) z)
      = fun s : ℝ => Ring.inverse (M - z • (1 : Matrix n n ℂ) + (s : ℂ) • A) := by
  funext s
  change (M + (s : ℂ) • A - z • (1 : Matrix n n ℂ))⁻¹ = _
  rw [Matrix.nonsing_inv_eq_ringInverse]
  congr 1
  abel

/-- Every matrix on the shifted line is invertible when `M`, `A` are Hermitian. -/
private lemma resolventBounds_isUnit_line {M A : Matrix n n ℂ} (hM : M.IsHermitian)
    (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (s : ℝ) :
    IsUnit (M - z • (1 : Matrix n n ℂ) + (s : ℂ) • A) := by
  have he : M - z • (1 : Matrix n n ℂ) + (s : ℂ) • A
      = (M + (s : ℂ) • A) - z • (1 : Matrix n n ℂ) := by abel
  rw [he]
  exact isUnit_sub_smul_one (resolventBounds_isHermitian_add_realSmul hM hA s) hz

/-- Along `s ↦ M + s A` with `M`, `A` Hermitian, the resolvent has derivative `-G A G`. -/
theorem hasDerivAt_resolventMat_line {M A : Matrix n n ℂ} (hM : M.IsHermitian)
    (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => resolventMat (M + (s : ℂ) • A) z)
      (-(resolventMat (M + (t : ℂ) • A) z * A * resolventMat (M + (t : ℂ) • A) z)) t := by
  have hU := resolventBounds_isUnit_line hM hA hz
  have h := resolventBounds_hasDerivAt_lineInverse hU t
  rw [← resolventBounds_resolventMat_line_eq z] at h
  have e : Ring.inverse (M - z • (1 : Matrix n n ℂ) + (t : ℂ) • A)
      = resolventMat (M + (t : ℂ) • A) z := by
    have := congrFun (resolventBounds_resolventMat_line_eq (M := M) (A := A) z) t
    exact this.symm
  rwa [e] at h

end LSBA
