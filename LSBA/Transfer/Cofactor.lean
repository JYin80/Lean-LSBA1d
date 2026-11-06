import LSBA.Transfer.VolCocycle

/-!
# The omitted-column identity

Lemma F.2 [cc:lem:cofactor]: for a maximal isotropic frame Φ and the flags omitting one column,
`e^{−c(T; U_j, Y)} = ‖e_j^* D^{−1}‖` (F.3) [cc:eq:cofactor], and `‖D^{−1}‖^s ≤ Σ_j e^{−s c(T; U_j,
Y)}` (F.4) [cc:eq:inverse] for `0 < s ≤ 2`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The pair `(P_{U_j}, P_Y)` with `Y = ran Φ` and `U_j` the span of the columns of `Φ` other
than the `j`-th (Lemma 8.6 [up:lem:operator-reduction], Lemma F.2 [cc:lem:cofactor]). -/
def omitPair {W : ℕ} (Φ : Matrix (Fin 2 × Fin W) (Fin W) ℂ) (j : Fin W) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (Φ * Φᴴ - Matrix.vecMulVec (fun i => Φ i j) (star fun i => Φ i j), Φ * Φᴴ)

/-- For `Ψ* Ψ = 1` and `Ψ* J Ψ = 0`, `Ψ Ψ*` is the orthogonal projection onto `ran Ψ`, of trace
`|κ|`, with `P J P = 0`. -/
private theorem cofactor_gram_proj {W : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Ψ : Matrix (Fin 2 × Fin W) κ ℂ) (h1 : Ψᴴ * Ψ = 1) (h2 : Ψᴴ * isoJ W * Ψ = 0) :
    (Ψ * Ψᴴ).IsHermitian ∧ Ψ * Ψᴴ * (Ψ * Ψᴴ) = Ψ * Ψᴴ ∧
      (Ψ * Ψᴴ).trace = (Fintype.card κ : ℂ) ∧ Ψ * Ψᴴ * isoJ W * (Ψ * Ψᴴ) = 0 := by
  refine ⟨Matrix.isHermitian_mul_conjTranspose_self _, ?_, ?_, ?_⟩
  · calc Ψ * Ψᴴ * (Ψ * Ψᴴ) = Ψ * (Ψᴴ * Ψ) * Ψᴴ := by simp only [Matrix.mul_assoc]
      _ = Ψ * Ψᴴ := by rw [h1, Matrix.mul_one]
  · rw [Matrix.trace_mul_comm, h1, Matrix.trace_one]
  · calc Ψ * Ψᴴ * isoJ W * (Ψ * Ψᴴ) = Ψ * (Ψᴴ * isoJ W * Ψ) * Ψᴴ := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h2, Matrix.mul_zero, Matrix.zero_mul]

/-- The frame `Ψ_j` obtained from `Φ` by removing its `j`-th column. -/
private def cofactor_frame {n : ℕ} (Φ : Matrix (Fin 2 × Fin (n + 1)) (Fin (n + 1)) ℂ)
    (j : Fin (n + 1)) : Matrix (Fin 2 × Fin (n + 1)) (Fin n) ℂ :=
  Φ.submatrix id j.succAbove

/-- `Ψ_j* X Ψ_j` is the principal submatrix of `Φ* X Φ` omitting the `j`-th index. -/
private theorem cofactor_frame_sandwich {n : ℕ} (Φ : Matrix (Fin 2 × Fin (n + 1)) (Fin (n + 1)) ℂ)
    (j : Fin (n + 1)) (X : Matrix (Fin 2 × Fin (n + 1)) (Fin 2 × Fin (n + 1)) ℂ) :
    (cofactor_frame Φ j)ᴴ * X * cofactor_frame Φ j =
      (Φᴴ * X * Φ).submatrix j.succAbove j.succAbove := by
  ext a b
  simp [cofactor_frame, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]

/-- `Ψ_j Ψ_j* = Φ Φ* - φ_j φ_j*`, where `φ_j` is the `j`-th column of `Φ`. -/
private theorem cofactor_frame_mul {n : ℕ} (Φ : Matrix (Fin 2 × Fin (n + 1)) (Fin (n + 1)) ℂ)
    (j : Fin (n + 1)) :
    cofactor_frame Φ j * (cofactor_frame Φ j)ᴴ =
      Φ * Φᴴ - Matrix.vecMulVec (fun i => Φ i j) (star fun i => Φ i j) := by
  ext a b
  simp only [cofactor_frame, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply,
    Matrix.sub_apply, Matrix.vecMulVec_apply, Pi.star_apply, id]
  rw [Fin.sum_univ_succAbove _ j]
  ring

/-- `Ψ_j* Ψ_j = 1` for `Φ* Φ = 1`. -/
private theorem cofactor_frame_gram {n : ℕ} {Φ : Matrix (Fin 2 × Fin (n + 1)) (Fin (n + 1)) ℂ}
    (h1 : Φᴴ * Φ = 1) (j : Fin (n + 1)) :
    (cofactor_frame Φ j)ᴴ * cofactor_frame Φ j = 1 := by
  have := cofactor_frame_sandwich Φ j 1
  simp only [Matrix.mul_one] at this
  rw [this, h1]
  ext a b
  simp [Matrix.one_apply]

/-- `Ψ_j* J Ψ_j = 0` for `Φ* J Φ = 0`. -/
private theorem cofactor_frame_isoJ {n : ℕ} {Φ : Matrix (Fin 2 × Fin (n + 1)) (Fin (n + 1)) ℂ}
    (h2 : Φᴴ * isoJ (n + 1) * Φ = 0) (j : Fin (n + 1)) :
    (cofactor_frame Φ j)ᴴ * isoJ (n + 1) * cofactor_frame Φ j = 0 := by
  rw [cofactor_frame_sandwich, h2]
  rfl

/-- For a frame satisfying (8.8) [up:eq:boundary-frame], `(U_j, Y)` is an isotropic flag. -/
theorem omitPair_mem_isoFlags {W : ℕ} {Φ : Matrix (Fin 2 × Fin W) (Fin W) ℂ}
    (hΦ : IsBoundaryFrame Φ) (j : Fin W) : omitPair Φ j ∈ isoFlags W := by
  rcases W with _ | n
  · exact j.elim0
  obtain ⟨h1, h2⟩ := hΦ
  have h1' := cofactor_frame_gram h1 j
  have h2' := cofactor_frame_isoJ h2 j
  obtain ⟨hUh, hUU, hUtr, hUJ⟩ := cofactor_gram_proj _ h1' h2'
  obtain ⟨hYh, hYY, hYtr, hYJ⟩ := cofactor_gram_proj Φ h1 h2
  have hPU : (omitPair Φ j).1 = cofactor_frame Φ j * (cofactor_frame Φ j)ᴴ :=
    (cofactor_frame_mul Φ j).symm
  have hPY : (omitPair Φ j).2 = Φ * Φᴴ := rfl
  have hYU : Φ * Φᴴ * (cofactor_frame Φ j * (cofactor_frame Φ j)ᴴ) =
      cofactor_frame Φ j * (cofactor_frame Φ j)ᴴ := by
    have hE : Φᴴ * cofactor_frame Φ j =
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).submatrix id j.succAbove := by
      rw [← h1]
      ext a b
      simp [cofactor_frame, Matrix.mul_apply, Matrix.submatrix_apply]
    have hF : Φ * (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).submatrix id j.succAbove =
        cofactor_frame Φ j := by
      ext a b
      simp [cofactor_frame, Matrix.mul_apply, Matrix.one_apply]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Φᴴ, hE, ← Matrix.mul_assoc, hF]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hPU]; exact hUh
  · rw [hPU]; exact hUU
  · rw [hPU, hUtr]; simp
  · rw [hPU]; exact hUJ
  · rw [hPY]; exact hYh
  · rw [hPY]; exact hYY
  · rw [hPY, hYtr]; simp
  · rw [hPY, hPU]; exact hYU
  · rw [hPY]; exact hYJ

/-- `J_ph² = 1`. -/
private theorem cofactor_phJ_mul_phJ (W : ℕ) : phJ W * phJ W = 1 := by
  unfold phJ
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have : (!![0, -Complex.I; Complex.I, 0] * !![0, -Complex.I; Complex.I, 0] :
      Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [this, Matrix.one_kronecker_one]

/-- `M* J_ph M = J_ph` forces `M` to be invertible. -/
private theorem cofactor_isUnit {W : ℕ} {M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hM : Mᴴ * phJ W * M = phJ W) : IsUnit M := by
  have h : (phJ W * Mᴴ * phJ W) * M = 1 := by
    calc phJ W * Mᴴ * phJ W * M = phJ W * (Mᴴ * phJ W * M) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hM, cofactor_phJ_mul_phJ]
  exact (Matrix.isUnit_iff_isUnit_det M).mpr (Matrix.isUnit_det_of_left_inverse h)

/-- (F.3) [cc:eq:cofactor] for `T = S* M S`: `e^{-c(T; U_j, Y)} = ‖e_j* D⁻¹‖` with
`D = √2 (I 0) T Φ = frameD M Φ`, for `M* J_ph M = J_ph` (Lemma F.2 [cc:lem:cofactor]). -/
theorem exp_neg_volCocycle_omitPair {W : ℕ} {M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hM : Mᴴ * phJ W * M = phJ W) {Φ : Matrix (Fin 2 × Fin W) (Fin W) ℂ} (hΦ : IsBoundaryFrame Φ)
    (j : Fin W) :
    Real.exp (-volCocycle ((freeConj W 0)ᴴ * M * freeConj W 0)
        ⟨omitPair Φ j, omitPair_mem_isoFlags hΦ j⟩) =
      Real.sqrt (∑ k, ‖(frameD M Φ)⁻¹ j k‖ ^ 2) := by
  rcases W with _ | n
  · exact j.elim0
  set S := freeConj (n + 1) 0 with hS
  set T := Sᴴ * M * S with hT
  set D := frameD M Φ with hD
  obtain ⟨hDu, -⟩ := frameD_spec hM (cofactor_isUnit hM) hΦ
  have hdetD : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hDu
  have hSS : S * Sᴴ = 1 := by
    have := freeConj_zero_mem_unitaryGroup (n + 1)
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at this
    exact this
  set G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Φᴴ * (Tᴴ * T) * Φ with hG
  have hGD : G = Dᴴ * D := by
    rw [← frameD_gram hM hΦ]
    calc G = (M * S * Φ)ᴴ * (S * Sᴴ) * (M * S * Φ) := by
          rw [hG, hT]
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
            Matrix.mul_assoc]
      _ = _ := by rw [hSS, Matrix.mul_one]
  have hdetG : IsUnit G.det := by
    rw [hGD, Matrix.det_mul, Matrix.det_conjTranspose]
    exact hdetD.star.mul hdetD
  -- the row norm
  set r : ℝ := ∑ k, ‖D⁻¹ j k‖ ^ 2 with hr
  have hr0 : 0 ≤ r := Finset.sum_nonneg fun _ _ => by positivity
  have hrpos : 0 < r := by
    refine lt_of_le_of_ne hr0 fun h0 => ?_
    have hz : ∀ k, D⁻¹ j k = 0 := fun k => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).mp h0.symm k
        (Finset.mem_univ _)
      simpa using this
    have h1 := congrFun (congrFun (Matrix.nonsing_inv_mul D hdetD) j) j
    simp [Matrix.mul_apply, hz] at h1
  have hGinv : G⁻¹ j j = (r : ℂ) := by
    rw [hGD, Matrix.mul_inv_rev, ← Matrix.conjTranspose_nonsing_inv, Matrix.mul_apply, hr]
    simp only [Matrix.conjTranspose_apply, Complex.ofReal_sum, Complex.ofReal_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, Complex.mul_conj']
  have hadj : Matrix.adjugate G = G.det • G⁻¹ := by
    calc Matrix.adjugate G = G⁻¹ * (G * Matrix.adjugate G) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetG, Matrix.one_mul]
      _ = G.det • G⁻¹ := by rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
  have hsub : (G.submatrix j.succAbove j.succAbove).det = G.det * (r : ℂ) := by
    have h := Matrix.adjugate_fin_succ_eq_det_submatrix G j j
    rw [hadj, Matrix.smul_apply, smul_eq_mul, hGinv, Even.neg_one_pow ⟨j, rfl⟩, one_mul] at h
    exact h.symm
  have hY : logVol T (omitPair Φ j).2 = Real.log ‖G.det‖ / 2 := by
    unfold logVol
    change Real.log ‖(Φ * Φᴴ * Tᴴ * T * (Φ * Φᴴ) + (1 - Φ * Φᴴ)).det‖ / 2 = _
    rw [det_flagGram_eq T hΦ.1]
    simp only [hG, Matrix.mul_assoc]
  have hU : logVol T (omitPair Φ j).1 =
      Real.log ‖(G.submatrix j.succAbove j.succAbove).det‖ / 2 := by
    have hPU : (omitPair Φ j).1 = cofactor_frame Φ j * (cofactor_frame Φ j)ᴴ :=
      (cofactor_frame_mul Φ j).symm
    unfold logVol
    rw [hPU, det_flagGram_eq T (cofactor_frame_gram hΦ.1 j)]
    have := cofactor_frame_sandwich Φ j (Tᴴ * T)
    simp only [hG, Matrix.mul_assoc] at this ⊢
    rw [this]
  have hG0 : 0 < ‖G.det‖ := norm_pos_iff.mpr hdetG.ne_zero
  have hn : ‖(G.submatrix j.succAbove j.succAbove).det‖ = ‖G.det‖ * r := by
    rw [hsub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0]
  change Real.exp (-(logVol T (omitPair Φ j).2 - logVol T (omitPair Φ j).1)) = _
  rw [hY, hU, hn, Real.log_mul hG0.ne' hrpos.ne', Real.sqrt_eq_rpow, Real.rpow_def_of_pos hrpos]
  congr 1
  ring

/-- The operator norm is at most the Hilbert–Schmidt norm. -/
private theorem cofactor_opNorm_le_hs {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (A : Matrix κ ι ℂ) :
    ‖A‖ ≤ Real.sqrt (∑ j, ∑ k, ‖A j k‖ ^ 2) := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  change ‖(EuclideanSpace.equiv κ ℂ).symm (A.mulVec x.ofLp)‖ ≤ _
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    ← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)]
  refine Real.sqrt_le_sqrt ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 : ((EuclideanSpace.equiv κ ℂ).symm (A *ᵥ x.ofLp)).ofLp j = ∑ i, A j i * x.ofLp i := rfl
  rw [h1]
  calc ‖∑ i, A j i * x.ofLp i‖ ^ 2 ≤ (∑ i, ‖A j i‖ * ‖x.ofLp i‖) ^ 2 := by
        gcongr
        exact (norm_sum_le _ _).trans (by simp)
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- Subadditivity of `x ↦ x^p` on finite sums of nonnegative reals, for `0 < p ≤ 1`. -/
private theorem cofactor_sum_rpow_le {ι : Type*} (s : Finset ι) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p ≤ 1) (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) : (∑ i ∈ s, f i) ^ p ≤ ∑ i ∈ s, f i ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow hp0.ne']
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    calc (f a + ∑ i ∈ s, f i) ^ p ≤ f a ^ p + (∑ i ∈ s, f i) ^ p :=
          Real.rpow_add_le_add_rpow (hf a) (Finset.sum_nonneg fun i _ => hf i) hp0.le hp1
      _ ≤ _ := by gcongr

/-- `‖A‖^s ≤ Σ_j ‖e_j* A‖^s` for `0 < s ≤ 2` (operator norm ≤ Hilbert–Schmidt norm, then
concavity; proof of (8.23) [eq:c-inverse-cocycle]). -/
theorem norm_rpow_le_sum_row_rpow {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (A : Matrix κ ι ℂ) {s : ℝ} (hs0 : 0 < s) (hs2 : s ≤ 2) :
    ‖A‖ ^ s ≤ ∑ j, Real.sqrt (∑ k, ‖A j k‖ ^ 2) ^ s := by
  have h0 : ∀ j, 0 ≤ ∑ k, ‖A j k‖ ^ 2 := fun j => Finset.sum_nonneg fun _ _ => by positivity
  have h1 : ‖A‖ ≤ (∑ j, ∑ k, ‖A j k‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]; exact cofactor_opNorm_le_hs A
  calc ‖A‖ ^ s ≤ ((∑ j, ∑ k, ‖A j k‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ s :=
        Real.rpow_le_rpow (norm_nonneg _) h1 hs0.le
    _ = (∑ j, ∑ k, ‖A j k‖ ^ 2) ^ (s / 2) := by
        rw [← Real.rpow_mul (Finset.sum_nonneg fun j _ => h0 j)]; congr 1; ring
    _ ≤ ∑ j, (∑ k, ‖A j k‖ ^ 2) ^ (s / 2) :=
        cofactor_sum_rpow_le _ (by positivity) (by linarith) _ h0
    _ = ∑ j, Real.sqrt (∑ k, ‖A j k‖ ^ 2) ^ s := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (h0 j)]; congr 1; ring

/-- (F.4) [cc:eq:inverse] for `T = S* M S`, for every `0 < s ≤ 2` (Lemma F.2
[cc:lem:cofactor]). -/
theorem norm_frameD_inv_rpow_le {W : ℕ} {M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hM : Mᴴ * phJ W * M = phJ W) {Φ : Matrix (Fin 2 × Fin W) (Fin W) ℂ} (hΦ : IsBoundaryFrame Φ)
    {s : ℝ} (hs0 : 0 < s) (hs2 : s ≤ 2) :
    ‖(frameD M Φ)⁻¹‖ ^ s ≤
      ∑ j, Real.exp (-s * volCocycle ((freeConj W 0)ᴴ * M * freeConj W 0)
        ⟨omitPair Φ j, omitPair_mem_isoFlags hΦ j⟩) := by
  have h := norm_rpow_le_sum_row_rpow (frameD M Φ)⁻¹ hs0 hs2
  refine h.trans (Finset.sum_le_sum fun j _ => le_of_eq ?_)
  rw [← exp_neg_volCocycle_omitPair hM hΦ j, ← Real.exp_mul]
  congr 1
  ring

end LSBA
