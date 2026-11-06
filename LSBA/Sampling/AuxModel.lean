import LSBA.Primitive.Defs
import LSBA.Gauss.Concentration

/-!
# The auxiliary model of Lemma 5.4 [uvc:lem:orbital-limit]

The block model of width `W̃` with deterministic part `Hdet g` and Gaussian blocks of variance
`tγ_g/W̃` at the characteristic spectral parameter, its normalized expected loops, their value
at `t = 0` (the primitive loops), the variance bound `O(W̃^{-2})` from the Gaussian Poincaré
inequality and the one-loop mean field `|E⟨G⟩_cc − m| ≤ C/W̃` used in the proof of Lemma 5.4
[uvc:lem:orbital-limit].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The resolvent `G_t^{(W̃)} = (A_g ⊗ I + √(tγ_g) V - z_t)⁻¹` of the auxiliary width-`W̃` model of
Lemma 5.4 [uvc:lem:orbital-limit] at a fixed time `t`. -/
def auxG (g : ℝ) (Wt L : ℕ) (E : ℝ) (m : ℂ) (t : ℝ) (ω : Ω Wt L) :
    Matrix (Fin L × Fin Wt) (Fin L × Fin Wt) ℂ :=
  (Hdet g (fun b => ((Real.sqrt t : ℝ) : ℂ) • gueBlock Wt L ω b) -
    zChar g E m t • (1 : Matrix (Fin L × Fin Wt) (Fin L × Fin Wt) ℂ))⁻¹

/-- The normalized expected loops `W̃^{k-1} E ℒ_k^{(W̃)}(t)` of the auxiliary model. -/
def auxLoop (g : ℝ) (Wt L : ℕ) (E : ℝ) (m : ℂ) (t : ℝ) : LoopFam L :=
  fun k a σ => (Wt : ℂ) ^ (k - 1) * ∫ ω, loopTr (auxG g Wt L E m t ω) a σ ∂(μ Wt L)

/-- At `t = 0` the auxiliary loops are the primitive loops, (5.3) [fo:eq:characteristic]. -/
theorem auxLoop_init (g : ℝ) (L : ℕ) (hL : 3 ≤ L) (E : ℝ) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (Wt : ℕ) (hWt : 1 ≤ Wt) (k : ℕ) (hk : 1 ≤ k)
    (a : Fin k → Fin L) (σ : Fin k → Bool) :
    auxLoop g Wt L E m 0 k a σ = primLoopF g L E m 0 a σ := by
  have hG : ∀ ω, auxG g Wt L E m 0 ω =
      dysonMat (hopB g) (gammaG g) L E m ⊗ₖ (1 : Matrix (Fin Wt) (Fin Wt) ℂ) := by
    intro ω
    have hk := Matrix.inv_kronecker ((hopB g : ℂ) • cycleAdj L -
      ((E : ℂ) + (gammaG g : ℂ) * m) • (1 : Matrix (Fin L) (Fin L) ℂ))
      (1 : Matrix (Fin Wt) (Fin Wt) ℂ)
    rw [inv_one] at hk
    rw [auxG, dysonMat, ← hk]
    congr 1
    ext ⟨b, α⟩ ⟨c, β⟩
    simp only [Hdet, zChar, blockDiagOp, hopB, Real.sqrt_zero, Complex.ofReal_zero,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, smul_eq_mul,
      Prod.mk.injEq, sub_zero, one_mul]
    split_ifs <;> (try tauto) <;> push_cast <;> ring
  have hW : (Wt : ℂ) ≠ 0 := by exact_mod_cast (by omega : Wt ≠ 0)
  simp only [auxLoop, hG, integral_const, probReal_univ, one_smul]
  rw [← primLoop_init g Wt L hWt hL E m hm a σ]
  change (Wt : ℂ) ^ (k - 1) * ((Wt : ℂ) ^ (1 - (k : ℤ)) * primLoopF g L E m 0 a σ) = _
  rw [← mul_assoc, ← zpow_natCast, ← zpow_add₀ hW, Nat.cast_sub hk]
  simp

section Generic

open scoped Matrix.Norms.L2Operator InnerProductSpace

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `A - z` is invertible for Hermitian `A` and `Im z ≠ 0`. -/
private lemma auxModel_isUnit {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
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

/-- `|Im z| ‖v‖ ≤ ‖(A - z) v‖` for Hermitian `A`. -/
private lemma auxModel_abs_im_mul_norm_le {A : Matrix n n ℂ} (hA : A.IsHermitian) (z : ℂ)
    (v : EuclideanSpace ℂ n) :
    |z.im| * ‖v‖ ≤ ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (A - z • (1 : Matrix n n ℂ)) v‖ := by
  set T := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (A - z • (1 : Matrix n n ℂ)) with hT
  have hTv : T v = Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A v - z • v := by
    simp [hT, map_sub, map_smul]
  have hinner : ⟪v, T v⟫_ℂ
      = ⟪v, Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A v⟫_ℂ - z * ⟪v, v⟫_ℂ := by
    rw [hTv, inner_sub_right, inner_smul_right]
  have hA0 : (⟪v, Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A v⟫_ℂ).im = 0 := by
    have := hA.im_star_dotProduct_mulVec_self (WithLp.ofLp v)
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simpa [dotProduct_comm] using this
  have hvv_im : (⟪v, v⟫_ℂ).im = 0 := by
    simpa [RCLike.im_to_complex] using inner_self_im (𝕜 := ℂ) v
  have hvv_re : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := by
    simpa [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜 := ℂ) v
  have him : (⟪v, T v⟫_ℂ).im = -(z.im * ‖v‖ ^ 2) := by
    rw [hinner, Complex.sub_im, Complex.mul_im, hvv_im, hvv_re, hA0]
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

/-- `‖(A - z)⁻¹‖ ≤ η⁻¹` for Hermitian `A` and `η ≤ |Im z|`, `η > 0`. -/
private lemma auxModel_norm_inv_le {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ} {η : ℝ}
    (hη : 0 < η) (hz : η ≤ |z.im|) : ‖(A - z • (1 : Matrix n n ℂ))⁻¹‖ ≤ η⁻¹ := by
  have hzim : z.im ≠ 0 := fun h => absurd hz (by rw [h]; simpa using hη)
  set B : Matrix n n ℂ := A - z • (1 : Matrix n n ℂ) with hB
  have hBu : IsUnit B := auxModel_isUnit hA hzim
  have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hBu
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
  have hkey := auxModel_abs_im_mul_norm_le hA z w
  rw [hBw] at hkey
  have hfin : η * ‖w‖ ≤ ‖v‖ := le_trans (by nlinarith [norm_nonneg w]) hkey
  rw [inv_mul_eq_div, le_div_iff₀ hη]
  linarith [hfin]

/-- Ward identity `G - G* = (z - z̄) G G*` for `G = (A - z)⁻¹`, `A` Hermitian, `Im z ≠ 0`. -/
private lemma auxModel_ward {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    (A - z • (1 : Matrix n n ℂ))⁻¹ - ((A - z • (1 : Matrix n n ℂ))⁻¹)ᴴ =
      (z - starRingEnd ℂ z) •
        ((A - z • (1 : Matrix n n ℂ))⁻¹ * ((A - z • (1 : Matrix n n ℂ))⁻¹)ᴴ) := by
  set B : Matrix n n ℂ := A - z • (1 : Matrix n n ℂ) with hB
  have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp (auxModel_isUnit hA hz)
  have hNB : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul _ hdet
  have hBHN : Bᴴ * (B⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.conjTranspose_one]
  have hBN : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hBH : Bᴴ - B = (z - starRingEnd ℂ z) • (1 : Matrix n n ℂ) := by
    rw [hB, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hA.eq, Matrix.conjTranspose_one,
      sub_smul]
    simp only [Complex.star_def]
    abel
  clear_value B
  calc B⁻¹ - (B⁻¹)ᴴ = B⁻¹ * (Bᴴ * (B⁻¹)ᴴ) - (B⁻¹ * B) * (B⁻¹)ᴴ := by
        rw [hBHN, hNB, Matrix.mul_one, Matrix.one_mul]
    _ = B⁻¹ * (Bᴴ - B) * (B⁻¹)ᴴ := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = _ := by rw [hBH, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- `Im G_{xx} = Im z · Σ_y |G_{xy}|²` for `G = (A - z)⁻¹`. -/
private lemma auxModel_im_diag {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (x : n) :
    ((A - z • (1 : Matrix n n ℂ))⁻¹ x x).im =
      z.im * ∑ y, ‖(A - z • (1 : Matrix n n ℂ))⁻¹ x y‖ ^ 2 := by
  have h := congrFun (congrFun (auxModel_ward hA hz) x) x
  set G := (A - z • (1 : Matrix n n ℂ))⁻¹
  simp only [Matrix.sub_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.mul_apply,
    smul_eq_mul] at h
  have hs : ∑ y, G x y * star (G x y) = ((∑ y, ‖G x y‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Complex.star_def, Complex.mul_conj']
  rw [hs] at h
  have him := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.mul_im,
    Complex.ofReal_im, Complex.ofReal_re, Complex.sub_re, Complex.conj_re, sub_self,
    mul_zero] at him
  linarith

/-- Hilbert–Schmidt norm `(Σ_{ij} |X_ij|²)^{1/2}`. -/
private def auxModel_hs (X : Matrix n n ℂ) : ℝ := Real.sqrt (∑ i, ∑ j, ‖X i j‖ ^ 2)

omit [DecidableEq n] in
private lemma auxModel_hs_nonneg (X : Matrix n n ℂ) : 0 ≤ auxModel_hs X := Real.sqrt_nonneg _

omit [DecidableEq n] in
private lemma auxModel_hs_sq (X : Matrix n n ℂ) :
    auxModel_hs X ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)

/-- Columnwise `Σ |(Y X)_ij|² ≤ ‖Y‖² Σ |X_ij|²`. -/
private lemma auxModel_sum_sq_mul_left (Y X : Matrix n n ℂ) :
    ∑ i, ∑ j, ‖(Y * X) i j‖ ^ 2 ≤ ‖Y‖ ^ 2 * ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => ‖X i j‖ ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  set x : EuclideanSpace ℂ n := (EuclideanSpace.equiv n ℂ).symm (fun i => X i j) with hx
  have h := Matrix.l2_opNorm_mulVec Y x
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  simpa [hx, Matrix.mul_apply, Matrix.mulVec, dotProduct] using h2

omit [DecidableEq n] in
private lemma auxModel_sum_sq_conjTranspose (X : Matrix n n ℂ) :
    ∑ i, ∑ j, ‖Xᴴ i j‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  rw [Finset.sum_comm]; simp [Matrix.conjTranspose_apply]

/-- `‖Y X‖_HS ≤ ‖Y‖ ‖X‖_HS`. -/
private lemma auxModel_hs_mul_left (Y X : Matrix n n ℂ) :
    auxModel_hs (Y * X) ≤ ‖Y‖ * auxModel_hs X := by
  rw [auxModel_hs, auxModel_hs, ← Real.sqrt_sq (norm_nonneg Y), ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt (auxModel_sum_sq_mul_left Y X)

/-- `‖X Y‖_HS ≤ ‖X‖_HS ‖Y‖`. -/
private lemma auxModel_hs_mul_right (X Y : Matrix n n ℂ) :
    auxModel_hs (X * Y) ≤ auxModel_hs X * ‖Y‖ := by
  have h := auxModel_sum_sq_mul_left Yᴴ Xᴴ
  rw [← Matrix.conjTranspose_mul, Matrix.l2_opNorm_conjTranspose,
    auxModel_sum_sq_conjTranspose, auxModel_sum_sq_conjTranspose] at h
  rw [auxModel_hs, auxModel_hs, mul_comm, ← Real.sqrt_sq (norm_nonneg Y),
    ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt h

omit [DecidableEq n] in
/-- Cauchy–Schwarz for the trace: `|Tr(X Y)| ≤ ‖X‖_HS ‖Y‖_HS`. -/
private lemma auxModel_norm_trace_mul_le (X Y : Matrix n n ℂ) :
    ‖(X * Y).trace‖ ≤ auxModel_hs X * auxModel_hs Y := by
  have h1 : ‖(X * Y).trace‖ ≤ ∑ i, ∑ j, ‖X i j‖ * ‖Y j i‖ := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
  have h2 : ∑ i, ∑ j, ‖X i j‖ * ‖Y j i‖ ≤
      Real.sqrt (∑ i, ∑ j, ‖X i j‖ ^ 2) * Real.sqrt (∑ i, ∑ j, ‖Y j i‖ ^ 2) := by
    rw [← Finset.sum_product', ← Finset.sum_product', ← Finset.sum_product']
    exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  refine h1.trans (h2.trans (le_of_eq ?_))
  rw [auxModel_hs, auxModel_hs, Finset.sum_comm (f := fun i j => ‖Y j i‖ ^ 2)]

/-- An entry is bounded by the operator norm. -/
private lemma auxModel_norm_entry_le (X : Matrix n n ℂ) (i j : n) : ‖X i j‖ ≤ ‖X‖ := by
  have h := auxModel_sum_sq_mul_left X (Matrix.diagonal (Pi.single j 1))
  have e1 : ∑ i', ∑ j', ‖(X * Matrix.diagonal (Pi.single j (1 : ℂ)) : Matrix n n ℂ) i' j'‖ ^ 2 =
      ∑ i', ‖X i' j‖ ^ 2 := by
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Finset.sum_eq_single j]
    · simp [Matrix.mul_diagonal]
    · intro b _ hb; simp [Matrix.mul_diagonal, hb]
    · simp
  have e2 : ∑ i', ∑ j', ‖(Matrix.diagonal (Pi.single j (1 : ℂ)) : Matrix n n ℂ) i' j'‖ ^ 2 =
      1 := by
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    · intro b _ hb
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hbc : b = c
      · subst hbc; simp [hb]
      · simp [hbc]
    · simp
  rw [e1, e2, mul_one] at h
  have h3 : ‖X i j‖ ^ 2 ≤ ‖X‖ ^ 2 :=
    le_trans (Finset.single_le_sum (f := fun i' => ‖X i' j‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ i)) h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h3

/-- The inverse along an affine family `x ↦ K₀ + T x` of invertible matrices has derivative
`v ↦ -(G (T v) G)`. -/
private lemma auxModel_hasFDerivAt_inv {ι : Type*} [Fintype ι] (K₀ : Matrix n n ℂ)
    (T : (ι → ℝ) →L[ℝ] Matrix n n ℂ) (x : ι → ℝ) (hu : IsUnit (K₀ + T x)) :
    HasFDerivAt (fun y => (K₀ + T y)⁻¹)
      ((-(ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (K₀ + T x)⁻¹ (K₀ + T x)⁻¹)).comp T)
      x := by
  set u : (Matrix n n ℂ)ˣ := hu.unit
  have hus : (u : Matrix n n ℂ) = K₀ + T x := IsUnit.unit_spec _
  have hinv : ((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ) = (K₀ + T x)⁻¹ := by
    rw [← hus, Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit]
  have hF : HasFDerivAt (Ring.inverse (M₀ := Matrix n n ℂ))
      (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) ↑u⁻¹) ↑u⁻¹) (K₀ + T x) := by
    rw [← hus]; exact hasFDerivAt_ringInverse u
  rw [hinv] at hF
  have hA : HasFDerivAt (fun y => K₀ + T y) T x := T.hasFDerivAt.const_add K₀
  have := hF.comp x hA
  simpa [Function.comp_def, Matrix.nonsing_inv_eq_ringInverse] using this

/-- The inverse along an affine family of invertible matrices is smooth. -/
private lemma auxModel_contDiff_inv {ι : Type*} [Fintype ι] (K₀ : Matrix n n ℂ)
    (T : (ι → ℝ) →L[ℝ] Matrix n n ℂ) (hu : ∀ x, IsUnit (K₀ + T x)) :
    ContDiff ℝ 1 (fun y => (K₀ + T y)⁻¹) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  set u : (Matrix n n ℂ)ˣ := (hu x).unit
  have hus : (u : Matrix n n ℂ) = K₀ + T x := IsUnit.unit_spec _
  have h1 : ContDiffAt ℝ 1 (Ring.inverse (M₀ := Matrix n n ℂ)) (K₀ + T x) := by
    rw [← hus]; exact contDiffAt_ringInverse ℝ u
  have h2 : ContDiffAt ℝ 1 (fun y => K₀ + T y) x :=
    (contDiff_const.add T.contDiff).contDiffAt
  simpa [Function.comp_def, Matrix.nonsing_inv_eq_ringInverse] using h1.comp x h2

end Generic

section Model

open scoped Matrix.Norms.L2Operator

/-- `gueBlock` is additive in the sample. -/
private lemma auxModel_gueBlock_add (W L : ℕ) (ω ω' : Ω W L) (a : Fin L) :
    gueBlock W L (ω + ω') a = gueBlock W L ω a + gueBlock W L ω' a := by
  ext α β
  simp only [gueBlock, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> push_cast <;> ring

/-- `gueBlock` is real-homogeneous in the sample. -/
private lemma auxModel_gueBlock_smul (W L : ℕ) (c : ℝ) (ω : Ω W L) (a : Fin L) :
    gueBlock W L (c • ω) a = (c : ℂ) • gueBlock W L ω a := by
  ext α β
  simp only [gueBlock, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

/-- The block-diagonal GUE matrix `diag(V_b)` as a real-linear map of the coordinates. -/
private def auxModel_D (W L : ℕ) : Ω W L →L[ℝ] Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ω => blockDiagOp (gueBlock W L ω)
      map_add' := fun ω ω' => by
        ext p q
        simp only [blockDiagOp, Matrix.of_apply, Matrix.add_apply, auxModel_gueBlock_add]
        split_ifs <;> simp
      map_smul' := fun c ω => by
        ext p q
        simp only [blockDiagOp, Matrix.of_apply, Matrix.smul_apply, auxModel_gueBlock_smul,
          RingHom.id_apply]
        split_ifs <;> simp [Complex.real_smul] }

private lemma auxModel_D_apply (W L : ℕ) (ω : Ω W L) :
    auxModel_D W L ω = blockDiagOp (gueBlock W L ω) := rfl

/-- The deterministic part `A_g ⊗ I - z_t` of the shifted auxiliary Hamiltonian. -/
private def auxModel_K (g : ℝ) (W L : ℕ) (E : ℝ) (m : ℂ) (t : ℝ) :
    Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  ((hopB g : ℝ) : ℂ) • (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) -
    zChar g E m t • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)

/-- The random part `√(tγ_g) V` of the auxiliary Hamiltonian as a real-linear map. -/
private def auxModel_T (g : ℝ) (W L : ℕ) (t : ℝ) :
    Ω W L →L[ℝ] Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  ((max 1 g)⁻¹ * Real.sqrt t) • auxModel_D W L

/-- The auxiliary Hamiltonian minus `z_t` is `K + T ω`. -/
private lemma auxModel_H_eq (g : ℝ) (W L : ℕ) (E : ℝ) (m : ℂ) (t : ℝ) (ω : Ω W L) :
    Hdet g (fun b => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω b) -
        zChar g E m t • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) =
      auxModel_K g W L E m t + auxModel_T g W L t ω := by
  ext p q
  simp only [Hdet, auxModel_K, auxModel_T, smul_apply, auxModel_D_apply,
    blockDiagOp, hopB, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
    smul_eq_mul, Complex.real_smul]
  split_ifs <;> push_cast <;> ring

/-- The auxiliary Hamiltonian is Hermitian. -/
private lemma auxModel_A_herm (g : ℝ) (W L : ℕ) (t : ℝ) (ω : Ω W L) :
    (Hdet g (fun b => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω b)).IsHermitian := by
  refine Hdet_isHermitian g fun b => ?_
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, (gueBlock_isHermitian W L ω b).eq]
  simp [Complex.conj_ofReal]

/-- `auxG` is the inverse of `K + T ω`. -/
private lemma auxModel_G_eq (g : ℝ) (W L : ℕ) (E : ℝ) (m : ℂ) (t : ℝ) (ω : Ω W L) :
    auxG g W L E m t ω = (auxModel_K g W L E m t + auxModel_T g W L t ω)⁻¹ := by
  rw [auxG, auxModel_H_eq]

/-- `Im z_t = (1 - t) γ_g Im m`. -/
private lemma auxModel_im_zChar (g E : ℝ) (m : ℂ) (t : ℝ) :
    (zChar g E m t).im = (1 - t) * gammaG g * m.im := by
  simp [zChar, Complex.add_im, Complex.mul_im]

end Model

section Deriv

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Product rule for an ordered product of `k` differentiable matrix curves. -/
private lemma auxModel_hasDerivAt_prod :
    ∀ (k : ℕ) (A : Fin k → ℝ → Matrix n n ℂ) (A' : Fin k → Matrix n n ℂ) (s : ℝ),
      (∀ j, HasDerivAt (A j) (A' j) s) →
      HasDerivAt (fun s => (List.ofFn fun j => A j s).prod)
        (∑ j : Fin k, ((List.ofFn fun i => A i s).take j).prod * A' j *
          ((List.ofFn fun i => A i s).drop (j + 1)).prod) s
  | 0, A, A', s, _ => by simpa using hasDerivAt_const s (1 : Matrix n n ℂ)
  | k + 1, A, A', s, h => by
    have ih := auxModel_hasDerivAt_prod k (fun j => A j.succ) (fun j => A' j.succ) s
      (fun j => h j.succ)
    have hm := (h 0).fun_mul ih
    simp only [List.ofFn_succ, List.prod_cons]
    convert hm using 1
    rw [Fin.sum_univ_succ, Finset.mul_sum]
    simp only [Fin.val_zero, List.take_zero, List.prod_nil, one_mul, zero_add, Fin.val_succ,
      List.take_succ_cons, List.prod_cons, List.drop_succ_cons, List.drop_zero, mul_assoc]

/-- The trace as a real-linear continuous map. -/
private def auxModel_trCLM : Matrix n n ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap ((Matrix.traceLinearMap n ℂ ℂ).restrictScalars ℝ)

omit [DecidableEq n] in
private lemma auxModel_trCLM_apply (X : Matrix n n ℂ) : auxModel_trCLM X = X.trace := rfl

/-- The conjugate transpose as a real-linear continuous map. -/
private def auxModel_ctCLM : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => Xᴴ
      map_add' := Matrix.conjTranspose_add
      map_smul' := fun c X => by simp [Matrix.conjTranspose_smul] }

/-- `X ↦ X^σ` is smooth. -/
private lemma auxModel_contDiff_sgnMat (σ : Bool) :
    ContDiff ℝ 1 (fun X : Matrix n n ℂ => sgnMat X σ) := by
  cases σ
  · exact (auxModel_ctCLM (n := n)).contDiff
  · exact contDiff_id

/-- An ordered product of smooth matrix functions is smooth. -/
private lemma auxModel_contDiff_prod {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ∀ (k : ℕ) (A : Fin k → F → Matrix n n ℂ), (∀ j, ContDiff ℝ 1 (A j)) →
      ContDiff ℝ 1 (fun x => (List.ofFn fun j => A j x).prod)
  | 0, A, _ => by simpa using contDiff_const
  | k + 1, A, h => by
    simp only [List.ofFn_succ, List.prod_cons]
    exact (h 0).mul (auxModel_contDiff_prod k (fun j => A j.succ) (fun j => h j.succ))

omit [Fintype n] [DecidableEq n] in
/-- `X^σ` along a line. -/
private lemma auxModel_sgnMat_line (X Y : Matrix n n ℂ) (s : ℝ) (σ : Bool) :
    sgnMat (X + s • Y) σ = sgnMat X σ + s • sgnMat Y σ := by
  cases σ <;> simp [sgnMat, Matrix.conjTranspose_add, Matrix.conjTranspose_smul]

end Deriv

section LoopDeriv

open scoped Matrix.Norms.L2Operator

/-- The loop is a smooth function of the matrix. -/
private lemma auxModel_contDiff_loopTr {W L k : ℕ} (a : Fin k → Fin L) (σ : Fin k → Bool) :
    ContDiff ℝ 1 (fun X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ => loopTr X a σ) := by
  unfold loopTr
  have h := auxModel_contDiff_prod (F := Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) k
    (fun j X => sgnMat X (σ j) * blockE W L (a j))
    (fun j => (auxModel_contDiff_sgnMat (σ j)).mul contDiff_const)
  exact auxModel_trCLM.contDiff.comp h

/-- Derivative of the loop along the line `X + sY` at `s = 0`. -/
private lemma auxModel_hasDerivAt_loopTr {W L k : ℕ}
    (X Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a : Fin k → Fin L) (σ : Fin k → Bool) :
    HasDerivAt (fun s : ℝ => loopTr (X + s • Y) a σ)
      (∑ j : Fin k, (((List.ofFn fun i => sgnMat X (σ i) * blockE W L (a i)).take j).prod *
        (sgnMat Y (σ j) * blockE W L (a j)) *
        ((List.ofFn fun i => sgnMat X (σ i) * blockE W L (a i)).drop (j + 1)).prod).trace) 0 := by
  have hA : ∀ j : Fin k, HasDerivAt (fun s : ℝ => sgnMat (X + s • Y) (σ j) * blockE W L (a j))
      (sgnMat Y (σ j) * blockE W L (a j)) 0 := by
    intro j
    simp only [auxModel_sgnMat_line, Matrix.add_mul, Matrix.smul_mul]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (sgnMat Y (σ j) * blockE W L (a j))).const_add
      (sgnMat X (σ j) * blockE W L (a j))
  have hp := auxModel_hasDerivAt_prod k (fun j s => sgnMat (X + s • Y) (σ j) * blockE W L (a j))
    (fun j => sgnMat Y (σ j) * blockE W L (a j)) 0 hA
  have ht := auxModel_trCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hp
  simp only [zero_smul, add_zero] at ht
  unfold loopTr
  rw [auxModel_trCLM_apply, Matrix.trace_sum] at ht
  exact ht

end LoopDeriv

section Bounds

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `‖1‖ ≤ 1` for the operator norm. -/
private lemma auxModel_norm_one_le : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by simp

/-- A product of factors of norm at most `ρ` has norm at most `ρ ^ length`. -/
private lemma auxModel_norm_prod_le {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∀ l : List (Matrix n n ℂ), (∀ x ∈ l, ‖x‖ ≤ ρ) → ‖l.prod‖ ≤ ρ ^ l.length
  | [], _ => by simpa using auxModel_norm_one_le
  | x :: l, h => by
    rw [List.prod_cons, List.length_cons, pow_succ']
    calc ‖x * l.prod‖ ≤ ‖x‖ * ‖l.prod‖ := norm_mul_le _ _
      _ ≤ ρ * ρ ^ l.length :=
          mul_le_mul (h x (by simp)) (auxModel_norm_prod_le hρ l fun y hy => h y (by simp [hy]))
            (norm_nonneg _) hρ

/-- `‖X^σ‖ = ‖X‖`. -/
private lemma auxModel_norm_sgnMat (X : Matrix n n ℂ) (σ : Bool) : ‖sgnMat X σ‖ = ‖X‖ := by
  cases σ
  · exact Matrix.l2_opNorm_conjTranspose X
  · rfl

omit [DecidableEq n] in
/-- `‖r X‖_HS = |r| ‖X‖_HS` for real `r`. -/
private lemma auxModel_hs_smul (r : ℝ) (X : Matrix n n ℂ) :
    auxModel_hs (r • X) = |r| * auxModel_hs X := by
  rw [auxModel_hs, auxModel_hs, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _),
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- One term of the derivative of a loop: the inserted factor `-(X^σ Z X^σ) E` is paired with
the Hilbert–Schmidt norms of `Z` and `E`. -/
private lemma auxModel_term_le (P D X Z E : Matrix n n ℂ) (hZ : Z.IsHermitian) (σ : Bool) :
    ‖(P * (sgnMat (-(X * Z * X)) σ * E) * D).trace‖ ≤
      auxModel_hs Z * (‖X‖ * (auxModel_hs E * (‖D‖ * ‖P‖ * ‖X‖))) := by
  set S := sgnMat X σ with hS
  have hsg : sgnMat (-(X * Z * X)) σ = -(S * Z * S) := by
    cases σ
    · simp [hS, sgnMat, Matrix.conjTranspose_mul, hZ.eq, Matrix.mul_assoc]
    · simp [hS, sgnMat]
  have h1 : P * (-(S * Z * S) * E) * D = -((P * S) * (Z * (S * E * D))) := by
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  rw [hsg, h1, Matrix.trace_neg, norm_neg, Matrix.trace_mul_comm, Matrix.mul_assoc]
  refine (auxModel_norm_trace_mul_le _ _).trans ?_
  gcongr
  · exact auxModel_hs_nonneg _
  · rw [← auxModel_norm_sgnMat X σ, ← hS]
    calc auxModel_hs (S * E * D * (P * S)) = auxModel_hs (S * (E * (D * P * S))) := by
          simp only [Matrix.mul_assoc]
      _ ≤ ‖S‖ * auxModel_hs (E * (D * P * S)) := auxModel_hs_mul_left _ _
      _ ≤ ‖S‖ * (auxModel_hs E * ‖D * P * S‖) := by
          gcongr; exact auxModel_hs_mul_right _ _
      _ ≤ ‖S‖ * (auxModel_hs E * (‖D‖ * ‖P‖ * ‖S‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left norm_mul₃_le (auxModel_hs_nonneg E))
            (norm_nonneg S)

omit [DecidableEq n] in
/-- Gradient bound for a real-linear functional: if `|D v| ≤ K |v|₂` then
`Σ_i |D e_i|² ≤ 2K²`. -/
private lemma auxModel_sum_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι] (D : (ι → ℝ) →L[ℝ] ℂ)
    {K : ℝ} (hK : 0 ≤ K) (h : ∀ v, ‖D v‖ ≤ K * Real.sqrt (∑ i, v i ^ 2)) :
    ∑ i, ‖D (Pi.single i 1)‖ ^ 2 ≤ 2 * K ^ 2 := by
  have hdec : ∀ v : ι → ℝ, D v = ∑ i, (v i : ℂ) * D (Pi.single i 1) := by
    intro v
    conv_lhs => rw [show v = ∑ i, v i • (Pi.single i (1 : ℝ) : ι → ℝ) by
      ext j; simp [Finset.sum_apply, Pi.single_apply]]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Complex.real_smul]
  have key : ∀ (u : ι → ℝ), (∀ i, u i = (D (Pi.single i 1)).re) ∨
      (∀ i, u i = (D (Pi.single i 1)).im) → ∑ i, u i ^ 2 ≤ K ^ 2 := by
    intro u hu
    set S := ∑ i, u i ^ 2 with hSdef
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hle : S ≤ K * Real.sqrt S := by
      refine le_trans ?_ (h u)
      rw [hdec u]
      rcases hu with hu | hu
      · refine le_trans (le_of_eq ?_) (Complex.re_le_norm _)
        rw [Complex.re_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.re_ofReal_mul, ← hu i, sq]
      · refine le_trans (le_of_eq ?_) (Complex.im_le_norm _)
        rw [Complex.im_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.im_ofReal_mul, ← hu i, sq]
    have hsq : Real.sqrt S ≤ K := by
      rcases eq_or_lt_of_le (Real.sqrt_nonneg S) with h0 | h0
      · rw [← h0]; exact hK
      · have : Real.sqrt S * Real.sqrt S ≤ K * Real.sqrt S := by
          rw [Real.mul_self_sqrt hS0]; exact hle
        exact le_of_mul_le_mul_right this h0
    calc S = Real.sqrt S ^ 2 := (Real.sq_sqrt hS0).symm
      _ ≤ K ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 2
  have h1 := key (fun i => (D (Pi.single i 1)).re) (Or.inl fun _ => rfl)
  have h2 := key (fun i => (D (Pi.single i 1)).im) (Or.inr fun _ => rfl)
  calc ∑ i, ‖D (Pi.single i 1)‖ ^ 2 =
        ∑ i, (D (Pi.single i 1)).re ^ 2 + ∑ i, (D (Pi.single i 1)).im ^ 2 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
    _ ≤ 2 * K ^ 2 := by linarith

omit [DecidableEq n] in
/-- Operator-norm bound for a real-linear functional with `|D v| ≤ K |v|₂`. -/
private lemma auxModel_opNorm_le {ι : Type*} [Fintype ι] (D : (ι → ℝ) →L[ℝ] ℂ)
    {K : ℝ} (hK : 0 ≤ K) (h : ∀ v, ‖D v‖ ≤ K * Real.sqrt (∑ i, v i ^ 2)) :
    ‖D‖ ≤ K * Real.sqrt (Fintype.card ι) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  refine (h v).trans ?_
  rw [mul_assoc]
  gcongr
  rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (Nat.cast_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, v i ^ 2 ≤ ∑ _i : ι, ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ => by
        have := norm_le_pi_norm v i
        rw [Real.norm_eq_abs] at this
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Bounds

section ModelBounds

open scoped Matrix.Norms.L2Operator

/-- `‖E_a‖ ≤ W⁻¹`. -/
private lemma auxModel_norm_blockE_le (W L : ℕ) (a : Fin L) : ‖blockE W L a‖ ≤ (W : ℝ)⁻¹ := by
  rw [blockE, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun p => ?_
  split_ifs <;> simp

/-- `‖E_a‖_HS = W^{-1/2}`. -/
private lemma auxModel_hs_blockE (W L : ℕ) (a : Fin L) :
    auxModel_hs (blockE W L a) = Real.sqrt (W : ℝ)⁻¹ := by
  rw [auxModel_hs]
  congr 1
  have h : ∀ p : Fin L × Fin W, ∑ q, ‖blockE W L a p q‖ ^ 2 =
      if p.1 = a then ((W : ℝ)⁻¹) ^ 2 else 0 := by
    intro p
    rw [Finset.sum_eq_single p]
    · simp only [blockE, Matrix.diagonal_apply_eq]
      split_ifs <;> simp
    · intro q _ hq; simp [blockE, Matrix.diagonal_apply_ne _ (Ne.symm hq)]
    · simp
  simp only [h, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp only [ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos W with h0 | h0
    · simp [h0]
    · field_simp
  · intro b _ hb; simp [hb]
  · simp

/-- `|V_{αβ}|² ≤ (ω_{αβ}² + ω_{βα}²)/W` for the GUE block entries. -/
private lemma auxModel_gueBlock_entry_sq (W L : ℕ) (v : Ω W L) (b : Fin L) (α β : Fin W) :
    ‖gueBlock W L v b α β‖ ^ 2 ≤ (v (b, α, β) ^ 2 + v (b, β, α) ^ 2) / W := by
  rcases Nat.eq_zero_or_pos W with h0 | hW
  · subst h0; exact α.elim0
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hs1 : Real.sqrt W * Real.sqrt W = W := Real.mul_self_sqrt hW'.le
  have hs2 : Real.sqrt (2 * W) * Real.sqrt (2 * W) = 2 * W := Real.mul_self_sqrt (by positivity)
  simp only [gueBlock, Matrix.of_apply]
  rw [Complex.sq_norm]
  split_ifs with h1 h2
  · subst h1
    rw [Complex.normSq_div, Complex.normSq_ofReal, Complex.normSq_ofReal, hs1]
    rw [div_le_div_iff_of_pos_right hW']
    nlinarith [sq_nonneg (v (b, α, α))]
  · rw [Complex.normSq_div, Complex.normSq_ofReal, hs2, mul_comm Complex.I,
      Complex.normSq_add_mul_I]
    rw [div_le_div_iff₀ (by positivity) hW']
    nlinarith [sq_nonneg (v (b, α, β)), sq_nonneg (v (b, β, α))]
  · have : ((v (b, β, α) : ℂ) - Complex.I * v (b, α, β)) =
        ((v (b, β, α) : ℂ) + Complex.I * ((-v (b, α, β) : ℝ) : ℂ)) := by push_cast; ring
    rw [this, Complex.normSq_div, Complex.normSq_ofReal, hs2, mul_comm Complex.I,
      Complex.normSq_add_mul_I]
    rw [div_le_div_iff₀ (by positivity) hW']
    nlinarith [sq_nonneg (v (b, α, β)), sq_nonneg (v (b, β, α))]

/-- `‖diag(V)‖²_HS ≤ (2/W) |ω|²`. -/
private lemma auxModel_hs_D_sq (W L : ℕ) (v : Ω W L) :
    auxModel_hs (auxModel_D W L v) ^ 2 ≤ 2 / W * ∑ i, v i ^ 2 := by
  rw [auxModel_hs_sq, auxModel_D_apply]
  have h : ∀ p : Fin L × Fin W, ∑ q, ‖blockDiagOp (gueBlock W L v) p q‖ ^ 2 =
      ∑ β, ‖gueBlock W L v p.1 p.2 β‖ ^ 2 := by
    intro p
    rw [Fintype.sum_prod_type, Finset.sum_eq_single p.1]
    · simp [blockDiagOp]
    · intro c _ hc; simp [blockDiagOp, Ne.symm hc]
    · simp
  simp only [h]
  calc ∑ p : Fin L × Fin W, ∑ β, ‖gueBlock W L v p.1 p.2 β‖ ^ 2
      ≤ ∑ p : Fin L × Fin W, ∑ β, (v (p.1, p.2, β) ^ 2 + v (p.1, β, p.2) ^ 2) / W :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun β _ =>
          auxModel_gueBlock_entry_sq W L v p.1 p.2 β
    _ = 2 / W * ∑ i, v i ^ 2 := by
        have e : ∀ b : Fin L, ∑ α : Fin W, ∑ β : Fin W, v (b, β, α) ^ 2 / (W : ℝ) =
            ∑ α : Fin W, ∑ β : Fin W, v (b, α, β) ^ 2 / W := fun b => Finset.sum_comm
        simp only [Fintype.sum_prod_type, add_div, Finset.sum_add_distrib, e, Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun β _ => ?_
        ring

end ModelBounds

section Variance

open scoped Matrix.Norms.L2Operator

/-- The derivative terms of a loop at `X` in the direction `-(X Z X)`, summed. -/
private lemma auxModel_deriv_sum_le {W L k : ℕ} (X Z : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hZ : Z.IsHermitian) {B : ℝ} (hB0 : 0 ≤ B) (hX : ‖X‖ ≤ B) (a : Fin k → Fin L)
    (σ : Fin k → Bool) :
    ‖∑ j : Fin k, (((List.ofFn fun i => sgnMat X (σ i) * blockE W L (a i)).take j).prod *
        (sgnMat (-(X * Z * X)) (σ j) * blockE W L (a j)) *
        ((List.ofFn fun i => sgnMat X (σ i) * blockE W L (a i)).drop (j + 1)).prod).trace‖ ≤
      k * (auxModel_hs Z * (B * (Real.sqrt (W : ℝ)⁻¹ * ((B * (W : ℝ)⁻¹) ^ (k - 1) * B)))) := by
  set l := List.ofFn fun i => sgnMat X (σ i) * blockE W L (a i) with hl
  have hρ : 0 ≤ B * (W : ℝ)⁻¹ := by positivity
  have hmem : ∀ x ∈ l, ‖x‖ ≤ B * (W : ℝ)⁻¹ := by
    intro x hx
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hx
    calc ‖sgnMat X (σ i) * blockE W L (a i)‖ ≤ ‖sgnMat X (σ i)‖ * ‖blockE W L (a i)‖ :=
          norm_mul_le _ _
      _ ≤ B * (W : ℝ)⁻¹ := by
          rw [auxModel_norm_sgnMat]
          exact mul_le_mul hX (auxModel_norm_blockE_le W L (a i)) (norm_nonneg _) hB0
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ j : Fin k, ‖(((l.take j).prod * (sgnMat (-(X * Z * X)) (σ j) *
      blockE W L (a j)) * (l.drop (j + 1)).prod).trace)‖ ≤
        auxModel_hs Z * (B * (Real.sqrt (W : ℝ)⁻¹ * ((B * (W : ℝ)⁻¹) ^ (k - 1) * B))) := by
    intro j
    refine (auxModel_term_le _ _ X Z _ hZ (σ j)).trans ?_
    have hP : ‖(l.take j).prod‖ ≤ (B * (W : ℝ)⁻¹) ^ (j : ℕ) := by
      have := auxModel_norm_prod_le hρ (l.take j) fun x hx => hmem x (List.mem_of_mem_take hx)
      rwa [List.length_take, hl, List.length_ofFn, min_eq_left j.isLt.le] at this
    have hD : ‖(l.drop (j + 1)).prod‖ ≤ (B * (W : ℝ)⁻¹) ^ (k - (j + 1)) := by
      have := auxModel_norm_prod_le hρ (l.drop (j + 1)) fun x hx => hmem x (List.mem_of_mem_drop hx)
      rwa [List.length_drop, hl, List.length_ofFn] at this
    have hDP : ‖(l.drop (j + 1)).prod‖ * ‖(l.take j).prod‖ ≤ (B * (W : ℝ)⁻¹) ^ (k - 1) := by
      calc _ ≤ (B * (W : ℝ)⁻¹) ^ (k - (j + 1)) * (B * (W : ℝ)⁻¹) ^ (j : ℕ) :=
            mul_le_mul hD hP (norm_nonneg _) (by positivity)
        _ = _ := by
            rw [← pow_add]
            congr 1
            have := j.isLt
            omega
    rw [auxModel_hs_blockE]
    gcongr
    · exact auxModel_hs_nonneg _
  refine (Finset.sum_le_sum fun j _ => hterm j).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `A - z_t` is invertible on the auxiliary model. -/
private lemma auxModel_isUnit_KT (g : ℝ) (W L : ℕ) (E : ℝ) (m : ℂ) (t : ℝ)
    (hz : (zChar g E m t).im ≠ 0) (ω : Ω W L) :
    IsUnit (auxModel_K g W L E m t + auxModel_T g W L t ω) := by
  rw [← auxModel_H_eq]
  exact auxModel_isUnit (auxModel_A_herm g W L t ω) hz

/-- `‖G_t‖ ≤ η⁻¹` on the auxiliary model. -/
private lemma auxModel_norm_G_le (g : ℝ) (W L : ℕ) (E : ℝ) (m : ℂ) (t : ℝ) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ (zChar g E m t).im) (ω : Ω W L) : ‖auxG g W L E m t ω‖ ≤ η⁻¹ := by
  rw [auxG]
  exact auxModel_norm_inv_le (auxModel_A_herm g W L t ω) hη (hz.trans (le_abs_self _))

/-- The random part is Hermitian. -/
private lemma auxModel_T_herm (g : ℝ) (W L : ℕ) (t : ℝ) (v : Ω W L) :
    (auxModel_T g W L t v).IsHermitian := by
  have h := blockDiagOp_isHermitian (fun b => gueBlock_isHermitian W L v b)
  unfold Matrix.IsHermitian at h ⊢
  rw [auxModel_T, smul_apply, auxModel_D_apply, Matrix.conjTranspose_smul, h]
  simp

/-- `‖√(tγ_g) diag(V(v))‖_HS ≤ √(tγ_g) √(2/W) |v|₂`. -/
private lemma auxModel_hs_T_le (g : ℝ) (W L : ℕ) (t : ℝ) (v : Ω W L) :
    auxModel_hs (auxModel_T g W L t v) ≤
      ((max 1 g)⁻¹ * Real.sqrt t) * (Real.sqrt (2 / W) * Real.sqrt (∑ i, v i ^ 2)) := by
  have hc : 0 ≤ (max 1 g)⁻¹ * Real.sqrt t :=
    mul_nonneg (inv_nonneg.mpr (le_trans zero_le_one (le_max_left _ _))) (Real.sqrt_nonneg _)
  rw [auxModel_T, smul_apply, auxModel_hs_smul, abs_of_nonneg hc]
  gcongr
  rw [← Real.sqrt_mul (by positivity)]
  rw [← Real.sqrt_sq (auxModel_hs_nonneg _)]
  exact Real.sqrt_le_sqrt (auxModel_hs_D_sq W L v)

/-- The loop functional `ω ↦ W^{k-1} ℒ_k(G_t(ω))`. -/
private def auxModel_f (g : ℝ) (W L : ℕ) (E : ℝ) (m : ℂ) (t : ℝ) {k : ℕ} (a : Fin k → Fin L)
    (σ : Fin k → Bool) (ω : Ω W L) : ℂ :=
  (W : ℂ) ^ (k - 1) * loopTr (auxG g W L E m t ω) a σ

/-- The loop functional is smooth. -/
private lemma auxModel_contDiff_f (g : ℝ) (W L : ℕ) (E : ℝ) (m : ℂ) (t : ℝ)
    (hz : (zChar g E m t).im ≠ 0) {k : ℕ} (a : Fin k → Fin L) (σ : Fin k → Bool) :
    ContDiff ℝ 1 (auxModel_f g W L E m t a σ) := by
  have hG : (fun ω => auxG g W L E m t ω) =
      fun ω => (auxModel_K g W L E m t + auxModel_T g W L t ω)⁻¹ := by
    funext ω; exact auxModel_G_eq g W L E m t ω
  have h1 := auxModel_contDiff_inv (auxModel_K g W L E m t) (auxModel_T g W L t)
    (auxModel_isUnit_KT g W L E m t hz)
  have h2 := (contDiff_const (c := ((W : ℂ) ^ (k - 1)))).mul
    ((auxModel_contDiff_loopTr (W := W) a σ).comp h1)
  unfold auxModel_f
  simp only [auxModel_G_eq]
  exact h2

/-- The derivative of the loop functional in the direction `v` is `O(|v|₂ / W)`. -/
private lemma auxModel_fderiv_le (g : ℝ) (W L : ℕ) (hW : 1 ≤ W) (E : ℝ) (m : ℂ) (t : ℝ)
    {η : ℝ} (hη : 0 < η) (hz : η ≤ (zChar g E m t).im) {k : ℕ} (hk : 1 ≤ k)
    (a : Fin k → Fin L) (σ : Fin k → Bool) (ω v : Ω W L) :
    ‖fderiv ℝ (auxModel_f g W L E m t a σ) ω v‖ ≤
      k * ((max 1 g)⁻¹ * Real.sqrt t) * Real.sqrt 2 * η⁻¹ ^ (k + 1) / W *
        Real.sqrt (∑ i, v i ^ 2) := by
  have hz0 : (zChar g E m t).im ≠ 0 := (lt_of_lt_of_le hη hz).ne'
  set K₀ := auxModel_K g W L E m t
  set T := auxModel_T g W L t
  set Λ : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ → ℂ := fun X => (W : ℂ) ^ (k - 1) * loopTr X a σ
    with hΛ
  have hfeq : auxModel_f g W L E m t a σ = fun ω => Λ ((K₀ + T ω)⁻¹) := by
    funext ω; simp only [auxModel_f, hΛ, auxModel_G_eq]; rfl
  have hGf := auxModel_hasFDerivAt_inv K₀ T ω (auxModel_isUnit_KT g W L E m t hz0 ω)
  have hΛc : ContDiff ℝ 1 Λ := contDiff_const.mul (auxModel_contDiff_loopTr (W := W) a σ)
  have hΛd : HasFDerivAt Λ (fderiv ℝ Λ ((K₀ + T ω)⁻¹)) ((K₀ + T ω)⁻¹) :=
    ((hΛc.differentiable one_ne_zero) _).hasFDerivAt
  have hf := hΛd.comp ω hGf
  have hf' : HasFDerivAt (fun ω' => Λ ((K₀ + T ω')⁻¹)) _ ω := hf
  rw [hfeq, hf'.fderiv]
  set G := (K₀ + T ω)⁻¹ with hGdef
  have hGb : ‖G‖ ≤ η⁻¹ := by
    rw [hGdef, ← auxModel_G_eq]; exact auxModel_norm_G_le g W L E m t hη hz ω
  simp only [ContinuousLinearMap.comp_apply, FunLike.coe_neg, Pi.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply]
  set Y := -(G * T v * G) with hY
  -- the derivative of `Λ` at `G` in the direction `Y`
  have hline : HasDerivAt (fun s : ℝ => G + s • Y) Y 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const Y).const_add G
  have h1 : HasDerivAt (fun s : ℝ => Λ (G + s • Y)) (fderiv ℝ Λ G Y) 0 :=
    hΛd.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have h2 := (auxModel_hasDerivAt_loopTr (W := W) G Y a σ).const_mul ((W : ℂ) ^ (k - 1))
  rw [h1.unique h2, norm_mul, norm_pow, Complex.norm_natCast]
  have hZ := auxModel_T_herm g W L t v
  have hsum := auxModel_deriv_sum_le (W := W) G (T v) hZ (by positivity) hGb a σ
  have hhs := auxModel_hs_T_le g W L t v
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hc : 0 ≤ (max 1 g)⁻¹ * Real.sqrt t :=
    mul_nonneg (inv_nonneg.mpr (le_trans zero_le_one (le_max_left _ _))) (Real.sqrt_nonneg _)
  calc (W : ℝ) ^ (k - 1) * ‖∑ j : Fin k, _‖
      ≤ (W : ℝ) ^ (k - 1) * (k * (auxModel_hs (T v) * (η⁻¹ * (Real.sqrt (W : ℝ)⁻¹ *
          ((η⁻¹ * (W : ℝ)⁻¹) ^ (k - 1) * η⁻¹))))) := by
        gcongr
    _ ≤ (W : ℝ) ^ (k - 1) * (k * ((((max 1 g)⁻¹ * Real.sqrt t) * (Real.sqrt (2 / W) *
          Real.sqrt (∑ i, v i ^ 2))) * (η⁻¹ * (Real.sqrt (W : ℝ)⁻¹ *
          ((η⁻¹ * (W : ℝ)⁻¹) ^ (k - 1) * η⁻¹))))) := by
        gcongr
    _ = _ := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        have hs1 : Real.sqrt (2 / W) = Real.sqrt 2 / Real.sqrt W := Real.sqrt_div' 2 hW'.le
        have hs2 : Real.sqrt (W : ℝ)⁻¹ = (Real.sqrt W)⁻¹ := Real.sqrt_inv _
        have hs3 : Real.sqrt (W : ℝ) * Real.sqrt W = W := Real.mul_self_sqrt hW'.le
        have hsW : 0 < Real.sqrt (W : ℝ) := Real.sqrt_pos.mpr hW'
        rw [hs1, hs2, mul_pow, inv_pow (W : ℝ)]
        field_simp
        rw [Real.sq_sqrt hW'.le]
        field_simp
        have hη2 : η ^ 2 * η⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hη.ne', one_pow]
        linear_combination (-(Real.sqrt t * Real.sqrt (∑ i, v i ^ 2) * η⁻¹ ^ j)) * hη2

end Variance

section VarianceProof

open scoped Matrix.Norms.L2Operator

/-- `|Tr X| ≤ |n| ‖X‖`. -/
private lemma auxModel_norm_trace_le {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    ‖X.trace‖ ≤ Fintype.card n * ‖X‖ := by
  rw [Matrix.trace]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => auxModel_norm_entry_le X i i).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The loop functional is bounded. -/
private lemma auxModel_f_bound (g : ℝ) (W L : ℕ) (E : ℝ) (m : ℂ) (t : ℝ) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ (zChar g E m t).im) {k : ℕ} (a : Fin k → Fin L) (σ : Fin k → Bool) (ω : Ω W L) :
    ‖auxModel_f g W L E m t a σ ω‖ ≤
      (W : ℝ) ^ (k - 1) * (Fintype.card (Fin L × Fin W) * (η⁻¹ * (W : ℝ)⁻¹) ^ k) := by
  have hG := auxModel_norm_G_le g W L E m t hη hz ω
  rw [auxModel_f, norm_mul, norm_pow, Complex.norm_natCast, loopTr]
  gcongr
  refine (auxModel_norm_trace_le _).trans ?_
  gcongr
  have := auxModel_norm_prod_le (by positivity : (0 : ℝ) ≤ η⁻¹ * (W : ℝ)⁻¹)
    (List.ofFn fun i => sgnMat (auxG g W L E m t ω) (σ i) * blockE W L (a i)) (fun x hx => by
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hx
      calc _ ≤ ‖sgnMat (auxG g W L E m t ω) (σ i)‖ * ‖blockE W L (a i)‖ := norm_mul_le _ _
        _ ≤ η⁻¹ * (W : ℝ)⁻¹ := by
          rw [auxModel_norm_sgnMat]
          exact mul_le_mul hG (auxModel_norm_blockE_le W L (a i)) (norm_nonneg _)
            (by positivity))
  rwa [List.length_ofFn] at this

/-- Gaussian Poincaré inequality for the normalized loops of the auxiliary model: the variance
of `W̃^{k-1} ℒ_k^{(W̃)}(t)` is `O(W̃^{-2})`, uniformly on `[0, T]`, `T < 1`. -/
theorem auxLoop_variance (g : ℝ) (hg : 0 < g) (L : ℕ) (hL : 3 ≤ L) (E : ℝ) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (T : ℝ) (hT0 : 0 ≤ T) (hT : T < 1) (k : ℕ)
    (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ Wt : ℕ, 1 ≤ Wt → ∀ t : ℝ, 0 ≤ t → t ≤ T →
      ∀ (a : Fin k → Fin L) (σ : Fin k → Bool),
        Integrable (fun ω => ‖(Wt : ℂ) ^ (k - 1) * loopTr (auxG g Wt L E m t ω) a σ -
          auxLoop g Wt L E m t k a σ‖ ^ 2) (μ Wt L) ∧
        ∫ ω, ‖(Wt : ℂ) ^ (k - 1) * loopTr (auxG g Wt L E m t ω) a σ -
          auxLoop g Wt L E m t k a σ‖ ^ 2 ∂(μ Wt L) ≤ C / (Wt : ℝ) ^ 2 := by
  have hγ : 0 < gammaG g := by
    have : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
    unfold gammaG; positivity
  set η := (1 - T) * gammaG g * m.im with hηdef
  have hη : 0 < η := mul_pos (mul_pos (by linarith) hγ) hm.1
  have hz : ∀ t, t ≤ T → η ≤ (zChar g E m t).im := by
    intro t ht
    rw [auxModel_im_zChar, hηdef]
    have := hm.1
    gcongr
  set A : ℝ → ℝ := fun s => k * ((max 1 g)⁻¹ * Real.sqrt s) * Real.sqrt 2 * η⁻¹ ^ (k + 1)
    with hAdef
  have hc0 : 0 ≤ (max 1 g)⁻¹ := inv_nonneg.mpr (le_trans zero_le_one (le_max_left _ _))
  have hA0 : ∀ s, 0 ≤ A s := fun s => by positivity
  have hAmono : ∀ s, s ≤ T → A s ≤ A T := by
    intro s hs
    simp only [hAdef]
    gcongr
  refine ⟨π ^ 2 / 8 * (2 * A T ^ 2) + 1, by positivity, ?_⟩
  intro Wt hWt t ht0 htT a σ
  have hW' : (0 : ℝ) < Wt := by exact_mod_cast hWt
  have hz0 : (zChar g E m t).im ≠ 0 := (lt_of_lt_of_le hη (hz t htT)).ne'
  set f := auxModel_f g Wt L E m t a σ with hfdef
  have hf : ContDiff ℝ 1 f := auxModel_contDiff_f g Wt L E m t hz0 a σ
  have hK0 : 0 ≤ A t / Wt := by positivity
  have hD : ∀ ω v, ‖fderiv ℝ f ω v‖ ≤ A t / Wt * Real.sqrt (∑ i, v i ^ 2) := by
    intro ω v
    exact auxModel_fderiv_le g Wt L hWt E m t hη (hz t htT) hk a σ ω v
  have hb : ∀ ω, ‖fderiv ℝ f ω‖ ≤ A t / Wt * Real.sqrt (Fintype.card (Fin L × Fin Wt × Fin Wt)) :=
    fun ω => auxModel_opNorm_le _ hK0 (hD ω)
  have hsum : ∀ ω, ∑ i, ‖fderiv ℝ f ω (Pi.single i 1)‖ ^ 2 ≤ 2 * (A t / Wt) ^ 2 :=
    fun ω => auxModel_sum_sq_le _ hK0 (hD ω)
  have hP := poincare_grad f hf hb
  have hμ : μ Wt L = stdGauss (Fin L × Fin Wt × Fin Wt) := rfl
  have hmean : auxLoop g Wt L E m t k a σ = ∫ ω, f ω ∂(μ Wt L) := by
    simp only [auxLoop, hfdef, auxModel_f]
    rw [integral_const_mul]
  have hfe : ∀ ω, (Wt : ℂ) ^ (k - 1) * loopTr (auxG g Wt L E m t ω) a σ = f ω := fun ω => rfl
  simp only [hfe, hmean]
  rw [hμ] at *
  refine ⟨?_, ?_⟩
  · refine Integrable.of_bound
      ((hf.continuous.sub continuous_const).norm.pow 2).aestronglyMeasurable
      (((Wt : ℝ) ^ (k - 1) * (Fintype.card (Fin L × Fin Wt) * (η⁻¹ * (Wt : ℝ)⁻¹) ^ k) +
        ‖∫ ω, f ω ∂stdGauss (Fin L × Fin Wt × Fin Wt)‖) ^ 2) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
    refine (norm_sub_le _ _).trans ?_
    gcongr
    exact auxModel_f_bound g Wt L E m t hη (hz t htT) a σ ω
  · refine hP.trans ?_
    have hI : ∫ x, ∑ i, ‖fderiv ℝ f x (Pi.single i 1)‖ ^ 2 ∂stdGauss (Fin L × Fin Wt × Fin Wt) ≤
        2 * (A t / Wt) ^ 2 := by
      refine (integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity)
        (integrable_const _) (Eventually.of_forall hsum)).trans (le_of_eq ?_)
      simp
    calc π ^ 2 / 8 * ∫ x, ∑ i, ‖fderiv ℝ f x (Pi.single i 1)‖ ^ 2 ∂stdGauss _
        ≤ π ^ 2 / 8 * (2 * (A t / Wt) ^ 2) := by gcongr
      _ = π ^ 2 / 8 * (2 * A t ^ 2) / (Wt : ℝ) ^ 2 := by field_simp
      _ ≤ (π ^ 2 / 8 * (2 * A T ^ 2) + 1) / (Wt : ℝ) ^ 2 := by
          gcongr
          have h1 : A t ^ 2 ≤ A T ^ 2 := pow_le_pow_left₀ (hA0 t) (hAmono t htT) 2
          have h2 : 0 ≤ π ^ 2 / 8 := by positivity
          nlinarith

end VarianceProof

/-- Coefficient of `ω_{(b,α,β)}` in the entry `V_b(α, β)`. -/
private def auxModel_gU (W : ℕ) (α β : Fin W) : ℂ :=
  if α = β then ((Real.sqrt W : ℝ) : ℂ)⁻¹
  else if α < β then ((Real.sqrt (2 * W) : ℝ) : ℂ)⁻¹
  else -Complex.I * ((Real.sqrt (2 * W) : ℝ) : ℂ)⁻¹

/-- Coefficient of `ω_{(b,β,α)}` in the entry `V_b(α, β)`. -/
private def auxModel_gV (W : ℕ) (α β : Fin W) : ℂ :=
  if α = β then 0
  else if α < β then Complex.I * ((Real.sqrt (2 * W) : ℝ) : ℂ)⁻¹
  else ((Real.sqrt (2 * W) : ℝ) : ℂ)⁻¹

private lemma auxModel_gueBlock_single (W L : ℕ) (i : Fin L × Fin W × Fin W) (b : Fin L)
    (α β : Fin W) :
    gueBlock W L (Pi.single i 1) b α β =
      auxModel_gU W α β * (if i = (b, α, β) then 1 else 0) +
        auxModel_gV W α β * (if i = (b, β, α) then 1 else 0) := by
  rcases lt_trichotomy α β with h | rfl | h
  · have hne : α ≠ β := h.ne
    have hne' : ¬β < α := not_lt.mpr h.le
    simp only [gueBlock, Matrix.of_apply, auxModel_gU, auxModel_gV, hne, h, ↓reduceIte]
    by_cases h1 : i = (b, α, β) <;> by_cases h2 : i = (b, β, α)
    · rw [h1, Prod.mk.injEq, Prod.mk.injEq] at h2; exact absurd h2.2.1 hne
    · subst h1; simp [hne, div_eq_mul_inv]
    · subst h2; simp [hne, Ne.symm hne, div_eq_mul_inv]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  · simp only [gueBlock, Matrix.of_apply, auxModel_gU, auxModel_gV, ↓reduceIte]
    by_cases h1 : i = (b, α, α)
    · subst h1; simp [div_eq_mul_inv]
    · simp [h1, Ne.symm h1]
  · have hne : α ≠ β := h.ne'
    have hne' : ¬α < β := not_lt.mpr h.le
    simp only [gueBlock, Matrix.of_apply, auxModel_gU, auxModel_gV, hne, hne', ↓reduceIte]
    by_cases h1 : i = (b, α, β) <;> by_cases h2 : i = (b, β, α)
    · rw [h1, Prod.mk.injEq, Prod.mk.injEq] at h2; exact absurd h2.2.1 hne
    · subst h1; simp [hne, Ne.symm hne, div_eq_mul_inv]
    · subst h2; simp [hne, Ne.symm hne, div_eq_mul_inv]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

/-- The GUE covariance in coordinates: `Σ_i V^{(i)}_b(α,β) V^{(i)}_{b'}(γ,δ) = W⁻¹ δ_{bb'} δ_{αδ}
δ_{βγ}`. -/
private lemma auxModel_kernel (W L : ℕ) (hW : 1 ≤ W) (b b' : Fin L) (α β γ δ : Fin W) :
    ∑ i, gueBlock W L (Pi.single i 1) b α β * gueBlock W L (Pi.single i 1) b' γ δ =
      if b = b' ∧ α = δ ∧ β = γ then (W : ℂ)⁻¹ else 0 := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have h1 : ((Real.sqrt W : ℝ) : ℂ) * ((Real.sqrt W : ℝ) : ℂ) = W := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hW'.le]; simp
  have h2 : ((Real.sqrt (2 * W) : ℝ) : ℂ) * ((Real.sqrt (2 * W) : ℝ) : ℂ) = 2 * W := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]; simp
  have hr2 : ((Real.sqrt (2 * W) : ℝ) : ℂ)⁻¹ ^ 2 = 2⁻¹ * (W : ℂ)⁻¹ := by
    rw [inv_pow, sq, h2, mul_inv]
  have hs2 : ((Real.sqrt W : ℝ) : ℂ)⁻¹ ^ 2 = (W : ℂ)⁻¹ := by
    rw [inv_pow, sq, h1]
  simp only [auxModel_gueBlock_single, add_mul, mul_add, Finset.sum_add_distrib, mul_ite,
    ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Prod.mk.injEq, auxModel_gU, auxModel_gV]
  generalize ((Real.sqrt (2 * W) : ℝ) : ℂ)⁻¹ = r at hr2 ⊢
  generalize ((Real.sqrt W : ℝ) : ℂ)⁻¹ = s at hs2 ⊢
  split_ifs <;>
    first
    | (exfalso; simp only [Fin.lt_def, Fin.ext_iff] at *; omega)
    | (ring_nf; done)
    | (ring_nf; simp only [hr2, hs2, Complex.I_sq]; done)
    | (ring_nf; simp only [hr2, Complex.I_sq]; ring_nf)

/-- The completeness relation `Σ_i D_i X D_i = diag(⟨X⟩_{bb}) ⊗ I` for the coordinate matrices
`D_i = diag(V(e_i))` of the GUE blocks. -/
private lemma auxModel_complete (W L : ℕ) (hW : 1 ≤ W)
    (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    ∑ i, blockDiagOp (gueBlock W L (Pi.single i 1)) * X *
        blockDiagOp (gueBlock W L (Pi.single i 1)) =
      Matrix.diagonal (fun p => (W : ℂ)⁻¹ * ∑ γ, X (p.1, γ) (p.1, γ)) := by
  ext p q
  set D : (Fin L × Fin W × Fin W) → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
    fun i => blockDiagOp (gueBlock W L (Pi.single i 1)) with hDdef
  have key : ∀ r s : Fin L × Fin W, ∑ i, D i p r * D i s q =
      if r.1 = p.1 ∧ s = r ∧ (p.1 = q.1 ∧ p.2 = q.2) then (W : ℂ)⁻¹ else 0 := by
    intro r s
    obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q; obtain ⟨r1, r2⟩ := r; obtain ⟨s1, s2⟩ := s
    simp only [hDdef, blockDiagOp, Matrix.of_apply, Prod.mk.injEq]
    by_cases h1 : p1 = r1
    · by_cases h2 : s1 = q1
      · rw [Finset.sum_congr rfl fun i _ => by rw [ite_eq_left h1, ite_eq_left h2]]
        rw [auxModel_kernel W L hW]
        subst h1 h2
        congr 1
        apply propext
        constructor
        · rintro ⟨h3, h4, h5⟩; exact ⟨rfl, ⟨h3.symm, h5.symm⟩, h3, h4⟩
        · rintro ⟨-, ⟨h3, h5⟩, h6, h4⟩; exact ⟨h6, h4, h5.symm⟩
      · rw [Finset.sum_congr rfl fun i _ => by rw [ite_eq_right h2, mul_zero],
          Finset.sum_const_zero]
        rw [ite_eq_right]
        rintro ⟨hr, ⟨hs, -⟩, hpq, -⟩
        exact h2 (by rw [hs, hr, hpq])
    · rw [Finset.sum_congr rfl fun i _ => by rw [ite_eq_right h1, zero_mul], Finset.sum_const_zero]
      rw [ite_eq_right]
      rintro ⟨hr, -, -⟩
      exact h1 hr.symm
  calc (∑ i, D i * X * D i) p q = ∑ r, ∑ s, X r s * ∑ i, D i p r * D i s q := by
        simp only [Matrix.sum_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        rw [Finset.sum_congr rfl fun s _ => Finset.sum_comm]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ =>
          Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = _ := by
        simp only [key, mul_ite, mul_zero, ite_and]
        by_cases hpq : p.1 = q.1 ∧ p.2 = q.2
        · have hpq' : p = q := Prod.ext hpq.1 hpq.2
          simp only [ite_true,
            Matrix.diagonal_apply_eq, hpq']
          subst hpq'
          rw [Fintype.sum_prod_type, Finset.sum_eq_single p.1]
          · simp [Finset.mul_sum, mul_comm]
          · intro b _ hb; simp [hb]
          · simp
        · have hpq' : p ≠ q := fun h => hpq ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
          rw [Matrix.diagonal_apply_ne _ hpq']
          refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun s _ => ?_
          split_ifs with h3 h4 h5 h6 <;> first | rfl | exact absurd ⟨h5, h6⟩ hpq


section Stein

open scoped Matrix.Norms.L2Operator

/-- Gaussian integration by parts for a resolvent functional:
`E[x_i ℓ(G)] = E[ℓ(-G (T e_i) G)]` for `G = (K₀ + T x)⁻¹` with `‖G‖ ≤ B`. -/
private lemma auxModel_stein {ι : Type*} [Fintype ι] [DecidableEq ι] {n : Type*} [Fintype n]
    [DecidableEq n] (K₀ : Matrix n n ℂ) (T : (ι → ℝ) →L[ℝ] Matrix n n ℂ)
    (hu : ∀ x, IsUnit (K₀ + T x)) {B : ℝ} (hB : ∀ x, ‖(K₀ + T x)⁻¹‖ ≤ B)
    (ℓ : Matrix n n ℂ →L[ℝ] ℂ) (i : ι) :
    ∫ x, (x i : ℂ) * ℓ ((K₀ + T x)⁻¹) ∂stdGauss ι =
      ∫ x, ℓ (-((K₀ + T x)⁻¹ * T (Pi.single i 1) * (K₀ + T x)⁻¹)) ∂stdGauss ι := by
  set F : (ι → ℝ) → ℂ := fun x => ℓ ((K₀ + T x)⁻¹) with hFdef
  have hF : ContDiff ℝ 1 F := ℓ.contDiff.comp (auxModel_contDiff_inv K₀ T hu)
  have hder : ∀ x v, fderiv ℝ F x v = ℓ (-((K₀ + T x)⁻¹ * T v * (K₀ + T x)⁻¹)) := by
    intro x v
    have h := (ℓ.hasFDerivAt.comp x (auxModel_hasFDerivAt_inv K₀ T x (hu x)))
    have h' : HasFDerivAt F _ x := h
    rw [h'.fderiv]
    simp [ContinuousLinearMap.mulLeftRight_apply]
  set B0 := max B 0 with hB0def
  have hB0 : 0 ≤ B0 := le_max_right _ _
  have hGB : ∀ x, ‖(K₀ + T x)⁻¹‖ ≤ B0 := fun x => (hB x).trans (le_max_left _ _)
  set C := ‖ℓ‖ * B0 + ‖ℓ‖ * (B0 * ‖T‖ * B0) with hCdef
  have hb : ∀ x, ‖F x‖ ≤ C * (1 + ‖x‖) ^ 0 := by
    intro x
    rw [pow_zero, mul_one]
    calc ‖F x‖ ≤ ‖ℓ‖ * ‖(K₀ + T x)⁻¹‖ := ℓ.le_opNorm _
      _ ≤ ‖ℓ‖ * B0 := by gcongr; exact hGB x
      _ ≤ C := le_add_of_nonneg_right (by positivity)
  have hb' : ∀ x, ‖fderiv ℝ F x‖ ≤ C * (1 + ‖x‖) ^ 0 := by
    intro x
    rw [pow_zero, mul_one]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [hder]
    calc ‖ℓ (-((K₀ + T x)⁻¹ * T v * (K₀ + T x)⁻¹))‖
        ≤ ‖ℓ‖ * ‖(K₀ + T x)⁻¹ * T v * (K₀ + T x)⁻¹‖ := by
          rw [← norm_neg ((K₀ + T x)⁻¹ * T v * (K₀ + T x)⁻¹)]; exact ℓ.le_opNorm _
      _ ≤ ‖ℓ‖ * (‖(K₀ + T x)⁻¹‖ * ‖T v‖ * ‖(K₀ + T x)⁻¹‖) := by gcongr; exact norm_mul₃_le
      _ ≤ ‖ℓ‖ * (B0 * (‖T‖ * ‖v‖) * B0) := by
          gcongr
          · exact hGB x
          · exact T.le_opNorm v
          · exact hGB x
      _ ≤ C * ‖v‖ := by
          rw [hCdef]
          have : 0 ≤ ‖ℓ‖ * B0 * ‖v‖ := by positivity
          nlinarith
  have h := integral_coord_mul_stdGauss F hF hb hb' i
  rw [h]
  exact integral_congr_ae (Eventually.of_forall fun x => hder x _)

/-- The normalized block entry `⟨X⟩_{bc} = W⁻¹ Σ_α X_{(b,α),(c,α)}` as a real-linear map. -/
private def auxModel_ptr {W L : ℕ} (b c : Fin L) :
    Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => (W : ℂ)⁻¹ * ∑ α, X (b, α) (c, α)
      map_add' := fun X Y => by simp [Finset.sum_add_distrib, mul_add]
      map_smul' := fun r X => by
        simp only [Matrix.smul_apply, Complex.real_smul, RingHom.id_apply, ← Finset.mul_sum]
        ring }

private lemma auxModel_ptr_apply {W L : ℕ} (b c : Fin L)
    (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    auxModel_ptr b c X = (W : ℂ)⁻¹ * ∑ α, X (b, α) (c, α) := rfl

/-- A bounded continuous function is integrable for the Gaussian product measure. -/
private lemma auxModel_integrable_bdd {W L : ℕ} {f : Ω W L → ℂ} (hf : Continuous f) (C : ℝ)
    (hb : ∀ ω, ‖f ω‖ ≤ C) : Integrable f (μ W L) :=
  Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall hb)

/-- A coordinate times a bounded continuous function is integrable. -/
private lemma auxModel_integrable_coord_mul {W L : ℕ} (i : Fin L × Fin W × Fin W)
    {f : Ω W L → ℂ} (hf : Continuous f) (C : ℝ) (hb : ∀ ω, ‖f ω‖ ≤ C) :
    Integrable (fun ω => (ω i : ℂ) * f ω) (μ W L) := by
  have hmp : MeasurePreserving (Function.eval i) (μ W L) (gaussianReal 0 1) :=
    measurePreserving_eval (fun _ => gaussianReal 0 1) i
  have hi : Integrable (fun ω : Ω W L => ω i) (μ W L) :=
    (hmp.integrable_comp (integrable_id_gaussianReal (var := 1)).aestronglyMeasurable).mpr
      (integrable_id_gaussianReal (var := 1))
  have := hi.ofReal.mul_bdd (𝕜 := ℂ) hf.aestronglyMeasurable (Eventually.of_forall hb)
  simpa using this

end Stein

section MeanField

open scoped Matrix.Norms.L2Operator

/-- `|⟨X⟩_{bc}| ≤ ‖X‖`. -/
private lemma auxModel_norm_ptr_le {W L : ℕ} (hW : 1 ≤ W) (b c : Fin L)
    (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) : ‖auxModel_ptr b c X‖ ≤ ‖X‖ := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  rw [auxModel_ptr_apply, norm_mul, norm_inv, Complex.norm_natCast]
  calc (W : ℝ)⁻¹ * ‖∑ α, X (b, α) (c, α)‖ ≤ (W : ℝ)⁻¹ * ∑ _α : Fin W, ‖X‖ := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => auxModel_norm_entry_le X _ _)
    _ = ‖X‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- `⟨K X⟩_{bc} = Σ_d (A_g)_{bd} ⟨X⟩_{dc} - z_t ⟨X⟩_{bc}`. -/
private lemma auxModel_ptr_K_mul (g : ℝ) (W L : ℕ) (E : ℝ) (m : ℂ) (t : ℝ) (b c : Fin L)
    (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    auxModel_ptr b c (auxModel_K g W L E m t * X) =
      ∑ d, ((hopB g : ℂ) * cycleAdj L b d) * auxModel_ptr d c X -
        zChar g E m t * auxModel_ptr b c X := by
  simp only [auxModel_ptr_apply, auxModel_K, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply]
  have h : ∀ α : Fin W, ∑ d : Fin L, ∑ β : Fin W,
      cycleAdj L b d * (if α = β then 1 else 0) * X (d, β) (c, α) =
      ∑ d : Fin L, cycleAdj L b d * X (d, α) (c, α) := by
    intro α
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_eq_single α]
    · simp
    · intro β _ hβ; simp [Ne.symm hβ]
    · simp
  simp only [Finset.mul_sum, mul_sub, Finset.sum_sub_distrib, h]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun α _ => ?_
    ring
  · refine Finset.sum_congr rfl fun α _ => ?_
    ring

/-- `⟨1⟩_{bc} = δ_{bc}`. -/
private lemma auxModel_ptr_one {W L : ℕ} (hW : 1 ≤ W) (b c : Fin L) :
    auxModel_ptr b c (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) = if b = c then 1 else 0 := by
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast (by omega : W ≠ 0)
  rw [auxModel_ptr_apply]
  by_cases h : b = c
  · subst h; simp [hW']
  · simp [h]

/-- `⟨diag(⟨X⟩_{pp}) Y⟩_{bc} = ⟨X⟩_{bb} ⟨Y⟩_{bc}`. -/
private lemma auxModel_ptr_diag_mul {W L : ℕ} (b c : Fin L)
    (X Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    auxModel_ptr b c (Matrix.diagonal (fun p => (W : ℂ)⁻¹ * ∑ γ, X (p.1, γ) (p.1, γ)) * Y) =
      auxModel_ptr b b X * auxModel_ptr b c Y := by
  simp only [auxModel_ptr_apply, Matrix.diagonal_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

/-- A real-linear map on coordinates is the sum of its values on the basis vectors. -/
private lemma auxModel_clm_decomp {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*}
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] (T : (ι → ℝ) →L[ℝ] F) (x : ι → ℝ) :
    T x = ∑ i, x i • T (Pi.single i 1) := by
  conv_lhs => rw [show x = ∑ i, x i • (Pi.single i (1 : ℝ) : ι → ℝ) by
    ext j; simp [Finset.sum_apply, Pi.single_apply]]
  rw [map_sum]
  simp only [map_smul]

/-- The expected Dyson equation of the auxiliary model: for all blocks `b, c`,
`Σ_d (A_g)_{bd} E⟨G⟩_{dc} - z_t E⟨G⟩_{bc} - tγ_g E[⟨G⟩_{bb}⟨G⟩_{bc}] = δ_{bc}`
(Gaussian integration by parts in the proof of Lemma 5.4 [uvc:lem:orbital-limit]). -/
private lemma auxModel_dyson_mean (g : ℝ) (W L : ℕ) (hW : 1 ≤ W) (E : ℝ) (m : ℂ) (t : ℝ)
    (ht : 0 ≤ t) {η : ℝ} (hη : 0 < η) (hz : η ≤ (zChar g E m t).im) (b c : Fin L) :
    ∑ d, ((hopB g : ℂ) * cycleAdj L b d) *
        ∫ ω, auxModel_ptr d c (auxG g W L E m t ω) ∂(μ W L) -
      zChar g E m t * ∫ ω, auxModel_ptr b c (auxG g W L E m t ω) ∂(μ W L) -
      ((gammaG g * t : ℝ) : ℂ) * ∫ ω, auxModel_ptr b b (auxG g W L E m t ω) *
        auxModel_ptr b c (auxG g W L E m t ω) ∂(μ W L) =
      if b = c then 1 else 0 := by
  have hz0 : (zChar g E m t).im ≠ 0 := (lt_of_lt_of_le hη hz).ne'
  set K₀ := auxModel_K g W L E m t with hK₀
  set T := auxModel_T g W L t with hT
  set G : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ := fun ω => auxG g W L E m t ω
    with hGdef
  have hGeq : ∀ ω, G ω = (K₀ + T ω)⁻¹ := fun ω => auxModel_G_eq g W L E m t ω
  have hu : ∀ ω, IsUnit (K₀ + T ω) := auxModel_isUnit_KT g W L E m t hz0
  have hGc : Continuous G := by
    have := (auxModel_contDiff_inv K₀ T hu).continuous
    convert this using 1
    funext ω; exact hGeq ω
  have hGb : ∀ ω, ‖G ω‖ ≤ η⁻¹ := fun ω => auxModel_norm_G_le g W L E m t hη hz ω
  have hη0 : 0 ≤ η⁻¹ := by positivity
  -- integrability of bounded continuous functionals of `G`
  have hint : ∀ (ℓ : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ →L[ℝ] ℂ)
      (P : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
      (hP : Continuous P) (B : ℝ) (hPB : ∀ ω, ‖P (G ω)‖ ≤ B),
      Integrable (fun ω => ℓ (P (G ω))) (μ W L) := by
    intro ℓ P hP B hPB
    exact auxModel_integrable_bdd (ℓ.continuous.comp (hP.comp hGc)) (‖ℓ‖ * B)
      fun ω => (ℓ.le_opNorm _).trans (by gcongr; exact hPB ω)
  -- pointwise resolvent identity
  have hpt : ∀ ω, auxModel_ptr b c (K₀ * G ω) + auxModel_ptr b c (T ω * G ω) =
      if b = c then 1 else 0 := by
    intro ω
    rw [← map_add, ← Matrix.add_mul, hGeq, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp (hu ω)), auxModel_ptr_one hW]
  -- the random term through Gaussian integration by parts
  set r : ℝ := (max 1 g)⁻¹ * Real.sqrt t with hr
  have hr2 : r * r = gammaG g * t := by
    rw [hr, gammaG]
    have : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht
    rw [mul_mul_mul_comm, this, ← mul_inv, ← sq]
  have hTi : ∀ i, T (Pi.single i 1) = r • blockDiagOp (gueBlock W L (Pi.single i 1)) := by
    intro i; rfl
  have hTG : ∀ ω, auxModel_ptr b c (T ω * G ω) =
      ∑ i, (ω i : ℂ) * auxModel_ptr b c (T (Pi.single i 1) * G ω) := by
    intro ω
    rw [auxModel_clm_decomp T ω, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_mul, map_smul, Complex.real_smul]
  have hstein : ∀ i, ∫ ω, (ω i : ℂ) * auxModel_ptr b c (T (Pi.single i 1) * G ω) ∂(μ W L) =
      ∫ ω, auxModel_ptr b c (T (Pi.single i 1) * -(G ω * T (Pi.single i 1) * G ω)) ∂(μ W L) := by
    intro i
    have h := auxModel_stein K₀ T hu (fun ω => by rw [← hGeq]; exact hGb ω)
      ((auxModel_ptr b c).comp (ContinuousLinearMap.mul ℝ _ (T (Pi.single i 1)))) i
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply'] at h
    simp only [hGeq]
    exact h
  have hcomplete : ∀ ω, ∑ i, auxModel_ptr b c (T (Pi.single i 1) * -(G ω * T (Pi.single i 1) * G ω))
      = -(((gammaG g * t : ℝ) : ℂ) * (auxModel_ptr b b (G ω) * auxModel_ptr b c (G ω))) := by
    intro ω
    have h1 : ∑ i, T (Pi.single i 1) * -(G ω * T (Pi.single i 1) * G ω) =
        -((r * r) • ((∑ i, blockDiagOp (gueBlock W L (Pi.single i 1)) * G ω *
          blockDiagOp (gueBlock W L (Pi.single i 1))) * G ω)) := by
      rw [Finset.sum_mul, Finset.smul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hTi]
      simp only [Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    rw [← map_sum, h1, auxModel_complete W L hW, map_neg, map_smul, auxModel_ptr_diag_mul, hr2,
      Complex.real_smul]
  have hcoord : ∀ i, Integrable (fun ω => (ω i : ℂ) * auxModel_ptr b c (T (Pi.single i 1) * G ω))
      (μ W L) := fun i =>
    auxModel_integrable_coord_mul i (f := fun ω => auxModel_ptr b c (T (Pi.single i 1) * G ω))
      ((auxModel_ptr b c).continuous.comp (continuous_const.mul hGc))
      (‖auxModel_ptr b c‖ * (‖T (Pi.single i 1)‖ * η⁻¹))
      (fun ω => (ContinuousLinearMap.le_opNorm _ _).trans (by
        gcongr; exact (norm_mul_le _ _).trans (by gcongr; exact hGb ω)))
  have hbdd : ∀ i, Integrable
      (fun ω => auxModel_ptr b c (T (Pi.single i 1) * -(G ω * T (Pi.single i 1) * G ω))) (μ W L) :=
    fun i => hint (auxModel_ptr b c) (fun X => T (Pi.single i 1) * -(X * T (Pi.single i 1) * X))
      (continuous_const.mul ((continuous_id.mul continuous_const).mul continuous_id).neg)
      (‖T (Pi.single i 1)‖ * (η⁻¹ * ‖T (Pi.single i 1)‖ * η⁻¹)) (fun ω => by
        refine (norm_mul_le _ _).trans ?_
        rw [norm_neg]
        gcongr
        refine norm_mul₃_le.trans ?_
        gcongr <;> exact hGb ω)
  have hrand : ∫ ω, auxModel_ptr b c (T ω * G ω) ∂(μ W L) =
      -(((gammaG g * t : ℝ) : ℂ) * ∫ ω, auxModel_ptr b b (G ω) * auxModel_ptr b c (G ω) ∂(μ W L))
      := by
    calc ∫ ω, auxModel_ptr b c (T ω * G ω) ∂(μ W L)
        = ∫ ω, ∑ i, (ω i : ℂ) * auxModel_ptr b c (T (Pi.single i 1) * G ω) ∂(μ W L) :=
          integral_congr_ae (Eventually.of_forall hTG)
      _ = ∑ i, ∫ ω, (ω i : ℂ) * auxModel_ptr b c (T (Pi.single i 1) * G ω) ∂(μ W L) :=
          integral_finsetSum _ fun i _ => hcoord i
      _ = ∑ i, ∫ ω, auxModel_ptr b c (T (Pi.single i 1) * -(G ω * T (Pi.single i 1) * G ω))
            ∂(μ W L) := Finset.sum_congr rfl fun i _ => hstein i
      _ = ∫ ω, ∑ i, auxModel_ptr b c (T (Pi.single i 1) * -(G ω * T (Pi.single i 1) * G ω))
            ∂(μ W L) := (integral_finsetSum _ fun i _ => hbdd i).symm
      _ = _ := by
          rw [integral_congr_ae (Eventually.of_forall hcomplete), integral_neg,
            integral_const_mul]
  -- the deterministic term
  have hdet : ∫ ω, auxModel_ptr b c (K₀ * G ω) ∂(μ W L) =
      ∑ d, ((hopB g : ℂ) * cycleAdj L b d) * ∫ ω, auxModel_ptr d c (G ω) ∂(μ W L) -
        zChar g E m t * ∫ ω, auxModel_ptr b c (G ω) ∂(μ W L) := by
    have hi : ∀ d, Integrable (fun ω => auxModel_ptr d c (G ω)) (μ W L) := fun d =>
      hint (auxModel_ptr d c) id continuous_id η⁻¹ hGb
    simp only [hK₀, auxModel_ptr_K_mul]
    rw [integral_sub (integrable_finsetSum _ fun d _ => (hi d).const_mul _)
      ((hi b).const_mul _), integral_finsetSum _ fun d _ => (hi d).const_mul _,
      integral_const_mul]
    simp only [integral_const_mul]
  have hTint : Integrable (fun ω => auxModel_ptr b c (T ω * G ω)) (μ W L) :=
    (integrable_finsetSum _ fun i _ => hcoord i).congr
      (Eventually.of_forall fun ω => (hTG ω).symm)
  have htot := congrArg (fun f => ∫ ω, f ω ∂(μ W L)) (funext hpt)
  simp only at htot
  rw [integral_add (hint (auxModel_ptr b c) (fun X => K₀ * X) (continuous_const.mul continuous_id)
      (‖K₀‖ * η⁻¹) fun ω => (norm_mul_le _ _).trans (by gcongr; exact hGb ω)) hTint,
    integral_const, probReal_univ, one_smul, hdet, hrand] at htot
  rw [← htot]; ring

end MeanField

section Shift

/-- `b.val = (a.val + 1) mod (n+1)` is `b = a + 1`. -/
private lemma auxModel_val_succ_iff {n : ℕ} (a b : Fin (n + 1)) :
    b.val = (a.val + 1) % (n + 1) ↔ b = a + 1 := by
  rw [Fin.ext_iff, Fin.val_add, Fin.val_one', Nat.add_mod_mod]

/-- The cycle adjacency matrix is invariant under the rotation `x ↦ x + 1`. -/
private lemma auxModel_cycleAdj_shift {n : ℕ} (x y : Fin (n + 1)) :
    cycleAdj (n + 1) (x + 1) (y + 1) = cycleAdj (n + 1) x y := by
  simp only [cycleAdj, Matrix.of_apply, auxModel_val_succ_iff, add_left_inj]

/-- The coordinate rotation `(b, α, β) ↦ (b + 1, α, β)` of the sample space. -/
private def auxModel_rot (W n : ℕ) :
    (Fin (n + 1) × Fin W × Fin W) ≃ (Fin (n + 1) × Fin W × Fin W) :=
  Equiv.prodCongr (Equiv.addRight 1) (Equiv.refl _)

/-- The rotated sample `ω'(b + 1, α, β) = ω(b, α, β)`. -/
private def auxModel_shift (W n : ℕ) : Ω W (n + 1) ≃ᵐ Ω W (n + 1) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℝ) (auxModel_rot W n)

private lemma auxModel_shift_apply (W n : ℕ) (ω : Ω W (n + 1)) (x : Fin (n + 1)) (α β : Fin W) :
    auxModel_shift W n ω (x + 1, α, β) = ω (x, α, β) :=
  MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ) (auxModel_rot W n) ω (x, α, β)

/-- The rotation preserves the Gaussian product measure. -/
private lemma auxModel_shift_mp (W n : ℕ) :
    MeasurePreserving (auxModel_shift W n) (μ W (n + 1)) (μ W (n + 1)) :=
  measurePreserving_piCongrLeft (fun _ => gaussianReal 0 1) (auxModel_rot W n)

/-- The resolvent of the rotated sample is the rotated resolvent. -/
private lemma auxModel_G_shift (g : ℝ) (W n : ℕ) (E : ℝ) (m : ℂ) (t : ℝ) (ω : Ω W (n + 1))
    (x y : Fin (n + 1)) (α β : Fin W) :
    auxG g W (n + 1) E m t (auxModel_shift W n ω) (x + 1, α) (y + 1, β) =
      auxG g W (n + 1) E m t ω (x, α) (y, β) := by
  set ê : (Fin (n + 1) × Fin W) ≃ (Fin (n + 1) × Fin W) :=
    Equiv.prodCongr (Equiv.addRight 1) (Equiv.refl _)
  have hV : ∀ x : Fin (n + 1), gueBlock W (n + 1) (auxModel_shift W n ω) (x + 1) =
      gueBlock W (n + 1) ω x := by
    intro x; ext α β
    simp only [gueBlock, Matrix.of_apply, auxModel_shift_apply]
  have hH : (Hdet g (fun b =>
      ((Real.sqrt t : ℝ) : ℂ) • gueBlock W (n + 1) (auxModel_shift W n ω) b) -
      zChar g E m t • (1 : Matrix (Fin (n + 1) × Fin W) (Fin (n + 1) × Fin W) ℂ)).submatrix ê ê =
      Hdet g (fun b => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W (n + 1) ω b) -
        zChar g E m t • (1 : Matrix (Fin (n + 1) × Fin W) (Fin (n + 1) × Fin W) ℂ) := by
    ext ⟨x, α⟩ ⟨y, β⟩
    simp only [ê, Matrix.submatrix_apply, Equiv.prodCongr_apply, Equiv.coe_addRight,
      Equiv.coe_refl, Prod.map_apply, id, Hdet, blockDiagOp, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.add_apply, Matrix.of_apply, Matrix.kroneckerMap_apply, auxModel_cycleAdj_shift,
      add_left_inj, hV, Matrix.one_apply, Prod.mk.injEq]
  have h := congrArg (fun M => M⁻¹) hH
  simp only [Matrix.inv_submatrix_equiv] at h
  have h2 := congrFun (congrFun h (x, α)) (y, β)
  simpa [ê, auxG] using h2

/-- The expected block traces `E⟨G⟩_{cc}` do not depend on `c` (invariance of the law under the
rotation of the blocks). -/
private lemma auxModel_mean_shift (g : ℝ) (W n : ℕ) (E : ℝ) (m : ℂ) (t : ℝ) (c : Fin (n + 1)) :
    ∫ ω, auxModel_ptr c c (auxG g W (n + 1) E m t ω) ∂(μ W (n + 1)) =
      ∫ ω, auxModel_ptr 0 0 (auxG g W (n + 1) E m t ω) ∂(μ W (n + 1)) := by
  have step : ∀ x : Fin (n + 1),
      ∫ ω, auxModel_ptr (x + 1) (x + 1) (auxG g W (n + 1) E m t ω) ∂(μ W (n + 1)) =
      ∫ ω, auxModel_ptr x x (auxG g W (n + 1) E m t ω) ∂(μ W (n + 1)) := by
    intro x
    rw [← (auxModel_shift_mp W n).integral_comp' (fun ω =>
      auxModel_ptr (x + 1) (x + 1) (auxG g W (n + 1) E m t ω))]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [auxModel_ptr_apply, auxModel_G_shift]
  refine Fin.induction (motive := fun c => ∫ ω, auxModel_ptr c c (auxG g W (n + 1) E m t ω)
    ∂(μ W (n + 1)) = ∫ ω, auxModel_ptr 0 0 (auxG g W (n + 1) E m t ω) ∂(μ W (n + 1))) rfl
    (fun i ih => ?_) c
  rw [← Fin.coeSucc_eq_succ, step, ih]

end Shift

section Stability

open scoped Matrix.Norms.L2Operator

/-- The real inequality behind the stability factor: `(tγ)² |X|² ≤ T (1 + γ|e|/η)`. -/
private lemma auxModel_stab_real {t T γ η y Sb a e X2 : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hT : T < 1) (hγ : 0 < γ) (hη : 0 < η) (hy : η + t * γ * a ≤ y) (ha : 0 ≤ a) (he : 0 ≤ e)
    (hward : y * Sb ≤ a + e) (hX2 : X2 ≤ Sb * γ⁻¹) :
    (t * γ) ^ 2 * X2 ≤ T * (1 + γ * e / η) := by
  have hT0 : 0 ≤ T := ht0.trans htT
  have hta : 0 ≤ t * γ * a := by positivity
  have hy0 : 0 < y := by linarith
  have ht1 : t ≤ 1 := by linarith
  have ht2 : t ^ 2 ≤ T := by nlinarith
  have h1 : (t * γ) ^ 2 * X2 ≤ t ^ 2 * γ * Sb := by
    calc (t * γ) ^ 2 * X2 ≤ (t * γ) ^ 2 * (Sb * γ⁻¹) := by gcongr
      _ = t ^ 2 * γ * Sb := by field_simp
  have h2 : y * (t ^ 2 * γ * Sb) ≤ t ^ 2 * γ * (a + e) := by
    have : 0 ≤ t ^ 2 * γ := by positivity
    calc y * (t ^ 2 * γ * Sb) = t ^ 2 * γ * (y * Sb) := by ring
      _ ≤ t ^ 2 * γ * (a + e) := by gcongr
  have h3a : t ^ 2 * γ * a ≤ T * y := by
    have : t ^ 2 * γ * a = t * (t * γ * a) := by ring
    rw [this]
    calc t * (t * γ * a) ≤ T * (t * γ * a) := by gcongr
      _ ≤ T * y := by gcongr; linarith
  have h3e : t ^ 2 * γ * e ≤ y * (T * (γ * e / η)) := by
    have hq : 1 ≤ y / η := by rw [le_div_iff₀ hη]; linarith
    calc t ^ 2 * γ * e ≤ T * γ * e := by gcongr
      _ = T * γ * e * 1 := by ring
      _ ≤ T * γ * e * (y / η) := by gcongr
      _ = y * (T * (γ * e / η)) := by ring
  have h4 : y * ((t * γ) ^ 2 * X2) ≤ y * (T * (1 + γ * e / η)) := by
    calc y * ((t * γ) ^ 2 * X2) ≤ y * (t ^ 2 * γ * Sb) := by gcongr
      _ ≤ t ^ 2 * γ * (a + e) := h2
      _ = t ^ 2 * γ * a + t ^ 2 * γ * e := by ring
      _ ≤ T * y + y * (T * (γ * e / η)) := add_le_add h3a h3e
      _ = y * (T * (1 + γ * e / η)) := by ring
  exact le_of_mul_le_mul_left h4 hy0

/-- The final step: from `d (1 - x) = e`, `|x|² ≤ T (1 + γ|e|/η)` and `|d| ≤ B`,
`|d| ≤ (4/(1-T) + 2γB/(η(1-T))) |e|`. -/
private lemma auxModel_stab_final {d x e : ℂ} {T γ η B : ℝ} (hT0 : 0 ≤ T) (hT : T < 1)
    (hγ : 0 < γ) (hη : 0 < η) (hB : 0 ≤ B) (hkey : d * (1 - x) = e)
    (hx2 : ‖x‖ ^ 2 ≤ T * (1 + γ * ‖e‖ / η)) (hd : ‖d‖ ≤ B) :
    ‖d‖ ≤ (4 / (1 - T) + 2 * γ * B / (η * (1 - T))) * ‖e‖ := by
  have hT1 : 0 < 1 - T := by linarith
  have hen : 0 ≤ ‖e‖ := norm_nonneg e
  have hA : 0 ≤ 2 * γ * B / (η * (1 - T)) * ‖e‖ := by positivity
  by_cases hcase : 2 * γ * ‖e‖ ≤ (1 - T) * η
  · have hq : γ * ‖e‖ / η ≤ (1 - T) / 2 := by
      rw [div_le_iff₀ hη]; linarith
    have hx2' : ‖x‖ ^ 2 ≤ (1 + T) / 2 := by
      refine hx2.trans ?_
      calc T * (1 + γ * ‖e‖ / η) ≤ T * (1 + (1 - T) / 2) := by gcongr
        _ ≤ (1 + T) / 2 := by nlinarith
    have hfac : (1 - T) / 4 ≤ ‖1 - x‖ := by
      have h1 : 1 - ‖x‖ ≤ ‖1 - x‖ := by
        have := norm_sub_norm_le (1 : ℂ) x
        rwa [norm_one] at this
      have h2 : (1 - ‖x‖ ^ 2) / 2 ≤ 1 - ‖x‖ := by nlinarith [sq_nonneg (1 - ‖x‖)]
      linarith
    have hpos : 0 < ‖1 - x‖ := lt_of_lt_of_le (by linarith) hfac
    have hde : ‖d‖ * ‖1 - x‖ = ‖e‖ := by rw [← norm_mul, hkey]
    have h4 : ‖d‖ * ((1 - T) / 4) ≤ ‖e‖ := by
      rw [← hde]; gcongr
    have h5 : ‖d‖ ≤ 4 / (1 - T) * ‖e‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hT1]; linarith
    linarith
  · rw [not_le] at hcase
    have h1 : 1 ≤ 2 * γ * ‖e‖ / (η * (1 - T)) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have h2 : B ≤ 2 * γ * B / (η * (1 - T)) * ‖e‖ := by
      calc B = B * 1 := by ring
        _ ≤ B * (2 * γ * ‖e‖ / (η * (1 - T))) := by gcongr
        _ = 2 * γ * B / (η * (1 - T)) * ‖e‖ := by ring
    have h3 : 0 ≤ 4 / (1 - T) * ‖e‖ := by positivity
    nlinarith

/-- Scalar stability of the one-loop mean field: if `R` solves the perturbed Dyson equation
`(b₀ A_L - (z + tγ m̄)) R = 1 + Err` with `R_cc = m̄`, then `|m̄ - m| ≤ C L η⁻¹ ε` where
`ε` bounds the entries of `Err` (the mean-field step of the proof of Lemma 5.4
[uvc:lem:orbital-limit]). -/
private lemma auxModel_stability {L : ℕ} (b0 γ : ℝ) (hγ : 0 < γ) (w m mb z : ℂ) (t T η : ℝ)
    (ht0 : 0 ≤ t) (htT : t ≤ T) (hT : T < 1) (hη : 0 < η) (hz : η ≤ z.im) (hm : 0 < m.im)
    (hzm : z + ((t * γ : ℝ) : ℂ) * m = w)
    (hMdiag : ∀ c, ((b0 : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹ c c = m)
    (hward : ∀ c, γ * ∑ d, ‖((b0 : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹ d c‖ ^ 2
      = 1)
    (hmb_im : 0 ≤ mb.im) (hmb : ‖mb‖ ≤ η⁻¹)
    (R Err : Matrix (Fin L) (Fin L) ℂ) (hR : ∀ c, R c c = mb) {ε : ℝ}
    (hErr : ∀ b c, ‖Err b c‖ ≤ ε)
    (hEq : ((b0 : ℂ) • cycleAdj L - (z + ((t * γ : ℝ) : ℂ) * mb) • 1) * R = 1 + Err)
    (c : Fin L) :
    ‖mb - m‖ ≤ (4 / (1 - T) + 2 * γ * (η⁻¹ + ‖m‖) / (η * (1 - T))) * (L * (η⁻¹ * ε)) := by
  set A : Matrix (Fin L) (Fin L) ℂ := (b0 : ℂ) • cycleAdj L with hA
  have hAh : A.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [hA, Matrix.conjTranspose_smul, (cycleAdj_isHermitian L).eq]
    simp [Complex.conj_ofReal]
  set wb := z + ((t * γ : ℝ) : ℂ) * mb with hwb
  have hwb_im : wb.im = z.im + t * γ * mb.im := by
    simp [hwb, Complex.add_im, Complex.mul_im]
  have htγ : 0 ≤ t * γ := mul_nonneg ht0 hγ.le
  have htγm : 0 ≤ t * γ * mb.im := mul_nonneg htγ hmb_im
  have hwb_η : η ≤ wb.im := by rw [hwb_im]; linarith
  have hw_im : w.im = z.im + t * γ * m.im := by
    rw [← hzm]; simp [Complex.add_im, Complex.mul_im]
  have hw_η : η ≤ w.im := by rw [hw_im]; nlinarith
  have hwb0 : wb.im ≠ 0 := (lt_of_lt_of_le hη hwb_η).ne'
  have hw0 : w.im ≠ 0 := (lt_of_lt_of_le hη hw_η).ne'
  set Mb := (A - wb • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹ with hMb
  set M := (A - w • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹ with hM
  have hdb := (Matrix.isUnit_iff_isUnit_det _).mp (auxModel_isUnit hAh hwb0)
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp (auxModel_isUnit hAh hw0)
  have hMbn : ‖Mb‖ ≤ η⁻¹ := auxModel_norm_inv_le hAh hη (hwb_η.trans (le_abs_self _))
  have h1 : Mb * (A - wb • 1) = 1 := Matrix.nonsing_inv_mul _ hdb
  have h2 : (A - w • 1) * M = 1 := Matrix.mul_nonsing_inv _ hd
  -- `R = Mb (1 + Err)`
  have hRe : R = Mb + Mb * Err := by
    have := congrArg (fun X => Mb * X) hEq
    simp only [← Matrix.mul_assoc] at this
    rw [h1, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one] at this
    exact this
  set e := (Mb * Err) c c with he
  have hmbe : mb = Mb c c + e := by
    rw [← hR c, hRe, Matrix.add_apply]
  have he_le : ‖e‖ ≤ L * (η⁻¹ * ε) := by
    rw [he, Matrix.mul_apply]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ d, ‖Mb c d * Err d c‖ ≤ ∑ _d : Fin L, η⁻¹ * ε := Finset.sum_le_sum fun d _ => by
          rw [norm_mul]
          exact mul_le_mul ((auxModel_norm_entry_le Mb c d).trans hMbn) (hErr d c)
            (norm_nonneg _) (by positivity)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- resolvent identity
  have hsplit : A - w • (1 : Matrix (Fin L) (Fin L) ℂ) = (A - wb • 1) + (wb - w) • 1 := by
    rw [sub_smul]; abel
  have hres : Mb - M = (wb - w) • (Mb * M) := by
    calc Mb - M = Mb * ((A - w • 1) * M) - M := by rw [h2, Matrix.mul_one]
      _ = Mb * (((A - wb • 1) + (wb - w) • 1) * M) - M := by rw [hsplit]
      _ = (wb - w) • (Mb * M) := by
          rw [Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_assoc, h1, Matrix.one_mul,
            Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]
          abel
  have hwbw : wb - w = ((t * γ : ℝ) : ℂ) * (mb - m) := by
    rw [hwb, ← hzm]; ring
  have hdiag := congrFun (congrFun hres c) c
  rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, hwbw, hMdiag c, smul_eq_mul] at hdiag
  set X := ∑ d, Mb c d * M d c with hX
  have hkey : (mb - m) * (1 - ((t * γ : ℝ) : ℂ) * X) = e := by
    linear_combination hdiag + hmbe
  -- Ward identity for `Mb`
  set Sb := ∑ d, ‖Mb c d‖ ^ 2 with hSb
  have hSb0 : 0 ≤ Sb := Finset.sum_nonneg fun _ _ => by positivity
  have hward_b : (Mb c c).im = wb.im * Sb := auxModel_im_diag hAh hwb0 c
  have hMbcc_im : wb.im * Sb ≤ mb.im + ‖e‖ := by
    rw [← hward_b]
    have : (Mb c c).im = mb.im - e.im := by rw [hmbe]; simp
    rw [this]
    linarith [(abs_le.mp (Complex.abs_im_le_norm e)).1]
  -- Cauchy–Schwarz
  have hX2 : ‖X‖ ^ 2 ≤ Sb * γ⁻¹ := by
    have h3 : ∑ d, ‖M d c‖ ^ 2 = γ⁻¹ := by
      have := hward c
      field_simp
      linarith
    have h4 : ‖X‖ ≤ Real.sqrt Sb * Real.sqrt γ⁻¹ := by
      rw [← h3]
      refine (norm_sum_le _ _).trans ?_
      simp only [norm_mul]
      exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    calc ‖X‖ ^ 2 ≤ (Real.sqrt Sb * Real.sqrt γ⁻¹) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h4 2
      _ = Sb * γ⁻¹ := by
          rw [mul_pow, Real.sq_sqrt hSb0, Real.sq_sqrt (inv_nonneg.mpr hγ.le)]
  have hx2 : ‖((t * γ : ℝ) : ℂ) * X‖ ^ 2 ≤ T * (1 + γ * ‖e‖ / η) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htγ, mul_pow]
    exact auxModel_stab_real ht0 htT hT hγ hη (by rw [hwb_im]; linarith) hmb_im (norm_nonneg e)
      hMbcc_im hX2
  have hd : ‖mb - m‖ ≤ η⁻¹ + ‖m‖ := (norm_sub_le _ _).trans (by linarith)
  have hfin := auxModel_stab_final (ht0.trans htT) hT hγ hη (by positivity) hkey hx2 hd
  refine hfin.trans ?_
  gcongr

end Stability

section One

open scoped Matrix.Norms.L2Operator

/-- `E|f| ≤ (E|f|²)^{1/2}` on the Gaussian probability space. -/
private lemma auxModel_integral_norm_le_sqrt {W L : ℕ} {f : Ω W L → ℂ}
    (hf1 : Integrable (fun ω => ‖f ω‖) (μ W L)) (hf2 : Integrable (fun ω => ‖f ω‖ ^ 2) (μ W L)) :
    ∫ ω, ‖f ω‖ ∂(μ W L) ≤ Real.sqrt (∫ ω, ‖f ω‖ ^ 2 ∂(μ W L)) := by
  set a := ∫ ω, ‖f ω‖ ∂(μ W L) with ha
  have ha0 : 0 ≤ a := integral_nonneg fun ω => norm_nonneg _
  have h0 : 0 ≤ ∫ ω, (‖f ω‖ - a) ^ 2 ∂(μ W L) := integral_nonneg fun ω => sq_nonneg _
  have e : (fun ω => (‖f ω‖ - a) ^ 2) =
      fun ω => (‖f ω‖ ^ 2 - (2 * a) * ‖f ω‖) + a ^ 2 := funext fun ω => by ring
  have i1 : ∫ ω, ((‖f ω‖ ^ 2 - (2 * a) * ‖f ω‖) + a ^ 2) ∂(μ W L) =
      ∫ ω, (‖f ω‖ ^ 2 - (2 * a) * ‖f ω‖) ∂(μ W L) + ∫ _ω, a ^ 2 ∂(μ W L) :=
    integral_add (hf2.sub (hf1.const_mul _)) (integrable_const _)
  have i2 : ∫ ω, (‖f ω‖ ^ 2 - (2 * a) * ‖f ω‖) ∂(μ W L) =
      ∫ ω, ‖f ω‖ ^ 2 ∂(μ W L) - ∫ ω, (2 * a) * ‖f ω‖ ∂(μ W L) :=
    integral_sub hf2 (hf1.const_mul _)
  rw [e, i1, i2, integral_const_mul, integral_const, probReal_univ, one_smul, ← ha] at h0
  exact Real.le_sqrt_of_sq_le (by nlinarith)

/-- The expected normalized block trace of the auxiliary model is within `C/W̃` of `m^σ`,
uniformly on `[0, T]` (Lemma 5.4 [uvc:lem:orbital-limit] at `k = 1`). -/
theorem auxLoop_one (g : ℝ) (hg : 0 < g) (L : ℕ) (hL : 3 ≤ L) (E : ℝ) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (T : ℝ) (hT0 : 0 ≤ T) (hT : T < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ Wt : ℕ, 1 ≤ Wt → ∀ t : ℝ, 0 ≤ t → t ≤ T → ∀ (c : Fin L) (s : Bool),
      ‖auxLoop g Wt L E m t 1 ![c] ![s] - (if s then m else star m)‖ ≤ C / Wt := by
  obtain ⟨C₁, hC₁, hvar⟩ := auxLoop_variance g hg L hL E m hm T hT0 hT 1 le_rfl
  have hD := primData_of_root g L hL E m hm
  set γ := gammaG g with hγdef
  have hγ : 0 < γ := hD.pos
  set η := (1 - T) * γ * m.im with hηdef
  have hη : 0 < η := mul_pos (mul_pos (by linarith) hγ) hm.1
  have hz : ∀ t, t ≤ T → η ≤ (zChar g E m t).im := by
    intro t ht
    rw [auxModel_im_zChar, hηdef]
    have := hm.1
    gcongr
  set Cs := 4 / (1 - T) + 2 * γ * (η⁻¹ + ‖m‖) / (η * (1 - T)) with hCs
  have hCs0 : 0 ≤ Cs := by
    have : 0 < 1 - T := by linarith
    positivity
  refine ⟨Cs * (L * (η⁻¹ * (γ * (η⁻¹ * Real.sqrt C₁)))) + 1, by positivity, ?_⟩
  intro W hW t ht0 htT
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  suffices key : ∀ c, ‖auxLoop g W L E m t 1 ![c] ![true] - m‖ ≤
      (Cs * (L * (η⁻¹ * (γ * (η⁻¹ * Real.sqrt C₁)))) + 1) / W by
    intro c s
    cases s
    · have hconj : auxLoop g W L E m t 1 ![c] ![false] =
          star (auxLoop g W L E m t 1 ![c] ![true]) := by
        simp only [auxLoop, pow_zero, one_mul, Nat.sub_self]
        rw [show (star (∫ ω, loopTr (auxG g W L E m t ω) ![c] ![true] ∂(μ W L)) : ℂ) =
          ∫ ω, star (loopTr (auxG g W L E m t ω) ![c] ![true]) ∂(μ W L) from
          (integral_conj (𝕜 := ℂ)).symm]
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        change loopTr (auxG g W L E m t ω) ![c] ![false] =
          star (loopTr (auxG g W L E m t ω) ![c] ![true])
        rw [star_loopTr]
        congr 1
        · funext j; simp [Fin.fin_one_eq_zero j]
        · funext j; simp [Fin.fin_one_eq_zero j]
      simp only [hconj, Bool.false_eq_true, ite_false]
      rw [← star_sub, norm_star]
      exact key c
    · simpa using key c
  intro c
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  have hzt := hz t htT
  have hz0 : (zChar g E m t).im ≠ 0 := (lt_of_lt_of_le hη hzt).ne'
  set G : Ω W (n + 1) → Matrix (Fin (n + 1) × Fin W) (Fin (n + 1) × Fin W) ℂ :=
    fun ω => auxG g W (n + 1) E m t ω with hGdef
  have hGc : Continuous G := by
    have := (auxModel_contDiff_inv (auxModel_K g W (n + 1) E m t) (auxModel_T g W (n + 1) t)
      (auxModel_isUnit_KT g W (n + 1) E m t hz0)).continuous
    convert this using 1
    funext ω; exact auxModel_G_eq g W (n + 1) E m t ω
  have hGb : ∀ ω, ‖G ω‖ ≤ η⁻¹ := fun ω => auxModel_norm_G_le g W (n + 1) E m t hη hzt ω
  have hRc : ∀ b c, Continuous fun ω => auxModel_ptr b c (G ω) := fun b c =>
    (auxModel_ptr b c).continuous.comp hGc
  have hRb : ∀ b c ω, ‖auxModel_ptr b c (G ω)‖ ≤ η⁻¹ := fun b c ω =>
    (auxModel_norm_ptr_le hW b c _).trans (hGb ω)
  have hRi : ∀ b c, Integrable (fun ω => auxModel_ptr b c (G ω)) (μ W (n + 1)) := fun b c =>
    auxModel_integrable_bdd (hRc b c) η⁻¹ (hRb b c)
  obtain ⟨Rb, hRbe⟩ : ∃ Rb : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      ∀ b c, Rb b c = ∫ ω, auxModel_ptr b c (G ω) ∂(μ W (n + 1)) :=
    ⟨fun b c => ∫ ω, auxModel_ptr b c (G ω) ∂(μ W (n + 1)), fun _ _ => rfl⟩
  obtain ⟨mb, hmbe⟩ : ∃ mb : ℂ, mb = Rb 0 0 := ⟨_, rfl⟩
  have hRdiag : ∀ b, Rb b b = mb := fun b => by
    rw [hmbe, hRbe, hRbe]; exact auxModel_mean_shift g W n E m t b
  have hloop : ∀ b, auxLoop g W (n + 1) E m t 1 ![b] ![true] = Rb b b := by
    intro b
    rw [hRbe]
    simp only [auxLoop, Nat.sub_self, pow_zero, one_mul, hGdef]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    change loopTr (auxG g W (n + 1) E m t ω) ![b] ![true] =
      auxModel_ptr b b (auxG g W (n + 1) E m t ω)
    rw [loopTr_one, auxModel_ptr_apply]
  -- the variance of the diagonal block traces
  have hcov : ∀ b c, ‖∫ ω, auxModel_ptr b b (G ω) * auxModel_ptr b c (G ω) ∂(μ W (n + 1)) -
      mb * Rb b c‖ ≤ η⁻¹ * (Real.sqrt C₁ / W) := by
    intro b c
    obtain ⟨hi2, hv⟩ := hvar W hW t ht0 htT ![b] ![true]
    have hfe : ∀ ω, (W : ℂ) ^ (1 - 1) * loopTr (auxG g W (n + 1) E m t ω) ![b] ![true] -
        auxLoop g W (n + 1) E m t 1 ![b] ![true] = auxModel_ptr b b (G ω) - mb := by
      intro ω
      rw [hloop, hRdiag, Nat.sub_self, pow_zero, one_mul, loopTr_one, auxModel_ptr_apply]
    simp only [hfe] at hi2 hv
    have hprod : Integrable (fun ω => auxModel_ptr b b (G ω) * auxModel_ptr b c (G ω))
        (μ W (n + 1)) :=
      auxModel_integrable_bdd (f := fun ω => auxModel_ptr b b (G ω) * auxModel_ptr b c (G ω))
        ((hRc b b).mul (hRc b c)) (η⁻¹ * η⁻¹)
        (fun ω => (norm_mul_le _ _).trans (mul_le_mul (hRb b b ω) (hRb b c ω) (norm_nonneg _)
          (by positivity)))
    have hdiff : ∫ ω, auxModel_ptr b b (G ω) * auxModel_ptr b c (G ω) ∂(μ W (n + 1)) -
        mb * Rb b c = ∫ ω, (auxModel_ptr b b (G ω) - mb) * auxModel_ptr b c (G ω)
          ∂(μ W (n + 1)) := by
      rw [show (fun ω => (auxModel_ptr b b (G ω) - mb) * auxModel_ptr b c (G ω)) =
        fun ω => auxModel_ptr b b (G ω) * auxModel_ptr b c (G ω) - mb * auxModel_ptr b c (G ω)
        from funext fun ω => sub_mul _ _ _]
      rw [integral_sub hprod ((hRi b c).const_mul mb), integral_const_mul, hRbe]
    have hi1 : Integrable (fun ω => ‖auxModel_ptr b b (G ω) - mb‖) (μ W (n + 1)) :=
      ((hRi b b).sub (integrable_const mb)).norm
    rw [hdiff]
    calc ‖∫ ω, (auxModel_ptr b b (G ω) - mb) * auxModel_ptr b c (G ω) ∂(μ W (n + 1))‖
        ≤ ∫ ω, ‖(auxModel_ptr b b (G ω) - mb) * auxModel_ptr b c (G ω)‖ ∂(μ W (n + 1)) :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ ω, η⁻¹ * ‖auxModel_ptr b b (G ω) - mb‖ ∂(μ W (n + 1)) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun ω => norm_nonneg _)
            (hi1.const_mul _) (Eventually.of_forall fun ω => ?_)
          dsimp only
          rw [norm_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (hRb b c ω) (norm_nonneg _)
      _ = η⁻¹ * ∫ ω, ‖auxModel_ptr b b (G ω) - mb‖ ∂(μ W (n + 1)) := integral_const_mul _ _
      _ ≤ η⁻¹ * Real.sqrt (C₁ / (W : ℝ) ^ 2) := by
          gcongr
          exact (auxModel_integral_norm_le_sqrt hi1 hi2).trans (Real.sqrt_le_sqrt hv)
      _ = η⁻¹ * (Real.sqrt C₁ / W) := by
          rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hW'.le]
  -- the perturbed Dyson equation for `E⟨G⟩`
  obtain ⟨Err, hErre⟩ : ∃ Err : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, ∀ b c, Err b c =
      ((γ * t : ℝ) : ℂ) * (∫ ω, auxModel_ptr b b (G ω) * auxModel_ptr b c (G ω) ∂(μ W (n + 1)) -
        mb * Rb b c) := ⟨fun b c => _, fun _ _ => rfl⟩
  have hEq : ((hopB g : ℂ) • cycleAdj (n + 1) -
      (zChar g E m t + ((t * γ : ℝ) : ℂ) * mb) • 1) * Rb = 1 + Err := by
    ext b c
    have h := auxModel_dyson_mean g W (n + 1) hW E m t ht0 hη hzt b c
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.add_apply,
      Matrix.one_apply, smul_eq_mul, Finset.mul_sum, hErre, hRbe]
    simp only [mul_assoc] at h ⊢
    rw [← hγdef] at h
    push_cast at h ⊢
    linear_combination h
  have hErr : ∀ b c, ‖Err b c‖ ≤ γ * (η⁻¹ * (Real.sqrt C₁ / W)) := by
    intro b c
    rw [hErre, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have ht1 : t ≤ 1 := by linarith
    calc γ * t * ‖_‖ ≤ γ * 1 * (η⁻¹ * (Real.sqrt C₁ / W)) := by
          gcongr
          exact hcov b c
      _ = _ := by ring
  -- the bounds on `m̄`
  have hmb_im : 0 ≤ mb.im := by
    rw [hmbe, hRbe]
    have := integral_im (hRi 0 0)
    simp only [RCLike.im_to_complex] at this
    rw [← this]
    refine integral_nonneg fun ω => ?_
    change 0 ≤ (auxModel_ptr 0 0 (auxG g W (n + 1) E m t ω)).im
    rw [auxModel_ptr_apply, auxG, Complex.mul_im, Complex.im_sum, Complex.re_sum]
    have hcast : ((W : ℂ)⁻¹).im = 0 := by simp
    rw [hcast, zero_mul, add_zero]
    have hre : 0 ≤ ((W : ℂ)⁻¹).re := by simp [Complex.inv_re]
    refine mul_nonneg hre (Finset.sum_nonneg fun α _ => ?_)
    rw [auxModel_im_diag (auxModel_A_herm g W (n + 1) t ω) hz0]
    exact mul_nonneg (le_trans hη.le hzt) (Finset.sum_nonneg fun _ _ => by positivity)
  have hmb : ‖mb‖ ≤ η⁻¹ := by
    rw [hmbe, hRbe]
    refine (norm_integral_le_of_norm_le_const (Eventually.of_forall (hRb 0 0))).trans ?_
    simp
  -- the root data
  have hMdiag : ∀ c, ((hopB g : ℂ) • cycleAdj (n + 1) -
      ((E : ℂ) + (γ : ℂ) * m) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ c c = m :=
    fun c => hD.diag c
  have hward : ∀ c, γ * ∑ d, ‖((hopB g : ℂ) • cycleAdj (n + 1) -
      ((E : ℂ) + (γ : ℂ) * m) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ d c‖ ^ 2 = 1 := by
    intro c
    change γ * ∑ d, ‖dysonMat (hopB g) γ (n + 1) E m d c‖ ^ 2 = 1
    rw [Finset.mul_sum]
    refine Eq.trans ?_ (hD.row_sum c)
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [pairP, Matrix.of_apply]
    rw [show dysonMat (hopB g) γ (n + 1) E m d c = dysonMat (hopB g) γ (n + 1) E m c d from
      congrFun (congrFun hD.symm c) d]
  have hzm : zChar g E m t + ((t * γ : ℝ) : ℂ) * m = (E : ℂ) + (γ : ℂ) * m := by
    simp only [zChar, hγdef]; push_cast; ring
  have hst := auxModel_stability (hopB g) γ hγ ((E : ℂ) + (γ : ℂ) * m) m mb (zChar g E m t) t T η
    ht0 htT hT hη hzt hm.1 hzm hMdiag hward hmb_im hmb Rb Err hRdiag hErr hEq c
  rw [hloop, hRdiag]
  refine hst.trans ?_
  rw [le_div_iff₀ hW']
  have : Cs * (((n + 1 : ℕ) : ℝ) * (η⁻¹ * (γ * (η⁻¹ * (Real.sqrt C₁ / W))))) * W =
      Cs * (((n + 1 : ℕ) : ℝ) * (η⁻¹ * (γ * (η⁻¹ * Real.sqrt C₁)))) := by
    field_simp
  rw [this]
  linarith

end One

end LSBA
