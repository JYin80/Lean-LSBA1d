import LSBA.Upper.SmallCutDiv
import LSBA.Upper.SmallScoreGrowth
import LSBA.Upper.AngularField
import LSBA.Gauss.DivergenceFrozen

/-!
# The hypotheses of Lemma 8.11 [up:lem:angular] for the small-coupling field

The field `χ X` of Lemma 8.12 [up:lem:small-contraction] grows at most linearly, by the pointwise
clauses of Lemma 9.3 [su:lem:chosen-generator] on `{χ ≠ 0}`: `‖K‖²_HS ≤ C`,
`g² ‖[K, R_4]‖ = g² ‖[K, P R_4 P]‖ ≤ 2 √C M₀`, `‖L‖²_HS ≤ 9 C² W⁻⁸` and `‖R_{q-1}‖ ≤ C W³`. It
allows Gaussian integration by parts (8.33) [up:eq:gaussian-divergence] after conditioning on the
preparation blocks, where its components vanish: every slice in the active coordinates is `C¹`
with polynomial growth, and the divergence is square integrable. With the cutoff clauses and
(8.34) [up:eq:angular-geometry] this gives the hypotheses of Lemma 8.11 [up:lem:angular] with
`C 𝔟` replaced by the bound of the Gaussian divergence in terms of `C`, `σ` and `M₀`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Entry bounds -/

/-- Every entry of a matrix is bounded by its operator norm. -/
private lemma SmallCutField_entry_le_opNorm {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ)
    (i j : Fin W) : ‖X i j‖ ≤ ‖X‖ := by
  have h := Matrix.l2_opNorm_mulVec X (WithLp.toLp 2 (Pi.single j (1 : ℂ)))
  have h1 : ‖(WithLp.toLp 2 (Pi.single j (1 : ℂ)) : EuclideanSpace ℂ (Fin W))‖ = 1 := by
    simp
  rw [h1, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le
    ((EuclideanSpace.equiv (Fin W) ℂ).symm (X *ᵥ Pi.single j (1 : ℂ))) i
  simpa [Matrix.mulVec_single_one] using this

/-- Every entry of a matrix is bounded by its Hilbert–Schmidt norm. -/
private lemma SmallCutField_entry_le_hsSq {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) (i j : Fin W) :
    ‖X i j‖ ≤ √(hsSq X) := by
  have h1 : ‖X i j‖ ^ 2 ≤ ∑ b, ‖X i b‖ ^ 2 :=
    Finset.single_le_sum (f := fun b => ‖X i b‖ ^ 2) (fun b _ => by positivity)
      (Finset.mem_univ j)
  have h2 : ∑ b, ‖X i b‖ ^ 2 ≤ hsSq X :=
    Finset.single_le_sum (f := fun a => ∑ b, ‖X a b‖ ^ 2) (fun a _ => by positivity)
      (Finset.mem_univ i)
  have := Real.abs_le_sqrt (h1.trans h2)
  rwa [abs_of_nonneg (norm_nonneg _)] at this

/-- If the entries of `A` and `B` are bounded by `α` and `β`, those of `A B` are bounded by
`W α β`. -/
private lemma SmallCutField_mul_entry_le {W : ℕ} {A B : Matrix (Fin W) (Fin W) ℂ} {α β : ℝ}
    (hA : ∀ i j, ‖A i j‖ ≤ α) (hB : ∀ i j, ‖B i j‖ ≤ β) (i j : Fin W) :
    ‖(A * B) i j‖ ≤ W * (α * β) := by
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ k ∈ (Finset.univ : Finset (Fin W)), ‖A i k * B k j‖ ≤ α * β := fun k _ => by
    rw [norm_mul]
    exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) ((norm_nonneg _).trans (hA i k))
  refine (Finset.sum_le_sum h).trans ?_
  simp

/-- If the entries of `A` and `B` are bounded by `α` and `β`, those of `[A, B]` are bounded by
`2 W α β`. -/
private lemma SmallCutField_comm_entry_le {W : ℕ} {A B : Matrix (Fin W) (Fin W) ℂ} {α β : ℝ}
    (hA : ∀ i j, ‖A i j‖ ≤ α) (hB : ∀ i j, ‖B i j‖ ≤ β) (i j : Fin W) :
    ‖(A * B - B * A) i j‖ ≤ 2 * W * (α * β) := by
  rw [Matrix.sub_apply]
  refine (norm_sub_le _ _).trans ?_
  have h1 := SmallCutField_mul_entry_le hA hB i j
  have h2 := SmallCutField_mul_entry_le hB hA i j
  rw [mul_comm β α] at h2
  linarith

/-- The entries of a block `V_{i+1}` (1.2) [eq:covariance] are bounded by `2 ‖ω‖`. -/
private lemma SmallCutField_gueBlock_entry_le {W q : ℕ} (hW : 1 ≤ W) (ω : Ω W q) (i : Fin q)
    (a b : Fin W) : ‖gueBlock W q ω i a b‖ ≤ 2 * ‖ω‖ := by
  have hdiv : ∀ (z : ℂ) (r : ℝ), 1 ≤ r → ‖z / (r : ℂ)‖ ≤ ‖z‖ := fun z r hr => by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    exact div_le_self (norm_nonneg _) hr
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hs1 : 1 ≤ Real.sqrt W := Real.one_le_sqrt.mpr hW1
  have hs2 : 1 ≤ Real.sqrt (2 * W) := Real.one_le_sqrt.mpr (by linarith)
  have hc : ∀ p, ‖((ω p : ℝ) : ℂ)‖ ≤ ‖ω‖ := fun p => by
    rw [Complex.norm_real]
    exact norm_le_pi_norm ω p
  have hω0 : 0 ≤ ‖ω‖ := norm_nonneg _
  simp only [gueBlock, Matrix.of_apply]
  split_ifs
  · exact (hdiv _ _ hs1).trans (by linarith [hc (i, a, a)])
  · refine (hdiv _ _ hs2).trans ?_
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul]
    linarith [hc (i, a, b), hc (i, b, a)]
  · refine (hdiv _ _ hs2).trans ?_
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul]
    linarith [hc (i, b, a), hc (i, a, b)]

/-- The sum of the moduli of the entries of the basis `hermBasis W`. -/
private def SmallCutField_hb (W : ℕ) : ℝ :=
  ∑ k : Fin W × Fin W, ∑ a, ∑ b, ‖hermBasis W k a b‖

private lemma SmallCutField_hb_nonneg (W : ℕ) : 0 ≤ SmallCutField_hb W := by
  unfold SmallCutField_hb
  positivity

/-- Standard coordinates (Section 8.4 [sec:upper-contraction-rates]) of an array whose entries are
bounded by `T`. -/
private lemma SmallCutField_hermCoord_le {W q : ℕ} {X : Fin q → Matrix (Fin W) (Fin W) ℂ} {T : ℝ}
    (hT : 0 ≤ T) (hX : ∀ i a b, ‖X i a b‖ ≤ T) :
    ‖hermCoord W q X‖ ≤ √W * (W * (W * (SmallCutField_hb W * T))) := by
  have hhb : ∀ k a b, ‖hermBasis W k a b‖ ≤ SmallCutField_hb W := fun k a b => by
    unfold SmallCutField_hb
    calc ‖hermBasis W k a b‖ ≤ ∑ b', ‖hermBasis W k a b'‖ :=
          Finset.single_le_sum (f := fun b' => ‖hermBasis W k a b'‖) (fun _ _ => norm_nonneg _)
            (Finset.mem_univ b)
      _ ≤ ∑ a', ∑ b', ‖hermBasis W k a' b'‖ :=
          Finset.single_le_sum (f := fun a' => ∑ b', ‖hermBasis W k a' b'‖)
            (fun _ _ => by positivity) (Finset.mem_univ a)
      _ ≤ _ :=
          Finset.single_le_sum (f := fun k' => ∑ a', ∑ b', ‖hermBasis W k' a' b'‖)
            (fun _ _ => by positivity) (Finset.mem_univ k)
  have hb0 := SmallCutField_hb_nonneg W
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun p => ?_
  rw [Real.norm_eq_abs]
  simp only [hermCoord]
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [Matrix.trace]
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ k ∈ (Finset.univ : Finset (Fin W)),
      ‖Matrix.diag (hermBasis W (p.2.1, p.2.2) * X p.1) k‖ ≤ W * (SmallCutField_hb W * T) :=
    fun k _ => SmallCutField_mul_entry_le (hhb _) (hX p.1) k k
  refine (Finset.sum_le_sum h).trans ?_
  simp

/-- The pointwise bound of the components of `X` of (9.10) [us:eq:physical] at a point where the
clauses of Lemma 9.3 [su:lem:chosen-generator] hold: `‖K‖²_HS ≤ C`,
`g² [K, R_4] = g² [K, P R_4 P]` with `g² ‖P R_4 P‖ ≤ M₀`, `‖L‖²_HS ≤ 9 C² W⁻⁸` by (9.26)
[su:eq:pair-matching-error], and `‖R_{q-1}‖ ≤ C W³`. -/
private lemma SmallCutField_field_le {W q : ℕ} {g E C σ M₀ : ℝ} (hW : 1 ≤ W) (hM₀ : 0 ≤ M₀)
    {P R : Matrix (Fin W) (Fin W) ℂ} (hPP : P * P = P) (hPR : P * R = R * P)
    {v : Fin W → ℂ} {Kv : (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ} {ω : Ω W q}
    (hpt : GenPoint W q g E P R v C M₀ σ Kv ω) (i : Fin q) (a b : Fin W) :
    ‖smallField W g E q R v (Kv v) ω i a b‖ ≤
      (2 * W * (√C * M₀) +
          2 * W * (√(9 * C ^ 2 * (W : ℝ) ^ (-8 : ℝ)) * (g ^ 2 * (max C 0 * (W : ℝ) ^ 3)))) +
        (2 * W * (√C * 2) + 2 * W * (√(9 * C ^ 2 * (W : ℝ) ^ (-8 : ℝ)) * 2)) * ‖ω‖ := by
  obtain ⟨-, -, hPKP, -, -, hKC, hcorr, -, hRq, hM⟩ := hpt
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  have hmax : 0 ≤ max C 0 := le_max_right _ _
  have hκ0 : 0 ≤ √C := Real.sqrt_nonneg _
  have hℓ0 : 0 ≤ √(9 * C ^ 2 * (W : ℝ) ^ (-8 : ℝ)) := Real.sqrt_nonneg _
  have hρ0 : 0 ≤ g ^ 2 * (max C 0 * (W : ℝ) ^ 3) :=
    mul_nonneg (sq_nonneg g) (mul_nonneg hmax (by positivity))
  have ht0 : 0 ≤ ‖ω‖ := norm_nonneg _
  have hcg : ‖((g : ℂ) ^ 2)‖ = g ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  -- entry bounds of the five ingredients
  have hK : ∀ a b, ‖Kv v a b‖ ≤ √C := fun a b =>
    (SmallCutField_entry_le_hsSq _ a b).trans (Real.sqrt_le_sqrt hKC)
  have hV : ∀ j a b, ‖gueBlock W q ω j a b‖ ≤ 2 * ‖ω‖ := SmallCutField_gueBlock_entry_le hW ω
  have hMe : ∀ a b, ‖(((g : ℂ) ^ 2) • (P * R * P)) a b‖ ≤ M₀ := fun a b => by
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, hcg]
    exact (mul_le_mul_of_nonneg_left (SmallCutField_entry_le_opNorm _ a b) (sq_nonneg g)).trans hM
  have hLs : hsSq (smallCorr W g E q R v (Kv v) ω) ≤ 9 * C ^ 2 * (W : ℝ) ^ (-8 : ℝ) := by
    have hc8 : 0 ≤ 9 * C ^ 2 * (W : ℝ) ^ (-8 : ℝ) := by positivity
    unfold smallCorr
    by_cases hu : chartProd W g E q R ω (q - 1) *ᵥ v = 0
    · have h0 : ∀ w : Fin W → ℂ, rotCorr (0 : Fin W → ℂ) w = 0 := fun w => by simp [rotCorr]
      have h1 : hsSq (0 : Matrix (Fin W) (Fin W) ℂ) = 0 := by simp [hsSq]
      rw [hu, h0, h1]
      exact hc8
    · have hSu : 0 < ∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2 := by
        obtain ⟨j, hj⟩ := Function.ne_iff.mp hu
        have hj' : 0 < ‖(chartProd W g E q R ω (q - 1) *ᵥ v) j‖ := norm_pos_iff.mpr hj
        exact Finset.sum_pos' (fun i _ => by positivity) ⟨j, Finset.mem_univ _, by positivity⟩
      refine (hsSq_rotCorr_le hu _).trans ?_
      rw [div_le_iff₀ hSu]
      linarith
  have hLe : ∀ a b, ‖smallCorr W g E q R v (Kv v) ω a b‖ ≤ √(9 * C ^ 2 * (W : ℝ) ^ (-8 : ℝ)) :=
    fun a b => (SmallCutField_entry_le_hsSq _ a b).trans (Real.sqrt_le_sqrt hLs)
  have hRe : ∀ a b, ‖(gueBlock W q ω i - ((g : ℂ) ^ 2) • chartR W g E q R ω (q - 1)) a b‖ ≤
      2 * ‖ω‖ + g ^ 2 * (max C 0 * (W : ℝ) ^ 3) := fun a b => by
    rw [Matrix.sub_apply]
    refine (norm_sub_le _ _).trans (add_le_add (hV i a b) ?_)
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, hcg]
    refine mul_le_mul_of_nonneg_left
      (((SmallCutField_entry_le_opNorm _ a b).trans hRq).trans ?_) (sq_nonneg g)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  -- `[K, R_4] = [K, P R_4 P]`
  have hKP : Kv v * P = Kv v := by
    calc Kv v * P = P * Kv v * P * P := by rw [hPKP]
      _ = P * Kv v * (P * P) := by rw [Matrix.mul_assoc (P * Kv v) P P]
      _ = Kv v := by rw [hPP, hPKP]
  have hPK : P * Kv v = Kv v := by
    calc P * Kv v = P * (P * Kv v * P) := by rw [hPKP]
      _ = P * P * Kv v * P := by simp only [Matrix.mul_assoc]
      _ = Kv v := by rw [hPP, hPKP]
  have hKR : Kv v * (P * R * P) = Kv v * R := by
    calc Kv v * (P * R * P) = Kv v * P * (R * P) := by simp only [Matrix.mul_assoc]
      _ = Kv v * (P * R) := by rw [hKP, hPR]
      _ = Kv v * R := by rw [← Matrix.mul_assoc, hKP]
  have hRK : P * R * P * Kv v = R * Kv v := by
    calc P * R * P * Kv v = P * R * (P * Kv v) := by simp only [Matrix.mul_assoc]
      _ = R * P * Kv v := by rw [hPK, hPR]
      _ = R * Kv v := by rw [Matrix.mul_assoc, hPK]
  have hnn : 0 ≤ W * (√C * M₀) ∧ 0 ≤ W * (√C * ‖ω‖) ∧
      0 ≤ W * (√(9 * C ^ 2 * (W : ℝ) ^ (-8 : ℝ)) * (g ^ 2 * (max C 0 * (W : ℝ) ^ 3))) ∧
      0 ≤ W * (√(9 * C ^ 2 * (W : ℝ) ^ (-8 : ℝ)) * ‖ω‖) :=
    ⟨mul_nonneg hW0 (mul_nonneg hκ0 hM₀), mul_nonneg hW0 (mul_nonneg hκ0 ht0),
      mul_nonneg hW0 (mul_nonneg hℓ0 hρ0), mul_nonneg hW0 (mul_nonneg hℓ0 ht0)⟩
  have hc1 := SmallCutField_comm_entry_le hK (hV i) a b
  simp only [smallField]
  split_ifs with h1 h2 h3
  · rw [Matrix.zero_apply, norm_zero]
    linarith [hnn.1, hnn.2.1, hnn.2.2.1, hnn.2.2.2]
  · have e4 : Kv v * (gueBlock W q ω i - ((g : ℂ) ^ 2) • R) -
        (gueBlock W q ω i - ((g : ℂ) ^ 2) • R) * Kv v =
        (Kv v * gueBlock W q ω i - gueBlock W q ω i * Kv v) -
          (Kv v * (((g : ℂ) ^ 2) • (P * R * P)) - (((g : ℂ) ^ 2) • (P * R * P)) * Kv v) := by
      simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, hKR, hRK]
      abel
    rw [e4, Matrix.sub_apply]
    have hc2 := SmallCutField_comm_entry_le hK hMe a b
    refine (norm_sub_le _ _).trans ?_
    linarith [hnn.1, hnn.2.1, hnn.2.2.1, hnn.2.2.2]
  · linarith [hnn.1, hnn.2.1, hnn.2.2.1, hnn.2.2.2]
  · rw [Matrix.sub_apply]
    have hc3 := SmallCutField_comm_entry_le hLe hRe a b
    refine (norm_sub_le _ _).trans ?_
    linarith [hnn.1, hnn.2.1, hnn.2.2.1, hnn.2.2.2]

/-! ### Slices and moments -/

/-- A `C¹` field whose values and derivative grow polynomially keeps these properties on every
slice `z ↦ F (A.piecewise z x)`. -/
private lemma SmallCutField_slice {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : (ι → ℝ) → ι → ℝ} (hF : ContDiff ℝ 1 F) (hg : PolyGrowth F)
    (hg' : PolyGrowth (fderiv ℝ F)) (A : Finset ι) (x : ι → ℝ) :
    ContDiff ℝ 1 (fun z => F (A.piecewise z x)) ∧ PolyGrowth (fun z => F (A.piecewise z x)) ∧
      PolyGrowth (fderiv ℝ (fun z => F (A.piecewise z x))) := by
  let Lp : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.pi fun k => if k ∈ A then ContinuousLinearMap.proj k else 0
  let c : ι → ℝ := fun k => if k ∈ A then 0 else x k
  have hΦ : ∀ z, A.piecewise z x = Lp z + c := fun z => by
    funext k
    by_cases hk : k ∈ A <;> simp [Lp, c, hk]
  have hfun : (fun z => F (A.piecewise z x)) = fun z => F (Lp z + c) :=
    funext fun z => by rw [hΦ]
  have hnorm : ∀ z, 1 + ‖A.piecewise z x‖ ≤ (1 + ‖x‖) * (1 + ‖z‖) := fun z => by
    have h : ‖A.piecewise z x‖ ≤ ‖z‖ + ‖x‖ := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => ?_
      by_cases hk : k ∈ A
      · rw [Finset.piecewise_eq_of_mem _ _ _ hk]
        linarith [norm_le_pi_norm z k, norm_nonneg x]
      · rw [Finset.piecewise_eq_of_notMem _ _ _ hk]
        linarith [norm_le_pi_norm x k, norm_nonneg z]
    nlinarith [norm_nonneg x, norm_nonneg z]
  have hpow : ∀ (k : ℕ) z, (1 + ‖A.piecewise z x‖) ^ k ≤ (1 + ‖x‖) ^ k * (1 + ‖z‖) ^ k :=
    fun k z => by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (hnorm z) k
  have hd : ∀ z, fderiv ℝ (fun z => F (A.piecewise z x)) z =
      (fderiv ℝ F (A.piecewise z x)).comp Lp := fun z => by
    rw [hfun, hΦ]
    have hdF : DifferentiableAt ℝ F (Lp z + c) := hF.differentiable one_ne_zero _
    exact (hdF.hasFDerivAt.comp z (Lp.hasFDerivAt.add_const c)).fderiv
  obtain ⟨C₁, k₁, h₁⟩ := hg
  obtain ⟨C₂, k₂, h₂⟩ := hg'
  refine ⟨?_, ⟨|C₁| * (1 + ‖x‖) ^ k₁, k₁, fun z => ?_⟩,
    ⟨|C₂| * ‖Lp‖ * (1 + ‖x‖) ^ k₂, k₂, fun z => ?_⟩⟩
  · rw [hfun]
    exact hF.comp (Lp.contDiff.add contDiff_const)
  · calc ‖F (A.piecewise z x)‖ ≤ C₁ * (1 + ‖A.piecewise z x‖) ^ k₁ := h₁ _
      _ ≤ |C₁| * (1 + ‖A.piecewise z x‖) ^ k₁ := by gcongr; exact le_abs_self _
      _ ≤ |C₁| * ((1 + ‖x‖) ^ k₁ * (1 + ‖z‖) ^ k₁) := by gcongr; exact hpow k₁ z
      _ = _ := by ring
  · rw [hd]
    have hC₂ : ‖fderiv ℝ F (A.piecewise z x)‖ ≤ |C₂| * ((1 + ‖x‖) ^ k₂ * (1 + ‖z‖) ^ k₂) :=
      calc ‖fderiv ℝ F (A.piecewise z x)‖ ≤ C₂ * (1 + ‖A.piecewise z x‖) ^ k₂ := h₂ _
        _ ≤ |C₂| * (1 + ‖A.piecewise z x‖) ^ k₂ := by gcongr; exact le_abs_self _
        _ ≤ _ := by gcongr; exact hpow k₂ z
    calc ‖(fderiv ℝ F (A.piecewise z x)).comp Lp‖ ≤ ‖fderiv ℝ F (A.piecewise z x)‖ * ‖Lp‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (|C₂| * ((1 + ‖x‖) ^ k₂ * (1 + ‖z‖) ^ k₂)) * ‖Lp‖ := by gcongr
      _ = _ := by ring

private lemma SmallCutField_one_add_abs_pow_le (m : ℕ) (x : ℝ) :
    (1 + |x|) ^ m ≤ 2 ^ m * (1 + |x| ^ m) := by
  have h2 : (0 : ℝ) ≤ 2 ^ m := by positivity
  have hx : (0 : ℝ) ≤ |x| ^ m := by positivity
  rcases le_total |x| 1 with h | h
  · calc (1 + |x|) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
      _ ≤ 2 ^ m * (1 + |x| ^ m) := by nlinarith
  · calc (1 + |x|) ^ m ≤ (2 * |x|) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
      _ = 2 ^ m * |x| ^ m := by rw [mul_pow]
      _ ≤ 2 ^ m * (1 + |x| ^ m) := by nlinarith

/-- Every polynomial moment of `|x|` is finite under the standard Gaussian on `ℝ`. -/
private lemma SmallCutField_integrable_one_add_abs_pow (m : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|) ^ m) (gaussianReal 0 1) := by
  have hm : MemLp id (m : ENNReal) (gaussianReal (0 : ℝ) 1) :=
    memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := 1) m (ENNReal.natCast_ne_top m)
  have hm' : MemLp id (m : ℕ) (gaussianReal (0 : ℝ) 1) := by simpa using hm
  have h1 : Integrable (fun x : ℝ => ‖id x‖ ^ m) (gaussianReal 0 1) := hm'.integrable_norm_pow'
  have h2 : Integrable (fun x : ℝ => (2 : ℝ) ^ m * (1 + |x| ^ m)) (gaussianReal 0 1) :=
    ((integrable_const (1 : ℝ)).add (by simpa using h1)).const_mul _
  refine h2.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (by fun_prop : Continuous fun x : ℝ => (1 + |x|) ^ m).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    exact SmallCutField_one_add_abs_pow_le m x

/-- Polynomial functions of the sup norm are integrable under the standard Gaussian on `ℝ^ι`. -/
private lemma SmallCutField_integrable_poly (ι : Type*) [Fintype ι] (m : ℕ) :
    Integrable (fun x : ι → ℝ => (1 + ‖x‖) ^ m) (stdGauss ι) := by
  have hone : ∀ (x : ι → ℝ) (s : Finset ι), (1 : ℝ) ≤ ∏ l ∈ s, (1 + |x l|) := fun x s =>
    Finset.one_le_prod₀ fun l _ => by linarith [abs_nonneg (x l)]
  have hle : ∀ x : ι → ℝ, 1 + ‖x‖ ≤ ∏ j, (1 + |x j|) := fun x => by
    have : ‖x‖ ≤ (∏ j, (1 + |x j|)) - 1 := by
      refine (pi_norm_le_iff_of_nonneg (by linarith [hone x Finset.univ])).mpr fun j => ?_
      have hj : 1 + |x j| ≤ ∏ l, (1 + |x l|) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
        exact le_mul_of_one_le_right (by positivity) (hone x _)
      rw [Real.norm_eq_abs]
      linarith
    linarith
  have hprod : Integrable (fun x : ι → ℝ => ∏ j, (1 + |x j|) ^ m) (stdGauss ι) :=
    Integrable.fintype_prod (f := fun _ (t : ℝ) => (1 + |t|) ^ m)
      (fun _ => SmallCutField_integrable_one_add_abs_pow m)
  refine hprod.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (by fun_prop : Continuous fun x : ι → ℝ => (1 + ‖x‖) ^ m).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity), Finset.prod_pow]
    exact pow_le_pow_left₀ (by positivity) (hle x) m

/-- Linear growth of the field `χ X` of Lemma 8.12 [up:lem:small-contraction]. -/
theorem norm_smallCut_smul_le {W q : ℕ} {g E C σ M₀ : ℝ} (hW : 1 ≤ W) (hq : 7 ≤ q) (hg : 0 < g)
    (hg1 : g ≤ 1) (hM₀ : 0 ≤ M₀) {x : IsoFlag W}
    {Pf : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ} {pre : Ω W q → ℝ}
    {Rf : Ω W q → Matrix (Fin W) (Fin W) ℂ} {vf : Ω W q → Fin W → ℂ}
    {Kh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ}
    {χh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → ℝ}
    (hG : ChosenGenerator W q g E x Pf C σ M₀ pre Rf vf Kh χh) :
    ∃ a b : ℝ, ∀ ω : Ω W q,
      ‖smallCut pre Rf vf χh ω • smallVec W g E q Rf vf Kh ω‖ ≤ a + b * ‖ω‖ := by
  have hcut := (smallCut_basic hG).2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, hfam, hpt, -⟩ := hG
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  have hb0 := SmallCutField_hb_nonneg W
  have hA0 : 0 ≤ 2 * W * (√C * M₀) +
      2 * W * (√(9 * C ^ 2 * (W : ℝ) ^ (-8 : ℝ)) * (g ^ 2 * (max C 0 * (W : ℝ) ^ 3))) :=
    add_nonneg (mul_nonneg (by positivity) (mul_nonneg (Real.sqrt_nonneg _) hM₀))
      (mul_nonneg (by positivity) (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (sq_nonneg g) (mul_nonneg (le_max_right _ _) (by positivity)))))
  have hB0 : 0 ≤ 2 * W * (√C * 2) + 2 * W * (√(9 * C ^ 2 * (W : ℝ) ^ (-8 : ℝ)) * 2) := by
    positivity
  refine ⟨√W * (W * (W * (SmallCutField_hb W * (2 * W * (√C * M₀) +
      2 * W * (√(9 * C ^ 2 * (W : ℝ) ^ (-8 : ℝ)) * (g ^ 2 * (max C 0 * (W : ℝ) ^ 3))))))),
    √W * (W * (W * (SmallCutField_hb W *
      (2 * W * (√C * 2) + 2 * W * (√(9 * C ^ 2 * (W : ℝ) ^ (-8 : ℝ)) * 2))))), fun ω => ?_⟩
  have ha : 0 ≤ √W * (W * (W * (SmallCutField_hb W * (2 * W * (√C * M₀) +
      2 * W * (√(9 * C ^ 2 * (W : ℝ) ^ (-8 : ℝ)) * (g ^ 2 * (max C 0 * (W : ℝ) ^ 3))))))) :=
    mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hW0 (mul_nonneg hW0 (mul_nonneg hb0 hA0)))
  have hb : 0 ≤ √W * (W * (W * (SmallCutField_hb W *
      (2 * W * (√C * 2) + 2 * W * (√(9 * C ^ 2 * (W : ℝ) ^ (-8 : ℝ)) * 2))))) :=
    mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hW0 (mul_nonneg hW0 (mul_nonneg hb0 hB0)))
  by_cases hχ : smallCut pre Rf vf χh ω = 0
  · rw [hχ, zero_smul, norm_zero]
    exact add_nonneg ha (mul_nonneg hb (norm_nonneg _))
  have hpre0 : pre ω ≠ 0 := left_ne_zero_of_mul hχ
  obtain ⟨-, hPP, hPR, -⟩ := hfam ω hpre0
  have hX := SmallCutField_field_le hW hM₀ hPP hPR (hpt ω hχ)
  have hY := SmallCutField_hermCoord_le (add_nonneg hA0 (mul_nonneg hB0 (norm_nonneg ω))) hX
  have hχ1 : ‖smallCut pre Rf vf χh ω‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [(hcut ω).1], (hcut ω).2⟩
  rw [norm_smul]
  refine (mul_le_mul_of_nonneg_right hχ1 (norm_nonneg _)).trans ?_
  rw [one_mul]
  refine hY.trans (le_of_eq ?_)
  ring

/-- Gaussian integration by parts (8.33) [up:eq:gaussian-divergence] for the field of Lemma 8.12
[up:lem:small-contraction], conditionally on the preparation blocks (Lemma 8.11
[up:lem:angular]). -/
theorem ibpAdmissible_smallCut {W q : ℕ} {g E C σ M₀ : ℝ} (hC : 0 < C) (hW : 1 ≤ W) (hq : 7 ≤ q)
    (hg : 0 < g) (hg1 : g ≤ 1) (hσ : 0 ≤ σ) (hM₀ : 0 ≤ M₀) {x : IsoFlag W}
    {Pf : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ} {pre : Ω W q → ℝ}
    {Rf : Ω W q → Matrix (Fin W) (Fin W) ℂ} {vf : Ω W q → Fin W → ℂ}
    {Kh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ}
    {χh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → ℝ}
    (hG : ChosenGenerator W q g E x Pf C σ M₀ pre Rf vf Kh χh) :
    IBPAdmissible (fun η => smallCut pre Rf vf χh η • smallVec W g E q Rf vf Kh η) := by
  obtain ⟨Cs, c, -, -, hbound⟩ := lintegral_gaussDiv_smallCut_le C hC
  have hL2 := hbound W q g E σ M₀ x Pf pre Rf vf Kh χh hW hq hg hg1 hσ hM₀ hG
  obtain ⟨a, b, hab⟩ := norm_smallCut_smul_le hW hq hg hg1 hM₀ hG
  have hYm := (measurable_smallCut_field hG).1
  obtain ⟨hpre, -, -, -, hpre5, hprep, -, -, -, hfam, -⟩ := id hG
  set A : Finset (Fin q × Fin W × Fin W) := Finset.univ.filter fun k => 4 ≤ (k.1 : ℕ) with hAdef
  have hdiv : Measurable
      (gaussDiv (fun η => smallCut pre Rf vf χh η • smallVec W g E q Rf vf Kh η)) := by
    have he : gaussDiv (fun η => smallCut pre Rf vf χh η • smallVec W g E q Rf vf Kh η) =
        fun ω => pre ω *
          gaussDiv (smallScoreField W g E q (Rf ω) (vf ω) (Kh (Rf ω)) (χh (Rf ω))) ω :=
      funext (gaussDiv_smallCut_eq hG)
    rw [he]
    exact (measurable_smallCut_field hG).2.comp (measurable_id.prodMk measurable_id)
  refine ibpAdmissible_of_frozen A ?_ ?_ hYm hdiv ?_ ?_
  · -- the components on the preparation blocks vanish
    intro y k hk
    have hk4 : (k.1 : ℕ) < 4 := by
      simpa [hAdef] using hk
    simp [smallVec, hermCoord, smallField, hk4]
  · -- the slices are `C¹` with polynomial growth
    refine Filter.Eventually.of_forall fun y => ?_
    have hS : (fun z => smallCut pre Rf vf χh (A.piecewise z y) •
        smallVec W g E q Rf vf Kh (A.piecewise z y)) = fun z => pre y •
          smallScoreField W g E q (Rf y) (vf y) (Kh (Rf y)) (χh (Rf y)) (A.piecewise z y) := by
      funext z
      have hblk : ∀ i : Fin q, (i : ℕ) < 4 →
          gueBlock W q (A.piecewise z y) i = gueBlock W q y i := fun i hi => by
        have hyx : ∀ α β, A.piecewise z y (i, α, β) = y (i, α, β) := fun α β =>
          Finset.piecewise_eq_of_notMem _ _ _ (by
            simp only [hAdef, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
            exact hi)
        ext α β
        simp only [gueBlock, Matrix.of_apply, hyx]
      obtain ⟨h1, h2, h3⟩ := hpre5 _ _ hblk
      simp only [smallCut, smallVec, smallScoreField, h1, h2, h3, mul_smul]
    rw [hS]
    rcases hpre y with hp | hp
    · simp only [hp, zero_smul]
      refine ⟨contDiff_const, ⟨0, 0, fun _ => by simp⟩, ⟨0, 0, fun _ => by simp⟩⟩
    · simp only [hp, one_smul]
      have hp0 : pre y ≠ 0 := by rw [hp]; exact one_ne_zero
      have hF := (hfam y hp0).2.2.2
      have hv : vf y ≠ 0 := (hprep y hp0).2.1
      obtain ⟨hg₁, hg₂⟩ := polyGrowth_smallScoreField hq hF hv
      exact SmallCutField_slice (contDiff_smallScoreField hF hv) hg₁ hg₂ A y
  · -- `‖χ Y‖ (1 + ‖x‖)^k` is integrable
    intro k
    refine ((SmallCutField_integrable_poly _ (k + 1)).const_mul (|a| + |b|)).mono' ?_
      (Filter.Eventually.of_forall fun y => ?_)
    · exact (hYm.norm.mul
        (by fun_prop : Continuous fun y : Ω W q => (1 + ‖y‖) ^ k).measurable).aestronglyMeasurable
    · have hy0 : 0 ≤ ‖y‖ := norm_nonneg y
      have h1 : ‖smallCut pre Rf vf χh y • smallVec W g E q Rf vf Kh y‖ ≤
          (|a| + |b|) * (1 + ‖y‖) := by
        have := hab y
        nlinarith [mul_le_mul_of_nonneg_right (le_abs_self b) hy0,
          mul_nonneg (abs_nonneg a) hy0, abs_nonneg b, le_abs_self a]
      rw [Real.norm_of_nonneg (by positivity), pow_succ]
      calc ‖smallCut pre Rf vf χh y • smallVec W g E q Rf vf Kh y‖ * (1 + ‖y‖) ^ k
          ≤ (|a| + |b|) * (1 + ‖y‖) * (1 + ‖y‖) ^ k := by gcongr
        _ = _ := by ring
  · -- `δ_G (χ Y)` is square integrable, hence integrable
    change Integrable _ (μ W q)
    have hsq : Integrable (fun ω =>
        gaussDiv (fun η => smallCut pre Rf vf χh η • smallVec W g E q Rf vf Kh η) ω ^ 2)
        (μ W q) := by
      refine ⟨(hdiv.pow_const 2).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      simp only [enorm_pow]
      exact lt_of_le_of_lt hL2 ENNReal.ofReal_lt_top
    exact ((memLp_two_iff_integrable_sq hdiv.aestronglyMeasurable).mpr hsq).integrable one_le_two

/-- The hypotheses of Lemma 8.11 [up:lem:angular] for the cutoff and the field of Lemma 8.12
[up:lem:small-contraction] built from the data of Lemma 9.3 [su:lem:chosen-generator], with the
bound of the Gaussian divergence in terms of `C`, `σ` and `M₀` in place of `C 𝔟`; the constants
`C_s, c` depend only on `C`. -/
theorem angularFieldAt_smallCut (C : ℝ) (hC : 0 < C) :
    ∃ Cs c : ℝ, 0 < Cs ∧ 0 < c ∧ ∀ (W q : ℕ) (g E σ M₀ : ℝ) (x : IsoFlag W)
      (Pf : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ) (pre : Ω W q → ℝ)
      (Rf : Ω W q → Matrix (Fin W) (Fin W) ℂ) (vf : Ω W q → Fin W → ℂ)
      (Kh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ)
      (χh : Matrix (Fin W) (Fin W) ℂ → Ω W q → (Fin W → ℂ) → ℝ),
      1 ≤ W → 7 ≤ q → 0 < g → g ≤ 1 → 0 ≤ σ → 0 ≤ M₀ →
      ChosenGenerator W q g E x Pf C σ M₀ pre Rf vf Kh χh →
      AngularFieldAt W g E q (smallDivBound Cs c C W g σ M₀) 1 x (smallCut pre Rf vf χh)
        (smallVec W g E q Rf vf Kh) := by
  obtain ⟨Cs, c, hCs, hc, hbound⟩ := lintegral_gaussDiv_smallCut_le C hC
  refine ⟨Cs, c, hCs, hc, fun W q g E σ M₀ x Pf pre Rf vf Kh χh hW hq hg hg1 hσ hM₀ hG => ?_⟩
  obtain ⟨hm, h01, hmean⟩ := smallCut_basic hG
  refine ⟨hm, h01, fun ω hω => smallCut_geom hg hg1 hq hG ω hω,
    ibpAdmissible_smallCut hC hW hq hg hg1 hσ hM₀ hG, hmean, ?_⟩
  rw [one_mul]
  exact hbound W q g E σ M₀ x Pf pre Rf vf Kh χh hW hq hg hg1 hσ hM₀ hG

end LSBA
