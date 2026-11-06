import LSBA.Upper.OperatorSemigroup
import LSBA.Transfer.Cofactor

/-!
# From the operator to the frame moments

The moment bound `𝔼‖T_i‖^{1/2} ≤ W^{B/2+1}` for one transfer matrix (8.9) [eq:c-transfer]; and,
through the second line of (8.20) [cc:eq:iterate] via (8.23) [eq:c-inverse-cocycle] and (F.4)
[cc:eq:inverse] with s = ½, the moment of `D_n⁻¹` at every length `n`, at one point, from (8.21)
[up:eq:power-input], with the incomplete batch paid by independence (the proof of Lemma 8.6
[up:lem:operator-reduction] needs multiples of the batch length, the second line of (8.20)
[cc:eq:iterate]; constants explicit).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Norm bounds for one transfer matrix -/

/-- `‖1‖ ≤ 1` for the operator norm. -/
private theorem reduction_norm_one_le {n : Type*} [Fintype n] [DecidableEq n] :
    ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by simp

/-- A unitary matrix has operator norm at most `1`. -/
private theorem reduction_norm_unitary_le {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) : ‖U‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self U
  rw [← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp hU] at h
  have h1 := reduction_norm_one_le (n := n)
  nlinarith [norm_nonneg U]

/-- `‖[[1, 0], [0, 0]] ⊗ V‖ ≤ ‖V‖`. -/
private theorem reduction_norm_kron_le {W : ℕ} (V : Matrix (Fin W) (Fin W) ℂ) :
    ‖(!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V‖ ≤ ‖V‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg V) fun x => ?_
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  set y : EuclideanSpace ℂ (Fin W) := WithLp.toLp 2 (fun β => x.ofLp (0, β)) with hy
  have hVy : ‖Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) V y‖ ≤ ‖V‖ * ‖y‖ := by
    have := (Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) V).le_opNorm y
    rwa [Matrix.l2_opNorm_toEuclideanCLM] at this
  have hyx : ‖y‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
      Fin.sum_univ_two]
    have : 0 ≤ ∑ β, ‖x.ofLp (1, β)‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    simp only [hy]
    linarith
  have key : ∀ (i : Fin 2) (β : Fin W),
      (((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V) *ᵥ x.ofLp) (i, β) =
        if i = 0 then (V *ᵥ y.ofLp) β else 0 := by
    intro i β
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, hy]
  rw [EuclideanSpace.norm_sq_eq, Matrix.ofLp_toEuclideanCLM]
  simp only [key, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, Finset.sum_const_zero, add_zero]
  have h1 : ∑ β, ‖(V *ᵥ y.ofLp) β‖ ^ 2 =
      ‖Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) V y‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Matrix.ofLp_toEuclideanCLM]
  rw [h1]
  calc _ ≤ (‖V‖ * ‖y‖) ^ 2 := by gcongr
    _ = ‖V‖ ^ 2 * ‖y‖ ^ 2 := by ring
    _ ≤ ‖V‖ ^ 2 * ‖x‖ ^ 2 := by gcongr
    _ = _ := by ring

/-- `‖T(z)‖ ≤ |z| + 1` for the free transfer matrix `[[z, -1], [1, 0]] ⊗ I`. -/
private theorem reduction_norm_transferFree_le (W : ℕ) (z : ℂ) :
    ‖transferFree W z‖ ≤ ‖z‖ + 1 := by
  have h1 : transferFree W z =
      z • ((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) +
        (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) := by
    unfold transferFree
    rw [← Matrix.smul_kronecker, ← Matrix.add_kronecker]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hR : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) ∈
      Matrix.unitaryGroup (Fin 2 × Fin W) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_one,
      Matrix.mul_one]
    have : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * !![0, -1; 1, 0] = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [this, Matrix.one_kronecker_one]
  rw [h1]
  refine (norm_add_le _ _).trans (add_le_add ?_ (reduction_norm_unitary_le hR))
  rw [norm_smul]
  have h2 := (reduction_norm_kron_le (1 : Matrix (Fin W) (Fin W) ℂ)).trans reduction_norm_one_le
  calc ‖z‖ * ‖(!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)‖
      ≤ ‖z‖ * 1 := by gcongr
    _ = ‖z‖ := mul_one _

/-- `‖T_i‖ ≤ |z| + 1 + ‖V‖ / |g|` for `T_i = [[z, -1], [1, 0]] ⊗ I - (1/g) [[1, 0], [0, 0]] ⊗ V`. -/
private theorem reduction_norm_transferMat_le {W : ℕ} (g z : ℝ) (V : Matrix (Fin W) (Fin W) ℂ) :
    ‖transferMat g (z : ℂ) V‖ ≤ |z| + 1 + |g|⁻¹ * ‖V‖ := by
  unfold transferMat
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  have h1 := reduction_norm_transferFree_le W (z : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs] at h1
  have h2 := reduction_norm_kron_le V
  have h3 : |g|⁻¹ * ‖(!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V‖ ≤ |g|⁻¹ * ‖V‖ := by
    gcongr
  linarith

/-! ### The reduction to the operator -/

/-- `‖a‖ₑ^s = ofReal (‖a‖^s)` for `0 ≤ s`. -/
private theorem reduction_enorm_rpow {E : Type*} [SeminormedAddGroup E] (a : E) {s : ℝ}
    (hs : 0 ≤ s) : ‖a‖ₑ ^ s = ENNReal.ofReal (‖a‖ ^ s) := by
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hs]

/-- (F.4) [cc:eq:inverse] at `s = 1/2` for the product of `n` blocks, in the form of the sum over
`j` of `e^{-c(S* T_n ⋯ T_1 S; x_j)/2}`. -/
private theorem reduction_frameD_inv_le {W : ℕ} (g E : ℝ) (n : ℕ) (ω : Ω W n)
    {Φ : Matrix (Fin 2 × Fin W) (Fin W) ℂ} (hΦ : IsBoundaryFrame Φ) :
    ‖(frameD (transferProd g ((max 1 g * E / g : ℝ) : ℂ)
        (fun i => if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0) n) Φ)⁻¹‖ ^ (1 / 2 : ℝ) ≤
      ∑ j, Real.exp (-(1 / 2 : ℝ) * volCocycle (batchMat W g E n ω)
        ⟨omitPair Φ j, omitPair_mem_isoFlags hΦ j⟩) := by
  have hV : ∀ i : ℕ, ((fun i => if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0) i).IsHermitian := by
    intro i
    by_cases h : i < n
    · simp only [h, dite_true]
      exact gueBlock_isHermitian W n ω ⟨i, h⟩
    · simp only [h, dite_false]
      exact Matrix.isHermitian_zero
  have hM := transferProd_conjTranspose_mul_phJ g (max 1 g * E / g)
    (fun i => if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0) hV n
  exact norm_frameD_inv_rpow_le hM hΦ (s := 1 / 2) (by norm_num) (by norm_num)

/-- `∫ ofReal (e^{-c(batchMat (qk); x)/2}) = (P_{1/2}^k 1)(x)` (first line of (8.20)
[cc:eq:iterate]), as a lower integral. -/
private theorem reduction_lintegral_exp_cocycle (W : ℕ) (g E : ℝ) (q k : ℕ) (x : IsoFlag W) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ) * volCocycle (batchMat W g E (q * k) ω) x))
        ∂(μ W (q * k)) =
      ENNReal.ofReal ((halfOp W g E q)^[k] (fun _ => 1) x) := by
  have hf : ∀ ω : Ω W (q * k), Real.exp (-(1 / 2 : ℝ) * volCocycle (batchMat W g E (q * k) ω) x) =
      Real.exp (-volCocycle (batchMat W g E (q * k) ω) x / 2) := fun ω => by
    congr 1
    ring
  simp only [hf]
  have hint : Integrable (fun ω => Real.exp (-volCocycle (batchMat W g E (q * k) ω) x / 2))
      (μ W (q * k)) := by
    simpa using integrable_halfOp g E (q * k) (h := fun _ => (1 : ℝ))
      ⟨measurable_const, 1, by simp⟩ x
  rw [iterate_halfOp_one, ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)]

/-- Measurability of `ω ↦ ofReal (e^{-c(batchMat n ω; x)/2})`. -/
private theorem reduction_measurable_exp_cocycle (W : ℕ) (g E : ℝ) (n : ℕ) (x : IsoFlag W) :
    Measurable fun ω : Ω W n =>
      ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ) * volCocycle (batchMat W g E n ω) x)) := by
  have hp : Measurable fun ω : Ω W n => (batchMat W g E n ω, x) :=
    (measurable_batchMat W g E n).prodMk measurable_const
  have h1 := (measurable_volCocycle W).comp hp
  have h2 : Measurable fun ω : Ω W n =>
      Real.exp (-(1 / 2 : ℝ) * volCocycle (batchMat W g E n ω) x) :=
    Real.measurable_exp.comp (h1.const_mul (-(1 / 2 : ℝ)))
  exact h2.ennreal_ofReal

/-- One transfer matrix of (8.9) [eq:c-transfer]: `𝔼‖T_i‖^{1/2} ≤ W^{B/2+1}` for
`W^{-B} ≤ g ≤ W^B`, `|E| ≤ E₀`, `W ≥ (4(E₀+1))^{2/3}` (proof of Lemma 8.6
[up:lem:operator-reduction]). -/
theorem lintegral_norm_transferMat_le {B E₀ : ℝ} (hB : 0 < B) (hE₀ : 0 < E₀) {W L : ℕ}
    (hW : (4 * (E₀ + 1)) ^ (2 / 3 : ℝ) ≤ W) {g E : ℝ} (hg1 : (W : ℝ) ^ (-B) ≤ g)
    (hg2 : g ≤ (W : ℝ) ^ B) (hE : |E| ≤ E₀) (a : Fin L) :
    ∫⁻ ω, ‖transferMat g ((max 1 g * E / g : ℝ) : ℂ) (gueBlock W L ω a)‖ₑ ^ (1 / 2 : ℝ) ∂(μ W L) ≤
      ENNReal.ofReal ((W : ℝ) ^ (B / 2 + 1)) := by
  have h4 : (1 : ℝ) ≤ 4 * (E₀ + 1) := by linarith
  have hW1 : (1 : ℝ) ≤ W := le_trans (Real.one_le_rpow h4 (by norm_num)) hW
  have hw0 : (0 : ℝ) < W := by linarith
  set s : ℝ := (W : ℝ) ^ B with hs
  have hs1 : 1 ≤ s := Real.one_le_rpow hW1 hB.le
  have hspos : 0 < s := by linarith
  have hsg : s⁻¹ ≤ g := by rwa [hs, ← Real.rpow_neg hw0.le]
  have hgpos : 0 < g := lt_of_lt_of_le (inv_pos.mpr hspos) hsg
  have hginv : g⁻¹ ≤ s := by
    calc g⁻¹ ≤ (s⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr hspos) hsg
      _ = s := inv_inv s
  set z : ℝ := max 1 g * E / g with hz
  have hmax : max 1 g / g ≤ s := by
    rcases le_total 1 g with h | h
    · rw [max_eq_right h, div_self hgpos.ne']
      exact hs1
    · rw [max_eq_left h, one_div]
      exact hginv
  have hzabs : |z| ≤ E₀ * s := by
    have : |z| = max 1 g / g * |E| := by
      rw [hz, mul_div_right_comm, abs_mul, abs_of_nonneg (div_nonneg
        (le_trans zero_le_one (le_max_left _ _)) hgpos.le)]
    rw [this]
    calc max 1 g / g * |E| ≤ s * E₀ := mul_le_mul hmax hE (abs_nonneg _) hspos.le
      _ = E₀ * s := mul_comm _ _
  -- the pointwise bound `‖T‖ ≤ (E₀ + 1) W^B (1 + ‖V‖)`
  set K : ℝ := (E₀ + 1) * s with hK
  have hnorm : ∀ V : Matrix (Fin W) (Fin W) ℂ,
      ‖transferMat g (z : ℂ) V‖ ≤ K * (1 + ‖V‖) := by
    intro V
    refine (reduction_norm_transferMat_le g z V).trans ?_
    rw [abs_of_pos hgpos]
    have hV := norm_nonneg V
    have h1 : g⁻¹ * ‖V‖ ≤ s * ‖V‖ := by gcongr
    have h2 : 0 ≤ E₀ * s * ‖V‖ := by positivity
    rw [hK]
    nlinarith
  have hroot : ∀ V : Matrix (Fin W) (Fin W) ℂ,
      ‖transferMat g (z : ℂ) V‖ ^ (1 / 2 : ℝ) ≤ K ^ (1 / 2 : ℝ) * (1 + ‖V‖ ^ (1 / 2 : ℝ)) := by
    intro V
    have hKpos : 0 ≤ K := by positivity
    calc ‖transferMat g (z : ℂ) V‖ ^ (1 / 2 : ℝ) ≤ (K * (1 + ‖V‖)) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (norm_nonneg _) (hnorm V) (by norm_num)
      _ = K ^ (1 / 2 : ℝ) * (1 + ‖V‖) ^ (1 / 2 : ℝ) :=
          Real.mul_rpow hKpos (by positivity)
      _ ≤ K ^ (1 / 2 : ℝ) * (1 + ‖V‖ ^ (1 / 2 : ℝ)) := by
          gcongr
          have := Real.rpow_add_le_add_rpow (zero_le_one' ℝ) (norm_nonneg V)
            (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
          simpa using this
  -- integrate
  have hpt : ∀ ω : Ω W L,
      ‖transferMat g (z : ℂ) (gueBlock W L ω a)‖ₑ ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (K ^ (1 / 2 : ℝ)) * (1 + ‖gueBlock W L ω a‖ₑ ^ (1 / 2 : ℝ)) := by
    intro ω
    rw [← ofReal_norm, ← ofReal_norm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add zero_le_one (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (hroot _)
  have hmom := lintegral_norm_gueBlock_rpow_le W L a (s := 1 / 2) (by norm_num) (by norm_num)
  calc ∫⁻ ω, ‖transferMat g (z : ℂ) (gueBlock W L ω a)‖ₑ ^ (1 / 2 : ℝ) ∂(μ W L)
      ≤ ∫⁻ ω, ENNReal.ofReal (K ^ (1 / 2 : ℝ)) *
          (1 + ‖gueBlock W L ω a‖ₑ ^ (1 / 2 : ℝ)) ∂(μ W L) := lintegral_mono hpt
    _ = ENNReal.ofReal (K ^ (1 / 2 : ℝ)) *
          (1 + ∫⁻ ω, ‖gueBlock W L ω a‖ₑ ^ (1 / 2 : ℝ) ∂(μ W L)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (K ^ (1 / 2 : ℝ)) *
          (1 + ENNReal.ofReal ((W : ℝ) ^ ((1 / 2 : ℝ) / 2))) := by gcongr
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (B / 2 + 1)) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        -- `a = (E₀ + 1)^{1/2}`, `u = W^{1/4}`, `u⁴ = W`, `a (1 + u) ≤ u⁴`
        set u : ℝ := (W : ℝ) ^ (1 / 4 : ℝ) with hu
        have hu4 : u ^ 4 = W := by
          rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hw0.le]
          norm_num
        have hu1 : 1 ≤ u := Real.one_le_rpow hW1 (by norm_num)
        have hupos : 0 < u := by linarith
        have hexp : (W : ℝ) ^ ((1 / 2 : ℝ) / 2) = u := by
          rw [hu]; norm_num
        rw [hexp]
        set a : ℝ := (E₀ + 1) ^ (1 / 2 : ℝ) with ha
        have ha2 : a ^ 2 = E₀ + 1 := by
          rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
          norm_num
        have hapos : 0 ≤ a := Real.rpow_nonneg (by linarith) _
        -- `4 (E₀ + 1) ≤ u⁶`
        have h6 : 4 * (E₀ + 1) ≤ u ^ 6 := by
          set t : ℝ := (4 * (E₀ + 1)) ^ (2 / 3 : ℝ) with ht
          have ht3 : t ^ 3 = (4 * (E₀ + 1)) ^ 2 := by
            rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
            norm_num
          have htw : t ^ 3 ≤ (u ^ 6) ^ 2 := by
            calc t ^ 3 ≤ (W : ℝ) ^ 3 := by gcongr
              _ = (u ^ 6) ^ 2 := by rw [← hu4]; ring
          have := (pow_le_pow_iff_left₀ (by linarith) (by positivity) (two_ne_zero)).mp
            (ht3 ▸ htw)
          exact this
        have h2a : 2 * a ≤ u ^ 3 := by
          refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) (two_ne_zero)).mp ?_
          calc (2 * a) ^ 2 = 4 * (E₀ + 1) := by rw [mul_pow, ha2]; norm_num
            _ ≤ u ^ 6 := h6
            _ = (u ^ 3) ^ 2 := by ring
        have hWu : a * (1 + u) ≤ W := by
          rw [← hu4]
          nlinarith
        have hKh : K ^ (1 / 2 : ℝ) = a * (W : ℝ) ^ (B / 2) := by
          rw [hK, hs, Real.mul_rpow (by linarith) (by positivity), ha, ← Real.rpow_mul hw0.le]
          congr 2
          ring
        rw [hKh, Real.rpow_add hw0, Real.rpow_one]
        calc a * (W : ℝ) ^ (B / 2) * (1 + u) = ((W : ℝ) ^ (B / 2)) * (a * (1 + u)) := by ring
          _ ≤ (W : ℝ) ^ (B / 2) * W := by gcongr

/-- The batches of the first `p` and the last `r` blocks are independent: the lower integral of a
product of a function of the first `p` and a function of the last `r` blocks factorizes. -/
private theorem reduction_lintegral_blockAppend {W : ℕ} (p r : ℕ) {F : Ω W p → ℝ≥0∞}
    {G : Ω W r → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G) :
    ∫⁻ ω, F (blockAppend W p r ω).1 * G (blockAppend W p r ω).2 ∂(μ W (p + r)) =
      (∫⁻ ω, F ω ∂(μ W p)) * ∫⁻ ω, G ω ∂(μ W r) := by
  have hmp := measurePreserving_blockAppend W p r
  have hm : Measurable fun x : Ω W p × Ω W r => F x.1 * G x.2 :=
    (hF.comp measurable_fst).mul (hG.comp measurable_snd)
  have h := hmp.lintegral_comp hm
  rw [h]
  exact lintegral_prod_mul hF.aemeasurable hG.aemeasurable

/-- `‖S* P S‖ ≤ ‖P‖` for the unitary `S = S_0`: the batch is bounded by the product of its
transfer matrices. -/
private theorem reduction_norm_batchMat_le {W : ℕ} (g E : ℝ) (n : ℕ) (ω : Ω W n) :
    ‖batchMat W g E n ω‖ ≤ ‖transferProd g ((max 1 g * E / g : ℝ) : ℂ)
      (fun i => if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0) n‖ := by
  have hS := reduction_norm_unitary_le (freeConj_zero_mem_unitaryGroup W)
  have hS' : ‖(freeConj W 0)ᴴ‖ ≤ 1 := by
    have := reduction_norm_unitary_le (Unitary.star_mem (freeConj_zero_mem_unitaryGroup W))
    rwa [Matrix.star_eq_conjTranspose] at this
  unfold batchMat
  calc _ ≤ ‖(freeConj W 0)ᴴ * transferProd g ((max 1 g * E / g : ℝ) : ℂ)
        (fun i => if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0) n‖ * ‖freeConj W 0‖ :=
        norm_mul_le _ _
    _ ≤ ‖(freeConj W 0)ᴴ * transferProd g ((max 1 g * E / g : ℝ) : ℂ)
        (fun i => if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0) n‖ * 1 := by gcongr
    _ ≤ ‖(freeConj W 0)ᴴ‖ * ‖transferProd g ((max 1 g * E / g : ℝ) : ℂ)
        (fun i => if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0) n‖ := by
        rw [mul_one]
        exact norm_mul_le _ _
    _ ≤ 1 * ‖transferProd g ((max 1 g * E / g : ℝ) : ℂ)
        (fun i => if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0) n‖ := by gcongr
    _ = _ := one_mul _

/-- The product of `r` blocks: `𝔼‖S* T_r ⋯ T_1 S‖^{1/2} ≤ W^{(B/2+1) r}` (independence of the
blocks and the bound for one transfer matrix). -/
private theorem reduction_lintegral_norm_batchMat_le {B E₀ : ℝ} (hB : 0 < B) (hE₀ : 0 < E₀)
    {W : ℕ} (hW : (4 * (E₀ + 1)) ^ (2 / 3 : ℝ) ≤ W) {g E : ℝ} (hg1 : (W : ℝ) ^ (-B) ≤ g)
    (hg2 : g ≤ (W : ℝ) ^ B) (hE : |E| ≤ E₀) (r : ℕ) :
    ∫⁻ ω, ‖batchMat W g E r ω‖ₑ ^ (1 / 2 : ℝ) ∂(μ W r) ≤
      ENNReal.ofReal ((W : ℝ) ^ ((B / 2 + 1) * r)) := by
  have h4 : (1 : ℝ) ≤ 4 * (E₀ + 1) := by linarith
  have hW1 : (1 : ℝ) ≤ W := le_trans (Real.one_le_rpow h4 (by norm_num)) hW
  have hw0 : (0 : ℝ) < W := by linarith
  induction r with
  | zero =>
    have h1 : ∀ ω : Ω W 0, ‖batchMat W g E 0 ω‖ₑ ^ (1 / 2 : ℝ) ≤ 1 := by
      intro ω
      rw [reduction_enorm_rpow _ (by norm_num), ← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have h2 : ‖batchMat W g E 0 ω‖ ≤ 1 :=
        (reduction_norm_batchMat_le g E 0 ω).trans (by simpa [transferProd] using
          (reduction_norm_one_le (n := Fin 2 × Fin W)))
      calc ‖batchMat W g E 0 ω‖ ^ (1 / 2 : ℝ) ≤ 1 ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (norm_nonneg _) h2 (by norm_num)
        _ = 1 := Real.one_rpow _
    calc ∫⁻ ω, ‖batchMat W g E 0 ω‖ₑ ^ (1 / 2 : ℝ) ∂(μ W 0) ≤ ∫⁻ _ω, 1 ∂(μ W 0) :=
          lintegral_mono h1
      _ = ENNReal.ofReal ((W : ℝ) ^ ((B / 2 + 1) * ((0 : ℕ) : ℝ))) := by
          simp
  | succ r ih =>
    have hone : ∀ ω : Ω W 1, ‖batchMat W g E 1 ω‖ₑ ^ (1 / 2 : ℝ) ≤
        ‖transferMat g ((max 1 g * E / g : ℝ) : ℂ) (gueBlock W 1 ω 0)‖ₑ ^ (1 / 2 : ℝ) := by
      intro ω
      rw [reduction_enorm_rpow _ (by norm_num), reduction_enorm_rpow _ (by norm_num)]
      refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) ?_ (by norm_num))
      refine (reduction_norm_batchMat_le g E 1 ω).trans ?_
      simp [transferProd]
    have hpt : ∀ ω : Ω W (r + 1), ‖batchMat W g E (r + 1) ω‖ₑ ^ (1 / 2 : ℝ) ≤
        ‖batchMat W g E r (blockAppend W r 1 ω).1‖ₑ ^ (1 / 2 : ℝ) *
          ‖batchMat W g E 1 (blockAppend W r 1 ω).2‖ₑ ^ (1 / 2 : ℝ) := by
      intro ω
      rw [batchMat_add, reduction_enorm_rpow _ (by norm_num),
        reduction_enorm_rpow _ (by norm_num), reduction_enorm_rpow _ (by norm_num),
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [mul_comm (‖batchMat W g E r _‖ ^ (1 / 2 : ℝ)), ← Real.mul_rpow (norm_nonneg _)
        (norm_nonneg _)]
      exact Real.rpow_le_rpow (norm_nonneg _) (norm_mul_le _ _) (by norm_num)
    have hone' : ∫⁻ ω, ‖batchMat W g E 1 ω‖ₑ ^ (1 / 2 : ℝ) ∂(μ W 1) ≤
        ENNReal.ofReal ((W : ℝ) ^ (B / 2 + 1)) :=
      (lintegral_mono hone).trans (lintegral_norm_transferMat_le hB hE₀ hW hg1 hg2 hE 0)
    have hmF : Measurable fun ω : Ω W r => ‖batchMat W g E r ω‖ₑ ^ (1 / 2 : ℝ) :=
      (measurable_batchMat W g E r).enorm.pow_const _
    have hmG : Measurable fun ω : Ω W 1 => ‖batchMat W g E 1 ω‖ₑ ^ (1 / 2 : ℝ) :=
      (measurable_batchMat W g E 1).enorm.pow_const _
    calc ∫⁻ ω, ‖batchMat W g E (r + 1) ω‖ₑ ^ (1 / 2 : ℝ) ∂(μ W (r + 1))
        ≤ ∫⁻ ω, ‖batchMat W g E r (blockAppend W r 1 ω).1‖ₑ ^ (1 / 2 : ℝ) *
          ‖batchMat W g E 1 (blockAppend W r 1 ω).2‖ₑ ^ (1 / 2 : ℝ) ∂(μ W (r + 1)) :=
          lintegral_mono hpt
      _ = (∫⁻ ω, ‖batchMat W g E r ω‖ₑ ^ (1 / 2 : ℝ) ∂(μ W r)) *
          ∫⁻ ω, ‖batchMat W g E 1 ω‖ₑ ^ (1 / 2 : ℝ) ∂(μ W 1) :=
          reduction_lintegral_blockAppend r 1 hmF hmG
      _ ≤ ENNReal.ofReal ((W : ℝ) ^ ((B / 2 + 1) * r)) *
          ENNReal.ofReal ((W : ℝ) ^ (B / 2 + 1)) := by gcongr
      _ = ENNReal.ofReal ((W : ℝ) ^ ((B / 2 + 1) * ((r + 1 : ℕ) : ℝ))) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hw0]
          congr 2
          push_cast
          ring

/-- `e^{-c(B₂ B₁; x)/2} ≤ e^{-c(B₁; x)/2} ‖B₂‖^{1/2}` for `B₁, B₂ ∈ 𝒢` (cocycle identity and
(F.2) [cc:eq:boundc], proof of Lemma 8.6 [up:lem:operator-reduction]). -/
private theorem reduction_exp_cocycle_le {W : ℕ} (hW : 0 < W)
    {B₁ B₂ : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (h₁ : B₁ ∈ isoGroup W)
    (h₂ : B₂ ∈ isoGroup W) (x : IsoFlag W) :
    Real.exp (-(1 / 2 : ℝ) * volCocycle (B₂ * B₁) x) ≤
      Real.exp (-(1 / 2 : ℝ) * volCocycle B₁ x) * ‖B₂‖ ^ (1 / 2 : ℝ) := by
  have : Nonempty (Fin 2 × Fin W) := ⟨(0, ⟨0, hW⟩)⟩
  have hu : IsUnit B₂ := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [h₂.2]; exact isUnit_one)
  have hpos : 0 < ‖B₂‖ := norm_pos_iff.mpr hu.ne_zero
  rw [volCocycle_mul h₁.1 hu, mul_add, Real.exp_add]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have habs := abs_volCocycle_le h₂.1 (flagAct B₁ x)
  rw [Real.rpow_def_of_pos hpos]
  refine Real.exp_le_exp.mpr ?_
  have := (abs_le.mp habs).1
  nlinarith

/-- The moment of `D_n⁻¹` at every length `n` from (8.21) [up:eq:power-input] at one point, with
`c′ = c/q` and `C′ = C e^c`, exponent `C + 1 + (B/2 + 1) q` (proof of Lemma 8.6
[up:lem:operator-reduction]). -/
theorem frameD_moment_le {B E₀ b c C : ℝ} (hB : 0 < B) (hE₀ : 0 < E₀) (hb : 1 ≤ b) (hc : 0 < c)
    {q : ℕ} (hq : 0 < q) {W : ℕ} (hW : (4 * (E₀ + 1)) ^ (2 / 3 : ℝ) ≤ W) {g E : ℝ}
    (hg1 : (W : ℝ) ^ (-B) ≤ g) (hg2 : g ≤ (W : ℝ) ^ B) (hE : |E| ≤ E₀)
    (hpow : PowerDecayAt W g E q b c C) {Φ : Matrix (Fin 2 × Fin W) (Fin W) ℂ}
    (hΦ : IsBoundaryFrame Φ) (n : ℕ) :
    ∫⁻ ω, ‖(frameD (transferProd g ((max 1 g * E / g : ℝ) : ℂ)
        (fun i => if h : i < n then gueBlock W n ω ⟨i, h⟩ else 0) n) Φ)⁻¹‖ₑ ^ (1 / 2 : ℝ)
        ∂(μ W n) ≤
      ENNReal.ofReal (C * Real.exp c * (W : ℝ) ^ (C + 1 + (B / 2 + 1) * q) *
        Real.exp (-(c / q) * n / b)) := by
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r : ℕ, r < q ∧ n = q * k + r :=
    ⟨n / q, n % q, Nat.mod_lt _ hq, (Nat.div_add_mod n q).symm⟩
  have h4 : (1 : ℝ) ≤ 4 * (E₀ + 1) := by linarith
  have hW1 : (1 : ℝ) ≤ W := le_trans (Real.one_le_rpow h4 (by norm_num)) hW
  have hw0 : (0 : ℝ) < W := by linarith
  have hWpos : 0 < W := by exact_mod_cast hw0
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  -- the cocycle splits the batch of `q k + r` blocks into the `k` full batches and the rest
  have hpt : ∀ ω : Ω W (q * k + r),
      ‖(frameD (transferProd g ((max 1 g * E / g : ℝ) : ℂ)
        (fun i => if h : i < q * k + r then gueBlock W (q * k + r) ω ⟨i, h⟩ else 0) (q * k + r))
        Φ)⁻¹‖ₑ ^ (1 / 2 : ℝ) ≤
      (∑ j, ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ) *
          volCocycle (batchMat W g E (q * k) (blockAppend W (q * k) r ω).1)
            ⟨omitPair Φ j, omitPair_mem_isoFlags hΦ j⟩))) *
        ‖batchMat W g E r (blockAppend W (q * k) r ω).2‖ₑ ^ (1 / 2 : ℝ) := by
    intro ω
    have h1 := reduction_frameD_inv_le g E (q * k + r) ω hΦ
    have h2 : ∀ j : Fin W, Real.exp (-(1 / 2 : ℝ) * volCocycle (batchMat W g E (q * k + r) ω)
        ⟨omitPair Φ j, omitPair_mem_isoFlags hΦ j⟩) ≤
        Real.exp (-(1 / 2 : ℝ) * volCocycle (batchMat W g E (q * k) (blockAppend W (q * k) r ω).1)
          ⟨omitPair Φ j, omitPair_mem_isoFlags hΦ j⟩) *
          ‖batchMat W g E r (blockAppend W (q * k) r ω).2‖ ^ (1 / 2 : ℝ) := fun j => by
      rw [batchMat_add]
      exact reduction_exp_cocycle_le hWpos (batchMat_mem_isoGroup W g E _ _)
        (batchMat_mem_isoGroup W g E _ _) _
    have h3 : ‖(frameD (transferProd g ((max 1 g * E / g : ℝ) : ℂ)
        (fun i => if h : i < q * k + r then gueBlock W (q * k + r) ω ⟨i, h⟩ else 0) (q * k + r))
        Φ)⁻¹‖ ^ (1 / 2 : ℝ) ≤
        (∑ j, Real.exp (-(1 / 2 : ℝ) *
          volCocycle (batchMat W g E (q * k) (blockAppend W (q * k) r ω).1)
            ⟨omitPair Φ j, omitPair_mem_isoFlags hΦ j⟩)) *
        ‖batchMat W g E r (blockAppend W (q * k) r ω).2‖ ^ (1 / 2 : ℝ) := by
      refine h1.trans ?_
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun j _ => h2 j
    rw [reduction_enorm_rpow _ (by norm_num), reduction_enorm_rpow _ (by norm_num),
      ← ENNReal.ofReal_sum_of_nonneg fun j _ => (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (Finset.sum_nonneg fun j _ => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal h3
  have hmF : Measurable fun ω : Ω W (q * k) => ∑ j, ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ) *
      volCocycle (batchMat W g E (q * k) ω) ⟨omitPair Φ j, omitPair_mem_isoFlags hΦ j⟩)) :=
    Finset.measurable_sum _ fun j _ => reduction_measurable_exp_cocycle W g E (q * k) _
  have hmG : Measurable fun ω : Ω W r => ‖batchMat W g E r ω‖ₑ ^ (1 / 2 : ℝ) :=
    (measurable_batchMat W g E r).enorm.pow_const _
  have hA := reduction_lintegral_norm_batchMat_le hB hE₀ hW hg1 hg2 hE r
  -- the sum over `j` of the power-decay bound
  have hsum : ∑ j : Fin W, ENNReal.ofReal
      ((halfOp W g E q)^[k] (fun _ => 1) ⟨omitPair Φ j, omitPair_mem_isoFlags hΦ j⟩) ≤
      ENNReal.ofReal ((W : ℝ) * (C * (W : ℝ) ^ C * Real.exp (-c * k / b))) := by
    calc _ ≤ ∑ _j : Fin W, ENNReal.ofReal (C * (W : ℝ) ^ C * Real.exp (-c * k / b)) :=
          Finset.sum_le_sum fun j _ =>
            ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hpow k _))
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  calc ∫⁻ ω, ‖(frameD (transferProd g ((max 1 g * E / g : ℝ) : ℂ)
        (fun i => if h : i < q * k + r then gueBlock W (q * k + r) ω ⟨i, h⟩ else 0) (q * k + r))
        Φ)⁻¹‖ₑ ^ (1 / 2 : ℝ) ∂(μ W (q * k + r))
      ≤ ∫⁻ ω, (∑ j, ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ) *
          volCocycle (batchMat W g E (q * k) (blockAppend W (q * k) r ω).1)
            ⟨omitPair Φ j, omitPair_mem_isoFlags hΦ j⟩))) *
        ‖batchMat W g E r (blockAppend W (q * k) r ω).2‖ₑ ^ (1 / 2 : ℝ) ∂(μ W (q * k + r)) :=
        lintegral_mono hpt
    _ = (∫⁻ ω, ∑ j, ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ) *
          volCocycle (batchMat W g E (q * k) ω) ⟨omitPair Φ j, omitPair_mem_isoFlags hΦ j⟩))
          ∂(μ W (q * k))) * ∫⁻ ω, ‖batchMat W g E r ω‖ₑ ^ (1 / 2 : ℝ) ∂(μ W r) :=
        reduction_lintegral_blockAppend (q * k) r hmF hmG
    _ = (∑ j : Fin W, ENNReal.ofReal
          ((halfOp W g E q)^[k] (fun _ => 1) ⟨omitPair Φ j, omitPair_mem_isoFlags hΦ j⟩)) *
          ∫⁻ ω, ‖batchMat W g E r ω‖ₑ ^ (1 / 2 : ℝ) ∂(μ W r) := by
        rw [lintegral_finsetSum _ fun j _ => reduction_measurable_exp_cocycle W g E (q * k) _]
        exact congrArg (· * _) (Finset.sum_congr rfl fun j _ =>
          reduction_lintegral_exp_cocycle W g E q k _)
    _ ≤ ENNReal.ofReal ((W : ℝ) * (C * (W : ℝ) ^ C * Real.exp (-c * k / b))) *
          ENNReal.ofReal ((W : ℝ) ^ ((B / 2 + 1) * r)) := by gcongr
    _ ≤ _ := by
        -- `C ≥ 0` from the bound at one point
        have hX : 0 ≤ C * (W : ℝ) ^ C * Real.exp (-c * k / b) :=
          (abs_nonneg _).trans (hpow k ⟨omitPair Φ ⟨0, hWpos⟩, omitPair_mem_isoFlags hΦ ⟨0, hWpos⟩⟩)
        have hWC : 0 < (W : ℝ) ^ C := Real.rpow_pos_of_pos hw0 _
        have hC : 0 ≤ C := by
          by_contra hneg
          have hneg := lt_of_not_ge hneg
          have := mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg hWC) (Real.exp_pos (-c * k / b))
          linarith
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        -- the incomplete batch: `W^{(B/2+1) r} ≤ W^{(B/2+1) q}`
        have hrq : (W : ℝ) ^ ((B / 2 + 1) * r) ≤ (W : ℝ) ^ ((B / 2 + 1) * q) :=
          Real.rpow_le_rpow_of_exponent_le hW1
            (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hr.le) (by positivity))
        -- the lost part of the last batch: `e^{-ck/𝔟} ≤ e^c e^{-(c/q)(qk + r)/𝔟}`
        have hrb : (r : ℝ) / (q * b) ≤ 1 := by
          rw [div_le_one (by nlinarith)]
          have : (r : ℝ) < q := by exact_mod_cast hr
          nlinarith
        have hexp : Real.exp (-c * k / b) ≤
            Real.exp c * Real.exp (-(c / q) * ((q * k + r : ℕ) : ℝ) / b) := by
          rw [← Real.exp_add]
          refine Real.exp_le_exp.mpr ?_
          have hid : -(c / q) * ((q * k + r : ℕ) : ℝ) / b =
              -(c * k / b) - c * ((r : ℝ) / (q * b)) := by
            push_cast
            field_simp
            ring
          rw [hid]
          have : c * ((r : ℝ) / (q * b)) ≤ c := mul_le_of_le_one_right hc.le hrb
          have e : -c * k / b = -(c * k / b) := by ring
          rw [e]
          linarith
        have hexpo : (W : ℝ) ^ (C + 1 + (B / 2 + 1) * q) =
            (W : ℝ) ^ C * (W : ℝ) * (W : ℝ) ^ ((B / 2 + 1) * q) := by
          rw [Real.rpow_add hw0, Real.rpow_add hw0, Real.rpow_one]
        rw [hexpo]
        have hA0 : 0 ≤ C * (W : ℝ) ^ C * (W : ℝ) := by positivity
        calc (W : ℝ) * (C * (W : ℝ) ^ C * Real.exp (-c * k / b)) * (W : ℝ) ^ ((B / 2 + 1) * r)
            = (C * (W : ℝ) ^ C * (W : ℝ)) *
                ((W : ℝ) ^ ((B / 2 + 1) * r) * Real.exp (-c * k / b)) := by ring
          _ ≤ (C * (W : ℝ) ^ C * (W : ℝ)) *
                ((W : ℝ) ^ ((B / 2 + 1) * q) *
                  (Real.exp c * Real.exp (-(c / q) * ((q * k + r : ℕ) : ℝ) / b))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul hrq hexp (Real.exp_pos _).le
                (Real.rpow_nonneg hw0.le _)) hA0
          _ = _ := by ring

end LSBA
