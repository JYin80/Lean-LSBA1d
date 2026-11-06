import LSBA.Spectral.DeformedOffDiagLaw
import LSBA.Gauss.RademacherChaos

/-!
# The isotropic local law

The second estimate of (G.1) [us:eq:weighted-local-law]:
`|u*(G − M_B)v| ≤ n^ξ(nη)^{−1/2}‖M_Bu‖‖M_Bv‖` with high probability.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal Matrix.Norms.L2Operator

noncomputable section
open scoped Classical

namespace LSBA

/-! ### Conjugation identities -/

/-- The inverse of `W X W*` is `W X⁻¹ W*` when `W W* = 1`. -/
private lemma isoLaw_inv_conj {ι : Type*} [Fintype ι] [DecidableEq ι] {W : Matrix ι ι ℂ}
    (hW : W * star W = 1) (X : Matrix ι ι ℂ) : (W * X * star W)⁻¹ = W * X⁻¹ * star W := by
  have hW' : star W * W = 1 := mul_eq_one_comm.mp hW
  have e1 : W⁻¹ = star W := Matrix.inv_eq_right_inv hW
  have e2 : (star W)⁻¹ = W := Matrix.inv_eq_right_inv hW'
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, e1, e2, Matrix.mul_assoc]

/-- The resolvent of `W A W*` is `W G(A) W*` when `W W* = 1`. -/
private lemma isoLaw_resolventMat_conj {ι : Type*} [Fintype ι] [DecidableEq ι] {W : Matrix ι ι ℂ}
    (hW : W * star W = 1) (A : Matrix ι ι ℂ) (z : ℂ) :
    resolventMat (W * A * star W) z = W * resolventMat A z * star W := by
  have h : W * A * star W - z • (1 : Matrix ι ι ℂ) = W * (A - z • (1 : Matrix ι ι ℂ)) * star W := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hW]
  unfold resolventMat
  rw [h, isoLaw_inv_conj hW]

/-- `Σ_k |(U w)_k|² = Σ_k |w_k|²` when `U* U = 1`. -/
private lemma isoLaw_sum_sq_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] {U : Matrix ι ι ℂ}
    (hU : star U * U = 1) (w : ι → ℂ) :
    ∑ k, ‖(U *ᵥ w) k‖ ^ 2 = ∑ k, ‖w k‖ ^ 2 := by
  have key : ∀ x : ι → ℂ, ((∑ k, ‖x k‖ ^ 2 : ℝ) : ℂ) = star x ⬝ᵥ x := by
    intro x
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  have h : star (U *ᵥ w) ⬝ᵥ (U *ᵥ w) = star w ⬝ᵥ w := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.star_eq_conjTranspose, hU, Matrix.one_mulVec]
  have h2 := (key (U *ᵥ w)).trans (h.trans (key w).symm)
  exact_mod_cast h2

/-- `u^*(U X U^*) v = (U^* u)^* X (U^* v)`. -/
private lemma isoLaw_dot_conj {ι : Type*} [Fintype ι] (U X : Matrix ι ι ℂ) (u v : ι → ℂ) :
    star u ⬝ᵥ ((U * X * star U) *ᵥ v) = star (star U *ᵥ u) ⬝ᵥ (X *ᵥ (star U *ᵥ v)) := by
  rw [Matrix.star_mulVec, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.star_eq_conjTranspose, Matrix.mul_assoc]

/-- The class of Lemma A.21 [da:lem:deformed] is invariant under unitary conjugation. -/
private lemma isoLaw_deformClass_conj {n : ℕ} (hn : 0 < n) {ε : ℝ} {B : Matrix (Fin n) (Fin n) ℂ}
    (hB : DeformClass ε B) (W : Matrix.unitaryGroup (Fin n) ℂ) :
    DeformClass ε ((W : Matrix (Fin n) (Fin n) ℂ) * B * star (W : Matrix (Fin n) (Fin n) ℂ)) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨hBh, Bs, Bb, hsum, hs, hb⟩ := hB
  have hWu : (W : Matrix (Fin n) (Fin n) ℂ) ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := W.2
  have hn1 : ‖(W : Matrix (Fin n) (Fin n) ℂ)‖ = 1 := CStarRing.norm_of_mem_unitary hWu
  have hn1' : ‖star (W : Matrix (Fin n) (Fin n) ℂ)‖ = 1 :=
    CStarRing.norm_of_mem_unitary (Unitary.star_mem hWu)
  refine ⟨?_, (W : Matrix (Fin n) (Fin n) ℂ) * Bs * star (W : Matrix (Fin n) (Fin n) ℂ),
    (W : Matrix (Fin n) (Fin n) ℂ) * Bb * star (W : Matrix (Fin n) (Fin n) ℂ), ?_, ?_, ?_⟩
  · have := Matrix.isHermitian_conjTranspose_mul_mul (star (W : Matrix (Fin n) (Fin n) ℂ)) hBh
    rwa [← Matrix.star_eq_conjTranspose, star_star] at this
  · rw [hsum, Matrix.mul_add, Matrix.add_mul]
  · calc ‖(W : Matrix (Fin n) (Fin n) ℂ) * Bs * star (W : Matrix (Fin n) (Fin n) ℂ)‖
        ≤ ‖(W : Matrix (Fin n) (Fin n) ℂ) * Bs‖ * ‖star (W : Matrix (Fin n) (Fin n) ℂ)‖ :=
          norm_mul_le _ _
      _ ≤ ‖(W : Matrix (Fin n) (Fin n) ℂ)‖ * ‖Bs‖ * ‖star (W : Matrix (Fin n) (Fin n) ℂ)‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ ε := by rw [hn1, hn1', one_mul, mul_one]; exact hs
  · have h1 : ((W : Matrix (Fin n) (Fin n) ℂ) * Bb * star (W : Matrix (Fin n) (Fin n) ℂ)).rank ≤
        Bb.rank := (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    exact (Nat.cast_le.mpr h1).trans hb

/-! ### Diagonal profiles -/

/-- For diagonal `B` the profile `M_B(z)` is diagonal. -/
private lemma isoLaw_MB_isDiag {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsDiag) (z : ℂ) :
    (MB B z).IsDiag := by
  unfold MB deformedMat resolventMat
  have h : -B - (z + mB B z) • (1 : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.diagonal (fun k => -B k k - (z + mB B z)) := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp
    · simp [Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab, hB hab]
  rw [h, Matrix.inv_diagonal]
  exact Matrix.isDiag_diagonal _

/-- A diagonal matrix acts on a vector coordinatewise. -/
private lemma isoLaw_mulVec_diag {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsDiag)
    (u : Fin n → ℂ) (k : Fin n) : (M *ᵥ u) k = M k k * u k := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single k]
  · intro j _ hj
    rw [hM (Ne.symm hj), zero_mul]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- The bilinear form against a diagonal `M` splits into the diagonal part and the off-diagonal
chaos form: `u^*(G - M)v = Σ_i ū_i (G_ii - M_ii) v_i + Σ_{i ≠ j} ū_i G_ij v_j`. -/
private lemma isoLaw_split {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsDiag)
    (G : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) :
    star u ⬝ᵥ ((G - M) *ᵥ v) = ∑ i, star (u i) * ((G i i - M i i) * v i) +
      ∑ k, ∑ l, (if k = l then 0 else star (u k) * G k l * v l) := by
  have h : ∀ i j, star (u i) * ((G - M) i j * v j) =
      (if i = j then star (u i) * ((G i i - M i i) * v i) else 0) +
        (if i = j then 0 else star (u i) * G i j * v j) := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp
    · simp only [hij, ite_false, Matrix.sub_apply, hM hij, sub_zero, zero_add]
      ring
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, h, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-! ### Random signs -/

/-- The sign matrix `S = diag(s)` is self-adjoint. -/
private lemma isoLaw_sign_star {n : ℕ} (s : Fin n → ℤˣ) :
    star (Matrix.diagonal (fun i => ((s i : ℤ) : ℂ))) =
      Matrix.diagonal (fun i => ((s i : ℤ) : ℂ)) := by
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 1
  ext i
  simp

/-- `S S^* = 1` for `S = diag(s)`. -/
private lemma isoLaw_sign_mul {n : ℕ} (s : Fin n → ℤˣ) :
    Matrix.diagonal (fun i => ((s i : ℤ) : ℂ)) * star (Matrix.diagonal (fun i => ((s i : ℤ) : ℂ)))
      = 1 := by
  rw [isoLaw_sign_star, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rcases Int.units_eq_one_or (s i) with h | h <;> simp [h]

/-- A sign squares to one. -/
private lemma isoLaw_sign_sq (x : ℤˣ) : ((x : ℤ) : ℂ) * ((x : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or x with h | h <;> simp [h]

/-- A sign has modulus one. -/
private lemma isoLaw_sign_norm (x : ℤˣ) : ‖((x : ℤ) : ℂ)‖ = 1 := by
  rcases Int.units_eq_one_or x with h | h <;> simp [h]

/-- Entries of `S X S` for `S = diag(s)`. -/
private lemma isoLaw_sign_entry {n : ℕ} (s : Fin n → ℤˣ) (X : Matrix (Fin n) (Fin n) ℂ)
    (k l : Fin n) :
    (Matrix.diagonal (fun i => ((s i : ℤ) : ℂ)) * X * Matrix.diagonal (fun i => ((s i : ℤ) : ℂ)))
      k l = ((s k : ℤ) : ℂ) * X k l * ((s l : ℤ) : ℂ) := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- A diagonal `B` is fixed by the sign conjugation. -/
private lemma isoLaw_sign_diag {n : ℕ} (s : Fin n → ℤˣ) {B : Matrix (Fin n) (Fin n) ℂ}
    (hB : B.IsDiag) :
    Matrix.diagonal (fun i => ((s i : ℤ) : ℂ)) * B * Matrix.diagonal (fun i => ((s i : ℤ) : ℂ)) =
      B := by
  ext k l
  rw [isoLaw_sign_entry]
  by_cases hkl : k = l
  · subst hkl
    rw [mul_comm _ (B k k), mul_assoc, isoLaw_sign_sq, mul_one]
  · rw [hB hkl, mul_zero, zero_mul]

/-! ### Probability -/

/-- Markov's inequality for a finite uniform average of `2p`-th powers: if
`Σ_s x_s^{2p} ≤ N K σ^{2p}`, then `#{s : x_s > t σ} ≤ N K t^{-2p}`. -/
private lemma isoLaw_markov {S : Type*} [Fintype S] (x : S → ℝ) (hx : ∀ s, 0 ≤ x s) {p : ℕ}
    (hp : 1 ≤ p) {N K σ t : ℝ} (hNK : 0 ≤ N * K) (hσ : 0 ≤ σ) (ht : 0 < t)
    (hsum : ∑ s, x s ^ (2 * p) ≤ N * K * σ ^ (2 * p)) :
    ∑ s, (if t * σ < x s then (1 : ℝ) else 0) ≤ N * K * (t ^ (2 * p))⁻¹ := by
  have hp2 : 2 * p ≠ 0 := by omega
  rcases hσ.eq_or_lt with h0 | hσ0
  · subst h0
    have hz : ∀ s, x s = 0 := by
      intro s
      have h1 : ∑ s, x s ^ (2 * p) ≤ 0 := by simpa [zero_pow hp2] using hsum
      have h2 : x s ^ (2 * p) ≤ 0 :=
        (Finset.single_le_sum (fun s _ => pow_nonneg (hx s) _) (Finset.mem_univ s)).trans h1
      have h3 : x s ^ (2 * p) = 0 := le_antisymm h2 (pow_nonneg (hx s) _)
      exact pow_eq_zero_iff hp2 |>.mp h3
    simp only [hz, mul_zero, lt_irrefl, ite_false, Finset.sum_const_zero]
    positivity
  · have htσ : 0 < (t * σ) ^ (2 * p) := by positivity
    calc ∑ s, (if t * σ < x s then (1 : ℝ) else 0)
        ≤ ∑ s, x s ^ (2 * p) / (t * σ) ^ (2 * p) := by
          refine Finset.sum_le_sum fun s _ => ?_
          split_ifs with h
          · rw [le_div_iff₀ htσ, one_mul]
            exact pow_le_pow_left₀ (by positivity) h.le _
          · exact div_nonneg (pow_nonneg (hx s) _) htσ.le
      _ = (∑ s, x s ^ (2 * p)) / (t * σ) ^ (2 * p) := by rw [Finset.sum_div]
      _ ≤ N * K * σ ^ (2 * p) / (t * σ) ^ (2 * p) := div_le_div_of_nonneg_right hsum htσ.le
      _ = N * K * (t ^ (2 * p))⁻¹ := by
          have : σ ^ (2 * p) ≠ 0 := by positivity
          rw [mul_pow]
          field_simp

/-- Averaging over a finite family of measure-preserving maps: if every orbit
`(T_s ω)_s` meets `A` at most `#S · K` times, then `μ(A) ≤ K`. -/
private lemma isoLaw_avg_le {n : ℕ} {S : Type*} [Fintype S] [Nonempty S]
    (T : S → Ω n 1 → Ω n 1) (hT : ∀ s, MeasurePreserving (T s) (μ n 1) (μ n 1))
    {A : Set (Ω n 1)} [DecidablePred (· ∈ A)] (hA : MeasurableSet A) {K : ℝ}
    (hK : ∀ ω, (∑ s, if T s ω ∈ A then (1 : ℝ) else 0) ≤ Fintype.card S * K) :
    μ n 1 A ≤ ENNReal.ofReal K := by
  have hpre : ∀ s, MeasurableSet (T s ⁻¹' A) := fun s => (hT s).measurable hA
  have h1 : (Fintype.card S : ℝ≥0∞) * μ n 1 A = ∫⁻ ω, ∑ s, (T s ⁻¹' A).indicator 1 ω ∂(μ n 1) := by
    rw [lintegral_finsetSum _ fun s _ => (measurable_one.indicator (hpre s))]
    simp_rw [lintegral_indicator_one (hpre _), (hT _).measure_preimage hA.nullMeasurableSet]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h2 : ∫⁻ ω, ∑ s, (T s ⁻¹' A).indicator 1 ω ∂(μ n 1) ≤
      ENNReal.ofReal (Fintype.card S * K) := by
    calc ∫⁻ ω, ∑ s, (T s ⁻¹' A).indicator 1 ω ∂(μ n 1)
        ≤ ∫⁻ _ω, ENNReal.ofReal (Fintype.card S * K) ∂(μ n 1) := by
          refine lintegral_mono fun ω => ?_
          have e : ∀ s, (T s ⁻¹' A).indicator (1 : Ω n 1 → ℝ≥0∞) ω =
              ENNReal.ofReal (if T s ω ∈ A then (1 : ℝ) else 0) := by
            intro s
            simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
            split_ifs <;> simp
          simp_rw [e]
          rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => by positivity)]
          exact ENNReal.ofReal_le_ofReal (hK ω)
      _ = ENNReal.ofReal (Fintype.card S * K) := by
          rw [lintegral_const, measure_univ, mul_one]
  have hc0 : (Fintype.card S : ℝ≥0∞) ≠ 0 := by
    have := Fintype.card_pos (α := S)
    exact_mod_cast this.ne'
  have hc1 : (Fintype.card S : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast] at h2
  exact (ENNReal.mul_le_mul_iff_right hc0 hc1).mp (h1 ▸ h2)

/-! ### Measurability -/

/-- The entries of the GUE matrix are measurable in the sample. -/
private lemma isoLaw_measurable_entry (n : ℕ) (a b : Fin n) :
    Measurable fun ω : Ω n 1 => gueMat n ω a b := by
  unfold gueMat gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

/-- The matrix inverse is measurable. -/
private lemma isoLaw_measurable_inv {m : Type*} [Fintype m] [DecidableEq m] :
    Measurable fun A : Matrix m m ℂ => A⁻¹ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  have hd : Measurable fun A : Matrix m m ℂ => A.det :=
    (continuous_id.matrix_det).measurable
  have ha : Measurable fun A : Matrix m m ℂ => A.adjugate i j :=
    (continuous_id.matrix_adjugate).measurable.eval_matrix
  exact (hd.inv).mul ha

/-- The entries of the resolvent of the deformed GUE matrix are measurable in the sample. -/
private lemma isoLaw_measurable_resolvent (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    (k l : Fin n) : Measurable fun ω : Ω n 1 => resolventMat (gueMat n ω - B) z k l := by
  have h : Measurable fun ω : Ω n 1 => resolventMat (gueMat n ω - B) z := by
    unfold resolventMat
    refine isoLaw_measurable_inv.comp ?_
    refine Measurable.of_eval_matrix _ fun a b => ?_
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    exact ((isoLaw_measurable_entry n a b).sub measurable_const).sub measurable_const
  exact (measurable_pi_apply l).comp ((measurable_pi_apply k).comp h)

/-! ### Exponents -/

/-- For large `n`: `n ≥ 3`, `n ≥ K` and `n^{ξ/2} ≥ 2`. -/
private lemma isoLaw_eventually {ξ : ℝ} (hξ : 0 < ξ) (K : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop, (3 : ℝ) ≤ n ∧ K ≤ n ∧ 2 ≤ (n : ℝ) ^ (ξ / 2) := by
  have h1 := tendsto_natCast_atTop_atTop (R := ℝ)
  exact (h1.eventually_ge_atTop 3).and ((h1.eventually_ge_atTop K).and
    (((tendsto_rpow_atTop (by positivity : 0 < ξ / 2)).comp h1).eventually_ge_atTop 2))

/-- The rate: `(1 + n^{ξ/4}) n^{ξ/4} ≤ n^ξ` once `n^{ξ/2} ≥ 2`. -/
private lemma isoLaw_rate {N ξ : ℝ} (hN : 1 ≤ N) (hξ : 0 < ξ) (h2 : 2 ≤ N ^ (ξ / 2)) :
    (1 + N ^ (ξ / 4)) * N ^ (ξ / 4) ≤ N ^ ξ := by
  have hN0 : 0 < N := by linarith
  have hx1 : 1 ≤ N ^ (ξ / 4) := Real.one_le_rpow hN (by positivity)
  have e2 : N ^ (ξ / 2) = (N ^ (ξ / 4)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  have e4 : N ^ ξ = (N ^ (ξ / 4)) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  rw [e2] at h2
  rw [e4]
  nlinarith

/-- The chaos tail: `K n^{-2p ξ/4} ≤ n^{-(D+1)}` when `p ≥ 2(D+2)/ξ` and `n ≥ K`. -/
private lemma isoLaw_chaos_tail {N ξ D K : ℝ} {p : ℕ} (hN : 1 ≤ N) (hξ : 0 < ξ) (hK : 0 < K)
    (hKN : K ≤ N) (hp : 2 * (D + 2) / ξ ≤ p) :
    K * ((N ^ (ξ / 4)) ^ (2 * p))⁻¹ ≤ N ^ (-(D + 1)) := by
  have hN0 : 0 < N := by linarith
  have e : (N ^ (ξ / 4)) ^ (2 * p) = N ^ (ξ / 4 * ((2 * p : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
  have hexp : D + 2 ≤ ξ / 4 * ((2 * p : ℕ) : ℝ) := by
    have := (div_le_iff₀ hξ).mp hp
    push_cast
    nlinarith
  have hpos : 0 < N ^ (D + 2) := Real.rpow_pos_of_pos hN0 _
  have h1 : N ^ (D + 2) ≤ (N ^ (ξ / 4)) ^ (2 * p) := by
    rw [e]; exact Real.rpow_le_rpow_of_exponent_le hN hexp
  calc K * ((N ^ (ξ / 4)) ^ (2 * p))⁻¹ ≤ K * (N ^ (D + 2))⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ hpos h1) hK.le
    _ ≤ N * (N ^ (D + 2))⁻¹ := mul_le_mul_of_nonneg_right hKN (inv_nonneg.mpr hpos.le)
    _ = N ^ (-(D + 1)) := by
        rw [← Real.rpow_neg hN0.le, show -(D + 1) = 1 + -(D + 2) by ring, Real.rpow_add hN0,
          Real.rpow_one]

/-- The union bound: `3 n^{-(D+1)} ≤ n^{-D}` for `n ≥ 3`. -/
private lemma isoLaw_union {N D : ℝ} (hN : 3 ≤ N) : 3 * N ^ (-(D + 1)) ≤ N ^ (-D) := by
  have hN0 : 0 < N := by linarith
  have hpos := Real.rpow_pos_of_pos hN0 (-D)
  rw [show -(D + 1) = -D + -1 by ring, Real.rpow_add hN0, Real.rpow_neg_one]
  have h3 : 3 * N⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hN0]; exact hN
  nlinarith

/-! ### The isotropic law for diagonal `B` -/

/-- The isotropic law for diagonal `B` (Appendix G.1 [app:relative-local-law-proof]): the
diagonal part by the entry law (G.3) [us:eq:weighted-entry-law] and Cauchy–Schwarz, the
off-diagonal part by the off-diagonal law (G.4) [us:eq:weighted-offdiagonal-law] and the order-two
chaos bound in random signs `s_i = ±1`, conditionally on `G`. -/
private theorem isoLaw_diag (κ₀ Cstar : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hC : 0 < Cstar) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε δ ξ D : ℝ, 0 < ε → ε ≤ ε₀ → 0 < δ → 0 < ξ → 0 < D →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (B : Matrix (Fin n) (Fin n) ℂ) (E η : ℝ),
        DeformClass ε B → B.IsDiag → |E| ≤ 2 - κ₀ → (n : ℝ) ^ (-1 + δ) ≤ η → η ≤ Cstar →
        ∀ u v : Fin n → ℂ,
        μ n 1 {ω | (n : ℝ) ^ ξ / Real.sqrt (n * η) *
              Real.sqrt (∑ k, ‖(MB B (E + η * Complex.I) *ᵥ u) k‖ ^ 2) *
              Real.sqrt (∑ k, ‖(MB B (E + η * Complex.I) *ᵥ v) k‖ ^ 2) <
            ‖star u ⬝ᵥ ((resolventMat (gueMat n ω - B) (E + η * Complex.I) -
              MB B (E + η * Complex.I)) *ᵥ v)‖} ≤
          ENNReal.ofReal ((n : ℝ) ^ (-D)) := by
  obtain ⟨ε₁, hε₁, hentry⟩ := localLaw_entry κ₀ Cstar hκ₀ hκ₀' hC
  obtain ⟨ε₂, hε₂, hoff⟩ := localLaw_offdiag κ₀ Cstar hκ₀ hκ₀' hC
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro ε δ ξ D hε hεε₀ hδ hξ hD
  obtain ⟨n₁, hn₁⟩ := hentry ε δ (ξ / 4) (D + 1) hε (hεε₀.trans (min_le_left _ _)) hδ
    (by positivity) (by linarith)
  obtain ⟨n₂, hn₂⟩ := hoff ε δ (ξ / 4) (D + 1) hε (hεε₀.trans (min_le_right _ _)) hδ
    (by positivity) (by linarith)
  set p : ℕ := ⌈2 * (D + 2) / ξ⌉₊ + 1 with hp
  have hp1 : 1 ≤ p := by omega
  have hpD : 2 * (D + 2) / ξ ≤ (p : ℝ) := by
    have := Nat.le_ceil (2 * (D + 2) / ξ)
    rw [hp]; push_cast; linarith
  obtain ⟨Cp, hCp, hchaos⟩ := rademacher_chaos p
  obtain ⟨n₃, hn₃⟩ := Filter.eventually_atTop.mp (isoLaw_eventually hξ Cp)
  refine ⟨max (max n₁ n₂) n₃, ?_⟩
  intro n hn B E η hcl hBd hE hηlow hηC u v
  obtain ⟨hN3, hNC, hN2⟩ := hn₃ n (le_of_max_le_right hn)
  have hN0 : (0 : ℝ) < n := by linarith
  have hN1 : (1 : ℝ) ≤ n := by linarith
  have hη0 : 0 < η := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hηlow
  set M : Matrix (Fin n) (Fin n) ℂ := MB B (E + η * Complex.I) with hMdef
  have hM : M.IsDiag := isoLaw_MB_isDiag hBd _
  obtain ⟨G, hG⟩ : ∃ G : Ω n 1 → Matrix (Fin n) (Fin n) ℂ,
      ∀ ω, G ω = resolventMat (gueMat n ω - B) (E + η * Complex.I) := ⟨_, fun _ => rfl⟩
  simp only [← hG]
  set t : ℝ := (n : ℝ) ^ (ξ / 4) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hN0 _
  set a : ℝ := t / Real.sqrt (n * η) with ha
  have ha0 : 0 ≤ a := by positivity
  set Su : ℝ := ∑ k, ‖(M *ᵥ u) k‖ ^ 2 with hSu
  set Sv : ℝ := ∑ k, ‖(M *ᵥ v) k‖ ^ 2 with hSv
  have hSu0 : 0 ≤ Su := by positivity
  have hSv0 : 0 ≤ Sv := by positivity
  set σ : ℝ := a * Real.sqrt Su * Real.sqrt Sv with hσ
  have hσ0 : 0 ≤ σ := by positivity
  set c : Ω n 1 → Fin n → Fin n → ℂ := fun ω k l => star (u k) * G ω k l * v l with hc
  set Q : Ω n 1 → ℂ := fun ω => ∑ k, ∑ l, (if k = l then 0 else c ω k l) with hQ
  set Good : Set (Ω n 1) := {ω | (∀ i, ‖G ω i i - M i i‖ ≤ a * ‖M i i‖ ^ 2) ∧
    ∀ i j, i ≠ j → ‖G ω i j‖ ≤ a * ‖M i i‖ * ‖M j j‖} with hGood
  set SE : Set (Ω n 1) := {ω | ∃ i, a * ‖M i i‖ ^ 2 < ‖G ω i i - M i i‖} with hSE
  set SO : Set (Ω n 1) := {ω | ∃ i j : Fin n, i ≠ j ∧ a * ‖M i i‖ * ‖M j j‖ < ‖G ω i j‖}
    with hSO
  set A : Set (Ω n 1) := Good ∩ {ω | t * σ < ‖Q ω‖} with hA
  -- the entry and off-diagonal events
  have hSEm : μ n 1 SE ≤ ENNReal.ofReal ((n : ℝ) ^ (-(D + 1))) := by
    have h := hn₁ n ((le_max_left _ _).trans (le_of_max_le_left hn)) B E η hcl hBd hE hηlow hηC
    simp only [← hG] at h
    exact h
  have hSOm : μ n 1 SO ≤ ENNReal.ofReal ((n : ℝ) ^ (-(D + 1))) := by
    have h := hn₂ n ((le_max_right _ _).trans (le_of_max_le_left hn)) B E η hcl hBd hE hηlow hηC
    simp only [← hG] at h
    exact h
  -- measurability
  have hGm : ∀ k l, Measurable fun ω => G ω k l := by
    intro k l
    simp only [hG]
    exact isoLaw_measurable_resolvent n B _ k l
  have hGoodm : MeasurableSet Good := by
    refine Measurable.setOf (Measurable.and (Measurable.forall fun i => ?_)
      (Measurable.forall fun i => Measurable.forall fun j => Measurable.imp measurable_const ?_))
    · exact measurableSet_setOfPred.1
        (measurableSet_le ((hGm i i).sub measurable_const).norm measurable_const)
    · exact measurableSet_setOfPred.1 (measurableSet_le (hGm i j).norm measurable_const)
  have hQm : Measurable Q := by
    refine Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ => ?_
    by_cases hkl : k = l
    · simp only [hkl, ite_true]; exact measurable_const
    · simp only [hkl, ite_false, hc]
      exact (measurable_const.mul (hGm k l)).mul measurable_const
  have hAm : MeasurableSet A := hGoodm.inter (measurableSet_lt measurable_const hQm.norm)
  -- the sign conjugations
  choose T hT hTV using fun s : Fin n → ℤˣ => measurePreserving_signConj n s
  have hGT : ∀ s ω k l, G (T s ω) k l = ((s k : ℤ) : ℂ) * G ω k l * ((s l : ℤ) : ℂ) := by
    intro s ω k l
    have h1 : gueMat n (T s ω) - B = Matrix.diagonal (fun i => ((s i : ℤ) : ℂ)) *
        (gueMat n ω - B) * star (Matrix.diagonal (fun i => ((s i : ℤ) : ℂ))) := by
      rw [hTV s ω, isoLaw_sign_star, Matrix.mul_sub, Matrix.sub_mul, isoLaw_sign_diag s hBd]
    rw [hG, hG, h1, isoLaw_resolventMat_conj (isoLaw_sign_mul s), isoLaw_sign_star,
      isoLaw_sign_entry]
  have hGoodT : ∀ s ω, T s ω ∈ Good ↔ ω ∈ Good := by
    intro s ω
    have hd : ∀ i, G (T s ω) i i = G ω i i := by
      intro i
      rw [hGT, mul_comm _ (G ω i i), mul_assoc, isoLaw_sign_sq, mul_one]
    have ho : ∀ i j, ‖G (T s ω) i j‖ = ‖G ω i j‖ := by
      intro i j
      rw [hGT, norm_mul, norm_mul, isoLaw_sign_norm, isoLaw_sign_norm, one_mul, mul_one]
    simp only [hGood, Set.mem_ofPred_eq, hd, ho]
  have hQT : ∀ s ω, Q (T s ω) = ∑ k, ∑ l,
      (if k = l then 0 else c ω k l * ((s k : ℤ) : ℂ) * ((s l : ℤ) : ℂ)) := by
    intro s ω
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    split_ifs
    · rfl
    · simp only [hc, hGT]; ring
  -- deterministic bounds on the good event
  have hMu : ∀ w : Fin n → ℂ, ∑ k, ‖(M *ᵥ w) k‖ ^ 2 = ∑ k, (‖M k k‖ * ‖w k‖) ^ 2 := by
    intro w
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [isoLaw_mulVec_diag hM, norm_mul]
  have hσsq : σ ^ 2 = a ^ 2 * Su * Sv := by
    rw [hσ, mul_pow, mul_pow, Real.sq_sqrt hSu0, Real.sq_sqrt hSv0]
  have hcs : ∀ ω ∈ Good, (∑ k, ∑ l, if k = l then (0 : ℝ) else ‖c ω k l‖ ^ 2) ≤ σ ^ 2 := by
    intro ω hω
    have e : a ^ 2 * Su * Sv = ∑ k, ∑ l,
        a ^ 2 * (‖M k k‖ * ‖u k‖) ^ 2 * (‖M l l‖ * ‖v l‖) ^ 2 := by
      rw [hSu, hSv, hMu u, hMu v, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [hσsq, e]
    refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
    split_ifs with hkl
    · positivity
    · have h1 := hω.2 k l hkl
      have h2 : ‖c ω k l‖ ≤ a * (‖M k k‖ * ‖u k‖) * (‖M l l‖ * ‖v l‖) := by
        simp only [hc, norm_mul, norm_star]
        calc ‖u k‖ * ‖G ω k l‖ * ‖v l‖ ≤ ‖u k‖ * (a * ‖M k k‖ * ‖M l l‖) * ‖v l‖ := by gcongr
          _ = _ := by ring
      calc ‖c ω k l‖ ^ 2 ≤ (a * (‖M k k‖ * ‖u k‖) * (‖M l l‖ * ‖v l‖)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h2 2
        _ = a ^ 2 * (‖M k k‖ * ‖u k‖) ^ 2 * (‖M l l‖ * ‖v l‖) ^ 2 := by ring
  have hdiag : ∀ ω ∈ Good, ‖∑ i, star (u i) * ((G ω i i - M i i) * v i)‖ ≤ σ := by
    intro ω hω
    calc ‖∑ i, star (u i) * ((G ω i i - M i i) * v i)‖
        ≤ ∑ i, ‖star (u i) * ((G ω i i - M i i) * v i)‖ := norm_sum_le _ _
      _ ≤ ∑ i, a * ((‖M i i‖ * ‖u i‖) * (‖M i i‖ * ‖v i‖)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul, norm_mul, norm_star]
          have := hω.1 i
          calc ‖u i‖ * (‖G ω i i - M i i‖ * ‖v i‖) ≤ ‖u i‖ * (a * ‖M i i‖ ^ 2 * ‖v i‖) := by
                gcongr
            _ = _ := by ring
      _ = a * ∑ i, (‖M i i‖ * ‖u i‖) * (‖M i i‖ * ‖v i‖) := by rw [Finset.mul_sum]
      _ ≤ a * (Real.sqrt (∑ i, (‖M i i‖ * ‖u i‖) ^ 2) *
            Real.sqrt (∑ i, (‖M i i‖ * ‖v i‖) ^ 2)) :=
          mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) ha0
      _ = σ := by rw [hσ, hSu, hSv, hMu u, hMu v, mul_assoc]
  -- the chaos event
  have hK : ∀ ω, (∑ s, if T s ω ∈ A then (1 : ℝ) else 0) ≤
      Fintype.card (Fin n → ℤˣ) * (Cp * (t ^ (2 * p))⁻¹) := by
    intro ω
    have hcard0 : (0 : ℝ) < Fintype.card (Fin n → ℤˣ) := by exact_mod_cast Fintype.card_pos
    by_cases hω : ω ∈ Good
    · have hmem : ∀ s, (T s ω ∈ A ↔ t * σ < ‖∑ k, ∑ l,
          (if k = l then 0 else c ω k l * ((s k : ℤ) : ℂ) * ((s l : ℤ) : ℂ))‖) := by
        intro s
        change T s ω ∈ Good ∧ t * σ < ‖Q (T s ω)‖ ↔ _
        rw [hGoodT s ω, hQT s ω]
        exact and_iff_right hω
      simp_rw [hmem]
      refine le_of_le_of_eq (isoLaw_markov (N := (Fintype.card (Fin n → ℤˣ) : ℝ)) (K := Cp)
        (fun s : Fin n → ℤˣ => ‖∑ k, ∑ l,
          (if k = l then 0 else c ω k l * ((s k : ℤ) : ℂ) * ((s l : ℤ) : ℂ))‖)
        (fun s => norm_nonneg _) hp1 (by positivity) hσ0 ht0 ?_) (by ring)
      have h1 := hchaos (κ := Fin n) (c ω)
      have hnn : 0 ≤ ∑ k, ∑ l, if k = l then (0 : ℝ) else ‖c ω k l‖ ^ 2 :=
        Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => by split_ifs <;> positivity
      have h2 : (∑ k, ∑ l, if k = l then (0 : ℝ) else ‖c ω k l‖ ^ 2) ^ p ≤ σ ^ (2 * p) := by
        rw [pow_mul]; exact pow_le_pow_left₀ hnn (hcs ω hω) p
      rw [inv_mul_le_iff₀ hcard0] at h1
      calc _ ≤ (Fintype.card (Fin n → ℤˣ) : ℝ) *
            (Cp * (∑ k, ∑ l, if k = l then (0 : ℝ) else ‖c ω k l‖ ^ 2) ^ p) := h1
        _ ≤ (Fintype.card (Fin n → ℤˣ) : ℝ) * (Cp * σ ^ (2 * p)) := by gcongr
        _ = (Fintype.card (Fin n → ℤˣ) : ℝ) * Cp * σ ^ (2 * p) := by ring
    · have hno : ∀ s, T s ω ∉ A := fun s h => hω ((hGoodT s ω).mp h.1)
      simp only [hno, ite_false, Finset.sum_const_zero]
      positivity
  have hAm' : μ n 1 A ≤ ENNReal.ofReal ((n : ℝ) ^ (-(D + 1))) :=
    (isoLaw_avg_le T hT hAm hK).trans
      (ENNReal.ofReal_le_ofReal (isoLaw_chaos_tail hN1 hξ hCp hNC hpD))
  -- inclusion of the bad event
  have hsub : {ω | (n : ℝ) ^ ξ / Real.sqrt (n * η) * Real.sqrt Su * Real.sqrt Sv <
      ‖star u ⬝ᵥ ((G ω - M) *ᵥ v)‖} ⊆ (SE ∪ SO) ∪ A := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, not_or] at hnot
    obtain ⟨⟨hnE, hnO⟩, hnA⟩ := hnot
    have hg : ω ∈ Good :=
      ⟨fun i => not_lt.mp fun h => hnE ⟨i, h⟩,
        fun i j hij => not_lt.mp fun h => hnO ⟨i, j, hij, h⟩⟩
    have hq : ‖Q ω‖ ≤ t * σ := not_lt.mp fun h => hnA ⟨hg, h⟩
    have hbound : ‖star u ⬝ᵥ ((G ω - M) *ᵥ v)‖ ≤ (1 + t) * σ := by
      rw [isoLaw_split hM (G ω) u v]
      calc _ ≤ ‖∑ i, star (u i) * ((G ω i i - M i i) * v i)‖ + ‖Q ω‖ := norm_add_le _ _
        _ ≤ σ + t * σ := add_le_add (hdiag ω hg) hq
        _ = (1 + t) * σ := by ring
    have hrate : (1 + t) * σ ≤ (n : ℝ) ^ ξ / Real.sqrt (n * η) * Real.sqrt Su * Real.sqrt Sv := by
      have h := isoLaw_rate hN1 hξ hN2
      have hr : 0 ≤ Real.sqrt Su * Real.sqrt Sv / Real.sqrt (n * η) := by positivity
      calc (1 + t) * σ = (1 + t) * t * (Real.sqrt Su * Real.sqrt Sv / Real.sqrt (n * η)) := by
            rw [hσ, ha]; ring
        _ ≤ (n : ℝ) ^ ξ * (Real.sqrt Su * Real.sqrt Sv / Real.sqrt (n * η)) :=
            mul_le_mul_of_nonneg_right h hr
        _ = _ := by ring
    exact absurd hω (not_lt.mpr (hbound.trans hrate))
  calc μ n 1 {ω | (n : ℝ) ^ ξ / Real.sqrt (n * η) * Real.sqrt Su * Real.sqrt Sv <
        ‖star u ⬝ᵥ ((G ω - M) *ᵥ v)‖}
      ≤ μ n 1 ((SE ∪ SO) ∪ A) := measure_mono hsub
    _ ≤ μ n 1 SE + μ n 1 SO + μ n 1 A :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal ((n : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((n : ℝ) ^ (-(D + 1))) +
          ENNReal.ofReal ((n : ℝ) ^ (-(D + 1))) := by gcongr
    _ = ENNReal.ofReal (3 * (n : ℝ) ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf
    _ ≤ ENNReal.ofReal ((n : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal (isoLaw_union hN3)

/-! ### The isotropic law -/

/-- Isotropic law of Lemma G.1 [us:lem:local-law], second estimate of (G.1)
[us:eq:weighted-local-law]: for deterministic `u, v`,
`|u^*(G - M_B)v| ≤ n^ξ (nη)^{-1/2} ‖M_B u‖ ‖M_B v‖` with probability `≥ 1 - n^{-D}`. -/
theorem localLaw_iso (κ₀ Cstar : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hC : 0 < Cstar) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε δ ξ D : ℝ, 0 < ε → ε ≤ ε₀ → 0 < δ → 0 < ξ → 0 < D →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (B : Matrix (Fin n) (Fin n) ℂ) (E η : ℝ),
        DeformClass ε B → |E| ≤ 2 - κ₀ → (n : ℝ) ^ (-1 + δ) ≤ η → η ≤ Cstar →
        ∀ u v : Fin n → ℂ,
        μ n 1 {ω | (n : ℝ) ^ ξ / Real.sqrt (n * η) *
              Real.sqrt (∑ k, ‖(MB B (E + η * Complex.I) *ᵥ u) k‖ ^ 2) *
              Real.sqrt (∑ k, ‖(MB B (E + η * Complex.I) *ᵥ v) k‖ ^ 2) <
            ‖star u ⬝ᵥ ((resolventMat (gueMat n ω - B) (E + η * Complex.I) -
              MB B (E + η * Complex.I)) *ᵥ v)‖} ≤
          ENNReal.ofReal ((n : ℝ) ^ (-D)) := by
  obtain ⟨ε₀, hε₀, hcore⟩ := isoLaw_diag κ₀ Cstar hκ₀ hκ₀' hC
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε δ ξ D hε hεε₀ hδ hξ hD
  obtain ⟨n₀, hn₀⟩ := hcore ε δ ξ D hε hεε₀ hδ hξ hD
  refine ⟨max n₀ 1, ?_⟩
  intro n hn B E η hcl hE hηlow hηC u v
  have hn0 : 0 < n := lt_of_lt_of_le one_pos (le_of_max_le_right hn)
  have : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  have hN0 : (0 : ℝ) < n := by exact_mod_cast hn0
  have hη0 : 0 < η := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hηlow
  have hz : 0 < (E + η * Complex.I).im := by simpa using hη0
  have hBh : B.IsHermitian := hcl.1
  set U : Matrix.unitaryGroup (Fin n) ℂ := hBh.eigenvectorUnitary with hU
  set Dg : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (RCLike.ofReal ∘ hBh.eigenvalues) with hDg
  have hspec : B = (U : Matrix (Fin n) (Fin n) ℂ) * Dg * star (U : Matrix (Fin n) (Fin n) ℂ) := by
    have := hBh.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hUU : (U : Matrix (Fin n) (Fin n) ℂ) * star (U : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.2
  have hUU' : star (U : Matrix (Fin n) (Fin n) ℂ) * (U : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.2
  set W : Matrix.unitaryGroup (Fin n) ℂ := U⁻¹ with hW
  have hWv : (W : Matrix (Fin n) (Fin n) ℂ) = star (U : Matrix (Fin n) (Fin n) ℂ) := rfl
  have hDW : Dg = (W : Matrix (Fin n) (Fin n) ℂ) * B * star (W : Matrix (Fin n) (Fin n) ℂ) := by
    rw [hWv, star_star]
    conv_rhs => rw [hspec]
    symm
    calc star (U : Matrix (Fin n) (Fin n) ℂ) * ((U : Matrix (Fin n) (Fin n) ℂ) * Dg *
          star (U : Matrix (Fin n) (Fin n) ℂ)) * (U : Matrix (Fin n) (Fin n) ℂ)
        = (star (U : Matrix (Fin n) (Fin n) ℂ) * U) * Dg *
            (star (U : Matrix (Fin n) (Fin n) ℂ) * U) := by simp only [Matrix.mul_assoc]
      _ = Dg := by rw [hUU', Matrix.one_mul, Matrix.mul_one]
  have hcl' : DeformClass ε Dg := by rw [hDW]; exact isoLaw_deformClass_conj hn0 hcl W
  have hMB : MB B (E + η * Complex.I) = (U : Matrix (Fin n) (Fin n) ℂ) *
      MB Dg (E + η * Complex.I) * star (U : Matrix (Fin n) (Fin n) ℂ) := by
    conv_lhs => rw [hspec]
    exact MB_conj U hcl'.1 hz
  have hG : ∀ ω, resolventMat (gueMat n ω - B) (E + η * Complex.I) =
      (U : Matrix (Fin n) (Fin n) ℂ) *
        resolventMat (gueMat n (conjMap n 1 W ω) - Dg) (E + η * Complex.I) *
          star (U : Matrix (Fin n) (Fin n) ℂ) := by
    intro ω
    have hV : gueMat n (conjMap n 1 W ω) = (W : Matrix (Fin n) (Fin n) ℂ) * gueMat n ω *
        star (W : Matrix (Fin n) (Fin n) ℂ) := gueBlock_conjMap n 1 W ω 0
    have h : gueMat n ω - B = (U : Matrix (Fin n) (Fin n) ℂ) *
        (gueMat n (conjMap n 1 W ω) - Dg) * star (U : Matrix (Fin n) (Fin n) ℂ) := by
      rw [hV, hWv, star_star, Matrix.mul_sub, Matrix.sub_mul, ← hspec]
      congr 1
      calc gueMat n ω = ((U : Matrix (Fin n) (Fin n) ℂ) * star (U : Matrix (Fin n) (Fin n) ℂ)) *
            gueMat n ω *
              ((U : Matrix (Fin n) (Fin n) ℂ) * star (U : Matrix (Fin n) (Fin n) ℂ)) := by
            rw [hUU, Matrix.one_mul, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [h, isoLaw_resolventMat_conj hUU]
  have hnorm : ∀ w : Fin n → ℂ, ∑ k, ‖(MB B (E + η * Complex.I) *ᵥ w) k‖ ^ 2 =
      ∑ k, ‖(MB Dg (E + η * Complex.I) *ᵥ (star (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ w)) k‖ ^ 2 := by
    intro w
    rw [hMB, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, isoLaw_sum_sq_mulVec hUU']
  refine le_trans (measure_mono ?_)
    (le_trans ((measurePreserving_conjMap n 1 W).measure_preimage_le _)
    (hn₀ n (le_of_max_le_left hn) Dg E η hcl' (Matrix.isDiag_diagonal _) hE hηlow hηC
      (star (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ u) (star (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ v)))
  intro ω hω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hω ⊢
  rw [hnorm u, hnorm v, hG ω, hMB, ← Matrix.sub_mul, ← Matrix.mul_sub, isoLaw_dot_conj] at hω
  exact hω

end LSBA
