import LSBA.Upper.CutoffChainTail
import LSBA.Upper.ActiveChainTail
import LSBA.Upper.OverlapWeak
import LSBA.Upper.OutputLower

/-!
# The mass of the cutoff in regime (i)

`𝔼 χ ≥ 1/2` of (9.84)
[su:eq:construction-cutoff-goals], regime (i), at fixed prepared data in `PrepGoodWeak` with
`v_4 ≠ 0`. The plateau of the cutoff with the levels of regime (i) fails only on the union of: the
chain plateau (`C q (W^{-3/2} + g^{1/2})`); the active-chain bound (9.66)
[su:eq:active-chain-inverse] (`C (q - 5)² W^{-1/2}`); the gap level, chosen with failure at most
`1/40`; the rank row (9.53) [su:eq:retained-rank-moment] with Lemma G.2 [us:lem:product]
(`C (W^{-δ₀} + g^{1/2})`); the overlap and compatibility cuts of (9.60) [su:eq:geometry]; and
the output plateau, whose failure on the regular chain has probability `W^{-D}` by (9.68)
[us:eq:profile]. The factor `‖v_4‖² ≤ W^{20} ‖P v_4‖²` holds by (9.5) [su:eq:prep]. Every term is
at most a fixed small constant for `W ≥ W₀`, uniformly in `a`, the energy and the prepared data.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `‖M v‖² ≤ ‖M‖²_HS ‖v‖²` (Cauchy–Schwarz row by row). -/
private lemma CutoffMassWeak_vecSq_mulVec_le {W : ℕ} (M : Matrix (Fin W) (Fin W) ℂ)
    (v : Fin W → ℂ) : ∑ i, ‖(M *ᵥ v) i‖ ^ 2 ≤ hsSq M * ∑ j, ‖v j‖ ^ 2 := by
  unfold hsSq
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ‖(M *ᵥ v) i‖ ^ 2 ≤ (∑ j, ‖M i j‖ * ‖v j‖) ^ 2 := by
        gcongr
        simp only [Matrix.mulVec, dotProduct]
        exact (norm_sum_le _ _).trans (by simp)
    _ ≤ (∑ j, ‖M i j‖ ^ 2) * ∑ j, ‖v j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- The operator norm is at most the Hilbert–Schmidt norm. -/
private lemma CutoffMassWeak_norm_le_sqrt_hsSq {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) :
    ‖A‖ ≤ Real.sqrt (hsSq A) := by
  have h0 : 0 ≤ hsSq A := by unfold hsSq; positivity
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  change ‖Matrix.toEuclideanLin A x‖ ≤ _ * ‖x‖
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_mul h0]
  refine Real.sqrt_le_sqrt ?_
  exact CutoffMassWeak_vecSq_mulVec_le A x.ofLp

/-- `‖M‖²_HS ≤ W ‖M‖²` for the operator norm of a `W × W` matrix. -/
private lemma CutoffMassWeak_hsSq_le {W : ℕ} (M : Matrix (Fin W) (Fin W) ℂ) :
    hsSq M ≤ W * ‖M‖ ^ 2 := by
  unfold hsSq
  rw [Finset.sum_comm]
  have hcol : ∀ b : Fin W, ∑ a, ‖M a b‖ ^ 2 ≤ ‖M‖ ^ 2 := by
    intro b
    have h := Matrix.l2_opNorm_mulVec M (EuclideanSpace.single b (1 : ℂ))
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [mul_pow, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)] at h2
    have h3 : ∑ x : Fin W, ‖(if x = b then (1 : ℂ) else 0)‖ ^ 2 = 1 := by
      rw [Finset.sum_eq_single b] <;> simp (config := {contextual := true})
    simp only [PiLp.ofLp_single, Matrix.mulVec_single, MulOpposite.op_one, one_smul,
      PiLp.continuousLinearEquiv_symm_apply, Matrix.col_apply, PiLp.single_apply] at h2
    rwa [h3, mul_one] at h2
  calc ∑ b, ∑ a, ‖M a b‖ ^ 2 ≤ ∑ _b : Fin W, ‖M‖ ^ 2 := Finset.sum_le_sum fun b _ => hcol b
    _ = _ := by simp

/-- The blocks `V_{j+1}` are Hermitian. -/
private lemma CutoffMassWeak_blockSeq_isHermitian {W q : ℕ} (ω : Ω W q) (j : ℕ) :
    (blockSeq W q ω j).IsHermitian := by
  unfold blockSeq
  split_ifs
  · exact gueBlock_isHermitian W q ω _
  · exact Matrix.isHermitian_zero

/-- For a Hermitian `R_4`, all graph coordinates `R_j` are Hermitian. -/
private lemma CutoffMassWeak_chartR_isHermitian {W q : ℕ} {g E : ℝ}
    {R : Matrix (Fin W) (Fin W) ℂ} (hR : R.IsHermitian) (ω : Ω W q) :
    ∀ j, (chartR W g E q R ω j).IsHermitian
  | 0 => by simpa only [chartR] using hR
  | j + 1 => by
    by_cases h4 : j < 4
    · simpa only [chartR, h4, ↓reduceIte] using hR
    · have hrec : chartR W g E q R ω (j + 1) =
          (blockSeq W q ω j - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • chartR W g E q R ω j)⁻¹ := by
        simp only [chartR, h4, ↓reduceIte]
      rw [hrec]
      have hE : IsSelfAdjoint (E : ℂ) := by rw [isSelfAdjoint_iff]; simp
      have hg : IsSelfAdjoint ((g : ℂ) ^ 2) := by rw [isSelfAdjoint_iff]; simp
      exact (((CutoffMassWeak_blockSeq_isHermitian ω j).sub (Matrix.isHermitian_one.smul hE)).sub
        ((CutoffMassWeak_chartR_isHermitian hR ω j).smul hg)).inv

/-- Eigenvalue counts of `U diag(d) U*` for the eigenvector unitary `U` of a Hermitian `A`. -/
private lemma CutoffMassWeak_countIn_diag {W : ℕ} {A : Matrix (Fin W) (Fin W) ℂ}
    (hA : A.IsHermitian) (d : Fin W → ℝ) {M : Matrix (Fin W) (Fin W) ℂ} (hMH : M.IsHermitian)
    (hM : M = (hA.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ) *
      Matrix.diagonal (fun k => (d k : ℂ)) *
        (hA.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)ᴴ)
    (S : Set ℝ) : countIn M S = #(univ.filter fun k => d k ∈ S) := by
  have hU1 : (hA.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)ᴴ *
      (hA.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  have hcp : M.charpoly = ∏ k, (Polynomial.X - Polynomial.C ((d k : ℂ))) := by
    rw [hM, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU1, Matrix.one_mul,
      Matrix.charpoly_diagonal]
  have hroots : M.charpoly.roots = Multiset.map (fun k => ((d k : ℝ) : ℂ)) Finset.univ.val := by
    rw [hcp, Polynomial.roots_prod]
    · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
    · exact Finset.prod_ne_zero_iff.mpr fun k _ => Polynomial.X_sub_C_ne_zero _
  rw [countIn_eq_card_roots hMH, hroots, Multiset.filter_map]
  simp [Finset.card_def, Finset.filter_val]

/-- For a Hermitian `Y` and `g > 0`: `#{|g² y| > g} ≤ #{eigenvalues of Y* Y above g⁻²}`. -/
private lemma CutoffMassWeak_countIn_le {W : ℕ} {Y : Matrix (Fin W) (Fin W) ℂ}
    (hY : Y.IsHermitian) {g : ℝ} (hg : 0 < g) :
    countIn (((g : ℂ) ^ 2) • Y) {x | g < |x|} ≤ countIn (Yᴴ * Y) (Set.Ioi (g⁻¹ ^ 2)) := by
  set U : Matrix (Fin W) (Fin W) ℂ := (hY.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)
    with hUdef
  have hU1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hY.eigenvectorUnitary.2
  have hspec : Y = U * Matrix.diagonal (fun k => (hY.eigenvalues k : ℂ)) * Uᴴ := by
    have h := hY.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hk : IsSelfAdjoint ((g : ℂ) ^ 2) := by rw [isSelfAdjoint_iff]; simp
  have h1 : ((g : ℂ) ^ 2) • Y =
      U * Matrix.diagonal (fun k => ((g ^ 2 * hY.eigenvalues k : ℝ) : ℂ)) * Uᴴ := by
    have hD : Matrix.diagonal (fun k => ((g ^ 2 * hY.eigenvalues k : ℝ) : ℂ)) =
        ((g : ℂ) ^ 2) • Matrix.diagonal (fun k => (hY.eigenvalues k : ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    conv_lhs => rw [hspec]
    rw [hD, Matrix.mul_smul, Matrix.smul_mul]
  have h2 : Yᴴ * Y = U * Matrix.diagonal (fun k => ((hY.eigenvalues k ^ 2 : ℝ) : ℂ)) * Uᴴ := by
    rw [hY.eq]
    conv_lhs => rw [hspec]
    calc U * Matrix.diagonal (fun k => (hY.eigenvalues k : ℂ)) * Uᴴ *
          (U * Matrix.diagonal (fun k => (hY.eigenvalues k : ℂ)) * Uᴴ)
        = U * (Matrix.diagonal (fun k => (hY.eigenvalues k : ℂ)) * (Uᴴ * U) *
          Matrix.diagonal (fun k => (hY.eigenvalues k : ℂ))) * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          have hd : (fun k => (hY.eigenvalues k : ℂ) * (hY.eigenvalues k : ℂ)) =
              fun k => ((hY.eigenvalues k ^ 2 : ℝ) : ℂ) := by
            funext k
            rw [Complex.ofReal_pow, sq]
          rw [hU1, Matrix.mul_one, Matrix.diagonal_mul_diagonal, hd]
  rw [CutoffMassWeak_countIn_diag hY _ (hY.smul hk) h1,
    CutoffMassWeak_countIn_diag hY _ (Matrix.isHermitian_conjTranspose_mul_self Y) h2]
  refine Finset.card_le_card fun k hk' => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
    Set.mem_Ioi] at hk' ⊢
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < g ^ 2)] at hk'
  have h3 : g * g⁻¹ < g * |hY.eigenvalues k| := by
    rw [mul_inv_cancel₀ hg.ne']
    nlinarith [abs_nonneg (hY.eigenvalues k)]
  have h4 : g⁻¹ < |hY.eigenvalues k| := lt_of_mul_lt_mul_left h3 hg.le
  calc g⁻¹ ^ 2 < |hY.eigenvalues k| ^ 2 := by gcongr
    _ = hY.eigenvalues k ^ 2 := sq_abs _

/-- On `ChainPlat` the states `R_5, …, R_{q-2}` are regular (9.3) [us:eq:regular]. -/
private lemma CutoffMassWeak_regular {W q : ℕ} {g E : ℝ} (hg : 0 < g)
    {R : Matrix (Fin W) (Fin W) ℂ} (hR : R.IsHermitian) {ω : Ω W q}
    (h : ChainPlat W g E q R ω) :
    ∀ j, 5 ≤ j → j ≤ q - 2 → IsRegularState W g (chartR W g E q R ω j) := by
  intro j h5 hj
  obtain ⟨-, hhs, hrk⟩ := h.1 j h5 hj
  have hH := CutoffMassWeak_chartR_isHermitian (g := g) (E := E) hR ω j
  have hW0 : (0 : ℝ) ≤ (W : ℝ) ^ 6 := by positivity
  have hcnt := (countIn_le_rankSurr (chartR W g E q R ω j) (inv_pos.2 hg) two_pos le_rfl).1
  have hcnt0 : (0 : ℝ) ≤ (countIn ((chartR W g E q R ω j)ᴴ * chartR W g E q R ω j)
      (Set.Ioi (g⁻¹ ^ 2)) : ℝ) := Nat.cast_nonneg _
  have hWs : (0 : ℝ) ≤ W * Real.sqrt g := by positivity
  refine ⟨hH, ?_, ?_⟩
  · calc ‖chartR W g E q R ω j‖ ≤ Real.sqrt (hsSq (chartR W g E q R ω j)) :=
          CutoffMassWeak_norm_le_sqrt_hsSq _
      _ ≤ Real.sqrt ((W : ℝ) ^ 6) := Real.sqrt_le_sqrt (by linarith)
      _ = (W : ℝ) ^ 3 := by
          rw [show (W : ℝ) ^ 6 = ((W : ℝ) ^ 3) ^ 2 by ring]
          exact Real.sqrt_sq (by positivity)
  · calc (countIn (((g : ℂ) ^ 2) • chartR W g E q R ω j) {x | g < |x|} : ℝ)
        ≤ countIn ((chartR W g E q R ω j)ᴴ * chartR W g E q R ω j) (Set.Ioi (g⁻¹ ^ 2)) := by
          exact_mod_cast CutoffMassWeak_countIn_le hH hg
      _ ≤ rankSurr g⁻¹ ((chartR W g E q R ω j)ᴴ * chartR W g E q R ω j) := hcnt
      _ ≤ W * Real.sqrt g := by linarith

/-- Six events of probability at most `1/40` cover a set of probability at most `1/4`. -/
private lemma CutoffMassWeak_union6 {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {S A₁ A₂ A₃ A₄ A₅ A₆ : Set X}
    (hS : ∀ x, x ∉ A₁ → x ∉ A₂ → x ∉ A₃ → x ∉ A₄ → x ∉ A₅ → x ∉ A₆ → x ∉ S)
    (h₁ : ν A₁ ≤ ENNReal.ofReal (1 / 40)) (h₂ : ν A₂ ≤ ENNReal.ofReal (1 / 40))
    (h₃ : ν A₃ ≤ ENNReal.ofReal (1 / 40)) (h₄ : ν A₄ ≤ ENNReal.ofReal (1 / 40))
    (h₅ : ν A₅ ≤ ENNReal.ofReal (1 / 40)) (h₆ : ν A₆ ≤ ENNReal.ofReal (1 / 40)) :
    ν S ≤ ENNReal.ofReal (1 / 4) := by
  have hsub : S ⊆ A₁ ∪ A₂ ∪ A₃ ∪ A₄ ∪ A₅ ∪ A₆ := by
    intro x hx
    by_contra h
    simp only [Set.mem_union, not_or] at h
    exact hS x h.1.1.1.1.1 h.1.1.1.1.2 h.1.1.1.2 h.1.1.2 h.1.2 h.2 hx
  calc ν S ≤ ν (A₁ ∪ A₂ ∪ A₃ ∪ A₄ ∪ A₅ ∪ A₆) := measure_mono hsub
    _ ≤ ν A₁ + ν A₂ + ν A₃ + ν A₄ + ν A₅ + ν A₆ := by
        refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
        refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
        refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
        refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (1 / 40) + ENNReal.ofReal (1 / 40) + ENNReal.ofReal (1 / 40) +
          ENNReal.ofReal (1 / 40) + ENNReal.ofReal (1 / 40) + ENNReal.ofReal (1 / 40) := by
        gcongr
    _ = ENNReal.ofReal (6 / 40) := by
        rw [← ENNReal.ofReal_add, ← ENNReal.ofReal_add, ← ENNReal.ofReal_add,
          ← ENNReal.ofReal_add, ← ENNReal.ofReal_add] <;> norm_num
    _ ≤ ENNReal.ofReal (1 / 4) := ENNReal.ofReal_le_ofReal (by norm_num)

/-- The real and the complex scalar multiples `(g² : ℝ) • R` and `(g : ℂ)² • R` agree. -/
private lemma CutoffMassWeak_smul_eq {W : ℕ} (g : ℝ) (R : Matrix (Fin W) (Fin W) ℂ) :
    ((g ^ 2 : ℝ) • R) = ((g : ℂ) ^ 2) • R := by
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul]

/-- The source conditions of the plateau at prepared data in `PrepGoodWeak` with `v ≠ 0`
(9.5) [su:eq:prep]: `P v ≠ 0` and `‖v‖² ≤ W^{20} ‖P v‖²`. -/
private lemma CutoffMassWeak_source {W : ℕ} (hW : 1 ≤ W) {g ε Cp : ℝ}
    {R : Matrix (Fin W) (Fin W) ℂ} {v : Fin W → ℂ} (h : (R, v) ∈ PrepGoodWeak W g ε Cp)
    (hv : v ≠ 0) :
    specProj ((g ^ 2 : ℝ) • R) (Set.Icc (-(W : ℝ) ^ (ε / 800)) ((W : ℝ) ^ (ε / 800))) *ᵥ v ≠ 0 ∧
    ∑ i, ‖v i‖ ^ 2 ≤ (W : ℝ) ^ 20 * ∑ i, ‖(specProj ((g ^ 2 : ℝ) • R)
      (Set.Icc (-(W : ℝ) ^ (ε / 800)) ((W : ℝ) ^ (ε / 800))) *ᵥ v) i‖ ^ 2 := by
  have h2 := h.2.1
  rw [← CutoffMassWeak_smul_eq] at h2
  set P := specProj ((g ^ 2 : ℝ) • R) (Set.Icc (-(W : ℝ) ^ (ε / 800)) ((W : ℝ) ^ (ε / 800)))
    with hP
  have h2' : (W : ℝ) ^ (-10 : ℝ) * l2Norm v ≤ l2Norm (P *ᵥ v) := h2
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hs : (W : ℝ) ^ (10 : ℕ) * (W : ℝ) ^ (-10 : ℝ) = 1 := by
    have e : (W : ℝ) ^ (10 : ℝ) = (W : ℝ) ^ (10 : ℕ) := by
      exact_mod_cast Real.rpow_natCast (W : ℝ) 10
    rw [Real.rpow_neg hW0.le, e]
    exact mul_inv_cancel₀ (by positivity)
  have hs0 : 0 < (W : ℝ) ^ (-10 : ℝ) := Real.rpow_pos_of_pos hW0 _
  have hv0 : 0 < ∑ i, ‖v i‖ ^ 2 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
    have hj' : 0 < ‖v j‖ ^ 2 := by
      have : v j ≠ 0 := hj
      positivity
    exact lt_of_lt_of_le hj' (Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2)
      (fun i _ => by positivity) (Finset.mem_univ j))
  have h3 : ((W : ℝ) ^ (-10 : ℝ)) ^ 2 * ∑ i, ‖v i‖ ^ 2 ≤ ∑ i, ‖(P *ᵥ v) i‖ ^ 2 := by
    have := pow_le_pow_left₀ (mul_nonneg hs0.le (Real.sqrt_nonneg _)) h2' 2
    unfold l2Norm at this
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at this
    exact this
  refine ⟨fun hPv => ?_, ?_⟩
  · have h0 : ∑ i, ‖(P *ᵥ v) i‖ ^ 2 = 0 := by simp [hPv]
    linarith [mul_pos (pow_pos hs0 2) hv0]
  · calc ∑ i, ‖v i‖ ^ 2
        = ((W : ℝ) ^ (10 : ℕ) * (W : ℝ) ^ (-10 : ℝ)) ^ 2 * ∑ i, ‖v i‖ ^ 2 := by
          rw [hs]; ring
      _ = ((W : ℝ) ^ 10) ^ 2 * (((W : ℝ) ^ (-10 : ℝ)) ^ 2 * ∑ i, ‖v i‖ ^ 2) := by ring
      _ ≤ ((W : ℝ) ^ 10) ^ 2 * ∑ i, ‖(P *ᵥ v) i‖ ^ 2 := by gcongr
      _ = (W : ℝ) ^ 20 * ∑ i, ‖(P *ᵥ v) i‖ ^ 2 := by ring

/-- `√(W^{-a}) ≤ W^{-α/2}` for `α ≤ a` and `W ≥ 1`. -/
private lemma CutoffMassWeak_sqrt_le {W : ℕ} (hW : 1 ≤ W) {α a : ℝ} (ha : α ≤ a) :
    Real.sqrt ((W : ℝ) ^ (-a)) ≤ (W : ℝ) ^ (-(α / 2)) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)

/-- For `α, δ₀, g₀ > 0` and constants `K₁, K₂, K₃`, the rows `K₁ (W^{-3/2} + W^{-α/2}) ≤ 1/40`,
`K₂ W^{-1/2} ≤ 1/40`, `W^{-α} ≤ g₀` and `K₃ (W^{-δ₀} + W^{-α/2}) ≤ 1/40` hold, with `40 ≤ W`, for
all large `W`. -/
private lemma CutoffMassWeak_eventually {α δ₀ g₀ : ℝ} (hα : 0 < α) (hδ₀ : 0 < δ₀) (hg₀ : 0 < g₀)
    (K₁ K₂ K₃ : ℝ) :
    ∃ N : ℕ, ∀ W : ℕ, N ≤ W → 40 ≤ W ∧
      K₁ * ((W : ℝ) ^ (-(3 / 2 : ℝ)) + (W : ℝ) ^ (-(α / 2))) ≤ 1 / 40 ∧
      K₂ * (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 / 40 ∧ (W : ℝ) ^ (-α) ≤ g₀ ∧
      K₃ * ((W : ℝ) ^ (-δ₀) + (W : ℝ) ^ (-(α / 2))) ≤ 1 / 40 := by
  have t : ∀ c : ℝ, 0 < c → Filter.Tendsto (fun W : ℕ => (W : ℝ) ^ (-c)) Filter.atTop (nhds 0) :=
    fun c hc => (tendsto_rpow_neg_atTop hc).comp tendsto_natCast_atTop_atTop
  have e1 : ∀ᶠ W : ℕ in Filter.atTop, K₁ * ((W : ℝ) ^ (-(3 / 2 : ℝ)) + (W : ℝ) ^ (-(α / 2))) ≤
      1 / 40 := by
    have := (((t (3 / 2) (by norm_num)).add (t (α / 2) (by positivity))).const_mul K₁)
    exact this.eventually (ge_mem_nhds (by simp))
  have e2 : ∀ᶠ W : ℕ in Filter.atTop, K₂ * (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 / 40 := by
    have := (t (1 / 2) (by norm_num)).const_mul K₂
    exact this.eventually (ge_mem_nhds (by simp))
  have e3 : ∀ᶠ W : ℕ in Filter.atTop, (W : ℝ) ^ (-α) ≤ g₀ :=
    (t α hα).eventually (ge_mem_nhds hg₀)
  have e4 : ∀ᶠ W : ℕ in Filter.atTop, K₃ * ((W : ℝ) ^ (-δ₀) + (W : ℝ) ^ (-(α / 2))) ≤ 1 / 40 := by
    have := (((t δ₀ hδ₀).add (t (α / 2) (by positivity))).const_mul K₃)
    exact this.eventually (ge_mem_nhds (by simp))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((Filter.eventually_ge_atTop 40).and (e1.and (e2.and (e3.and e4))))
  exact ⟨N, fun W hW => by
    obtain ⟨a, b, c, d, e⟩ := hN W hW
    exact ⟨a, b, c, d, e⟩⟩

/-- Regime (i): for a gap level `L` whose gap event fails with probability at most `1/40`, the
plateau `CutPlat` with the levels of regime (i) fails with probability at most `1/4`. -/
theorem cutPlat_weak (κ₀ α β ε Cp : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hα : 0 < α)
    (hαβ : α < β) (hβ : β < 1 / 2) (hε : 0 < ε) (hε1 : ε ≤ 1) (hεα : ε ≤ 100 * α)
    (hCp : 0 < Cp) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ a ∈ Set.Icc α β, ∀ E : ℝ, |E| ≤ 2 - κ₀ → ∀ L : ℝ, 0 < L →
      μ W (qWeak β ε) {ω | ¬ (IsUnit ((cavProd W ((W : ℝ) ^ (-a)) E (qWeak β ε) ω
          (qWeak β ε - 6))ᴴ * cavProd W ((W : ℝ) ^ (-a)) E (qWeak β ε) ω (qWeak β ε - 6) -
          ((((levelsWeak W ((W : ℝ) ^ (-a)) α β ε L).t) ^ 2 : ℝ) : ℂ) • 1) ∧
        hsSq ((cavProd W ((W : ℝ) ^ (-a)) E (qWeak β ε) ω (qWeak β ε - 6))ᴴ *
          cavProd W ((W : ℝ) ^ (-a)) E (qWeak β ε) ω (qWeak β ε - 6) -
          ((((levelsWeak W ((W : ℝ) ^ (-a)) α β ε L).t) ^ 2 : ℝ) : ℂ) • 1)⁻¹ ≤ L)} ≤
        ENNReal.ofReal (1 / 40) →
      ∀ (R : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ),
        (R, v) ∈ PrepGoodWeak W ((W : ℝ) ^ (-a)) ε Cp → v ≠ 0 →
        μ W (qWeak β ε) {ω | ¬ CutPlat W ((W : ℝ) ^ (-a)) E (qWeak β ε) R
            (specProj ((((W : ℝ) ^ (-a)) ^ 2 : ℝ) • R)
              (Set.Icc (-(W : ℝ) ^ (ε / 800)) ((W : ℝ) ^ (ε / 800))))
            (levelsWeak W ((W : ℝ) ^ (-a)) α β ε L) ω v} ≤ ENNReal.ofReal (1 / 4) := by
  obtain ⟨hq7, hp0, hpq, -⟩ := levels_weak α β ε hα hαβ hβ hε hε1 hεα
  obtain ⟨C₁, hC₁, H₁⟩ := chainPlat_tail
  obtain ⟨C₂, hC₂, H₂⟩ := activeMat_inv_tail
  obtain ⟨g₀, δ₀, C₃, hg₀, hδ₀, hC₃, W₃, H₃⟩ := cavRank_tail κ₀ hκ₀ hκ₀' (qWeak β ε) hq7
    (pWeak β ε) (ε / 3200) hp0 hpq (by positivity)
  obtain ⟨W₄, H₄⟩ := overlap_weak κ₀ α β ε Cp hκ₀ hκ₀' hα hαβ hβ hε hε1 hεα hCp (1 / 40)
    (by norm_num)
  obtain ⟨W₅, H₅⟩ := output_lower_weak κ₀ α β ε Cp hκ₀ hκ₀' hα hαβ hβ hε hε1 hCp 1 one_pos
  obtain ⟨N, hN⟩ := CutoffMassWeak_eventually hα hδ₀ hg₀ (C₁ * (qWeak β ε : ℝ))
    (C₂ * ((qWeak β ε : ℝ) - 5) ^ 2) C₃
  refine ⟨max (max N W₃) (max W₄ W₅), fun W hW a ha E hE L hL hgap R v hRv hv => ?_⟩
  obtain ⟨hWN, hWW₃, hWW₄, hWW₅⟩ : N ≤ W ∧ W₃ ≤ W ∧ W₄ ≤ W ∧ W₅ ≤ W := by
    simp only [max_le_iff] at hW
    exact ⟨hW.1.1, hW.1.2, hW.2.1, hW.2.2⟩
  obtain ⟨hW40, r1, r2, r3, r4⟩ := hN W hWN
  have hW1 : 1 ≤ W := by omega
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hg0 : 0 < (W : ℝ) ^ (-a) := Real.rpow_pos_of_pos (by linarith) _
  have hg1 : (W : ℝ) ^ (-a) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hWr (by linarith [ha.1, hα])
  have hgα : (W : ℝ) ^ (-a) ≤ (W : ℝ) ^ (-α) :=
    Real.rpow_le_rpow_of_exponent_le hWr (by linarith [ha.1])
  have hsq : Real.sqrt ((W : ℝ) ^ (-a)) ≤ (W : ℝ) ^ (-(α / 2)) :=
    CutoffMassWeak_sqrt_le hW1 ha.1
  have hRreg : IsRegularState W ((W : ℝ) ^ (-a)) R := hRv.1
  obtain ⟨hRH, hRn, -⟩ := hRreg
  have hRs : ((W : ℝ) ^ (-a)) ^ 4 * hsSq R ≤ (W : ℝ) ^ 7 := by
    have h0 : 0 ≤ hsSq R := by unfold hsSq; positivity
    have h4 : ((W : ℝ) ^ (-a)) ^ 4 ≤ 1 := pow_le_one₀ hg0.le hg1
    calc ((W : ℝ) ^ (-a)) ^ 4 * hsSq R ≤ 1 * hsSq R := by gcongr
      _ = hsSq R := one_mul _
      _ ≤ W * ‖R‖ ^ 2 := CutoffMassWeak_hsSq_le R
      _ ≤ W * ((W : ℝ) ^ 3) ^ 2 := by gcongr
      _ = (W : ℝ) ^ 7 := by ring
  have hq5 : 6 ≤ qWeak β ε := by omega
  -- the six events
  have h1 := (H₁ W (qWeak β ε) ((W : ℝ) ^ (-a)) E R (by omega) hq7 hg0 hg1 hRH hRs).trans
    (ENNReal.ofReal_le_ofReal (by
      calc C₁ * (qWeak β ε : ℝ) * ((W : ℝ) ^ (-(3 / 2 : ℝ)) + Real.sqrt ((W : ℝ) ^ (-a)))
          ≤ C₁ * (qWeak β ε : ℝ) * ((W : ℝ) ^ (-(3 / 2 : ℝ)) + (W : ℝ) ^ (-(α / 2))) := by
            gcongr
        _ ≤ 1 / 40 := r1))
  have h2 := (H₂ W (qWeak β ε) ((W : ℝ) ^ (-a)) E R hW1 hq5 hRH).trans
    (ENNReal.ofReal_le_ofReal r2)
  have ht : 0 < (W : ℝ) ^ (-40 : ℝ) * (((W : ℝ) ^ (-a)) ^ qWeak β ε)⁻¹ := by positivity
  have h4 := (H₃ W hWW₃ ((W : ℝ) ^ (-a)) E
      ((W : ℝ) ^ (-40 : ℝ) * (((W : ℝ) ^ (-a)) ^ qWeak β ε)⁻¹) hg0 (hgα.trans r3) hE ht).trans
    (ENNReal.ofReal_le_ofReal (by
      calc C₃ * ((W : ℝ) ^ (-δ₀) + Real.sqrt ((W : ℝ) ^ (-a)))
          ≤ C₃ * ((W : ℝ) ^ (-δ₀) + (W : ℝ) ^ (-(α / 2))) := by gcongr
        _ ≤ 1 / 40 := r4))
  have h5 := H₄ W hWW₄ a ha E hE R v hRv
  have h6 := (H₅ W hWW₅ a ha E hE R v hRv).trans
    (ENNReal.ofReal_le_ofReal (show (W : ℝ) ^ (-(1 : ℝ)) ≤ 1 / 40 by
      rw [Real.rpow_neg_one]
      have h40 : (40 : ℝ) ≤ W := by exact_mod_cast hW40
      calc (W : ℝ)⁻¹ ≤ (40 : ℝ)⁻¹ := by gcongr
        _ = 1 / 40 := by norm_num))
  obtain ⟨hPv, hvn⟩ := CutoffMassWeak_source hW1 hRv hv
  refine CutoffMassWeak_union6 ?_ h1 h2 hgap h4 h5 h6
  intro ω n1 n2 n3 n4 n5 n6 hcon
  have c1 : ChainPlat W ((W : ℝ) ^ (-a)) E (qWeak β ε) R ω := not_not.mp n1
  have c2 := not_not.mp n2
  have c3 := not_not.mp n3
  have c4 := not_lt.mp (Set.notMem_ofPred_iff.mp n4)
  obtain ⟨hov, hQP, hcomp⟩ := not_not.mp n5
  have hreg := CutoffMassWeak_regular hg0 hRH c1
  have hout := not_lt.mp fun hlt => n6 ⟨hreg, hlt⟩
  exact hcon ⟨c1, c2, c3, c4, hcomp, hPv, hvn, hov, hQP, hout⟩

end LSBA
