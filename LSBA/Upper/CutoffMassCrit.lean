import LSBA.Upper.CutoffChainTail
import LSBA.Upper.ActiveChainTail
import LSBA.Upper.OverlapCrit
import LSBA.Upper.OutputLower

/-!
# The mass of the cutoff in regime (ii)

`𝔼 χ ≥ 1/2` of (9.84)
[su:eq:construction-cutoff-goals], regime (ii), where `P = 1`, at fixed prepared data in
`PrepGoodCrit` with `v_4 ≠ 0`. The plateau of the cutoff with the levels of regime (ii) fails
only on the union of: the chain plateau; the active-chain bound (9.66)
[su:eq:active-chain-inverse]; the gap level, chosen with failure at most `1/40`; the rank row
(9.53) [su:eq:retained-rank-moment] with Lemma G.2 [us:lem:product]; the overlap cut of (9.64)
[nc:eq:geometry], which also gives the `Q v_4` cut since `W^{-1+14θ} ≤ 1/16`; and the output
plateau, whose failure on the regular chain has probability `W^{-D}` by Lemma G.3
[nc:lem:buffer]. The compatibility cut is automatic since `1 - P = 0`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `‖M v‖² ≤ ‖M‖²_HS ‖v‖²` (Cauchy–Schwarz row by row). -/
private lemma CutoffMassCrit_vecSq_mulVec_le {W : ℕ} (M : Matrix (Fin W) (Fin W) ℂ)
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
private lemma CutoffMassCrit_norm_le_sqrt_hsSq {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) :
    ‖A‖ ≤ Real.sqrt (hsSq A) := by
  have h0 : 0 ≤ hsSq A := by unfold hsSq; positivity
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  change ‖Matrix.toEuclideanLin A x‖ ≤ _ * ‖x‖
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_mul h0]
  refine Real.sqrt_le_sqrt ?_
  exact CutoffMassCrit_vecSq_mulVec_le A x.ofLp

/-- `‖M‖²_HS ≤ W ‖M‖²` for the operator norm of a `W × W` matrix. -/
private lemma CutoffMassCrit_hsSq_le {W : ℕ} (M : Matrix (Fin W) (Fin W) ℂ) :
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
private lemma CutoffMassCrit_blockSeq_isHermitian {W q : ℕ} (ω : Ω W q) (j : ℕ) :
    (blockSeq W q ω j).IsHermitian := by
  unfold blockSeq
  split_ifs
  · exact gueBlock_isHermitian W q ω _
  · exact Matrix.isHermitian_zero

/-- For a Hermitian `R_4`, all graph coordinates `R_j` are Hermitian. -/
private lemma CutoffMassCrit_chartR_isHermitian {W q : ℕ} {g E : ℝ}
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
      exact (((CutoffMassCrit_blockSeq_isHermitian ω j).sub (Matrix.isHermitian_one.smul hE)).sub
        ((CutoffMassCrit_chartR_isHermitian hR ω j).smul hg)).inv

/-- Eigenvalue counts of `U diag(d) U*` for the eigenvector unitary `U` of a Hermitian `A`. -/
private lemma CutoffMassCrit_countIn_diag {W : ℕ} {A : Matrix (Fin W) (Fin W) ℂ}
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
private lemma CutoffMassCrit_countIn_le {W : ℕ} {Y : Matrix (Fin W) (Fin W) ℂ}
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
  rw [CutoffMassCrit_countIn_diag hY _ (hY.smul hk) h1,
    CutoffMassCrit_countIn_diag hY _ (Matrix.isHermitian_conjTranspose_mul_self Y) h2]
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
private lemma CutoffMassCrit_regular {W q : ℕ} {g E : ℝ} (hg : 0 < g)
    {R : Matrix (Fin W) (Fin W) ℂ} (hR : R.IsHermitian) {ω : Ω W q}
    (h : ChainPlat W g E q R ω) :
    ∀ j, 5 ≤ j → j ≤ q - 2 → IsRegularState W g (chartR W g E q R ω j) := by
  intro j h5 hj
  obtain ⟨-, hhs, hrk⟩ := h.1 j h5 hj
  have hH := CutoffMassCrit_chartR_isHermitian (g := g) (E := E) hR ω j
  have hW0 : (0 : ℝ) ≤ (W : ℝ) ^ 6 := by positivity
  have hcnt := (countIn_le_rankSurr (chartR W g E q R ω j) (inv_pos.2 hg) two_pos le_rfl).1
  have hcnt0 : (0 : ℝ) ≤ (countIn ((chartR W g E q R ω j)ᴴ * chartR W g E q R ω j)
      (Set.Ioi (g⁻¹ ^ 2)) : ℝ) := Nat.cast_nonneg _
  have hWs : (0 : ℝ) ≤ W * Real.sqrt g := by positivity
  refine ⟨hH, ?_, ?_⟩
  · calc ‖chartR W g E q R ω j‖ ≤ Real.sqrt (hsSq (chartR W g E q R ω j)) :=
          CutoffMassCrit_norm_le_sqrt_hsSq _
      _ ≤ Real.sqrt ((W : ℝ) ^ 6) := Real.sqrt_le_sqrt (by linarith)
      _ = (W : ℝ) ^ 3 := by
          rw [show (W : ℝ) ^ 6 = ((W : ℝ) ^ 3) ^ 2 by ring]
          exact Real.sqrt_sq (by positivity)
  · calc (countIn (((g : ℂ) ^ 2) • chartR W g E q R ω j) {x | g < |x|} : ℝ)
        ≤ countIn ((chartR W g E q R ω j)ᴴ * chartR W g E q R ω j) (Set.Ioi (g⁻¹ ^ 2)) := by
          exact_mod_cast CutoffMassCrit_countIn_le hH hg
      _ ≤ rankSurr g⁻¹ ((chartR W g E q R ω j)ᴴ * chartR W g E q R ω j) := hcnt
      _ ≤ W * Real.sqrt g := by linarith

/-- Six events of probability at most `1/40` cover a set of probability at most `1/4`. -/
private lemma CutoffMassCrit_union6 {X : Type*} [MeasurableSpace X] {ν : Measure X}
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

/-- `√g ≤ W^{-(α/2)}` for `g ≤ W^{-α}` and `W ≥ 1`. -/
private lemma CutoffMassCrit_sqrt_le {W : ℕ} (hW : 1 ≤ W) {α g : ℝ}
    (hg : g ≤ (W : ℝ) ^ (-α)) : Real.sqrt g ≤ (W : ℝ) ^ (-(α / 2)) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  calc Real.sqrt g ≤ Real.sqrt ((W : ℝ) ^ (-α)) := Real.sqrt_le_sqrt hg
    _ = (W : ℝ) ^ (-(α / 2)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith)]
        congr 1
        ring

/-- For `α, δ₀, g₀ > 0` and constants `K₁, K₂, K₃`, the rows `K₁ (W^{-3/2} + W^{-α/2}) ≤ 1/40`,
`K₂ W^{-1/2} ≤ 1/40`, `W^{-α} ≤ g₀`, `K₃ (W^{-δ₀} + W^{-α/2}) ≤ 1/40` and `W^{-1/2} ≤ 1/16` hold,
with `40 ≤ W`, for all large `W`. -/
private lemma CutoffMassCrit_eventually {α δ₀ g₀ : ℝ} (hα : 0 < α) (hδ₀ : 0 < δ₀) (hg₀ : 0 < g₀)
    (K₁ K₂ K₃ : ℝ) :
    ∃ N : ℕ, ∀ W : ℕ, N ≤ W → 40 ≤ W ∧
      K₁ * ((W : ℝ) ^ (-(3 / 2 : ℝ)) + (W : ℝ) ^ (-(α / 2))) ≤ 1 / 40 ∧
      K₂ * (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 / 40 ∧ (W : ℝ) ^ (-α) ≤ g₀ ∧
      K₃ * ((W : ℝ) ^ (-δ₀) + (W : ℝ) ^ (-(α / 2))) ≤ 1 / 40 ∧
      (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 / 16 := by
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
  have e5 : ∀ᶠ W : ℕ in Filter.atTop, (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 / 16 :=
    (t (1 / 2) (by norm_num)).eventually (ge_mem_nhds (by norm_num))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((Filter.eventually_ge_atTop 40).and (e1.and (e2.and (e3.and (e4.and e5)))))
  exact ⟨N, fun W hW => by
    obtain ⟨a, b, c, d, e, f⟩ := hN W hW
    exact ⟨a, b, c, d, e, f⟩⟩

/-- Regime (ii): for a gap level `L` whose gap event fails with probability at most `1/40`, the
plateau `CutPlat` with `P = 1` and the levels of regime (ii) fails with probability at most
`1/4`. -/
theorem cutPlat_crit (κ₀ θ : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hθ : 0 < θ)
    (hθ' : θ ≤ 1 / 100) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, 0 < g → g ≤ (W : ℝ) ^ (-(1 / 2 : ℝ) + θ / 2) →
      ∀ E : ℝ, |E| ≤ 2 - κ₀ → ∀ L : ℝ, 0 < L →
      μ W (qCrit θ) {ω | ¬ (IsUnit ((cavProd W g E (qCrit θ) ω (qCrit θ - 6))ᴴ *
          cavProd W g E (qCrit θ) ω (qCrit θ - 6) - ((((levelsCrit W θ L).t) ^ 2 : ℝ) : ℂ) • 1) ∧
        hsSq ((cavProd W g E (qCrit θ) ω (qCrit θ - 6))ᴴ *
          cavProd W g E (qCrit θ) ω (qCrit θ - 6) -
          ((((levelsCrit W θ L).t) ^ 2 : ℝ) : ℂ) • 1)⁻¹ ≤ L)} ≤ ENNReal.ofReal (1 / 40) →
      ∀ (R : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ), (R, v) ∈ PrepGoodCrit W g θ → v ≠ 0 →
        μ W (qCrit θ) {ω | ¬ CutPlat W g E (qCrit θ) R 1 (levelsCrit W θ L) ω v} ≤
          ENNReal.ofReal (1 / 4) := by
  obtain ⟨hq7, hp0, hpq, -⟩ := levels_crit θ 1 hθ hθ' one_pos
  obtain ⟨C₁, hC₁, H₁⟩ := chainPlat_tail
  obtain ⟨C₂, hC₂, H₂⟩ := activeMat_inv_tail
  obtain ⟨g₀, δ₀, C₃, hg₀, hδ₀, hC₃, W₃, H₃⟩ := cavRank_tail κ₀ hκ₀ hκ₀' (qCrit θ) hq7
    (pCrit θ) (θ / 4) hp0 hpq (by positivity)
  obtain ⟨W₄, H₄⟩ := overlap_crit κ₀ θ hκ₀ hκ₀' hθ hθ' (1 / 40) (by norm_num)
  obtain ⟨W₅, H₅⟩ := output_lower_crit κ₀ θ hκ₀ hκ₀' hθ hθ' 1 one_pos
  have hα : 0 < 1 / 2 - θ / 2 := by linarith
  obtain ⟨N, hN⟩ := CutoffMassCrit_eventually hα hδ₀ hg₀ (C₁ * (qCrit θ : ℝ))
    (C₂ * ((qCrit θ : ℝ) - 5) ^ 2) C₃
  refine ⟨max (max N W₃) (max W₄ W₅), fun W hW g hg0 hgW E hE L hL hgap R v hRv hv => ?_⟩
  obtain ⟨hWN, hWW₃, hWW₄, hWW₅⟩ : N ≤ W ∧ W₃ ≤ W ∧ W₄ ≤ W ∧ W₅ ≤ W := by
    simp only [max_le_iff] at hW
    exact ⟨hW.1.1, hW.1.2, hW.2.1, hW.2.2⟩
  obtain ⟨hW40, r1, r2, r3, r4, r5⟩ := hN W hWN
  have hW1 : 1 ≤ W := by omega
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hgα : g ≤ (W : ℝ) ^ (-(1 / 2 - θ / 2)) := by
    have e : -(1 / 2 : ℝ) + θ / 2 = -(1 / 2 - θ / 2) := by ring
    rwa [e] at hgW
  have hg1 : g ≤ 1 :=
    hgα.trans (Real.rpow_le_one_of_one_le_of_nonpos hWr (by linarith))
  have hsq : Real.sqrt g ≤ (W : ℝ) ^ (-((1 / 2 - θ / 2) / 2)) :=
    CutoffMassCrit_sqrt_le hW1 hgα
  have hRreg : IsRegularState W g R := hRv.1
  obtain ⟨hRH, hRn, -⟩ := hRreg
  have hRs : g ^ 4 * hsSq R ≤ (W : ℝ) ^ 7 := by
    have h0 : 0 ≤ hsSq R := by unfold hsSq; positivity
    have h4 : g ^ 4 ≤ 1 := pow_le_one₀ hg0.le hg1
    calc g ^ 4 * hsSq R ≤ 1 * hsSq R := by gcongr
      _ = hsSq R := one_mul _
      _ ≤ W * ‖R‖ ^ 2 := CutoffMassCrit_hsSq_le R
      _ ≤ W * ((W : ℝ) ^ 3) ^ 2 := by gcongr
      _ = (W : ℝ) ^ 7 := by ring
  have hq5 : 6 ≤ qCrit θ := by omega
  -- the six events
  have h1 := (H₁ W (qCrit θ) g E R (by omega) hq7 hg0 hg1 hRH hRs).trans
    (ENNReal.ofReal_le_ofReal (by
      calc C₁ * (qCrit θ : ℝ) * ((W : ℝ) ^ (-(3 / 2 : ℝ)) + Real.sqrt g)
          ≤ C₁ * (qCrit θ : ℝ) *
            ((W : ℝ) ^ (-(3 / 2 : ℝ)) + (W : ℝ) ^ (-((1 / 2 - θ / 2) / 2))) := by
            gcongr
        _ ≤ 1 / 40 := r1))
  have h2 := (H₂ W (qCrit θ) g E R hW1 hq5 hRH).trans (ENNReal.ofReal_le_ofReal r2)
  have ht : 0 < (levelsCrit W θ L).t := Real.rpow_pos_of_pos (by linarith) _
  have h4 := (H₃ W hWW₃ g E (levelsCrit W θ L).t hg0 (hgα.trans r3) hE ht).trans
    (ENNReal.ofReal_le_ofReal (by
      calc C₃ * ((W : ℝ) ^ (-δ₀) + Real.sqrt g)
          ≤ C₃ * ((W : ℝ) ^ (-δ₀) + (W : ℝ) ^ (-((1 / 2 - θ / 2) / 2))) := by gcongr
        _ ≤ 1 / 40 := r4))
  have h5 := H₄ W hWW₄ g hg0 hgW E hE R v hRv
  have h6 := (H₅ W hWW₅ g hg0 hgW E hE R v hRv).trans
    (ENNReal.ofReal_le_ofReal (show (W : ℝ) ^ (-(1 : ℝ)) ≤ 1 / 40 by
      rw [Real.rpow_neg_one]
      have h40 : (40 : ℝ) ≤ W := by exact_mod_cast hW40
      calc (W : ℝ)⁻¹ ≤ (40 : ℝ)⁻¹ := by gcongr
        _ = 1 / 40 := by norm_num))
  -- the overlap level is at most `1/16`
  have hLov : 16 * (levelsCrit W θ L).Lov ≤ 1 := by
    have h : (levelsCrit W θ L).Lov ≤ (W : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hWr (by linarith)
    linarith
  refine CutoffMassCrit_union6 ?_ h1 h2 hgap h4 h5 h6
  intro ω n1 n2 n3 n4 n5 n6 hcon
  have c1 : ChainPlat W g E (qCrit θ) R ω := not_not.mp n1
  have c2 := not_not.mp n2
  have c3 := not_not.mp n3
  have c4 := not_lt.mp (Set.notMem_ofPred_iff.mp n4)
  have c5 := not_not.mp n5
  have hreg := CutoffMassCrit_regular hg0 hRH c1
  have hout := not_lt.mp fun hlt => n6 ⟨hreg, hlt⟩
  have hV0 : 0 ≤ ∑ i, ‖v i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have hcomp : 2 * 8 ^ (levelsCrit W θ L).kP *
      ((retProj W g E (qCrit θ) R (levelsCrit W θ L).t ω * (1 - 1) *
        retProj W g E (qCrit θ) R (levelsCrit W θ L).t ω) ^
        (levelsCrit W θ L).kP).trace.re ≤ 1 := by
    simp [levelsCrit]
  refine hcon ⟨c1, c2, c3, c4, hcomp, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.one_mulVec]
    exact hv
  · simp only [Matrix.one_mulVec]
    exact le_mul_of_one_le_left hV0 (one_le_pow₀ hWr)
  · simp only [Matrix.one_mulVec]
    exact c5
  · simp only [Matrix.one_mulVec]
    calc 16 * ∑ i, ‖(retProj W g E (qCrit θ) R (levelsCrit W θ L).t ω *ᵥ v) i‖ ^ 2
        ≤ 16 * ((levelsCrit W θ L).Lov * ∑ i, ‖v i‖ ^ 2) :=
          mul_le_mul_of_nonneg_left c5 (by norm_num)
      _ = (16 * (levelsCrit W θ L).Lov) * ∑ i, ‖v i‖ ^ 2 := by ring
      _ ≤ 1 * ∑ i, ‖v i‖ ^ 2 := by gcongr
      _ = ∑ i, ‖v i‖ ^ 2 := one_mul _
  · simp only [Matrix.one_mulVec]
    exact hout

end LSBA
