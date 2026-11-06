import LSBA.Upper.SrcCutoff
import LSBA.Upper.GenDeriv
import LSBA.Upper.AllowBound
import LSBA.Upper.ChosenGenerator

/-!
# The pointwise clauses of Lemma 9.3 [su:lem:chosen-generator] on the support of the cutoff

Section 9.4.2 [su:sec:error-derivative-estimates] and the proof of Lemma 9.3
[su:lem:chosen-generator] (Section 9.4 [su:sec:construction-estimates]). On `CutSupp`: `B_Q ≥ 3/4`
on `ran Q` from the common
conclusion of Section 9.4.1 [su:sec:retained-geometry] with `‖(1 - P) Q‖² ≤ 1/8` and
`‖P v‖⁻² ‖Q P v‖² ≤ 1/8`; `‖y‖ ≤ ‖v‖` from `‖y‖ ≤ (4/3) ‖Q v‖`; the active-chain bound (9.66)
[su:eq:active-chain-inverse] through the Schur identities; the matching error (9.70)
[su:eq:error], `‖A_< R̃‖ ≤ t ‖R̃‖`, at the output scale; hence (9.19)
[su:eq:generator-admissibility], (9.20) [us:eq:sourceenergy], (9.21)
[su:eq:normalized-generator-costs], and the smoothness set of the construction. With the
derivative bounds (9.78) [su:eq:construction-derivative-goals], the output ratio (9.72)
[su:eq:output-derivative-ratio] and the rank surrogate, the pointwise clauses `GenPoint` of
Lemma 9.3 [su:lem:chosen-generator] hold with the rate `σ` and the bound `M₀`, once the levels
satisfy the rows of the
regime.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Auxiliary lemmas -/

/-- `Σ |x_i|²` is the square of `l2Norm x`. -/
private lemma SrcCutoffPoint_l2Norm_sq {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    l2Norm x ^ 2 = ∑ i, ‖x i‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- `‖M x‖² ≤ ‖M‖²_HS ‖x‖²` (Cauchy–Schwarz row by row). -/
private lemma SrcCutoffPoint_sumSq_mulVec_le {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) (x : n → ℂ) :
    ∑ i, ‖(M *ᵥ x) i‖ ^ 2 ≤ hsSq M * ∑ j, ‖x j‖ ^ 2 := by
  unfold hsSq
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ‖(M *ᵥ x) i‖ ^ 2 ≤ (∑ j, ‖M i j‖ * ‖x j‖) ^ 2 := by
        gcongr
        simp only [Matrix.mulVec, dotProduct]
        exact (norm_sum_le _ _).trans (by simp)
    _ ≤ (∑ j, ‖M i j‖ ^ 2) * ∑ j, ‖x j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- If `‖A‖²_HS ≤ a⁶` with `a ≥ 0`, then the operator norm of `A` is at most `a³`. -/
private lemma SrcCutoffPoint_norm_le_cube {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) {a : ℝ} (ha : 0 ≤ a) (h : hsSq A ≤ a ^ 6) : ‖A‖ ≤ a ^ 3 := by
  have h0 : 0 ≤ hsSq A := by unfold hsSq; positivity
  have hs : ‖A‖ ≤ Real.sqrt (hsSq A) := by
    rw [Matrix.l2_opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    change ‖Matrix.toEuclideanLin A x‖ ≤ _ * ‖x‖
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_mul h0]
    exact Real.sqrt_le_sqrt (SrcCutoffPoint_sumSq_mulVec_le A x.ofLp)
  calc ‖A‖ ≤ Real.sqrt (hsSq A) := hs
    _ ≤ Real.sqrt ((a ^ 3) ^ 2) := Real.sqrt_le_sqrt (by rw [← pow_mul]; exact h)
    _ = a ^ 3 := Real.sqrt_sq (by positivity)

/-- An orthogonal projection does not increase `Σ |x_i|²`. -/
private lemma SrcCutoffPoint_sumSq_proj_le {W : ℕ} {P : Matrix (Fin W) (Fin W) ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (x : Fin W → ℂ) :
    ∑ i, ‖(P *ᵥ x) i‖ ^ 2 ≤ ∑ i, ‖x i‖ ^ 2 := by
  have hn : ‖P‖ * ‖P‖ = ‖P‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hP.eq, hPP]
  have h1 : ‖P‖ ≤ 1 := by nlinarith [norm_nonneg P]
  have hx : 0 ≤ l2Norm x := Real.sqrt_nonneg _
  have h2 : l2Norm (P *ᵥ x) ≤ l2Norm x :=
    (l2Norm_mulVec_le P x).trans (mul_le_of_le_one_left hx h1)
  have h3 : l2Norm (P *ᵥ x) ^ 2 ≤ l2Norm x ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
  simpa only [SrcCutoffPoint_l2Norm_sq] using h3

open scoped ComplexOrder in
/-- For a positive semidefinite `M`, `k ≥ 1` and `a ≥ 0`, `Re Tr M^k ≤ a^k` gives `‖M‖ ≤ a`: every
eigenvalue `λ ≥ 0` has `λ^k ≤ Σ_i λ_i^k = Re Tr M^k`. -/
private lemma SrcCutoffPoint_norm_le_of_trace_pow {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.PosSemidef) {k : ℕ} (hk : k ≠ 0) {a : ℝ} (ha : 0 ≤ a)
    (h : (M ^ k).trace.re ≤ a ^ k) : ‖M‖ ≤ a := by
  have hl : ∀ i, 0 ≤ hM.1.eigenvalues i := hM.eigenvalues_nonneg
  have htr : (M ^ k).trace.re = ∑ i, hM.1.eigenvalues i ^ k := by
    conv_lhs => rw [hM.1.spectral_theorem, ← map_pow, Unitary.conjStarAlgAut_apply,
      Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul, Matrix.diagonal_pow,
      Matrix.trace_diagonal, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [← Complex.ofReal_pow]
  have hnorm : ‖M‖ = ‖(RCLike.ofReal ∘ hM.1.eigenvalues : n → ℂ)‖ := by
    conv_lhs => rw [hM.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
      Matrix.l2_opNorm_diagonal]
  rw [hnorm]
  refine (pi_norm_le_iff_of_nonneg ha).mpr fun i => ?_
  have hi : hM.1.eigenvalues i ^ k ≤ a ^ k := by
    rw [htr] at h
    exact (Finset.single_le_sum (fun j _ => pow_nonneg (hl j) k) (Finset.mem_univ i)).trans h
  have hi' := (pow_le_pow_iff_left₀ (hl i) ha hk).mp hi
  simpa [abs_of_nonneg (hl i)] using hi'

open scoped ComplexOrder in
/-- The common consequences of `CutSupp` for `0 < t`, `64 L_ov ≤ 1`, `k ≥ 1` and
`32 t² W^{34} ≤ κ²`: `R_5, …, R_{q-1}` exist; `P v ≠ 0`; `B_Q ≥ 3/4` on `ran Q` (the common
conclusion of Section 9.4.1 [su:sec:retained-geometry] with `‖(1 - P) Q‖² ≤ 1/8` and
`‖P v‖⁻² ‖Q P v‖² ≤ 1/8`); `4 ‖Q v‖² ≤ ‖P v‖²`; `Q Π Q + 1 - Q` is invertible and `‖y‖² ≤ ‖v‖²`;
`‖A_< R̃‖² ‖v‖² ≤ 2 t² W^{26} ‖P v‖²`, and so (9.70) [su:eq:error] in the form
`‖A_< R̃‖² ‖v‖² ≤ ‖v_{q-1}‖² / 16`. -/
private lemma SrcCutoffPoint_core {W q : ℕ} {g E : ℝ} {R P : Matrix (Fin W) (Fin W) ℂ}
    {c : CutLevels} {ω : Ω W q} {v : Fin W → ℂ} (hW : 1 ≤ W) (hP : P.IsHermitian)
    (hPP : P * P = P) (hv : v ≠ 0) (ht : 0 < c.t) (hLov' : 64 * c.Lov ≤ 1) (hkP : 1 ≤ c.kP)
    (herr : 32 * c.t ^ 2 * (W : ℝ) ^ 34 ≤ c.kOut ^ 2) (h : CutSupp W g E q R P c ω v) :
    (∀ j, 5 ≤ j → j ≤ q - 1 → IsUnit (chartR W g E q R ω j)) ∧
    P *ᵥ v ≠ 0 ∧
    (∀ u : Fin W → ℂ, retProj W g E q R c.t ω *ᵥ u = u →
      (3 / 4 : ℝ) * ∑ i, ‖u i‖ ^ 2 ≤ (star u ⬝ᵥ (allowProj P v *ᵥ u)).re) ∧
    4 * ∑ i, ‖(retProj W g E q R c.t ω *ᵥ v) i‖ ^ 2 ≤ ∑ i, ‖(P *ᵥ v) i‖ ^ 2 ∧
    IsUnit (retProj W g E q R c.t ω * allowProj P v * retProj W g E q R c.t ω +
        (1 - retProj W g E q R c.t ω)) ∧
    ∑ i, ‖srcVec W g E q R c.t P ω v i‖ ^ 2 ≤ ∑ i, ‖v i‖ ^ 2 ∧
    ‖cavProd W g E q ω (q - 6) *
          specProj ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6))
            (Set.Iic (c.t ^ 2)) * cavRes W g E q R ω‖ ^ 2 * ∑ i, ‖v i‖ ^ 2 ≤
      2 * c.t ^ 2 * (W : ℝ) ^ 26 * ∑ i, ‖(P *ᵥ v) i‖ ^ 2 ∧
    ‖cavProd W g E q ω (q - 6) *
          specProj ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6))
            (Set.Iic (c.t ^ 2)) * cavRes W g E q R ω‖ ^ 2 * ∑ i, ‖v i‖ ^ 2 ≤
      (1 / 16 : ℝ) * ∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2 := by
  obtain ⟨h1, h2, -, ⟨hT, hTs⟩, -, -, -, hcomp, -, -, hvP, hQv, hQPv, hout⟩ := h
  have hRu : ∀ j, 5 ≤ j → j ≤ q - 1 → IsUnit (chartR W g E q R ω j) := fun j h5 hj => by
    rcases Nat.lt_or_ge j (q - 1) with hj' | hj'
    · exact (h1 j h5 (by omega)).1
    · obtain rfl : j = q - 1 := by omega
      exact h2.1
  obtain ⟨hQh, hQQ, -⟩ := trace_retProj (g := g) (E := E) R c.t ω hT
  set Q := retProj W g E q R c.t ω with hQ
  set nP := ∑ i, ‖(P *ᵥ v) i‖ ^ 2 with hnP
  have hv0 : 0 < ∑ i, ‖v i‖ ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2)
      (Finset.single_le_sum (f := fun j => ‖v j‖ ^ 2) (fun j _ => by positivity)
        (Finset.mem_univ i))
  have hPv : P *ᵥ v ≠ 0 := by
    intro h0
    have : nP = 0 := by rw [hnP, h0]; simp
    rw [this, mul_zero] at hvP
    linarith
  have hnP0 : 0 < nP := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hPv
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2)
      (Finset.single_le_sum (f := fun j => ‖(P *ᵥ v) j‖ ^ 2) (fun j _ => by positivity)
        (Finset.mem_univ i))
  -- `‖(1 - P) Q‖² ≤ 1/8` from the compatibility cut
  have h1P : (1 - P)ᴴ = 1 - P := by rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP.eq]
  have h1PP : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, mul_sub, mul_sub, hPP, one_mul, mul_one, one_mul]
    abel
  have hBB : ((1 - P) * Q)ᴴ * ((1 - P) * Q) = Q * (1 - P) * Q := by
    rw [Matrix.conjTranspose_mul, h1P, hQh.eq, Matrix.mul_assoc, ← Matrix.mul_assoc (1 - P), h1PP,
      Matrix.mul_assoc]
  have hpsd : (Q * (1 - P) * Q).PosSemidef := hBB ▸ Matrix.posSemidef_conjTranspose_mul_self _
  have hM : ‖Q * (1 - P) * Q‖ ≤ 1 / 8 := by
    refine SrcCutoffPoint_norm_le_of_trace_pow hpsd (k := c.kP) (by omega) (by norm_num) ?_
    rw [div_pow, one_pow, le_div_iff₀ (by positivity)]
    linarith
  have hD2 : ‖(1 - P) * Q‖ ^ 2 ≤ 1 / 8 := by
    rw [sq, ← Matrix.l2_opNorm_conjTranspose_mul_self, hBB]
    exact hM
  -- `B_Q ≥ 3/4`
  have hQP : l2Norm (Q *ᵥ (P *ᵥ v)) ^ 2 / l2Norm (P *ᵥ v) ^ 2 ≤ 1 / 8 := by
    rw [SrcCutoffPoint_l2Norm_sq, SrcCutoffPoint_l2Norm_sq, div_le_iff₀ hnP0]
    linarith
  have hBQl : ∀ u : Fin W → ℂ, Q *ᵥ u = u →
      (3 / 4 : ℝ) * l2Norm u ^ 2 ≤ (star u ⬝ᵥ (allowProj P v *ᵥ u)).re := fun u hu => by
    have hl := allowProj_lower hP hPP hQh hQQ hPv u hu
    have hu0 : 0 ≤ l2Norm u ^ 2 := by positivity
    have hc : (3 / 4 : ℝ) ≤
        1 - ‖(1 - P) * Q‖ ^ 2 - l2Norm (Q *ᵥ (P *ᵥ v)) ^ 2 / l2Norm (P *ᵥ v) ^ 2 := by linarith
    exact (mul_le_mul_of_nonneg_right hc hu0).trans hl
  have hBQ : ∀ u : Fin W → ℂ, Q *ᵥ u = u →
      (3 / 4 : ℝ) * ∑ i, ‖u i‖ ^ 2 ≤ (star u ⬝ᵥ (allowProj P v *ᵥ u)).re := fun u hu => by
    rw [← SrcCutoffPoint_l2Norm_sq]
    exact hBQl u hu
  -- the source vector
  obtain ⟨hX, hy⟩ := srcVec_sq_le R c.t hP hPP ω hT (b := 3 / 4) (by norm_num) hBQl
  rw [SrcCutoffPoint_l2Norm_sq, SrcCutoffPoint_l2Norm_sq] at hy
  have hQv' : ∑ i, ‖(Q *ᵥ v) i‖ ^ 2 ≤ nP / 32 := by
    have : 2 * c.Lov * nP ≤ nP / 32 := by nlinarith
    linarith
  have hPvv : nP ≤ ∑ i, ‖v i‖ ^ 2 := SrcCutoffPoint_sumSq_proj_le hP hPP v
  have hy' : ∑ i, ‖srcVec W g E q R c.t P ω v i‖ ^ 2 ≤ ∑ i, ‖v i‖ ^ 2 := by
    have h43 : ((3 / 4 : ℝ)⁻¹) ^ 2 = 16 / 9 := by norm_num
    rw [h43] at hy
    nlinarith
  -- the matching error
  have hTn : ‖cavRes W g E q R ω‖ ≤ (W : ℝ) ^ 3 :=
    SrcCutoffPoint_norm_le_cube _ (Nat.cast_nonneg W) hTs
  have hAS := (norm_mul_specProj_le (Matrix.isHermitian_one (n := Fin W) (α := ℂ)) le_rfl
    (Set.empty_subset _) (cavProd W g E q ω (q - 6)) ht.le).2
  have hN : ‖cavProd W g E q ω (q - 6) *
      specProj ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)) (Set.Iic (c.t ^ 2)) *
      cavRes W g E q R ω‖ ≤ c.t * (W : ℝ) ^ 3 :=
    (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hAS hTn (norm_nonneg _) ht.le)
  have hN2 : ‖cavProd W g E q ω (q - 6) *
      specProj ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)) (Set.Iic (c.t ^ 2)) *
      cavRes W g E q R ω‖ ^ 2 ≤ c.t ^ 2 * (W : ℝ) ^ 6 := by
    calc _ ≤ (c.t * (W : ℝ) ^ 3) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hN 2
      _ = c.t ^ 2 * (W : ℝ) ^ 6 := by ring
  have hE : ‖cavProd W g E q ω (q - 6) *
      specProj ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)) (Set.Iic (c.t ^ 2)) *
      cavRes W g E q R ω‖ ^ 2 * ∑ i, ‖v i‖ ^ 2 ≤ 2 * c.t ^ 2 * (W : ℝ) ^ 26 * nP := by
    calc _ ≤ c.t ^ 2 * (W : ℝ) ^ 6 * (2 * (W : ℝ) ^ 20 * nP) :=
          mul_le_mul hN2 hvP hv0.le (by positivity)
      _ = 2 * c.t ^ 2 * (W : ℝ) ^ 26 * nP := by ring
  have hW26 : (W : ℝ) ^ 26 ≤ (W : ℝ) ^ 34 :=
    pow_le_pow_right₀ (by exact_mod_cast hW) (by norm_num)
  have h32 : 32 * c.t ^ 2 * (W : ℝ) ^ 26 * nP ≤ c.kOut ^ 2 * nP := by
    refine mul_le_mul_of_nonneg_right ?_ hnP0.le
    calc 32 * c.t ^ 2 * (W : ℝ) ^ 26 ≤ 32 * c.t ^ 2 * (W : ℝ) ^ 34 := by gcongr
      _ ≤ c.kOut ^ 2 := herr
  refine ⟨hRu, hPv, hBQ, by linarith, hX, hy', hE, by linarith⟩

/-- (9.19) [su:eq:generator-admissibility] on `CutSupp`: if `0 < L_ov ≤ 1/64`, `k ≥ 1` and
`32 t² W^{34} ≤ κ²`, the point `(ω, v)` lies in the open set on which the construction is
smooth. -/
theorem cutSupp_genGood {W q : ℕ} {g E : ℝ} {R P : Matrix (Fin W) (Fin W) ℂ} {c : CutLevels}
    {ω : Ω W q} {v : Fin W → ℂ} (hW : 1 ≤ W) (hq : 7 ≤ q) (hg : 0 < g) (hg1 : g ≤ 1)
    (hR : R.IsHermitian) (hP : P.IsHermitian) (hPP : P * P = P) (hv : v ≠ 0) (ht : 0 < c.t)
    (hLov : 0 < c.Lov) (hLov' : 64 * c.Lov ≤ 1) (hkOut : 0 < c.kOut) (hkP : 1 ≤ c.kP)
    (herr : 32 * c.t ^ 2 * (W : ℝ) ^ 34 ≤ c.kOut ^ 2) (h : CutSupp W g E q R P c ω v) :
    (ω, v) ∈ genGood W g E q R c.t P := by
  have _ := hg
  have _ := hg1
  have _ := hkOut
  obtain ⟨hRu, hPv, hBQ, -, hX, hy, -, hA⟩ :=
    SrcCutoffPoint_core hW hP hPP hv ht hLov' hkP herr h
  obtain ⟨-, -, h3, h4, -, h6, -⟩ := h
  have hC : ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω m) := fun m hm => (h3 m hm).1
  have hBQ2 : ∀ u : Fin W → ℂ, retProj W g E q R c.t ω *ᵥ u = u →
      (1 / 2 : ℝ) * ∑ i, ‖u i‖ ^ 2 ≤ (star u ⬝ᵥ (allowProj P v *ᵥ u)).re := fun u hu => by
    have h0 : 0 ≤ ∑ i, ‖u i‖ ^ 2 := by positivity
    linarith [hBQ u hu]
  have hb := smallGen_bounds hq hR c.t hP hPP ω hRu hC h4.1 hPv hBQ2 hy hA
  exact ⟨hRu, hC, h4.1, h6.1, hPv, hX, by linarith [hb.2.2.1]⟩

/-- The proof of Lemma 9.3 [su:lem:chosen-generator], parts (i), (iii)–(v), at a point of
`CutSupp`: if the levels satisfy `0 < L_ov ≤ 1/64`, `32 t² W^{34} ≤ κ²`,
`2 t² W^{26} (κ² + W⁶ g^{-2(q-6)}) ≤ κ⁴`, `4 L_rk + 1 ≤ C W σ` and `k ≥ 1`, then `GenPoint`
holds with the generator `K = K̂(ω; ·)` for every `C ≥ C₁`, and `‖K‖²_HS ≤ 64 L_ov` by (9.21)
[su:eq:normalized-generator-costs]. -/
theorem genPoint_of_cutSupp : ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ {W q : ℕ} {g E C M₀ σ : ℝ}
    {R P : Matrix (Fin W) (Fin W) ℂ} {c : CutLevels} {ω : Ω W q} {v : Fin W → ℂ},
    1 ≤ W → 7 ≤ q → 0 < g → g ≤ 1 → R.IsHermitian → P.IsHermitian → P * P = P →
    v ≠ 0 → 0 < c.t → 0 < c.Lov → 64 * c.Lov ≤ 1 → 0 < c.kOut → 1 ≤ c.kP →
    32 * c.t ^ 2 * (W : ℝ) ^ 34 ≤ c.kOut ^ 2 →
    2 * c.t ^ 2 * (W : ℝ) ^ 26 * (c.kOut ^ 2 + (W : ℝ) ^ 6 / g ^ (2 * (q - 6))) ≤
      c.kOut ^ 4 →
    4 * c.Lrk + 1 ≤ C * W * σ → C₁ ≤ C → g ^ 2 * ‖P * R * P‖ ≤ M₀ →
    CutSupp W g E q R P c ω v →
    GenPoint W q g E P R v C M₀ σ (fun w => smallGen W g E q R c.t P ω w) ω ∧
      hsSq (smallGen W g E q R c.t P ω v) ≤ 64 * c.Lov := by
  obtain ⟨CD, hCD, hD⟩ := smallGen_srcDeriv
  refine ⟨2 + 2 * CD, by linarith, ?_⟩
  intro W q g E C M₀ σ R P c ω v hW hq hg hg1 hR hP hPP hv ht hLov hLov' hkOut hkP herr hrow
    hrk hC hM₀ h
  have hgood := cutSupp_genGood hW hq hg hg1 hR hP hPP hv ht hLov hLov' hkOut hkP herr h
  obtain ⟨hRu, hPv, hBQ, hQv4, hX, hy, hE, hA⟩ :=
    SrcCutoffPoint_core hW hP hPP hv ht hLov' hkP herr h
  obtain ⟨-, hCu, hTu, -, -, -, hξ⟩ := id hgood
  obtain ⟨-, h2, h3, -, ⟨-, hHs⟩, -, hrkS, -, -, -, -, hQv, -, hout⟩ := h
  set nP := ∑ i, ‖(P *ᵥ v) i‖ ^ 2 with hnP
  set nO := ∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2 with hnO
  have hnP0 : 0 < nP := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hPv
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2)
      (Finset.single_le_sum (f := fun j => ‖(P *ᵥ v) j‖ ^ 2) (fun j _ => by positivity)
        (Finset.mem_univ i))
  have hnO0 : 0 ≤ nO := by positivity
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hC2 : 2 ≤ C := by linarith
  have hCsq : 2 * CD ≤ C ^ 2 := by nlinarith
  have hC4 : 4 ≤ C ^ 2 := by nlinarith
  have hBQ2 : ∀ u : Fin W → ℂ, retProj W g E q R c.t ω *ᵥ u = u →
      (1 / 2 : ℝ) * ∑ i, ‖u i‖ ^ 2 ≤ (star u ⬝ᵥ (allowProj P v *ᵥ u)).re := fun u hu => by
    have h0 : 0 ≤ ∑ i, ‖u i‖ ^ 2 := by positivity
    linarith [hBQ u hu]
  have hC' : ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω m) := fun m hm => (h3 m hm).1
  obtain ⟨-, -, -, -, -, hK, herrK, -⟩ :=
    smallGen_bounds hq hR c.t hP hPP ω hRu hC' hTu hPv hBQ2 hy hA
  obtain ⟨hs1, hs2, hs3⟩ := (smallGen_spec R c.t hP hPP ω hPv).2 hξ
  -- `‖K‖²_HS ≤ 64 L_ov`, (9.21) [su:eq:normalized-generator-costs]
  have hK64 : hsSq (smallGen W g E q R c.t P ω v) ≤ 64 * c.Lov := by
    refine hK.trans ?_
    rw [div_le_iff₀ hnP0]
    linarith
  -- (9.26) [su:eq:pair-matching-error] in squared form
  have hw8 : (W : ℝ) ^ (-8 : ℝ) = ((W : ℝ) ^ 8)⁻¹ := by
    rw [show (-8 : ℝ) = -((8 : ℕ) : ℝ) by norm_num, Real.rpow_neg (Nat.cast_nonneg _),
      Real.rpow_natCast]
  have herrC : ∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ (smallGen W g E q R c.t P ω v *ᵥ v) -
      chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2 ≤ C ^ 2 * (W : ℝ) ^ (-8 : ℝ) * nO := by
    have key : 128 * c.t ^ 2 * (W : ℝ) ^ 26 * nP * (W : ℝ) ^ 8 ≤ C ^ 2 * nO := by
      calc 128 * c.t ^ 2 * (W : ℝ) ^ 26 * nP * (W : ℝ) ^ 8
          = 4 * ((32 * c.t ^ 2 * (W : ℝ) ^ 34) * nP) := by ring
        _ ≤ 4 * (c.kOut ^ 2 * nP) := by gcongr
        _ ≤ 4 * nO := by linarith [hout]
        _ ≤ C ^ 2 * nO := by gcongr
    have hdiv : C ^ 2 * ((W : ℝ) ^ 8)⁻¹ * nO = C ^ 2 * nO / (W : ℝ) ^ 8 := by ring
    rw [hw8, hdiv, le_div_iff₀ (by positivity)]
    calc _ ≤ 64 * (2 * c.t ^ 2 * (W : ℝ) ^ 26 * nP) * (W : ℝ) ^ 8 := by
          gcongr
          exact herrK.trans (by linarith [hE])
      _ = 128 * c.t ^ 2 * (W : ℝ) ^ 26 * nP * (W : ℝ) ^ 8 := by ring
      _ ≤ C ^ 2 * nO := key
  -- the levels `e` and `ρ` of (9.78) [su:eq:construction-derivative-goals]
  set X := (W : ℝ) ^ 6 / g ^ (2 * (q - 6)) with hX
  set e := 2 * c.t ^ 2 * (W : ℝ) ^ 26 / c.kOut ^ 2 with he
  set ρ := X / c.kOut ^ 2 with hρ
  have hk2 : 0 < c.kOut ^ 2 := by positivity
  have hgq : 0 < g ^ (2 * (q - 6)) := by positivity
  have hX0 : 0 ≤ X := by positivity
  have hρ0 : 0 ≤ ρ := by positivity
  have hAe : ‖cavProd W g E q ω (q - 6) *
      specProj ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)) (Set.Iic (c.t ^ 2)) *
      cavRes W g E q R ω‖ ^ 2 * ∑ i, ‖v i‖ ^ 2 ≤ e * nO := by
    refine hE.trans ?_
    have he' : 2 * c.t ^ 2 * (W : ℝ) ^ 26 = e * c.kOut ^ 2 := by
      rw [he, div_mul_cancel₀ _ hk2.ne']
    rw [he']
    have he0 : 0 ≤ e := by positivity
    calc e * c.kOut ^ 2 * nP = e * (c.kOut ^ 2 * nP) := by ring
      _ ≤ e * nO := by gcongr
  have he16 : e ≤ 1 / 16 := by
    rw [he, div_le_iff₀ hk2]
    have hW26 : (W : ℝ) ^ 26 ≤ (W : ℝ) ^ 34 :=
      pow_le_pow_right₀ (by exact_mod_cast hW) (by norm_num)
    have : c.t ^ 2 * (W : ℝ) ^ 26 ≤ c.t ^ 2 * (W : ℝ) ^ 34 := by gcongr
    linarith
  have hHn : ‖(activeMat W g E q R ω)⁻¹‖ ≤ (W : ℝ) ^ 3 :=
    SrcCutoffPoint_norm_le_cube _ (Nat.cast_nonneg W) hHs
  have hsch := (activeMat_schur hq hg.le hR ω hRu hCu hTu).2.2.2
  have hRP : ‖chartProd W g E q R ω (q - 1)‖ ^ 2 ≤ X := by
    rw [hX, le_div_iff₀ hgq, pow_mul', show (W : ℝ) ^ 6 = ((W : ℝ) ^ 3) ^ 2 by ring]
    have h0 : 0 ≤ g ^ (q - 6) * ‖chartProd W g E q R ω (q - 1)‖ := by positivity
    calc ‖chartProd W g E q R ω (q - 1)‖ ^ 2 * (g ^ (q - 6)) ^ 2
        = (g ^ (q - 6) * ‖chartProd W g E q R ω (q - 1)‖) ^ 2 := by ring
      _ ≤ ((W : ℝ) ^ 3) ^ 2 := pow_le_pow_left₀ h0 (hsch.trans hHn) 2
  have hρb : nP * ‖chartProd W g E q R ω (q - 1)‖ ^ 2 ≤ ρ * nO := by
    calc nP * ‖chartProd W g E q R ω (q - 1)‖ ^ 2 ≤ nP * X := by gcongr
      _ = ρ * (c.kOut ^ 2 * nP) := by rw [hρ]; field_simp
      _ ≤ ρ * nO := by gcongr
  have heρ : e * (1 + ρ) ≤ 1 := by
    have heq : e * (1 + ρ) =
        2 * c.t ^ 2 * (W : ℝ) ^ 26 * (c.kOut ^ 2 + X) / c.kOut ^ 4 := by
      rw [he, hρ]
      field_simp
    rw [heq, div_le_one (by positivity)]
    exact hrow
  obtain ⟨Es, hEs, hdim, hd1, hd2⟩ :=
    hD hq hR hP hPP hgood hBQ hQv4 hAe he16 hρb hρ0
  -- the dimension of `𝓔`, (9.28) [su:eq:pair-exceptional-dimension]
  have hdimC : (Module.finrank ℝ Es : ℝ) ≤ C * W * σ := by
    obtain ⟨-, -, htr⟩ := trace_retProj (g := g) (E := E) R c.t ω hTu
    have hcnt := (countIn_le_rankSurr (cavProd W g E q ω (q - 6)) ht one_pos one_le_two).1
    have hre : (retProj W g E q R c.t ω).trace.re =
        (countIn ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6))
          (Set.Ioi (c.t ^ 2)) : ℝ) := by
      rw [htr]; simp
    rw [hre] at hdim
    linarith only [hdim, hcnt, hrkS, hrk]
  -- the bound of `R_{q-1}`
  have hnR : ‖chartR W g E q R ω (q - 1)‖ ≤ C * (W : ℝ) ^ 3 := by
    have h0 := SrcCutoffPoint_norm_le_cube _ (Nat.cast_nonneg W) h2.2
    have : (W : ℝ) ^ 3 ≤ C * (W : ℝ) ^ 3 :=
      le_mul_of_one_le_left (by positivity) (by linarith only [hC2])
    exact h0.trans this
  refine ⟨⟨hPv, hs1, hs2, hs3, hRu, hK64.trans (by linarith only [hLov', hC2]), herrC,
    ⟨Es, hEs, hdimC, fun w hw1 hw2 => ?_, fun w hw1 hw2 hw3 => ?_⟩, hnR, hM₀⟩, hK64⟩
  · refine (hd1 w hw1 hw2).trans ?_
    have hw0 : 0 ≤ ∑ i, ‖w i‖ ^ 2 := by positivity
    have : CD * (1 + e * (1 + ρ)) ≤ C ^ 2 :=
      calc CD * (1 + e * (1 + ρ)) ≤ CD * 2 :=
            mul_le_mul_of_nonneg_left (by linarith only [heρ]) hCD.le
        _ ≤ C ^ 2 := by linarith only [hCsq]
    exact mul_le_mul_of_nonneg_right this hw0
  · refine (hd2 w hw1 hw2 hw3).trans ?_
    have hw0 : 0 ≤ ∑ i, ‖w i‖ ^ 2 := by positivity
    have hK0 : 0 ≤ hsSq (smallGen W g E q R c.t P ω v) := by unfold hsSq; positivity
    have : CD ≤ C ^ 2 := by linarith only [hCsq, hCD]
    gcongr

end LSBA
