import LSBA.Prop.Step2

/-!
# Step 3 of the one-step propagation: the same-sign pair

The same-sign pair (C.37) [fo:eq:same-pair]–(C.39) [gc:eq:same-pair-stop] of Appendix C.3
[sec:gc-one-step]: the moment comparison with the majorant
`|ℒ_2(a,c;+,+)| ≤ (ℒ_2(a,c;+,−) ℒ_2(c,a;+,−))^{1/2}`, with loss `R^{7/2}` and no barrier.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ### The same-sign pair error as a field of the Gaussian block coordinates -/

section Step3Field

/-- The same-sign two-loop error `D₂(r; a, b; +, +) = ℒ₂ - 𝒦₂` of (5.17)
[fo:eq:error-hierarchy] at the slice `A_g ⊗ I + Σ x_{c,k} T_{c,k}`. -/
private def step3s_field (g E : ℝ) (m : ℂ) (W L : ℕ) (r : ℝ) (x : Ω W L)
    (ab : Fin L × Fin L) : ℂ :=
  loopTr (resolventMat (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) x)
      (zChar g E m r)) ![ab.1, ab.2] ![true, true] -
    primLoop g W L E m r ![ab.1, ab.2] ![true, true]

/-- `A_g ⊗ I` is Hermitian. -/
private theorem step3s_herm (g : ℝ) (W L : ℕ) :
    (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)).IsHermitian := by
  have hA : (Ag g L).IsHermitian := by
    unfold Matrix.IsHermitian Ag
    rw [Matrix.conjTranspose_smul, (cycleAdj_isHermitian L).eq]
    simp
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_kronecker, hA.eq, Matrix.conjTranspose_one]

/-- Primitive loops of every length are continuous in time on `(-1, 1)` at a root. -/
private theorem step3s_primLoop_contOn (g : ℝ) (W L : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ L) (E : ℝ)
    (m : ℂ) (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {n : ℕ} (a : Fin n → Fin L)
    (σ : Fin n → Bool) : ContinuousOn (fun r => primLoop g W L E m r a σ) (Set.Ioo (-1) 1) := by
  rcases n with _ | _ | n
  · exact continuousOn_const (c := primLoop g W L E m 0 a σ)
  · exact continuousOn_const (c := primLoop g W L E m 0 a σ)
  · exact fun r hr => (primLoop_hasDerivAt g W L hW hL E m hm r hr (by omega) a σ).continuousAt
      |>.continuousWithinAt

/-- The primitive loops satisfy (5.10) [fo:eq:primitive] at every `u ∈ (-1, 1)`, all lengths. -/
private theorem step3s_primDeriv (g : ℝ) (W L : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ L) (E : ℝ) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (u : ℝ) (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    IsPrimDeriv (gammaG g) W L (fun r n b τ => primLoop g W L E m r (k := n) b τ) u := by
  intro n a σ
  rcases n with _ | _ | n
  · have h0 : cutSumFam (fun n b τ => primLoop g W L E m u (k := n) b τ) a σ = 0 := by
      simp [cutSumFam]
    rw [h0, mul_zero]
    exact hasDerivAt_const u (primLoop g W L E m 0 a σ)
  · have h1 : cutSumFam (fun n b τ => primLoop g W L E m u (k := n) b τ) a σ = 0 := by
      simp [cutSumFam]
    rw [h1, mul_zero]
    exact hasDerivAt_const u (primLoop g W L E m 0 a σ)
  · exact primLoop_hasDerivAt g W L hW hL E m hm u hu (by omega) a σ

/-- The same-sign pair error field is in the bounded `C^{1,2}` class on every `(a, b)` with
`-1 < a` and `b < 1`, at a root of (5.2) [fo:eq:dyson-family]. -/
private theorem step3s_heatClass (g E : ℝ) (m : ℂ) (W L : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ L)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (ab : Fin L × Fin L) {a b : ℝ} (ha : -1 < a)
    (hb : b < 1) :
    HeatClass (fun r x => step3s_field g E m W L r x ab) a b := by
  have hsub : Set.Ioo a b ⊆ Set.Ioo (-1) 1 := fun r hr => ⟨ha.trans hr.1, hr.2.trans hb⟩
  have hIcc : Set.Icc a b ⊆ Set.Ioo (-1) 1 := fun r hr =>
    ⟨ha.trans_le hr.1, hr.2.trans_lt hb⟩
  set κ : ℝ → ℂ := fun r => primLoop g W L E m r ![ab.1, ab.2] ![true, true] with hκdef
  set κ' : ℝ → ℂ := fun r => ((gammaG g * W : ℝ) : ℂ) *
    cutSumFam (fun n c τ => primLoop g W L E m r (k := n) c τ) ![ab.1, ab.2] ![true, true]
    with hκ'def
  have hc : ContinuousOn κ (Set.Ioo (-1) 1) :=
    step3s_primLoop_contOn g W L hW hL E m hm _ _
  have hc' : ContinuousOn κ' (Set.Ioo (-1) 1) := by
    refine continuousOn_const.mul ?_
    unfold cutSumFam
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    split_ifs
    · exact continuousOn_finsetSum _ fun c _ =>
        (step3s_primLoop_contOn g W L hW hL E m hm _ _).mul
          (step3s_primLoop_contOn g W L hW hL E m hm _ _)
    · exact continuousOn_const
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc.mono hIcc)
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc'.mono hIcc)
  have h := (heatClass_loopTr W L 2 _ (step3s_herm g W L) g E m hm.1 ![ab.1, ab.2]
    ![true, true] (a' := a) hb).sub_time κ κ'
    (fun r hr => primLoop_hasDerivAt g W L hW hL E m hm r (hsub hr) le_rfl _ _)
    (hc'.mono hsub)
    ⟨max C₁ C₂, fun r hr => ⟨(hC₁ r (Set.Ioo_subset_Icc_self hr)).trans (le_max_left _ _),
      (hC₂ r (Set.Ioo_subset_Icc_self hr)).trans (le_max_right _ _)⟩⟩
  exact h

/-- The cut terms of (5.17) [fo:eq:error-hierarchy] at `k = 2`, `(a, b; +, +)`. -/
private theorem step3s_cutErrSum_two {L : ℕ} (K D : LoopFam L) (a b : Fin L) :
    cutErrSum K D ![a, b] ![true, true] = ∑ c : Fin L,
      (K 2 ![c, b] ![true, true] * D 2 ![a, c] ![true, true] +
        D 2 ![c, b] ![true, true] * K 2 ![a, c] ![true, true] +
        D 2 ![c, b] ![true, true] * D 2 ![a, c] ![true, true]) := by
  unfold cutErrSum
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  have h00 : ¬((0 : Fin 2) < 0) := by decide
  have h01 : (0 : Fin 2) < 1 := by decide
  have h10 : ¬((1 : Fin 2) < 0) := by decide
  have h11 : ¬((1 : Fin 2) < 1) := by decide
  simp only [h00, h01, h10, h11, ↓reduceIte, zero_add, add_zero]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hL : cutLLab ![a, b] (0 : Fin 2) 1 c = ![c, b] := by
    funext p; fin_cases p <;> rfl
  have hLs : cutLSgn ![true, true] (0 : Fin 2) 1 = ![true, true] := by
    funext p; fin_cases p <;> rfl
  have hR : cutRLab ![a, b] (0 : Fin 2) 1 c = ![a, c] := by
    funext p; fin_cases p <;> rfl
  have hRs : cutRSgn ![true, true] (0 : Fin 2) 1 = ![true, true] := by
    funext p; fin_cases p <;> rfl
  rw [hL, hLs, hR, hRs]
  rfl

/-- (5.17) [fo:eq:error-hierarchy] for the same-sign pair in generator form:
`𝒢D₂(a,b;+,+) = 𝒲₂ + γ_gW Σ_c (𝒦₂(a,c) D₂(c,b) + D₂(a,c) ℒ₂(c,b))`. -/
private theorem step3s_blockGen (g E : ℝ) (m : ℂ) (W L : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ L)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {u : ℝ} (hu : u ∈ Set.Ioo (-1 : ℝ) 1)
    {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian) (a b : Fin L) :
    blockGen W L (gammaG g) (fun r N => resLoop g E m ![a, b] ![true, true] r N -
        primLoop g W L E m r ![a, b] ![true, true]) u M =
      lightW g E m ![a, b] ![true, true] u M +
        ((gammaG g * W : ℝ) : ℂ) * ∑ c : Fin L,
          (primLoop g W L E m u ![a, c] ![true, true] *
              (resLoop g E m ![c, b] ![true, true] u M -
                primLoop g W L E m u ![c, b] ![true, true]) +
            (resLoop g E m ![a, c] ![true, true] u M -
                primLoop g W L E m u ![a, c] ![true, true]) *
              resLoop g E m ![c, b] ![true, true] u M) := by
  have h := blockGen_errorLoop g E m hm.1 hu.2 hM _ (step3s_primDeriv g W L hW hL E m hm u hu)
    ![a, b] ![true, true]
  rw [h]
  congr 2
  rw [step3s_cutErrSum_two]
  simp only [errFam, resLoop]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-- The bracket of the same-sign pair error is the bracket of the loop, (5.9) [gc:eq:bracket]. -/
private theorem step3s_blockGamma_err (g E : ℝ) (m : ℂ) (W L : ℕ) (u : ℝ)
    (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) :
    blockGamma W L (gammaG g)
        (fun N => resLoop g E m ![a, b] ![true, true] u N -
          primLoop g W L E m u ![a, b] ![true, true])
        (fun N => resLoop g E m ![a, b] ![true, true] u N -
          primLoop g W L E m u ![a, b] ![true, true]) M =
      blockGamma W L (gammaG g) (resLoop g E m ![a, b] ![true, true] u)
        (resLoop g E m ![a, b] ![true, true] u) M := by
  unfold blockGamma
  simp only [deriv_sub_const]

/-- The coordinate generator of the field is the block generator at the slice. -/
private theorem step3s_coordGen_eq (g E : ℝ) (m : ℂ) (W L : ℕ) (ab : Fin L × Fin L) (u : ℝ)
    (y : Ω W L) :
    coordGen (gammaG g / W) (fun r x => step3s_field g E m W L r x ab) u y =
      blockGen W L (gammaG g) (fun r N => resLoop g E m ![ab.1, ab.2] ![true, true] r N -
        primLoop g W L E m r ![ab.1, ab.2] ![true, true]) u
        (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y) := by
  rw [blockGen_slice]
  rfl

/-- The carré du champ of the field is the bracket of the loop at the slice. -/
private theorem step3s_coordGamma_eq (g E : ℝ) (m : ℂ) (W L : ℕ) (ab : Fin L × Fin L) (u : ℝ)
    (y : Ω W L) :
    coordGamma (gammaG g / W) (fun x => step3s_field g E m W L u x ab)
        (fun x => step3s_field g E m W L u x ab) y =
      blockGamma W L (gammaG g) (resLoop g E m ![ab.1, ab.2] ![true, true] u)
        (resLoop g E m ![ab.1, ab.2] ![true, true] u)
        (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y) := by
  rw [← step3s_blockGamma_err, blockGamma_slice]
  rfl

/-- The flow at time `u ≥ 0` is the slice at the scaled coordinates `√(uγ_g/W) ω`. -/
private theorem step3s_flowH_eq (g : ℝ) (W L : ℕ) {u : ℝ} (hu : 0 ≤ u) (ω : Ω W L) :
    flowH g W L u ω = blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
      (Real.sqrt (u * (gammaG g / W)) • ω) := by
  have hγ : 0 ≤ gammaG g := by unfold gammaG; positivity
  unfold flowH
  rw [blockFlow_eq_blockSlice _ _ _ (mul_nonneg hu hγ), mul_div_assoc]

/-- The same-sign pair error along the flow is the field at the scaled coordinates. -/
private theorem step3s_flowErr_eq (g E : ℝ) (W L : ℕ) {u : ℝ} (hu : 0 ≤ u) (l : Fin L × Fin L)
    (ω : Ω W L) :
    flowErr W ⟨g, E, L, u⟩ ![l.1, l.2] ![true, true] ω =
      step3s_field g E (mRoot g L E) W L u (Real.sqrt (u * (gammaG g / W)) • ω) l := by
  unfold flowErr flowG step3s_field
  simp only
  rw [step3s_flowH_eq g W L hu]

end Step3Field

/-! ### Hilbert–Schmidt norms of blocks -/

section Step3LinAlg

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Squared Hilbert–Schmidt norm `Σ_{ij} |A_{ij}|²`. -/
private def step3s_hs (A : Matrix n n ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

omit [DecidableEq n] in
private lemma step3s_hs_nonneg (A : Matrix n n ℂ) : 0 ≤ step3s_hs A := by
  unfold step3s_hs; positivity

/-- `‖A u‖² ≤ ‖A‖² ‖u‖²` for the operator norm. -/
private lemma step3s_nsq_le (A : Matrix n n ℂ) (u : n → ℂ) :
    ∑ i, ‖(A *ᵥ u) i‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ i, ‖u i‖ ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 u)
  have h1 : ‖(EuclideanSpace.equiv n ℂ).symm (A *ᵥ u)‖ ^ 2 = ∑ i, ‖(A *ᵥ u) i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  have h2 : ‖(WithLp.toLp 2 u : EuclideanSpace ℂ n)‖ ^ 2 = ∑ i, ‖u i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
  rw [← h1, ← h2, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- `‖Y X‖²_HS ≤ ‖Y‖² ‖X‖²_HS`. -/
private lemma step3s_hs_mul_left (Y X : Matrix n n ℂ) :
    step3s_hs (Y * X) ≤ ‖Y‖ ^ 2 * step3s_hs X := by
  unfold step3s_hs
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => ‖X i j‖ ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h := step3s_nsq_le Y (fun i => X i j)
  have e : (Y *ᵥ fun i => X i j) = fun i => (Y * X) i j := by
    funext i; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  rw [e] at h
  exact h

omit [DecidableEq n] in
private lemma step3s_hs_conjTranspose (X : Matrix n n ℂ) :
    step3s_hs Xᴴ = step3s_hs X := by
  unfold step3s_hs
  rw [Finset.sum_comm]
  simp [Matrix.conjTranspose_apply]

/-- `‖X Y‖²_HS ≤ ‖Y‖² ‖X‖²_HS`. -/
private lemma step3s_hs_mul_right (X Y : Matrix n n ℂ) :
    step3s_hs (X * Y) ≤ ‖Y‖ ^ 2 * step3s_hs X := by
  have h := step3s_hs_mul_left Yᴴ Xᴴ
  rwa [← Matrix.conjTranspose_mul, step3s_hs_conjTranspose, Matrix.l2_opNorm_conjTranspose,
    step3s_hs_conjTranspose] at h

omit [DecidableEq n] in
/-- `|Tr(A B)| ≤ ‖A‖_HS ‖B‖_HS`. -/
private lemma step3s_trace_mul_le (A B : Matrix n n ℂ) :
    ‖(A * B).trace‖ ≤ Real.sqrt (step3s_hs A) * Real.sqrt (step3s_hs B) := by
  have h1 : (A * B).trace = ∑ x : n × n, A x.1 x.2 * B x.2 x.1 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact (Fintype.sum_prod_type' _).symm
  have hA : step3s_hs A = ∑ x : n × n, ‖A x.1 x.2‖ ^ 2 := (Fintype.sum_prod_type' _).symm
  have hB : step3s_hs B = ∑ x : n × n, ‖B x.2 x.1‖ ^ 2 := by
    unfold step3s_hs
    rw [Finset.sum_comm]
    exact (Fintype.sum_prod_type' (fun i j => ‖B j i‖ ^ 2)).symm
  rw [h1, hA, hB]
  calc ‖∑ x : n × n, A x.1 x.2 * B x.2 x.1‖ ≤ ∑ x : n × n, ‖A x.1 x.2‖ * ‖B x.2 x.1‖ :=
        (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun x _ => norm_mul _ _))
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- `|Tr(A B C)| ≤ ‖A‖ ‖B‖_HS ‖C‖_HS`. -/
private lemma step3s_trace3_le (A B C : Matrix n n ℂ) :
    ‖(A * B * C).trace‖ ≤
      ‖A‖ * (Real.sqrt (step3s_hs B) * Real.sqrt (step3s_hs C)) := by
  refine (step3s_trace_mul_le _ _).trans ?_
  have h : Real.sqrt (step3s_hs (A * B)) ≤ ‖A‖ * Real.sqrt (step3s_hs B) := by
    rw [← Real.sqrt_sq (norm_nonneg A), ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt (step3s_hs_mul_left A B)
  calc Real.sqrt (step3s_hs (A * B)) * Real.sqrt (step3s_hs C)
      ≤ ‖A‖ * Real.sqrt (step3s_hs B) * Real.sqrt (step3s_hs C) :=
        mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg _)
    _ = _ := by ring

omit [DecidableEq n] in
/-- `‖A + B‖²_HS ≤ 2‖A‖²_HS + 2‖B‖²_HS`. -/
private lemma step3s_hs_add_le (A B : Matrix n n ℂ) :
    step3s_hs (A + B) ≤ 2 * step3s_hs A + 2 * step3s_hs B := by
  unfold step3s_hs
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Matrix.add_apply]
  have h := norm_add_le (A i j) (B i j)
  have h0 := norm_nonneg (A i j + B i j)
  nlinarith [sq_nonneg (‖A i j‖ - ‖B i j‖), norm_nonneg (A i j), norm_nonneg (B i j)]

omit [DecidableEq n] in
private lemma step3s_hs_smul (k : ℂ) (A : Matrix n n ℂ) :
    step3s_hs (k • A) = ‖k‖ ^ 2 * step3s_hs A := by
  unfold step3s_hs
  simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

omit [DecidableEq n] in
/-- `Tr(Z Z*) = ‖Z‖²_HS`. -/
private lemma step3s_trace_mul_conjTranspose (Z : Matrix n n ℂ) :
    (Z * Zᴴ).trace = ((step3s_hs Z : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    step3s_hs]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj']

end Step3LinAlg

section Step3Block

open scoped Matrix.Norms.L2Operator

variable {W L : ℕ}

/-- `(X E_a Y)_{cd} = W⁻¹ X_{ca} Y_{ad}`. -/
private lemma step3s_blockOf_mul_blockE_mul (X Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a c d : Fin L) :
    blockOf (X * blockE W L a * Y) c d = (W : ℂ)⁻¹ • (blockOf X c a * blockOf Y a d) := by
  ext α β
  simp only [blockOf, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
  simp only [blockE, Matrix.mul_diagonal, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun γ _ => ?_
    simp only [ite_true, Matrix.of_apply]; ring
  · intro e _ he; simp [he]
  · simp

/-- `Tr(Y E_z) = W⁻¹ Tr Y_{zz}`. -/
private lemma step3s_trace_mul_blockE (Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (z : Fin L) : (Y * blockE W L z).trace = (W : ℂ)⁻¹ * (blockOf Y z z).trace := by
  simp only [Matrix.trace, Matrix.diag, blockE, Matrix.mul_diagonal, blockOf, Matrix.of_apply,
    Fintype.sum_prod_type, Finset.mul_sum]
  rw [Finset.sum_eq_single z]
  · refine Finset.sum_congr rfl fun γ _ => ?_
    simp only [ite_true]; ring
  · intro e _ he; simp [he]
  · simp

/-- A loop of length three as the trace of the product of three blocks. -/
private lemma step3s_loopTr_three (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (x y z : Fin L) (s₀ s₁ s₂ : Bool) :
    loopTr X ![x, y, z] ![s₀, s₁, s₂] = (W : ℂ)⁻¹ ^ 3 *
      (blockOf (sgnMat X s₀) z x * blockOf (sgnMat X s₁) x y *
        blockOf (sgnMat X s₂) y z).trace := by
  have e : (List.ofFn fun i : Fin 3 =>
      sgnMat X (![s₀, s₁, s₂] i) * blockE W L (![x, y, z] i)).prod =
      sgnMat X s₀ * blockE W L x * (sgnMat X s₁ * blockE W L y * sgnMat X s₂) * blockE W L z := by
    simp [List.ofFn_succ, Matrix.mul_assoc]
  unfold loopTr
  rw [e, step3s_trace_mul_blockE, step3s_blockOf_mul_blockE_mul,
    step3s_blockOf_mul_blockE_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul,
    smul_eq_mul, Matrix.mul_assoc]
  ring

private lemma step3s_blockOf_conjTranspose (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (e f : Fin L) : blockOf Xᴴ e f = (blockOf X f e)ᴴ := by
  ext α β; simp [blockOf, Matrix.conjTranspose_apply]

private lemma step3s_hs_blockOf (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (e f : Fin L) : step3s_hs (blockOf X e f) = blockHS2 X e f := by
  simp [step3s_hs, blockHS2, blockOf]

/-- The diagonal block of `X E_a (Y E_b Z)` is `W⁻² X_{ca} Y_{ab} Z_{bc}`. -/
private lemma step3s_blockOf_five (X Y Z : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b c : Fin L) :
    blockOf (X * blockE W L a * (Y * blockE W L b * Z)) c c =
      ((W : ℂ)⁻¹ * (W : ℂ)⁻¹) • (blockOf X c a * (blockOf Y a b * blockOf Z b c)) := by
  rw [step3s_blockOf_mul_blockE_mul, step3s_blockOf_mul_blockE_mul, Matrix.mul_smul,
    smul_smul]

private lemma step3s_blockOf_add (X Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (c d : Fin L) : blockOf (X + Y) c d = blockOf X c d + blockOf Y c d := by
  ext α β; simp [blockOf]

/-- `Tr(P_c Z P_c Z*) = ‖Z_{cc}‖²_HS` with `P_c = W E_c`. -/
private lemma step3s_trace_proj (hW : 1 ≤ W) (c : Fin L)
    (Z : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    (((W : ℂ) • blockE W L c) * Z * ((W : ℂ) • blockE W L c) * Zᴴ).trace =
      ((step3s_hs (blockOf Z c c) : ℝ) : ℂ) := by
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast (by omega : W ≠ 0)
  have e : ((W : ℂ) • blockE W L c) * Z * ((W : ℂ) • blockE W L c) * Zᴴ =
      ((W : ℂ) * W) • (blockE W L c * (Z * blockE W L c * Zᴴ)) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [e, Matrix.trace_smul, Matrix.trace_mul_comm, step3s_trace_mul_blockE,
    step3s_blockOf_mul_blockE_mul, Matrix.trace_smul, step3s_blockOf_conjTranspose,
    step3s_trace_mul_conjTranspose, smul_eq_mul, smul_eq_mul]
  field_simp

/-- `‖A B‖ ≤ ‖A‖ ‖B‖` for the operator norm of `W × W` blocks. -/
private lemma step3s_opNorm_mul_le (A B : Matrix (Fin W) (Fin W) ℂ) : ‖A * B‖ ≤ ‖A‖ * ‖B‖ :=
  Matrix.l2_opNorm_mul A B

/-- `ℒ₁(a, +) = ⟨X⟩_{aa}`. -/
private lemma step3s_loopTr_one_eq (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a : Fin L) : loopTr X ![a] ![true] = blockTr X a a := by
  rw [loopTr_one]; rfl

/-- `ℒ₂(a, b; +, -) = W⁻² ‖X_{ba}‖²_HS`. -/
private lemma step3s_loopTr_pm (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) :
    loopTr X ![a, b] ![true, false] = ((((W : ℝ) ^ 2)⁻¹ * blockHS2 X b a : ℝ) : ℂ) := by
  rw [loopTr_two]
  rfl

/-- Ward's identity for the rows and columns of a resolvent at `Im z > 0`:
`Σ_y |G_{xy}|² = Σ_y |G_{yx}|² = Im G_{xx}/Im z`. -/
private theorem step3s_ward_entry {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (x : n) :
    ∑ y, ‖resolventMat H z x y‖ ^ 2 = (resolventMat H z x x).im / z.im ∧
      ∑ y, ‖resolventMat H z y x‖ ^ 2 = (resolventMat H z x x).im / z.im := by
  have hz0 : z.im ≠ 0 := hz.ne'
  have ez : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := (Complex.re_add_im z).symm
  refine ⟨?_, ?_⟩
  · have h := ward hH z.re hz0 x
    rw [← ez] at h
    exact h
  · set G := resolventMat H z with hG
    have hx := congrFun (congrFun (ward_matrix hH hz0) x) x
    rw [Matrix.mul_apply] at hx
    simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply] at hx
    have e : ∑ y, star (G y x) * G y x = ((∑ y, ‖G y x‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Complex.star_def, Complex.conj_mul']
    rw [e, smul_eq_mul] at hx
    have hw : ∀ w : ℂ, w - star w = ((2 * w.im : ℝ) : ℂ) * Complex.I := fun w => by
      apply Complex.ext <;> simp [two_mul]
    rw [hw] at hx
    apply Complex.ofReal_injective
    rw [hx]
    push_cast
    have hη' : (z.im : ℂ) ≠ 0 := by exact_mod_cast hz0
    field_simp
    rfl

/-- The Ward identity (5.11) [gc:eq:ward] for the blocks of a resolvent at `Im z > 0`:
`Σ_c ‖G_{ca}‖²_HS = Σ_c ‖G_{ac}‖²_HS = W Im⟨G⟩_{aa}/Im z`. -/
private theorem step3s_ward (hW : 1 ≤ W) (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im) (a : Fin L) :
    ∑ c, blockHS2 (resolventMat H z) c a =
        W * (blockTr (resolventMat H z) a a).im / z.im ∧
      ∑ c, blockHS2 (resolventMat H z) a c =
        W * (blockTr (resolventMat H z) a a).im / z.im := by
  set G := resolventMat H z with hG
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hbt : W * (blockTr G a a).im / z.im = ∑ α : Fin W, (G (a, α) (a, α)).im / z.im := by
    unfold blockTr
    rw [← Finset.sum_div]
    congr 1
    rw [show ((W : ℂ)⁻¹ * ∑ α, G (a, α) (a, α)) = (((W : ℝ)⁻¹ : ℝ) : ℂ) * ∑ α, G (a, α) (a, α)
      by push_cast; rfl, Complex.im_ofReal_mul, Complex.im_sum]
    field_simp
  rw [hbt]
  constructor
  · unfold blockHS2
    rw [Finset.sum_congr rfl (fun c _ => Finset.sum_comm), Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [← (step3s_ward_entry hH hz (a, β)).2, Fintype.sum_prod_type]
  · unfold blockHS2
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← (step3s_ward_entry hH hz (a, α)).1, Fintype.sum_prod_type]

end Step3Block

/-! ### Rows of the generator and the bracket at a good point -/

section Step3Rows

open scoped Matrix.Norms.L2Operator

variable {W L : ℕ}

/-- `Σ_c √x_c √y_c ≤ X` when `Σ_c x_c ≤ X` and `Σ_c y_c ≤ X`. -/
private lemma step3s_sum_sqrt_le {ι : Type*} [Fintype ι] (x y : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hy : ∀ i, 0 ≤ y i) {X : ℝ} (hX : ∑ i, x i ≤ X) (hY : ∑ i, y i ≤ X) :
    ∑ i, Real.sqrt (x i) * Real.sqrt (y i) ≤ X := by
  have h := Real.sum_sqrt_mul_sqrt_le Finset.univ hx hy
  have hX0 : 0 ≤ X := (Finset.sum_nonneg fun i _ => hx i).trans hX
  refine h.trans ?_
  calc Real.sqrt (∑ i, x i) * Real.sqrt (∑ i, y i) ≤ Real.sqrt X * Real.sqrt X :=
        mul_le_mul (Real.sqrt_le_sqrt hX) (Real.sqrt_le_sqrt hY) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = X := Real.mul_self_sqrt hX0

/-- The light term (5.7) [fo:eq:light] of the same-sign pair at a good point: with
`‖G_{xy}‖ ≤ O`, `Im⟨G⟩_{xx} ≤ ρ` and `|⟨G⟩_{cc} - m| ≤ τ`,
`|𝒲₂(a,b;+,+)| ≤ 2γ_gW τ W⁻³ O (Wρ/η)`, by the Ward identity (5.11) [gc:eq:ward]. -/
private theorem step3s_light_le (g E : ℝ) (m : ℂ) (hW : 1 ≤ W) {u : ℝ}
    {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    (hz : 0 < (zChar g E m u).im) {O τ ρ : ℝ} (hO : 0 ≤ O) (hτ : 0 ≤ τ)
    (hop : ∀ x y, ‖blockOf (resolventMat M (zChar g E m u)) x y‖ ≤ O)
    (hden : ∀ x, (blockTr (resolventMat M (zChar g E m u)) x x).im ≤ ρ)
    (havg : ∀ c, ‖loopTr (resolventMat M (zChar g E m u)) ![c] ![true] - m‖ ≤ τ) (a b : Fin L) :
    ‖lightW g E m ![a, b] ![true, true] u M‖ ≤
      2 * (gammaG g * W) * τ * ((W : ℝ)⁻¹ ^ 3 * (O * (W * ρ / (zChar g E m u).im))) := by
  set G := resolventMat M (zChar g E m u) with hG
  set η := (zChar g E m u).im with hη
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hγW : 0 ≤ gammaG g * W := by positivity
  have hward := fun x => step3s_ward hW M hM (zChar g E m u) hz x
  have hX : ∀ x, W * (blockTr G x x).im / η ≤ W * ρ / η := fun x => by
    have := hden x
    gcongr
  have hs : ∀ x y, step3s_hs (blockOf G x y) = blockHS2 G x y := step3s_hs_blockOf G
  have hhs0 : ∀ x y, 0 ≤ blockHS2 G x y := fun x y => by unfold blockHS2; positivity
  -- the three-loops through `c`
  have h3 : ∀ i : Fin 2, ∑ c : Fin L, ‖loopTr G (insLab ![a, b] i c) (insSgn ![true, true] i)‖ ≤
      (W : ℝ)⁻¹ ^ 3 * (O * (W * ρ / η)) := by
    intro i
    fin_cases i
    · have e : ∀ c : Fin L, insLab ![a, b] (0 : Fin 2) c = ![c, a, b] := fun c => by
        funext j; fin_cases j <;> rfl
      have es : insSgn (![true, true] : Fin 2 → Bool) (0 : Fin 2) = ![true, true, true] := by
        funext j; fin_cases j <;> rfl
      have hc : ∀ c : Fin L, ‖loopTr G (insLab ![a, b] (0 : Fin 2) c)
          (insSgn ![true, true] (0 : Fin 2))‖ ≤ (W : ℝ)⁻¹ ^ 3 *
            (O * (Real.sqrt (blockHS2 G b c) * Real.sqrt (blockHS2 G c a))) := by
        intro c
        rw [e, es, step3s_loopTr_three]
        simp only [sgnMat, ite_true]
        rw [norm_mul, norm_pow, norm_inv, Complex.norm_natCast, Matrix.trace_mul_cycle]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (step3s_trace3_le _ _ _).trans ?_
        rw [hs, hs]
        exact mul_le_mul_of_nonneg_right (hop a b) (by positivity)
      calc _ ≤ ∑ c : Fin L, (W : ℝ)⁻¹ ^ 3 *
            (O * (Real.sqrt (blockHS2 G b c) * Real.sqrt (blockHS2 G c a))) :=
            Finset.sum_le_sum fun c _ => hc c
        _ = (W : ℝ)⁻¹ ^ 3 * (O * ∑ c : Fin L,
            Real.sqrt (blockHS2 G b c) * Real.sqrt (blockHS2 G c a)) := by
            simp only [Finset.mul_sum]
        _ ≤ _ := by
            gcongr
            exact step3s_sum_sqrt_le _ _ (fun c => hhs0 b c) (fun c => hhs0 c a)
              (((hward b).2).le.trans (hX b)) (((hward a).1).le.trans (hX a))
    · have e : ∀ c : Fin L, insLab ![a, b] (1 : Fin 2) c = ![a, c, b] := fun c => by
        funext j; fin_cases j <;> rfl
      have es : insSgn (![true, true] : Fin 2 → Bool) (1 : Fin 2) = ![true, true, true] := by
        funext j; fin_cases j <;> rfl
      have hc : ∀ c : Fin L, ‖loopTr G (insLab ![a, b] (1 : Fin 2) c)
          (insSgn ![true, true] (1 : Fin 2))‖ ≤ (W : ℝ)⁻¹ ^ 3 *
            (O * (Real.sqrt (blockHS2 G a c) * Real.sqrt (blockHS2 G c b))) := by
        intro c
        rw [e, es, step3s_loopTr_three]
        simp only [sgnMat, ite_true]
        rw [norm_mul, norm_pow, norm_inv, Complex.norm_natCast]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (step3s_trace3_le _ _ _).trans ?_
        rw [hs, hs]
        exact mul_le_mul_of_nonneg_right (hop b a) (by positivity)
      calc _ ≤ ∑ c : Fin L, (W : ℝ)⁻¹ ^ 3 *
            (O * (Real.sqrt (blockHS2 G a c) * Real.sqrt (blockHS2 G c b))) :=
            Finset.sum_le_sum fun c _ => hc c
        _ = (W : ℝ)⁻¹ ^ 3 * (O * ∑ c : Fin L,
            Real.sqrt (blockHS2 G a c) * Real.sqrt (blockHS2 G c b)) := by
            simp only [Finset.mul_sum]
        _ ≤ _ := by
            gcongr
            exact step3s_sum_sqrt_le _ _ (fun c => hhs0 a c) (fun c => hhs0 c b)
              (((hward a).2).le.trans (hX a)) (((hward b).1).le.trans (hX b))
  unfold lightW
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hγW]
  have hsum : ‖∑ i : Fin 2, ∑ c : Fin L,
      (loopTr G ![c] ![(![true, true] : Fin 2 → Bool) i] -
        sgnScalar m ((![true, true] : Fin 2 → Bool) i)) *
        loopTr G (insLab ![a, b] i c) (insSgn ![true, true] i)‖ ≤
      2 * τ * ((W : ℝ)⁻¹ ^ 3 * (O * (W * ρ / η))) := by
    refine (norm_sum_le _ _).trans ?_
    have hi : ∀ i : Fin 2, ‖∑ c : Fin L,
        (loopTr G ![c] ![(![true, true] : Fin 2 → Bool) i] -
          sgnScalar m ((![true, true] : Fin 2 → Bool) i)) *
          loopTr G (insLab ![a, b] i c) (insSgn ![true, true] i)‖ ≤
        τ * ((W : ℝ)⁻¹ ^ 3 * (O * (W * ρ / η))) := by
      intro i
      have hti : (![true, true] : Fin 2 → Bool) i = true := by fin_cases i <;> rfl
      simp only [hti, sgnScalar, ite_true]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ c : Fin L, ‖(loopTr G ![c] ![true] - m) *
            loopTr G (insLab ![a, b] i c) (insSgn ![true, true] i)‖
          ≤ ∑ c : Fin L, τ * ‖loopTr G (insLab ![a, b] i c) (insSgn ![true, true] i)‖ := by
            refine Finset.sum_le_sum fun c _ => ?_
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (havg c) (norm_nonneg _)
        _ = τ * ∑ c : Fin L, ‖loopTr G (insLab ![a, b] i c) (insSgn ![true, true] i)‖ := by
            rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left (h3 i) hτ
    calc ∑ i : Fin 2, ‖∑ c : Fin L,
          (loopTr G ![c] ![(![true, true] : Fin 2 → Bool) i] -
            sgnScalar m ((![true, true] : Fin 2 → Bool) i)) *
          loopTr G (insLab ![a, b] i c) (insSgn ![true, true] i)‖
        ≤ ∑ _i : Fin 2, τ * ((W : ℝ)⁻¹ ^ 3 * (O * (W * ρ / η))) :=
          Finset.sum_le_sum fun i _ => hi i
      _ = _ := by simp; ring
  calc gammaG g * W * ‖∑ i : Fin 2, ∑ c : Fin L,
        (loopTr G ![c] ![(![true, true] : Fin 2 → Bool) i] -
          sgnScalar m ((![true, true] : Fin 2 → Bool) i)) *
        loopTr G (insLab ![a, b] i c) (insSgn ![true, true] i)‖
      ≤ gammaG g * W * (2 * τ * ((W : ℝ)⁻¹ ^ 3 * (O * (W * ρ / η)))) :=
        mul_le_mul_of_nonneg_left hsum hγW
    _ = _ := by ring

/-- The bracket (5.9) [gc:eq:bracket] of `ℒ₂(a,b;+,+)` is `(γ/W) Σ_c ‖Z_{cc}‖²_HS` with
`Z = G E_a G E_b G + G E_b G E_a G`. -/
private lemma step3s_gamma_eq (g E : ℝ) (m : ℂ) (hm : 0 < m.im) (hW : 1 ≤ W) {u : ℝ}
    (hu : u < 1) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    (a b : Fin L) :
    blockGamma W L (gammaG g) (resLoop g E m ![a, b] ![true, true] u)
        (resLoop g E m ![a, b] ![true, true] u) M =
      ((gammaG g / W : ℝ) : ℂ) * ∑ c, ((step3s_hs (blockOf
        (resolventMat M (zChar g E m u) * blockE W L a *
            (resolventMat M (zChar g E m u) * blockE W L b * resolventMat M (zChar g E m u)) +
          resolventMat M (zChar g E m u) * blockE W L b *
            (resolventMat M (zChar g E m u) * blockE W L a * resolventMat M (zChar g E m u)))
        c c) : ℝ) : ℂ) := by
  rw [blockGamma_loopTr g E m hm hu hM]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  set G := resolventMat M (zChar g E m u)
  have hB0 : loopB G ![a, b] ![true, true] 0 = G * blockE W L a * (G * blockE W L b * G) := by
    simp [loopB, List.ofFn_succ, sgnMat, Matrix.mul_assoc]
  have hB1 : loopB G ![a, b] ![true, true] 1 = G * blockE W L b * (G * blockE W L a * G) := by
    simp [loopB, List.ofFn_succ, sgnMat, Matrix.mul_assoc]
  rw [← step3s_trace_proj hW c]
  simp only [Fin.sum_univ_two, hB0, hB1, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul,
    Matrix.trace_add]
  ring

/-- The bracket (5.9) [gc:eq:bracket] of `ℒ₂(a,b;+,+)` at a good point:
`Γ ≤ 4(γ/W) W⁻⁴ O⁴ (Wρ/η)`, by the Ward identity (5.11) [gc:eq:ward]. -/
private theorem step3s_gamma_le (g E : ℝ) (m : ℂ) (hm : 0 < m.im) (hW : 1 ≤ W) {u : ℝ}
    (hu : u < 1) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    {O ρ : ℝ} (hO : 0 ≤ O)
    (hop : ∀ x y, ‖blockOf (resolventMat M (zChar g E m u)) x y‖ ≤ O)
    (hden : ∀ x, (blockTr (resolventMat M (zChar g E m u)) x x).im ≤ ρ) (a b : Fin L) :
    ‖blockGamma W L (gammaG g) (resLoop g E m ![a, b] ![true, true] u)
        (resLoop g E m ![a, b] ![true, true] u) M‖ ≤
      4 * (gammaG g / W) * ((W : ℝ)⁻¹ ^ 4 * O ^ 4 * (W * ρ / (zChar g E m u).im)) := by
  have hz : 0 < (zChar g E m u).im := by
    rw [im_zChar]; exact etaChar_pos g m hm hu
  set G := resolventMat M (zChar g E m u) with hG
  set η := (zChar g E m u).im with hη
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hward := fun x => step3s_ward hW M hM (zChar g E m u) hz x
  have hX : ∀ x, W * (blockTr G x x).im / η ≤ W * ρ / η := fun x => by
    have := hden x
    gcongr
  have hhs0 : ∀ x y, 0 ≤ blockHS2 G x y := fun x y => by unfold blockHS2; positivity
  rw [step3s_gamma_eq g E m hm hW hu hM a b, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), ← Complex.ofReal_sum, Complex.norm_real,
    Real.norm_of_nonneg (Finset.sum_nonneg fun c _ => step3s_hs_nonneg _)]
  have hk : ‖(W : ℂ)⁻¹ * (W : ℂ)⁻¹‖ ^ 2 = ((W : ℝ)⁻¹) ^ 4 := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]; ring
  have hc : ∀ c, step3s_hs (blockOf (G * blockE W L a * (G * blockE W L b * G) +
      G * blockE W L b * (G * blockE W L a * G)) c c) ≤
      2 * ((W : ℝ)⁻¹ ^ 4 * O ^ 4) * (blockHS2 G c a + blockHS2 G c b) := by
    intro c
    rw [step3s_blockOf_add, step3s_blockOf_five, step3s_blockOf_five]
    refine (step3s_hs_add_le _ _).trans ?_
    rw [step3s_hs_smul, step3s_hs_smul, hk]
    have hprod : ∀ x y z : Fin L, ‖blockOf G x y * blockOf G y z‖ ^ 2 ≤ O ^ 4 := by
      intro x y z
      have h1 := step3s_opNorm_mul_le (blockOf G x y) (blockOf G y z)
      have h2 : ‖blockOf G x y‖ * ‖blockOf G y z‖ ≤ O * O :=
        mul_le_mul (hop x y) (hop y z) (norm_nonneg _) hO
      have h3 : ‖blockOf G x y * blockOf G y z‖ ≤ O ^ 2 := by nlinarith
      have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
      calc _ ≤ (O ^ 2) ^ 2 := h4
        _ = O ^ 4 := by ring
    have e0 := step3s_hs_mul_right (blockOf G c a) (blockOf G a b * blockOf G b c)
    have e1 := step3s_hs_mul_right (blockOf G c b) (blockOf G b a * blockOf G a c)
    rw [step3s_hs_blockOf] at e0 e1
    have f0 : step3s_hs (blockOf G c a * (blockOf G a b * blockOf G b c)) ≤
        O ^ 4 * blockHS2 G c a :=
      e0.trans (mul_le_mul_of_nonneg_right (hprod a b c) (hhs0 c a))
    have f1 : step3s_hs (blockOf G c b * (blockOf G b a * blockOf G a c)) ≤
        O ^ 4 * blockHS2 G c b :=
      e1.trans (mul_le_mul_of_nonneg_right (hprod b a c) (hhs0 c b))
    have hW4 : (0 : ℝ) ≤ ((W : ℝ)⁻¹) ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left f0 hW4, mul_le_mul_of_nonneg_left f1 hW4]
  calc gammaG g / W * ∑ c, step3s_hs (blockOf (G * blockE W L a * (G * blockE W L b * G) +
        G * blockE W L b * (G * blockE W L a * G)) c c)
      ≤ gammaG g / W * ∑ c, 2 * ((W : ℝ)⁻¹ ^ 4 * O ^ 4) * (blockHS2 G c a + blockHS2 G c b) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => hc c) (by positivity)
    _ = gammaG g / W * (2 * ((W : ℝ)⁻¹ ^ 4 * O ^ 4) *
          (∑ c, blockHS2 G c a + ∑ c, blockHS2 G c b)) := by
        rw [← Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ gammaG g / W * (2 * ((W : ℝ)⁻¹ ^ 4 * O ^ 4) * (W * ρ / η + W * ρ / η)) := by
        gcongr
        · exact ((hward a).1).le.trans (hX a)
        · exact ((hward b).1).le.trans (hX b)
    _ = _ := by ring

/-- `Re ℒ₂(a,b;+,-) ≥ 0`. -/
private lemma step3s_pm_re_nonneg (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) :
    0 ≤ (loopTr X ![a, b] ![true, false]).re := by
  rw [step3s_loopTr_pm, Complex.ofReal_re]
  have : 0 ≤ blockHS2 X b a := by unfold blockHS2; positivity
  positivity

/-- The majorant `|ℒ₂(c,b;+,+)| ≤ (ℒ₂(c,b;+,-) ℒ₂(b,c;+,-))^{1/2}` with the mixed pairs
bounded by their primitive loops plus `e`. -/
private theorem step3s_pp_le_maj (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (k : Fin L →
    Fin L → ℝ) (e : Fin L → Fin L → ℝ)
    (he : ∀ x y, ‖loopTr X ![x, y] ![true, false] - (k x y : ℂ)‖ ≤ e x y) (c b : Fin L) :
    ‖loopTr X ![c, b] ![true, true]‖ ≤
      Real.sqrt ((k c b + e c b) * (k b c + e b c)) := by
  refine (norm_loopTr_pp_le X c b).trans (Real.sqrt_le_sqrt ?_)
  have hre : ∀ x y, (loopTr X ![x, y] ![true, false]).re ≤ k x y + e x y := by
    intro x y
    have h1 := Complex.re_le_norm (loopTr X ![x, y] ![true, false] - (k x y : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at h1
    linarith [he x y]
  exact mul_le_mul (hre c b) (hre b c) (step3s_pm_re_nonneg X b c)
    ((step3s_pm_re_nonneg X c b).trans (hre c b))

/-- The sum of the majorants: with the kernel `K = P(I - uP)⁻¹` of row and column sums
`(1-u)⁻¹` and `Σ_c e(c,b), Σ_c e(b,c) ≤ S`,
`γW Σ_c ((K(c,b)/γW + e(c,b))(K(b,c)/γW + e(b,c)))^{1/2} ≤ (1-u)⁻¹ + γW S`. -/
private theorem step3s_maj_sum {γW u S : ℝ} (hγW : 0 < γW) (K : Fin L → Fin L → ℝ)
    (hK0 : ∀ x y, 0 ≤ K x y) (hKr : ∀ x, ∑ y, K x y = (1 - u)⁻¹) (hKs : ∀ x y, K x y = K y x)
    (e : Fin L → Fin L → ℝ) (he0 : ∀ x y, 0 ≤ e x y)
    (hS : ∀ x, ∑ y, e y x ≤ S ∧ ∑ y, e x y ≤ S) (b : Fin L) :
    γW * ∑ c, Real.sqrt ((γW⁻¹ * K c b + e c b) * (γW⁻¹ * K b c + e b c)) ≤
      (1 - u)⁻¹ + γW * S := by
  have hγi : 0 ≤ γW⁻¹ := (inv_pos.mpr hγW).le
  have hx : ∀ c, 0 ≤ γW⁻¹ * K c b + e c b := fun c =>
    add_nonneg (mul_nonneg hγi (hK0 c b)) (he0 c b)
  have hy : ∀ c, 0 ≤ γW⁻¹ * K b c + e b c := fun c =>
    add_nonneg (mul_nonneg hγi (hK0 b c)) (he0 b c)
  have hsx : ∑ c, (γW⁻¹ * K c b + e c b) ≤ γW⁻¹ * (1 - u)⁻¹ + S := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have : ∑ c, K c b = (1 - u)⁻¹ := by rw [← hKr b]; exact Finset.sum_congr rfl fun c _ => hKs c b
    rw [this]
    linarith [(hS b).1]
  have hsy : ∑ c, (γW⁻¹ * K b c + e b c) ≤ γW⁻¹ * (1 - u)⁻¹ + S := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hKr b]
    linarith [(hS b).2]
  have h := step3s_sum_sqrt_le _ _ hx hy hsx hsy
  have hsq : ∀ c, Real.sqrt ((γW⁻¹ * K c b + e c b) * (γW⁻¹ * K b c + e b c)) =
      Real.sqrt (γW⁻¹ * K c b + e c b) * Real.sqrt (γW⁻¹ * K b c + e b c) := fun c =>
    Real.sqrt_mul (hx c) _
  simp only [hsq]
  calc γW * ∑ c, Real.sqrt (γW⁻¹ * K c b + e c b) * Real.sqrt (γW⁻¹ * K b c + e b c)
      ≤ γW * (γW⁻¹ * (1 - u)⁻¹ + S) := mul_le_mul_of_nonneg_left h hγW.le
    _ = (1 - u)⁻¹ + γW * S := by field_simp

/-- The row sums of the same-sign kernel: `Σ_c |γ_gW 𝒦₂(u;a,c;+,+)| ≤ C²` from the Dyson bounds
(6.2) [fo:eq:propagation-dyson]. -/
private theorem step3s_Q_row (g : ℝ) (W L : ℕ) (hW : 1 ≤ W) (E : ℝ) (m : ℂ) (u C : ℝ)
    (hC : 0 ≤ C)
    (hrow1 : ∀ a, gammaG g * ∑ b, (‖dysonMat (hopB g) (gammaG g) L E m a b‖ +
      ‖dysonMat (hopB g) (gammaG g) L E m a b‖ ^ 2) ≤ C)
    (hrow2 : ∀ a, ∑ b, ‖(1 - (u : ℂ) • pairQ (gammaG g)
      (dysonMat (hopB g) (gammaG g) L E m))⁻¹ a b‖ ≤ C) (a : Fin L) :
    ∑ c, ‖((gammaG g * W : ℝ) : ℂ) * primLoop g W L E m u ![a, c] ![true, true]‖ ≤ C * C := by
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hγW : ((gammaG g * W : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (mul_pos hγ hW0).ne'
  set Q := pairQ (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) with hQ
  set N := (1 - (u : ℂ) • Q)⁻¹ with hN
  have e : ∀ c, ((gammaG g * W : ℝ) : ℂ) * primLoop g W L E m u ![a, c] ![true, true] =
      (Q * N) a c := by
    intro c
    rw [primLoop_two_pp, ← mul_assoc, mul_inv_cancel₀ hγW, one_mul]
  simp only [e]
  have hQa : ∑ d, ‖Q a d‖ ≤ C := by
    refine le_trans ?_ (hrow1 a)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun d _ => ?_
    simp only [hQ, pairQ, Matrix.of_apply, norm_mul, Complex.norm_real, norm_pow,
      Real.norm_of_nonneg hγ.le]
    have : 0 ≤ ‖dysonMat (hopB g) (gammaG g) L E m a d‖ := norm_nonneg _
    nlinarith
  calc ∑ c, ‖(Q * N) a c‖ ≤ ∑ c, ∑ d, ‖Q a d‖ * ‖N d c‖ := by
        refine Finset.sum_le_sum fun c _ => ?_
        rw [Matrix.mul_apply]
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun d _ => norm_mul _ _
    _ = ∑ d, ‖Q a d‖ * ∑ c, ‖N d c‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun d _ => by rw [Finset.mul_sum]
    _ ≤ ∑ d, ‖Q a d‖ * C :=
        Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left (hrow2 d) (norm_nonneg _)
    _ = (∑ d, ‖Q a d‖) * C := by rw [Finset.sum_mul]
    _ ≤ C * C := mul_le_mul_of_nonneg_right hQa hC

/-- The generator of the same-sign pair at a point bounded by the light term, the same-sign kernel
row and a majorant `β` of `|ℒ₂(c,b;+,+)|`:
`|𝒢D₂(a,b)| ≤ |𝒲₂| + Σ_c |γW𝒦₂(a,c)| |D₂(c,b)| + Σ_c γW β_c |D₂(a,c)|`. -/
private theorem step3s_gen_split (g E : ℝ) (m : ℂ) (W L : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ L)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {u : ℝ} (hu : u ∈ Set.Ioo (-1 : ℝ) 1)
    {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian) (a b : Fin L)
    (β : Fin L → ℝ) (hβ : ∀ c, ‖resLoop g E m ![c, b] ![true, true] u M‖ ≤ β c) :
    ‖blockGen W L (gammaG g) (fun r N => resLoop g E m ![a, b] ![true, true] r N -
        primLoop g W L E m r ![a, b] ![true, true]) u M‖ ≤
      ‖lightW g E m ![a, b] ![true, true] u M‖ +
        ∑ c, ‖((gammaG g * W : ℝ) : ℂ) * primLoop g W L E m u ![a, c] ![true, true]‖ *
          ‖resLoop g E m ![c, b] ![true, true] u M - primLoop g W L E m u ![c, b] ![true, true]‖ +
        ∑ c, gammaG g * W * β c *
          ‖resLoop g E m ![a, c] ![true, true] u M -
            primLoop g W L E m u ![a, c] ![true, true]‖ := by
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hγW : 0 ≤ gammaG g * W := by positivity
  rw [step3s_blockGen g E m W L hW hL hm hu hM a b, add_assoc]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [mul_add]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [← mul_assoc, norm_mul]
  · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hγW]
    calc gammaG g * W * (‖resLoop g E m ![a, c] ![true, true] u M -
          primLoop g W L E m u ![a, c] ![true, true]‖ * ‖resLoop g E m ![c, b] ![true, true] u M‖)
        ≤ gammaG g * W * (‖resLoop g E m ![a, c] ![true, true] u M -
          primLoop g W L E m u ![a, c] ![true, true]‖ * β c) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hβ c) (norm_nonneg _)) hγW
      _ = _ := by ring

end Step3Rows

/-! ### Grönwall's inequality, moments and the moment comparison along good events -/

/-- `∫_s^u (1 - r)⁻¹ dr = log((1 - s)/(1 - u))` for `s, u < 1`. -/
private theorem step3s_int_inv {s u : ℝ} (hs : s < 1) (hu : u < 1) :
    ∫ r in s..u, (1 - r)⁻¹ = Real.log ((1 - s) / (1 - u)) := by
  rw [intervalIntegral.integral_comp_sub_left (fun x => x⁻¹) 1,
    integral_inv_of_pos (by linarith) (by linarith)]

/-- Grönwall's inequality for the rate `C + κ/(1 - r)` and the source `h/(1 - r)`: if
`F(u) ≤ c₀ + ∫_s^u ((C + κ/(1 - r)) F + h/(1 - r))` on `[s, v]`, then
`F(v) ≤ e^{C(v - s)} ((1 - s)/(1 - v))^κ (c₀ + h log((1 - s)/(1 - v)))`. -/
private theorem step3s_gronwall {s v C κ h c₀ : ℝ} (hsv : s ≤ v) (hv : v < 1) (F : ℝ → ℝ)
    (hF : ContinuousOn F (Set.Icc s v)) (hC : 0 ≤ C) (hκ : 0 ≤ κ) (hh : 0 ≤ h)
    (hint : ∀ u ∈ Set.Icc s v,
      F u ≤ c₀ + ∫ r in s..u, ((C + κ * (1 - r)⁻¹) * F r + h * (1 - r)⁻¹)) :
    F v ≤ Real.exp (C * (v - s)) * ((1 - s) / (1 - v)) ^ κ *
      (c₀ + h * Real.log ((1 - s) / (1 - v))) := by
  have hs1 : s < 1 := lt_of_le_of_lt hsv hv
  set φ : ℝ → ℝ := fun r => (C + κ * (1 - r)⁻¹) * F r + h * (1 - r)⁻¹ with hφ
  have hinvc : ContinuousOn (fun r : ℝ => (1 - r)⁻¹) (Set.Icc s v) :=
    (continuousOn_const.sub continuousOn_id).inv₀ fun r hr => by
      show (1 : ℝ) - r ≠ 0
      linarith [hr.2]
  have hφc : ContinuousOn φ (Set.Icc s v) :=
    ((continuousOn_const.add (continuousOn_const.mul hinvc)).mul hF).add
      (continuousOn_const.mul hinvc)
  have hφi : IntervalIntegrable φ MeasureTheory.volume s v :=
    (hφc.mono (by rw [Set.uIcc_of_le hsv])).intervalIntegrable
  set I : ℝ → ℝ := fun u => c₀ + ∫ r in s..u, φ r with hI
  set E : ℝ → ℝ := fun u => Real.exp (-(C * u)) * (1 - u) ^ κ with hE
  set Ψ : ℝ → ℝ := fun u => I u * E u + E s * h * Real.log (1 - u) with hΨ
  have hE0 : ∀ u, u < 1 → 0 < E u := fun u hu => by
    simp only [hE]; exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by linarith) _)
  have hEanti : ∀ u ∈ Set.Icc s v, E u ≤ E s := by
    intro u hu
    simp only [hE]
    refine mul_le_mul ?_ ?_ (Real.rpow_nonneg (by linarith [hu.2]) _) (Real.exp_pos _).le
    · exact Real.exp_le_exp.mpr (by nlinarith [hu.1])
    · exact Real.rpow_le_rpow (by linarith [hu.2]) (by linarith [hu.1]) hκ
  -- continuity of `Ψ`
  have hIc : ContinuousOn I (Set.Icc s v) := by
    have h := intervalIntegral.continuousOn_primitive_interval (μ := MeasureTheory.volume)
      (f := φ) (a := s) (b := v) (by rw [Set.uIcc_of_le hsv]; exact hφc.integrableOn_Icc)
    rw [Set.uIcc_of_le hsv] at h
    exact continuousOn_const.add h
  have hEc : ContinuousOn E (Set.Icc s v) := by
    refine ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn).mul ?_
    exact (continuousOn_const.sub continuousOn_id).rpow_const fun r hr =>
      Or.inl (show (1 : ℝ) - r ≠ 0 by linarith [hr.2])
  have hlogc : ContinuousOn (fun u : ℝ => Real.log (1 - u)) (Set.Icc s v) :=
    (continuousOn_const.sub continuousOn_id).log fun r hr =>
      show (1 : ℝ) - r ≠ 0 by linarith [hr.2]
  have hΨc : ContinuousOn Ψ (Set.Icc s v) :=
    (hIc.mul hEc).add (continuousOn_const.mul hlogc)
  -- the derivative on `(s, v)`
  have hder : ∀ u ∈ Set.Ioo s v, HasDerivAt Ψ
      (φ u * E u + I u * (-(C * E u) - κ * (1 - u)⁻¹ * E u) - E s * h * (1 - u)⁻¹) u := by
    intro u hu
    have hu1 : 0 < 1 - u := by linarith [hu.2]
    have hIu : HasDerivAt I (φ u) u := by
      have hmem : Set.Icc s v ∈ 𝓝 u := Icc_mem_nhds hu.1 hu.2
      have h1 : StronglyMeasurableAtFilter φ (𝓝 u) MeasureTheory.volume :=
        (hφc.mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo u hu
      have h2 : IntervalIntegrable φ MeasureTheory.volume s u :=
        (hφc.mono (by rw [Set.uIcc_of_le hu.1.le]; exact Set.Icc_subset_Icc le_rfl hu.2.le)
          ).intervalIntegrable
      have h3 : ContinuousAt φ u := hφc.continuousAt hmem
      exact (intervalIntegral.integral_hasDerivAt_right h2 h1 h3).const_add c₀
    have hEu : HasDerivAt E (-(C * E u) - κ * (1 - u)⁻¹ * E u) u := by
      have h1 : HasDerivAt (fun r : ℝ => Real.exp (-(C * r))) (Real.exp (-(C * u)) * (-C)) u := by
        have := ((hasDerivAt_id u).const_mul C).neg.exp
        simpa using this
      have h2 : HasDerivAt (fun r : ℝ => (1 - r) ^ κ) ((-1) * κ * (1 - u) ^ (κ - 1)) u := by
        have := ((hasDerivAt_id u).const_sub 1).rpow_const (p := κ) (Or.inl hu1.ne')
        simpa using this
      have h3 := h1.mul h2
      convert h3 using 1
      simp only [hE]
      rw [Real.rpow_sub_one hu1.ne']
      field_simp
      ring
    have hlog : HasDerivAt (fun r : ℝ => Real.log (1 - r)) (-(1 - u)⁻¹) u := by
      have h1 : HasDerivAt (fun r : ℝ => 1 - r) (-1) u := by
        simpa using (hasDerivAt_id u).const_sub 1
      have := h1.log hu1.ne'
      convert this using 1
      field_simp
    have h := (hIu.mul hEu).add (hlog.const_mul (E s * h))
    convert h using 1
    ring
  have hanti : AntitoneOn Ψ (Set.Icc s v) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc s v) hΨc ?_ ?_
    · rw [interior_Icc]
      exact fun u hu => (hder u hu).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro u hu
      rw [(hder u hu).deriv]
      have hu1 : 0 < 1 - u := by linarith [hu.2]
      have hFI : F u ≤ I u := hint u ⟨hu.1.le, hu.2.le⟩
      have hEu0 := hE0 u (by linarith [hu.2])
      have hEus := hEanti u ⟨hu.1.le, hu.2.le⟩
      have hk : 0 ≤ C + κ * (1 - u)⁻¹ := by positivity
      have e : φ u * E u + I u * (-(C * E u) - κ * (1 - u)⁻¹ * E u) - E s * h * (1 - u)⁻¹ =
          (C + κ * (1 - u)⁻¹) * E u * (F u - I u) + h * (1 - u)⁻¹ * (E u - E s) := by
        simp only [hφ]; ring
      rw [e]
      have h1 : (C + κ * (1 - u)⁻¹) * E u * (F u - I u) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hk hEu0.le) (by linarith)
      have h2 : h * (1 - u)⁻¹ * (E u - E s) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
      linarith
  have hsI : s ∈ Set.Icc s v := ⟨le_rfl, hsv⟩
  have hvI : v ∈ Set.Icc s v := ⟨hsv, le_rfl⟩
  have hΨsv := hanti hsI hvI hsv
  have hIs : I s = c₀ := by simp [hI]
  simp only [hΨ, hIs] at hΨsv
  have hEv := hE0 v hv
  have hEs := hE0 s hs1
  have hlog : Real.log (1 - v) = Real.log (1 - s) - Real.log ((1 - s) / (1 - v)) := by
    rw [Real.log_div (by linarith) (by linarith)]; ring
  rw [hlog] at hΨsv
  have hIv : I v * E v ≤ E s * (c₀ + h * Real.log ((1 - s) / (1 - v))) := by nlinarith
  have hFv : F v ≤ I v := hint v hvI
  have hratio : E s / E v = Real.exp (C * (v - s)) * ((1 - s) / (1 - v)) ^ κ := by
    simp only [hE]
    rw [Real.div_rpow (by linarith) (by linarith)]
    have : Real.exp (C * (v - s)) = Real.exp (-(C * s)) / Real.exp (-(C * v)) := by
      rw [← Real.exp_sub]; ring_nf
    rw [this]
    field_simp
  calc F v ≤ I v := hFv
    _ ≤ E s * (c₀ + h * Real.log ((1 - s) / (1 - v))) / E v := by
        rw [le_div_iff₀ hEv]; linarith
    _ = E s / E v * (c₀ + h * Real.log ((1 - s) / (1 - v))) := by ring
    _ = _ := by rw [hratio]


section Step3Lp

variable {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]

/-- For a bounded nonnegative function, `‖h‖_{L^q} = (E h^q)^{1/q}`. -/
private theorem step3s_eLpNorm_eq (q : ℕ) (hq : 1 ≤ q) (h : Ω' → ℝ)
    (hm : AEStronglyMeasurable h P) (h0 : ∀ x, 0 ≤ h x) (hb : ∃ K, ∀ x, h x ≤ K) :
    eLpNorm h q P = ENNReal.ofReal ((∫ x, h x ^ q ∂P) ^ (1 / (q : ℝ))) := by
  obtain ⟨K, hK⟩ := hb
  have hmem : MemLp h q P := MemLp.of_bound hm K (Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (h0 x)]; exact hK x)
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  rw [hmem.eLpNorm_eq_integral_rpow_norm hq0 (ENNReal.natCast_ne_top q)]
  congr 2
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [ENNReal.toReal_natCast]
    rw [Real.norm_of_nonneg (h0 x), Real.rpow_natCast]
  · simp

/-- Minkowski's inequality in `L^q` for a pointwise bound by a constant, a finite nonnegative
combination and one more function. -/
private theorem step3s_mink {S : Type*} [Fintype S] (q : ℕ) (hq : 1 ≤ q) (f e : Ω' → ℝ)
    (g : S → Ω' → ℝ) (c₀ : ℝ) (c : S → ℝ) (hc₀ : 0 ≤ c₀) (hc : ∀ i, 0 ≤ c i)
    (hf : AEStronglyMeasurable f P) (hf0 : ∀ x, 0 ≤ f x)
    (he : AEStronglyMeasurable e P) (he0 : ∀ x, 0 ≤ e x) (heb : ∃ K, ∀ x, e x ≤ K)
    (hg : ∀ i, AEStronglyMeasurable (g i) P) (hg0 : ∀ i x, 0 ≤ g i x)
    (hgb : ∀ i, ∃ K, ∀ x, g i x ≤ K) (hle : ∀ x, f x ≤ c₀ + ∑ i, c i * g i x + e x) :
    (∫ x, f x ^ q ∂P) ^ (1 / (q : ℝ)) ≤
      c₀ + ∑ i, c i * (∫ x, g i x ^ q ∂P) ^ (1 / (q : ℝ)) + (∫ x, e x ^ q ∂P) ^ (1 / (q : ℝ)) := by
  have hq1 : (1 : ℝ≥0∞) ≤ q := by exact_mod_cast hq
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  choose Kg hKg using hgb
  obtain ⟨Ke, hKe⟩ := heb
  have hfb : ∃ K, ∀ x, f x ≤ K :=
    ⟨c₀ + ∑ i, c i * Kg i + Ke, fun x => (hle x).trans (by
      gcongr with i
      · exact hc i
      · exact hKg i x
      · exact hKe x)⟩
  have hN : ∀ (h : Ω' → ℝ), AEStronglyMeasurable h P → (∀ x, 0 ≤ h x) → (∃ K, ∀ x, h x ≤ K) →
      0 ≤ (∫ x, h x ^ q ∂P) ^ (1 / (q : ℝ)) := fun h _ h0 _ =>
    Real.rpow_nonneg (integral_nonneg fun x => pow_nonneg (h0 x) q) _
  have hsum_m : AEStronglyMeasurable (fun x => ∑ i, c i * g i x) P :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hg i).const_mul (c i)
  have h1 : eLpNorm f q P ≤ eLpNorm (fun x => c₀ + ∑ i, c i * g i x + e x) q P := by
    refine eLpNorm_mono hf fun x => ?_
    rw [Real.norm_of_nonneg (hf0 x), Real.norm_of_nonneg (by
      have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => mul_nonneg (hc i) (hg0 i x)
      linarith [he0 x])]
    exact hle x
  have h2 : eLpNorm (fun x => c₀ + ∑ i, c i * g i x + e x) q P ≤
      eLpNorm (fun _ => c₀) q P + eLpNorm (fun x => ∑ i, c i * g i x) q P + eLpNorm e q P := by
    have e1 : (fun x => c₀ + ∑ i, c i * g i x + e x) =
        ((fun _ => c₀) + fun x => ∑ i, c i * g i x) + e := rfl
    rw [e1]
    refine (eLpNorm_add_le hq1).trans ?_
    gcongr
    exact eLpNorm_add_le hq1
  have h3 : eLpNorm (fun x => ∑ i, c i * g i x) q P ≤
      ∑ i, ENNReal.ofReal (c i) * eLpNorm (g i) q P := by
    have e1 : (fun x => ∑ i, c i * g i x) = ∑ i, (c i) • g i := by
      funext x; simp [Finset.sum_apply]
    rw [e1]
    refine (eLpNorm_sum_le hq1).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (hc i)]
  have h4 : eLpNorm (fun _ : Ω' => c₀) q P = ENNReal.ofReal c₀ := by
    rw [eLpNorm_const _ hq0 (IsProbabilityMeasure.ne_zero P), measure_univ, ENNReal.one_rpow,
      mul_one, Real.enorm_eq_ofReal hc₀]
  rw [step3s_eLpNorm_eq P q hq f hf hf0 hfb] at h1
  rw [h4, step3s_eLpNorm_eq P q hq e he he0 ⟨Ke, hKe⟩] at h2
  have h5 : ∀ i, eLpNorm (g i) q P =
      ENNReal.ofReal ((∫ x, g i x ^ q ∂P) ^ (1 / (q : ℝ))) := fun i =>
    step3s_eLpNorm_eq P q hq (g i) (hg i) (hg0 i) ⟨Kg i, hKg i⟩
  simp only [h5] at h3
  have hall := h1.trans (h2.trans (add_le_add (add_le_add le_rfl h3) le_rfl))
  have hNg : ∀ i, 0 ≤ (∫ x, g i x ^ q ∂P) ^ (1 / (q : ℝ)) := fun i =>
    hN (g i) (hg i) (hg0 i) ⟨Kg i, hKg i⟩
  have hNe := hN e he he0 ⟨Ke, hKe⟩
  have hsum0 : 0 ≤ ∑ i, c i * (∫ x, g i x ^ q ∂P) ^ (1 / (q : ℝ)) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (hNg i)
  have key : ENNReal.ofReal c₀ + ∑ i, ENNReal.ofReal (c i) *
      ENNReal.ofReal ((∫ x, g i x ^ q ∂P) ^ (1 / (q : ℝ))) +
        ENNReal.ofReal ((∫ x, e x ^ q ∂P) ^ (1 / (q : ℝ))) =
      ENNReal.ofReal (c₀ + ∑ i, c i * (∫ x, g i x ^ q ∂P) ^ (1 / (q : ℝ)) +
        (∫ x, e x ^ q ∂P) ^ (1 / (q : ℝ))) := by
    rw [ENNReal.ofReal_add (add_nonneg hc₀ hsum0) hNe, ENNReal.ofReal_add hc₀ hsum0,
      ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hc i) (hNg i))]
    simp only [ENNReal.ofReal_mul (hc _)]
  rw [key] at hall
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (add_nonneg hc₀ hsum0) hNe)).mp hall

/-- The off-set term: `(E (1_T f)^q)^{1/q} ≤ (√M √δ)^{1/q}` when `E f^{2q} ≤ M`,
`ℙ(T) ≤ δ`. -/
private theorem step3s_off (q : ℕ) (hq : 1 ≤ q) (f : Ω' → ℝ) (hfm : AEStronglyMeasurable f P)
    (hf0 : ∀ x, 0 ≤ f x) (hfb : ∃ K, ∀ x, f x ≤ K) {T : Set Ω'} (hT : MeasurableSet T)
    {δ M : ℝ} (hδ : 0 ≤ δ) (hTδ : P T ≤ ENNReal.ofReal δ) (hM : ∫ x, f x ^ (2 * q) ∂P ≤ M) :
    (∫ x, (T.indicator f x) ^ q ∂P) ^ (1 / (q : ℝ)) ≤
      (Real.sqrt M * Real.sqrt δ) ^ (1 / (q : ℝ)) := by
  obtain ⟨K, hK⟩ := hfb
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hfq_m : AEStronglyMeasurable (fun x => f x ^ q) P := hfm.pow q
  have hsq : ∀ x, (f x ^ q) ^ 2 = f x ^ (2 * q) := fun x => by rw [← pow_mul, mul_comm]
  have hK0 : ∀ x, f x ^ q ≤ K ^ q := fun x => pow_le_pow_left₀ (hf0 x) (hK x) q
  have hmem : MemLp (fun x => f x ^ q) 2 P := MemLp.of_bound hfq_m (K ^ q)
    (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (pow_nonneg (hf0 x) q)]; exact hK0 x)
  have hM0 : 0 ≤ M := (integral_nonneg fun x => pow_nonneg (hf0 x) _).trans hM
  have hcs := lemmaNOffset_cs P (fun x => f x ^ q) hmem hT (K := Real.sqrt M) (δ := δ)
    (Real.sqrt_nonneg _) (by rw [Real.sq_sqrt hM0]; simpa only [hsq] using hM)
    (by rw [measureReal_def]; exact ENNReal.toReal_le_of_le_ofReal hδ hTδ)
  have e : ∀ x, (T.indicator f x) ^ q = T.indicator (fun x => |f x ^ q|) x := by
    intro x
    by_cases hx : x ∈ T
    · simp [Set.indicator_of_mem hx, abs_of_nonneg (hf0 x)]
    · simp [Set.indicator_of_notMem hx, zero_pow (by omega : q ≠ 0)]
  simp only [e]
  have hI0 : 0 ≤ ∫ x, T.indicator (fun x => |f x ^ q|) x ∂P :=
    integral_nonneg fun x => Set.indicator_nonneg (fun _ _ => abs_nonneg _) x
  exact Real.rpow_le_rpow hI0 hcs (by positivity)

end Step3Lp


section Step3Jet

/-- Along a line, `e ↦ G(y + e v)` has first derivative `DG(y) v` at `0`. -/
private theorem step3s_deriv_line {ι : Type*} [Fintype ι] {G : (ι → ℝ) → ℂ}
    {DG : (ι → ℝ) → ((ι → ℝ) →L[ℝ] ℂ)} (hD : ∀ x, HasFDerivAt G (DG x) x) (y v : ι → ℝ) :
    deriv (fun e : ℝ => G (y + e • v)) 0 = DG y v := by
  have hl : HasDerivAt (fun e : ℝ => y + e • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have h := ((hD (y + (0 : ℝ) • v)).comp_hasDerivAt (0 : ℝ) hl)
  have h2 : HasDerivAt (fun e : ℝ => G (y + e • v)) (DG y v) 0 := by
    simpa [Function.comp_def] using h
  exact h2.deriv

/-- Along a line, `e ↦ G(y + e v)` has second derivative `D²G(y) v v` at `0`. -/
private theorem step3s_iteratedDeriv_line {ι : Type*} [Fintype ι] {G : (ι → ℝ) → ℂ}
    {DG : (ι → ℝ) → ((ι → ℝ) →L[ℝ] ℂ)} {D2G : (ι → ℝ) → ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℂ)}
    (hD : ∀ x, HasFDerivAt G (DG x) x) (hD2 : ∀ x, HasFDerivAt DG (D2G x) x) (y v : ι → ℝ) :
    iteratedDeriv 2 (fun e : ℝ => G (y + e • v)) 0 = D2G y v v := by
  have hl : ∀ e : ℝ, HasDerivAt (fun e : ℝ => y + e • v) v e := fun e => by
    simpa using ((hasDerivAt_id e).smul_const v).const_add y
  have h1 : deriv (fun e : ℝ => G (y + e • v)) = fun e => DG (y + e • v) v :=
    funext fun e => ((hD _).comp_hasDerivAt e (hl e)).deriv
  have h2 : HasDerivAt (fun e : ℝ => DG (y + e • v) v) (D2G y v v) 0 := by
    have h := ((hD2 _).comp_hasDerivAt 0 (hl 0)).clm_apply (hasDerivAt_const (0 : ℝ) v)
    simpa using h
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1, h2.deriv]

/-- A function jointly continuous on `(a,b) × ℝ^ι` is continuous in `x` at each time in `(a,b)`. -/
private theorem step3s_slice {ι E : Type*} [TopologicalSpace E] {g : ℝ → (ι → ℝ) → E}
    {a b : ℝ} (hg : ContinuousOn (Function.uncurry g) (Set.Ioo a b ×ˢ Set.univ)) {r : ℝ}
    (hr : r ∈ Set.Ioo a b) : Continuous (g r) :=
  hg.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hr, trivial⟩

/-- Jet data of a member of the class at a time `u ∈ (a,b)`: differentiability in time, `C²`
regularity in space, and continuity and boundedness of `F u`, `𝒢F u`, `Γ(F u, F u)`. -/
private theorem step3s_class_jet {ι : Type*} [Fintype ι] {F : ℝ → (ι → ℝ) → ℂ} {a b : ℝ}
    (hF : HeatClass F a b) {u : ℝ} (hu : u ∈ Set.Ioo a b) (σ2 : ℝ) :
    (∀ y, DifferentiableAt ℝ (fun r => F r y) u) ∧ ContDiff ℝ 2 (F u) ∧
      (∃ C : ℝ, ∀ y, ‖F u y‖ ≤ C) ∧
      (Continuous (coordGen σ2 F u) ∧ ∃ C : ℝ, ∀ y, ‖coordGen σ2 F u y‖ ≤ C) ∧
      (Continuous (coordGamma σ2 (F u) (F u)) ∧
        ∃ C : ℝ, ∀ y, ‖coordGamma σ2 (F u) (F u) y‖ ≤ C) := by
  obtain ⟨hc, ⟨C₀, hC₀⟩, ⟨Fu, hu', hcu, C₁, hC₁⟩, ⟨DF, D2F, hD, hD2, hcD, hcD2, C₂, hC₂⟩⟩ := hF
  have hei : ∀ i : ι, ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖ ≤ 1 := fun i => by
    rw [Pi.norm_single]; simp
  have hDc : Continuous (DF u) := step3s_slice hcD hu
  have hD2c : Continuous (D2F u) := step3s_slice hcD2 hu
  have hFuc : Continuous (Fu u) := step3s_slice hcu hu
  have hC₂0 : 0 ≤ C₂ := (norm_nonneg _).trans (hC₂ u hu 0).1
  have hb1 : ∀ (y : ι → ℝ) (i : ι), ‖DF u y (Pi.single i 1)‖ ≤ C₂ := fun y i =>
    calc ‖DF u y (Pi.single i 1)‖ ≤ ‖DF u y‖ * ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖ :=
          (DF u y).le_opNorm _
      _ ≤ C₂ * 1 := mul_le_mul (hC₂ u hu y).1 (hei i) (norm_nonneg _) hC₂0
      _ = C₂ := mul_one _
  have hb2 : ∀ (y : ι → ℝ) (i : ι), ‖D2F u y (Pi.single i 1) (Pi.single i 1)‖ ≤ C₂ := fun y i =>
    calc ‖D2F u y (Pi.single i 1) (Pi.single i 1)‖
        ≤ ‖D2F u y (Pi.single i 1)‖ * ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖ := (D2F u y _).le_opNorm _
      _ ≤ (‖D2F u y‖ * ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖) * 1 :=
          mul_le_mul ((D2F u y).le_opNorm _) (hei i) (norm_nonneg _) (by positivity)
      _ ≤ (C₂ * 1) * 1 := by
          gcongr
          · exact (hC₂ u hu y).2
          · exact hei i
      _ = C₂ := by ring
  have hgen : ∀ y, coordGen σ2 F u y =
      Fu u y + ((σ2 / 2 : ℝ) : ℂ) * ∑ i, D2F u y (Pi.single i 1) (Pi.single i 1) := by
    intro y
    simp only [coordGen, (hu' u hu y).deriv]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    exact step3s_iteratedDeriv_line (hD u hu) (hD2 u hu) y _
  have hgam : ∀ y, coordGamma σ2 (F u) (F u) y =
      (σ2 : ℂ) * ∑ i, DF u y (Pi.single i 1) * star (DF u y (Pi.single i 1)) := by
    intro y
    simp only [coordGamma, step3s_deriv_line (hD u hu)]
  have hFdiff : Differentiable ℝ (F u) := fun x => (hD u hu x).differentiableAt
  have hDdiff : Differentiable ℝ (DF u) := fun x => (hD2 u hu x).differentiableAt
  refine ⟨fun y => (hu' u hu y).differentiableAt, ?_, ⟨C₀, fun y => hC₀ u hu y⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩⟩
  · rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_fderiv]
    refine ⟨hFdiff, by simp, ?_⟩
    have hfd : fderiv ℝ (F u) = DF u := funext fun x => (hD u hu x).fderiv
    rw [hfd, contDiff_one_iff_fderiv]
    refine ⟨hDdiff, ?_⟩
    have : fderiv ℝ (DF u) = D2F u := funext fun x => (hD2 u hu x).fderiv
    rw [this]; exact hD2c
  · have : coordGen σ2 F u = fun y => Fu u y + ((σ2 / 2 : ℝ) : ℂ) *
        ∑ i, D2F u y (Pi.single i 1) (Pi.single i 1) := funext hgen
    rw [this]
    refine hFuc.add (continuous_const.mul (continuous_finsetSum _ fun i _ => ?_))
    exact (hD2c.clm_apply continuous_const).clm_apply continuous_const
  · refine ⟨C₁ + |σ2 / 2| * (Fintype.card ι * C₂), fun y => ?_⟩
    rw [hgen]
    refine (norm_add_le _ _).trans (add_le_add (hC₁ u hu y) ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖D2F u y (Pi.single i 1) (Pi.single i 1)‖ ≤ ∑ _i : ι, C₂ :=
          Finset.sum_le_sum fun i _ => hb2 y i
      _ = Fintype.card ι * C₂ := by simp
  · have : coordGamma σ2 (F u) (F u) = fun y => (σ2 : ℂ) *
        ∑ i, DF u y (Pi.single i 1) * star (DF u y (Pi.single i 1)) := funext hgam
    rw [this]
    refine continuous_const.mul (continuous_finsetSum _ fun i _ => ?_)
    exact (hDc.clm_apply continuous_const).mul
      (continuous_star.comp (hDc.clm_apply continuous_const))
  · refine ⟨|σ2| * (Fintype.card ι * (C₂ * C₂)), fun y => ?_⟩
    rw [hgam, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖DF u y (Pi.single i 1) * star (DF u y (Pi.single i 1))‖ ≤ ∑ _i : ι, C₂ * C₂ :=
          Finset.sum_le_sum fun i _ => by
            rw [norm_mul, norm_star]
            exact mul_le_mul (hb1 y i) (hb1 y i) (norm_nonneg _) hC₂0
      _ = Fintype.card ι * (C₂ * C₂) := by simp

/-- `|Y|^{2p}` lies in the class when `Y` does. -/
private theorem step3s_class_normPow {ι : Type*} [Fintype ι] {Y : ℝ → (ι → ℝ) → ℂ} {a b : ℝ}
    (hY : HeatClass Y a b) (p : ℕ) (hp : 1 ≤ p) :
    HeatClass (fun r z => ((‖Y r z‖ ^ (2 * p) : ℝ) : ℂ)) a b := by
  have h0 : HeatClass (fun r z => Y r z * star (Y r z)) a b := hY.mul hY.star
  have hpow : ∀ n : ℕ, 1 ≤ n → HeatClass (fun r z => (Y r z * star (Y r z)) ^ n) a b := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simpa using h0
    | succ n hn ih =>
      have := ih.mul h0
      simpa [pow_succ] using this
  have hfun : (fun r z => ((‖Y r z‖ ^ (2 * p) : ℝ) : ℂ)) =
      fun r z => (Y r z * star (Y r z)) ^ p := by
    funext r z
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow,
      ← pow_mul]
  rw [hfun]
  exact hpow p hp

/-- The moment `u ↦ E|Y_u(√(uσ²) ξ)|^{2p}` of a member of the class is continuous on `[0, v]`. -/
private theorem step3s_moment_cont {ι : Type*} [Fintype ι] (σ2 : ℝ) (hσ2 : 0 ≤ σ2)
    {Y : ℝ → (ι → ℝ) → ℂ} {a b v : ℝ} (ha : a < 0) (hv : 0 ≤ v) (hvb : v < b)
    (hY : HeatClass Y a b) (p : ℕ) (hp : 1 ≤ p) :
    ContinuousOn (fun u => (∫ x, ‖Y u (Real.sqrt (u * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι)) ^
      (1 / (2 * (p : ℝ)))) (Set.Icc 0 v) := by
  have h := (heat_generator σ2 hσ2 _ ha hv hvb (step3s_class_normPow hY p hp)).1
  have e : (fun u => ∫ x, ((‖Y u (Real.sqrt (u * σ2) • x)‖ ^ (2 * p) : ℝ) : ℂ) ∂(stdGauss ι)) =
      fun u => (((∫ x, ‖Y u (Real.sqrt (u * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι)) : ℝ) : ℂ) :=
    funext fun u => integral_ofReal
  rw [e] at h
  have h2 : ContinuousOn (fun u => ∫ x, ‖Y u (Real.sqrt (u * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι))
      (Set.Icc 0 v) := by
    have := Complex.continuous_re.comp_continuousOn h
    exact this.congr fun u _ => by simp
  exact h2.rpow_const fun u _ => Or.inr (by positivity)

end Step3Jet

section Step3Core

/-- A moment split along a good event: if `0 ≤ f ≤ A₀` off a measurable set `T` with
`ℙ(T) ≤ δ` and `E f^{2q} ≤ M`, then `‖f‖_q ≤ A₀ + (M^{1/2} δ^{1/2})^{1/q}`. -/
private theorem step3s_moment_split {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] (f : Ω' → ℝ) (hfm : AEStronglyMeasurable f P) (hf0 : ∀ x, 0 ≤ f x)
    (hfb : ∃ K, ∀ x, f x ≤ K)
    (q : ℕ) (hq : 1 ≤ q) {T : Set Ω'} (hT : MeasurableSet T) {δ A₀ Mf : ℝ} (hδ : 0 ≤ δ)
    (hTδ : P T ≤ ENNReal.ofReal δ) (hA₀ : 0 ≤ A₀) (hgood : ∀ x, x ∉ T → f x ≤ A₀)
    (hM : ∫ x, f x ^ (2 * q) ∂P ≤ Mf) :
    (∫ x, f x ^ q ∂P) ^ (1 / (q : ℝ)) ≤ A₀ + (Real.sqrt Mf * Real.sqrt δ) ^ (1 / (q : ℝ)) := by
  obtain ⟨K, hK⟩ := hfb
  have h := step3s_mink P (S := Fin 0) q hq f (T.indicator f) (fun _ _ => 0) A₀ (fun _ => 0)
    hA₀ (fun _ => le_rfl) hfm hf0 (hfm.indicator hT)
    (fun x => Set.indicator_nonneg (fun y _ => hf0 y) x)
    ⟨max K 0, fun x => by
      by_cases hx : x ∈ T
      · rw [Set.indicator_of_mem hx]; exact (hK x).trans (le_max_left _ _)
      · rw [Set.indicator_of_notMem hx]; exact le_max_right _ _⟩
    (fun _ => aestronglyMeasurable_const) (fun _ _ => le_rfl) (fun _ => ⟨0, fun _ => le_rfl⟩)
    (fun x => by
      by_cases hx : x ∈ T
      · rw [Set.indicator_of_mem hx]
        simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
        linarith [hf0 x]
      · rw [Set.indicator_of_notMem hx]
        simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
        exact hgood x hx)
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at h
  exact h.trans (add_le_add le_rfl (step3s_off P q hq f hfm hf0 ⟨K, hK⟩ hT hδ hTδ hM))

/-- The moment comparison with Grönwall: for a finite family `Y_l` of the class with
`|𝒢Y_l| ≤ h₁/(1 - r) + Σ_{l'} α_{ll'} |Y_{l'}|`, `Σ_{l'} α_{ll'} ≤ C + κ/(1 - r)` and
`|Γ(Y_l)| ≤ b₁/(1 - r)` off sets of probability `≤ δ`, `|Y_l(s)| ≤ I₀` off a set of probability
`≤ δ`, and crude moments, the moments at `v` grow at most like `e^{C(v-s)}((1-s)/(1-v))^κ`. -/
private theorem step3s_core {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S] (σ2 : ℝ)
    (hσ2 : 0 ≤ σ2) (Y : S → ℝ → (ι → ℝ) → ℂ) {a' b' s v : ℝ} (ha : a' < 0) (hs : 0 ≤ s)
    (hsv : s ≤ v) (hvb : v < b') (hv1 : v < 1) (hY : ∀ l, HeatClass (Y l) a' b') (p : ℕ)
    (hp : 1 ≤ p) (T : ℝ → Set (ι → ℝ)) (hTm : ∀ r, MeasurableSet (T r)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hTδ : ∀ r ∈ Set.Ioo s v, stdGauss ι (T r) ≤ ENNReal.ofReal δ) (T0 : Set (ι → ℝ))
    (hT0m : MeasurableSet T0) (hT0δ : stdGauss ι T0 ≤ ENNReal.ofReal δ)
    (α : ℝ → S → S → ℝ) (hα0 : ∀ r l l', 0 ≤ α r l l') {C κ h₁ b₁ I₀ MA MB MI : ℝ}
    (hC : 0 ≤ C) (hκ : 0 ≤ κ) (hh₁ : 0 ≤ h₁) (hb₁ : 0 ≤ b₁) (hI₀ : 0 ≤ I₀)
    (hαs : ∀ r ∈ Set.Ioo s v, ∀ l, ∑ l', α r l l' ≤ C + κ * (1 - r)⁻¹)
    (hGgood : ∀ r ∈ Set.Ioo s v, ∀ l x, x ∉ T r →
      ‖coordGen σ2 (Y l) r (Real.sqrt (r * σ2) • x)‖ ≤
        h₁ * (1 - r)⁻¹ + ∑ l', α r l l' * ‖Y l' r (Real.sqrt (r * σ2) • x)‖)
    (hΓgood : ∀ r ∈ Set.Ioo s v, ∀ l x, x ∉ T r →
      ‖coordGamma σ2 (Y l r) (Y l r) (Real.sqrt (r * σ2) • x)‖ ≤ b₁ * (1 - r)⁻¹)
    (hIgood : ∀ l x, x ∉ T0 → ‖Y l s (Real.sqrt (s * σ2) • x)‖ ≤ I₀)
    (hMA : ∀ r ∈ Set.Ioo s v, ∀ l,
      ∫ x, ‖coordGen σ2 (Y l) r (Real.sqrt (r * σ2) • x)‖ ^ (2 * (2 * p)) ∂(stdGauss ι) ≤ MA)
    (hMB : ∀ r ∈ Set.Ioo s v, ∀ l,
      ∫ x, ‖coordGamma σ2 (Y l r) (Y l r) (Real.sqrt (r * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι) ≤ MB)
    (hMI : ∀ l, ∫ x, ‖Y l s (Real.sqrt (s * σ2) • x)‖ ^ (2 * (2 * p)) ∂(stdGauss ι) ≤ MI)
    (l : S) :
    (∫ x, ‖Y l v (Real.sqrt (v * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι)) ^ (1 / (2 * (p : ℝ))) ≤
      Real.exp (C * (v - s)) * ((1 - s) / (1 - v)) ^ κ *
        (Real.sqrt ((I₀ + (Real.sqrt MI * Real.sqrt δ) ^ (1 / (2 * (p : ℝ)))) ^ 2 +
            (2 * p - 1) * ((b₁ + (Real.sqrt MB * Real.sqrt δ) ^ (1 / (p : ℝ))) *
              Real.log ((1 - s) / (1 - v)))) +
          (h₁ + (Real.sqrt MA * Real.sqrt δ) ^ (1 / (2 * (p : ℝ)))) *
            Real.log ((1 - s) / (1 - v))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hcast : ((2 * p : ℕ) : ℝ) = 2 * (p : ℝ) := by push_cast; ring
  have hv0 : 0 ≤ v := hs.trans hsv
  have hs1 : s < 1 := lt_of_le_of_lt hsv hv1
  set ρA := (Real.sqrt MA * Real.sqrt δ) ^ (1 / (2 * (p : ℝ))) with hρA
  set ρB := (Real.sqrt MB * Real.sqrt δ) ^ (1 / (p : ℝ)) with hρB
  set ρI := (Real.sqrt MI * Real.sqrt δ) ^ (1 / (2 * (p : ℝ))) with hρI
  have hρA0 : 0 ≤ ρA := by positivity
  have hρB0 : 0 ≤ ρB := by positivity
  have hρI0 : 0 ≤ ρI := by positivity
  set N : S → ℝ → ℝ := fun l u =>
    (∫ x, ‖Y l u (Real.sqrt (u * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι)) ^ (1 / (2 * (p : ℝ)))
    with hN
  have hN0 : ∀ l u, 0 ≤ N l u := fun l u =>
    Real.rpow_nonneg (integral_nonneg fun x => by positivity) _
  have hne : (Finset.univ : Finset S).Nonempty := Finset.univ_nonempty
  set F : ℝ → ℝ := fun u => Finset.univ.sup' hne (fun l => N l u) with hF
  have hNF : ∀ l u, N l u ≤ F u := fun l u => Finset.le_sup' (fun l => N l u) (Finset.mem_univ l)
  have hF0 : ∀ u, 0 ≤ F u := fun u => (hN0 l u).trans (hNF l u)
  have hFc : ContinuousOn F (Set.Icc s v) := by
    refine ContinuousOn.finset_sup'_apply hne fun l _ => ?_
    exact (step3s_moment_cont σ2 hσ2 ha hv0 hvb (hY l) p hp).mono
      (Set.Icc_subset_Icc hs le_rfl)
  have hinv1 : ∀ r ∈ Set.Ioo s v, 1 ≤ (1 - r)⁻¹ := fun r hr => by
    rw [one_le_inv₀ (by linarith [hr.2])]; linarith [hr.1]
  -- the jets at a time of `(s, v)`
  have hjet : ∀ l, ∀ r ∈ Set.Ioo s v, _ := fun l r hr =>
    step3s_class_jet (hY l) (⟨ha.trans_le (hs.trans hr.1.le), hr.2.trans hvb⟩ :
      r ∈ Set.Ioo a' b') σ2
  -- the generator in `L^{2p}`
  have hAg : ∀ l, ∀ r ∈ Set.Ioo s v,
      (∫ x, ‖coordGen σ2 (Y l) r (Real.sqrt (r * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι)) ^
        (1 / (2 * (p : ℝ))) ≤ (C + κ * (1 - r)⁻¹) * F r + (h₁ + ρA) * (1 - r)⁻¹ := by
    intro l r hr
    obtain ⟨-, -, -, ⟨hGc, CG, hCG⟩, -⟩ := hjet l r hr
    have hfc : Continuous (fun x : ι → ℝ => ‖coordGen σ2 (Y l) r (Real.sqrt (r * σ2) • x)‖) :=
      continuous_norm.comp (hGc.comp (continuous_const_smul _))
    have hgc : ∀ l', Continuous (fun x : ι → ℝ => ‖Y l' r (Real.sqrt (r * σ2) • x)‖) := fun l' =>
      continuous_norm.comp (((hjet l' r hr).2.1.continuous).comp (continuous_const_smul _))
    have hgb : ∀ l', ∃ K, ∀ x : ι → ℝ, ‖Y l' r (Real.sqrt (r * σ2) • x)‖ ≤ K := fun l' => by
      obtain ⟨-, -, ⟨CY, hCY⟩, -, -⟩ := hjet l' r hr
      exact ⟨CY, fun x => hCY _⟩
    have hm := step3s_mink (stdGauss ι) (2 * p) (by omega)
      (fun x => ‖coordGen σ2 (Y l) r (Real.sqrt (r * σ2) • x)‖)
      ((T r).indicator fun x => ‖coordGen σ2 (Y l) r (Real.sqrt (r * σ2) • x)‖)
      (fun l' x => ‖Y l' r (Real.sqrt (r * σ2) • x)‖) (h₁ * (1 - r)⁻¹) (α r l)
      (mul_nonneg hh₁ (by linarith [hinv1 r hr])) (hα0 r l) hfc.aestronglyMeasurable
      (fun x => norm_nonneg _) (hfc.aestronglyMeasurable.indicator (hTm r))
      (fun x => Set.indicator_nonneg (fun y _ => norm_nonneg _) x)
      ⟨max CG 0, fun x => by
        by_cases hx : x ∈ T r
        · rw [Set.indicator_of_mem hx]; exact (hCG _).trans (le_max_left _ _)
        · rw [Set.indicator_of_notMem hx]; exact le_max_right _ _⟩
      (fun l' => (hgc l').aestronglyMeasurable) (fun l' x => norm_nonneg _) hgb
      (fun x => by
        by_cases hx : x ∈ T r
        · rw [Set.indicator_of_mem hx]
          have h1 : 0 ≤ h₁ * (1 - r)⁻¹ := mul_nonneg hh₁ (by linarith [hinv1 r hr])
          have h2 : 0 ≤ ∑ l', α r l l' * ‖Y l' r (Real.sqrt (r * σ2) • x)‖ :=
            Finset.sum_nonneg fun l' _ => mul_nonneg (hα0 r l l') (norm_nonneg _)
          linarith
        · rw [Set.indicator_of_notMem hx, add_zero]
          exact hGgood r hr l x hx)
    have hoff := step3s_off (stdGauss ι) (2 * p) (by omega)
      (fun x => ‖coordGen σ2 (Y l) r (Real.sqrt (r * σ2) • x)‖) hfc.aestronglyMeasurable
      (fun x => norm_nonneg _) ⟨CG, fun x => hCG _⟩ (hTm r) hδ (hTδ r hr) (hMA r hr l)
    rw [hcast] at hm hoff
    have hsum : ∑ l', α r l l' * N l' r ≤ (C + κ * (1 - r)⁻¹) * F r := by
      calc ∑ l', α r l l' * N l' r ≤ ∑ l', α r l l' * F r :=
            Finset.sum_le_sum fun l' _ => mul_le_mul_of_nonneg_left (hNF l' r) (hα0 r l l')
        _ = (∑ l', α r l l') * F r := by rw [Finset.sum_mul]
        _ ≤ (C + κ * (1 - r)⁻¹) * F r := mul_le_mul_of_nonneg_right (hαs r hr l) (hF0 r)
    have hρ : ρA ≤ ρA * (1 - r)⁻¹ := le_mul_of_one_le_right hρA0 (hinv1 r hr)
    calc _ ≤ h₁ * (1 - r)⁻¹ + ∑ l', α r l l' * N l' r + ρA := hm.trans (by
          gcongr)
      _ ≤ _ := by nlinarith
  -- the bracket in `L^p`
  have hBg : ∀ l, ∀ r ∈ Set.Ioo s v,
      (∫ x, ‖coordGamma σ2 (Y l r) (Y l r) (Real.sqrt (r * σ2) • x)‖ ^ p ∂(stdGauss ι)) ^
        (1 / (p : ℝ)) ≤ (b₁ + ρB) * (1 - r)⁻¹ := by
    intro l r hr
    obtain ⟨-, -, -, -, ⟨hΓc, CΓ, hCΓ⟩⟩ := hjet l r hr
    have hfc : Continuous
        (fun x : ι → ℝ => ‖coordGamma σ2 (Y l r) (Y l r) (Real.sqrt (r * σ2) • x)‖) :=
      continuous_norm.comp (hΓc.comp (continuous_const_smul _))
    have h := step3s_moment_split (stdGauss ι) _ hfc.aestronglyMeasurable
      (fun x => norm_nonneg _) ⟨CΓ, fun x => hCΓ _⟩ p hp (hTm r) hδ (hTδ r hr)
      (mul_nonneg hb₁ (by linarith [hinv1 r hr])) (fun x hx => hΓgood r hr l x hx) (hMB r hr l)
    have hρ : ρB ≤ ρB * (1 - r)⁻¹ := le_mul_of_one_le_right hρB0 (hinv1 r hr)
    calc _ ≤ b₁ * (1 - r)⁻¹ + ρB := h
      _ ≤ _ := by nlinarith
  -- the initial value
  have hIs : ∀ l, N l s ≤ I₀ + ρI := by
    intro l
    have hsI : s ∈ Set.Ioo a' b' := ⟨ha.trans_le hs, lt_of_le_of_lt hsv hvb⟩
    obtain ⟨-, hc2, ⟨CY, hCY⟩, -, -⟩ := step3s_class_jet (hY l) hsI σ2
    have hfc : Continuous (fun x : ι → ℝ => ‖Y l s (Real.sqrt (s * σ2) • x)‖) :=
      continuous_norm.comp (hc2.continuous.comp (continuous_const_smul _))
    have h := step3s_moment_split (stdGauss ι) _ hfc.aestronglyMeasurable
      (fun x => norm_nonneg _) ⟨CY, fun x => hCY _⟩ (2 * p) (by omega) hT0m hδ hT0δ hI₀
      (hIgood l) (hMI l)
    rw [hcast] at h
    exact h
  -- the integral inequality on `[s, v]`
  set Lv := Real.log ((1 - s) / (1 - v)) with hLv
  set c₀ := Real.sqrt ((I₀ + ρI) ^ 2 + (2 * p - 1) * ((b₁ + ρB) * Lv)) with hc₀
  have hp1 : (0 : ℝ) ≤ 2 * p - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hLv0 : 0 ≤ Lv := Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  have hc₀I : I₀ + ρI ≤ c₀ := by
    rw [hc₀]
    refine Real.le_sqrt_of_sq_le ?_
    have : 0 ≤ (2 * p - 1) * ((b₁ + ρB) * Lv) := by positivity
    linarith
  have hint : ∀ u ∈ Set.Icc s v, F u ≤ c₀ + ∫ r in s..u,
      ((C + κ * (1 - r)⁻¹) * F r + (h₁ + ρA) * (1 - r)⁻¹) := by
    intro u hu
    rcases eq_or_lt_of_le hu.1 with hsu | hsu
    · subst hsu
      simp only [intervalIntegral.integral_same, add_zero]
      exact Finset.sup'_le hne _ fun l _ => (hIs l).trans hc₀I
    · refine Finset.sup'_le hne _ fun l _ => ?_
      have hu1 : u < 1 := lt_of_le_of_lt hu.2 hv1
      have hsub : Set.Icc s u ⊆ Set.Icc s v := Set.Icc_subset_Icc le_rfl hu.2
      have hsubo : Set.Ioo s u ⊆ Set.Ioo s v := Set.Ioo_subset_Ioo le_rfl hu.2
      have hinvc : ContinuousOn (fun r : ℝ => (1 - r)⁻¹) (Set.Icc s u) :=
        (continuousOn_const.sub continuousOn_id).inv₀ fun r hr =>
          show (1 : ℝ) - r ≠ 0 by linarith [hr.2]
      have hM := lemmaM_gaussian σ2 hσ2 (Y l) ha hs hsu.le (lt_of_le_of_lt hu.2 hvb) (hY l) p hp
        (fun r => (C + κ * (1 - r)⁻¹) * F r + (h₁ + ρA) * (1 - r)⁻¹)
        (fun r => (b₁ + ρB) * (1 - r)⁻¹)
        (((continuousOn_const.add (continuousOn_const.mul hinvc)).mul (hFc.mono hsub)).add
          (continuousOn_const.mul hinvc))
        (continuousOn_const.mul hinvc)
        (fun r hr => by
          have : 0 ≤ (1 - r)⁻¹ := inv_nonneg.mpr (by linarith [hr.2])
          have := hF0 r
          positivity)
        (fun r hr => by
          have : 0 ≤ (1 - r)⁻¹ := inv_nonneg.mpr (by linarith [hr.2])
          positivity)
        (fun r hr => hAg l r (hsubo hr)) (fun r hr => hBg l r (hsubo hr))
      have hB : ∫ r in s..u, (b₁ + ρB) * (1 - r)⁻¹ ≤ (b₁ + ρB) * Lv := by
        rw [intervalIntegral.integral_const_mul, step3s_int_inv hs1 hu1]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine Real.log_le_log (div_pos (by linarith) (by linarith)) ?_
        exact div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith [hu.2])
      have hI0 : 0 ≤ ∫ x, ‖Y l s (Real.sqrt (s * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι) :=
        integral_nonneg fun x => by positivity
      have hIsq : (∫ x, ‖Y l s (Real.sqrt (s * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι)) ^
          (1 / (p : ℝ)) = N l s ^ 2 := by
        simp only [hN]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hI0]
        congr 1; push_cast; field_simp
      rw [hIsq] at hM
      refine hM.trans (add_le_add ?_ le_rfl)
      rw [hc₀]
      refine Real.sqrt_le_sqrt (add_le_add ?_ (mul_le_mul_of_nonneg_left hB hp1))
      exact pow_le_pow_left₀ (hN0 l s) (hIs l) 2
  have hG := step3s_gronwall hsv hv1 F hFc hC hκ (add_nonneg hh₁ hρA0) hint
  exact (hNF l v).trans hG

end Step3Core

/-! ### Crude bounds by the blocks of the resolvent -/

section Step3Crude

open scoped Matrix.Norms.L2Operator

variable {W L : ℕ}

/-- An entry is bounded by the operator norm. -/
private lemma step3s_norm_entry_le {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (i j : n) : ‖X i j‖ ≤ ‖X‖ := by
  have h := Matrix.l2_opNorm_mulVec X ((EuclideanSpace.equiv n ℂ).symm (Pi.single j 1))
  have hx : ‖(EuclideanSpace.equiv n ℂ).symm (Pi.single j (1 : ℂ))‖ = 1 := by simp
  rw [hx, mul_one] at h
  refine le_trans (le_of_eq ?_) ((PiLp.norm_apply_le _ i).trans h)
  simp [Matrix.mulVec_single]

/-- `‖A‖²_HS ≤ n ‖A‖²` for an `n × n` matrix. -/
private lemma step3s_hs_le_op {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    step3s_hs A ≤ Fintype.card n * ‖A‖ ^ 2 := by
  unfold step3s_hs
  rw [Finset.sum_comm]
  have h : ∀ j : n, ∑ i, ‖A i j‖ ^ 2 ≤ ‖A‖ ^ 2 := by
    intro j
    have h1 := step3s_nsq_le A (Pi.single j 1)
    have e1 : (A *ᵥ Pi.single j 1) = fun i => A i j := by
      funext i; simp [Matrix.mulVec_single]
    have e2 : ∑ i, ‖(Pi.single j (1 : ℂ) : n → ℂ) i‖ ^ 2 = 1 := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    rw [e1, e2, mul_one] at h1
    exact h1
  calc ∑ j, ∑ i, ‖A i j‖ ^ 2 ≤ ∑ _j : n, ‖A‖ ^ 2 := Finset.sum_le_sum fun j _ => h j
    _ = _ := by simp

/-- `|Tr A| ≤ n ‖A‖` for an `n × n` matrix. -/
private lemma step3s_trace_le_op {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    ‖A.trace‖ ≤ Fintype.card n * ‖A‖ := by
  unfold Matrix.trace Matrix.diag
  calc ‖∑ i, A i i‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : n, ‖A‖ := Finset.sum_le_sum fun i _ => step3s_norm_entry_le A i i
    _ = _ := by simp

/-- `|⟨X⟩_{cc}| ≤ ‖X_{cc}‖`. -/
private lemma step3s_blockTr_le (hW : 1 ≤ W) (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (c : Fin L) : ‖blockTr X c c‖ ≤ ‖blockOf X c c‖ := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have e : blockTr X c c = (W : ℂ)⁻¹ * (blockOf X c c).trace := rfl
  rw [e, norm_mul, norm_inv, Complex.norm_natCast]
  have h := step3s_trace_le_op (blockOf X c c)
  rw [Fintype.card_fin] at h
  calc (W : ℝ)⁻¹ * ‖(blockOf X c c).trace‖ ≤ (W : ℝ)⁻¹ * (W * ‖blockOf X c c‖) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp

/-- `|ℒ₂(x,y;+,+)| ≤ ‖X_{xy}‖ ‖X_{yx}‖`. -/
private lemma step3s_crude_pp (hW : 1 ≤ W) (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (x y : Fin L) :
    ‖loopTr X ![x, y] ![true, true]‖ ≤ ‖blockOf X x y‖ * ‖blockOf X y x‖ := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  refine (norm_loopTr_pp_le X x y).trans ?_
  have hre : ∀ u v : Fin L, (loopTr X ![u, v] ![true, false]).re ≤ ‖blockOf X v u‖ ^ 2 := by
    intro u v
    rw [step3s_loopTr_pm, Complex.ofReal_re, ← step3s_hs_blockOf]
    have h := step3s_hs_le_op (blockOf X v u)
    rw [Fintype.card_fin] at h
    have h0 : 0 ≤ step3s_hs (blockOf X v u) := step3s_hs_nonneg _
    calc ((W : ℝ) ^ 2)⁻¹ * step3s_hs (blockOf X v u) ≤ ((W : ℝ) ^ 2)⁻¹ *
          (W * ‖blockOf X v u‖ ^ 2) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = (W : ℝ)⁻¹ * ‖blockOf X v u‖ ^ 2 := by field_simp
      _ ≤ 1 * ‖blockOf X v u‖ ^ 2 := by
          gcongr
          exact inv_le_one_of_one_le₀ hW1
      _ = _ := one_mul _
  have h1 := hre x y
  have h2 := hre y x
  have h0 : 0 ≤ (loopTr X ![x, y] ![true, false]).re := step3s_pm_re_nonneg X x y
  calc Real.sqrt ((loopTr X ![x, y] ![true, false]).re * (loopTr X ![y, x] ![true, false]).re)
      ≤ Real.sqrt (‖blockOf X y x‖ ^ 2 * ‖blockOf X x y‖ ^ 2) :=
        Real.sqrt_le_sqrt (mul_le_mul h1 h2 (step3s_pm_re_nonneg X y x) (by positivity))
    _ = ‖blockOf X y x‖ * ‖blockOf X x y‖ := by
        rw [← mul_pow, Real.sqrt_sq (by positivity)]
    _ = _ := mul_comm _ _

/-- `|ℒ₃(x,y,z;+,+,+)| ≤ ‖X_{zx}‖ ‖X_{xy}‖ ‖X_{yz}‖`. -/
private lemma step3s_crude_three (hW : 1 ≤ W) (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (x y z : Fin L) :
    ‖loopTr X ![x, y, z] ![true, true, true]‖ ≤
      ‖blockOf X z x‖ * ‖blockOf X x y‖ * ‖blockOf X y z‖ := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  rw [step3s_loopTr_three]
  simp only [sgnMat, ite_true]
  rw [norm_mul, norm_pow, norm_inv, Complex.norm_natCast]
  have hhs : ∀ A : Matrix (Fin W) (Fin W) ℂ, Real.sqrt (step3s_hs A) ≤ Real.sqrt W * ‖A‖ := by
    intro A
    have h := step3s_hs_le_op A
    rw [Fintype.card_fin] at h
    rw [← Real.sqrt_sq (norm_nonneg A), ← Real.sqrt_mul (Nat.cast_nonneg W)]
    exact Real.sqrt_le_sqrt h
  have h3 := step3s_trace3_le (blockOf X z x) (blockOf X x y) (blockOf X y z)
  have hsW : Real.sqrt W * Real.sqrt W = W := Real.mul_self_sqrt (Nat.cast_nonneg W)
  have h4 : ‖(blockOf X z x * blockOf X x y * blockOf X y z).trace‖ ≤
      W * (‖blockOf X z x‖ * ‖blockOf X x y‖ * ‖blockOf X y z‖) := by
    refine h3.trans ?_
    calc ‖blockOf X z x‖ * (Real.sqrt (step3s_hs (blockOf X x y)) *
          Real.sqrt (step3s_hs (blockOf X y z)))
        ≤ ‖blockOf X z x‖ * ((Real.sqrt W * ‖blockOf X x y‖) *
          (Real.sqrt W * ‖blockOf X y z‖)) := by
          gcongr
          · exact hhs _
          · exact hhs _
      _ = (Real.sqrt W * Real.sqrt W) *
          (‖blockOf X z x‖ * ‖blockOf X x y‖ * ‖blockOf X y z‖) := by ring
      _ = _ := by rw [hsW]
  have h5 : (W : ℝ)⁻¹ ^ 3 * W ≤ 1 := by
    rw [show (W : ℝ)⁻¹ ^ 3 * W = ((W : ℝ) ^ 2)⁻¹ by field_simp]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hW1)
  have h6 : 0 ≤ ‖blockOf X z x‖ * ‖blockOf X x y‖ * ‖blockOf X y z‖ := by positivity
  calc (W : ℝ)⁻¹ ^ 3 * ‖(blockOf X z x * blockOf X x y * blockOf X y z).trace‖
      ≤ (W : ℝ)⁻¹ ^ 3 * (W * (‖blockOf X z x‖ * ‖blockOf X x y‖ * ‖blockOf X y z‖)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = ((W : ℝ)⁻¹ ^ 3 * W) * (‖blockOf X z x‖ * ‖blockOf X x y‖ * ‖blockOf X y z‖) := by ring
    _ ≤ 1 * (‖blockOf X z x‖ * ‖blockOf X x y‖ * ‖blockOf X y z‖) :=
        mul_le_mul_of_nonneg_right h5 h6
    _ = _ := one_mul _

/-- The bound `K_c = W + 1 + Σ_{u,v ∈ {a,b,c}} ‖X_{uv}‖` on the blocks between `a, b, c`. -/
private def step3sK (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b c : Fin L) : ℝ :=
  ((W : ℝ) + 1) + ∑ ij : Fin 3 × Fin 3, ‖blockOf X (![a, b, c] ij.1) (![a, b, c] ij.2)‖

private lemma step3sK_ge (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b c : Fin L) :
    (W : ℝ) + 1 ≤ step3sK X a b c := by
  unfold step3sK
  have : 0 ≤ ∑ ij : Fin 3 × Fin 3, ‖blockOf X (![a, b, c] ij.1) (![a, b, c] ij.2)‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  linarith

private lemma step3sK_block (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b c : Fin L)
    (i j : Fin 3) : ‖blockOf X (![a, b, c] i) (![a, b, c] j)‖ ≤ step3sK X a b c := by
  have h := Finset.single_le_sum (f := fun ij : Fin 3 × Fin 3 =>
    ‖blockOf X (![a, b, c] ij.1) (![a, b, c] ij.2)‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ (i, j))
  unfold step3sK
  have : (0 : ℝ) ≤ W + 1 := by positivity
  simp only at h
  linarith

end Step3Crude

section Step3Crude2

open scoped Matrix.Norms.L2Operator

variable {W L : ℕ}

/-- Crude light term: `|𝒲₂(a,b;+,+)| ≤ γ_gW Σ_c 2(K_c + |m|) K_c³`. -/
private lemma step3s_crude_light (g E : ℝ) (m : ℂ) (hW : 1 ≤ W) (u : ℝ)
    (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) :
    ‖lightW g E m ![a, b] ![true, true] u M‖ ≤
      gammaG g * W * ∑ c, 2 * (step3sK (resolventMat M (zChar g E m u)) a b c + ‖m‖) *
        step3sK (resolventMat M (zChar g E m u)) a b c ^ 3 := by
  set G := resolventMat M (zChar g E m u) with hG
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  have hγW : 0 ≤ gammaG g * W := by positivity
  have hK1 : ∀ c, (1 : ℝ) ≤ step3sK G a b c := fun c => by
    have := step3sK_ge G a b c; have : (0 : ℝ) ≤ W := Nat.cast_nonneg W; linarith
  have hKb : ∀ c (i j : Fin 3), ‖blockOf G (![a, b, c] i) (![a, b, c] j)‖ ≤ step3sK G a b c :=
    fun c i j => step3sK_block G a b c i j
  have hterm : ∀ (i : Fin 2) (c : Fin L),
      ‖(loopTr G ![c] ![(![true, true] : Fin 2 → Bool) i] -
          sgnScalar m ((![true, true] : Fin 2 → Bool) i)) *
        loopTr G (insLab ![a, b] i c) (insSgn ![true, true] i)‖ ≤
      (step3sK G a b c + ‖m‖) * step3sK G a b c ^ 3 := by
    intro i c
    have hti : (![true, true] : Fin 2 → Bool) i = true := by fin_cases i <;> rfl
    simp only [hti, sgnScalar, ite_true]
    rw [norm_mul]
    have h1 : ‖loopTr G ![c] ![true] - m‖ ≤ step3sK G a b c + ‖m‖ := by
      refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
      rw [step3s_loopTr_one_eq]
      exact (step3s_blockTr_le hW G c).trans (by simpa using hKb c 2 2)
    have h2 : ‖loopTr G (insLab ![a, b] i c) (insSgn ![true, true] i)‖ ≤ step3sK G a b c ^ 3 := by
      fin_cases i
      · have e : insLab ![a, b] (0 : Fin 2) c = ![c, a, b] := by
          funext j; fin_cases j <;> rfl
        have es : insSgn (![true, true] : Fin 2 → Bool) (0 : Fin 2) = ![true, true, true] := by
          funext j; fin_cases j <;> rfl
        simp only [Fin.zero_eta, Fin.isValue] at e es ⊢
        rw [e, es]
        refine (step3s_crude_three hW G c a b).trans ?_
        rw [pow_three]
        have k1 : ‖blockOf G b c‖ ≤ step3sK G a b c := by simpa using hKb c 1 2
        have k2 : ‖blockOf G c a‖ ≤ step3sK G a b c := by simpa using hKb c 2 0
        have k3 : ‖blockOf G a b‖ ≤ step3sK G a b c := by simpa using hKb c 0 1
        calc ‖blockOf G b c‖ * ‖blockOf G c a‖ * ‖blockOf G a b‖ ≤
            step3sK G a b c * step3sK G a b c * step3sK G a b c :=
              mul_le_mul (mul_le_mul k1 k2 (norm_nonneg _) (by linarith [hK1 c])) k3
                (norm_nonneg _) (by nlinarith [hK1 c])
          _ = _ := by ring
      · have e : insLab ![a, b] (1 : Fin 2) c = ![a, c, b] := by
          funext j; fin_cases j <;> rfl
        have es : insSgn (![true, true] : Fin 2 → Bool) (1 : Fin 2) = ![true, true, true] := by
          funext j; fin_cases j <;> rfl
        simp only [Fin.mk_one, Fin.isValue] at e es ⊢
        rw [e, es]
        refine (step3s_crude_three hW G a c b).trans ?_
        rw [pow_three]
        have k1 : ‖blockOf G b a‖ ≤ step3sK G a b c := by simpa using hKb c 1 0
        have k2 : ‖blockOf G a c‖ ≤ step3sK G a b c := by simpa using hKb c 0 2
        have k3 : ‖blockOf G c b‖ ≤ step3sK G a b c := by simpa using hKb c 2 1
        calc ‖blockOf G b a‖ * ‖blockOf G a c‖ * ‖blockOf G c b‖ ≤
            step3sK G a b c * step3sK G a b c * step3sK G a b c :=
              mul_le_mul (mul_le_mul k1 k2 (norm_nonneg _) (by linarith [hK1 c])) k3
                (norm_nonneg _) (by nlinarith [hK1 c])
          _ = _ := by ring
    exact mul_le_mul h1 h2 (norm_nonneg _) (by linarith [hK1 c, norm_nonneg m])
  unfold lightW
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hγW]
  refine mul_le_mul_of_nonneg_left ?_ hγW
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i : Fin 2, ‖∑ c : Fin L, (loopTr G ![c] ![(![true, true] : Fin 2 → Bool) i] -
          sgnScalar m ((![true, true] : Fin 2 → Bool) i)) *
        loopTr G (insLab ![a, b] i c) (insSgn ![true, true] i)‖
      ≤ ∑ _i : Fin 2, ∑ c, (step3sK G a b c + ‖m‖) * step3sK G a b c ^ 3 :=
        Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun c _ => hterm i c)
    _ = _ := by
        rw [Fin.sum_univ_two, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun c _ => by ring

/-- Crude generator: with `|𝒦₂(x,y;+,+)| ≤ W`,
`|𝒢D₂(a,b;+,+)| ≤ γ_gW (6 + 2|m|) Σ_c K_c⁴`. -/
private lemma step3s_crude_gen (g E : ℝ) (m : ℂ) (hW : 1 ≤ W) (hL : 3 ≤ L)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {u : ℝ} (hu : u ∈ Set.Ioo (-1 : ℝ) 1)
    {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    (hK : ∀ x y : Fin L, ‖primLoop g W L E m u ![x, y] ![true, true]‖ ≤ W) (a b : Fin L) :
    ‖blockGen W L (gammaG g) (fun r N => resLoop g E m ![a, b] ![true, true] r N -
        primLoop g W L E m r ![a, b] ![true, true]) u M‖ ≤
      gammaG g * W * (6 + 2 * ‖m‖) *
        ∑ c, step3sK (resolventMat M (zChar g E m u)) a b c ^ 4 := by
  set G := resolventMat M (zChar g E m u) with hG
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  have hγW : 0 ≤ gammaG g * W := by positivity
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hK1 : ∀ c, (1 : ℝ) ≤ step3sK G a b c := fun c => by
    have := step3sK_ge G a b c; linarith
  have hKW : ∀ c, (W : ℝ) ≤ step3sK G a b c := fun c => by
    have := step3sK_ge G a b c; linarith
  have hKb : ∀ c (i j : Fin 3), ‖blockOf G (![a, b, c] i) (![a, b, c] j)‖ ≤ step3sK G a b c :=
    fun c i j => step3sK_block G a b c i j
  have hgs := step3s_gen_split g E m W L hW hL hm hu hM a b
    (fun c => ‖blockOf G c b‖ * ‖blockOf G b c‖) (fun c => step3s_crude_pp hW G c b)
  refine hgs.trans ?_
  have hlight := step3s_crude_light g E m hW u M a b
  have hD : ∀ c x y : Fin L, ‖blockOf G x y‖ ≤ step3sK G a b c →
      ‖blockOf G y x‖ ≤ step3sK G a b c →
      ‖resLoop g E m ![x, y] ![true, true] u M - primLoop g W L E m u ![x, y] ![true, true]‖ ≤
        2 * step3sK G a b c ^ 2 := by
    intro c x y hxy hyx
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖resLoop g E m ![x, y] ![true, true] u M‖ ≤ step3sK G a b c ^ 2 := by
      refine (step3s_crude_pp hW G x y).trans ?_
      rw [sq]; exact mul_le_mul hxy hyx (norm_nonneg _) (by linarith [hK1 c])
    have h2 := hK x y
    have h3 : (W : ℝ) ≤ step3sK G a b c ^ 2 := (hKW c).trans
      (le_self_pow₀ (hK1 c) (by norm_num))
    linarith
  have hA : ∀ c, ‖((gammaG g * W : ℝ) : ℂ) * primLoop g W L E m u ![a, c] ![true, true]‖ *
      ‖resLoop g E m ![c, b] ![true, true] u M - primLoop g W L E m u ![c, b] ![true, true]‖ ≤
      gammaG g * W * (2 * step3sK G a b c ^ 4) := by
    intro c
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hγW]
    have h1 := hD c c b (by simpa using hKb c 2 1) (by simpa using hKb c 1 2)
    have h2 := hK a c
    have hK3 : (W : ℝ) * (2 * step3sK G a b c ^ 2) ≤ 2 * step3sK G a b c ^ 4 := by
      have := hKW c
      have h4 : step3sK G a b c ^ 4 = step3sK G a b c ^ 2 * step3sK G a b c ^ 2 := by ring
      have h5 : (W : ℝ) ≤ step3sK G a b c ^ 2 := this.trans (le_self_pow₀ (hK1 c) (by norm_num))
      rw [h4]
      have : 0 ≤ step3sK G a b c ^ 2 := by positivity
      nlinarith
    calc gammaG g * W * ‖primLoop g W L E m u ![a, c] ![true, true]‖ *
          ‖resLoop g E m ![c, b] ![true, true] u M - primLoop g W L E m u ![c, b] ![true, true]‖
        ≤ gammaG g * W * W * (2 * step3sK G a b c ^ 2) := by
          gcongr
      _ = gammaG g * W * (W * (2 * step3sK G a b c ^ 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hK3 hγW
  have hB : ∀ c, gammaG g * W * (‖blockOf G c b‖ * ‖blockOf G b c‖) *
      ‖resLoop g E m ![a, c] ![true, true] u M - primLoop g W L E m u ![a, c] ![true, true]‖ ≤
      gammaG g * W * (2 * step3sK G a b c ^ 4) := by
    intro c
    have h1 := hD c a c (by simpa using hKb c 0 2) (by simpa using hKb c 2 0)
    have k1 : ‖blockOf G c b‖ ≤ step3sK G a b c := by simpa using hKb c 2 1
    have k2 : ‖blockOf G b c‖ ≤ step3sK G a b c := by simpa using hKb c 1 2
    have hβ : ‖blockOf G c b‖ * ‖blockOf G b c‖ ≤ step3sK G a b c ^ 2 := by
      rw [sq]; exact mul_le_mul k1 k2 (norm_nonneg _) (by linarith [hK1 c])
    calc gammaG g * W * (‖blockOf G c b‖ * ‖blockOf G b c‖) *
          ‖resLoop g E m ![a, c] ![true, true] u M - primLoop g W L E m u ![a, c] ![true, true]‖
        ≤ gammaG g * W * step3sK G a b c ^ 2 * (2 * step3sK G a b c ^ 2) := by gcongr
      _ = _ := by ring
  have hL' : ∀ c, 2 * (step3sK G a b c + ‖m‖) * step3sK G a b c ^ 3 ≤
      (2 + 2 * ‖m‖) * step3sK G a b c ^ 4 := by
    intro c
    have h1 := hK1 c
    have hm0 := norm_nonneg m
    have : ‖m‖ ≤ ‖m‖ * step3sK G a b c := le_mul_of_one_le_right hm0 h1
    have h3 : 0 ≤ step3sK G a b c ^ 3 := by positivity
    have e : (2 + 2 * ‖m‖) * step3sK G a b c ^ 4 =
        2 * (step3sK G a b c + ‖m‖ * step3sK G a b c) * step3sK G a b c ^ 3 := by ring
    rw [e]
    gcongr
  calc _ ≤ gammaG g * W * ∑ c, 2 * (step3sK G a b c + ‖m‖) * step3sK G a b c ^ 3 +
        ∑ c, gammaG g * W * (2 * step3sK G a b c ^ 4) +
        ∑ c, gammaG g * W * (2 * step3sK G a b c ^ 4) :=
        add_le_add (add_le_add hlight (Finset.sum_le_sum fun c _ => hA c))
          (Finset.sum_le_sum fun c _ => hB c)
    _ ≤ gammaG g * W * ∑ c, (2 + 2 * ‖m‖) * step3sK G a b c ^ 4 +
        ∑ c, gammaG g * W * (2 * step3sK G a b c ^ 4) +
        ∑ c, gammaG g * W * (2 * step3sK G a b c ^ 4) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun c _ => hL' c) hγW) le_rfl) le_rfl
    _ = _ := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun c _ => by ring

/-- Crude bracket: `|Γ(ℒ₂(a,b;+,+))| ≤ 4γ_g Σ_c K_c⁶`. -/
private lemma step3s_crude_gamma (g E : ℝ) (m : ℂ) (hm : 0 < m.im) (hW : 1 ≤ W) {u : ℝ}
    (hu : u < 1) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    (a b : Fin L) :
    ‖blockGamma W L (gammaG g) (resLoop g E m ![a, b] ![true, true] u)
        (resLoop g E m ![a, b] ![true, true] u) M‖ ≤
      4 * gammaG g * ∑ c, step3sK (resolventMat M (zChar g E m u)) a b c ^ 6 := by
  set G := resolventMat M (zChar g E m u) with hG
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hK1 : ∀ c, (1 : ℝ) ≤ step3sK G a b c := fun c => by
    have := step3sK_ge G a b c; linarith
  have hKb : ∀ c (i j : Fin 3), ‖blockOf G (![a, b, c] i) (![a, b, c] j)‖ ≤ step3sK G a b c :=
    fun c i j => step3sK_block G a b c i j
  rw [step3s_gamma_eq g E m hm hW hu hM a b, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), ← Complex.ofReal_sum, Complex.norm_real,
    Real.norm_of_nonneg (Finset.sum_nonneg fun c _ => step3s_hs_nonneg _)]
  have hk : ‖(W : ℂ)⁻¹ * (W : ℂ)⁻¹‖ ^ 2 = ((W : ℝ)⁻¹) ^ 4 := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]; ring
  have hhs : ∀ A : Matrix (Fin W) (Fin W) ℂ, step3s_hs A ≤ W * ‖A‖ ^ 2 := fun A => by
    have h := step3s_hs_le_op A
    rwa [Fintype.card_fin] at h
  have hc : ∀ c, step3s_hs (blockOf (G * blockE W L a * (G * blockE W L b * G) +
      G * blockE W L b * (G * blockE W L a * G)) c c) ≤
      4 * ((W : ℝ)⁻¹ ^ 4 * W) * step3sK G a b c ^ 6 := by
    intro c
    rw [step3s_blockOf_add, step3s_blockOf_five, step3s_blockOf_five]
    refine (step3s_hs_add_le _ _).trans ?_
    rw [step3s_hs_smul, step3s_hs_smul, hk]
    have hprod : ∀ x y z : Fin L, ‖blockOf G x y‖ ≤ step3sK G a b c →
        ‖blockOf G y z‖ ≤ step3sK G a b c → ‖blockOf G x y * blockOf G y z‖ ^ 2 ≤
          step3sK G a b c ^ 4 := by
      intro x y z h1 h2
      have h3 := step3s_opNorm_mul_le (blockOf G x y) (blockOf G y z)
      have h4 : ‖blockOf G x y * blockOf G y z‖ ≤ step3sK G a b c ^ 2 := by
        rw [sq]; exact h3.trans (mul_le_mul h1 h2 (norm_nonneg _) (by linarith [hK1 c]))
      calc _ ≤ (step3sK G a b c ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h4 2
        _ = _ := by ring
    have e0 := step3s_hs_mul_right (blockOf G c a) (blockOf G a b * blockOf G b c)
    have e1 := step3s_hs_mul_right (blockOf G c b) (blockOf G b a * blockOf G a c)
    have p0 := hprod a b c (by simpa using hKb c 0 1) (by simpa using hKb c 1 2)
    have p1 := hprod b a c (by simpa using hKb c 1 0) (by simpa using hKb c 0 2)
    have q0 : step3s_hs (blockOf G c a) ≤ W * step3sK G a b c ^ 2 :=
      (hhs _).trans (by gcongr; simpa using hKb c 2 0)
    have q1 : step3s_hs (blockOf G c b) ≤ W * step3sK G a b c ^ 2 :=
      (hhs _).trans (by gcongr; simpa using hKb c 2 1)
    have f0 : step3s_hs (blockOf G c a * (blockOf G a b * blockOf G b c)) ≤
        W * step3sK G a b c ^ 6 := by
      refine e0.trans ?_
      calc _ ≤ step3sK G a b c ^ 4 * (W * step3sK G a b c ^ 2) :=
            mul_le_mul p0 q0 (step3s_hs_nonneg _) (by positivity)
        _ = _ := by ring
    have f1 : step3s_hs (blockOf G c b * (blockOf G b a * blockOf G a c)) ≤
        W * step3sK G a b c ^ 6 := by
      refine e1.trans ?_
      calc _ ≤ step3sK G a b c ^ 4 * (W * step3sK G a b c ^ 2) :=
            mul_le_mul p1 q1 (step3s_hs_nonneg _) (by positivity)
        _ = _ := by ring
    have hW4 : (0 : ℝ) ≤ ((W : ℝ)⁻¹) ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left f0 hW4, mul_le_mul_of_nonneg_left f1 hW4]
  have hfac : gammaG g / W * (4 * ((W : ℝ)⁻¹ ^ 4 * W)) ≤ 4 * gammaG g := by
    have e : gammaG g / W * (4 * ((W : ℝ)⁻¹ ^ 4 * W)) = 4 * gammaG g * ((W : ℝ) ^ 4)⁻¹ := by
      field_simp
    rw [e]
    calc 4 * gammaG g * ((W : ℝ) ^ 4)⁻¹ ≤ 4 * gammaG g * 1 :=
          mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ (one_le_pow₀ hW1)) (by positivity)
      _ = _ := mul_one _
  calc gammaG g / W * ∑ c, step3s_hs (blockOf (G * blockE W L a * (G * blockE W L b * G) +
        G * blockE W L b * (G * blockE W L a * G)) c c)
      ≤ gammaG g / W * ∑ c, 4 * ((W : ℝ)⁻¹ ^ 4 * W) * step3sK G a b c ^ 6 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => hc c) (by positivity)
    _ = (gammaG g / W * (4 * ((W : ℝ)⁻¹ ^ 4 * W))) * ∑ c, step3sK G a b c ^ 6 := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfac (Finset.sum_nonneg fun c _ => by positivity)

end Step3Crude2

section Step3CrudeMoment

/-- Jensen for weighted sums: `(Σ w_i f_i)^n ≤ (Σ w_i)^{n-1} Σ w_i f_i^n`. -/
private lemma step3s_wsum_pow_le {ι : Type*} [Fintype ι] (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) {n : ℕ} (hn : 1 ≤ n) :
    (∑ i, w i * f i) ^ n ≤ (∑ i, w i) ^ (n - 1) * ∑ i, w i * f i ^ n := by
  set S := ∑ i, w i with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hw i
  rcases hS0.eq_or_lt with h0 | hpos
  · have hw0 : ∀ i, w i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hw i)).1 h0.symm i (Finset.mem_univ i)
    simp [hw0, zero_pow (by omega : n ≠ 0)]
  · have hw1 : ∑ i, w i / S = 1 := by rw [← Finset.sum_div]; exact div_self hpos.ne'
    have h := Real.pow_arith_mean_le_arith_mean_pow Finset.univ (fun i => w i / S) f
      (fun i _ => div_nonneg (hw i) hS0) hw1 (fun i _ => hf i) n
    have e1 : ∑ i, w i / S * f i = (∑ i, w i * f i) / S := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ i, w i / S * f i ^ n = (∑ i, w i * f i ^ n) / S := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, e2, div_pow] at h
    have hSn : 0 < S ^ n := pow_pos hpos n
    rw [div_le_div_iff₀ hSn hpos] at h
    have : S ^ n = S ^ (n - 1) * S := by rw [← pow_succ]; congr 1; omega
    rw [this] at h
    nlinarith [h, pow_pos hpos (n - 1)]

/-- A weighted sum of nonnegative functions with integrable `n`-th powers has an integrable
`n`-th power, with the weighted moment bound. -/
private lemma step3s_wsum_moment {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (f : ι → Ω' → ℝ) (hf0 : ∀ i x, 0 ≤ f i x) {n : ℕ} (hn : 1 ≤ n) {B : ℝ}
    (hfi : ∀ i, Integrable (fun x => f i x ^ n) P ∧ ∫ x, f i x ^ n ∂P ≤ B)
    (Q : Ω' → ℝ) (hQm : AEStronglyMeasurable Q P) (hQ0 : ∀ x, 0 ≤ Q x)
    (hQ : ∀ x, Q x ≤ ∑ i, w i * f i x) :
    Integrable (fun x => Q x ^ n) P ∧ ∫ x, Q x ^ n ∂P ≤ (∑ i, w i) ^ n * B := by
  set S := ∑ i, w i with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hw i
  have hpt : ∀ x, Q x ^ n ≤ S ^ (n - 1) * ∑ i, w i * f i x ^ n := fun x =>
    (pow_le_pow_left₀ (hQ0 x) (hQ x) n).trans
      (step3s_wsum_pow_le w (fun i => f i x) hw (fun i => hf0 i x) hn)
  have hRi : Integrable (fun x => S ^ (n - 1) * ∑ i, w i * f i x ^ n) P :=
    (integrable_finsetSum Finset.univ fun i _ => (hfi i).1.const_mul (w i)).const_mul _
  refine ⟨Integrable.mono' hRi (hQm.pow n) (Filter.Eventually.of_forall fun x => ?_), ?_⟩
  · rw [Real.norm_of_nonneg (pow_nonneg (hQ0 x) n)]
    exact hpt x
  · calc ∫ x, Q x ^ n ∂P ≤ ∫ x, S ^ (n - 1) * ∑ i, w i * f i x ^ n ∂P :=
          integral_mono (Integrable.mono' hRi (hQm.pow n)
            (Filter.Eventually.of_forall fun x => by
              rw [Real.norm_of_nonneg (pow_nonneg (hQ0 x) n)]; exact hpt x)) hRi hpt
      _ = S ^ (n - 1) * ∑ i, w i * ∫ x, f i x ^ n ∂P := by
          rw [integral_const_mul, integral_finsetSum Finset.univ fun i _ =>
            (hfi i).1.const_mul (w i)]
          congr 1
          exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
      _ ≤ S ^ (n - 1) * ∑ i, w i * B := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (pow_nonneg hS0 _)
          exact mul_le_mul_of_nonneg_left (hfi i).2 (hw i)
      _ = S ^ n * B := by
          rw [← Finset.sum_mul]
          have : S ^ n = S ^ (n - 1) * S := by rw [← pow_succ]; congr 1; omega
          rw [this]; ring

/-- A constant plus a finite sum of nonnegative functions with integrable `n`-th powers. -/
private lemma step3s_const_sum_moment {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] {ι : Type*} [Fintype ι] {A : ℝ} (hA : 0 ≤ A) (z : ι → Ω' → ℝ)
    (hz0 : ∀ i x, 0 ≤ z i x) {n : ℕ} (hn : 1 ≤ n) {B : ℝ}
    (hzi : ∀ i, Integrable (fun x => z i x ^ n) P ∧ ∫ x, z i x ^ n ∂P ≤ B)
    (hm : AEStronglyMeasurable (fun x => A + ∑ i, z i x) P) :
    Integrable (fun x => (A + ∑ i, z i x) ^ n) P ∧
      ∫ x, (A + ∑ i, z i x) ^ n ∂P ≤ 2 ^ (n - 1) * (A ^ n + (Fintype.card ι : ℝ) ^ n * B) := by
  have hZ0 : ∀ x, 0 ≤ ∑ i, z i x := fun x => Finset.sum_nonneg fun i _ => hz0 i x
  have hpt : ∀ x, (A + ∑ i, z i x) ^ n ≤
      2 ^ (n - 1) * (A ^ n + (Fintype.card ι : ℝ) ^ (n - 1) * ∑ i, z i x ^ n) := by
    intro x
    refine (add_pow_le hA (hZ0 x) n).trans ?_
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by positivity)
    have h := step3s_wsum_pow_le (fun _ : ι => (1 : ℝ)) (fun i => z i x)
      (fun _ => zero_le_one) (fun i => hz0 i x) hn
    simpa using h
  have hRi : Integrable (fun x => 2 ^ (n - 1) *
      (A ^ n + (Fintype.card ι : ℝ) ^ (n - 1) * ∑ i, z i x ^ n)) P :=
    ((integrable_const _).add
      ((integrable_finsetSum Finset.univ fun i _ => (hzi i).1).const_mul _)).const_mul _
  have hI : Integrable (fun x => (A + ∑ i, z i x) ^ n) P :=
    Integrable.mono' hRi (hm.pow n) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (pow_nonneg (add_nonneg hA (hZ0 x)) n)]; exact hpt x)
  refine ⟨hI, ?_⟩
  calc ∫ x, (A + ∑ i, z i x) ^ n ∂P
      ≤ ∫ x, 2 ^ (n - 1) * (A ^ n + (Fintype.card ι : ℝ) ^ (n - 1) * ∑ i, z i x ^ n) ∂P :=
        integral_mono hI hRi hpt
    _ = 2 ^ (n - 1) * (A ^ n + (Fintype.card ι : ℝ) ^ (n - 1) * ∑ i, ∫ x, z i x ^ n ∂P) := by
        rw [integral_const_mul, integral_add (integrable_const _)
          ((integrable_finsetSum Finset.univ fun i _ => (hzi i).1).const_mul _),
          integral_const_mul, integral_finsetSum Finset.univ fun i _ => (hzi i).1]
        simp
    _ ≤ 2 ^ (n - 1) * (A ^ n + (Fintype.card ι : ℝ) ^ (n - 1) * ∑ _i : ι, B) := by
        refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => (hzi i).2) (by positivity)
    _ = 2 ^ (n - 1) * (A ^ n + (Fintype.card ι : ℝ) ^ n * B) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have : (Fintype.card ι : ℝ) ^ n = (Fintype.card ι : ℝ) ^ (n - 1) * Fintype.card ι := by
          rw [← pow_succ]; congr 1; omega
        rw [this]; ring

/-- The resolvent of the single-time realization is continuous in the sample off the real
axis. -/
private lemma step3s_continuous_resolvent (g u : ℝ) (W L : ℕ) {z : ℂ} (hz : z.im ≠ 0) :
    Continuous fun ω : Ω W L => resolventMat (flowH g W L u ω) z := by
  have hV : Continuous fun ω : Ω W L => blockV W L ω := by
    simp only [blockV_eq_sum_blockBasis]
    fun_prop
  have hF : Continuous fun ω : Ω W L => flowH g W L u ω := by
    unfold flowH blockFlow
    fun_prop
  have hc : Continuous fun ω : Ω W L => flowH g W L u ω - z • (1 : Matrix _ _ ℂ) :=
    hF.sub continuous_const
  refine continuous_iff_continuousAt.2 fun ω => ?_
  have hu := isUnit_sub_smul_one (flowH_isHermitian g W L u ω) hz
  have hdet : (flowH g W L u ω - z • (1 : Matrix _ _ ℂ)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  refine (continuousAt_matrix_inv _ ?_).comp hc.continuousAt
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ hdet

open scoped Matrix.Norms.L2Operator in
/-- The moments of `K_c^n` from the moments of the blocks of `G`. -/
private lemma step3sK_moment (p : FlowPt) (W : ℕ)
    (hz : (zChar p.g p.E (mRoot p.g p.L p.E) p.u).im ≠ 0) {n : ℕ} (hn : 1 ≤ n) {B : ℝ}
    (hcr : ∀ y z : Fin p.L, Integrable (fun ω => ‖blockOf (flowG W p ω) y z‖ ^ n) (μ W p.L) ∧
      ∫ ω, ‖blockOf (flowG W p ω) y z‖ ^ n ∂(μ W p.L) ≤ B) (a b c : Fin p.L) :
    Continuous (fun ω => step3sK (flowG W p ω) a b c) ∧
    Integrable (fun ω => step3sK (flowG W p ω) a b c ^ n) (μ W p.L) ∧
      ∫ ω, step3sK (flowG W p ω) a b c ^ n ∂(μ W p.L) ≤
        2 ^ (n - 1) * (((W : ℝ) + 1) ^ n + 9 ^ n * B) := by
  have hGc : Continuous fun ω : Ω W p.L => flowG W p ω :=
    step3s_continuous_resolvent p.g p.u W p.L hz
  have hbc : ∀ y z : Fin p.L, Continuous fun ω : Ω W p.L => ‖blockOf (flowG W p ω) y z‖ := by
    intro y z
    refine Continuous.norm (continuous_matrix fun α β => ?_)
    exact (continuous_apply (z, β)).comp ((continuous_apply (y, α)).comp hGc)
  have hKc : Continuous (fun ω : Ω W p.L => step3sK (flowG W p ω) a b c) := by
    unfold step3sK
    exact continuous_const.add (continuous_finsetSum _ fun ij _ => hbc _ _)
  have h := step3s_const_sum_moment (μ W p.L) (A := (W : ℝ) + 1) (by positivity)
    (fun (ij : Fin 3 × Fin 3) ω => ‖blockOf (flowG W p ω) (![a, b, c] ij.1) (![a, b, c] ij.2)‖)
    (fun _ _ => norm_nonneg _) hn (B := B) (fun ij => hcr _ _) hKc.aestronglyMeasurable
  refine ⟨hKc, h.1, h.2.trans (le_of_eq ?_)⟩
  simp [Fintype.card_prod]

open scoped Matrix.Norms.L2Operator in
/-- A crude moment from a pointwise bound `Q ≤ w Σ_c K_c^j`. -/
private lemma step3s_crude_moment (p : FlowPt) (W : ℕ)
    (hz : (zChar p.g p.E (mRoot p.g p.L p.E) p.u).im ≠ 0) {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j)
    {B : ℝ}
    (hcr : ∀ y z : Fin p.L, Integrable (fun ω => ‖blockOf (flowG W p ω) y z‖ ^ (j * n))
      (μ W p.L) ∧ ∫ ω, ‖blockOf (flowG W p ω) y z‖ ^ (j * n) ∂(μ W p.L) ≤ B) (a b : Fin p.L)
    {w : ℝ} (hw : 0 ≤ w) (Q : Ω W p.L → ℝ) (hQm : AEStronglyMeasurable Q (μ W p.L))
    (hQ0 : ∀ x, 0 ≤ Q x) (hQ : ∀ x, Q x ≤ w * ∑ c, step3sK (flowG W p x) a b c ^ j) :
    ∫ x, Q x ^ n ∂(μ W p.L) ≤
      (w * p.L) ^ n * (2 ^ (j * n - 1) * (((W : ℝ) + 1) ^ (j * n) + 9 ^ (j * n) * B)) := by
  have hjn : 1 ≤ j * n := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hK := fun c => step3sK_moment p W hz hjn hcr a b c
  have h := step3s_wsum_moment (μ W p.L) (fun _ : Fin p.L => w) (fun _ => hw)
    (fun c x => step3sK (flowG W p x) a b c ^ j) (fun c x => by
      have := step3sK_ge (flowG W p x) a b c
      have : (0 : ℝ) ≤ step3sK (flowG W p x) a b c := by
        have : (0 : ℝ) ≤ W := Nat.cast_nonneg W
        linarith
      positivity) hn
    (B := 2 ^ (j * n - 1) * (((W : ℝ) + 1) ^ (j * n) + 9 ^ (j * n) * B))
    (fun c => by
      obtain ⟨-, h1, h2⟩ := hK c
      simp only [← pow_mul]
      exact ⟨h1, h2⟩) Q hQm hQ0 (fun x => (hQ x).trans (le_of_eq (Finset.mul_sum _ _ _)))
  refine h.2.trans (le_of_eq ?_)
  simp [mul_comm]

end Step3CrudeMoment

/-! ### The same-sign pair moments at fixed `W` -/

section Step3Aux

/-- The Dyson matrix is symmetric. -/
private theorem step3s_dysonMat_symm (b β : ℝ) (L : ℕ) (z m : ℂ) (i j : Fin L) :
    dysonMat b β L z m i j = dysonMat b β L z m j i := by
  have hA : (cycleAdj L).transpose = cycleAdj L := by
    ext i j
    simp only [Matrix.transpose_apply, cycleAdj, Matrix.of_apply]
    rw [add_comm]
  have h : (dysonMat b β L z m).transpose = dysonMat b β L z m := by
    unfold dysonMat
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_smul, Matrix.transpose_one, hA]
  conv_lhs => rw [← h]
  rfl

/-- The mixed kernel of a symmetric matrix is symmetric. -/
private theorem step3s_mixedKer_symm {L : ℕ} (P : Matrix (Fin L) (Fin L) ℝ)
    (hP : ∀ a b, P a b = P b a) (u : ℝ) (a b : Fin L) :
    mixedKer P u a b = mixedKer P u b a := by
  have hPt : P.transpose = P := by ext i j; exact (hP j i)
  set B := (1 : Matrix (Fin L) (Fin L) ℝ) - u • P with hB
  have hBt : B.transpose = B := by
    rw [hB, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hPt]
  have hcomm : P * B = B * P := by
    rw [hB, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  have hinv : P * B⁻¹ = B⁻¹ * P := by
    by_cases hd : IsUnit B.det
    · calc P * B⁻¹ = B⁻¹ * B * (P * B⁻¹) := by rw [Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
        _ = B⁻¹ * (B * P) * B⁻¹ := by simp only [Matrix.mul_assoc]
        _ = B⁻¹ * (P * B) * B⁻¹ := by rw [hcomm]
        _ = B⁻¹ * P * (B * B⁻¹) := by simp only [Matrix.mul_assoc]
        _ = B⁻¹ * P := by rw [Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    · rw [Matrix.nonsing_inv_apply_not_isUnit _ hd, Matrix.mul_zero, Matrix.zero_mul]
  have hK : (mixedKer P u).transpose = mixedKer P u := by
    unfold mixedKer
    rw [← hB, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hBt, hPt, hinv]
  conv_lhs => rw [← hK]
  rfl

/-- `P_ab = γ|M_ab|²` is symmetric. -/
private theorem step3s_pairP_symm (b β : ℝ) (L : ℕ) (z m : ℂ) (x y : Fin L) :
    pairP β (dysonMat b β L z m) x y = pairP β (dysonMat b β L z m) y x := by
  simp only [pairP, Matrix.of_apply, step3s_dysonMat_symm b β L z m x y]

/-- The length-one loop against `m` is the centered block trace. -/
private theorem step3s_loop_one_sub (g E : ℝ) (W L : ℕ) (hW : 1 ≤ W) (hL : 1 ≤ L) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (c : Fin L) :
    ‖loopTr G ![c] ![true] - m‖ =
      ‖blockTr (G - dysonMat (hopB g) (gammaG g) L E m ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) c c‖ := by
  have hM := loopTr_one_dysonMat g E W L hW hL m hm c true
  simp only [ite_true] at hM
  have hbt : ∀ X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ,
      blockTr X c c = loopTr X ![c] ![true] := by
    intro X; rw [loopTr_one]; rfl
  have e : blockTr (G - dysonMat (hopB g) (gammaG g) L E m ⊗ₖ
      (1 : Matrix (Fin W) (Fin W) ℂ)) c c = blockTr G c c -
        blockTr (dysonMat (hopB g) (gammaG g) L E m ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) c c := by
    unfold blockTr
    simp only [Matrix.sub_apply, Finset.sum_sub_distrib, mul_sub]
  rw [e, hbt G, hbt, hM]

/-- `|m| ≤ max_{ab} |M_ab|`: the diagonal of the Dyson matrix is `m`. -/
private theorem step3s_norm_m_le (g E : ℝ) (L : ℕ) (hL : 1 ≤ L) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {C : ℝ}
    (hC : ∀ a b, ‖dysonMat (hopB g) (gammaG g) L E m a b‖ ≤ C) : ‖m‖ ≤ C := by
  have hM := loopTr_one_dysonMat g E 1 L le_rfl hL m hm ⟨0, by omega⟩ true
  simp only [ite_true] at hM
  rw [loopTr_one] at hM
  rw [← hM]
  refine le_trans (le_of_eq ?_) (hC ⟨0, by omega⟩ ⟨0, by omega⟩)
  simp [Matrix.kroneckerMap_apply]

/-- Sums against the coefficients of the two cut terms:
`Σ_{l'} ([l'_2 = b] A_{l'_1} + [l'_1 = a] B_{l'_2}) f_{l'} = Σ_c A_c f_{cb} + Σ_c B_c f_{ac}`. -/
private theorem step3s_sum_pairs {L : ℕ} (A B : Fin L → ℝ) (f : Fin L × Fin L → ℝ)
    (a b : Fin L) :
    ∑ l' : Fin L × Fin L, ((if l'.2 = b then A l'.1 else 0) + (if l'.1 = a then B l'.2 else 0)) *
      f l' = ∑ c, A c * f (c, b) + ∑ c, B c * f (a, c) := by
  rw [Fintype.sum_prod_type]
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  congr 1
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_ite_eq']; simp
  · have e : ∀ x : Fin L, (∑ y : Fin L, if x = a then B y * f (x, y) else 0) =
        if x = a then ∑ y, B y * f (x, y) else 0 := fun x => by
      split_ifs <;> simp
    simp only [e]
    rw [Finset.sum_ite_eq']; simp

/-- The light-term rate: `2γW(ωζ)W⁻³(ωWRζ)(Wω/η) ≤ 2C ω³ R ζ_v²/(1-r)` with
`η = (1-r)γ Im m`, `Im m ≥ C⁻¹`, `ζ ≤ ζ_v`. -/
private theorem step3s_num_light {γ Wr ω ζ ζv Rr r Im CR : ℝ} (hγ : 0 < γ) (hW : 0 < Wr)
    (hω : 0 ≤ ω) (hζ : 0 ≤ ζ) (hζv : ζ ≤ ζv) (hR : 0 ≤ Rr) (h1r : 0 < 1 - r)
    (hCR : 0 < CR) (hIm : CR⁻¹ ≤ Im) :
    2 * (γ * Wr) * (ω * ζ) * (Wr⁻¹ ^ 3 * ((ω * (Wr * Rr * ζ)) * (Wr * (ω * 1) /
      ((1 - r) * γ * Im)))) ≤ 2 * CR * ω ^ 3 * Rr * ζv ^ 2 * (1 - r)⁻¹ := by
  have hIm0 : 0 < Im := lt_of_lt_of_le (inv_pos.mpr hCR) hIm
  have hIC : 1 ≤ CR * Im := by
    have := mul_le_mul_of_nonneg_left hIm hCR.le
    rwa [mul_inv_cancel₀ hCR.ne'] at this
  have e : 2 * (γ * Wr) * (ω * ζ) * (Wr⁻¹ ^ 3 * ((ω * (Wr * Rr * ζ)) * (Wr * (ω * 1) /
      ((1 - r) * γ * Im)))) = 2 * ω ^ 3 * Rr * ζ ^ 2 * (1 - r)⁻¹ * Im⁻¹ := by
    field_simp
  rw [e]
  have h1 : ζ ^ 2 ≤ ζv ^ 2 := pow_le_pow_left₀ hζ hζv 2
  have h2 : Im⁻¹ ≤ CR := by
    rw [inv_le_iff_one_le_mul₀ hIm0]; linarith
  have h0 : 0 ≤ 2 * ω ^ 3 * Rr * (1 - r)⁻¹ := by
    have := inv_nonneg.mpr h1r.le
    positivity
  calc 2 * ω ^ 3 * Rr * ζ ^ 2 * (1 - r)⁻¹ * Im⁻¹ =
      (2 * ω ^ 3 * Rr * (1 - r)⁻¹) * (ζ ^ 2 * Im⁻¹) := by ring
    _ ≤ (2 * ω ^ 3 * Rr * (1 - r)⁻¹) * (ζv ^ 2 * CR) := by
        gcongr
    _ = _ := by ring

/-- The bracket rate: `4(γ/W)W⁻⁴(ωWRζ)⁴(Wω/η) ≤ 4C ω⁵ R⁴ ζ_v⁴/(1-r)`. -/
private theorem step3s_num_gamma {γ Wr ω ζ ζv Rr r Im CR : ℝ} (hγ : 0 < γ) (hW : 0 < Wr)
    (hω : 0 ≤ ω) (hζ : 0 ≤ ζ) (hζv : ζ ≤ ζv) (_hR : 0 ≤ Rr) (h1r : 0 < 1 - r)
    (hCR : 0 < CR) (hIm : CR⁻¹ ≤ Im) :
    4 * (γ / Wr) * (Wr⁻¹ ^ 4 * (ω * (Wr * Rr * ζ)) ^ 4 * (Wr * (ω * 1) /
      ((1 - r) * γ * Im))) ≤ 4 * CR * ω ^ 5 * Rr ^ 4 * ζv ^ 4 * (1 - r)⁻¹ := by
  have hIm0 : 0 < Im := lt_of_lt_of_le (inv_pos.mpr hCR) hIm
  have hIC : 1 ≤ CR * Im := by
    have := mul_le_mul_of_nonneg_left hIm hCR.le
    rwa [mul_inv_cancel₀ hCR.ne'] at this
  have e : 4 * (γ / Wr) * (Wr⁻¹ ^ 4 * (ω * (Wr * Rr * ζ)) ^ 4 * (Wr * (ω * 1) /
      ((1 - r) * γ * Im))) = 4 * ω ^ 5 * Rr ^ 4 * ζ ^ 4 * (1 - r)⁻¹ * Im⁻¹ := by
    field_simp
  rw [e]
  have h1 : ζ ^ 4 ≤ ζv ^ 4 := pow_le_pow_left₀ hζ hζv 4
  have h2 : Im⁻¹ ≤ CR := by
    rw [inv_le_iff_one_le_mul₀ hIm0]; linarith
  have h0 : 0 ≤ 4 * ω ^ 5 * Rr ^ 4 * (1 - r)⁻¹ := by
    have := inv_nonneg.mpr h1r.le
    positivity
  calc 4 * ω ^ 5 * Rr ^ 4 * ζ ^ 4 * (1 - r)⁻¹ * Im⁻¹ =
      (4 * ω ^ 5 * Rr ^ 4 * (1 - r)⁻¹) * (ζ ^ 4 * Im⁻¹) := by ring
    _ ≤ (4 * ω ^ 5 * Rr ^ 4 * (1 - r)⁻¹) * (ζv ^ 4 * CR) := by
        gcongr
    _ = _ := by ring

end Step3Aux

section Step3AtW

open scoped Matrix.Norms.L2Operator

set_option maxHeartbeats 4000000 in
-- The fixed-`W` instantiation of the moment comparison core is long.
/-- The moments of the same-sign pair error at the terminal time `v` at fixed `W`, from the
good events of Steps 1–2 at the times of `(s, v)`, the input (5.22) [gc:eq:one-step-input] at
`s`, the Dyson bounds (6.2) [fo:eq:propagation-dyson] and the crude moments: the moment comparison
for each `D₂(a,b;+,+)` with the generator (5.17) [fo:eq:error-hierarchy], the majorant of the
same-sign loop and Grönwall's inequality. -/
private theorem step3s_atW (g E : ℝ) {W L : ℕ} (hW : 1 ≤ W) (hL : 3 ≤ L) (hg : 0 ≤ g)
    (hroot : IsDysonRootV (hopB g) (gammaG g) L E (mRoot g L E))
    {s v : ℝ} (hs : 1 / 2 ≤ s) (hsv : s ≤ v) (hv1 : v < 1) (p : ℕ) (hp : 1 ≤ p)
    {CR ω Rr Sw δ MA MB MI B16 B12 B8 : ℝ} (hCR : 1 ≤ CR) (hω : 0 ≤ ω) (hR : 0 ≤ Rr)
    (hSw : 0 ≤ Sw) (hδ : 0 ≤ δ)
    (hIm : CR⁻¹ ≤ (mRoot g L E).im) (hmC : ‖mRoot g L E‖ ≤ CR)
    (hrow1 : ∀ a, gammaG g * ∑ b, (‖dysonMat (hopB g) (gammaG g) L E (mRoot g L E) a b‖ +
      ‖dysonMat (hopB g) (gammaG g) L E (mRoot g L E) a b‖ ^ 2) ≤ CR)
    (hrow2 : ∀ r ∈ Set.Icc s v, ∀ a, ∑ b, ‖(1 - (r : ℂ) • pairQ (gammaG g)
      (dysonMat (hopB g) (gammaG g) L E (mRoot g L E)))⁻¹ a b‖ ≤ CR)
    (hK : ∀ r ∈ Set.Icc s v, ∀ x y : Fin L,
      ‖primLoop g W L E (mRoot g L E) r ![x, y] ![true, true]‖ ≤ W)
    (w : ℝ → Fin L → Fin L → ℝ) (hw0 : ∀ r x y, 0 ≤ w r x y)
    (hwrow : ∀ r ∈ Set.Icc s v, ∀ x, ∑ y, w r y x ≤ Sw * ellProp g L r ∧
      ∑ y, w r x y ≤ Sw * ellProp g L r)
    (Bad : ℝ → Set (Ω W L)) (hBad : ∀ r ∈ Set.Ioo s v, μ W L (Bad r) ≤ ENNReal.ofReal δ)
    (hgood : ∀ r ∈ Set.Ioo s v, ∀ x, x ∉ Bad r →
      (∀ y z, ‖blockOf (flowG W ⟨g, E, L, r⟩ x) y z‖ ≤ ω * (W * Rr * zetaProp g W L r)) ∧
      (∀ y, (blockTr (flowG W ⟨g, E, L, r⟩ x) y y).im ≤ ω * 1) ∧
      (∀ c, ‖blockTr (flowG W ⟨g, E, L, r⟩ x - flowM W ⟨g, E, L, r⟩) c c‖ ≤
        ω * zetaProp g W L r) ∧
      (∀ y z, ‖flowErr W ⟨g, E, L, r⟩ ![y, z] ![true, false] x‖ ≤
        ω * (Rr ^ 6 * zetaProp g W L r ^ 2 * w r y z)))
    (Bad0 : Set (Ω W L)) (hBad0 : μ W L Bad0 ≤ ENNReal.ofReal δ)
    (hgood0 : ∀ x, x ∉ Bad0 → ∀ a b : Fin L,
      ‖flowErr W ⟨g, E, L, s⟩ ![a, b] ![true, true] x‖ ≤ ω * zetaProp g W L s ^ 2)
    (hcr16 : ∀ r ∈ Set.Icc s v, ∀ y z : Fin L,
      Integrable (fun x => ‖blockOf (flowG W ⟨g, E, L, r⟩ x) y z‖ ^ (4 * (2 * (2 * p))))
        (μ W L) ∧
      ∫ x, ‖blockOf (flowG W ⟨g, E, L, r⟩ x) y z‖ ^ (4 * (2 * (2 * p))) ∂(μ W L) ≤ B16)
    (hcr12 : ∀ r ∈ Set.Icc s v, ∀ y z : Fin L,
      Integrable (fun x => ‖blockOf (flowG W ⟨g, E, L, r⟩ x) y z‖ ^ (6 * (2 * p))) (μ W L) ∧
      ∫ x, ‖blockOf (flowG W ⟨g, E, L, r⟩ x) y z‖ ^ (6 * (2 * p)) ∂(μ W L) ≤ B12)
    (hcr8 : ∀ y z : Fin L,
      Integrable (fun x => ‖blockOf (flowG W ⟨g, E, L, s⟩ x) y z‖ ^ (2 * (2 * (2 * p))))
        (μ W L) ∧
      ∫ x, ‖blockOf (flowG W ⟨g, E, L, s⟩ x) y z‖ ^ (2 * (2 * (2 * p))) ∂(μ W L) ≤ B8)
    (hMA : (gammaG g * W * (6 + 2 * CR) * L) ^ (2 * (2 * p)) * (2 ^ (4 * (2 * (2 * p)) - 1) *
      (((W : ℝ) + 1) ^ (4 * (2 * (2 * p))) + 9 ^ (4 * (2 * (2 * p))) * B16)) ≤ MA)
    (hMB : (4 * gammaG g * L) ^ (2 * p) * (2 ^ (6 * (2 * p) - 1) *
      (((W : ℝ) + 1) ^ (6 * (2 * p)) + 9 ^ (6 * (2 * p)) * B12)) ≤ MB)
    (hMI : 2 ^ (2 * (2 * p)) * (2 ^ (2 * (2 * (2 * p)) - 1) *
      (((W : ℝ) + 1) ^ (2 * (2 * (2 * p))) + 9 ^ (2 * (2 * (2 * p))) * B8)) ≤ MI)
    (a b : Fin L) :
    (∫ x, ‖flowErr W ⟨g, E, L, v⟩ ![a, b] ![true, true] x‖ ^ (2 * p) ∂(μ W L)) ^
        (1 / (2 * (p : ℝ))) ≤
      Real.exp (CR * CR * (v - s)) *
        ((1 - s) / (1 - v)) ^ (1 + Sw * ω * Rr ^ 6 * zetaProp g W L v) *
        (Real.sqrt ((ω * zetaProp g W L s ^ 2 +
              (Real.sqrt MI * Real.sqrt δ) ^ (1 / (2 * (p : ℝ)))) ^ 2 +
            (2 * p - 1) * ((4 * CR * ω ^ 5 * Rr ^ 4 * zetaProp g W L v ^ 4 +
              (Real.sqrt MB * Real.sqrt δ) ^ (1 / (p : ℝ))) * Real.log ((1 - s) / (1 - v)))) +
          (2 * CR * ω ^ 3 * Rr * zetaProp g W L v ^ 2 +
            (Real.sqrt MA * Real.sqrt δ) ^ (1 / (2 * (p : ℝ)))) *
              Real.log ((1 - s) / (1 - v))) := by
  set m := mRoot g L E with hmdef
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hL1 : 1 ≤ L := by omega
  have hs0 : 0 ≤ s := by linarith
  have hv0 : 0 ≤ v := hs0.trans hsv
  have hCR0 : 0 < CR := by linarith
  have hγW : 0 < gammaG g * W := mul_pos hγ hW0
  have : Nonempty (Fin L) := ⟨⟨0, by omega⟩⟩
  set σ2 := gammaG g / W with hσ2def
  have hσ2 : 0 ≤ σ2 := by positivity
  set Y : Fin L × Fin L → ℝ → Ω W L → ℂ := fun l r x => step3s_field g E m W L r x l with hYdef
  have hY : ∀ l, HeatClass (Y l) (-1 / 2) ((1 + v) / 2) := fun l =>
    step3s_heatClass g E m W L hW hL hroot l (by norm_num) (by linarith)
  have eY : ∀ l (r : ℝ), 0 ≤ r → ∀ x, Y l r (Real.sqrt (r * σ2) • x) =
      flowErr W ⟨g, E, L, r⟩ ![l.1, l.2] ![true, true] x := fun l r hr x =>
    (step3s_flowErr_eq g E W L hr l x).symm
  have eGen : ∀ l (r : ℝ), 0 ≤ r → ∀ x, coordGen σ2 (Y l) r (Real.sqrt (r * σ2) • x) =
      blockGen W L (gammaG g) (fun r N => resLoop g E m ![l.1, l.2] ![true, true] r N -
        primLoop g W L E m r ![l.1, l.2] ![true, true]) r (flowH g W L r x) := by
    intro l r hr x
    rw [step3s_flowH_eq g W L hr x]
    exact step3s_coordGen_eq g E m W L l r _
  have eGam : ∀ l (r : ℝ), 0 ≤ r → ∀ x,
      coordGamma σ2 (Y l r) (Y l r) (Real.sqrt (r * σ2) • x) =
      blockGamma W L (gammaG g) (resLoop g E m ![l.1, l.2] ![true, true] r)
        (resLoop g E m ![l.1, l.2] ![true, true] r) (flowH g W L r x) := by
    intro l r hr x
    rw [step3s_flowH_eq g W L hr x]
    exact step3s_coordGamma_eq g E m W L l r _
  have eD : ∀ l (r : ℝ), 0 ≤ r → ∀ x, ‖Y l r (Real.sqrt (r * σ2) • x)‖ =
      ‖resLoop g E m ![l.1, l.2] ![true, true] r (flowH g W L r x) -
        primLoop g W L E m r ![l.1, l.2] ![true, true]‖ := by
    intro l r hr x
    rw [eY l r hr x]
    rfl
  -- the bad sets
  set T : ℝ → Set (Ω W L) := fun r => toMeasurable (μ W L) (Bad r) with hTdef
  have hTm : ∀ r, MeasurableSet (T r) := fun r => measurableSet_toMeasurable _ _
  have hTδ : ∀ r ∈ Set.Ioo s v,
      stdGauss (Fin L × Fin W × Fin W) (T r) ≤ ENNReal.ofReal δ := fun r hr => by
    change μ W L (toMeasurable (μ W L) (Bad r)) ≤ _
    rw [measure_toMeasurable]; exact hBad r hr
  have hTsub : ∀ r x, x ∉ T r → x ∉ Bad r := fun r x hx h => hx (subset_toMeasurable _ _ h)
  set T0 := toMeasurable (μ W L) Bad0 with hT0def
  have hT0m : MeasurableSet T0 := measurableSet_toMeasurable _ _
  have hT0δ : stdGauss (Fin L × Fin W × Fin W) T0 ≤ ENNReal.ofReal δ := by
    change μ W L (toMeasurable (μ W L) Bad0) ≤ _
    rw [measure_toMeasurable]; exact hBad0
  have hT0sub : ∀ x, x ∉ T0 → x ∉ Bad0 := fun x hx h => hx (subset_toMeasurable _ _ h)
  -- the kernels
  set P := pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) with hPdef
  have hP0 : ∀ x z, 0 ≤ P x z := fun x z => by
    simp only [hPdef, pairP, Matrix.of_apply]; positivity
  have hProw : ∀ x, ∑ z, P x z = 1 := fun x =>
    pairP_row_sum (hopB g) (gammaG g) hγ L hL1 E m hroot x
  have hPs : ∀ x z, P x z = P z x := fun x z => step3s_pairP_symm _ _ _ _ _ x z
  set kk : ℝ → Fin L → Fin L → ℝ := fun r x y => (gammaG g * W)⁻¹ * mixedKer P r x y with hkk
  set ee : ℝ → Fin L → Fin L → ℝ := fun r x y =>
    ω * (Rr ^ 6 * zetaProp g W L r ^ 2 * w r x y) with hee
  set β : ℝ → Fin L → Fin L → ℝ := fun r c b =>
    Real.sqrt ((kk r c b + ee r c b) * (kk r b c + ee r b c)) with hβ
  set α : ℝ → Fin L × Fin L → Fin L × Fin L → ℝ := fun r l l' =>
    (if l'.2 = l.2 then ‖((gammaG g * W : ℝ) : ℂ) * primLoop g W L E m r ![l.1, l'.1] ![true, true]‖
      else 0) + (if l'.1 = l.1 then gammaG g * W * β r l'.2 l.2 else 0) with hα
  have hα0 : ∀ r l l', 0 ≤ α r l l' := by
    intro r l l'
    simp only [hα]
    refine add_nonneg ?_ ?_
    · split_ifs
      · exact norm_nonneg _
      · exact le_rfl
    · split_ifs
      · exact mul_nonneg hγW.le (Real.sqrt_nonneg _)
      · exact le_rfl
  have hζmono : ∀ r ∈ Set.Icc s v, zetaProp g W L r ≤ zetaProp g W L v := fun r hr =>
    (scale_facts g hg W L hW hL1 r v (hs0.trans hr.1) hr.2 hv1).2.2.2.2.1
  have hζ0 : ∀ r ∈ Set.Icc s v, 0 ≤ zetaProp g W L r := fun r hr =>
    le_trans (by positivity)
      (scale_facts g hg W L hW hL1 r r (hs0.trans hr.1) le_rfl (lt_of_le_of_lt hr.2 hv1)).2.2.2.1
  -- the row sums of the coefficients
  have hαs : ∀ r ∈ Set.Ioo s v, ∀ l, ∑ l', α r l l' ≤
      CR * CR + (1 + Sw * ω * Rr ^ 6 * zetaProp g W L v) * (1 - r)⁻¹ := by
    intro r hr l
    have hrI : r ∈ Set.Icc s v := ⟨hr.1.le, hr.2.le⟩
    have hr0 : 0 ≤ r := hs0.trans hr.1.le
    have hr1 : r < 1 := lt_trans hr.2 hv1
    have e := step3s_sum_pairs
      (fun c => ‖((gammaG g * W : ℝ) : ℂ) * primLoop g W L E m r ![l.1, c] ![true, true]‖)
      (fun c => gammaG g * W * β r c l.2) (fun _ => 1) l.1 l.2
    simp only [mul_one] at e
    have hsum : ∑ l', α r l l' = ∑ c, ‖((gammaG g * W : ℝ) : ℂ) *
        primLoop g W L E m r ![l.1, c] ![true, true]‖ + ∑ c, gammaG g * W * β r c l.2 := e
    rw [hsum]
    have hQ := step3s_Q_row g W L hW E m r CR hCR0.le hrow1 (hrow2 r hrI) l.1
    obtain ⟨hK0, hKr⟩ := mixedKer_nonneg_row P hP0 hProw r hr0 hr1
    have hKs : ∀ x y, mixedKer P r x y = mixedKer P r y x := fun x y =>
      step3s_mixedKer_symm P hPs r x y
    obtain ⟨hℓ1, -, -, -, -, -, hscale⟩ :=
      scale_facts g hg W L hW hL1 r r hr0 le_rfl hr1
    set S := ω * Rr ^ 6 * zetaProp g W L r ^ 2 * (Sw * ellProp g L r) with hS
    have hS' : ∀ x, ∑ y, ee r y x ≤ S ∧ ∑ y, ee r x y ≤ S := by
      intro x
      have hw := hwrow r hrI x
      constructor
      · simp only [hee, ← Finset.mul_sum]
        have : ω * (Rr ^ 6 * zetaProp g W L r ^ 2 * ∑ y, w r y x) ≤
            ω * (Rr ^ 6 * zetaProp g W L r ^ 2 * (Sw * ellProp g L r)) := by
          have := hζ0 r hrI
          gcongr
          exact hw.1
        linarith [show S = ω * (Rr ^ 6 * zetaProp g W L r ^ 2 * (Sw * ellProp g L r)) by ring]
      · simp only [hee, ← Finset.mul_sum]
        have : ω * (Rr ^ 6 * zetaProp g W L r ^ 2 * ∑ y, w r x y) ≤
            ω * (Rr ^ 6 * zetaProp g W L r ^ 2 * (Sw * ellProp g L r)) := by
          have := hζ0 r hrI
          gcongr
          exact hw.2
        linarith [show S = ω * (Rr ^ 6 * zetaProp g W L r ^ 2 * (Sw * ellProp g L r)) by ring]
    have hmaj := step3s_maj_sum hγW (mixedKer P r) hK0 hKr hKs (ee r)
      (fun x y => by simp only [hee]; have := hζ0 r hrI; have := hw0 r x y; positivity) hS' l.2
    have hB : ∑ c, gammaG g * W * β r c l.2 ≤ (1 - r)⁻¹ + gammaG g * W * S := by
      rw [← Finset.mul_sum]
      exact hmaj
    have hγWS : gammaG g * W * S ≤ Sw * ω * Rr ^ 6 * zetaProp g W L v * (1 - r)⁻¹ := by
      have e2 : gammaG g * W * S = Sw * ω * Rr ^ 6 * zetaProp g W L r *
          (gammaG g * W * ellProp g L r * zetaProp g W L r) := by rw [hS]; ring
      rw [e2, hscale]
      have := hζmono r hrI
      have := inv_nonneg.mpr (show (0 : ℝ) ≤ 1 - r by linarith)
      gcongr
    have := inv_nonneg.mpr (show (0 : ℝ) ≤ 1 - r by linarith)
    nlinarith
  -- the generator at a good point
  have hGgood : ∀ r ∈ Set.Ioo s v, ∀ l x, x ∉ T r →
      ‖coordGen σ2 (Y l) r (Real.sqrt (r * σ2) • x)‖ ≤
        2 * CR * ω ^ 3 * Rr * zetaProp g W L v ^ 2 * (1 - r)⁻¹ +
          ∑ l', α r l l' * ‖Y l' r (Real.sqrt (r * σ2) • x)‖ := by
    intro r hr l x hx
    have hrI : r ∈ Set.Icc s v := ⟨hr.1.le, hr.2.le⟩
    have hr0 : 0 ≤ r := hs0.trans hr.1.le
    have hr1 : r < 1 := lt_trans hr.2 hv1
    obtain ⟨hop, hden, havg, hpair⟩ := hgood r hr x (hTsub r x hx)
    rw [eGen l r hr0 x]
    set M := flowH g W L r x with hMdef
    have hM : M.IsHermitian := flowH_isHermitian g W L r x
    have hz : 0 < (zChar g E m r).im := by rw [im_zChar]; exact etaChar_pos g m hroot.1 hr1
    have he : ∀ y z, ‖loopTr (resolventMat M (zChar g E m r)) ![y, z] ![true, false] -
        ((kk r y z : ℝ) : ℂ)‖ ≤ ee r y z := by
      intro y z
      have h := hpair y z
      unfold flowErr at h
      rw [primLoop_two_pm] at h
      have e1 : ((kk r y z : ℝ) : ℂ) = ((gammaG g * W : ℝ) : ℂ)⁻¹ *
          ((mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) r y z : ℝ) : ℂ) := by
        simp only [hkk]; push_cast; ring
      rw [e1]
      exact h
    have hsplit := step3s_gen_split g E m W L hW hL hroot ⟨by linarith, hr1⟩ hM l.1 l.2
      (fun c => β r c l.2) (fun c => step3s_pp_le_maj (resolventMat M (zChar g E m r))
        (kk r) (ee r) he c l.2)
    have havg' : ∀ c, ‖loopTr (resolventMat M (zChar g E m r)) ![c] ![true] - m‖ ≤
        ω * zetaProp g W L r := by
      intro c
      rw [step3s_loop_one_sub g E W L hW hL1 m hroot]
      exact havg c
    have hlight := step3s_light_le g E m hW hM hz (O := ω * (W * Rr * zetaProp g W L r))
      (ρ := ω * 1) (τ := ω * zetaProp g W L r) (by have := hζ0 r hrI; positivity)
      (by have := hζ0 r hrI; positivity) hop hden havg' l.1 l.2
    rw [im_zChar] at hlight
    unfold etaChar at hlight
    have hnum := step3s_num_light (γ := gammaG g) (Wr := W) (ω := ω) (ζ := zetaProp g W L r)
      (ζv := zetaProp g W L v) (Rr := Rr) (r := r) (Im := m.im) (CR := CR) hγ hW0 hω
      (hζ0 r hrI) (hζmono r hrI) hR (by linarith) hCR0 hIm
    have e := step3s_sum_pairs
      (fun c => ‖((gammaG g * W : ℝ) : ℂ) * primLoop g W L E m r ![l.1, c] ![true, true]‖)
      (fun c => gammaG g * W * β r c l.2) (fun l' => ‖Y l' r (Real.sqrt (r * σ2) • x)‖) l.1 l.2
    have hsum : ∑ l', α r l l' * ‖Y l' r (Real.sqrt (r * σ2) • x)‖ =
        ∑ c, ‖((gammaG g * W : ℝ) : ℂ) * primLoop g W L E m r ![l.1, c] ![true, true]‖ *
          ‖resLoop g E m ![c, l.2] ![true, true] r M -
            primLoop g W L E m r ![c, l.2] ![true, true]‖ +
        ∑ c, gammaG g * W * β r c l.2 *
          ‖resLoop g E m ![l.1, c] ![true, true] r M -
            primLoop g W L E m r ![l.1, c] ![true, true]‖ := by
      rw [e]
      simp only [eD _ r hr0 x]
      rfl
    rw [hsum]
    refine hsplit.trans ?_
    linarith
  -- the bracket at a good point
  have hΓgood : ∀ r ∈ Set.Ioo s v, ∀ l x, x ∉ T r →
      ‖coordGamma σ2 (Y l r) (Y l r) (Real.sqrt (r * σ2) • x)‖ ≤
        4 * CR * ω ^ 5 * Rr ^ 4 * zetaProp g W L v ^ 4 * (1 - r)⁻¹ := by
    intro r hr l x hx
    have hrI : r ∈ Set.Icc s v := ⟨hr.1.le, hr.2.le⟩
    have hr0 : 0 ≤ r := hs0.trans hr.1.le
    have hr1 : r < 1 := lt_trans hr.2 hv1
    obtain ⟨hop, hden, -, -⟩ := hgood r hr x (hTsub r x hx)
    rw [eGam l r hr0 x]
    have h := step3s_gamma_le g E m hroot.1 hW hr1 (flowH_isHermitian g W L r x)
      (O := ω * (W * Rr * zetaProp g W L r)) (ρ := ω * 1)
      (by have := hζ0 r hrI; positivity) hop hden l.1 l.2
    rw [im_zChar] at h
    unfold etaChar at h
    exact h.trans (step3s_num_gamma hγ hW0 hω (hζ0 r hrI) (hζmono r hrI) hR (by linarith) hCR0
      hIm)
  -- the input at `s`
  have hIgood : ∀ l x, x ∉ T0 → ‖Y l s (Real.sqrt (s * σ2) • x)‖ ≤ ω * zetaProp g W L s ^ 2 := by
    intro l x hx
    rw [eY l s hs0 x]
    exact hgood0 x (hT0sub x hx) l.1 l.2
  -- the crude moments
  have hmC' : ‖m‖ ≤ CR := hmC
  have hB16 : 0 ≤ B16 := le_trans (integral_nonneg fun x => by positivity)
    (hcr16 s ⟨le_rfl, hsv⟩ ⟨0, by omega⟩ ⟨0, by omega⟩).2
  have hB12 : 0 ≤ B12 := le_trans (integral_nonneg fun x => by positivity)
    (hcr12 s ⟨le_rfl, hsv⟩ ⟨0, by omega⟩ ⟨0, by omega⟩).2
  have hjetI : ∀ l, ∀ r ∈ Set.Icc s v, _ := fun l r hr =>
    step3s_class_jet (hY l) (⟨by linarith [hr.1], by linarith [hr.2]⟩ :
      r ∈ Set.Ioo (-1 / 2 : ℝ) ((1 + v) / 2)) σ2
  have hMA' : ∀ r ∈ Set.Ioo s v, ∀ l, ∫ x, ‖coordGen σ2 (Y l) r (Real.sqrt (r * σ2) • x)‖ ^
      (2 * (2 * p)) ∂(stdGauss (Fin L × Fin W × Fin W)) ≤ MA := by
    intro r hr l
    have hrI : r ∈ Set.Icc s v := ⟨hr.1.le, hr.2.le⟩
    have hr0 : 0 ≤ r := hs0.trans hr.1.le
    have hr1 : r < 1 := lt_trans hr.2 hv1
    have hz : (zChar g E m r).im ≠ 0 := by
      rw [im_zChar]; exact (etaChar_pos g m hroot.1 hr1).ne'
    obtain ⟨-, -, -, ⟨hGc, -⟩, -⟩ := hjetI l r hrI
    have hQc : Continuous (fun x : Ω W L => ‖coordGen σ2 (Y l) r (Real.sqrt (r * σ2) • x)‖) :=
      continuous_norm.comp (hGc.comp (continuous_const_smul _))
    have h := step3s_crude_moment ⟨g, E, L, r⟩ W hz (n := 2 * (2 * p)) (j := 4) (by omega)
      (by norm_num) (hcr16 r hrI) l.1 l.2 (w := gammaG g * W * (6 + 2 * ‖m‖))
      (by positivity) (fun x => ‖coordGen σ2 (Y l) r (Real.sqrt (r * σ2) • x)‖)
      hQc.aestronglyMeasurable (fun x => norm_nonneg _) (fun x => by
        rw [eGen l r hr0 x]
        exact step3s_crude_gen g E m hW hL hroot ⟨by linarith, hr1⟩ (flowH_isHermitian g W L r x)
          (hK r hrI) l.1 l.2)
    refine le_trans h (le_trans ?_ hMA)
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine pow_le_pow_left₀ (by positivity) ?_ _
    change gammaG g * W * (6 + 2 * ‖m‖) * (L : ℝ) ≤ gammaG g * W * (6 + 2 * CR) * L
    gcongr
  have hMB' : ∀ r ∈ Set.Ioo s v, ∀ l, ∫ x, ‖coordGamma σ2 (Y l r) (Y l r)
      (Real.sqrt (r * σ2) • x)‖ ^ (2 * p) ∂(stdGauss (Fin L × Fin W × Fin W)) ≤ MB := by
    intro r hr l
    have hrI : r ∈ Set.Icc s v := ⟨hr.1.le, hr.2.le⟩
    have hr0 : 0 ≤ r := hs0.trans hr.1.le
    have hr1 : r < 1 := lt_trans hr.2 hv1
    have hz : (zChar g E m r).im ≠ 0 := by
      rw [im_zChar]; exact (etaChar_pos g m hroot.1 hr1).ne'
    obtain ⟨-, -, -, -, ⟨hΓc, -⟩⟩ := hjetI l r hrI
    have hQc : Continuous
        (fun x : Ω W L => ‖coordGamma σ2 (Y l r) (Y l r) (Real.sqrt (r * σ2) • x)‖) :=
      continuous_norm.comp (hΓc.comp (continuous_const_smul _))
    have h := step3s_crude_moment ⟨g, E, L, r⟩ W hz (n := 2 * p) (j := 6) (by omega)
      (by norm_num) (hcr12 r hrI) l.1 l.2 (w := 4 * gammaG g) (by positivity)
      (fun x => ‖coordGamma σ2 (Y l r) (Y l r) (Real.sqrt (r * σ2) • x)‖)
      hQc.aestronglyMeasurable (fun x => norm_nonneg _) (fun x => by
        rw [eGam l r hr0 x]
        exact step3s_crude_gamma g E m hroot.1 hW hr1 (flowH_isHermitian g W L r x) l.1 l.2)
    exact le_trans h hMB
  have hMI' : ∀ l, ∫ x, ‖Y l s (Real.sqrt (s * σ2) • x)‖ ^ (2 * (2 * p))
      ∂(stdGauss (Fin L × Fin W × Fin W)) ≤ MI := by
    intro l
    have hs1 : s < 1 := lt_of_le_of_lt hsv hv1
    have hz : (zChar g E m s).im ≠ 0 := by
      rw [im_zChar]; exact (etaChar_pos g m hroot.1 hs1).ne'
    obtain ⟨-, hc2, -, -, -⟩ := hjetI l s ⟨le_rfl, hsv⟩
    have hQc : Continuous (fun x : Ω W L => ‖Y l s (Real.sqrt (s * σ2) • x)‖) :=
      continuous_norm.comp (hc2.continuous.comp (continuous_const_smul _))
    obtain ⟨-, hKi, hKm⟩ := step3sK_moment ⟨g, E, L, s⟩ W hz (n := 2 * (2 * (2 * p)))
      (by omega) hcr8 l.1 l.2 l.1
    set K : Ω W L → ℝ := fun x => step3sK (flowG W ⟨g, E, L, s⟩ x) l.1 l.2 l.1 with hKdef
    have hK1 : ∀ x, (1 : ℝ) ≤ K x := fun x => by
      have := step3sK_ge (flowG W ⟨g, E, L, s⟩ x) l.1 l.2 l.1
      linarith
    have hpt : ∀ x, ‖Y l s (Real.sqrt (s * σ2) • x)‖ ≤ 2 * K x ^ 2 := by
      intro x
      rw [eY l s hs0 x]
      unfold flowErr
      refine (norm_sub_le _ _).trans ?_
      have h1 := step3s_crude_pp hW (flowG W ⟨g, E, L, s⟩ x) l.1 l.2
      have k1 : ‖blockOf (flowG W ⟨g, E, L, s⟩ x) l.1 l.2‖ ≤ K x := by
        simpa using step3sK_block (flowG W ⟨g, E, L, s⟩ x) l.1 l.2 l.1 0 1
      have k2 : ‖blockOf (flowG W ⟨g, E, L, s⟩ x) l.2 l.1‖ ≤ K x := by
        simpa using step3sK_block (flowG W ⟨g, E, L, s⟩ x) l.1 l.2 l.1 1 0
      have h2 := hK s ⟨le_rfl, hsv⟩ l.1 l.2
      have hWK : (W : ℝ) ≤ K x := by
        have := step3sK_ge (flowG W ⟨g, E, L, s⟩ x) l.1 l.2 l.1
        linarith
      have hKK : K x ≤ K x ^ 2 := le_self_pow₀ (hK1 x) (by norm_num)
      have h3 : ‖blockOf (flowG W ⟨g, E, L, s⟩ x) l.1 l.2‖ *
          ‖blockOf (flowG W ⟨g, E, L, s⟩ x) l.2 l.1‖ ≤ K x ^ 2 := by
        rw [sq]; exact mul_le_mul k1 k2 (norm_nonneg _) (by linarith [hK1 x])
      change ‖loopTr (flowG W ⟨g, E, L, s⟩ x) ![l.1, l.2] ![true, true]‖ +
        ‖primLoop g W L E m s ![l.1, l.2] ![true, true]‖ ≤ 2 * K x ^ 2
      linarith
    have hint : Integrable (fun x => (2 * K x ^ 2) ^ (2 * (2 * p))) (μ W L) := by
      have e : (fun x => (2 * K x ^ 2) ^ (2 * (2 * p))) =
          fun x => 2 ^ (2 * (2 * p)) * K x ^ (2 * (2 * (2 * p))) := by
        funext x; rw [mul_pow, ← pow_mul]
      rw [e]; exact hKi.const_mul _
    have hle : ∀ x, ‖Y l s (Real.sqrt (s * σ2) • x)‖ ^ (2 * (2 * p)) ≤
        (2 * K x ^ 2) ^ (2 * (2 * p)) := fun x => pow_le_pow_left₀ (norm_nonneg _) (hpt x) _
    calc ∫ x, ‖Y l s (Real.sqrt (s * σ2) • x)‖ ^ (2 * (2 * p)) ∂(stdGauss (Fin L × Fin W × Fin W))
        ≤ ∫ x, (2 * K x ^ 2) ^ (2 * (2 * p)) ∂(μ W L) := by
          refine integral_mono (Integrable.mono' hint (hQc.pow _).aestronglyMeasurable
            (Eventually.of_forall fun x => ?_)) hint hle
          rw [Real.norm_of_nonneg (by positivity)]; exact hle x
      _ = 2 ^ (2 * (2 * p)) * ∫ x, K x ^ (2 * (2 * (2 * p))) ∂(μ W L) := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only [mul_pow, ← pow_mul]
      _ ≤ 2 ^ (2 * (2 * p)) * (2 ^ (2 * (2 * (2 * p)) - 1) *
          (((W : ℝ) + 1) ^ (2 * (2 * (2 * p))) + 9 ^ (2 * (2 * (2 * p))) * B8)) :=
          mul_le_mul_of_nonneg_left hKm (by positivity)
      _ ≤ MI := hMI
  -- The moment comparison with Grönwall
  have hc := step3s_core σ2 hσ2 Y (a' := -1 / 2) (b' := (1 + v) / 2) (s := s) (v := v)
    (by norm_num) hs0 hsv (by linarith) hv1 hY p hp T hTm hδ hTδ T0 hT0m hT0δ α hα0
    (C := CR * CR) (κ := 1 + Sw * ω * Rr ^ 6 * zetaProp g W L v)
    (h₁ := 2 * CR * ω ^ 3 * Rr * zetaProp g W L v ^ 2)
    (b₁ := 4 * CR * ω ^ 5 * Rr ^ 4 * zetaProp g W L v ^ 4) (I₀ := ω * zetaProp g W L s ^ 2)
    (MA := MA) (MB := MB) (MI := MI) (by positivity)
    (by have := hζ0 v ⟨hsv, le_rfl⟩; positivity)
    (by have := hζ0 v ⟨hsv, le_rfl⟩; positivity) (by have := hζ0 v ⟨hsv, le_rfl⟩; positivity)
    (by have := hζ0 s ⟨le_rfl, hsv⟩; positivity) hαs hGgood hΓgood hIgood hMA' hMB' hMI' (a, b)
  have e : (∫ x, ‖flowErr W ⟨g, E, L, v⟩ ![a, b] ![true, true] x‖ ^ (2 * p) ∂(μ W L)) =
      ∫ x, ‖Y (a, b) v (Real.sqrt (v * σ2) • x)‖ ^ (2 * p)
        ∂(stdGauss (Fin L × Fin W × Fin W)) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [eY (a, b) v hv0 x]
  rw [e]
  exact hc

end Step3AtW

/-! ### Numerics of the conclusion -/

section Step3Num

/-- `√(x² + y) ≤ x + √y` for `x, y ≥ 0`. -/
private lemma step3s_sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x ^ 2 + y) ≤ x + Real.sqrt y := by
  rw [Real.sqrt_le_left (by positivity)]
  have := Real.sq_sqrt hy
  nlinarith [Real.sqrt_nonneg y]

/-- `√(x + y) ≤ √x + √y` for `x, y ≥ 0`. -/
private lemma step3s_sqrt_add_le2 {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_left (by positivity)]
  have := Real.sq_sqrt hx
  have := Real.sq_sqrt hy
  nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y, mul_nonneg (Real.sqrt_nonneg x)
    (Real.sqrt_nonneg y)]

set_option maxHeartbeats 1000000 in
-- A long chain of elementary estimates.
/-- The moment bound after Grönwall at fixed `W`, simplified to `W^{3ε/8} R³ ζ_v²`. -/
private theorem step3s_num_final {Wr ω Rr Rv ζs ζv CR Sw ρA ρB ρI s v e₁ : ℝ} (p : ℕ)
    (hp : 1 ≤ p) (hW : 4 ≤ Wr) (hω1 : 1 ≤ ω) (hωW : ω ≤ Wr) (hR1 : 1 ≤ Rr) (hRv1 : 1 ≤ Rv)
    (hRvR : Rv ≤ Rr) (hζs0 : 0 ≤ ζs) (hζsv : ζs ≤ ζv) (hζv : (2 * Wr)⁻¹ ≤ ζv) (hCR : 1 ≤ CR)
    (hSw : 0 ≤ Sw) (_hsv : 0 ≤ v - s) (hvs : v - s ≤ 1)
    (hδlog : Sw * ω * Rr ^ 6 * ζv * Real.log Rr ≤ 1) (hlog : Real.log Rr ≤ ω)
    (hpW : 2 * (p : ℝ) ≤ Wr) (hρA0 : 0 ≤ ρA) (hρB0 : 0 ≤ ρB) (hρI0 : 0 ≤ ρI)
    (hρA : ρA ≤ Wr ^ (-12 : ℝ)) (hρB : ρB ≤ Wr ^ (-24 : ℝ)) (hρI : ρI ≤ Wr ^ (-12 : ℝ))
    (hK : Real.exp (CR * CR) * Real.exp 1 * (2 + Real.sqrt (8 * p * CR) + 2 * CR) ≤
      Wr ^ (e₁ / 8))
    (hω4 : ω ^ 4 ≤ Wr ^ (e₁ / 4)) :
    Real.exp (CR * CR * (v - s)) * Rv ^ (1 + Sw * ω * Rr ^ 6 * ζv) *
        (Real.sqrt ((ω * ζs ^ 2 + ρI) ^ 2 +
            (2 * p - 1) * ((4 * CR * ω ^ 5 * Rr ^ 4 * ζv ^ 4 + ρB) * Real.log Rv)) +
          (2 * CR * ω ^ 3 * Rr * ζv ^ 2 + ρA) * Real.log Rv) ≤
      Wr ^ (3 * e₁ / 8) * Rr ^ 3 * ζv ^ 2 := by
  have hW0 : 0 < Wr := by linarith
  have hW1 : 1 ≤ Wr := by linarith
  have hζv0 : 0 < ζv := lt_of_lt_of_le (by positivity) hζv
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  set δ := Sw * ω * Rr ^ 6 * ζv with hδ
  have hδ0 : 0 ≤ δ := by positivity
  set Lv := Real.log Rv with hLv
  have hLv0 : 0 ≤ Lv := Real.log_nonneg hRv1
  have hLvω : Lv ≤ ω := (Real.log_le_log (by linarith) hRvR).trans hlog
  -- the growth factor
  have hgrow : Rv ^ (1 + δ) ≤ Rr * Real.exp 1 := by
    have h1 : Rv ^ (1 + δ) ≤ Rr ^ (1 + δ) := Real.rpow_le_rpow (by linarith) hRvR (by positivity)
    have h2 : Rr ^ (1 + δ) = Rr * Rr ^ δ := by
      rw [Real.rpow_add (by linarith), Real.rpow_one]
    have h3 : Rr ^ δ ≤ Real.exp 1 := by
      rw [Real.rpow_def_of_pos (by linarith)]
      exact Real.exp_le_exp.mpr (by nlinarith)
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h3 (by linarith))
  have hexp : Real.exp (CR * CR * (v - s)) ≤ Real.exp (CR * CR) :=
    Real.exp_le_exp.mpr (by nlinarith)
  -- the remainders
  have hW12 : Wr ^ (-12 : ℝ) * Wr ≤ Wr ^ (-11 : ℝ) := by
    rw [show (-11 : ℝ) = -12 + 1 by norm_num, Real.rpow_add hW0, Real.rpow_one]
  have hW24 : Real.sqrt (Wr * Wr ^ (-24 : ℝ) * Wr) = Wr ^ (-11 : ℝ) := by
    have e : Wr * Wr ^ (-24 : ℝ) * Wr = Wr ^ (-11 : ℝ) * Wr ^ (-11 : ℝ) := by
      rw [← Real.rpow_add hW0]
      have e1 : Wr * Wr ^ (-24 : ℝ) * Wr = Wr ^ (1 : ℝ) * Wr ^ (-24 : ℝ) * Wr ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      rw [e1, ← Real.rpow_add hW0, ← Real.rpow_add hW0]
      norm_num
    rw [e, Real.sqrt_mul_self (by positivity)]
  have hW11 : 3 * Wr ^ (-11 : ℝ) ≤ ζv ^ 2 := by
    have h1 : (4 * Wr ^ 2)⁻¹ ≤ ζv ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hζv 2
      calc (4 * Wr ^ 2)⁻¹ = ((2 * Wr)⁻¹) ^ 2 := by ring
        _ ≤ _ := this
    refine le_trans ?_ h1
    rw [Real.rpow_neg hW0.le, show (11 : ℝ) = ((11 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
    have h9 : (4 : ℝ) ^ 9 ≤ Wr ^ 9 := pow_le_pow_left₀ (by norm_num) hW 9
    nlinarith [pow_pos hW0 2]
  have hrem : ρI + Real.sqrt (2 * p * ρB * ω) + ρA * ω ≤ ζv ^ 2 := by
    have h1 : Real.sqrt (2 * p * ρB * ω) ≤ Wr ^ (-11 : ℝ) := by
      rw [← hW24]
      refine Real.sqrt_le_sqrt ?_
      have := mul_le_mul hpW hρB (by positivity) hW0.le
      calc 2 * p * ρB * ω ≤ (2 * p * ρB) * Wr := by gcongr
        _ ≤ Wr * Wr ^ (-24 : ℝ) * Wr := by gcongr
    have h2 : ρA * ω ≤ Wr ^ (-11 : ℝ) :=
      (mul_le_mul hρA hωW (by linarith) (by positivity)).trans hW12
    have h3 : ρI ≤ Wr ^ (-11 : ℝ) := by
      refine hρI.trans (Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num))
    linarith
  -- the main terms
  set Z := ω ^ 4 * Rr ^ 2 * ζv ^ 2 with hZ
  have hω3 : ω ^ 3 ≤ ω ^ 4 := pow_le_pow_right₀ hω1 (by norm_num)
  have hR2 : Rr ≤ Rr ^ 2 := le_self_pow₀ hR1 (by norm_num)
  have hR21 : 1 ≤ Rr ^ 2 := one_le_pow₀ hR1
  have hω41 : 1 ≤ ω ^ 4 := one_le_pow₀ hω1
  have hζ2 : ζv ^ 2 ≤ Z := by
    rw [hZ]
    have : 1 ≤ ω ^ 4 * Rr ^ 2 := one_le_mul_of_one_le_of_one_le hω41 hR21
    nlinarith [sq_nonneg ζv]
  have hA1 : ω * ζs ^ 2 ≤ Z := by
    have h1 : ζs ^ 2 ≤ ζv ^ 2 := pow_le_pow_left₀ hζs0 hζsv 2
    have h2 : ω ≤ ω ^ 4 * Rr ^ 2 := by
      calc ω ≤ ω ^ 4 := le_self_pow₀ hω1 (by norm_num)
        _ = ω ^ 4 * 1 := (mul_one _).symm
        _ ≤ ω ^ 4 * Rr ^ 2 := by gcongr
    calc ω * ζs ^ 2 ≤ (ω ^ 4 * Rr ^ 2) * ζv ^ 2 := mul_le_mul h2 h1 (by positivity) (by positivity)
      _ = Z := rfl
  have hB1 : Real.sqrt ((2 * p - 1) * ((4 * CR * ω ^ 5 * Rr ^ 4 * ζv ^ 4 + ρB) * Lv)) ≤
      Real.sqrt (8 * p * CR) * Z + Real.sqrt (2 * p * ρB * ω) := by
    have h1 : (2 * p - 1) * ((4 * CR * ω ^ 5 * Rr ^ 4 * ζv ^ 4 + ρB) * Lv) ≤
        8 * p * CR * Z ^ 2 + 2 * p * ρB * ω := by
      have h2 : (2 * p - 1) * ((4 * CR * ω ^ 5 * Rr ^ 4 * ζv ^ 4 + ρB) * Lv) ≤
          (2 * p) * ((4 * CR * ω ^ 5 * Rr ^ 4 * ζv ^ 4 + ρB) * ω) := by
        gcongr
        · linarith
      have h3 : (2 * p) * ((4 * CR * ω ^ 5 * Rr ^ 4 * ζv ^ 4 + ρB) * ω) =
          8 * p * CR * (ω ^ 6 * Rr ^ 4 * ζv ^ 4) + 2 * p * ρB * ω := by ring
      have h4 : ω ^ 6 * Rr ^ 4 * ζv ^ 4 ≤ Z ^ 2 := by
        rw [hZ]
        have : ω ^ 6 ≤ ω ^ 8 := pow_le_pow_right₀ hω1 (by norm_num)
        have e : (ω ^ 4 * Rr ^ 2 * ζv ^ 2) ^ 2 = ω ^ 8 * Rr ^ 4 * ζv ^ 4 := by ring
        rw [e]; gcongr
      have h5 : 8 * p * CR * (ω ^ 6 * Rr ^ 4 * ζv ^ 4) ≤ 8 * p * CR * Z ^ 2 :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      linarith
    calc _ ≤ Real.sqrt (8 * p * CR * Z ^ 2 + 2 * p * ρB * ω) := Real.sqrt_le_sqrt h1
      _ ≤ Real.sqrt (8 * p * CR * Z ^ 2) + Real.sqrt (2 * p * ρB * ω) :=
          step3s_sqrt_add_le2 (by positivity) (by positivity)
      _ = _ := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hC1 : (2 * CR * ω ^ 3 * Rr * ζv ^ 2 + ρA) * Lv ≤ 2 * CR * Z + ρA * ω := by
    have h1 : (2 * CR * ω ^ 3 * Rr * ζv ^ 2 + ρA) * Lv ≤
        (2 * CR * ω ^ 3 * Rr * ζv ^ 2 + ρA) * ω :=
      mul_le_mul_of_nonneg_left hLvω (by positivity)
    have h2 : 2 * CR * ω ^ 3 * Rr * ζv ^ 2 * ω ≤ 2 * CR * Z := by
      rw [hZ]
      have e : 2 * CR * ω ^ 3 * Rr * ζv ^ 2 * ω = 2 * CR * (ω ^ 4 * Rr * ζv ^ 2) := by ring
      rw [e]
      gcongr
    calc (2 * CR * ω ^ 3 * Rr * ζv ^ 2 + ρA) * Lv ≤
        (2 * CR * ω ^ 3 * Rr * ζv ^ 2 + ρA) * ω := h1
      _ = 2 * CR * ω ^ 3 * Rr * ζv ^ 2 * ω + ρA * ω := by ring
      _ ≤ 2 * CR * Z + ρA * ω := by linarith [h2]
  have hinner : Real.sqrt ((ω * ζs ^ 2 + ρI) ^ 2 +
      (2 * p - 1) * ((4 * CR * ω ^ 5 * Rr ^ 4 * ζv ^ 4 + ρB) * Lv)) +
        (2 * CR * ω ^ 3 * Rr * ζv ^ 2 + ρA) * Lv ≤
      (2 + Real.sqrt (8 * p * CR) + 2 * CR) * Z := by
    have h0 : 0 ≤ (2 * p - 1) * ((4 * CR * ω ^ 5 * Rr ^ 4 * ζv ^ 4 + ρB) * Lv) := by
      have : (0 : ℝ) ≤ 2 * p - 1 := by linarith
      positivity
    have h1 := step3s_sqrt_add_le (by positivity : 0 ≤ ω * ζs ^ 2 + ρI) h0
    have e : (2 + Real.sqrt (8 * p * CR) + 2 * CR) * Z =
        2 * Z + Real.sqrt (8 * p * CR) * Z + 2 * CR * Z := by ring
    rw [e]
    linarith [hA1, hB1, hC1, hrem, hζ2]
  have hinner0 : 0 ≤ Real.sqrt ((ω * ζs ^ 2 + ρI) ^ 2 +
      (2 * p - 1) * ((4 * CR * ω ^ 5 * Rr ^ 4 * ζv ^ 4 + ρB) * Lv)) +
        (2 * CR * ω ^ 3 * Rr * ζv ^ 2 + ρA) * Lv := by positivity
  calc _ ≤ Real.exp (CR * CR) * (Rr * Real.exp 1) *
        ((2 + Real.sqrt (8 * p * CR) + 2 * CR) * Z) := by
        gcongr
    _ = (Real.exp (CR * CR) * Real.exp 1 * (2 + Real.sqrt (8 * p * CR) + 2 * CR)) *
        ω ^ 4 * (Rr ^ 3 * ζv ^ 2) := by rw [hZ]; ring
    _ ≤ Wr ^ (e₁ / 8) * Wr ^ (e₁ / 4) * (Rr ^ 3 * ζv ^ 2) := by gcongr
    _ = _ := by
        rw [← Real.rpow_add hW0]
        ring_nf

end Step3Num

/-! ### Markov's inequality at the sampled words -/

section Step3Conclude

/-- Markov's inequality in moment form: `ℙ(T < f) ≤ E f^q / T^q` for `f ≥ 0`, `T > 0`. -/
private theorem step3s_markov {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] (f : Ω' → ℝ) (hf0 : ∀ x, 0 ≤ f x) (q : ℕ)
    (hint : Integrable (fun x => f x ^ q) P) {T : ℝ} (hT : 0 < T) :
    P {x | T < f x} ≤ ENNReal.ofReal ((∫ x, f x ^ q ∂P) / T ^ q) := by
  have hTq : 0 < T ^ q := pow_pos hT q
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := P)
    (Eventually.of_forall fun x => pow_nonneg (hf0 x) q) hint (T ^ q)
  have hsub : {x | T < f x} ⊆ {x | T ^ q ≤ f x ^ q} := fun x hx =>
    pow_le_pow_left₀ hT.le (le_of_lt hx) q
  calc P {x | T < f x} ≤ P {x | T ^ q ≤ f x ^ q} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {x | T ^ q ≤ f x ^ q}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal ((∫ x, f x ^ q ∂P) / T ^ q) := by
        apply ENNReal.ofReal_le_ofReal
        rw [le_div_iff₀ hTq]
        linarith

/-- Markov's inequality at the sampled labels and the sampling inequality (5.34)
[fo:eq:weighted-sampling-input] with unit weights: if `‖X_l‖_{2p} ≤ B`, then the maximum over all
labels exceeds `T ≥ C_s T₀ + δ` with probability at most `η + |S| (B/T₀)^{2p}`. -/
private theorem step3s_sample_markov {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] {Λ : Type*} (X : Λ → Ω' → ℂ) (S₀ : Finset Λ)
    {Cs δ η B T₀ T : ℝ} (p : ℕ) (hp : 1 ≤ p) (hCs : 0 ≤ Cs) (_hB : 0 ≤ B) (hT₀ : 0 < T₀)
    (hsb : SampleBound P X (fun _ => 1) S₀ Cs δ η)
    (hint : ∀ l, Integrable (fun x => ‖X l x‖ ^ (2 * p)) P)
    (hmom : ∀ l, (∫ x, ‖X l x‖ ^ (2 * p) ∂P) ^ (1 / (2 * (p : ℝ))) ≤ B)
    (hsmall : Cs * T₀ + δ ≤ T) :
    P {x | ∃ l, T < ‖X l x‖} ≤
      ENNReal.ofReal η + (S₀.card : ENNReal) * ENNReal.ofReal ((B / T₀) ^ (2 * p)) := by
  set Bad := {x | ∃ l, Cs * (⨆ s : S₀, ‖X s x‖ / 1) + δ < ‖X l x‖ / 1} with hBad
  set E : Λ → Set Ω' := fun s => {x | T₀ < ‖X s x‖} with hE
  have hsub : {x | ∃ l, T < ‖X l x‖} ⊆ Bad ∪ ⋃ s ∈ S₀, E s := by
    rintro x ⟨l, hl⟩
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hcon
    obtain ⟨hnb, hns⟩ := hcon
    have hs : ∀ s ∈ S₀, ‖X s x‖ / 1 ≤ T₀ := by
      intro s hs
      have := hns s hs
      simp only [hE, Set.mem_ofPred_eq, not_lt] at this
      rw [div_one]; exact this
    have hsup : (⨆ s : S₀, ‖X s x‖ / 1) ≤ T₀ :=
      Real.iSup_le (fun s => hs s s.2) hT₀.le
    have hnb' : ‖X l x‖ / 1 ≤ Cs * (⨆ s : S₀, ‖X s x‖ / 1) + δ := by
      simp only [hBad, Set.mem_ofPred_eq, not_exists, not_lt] at hnb
      exact hnb l
    have : Cs * (⨆ s : S₀, ‖X s x‖ / 1) ≤ Cs * T₀ := mul_le_mul_of_nonneg_left hsup hCs
    rw [div_one] at hnb'
    linarith
  have hEs : ∀ s, P (E s) ≤ ENNReal.ofReal ((B / T₀) ^ (2 * p)) := by
    intro s
    have hm := step3s_markov P (fun x => ‖X s x‖) (fun x => norm_nonneg _) (2 * p) (hint s) hT₀
    refine hm.trans (ENNReal.ofReal_le_ofReal ?_)
    have hI0 : 0 ≤ ∫ x, ‖X s x‖ ^ (2 * p) ∂P := integral_nonneg fun x => by positivity
    have hI : ∫ x, ‖X s x‖ ^ (2 * p) ∂P ≤ B ^ (2 * p) := by
      have h1 := hmom s
      have h2 : ((∫ x, ‖X s x‖ ^ (2 * p) ∂P) ^ (1 / (2 * (p : ℝ)))) ^ ((2 * p : ℕ) : ℝ) =
          ∫ x, ‖X s x‖ ^ (2 * p) ∂P := by
        rw [← Real.rpow_mul hI0]
        have : 1 / (2 * (p : ℝ)) * ((2 * p : ℕ) : ℝ) = 1 := by
          push_cast; field_simp
        rw [this, Real.rpow_one]
      rw [← h2, Real.rpow_natCast]
      exact pow_le_pow_left₀ (by positivity) h1 _
    calc (∫ x, ‖X s x‖ ^ (2 * p) ∂P) / T₀ ^ (2 * p) ≤ B ^ (2 * p) / T₀ ^ (2 * p) := by gcongr
      _ = (B / T₀) ^ (2 * p) := by rw [div_pow]
  calc P {x | ∃ l, T < ‖X l x‖} ≤ P (Bad ∪ ⋃ s ∈ S₀, E s) := measure_mono hsub
    _ ≤ P Bad + ∑ s ∈ S₀, P (E s) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_biUnion_finset_le _ _))
    _ ≤ ENNReal.ofReal η + ∑ _s ∈ S₀, ENNReal.ofReal ((B / T₀) ^ (2 * p)) := by
        gcongr with s hs
        · exact hsb
        · exact hEs s
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- `2 W^{-(D+1)} ≤ W^{-D}` for `W ≥ 2`. -/
private theorem step3s_two (W : ℕ) (hW : 2 ≤ W) (D : ℝ) :
    ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) ≤
      ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hW2 : (2 : ℝ) ≤ W := by exact_mod_cast hW
  rw [← ENNReal.ofReal_add (Real.rpow_nonneg hW0.le _) (Real.rpow_nonneg hW0.le _)]
  apply ENNReal.ofReal_le_ofReal
  have e : (W : ℝ) ^ (-(D + 1)) = (W : ℝ) ^ (-D) * (W : ℝ)⁻¹ := by
    rw [show -(D + 1) = -D + (-1) by ring, Real.rpow_add hW0, Real.rpow_neg_one]
  have hpos : 0 < (W : ℝ) ^ (-D) := Real.rpow_pos_of_pos hW0 _
  have hinv : (W : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hW2
  rw [e]; nlinarith

/-- The final count: `|S| x^{2p} ≤ W^{-(D+1)}` from `x ≤ W^{-ε/8}`, `|S| ≤ W^{C}` and
`εp/4 ≥ D + C + 2`. -/
private theorem step3s_num_count {W : ℕ} (hW : 1 ≤ W) {n x ε C D : ℝ} (p : ℕ) (_hn0 : 0 ≤ n)
    (hn : n ≤ (W : ℝ) ^ C) (hx0 : 0 ≤ x) (hx : x ≤ (W : ℝ) ^ (-(ε / 8)))
    (hp : D + C + 2 ≤ ε * p / 4) :
    n * x ^ (2 * p) ≤ (W : ℝ) ^ (-(D + 1)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have h1 : x ^ (2 * p) ≤ (W : ℝ) ^ (-(ε / 8) * ((2 * p : ℕ) : ℝ)) := by
    rw [Real.rpow_mul hW0.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ hx0 hx _
  calc n * x ^ (2 * p) ≤ (W : ℝ) ^ C * (W : ℝ) ^ (-(ε / 8) * ((2 * p : ℕ) : ℝ)) :=
        mul_le_mul hn h1 (by positivity) (by positivity)
    _ = (W : ℝ) ^ (C + -(ε / 8) * ((2 * p : ℕ) : ℝ)) := (Real.rpow_add hW0 _ _).symm
    _ ≤ (W : ℝ) ^ (-(D + 1)) := by
        apply Real.rpow_le_rpow_of_exponent_le hW1
        push_cast
        nlinarith

/-- `C_s T₀ + W^{-4} ≤ T` for `T₀ = W^{ε/2} R³ ζ²`, `T = W^ε R^{7/2} ζ²`, `C_s + 1 ≤ W^{ε/2}`,
`R ≥ 1`, `ζ ≥ (2W)⁻¹`. -/
private theorem step3s_num_small {Wr Cs e Rr z : ℝ} (hW : 4 ≤ Wr) (_hCs : 0 ≤ Cs)
    (hCsW : Cs + 1 ≤ Wr ^ (e / 2)) (he : 0 ≤ e) (hR : 1 ≤ Rr) (hz : (2 * Wr)⁻¹ ≤ z) :
    Cs * (Wr ^ (e / 2) * Rr ^ 3 * z ^ 2) + Wr ^ (-(4 : ℝ)) ≤
      Wr ^ e * (Rr ^ ((7 : ℝ) / 2) * z ^ 2) := by
  have hW0 : 0 < Wr := by linarith
  have hW1 : 1 ≤ Wr := by linarith
  have hz0 : 0 < z := lt_of_lt_of_le (by positivity) hz
  have hz2 : (4 * Wr ^ 2)⁻¹ ≤ z ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hz 2
    calc (4 * Wr ^ 2)⁻¹ = ((2 * Wr)⁻¹) ^ 2 := by ring
      _ ≤ z ^ 2 := this
  have h4 : Wr ^ (-(4 : ℝ)) ≤ (4 * Wr ^ 2)⁻¹ := by
    have e4 : Wr ^ (4 : ℝ) = Wr ^ (4 : ℕ) := by norm_cast
    rw [Real.rpow_neg hW0.le, e4]
    apply inv_anti₀ (by positivity)
    have h16 : (16 : ℝ) ≤ Wr ^ 2 := by nlinarith
    have : Wr ^ 4 = Wr ^ 2 * Wr ^ 2 := by ring
    rw [this]
    have h2 : (0 : ℝ) ≤ Wr ^ 2 := by positivity
    nlinarith
  have hWe : 1 ≤ Wr ^ (e / 2) := Real.one_le_rpow hW1 (by linarith)
  have hR3 : 1 ≤ Rr ^ 3 := one_le_pow₀ hR
  have hR72 : Rr ^ 3 ≤ Rr ^ ((7 : ℝ) / 2) := by
    rw [show Rr ^ 3 = Rr ^ ((3 : ℕ) : ℝ) by rw [Real.rpow_natCast]]
    exact Real.rpow_le_rpow_of_exponent_le hR (by norm_num)
  have h5 : Wr ^ (-(4 : ℝ)) ≤ Wr ^ (e / 2) * Rr ^ 3 * z ^ 2 := by
    refine h4.trans (hz2.trans ?_)
    have : 1 ≤ Wr ^ (e / 2) * Rr ^ 3 := one_le_mul_of_one_le_of_one_le hWe hR3
    nlinarith [sq_nonneg z]
  have hsplit : Wr ^ e = Wr ^ (e / 2) * Wr ^ (e / 2) := by
    rw [← Real.rpow_add hW0]; ring_nf
  have h0 : 0 ≤ Wr ^ (e / 2) * Rr ^ 3 * z ^ 2 := by positivity
  calc Cs * (Wr ^ (e / 2) * Rr ^ 3 * z ^ 2) + Wr ^ (-(4 : ℝ))
      ≤ (Cs + 1) * (Wr ^ (e / 2) * Rr ^ 3 * z ^ 2) := by nlinarith
    _ ≤ Wr ^ (e / 2) * (Wr ^ (e / 2) * Rr ^ 3 * z ^ 2) := mul_le_mul_of_nonneg_right hCsW h0
    _ = Wr ^ e * (Rr ^ 3 * z ^ 2) := by rw [hsplit]; ring
    _ ≤ Wr ^ e * (Rr ^ ((7 : ℝ) / 2) * z ^ 2) := by gcongr

/-- `𝒦₂(a,b;-,-) = conj 𝒦₂(a,b;+,+)`, (5.13) [fo:eq:pairs]. -/
private theorem step3s_primLoop_ff (g : ℝ) (W L : ℕ) (E : ℝ) (m : ℂ) (t : ℝ) (a b : Fin L) :
    primLoop g W L E m t ![a, b] ![false, false] =
      star (primLoop g W L E m t ![a, b] ![true, true]) := by
  have e : ∀ σ : Bool, primLoop g W L E m t ![a, b] ![σ, σ] = (W : ℂ) ^ (1 - (2 : ℤ)) *
      (((gammaG g : ℝ) : ℂ)⁻¹ * pairK (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ σ a b) :=
    fun σ => rfl
  rw [e, e]
  simp only [pairK, ite_true, Bool.false_eq_true, ite_false, Matrix.map_apply, star_mul',
    star_inv₀, Complex.star_def, Complex.conj_ofReal, map_zpow₀, Complex.conj_natCast]

/-- `D₂(x,y;-,-) = conj D₂(y,x;+,+)`. -/
private theorem step3s_flowErr_mm (W : ℕ) (p : FlowPt) (x y : Fin p.L) (ω : Ω W p.L) :
    flowErr W p ![x, y] ![false, false] ω = star (flowErr W p ![y, x] ![true, true] ω) := by
  have hl := star_loopTr (flowG W p ω) ![y, x] ![true, true]
  have e1 : (![y, x] : Fin 2 → Fin p.L) ∘ Fin.rev = ![x, y] := by
    funext i; fin_cases i <;> rfl
  have e2 : (fun j : Fin 2 => !((![true, true] : Fin 2 → Bool) (finRotate 2 (Fin.rev j)))) =
      ![false, false] := by
    funext j; fin_cases j <;> rfl
  rw [e1, e2] at hl
  unfold flowErr
  rw [star_sub, hl, step3s_primLoop_ff, primLoop_two_swap p.g W p.L p.E _ p.u y x true true]

end Step3Conclude

/-! ### Thresholds in `W` -/

section Step3Large

/-- `C ≤ W^a` for all large `W`. -/
private theorem step3s_large_const (C : ℝ) {a : ℝ} (ha : 0 < a) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → C ≤ (W : ℝ) ^ a := by
  refine ⟨⌈(max C 1) ^ (1 / a)⌉₊ + 1, fun W hW => ?_⟩
  have hC1 : (1 : ℝ) ≤ max C 1 := le_max_right _ _
  have hb : (max C 1) ^ (1 / a) ≤ (W : ℝ) := by
    have := Nat.le_ceil ((max C 1) ^ (1 / a))
    have h2 : ((⌈(max C 1) ^ (1 / a)⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW
    push_cast at h2
    linarith
  have h0 : 0 ≤ (max C 1) ^ (1 / a) := by positivity
  calc C ≤ max C 1 := le_max_left _ _
    _ = ((max C 1) ^ (1 / a)) ^ a := by
        rw [← Real.rpow_mul (by linarith), one_div_mul_cancel ha.ne', Real.rpow_one]
    _ ≤ (W : ℝ) ^ a := Real.rpow_le_rpow h0 hb ha.le

/-- `K log W ≤ W^a` for all large `W`. -/
private theorem step3s_large_log (K : ℝ) {a : ℝ} (ha : 0 < a) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → K * Real.log W ≤ (W : ℝ) ^ a := by
  obtain ⟨W₁, hW₁⟩ := step3s_large_const (2 * |K| / a) (half_pos ha)
  refine ⟨max W₁ 1, fun W hW => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_of_max_le_right hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hlog0 : 0 ≤ Real.log W := Real.log_nonneg hW1
  have h1 : Real.log W ≤ (W : ℝ) ^ (a / 2) / (a / 2) := Real.log_le_rpow_div hW0.le (half_pos ha)
  have h2 := hW₁ W (le_of_max_le_left hW)
  have hpos : 0 < (W : ℝ) ^ (a / 2) := Real.rpow_pos_of_pos hW0 _
  calc K * Real.log W ≤ |K| * Real.log W := mul_le_mul_of_nonneg_right (le_abs_self K) hlog0
    _ ≤ |K| * ((W : ℝ) ^ (a / 2) / (a / 2)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg K)
    _ = (2 * |K| / a) * (W : ℝ) ^ (a / 2) := by field_simp
    _ ≤ (W : ℝ) ^ (a / 2) * (W : ℝ) ^ (a / 2) := mul_le_mul_of_nonneg_right h2 hpos.le
    _ = (W : ℝ) ^ a := by rw [← Real.rpow_add hW0]; ring_nf

/-- A crude moment bound is a power of `W`: if `0 ≤ A ≤ K₁ W^{e₁}`, `B ≤ C W^{e₂}` and the
constant `K₁^n 2^k (2^k + 9^k C)` is at most `W`, then
`A^n 2^{k-1}((W + 1)^k + 9^k B) ≤ W^{e₁ n + k + e₂ + 1}`. -/
private theorem step3s_num_crude {Wr A K₁ B C e₁ e₂ : ℝ} (n k : ℕ) (hk : 1 ≤ k) (hW : 1 ≤ Wr)
    (hA : 0 ≤ A) (hAK : A ≤ K₁ * Wr ^ e₁) (_hK₁ : 0 ≤ K₁) (hC : 0 ≤ C) (he₂ : 0 ≤ e₂)
    (hBC : B ≤ C * Wr ^ e₂) (hK : K₁ ^ n * 2 ^ k * (2 ^ k + 9 ^ k * C) ≤ Wr) :
    A ^ n * (2 ^ (k - 1) * ((Wr + 1) ^ k + 9 ^ k * B)) ≤ Wr ^ (e₁ * n + k + e₂ + 1) := by
  have hW0 : 0 < Wr := by linarith
  have h1 : A ^ n ≤ K₁ ^ n * Wr ^ (e₁ * n) := by
    rw [Real.rpow_mul hW0.le, Real.rpow_natCast, ← mul_pow]
    exact pow_le_pow_left₀ hA hAK n
  have hWk : (Wr + 1) ^ k ≤ 2 ^ k * Wr ^ ((k : ℝ) + e₂) := by
    rw [Real.rpow_add hW0, Real.rpow_natCast]
    have h2 : Wr + 1 ≤ 2 * Wr := by linarith
    have h3 : 1 ≤ Wr ^ e₂ := Real.one_le_rpow hW he₂
    calc (Wr + 1) ^ k ≤ (2 * Wr) ^ k := pow_le_pow_left₀ (by linarith) h2 k
      _ = 2 ^ k * Wr ^ k * 1 := by rw [mul_pow, mul_one]
      _ ≤ 2 ^ k * (Wr ^ k * Wr ^ e₂) := by
          rw [mul_assoc]; gcongr
  have hB : 9 ^ k * B ≤ 9 ^ k * C * Wr ^ ((k : ℝ) + e₂) := by
    rw [Real.rpow_add hW0, Real.rpow_natCast]
    have h3 : 1 ≤ Wr ^ k := one_le_pow₀ hW
    calc 9 ^ k * B ≤ 9 ^ k * (C * Wr ^ e₂) := by gcongr
      _ = 9 ^ k * C * (1 * Wr ^ e₂) := by ring
      _ ≤ 9 ^ k * C * (Wr ^ k * Wr ^ e₂) := by gcongr
  have h2k : (2 : ℝ) ^ (k - 1) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
  calc A ^ n * (2 ^ (k - 1) * ((Wr + 1) ^ k + 9 ^ k * B))
      ≤ A ^ n * (2 ^ k * ((2 ^ k + 9 ^ k * C) * Wr ^ ((k : ℝ) + e₂))) := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hA n)
        have h4 : (Wr + 1) ^ k + 9 ^ k * B ≤ (2 ^ k + 9 ^ k * C) * Wr ^ ((k : ℝ) + e₂) := by
          nlinarith
        have h5 : 0 ≤ (2 ^ k + 9 ^ k * C) * Wr ^ ((k : ℝ) + e₂) := by positivity
        rcases le_or_gt 0 ((Wr + 1) ^ k + 9 ^ k * B) with h6 | h6
        · exact mul_le_mul h2k h4 h6 (by positivity)
        · nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) (k - 1)]
    _ ≤ (K₁ ^ n * Wr ^ (e₁ * n)) * (2 ^ k * ((2 ^ k + 9 ^ k * C) * Wr ^ ((k : ℝ) + e₂))) := by
        gcongr
    _ = (K₁ ^ n * 2 ^ k * (2 ^ k + 9 ^ k * C)) * (Wr ^ (e₁ * n) * Wr ^ ((k : ℝ) + e₂)) := by
        ring
    _ ≤ Wr * (Wr ^ (e₁ * n) * Wr ^ ((k : ℝ) + e₂)) := by gcongr
    _ = Wr ^ (e₁ * n + k + e₂ + 1) := by
        rw [show e₁ * n + k + e₂ + 1 = e₁ * n + ((k : ℝ) + e₂) + 1 by ring,
          Real.rpow_add hW0 (e₁ * n + ((k : ℝ) + e₂)) 1,
          Real.rpow_add hW0 (e₁ * n) ((k : ℝ) + e₂), Real.rpow_one]
        ring

/-- The off-event remainders: with `M = W^E`, `δ = 4 W^{-D'}`, `D' = E + 2 + 48p`,
`(√M √δ)^{1/(2p)} ≤ W^{-12}` and `(√M √δ)^{1/p} ≤ W^{-24}`. -/
private theorem step3s_num_rho {Wr E : ℝ} (p : ℕ) (hp : 1 ≤ p) (hW : 2 ≤ Wr) :
    (Real.sqrt (Wr ^ E) * Real.sqrt (4 * Wr ^ (-(E + 2 + 48 * p)))) ^ (1 / (2 * (p : ℝ))) ≤
        Wr ^ (-12 : ℝ) ∧
      (Real.sqrt (Wr ^ E) * Real.sqrt (4 * Wr ^ (-(E + 2 + 48 * p)))) ^ (1 / (p : ℝ)) ≤
        Wr ^ (-24 : ℝ) := by
  have hW0 : 0 < Wr := by linarith
  have hW1 : 1 ≤ Wr := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have e : Real.sqrt (Wr ^ E) * Real.sqrt (4 * Wr ^ (-(E + 2 + 48 * p))) =
      2 * Wr ^ (-(1 + 24 * p : ℝ)) := by
    rw [← Real.sqrt_mul (by positivity), show Wr ^ E * (4 * Wr ^ (-(E + 2 + 48 * p))) =
      (2 * Wr ^ (-(1 + 24 * p : ℝ))) ^ 2 by
        rw [mul_pow, ← Real.rpow_natCast (Wr ^ _), ← Real.rpow_mul hW0.le,
          mul_comm (Wr ^ E), mul_assoc, ← Real.rpow_add hW0]
        norm_num
        ring_nf]
    exact Real.sqrt_sq (by positivity)
  have h2 : 2 * Wr ^ (-(1 + 24 * p : ℝ)) ≤ Wr ^ (-(24 * p : ℝ)) := by
    rw [show -(1 + 24 * p : ℝ) = -1 + -(24 * p) by ring, Real.rpow_add hW0, Real.rpow_neg_one]
    have : 0 < Wr ^ (-(24 * p : ℝ)) := Real.rpow_pos_of_pos hW0 _
    have h3 : 2 * Wr⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hW0]; exact hW
    nlinarith
  rw [e]
  have h0 : 0 ≤ 2 * Wr ^ (-(1 + 24 * p : ℝ)) := by positivity
  constructor
  · calc (2 * Wr ^ (-(1 + 24 * p : ℝ))) ^ (1 / (2 * (p : ℝ))) ≤
        (Wr ^ (-(24 * p : ℝ))) ^ (1 / (2 * (p : ℝ))) := Real.rpow_le_rpow h0 h2 (by positivity)
      _ = Wr ^ (-12 : ℝ) := by
          rw [← Real.rpow_mul hW0.le]; congr 1; field_simp; ring
  · calc (2 * Wr ^ (-(1 + 24 * p : ℝ))) ^ (1 / (p : ℝ)) ≤
        (Wr ^ (-(24 * p : ℝ))) ^ (1 / (p : ℝ)) := Real.rpow_le_rpow h0 h2 (by positivity)
      _ = Wr ^ (-24 : ℝ) := by
          rw [← Real.rpow_mul hW0.le]; congr 1; field_simp

/-- Cyclic distance is symmetric. -/
private lemma step3s_cycDist_comm {L : ℕ} (a b : Fin L) : cycDist a b = cycDist b a := by
  unfold cycDist; exact min_comm _ _

/-- `‖a - a‖_L = 0`. -/
private lemma step3s_cycDist_self {L : ℕ} (a : Fin L) : cycDist a a = 0 := by
  unfold cycDist; simp

/-- On the characteristic, the resolvent of a pair `(p, η_u)` is the resolvent of the flow. -/
private theorem step3s_segG_eta (W : ℕ) (p : FlowPt) (ω : Ω W p.L) :
    segG W (p, etaChar p.g (mRoot p.g p.L p.E) p.u) ω = flowG W p ω := by
  unfold segG flowG
  congr 1
  apply Complex.ext
  · simp
  · simp [zChar, etaChar]

/-- A sampling bound with a constant `C_s` holds with any larger constant. -/
private theorem step3s_sb_mono {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') {Λ : Type*}
    (X : Λ → Ω' → ℂ) (S₀ : Finset Λ) {C C' δ η : ℝ} (hCC : C ≤ C')
    (h : SampleBound P X (fun _ => 1) S₀ C δ η) : SampleBound P X (fun _ => 1) S₀ C' δ η := by
  refine le_trans (measure_mono ?_) h
  rintro x ⟨l, hl⟩
  refine ⟨l, lt_of_le_of_lt ?_ hl⟩
  have h0 : 0 ≤ ⨆ s : S₀, ‖X s x‖ / 1 := Real.iSup_nonneg fun s => by positivity
  have := mul_le_mul_of_nonneg_right hCC h0
  linarith

end Step3Large

/-! ### Step 3, the same-sign pair -/

section Step3Main

open scoped Matrix.Norms.L2Operator

set_option maxHeartbeats 8000000 in
-- The thresholds in `W` and the instantiation of the fixed-`W` estimate are long.
/-- The same-sign pair estimate of Step 3: the fixed-`W` moment bound, Markov's inequality at the
sampled words and the sampling inequality (5.34) [fo:eq:weighted-sampling-input]. -/
private theorem step3s_main (R : PropRegime) (I : PropInputs R.base R.J) (c cp θ N cp₂ : ℝ)
    (hc : 0 < c) (hcp₂ : 0 < cp₂) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2) (hN : lemmaNN0 I.Cw ≤ N)
    (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q})
    (hSu : ∀ W, ∀ q ∈ S W, ∀ v : ℝ, q.s ≤ v → v ≤ q.u →
      (⟨q.g, q.E, q.L, q.s, q.t, v⟩ : StepPt) ∈ S W)
    (hin : OneStepInput cp θ (fun q : StepPt => q.at q.s) S) (h1 : Step1Out S)
    (h2 : Step2Out cp₂ θ S) :
    PrecMax StepPt.L S (Λ := fun _ q => Fin q.L × Fin q.L × Bool)
      (fun W q x ω => flowErr W (q.at q.u) ![x.1, x.2.1] ![x.2.2, x.2.2] ω)
      (fun W q _ => q.ratio ^ ((7 : ℝ) / 2) * zetaProp q.g W q.L q.u ^ 2) := by
  intro ε D hε hD
  -- the losses and the constants fixed before `W`
  set ε₁ := min ε 1 with hε₁def
  have hε₁0 : 0 < ε₁ := lt_min hε one_pos
  have hε₁ε : ε₁ ≤ ε := min_le_left _ _
  have hε₁1 : ε₁ ≤ 1 := min_le_right _ _
  set a := min (ε₁ / 16) (c / 4) with hadef
  have ha0 : 0 < a := lt_min (by positivity) (by positivity)
  have ha16 : a ≤ ε₁ / 16 := min_le_left _ _
  have hac : a ≤ c / 4 := min_le_right _ _
  have ha1 : a ≤ 1 := by linarith
  have hN20 : (20 : ℝ) ≤ N := le_trans (le_max_left _ _) hN
  set CR := R.C with hCRdef
  have hRC : 1 ≤ CR := R.one_le_C
  have hCR0 : 0 < CR := by linarith
  set F₁ := 2 * CR + 2 with hF₁def
  have hF₁ : 0 < F₁ := by positivity
  obtain ⟨Cc, hCc0, hconvAll⟩ := weight_convolution cp₂ θ F₁ hcp₂ hθ hθ2 hF₁
  set Sw := Real.sqrt 2 * Cc with hSwdef
  have hSw : 0 ≤ Sw := by positivity
  obtain ⟨Wdy, hdy⟩ := R.dyson
  obtain ⟨Wbud, hbud⟩ := R.budget
  obtain ⟨Wpr, hpr⟩ := R.prim 2 1 one_pos
  obtain ⟨CS, Cs, Wsm, hsm⟩ := I.sampling.1 2 (by norm_num) cp₂ θ F₁ hcp₂ hθ hθ2 hF₁ 4 (D + 2)
    (by norm_num) (by linarith)
  set CS' := max CS 0 with hCS'
  set Cs' := max Cs 0 with hCs'
  have hCs'0 : 0 ≤ Cs' := le_max_right _ _
  -- the moment order
  set p : ℕ := ⌈4 * (D + CS' + 3) / ε₁⌉₊ + 1 with hpdef
  have hp : 1 ≤ p := by omega
  have hpε : D + 1 + CS' + 2 ≤ ε₁ * p / 4 := by
    have h1 := Nat.le_ceil (4 * (D + CS' + 3) / ε₁)
    have h2 : 4 * (D + CS' + 3) / ε₁ ≤ p := by simp only [hpdef]; push_cast; linarith
    rw [div_le_iff₀ hε₁0] at h2
    linarith
  -- the crude moments
  obtain ⟨C₀, hcrude⟩ := I.crude
  obtain ⟨C16, Wc16, hc16⟩ := hcrude (4 * (2 * (2 * p))) (by omega)
  obtain ⟨C12, Wc12, hc12⟩ := hcrude (6 * (2 * p)) (by omega)
  obtain ⟨C8, Wc8, hc8⟩ := hcrude (2 * (2 * (2 * p))) (by omega)
  set C₀' := max C₀ 0 with hC₀'
  have hC₀'0 : 0 ≤ C₀' := le_max_right _ _
  set Ccr := max (max C16 C12) (max C8 0) with hCcr
  have hCcr0 : 0 ≤ Ccr := le_trans (le_max_right _ _) (le_max_right _ _)
  set EE : ℝ := (CR + 1) * ((2 * (2 * p) : ℕ) : ℝ) + (1 + C₀') * ((4 * (2 * (2 * p)) : ℕ) : ℝ) + 1
    with hEE
  have hEE0 : 0 ≤ EE := by positivity
  set D' : ℝ := EE + 2 + 48 * p with hD'
  have hD'0 : 0 < D' := by positivity
  -- the good events
  obtain ⟨Wop, hopW⟩ := h1.op a D' ha0 hD'0
  obtain ⟨Wden, hdenW⟩ := h1.density a D' ha0 hD'0
  obtain ⟨Wavg, havgW⟩ := h2.avg a D' ha0 hD'0
  obtain ⟨Wpair, hpairW⟩ := h2.pair F₁ hF₁ a D' ha0 hD'0
  obtain ⟨Win, hinW⟩ := hin.err 2 (by norm_num) a D' ha0 hD'0
  -- thresholds
  obtain ⟨Wl1, hl1⟩ := step3s_large_log (3 * Sw) (by positivity : (0 : ℝ) < 3 * c / 4)
  obtain ⟨Wl2, hl2⟩ := step3s_large_log 3 ha0
  set KK := Real.exp (CR * CR) * Real.exp 1 * (2 + Real.sqrt (8 * p * CR) + 2 * CR) with hKK
  obtain ⟨WK, hWK⟩ := step3s_large_const KK (by positivity : (0 : ℝ) < ε₁ / 8)
  obtain ⟨WCs, hWCs⟩ := step3s_large_const (Cs' + 1) (by positivity : (0 : ℝ) < ε₁ / 2)
  set KA := (6 + 2 * CR) ^ (2 * (2 * p)) * 2 ^ (4 * (2 * (2 * p))) *
    (2 ^ (4 * (2 * (2 * p))) + 9 ^ (4 * (2 * (2 * p))) * Ccr) with hKA
  set KB := (4 : ℝ) ^ (2 * p) * 2 ^ (6 * (2 * p)) * (2 ^ (6 * (2 * p)) + 9 ^ (6 * (2 * p)) * Ccr)
    with hKB
  set KI := (2 : ℝ) ^ (2 * (2 * p)) * 2 ^ (2 * (2 * (2 * p))) *
    (2 ^ (2 * (2 * (2 * p))) + 9 ^ (2 * (2 * (2 * p))) * Ccr) with hKI
  have hKA0 : 0 ≤ KA := by positivity
  have hKB0 : 0 ≤ KB := by positivity
  have hKI0 : 0 ≤ KI := by positivity
  obtain ⟨Wcr, hWcr⟩ := step3s_large_const (KA + KB + KI) one_pos
  refine ⟨max (max (max 4 (2 * p)) (max Wl1 (max Wl2 (max WK (max WCs Wcr)))))
    (max (max Wdy (max Wbud (max Wpr Wsm))) (max (max Wc16 (max Wc12 Wc8))
      (max Wop (max Wden (max Wavg (max Wpair Win)))))), fun W hW q hq => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hW4, hW2p⟩, hWl1, hWl2, hWK', hWCs', hWcr'⟩, ⟨hWdy, hWbud, hWpr, hWsm⟩,
    ⟨hWc16, hWc12, hWc8⟩, hWop, hWden, hWavg, hWpair, hWin⟩ := hW
  -- the step point
  have hadmq := hS W hq
  rcases q with ⟨g, E, L, s, t, v⟩
  obtain ⟨⟨d, hdJ, hreach⟩, hs, hsv, hvt, hst, ht3, hRN⟩ := hadmq
  change 1 / 2 ≤ s at hs
  change s ≤ v at hsv
  change v ≤ t at hvt
  change s < t at hst
  change (W : ℝ) ^ (-3 : ℝ) ≤ 1 - t at ht3
  change ((1 - s) / (1 - t)) ^ N * zetaProp g W L t ≤ (W : ℝ) ^ (-c) at hRN
  change CmpReach R.base W d ⟨g, E, L, t⟩ at hreach
  have hW1 : 1 ≤ W := by omega
  have hW2 : 2 ≤ W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW4r : (4 : ℝ) ≤ W := by exact_mod_cast hW4
  have ht1 : t < 1 := by
    have : 0 < (W : ℝ) ^ (-3 : ℝ) := Real.rpow_pos_of_pos hW0 _
    linarith
  have hv1 : v < 1 := lt_of_le_of_lt hvt ht1
  have hs0 : 0 ≤ s := by linarith
  have hv0 : 0 ≤ v := hs0.trans hsv
  have hreachu : ∀ u : ℝ, 1 / 2 ≤ u → u ≤ t → CmpReach R.base W d ⟨g, E, L, u⟩ :=
    fun u hu1 hu2 => CmpReach.earlier u hreach hu1 hu2
  obtain ⟨hL, hg, hroot, hIm1, -, hMab, hrow1, hrow2⟩ := hdy W hWdy d ⟨g, E, L, t⟩ hdJ.le hreach
  change 3 ≤ L at hL
  change 0 ≤ g at hg
  have hL1 : 1 ≤ L := by omega
  have hmC : ‖mRoot g L E‖ ≤ CR := step3s_norm_m_le g E L hL1 _ hroot hMab
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  set Rr := (1 - s) / (1 - t) with hRrdef
  have h1t : 0 < 1 - t := by linarith
  have hR1 : 1 ≤ Rr := by rw [hRrdef, le_div_iff₀ h1t]; linarith
  have hR3 : Rr ≤ (W : ℝ) ^ 3 := by
    have hW3' : (W : ℝ) ^ (-3 : ℝ) = ((W : ℝ) ^ 3)⁻¹ := by
      rw [Real.rpow_neg hW0.le]; norm_cast
    rw [hW3'] at ht3
    rw [hRrdef, div_le_iff₀ h1t]
    have h1 : 1 ≤ (W : ℝ) ^ 3 * (1 - t) := by
      have := mul_le_mul_of_nonneg_left ht3 (by positivity : (0 : ℝ) ≤ (W : ℝ) ^ 3)
      rwa [mul_inv_cancel₀ (by positivity)] at this
    linarith
  -- scales
  have hsc : ∀ r ∈ Set.Icc s t, 1 ≤ ellProp g L r ∧ ellProp g L r ≤ L ∧
      (2 * (W : ℝ))⁻¹ ≤ zetaProp g W L r ∧ zetaProp g W L r ≤ zetaProp g W L t := by
    intro r hr
    obtain ⟨hℓ1, -, hℓL, hζ2, -, -, -⟩ :=
      scale_facts g hg W L hW1 hL1 r r (hs0.trans hr.1) le_rfl (lt_of_le_of_lt hr.2 ht1)
    exact ⟨hℓ1, hℓL, hζ2,
      (scale_facts g hg W L hW1 hL1 r t (hs0.trans hr.1) hr.2 ht1).2.2.2.2.1⟩
  have hζt0 : 0 ≤ zetaProp g W L t := le_trans (by positivity) (hsc t ⟨hst.le, le_rfl⟩).2.2.1
  have hRN1 : Rr ^ N * zetaProp g W L t ≤ 1 :=
    hRN.trans (Real.rpow_le_one_of_one_le_of_nonpos hW1r (by linarith))
  have hζt1 : zetaProp g W L t ≤ 1 := by
    have h1 : 1 ≤ Rr ^ N := Real.one_le_rpow hR1 (by linarith)
    nlinarith
  have hζv : zetaProp g W L v ≤ zetaProp g W L t := (hsc v ⟨hsv, hvt⟩).2.2.2
  have hR6 : Rr ^ 6 * zetaProp g W L v ≤ (W : ℝ) ^ (-c) := by
    have h6 : Rr ^ 6 ≤ Rr ^ N := by
      rw [show Rr ^ 6 = Rr ^ ((6 : ℕ) : ℝ) by rw [Real.rpow_natCast]]
      exact Real.rpow_le_rpow_of_exponent_le hR1 (by push_cast; linarith)
    calc Rr ^ 6 * zetaProp g W L v ≤ Rr ^ N * zetaProp g W L t :=
          mul_le_mul h6 hζv (le_trans (by positivity) (hsc v ⟨hsv, hvt⟩).2.2.1)
            (by positivity)
      _ ≤ _ := hRN
  set ω := (W : ℝ) ^ a with hωdef
  have hω1 : 1 ≤ ω := Real.one_le_rpow hW1r ha0.le
  have hωW : ω ≤ W := by
    calc ω = (W : ℝ) ^ a := rfl
      _ ≤ (W : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hW1r ha1
      _ = W := Real.rpow_one _
  have hlogR : Real.log Rr ≤ 3 * Real.log W := by
    calc Real.log Rr ≤ Real.log ((W : ℝ) ^ 3) := Real.log_le_log (by linarith) hR3
      _ = 3 * Real.log W := by rw [Real.log_pow]; norm_num
  have hlog : Real.log Rr ≤ ω := hlogR.trans (hl2 W hWl2)
  have hδlog : Sw * ω * Rr ^ 6 * zetaProp g W L v * Real.log Rr ≤ 1 := by
    have hlR0 : 0 ≤ Real.log Rr := Real.log_nonneg hR1
    have hωc : ω * (W : ℝ) ^ (-c) ≤ (W : ℝ) ^ (-(3 * c / 4)) := by
      rw [hωdef, ← Real.rpow_add hW0]
      exact Real.rpow_le_rpow_of_exponent_le hW1r (by linarith)
    have hl := hl1 W hWl1
    have hpos : 0 < (W : ℝ) ^ (3 * c / 4) := Real.rpow_pos_of_pos hW0 _
    have hinv : (W : ℝ) ^ (-(3 * c / 4)) * (W : ℝ) ^ (3 * c / 4) = 1 := by
      rw [← Real.rpow_add hW0]; simp
    calc Sw * ω * Rr ^ 6 * zetaProp g W L v * Real.log Rr =
        Sw * (ω * (Rr ^ 6 * zetaProp g W L v)) * Real.log Rr := by ring
      _ ≤ Sw * (ω * (W : ℝ) ^ (-c)) * (3 * Real.log W) := by gcongr
      _ ≤ Sw * (W : ℝ) ^ (-(3 * c / 4)) * (3 * Real.log W) := by gcongr
      _ = (W : ℝ) ^ (-(3 * c / 4)) * (3 * Sw * Real.log W) := by ring
      _ ≤ (W : ℝ) ^ (-(3 * c / 4)) * (W : ℝ) ^ (3 * c / 4) := by gcongr
      _ = 1 := hinv
  -- the weights
  set w : ℝ → Fin L → Fin L → ℝ := fun r x y =>
    weightFn cp₂ θ F₁ W (ellProp g L r) (cycDist x y) with hwdef
  have hw0 : ∀ r x y, 0 ≤ w r x y := fun r x y => by
    simp only [hwdef, weightFn]; positivity
  have hγL : gammaG g * L ≤ (W : ℝ) ^ CR := by
    have hb := hbud W hWbud d ⟨g, E, L, t⟩ hdJ.le hreach
    change gammaG g * L + L / ellProp g L t ≤ (W : ℝ) ^ CR at hb
    have : 0 ≤ (L : ℝ) / ellProp g L t := by
      have := (hsc t ⟨hst.le, le_rfl⟩).1
      positivity
    linarith
  have hwrow : ∀ r ∈ Set.Icc s v, ∀ x, ∑ y, w r y x ≤ Sw * ellProp g L r ∧
      ∑ y, w r x y ≤ Sw * ellProp g L r := by
    intro r hr x
    have hrt : r ∈ Set.Icc s t := ⟨hr.1, hr.2.trans hvt⟩
    obtain ⟨hℓ1, hℓL, -, -⟩ := hsc r hrt
    have hℓ0 : 0 < ellProp g L r := by linarith
    have hLW : (L : ℝ) * (W : ℝ) ^ (-(F₁ / 2)) ≤ ellProp g L r := by
      have hb := hbud W hWbud d ⟨g, E, L, r⟩ hdJ.le (hreachu r (by linarith [hr.1]) hrt.2)
      change gammaG g * L + L / ellProp g L r ≤ (W : ℝ) ^ CR at hb
      have h1 : (L : ℝ) / ellProp g L r ≤ (W : ℝ) ^ CR := by
        have : 0 ≤ gammaG g * L := by positivity
        linarith
      rw [div_le_iff₀ hℓ0] at h1
      have h2 : (W : ℝ) ^ CR * (W : ℝ) ^ (-(F₁ / 2)) ≤ 1 := by
        rw [← Real.rpow_add hW0]
        exact Real.rpow_le_one_of_one_le_of_nonpos hW1r (by rw [hF₁def]; linarith)
      calc (L : ℝ) * (W : ℝ) ^ (-(F₁ / 2)) ≤ (W : ℝ) ^ CR * ellProp g L r *
            (W : ℝ) ^ (-(F₁ / 2)) := by gcongr
        _ = ((W : ℝ) ^ CR * (W : ℝ) ^ (-(F₁ / 2))) * ellProp g L r := by ring
        _ ≤ 1 * ellProp g L r := by gcongr
        _ = _ := one_mul _
    have hconv := (hconvAll W L hW1 hL1 (ellProp g L r) hℓ1 hℓL hLW x x).2
    have hsym : ∀ y, w r y x = w r x y := fun y => by
      simp only [hwdef, step3s_cycDist_comm y x]
    have hsq : ∀ y, Real.sqrt (weightFn cp₂ θ F₁ W (ellProp g L r) (cycDist x y) *
        weightFn cp₂ θ F₁ W (ellProp g L r) (cycDist y x)) = w r x y := fun y => by
      rw [step3s_cycDist_comm y x, Real.sqrt_mul_self (hw0 r x y)]
    simp only [hsq] at hconv
    have hxx : Real.sqrt (weightFn cp₂ θ F₁ W (ellProp g L r) (cycDist x x)) ≤ Real.sqrt 2 := by
      refine Real.sqrt_le_sqrt ?_
      simp only [weightFn, step3s_cycDist_self, Nat.cast_zero, zero_div,
        Real.zero_rpow hθ.ne', mul_zero, neg_zero, Real.exp_zero]
      have : (W : ℝ) ^ (-F₁) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1r (by linarith)
      linarith
    have h1 : ∑ y, w r x y ≤ Sw * ellProp g L r := by
      refine hconv.trans ?_
      rw [hSwdef]
      calc Cc * ellProp g L r * Real.sqrt (weightFn cp₂ θ F₁ W (ellProp g L r) (cycDist x x))
          ≤ Cc * ellProp g L r * Real.sqrt 2 := by gcongr
        _ = _ := by ring
    refine ⟨?_, h1⟩
    rw [Finset.sum_congr rfl fun y _ => hsym y]
    exact h1
  -- the primitive same-sign pairs
  have hK : ∀ r ∈ Set.Icc s v, ∀ x y : Fin L,
      ‖primLoop g W L E (mRoot g L E) r ![x, y] ![true, true]‖ ≤ W := by
    intro r hr x y
    have hrt : r ∈ Set.Icc s t := ⟨hr.1, hr.2.trans hvt⟩
    have h := hpr W hWpr d ⟨g, E, L, r⟩ hdJ.le (hreachu r (by linarith [hr.1]) hrt.2) 2 le_rfl
      le_rfl ![x, y] ![true, true]
    refine h.trans ?_
    rw [Real.rpow_one, pow_one]
    have hζr : zetaProp g W L r ≤ 1 := (hsc r hrt).2.2.2.trans hζt1
    calc (W : ℝ) * zetaProp g W L r ≤ W * 1 := by gcongr
      _ = W := mul_one _
  -- the intermediate step points and the bad events
  have hqr : ∀ r ∈ Set.Icc s v, (⟨g, E, L, s, t, r⟩ : StepPt) ∈ S W := fun r hr =>
    hSu W _ hq r hr.1 hr.2
  set B1 : ℝ → Set (Ω W L) := fun r => {x | ∃ l : Fin L × Fin L,
    (W : ℝ) ^ a * (W * Rr * zetaProp g W L r) <
      ‖((‖blockOf (flowG W ⟨g, E, L, r⟩ x) l.1 l.2‖ : ℝ) : ℂ)‖} with hB1
  set B2 : ℝ → Set (Ω W L) := fun r => {x | ∃ l : Fin L,
    (W : ℝ) ^ a * 1 < ‖(((blockTr (flowG W ⟨g, E, L, r⟩ x) l l).im : ℝ) : ℂ)‖} with hB2
  set B3 : ℝ → Set (Ω W L) := fun r => {x | ∃ l : Fin L × Fin L,
    (W : ℝ) ^ a * zetaProp g W L r <
      ‖blockTr (flowG W ⟨g, E, L, r⟩ x - flowM W ⟨g, E, L, r⟩) l.1 l.2‖} with hB3
  set B4 : ℝ → Set (Ω W L) := fun r => {x | ∃ l : Fin L × Fin L,
    (W : ℝ) ^ a * (Rr ^ 6 * zetaProp g W L r ^ 2 *
      weightFn cp₂ θ F₁ W (ellProp g L r) (cycDist l.1 l.2)) <
      ‖flowErr W ⟨g, E, L, r⟩ ![l.1, l.2] ![true, false] x‖} with hB4
  set Bad : ℝ → Set (Ω W L) := fun r => B1 r ∪ B2 r ∪ B3 r ∪ B4 r with hBad
  set δ := 4 * (W : ℝ) ^ (-D') with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  have hBadμ : ∀ r ∈ Set.Ioo s v, μ W L (Bad r) ≤ ENNReal.ofReal δ := by
    intro r hr
    have hrI : r ∈ Set.Icc s v := ⟨hr.1.le, hr.2.le⟩
    have e1 : μ W L (B1 r) ≤ ENNReal.ofReal ((W : ℝ) ^ (-D')) := hopW W hWop _ (hqr r hrI)
    have e2 : μ W L (B2 r) ≤ ENNReal.ofReal ((W : ℝ) ^ (-D')) := hdenW W hWden _ (hqr r hrI)
    have e3 : μ W L (B3 r) ≤ ENNReal.ofReal ((W : ℝ) ^ (-D')) := havgW W hWavg _ (hqr r hrI)
    have e4 : μ W L (B4 r) ≤ ENNReal.ofReal ((W : ℝ) ^ (-D')) := hpairW W hWpair _ (hqr r hrI)
    have hx0 : 0 ≤ (W : ℝ) ^ (-D') := by positivity
    calc μ W L (Bad r) ≤ μ W L (B1 r) + μ W L (B2 r) + μ W L (B3 r) + μ W L (B4 r) := by
          refine (measure_union_le _ _).trans ?_
          gcongr
          refine (measure_union_le _ _).trans ?_
          gcongr
          exact measure_union_le _ _
      _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-D')) + ENNReal.ofReal ((W : ℝ) ^ (-D')) +
          ENNReal.ofReal ((W : ℝ) ^ (-D')) + ENNReal.ofReal ((W : ℝ) ^ (-D')) := by
          gcongr
      _ = ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_add hx0 hx0, ← ENNReal.ofReal_add (by positivity) hx0,
            ← ENNReal.ofReal_add (by positivity) hx0, hδdef]
          congr 1; ring
  have hgood : ∀ r ∈ Set.Ioo s v, ∀ x, x ∉ Bad r →
      (∀ y z, ‖blockOf (flowG W ⟨g, E, L, r⟩ x) y z‖ ≤ ω * (W * Rr * zetaProp g W L r)) ∧
      (∀ y, (blockTr (flowG W ⟨g, E, L, r⟩ x) y y).im ≤ ω * 1) ∧
      (∀ c, ‖blockTr (flowG W ⟨g, E, L, r⟩ x - flowM W ⟨g, E, L, r⟩) c c‖ ≤
        ω * zetaProp g W L r) ∧
      (∀ y z, ‖flowErr W ⟨g, E, L, r⟩ ![y, z] ![true, false] x‖ ≤
        ω * (Rr ^ 6 * zetaProp g W L r ^ 2 * w r y z)) := by
    intro r hr x hx
    simp only [hBad, Set.mem_union, not_or] at hx
    obtain ⟨⟨⟨hx1, hx2⟩, hx3⟩, hx4⟩ := hx
    refine ⟨fun y z => ?_, fun y => ?_, fun c' => ?_, fun y z => ?_⟩
    · have := not_lt.mp (fun h => hx1 ⟨(y, z), h⟩)
      rwa [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)] at this
    · have := not_lt.mp (fun h => hx2 ⟨y, h⟩)
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      exact (le_abs_self _).trans this
    · exact not_lt.mp (fun h => hx3 ⟨(c', c'), h⟩)
    · exact not_lt.mp (fun h => hx4 ⟨(y, z), h⟩)
  set Bad0 : Set (Ω W L) := {x | ∃ l : Word 2 L,
    (W : ℝ) ^ a * zetaProp g W L s ^ 2 < ‖flowErr W ⟨g, E, L, s⟩ l.1 l.2 x‖} with hBad0
  have hBad0μ : μ W L Bad0 ≤ ENNReal.ofReal δ := by
    refine le_trans (hinW W hWin _ hq) (ENNReal.ofReal_le_ofReal ?_)
    have : (0 : ℝ) ≤ (W : ℝ) ^ (-D') := by positivity
    rw [hδdef]; linarith
  have hgood0 : ∀ x, x ∉ Bad0 → ∀ a b : Fin L,
      ‖flowErr W ⟨g, E, L, s⟩ ![a, b] ![true, true] x‖ ≤ ω * zetaProp g W L s ^ 2 := by
    intro x hx a' b'
    exact not_lt.mp (fun h => hx ⟨(![a', b'], ![true, true]), h⟩)
  -- the crude moments of the blocks
  have hcrB : ∀ (n : ℕ) (Cn : ℝ), Cn ≤ Ccr → ∀ r ∈ Set.Icc s v, ∀ y z : Fin L,
      (Integrable (fun x => ‖blockOf (segG W (⟨g, E, L, r⟩, etaChar g (mRoot g L E) r) x) y z‖ ^ n)
        (μ W L) ∧
      ∫ x, ‖blockOf (segG W (⟨g, E, L, r⟩, etaChar g (mRoot g L E) r) x) y z‖ ^ n ∂(μ W L) ≤
        Cn * (W : ℝ) ^ (C₀ * n)) →
      Integrable (fun x => ‖blockOf (flowG W ⟨g, E, L, r⟩ x) y z‖ ^ n) (μ W L) ∧
      ∫ x, ‖blockOf (flowG W ⟨g, E, L, r⟩ x) y z‖ ^ n ∂(μ W L) ≤
        Ccr * (W : ℝ) ^ (C₀' * n) := by
    intro n Cn hCn r hr y z h
    have eG : ∀ x : Ω W L, segG W (⟨g, E, L, r⟩, etaChar g (mRoot g L E) r) x =
        flowG W ⟨g, E, L, r⟩ x := fun x => step3s_segG_eta W ⟨g, E, L, r⟩ x
    simp only [eG] at h
    refine ⟨h.1, h.2.trans ?_⟩
    have hWn : (W : ℝ) ^ (C₀ * n) ≤ (W : ℝ) ^ (C₀' * n) :=
      Real.rpow_le_rpow_of_exponent_le hW1r
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
    rcases le_or_gt 0 Cn with h0 | h0
    · exact mul_le_mul hCn hWn (by positivity) hCcr0
    · have : Cn * (W : ℝ) ^ (C₀ * n) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h0.le (by positivity)
      exact this.trans (by positivity)
  have hseg : ∀ r ∈ Set.Icc s v, SegAdm R.base R.J W (⟨g, E, L, r⟩, etaChar g (mRoot g L E) r) :=
    fun r hr => ⟨d, hdJ.le, hreachu r (by linarith [hr.1]) (hr.2.trans hvt), Or.inl rfl⟩
  have hcr16 : ∀ r ∈ Set.Icc s v, ∀ y z : Fin L,
      Integrable (fun x => ‖blockOf (flowG W ⟨g, E, L, r⟩ x) y z‖ ^ (4 * (2 * (2 * p))))
        (μ W L) ∧
      ∫ x, ‖blockOf (flowG W ⟨g, E, L, r⟩ x) y z‖ ^ (4 * (2 * (2 * p))) ∂(μ W L) ≤
        Ccr * (W : ℝ) ^ (C₀' * ((4 * (2 * (2 * p)) : ℕ) : ℝ)) := fun r hr y z =>
    hcrB _ C16 (le_trans (le_max_left _ _) (le_max_left _ _)) r hr y z
      (hc16 W hWc16 _ (hseg r hr) y z)
  have hcr12 : ∀ r ∈ Set.Icc s v, ∀ y z : Fin L,
      Integrable (fun x => ‖blockOf (flowG W ⟨g, E, L, r⟩ x) y z‖ ^ (6 * (2 * p))) (μ W L) ∧
      ∫ x, ‖blockOf (flowG W ⟨g, E, L, r⟩ x) y z‖ ^ (6 * (2 * p)) ∂(μ W L) ≤
        Ccr * (W : ℝ) ^ (C₀' * ((6 * (2 * p) : ℕ) : ℝ)) := fun r hr y z =>
    hcrB _ C12 (le_trans (le_max_right _ _) (le_max_left _ _)) r hr y z
      (hc12 W hWc12 _ (hseg r hr) y z)
  have hcr8 : ∀ y z : Fin L,
      Integrable (fun x => ‖blockOf (flowG W ⟨g, E, L, s⟩ x) y z‖ ^ (2 * (2 * (2 * p))))
        (μ W L) ∧
      ∫ x, ‖blockOf (flowG W ⟨g, E, L, s⟩ x) y z‖ ^ (2 * (2 * (2 * p))) ∂(μ W L) ≤
        Ccr * (W : ℝ) ^ (C₀' * ((2 * (2 * (2 * p)) : ℕ) : ℝ)) := fun y z =>
    hcrB _ C8 (le_trans (le_max_left _ _) (le_max_right _ _)) s ⟨le_rfl, hsv⟩ y z
      (hc8 W hWc8 _ (hseg s ⟨le_rfl, hsv⟩) y z)
  have hKcr := hWcr W hWcr'
  rw [Real.rpow_one] at hKcr
  have hMA : (gammaG g * W * (6 + 2 * CR) * L) ^ (2 * (2 * p)) * (2 ^ (4 * (2 * (2 * p)) - 1) *
      (((W : ℝ) + 1) ^ (4 * (2 * (2 * p))) + 9 ^ (4 * (2 * (2 * p))) *
        (Ccr * (W : ℝ) ^ (C₀' * ((4 * (2 * (2 * p)) : ℕ) : ℝ))))) ≤ (W : ℝ) ^ EE := by
    have hA : gammaG g * W * (6 + 2 * CR) * L ≤ (6 + 2 * CR) * (W : ℝ) ^ (CR + 1) := by
      rw [Real.rpow_add hW0, Real.rpow_one]
      have : gammaG g * W * (6 + 2 * CR) * L = (6 + 2 * CR) * W * (gammaG g * L) := by ring
      rw [this]
      calc (6 + 2 * CR) * W * (gammaG g * L) ≤ (6 + 2 * CR) * W * (W : ℝ) ^ CR := by gcongr
        _ = _ := by ring
    have h := step3s_num_crude (2 * (2 * p)) (4 * (2 * (2 * p)))
      (e₂ := C₀' * ((4 * (2 * (2 * p)) : ℕ) : ℝ))
      (B := Ccr * (W : ℝ) ^ (C₀' * ((4 * (2 * (2 * p)) : ℕ) : ℝ))) (by omega) hW1r
      (by positivity) hA (by positivity) hCcr0 (by positivity) le_rfl (by linarith)
    refine h.trans (Real.rpow_le_rpow_of_exponent_le hW1r ?_)
    rw [hEE]; push_cast; nlinarith
  have hMB : (4 * gammaG g * L) ^ (2 * p) * (2 ^ (6 * (2 * p) - 1) *
      (((W : ℝ) + 1) ^ (6 * (2 * p)) + 9 ^ (6 * (2 * p)) *
        (Ccr * (W : ℝ) ^ (C₀' * ((6 * (2 * p) : ℕ) : ℝ))))) ≤ (W : ℝ) ^ EE := by
    have hA : 4 * gammaG g * L ≤ 4 * (W : ℝ) ^ CR := by
      rw [mul_assoc]; gcongr
    have h := step3s_num_crude (2 * p) (6 * (2 * p))
      (e₂ := C₀' * ((6 * (2 * p) : ℕ) : ℝ))
      (B := Ccr * (W : ℝ) ^ (C₀' * ((6 * (2 * p) : ℕ) : ℝ))) (by omega) hW1r
      (by positivity) hA (by positivity) hCcr0 (by positivity) le_rfl (by linarith)
    refine h.trans (Real.rpow_le_rpow_of_exponent_le hW1r ?_)
    rw [hEE]; push_cast; nlinarith
  have hMI : (2 : ℝ) ^ (2 * (2 * p)) * (2 ^ (2 * (2 * (2 * p)) - 1) *
      (((W : ℝ) + 1) ^ (2 * (2 * (2 * p))) + 9 ^ (2 * (2 * (2 * p))) *
        (Ccr * (W : ℝ) ^ (C₀' * ((2 * (2 * (2 * p)) : ℕ) : ℝ))))) ≤ (W : ℝ) ^ EE := by
    have hA : (2 : ℝ) ≤ 2 * (W : ℝ) ^ (0 : ℝ) := by rw [Real.rpow_zero, mul_one]
    have h := step3s_num_crude (2 * (2 * p)) (2 * (2 * (2 * p)))
      (e₂ := C₀' * ((2 * (2 * (2 * p)) : ℕ) : ℝ))
      (B := Ccr * (W : ℝ) ^ (C₀' * ((2 * (2 * (2 * p)) : ℕ) : ℝ))) (by omega) hW1r
      (by norm_num) hA (by norm_num) hCcr0 (by positivity) le_rfl (by linarith)
    refine h.trans (Real.rpow_le_rpow_of_exponent_le hW1r ?_)
    rw [hEE]; push_cast; nlinarith
  -- the moment bound at the terminal time
  have hρ := step3s_num_rho (Wr := W) (E := EE) p hp (by exact_mod_cast hW2)
  have hmom : ∀ a' b' : Fin L,
      (∫ x, ‖flowErr W ⟨g, E, L, v⟩ ![a', b'] ![true, true] x‖ ^ (2 * p) ∂(μ W L)) ^
        (1 / (2 * (p : ℝ))) ≤ (W : ℝ) ^ (3 * ε₁ / 8) * Rr ^ 3 * zetaProp g W L v ^ 2 := by
    intro a' b'
    have hat := step3s_atW g E hW1 hL hg hroot hs hsv hv1 p hp (CR := CR) (ω := ω) (Rr := Rr)
      (Sw := Sw) (δ := δ) (MA := (W : ℝ) ^ EE) (MB := (W : ℝ) ^ EE) (MI := (W : ℝ) ^ EE)
      hRC (by positivity) (by linarith) hSw hδ0 hIm1 hmC hrow1
      (fun r hr a'' => hrow2 r (by linarith [hr.1]) (by linarith [hr.2, hv1]) a'') hK w hw0 hwrow
      Bad hBadμ hgood Bad0 hBad0μ hgood0 hcr16 hcr12 hcr8 hMA hMB hMI a' b'
    refine hat.trans ?_
    have hsv' := hsc s ⟨le_rfl, hst.le⟩
    have hvv := hsc v ⟨hsv, hvt⟩
    have hRv1 : 1 ≤ (1 - s) / (1 - v) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    have hRvR : (1 - s) / (1 - v) ≤ Rr := by
      rw [hRrdef]
      exact div_le_div_of_nonneg_left (by linarith) h1t (by linarith)
    have hζsv : zetaProp g W L s ≤ zetaProp g W L v :=
      (scale_facts g hg W L hW1 hL1 s v hs0 hsv hv1).2.2.2.2.1
    have hδeq : δ = 4 * (W : ℝ) ^ (-(EE + 2 + 48 * p)) := rfl
    rw [hδeq]
    refine step3s_num_final p hp hW4r hω1 hωW hR1 hRv1 hRvR
      (le_trans (by positivity) hsv'.2.2.1) hζsv hvv.2.2.1 hRC hSw (by linarith) (by linarith)
      hδlog hlog (by exact_mod_cast hW2p) (by positivity) (by positivity) (by positivity)
      hρ.1 hρ.2 hρ.1 ?_ ?_
    · have := hWK W hWK'
      exact this
    · rw [hωdef, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
      exact Real.rpow_le_rpow_of_exponent_le hW1r (by push_cast; linarith)
  -- all words and both signs
  have hword : ∀ a' : Fin 2 → Fin L, a' = ![a' 0, a' 1] := fun a' => by
    funext i; fin_cases i <;> rfl
  have hnorm : ∀ (a' : Fin 2 → Fin L) (σ : Bool) (x : Ω W L),
      ‖flowErr W ⟨g, E, L, v⟩ a' ![σ, σ] x‖ =
        ‖flowErr W ⟨g, E, L, v⟩ (if σ then ![a' 0, a' 1] else ![a' 1, a' 0]) ![true, true] x‖ := by
    intro a' σ x
    rw [hword a']
    cases σ
    · simp only [Bool.false_eq_true, ite_false]
      rw [step3s_flowErr_mm W ⟨g, E, L, v⟩ (a' 0) (a' 1) x, norm_star]
      rfl
    · rfl
  set B := (W : ℝ) ^ (3 * ε₁ / 8) * Rr ^ 3 * zetaProp g W L v ^ 2 with hBdef
  have hmom' : ∀ (σ : Bool) (a' : Fin 2 → Fin L),
      (∫ x, ‖flowErr W ⟨g, E, L, v⟩ a' ![σ, σ] x‖ ^ (2 * p) ∂(μ W L)) ^
        (1 / (2 * (p : ℝ))) ≤ B := by
    intro σ a'
    simp only [hnorm a' σ]
    cases σ
    · exact hmom _ _
    · exact hmom _ _
  have hint : ∀ (σ : Bool) (a' : Fin 2 → Fin L),
      Integrable (fun x => ‖flowErr W ⟨g, E, L, v⟩ a' ![σ, σ] x‖ ^ (2 * p)) (μ W L) := by
    intro σ a'
    simp only [hnorm a' σ]
    set l : Fin L × Fin L := if σ then (a' 0, a' 1) else (a' 1, a' 0) with hl
    have el : (if σ then ![a' 0, a' 1] else ![a' 1, a' 0]) = ![l.1, l.2] := by
      cases σ <;> rfl
    rw [el]
    have hcls := step3s_heatClass g E (mRoot g L E) W L hW1 hL hroot l
      (a := -1 / 2) (b := (1 + v) / 2) (by norm_num) (by linarith)
    obtain ⟨-, hc2, ⟨CY, hCY⟩, -, -⟩ := step3s_class_jet hcls
      (⟨by linarith, by linarith⟩ : v ∈ Set.Ioo (-1 / 2 : ℝ) ((1 + v) / 2)) (gammaG g / W)
    have e : (fun x => ‖flowErr W ⟨g, E, L, v⟩ ![l.1, l.2] ![true, true] x‖ ^ (2 * p)) =
        fun x => ‖step3s_field g E (mRoot g L E) W L v (Real.sqrt (v * (gammaG g / W)) • x) l‖ ^
          (2 * p) := by
      funext x; rw [step3s_flowErr_eq g E W L hv0 l x]
    rw [e]
    have hfc : Continuous fun x : Ω W L =>
        ‖step3s_field g E (mRoot g L E) W L v (Real.sqrt (v * (gammaG g / W)) • x) l‖ :=
      continuous_norm.comp (hc2.continuous.comp (continuous_const_smul _))
    refine (integrable_const ((max CY 0) ^ (2 * p))).mono' (hfc.pow _).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) ((hCY _).trans (le_max_left _ _)) _
  -- sampling and Markov
  obtain ⟨S₀, hS₀card, hS₀⟩ := hsm W hWsm d ⟨g, E, L, t⟩ hdJ.le hreach
  have hcard : ((S₀.card : ℕ) : ℝ) ≤ (W : ℝ) ^ CS' :=
    hS₀card.trans (Real.rpow_le_rpow_of_exponent_le hW1r (le_max_left _ _))
  have hζv2 := (hsc v ⟨hsv, hvt⟩).2.2.1
  have hζv0 : 0 < zetaProp g W L v := lt_of_lt_of_le (by positivity) hζv2
  set T₀ := (W : ℝ) ^ (ε₁ / 2) * Rr ^ 3 * zetaProp g W L v ^ 2 with hT₀def
  have hT₀ : 0 < T₀ := by
    have : 0 < Rr := by linarith
    positivity
  set T := (W : ℝ) ^ ε₁ * (Rr ^ ((7 : ℝ) / 2) * zetaProp g W L v ^ 2) with hTdef
  have hsmall : Cs' * T₀ + (W : ℝ) ^ (-(4 : ℝ)) ≤ T :=
    step3s_num_small hW4r hCs'0 (hWCs W hWCs') hε₁0.le hR1 hζv2
  have hB0 : 0 ≤ B := by positivity
  have hratio : B / T₀ ≤ (W : ℝ) ^ (-(ε₁ / 8)) := by
    rw [hBdef, hT₀def, div_le_iff₀ hT₀]
    have e : (W : ℝ) ^ (3 * ε₁ / 8) = (W : ℝ) ^ (-(ε₁ / 8)) * (W : ℝ) ^ (ε₁ / 2) := by
      rw [← Real.rpow_add hW0]; ring_nf
    rw [e]; apply le_of_eq; ring
  have hcnt : ((S₀.card : ℕ) : ℝ) * (B / T₀) ^ (2 * p) ≤ (W : ℝ) ^ (-(D + 1 + 1)) :=
    step3s_num_count hW1 p (Nat.cast_nonneg _) hcard (div_nonneg hB0 hT₀.le) hratio hpε
  have hσ : ∀ σ : Bool, μ W L {x | ∃ a' : Fin 2 → Fin L,
      T < ‖flowErr W ⟨g, E, L, v⟩ a' ![σ, σ] x‖} ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) := by
    intro σ
    have hsb := step3s_sb_mono (μ W L) (fun a' x => flowErr W ⟨g, E, L, v⟩ a' ![σ, σ] x) S₀
      (le_max_left Cs 0) (hS₀ ![σ, σ] v hv0 hvt).2.1
    have h := step3s_sample_markov (μ W L) (fun a' x => flowErr W ⟨g, E, L, v⟩ a' ![σ, σ] x) S₀
      p hp hCs'0 hB0 hT₀ hsb (hint σ) (hmom' σ) hsmall
    refine h.trans ?_
    have e2 : (W : ℝ) ^ (-(D + 2)) = (W : ℝ) ^ (-(D + 1 + 1)) := by ring_nf
    rw [e2, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact le_trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hcnt)) (step3s_two W hW2 (D + 1))
  -- the conclusion
  change μ W L {x | ∃ l : Fin L × Fin L × Bool, (W : ℝ) ^ ε * (Rr ^ ((7 : ℝ) / 2) *
    zetaProp g W L v ^ 2) < ‖flowErr W ⟨g, E, L, v⟩ ![l.1, l.2.1] ![l.2.2, l.2.2] x‖} ≤ _
  have hsub : {x : Ω W L | ∃ l : Fin L × Fin L × Bool, (W : ℝ) ^ ε * (Rr ^ ((7 : ℝ) / 2) *
      zetaProp g W L v ^ 2) < ‖flowErr W ⟨g, E, L, v⟩ ![l.1, l.2.1] ![l.2.2, l.2.2] x‖} ⊆
      {x | ∃ a' : Fin 2 → Fin L, T < ‖flowErr W ⟨g, E, L, v⟩ a' ![true, true] x‖} ∪
      {x | ∃ a' : Fin 2 → Fin L, T < ‖flowErr W ⟨g, E, L, v⟩ a' ![false, false] x‖} := by
    rintro x ⟨⟨a', b', σ⟩, hl⟩
    have hT : T ≤ (W : ℝ) ^ ε * (Rr ^ ((7 : ℝ) / 2) * zetaProp g W L v ^ 2) := by
      rw [hTdef]
      have : 0 ≤ Rr ^ ((7 : ℝ) / 2) * zetaProp g W L v ^ 2 := by
        have : 0 < Rr := by linarith
        positivity
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hW1r hε₁ε) this
    cases σ
    · exact Or.inr ⟨![a', b'], lt_of_le_of_lt hT hl⟩
    · exact Or.inl ⟨![a', b'], lt_of_le_of_lt hT hl⟩
  calc _ ≤ μ W L ({x | ∃ a' : Fin 2 → Fin L, T < ‖flowErr W ⟨g, E, L, v⟩ a' ![true, true] x‖} ∪
        {x | ∃ a' : Fin 2 → Fin L, T < ‖flowErr W ⟨g, E, L, v⟩ a' ![false, false] x‖}) :=
        measure_mono hsub
    _ ≤ _ := (measure_union_le _ _).trans
        ((add_le_add (hσ true) (hσ false)).trans (step3s_two W hW2 D))

end Step3Main

/-- Step 3 of Appendix C.3 [sec:gc-one-step], same-sign pair (C.37) [fo:eq:same-pair] at fixed
times without a barrier: on the mixed-pair events,
`|ℒ₂^{++}(a,c)| ≤ (ℒ₂^{+-}(a,c) ℒ₂^{+-}(c,a))^{1/2}`, and the moment comparison for `D₂` with a
Grönwall step gives `|D₂(u; a, b; σ, σ)| ≺ R^{7/2} ζ_u²`. -/
theorem step3_same (R : PropRegime) (I : PropInputs R.base R.J) (c cp θ N cp₂ : ℝ) (hc : 0 < c)
    (hcp₂ : 0 < cp₂) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2) (hN : lemmaNN0 I.Cw ≤ N)
    (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q})
    (hSu : ∀ W, ∀ q ∈ S W, ∀ v : ℝ, q.s ≤ v → v ≤ q.u →
      (⟨q.g, q.E, q.L, q.s, q.t, v⟩ : StepPt) ∈ S W)
    (hin : OneStepInput cp θ (fun q : StepPt => q.at q.s) S) (h1 : Step1Out S)
    (h2 : Step2Out cp₂ θ S) :
    PrecMax StepPt.L S (Λ := fun _ q => Fin q.L × Fin q.L × Bool)
      (fun W q x ω => flowErr W (q.at q.u) ![x.1, x.2.1] ![x.2.2, x.2.2] ω)
      (fun W q _ => q.ratio ^ ((7 : ℝ) / 2) * zetaProp q.g W q.L q.u ^ 2) := by
  exact step3s_main R I c cp θ N cp₂ hc hcp₂ hθ hθ2 hN S hS hSu hin h1 h2

end LSBA
