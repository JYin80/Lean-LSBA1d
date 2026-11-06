import LSBA.Upper.SmallChart
import LSBA.Upper.AngularField
import LSBA.Analysis.FlagDerivativeRot

/-!
# Lemma 9.2 [su:lem:field-geometry]: the constructed field satisfies the geometric conditions

Lemma 9.2 [su:lem:field-geometry]. At a sample with the prepared chart (9.1) [su:eq:graph-input]
at `j = 4`, with `R_5, …, R_{q-1}` defined, and a skew-Hermitian `K` with the normalization (9.8)
[su:eq:generator-normalization], the line derivative `D` of the batch `T = S* T_q ⋯ T_1 S` along
the field `X` of (9.10) [us:eq:physical] has the form `D = (1 ⊗ (K - L)) T + T N` with `N` leaving
`U` and `Y` invariant and `Re Tr(P_Y N) - Re Tr(P_U N) = 1`. Hence (9.11) [su:eq:field-geometry]
holds in the projection form of (8.34) [up:eq:angular-geometry] with `K_out = K - L`. No condition
is imposed on `V_q`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `ran A ⊆ ran B` gives a factorization `A = B C`. -/
private lemma FieldGeometry_exists_mul {m n k : Type*} [Fintype n] [Fintype k]
    {A : Matrix m n ℂ} {B : Matrix m k ℂ}
    (h : LinearMap.range A.mulVecLin ≤ LinearMap.range B.mulVecLin) :
    ∃ C : Matrix k n ℂ, A = B * C := by
  have hc : ∀ j : n, ∃ c : k → ℂ, B *ᵥ c = A *ᵥ Pi.single j 1 := by
    intro j
    obtain ⟨c, hc⟩ := h (LinearMap.mem_range_self A.mulVecLin (Pi.single j 1))
    exact ⟨c, hc⟩
  choose c hc using hc
  refine ⟨Matrix.of fun i j => c j i, ?_⟩
  ext i j
  have := congrFun (hc j) i
  rw [Matrix.mulVec_single_one] at this
  simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this.symm

/-- The graph frame `(I; -g R)` is injective: `G A = G B` implies `A = B`. -/
private lemma FieldGeometry_graph_cancel {W : ℕ} {n : Type*} (g : ℝ) (R : Matrix (Fin W) (Fin W) ℂ)
    {A B : Matrix (Fin W) n ℂ} (h : graphFrame g R * A = graphFrame g R * B) : A = B := by
  ext i j
  have := congrFun (congrFun h (0, i)) j
  simpa [graphFrame, colStack, Matrix.mul_apply, Matrix.one_apply] using this

/-- `A ⊗ (B - C) = A ⊗ B - A ⊗ C`. -/
private lemma FieldGeometry_kron_sub {W : ℕ} (A : Matrix (Fin 2) (Fin 2) ℂ)
    (B C : Matrix (Fin W) (Fin W) ℂ) : A ⊗ₖ (B - C) = A ⊗ₖ B - A ⊗ₖ C := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp [Matrix.kroneckerMap_apply, mul_sub]

/-- `(X; Y) - (X'; Y') = (X - X'; Y - Y')`. -/
private lemma FieldGeometry_colStack_sub {W : ℕ} (X Y X' Y' : Matrix (Fin W) (Fin W) ℂ) :
    colStack X Y - colStack X' Y' = colStack (X - X') (Y - Y') := by
  ext ⟨i, α⟩ β
  fin_cases i <;> simp [colStack]

/-- `(X; Y) B = (X B; Y B)`. -/
private lemma FieldGeometry_colStack_mul {W : ℕ} (X Y B : Matrix (Fin W) (Fin W) ℂ) :
    colStack X Y * B = colStack (X * B) (Y * B) := by
  ext ⟨i, α⟩ β
  fin_cases i <;> simp [colStack, Matrix.mul_apply]

/-- `(1 ⊗ K) (X; Y) = (K X; K Y)`. -/
private lemma FieldGeometry_one_kron_colStack {W : ℕ} (K X Y : Matrix (Fin W) (Fin W) ℂ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K) * colStack X Y = colStack (K * X) (K * Y) := by
  ext ⟨i, α⟩ β
  fin_cases i <;> simp [colStack, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- `(E₀₀ ⊗ Z) (X; Y) = (Z X; 0)`. -/
private lemma FieldGeometry_e00_kron_colStack {W : ℕ} (Z X Y : Matrix (Fin W) (Fin W) ℂ) :
    (!![1, 0; 0, 0] ⊗ₖ Z) * colStack X Y = colStack (Z * X) 0 := by
  ext ⟨i, α⟩ β
  fin_cases i <;> simp [colStack, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.kroneckerMap_apply]

/-- `T(z) (X; Y) = (z X - g⁻¹ V X - Y; X)` for the transfer matrix of Definition 7.1
[def:transfer-matrices]. -/
private lemma FieldGeometry_transferMat_colStack {W : ℕ} (g : ℝ) (z : ℂ)
    (V X Y : Matrix (Fin W) (Fin W) ℂ) :
    transferMat g z V * colStack X Y = colStack (z • X - (g : ℂ)⁻¹ • (V * X) - Y) X := by
  ext ⟨i, α⟩ β
  fin_cases i
  · simp [colStack, transferMat, transferFree, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.sub_apply,
      Matrix.smul_apply, Finset.mul_sum, sub_mul, Finset.sum_sub_distrib, mul_assoc]
    ring
  · simp [colStack, transferMat, transferFree, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- `T(z) (1 ⊗ K) = (1 ⊗ K) T(z) + g⁻¹ E₀₀ ⊗ [K, V]`. -/
private lemma FieldGeometry_transferMat_comm {W : ℕ} (g : ℝ) (z : ℂ)
    (V K : Matrix (Fin W) (Fin W) ℂ) :
    transferMat g z V * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K) =
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K) * transferMat g z V +
        (g : ℂ)⁻¹ • (!![1, 0; 0, 0] ⊗ₖ (K * V - V * K)) := by
  unfold transferMat transferFree
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, FieldGeometry_kron_sub, smul_sub]
  simp only [Matrix.mul_one, Matrix.one_mul]
  abel

/-- The derivative of the prefix products `T_j ⋯ T_1` when the blocks move with velocities
`X_k`: `D_0 = 0`, `D_{j+1} = -g⁻¹ (E₀₀ ⊗ X_j) T_j ⋯ T_1 + T_{j+1} D_j`. -/
private def FieldGeometry_dProd {W : ℕ} (g : ℝ) (z : ℂ) (V Xs : ℕ → Matrix (Fin W) (Fin W) ℂ) :
    ℕ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ
  | 0 => 0
  | j + 1 => -((g : ℂ)⁻¹ • (!![1, 0; 0, 0] ⊗ₖ Xs j)) * transferProd g z V j +
      transferMat g z (V j) * FieldGeometry_dProd g z V Xs j

/-- The prefix products have the derivative `FieldGeometry_dProd` when every block has a
derivative. -/
private lemma FieldGeometry_hasDerivAt_transferProd {W : ℕ} (g : ℝ) (z : ℂ)
    (V : ℝ → ℕ → Matrix (Fin W) (Fin W) ℂ) (Xs : ℕ → Matrix (Fin W) (Fin W) ℂ)
    (hV : ∀ k, HasDerivAt (fun t => V t k) (Xs k) 0) (j : ℕ) :
    HasDerivAt (fun t => transferProd g z (V t) j) (FieldGeometry_dProd g z (V 0) Xs j) 0 := by
  induction j with
  | zero =>
    simp only [transferProd, FieldGeometry_dProd]
    exact hasDerivAt_const _ _
  | succ j ih =>
    let Φ : Matrix (Fin W) (Fin W) ℂ →ₗ[ℝ] Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
      { toFun := fun A => (g : ℂ)⁻¹ • (!![1, 0; 0, 0] ⊗ₖ A)
        map_add' := fun A B => by rw [Matrix.kronecker_add, smul_add]
        map_smul' := fun c A => by
          rw [RingHom.id_apply, ← Complex.coe_smul, Matrix.kronecker_smul, smul_comm,
            Complex.coe_smul] }
    have h1 := (LinearMap.toContinuousLinearMap Φ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hV j)
    have hT : HasDerivAt (fun t => transferMat g z (V t j))
        (-((g : ℂ)⁻¹ • (!![1, 0; 0, 0] ⊗ₖ Xs j))) 0 := by
      have h2 := h1.const_sub (transferFree W z)
      simpa [Φ, Function.comp_def, transferMat, zero_sub] using h2
    have := hT.mul ih
    simp only [transferProd, FieldGeometry_dProd]
    exact this

/-- `-(X; Y) = (-X; -Y)`. -/
private lemma FieldGeometry_neg_colStack {W : ℕ} (X Y : Matrix (Fin W) (Fin W) ℂ) :
    -colStack X Y = colStack (-X) (-Y) := by
  ext ⟨i, α⟩ β
  fin_cases i <;> simp [colStack]

/-- `c (X; Y) = (c X; c Y)`. -/
private lemma FieldGeometry_smul_colStack {W : ℕ} (c : ℂ) (X Y : Matrix (Fin W) (Fin W) ℂ) :
    c • colStack X Y = colStack (c • X) (c • Y) := by
  ext ⟨i, α⟩ β
  fin_cases i <;> simp [colStack]

/-- Equal blocks give equal stacks. -/
private lemma FieldGeometry_colStack_inj {W : ℕ} {X Y X' Y' : Matrix (Fin W) (Fin W) ℂ}
    (h1 : X = X') (h2 : Y = Y') : colStack X Y = colStack X' Y' := by
  rw [h1, h2]

/-- The first active block: `-g⁻¹ (E₀₀ ⊗ [K, V - g² R]) G = (1 ⊗ K) T G - T G K` for the graph
frame `G = (I; -g R)` and `T = T(z)` with `g z = E`. -/
private lemma FieldGeometry_base_id {W : ℕ} {g : ℝ} (hg : g ≠ 0) (z : ℂ)
    (V R K : Matrix (Fin W) (Fin W) ℂ) :
    -((g : ℂ)⁻¹ • (!![1, 0; 0, 0] ⊗ₖ (K * (V - ((g : ℂ) ^ 2) • R) - (V - ((g : ℂ) ^ 2) • R) * K)))
        * graphFrame g R =
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K) * (transferMat g z V * graphFrame g R) -
        transferMat g z V * graphFrame g R * K := by
  have hgc : (g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg
  rw [graphFrame, FieldGeometry_transferMat_colStack, FieldGeometry_one_kron_colStack,
    FieldGeometry_colStack_mul, FieldGeometry_colStack_sub, Matrix.neg_mul, Matrix.smul_mul,
    FieldGeometry_e00_kron_colStack, FieldGeometry_smul_colStack, FieldGeometry_neg_colStack]
  apply FieldGeometry_colStack_inj
  · have h : (g : ℂ)⁻¹ * (g : ℂ) ^ 2 = g := by field_simp
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, smul_sub, Matrix.mul_one, Matrix.one_mul, smul_smul, h, sub_neg_eq_add]
    abel
  · simp

/-- Every graph coordinate `R_j` is Hermitian when `R_4` is. -/
private lemma FieldGeometry_chartR_herm {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    (hR : R.IsHermitian) (ω : Ω W q) (j : ℕ) : (chartR W g E q R ω j).IsHermitian := by
  have hB : ∀ k, (blockSeq W q ω k).IsHermitian := by
    intro k
    unfold blockSeq
    split_ifs
    · exact gueBlock_isHermitian W q ω _
    · exact Matrix.isHermitian_zero
  have hs : ∀ (r : ℝ) (A : Matrix (Fin W) (Fin W) ℂ), A.IsHermitian →
      ((r : ℂ) • A).IsHermitian := by
    intro r A hA
    unfold Matrix.IsHermitian at hA ⊢
    rw [Matrix.conjTranspose_smul, hA]
    simp
  induction j with
  | zero => simpa [chartR] using hR
  | succ j ih =>
    simp only [chartR]
    split_ifs
    · exact hR
    · have h2 := hs (g ^ 2) _ ih
      push_cast at h2
      exact ((hB j).sub (hs E 1 Matrix.isHermitian_one)).sub h2 |>.inv

/-- Transport of the prepared frame through the active blocks `5 ≤ j ≤ q - 1` (proof of
Lemma 9.2 [su:lem:field-geometry]): if `T_4 ⋯ T_1 B = G_4 C`, then `T_j ⋯ T_1 B = G_j Φ_j C`
and its derivative along `X` is `(1 ⊗ K) G_j Φ_j C - G_j Φ_j K C`, where
`G_j = (I; -g R_j)` and `Φ_j R_{[j,5]}* = c_j` for a real `c_j ≠ 0`. -/
private lemma FieldGeometry_chain {W q : ℕ} {g E : ℝ} (hg : g ≠ 0) {z : ℂ}
    (hgz : (g : ℂ) * z = E) (ω : Ω W q) {R : Matrix (Fin W) (Fin W) ℂ} (hR : R.IsHermitian)
    (hRu : ∀ j, 5 ≤ j → j ≤ q - 1 → IsUnit (chartR W g E q R ω j))
    {K : Matrix (Fin W) (Fin W) ℂ} {Xs : ℕ → Matrix (Fin W) (Fin W) ℂ}
    (hX0 : ∀ k, k < 4 → Xs k = 0)
    (hX4 : Xs 4 = K * (blockSeq W q ω 4 - ((g : ℂ) ^ 2) • R) -
      (blockSeq W q ω 4 - ((g : ℂ) ^ 2) • R) * K)
    (hXmid : ∀ j, 5 ≤ j → j + 1 < q → Xs j = K * blockSeq W q ω j - blockSeq W q ω j * K) :
    ∀ j, 5 ≤ j → j ≤ q - 1 → ∃ (Φ : Matrix (Fin W) (Fin W) ℂ) (c : ℝ), c ≠ 0 ∧
      Φ * (chartProd W g E q R ω j)ᴴ = (c : ℂ) • 1 ∧
      ∀ (B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (C : Matrix (Fin W) (Fin 2 × Fin W) ℂ),
        transferProd g z (blockSeq W q ω) 4 * B = graphFrame g R * C →
        transferProd g z (blockSeq W q ω) j * B = graphFrame g (chartR W g E q R ω j) * Φ * C ∧
        FieldGeometry_dProd g z (blockSeq W q ω) Xs j * B =
          ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K) * (graphFrame g (chartR W g E q R ω j) * Φ * C) -
            graphFrame g (chartR W g E q R ω j) * Φ * K * C := by
  set V := blockSeq W q ω with hVdef
  have hgc : (g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg
  -- the matrices `M_j = V_j - E - g² R_j` and the recursion `R_{j+1} = M_j⁻¹`
  have hRsucc : ∀ {j : ℕ}, 4 ≤ j → chartR W g E q R ω (j + 1) =
      (V j - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • chartR W g E q R ω j)⁻¹ := by
    intro j hj
    have h4 : ¬ j < 4 := not_lt.mpr hj
    simp only [chartR, h4, ↓reduceIte, hVdef]
  have hPsucc : ∀ {j : ℕ}, 4 ≤ j →
      chartProd W g E q R ω (j + 1) = chartR W g E q R ω (j + 1) * chartProd W g E q R ω j := by
    intro j hj
    have h4 : ¬ j < 4 := not_lt.mpr hj
    simp only [chartProd, h4, ↓reduceIte]
  have hR4 : chartR W g E q R ω 4 = R := by simp [chartR]
  have hP4 : chartProd W g E q R ω 4 = 1 := by simp [chartProd]
  have hD4 : FieldGeometry_dProd g z V Xs 4 = 0 := by
    simp [FieldGeometry_dProd, hX0]
  -- one transfer step on the chart: `T_j G_j = G_{j+1} (-g⁻¹ M_j)`
  have hstep : ∀ {j : ℕ}, 4 ≤ j → IsUnit (chartR W g E q R ω (j + 1)) →
      transferMat g z (V j) * graphFrame g (chartR W g E q R ω j) =
        graphFrame g (chartR W g E q R ω (j + 1)) *
          (-((g : ℂ)⁻¹ • (V j - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • chartR W g E q R ω j))) ∧
      (V j - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • chartR W g E q R ω j) *
        chartR W g E q R ω (j + 1) = 1 := by
    intro j hj hu
    rw [hRsucc hj] at hu ⊢
    have hu' := Matrix.isUnit_nonsing_inv_iff.mp hu
    have hu'' := hu'
    rw [← hgz] at hu''
    constructor
    · have := transferMat_mul_graphFrame_of_isUnit hg z (V j) (chartR W g E q R ω j) hu''
      rw [hgz] at this
      exact this
    · exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu')
  have hPi : ∀ j, transferProd g z V (j + 1) = transferMat g z (V j) * transferProd g z V j :=
    fun _ => rfl
  have hDs : ∀ j, FieldGeometry_dProd g z V Xs (j + 1) =
      -((g : ℂ)⁻¹ • (!![1, 0; 0, 0] ⊗ₖ Xs j)) * transferProd g z V j +
        transferMat g z (V j) * FieldGeometry_dProd g z V Xs j := fun _ => rfl
  -- the induction
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro hq5
    obtain ⟨hT, hMR⟩ := hstep (le_refl 4) (hRu 5 (le_refl 5) hq5)
    rw [hR4] at hT hMR
    refine ⟨-((g : ℂ)⁻¹ • (V 4 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R)), -g⁻¹,
      neg_ne_zero.mpr (inv_ne_zero hg), ?_, ?_⟩
    · rw [hPsucc (le_refl 4), hP4, Matrix.mul_one, (FieldGeometry_chartR_herm hR ω 5).eq,
        Matrix.neg_mul, Matrix.smul_mul, hMR]
      push_cast
      simp
    · intro B C hBC
      have hGΦ : graphFrame g (chartR W g E q R ω 5) *
          -((g : ℂ)⁻¹ • (V 4 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R)) =
          transferMat g z (V 4) * graphFrame g R := hT.symm
      constructor
      · rw [hPi, Matrix.mul_assoc, hBC, hGΦ, Matrix.mul_assoc]
      · rw [hDs, hD4, Matrix.mul_zero, add_zero, Matrix.mul_assoc, hBC, hGΦ, hX4,
          ← Matrix.mul_assoc, FieldGeometry_base_id hg z]
        simp only [Matrix.sub_mul, Matrix.mul_assoc]
  | succ j hj ih =>
    intro hjq
    obtain ⟨Φ, c, hc, hΦ, hBC'⟩ := ih (by omega)
    obtain ⟨hT, hMR⟩ := hstep (by omega : 4 ≤ j) (hRu (j + 1) (by omega) hjq)
    set M := V j - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • chartR W g E q R ω j with hMdef
    refine ⟨-((g : ℂ)⁻¹ • M) * Φ, -g⁻¹ * c, mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hg)) hc,
      ?_, ?_⟩
    · rw [hPsucc (by omega : 4 ≤ j), Matrix.conjTranspose_mul,
        (FieldGeometry_chartR_herm hR ω (j + 1)).eq, Matrix.mul_assoc, ← Matrix.mul_assoc Φ,
        hΦ, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.neg_mul, Matrix.smul_mul,
        hMR]
      push_cast
      simp [smul_smul, mul_comm]
    · intro B C hBC
      obtain ⟨h1, h2⟩ := hBC' B C hBC
      have hGΦ : graphFrame g (chartR W g E q R ω (j + 1)) * (-((g : ℂ)⁻¹ • M) * Φ) =
          transferMat g z (V j) * (graphFrame g (chartR W g E q R ω j) * Φ) := by
        rw [← Matrix.mul_assoc, ← hT, Matrix.mul_assoc]
      have hcomm := FieldGeometry_transferMat_comm g z (V j) K
      have hX := hXmid j hj (by omega)
      constructor
      · rw [hPi, Matrix.mul_assoc, h1, hGΦ]
        simp only [Matrix.mul_assoc]
      · set T := transferMat g z (V j)
        set G := graphFrame g (chartR W g E q R ω j)
        set A : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K
        have h0 : -((g : ℂ)⁻¹ • (!![1, 0; 0, 0] ⊗ₖ Xs j)) + (T * A - A * T) = 0 := by
          rw [hcomm, hX]
          abel
        calc FieldGeometry_dProd g z V Xs (j + 1) * B
            = -((g : ℂ)⁻¹ • (!![1, 0; 0, 0] ⊗ₖ Xs j)) * (transferProd g z V j * B) +
                T * (FieldGeometry_dProd g z V Xs j * B) := by
              rw [hDs, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc]
          _ = (-((g : ℂ)⁻¹ • (!![1, 0; 0, 0] ⊗ₖ Xs j)) + (T * A - A * T)) * (G * Φ * C) +
                A * (T * (G * Φ * C)) - T * (G * Φ * K * C) := by
              rw [h1, h2]
              noncomm_ring
          _ = A * (T * (G * Φ) * C) - T * (G * Φ) * K * C := by
              rw [h0]
              simp only [Matrix.zero_mul, zero_add, Matrix.mul_assoc]
          _ = _ := by rw [← hGΦ]

/-- The last block: `g⁻¹ (E₀₀ ⊗ [L, V - g² R]) G = T G L - (1 ⊗ L) T G` for the graph frame
`G = (I; -g R)` and `T = T(z)`. -/
private lemma FieldGeometry_last_id {W : ℕ} {g : ℝ} (hg : g ≠ 0) (z : ℂ)
    (V R L : Matrix (Fin W) (Fin W) ℂ) :
    (g : ℂ)⁻¹ • (!![1, 0; 0, 0] ⊗ₖ (L * (V - ((g : ℂ) ^ 2) • R) - (V - ((g : ℂ) ^ 2) • R) * L))
        * graphFrame g R =
      transferMat g z V * graphFrame g R * L -
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ L) * (transferMat g z V * graphFrame g R) := by
  have hgc : (g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg
  have h : (g : ℂ)⁻¹ * (g : ℂ) ^ 2 = g := by field_simp
  rw [graphFrame, FieldGeometry_transferMat_colStack, FieldGeometry_one_kron_colStack,
    FieldGeometry_colStack_mul, FieldGeometry_colStack_sub, Matrix.smul_mul,
    FieldGeometry_e00_kron_colStack, FieldGeometry_smul_colStack]
  apply FieldGeometry_colStack_inj
  · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, smul_sub, Matrix.mul_one, Matrix.one_mul, smul_smul, h, sub_neg_eq_add]
    abel
  · simp

/-- `1 ⊗ A` commutes with `S_0*`. -/
private lemma FieldGeometry_freeConj_comm {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ A) * (freeConj W 0)ᴴ =
      (freeConj W 0)ᴴ * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ A) := by
  unfold freeConj
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_kronecker, Matrix.mul_smul,
    Matrix.smul_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.conjTranspose_one]

/-- The orthogonal projection `1 - ‖v‖⁻² v v*` is idempotent and kills `v v*`. -/
private lemma FieldGeometry_proj {W : ℕ} {v : Fin W → ℂ} (hv : star v ⬝ᵥ v ≠ 0) :
    Matrix.vecMulVec v (star v) *
        (1 - (star v ⬝ᵥ v)⁻¹ • Matrix.vecMulVec v (star v)) = 0 ∧
      (1 - (star v ⬝ᵥ v)⁻¹ • Matrix.vecMulVec v (star v)) *
        (1 - (star v ⬝ᵥ v)⁻¹ • Matrix.vecMulVec v (star v)) =
        1 - (star v ⬝ᵥ v)⁻¹ • Matrix.vecMulVec v (star v) := by
  have hPP : Matrix.vecMulVec v (star v) * Matrix.vecMulVec v (star v) =
      (star v ⬝ᵥ v) • Matrix.vecMulVec v (star v) := by
    rw [Matrix.vecMulVec_mul_vecMulVec]
    ext i j
    simp [Matrix.vecMulVec_apply]
    ring
  have h1 : Matrix.vecMulVec v (star v) *
      (1 - (star v ⬝ᵥ v)⁻¹ • Matrix.vecMulVec v (star v)) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, hPP, smul_smul, inv_mul_cancel₀ hv,
      one_smul, sub_self]
  refine ⟨h1, ?_⟩
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, h1, smul_zero, sub_zero]

/-- The choice of `M_U`, `M_Y` from a matrix `Z` with `v* Z = v*`, and the trace identity
`Re Tr(P_Y M_Y) - Re Tr(P_U M_U) = 1`. -/
private lemma FieldGeometry_motion_alg {W : ℕ} {ι : Type*} [Fintype ι]
    {v : Fin W → ℂ} (hv : star v ⬝ᵥ v ≠ 0) {Z : Matrix (Fin W) (Fin W) ℂ}
    (hZ : Matrix.vecMulVec v (star v) * Z = Matrix.vecMulVec v (star v))
    {PY PU : Matrix ι ι ℂ} {CY CU : Matrix (Fin W) ι ℂ} {RY RU : Matrix ι (Fin W) ℂ}
    (hCRY : CY * RY = 1) (hPRY : PY * RY = RY)
    (hCRU : CU * RU = 1 - (star v ⬝ᵥ v)⁻¹ • Matrix.vecMulVec v (star v)) (hPRU : PU * RU = RU)
    (hQCU : (1 - (star v ⬝ᵥ v)⁻¹ • Matrix.vecMulVec v (star v)) * CU = CU) :
    CY * (RY * Z * CY) = Z * CY ∧ CU * (RU * Z * CU) = Z * CU ∧
      (PY * (RY * Z * CY)).trace.re - (PU * (RU * Z * CU)).trace.re = 1 := by
  set Pv := Matrix.vecMulVec v (star v) with hPv
  set Q := 1 - (star v ⬝ᵥ v)⁻¹ • Pv with hQ
  obtain ⟨hPQ, -⟩ := FieldGeometry_proj hv
  have hQZ : Q * Z = Z - (star v ⬝ᵥ v)⁻¹ • Pv := by
    rw [hQ, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, hZ]
  have hQZQ : Q * Z * Q = Z * Q := by
    rw [hQZ, Matrix.sub_mul, Matrix.smul_mul, hPQ, smul_zero, sub_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hCRY, Matrix.one_mul]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hCRU, ← hQCU, ← Matrix.mul_assoc, hQZQ,
      Matrix.mul_assoc, hQCU]
  · have hY : (PY * (RY * Z * CY)).trace = Z.trace := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPRY, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
        hCRY, Matrix.one_mul]
    have hU : (PU * (RU * Z * CU)).trace = Z.trace - 1 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPRU, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
        hCRU, hQZ, Matrix.trace_sub, Matrix.trace_smul, hPv, Matrix.trace_vecMulVec,
        dotProduct_comm v, smul_eq_mul, inv_mul_cancel₀ hv]
    rw [hY, hU, Complex.sub_re, Complex.one_re]
    ring

open scoped ComplexOrder in
/-- `v* v ≠ 0` for `v ≠ 0`. -/
private lemma FieldGeometry_dot_ne {W : ℕ} {v : Fin W → ℂ} (hv : v ≠ 0) : star v ⬝ᵥ v ≠ 0 :=
  fun h => hv (dotProduct_star_self_eq_zero.mp h)

/-- The motion of the batch along `X` of (9.10) [us:eq:physical] (proof of Lemma 9.2
[su:lem:field-geometry]): `(D - (1 ⊗ (K - L)) T) P_U = T P_U M_U`,
`(D - (1 ⊗ (K - L)) T) P_Y = T P_Y M_Y` and `Re Tr(P_Y M_Y) - Re Tr(P_U M_U) = 1`. -/
theorem smallField_motion {W q : ℕ} {g E : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) (hq : 7 ≤ q)
    (x : IsoFlag W) (ω : Ω W q) {R : Matrix (Fin W) (Fin W) ℂ} {v : Fin W → ℂ}
    (hprep : IsPrepChart W g E q x ω R v)
    (hRu : ∀ j, 5 ≤ j → j ≤ q - 1 → IsUnit (chartR W g E q R ω j))
    {K : Matrix (Fin W) (Fin W) ℂ} (hK : Kᴴ = -K) (hn : IsGenNormalized W g E q R v K ω) :
    ∃ D : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
      HasLineDerivAt ℝ (batchMat W g E q) D ω (hermCoord W q (smallField W g E q R v K ω)) ∧
      ∃ MU MY : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
        (D - ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (K - smallCorr W g E q R v K ω)) *
            batchMat W g E q ω) * x.1.1 = batchMat W g E q ω * x.1.1 * MU ∧
        (D - ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (K - smallCorr W g E q R v K ω)) *
            batchMat W g E q ω) * x.1.2 = batchMat W g E q ω * x.1.2 * MY ∧
        (x.1.2 * MY).trace.re - (x.1.1 * MU).trace.re = 1 := by
  have hg0 : g ≠ 0 := hg.ne'
  have hgc : (g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg0
  have hq4 : 4 < q := by omega
  obtain ⟨hR, hv, hrY, hrU⟩ := hprep
  have hXh := smallField_isHermitian hR hK ω hn
  set z : ℂ := ((max 1 g * E / g : ℝ) : ℂ) with hz
  have hgz : (g : ℂ) * z = E := by
    rw [hz, max_eq_left hg1]
    push_cast
    field_simp
  set X := smallField W g E q R v K ω with hXdef
  set L := smallCorr W g E q R v K ω with hLdef
  set Y := hermCoord W q X with hYdef
  set S := freeConj W 0 with hSdef
  set V := blockSeq W q ω with hVdef
  set Xs : ℕ → Matrix (Fin W) (Fin W) ℂ := fun k => if h : k < q then X ⟨k, h⟩ else 0 with hXs
  -- the blocks move along `X`
  have hV : ∀ k, HasDerivAt (fun t : ℝ => blockSeq W q (ω + t • Y) k) (Xs k) 0 := by
    intro k
    by_cases hk : k < q
    · have h : ∀ t : ℝ, blockSeq W q (ω + t • Y) k = V k + t • X ⟨k, hk⟩ := by
        intro t
        simp only [hVdef, blockSeq, hk, dite_true]
        rw [gueBlock_add_smul_hermCoord hXh, Complex.coe_smul]
      have := ((hasDerivAt_id (0 : ℝ)).smul_const (X ⟨k, hk⟩)).const_add (V k)
      simp only [hXs, hk, dite_true]
      simpa [h] using this
    · simp only [blockSeq, hk, dite_false, hXs]
      exact hasDerivAt_const _ _
  have hPd := FieldGeometry_hasDerivAt_transferProd g z (fun t => blockSeq W q (ω + t • Y)) Xs hV q
  simp only [zero_smul, add_zero] at hPd
  set D := Sᴴ * FieldGeometry_dProd g z V Xs q * S with hDdef
  have hbatch : ∀ η, batchMat W g E q η = Sᴴ * transferProd g z (blockSeq W q η) q * S :=
    fun _ => rfl
  refine ⟨D, ?_, ?_⟩
  · unfold HasLineDerivAt
    simp only [hbatch]
    exact (hPd.const_mul Sᴴ).mul_const S
  -- the components of `X`
  have hblock : ∀ {k : ℕ} (hk : k < q), V k = gueBlock W q ω ⟨k, hk⟩ := by
    intro k hk
    simp [hVdef, blockSeq, hk]
  have hX0 : ∀ k, k < 4 → Xs k = 0 := by
    intro k hk
    have hkq : k < q := by omega
    simp [hXs, hkq, hXdef, smallField, hk]
  have hX4 : Xs 4 = K * (V 4 - ((g : ℂ) ^ 2) • R) - (V 4 - ((g : ℂ) ^ 2) • R) * K := by
    rw [hblock hq4]
    simp [hXs, hq4, hXdef, smallField]
  have hXmid : ∀ j, 5 ≤ j → j + 1 < q → Xs j = K * V j - V j * K := by
    intro j hj hjq
    have hjq' : j < q := by omega
    rw [hblock hjq']
    have h1 : ¬ j < 4 := by omega
    have h2 : j ≠ 4 := by omega
    simp [hXs, hjq', hXdef, smallField, h1, h2, hjq]
  have hXlast : Xs (q - 1) = K * V (q - 1) - V (q - 1) * K -
      (L * (V (q - 1) - ((g : ℂ) ^ 2) • chartR W g E q R ω (q - 1)) -
        (V (q - 1) - ((g : ℂ) ^ 2) • chartR W g E q R ω (q - 1)) * L) := by
    have hq1 : q - 1 < q := by omega
    rw [hblock hq1]
    have h1 : ¬ q - 1 < 4 := by omega
    have h2 : q - 1 ≠ 4 := by omega
    have h3 : ¬ q - 1 + 1 < q := by omega
    simp [hXs, hq1, hXdef, hLdef, smallField, h1, h2, h3]
  -- the chart up to block `q - 1`
  obtain ⟨Φ, c, hc, hΦ, hBC⟩ :=
    FieldGeometry_chain hg0 hgz ω hR hRu hX0 hX4 hXmid (q - 1) (by omega) le_rfl
  set P := chartProd W g E q R ω (q - 1) with hPdef
  have hcc : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  set Ψ : Matrix (Fin W) (Fin W) ℂ := ((c : ℂ)⁻¹) • Pᴴ with hΨdef
  have hΦΨ : Φ * Ψ = 1 := by
    rw [hΨdef, Matrix.mul_smul, hΦ, smul_smul, inv_mul_cancel₀ hcc, one_smul]
  have hΨΦ : Ψ * Φ = 1 := mul_eq_one_comm.mp hΦΨ
  have hΨH : Ψᴴ = ((c : ℂ)⁻¹) • P := by
    rw [hΨdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose]
    congr 1
    simp
  have hΦΨH : Φᴴ * Ψᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hΨΦ, Matrix.conjTranspose_one]
  -- the correction `L` of (9.9) [us:eq:L]
  set w := P *ᵥ v with hw
  have hre : (star w ⬝ᵥ (P *ᵥ (K *ᵥ v) - w)).re = 0 := by
    rw [dotProduct_sub, Complex.sub_re]
    have h2 : star w ⬝ᵥ w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
      simp [dotProduct, Complex.conj_mul', Complex.ofReal_sum]
    rw [h2, Complex.ofReal_re]
    have hn' := hn
    unfold IsGenNormalized at hn'
    rw [hn']
    ring
  obtain ⟨hLskew, hLv⟩ := rotCorr_spec hre
  have hLeq : L = rotCorr w (P *ᵥ (K *ᵥ v) - w) := rfl
  rw [← hLeq] at hLskew hLv
  have hw0 : w ≠ 0 := by
    intro h0
    apply hv
    have h1 : Φᴴ *ᵥ (Ψᴴ *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, hΦΨH, Matrix.one_mulVec]
    rw [← h1, hΨH, Matrix.smul_mulVec, ← hw, h0, smul_zero, Matrix.mulVec_zero]
  -- `Z = Φ⁻¹ L Φ - K` fixes `v*` from the right
  set Z := Ψ * L * Φ - K with hZdef
  have hΦZ : Φ * Z = L * Φ - Φ * K := by
    rw [hZdef, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hΦΨ, Matrix.one_mul]
  have hZv : Zᴴ *ᵥ v = v := by
    have hZH : Zᴴ = -(Φᴴ * (L * Ψᴴ)) + K := by
      rw [hZdef, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        hLskew, hK]
      simp only [Matrix.mul_neg, Matrix.neg_mul, sub_neg_eq_add]
    have h1 : L *ᵥ (Ψᴴ *ᵥ v) = Ψᴴ *ᵥ (K *ᵥ v - v) := by
      rw [hΨH, Matrix.smul_mulVec, Matrix.mulVec_smul, ← hw, hLv hw0,
        Matrix.smul_mulVec, Matrix.mulVec_sub]
    rw [hZH, Matrix.add_mulVec, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      h1, Matrix.mulVec_mulVec, hΦΨH, Matrix.one_mulVec]
    abel
  have hv' : star v ⬝ᵥ v ≠ 0 := FieldGeometry_dot_ne hv
  have hZ : Matrix.vecMulVec v (star v) * Z = Matrix.vecMulVec v (star v) := by
    rw [Matrix.vecMulVec_mul]
    congr 1
    have := Matrix.star_mulVec Zᴴ v
    rw [hZv, Matrix.conjTranspose_conjTranspose] at this
    exact this.symm
  -- the prepared frames: `T_4 ⋯ T_1 S P = G_4 C` with right inverses of `C` on `ran P`
  have hYU : x.1.2 * x.1.1 = x.1.1 := x.2.2.2.2.2.1
  have hUU : x.1.1 * x.1.1 = x.1.1 := x.2.1.2.1
  have hYY : x.1.2 * x.1.2 = x.1.2 := x.2.2.2.1
  set G4 := graphFrame g R with hG4
  set Qv : Matrix (Fin W) (Fin W) ℂ :=
    1 - (star v ⬝ᵥ v)⁻¹ • Matrix.vecMulVec v (star v) with hQv
  set Pr4 := prepMat W g E q ω with hPr4
  obtain ⟨CY, hCY⟩ := FieldGeometry_exists_mul hrY.le
  obtain ⟨Y0, hY0⟩ := FieldGeometry_exists_mul hrY.ge
  obtain ⟨C', hC'⟩ := FieldGeometry_exists_mul hrU.le
  obtain ⟨Y1, hY1⟩ := FieldGeometry_exists_mul hrU.ge
  set CU := CY * x.1.1 with hCUdef
  have hCU : Pr4 * x.1.1 = G4 * CU := by
    rw [← hYU, ← Matrix.mul_assoc, hCY, Matrix.mul_assoc]
  have hQCU : Qv * CU = CU := by
    have h : CU = Qv * C' :=
      FieldGeometry_graph_cancel g R (hCU.symm.trans (hC'.trans (Matrix.mul_assoc _ _ _)))
    rw [h, ← Matrix.mul_assoc, (FieldGeometry_proj hv').2]
  have hPRY : x.1.2 * (x.1.2 * Y0) = x.1.2 * Y0 := by rw [← Matrix.mul_assoc, hYY]
  have hPRU : x.1.1 * (x.1.1 * Y1) = x.1.1 * Y1 := by rw [← Matrix.mul_assoc, hUU]
  have hCRY : CY * (x.1.2 * Y0) = 1 := by
    refine FieldGeometry_graph_cancel g R ?_
    change G4 * _ = G4 * 1
    calc G4 * (CY * (x.1.2 * Y0)) = Pr4 * x.1.2 * x.1.2 * Y0 := by
          rw [← Matrix.mul_assoc, ← hCY]; simp only [Matrix.mul_assoc]
      _ = G4 * (1 : Matrix (Fin W) (Fin W) ℂ) := by
          simp only [Matrix.mul_assoc]
          rw [hPRY, ← Matrix.mul_assoc, ← hY0, Matrix.mul_one]
  have hCRU : CU * (x.1.1 * Y1) = Qv := by
    refine FieldGeometry_graph_cancel g R ?_
    change G4 * _ = G4 * Qv
    calc G4 * (CU * (x.1.1 * Y1)) = Pr4 * x.1.1 * x.1.1 * Y1 := by
          rw [← Matrix.mul_assoc, ← hCU]; simp only [Matrix.mul_assoc]
      _ = G4 * Qv := by
          simp only [Matrix.mul_assoc]
          rw [hPRU, ← Matrix.mul_assoc, ← hY1]
  obtain ⟨hMY, hMU, htr⟩ := FieldGeometry_motion_alg hv' hZ hCRY hPRY hCRU hPRU hQCU
  -- the mixed form `(D - (1 ⊗ (K - L)) T) P = T P M` whenever `C M = Z C`
  have hPq : ∀ m, 0 < m → transferProd g z V m = transferMat g z (V (m - 1)) *
      transferProd g z V (m - 1) := by
    intro m hm
    cases m with
    | zero => omega
    | succ k => rfl
  have hDq : ∀ m, 0 < m → FieldGeometry_dProd g z V Xs m =
      -((g : ℂ)⁻¹ • (!![1, 0; 0, 0] ⊗ₖ Xs (m - 1))) * transferProd g z V (m - 1) +
        transferMat g z (V (m - 1)) * FieldGeometry_dProd g z V Xs (m - 1) := by
    intro m hm
    cases m with
    | zero => omega
    | succ k => rfl
  have key : ∀ (Pr : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
      (C : Matrix (Fin W) (Fin 2 × Fin W) ℂ) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ),
      Pr4 * Pr = G4 * C → C * M = Z * C →
      (D - ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (K - L)) * batchMat W g E q ω) * Pr =
        batchMat W g E q ω * Pr * M := by
    intro Pr C M hPC hCM
    have hB : transferProd g z V 4 * (S * Pr) = G4 * C := by
      rw [← Matrix.mul_assoc]; exact hPC
    obtain ⟨h1, h2⟩ := hBC (S * Pr) C hB
    rw [← hVdef] at h1 h2
    have hlast := FieldGeometry_last_id hg0 z (V (q - 1)) (chartR W g E q R ω (q - 1)) L
    have hcomm := FieldGeometry_transferMat_comm g z (V (q - 1)) K
    set T := transferMat g z (V (q - 1)) with hT
    set G := graphFrame g (chartR W g E q R ω (q - 1)) with hG
    set A : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K
      with hA
    set B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ L
      with hBdef
    have h0 : -((g : ℂ)⁻¹ • (!![1, 0; 0, 0] ⊗ₖ Xs (q - 1))) + (T * A - A * T) =
        (g : ℂ)⁻¹ • (!![1, 0; 0, 0] ⊗ₖ
          (L * (V (q - 1) - ((g : ℂ) ^ 2) • chartR W g E q R ω (q - 1)) -
            (V (q - 1) - ((g : ℂ) ^ 2) • chartR W g E q R ω (q - 1)) * L)) := by
      rw [hcomm, hXlast]
      simp only [FieldGeometry_kron_sub, smul_sub]
      abel
    have hinner : (FieldGeometry_dProd g z V Xs q -
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (K - L)) * transferProd g z V q) * (S * Pr) =
        transferProd g z V q * (S * Pr) * M := by
      have hPq' := hPq q (by omega)
      have hDq' := hDq q (by omega)
      rw [FieldGeometry_kron_sub, ← hA, ← hBdef, hPq', hDq']
      calc (-((g : ℂ)⁻¹ • (!![1, 0; 0, 0] ⊗ₖ Xs (q - 1))) * transferProd g z V (q - 1) +
            T * FieldGeometry_dProd g z V Xs (q - 1) - (A - B) * (T * transferProd g z V (q - 1)))
            * (S * Pr)
          = (-((g : ℂ)⁻¹ • (!![1, 0; 0, 0] ⊗ₖ Xs (q - 1))) + (T * A - A * T)) * (G * Φ * C) +
              B * (T * (G * Φ * C)) - T * (G * Φ * K * C) := by
            rw [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc,
              Matrix.mul_assoc, Matrix.mul_assoc, h1, h2]
            noncomm_ring
        _ = (T * G * L - B * (T * G)) * Φ * C + B * (T * (G * Φ * C)) - T * (G * Φ * K * C) := by
            rw [h0, ← hlast]
            simp only [Matrix.mul_assoc]
        _ = T * G * (Φ * Z) * C := by
            rw [hΦZ]
            simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
            abel
        _ = _ := by
            rw [Matrix.mul_assoc _ _ (S * Pr), h1]
            simp only [Matrix.mul_assoc]
            rw [hCM]
    have hS := FieldGeometry_freeConj_comm (K - L)
    calc (D - ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (K - L)) * batchMat W g E q ω) * Pr
        = Sᴴ * ((FieldGeometry_dProd g z V Xs q -
            ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (K - L)) * transferProd g z V q) * (S * Pr)) := by
          have e1 : ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (K - L)) * (Sᴴ * transferProd g z V q * S) =
              Sᴴ * (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (K - L)) * transferProd g z V q) * S := by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hS, Matrix.mul_assoc Sᴴ]
          rw [hDdef, hbatch, ← hVdef, e1]
          noncomm_ring
      _ = batchMat W g E q ω * Pr * M := by
          rw [hinner, hbatch, ← hVdef]
          simp only [Matrix.mul_assoc]
  exact ⟨x.1.1 * Y1 * Z * CU, x.1.2 * Y0 * Z * CY, key _ _ _ hCU hMU, key _ _ _ hCY hMY, htr⟩

/-- Lemma 9.2 [su:lem:field-geometry]: under the prepared chart, with `R_5, …, R_{q-1}` defined,
`K* = -K` and (9.8) [su:eq:generator-normalization], every field `Y` whose value at `ω` is `X` of
(9.10) [us:eq:physical] in standard coordinates satisfies (9.11) [su:eq:field-geometry], that is
(8.34) [up:eq:angular-geometry] at `ω` with the skew-Hermitian `K_out = K - L`. -/
theorem field_geometry {W q : ℕ} {g E : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) (hq : 7 ≤ q)
    (x : IsoFlag W) (ω : Ω W q) {R : Matrix (Fin W) (Fin W) ℂ} {v : Fin W → ℂ}
    (hprep : IsPrepChart W g E q x ω R v)
    (hRu : ∀ j, 5 ≤ j → j ≤ q - 1 → IsUnit (chartR W g E q R ω j))
    {K : Matrix (Fin W) (Fin W) ℂ} (hK : Kᴴ = -K) (hn : IsGenNormalized W g E q R v K ω)
    {Y : Ω W q → Ω W q} (hY : Y ω = hermCoord W q (smallField W g E q R v K ω)) :
    (K - smallCorr W g E q R v K ω)ᴴ = -(K - smallCorr W g E q R v K ω) ∧
      FlagFieldGeom W g E q x Y ω (K - smallCorr W g E q R v K ω) := by
  set L := smallCorr W g E q R v K ω with hLdef
  set P := chartProd W g E q R ω (q - 1) with hPdef
  have hre : (star (P *ᵥ v) ⬝ᵥ (P *ᵥ (K *ᵥ v) - P *ᵥ v)).re = 0 := by
    rw [dotProduct_sub, Complex.sub_re]
    have h2 : star (P *ᵥ v) ⬝ᵥ (P *ᵥ v) = ((∑ i, ‖(P *ᵥ v) i‖ ^ 2 : ℝ) : ℂ) := by
      simp [dotProduct, Complex.conj_mul', Complex.ofReal_sum]
    rw [h2, Complex.ofReal_re]
    have hn' := hn
    unfold IsGenNormalized at hn'
    rw [hn']
    ring
  have hLskew : Lᴴ = -L := (rotCorr_spec hre).1
  have hA : (K - L)ᴴ = -(K - L) := by
    rw [Matrix.conjTranspose_sub, hK, hLskew]
    abel
  refine ⟨hA, ?_⟩
  obtain ⟨D, hD, MU, MY, hMU, hMY, htr⟩ := smallField_motion hg hg1 hq x ω hprep hRu hK hn
  have hAskew : ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (K - L))ᴴ =
      -((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (K - L)) := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, hA]
    ext ⟨a, i⟩ ⟨b, j⟩
    simp only [Matrix.kroneckerMap_apply, Matrix.neg_apply, Matrix.sub_apply]
    ring
  have hu : IsUnit (batchMat W g E q ω) := by
    rw [Matrix.isUnit_iff_isUnit_det, (batchMat_mem_isoGroup W g E q ω).2]
    exact isUnit_one
  have hJ : ∀ η, (batchMat W g E q η)ᴴ * isoJ W * batchMat W g E q η = isoJ W :=
    fun η => (batchMat_mem_isoGroup W g E q η).1
  obtain ⟨⟨hUh, hUU, -, -⟩, hYh, hYY, -, -, -⟩ := x.2
  obtain ⟨hU1, hU2⟩ := hasLineDerivAt_flagProj_logVol_of_rot hD hu hAskew hUh hUU hMU
  obtain ⟨hY1, hY2⟩ := hasLineDerivAt_flagProj_logVol_of_rot hD hu hAskew hYh hYY hMY
  unfold FlagFieldGeom
  rw [hY]
  constructor
  · unfold HasLineDerivAt at hU2 hY2 ⊢
    have h := hY2.sub hU2
    rw [htr] at h
    exact h
  · have hfun : (fun η : Ω W q => ((flagAct (batchMat W g E q η) x : IsoFlag W) :
        Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) =
        fun η => (flagProj (batchMat W g E q η) x.1.1, flagProj (batchMat W g E q η) x.1.2) := by
      funext η
      exact flagAct_coe (hJ η) x
    have hω := flagAct_coe (hJ ω) x
    rw [hfun, hω]
    unfold HasLineDerivAt at hU1 hY1 ⊢
    exact hU1.prodMk hY1

end LSBA
