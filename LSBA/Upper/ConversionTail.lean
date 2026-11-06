import LSBA.Gauss.ScalarDensity
import LSBA.Volume.LocalComparison

/-!
# Tail of resolvent blocks under scalar averaging

`μ{h < ‖G(x, y)‖} ≤ (4/√π) W²/(c h)` for `G = (K₀ + c · diag V − E)⁻¹` with GUE blocks, by
averaging the scalar parts of the blocks x and y: the tail behind (8.7) [eq:c-apriori].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The upper-left block of the inverse of a block matrix with invertible lower-right block is
the inverse of the Schur complement. -/
private lemma convTail_toBlocks₁₁_inv {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    (hD : IsUnit D.det) :
    ((Matrix.fromBlocks A B C D)⁻¹).toBlocks₁₁ = (A - B * D⁻¹ * C)⁻¹ := by
  let : Invertible D := Matrix.invertibleOfIsUnitDet D hD
  have hDinv : (⅟D : Matrix n n ℂ) = D⁻¹ := Matrix.invOf_eq_nonsing_inv D
  by_cases hT : IsUnit (A - B * D⁻¹ * C).det
  · let : Invertible (A - B * ⅟D * C) := by
      rw [hDinv]; exact Matrix.invertibleOfIsUnitDet _ hT
    let : Invertible (Matrix.fromBlocks A B C D) := Matrix.fromBlocks₂₂Invertible A B C D
    have h := Matrix.invOf_fromBlocks₂₂_eq A B C D
    rw [Matrix.invOf_eq_nonsing_inv] at h
    rw [h, Matrix.toBlocks_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv, hDinv]
  · have hdet : (Matrix.fromBlocks A B C D).det = D.det * (A - B * D⁻¹ * C).det := by
      rw [Matrix.det_fromBlocks₂₂, hDinv]
    have hU : ¬ IsUnit (Matrix.fromBlocks A B C D).det := by
      rw [hdet]
      intro h
      exact hT (isUnit_of_mul_isUnit_right h)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hU, Matrix.nonsing_inv_apply_not_isUnit _ hT]
    ext i j
    simp [Matrix.toBlocks₁₁]

/-- Schur complement along the indices with `p`: for Hermitian `B₀` whose block on the complement
is invertible, the `p`-block of `(B₀ + s P)⁻¹` is `(s - A)⁻¹` for one Hermitian `A`, for every
real `s`, where `P` is the diagonal projection onto the `p`-indices. -/
private lemma convTail_schur {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → Prop)
    [DecidablePred p] (B₀ : Matrix ι ι ℂ) (hB : B₀.IsHermitian)
    (hr : (B₀.submatrix (Subtype.val : {i // ¬ p i} → ι) Subtype.val).det ≠ 0) :
    ∃ A : Matrix {i // p i} {i // p i} ℂ, A.IsHermitian ∧ ∀ s : ℝ,
      ((B₀ + (s : ℂ) • Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0))⁻¹).submatrix
        (Subtype.val : {i // p i} → ι) Subtype.val =
      ((s : ℂ) • (1 : Matrix {i // p i} {i // p i} ℂ) - A)⁻¹ := by
  set Bkk : Matrix {i // p i} {i // p i} ℂ := B₀.submatrix Subtype.val Subtype.val with hBkk
  set Bkr : Matrix {i // p i} {i // ¬ p i} ℂ := B₀.submatrix Subtype.val Subtype.val with hBkr
  set Brk : Matrix {i // ¬ p i} {i // p i} ℂ := B₀.submatrix Subtype.val Subtype.val with hBrk
  set Brr : Matrix {i // ¬ p i} {i // ¬ p i} ℂ := B₀.submatrix Subtype.val Subtype.val with hBrr
  have hBrk' : Brk = Bkrᴴ := by
    rw [hBrk, hBkr, Matrix.conjTranspose_submatrix, hB.eq]
  have hherm : (Bkk - Bkr * Brr⁻¹ * Brk).IsHermitian := by
    refine (hB.submatrix _).sub ?_
    rw [hBrk']
    exact Matrix.isHermitian_mul_mul_conjTranspose Bkr ((hB.submatrix _).inv)
  refine ⟨-(Bkk - Bkr * Brr⁻¹ * Brk), hherm.neg, fun s => ?_⟩
  set f : {i // p i} ⊕ {i // ¬ p i} ≃ ι := Equiv.sumCompl p with hf
  set M : Matrix ι ι ℂ :=
    B₀ + (s : ℂ) • Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0) with hM
  have hN : M.submatrix f f = Matrix.fromBlocks (Bkk + (s : ℂ) • 1) Bkr Brk Brr := by
    ext (i | i) (j | j)
    · simp [hM, hf, hBkk, Matrix.diagonal_apply, Matrix.one_apply, Subtype.ext_iff, i.2]
    · have hij : (i : ι) ≠ j := fun h => j.2 (h ▸ i.2)
      simp [hM, hf, hBkr, hij]
    · have hij : (i : ι) ≠ j := fun h => i.2 (h ▸ j.2)
      simp [hM, hf, hBrk, hij]
    · simp [hM, hf, hBrr, Matrix.diagonal_apply, i.2]
  have hdet : IsUnit Brr.det := isUnit_iff_ne_zero.mpr hr
  have h1 := convTail_toBlocks₁₁_inv (Bkk + (s : ℂ) • 1) Bkr Brk Brr hdet
  rw [← hN, Matrix.inv_submatrix_equiv] at h1
  have h2 : (M⁻¹).submatrix (Subtype.val : {i // p i} → ι) Subtype.val =
      ((M⁻¹).submatrix f f).toBlocks₁₁ := by
    ext i j
    simp [Matrix.toBlocks₁₁, hf]
  rw [h2, h1]
  congr 1
  rw [neg_sub]
  abel

/-- Summing a function supported on the range of an injective map. -/
private lemma convTail_sum_extend {γ δ M : Type*} [Fintype γ] [Fintype δ] [AddCommMonoid M]
    {g : γ → δ} (hg : Function.Injective g) (φ : δ → M) (hφ : ∀ j, j ∉ Set.range g → φ j = 0) :
    ∑ j', φ j' = ∑ j, φ (g j) := by
  rw [← Finset.sum_image (f := φ) (s := Finset.univ) (g := g) (fun a _ b _ hab => hg hab)]
  refine (Finset.sum_subset (Finset.subset_univ _) fun j' _ hj' => hφ j' ?_).symm
  intro hr
  obtain ⟨a, ha⟩ := hr
  exact hj' (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩)

/-- A submatrix on injective index maps has operator norm at most that of the matrix. -/
private lemma convTail_norm_submatrix_le {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [Fintype δ] (X : Matrix β δ ℂ) {f : α → β} {g : γ → δ} (hf : Function.Injective f)
    (hg : Function.Injective g) : ‖X.submatrix f g‖ ≤ ‖X‖ := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  set u : EuclideanSpace ℂ δ := WithLp.toLp 2 (Function.extend g v.ofLp 0) with hu
  have hug : ∀ j, u.ofLp (g j) = v.ofLp j := fun j => hg.extend_apply _ _ j
  have hu0 : ∀ j, j ∉ Set.range g → u.ofLp j = 0 := fun j hj =>
    Function.extend_apply' _ _ _ (by simpa using hj)
  have h := Matrix.l2_opNorm_mulVec X u
  have hnu : ‖u‖ = ‖v‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    rw [convTail_sum_extend hg (fun j => ‖u.ofLp j‖ ^ 2)
      (fun j hj => by simp [hu0 j hj])]
    simp [hug]
  have hentry : ∀ i : α, (Matrix.toEuclideanLin (𝕜 := ℂ) (X.submatrix f g)) v i =
      (X *ᵥ u.ofLp) (f i) := by
    intro i
    change ((X.submatrix f g) *ᵥ v.ofLp) i = _
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
    rw [convTail_sum_extend hg (fun j => X (f i) j * u.ofLp j)
      (fun j hj => by simp [hu0 j hj])]
    simp [hug]
  have key : ‖(Matrix.toEuclideanLin (𝕜 := ℂ) (X.submatrix f g)) v‖ ≤
      ‖(EuclideanSpace.equiv β ℂ).symm (X *ᵥ u)‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    calc _ = ∑ i : α, ‖(X *ᵥ u.ofLp) (f i)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hentry i]
      _ = ∑ b ∈ Finset.univ.image f, ‖(X *ᵥ u.ofLp) b‖ ^ 2 := by
          rw [Finset.sum_image (fun a _ b _ hab => hf hab)]
      _ ≤ ∑ b : β, ‖(X *ᵥ u.ofLp) b‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun b _ _ => by positivity
      _ = _ := rfl
  calc _ ≤ _ := key
    _ ≤ _ := h
    _ = _ := by rw [hnu]

/-- Moving the sample along `scalarDir W n S` adds a multiple of the projection onto the blocks of
`S` to `K₀ + c · diag V - E`. -/
private lemma convTail_shift {W n : ℕ} (K₀ : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) (c E : ℝ)
    (S : Finset (Fin n)) (ω : Ω W n) (t : ℝ) :
    K₀ + (c : ℂ) • blockDiagOp (gueBlock W n (ω + t • scalarDir W n S)) -
        (E : ℂ) • (1 : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) =
      (K₀ + (c : ℂ) • blockDiagOp (gueBlock W n ω) -
          (E : ℂ) • (1 : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ)) +
        ((c * (t / ((W : ℝ) * Real.sqrt S.card)) : ℝ) : ℂ) •
          Matrix.diagonal (fun i : Fin n × Fin W => if i.1 ∈ S then (1 : ℂ) else 0) := by
  have h1 : blockDiagOp (gueBlock W n (ω + t • scalarDir W n S)) =
      blockDiagOp (gueBlock W n ω) + ((t / ((W : ℝ) * Real.sqrt S.card) : ℝ) : ℂ) •
        Matrix.diagonal (fun i : Fin n × Fin W => if i.1 ∈ S then (1 : ℂ) else 0) := by
    ext ⟨a, α⟩ ⟨b, β⟩
    by_cases hab : a = b
    · subst hab
      by_cases hS : a ∈ S
      · by_cases hαβ : α = β
        · subst hαβ
          simp [blockDiagOp, gueBlock_add_smul_scalarDir, hS]
        · simp [blockDiagOp, gueBlock_add_smul_scalarDir, hS, hαβ]
      · simp [blockDiagOp, gueBlock_add_smul_scalarDir, hS, Matrix.diagonal_apply]
    · simp [blockDiagOp, hab]
  rw [h1, smul_add, smul_smul]
  push_cast
  abel


/-- `M + κ t` is invertible for almost every Gaussian `t`, for `κ ≠ 0`. -/
private lemma convTail_ae_det_line {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℂ)
    {κ : ℝ} (hκ : κ ≠ 0) :
    ∀ᵐ t ∂(gaussianReal 0 1),
      (M + ((κ * t : ℝ) : ℂ) • (1 : Matrix m m ℂ)).det ≠ 0 := by
  have hpoly : (-M).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hfin : {x : ℂ | (-M).charpoly.IsRoot x}.Finite := Polynomial.finite_setOfPred_isRoot hpoly
  let f : ℝ → ℂ := fun t => ((κ * t : ℝ) : ℂ)
  have hf : Function.Injective f := by
    intro t t' h
    have h' : κ * t = κ * t' := Complex.ofReal_injective h
    exact mul_left_cancel₀ hκ h'
  have hfin' : (f ⁻¹' {x : ℂ | (-M).charpoly.IsRoot x}).Finite := hfin.preimage hf.injOn
  have hnull : gaussianReal 0 1 (f ⁻¹' {x : ℂ | (-M).charpoly.IsRoot x}) = 0 :=
    gaussianReal_absolutelyContinuous 0 one_ne_zero (hfin'.measure_zero volume)
  rw [measure_eq_zero_iff_ae_notMem] at hnull
  filter_upwards [hnull] with t ht h0
  apply ht
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Polynomial.IsRoot.def]
  rw [Matrix.eval_charpoly, ← h0]
  congr 1
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, sub_neg_eq_add, add_comm]


/-- The block of a matrix on the indices outside the blocks of `S`. -/
private def convTail_compl {W n : ℕ} (S : Finset (Fin n))
    (X : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) :
    Matrix {i : Fin n × Fin W // i.1 ∉ S} {i : Fin n × Fin W // i.1 ∉ S} ℂ :=
  X.submatrix Subtype.val Subtype.val

/-- Adding a multiple of the projection onto the blocks of `Sᶜ` adds that multiple of the
identity to the block outside `S`. -/
private lemma convTail_compl_add {W n : ℕ} (S : Finset (Fin n))
    (X : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) (z : ℂ) :
    convTail_compl S (X + z • Matrix.diagonal
        (fun i : Fin n × Fin W => if i.1 ∈ Sᶜ then (1 : ℂ) else 0)) =
      convTail_compl S X + z • (1 : Matrix {i : Fin n × Fin W // i.1 ∉ S}
        {i : Fin n × Fin W // i.1 ∉ S} ℂ) := by
  ext p q
  simp only [convTail_compl, Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.diagonal_apply, Matrix.one_apply, Subtype.ext_iff, Finset.mem_compl, p.2,
    not_false_eq_true, ite_true, smul_eq_mul]

/-- Each entry of a GUE block is a measurable function of the sample. -/
private lemma convTail_measurable_gueBlock_apply {W n : ℕ} (a : Fin n) (α β : Fin W) :
    Measurable fun ω : Ω W n => gueBlock W n ω a α β := by
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs
  · fun_prop
  · fun_prop
  · fun_prop

/-- The matrix `K₀ + c · diag V(ω) - z` is a measurable function of the sample. -/
private lemma convTail_measurable_mat {W n : ℕ}
    (K₀ : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) (c : ℝ) (z : ℂ) :
    Measurable fun ω : Ω W n => K₀ + (c : ℂ) • blockDiagOp (gueBlock W n ω) -
      z • (1 : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) := by
  refine Measurable.of_eval_matrix _ fun p q => ?_
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, blockDiagOp, Matrix.of_apply,
    smul_eq_mul]
  by_cases h : p.1 = q.1
  · simp only [h, ite_true]
    have := convTail_measurable_gueBlock_apply (W := W) (n := n) q.1 p.2 q.2
    fun_prop
  · simp only [h, ite_false]
    fun_prop

/-- Almost surely the block of `K₀ + c · diag V - E` on the blocks outside `S` is invertible. -/
private lemma convTail_ae_det_compl {W n : ℕ} (hW : 1 ≤ W)
    (K₀ : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) {c : ℝ} (hc : c ≠ 0) (E : ℝ)
    (S : Finset (Fin n)) :
    ∀ᵐ ω ∂(μ W n),
      (convTail_compl S (K₀ + (c : ℂ) • blockDiagOp (gueBlock W n ω) -
          (E : ℂ) • (1 : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ))).det ≠ 0 := by
  rcases Sᶜ.eq_empty_or_nonempty with hT | hT
  · refine ae_of_all _ fun ω => ?_
    have hE : IsEmpty {i : Fin n × Fin W // i.1 ∉ S} := by
      refine ⟨fun i => ?_⟩
      have : i.1.1 ∈ Sᶜ := Finset.mem_compl.mpr i.2
      rw [hT] at this
      exact absurd this (Finset.notMem_empty _)
    rw [Matrix.det_isEmpty]
    exact one_ne_zero
  set e : Ω W n := scalarDir W n Sᶜ with he_def
  have he : ∑ p, e p ^ 2 = 1 := sum_sq_scalarDir hW hT
  set Bad : Set (Ω W n) := {ω | (convTail_compl S (K₀ + (c : ℂ) • blockDiagOp (gueBlock W n ω) -
      (E : ℂ) • (1 : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ))).det = 0}
    with hBad_def
  have hsub : Measurable fun ω : Ω W n => convTail_compl S (K₀ + (c : ℂ) •
      blockDiagOp (gueBlock W n ω) - (E : ℂ) • (1 : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ)) := by
    refine Measurable.of_eval_matrix _ fun p q => ?_
    exact (convTail_measurable_mat K₀ c (E : ℂ)).eval_matrix (i := p.1) (j := q.1)
  have hBad : MeasurableSet Bad :=
    ((continuous_id.matrix_det).measurable.comp hsub) (measurableSet_singleton 0)
  have hline := lintegral_stdGauss_line e he (F := Bad.indicator 1)
    (measurable_one.indicator hBad)
  rw [ae_iff]
  have hset : {ω | ¬ (convTail_compl S (K₀ + (c : ℂ) • blockDiagOp (gueBlock W n ω) -
      (E : ℂ) • (1 : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ))).det ≠ 0} = Bad := by
    simp [hBad_def]
  rw [hset, ← lintegral_indicator_one hBad]
  change ∫⁻ ω, Bad.indicator 1 ω ∂(stdGauss (Fin n × Fin W × Fin W)) = 0
  rw [hline]
  have hκ : c / ((W : ℝ) * Real.sqrt (Sᶜ.card : ℕ)) ≠ 0 := by
    have hWp : (0 : ℝ) < W := by exact_mod_cast hW
    have hSp : (0 : ℝ) < (Sᶜ.card : ℕ) := by exact_mod_cast hT.card_pos
    positivity
  have hinner : ∀ ω : Ω W n, ∫⁻ t, Bad.indicator 1
      (ω - (∑ i, ω i * e i) • e + t • e) ∂(gaussianReal 0 1) = 0 := fun ω => by
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [convTail_ae_det_line
      (convTail_compl S (K₀ + (c : ℂ) • blockDiagOp (gueBlock W n (ω - (∑ i, ω i * e i) • e)) -
          (E : ℂ) • (1 : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ))) hκ] with t ht
    refine Set.indicator_of_notMem ?_ _
    intro hmem
    apply ht
    simp only [hBad_def, Set.mem_ofPred_eq] at hmem
    refine Eq.trans ?_ hmem
    rw [convTail_shift, convTail_compl_add,
      show c / ((W : ℝ) * Real.sqrt (Sᶜ.card : ℕ)) * t =
        c * (t / ((W : ℝ) * Real.sqrt (Sᶜ.card : ℕ))) by ring]
  simp [hinner]

/-- The block of a matrix on the indices in the blocks of `S`. -/
private def convTail_block {W n : ℕ} (S : Finset (Fin n))
    (X : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) :
    Matrix {i : Fin n × Fin W // i.1 ∈ S} {i : Fin n × Fin W // i.1 ∈ S} ℂ :=
  X.submatrix Subtype.val Subtype.val

/-- The compression of a matrix to the blocks `x` and `y` of `S` has operator norm at most that of
the compression to all blocks of `S`. -/
private lemma convTail_norm_blockOf_le {W n : ℕ} (X : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ)
    (S : Finset (Fin n)) {x y : Fin n} (hx : x ∈ S) (hy : y ∈ S) :
    ‖blockOf X x y‖ ≤ ‖convTail_block S X‖ := by
  have e : blockOf X x y = (convTail_block S X).submatrix
      (fun α : Fin W => (⟨(x, α), hx⟩ : {i : Fin n × Fin W // i.1 ∈ S}))
      (fun β : Fin W => (⟨(y, β), hy⟩ : {i : Fin n × Fin W // i.1 ∈ S})) := rfl
  rw [e]
  refine convTail_norm_submatrix_le _ ?_ ?_
  · intro a b hab
    exact congrArg (fun i : {i : Fin n × Fin W // i.1 ∈ S} => i.1.2) hab
  · intro a b hab
    exact congrArg (fun i : {i : Fin n × Fin W // i.1 ∈ S} => i.1.2) hab

/-- The number of indices in the blocks of `S` is `|S| W`. -/
private lemma convTail_card {W n : ℕ} (S : Finset (Fin n)) :
    Fintype.card {i : Fin n × Fin W // i.1 ∈ S} = S.card * W := by
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun i : Fin n × Fin W => i.1 ∈ S) = S ×ˢ Finset.univ := by
    ext i
    simp
  rw [this, Finset.card_product, Finset.card_univ, Fintype.card_fin]

/-- Along the line `ω' + t • scalarDir W n S`, the Gaussian measure of `t` with a large block
`(x, y)` of the resolvent is at most the scalar density bound of `|S| W` eigenvalues, when the
block of `K₀ + c · diag V(ω') - E` outside `S` is invertible. -/
private lemma convTail_line_le {W n : ℕ} (hW : 1 ≤ W) {c : ℝ} (hc : 0 < c)
    (K₀ : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) (hK₀ : K₀.IsHermitian) (E : ℝ)
    {S : Finset (Fin n)} (hS : S.Nonempty) {x y : Fin n} (hx : x ∈ S) (hy : y ∈ S) {h : ℝ}
    (hh : 0 < h) (ω' : Ω W n)
    (hr : (convTail_compl S (K₀ + (c : ℂ) • blockDiagOp (gueBlock W n ω') -
      (E : ℂ) • (1 : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ))).det ≠ 0) :
    gaussianReal 0 1 {t : ℝ | h < ‖blockOf (resolventMat (K₀ + (c : ℂ) •
        blockDiagOp (gueBlock W n (ω' + t • scalarDir W n S))) E) x y‖} ≤
      ENNReal.ofReal (2 * ((S.card * W : ℕ) : ℝ) /
        (h * |c / ((W : ℝ) * Real.sqrt S.card)| * Real.sqrt (2 * π))) := by
  have hWp : (0 : ℝ) < W := by exact_mod_cast hW
  have hSp : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  set c' : ℝ := c / ((W : ℝ) * Real.sqrt S.card) with hc'_def
  have hc' : c' ≠ 0 := by positivity
  set B₀ : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ :=
    K₀ + (c : ℂ) • blockDiagOp (gueBlock W n ω') -
      (E : ℂ) • (1 : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) with hB₀_def
  have hB₀ : B₀.IsHermitian := by
    have h1 : ((c : ℂ) • blockDiagOp (gueBlock W n ω')).IsHermitian := by
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_smul, (blockDiagOp_isHermitian (gueBlock_isHermitian W n ω')).eq]
      simp
    have h2 : ((E : ℂ) • (1 : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ)).IsHermitian := by
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
      simp
    exact (hK₀.add h1).sub h2
  obtain ⟨A, hA, hAeq⟩ := convTail_schur (fun i : Fin n × Fin W => i.1 ∈ S) B₀ hB₀ hr
  have hkey : ∀ t : ℝ, ‖blockOf (resolventMat (K₀ + (c : ℂ) •
      blockDiagOp (gueBlock W n (ω' + t • scalarDir W n S))) E) x y‖ ≤
      ‖(((t * c' : ℝ) : ℂ) • (1 : Matrix {i : Fin n × Fin W // i.1 ∈ S}
        {i : Fin n × Fin W // i.1 ∈ S} ℂ) - A)⁻¹‖ := by
    intro t
    have e1 : resolventMat (K₀ + (c : ℂ) • blockDiagOp (gueBlock W n (ω' + t • scalarDir W n S)))
        (E : ℂ) = (B₀ + ((c * (t / ((W : ℝ) * Real.sqrt S.card)) : ℝ) : ℂ) •
          Matrix.diagonal (fun i : Fin n × Fin W => if i.1 ∈ S then (1 : ℂ) else 0))⁻¹ := by
      unfold resolventMat
      rw [convTail_shift]
    have e2 := hAeq (c * (t / ((W : ℝ) * Real.sqrt S.card)))
    have e3 : c * (t / ((W : ℝ) * Real.sqrt S.card)) = t * c' := by
      rw [hc'_def]; ring
    rw [e3] at e1 e2
    refine (convTail_norm_blockOf_le _ S hx hy).trans (le_of_eq ?_)
    rw [e1]
    exact congrArg norm e2
  have hcard : Fintype.card {i : Fin n × Fin W // i.1 ∈ S} = S.card * W := convTail_card S
  calc gaussianReal 0 1 {t : ℝ | h < ‖blockOf (resolventMat (K₀ + (c : ℂ) •
        blockDiagOp (gueBlock W n (ω' + t • scalarDir W n S))) E) x y‖}
      ≤ gaussianReal 0 1 {t : ℝ | h < ‖(((t * c' : ℝ) : ℂ) • (1 : Matrix
          {i : Fin n × Fin W // i.1 ∈ S} {i : Fin n × Fin W // i.1 ∈ S} ℂ) - A)⁻¹‖} :=
        measure_mono fun t ht => lt_of_lt_of_le ht (hkey t)
    _ ≤ ENNReal.ofReal (2 * Fintype.card {i : Fin n × Fin W // i.1 ∈ S} /
          (h * |c'| * Real.sqrt (2 * π))) := gaussianReal_norm_inv_gt_le A hA hc' hh
    _ = _ := by rw [hcard]

/-- The constant of the tail bound: `2 |S| W / (h (c/(W √|S|)) √(2π)) ≤ (4/√π) W²/(c h)` for
`1 ≤ |S| ≤ 2`. -/
private lemma convTail_const {W : ℕ} (hW : 1 ≤ W) {c h : ℝ} (hc : 0 < c) (hh : 0 < h) {s : ℕ}
    (hs1 : 1 ≤ s) (hs2 : s ≤ 2) :
    2 * ((s * W : ℕ) : ℝ) / (h * |c / ((W : ℝ) * Real.sqrt s)| * Real.sqrt (2 * π)) ≤
      4 / Real.sqrt π * (W : ℝ) ^ 2 / (c * h) := by
  have hWp : (0 : ℝ) < W := by exact_mod_cast hW
  have hs1' : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hs2' : (s : ℝ) ≤ 2 := by exact_mod_cast hs2
  have hr0 : 0 < Real.sqrt s := Real.sqrt_pos.mpr (by linarith)
  have hr2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt (by linarith)
  have hrle : Real.sqrt s ≤ Real.sqrt 2 := Real.sqrt_le_sqrt hs2'
  have h20 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hsr : (s : ℝ) * Real.sqrt s ≤ 2 * Real.sqrt 2 := by
    calc (s : ℝ) * Real.sqrt s = Real.sqrt s ^ 2 * Real.sqrt s := by rw [hr2]
      _ = Real.sqrt s ^ 3 := by ring
      _ ≤ Real.sqrt 2 ^ 3 := pow_le_pow_left₀ hr0.le hrle 3
      _ = 2 * Real.sqrt 2 := by rw [pow_succ, h22]
  have hcpos : 0 < c / ((W : ℝ) * Real.sqrt s) := by positivity
  rw [abs_of_pos hcpos, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Nat.cast_mul]
  have e1 : 2 * ((s : ℝ) * W) / (h * (c / ((W : ℝ) * Real.sqrt s)) *
      (Real.sqrt 2 * Real.sqrt π)) =
      ((s : ℝ) * Real.sqrt s * Real.sqrt 2) * ((W : ℝ) ^ 2 / (Real.sqrt π * (c * h))) := by
    field_simp
    nlinarith [h22]
  have e2 : 4 / Real.sqrt π * (W : ℝ) ^ 2 / (c * h) =
      4 * ((W : ℝ) ^ 2 / (Real.sqrt π * (c * h))) := by
    field_simp
  rw [e1, e2]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  calc (s : ℝ) * Real.sqrt s * Real.sqrt 2 ≤ 2 * Real.sqrt 2 * Real.sqrt 2 :=
        mul_le_mul_of_nonneg_right hsr h20.le
    _ = 4 := by nlinarith [h22]

/-- Adding a multiple of the projection onto the blocks of `S` does not change the block outside
`S`. -/
private lemma convTail_compl_add_proj {W n : ℕ} (S : Finset (Fin n))
    (X : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) (z : ℂ) :
    convTail_compl S (X + z • Matrix.diagonal
        (fun i : Fin n × Fin W => if i.1 ∈ S then (1 : ℂ) else 0)) = convTail_compl S X := by
  ext p q
  simp [convTail_compl, Matrix.diagonal_apply, p.2]

/-- Measurability of the block `(x, y)` of a matrix-valued function. -/
private lemma convTail_measurable_blockOf {W n : ℕ} (x y : Fin n) :
    Measurable fun X : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ => blockOf X x y := by
  refine Measurable.of_eval_matrix _ fun α β => ?_
  exact measurable_id.eval_matrix (i := (x, α)) (j := (y, β))

/-- Tail of a block of the resolvent under scalar Gaussian averaging (proof of (8.7)
[eq:c-apriori]): `P(‖G(x, y)‖ > h) ≤ (4/√π) W² / (c h)` for `K₀ + c · diag(V_a)`. -/
theorem resolvent_block_tail_le {W n : ℕ} {c : ℝ} (hc : 0 < c)
    (K₀ : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) (hK₀ : K₀.IsHermitian) (E : ℝ)
    (x y : Fin n) {h : ℝ} (hh : 0 < h) :
    (μ W n) {ω | h < ‖blockOf (resolventMat (K₀ + (c : ℂ) • blockDiagOp (gueBlock W n ω)) E) x y‖} ≤
      ENNReal.ofReal (4 / Real.sqrt π * (W : ℝ) ^ 2 / (c * h)) := by
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · have hz : ∀ M : Matrix (Fin 0) (Fin 0) ℂ, ‖M‖ = 0 := fun M => by
      rw [Subsingleton.elim M 0, norm_zero]
    have hempty : {ω : Ω 0 n | h < ‖blockOf (resolventMat (K₀ + (c : ℂ) •
        blockDiagOp (gueBlock 0 n ω)) E) x y‖} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      rw [hz]
      exact hh.le
    rw [hempty]
    simp
  set S : Finset (Fin n) := {x, y} with hS_def
  have hx : x ∈ S := by simp [hS_def]
  have hy : y ∈ S := by simp [hS_def]
  have hS : S.Nonempty := ⟨x, hx⟩
  have hcard : S.card ≤ 2 := Finset.card_le_two
  set e : Ω W n := scalarDir W n S with he_def
  have he : ∑ p, e p ^ 2 = 1 := sum_sq_scalarDir hW hS
  set Ev : Set (Ω W n) := {ω | h < ‖blockOf (resolventMat (K₀ + (c : ℂ) •
    blockDiagOp (gueBlock W n ω)) E) x y‖} with hEv_def
  have hEv : MeasurableSet Ev :=
    measurableSet_lt measurable_const (continuous_norm.measurable.comp
      ((convTail_measurable_blockOf x y).comp (measurable_resolventMat_gueBlock K₀ c (E : ℂ))))
  set β : ℝ≥0∞ := ENNReal.ofReal (2 * ((S.card * W : ℕ) : ℝ) /
    (h * |c / ((W : ℝ) * Real.sqrt S.card)| * Real.sqrt (2 * π))) with hβ_def
  have hline := lintegral_stdGauss_line e he (F := Ev.indicator 1) (measurable_one.indicator hEv)
  have hae := convTail_ae_det_compl hW K₀ hc.ne' E S
  calc (μ W n) Ev = ∫⁻ ω, Ev.indicator 1 ω ∂(μ W n) := (lintegral_indicator_one hEv).symm
    _ = ∫⁻ ω, ∫⁻ t, Ev.indicator 1 (ω - (∑ i, ω i * e i) • e + t • e) ∂(gaussianReal 0 1)
          ∂(μ W n) := hline
    _ ≤ ∫⁻ _ω, β ∂(μ W n) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with ω hω
        set ω' : Ω W n := ω - (∑ i, ω i * e i) • e with hω'
        have hr : (convTail_compl S (K₀ + (c : ℂ) • blockDiagOp (gueBlock W n ω') -
            (E : ℂ) • (1 : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ))).det ≠ 0 := by
          have h1 : ω' = ω + (-(∑ i, ω i * e i)) • e := by
            rw [hω', sub_eq_add_neg, neg_smul]
          rw [h1, convTail_shift, convTail_compl_add_proj]
          exact hω
        have hmeas : Measurable fun t : ℝ => ω' + t • e :=
          measurable_const.add (measurable_id.smul_const e)
        have hfun : (fun t : ℝ => Ev.indicator (1 : Ω W n → ℝ≥0∞) (ω' + t • e)) =
            ({t : ℝ | ω' + t • e ∈ Ev}).indicator 1 := by
          funext t
          simp [Set.indicator]
        have hmeasS : MeasurableSet {t : ℝ | ω' + t • e ∈ Ev} := hEv.preimage hmeas
        rw [hfun, lintegral_indicator_one hmeasS]
        exact convTail_line_le hW hc K₀ hK₀ E hS hx hy hh ω' hr
    _ = β := by simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal (convTail_const hW hc hh hS.card_pos hcard)

end LSBA
