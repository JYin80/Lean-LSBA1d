import LSBA.Sampling.Transfer

/-!
# The common space of Lemma 7.5 [uvc:lem:space]

Lemma 7.5 [uvc:lem:space], (7.12) [uvc:eq:common-space-errors]: on a product of cells, the span of
the products over the `k` edges of the free coefficients of the two anchors of each cell and the
free differences, of dimension at most `6^k`, and the distance of `W^{k-1} ℒ_k` to this space
under the closeness of the transfer products.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The product `I_1 × ⋯ × I_k` of the cells of the labels of `a` (Lemma 7.5 [uvc:lem:space]). -/
abbrev CellProd (n : ℕ) {L k : ℕ} (a : Fin k → Fin L) : Type :=
  {x : Fin k → Fin L // ∀ j, cellStart n (x j) = cellStart n (a j)}

/-- The six coefficient functions of one edge `(x, y)` of a loop word: `c_{xα} c_{yβ}` for the
two anchors of each cell, `d_{xy}` and `d_{yx}` (coefficients of (7.10) [uvc:eq:interpolate]). -/
def edgeFn (n : ℕ) (E : ℝ) {L : ℕ} : (Bool × Bool) ⊕ Bool → Fin L → Fin L → ℂ
  | .inl (i, j), x, y =>
      ((cellCoef n E x (if i then cellStart n x else cellPrev n x) *
        cellCoef n E y (if j then cellStart n y else cellPrev n y) : ℝ) : ℂ)
  | .inr false, x, y => ((cellD n E x y : ℝ) : ℂ)
  | .inr true, x, y => ((cellD n E y x : ℝ) : ℂ)

/-- The common interpolation space `𝒱` of Lemma 7.5 [uvc:lem:space] on the cell product of `a`:
the span of the products over the `k` edges of a loop word of edge coefficient functions. -/
def loopSpace (n : ℕ) (E : ℝ) {L k : ℕ} (a : Fin k → Fin L) : Submodule ℂ (CellProd n a → ℂ) :=
  Submodule.span ℂ (Set.range fun s : Fin k → (Bool × Bool) ⊕ Bool =>
    fun x : CellProd n a => ∏ j : Fin k, edgeFn n E (s j) (x.1 j) (x.1 (finRotate k j)))

/-- Lemma 7.5 [uvc:lem:space]: `dim 𝒱 ≤ d_k = 6^k`. -/
theorem finrank_loopSpace_le (n : ℕ) (E : ℝ) {L k : ℕ} (a : Fin k → Fin L) :
    Module.finrank ℂ (loopSpace n E a) ≤ 6 ^ k := by
  unfold loopSpace
  refine (finrank_range_le_card _).trans ?_
  simp

/-! ## The loop in block form -/

/-- The inclusion `ℂ^W → ℂ^L ⊗ ℂ^W` of the coordinates into block `b`. -/
private def spaceEmb (W L : ℕ) (b : Fin L) : Matrix (Fin L × Fin W) (Fin W) ℂ :=
  Matrix.of fun p β => if p = (b, β) then 1 else 0

/-- `E_b = W⁻¹ ι_b ι_b*`. -/
private theorem space_emb_blockE (W L : ℕ) (b : Fin L) :
    blockE W L b = (W : ℂ)⁻¹ • (spaceEmb W L b * (spaceEmb W L b)ᴴ) := by
  ext p q
  simp only [blockE, spaceEmb, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.of_apply, smul_eq_mul]
  by_cases h : p = q
  · subst h
    obtain ⟨a, α⟩ := p
    by_cases hb : a = b
    · subst hb; simp
    · simp [hb]
  · simp only [h, ↓reduceIte]
    symm
    rw [mul_eq_zero]
    right
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hp : p = (b, x)
    · by_cases hq : q = (b, x)
      · exact absurd (hp.trans hq.symm) h
      · simp [hq]
    · simp [hp]

/-- `ι_a* X ι_b` is the `(a, b)` block of `X`. -/
private theorem space_emb_block (W L : ℕ) (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : (spaceEmb W L a)ᴴ * X * spaceEmb W L b = blockOf X a b := by
  ext α β
  simp [spaceEmb, blockOf, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- `ι_{z_0}* X_1 E_{z_1} ⋯ X_m E_{z_m}` is `W^{-m}` times the ordered product of the blocks
`(X_i)_{z_{i-1} z_i}` and `ι_{z_m}*`. -/
private theorem space_chain (W L : ℕ) :
    ∀ (m : ℕ) (z : Fin (m + 1) → Fin L) (X : Fin m → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ),
      (spaceEmb W L (z 0))ᴴ * (List.ofFn fun i : Fin m => X i * blockE W L (z i.succ)).prod =
        ((W : ℂ)⁻¹ ^ m) •
          (List.ofFn fun i : Fin m => blockOf (X i) (z i.castSucc) (z i.succ)).prod
          * (spaceEmb W L (z (Fin.last m)))ᴴ := by
  intro m
  induction m with
  | zero =>
    intro z X
    simp
  | succ m ih =>
    intro z X
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    have h := ih (fun i => z i.succ) (fun i => X i.succ)
    simp only [Fin.succ_castSucc, Fin.succ_last] at h
    set rest := (List.ofFn fun i : Fin m => X i.succ * blockE W L (z i.succ.succ)).prod
    have e1 : (spaceEmb W L (z 0))ᴴ * (X 0 * blockE W L (z (Fin.succ 0)) * rest) =
        (W : ℂ)⁻¹ • (blockOf (X 0) (z 0) (z (Fin.succ 0)) *
          ((spaceEmb W L (z (Fin.succ 0)))ᴴ * rest)) := by
      rw [space_emb_blockE, ← space_emb_block W L (X 0) (z 0) (z (Fin.succ 0))]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [e1, h, Fin.castSucc_zero]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, smul_smul, pow_succ]
    congr 1
    ring

private theorem space_rot_symm_zero (m : ℕ) : (finRotate (m + 1)).symm 0 = Fin.last m :=
  (finRotate (m + 1)).symm_apply_eq.mpr finRotate_last'.symm

private theorem space_rot_symm_succ (m : ℕ) (i : Fin m) :
    (finRotate (m + 1)).symm i.succ = i.castSucc :=
  (finRotate (m + 1)).symm_apply_eq.mpr (by rw [finRotate_apply, Fin.coeSucc_eq_succ])

/-- The loop trace of (5.5) [fo:eq:loops] in block form: `Tr(X_1 E_{x_1} ⋯ X_k E_{x_k})` is
`W^{-k}` times the trace of the ordered product of the blocks `(X_i)_{x_{i-1} x_i}`, with
`x_0 = x_k`. -/
private theorem space_loop_trace (W L m : ℕ)
    (X : Fin (m + 1) → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (x : Fin (m + 1) → Fin L) :
    Matrix.trace (List.ofFn fun i : Fin (m + 1) => X i * blockE W L (x i)).prod =
      (W : ℂ)⁻¹ ^ (m + 1) * Matrix.trace (List.ofFn fun i : Fin (m + 1) =>
        blockOf (X i) (x ((finRotate (m + 1)).symm i)) (x i)).prod := by
  have h := space_chain W L m x (fun i => X i.succ)
  rw [List.ofFn_succ, List.prod_cons]
  set rest := (List.ofFn fun i : Fin m => X i.succ * blockE W L (x i.succ)).prod
  set chain := (List.ofFn fun i : Fin m => blockOf (X i.succ) (x i.castSucc) (x i.succ)).prod
  have e1 : X 0 * blockE W L (x 0) * rest = (W : ℂ)⁻¹ • ((X 0 * spaceEmb W L (x 0)) *
      ((spaceEmb W L (x 0))ᴴ * rest)) := by
    rw [space_emb_blockE]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  have e2 : (List.ofFn fun i : Fin (m + 1) =>
        blockOf (X i) (x ((finRotate (m + 1)).symm i)) (x i)).prod =
      blockOf (X 0) (x (Fin.last m)) (x 0) * chain := by
    rw [List.ofFn_succ, List.prod_cons, space_rot_symm_zero]
    simp only [space_rot_symm_succ]
    rfl
  rw [e1, h, e2, Matrix.trace_smul, smul_eq_mul]
  have e3 : (X 0 * spaceEmb W L (x 0)) *
      (((W : ℂ)⁻¹ ^ m) • chain * (spaceEmb W L (x (Fin.last m)))ᴴ) =
      ((W : ℂ)⁻¹ ^ m) •
        ((X 0 * spaceEmb W L (x 0) * chain) * (spaceEmb W L (x (Fin.last m)))ᴴ) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [e3, Matrix.trace_smul, Matrix.trace_mul_comm, smul_eq_mul]
  have e4 : (spaceEmb W L (x (Fin.last m)))ᴴ * (X 0 * spaceEmb W L (x 0) * chain) =
      blockOf (X 0) (x (Fin.last m)) (x 0) * chain := by
    rw [← space_emb_block W L (X 0) (x (Fin.last m)) (x 0)]
    simp only [Matrix.mul_assoc]
  rw [e4]
  ring

/-! ## Anchor sums and coefficient bounds -/

/-- The first block `c` of a cell and its predecessor, indexed by `true` and `false`. -/
private def spaceAnch {L : ℕ} (c : Fin L) (i : Bool) : Fin L :=
  if i then c else (finRotate L).symm c

private theorem space_anch_true {L : ℕ} (n : ℕ) (x : Fin L) :
    spaceAnch (cellStart n x) true = cellStart n x := rfl

private theorem space_anch_false {L : ℕ} (n : ℕ) (x : Fin L) :
    spaceAnch (cellStart n x) false = cellPrev n x := rfl

private theorem space_prev_ne {L : ℕ} (hL : 2 ≤ L) (c : Fin L) : (finRotate L).symm c ≠ c := by
  intro h
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 2 := ⟨L - 2, by omega⟩
  have h2 : c + 1 = c := by
    have := (finRotate (m + 2)).symm_apply_eq.mp h
    simpa using this.symm
  have h3 : (1 : Fin (m + 2)) = 0 := by simp at h2
  rw [Fin.one_eq_zero_iff] at h3
  omega

/-- A sum supported on the two anchors of a cell has two terms. -/
private theorem space_sum_two {L : ℕ} (hL : 2 ≤ L) (c : Fin L) {M : Type*} [AddCommMonoid M]
    (φ : Fin L → M) (h0 : ∀ α, α ≠ c → α ≠ (finRotate L).symm c → φ α = 0) :
    ∑ α, φ α = ∑ i : Bool, φ (spaceAnch c i) := by
  rw [Fintype.sum_bool, Finset.sum_eq_add c ((finRotate L).symm c)
    (space_prev_ne hL c).symm (fun α _ hα => h0 α hα.1 hα.2)
    (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h)]
  simp [spaceAnch]

/-- In the bulk `|E| ≤ 2 - κ`: `sin ϑ ≥ κ/2` for `ϑ = arccos (E/2)`. -/
private theorem space_sin_ge {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ) :
    κ / 2 ≤ Real.sin (Real.arccos (E / 2)) := by
  have hS := Real.sin_arccos (E / 2)
  set S := Real.sin (Real.arccos (E / 2))
  have hE2 : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hE 2
  have hpos : 0 ≤ 1 - (E / 2) ^ 2 := by nlinarith
  have hS2 : S ^ 2 = 1 - (E / 2) ^ 2 := by rw [hS, Real.sq_sqrt hpos]
  have hS1 : S ≤ 1 := Real.sin_le_one _
  have hS0 : 0 ≤ S := by rw [hS]; exact Real.sqrt_nonneg _
  nlinarith

/-- `|sin t / sin ϑ| ≤ 2/κ` in the bulk. -/
private theorem space_abs_div_le {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (t : ℝ) : |Real.sin t / Real.sin (Real.arccos (E / 2))| ≤ 2 / κ := by
  have hs := space_sin_ge hκ hκ2 hE
  have hs0 : 0 < Real.sin (Real.arccos (E / 2)) := by linarith
  rw [abs_div, abs_of_pos hs0, div_le_div_iff₀ hs0 hκ]
  have := Real.abs_sin_le_one t
  nlinarith

/-- The free coefficients satisfy `|c_{aα}| ≤ 2/κ`. -/
private theorem space_coef_abs_le {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (n : ℕ) {L : ℕ} (a α : Fin L) : |cellCoef n E a α| ≤ 2 / κ := by
  unfold cellCoef
  split_ifs
  · exact space_abs_div_le hκ hκ2 hE _
  · rw [abs_neg]; exact space_abs_div_le hκ hκ2 hE _
  · rw [abs_zero]; positivity

/-- The free source coefficients satisfy `|q_{ab}| ≤ 2/κ`. -/
private theorem space_src_abs_le {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (n : ℕ) {L : ℕ} (a b : Fin L) : |cellSrc n E a b| ≤ 2 / κ := by
  unfold cellSrc
  split_ifs
  · exact space_abs_div_le hκ hκ2 hE _
  · rw [abs_zero]; positivity

/-- `c_{aα}` vanishes off the two anchors of the cell of `a`. -/
private theorem space_coef_other (n : ℕ) (E : ℝ) {L : ℕ} (a α : Fin L) (h1 : α ≠ cellStart n a)
    (h2 : α ≠ (finRotate L).symm (cellStart n a)) : cellCoef n E a α = 0 := by
  have h2' : α ≠ cellPrev n a := h2
  simp only [cellCoef, h1, h2', ite_false]

/-- `|d_{ab}| ≤ K + 2K²` with `K = 2/κ`. -/
private theorem space_d_abs_le {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (n : ℕ) {L : ℕ} (hL : 2 ≤ L) (a b : Fin L) :
    |cellD n E a b| ≤ 2 / κ + 2 * (2 / κ) ^ 2 := by
  have hK : 0 ≤ 2 / κ := by positivity
  unfold cellD
  rw [space_sum_two hL (cellStart n a) (fun α => cellCoef n E a α * cellSrc n E b α)
    (fun α h1 h2 => by
      rw [space_coef_other n E a α h1 h2, zero_mul])]
  refine (abs_add_le _ _).trans ?_
  have h1 := space_src_abs_le hκ hκ2 hE n a b
  have h2 : |∑ i : Bool, cellCoef n E a (spaceAnch (cellStart n a) i) *
      cellSrc n E b (spaceAnch (cellStart n a) i)| ≤ 2 * (2 / κ) ^ 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ i : Bool, |cellCoef n E a (spaceAnch (cellStart n a) i) *
        cellSrc n E b (spaceAnch (cellStart n a) i)| ≤ (2 / κ) ^ 2 := by
      intro i
      rw [abs_mul, sq]
      exact mul_le_mul (space_coef_abs_le hκ hκ2 hE n _ _) (space_src_abs_le hκ hκ2 hE n _ _)
        (abs_nonneg _) hK
    calc _ ≤ ∑ _i : Bool, (2 / κ) ^ 2 := Finset.sum_le_sum fun i _ => this i
      _ = 2 * (2 / κ) ^ 2 := by simp
  linarith

/-! ## Expansion of the interpolated blocks -/

/-- The anchor-pair edge functions through the anchors `spaceAnch`. -/
private theorem space_edgeFn_inl (n : ℕ) (E : ℝ) {L : ℕ} (i j : Bool) (x y : Fin L) :
    edgeFn n E (.inl (i, j)) x y =
      ((cellCoef n E x (spaceAnch (cellStart n x) i) *
        cellCoef n E y (spaceAnch (cellStart n y) j) : ℝ) : ℂ) := by
  cases i <;> cases j <;> rfl

/-- The double sum over blocks of `c_{pα} c_{qβ} f(α, β)` has only the four anchor terms. -/
private theorem space_dblsum {L : ℕ} (hL : 2 ≤ L) (n : ℕ) (E : ℝ) (p q : Fin L) {M : Type*}
    [AddCommMonoid M] [Module ℂ M] (f : Fin L → Fin L → M) :
    ∑ α, ∑ β, ((cellCoef n E p α * cellCoef n E q β : ℝ) : ℂ) • f α β =
      ∑ i : Bool, ∑ j : Bool, ((cellCoef n E p (spaceAnch (cellStart n p) i) *
        cellCoef n E q (spaceAnch (cellStart n q) j) : ℝ) : ℂ) •
          f (spaceAnch (cellStart n p) i) (spaceAnch (cellStart n q) j) := by
  rw [space_sum_two hL (cellStart n p) _ ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [space_sum_two hL (cellStart n q) _ ?_]
    intro β h1 h2
    rw [space_coef_other n E q β h1 h2]
    simp
  · intro α h1 h2
    refine Finset.sum_eq_zero fun β _ => ?_
    rw [space_coef_other n E p α h1 h2]
    simp

/-- The constant matrices multiplying the six edge functions in the interpolation of the block
`(p, q)` (for the sign `σ`), where `c` and `d` are the first blocks of the cells of `p` and `q`. -/
private def spaceMat {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (σ : Bool)
    (c d : Fin L) : (Bool × Bool) ⊕ Bool → Matrix (Fin W) (Fin W) ℂ
  | .inl (i, j) => if σ then blockOf G (spaceAnch c i) (spaceAnch d j)
      else (blockOf G (spaceAnch d j) (spaceAnch c i))ᴴ
  | .inr false => if σ then 1 else 0
  | .inr true => if σ then 0 else 1

/-- The interpolation of `G_{pq}` as a combination of the six edge functions with constant
matrices. -/
private theorem space_expand_true {W L : ℕ} (hL : 2 ≤ L) (n : ℕ) (E : ℝ)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (p q : Fin L) :
    interpBlock n E G p q =
      ∑ s, edgeFn n E s p q • spaceMat G true (cellStart n p) (cellStart n q) s := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, interpBlock,
    space_dblsum hL n E p q (fun α β => blockOf G α β)]
  simp only [spaceMat, Fintype.sum_bool, edgeFn, ite_true, smul_zero, Bool.false_eq_true,
    ite_false, zero_add]
  rfl

/-- The adjoint of the interpolation of `G_{qp}` as a combination of the six edge functions of
`(p, q)` with constant matrices. -/
private theorem space_expand_false {W L : ℕ} (hL : 2 ≤ L) (n : ℕ) (E : ℝ)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (p q : Fin L) :
    (interpBlock n E G q p)ᴴ =
      ∑ s, edgeFn n E s p q • spaceMat G false (cellStart n p) (cellStart n q) s := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, interpBlock,
    Matrix.conjTranspose_add, Matrix.conjTranspose_sum]
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Complex.star_def,
    Complex.conj_ofReal, Matrix.conjTranspose_one]
  rw [space_dblsum hL n E q p (fun α β => (blockOf G α β)ᴴ)]
  simp only [spaceMat, Fintype.sum_bool, edgeFn, Bool.false_eq_true, ite_false, smul_zero,
    ite_true, add_zero, space_anch_true, space_anch_false,
    mul_comm (cellCoef n E p _) (cellCoef n E q _)]
  abel

/-! ## Norm bounds -/

/-- The identity matrix has operator norm at most `1`. -/
private theorem space_norm_one_le (k : Type*) [Fintype k] [DecidableEq k] :
    ‖(1 : Matrix k k ℂ)‖ ≤ 1 := by
  have := Matrix.l2_opNorm_conjTranspose_mul_self (1 : Matrix k k ℂ)
  rw [Matrix.conjTranspose_one, Matrix.one_mul] at this
  nlinarith [norm_nonneg (1 : Matrix k k ℂ)]

/-- An anchor block is bounded by the anchor norm. -/
private theorem space_anchor_le (n : ℕ) {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (p q : Fin L) (i j : Bool) :
    ‖blockOf G (spaceAnch (cellStart n p) i) (spaceAnch (cellStart n q) j)‖ ≤
      anchorNorm n G p q := by
  unfold anchorNorm
  cases i <;> cases j <;> simp [space_anch_true, space_anch_false]

/-- The anchor norm is nonnegative. -/
private theorem space_anchorNorm_nonneg (n : ℕ) {W L : ℕ}
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (p q : Fin L) : 0 ≤ anchorNorm n G p q :=
  le_max_of_le_left (le_max_of_le_left (norm_nonneg _))

/-- The anchor norm is at most the anchor envelope. -/
private theorem space_anchorNorm_le_env (n : ℕ) {W L : ℕ}
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (p q : Fin L) :
    anchorNorm n G p q ≤ anchorEnv n G :=
  le_ciSup (f := fun ab : Fin L × Fin L => anchorNorm n G ab.1 ab.2)
    (Set.finite_range _).bddAbove (p, q)

/-- The anchor-pair matrices are bounded by the anchor envelope. -/
private theorem space_mat_norm_le (n : ℕ) {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (σ : Bool) (p q : Fin L) (i j : Bool) :
    ‖spaceMat G σ (cellStart n p) (cellStart n q) (.inl (i, j))‖ ≤ anchorEnv n G := by
  cases σ
  · simp only [spaceMat, Bool.false_eq_true, ite_false, Matrix.l2_opNorm_conjTranspose]
    exact (space_anchor_le n G q p j i).trans (space_anchorNorm_le_env n G q p)
  · simp only [spaceMat, ite_true]
    exact (space_anchor_le n G p q i j).trans (space_anchorNorm_le_env n G p q)

/-- The interpolation of a block is bounded by `(6K² + K)(1 + 𝒢)` with `K = 2/κ`: four anchor
terms with coefficients at most `K²`, and the `d` term of size at most `K + 2K²`. -/
private theorem space_expand_norm_le {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (n : ℕ) {W L : ℕ} (hL : 2 ≤ L) (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (σ : Bool)
    (p q : Fin L) :
    ‖∑ s, edgeFn n E s p q • spaceMat G σ (cellStart n p) (cellStart n q) s‖ ≤
      (6 * (2 / κ) ^ 2 + 2 / κ) * (1 + anchorEnv n G) := by
  have hK : 0 ≤ 2 / κ := by positivity
  have hG : 0 ≤ anchorEnv n G := (space_anchorNorm_nonneg n G p q).trans
    (space_anchorNorm_le_env n G p q)
  refine (norm_sum_le _ _).trans ?_
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  have hin : ∀ i j : Bool, ‖edgeFn n E (.inl (i, j)) p q •
      spaceMat G σ (cellStart n p) (cellStart n q) (.inl (i, j))‖ ≤
        (2 / κ) ^ 2 * anchorEnv n G := by
    intro i j
    rw [norm_smul, space_edgeFn_inl, Complex.norm_real, Real.norm_eq_abs, abs_mul, sq]
    exact mul_le_mul (mul_le_mul (space_coef_abs_le hκ hκ2 hE n _ _)
      (space_coef_abs_le hκ hκ2 hE n _ _) (abs_nonneg _) hK) (space_mat_norm_le n G σ p q i j)
      (norm_nonneg _) (by positivity)
  have hD := space_d_abs_le hκ hκ2 hE n hL
  have hout : ∀ b : Bool, ‖edgeFn n E (.inr b) p q •
      spaceMat G σ (cellStart n p) (cellStart n q) (.inr b)‖ ≤
        (2 / κ + 2 * (2 / κ) ^ 2) * ‖spaceMat G σ (cellStart n p) (cellStart n q) (.inr b)‖ := by
    intro b
    rw [norm_smul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    cases b
    · rw [show edgeFn n E (.inr false) p q = ((cellD n E p q : ℝ) : ℂ) from rfl,
        Complex.norm_real, Real.norm_eq_abs]
      exact hD p q
    · rw [show edgeFn n E (.inr true) p q = ((cellD n E q p : ℝ) : ℂ) from rfl,
        Complex.norm_real, Real.norm_eq_abs]
      exact hD q p
  have h1 : ‖spaceMat G σ (cellStart n p) (cellStart n q) (.inr false)‖ +
      ‖spaceMat G σ (cellStart n p) (cellStart n q) (.inr true)‖ ≤ 1 := by
    cases σ
    · simp only [spaceMat, Bool.false_eq_true, ite_false, norm_zero, zero_add]
      exact space_norm_one_le _
    · simp only [spaceMat, ite_true, norm_zero, add_zero]
      exact space_norm_one_le _
  have hsumin : ∑ i : Bool, ∑ j : Bool, ‖edgeFn n E (.inl (i, j)) p q •
      spaceMat G σ (cellStart n p) (cellStart n q) (.inl (i, j))‖ ≤
        4 * ((2 / κ) ^ 2 * anchorEnv n G) := by
    calc _ ≤ ∑ _i : Bool, ∑ _j : Bool, (2 / κ) ^ 2 * anchorEnv n G :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hin i j
      _ = _ := by simp; ring
  have hsumout : ∑ b : Bool, ‖edgeFn n E (.inr b) p q •
      spaceMat G σ (cellStart n p) (cellStart n q) (.inr b)‖ ≤ 2 / κ + 2 * (2 / κ) ^ 2 := by
    calc _ ≤ ∑ b : Bool, (2 / κ + 2 * (2 / κ) ^ 2) *
          ‖spaceMat G σ (cellStart n p) (cellStart n q) (.inr b)‖ :=
          Finset.sum_le_sum fun b _ => hout b
      _ = (2 / κ + 2 * (2 / κ) ^ 2) *
          (‖spaceMat G σ (cellStart n p) (cellStart n q) (.inr false)‖ +
            ‖spaceMat G σ (cellStart n p) (cellStart n q) (.inr true)‖) := by
        rw [Fintype.sum_bool]; ring
      _ ≤ (2 / κ + 2 * (2 / κ) ^ 2) * 1 := by gcongr
      _ = _ := mul_one _
  nlinarith [sq_nonneg (2 / κ), mul_nonneg (sq_nonneg (2 / κ)) hG]

/-- The `(a, b)` block of an adjoint is the adjoint of the `(b, a)` block. -/
private theorem space_blockOf_conjTranspose {W L : ℕ}
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) :
    blockOf Gᴴ a b = (blockOf G b a)ᴴ := by
  ext; simp [blockOf]

/-- The interpolation remainder of one factor of a loop word, for either sign:
`‖X^σ_{pq} - Σ_s f_s(p, q) M_s‖ ≤ C ε (1 + 𝒢)`. -/
private theorem space_edge_err (n : ℕ) {E ε Cg : ℝ} {W L : ℕ} (hL : 2 ≤ L) (hCg : 0 ≤ Cg)
    (hε : 0 ≤ ε) (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hR : ∀ a b : Fin L, ‖blockOf G a b - interpBlock n E G a b‖ ≤
      Cg * ε * (1 + anchorNorm n G a b)) (σ : Bool) (p q : Fin L) :
    ‖blockOf (sgnMat G σ) p q -
      ∑ s, edgeFn n E s p q • spaceMat G σ (cellStart n p) (cellStart n q) s‖ ≤
        Cg * ε * (1 + anchorEnv n G) := by
  have hCe : 0 ≤ Cg * ε := mul_nonneg hCg hε
  cases σ
  · rw [← space_expand_false hL n E G p q]
    simp only [sgnMat, Bool.false_eq_true, ite_false, space_blockOf_conjTranspose]
    rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
    exact (hR q p).trans (mul_le_mul_of_nonneg_left
      (by linarith [space_anchorNorm_le_env n G q p]) hCe)
  · rw [← space_expand_true hL n E G p q]
    simp only [sgnMat, ite_true]
    exact (hR p q).trans (mul_le_mul_of_nonneg_left
      (by linarith [space_anchorNorm_le_env n G p q]) hCe)

/-! ## Products, traces and expansions -/

/-- Norm of an ordered product of `m` factors of norm at most `B`. -/
private theorem space_prod_norm_le {R : Type*} [NormedRing R] {B : ℝ} (hB : 0 ≤ B)
    (h1 : ‖(1 : R)‖ ≤ 1) :
    ∀ (m : ℕ) (Y : Fin m → R), (∀ i, ‖Y i‖ ≤ B) → ‖(List.ofFn Y).prod‖ ≤ B ^ m := by
  intro m
  induction m with
  | zero => intro Y _; simpa using h1
  | succ m ih =>
    intro Y hY
    rw [List.ofFn_succ, List.prod_cons, pow_succ']
    refine (norm_mul_le _ _).trans (mul_le_mul (hY 0) (ih _ fun i => hY _) (norm_nonneg _) hB)

/-- Telescoping bound for two ordered products of `m` factors. -/
private theorem space_prod_sub_le {R : Type*} [NormedRing R] {B δ : ℝ} (hB : 0 ≤ B)
    (hδ : 0 ≤ δ) (h1 : ‖(1 : R)‖ ≤ 1) :
    ∀ (m : ℕ) (Y Z : Fin m → R), (∀ i, ‖Y i‖ ≤ B) → (∀ i, ‖Z i‖ ≤ B) →
      (∀ i, ‖Y i - Z i‖ ≤ δ) →
        ‖(List.ofFn Y).prod - (List.ofFn Z).prod‖ ≤ m * δ * B ^ (m - 1) := by
  intro m
  induction m with
  | zero => intro Y Z _ _ _; simp
  | succ m ih =>
    intro Y Z hY hZ hd
    have hP := space_prod_norm_le hB h1 m (fun i => Y i.succ) (fun i => hY _)
    have hQ := ih (fun i => Y i.succ) (fun i => Z i.succ) (fun i => hY _) (fun i => hZ _)
      (fun i => hd _)
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    have e : Y 0 * (List.ofFn fun i : Fin m => Y i.succ).prod -
        Z 0 * (List.ofFn fun i : Fin m => Z i.succ).prod =
        (Y 0 - Z 0) * (List.ofFn fun i : Fin m => Y i.succ).prod +
          Z 0 * ((List.ofFn fun i : Fin m => Y i.succ).prod -
            (List.ofFn fun i : Fin m => Z i.succ).prod) := by noncomm_ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have t1 : ‖(Y 0 - Z 0) * (List.ofFn fun i : Fin m => Y i.succ).prod‖ ≤ δ * B ^ m :=
      (norm_mul_le _ _).trans (mul_le_mul (hd 0) hP (norm_nonneg _) hδ)
    have t2 : ‖Z 0 * ((List.ofFn fun i : Fin m => Y i.succ).prod -
        (List.ofFn fun i : Fin m => Z i.succ).prod)‖ ≤ B * (m * δ * B ^ (m - 1)) :=
      (norm_mul_le _ _).trans (mul_le_mul (hZ 0) hQ (norm_nonneg _) hB)
    refine (add_le_add t1 t2).trans ?_
    rcases m with _ | m
    · simp
    · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
      nlinarith [mul_nonneg hδ (pow_nonneg hB m)]


/-- An entry is bounded by the operator norm. -/
private theorem space_norm_entry_le {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (i j : n) : ‖M i j‖ ≤ ‖M‖ := by
  have h := Matrix.l2_opNorm_mulVec M (EuclideanSpace.single j (1 : ℂ))
  have hn : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  rw [hn, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le ((EuclideanSpace.equiv n ℂ).symm
    (M.mulVec (EuclideanSpace.single j (1 : ℂ)).ofLp)) i
  convert this using 2
  simp

/-- `‖Tr D‖ ≤ W ‖D‖` for `D` on `ℂ^W`. -/
private theorem space_norm_trace_le (W : ℕ) (D : Matrix (Fin W) (Fin W) ℂ) :
    ‖Matrix.trace D‖ ≤ W * ‖D‖ := by
  unfold Matrix.trace
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖Matrix.diag D i‖ ≤ ∑ _i : Fin W, ‖D‖ :=
        Finset.sum_le_sum fun i _ => space_norm_entry_le D i i
    _ = W * ‖D‖ := by simp

/-- Expansion of an ordered product of sums of scalar multiples of matrices. -/
private theorem space_prod_sum {ι : Type*} [Fintype ι] {W : ℕ} :
    ∀ (m : ℕ) (c : Fin m → ι → ℂ) (M : Fin m → ι → Matrix (Fin W) (Fin W) ℂ),
      (List.ofFn fun i => ∑ s, c i s • M i s).prod =
        ∑ t : Fin m → ι, (∏ i, c i (t i)) • (List.ofFn fun i => M i (t i)).prod := by
  intro m
  induction m with
  | zero => intro c M; simp
  | succ m ih =>
    intro c M
    rw [List.ofFn_succ, List.prod_cons, ih (fun i => c i.succ) (fun i => M i.succ),
      ← (Fin.consEquiv (fun _ : Fin (m + 1) => ι)).sum_comp, Fintype.sum_prod_type,
      Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ, Fin.prod_univ_succ,
      List.ofFn_succ, List.prod_cons, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [mul_comm]

/-- Lemma 7.5 [uvc:lem:space], random bound of (7.12) [uvc:eq:common-space-errors], deterministic
form: under the hypotheses of `green_interp`, `W^{k-1} ℒ_k` is within `C ε (1 + 𝒢)^k` of `𝒱` on
every cell product, for every sign word. -/
theorem loopTr_dist_space (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W L n : ℕ) (E ε : ℝ) (z : ℂ) (V : Fin L → Matrix (Fin W) (Fin W) ℂ),
      1 ≤ W → 3 ≤ L → 1 ≤ n → |E| ≤ 2 - κ → (∀ r, (V r).IsHermitian) → z.im ≠ 0 → 0 ≤ ε →
      ε ≤ 1 → CellClose n E z V ε → CellClose n E (starRingEnd ℂ z) V ε →
      let G := resolventMat (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V) z
      ∀ (a : Fin k → Fin L) (σ : Fin k → Bool), ∃ v ∈ loopSpace n E a, ∀ x : CellProd n a,
        ‖(W : ℂ) ^ (k - 1) * loopTr G x.1 σ - v x‖ ≤ C * ε * (1 + anchorEnv n G) ^ k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨Cg, hCg, hgi⟩ := green_interp κ hκ hκ2
  have hK : 0 ≤ 2 / κ := by positivity
  have hA : 0 ≤ 6 * (2 / κ) ^ 2 + 2 / κ := by positivity
  refine ⟨((m + 1 : ℕ) : ℝ) * Cg * ((6 * (2 / κ) ^ 2 + 2 / κ) + Cg) ^ m,
    by positivity, ?_⟩
  intro W L n E ε z V hW hL hn hE hV hz hε0 hε1 hcl hcl' G a σ
  have hL2 : 2 ≤ L := by omega
  have hR : ∀ p q : Fin L, ‖blockOf G p q - interpBlock n E G p q‖ ≤
      Cg * ε * (1 + anchorNorm n G p q) :=
    hgi W L n E ε z V hL hn hE hV hz hε0 hε1 hcl hcl'
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast (by omega : W ≠ 0)
  have hWpos : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hL0 : 0 < L := by omega
  have hG : 0 ≤ anchorEnv n G :=
    (space_anchorNorm_nonneg n G ⟨0, hL0⟩ ⟨0, hL0⟩).trans
      (space_anchorNorm_le_env n G ⟨0, hL0⟩ ⟨0, hL0⟩)
  set e := finRotate (m + 1) with he
  set A : ℝ := 6 * (2 / κ) ^ 2 + 2 / κ with hAdef
  set 𝒢 := anchorEnv n G with h𝒢
  -- the constant matrices and the coefficient functions of the interpolants
  let M : Fin (m + 1) → (Bool × Bool) ⊕ Bool → Matrix (Fin W) (Fin W) ℂ := fun i s =>
    spaceMat G (σ i) (cellStart n (a (e.symm i))) (cellStart n (a i)) s
  let Mt : (Fin (m + 1) → (Bool × Bool) ⊕ Bool) → Matrix (Fin W) (Fin W) ℂ := fun t =>
    (List.ofFn fun i => M i (t i)).prod
  let v : CellProd n a → ℂ := fun x => ∑ t : Fin (m + 1) → (Bool × Bool) ⊕ Bool,
    ((W : ℂ)⁻¹ * Matrix.trace (Mt t)) * ∏ j, edgeFn n E (t (e j)) (x.1 j) (x.1 (e j))
  refine ⟨v, ?_, ?_⟩
  · have hv : v = ∑ t : Fin (m + 1) → (Bool × Bool) ⊕ Bool, ((W : ℂ)⁻¹ * Matrix.trace (Mt t)) •
        (fun x : CellProd n a => ∏ j, edgeFn n E (t (e j)) (x.1 j) (x.1 (e j))) := by
      funext x
      simp [v, Finset.sum_apply]
    rw [hv]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨fun j => t (e j), rfl⟩)
  · intro x
    let Y : Fin (m + 1) → Matrix (Fin W) (Fin W) ℂ := fun i =>
      blockOf (sgnMat G (σ i)) (x.1 (e.symm i)) (x.1 i)
    let Z : Fin (m + 1) → Matrix (Fin W) (Fin W) ℂ := fun i =>
      ∑ s, edgeFn n E s (x.1 (e.symm i)) (x.1 i) • M i s
    have hZ : ∀ i, Z i = ∑ s, edgeFn n E s (x.1 (e.symm i)) (x.1 i) •
        spaceMat G (σ i) (cellStart n (x.1 (e.symm i))) (cellStart n (x.1 i)) s := by
      intro i
      simp only [Z, M, x.2 (e.symm i), x.2 i]
    have hYZ : ∀ i, ‖Y i - Z i‖ ≤ Cg * ε * (1 + 𝒢) := by
      intro i
      rw [hZ i]
      exact space_edge_err n hL2 hCg.le hε0 G hR (σ i) _ _
    have hZn : ∀ i, ‖Z i‖ ≤ A * (1 + 𝒢) := by
      intro i
      rw [hZ i]
      exact space_expand_norm_le hκ hκ2 hE n hL2 G (σ i) _ _
    have hYn : ∀ i, ‖Y i‖ ≤ (A + Cg) * (1 + 𝒢) := by
      intro i
      have h1 : ‖Y i‖ ≤ ‖Z i‖ + ‖Y i - Z i‖ := by
        calc ‖Y i‖ = ‖Z i + (Y i - Z i)‖ := by rw [add_sub_cancel]
          _ ≤ _ := norm_add_le _ _
      have h2 : Cg * ε * (1 + 𝒢) ≤ Cg * (1 + 𝒢) := by
        have : 0 ≤ Cg * (1 + 𝒢) := by positivity
        nlinarith
      nlinarith [hZn i, hYZ i]
    have hloop : (W : ℂ) ^ m * loopTr G x.1 σ =
        (W : ℂ)⁻¹ * Matrix.trace (List.ofFn Y).prod := by
      have h := space_loop_trace W L m (fun i => sgnMat G (σ i)) x.1
      have h' : loopTr G x.1 σ = Matrix.trace (List.ofFn fun i : Fin (m + 1) =>
          sgnMat G (σ i) * blockE W L (x.1 i)).prod := rfl
      rw [h', h]
      change (W : ℂ) ^ m * ((W : ℂ)⁻¹ ^ (m + 1) * Matrix.trace (List.ofFn Y).prod) = _
      rw [pow_succ, inv_pow]
      field_simp
    have hvx : v x = (W : ℂ)⁻¹ * Matrix.trace (List.ofFn Z).prod := by
      have h := space_prod_sum (ι := (Bool × Bool) ⊕ Bool) (W := W) (m + 1)
        (fun i s => edgeFn n E s (x.1 (e.symm i)) (x.1 i)) M
      change (List.ofFn fun i => ∑ s, edgeFn n E s (x.1 (e.symm i)) (x.1 i) • M i s).prod = _
        at h
      change v x = (W : ℂ)⁻¹ * Matrix.trace (List.ofFn fun i => ∑ s, edgeFn n E s
        (x.1 (e.symm i)) (x.1 i) • M i s).prod
      rw [h, Matrix.trace_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Matrix.trace_smul, smul_eq_mul]
      have hp : ∏ i, edgeFn n E (t i) (x.1 (e.symm i)) (x.1 i) =
          ∏ j, edgeFn n E (t (e j)) (x.1 j) (x.1 (e j)) := by
        rw [← Equiv.prod_comp e]
        simp
      rw [hp]
      simp only [Mt]
      ring
    have hD : ‖(List.ofFn Y).prod - (List.ofFn Z).prod‖ ≤
        ((m + 1 : ℕ) : ℝ) * (Cg * ε * (1 + 𝒢)) * ((A + Cg) * (1 + 𝒢)) ^ m := by
      have := space_prod_sub_le (R := Matrix (Fin W) (Fin W) ℂ) (B := (A + Cg) * (1 + 𝒢))
        (δ := Cg * ε * (1 + 𝒢)) (by positivity) (by positivity) (space_norm_one_le _) (m + 1) Y Z
        hYn (fun i => (hZn i).trans (by nlinarith [mul_nonneg hCg.le (by linarith : 0 ≤ 1 + 𝒢)]))
        hYZ
      simpa using this
    rw [Nat.add_sub_cancel, hloop, hvx, ← mul_sub, ← Matrix.trace_sub, norm_mul, norm_inv,
      Complex.norm_natCast]
    have ht := space_norm_trace_le W ((List.ofFn Y).prod - (List.ofFn Z).prod)
    calc (W : ℝ)⁻¹ * ‖((List.ofFn Y).prod - (List.ofFn Z).prod).trace‖
        ≤ (W : ℝ)⁻¹ * (W * ‖(List.ofFn Y).prod - (List.ofFn Z).prod‖) :=
          mul_le_mul_of_nonneg_left ht (by positivity)
      _ = ‖(List.ofFn Y).prod - (List.ofFn Z).prod‖ := by field_simp
      _ ≤ _ := hD
      _ = _ := by push_cast; rw [mul_pow]; ring

end LSBA
