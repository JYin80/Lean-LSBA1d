import LSBA.Upper.SmallChart

/-!
# The prepared chart

Chart entry in the proof of Lemma 9.1 [su:lem:preparation]. For an isotropic flag `(U, Y)` take
an orthonormal frame `F_Y` of `Y` and a unit normal `n_0` of `U` inside `Y` in these coordinates.
With `S = S_0`, the frame `S F_Y = (A; B)` satisfies `A* B = B* A`, because `S_0* J_ph S_0 = J`.
The first transfer step gives `T_1 S F_Y = (X_1; Y_1)` with `X_1 = -g⁻¹((V_1 - E) A + g B)` and
`Y_1 = A`. Where `X_1` is invertible, `T_1 S Y` is the graph of `-g R_1` with the Hermitian
`R_1 = -g⁻¹ Y_1 X_1⁻¹`, and `T_1 S U` is cut out by `v_1 = (X_1*)⁻¹ n_0`. The next steps are
`R_j = (V_j - E - g² R_{j-1})⁻¹` and `v_j = R_j v_{j-1}` ((9.2) [su:eq:transported-normal]).
Where all four steps are invertible, `(R_4, v_4)` is a prepared chart (9.1) [su:eq:graph-input].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- An orthonormal frame `F_Y` of the space `Y` of the flag: `F_Y* F_Y = 1` and
`F_Y F_Y* = P_Y` (`0` if none exists). -/
def prepFrame {W : ℕ} (x : IsoFlag W) : Matrix (Fin 2 × Fin W) (Fin W) ℂ :=
  if h : ∃ F : Matrix (Fin 2 × Fin W) (Fin W) ℂ, Fᴴ * F = 1 ∧ F * Fᴴ = x.1.2 then h.choose
  else 0

/-- A unit normal `n_0` of `U` inside `Y` in the coordinates of `prepFrame`:
`F_Y* P_U F_Y = 1 - n_0 n_0*` (`0` if none exists). -/
def prepNormal {W : ℕ} (x : IsoFlag W) : Fin W → ℂ :=
  if h : ∃ n : Fin W → ℂ, star n ⬝ᵥ n = 1 ∧
      (prepFrame x)ᴴ * x.1.1 * prepFrame x = 1 - Matrix.vecMulVec n (star n) then h.choose
  else 0

/-- The upper block `X_1` of `T_1 S F_Y` (proof of Lemma 9.1 [su:lem:preparation]). -/
def prepTop (W : ℕ) (g E : ℝ) (q : ℕ) (x : IsoFlag W) (ω : Ω W q) : Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun α β => (transferProd g ((max 1 g * E / g : ℝ) : ℂ) (blockSeq W q ω) 1 *
    freeConj W 0 * prepFrame x) (0, α) β

/-- The lower block `Y_1` of `T_1 S F_Y`. -/
def prepBot (W : ℕ) (g E : ℝ) (q : ℕ) (x : IsoFlag W) (ω : Ω W q) : Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun α β => (transferProd g ((max 1 g * E / g : ℝ) : ℂ) (blockSeq W q ω) 1 *
    freeConj W 0 * prepFrame x) (1, α) β

/-- The prepared graph coordinates of (9.2) [su:eq:transported-normal]: `R_1 = -g⁻¹ Y_1 X_1⁻¹`
and `R_j = (V_j - E - g² R_{j-1})⁻¹` for `j ≥ 2` (`prepR … 0 = 0` is not used). -/
def prepR (W : ℕ) (g E : ℝ) (q : ℕ) (x : IsoFlag W) (ω : Ω W q) :
    ℕ → Matrix (Fin W) (Fin W) ℂ
  | 0 => 0
  | 1 => -((g : ℂ)⁻¹ • (prepBot W g E q x ω * (prepTop W g E q x ω)⁻¹))
  | j + 2 => (blockSeq W q ω (j + 1) - (E : ℂ) • 1 -
      ((g : ℂ) ^ 2) • prepR W g E q x ω (j + 1))⁻¹

/-- The prepared normals of (9.2) [su:eq:transported-normal]: `v_1 = (X_1*)⁻¹ n_0` and
`v_j = R_j v_{j-1}` for `j ≥ 2` (`prepV … 0 = 0` is not used). -/
def prepV (W : ℕ) (g E : ℝ) (q : ℕ) (x : IsoFlag W) (ω : Ω W q) : ℕ → Fin W → ℂ
  | 0 => 0
  | 1 => ((prepTop W g E q x ω)ᴴ)⁻¹ *ᵥ prepNormal x
  | j + 2 => prepR W g E q x ω (j + 2) *ᵥ prepV W g E q x ω (j + 1)

/-- Chart entry at the four preparation steps: `X_1` and `V_j - E - g² R_{j-1}` (`j = 2, 3, 4`)
are invertible. -/
def PrepOK (W : ℕ) (g E : ℝ) (q : ℕ) (x : IsoFlag W) (ω : Ω W q) : Prop :=
  IsUnit (prepTop W g E q x ω) ∧ ∀ j, 1 ≤ j → j ≤ 3 →
    IsUnit (blockSeq W q ω j - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • prepR W g E q x ω j)

/-- A `2W × W` matrix is the stack of its top and bottom `W × W` blocks. -/
private theorem prepChart_colStack_top_bot {W : ℕ} (Q : Matrix (Fin 2 × Fin W) (Fin W) ℂ) :
    Q = colStack (Matrix.of fun α β => Q (0, α) β) (Matrix.of fun α β => Q (1, α) β) := by
  ext ⟨i, α⟩ β
  fin_cases i <;> simp [colStack]

/-- Right multiplication acts on both blocks of a stacked matrix. -/
private theorem prepChart_colStack_mul {W : ℕ} (X Y B : Matrix (Fin W) (Fin W) ℂ) :
    colStack X Y * B = colStack (X * B) (Y * B) := by
  ext ⟨i, α⟩ β
  fin_cases i <;> simp [colStack, Matrix.mul_apply]

/-- One transfer step on a stacked matrix (Definition 7.1 [def:transfer-matrices]):
`T(V) (X; Y) = (z X - g⁻¹ V X - Y; X)`. -/
private theorem prepChart_transferMat_mul_colStack {W : ℕ} (g : ℝ) (z : ℂ)
    (V X Y : Matrix (Fin W) (Fin W) ℂ) :
    transferMat g z V * colStack X Y = colStack (z • X - (g : ℂ)⁻¹ • (V * X) - Y) X := by
  ext ⟨i, α⟩ β
  fin_cases i
  · simp [transferMat, transferFree, colStack, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.smul_apply,
      Matrix.sub_apply]
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, mul_assoc, ← Finset.mul_sum]
    ring
  · simp [transferMat, transferFree, colStack, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- `(X; Y)* J_ph (X'; Y') = i Y* X' - i X* Y'`. -/
private theorem prepChart_colStack_phJ {W : ℕ} (X Y X' Y' : Matrix (Fin W) (Fin W) ℂ) :
    (colStack X Y)ᴴ * phJ W * colStack X' Y' =
      (Complex.I • (Yᴴ * X')) - Complex.I • (Xᴴ * Y') := by
  ext α β
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, colStack, phJ,
    Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.kroneckerMap_apply]
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, sub_eq_add_neg]
  exact Finset.sum_congr rfl fun x _ => by ring

open scoped ComplexOrder in
/-- A Hermitian idempotent matrix of trace `1` is `n n*` for a unit vector `n`. -/
private theorem prepChart_rankOne {W : ℕ} {R : Matrix (Fin W) (Fin W) ℂ} (hH : Rᴴ = R)
    (hI : R * R = R) (hT : R.trace = 1) :
    ∃ n : Fin W → ℂ, star n ⬝ᵥ n = 1 ∧ R = Matrix.vecMulVec n (star n) := by
  obtain ⟨j, hj⟩ : ∃ j, R j j ≠ 0 := by
    by_contra hcon
    have h0 : R.trace = 0 :=
      Finset.sum_eq_zero fun i _ => by by_contra h; exact hcon ⟨i, h⟩
    rw [hT] at h0
    exact one_ne_zero h0
  set c : Fin W → ℂ := fun a => R a j with hc
  have hRc : R *ᵥ c = c := by
    ext a
    simp only [Matrix.mulVec, dotProduct, hc]
    exact congrFun (congrFun hI a) j
  have hcc : star c ⬝ᵥ c = R j j := by
    have h1 : ∀ a, star (c a) = R j a := by
      intro a
      have := congrFun (congrFun hH j) a
      simpa [Matrix.conjTranspose_apply, hc] using this
    have h2 := congrFun (congrFun hI j) j
    rw [Matrix.mul_apply] at h2
    refine (Finset.sum_congr rfl fun a _ => ?_).trans h2
    rw [Pi.star_apply, h1 a]
  have hre : ((R j j).re : ℂ) = R j j := Matrix.IsHermitian.coe_re_apply_self hH j
  have hnn : 0 ≤ R j j := by rw [← hcc]; exact dotProduct_star_self_nonneg c
  have ht : 0 < (R j j).re := by
    have h1 : 0 ≤ (R j j).re := (Complex.nonneg_iff.mp hnn).1
    refine lt_of_le_of_ne h1 fun h0 => hj ?_
    rw [← hre, ← h0]; simp
  set t : ℝ := (R j j).re with htdef
  set l : ℂ := (((Real.sqrt t)⁻¹ : ℝ) : ℂ) with hl
  have hll : star l * l = (t : ℂ)⁻¹ := by
    rw [hl, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt ht.le]
    simp
  set n : Fin W → ℂ := l • c with hn
  have hnn1 : star n ⬝ᵥ n = 1 := by
    rw [hn, star_smul, smul_dotProduct, dotProduct_smul, hcc, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, hll, ← hre]
    exact inv_mul_cancel₀ (by exact_mod_cast ht.ne')
  refine ⟨n, hnn1, ?_⟩
  have hRn : R *ᵥ n = n := by rw [hn, Matrix.mulVec_smul, hRc]
  set K : Matrix (Fin W) (Fin W) ℂ := Matrix.vecMulVec n (star n) with hK
  have hKH : Kᴴ = K := by rw [hK, Matrix.conjTranspose_vecMulVec, star_star]
  have hKK : K * K = K := by
    rw [hK, Matrix.vecMulVec_mul_vecMulVec, hnn1, one_smul]
  have hRK : R * K = K := by rw [hK, Matrix.mul_vecMulVec, hRn]
  have hKR : K * R = K := by
    have := congrArg Matrix.conjTranspose hRK
    rwa [Matrix.conjTranspose_mul, hH, hKH] at this
  have hNH : (R - K)ᴴ = R - K := by rw [Matrix.conjTranspose_sub, hH, hKH]
  have hNN : (R - K) * (R - K) = R - K := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hI, hRK, hKR, hKK]
    abel
  have hNT : (R - K).trace = 0 := by
    rw [Matrix.trace_sub, hT, hK, Matrix.trace_vecMulVec, dotProduct_comm, hnn1, sub_self]
  have hN0 : R - K = 0 := by
    rw [← Matrix.trace_conjTranspose_mul_self_eq_zero_iff, hNH, hNN, hNT]
  exact sub_eq_zero.mp hN0

/-- A nonzero scalar multiple of an invertible matrix is invertible. -/
private theorem prepChart_isUnit_smul {W : ℕ} {M : Matrix (Fin W) (Fin W) ℂ} (hM : IsUnit M)
    {c : ℂ} (hc : c ≠ 0) : IsUnit (c • M) := by
  rw [Matrix.isUnit_iff_isUnit_det] at hM ⊢
  rw [Matrix.det_smul]
  exact (IsUnit.pow _ hc.isUnit).mul hM

/-- `M⁻¹ M = 1` for invertible `M`. -/
private theorem prepChart_inv_mul {W : ℕ} {M : Matrix (Fin W) (Fin W) ℂ} (h : IsUnit M) :
    M⁻¹ * M = 1 :=
  Matrix.nonsing_inv_mul M ((Matrix.isUnit_iff_isUnit_det M).mp h)

/-- `M M⁻¹ = 1` for invertible `M`. -/
private theorem prepChart_mul_inv {W : ℕ} {M : Matrix (Fin W) (Fin W) ℂ} (h : IsUnit M) :
    M * M⁻¹ = 1 :=
  Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp h)

/-- The conjugate transpose of an invertible matrix is invertible. -/
private theorem prepChart_isUnit_conjTranspose {W : ℕ} {M : Matrix (Fin W) (Fin W) ℂ}
    (h : IsUnit M) : IsUnit Mᴴ := by
  have := h.star
  rwa [Matrix.star_eq_conjTranspose] at this

/-- `R_1 = -g⁻¹ A X_1⁻¹` is Hermitian when `A* B = B* A` and `X_1 = z A - g⁻¹ V_1 A - B` is
invertible (proof of Lemma 9.1 [su:lem:preparation]). -/
private theorem prepChart_R1_herm {W : ℕ} {g : ℝ} {V0 A B X : Matrix (Fin W) (Fin W) ℂ}
    (hV0 : V0ᴴ = V0) (z : ℝ) (hAB : Aᴴ * B = Bᴴ * A)
    (hX : X = (z : ℂ) • A - (g : ℂ)⁻¹ • (V0 * A) - B) (hXu : IsUnit X) :
    (-((g : ℂ)⁻¹ • (A * X⁻¹))).IsHermitian := by
  have hXA : Aᴴ * X = Xᴴ * A := by
    rw [hX]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hV0,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hAB, Complex.star_def,
      Complex.conj_ofReal, map_inv₀, Complex.conj_ofReal, Matrix.mul_assoc]
  have hXi := prepChart_isUnit_conjTranspose hXu
  have key : (Xᴴ)⁻¹ * Aᴴ = A * X⁻¹ := by
    calc (Xᴴ)⁻¹ * Aᴴ = (Xᴴ)⁻¹ * (Aᴴ * (X * X⁻¹)) := by
          rw [prepChart_mul_inv hXu, Matrix.mul_one]
      _ = (Xᴴ)⁻¹ * (Aᴴ * X) * X⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (Xᴴ)⁻¹ * (Xᴴ * A) * X⁻¹ := by rw [hXA]
      _ = A * X⁻¹ := by rw [← Matrix.mul_assoc (Xᴴ)⁻¹, prepChart_inv_mul hXi, Matrix.one_mul]
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_nonsing_inv, key]
  simp

/-- The first transfer step in graph form (9.1) [su:eq:graph-input]:
`T_1 (A; B) = (I; -g R_1) X_1` with `R_1 = -g⁻¹ A X_1⁻¹`. -/
private theorem prepChart_graph1 {W : ℕ} {g : ℝ} (hg : g ≠ 0) {V0 A B X : Matrix (Fin W) (Fin W) ℂ}
    (z : ℝ) (hX : X = (z : ℂ) • A - (g : ℂ)⁻¹ • (V0 * A) - B) (hXu : IsUnit X) :
    transferMat g (z : ℂ) V0 * colStack A B = graphFrame g (-((g : ℂ)⁻¹ • (A * X⁻¹))) * X := by
  have hgc : (g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg
  rw [prepChart_transferMat_mul_colStack, ← hX, graphFrame, prepChart_colStack_mul, Matrix.one_mul]
  congr 1
  rw [smul_neg, neg_neg, smul_smul, mul_inv_cancel₀ hgc, one_smul, Matrix.mul_assoc,
    prepChart_inv_mul hXu, Matrix.mul_one]

/-- One transfer step on a graph frame (9.2) [su:eq:transported-normal], with `g z = E`. -/
private theorem prepChart_step_graph {W : ℕ} {g : ℝ} (hg : g ≠ 0) (z E : ℝ) (hgz : g * z = E)
    (V R : Matrix (Fin W) (Fin W) ℂ) (hM : IsUnit (V - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R)) :
    transferMat g (z : ℂ) V * graphFrame g R =
      graphFrame g (V - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R)⁻¹ *
        (-((g : ℂ)⁻¹ • (V - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R))) := by
  have h : (g : ℂ) * (z : ℂ) = (E : ℂ) := by exact_mod_cast hgz
  have := transferMat_mul_graphFrame_of_isUnit hg (z : ℂ) V R (by rw [h]; exact hM)
  rwa [h] at this

/-- `V - E - g² R` is Hermitian for Hermitian `V` and `R` and real `g`, `E`. -/
private theorem prepChart_M_herm {W : ℕ} {g E : ℝ} {V R : Matrix (Fin W) (Fin W) ℂ}
    (hV : Vᴴ = V) (hR : Rᴴ = R) :
    (V - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R)ᴴ = V - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hV, hR]
  simp [Complex.conj_ofReal]

/-- The transported normal (9.2) [su:eq:transported-normal]: if `n = N* ((-g)^j v)` then
`n = (c N)* ((-g)^{j+1} M⁻¹ v)` for `c = -g⁻¹ M` with `M` Hermitian and invertible. -/
private theorem prepChart_step_normal {W : ℕ} {g : ℝ} (hg : g ≠ 0) {M N : Matrix (Fin W) (Fin W) ℂ}
    (hM : IsUnit M) (hMH : Mᴴ = M) (n v : Fin W → ℂ) (j : ℕ)
    (h : n = Nᴴ *ᵥ ((-(g : ℂ)) ^ j • v)) :
    n = (-((g : ℂ)⁻¹ • M) * N)ᴴ *ᵥ ((-(g : ℂ)) ^ (j + 1) • (M⁻¹ *ᵥ v)) := by
  have hgc : (g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg
  have hc : (-((g : ℂ)⁻¹ • M))ᴴ = -((g : ℂ)⁻¹ • M) := by
    rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_smul, hMH]
    simp [Complex.conj_ofReal]
  rw [Matrix.conjTranspose_mul, hc, ← Matrix.mulVec_mulVec, Matrix.neg_mulVec,
    Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    prepChart_mul_inv hM, Matrix.one_mulVec, smul_smul, h]
  congr 1
  rw [← neg_smul]
  congr 1
  rw [pow_succ]
  field_simp

/-- Every input block `V_{k+1}` is Hermitian. -/
private theorem prepChart_blockSeq_herm (W q : ℕ) (ω : Ω W q) (k : ℕ) :
    (blockSeq W q ω k)ᴴ = blockSeq W q ω k := by
  unfold blockSeq
  split_ifs
  · exact (gueBlock_isHermitian W q ω _).eq
  · exact Matrix.conjTranspose_zero

/-- For an orthonormal frame `F` of the isotropic space `Y`, `(S F)* J_ph (S F) = 0`, because
`S* J_ph S = J` (proof of Lemma 9.1 [su:lem:preparation]). -/
private theorem prepChart_isotropic {W : ℕ} (x : IsoFlag W) {F : Matrix (Fin 2 × Fin W) (Fin W) ℂ}
    (hF1 : Fᴴ * F = 1) (hF2 : F * Fᴴ = x.1.2) :
    (freeConj W 0 * F)ᴴ * phJ W * (freeConj W 0 * F) = 0 := by
  have hJ : x.1.2 * isoJ W * x.1.2 = 0 := x.2.2.2.2.2.2
  have h0 : Fᴴ * isoJ W * F = 0 := by
    calc Fᴴ * isoJ W * F = (Fᴴ * (F * Fᴴ)) * isoJ W * ((F * Fᴴ) * F) := by
          rw [← Matrix.mul_assoc Fᴴ F Fᴴ, hF1, Matrix.one_mul, Matrix.mul_assoc F Fᴴ F, hF1,
            Matrix.mul_one]
      _ = Fᴴ * (F * Fᴴ * isoJ W * (F * Fᴴ)) * F := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hF2, hJ, Matrix.mul_zero, Matrix.zero_mul]
  calc (freeConj W 0 * F)ᴴ * phJ W * (freeConj W 0 * F)
      = Fᴴ * ((freeConj W 0)ᴴ * phJ W * freeConj W 0) * F := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 0 := by rw [conjTranspose_freeConj_mul_phJ_mul, h0]

/-- Every orthonormal frame `F` of `Y` has a unit normal `n_0` of `U` inside `Y`:
`F* P_U F = 1 - n_0 n_0*`. -/
private theorem prepChart_normal_exists {W : ℕ} [NeZero W] (x : IsoFlag W)
    {F : Matrix (Fin 2 × Fin W) (Fin W) ℂ} (hF2 : F * Fᴴ = x.1.2) :
    ∃ n : Fin W → ℂ, star n ⬝ᵥ n = 1 ∧
      Fᴴ * x.1.1 * F = 1 - Matrix.vecMulVec n (star n) := by
  obtain ⟨⟨hUH, hUU, hUT, -⟩, hYH, -, -, hYU, -⟩ := x.2
  have hUY : x.1.1 * x.1.2 = x.1.1 := by
    have := congrArg Matrix.conjTranspose hYU
    rwa [Matrix.conjTranspose_mul, hUH.eq, hYH.eq] at this
  have hQH : (Fᴴ * x.1.1 * F)ᴴ = Fᴴ * x.1.1 * F := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hUH.eq, Matrix.mul_assoc]
  have hQQ : (Fᴴ * x.1.1 * F) * (Fᴴ * x.1.1 * F) = Fᴴ * x.1.1 * F := by
    calc (Fᴴ * x.1.1 * F) * (Fᴴ * x.1.1 * F)
        = Fᴴ * (x.1.1 * (F * Fᴴ) * x.1.1) * F := by simp only [Matrix.mul_assoc]
      _ = Fᴴ * (x.1.1 * x.1.1) * F := by rw [hF2, hUY]
      _ = Fᴴ * x.1.1 * F := by rw [hUU]
  have hQT : (Fᴴ * x.1.1 * F).trace = ((W - 1 : ℕ) : ℂ) := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hF2, hYU, hUT]
  have hW1 : 1 ≤ W := Nat.one_le_iff_ne_zero.mpr (NeZero.ne W)
  have hR := prepChart_rankOne (R := 1 - Fᴴ * x.1.1 * F)
    (by rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hQH])
    (by simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul, hQQ]
        abel)
    (by rw [Matrix.trace_sub, Matrix.trace_one, hQT, Fintype.card_fin, Nat.cast_sub hW1]
        simp)
  obtain ⟨n, hn, hQ⟩ := hR
  exact ⟨n, hn, by rw [← hQ, sub_sub_cancel]⟩

/-- The blocks of `T_1 S F_Y` for `S F_Y = (A; B)`: `X_1 = z A - g⁻¹ V_1 A - B` and `Y_1 = A`. -/
private theorem prepChart_topBot {W q : ℕ} (g E : ℝ) (x : IsoFlag W) (ω : Ω W q)
    {A B : Matrix (Fin W) (Fin W) ℂ} (hSF : freeConj W 0 * prepFrame x = colStack A B) :
    prepTop W g E q x ω = ((max 1 g * E / g : ℝ) : ℂ) • A -
        (g : ℂ)⁻¹ • (blockSeq W q ω 0 * A) - B ∧ prepBot W g E q x ω = A := by
  have hprod1 : transferProd g ((max 1 g * E / g : ℝ) : ℂ) (blockSeq W q ω) 1 * colStack A B =
      colStack (((max 1 g * E / g : ℝ) : ℂ) • A - (g : ℂ)⁻¹ • (blockSeq W q ω 0 * A) - B) A := by
    rw [show transferProd g ((max 1 g * E / g : ℝ) : ℂ) (blockSeq W q ω) 1 =
      transferMat g ((max 1 g * E / g : ℝ) : ℂ) (blockSeq W q ω 0) from by simp [transferProd],
      prepChart_transferMat_mul_colStack]
  constructor
  · unfold prepTop
    rw [Matrix.mul_assoc, hSF, hprod1]
    ext α β
    simp [colStack]
  · unfold prepBot
    rw [Matrix.mul_assoc, hSF, hprod1]
    ext α β
    simp [colStack]

/-- If an orthonormal frame of `Y` exists, `prepFrame x` is one. -/
private theorem prepChart_frame_spec {W : ℕ} (x : IsoFlag W)
    (hex : ∃ F : Matrix (Fin 2 × Fin W) (Fin W) ℂ, Fᴴ * F = 1 ∧ F * Fᴴ = x.1.2) :
    (prepFrame x)ᴴ * prepFrame x = 1 ∧ prepFrame x * (prepFrame x)ᴴ = x.1.2 := by
  have hFd : prepFrame x = hex.choose := by
    unfold prepFrame
    split
    · rfl
    · rename_i hh
      exact absurd hex hh
  rw [hFd]
  exact hex.choose_spec

/-- The frame recursion of the proof of Lemma 9.1 [su:lem:preparation]: for `j = 1, …, 4`,
`T_j ⋯ T_1 S F_Y = (I; -g R_j) N_j` with `N_j` invertible, `R_j` Hermitian, and the normal `n_0`
equals `N_j* ((-g)^{j-1} v_j)` ((9.2) [su:eq:transported-normal]) -/
private theorem prepChart_chain {W q : ℕ} {g E : ℝ} (hg : 0 < g) (hg1 : g ≤ 1)
    (x : IsoFlag W) {ω : Ω W q} (h : PrepOK W g E q x ω)
    (hiso : (freeConj W 0 * prepFrame x)ᴴ * phJ W * (freeConj W 0 * prepFrame x) = 0) :
    ∀ j, 1 ≤ j → j ≤ 4 → ∃ N : Matrix (Fin W) (Fin W) ℂ, IsUnit N ∧
      transferProd g ((max 1 g * E / g : ℝ) : ℂ) (blockSeq W q ω) j *
          (freeConj W 0 * prepFrame x) = graphFrame g (prepR W g E q x ω j) * N ∧
      prepNormal x = Nᴴ *ᵥ ((-(g : ℂ)) ^ (j - 1) • prepV W g E q x ω j) ∧
      (prepR W g E q x ω j).IsHermitian := by
  have hg0 : g ≠ 0 := hg.ne'
  have hgc : (g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg0
  have hV := prepChart_blockSeq_herm W q ω
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = max 1 g * E / g := ⟨_, rfl⟩
  have hgz : g * z = E := by
    rw [hz, max_eq_left hg1]
    field_simp
  obtain ⟨A, B, hSF⟩ : ∃ A B : Matrix (Fin W) (Fin W) ℂ,
      freeConj W 0 * prepFrame x = colStack A B := ⟨_, _, prepChart_colStack_top_bot _⟩
  rw [hSF, prepChart_colStack_phJ] at hiso
  have hAB : Aᴴ * B = Bᴴ * A := by
    have := sub_eq_zero.mp hiso
    exact (smul_right_injective _ Complex.I_ne_zero this).symm
  obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin W) (Fin W) ℂ,
      X = (z : ℂ) • A - (g : ℂ)⁻¹ • (blockSeq W q ω 0 * A) - B := ⟨_, rfl⟩
  have hTB := prepChart_topBot g E x ω hSF
  rw [← hz] at hTB
  have hTop : prepTop W g E q x ω = X := by rw [hTB.1, hX]
  have hBot : prepBot W g E q x ω = A := hTB.2
  have hXu : IsUnit X := hTop ▸ h.1
  have hR1 : prepR W g E q x ω 1 = -((g : ℂ)⁻¹ • (A * X⁻¹)) := by
    change -((g : ℂ)⁻¹ • (prepBot W g E q x ω * (prepTop W g E q x ω)⁻¹)) = _
    rw [hTop, hBot]
  rw [← hz, hSF]
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro _
    refine ⟨X, hXu, ?_, ?_, ?_⟩
    · rw [hR1, show transferProd g (z : ℂ) (blockSeq W q ω) 1 =
        transferMat g (z : ℂ) (blockSeq W q ω 0) from by simp [transferProd]]
      exact prepChart_graph1 hg0 z hX hXu
    · have hXi : IsUnit Xᴴ := prepChart_isUnit_conjTranspose hXu
      have hV1 : prepV W g E q x ω 1 = (Xᴴ)⁻¹ *ᵥ prepNormal x := by
        change ((prepTop W g E q x ω)ᴴ)⁻¹ *ᵥ prepNormal x = _
        rw [hTop]
      rw [hV1, Nat.sub_self, pow_zero, one_smul, Matrix.mulVec_mulVec, prepChart_mul_inv hXi,
        Matrix.one_mulVec]
    · rw [hR1]
      exact prepChart_R1_herm (prepChart_blockSeq_herm W q ω 0) z hAB hX hXu
  | succ j hj ih =>
    intro hj4
    obtain ⟨N, hNu, hNeq, hNn, hNH⟩ := ih (by omega)
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hPrep := h.2 (j' + 1) (by omega) (by omega)
    have hRdef : prepR W g E q x ω (j' + 1 + 1) =
        (blockSeq W q ω (j' + 1) - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • prepR W g E q x ω (j' + 1))⁻¹ :=
      rfl
    have hVdef : prepV W g E q x ω (j' + 1 + 1) =
        prepR W g E q x ω (j' + 1 + 1) *ᵥ prepV W g E q x ω (j' + 1) := rfl
    have hMH := prepChart_M_herm (g := g) (E := E) (hV (j' + 1)) hNH.eq
    refine ⟨-((g : ℂ)⁻¹ • (blockSeq W q ω (j' + 1) - (E : ℂ) • 1 -
        ((g : ℂ) ^ 2) • prepR W g E q x ω (j' + 1))) * N, ?_, ?_, ?_, ?_⟩
    · rw [← neg_smul]
      exact (prepChart_isUnit_smul hPrep (neg_ne_zero.mpr (inv_ne_zero hgc))).mul hNu
    · change transferMat g (z : ℂ) (blockSeq W q ω (j' + 1)) *
          transferProd g (z : ℂ) (blockSeq W q ω) (j' + 1) * colStack A B = _
      rw [Matrix.mul_assoc, hNeq, ← Matrix.mul_assoc,
        prepChart_step_graph hg0 z E hgz _ _ hPrep, Matrix.mul_assoc, ← hRdef]
    · have := prepChart_step_normal hg0 hPrep hMH (prepNormal x)
        (prepV W g E q x ω (j' + 1)) j' (by simpa using hNn)
      rw [hVdef, hRdef]
      simpa using this
    · rw [hRdef]
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_nonsing_inv, hMH]


/-- `P_U = F (F* P_U F) F*` for an orthonormal frame `F` of `Y`. -/
private theorem prepChart_flag_proj {W : ℕ} (x : IsoFlag W) {F : Matrix (Fin 2 × Fin W) (Fin W) ℂ}
    (hF2 : F * Fᴴ = x.1.2) : x.1.1 = F * (Fᴴ * x.1.1 * F) * Fᴴ := by
  obtain ⟨⟨hUH, -, -, -⟩, hYH, -, -, hYU, -⟩ := x.2
  have hUY : x.1.1 * x.1.2 = x.1.1 := by
    have := congrArg Matrix.conjTranspose hYU
    rwa [Matrix.conjTranspose_mul, hUH.eq, hYH.eq] at this
  calc x.1.1 = x.1.2 * x.1.1 * x.1.2 := by rw [hYU, hUY]
    _ = F * (Fᴴ * x.1.1 * F) * Fᴴ := by rw [← hF2]; simp only [Matrix.mul_assoc]

/-- `(a b*) u = (b ⬝ᵥ u) a` in the form of `Matrix.vecMulVec`. -/
private theorem prepChart_vecMulVec_mulVec {W : ℕ} (a b u : Fin W → ℂ) :
    Matrix.vecMulVec a b *ᵥ u = (b ⬝ᵥ u) • a := by
  rw [Matrix.vecMulVec_mulVec]
  simp

/-- Equal ranges of `H₁` and `H₂` give equal ranges of `G H₁` and `G H₂`. -/
private theorem prepChart_range_mul {ι κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂]
    {W : ℕ} (G : Matrix ι (Fin W) ℂ) (H₁ : Matrix (Fin W) κ₁ ℂ) (H₂ : Matrix (Fin W) κ₂ ℂ)
    (h : LinearMap.range H₁.mulVecLin = LinearMap.range H₂.mulVecLin) :
    LinearMap.range (G * H₁).mulVecLin = LinearMap.range (G * H₂).mulVecLin := by
  rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, LinearMap.range_comp, LinearMap.range_comp, h]

/-- `N F*` has full range for invertible `N` and `F* F = 1`. -/
private theorem prepChart_range_all {κ : Type*} [Fintype κ] {W : ℕ} {N : Matrix (Fin W) (Fin W) ℂ}
    {F : Matrix κ (Fin W) ℂ} (hNu : IsUnit N) (hF1 : Fᴴ * F = 1) :
    LinearMap.range (N * Fᴴ).mulVecLin =
      LinearMap.range (1 : Matrix (Fin W) (Fin W) ℂ).mulVecLin := by
  ext z
  simp only [LinearMap.mem_range, Matrix.mulVecLin_apply, Matrix.one_mulVec]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨N *ᵥ (Fᴴ *ᵥ y), by rw [Matrix.mulVec_mulVec]⟩
  · rintro ⟨y, rfl⟩
    refine ⟨F *ᵥ (N⁻¹ *ᵥ y), ?_⟩
    have h1 : N * Fᴴ * F * N⁻¹ = 1 := by
      rw [Matrix.mul_assoc N, hF1, Matrix.mul_one, prepChart_mul_inv hNu]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

open scoped ComplexOrder in
/-- The range of the orthogonal projection onto `v⊥`. -/
private theorem prepChart_mem_range_proj {W : ℕ} {v : Fin W → ℂ} (hv : v ≠ 0) (z : Fin W → ℂ) :
    z ∈ LinearMap.range
        (1 - (star v ⬝ᵥ v)⁻¹ • Matrix.vecMulVec v (star v)).mulVecLin ↔ star v ⬝ᵥ z = 0 := by
  have hs : star v ⬝ᵥ v ≠ 0 := fun h0 => hv (dotProduct_star_self_eq_zero.mp h0)
  have hP : ∀ y : Fin W → ℂ, (1 - (star v ⬝ᵥ v)⁻¹ • Matrix.vecMulVec v (star v)) *ᵥ y =
      y - ((star v ⬝ᵥ v)⁻¹ * (star v ⬝ᵥ y)) • v := by
    intro y
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, prepChart_vecMulVec_mulVec,
      smul_smul]
  have hP0 : ∀ y : Fin W → ℂ,
      star v ⬝ᵥ ((1 - (star v ⬝ᵥ v)⁻¹ • Matrix.vecMulVec v (star v)) *ᵥ y) = 0 := by
    intro y
    rw [hP, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    have : (star v ⬝ᵥ v)⁻¹ * (star v ⬝ᵥ y) * (star v ⬝ᵥ v) = star v ⬝ᵥ y := by
      field_simp
    rw [this, sub_self]
  simp only [LinearMap.mem_range, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨y, rfl⟩
    exact hP0 y
  · intro hz
    refine ⟨z, ?_⟩
    rw [hP, hz, mul_zero, zero_smul, sub_zero]

open scoped ComplexOrder in
/-- `ran (N (1 - n n*) F*)` is the orthogonal complement of `v` when `n = N* (c v)` and `c ≠ 0` is
real. -/
private theorem prepChart_range_U {κ : Type*} [Fintype κ] {W : ℕ} {N : Matrix (Fin W) (Fin W) ℂ}
    {F : Matrix κ (Fin W) ℂ} (hNu : IsUnit N) (hF1 : Fᴴ * F = 1) {n v : Fin W → ℂ}
    (hn1 : star n ⬝ᵥ n = 1) {c : ℂ} (hc : c ≠ 0) (hcs : star c = c)
    (hnv : n = Nᴴ *ᵥ (c • v)) (hv : v ≠ 0) :
    LinearMap.range (N * (1 - Matrix.vecMulVec n (star n)) * Fᴴ).mulVecLin =
      LinearMap.range
        (1 - (star v ⬝ᵥ v)⁻¹ • Matrix.vecMulVec v (star v)).mulVecLin := by
  have kf : ∀ u, star n ⬝ᵥ u = c * (star v ⬝ᵥ (N *ᵥ u)) := by
    intro u
    rw [hnv, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, star_smul, hcs,
      ← Matrix.dotProduct_mulVec, smul_dotProduct, smul_eq_mul]
  have hProj : ∀ u : Fin W → ℂ, (1 - Matrix.vecMulVec n (star n)) *ᵥ u =
      u - (star n ⬝ᵥ u) • n := by
    intro u
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, prepChart_vecMulVec_mulVec]
  have hp0 : ∀ u : Fin W → ℂ, star n ⬝ᵥ ((1 - Matrix.vecMulVec n (star n)) *ᵥ u) = 0 := by
    intro u
    rw [hProj, dotProduct_sub, dotProduct_smul, smul_eq_mul, hn1, mul_one, sub_self]
  have hmem : ∀ z : Fin W → ℂ, z ∈ LinearMap.range
      (N * (1 - Matrix.vecMulVec n (star n)) * Fᴴ).mulVecLin ↔ star v ⬝ᵥ z = 0 := by
    intro z
    simp only [LinearMap.mem_range, Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨y, rfl⟩
      have h1 : (N * (1 - Matrix.vecMulVec n (star n)) * Fᴴ) *ᵥ y =
          N *ᵥ ((1 - Matrix.vecMulVec n (star n)) *ᵥ (Fᴴ *ᵥ y)) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      rw [h1]
      have := kf ((1 - Matrix.vecMulVec n (star n)) *ᵥ (Fᴴ *ᵥ y))
      rw [hp0] at this
      exact (mul_eq_zero.mp this.symm).resolve_left hc
    · intro hz
      refine ⟨F *ᵥ (N⁻¹ *ᵥ z), ?_⟩
      have hu : star n ⬝ᵥ (N⁻¹ *ᵥ z) = 0 := by
        rw [kf, Matrix.mulVec_mulVec, prepChart_mul_inv hNu, Matrix.one_mulVec, hz, mul_zero]
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc _ Fᴴ F, hF1, Matrix.mul_one,
        ← Matrix.mulVec_mulVec, hProj, hu, zero_smul, sub_zero, Matrix.mulVec_mulVec,
        prepChart_mul_inv hNu, Matrix.one_mulVec]
  exact Submodule.ext fun z => (hmem z).trans (prepChart_mem_range_proj hv z).symm


/-- Where the four preparation steps are invertible, `(R_4, v_4) = (prepR … 4, prepV … 4)` is a
prepared chart (9.1) [su:eq:graph-input] for `0 < g ≤ 1` (proof of Lemma 9.1
[su:lem:preparation]). -/
theorem isPrepChart_of_prepOK {W q : ℕ} [NeZero W] {g E : ℝ} (hg : 0 < g) (hg1 : g ≤ 1)
    (x : IsoFlag W) {ω : Ω W q} (h : PrepOK W g E q x ω) :
    IsPrepChart W g E q x ω (prepR W g E q x ω 4) (prepV W g E q x ω 4) := by
  have hg0 : g ≠ 0 := hg.ne'
  have hFex : ∃ F : Matrix (Fin 2 × Fin W) (Fin W) ℂ, Fᴴ * F = 1 ∧ F * Fᴴ = x.1.2 := by
    by_contra hno
    have h0 : prepFrame x = 0 := by
      unfold prepFrame
      split
      · rename_i hh
        exact absurd hh hno
      · rfl
    have h1 : prepTop W g E q x ω = 0 := by
      unfold prepTop
      rw [h0]
      ext α β
      simp
    exact not_isUnit_zero (h1 ▸ h.1)
  obtain ⟨hF1, hF2⟩ := prepChart_frame_spec x hFex
  have hNex : ∃ n : Fin W → ℂ, star n ⬝ᵥ n = 1 ∧
      (prepFrame x)ᴴ * x.1.1 * prepFrame x = 1 - Matrix.vecMulVec n (star n) :=
    prepChart_normal_exists x hF2
  have hNd : prepNormal x = hNex.choose := by
    unfold prepNormal
    split
    · rfl
    · rename_i hh
      exact absurd hNex hh
  have hn1 : star (prepNormal x) ⬝ᵥ prepNormal x = 1 := by
    rw [hNd]
    exact hNex.choose_spec.1
  have hn2 : (prepFrame x)ᴴ * x.1.1 * prepFrame x =
      1 - Matrix.vecMulVec (prepNormal x) (star (prepNormal x)) := by
    rw [hNd]
    exact hNex.choose_spec.2
  obtain ⟨N, hNu, hNeq, hNn, hRH⟩ :=
    prepChart_chain hg hg1 x h (prepChart_isotropic x hF1 hF2) 4 (by norm_num) le_rfl
  have hNn3 : prepNormal x =
      Nᴴ *ᵥ ((-(g : ℂ)) ^ 3 • prepV W g E q x ω 4) := hNn
  have hc : (-(g : ℂ)) ^ 3 ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hg0))
  have hcs : star ((-(g : ℂ)) ^ 3) = (-(g : ℂ)) ^ 3 := by
    simp [Complex.conj_ofReal]
  have hv : prepV W g E q x ω 4 ≠ 0 := by
    intro hv0
    rw [hv0, smul_zero, Matrix.mulVec_zero] at hNn3
    rw [hNn3] at hn1
    simp at hn1
  have hY : prepMat W g E q ω * x.1.2 =
      graphFrame g (prepR W g E q x ω 4) * (N * (prepFrame x)ᴴ) := by
    calc prepMat W g E q ω * x.1.2 = prepMat W g E q ω * (prepFrame x * (prepFrame x)ᴴ) := by
          rw [hF2]
      _ = (transferProd g ((max 1 g * E / g : ℝ) : ℂ) (blockSeq W q ω) 4 *
            (freeConj W 0 * prepFrame x)) * (prepFrame x)ᴴ := by
          unfold prepMat
          simp only [Matrix.mul_assoc]
      _ = graphFrame g (prepR W g E q x ω 4) * (N * (prepFrame x)ᴴ) := by
          rw [hNeq, Matrix.mul_assoc]
  have hU : prepMat W g E q ω * x.1.1 =
      graphFrame g (prepR W g E q x ω 4) *
        (N * (1 - Matrix.vecMulVec (prepNormal x) (star (prepNormal x))) * (prepFrame x)ᴴ) := by
    calc prepMat W g E q ω * x.1.1
        = prepMat W g E q ω * (prepFrame x * ((prepFrame x)ᴴ * x.1.1 * prepFrame x) *
            (prepFrame x)ᴴ) := by
          rw [← prepChart_flag_proj x hF2]
      _ = (transferProd g ((max 1 g * E / g : ℝ) : ℂ) (blockSeq W q ω) 4 *
            (freeConj W 0 * prepFrame x)) *
            (((prepFrame x)ᴴ * x.1.1 * prepFrame x) * (prepFrame x)ᴴ) := by
          unfold prepMat
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hNeq, hn2]
          simp only [Matrix.mul_assoc]
  refine ⟨hRH, hv, ?_, ?_⟩
  · rw [hY]
    calc _ = LinearMap.range (graphFrame g (prepR W g E q x ω 4) *
          (1 : Matrix (Fin W) (Fin W) ℂ)).mulVecLin :=
          prepChart_range_mul _ _ _ (prepChart_range_all hNu hF1)
      _ = _ := by rw [Matrix.mul_one]
  · rw [hU]
    exact prepChart_range_mul _ _ _
      (prepChart_range_U hNu hF1 hn1 hc hcs hNn3 hv)


end LSBA
