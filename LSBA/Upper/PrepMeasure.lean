import LSBA.Upper.PrepChart
import LSBA.Gauss.GUEFirstRow
import LSBA.Gauss.FreshEvent

/-!
# The preparation data as functions of the preparation blocks

Proof of Lemma 9.1 [su:lem:preparation]. Chart entry holds almost surely for every flag and
energy: `det X_1` is a polynomial in the entries of `V_1` that does not vanish at
`V_1 = E + g z_0` for a real `z_0` with `det(z_0 A + B) ≠ 0` (which exists because `iA + B` has
trivial kernel, by `A* B = B* A` and full rank), and each later step inverts a GUE block shifted by
a Hermitian matrix fixed before it. The preparation indicator of a measurable set `G` of prepared
data, `1` on `PrepOK ∩ {(R_4, v_4) ∈ G}`, together with `R_4` and `v_4`, gives the data
`(pre, R_4, v_4)` of Lemma 9.3 [su:lem:chosen-generator]: measurable functions of the four
preparation blocks, with the prepared chart (9.1) [su:eq:graph-input] where `pre = 1`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- A Hermitian idempotent of trace `W` is `F F*` for a matrix `F` with `F* F = 1`. -/
private theorem prepMeasure_frame_exists {n : Type*} [Fintype n] {W : ℕ}
    {P : Matrix n n ℂ} (hH : Pᴴ = P) (hI : P * P = P) (hT : P.trace = (W : ℂ)) :
    ∃ F : Matrix n (Fin W) ℂ, Fᴴ * F = 1 ∧ F * Fᴴ = P := by
  have hA : P.IsHermitian := hH
  set u := hA.eigenvectorBasis with hu
  set e : n → ℝ := hA.eigenvalues with he
  have hspec : ∀ p q, P p q = ∑ i, u i p * (e i : ℂ) * star (u i q) := by
    intro p q
    have := congrFun (congrFun hA.spectral_theorem p) q
    rw [Unitary.conjStarAlgAut_apply] at this
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, Function.comp_apply] at this
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_ite, Matrix.star_apply]
    rfl
  have hPu : ∀ i, P *ᵥ ⇑(u i) = (e i : ℂ) • ⇑(u i) := by
    intro i
    have := hA.mulVec_eigenvectorBasis i
    rw [this, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have hu0 : ∀ i, ∃ p, u i p ≠ 0 := by
    intro i
    by_contra hcon
    have : u i = 0 := by
      ext p
      exact not_not.mp fun h => hcon ⟨p, h⟩
    exact u.orthonormal.ne_zero i this
  have heig : ∀ i, e i = 0 ∨ e i = 1 := by
    intro i
    obtain ⟨p, hp⟩ := hu0 i
    have h1 : P *ᵥ (P *ᵥ ⇑(u i)) = P *ᵥ ⇑(u i) := by rw [Matrix.mulVec_mulVec, hI]
    rw [hPu, Matrix.mulVec_smul, hPu, smul_smul] at h1
    have h2 := congrFun h1 p
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    have h3 : (e i : ℂ) * (e i : ℂ) = e i := by
      refine mul_right_cancel₀ hp ?_
      rw [h2]
    have h4 : e i * e i = e i := by exact_mod_cast h3
    by_cases h : e i = 0
    · exact Or.inl h
    · exact Or.inr (mul_left_cancel₀ h (by linarith : e i * e i = e i * 1))
  set s : Finset n := Finset.univ.filter fun i => e i = 1 with hs
  have hcard : s.card = W := by
    have h1 := hA.trace_eq_sum_eigenvalues
    rw [hT] at h1
    have h2 : ∑ i, (e i : ℂ) = (s.card : ℂ) := by
      rw [hs, Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rcases heig i with h | h <;> simp [h]
    exact_mod_cast (h1.trans h2).symm
  let σ : {i // i ∈ s} ≃ Fin W :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hcard])
  refine ⟨Matrix.of fun p β => u (σ.symm β).1 p, ?_, ?_⟩
  · ext β γ
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
    have := (orthonormal_iff_ite.mp u.orthonormal) (σ.symm β).1 (σ.symm γ).1
    rw [EuclideanSpace.inner_eq_star_dotProduct] at this
    simp only [dotProduct] at this
    by_cases hβγ : β = γ
    · subst hβγ
      simpa [mul_comm] using this
    · have hne : (σ.symm β).1 ≠ (σ.symm γ).1 := fun h => hβγ (σ.symm.injective (Subtype.ext h))
      simp only [hne, hβγ, ↓reduceIte] at this ⊢
      simpa [mul_comm] using this
  · ext p q
    rw [hspec]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
    have h1 : ∑ j : Fin W, (u (σ.symm j).1).ofLp p * star ((u (σ.symm j).1).ofLp q) =
        ∑ i : {i // i ∈ s}, (u i.1).ofLp p * star ((u i.1).ofLp q) :=
      Equiv.sum_comp σ.symm (fun i : {i // i ∈ s} => (u i.1).ofLp p * star ((u i.1).ofLp q))
    rw [h1, Finset.sum_coe_sort s (fun i => (u i).ofLp p * star ((u i).ofLp q)), hs,
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases heig i with h | h <;> simp [h]

/-- The projection `P_Y` of a flag has an orthonormal frame. -/
private theorem prepMeasure_flag_frame {W : ℕ} (x : IsoFlag W) :
    ∃ F : Matrix (Fin 2 × Fin W) (Fin W) ℂ, Fᴴ * F = 1 ∧ F * Fᴴ = x.1.2 :=
  prepMeasure_frame_exists x.2.2.1.eq x.2.2.2.1 x.2.2.2.2.1

/-- `prepFrame x` is an orthonormal frame of `Y`. -/
private theorem prepMeasure_frame_spec {W : ℕ} (x : IsoFlag W) :
    (prepFrame x)ᴴ * prepFrame x = 1 ∧ prepFrame x * (prepFrame x)ᴴ = x.1.2 := by
  have hex := prepMeasure_flag_frame x
  have hFd : prepFrame x = hex.choose := by
    simp only [prepFrame, hex, ↓reduceDIte]
  rw [hFd]
  exact hex.choose_spec

/-- A `2W × W` matrix is the stack of its top and bottom `W × W` blocks. -/
private theorem prepMeasure_colStack_top_bot {W : ℕ} (Q : Matrix (Fin 2 × Fin W) (Fin W) ℂ) :
    Q = colStack (Matrix.of fun α β => Q (0, α) β) (Matrix.of fun α β => Q (1, α) β) := by
  ext ⟨i, α⟩ β
  fin_cases i <;> simp [colStack]

/-- One transfer step on a stacked matrix (Definition 7.1 [def:transfer-matrices]):
`T(V) (X; Y) = (z X - g⁻¹ V X - Y; X)`. -/
private theorem prepMeasure_transferMat_mul_colStack {W : ℕ} (g : ℝ) (z : ℂ)
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
private theorem prepMeasure_colStack_phJ {W : ℕ} (X Y X' Y' : Matrix (Fin W) (Fin W) ℂ) :
    (colStack X Y)ᴴ * phJ W * colStack X' Y' =
      (Complex.I • (Yᴴ * X')) - Complex.I • (Xᴴ * Y') := by
  ext α β
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, colStack, phJ,
    Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.kroneckerMap_apply]
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, sub_eq_add_neg]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- `M⁻¹ M = 1` for invertible `M`. -/
private theorem prepMeasure_inv_mul {W : ℕ} {M : Matrix (Fin W) (Fin W) ℂ} (h : IsUnit M) :
    M⁻¹ * M = 1 :=
  Matrix.nonsing_inv_mul M ((Matrix.isUnit_iff_isUnit_det M).mp h)

/-- `M M⁻¹ = 1` for invertible `M`. -/
private theorem prepMeasure_mul_inv {W : ℕ} {M : Matrix (Fin W) (Fin W) ℂ} (h : IsUnit M) :
    M * M⁻¹ = 1 :=
  Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp h)

/-- The conjugate transpose of an invertible matrix is invertible. -/
private theorem prepMeasure_isUnit_conjTranspose {W : ℕ} {M : Matrix (Fin W) (Fin W) ℂ}
    (h : IsUnit M) : IsUnit Mᴴ := by
  have := h.star
  rwa [Matrix.star_eq_conjTranspose] at this

/-- `R_1 = -g⁻¹ A X_1⁻¹` is Hermitian when `A* B = B* A` and `X_1 = z A - g⁻¹ V_1 A - B` is
invertible, and `R_1 = 0` when `X_1` is not invertible (proof of Lemma 9.1
[su:lem:preparation]). -/
private theorem prepMeasure_R1_herm {W : ℕ} {g : ℝ} {V0 A B X : Matrix (Fin W) (Fin W) ℂ}
    (hV0 : V0ᴴ = V0) (z : ℝ) (hAB : Aᴴ * B = Bᴴ * A)
    (hX : X = (z : ℂ) • A - (g : ℂ)⁻¹ • (V0 * A) - B) :
    (-((g : ℂ)⁻¹ • (A * X⁻¹))).IsHermitian := by
  by_cases hXu : IsUnit X
  · have hXA : Aᴴ * X = Xᴴ * A := by
      rw [hX]
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
        hV0, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hAB,
        Complex.star_def, Complex.conj_ofReal, map_inv₀, Complex.conj_ofReal, Matrix.mul_assoc]
    have hXi := prepMeasure_isUnit_conjTranspose hXu
    have key : (Xᴴ)⁻¹ * Aᴴ = A * X⁻¹ := by
      calc (Xᴴ)⁻¹ * Aᴴ = (Xᴴ)⁻¹ * (Aᴴ * (X * X⁻¹)) := by
            rw [prepMeasure_mul_inv hXu, Matrix.mul_one]
        _ = (Xᴴ)⁻¹ * (Aᴴ * X) * X⁻¹ := by simp only [Matrix.mul_assoc]
        _ = (Xᴴ)⁻¹ * (Xᴴ * A) * X⁻¹ := by rw [hXA]
        _ = A * X⁻¹ := by
          rw [← Matrix.mul_assoc (Xᴴ)⁻¹, prepMeasure_inv_mul hXi, Matrix.one_mul]
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_nonsing_inv, key]
    simp
  · rw [Matrix.nonsing_inv_apply_not_isUnit _
      (fun h => hXu ((Matrix.isUnit_iff_isUnit_det X).mpr h))]
    simp [Matrix.IsHermitian]

/-- For an orthonormal frame `F` of the isotropic space `Y`, `(S F)* J_ph (S F) = 0`, because
`S* J_ph S = J` (proof of Lemma 9.1 [su:lem:preparation]). -/
private theorem prepMeasure_isotropic {W : ℕ} (x : IsoFlag W)
    {F : Matrix (Fin 2 × Fin W) (Fin W) ℂ} (hF1 : Fᴴ * F = 1) (hF2 : F * Fᴴ = x.1.2) :
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

/-- The blocks of `T_1 S F_Y` for `S F_Y = (A; B)`: `X_1 = z A - g⁻¹ V_1 A - B` and `Y_1 = A`. -/
private theorem prepMeasure_topBot {W q : ℕ} (g E : ℝ) (x : IsoFlag W) (ω : Ω W q)
    {A B : Matrix (Fin W) (Fin W) ℂ} (hSF : freeConj W 0 * prepFrame x = colStack A B) :
    prepTop W g E q x ω = ((max 1 g * E / g : ℝ) : ℂ) • A -
        (g : ℂ)⁻¹ • (blockSeq W q ω 0 * A) - B ∧ prepBot W g E q x ω = A := by
  have hprod1 : transferProd g ((max 1 g * E / g : ℝ) : ℂ) (blockSeq W q ω) 1 * colStack A B =
      colStack (((max 1 g * E / g : ℝ) : ℂ) • A - (g : ℂ)⁻¹ • (blockSeq W q ω 0 * A) - B) A := by
    rw [show transferProd g ((max 1 g * E / g : ℝ) : ℂ) (blockSeq W q ω) 1 =
      transferMat g ((max 1 g * E / g : ℝ) : ℂ) (blockSeq W q ω 0) from by simp [transferProd],
      prepMeasure_transferMat_mul_colStack]
  constructor
  · unfold prepTop
    rw [Matrix.mul_assoc, hSF, hprod1]
    ext α β
    simp [colStack]
  · unfold prepBot
    rw [Matrix.mul_assoc, hSF, hprod1]
    ext α β
    simp [colStack]

open scoped ComplexOrder in
/-- If `(S F)* J_ph (S F) = 0` for `S F = (A; B)` and `F* F = 1`, then `i A + B` has trivial kernel
(proof of Lemma 9.1 [su:lem:preparation]: `iA + B` is invertible by `A* B = B* A` and full
rank). -/
private theorem prepMeasure_ker_trivial {W : ℕ} {F : Matrix (Fin 2 × Fin W) (Fin W) ℂ}
    {A B : Matrix (Fin W) (Fin W) ℂ} (hF1 : Fᴴ * F = 1)
    (hSF : freeConj W 0 * F = colStack A B) (hAB : Aᴴ * B = Bᴴ * A) (v : Fin W → ℂ)
    (hv : (Complex.I • A + B) *ᵥ v = 0) : v = 0 := by
  have hBv : B *ᵥ v = -(Complex.I • (A *ᵥ v)) := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec] at hv
    exact eq_neg_of_add_eq_zero_right hv
  set u : Fin W → ℂ := A *ᵥ v with hu
  have h1 : star u ⬝ᵥ (B *ᵥ v) = star (B *ᵥ v) ⬝ᵥ u := by
    rw [hu, Matrix.star_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hAB]
  have h2 : star u ⬝ᵥ (B *ᵥ v) = -Complex.I * (star u ⬝ᵥ u) := by
    rw [hBv, dotProduct_neg, dotProduct_smul, smul_eq_mul, neg_mul]
  have h3 : star (B *ᵥ v) ⬝ᵥ u = Complex.I * (star u ⬝ᵥ u) := by
    rw [hBv, star_neg, star_smul, neg_dotProduct, smul_dotProduct, smul_eq_mul]
    simp
  have h4 : (star u ⬝ᵥ u) = 0 := by
    rw [h2, h3] at h1
    have h5 : (2 * Complex.I) * (star u ⬝ᵥ u) = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp h5).resolve_left (by simp)
  have hu0 : u = 0 := dotProduct_star_self_eq_zero.mp h4
  have hB0 : B *ᵥ v = 0 := by rw [hBv, hu0]; simp
  have hS : (freeConj W 0 * F) *ᵥ v = 0 := by
    rw [hSF]
    ext ⟨i, α⟩
    fin_cases i
    · simpa [colStack, Matrix.mulVec, dotProduct, hu] using congrFun hu0 α
    · simpa [colStack, Matrix.mulVec, dotProduct] using congrFun hB0 α
  have hU := Matrix.mem_unitaryGroup_iff'.mp (freeConj_zero_mem_unitaryGroup W)
  have hFv : F *ᵥ v = 0 := by
    have h' : (star (freeConj W 0) * freeConj W 0) *ᵥ (F *ᵥ v) = 0 := by
      rw [← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ (freeConj W 0) F, hS, Matrix.mulVec_zero]
    rwa [hU, Matrix.one_mulVec] at h'
  have := congrArg (fun w => Fᴴ *ᵥ w) hFv
  simpa [Matrix.mulVec_mulVec, hF1] using this

/-- A real `z` with `det (z A + B) ≠ 0`, when `i A + B` has trivial kernel. -/
private theorem prepMeasure_exists_real {W : ℕ} {A B : Matrix (Fin W) (Fin W) ℂ}
    (h : ∀ v : Fin W → ℂ, (Complex.I • A + B) *ᵥ v = 0 → v = 0) :
    ∃ z : ℝ, ((z : ℂ) • A + B).det ≠ 0 := by
  by_contra hcon
  have hz : ∀ z : ℝ, ((z : ℂ) • A + B).det = 0 := fun z => not_not.mp fun h' => hcon ⟨z, h'⟩
  set M : Matrix (Fin W) (Fin W) (Polynomial ℂ) :=
    Matrix.of fun i j => Polynomial.C (A i j) * Polynomial.X + Polynomial.C (B i j) with hM
  have hev : ∀ z : ℂ, Polynomial.eval z M.det = ((z : ℂ) • A + B).det := by
    intro z
    have := RingHom.map_det (Polynomial.evalRingHom z) M
    simp only [Polynomial.coe_evalRingHom] at this
    rw [this]
    congr 1
    ext i j
    simp [hM]
    ring
  have hp : M.det = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _ ?_
    refine Set.Infinite.mono (s := Set.range ((↑) : ℝ → ℂ)) ?_
      (Set.infinite_range_of_injective Complex.ofReal_injective)
    rintro _ ⟨z, rfl⟩
    exact (hev z).trans (hz z)
  have hdet : (Complex.I • A + B).det = 0 := by
    rw [← hev, hp]
    simp
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  exact hv0 (h v hv)

/-- The first preparation step: `S F_Y = (A; B)` with `A* B = B* A`, `i A + B` of trivial kernel,
and `X_1 = z A - g⁻¹ V_1 A - B`, `Y_1 = A` for every sample (proof of Lemma 9.1
[su:lem:preparation]). -/
private theorem prepMeasure_top_eq {W : ℕ} (q : ℕ) (g E : ℝ) (x : IsoFlag W) :
    ∃ A B : Matrix (Fin W) (Fin W) ℂ, Aᴴ * B = Bᴴ * A ∧
      (∀ v : Fin W → ℂ, (Complex.I • A + B) *ᵥ v = 0 → v = 0) ∧
      ∀ ω : Ω W q, prepTop W g E q x ω = ((max 1 g * E / g : ℝ) : ℂ) • A -
        (g : ℂ)⁻¹ • (blockSeq W q ω 0 * A) - B ∧ prepBot W g E q x ω = A := by
  obtain ⟨hF1, hF2⟩ := prepMeasure_frame_spec x
  obtain ⟨A, B, hSF⟩ : ∃ A B : Matrix (Fin W) (Fin W) ℂ,
      freeConj W 0 * prepFrame x = colStack A B := ⟨_, _, prepMeasure_colStack_top_bot _⟩
  have hiso := prepMeasure_isotropic x hF1 hF2
  rw [hSF, prepMeasure_colStack_phJ] at hiso
  have hAB : Aᴴ * B = Bᴴ * A := by
    have := sub_eq_zero.mp hiso
    exact (smul_right_injective _ Complex.I_ne_zero this).symm
  exact ⟨A, B, hAB, fun v hv => prepMeasure_ker_trivial hF1 hSF hAB v hv,
    fun ω => prepMeasure_topBot g E x ω hSF⟩

/-- Every input block `V_{k+1}` is Hermitian. -/
private theorem prepMeasure_blockSeq_herm (W q : ℕ) (ω : Ω W q) (k : ℕ) :
    (blockSeq W q ω k)ᴴ = blockSeq W q ω k := by
  unfold blockSeq
  split_ifs
  · exact (gueBlock_isHermitian W q ω _).eq
  · exact Matrix.conjTranspose_zero

/-- `V - E - g² R` is Hermitian for Hermitian `V` and `R` and real `g`, `E`. -/
private theorem prepMeasure_M_herm {W : ℕ} {g E : ℝ} {V R : Matrix (Fin W) (Fin W) ℂ}
    (hV : Vᴴ = V) (hR : Rᴴ = R) :
    (V - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R)ᴴ = V - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hV, hR]
  simp [Complex.conj_ofReal]

/-- Every `R_j` is Hermitian, for every sample (proof of Lemma 9.1 [su:lem:preparation]). -/
private theorem prepMeasure_R_herm {W q : ℕ} {g E : ℝ} (x : IsoFlag W) (ω : Ω W q) :
    ∀ j, (prepR W g E q x ω j).IsHermitian := by
  intro j
  induction j with
  | zero => exact Matrix.isHermitian_zero
  | succ n ih =>
    cases n with
    | zero =>
      obtain ⟨A, B, hAB, -, hform⟩ := prepMeasure_top_eq q g E x
      obtain ⟨h1, h2⟩ := hform ω
      change (-((g : ℂ)⁻¹ • (prepBot W g E q x ω * (prepTop W g E q x ω)⁻¹))).IsHermitian
      rw [h2]
      exact prepMeasure_R1_herm (prepMeasure_blockSeq_herm W q ω 0) _ hAB h1
    | succ m =>
      change ((blockSeq W q ω (m + 1) - (E : ℂ) • 1 -
        ((g : ℂ) ^ 2) • prepR W g E q x ω (m + 1))⁻¹).IsHermitian
      exact Matrix.IsHermitian.inv
        (prepMeasure_M_herm (prepMeasure_blockSeq_herm W q ω (m + 1)) ih.eq)

/-- The top and bottom blocks `X_1`, `Y_1` depend only on block `V_1`. -/
private theorem prepMeasure_topBot_congr {W q : ℕ} (g E : ℝ) (x : IsoFlag W) {ω ω' : Ω W q}
    (h : blockSeq W q ω 0 = blockSeq W q ω' 0) :
    prepTop W g E q x ω = prepTop W g E q x ω' ∧ prepBot W g E q x ω = prepBot W g E q x ω' := by
  constructor <;> simp only [prepTop, prepBot, transferProd, h]

/-- `R_j` depends only on the blocks `V_1, …, V_j`. -/
private theorem prepMeasure_R_congr {W q : ℕ} (g E : ℝ) (x : IsoFlag W) {ω ω' : Ω W q} {n : ℕ}
    (h : ∀ k, k < n → blockSeq W q ω k = blockSeq W q ω' k) :
    ∀ j, j ≤ n → prepR W g E q x ω j = prepR W g E q x ω' j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    cases j with
    | zero =>
      have := prepMeasure_topBot_congr g E x (h 0 (by omega))
      change -((g : ℂ)⁻¹ • (prepBot W g E q x ω * (prepTop W g E q x ω)⁻¹)) =
        -((g : ℂ)⁻¹ • (prepBot W g E q x ω' * (prepTop W g E q x ω')⁻¹))
      rw [this.1, this.2]
    | succ m =>
      change (blockSeq W q ω (m + 1) - (E : ℂ) • 1 -
          ((g : ℂ) ^ 2) • prepR W g E q x ω (m + 1))⁻¹ =
        (blockSeq W q ω' (m + 1) - (E : ℂ) • 1 -
          ((g : ℂ) ^ 2) • prepR W g E q x ω' (m + 1))⁻¹
      rw [h (m + 1) (by omega), ih (by omega)]

/-- `v_j` depends only on the blocks `V_1, …, V_j`. -/
private theorem prepMeasure_V_congr {W q : ℕ} (g E : ℝ) (x : IsoFlag W) {ω ω' : Ω W q} {n : ℕ}
    (h : ∀ k, k < n → blockSeq W q ω k = blockSeq W q ω' k) :
    ∀ j, j ≤ n → prepV W g E q x ω j = prepV W g E q x ω' j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    cases j with
    | zero =>
      have := prepMeasure_topBot_congr g E x (h 0 (by omega))
      change ((prepTop W g E q x ω)ᴴ)⁻¹ *ᵥ prepNormal x =
        ((prepTop W g E q x ω')ᴴ)⁻¹ *ᵥ prepNormal x
      rw [this.1]
    | succ m =>
      change prepR W g E q x ω (m + 2) *ᵥ prepV W g E q x ω (m + 1) =
        prepR W g E q x ω' (m + 2) *ᵥ prepV W g E q x ω' (m + 1)
      rw [prepMeasure_R_congr g E x h (m + 2) hj, ih (by omega)]

/-- `PrepOK` depends only on the blocks `V_1, …, V_4`. -/
private theorem prepMeasure_PrepOK_congr {W q : ℕ} (g E : ℝ) (x : IsoFlag W) {ω ω' : Ω W q}
    (h : ∀ k, k < 4 → blockSeq W q ω k = blockSeq W q ω' k) :
    PrepOK W g E q x ω ↔ PrepOK W g E q x ω' := by
  have htop := (prepMeasure_topBot_congr g E x (h 0 (by norm_num))).1
  unfold PrepOK
  rw [htop]
  refine and_congr Iff.rfl
    (forall_congr' fun j => forall_congr' fun hj1 => forall_congr' fun hj3 => ?_)
  rw [h j (by omega), prepMeasure_R_congr g E x h j (by omega)]

/-- Block `k` of the sample, as a `W × W` matrix, is measurable in the sample. -/
private theorem prepMeasure_measurable_gueBlock (W q : ℕ) (k : Fin q) :
    Measurable fun ω : Ω W q => gueBlock W q ω k := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

/-- The input blocks `V_{k+1}` are measurable in the sample. -/
private theorem prepMeasure_measurable_blockSeq (W q k : ℕ) :
    Measurable fun ω : Ω W q => blockSeq W q ω k := by
  by_cases h : k < q
  · have : (fun ω : Ω W q => blockSeq W q ω k) = fun ω => gueBlock W q ω ⟨k, h⟩ := by
      funext ω
      simp only [blockSeq, h, ↓reduceDIte]
    rw [this]
    exact prepMeasure_measurable_gueBlock W q ⟨k, h⟩
  · have : (fun ω : Ω W q => blockSeq W q ω k) = fun _ => 0 := by
      funext ω
      simp only [blockSeq, h, ↓reduceDIte]
    rw [this]
    exact measurable_const

/-- The matrix inverse is measurable. -/
private theorem prepMeasure_measurable_inv {W : ℕ} :
    Measurable fun A : Matrix (Fin W) (Fin W) ℂ => A⁻¹ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  have hd : Measurable fun A : Matrix (Fin W) (Fin W) ℂ => A.det :=
    (continuous_id.matrix_det).measurable
  have ha : Measurable fun A : Matrix (Fin W) (Fin W) ℂ => A.adjugate i j :=
    (continuous_id.matrix_adjugate).measurable.eval_matrix
  exact (hd.inv).mul ha

/-- `X_1`, `Y_1` are measurable in the sample. -/
private theorem prepMeasure_measurable_topBot {W q : ℕ} (g E : ℝ) (x : IsoFlag W) :
    Measurable (prepTop W g E q x) ∧ Measurable (prepBot W g E q x) := by
  obtain ⟨A, B, -, -, hform⟩ := prepMeasure_top_eq q g E x
  have hb := prepMeasure_measurable_blockSeq W q 0
  constructor
  · have : prepTop W g E q x = fun ω => ((max 1 g * E / g : ℝ) : ℂ) • A -
        (g : ℂ)⁻¹ • (blockSeq W q ω 0 * A) - B := funext fun ω => (hform ω).1
    rw [this]
    have hc : Continuous fun V : Matrix (Fin W) (Fin W) ℂ => ((max 1 g * E / g : ℝ) : ℂ) • A -
        (g : ℂ)⁻¹ • (V * A) - B := by fun_prop
    exact hc.measurable.comp hb
  · have : prepBot W g E q x = fun _ => A := funext fun ω => (hform ω).2
    rw [this]
    exact measurable_const

/-- `R_j` is measurable in the sample. -/
private theorem prepMeasure_measurable_R {W q : ℕ} (g E : ℝ) (x : IsoFlag W) (j : ℕ) :
    Measurable fun ω : Ω W q => prepR W g E q x ω j := by
  induction j with
  | zero => exact measurable_const
  | succ n ih =>
    cases n with
    | zero =>
      obtain ⟨hT, hB⟩ := prepMeasure_measurable_topBot (q := q) g E x
      have hc : Continuous fun p : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ =>
          -((g : ℂ)⁻¹ • (p.1 * p.2)) := by fun_prop
      have := hc.measurable.comp (hB.prodMk (prepMeasure_measurable_inv.comp hT))
      exact this
    | succ m =>
      have hc : Continuous fun p : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ =>
          p.1 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • p.2 := by fun_prop
      have := prepMeasure_measurable_inv.comp
        (hc.measurable.comp ((prepMeasure_measurable_blockSeq W q (m + 1)).prodMk ih))
      exact this

/-- `v_j` is measurable in the sample. -/
private theorem prepMeasure_measurable_V {W q : ℕ} (g E : ℝ) (x : IsoFlag W) (j : ℕ) :
    Measurable fun ω : Ω W q => prepV W g E q x ω j := by
  induction j with
  | zero => exact measurable_const
  | succ n ih =>
    cases n with
    | zero =>
      obtain ⟨hT, -⟩ := prepMeasure_measurable_topBot (q := q) g E x
      have hc : Continuous fun M : Matrix (Fin W) (Fin W) ℂ => Mᴴ := by fun_prop
      have hc2 : Continuous fun p : Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ) => p.1 *ᵥ p.2 :=
        continuous_fst.matrix_mulVec continuous_snd
      exact hc2.measurable.comp
        ((prepMeasure_measurable_inv.comp (hc.measurable.comp hT)).prodMk measurable_const)
    | succ m =>
      have hc2 : Continuous fun p : Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ) => p.1 *ᵥ p.2 :=
        continuous_fst.matrix_mulVec continuous_snd
      exact hc2.measurable.comp ((prepMeasure_measurable_R g E x (m + 2)).prodMk ih)

/-- The set where a measurable matrix-valued function is invertible is measurable. -/
private theorem prepMeasure_measurableSet_isUnit {W : ℕ} {α : Type*} [MeasurableSpace α]
    {f : α → Matrix (Fin W) (Fin W) ℂ} (hf : Measurable f) :
    MeasurableSet {ω | IsUnit (f ω)} := by
  have h : {ω | IsUnit (f ω)} = (fun ω => (f ω).det) ⁻¹' {0}ᶜ := by
    ext ω
    simp [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  rw [h]
  exact (measurableSet_singleton 0).compl.preimage ((continuous_id.matrix_det).measurable.comp hf)

/-- `{PrepOK}` is measurable. -/
private theorem prepMeasure_measurableSet_PrepOK {W q : ℕ} (g E : ℝ) (x : IsoFlag W) :
    MeasurableSet {ω : Ω W q | PrepOK W g E q x ω} := by
  have hM : ∀ j, Measurable fun ω : Ω W q => blockSeq W q ω j - (E : ℂ) • 1 -
      ((g : ℂ) ^ 2) • prepR W g E q x ω j := fun j => by
    have hc : Continuous fun p : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ =>
        p.1 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • p.2 := by fun_prop
    exact hc.measurable.comp ((prepMeasure_measurable_blockSeq W q j).prodMk
      (prepMeasure_measurable_R g E x j))
  have h : {ω : Ω W q | PrepOK W g E q x ω} =
      {ω | IsUnit (prepTop W g E q x ω)} ∩
        ⋂ j : ℕ, ⋂ (_ : 1 ≤ j), ⋂ (_ : j ≤ 3), {ω | IsUnit (blockSeq W q ω j - (E : ℂ) • 1 -
          ((g : ℂ) ^ 2) • prepR W g E q x ω j)} := by
    ext ω
    simp only [PrepOK, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [h]
  exact (prepMeasure_measurableSet_isUnit (prepMeasure_measurable_topBot g E x).1).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
      prepMeasure_measurableSet_isUnit (hM j))

/-- The entry `(α, β)` of block `a` as a polynomial in the Gaussian coordinates. -/
private def prepMeasure_gueEntry {W q : ℕ} (a : Fin q) (α β : Fin W) :
    MvPolynomial (Fin q × Fin W × Fin W) ℂ :=
  if α = β then MvPolynomial.X (a, α, α) * MvPolynomial.C (((Real.sqrt W : ℝ) : ℂ)⁻¹)
  else if α < β then
    (MvPolynomial.X (a, α, β) + MvPolynomial.C Complex.I * MvPolynomial.X (a, β, α)) *
      MvPolynomial.C (((Real.sqrt (2 * W) : ℝ) : ℂ)⁻¹)
  else
    (MvPolynomial.X (a, β, α) - MvPolynomial.C Complex.I * MvPolynomial.X (a, α, β)) *
      MvPolynomial.C (((Real.sqrt (2 * W) : ℝ) : ℂ)⁻¹)

private theorem prepMeasure_eval_gueEntry {W q : ℕ} (a : Fin q) (ω : Ω W q) (α β : Fin W) :
    MvPolynomial.eval (fun i => (ω i : ℂ)) (prepMeasure_gueEntry a α β) =
      gueBlock W q ω a α β := by
  simp only [prepMeasure_gueEntry, gueBlock, Matrix.of_apply]
  split_ifs <;> simp [div_eq_mul_inv, mul_comm]

/-- `X_1` is invertible for almost every sample (proof of Lemma 9.1
[su:lem:preparation]): `det X_1` is a polynomial in the entries of `V_1` that does not vanish at
`V_1 = E + g z_0` for a real `z_0` with `det(z_0 A + B) ≠ 0`. -/
private theorem prepMeasure_ae_top {W q : ℕ} {g E : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) (hq : 0 < q)
    (x : IsoFlag W) : μ W q {ω | ¬ IsUnit (prepTop W g E q x ω)} = 0 := by
  obtain ⟨A, B, -, hker, hform⟩ := prepMeasure_top_eq q g E x
  obtain ⟨z₀, hz₀⟩ := prepMeasure_exists_real hker
  have hg0 : g ≠ 0 := hg.ne'
  have hgc : (g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg0
  set a : Fin q := ⟨0, hq⟩ with ha
  set z : ℝ := max 1 g * E / g with hz
  have hb0 : ∀ ω : Ω W q, blockSeq W q ω 0 = gueBlock W q ω a := fun ω => by
    simp only [blockSeq, hq, ↓reduceDIte, ha]
  set Xp : Matrix (Fin W) (Fin W) (MvPolynomial (Fin q × Fin W × Fin W) ℂ) :=
    Matrix.of fun α β => MvPolynomial.C ((z : ℂ) * A α β - B α β) -
      MvPolynomial.C ((g : ℂ)⁻¹) *
        ∑ γ, prepMeasure_gueEntry a α γ * MvPolynomial.C (A γ β) with hXp
  set P := Xp.det with hP
  have hXe : ∀ ω : Ω W q, MvPolynomial.eval (fun i => (ω i : ℂ)) P =
      (prepTop W g E q x ω).det := by
    intro ω
    rw [hP, RingHom.map_det]
    congr 1
    rw [(hform ω).1, hb0]
    ext α β
    simp [hXp, Matrix.mul_apply, prepMeasure_eval_gueEntry, Matrix.sub_apply, Matrix.smul_apply,
      Finset.mul_sum, hz]
    ring
  set V₀ : Matrix (Fin W) (Fin W) ℂ := ((E + g * z₀ : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)
    with hV₀
  have hV₀H : V₀.IsHermitian :=
    Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint, Complex.conj_ofReal])
  set ω₀ : Ω W q := gueCoord W q (fun _ => V₀) with hω₀
  have hω₀B : gueBlock W q ω₀ a = V₀ :=
    congrFun (gueBlock_gueCoord W q (fun _ => V₀) (fun _ => hV₀H)) a
  have hX₀ : prepTop W g E q x ω₀ = -((z₀ : ℂ) • A + B) := by
    rw [(hform ω₀).1, hb0, hω₀B, hV₀, hz, max_eq_left hg1]
    ext α β
    simp [Matrix.sub_apply, Matrix.smul_apply]
    field_simp
    ring
  have hP₀ : MvPolynomial.eval (fun i => (ω₀ i : ℂ)) P ≠ 0 := by
    rw [hXe, hX₀, Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hz₀
  have : NullSingletonClass (gaussianReal (0 : ℝ) 1) :=
    nullSingletonClass_gaussianReal one_ne_zero
  have hnull := measure_zero_mvPolynomial (fun _ : Fin q × Fin W × Fin W => gaussianReal 0 1) P
    (fun i => ω₀ i) hP₀
  have h2 : {ω : Ω W q | ¬ IsUnit (prepTop W g E q x ω)} =
      {ω | MvPolynomial.eval (fun i => (ω i : ℂ)) P = 0} := by
    ext ω
    simp [hXe, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  rw [h2]
  exact hnull

/-- Block `a` of two samples that agree on the coordinates of block `a` coincide. -/
private theorem prepMeasure_gueBlock_congr {W q : ℕ} {ω ω' : Ω W q} (a : Fin q)
    (h : ∀ α β, ω (a, α, β) = ω' (a, α, β)) : gueBlock W q ω a = gueBlock W q ω' a := by
  unfold gueBlock
  simp only [h]

/-- Step `j` of the preparation: `V_{j+1} - E - g² R_j` is invertible almost surely, because
`V_{j+1}` is a fresh GUE block and `R_j` is fixed before it (proof of Lemma 9.1
[su:lem:preparation]). -/
private theorem prepMeasure_ae_step {W q : ℕ} {g E : ℝ} (x : IsoFlag W) {j : ℕ}
    (hjq : j < q) :
    μ W q {ω | ¬ IsUnit (blockSeq W q ω j - (E : ℂ) • 1 -
      ((g : ℂ) ^ 2) • prepR W g E q x ω j)} = 0 := by
  set a : Fin q := ⟨j, hjq⟩ with ha
  set T : Set (Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ) :=
    {p | ¬ IsUnit (p.1 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • p.2)} with hT
  have hTm : MeasurableSet T := by
    have hc : Continuous fun p : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ =>
        p.1 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • p.2 := by fun_prop
    exact (prepMeasure_measurableSet_isUnit hc.measurable).compl
  have hD : Measurable fun ω : Ω W q => prepR W g E q x ω j := prepMeasure_measurable_R g E x j
  have hDa : OffBlock W q a (fun ω => prepR W g E q x ω j) := by
    intro ω ω' h
    refine prepMeasure_R_congr g E x (n := j) (fun k hk => ?_) j le_rfl
    have hkq : k < q := by omega
    simp only [blockSeq, hkq, ↓reduceDIte]
    refine prepMeasure_gueBlock_congr ⟨k, hkq⟩ fun α β => h (⟨k, hkq⟩, α, β) ?_
    intro hka
    have := congrArg Fin.val hka
    simp only [ha] at this
    omega
  have hSa : OffBlock W q a (· ∈ (Set.univ : Set (Ω W q))) := fun _ _ _ => rfl
  have hb : ∀ ω ∈ (Set.univ : Set (Ω W q)),
      μ W 1 {ω' | (gueMat W ω', prepR W g E q x ω j) ∈ T} ≤ 0 := by
    intro ω _
    have hH : ((0 : Matrix (Fin W) (Fin W) ℂ) - (E : ℂ) • 1 -
        ((g : ℂ) ^ 2) • prepR W g E q x ω j).IsHermitian :=
      prepMeasure_M_herm (g := g) (E := E) Matrix.conjTranspose_zero
        (prepMeasure_R_herm x ω j).eq
    have hae := ae_det_ne_zero_gueMat W hH (c := 1) one_ne_zero
    refine (measure_mono_null (fun ω' hω' => ?_) (ae_iff.mp hae)).le
    simp only [hT, Set.mem_ofPred_eq, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
      not_not] at hω' ⊢
    rw [← hω']
    congr 1
    simp only [Complex.ofReal_one, one_smul]
    abel
  have key := measure_gueBlock_fresh_le W q a hD hDa MeasurableSet.univ hSa hTm hb
  simp only [zero_mul, Set.mem_univ, true_and, nonpos_iff_eq_zero] at key
  have hset : {ω : Ω W q | ¬ IsUnit (blockSeq W q ω j - (E : ℂ) • 1 -
      ((g : ℂ) ^ 2) • prepR W g E q x ω j)} =
      {ω | (gueBlock W q ω a, prepR W g E q x ω j) ∈ T} := by
    ext ω
    simp only [hT, Set.mem_ofPred_eq, blockSeq, hjq, ↓reduceDIte, ha]
  rw [hset]
  exact key

/-- Chart entry almost surely (proof of Lemma 9.1 [su:lem:preparation]): for `0 < g ≤ 1` and
`q ≥ 4`, every flag and every energy, the four preparation steps are invertible for almost every
sample. -/
theorem ae_prepOK {W q : ℕ} {g E : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) (hq : 4 ≤ q) (x : IsoFlag W) :
    μ W q {ω | ¬ PrepOK W g E q x ω} = 0 := by
  have hq0 : 0 < q := by omega
  have h0 := prepMeasure_ae_top (E := E) hg hg1 hq0 x
  have h1 := prepMeasure_ae_step (W := W) (q := q) (g := g) (E := E) x (j := 1) (by omega)
  have h2 := prepMeasure_ae_step (W := W) (q := q) (g := g) (E := E) x (j := 2) (by omega)
  have h3 := prepMeasure_ae_step (W := W) (q := q) (g := g) (E := E) x (j := 3) (by omega)
  refine measure_mono_null (fun ω hω => ?_)
    (measure_union_null (measure_union_null (measure_union_null h0 h1) h2) h3)
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
  obtain ⟨⟨⟨h0', h1'⟩, h2'⟩, h3'⟩ := hc
  refine hω ⟨h0', fun j hj1 hj3 => ?_⟩
  interval_cases j <;> assumption

/-- The preparation indicator of a set `G` of prepared data: `1` where the four preparation steps
are invertible and `(R_4, v_4) ∈ G`, `0` otherwise. -/
def prepInd (W : ℕ) (g E : ℝ) (q : ℕ) (x : IsoFlag W)
    (G : Set (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ))) (ω : Ω W q) : ℝ :=
  if PrepOK W g E q x ω ∧ (prepR W g E q x ω 4, prepV W g E q x ω 4) ∈ G then 1 else 0

/-- The preparation data of Lemma 9.3 [su:lem:chosen-generator]: for `0 < g ≤ 1` and a measurable
`G`, `pre = prepInd … G` takes the values `0, 1`; `pre`, `R_4 = prepR … 4` and `v_4 = prepV … 4`
are measurable and depend only on the blocks `0, …, 3`; and where `pre ≠ 0` the prepared chart
(9.1) [su:eq:graph-input] holds. -/
theorem prepInd_spec {W q : ℕ} [NeZero W] {g E : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) (x : IsoFlag W)
    {G : Set (Matrix (Fin W) (Fin W) ℂ × (Fin W → ℂ))} (hG : MeasurableSet G) :
    (∀ ω, prepInd W g E q x G ω = 0 ∨ prepInd W g E q x G ω = 1) ∧
    Measurable (prepInd W g E q x G) ∧ Measurable (fun ω => prepR W g E q x ω 4) ∧
    Measurable (fun ω => prepV W g E q x ω 4) ∧
    (∀ ω ω' : Ω W q, (∀ i : Fin q, (i : ℕ) < 4 → gueBlock W q ω i = gueBlock W q ω' i) →
      prepInd W g E q x G ω = prepInd W g E q x G ω' ∧
        prepR W g E q x ω 4 = prepR W g E q x ω' 4 ∧ prepV W g E q x ω 4 = prepV W g E q x ω' 4) ∧
    ∀ ω, prepInd W g E q x G ω ≠ 0 →
      IsPrepChart W g E q x ω (prepR W g E q x ω 4) (prepV W g E q x ω 4) := by
  have hS : MeasurableSet {ω : Ω W q | PrepOK W g E q x ω ∧
      (prepR W g E q x ω 4, prepV W g E q x ω 4) ∈ G} :=
    (prepMeasure_measurableSet_PrepOK g E x).inter (hG.preimage
      ((prepMeasure_measurable_R g E x 4).prodMk (prepMeasure_measurable_V g E x 4)))
  refine ⟨?_, ?_, prepMeasure_measurable_R g E x 4, prepMeasure_measurable_V g E x 4, ?_, ?_⟩
  · intro ω
    unfold prepInd
    split_ifs <;> simp
  · unfold prepInd
    exact Measurable.ite hS measurable_const measurable_const
  · intro ω ω' h
    have h4 : ∀ k, k < 4 → blockSeq W q ω k = blockSeq W q ω' k := by
      intro k hk
      by_cases hkq : k < q
      · simp only [blockSeq, hkq, ↓reduceDIte]
        rw [h ⟨k, hkq⟩ hk]
      · simp only [blockSeq, hkq, ↓reduceDIte]
    have hR := prepMeasure_R_congr g E x h4 4 le_rfl
    have hV := prepMeasure_V_congr g E x h4 4 le_rfl
    have hP := prepMeasure_PrepOK_congr g E x h4
    refine ⟨?_, hR, hV⟩
    simp only [prepInd, hP, hR, hV]
  · intro ω hω
    have hP : PrepOK W g E q x ω := by
      by_contra hc
      exact hω (by simp [prepInd, hc])
    exact isPrepChart_of_prepOK hg hg1 x hP

end LSBA
