import LSBA.Primitive.Defs

/-!
# Primitive loops: the primitive equation

The dissection sum (B.1) [ba:eq:dissection] solves the primitive equation (5.10)
[fo:eq:primitive] on `-1 < t < 1`: the derivative of `F_k` is `β` times the quadratic cut sum
(`cutSumFam`), and that of `𝒦_k` is `γ_g W` times it.
-/

open MeasureTheory Real Filter Topology Complex Finset
open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ## The one-label inverses and pair kernels as functions of `t` -/

section Calculus

open scoped Matrix.Norms.Operator

variable {L : ℕ}

/-- The pair matrix of a sign pair: `P` for opposite signs, `Q` for `++`, its conjugate for
`--` (Appendix B.2 [sec:bl-primitives]). -/
private def tree_pairX (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (s s' : Bool) :
    Matrix (Fin L) (Fin L) ℂ :=
  if s = s' then (if s then pairQ β M else (pairQ β M).map star)
  else (pairP β M).map ((↑) : ℝ → ℂ)

/-- The pair matrix does not depend on the order of the two signs. -/
private lemma tree_pairX_swap (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (s s' : Bool) :
    tree_pairX β M s s' = tree_pairX β M s' s := by
  cases s <;> cases s' <;> rfl

/-- Under the primitive data, the rows of `|X|` sum to one. -/
private lemma tree_pairX_rowsum {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) (s s' : Bool) (a : Fin L) :
    ∑ b, ‖tree_pairX β M s s' a b‖ = 1 := by
  have hQ : ∀ b, ‖pairQ β M a b‖ = pairP β M a b := by
    intro b
    simp [pairQ, pairP, norm_pow, Complex.norm_real, abs_of_pos hD.pos]
  have hP : ∀ b, ‖((pairP β M a b : ℝ) : ℂ)‖ = pairP β M a b := by
    intro b
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    simp only [pairP, Matrix.of_apply]
    exact mul_nonneg hD.pos.le (sq_nonneg _)
  rw [← hD.row_sum a]
  unfold tree_pairX
  split_ifs
  · exact Finset.sum_congr rfl fun b _ => hQ b
  · exact Finset.sum_congr rfl fun b _ => by rw [Matrix.map_apply, norm_star, hQ b]
  · exact Finset.sum_congr rfl fun b _ => by rw [Matrix.map_apply, hP b]

/-- The pair matrix is symmetric when `M` is. -/
private lemma tree_pairX_transpose {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} (hM : Mᵀ = M)
    (s s' : Bool) : (tree_pairX β M s s')ᵀ = tree_pairX β M s s' := by
  have h : ∀ a b, M b a = M a b := fun a b => congrFun (congrFun hM a) b
  unfold tree_pairX
  split_ifs <;> ext a b <;> simp [pairQ, pairP, h a b]

/-- Row sums of `|X|` at most `1` give `‖X‖_{∞→∞} ≤ 1`. -/
private lemma tree_norm_le {X : Matrix (Fin L) (Fin L) ℂ} (hX : ∀ a, ∑ b, ‖X a b‖ ≤ 1) :
    ‖X‖ ≤ 1 := by
  have h : ‖X‖₊ ≤ 1 := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun a _ => ?_
    rw [← NNReal.coe_le_coe, NNReal.coe_sum, NNReal.coe_one]
    simpa using hX a
  exact_mod_cast h

private lemma tree_isUnit {X : Matrix (Fin L) (Fin L) ℂ} (hX : ‖X‖ ≤ 1) {t : ℝ} (ht : |t| < 1) :
    IsUnit (1 - (t : ℂ) • X) := by
  have h : ‖(t : ℂ) • X‖ < 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc |t| * ‖X‖ ≤ |t| * 1 := mul_le_mul_of_nonneg_left hX (abs_nonneg t)
      _ < 1 := by rwa [mul_one]
  exact ⟨Units.oneSub _ h, Units.val_oneSub _ _⟩

private lemma tree_isUnit_det {X : Matrix (Fin L) (Fin L) ℂ} (hX : ‖X‖ ≤ 1) {t : ℝ}
    (ht : |t| < 1) : IsUnit (1 - (t : ℂ) • X).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (tree_isUnit hX ht)

/-- The entrywise image of an inverse under a ring hom of fields. -/
private lemma tree_map_inv {R S : Type*} [Field R] [Field S] (f : R →+* S)
    (A : Matrix (Fin L) (Fin L) R) : (A⁻¹).map f = (A.map f)⁻¹ := by
  by_cases h : IsUnit A.det
  · symm
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ h, Matrix.map_one _ (map_zero f) (map_one f)]
  · have h' : ¬IsUnit (A.map f).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, isUnit_iff_ne_zero,
        map_ne_zero_iff _ f.injective, ← isUnit_iff_ne_zero]
      exact h
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h']
    ext a b
    simp

private lemma tree_map_star_eq (A : Matrix (Fin L) (Fin L) ℂ) :
    A.map star = A.map (starRingEnd ℂ) := rfl

/-- The one-label inverse is `(I - tX)⁻¹`. -/
private lemma tree_pairV_eq (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) (s s' : Bool) :
    pairV β M t s s' = (1 - (t : ℂ) • tree_pairX β M s s')⁻¹ := by
  unfold pairV tree_pairX
  split_ifs with h1 h2
  · rfl
  · rw [tree_map_star_eq, tree_map_inv]
    congr 1
    ext a b
    simp [Matrix.one_apply]
  · rw [show ((1 - t • pairP β M)⁻¹).map ((↑) : ℝ → ℂ) =
        ((1 - t • pairP β M)⁻¹).map Complex.ofRealHom from rfl, tree_map_inv]
    congr 1
    ext a b
    simp [Matrix.one_apply]
    split_ifs <;> simp

/-- The pair kernel is `X(I - tX)⁻¹`. -/
private lemma tree_pairK_eq (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) (s s' : Bool) :
    pairK β M t s s' = tree_pairX β M s s' * (1 - (t : ℂ) • tree_pairX β M s s')⁻¹ := by
  have hV := tree_pairV_eq β M t s s'
  cases s <;> cases s' <;>
    simp only [pairK, pairV, tree_pairX, Bool.false_eq_true, Bool.true_eq_false, ite_true,
      ite_false, mixedKer] at hV ⊢
  · rw [← hV, tree_map_star_eq, tree_map_star_eq, tree_map_star_eq, Matrix.map_mul]
  · rw [← hV, show ((pairP β M * (1 - t • pairP β M)⁻¹)).map ((↑) : ℝ → ℂ) =
        ((pairP β M * (1 - t • pairP β M)⁻¹)).map Complex.ofRealHom from rfl, Matrix.map_mul]
    rfl
  · rw [← hV, show ((pairP β M * (1 - t • pairP β M)⁻¹)).map ((↑) : ℝ → ℂ) =
        ((pairP β M * (1 - t • pairP β M)⁻¹)).map Complex.ofRealHom from rfl, Matrix.map_mul]
    rfl


section Generic

variable {X : Matrix (Fin L) (Fin L) ℂ}

private lemma tree_inv_mul (hX : ‖X‖ ≤ 1) {t : ℝ} (ht : |t| < 1) :
    (1 - (t : ℂ) • X)⁻¹ * (1 - (t : ℂ) • X) = 1 :=
  Matrix.nonsing_inv_mul _ (tree_isUnit_det hX ht)

private lemma tree_mul_inv (hX : ‖X‖ ≤ 1) {t : ℝ} (ht : |t| < 1) :
    (1 - (t : ℂ) • X) * (1 - (t : ℂ) • X)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (tree_isUnit_det hX ht)

/-- `V = 1 + t V X`. -/
private lemma tree_inv_eq_right (hX : ‖X‖ ≤ 1) {t : ℝ} (ht : |t| < 1) :
    (1 - (t : ℂ) • X)⁻¹ = 1 + (t : ℂ) • ((1 - (t : ℂ) • X)⁻¹ * X) := by
  have h := tree_inv_mul hX ht
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul] at h
  exact sub_eq_iff_eq_add.mp h

/-- `X` commutes with `V = (1 - tX)⁻¹`. -/
private lemma tree_comm (hX : ‖X‖ ≤ 1) {t : ℝ} (ht : |t| < 1) :
    X * (1 - (t : ℂ) • X)⁻¹ = (1 - (t : ℂ) • X)⁻¹ * X := by
  have hc : (1 - (t : ℂ) • X) * X = X * (1 - (t : ℂ) • X) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul]
  set V := (1 - (t : ℂ) • X)⁻¹
  calc X * V = (V * (1 - (t : ℂ) • X)) * X * V := by rw [tree_inv_mul hX ht, Matrix.one_mul]
    _ = V * ((1 - (t : ℂ) • X) * X) * V := by simp only [Matrix.mul_assoc]
    _ = V * (X * (1 - (t : ℂ) • X)) * V := by rw [hc]
    _ = V * X * ((1 - (t : ℂ) • X) * V) := by simp only [Matrix.mul_assoc]
    _ = V * X := by rw [tree_mul_inv hX ht, Matrix.mul_one]

/-- The resolvent identity `V_s - V_t = (s - t) V_s X V_t`. -/
private lemma tree_inv_sub (hX : ‖X‖ ≤ 1) {s t : ℝ} (hs : |s| < 1) (ht : |t| < 1) :
    (1 - (s : ℂ) • X)⁻¹ - (1 - (t : ℂ) • X)⁻¹ =
      ((s - t : ℝ) : ℂ) • ((1 - (s : ℂ) • X)⁻¹ * X * (1 - (t : ℂ) • X)⁻¹) := by
  set A := (1 - (s : ℂ) • X)⁻¹
  set B := (1 - (t : ℂ) • X)⁻¹
  have hd : (1 - (t : ℂ) • X) - (1 - (s : ℂ) • X) = ((s - t : ℝ) : ℂ) • X := by
    rw [sub_sub_sub_cancel_left, ← sub_smul]; push_cast; rfl
  calc A - B = A * ((1 - (t : ℂ) • X) * B) - A * (1 - (s : ℂ) • X) * B := by
        rw [tree_mul_inv hX ht, tree_inv_mul hX hs, Matrix.mul_one, Matrix.one_mul]
    _ = A * ((1 - (t : ℂ) • X) - (1 - (s : ℂ) • X)) * B := by noncomm_ring
    _ = ((s - t : ℝ) : ℂ) • (A * X * B) := by
        rw [hd, Matrix.mul_smul, Matrix.smul_mul]

private lemma tree_inv_continuousAt (hX : ‖X‖ ≤ 1) {t : ℝ} (ht : |t| < 1) :
    ContinuousAt (fun s : ℝ => (1 - (s : ℂ) • X)⁻¹) t := by
  obtain ⟨u, hu⟩ := tree_isUnit hX ht
  have hinv : ContinuousAt (Ring.inverse : Matrix (Fin L) (Fin L) ℂ → _) (1 - (t : ℂ) • X) := by
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  have hlin : ContinuousAt (fun s : ℝ => 1 - (s : ℂ) • X) t :=
    continuousAt_const.sub ((Complex.continuous_ofReal.continuousAt).smul continuousAt_const)
  have h := ContinuousAt.comp (g := Ring.inverse) (f := fun s : ℝ => 1 - (s : ℂ) • X) hinv hlin
  simpa only [Function.comp_def, ← Matrix.nonsing_inv_eq_ringInverse] using h

/-- `∂_t (V_t)_{ab} = (V_t X V_t)_{ab}`. -/
private lemma tree_inv_hasDerivAt (hX : ‖X‖ ≤ 1) {t : ℝ} (ht : |t| < 1) (a b : Fin L) :
    HasDerivAt (fun s : ℝ => (1 - (s : ℂ) • X)⁻¹ a b)
      (((1 - (t : ℂ) • X)⁻¹ * X * (1 - (t : ℂ) • X)⁻¹) a b) t := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hball : ∀ᶠ s : ℝ in 𝓝[≠] t, |s| < 1 :=
    eventually_nhdsWithin_of_eventually_nhds
      ((isOpen_lt continuous_abs continuous_const).mem_nhds ht)
  have hslope : ∀ᶠ s : ℝ in 𝓝[≠] t,
      ((1 - (s : ℂ) • X)⁻¹ * X * (1 - (t : ℂ) • X)⁻¹) a b =
        slope (fun s : ℝ => (1 - (s : ℂ) • X)⁻¹ a b) t s := by
    filter_upwards [hball, self_mem_nhdsWithin] with s hs hmem
    have hne : s - t ≠ 0 := sub_ne_zero_of_ne hmem
    have hdiff : (1 - (s : ℂ) • X)⁻¹ a b - (1 - (t : ℂ) • X)⁻¹ a b
        = ((s - t : ℝ) : ℂ) * ((1 - (s : ℂ) • X)⁻¹ * X * (1 - (t : ℂ) • X)⁻¹) a b := by
      have h := congrFun (congrFun (tree_inv_sub hX hs ht) a) b
      simpa [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using h
    rw [slope_def_module, hdiff, Complex.real_smul]
    have hne' : ((s - t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
    rw [← mul_assoc, mul_comm (((s - t)⁻¹ : ℝ) : ℂ), Complex.ofReal_inv, mul_inv_cancel₀ hne',
      one_mul]
  refine Tendsto.congr' hslope ?_
  have hM : Tendsto (fun s : ℝ => (1 - (s : ℂ) • X)⁻¹) (𝓝[≠] t) (𝓝 ((1 - (t : ℂ) • X)⁻¹)) :=
    (tree_inv_continuousAt hX ht).tendsto.mono_left nhdsWithin_le_nhds
  have hmul : Tendsto (fun s : ℝ => (1 - (s : ℂ) • X)⁻¹ * X * (1 - (t : ℂ) • X)⁻¹) (𝓝[≠] t)
      (𝓝 ((1 - (t : ℂ) • X)⁻¹ * X * (1 - (t : ℂ) • X)⁻¹)) :=
    (hM.mul tendsto_const_nhds).mul tendsto_const_nhds
  have hent : Continuous fun A : Matrix (Fin L) (Fin L) ℂ => A a b :=
    (continuous_apply b).comp (continuous_apply a)
  exact (hent.continuousAt.tendsto).comp hmul

end Generic


section Pair

variable {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}

private lemma tree_pairX_norm (hD : PrimData β M m) (s s' : Bool) : ‖tree_pairX β M s s'‖ ≤ 1 :=
  tree_norm_le fun a => (tree_pairX_rowsum hD s s' a).le

/-- `∂_t V_t = K_t V_t`, entrywise. -/
private lemma tree_pairV_hasDerivAt (hD : PrimData β M m) {t : ℝ} (ht : |t| < 1) (s s' : Bool)
    (a b : Fin L) :
    HasDerivAt (fun r => pairV β M r s s' a b) ((pairK β M t s s' * pairV β M t s s') a b) t := by
  have h := tree_inv_hasDerivAt (tree_pairX_norm hD s s') ht a b
  simp only [tree_pairV_eq, tree_pairK_eq]
  rwa [tree_comm (tree_pairX_norm hD s s') ht]

/-- `∂_t K_t = K_t K_t`, entrywise. -/
private lemma tree_pairK_hasDerivAt (hD : PrimData β M m) {t : ℝ} (ht : |t| < 1) (s s' : Bool)
    (a b : Fin L) :
    HasDerivAt (fun r => pairK β M r s s' a b) ((pairK β M t s s' * pairK β M t s s') a b) t := by
  set X := tree_pairX β M s s'
  have h : ∀ c ∈ (Finset.univ : Finset (Fin L)),
      HasDerivAt (fun r : ℝ => X a c * (1 - (r : ℂ) • X)⁻¹ c b)
        (X a c * ((1 - (t : ℂ) • X)⁻¹ * X * (1 - (t : ℂ) • X)⁻¹) c b) t :=
    fun c _ => (tree_inv_hasDerivAt (tree_pairX_norm hD s s') ht c b).const_mul _
  have h2 := HasDerivAt.fun_sum h
  simp only [tree_pairK_eq]
  simp only [Matrix.mul_apply] at h2 ⊢
  convert h2 using 1
  simp only [← Matrix.mul_apply]
  simp only [Matrix.mul_assoc]
  rfl

/-- `∂_t (β t V_t) = β V_t V_t`, entrywise. -/
private lemma tree_link_hasDerivAt (hD : PrimData β M m) {t : ℝ} (ht : |t| < 1) (s s' : Bool)
    (a b : Fin L) :
    HasDerivAt (fun r => ((β * r : ℝ) : ℂ) * pairV β M r s s' a b)
      ((β : ℂ) * (pairV β M t s s' * pairV β M t s s') a b) t := by
  set X := tree_pairX β M s s'
  have hX := tree_pairX_norm hD s s'
  have h1 : HasDerivAt (fun r : ℝ => ((β * r : ℝ) : ℂ)) (β : ℂ) t := by
    have := ((hasDerivAt_id t).const_mul β).ofReal_comp
    simpa using this
  have h2 := h1.mul (tree_inv_hasDerivAt hX ht a b)
  simp only [tree_pairV_eq]
  convert h2 using 1
  have hV := tree_inv_eq_right hX ht
  set V := (1 - (t : ℂ) • X)⁻¹
  have hVV : V * V = V + (t : ℂ) • (V * X * V) := by
    conv_lhs => rw [hV]
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
    conv_lhs => rw [← hV]
  rw [hVV, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- The one-label inverses are symmetric. -/
private lemma tree_pairV_transpose (hD : PrimData β M m) (t : ℝ) (s s' : Bool) :
    (pairV β M t s s')ᵀ = pairV β M t s s' := by
  rw [tree_pairV_eq, Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.transpose_smul, tree_pairX_transpose hD.symm]

private lemma tree_pairV_swap (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) (s s' : Bool) :
    pairV β M t s s' = pairV β M t s' s := by
  rw [tree_pairV_eq, tree_pairV_eq, tree_pairX_swap]

/-- The transpose of the pair kernel swaps the two signs. -/
private lemma tree_pairK_transpose (hD : PrimData β M m) {t : ℝ} (ht : |t| < 1) (s s' : Bool) :
    (pairK β M t s s')ᵀ = pairK β M t s' s := by
  rw [tree_pairK_eq, tree_pairK_eq, Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
    Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
    tree_pairX_transpose hD.symm, tree_pairX_swap β M s' s,
    tree_comm (tree_pairX_norm hD s s') ht]

end Pair

end Calculus

/-! ## The two polygons cut off by a diagonal

For a diagonal `(i, j)` of the `k`-gon, the vertices `0, …, i, j, …, k-1` form the polygon of
Cut_L and the vertices `i, …, j` the polygon of Cut_R of (5.6) [fo:eq:cuts]. -/

section Polygon

variable {k : ℕ}

/-- The cyclic offset without `mod`. -/
private lemma tree_polyOff_eq {n : ℕ} (v w : Fin n) :
    polyOff v w = if v.val ≤ w.val then w.val - v.val else w.val + n - v.val := by
  have := v.isLt
  have := w.isLt
  unfold polyOff
  split_ifs with h
  · rw [show w.val + n - v.val = (w.val - v.val) + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

private lemma tree_polyOff_cases {n : ℕ} (v w : Fin n) :
    (v.val ≤ w.val ∧ polyOff v w = w.val - v.val) ∨
      (w.val < v.val ∧ polyOff v w = w.val + n - v.val) := by
  rw [tree_polyOff_eq]
  split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨by omega, rfl⟩

/-- The value of the cyclic successor. -/
private lemma tree_finRotate_val {n : ℕ} (v : Fin n) :
    (finRotate n v).val = if v.val + 1 = n then 0 else v.val + 1 := by
  rcases n with _ | n
  · exact v.elim0
  · rw [coe_finRotate]
    by_cases h : v = Fin.last n
    · subst h; simp
    · have h' : v.val ≠ n := fun e => h (Fin.ext e)
      simp [h, h']

/-- The vertex map of the polygon of `Cut_{L,i,j}`. -/
private def tree_vL (i j : Fin k) (p : Fin (k + i - j + 1)) : Fin k :=
  ⟨if p.val ≤ i.val then p.val else p.val + j.val - i.val - 1, by
    have := p.isLt; have := i.isLt; have := j.isLt; split_ifs <;> omega⟩

/-- The vertex map of the polygon of `Cut_{R,i,j}`. -/
private def tree_vR (i j : Fin k) (q : Fin (j - i + 1)) : Fin k :=
  ⟨i.val + q.val, by have := q.isLt; have := i.isLt; have := j.isLt; omega⟩

private lemma tree_vL_val (i j : Fin k) (p : Fin (k + i - j + 1)) :
    (tree_vL i j p).val = if p.val ≤ i.val then p.val else p.val + j.val - i.val - 1 := rfl

private lemma tree_vR_val (i j : Fin k) (q : Fin (j - i + 1)) :
    (tree_vR i j q).val = i.val + q.val := rfl

private lemma tree_vL_cases (i j : Fin k) (p : Fin (k + i - j + 1)) :
    (p.val ≤ i.val ∧ (tree_vL i j p).val = p.val) ∨
      (i.val < p.val ∧ (tree_vL i j p).val = p.val + j.val - i.val - 1) := by
  rw [tree_vL_val]
  split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨by omega, rfl⟩

private lemma tree_vL_strictMono {i j : Fin k} (hij : i.val < j.val) :
    StrictMono (tree_vL i j) := by
  intro p p' h
  rw [Fin.lt_def, tree_vL_val, tree_vL_val]
  rw [Fin.lt_def] at h
  split_ifs <;> omega

private lemma tree_vR_strictMono (i j : Fin k) : StrictMono (tree_vR i j) := by
  intro q q' h
  rw [Fin.lt_def, tree_vR_val, tree_vR_val]
  rw [Fin.lt_def] at h
  omega

/-- The inverse of `tree_vL` on its range. -/
private def tree_uL (i j : Fin k) (v : Fin k) : Fin (k + i - j + 1) :=
  ⟨if v.val ≤ i.val then v.val else v.val + i.val + 1 - j.val, by
    have := v.isLt; have := i.isLt; have := j.isLt; split_ifs <;> omega⟩

/-- The inverse of `tree_vR` on its range. -/
private def tree_uR (i j : Fin k) (v : Fin k) : Fin (j - i + 1) :=
  ⟨if v.val ≤ j.val then v.val - i.val else 0, by split_ifs <;> omega⟩

private lemma tree_uL_val (i j v : Fin k) :
    (tree_uL i j v).val = if v.val ≤ i.val then v.val else v.val + i.val + 1 - j.val := rfl

private lemma tree_uR_val (i j v : Fin k) :
    (tree_uR i j v).val = if v.val ≤ j.val then v.val - i.val else 0 := rfl

private lemma tree_vL_uL {i j : Fin k} {v : Fin k}
    (hv : v.val ≤ i.val ∨ j.val ≤ v.val) : tree_vL i j (tree_uL i j v) = v := by
  apply Fin.ext
  rw [tree_vL_val, tree_uL_val]
  split_ifs <;> omega

private lemma tree_vR_uR {i j : Fin k} {v : Fin k} (hv : i.val ≤ v.val ∧ v.val ≤ j.val) :
    tree_vR i j (tree_uR i j v) = v := by
  apply Fin.ext
  rw [tree_vR_val, tree_uR_val]
  split_ifs <;> omega

private lemma tree_uL_vL {i j : Fin k} (hij : i.val < j.val) (p : Fin (k + i - j + 1)) :
    tree_uL i j (tree_vL i j p) = p := by
  have := p.isLt; have := j.isLt
  apply Fin.ext
  rw [tree_uL_val, tree_vL_val]
  split_ifs <;> omega

private lemma tree_uR_vR (i j : Fin k) (q : Fin (j - i + 1)) :
    tree_uR i j (tree_vR i j q) = q := by
  have := q.isLt; have := j.isLt
  apply Fin.ext
  rw [tree_uR_val, tree_vR_val]
  split_ifs <;> omega

private lemma tree_vL_inj {i j : Fin k} (hij : i.val < j.val) {p p' : Fin (k + i - j + 1)}
    (h : tree_vL i j p = tree_vL i j p') : p = p' :=
  (tree_vL_strictMono hij).injective h

private lemma tree_vR_inj {i j : Fin k} {q q' : Fin (j - i + 1)}
    (h : tree_vR i j q = tree_vR i j q') : q = q' :=
  (tree_vR_strictMono i j).injective h

/-- The cyclic order seen from a vertex is preserved by `tree_vL`. -/
private lemma tree_off_vL {i j : Fin k} (hij : i.val < j.val) (v w w' : Fin (k + i - j + 1)) :
    polyOff v w < polyOff v w' ↔
      polyOff (tree_vL i j v) (tree_vL i j w) < polyOff (tree_vL i j v) (tree_vL i j w') := by
  have := v.isLt; have := w.isLt; have := w'.isLt; have := j.isLt
  simp only [tree_polyOff_eq, tree_vL_val]
  split_ifs <;> omega

/-- The cyclic order seen from a vertex is preserved by `tree_vR`. -/
private lemma tree_off_vR (i j : Fin k) (v w w' : Fin (j - i + 1)) :
    polyOff v w < polyOff v w' ↔
      polyOff (tree_vR i j v) (tree_vR i j w) < polyOff (tree_vR i j v) (tree_vR i j w') := by
  have := v.isLt; have := w.isLt; have := w'.isLt; have := j.isLt
  simp only [tree_polyOff_eq, tree_vR_val, Nat.add_le_add_iff_left]
  split_ifs <;> omega

/-- The labels of Cut_L through the vertex map. -/
private lemma tree_cutLLab_eq {α : Type*} (a : Fin k → α) (i j : Fin k) (c : α)
    (p : Fin (k + i - j + 1)) :
    cutLLab a i j c p = if p.val = i.val then c else a (tree_vL i j p) := by
  unfold cutLLab
  split_ifs <;> first | omega | rfl | (congr 1; apply Fin.ext; simp [tree_vL_val]; omega)

private lemma tree_cutLSgn_eq (σ : Fin k → Bool) (i j : Fin k) (p : Fin (k + i - j + 1)) :
    cutLSgn σ i j p = σ (tree_vL i j p) := by
  unfold cutLSgn
  split_ifs with h1 <;> (congr 1; apply Fin.ext; simp [tree_vL_val, h1])

private lemma tree_cutRLab_eq {α : Type*} (a : Fin k → α) (i j : Fin k) (c : α)
    (q : Fin (j - i + 1)) :
    cutRLab a i j c q = if q.val = j.val - i.val then c else a (tree_vR i j q) := by
  have := q.isLt
  unfold cutRLab
  split_ifs with h1 h2 h2 <;> first | omega | rfl

private lemma tree_cutRSgn_eq (σ : Fin k → Bool) (i j : Fin k) (q : Fin (j - i + 1)) :
    cutRSgn σ i j q = σ (tree_vR i j q) := rfl

end Polygon

/-! ## Splitting a dissection along a diagonal -/

section Split

variable {k : ℕ}

private lemma tree_mem_polyDiags {n : ℕ} (e : Fin n × Fin n) :
    e ∈ polyDiags n ↔ e.1.val + 2 ≤ e.2.val ∧ ¬(e.1.val = 0 ∧ e.2.val + 1 = n) := by
  simp [polyDiags, IsPolyDiag]

private lemma tree_mem_dissections {n : ℕ} (F : Finset (Fin n × Fin n)) :
    F ∈ dissections n ↔ F ⊆ polyDiags n ∧ ∀ d ∈ F, ∀ e ∈ F, ¬DiagCross d e := by
  simp [dissections]

private lemma tree_diagCross_iff {n : ℕ} (d e : Fin n × Fin n) :
    DiagCross d e ↔ (d.1.val < e.1.val ∧ e.1.val < d.2.val ∧ d.2.val < e.2.val) ∨
      (e.1.val < d.1.val ∧ d.1.val < e.2.val ∧ e.2.val < d.2.val) := by
  unfold DiagCross
  simp only [Fin.lt_def]

private lemma tree_prod_ne {n : ℕ} {e d : Fin n × Fin n} (h : e ≠ d) :
    ¬(e.1.val = d.1.val ∧ e.2.val = d.2.val) :=
  fun h' => h (Prod.ext (Fin.ext h'.1) (Fin.ext h'.2))

/-- The dissection of the polygon of `Cut_{L,i,j}` induced by `F`. -/
private def tree_splitL (i j : Fin k) (F : Finset (Fin k × Fin k)) :
    Finset (Fin (k + i - j + 1) × Fin (k + i - j + 1)) :=
  Finset.univ.filter fun e =>
    (tree_vL i j e.1, tree_vL i j e.2) ∈ F ∧ (tree_vL i j e.1, tree_vL i j e.2) ≠ (i, j)

/-- The dissection of the polygon of `Cut_{R,i,j}` induced by `F`. -/
private def tree_splitR (i j : Fin k) (F : Finset (Fin k × Fin k)) :
    Finset (Fin (j - i + 1) × Fin (j - i + 1)) :=
  Finset.univ.filter fun e =>
    (tree_vR i j e.1, tree_vR i j e.2) ∈ F ∧ (tree_vR i j e.1, tree_vR i j e.2) ≠ (i, j)

/-- The dissection of the `k`-gon glued from dissections of the two polygons and `(i, j)`. -/
private def tree_glue (i j : Fin k) (FL : Finset (Fin (k + i - j + 1) × Fin (k + i - j + 1)))
    (FR : Finset (Fin (j - i + 1) × Fin (j - i + 1))) : Finset (Fin k × Fin k) :=
  insert (i, j) (FL.image (fun e => (tree_vL i j e.1, tree_vL i j e.2)) ∪
    FR.image (fun e => (tree_vR i j e.1, tree_vR i j e.2)))

private lemma tree_mem_splitL {i j : Fin k} {F : Finset (Fin k × Fin k)}
    (e : Fin (k + i - j + 1) × Fin (k + i - j + 1)) :
    e ∈ tree_splitL i j F ↔
      (tree_vL i j e.1, tree_vL i j e.2) ∈ F ∧ (tree_vL i j e.1, tree_vL i j e.2) ≠ (i, j) := by
  simp [tree_splitL]

private lemma tree_mem_splitR {i j : Fin k} {F : Finset (Fin k × Fin k)}
    (e : Fin (j - i + 1) × Fin (j - i + 1)) :
    e ∈ tree_splitR i j F ↔
      (tree_vR i j e.1, tree_vR i j e.2) ∈ F ∧ (tree_vR i j e.1, tree_vR i j e.2) ≠ (i, j) := by
  simp [tree_splitR]

/-- Every other diagonal of a dissection containing `(i, j)` lies on one side of it. -/
private lemma tree_cover {i j : Fin k} {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k)
    (hd : (i, j) ∈ F) {e : Fin k × Fin k} (he : e ∈ F) (hne : e ≠ (i, j)) :
    ((e.1.val ≤ i.val ∨ j.val ≤ e.1.val) ∧ (e.2.val ≤ i.val ∨ j.val ≤ e.2.val)) ∨
      ((i.val ≤ e.1.val ∧ e.1.val ≤ j.val) ∧ (i.val ≤ e.2.val ∧ e.2.val ≤ j.val)) := by
  rw [tree_mem_dissections] at hF
  have h0 := (tree_mem_polyDiags _).mp (hF.1 he)
  have h1 := hF.2 _ hd _ he
  have h2 := hF.2 _ he _ hd
  have h3 := tree_prod_ne hne
  rw [tree_diagCross_iff] at h1 h2
  simp only at h1 h2 h3
  omega

private lemma tree_splitL_mem {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) :
    tree_splitL i j F ∈ dissections (k + i - j + 1) := by
  have hdv := (tree_mem_polyDiags _).mp hd
  simp only at hdv
  rw [tree_mem_dissections] at hF ⊢
  refine ⟨fun e he => ?_, fun d' hd' e he => ?_⟩
  · rw [tree_mem_splitL] at he
    have h1 := (tree_mem_polyDiags _).mp (hF.1 he.1)
    have h2 := tree_prod_ne he.2
    rw [tree_mem_polyDiags]
    simp only [tree_vL_val] at h1 h2
    have := e.1.isLt; have := e.2.isLt; have := j.isLt
    split_ifs at h1 h2 <;> omega
  · rw [tree_mem_splitL] at hd' he
    have h := hF.2 _ hd'.1 _ he.1
    rw [tree_diagCross_iff] at h ⊢
    simp only [tree_vL_val] at h
    split_ifs at h <;> omega

private lemma tree_splitR_mem {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) :
    tree_splitR i j F ∈ dissections (j - i + 1) := by
  have hdv := (tree_mem_polyDiags _).mp hd
  simp only at hdv
  rw [tree_mem_dissections] at hF ⊢
  refine ⟨fun e he => ?_, fun d' hd' e he => ?_⟩
  · rw [tree_mem_splitR] at he
    have h1 := (tree_mem_polyDiags _).mp (hF.1 he.1)
    have h2 := tree_prod_ne he.2
    rw [tree_mem_polyDiags]
    simp only [tree_vR_val] at h1 h2
    have := e.1.isLt; have := e.2.isLt; have := j.isLt
    omega
  · rw [tree_mem_splitR] at hd' he
    have h := hF.2 _ hd'.1 _ he.1
    rw [tree_diagCross_iff] at h ⊢
    simp only [tree_vR_val] at h
    omega

private lemma tree_glue_mem {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {FL : Finset (Fin (k + i - j + 1) × Fin (k + i - j + 1))}
    {FR : Finset (Fin (j - i + 1) × Fin (j - i + 1))}
    (hL : FL ∈ dissections (k + i - j + 1)) (hR : FR ∈ dissections (j - i + 1)) :
    tree_glue i j FL FR ∈ dissections k := by
  have hdv := (tree_mem_polyDiags _).mp hd
  simp only at hdv
  have hj := j.isLt
  rw [tree_mem_dissections] at hL hR ⊢
  refine ⟨fun e he => ?_, fun e he f hf => ?_⟩
  · simp only [tree_glue, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at he
    rcases he with rfl | ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
    · exact hd
    · have h1 := (tree_mem_polyDiags _).mp (hL.1 ha)
      have := a.1.isLt; have := a.2.isLt
      rw [tree_mem_polyDiags]
      simp only [tree_vL_val]
      split_ifs <;> omega
    · have h1 := (tree_mem_polyDiags _).mp (hR.1 hb)
      have := b.1.isLt; have := b.2.isLt
      rw [tree_mem_polyDiags]
      simp only [tree_vR_val]
      omega
  · simp only [tree_glue, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at he hf
    rw [tree_diagCross_iff]
    rcases he with rfl | ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩ <;>
      rcases hf with rfl | ⟨a', ha', rfl⟩ | ⟨b', hb', rfl⟩
    · omega
    · have h1 := (tree_mem_polyDiags _).mp (hL.1 ha')
      have := a'.1.isLt; have := a'.2.isLt
      simp only [tree_vL_val]
      split_ifs <;> omega
    · have h1 := (tree_mem_polyDiags _).mp (hR.1 hb')
      have := b'.1.isLt; have := b'.2.isLt
      simp only [tree_vR_val]
      omega
    · have h1 := (tree_mem_polyDiags _).mp (hL.1 ha)
      have := a.1.isLt; have := a.2.isLt
      simp only [tree_vL_val]
      split_ifs <;> omega
    · have h1 := (tree_mem_polyDiags _).mp (hL.1 ha)
      have h2 := (tree_mem_polyDiags _).mp (hL.1 ha')
      have h3 := hL.2 _ ha _ ha'
      rw [tree_diagCross_iff] at h3
      have := a.1.isLt; have := a.2.isLt; have := a'.1.isLt; have := a'.2.isLt
      simp only [tree_vL_val]
      split_ifs <;> omega
    · have h1 := (tree_mem_polyDiags _).mp (hL.1 ha)
      have h2 := (tree_mem_polyDiags _).mp (hR.1 hb')
      have := a.1.isLt; have := a.2.isLt; have := b'.1.isLt; have := b'.2.isLt
      simp only [tree_vL_val, tree_vR_val]
      split_ifs <;> omega
    · have h1 := (tree_mem_polyDiags _).mp (hR.1 hb)
      have := b.1.isLt; have := b.2.isLt
      simp only [tree_vR_val]
      omega
    · have h1 := (tree_mem_polyDiags _).mp (hR.1 hb)
      have h2 := (tree_mem_polyDiags _).mp (hL.1 ha')
      have := b.1.isLt; have := b.2.isLt; have := a'.1.isLt; have := a'.2.isLt
      simp only [tree_vL_val, tree_vR_val]
      split_ifs <;> omega
    · have h1 := (tree_mem_polyDiags _).mp (hR.1 hb)
      have h2 := (tree_mem_polyDiags _).mp (hR.1 hb')
      have h3 := hR.2 _ hb _ hb'
      rw [tree_diagCross_iff] at h3
      have := b.1.isLt; have := b.2.isLt; have := b'.1.isLt; have := b'.2.isLt
      simp only [tree_vR_val]
      omega

private lemma tree_glue_split {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F) :
    tree_glue i j (tree_splitL i j F) (tree_splitR i j F) = F := by
  have hdv := (tree_mem_polyDiags _).mp hd
  simp only at hdv
  ext e
  simp only [tree_glue, Finset.mem_insert, Finset.mem_union, Finset.mem_image, tree_mem_splitL,
    tree_mem_splitR]
  constructor
  · rintro (rfl | ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
    · exact hdF
    · exact ha.1
    · exact hb.1
  · intro he
    by_cases hne : e = (i, j)
    · exact Or.inl hne
    right
    rcases tree_cover hF hdF he hne with h | h
    · left
      refine ⟨(tree_uL i j e.1, tree_uL i j e.2), ?_, ?_⟩ <;>
        simp only [tree_vL_uL h.1, tree_vL_uL h.2]
      exact ⟨he, hne⟩
    · right
      refine ⟨(tree_uR i j e.1, tree_uR i j e.2), ?_, ?_⟩ <;>
        simp only [tree_vR_uR h.1, tree_vR_uR h.2]
      exact ⟨he, hne⟩

private lemma tree_splitL_glue {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {FL : Finset (Fin (k + i - j + 1) × Fin (k + i - j + 1))}
    {FR : Finset (Fin (j - i + 1) × Fin (j - i + 1))}
    (hL : FL ∈ dissections (k + i - j + 1)) (hR : FR ∈ dissections (j - i + 1)) :
    tree_splitL i j (tree_glue i j FL FR) = FL := by
  have hdv := (tree_mem_polyDiags _).mp hd
  simp only at hdv
  have hj := j.isLt
  rw [tree_mem_dissections] at hL hR
  ext e
  rw [tree_mem_splitL]
  simp only [tree_glue, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨h | ⟨a, ha, he⟩ | ⟨b, hb, he⟩, hne⟩
    · exact absurd h hne
    · have h1 : a = e := by
        have := congrArg Prod.fst he; have := congrArg Prod.snd he
        exact Prod.ext (tree_vL_inj (by omega) (by assumption))
          (tree_vL_inj (by omega) (by assumption))
      exact h1 ▸ ha
    · exfalso
      have h1 := (tree_mem_polyDiags _).mp (hR.1 hb)
      have h2 := tree_prod_ne hne
      have e1 := congrArg (fun x => x.1.val) he
      have e2 := congrArg (fun x => x.2.val) he
      have := b.1.isLt; have := b.2.isLt; have := e.1.isLt; have := e.2.isLt
      simp only [tree_vL_val, tree_vR_val] at e1 e2 h2
      split_ifs at e1 e2 h2 <;> omega
  · intro he
    have h1 := (tree_mem_polyDiags _).mp (hL.1 he)
    refine ⟨Or.inr (Or.inl ⟨e, he, rfl⟩), fun h => ?_⟩
    have e1 := congrArg (fun x => x.1.val) h
    have e2 := congrArg (fun x => x.2.val) h
    have := e.1.isLt; have := e.2.isLt
    simp only [tree_vL_val] at e1 e2
    split_ifs at e1 e2 <;> omega

private lemma tree_splitR_glue {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {FL : Finset (Fin (k + i - j + 1) × Fin (k + i - j + 1))}
    {FR : Finset (Fin (j - i + 1) × Fin (j - i + 1))}
    (hL : FL ∈ dissections (k + i - j + 1)) (hR : FR ∈ dissections (j - i + 1)) :
    tree_splitR i j (tree_glue i j FL FR) = FR := by
  have hdv := (tree_mem_polyDiags _).mp hd
  simp only at hdv
  have hj := j.isLt
  rw [tree_mem_dissections] at hL hR
  ext e
  rw [tree_mem_splitR]
  simp only [tree_glue, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨h | ⟨a, ha, he⟩ | ⟨b, hb, he⟩, hne⟩
    · exact absurd h hne
    · exfalso
      have h1 := (tree_mem_polyDiags _).mp (hL.1 ha)
      have h2 := tree_prod_ne hne
      have e1 := congrArg (fun x => x.1.val) he
      have e2 := congrArg (fun x => x.2.val) he
      have := a.1.isLt; have := a.2.isLt; have := e.1.isLt; have := e.2.isLt
      simp only [tree_vL_val, tree_vR_val] at e1 e2 h2
      split_ifs at e1 e2 h2 <;> omega
    · have h1 : b = e := by
        have := congrArg Prod.fst he; have := congrArg Prod.snd he
        exact Prod.ext (tree_vR_inj (by assumption)) (tree_vR_inj (by assumption))
      exact h1 ▸ hb
  · intro he
    have h1 := (tree_mem_polyDiags _).mp (hR.1 he)
    refine ⟨Or.inr (Or.inr ⟨e, he, rfl⟩), fun h => ?_⟩
    have e1 := congrArg (fun x => x.1.val) h
    have e2 := congrArg (fun x => x.2.val) h
    have := e.1.isLt; have := e.2.isLt
    simp only [tree_vR_val] at e1 e2
    omega

/-- Marking the diagonal `(i, j)` in a dissection is a bijection onto the pairs of dissections
of the two polygons of the cut. -/
private lemma tree_sum_split {i j : Fin k} (hd : (i, j) ∈ polyDiags k) {γ : Type*}
    [AddCommMonoid γ]
    (H : Finset (Fin (k + i - j + 1) × Fin (k + i - j + 1)) →
      Finset (Fin (j - i + 1) × Fin (j - i + 1)) → γ) :
    ∑ F ∈ (dissections k).filter (fun F => (i, j) ∈ F), H (tree_splitL i j F) (tree_splitR i j F)
      = ∑ FL ∈ dissections (k + i - j + 1), ∑ FR ∈ dissections (j - i + 1), H FL FR := by
  rw [← Finset.sum_product']
  apply Finset.sum_nbij' (fun F => (tree_splitL i j F, tree_splitR i j F))
    (fun p => tree_glue i j p.1 p.2)
  · intro F hF
    rw [Finset.mem_filter] at hF
    rw [Finset.mem_product]
    exact ⟨tree_splitL_mem hd hF.1, tree_splitR_mem hd hF.1⟩
  · intro p hp
    rw [Finset.mem_product] at hp
    rw [Finset.mem_filter]
    exact ⟨tree_glue_mem hd hp.1 hp.2, Finset.mem_insert_self _ _⟩
  · intro F hF
    rw [Finset.mem_filter] at hF
    exact tree_glue_split hd hF.1 hF.2
  · intro p hp
    rw [Finset.mem_product] at hp
    exact Prod.ext (tree_splitL_glue hd hp.1 hp.2) (tree_splitR_glue hd hp.1 hp.2)
  · intro F _
    rfl

end Split

/-! ## Face corners of the two polygons of a cut -/

section Corners

variable {k : ℕ}

private lemma tree_minmax {n : ℕ} {v u : Fin n} (h : u ≠ v) :
    ((min v u).val = v.val ∧ (max v u).val = u.val ∧ v.val < u.val) ∨
      ((min v u).val = u.val ∧ (max v u).val = v.val ∧ u.val < v.val) := by
  rcases lt_or_gt_of_ne h with h' | h'
  · right
    rw [min_eq_right h'.le, max_eq_left h'.le]
    exact ⟨rfl, rfl, h'⟩
  · left
    rw [min_eq_left h'.le, max_eq_right h'.le]
    exact ⟨rfl, rfl, h'⟩

private lemma tree_mem_polyCorners {n : ℕ} (F : Finset (Fin n × Fin n)) (v : Fin n)
    (p : Fin n × Fin n) :
    p ∈ polyCorners F v ↔ PolyNbr F v p.1 ∧ PolyNbr F v p.2 ∧ polyOff v p.1 < polyOff v p.2 ∧
      ∀ u, PolyNbr F v u → ¬(polyOff v p.1 < polyOff v u ∧ polyOff v u < polyOff v p.2) := by
  simp [polyCorners]

/-- Neighbours in a dissection containing `(i, j)` lie on a common side of it. -/
private lemma tree_nbr_side {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F) {v u : Fin k}
    (h : PolyNbr F v u) :
    ((v.val ≤ i.val ∨ j.val ≤ v.val) ∧ (u.val ≤ i.val ∨ j.val ≤ u.val)) ∨
      ((i.val ≤ v.val ∧ v.val ≤ j.val) ∧ (i.val ≤ u.val ∧ u.val ≤ j.val)) := by
  have hdv := (tree_mem_polyDiags _).mp hd
  simp only at hdv
  have := v.isLt; have := u.isLt
  obtain ⟨hne, h⟩ := h
  have hmm := tree_minmax hne
  rcases h with h | h | h
  · rw [tree_polyOff_eq] at h; split_ifs at h <;> omega
  · rw [tree_polyOff_eq] at h; split_ifs at h <;> omega
  · by_cases he : (min v u, max v u) = (i, j)
    · have e1 := congrArg (fun x => x.1.val) he
      have e2 := congrArg (fun x => x.2.val) he
      simp only at e1 e2
      omega
    · have := tree_cover hF hdF h he
      simp only at this
      omega

/-- `tree_vL` preserves and reflects neighbours. -/
private lemma tree_nbr_vL {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) (v w : Fin (k + i - j + 1)) :
    PolyNbr F (tree_vL i j v) (tree_vL i j w) ↔ PolyNbr (tree_splitL i j F) v w := by
  have hdv := (tree_mem_polyDiags _).mp hd
  simp only at hdv
  have hmono := (tree_vL_strictMono (i := i) (j := j) (by omega)).monotone
  unfold PolyNbr
  rw [← hmono.map_min, ← hmono.map_max, tree_mem_splitL]
  by_cases hw : w = v
  · subst hw; simp
  have hw' : tree_vL i j w ≠ tree_vL i j v := fun h => hw (tree_vL_inj (by omega) h)
  have hmm := tree_minmax hw
  have := v.isLt; have := w.isLt; have := j.isLt
  have key : ((tree_vL i j (min v w), tree_vL i j (max v w)) = (i, j) →
      (polyOff v w = 1 ∨ polyOff v w + 1 = k + i - j + 1)) ∧
      ((tree_vL i j (min v w), tree_vL i j (max v w)) ≠ (i, j) →
        ((polyOff (tree_vL i j v) (tree_vL i j w) = 1 ∨
          polyOff (tree_vL i j v) (tree_vL i j w) + 1 = k) ↔
        (polyOff v w = 1 ∨ polyOff v w + 1 = k + i - j + 1))) := by
    constructor
    · intro he
      have e1 := congrArg (fun x => x.1.val) he
      have e2 := congrArg (fun x => x.2.val) he
      simp only [tree_vL_val] at e1 e2
      simp only [tree_polyOff_eq]
      split_ifs at e1 e2 ⊢ <;> omega
    · intro he
      have he' := tree_prod_ne he
      simp only [tree_vL_val] at he'
      simp only [tree_polyOff_eq, tree_vL_val]
      split_ifs at he' ⊢ <;> omega
  by_cases hq : (tree_vL i j (min v w), tree_vL i j (max v w)) = (i, j)
  · have hB := key.1 hq
    rw [hq]
    exact ⟨fun _ => ⟨hw, hB.elim Or.inl (fun h => Or.inr (Or.inl h))⟩,
      fun _ => ⟨hw', Or.inr (Or.inr hdF)⟩⟩
  · have hAB := key.2 hq
    constructor
    · rintro ⟨-, h⟩
      refine ⟨hw, ?_⟩
      rcases h with h | h | h
      · exact (hAB.mp (Or.inl h)).elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact (hAB.mp (Or.inr h)).elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact Or.inr (Or.inr ⟨h, hq⟩)
    · rintro ⟨-, h⟩
      refine ⟨hw', ?_⟩
      rcases h with h | h | h
      · exact (hAB.mpr (Or.inl h)).elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact (hAB.mpr (Or.inr h)).elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact Or.inr (Or.inr h.1)

/-- `tree_vR` preserves and reflects neighbours. -/
private lemma tree_nbr_vR {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) (v w : Fin (j - i + 1)) :
    PolyNbr F (tree_vR i j v) (tree_vR i j w) ↔ PolyNbr (tree_splitR i j F) v w := by
  have hdv := (tree_mem_polyDiags _).mp hd
  simp only at hdv
  have hmono := (tree_vR_strictMono i j).monotone
  unfold PolyNbr
  rw [← hmono.map_min, ← hmono.map_max, tree_mem_splitR]
  by_cases hw : w = v
  · subst hw; simp
  have hw' : tree_vR i j w ≠ tree_vR i j v := fun h => hw (tree_vR_inj h)
  have hmm := tree_minmax hw
  have := v.isLt; have := w.isLt; have := j.isLt
  have key : ((tree_vR i j (min v w), tree_vR i j (max v w)) = (i, j) →
      (polyOff v w = 1 ∨ polyOff v w + 1 = j - i + 1)) ∧
      ((tree_vR i j (min v w), tree_vR i j (max v w)) ≠ (i, j) →
        ((polyOff (tree_vR i j v) (tree_vR i j w) = 1 ∨
          polyOff (tree_vR i j v) (tree_vR i j w) + 1 = k) ↔
        (polyOff v w = 1 ∨ polyOff v w + 1 = j - i + 1))) := by
    constructor
    · intro he
      have e1 := congrArg (fun x => x.1.val) he
      have e2 := congrArg (fun x => x.2.val) he
      simp only [tree_vR_val] at e1 e2
      simp only [tree_polyOff_eq]
      split_ifs <;> omega
    · intro he
      have he' := tree_prod_ne he
      simp only [tree_vR_val] at he'
      simp only [tree_polyOff_eq, tree_vR_val, Nat.add_le_add_iff_left]
      split_ifs <;> omega
  by_cases hq : (tree_vR i j (min v w), tree_vR i j (max v w)) = (i, j)
  · have hB := key.1 hq
    rw [hq]
    exact ⟨fun _ => ⟨hw, hB.elim Or.inl (fun h => Or.inr (Or.inl h))⟩,
      fun _ => ⟨hw', Or.inr (Or.inr hdF)⟩⟩
  · have hAB := key.2 hq
    constructor
    · rintro ⟨-, h⟩
      refine ⟨hw, ?_⟩
      rcases h with h | h | h
      · exact (hAB.mp (Or.inl h)).elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact (hAB.mp (Or.inr h)).elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact Or.inr (Or.inr ⟨h, hq⟩)
    · rintro ⟨-, h⟩
      refine ⟨hw', ?_⟩
      rcases h with h | h | h
      · exact (hAB.mpr (Or.inl h)).elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact (hAB.mpr (Or.inr h)).elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact Or.inr (Or.inr h.1)

/-- The face corners of a dissection as a set of triples `(v, w, w')`. -/
private def tree_cornerP {n : ℕ} (F : Finset (Fin n × Fin n)) : Finset (Fin n × (Fin n × Fin n)) :=
  Finset.univ.filter fun x => x.2 ∈ polyCorners F x.1

private lemma tree_prod_corners {n : ℕ} (F : Finset (Fin n × Fin n))
    (f : Fin n → Fin n × Fin n → ℂ) :
    ∏ v, ∏ p ∈ polyCorners F v, f v p = ∏ x ∈ tree_cornerP F, f x.1 x.2 := by
  rw [tree_cornerP, Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun v _ => ?_
  dsimp only
  rw [Finset.prod_ite_mem, Finset.univ_inter]

private lemma tree_nbr_diag {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) : PolyNbr F i j ∧ PolyNbr F j i := by
  have hdv := (tree_mem_polyDiags _).mp hd
  simp only at hdv
  have hle : i ≤ j := by rw [Fin.le_def]; omega
  have hne : j ≠ i := fun h => by rw [h] at hdv; omega
  refine ⟨⟨hne, Or.inr (Or.inr ?_)⟩, ⟨hne.symm, Or.inr (Or.inr ?_)⟩⟩
  · rwa [min_eq_left hle, max_eq_right hle]
  · rwa [min_eq_right hle, max_eq_left hle]

private lemma tree_corner_toL {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) {v w w' : Fin k}
    (hv : v.val ≤ i.val ∨ j.val ≤ v.val) (hw : w.val ≤ i.val ∨ j.val ≤ w.val)
    (hw' : w'.val ≤ i.val ∨ j.val ≤ w'.val) (h : (w, w') ∈ polyCorners F v) :
    (tree_uL i j w, tree_uL i j w') ∈ polyCorners (tree_splitL i j F) (tree_uL i j v) := by
  have hdv := (tree_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  rw [← tree_vL_uL hv, ← tree_vL_uL hw, ← tree_vL_uL hw'] at h
  rw [tree_mem_polyCorners] at h ⊢
  dsimp only at h ⊢
  obtain ⟨n1, n2, o, nb⟩ := h
  refine ⟨(tree_nbr_vL hd hdF _ _).mp n1, (tree_nbr_vL hd hdF _ _).mp n2,
    (tree_off_vL hij _ _ _).mpr o, fun u hu => ?_⟩
  rw [tree_off_vL hij _ _ u, tree_off_vL hij _ u _]
  exact nb _ ((tree_nbr_vL hd hdF _ _).mpr hu)

private lemma tree_corner_toR {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) {v w w' : Fin k}
    (hv : i.val ≤ v.val ∧ v.val ≤ j.val) (hw : i.val ≤ w.val ∧ w.val ≤ j.val)
    (hw' : i.val ≤ w'.val ∧ w'.val ≤ j.val) (h : (w, w') ∈ polyCorners F v) :
    (tree_uR i j w, tree_uR i j w') ∈ polyCorners (tree_splitR i j F) (tree_uR i j v) := by
  rw [← tree_vR_uR hv, ← tree_vR_uR hw, ← tree_vR_uR hw'] at h
  rw [tree_mem_polyCorners] at h ⊢
  dsimp only at h ⊢
  obtain ⟨n1, n2, o, nb⟩ := h
  refine ⟨(tree_nbr_vR hd hdF _ _).mp n1, (tree_nbr_vR hd hdF _ _).mp n2,
    (tree_off_vR i j _ _ _).mpr o, fun u hu => ?_⟩
  rw [tree_off_vR i j _ _ u, tree_off_vR i j _ u _]
  exact nb _ ((tree_nbr_vR hd hdF _ _).mpr hu)

private lemma tree_corner_fromL {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F)
    {v w w' : Fin (k + i - j + 1)} (h : (w, w') ∈ polyCorners (tree_splitL i j F) v) :
    (tree_vL i j w, tree_vL i j w') ∈ polyCorners F (tree_vL i j v) := by
  have hdv := (tree_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  rw [tree_mem_polyCorners] at h ⊢
  dsimp only at h ⊢
  obtain ⟨n1, n2, o, nb⟩ := h
  refine ⟨(tree_nbr_vL hd hdF _ _).mpr n1, (tree_nbr_vL hd hdF _ _).mpr n2,
    (tree_off_vL hij _ _ _).mp o, fun u hu => ?_⟩
  by_cases huL : u.val ≤ i.val ∨ j.val ≤ u.val
  · rw [← tree_vL_uL huL] at hu ⊢
    rw [← tree_off_vL hij, ← tree_off_vL hij]
    exact nb _ ((tree_nbr_vL hd hdF _ _).mp hu)
  · have hs := tree_nbr_side hd hF hdF hu
    have h1 : w ≠ v := n1.1
    have h2 : w' ≠ v := n2.1
    have h1' : w.val ≠ v.val := fun e => h1 (Fin.ext e)
    have h2' : w'.val ≠ v.val := fun e => h2 (Fin.ext e)
    have := v.isLt; have := w.isLt; have := w'.isLt; have := u.isLt
    simp only [tree_vL_val] at hs
    simp only [tree_polyOff_eq, tree_vL_val]
    split_ifs at hs ⊢ <;> omega

private lemma tree_corner_fromR {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F)
    {v w w' : Fin (j - i + 1)} (h : (w, w') ∈ polyCorners (tree_splitR i j F) v) :
    (tree_vR i j w, tree_vR i j w') ∈ polyCorners F (tree_vR i j v) := by
  have hdv := (tree_mem_polyDiags _).mp hd
  simp only at hdv
  rw [tree_mem_polyCorners] at h ⊢
  dsimp only at h ⊢
  obtain ⟨n1, n2, o, nb⟩ := h
  refine ⟨(tree_nbr_vR hd hdF _ _).mpr n1, (tree_nbr_vR hd hdF _ _).mpr n2,
    (tree_off_vR i j _ _ _).mp o, fun u hu => ?_⟩
  by_cases huR : i.val ≤ u.val ∧ u.val ≤ j.val
  · rw [← tree_vR_uR huR] at hu ⊢
    rw [← tree_off_vR, ← tree_off_vR]
    exact nb _ ((tree_nbr_vR hd hdF _ _).mp hu)
  · have hs := tree_nbr_side hd hF hdF hu
    have h1 : w ≠ v := n1.1
    have h2 : w' ≠ v := n2.1
    have h1' : w.val ≠ v.val := fun e => h1 (Fin.ext e)
    have h2' : w'.val ≠ v.val := fun e => h2 (Fin.ext e)
    have := v.isLt; have := w.isLt; have := w'.isLt; have := u.isLt; have := j.isLt
    simp only [tree_vR_val] at hs
    have c1 := tree_polyOff_cases (tree_vR i j v) (tree_vR i j w)
    have c2 := tree_polyOff_cases (tree_vR i j v) u
    have c3 := tree_polyOff_cases (tree_vR i j v) (tree_vR i j w')
    simp only [tree_vR_val] at c1 c2 c3
    omega

/-- Every face corner lies in one of the two polygons of the cut. -/
private lemma tree_corner_sides {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F) {v w w' : Fin k}
    (h : (w, w') ∈ polyCorners F v) :
    ((v.val ≤ i.val ∨ j.val ≤ v.val) ∧ (w.val ≤ i.val ∨ j.val ≤ w.val) ∧
        (w'.val ≤ i.val ∨ j.val ≤ w'.val)) ∨
      ((i.val ≤ v.val ∧ v.val ≤ j.val) ∧ (i.val ≤ w.val ∧ w.val ≤ j.val) ∧
        (i.val ≤ w'.val ∧ w'.val ≤ j.val)) := by
  have hdv := (tree_mem_polyDiags _).mp hd
  simp only at hdv
  rw [tree_mem_polyCorners] at h
  dsimp only at h
  obtain ⟨n1, n2, o, nb⟩ := h
  have s1 := tree_nbr_side hd hF hdF n1
  have s2 := tree_nbr_side hd hF hdF n2
  have h1' : w.val ≠ v.val := fun e => n1.1 (Fin.ext e)
  have h2' : w'.val ≠ v.val := fun e => n2.1 (Fin.ext e)
  have := v.isLt; have := w.isLt; have := w'.isLt; have := j.isLt
  by_cases hvi : v = i
  · subst hvi
    have hb := nb j (tree_nbr_diag hd hdF).1
    have c1 := tree_polyOff_cases v w
    have c2 := tree_polyOff_cases v w'
    have c3 := tree_polyOff_cases v j
    omega
  by_cases hvj : v = j
  · subst hvj
    have hb := nb i (tree_nbr_diag hd hdF).2
    have c1 := tree_polyOff_cases v w
    have c2 := tree_polyOff_cases v w'
    have c3 := tree_polyOff_cases v i
    omega
  have hvi' : v.val ≠ i.val := fun e => hvi (Fin.ext e)
  have hvj' : v.val ≠ j.val := fun e => hvj (Fin.ext e)
  omega

/-- The face corners of `F` are those of the two polygons of the cut, transported by the vertex
maps. -/
private lemma tree_prod_cornerP_split {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F)
    (g : Fin k × (Fin k × Fin k) → ℂ) :
    ∏ x ∈ tree_cornerP F, g x =
      (∏ x ∈ tree_cornerP (tree_splitL i j F),
        g (tree_vL i j x.1, (tree_vL i j x.2.1, tree_vL i j x.2.2))) *
      ∏ x ∈ tree_cornerP (tree_splitR i j F),
        g (tree_vR i j x.1, (tree_vR i j x.2.1, tree_vR i j x.2.2)) := by
  have hdv := (tree_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  set ψL : Fin (k + i - j + 1) × (Fin (k + i - j + 1) × Fin (k + i - j + 1)) →
      Fin k × (Fin k × Fin k) := fun x => (tree_vL i j x.1, (tree_vL i j x.2.1, tree_vL i j x.2.2))
  set ψR : Fin (j - i + 1) × (Fin (j - i + 1) × Fin (j - i + 1)) →
      Fin k × (Fin k × Fin k) := fun x => (tree_vR i j x.1, (tree_vR i j x.2.1, tree_vR i j x.2.2))
  have hS : tree_cornerP F = (tree_cornerP (tree_splitL i j F)).image ψL ∪
      (tree_cornerP (tree_splitR i j F)).image ψR := by
    ext ⟨v, w, w'⟩
    simp only [tree_cornerP, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro h
      rcases tree_corner_sides hd hF hdF h with ⟨hv, hw, hw'⟩ | ⟨hv, hw, hw'⟩
      · left
        refine ⟨(tree_uL i j v, (tree_uL i j w, tree_uL i j w')),
          tree_corner_toL hd hdF hv hw hw' h, ?_⟩
        simp only [ψL, tree_vL_uL hv, tree_vL_uL hw, tree_vL_uL hw']
      · right
        refine ⟨(tree_uR i j v, (tree_uR i j w, tree_uR i j w')),
          tree_corner_toR hd hdF hv hw hw' h, ?_⟩
        simp only [ψR, tree_vR_uR hv, tree_vR_uR hw, tree_vR_uR hw']
    · rintro (⟨x, hx, hxe⟩ | ⟨x, hx, hxe⟩)
      · simp only [ψL, Prod.mk.injEq] at hxe
        obtain ⟨rfl, rfl, rfl⟩ := hxe
        exact tree_corner_fromL hd hF hdF hx
      · simp only [ψR, Prod.mk.injEq] at hxe
        obtain ⟨rfl, rfl, rfl⟩ := hxe
        exact tree_corner_fromR hd hF hdF hx
  have hinjL : Set.InjOn ψL (tree_cornerP (tree_splitL i j F)) := by
    intro x _ y _ hxy
    simp only [ψL, Prod.mk.injEq] at hxy
    exact Prod.ext (tree_vL_inj hij hxy.1)
      (Prod.ext (tree_vL_inj hij hxy.2.1) (tree_vL_inj hij hxy.2.2))
  have hinjR : Set.InjOn ψR (tree_cornerP (tree_splitR i j F)) := by
    intro x _ y _ hxy
    simp only [ψR, Prod.mk.injEq] at hxy
    exact Prod.ext (tree_vR_inj hxy.1) (Prod.ext (tree_vR_inj hxy.2.1) (tree_vR_inj hxy.2.2))
  have hdisj : Disjoint ((tree_cornerP (tree_splitL i j F)).image ψL)
      ((tree_cornerP (tree_splitR i j F)).image ψR) := by
    rw [Finset.disjoint_left]
    rintro z hzL hzR
    simp only [Finset.mem_image, tree_cornerP, Finset.mem_filter, Finset.mem_univ,
      true_and] at hzL hzR
    obtain ⟨x, hx, rfl⟩ := hzL
    obtain ⟨y, hy, hxy⟩ := hzR
    simp only [ψL, ψR, Prod.mk.injEq] at hxy
    obtain ⟨e1, e2, e3⟩ := hxy
    rw [tree_mem_polyCorners] at hx
    obtain ⟨n1, n2, o, -⟩ := hx
    have h1 : x.2.1.val ≠ x.1.val := fun e => n1.1 (Fin.ext e)
    have h2 : x.2.2.val ≠ x.1.val := fun e => n2.1 (Fin.ext e)
    have h3 : x.2.1.val ≠ x.2.2.val := by
      intro e
      have : x.2.1 = x.2.2 := Fin.ext e
      rw [this] at o
      exact lt_irrefl _ o
    have f1 := congrArg Fin.val e1
    have f2 := congrArg Fin.val e2
    have f3 := congrArg Fin.val e3
    have := y.1.isLt; have := y.2.1.isLt; have := y.2.2.isLt; have := j.isLt
    have := x.1.isLt; have := x.2.1.isLt; have := x.2.2.isLt
    simp only [tree_vL_val, tree_vR_val] at f1 f2 f3
    split_ifs at f1 f2 f3 <;> omega
  rw [hS, Finset.prod_union hdisj, Finset.prod_image hinjL, Finset.prod_image hinjR]


private lemma tree_corner_conds {n : ℕ} {F : Finset (Fin n × Fin n)} {v : Fin n}
    {p : Fin n × Fin n} (h : p ∈ polyCorners F v) :
    PolyNbr F v p.1 ∧ PolyNbr F v p.2 ∧ polyOff v p.1 + 1 ≠ n ∧ polyOff v p.2 ≠ 1 := by
  rw [tree_mem_polyCorners] at h
  obtain ⟨n1, n2, o, -⟩ := h
  have h1 : p.1.val ≠ v.val := fun e => n1.1 (Fin.ext e)
  have h2 : p.2.val ≠ v.val := fun e => n2.1 (Fin.ext e)
  have c1 := tree_polyOff_cases v p.1
  have c2 := tree_polyOff_cases v p.2
  have := v.isLt; have := p.1.isLt; have := p.2.isLt
  exact ⟨n1, n2, by omega, by omega⟩

/-- The diagonals of the polygon of Cut_L as diagonals of `F`. -/
private def tree_ιL (i j : Fin k) (F : Finset (Fin k × Fin k)) (e : ↥(tree_splitL i j F)) : ↥F :=
  ⟨(tree_vL i j e.1.1, tree_vL i j e.1.2), ((tree_mem_splitL _).mp e.2).1⟩

/-- The diagonals of the polygon of Cut_R as diagonals of `F`. -/
private def tree_ιR (i j : Fin k) (F : Finset (Fin k × Fin k)) (e : ↥(tree_splitR i j F)) : ↥F :=
  ⟨(tree_vR i j e.1.1, tree_vR i j e.1.2), ((tree_mem_splitR _).mp e.2).1⟩

/-- The edge labels of the polygon of Cut_L: the side `i` carries the outer copy of the
label of `(i, j)`. -/
private lemma tree_edgeLab_L {L : ℕ} {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) (y : Fin k → Fin L) (cIn cOut : ↥F → Fin L)
    {v w : Fin (k + i - j + 1)} (hn : PolyNbr (tree_splitL i j F) v w) (small : Bool)
    (hs : if small then polyOff v w ≠ 1 else polyOff v w + 1 ≠ k + i - j + 1) :
    edgeLab (tree_splitL i j F)
        (fun p => if p.val = i.val then cOut ⟨(i, j), hdF⟩ else y (tree_vL i j p))
        (fun e => cIn (tree_ιL i j F e)) (fun e => cOut (tree_ιL i j F e)) v w small =
      edgeLab F y cIn cOut (tree_vL i j v) (tree_vL i j w) small := by
  have hdv := (tree_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  have hsm := tree_vL_strictMono (i := i) (j := j) hij
  have hmono := hsm.monotone
  simp only [edgeLab, ← hmono.map_min, ← hmono.map_max]
  obtain ⟨hne, hside⟩ := hn
  have hmm := tree_minmax hne
  have cv := tree_vL_cases i j v
  have cw := tree_vL_cases i j w
  have co := tree_polyOff_cases v w
  have co' := tree_polyOff_cases (tree_vL i j v) (tree_vL i j w)
  have := v.isLt; have := w.isLt; have := j.isLt
  have hlt : decide (v < w) = decide (tree_vL i j v < tree_vL i j w) := by
    simp only [hsm.lt_iff_lt]
  by_cases h' : (min v w, max v w) ∈ tree_splitL i j F
  · have h1 : (tree_vL i j (min v w), tree_vL i j (max v w)) ∈ F :=
      ((tree_mem_splitL _).mp h').1
    rw [dite_eq_left h', dite_eq_left h1, hlt]
    rfl
  · rw [dite_eq_right h']
    have hside' : polyOff v w = 1 ∨ polyOff v w + 1 = k + i - j + 1 := by
      rcases hside with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h h'
    by_cases hq : (tree_vL i j (min v w), tree_vL i j (max v w)) = (i, j)
    · have h1 : (tree_vL i j (min v w), tree_vL i j (max v w)) ∈ F := hq ▸ hdF
      rw [dite_eq_left h1]
      have e1 := congrArg (fun x => x.1.val) hq
      have e2 := congrArg (fun x => x.2.val) hq
      have cmin := tree_vL_cases i j (min v w)
      have cmax := tree_vL_cases i j (max v w)
      simp only at e1 e2
      have hsub : (⟨(tree_vL i j (min v w), tree_vL i j (max v w)), h1⟩ : ↥F) = ⟨(i, j), hdF⟩ :=
        Subtype.ext hq
      cases small
      · simp only [Bool.false_eq_true, ite_false] at hs
        have hv : v.val = i.val := by omega
        have hw : ¬ tree_vL i j v < tree_vL i j w → False := by
          intro h; rw [Fin.lt_def] at h; omega
        have hpos : polyOff v w = 1 := by omega
        rw [ite_eq_left hpos, ite_eq_left hv, hsub]
        have : decide (tree_vL i j v < tree_vL i j w) = true := by
          by_contra hc; exact hw (by simpa using hc)
        rw [this]
        rfl
      · simp only [ite_true] at hs
        have hw : w.val = i.val := by omega
        have hv : ¬ tree_vL i j v < tree_vL i j w := by
          rw [Fin.lt_def]; omega
        rw [ite_eq_right hs, ite_eq_left hw, hsub]
        simp [hv]
    · have h1 : (tree_vL i j (min v w), tree_vL i j (max v w)) ∉ F :=
        fun h => h' ((tree_mem_splitL _).mpr ⟨h, hq⟩)
      rw [dite_eq_right h1]
      clear hmm
      by_cases h1 : polyOff v w = 1
      · have h2 : polyOff (tree_vL i j v) (tree_vL i j w) = 1 := by
          have hq' := tree_prod_ne hq
          simp only at hq'
          have hw1 : (w.val = v.val + 1) ∨ (v.val + 1 = k + i - j + 1 ∧ w.val = 0) := by omega
          rcases hw1 with hw1 | hw1
          · have hvw : v < w := by rw [Fin.lt_def]; omega
            rw [min_eq_left hvw.le, max_eq_right hvw.le] at hq'
            omega
          · have hvw : w < v := by rw [Fin.lt_def]; omega
            rw [min_eq_right hvw.le, max_eq_left hvw.le] at hq'
            omega
        have h3 : v.val ≠ i.val := by
          clear co'
          have hmm := tree_minmax hne
          have hq' := tree_prod_ne hq
          have cmin := tree_vL_cases i j (min v w)
          have cmax := tree_vL_cases i j (max v w)
          simp only at hq'
          omega
        rw [ite_eq_left h1, ite_eq_left h2, ite_eq_right h3]
      · have h2 : polyOff (tree_vL i j v) (tree_vL i j w) ≠ 1 := by omega
        have h3 : w.val ≠ i.val := by
          clear co'
          have hmm := tree_minmax hne
          have hq' := tree_prod_ne hq
          have cmin := tree_vL_cases i j (min v w)
          have cmax := tree_vL_cases i j (max v w)
          simp only at hq'
          omega
        rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]

/-- The edge labels of the polygon of Cut_R: the last side carries the inner copy of the
label of `(i, j)`. -/
private lemma tree_edgeLab_R {L : ℕ} {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) (y : Fin k → Fin L) (cIn cOut : ↥F → Fin L)
    {v w : Fin (j - i + 1)} (hn : PolyNbr (tree_splitR i j F) v w) (small : Bool)
    (hs : if small then polyOff v w ≠ 1 else polyOff v w + 1 ≠ j - i + 1) :
    edgeLab (tree_splitR i j F)
        (fun q => if q.val = j.val - i.val then cIn ⟨(i, j), hdF⟩ else y (tree_vR i j q))
        (fun e => cIn (tree_ιR i j F e)) (fun e => cOut (tree_ιR i j F e)) v w small =
      edgeLab F y cIn cOut (tree_vR i j v) (tree_vR i j w) small := by
  have hdv := (tree_mem_polyDiags _).mp hd
  simp only at hdv
  have hsm := tree_vR_strictMono i j
  have hmono := hsm.monotone
  simp only [edgeLab, ← hmono.map_min, ← hmono.map_max]
  obtain ⟨hne, hside⟩ := hn
  have hmm := tree_minmax hne
  have cv := tree_vR_val i j v
  have cw := tree_vR_val i j w
  have co := tree_polyOff_cases v w
  have co' := tree_polyOff_cases (tree_vR i j v) (tree_vR i j w)
  have := v.isLt; have := w.isLt; have := j.isLt
  have hlt : decide (v < w) = decide (tree_vR i j v < tree_vR i j w) := by
    simp only [hsm.lt_iff_lt]
  by_cases h' : (min v w, max v w) ∈ tree_splitR i j F
  · have h1 : (tree_vR i j (min v w), tree_vR i j (max v w)) ∈ F :=
      ((tree_mem_splitR _).mp h').1
    rw [dite_eq_left h', dite_eq_left h1, hlt]
    rfl
  · rw [dite_eq_right h']
    have hside' : polyOff v w = 1 ∨ polyOff v w + 1 = j - i + 1 := by
      rcases hside with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h h'
    by_cases hq : (tree_vR i j (min v w), tree_vR i j (max v w)) = (i, j)
    · have h1 : (tree_vR i j (min v w), tree_vR i j (max v w)) ∈ F := hq ▸ hdF
      rw [dite_eq_left h1]
      have e1 := congrArg (fun x => x.1.val) hq
      have e2 := congrArg (fun x => x.2.val) hq
      have cmin := tree_vR_val i j (min v w)
      have cmax := tree_vR_val i j (max v w)
      simp only at e1 e2
      have hsub : (⟨(tree_vR i j (min v w), tree_vR i j (max v w)), h1⟩ : ↥F) = ⟨(i, j), hdF⟩ :=
        Subtype.ext hq
      cases small
      · simp only [Bool.false_eq_true, ite_false] at hs
        have hv : v.val = j.val - i.val := by omega
        have hw : ¬ tree_vR i j v < tree_vR i j w := by
          rw [Fin.lt_def]; omega
        have hpos : polyOff v w = 1 := by omega
        rw [ite_eq_left hpos, ite_eq_left hv, hsub]
        simp [hw]
      · simp only [ite_true] at hs
        have hw : w.val = j.val - i.val := by omega
        have hv : tree_vR i j v < tree_vR i j w := by
          rw [Fin.lt_def]; omega
        rw [ite_eq_right hs, ite_eq_left hw, hsub]
        simp [hv]
    · have h1 : (tree_vR i j (min v w), tree_vR i j (max v w)) ∉ F :=
        fun h => h' ((tree_mem_splitR _).mpr ⟨h, hq⟩)
      rw [dite_eq_right h1]
      clear hmm
      by_cases h1 : polyOff v w = 1
      · have h2 : polyOff (tree_vR i j v) (tree_vR i j w) = 1 := by
          have hq' := tree_prod_ne hq
          simp only at hq'
          have hw1 : (w.val = v.val + 1) ∨ (v.val + 1 = j - i + 1 ∧ w.val = 0) := by omega
          rcases hw1 with hw1 | hw1
          · have hvw : v < w := by rw [Fin.lt_def]; omega
            rw [min_eq_left hvw.le, max_eq_right hvw.le] at hq'
            omega
          · have hvw : w < v := by rw [Fin.lt_def]; omega
            rw [min_eq_right hvw.le, max_eq_left hvw.le] at hq'
            omega
        have h3 : v.val ≠ j.val - i.val := by
          clear co'
          have hmm := tree_minmax hne
          have hq' := tree_prod_ne hq
          have cmin := tree_vR_val i j (min v w)
          have cmax := tree_vR_val i j (max v w)
          simp only at hq'
          omega
        rw [ite_eq_left h1, ite_eq_left h2, ite_eq_right h3]
      · have h2 : polyOff (tree_vR i j v) (tree_vR i j w) ≠ 1 := by omega
        have h3 : w.val ≠ j.val - i.val := by
          clear co'
          have hmm := tree_minmax hne
          have hq' := tree_prod_ne hq
          have cmin := tree_vR_val i j (min v w)
          have cmax := tree_vR_val i j (max v w)
          simp only at hq'
          omega
        rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]


/-- The corner product of `F` splits into the corner products of the two polygons of the cut,
with the outer copy of the label of `(i, j)` on the side `i` of Cut_L and its inner copy on
the last side of Cut_R. -/
private lemma tree_corners_split {L : ℕ} {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F)
    (M : Matrix (Fin L) (Fin L) ℂ) (σ : Fin k → Bool) (y : Fin k → Fin L)
    (cIn cOut : ↥F → Fin L) :
    (∏ v : Fin k, ∏ p ∈ polyCorners F v,
        sgnMat M (σ v) (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false)) =
      (∏ v : Fin (k + i - j + 1), ∏ p ∈ polyCorners (tree_splitL i j F) v,
        sgnMat M (cutLSgn σ i j v)
          (edgeLab (tree_splitL i j F)
            (fun p => if p.val = i.val then cOut ⟨(i, j), hdF⟩ else y (tree_vL i j p))
            (fun e => cIn (tree_ιL i j F e)) (fun e => cOut (tree_ιL i j F e)) v p.2 true)
          (edgeLab (tree_splitL i j F)
            (fun p => if p.val = i.val then cOut ⟨(i, j), hdF⟩ else y (tree_vL i j p))
            (fun e => cIn (tree_ιL i j F e)) (fun e => cOut (tree_ιL i j F e)) v p.1 false)) *
      (∏ v : Fin (j - i + 1), ∏ p ∈ polyCorners (tree_splitR i j F) v,
        sgnMat M (cutRSgn σ i j v)
          (edgeLab (tree_splitR i j F)
            (fun q => if q.val = j.val - i.val then cIn ⟨(i, j), hdF⟩ else y (tree_vR i j q))
            (fun e => cIn (tree_ιR i j F e)) (fun e => cOut (tree_ιR i j F e)) v p.2 true)
          (edgeLab (tree_splitR i j F)
            (fun q => if q.val = j.val - i.val then cIn ⟨(i, j), hdF⟩ else y (tree_vR i j q))
            (fun e => cIn (tree_ιR i j F e)) (fun e => cOut (tree_ιR i j F e)) v p.1 false)) := by
  rw [tree_prod_corners, tree_prod_corners, tree_prod_corners,
    tree_prod_cornerP_split hd hF hdF]
  congr 1
  · refine Finset.prod_congr rfl fun x hx => ?_
    simp only [tree_cornerP, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨n1, n2, c1, c2⟩ := tree_corner_conds hx
    rw [tree_cutLSgn_eq, tree_edgeLab_L hd hdF y cIn cOut n2 true (by simpa using c2),
      tree_edgeLab_L hd hdF y cIn cOut n1 false (by simpa using c1)]
  · refine Finset.prod_congr rfl fun x hx => ?_
    simp only [tree_cornerP, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨n1, n2, c1, c2⟩ := tree_corner_conds hx
    rw [tree_cutRSgn_eq, tree_edgeLab_R hd hdF y cIn cOut n2 true (by simpa using c2),
      tree_edgeLab_R hd hdF y cIn cOut n1 false (by simpa using c1)]

end Corners

/-! ## The core of a dissection with one link differentiated -/

section Glue

variable {k L : ℕ}

private lemma tree_sum_pair {T Y : Type*} [Fintype T] [DecidableEq T] [Fintype Y]
    (G : (T → Y) → (T → Y) → ℂ) :
    ∑ cIn : T → Y, ∑ cOut : T → Y, G cIn cOut =
      ∑ c : T → Y × Y, G (fun t => (c t).1) (fun t => (c t).2) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow T (fun _ => Y) (fun _ => Y)) _ _
    (fun c => rfl)).symm

private lemma tree_sum_option {A B T X : Type} [Fintype A] [Fintype B] [Fintype T]
    [DecidableEq A] [DecidableEq B] [DecidableEq T] [Fintype X] (e : Option (A ⊕ B) ≃ T)
    (G : (T → X) → ℂ) :
    ∑ c : T → X, G c = ∑ x : X, ∑ f : A → X, ∑ g : B → X,
      G (fun t => Option.elim (e.symm t) x (Sum.elim f g)) := by
  let E : X × ((A → X) × (B → X)) ≃ (T → X) :=
    ((Equiv.prodCongr (Equiv.refl X) (Equiv.sumArrowEquivProdArrow A B X).symm).trans
      (Equiv.piOptionEquivProd (α := A ⊕ B) (β := fun _ => X)).symm).trans
      (Equiv.arrowCongr e (Equiv.refl X))
  rw [← E.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun g _ => ?_
  congr 1
  funext t
  simp only [E, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.prodCongr_apply,
    Equiv.coe_refl, Prod.map, id, Function.comp_apply, Equiv.refl_apply]
  cases e.symm t with
  | none => rfl
  | some a => cases a <;> rfl

/-- The diagonals of `F`: `(i, j)` and those of the two polygons of the cut. -/
private def tree_eqvFun (i j : Fin k) (F : Finset (Fin k × Fin k)) (hdF : (i, j) ∈ F) :
    Option (↥(tree_splitL i j F) ⊕ ↥(tree_splitR i j F)) → ↥F
  | none => ⟨(i, j), hdF⟩
  | some (Sum.inl a) => tree_ιL i j F a
  | some (Sum.inr b) => tree_ιR i j F b

private lemma tree_eqvFun_bij {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F) :
    Function.Bijective (tree_eqvFun i j F hdF) := by
  have hdv := (tree_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  have hFL := tree_splitL_mem hd hF
  have hFR := tree_splitR_mem hd hF
  rw [tree_mem_dissections] at hFL hFR
  have hj := j.isLt
  constructor
  · intro o o' h
    rcases o with _ | a | b <;> rcases o' with _ | a' | b'
    · rfl
    · exfalso
      have := ((tree_mem_splitL _).mp a'.2).2
      exact this (congrArg Subtype.val h).symm
    · exfalso
      have := ((tree_mem_splitR _).mp b'.2).2
      exact this (congrArg Subtype.val h).symm
    · exfalso
      have := ((tree_mem_splitL _).mp a.2).2
      exact this (congrArg Subtype.val h)
    · have h1 := congrArg Subtype.val h
      simp only [tree_eqvFun, tree_ιL, Prod.mk.injEq] at h1
      have e1 := tree_vL_inj hij h1.1
      have e2 := tree_vL_inj hij h1.2
      rw [Subtype.ext (Prod.ext e1 e2)]
    · exfalso
      have h1 := congrArg Subtype.val h
      simp only [tree_eqvFun, tree_ιL, tree_ιR, Prod.mk.injEq] at h1
      have ha := (tree_mem_polyDiags _).mp (hFL.1 a.2)
      have f1 := congrArg Fin.val h1.1
      have f2 := congrArg Fin.val h1.2
      have ca1 := tree_vL_cases i j a.1.1
      have ca2 := tree_vL_cases i j a.1.2
      have hne := tree_prod_ne ((tree_mem_splitL _).mp a.2).2
      simp only [tree_vR_val] at f1 f2
      simp only at hne
      have := a.1.1.isLt; have := a.1.2.isLt; have := b'.1.1.isLt; have := b'.1.2.isLt
      omega
    · exfalso
      have := ((tree_mem_splitR _).mp b.2).2
      exact this (congrArg Subtype.val h)
    · exfalso
      have h1 := congrArg Subtype.val h
      simp only [tree_eqvFun, tree_ιL, tree_ιR, Prod.mk.injEq] at h1
      have ha := (tree_mem_polyDiags _).mp (hFL.1 a'.2)
      have f1 := congrArg Fin.val h1.1
      have f2 := congrArg Fin.val h1.2
      have ca1 := tree_vL_cases i j a'.1.1
      have ca2 := tree_vL_cases i j a'.1.2
      have hne := tree_prod_ne ((tree_mem_splitL _).mp a'.2).2
      simp only [tree_vR_val] at f1 f2
      simp only at hne
      have := a'.1.1.isLt; have := a'.1.2.isLt; have := b.1.1.isLt; have := b.1.2.isLt
      omega
    · have h1 := congrArg Subtype.val h
      simp only [tree_eqvFun, tree_ιR, Prod.mk.injEq] at h1
      have e1 := tree_vR_inj h1.1
      have e2 := tree_vR_inj h1.2
      rw [Subtype.ext (Prod.ext e1 e2)]
  · intro e
    by_cases he : e.1 = (i, j)
    · exact ⟨none, Subtype.ext he.symm⟩
    rcases tree_cover hF hdF e.2 he with h | h
    · refine ⟨some (Sum.inl ⟨(tree_uL i j e.1.1, tree_uL i j e.1.2), ?_⟩), ?_⟩
      · rw [tree_mem_splitL]
        simp only [tree_vL_uL h.1, tree_vL_uL h.2]
        exact ⟨e.2, he⟩
      · apply Subtype.ext
        simp only [tree_eqvFun, tree_ιL, tree_vL_uL h.1, tree_vL_uL h.2]
    · refine ⟨some (Sum.inr ⟨(tree_uR i j e.1.1, tree_uR i j e.1.2), ?_⟩), ?_⟩
      · rw [tree_mem_splitR]
        simp only [tree_vR_uR h.1, tree_vR_uR h.2]
        exact ⟨e.2, he⟩
      · apply Subtype.ext
        simp only [tree_eqvFun, tree_ιR, tree_vR_uR h.1, tree_vR_uR h.2]

/-- The core of `F` in which the link of the diagonal `d` is its time derivative
`β V_t V_t`. -/
private def tree_coreD (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) (σ : Fin k → Bool)
    (F : Finset (Fin k × Fin k)) (d : Fin k × Fin k) (y : Fin k → Fin L) : ℂ :=
  ∑ cIn : ↥F → Fin L, ∑ cOut : ↥F → Fin L,
    (∏ e : ↥F, if e.1 = d then
        (β : ℂ) * (pairV β M t (σ e.1.1) (σ e.1.2) * pairV β M t (σ e.1.1) (σ e.1.2))
          (cOut e) (cIn e)
      else ((β * t : ℝ) : ℂ) * pairV β M t (σ e.1.1) (σ e.1.2) (cOut e) (cIn e)) *
      ∏ v : Fin k, ∏ p ∈ polyCorners F v,
        sgnMat M (σ v) (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false)

/-- The differentiated link of `(i, j)` glues the cores of the two polygons of the cut. -/
private lemma tree_coreD_split {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {t : ℝ}
    {σ : Fin k → Bool} {i j : Fin k} (hd : (i, j) ∈ polyDiags k) {F : Finset (Fin k × Fin k)}
    (hF : F ∈ dissections k) (hdF : (i, j) ∈ F) (y : Fin k → Fin L) :
    tree_coreD β M t σ F (i, j) y =
      ∑ xo : Fin L, ∑ xi : Fin L,
        (β : ℂ) * (pairV β M t (σ i) (σ j) * pairV β M t (σ i) (σ j)) xo xi *
          dissCore β M t (cutLSgn σ i j) (tree_splitL i j F)
            (fun p => if p.val = i.val then xo else y (tree_vL i j p)) *
          dissCore β M t (cutRSgn σ i j) (tree_splitR i j F)
            (fun q => if q.val = j.val - i.val then xi else y (tree_vR i j q)) := by
  set e := Equiv.ofBijective _ (tree_eqvFun_bij hd hF hdF) with he_def
  have he0 : e none = ⟨(i, j), hdF⟩ := rfl
  have heL : ∀ a, e (some (Sum.inl a)) = tree_ιL i j F a := fun a => rfl
  have heR : ∀ b, e (some (Sum.inr b)) = tree_ιR i j F b := fun b => rfl
  have hs0 : e.symm ⟨(i, j), hdF⟩ = none := by rw [← he0, Equiv.symm_apply_apply]
  have hsL : ∀ a, e.symm (tree_ιL i j F a) = some (Sum.inl a) := fun a => by
    rw [← heL, Equiv.symm_apply_apply]
  have hsR : ∀ b, e.symm (tree_ιR i j F b) = some (Sum.inr b) := fun b => by
    rw [← heR, Equiv.symm_apply_apply]
  have hL : ∀ a : ↥(tree_splitL i j F), ¬(tree_ιL i j F a).1 = (i, j) :=
    fun a => ((tree_mem_splitL _).mp a.2).2
  have hR : ∀ b : ↥(tree_splitR i j F), ¬(tree_ιR i j F b).1 = (i, j) :=
    fun b => ((tree_mem_splitR _).mp b.2).2
  unfold tree_coreD
  rw [tree_sum_pair, tree_sum_option e, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun xo _ => Finset.sum_congr rfl fun xi _ => ?_
  unfold dissCore
  rw [tree_sum_pair, tree_sum_pair, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [tree_corners_split hd hF hdF M σ y]
  rw [← e.prod_comp, Fintype.prod_option, Fintype.prod_sum_type]
  simp only [he0, heL, heR, hs0, hsL, hsR, Option.elim, Sum.elim_inl,
    Sum.elim_inr, ite_true, hL, hR, ite_false]
  have hvL : ∀ a : ↥(tree_splitL i j F),
      (tree_ιL i j F a).1 = (tree_vL i j a.1.1, tree_vL i j a.1.2) := fun a => rfl
  have hvR : ∀ b : ↥(tree_splitR i j F),
      (tree_ιR i j F b).1 = (tree_vR i j b.1.1, tree_vR i j b.1.2) := fun b => rfl
  simp only [hvL, hvR, tree_cutLSgn_eq, tree_cutRSgn_eq]
  ring

end Glue

/-! ## The external labels of the two polygons of a cut -/

section Sides

variable {k L : ℕ}

/-- The side `i` of the polygon of Cut_L. -/
private def tree_iL (i j : Fin k) : Fin (k + i - j + 1) := ⟨i.val, by have := j.isLt; omega⟩

/-- The last side of the polygon of Cut_R. -/
private def tree_lastR (i j : Fin k) : Fin (j - i + 1) := ⟨j.val - i.val, by omega⟩

private lemma tree_vL_rot {i j : Fin k} (hd : (i, j) ∈ polyDiags k) {p : Fin (k + i - j + 1)}
    (hp : p.val ≠ i.val) : tree_vL i j (finRotate _ p) = finRotate k (tree_vL i j p) := by
  have hdv := (tree_mem_polyDiags _).mp hd
  simp only at hdv
  have := p.isLt; have := j.isLt
  apply Fin.ext
  rw [tree_finRotate_val, tree_vL_val, tree_vL_val, tree_finRotate_val]
  split_ifs <;> omega

private lemma tree_vL_rot_iL {i j : Fin k} (hd : (i, j) ∈ polyDiags k) :
    tree_vL i j (finRotate _ (tree_iL i j)) = j := by
  have hdv := (tree_mem_polyDiags _).mp hd
  simp only at hdv
  have := j.isLt
  have hr : (finRotate _ (tree_iL i j)).val = i.val + 1 := by
    have h1 := tree_finRotate_val (tree_iL i j)
    have h0 : (tree_iL i j).val = i.val := rfl
    split_ifs at h1 <;> omega
  have h2 := tree_vL_cases i j (finRotate _ (tree_iL i j))
  apply Fin.ext
  omega

private lemma tree_vR_rot {i j : Fin k} (hd : (i, j) ∈ polyDiags k) {q : Fin (j - i + 1)}
    (hq : q.val ≠ j.val - i.val) : tree_vR i j (finRotate _ q) = finRotate k (tree_vR i j q) := by
  have hdv := (tree_mem_polyDiags _).mp hd
  simp only at hdv
  have := q.isLt; have := j.isLt
  apply Fin.ext
  rw [tree_finRotate_val, tree_vR_val, tree_vR_val, tree_finRotate_val]
  split_ifs <;> omega

private lemma tree_vR_rot_lastR {i j : Fin k} (hd : (i, j) ∈ polyDiags k) :
    tree_vR i j (finRotate _ (tree_lastR i j)) = i := by
  have hdv := (tree_mem_polyDiags _).mp hd
  simp only at hdv
  apply Fin.ext
  rw [tree_vR_val, tree_finRotate_val]
  simp only [tree_lastR]
  split_ifs <;> omega

/-- The sides of the `k`-gon are the sides of the two polygons other than the side `(i, j)`. -/
private lemma tree_prod_sides {i j : Fin k} (hd : (i, j) ∈ polyDiags k) (h : Fin k → ℂ) :
    ∏ s, h s = (∏ p ∈ Finset.univ.erase (tree_iL i j), h (tree_vL i j p)) *
      ∏ q ∈ Finset.univ.erase (tree_lastR i j), h (tree_vR i j q) := by
  have hdv := (tree_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  have hj := j.isLt
  have hU : (Finset.univ : Finset (Fin k)) =
      (Finset.univ.erase (tree_iL i j)).image (tree_vL i j) ∪
        (Finset.univ.erase (tree_lastR i j)).image (tree_vR i j) := by
    ext s
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_image, Finset.mem_erase, ne_eq,
      and_true, true_iff]
    by_cases hs : s.val < i.val ∨ j.val ≤ s.val
    · left
      refine ⟨tree_uL i j s, fun h => ?_, tree_vL_uL (by omega)⟩
      have := congrArg Fin.val h
      simp only [tree_uL_val, tree_iL] at this
      split_ifs at this <;> omega
    · right
      refine ⟨tree_uR i j s, fun h => ?_, tree_vR_uR (by omega)⟩
      have := congrArg Fin.val h
      simp only [tree_uR_val, tree_lastR] at this
      split_ifs at this <;> omega
  have hdisj : Disjoint ((Finset.univ.erase (tree_iL i j)).image (tree_vL i j))
      ((Finset.univ.erase (tree_lastR i j)).image (tree_vR i j)) := by
    rw [Finset.disjoint_left]
    intro s h1 h2
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true] at h1 h2
    obtain ⟨p, hp, rfl⟩ := h1
    obtain ⟨q, hq, hpq⟩ := h2
    have e := congrArg Fin.val hpq
    have hp' : p.val ≠ i.val := fun h => hp (Fin.ext h)
    have hq' : q.val ≠ j.val - i.val := fun h => hq (Fin.ext h)
    have := p.isLt; have := q.isLt
    have cp := tree_vL_cases i j p
    rw [tree_vR_val] at e
    omega
  rw [hU, Finset.prod_union hdisj,
    Finset.prod_image (fun p _ q _ h => tree_vL_inj hij h),
    Finset.prod_image (fun p _ q _ h => tree_vR_inj h)]

/-- The external pre-labels of `F` and the two copies of the label of `(i, j)` are the external
pre-labels of the two polygons of the cut. -/
private lemma tree_sum_labels {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    (G : (Fin (k + i - j + 1) → Fin L) → (Fin (j - i + 1) → Fin L) → ℂ) :
    ∑ zL : Fin (k + i - j + 1) → Fin L, ∑ zR : Fin (j - i + 1) → Fin L, G zL zR =
      ∑ y : Fin k → Fin L, ∑ xo : Fin L, ∑ xi : Fin L,
        G (fun p => if p.val = i.val then xo else y (tree_vL i j p))
          (fun q => if q.val = j.val - i.val then xi else y (tree_vR i j q)) := by
  have hdv := (tree_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  have hj := j.isLt
  let E : (Fin k → Fin L) × (Fin L × Fin L) ≃
      (Fin (k + i - j + 1) → Fin L) × (Fin (j - i + 1) → Fin L) :=
    { toFun := fun x => (fun p => if p.val = i.val then x.2.1 else x.1 (tree_vL i j p),
        fun q => if q.val = j.val - i.val then x.2.2 else x.1 (tree_vR i j q))
      invFun := fun z => (fun s => if s.val < i.val ∨ j.val ≤ s.val then z.1 (tree_uL i j s)
          else z.2 (tree_uR i j s), (z.1 (tree_iL i j), z.2 (tree_lastR i j)))
      left_inv := by
        rintro ⟨y, xo, xi⟩
        simp only [tree_iL, tree_lastR, ite_true, Prod.mk.injEq, and_true]
        funext s
        by_cases hs : s.val < i.val ∨ j.val ≤ s.val
        · rw [ite_eq_left hs]
          have : (tree_uL i j s).val ≠ i.val := by
            rw [tree_uL_val]; split_ifs <;> omega
          rw [ite_eq_right this, tree_vL_uL (by omega)]
        · rw [ite_eq_right hs]
          have : (tree_uR i j s).val ≠ j.val - i.val := by
            rw [tree_uR_val]; split_ifs <;> omega
          rw [ite_eq_right this, tree_vR_uR (by omega)]
      right_inv := by
        rintro ⟨zL, zR⟩
        simp only [Prod.mk.injEq]
        constructor
        · funext p
          by_cases hp : p.val = i.val
          · rw [ite_eq_left hp]
            congr 1
            exact Fin.ext hp.symm
          · rw [ite_eq_right hp]
            have cp := tree_vL_cases i j p
            have hs : (tree_vL i j p).val < i.val ∨ j.val ≤ (tree_vL i j p).val := by omega
            rw [ite_eq_left hs, tree_uL_vL hij]
        · funext q
          by_cases hq : q.val = j.val - i.val
          · rw [ite_eq_left hq]
            congr 1
            exact Fin.ext hq.symm
          · rw [ite_eq_right hq]
            have := q.isLt
            have hs : ¬((tree_vR i j q).val < i.val ∨ j.val ≤ (tree_vR i j q).val) := by
              rw [tree_vR_val]; omega
            rw [ite_eq_right hs, tree_uR_vR] }
  rw [← Fintype.sum_prod_type', ← E.sum_comp, Fintype.sum_prod_type, Fintype.sum_congr]
  intro y
  rw [Fintype.sum_prod_type]
  rfl

/-- The external dressing of the polygon of Cut_L. -/
private lemma tree_dressL {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    (W : Bool → Bool → Fin L → Fin L → ℂ) (σ : Fin k → Bool) (a : Fin k → Fin L) (c : Fin L)
    (y : Fin k → Fin L) (xo : Fin L) :
    ∏ p, W (cutLSgn σ i j p) (cutLSgn σ i j (finRotate _ p)) (cutLLab a i j c p)
        (if p.val = i.val then xo else y (tree_vL i j p)) =
      W (σ i) (σ j) c xo * ∏ p ∈ Finset.univ.erase (tree_iL i j),
        W (σ (tree_vL i j p)) (σ (finRotate k (tree_vL i j p))) (a (tree_vL i j p))
          (y (tree_vL i j p)) := by
  have hdv := (tree_mem_polyDiags _).mp hd
  simp only at hdv
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (tree_iL i j))]
  have hvi : tree_vL i j (tree_iL i j) = i := by
    apply Fin.ext; rw [tree_vL_val]; simp [tree_iL]
  have hi : (tree_iL i j).val = i.val := rfl
  congr 1
  · rw [tree_cutLSgn_eq, tree_cutLSgn_eq, hvi, tree_vL_rot_iL hd, tree_cutLLab_eq, ite_eq_left hi,
      ite_eq_left hi]
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hp' : p.val ≠ i.val := fun h => (Finset.mem_erase.mp hp).1 (Fin.ext h)
    rw [tree_cutLSgn_eq, tree_cutLSgn_eq, tree_vL_rot hd hp', tree_cutLLab_eq, ite_eq_right hp',
      ite_eq_right hp']

/-- The external dressing of the polygon of Cut_R. -/
private lemma tree_dressR {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    (W : Bool → Bool → Fin L → Fin L → ℂ) (σ : Fin k → Bool) (a : Fin k → Fin L) (c : Fin L)
    (y : Fin k → Fin L) (xi : Fin L) :
    ∏ q, W (cutRSgn σ i j q) (cutRSgn σ i j (finRotate _ q)) (cutRLab a i j c q)
        (if q.val = j.val - i.val then xi else y (tree_vR i j q)) =
      W (σ j) (σ i) c xi * ∏ q ∈ Finset.univ.erase (tree_lastR i j),
        W (σ (tree_vR i j q)) (σ (finRotate k (tree_vR i j q))) (a (tree_vR i j q))
          (y (tree_vR i j q)) := by
  have hdv := (tree_mem_polyDiags _).mp hd
  simp only at hdv
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (tree_lastR i j))]
  have hvj : tree_vR i j (tree_lastR i j) = j := by
    apply Fin.ext; rw [tree_vR_val]; simp only [tree_lastR]; omega
  have hl : (tree_lastR i j).val = j.val - i.val := rfl
  congr 1
  · rw [tree_cutRSgn_eq, tree_cutRSgn_eq, hvj, tree_vR_rot_lastR hd, tree_cutRLab_eq,
      ite_eq_left hl, ite_eq_left hl]
  · refine Finset.prod_congr rfl fun q hq => ?_
    have hq' : q.val ≠ j.val - i.val := fun h => (Finset.mem_erase.mp hq).1 (Fin.ext h)
    rw [tree_cutRSgn_eq, tree_cutRSgn_eq, tree_vR_rot hd hq', tree_cutRLab_eq, ite_eq_right hq',
      ite_eq_right hq']

end Sides

/-! ## The marked-diagonal identity -/

section Key

variable {k L : ℕ}


private lemma tree_sum_swap3 {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] (b : ℂ)
    (A : X → Y → ℂ) (B : X → Z → ℂ) :
    b * ∑ x, (∑ y, A x y) * (∑ z, B x z) = ∑ y, ∑ z, b * ∑ x, A x y * B x z := by
  calc b * ∑ x, (∑ y, A x y) * (∑ z, B x z) = ∑ x, ∑ y, ∑ z, b * (A x y * B x z) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ y, ∑ x, ∑ z, b * (A x y * B x z) := Finset.sum_comm
    _ = ∑ y, ∑ z, ∑ x, b * (A x y * B x z) :=
        Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ = ∑ y, ∑ z, b * ∑ x, A x y * B x z := by simp only [Finset.mul_sum]

/-- The dressed core of `F` with the link of the diagonal `(i, j)` differentiated is `β` times
the product of the dressed values of the dissections of the two polygons of the cut, summed over
the new label `c`: the marked-diagonal step of the tree representation of (B.1)
[ba:eq:dissection]. -/
private lemma tree_key {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} (hD : PrimData β M m)
    (t : ℝ) (σ : Fin k → Bool) {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F)
    (a : Fin k → Fin L) :
    ∑ y : Fin k → Fin L, (∏ s, pairV β M t (σ s) (σ (finRotate k s)) (a s) (y s)) *
        tree_coreD β M t σ F (i, j) y =
      (β : ℂ) * ∑ c : Fin L, dissVal β M t (cutLSgn σ i j) (tree_splitL i j F) (cutLLab a i j c) *
        dissVal β M t (cutRSgn σ i j) (tree_splitR i j F) (cutRLab a i j c) := by
  simp only [tree_coreD_split hd hF hdF]
  unfold dissVal
  rw [tree_sum_swap3, tree_sum_labels hd]
  conv_lhs => simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun xo _ =>
    Finset.sum_congr rfl fun xi _ => ?_
  beta_reduce
  simp only [tree_dressL hd (pairV β M t) σ a, tree_dressR hd (pairV β M t) σ a]
  rw [tree_prod_sides hd (fun s => pairV β M t (σ s) (σ (finRotate k s)) (a s) (y s))]
  have hVV : (pairV β M t (σ i) (σ j) * pairV β M t (σ i) (σ j)) xo xi =
      ∑ c, pairV β M t (σ i) (σ j) c xo * pairV β M t (σ j) (σ i) c xi := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [tree_pairV_swap β M t (σ j) (σ i)]
    congr 1
    conv_lhs => rw [← tree_pairV_transpose hD t (σ i) (σ j)]
    rfl
  rw [hVV]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

end Key

/-! ## The time derivative of a dressed dissection value -/

section Deriv

variable {k L : ℕ}

private lemma tree_sum_perm1 {Y S C : Type*} [Fintype Y] [Fintype S] [Fintype C]
    (A : S → Y → ℂ) (K : S → C → ℂ) (V : S → C → Y → ℂ) (D : Y → ℂ) :
    ∑ y, (∑ s, A s y * ∑ c, K s c * V s c y) * D y =
      ∑ s, ∑ c, K s c * ∑ y, V s c y * A s y * D y := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun y _ => ?_
  ring

private lemma tree_sum_perm2 {Y C E : Type*} [Fintype Y] [Fintype C] [Fintype E]
    (P : Y → ℂ) (X : E → C → C → ℂ) (D : Y → C → C → ℂ) :
    ∑ y, P y * ∑ a, ∑ b, (∑ e, X e a b) * D y a b =
      ∑ e, ∑ y, P y * ∑ a, ∑ b, X e a b * D y a b := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  calc ∑ y, ∑ a, ∑ b, ∑ e, P y * (X e a b * D y a b)
      = ∑ y, ∑ a, ∑ e, ∑ b, P y * (X e a b * D y a b) :=
        Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ y, ∑ e, ∑ a, ∑ b, P y * (X e a b * D y a b) :=
        Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ = ∑ e, ∑ y, ∑ a, ∑ b, P y * (X e a b * D y a b) := Finset.sum_comm

private lemma tree_prod_update (g : Fin k → Fin L → ℂ) (a : Fin k → Fin L) (s : Fin k)
    (c : Fin L) :
    ∏ s', g s' (Function.update a s c s') = g s c * ∏ s' ∈ Finset.univ.erase s, g s' (a s') := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ s), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun s' hs' => ?_
  rw [Function.update_of_ne (Finset.mem_erase.mp hs').1]

private lemma tree_prod_erase_ite {F : Finset (Fin k × Fin k)} (f g : ↥F → ℂ) (e : ↥F) :
    (∏ e' ∈ Finset.univ.erase e, f e') * g e = ∏ e', if e'.1 = e.1 then g e' else f e' := by
  rw [← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ e), ite_eq_left rfl]
  congr 1
  refine Finset.prod_congr rfl fun e' he' => ?_
  have : e'.1 ≠ e.1 := fun h => (Finset.mem_erase.mp he').1 (Subtype.ext h)
  rw [ite_eq_right this]

/-- The derivative of a dressed dissection value: the external inverses give the pair kernels,
each link `β t V_t` gives `β V_t V_t`. -/
private lemma tree_dissVal_hasDerivAt {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {t : ℝ} (ht : |t| < 1) (σ : Fin k → Bool)
    (F : Finset (Fin k × Fin k)) (a : Fin k → Fin L) :
    HasDerivAt (fun r => dissVal β M r σ F a)
      ((∑ s, ∑ c, pairK β M t (σ s) (σ (finRotate k s)) (a s) c *
          dissVal β M t σ F (Function.update a s c)) +
        ∑ d ∈ F, ∑ y, (∏ s, pairV β M t (σ s) (σ (finRotate k s)) (a s) (y s)) *
          tree_coreD β M t σ F d y) t := by
  have hP : ∀ y : Fin k → Fin L,
      HasDerivAt (fun r => ∏ s, pairV β M r (σ s) (σ (finRotate k s)) (a s) (y s))
        (∑ s, (∏ s' ∈ Finset.univ.erase s, pairV β M t (σ s') (σ (finRotate k s')) (a s') (y s'))
          • (pairK β M t (σ s) (σ (finRotate k s)) * pairV β M t (σ s) (σ (finRotate k s)))
            (a s) (y s)) t :=
    fun y => HasDerivAt.fun_finsetProd (fun s _ => tree_pairV_hasDerivAt hD ht _ _ _ _)
  have hQ : ∀ cIn cOut : ↥F → Fin L,
      HasDerivAt (fun r => ∏ e : ↥F,
          ((β * r : ℝ) : ℂ) * pairV β M r (σ e.1.1) (σ e.1.2) (cOut e) (cIn e))
        (∑ e, (∏ e' ∈ Finset.univ.erase e,
            ((β * t : ℝ) : ℂ) * pairV β M t (σ e'.1.1) (σ e'.1.2) (cOut e') (cIn e')) •
          ((β : ℂ) * (pairV β M t (σ e.1.1) (σ e.1.2) * pairV β M t (σ e.1.1) (σ e.1.2))
            (cOut e) (cIn e))) t :=
    fun cIn cOut => HasDerivAt.fun_finsetProd (fun e _ => tree_link_hasDerivAt hD ht _ _ _ _)
  have hC : ∀ y : Fin k → Fin L, HasDerivAt (fun r => dissCore β M r σ F y)
      (∑ cIn : ↥F → Fin L, ∑ cOut : ↥F → Fin L,
        (∑ e, (∏ e' ∈ Finset.univ.erase e,
            ((β * t : ℝ) : ℂ) * pairV β M t (σ e'.1.1) (σ e'.1.2) (cOut e') (cIn e')) •
          ((β : ℂ) * (pairV β M t (σ e.1.1) (σ e.1.2) * pairV β M t (σ e.1.1) (σ e.1.2))
            (cOut e) (cIn e))) *
        ∏ v : Fin k, ∏ p ∈ polyCorners F v,
          sgnMat M (σ v) (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false)) t :=
    fun y => HasDerivAt.fun_sum fun cIn _ => HasDerivAt.fun_sum fun cOut _ =>
      (hQ cIn cOut).mul_const _
  have hV := HasDerivAt.fun_sum (u := Finset.univ) (fun y _ => (hP y).mul (hC y))
  unfold dissVal
  refine hV.congr_deriv ?_
  rw [Finset.sum_add_distrib]
  congr 1
  · simp only [smul_eq_mul, Matrix.mul_apply]
    rw [tree_sum_perm1]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun c _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [tree_prod_update (fun s' x => pairV β M t (σ s') (σ (finRotate k s')) x (y s')) a s c]
  · simp only [smul_eq_mul]
    rw [tree_sum_perm2, ← Finset.sum_coe_sort F]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun y _ => ?_
    unfold tree_coreD
    congr 1
    refine Finset.sum_congr rfl fun cIn _ => Finset.sum_congr rfl fun cOut _ => ?_
    congr 1
    exact tree_prod_erase_ite
      (fun e' => ((β * t : ℝ) : ℂ) * pairV β M t (σ e'.1.1) (σ e'.1.2) (cOut e') (cIn e'))
      (fun e' => (β : ℂ) * (pairV β M t (σ e'.1.1) (σ e'.1.2) * pairV β M t (σ e'.1.1) (σ e'.1.2))
        (cOut e') (cIn e')) e

end Deriv

/-! ## Assembly -/

section Assembly

variable {L : ℕ}

private lemma tree_primF_eq_sum (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (t : ℝ) {n : ℕ}
    (hn : 3 ≤ n) (a : Fin n → Fin L) (σ : Fin n → Bool) :
    primF β M m t a σ = ∑ F ∈ dissections n, dissVal β M t σ F a := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 3 := ⟨n - 3, by omega⟩
  rfl

private lemma tree_primF_two (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (t : ℝ) {n : ℕ}
    (h : n = 2) (a : Fin n → Fin L) (σ : Fin n → Bool) :
    primF β M m t a σ = (β : ℂ)⁻¹ * pairK β M t (σ ⟨0, by omega⟩) (σ ⟨1, by omega⟩)
      (a ⟨0, by omega⟩) (a ⟨1, by omega⟩) := by
  subst h
  rfl

private lemma tree_primF_cast (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (t : ℝ) {n n' : ℕ}
    (h : n = n') (a : Fin n → Fin L) (σ : Fin n → Bool) :
    primF β M m t a σ =
      primF β M m t (fun p : Fin n' => a (Fin.cast h.symm p)) (fun p => σ (Fin.cast h.symm p)) := by
  subst h
  rfl

/-- The adjacent pair starting at the position `s`: `(s, s + 1)`, and `(0, k - 1)` for the last
position. -/
private def tree_adj {n : ℕ} (s : Fin (n + 3)) : Fin (n + 3) × Fin (n + 3) :=
  if h : s.val + 1 < n + 3 then (s, ⟨s.val + 1, h⟩) else (0, Fin.last (n + 2))

/-- The pairs `i < j` are the `k` adjacent pairs and the diagonals. -/
private lemma tree_pairs_split {n : ℕ} (T : Fin (n + 3) → Fin (n + 3) → ℂ) :
    ∑ i : Fin (n + 3), ∑ j : Fin (n + 3), (if i < j then T i j else 0) =
      ∑ s, T (tree_adj s).1 (tree_adj s).2 + ∑ d ∈ polyDiags (n + 3), T d.1 d.2 := by
  rw [← Finset.sum_product' (f := fun i j => if i < j then T i j else 0), ← Finset.sum_filter]
  have hadj : ∀ s : Fin (n + 3), ((tree_adj s).1.val = s.val ∧ (tree_adj s).2.val = s.val + 1 ∧
      s.val + 1 < n + 3) ∨ ((tree_adj s).1.val = 0 ∧ (tree_adj s).2.val = n + 2 ∧
      s.val = n + 2) := by
    intro s
    have := s.isLt
    unfold tree_adj
    split_ifs with h
    · exact Or.inl ⟨rfl, rfl, h⟩
    · exact Or.inr ⟨rfl, rfl, by omega⟩
  have hU : (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin (n + 3) × Fin (n + 3) => p.1 < p.2)
      = Finset.univ.image tree_adj ∪ polyDiags (n + 3) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_image, tree_mem_polyDiags, Fin.lt_def]
    have := i.isLt; have := j.isLt
    constructor
    · intro h
      by_cases h1 : j.val = i.val + 1
      · left
        refine ⟨i, ?_⟩
        have := hadj i
        apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega
      by_cases h2 : i.val = 0 ∧ j.val = n + 2
      · left
        refine ⟨Fin.last (n + 2), ?_⟩
        have := hadj (Fin.last (n + 2))
        simp only [Fin.val_last] at this
        apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega
      · right
        omega
    · rintro (⟨s, hs⟩ | h)
      · have := hadj s
        have e1 := congrArg (fun p => p.1.val) hs
        have e2 := congrArg (fun p => p.2.val) hs
        simp only at e1 e2
        omega
      · omega
  have hdisj : Disjoint (Finset.univ.image tree_adj) (polyDiags (n + 3)) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hp
    rw [tree_mem_polyDiags] at hp'
    have := hadj s
    omega
  have hinj : ∀ s ∈ (Finset.univ : Finset (Fin (n + 3))),
      ∀ s' ∈ (Finset.univ : Finset (Fin (n + 3))), tree_adj s = tree_adj s' → s = s' := by
    intro s _ s' _ h
    have h1 := hadj s
    have h2 := hadj s'
    have e1 := congrArg (fun p => p.1.val) h
    have e2 := congrArg (fun p => p.2.val) h
    apply Fin.ext
    omega
  rw [hU, Finset.sum_union hdisj, Finset.sum_image hinj]

/-- The cut term of the adjacent pair `(s, s + 1)`. -/
private lemma tree_adj_succ {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} (hD : PrimData β M m)
    {t : ℝ} {n : ℕ} (a : Fin (n + 3) → Fin L) (σ : Fin (n + 3) → Bool)
    (s : Fin (n + 3)) (h : s.val + 1 < n + 3) :
    (β : ℂ) * ∑ c : Fin L, primF β M m t (cutLLab a s ⟨s.val + 1, h⟩ c)
        (cutLSgn σ s ⟨s.val + 1, h⟩) *
      primF β M m t (cutRLab a s ⟨s.val + 1, h⟩ c) (cutRSgn σ s ⟨s.val + 1, h⟩) =
    ∑ c : Fin L, pairK β M t (σ s) (σ (finRotate _ s)) (a s) c *
      primF β M m t (Function.update a s c) σ := by
  have hβ : (β : ℂ) ≠ 0 := by exact_mod_cast hD.pos.ne'
  set j : Fin (n + 3) := ⟨s.val + 1, h⟩ with hj
  have hjv : j.val = s.val + 1 := rfl
  have hrot : finRotate (n + 3) s = j := by
    apply Fin.ext
    rw [tree_finRotate_val, ite_eq_right (by omega)]
  have hlenL : n + 3 + s.val - j.val + 1 = n + 3 := by omega
  have hlenR : j.val - s.val + 1 = 2 := by omega
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [tree_primF_cast β M m t hlenL, tree_primF_two β M m t hlenR]
  have hvL : ∀ p : Fin (n + 3), tree_vL s j (Fin.cast hlenL.symm p) = p := by
    intro p
    apply Fin.ext
    rw [tree_vL_val, Fin.val_cast]
    split_ifs <;> omega
  have hwL : (fun p : Fin (n + 3) => cutLLab a s j c (Fin.cast hlenL.symm p)) =
      Function.update a s c := by
    funext p
    rw [tree_cutLLab_eq, hvL, Function.update_apply, Fin.val_cast]
    by_cases hp : p = s
    · rw [ite_eq_left (congrArg Fin.val hp), ite_eq_left hp]
    · rw [ite_eq_right (fun e => hp (Fin.ext e)), ite_eq_right hp]
  have hsL : (fun p : Fin (n + 3) => cutLSgn σ s j (Fin.cast hlenL.symm p)) = σ := by
    funext p
    rw [tree_cutLSgn_eq, hvL]
  have hv0 : tree_vR s j ⟨0, by omega⟩ = s := Fin.ext (by rw [tree_vR_val]; rfl)
  have hv1 : tree_vR s j ⟨1, by omega⟩ = j := Fin.ext (by rw [tree_vR_val])
  rw [hwL, hsL, tree_cutRSgn_eq, tree_cutRSgn_eq, tree_cutRLab_eq, tree_cutRLab_eq, hv0, hv1,
    ite_eq_right (show (0 : ℕ) ≠ j.val - s.val by omega),
    ite_eq_left (show (1 : ℕ) = j.val - s.val by omega), hrot]
  field_simp

/-- The cut term of the cyclic pair `(0, k - 1)`. -/
private lemma tree_adj_last {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} (hD : PrimData β M m)
    {t : ℝ} (ht : |t| < 1) {n : ℕ} (a : Fin (n + 3) → Fin L) (σ : Fin (n + 3) → Bool) :
    (β : ℂ) * ∑ c : Fin L, primF β M m t (cutLLab a 0 (Fin.last (n + 2)) c)
        (cutLSgn σ 0 (Fin.last (n + 2))) *
      primF β M m t (cutRLab a 0 (Fin.last (n + 2)) c) (cutRSgn σ 0 (Fin.last (n + 2))) =
    ∑ c : Fin L, pairK β M t (σ (Fin.last (n + 2))) (σ (finRotate _ (Fin.last (n + 2))))
      (a (Fin.last (n + 2))) c * primF β M m t (Function.update a (Fin.last (n + 2)) c) σ := by
  have hβ : (β : ℂ) ≠ 0 := by exact_mod_cast hD.pos.ne'
  have hlenL : n + 3 + (0 : Fin (n + 3)).val - (Fin.last (n + 2)).val + 1 = 2 := by simp
  have hlenR : (Fin.last (n + 2)).val - (0 : Fin (n + 3)).val + 1 = n + 3 := by simp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [tree_primF_cast β M m t hlenR, tree_primF_two β M m t hlenL]
  have hvR : ∀ q : Fin (n + 3), tree_vR 0 (Fin.last (n + 2)) (Fin.cast hlenR.symm q) = q := by
    intro q
    apply Fin.ext
    rw [tree_vR_val, Fin.val_cast]
    simp
  have hwR : (fun q : Fin (n + 3) => cutRLab a 0 (Fin.last (n + 2)) c (Fin.cast hlenR.symm q)) =
      Function.update a (Fin.last (n + 2)) c := by
    funext q
    rw [tree_cutRLab_eq, hvR, Function.update_apply, Fin.val_cast]
    by_cases hq : q = Fin.last (n + 2)
    · rw [ite_eq_left (by rw [hq]; simp), ite_eq_left hq]
    · have : q.val ≠ n + 2 := fun e => hq (Fin.ext e)
      rw [ite_eq_right (by simpa using this), ite_eq_right hq]
  have hsR : (fun q : Fin (n + 3) => cutRSgn σ 0 (Fin.last (n + 2)) (Fin.cast hlenR.symm q)) =
      σ := by
    funext q
    rw [tree_cutRSgn_eq, hvR]
  have hv0 : tree_vL 0 (Fin.last (n + 2)) ⟨0, by omega⟩ = 0 := Fin.ext (by rw [tree_vL_val]; simp)
  have hv1 : tree_vL 0 (Fin.last (n + 2)) ⟨1, by omega⟩ = Fin.last (n + 2) :=
    Fin.ext (by rw [tree_vL_val]; simp)
  have hrot : finRotate (n + 3) (Fin.last (n + 2)) = 0 := finRotate_last
  rw [hwR, hsR, tree_cutLSgn_eq, tree_cutLSgn_eq, tree_cutLLab_eq, tree_cutLLab_eq, hv0, hv1,
    ite_eq_left (show (0 : ℕ) = (0 : Fin (n + 3)).val by simp),
    ite_eq_right (show (1 : ℕ) ≠ (0 : Fin (n + 3)).val by simp), hrot]
  have hK := congrFun (congrFun (tree_pairK_transpose hD ht (σ (Fin.last (n + 2))) (σ 0)) c)
    (a (Fin.last (n + 2)))
  rw [Matrix.transpose_apply] at hK
  rw [← hK]
  field_simp

/-- The cut term of an adjacent pair: the derivative of the external inverse on one label. -/
private lemma tree_adj_term {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} (hD : PrimData β M m)
    {t : ℝ} (ht : |t| < 1) {n : ℕ} (a : Fin (n + 3) → Fin L) (σ : Fin (n + 3) → Bool)
    (s : Fin (n + 3)) :
    (β : ℂ) * ∑ c : Fin L, primF β M m t (cutLLab a (tree_adj s).1 (tree_adj s).2 c)
        (cutLSgn σ (tree_adj s).1 (tree_adj s).2) *
      primF β M m t (cutRLab a (tree_adj s).1 (tree_adj s).2 c)
        (cutRSgn σ (tree_adj s).1 (tree_adj s).2) =
    ∑ c : Fin L, pairK β M t (σ s) (σ (finRotate _ s)) (a s) c *
      primF β M m t (Function.update a s c) σ := by
  have key : ∀ p : Fin (n + 3) × Fin (n + 3), p = tree_adj s →
      (β : ℂ) * ∑ c : Fin L, primF β M m t (cutLLab a p.1 p.2 c) (cutLSgn σ p.1 p.2) *
        primF β M m t (cutRLab a p.1 p.2 c) (cutRSgn σ p.1 p.2) =
      ∑ c : Fin L, pairK β M t (σ s) (σ (finRotate _ s)) (a s) c *
        primF β M m t (Function.update a s c) σ := by
    intro p hp
    unfold tree_adj at hp
    split_ifs at hp with h
    · subst hp
      exact tree_adj_succ hD a σ s h
    · subst hp
      have hsl : s = Fin.last (n + 2) := Fin.ext (by have := s.isLt; simp; omega)
      subst hsl
      exact tree_adj_last hD ht a σ
  exact key _ rfl

private lemma tree_sum_swap3' {X Y Z : Type*} [Fintype X] (u : Finset Y) (v : Finset Z) (b : ℂ)
    (A : X → Y → ℂ) (B : X → Z → ℂ) :
    b * ∑ x, (∑ y ∈ u, A x y) * (∑ z ∈ v, B x z) = ∑ y ∈ u, ∑ z ∈ v, b * ∑ x, A x y * B x z := by
  calc b * ∑ x, (∑ y ∈ u, A x y) * (∑ z ∈ v, B x z)
      = ∑ x, ∑ y ∈ u, ∑ z ∈ v, b * (A x y * B x z) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ y ∈ u, ∑ x, ∑ z ∈ v, b * (A x y * B x z) := Finset.sum_comm
    _ = ∑ y ∈ u, ∑ z ∈ v, ∑ x, b * (A x y * B x z) :=
        Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ = ∑ y ∈ u, ∑ z ∈ v, b * ∑ x, A x y * B x z := by simp only [Finset.mul_sum]

/-- The cut term of a diagonal: the derivative of its links, summed over the dissections
containing it. -/
private lemma tree_diag_term {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} (hD : PrimData β M m)
    (t : ℝ) {n : ℕ} (σ : Fin (n + 3) → Bool) {d : Fin (n + 3) × Fin (n + 3)}
    (hd : d ∈ polyDiags (n + 3)) (a : Fin (n + 3) → Fin L) :
    ∑ F ∈ (dissections (n + 3)).filter (fun F => d ∈ F), ∑ y : Fin (n + 3) → Fin L,
        (∏ s, pairV β M t (σ s) (σ (finRotate _ s)) (a s) (y s)) * tree_coreD β M t σ F d y =
      (β : ℂ) * ∑ c : Fin L, primF β M m t (cutLLab a d.1 d.2 c) (cutLSgn σ d.1 d.2) *
        primF β M m t (cutRLab a d.1 d.2 c) (cutRSgn σ d.1 d.2) := by
  obtain ⟨i, j⟩ := d
  have hdv := (tree_mem_polyDiags _).mp hd
  simp only at hdv
  have hj := j.isLt
  rw [Finset.sum_congr rfl (fun F hF => tree_key hD t σ hd (Finset.mem_filter.mp hF).1
    (Finset.mem_filter.mp hF).2 a)]
  rw [tree_sum_split hd (fun FL FR => (β : ℂ) * ∑ c : Fin L,
    dissVal β M t (cutLSgn σ i j) FL (cutLLab a i j c) *
      dissVal β M t (cutRSgn σ i j) FR (cutRLab a i j c))]
  simp only [tree_primF_eq_sum β M m t (show 3 ≤ n + 3 + i.val - j.val + 1 by omega),
    tree_primF_eq_sum β M m t (show 3 ≤ j.val - i.val + 1 by omega)]
  rw [tree_sum_swap3']

/-- (5.10) [fo:eq:primitive] for `F_k`, `k ≥ 3`. -/
private lemma tree_primF_hasDerivAt_three {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {t : ℝ} (ht : |t| < 1) {n : ℕ} (a : Fin (n + 3) → Fin L)
    (σ : Fin (n + 3) → Bool) :
    HasDerivAt (fun s => primF β M m s a σ)
      ((β : ℂ) * cutSumFam (fun n b τ => primF β M m t (k := n) b τ) a σ) t := by
  have h := HasDerivAt.fun_sum (u := dissections (n + 3))
    (fun F _ => tree_dissVal_hasDerivAt hD ht σ F a)
  have e : (fun s => primF β M m s a σ) =
      fun s => ∑ F ∈ dissections (n + 3), dissVal β M s σ F a := rfl
  rw [e]
  refine h.congr_deriv ?_
  rw [Finset.sum_add_distrib]
  unfold cutSumFam
  rw [tree_pairs_split, mul_add]
  congr 1
  · rw [Finset.mul_sum]
    simp only [tree_adj_term hD ht a σ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.mul_sum]
    rfl
  · rw [Finset.sum_comm' (t' := polyDiags (n + 3))
      (s' := fun d => (dissections (n + 3)).filter (fun F => d ∈ F))]
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun d hd => tree_diag_term hD t σ hd a
    · intro F d
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hF, hdF⟩
        exact ⟨⟨hF, hdF⟩, ((tree_mem_dissections F).mp hF).1 hdF⟩
      · rintro ⟨⟨hF, hdF⟩, -⟩
        exact ⟨hF, hdF⟩


/-- (5.10) [fo:eq:primitive] for `F_2`: the Riccati equation `∂_t K_t = K_t K_t` of the pair formula
(5.13)
[fo:eq:pairs]. -/
private lemma tree_primF_hasDerivAt_two {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {t : ℝ} (ht : |t| < 1) (a : Fin 2 → Fin L) (σ : Fin 2 → Bool) :
    HasDerivAt (fun s => primF β M m s a σ)
      ((β : ℂ) * cutSumFam (fun n b τ => primF β M m t (k := n) b τ) a σ) t := by
  have hβ : (β : ℂ) ≠ 0 := by exact_mod_cast hD.pos.ne'
  have h := (tree_pairK_hasDerivAt hD ht (σ 0) (σ 1) (a 0) (a 1)).const_mul ((β : ℂ)⁻¹)
  have e : (fun s => primF β M m s a σ) =
      fun s => (β : ℂ)⁻¹ * pairK β M s (σ 0) (σ 1) (a 0) (a 1) := rfl
  rw [e]
  refine h.congr_deriv ?_
  unfold cutSumFam
  have h01 : (0 : Fin 2) < 1 := by decide
  simp only [Fin.sum_univ_two, lt_self_iff_false, ite_false, h01, ite_true,
    show ¬((1 : Fin 2) < 0) by decide, zero_add, add_zero]
  rw [Matrix.mul_apply, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [tree_primF_two β M m t (show 2 + (0 : Fin 2).val - (1 : Fin 2).val + 1 = 2 from rfl),
    tree_primF_two β M m t (show (1 : Fin 2).val - (0 : Fin 2).val + 1 = 2 from rfl)]
  rw [tree_cutLSgn_eq, tree_cutLSgn_eq, tree_cutLLab_eq, tree_cutLLab_eq, tree_cutRSgn_eq,
    tree_cutRSgn_eq, tree_cutRLab_eq, tree_cutRLab_eq]
  have v0 : ∀ h, tree_vL (0 : Fin 2) 1 ⟨0, h⟩ = 0 := fun h => rfl
  have v1 : ∀ h, tree_vL (0 : Fin 2) 1 ⟨1, h⟩ = 1 := fun h => rfl
  have w0 : ∀ h, tree_vR (0 : Fin 2) 1 ⟨0, h⟩ = 0 := fun h => rfl
  have w1 : ∀ h, tree_vR (0 : Fin 2) 1 ⟨1, h⟩ = 1 := fun h => rfl
  simp only [v0, v1, w0, w1, Fin.val_zero, Fin.val_one, ite_true, one_ne_zero, ite_false,
    zero_ne_one, Nat.sub_zero]
  field_simp

end Assembly

/-- The primitive equation (5.10) [fo:eq:primitive] for `F_k`: the cut coefficient is `β`.
The dissection sum (B.1) [ba:eq:dissection] solves it for `|t| < 1`. -/
theorem primF_hasDerivAt {L : ℕ} {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) (t : ℝ) (ht : t ∈ Set.Ioo (-1 : ℝ) 1) {k : ℕ} (hk : 2 ≤ k)
    (a : Fin k → Fin L) (σ : Fin k → Bool) :
    HasDerivAt (fun s => primF β M m s a σ)
      ((β : ℂ) * cutSumFam (fun n b τ => primF β M m t (k := n) b τ) a σ) t := by
  have ht' : |t| < 1 := abs_lt.mpr ht
  rcases k with _ | _ | _ | n
  · omega
  · omega
  · exact tree_primF_hasDerivAt_two hD ht' a σ
  · exact tree_primF_hasDerivAt_three hD ht' a σ

/-- (5.10) [fo:eq:primitive] for the model, with the cut coefficient `γ_g W`. -/
theorem primLoop_hasDerivAt (g : ℝ) (W L : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ L) (E : ℝ) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (t : ℝ) (ht : t ∈ Set.Ioo (-1 : ℝ) 1)
    {k : ℕ} (hk : 2 ≤ k) (a : Fin k → Fin L) (σ : Fin k → Bool) :
    HasDerivAt (fun s => primLoop g W L E m s a σ)
      (((gammaG g * W : ℝ) : ℂ) *
        cutSumFam (fun n b τ => primLoop g W L E m t (k := n) b τ) a σ) t := by
  have hD := primData_of_root g L hL E m hm
  have h := (primF_hasDerivAt hD t ht hk a σ).const_mul ((W : ℂ) ^ (1 - (k : ℤ)))
  have e : (fun s => primLoop g W L E m s a σ) = fun s => (W : ℂ) ^ (1 - (k : ℤ)) *
      primF (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) m s a σ := rfl
  rw [e]
  refine h.congr_deriv ?_
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast (show W ≠ 0 by omega)
  unfold cutSumFam
  simp only [primLoop, primK]
  rw [← mul_assoc, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hi := i.isLt
    have hj := j.isLt
    have hij' : i.val < j.val := hij
    have hexp : (W : ℂ) ^ (1 - (k : ℤ)) =
        (W : ℂ) * ((W : ℂ) ^ (1 - ((k + i.val - j.val + 1 : ℕ) : ℤ)) *
          (W : ℂ) ^ (1 - ((j.val - i.val + 1 : ℕ) : ℤ))) := by
      rw [← zpow_add₀ hW', ← zpow_one_add₀ hW']
      congr 1
      omega
    rw [hexp]
    push_cast
    ring
  · simp

end LSBA
