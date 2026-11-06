import LSBA.Primitive.Molecule
import LSBA.Primitive.Uniform

/-!
# Primitive loops at large coupling

Lemma 5.2(b) [fo:lem:deterministic] at large coupling, the weighted bound, the tail (5.21)
[fo:eq:primitive-tail] in case (b), the free-label bound (B.14) [b:eq:early-free-label], and the
long-pair bound (B.16) [b:eq:primitive-long-pair] on the large-coupling branch of (6.1)
[da:eq:propagation-domain].
-/

open MeasureTheory Real Filter Topology Complex Finset
open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ## The cyclic distance and the diameter of a word -/

section Cyc

variable {L : ℕ}

private lemma lgw_mod {x y : ℕ} (hx : x < L) (hy : y < L) :
    (x + L - y) % L = if y ≤ x then x - y else x + L - y := by
  split_ifs with h
  · have : x + L - y = (x - y) + L := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

private lemma lgw_cd_comm (a b : Fin L) : cycDist a b = cycDist b a := by
  unfold cycDist; exact min_comm _ _

private lemma lgw_cd_self (a : Fin L) : cycDist a a = 0 := by
  simp [cycDist]

private lemma lgw_cd_tri (a b c : Fin L) : cycDist a c ≤ cycDist a b + cycDist b c := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  simp only [cycDist, lgw_mod ha hb, lgw_mod hb ha, lgw_mod ha hc, lgw_mod hc ha,
    lgw_mod hb hc, lgw_mod hc hb]
  split_ifs <;> omega

private lemma lgw_cd_le_diam {k : ℕ} (a : Fin k → Fin L) (p q : Fin k) :
    cycDist (a p) (a q) ≤ wordDiam a :=
  Finset.le_sup (f := fun p : Fin k × Fin k => cycDist (a p.1) (a p.2)) (Finset.mem_univ (p, q))

private lemma lgw_diam_le {k : ℕ} (a : Fin k → Fin L) {N : ℕ}
    (h : ∀ p q, cycDist (a p) (a q) ≤ N) : wordDiam a ≤ N :=
  Finset.sup_le fun p _ => h p.1 p.2

/-- Moving every label by `d_i` moves the diameter by at most `2 Σ d_i`. -/
private lemma lgw_diam_perturb {k : ℕ} (a b : Fin k → Fin L) :
    wordDiam a ≤ wordDiam b + 2 * ∑ i, cycDist (a i) (b i) := by
  refine lgw_diam_le a fun p q => ?_
  have h1 := lgw_cd_tri (a p) (b p) (a q)
  have h2 := lgw_cd_tri (b p) (b q) (a q)
  have h3 := lgw_cd_le_diam b p q
  have h4 : cycDist (a p) (b p) ≤ ∑ i, cycDist (a i) (b i) :=
    Finset.single_le_sum (f := fun i => cycDist (a i) (b i)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ p)
  have h5 : cycDist (a q) (b q) ≤ ∑ i, cycDist (a i) (b i) :=
    Finset.single_le_sum (f := fun i => cycDist (a i) (b i)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ q)
  rw [lgw_cd_comm (b q) (a q)] at h2
  omega

private lemma lgw_wexp_perturb (θ : ℝ) (hθ : 0 ≤ θ) {k : ℕ} (a b : Fin k → Fin L) :
    Real.exp (θ * wordDiam a) ≤
      Real.exp (θ * wordDiam b) * ∏ i, Real.exp (2 * θ * cycDist (a i) (b i)) := by
  rw [← Real.exp_sum, ← Real.exp_add, ← Finset.mul_sum]
  apply Real.exp_le_exp.mpr
  have h : (wordDiam a : ℝ) ≤ wordDiam b + 2 * ∑ i, (cycDist (a i) (b i) : ℝ) := by
    exact_mod_cast lgw_diam_perturb a b
  have : θ * (wordDiam a : ℝ) ≤ θ * (wordDiam b + 2 * ∑ i, (cycDist (a i) (b i) : ℝ)) :=
    mul_le_mul_of_nonneg_left h hθ
  nlinarith

end Cyc

/-! ## The pair matrices of a sign pair

For a pair of signs `(s, s')` the one-label inverse, pair kernel and propagator of Appendix B.2
[sec:bl-primitives] and (5.15) [fo:eq:propagators] are the functions `(1 - tX)⁻¹`, `X(1 - tX)⁻¹` and
`(1 - uX)(1 - tX)⁻¹` of one matrix `X`: `P` for opposite signs, `Q` for `++` and its conjugate
for `--`. -/

section Algebra

open scoped Matrix.Norms.Operator

variable {L : ℕ}

/-- The pair matrix of a sign pair: `P` for opposite signs, `Q` for `++`, its conjugate for
`--`. -/
private def lgw_pairX (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (s s' : Bool) :
    Matrix (Fin L) (Fin L) ℂ :=
  if s = s' then (if s then pairQ β M else (pairQ β M).map star)
  else (pairP β M).map ((↑) : ℝ → ℂ)

/-- Under the primitive data, the rows of `|X|` sum to one. -/
private lemma lgw_pairX_rowsum {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) (s s' : Bool) (a : Fin L) :
    ∑ b, ‖lgw_pairX β M s s' a b‖ = 1 := by
  have hQ : ∀ b, ‖pairQ β M a b‖ = pairP β M a b := by
    intro b
    simp [pairQ, pairP, norm_pow, Complex.norm_real, abs_of_pos hD.pos]
  have hP : ∀ b, ‖((pairP β M a b : ℝ) : ℂ)‖ = pairP β M a b := by
    intro b
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    simp only [pairP, Matrix.of_apply]
    exact mul_nonneg hD.pos.le (sq_nonneg _)
  rw [← hD.row_sum a]
  unfold lgw_pairX
  split_ifs
  · exact Finset.sum_congr rfl fun b _ => hQ b
  · exact Finset.sum_congr rfl fun b _ => by rw [Matrix.map_apply, norm_star, hQ b]
  · exact Finset.sum_congr rfl fun b _ => by rw [Matrix.map_apply, hP b]

/-- The pair matrix is symmetric when `M` is. -/
private lemma lgw_pairX_transpose {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} (hM : Mᵀ = M)
    (s s' : Bool) : (lgw_pairX β M s s')ᵀ = lgw_pairX β M s s' := by
  have h : ∀ a b, M b a = M a b := fun a b => congrFun (congrFun hM a) b
  unfold lgw_pairX
  split_ifs <;> ext a b <;> simp [pairQ, pairP, h a b]

/-- Row sums of `|X|` at most `1` give `‖X‖_{∞→∞} ≤ 1`. -/
private lemma lgw_norm_le {X : Matrix (Fin L) (Fin L) ℂ} (hX : ∀ a, ∑ b, ‖X a b‖ ≤ 1) :
    ‖X‖ ≤ 1 := by
  have h : ‖X‖₊ ≤ 1 := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun a _ => ?_
    rw [← NNReal.coe_le_coe, NNReal.coe_sum, NNReal.coe_one]
    simpa using hX a
  exact_mod_cast h

/-- `1 - tX` is invertible for `‖X‖ ≤ 1` and `|t| < 1`. -/
private lemma lgw_isUnit {X : Matrix (Fin L) (Fin L) ℂ} (hX : ‖X‖ ≤ 1) {t : ℝ} (ht : |t| < 1) :
    IsUnit (1 - (t : ℂ) • X) := by
  have h : ‖(t : ℂ) • X‖ < 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc |t| * ‖X‖ ≤ |t| * 1 := mul_le_mul_of_nonneg_left hX (abs_nonneg t)
      _ < 1 := by rwa [mul_one]
  exact ⟨Units.oneSub _ h, Units.val_oneSub _ _⟩

/-- `1 - tX` is invertible for the pair matrices of the primitive data and `|t| < 1`. -/
private lemma lgw_pairX_isUnit {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {t : ℝ} (ht : |t| < 1) (s s' : Bool) :
    IsUnit (1 - (t : ℂ) • lgw_pairX β M s s') :=
  lgw_isUnit (lgw_norm_le fun a => (lgw_pairX_rowsum hD s s' a).le) ht

/-- The entrywise image of an inverse under a ring hom of fields. -/
private lemma lgw_map_inv {R S : Type*} [Field R] [Field S] (f : R →+* S)
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

private lemma lgw_map_star_eq (A : Matrix (Fin L) (Fin L) ℂ) :
    A.map star = A.map (starRingEnd ℂ) := rfl

/-- The one-label inverse is `(I - tX)⁻¹`. -/
private lemma lgw_pairV_eq (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) (s s' : Bool) :
    pairV β M t s s' = (1 - (t : ℂ) • lgw_pairX β M s s')⁻¹ := by
  unfold pairV lgw_pairX
  split_ifs with h1 h2
  · rfl
  · rw [lgw_map_star_eq, lgw_map_inv]
    congr 1
    ext a b
    simp [Matrix.one_apply]
  · rw [show ((1 - t • pairP β M)⁻¹).map ((↑) : ℝ → ℂ) =
        ((1 - t • pairP β M)⁻¹).map Complex.ofRealHom from rfl, lgw_map_inv]
    congr 1
    ext a b
    simp [Matrix.one_apply]
    split_ifs <;> simp

/-- The pair kernel is `X(I - tX)⁻¹`. -/
private lemma lgw_pairK_eq (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) (s s' : Bool) :
    pairK β M t s s' = lgw_pairX β M s s' * (1 - (t : ℂ) • lgw_pairX β M s s')⁻¹ := by
  have hV := lgw_pairV_eq β M t s s'
  cases s <;> cases s' <;>
    simp only [pairK, pairV, lgw_pairX, Bool.false_eq_true, Bool.true_eq_false, ite_true,
      ite_false, mixedKer] at hV ⊢
  · rw [← hV, lgw_map_star_eq, lgw_map_star_eq, lgw_map_star_eq, Matrix.map_mul]
  · rw [← hV, show ((pairP β M * (1 - t • pairP β M)⁻¹)).map ((↑) : ℝ → ℂ) =
        ((pairP β M * (1 - t • pairP β M)⁻¹)).map Complex.ofRealHom from rfl, Matrix.map_mul]
    rfl
  · rw [← hV, show ((pairP β M * (1 - t • pairP β M)⁻¹)).map ((↑) : ℝ → ℂ) =
        ((pairP β M * (1 - t • pairP β M)⁻¹)).map Complex.ofRealHom from rfl, Matrix.map_mul]
    rfl

/-- The propagator is `(I - uX)(I - tX)⁻¹`. -/
private lemma lgw_pairU_eq (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (u t : ℝ) (s s' : Bool) :
    pairU β M u t s s' = (1 - (u : ℂ) • lgw_pairX β M s s') *
      (1 - (t : ℂ) • lgw_pairX β M s s')⁻¹ := by
  unfold pairU lgw_pairX propPP propPM
  split_ifs with h1 h2
  · rfl
  · rw [lgw_map_star_eq, Matrix.map_mul, lgw_map_inv]
    congr 2
    · ext a b
      simp [Matrix.one_apply]
    · ext a b
      simp [Matrix.one_apply]
  · rw [show ((1 - u • pairP β M) * (1 - t • pairP β M)⁻¹).map ((↑) : ℝ → ℂ) =
        ((1 - u • pairP β M) * (1 - t • pairP β M)⁻¹).map Complex.ofRealHom from rfl,
      Matrix.map_mul, lgw_map_inv]
    congr 2
    · ext a b
      simp [Matrix.one_apply]
      split_ifs <;> simp
    · ext a b
      simp [Matrix.one_apply]
      split_ifs <;> simp

section Generic

variable {X : Matrix (Fin L) (Fin L) ℂ}

private lemma lgw_inv_mul {t : ℝ} (hU : IsUnit (1 - (t : ℂ) • X)) :
    (1 - (t : ℂ) • X)⁻¹ * (1 - (t : ℂ) • X) = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)

private lemma lgw_mul_inv {t : ℝ} (hU : IsUnit (1 - (t : ℂ) • X)) :
    (1 - (t : ℂ) • X) * (1 - (t : ℂ) • X)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)

/-- `X` commutes with `(1 - tX)⁻¹`. -/
private lemma lgw_comm {t : ℝ} (hU : IsUnit (1 - (t : ℂ) • X)) :
    X * (1 - (t : ℂ) • X)⁻¹ = (1 - (t : ℂ) • X)⁻¹ * X := by
  have hc : (1 - (t : ℂ) • X) * X = X * (1 - (t : ℂ) • X) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul]
  set V := (1 - (t : ℂ) • X)⁻¹
  calc X * V = (V * (1 - (t : ℂ) • X)) * X * V := by rw [lgw_inv_mul hU, Matrix.one_mul]
    _ = V * ((1 - (t : ℂ) • X) * X) * V := by simp only [Matrix.mul_assoc]
    _ = V * (X * (1 - (t : ℂ) • X)) * V := by rw [hc]
    _ = V * X * ((1 - (t : ℂ) • X) * V) := by simp only [Matrix.mul_assoc]
    _ = V * X := by rw [lgw_mul_inv hU, Matrix.mul_one]

end Generic

section Rows

variable {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}

/-- The entries of the pair matrices have modulus `β |M_{ab}|²`. -/
private lemma lgw_pairX_norm (hD : PrimData β M m) (s s' : Bool) (a b : Fin L) :
    ‖lgw_pairX β M s s' a b‖ = β * ‖M a b‖ ^ 2 := by
  have hQ : ‖pairQ β M a b‖ = β * ‖M a b‖ ^ 2 := by
    simp [pairQ, norm_pow, Complex.norm_real, abs_of_pos hD.pos]
  unfold lgw_pairX
  split_ifs
  · exact hQ
  · rw [Matrix.map_apply, norm_star, hQ]
  · rw [Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    · simp [pairP]
    · simp only [pairP, Matrix.of_apply]
      exact mul_nonneg hD.pos.le (sq_nonneg _)

/-- The one-label inverse is symmetric. -/
private lemma lgw_V_symm (hD : PrimData β M m) (t : ℝ) (s s' : Bool) :
    (pairV β M t s s')ᵀ = pairV β M t s s' := by
  rw [lgw_pairV_eq, Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.transpose_smul, lgw_pairX_transpose hD.symm]

/-- The pair kernel is symmetric. -/
private lemma lgw_K_symm (hD : PrimData β M m) {t : ℝ} (ht : |t| < 1) (s s' : Bool) :
    (pairK β M t s s')ᵀ = pairK β M t s s' := by
  rw [lgw_pairK_eq, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.transpose_sub,
    Matrix.transpose_one, Matrix.transpose_smul, lgw_pairX_transpose hD.symm,
    lgw_comm (lgw_pairX_isUnit hD ht s s')]

/-- The pair kernel is `X V`, entrywise. -/
private lemma lgw_K_apply (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) (s s' : Bool)
    (a b : Fin L) :
    pairK β M t s s' a b = ∑ c, lgw_pairX β M s s' a c * pairV β M t s s' c b := by
  rw [lgw_pairK_eq, lgw_pairV_eq, Matrix.mul_apply]

/-- `U_{u,t} = I + (t - u) K_t`. -/
private lemma lgw_U_eq' (hD : PrimData β M m) {t : ℝ} (ht : |t| < 1) (u : ℝ) (s s' : Bool) :
    pairU β M u t s s' = 1 + ((t - u : ℝ) : ℂ) • pairK β M t s s' := by
  have hU := lgw_pairX_isUnit hD ht s s'
  have h : (1 - (u : ℂ) • lgw_pairX β M s s') =
      (1 - (t : ℂ) • lgw_pairX β M s s') + ((t - u : ℝ) : ℂ) • lgw_pairX β M s s' := by
    push_cast
    rw [sub_smul]
    abel
  rw [lgw_pairU_eq, h, add_mul, lgw_mul_inv hU, Matrix.smul_mul, lgw_pairK_eq]

/-- The columns of the propagators have the same bound (the propagator is symmetric). -/
private lemma lgw_U_symm (hD : PrimData β M m) {t : ℝ} (ht : |t| < 1) (u : ℝ) (s s' : Bool) :
    (pairU β M u t s s')ᵀ = pairU β M u t s s' := by
  rw [lgw_U_eq' hD ht, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul,
    lgw_K_symm hD ht]

end Rows

end Algebra

/-! ## Propagation of the weighted sup and row bounds through the labels -/

section Propagate

variable {L : ℕ}

/-- The sum over words of a product of one-label factors is the product of the sums. -/
private lemma lgw_sum_prod {n : ℕ} (f : Fin n → Fin L → ℝ) :
    ∑ b : Fin n → Fin L, ∏ i, f i (b i) = ∏ i, ∑ y, f i y := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- Sum over words of a function of the word updated at `j`. -/
private lemma lgw_sum_update {n : ℕ} (j : Fin n) (Θ : (Fin n → Fin L) → ℝ) :
    ∑ b : Fin n → Fin L, ∑ y : Fin L, Θ (Function.update b j y) = L * ∑ b, Θ b := by
  let eqv : ((Fin n → Fin L) × Fin L) ≃ ((Fin n → Fin L) × Fin L) :=
    { toFun := fun p => (Function.update p.1 j p.2, p.1 j)
      invFun := fun p => (Function.update p.1 j p.2, p.1 j)
      left_inv := by intro p; simp
      right_inv := by intro p; simp }
  have h1 : ∑ b : Fin n → Fin L, ∑ y : Fin L, Θ (Function.update b j y) =
      ∑ p : (Fin n → Fin L) × Fin L, Θ (Function.update p.1 j p.2) := by
    rw [Fintype.sum_prod_type]
  have h2 := Equiv.sum_comp eqv (fun q : (Fin n → Fin L) × Fin L => Θ q.1)
  have h3 : ∑ p : (Fin n → Fin L) × Fin L, Θ p.1 = L * ∑ b, Θ b := by
    rw [Fintype.sum_prod_type]
    simp [Finset.sum_const, Finset.mul_sum]
  rw [h1, ← h3, ← h2]
  rfl

/-- Propagation of the weighted sup bound through the one-label factors `U_i`. -/
private lemma lgw_prop_sup (θ : ℝ) (hθ : 0 ≤ θ) {n : ℕ} (U : Fin n → Matrix (Fin L) (Fin L) ℂ)
    {r N : ℝ} (hN : 0 ≤ N)
    (hrow : ∀ i a, ∑ b, Real.exp (2 * θ * cycDist a b) * ‖U i a b‖ ≤ r)
    (G : (Fin n → Fin L) → ℂ) (hG : ∀ b, Real.exp (θ * wordDiam b) * ‖G b‖ ≤ N)
    (a : Fin n → Fin L) :
    Real.exp (θ * wordDiam a) * ‖∑ b, (∏ i, U i (a i) (b i)) * G b‖ ≤ r ^ n * N := by
  set f : Fin n → Fin L → ℝ :=
    fun i y => Real.exp (2 * θ * cycDist (a i) y) * ‖U i (a i) y‖ with hf
  have hf0 : ∀ i y, 0 ≤ f i y := fun i y => by positivity
  have hw0 : 0 ≤ Real.exp (θ * wordDiam a) := (Real.exp_pos _).le
  calc Real.exp (θ * wordDiam a) * ‖∑ b, (∏ i, U i (a i) (b i)) * G b‖
      ≤ Real.exp (θ * wordDiam a) * ∑ b, (∏ i, ‖U i (a i) (b i)‖) * ‖G b‖ := by
        refine mul_le_mul_of_nonneg_left ?_ hw0
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [norm_mul, norm_prod]
    _ = ∑ b, Real.exp (θ * wordDiam a) * ((∏ i, ‖U i (a i) (b i)‖) * ‖G b‖) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ b : Fin n → Fin L, (∏ i, f i (b i)) * N := by
        refine Finset.sum_le_sum fun b _ => ?_
        have h1 := lgw_wexp_perturb θ hθ a b
        have h2 : 0 ≤ (∏ i, ‖U i (a i) (b i)‖) * ‖G b‖ := by positivity
        calc Real.exp (θ * wordDiam a) * ((∏ i, ‖U i (a i) (b i)‖) * ‖G b‖)
            ≤ (Real.exp (θ * wordDiam b) * ∏ i, Real.exp (2 * θ * cycDist (a i) (b i))) *
                ((∏ i, ‖U i (a i) (b i)‖) * ‖G b‖) := mul_le_mul_of_nonneg_right h1 h2
          _ = (∏ i, f i (b i)) * (Real.exp (θ * wordDiam b) * ‖G b‖) := by
              simp only [hf, Finset.prod_mul_distrib]
              ring
          _ ≤ (∏ i, f i (b i)) * N :=
              mul_le_mul_of_nonneg_left (hG b) (Finset.prod_nonneg fun i _ => hf0 i _)
    _ = N * ∏ i, ∑ y, f i y := by
        rw [← Finset.sum_mul, lgw_sum_prod, mul_comm]
    _ ≤ N * r ^ n := by
        refine mul_le_mul_of_nonneg_left ?_ hN
        calc ∏ i, ∑ y, f i y ≤ ∏ _i : Fin n, r :=
              Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun y _ => hf0 i y)
                (fun i _ => hrow i (a i))
          _ = r ^ n := by simp
    _ = r ^ n * N := by ring

/-- Propagation of the weighted row bound at the slot `j` through the one-label factors `U_i`. -/
private lemma lgw_prop_row (θ : ℝ) (hθ : 0 ≤ θ) {n : ℕ} (U : Fin n → Matrix (Fin L) (Fin L) ℂ)
    {r N : ℝ} (hN : 0 ≤ N)
    (hrow : ∀ i a, ∑ b, Real.exp (2 * θ * cycDist a b) * ‖U i a b‖ ≤ r)
    (hcol : ∀ i b, ∑ a, Real.exp (2 * θ * cycDist a b) * ‖U i a b‖ ≤ r)
    (G : (Fin n → Fin L) → ℂ) (j : Fin n)
    (hG : ∀ b, ∑ y, Real.exp (θ * wordDiam (Function.update b j y)) *
      ‖G (Function.update b j y)‖ ≤ N)
    (a : Fin n → Fin L) :
    ∑ x, Real.exp (θ * wordDiam (Function.update a j x)) *
      ‖∑ b, (∏ i, U i ((Function.update a j x) i) (b i)) * G b‖ ≤ r ^ n * N := by
  have hr : 0 ≤ r := (Finset.sum_nonneg fun b _ => by positivity).trans (hrow j (a j))
  have hLpos : (0 : ℝ) < L := by
    have : 0 < L := Nat.pos_of_ne_zero (by rintro rfl; exact (a j).elim0)
    exact_mod_cast this
  set H : (Fin n → Fin L) → ℝ := fun b => Real.exp (θ * wordDiam b) * ‖G b‖ with hH
  have hH0 : ∀ b, 0 ≤ H b := fun b => by positivity
  set f : Fin n → Fin L → ℝ :=
    fun i y => Real.exp (2 * θ * cycDist (a i) y) * ‖U i (a i) y‖ with hf
  have hf0 : ∀ i y, 0 ≤ f i y := fun i y => by positivity
  set Q : (Fin n → Fin L) → ℝ := fun b => ∏ i ∈ Finset.univ.erase j, f i (b i) with hQ
  have hQ0 : ∀ b, 0 ≤ Q b := fun b => Finset.prod_nonneg fun i _ => hf0 i _
  have hQu : ∀ b y, Q (Function.update b j y) = Q b := by
    intro b y
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  -- step 1: each term is bounded by the kernel times `H`
  have step1 : ∀ x, Real.exp (θ * wordDiam (Function.update a j x)) *
      ‖∑ b, (∏ i, U i ((Function.update a j x) i) (b i)) * G b‖ ≤
      ∑ b, (Real.exp (2 * θ * cycDist x (b j)) * ‖U j x (b j)‖) * Q b * H b := by
    intro x
    set a' := Function.update a j x with ha'
    have hw0 : 0 ≤ Real.exp (θ * wordDiam a') := (Real.exp_pos _).le
    calc Real.exp (θ * wordDiam a') * ‖∑ b, (∏ i, U i (a' i) (b i)) * G b‖
        ≤ Real.exp (θ * wordDiam a') * ∑ b, (∏ i, ‖U i (a' i) (b i)‖) * ‖G b‖ := by
          refine mul_le_mul_of_nonneg_left ?_ hw0
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
          rw [norm_mul, norm_prod]
      _ = ∑ b, Real.exp (θ * wordDiam a') * ((∏ i, ‖U i (a' i) (b i)‖) * ‖G b‖) := by
          rw [Finset.mul_sum]
      _ ≤ _ := by
          refine Finset.sum_le_sum fun b _ => ?_
          have h1 := lgw_wexp_perturb θ hθ a' b
          have h2 : 0 ≤ (∏ i, ‖U i (a' i) (b i)‖) * ‖G b‖ := by positivity
          refine (mul_le_mul_of_nonneg_right h1 h2).trans (le_of_eq ?_)
          rw [← Finset.mul_prod_erase Finset.univ (fun i => Real.exp (2 * θ * cycDist (a' i) (b i)))
              (Finset.mem_univ j), ← Finset.mul_prod_erase Finset.univ
              (fun i => ‖U i (a' i) (b i)‖) (Finset.mem_univ j)]
          have hprod : ∀ (g : ℝ → ℝ), ∏ i ∈ Finset.univ.erase j, g (cycDist (a' i) (b i)) =
              ∏ i ∈ Finset.univ.erase j, g (cycDist (a i) (b i)) := by
            intro g
            refine Finset.prod_congr rfl fun i hi => ?_
            rw [ha', Function.update_of_ne (Finset.ne_of_mem_erase hi)]
          have hprod2 : ∏ i ∈ Finset.univ.erase j, ‖U i (a' i) (b i)‖ =
              ∏ i ∈ Finset.univ.erase j, ‖U i (a i) (b i)‖ := by
            refine Finset.prod_congr rfl fun i hi => ?_
            rw [ha', Function.update_of_ne (Finset.ne_of_mem_erase hi)]
          have hprod3 : ∏ i ∈ Finset.univ.erase j,
              Real.exp (2 * θ * cycDist (a' i) (b i)) =
              ∏ i ∈ Finset.univ.erase j, Real.exp (2 * θ * cycDist (a i) (b i)) := by
            refine Finset.prod_congr rfl fun i hi => ?_
            rw [ha', Function.update_of_ne (Finset.ne_of_mem_erase hi)]
          have hjj : a' j = x := by rw [ha']; simp
          have hQe : Q b = ∏ i ∈ Finset.univ.erase j, (Real.exp (2 * θ * cycDist (a i) (b i)) *
              ‖U i (a i) (b i)‖) := rfl
          rw [hprod2, hprod3, hjj, hQe, Finset.prod_mul_distrib]
          simp only [hH]
          ring
  -- step 2: sum over `x` of the kernel in the slot `j`
  calc ∑ x, Real.exp (θ * wordDiam (Function.update a j x)) *
        ‖∑ b, (∏ i, U i ((Function.update a j x) i) (b i)) * G b‖
      ≤ ∑ x, ∑ b, (Real.exp (2 * θ * cycDist x (b j)) * ‖U j x (b j)‖) * Q b * H b :=
        Finset.sum_le_sum fun x _ => step1 x
    _ = ∑ b, (∑ x, Real.exp (2 * θ * cycDist x (b j)) * ‖U j x (b j)‖) * (Q b * H b) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    _ ≤ ∑ b, r * (Q b * H b) := by
        refine Finset.sum_le_sum fun b _ => ?_
        exact mul_le_mul_of_nonneg_right (hcol j (b j)) (mul_nonneg (hQ0 b) (hH0 b))
    _ = r * ∑ b, Q b * H b := by rw [Finset.mul_sum]
    _ ≤ r * (N * r ^ (n - 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ hr
        -- the `L`-trick
        have hA : (L : ℝ) * ∑ b, Q b * H b = ∑ b, Q b * ∑ y, H (Function.update b j y) := by
          rw [← lgw_sum_update j (fun b => Q b * H b)]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [hQu]
        have hB : ∑ b, Q b * ∑ y, H (Function.update b j y) ≤ ∑ b, Q b * N :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hG b) (hQ0 b)
        set g : Fin n → Fin L → ℝ := fun i y => if i = j then 1 else f i y with hg
        have hQg : ∀ b, Q b = ∏ i, g i (b i) := by
          intro b
          rw [← Finset.mul_prod_erase Finset.univ (fun i => g i (b i)) (Finset.mem_univ j)]
          simp only [hg, ite_true, one_mul]
          refine Finset.prod_congr rfl fun i hi => ?_
          simp [Finset.ne_of_mem_erase hi]
        have hC : ∑ b, Q b = L * ∏ i ∈ Finset.univ.erase j, ∑ y, f i y := by
          simp only [hQg]
          rw [lgw_sum_prod, ← Finset.mul_prod_erase Finset.univ (fun i => ∑ y, g i y)
            (Finset.mem_univ j)]
          simp only [hg, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, mul_one]
          congr 1
          refine Finset.prod_congr rfl fun i hi => ?_
          simp [Finset.ne_of_mem_erase hi]
        have hD : ∏ i ∈ Finset.univ.erase j, ∑ y, f i y ≤ r ^ (n - 1) := by
          calc ∏ i ∈ Finset.univ.erase j, ∑ y, f i y ≤ ∏ _i ∈ Finset.univ.erase j, r :=
                Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun y _ => hf0 i y)
                  (fun i _ => hrow i (a i))
            _ = r ^ (n - 1) := by
                rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j)]
                simp
        have hE : (L : ℝ) * ∑ b, Q b * H b ≤ L * (N * r ^ (n - 1)) := by
          rw [hA]
          refine hB.trans ?_
          rw [← Finset.sum_mul, hC]
          calc ((L : ℝ) * ∏ i ∈ Finset.univ.erase j, ∑ y, f i y) * N
              = N * (L * ∏ i ∈ Finset.univ.erase j, ∑ y, f i y) := by ring
            _ ≤ N * (L * r ^ (n - 1)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD hLpos.le) hN
            _ = L * (N * r ^ (n - 1)) := by ring
        exact le_of_mul_le_mul_left hE hLpos
    _ = r ^ n * N := by
        have hn : n = (n - 1) + 1 := by
          have : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact j.elim0)
          omega
        conv_rhs => rw [hn, pow_succ]
        ring

end Propagate

/-! ## The cut words -/

section CutWords

variable {L : ℕ}

/-- The label `c` sits at the position `i` of the left cut word. -/
private lemma lgw_cutL_c {k : ℕ} (b : Fin k → Fin L) (i j : Fin k) (c c₀ : Fin L) :
    cutLLab b i j c = Function.update (cutLLab b i j c₀)
      ⟨i.val, by have := j.2; omega⟩ c := by
  funext p
  simp only [cutLLab, Function.update_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- The label `c` sits at the last position of the right cut word. -/
private lemma lgw_cutR_c {k : ℕ} (b : Fin k → Fin L) (i j : Fin k) (c c₀ : Fin L) :
    cutRLab b i j c = Function.update (cutRLab b i j c₀) (Fin.last (j.val - i.val)) c := by
  funext p
  simp only [cutRLab, Function.update_apply, Fin.ext_iff, Fin.val_last]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- A label of `b` to the left of `i` is a label of the left cut word. -/
private lemma lgw_cut_update_lt {k : ℕ} (b : Fin k → Fin L) (i j j₀ : Fin k)
    (hij : i.val < j.val) (hj₀ : j₀.val < i.val) (x c : Fin L) :
    cutLLab (Function.update b j₀ x) i j c =
      Function.update (cutLLab b i j c) ⟨j₀.val, by have := j.2; omega⟩ x ∧
    cutRLab (Function.update b j₀ x) i j c = cutRLab b i j c := by
  refine ⟨?_, ?_⟩
  · funext p
    simp only [cutLLab, Function.update_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  · funext p
    simp only [cutRLab, Function.update_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)

/-- A label of `b` between `i` and `j` is a label of the right cut word. -/
private lemma lgw_cut_update_mid {k : ℕ} (b : Fin k → Fin L) (i j j₀ : Fin k)
    (h1 : i.val ≤ j₀.val) (h2 : j₀.val < j.val) (x c : Fin L) :
    cutRLab (Function.update b j₀ x) i j c =
      Function.update (cutRLab b i j c) ⟨j₀.val - i.val, by omega⟩ x ∧
    cutLLab (Function.update b j₀ x) i j c = cutLLab b i j c := by
  refine ⟨?_, ?_⟩
  · funext p
    simp only [cutRLab, Function.update_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  · funext p
    simp only [cutLLab, Function.update_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)

/-- A label of `b` from `j` on is a label of the left cut word. -/
private lemma lgw_cut_update_ge {k : ℕ} (b : Fin k → Fin L) (i j j₀ : Fin k)
    (hij : i.val < j.val) (h1 : j.val ≤ j₀.val) (x c : Fin L) :
    cutLLab (Function.update b j₀ x) i j c =
      Function.update (cutLLab b i j c) ⟨j₀.val + i.val + 1 - j.val, by have := j₀.2; omega⟩ x ∧
    cutRLab (Function.update b j₀ x) i j c = cutRLab b i j c := by
  refine ⟨?_, ?_⟩
  · funext p
    simp only [cutLLab, Function.update_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  · funext p
    simp only [cutRLab, Function.update_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)

/-- The diameter of a word is at most the sum of the diameters of its two cut words (the label
`c` is in both). -/
private lemma lgw_diam_cut {k : ℕ} (b : Fin k → Fin L) (i j : Fin k) (hij : i.val < j.val)
    (c : Fin L) : wordDiam b ≤ wordDiam (cutLLab b i j c) + wordDiam (cutRLab b i j c) := by
  have hLm : ∀ p : Fin k, (p.val < i.val ∨ j.val ≤ p.val) → ∃ r, cutLLab b i j c r = b p := by
    intro p hp
    rcases hp with hp | hp
    · refine ⟨⟨p.val, by have := j.2; omega⟩, ?_⟩
      simp [cutLLab, hp]
    · refine ⟨⟨p.val + i.val + 1 - j.val, by have := p.2; omega⟩, ?_⟩
      simp only [cutLLab]
      split_ifs with h1 h2
      · exfalso; omega
      · exfalso; omega
      · congr 1; ext; simp only; omega
  have hRm : ∀ p : Fin k, i.val ≤ p.val → p.val < j.val → ∃ r, cutRLab b i j c r = b p := by
    intro p h1 h2
    refine ⟨⟨p.val - i.val, by omega⟩, ?_⟩
    simp only [cutRLab]
    split_ifs with h3
    · congr 1; ext; simp only; omega
    · exfalso; omega
  have hLc : ∃ r, cutLLab b i j c r = c :=
    ⟨⟨i.val, by have := j.2; omega⟩, by simp [cutLLab]⟩
  have hRc : ∃ r, cutRLab b i j c r = c := ⟨Fin.last _, by simp [cutRLab]⟩
  have hmem : ∀ p : Fin k, (∃ r, cutLLab b i j c r = b p) ∨ (∃ r, cutRLab b i j c r = b p) := by
    intro p
    by_cases h : i.val ≤ p.val ∧ p.val < j.val
    · exact Or.inr (hRm p h.1 h.2)
    · exact Or.inl (hLm p (by omega))
  obtain ⟨rLc, hrLc⟩ := hLc
  obtain ⟨rRc, hrRc⟩ := hRc
  refine lgw_diam_le b fun p q => ?_
  rcases hmem p with ⟨rp, hrp⟩ | ⟨rp, hrp⟩ <;> rcases hmem q with ⟨rq, hrq⟩ | ⟨rq, hrq⟩
  · have := lgw_cd_le_diam (cutLLab b i j c) rp rq
    rw [hrp, hrq] at this
    omega
  · have h1 := lgw_cd_le_diam (cutLLab b i j c) rp rLc
    have h2 := lgw_cd_le_diam (cutRLab b i j c) rRc rq
    rw [hrp, hrLc] at h1
    rw [hrRc, hrq] at h2
    have := lgw_cd_tri (b p) c (b q)
    omega
  · have h1 := lgw_cd_le_diam (cutRLab b i j c) rp rRc
    have h2 := lgw_cd_le_diam (cutLLab b i j c) rLc rq
    rw [hrp, hrRc] at h1
    rw [hrLc, hrq] at h2
    have := lgw_cd_tri (b p) c (b q)
    omega
  · have := lgw_cd_le_diam (cutRLab b i j c) rp rq
    rw [hrp, hrq] at this
    omega

end CutWords

/-! ## The induction on the length -/

section Induct

variable {L : ℕ}

/-- The weighted sup bound and the weighted row bound of `F_n` up to the time `T`, with the
profile `(1 - t)^{-(2n-3)}` of (7.20) [uvc:eq:primitive-coarse-row]. -/
private def lgw_Bd (θ β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (T : ℝ) (n : ℕ)
    (A : ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t ≤ T →
    (∀ (a : Fin n → Fin L) (σ : Fin n → Bool),
      Real.exp (θ * wordDiam a) * ‖primF β M m t a σ‖ ≤ A * ((1 - t) ^ (2 * n - 3))⁻¹) ∧
    (∀ (j : Fin n) (a : Fin n → Fin L) (σ : Fin n → Bool),
      β * ∑ c : Fin L, Real.exp (θ * wordDiam (Function.update a j c)) *
        ‖primF β M m t (Function.update a j c) σ‖ ≤ A * ((1 - t) ^ (2 * n - 3))⁻¹)

/-- The diagonal source of the Duhamel formula (5.16) [fo:eq:duhamel]. -/
private def lgw_src (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (n : ℕ) (u : ℝ)
    (σ : Fin n → Bool) (b : Fin n → Fin L) : ℂ :=
  ∑ d ∈ polyDiags n, ∑ c : Fin L,
    primF β M m u (cutLLab b d.1 d.2 c) (cutLSgn σ d.1 d.2) *
      primF β M m u (cutRLab b d.1 d.2 c) (cutRSgn σ d.1 d.2)

/-- The children of a diagonal have lengths in `[2, n - 1]` (in fact `[3, n - 1]`). -/
private lemma lgw_diag_len {n : ℕ} {d : Fin n × Fin n} (hd : d ∈ polyDiags n) :
    2 ≤ n + d.1.val - d.2.val + 1 ∧ n + d.1.val - d.2.val + 1 < n ∧
      2 ≤ d.2.val - d.1.val + 1 ∧ d.2.val - d.1.val + 1 < n ∧ d.1.val < d.2.val := by
  have hd' : IsPolyDiag n d := (Finset.mem_filter.mp hd).2
  obtain ⟨h1, h2⟩ := hd'
  have := d.2.2
  have := d.1.2
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- Sup bound for one diagonal term of the source. -/
private lemma lgw_term_sup {θ β : ℝ} (hθ : 0 ≤ θ) (hβ : 0 < β) {M : Matrix (Fin L) (Fin L) ℂ}
    {m : ℂ} {T A : ℝ} {n : ℕ}
    (hIH : ∀ n', 2 ≤ n' → n' < n → lgw_Bd θ β M m T n' A) {u : ℝ} (hu : 0 ≤ u) (huT : u ≤ T)
    (σ : Fin n → Bool) (b : Fin n → Fin L) {d : Fin n × Fin n} (hd : d ∈ polyDiags n) :
    β * (Real.exp (θ * wordDiam b) * ‖∑ c : Fin L,
      primF β M m u (cutLLab b d.1 d.2 c) (cutLSgn σ d.1 d.2) *
        primF β M m u (cutRLab b d.1 d.2 c) (cutRSgn σ d.1 d.2)‖) ≤
      A ^ 2 * ((1 - u) ^ (2 * n - 2))⁻¹ := by
  obtain ⟨hL1, hL2, hR1, hR2, hij⟩ := lgw_diag_len hd
  obtain ⟨hLs, -⟩ := hIH _ hL1 hL2 u hu huT
  obtain ⟨-, hRr⟩ := hIH _ hR1 hR2 u hu huT
  have hexp : 2 * (n + d.1.val - d.2.val + 1) - 3 + (2 * (d.2.val - d.1.val + 1) - 3) =
      2 * n - 2 := by omega
  set i := d.1 with hi
  set j := d.2 with hj
  set c₀ : Fin L := b i with hc₀
  have hrowR : β * ∑ c : Fin L, Real.exp (θ * wordDiam (cutRLab b i j c)) *
      ‖primF β M m u (cutRLab b i j c) (cutRSgn σ i j)‖ ≤
        A * ((1 - u) ^ (2 * (j.val - i.val + 1) - 3))⁻¹ := by
    have := hRr (Fin.last (j.val - i.val)) (cutRLab b i j c₀) (cutRSgn σ i j)
    simpa only [← lgw_cutR_c b i j _ c₀] using this
  have hpow : ((1 - u) ^ (2 * (n + i.val - j.val + 1) - 3))⁻¹ *
      ((1 - u) ^ (2 * (j.val - i.val + 1) - 3))⁻¹ = ((1 - u) ^ (2 * n - 2))⁻¹ := by
    rw [← mul_inv, ← pow_add, hexp]
  have hwF : ∀ c, 0 ≤ Real.exp (θ * wordDiam (cutRLab b i j c)) *
      ‖primF β M m u (cutRLab b i j c) (cutRSgn σ i j)‖ := fun c => by positivity
  calc β * (Real.exp (θ * wordDiam b) * ‖∑ c : Fin L,
        primF β M m u (cutLLab b i j c) (cutLSgn σ i j) *
          primF β M m u (cutRLab b i j c) (cutRSgn σ i j)‖)
      ≤ β * (Real.exp (θ * wordDiam b) * ∑ c : Fin L,
        ‖primF β M m u (cutLLab b i j c) (cutLSgn σ i j)‖ *
          ‖primF β M m u (cutRLab b i j c) (cutRSgn σ i j)‖) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
          hβ.le
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => by rw [norm_mul])
    _ ≤ β * ∑ c : Fin L, (Real.exp (θ * wordDiam (cutLLab b i j c)) *
        ‖primF β M m u (cutLLab b i j c) (cutLSgn σ i j)‖) *
          (Real.exp (θ * wordDiam (cutRLab b i j c)) *
        ‖primF β M m u (cutRLab b i j c) (cutRSgn σ i j)‖) := by
        refine mul_le_mul_of_nonneg_left ?_ hβ.le
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun c _ => ?_
        have h1 : Real.exp (θ * wordDiam b) ≤ Real.exp (θ * wordDiam (cutLLab b i j c)) *
            Real.exp (θ * wordDiam (cutRLab b i j c)) := by
          rw [← Real.exp_add, ← mul_add]
          apply Real.exp_le_exp.mpr
          have := lgw_diam_cut b i j hij c
          have h' : (wordDiam b : ℝ) ≤ wordDiam (cutLLab b i j c) + wordDiam (cutRLab b i j c) := by
            exact_mod_cast this
          exact mul_le_mul_of_nonneg_left h' hθ
        have h2 : 0 ≤ ‖primF β M m u (cutLLab b i j c) (cutLSgn σ i j)‖ *
          ‖primF β M m u (cutRLab b i j c) (cutRSgn σ i j)‖ := by positivity
        calc Real.exp (θ * wordDiam b) * (‖primF β M m u (cutLLab b i j c) (cutLSgn σ i j)‖ *
              ‖primF β M m u (cutRLab b i j c) (cutRSgn σ i j)‖)
            ≤ (Real.exp (θ * wordDiam (cutLLab b i j c)) *
                Real.exp (θ * wordDiam (cutRLab b i j c))) *
                (‖primF β M m u (cutLLab b i j c) (cutLSgn σ i j)‖ *
              ‖primF β M m u (cutRLab b i j c) (cutRSgn σ i j)‖) :=
              mul_le_mul_of_nonneg_right h1 h2
          _ = _ := by ring
    _ ≤ β * ∑ c : Fin L, (A * ((1 - u) ^ (2 * (n + i.val - j.val + 1) - 3))⁻¹) *
          (Real.exp (θ * wordDiam (cutRLab b i j c)) *
        ‖primF β M m u (cutRLab b i j c) (cutRSgn σ i j)‖) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => ?_) hβ.le
        exact mul_le_mul_of_nonneg_right (hLs _ _) (hwF c)
    _ = (A * ((1 - u) ^ (2 * (n + i.val - j.val + 1) - 3))⁻¹) *
        (β * ∑ c : Fin L, Real.exp (θ * wordDiam (cutRLab b i j c)) *
        ‖primF β M m u (cutRLab b i j c) (cutRSgn σ i j)‖) := by
        rw [← Finset.mul_sum]
        ring
    _ ≤ (A * ((1 - u) ^ (2 * (n + i.val - j.val + 1) - 3))⁻¹) *
        (A * ((1 - u) ^ (2 * (j.val - i.val + 1) - 3))⁻¹) := by
        refine mul_le_mul_of_nonneg_left hrowR ?_
        refine le_trans ?_ (hLs (cutLLab b i j c₀) (cutLSgn σ i j))
        positivity
    _ = A ^ 2 * ((1 - u) ^ (2 * n - 2))⁻¹ := by
        rw [← hpow]
        ring

/-- Sup bound for the whole diagonal source. -/
private lemma lgw_src_sup {θ β : ℝ} (hθ : 0 ≤ θ) (hβ : 0 < β) {M : Matrix (Fin L) (Fin L) ℂ}
    {m : ℂ} {T A : ℝ} {n : ℕ}
    (hIH : ∀ n', 2 ≤ n' → n' < n → lgw_Bd θ β M m T n' A) {u : ℝ} (hu : 0 ≤ u) (huT : u ≤ T)
    (σ : Fin n → Bool) (b : Fin n → Fin L) :
    β * (Real.exp (θ * wordDiam b) * ‖lgw_src β M m n u σ b‖) ≤
      ((polyDiags n).card : ℝ) * (A ^ 2 * ((1 - u) ^ (2 * n - 2))⁻¹) := by
  calc β * (Real.exp (θ * wordDiam b) * ‖lgw_src β M m n u σ b‖)
      ≤ β * (Real.exp (θ * wordDiam b) * ∑ d ∈ polyDiags n, ‖∑ c : Fin L,
        primF β M m u (cutLLab b d.1 d.2 c) (cutLSgn σ d.1 d.2) *
          primF β M m u (cutRLab b d.1 d.2 c) (cutRSgn σ d.1 d.2)‖) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
          hβ.le
        exact norm_sum_le _ _
    _ = ∑ d ∈ polyDiags n, β * (Real.exp (θ * wordDiam b) * ‖∑ c : Fin L,
        primF β M m u (cutLLab b d.1 d.2 c) (cutLSgn σ d.1 d.2) *
          primF β M m u (cutRLab b d.1 d.2 c) (cutRSgn σ d.1 d.2)‖) := by
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ ∑ _d ∈ polyDiags n, (A ^ 2 * ((1 - u) ^ (2 * n - 2))⁻¹) :=
        Finset.sum_le_sum fun d hd => lgw_term_sup hθ hβ hIH hu huT σ b hd
    _ = ((polyDiags n).card : ℝ) * (A ^ 2 * ((1 - u) ^ (2 * n - 2))⁻¹) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- Pointwise: the weight times the modulus of a diagonal term is at most the sum of the products
of the weighted moduli of the two cut loops. -/
private lemma lgw_term_pw {θ β : ℝ} (hθ : 0 ≤ θ) {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} {n : ℕ}
    (u : ℝ) (σ : Fin n → Bool) (b : Fin n → Fin L) {d : Fin n × Fin n} (hd : d ∈ polyDiags n) :
    Real.exp (θ * wordDiam b) * ‖∑ c : Fin L,
      primF β M m u (cutLLab b d.1 d.2 c) (cutLSgn σ d.1 d.2) *
        primF β M m u (cutRLab b d.1 d.2 c) (cutRSgn σ d.1 d.2)‖ ≤
      ∑ c : Fin L, (Real.exp (θ * wordDiam (cutLLab b d.1 d.2 c)) *
        ‖primF β M m u (cutLLab b d.1 d.2 c) (cutLSgn σ d.1 d.2)‖) *
          (Real.exp (θ * wordDiam (cutRLab b d.1 d.2 c)) *
        ‖primF β M m u (cutRLab b d.1 d.2 c) (cutRSgn σ d.1 d.2)‖) := by
  obtain ⟨-, -, -, -, hij⟩ := lgw_diag_len hd
  calc Real.exp (θ * wordDiam b) * ‖∑ c : Fin L,
      primF β M m u (cutLLab b d.1 d.2 c) (cutLSgn σ d.1 d.2) *
        primF β M m u (cutRLab b d.1 d.2 c) (cutRSgn σ d.1 d.2)‖
      ≤ Real.exp (θ * wordDiam b) * ∑ c : Fin L,
        ‖primF β M m u (cutLLab b d.1 d.2 c) (cutLSgn σ d.1 d.2)‖ *
          ‖primF β M m u (cutRLab b d.1 d.2 c) (cutRSgn σ d.1 d.2)‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => by rw [norm_mul])
    _ ≤ _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun c _ => ?_
        have h1 : Real.exp (θ * wordDiam b) ≤ Real.exp (θ * wordDiam (cutLLab b d.1 d.2 c)) *
            Real.exp (θ * wordDiam (cutRLab b d.1 d.2 c)) := by
          rw [← Real.exp_add, ← mul_add]
          apply Real.exp_le_exp.mpr
          have := lgw_diam_cut b d.1 d.2 hij c
          have h' : (wordDiam b : ℝ) ≤ wordDiam (cutLLab b d.1 d.2 c) +
              wordDiam (cutRLab b d.1 d.2 c) := by exact_mod_cast this
          exact mul_le_mul_of_nonneg_left h' hθ
        have h2 : 0 ≤ ‖primF β M m u (cutLLab b d.1 d.2 c) (cutLSgn σ d.1 d.2)‖ *
          ‖primF β M m u (cutRLab b d.1 d.2 c) (cutRSgn σ d.1 d.2)‖ := by positivity
        calc Real.exp (θ * wordDiam b) *
              (‖primF β M m u (cutLLab b d.1 d.2 c) (cutLSgn σ d.1 d.2)‖ *
              ‖primF β M m u (cutRLab b d.1 d.2 c) (cutRSgn σ d.1 d.2)‖)
            ≤ (Real.exp (θ * wordDiam (cutLLab b d.1 d.2 c)) *
                Real.exp (θ * wordDiam (cutRLab b d.1 d.2 c))) *
                (‖primF β M m u (cutLLab b d.1 d.2 c) (cutLSgn σ d.1 d.2)‖ *
              ‖primF β M m u (cutRLab b d.1 d.2 c) (cutRSgn σ d.1 d.2)‖) :=
              mul_le_mul_of_nonneg_right h1 h2
          _ = _ := by ring

/-- Combination of a row bound in one variable with a row bound in the other. -/
private lemma lgw_comb {X : Type*} [Fintype X] {β AL AR : ℝ} (hβ : 0 < β) (hAL : 0 ≤ AL)
    (f : X → Fin L → ℝ) (g : Fin L → ℝ) (hg : ∀ c, 0 ≤ g c)
    (hfL : ∀ c, β * ∑ x, f x c ≤ AL) (hgR : β * ∑ c, g c ≤ AR) :
    β ^ 2 * ∑ x, ∑ c, f x c * g c ≤ AL * AR := by
  calc β ^ 2 * ∑ x, ∑ c, f x c * g c = ∑ c, (β * g c) * (β * ∑ x, f x c) := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [← Finset.sum_mul, Finset.mul_sum]
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    _ ≤ ∑ c, (β * g c) * AL :=
        Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hfL c)
          (mul_nonneg hβ.le (hg c))
    _ = AL * (β * ∑ c, g c) := by rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
    _ ≤ AL * AR := mul_le_mul_of_nonneg_left hgR hAL

/-- Row bound for one diagonal term of the source, at the label `j₀` of the word. -/
private lemma lgw_term_row {θ β : ℝ} (hθ : 0 ≤ θ) (hβ : 0 < β)
    {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} {T A : ℝ} {n : ℕ}
    (hIH : ∀ n', 2 ≤ n' → n' < n → lgw_Bd θ β M m T n' A) {u : ℝ} (hu : 0 ≤ u) (huT : u ≤ T)
    (σ : Fin n → Bool) (b : Fin n → Fin L) (j₀ : Fin n) {d : Fin n × Fin n}
    (hd : d ∈ polyDiags n) :
    β ^ 2 * ∑ x : Fin L, Real.exp (θ * wordDiam (Function.update b j₀ x)) *
      ‖∑ c : Fin L, primF β M m u (cutLLab (Function.update b j₀ x) d.1 d.2 c)
          (cutLSgn σ d.1 d.2) *
        primF β M m u (cutRLab (Function.update b j₀ x) d.1 d.2 c) (cutRSgn σ d.1 d.2)‖ ≤
      A ^ 2 * ((1 - u) ^ (2 * n - 2))⁻¹ := by
  obtain ⟨hL1, hL2, hR1, hR2, hij⟩ := lgw_diag_len hd
  obtain ⟨-, hLr⟩ := hIH _ hL1 hL2 u hu huT
  obtain ⟨-, hRr⟩ := hIH _ hR1 hR2 u hu huT
  have hexp : 2 * (n + d.1.val - d.2.val + 1) - 3 + (2 * (d.2.val - d.1.val + 1) - 3) =
      2 * n - 2 := by omega
  set i := d.1 with hi
  set j := d.2 with hj
  set c₀ : Fin L := b i with hc₀
  set L₀ := cutLLab b i j c₀ with hL₀
  set R₀ := cutRLab b i j c₀ with hR₀
  set τL := cutLSgn σ i j with hτL
  set τR := cutRSgn σ i j with hτR
  have hpow : ((1 - u) ^ (2 * (n + i.val - j.val + 1) - 3))⁻¹ *
      ((1 - u) ^ (2 * (j.val - i.val + 1) - 3))⁻¹ = ((1 - u) ^ (2 * n - 2))⁻¹ := by
    rw [← mul_inv, ← pow_add, hexp]
  have hAL : 0 ≤ A * ((1 - u) ^ (2 * (n + i.val - j.val + 1) - 3))⁻¹ := by
    refine le_trans ?_ ((hLr ⟨i.val, by have := j.2; omega⟩ L₀ τL))
    have := hβ
    positivity
  have hAR : 0 ≤ A * ((1 - u) ^ (2 * (j.val - i.val + 1) - 3))⁻¹ := by
    refine le_trans ?_ ((hRr (Fin.last _) R₀ τR))
    have := hβ
    positivity
  have hfin : A ^ 2 * ((1 - u) ^ (2 * n - 2))⁻¹ =
      (A * ((1 - u) ^ (2 * (n + i.val - j.val + 1) - 3))⁻¹) *
        (A * ((1 - u) ^ (2 * (j.val - i.val + 1) - 3))⁻¹) := by
    rw [← hpow]; ring
  have hstep : ∀ x : Fin L, Real.exp (θ * wordDiam (Function.update b j₀ x)) *
      ‖∑ c : Fin L, primF β M m u (cutLLab (Function.update b j₀ x) i j c) τL *
        primF β M m u (cutRLab (Function.update b j₀ x) i j c) τR‖ ≤
      ∑ c : Fin L, (Real.exp (θ * wordDiam (cutLLab (Function.update b j₀ x) i j c)) *
        ‖primF β M m u (cutLLab (Function.update b j₀ x) i j c) τL‖) *
          (Real.exp (θ * wordDiam (cutRLab (Function.update b j₀ x) i j c)) *
        ‖primF β M m u (cutRLab (Function.update b j₀ x) i j c) τR‖) :=
    fun x => lgw_term_pw hθ u σ (Function.update b j₀ x) hd
  have hwL : ∀ a : Fin (n + i.val - j.val + 1) → Fin L, 0 ≤ Real.exp (θ * wordDiam a) *
      ‖primF β M m u a τL‖ := fun a => by positivity
  have hwR : ∀ a : Fin (j.val - i.val + 1) → Fin L, 0 ≤ Real.exp (θ * wordDiam a) *
      ‖primF β M m u a τR‖ := fun a => by positivity
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hstep x)
    (by positivity)) ?_
  rw [hfin]
  by_cases h1 : j₀.val < i.val
  · -- the label is in the left cut word, before `i`
    have hLw : ∀ x c, cutLLab (Function.update b j₀ x) i j c =
        Function.update (Function.update L₀ ⟨i.val, by have := j.2; omega⟩ c)
          ⟨j₀.val, by have := j.2; omega⟩ x := by
      intro x c
      rw [(lgw_cut_update_lt b i j j₀ hij h1 x c).1, lgw_cutL_c b i j c c₀]
    have hRw : ∀ x c, cutRLab (Function.update b j₀ x) i j c =
        Function.update R₀ (Fin.last (j.val - i.val)) c := by
      intro x c
      rw [(lgw_cut_update_lt b i j j₀ hij h1 x c).2, lgw_cutR_c b i j c c₀]
    simp only [hLw, hRw]
    exact lgw_comb hβ hAL
      (fun x c => Real.exp (θ * wordDiam (Function.update (Function.update L₀
          ⟨i.val, by have := j.2; omega⟩ c) ⟨j₀.val, by have := j.2; omega⟩ x)) *
        ‖primF β M m u (Function.update (Function.update L₀
          ⟨i.val, by have := j.2; omega⟩ c) ⟨j₀.val, by have := j.2; omega⟩ x) τL‖)
      (fun c => Real.exp (θ * wordDiam (Function.update R₀ (Fin.last (j.val - i.val)) c)) *
        ‖primF β M m u (Function.update R₀ (Fin.last (j.val - i.val)) c) τR‖)
      (fun c => hwR _)
      (fun c => hLr ⟨j₀.val, by have := j.2; omega⟩ (Function.update L₀
          ⟨i.val, by have := j.2; omega⟩ c) τL)
      (hRr (Fin.last _) R₀ τR)
  · by_cases h2 : j₀.val < j.val
    · -- the label is in the right cut word
      have hRw : ∀ x c, cutRLab (Function.update b j₀ x) i j c =
          Function.update (Function.update R₀ (Fin.last (j.val - i.val)) c)
            ⟨j₀.val - i.val, by omega⟩ x := by
        intro x c
        rw [(lgw_cut_update_mid b i j j₀ (by omega) h2 x c).1, lgw_cutR_c b i j c c₀]
      have hLw : ∀ x c, cutLLab (Function.update b j₀ x) i j c =
          Function.update L₀ ⟨i.val, by have := j.2; omega⟩ c := by
        intro x c
        rw [(lgw_cut_update_mid b i j j₀ (by omega) h2 x c).2, lgw_cutL_c b i j c c₀]
      simp only [hLw, hRw]
      have key := lgw_comb (X := Fin L) hβ hAR
        (fun x c => Real.exp (θ * wordDiam (Function.update (Function.update R₀
            (Fin.last (j.val - i.val)) c) ⟨j₀.val - i.val, by omega⟩ x)) *
          ‖primF β M m u (Function.update (Function.update R₀ (Fin.last (j.val - i.val)) c)
            ⟨j₀.val - i.val, by omega⟩ x) τR‖)
        (fun c => Real.exp (θ * wordDiam (Function.update L₀ ⟨i.val, by have := j.2; omega⟩ c)) *
          ‖primF β M m u (Function.update L₀ ⟨i.val, by have := j.2; omega⟩ c) τL‖)
        (fun c => hwL _)
        (fun c => hRr ⟨j₀.val - i.val, by omega⟩ (Function.update R₀
            (Fin.last (j.val - i.val)) c) τR)
        (hLr ⟨i.val, by have := j.2; omega⟩ L₀ τL)
      refine le_trans (le_of_eq ?_) (key.trans (le_of_eq (mul_comm _ _)))
      congr 1
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun c _ => mul_comm _ _
    · -- the label is in the left cut word, from `j` on
      have hLw : ∀ x c, cutLLab (Function.update b j₀ x) i j c =
          Function.update (Function.update L₀ ⟨i.val, by have := j.2; omega⟩ c)
            ⟨j₀.val + i.val + 1 - j.val, by have := j₀.2; omega⟩ x := by
        intro x c
        rw [(lgw_cut_update_ge b i j j₀ hij (by omega) x c).1, lgw_cutL_c b i j c c₀]
      have hRw : ∀ x c, cutRLab (Function.update b j₀ x) i j c =
          Function.update R₀ (Fin.last (j.val - i.val)) c := by
        intro x c
        rw [(lgw_cut_update_ge b i j j₀ hij (by omega) x c).2, lgw_cutR_c b i j c c₀]
      simp only [hLw, hRw]
      exact lgw_comb hβ hAL
        (fun x c => Real.exp (θ * wordDiam (Function.update (Function.update L₀
            ⟨i.val, by have := j.2; omega⟩ c) ⟨j₀.val + i.val + 1 - j.val, by
              have := j₀.2; omega⟩ x)) *
          ‖primF β M m u (Function.update (Function.update L₀
            ⟨i.val, by have := j.2; omega⟩ c) ⟨j₀.val + i.val + 1 - j.val, by
              have := j₀.2; omega⟩ x) τL‖)
        (fun c => Real.exp (θ * wordDiam (Function.update R₀ (Fin.last (j.val - i.val)) c)) *
          ‖primF β M m u (Function.update R₀ (Fin.last (j.val - i.val)) c) τR‖)
        (fun c => hwR _)
        (fun c => hLr ⟨j₀.val + i.val + 1 - j.val, by have := j₀.2; omega⟩ (Function.update L₀
            ⟨i.val, by have := j.2; omega⟩ c) τL)
        (hRr (Fin.last _) R₀ τR)

/-- Row bound for the whole diagonal source. -/
private lemma lgw_src_row {θ β : ℝ} (hθ : 0 ≤ θ) (hβ : 0 < β) {M : Matrix (Fin L) (Fin L) ℂ}
    {m : ℂ} {T A : ℝ} {n : ℕ}
    (hIH : ∀ n', 2 ≤ n' → n' < n → lgw_Bd θ β M m T n' A) {u : ℝ} (hu : 0 ≤ u) (huT : u ≤ T)
    (σ : Fin n → Bool) (b : Fin n → Fin L) (j₀ : Fin n) :
    β ^ 2 * ∑ x : Fin L, Real.exp (θ * wordDiam (Function.update b j₀ x)) *
      ‖lgw_src β M m n u σ (Function.update b j₀ x)‖ ≤
      ((polyDiags n).card : ℝ) * (A ^ 2 * ((1 - u) ^ (2 * n - 2))⁻¹) := by
  calc β ^ 2 * ∑ x : Fin L, Real.exp (θ * wordDiam (Function.update b j₀ x)) *
        ‖lgw_src β M m n u σ (Function.update b j₀ x)‖
      ≤ β ^ 2 * ∑ x : Fin L, ∑ d ∈ polyDiags n, Real.exp (θ * wordDiam (Function.update b j₀ x)) *
        ‖∑ c : Fin L, primF β M m u (cutLLab (Function.update b j₀ x) d.1 d.2 c)
          (cutLSgn σ d.1 d.2) *
        primF β M m u (cutRLab (Function.update b j₀ x) d.1 d.2 c) (cutRSgn σ d.1 d.2)‖ := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => ?_) (by positivity)
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Real.exp_pos _).le
    _ = ∑ d ∈ polyDiags n, β ^ 2 * ∑ x : Fin L,
        Real.exp (θ * wordDiam (Function.update b j₀ x)) *
        ‖∑ c : Fin L, primF β M m u (cutLLab (Function.update b j₀ x) d.1 d.2 c)
          (cutLSgn σ d.1 d.2) *
        primF β M m u (cutRLab (Function.update b j₀ x) d.1 d.2 c) (cutRSgn σ d.1 d.2)‖ := by
        rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ _d ∈ polyDiags n, (A ^ 2 * ((1 - u) ^ (2 * n - 2))⁻¹) :=
        Finset.sum_le_sum fun d hd => lgw_term_row hθ hβ hIH hu huT σ b j₀ hd
    _ = ((polyDiags n).card : ℝ) * (A ^ 2 * ((1 - u) ^ (2 * n - 2))⁻¹) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- `∫_0^t (1 - u)^{-(p+1)} du ≤ (1 - t)^{-p}` for `p ≥ 1`. -/
private lemma lgw_int {p : ℕ} (hp : 1 ≤ p) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∫ u in (0 : ℝ)..t, ((1 - u) ^ (p + 1))⁻¹ ≤ ((1 - t) ^ p)⁻¹ := by
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun u : ℝ => (1 / (p : ℝ)) * ((1 - u) ^ p)⁻¹) (((1 - u) ^ (p + 1))⁻¹) u := by
    intro u hu
    rw [Set.uIcc_of_le ht0] at hu
    have hu1 : 0 < 1 - u := by linarith [hu.2]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    have h1 : HasDerivAt (fun u : ℝ => (1 - u) ^ (q + 1))
        (((q + 1 : ℕ) : ℝ) * (1 - u) ^ q * (-1)) u := by
      simpa using ((hasDerivAt_id u).const_sub 1).fun_pow (q + 1)
    have h2 := (h1.inv (pow_ne_zero _ hu1.ne')).const_mul (1 / ((q + 1 : ℕ) : ℝ))
    refine h2.congr_deriv ?_
    have hq : ((q + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hcont : ContinuousOn (fun u : ℝ => ((1 - u) ^ (p + 1))⁻¹) (Set.uIcc 0 t) := by
    rw [Set.uIcc_of_le ht0]
    refine ContinuousOn.inv₀ (by fun_prop) fun u hu => ?_
    have : 0 < 1 - u := by linarith [hu.2]
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp only [sub_zero, one_pow, inv_one]
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hX : 0 ≤ ((1 - t) ^ p)⁻¹ := by
    have : 0 < 1 - t := by linarith
    positivity
  have hp1 : 1 / (p : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact hp'
  have hp2 : 0 ≤ 1 / (p : ℝ) := by positivity
  nlinarith

/-- The propagator is continuous in the starting time. -/
private lemma lgw_pairU_cont {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {t : ℝ} (ht : |t| < 1) (s s' : Bool) (a b : Fin L) :
    Continuous fun u : ℝ => pairU β M u t s s' a b := by
  have : (fun u : ℝ => pairU β M u t s s' a b) = fun u : ℝ =>
      (1 : Matrix (Fin L) (Fin L) ℂ) a b + ((t - u : ℝ) : ℂ) * pairK β M t s s' a b := by
    funext u
    rw [lgw_U_eq' hD ht]
    simp [Matrix.add_apply, Matrix.smul_apply]
  rw [this]
  fun_prop

/-- `F_k`, `k ≥ 2`, is continuous in time on `[0, t]`, `t < 1`. -/
private lemma lgw_primF_cont {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {t : ℝ} (ht1 : t < 1) {k : ℕ} (hk : 2 ≤ k) (a : Fin k → Fin L)
    (σ : Fin k → Bool) : ContinuousOn (fun s => primF β M m s a σ) (Set.Icc 0 t) :=
  fun s hs => (primF_hasDerivAt hD s ⟨by linarith [hs.1], by linarith [hs.2]⟩ hk a
    σ).continuousAt.continuousWithinAt

/-- The Duhamel integrand is continuous in time. -/
private lemma lgw_g_cont {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} (hD : PrimData β M m)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {n : ℕ} (a : Fin n → Fin L) (σ : Fin n → Bool) :
    ContinuousOn (fun u : ℝ => ∑ b : Fin n → Fin L,
      (∏ j, pairU β M u t (σ j) (σ (finRotate n j)) (a j) (b j)) * lgw_src β M m n u σ b)
      (Set.Icc 0 t) := by
  have ht : |t| < 1 := abs_lt.mpr ⟨by linarith, ht1⟩
  refine continuousOn_finsetSum _ fun b _ => ContinuousOn.mul ?_ ?_
  · exact (continuous_finsetProd _ fun j _ => lgw_pairU_cont hD ht _ _ _ _).continuousOn
  · unfold lgw_src
    refine continuousOn_finsetSum _ fun d hd => continuousOn_finsetSum _ fun c _ =>
      ContinuousOn.mul ?_ ?_
    · obtain ⟨h1, -, -, -, -⟩ := lgw_diag_len hd
      exact lgw_primF_cont hD ht1 h1 _ _
    · obtain ⟨-, -, h1, -, -⟩ := lgw_diag_len hd
      exact lgw_primF_cont hD ht1 h1 _ _

/-- The columns of the propagators: the row bound passes to the column bound by symmetry. -/
private lemma lgw_U_col {θ β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} (hD : PrimData β M m)
    {u t r : ℝ} (ht : |t| < 1) (s s' : Bool)
    (hrow : ∀ a, ∑ y, Real.exp (2 * θ * cycDist a y) * ‖pairU β M u t s s' a y‖ ≤ r) (b : Fin L) :
    ∑ a, Real.exp (2 * θ * cycDist a b) * ‖pairU β M u t s s' a b‖ ≤ r := by
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_)) (hrow b)
  have e : pairU β M u t s s' a b = pairU β M u t s s' b a := by
    have := congrFun (congrFun (lgw_U_symm hD ht u s s') b) a
    simpa [Matrix.transpose_apply] using this
  rw [e, lgw_cd_comm a b]

/-- The algebra of the integrand of the source: the powers of `1 - u`. -/
private lemma lgw_alg {Bp A N : ℝ} {n : ℕ} (hn : 2 ≤ n) {u t : ℝ} (hu : u < 1) (ht : t < 1) :
    (Bp * ((1 - u) / (1 - t))) ^ n * (N * (A ^ 2 * ((1 - u) ^ (2 * n - 2))⁻¹)) =
      (Bp ^ n * N * A ^ 2 * ((1 - t) ^ n)⁻¹) * ((1 - u) ^ (n - 2))⁻¹ := by
  have hu' : 0 < 1 - u := by linarith
  have ht' : 0 < 1 - t := by linarith
  have h2 : 2 * n - 2 = n + (n - 2) := by omega
  rw [h2, pow_add, mul_pow, div_pow]
  field_simp

/-- The source part of the weighted sup bound of Duhamel's formula. -/
private lemma lgw_int_sup {θ β : ℝ} (hθ : 0 ≤ θ) {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {T Bp A : ℝ} {n : ℕ} (hn : 4 ≤ n) (hT1 : T < 1) (hBp : 0 ≤ Bp)
    (hU : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T → ∀ (s s' : Bool) (a : Fin L),
      ∑ b, Real.exp (2 * θ * cycDist a b) * ‖pairU β M u t s s' a b‖ ≤ Bp * ((1 - u) / (1 - t)))
    (hIH : ∀ n', 2 ≤ n' → n' < n → lgw_Bd θ β M m T n' A) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    (a : Fin n → Fin L) (σ : Fin n → Bool) :
    β * (Real.exp (θ * wordDiam a) * ‖∫ u in (0 : ℝ)..t, ∑ b : Fin n → Fin L,
        (∏ j, pairU β M u t (σ j) (σ (finRotate n j)) (a j) (b j)) *
          lgw_src β M m n u σ b‖) ≤
      Bp ^ n * ((polyDiags n).card : ℝ) * A ^ 2 * ((1 - t) ^ (2 * n - 3))⁻¹ := by
  have hβ := hD.pos
  have ht1 : t < 1 := lt_of_le_of_lt htT hT1
  have ht : |t| < 1 := abs_lt.mpr ⟨by linarith, ht1⟩
  have h1t : 0 < 1 - t := by linarith
  set g : ℝ → ℂ := fun u => ∑ b : Fin n → Fin L,
    (∏ j, pairU β M u t (σ j) (σ (finRotate n j)) (a j) (b j)) * lgw_src β M m n u σ b with hg
  set w : ℝ := Real.exp (θ * wordDiam a) with hw
  set Cst : ℝ := Bp ^ n * ((polyDiags n).card : ℝ) * A ^ 2 * ((1 - t) ^ n)⁻¹ with hCst
  have hw0 : 0 < w := Real.exp_pos _
  have hCst0 : 0 ≤ Cst := by rw [hCst]; positivity
  have hpt : ∀ u ∈ Set.Ioc (0 : ℝ) t,
      ‖((β * w : ℝ) : ℂ) * g u‖ ≤ Cst * ((1 - u) ^ (n - 2))⁻¹ := by
    intro u hu
    have hu0 : 0 ≤ u := hu.1.le
    have huT : u ≤ T := hu.2.trans htT
    have hu1 : u < 1 := by linarith [hu.2]
    have hrowU : ∀ i : Fin n, ∀ a' : Fin L, ∑ y, Real.exp (2 * θ * cycDist a' y) *
        ‖pairU β M u t (σ i) (σ (finRotate n i)) a' y‖ ≤ Bp * ((1 - u) / (1 - t)) :=
      fun i a' => hU u t hu0 hu.2 htT _ _ a'
    set X : ℝ := ((polyDiags n).card : ℝ) * (A ^ 2 * ((1 - u) ^ (2 * n - 2))⁻¹) with hX
    have hX0 : 0 ≤ X := by positivity
    have hG : ∀ b : Fin n → Fin L, Real.exp (θ * wordDiam b) * ‖lgw_src β M m n u σ b‖ ≤
        X / β := fun b => by
      rw [le_div_iff₀ hβ, mul_comm]
      exact lgw_src_sup hθ hβ hIH hu0 huT σ b
    have hP := lgw_prop_sup θ hθ (fun i => pairU β M u t (σ i) (σ (finRotate n i)))
      (div_nonneg hX0 hβ.le) hrowU (lgw_src β M m n u σ) hG a
    have hr0 : 0 ≤ Bp * ((1 - u) / (1 - t)) :=
      le_trans (Finset.sum_nonneg fun b _ => by positivity)
        (hrowU ⟨0, by omega⟩ (a ⟨0, by omega⟩))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc β * w * ‖g u‖ = β * (w * ‖g u‖) := by ring
      _ ≤ β * ((Bp * ((1 - u) / (1 - t))) ^ n * (X / β)) :=
          mul_le_mul_of_nonneg_left hP hβ.le
      _ = (Bp * ((1 - u) / (1 - t))) ^ n * X := by field_simp
      _ = Cst * ((1 - u) ^ (n - 2))⁻¹ := lgw_alg (by omega) hu1 ht1
  have hn3 : 1 ≤ n - 3 := by omega
  have hint : IntervalIntegrable (fun u : ℝ => Cst * ((1 - u) ^ (n - 2))⁻¹) MeasureTheory.volume
      0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le ht0]
    refine continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop) fun u hu => ?_)
    have : 0 < 1 - u := by linarith [hu.2]
    positivity
  have h1 := intervalIntegral.norm_integral_le_of_norm_le ht0
    (Filter.Eventually.of_forall hpt) hint
  have h2 : ∫ u in (0 : ℝ)..t, Cst * ((1 - u) ^ (n - 2))⁻¹ ≤ Cst * ((1 - t) ^ (n - 3))⁻¹ := by
    rw [intervalIntegral.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ hCst0
    have := lgw_int hn3 ht0 ht1
    rwa [show n - 3 + 1 = n - 2 by omega] at this
  have h3 : β * (w * ‖∫ u in (0 : ℝ)..t, g u‖) =
      ‖∫ u in (0 : ℝ)..t, ((β * w : ℝ) : ℂ) * g u‖ := by
    rw [intervalIntegral.integral_const_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    ring
  rw [h3]
  refine h1.trans (h2.trans (le_of_eq ?_))
  rw [hCst]
  have : 2 * n - 3 = n + (n - 3) := by omega
  rw [this, pow_add, mul_inv]
  ring

/-- The source part of the weighted row bound of Duhamel's formula. -/
private lemma lgw_int_row {θ β : ℝ} (hθ : 0 ≤ θ) {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {T Bp A : ℝ} {n : ℕ} (hn : 4 ≤ n) (hT1 : T < 1) (hBp : 0 ≤ Bp)
    (hU : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T → ∀ (s s' : Bool) (a : Fin L),
      ∑ b, Real.exp (2 * θ * cycDist a b) * ‖pairU β M u t s s' a b‖ ≤ Bp * ((1 - u) / (1 - t)))
    (hIH : ∀ n', 2 ≤ n' → n' < n → lgw_Bd θ β M m T n' A) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    (j : Fin n) (a : Fin n → Fin L) (σ : Fin n → Bool) :
    β * ∑ x : Fin L, Real.exp (θ * wordDiam (Function.update a j x)) *
        ‖(β : ℂ) * ∫ u in (0 : ℝ)..t, ∑ b : Fin n → Fin L,
          (∏ i, pairU β M u t (σ i) (σ (finRotate n i)) ((Function.update a j x) i) (b i)) *
            lgw_src β M m n u σ b‖ ≤
      Bp ^ n * ((polyDiags n).card : ℝ) * A ^ 2 * ((1 - t) ^ (2 * n - 3))⁻¹ := by
  have hβ := hD.pos
  have ht1 : t < 1 := lt_of_le_of_lt htT hT1
  have ht : |t| < 1 := abs_lt.mpr ⟨by linarith, ht1⟩
  have h1t : 0 < 1 - t := by linarith
  set g : (Fin L) → ℝ → ℂ := fun x u => ∑ b : Fin n → Fin L,
    (∏ i, pairU β M u t (σ i) (σ (finRotate n i)) ((Function.update a j x) i) (b i)) *
      lgw_src β M m n u σ b with hg
  set w : Fin L → ℝ := fun x => Real.exp (θ * wordDiam (Function.update a j x)) with hw
  set Cst : ℝ := Bp ^ n * ((polyDiags n).card : ℝ) * A ^ 2 * ((1 - t) ^ n)⁻¹ with hCst
  have hCst0 : 0 ≤ Cst := by rw [hCst]; positivity
  have hw0 : ∀ x, 0 < w x := fun x => Real.exp_pos _
  have hpt : ∀ u ∈ Set.Icc (0 : ℝ) t,
      β ^ 2 * ∑ x, w x * ‖g x u‖ ≤ Cst * ((1 - u) ^ (n - 2))⁻¹ := by
    intro u hu
    have hu0 : 0 ≤ u := hu.1
    have huT : u ≤ T := hu.2.trans htT
    have hu1 : u < 1 := by linarith [hu.2]
    have hrowU : ∀ i : Fin n, ∀ a' : Fin L, ∑ y, Real.exp (2 * θ * cycDist a' y) *
        ‖pairU β M u t (σ i) (σ (finRotate n i)) a' y‖ ≤ Bp * ((1 - u) / (1 - t)) :=
      fun i a' => hU u t hu0 hu.2 htT _ _ a'
    have hcolU : ∀ i : Fin n, ∀ b' : Fin L, ∑ a', Real.exp (2 * θ * cycDist a' b') *
        ‖pairU β M u t (σ i) (σ (finRotate n i)) a' b'‖ ≤ Bp * ((1 - u) / (1 - t)) :=
      fun i b' => lgw_U_col hD ht _ _ (fun a' => hrowU i a') b'
    set X : ℝ := ((polyDiags n).card : ℝ) * (A ^ 2 * ((1 - u) ^ (2 * n - 2))⁻¹) with hX
    have hX0 : 0 ≤ X := by positivity
    have hG : ∀ b : Fin n → Fin L, ∑ y, Real.exp (θ * wordDiam (Function.update b j y)) *
        ‖lgw_src β M m n u σ (Function.update b j y)‖ ≤ X / β ^ 2 := fun b => by
      rw [le_div_iff₀ (by positivity), mul_comm]
      exact lgw_src_row hθ hβ hIH hu0 huT σ b j
    have hP := lgw_prop_row θ hθ (fun i => pairU β M u t (σ i) (σ (finRotate n i)))
      (div_nonneg hX0 (by positivity)) hrowU hcolU (lgw_src β M m n u σ) j hG a
    calc β ^ 2 * ∑ x, w x * ‖g x u‖
        ≤ β ^ 2 * ((Bp * ((1 - u) / (1 - t))) ^ n * (X / β ^ 2)) :=
          mul_le_mul_of_nonneg_left hP (by positivity)
      _ = (Bp * ((1 - u) / (1 - t))) ^ n * X := by field_simp
      _ = Cst * ((1 - u) ^ (n - 2))⁻¹ := lgw_alg (by omega) hu1 ht1
  have hcontx : ∀ x, ContinuousOn (fun u => ‖g x u‖) (Set.Icc 0 t) :=
    fun x => (lgw_g_cont hD ht0 ht1 (Function.update a j x) σ).norm
  have hint1 : ∀ x, IntervalIntegrable (fun u => ‖g x u‖) MeasureTheory.volume 0 t := by
    intro x
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le ht0]
    exact hcontx x
  have hint2 : IntervalIntegrable (fun u : ℝ => Cst * ((1 - u) ^ (n - 2))⁻¹)
      MeasureTheory.volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le ht0]
    refine continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop) fun u hu => ?_)
    have : 0 < 1 - u := by linarith [hu.2]
    positivity
  have hint3 : IntervalIntegrable (fun u => β ^ 2 * ∑ x, w x * ‖g x u‖)
      MeasureTheory.volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le ht0]
    exact continuousOn_const.mul (continuousOn_finsetSum _ fun x _ =>
      continuousOn_const.mul (hcontx x))
  have hn3 : 1 ≤ n - 3 := by omega
  have hbound : ∫ u in (0 : ℝ)..t, β ^ 2 * ∑ x, w x * ‖g x u‖ ≤ Cst * ((1 - t) ^ (n - 3))⁻¹ := by
    refine (intervalIntegral.integral_mono_on ht0 hint3 hint2 hpt).trans ?_
    rw [intervalIntegral.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ hCst0
    have := lgw_int hn3 ht0 ht1
    rwa [show n - 3 + 1 = n - 2 by omega] at this
  have hswap : ∫ u in (0 : ℝ)..t, β ^ 2 * ∑ x, w x * ‖g x u‖ =
      β ^ 2 * ∑ x, w x * ∫ u in (0 : ℝ)..t, ‖g x u‖ := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
      (fun x _ => (hint1 x).const_mul (w x))]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [intervalIntegral.integral_const_mul]
  calc β * ∑ x, w x * ‖(β : ℂ) * ∫ u in (0 : ℝ)..t, g x u‖
      = β ^ 2 * ∑ x, w x * ‖∫ u in (0 : ℝ)..t, g x u‖ := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ]
        ring
    _ ≤ β ^ 2 * ∑ x, w x * ∫ u in (0 : ℝ)..t, ‖g x u‖ := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm ht0)
          (hw0 x).le
    _ = ∫ u in (0 : ℝ)..t, β ^ 2 * ∑ x, w x * ‖g x u‖ := hswap.symm
    _ ≤ Cst * ((1 - t) ^ (n - 3))⁻¹ := hbound
    _ = Bp ^ n * ((polyDiags n).card : ℝ) * A ^ 2 * ((1 - t) ^ (2 * n - 3))⁻¹ := by
        rw [hCst]
        have : 2 * n - 3 = n + (n - 3) := by omega
        rw [this, pow_add, mul_inv]
        ring

/-- One step of the induction on the length: the weighted sup and row bounds of `F_n`, `n ≥ 3`,
from those of the shorter loops, the propagator rows and the initial values, by Duhamel's formula
(5.16) [fo:eq:duhamel]. -/
private lemma lgw_step {θ β : ℝ} (hθ : 0 ≤ θ) {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {T Bp I A : ℝ} {n : ℕ} (hn : 3 ≤ n) (hT1 : T < 1)
    (hBp : 1 ≤ Bp) (hI : 1 ≤ I) (hA : 1 ≤ A)
    (hU : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T → ∀ (s s' : Bool) (a : Fin L),
      ∑ b, Real.exp (2 * θ * cycDist a b) * ‖pairU β M u t s s' a b‖ ≤ Bp * ((1 - u) / (1 - t)))
    (hI_sup : ∀ (a : Fin n → Fin L) (σ : Fin n → Bool),
      Real.exp (θ * wordDiam a) * ‖primF β M m 0 a σ‖ ≤ I ^ n)
    (hI_row : ∀ (j : Fin n) (a : Fin n → Fin L) (σ : Fin n → Bool),
      β * ∑ c : Fin L, Real.exp (θ * wordDiam (Function.update a j c)) *
        ‖primF β M m 0 (Function.update a j c) σ‖ ≤ I ^ n)
    (hIH : ∀ n', 2 ≤ n' → n' < n → lgw_Bd θ β M m T n' A) :
    lgw_Bd θ β M m T n (Bp ^ n * (I ^ n + (n : ℝ) ^ 2 * A ^ 2)) := by
  intro t ht0 htT
  have hβ := hD.pos
  have ht1 : t < 1 := lt_of_le_of_lt htT hT1
  have ht : |t| < 1 := abs_lt.mpr ⟨by linarith, ht1⟩
  have h1t : 0 < 1 - t := by linarith
  have hBp0 : 0 ≤ Bp := by linarith
  have hmono : ((1 - t) ^ n)⁻¹ ≤ ((1 - t) ^ (2 * n - 3))⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_of_le_one h1t.le (by linarith) (by omega))
  have hcard : ((polyDiags n).card : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (polyDiags n).card ≤ n ^ 2 := by
      calc (polyDiags n).card ≤ Fintype.card (Fin n × Fin n) := Finset.card_le_univ _
        _ = n ^ 2 := by simp [sq]
    exact_mod_cast this
  -- the propagation part, with `s = 0`
  have hrow0 : ∀ i : Fin n, ∀ (σ : Fin n → Bool) (a' : Fin L),
      ∑ y, Real.exp (2 * θ * cycDist a' y) *
        ‖pairU β M 0 t (σ i) (σ (finRotate n i)) a' y‖ ≤ Bp * ((1 - 0) / (1 - t)) :=
    fun i σ a' => hU 0 t le_rfl ht0 htT _ _ a'
  have hcol0 : ∀ i : Fin n, ∀ (σ : Fin n → Bool) (b' : Fin L),
      ∑ a', Real.exp (2 * θ * cycDist a' b') *
        ‖pairU β M 0 t (σ i) (σ (finRotate n i)) a' b'‖ ≤ Bp * ((1 - 0) / (1 - t)) :=
    fun i σ b' => lgw_U_col hD ht _ _ (fun a' => hrow0 i σ a') b'
  have hr0 : 0 ≤ Bp * ((1 - 0) / (1 - t)) := by simp only [sub_zero, one_div]; positivity
  have hrp : (Bp * ((1 - 0) / (1 - t))) ^ n = Bp ^ n * ((1 - t) ^ n)⁻¹ := by
    simp [mul_pow, inv_pow]
  have hI0 : 0 ≤ I ^ n := by positivity
  have hfin : Bp ^ n * (I ^ n * ((1 - t) ^ n)⁻¹) +
      Bp ^ n * (n : ℝ) ^ 2 * A ^ 2 * ((1 - t) ^ (2 * n - 3))⁻¹ ≤
      Bp ^ n * (I ^ n + (n : ℝ) ^ 2 * A ^ 2) * ((1 - t) ^ (2 * n - 3))⁻¹ := by
    have h1 : Bp ^ n * (I ^ n * ((1 - t) ^ n)⁻¹) ≤ Bp ^ n * (I ^ n * ((1 - t) ^ (2 * n - 3))⁻¹) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono hI0) (by positivity)
    nlinarith
  refine ⟨fun a σ => ?_, fun j a σ => ?_⟩
  · -- the weighted sup bound
    have hdu : primF β M m t a σ = ∑ b : Fin n → Fin L,
        (∏ i, pairU β M 0 t (σ i) (σ (finRotate n i)) (a i) (b i)) * primF β M m 0 b σ +
        (β : ℂ) * ∫ u in (0 : ℝ)..t, ∑ b : Fin n → Fin L,
          (∏ i, pairU β M u t (σ i) (σ (finRotate n i)) (a i) (b i)) *
            lgw_src β M m n u σ b := primF_duhamel hD 0 t le_rfl ht0 ht1 hn a σ
    have hP := lgw_prop_sup θ hθ (fun i => pairU β M 0 t (σ i) (σ (finRotate n i))) hI0
      (fun i a' => hrow0 i σ a') (fun b => primF β M m 0 b σ) (fun b => hI_sup b σ) a
    have hsrc : β * (Real.exp (θ * wordDiam a) * ‖(∫ u in (0 : ℝ)..t, ∑ b : Fin n → Fin L,
          (∏ i, pairU β M u t (σ i) (σ (finRotate n i)) (a i) (b i)) *
            lgw_src β M m n u σ b)‖) ≤
        Bp ^ n * (n : ℝ) ^ 2 * A ^ 2 * ((1 - t) ^ (2 * n - 3))⁻¹ := by
      rcases hn.eq_or_lt with h3 | h4
      · subst h3
        have hpd : polyDiags 3 = ∅ := by decide
        have hz : ∀ (u : ℝ) (b : Fin 3 → Fin L), lgw_src β M m 3 u σ b = 0 := by
          intro u b
          simp [lgw_src, hpd]
        simp only [hz, mul_zero, Finset.sum_const_zero, intervalIntegral.integral_zero, norm_zero]
        positivity
      · have := lgw_int_sup hθ hD (by omega : 4 ≤ n) hT1 hBp0 hU hIH ht0 htT a σ
        refine this.trans ?_
        have : Bp ^ n * ((polyDiags n).card : ℝ) * A ^ 2 ≤ Bp ^ n * (n : ℝ) ^ 2 * A ^ 2 := by
          gcongr
        exact mul_le_mul_of_nonneg_right this (by positivity)
    rw [hdu]
    calc Real.exp (θ * wordDiam a) * ‖∑ b : Fin n → Fin L,
          (∏ i, pairU β M 0 t (σ i) (σ (finRotate n i)) (a i) (b i)) * primF β M m 0 b σ +
        (β : ℂ) * ∫ u in (0 : ℝ)..t, ∑ b : Fin n → Fin L,
          (∏ i, pairU β M u t (σ i) (σ (finRotate n i)) (a i) (b i)) *
            lgw_src β M m n u σ b‖
        ≤ Real.exp (θ * wordDiam a) * (‖∑ b : Fin n → Fin L,
          (∏ i, pairU β M 0 t (σ i) (σ (finRotate n i)) (a i) (b i)) * primF β M m 0 b σ‖ +
        ‖(β : ℂ) * ∫ u in (0 : ℝ)..t, ∑ b : Fin n → Fin L,
          (∏ i, pairU β M u t (σ i) (σ (finRotate n i)) (a i) (b i)) *
            lgw_src β M m n u σ b‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.exp_pos _).le
      _ = Real.exp (θ * wordDiam a) * ‖∑ b : Fin n → Fin L,
          (∏ i, pairU β M 0 t (σ i) (σ (finRotate n i)) (a i) (b i)) * primF β M m 0 b σ‖ +
          β * (Real.exp (θ * wordDiam a) * ‖(∫ u in (0 : ℝ)..t, ∑ b : Fin n → Fin L,
          (∏ i, pairU β M u t (σ i) (σ (finRotate n i)) (a i) (b i)) *
            lgw_src β M m n u σ b)‖) := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ]
          ring
      _ ≤ (Bp ^ n * ((1 - t) ^ n)⁻¹) * I ^ n +
          Bp ^ n * (n : ℝ) ^ 2 * A ^ 2 * ((1 - t) ^ (2 * n - 3))⁻¹ := by
          refine add_le_add ?_ hsrc
          rw [← hrp]
          exact hP
      _ ≤ _ := by
          calc _ = Bp ^ n * (I ^ n * ((1 - t) ^ n)⁻¹) +
              Bp ^ n * (n : ℝ) ^ 2 * A ^ 2 * ((1 - t) ^ (2 * n - 3))⁻¹ := by ring
            _ ≤ _ := hfin
  · -- the weighted row bound
    have hdu : ∀ x : Fin L, primF β M m t (Function.update a j x) σ = ∑ b : Fin n → Fin L,
        (∏ i, pairU β M 0 t (σ i) (σ (finRotate n i)) ((Function.update a j x) i) (b i)) *
          primF β M m 0 b σ +
        (β : ℂ) * ∫ u in (0 : ℝ)..t, ∑ b : Fin n → Fin L,
          (∏ i, pairU β M u t (σ i) (σ (finRotate n i)) ((Function.update a j x) i) (b i)) *
            lgw_src β M m n u σ b := fun x =>
      primF_duhamel hD 0 t le_rfl ht0 ht1 hn (Function.update a j x) σ
    have hG0 : ∀ b : Fin n → Fin L, ∑ y, Real.exp (θ * wordDiam (Function.update b j y)) *
        ‖primF β M m 0 (Function.update b j y) σ‖ ≤ I ^ n / β := fun b => by
      rw [le_div_iff₀ hβ, mul_comm]
      exact hI_row j b σ
    have hP := lgw_prop_row θ hθ (fun i => pairU β M 0 t (σ i) (σ (finRotate n i)))
      (div_nonneg hI0 hβ.le) (fun i a' => hrow0 i σ a') (fun i b' => hcol0 i σ b')
      (fun b => primF β M m 0 b σ) j hG0 a
    have hsrc : β * ∑ x : Fin L, Real.exp (θ * wordDiam (Function.update a j x)) *
        ‖(β : ℂ) * ∫ u in (0 : ℝ)..t, ∑ b : Fin n → Fin L,
          (∏ i, pairU β M u t (σ i) (σ (finRotate n i)) ((Function.update a j x) i) (b i)) *
            lgw_src β M m n u σ b‖ ≤
        Bp ^ n * (n : ℝ) ^ 2 * A ^ 2 * ((1 - t) ^ (2 * n - 3))⁻¹ := by
      rcases hn.eq_or_lt with h3 | h4
      · subst h3
        have hpd : polyDiags 3 = ∅ := by decide
        have hz : ∀ (u : ℝ) (b : Fin 3 → Fin L), lgw_src β M m 3 u σ b = 0 := by
          intro u b
          simp [lgw_src, hpd]
        simp only [hz, mul_zero, Finset.sum_const_zero, intervalIntegral.integral_zero, norm_zero]
        positivity
      · have := lgw_int_row hθ hD (by omega : 4 ≤ n) hT1 hBp0 hU hIH ht0 htT j a σ
        refine this.trans ?_
        have : Bp ^ n * ((polyDiags n).card : ℝ) * A ^ 2 ≤ Bp ^ n * (n : ℝ) ^ 2 * A ^ 2 := by
          gcongr
        exact mul_le_mul_of_nonneg_right this (by positivity)
    calc β * ∑ c : Fin L, Real.exp (θ * wordDiam (Function.update a j c)) *
          ‖primF β M m t (Function.update a j c) σ‖
        ≤ β * ∑ x : Fin L, Real.exp (θ * wordDiam (Function.update a j x)) *
          (‖∑ b : Fin n → Fin L,
            (∏ i, pairU β M 0 t (σ i) (σ (finRotate n i)) ((Function.update a j x) i) (b i)) *
              primF β M m 0 b σ‖ +
          ‖(β : ℂ) * ∫ u in (0 : ℝ)..t, ∑ b : Fin n → Fin L,
            (∏ i, pairU β M u t (σ i) (σ (finRotate n i)) ((Function.update a j x) i) (b i)) *
              lgw_src β M m n u σ b‖) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => ?_) hβ.le
          rw [hdu x]
          exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.exp_pos _).le
      _ = β * ∑ x : Fin L, Real.exp (θ * wordDiam (Function.update a j x)) *
          ‖∑ b : Fin n → Fin L,
            (∏ i, pairU β M 0 t (σ i) (σ (finRotate n i)) ((Function.update a j x) i) (b i)) *
              primF β M m 0 b σ‖ +
          β * ∑ x : Fin L, Real.exp (θ * wordDiam (Function.update a j x)) *
          ‖(β : ℂ) * ∫ u in (0 : ℝ)..t, ∑ b : Fin n → Fin L,
            (∏ i, pairU β M u t (σ i) (σ (finRotate n i)) ((Function.update a j x) i) (b i)) *
              lgw_src β M m n u σ b‖ := by
          rw [← mul_add, ← Finset.sum_add_distrib]
          congr 1
          refine Finset.sum_congr rfl fun x _ => ?_
          ring
      _ ≤ (Bp ^ n * ((1 - t) ^ n)⁻¹) * I ^ n +
          Bp ^ n * (n : ℝ) ^ 2 * A ^ 2 * ((1 - t) ^ (2 * n - 3))⁻¹ := by
          refine add_le_add ?_ hsrc
          rw [← hrp]
          calc β * ∑ x : Fin L, Real.exp (θ * wordDiam (Function.update a j x)) *
              ‖∑ b : Fin n → Fin L,
                (∏ i, pairU β M 0 t (σ i) (σ (finRotate n i)) ((Function.update a j x) i)
                  (b i)) * primF β M m 0 b σ‖
              ≤ β * ((Bp * ((1 - 0) / (1 - t))) ^ n * (I ^ n / β)) :=
                mul_le_mul_of_nonneg_left hP hβ.le
            _ = (Bp * ((1 - 0) / (1 - t))) ^ n * I ^ n := by field_simp
      _ ≤ _ := by
          calc _ = Bp ^ n * (I ^ n * ((1 - t) ^ n)⁻¹) +
              Bp ^ n * (n : ℝ) ^ 2 * A ^ 2 * ((1 - t) ^ (2 * n - 3))⁻¹ := by ring
            _ ≤ _ := hfin

/-- The bound `lgw_Bd` weakens with the constant. -/
private lemma lgw_Bd_mono {θ β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} {T : ℝ}
    (hT1 : T < 1) {n : ℕ} {A A' : ℝ} (h : lgw_Bd θ β M m T n A) (hAA : A ≤ A') :
    lgw_Bd θ β M m T n A' := by
  intro t ht0 htT
  obtain ⟨h1, h2⟩ := h t ht0 htT
  have h1t : 0 < 1 - t := by linarith
  have hp : 0 ≤ ((1 - t) ^ (2 * n - 3))⁻¹ := by positivity
  exact ⟨fun a σ => (h1 a σ).trans (mul_le_mul_of_nonneg_right hAA hp),
    fun j a σ => (h2 j a σ).trans (mul_le_mul_of_nonneg_right hAA hp)⟩

/-- The induction on the length: with the propagator rows (constant `Bp`), the bound of the
two-loops (constant `A₂`) and the initial values (constant `I`), one constant `A` bounds the
weighted sup and row of every `F_n`, `2 ≤ n ≤ K`. The constant depends on `(Bp, A₂, I, K)` only. -/
private lemma lgw_induct (Bp A₂ I : ℝ) (hBp : 1 ≤ Bp) (hA₂ : 1 ≤ A₂) (hI : 1 ≤ I) (K : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (L : ℕ) (β θ T : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ),
      PrimData β M m → 0 ≤ θ → T < 1 →
      (∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T → ∀ (s s' : Bool) (a : Fin L),
        ∑ b, Real.exp (2 * θ * cycDist a b) * ‖pairU β M u t s s' a b‖ ≤
          Bp * ((1 - u) / (1 - t))) →
      lgw_Bd θ β M m T 2 A₂ →
      (∀ n, 3 ≤ n → (∀ (a : Fin n → Fin L) (σ : Fin n → Bool),
          Real.exp (θ * wordDiam a) * ‖primF β M m 0 a σ‖ ≤ I ^ n) ∧
        (∀ (j : Fin n) (a : Fin n → Fin L) (σ : Fin n → Bool),
          β * ∑ c : Fin L, Real.exp (θ * wordDiam (Function.update a j c)) *
            ‖primF β M m 0 (Function.update a j c) σ‖ ≤ I ^ n)) →
      ∀ n, 2 ≤ n → n ≤ K → lgw_Bd θ β M m T n A := by
  induction K with
  | zero =>
    exact ⟨A₂, hA₂, fun L β θ T M m hD hθ hT1 hU h2 hinit n hn hnK => by omega⟩
  | succ K ih =>
    obtain ⟨A, hA, hK⟩ := ih
    refine ⟨max (max A A₂) (Bp ^ (K + 1) * (I ^ (K + 1) + ((K + 1 : ℕ) : ℝ) ^ 2 * A ^ 2)),
      le_trans hA ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
    intro L β θ T M m hD hθ hT1 hU h2 hinit n hn hnK
    have hAA : A ≤ max (max A A₂) (Bp ^ (K + 1) * (I ^ (K + 1) + ((K + 1 : ℕ) : ℝ) ^ 2 * A ^ 2)) :=
      (le_max_left _ _).trans (le_max_left _ _)
    have hA₂A : A₂ ≤ max (max A A₂)
        (Bp ^ (K + 1) * (I ^ (K + 1) + ((K + 1 : ℕ) : ℝ) ^ 2 * A ^ 2)) :=
      (le_max_right _ _).trans (le_max_left _ _)
    rcases Nat.lt_or_ge n (K + 1) with hlt | hge
    · exact lgw_Bd_mono hT1 (hK L β θ T M m hD hθ hT1 hU h2 hinit n hn (by omega)) hAA
    · have hn' : n = K + 1 := by omega
      subst hn'
      rcases Nat.lt_or_ge (K + 1) 3 with h3 | h3
      · have hK1 : K = 1 := by omega
        subst hK1
        exact lgw_Bd_mono hT1 h2 hA₂A
      · obtain ⟨hs, hr⟩ := hinit (K + 1) h3
        have := lgw_step hθ hD h3 hT1 hBp hI hA
          (hU) hs hr (fun n' hn'1 hn'2 => hK L β θ T M m hD hθ hT1 hU h2 hinit n' hn'1
            (by omega))
        exact lgw_Bd_mono hT1 this (le_max_right _ _)

/-- The diameter of a word is at most the length of the closed path through its labels. -/
private lemma lgw_diam_cycle {n : ℕ} (a : Fin n → Fin L) :
    wordDiam a ≤ ∑ l, cycDist (a l) (a (finRotate n l)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [wordDiam]
  set F : ℕ → ℕ := fun i =>
    if h : i < n then cycDist (a ⟨i, h⟩) (a (finRotate n ⟨i, h⟩)) else 0 with hF
  set f : ℕ → Fin L := fun i => if h : i < n then a ⟨i, h⟩ else a ⟨0, hn⟩ with hf
  have hsum : ∑ l, cycDist (a l) (a (finRotate n l)) = ∑ i ∈ Finset.range n, F i := by
    rw [← Fin.sum_univ_eq_sum_range F n]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [hF, l.2]
  have hrot : ∀ i (h : i + 1 < n),
      finRotate n ⟨i, by omega⟩ = ⟨i + 1, h⟩ := by
    intro i h
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    apply Fin.ext
    rw [coe_finRotate]
    have : (⟨i, by omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
      intro h'
      have := congrArg Fin.val h'
      simp at this
      omega
    simp [this]
  have chain : ∀ p d, p + d < n → cycDist (f p) (f (p + d)) ≤ ∑ i ∈ Finset.range d, F (p + i) := by
    intro p d
    induction d with
    | zero =>
      intro _
      simp [lgw_cd_self]
    | succ d ih =>
      intro hd
      have h1 := ih (by omega)
      have h2 := lgw_cd_tri (f p) (f (p + d)) (f (p + (d + 1)))
      have h3 : cycDist (f (p + d)) (f (p + (d + 1))) = F (p + d) := by
        have hlt : p + d < n := by omega
        have hlt' : p + d + 1 < n := by omega
        simp only [hf, hF, hlt, hd, dite_true]
        rw [hrot (p + d) hlt']
        rfl
      rw [Finset.sum_range_succ]
      omega
  refine lgw_diam_le a fun p q => ?_
  have key : ∀ p q : Fin n, p.val ≤ q.val →
      cycDist (a p) (a q) ≤ ∑ l, cycDist (a l) (a (finRotate n l)) := by
    intro p q hpq
    have := chain p.val (q.val - p.val) (by have := q.2; omega)
    have e1 : f p.val = a p := by simp [hf, p.2]
    have e2 : f (p.val + (q.val - p.val)) = a q := by
      have : p.val + (q.val - p.val) = q.val := by omega
      rw [this]; simp [hf, q.2]
    rw [e1, e2] at this
    refine this.trans ?_
    rw [hsum]
    have hsub : ∑ i ∈ Finset.range (q.val - p.val), F (p.val + i) =
        ∑ i ∈ Finset.Ico p.val q.val, F i := by
      rw [Finset.sum_Ico_eq_sum_range]
    rw [hsub]
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => by
      simp only [Finset.mem_Ico] at hi
      simp only [Finset.mem_range]
      have := q.2; omega) (fun i _ _ => Nat.zero_le _)
  rcases le_total p.val q.val with h | h
  · exact key p q h
  · rw [lgw_cd_comm]
    exact key q p h

/-- The weighted modulus of an entry of `M`. -/
private def lgw_g (θ : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (x y : Fin L) : ℝ :=
  Real.exp (θ * cycDist x y) * ‖M x y‖

private lemma lgw_g_nonneg (θ : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (x y : Fin L) :
    0 ≤ lgw_g θ M x y := by
  unfold lgw_g; positivity

/-- The signed matrices have the moduli of `M` (`M` is symmetric). -/
private lemma lgw_sgn_norm {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) (s : Bool) (x y : Fin L) : ‖sgnMat M s x y‖ = ‖M x y‖ := by
  have hsym : M y x = M x y := congrFun (congrFun hD.symm x) y
  cases s
  · simp [sgnMat, Matrix.conjTranspose_apply, hsym]
  · simp [sgnMat]

/-- Pointwise: the weighted modulus of the initial value is at most the product of the weighted
moduli of the entries of `M` around the cycle. -/
private lemma lgw_init_pw {θ β : ℝ} (hθ : 0 ≤ θ) {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {n : ℕ} (a : Fin n → Fin L) (σ : Fin n → Bool) :
    Real.exp (θ * wordDiam a) * ‖∏ l, sgnMat M (σ l) (a ((finRotate n).symm l)) (a l)‖ ≤
      ∏ l, lgw_g θ M (a ((finRotate n).symm l)) (a l) := by
  have h1 : Real.exp (θ * wordDiam a) ≤
      ∏ l, Real.exp (θ * cycDist (a ((finRotate n).symm l)) (a l)) := by
    rw [← Real.exp_sum, ← Finset.mul_sum]
    apply Real.exp_le_exp.mpr
    have h2 := lgw_diam_cycle a
    have h3 : ∑ l, cycDist (a l) (a (finRotate n l)) =
        ∑ l, cycDist (a ((finRotate n).symm l)) (a l) := by
      have := Equiv.sum_comp (finRotate n) (fun l => cycDist (a ((finRotate n).symm l)) (a l))
      simp only [Equiv.symm_apply_apply] at this
      exact this
    rw [h3] at h2
    have h4 : (wordDiam a : ℝ) ≤ ∑ l, (cycDist (a ((finRotate n).symm l)) (a l) : ℝ) := by
      exact_mod_cast h2
    exact mul_le_mul_of_nonneg_left h4 hθ
  have h5 : ‖∏ l, sgnMat M (σ l) (a ((finRotate n).symm l)) (a l)‖ =
      ∏ l, ‖M (a ((finRotate n).symm l)) (a l)‖ := by
    rw [norm_prod]
    exact Finset.prod_congr rfl fun l _ => lgw_sgn_norm hD _ _ _
  rw [h5]
  calc Real.exp (θ * wordDiam a) * ∏ l, ‖M (a ((finRotate n).symm l)) (a l)‖
      ≤ (∏ l, Real.exp (θ * cycDist (a ((finRotate n).symm l)) (a l))) *
        ∏ l, ‖M (a ((finRotate n).symm l)) (a l)‖ :=
        mul_le_mul_of_nonneg_right h1 (Finset.prod_nonneg fun l _ => norm_nonneg _)
    _ = _ := (Finset.prod_mul_distrib).symm

/-- Initial values, sup bound. -/
private lemma lgw_init_sup {θ β : ℝ} (hθ : 0 ≤ θ) {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {I : ℝ}
    (hMe : ∀ x y, lgw_g θ M x y ≤ I) {n : ℕ} (a : Fin n → Fin L)
    (σ : Fin n → Bool) :
    Real.exp (θ * wordDiam a) * ‖∏ l, sgnMat M (σ l) (a ((finRotate n).symm l)) (a l)‖ ≤
      I ^ n := by
  refine (lgw_init_pw hθ hD a σ).trans ?_
  calc ∏ l, lgw_g θ M (a ((finRotate n).symm l)) (a l) ≤ ∏ _l : Fin n, I :=
        Finset.prod_le_prod₀ (fun l _ => lgw_g_nonneg _ _ _ _) (fun l _ => hMe _ _)
    _ = I ^ n := by simp

/-- Initial values, row bound at a label `j`. -/
private lemma lgw_init_row {θ β : ℝ} (hθ : 0 ≤ θ) (hβ : 0 < β) {M : Matrix (Fin L) (Fin L) ℂ}
    {m : ℂ} (hD : PrimData β M m) {I : ℝ} (hI : 0 ≤ I)
    (hMe : ∀ x y, lgw_g θ M x y ≤ I)
    (hMr : ∀ x y, β * ∑ z, lgw_g θ M x z * lgw_g θ M z y ≤ I ^ 2) {n : ℕ} (hn : 2 ≤ n)
    (j : Fin n) (a : Fin n → Fin L) (σ : Fin n → Bool) :
    β * ∑ c : Fin L, Real.exp (θ * wordDiam (Function.update a j c)) *
      ‖∏ l, sgnMat M (σ l) ((Function.update a j c) ((finRotate n).symm l))
        ((Function.update a j c) l)‖ ≤ I ^ n := by
  obtain ⟨m', rfl⟩ : ∃ m', n = m' + 2 := ⟨n - 2, by omega⟩
  set r := finRotate (m' + 2) j with hr
  have hrj : r ≠ j := by
    intro h
    have := congrArg Fin.val h
    rw [hr, coe_finRotate] at this
    split_ifs at this with hj
    · rw [hj] at this; simp at this
    · simp at this
  have hpj : (finRotate (m' + 2)).symm j ≠ j := by
    intro h
    apply hrj
    have := congrArg (finRotate (m' + 2)) h
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  have hpr : (finRotate (m' + 2)).symm r = j := Equiv.symm_apply_apply _ _
  have hpl : ∀ l, l ≠ r → (finRotate (m' + 2)).symm l ≠ j := by
    intro l hl h
    apply hl
    have := congrArg (finRotate (m' + 2)) h
    rw [Equiv.apply_symm_apply] at this
    exact this
  have hrmem : r ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hrj, Finset.mem_univ r⟩
  have hcard : ((Finset.univ.erase j).erase r).card = m' := by
    rw [Finset.card_erase_of_mem hrmem, Finset.card_erase_of_mem (Finset.mem_univ j)]
    simp
  have hpc : ∀ c : Fin L, Real.exp (θ * wordDiam (Function.update a j c)) *
      ‖∏ l, sgnMat M (σ l) ((Function.update a j c) ((finRotate (m' + 2)).symm l))
        ((Function.update a j c) l)‖ ≤
      I ^ m' * (lgw_g θ M (a ((finRotate (m' + 2)).symm j)) c * lgw_g θ M c (a r)) := by
    intro c
    refine (lgw_init_pw hθ hD _ σ).trans ?_
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
      ← Finset.mul_prod_erase (Finset.univ.erase j) _ hrmem]
    have e1 : lgw_g θ M ((Function.update a j c) ((finRotate (m' + 2)).symm j))
        ((Function.update a j c) j) = lgw_g θ M (a ((finRotate (m' + 2)).symm j)) c := by
      rw [Function.update_of_ne hpj, Function.update_self]
    have e2 : lgw_g θ M ((Function.update a j c) ((finRotate (m' + 2)).symm r))
        ((Function.update a j c) r) = lgw_g θ M c (a r) := by
      rw [hpr, Function.update_self, Function.update_of_ne hrj]
    have e3 : ∏ l ∈ (Finset.univ.erase j).erase r,
        lgw_g θ M ((Function.update a j c) ((finRotate (m' + 2)).symm l))
          ((Function.update a j c) l) =
        ∏ l ∈ (Finset.univ.erase j).erase r,
          lgw_g θ M (a ((finRotate (m' + 2)).symm l)) (a l) := by
      refine Finset.prod_congr rfl fun l hl => ?_
      have hlr : l ≠ r := Finset.ne_of_mem_erase hl
      have hlj : l ≠ j := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hl)
      rw [Function.update_of_ne (hpl l hlr), Function.update_of_ne hlj]
    have e4 : ∏ l ∈ (Finset.univ.erase j).erase r,
        lgw_g θ M (a ((finRotate (m' + 2)).symm l)) (a l) ≤ I ^ m' := by
      calc _ ≤ ∏ _l ∈ (Finset.univ.erase j).erase r, I :=
            Finset.prod_le_prod₀ (fun l _ => lgw_g_nonneg _ _ _ _) (fun l _ => hMe _ _)
        _ = I ^ m' := by rw [Finset.prod_const, hcard]
    rw [e1, e2, e3]
    calc lgw_g θ M (a ((finRotate (m' + 2)).symm j)) c * (lgw_g θ M c (a r) *
          ∏ l ∈ (Finset.univ.erase j).erase r,
            lgw_g θ M (a ((finRotate (m' + 2)).symm l)) (a l))
        ≤ lgw_g θ M (a ((finRotate (m' + 2)).symm j)) c * (lgw_g θ M c (a r) * I ^ m') := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e4
            (lgw_g_nonneg _ _ _ _)) (lgw_g_nonneg _ _ _ _)
      _ = _ := by ring
  calc β * ∑ c : Fin L, Real.exp (θ * wordDiam (Function.update a j c)) *
      ‖∏ l, sgnMat M (σ l) ((Function.update a j c) ((finRotate (m' + 2)).symm l))
        ((Function.update a j c) l)‖
      ≤ β * ∑ c : Fin L, I ^ m' * (lgw_g θ M (a ((finRotate (m' + 2)).symm j)) c *
          lgw_g θ M c (a r)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => hpc c) hβ.le
    _ = I ^ m' * (β * ∑ c, lgw_g θ M (a ((finRotate (m' + 2)).symm j)) c *
          lgw_g θ M c (a r)) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ I ^ m' * I ^ 2 :=
        mul_le_mul_of_nonneg_left (hMr _ _) (by positivity)
    _ = I ^ (m' + 2) := by ring

/-- All lengths `n ≥ 3`: the initial bounds from the entry bounds of `M`. -/
private lemma lgw_init_all {θ β : ℝ} (hθ : 0 ≤ θ) (hβ : 0 < β) {M : Matrix (Fin L) (Fin L) ℂ}
    {m : ℂ} (hD : PrimData β M m)
    (hprod : ∀ (k : ℕ), 1 ≤ k → ∀ (a : Fin k → Fin L) (σ : Fin k → Bool),
      primF β M m 0 a σ = ∏ j, sgnMat M (σ j) (a ((finRotate k).symm j)) (a j))
    {I : ℝ} (hI : 1 ≤ I) (hMe : ∀ x y, lgw_g θ M x y ≤ I)
    (hMr : ∀ x y, β * ∑ z, lgw_g θ M x z * lgw_g θ M z y ≤ I ^ 2) :
    ∀ n, 3 ≤ n → (∀ (a : Fin n → Fin L) (σ : Fin n → Bool),
          Real.exp (θ * wordDiam a) * ‖primF β M m 0 a σ‖ ≤ I ^ n) ∧
        (∀ (j : Fin n) (a : Fin n → Fin L) (σ : Fin n → Bool),
          β * ∑ c : Fin L, Real.exp (θ * wordDiam (Function.update a j c)) *
            ‖primF β M m 0 (Function.update a j c) σ‖ ≤ I ^ n) := by
  intro n hn
  refine ⟨fun a σ => ?_, fun j a σ => ?_⟩
  · rw [hprod n (by omega) a σ]
    exact lgw_init_sup hθ hD hMe a σ
  · simp only [hprod n (by omega) _ σ]
    exact lgw_init_row hθ hβ hD (by linarith) hMe hMr (by omega) j a σ

end Induct

section WeightedRowsW

variable {L : ℕ}

/-- The cyclic distance enters the weights `e^{λ d}` through the triangle inequality. -/
private lemma lgw_exp_tri {lm : ℝ} (hlm : 0 ≤ lm) (a b c : Fin L) :
    Real.exp (lm * cycDist a c) ≤ Real.exp (lm * cycDist a b) * Real.exp (lm * cycDist b c) := by
  rw [← Real.exp_add, ← mul_add]
  apply Real.exp_le_exp.mpr
  have : (cycDist a c : ℝ) ≤ cycDist a b + cycDist b c := by exact_mod_cast lgw_cd_tri a b c
  exact mul_le_mul_of_nonneg_left this hlm


/-- Weighted rows of the propagators. -/
private lemma lgw_U_wrow {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} (hD : PrimData β M m)
    {u t lm CK' : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (ht1 : t < 1) (hCK' : 0 ≤ CK')
    (hK : ∀ (s s' : Bool) (a : Fin L),
      ∑ b, Real.exp (lm * cycDist a b) * ‖pairK β M t s s' a b‖ ≤ CK' / (1 - t))
    (s s' : Bool) (a : Fin L) :
    ∑ b, Real.exp (lm * cycDist a b) * ‖pairU β M u t s s' a b‖ ≤
      (1 + CK') * ((1 - u) / (1 - t)) := by
  have ht0 : 0 ≤ t := hu.trans hut
  have ht : |t| < 1 := abs_lt.mpr ⟨by linarith, ht1⟩
  have h1t : 0 < 1 - t := by linarith
  calc ∑ b, Real.exp (lm * cycDist a b) * ‖pairU β M u t s s' a b‖
      ≤ ∑ b, ((if a = b then (1 : ℝ) else 0) +
          (t - u) * (Real.exp (lm * cycDist a b) * ‖pairK β M t s s' a b‖)) := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [lgw_U_eq' hD ht]
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
        have h2 : ‖(if a = b then (1 : ℂ) else 0) + ((t - u : ℝ) : ℂ) * pairK β M t s s' a b‖ ≤
            (if a = b then (1 : ℝ) else 0) + (t - u) * ‖pairK β M t s s' a b‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · split_ifs <;> simp
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        by_cases hab : a = b
        · subst hab
          simp only [lgw_cd_self, Nat.cast_zero, mul_zero, Real.exp_zero, one_mul,
            ite_true] at h2 ⊢
          exact h2
        · simp only [hab, ite_false, zero_add] at h2 ⊢
          calc Real.exp (lm * cycDist a b) * ‖(((t - u : ℝ) : ℂ) * pairK β M t s s' a b)‖
              ≤ Real.exp (lm * cycDist a b) * ((t - u) * ‖pairK β M t s s' a b‖) :=
                mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
            _ = _ := by ring
    _ = 1 + (t - u) * ∑ b, Real.exp (lm * cycDist a b) * ‖pairK β M t s s' a b‖ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp
    _ ≤ 1 + (t - u) * (CK' / (1 - t)) := by
        have := mul_le_mul_of_nonneg_left (hK s s' a) (by linarith : 0 ≤ t - u)
        linarith
    _ ≤ (1 + CK') * ((1 - u) / (1 - t)) := by
        have h3 : 1 ≤ (1 - u) / (1 - t) := by
          rw [le_div_iff₀ h1t]; linarith
        have h4 : (t - u) / (1 - t) ≤ (1 - u) / (1 - t) :=
          div_le_div_of_nonneg_right (by linarith) h1t.le
        calc 1 + (t - u) * (CK' / (1 - t)) = 1 + CK' * ((t - u) / (1 - t)) := by ring
          _ ≤ 1 * ((1 - u) / (1 - t)) + CK' * ((1 - u) / (1 - t)) := by
              refine add_le_add (by linarith) (mul_le_mul_of_nonneg_left h4 hCK')
          _ = _ := by ring

end WeightedRowsW

/-! ## The two polygons cut off by a diagonal

For a diagonal `(i, j)` of the `k`-gon, the vertices `0, …, i, j, …, k-1` form the polygon of
Cut_L and the vertices `i, …, j` the polygon of Cut_R of (5.6) [fo:eq:cuts]. -/

section Polygon

variable {k : ℕ}

/-- The cyclic offset without `mod`. -/
private lemma lgs_polyOff_eq {n : ℕ} (v w : Fin n) :
    polyOff v w = if v.val ≤ w.val then w.val - v.val else w.val + n - v.val := by
  have := v.isLt
  have := w.isLt
  unfold polyOff
  split_ifs with h
  · rw [show w.val + n - v.val = (w.val - v.val) + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

private lemma lgs_polyOff_cases {n : ℕ} (v w : Fin n) :
    (v.val ≤ w.val ∧ polyOff v w = w.val - v.val) ∨
      (w.val < v.val ∧ polyOff v w = w.val + n - v.val) := by
  rw [lgs_polyOff_eq]
  split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨by omega, rfl⟩

/-- The value of the cyclic successor. -/
private lemma lgs_finRotate_val {n : ℕ} (v : Fin n) :
    (finRotate n v).val = if v.val + 1 = n then 0 else v.val + 1 := by
  rcases n with _ | n
  · exact v.elim0
  · rw [coe_finRotate]
    by_cases h : v = Fin.last n
    · subst h; simp
    · have h' : v.val ≠ n := fun e => h (Fin.ext e)
      simp [h, h']

/-- The vertex map of the polygon of `Cut_{L,i,j}`. -/
private def lgs_vL (i j : Fin k) (p : Fin (k + i - j + 1)) : Fin k :=
  ⟨if p.val ≤ i.val then p.val else p.val + j.val - i.val - 1, by
    have := p.isLt; have := i.isLt; have := j.isLt; split_ifs <;> omega⟩

/-- The vertex map of the polygon of `Cut_{R,i,j}`. -/
private def lgs_vR (i j : Fin k) (q : Fin (j - i + 1)) : Fin k :=
  ⟨i.val + q.val, by have := q.isLt; have := i.isLt; have := j.isLt; omega⟩

private lemma lgs_vL_val (i j : Fin k) (p : Fin (k + i - j + 1)) :
    (lgs_vL i j p).val = if p.val ≤ i.val then p.val else p.val + j.val - i.val - 1 := rfl

private lemma lgs_vR_val (i j : Fin k) (q : Fin (j - i + 1)) :
    (lgs_vR i j q).val = i.val + q.val := rfl

private lemma lgs_vL_cases (i j : Fin k) (p : Fin (k + i - j + 1)) :
    (p.val ≤ i.val ∧ (lgs_vL i j p).val = p.val) ∨
      (i.val < p.val ∧ (lgs_vL i j p).val = p.val + j.val - i.val - 1) := by
  rw [lgs_vL_val]
  split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨by omega, rfl⟩

private lemma lgs_vL_strictMono {i j : Fin k} (hij : i.val < j.val) :
    StrictMono (lgs_vL i j) := by
  intro p p' h
  rw [Fin.lt_def, lgs_vL_val, lgs_vL_val]
  rw [Fin.lt_def] at h
  split_ifs <;> omega

private lemma lgs_vR_strictMono (i j : Fin k) : StrictMono (lgs_vR i j) := by
  intro q q' h
  rw [Fin.lt_def, lgs_vR_val, lgs_vR_val]
  rw [Fin.lt_def] at h
  omega

/-- The inverse of `lgs_vL` on its range. -/
private def lgs_uL (i j : Fin k) (v : Fin k) : Fin (k + i - j + 1) :=
  ⟨if v.val ≤ i.val then v.val else v.val + i.val + 1 - j.val, by
    have := v.isLt; have := i.isLt; have := j.isLt; split_ifs <;> omega⟩

/-- The inverse of `lgs_vR` on its range. -/
private def lgs_uR (i j : Fin k) (v : Fin k) : Fin (j - i + 1) :=
  ⟨if v.val ≤ j.val then v.val - i.val else 0, by split_ifs <;> omega⟩

private lemma lgs_uL_val (i j v : Fin k) :
    (lgs_uL i j v).val = if v.val ≤ i.val then v.val else v.val + i.val + 1 - j.val := rfl

private lemma lgs_uR_val (i j v : Fin k) :
    (lgs_uR i j v).val = if v.val ≤ j.val then v.val - i.val else 0 := rfl

private lemma lgs_vL_uL {i j : Fin k} {v : Fin k}
    (hv : v.val ≤ i.val ∨ j.val ≤ v.val) : lgs_vL i j (lgs_uL i j v) = v := by
  apply Fin.ext
  rw [lgs_vL_val, lgs_uL_val]
  split_ifs <;> omega

private lemma lgs_vR_uR {i j : Fin k} {v : Fin k} (hv : i.val ≤ v.val ∧ v.val ≤ j.val) :
    lgs_vR i j (lgs_uR i j v) = v := by
  apply Fin.ext
  rw [lgs_vR_val, lgs_uR_val]
  split_ifs <;> omega

private lemma lgs_uL_vL {i j : Fin k} (hij : i.val < j.val) (p : Fin (k + i - j + 1)) :
    lgs_uL i j (lgs_vL i j p) = p := by
  have := p.isLt; have := j.isLt
  apply Fin.ext
  rw [lgs_uL_val, lgs_vL_val]
  split_ifs <;> omega

private lemma lgs_uR_vR (i j : Fin k) (q : Fin (j - i + 1)) :
    lgs_uR i j (lgs_vR i j q) = q := by
  have := q.isLt; have := j.isLt
  apply Fin.ext
  rw [lgs_uR_val, lgs_vR_val]
  split_ifs <;> omega

private lemma lgs_vL_inj {i j : Fin k} (hij : i.val < j.val) {p p' : Fin (k + i - j + 1)}
    (h : lgs_vL i j p = lgs_vL i j p') : p = p' :=
  (lgs_vL_strictMono hij).injective h

private lemma lgs_vR_inj {i j : Fin k} {q q' : Fin (j - i + 1)}
    (h : lgs_vR i j q = lgs_vR i j q') : q = q' :=
  (lgs_vR_strictMono i j).injective h

/-- The cyclic order seen from a vertex is preserved by `lgs_vL`. -/
private lemma lgs_off_vL {i j : Fin k} (hij : i.val < j.val) (v w w' : Fin (k + i - j + 1)) :
    polyOff v w < polyOff v w' ↔
      polyOff (lgs_vL i j v) (lgs_vL i j w) < polyOff (lgs_vL i j v) (lgs_vL i j w') := by
  have := v.isLt; have := w.isLt; have := w'.isLt; have := j.isLt
  simp only [lgs_polyOff_eq, lgs_vL_val]
  split_ifs <;> omega

/-- The cyclic order seen from a vertex is preserved by `lgs_vR`. -/
private lemma lgs_off_vR (i j : Fin k) (v w w' : Fin (j - i + 1)) :
    polyOff v w < polyOff v w' ↔
      polyOff (lgs_vR i j v) (lgs_vR i j w) < polyOff (lgs_vR i j v) (lgs_vR i j w') := by
  have := v.isLt; have := w.isLt; have := w'.isLt; have := j.isLt
  simp only [lgs_polyOff_eq, lgs_vR_val, Nat.add_le_add_iff_left]
  split_ifs <;> omega

/-- The labels of Cut_L through the vertex map. -/
private lemma lgs_cutLLab_eq {α : Type*} (a : Fin k → α) (i j : Fin k) (c : α)
    (p : Fin (k + i - j + 1)) :
    cutLLab a i j c p = if p.val = i.val then c else a (lgs_vL i j p) := by
  unfold cutLLab
  split_ifs <;> first | omega | rfl | (congr 1; apply Fin.ext; simp [lgs_vL_val]; omega)

private lemma lgs_cutLSgn_eq (σ : Fin k → Bool) (i j : Fin k) (p : Fin (k + i - j + 1)) :
    cutLSgn σ i j p = σ (lgs_vL i j p) := by
  unfold cutLSgn
  split_ifs with h1 <;> (congr 1; apply Fin.ext; simp [lgs_vL_val, h1])

private lemma lgs_cutRLab_eq {α : Type*} (a : Fin k → α) (i j : Fin k) (c : α)
    (q : Fin (j - i + 1)) :
    cutRLab a i j c q = if q.val = j.val - i.val then c else a (lgs_vR i j q) := by
  have := q.isLt
  unfold cutRLab
  split_ifs with h1 h2 h2 <;> first | omega | rfl

private lemma lgs_cutRSgn_eq (σ : Fin k → Bool) (i j : Fin k) (q : Fin (j - i + 1)) :
    cutRSgn σ i j q = σ (lgs_vR i j q) := rfl

end Polygon

/-! ## Splitting a dissection along a diagonal -/

section Split

variable {k : ℕ}

private lemma lgs_mem_polyDiags {n : ℕ} (e : Fin n × Fin n) :
    e ∈ polyDiags n ↔ e.1.val + 2 ≤ e.2.val ∧ ¬(e.1.val = 0 ∧ e.2.val + 1 = n) := by
  simp [polyDiags, IsPolyDiag]

private lemma lgs_mem_dissections {n : ℕ} (F : Finset (Fin n × Fin n)) :
    F ∈ dissections n ↔ F ⊆ polyDiags n ∧ ∀ d ∈ F, ∀ e ∈ F, ¬DiagCross d e := by
  simp [dissections]

private lemma lgs_diagCross_iff {n : ℕ} (d e : Fin n × Fin n) :
    DiagCross d e ↔ (d.1.val < e.1.val ∧ e.1.val < d.2.val ∧ d.2.val < e.2.val) ∨
      (e.1.val < d.1.val ∧ d.1.val < e.2.val ∧ e.2.val < d.2.val) := by
  unfold DiagCross
  simp only [Fin.lt_def]

private lemma lgs_prod_ne {n : ℕ} {e d : Fin n × Fin n} (h : e ≠ d) :
    ¬(e.1.val = d.1.val ∧ e.2.val = d.2.val) :=
  fun h' => h (Prod.ext (Fin.ext h'.1) (Fin.ext h'.2))

/-- The dissection of the polygon of `Cut_{L,i,j}` induced by `F`. -/
private def lgs_splitL (i j : Fin k) (F : Finset (Fin k × Fin k)) :
    Finset (Fin (k + i - j + 1) × Fin (k + i - j + 1)) :=
  Finset.univ.filter fun e =>
    (lgs_vL i j e.1, lgs_vL i j e.2) ∈ F ∧ (lgs_vL i j e.1, lgs_vL i j e.2) ≠ (i, j)

/-- The dissection of the polygon of `Cut_{R,i,j}` induced by `F`. -/
private def lgs_splitR (i j : Fin k) (F : Finset (Fin k × Fin k)) :
    Finset (Fin (j - i + 1) × Fin (j - i + 1)) :=
  Finset.univ.filter fun e =>
    (lgs_vR i j e.1, lgs_vR i j e.2) ∈ F ∧ (lgs_vR i j e.1, lgs_vR i j e.2) ≠ (i, j)

/-- The dissection of the `k`-gon glued from dissections of the two polygons and `(i, j)`. -/
private def lgs_glue (i j : Fin k) (FL : Finset (Fin (k + i - j + 1) × Fin (k + i - j + 1)))
    (FR : Finset (Fin (j - i + 1) × Fin (j - i + 1))) : Finset (Fin k × Fin k) :=
  insert (i, j) (FL.image (fun e => (lgs_vL i j e.1, lgs_vL i j e.2)) ∪
    FR.image (fun e => (lgs_vR i j e.1, lgs_vR i j e.2)))

private lemma lgs_mem_splitL {i j : Fin k} {F : Finset (Fin k × Fin k)}
    (e : Fin (k + i - j + 1) × Fin (k + i - j + 1)) :
    e ∈ lgs_splitL i j F ↔
      (lgs_vL i j e.1, lgs_vL i j e.2) ∈ F ∧ (lgs_vL i j e.1, lgs_vL i j e.2) ≠ (i, j) := by
  simp [lgs_splitL]

private lemma lgs_mem_splitR {i j : Fin k} {F : Finset (Fin k × Fin k)}
    (e : Fin (j - i + 1) × Fin (j - i + 1)) :
    e ∈ lgs_splitR i j F ↔
      (lgs_vR i j e.1, lgs_vR i j e.2) ∈ F ∧ (lgs_vR i j e.1, lgs_vR i j e.2) ≠ (i, j) := by
  simp [lgs_splitR]

/-- Every other diagonal of a dissection containing `(i, j)` lies on one side of it. -/
private lemma lgs_cover {i j : Fin k} {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k)
    (hd : (i, j) ∈ F) {e : Fin k × Fin k} (he : e ∈ F) (hne : e ≠ (i, j)) :
    ((e.1.val ≤ i.val ∨ j.val ≤ e.1.val) ∧ (e.2.val ≤ i.val ∨ j.val ≤ e.2.val)) ∨
      ((i.val ≤ e.1.val ∧ e.1.val ≤ j.val) ∧ (i.val ≤ e.2.val ∧ e.2.val ≤ j.val)) := by
  rw [lgs_mem_dissections] at hF
  have h0 := (lgs_mem_polyDiags _).mp (hF.1 he)
  have h1 := hF.2 _ hd _ he
  have h2 := hF.2 _ he _ hd
  have h3 := lgs_prod_ne hne
  rw [lgs_diagCross_iff] at h1 h2
  simp only at h1 h2 h3
  omega

private lemma lgs_splitL_mem {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) :
    lgs_splitL i j F ∈ dissections (k + i - j + 1) := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  rw [lgs_mem_dissections] at hF ⊢
  refine ⟨fun e he => ?_, fun d' hd' e he => ?_⟩
  · rw [lgs_mem_splitL] at he
    have h1 := (lgs_mem_polyDiags _).mp (hF.1 he.1)
    have h2 := lgs_prod_ne he.2
    rw [lgs_mem_polyDiags]
    simp only [lgs_vL_val] at h1 h2
    have := e.1.isLt; have := e.2.isLt; have := j.isLt
    split_ifs at h1 h2 <;> omega
  · rw [lgs_mem_splitL] at hd' he
    have h := hF.2 _ hd'.1 _ he.1
    rw [lgs_diagCross_iff] at h ⊢
    simp only [lgs_vL_val] at h
    split_ifs at h <;> omega

private lemma lgs_splitR_mem {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) :
    lgs_splitR i j F ∈ dissections (j - i + 1) := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  rw [lgs_mem_dissections] at hF ⊢
  refine ⟨fun e he => ?_, fun d' hd' e he => ?_⟩
  · rw [lgs_mem_splitR] at he
    have h1 := (lgs_mem_polyDiags _).mp (hF.1 he.1)
    have h2 := lgs_prod_ne he.2
    rw [lgs_mem_polyDiags]
    simp only [lgs_vR_val] at h1 h2
    have := e.1.isLt; have := e.2.isLt; have := j.isLt
    omega
  · rw [lgs_mem_splitR] at hd' he
    have h := hF.2 _ hd'.1 _ he.1
    rw [lgs_diagCross_iff] at h ⊢
    simp only [lgs_vR_val] at h
    omega

private lemma lgs_glue_mem {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {FL : Finset (Fin (k + i - j + 1) × Fin (k + i - j + 1))}
    {FR : Finset (Fin (j - i + 1) × Fin (j - i + 1))}
    (hL : FL ∈ dissections (k + i - j + 1)) (hR : FR ∈ dissections (j - i + 1)) :
    lgs_glue i j FL FR ∈ dissections k := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  have hj := j.isLt
  rw [lgs_mem_dissections] at hL hR ⊢
  refine ⟨fun e he => ?_, fun e he f hf => ?_⟩
  · simp only [lgs_glue, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at he
    rcases he with rfl | ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
    · exact hd
    · have h1 := (lgs_mem_polyDiags _).mp (hL.1 ha)
      have := a.1.isLt; have := a.2.isLt
      rw [lgs_mem_polyDiags]
      simp only [lgs_vL_val]
      split_ifs <;> omega
    · have h1 := (lgs_mem_polyDiags _).mp (hR.1 hb)
      have := b.1.isLt; have := b.2.isLt
      rw [lgs_mem_polyDiags]
      simp only [lgs_vR_val]
      omega
  · simp only [lgs_glue, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at he hf
    rw [lgs_diagCross_iff]
    rcases he with rfl | ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩ <;>
      rcases hf with rfl | ⟨a', ha', rfl⟩ | ⟨b', hb', rfl⟩
    · omega
    · have h1 := (lgs_mem_polyDiags _).mp (hL.1 ha')
      have := a'.1.isLt; have := a'.2.isLt
      simp only [lgs_vL_val]
      split_ifs <;> omega
    · have h1 := (lgs_mem_polyDiags _).mp (hR.1 hb')
      have := b'.1.isLt; have := b'.2.isLt
      simp only [lgs_vR_val]
      omega
    · have h1 := (lgs_mem_polyDiags _).mp (hL.1 ha)
      have := a.1.isLt; have := a.2.isLt
      simp only [lgs_vL_val]
      split_ifs <;> omega
    · have h1 := (lgs_mem_polyDiags _).mp (hL.1 ha)
      have h2 := (lgs_mem_polyDiags _).mp (hL.1 ha')
      have h3 := hL.2 _ ha _ ha'
      rw [lgs_diagCross_iff] at h3
      have := a.1.isLt; have := a.2.isLt; have := a'.1.isLt; have := a'.2.isLt
      simp only [lgs_vL_val]
      split_ifs <;> omega
    · have h1 := (lgs_mem_polyDiags _).mp (hL.1 ha)
      have h2 := (lgs_mem_polyDiags _).mp (hR.1 hb')
      have := a.1.isLt; have := a.2.isLt; have := b'.1.isLt; have := b'.2.isLt
      simp only [lgs_vL_val, lgs_vR_val]
      split_ifs <;> omega
    · have h1 := (lgs_mem_polyDiags _).mp (hR.1 hb)
      have := b.1.isLt; have := b.2.isLt
      simp only [lgs_vR_val]
      omega
    · have h1 := (lgs_mem_polyDiags _).mp (hR.1 hb)
      have h2 := (lgs_mem_polyDiags _).mp (hL.1 ha')
      have := b.1.isLt; have := b.2.isLt; have := a'.1.isLt; have := a'.2.isLt
      simp only [lgs_vL_val, lgs_vR_val]
      split_ifs <;> omega
    · have h1 := (lgs_mem_polyDiags _).mp (hR.1 hb)
      have h2 := (lgs_mem_polyDiags _).mp (hR.1 hb')
      have h3 := hR.2 _ hb _ hb'
      rw [lgs_diagCross_iff] at h3
      have := b.1.isLt; have := b.2.isLt; have := b'.1.isLt; have := b'.2.isLt
      simp only [lgs_vR_val]
      omega

private lemma lgs_glue_split {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F) :
    lgs_glue i j (lgs_splitL i j F) (lgs_splitR i j F) = F := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  ext e
  simp only [lgs_glue, Finset.mem_insert, Finset.mem_union, Finset.mem_image, lgs_mem_splitL,
    lgs_mem_splitR]
  constructor
  · rintro (rfl | ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
    · exact hdF
    · exact ha.1
    · exact hb.1
  · intro he
    by_cases hne : e = (i, j)
    · exact Or.inl hne
    right
    rcases lgs_cover hF hdF he hne with h | h
    · left
      refine ⟨(lgs_uL i j e.1, lgs_uL i j e.2), ?_, ?_⟩ <;>
        simp only [lgs_vL_uL h.1, lgs_vL_uL h.2]
      exact ⟨he, hne⟩
    · right
      refine ⟨(lgs_uR i j e.1, lgs_uR i j e.2), ?_, ?_⟩ <;>
        simp only [lgs_vR_uR h.1, lgs_vR_uR h.2]
      exact ⟨he, hne⟩

private lemma lgs_splitL_glue {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {FL : Finset (Fin (k + i - j + 1) × Fin (k + i - j + 1))}
    {FR : Finset (Fin (j - i + 1) × Fin (j - i + 1))}
    (hL : FL ∈ dissections (k + i - j + 1)) (hR : FR ∈ dissections (j - i + 1)) :
    lgs_splitL i j (lgs_glue i j FL FR) = FL := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  have hj := j.isLt
  rw [lgs_mem_dissections] at hL hR
  ext e
  rw [lgs_mem_splitL]
  simp only [lgs_glue, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨h | ⟨a, ha, he⟩ | ⟨b, hb, he⟩, hne⟩
    · exact absurd h hne
    · have h1 : a = e := by
        have := congrArg Prod.fst he; have := congrArg Prod.snd he
        exact Prod.ext (lgs_vL_inj (by omega) (by assumption))
          (lgs_vL_inj (by omega) (by assumption))
      exact h1 ▸ ha
    · exfalso
      have h1 := (lgs_mem_polyDiags _).mp (hR.1 hb)
      have h2 := lgs_prod_ne hne
      have e1 := congrArg (fun x => x.1.val) he
      have e2 := congrArg (fun x => x.2.val) he
      have := b.1.isLt; have := b.2.isLt; have := e.1.isLt; have := e.2.isLt
      simp only [lgs_vL_val, lgs_vR_val] at e1 e2 h2
      split_ifs at e1 e2 h2 <;> omega
  · intro he
    have h1 := (lgs_mem_polyDiags _).mp (hL.1 he)
    refine ⟨Or.inr (Or.inl ⟨e, he, rfl⟩), fun h => ?_⟩
    have e1 := congrArg (fun x => x.1.val) h
    have e2 := congrArg (fun x => x.2.val) h
    have := e.1.isLt; have := e.2.isLt
    simp only [lgs_vL_val] at e1 e2
    split_ifs at e1 e2 <;> omega

private lemma lgs_splitR_glue {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {FL : Finset (Fin (k + i - j + 1) × Fin (k + i - j + 1))}
    {FR : Finset (Fin (j - i + 1) × Fin (j - i + 1))}
    (hL : FL ∈ dissections (k + i - j + 1)) (hR : FR ∈ dissections (j - i + 1)) :
    lgs_splitR i j (lgs_glue i j FL FR) = FR := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  have hj := j.isLt
  rw [lgs_mem_dissections] at hL hR
  ext e
  rw [lgs_mem_splitR]
  simp only [lgs_glue, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨h | ⟨a, ha, he⟩ | ⟨b, hb, he⟩, hne⟩
    · exact absurd h hne
    · exfalso
      have h1 := (lgs_mem_polyDiags _).mp (hL.1 ha)
      have h2 := lgs_prod_ne hne
      have e1 := congrArg (fun x => x.1.val) he
      have e2 := congrArg (fun x => x.2.val) he
      have := a.1.isLt; have := a.2.isLt; have := e.1.isLt; have := e.2.isLt
      simp only [lgs_vL_val, lgs_vR_val] at e1 e2 h2
      split_ifs at e1 e2 h2 <;> omega
    · have h1 : b = e := by
        have := congrArg Prod.fst he; have := congrArg Prod.snd he
        exact Prod.ext (lgs_vR_inj (by assumption)) (lgs_vR_inj (by assumption))
      exact h1 ▸ hb
  · intro he
    have h1 := (lgs_mem_polyDiags _).mp (hR.1 he)
    refine ⟨Or.inr (Or.inr ⟨e, he, rfl⟩), fun h => ?_⟩
    have e1 := congrArg (fun x => x.1.val) h
    have e2 := congrArg (fun x => x.2.val) h
    have := e.1.isLt; have := e.2.isLt
    simp only [lgs_vR_val] at e1 e2
    omega

/-- Marking the diagonal `(i, j)` in a dissection is a bijection onto the pairs of dissections
of the two polygons of the cut. -/
private lemma lgs_sum_split {i j : Fin k} (hd : (i, j) ∈ polyDiags k) {γ : Type*}
    [AddCommMonoid γ]
    (H : Finset (Fin (k + i - j + 1) × Fin (k + i - j + 1)) →
      Finset (Fin (j - i + 1) × Fin (j - i + 1)) → γ) :
    ∑ F ∈ (dissections k).filter (fun F => (i, j) ∈ F), H (lgs_splitL i j F) (lgs_splitR i j F)
      = ∑ FL ∈ dissections (k + i - j + 1), ∑ FR ∈ dissections (j - i + 1), H FL FR := by
  rw [← Finset.sum_product']
  apply Finset.sum_nbij' (fun F => (lgs_splitL i j F, lgs_splitR i j F))
    (fun p => lgs_glue i j p.1 p.2)
  · intro F hF
    rw [Finset.mem_filter] at hF
    rw [Finset.mem_product]
    exact ⟨lgs_splitL_mem hd hF.1, lgs_splitR_mem hd hF.1⟩
  · intro p hp
    rw [Finset.mem_product] at hp
    rw [Finset.mem_filter]
    exact ⟨lgs_glue_mem hd hp.1 hp.2, Finset.mem_insert_self _ _⟩
  · intro F hF
    rw [Finset.mem_filter] at hF
    exact lgs_glue_split hd hF.1 hF.2
  · intro p hp
    rw [Finset.mem_product] at hp
    exact Prod.ext (lgs_splitL_glue hd hp.1 hp.2) (lgs_splitR_glue hd hp.1 hp.2)
  · intro F _
    rfl

end Split

/-! ## Face corners of the two polygons of a cut -/

section Corners

variable {k : ℕ}

private lemma lgs_minmax {n : ℕ} {v u : Fin n} (h : u ≠ v) :
    ((min v u).val = v.val ∧ (max v u).val = u.val ∧ v.val < u.val) ∨
      ((min v u).val = u.val ∧ (max v u).val = v.val ∧ u.val < v.val) := by
  rcases lt_or_gt_of_ne h with h' | h'
  · right
    rw [min_eq_right h'.le, max_eq_left h'.le]
    exact ⟨rfl, rfl, h'⟩
  · left
    rw [min_eq_left h'.le, max_eq_right h'.le]
    exact ⟨rfl, rfl, h'⟩

private lemma lgs_mem_polyCorners {n : ℕ} (F : Finset (Fin n × Fin n)) (v : Fin n)
    (p : Fin n × Fin n) :
    p ∈ polyCorners F v ↔ PolyNbr F v p.1 ∧ PolyNbr F v p.2 ∧ polyOff v p.1 < polyOff v p.2 ∧
      ∀ u, PolyNbr F v u → ¬(polyOff v p.1 < polyOff v u ∧ polyOff v u < polyOff v p.2) := by
  simp [polyCorners]

/-- Neighbours in a dissection containing `(i, j)` lie on a common side of it. -/
private lemma lgs_nbr_side {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F) {v u : Fin k}
    (h : PolyNbr F v u) :
    ((v.val ≤ i.val ∨ j.val ≤ v.val) ∧ (u.val ≤ i.val ∨ j.val ≤ u.val)) ∨
      ((i.val ≤ v.val ∧ v.val ≤ j.val) ∧ (i.val ≤ u.val ∧ u.val ≤ j.val)) := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  have := v.isLt; have := u.isLt
  obtain ⟨hne, h⟩ := h
  have hmm := lgs_minmax hne
  rcases h with h | h | h
  · rw [lgs_polyOff_eq] at h; split_ifs at h <;> omega
  · rw [lgs_polyOff_eq] at h; split_ifs at h <;> omega
  · by_cases he : (min v u, max v u) = (i, j)
    · have e1 := congrArg (fun x => x.1.val) he
      have e2 := congrArg (fun x => x.2.val) he
      simp only at e1 e2
      omega
    · have := lgs_cover hF hdF h he
      simp only at this
      omega

/-- `lgs_vL` preserves and reflects neighbours. -/
private lemma lgs_nbr_vL {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) (v w : Fin (k + i - j + 1)) :
    PolyNbr F (lgs_vL i j v) (lgs_vL i j w) ↔ PolyNbr (lgs_splitL i j F) v w := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  have hmono := (lgs_vL_strictMono (i := i) (j := j) (by omega)).monotone
  unfold PolyNbr
  rw [← hmono.map_min, ← hmono.map_max, lgs_mem_splitL]
  by_cases hw : w = v
  · subst hw; simp
  have hw' : lgs_vL i j w ≠ lgs_vL i j v := fun h => hw (lgs_vL_inj (by omega) h)
  have hmm := lgs_minmax hw
  have := v.isLt; have := w.isLt; have := j.isLt
  have key : ((lgs_vL i j (min v w), lgs_vL i j (max v w)) = (i, j) →
      (polyOff v w = 1 ∨ polyOff v w + 1 = k + i - j + 1)) ∧
      ((lgs_vL i j (min v w), lgs_vL i j (max v w)) ≠ (i, j) →
        ((polyOff (lgs_vL i j v) (lgs_vL i j w) = 1 ∨
          polyOff (lgs_vL i j v) (lgs_vL i j w) + 1 = k) ↔
        (polyOff v w = 1 ∨ polyOff v w + 1 = k + i - j + 1))) := by
    constructor
    · intro he
      have e1 := congrArg (fun x => x.1.val) he
      have e2 := congrArg (fun x => x.2.val) he
      simp only [lgs_vL_val] at e1 e2
      simp only [lgs_polyOff_eq]
      split_ifs at e1 e2 ⊢ <;> omega
    · intro he
      have he' := lgs_prod_ne he
      simp only [lgs_vL_val] at he'
      simp only [lgs_polyOff_eq, lgs_vL_val]
      split_ifs at he' ⊢ <;> omega
  by_cases hq : (lgs_vL i j (min v w), lgs_vL i j (max v w)) = (i, j)
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

/-- `lgs_vR` preserves and reflects neighbours. -/
private lemma lgs_nbr_vR {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) (v w : Fin (j - i + 1)) :
    PolyNbr F (lgs_vR i j v) (lgs_vR i j w) ↔ PolyNbr (lgs_splitR i j F) v w := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  have hmono := (lgs_vR_strictMono i j).monotone
  unfold PolyNbr
  rw [← hmono.map_min, ← hmono.map_max, lgs_mem_splitR]
  by_cases hw : w = v
  · subst hw; simp
  have hw' : lgs_vR i j w ≠ lgs_vR i j v := fun h => hw (lgs_vR_inj h)
  have hmm := lgs_minmax hw
  have := v.isLt; have := w.isLt; have := j.isLt
  have key : ((lgs_vR i j (min v w), lgs_vR i j (max v w)) = (i, j) →
      (polyOff v w = 1 ∨ polyOff v w + 1 = j - i + 1)) ∧
      ((lgs_vR i j (min v w), lgs_vR i j (max v w)) ≠ (i, j) →
        ((polyOff (lgs_vR i j v) (lgs_vR i j w) = 1 ∨
          polyOff (lgs_vR i j v) (lgs_vR i j w) + 1 = k) ↔
        (polyOff v w = 1 ∨ polyOff v w + 1 = j - i + 1))) := by
    constructor
    · intro he
      have e1 := congrArg (fun x => x.1.val) he
      have e2 := congrArg (fun x => x.2.val) he
      simp only [lgs_vR_val] at e1 e2
      simp only [lgs_polyOff_eq]
      split_ifs <;> omega
    · intro he
      have he' := lgs_prod_ne he
      simp only [lgs_vR_val] at he'
      simp only [lgs_polyOff_eq, lgs_vR_val, Nat.add_le_add_iff_left]
      split_ifs <;> omega
  by_cases hq : (lgs_vR i j (min v w), lgs_vR i j (max v w)) = (i, j)
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
private def lgs_cornerP {n : ℕ} (F : Finset (Fin n × Fin n)) : Finset (Fin n × (Fin n × Fin n)) :=
  Finset.univ.filter fun x => x.2 ∈ polyCorners F x.1

private lemma lgs_prod_corners {n : ℕ} (F : Finset (Fin n × Fin n))
    (f : Fin n → Fin n × Fin n → ℂ) :
    ∏ v, ∏ p ∈ polyCorners F v, f v p = ∏ x ∈ lgs_cornerP F, f x.1 x.2 := by
  rw [lgs_cornerP, Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun v _ => ?_
  dsimp only
  rw [Finset.prod_ite_mem, Finset.univ_inter]

private lemma lgs_nbr_diag {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) : PolyNbr F i j ∧ PolyNbr F j i := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  have hle : i ≤ j := by rw [Fin.le_def]; omega
  have hne : j ≠ i := fun h => by rw [h] at hdv; omega
  refine ⟨⟨hne, Or.inr (Or.inr ?_)⟩, ⟨hne.symm, Or.inr (Or.inr ?_)⟩⟩
  · rwa [min_eq_left hle, max_eq_right hle]
  · rwa [min_eq_right hle, max_eq_left hle]

private lemma lgs_corner_toL {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) {v w w' : Fin k}
    (hv : v.val ≤ i.val ∨ j.val ≤ v.val) (hw : w.val ≤ i.val ∨ j.val ≤ w.val)
    (hw' : w'.val ≤ i.val ∨ j.val ≤ w'.val) (h : (w, w') ∈ polyCorners F v) :
    (lgs_uL i j w, lgs_uL i j w') ∈ polyCorners (lgs_splitL i j F) (lgs_uL i j v) := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  rw [← lgs_vL_uL hv, ← lgs_vL_uL hw, ← lgs_vL_uL hw'] at h
  rw [lgs_mem_polyCorners] at h ⊢
  dsimp only at h ⊢
  obtain ⟨n1, n2, o, nb⟩ := h
  refine ⟨(lgs_nbr_vL hd hdF _ _).mp n1, (lgs_nbr_vL hd hdF _ _).mp n2,
    (lgs_off_vL hij _ _ _).mpr o, fun u hu => ?_⟩
  rw [lgs_off_vL hij _ _ u, lgs_off_vL hij _ u _]
  exact nb _ ((lgs_nbr_vL hd hdF _ _).mpr hu)

private lemma lgs_corner_toR {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) {v w w' : Fin k}
    (hv : i.val ≤ v.val ∧ v.val ≤ j.val) (hw : i.val ≤ w.val ∧ w.val ≤ j.val)
    (hw' : i.val ≤ w'.val ∧ w'.val ≤ j.val) (h : (w, w') ∈ polyCorners F v) :
    (lgs_uR i j w, lgs_uR i j w') ∈ polyCorners (lgs_splitR i j F) (lgs_uR i j v) := by
  rw [← lgs_vR_uR hv, ← lgs_vR_uR hw, ← lgs_vR_uR hw'] at h
  rw [lgs_mem_polyCorners] at h ⊢
  dsimp only at h ⊢
  obtain ⟨n1, n2, o, nb⟩ := h
  refine ⟨(lgs_nbr_vR hd hdF _ _).mp n1, (lgs_nbr_vR hd hdF _ _).mp n2,
    (lgs_off_vR i j _ _ _).mpr o, fun u hu => ?_⟩
  rw [lgs_off_vR i j _ _ u, lgs_off_vR i j _ u _]
  exact nb _ ((lgs_nbr_vR hd hdF _ _).mpr hu)

private lemma lgs_corner_fromL {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F)
    {v w w' : Fin (k + i - j + 1)} (h : (w, w') ∈ polyCorners (lgs_splitL i j F) v) :
    (lgs_vL i j w, lgs_vL i j w') ∈ polyCorners F (lgs_vL i j v) := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  rw [lgs_mem_polyCorners] at h ⊢
  dsimp only at h ⊢
  obtain ⟨n1, n2, o, nb⟩ := h
  refine ⟨(lgs_nbr_vL hd hdF _ _).mpr n1, (lgs_nbr_vL hd hdF _ _).mpr n2,
    (lgs_off_vL hij _ _ _).mp o, fun u hu => ?_⟩
  by_cases huL : u.val ≤ i.val ∨ j.val ≤ u.val
  · rw [← lgs_vL_uL huL] at hu ⊢
    rw [← lgs_off_vL hij, ← lgs_off_vL hij]
    exact nb _ ((lgs_nbr_vL hd hdF _ _).mp hu)
  · have hs := lgs_nbr_side hd hF hdF hu
    have h1 : w ≠ v := n1.1
    have h2 : w' ≠ v := n2.1
    have h1' : w.val ≠ v.val := fun e => h1 (Fin.ext e)
    have h2' : w'.val ≠ v.val := fun e => h2 (Fin.ext e)
    have := v.isLt; have := w.isLt; have := w'.isLt; have := u.isLt
    simp only [lgs_vL_val] at hs
    simp only [lgs_polyOff_eq, lgs_vL_val]
    split_ifs at hs ⊢ <;> omega

private lemma lgs_corner_fromR {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F)
    {v w w' : Fin (j - i + 1)} (h : (w, w') ∈ polyCorners (lgs_splitR i j F) v) :
    (lgs_vR i j w, lgs_vR i j w') ∈ polyCorners F (lgs_vR i j v) := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  rw [lgs_mem_polyCorners] at h ⊢
  dsimp only at h ⊢
  obtain ⟨n1, n2, o, nb⟩ := h
  refine ⟨(lgs_nbr_vR hd hdF _ _).mpr n1, (lgs_nbr_vR hd hdF _ _).mpr n2,
    (lgs_off_vR i j _ _ _).mp o, fun u hu => ?_⟩
  by_cases huR : i.val ≤ u.val ∧ u.val ≤ j.val
  · rw [← lgs_vR_uR huR] at hu ⊢
    rw [← lgs_off_vR, ← lgs_off_vR]
    exact nb _ ((lgs_nbr_vR hd hdF _ _).mp hu)
  · have hs := lgs_nbr_side hd hF hdF hu
    have h1 : w ≠ v := n1.1
    have h2 : w' ≠ v := n2.1
    have h1' : w.val ≠ v.val := fun e => h1 (Fin.ext e)
    have h2' : w'.val ≠ v.val := fun e => h2 (Fin.ext e)
    have := v.isLt; have := w.isLt; have := w'.isLt; have := u.isLt; have := j.isLt
    simp only [lgs_vR_val] at hs
    have c1 := lgs_polyOff_cases (lgs_vR i j v) (lgs_vR i j w)
    have c2 := lgs_polyOff_cases (lgs_vR i j v) u
    have c3 := lgs_polyOff_cases (lgs_vR i j v) (lgs_vR i j w')
    simp only [lgs_vR_val] at c1 c2 c3
    omega

/-- Every face corner lies in one of the two polygons of the cut. -/
private lemma lgs_corner_sides {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F) {v w w' : Fin k}
    (h : (w, w') ∈ polyCorners F v) :
    ((v.val ≤ i.val ∨ j.val ≤ v.val) ∧ (w.val ≤ i.val ∨ j.val ≤ w.val) ∧
        (w'.val ≤ i.val ∨ j.val ≤ w'.val)) ∨
      ((i.val ≤ v.val ∧ v.val ≤ j.val) ∧ (i.val ≤ w.val ∧ w.val ≤ j.val) ∧
        (i.val ≤ w'.val ∧ w'.val ≤ j.val)) := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  rw [lgs_mem_polyCorners] at h
  dsimp only at h
  obtain ⟨n1, n2, o, nb⟩ := h
  have s1 := lgs_nbr_side hd hF hdF n1
  have s2 := lgs_nbr_side hd hF hdF n2
  have h1' : w.val ≠ v.val := fun e => n1.1 (Fin.ext e)
  have h2' : w'.val ≠ v.val := fun e => n2.1 (Fin.ext e)
  have := v.isLt; have := w.isLt; have := w'.isLt; have := j.isLt
  by_cases hvi : v = i
  · subst hvi
    have hb := nb j (lgs_nbr_diag hd hdF).1
    have c1 := lgs_polyOff_cases v w
    have c2 := lgs_polyOff_cases v w'
    have c3 := lgs_polyOff_cases v j
    omega
  by_cases hvj : v = j
  · subst hvj
    have hb := nb i (lgs_nbr_diag hd hdF).2
    have c1 := lgs_polyOff_cases v w
    have c2 := lgs_polyOff_cases v w'
    have c3 := lgs_polyOff_cases v i
    omega
  have hvi' : v.val ≠ i.val := fun e => hvi (Fin.ext e)
  have hvj' : v.val ≠ j.val := fun e => hvj (Fin.ext e)
  omega

/-- The face corners of `F` are those of the two polygons of the cut, transported by the vertex
maps. -/
private lemma lgs_prod_cornerP_split {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F)
    (g : Fin k × (Fin k × Fin k) → ℂ) :
    ∏ x ∈ lgs_cornerP F, g x =
      (∏ x ∈ lgs_cornerP (lgs_splitL i j F),
        g (lgs_vL i j x.1, (lgs_vL i j x.2.1, lgs_vL i j x.2.2))) *
      ∏ x ∈ lgs_cornerP (lgs_splitR i j F),
        g (lgs_vR i j x.1, (lgs_vR i j x.2.1, lgs_vR i j x.2.2)) := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  set ψL : Fin (k + i - j + 1) × (Fin (k + i - j + 1) × Fin (k + i - j + 1)) →
      Fin k × (Fin k × Fin k) := fun x => (lgs_vL i j x.1, (lgs_vL i j x.2.1, lgs_vL i j x.2.2))
  set ψR : Fin (j - i + 1) × (Fin (j - i + 1) × Fin (j - i + 1)) →
      Fin k × (Fin k × Fin k) := fun x => (lgs_vR i j x.1, (lgs_vR i j x.2.1, lgs_vR i j x.2.2))
  have hS : lgs_cornerP F = (lgs_cornerP (lgs_splitL i j F)).image ψL ∪
      (lgs_cornerP (lgs_splitR i j F)).image ψR := by
    ext ⟨v, w, w'⟩
    simp only [lgs_cornerP, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro h
      rcases lgs_corner_sides hd hF hdF h with ⟨hv, hw, hw'⟩ | ⟨hv, hw, hw'⟩
      · left
        refine ⟨(lgs_uL i j v, (lgs_uL i j w, lgs_uL i j w')),
          lgs_corner_toL hd hdF hv hw hw' h, ?_⟩
        simp only [ψL, lgs_vL_uL hv, lgs_vL_uL hw, lgs_vL_uL hw']
      · right
        refine ⟨(lgs_uR i j v, (lgs_uR i j w, lgs_uR i j w')),
          lgs_corner_toR hd hdF hv hw hw' h, ?_⟩
        simp only [ψR, lgs_vR_uR hv, lgs_vR_uR hw, lgs_vR_uR hw']
    · rintro (⟨x, hx, hxe⟩ | ⟨x, hx, hxe⟩)
      · simp only [ψL, Prod.mk.injEq] at hxe
        obtain ⟨rfl, rfl, rfl⟩ := hxe
        exact lgs_corner_fromL hd hF hdF hx
      · simp only [ψR, Prod.mk.injEq] at hxe
        obtain ⟨rfl, rfl, rfl⟩ := hxe
        exact lgs_corner_fromR hd hF hdF hx
  have hinjL : Set.InjOn ψL (lgs_cornerP (lgs_splitL i j F)) := by
    intro x _ y _ hxy
    simp only [ψL, Prod.mk.injEq] at hxy
    exact Prod.ext (lgs_vL_inj hij hxy.1)
      (Prod.ext (lgs_vL_inj hij hxy.2.1) (lgs_vL_inj hij hxy.2.2))
  have hinjR : Set.InjOn ψR (lgs_cornerP (lgs_splitR i j F)) := by
    intro x _ y _ hxy
    simp only [ψR, Prod.mk.injEq] at hxy
    exact Prod.ext (lgs_vR_inj hxy.1) (Prod.ext (lgs_vR_inj hxy.2.1) (lgs_vR_inj hxy.2.2))
  have hdisj : Disjoint ((lgs_cornerP (lgs_splitL i j F)).image ψL)
      ((lgs_cornerP (lgs_splitR i j F)).image ψR) := by
    rw [Finset.disjoint_left]
    rintro z hzL hzR
    simp only [Finset.mem_image, lgs_cornerP, Finset.mem_filter, Finset.mem_univ,
      true_and] at hzL hzR
    obtain ⟨x, hx, rfl⟩ := hzL
    obtain ⟨y, hy, hxy⟩ := hzR
    simp only [ψL, ψR, Prod.mk.injEq] at hxy
    obtain ⟨e1, e2, e3⟩ := hxy
    rw [lgs_mem_polyCorners] at hx
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
    simp only [lgs_vL_val, lgs_vR_val] at f1 f2 f3
    split_ifs at f1 f2 f3 <;> omega
  rw [hS, Finset.prod_union hdisj, Finset.prod_image hinjL, Finset.prod_image hinjR]


private lemma lgs_corner_conds {n : ℕ} {F : Finset (Fin n × Fin n)} {v : Fin n}
    {p : Fin n × Fin n} (h : p ∈ polyCorners F v) :
    PolyNbr F v p.1 ∧ PolyNbr F v p.2 ∧ polyOff v p.1 + 1 ≠ n ∧ polyOff v p.2 ≠ 1 := by
  rw [lgs_mem_polyCorners] at h
  obtain ⟨n1, n2, o, -⟩ := h
  have h1 : p.1.val ≠ v.val := fun e => n1.1 (Fin.ext e)
  have h2 : p.2.val ≠ v.val := fun e => n2.1 (Fin.ext e)
  have c1 := lgs_polyOff_cases v p.1
  have c2 := lgs_polyOff_cases v p.2
  have := v.isLt; have := p.1.isLt; have := p.2.isLt
  exact ⟨n1, n2, by omega, by omega⟩

/-- The diagonals of the polygon of Cut_L as diagonals of `F`. -/
private def lgs_ιL (i j : Fin k) (F : Finset (Fin k × Fin k)) (e : ↥(lgs_splitL i j F)) : ↥F :=
  ⟨(lgs_vL i j e.1.1, lgs_vL i j e.1.2), ((lgs_mem_splitL _).mp e.2).1⟩

/-- The diagonals of the polygon of Cut_R as diagonals of `F`. -/
private def lgs_ιR (i j : Fin k) (F : Finset (Fin k × Fin k)) (e : ↥(lgs_splitR i j F)) : ↥F :=
  ⟨(lgs_vR i j e.1.1, lgs_vR i j e.1.2), ((lgs_mem_splitR _).mp e.2).1⟩

/-- The edge labels of the polygon of Cut_L: the side `i` carries the outer copy of the
label of `(i, j)`. -/
private lemma lgs_edgeLab_L {L : ℕ} {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) (y : Fin k → Fin L) (cIn cOut : ↥F → Fin L)
    {v w : Fin (k + i - j + 1)} (hn : PolyNbr (lgs_splitL i j F) v w) (small : Bool)
    (hs : if small then polyOff v w ≠ 1 else polyOff v w + 1 ≠ k + i - j + 1) :
    edgeLab (lgs_splitL i j F)
        (fun p => if p.val = i.val then cOut ⟨(i, j), hdF⟩ else y (lgs_vL i j p))
        (fun e => cIn (lgs_ιL i j F e)) (fun e => cOut (lgs_ιL i j F e)) v w small =
      edgeLab F y cIn cOut (lgs_vL i j v) (lgs_vL i j w) small := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  have hsm := lgs_vL_strictMono (i := i) (j := j) hij
  have hmono := hsm.monotone
  simp only [edgeLab, ← hmono.map_min, ← hmono.map_max]
  obtain ⟨hne, hside⟩ := hn
  have hmm := lgs_minmax hne
  have cv := lgs_vL_cases i j v
  have cw := lgs_vL_cases i j w
  have co := lgs_polyOff_cases v w
  have co' := lgs_polyOff_cases (lgs_vL i j v) (lgs_vL i j w)
  have := v.isLt; have := w.isLt; have := j.isLt
  have hlt : decide (v < w) = decide (lgs_vL i j v < lgs_vL i j w) := by
    simp only [hsm.lt_iff_lt]
  by_cases h' : (min v w, max v w) ∈ lgs_splitL i j F
  · have h1 : (lgs_vL i j (min v w), lgs_vL i j (max v w)) ∈ F :=
      ((lgs_mem_splitL _).mp h').1
    rw [dite_eq_left h', dite_eq_left h1, hlt]
    rfl
  · rw [dite_eq_right h']
    have hside' : polyOff v w = 1 ∨ polyOff v w + 1 = k + i - j + 1 := by
      rcases hside with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h h'
    by_cases hq : (lgs_vL i j (min v w), lgs_vL i j (max v w)) = (i, j)
    · have h1 : (lgs_vL i j (min v w), lgs_vL i j (max v w)) ∈ F := hq ▸ hdF
      rw [dite_eq_left h1]
      have e1 := congrArg (fun x => x.1.val) hq
      have e2 := congrArg (fun x => x.2.val) hq
      have cmin := lgs_vL_cases i j (min v w)
      have cmax := lgs_vL_cases i j (max v w)
      simp only at e1 e2
      have hsub : (⟨(lgs_vL i j (min v w), lgs_vL i j (max v w)), h1⟩ : ↥F) = ⟨(i, j), hdF⟩ :=
        Subtype.ext hq
      cases small
      · simp only [Bool.false_eq_true, ite_false] at hs
        have hv : v.val = i.val := by omega
        have hw : ¬ lgs_vL i j v < lgs_vL i j w → False := by
          intro h; rw [Fin.lt_def] at h; omega
        have hpos : polyOff v w = 1 := by omega
        rw [ite_eq_left hpos, ite_eq_left hv, hsub]
        have : decide (lgs_vL i j v < lgs_vL i j w) = true := by
          by_contra hc; exact hw (by simpa using hc)
        rw [this]
        rfl
      · simp only [ite_true] at hs
        have hw : w.val = i.val := by omega
        have hv : ¬ lgs_vL i j v < lgs_vL i j w := by
          rw [Fin.lt_def]; omega
        rw [ite_eq_right hs, ite_eq_left hw, hsub]
        simp [hv]
    · have h1 : (lgs_vL i j (min v w), lgs_vL i j (max v w)) ∉ F :=
        fun h => h' ((lgs_mem_splitL _).mpr ⟨h, hq⟩)
      rw [dite_eq_right h1]
      clear hmm
      by_cases h1 : polyOff v w = 1
      · have h2 : polyOff (lgs_vL i j v) (lgs_vL i j w) = 1 := by
          have hq' := lgs_prod_ne hq
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
          have hmm := lgs_minmax hne
          have hq' := lgs_prod_ne hq
          have cmin := lgs_vL_cases i j (min v w)
          have cmax := lgs_vL_cases i j (max v w)
          simp only at hq'
          omega
        rw [ite_eq_left h1, ite_eq_left h2, ite_eq_right h3]
      · have h2 : polyOff (lgs_vL i j v) (lgs_vL i j w) ≠ 1 := by omega
        have h3 : w.val ≠ i.val := by
          clear co'
          have hmm := lgs_minmax hne
          have hq' := lgs_prod_ne hq
          have cmin := lgs_vL_cases i j (min v w)
          have cmax := lgs_vL_cases i j (max v w)
          simp only at hq'
          omega
        rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]

/-- The edge labels of the polygon of Cut_R: the last side carries the inner copy of the
label of `(i, j)`. -/
private lemma lgs_edgeLab_R {L : ℕ} {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) (y : Fin k → Fin L) (cIn cOut : ↥F → Fin L)
    {v w : Fin (j - i + 1)} (hn : PolyNbr (lgs_splitR i j F) v w) (small : Bool)
    (hs : if small then polyOff v w ≠ 1 else polyOff v w + 1 ≠ j - i + 1) :
    edgeLab (lgs_splitR i j F)
        (fun q => if q.val = j.val - i.val then cIn ⟨(i, j), hdF⟩ else y (lgs_vR i j q))
        (fun e => cIn (lgs_ιR i j F e)) (fun e => cOut (lgs_ιR i j F e)) v w small =
      edgeLab F y cIn cOut (lgs_vR i j v) (lgs_vR i j w) small := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  have hsm := lgs_vR_strictMono i j
  have hmono := hsm.monotone
  simp only [edgeLab, ← hmono.map_min, ← hmono.map_max]
  obtain ⟨hne, hside⟩ := hn
  have hmm := lgs_minmax hne
  have cv := lgs_vR_val i j v
  have cw := lgs_vR_val i j w
  have co := lgs_polyOff_cases v w
  have co' := lgs_polyOff_cases (lgs_vR i j v) (lgs_vR i j w)
  have := v.isLt; have := w.isLt; have := j.isLt
  have hlt : decide (v < w) = decide (lgs_vR i j v < lgs_vR i j w) := by
    simp only [hsm.lt_iff_lt]
  by_cases h' : (min v w, max v w) ∈ lgs_splitR i j F
  · have h1 : (lgs_vR i j (min v w), lgs_vR i j (max v w)) ∈ F :=
      ((lgs_mem_splitR _).mp h').1
    rw [dite_eq_left h', dite_eq_left h1, hlt]
    rfl
  · rw [dite_eq_right h']
    have hside' : polyOff v w = 1 ∨ polyOff v w + 1 = j - i + 1 := by
      rcases hside with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h h'
    by_cases hq : (lgs_vR i j (min v w), lgs_vR i j (max v w)) = (i, j)
    · have h1 : (lgs_vR i j (min v w), lgs_vR i j (max v w)) ∈ F := hq ▸ hdF
      rw [dite_eq_left h1]
      have e1 := congrArg (fun x => x.1.val) hq
      have e2 := congrArg (fun x => x.2.val) hq
      have cmin := lgs_vR_val i j (min v w)
      have cmax := lgs_vR_val i j (max v w)
      simp only at e1 e2
      have hsub : (⟨(lgs_vR i j (min v w), lgs_vR i j (max v w)), h1⟩ : ↥F) = ⟨(i, j), hdF⟩ :=
        Subtype.ext hq
      cases small
      · simp only [Bool.false_eq_true, ite_false] at hs
        have hv : v.val = j.val - i.val := by omega
        have hw : ¬ lgs_vR i j v < lgs_vR i j w := by
          rw [Fin.lt_def]; omega
        have hpos : polyOff v w = 1 := by omega
        rw [ite_eq_left hpos, ite_eq_left hv, hsub]
        simp [hw]
      · simp only [ite_true] at hs
        have hw : w.val = j.val - i.val := by omega
        have hv : lgs_vR i j v < lgs_vR i j w := by
          rw [Fin.lt_def]; omega
        rw [ite_eq_right hs, ite_eq_left hw, hsub]
        simp [hv]
    · have h1 : (lgs_vR i j (min v w), lgs_vR i j (max v w)) ∉ F :=
        fun h => h' ((lgs_mem_splitR _).mpr ⟨h, hq⟩)
      rw [dite_eq_right h1]
      clear hmm
      by_cases h1 : polyOff v w = 1
      · have h2 : polyOff (lgs_vR i j v) (lgs_vR i j w) = 1 := by
          have hq' := lgs_prod_ne hq
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
          have hmm := lgs_minmax hne
          have hq' := lgs_prod_ne hq
          have cmin := lgs_vR_val i j (min v w)
          have cmax := lgs_vR_val i j (max v w)
          simp only at hq'
          omega
        rw [ite_eq_left h1, ite_eq_left h2, ite_eq_right h3]
      · have h2 : polyOff (lgs_vR i j v) (lgs_vR i j w) ≠ 1 := by omega
        have h3 : w.val ≠ j.val - i.val := by
          clear co'
          have hmm := lgs_minmax hne
          have hq' := lgs_prod_ne hq
          have cmin := lgs_vR_val i j (min v w)
          have cmax := lgs_vR_val i j (max v w)
          simp only at hq'
          omega
        rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]


/-- The corner product of `F` splits into the corner products of the two polygons of the cut,
with the outer copy of the label of `(i, j)` on the side `i` of Cut_L and its inner copy on
the last side of Cut_R. -/
private lemma lgs_corners_split {L : ℕ} {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F)
    (M : Matrix (Fin L) (Fin L) ℂ) (σ : Fin k → Bool) (y : Fin k → Fin L)
    (cIn cOut : ↥F → Fin L) :
    (∏ v : Fin k, ∏ p ∈ polyCorners F v,
        sgnMat M (σ v) (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false)) =
      (∏ v : Fin (k + i - j + 1), ∏ p ∈ polyCorners (lgs_splitL i j F) v,
        sgnMat M (cutLSgn σ i j v)
          (edgeLab (lgs_splitL i j F)
            (fun p => if p.val = i.val then cOut ⟨(i, j), hdF⟩ else y (lgs_vL i j p))
            (fun e => cIn (lgs_ιL i j F e)) (fun e => cOut (lgs_ιL i j F e)) v p.2 true)
          (edgeLab (lgs_splitL i j F)
            (fun p => if p.val = i.val then cOut ⟨(i, j), hdF⟩ else y (lgs_vL i j p))
            (fun e => cIn (lgs_ιL i j F e)) (fun e => cOut (lgs_ιL i j F e)) v p.1 false)) *
      (∏ v : Fin (j - i + 1), ∏ p ∈ polyCorners (lgs_splitR i j F) v,
        sgnMat M (cutRSgn σ i j v)
          (edgeLab (lgs_splitR i j F)
            (fun q => if q.val = j.val - i.val then cIn ⟨(i, j), hdF⟩ else y (lgs_vR i j q))
            (fun e => cIn (lgs_ιR i j F e)) (fun e => cOut (lgs_ιR i j F e)) v p.2 true)
          (edgeLab (lgs_splitR i j F)
            (fun q => if q.val = j.val - i.val then cIn ⟨(i, j), hdF⟩ else y (lgs_vR i j q))
            (fun e => cIn (lgs_ιR i j F e)) (fun e => cOut (lgs_ιR i j F e)) v p.1 false)) := by
  rw [lgs_prod_corners, lgs_prod_corners, lgs_prod_corners,
    lgs_prod_cornerP_split hd hF hdF]
  congr 1
  · refine Finset.prod_congr rfl fun x hx => ?_
    simp only [lgs_cornerP, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨n1, n2, c1, c2⟩ := lgs_corner_conds hx
    rw [lgs_cutLSgn_eq, lgs_edgeLab_L hd hdF y cIn cOut n2 true (by simpa using c2),
      lgs_edgeLab_L hd hdF y cIn cOut n1 false (by simpa using c1)]
  · refine Finset.prod_congr rfl fun x hx => ?_
    simp only [lgs_cornerP, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨n1, n2, c1, c2⟩ := lgs_corner_conds hx
    rw [lgs_cutRSgn_eq, lgs_edgeLab_R hd hdF y cIn cOut n2 true (by simpa using c2),
      lgs_edgeLab_R hd hdF y cIn cOut n1 false (by simpa using c1)]

end Corners

/-! ## The core of a dissection with one link differentiated -/

section Glue

variable {k L : ℕ}

private lemma lgs_sum_pair {T Y : Type*} [Fintype T] [DecidableEq T] [Fintype Y]
    (G : (T → Y) → (T → Y) → ℂ) :
    ∑ cIn : T → Y, ∑ cOut : T → Y, G cIn cOut =
      ∑ c : T → Y × Y, G (fun t => (c t).1) (fun t => (c t).2) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow T (fun _ => Y) (fun _ => Y)) _ _
    (fun c => rfl)).symm

private lemma lgs_sum_option {A B T X : Type} [Fintype A] [Fintype B] [Fintype T]
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
private def lgs_eqvFun (i j : Fin k) (F : Finset (Fin k × Fin k)) (hdF : (i, j) ∈ F) :
    Option (↥(lgs_splitL i j F) ⊕ ↥(lgs_splitR i j F)) → ↥F
  | none => ⟨(i, j), hdF⟩
  | some (Sum.inl a) => lgs_ιL i j F a
  | some (Sum.inr b) => lgs_ιR i j F b

private lemma lgs_eqvFun_bij {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F) :
    Function.Bijective (lgs_eqvFun i j F hdF) := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  have hFL := lgs_splitL_mem hd hF
  have hFR := lgs_splitR_mem hd hF
  rw [lgs_mem_dissections] at hFL hFR
  have hj := j.isLt
  constructor
  · intro o o' h
    rcases o with _ | a | b <;> rcases o' with _ | a' | b'
    · rfl
    · exfalso
      have := ((lgs_mem_splitL _).mp a'.2).2
      exact this (congrArg Subtype.val h).symm
    · exfalso
      have := ((lgs_mem_splitR _).mp b'.2).2
      exact this (congrArg Subtype.val h).symm
    · exfalso
      have := ((lgs_mem_splitL _).mp a.2).2
      exact this (congrArg Subtype.val h)
    · have h1 := congrArg Subtype.val h
      simp only [lgs_eqvFun, lgs_ιL, Prod.mk.injEq] at h1
      have e1 := lgs_vL_inj hij h1.1
      have e2 := lgs_vL_inj hij h1.2
      rw [Subtype.ext (Prod.ext e1 e2)]
    · exfalso
      have h1 := congrArg Subtype.val h
      simp only [lgs_eqvFun, lgs_ιL, lgs_ιR, Prod.mk.injEq] at h1
      have ha := (lgs_mem_polyDiags _).mp (hFL.1 a.2)
      have f1 := congrArg Fin.val h1.1
      have f2 := congrArg Fin.val h1.2
      have ca1 := lgs_vL_cases i j a.1.1
      have ca2 := lgs_vL_cases i j a.1.2
      have hne := lgs_prod_ne ((lgs_mem_splitL _).mp a.2).2
      simp only [lgs_vR_val] at f1 f2
      simp only at hne
      have := a.1.1.isLt; have := a.1.2.isLt; have := b'.1.1.isLt; have := b'.1.2.isLt
      omega
    · exfalso
      have := ((lgs_mem_splitR _).mp b.2).2
      exact this (congrArg Subtype.val h)
    · exfalso
      have h1 := congrArg Subtype.val h
      simp only [lgs_eqvFun, lgs_ιL, lgs_ιR, Prod.mk.injEq] at h1
      have ha := (lgs_mem_polyDiags _).mp (hFL.1 a'.2)
      have f1 := congrArg Fin.val h1.1
      have f2 := congrArg Fin.val h1.2
      have ca1 := lgs_vL_cases i j a'.1.1
      have ca2 := lgs_vL_cases i j a'.1.2
      have hne := lgs_prod_ne ((lgs_mem_splitL _).mp a'.2).2
      simp only [lgs_vR_val] at f1 f2
      simp only at hne
      have := a'.1.1.isLt; have := a'.1.2.isLt; have := b.1.1.isLt; have := b.1.2.isLt
      omega
    · have h1 := congrArg Subtype.val h
      simp only [lgs_eqvFun, lgs_ιR, Prod.mk.injEq] at h1
      have e1 := lgs_vR_inj h1.1
      have e2 := lgs_vR_inj h1.2
      rw [Subtype.ext (Prod.ext e1 e2)]
  · intro e
    by_cases he : e.1 = (i, j)
    · exact ⟨none, Subtype.ext he.symm⟩
    rcases lgs_cover hF hdF e.2 he with h | h
    · refine ⟨some (Sum.inl ⟨(lgs_uL i j e.1.1, lgs_uL i j e.1.2), ?_⟩), ?_⟩
      · rw [lgs_mem_splitL]
        simp only [lgs_vL_uL h.1, lgs_vL_uL h.2]
        exact ⟨e.2, he⟩
      · apply Subtype.ext
        simp only [lgs_eqvFun, lgs_ιL, lgs_vL_uL h.1, lgs_vL_uL h.2]
    · refine ⟨some (Sum.inr ⟨(lgs_uR i j e.1.1, lgs_uR i j e.1.2), ?_⟩), ?_⟩
      · rw [lgs_mem_splitR]
        simp only [lgs_vR_uR h.1, lgs_vR_uR h.2]
        exact ⟨e.2, he⟩
      · apply Subtype.ext
        simp only [lgs_eqvFun, lgs_ιR, lgs_vR_uR h.1, lgs_vR_uR h.2]

/-- The core of `F` in which the link of the diagonal `d` is replaced by the matrix `X`. -/
private def lgs_coreX (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) (σ : Fin k → Bool)
    (F : Finset (Fin k × Fin k)) (d : Fin k × Fin k) (X : Matrix (Fin L) (Fin L) ℂ)
    (y : Fin k → Fin L) : ℂ :=
  ∑ cIn : ↥F → Fin L, ∑ cOut : ↥F → Fin L,
    (∏ e : ↥F, if e.1 = d then X (cOut e) (cIn e)
      else ((β * t : ℝ) : ℂ) * pairV β M t (σ e.1.1) (σ e.1.2) (cOut e) (cIn e)) *
      ∏ v : Fin k, ∏ p ∈ polyCorners F v,
        sgnMat M (σ v) (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false)

/-- The link `X` of `(i, j)` glues the cores of the two polygons of the cut. -/
private lemma lgs_coreX_split {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {t : ℝ}
    {σ : Fin k → Bool} {i j : Fin k} (hd : (i, j) ∈ polyDiags k) {F : Finset (Fin k × Fin k)}
    (hF : F ∈ dissections k) (hdF : (i, j) ∈ F) (X : Matrix (Fin L) (Fin L) ℂ)
    (y : Fin k → Fin L) :
    lgs_coreX β M t σ F (i, j) X y =
      ∑ xo : Fin L, ∑ xi : Fin L,
        X xo xi *
          dissCore β M t (cutLSgn σ i j) (lgs_splitL i j F)
            (fun p => if p.val = i.val then xo else y (lgs_vL i j p)) *
          dissCore β M t (cutRSgn σ i j) (lgs_splitR i j F)
            (fun q => if q.val = j.val - i.val then xi else y (lgs_vR i j q)) := by
  set e := Equiv.ofBijective _ (lgs_eqvFun_bij hd hF hdF) with he_def
  have he0 : e none = ⟨(i, j), hdF⟩ := rfl
  have heL : ∀ a, e (some (Sum.inl a)) = lgs_ιL i j F a := fun a => rfl
  have heR : ∀ b, e (some (Sum.inr b)) = lgs_ιR i j F b := fun b => rfl
  have hs0 : e.symm ⟨(i, j), hdF⟩ = none := by rw [← he0, Equiv.symm_apply_apply]
  have hsL : ∀ a, e.symm (lgs_ιL i j F a) = some (Sum.inl a) := fun a => by
    rw [← heL, Equiv.symm_apply_apply]
  have hsR : ∀ b, e.symm (lgs_ιR i j F b) = some (Sum.inr b) := fun b => by
    rw [← heR, Equiv.symm_apply_apply]
  have hL : ∀ a : ↥(lgs_splitL i j F), ¬(lgs_ιL i j F a).1 = (i, j) :=
    fun a => ((lgs_mem_splitL _).mp a.2).2
  have hR : ∀ b : ↥(lgs_splitR i j F), ¬(lgs_ιR i j F b).1 = (i, j) :=
    fun b => ((lgs_mem_splitR _).mp b.2).2
  unfold lgs_coreX
  rw [lgs_sum_pair, lgs_sum_option e, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun xo _ => Finset.sum_congr rfl fun xi _ => ?_
  unfold dissCore
  rw [lgs_sum_pair, lgs_sum_pair, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [lgs_corners_split hd hF hdF M σ y]
  rw [← e.prod_comp, Fintype.prod_option, Fintype.prod_sum_type]
  simp only [he0, heL, heR, hs0, hsL, hsR, Option.elim, Sum.elim_inl,
    Sum.elim_inr, ite_true, hL, hR, ite_false]
  have hvL : ∀ a : ↥(lgs_splitL i j F),
      (lgs_ιL i j F a).1 = (lgs_vL i j a.1.1, lgs_vL i j a.1.2) := fun a => rfl
  have hvR : ∀ b : ↥(lgs_splitR i j F),
      (lgs_ιR i j F b).1 = (lgs_vR i j b.1.1, lgs_vR i j b.1.2) := fun b => rfl
  simp only [hvL, hvR, lgs_cutLSgn_eq, lgs_cutRSgn_eq]
  ring

/-- The core of a dissection containing `(i, j)` is the core with the link `βtV` of `(i, j)`
written as the matrix `X`. -/
private lemma lgs_dissCore_eq_coreX {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {t : ℝ}
    {σ : Fin k → Bool} {i j : Fin k} {F : Finset (Fin k × Fin k)} (y : Fin k → Fin L) :
    dissCore β M t σ F y =
      lgs_coreX β M t σ F (i, j) (((β * t : ℝ) : ℂ) • pairV β M t (σ i) (σ j)) y := by
  unfold dissCore lgs_coreX
  refine Finset.sum_congr rfl fun cIn _ => Finset.sum_congr rfl fun cOut _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun e _ => ?_
  split_ifs with h
  · rw [Matrix.smul_apply, smul_eq_mul, h]
  · rfl

end Glue

/-! ## The external labels of the two polygons of a cut -/

section Sides

variable {k L : ℕ}

/-- The side `i` of the polygon of Cut_L. -/
private def lgs_iL (i j : Fin k) : Fin (k + i - j + 1) := ⟨i.val, by have := j.isLt; omega⟩

/-- The last side of the polygon of Cut_R. -/
private def lgs_lastR (i j : Fin k) : Fin (j - i + 1) := ⟨j.val - i.val, by omega⟩

private lemma lgs_vL_rot {i j : Fin k} (hd : (i, j) ∈ polyDiags k) {p : Fin (k + i - j + 1)}
    (hp : p.val ≠ i.val) : lgs_vL i j (finRotate _ p) = finRotate k (lgs_vL i j p) := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  have := p.isLt; have := j.isLt
  apply Fin.ext
  rw [lgs_finRotate_val, lgs_vL_val, lgs_vL_val, lgs_finRotate_val]
  split_ifs <;> omega

private lemma lgs_vL_rot_iL {i j : Fin k} (hd : (i, j) ∈ polyDiags k) :
    lgs_vL i j (finRotate _ (lgs_iL i j)) = j := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  have := j.isLt
  have hr : (finRotate _ (lgs_iL i j)).val = i.val + 1 := by
    have h1 := lgs_finRotate_val (lgs_iL i j)
    have h0 : (lgs_iL i j).val = i.val := rfl
    split_ifs at h1 <;> omega
  have h2 := lgs_vL_cases i j (finRotate _ (lgs_iL i j))
  apply Fin.ext
  omega

private lemma lgs_vR_rot {i j : Fin k} (hd : (i, j) ∈ polyDiags k) {q : Fin (j - i + 1)}
    (hq : q.val ≠ j.val - i.val) : lgs_vR i j (finRotate _ q) = finRotate k (lgs_vR i j q) := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  have := q.isLt; have := j.isLt
  apply Fin.ext
  rw [lgs_finRotate_val, lgs_vR_val, lgs_vR_val, lgs_finRotate_val]
  split_ifs <;> omega

private lemma lgs_vR_rot_lastR {i j : Fin k} (hd : (i, j) ∈ polyDiags k) :
    lgs_vR i j (finRotate _ (lgs_lastR i j)) = i := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  apply Fin.ext
  rw [lgs_vR_val, lgs_finRotate_val]
  simp only [lgs_lastR]
  split_ifs <;> omega



/-- The external pre-labels of `F` and the two copies of the label of `(i, j)` are the external
pre-labels of the two polygons of the cut. -/
private lemma lgs_sum_labels {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    (G : (Fin (k + i - j + 1) → Fin L) → (Fin (j - i + 1) → Fin L) → ℂ) :
    ∑ zL : Fin (k + i - j + 1) → Fin L, ∑ zR : Fin (j - i + 1) → Fin L, G zL zR =
      ∑ y : Fin k → Fin L, ∑ xo : Fin L, ∑ xi : Fin L,
        G (fun p => if p.val = i.val then xo else y (lgs_vL i j p))
          (fun q => if q.val = j.val - i.val then xi else y (lgs_vR i j q)) := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  have hj := j.isLt
  let E : (Fin k → Fin L) × (Fin L × Fin L) ≃
      (Fin (k + i - j + 1) → Fin L) × (Fin (j - i + 1) → Fin L) :=
    { toFun := fun x => (fun p => if p.val = i.val then x.2.1 else x.1 (lgs_vL i j p),
        fun q => if q.val = j.val - i.val then x.2.2 else x.1 (lgs_vR i j q))
      invFun := fun z => (fun s => if s.val < i.val ∨ j.val ≤ s.val then z.1 (lgs_uL i j s)
          else z.2 (lgs_uR i j s), (z.1 (lgs_iL i j), z.2 (lgs_lastR i j)))
      left_inv := by
        rintro ⟨y, xo, xi⟩
        simp only [lgs_iL, lgs_lastR, ite_true, Prod.mk.injEq, and_true]
        funext s
        by_cases hs : s.val < i.val ∨ j.val ≤ s.val
        · rw [ite_eq_left hs]
          have : (lgs_uL i j s).val ≠ i.val := by
            rw [lgs_uL_val]; split_ifs <;> omega
          rw [ite_eq_right this, lgs_vL_uL (by omega)]
        · rw [ite_eq_right hs]
          have : (lgs_uR i j s).val ≠ j.val - i.val := by
            rw [lgs_uR_val]; split_ifs <;> omega
          rw [ite_eq_right this, lgs_vR_uR (by omega)]
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
            have cp := lgs_vL_cases i j p
            have hs : (lgs_vL i j p).val < i.val ∨ j.val ≤ (lgs_vL i j p).val := by omega
            rw [ite_eq_left hs, lgs_uL_vL hij]
        · funext q
          by_cases hq : q.val = j.val - i.val
          · rw [ite_eq_left hq]
            congr 1
            exact Fin.ext hq.symm
          · rw [ite_eq_right hq]
            have := q.isLt
            have hs : ¬((lgs_vR i j q).val < i.val ∨ j.val ≤ (lgs_vR i j q).val) := by
              rw [lgs_vR_val]; omega
            rw [ite_eq_right hs, lgs_uR_vR] }
  rw [← Fintype.sum_prod_type', ← E.sum_comp, Fintype.sum_prod_type, Fintype.sum_congr]
  intro y
  rw [Fintype.sum_prod_type]
  rfl

end Sides

/-! ## Relabelling of the physical labels -/

section Relabel

/-- `(1 - cX)⁻¹` is invariant under a relabelling that leaves `X` invariant. -/
private lemma lgs_oneSub_inv_submatrix {R : Type*} [CommRing R] {L : ℕ} (e : Fin L ≃ Fin L)
    {X : Matrix (Fin L) (Fin L) R} (hX : X.submatrix e e = X) (c : R) :
    ((1 - c • X)⁻¹).submatrix e e = (1 - c • X)⁻¹ := by
  have h1 : (1 - c • X).submatrix e e = 1 - c • X := by
    ext x y
    have := congrFun (congrFun hX x) y
    simp only [Matrix.submatrix_apply] at this
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      e.injective.eq_iff, this]
  rw [← Matrix.inv_submatrix_equiv, h1]

/-- `P` is invariant when `M` is. -/
private lemma lgs_pairP_submatrix {L : ℕ} (β : ℝ) {M : Matrix (Fin L) (Fin L) ℂ}
    (e : Fin L ≃ Fin L) (hM : ∀ x y, M (e x) (e y) = M x y) :
    (pairP β M).submatrix e e = pairP β M := by
  ext x y
  simp only [Matrix.submatrix_apply, pairP, Matrix.of_apply, hM]

/-- `Q` is invariant when `M` is. -/
private lemma lgs_pairQ_submatrix {L : ℕ} (β : ℝ) {M : Matrix (Fin L) (Fin L) ℂ}
    (e : Fin L ≃ Fin L) (hM : ∀ x y, M (e x) (e y) = M x y) :
    (pairQ β M).submatrix e e = pairQ β M := by
  ext x y
  simp only [Matrix.submatrix_apply, pairQ, Matrix.of_apply, hM]

/-- The one-label inverses are invariant when `M` is. -/
private lemma lgs_pairV_submatrix {L : ℕ} (β : ℝ) {M : Matrix (Fin L) (Fin L) ℂ}
    (e : Fin L ≃ Fin L) (hM : ∀ x y, M (e x) (e y) = M x y) (t : ℝ) (s s' : Bool) :
    (pairV β M t s s').submatrix e e = pairV β M t s s' := by
  have hQ := lgs_oneSub_inv_submatrix e (lgs_pairQ_submatrix β e hM) (t : ℂ)
  have hP := lgs_oneSub_inv_submatrix e (lgs_pairP_submatrix β e hM) t
  unfold pairV
  split_ifs
  · exact hQ
  · rw [Matrix.submatrix_map, hQ]
  · rw [Matrix.submatrix_map, hP]

/-- Entries of the one-label inverses are invariant. -/
private lemma lgs_pairV_equiv {L : ℕ} (β : ℝ) {M : Matrix (Fin L) (Fin L) ℂ}
    (e : Fin L ≃ Fin L) (hM : ∀ x y, M (e x) (e y) = M x y) (t : ℝ) (s s' : Bool) (x y : Fin L) :
    pairV β M t s s' (e x) (e y) = pairV β M t s s' x y :=
  congrFun (congrFun (lgs_pairV_submatrix β e hM t s s') x) y

/-- `cycleAdj L` is the adjacency of `a ↦ a + 1` on `Fin L`. -/
private lemma lgs_cycleAdj_eq {L : ℕ} [NeZero L] (a b : Fin L) :
    cycleAdj L a b = (if b = a + 1 then 1 else 0) + (if a = b + 1 then 1 else 0) := by
  have h1 : ∀ x : Fin L, (x + 1).val = (x.val + 1) % L := by
    intro x
    rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  simp only [cycleAdj, Matrix.of_apply, Fin.ext_iff, h1]

/-- The cycle adjacency is invariant under translations. -/
private lemma lgs_cycleAdj_add {L : ℕ} [NeZero L] (c a b : Fin L) :
    cycleAdj L (a + c) (b + c) = cycleAdj L a b := by
  have h1 : ∀ x y : Fin L, (y + c = x + c + 1) ↔ (y = x + 1) := by
    intro x y
    rw [add_right_comm x c 1, add_left_inj]
  rw [lgs_cycleAdj_eq, lgs_cycleAdj_eq]
  simp only [h1]

/-- `M_B` is invariant under a relabelling that leaves the cycle adjacency invariant. -/
private lemma lgs_dysonMat_equiv {L : ℕ} (e : Fin L ≃ Fin L)
    (hA : ∀ x y, cycleAdj L (e x) (e y) = cycleAdj L x y) (b β : ℝ) (z m : ℂ) (x y : Fin L) :
    dysonMat b β L z m (e x) (e y) = dysonMat b β L z m x y := by
  have h : (dysonMat b β L z m).submatrix e e = dysonMat b β L z m := by
    unfold dysonMat
    rw [← Matrix.inv_submatrix_equiv]
    congr 1
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      e.injective.eq_iff, hA]
  exact congrFun (congrFun h x) y

end Relabel

section SidesProd

variable {k : ℕ}

/-- The sides of the `k`-gon are the sides of the two polygons other than the side `(i, j)`. -/
private lemma lgs_prod_sides {i j : Fin k} (hd : (i, j) ∈ polyDiags k) (h : Fin k → ℂ) :
    ∏ s, h s = (∏ p ∈ Finset.univ.erase (lgs_iL i j), h (lgs_vL i j p)) *
      ∏ q ∈ Finset.univ.erase (lgs_lastR i j), h (lgs_vR i j q) := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  have hj := j.isLt
  have hU : (Finset.univ : Finset (Fin k)) =
      (Finset.univ.erase (lgs_iL i j)).image (lgs_vL i j) ∪
        (Finset.univ.erase (lgs_lastR i j)).image (lgs_vR i j) := by
    ext s
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_image, Finset.mem_erase, ne_eq,
      and_true, true_iff]
    by_cases hs : s.val < i.val ∨ j.val ≤ s.val
    · left
      refine ⟨lgs_uL i j s, fun h => ?_, lgs_vL_uL (by omega)⟩
      have := congrArg Fin.val h
      simp only [lgs_uL_val, lgs_iL] at this
      split_ifs at this <;> omega
    · right
      refine ⟨lgs_uR i j s, fun h => ?_, lgs_vR_uR (by omega)⟩
      have := congrArg Fin.val h
      simp only [lgs_uR_val, lgs_lastR] at this
      split_ifs at this <;> omega
  have hdisj : Disjoint ((Finset.univ.erase (lgs_iL i j)).image (lgs_vL i j))
      ((Finset.univ.erase (lgs_lastR i j)).image (lgs_vR i j)) := by
    rw [Finset.disjoint_left]
    intro s h1 h2
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true] at h1 h2
    obtain ⟨p, hp, rfl⟩ := h1
    obtain ⟨q, hq, hpq⟩ := h2
    have e := congrArg Fin.val hpq
    have hp' : p.val ≠ i.val := fun h => hp (Fin.ext h)
    have hq' : q.val ≠ j.val - i.val := fun h => hq (Fin.ext h)
    have := p.isLt; have := q.isLt
    have cp := lgs_vL_cases i j p
    rw [lgs_vR_val] at e
    omega
  rw [hU, Finset.prod_union hdisj,
    Finset.prod_image (fun p _ q _ h => lgs_vL_inj hij h),
    Finset.prod_image (fun p _ q _ h => lgs_vR_inj h)]

end SidesProd

/-! ## The kernel facts at large coupling -/

section Facts

private lemma lgk_hopB {g : ℝ} (hg : 1 ≤ g) : hopB g = 1 := by
  unfold hopB; rw [max_eq_right hg, div_self (by linarith)]

private lemma lgk_gammaG {g : ℝ} (hg : 1 ≤ g) : gammaG g = (g ^ 2)⁻¹ := by
  unfold gammaG; rw [max_eq_right hg]

/-- The facts on the kernels of the model at large coupling used below, at the time `t`, with
`ℓ = min{L, g²/√(1 - t)}`. -/
private structure LgFacts (g : ℝ) (L : ℕ) (E : ℝ) (m : ℂ) (t c C : ℝ) : Prop where
  hg : 1 ≤ g
  hγ : gammaG g = (g ^ 2)⁻¹
  hL : 3 ≤ L
  hm : IsDysonRootV (hopB g) (gammaG g) L E m
  ht0 : 0 ≤ t
  ht1 : t < 1
  hc : 0 < c
  hC : 1 ≤ C
  ell_ge : g ^ 2 ≤ min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t))
  ell_le : min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t)) ≤ ellProp g L t
  ell_le2 : ellProp g L t ≤ 2 * min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t))
  A_ge : 1 ≤ g ^ 2 / ((1 - t) * min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t)))
  M_pt : ∀ a b, ‖dysonMat (hopB g) (gammaG g) L E m a b‖ ≤
    C * Real.exp (-(c * cycDist a b / g ^ 2))
  M_row : ∀ a, ∑ b, Real.exp (c * cycDist a b / g ^ 2) *
    ‖dysonMat (hopB g) (gammaG g) L E m a b‖ ≤ C * g ^ 2
  Q_row : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ a, ∑ b, Real.exp (c * cycDist a b / g ^ 2) *
    ‖(1 - (u : ℂ) • pairQ (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))⁻¹ a b‖ ≤ C
  U_row : ∀ a, ∑ b, Real.exp (c * cycDist a b / min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t))) *
    |(1 - t • pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))⁻¹ a b| ≤ C / (1 - t)
  K_pt : ∀ a b, 0 ≤ mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) t a b ∧
    mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) t a b ≤
      C / ((1 - t) * min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t)))


/-- The kernel decomposition (A.36) [da:eq:actual-kernel-decomposition] of the mixed inverse in
convolution form, with the bounds of Appendix B.5 [app:uniform-profile] at the scale `g²`. -/
private def LgUvp (g : ℝ) (L : ℕ) (E : ℝ) (m : ℂ) (t C : ℝ) : Prop :=
  ∀ [NeZero L], ∃ (ξ Er : Fin L → ℂ) (ε : ℝ),
    (∀ x, ξ (-x) = ξ x) ∧ (∀ x, Er (-x) = Er x) ∧
    (∀ x y, (((1 - t • pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))⁻¹ x y : ℝ) : ℂ) =
      (if x - y = 0 then 1 else 0) + ξ (x - y) + Er (x - y)) ∧
    ∑ x, ‖ξ x‖ ≤ C / (1 - t) ∧
    (∀ x, ‖ξ x‖ ≤ C / ((1 - t) * min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t)))) ∧
    ∑ x, ‖ξ (finRotate L x) - ξ x‖ ≤ C * (Real.sqrt (1 - t) / g ^ 2) / (1 - t) ∧
    (∀ x, ‖ξ (finRotate L x) - ξ x‖ ≤
      C * (Real.sqrt (1 - t) / g ^ 2) / ((1 - t) * min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t)))) ∧
    ∑ x, ‖ξ (finRotate L (finRotate L x)) - 2 * ξ (finRotate L x) + ξ x‖ ≤
      C * (Real.sqrt (1 - t) / g ^ 2) ^ 2 / (1 - t) ∧
    ∑ x, ‖Er x‖ ≤ C * ε / (1 - t) ^ 2 ∧ (∀ x, ‖Er x‖ ≤ C * ε / (g ^ 2 * (1 - t) ^ 2)) ∧
    ε ≤ (1 - t) ^ 2

/-- A translation-invariant symmetric matrix is a convolution. -/
private lemma lgk_ti_apply {R : Type*} {L : ℕ} [NeZero L] (X : Matrix (Fin L) (Fin L) R)
    (hT : ∀ a b c : Fin L, X (a + c) (b + c) = X a b) (hS : ∀ a b, X a b = X b a)
    (a b : Fin L) : X a b = X 0 (a - b) := by
  have := hT (a - b) 0 b
  rw [sub_add_cancel, zero_add] at this
  rw [this, hS]

/-- The convolution kernel of a translation-invariant symmetric matrix is even. -/
private lemma lgk_ti_even {R : Type*} {L : ℕ} [NeZero L] (X : Matrix (Fin L) (Fin L) R)
    (hT : ∀ a b c : Fin L, X (a + c) (b + c) = X a b) (hS : ∀ a b, X a b = X b a)
    (z : Fin L) : X 0 (-z) = X 0 z := by
  have := hT 0 (-z) z
  rw [zero_add, neg_add_cancel] at this
  rw [← this, hS]

/-- The periodization of an even kernel is even. -/
private lemma lgk_perLine_neg {L : ℕ} [NeZero L] (p : ℤ → ℝ) (hp : ∀ x, p (-x) = p x) (x : Fin L) :
    perLine p L (-x) = perLine p L x := by
  unfold perLine
  by_cases hx : x = 0
  · subst hx; simp
  · have hx0 : x.val ≠ 0 := fun h => hx (Fin.ext h)
    have hv : ((-x : Fin L) : ℕ) = L - x.val := by
      rw [Fin.val_neg']
      exact Nat.mod_eq_of_lt (by have := x.isLt; omega)
    have e : ∀ j : ℤ, p ((((-x : Fin L) : ℕ) : ℤ) + j * L) = p ((x.val : ℤ) + (-j - 1) * L) := by
      intro j
      rw [hv, ← hp]
      congr 1
      push_cast [Nat.cast_sub x.isLt.le]
      ring
    simp_rw [e]
    exact Equiv.tsum_eq ((Equiv.neg ℤ).trans (Equiv.subRight 1)) (fun j => p ((x.val : ℤ) + j * L))

/-- `X(1 - cX)⁻¹` is symmetric when `X` is, for every `c`. -/
private lemma lgk_ker_transpose {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (X : Matrix n n R) (hX : Xᵀ = X) (c : R) :
    (X * (1 - c • X)⁻¹)ᵀ = X * (1 - c • X)⁻¹ := by
  have hA : (1 - c • X)ᵀ = 1 - c • X := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hX]
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hA, hX]
  by_cases h : IsUnit (1 - c • X).det
  · have hc : (1 - c • X) * X = X * (1 - c • X) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
        Matrix.mul_smul]
    calc (1 - c • X)⁻¹ * X = (1 - c • X)⁻¹ * X * ((1 - c • X) * (1 - c • X)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ h, Matrix.mul_one]
      _ = (1 - c • X)⁻¹ * ((1 - c • X) * X) * (1 - c • X)⁻¹ := by
          rw [hc]; simp only [Matrix.mul_assoc]
      _ = X * (1 - c • X)⁻¹ := by
          rw [← Matrix.mul_assoc (1 - c • X)⁻¹, Matrix.nonsing_inv_mul _ h, Matrix.one_mul]
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.mul_zero, Matrix.zero_mul]

/-- `M_B` is invariant under translations. -/
private lemma lgk_M_add {L : ℕ} [NeZero L] (b β : ℝ) (z m : ℂ) (c x y : Fin L) :
    dysonMat b β L z m (x + c) (y + c) = dysonMat b β L z m x y :=
  lgs_dysonMat_equiv (Equiv.addRight c) (fun x y => lgs_cycleAdj_add c x y) b β z m x y

/-- The one-label inverses are invariant under translations. -/
private lemma lgk_pairV_add {L : ℕ} [NeZero L] (β b β' : ℝ) (z m : ℂ) (t : ℝ) (s s' : Bool)
    (c x y : Fin L) :
    pairV β (dysonMat b β' L z m) t s s' (x + c) (y + c) =
      pairV β (dysonMat b β' L z m) t s s' x y :=
  lgs_pairV_equiv β (Equiv.addRight c) (fun x y => lgk_M_add b β' z m c x y) t s s' x y

/-- The mixed inverse `(1 - tP)⁻¹` is invariant under translations. -/
private lemma lgk_U_add {L : ℕ} [NeZero L] (β b β' : ℝ) (z m : ℂ) (t : ℝ) (c x y : Fin L) :
    (1 - t • pairP β (dysonMat b β' L z m))⁻¹ (x + c) (y + c) =
      (1 - t • pairP β (dysonMat b β' L z m))⁻¹ x y :=
  congrFun (congrFun (lgs_oneSub_inv_submatrix (Equiv.addRight c)
    (lgs_pairP_submatrix β (Equiv.addRight c) (fun x y => lgk_M_add b β' z m c x y)) t) x) y

/-- The mixed inverse `(1 - tP)⁻¹` is symmetric under the primitive data. -/
private lemma lgk_U_symm {L : ℕ} {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m)
    (t : ℝ) (x y : Fin L) : (1 - t • pairP β M)⁻¹ x y = (1 - t • pairP β M)⁻¹ y x := by
  have hP : (pairP β M)ᵀ = pairP β M := by
    ext a b
    have h := congrFun (congrFun hD.symm a) b
    simp only [Matrix.transpose_apply] at h
    simp only [Matrix.transpose_apply, pairP, Matrix.of_apply, h]
  have : ((1 - t • pairP β M)⁻¹)ᵀ = (1 - t • pairP β M)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_one,
      Matrix.transpose_smul, hP]
  have h := congrFun (congrFun this y) x
  rw [Matrix.transpose_apply] at h
  exact h

/-- The one-label inverses are symmetric under the primitive data. -/
private lemma lgk_V_symm {L : ℕ} {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m)
    (t : ℝ) (s s' : Bool) (x y : Fin L) : pairV β M t s s' x y = pairV β M t s s' y x := by
  have h := congrFun (congrFun (lgw_V_symm hD t s s') y) x
  rw [Matrix.transpose_apply] at h
  exact h

/-- The one-label inverse of a sign pair does not depend on the order of the two signs. -/
private lemma lgk_pairV_swap {L : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) (s s' : Bool) :
    pairV β M t s s' = pairV β M t s' s := by
  cases s <;> cases s' <;> rfl


/-- The circulant matrix of `P₀` is invariant under translations. -/
private lemma lgk_circ_add {L : ℕ} [NeZero L] (v : Fin L → ℝ) (c x y : Fin L) :
    Matrix.circulant v (x + c) (y + c) = Matrix.circulant v x y := by
  simp only [Matrix.circulant_apply, add_sub_add_right_eq_sub]

/-- The kernel `Ξ = s P₀(1 - sP₀)⁻¹` of (A.36) [da:eq:actual-kernel-decomposition] is translation
invariant and symmetric. -/
private lemma lgk_Xi_ti {L : ℕ} [NeZero L] (v : Fin L → ℝ) (hv : ∀ x, v (-x) = v x) (s : ℝ) :
    (∀ a b c : Fin L, (s • mixedKer (Matrix.circulant v) s) (a + c) (b + c) =
      (s • mixedKer (Matrix.circulant v) s) a b) ∧
    ∀ a b : Fin L, (s • mixedKer (Matrix.circulant v) s) a b =
      (s • mixedKer (Matrix.circulant v) s) b a := by
  set C := Matrix.circulant v with hC
  have hCs : ∀ c : Fin L, C.submatrix (Equiv.addRight c) (Equiv.addRight c) = C := by
    intro c; ext x y
    simp only [Matrix.submatrix_apply, Equiv.coe_addRight, hC, lgk_circ_add]
  have hCt : Cᵀ = C := by
    ext x y
    simp only [Matrix.transpose_apply, hC, Matrix.circulant_apply]
    rw [← hv, neg_sub]
  constructor
  · intro a b c
    have h1 := lgs_oneSub_inv_submatrix (Equiv.addRight c) (hCs c) s
    have h2 : (mixedKer C s).submatrix (Equiv.addRight c) (Equiv.addRight c) = mixedKer C s := by
      unfold mixedKer
      rw [← Matrix.submatrix_mul_equiv _ _ _ (Equiv.addRight c), hCs c, h1]
    have := congrFun (congrFun h2 a) b
    simp only [Matrix.submatrix_apply, Equiv.coe_addRight] at this
    simp only [Matrix.smul_apply, this]
  · intro a b
    have h := congrFun (congrFun (lgk_ker_transpose C hCt s) b) a
    simp only [Matrix.transpose_apply] at h
    simp only [Matrix.smul_apply, mixedKer, h]

/-- `P₀` of Lemma A.4 [uvp:prop:finite] is even. -/
private lemma lgk_perP0_neg {L : ℕ} [NeZero L] (g E : ℝ) (mInf : ℂ) (x : Fin L) :
    perP0 g L E mInf (-x) = perP0 g L E mInf x := by
  unfold perP0
  exact lgk_perLine_neg _ (fun y => by simp only [Int.natAbs_neg]) x


/-- The rows of a circulant matrix are the sums of its profile. -/
private lemma lgk_circ_row {L : ℕ} [NeZero L] (v : Fin L → ℝ) (a : Fin L) :
    ∑ b, Matrix.circulant v a b = ∑ x, v x := by
  simp only [Matrix.circulant_apply]
  exact Equiv.sum_comp (Equiv.subLeft a) v

/-- The kernel facts at large coupling, from Lemma A.4 [uvp:prop:finite] and Lemma A.10
[uvp:lem:actual-kernels], under `L ≥ R(1 + |log(1 - t)|)g²`. -/
private lemma lgk_facts (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ R c C : ℝ, 1 ≤ Cκ ∧ 1 ≤ R ∧ 0 < c ∧ 1 ≤ C ∧ ∀ g : ℝ, Cκ ≤ g → ∀ L : ℕ, 3 ≤ L →
      ∀ t : ℝ, 0 ≤ t → t < 1 → R * (1 + |Real.log (1 - t)|) * g ^ 2 ≤ L →
      ∀ E : ℝ, |E| ≤ 2 - κ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m →
      LgFacts g L E m t c C ∧ LgUvp g L E m t C := by
  obtain ⟨Cκ₁, R₁, c₁, C₁, hCκ₁, hR₁, hc₁, hC₁, H₁⟩ := large_actual_kernels κ hκ hκ2
  obtain ⟨Cκ₂, R₂, c₂, C₂, hCκ₂, hR₂, hc₂, hC₂, H₂⟩ := large_periodic_comparison κ hκ hκ2
  have hmax1 : (1 : ℝ) ≤ max 1 c₁ := le_max_left _ _
  have hCm : 0 ≤ C₁ * max 1 c₁ := mul_nonneg hC₁.le (by linarith)
  refine ⟨max Cκ₁ Cκ₂, max (max R₁ R₂) 1, min (c₂ / 2) c₁, C₁ * max 1 c₁ + C₁ + C₂ + 1,
    le_trans hCκ₁ (le_max_left _ _), le_max_right _ _, lt_min (by positivity) hc₁, by linarith,
    ?_⟩
  intro g hg L hL t ht0 ht1 hRL E hE m hm
  have hc_le2 : min (c₂ / 2) c₁ ≤ c₂ / 2 := min_le_left _ _
  have hc_le1 : min (c₂ / 2) c₁ ≤ c₁ := min_le_right _ _
  have hc0 : 0 < min (c₂ / 2) c₁ := lt_min (by positivity) hc₁
  have hC1le : C₁ ≤ C₁ * max 1 c₁ + C₁ + C₂ + 1 := by linarith
  have hC2le : C₂ ≤ C₁ * max 1 c₁ + C₁ + C₂ + 1 := by linarith
  have hCmle : C₁ * max 1 c₁ ≤ C₁ * max 1 c₁ + C₁ + C₂ + 1 := by linarith
  set c := min (c₂ / 2) c₁ with hcdef
  set C := C₁ * max 1 c₁ + C₁ + C₂ + 1 with hCdef
  have hC1 : 1 ≤ C := by linarith
  have hg1 : 1 ≤ g := le_trans (le_trans hCκ₁ (le_max_left _ _)) hg
  have hg0 : 0 < g := by linarith
  have hg2 : 0 < g ^ 2 := by positivity
  have hγ := lgk_gammaG hg1
  have hδ0 : 0 < 1 - t := by linarith
  have hδ1 : 1 - t ≤ 1 := by linarith
  have hlog : 0 ≤ |Real.log (1 - t)| := abs_nonneg _
  have hR1 : (1 : ℝ) ≤ max (max R₁ R₂) 1 := le_max_right _ _
  have hRR₁ : R₁ ≤ max (max R₁ R₂) 1 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hRR₂ : R₂ ≤ max (max R₁ R₂) 1 := le_trans (le_max_right _ _) (le_max_left _ _)
  have hgL : g ^ 2 ≤ L := by
    have : g ^ 2 ≤ max (max R₁ R₂) 1 * (1 + |Real.log (1 - t)|) * g ^ 2 := by
      have : (1 : ℝ) ≤ max (max R₁ R₂) 1 * (1 + |Real.log (1 - t)|) := by nlinarith
      nlinarith
    linarith
  have hRL₂ : R₂ * g ^ 2 ≤ L := by
    have : R₂ * g ^ 2 ≤ max (max R₁ R₂) 1 * (1 + |Real.log (1 - t)|) * g ^ 2 := by
      have : R₂ ≤ max (max R₁ R₂) 1 * (1 + |Real.log (1 - t)|) := by nlinarith
      nlinarith
    linarith
  have hRL₁ : R₁ * (1 + |Real.log (1 - t)|) ≤ L / g ^ 2 := by
    rw [le_div_iff₀ hg2]
    have : R₁ * (1 + |Real.log (1 - t)|) ≤ max (max R₁ R₂) 1 * (1 + |Real.log (1 - t)|) :=
      mul_le_mul_of_nonneg_right hRR₁ (by linarith)
    nlinarith
  obtain ⟨m', mInf, hm', hmInf, -, -, -, -, -, hP0nn, hP0sum, -, -, hMpt, hMrow, hQrow⟩ :=
    H₂ g (le_trans (le_max_right _ _) hg) L hRL₂ E hE
  have hmm : m' = m := isDysonRootV_unique (hopB g) (gammaG g)
    (by rw [lgk_hopB hg1]; norm_num) (by rw [hγ]; positivity) L hL E (by simp) m' m hm' hm
  subst hmm
  have h11 : (1 : ℝ) - (1 - t) = t := sub_sub_cancel 1 t
  obtain ⟨hε, hK, hΞrow, hΞpt, hΔ1, hΔpt, hΔ2, hErow, hEpt, ⟨hℓ1, hℓ2⟩, hUw, -, hA1, -⟩ :=
    H₁ g (le_trans (le_max_left _ _) hg) L E hE m' mInf hm hmInf (1 - t) hδ0 hδ1 hRL₁
  simp only [h11] at hK hℓ1 hℓ2 hUw hΔ1 hΔpt hΔ2 hErow hEpt hΞrow hΞpt
  set ℓ := min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t)) with hℓdef
  have hsq : Real.sqrt (1 - t) ≤ 1 := Real.sqrt_le_one.mpr hδ1
  have hsq0 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr hδ0
  have hℓg : g ^ 2 ≤ ℓ := by
    refine le_min hgL ?_
    rw [le_div_iff₀ hsq0]
    nlinarith
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le hg2 hℓg
  have hexp_mono : ∀ (x y : ℝ) (d : ℕ), 0 < y → x ≤ y →
      Real.exp (-(y * d / g ^ 2)) ≤ Real.exp (-(x * d / g ^ 2)) := by
    intro x y d hy hxy
    apply Real.exp_le_exp.mpr
    have : x * (d : ℝ) / g ^ 2 ≤ y * d / g ^ 2 := by
      apply div_le_div_of_nonneg_right _ hg2.le
      exact mul_le_mul_of_nonneg_right hxy (Nat.cast_nonneg _)
    linarith
  refine ⟨⟨hg1, hγ, hL, hm, ht0, ht1, hc0, hC1, hℓg, hℓ1, hℓ2, hA1, fun a b => ?_, fun a => ?_,
    fun u hu0 hu1 a => ?_, fun a => ?_, fun a b => ?_⟩, ?_⟩
  · calc ‖dysonMat (hopB g) (gammaG g) L E m' a b‖
        ≤ C₂ * Real.exp (-(c₂ * cycDist a b / g ^ 2)) := hMpt a b
      _ ≤ C * Real.exp (-(c * cycDist a b / g ^ 2)) :=
          mul_le_mul hC2le (hexp_mono _ _ _ hc₂ (by linarith)) (Real.exp_pos _).le (by linarith)
  · refine le_trans (Finset.sum_le_sum fun b _ => ?_) ((hMrow a).trans
      (mul_le_mul_of_nonneg_right hC2le hg2.le))
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    apply div_le_div_of_nonneg_right _ hg2.le
    exact mul_le_mul_of_nonneg_right hc_le2 (Nat.cast_nonneg _)
  · refine le_trans (Finset.sum_le_sum fun b _ => ?_) ((hQrow u hu0 hu1 a).trans hC2le)
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    apply div_le_div_of_nonneg_right _ hg2.le
    exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  · refine le_trans (Finset.sum_le_sum fun b _ => ?_) ((hUw a).trans
      (div_le_div_of_nonneg_right hC1le hδ0.le))
    have h1 : Real.exp (c * cycDist a b / ℓ) ≤ Real.exp (c₁ * cycDist a b / ℓ) := by
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ hℓ0.le
      exact mul_le_mul_of_nonneg_right hc_le1 (Nat.cast_nonneg _)
    exact mul_le_mul h1 (le_add_of_nonneg_left (abs_nonneg _)) (abs_nonneg _)
      (Real.exp_pos _).le
  · exact ⟨(hK a b).1, (hK a b).2.trans (div_le_div_of_nonneg_right hC1le (by positivity))⟩
  · intro hNZ
    have hD := primData_of_root g L hL E m' hm
    obtain ⟨hΞT, hΞS⟩ := lgk_Xi_ti (perP0 g L E mInf) (lgk_perP0_neg g E mInf) t
    set P := pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m') with hPdef
    set Ξ := t • mixedKer (Matrix.circulant (perP0 g L E mInf)) t with hΞdef
    set U := (1 - t • P)⁻¹ with hUdef
    have hUT : ∀ a b c, U (a + c) (b + c) = U a b := fun a b c => lgk_U_add _ _ _ _ _ t c a b
    have hUS : ∀ a b, U a b = U b a := fun a b => lgk_U_symm hD t a b
    set 𝓔 := U - 1 - Ξ with h𝓔
    have hET : ∀ a b c, 𝓔 (a + c) (b + c) = 𝓔 a b := by
      intro a b c
      simp only [h𝓔, Matrix.sub_apply, hUT, hΞT, Matrix.one_apply, add_left_inj]
    have hES : ∀ a b, 𝓔 a b = 𝓔 b a := by
      intro a b
      simp only [h𝓔, Matrix.sub_apply, hUS a b, hΞS a b, Matrix.one_apply, eq_comm]
    have hΞnn : ∀ a b, 0 ≤ Ξ a b := by
      obtain ⟨hnn, -⟩ := mixedKer_nonneg_row (Matrix.circulant (perP0 g L E mInf))
        (fun a b => by rw [Matrix.circulant_apply]; exact hP0nn _)
        (fun a => by rw [lgk_circ_row]; exact hP0sum) t ht0 ht1
      intro a b
      simp only [hΞdef, Matrix.smul_apply, smul_eq_mul]
      exact mul_nonneg ht0 (hnn a b)
    have hεnn : 0 ≤ epsL C₁ c₁ g L := by
      unfold epsL
      exact mul_nonneg (mul_nonneg hC₁.le (Real.rpow_nonneg (by positivity) _)) (Real.exp_pos _).le
    have hcast : ∀ r : ℝ, ‖(r : ℂ)‖ = |r| := fun r => by
      rw [Complex.norm_real, Real.norm_eq_abs]
    have hmx0 : 0 < max 1 c₁ := by linarith
    set ε := epsL C₁ c₁ g L with hεdef
    have hεC : ∀ D : ℝ, 0 < D → C₁ * ε / D ≤ C * (ε / max 1 c₁) / D := by
      intro D hD0
      apply div_le_div_of_nonneg_right _ hD0.le
      have : C₁ * ε = (C₁ * max 1 c₁) * (ε / max 1 c₁) := by field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_right hCmle (div_nonneg hεnn hmx0.le)
    refine ⟨fun x => ((Ξ 0 x : ℝ) : ℂ), fun x => ((𝓔 0 x : ℝ) : ℂ), ε / max 1 c₁,
      fun x => by simp only [lgk_ti_even Ξ hΞT hΞS x],
      fun x => by simp only [lgk_ti_even 𝓔 hET hES x], fun x y => ?_, ?_, fun x => ?_, ?_,
      fun x => ?_, ?_, ?_, fun x => ?_, ?_⟩
    · rw [lgk_ti_apply U hUT hUS x y]
      have e : U 0 (x - y) = (1 : Matrix (Fin L) (Fin L) ℝ) 0 (x - y) + Ξ 0 (x - y) +
          𝓔 0 (x - y) := by
        simp only [h𝓔, Matrix.sub_apply]; ring
      rw [e, Matrix.one_apply]
      push_cast
      congr 2
      by_cases h : x - y = 0
      · rw [ite_eq_left h, ite_eq_left h.symm]; simp
      · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]; simp
    · simp only [hcast, abs_of_nonneg (hΞnn _ _)]
      exact (hΞrow 0).trans (div_le_div_of_nonneg_right hC1le hδ0.le)
    · rw [hcast, abs_of_nonneg (hΞnn _ _)]
      exact (hΞpt 0 x).trans (div_le_div_of_nonneg_right hC1le (by positivity))
    · simp only [← Complex.ofReal_sub, hcast]
      exact (hΔ1 0).trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC1le (by positivity)) hδ0.le)
    · rw [← Complex.ofReal_sub, hcast]
      exact (hΔpt 0 x).trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC1le (by positivity)) (by positivity))
    · have e : ∀ x, ((Ξ 0 (finRotate L (finRotate L x)) : ℝ) : ℂ) -
          2 * ((Ξ 0 (finRotate L x) : ℝ) : ℂ) + ((Ξ 0 x : ℝ) : ℂ) =
          ((Ξ 0 (finRotate L (finRotate L x)) - 2 * Ξ 0 (finRotate L x) + Ξ 0 x : ℝ) : ℂ) := by
        intro x; push_cast; ring
      simp only [e, hcast]
      exact (hΔ2 0).trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC1le (by positivity)) hδ0.le)
    · simp only [hcast]
      exact (hErow 0).trans (hεC _ (by positivity))
    · rw [hcast]
      have h1 := hEpt 0 x
      have h2 := hεC (g ^ 2 * (1 - t) ^ 2) (by positivity)
      exact h1.trans h2
    · rw [div_le_iff₀ hmx0]
      calc ε ≤ c₁ * (1 - t) ^ 2 := hε
        _ ≤ max 1 c₁ * (1 - t) ^ 2 := mul_le_mul_of_nonneg_right (le_max_right _ _)
            (by positivity)
        _ = (1 - t) ^ 2 * max 1 c₁ := mul_comm _ _

end Facts

/-! ## Weighted rows of the kernels at large coupling -/

section WeightedA

/-- `e^{λd} ≤ e^{cd/D}` for `0 ≤ λ ≤ c/D`. -/
private lemma lgk_exp_le {lm c D : ℝ} (hlm : lm ≤ c / D) (d : ℕ) :
    Real.exp (lm * d) ≤ Real.exp (c * d / D) := by
  apply Real.exp_le_exp.mpr
  have : lm * (d : ℝ) ≤ c / D * d := mul_le_mul_of_nonneg_right hlm (Nat.cast_nonneg _)
  calc lm * (d : ℝ) ≤ c / D * d := this
    _ = c * d / D := by ring

/-- Weighted rows of the pair matrices `X ∈ {P, Q, Q̄}`: `Σ_y e^{λd}|X| ≤ C²` for `λ ≤ c/g²`. -/
private lemma lgk_X_wrow {g : ℝ} {L : ℕ} {E : ℝ} {m : ℂ} {t c C : ℝ} (F : LgFacts g L E m t c C)
    {lm : ℝ} (hlm : lm ≤ c / g ^ 2) (s s' : Bool) (a : Fin L) :
    ∑ y, Real.exp (lm * cycDist a y) *
      ‖lgw_pairX (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) s s' a y‖ ≤ C ^ 2 := by
  have hD := primData_of_root g L F.hL E m F.hm
  have hg2 : 0 < g ^ 2 := by have := F.hg; positivity
  set M := dysonMat (hopB g) (gammaG g) L E m with hM
  have hMC : ∀ x y, ‖M x y‖ ≤ C := by
    intro x y
    have h0 : 0 ≤ c * cycDist x y / g ^ 2 := by have := F.hc; positivity
    exact (F.M_pt x y).trans (mul_le_of_le_one_right (by linarith [F.hC])
      (Real.exp_le_one_iff.mpr (by linarith)))
  calc ∑ y, Real.exp (lm * cycDist a y) * ‖lgw_pairX (gammaG g) M s s' a y‖
      ≤ ∑ y, gammaG g * C * (Real.exp (c * cycDist a y / g ^ 2) * ‖M a y‖) := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [lgw_pairX_norm hD]
        have h1 := lgk_exp_le hlm (cycDist a y)
        have h2 : gammaG g * ‖M a y‖ ^ 2 ≤ gammaG g * C * ‖M a y‖ := by
          calc gammaG g * ‖M a y‖ ^ 2 = (gammaG g * ‖M a y‖) * ‖M a y‖ := by ring
            _ ≤ (gammaG g * ‖M a y‖) * C :=
                mul_le_mul_of_nonneg_left (hMC a y) (mul_nonneg hD.pos.le (norm_nonneg _))
            _ = gammaG g * C * ‖M a y‖ := by ring
        calc Real.exp (lm * cycDist a y) * (gammaG g * ‖M a y‖ ^ 2)
            ≤ Real.exp (c * cycDist a y / g ^ 2) * (gammaG g * C * ‖M a y‖) :=
              mul_le_mul h1 h2 (by have := hD.pos; positivity) (Real.exp_pos _).le
          _ = _ := by ring
    _ = gammaG g * C * ∑ y, Real.exp (c * cycDist a y / g ^ 2) * ‖M a y‖ := by
        rw [Finset.mul_sum]
    _ ≤ gammaG g * C * (C * g ^ 2) :=
        mul_le_mul_of_nonneg_left (F.M_row a) (by have := hD.pos; have := F.hC; positivity)
    _ = C ^ 2 := by
        rw [F.hγ]
        calc (g ^ 2)⁻¹ * C * (C * g ^ 2) = C ^ 2 * ((g ^ 2)⁻¹ * g ^ 2) := by ring
          _ = C ^ 2 := by rw [inv_mul_cancel₀ hg2.ne', mul_one]

/-- Weighted rows of the one-label inverses: `Σ_b e^{λd}|V_t| ≤ C/(1 - t)` for `λ ≤ c/ℓ`. -/
private lemma lgk_V_wrow {g : ℝ} {L : ℕ} {E : ℝ} {m : ℂ} {t c C : ℝ} (F : LgFacts g L E m t c C)
    {lm : ℝ} (hlm : lm ≤ c / min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t))) (s s' : Bool)
    (a : Fin L) :
    ∑ b, Real.exp (lm * cycDist a b) *
      ‖pairV (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t s s' a b‖ ≤ C / (1 - t) := by
  have hg2 : 0 < g ^ 2 := by have := F.hg; positivity
  have hℓ0 : 0 < min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t)) := lt_of_lt_of_le hg2 F.ell_ge
  have h1t : 0 < 1 - t := by linarith [F.ht1]
  have hlm' : lm ≤ c / g ^ 2 := hlm.trans (div_le_div_of_nonneg_left F.hc.le hg2 F.ell_ge)
  have hQ : ∑ b, Real.exp (lm * cycDist a b) *
      ‖(1 - (t : ℂ) • pairQ (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))⁻¹ a b‖ ≤
        C / (1 - t) := by
    refine le_trans (Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right
      (lgk_exp_le hlm' _) (norm_nonneg _)) ((F.Q_row t F.ht0 F.ht1.le a).trans ?_)
    rw [le_div_iff₀ h1t]
    nlinarith [F.hC, F.ht0]
  by_cases hss : s = s'
  · subst hss
    cases s
    · simp only [pairV, ite_true, Bool.false_eq_true, ite_false, Matrix.map_apply, norm_star]
      exact hQ
    · simp only [pairV, ite_true]
      exact hQ
  · have hv : pairV (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t s s' =
        ((1 - t • pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))⁻¹).map
          ((↑) : ℝ → ℂ) := by
      unfold pairV; rw [ite_eq_right hss]
    rw [hv]
    refine le_trans (Finset.sum_le_sum fun b _ => ?_) (F.U_row a)
    rw [Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (lgk_exp_le hlm _) (abs_nonneg _)

/-- Weighted rows of the pair kernels: `Σ_b e^{λd}|K_t| ≤ C³/(1 - t)` for `λ ≤ c/ℓ`. -/
private lemma lgk_K_wrow {g : ℝ} {L : ℕ} {E : ℝ} {m : ℂ} {t c C : ℝ} (F : LgFacts g L E m t c C)
    {lm : ℝ} (hlm0 : 0 ≤ lm) (hlm : lm ≤ c / min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t)))
    (s s' : Bool) (a : Fin L) :
    ∑ b, Real.exp (lm * cycDist a b) *
      ‖pairK (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t s s' a b‖ ≤
        C ^ 2 * (C / (1 - t)) := by
  have hg2 : 0 < g ^ 2 := by have := F.hg; positivity
  have hlm' : lm ≤ c / g ^ 2 := hlm.trans (div_le_div_of_nonneg_left F.hc.le hg2 F.ell_ge)
  set β := gammaG g
  set M := dysonMat (hopB g) (gammaG g) L E m
  calc ∑ b, Real.exp (lm * cycDist a b) * ‖pairK β M t s s' a b‖
      ≤ ∑ b, ∑ y, (Real.exp (lm * cycDist a y) * ‖lgw_pairX β M s s' a y‖) *
          (Real.exp (lm * cycDist y b) * ‖pairV β M t s s' y b‖) := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [lgw_K_apply]
        calc Real.exp (lm * cycDist a b) * ‖∑ y, lgw_pairX β M s s' a y * pairV β M t s s' y b‖
            ≤ Real.exp (lm * cycDist a b) * ∑ y, ‖lgw_pairX β M s s' a y‖ *
                ‖pairV β M t s s' y b‖ :=
              mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
                (Finset.sum_le_sum fun y _ => by rw [norm_mul])) (Real.exp_pos _).le
          _ = ∑ y, Real.exp (lm * cycDist a b) * (‖lgw_pairX β M s s' a y‖ *
                ‖pairV β M t s s' y b‖) := by rw [Finset.mul_sum]
          _ ≤ _ := by
              refine Finset.sum_le_sum fun y _ => ?_
              calc Real.exp (lm * cycDist a b) * (‖lgw_pairX β M s s' a y‖ *
                    ‖pairV β M t s s' y b‖)
                  ≤ (Real.exp (lm * cycDist a y) * Real.exp (lm * cycDist y b)) *
                      (‖lgw_pairX β M s s' a y‖ * ‖pairV β M t s s' y b‖) :=
                    mul_le_mul_of_nonneg_right (lgw_exp_tri hlm0 a y b) (by positivity)
                _ = _ := by ring
    _ = ∑ y, (Real.exp (lm * cycDist a y) * ‖lgw_pairX β M s s' a y‖) *
          ∑ b, Real.exp (lm * cycDist y b) * ‖pairV β M t s s' y b‖ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ y, (Real.exp (lm * cycDist a y) * ‖lgw_pairX β M s s' a y‖) * (C / (1 - t)) :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (lgk_V_wrow F hlm s s' y)
          (by positivity)
    _ = (∑ y, Real.exp (lm * cycDist a y) * ‖lgw_pairX β M s s' a y‖) * (C / (1 - t)) := by
        rw [Finset.sum_mul]
    _ ≤ C ^ 2 * (C / (1 - t)) :=
        mul_le_mul_of_nonneg_right (lgk_X_wrow F hlm' s s' a)
          (div_nonneg (by linarith [F.hC]) (by linarith [F.ht1]))

/-- Weighted entries of the pair kernels: `β⁻¹ e^{λd}|K_t| ≤ C³/(1 - t)` for `λ ≤ c/ℓ`. -/
private lemma lgk_K_wpt {g : ℝ} {L : ℕ} {E : ℝ} {m : ℂ} {t c C : ℝ} (F : LgFacts g L E m t c C)
    {lm : ℝ} (hlm0 : 0 ≤ lm) (hlm : lm ≤ c / min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t)))
    (s s' : Bool) (a b : Fin L) :
    (gammaG g)⁻¹ * (Real.exp (lm * cycDist a b) *
      ‖pairK (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t s s' a b‖) ≤
        C ^ 2 * (C / (1 - t)) := by
  have hD := primData_of_root g L F.hL E m F.hm
  have hg2 : 0 < g ^ 2 := by have := F.hg; positivity
  have hlm' : lm ≤ c / g ^ 2 := hlm.trans (div_le_div_of_nonneg_left F.hc.le hg2 F.ell_ge)
  set β := gammaG g
  set M := dysonMat (hopB g) (gammaG g) L E m
  have hβ := hD.pos
  have hMC : ∀ x y, Real.exp (lm * cycDist x y) * ‖M x y‖ ≤ C := by
    intro x y
    have h1 := F.M_pt x y
    calc Real.exp (lm * cycDist x y) * ‖M x y‖
        ≤ Real.exp (c * cycDist x y / g ^ 2) * (C * Real.exp (-(c * cycDist x y / g ^ 2))) :=
          mul_le_mul (lgk_exp_le hlm' _) h1 (norm_nonneg _) (Real.exp_pos _).le
      _ = C := by
          rw [mul_comm C, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  have hMC' : ∀ x y, ‖M x y‖ ≤ C := fun x y =>
    le_trans (le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by
      have := lgk_exp_le hlm' 0
      positivity))) (hMC x y)
  have hX : ∀ y, Real.exp (lm * cycDist a y) * ‖lgw_pairX β M s s' a y‖ ≤ β * C ^ 2 := by
    intro y
    rw [lgw_pairX_norm hD]
    calc Real.exp (lm * cycDist a y) * (β * ‖M a y‖ ^ 2)
        = β * ((Real.exp (lm * cycDist a y) * ‖M a y‖) * ‖M a y‖) := by ring
      _ ≤ β * (C * C) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul (hMC a y) (hMC' a y) (norm_nonneg _)
            (by linarith [F.hC])) hβ.le
      _ = β * C ^ 2 := by ring
  have hVc : ∑ y, Real.exp (lm * cycDist y b) * ‖pairV β M t s s' y b‖ ≤ C / (1 - t) := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun y _ => ?_)) (lgk_V_wrow F hlm s s' b)
    rw [lgw_cd_comm y b, lgk_V_symm hD t s s' y b]
  calc β⁻¹ * (Real.exp (lm * cycDist a b) * ‖pairK β M t s s' a b‖)
      ≤ β⁻¹ * ∑ y, (Real.exp (lm * cycDist a y) * ‖lgw_pairX β M s s' a y‖) *
          (Real.exp (lm * cycDist y b) * ‖pairV β M t s s' y b‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hβ.le)
        rw [lgw_K_apply]
        calc Real.exp (lm * cycDist a b) * ‖∑ y, lgw_pairX β M s s' a y * pairV β M t s s' y b‖
            ≤ Real.exp (lm * cycDist a b) * ∑ y, ‖lgw_pairX β M s s' a y‖ *
                ‖pairV β M t s s' y b‖ :=
              mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
                (Finset.sum_le_sum fun y _ => by rw [norm_mul])) (Real.exp_pos _).le
          _ = ∑ y, Real.exp (lm * cycDist a b) * (‖lgw_pairX β M s s' a y‖ *
                ‖pairV β M t s s' y b‖) := by rw [Finset.mul_sum]
          _ ≤ _ := by
              refine Finset.sum_le_sum fun y _ => ?_
              calc Real.exp (lm * cycDist a b) * (‖lgw_pairX β M s s' a y‖ *
                    ‖pairV β M t s s' y b‖)
                  ≤ (Real.exp (lm * cycDist a y) * Real.exp (lm * cycDist y b)) *
                      (‖lgw_pairX β M s s' a y‖ * ‖pairV β M t s s' y b‖) :=
                    mul_le_mul_of_nonneg_right (lgw_exp_tri hlm0 a y b) (by positivity)
                _ = _ := by ring
    _ ≤ β⁻¹ * ∑ y, (β * C ^ 2) * (Real.exp (lm * cycDist y b) * ‖pairV β M t s s' y b‖) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => ?_)
          (inv_nonneg.mpr hβ.le)
        exact mul_le_mul_of_nonneg_right (hX y) (by positivity)
    _ = C ^ 2 * ∑ y, Real.exp (lm * cycDist y b) * ‖pairV β M t s s' y b‖ := by
        rw [← Finset.mul_sum, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hβ.ne', one_mul]
    _ ≤ C ^ 2 * (C / (1 - t)) := mul_le_mul_of_nonneg_left hVc (by positivity)

variable {L : ℕ}

private lemma lgk_base_wtd {θ β : ℝ} (hθ : 0 ≤ θ) {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {T CKK : ℝ} (hT1 : T < 1)
    (hpt : ∀ t : ℝ, 0 ≤ t → t ≤ T → ∀ (s s' : Bool) (a b : Fin L),
      β⁻¹ * (Real.exp (θ * cycDist a b) * ‖pairK β M t s s' a b‖) ≤ CKK / (1 - t))
    (hrow : ∀ t : ℝ, 0 ≤ t → t ≤ T → ∀ (s s' : Bool) (a : Fin L),
      ∑ b, Real.exp (θ * cycDist a b) * ‖pairK β M t s s' a b‖ ≤ CKK / (1 - t)) :
    lgw_Bd θ β M m T 2 CKK := by
  have hβ := hD.pos
  intro t ht0 htT
  have ht1 : t < 1 := lt_of_le_of_lt htT hT1
  have h1t : 0 < 1 - t := by linarith
  have hkey : ∀ (a : Fin 2 → Fin L) (σ : Fin 2 → Bool), ‖primF β M m t a σ‖ =
      β⁻¹ * ‖pairK β M t (σ 0) (σ 1) (a 0) (a 1)‖ := by
    intro a σ
    change ‖(β : ℂ)⁻¹ * pairK β M t (σ 0) (σ 1) (a 0) (a 1)‖ = _
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ]
  have hpow : ((1 - t) ^ (2 * 2 - 3))⁻¹ = (1 - t)⁻¹ := by norm_num
  have hdiam : ∀ (a : Fin 2 → Fin L), wordDiam a ≤ cycDist (a 0) (a 1) := by
    intro a
    refine lgw_diam_le a fun p q => ?_
    fin_cases p <;> fin_cases q <;> simp [lgw_cd_self, lgw_cd_comm]
  have hexp : ∀ (a : Fin 2 → Fin L), Real.exp (θ * wordDiam a) ≤
      Real.exp (θ * cycDist (a 0) (a 1)) := fun a => by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hdiam a) hθ
  have hA : CKK / (1 - t) ≤ CKK * (1 - t)⁻¹ := le_of_eq (div_eq_mul_inv _ _)
  have hsum : ∀ (F : Fin L → ℝ), β * ∑ c, β⁻¹ * F c = ∑ c, F c := by
    intro F
    rw [← Finset.mul_sum, ← mul_assoc, mul_inv_cancel₀ hβ.ne', one_mul]
  refine ⟨fun a σ => ?_, fun j a σ => ?_⟩
  · rw [hkey, hpow]
    calc Real.exp (θ * wordDiam a) * (β⁻¹ * ‖pairK β M t (σ 0) (σ 1) (a 0) (a 1)‖)
        ≤ Real.exp (θ * cycDist (a 0) (a 1)) *
            (β⁻¹ * ‖pairK β M t (σ 0) (σ 1) (a 0) (a 1)‖) :=
          mul_le_mul_of_nonneg_right (hexp a) (by positivity)
      _ = β⁻¹ * (Real.exp (θ * cycDist (a 0) (a 1)) *
            ‖pairK β M t (σ 0) (σ 1) (a 0) (a 1)‖) := by ring
      _ ≤ CKK / (1 - t) := hpt t ht0 htT _ _ _ _
      _ = CKK * (1 - t)⁻¹ := div_eq_mul_inv _ _
  · have hexp' : ∀ c : Fin L, Real.exp (θ * wordDiam (Function.update a j c)) *
        ‖primF β M m t (Function.update a j c) σ‖ =
        β⁻¹ * (Real.exp (θ * wordDiam (Function.update a j c)) *
        ‖pairK β M t (σ 0) (σ 1) ((Function.update a j c) 0) ((Function.update a j c) 1)‖) := by
      intro c
      rw [hkey]; ring
    simp only [hexp']
    rw [hsum (fun c => Real.exp (θ * wordDiam (Function.update a j c)) *
        ‖pairK β M t (σ 0) (σ 1) ((Function.update a j c) 0) ((Function.update a j c) 1)‖), hpow]
    refine le_trans ?_ hA
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, Function.update_self,
        Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
      have hsymm : ∀ c, ‖pairK β M t (σ 0) (σ 1) c (a 1)‖ = ‖pairK β M t (σ 0) (σ 1) (a 1) c‖ := by
        intro c
        have := congrFun (congrFun (lgw_K_symm hD (abs_lt.mpr ⟨by linarith, ht1⟩) (σ 0) (σ 1))
          c) (a 1)
        rw [Matrix.transpose_apply] at this
        rw [this]
      refine le_trans (Finset.sum_le_sum fun c _ => ?_) (hrow t ht0 htT (σ 0) (σ 1) (a 1))
      rw [hsymm c]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      refine (hexp _).trans ?_
      simp only [Function.update_self, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
      rw [lgw_cd_comm]
    · simp only [Fin.mk_one, Fin.isValue, Function.update_self,
        Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
      refine le_trans (Finset.sum_le_sum fun c _ => ?_) (hrow t ht0 htT (σ 0) (σ 1) (a 0))
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      refine (hexp _).trans ?_
      simp only [Function.update_self, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
      exact le_rfl

end WeightedA

/-! ## The weighted bound -/

/-- `|log(1 - t')| ≤ |log(1 - t)|` for `0 ≤ t' ≤ t < 1`. -/
private lemma lgk_log_mono {t t' : ℝ} (ht0 : 0 ≤ t') (htt : t' ≤ t) (ht1 : t < 1) :
    |Real.log (1 - t')| ≤ |Real.log (1 - t)| := by
  have h1 : 0 < 1 - t := by linarith
  have h2 : Real.log (1 - t') ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have h3 : Real.log (1 - t) ≤ Real.log (1 - t') := Real.log_le_log h1 (by linarith)
  rw [abs_of_nonpos h2, abs_of_nonpos (h3.trans h2)]
  linarith

/-- `ℓ = min{L, g²/√(1 - t)}` is nondecreasing in `t`. -/
private lemma lgk_ell_mono {g : ℝ} {L : ℕ} {t t' : ℝ} (htt : t' ≤ t) (ht1 : t < 1) :
    min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t')) ≤ min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t)) := by
  refine min_le_min le_rfl (div_le_div_of_nonneg_left (sq_nonneg g)
    (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_le_sqrt (by linarith)))

/-! ## Mixed trees: the dissections with a prescribed set of mixed diagonals -/

section Tree

variable {L : ℕ}

/-- The external factor of the side `s`: the one-label inverse, or the identity if `s` is the
undressed side `u`. -/
private def lgLeg (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) {n : ℕ} (σ : Fin n → Bool)
    (u : Option (Fin n)) (s : Fin n) (x y : Fin L) : ℂ :=
  if u = some s then (if x = y then 1 else 0) else pairV β M t (σ s) (σ (finRotate n s)) x y

/-- The diagonals of `F` joining opposite signs. -/
private def lgMix {n : ℕ} (σ : Fin n → Bool) (F : Finset (Fin n × Fin n)) :
    Finset (Fin n × Fin n) :=
  F.filter (fun d => σ d.1 ≠ σ d.2)

/-- The dressed value of one dissection, with the side `u` undressed. -/
private def lgPhi (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) {n : ℕ} (σ : Fin n → Bool)
    (u : Option (Fin n)) (F : Finset (Fin n × Fin n)) (x : Fin n → Fin L) : ℂ :=
  ∑ y : Fin n → Fin L, (∏ s, lgLeg β M t σ u s (x s) (y s)) * dissCore β M t σ F y

/-- The sum of the dressed values over the dissections whose mixed diagonals are `G`. -/
private def lgT (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) {n : ℕ} (σ : Fin n → Bool)
    (G : Finset (Fin n × Fin n)) (u : Option (Fin n)) (x : Fin n → Fin L) : ℂ :=
  ∑ F ∈ (dissections n).filter (fun F => lgMix σ F = G), lgPhi β M t σ u F x

/-- The external sides and the core of a dissection containing `(i, j)` split into those of the
two polygons of the cut, joined by the link of `(i, j)`. -/
private lemma lgt_core_split {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {t : ℝ} {n : ℕ}
    {σ : Fin n → Bool} {i j : Fin n} (hd : (i, j) ∈ polyDiags n)
    {F : Finset (Fin n × Fin n)} (hF : F ∈ dissections n) (hdF : (i, j) ∈ F)
    (W : Fin n → Fin L → Fin L → ℂ) (x : Fin n → Fin L) :
    ∑ y : Fin n → Fin L, (∏ s, W s (x s) (y s)) * dissCore β M t σ F y =
      ∑ zL : Fin (n + i - j + 1) → Fin L, ∑ zR : Fin (j - i + 1) → Fin L,
        (∏ p ∈ Finset.univ.erase (lgs_iL i j), W (lgs_vL i j p) (x (lgs_vL i j p)) (zL p)) *
        (∏ q ∈ Finset.univ.erase (lgs_lastR i j), W (lgs_vR i j q) (x (lgs_vR i j q)) (zR q)) *
        (((β * t : ℝ) : ℂ) • pairV β M t (σ i) (σ j)) (zL (lgs_iL i j)) (zR (lgs_lastR i j)) *
        dissCore β M t (cutLSgn σ i j) (lgs_splitL i j F) zL *
        dissCore β M t (cutRSgn σ i j) (lgs_splitR i j F) zR := by
  rw [lgs_sum_labels hd (fun zL zR =>
    (∏ p ∈ Finset.univ.erase (lgs_iL i j), W (lgs_vL i j p) (x (lgs_vL i j p)) (zL p)) *
        (∏ q ∈ Finset.univ.erase (lgs_lastR i j), W (lgs_vR i j q) (x (lgs_vR i j q)) (zR q)) *
        (((β * t : ℝ) : ℂ) • pairV β M t (σ i) (σ j)) (zL (lgs_iL i j)) (zR (lgs_lastR i j)) *
        dissCore β M t (cutLSgn σ i j) (lgs_splitL i j F) zL *
        dissCore β M t (cutRSgn σ i j) (lgs_splitR i j F) zR)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [lgs_dissCore_eq_coreX (i := i) (j := j) y, lgs_coreX_split hd hF hdF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun xo _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun xi _ => ?_
  have hL : ∏ p ∈ Finset.univ.erase (lgs_iL i j), W (lgs_vL i j p) (x (lgs_vL i j p))
      (if p.val = i.val then xo else y (lgs_vL i j p)) =
      ∏ p ∈ Finset.univ.erase (lgs_iL i j), W (lgs_vL i j p) (x (lgs_vL i j p))
        (y (lgs_vL i j p)) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp' : p.val ≠ i.val := fun h => (Finset.mem_erase.mp hp).1 (Fin.ext h)
    rw [ite_eq_right hp']
  have hR : ∏ q ∈ Finset.univ.erase (lgs_lastR i j), W (lgs_vR i j q) (x (lgs_vR i j q))
      (if q.val = j.val - i.val then xi else y (lgs_vR i j q)) =
      ∏ q ∈ Finset.univ.erase (lgs_lastR i j), W (lgs_vR i j q) (x (lgs_vR i j q))
        (y (lgs_vR i j q)) := by
    refine Finset.prod_congr rfl fun q hq => ?_
    have hq' : q.val ≠ j.val - i.val := fun h => (Finset.mem_erase.mp hq).1 (Fin.ext h)
    rw [ite_eq_right hq']
  have hiL : (lgs_iL i j).val = i.val := rfl
  have hlR : (lgs_lastR i j).val = j.val - i.val := rfl
  simp only [hL, hR, hiL, hlR, ite_true]
  rw [lgs_prod_sides hd (fun s => W s (x s) (y s))]
  ring

/-- The sides of the polygon of Cut_L other than the cut keep their factors. -/
private lemma lgt_legL {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {t : ℝ} {n : ℕ} (σ : Fin n → Bool)
    {i j : Fin n} (hd : (i, j) ∈ polyDiags n) (u : Option (Fin n))
    (hu : ∀ s, u = some s → s.val < i.val ∨ j.val ≤ s.val) (p : Fin (n + i - j + 1))
    (hp : p.val ≠ i.val) (w₁ w₂ : Fin L) :
    lgLeg β M t (cutLSgn σ i j) (u.map (lgs_uL i j)) p w₁ w₂ =
      lgLeg β M t σ u (lgs_vL i j p) w₁ w₂ := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  have hiff : u.map (lgs_uL i j) = some p ↔ u = some (lgs_vL i j p) := by
    constructor
    · intro h
      obtain ⟨s, hs, hsp⟩ := Option.map_eq_some_iff.mp h
      subst hs
      rw [← hsp, lgs_vL_uL (by rcases hu s rfl with h | h <;> omega)]
    · intro h
      rw [h, Option.map_some, lgs_uL_vL hij]
  unfold lgLeg
  rw [lgs_cutLSgn_eq, lgs_cutLSgn_eq, lgs_vL_rot hd hp]
  by_cases h : u = some (lgs_vL i j p)
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hiff.mp h')), ite_eq_right h]

/-- The sides of the polygon of Cut_R other than the cut keep their factors. -/
private lemma lgt_legR {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {t : ℝ} {n : ℕ} (σ : Fin n → Bool)
    {i j : Fin n} (hd : (i, j) ∈ polyDiags n) (u : Option (Fin n))
    (hu : ∀ s, u = some s → i.val ≤ s.val ∧ s.val < j.val) (q : Fin (j - i + 1))
    (hq : q.val ≠ j.val - i.val) (w₁ w₂ : Fin L) :
    lgLeg β M t (cutRSgn σ i j) (u.map (lgs_uR i j)) q w₁ w₂ =
      lgLeg β M t σ u (lgs_vR i j q) w₁ w₂ := by
  have hiff : u.map (lgs_uR i j) = some q ↔ u = some (lgs_vR i j q) := by
    constructor
    · intro h
      obtain ⟨s, hs, hsq⟩ := Option.map_eq_some_iff.mp h
      subst hs
      rw [← hsq, lgs_vR_uR (by have := hu s rfl; omega)]
    · intro h
      rw [h, Option.map_some, lgs_uR_vR]
  unfold lgLeg
  rw [lgs_cutRSgn_eq, lgs_cutRSgn_eq, lgs_vR_rot hd hq]
  by_cases h : u = some (lgs_vR i j q)
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hiff.mp h')), ite_eq_right h]

/-- The sides of Cut_L other than the cut, all dressed. -/
private lemma lgt_legL_dressed {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {t : ℝ} {n : ℕ}
    (σ : Fin n → Bool) {i j : Fin n} (hd : (i, j) ∈ polyDiags n) (u : Option (Fin n))
    (hu : ∀ s, u = some s → i.val ≤ s.val ∧ s.val < j.val) (p : Fin (n + i - j + 1))
    (hp : p.val ≠ i.val) (w₁ w₂ : Fin L) :
    lgLeg β M t (cutLSgn σ i j) (some (lgs_iL i j)) p w₁ w₂ =
      lgLeg β M t σ u (lgs_vL i j p) w₁ w₂ := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  have h1 : ¬(some (lgs_iL i j) = some p) := fun h => hp (by
    have := congrArg Fin.val (Option.some_injective _ h); simp [lgs_iL] at this; omega)
  have h2 : ¬(u = some (lgs_vL i j p)) := by
    intro h
    have := hu _ h
    have cp := lgs_vL_cases i j p
    omega
  unfold lgLeg
  rw [ite_eq_right h1, ite_eq_right h2, lgs_cutLSgn_eq, lgs_cutLSgn_eq, lgs_vL_rot hd hp]

/-- The sides of Cut_R other than the cut, all dressed. -/
private lemma lgt_legR_dressed {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {t : ℝ} {n : ℕ}
    (σ : Fin n → Bool) {i j : Fin n} (hd : (i, j) ∈ polyDiags n) (u : Option (Fin n))
    (hu : ∀ s, u = some s → s.val < i.val ∨ j.val ≤ s.val) (q : Fin (j - i + 1))
    (hq : q.val ≠ j.val - i.val) (w₁ w₂ : Fin L) :
    lgLeg β M t (cutRSgn σ i j) (some (lgs_lastR i j)) q w₁ w₂ =
      lgLeg β M t σ u (lgs_vR i j q) w₁ w₂ := by
  have h1 : ¬(some (lgs_lastR i j) = some q) := fun h => hq (by
    have := congrArg Fin.val (Option.some_injective _ h); simp [lgs_lastR] at this; omega)
  have h2 : ¬(u = some (lgs_vR i j q)) := by
    intro h
    have h3 := hu _ h
    have h4 := q.isLt
    simp only [lgs_vR_val] at h3
    omega
  unfold lgLeg
  rw [ite_eq_right h1, ite_eq_right h2, lgs_cutRSgn_eq, lgs_cutRSgn_eq, lgs_vR_rot hd hq]

/-- Summing a factor against the identity on the other side collapses the label. -/
private lemma lgt_collapse {A B : Type*} [Fintype A] [Fintype B] (κ : ℂ) (X : A → Fin L → ℂ)
    (pR : B → Fin L) (Y : B → ℂ) :
    κ * ∑ z, (∑ a, X a z) * (∑ b, (if z = pR b then 1 else 0) * Y b) =
      ∑ a, ∑ b, κ * X a (pR b) * Y b := by
  calc κ * ∑ z, (∑ a, X a z) * (∑ b, (if z = pR b then 1 else 0) * Y b)
      = ∑ z, ∑ a, ∑ b, κ * (X a z * ((if z = pR b then 1 else 0) * Y b)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ a, ∑ b, ∑ z, κ * (X a z * ((if z = pR b then 1 else 0) * Y b)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
    _ = _ := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [Fintype.sum_eq_single (pR b) (fun z hz => by rw [ite_eq_right hz]; ring)]
        rw [ite_eq_left rfl]; ring

/-- The mirror form of `lgt_collapse`. -/
private lemma lgt_collapse' {A B : Type*} [Fintype A] [Fintype B] (κ : ℂ) (pL : A → Fin L)
    (X : A → ℂ) (Y : B → Fin L → ℂ) :
    κ * ∑ z, (∑ a, (if z = pL a then 1 else 0) * X a) * (∑ b, Y b z) =
      ∑ a, ∑ b, κ * X a * Y b (pL a) := by
  calc κ * ∑ z, (∑ a, (if z = pL a then 1 else 0) * X a) * (∑ b, Y b z)
      = ∑ z, ∑ a, ∑ b, κ * ((if z = pL a then 1 else 0) * X a * Y b z) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ a, ∑ b, ∑ z, κ * ((if z = pL a then 1 else 0) * X a * Y b z) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
    _ = _ := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [Fintype.sum_eq_single (pL a) (fun z hz => by rw [ite_eq_right hz]; ring)]
        rw [ite_eq_left rfl]; ring

private lemma lgt_vL_iL {n : ℕ} (i j : Fin n) : lgs_vL i j (lgs_iL i j) = i := by
  apply Fin.ext; rw [lgs_vL_val]; simp [lgs_iL]

private lemma lgt_vR_lastR {n : ℕ} {i j : Fin n} (hd : (i, j) ∈ polyDiags n) :
    lgs_vR i j (lgs_lastR i j) = j := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  apply Fin.ext; rw [lgs_vR_val]; simp only [lgs_lastR]; omega

/-- Splitting a dressed dissection value along `(i, j)`, with the cut undressed on the side of
Cut_R (the undressed side `u`, if any, lies in Cut_L). -/
private lemma lgt_phi_splitR {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} (hD : PrimData β M m)
    (t : ℝ) {n : ℕ} (σ : Fin n → Bool) {i j : Fin n} (hd : (i, j) ∈ polyDiags n)
    {F : Finset (Fin n × Fin n)} (hF : F ∈ dissections n) (hdF : (i, j) ∈ F)
    (u : Option (Fin n)) (hu : ∀ s, u = some s → s.val < i.val ∨ j.val ≤ s.val)
    (x : Fin n → Fin L) :
    lgPhi β M t σ u F x = ((β * t : ℝ) : ℂ) * ∑ z : Fin L,
      lgPhi β M t (cutLSgn σ i j) (u.map (lgs_uL i j)) (lgs_splitL i j F) (cutLLab x i j z) *
      lgPhi β M t (cutRSgn σ i j) (some (lgs_lastR i j)) (lgs_splitR i j F)
        (cutRLab x i j z) := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  have hLz : ∀ z : Fin L, ∑ zL, (∏ p, lgLeg β M t (cutLSgn σ i j) (u.map (lgs_uL i j)) p
      (cutLLab x i j z p) (zL p)) * dissCore β M t (cutLSgn σ i j) (lgs_splitL i j F) zL =
      ∑ zL, pairV β M t (σ i) (σ j) z (zL (lgs_iL i j)) *
        ((∏ p ∈ Finset.univ.erase (lgs_iL i j), lgLeg β M t σ u (lgs_vL i j p)
          (x (lgs_vL i j p)) (zL p)) * dissCore β M t (cutLSgn σ i j) (lgs_splitL i j F) zL) := by
    intro z
    refine Finset.sum_congr rfl fun zL _ => ?_
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (lgs_iL i j))]
    have hne : u.map (lgs_uL i j) ≠ some (lgs_iL i j) := by
      intro h
      obtain ⟨s, hs, hsi⟩ := Option.map_eq_some_iff.mp h
      have := congrArg Fin.val hsi
      rw [lgs_uL_val] at this
      simp only [lgs_iL] at this
      rcases hu s hs with h1 | h1 <;> split_ifs at this <;> omega
    have h0 : lgLeg β M t (cutLSgn σ i j) (u.map (lgs_uL i j)) (lgs_iL i j)
        (cutLLab x i j z (lgs_iL i j)) (zL (lgs_iL i j)) =
        pairV β M t (σ i) (σ j) z (zL (lgs_iL i j)) := by
      unfold lgLeg
      have hiL : (lgs_iL i j).val = i.val := rfl
      rw [ite_eq_right hne, lgs_cutLSgn_eq, lgs_cutLSgn_eq, lgt_vL_iL, lgs_vL_rot_iL hd,
        lgs_cutLLab_eq, ite_eq_left hiL]
    have h1 : ∏ p ∈ Finset.univ.erase (lgs_iL i j), lgLeg β M t (cutLSgn σ i j)
        (u.map (lgs_uL i j)) p (cutLLab x i j z p) (zL p) =
        ∏ p ∈ Finset.univ.erase (lgs_iL i j), lgLeg β M t σ u (lgs_vL i j p)
          (x (lgs_vL i j p)) (zL p) := by
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp' : p.val ≠ i.val := fun h => (Finset.mem_erase.mp hp).1 (Fin.ext h)
      rw [lgt_legL σ hd u hu p hp', lgs_cutLLab_eq, ite_eq_right hp']
    rw [h0, h1]; ring
  have hRz : ∀ z : Fin L, ∑ zR, (∏ q, lgLeg β M t (cutRSgn σ i j) (some (lgs_lastR i j)) q
      (cutRLab x i j z q) (zR q)) * dissCore β M t (cutRSgn σ i j) (lgs_splitR i j F) zR =
      ∑ zR, (if z = zR (lgs_lastR i j) then 1 else 0) *
        ((∏ q ∈ Finset.univ.erase (lgs_lastR i j), lgLeg β M t σ u (lgs_vR i j q)
          (x (lgs_vR i j q)) (zR q)) * dissCore β M t (cutRSgn σ i j) (lgs_splitR i j F) zR) := by
    intro z
    refine Finset.sum_congr rfl fun zR _ => ?_
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (lgs_lastR i j))]
    have h0 : lgLeg β M t (cutRSgn σ i j) (some (lgs_lastR i j)) (lgs_lastR i j)
        (cutRLab x i j z (lgs_lastR i j)) (zR (lgs_lastR i j)) =
        if z = zR (lgs_lastR i j) then 1 else 0 := by
      have hlR : (lgs_lastR i j).val = j.val - i.val := rfl
      unfold lgLeg
      rw [ite_eq_left rfl, lgs_cutRLab_eq, ite_eq_left hlR]
    have h1 : ∏ q ∈ Finset.univ.erase (lgs_lastR i j), lgLeg β M t (cutRSgn σ i j)
        (some (lgs_lastR i j)) q (cutRLab x i j z q) (zR q) =
        ∏ q ∈ Finset.univ.erase (lgs_lastR i j), lgLeg β M t σ u (lgs_vR i j q)
          (x (lgs_vR i j q)) (zR q) := by
      refine Finset.prod_congr rfl fun q hq => ?_
      have hq' : q.val ≠ j.val - i.val := fun h => (Finset.mem_erase.mp hq).1 (Fin.ext h)
      rw [lgt_legR_dressed σ hd u hu q hq', lgs_cutRLab_eq, ite_eq_right hq']
    rw [h0, h1]; ring
  unfold lgPhi
  simp only [hLz, hRz]
  rw [lgt_core_split hd hF hdF, lgt_collapse]
  refine Finset.sum_congr rfl fun zL _ => Finset.sum_congr rfl fun zR _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, lgk_V_symm hD t (σ i) (σ j) (zL (lgs_iL i j))]
  ring

/-- Splitting a dressed dissection value along `(i, j)`, with the cut undressed on the side of
Cut_L (the undressed side `u`, if any, lies in Cut_R). -/
private lemma lgt_phi_splitL {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} (t : ℝ) {n : ℕ}
    (σ : Fin n → Bool) {i j : Fin n} (hd : (i, j) ∈ polyDiags n)
    {F : Finset (Fin n × Fin n)} (hF : F ∈ dissections n) (hdF : (i, j) ∈ F)
    (u : Option (Fin n)) (hu : ∀ s, u = some s → i.val ≤ s.val ∧ s.val < j.val)
    (x : Fin n → Fin L) :
    lgPhi β M t σ u F x = ((β * t : ℝ) : ℂ) * ∑ z : Fin L,
      lgPhi β M t (cutLSgn σ i j) (some (lgs_iL i j)) (lgs_splitL i j F) (cutLLab x i j z) *
      lgPhi β M t (cutRSgn σ i j) (u.map (lgs_uR i j)) (lgs_splitR i j F)
        (cutRLab x i j z) := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  have hLz : ∀ z : Fin L, ∑ zL, (∏ p, lgLeg β M t (cutLSgn σ i j) (some (lgs_iL i j)) p
      (cutLLab x i j z p) (zL p)) * dissCore β M t (cutLSgn σ i j) (lgs_splitL i j F) zL =
      ∑ zL, (if z = zL (lgs_iL i j) then 1 else 0) *
        ((∏ p ∈ Finset.univ.erase (lgs_iL i j), lgLeg β M t σ u (lgs_vL i j p)
          (x (lgs_vL i j p)) (zL p)) * dissCore β M t (cutLSgn σ i j) (lgs_splitL i j F) zL) := by
    intro z
    refine Finset.sum_congr rfl fun zL _ => ?_
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (lgs_iL i j))]
    have h0 : lgLeg β M t (cutLSgn σ i j) (some (lgs_iL i j)) (lgs_iL i j)
        (cutLLab x i j z (lgs_iL i j)) (zL (lgs_iL i j)) =
        if z = zL (lgs_iL i j) then 1 else 0 := by
      have hiL : (lgs_iL i j).val = i.val := rfl
      unfold lgLeg
      rw [ite_eq_left rfl, lgs_cutLLab_eq, ite_eq_left hiL]
    have h1 : ∏ p ∈ Finset.univ.erase (lgs_iL i j), lgLeg β M t (cutLSgn σ i j)
        (some (lgs_iL i j)) p (cutLLab x i j z p) (zL p) =
        ∏ p ∈ Finset.univ.erase (lgs_iL i j), lgLeg β M t σ u (lgs_vL i j p)
          (x (lgs_vL i j p)) (zL p) := by
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp' : p.val ≠ i.val := fun h => (Finset.mem_erase.mp hp).1 (Fin.ext h)
      rw [lgt_legL_dressed σ hd u hu p hp', lgs_cutLLab_eq, ite_eq_right hp']
    rw [h0, h1]; ring
  have hRz : ∀ z : Fin L, ∑ zR, (∏ q, lgLeg β M t (cutRSgn σ i j) (u.map (lgs_uR i j)) q
      (cutRLab x i j z q) (zR q)) * dissCore β M t (cutRSgn σ i j) (lgs_splitR i j F) zR =
      ∑ zR, pairV β M t (σ i) (σ j) z (zR (lgs_lastR i j)) *
        ((∏ q ∈ Finset.univ.erase (lgs_lastR i j), lgLeg β M t σ u (lgs_vR i j q)
          (x (lgs_vR i j q)) (zR q)) * dissCore β M t (cutRSgn σ i j) (lgs_splitR i j F) zR) := by
    intro z
    refine Finset.sum_congr rfl fun zR _ => ?_
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (lgs_lastR i j))]
    have hne : u.map (lgs_uR i j) ≠ some (lgs_lastR i j) := by
      intro h
      obtain ⟨s, hs, hsi⟩ := Option.map_eq_some_iff.mp h
      have h3 := congrArg Fin.val hsi
      rw [lgs_uR_val] at h3
      simp only [lgs_lastR] at h3
      have h4 := hu s hs
      split_ifs at h3 <;> omega
    have h0 : lgLeg β M t (cutRSgn σ i j) (u.map (lgs_uR i j)) (lgs_lastR i j)
        (cutRLab x i j z (lgs_lastR i j)) (zR (lgs_lastR i j)) =
        pairV β M t (σ i) (σ j) z (zR (lgs_lastR i j)) := by
      unfold lgLeg
      have hlR : (lgs_lastR i j).val = j.val - i.val := rfl
      rw [ite_eq_right hne, lgs_cutRSgn_eq, lgs_cutRSgn_eq, lgt_vR_lastR hd, lgs_vR_rot_lastR hd,
        lgs_cutRLab_eq, ite_eq_left hlR, lgk_pairV_swap]
    have h1 : ∏ q ∈ Finset.univ.erase (lgs_lastR i j), lgLeg β M t (cutRSgn σ i j)
        (u.map (lgs_uR i j)) q (cutRLab x i j z q) (zR q) =
        ∏ q ∈ Finset.univ.erase (lgs_lastR i j), lgLeg β M t σ u (lgs_vR i j q)
          (x (lgs_vR i j q)) (zR q) := by
      refine Finset.prod_congr rfl fun q hq => ?_
      have hq' : q.val ≠ j.val - i.val := fun h => (Finset.mem_erase.mp hq).1 (Fin.ext h)
      rw [lgt_legR σ hd u hu q hq', lgs_cutRLab_eq, ite_eq_right hq']
    rw [h0, h1]; ring
  unfold lgPhi
  simp only [hLz, hRz]
  rw [lgt_core_split hd hF hdF, lgt_collapse']
  refine Finset.sum_congr rfl fun zL _ => Finset.sum_congr rfl fun zR _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  ring

/-- The mixed diagonals of the polygon of Cut_L are the mixed diagonals of `F` there. -/
private lemma lgt_mix_splitL {n : ℕ} (σ : Fin n → Bool) (i j : Fin n) (F : Finset (Fin n × Fin n)) :
    lgMix (cutLSgn σ i j) (lgs_splitL i j F) = lgs_splitL i j (lgMix σ F) := by
  ext e
  simp only [lgMix, Finset.mem_filter, lgs_mem_splitL, lgs_cutLSgn_eq]
  tauto

/-- The mixed diagonals of the polygon of Cut_R are the mixed diagonals of `F` there. -/
private lemma lgt_mix_splitR {n : ℕ} (σ : Fin n → Bool) (i j : Fin n) (F : Finset (Fin n × Fin n)) :
    lgMix (cutRSgn σ i j) (lgs_splitR i j F) = lgs_splitR i j (lgMix σ F) := by
  ext e
  rw [lgMix, lgMix, Finset.mem_filter, lgs_mem_splitR, lgs_mem_splitR, Finset.mem_filter]
  simp only [lgs_cutRSgn_eq]
  tauto

/-- The mixed diagonals of a dissection form a dissection. -/
private lemma lgt_mix_mem {n : ℕ} (σ : Fin n → Bool) {F : Finset (Fin n × Fin n)}
    (hF : F ∈ dissections n) : lgMix σ F ∈ dissections n := by
  rw [lgs_mem_dissections] at hF ⊢
  exact ⟨(Finset.filter_subset _ _).trans hF.1, fun d hd e he =>
    hF.2 d (Finset.mem_of_mem_filter _ hd) e (Finset.mem_of_mem_filter _ he)⟩

/-- A dissection containing the mixed diagonal `(i, j)` has the mixed diagonals `G ∋ (i, j)` if
and only if its two parts have the two parts of `G`. -/
private lemma lgt_mix_iff {n : ℕ} (σ : Fin n → Bool) {i j : Fin n} (hd : (i, j) ∈ polyDiags n)
    (hmix : σ i ≠ σ j) {F G : Finset (Fin n × Fin n)} (hF : F ∈ dissections n)
    (hdF : (i, j) ∈ F) (hG : G ∈ dissections n) (hdG : (i, j) ∈ G) :
    lgMix σ F = G ↔ lgMix (cutLSgn σ i j) (lgs_splitL i j F) = lgs_splitL i j G ∧
      lgMix (cutRSgn σ i j) (lgs_splitR i j F) = lgs_splitR i j G := by
  rw [lgt_mix_splitL, lgt_mix_splitR]
  constructor
  · intro h; rw [h]; exact ⟨rfl, rfl⟩
  · rintro ⟨hL, hR⟩
    have hmF := lgt_mix_mem σ hF
    have hdm : (i, j) ∈ lgMix σ F := Finset.mem_filter.mpr ⟨hdF, hmix⟩
    rw [← lgs_glue_split hd hmF hdm, ← lgs_glue_split hd hG hdG, hL, hR]

/-- The sums over pairs of dissections of the two polygons factorize. -/
private lemma lgt_alg {α γ : Type*} (dL : Finset α) (dR : Finset γ) (pL : α → Prop) (pR : γ → Prop)
    [DecidablePred pL] [DecidablePred pR] (κ : ℂ) (aL : α → Fin L → ℂ) (aR : γ → Fin L → ℂ) :
    ∑ FL ∈ dL, ∑ FR ∈ dR, (if pL FL ∧ pR FR then κ * ∑ z, aL FL z * aR FR z else 0) =
      κ * ∑ z, (∑ FL ∈ dL.filter pL, aL FL z) * (∑ FR ∈ dR.filter pR, aR FR z) := by
  simp only [Finset.sum_filter]
  calc ∑ FL ∈ dL, ∑ FR ∈ dR, (if pL FL ∧ pR FR then κ * ∑ z, aL FL z * aR FR z else 0)
      = ∑ FL ∈ dL, ∑ FR ∈ dR, ∑ z, κ * ((if pL FL then aL FL z else 0) *
          (if pR FR then aR FR z else 0)) := by
        refine Finset.sum_congr rfl fun FL _ => Finset.sum_congr rfl fun FR _ => ?_
        by_cases h1 : pL FL <;> by_cases h2 : pR FR <;> simp [h1, h2, Finset.mul_sum]
    _ = ∑ FL ∈ dL, ∑ z, ∑ FR ∈ dR, κ * ((if pL FL then aL FL z else 0) *
          (if pR FR then aR FR z else 0)) :=
        Finset.sum_congr rfl fun FL _ => Finset.sum_comm
    _ = ∑ z, ∑ FL ∈ dL, ∑ FR ∈ dR, κ * ((if pL FL then aL FL z else 0) *
          (if pR FR then aR FR z else 0)) := Finset.sum_comm
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun FL _ => ?_
        rw [Finset.mul_sum]

/-- The restriction to the dissections with mixed diagonals `G ∋ (i, j)`. -/
private lemma lgt_T_restrict {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} (t : ℝ) {n : ℕ}
    (σ : Fin n → Bool) {i j : Fin n} (hd : (i, j) ∈ polyDiags n) (hmix : σ i ≠ σ j)
    {G : Finset (Fin n × Fin n)} (hG : G ∈ dissections n) (hdG : (i, j) ∈ G)
    (u : Option (Fin n)) (x : Fin n → Fin L) (Ψ : Finset (Fin (n + i - j + 1) ×
      Fin (n + i - j + 1)) → Finset (Fin (j - i + 1) × Fin (j - i + 1)) → ℂ)
    (hΨ : ∀ F ∈ dissections n, (i, j) ∈ F →
      lgPhi β M t σ u F x = Ψ (lgs_splitL i j F) (lgs_splitR i j F)) :
    lgT β M t σ G u x = ∑ FL ∈ dissections (n + i - j + 1), ∑ FR ∈ dissections (j - i + 1),
      (if lgMix (cutLSgn σ i j) FL = lgs_splitL i j G ∧
          lgMix (cutRSgn σ i j) FR = lgs_splitR i j G then Ψ FL FR else 0) := by
  unfold lgT
  rw [← lgs_sum_split hd]
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun F hF => ?_
  by_cases hdF : (i, j) ∈ F
  · rw [ite_eq_left hdF]
    by_cases hFG : lgMix σ F = G
    · rw [ite_eq_left hFG, ite_eq_left ((lgt_mix_iff σ hd hmix hF hdF hG hdG).mp hFG),
        hΨ F hF hdF]
    · rw [ite_eq_right hFG,
        ite_eq_right (fun h => hFG ((lgt_mix_iff σ hd hmix hF hdF hG hdG).mpr h))]
  · have hFG : ¬lgMix σ F = G := fun h => hdF (by
      have h' : (i, j) ∈ lgMix σ F := h ▸ hdG
      exact (Finset.mem_filter.mp h').1)
    rw [ite_eq_right hFG, ite_eq_right hdF]

/-- The mixed-tree sum splits along a mixed diagonal `(i, j) ∈ G`, with the cut undressed
on the side of Cut_R. -/
private lemma lgt_T_splitR {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} (hD : PrimData β M m)
    (t : ℝ) {n : ℕ} (σ : Fin n → Bool) {i j : Fin n} (hd : (i, j) ∈ polyDiags n)
    (hmix : σ i ≠ σ j) {G : Finset (Fin n × Fin n)} (hG : G ∈ dissections n)
    (hdG : (i, j) ∈ G) (u : Option (Fin n))
    (hu : ∀ s, u = some s → s.val < i.val ∨ j.val ≤ s.val) (x : Fin n → Fin L) :
    lgT β M t σ G u x = ((β * t : ℝ) : ℂ) * ∑ z : Fin L,
      lgT β M t (cutLSgn σ i j) (lgs_splitL i j G) (u.map (lgs_uL i j)) (cutLLab x i j z) *
      lgT β M t (cutRSgn σ i j) (lgs_splitR i j G) (some (lgs_lastR i j)) (cutRLab x i j z) := by
  rw [lgt_T_restrict t σ hd hmix hG hdG u x (fun FL FR => ((β * t : ℝ) : ℂ) * ∑ z : Fin L,
      lgPhi β M t (cutLSgn σ i j) (u.map (lgs_uL i j)) FL (cutLLab x i j z) *
      lgPhi β M t (cutRSgn σ i j) (some (lgs_lastR i j)) FR (cutRLab x i j z))
    (fun F hF hdF => lgt_phi_splitR hD t σ hd hF hdF u hu x), lgt_alg]
  rfl

/-- The mixed-tree sum splits along a mixed diagonal `(i, j) ∈ G`, with the cut undressed
on the side of Cut_L. -/
private lemma lgt_T_splitL {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} (t : ℝ) {n : ℕ}
    (σ : Fin n → Bool) {i j : Fin n} (hd : (i, j) ∈ polyDiags n)
    (hmix : σ i ≠ σ j) {G : Finset (Fin n × Fin n)} (hG : G ∈ dissections n)
    (hdG : (i, j) ∈ G) (u : Option (Fin n))
    (hu : ∀ s, u = some s → i.val ≤ s.val ∧ s.val < j.val) (x : Fin n → Fin L) :
    lgT β M t σ G u x = ((β * t : ℝ) : ℂ) * ∑ z : Fin L,
      lgT β M t (cutLSgn σ i j) (lgs_splitL i j G) (some (lgs_iL i j)) (cutLLab x i j z) *
      lgT β M t (cutRSgn σ i j) (lgs_splitR i j G) (u.map (lgs_uR i j)) (cutRLab x i j z) := by
  rw [lgt_T_restrict t σ hd hmix hG hdG u x (fun FL FR => ((β * t : ℝ) : ℂ) * ∑ z : Fin L,
      lgPhi β M t (cutLSgn σ i j) (some (lgs_iL i j)) FL (cutLLab x i j z) *
      lgPhi β M t (cutRSgn σ i j) (u.map (lgs_uR i j)) FR (cutRLab x i j z))
    (fun F hF hdF => lgt_phi_splitL t σ hd hF hdF u hu x), lgt_alg]
  rfl

/-- One join, pointwise: Theorem B.7 [uvp:thm:tree]. -/
private lemma lgt_glue_pt {κ : ℂ} {b P R : ℝ} (hκ : ‖κ‖ ≤ b) (hP : 0 ≤ P) (f g : Fin L → ℂ)
    (hf : ∀ z, ‖f z‖ ≤ P) (hg : ∑ z, ‖g z‖ ≤ R) : ‖κ * ∑ z, f z * g z‖ ≤ b * (P * R) := by
  rw [norm_mul]
  refine mul_le_mul hκ ?_ (norm_nonneg _) ((norm_nonneg _).trans hκ)
  calc ‖∑ z, f z * g z‖ ≤ ∑ z, ‖f z‖ * ‖g z‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => by rw [norm_mul])
    _ ≤ ∑ z, P * ‖g z‖ := Finset.sum_le_sum fun z _ =>
        mul_le_mul_of_nonneg_right (hf z) (norm_nonneg _)
    _ = P * ∑ z, ‖g z‖ := by rw [Finset.mul_sum]
    _ ≤ P * R := mul_le_mul_of_nonneg_left hg hP

/-- One join, retained row on the side of `f`: Theorem B.7 [uvp:thm:tree]. -/
private lemma lgt_glue_rowL {κ : ℂ} {b P R : ℝ} (hκ : ‖κ‖ ≤ b) (hP : 0 ≤ P) (f : Fin L → Fin L → ℂ)
    (g : Fin L → ℂ) (hf : ∀ z, ∑ w, ‖f w z‖ ≤ P) (hg : ∑ z, ‖g z‖ ≤ R) :
    ∑ w, ‖κ * ∑ z, f w z * g z‖ ≤ b * (P * R) := by
  have hb : 0 ≤ b := (norm_nonneg _).trans hκ
  calc ∑ w, ‖κ * ∑ z, f w z * g z‖ ≤ ∑ w, b * ∑ z, ‖f w z‖ * ‖g z‖ := by
        refine Finset.sum_le_sum fun w _ => ?_
        rw [norm_mul]
        exact mul_le_mul hκ ((norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => by
          rw [norm_mul])) (norm_nonneg _) hb
    _ = b * ∑ z, (∑ w, ‖f w z‖) * ‖g z‖ := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [Finset.sum_mul]
    _ ≤ b * ∑ z, P * ‖g z‖ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ =>
        mul_le_mul_of_nonneg_right (hf z) (norm_nonneg _)) hb
    _ ≤ b * (P * R) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg hP) hb

/-- One join, retained row on the side of `g`: Theorem B.7 [uvp:thm:tree]. -/
private lemma lgt_glue_rowR {κ : ℂ} {b P R : ℝ} (hκ : ‖κ‖ ≤ b) (hR : 0 ≤ R) (f : Fin L → ℂ)
    (g : Fin L → Fin L → ℂ) (hf : ∑ z, ‖f z‖ ≤ P) (hg : ∀ z, ∑ w, ‖g w z‖ ≤ R) :
    ∑ w, ‖κ * ∑ z, f z * g w z‖ ≤ b * (P * R) := by
  have h := lgt_glue_rowL hκ hR g f hg hf
  calc ∑ w, ‖κ * ∑ z, f z * g w z‖ = ∑ w, ‖κ * ∑ z, g w z * f z‖ := by
        simp only [mul_comm (f _)]
    _ ≤ b * (R * P) := h
    _ = b * (P * R) := by ring

/-- The bounds of the mixed-tree sums of words of length `n`: pointwise
`K^{n-2} A^{n-1}`, and `K^{n-2} a A^{n-2}` for every undressed row at a mixed side. -/
private def lgBnd (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t K a A : ℝ) (n : ℕ) : Prop :=
  ∀ (σ : Fin n → Bool) (G : Finset (Fin n × Fin n)),
    (∀ x, ‖lgT β M t σ G none x‖ ≤ K ^ (n - 2) * A ^ (n - 1)) ∧
    ∀ v : Fin n, σ v ≠ σ (finRotate n v) → ∀ x : Fin n → Fin L,
      ∑ xv : Fin L, ‖lgT β M t σ G (some v) (Function.update x v xv)‖ ≤
        K ^ (n - 2) * (a * A ^ (n - 2))

private lemma lgt_cutRLab_update {α : Type*} {n : ℕ} (x : Fin n → α) (i j : Fin n) (z z₀ : α) :
    cutRLab x i j z = Function.update (cutRLab x i j z₀) (lgs_lastR i j) z := by
  funext q
  rw [lgs_cutRLab_eq, Function.update_apply, lgs_cutRLab_eq]
  by_cases hq : q = lgs_lastR i j
  · rw [ite_eq_left hq, ite_eq_left (by rw [hq]; rfl)]
  · have : q.val ≠ j.val - i.val := fun h => hq (Fin.ext h)
    rw [ite_eq_right hq, ite_eq_right this, ite_eq_right this]

private lemma lgt_cutLLab_update {α : Type*} {n : ℕ} (x : Fin n → α) (i j : Fin n) (z z₀ : α) :
    cutLLab x i j z = Function.update (cutLLab x i j z₀) (lgs_iL i j) z := by
  funext p
  rw [lgs_cutLLab_eq, Function.update_apply, lgs_cutLLab_eq]
  by_cases hp : p = lgs_iL i j
  · rw [ite_eq_left hp, ite_eq_left (by rw [hp]; rfl)]
  · have : p.val ≠ i.val := fun h => hp (Fin.ext h)
    rw [ite_eq_right hp, ite_eq_right this, ite_eq_right this]

private lemma lgt_cutLLab_updL {α : Type*} {n : ℕ} {i j : Fin n} (hd : (i, j) ∈ polyDiags n)
    (x : Fin n → α) (v : Fin n) (hv : v.val < i.val ∨ j.val ≤ v.val) (w z : α) :
    cutLLab (Function.update x v w) i j z =
      Function.update (cutLLab x i j z) (lgs_uL i j v) w := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  funext p
  rw [lgs_cutLLab_eq, Function.update_apply, Function.update_apply, lgs_cutLLab_eq]
  by_cases hp : p.val = i.val
  · have : p ≠ lgs_uL i j v := by
      intro h; rw [h, lgs_uL_val] at hp; split_ifs at hp <;> omega
    rw [ite_eq_left hp, ite_eq_left hp, ite_eq_right this]
  · rw [ite_eq_right hp, ite_eq_right hp]
    by_cases hpv : p = lgs_uL i j v
    · rw [ite_eq_left hpv, ite_eq_left (by rw [hpv, lgs_vL_uL (by omega)])]
    · have : lgs_vL i j p ≠ v := fun h => hpv (by rw [← h, lgs_uL_vL hij])
      rw [ite_eq_right hpv, ite_eq_right this]

private lemma lgt_cutRLab_updL {α : Type*} {n : ℕ} {i j : Fin n} (hd : (i, j) ∈ polyDiags n)
    (x : Fin n → α) (v : Fin n) (hv : v.val < i.val ∨ j.val ≤ v.val) (w z : α) :
    cutRLab (Function.update x v w) i j z = cutRLab x i j z := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  funext q
  rw [lgs_cutRLab_eq, lgs_cutRLab_eq]
  by_cases hq : q.val = j.val - i.val
  · rw [ite_eq_left hq, ite_eq_left hq]
  · rw [ite_eq_right hq, ite_eq_right hq, Function.update_apply, ite_eq_right]
    intro h
    have := q.isLt
    have h2 := congrArg Fin.val h
    rw [lgs_vR_val] at h2
    omega

private lemma lgt_cutRLab_updR {α : Type*} {n : ℕ} {i j : Fin n} (x : Fin n → α) (v : Fin n)
    (hv : i.val ≤ v.val ∧ v.val < j.val) (w z : α) :
    cutRLab (Function.update x v w) i j z =
      Function.update (cutRLab x i j z) (lgs_uR i j v) w := by
  funext q
  rw [lgs_cutRLab_eq, Function.update_apply, Function.update_apply, lgs_cutRLab_eq]
  by_cases hq : q.val = j.val - i.val
  · have : q ≠ lgs_uR i j v := by
      intro h; rw [h, lgs_uR_val] at hq; split_ifs at hq <;> omega
    rw [ite_eq_left hq, ite_eq_left hq, ite_eq_right this]
  · rw [ite_eq_right hq, ite_eq_right hq]
    by_cases hqv : q = lgs_uR i j v
    · rw [ite_eq_left hqv, ite_eq_left (by rw [hqv, lgs_vR_uR (by omega)])]
    · have : lgs_vR i j q ≠ v := fun h => hqv (by rw [← h, lgs_uR_vR])
      rw [ite_eq_right hqv, ite_eq_right this]

private lemma lgt_cutLLab_updR {α : Type*} {n : ℕ} {i j : Fin n} (x : Fin n → α) (v : Fin n)
    (hv : i.val ≤ v.val ∧ v.val < j.val) (w z : α) :
    cutLLab (Function.update x v w) i j z = cutLLab x i j z := by
  funext p
  rw [lgs_cutLLab_eq, lgs_cutLLab_eq]
  by_cases hp : p.val = i.val
  · rw [ite_eq_left hp, ite_eq_left hp]
  · rw [ite_eq_right hp, ite_eq_right hp, Function.update_apply, ite_eq_right]
    intro h
    have cp := lgs_vL_cases i j p
    have h2 := congrArg Fin.val h
    omega

/-- Signs of the cut sides. -/
private lemma lgt_sgn_lastR {n : ℕ} (σ : Fin n → Bool) {i j : Fin n} (hd : (i, j) ∈ polyDiags n) :
    cutRSgn σ i j (lgs_lastR i j) = σ j ∧
      cutRSgn σ i j (finRotate _ (lgs_lastR i j)) = σ i := by
  rw [lgs_cutRSgn_eq, lgs_cutRSgn_eq, lgt_vR_lastR hd, lgs_vR_rot_lastR hd]
  exact ⟨rfl, rfl⟩

private lemma lgt_sgn_iL {n : ℕ} (σ : Fin n → Bool) {i j : Fin n} (hd : (i, j) ∈ polyDiags n) :
    cutLSgn σ i j (lgs_iL i j) = σ i ∧ cutLSgn σ i j (finRotate _ (lgs_iL i j)) = σ j := by
  rw [lgs_cutLSgn_eq, lgs_cutLSgn_eq, lgt_vL_iL, lgs_vL_rot_iL hd]
  exact ⟨rfl, rfl⟩

private lemma lgt_sgn_uL {n : ℕ} (σ : Fin n → Bool) {i j : Fin n} (hd : (i, j) ∈ polyDiags n)
    (v : Fin n) (hv : v.val < i.val ∨ j.val ≤ v.val) :
    cutLSgn σ i j (lgs_uL i j v) = σ v ∧
      cutLSgn σ i j (finRotate _ (lgs_uL i j v)) = σ (finRotate n v) := by
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  have hne : (lgs_uL i j v).val ≠ i.val := by rw [lgs_uL_val]; split_ifs <;> omega
  rw [lgs_cutLSgn_eq, lgs_cutLSgn_eq, lgs_vL_rot hd hne, lgs_vL_uL (by omega)]
  exact ⟨rfl, rfl⟩

private lemma lgt_sgn_uR {n : ℕ} (σ : Fin n → Bool) {i j : Fin n} (hd : (i, j) ∈ polyDiags n)
    (v : Fin n) (hv : i.val ≤ v.val ∧ v.val < j.val) :
    cutRSgn σ i j (lgs_uR i j v) = σ v ∧
      cutRSgn σ i j (finRotate _ (lgs_uR i j v)) = σ (finRotate n v) := by
  have hne : (lgs_uR i j v).val ≠ j.val - i.val := by rw [lgs_uR_val]; split_ifs <;> omega
  rw [lgs_cutRSgn_eq, lgs_cutRSgn_eq, lgs_vR_rot hd hne, lgs_vR_uR (by omega)]
  exact ⟨rfl, rfl⟩

/-- Theorem B.7 [uvp:thm:tree]: the bounds of the stable molecules (the sums with no mixed
diagonal) give the bounds of all the mixed-tree sums, by induction on the length. -/
private lemma lgt_bounds {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} (hD : PrimData β M m)
    {t K a A : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hβa : β * a = 1) (ha : 0 < a) (hA : 1 ≤ A)
    (hK : 1 ≤ K) (N : ℕ)
    (hmol : ∀ n, 3 ≤ n → n ≤ N → ∀ σ : Fin n → Bool,
      (∀ x, ‖lgT β M t σ ∅ none x‖ ≤ K * A ^ (n - 1)) ∧
      ∀ v : Fin n, σ v ≠ σ (finRotate n v) → ∀ x : Fin n → Fin L,
        ∑ xv : Fin L, ‖lgT β M t σ ∅ (some v) (Function.update x v xv)‖ ≤
          K * (a * A ^ (n - 2))) :
    ∀ n, 3 ≤ n → n ≤ N → lgBnd β M t K a A n := by
  have hβ := hD.pos
  have hκ : ‖((β * t : ℝ) : ℂ)‖ ≤ a⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : β = a⁻¹ := by
      calc β = β * a * a⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ ha.ne', mul_one]
        _ = a⁻¹ := by rw [hβa, one_mul]
    rw [this]
    exact mul_le_of_le_one_right (inv_nonneg.mpr ha.le) ht1
  have hA0 : 0 ≤ A := by linarith
  have hK0 : 0 ≤ K := by linarith
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn hnN σ G
  by_cases hex : ∃ F ∈ dissections n, lgMix σ F = G
  swap
  · have h0 : ∀ u x, lgT β M t σ G u x = 0 := by
      intro u x
      unfold lgT
      refine Finset.sum_eq_zero fun F hF => ?_
      exact absurd ⟨F, (Finset.mem_filter.mp hF).1, (Finset.mem_filter.mp hF).2⟩ hex
    simp only [h0, norm_zero, Finset.sum_const_zero]
    exact ⟨fun x => by positivity, fun v _ x => by positivity⟩
  obtain ⟨F₀, hF₀, hF₀G⟩ := hex
  have hG : G ∈ dissections n := hF₀G ▸ lgt_mix_mem σ hF₀
  have hGmix : ∀ d ∈ G, σ d.1 ≠ σ d.2 := fun d hd => by
    rw [← hF₀G] at hd; exact (Finset.mem_filter.mp hd).2
  have hKp : K ≤ K ^ (n - 2) := le_self_pow₀ hK (by omega)
  rcases G.eq_empty_or_nonempty with hG0 | ⟨⟨i, j⟩, hdG⟩
  · subst hG0
    obtain ⟨h1, h2⟩ := hmol n hn hnN σ
    exact ⟨fun x => (h1 x).trans (mul_le_mul_of_nonneg_right hKp (by positivity)),
      fun v hv x => (h2 v hv x).trans (mul_le_mul_of_nonneg_right hKp (by positivity))⟩
  have hd : (i, j) ∈ polyDiags n := ((lgs_mem_dissections _).mp hG).1 hdG
  have hmix : σ i ≠ σ j := hGmix _ hdG
  have hdv := (lgs_mem_polyDiags _).mp hd
  simp only at hdv
  have hj := j.isLt
  have hL3 : 3 ≤ n + i.val - j.val + 1 := by omega
  have hLn : n + i.val - j.val + 1 < n := by omega
  have hR3 : 3 ≤ j.val - i.val + 1 := by omega
  have hRn : j.val - i.val + 1 < n := by omega
  obtain IHL := ih _ hLn hL3 (by omega) (cutLSgn σ i j) (lgs_splitL i j G)
  obtain IHR := ih _ hRn hR3 (by omega) (cutRSgn σ i j) (lgs_splitR i j G)
  have hRlast : cutRSgn σ i j (lgs_lastR i j) ≠
      cutRSgn σ i j (finRotate _ (lgs_lastR i j)) := by
    rw [(lgt_sgn_lastR σ hd).1, (lgt_sgn_lastR σ hd).2]; exact Ne.symm hmix
  have hLiL : cutLSgn σ i j (lgs_iL i j) ≠ cutLSgn σ i j (finRotate _ (lgs_iL i j)) := by
    rw [(lgt_sgn_iL σ hd).1, (lgt_sgn_iL σ hd).2]; exact hmix
  -- the rows of the two cut sides
  have hRrow : ∀ x : Fin n → Fin L, ∑ z, ‖lgT β M t (cutRSgn σ i j) (lgs_splitR i j G)
      (some (lgs_lastR i j)) (cutRLab x i j z)‖ ≤
        K ^ (j.val - i.val + 1 - 2) * (a * A ^ (j.val - i.val + 1 - 2)) := by
    intro x
    have := IHR.2 (lgs_lastR i j) hRlast (cutRLab x i j (x i))
    simpa only [← lgt_cutRLab_update] using this
  have hLrow : ∀ x : Fin n → Fin L, ∑ z, ‖lgT β M t (cutLSgn σ i j) (lgs_splitL i j G)
      (some (lgs_iL i j)) (cutLLab x i j z)‖ ≤
        K ^ (n + i.val - j.val + 1 - 2) * (a * A ^ (n + i.val - j.val + 1 - 2)) := by
    intro x
    have := IHL.2 (lgs_iL i j) hLiL (cutLLab x i j (x i))
    simpa only [← lgt_cutLLab_update] using this
  have hpK : K ^ (n + i.val - j.val + 1 - 2) * K ^ (j.val - i.val + 1 - 2) = K ^ (n - 2) := by
    rw [← pow_add]; congr 1; omega
  have hpA1 : A ^ (n + i.val - j.val + 1 - 1) * A ^ (j.val - i.val + 1 - 2) = A ^ (n - 1) := by
    rw [← pow_add]; congr 1; omega
  have hpA2 : A ^ (n + i.val - j.val + 1 - 2) * A ^ (j.val - i.val + 1 - 2) = A ^ (n - 2) := by
    rw [← pow_add]; congr 1; omega
  have haa : a⁻¹ * a = 1 := inv_mul_cancel₀ ha.ne'
  refine ⟨fun x => ?_, fun v hv x => ?_⟩
  · rw [lgt_T_splitR hD t σ hd hmix hG hdG none (by simp) x]
    refine (lgt_glue_pt hκ (by positivity) _ _ (fun z => IHL.1 _) (hRrow x)).trans
      (le_of_eq ?_)
    calc a⁻¹ * (K ^ (n + i.val - j.val + 1 - 2) * A ^ (n + i.val - j.val + 1 - 1) *
          (K ^ (j.val - i.val + 1 - 2) * (a * A ^ (j.val - i.val + 1 - 2))))
        = (a⁻¹ * a) * (K ^ (n + i.val - j.val + 1 - 2) * K ^ (j.val - i.val + 1 - 2)) *
          (A ^ (n + i.val - j.val + 1 - 1) * A ^ (j.val - i.val + 1 - 2)) := by ring
      _ = K ^ (n - 2) * A ^ (n - 1) := by rw [haa, hpK, hpA1, one_mul]
  · by_cases hvL : v.val < i.val ∨ j.val ≤ v.val
    · have hu : ∀ s, some v = some s → s.val < i.val ∨ j.val ≤ s.val := by
        intro s hs; rw [← Option.some_injective _ hs]; exact hvL
      have hmixv : cutLSgn σ i j (lgs_uL i j v) ≠
          cutLSgn σ i j (finRotate _ (lgs_uL i j v)) := by
        rw [(lgt_sgn_uL σ hd v hvL).1, (lgt_sgn_uL σ hd v hvL).2]; exact hv
      have e : ∀ xv : Fin L, lgT β M t σ G (some v) (Function.update x v xv) =
          ((β * t : ℝ) : ℂ) * ∑ z, lgT β M t (cutLSgn σ i j) (lgs_splitL i j G)
            (some (lgs_uL i j v)) (Function.update (cutLLab x i j z) (lgs_uL i j v) xv) *
            lgT β M t (cutRSgn σ i j) (lgs_splitR i j G) (some (lgs_lastR i j))
              (cutRLab x i j z) := by
        intro xv
        rw [lgt_T_splitR hD t σ hd hmix hG hdG (some v) hu]
        simp only [Option.map_some, lgt_cutLLab_updL hd x v hvL, lgt_cutRLab_updL hd x v hvL]
      simp only [e]
      refine (lgt_glue_rowL hκ (by positivity) _ _ (fun z => IHL.2 _ hmixv _)
        (hRrow x)).trans (le_of_eq ?_)
      calc a⁻¹ * (K ^ (n + i.val - j.val + 1 - 2) * (a * A ^ (n + i.val - j.val + 1 - 2)) *
            (K ^ (j.val - i.val + 1 - 2) * (a * A ^ (j.val - i.val + 1 - 2))))
          = (a⁻¹ * a) * (K ^ (n + i.val - j.val + 1 - 2) * K ^ (j.val - i.val + 1 - 2)) *
            (a * (A ^ (n + i.val - j.val + 1 - 2) * A ^ (j.val - i.val + 1 - 2))) := by ring
        _ = K ^ (n - 2) * (a * A ^ (n - 2)) := by rw [haa, hpK, hpA2, one_mul]
    · have hvR : i.val ≤ v.val ∧ v.val < j.val := by omega
      have hu : ∀ s, some v = some s → i.val ≤ s.val ∧ s.val < j.val := by
        intro s hs; rw [← Option.some_injective _ hs]; exact hvR
      have hmixv : cutRSgn σ i j (lgs_uR i j v) ≠
          cutRSgn σ i j (finRotate _ (lgs_uR i j v)) := by
        rw [(lgt_sgn_uR σ hd v hvR).1, (lgt_sgn_uR σ hd v hvR).2]; exact hv
      have e : ∀ xv : Fin L, lgT β M t σ G (some v) (Function.update x v xv) =
          ((β * t : ℝ) : ℂ) * ∑ z, lgT β M t (cutLSgn σ i j) (lgs_splitL i j G)
            (some (lgs_iL i j)) (cutLLab x i j z) *
            lgT β M t (cutRSgn σ i j) (lgs_splitR i j G) (some (lgs_uR i j v))
              (Function.update (cutRLab x i j z) (lgs_uR i j v) xv) := by
        intro xv
        rw [lgt_T_splitL t σ hd hmix hG hdG (some v) hu]
        simp only [Option.map_some, lgt_cutLLab_updR x v hvR, lgt_cutRLab_updR x v hvR]
      simp only [e]
      refine (lgt_glue_rowR hκ (by positivity) _ _ (hLrow x)
        (fun z => IHR.2 _ hmixv _)).trans (le_of_eq ?_)
      calc a⁻¹ * (K ^ (n + i.val - j.val + 1 - 2) * (a * A ^ (n + i.val - j.val + 1 - 2)) *
            (K ^ (j.val - i.val + 1 - 2) * (a * A ^ (j.val - i.val + 1 - 2))))
          = (a⁻¹ * a) * (K ^ (n + i.val - j.val + 1 - 2) * K ^ (j.val - i.val + 1 - 2)) *
            (a * (A ^ (n + i.val - j.val + 1 - 2) * A ^ (j.val - i.val + 1 - 2))) := by ring
        _ = K ^ (n - 2) * (a * A ^ (n - 2)) := by rw [haa, hpK, hpA2, one_mul]

/-- The mixed-tree sum with no mixed diagonal is the dressed stable molecule. -/
private lemma lgt_T_empty [NeZero L] {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {t : ℝ} {n : ℕ}
    (σ : Fin n → Bool) (ξ Er : Fin L → ℂ) (mixed : Fin n → Bool) (Vst : Fin n → Fin L → ℂ)
    (hleg : ∀ s (x y : Fin L), pairV β M t (σ s) (σ (finRotate n s)) x y =
      uvpLeg ξ Er mixed Vst s (x - y))
    (u : Option (Fin n)) (x : Fin n → Fin L) :
    lgT β M t σ ∅ u x = uvpDress ξ Er mixed Vst (stableMol β M t σ) u x := by
  have hfil : (dissections n).filter (fun F => lgMix σ F = ∅) =
      (dissections n).filter (fun F => ∀ d ∈ F, σ d.1 = σ d.2) := by
    refine Finset.filter_congr fun F _ => ?_
    rw [lgMix, Finset.filter_eq_empty_iff]
    simp only [not_not]
  unfold lgT lgPhi uvpDress stableMol
  rw [hfil, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.mul_sum, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  unfold lgLeg
  rw [hleg]

end Tree

/-- The pair kernels at large coupling: `γ_g⁻¹|K_t| ≤ C³ A` (Lemma 5.2(b) [fo:lem:deterministic] at
`k = 2`). -/
private lemma lgk_K2 {g : ℝ} {L : ℕ} {E : ℝ} {m : ℂ} {t c C : ℝ} (F : LgFacts g L E m t c C)
    (s s' : Bool) (a b : Fin L) :
    (gammaG g)⁻¹ * ‖pairK (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t s s' a b‖ ≤
      C ^ 3 * (g ^ 2 / ((1 - t) * min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t)))) := by
  have hD := primData_of_root g L F.hL E m F.hm
  have hg2 : 0 < g ^ 2 := by have := F.hg; positivity
  have hC := F.hC
  set β := gammaG g with hβ
  set M := dysonMat (hopB g) (gammaG g) L E m with hM
  set ℓ := min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t)) with hℓ
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le hg2 F.ell_ge
  have h1t : 0 < 1 - t := by linarith [F.ht1]
  have hA1 := F.A_ge
  have hβg : β⁻¹ = g ^ 2 := by rw [hβ, F.hγ, inv_inv]
  have hC3 : C ≤ C ^ 3 := by nlinarith [sq_nonneg C]
  by_cases hss : s = s'
  · subst hss
    have hMC : ∀ x y, ‖M x y‖ ≤ C := by
      intro x y
      have h0 : 0 ≤ c * cycDist x y / g ^ 2 := by have := F.hc; positivity
      exact (F.M_pt x y).trans (mul_le_of_le_one_right (by linarith)
        (Real.exp_le_one_iff.mpr (by linarith)))
    have hV : ∀ x, ∑ y, ‖pairV β M t s s x y‖ ≤ C := by
      intro x
      have hrow : ∑ y, ‖(1 - (t : ℂ) • pairQ β M)⁻¹ x y‖ ≤ C := by
        refine le_trans (Finset.sum_le_sum fun y _ => ?_) (F.Q_row t F.ht0 F.ht1.le x)
        exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by
          have := F.hc; positivity))
      cases s
      · simp only [pairV, ite_true, Bool.false_eq_true, ite_false, Matrix.map_apply, norm_star]
        exact hrow
      · simp only [pairV, ite_true]
        exact hrow
    have hK : ‖pairK β M t s s a b‖ ≤ β * C ^ 3 := by
      rw [lgw_K_apply]
      calc ‖∑ y, lgw_pairX β M s s a y * pairV β M t s s y b‖
          ≤ ∑ y, ‖lgw_pairX β M s s a y‖ * ‖pairV β M t s s y b‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => by rw [norm_mul])
        _ ≤ ∑ y, β * C ^ 2 * ‖pairV β M t s s b y‖ := by
            refine Finset.sum_le_sum fun y _ => ?_
            rw [lgw_pairX_norm hD, lgk_V_symm hD t s s y b]
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (norm_nonneg _) (hMC a y) 2) hD.pos.le) (norm_nonneg _)
        _ = β * C ^ 2 * ∑ y, ‖pairV β M t s s b y‖ := by rw [Finset.mul_sum]
        _ ≤ β * C ^ 2 * C := mul_le_mul_of_nonneg_left (hV b) (by have := hD.pos; positivity)
        _ = β * C ^ 3 := by ring
    calc β⁻¹ * ‖pairK β M t s s a b‖ ≤ β⁻¹ * (β * C ^ 3) :=
          mul_le_mul_of_nonneg_left hK (inv_nonneg.mpr hD.pos.le)
      _ = C ^ 3 := by rw [← mul_assoc, inv_mul_cancel₀ hD.pos.ne', one_mul]
      _ ≤ C ^ 3 * (g ^ 2 / ((1 - t) * ℓ)) := le_mul_of_one_le_right (by positivity) hA1
  · have hv : pairK β M t s s' = (mixedKer (pairP β M) t).map ((↑) : ℝ → ℂ) := by
      unfold pairK; rw [ite_eq_right hss]
    rw [hv, Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (F.K_pt a b).1, hβg]
    calc g ^ 2 * mixedKer (pairP β M) t a b ≤ g ^ 2 * (C / ((1 - t) * ℓ)) :=
          mul_le_mul_of_nonneg_left (F.K_pt a b).2 hg2.le
      _ = C * (g ^ 2 / ((1 - t) * ℓ)) := by ring
      _ ≤ C ^ 3 * (g ^ 2 / ((1 - t) * ℓ)) :=
          mul_le_mul_of_nonneg_right hC3 (by positivity)

/-! ## Consequences: the `W`-dependent forms, the tail, the long pair and the free label -/

section Cons

private lemma lgk_u_cycDist_eq {L : ℕ} [NeZero L] (a b : Fin L) :
    cycDist a b = min (a - b).val (-(a - b)).val := by
  rw [neg_sub]
  unfold cycDist
  rw [Fin.val_sub, Fin.val_sub]
  have ha := a.isLt
  have hb := b.isLt
  have e1 : L - (b : ℕ) + (a : ℕ) = (a : ℕ) + L - (b : ℕ) := by omega
  have e2 : L - (a : ℕ) + (b : ℕ) = (b : ℕ) + L - (a : ℕ) := by omega
  rw [e1, e2]

private lemma lgk_u_cycDist_sub_zero {L : ℕ} [NeZero L] (a b : Fin L) :
    cycDist a b = cycDist (a - b) 0 := by
  rw [lgk_u_cycDist_eq a b, lgk_u_cycDist_eq (a - b) 0, sub_zero]

private lemma lgk_u_geom_sum {L : ℕ} [NeZero L] (c' a : ℝ) (hc' : 0 < c') (ha : 0 < a) :
    ∑ y : Fin L, Real.exp (-(c' * (cycDist y 0 : ℝ) / a)) ≤ 2 * (1 + a / c') := by
  set s : ℝ := c' / a with hs
  have hs0 : 0 < s := div_pos hc' ha
  set r : ℝ := Real.exp (-s) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; linarith
  have hpow : ∀ n : ℕ, Real.exp (-(c' * (n : ℝ) / a)) = r ^ n := by
    intro n
    rw [hr, ← Real.exp_nat_mul]
    congr 1
    rw [hs]; field_simp
  have hgeom : ∑ y : Fin L, r ^ (y : ℕ) ≤ 1 / (1 - r) := by
    rw [Fin.sum_univ_eq_sum_range (fun n => r ^ n) L, Finset.range_eq_Ico]
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := L) hr0.le hr1
    simpa using this
  have hneg : ∑ y : Fin L, r ^ ((-y : Fin L) : ℕ) = ∑ y : Fin L, r ^ (y : ℕ) :=
    Fintype.sum_equiv (Equiv.neg _) _ _ (fun x => rfl)
  have hterm : ∀ y : Fin L, Real.exp (-(c' * (cycDist y 0 : ℝ) / a)) ≤
      r ^ (y : ℕ) + r ^ ((-y : Fin L) : ℕ) := by
    intro y
    rw [hpow, lgk_u_cycDist_eq, sub_zero]
    rcases min_choice (y : ℕ) ((-y : Fin L) : ℕ) with h | h
    · rw [h]; have : 0 ≤ r ^ ((-y : Fin L) : ℕ) := by positivity
      linarith
    · rw [h]; have : 0 ≤ r ^ (y : ℕ) := by positivity
      linarith
  calc ∑ y : Fin L, Real.exp (-(c' * (cycDist y 0 : ℝ) / a))
      ≤ ∑ y : Fin L, (r ^ (y : ℕ) + r ^ ((-y : Fin L) : ℕ)) :=
        Finset.sum_le_sum (fun y _ => hterm y)
    _ = 2 * ∑ y : Fin L, r ^ (y : ℕ) := by
        rw [Finset.sum_add_distrib, hneg]; ring
    _ ≤ 2 * (1 / (1 - r)) := by gcongr
    _ ≤ 2 * (1 + a / c') := by
        have h1 : 1 / (1 - r) ≤ 1 + a / c' := by
          have hE : s + 1 ≤ Real.exp s := Real.add_one_le_exp s
          have hrE : r * Real.exp s = 1 := by rw [hr, ← Real.exp_add]; simp
          have hlow : 1 - r ≥ s / (1 + s) := by
            have : r ≤ 1 / (1 + s) := by
              rw [le_div_iff₀ (by linarith)]
              nlinarith
            have h2 : 1 - 1 / (1 + s) = s / (1 + s) := by field_simp; ring
            linarith
          have hpos : 0 < s / (1 + s) := by positivity
          calc 1 / (1 - r) ≤ 1 / (s / (1 + s)) := by gcongr
            _ = 1 + a / c' := by rw [hs]; field_simp; ring
        linarith

/-- `1 + |log(1 - t)| ≤ 4 log W` for `W ≥ 3` and `1 - t ≥ W^{-3}`. -/
private lemma lgk_logW {W : ℕ} (hW : 3 ≤ W) {t : ℝ} (ht0 : 0 ≤ t)
    (hWt : (W : ℝ) ^ (-3 : ℝ) ≤ 1 - t) :
    t < 1 ∧ 1 + |Real.log (1 - t)| ≤ 4 * Real.log W := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  have hW3 : 0 < (W : ℝ) ^ (-3 : ℝ) := Real.rpow_pos_of_pos hW0 _
  have ht1 : t < 1 := by linarith
  refine ⟨ht1, ?_⟩
  have hlog3 : 1 < Real.log W := by
    have h3 : (3 : ℝ) ≤ W := by exact_mod_cast hW
    have : 1 < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith
    exact this.trans_le (Real.log_le_log (by norm_num) h3)
  have h1 : Real.log ((W : ℝ) ^ (-3 : ℝ)) ≤ Real.log (1 - t) := Real.log_le_log hW3 hWt
  rw [Real.log_rpow hW0] at h1
  have h2 : Real.log (1 - t) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  rw [abs_of_nonpos h2]
  linarith

/-- `‖𝒦_k‖ = W^{1-k} ‖F_k‖ ≤ ‖F_k‖`. -/
private lemma lgk_primLoop_le (g : ℝ) {W L : ℕ} (E : ℝ) (m : ℂ) (t : ℝ) {k : ℕ}
    (hk : 1 ≤ k) (a : Fin k → Fin L) (σ : Fin k → Bool) :
    ‖primLoop g W L E m t a σ‖ = ((W : ℝ) ^ (k - 1))⁻¹ * ‖primLoopF g L E m t a σ‖ := by
  have : primLoop g W L E m t a σ = (W : ℂ) ^ (1 - (k : ℤ)) * primLoopF g L E m t a σ := rfl
  rw [this, norm_mul, norm_zpow, Complex.norm_natCast]
  congr 1
  have e : (1 : ℤ) - k = -((k - 1 : ℕ) : ℤ) := by omega
  rw [e, zpow_neg, zpow_natCast]

/-- `A/W ≤ 2ζ_t`. -/
private lemma lgk_zeta {g : ℝ} {L : ℕ} {E : ℝ} {m : ℂ} {t c C : ℝ} (F : LgFacts g L E m t c C)
    {W : ℕ} (hW : 1 ≤ W) :
    g ^ 2 / ((1 - t) * min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t))) / W ≤ 2 * zetaProp g W L t := by
  have hg2 : 0 < g ^ 2 := by have := F.hg; positivity
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set ℓ := min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t)) with hℓ
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le hg2 F.ell_ge
  have h1t : 0 < 1 - t := by linarith [F.ht1]
  have hE0 : 0 < ellProp g L t := lt_of_lt_of_le hℓ0 F.ell_le
  have hz : zetaProp g W L t = g ^ 2 / ((W : ℝ) * ellProp g L t * (1 - t)) := by
    rw [zetaProp, F.hγ]; field_simp
  rw [hz]
  have hEl := F.ell_le2
  calc g ^ 2 / ((1 - t) * ℓ) / W = 2 * (g ^ 2 / ((W : ℝ) * (2 * ℓ) * (1 - t))) := by
        field_simp
    _ ≤ 2 * (g ^ 2 / ((W : ℝ) * ellProp g L t * (1 - t))) := by
        gcongr

/-- `ζ_v ≥ 1/(2W)` at large coupling. -/
private lemma lgk_zeta_ge {g : ℝ} {L : ℕ} {E : ℝ} {m : ℂ} {t c C : ℝ} (F : LgFacts g L E m t c C)
    {W : ℕ} (hW : 1 ≤ W) : 1 / (2 * W) ≤ zetaProp g W L t := by
  have hg2 : 0 < g ^ 2 := by have := F.hg; positivity
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set ℓ := min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t)) with hℓ
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le hg2 F.ell_ge
  have h1t : 0 < 1 - t := by linarith [F.ht1]
  have hs0 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr h1t
  have hs1 : Real.sqrt (1 - t) ≤ 1 := Real.sqrt_le_one.mpr (by linarith [F.ht0])
  have hE0 : 0 < ellProp g L t := lt_of_lt_of_le hℓ0 F.ell_le
  have hz : zetaProp g W L t = g ^ 2 / ((W : ℝ) * ellProp g L t * (1 - t)) := by
    rw [zetaProp, F.hγ]; field_simp
  have hEl : ellProp g L t * (1 - t) ≤ 2 * g ^ 2 := by
    have h1 : ellProp g L t ≤ 2 * (g ^ 2 / Real.sqrt (1 - t)) :=
      F.ell_le2.trans (by linarith [min_le_right (L : ℝ) (g ^ 2 / Real.sqrt (1 - t))])
    have h2 : (g ^ 2 / Real.sqrt (1 - t)) * (1 - t) = g ^ 2 * Real.sqrt (1 - t) := by
      have hss : Real.sqrt (1 - t) * Real.sqrt (1 - t) = 1 - t := Real.mul_self_sqrt h1t.le
      calc (g ^ 2 / Real.sqrt (1 - t)) * (1 - t)
          = (g ^ 2 / Real.sqrt (1 - t)) * (Real.sqrt (1 - t) * Real.sqrt (1 - t)) := by
            rw [hss]
        _ = g ^ 2 * Real.sqrt (1 - t) := by field_simp
    calc ellProp g L t * (1 - t) ≤ 2 * (g ^ 2 / Real.sqrt (1 - t)) * (1 - t) :=
          mul_le_mul_of_nonneg_right h1 h1t.le
      _ = 2 * (g ^ 2 * Real.sqrt (1 - t)) := by rw [mul_assoc, h2]
      _ ≤ 2 * (g ^ 2 * 1) := by gcongr
      _ = 2 * g ^ 2 := by ring
  rw [hz, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Superpolynomial decay: `C₁ W^{3C₁} e^{-c₁ W^ε} ≤ W^{-Q}` for large `W`. -/
private lemma lgk_tail_analytic {C₁ c₁ ε Q : ℝ} (hC₁ : 0 < C₁) (hc₁ : 0 < c₁) (hε : 0 < ε) :
    ∃ W₀ : ℕ, 1 ≤ W₀ ∧ ∀ W : ℕ, W₀ ≤ W →
      C₁ * (W : ℝ) ^ (3 * C₁) * Real.exp (-(c₁ * (W : ℝ) ^ ε)) ≤ (W : ℝ) ^ (-Q) := by
  set s : ℝ := (3 * C₁ + Q) / ε with hs
  have h1 := isLittleO_rpow_exp_pos_mul_atTop s hc₁
  have hy : Filter.Tendsto (fun x : ℝ => x ^ ε) Filter.atTop Filter.atTop := tendsto_rpow_atTop hε
  have h2 := h1.comp_tendsto hy
  have h3 := h2.def (by positivity : 0 < 1 / C₁)
  have h4 : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x ∧ ‖((fun y : ℝ => y ^ s) ∘ fun x : ℝ => x ^ ε) x‖ ≤
      1 / C₁ * ‖(fun y : ℝ => Real.exp (c₁ * y)) (x ^ ε)‖ :=
    (Filter.eventually_ge_atTop 1).and h3
  have h5 := tendsto_natCast_atTop_atTop (R := ℝ) |>.eventually h4
  obtain ⟨W₀, hW₀⟩ := Filter.eventually_atTop.mp h5
  refine ⟨max W₀ 1, le_max_right _ _, fun W hW => ?_⟩
  obtain ⟨hW1, hW2⟩ := hW₀ W (le_trans (le_max_left _ _) hW)
  have hW0 : (0 : ℝ) < W := by linarith
  simp only [Function.comp_apply, Real.norm_eq_abs] at hW2
  rw [abs_of_nonneg (Real.rpow_nonneg (Real.rpow_nonneg hW0.le _) _),
    abs_of_nonneg (Real.exp_pos _).le] at hW2
  have e1 : ((W : ℝ) ^ ε) ^ s = (W : ℝ) ^ (3 * C₁ + Q) := by
    rw [← Real.rpow_mul hW0.le, hs]
    congr 1
    field_simp
  rw [e1, Real.rpow_add hW0] at hW2
  have hQ0 : 0 < (W : ℝ) ^ Q := Real.rpow_pos_of_pos hW0 _
  have hE : C₁ * ((W : ℝ) ^ (3 * C₁) * (W : ℝ) ^ Q) ≤ Real.exp (c₁ * (W : ℝ) ^ ε) := by
    have := mul_le_mul_of_nonneg_left hW2 hC₁.le
    rwa [← mul_assoc C₁ (1 / C₁), mul_one_div_cancel hC₁.ne', one_mul] at this
  rw [Real.rpow_neg hW0.le, Real.exp_neg, ← div_eq_mul_inv, ← one_div,
    div_le_div_iff₀ (Real.exp_pos _) hQ0]
  linarith [hE, mul_assoc C₁ ((W : ℝ) ^ (3 * C₁)) ((W : ℝ) ^ Q)]

/-- `W⁻¹ C₁ W^{3C₁} e^{-c₁(log W)^{3/2}} ≤ W^{-F}/(4W²)` for large `W`. -/
private lemma lgk_pair_analytic {C₁ c₁ F : ℝ} (hC₁ : 0 < C₁) (hc₁ : 0 < c₁) (hF : 0 < F) :
    ∃ W₀ : ℕ, 3 ≤ W₀ ∧ ∀ W : ℕ, W₀ ≤ W →
      ((W : ℝ) ^ (2 - 1))⁻¹ * (C₁ * (W : ℝ) ^ (3 * C₁) *
        Real.exp (-(c₁ * Real.log W ^ ((3 : ℝ) / 2)))) ≤ (W : ℝ) ^ (-F) / (4 * (W : ℝ) ^ 2) := by
  set K : ℝ := 3 * C₁ + F + 1 with hK
  set B : ℝ := |Real.log (4 * C₁)| with hB
  have hK0 : 0 < K := by positivity
  have hB0 : 0 ≤ B := abs_nonneg _
  set x₀ : ℝ := max 1 (((K + B) / c₁) ^ 2) with hx₀
  refine ⟨max 3 ⌈Real.exp x₀⌉₊, le_max_left _ _, fun W hW => ?_⟩
  have hW3 : 3 ≤ W := le_trans (le_max_left _ _) hW
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  set x := Real.log W with hx
  have hxx₀ : x₀ ≤ x := by
    have h1 : Real.exp x₀ ≤ W := by
      have : (⌈Real.exp x₀⌉₊ : ℝ) ≤ W := by exact_mod_cast le_trans (le_max_right _ _) hW
      exact (Nat.le_ceil _).trans this
    rw [hx, ← Real.log_exp x₀]
    exact Real.log_le_log (Real.exp_pos _) h1
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hxx₀
  have hx0 : 0 < x := by linarith
  have hsq : (K + B) / c₁ ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by positivity) hx0.le]
    exact le_trans (le_max_right _ _) hxx₀
  have hpow : x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hx0, Real.rpow_one,
      Real.sqrt_eq_rpow]
  have hkey : Real.log (4 * C₁) + K * x ≤ c₁ * x ^ ((3 : ℝ) / 2) := by
    rw [hpow]
    have h1 : (K + B) ≤ c₁ * Real.sqrt x := by
      rw [div_le_iff₀ hc₁] at hsq; linarith
    have h2 : Real.log (4 * C₁) ≤ B := le_abs_self _
    have h3 : (K + B) * x ≤ c₁ * Real.sqrt x * x := mul_le_mul_of_nonneg_right h1 hx0.le
    nlinarith
  have hWe : (W : ℝ) = Real.exp x := (Real.exp_log hW0).symm
  rw [hWe]
  have e1 : (Real.exp x ^ (2 - 1))⁻¹ = Real.exp (-x) := by
    rw [show (2 - 1 : ℕ) = 1 by norm_num, pow_one, Real.exp_neg]
  have e2 : Real.exp x ^ (3 * C₁) = Real.exp (x * (3 * C₁)) := (Real.exp_mul x _).symm
  have e3 : Real.exp x ^ (-F) = Real.exp (x * (-F)) := (Real.exp_mul x _).symm
  have e4 : (Real.exp x) ^ 2 = Real.exp (2 * x) := by rw [← Real.exp_nat_mul]; norm_num
  have e5 : 4 * C₁ = Real.exp (Real.log (4 * C₁)) := (Real.exp_log (by positivity)).symm
  rw [e1, e2, e3, e4, le_div_iff₀ (by positivity)]
  calc Real.exp (-x) * (C₁ * Real.exp (x * (3 * C₁)) *
        Real.exp (-(c₁ * x ^ ((3 : ℝ) / 2)))) * (4 * Real.exp (2 * x))
      = (4 * C₁) * Real.exp (-x + x * (3 * C₁) - c₁ * x ^ ((3 : ℝ) / 2) + 2 * x) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_add]; ring
    _ = Real.exp (Real.log (4 * C₁) + (-x + x * (3 * C₁) - c₁ * x ^ ((3 : ℝ) / 2) + 2 * x)) := by
        rw [Real.exp_add (Real.log (4 * C₁)), ← e5]
    _ ≤ Real.exp (x * (-F)) := by
        apply Real.exp_le_exp.mpr
        nlinarith

end Cons

/-! ## The large-coupling bounds -/

/-- Corollary B.9 [uvp:cor:joint-tail], crude weighted bound, W-free form under
`L/g² ≥ C_*(1 + |log δ|)`, with no finite-cycle remainder. -/
theorem primLoopF_large_weighted (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (k : ℕ) (hk : 2 ≤ k) :
    ∃ Cκ Cs C₁ c₁ : ℝ, 1 ≤ Cκ ∧ 0 < Cs ∧ 0 < C₁ ∧ 0 < c₁ ∧ ∀ g : ℝ, Cκ ≤ g →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ L : ℕ, 3 ≤ L → Cs * (1 + |Real.log (1 - t)|) * g ^ 2 ≤ L →
      ∀ E : ℝ, |E| ≤ 2 - κ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m →
      ∀ (a : Fin k → Fin L) (σ : Fin k → Bool),
        ‖primLoopF g L E m t a σ‖ ≤ C₁ * (1 - t) ^ (-C₁) *
          Real.exp (-(c₁ * wordDiam a / min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t)))) := by
  obtain ⟨Cκ, R, c, C, hCκ, hR, hc, hC, H⟩ := lgk_facts κ hκ hκ2
  have hCKK : 1 ≤ C ^ 2 * C := by
    have : 1 ≤ C ^ 2 := one_le_pow₀ hC
    nlinarith
  obtain ⟨A, hA1, hA⟩ := lgw_induct (1 + C ^ 2 * C) (C ^ 2 * C) C (by linarith) hCKK hC k
  refine ⟨Cκ, R, A + 2 * k, c / 2, hCκ, by linarith, by positivity, by positivity, ?_⟩
  intro g hg t ht0 ht1 L hL hRL E hE m hm a σ
  have F := (H g hg L hL t ht0 ht1 hRL E hE m hm).1
  have hg2 : 0 < g ^ 2 := by have := F.hg; positivity
  have Ft : ∀ t', 0 ≤ t' → t' ≤ t → LgFacts g L E m t' c C := by
    intro t' h0 h1
    refine (H g hg L hL t' h0 (lt_of_le_of_lt h1 ht1) (le_trans ?_ hRL) E hE m hm).1
    have := lgk_log_mono h0 h1 ht1
    have : R * (1 + |Real.log (1 - t')|) ≤ R * (1 + |Real.log (1 - t)|) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    exact mul_le_mul_of_nonneg_right this hg2.le
  set ℓ := min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t)) with hℓ
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le hg2 F.ell_ge
  set θ := c / 2 / ℓ with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have h2θ : ∀ t', 0 ≤ t' → t' ≤ t → 2 * θ ≤ c / min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t')) := by
    intro t' h0 h1
    have e : 2 * θ = c / ℓ := by rw [hθ]; field_simp
    rw [e]
    exact div_le_div_of_nonneg_left hc.le (lt_of_lt_of_le hg2 (Ft t' h0 h1).ell_ge)
      (lgk_ell_mono h1 ht1)
  have hθ' : ∀ t', 0 ≤ t' → t' ≤ t → θ ≤ c / min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t')) :=
    fun t' h0 h1 => le_trans (by linarith) (h2θ t' h0 h1)
  have hD := primData_of_root g L hL E m hm
  set β := gammaG g with hβ
  set M := dysonMat (hopB g) (gammaG g) L E m with hM
  have hU : ∀ u t' : ℝ, 0 ≤ u → u ≤ t' → t' ≤ t → ∀ (s s' : Bool) (x : Fin L),
      ∑ b, Real.exp (2 * θ * cycDist x b) * ‖pairU β M u t' s s' x b‖ ≤
        (1 + C ^ 2 * C) * ((1 - u) / (1 - t')) := by
    intro u t' hu hut' ht't s s' x
    have ht'0 : 0 ≤ t' := hu.trans hut'
    have ht'1 : t' < 1 := lt_of_le_of_lt ht't ht1
    refine lgw_U_wrow hD hu hut' ht'1 (by linarith) (fun s s' x => ?_) s s' x
    refine (lgk_K_wrow (Ft t' ht'0 ht't) (by positivity) (h2θ t' ht'0 ht't) s s' x).trans
      (le_of_eq ?_)
    ring
  have hbase : lgw_Bd θ β M m t 2 (C ^ 2 * C) := by
    refine lgk_base_wtd hθ0 hD ht1 (fun t' h0 h1 s s' x y => ?_) (fun t' h0 h1 s s' x => ?_)
    · exact (lgk_K_wpt (Ft t' h0 h1) hθ0 (hθ' t' h0 h1) s s' x y).trans (le_of_eq (by ring))
    · exact (lgk_K_wrow (Ft t' h0 h1) hθ0 (hθ' t' h0 h1) s s' x).trans (le_of_eq (by ring))
  have hθg : θ ≤ c / g ^ 2 := (hθ' t ht0 le_rfl).trans
    (div_le_div_of_nonneg_left hc.le hg2 F.ell_ge)
  have hMe : ∀ x y, lgw_g θ M x y ≤ C := by
    intro x y
    unfold lgw_g
    calc Real.exp (θ * cycDist x y) * ‖M x y‖
        ≤ Real.exp (c * cycDist x y / g ^ 2) * (C * Real.exp (-(c * cycDist x y / g ^ 2))) :=
          mul_le_mul (lgk_exp_le hθg _) (F.M_pt x y) (norm_nonneg _) (Real.exp_pos _).le
      _ = C := by
          rw [mul_comm C, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  have hMr : ∀ x y, β * ∑ z, lgw_g θ M x z * lgw_g θ M z y ≤ C ^ 2 := by
    intro x y
    calc β * ∑ z, lgw_g θ M x z * lgw_g θ M z y ≤ β * ∑ z, lgw_g θ M x z * C :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ =>
            mul_le_mul_of_nonneg_left (hMe z y) (lgw_g_nonneg _ _ _ _)) hD.pos.le
      _ = β * C * ∑ z, Real.exp (θ * cycDist x z) * ‖M x z‖ := by
          rw [← Finset.sum_mul]; unfold lgw_g; ring
      _ ≤ β * C * (C * g ^ 2) := by
          refine mul_le_mul_of_nonneg_left ((Finset.sum_le_sum fun z _ =>
            mul_le_mul_of_nonneg_right (lgk_exp_le hθg _) (norm_nonneg _)).trans (F.M_row x))
            (mul_nonneg hD.pos.le (by linarith))
      _ = C ^ 2 := by
          rw [hβ, F.hγ]
          calc (g ^ 2)⁻¹ * C * (C * g ^ 2) = C ^ 2 * ((g ^ 2)⁻¹ * g ^ 2) := by ring
            _ = C ^ 2 := by rw [inv_mul_cancel₀ hg2.ne', mul_one]
  have hinit := lgw_init_all hθ0 hD.pos hD
    (fun k' hk' a σ => primLoopF_init g L hL E m hm k' hk' a σ) hC hMe hMr
  have hbd := hA L β θ t M m hD hθ0 ht1 hU hbase hinit k hk le_rfl
  have h := (hbd t ht0 le_rfl).1 a σ
  have h1t : 0 < 1 - t := by linarith
  have hw : ‖primLoopF g L E m t a σ‖ ≤
      (A * ((1 - t) ^ (2 * k - 3))⁻¹) * Real.exp (-(θ * wordDiam a)) := by
    calc ‖primLoopF g L E m t a σ‖
        = Real.exp (-(θ * wordDiam a)) *
            (Real.exp (θ * wordDiam a) * ‖primLoopF g L E m t a σ‖) := by
          rw [← mul_assoc, ← Real.exp_add]
          simp
      _ ≤ Real.exp (-(θ * wordDiam a)) * (A * ((1 - t) ^ (2 * k - 3))⁻¹) :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = _ := by ring
  have hθd : θ * (wordDiam a : ℝ) = c / 2 * wordDiam a / ℓ := by
    rw [hθ]; field_simp
  have hrp : ((1 - t) ^ (2 * k - 3))⁻¹ ≤ (1 - t) ^ (-(A + 2 * k)) := by
    have e : ((1 - t) ^ (2 * k - 3))⁻¹ = (1 - t) ^ (-((2 * k - 3 : ℕ) : ℝ)) := by
      rw [Real.rpow_neg h1t.le, Real.rpow_natCast]
    rw [e]
    refine Real.rpow_le_rpow_of_exponent_ge h1t (by linarith) ?_
    have : ((2 * k - 3 : ℕ) : ℝ) ≤ 2 * k := by
      have : 2 * k - 3 ≤ 2 * k := Nat.sub_le _ _
      exact_mod_cast this
    linarith
  rw [hθd] at hw
  refine hw.trans ?_
  have hexp0 : 0 ≤ Real.exp (-(c / 2 * wordDiam a / ℓ)) := (Real.exp_pos _).le
  have hp0 : 0 ≤ ((1 - t) ^ (2 * k - 3))⁻¹ := by positivity
  have hAC : A ≤ A + 2 * k := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  exact mul_le_mul_of_nonneg_right (mul_le_mul hAC hrp hp0
    (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])) hexp0

/-! ## Large coupling: the threshold `C_κ` before the length, the cutoffs and the parameters -/

section Uniform

/-- Theorem B.6 [uvp:thm:molecule] for the stable molecules of the model at large coupling, with
the actual kernels of Lemma A.10 [uvp:lem:actual-kernels] and the cores of Proposition B.8
[uvp:prop:cores]: the coupling threshold `C_κ` depends on `κ` only, uniformly in the length
`n`. -/
private lemma lgt_mol' (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ : ℝ, 1 ≤ Cκ ∧ ∀ n : ℕ, 3 ≤ n → ∃ R K : ℝ, 1 ≤ R ∧ 1 ≤ K ∧
      ∀ g : ℝ, Cκ ≤ g → ∀ L : ℕ, 3 ≤ L →
      ∀ t : ℝ, 0 ≤ t → t < 1 → R * (1 + |Real.log (1 - t)|) * g ^ 2 ≤ L →
      ∀ E : ℝ, |E| ≤ 2 - κ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m →
      ∀ σ : Fin n → Bool,
      (∀ x, ‖lgT (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ ∅ none x‖ ≤
        K * (g ^ 2 / ((1 - t) * min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t)))) ^ (n - 1)) ∧
      ∀ v : Fin n, σ v ≠ σ (finRotate n v) → ∀ x : Fin n → Fin L,
        ∑ xv : Fin L, ‖lgT (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ ∅ (some v)
          (Function.update x v xv)‖ ≤
          K * (g ^ 2 * (g ^ 2 / ((1 - t) * min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t)))) ^
            (n - 2)) := by
  obtain ⟨Cκ₁, R₁, c₁, C₁, hCκ₁, hR₁, hc₁, hC₁, H₁⟩ := lgk_facts κ hκ hκ2
  obtain ⟨Cκ₂, R₂, hCκ₂, hR₂, H₂'⟩ := stableMol_large' κ hκ hκ2
  refine ⟨max Cκ₁ Cκ₂, le_trans hCκ₁ (le_max_left _ _), fun n hn => ?_⟩
  obtain ⟨c₂, C₂, hc₂, hC₂, H₂⟩ := H₂' n hn
  set c := min c₁ c₂ with hcdef
  set C := max C₁ C₂ with hCdef
  have hc : 0 < c := lt_min hc₁ hc₂
  have hC1 : C₁ ≤ C := le_max_left _ _
  have hC2 : C₂ ≤ C := le_max_right _ _
  have hC : 0 < C := by linarith
  obtain ⟨K', hK', HU⟩ := uvp_molecule n hn c C hc hC
  refine ⟨max (max R₁ R₂) 1, max K' 1, le_max_right _ _, le_max_right _ _, ?_⟩
  intro g hg L hL t ht0 ht1 hRL E hE m hm σ
  have hlog : 0 ≤ |Real.log (1 - t)| := abs_nonneg _
  have hg1 : 1 ≤ g := le_trans (le_trans hCκ₁ (le_max_left _ _)) hg
  have hg2 : 0 < g ^ 2 := by positivity
  have hRL₁ : R₁ * (1 + |Real.log (1 - t)|) * g ^ 2 ≤ L := by
    refine le_trans ?_ hRL
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by linarith)) hg2.le
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hRL₂ : R₂ * g ^ 2 ≤ L := by
    refine le_trans ?_ hRL
    have h1 : R₂ ≤ max (max R₁ R₂) 1 := le_trans (le_max_right _ _) (le_max_left _ _)
    have h2 : R₂ ≤ max (max R₁ R₂) 1 * (1 + |Real.log (1 - t)|) := by nlinarith
    exact mul_le_mul_of_nonneg_right h2 hg2.le
  obtain ⟨F, HUv⟩ := H₁ g (le_trans (le_max_left _ _) hg) L hL t ht0 ht1 hRL₁ E hE m hm
  obtain ⟨hprof, hmass⟩ := H₂ g (le_trans (le_max_right _ _) hg) L hRL₂ E hE m hm t ht0 ht1 σ
  have : NeZero L := ⟨by omega⟩
  have hD := primData_of_root g L hL E m hm
  set β := gammaG g with hβ
  set M := dysonMat (hopB g) (gammaG g) L E m with hM
  obtain ⟨ξ, Er, ε, hξe, hEe, hdec, h1, h2, h3, h4, h5, h6, h7, h8⟩ := HUv
  set mixed : Fin n → Bool := fun s => σ s != σ (finRotate n s) with hmixed
  set Vst : Fin n → Fin L → ℂ := fun s z => pairV β M t (σ s) (σ (finRotate n s)) 0 z with hVst
  have hVT : ∀ (s s' : Bool) (a b c : Fin L),
      pairV β M t s s' (a + c) (b + c) = pairV β M t s s' a b :=
    fun s s' a b c => lgk_pairV_add _ _ _ _ _ t s s' c a b
  have hVS : ∀ (s s' : Bool) (a b : Fin L), pairV β M t s s' a b = pairV β M t s s' b a :=
    fun s s' a b => lgk_V_symm hD t s s' a b
  have hleg : ∀ s (x y : Fin L), pairV β M t (σ s) (σ (finRotate n s)) x y =
      uvpLeg ξ Er mixed Vst s (x - y) := by
    intro s x y
    unfold uvpLeg
    by_cases hs : σ s = σ (finRotate n s)
    · have : mixed s = false := by
        change (σ s != σ (finRotate n s)) = false
        rw [hs]; exact bne_self_eq_false _
      rw [ite_eq_right (by rw [this]; decide)]
      simp only [hVst]
      exact lgk_ti_apply _ (hVT _ _) (hVS _ _) x y
    · have : mixed s = true := bne_iff_ne.mpr hs
      rw [ite_eq_left this]
      have hv : pairV β M t (σ s) (σ (finRotate n s)) =
          ((1 - t • pairP β M)⁻¹).map ((↑) : ℝ → ℂ) := by
        unfold pairV; rw [ite_eq_right hs]
      rw [hv, Matrix.map_apply, hdec x y]
  have hδ0 : 0 < 1 - t := by linarith
  have hε0 : 0 ≤ ε := by
    have h0 := (norm_nonneg (Er 0)).trans (h7 0)
    by_contra h
    replace h := lt_of_not_ge h
    have : C₁ * ε / (g ^ 2 * (1 - t) ^ 2) < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) h) (by positivity)
    linarith
  have hKer : UvpKernels L (g ^ 2) (1 - t) c C ε ξ Er mixed Vst := by
    have hmulC : ∀ y : ℝ, 0 ≤ y → C₁ * y ≤ C * y := fun y hy => mul_le_mul_of_nonneg_right hC1 hy
    refine ⟨hξe, hEe, fun j hj => ⟨fun x => ?_, ?_⟩, ?_, fun x => ?_, ?_, fun x => ?_, ?_, ?_,
      fun x => ?_, h8⟩
    · simp only [hVst]
      exact lgk_ti_even _ (hVT _ _) (hVS _ _) x
    · have hs : σ j = σ (finRotate n j) := by simpa [hmixed] using hj
      have hrow : ∑ b, Real.exp (c₁ * cycDist 0 b / g ^ 2) *
          ‖pairV β M t (σ j) (σ (finRotate n j)) 0 b‖ ≤ C₁ := by
        rw [← hs]
        cases hσ : σ j
        · simp only [pairV, ite_true, Bool.false_eq_true, ite_false, Matrix.map_apply, norm_star]
          exact F.Q_row t ht0 ht1.le 0
        · simp only [pairV, ite_true]
          exact F.Q_row t ht0 ht1.le 0
      refine le_trans (Finset.sum_le_sum fun x _ => ?_) (hrow.trans hC1)
      simp only [hVst]
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
      rw [lgw_cd_comm x 0]
      apply div_le_div_of_nonneg_right _ hg2.le
      exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)
    · exact h1.trans (div_le_div_of_nonneg_right hC1 hδ0.le)
    · exact (h2 x).trans (div_le_div_of_nonneg_right hC1 (by
        have := lt_of_lt_of_le hg2 F.ell_ge; positivity))
    · exact h3.trans (div_le_div_of_nonneg_right (hmulC _ (by positivity)) hδ0.le)
    · exact (h4 x).trans (div_le_div_of_nonneg_right (hmulC _ (by positivity)) (by
        have := lt_of_lt_of_le hg2 F.ell_ge; positivity))
    · exact h5.trans (div_le_div_of_nonneg_right (hmulC _ (by positivity)) hδ0.le)
    · exact h6.trans (div_le_div_of_nonneg_right (hmulC _ hε0) (by positivity))
    · exact (h7 x).trans (div_le_div_of_nonneg_right (hmulC _ hε0) (by positivity))
  have hCore : UvpCore L (g ^ 2) (1 - t) c C (∀ j, mixed j = true) (stableMol β M t σ) := by
    refine ⟨fun x z => (stableMol_symm g L hL E m hm t σ x z).1,
      fun x => (stableMol_symm g L hL E m hm t σ x 0).2, fun x => ?_, fun halt v => ?_⟩
    · refine (hprof x).trans (mul_le_mul hC2 (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
        (by linarith))
      have : c * (wordDiam x : ℝ) / g ^ 2 ≤ c₂ * wordDiam x / g ^ 2 := by
        apply div_le_div_of_nonneg_right _ hg2.le
        exact mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _)
      linarith
    · have halt' : ∀ i, σ (finRotate n i) = !σ i := by
        intro i
        have h' : σ i ≠ σ (finRotate n i) := bne_iff_ne.mp (halt i)
        exact Bool.eq_not_iff.mpr h'.symm
      refine (hmass halt' v 0).trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 hδ0.le) (by positivity)
  have hgL : g ^ 2 ≤ (L : ℝ) := F.ell_ge.trans (min_le_left _ _)
  obtain ⟨Hpt, Hrow⟩ := HU L (g ^ 2) (1 - t) ε (by nlinarith) hgL hδ0 (by linarith) ξ Er mixed Vst
    (stableMol β M t σ) hKer hCore
  have hK1 : K' ≤ max K' 1 := le_max_left _ _
  have hA0 : 0 ≤ g ^ 2 / ((1 - t) * min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t))) := by
    have := lt_of_lt_of_le hg2 F.ell_ge; positivity
  refine ⟨fun x => ?_, fun v hv x => ?_⟩
  · rw [lgt_T_empty σ ξ Er mixed Vst hleg]
    exact (Hpt x).trans (mul_le_mul_of_nonneg_right hK1 (by positivity))
  · have hmv : mixed v = true := bne_iff_ne.mpr hv
    simp only [lgt_T_empty σ ξ Er mixed Vst hleg]
    refine (Hrow v hmv x).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right hK1 (by positivity)

/-- The bounds of Theorem B.6 [uvp:thm:molecule] for all the lengths `3 ≤ n ≤ N`: the coupling
threshold `C_κ` depends on `κ` only, the constants `R` and `K` on `N`. -/
private lemma lgt_mol_all' (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ : ℝ, 1 ≤ Cκ ∧ ∀ N : ℕ, ∃ R K : ℝ, 1 ≤ R ∧ 1 ≤ K ∧
      ∀ g : ℝ, Cκ ≤ g → ∀ L : ℕ, 3 ≤ L →
      ∀ t : ℝ, 0 ≤ t → t < 1 → R * (1 + |Real.log (1 - t)|) * g ^ 2 ≤ L →
      ∀ E : ℝ, |E| ≤ 2 - κ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m →
      ∀ n, 3 ≤ n → n ≤ N → ∀ σ : Fin n → Bool,
      (∀ x, ‖lgT (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ ∅ none x‖ ≤
        K * (g ^ 2 / ((1 - t) * min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t)))) ^ (n - 1)) ∧
      ∀ v : Fin n, σ v ≠ σ (finRotate n v) → ∀ x : Fin n → Fin L,
        ∑ xv : Fin L, ‖lgT (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ ∅ (some v)
          (Function.update x v xv)‖ ≤
          K * (g ^ 2 * (g ^ 2 / ((1 - t) * min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t)))) ^
            (n - 2)) := by
  obtain ⟨Cκ, hCκ, Hm⟩ := lgt_mol' κ hκ hκ2
  refine ⟨Cκ, hCκ, fun N => ?_⟩
  induction N with
  | zero =>
    exact ⟨1, 1, le_rfl, le_rfl, fun g _ L _ t _ _ _ E _ m _ n hn hnN => by omega⟩
  | succ N ih =>
    obtain ⟨R, K, hR, hK, H⟩ := ih
    by_cases hN : N + 1 < 3
    · exact ⟨R, K, hR, hK, fun g hg L hL t ht0 ht1 hRL E hE m hm n hn hnN =>
        H g hg L hL t ht0 ht1 hRL E hE m hm n hn (by omega)⟩
    obtain ⟨R', K', hR', hK', H'⟩ := Hm (N + 1) (by omega)
    refine ⟨max R R', max K K', le_trans hR (le_max_left _ _), le_trans hK (le_max_left _ _), ?_⟩
    intro g hg L hL t ht0 ht1 hRL E hE m hm n hn hnN σ
    have hlog : 0 ≤ |Real.log (1 - t)| := abs_nonneg _
    have hg2 : 0 ≤ g ^ 2 := sq_nonneg g
    have hRL1 : R * (1 + |Real.log (1 - t)|) * g ^ 2 ≤ L := le_trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
        hg2) hRL
    have hRL2 : R' * (1 + |Real.log (1 - t)|) * g ^ 2 ≤ L := le_trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith))
        hg2) hRL
    have hA0 : 0 ≤ g ^ 2 / ((1 - t) * min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t))) := by
      refine div_nonneg hg2 (mul_nonneg (by linarith) (le_min (Nat.cast_nonneg _)
        (div_nonneg hg2 (Real.sqrt_nonneg _))))
    rcases Nat.lt_or_ge n (N + 1) with hlt | hge
    · obtain ⟨h1, h2⟩ := H g hg L hL t ht0 ht1 hRL1 E hE m hm n hn (by omega) σ
      exact ⟨fun x => (h1 x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)),
        fun v hv x => (h2 v hv x).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))⟩
    · obtain rfl : n = N + 1 := by omega
      obtain ⟨h1, h2⟩ := H' g hg L hL t ht0 ht1 hRL2 E hE m hm σ
      exact ⟨fun x => (h1 x).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
          (by positivity)),
        fun v hv x => (h2 v hv x).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))⟩

/-- Lemma 5.2 [fo:lem:deterministic](b) through (B.12) [uvp:eq:primitive-final], W-free form:
`|F_k| ≤ C'A^{k-1}`, `A = g²/(δℓ)`, `ℓ = min{L, g²/√δ}`, `δ = 1 - t`, under
`L ≥ C_*(1 + |log δ|)g²`, with no upper bound on `g` or `L`; the coupling threshold `C_κ`
depends on `κ` only, uniformly in `k`. -/
private lemma lgu_primLoopF (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ : ℝ, 1 ≤ Cκ ∧ ∀ k : ℕ, 2 ≤ k → ∃ Cs C' : ℝ, 0 < Cs ∧ 0 < C' ∧
      ∀ g : ℝ, Cκ ≤ g → ∀ t : ℝ, 0 ≤ t → t < 1 →
      ∀ L : ℕ, 3 ≤ L → Cs * (1 + |Real.log (1 - t)|) * g ^ 2 ≤ L → ∀ E : ℝ, |E| ≤ 2 - κ →
      ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m →
      ∀ (a : Fin k → Fin L) (σ : Fin k → Bool),
        ‖primLoopF g L E m t a σ‖ ≤
          C' * (g ^ 2 / ((1 - t) * min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t)))) ^ (k - 1) := by
  obtain ⟨Cκ₁, R₁, c₁, C₁, hCκ₁, hR₁, hc₁, hC₁, H₁⟩ := lgk_facts κ hκ hκ2
  obtain ⟨Cκ₂, hCκ₂, H₂'⟩ := lgt_mol_all' κ hκ hκ2
  refine ⟨max Cκ₁ Cκ₂, le_trans hCκ₁ (le_max_left _ _), fun k hk => ?_⟩
  obtain ⟨R₂, K, hR₂, hK, H₂⟩ := H₂' k
  have hC3 : 0 < C₁ ^ 3 := by positivity
  have hK2 : 0 < (2 : ℝ) ^ (k * k) * K ^ (k - 2) := by positivity
  refine ⟨max R₁ R₂, C₁ ^ 3 + 2 ^ (k * k) * K ^ (k - 2),
    lt_of_lt_of_le (by linarith) (le_max_left _ _), by linarith, ?_⟩
  intro g hg t ht0 ht1 L hL hRL E hE m hm a σ
  have hlog : 0 ≤ |Real.log (1 - t)| := abs_nonneg _
  have hg2 : 0 ≤ g ^ 2 := sq_nonneg g
  have hRL1 : R₁ * (1 + |Real.log (1 - t)|) * g ^ 2 ≤ L := le_trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
      hg2) hRL
  have hRL2 : R₂ * (1 + |Real.log (1 - t)|) * g ^ 2 ≤ L := le_trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith))
      hg2) hRL
  have F := (H₁ g (le_trans (le_max_left _ _) hg) L hL t ht0 ht1 hRL1 E hE m hm).1
  have hD := primData_of_root g L hL E m hm
  set β := gammaG g with hβ
  set M := dysonMat (hopB g) (gammaG g) L E m with hM
  set A := g ^ 2 / ((1 - t) * min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t))) with hA
  have hA1 : 1 ≤ A := F.A_ge
  have hA0 : 0 ≤ A := by linarith
  rcases eq_or_lt_of_le hk with hk2 | hk3
  · subst hk2
    have e : ‖primLoopF g L E m t a σ‖ = β⁻¹ * ‖pairK β M t (σ 0) (σ 1) (a 0) (a 1)‖ := by
      change ‖(β : ℂ)⁻¹ * pairK β M t (σ 0) (σ 1) (a 0) (a 1)‖ = _
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD.pos]
    rw [e]
    refine (lgk_K2 F (σ 0) (σ 1) (a 0) (a 1)).trans ?_
    have e2 : A ^ (2 - 1) = A := by norm_num
    rw [e2]
    exact mul_le_mul_of_nonneg_right (by linarith) hA0
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 3 := ⟨k - 3, by omega⟩
    have hB := lgt_bounds hD ht0 ht1.le (by
        rw [hβ, F.hγ, inv_mul_cancel₀ (by have := F.hg; positivity)])
      (by have := F.hg; positivity) hA1 hK (k' + 3)
      (fun n hn hnN σ => H₂ g (le_trans (le_max_right _ _) hg) L hL t ht0 ht1 hRL2 E hE m hm
        n hn hnN σ) (k' + 3) (by omega) le_rfl
    have hsum : primLoopF g L E m t a σ =
        ∑ G ∈ (polyDiags (k' + 3)).powerset, lgT β M t σ G none a := by
      unfold lgT
      rw [Finset.sum_fiberwise_of_maps_to (g := lgMix σ) (fun F hF => Finset.mem_powerset.mpr
        ((Finset.filter_subset _ _).trans ((lgs_mem_dissections _).mp hF).1))]
      change ∑ F ∈ dissections (k' + 3), dissVal β M t σ F a = _
      refine Finset.sum_congr rfl fun F _ => ?_
      unfold dissVal lgPhi lgLeg
      simp
    rw [hsum]
    have hcard : ((polyDiags (k' + 3)).powerset.card : ℝ) ≤ 2 ^ ((k' + 3) * (k' + 3)) := by
      rw [Finset.card_powerset]
      have : (polyDiags (k' + 3)).card ≤ (k' + 3) * (k' + 3) := by
        calc (polyDiags (k' + 3)).card ≤ Fintype.card (Fin (k' + 3) × Fin (k' + 3)) :=
              Finset.card_le_univ _
          _ = (k' + 3) * (k' + 3) := by simp
      exact_mod_cast pow_le_pow_right₀ (by norm_num) this
    calc ‖∑ G ∈ (polyDiags (k' + 3)).powerset, lgT β M t σ G none a‖
        ≤ ∑ G ∈ (polyDiags (k' + 3)).powerset, ‖lgT β M t σ G none a‖ := norm_sum_le _ _
      _ ≤ ∑ G ∈ (polyDiags (k' + 3)).powerset, K ^ (k' + 3 - 2) * A ^ (k' + 3 - 1) :=
          Finset.sum_le_sum fun G _ => (hB σ G).1 a
      _ = ((polyDiags (k' + 3)).powerset.card : ℝ) * (K ^ (k' + 3 - 2) * A ^ (k' + 3 - 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 ^ ((k' + 3) * (k' + 3)) * (K ^ (k' + 3 - 2) * A ^ (k' + 3 - 1)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ (C₁ ^ 3 + 2 ^ ((k' + 3) * (k' + 3)) * K ^ (k' + 3 - 2)) * A ^ (k' + 3 - 1) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- Lemma 5.2 [fo:lem:deterministic](b), (5.20) [fo:eq:primitivebound] case (b) and its
length-two bound: `W ≥ 3`, `1 - t ≥ W^{-3}`, `L ≥ C_* g² log W`, with `C_κ` depending on `κ`
only and `C_* = C_*(κ, k)`, as in the statement of Lemma 5.2(b) [fo:lem:deterministic]. -/
theorem primLoop_large' (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ : ℝ, 1 ≤ Cκ ∧ ∀ k : ℕ, 2 ≤ k → ∃ Cs C' : ℝ, 0 < Cs ∧ 0 < C' ∧
      ∀ W : ℕ, 3 ≤ W → ∀ g : ℝ, Cκ ≤ g →
      ∀ L : ℕ, 3 ≤ L → Cs * g ^ 2 * Real.log W ≤ L → ∀ E : ℝ, |E| ≤ 2 - κ →
      ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m →
      ∀ t : ℝ, 0 ≤ t → (W : ℝ) ^ (-3 : ℝ) ≤ 1 - t → ∀ (a : Fin k → Fin L) (σ : Fin k → Bool),
        ‖primLoop g W L E m t a σ‖ ≤ C' * zetaProp g W L t ^ (k - 1) := by
  obtain ⟨Cκ₁, hCκ₁, H₁'⟩ := lgu_primLoopF κ hκ hκ2
  obtain ⟨Cκ₂, R₂, c₂, C₂, hCκ₂, hR₂, hc₂, hC₂, H₂⟩ := lgk_facts κ hκ hκ2
  refine ⟨max Cκ₁ Cκ₂, le_trans hCκ₁ (le_max_left _ _), fun k hk => ?_⟩
  obtain ⟨Cs₁, C₁, hCs₁, hC₁, H₁⟩ := H₁' k hk
  refine ⟨4 * max Cs₁ R₂, 2 ^ (k - 1) * C₁, by positivity, by positivity, ?_⟩
  intro W hW g hg L hL hRL E hE m hm t ht0 hWt a σ
  obtain ⟨ht1, hlogW⟩ := lgk_logW hW ht0 hWt
  have hg2 : 0 ≤ g ^ 2 := sq_nonneg g
  have hmax : 0 ≤ max Cs₁ R₂ := le_trans hCs₁.le (le_max_left _ _)
  have hX : max Cs₁ R₂ * (1 + |Real.log (1 - t)|) * g ^ 2 ≤ L := by
    calc max Cs₁ R₂ * (1 + |Real.log (1 - t)|) * g ^ 2
        ≤ max Cs₁ R₂ * (4 * Real.log W) * g ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogW hmax) hg2
      _ = 4 * max Cs₁ R₂ * g ^ 2 * Real.log W := by ring
      _ ≤ L := hRL
  have hlog : 0 ≤ |Real.log (1 - t)| := abs_nonneg _
  have h1 : Cs₁ * (1 + |Real.log (1 - t)|) * g ^ 2 ≤ L := le_trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
      hg2) hX
  have h2 : R₂ * (1 + |Real.log (1 - t)|) * g ^ 2 ≤ L := le_trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith))
      hg2) hX
  have F := (H₂ g (le_trans (le_max_right _ _) hg) L hL t ht0 ht1 h2 E hE m hm).1
  have hF := H₁ g (le_trans (le_max_left _ _) hg) t ht0 ht1 L hL h1 E hE m hm a σ
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  rw [lgk_primLoop_le g E m t (by omega) a σ]
  set A := g ^ 2 / ((1 - t) * min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t))) with hA
  have hA0 : 0 ≤ A := le_trans zero_le_one F.A_ge
  calc ((W : ℝ) ^ (k - 1))⁻¹ * ‖primLoopF g L E m t a σ‖
      ≤ ((W : ℝ) ^ (k - 1))⁻¹ * (C₁ * A ^ (k - 1)) :=
        mul_le_mul_of_nonneg_left hF (by positivity)
    _ = C₁ * (A / W) ^ (k - 1) := by rw [div_pow, div_eq_mul_inv]; ring
    _ ≤ C₁ * (2 * zetaProp g W L t) ^ (k - 1) := by
        gcongr
        exact lgk_zeta F (by omega)
    _ = 2 ^ (k - 1) * C₁ * zetaProp g W L t ^ (k - 1) := by rw [mul_pow]; ring

/-- Corollary B.9 [uvp:cor:joint-tail], crude weighted bound, W-free form under
`L/g² ≥ C_*(1 + |log δ|)`, with no finite-cycle remainder; the coupling threshold `C_κ` depends
on `κ` only, uniformly in `k`. -/
private lemma lgu_weighted (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ : ℝ, 1 ≤ Cκ ∧ ∀ k : ℕ, 2 ≤ k → ∃ Cs C₁ c₁ : ℝ, 0 < Cs ∧ 0 < C₁ ∧ 0 < c₁ ∧
      ∀ g : ℝ, Cκ ≤ g →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ L : ℕ, 3 ≤ L → Cs * (1 + |Real.log (1 - t)|) * g ^ 2 ≤ L →
      ∀ E : ℝ, |E| ≤ 2 - κ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m →
      ∀ (a : Fin k → Fin L) (σ : Fin k → Bool),
        ‖primLoopF g L E m t a σ‖ ≤ C₁ * (1 - t) ^ (-C₁) *
          Real.exp (-(c₁ * wordDiam a / min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t)))) := by
  obtain ⟨Cκ, R, c, C, hCκ, hR, hc, hC, H⟩ := lgk_facts κ hκ hκ2
  refine ⟨Cκ, hCκ, fun k hk => ?_⟩
  have hCKK : 1 ≤ C ^ 2 * C := by
    have : 1 ≤ C ^ 2 := one_le_pow₀ hC
    nlinarith
  obtain ⟨A, hA1, hA⟩ := lgw_induct (1 + C ^ 2 * C) (C ^ 2 * C) C (by linarith) hCKK hC k
  refine ⟨R, A + 2 * k, c / 2, by linarith, by positivity, by positivity, ?_⟩
  intro g hg t ht0 ht1 L hL hRL E hE m hm a σ
  have F := (H g hg L hL t ht0 ht1 hRL E hE m hm).1
  have hg2 : 0 < g ^ 2 := by have := F.hg; positivity
  have Ft : ∀ t', 0 ≤ t' → t' ≤ t → LgFacts g L E m t' c C := by
    intro t' h0 h1
    refine (H g hg L hL t' h0 (lt_of_le_of_lt h1 ht1) (le_trans ?_ hRL) E hE m hm).1
    have := lgk_log_mono h0 h1 ht1
    have : R * (1 + |Real.log (1 - t')|) ≤ R * (1 + |Real.log (1 - t)|) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    exact mul_le_mul_of_nonneg_right this hg2.le
  set ℓ := min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t)) with hℓ
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le hg2 F.ell_ge
  set θ := c / 2 / ℓ with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have h2θ : ∀ t', 0 ≤ t' → t' ≤ t → 2 * θ ≤ c / min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t')) := by
    intro t' h0 h1
    have e : 2 * θ = c / ℓ := by rw [hθ]; field_simp
    rw [e]
    exact div_le_div_of_nonneg_left hc.le (lt_of_lt_of_le hg2 (Ft t' h0 h1).ell_ge)
      (lgk_ell_mono h1 ht1)
  have hθ' : ∀ t', 0 ≤ t' → t' ≤ t → θ ≤ c / min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t')) :=
    fun t' h0 h1 => le_trans (by linarith) (h2θ t' h0 h1)
  have hD := primData_of_root g L hL E m hm
  set β := gammaG g with hβ
  set M := dysonMat (hopB g) (gammaG g) L E m with hM
  have hU : ∀ u t' : ℝ, 0 ≤ u → u ≤ t' → t' ≤ t → ∀ (s s' : Bool) (x : Fin L),
      ∑ b, Real.exp (2 * θ * cycDist x b) * ‖pairU β M u t' s s' x b‖ ≤
        (1 + C ^ 2 * C) * ((1 - u) / (1 - t')) := by
    intro u t' hu hut' ht't s s' x
    have ht'0 : 0 ≤ t' := hu.trans hut'
    have ht'1 : t' < 1 := lt_of_le_of_lt ht't ht1
    refine lgw_U_wrow hD hu hut' ht'1 (by linarith) (fun s s' x => ?_) s s' x
    refine (lgk_K_wrow (Ft t' ht'0 ht't) (by positivity) (h2θ t' ht'0 ht't) s s' x).trans
      (le_of_eq ?_)
    ring
  have hbase : lgw_Bd θ β M m t 2 (C ^ 2 * C) := by
    refine lgk_base_wtd hθ0 hD ht1 (fun t' h0 h1 s s' x y => ?_) (fun t' h0 h1 s s' x => ?_)
    · exact (lgk_K_wpt (Ft t' h0 h1) hθ0 (hθ' t' h0 h1) s s' x y).trans (le_of_eq (by ring))
    · exact (lgk_K_wrow (Ft t' h0 h1) hθ0 (hθ' t' h0 h1) s s' x).trans (le_of_eq (by ring))
  have hθg : θ ≤ c / g ^ 2 := (hθ' t ht0 le_rfl).trans
    (div_le_div_of_nonneg_left hc.le hg2 F.ell_ge)
  have hMe : ∀ x y, lgw_g θ M x y ≤ C := by
    intro x y
    unfold lgw_g
    calc Real.exp (θ * cycDist x y) * ‖M x y‖
        ≤ Real.exp (c * cycDist x y / g ^ 2) * (C * Real.exp (-(c * cycDist x y / g ^ 2))) :=
          mul_le_mul (lgk_exp_le hθg _) (F.M_pt x y) (norm_nonneg _) (Real.exp_pos _).le
      _ = C := by
          rw [mul_comm C, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  have hMr : ∀ x y, β * ∑ z, lgw_g θ M x z * lgw_g θ M z y ≤ C ^ 2 := by
    intro x y
    calc β * ∑ z, lgw_g θ M x z * lgw_g θ M z y ≤ β * ∑ z, lgw_g θ M x z * C :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ =>
            mul_le_mul_of_nonneg_left (hMe z y) (lgw_g_nonneg _ _ _ _)) hD.pos.le
      _ = β * C * ∑ z, Real.exp (θ * cycDist x z) * ‖M x z‖ := by
          rw [← Finset.sum_mul]; unfold lgw_g; ring
      _ ≤ β * C * (C * g ^ 2) := by
          refine mul_le_mul_of_nonneg_left ((Finset.sum_le_sum fun z _ =>
            mul_le_mul_of_nonneg_right (lgk_exp_le hθg _) (norm_nonneg _)).trans (F.M_row x))
            (mul_nonneg hD.pos.le (by linarith))
      _ = C ^ 2 := by
          rw [hβ, F.hγ]
          calc (g ^ 2)⁻¹ * C * (C * g ^ 2) = C ^ 2 * ((g ^ 2)⁻¹ * g ^ 2) := by ring
            _ = C ^ 2 := by rw [inv_mul_cancel₀ hg2.ne', mul_one]
  have hinit := lgw_init_all hθ0 hD.pos hD
    (fun k' hk' a σ => primLoopF_init g L hL E m hm k' hk' a σ) hC hMe hMr
  have hbd := hA L β θ t M m hD hθ0 ht1 hU hbase hinit k hk le_rfl
  have h := (hbd t ht0 le_rfl).1 a σ
  have h1t : 0 < 1 - t := by linarith
  have hw : ‖primLoopF g L E m t a σ‖ ≤
      (A * ((1 - t) ^ (2 * k - 3))⁻¹) * Real.exp (-(θ * wordDiam a)) := by
    calc ‖primLoopF g L E m t a σ‖
        = Real.exp (-(θ * wordDiam a)) *
            (Real.exp (θ * wordDiam a) * ‖primLoopF g L E m t a σ‖) := by
          rw [← mul_assoc, ← Real.exp_add]
          simp
      _ ≤ Real.exp (-(θ * wordDiam a)) * (A * ((1 - t) ^ (2 * k - 3))⁻¹) :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = _ := by ring
  have hθd : θ * (wordDiam a : ℝ) = c / 2 * wordDiam a / ℓ := by
    rw [hθ]; field_simp
  have hrp : ((1 - t) ^ (2 * k - 3))⁻¹ ≤ (1 - t) ^ (-(A + 2 * k)) := by
    have e : ((1 - t) ^ (2 * k - 3))⁻¹ = (1 - t) ^ (-((2 * k - 3 : ℕ) : ℝ)) := by
      rw [Real.rpow_neg h1t.le, Real.rpow_natCast]
    rw [e]
    refine Real.rpow_le_rpow_of_exponent_ge h1t (by linarith) ?_
    have : ((2 * k - 3 : ℕ) : ℝ) ≤ 2 * k := by
      have : 2 * k - 3 ≤ 2 * k := Nat.sub_le _ _
      exact_mod_cast this
    linarith
  rw [hθd] at hw
  refine hw.trans ?_
  have hexp0 : 0 ≤ Real.exp (-(c / 2 * wordDiam a / ℓ)) := (Real.exp_pos _).le
  have hp0 : 0 ≤ ((1 - t) ^ (2 * k - 3))⁻¹ := by positivity
  have hAC : A ≤ A + 2 * k := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  exact mul_le_mul_of_nonneg_right (mul_le_mul hAC hrp hp0
    (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])) hexp0

/-- (5.21) [fo:eq:primitive-tail] in case (b), Corollary B.9 [uvp:cor:joint-tail], under
`L ≥ C_* g² log W`, with `C_κ` depending on `κ` only, uniformly in `k`, `ε` and `Q`. -/
theorem primLoop_large_tail' (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ : ℝ, 1 ≤ Cκ ∧ ∀ ε Q : ℝ, 0 < ε → 0 < Q → ∀ k : ℕ, 2 ≤ k →
      ∃ Cs : ℝ, ∃ W₀ : ℕ, 0 < Cs ∧ ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, Cκ ≤ g →
      ∀ L : ℕ, 3 ≤ L → Cs * g ^ 2 * Real.log W ≤ L → ∀ E : ℝ, |E| ≤ 2 - κ →
      ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m →
      ∀ t : ℝ, 0 ≤ t → (W : ℝ) ^ (-3 : ℝ) ≤ 1 - t → ∀ (a : Fin k → Fin L) (σ : Fin k → Bool),
        (W : ℝ) ^ ε * ellProp g L t < wordDiam a →
        ‖primLoop g W L E m t a σ‖ ≤ (W : ℝ) ^ (-Q) := by
  obtain ⟨Cκ₁, hCκ₁, H₁'⟩ := lgu_weighted κ hκ hκ2
  obtain ⟨Cκ₂, R₂, c₂, C₂, hCκ₂, hR₂, hc₂, hC₂, H₂⟩ := lgk_facts κ hκ hκ2
  refine ⟨max Cκ₁ Cκ₂, le_trans hCκ₁ (le_max_left _ _), fun ε Q hε _hQ k hk => ?_⟩
  obtain ⟨Cs₁, C₁, c₁, hCs₁, hC₁, hc₁, H₁⟩ := H₁' k hk
  obtain ⟨W₀, hW₀1, hW₀⟩ := lgk_tail_analytic (Q := Q) hC₁ hc₁ hε
  refine ⟨4 * max Cs₁ R₂, max W₀ 3, by positivity, ?_⟩
  intro W hW g hg L hL hRL E hE m hm t ht0 hWt a σ hdiam
  have hW3 : 3 ≤ W := le_trans (le_max_right _ _) hW
  obtain ⟨ht1, hlogW⟩ := lgk_logW hW3 ht0 hWt
  have hg2 : 0 ≤ g ^ 2 := sq_nonneg g
  have hmax : 0 ≤ max Cs₁ R₂ := le_trans hCs₁.le (le_max_left _ _)
  have hX : max Cs₁ R₂ * (1 + |Real.log (1 - t)|) * g ^ 2 ≤ L := by
    calc max Cs₁ R₂ * (1 + |Real.log (1 - t)|) * g ^ 2
        ≤ max Cs₁ R₂ * (4 * Real.log W) * g ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogW hmax) hg2
      _ = 4 * max Cs₁ R₂ * g ^ 2 * Real.log W := by ring
      _ ≤ L := hRL
  have hlog : 0 ≤ |Real.log (1 - t)| := abs_nonneg _
  have h1 : Cs₁ * (1 + |Real.log (1 - t)|) * g ^ 2 ≤ L := le_trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
      hg2) hX
  have h2 : R₂ * (1 + |Real.log (1 - t)|) * g ^ 2 ≤ L := le_trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith))
      hg2) hX
  have F := (H₂ g (le_trans (le_max_right _ _) hg) L hL t ht0 ht1 h2 E hE m hm).1
  have hF := H₁ g (le_trans (le_max_left _ _) hg) t ht0 ht1 L hL h1 E hE m hm a σ
  have hW1 : 1 ≤ W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hW3' : 0 < (W : ℝ) ^ (-3 : ℝ) := Real.rpow_pos_of_pos hW0 _
  have h1t : 0 < 1 - t := by linarith
  set ℓ := min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t)) with hℓ
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le (by have := F.hg; positivity) F.ell_ge
  have hle : ‖primLoop g W L E m t a σ‖ ≤ ‖primLoopF g L E m t a σ‖ := by
    rw [lgk_primLoop_le g E m t (by omega) a σ]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hW1))
  have hdiam' : (W : ℝ) ^ ε < wordDiam a / ℓ := by
    rw [lt_div_iff₀ hℓ0]
    calc (W : ℝ) ^ ε * ℓ ≤ (W : ℝ) ^ ε * ellProp g L t :=
          mul_le_mul_of_nonneg_left F.ell_le (by positivity)
      _ < wordDiam a := hdiam
  have hexp : Real.exp (-(c₁ * wordDiam a / ℓ)) ≤ Real.exp (-(c₁ * (W : ℝ) ^ ε)) := by
    apply Real.exp_le_exp.mpr
    have : c₁ * (W : ℝ) ^ ε ≤ c₁ * (wordDiam a / ℓ) :=
      mul_le_mul_of_nonneg_left hdiam'.le hc₁.le
    have e : c₁ * wordDiam a / ℓ = c₁ * (wordDiam a / ℓ) := by ring
    linarith
  have hpow : (1 - t) ^ (-C₁) ≤ (W : ℝ) ^ (3 * C₁) := by
    have h1 : (1 - t) ^ (-C₁) ≤ ((W : ℝ) ^ (-3 : ℝ)) ^ (-C₁) :=
      Real.rpow_le_rpow_of_nonpos hW3' hWt (by linarith)
    refine h1.trans (le_of_eq ?_)
    rw [← Real.rpow_mul hW0.le]
    congr 1
    ring
  calc ‖primLoop g W L E m t a σ‖ ≤ ‖primLoopF g L E m t a σ‖ := hle
    _ ≤ C₁ * (1 - t) ^ (-C₁) * Real.exp (-(c₁ * wordDiam a / ℓ)) := hF
    _ ≤ C₁ * (W : ℝ) ^ (3 * C₁) * Real.exp (-(c₁ * (W : ℝ) ^ ε)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow hC₁.le) hexp (Real.exp_pos _).le
          (by positivity)
    _ ≤ (W : ℝ) ^ (-Q) := hW₀ W (le_trans (le_max_left _ _) hW)

/-- (B.16) [b:eq:primitive-long-pair], Lemma B.11 [b:lem:primitive-pair], on the large-coupling
branch of (6.1) [da:eq:propagation-domain], under `L ≥ C_* g² log W`, with `C_κ` depending on
`κ` only, uniformly in `θ`, `c_p` and `F`. -/
theorem primLoop_longPair_large' (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ : ℝ, 1 ≤ Cκ ∧ ∀ θ cp F : ℝ, 0 < θ → θ ≤ 1 / 2 → 0 < cp → 0 < F →
      ∃ Cs C' : ℝ, ∃ W₀ : ℕ, 0 < Cs ∧ 0 < C' ∧ ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, Cκ ≤ g →
      ∀ L : ℕ, 3 ≤ L → Cs * g ^ 2 * Real.log W ≤ L → ∀ E : ℝ, |E| ≤ 2 - κ →
      ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m →
      ∀ v : ℝ, 1 / 2 ≤ v → (W : ℝ) ^ (-3 : ℝ) ≤ 1 - v → ∀ (a b : Fin L) (σ₁ σ₂ : Bool),
        ellProp g L v * Real.log W ^ ((3 : ℝ) / 2) ≤ cycDist a b →
        ‖primLoop g W L E m v ![a, b] ![σ₁, σ₂]‖ ≤
          C' * zetaProp g W L v ^ 2 * weightFn cp θ F W (ellProp g L v) (cycDist a b) := by
  obtain ⟨Cκ₁, hCκ₁, H₁'⟩ := lgu_weighted κ hκ hκ2
  obtain ⟨Cκ₂, R₂, c₂, C₂, hCκ₂, hR₂, hc₂, hC₂, H₂⟩ := lgk_facts κ hκ hκ2
  obtain ⟨Cs₁, C₁, c₁, hCs₁, hC₁, hc₁, H₁⟩ := H₁' 2 le_rfl
  refine ⟨max Cκ₁ Cκ₂, le_trans hCκ₁ (le_max_left _ _), fun θ cp F _hθ _hθ2 _hcp hF => ?_⟩
  obtain ⟨W₀, hW₀3, hW₀⟩ := lgk_pair_analytic hC₁ hc₁ hF
  refine ⟨4 * max Cs₁ R₂, 1, W₀, by positivity, one_pos, ?_⟩
  intro W hW g hg L hL hRL E hE m hm v hv hWv a b σ₁ σ₂ hd
  have hW3 : 3 ≤ W := le_trans hW₀3 hW
  have hv0 : 0 ≤ v := by linarith
  obtain ⟨hv1, hlogW⟩ := lgk_logW hW3 hv0 hWv
  have hg2 : 0 ≤ g ^ 2 := sq_nonneg g
  have hmax : 0 ≤ max Cs₁ R₂ := le_trans hCs₁.le (le_max_left _ _)
  have hX : max Cs₁ R₂ * (1 + |Real.log (1 - v)|) * g ^ 2 ≤ L := by
    calc max Cs₁ R₂ * (1 + |Real.log (1 - v)|) * g ^ 2
        ≤ max Cs₁ R₂ * (4 * Real.log W) * g ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogW hmax) hg2
      _ = 4 * max Cs₁ R₂ * g ^ 2 * Real.log W := by ring
      _ ≤ L := hRL
  have hlog : 0 ≤ |Real.log (1 - v)| := abs_nonneg _
  have h1 : Cs₁ * (1 + |Real.log (1 - v)|) * g ^ 2 ≤ L := le_trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
      hg2) hX
  have h2 : R₂ * (1 + |Real.log (1 - v)|) * g ^ 2 ≤ L := le_trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith))
      hg2) hX
  have Fv := (H₂ g (le_trans (le_max_right _ _) hg) L hL v hv0 hv1 h2 E hE m hm).1
  have hFb := H₁ g (le_trans (le_max_left _ _) hg) v hv0 hv1 L hL h1 E hE m hm ![a, b]
    ![σ₁, σ₂]
  have hW1 : 1 ≤ W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hW3' : 0 < (W : ℝ) ^ (-3 : ℝ) := Real.rpow_pos_of_pos hW0 _
  have h1v : 0 < 1 - v := by linarith
  set ℓ := min (L : ℝ) (g ^ 2 / Real.sqrt (1 - v)) with hℓ
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le (by have := Fv.hg; positivity) Fv.ell_ge
  have hlogW0 : 0 ≤ Real.log W := Real.log_nonneg (by exact_mod_cast hW1)
  have hx0 : 0 ≤ Real.log W ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hlogW0 _
  have hdiam : (cycDist a b : ℝ) ≤ wordDiam ![a, b] := by
    have := lgw_cd_le_diam ![a, b] 0 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    exact_mod_cast this
  have hexp : Real.exp (-(c₁ * wordDiam ![a, b] / ℓ)) ≤
      Real.exp (-(c₁ * Real.log W ^ ((3 : ℝ) / 2))) := by
    apply Real.exp_le_exp.mpr
    have h3 : ℓ * Real.log W ^ ((3 : ℝ) / 2) ≤ wordDiam ![a, b] :=
      le_trans (mul_le_mul_of_nonneg_right Fv.ell_le hx0) (hd.trans hdiam)
    have h4 : Real.log W ^ ((3 : ℝ) / 2) ≤ wordDiam ![a, b] / ℓ := by
      rw [le_div_iff₀ hℓ0]; linarith
    have h5 : c₁ * Real.log W ^ ((3 : ℝ) / 2) ≤ c₁ * (wordDiam ![a, b] / ℓ) :=
      mul_le_mul_of_nonneg_left h4 hc₁.le
    have e : c₁ * wordDiam ![a, b] / ℓ = c₁ * (wordDiam ![a, b] / ℓ) := by ring
    linarith
  have hpow : (1 - v) ^ (-C₁) ≤ (W : ℝ) ^ (3 * C₁) := by
    have h1 : (1 - v) ^ (-C₁) ≤ ((W : ℝ) ^ (-3 : ℝ)) ^ (-C₁) :=
      Real.rpow_le_rpow_of_nonpos hW3' hWv (by linarith)
    refine h1.trans (le_of_eq ?_)
    rw [← Real.rpow_mul hW0.le]
    congr 1
    ring
  have hζ := lgk_zeta_ge Fv hW1
  have hw : (W : ℝ) ^ (-F) ≤ weightFn cp θ F W (ellProp g L v) (cycDist a b) := by
    unfold weightFn
    linarith [Real.exp_pos (-(cp * (↑(cycDist a b) / ellProp g L v) ^ θ))]
  rw [lgk_primLoop_le g E m v (by norm_num) _ _]
  calc ((W : ℝ) ^ (2 - 1))⁻¹ * ‖primLoopF g L E m v ![a, b] ![σ₁, σ₂]‖
      ≤ ((W : ℝ) ^ (2 - 1))⁻¹ * (C₁ * (W : ℝ) ^ (3 * C₁) *
          Real.exp (-(c₁ * Real.log W ^ ((3 : ℝ) / 2)))) := by
        refine mul_le_mul_of_nonneg_left (hFb.trans ?_) (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hC₁.le) hexp (Real.exp_pos _).le
          (by positivity)
    _ ≤ (W : ℝ) ^ (-F) / (4 * (W : ℝ) ^ 2) := hW₀ W hW
    _ = (1 / (2 * W)) ^ 2 * (W : ℝ) ^ (-F) := by field_simp; ring
    _ ≤ zetaProp g W L v ^ 2 * weightFn cp θ F W (ellProp g L v) (cycDist a b) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hζ 2) hw (by positivity)
          (by positivity)
    _ = 1 * zetaProp g W L v ^ 2 * weightFn cp θ F W (ellProp g L v) (cycDist a b) := by ring

/-- (B.14) [b:eq:early-free-label], Lemma B.10 [b:lem:early-primitive](b), W-free form for
every `L ≥ C_* g²`, with the coupling threshold `C_κ` depending on `κ` only, uniformly in `k`. -/
theorem primLoopF_freeLabel' (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ : ℝ, 1 ≤ Cκ ∧ ∀ k : ℕ, 2 ≤ k → ∃ Cs C' : ℝ, 0 < Cs ∧ 0 < C' ∧
      ∀ g : ℝ, Cκ ≤ g → ∀ L : ℕ, 3 ≤ L →
      Cs * g ^ 2 ≤ L → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 → ∀ (i : Fin k) (a : Fin k → Fin L) (σ : Fin k → Bool),
        ∑ b : Fin L, ‖primLoopF g L E m t (Function.update a i b) σ‖ ≤ C' * g ^ 2 := by
  obtain ⟨Cκ₁, hCκ₁, H₁'⟩ := lgu_weighted κ hκ hκ2
  refine ⟨Cκ₁, hCκ₁, fun k hk => ?_⟩
  obtain ⟨Cs₁, C₁, c₁, hCs₁, hC₁, hc₁, H₁⟩ := H₁' k hk
  refine ⟨2 * Cs₁, C₁ * 2 ^ C₁ * (2 * (1 + 2 / c₁)), by positivity, by positivity, ?_⟩
  intro g hg L hL hRL E hE m hm t ht0 ht12 i a σ
  have : NeZero L := ⟨by omega⟩
  have hg1 : 1 ≤ g := le_trans hCκ₁ hg
  have hg2 : 0 < g ^ 2 := by positivity
  have hg21 : 1 ≤ g ^ 2 := one_le_pow₀ hg1
  have ht1 : t < 1 := by linarith
  have h1t : 1 / 2 ≤ 1 - t := by linarith
  have hlog : |Real.log (1 - t)| ≤ 1 := by
    have h2 : Real.log (1 - t) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    have h3 : Real.log (1 / 2) ≤ Real.log (1 - t) := Real.log_le_log (by norm_num) h1t
    rw [one_div, Real.log_inv] at h3
    have h4 := Real.log_two_lt_d9
    rw [abs_of_nonpos h2]
    linarith
  have h1 : Cs₁ * (1 + |Real.log (1 - t)|) * g ^ 2 ≤ L := by
    calc Cs₁ * (1 + |Real.log (1 - t)|) * g ^ 2 ≤ Cs₁ * 2 * g ^ 2 := by
          gcongr; linarith
      _ = 2 * Cs₁ * g ^ 2 := by ring
      _ ≤ L := hRL
  set ℓ := min (L : ℝ) (g ^ 2 / Real.sqrt (1 - t)) with hℓ
  have hs : 1 / 2 ≤ Real.sqrt (1 - t) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hs0 : 0 < Real.sqrt (1 - t) := by linarith
  have hℓ0 : 0 < ℓ := lt_min (by exact_mod_cast (show 0 < L by omega)) (by positivity)
  have hℓ2 : ℓ ≤ 2 * g ^ 2 := by
    refine (min_le_right _ _).trans ?_
    rw [div_le_iff₀ hs0]
    nlinarith
  have hpow : (1 - t) ^ (-C₁) ≤ 2 ^ C₁ := by
    have := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 2) h1t
      (by linarith : -C₁ ≤ 0)
    refine this.trans (le_of_eq ?_)
    rw [Real.rpow_neg (by norm_num), one_div, Real.inv_rpow (by norm_num), inv_inv]
  set j : Fin k := if i.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩ with hj
  have hji : j ≠ i := by
    intro h
    have := congrArg Fin.val h
    simp only [hj] at this
    split_ifs at this with h0 <;> simp at this <;> omega
  have hterm : ∀ b : Fin L, ‖primLoopF g L E m t (Function.update a i b) σ‖ ≤
      C₁ * 2 ^ C₁ * Real.exp (-(c₁ * (cycDist (b - a j) 0 : ℝ) / (2 * g ^ 2))) := by
    intro b
    refine (H₁ g hg t ht0 ht1 L hL h1 E hE m hm _ σ).trans ?_
    refine mul_le_mul (mul_le_mul_of_nonneg_left hpow hC₁.le) (Real.exp_le_exp.mpr ?_)
      (Real.exp_pos _).le (by positivity)
    have hd : (cycDist b (a j) : ℝ) ≤ wordDiam (Function.update a i b) := by
      have := lgw_cd_le_diam (Function.update a i b) i j
      rw [Function.update_self, Function.update_of_ne hji] at this
      exact_mod_cast this
    rw [← lgk_u_cycDist_sub_zero]
    have h3 : c₁ * (cycDist b (a j) : ℝ) / (2 * g ^ 2) ≤
        c₁ * wordDiam (Function.update a i b) / ℓ := by
      calc c₁ * (cycDist b (a j) : ℝ) / (2 * g ^ 2) ≤ c₁ * (cycDist b (a j) : ℝ) / ℓ :=
            div_le_div_of_nonneg_left (by positivity) hℓ0 hℓ2
        _ ≤ c₁ * wordDiam (Function.update a i b) / ℓ := by
            gcongr
    linarith
  calc ∑ b : Fin L, ‖primLoopF g L E m t (Function.update a i b) σ‖
      ≤ ∑ b : Fin L, C₁ * 2 ^ C₁ * Real.exp (-(c₁ * (cycDist (b - a j) 0 : ℝ) / (2 * g ^ 2))) :=
        Finset.sum_le_sum fun b _ => hterm b
    _ = C₁ * 2 ^ C₁ * ∑ y : Fin L, Real.exp (-(c₁ * (cycDist y 0 : ℝ) / (2 * g ^ 2))) := by
        rw [← Finset.mul_sum]
        congr 1
        exact Fintype.sum_equiv (Equiv.subRight (a j)) _ _ (fun b => rfl)
    _ ≤ C₁ * 2 ^ C₁ * (2 * (1 + 2 * g ^ 2 / c₁)) :=
        mul_le_mul_of_nonneg_left (lgk_u_geom_sum c₁ (2 * g ^ 2) hc₁ (by positivity))
          (by positivity)
    _ ≤ C₁ * 2 ^ C₁ * ((2 * (1 + 2 / c₁)) * g ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have e : 2 * g ^ 2 / c₁ = (2 / c₁) * g ^ 2 := by ring
        rw [e]
        have h2c : 0 ≤ 2 / c₁ := by positivity
        nlinarith
    _ = C₁ * 2 ^ C₁ * (2 * (1 + 2 / c₁)) * g ^ 2 := by ring

end Uniform

end LSBA
