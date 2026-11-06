import LSBA.Primitive.Solve
import LSBA.Kernel.Bounded

/-!
# Primitive loops: early-time, coarse and tail bounds

(B.13) [b:eq:early-primitive] on `0 ≤ t ≤ 1/2`, the coarse bounds (7.20)
[uvc:eq:primitive-coarse-row] and (7.21) [uvc:eq:primitive-coarse-derivative] from `|M_B| ≤ C_M`,
the weighted bound of Proposition B.2 [ba:prop:primitive] at bounded coupling, and the tail
(5.22)(a) [gc:eq:one-step-input].
-/

open MeasureTheory Real Filter Topology Complex Finset
open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ## The cyclic distance and the diameter of a word -/

section Cyc

variable {L : ℕ}

private lemma early_mod {x y : ℕ} (hx : x < L) (hy : y < L) :
    (x + L - y) % L = if y ≤ x then x - y else x + L - y := by
  split_ifs with h
  · have : x + L - y = (x - y) + L := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

private lemma early_cd_comm (a b : Fin L) : cycDist a b = cycDist b a := by
  unfold cycDist; exact min_comm _ _

private lemma early_cd_self (a : Fin L) : cycDist a a = 0 := by
  simp [cycDist]

private lemma early_cd_tri (a b c : Fin L) : cycDist a c ≤ cycDist a b + cycDist b c := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  simp only [cycDist, early_mod ha hb, early_mod hb ha, early_mod ha hc, early_mod hc ha,
    early_mod hb hc, early_mod hc hb]
  split_ifs <;> omega

private lemma early_cd_le_diam {k : ℕ} (a : Fin k → Fin L) (p q : Fin k) :
    cycDist (a p) (a q) ≤ wordDiam a :=
  Finset.le_sup (f := fun p : Fin k × Fin k => cycDist (a p.1) (a p.2)) (Finset.mem_univ (p, q))

private lemma early_diam_le {k : ℕ} (a : Fin k → Fin L) {N : ℕ}
    (h : ∀ p q, cycDist (a p) (a q) ≤ N) : wordDiam a ≤ N :=
  Finset.sup_le fun p _ => h p.1 p.2

/-- Moving every label by `d_i` moves the diameter by at most `2 Σ d_i`. -/
private lemma early_diam_perturb {k : ℕ} (a b : Fin k → Fin L) :
    wordDiam a ≤ wordDiam b + 2 * ∑ i, cycDist (a i) (b i) := by
  refine early_diam_le a fun p q => ?_
  have h1 := early_cd_tri (a p) (b p) (a q)
  have h2 := early_cd_tri (b p) (b q) (a q)
  have h3 := early_cd_le_diam b p q
  have h4 : cycDist (a p) (b p) ≤ ∑ i, cycDist (a i) (b i) :=
    Finset.single_le_sum (f := fun i => cycDist (a i) (b i)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ p)
  have h5 : cycDist (a q) (b q) ≤ ∑ i, cycDist (a i) (b i) :=
    Finset.single_le_sum (f := fun i => cycDist (a i) (b i)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ q)
  rw [early_cd_comm (b q) (a q)] at h2
  omega

private lemma early_wexp_perturb (θ : ℝ) (hθ : 0 ≤ θ) {k : ℕ} (a b : Fin k → Fin L) :
    Real.exp (θ * wordDiam a) ≤
      Real.exp (θ * wordDiam b) * ∏ i, Real.exp (2 * θ * cycDist (a i) (b i)) := by
  rw [← Real.exp_sum, ← Real.exp_add, ← Finset.mul_sum]
  apply Real.exp_le_exp.mpr
  have h : (wordDiam a : ℝ) ≤ wordDiam b + 2 * ∑ i, (cycDist (a i) (b i) : ℝ) := by
    exact_mod_cast early_diam_perturb a b
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
private def early_pairX (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (s s' : Bool) :
    Matrix (Fin L) (Fin L) ℂ :=
  if s = s' then (if s then pairQ β M else (pairQ β M).map star)
  else (pairP β M).map ((↑) : ℝ → ℂ)

/-- Under the primitive data, the rows of `|X|` sum to one. -/
private lemma early_pairX_rowsum {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) (s s' : Bool) (a : Fin L) :
    ∑ b, ‖early_pairX β M s s' a b‖ = 1 := by
  have hQ : ∀ b, ‖pairQ β M a b‖ = pairP β M a b := by
    intro b
    simp [pairQ, pairP, norm_pow, Complex.norm_real, abs_of_pos hD.pos]
  have hP : ∀ b, ‖((pairP β M a b : ℝ) : ℂ)‖ = pairP β M a b := by
    intro b
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    simp only [pairP, Matrix.of_apply]
    exact mul_nonneg hD.pos.le (sq_nonneg _)
  rw [← hD.row_sum a]
  unfold early_pairX
  split_ifs
  · exact Finset.sum_congr rfl fun b _ => hQ b
  · exact Finset.sum_congr rfl fun b _ => by rw [Matrix.map_apply, norm_star, hQ b]
  · exact Finset.sum_congr rfl fun b _ => by rw [Matrix.map_apply, hP b]

/-- The pair matrix is symmetric when `M` is. -/
private lemma early_pairX_transpose {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} (hM : Mᵀ = M)
    (s s' : Bool) : (early_pairX β M s s')ᵀ = early_pairX β M s s' := by
  have h : ∀ a b, M b a = M a b := fun a b => congrFun (congrFun hM a) b
  unfold early_pairX
  split_ifs <;> ext a b <;> simp [pairQ, pairP, h a b]

/-- Row sums of `|X|` at most `1` give `‖X‖_{∞→∞} ≤ 1`. -/
private lemma early_norm_le {X : Matrix (Fin L) (Fin L) ℂ} (hX : ∀ a, ∑ b, ‖X a b‖ ≤ 1) :
    ‖X‖ ≤ 1 := by
  have h : ‖X‖₊ ≤ 1 := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun a _ => ?_
    rw [← NNReal.coe_le_coe, NNReal.coe_sum, NNReal.coe_one]
    simpa using hX a
  exact_mod_cast h

/-- `1 - tX` is invertible for `‖X‖ ≤ 1` and `|t| < 1`. -/
private lemma early_isUnit {X : Matrix (Fin L) (Fin L) ℂ} (hX : ‖X‖ ≤ 1) {t : ℝ} (ht : |t| < 1) :
    IsUnit (1 - (t : ℂ) • X) := by
  have h : ‖(t : ℂ) • X‖ < 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc |t| * ‖X‖ ≤ |t| * 1 := mul_le_mul_of_nonneg_left hX (abs_nonneg t)
      _ < 1 := by rwa [mul_one]
  exact ⟨Units.oneSub _ h, Units.val_oneSub _ _⟩

/-- `1 - tX` is invertible for the pair matrices of the primitive data and `|t| < 1`. -/
private lemma early_pairX_isUnit {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {t : ℝ} (ht : |t| < 1) (s s' : Bool) :
    IsUnit (1 - (t : ℂ) • early_pairX β M s s') :=
  early_isUnit (early_norm_le fun a => (early_pairX_rowsum hD s s' a).le) ht

/-- The entrywise image of an inverse under a ring hom of fields. -/
private lemma early_map_inv {R S : Type*} [Field R] [Field S] (f : R →+* S)
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

private lemma early_map_star_eq (A : Matrix (Fin L) (Fin L) ℂ) :
    A.map star = A.map (starRingEnd ℂ) := rfl

/-- The one-label inverse is `(I - tX)⁻¹`. -/
private lemma early_pairV_eq (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) (s s' : Bool) :
    pairV β M t s s' = (1 - (t : ℂ) • early_pairX β M s s')⁻¹ := by
  unfold pairV early_pairX
  split_ifs with h1 h2
  · rfl
  · rw [early_map_star_eq, early_map_inv]
    congr 1
    ext a b
    simp [Matrix.one_apply]
  · rw [show ((1 - t • pairP β M)⁻¹).map ((↑) : ℝ → ℂ) =
        ((1 - t • pairP β M)⁻¹).map Complex.ofRealHom from rfl, early_map_inv]
    congr 1
    ext a b
    simp [Matrix.one_apply]
    split_ifs <;> simp

/-- The pair kernel is `X(I - tX)⁻¹`. -/
private lemma early_pairK_eq (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) (s s' : Bool) :
    pairK β M t s s' = early_pairX β M s s' * (1 - (t : ℂ) • early_pairX β M s s')⁻¹ := by
  have hV := early_pairV_eq β M t s s'
  cases s <;> cases s' <;>
    simp only [pairK, pairV, early_pairX, Bool.false_eq_true, Bool.true_eq_false, ite_true,
      ite_false, mixedKer] at hV ⊢
  · rw [← hV, early_map_star_eq, early_map_star_eq, early_map_star_eq, Matrix.map_mul]
  · rw [← hV, show ((pairP β M * (1 - t • pairP β M)⁻¹)).map ((↑) : ℝ → ℂ) =
        ((pairP β M * (1 - t • pairP β M)⁻¹)).map Complex.ofRealHom from rfl, Matrix.map_mul]
    rfl
  · rw [← hV, show ((pairP β M * (1 - t • pairP β M)⁻¹)).map ((↑) : ℝ → ℂ) =
        ((pairP β M * (1 - t • pairP β M)⁻¹)).map Complex.ofRealHom from rfl, Matrix.map_mul]
    rfl

/-- The propagator is `(I - uX)(I - tX)⁻¹`. -/
private lemma early_pairU_eq (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (u t : ℝ) (s s' : Bool) :
    pairU β M u t s s' = (1 - (u : ℂ) • early_pairX β M s s') *
      (1 - (t : ℂ) • early_pairX β M s s')⁻¹ := by
  unfold pairU early_pairX propPP propPM
  split_ifs with h1 h2
  · rfl
  · rw [early_map_star_eq, Matrix.map_mul, early_map_inv]
    congr 2
    · ext a b
      simp [Matrix.one_apply]
    · ext a b
      simp [Matrix.one_apply]
  · rw [show ((1 - u • pairP β M) * (1 - t • pairP β M)⁻¹).map ((↑) : ℝ → ℂ) =
        ((1 - u • pairP β M) * (1 - t • pairP β M)⁻¹).map Complex.ofRealHom from rfl,
      Matrix.map_mul, early_map_inv]
    congr 2
    · ext a b
      simp [Matrix.one_apply]
      split_ifs <;> simp
    · ext a b
      simp [Matrix.one_apply]
      split_ifs <;> simp

section Generic

variable {X : Matrix (Fin L) (Fin L) ℂ}

private lemma early_inv_mul {t : ℝ} (hU : IsUnit (1 - (t : ℂ) • X)) :
    (1 - (t : ℂ) • X)⁻¹ * (1 - (t : ℂ) • X) = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)

private lemma early_mul_inv {t : ℝ} (hU : IsUnit (1 - (t : ℂ) • X)) :
    (1 - (t : ℂ) • X) * (1 - (t : ℂ) • X)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)

/-- `X` commutes with `(1 - tX)⁻¹`. -/
private lemma early_comm {t : ℝ} (hU : IsUnit (1 - (t : ℂ) • X)) :
    X * (1 - (t : ℂ) • X)⁻¹ = (1 - (t : ℂ) • X)⁻¹ * X := by
  have hc : (1 - (t : ℂ) • X) * X = X * (1 - (t : ℂ) • X) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul]
  set V := (1 - (t : ℂ) • X)⁻¹
  calc X * V = (V * (1 - (t : ℂ) • X)) * X * V := by rw [early_inv_mul hU, Matrix.one_mul]
    _ = V * ((1 - (t : ℂ) • X) * X) * V := by simp only [Matrix.mul_assoc]
    _ = V * (X * (1 - (t : ℂ) • X)) * V := by rw [hc]
    _ = V * X * ((1 - (t : ℂ) • X) * V) := by simp only [Matrix.mul_assoc]
    _ = V * X := by rw [early_mul_inv hU, Matrix.mul_one]

end Generic

section Rows

variable {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}

/-- The entries of the pair matrices have modulus `β |M_{ab}|²`. -/
private lemma early_pairX_norm (hD : PrimData β M m) (s s' : Bool) (a b : Fin L) :
    ‖early_pairX β M s s' a b‖ = β * ‖M a b‖ ^ 2 := by
  have hQ : ‖pairQ β M a b‖ = β * ‖M a b‖ ^ 2 := by
    simp [pairQ, norm_pow, Complex.norm_real, abs_of_pos hD.pos]
  unfold early_pairX
  split_ifs
  · exact hQ
  · rw [Matrix.map_apply, norm_star, hQ]
  · rw [Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    · simp [pairP]
    · simp only [pairP, Matrix.of_apply]
      exact mul_nonneg hD.pos.le (sq_nonneg _)

/-- The one-label inverse is symmetric. -/
private lemma early_V_symm (hD : PrimData β M m) (t : ℝ) (s s' : Bool) :
    (pairV β M t s s')ᵀ = pairV β M t s s' := by
  rw [early_pairV_eq, Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.transpose_smul, early_pairX_transpose hD.symm]

/-- The pair kernel is symmetric. -/
private lemma early_K_symm (hD : PrimData β M m) {t : ℝ} (ht : |t| < 1) (s s' : Bool) :
    (pairK β M t s s')ᵀ = pairK β M t s s' := by
  rw [early_pairK_eq, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.transpose_sub,
    Matrix.transpose_one, Matrix.transpose_smul, early_pairX_transpose hD.symm,
    early_comm (early_pairX_isUnit hD ht s s')]

/-- The pair kernel is `X V`, entrywise. -/
private lemma early_K_apply (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) (s s' : Bool)
    (a b : Fin L) :
    pairK β M t s s' a b = ∑ c, early_pairX β M s s' a c * pairV β M t s s' c b := by
  rw [early_pairK_eq, early_pairV_eq, Matrix.mul_apply]

/-- `V = I + t X V`. -/
private lemma early_V_fix (hD : PrimData β M m) {t : ℝ} (ht : |t| < 1) (s s' : Bool) :
    pairV β M t s s' = 1 + (t : ℂ) • (early_pairX β M s s' * pairV β M t s s') := by
  have h := early_mul_inv (early_pairX_isUnit hD ht s s')
  rw [← early_pairV_eq] at h
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul] at h
  rw [← h]
  abel

/-- `U_{u,t} = I + (t - u) K_t`. -/
private lemma early_U_eq' (hD : PrimData β M m) {t : ℝ} (ht : |t| < 1) (u : ℝ) (s s' : Bool) :
    pairU β M u t s s' = 1 + ((t - u : ℝ) : ℂ) • pairK β M t s s' := by
  have hU := early_pairX_isUnit hD ht s s'
  have h : (1 - (u : ℂ) • early_pairX β M s s') =
      (1 - (t : ℂ) • early_pairX β M s s') + ((t - u : ℝ) : ℂ) • early_pairX β M s s' := by
    push_cast
    rw [sub_smul]
    abel
  rw [early_pairU_eq, h, add_mul, early_mul_inv hU, Matrix.smul_mul, early_pairK_eq]

/-- Row sums of the one-label inverse for `0 ≤ t < 1`. -/
private lemma early_V_row (hD : PrimData β M m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (s s' : Bool) (a : Fin L) : ∑ b, ‖pairV β M t s s' a b‖ ≤ (1 - t)⁻¹ := by
  have ht : |t| < 1 := abs_lt.mpr ⟨by linarith, ht1⟩
  have hfix := early_V_fix hD ht s s'
  set V := pairV β M t s s' with hVdef
  set X := early_pairX β M s s' with hXdef
  set S : Fin L → ℝ := fun c => ∑ b, ‖V c b‖ with hS
  have hrow : ∀ c, ∑ d, ‖X c d‖ = 1 := fun c => early_pairX_rowsum hD s s' c
  have step : ∀ x, S x ≤ 1 + t * ∑ c, ‖X x c‖ * S c := by
    intro x
    calc S x = ∑ b, ‖V x b‖ := rfl
      _ ≤ ∑ b, ((if x = b then (1 : ℝ) else 0) + t * ∑ c, ‖X x c‖ * ‖V c b‖) := by
          refine Finset.sum_le_sum fun b _ => ?_
          have e : V x b = (if x = b then 1 else 0) + (t : ℂ) * ∑ c, X x c * V c b := by
            conv_lhs => rw [hfix]
            simp [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply]
          rw [e]
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · split_ifs <;> simp
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
            refine mul_le_mul_of_nonneg_left ?_ ht0
            exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => by rw [norm_mul])
      _ = 1 + t * ∑ c, ‖X x c‖ * S c := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
          congr 2
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [hS]
          simp only [Finset.mul_sum]
  obtain ⟨a₀, -, ha₀⟩ := Finset.exists_max_image Finset.univ S ⟨a, Finset.mem_univ a⟩
  have h1 : S a₀ ≤ 1 + t * S a₀ := by
    refine (step a₀).trans ?_
    have : ∑ c, ‖X a₀ c‖ * S c ≤ ∑ c, ‖X a₀ c‖ * S a₀ :=
      Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (ha₀ c (Finset.mem_univ c))
        (norm_nonneg _)
    rw [← Finset.sum_mul, hrow, one_mul] at this
    nlinarith
  have h2 : S a₀ ≤ (1 - t)⁻¹ := by
    rw [← one_div, le_div_iff₀ (by linarith)]
    nlinarith
  exact (ha₀ a (Finset.mem_univ a)).trans h2

/-- Row sums of the pair kernel for `0 ≤ t < 1`. -/
private lemma early_K_row (hD : PrimData β M m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (s s' : Bool) (a : Fin L) : ∑ b, ‖pairK β M t s s' a b‖ ≤ (1 - t)⁻¹ := by
  calc ∑ b, ‖pairK β M t s s' a b‖
      ≤ ∑ b, ∑ c, ‖early_pairX β M s s' a c‖ * ‖pairV β M t s s' c b‖ := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [early_K_apply]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => by rw [norm_mul])
    _ = ∑ c, ‖early_pairX β M s s' a c‖ * ∑ b, ‖pairV β M t s s' c b‖ := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
    _ ≤ ∑ c, ‖early_pairX β M s s' a c‖ * (1 - t)⁻¹ :=
        Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (early_V_row hD ht0 ht1 s s' c)
          (norm_nonneg _)
    _ = (1 - t)⁻¹ := by rw [← Finset.sum_mul, early_pairX_rowsum hD, one_mul]

/-- Row sums of the propagators: `Σ_b |U_{u,t}(a, b)| ≤ (1 - u)/(1 - t)`. -/
private lemma early_U_row (hD : PrimData β M m) {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (ht1 : t < 1)
    (s s' : Bool) (a : Fin L) : ∑ b, ‖pairU β M u t s s' a b‖ ≤ (1 - u) / (1 - t) := by
  have ht0 : 0 ≤ t := hu.trans hut
  have ht : |t| < 1 := abs_lt.mpr ⟨by linarith, ht1⟩
  have h1t : 0 < 1 - t := by linarith
  calc ∑ b, ‖pairU β M u t s s' a b‖
      ≤ ∑ b, ((if a = b then (1 : ℝ) else 0) + (t - u) * ‖pairK β M t s s' a b‖) := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [early_U_eq' hD ht]
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · split_ifs <;> simp
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    _ = 1 + (t - u) * ∑ b, ‖pairK β M t s s' a b‖ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp
    _ ≤ 1 + (t - u) * (1 - t)⁻¹ := by
        have := mul_le_mul_of_nonneg_left (early_K_row hD ht0 ht1 s s' a) (by linarith : 0 ≤ t - u)
        linarith
    _ = (1 - u) / (1 - t) := by
        field_simp
        ring

/-- The columns of the propagators have the same bound (the propagator is symmetric). -/
private lemma early_U_symm (hD : PrimData β M m) {t : ℝ} (ht : |t| < 1) (u : ℝ) (s s' : Bool) :
    (pairU β M u t s s')ᵀ = pairU β M u t s s' := by
  rw [early_U_eq' hD ht, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul,
    early_K_symm hD ht]

/-- The entries of the pair kernel are at most `β C_M² /(1 - t)` if `|M_{ab}| ≤ C_M`. -/
private lemma early_K_entry (hD : PrimData β M m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {CM : ℝ}
    (hCM : ∀ a b, ‖M a b‖ ≤ CM) (s s' : Bool) (a b : Fin L) :
    ‖pairK β M t s s' a b‖ ≤ β * CM ^ 2 * (1 - t)⁻¹ := by
  have hX : ∀ c, ‖early_pairX β M s s' a c‖ ≤ β * CM ^ 2 := by
    intro c
    rw [early_pairX_norm hD]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hCM a c) 2) hD.pos.le
  calc ‖pairK β M t s s' a b‖
      ≤ ∑ c, ‖early_pairX β M s s' a c‖ * ‖pairV β M t s s' c b‖ := by
        rw [early_K_apply]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => by rw [norm_mul])
    _ ≤ ∑ c, β * CM ^ 2 * ‖pairV β M t s s' b c‖ := by
        refine Finset.sum_le_sum fun c _ => ?_
        have e : pairV β M t s s' c b = pairV β M t s s' b c := by
          have := congrFun (congrFun (early_V_symm hD t s s') b) c
          simpa [Matrix.transpose_apply] using this
        rw [e]
        exact mul_le_mul_of_nonneg_right (hX c) (norm_nonneg _)
    _ ≤ β * CM ^ 2 * (1 - t)⁻¹ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (early_V_row hD ht0 ht1 s s' b) (by
          have := hD.pos
          positivity)

end Rows

end Algebra

/-! ## Propagation of the weighted sup and row bounds through the labels -/

section Propagate

variable {L : ℕ}

/-- The sum over words of a product of one-label factors is the product of the sums. -/
private lemma early_sum_prod {n : ℕ} (f : Fin n → Fin L → ℝ) :
    ∑ b : Fin n → Fin L, ∏ i, f i (b i) = ∏ i, ∑ y, f i y := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- Sum over words of a function of the word updated at `j`. -/
private lemma early_sum_update {n : ℕ} (j : Fin n) (Θ : (Fin n → Fin L) → ℝ) :
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
private lemma early_prop_sup (θ : ℝ) (hθ : 0 ≤ θ) {n : ℕ} (U : Fin n → Matrix (Fin L) (Fin L) ℂ)
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
        have h1 := early_wexp_perturb θ hθ a b
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
        rw [← Finset.sum_mul, early_sum_prod, mul_comm]
    _ ≤ N * r ^ n := by
        refine mul_le_mul_of_nonneg_left ?_ hN
        calc ∏ i, ∑ y, f i y ≤ ∏ _i : Fin n, r :=
              Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun y _ => hf0 i y)
                (fun i _ => hrow i (a i))
          _ = r ^ n := by simp
    _ = r ^ n * N := by ring

/-- Propagation of the weighted row bound at the slot `j` through the one-label factors `U_i`. -/
private lemma early_prop_row (θ : ℝ) (hθ : 0 ≤ θ) {n : ℕ} (U : Fin n → Matrix (Fin L) (Fin L) ℂ)
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
          have h1 := early_wexp_perturb θ hθ a' b
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
          rw [← early_sum_update j (fun b => Q b * H b)]
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
          rw [early_sum_prod, ← Finset.mul_prod_erase Finset.univ (fun i => ∑ y, g i y)
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
private lemma early_cutL_c {k : ℕ} (b : Fin k → Fin L) (i j : Fin k) (c c₀ : Fin L) :
    cutLLab b i j c = Function.update (cutLLab b i j c₀)
      ⟨i.val, by have := j.2; omega⟩ c := by
  funext p
  simp only [cutLLab, Function.update_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- The label `c` sits at the last position of the right cut word. -/
private lemma early_cutR_c {k : ℕ} (b : Fin k → Fin L) (i j : Fin k) (c c₀ : Fin L) :
    cutRLab b i j c = Function.update (cutRLab b i j c₀) (Fin.last (j.val - i.val)) c := by
  funext p
  simp only [cutRLab, Function.update_apply, Fin.ext_iff, Fin.val_last]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- A label of `b` to the left of `i` is a label of the left cut word. -/
private lemma early_cut_update_lt {k : ℕ} (b : Fin k → Fin L) (i j j₀ : Fin k)
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
private lemma early_cut_update_mid {k : ℕ} (b : Fin k → Fin L) (i j j₀ : Fin k)
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
private lemma early_cut_update_ge {k : ℕ} (b : Fin k → Fin L) (i j j₀ : Fin k)
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
private lemma early_diam_cut {k : ℕ} (b : Fin k → Fin L) (i j : Fin k) (hij : i.val < j.val)
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
  refine early_diam_le b fun p q => ?_
  rcases hmem p with ⟨rp, hrp⟩ | ⟨rp, hrp⟩ <;> rcases hmem q with ⟨rq, hrq⟩ | ⟨rq, hrq⟩
  · have := early_cd_le_diam (cutLLab b i j c) rp rq
    rw [hrp, hrq] at this
    omega
  · have h1 := early_cd_le_diam (cutLLab b i j c) rp rLc
    have h2 := early_cd_le_diam (cutRLab b i j c) rRc rq
    rw [hrp, hrLc] at h1
    rw [hrRc, hrq] at h2
    have := early_cd_tri (b p) c (b q)
    omega
  · have h1 := early_cd_le_diam (cutRLab b i j c) rp rRc
    have h2 := early_cd_le_diam (cutLLab b i j c) rLc rq
    rw [hrp, hrRc] at h1
    rw [hrLc, hrq] at h2
    have := early_cd_tri (b p) c (b q)
    omega
  · have := early_cd_le_diam (cutRLab b i j c) rp rq
    rw [hrp, hrq] at this
    omega

end CutWords

/-! ## The induction on the length -/

section Induct

variable {L : ℕ}

/-- The weighted sup bound and the weighted row bound of `F_n` up to the time `T`, with the
profile `(1 - t)^{-(2n-3)}` of (7.20) [uvc:eq:primitive-coarse-row]. -/
private def early_Bd (θ β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (T : ℝ) (n : ℕ)
    (A : ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t ≤ T →
    (∀ (a : Fin n → Fin L) (σ : Fin n → Bool),
      Real.exp (θ * wordDiam a) * ‖primF β M m t a σ‖ ≤ A * ((1 - t) ^ (2 * n - 3))⁻¹) ∧
    (∀ (j : Fin n) (a : Fin n → Fin L) (σ : Fin n → Bool),
      β * ∑ c : Fin L, Real.exp (θ * wordDiam (Function.update a j c)) *
        ‖primF β M m t (Function.update a j c) σ‖ ≤ A * ((1 - t) ^ (2 * n - 3))⁻¹)

/-- The diagonal source of the Duhamel formula (5.16) [fo:eq:duhamel]. -/
private def early_src (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (n : ℕ) (u : ℝ)
    (σ : Fin n → Bool) (b : Fin n → Fin L) : ℂ :=
  ∑ d ∈ polyDiags n, ∑ c : Fin L,
    primF β M m u (cutLLab b d.1 d.2 c) (cutLSgn σ d.1 d.2) *
      primF β M m u (cutRLab b d.1 d.2 c) (cutRSgn σ d.1 d.2)

/-- The children of a diagonal have lengths in `[2, n - 1]` (in fact `[3, n - 1]`). -/
private lemma early_diag_len {n : ℕ} {d : Fin n × Fin n} (hd : d ∈ polyDiags n) :
    2 ≤ n + d.1.val - d.2.val + 1 ∧ n + d.1.val - d.2.val + 1 < n ∧
      2 ≤ d.2.val - d.1.val + 1 ∧ d.2.val - d.1.val + 1 < n ∧ d.1.val < d.2.val := by
  have hd' : IsPolyDiag n d := (Finset.mem_filter.mp hd).2
  obtain ⟨h1, h2⟩ := hd'
  have := d.2.2
  have := d.1.2
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- Sup bound for one diagonal term of the source. -/
private lemma early_term_sup {θ β : ℝ} (hθ : 0 ≤ θ) (hβ : 0 < β) {M : Matrix (Fin L) (Fin L) ℂ}
    {m : ℂ} {T A : ℝ} {n : ℕ}
    (hIH : ∀ n', 2 ≤ n' → n' < n → early_Bd θ β M m T n' A) {u : ℝ} (hu : 0 ≤ u) (huT : u ≤ T)
    (σ : Fin n → Bool) (b : Fin n → Fin L) {d : Fin n × Fin n} (hd : d ∈ polyDiags n) :
    β * (Real.exp (θ * wordDiam b) * ‖∑ c : Fin L,
      primF β M m u (cutLLab b d.1 d.2 c) (cutLSgn σ d.1 d.2) *
        primF β M m u (cutRLab b d.1 d.2 c) (cutRSgn σ d.1 d.2)‖) ≤
      A ^ 2 * ((1 - u) ^ (2 * n - 2))⁻¹ := by
  obtain ⟨hL1, hL2, hR1, hR2, hij⟩ := early_diag_len hd
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
    simpa only [← early_cutR_c b i j _ c₀] using this
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
          have := early_diam_cut b i j hij c
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
private lemma early_src_sup {θ β : ℝ} (hθ : 0 ≤ θ) (hβ : 0 < β) {M : Matrix (Fin L) (Fin L) ℂ}
    {m : ℂ} {T A : ℝ} {n : ℕ}
    (hIH : ∀ n', 2 ≤ n' → n' < n → early_Bd θ β M m T n' A) {u : ℝ} (hu : 0 ≤ u) (huT : u ≤ T)
    (σ : Fin n → Bool) (b : Fin n → Fin L) :
    β * (Real.exp (θ * wordDiam b) * ‖early_src β M m n u σ b‖) ≤
      ((polyDiags n).card : ℝ) * (A ^ 2 * ((1 - u) ^ (2 * n - 2))⁻¹) := by
  calc β * (Real.exp (θ * wordDiam b) * ‖early_src β M m n u σ b‖)
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
        Finset.sum_le_sum fun d hd => early_term_sup hθ hβ hIH hu huT σ b hd
    _ = ((polyDiags n).card : ℝ) * (A ^ 2 * ((1 - u) ^ (2 * n - 2))⁻¹) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- Pointwise: the weight times the modulus of a diagonal term is at most the sum of the products
of the weighted moduli of the two cut loops. -/
private lemma early_term_pw {θ β : ℝ} (hθ : 0 ≤ θ) {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} {n : ℕ}
    (u : ℝ) (σ : Fin n → Bool) (b : Fin n → Fin L) {d : Fin n × Fin n} (hd : d ∈ polyDiags n) :
    Real.exp (θ * wordDiam b) * ‖∑ c : Fin L,
      primF β M m u (cutLLab b d.1 d.2 c) (cutLSgn σ d.1 d.2) *
        primF β M m u (cutRLab b d.1 d.2 c) (cutRSgn σ d.1 d.2)‖ ≤
      ∑ c : Fin L, (Real.exp (θ * wordDiam (cutLLab b d.1 d.2 c)) *
        ‖primF β M m u (cutLLab b d.1 d.2 c) (cutLSgn σ d.1 d.2)‖) *
          (Real.exp (θ * wordDiam (cutRLab b d.1 d.2 c)) *
        ‖primF β M m u (cutRLab b d.1 d.2 c) (cutRSgn σ d.1 d.2)‖) := by
  obtain ⟨-, -, -, -, hij⟩ := early_diag_len hd
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
          have := early_diam_cut b d.1 d.2 hij c
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
private lemma early_comb {X : Type*} [Fintype X] {β AL AR : ℝ} (hβ : 0 < β) (hAL : 0 ≤ AL)
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
private lemma early_term_row {θ β : ℝ} (hθ : 0 ≤ θ) (hβ : 0 < β)
    {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} {T A : ℝ} {n : ℕ}
    (hIH : ∀ n', 2 ≤ n' → n' < n → early_Bd θ β M m T n' A) {u : ℝ} (hu : 0 ≤ u) (huT : u ≤ T)
    (σ : Fin n → Bool) (b : Fin n → Fin L) (j₀ : Fin n) {d : Fin n × Fin n}
    (hd : d ∈ polyDiags n) :
    β ^ 2 * ∑ x : Fin L, Real.exp (θ * wordDiam (Function.update b j₀ x)) *
      ‖∑ c : Fin L, primF β M m u (cutLLab (Function.update b j₀ x) d.1 d.2 c)
          (cutLSgn σ d.1 d.2) *
        primF β M m u (cutRLab (Function.update b j₀ x) d.1 d.2 c) (cutRSgn σ d.1 d.2)‖ ≤
      A ^ 2 * ((1 - u) ^ (2 * n - 2))⁻¹ := by
  obtain ⟨hL1, hL2, hR1, hR2, hij⟩ := early_diag_len hd
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
    fun x => early_term_pw hθ u σ (Function.update b j₀ x) hd
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
      rw [(early_cut_update_lt b i j j₀ hij h1 x c).1, early_cutL_c b i j c c₀]
    have hRw : ∀ x c, cutRLab (Function.update b j₀ x) i j c =
        Function.update R₀ (Fin.last (j.val - i.val)) c := by
      intro x c
      rw [(early_cut_update_lt b i j j₀ hij h1 x c).2, early_cutR_c b i j c c₀]
    simp only [hLw, hRw]
    exact early_comb hβ hAL
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
        rw [(early_cut_update_mid b i j j₀ (by omega) h2 x c).1, early_cutR_c b i j c c₀]
      have hLw : ∀ x c, cutLLab (Function.update b j₀ x) i j c =
          Function.update L₀ ⟨i.val, by have := j.2; omega⟩ c := by
        intro x c
        rw [(early_cut_update_mid b i j j₀ (by omega) h2 x c).2, early_cutL_c b i j c c₀]
      simp only [hLw, hRw]
      have key := early_comb (X := Fin L) hβ hAR
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
        rw [(early_cut_update_ge b i j j₀ hij (by omega) x c).1, early_cutL_c b i j c c₀]
      have hRw : ∀ x c, cutRLab (Function.update b j₀ x) i j c =
          Function.update R₀ (Fin.last (j.val - i.val)) c := by
        intro x c
        rw [(early_cut_update_ge b i j j₀ hij (by omega) x c).2, early_cutR_c b i j c c₀]
      simp only [hLw, hRw]
      exact early_comb hβ hAL
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
private lemma early_src_row {θ β : ℝ} (hθ : 0 ≤ θ) (hβ : 0 < β) {M : Matrix (Fin L) (Fin L) ℂ}
    {m : ℂ} {T A : ℝ} {n : ℕ}
    (hIH : ∀ n', 2 ≤ n' → n' < n → early_Bd θ β M m T n' A) {u : ℝ} (hu : 0 ≤ u) (huT : u ≤ T)
    (σ : Fin n → Bool) (b : Fin n → Fin L) (j₀ : Fin n) :
    β ^ 2 * ∑ x : Fin L, Real.exp (θ * wordDiam (Function.update b j₀ x)) *
      ‖early_src β M m n u σ (Function.update b j₀ x)‖ ≤
      ((polyDiags n).card : ℝ) * (A ^ 2 * ((1 - u) ^ (2 * n - 2))⁻¹) := by
  calc β ^ 2 * ∑ x : Fin L, Real.exp (θ * wordDiam (Function.update b j₀ x)) *
        ‖early_src β M m n u σ (Function.update b j₀ x)‖
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
        Finset.sum_le_sum fun d hd => early_term_row hθ hβ hIH hu huT σ b j₀ hd
    _ = ((polyDiags n).card : ℝ) * (A ^ 2 * ((1 - u) ^ (2 * n - 2))⁻¹) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- `∫_0^t (1 - u)^{-(p+1)} du ≤ (1 - t)^{-p}` for `p ≥ 1`. -/
private lemma early_int {p : ℕ} (hp : 1 ≤ p) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
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
private lemma early_pairU_cont {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {t : ℝ} (ht : |t| < 1) (s s' : Bool) (a b : Fin L) :
    Continuous fun u : ℝ => pairU β M u t s s' a b := by
  have : (fun u : ℝ => pairU β M u t s s' a b) = fun u : ℝ =>
      (1 : Matrix (Fin L) (Fin L) ℂ) a b + ((t - u : ℝ) : ℂ) * pairK β M t s s' a b := by
    funext u
    rw [early_U_eq' hD ht]
    simp [Matrix.add_apply, Matrix.smul_apply]
  rw [this]
  fun_prop

/-- `F_k`, `k ≥ 2`, is continuous in time on `[0, t]`, `t < 1`. -/
private lemma early_primF_cont {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {t : ℝ} (ht1 : t < 1) {k : ℕ} (hk : 2 ≤ k) (a : Fin k → Fin L)
    (σ : Fin k → Bool) : ContinuousOn (fun s => primF β M m s a σ) (Set.Icc 0 t) :=
  fun s hs => (primF_hasDerivAt hD s ⟨by linarith [hs.1], by linarith [hs.2]⟩ hk a
    σ).continuousAt.continuousWithinAt

/-- The Duhamel integrand is continuous in time. -/
private lemma early_g_cont {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} (hD : PrimData β M m)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {n : ℕ} (a : Fin n → Fin L) (σ : Fin n → Bool) :
    ContinuousOn (fun u : ℝ => ∑ b : Fin n → Fin L,
      (∏ j, pairU β M u t (σ j) (σ (finRotate n j)) (a j) (b j)) * early_src β M m n u σ b)
      (Set.Icc 0 t) := by
  have ht : |t| < 1 := abs_lt.mpr ⟨by linarith, ht1⟩
  refine continuousOn_finsetSum _ fun b _ => ContinuousOn.mul ?_ ?_
  · exact (continuous_finsetProd _ fun j _ => early_pairU_cont hD ht _ _ _ _).continuousOn
  · unfold early_src
    refine continuousOn_finsetSum _ fun d hd => continuousOn_finsetSum _ fun c _ =>
      ContinuousOn.mul ?_ ?_
    · obtain ⟨h1, -, -, -, -⟩ := early_diag_len hd
      exact early_primF_cont hD ht1 h1 _ _
    · obtain ⟨-, -, h1, -, -⟩ := early_diag_len hd
      exact early_primF_cont hD ht1 h1 _ _

/-- The columns of the propagators: the row bound passes to the column bound by symmetry. -/
private lemma early_U_col {θ β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} (hD : PrimData β M m)
    {u t r : ℝ} (ht : |t| < 1) (s s' : Bool)
    (hrow : ∀ a, ∑ y, Real.exp (2 * θ * cycDist a y) * ‖pairU β M u t s s' a y‖ ≤ r) (b : Fin L) :
    ∑ a, Real.exp (2 * θ * cycDist a b) * ‖pairU β M u t s s' a b‖ ≤ r := by
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_)) (hrow b)
  have e : pairU β M u t s s' a b = pairU β M u t s s' b a := by
    have := congrFun (congrFun (early_U_symm hD ht u s s') b) a
    simpa [Matrix.transpose_apply] using this
  rw [e, early_cd_comm a b]

/-- The algebra of the integrand of the source: the powers of `1 - u`. -/
private lemma early_alg {Bp A N : ℝ} {n : ℕ} (hn : 2 ≤ n) {u t : ℝ} (hu : u < 1) (ht : t < 1) :
    (Bp * ((1 - u) / (1 - t))) ^ n * (N * (A ^ 2 * ((1 - u) ^ (2 * n - 2))⁻¹)) =
      (Bp ^ n * N * A ^ 2 * ((1 - t) ^ n)⁻¹) * ((1 - u) ^ (n - 2))⁻¹ := by
  have hu' : 0 < 1 - u := by linarith
  have ht' : 0 < 1 - t := by linarith
  have h2 : 2 * n - 2 = n + (n - 2) := by omega
  rw [h2, pow_add, mul_pow, div_pow]
  field_simp

/-- The source part of the weighted sup bound of Duhamel's formula. -/
private lemma early_int_sup {θ β : ℝ} (hθ : 0 ≤ θ) {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {T Bp A : ℝ} {n : ℕ} (hn : 4 ≤ n) (hT1 : T < 1) (hBp : 0 ≤ Bp)
    (hU : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T → ∀ (s s' : Bool) (a : Fin L),
      ∑ b, Real.exp (2 * θ * cycDist a b) * ‖pairU β M u t s s' a b‖ ≤ Bp * ((1 - u) / (1 - t)))
    (hIH : ∀ n', 2 ≤ n' → n' < n → early_Bd θ β M m T n' A) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    (a : Fin n → Fin L) (σ : Fin n → Bool) :
    β * (Real.exp (θ * wordDiam a) * ‖∫ u in (0 : ℝ)..t, ∑ b : Fin n → Fin L,
        (∏ j, pairU β M u t (σ j) (σ (finRotate n j)) (a j) (b j)) *
          early_src β M m n u σ b‖) ≤
      Bp ^ n * ((polyDiags n).card : ℝ) * A ^ 2 * ((1 - t) ^ (2 * n - 3))⁻¹ := by
  have hβ := hD.pos
  have ht1 : t < 1 := lt_of_le_of_lt htT hT1
  have ht : |t| < 1 := abs_lt.mpr ⟨by linarith, ht1⟩
  have h1t : 0 < 1 - t := by linarith
  set g : ℝ → ℂ := fun u => ∑ b : Fin n → Fin L,
    (∏ j, pairU β M u t (σ j) (σ (finRotate n j)) (a j) (b j)) * early_src β M m n u σ b with hg
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
    have hG : ∀ b : Fin n → Fin L, Real.exp (θ * wordDiam b) * ‖early_src β M m n u σ b‖ ≤
        X / β := fun b => by
      rw [le_div_iff₀ hβ, mul_comm]
      exact early_src_sup hθ hβ hIH hu0 huT σ b
    have hP := early_prop_sup θ hθ (fun i => pairU β M u t (σ i) (σ (finRotate n i)))
      (div_nonneg hX0 hβ.le) hrowU (early_src β M m n u σ) hG a
    have hr0 : 0 ≤ Bp * ((1 - u) / (1 - t)) :=
      le_trans (Finset.sum_nonneg fun b _ => by positivity)
        (hrowU ⟨0, by omega⟩ (a ⟨0, by omega⟩))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc β * w * ‖g u‖ = β * (w * ‖g u‖) := by ring
      _ ≤ β * ((Bp * ((1 - u) / (1 - t))) ^ n * (X / β)) :=
          mul_le_mul_of_nonneg_left hP hβ.le
      _ = (Bp * ((1 - u) / (1 - t))) ^ n * X := by field_simp
      _ = Cst * ((1 - u) ^ (n - 2))⁻¹ := early_alg (by omega) hu1 ht1
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
    have := early_int hn3 ht0 ht1
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
private lemma early_int_row {θ β : ℝ} (hθ : 0 ≤ θ) {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {T Bp A : ℝ} {n : ℕ} (hn : 4 ≤ n) (hT1 : T < 1) (hBp : 0 ≤ Bp)
    (hU : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T → ∀ (s s' : Bool) (a : Fin L),
      ∑ b, Real.exp (2 * θ * cycDist a b) * ‖pairU β M u t s s' a b‖ ≤ Bp * ((1 - u) / (1 - t)))
    (hIH : ∀ n', 2 ≤ n' → n' < n → early_Bd θ β M m T n' A) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    (j : Fin n) (a : Fin n → Fin L) (σ : Fin n → Bool) :
    β * ∑ x : Fin L, Real.exp (θ * wordDiam (Function.update a j x)) *
        ‖(β : ℂ) * ∫ u in (0 : ℝ)..t, ∑ b : Fin n → Fin L,
          (∏ i, pairU β M u t (σ i) (σ (finRotate n i)) ((Function.update a j x) i) (b i)) *
            early_src β M m n u σ b‖ ≤
      Bp ^ n * ((polyDiags n).card : ℝ) * A ^ 2 * ((1 - t) ^ (2 * n - 3))⁻¹ := by
  have hβ := hD.pos
  have ht1 : t < 1 := lt_of_le_of_lt htT hT1
  have ht : |t| < 1 := abs_lt.mpr ⟨by linarith, ht1⟩
  have h1t : 0 < 1 - t := by linarith
  set g : (Fin L) → ℝ → ℂ := fun x u => ∑ b : Fin n → Fin L,
    (∏ i, pairU β M u t (σ i) (σ (finRotate n i)) ((Function.update a j x) i) (b i)) *
      early_src β M m n u σ b with hg
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
      fun i b' => early_U_col hD ht _ _ (fun a' => hrowU i a') b'
    set X : ℝ := ((polyDiags n).card : ℝ) * (A ^ 2 * ((1 - u) ^ (2 * n - 2))⁻¹) with hX
    have hX0 : 0 ≤ X := by positivity
    have hG : ∀ b : Fin n → Fin L, ∑ y, Real.exp (θ * wordDiam (Function.update b j y)) *
        ‖early_src β M m n u σ (Function.update b j y)‖ ≤ X / β ^ 2 := fun b => by
      rw [le_div_iff₀ (by positivity), mul_comm]
      exact early_src_row hθ hβ hIH hu0 huT σ b j
    have hP := early_prop_row θ hθ (fun i => pairU β M u t (σ i) (σ (finRotate n i)))
      (div_nonneg hX0 (by positivity)) hrowU hcolU (early_src β M m n u σ) j hG a
    calc β ^ 2 * ∑ x, w x * ‖g x u‖
        ≤ β ^ 2 * ((Bp * ((1 - u) / (1 - t))) ^ n * (X / β ^ 2)) :=
          mul_le_mul_of_nonneg_left hP (by positivity)
      _ = (Bp * ((1 - u) / (1 - t))) ^ n * X := by field_simp
      _ = Cst * ((1 - u) ^ (n - 2))⁻¹ := early_alg (by omega) hu1 ht1
  have hcontx : ∀ x, ContinuousOn (fun u => ‖g x u‖) (Set.Icc 0 t) :=
    fun x => (early_g_cont hD ht0 ht1 (Function.update a j x) σ).norm
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
    have := early_int hn3 ht0 ht1
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
private lemma early_step {θ β : ℝ} (hθ : 0 ≤ θ) {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {T Bp I A : ℝ} {n : ℕ} (hn : 3 ≤ n) (hT1 : T < 1)
    (hBp : 1 ≤ Bp) (hI : 1 ≤ I) (hA : 1 ≤ A)
    (hU : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T → ∀ (s s' : Bool) (a : Fin L),
      ∑ b, Real.exp (2 * θ * cycDist a b) * ‖pairU β M u t s s' a b‖ ≤ Bp * ((1 - u) / (1 - t)))
    (hI_sup : ∀ (a : Fin n → Fin L) (σ : Fin n → Bool),
      Real.exp (θ * wordDiam a) * ‖primF β M m 0 a σ‖ ≤ I ^ n)
    (hI_row : ∀ (j : Fin n) (a : Fin n → Fin L) (σ : Fin n → Bool),
      β * ∑ c : Fin L, Real.exp (θ * wordDiam (Function.update a j c)) *
        ‖primF β M m 0 (Function.update a j c) σ‖ ≤ I ^ n)
    (hIH : ∀ n', 2 ≤ n' → n' < n → early_Bd θ β M m T n' A) :
    early_Bd θ β M m T n (Bp ^ n * (I ^ n + (n : ℝ) ^ 2 * A ^ 2)) := by
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
    fun i σ b' => early_U_col hD ht _ _ (fun a' => hrow0 i σ a') b'
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
            early_src β M m n u σ b := primF_duhamel hD 0 t le_rfl ht0 ht1 hn a σ
    have hP := early_prop_sup θ hθ (fun i => pairU β M 0 t (σ i) (σ (finRotate n i))) hI0
      (fun i a' => hrow0 i σ a') (fun b => primF β M m 0 b σ) (fun b => hI_sup b σ) a
    have hsrc : β * (Real.exp (θ * wordDiam a) * ‖(∫ u in (0 : ℝ)..t, ∑ b : Fin n → Fin L,
          (∏ i, pairU β M u t (σ i) (σ (finRotate n i)) (a i) (b i)) *
            early_src β M m n u σ b)‖) ≤
        Bp ^ n * (n : ℝ) ^ 2 * A ^ 2 * ((1 - t) ^ (2 * n - 3))⁻¹ := by
      rcases hn.eq_or_lt with h3 | h4
      · subst h3
        have hpd : polyDiags 3 = ∅ := by decide
        have hz : ∀ (u : ℝ) (b : Fin 3 → Fin L), early_src β M m 3 u σ b = 0 := by
          intro u b
          simp [early_src, hpd]
        simp only [hz, mul_zero, Finset.sum_const_zero, intervalIntegral.integral_zero, norm_zero]
        positivity
      · have := early_int_sup hθ hD (by omega : 4 ≤ n) hT1 hBp0 hU hIH ht0 htT a σ
        refine this.trans ?_
        have : Bp ^ n * ((polyDiags n).card : ℝ) * A ^ 2 ≤ Bp ^ n * (n : ℝ) ^ 2 * A ^ 2 := by
          gcongr
        exact mul_le_mul_of_nonneg_right this (by positivity)
    rw [hdu]
    calc Real.exp (θ * wordDiam a) * ‖∑ b : Fin n → Fin L,
          (∏ i, pairU β M 0 t (σ i) (σ (finRotate n i)) (a i) (b i)) * primF β M m 0 b σ +
        (β : ℂ) * ∫ u in (0 : ℝ)..t, ∑ b : Fin n → Fin L,
          (∏ i, pairU β M u t (σ i) (σ (finRotate n i)) (a i) (b i)) *
            early_src β M m n u σ b‖
        ≤ Real.exp (θ * wordDiam a) * (‖∑ b : Fin n → Fin L,
          (∏ i, pairU β M 0 t (σ i) (σ (finRotate n i)) (a i) (b i)) * primF β M m 0 b σ‖ +
        ‖(β : ℂ) * ∫ u in (0 : ℝ)..t, ∑ b : Fin n → Fin L,
          (∏ i, pairU β M u t (σ i) (σ (finRotate n i)) (a i) (b i)) *
            early_src β M m n u σ b‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.exp_pos _).le
      _ = Real.exp (θ * wordDiam a) * ‖∑ b : Fin n → Fin L,
          (∏ i, pairU β M 0 t (σ i) (σ (finRotate n i)) (a i) (b i)) * primF β M m 0 b σ‖ +
          β * (Real.exp (θ * wordDiam a) * ‖(∫ u in (0 : ℝ)..t, ∑ b : Fin n → Fin L,
          (∏ i, pairU β M u t (σ i) (σ (finRotate n i)) (a i) (b i)) *
            early_src β M m n u σ b)‖) := by
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
            early_src β M m n u σ b := fun x =>
      primF_duhamel hD 0 t le_rfl ht0 ht1 hn (Function.update a j x) σ
    have hG0 : ∀ b : Fin n → Fin L, ∑ y, Real.exp (θ * wordDiam (Function.update b j y)) *
        ‖primF β M m 0 (Function.update b j y) σ‖ ≤ I ^ n / β := fun b => by
      rw [le_div_iff₀ hβ, mul_comm]
      exact hI_row j b σ
    have hP := early_prop_row θ hθ (fun i => pairU β M 0 t (σ i) (σ (finRotate n i)))
      (div_nonneg hI0 hβ.le) (fun i a' => hrow0 i σ a') (fun i b' => hcol0 i σ b')
      (fun b => primF β M m 0 b σ) j hG0 a
    have hsrc : β * ∑ x : Fin L, Real.exp (θ * wordDiam (Function.update a j x)) *
        ‖(β : ℂ) * ∫ u in (0 : ℝ)..t, ∑ b : Fin n → Fin L,
          (∏ i, pairU β M u t (σ i) (σ (finRotate n i)) ((Function.update a j x) i) (b i)) *
            early_src β M m n u σ b‖ ≤
        Bp ^ n * (n : ℝ) ^ 2 * A ^ 2 * ((1 - t) ^ (2 * n - 3))⁻¹ := by
      rcases hn.eq_or_lt with h3 | h4
      · subst h3
        have hpd : polyDiags 3 = ∅ := by decide
        have hz : ∀ (u : ℝ) (b : Fin 3 → Fin L), early_src β M m 3 u σ b = 0 := by
          intro u b
          simp [early_src, hpd]
        simp only [hz, mul_zero, Finset.sum_const_zero, intervalIntegral.integral_zero, norm_zero]
        positivity
      · have := early_int_row hθ hD (by omega : 4 ≤ n) hT1 hBp0 hU hIH ht0 htT j a σ
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
              early_src β M m n u σ b‖) := by
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
              early_src β M m n u σ b‖ := by
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

/-- The bound `early_Bd` weakens with the constant. -/
private lemma early_Bd_mono {θ β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} {T : ℝ}
    (hT1 : T < 1) {n : ℕ} {A A' : ℝ} (h : early_Bd θ β M m T n A) (hAA : A ≤ A') :
    early_Bd θ β M m T n A' := by
  intro t ht0 htT
  obtain ⟨h1, h2⟩ := h t ht0 htT
  have h1t : 0 < 1 - t := by linarith
  have hp : 0 ≤ ((1 - t) ^ (2 * n - 3))⁻¹ := by positivity
  exact ⟨fun a σ => (h1 a σ).trans (mul_le_mul_of_nonneg_right hAA hp),
    fun j a σ => (h2 j a σ).trans (mul_le_mul_of_nonneg_right hAA hp)⟩

/-- The induction on the length: with the propagator rows (constant `Bp`), the bound of the
two-loops (constant `A₂`) and the initial values (constant `I`), one constant `A` bounds the
weighted sup and row of every `F_n`, `2 ≤ n ≤ K`. The constant depends on `(Bp, A₂, I, K)` only. -/
private lemma early_induct (Bp A₂ I : ℝ) (hBp : 1 ≤ Bp) (hA₂ : 1 ≤ A₂) (hI : 1 ≤ I) (K : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (L : ℕ) (β θ T : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ),
      PrimData β M m → 0 ≤ θ → T < 1 →
      (∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T → ∀ (s s' : Bool) (a : Fin L),
        ∑ b, Real.exp (2 * θ * cycDist a b) * ‖pairU β M u t s s' a b‖ ≤
          Bp * ((1 - u) / (1 - t))) →
      early_Bd θ β M m T 2 A₂ →
      (∀ n, 3 ≤ n → (∀ (a : Fin n → Fin L) (σ : Fin n → Bool),
          Real.exp (θ * wordDiam a) * ‖primF β M m 0 a σ‖ ≤ I ^ n) ∧
        (∀ (j : Fin n) (a : Fin n → Fin L) (σ : Fin n → Bool),
          β * ∑ c : Fin L, Real.exp (θ * wordDiam (Function.update a j c)) *
            ‖primF β M m 0 (Function.update a j c) σ‖ ≤ I ^ n)) →
      ∀ n, 2 ≤ n → n ≤ K → early_Bd θ β M m T n A := by
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
    · exact early_Bd_mono hT1 (hK L β θ T M m hD hθ hT1 hU h2 hinit n hn (by omega)) hAA
    · have hn' : n = K + 1 := by omega
      subst hn'
      rcases Nat.lt_or_ge (K + 1) 3 with h3 | h3
      · have hK1 : K = 1 := by omega
        subst hK1
        exact early_Bd_mono hT1 h2 hA₂A
      · obtain ⟨hs, hr⟩ := hinit (K + 1) h3
        have := early_step hθ hD h3 hT1 hBp hI hA
          (hU) hs hr (fun n' hn'1 hn'2 => hK L β θ T M m hD hθ hT1 hU h2 hinit n' hn'1
            (by omega))
        exact early_Bd_mono hT1 this (le_max_right _ _)

/-- The diameter of a word is at most the length of the closed path through its labels. -/
private lemma early_diam_cycle {n : ℕ} (a : Fin n → Fin L) :
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
      simp [early_cd_self]
    | succ d ih =>
      intro hd
      have h1 := ih (by omega)
      have h2 := early_cd_tri (f p) (f (p + d)) (f (p + (d + 1)))
      have h3 : cycDist (f (p + d)) (f (p + (d + 1))) = F (p + d) := by
        have hlt : p + d < n := by omega
        have hlt' : p + d + 1 < n := by omega
        simp only [hf, hF, hlt, hd, dite_true]
        rw [hrot (p + d) hlt']
        rfl
      rw [Finset.sum_range_succ]
      omega
  refine early_diam_le a fun p q => ?_
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
  · rw [early_cd_comm]
    exact key q p h

/-- The weighted modulus of an entry of `M`. -/
private def early_g (θ : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (x y : Fin L) : ℝ :=
  Real.exp (θ * cycDist x y) * ‖M x y‖

private lemma early_g_nonneg (θ : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (x y : Fin L) :
    0 ≤ early_g θ M x y := by
  unfold early_g; positivity

/-- The signed matrices have the moduli of `M` (`M` is symmetric). -/
private lemma early_sgn_norm {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) (s : Bool) (x y : Fin L) : ‖sgnMat M s x y‖ = ‖M x y‖ := by
  have hsym : M y x = M x y := congrFun (congrFun hD.symm x) y
  cases s
  · simp [sgnMat, Matrix.conjTranspose_apply, hsym]
  · simp [sgnMat]

/-- Pointwise: the weighted modulus of the initial value is at most the product of the weighted
moduli of the entries of `M` around the cycle. -/
private lemma early_init_pw {θ β : ℝ} (hθ : 0 ≤ θ) {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {n : ℕ} (a : Fin n → Fin L) (σ : Fin n → Bool) :
    Real.exp (θ * wordDiam a) * ‖∏ l, sgnMat M (σ l) (a ((finRotate n).symm l)) (a l)‖ ≤
      ∏ l, early_g θ M (a ((finRotate n).symm l)) (a l) := by
  have h1 : Real.exp (θ * wordDiam a) ≤
      ∏ l, Real.exp (θ * cycDist (a ((finRotate n).symm l)) (a l)) := by
    rw [← Real.exp_sum, ← Finset.mul_sum]
    apply Real.exp_le_exp.mpr
    have h2 := early_diam_cycle a
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
    exact Finset.prod_congr rfl fun l _ => early_sgn_norm hD _ _ _
  rw [h5]
  calc Real.exp (θ * wordDiam a) * ∏ l, ‖M (a ((finRotate n).symm l)) (a l)‖
      ≤ (∏ l, Real.exp (θ * cycDist (a ((finRotate n).symm l)) (a l))) *
        ∏ l, ‖M (a ((finRotate n).symm l)) (a l)‖ :=
        mul_le_mul_of_nonneg_right h1 (Finset.prod_nonneg fun l _ => norm_nonneg _)
    _ = _ := (Finset.prod_mul_distrib).symm

/-- Initial values, sup bound. -/
private lemma early_init_sup {θ β : ℝ} (hθ : 0 ≤ θ) {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {I : ℝ}
    (hMe : ∀ x y, early_g θ M x y ≤ I) {n : ℕ} (a : Fin n → Fin L)
    (σ : Fin n → Bool) :
    Real.exp (θ * wordDiam a) * ‖∏ l, sgnMat M (σ l) (a ((finRotate n).symm l)) (a l)‖ ≤
      I ^ n := by
  refine (early_init_pw hθ hD a σ).trans ?_
  calc ∏ l, early_g θ M (a ((finRotate n).symm l)) (a l) ≤ ∏ _l : Fin n, I :=
        Finset.prod_le_prod₀ (fun l _ => early_g_nonneg _ _ _ _) (fun l _ => hMe _ _)
    _ = I ^ n := by simp

/-- Initial values, row bound at a label `j`. -/
private lemma early_init_row {θ β : ℝ} (hθ : 0 ≤ θ) (hβ : 0 < β) {M : Matrix (Fin L) (Fin L) ℂ}
    {m : ℂ} (hD : PrimData β M m) {I : ℝ} (hI : 0 ≤ I)
    (hMe : ∀ x y, early_g θ M x y ≤ I)
    (hMr : ∀ x y, β * ∑ z, early_g θ M x z * early_g θ M z y ≤ I ^ 2) {n : ℕ} (hn : 2 ≤ n)
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
      I ^ m' * (early_g θ M (a ((finRotate (m' + 2)).symm j)) c * early_g θ M c (a r)) := by
    intro c
    refine (early_init_pw hθ hD _ σ).trans ?_
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
      ← Finset.mul_prod_erase (Finset.univ.erase j) _ hrmem]
    have e1 : early_g θ M ((Function.update a j c) ((finRotate (m' + 2)).symm j))
        ((Function.update a j c) j) = early_g θ M (a ((finRotate (m' + 2)).symm j)) c := by
      rw [Function.update_of_ne hpj, Function.update_self]
    have e2 : early_g θ M ((Function.update a j c) ((finRotate (m' + 2)).symm r))
        ((Function.update a j c) r) = early_g θ M c (a r) := by
      rw [hpr, Function.update_self, Function.update_of_ne hrj]
    have e3 : ∏ l ∈ (Finset.univ.erase j).erase r,
        early_g θ M ((Function.update a j c) ((finRotate (m' + 2)).symm l))
          ((Function.update a j c) l) =
        ∏ l ∈ (Finset.univ.erase j).erase r,
          early_g θ M (a ((finRotate (m' + 2)).symm l)) (a l) := by
      refine Finset.prod_congr rfl fun l hl => ?_
      have hlr : l ≠ r := Finset.ne_of_mem_erase hl
      have hlj : l ≠ j := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hl)
      rw [Function.update_of_ne (hpl l hlr), Function.update_of_ne hlj]
    have e4 : ∏ l ∈ (Finset.univ.erase j).erase r,
        early_g θ M (a ((finRotate (m' + 2)).symm l)) (a l) ≤ I ^ m' := by
      calc _ ≤ ∏ _l ∈ (Finset.univ.erase j).erase r, I :=
            Finset.prod_le_prod₀ (fun l _ => early_g_nonneg _ _ _ _) (fun l _ => hMe _ _)
        _ = I ^ m' := by rw [Finset.prod_const, hcard]
    rw [e1, e2, e3]
    calc early_g θ M (a ((finRotate (m' + 2)).symm j)) c * (early_g θ M c (a r) *
          ∏ l ∈ (Finset.univ.erase j).erase r,
            early_g θ M (a ((finRotate (m' + 2)).symm l)) (a l))
        ≤ early_g θ M (a ((finRotate (m' + 2)).symm j)) c * (early_g θ M c (a r) * I ^ m') := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e4
            (early_g_nonneg _ _ _ _)) (early_g_nonneg _ _ _ _)
      _ = _ := by ring
  calc β * ∑ c : Fin L, Real.exp (θ * wordDiam (Function.update a j c)) *
      ‖∏ l, sgnMat M (σ l) ((Function.update a j c) ((finRotate (m' + 2)).symm l))
        ((Function.update a j c) l)‖
      ≤ β * ∑ c : Fin L, I ^ m' * (early_g θ M (a ((finRotate (m' + 2)).symm j)) c *
          early_g θ M c (a r)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => hpc c) hβ.le
    _ = I ^ m' * (β * ∑ c, early_g θ M (a ((finRotate (m' + 2)).symm j)) c *
          early_g θ M c (a r)) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ I ^ m' * I ^ 2 :=
        mul_le_mul_of_nonneg_left (hMr _ _) (by positivity)
    _ = I ^ (m' + 2) := by ring

/-- All lengths `n ≥ 3`: the initial bounds from the entry bounds of `M`. -/
private lemma early_init_all {θ β : ℝ} (hθ : 0 ≤ θ) (hβ : 0 < β) {M : Matrix (Fin L) (Fin L) ℂ}
    {m : ℂ} (hD : PrimData β M m)
    (hprod : ∀ (k : ℕ), 1 ≤ k → ∀ (a : Fin k → Fin L) (σ : Fin k → Bool),
      primF β M m 0 a σ = ∏ j, sgnMat M (σ j) (a ((finRotate k).symm j)) (a j))
    {I : ℝ} (hI : 1 ≤ I) (hMe : ∀ x y, early_g θ M x y ≤ I)
    (hMr : ∀ x y, β * ∑ z, early_g θ M x z * early_g θ M z y ≤ I ^ 2) :
    ∀ n, 3 ≤ n → (∀ (a : Fin n → Fin L) (σ : Fin n → Bool),
          Real.exp (θ * wordDiam a) * ‖primF β M m 0 a σ‖ ≤ I ^ n) ∧
        (∀ (j : Fin n) (a : Fin n → Fin L) (σ : Fin n → Bool),
          β * ∑ c : Fin L, Real.exp (θ * wordDiam (Function.update a j c)) *
            ‖primF β M m 0 (Function.update a j c) σ‖ ≤ I ^ n) := by
  intro n hn
  refine ⟨fun a σ => ?_, fun j a σ => ?_⟩
  · rw [hprod n (by omega) a σ]
    exact early_init_sup hθ hD hMe a σ
  · simp only [hprod n (by omega) _ σ]
    exact early_init_row hθ hβ hD (by linarith) hMe hMr (by omega) j a σ

/-- The weighted base case at `θ = 0`: the two-loops are bounded by `C_M² (1 - t)⁻¹`, in sup and
in row, from the entry bound of `M` alone. -/
private lemma early_base_coarse {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {T CM : ℝ} (hT1 : T < 1) (hCM : ∀ a b, ‖M a b‖ ≤ CM) :
    early_Bd 0 β M m T 2 (max (CM ^ 2) 1) := by
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
  refine ⟨fun a σ => ?_, fun j a σ => ?_⟩
  · simp only [zero_mul, Real.exp_zero, one_mul, hkey, hpow]
    have := early_K_entry hD ht0 ht1 hCM (σ 0) (σ 1) (a 0) (a 1)
    calc β⁻¹ * ‖pairK β M t (σ 0) (σ 1) (a 0) (a 1)‖ ≤ β⁻¹ * (β * CM ^ 2 * (1 - t)⁻¹) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = CM ^ 2 * (1 - t)⁻¹ := by field_simp
      _ ≤ max (CM ^ 2) 1 * (1 - t)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · simp only [zero_mul, Real.exp_zero, one_mul, hkey, hpow]
    have hmax : (1 - t)⁻¹ ≤ max (CM ^ 2) 1 * (1 - t)⁻¹ := by
      have : (0 : ℝ) ≤ (1 - t)⁻¹ := by positivity
      nlinarith [le_max_right (CM ^ 2) 1]
    have hsum : ∀ (F : Fin L → ℝ), β * ∑ c, β⁻¹ * F c = ∑ c, F c := by
      intro F
      rw [← Finset.mul_sum, ← mul_assoc, mul_inv_cancel₀ hβ.ne', one_mul]
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, Function.update_self,
        Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
      rw [hsum (fun c => ‖pairK β M t (σ 0) (σ 1) c (a 1)‖)]
      refine le_trans ?_ hmax
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun c _ => ?_))
        (early_K_row hD ht0 ht1 (σ 0) (σ 1) (a 1))
      have := congrFun (congrFun (early_K_symm hD (abs_lt.mpr ⟨by linarith, ht1⟩) (σ 0) (σ 1)) c)
        (a 1)
      rw [Matrix.transpose_apply] at this
      rw [this]
    · simp only [Fin.mk_one, Fin.isValue, Function.update_self,
        Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
      rw [hsum (fun c => ‖pairK β M t (σ 0) (σ 1) (a 0) c‖)]
      exact le_trans (early_K_row hD ht0 ht1 (σ 0) (σ 1) (a 0)) hmax

/-- Cauchy-Schwarz for the entries of `M`: `β Σ_z |M_{xz}||M_{zy}| ≤ 1`. -/
private lemma early_Mr_coarse {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {I : ℝ} (hI : 1 ≤ I) (x y : Fin L) :
    β * ∑ z, early_g 0 M x z * early_g 0 M z y ≤ I ^ 2 := by
  have hβ := hD.pos
  have hg : ∀ u v, early_g 0 M u v = ‖M u v‖ := fun u v => by simp [early_g]
  simp only [hg]
  have h1 : ∑ z, β * ‖M x z‖ ^ 2 = 1 := by
    have := hD.row_sum x
    simpa [pairP] using this
  have h2 : ∑ z, β * ‖M z y‖ ^ 2 = 1 := by
    have := hD.row_sum y
    simp only [pairP, Matrix.of_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [show M z y = M y z from congrFun (congrFun hD.symm y) z]
  calc β * ∑ z, ‖M x z‖ * ‖M z y‖
      ≤ (∑ z, β * ‖M x z‖ ^ 2 + ∑ z, β * ‖M z y‖ ^ 2) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_le_sum fun z _ => ?_
        nlinarith [sq_nonneg (‖M x z‖ - ‖M z y‖), hβ]
    _ = 1 := by rw [h1, h2]; norm_num
    _ ≤ I ^ 2 := by nlinarith

/-- One pair of the cut sum, at `θ = 0`: `β Σ_c |F_L||F_R| ≤ A² (1 - t)^{-(2k-2)}`. -/
private lemma early_pair_bound {β : ℝ} (hβ : 0 < β) {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    {A t : ℝ} {k : ℕ} (ht0 : 0 ≤ t)
    (hbd : ∀ n', 2 ≤ n' → n' ≤ k → early_Bd 0 β M m t n' A) (a : Fin k → Fin L)
    (σ : Fin k → Bool) {i j : Fin k} (hij : i < j) :
    β * ∑ c : Fin L, ‖primF β M m t (cutLLab a i j c) (cutLSgn σ i j)‖ *
      ‖primF β M m t (cutRLab a i j c) (cutRSgn σ i j)‖ ≤
      A ^ 2 * ((1 - t) ^ (2 * k - 2))⁻¹ := by
  have hij' : i.val < j.val := hij
  have hjk := j.2
  have hL1 : 2 ≤ k + i.val - j.val + 1 := by omega
  have hL2 : k + i.val - j.val + 1 ≤ k := by omega
  have hR1 : 2 ≤ j.val - i.val + 1 := by omega
  have hR2 : j.val - i.val + 1 ≤ k := by omega
  obtain ⟨hLs, -⟩ := hbd _ hL1 hL2 t ht0 le_rfl
  obtain ⟨-, hRr⟩ := hbd _ hR1 hR2 t ht0 le_rfl
  have hexp : 2 * (k + i.val - j.val + 1) - 3 + (2 * (j.val - i.val + 1) - 3) = 2 * k - 2 := by
    omega
  set c₀ : Fin L := a i with hc₀
  have hrowR : β * ∑ c : Fin L, ‖primF β M m t (cutRLab a i j c) (cutRSgn σ i j)‖ ≤
      A * ((1 - t) ^ (2 * (j.val - i.val + 1) - 3))⁻¹ := by
    have := hRr (Fin.last (j.val - i.val)) (cutRLab a i j c₀) (cutRSgn σ i j)
    simpa only [← early_cutR_c a i j _ c₀, zero_mul, Real.exp_zero, one_mul] using this
  have hpow : ((1 - t) ^ (2 * (k + i.val - j.val + 1) - 3))⁻¹ *
      ((1 - t) ^ (2 * (j.val - i.val + 1) - 3))⁻¹ = ((1 - t) ^ (2 * k - 2))⁻¹ := by
    rw [← mul_inv, ← pow_add, hexp]
  have hLs' : ∀ c : Fin L, ‖primF β M m t (cutLLab a i j c) (cutLSgn σ i j)‖ ≤
      A * ((1 - t) ^ (2 * (k + i.val - j.val + 1) - 3))⁻¹ := fun c => by
    simpa only [zero_mul, Real.exp_zero, one_mul] using hLs (cutLLab a i j c) (cutLSgn σ i j)
  calc β * ∑ c : Fin L, ‖primF β M m t (cutLLab a i j c) (cutLSgn σ i j)‖ *
      ‖primF β M m t (cutRLab a i j c) (cutRSgn σ i j)‖
      ≤ β * ∑ c : Fin L, (A * ((1 - t) ^ (2 * (k + i.val - j.val + 1) - 3))⁻¹) *
          ‖primF β M m t (cutRLab a i j c) (cutRSgn σ i j)‖ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_right (hLs' c) (norm_nonneg _)) hβ.le
    _ = (A * ((1 - t) ^ (2 * (k + i.val - j.val + 1) - 3))⁻¹) *
        (β * ∑ c : Fin L, ‖primF β M m t (cutRLab a i j c) (cutRSgn σ i j)‖) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ (A * ((1 - t) ^ (2 * (k + i.val - j.val + 1) - 3))⁻¹) *
        (A * ((1 - t) ^ (2 * (j.val - i.val + 1) - 3))⁻¹) := by
        refine mul_le_mul_of_nonneg_left hrowR ?_
        refine le_trans ?_ (hLs' c₀)
        exact norm_nonneg _
    _ = A ^ 2 * ((1 - t) ^ (2 * k - 2))⁻¹ := by
        rw [← hpow]; ring

/-- The time derivative of `F_k` at `θ = 0`, from the bounds of the loops of lengths `2, …, k`:
`|∂_t F_k| ≤ k² A² (1 - t)^{-(2k-2)}`. -/
private lemma early_deriv {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} (hD : PrimData β M m)
    {A t : ℝ} {k : ℕ} (hk : 2 ≤ k) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hbd : ∀ n', 2 ≤ n' → n' ≤ k → early_Bd 0 β M m t n' A) (a : Fin k → Fin L)
    (σ : Fin k → Bool) :
    ‖deriv (fun s => primF β M m s a σ) t‖ ≤
      (k : ℝ) ^ 2 * (A ^ 2 * ((1 - t) ^ (2 * k - 2))⁻¹) := by
  have hβ := hD.pos
  have hder := primF_hasDerivAt hD t ⟨by linarith, ht1⟩ hk a σ
  rw [hder.deriv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ]
  unfold cutSumFam
  have hX : 0 ≤ A ^ 2 * ((1 - t) ^ (2 * k - 2))⁻¹ := by
    have : 0 < 1 - t := by linarith
    positivity
  calc β * ‖∑ i : Fin k, ∑ j : Fin k, if i < j then ∑ c : Fin L,
        primF β M m t (cutLLab a i j c) (cutLSgn σ i j) *
          primF β M m t (cutRLab a i j c) (cutRSgn σ i j) else 0‖
      ≤ β * ∑ i : Fin k, ∑ j : Fin k, if i < j then ∑ c : Fin L,
        ‖primF β M m t (cutLLab a i j c) (cutLSgn σ i j)‖ *
          ‖primF β M m t (cutRLab a i j c) (cutRSgn σ i j)‖ else 0 := by
        refine mul_le_mul_of_nonneg_left ?_ hβ.le
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        split_ifs
        · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => by rw [norm_mul])
        · simp
    _ = ∑ i : Fin k, ∑ j : Fin k, if i < j then β * ∑ c : Fin L,
        ‖primF β M m t (cutLLab a i j c) (cutLSgn σ i j)‖ *
          ‖primF β M m t (cutRLab a i j c) (cutRSgn σ i j)‖ else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> simp
    _ ≤ ∑ _i : Fin k, ∑ _j : Fin k, A ^ 2 * ((1 - t) ^ (2 * k - 2))⁻¹ := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        split_ifs with hij
        · exact early_pair_bound hβ ht0 hbd a σ hij
        · exact hX
    _ = (k : ℝ) ^ 2 * (A ^ 2 * ((1 - t) ^ (2 * k - 2))⁻¹) := by
        simp [Finset.sum_const, sq]
        ring

end Induct

/-! ## The scale `ℓ_t` -/

section Scale

private lemma early_gamma_pos (g : ℝ) : 0 < gammaG g := by
  have : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  unfold gammaG; positivity

private lemma early_ell_ge_one (g : ℝ) (hg : 0 ≤ g) (L : ℕ) (hL : 1 ≤ L) (t : ℝ) :
    1 ≤ ellProp g L t := by
  unfold ellProp
  refine le_min (by exact_mod_cast hL) ?_
  have : 0 ≤ g / Real.sqrt (gammaG g * (1 - t)) := div_nonneg hg (Real.sqrt_nonneg _)
  linarith

private lemma early_ell_mono (g : ℝ) (hg : 0 ≤ g) (L : ℕ) {s u : ℝ} (hsu : s ≤ u) (hu : u < 1) :
    ellProp g L s ≤ ellProp g L u := by
  have hγ := early_gamma_pos g
  have hu1 : 0 < 1 - u := by linarith
  unfold ellProp
  refine min_le_min le_rfl ?_
  have h1 : Real.sqrt (gammaG g * (1 - u)) ≤ Real.sqrt (gammaG g * (1 - s)) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have h2 : 0 < Real.sqrt (gammaG g * (1 - u)) := Real.sqrt_pos.mpr (mul_pos hγ hu1)
  have := div_le_div_of_nonneg_left hg h2 h1
  linarith

end Scale

/-! ## Weighted rows of the pair kernels and propagators at bounded coupling -/

section WeightedRows

variable {L : ℕ}

/-- The cyclic distance enters the weights `e^{λ d}` through the triangle inequality. -/
private lemma early_exp_tri {lm : ℝ} (hlm : 0 ≤ lm) (a b c : Fin L) :
    Real.exp (lm * cycDist a c) ≤ Real.exp (lm * cycDist a b) * Real.exp (lm * cycDist b c) := by
  rw [← Real.exp_add, ← mul_add]
  apply Real.exp_le_exp.mpr
  have : (cycDist a c : ℝ) ≤ cycDist a b + cycDist b c := by exact_mod_cast early_cd_tri a b c
  exact mul_le_mul_of_nonneg_left this hlm

/-- Weighted row of the same-sign pair kernel `Q (1 - tQ)⁻¹`. -/
private lemma early_QV_wrow {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} (hD : PrimData β M m)
    (hβ1 : β ≤ 1) {t c lm CK : ℝ} (hlm : 0 ≤ lm) (hlmc : lm ≤ c) (hCK : 0 ≤ CK)
    (hMrow : ∀ a, ∑ b, Real.exp (c * cycDist a b) * ‖M a b‖ ≤ CK)
    (hVrow : ∀ a, ∑ b, Real.exp (c * cycDist a b) *
      ‖(1 - (t : ℂ) • pairQ β M)⁻¹ a b‖ ≤ CK) (a : Fin L) :
    ∑ b, Real.exp (lm * cycDist a b) *
      ‖(pairQ β M * (1 - (t : ℂ) • pairQ β M)⁻¹) a b‖ ≤ CK ^ 3 := by
  have hβ := hD.pos
  set V := (1 - (t : ℂ) • pairQ β M)⁻¹ with hV
  have hexp : ∀ x y : Fin L, Real.exp (lm * cycDist x y) ≤ Real.exp (c * cycDist x y) := fun x y =>
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hlmc (Nat.cast_nonneg _))
  have hMsingle : ∀ x y : Fin L, ‖M x y‖ ≤ CK := fun x y => by
    refine le_trans ?_ ((Finset.single_le_sum (f := fun b => Real.exp (c * cycDist x b) * ‖M x b‖)
      (fun b _ => by positivity) (Finset.mem_univ y)).trans (hMrow x))
    exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by
      have : (0 : ℝ) ≤ c * cycDist x y := by
        refine mul_nonneg ?_ (Nat.cast_nonneg _)
        exact hlm.trans hlmc
      exact this))
  have hQ : ∀ x y : Fin L, ‖pairQ β M x y‖ = β * ‖M x y‖ ^ 2 := fun x y => by
    simp [pairQ, norm_pow, Complex.norm_real, abs_of_pos hβ]
  have hQrow : ∑ y, Real.exp (lm * cycDist a y) * ‖pairQ β M a y‖ ≤ CK * CK := by
    calc ∑ y, Real.exp (lm * cycDist a y) * ‖pairQ β M a y‖
        ≤ ∑ y, CK * (Real.exp (c * cycDist a y) * ‖M a y‖) := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [hQ]
          have h1 : β * ‖M a y‖ ^ 2 ≤ ‖M a y‖ * CK := by
            have := hMsingle a y
            nlinarith [norm_nonneg (M a y)]
          calc Real.exp (lm * cycDist a y) * (β * ‖M a y‖ ^ 2)
              ≤ Real.exp (c * cycDist a y) * (‖M a y‖ * CK) :=
                mul_le_mul (hexp a y) h1 (by positivity) (by positivity)
            _ = CK * (Real.exp (c * cycDist a y) * ‖M a y‖) := by ring
      _ = CK * ∑ y, Real.exp (c * cycDist a y) * ‖M a y‖ := by rw [Finset.mul_sum]
      _ ≤ CK * CK := mul_le_mul_of_nonneg_left (hMrow a) hCK
  calc ∑ b, Real.exp (lm * cycDist a b) * ‖(pairQ β M * V) a b‖
      ≤ ∑ b, ∑ y, (Real.exp (lm * cycDist a y) * ‖pairQ β M a y‖) *
          (Real.exp (c * cycDist y b) * ‖V y b‖) := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [Matrix.mul_apply]
        calc Real.exp (lm * cycDist a b) * ‖∑ y, pairQ β M a y * V y b‖
            ≤ Real.exp (lm * cycDist a b) * ∑ y, ‖pairQ β M a y‖ * ‖V y b‖ :=
              mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
                (Finset.sum_le_sum fun y _ => by rw [norm_mul])) (Real.exp_pos _).le
          _ = ∑ y, Real.exp (lm * cycDist a b) * (‖pairQ β M a y‖ * ‖V y b‖) := by
              rw [Finset.mul_sum]
          _ ≤ _ := by
              refine Finset.sum_le_sum fun y _ => ?_
              have h1 := early_exp_tri hlm a y b
              have h2 : Real.exp (lm * cycDist y b) ≤ Real.exp (c * cycDist y b) := hexp y b
              calc Real.exp (lm * cycDist a b) * (‖pairQ β M a y‖ * ‖V y b‖)
                  ≤ (Real.exp (lm * cycDist a y) * Real.exp (c * cycDist y b)) *
                      (‖pairQ β M a y‖ * ‖V y b‖) :=
                    mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left h2
                      (Real.exp_pos _).le)) (by positivity)
                _ = _ := by ring
    _ = ∑ y, (Real.exp (lm * cycDist a y) * ‖pairQ β M a y‖) *
          ∑ b, Real.exp (c * cycDist y b) * ‖V y b‖ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ y, (Real.exp (lm * cycDist a y) * ‖pairQ β M a y‖) * CK :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hVrow y) (by positivity)
    _ = (∑ y, Real.exp (lm * cycDist a y) * ‖pairQ β M a y‖) * CK := by rw [Finset.sum_mul]
    _ ≤ (CK * CK) * CK := mul_le_mul_of_nonneg_right hQrow hCK
    _ = CK ^ 3 := by ring

/-- Weighted rows of the pair kernels, every sign pair, from the weighted bounds of the kernels,
of `M_B` and of the same-sign inverse. -/
private lemma early_K_wrow {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} (hD : PrimData β M m)
    (hβ1 : β ≤ 1) {t c ℓ lm CK : ℝ} (hℓ : 1 ≤ ℓ) (hlm : 0 ≤ lm) (hlmc : lm ≤ c / ℓ)
    (hCK : 1 ≤ CK) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hKnn : ∀ a b, 0 ≤ mixedKer (pairP β M) t a b)
    (hMrow : ∀ a, ∑ b, Real.exp (c * cycDist a b) * ‖M a b‖ ≤ CK)
    (hKrow : ∀ a, ∑ b, Real.exp (c * cycDist a b / ℓ) * mixedKer (pairP β M) t a b ≤
      CK / (1 - t))
    (hVrow : ∀ a, ∑ b, Real.exp (c * cycDist a b) *
      ‖(1 - (t : ℂ) • pairQ β M)⁻¹ a b‖ ≤ CK) (s s' : Bool) (a : Fin L) :
    ∑ b, Real.exp (lm * cycDist a b) * ‖pairK β M t s s' a b‖ ≤ (CK + CK ^ 3) / (1 - t) := by
  have h1t : 0 < 1 - t := by linarith
  have hc0 : 0 ≤ c := by
    have : lm * ℓ ≤ c := by
      have := mul_le_mul_of_nonneg_right hlmc (by linarith : 0 ≤ ℓ)
      rwa [div_mul_cancel₀ _ (by linarith : ℓ ≠ 0)] at this
    nlinarith
  have hlmc' : lm ≤ c := by
    refine hlmc.trans ?_
    exact div_le_self hc0 hℓ
  have hCK3 : CK ≤ CK ^ 3 := by nlinarith [sq_nonneg CK]
  have hbig : CK / (1 - t) ≤ (CK + CK ^ 3) / (1 - t) := by
    apply div_le_div_of_nonneg_right _ h1t.le
    nlinarith [sq_nonneg CK]
  by_cases hss : s = s'
  · subst hss
    have hQV := early_QV_wrow hD hβ1 hlm hlmc' (by linarith : 0 ≤ CK) hMrow hVrow a
    have hle : CK ^ 3 ≤ (CK + CK ^ 3) / (1 - t) := by
      rw [le_div_iff₀ h1t]
      have h3 : 0 ≤ CK ^ 3 * t := by positivity
      nlinarith
    cases s
    · simp only [pairK, ite_true, Bool.false_eq_true, ite_false]
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_)) (hQV.trans hle)
      rw [Matrix.map_apply, norm_star]
    · simp only [pairK, ite_true]
      exact hQV.trans hle
  · have hmix : ∀ b, ‖pairK β M t s s' a b‖ = mixedKer (pairP β M) t a b := by
      intro b
      have : pairK β M t s s' = (mixedKer (pairP β M) t).map ((↑) : ℝ → ℂ) := by
        simp [pairK, hss]
      rw [this, Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hKnn a b)]
    refine le_trans (Finset.sum_le_sum fun b _ => ?_) (le_trans (hKrow a) hbig)
    rw [hmix]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (hKnn a b)
    calc lm * (cycDist a b : ℝ) ≤ c / ℓ * (cycDist a b : ℝ) :=
          mul_le_mul_of_nonneg_right hlmc (Nat.cast_nonneg _)
      _ = c * (cycDist a b : ℝ) / ℓ := by ring

/-- Weighted rows of the propagators. -/
private lemma early_U_wrow {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ} (hD : PrimData β M m)
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
        rw [early_U_eq' hD ht]
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
        have h2 : ‖(if a = b then (1 : ℂ) else 0) + ((t - u : ℝ) : ℂ) * pairK β M t s s' a b‖ ≤
            (if a = b then (1 : ℝ) else 0) + (t - u) * ‖pairK β M t s s' a b‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · split_ifs <;> simp
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        by_cases hab : a = b
        · subst hab
          simp only [early_cd_self, Nat.cast_zero, mul_zero, Real.exp_zero, one_mul,
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

/-- The weighted base case: the two-loops from the weighted rows of the pair kernels. -/
private lemma early_base_wtd {θ β : ℝ} (hθ : 0 ≤ θ) {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) {T Gm CKK : ℝ} (hT1 : T < 1) (hGm : β⁻¹ ≤ Gm) (hGm1 : 1 ≤ Gm)
    (hCKK : 1 ≤ CKK)
    (hrow : ∀ t : ℝ, 0 ≤ t → t ≤ T → ∀ (s s' : Bool) (a : Fin L),
      ∑ b, Real.exp (θ * cycDist a b) * ‖pairK β M t s s' a b‖ ≤ CKK / (1 - t)) :
    early_Bd θ β M m T 2 (max 1 (Gm * CKK)) := by
  have hβ := hD.pos
  have hGm0 : 0 ≤ Gm := (inv_nonneg.mpr hβ.le).trans hGm
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
    refine early_diam_le a fun p q => ?_
    fin_cases p <;> fin_cases q <;> simp [early_cd_self, early_cd_comm]
  have hexp : ∀ (a : Fin 2 → Fin L), Real.exp (θ * wordDiam a) ≤
      Real.exp (θ * cycDist (a 0) (a 1)) := fun a => by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hdiam a) hθ
  have hA : CKK / (1 - t) ≤ max 1 (Gm * CKK) * (1 - t)⁻¹ := by
    rw [div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right (le_trans ?_ (le_max_right _ _)) (by positivity)
    nlinarith
  have hA' : Gm * CKK * (1 - t)⁻¹ ≤ max 1 (Gm * CKK) * (1 - t)⁻¹ :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hsum : ∀ (F : Fin L → ℝ), β * ∑ c, β⁻¹ * F c = ∑ c, F c := by
    intro F
    rw [← Finset.mul_sum, ← mul_assoc, mul_inv_cancel₀ hβ.ne', one_mul]
  refine ⟨fun a σ => ?_, fun j a σ => ?_⟩
  · rw [hkey, hpow]
    have h1 : Real.exp (θ * cycDist (a 0) (a 1)) * ‖pairK β M t (σ 0) (σ 1) (a 0) (a 1)‖ ≤
        CKK / (1 - t) :=
      (Finset.single_le_sum (f := fun b => Real.exp (θ * cycDist (a 0) b) *
        ‖pairK β M t (σ 0) (σ 1) (a 0) b‖) (fun b _ => by positivity)
        (Finset.mem_univ (a 1))).trans (hrow t ht0 htT (σ 0) (σ 1) (a 0))
    calc Real.exp (θ * wordDiam a) * (β⁻¹ * ‖pairK β M t (σ 0) (σ 1) (a 0) (a 1)‖)
        ≤ Real.exp (θ * cycDist (a 0) (a 1)) *
            (β⁻¹ * ‖pairK β M t (σ 0) (σ 1) (a 0) (a 1)‖) :=
          mul_le_mul_of_nonneg_right (hexp a) (by positivity)
      _ = β⁻¹ * (Real.exp (θ * cycDist (a 0) (a 1)) *
            ‖pairK β M t (σ 0) (σ 1) (a 0) (a 1)‖) := by ring
      _ ≤ Gm * (CKK / (1 - t)) :=
          mul_le_mul hGm h1 (by positivity) hGm0
      _ = Gm * CKK * (1 - t)⁻¹ := by ring
      _ ≤ _ := hA'
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
        have := congrFun (congrFun (early_K_symm hD (abs_lt.mpr ⟨by linarith, ht1⟩) (σ 0) (σ 1))
          c) (a 1)
        rw [Matrix.transpose_apply] at this
        rw [this]
      refine le_trans (Finset.sum_le_sum fun c _ => ?_) (hrow t ht0 htT (σ 0) (σ 1) (a 1))
      rw [hsymm c]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      refine (hexp _).trans ?_
      simp only [Function.update_self, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
      rw [early_cd_comm]
    · simp only [Fin.mk_one, Fin.isValue, Function.update_self,
        Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
      refine le_trans (Finset.sum_le_sum fun c _ => ?_) (hrow t ht0 htT (σ 0) (σ 1) (a 0))
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      refine (hexp _).trans ?_
      simp only [Function.update_self, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
      exact le_rfl

/-- Entry and row bounds of the weighted moduli of `M` from the weighted row of `M_B`. -/
private lemma early_Mwt {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} (hβ1 : β ≤ 1)
    {θ c CK I : ℝ} (hθc : θ ≤ c) (hCKI : CK ≤ I) (hCK0 : 0 ≤ CK)
    (hMrow : ∀ a, ∑ b, Real.exp (c * cycDist a b) * ‖M a b‖ ≤ CK) :
    (∀ x y, early_g θ M x y ≤ I) ∧
      (∀ x y, β * ∑ z, early_g θ M x z * early_g θ M z y ≤ I ^ 2) := by
  have hexp : ∀ x y : Fin L, Real.exp (θ * cycDist x y) ≤ Real.exp (c * cycDist x y) :=
    fun x y => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hθc (Nat.cast_nonneg _))
  have hsingle : ∀ x y : Fin L, early_g θ M x y ≤ CK := fun x y => by
    unfold early_g
    refine le_trans ?_ ((Finset.single_le_sum (f := fun b => Real.exp (c * cycDist x b) * ‖M x b‖)
      (fun b _ => by positivity) (Finset.mem_univ y)).trans (hMrow x))
    exact mul_le_mul_of_nonneg_right (hexp x y) (norm_nonneg _)
  have hrow : ∀ x, ∑ z, early_g θ M x z ≤ CK := fun x => by
    refine le_trans (Finset.sum_le_sum fun z _ => ?_) (hMrow x)
    unfold early_g
    exact mul_le_mul_of_nonneg_right (hexp x z) (norm_nonneg _)
  refine ⟨fun x y => (hsingle x y).trans hCKI, fun x y => ?_⟩
  have hI0 : 0 ≤ I := hCK0.trans hCKI
  calc β * ∑ z, early_g θ M x z * early_g θ M z y
      ≤ 1 * ∑ z, early_g θ M x z * early_g θ M z y :=
        mul_le_mul_of_nonneg_right hβ1 (Finset.sum_nonneg fun z _ =>
          mul_nonneg (early_g_nonneg _ _ _ _) (early_g_nonneg _ _ _ _))
    _ ≤ ∑ z, early_g θ M x z * I :=
        by rw [one_mul]; exact Finset.sum_le_sum fun z _ =>
          mul_le_mul_of_nonneg_left ((hsingle z y).trans hCKI) (early_g_nonneg _ _ _ _)
    _ = (∑ z, early_g θ M x z) * I := by rw [Finset.sum_mul]
    _ ≤ I * I := mul_le_mul (hrow x |>.trans hCKI) le_rfl hI0 hI0
    _ = I ^ 2 := by ring

end WeightedRows


/-- (7.20) [uvc:eq:primitive-coarse-row] and (7.21) [uvc:eq:primitive-coarse-derivative]:
coarse bounds of `F_k` from `|M_B| ≤ C_M` alone, uniformly in `g` and `L`. -/
theorem primLoopF_coarse (CM : ℝ) (hCM : 0 < CM) (k : ℕ) (hk : 2 ≤ k) :
    ∃ Ck : ℝ, 0 < Ck ∧ ∀ g : ℝ, 0 ≤ g → ∀ L : ℕ, 3 ≤ L → ∀ (E : ℝ) (m : ℂ),
      IsDysonRootV (hopB g) (gammaG g) L E m →
      (∀ a b, ‖dysonMat (hopB g) (gammaG g) L E m a b‖ ≤ CM) → ∀ t : ℝ, 0 ≤ t → t < 1 →
      (∀ (a : Fin k → Fin L) (σ : Fin k → Bool),
        ‖primLoopF g L E m t a σ‖ ≤ Ck * ((1 - t) ^ (2 * k - 3))⁻¹) ∧
      (∀ (j : Fin k) (a : Fin k → Fin L) (σ : Fin k → Bool),
        gammaG g * ∑ b : Fin L, ‖primLoopF g L E m t (Function.update a j b) σ‖ ≤
          Ck * ((1 - t) ^ (2 * k - 3))⁻¹) ∧
      ∀ (a : Fin k → Fin L) (σ : Fin k → Bool),
        ‖deriv (fun s => primLoopF g L E m s a σ) t‖ ≤ Ck * ((1 - t) ^ (2 * k - 2))⁻¹ := by
  have _hCM := hCM
  obtain ⟨A, hA1, hA⟩ := early_induct 1 (max (CM ^ 2) 1) (max CM 1) le_rfl (le_max_right _ _)
    (le_max_right _ _) k
  refine ⟨(k : ℝ) ^ 2 * A ^ 2, by positivity, ?_⟩
  intro g hg L hL E m hm hMb t ht0 ht1
  have hD := primData_of_root g L hL E m hm
  have hU : ∀ u t' : ℝ, 0 ≤ u → u ≤ t' → t' ≤ t → ∀ (s s' : Bool) (a : Fin L),
      ∑ b, Real.exp (2 * 0 * cycDist a b) *
        ‖pairU (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) u t' s s' a b‖ ≤
          1 * ((1 - u) / (1 - t')) := by
    intro u t' hu hut' ht't s s' a
    simp only [mul_zero, zero_mul, Real.exp_zero, one_mul]
    exact early_U_row hD hu hut' (lt_of_le_of_lt ht't ht1) s s' a
  have hbase := early_base_coarse hD ht1 hMb
  have hI : (1 : ℝ) ≤ max CM 1 := le_max_right _ _
  have hinit := early_init_all le_rfl hD.pos hD
    (fun k' hk' a σ => primLoopF_init g L hL E m hm k' hk' a σ) hI
    (fun x y => by
      simp only [early_g, zero_mul, Real.exp_zero, one_mul]
      exact (hMb x y).trans (le_max_left _ _))
    (fun x y => early_Mr_coarse hD hI x y)
  have hbd := hA L (gammaG g) 0 t (dysonMat (hopB g) (gammaG g) L E m) m hD le_rfl ht1 hU hbase
    hinit
  have hAk : A ≤ (k : ℝ) ^ 2 * A ^ 2 := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      nlinarith
    nlinarith
  have h1t : 0 < 1 - t := by linarith
  have hp : 0 ≤ ((1 - t) ^ (2 * k - 3))⁻¹ := by positivity
  refine ⟨fun a σ => ?_, fun j a σ => ?_, fun a σ => ?_⟩
  · have := ((hbd k hk le_rfl) t ht0 le_rfl).1 a σ
    simp only [zero_mul, Real.exp_zero, one_mul] at this
    exact this.trans (mul_le_mul_of_nonneg_right hAk hp)
  · have := ((hbd k hk le_rfl) t ht0 le_rfl).2 j a σ
    simp only [zero_mul, Real.exp_zero, one_mul] at this
    exact this.trans (mul_le_mul_of_nonneg_right hAk hp)
  · exact (early_deriv hD hk ht0 ht1 (fun n' h1 h2 => hbd n' h1 h2) a σ).trans
      (le_of_eq (by ring))

/-- The crude weighted bound of the proof of Proposition B.2 [ba:prop:primitive], on
`0 ≤ g ≤ C`, with no condition on `W` or an upper bound on `L`. -/
theorem primLoopF_bdd_weighted (C B₀ c' : ℝ) (hC : 0 < C) (hB₀ : 0 < B₀) (hc' : 0 < c')
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ C₁ c₁ : ℝ, ∃ L₀ : ℕ, 0 < C₁ ∧ 0 < c₁ ∧ ∀ g : ℝ, 0 ≤ g → g ≤ C → ∀ L : ℕ, 3 ≤ L →
      L₀ ≤ L → ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m →
      c' ≤ m.im → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (a : Fin k → Fin L) (σ : Fin k → Bool),
        ‖primLoopF g L E m t a σ‖ ≤
          C₁ * (1 - t) ^ (-C₁) * Real.exp (-(c₁ * wordDiam a / ellProp g L t)) := by
  obtain ⟨cK, CK, L₁, hcK, hCK, H1⟩ := bdd_kernels C B₀ c' hC hB₀ hc'
  obtain ⟨c₂, C₂, L₂, hc₂, hC₂, H2⟩ := scalesProp_bdd C B₀ c' hC hB₀ hc'
  set CKm : ℝ := max CK 1 with hCKm
  have hCKm1 : 1 ≤ CKm := le_max_right _ _
  set CKK : ℝ := CKm + CKm ^ 3 with hCKK
  have hCKK1 : 1 ≤ CKK := by
    have : 0 ≤ CKm ^ 3 := by positivity
    linarith
  set Γ : ℝ := (max 1 C) ^ 2 with hΓ
  have hΓ1 : 1 ≤ Γ := one_le_pow₀ (le_max_left _ _)
  obtain ⟨A, hA1, hA⟩ := early_induct (1 + CKK) (max 1 (Γ * CKK)) CKm (by linarith)
    (le_max_left _ _) hCKm1 k
  refine ⟨A + 2 * k, cK / 2, max L₁ L₂, by positivity, by positivity, ?_⟩
  intro g hg hgC L hL hL₀ E hE m hm hcm t ht0 ht1 a σ
  have hD := primData_of_root g L hL E m hm
  have hL₁ : L₁ ≤ L := le_trans (le_max_left _ _) hL₀
  have hL₂ : L₂ ≤ L := le_trans (le_max_right _ _) hL₀
  have hmax : (1 : ℝ) ≤ max 1 g := le_max_left _ _
  have hβ1 : gammaG g ≤ 1 := by
    unfold gammaG
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hmax)
  have hβinv : (gammaG g)⁻¹ ≤ Γ := by
    unfold gammaG
    rw [inv_inv]
    exact pow_le_pow_left₀ (by linarith) (max_le_max le_rfl hgC) 2
  have hβinv1 : 1 ≤ (gammaG g)⁻¹ := by
    rw [one_le_inv₀ hD.pos]; exact hβ1
  have hell1 : ∀ t' : ℝ, 0 ≤ t' → t' < 1 → 1 ≤ ellProp g L t' := fun t' _ _ =>
    early_ell_ge_one g hg L (by omega) t'
  have hellmono : ∀ t' : ℝ, 0 ≤ t' → t' ≤ t → ellProp g L t' ≤ ellProp g L t := fun t' _ h1 =>
    early_ell_mono g hg L h1 ht1
  set ℓ : ℝ := ellProp g L t with hℓ
  have hℓ1 : 1 ≤ ℓ := hell1 t ht0 ht1
  set θ : ℝ := cK / (2 * ℓ) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have h2θ : 2 * θ = cK / ℓ := by rw [hθ]; field_simp
  have hθK : θ ≤ cK / ellProp g L t := by
    rw [← hℓ]
    calc θ = cK / (2 * ℓ) := rfl
      _ ≤ cK / ℓ := div_le_div_of_nonneg_left hcK.le (by linarith) (by linarith)
  have hθc : θ ≤ cK := by
    refine hθK.trans ?_
    exact div_le_self hcK.le hℓ1
  -- the weighted bounds of the kernels at the times `t' ∈ [0, t]`
  have hKw : ∀ t' : ℝ, 0 ≤ t' → t' ≤ t → ∀ lm : ℝ, 0 ≤ lm → lm ≤ cK / ellProp g L t' →
      ∀ (s s' : Bool) (x : Fin L),
      ∑ b, Real.exp (lm * cycDist x b) * ‖pairK (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)
        t' s s' x b‖ ≤ CKK / (1 - t') := by
    intro t' ht'0 ht't lm hlm hlmK s s' x
    have ht'1 : t' < 1 := lt_of_le_of_lt ht't ht1
    have F1 := H1 g hg hgC L hL hL₁ E hE m hm hcm t' ht'0 ht'1
    have F2 := H2 g hg hgC L hL hL₂ E hE m hm hcm
    exact early_K_wrow hD hβ1 (hell1 t' ht'0 ht'1) hlm hlmK hCKm1 ht'0 ht'1
      (fun a b => (F2.2.2.2.2 t' ht'0 ht'1 a b).1)
      (fun a => (F1.2.2.1 a).trans (le_max_left _ _))
      (fun a => (F1.2.2.2.1 a).trans (div_le_div_of_nonneg_right (le_max_left _ _) (by linarith)))
      (fun a => (F1.2.2.2.2 a).trans (le_max_left _ _)) s s' x
  have hU : ∀ u t' : ℝ, 0 ≤ u → u ≤ t' → t' ≤ t → ∀ (s s' : Bool) (x : Fin L),
      ∑ b, Real.exp (2 * θ * cycDist x b) *
        ‖pairU (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) u t' s s' x b‖ ≤
          (1 + CKK) * ((1 - u) / (1 - t')) := by
    intro u t' hu hut' ht't s s' x
    have ht'0 : 0 ≤ t' := hu.trans hut'
    have ht'1 : t' < 1 := lt_of_le_of_lt ht't ht1
    have h2θ' : 2 * θ ≤ cK / ellProp g L t' := by
      rw [h2θ]
      exact div_le_div_of_nonneg_left hcK.le (by linarith [hell1 t' ht'0 ht'1])
        (hellmono t' ht'0 ht't)
    exact early_U_wrow hD hu hut' ht'1 (by linarith)
      (fun s s' x => hKw t' ht'0 ht't (2 * θ) (by positivity) h2θ' s s' x) s s' x
  have hθ' : ∀ t' : ℝ, 0 ≤ t' → t' ≤ t → θ ≤ cK / ellProp g L t' := by
    intro t' ht'0 ht't
    have h1 := hell1 t' ht'0 (lt_of_le_of_lt ht't ht1)
    exact hθK.trans (div_le_div_of_nonneg_left hcK.le (by linarith) (hellmono t' ht'0 ht't))
  have hbase := early_base_wtd hθ0 hD ht1 hβinv hΓ1 hCKK1
    (fun t' ht'0 ht't s s' x => hKw t' ht'0 ht't θ hθ0 (hθ' t' ht'0 ht't) s s' x)
  have hF0 := H1 g hg hgC L hL hL₁ E hE m hm hcm 0 le_rfl one_pos
  have hMrow : ∀ x : Fin L, ∑ b, Real.exp (cK * cycDist x b) *
      ‖dysonMat (hopB g) (gammaG g) L E m x b‖ ≤ CKm := fun x =>
    (hF0.2.2.1 x).trans (le_max_left _ _)
  obtain ⟨hMe, hMr⟩ := early_Mwt hβ1 hθc le_rfl (by linarith) hMrow
  have hinit := early_init_all hθ0 hD.pos hD
    (fun k' hk' a σ => primLoopF_init g L hL E m hm k' hk' a σ) hCKm1 hMe hMr
  have hbd := hA L (gammaG g) θ t (dysonMat (hopB g) (gammaG g) L E m) m hD hθ0 ht1 hU hbase hinit
    k hk le_rfl
  have h := (hbd t ht0 le_rfl).1 a σ
  have h1t : 0 < 1 - t := by linarith
  -- the weight
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
  have hθd : θ * (wordDiam a : ℝ) = cK / 2 * wordDiam a / ellProp g L t := by
    rw [hθ, hℓ]; field_simp
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
  have hexp0 : 0 ≤ Real.exp (-(cK / 2 * wordDiam a / ellProp g L t)) := (Real.exp_pos _).le
  have hp0 : 0 ≤ ((1 - t) ^ (2 * k - 3))⁻¹ := by positivity
  have hAC : A ≤ A + 2 * k := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  calc A * ((1 - t) ^ (2 * k - 3))⁻¹ * Real.exp (-(cK / 2 * wordDiam a / ellProp g L t))
      ≤ (A + 2 * k) * (1 - t) ^ (-(A + 2 * k)) *
          Real.exp (-(cK / 2 * wordDiam a / ellProp g L t)) := by
        refine mul_le_mul_of_nonneg_right ?_ hexp0
        exact mul_le_mul hAC hrp hp0 (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])

/-- For `t ≤ 1/2` and `0 ≤ g ≤ C` the quantity `1 + g/√(γ_g (1 - t))` is at most
`1 + 2 C max{1, C}`. -/
private lemma early_ell_core {C g t : ℝ} (hg : 0 ≤ g) (hgC : g ≤ C) (ht : t ≤ 1 / 2) :
    1 + g / Real.sqrt (gammaG g * (1 - t)) ≤ 1 + 2 * C * max 1 C := by
  have hM : (1 : ℝ) ≤ max 1 C := le_max_left _ _
  have hM0 : 0 < max 1 C := by linarith
  have hγ : 1 / (max 1 C) ^ 2 ≤ gammaG g := by
    unfold gammaG
    rw [one_div]
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_left₀ (by linarith [le_max_left 1 g]) (max_le_max le_rfl hgC) 2
  have hX : (1 / (2 * max 1 C)) ^ 2 ≤ gammaG g * (1 - t) := by
    calc (1 / (2 * max 1 C)) ^ 2 = 1 / (4 * (max 1 C) ^ 2) := by field_simp; ring
      _ ≤ 1 / (max 1 C) ^ 2 * (1 / 2) := by
          rw [div_mul_div_comm, one_mul]
          apply one_div_le_one_div_of_le (by positivity)
          nlinarith [sq_nonneg (max 1 C)]
      _ ≤ gammaG g * (1 - t) := by
          apply mul_le_mul hγ (by linarith) (by norm_num) (early_gamma_pos g).le
  have hs : 1 / (2 * max 1 C) ≤ Real.sqrt (gammaG g * (1 - t)) :=
    Real.le_sqrt_of_sq_le hX
  have hspos : 0 < 1 / (2 * max 1 C) := by positivity
  calc 1 + g / Real.sqrt (gammaG g * (1 - t)) ≤ 1 + g / (1 / (2 * max 1 C)) := by
        have := div_le_div_of_nonneg_left hg hspos hs
        linarith
    _ = 1 + 2 * max 1 C * g := by field_simp
    _ ≤ 1 + 2 * C * max 1 C := by nlinarith

/-- For `t ≤ 1/2` and `0 ≤ g ≤ C` the scale `ℓ_t` is at most `1 + 2 C max{1, C}`. -/
private lemma early_ell_bdd {C g t : ℝ} (hg : 0 ≤ g) (hgC : g ≤ C) (L : ℕ)
    (ht : t ≤ 1 / 2) : ellProp g L t ≤ 1 + 2 * C * max 1 C :=
  (min_le_right _ _).trans (early_ell_core hg hgC ht)

/-- (B.13) [b:eq:early-primitive], Lemma B.10 [b:lem:early-primitive](a), on `0 ≤ g ≤ C`, for
every `W ≥ 1` and `L ≥ L₀`. -/
theorem primLoop_early (C B₀ c' : ℝ) (hC : 0 < C) (hB₀ : 0 < B₀) (hc' : 0 < c') (k : ℕ)
    (hk : 2 ≤ k) :
    ∃ Ck ck : ℝ, ∃ L₀ : ℕ, 0 < Ck ∧ 0 < ck ∧ ∀ g : ℝ, 0 ≤ g → g ≤ C → ∀ L : ℕ, 3 ≤ L →
      L₀ ≤ L → ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m →
      c' ≤ m.im → ∀ W : ℕ, 1 ≤ W → ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 →
      ∀ (a : Fin k → Fin L) (σ : Fin k → Bool),
        Real.exp (ck * wordDiam a) * ‖primLoop g W L E m t a σ‖ ≤ Ck * (W : ℝ) ^ (1 - (k : ℝ)) := by
  obtain ⟨C₁, c₁, L₀, hC₁, hc₁, H⟩ := primLoopF_bdd_weighted C B₀ c' hC hB₀ hc' k hk
  set ℓb : ℝ := 1 + 2 * C * max 1 C with hℓb
  have hℓb1 : 1 ≤ ℓb := by
    have : 0 ≤ 2 * C * max 1 C := by positivity
    linarith
  refine ⟨C₁ * (1 / 2 : ℝ) ^ (-C₁), c₁ / ℓb, L₀, by positivity, by positivity, ?_⟩
  intro g hg hgC L hL hL₀ E hE m hm hcm W hW t ht0 ht2 a σ
  have ht1 : t < 1 := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hF := H g hg hgC L hL hL₀ E hE m hm hcm t ht0 ht1 a σ
  have hell : ellProp g L t ≤ ℓb := early_ell_bdd hg hgC L ht2
  have hell1 : 1 ≤ ellProp g L t := early_ell_ge_one g hg L (by omega) t
  have hnorm : ‖primLoop g W L E m t a σ‖ = (W : ℝ) ^ (1 - (k : ℝ)) *
      ‖primLoopF g L E m t a σ‖ := by
    have : primLoop g W L E m t a σ = (W : ℂ) ^ (1 - (k : ℤ)) * primLoopF g L E m t a σ := rfl
    rw [this, norm_mul, norm_zpow, Complex.norm_natCast]
    congr 1
    rw [← Real.rpow_intCast]
    push_cast
    rfl
  rw [hnorm]
  have hdiam : c₁ / ℓb * (wordDiam a : ℝ) ≤ c₁ * wordDiam a / ellProp g L t := by
    have h1 : c₁ / ℓb ≤ c₁ / ellProp g L t :=
      div_le_div_of_nonneg_left hc₁.le (by linarith) hell
    calc c₁ / ℓb * (wordDiam a : ℝ) ≤ c₁ / ellProp g L t * (wordDiam a : ℝ) :=
          mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
      _ = c₁ * wordDiam a / ellProp g L t := by ring
  have h2 : (1 - t) ^ (-C₁) ≤ (1 / 2 : ℝ) ^ (-C₁) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by linarith)
  have hexp : Real.exp (c₁ / ℓb * wordDiam a) *
      Real.exp (-(c₁ * wordDiam a / ellProp g L t)) ≤ 1 := by
    rw [← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    linarith
  have hWk : 0 ≤ (W : ℝ) ^ (1 - (k : ℝ)) := (Real.rpow_pos_of_pos hW0 _).le
  calc Real.exp (c₁ / ℓb * wordDiam a) *
        ((W : ℝ) ^ (1 - (k : ℝ)) * ‖primLoopF g L E m t a σ‖)
      ≤ Real.exp (c₁ / ℓb * wordDiam a) * ((W : ℝ) ^ (1 - (k : ℝ)) *
          (C₁ * (1 - t) ^ (-C₁) * Real.exp (-(c₁ * wordDiam a / ellProp g L t)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hF hWk) (Real.exp_pos _).le
    _ = (W : ℝ) ^ (1 - (k : ℝ)) * (C₁ * (1 - t) ^ (-C₁)) *
          (Real.exp (c₁ / ℓb * wordDiam a) * Real.exp (-(c₁ * wordDiam a / ellProp g L t))) := by
        ring
    _ ≤ (W : ℝ) ^ (1 - (k : ℝ)) * (C₁ * (1 - t) ^ (-C₁)) * 1 :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ (W : ℝ) ^ (1 - (k : ℝ)) * (C₁ * (1 / 2 : ℝ) ^ (-C₁)) := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hC₁.le) hWk
    _ = C₁ * (1 / 2 : ℝ) ^ (-C₁) * (W : ℝ) ^ (1 - (k : ℝ)) := by ring

/-- Superpolynomial decay: `C₁ W^{3C₁} e^{-c₁ W^ε} ≤ W^{-Q}` for large `W`. -/
private lemma early_tail_analytic {C₁ c₁ ε Q : ℝ} (hC₁ : 0 < C₁) (hc₁ : 0 < c₁) (hε : 0 < ε) :
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

/-- (5.21) [fo:eq:primitive-tail] in case (a), Appendix B.6 [app:primitive-tails], on
`0 ≤ g ≤ C`. -/
theorem primLoop_bdd_tail (C B₀ c' ε Q : ℝ) (hC : 0 < C) (hB₀ : 0 < B₀) (hc' : 0 < c')
    (hε : 0 < ε) (hQ : 0 < Q) (k : ℕ) (hk : 2 ≤ k) :
    ∃ W₀ L₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, 0 ≤ g → g ≤ C → ∀ L : ℕ, 3 ≤ L → L₀ ≤ L →
      ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m → c' ≤ m.im →
      ∀ t : ℝ, 0 ≤ t → (W : ℝ) ^ (-3 : ℝ) ≤ 1 - t → ∀ (a : Fin k → Fin L) (σ : Fin k → Bool),
        (W : ℝ) ^ ε * ellProp g L t < wordDiam a →
        ‖primLoop g W L E m t a σ‖ ≤ (W : ℝ) ^ (-Q) := by
  have _hQ := hQ
  obtain ⟨C₁, c₁, L₀, hC₁, hc₁, H⟩ := primLoopF_bdd_weighted C B₀ c' hC hB₀ hc' k hk
  obtain ⟨W₀, hW₀1, hW₀⟩ := early_tail_analytic (Q := Q) hC₁ hc₁ hε
  refine ⟨W₀, L₀, ?_⟩
  intro W hW g hg hgC L hL hL₀ E hE m hm hcm t ht0 hWt a σ hdiam
  have hW1 : 1 ≤ W := le_trans hW₀1 hW
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hW3 : 0 < (W : ℝ) ^ (-3 : ℝ) := Real.rpow_pos_of_pos hW0 _
  have ht1 : t < 1 := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hF := H g hg hgC L hL hL₀ E hE m hm hcm t ht0 ht1 a σ
  have hle : ‖primLoop g W L E m t a σ‖ ≤ ‖primLoopF g L E m t a σ‖ := by
    have : primLoop g W L E m t a σ = (W : ℂ) ^ (1 - (k : ℤ)) * primLoopF g L E m t a σ := rfl
    rw [this, norm_mul, norm_zpow, Complex.norm_natCast]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    exact zpow_le_one_of_nonpos₀ (by exact_mod_cast hW1) (by omega)
  have hell1 : 1 ≤ ellProp g L t := early_ell_ge_one g hg L (by omega) t
  have hdiam' : (W : ℝ) ^ ε < wordDiam a / ellProp g L t := by
    rw [lt_div_iff₀ (by linarith)]
    exact hdiam
  have hexp : Real.exp (-(c₁ * wordDiam a / ellProp g L t)) ≤
      Real.exp (-(c₁ * (W : ℝ) ^ ε)) := by
    apply Real.exp_le_exp.mpr
    have : c₁ * (W : ℝ) ^ ε ≤ c₁ * (wordDiam a / ellProp g L t) :=
      mul_le_mul_of_nonneg_left hdiam'.le hc₁.le
    have e : c₁ * wordDiam a / ellProp g L t = c₁ * (wordDiam a / ellProp g L t) := by ring
    linarith
  have hpow : (1 - t) ^ (-C₁) ≤ (W : ℝ) ^ (3 * C₁) := by
    have h1 : (1 - t) ^ (-C₁) ≤ ((W : ℝ) ^ (-3 : ℝ)) ^ (-C₁) :=
      Real.rpow_le_rpow_of_nonpos hW3 hWt (by linarith)
    refine h1.trans (le_of_eq ?_)
    rw [← Real.rpow_mul hW0.le]
    congr 1
    ring
  calc ‖primLoop g W L E m t a σ‖ ≤ ‖primLoopF g L E m t a σ‖ := hle
    _ ≤ C₁ * (1 - t) ^ (-C₁) * Real.exp (-(c₁ * wordDiam a / ellProp g L t)) := hF
    _ ≤ C₁ * (W : ℝ) ^ (3 * C₁) * Real.exp (-(c₁ * (W : ℝ) ^ ε)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow hC₁.le) hexp (Real.exp_pos _).le (by positivity)
    _ ≤ (W : ℝ) ^ (-Q) := hW₀ W hW

end LSBA
