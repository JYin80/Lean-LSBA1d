import LSBA.Upper.LiftPairs
import LSBA.Analysis.LeastSquares

/-!
# The reconstruction `𝒦₀` and the left inverse of `g 𝒜*`

The left inverse `𝒥 = (𝓛*𝓛)⁻¹ 𝓛*` of `𝓛_G` on `𝒬_W = {P : Im Tr P = 0}` where
`S_W(G) ≥ c₁ > 0`, realized as the least-squares left inverse of
`P ↦ (𝓛_G P, W^{-1/2} Im Tr P)` in the real coordinates of `P`; `𝒦_P = 2^{-1/2} g 𝒥 𝓕` and
`𝒦₀ R = [[P, P C_q + C_q P* + C_q R_q C_q - R_{q-1}], [R_q, -P*]]` of (10.15)
[eq:c-main-reconstruction] and (G.20) [eq:c-reconstruction]; the left-inverse identity (10.10)
[eq:c-main-left-inverse], (G.21) [eq:c-right-inverse] `𝒦₀(g 𝒜* Z) = Z`; and the pairing
(10.25) [eq:c-K0-adjoint] (Section 10 [sec:compact-proof], Appendix G.5 [sec:c-component-proof]).
-/

open Real Finset
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The real matrix of `P ↦ (𝓛_G P, W^{-1/2} Im Tr P)` in the coordinates `reCoord`. -/
def cohRealMat {m W : ℕ} (G : Fin m → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Option (Fin m × Fin 2 × Fin W × Fin W)) (Fin 2 × Fin W × Fin W) ℝ :=
  Matrix.of fun p r => Option.elim p
    ((ofReCoord (Pi.single r 1) : Matrix (Fin W) (Fin W) ℂ).trace.im / Real.sqrt W)
    fun s => reCoord (cohMap G (ofReCoord (Pi.single r 1)) s.1) s.2

/-- The left inverse `𝒥 D = (𝓛*𝓛)⁻¹ 𝓛* D` of `𝓛_G` on `𝒬_W` (Section 10 [sec:compact-proof]),
as the least-squares solution of `𝓛_G P = D`, `Im Tr P = 0`. -/
def cohLeftInv {m W : ℕ} (G D : Fin m → Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  ofReCoord (lsqInv (cohRealMat G) *ᵥ fun p => Option.elim p 0 fun s => reCoord (D s.1) s.2)

section LiftReconstructAux

private lemma LiftReconstruct_ofReCoord_add {k l : Type*} (a : ℝ) (x y : Fin 2 × k × l → ℝ) :
    (ofReCoord (a • x + y) : Matrix k l ℂ) = a • ofReCoord x + ofReCoord y := by
  ext i j
  apply Complex.ext <;> simp [ofReCoord]

private lemma LiftReconstruct_reCoord_add {k l : Type*} (a : ℝ) (A B : Matrix k l ℂ) :
    reCoord (a • A + B) = a • reCoord A + reCoord B := by
  funext p
  by_cases h : p.1 = 0 <;> simp [reCoord, h]

private lemma LiftReconstruct_cohMap_add {m W : ℕ} (G : Fin m → Matrix (Fin W) (Fin W) ℂ)
    (a : ℝ) (P Q : Matrix (Fin W) (Fin W) ℂ) :
    cohMap G (a • P + Q) = a • cohMap G P + cohMap G Q := by
  funext j
  simp only [cohMap, Pi.add_apply, Pi.smul_apply, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, star_trivial, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_add]
  abel

/-- The real-linear map whose matrix is `cohRealMat G`. -/
private def LiftReconstruct_lin {m W : ℕ} (G : Fin m → Matrix (Fin W) (Fin W) ℂ) :
    (Fin 2 × Fin W × Fin W → ℝ) →ₗ[ℝ] (Option (Fin m × Fin 2 × Fin W × Fin W) → ℝ) where
  toFun x p := Option.elim p
    ((ofReCoord x : Matrix (Fin W) (Fin W) ℂ).trace.im / Real.sqrt W)
    fun s => reCoord (cohMap G (ofReCoord x) s.1) s.2
  map_add' x y := by
    have h := LiftReconstruct_ofReCoord_add (k := Fin W) (l := Fin W) 1 x y
    have h' := LiftReconstruct_cohMap_add G 1 (ofReCoord x) (ofReCoord y)
    simp only [one_smul] at h h'
    funext p
    cases p with
    | none => simp [h, Matrix.trace_add, add_div]
    | some s =>
      have h'' := congrFun (LiftReconstruct_reCoord_add 1 (cohMap G (ofReCoord x) s.1)
        (cohMap G (ofReCoord y) s.1)) s.2
      simpa [h, h'] using h''
  map_smul' a x := by
    have h := LiftReconstruct_ofReCoord_add (k := Fin W) (l := Fin W) a x 0
    have h' := LiftReconstruct_cohMap_add G a (ofReCoord x) 0
    have h0 : (ofReCoord (0 : Fin 2 × Fin W × Fin W → ℝ) : Matrix (Fin W) (Fin W) ℂ) = 0 := by
      ext i j; apply Complex.ext <;> simp [ofReCoord]
    have hc0 : cohMap G (0 : Matrix (Fin W) (Fin W) ℂ) = 0 := by
      funext j; simp [cohMap]
    simp only [add_zero, h0, hc0] at h h'
    funext p
    cases p with
    | none => simp [h, Matrix.trace_smul, mul_div_assoc]
    | some s =>
      have h'' := LiftReconstruct_reCoord_add a (cohMap G (ofReCoord x) s.1) 0
      simp only [add_zero] at h''
      have h0' : reCoord (0 : Matrix (Fin W) (Fin W) ℂ) = 0 := by
        funext p; simp [reCoord]
      simp [h, h', h'', h0']

private lemma LiftReconstruct_mulVec {m W : ℕ} (G : Fin m → Matrix (Fin W) (Fin W) ℂ)
    (x : Fin 2 × Fin W × Fin W → ℝ) :
    cohRealMat G *ᵥ x = fun p => Option.elim p
      ((ofReCoord x : Matrix (Fin W) (Fin W) ℂ).trace.im / Real.sqrt W)
      fun s => reCoord (cohMap G (ofReCoord x) s.1) s.2 := by
  have e : cohRealMat G = LinearMap.toMatrix' (LiftReconstruct_lin G) := by
    ext p r
    rw [LinearMap.toMatrix'_apply]
    rfl
  rw [e, LinearMap.toMatrix'_mulVec]
  rfl

private lemma LiftReconstruct_sum_sq_reCoord {k l : Type*} [Fintype k] [Fintype l]
    (A : Matrix k l ℂ) : ∑ p, reCoord A p ^ 2 = hsSq A := by
  obtain ⟨-, h2, -, -, h5⟩ := hsInner_reCoord A A 0
  rw [← h2, ← h5]
  simp only [sq]

private lemma LiftReconstruct_sum_sq {k l : Type*} [Fintype k] [Fintype l]
    (x : Fin 2 × k × l → ℝ) : ∑ r, x r ^ 2 = hsSq (ofReCoord x : Matrix k l ℂ) := by
  rw [← LiftReconstruct_sum_sq_reCoord, (hsInner_reCoord (0 : Matrix k l ℂ) 0 x).2.2.2.1]

private lemma LiftReconstruct_sum_sq_mulVec {m W : ℕ} (G : Fin m → Matrix (Fin W) (Fin W) ℂ)
    (x : Fin 2 × Fin W × Fin W → ℝ) :
    ∑ p, (cohRealMat G *ᵥ x) p ^ 2 =
      (ofReCoord x : Matrix (Fin W) (Fin W) ℂ).trace.im ^ 2 / W +
        ∑ j, hsSq (cohMap G (ofReCoord x) j) := by
  rw [LiftReconstruct_mulVec, Fintype.sum_option, Fintype.sum_prod_type]
  simp only [Option.elim_none, Option.elim_some]
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg W)]
  congr 1
  exact Finset.sum_congr rfl fun j _ => LiftReconstruct_sum_sq_reCoord _

private lemma LiftReconstruct_sum_sq_data {m W : ℕ} (D : Fin m → Matrix (Fin W) (Fin W) ℂ) :
    ∑ p : Option (Fin m × Fin 2 × Fin W × Fin W),
      (Option.elim p 0 fun s => reCoord (D s.1) s.2 : ℝ) ^ 2 = ∑ j, hsSq (D j) := by
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [Option.elim_none, Option.elim_some]
  rw [sq, zero_mul, zero_add]
  exact Finset.sum_congr rfl fun j _ => LiftReconstruct_sum_sq_reCoord _

private lemma LiftReconstruct_hsInner_I {W : ℕ} (P : Matrix (Fin W) (Fin W) ℂ) :
    hsInner P (Complex.I • (1 : Matrix (Fin W) (Fin W) ℂ)) = P.trace.im := by
  rw [(hsInner_reCoord _ _ 0).1, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    Matrix.trace_conjTranspose]
  simp [Complex.mul_re]

private lemma LiftReconstruct_cohMap_I {m W : ℕ} (G : Fin m → Matrix (Fin W) (Fin W) ℂ) :
    cohMap G (Complex.I • (1 : Matrix (Fin W) (Fin W) ℂ)) = 0 := by
  funext j
  simp [cohMap, Matrix.conjTranspose_smul]

private lemma LiftReconstruct_W_ne {m W : ℕ} {G : Fin m → Matrix (Fin W) (Fin W) ℂ} {c₁ : ℝ}
    (hc₁ : 0 < c₁) (hc : c₁ ≤ coerMin G) : (W : ℝ) ≠ 0 := by
  intro hW
  have hW' : W = 0 := by exact_mod_cast hW
  subst hW'
  have : IsEmpty {P : Matrix (Fin 0) (Fin 0) ℂ // P.trace.im = 0 ∧ hsSq P = 1} :=
    ⟨fun ⟨P, _, h⟩ => by simp [hsSq] at h⟩
  have h0 : coerMin G = 0 := Real.iInf_of_isEmpty _
  linarith

private lemma LiftReconstruct_lower {m W : ℕ} {G : Fin m → Matrix (Fin W) (Fin W) ℂ} {c₁ : ℝ}
    (hc₁ : 0 < c₁) (hc : c₁ ≤ coerMin G) (x : Fin 2 × Fin W × Fin W → ℝ) :
    min c₁ 1 ^ 2 * ∑ r, x r ^ 2 ≤ ∑ p, (cohRealMat G *ᵥ x) p ^ 2 := by
  have hW := LiftReconstruct_W_ne hc₁ hc
  have hWpos : (0 : ℝ) < W := lt_of_le_of_ne (Nat.cast_nonneg W) (Ne.symm hW)
  set E : Matrix (Fin W) (Fin W) ℂ := Complex.I • 1 with hE
  set P : Matrix (Fin W) (Fin W) ℂ := ofReCoord x with hP
  set θ := P.trace.im with hθ
  set a : ℝ := -(θ / W) with ha
  have hEE : hsSq E = W := by
    rw [← (hsInner_reCoord E E 0).2.1, hE, LiftReconstruct_hsInner_I]
    simp [Matrix.trace_smul]
  have h1 : (a • E + P).trace.im = 0 := by
    rw [Matrix.trace_add, Complex.add_im, Matrix.trace_smul, Complex.smul_im, ← hθ]
    have : E.trace.im = W := by rw [hE]; simp [Matrix.trace_smul]
    rw [this, ha, smul_eq_mul, neg_mul, div_mul_cancel₀ θ hW]
    ring
  have h2 : cohMap G (a • E + P) = cohMap G P := by
    rw [LiftReconstruct_cohMap_add, hE, LiftReconstruct_cohMap_I, smul_zero, zero_add]
  have h3 : hsSq P = hsSq (a • E + P) + θ ^ 2 / W := by
    rw [← LiftReconstruct_sum_sq_reCoord, ← LiftReconstruct_sum_sq_reCoord (a • E + P),
      LiftReconstruct_reCoord_add]
    have hEP : ∑ r, reCoord P r * reCoord E r = θ := by
      rw [(hsInner_reCoord P E 0).2.2.2.2, hE, LiftReconstruct_hsInner_I]
    have hE2 : ∑ r, reCoord E r ^ 2 = W := by rw [LiftReconstruct_sum_sq_reCoord, hEE]
    have e : ∀ r, ((a • reCoord E + reCoord P) r) ^ 2 =
        a ^ 2 * reCoord E r ^ 2 + 2 * a * (reCoord P r * reCoord E r) + reCoord P r ^ 2 := by
      intro r
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    simp only [e]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hEP, hE2]
    rw [ha]
    field_simp
    ring
  have h4 : c₁ ^ 2 * hsSq (a • E + P) ≤ ∑ j, hsSq (cohMap G P j) := by
    have hm := coerMin_mul_le G h1
    rw [h2] at hm
    have hs0 : 0 ≤ hsSq (a • E + P) := by
      rw [← LiftReconstruct_sum_sq_reCoord]; positivity
    have hS0 : 0 ≤ ∑ j, hsSq (cohMap G P j) := by
      refine Finset.sum_nonneg fun j _ => ?_
      rw [← LiftReconstruct_sum_sq_reCoord]; positivity
    have hm' : c₁ * Real.sqrt (hsSq (a • E + P)) ≤ Real.sqrt (∑ j, hsSq (cohMap G P j)) :=
      (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)).trans hm
    have := pow_le_pow_left₀ (by positivity) hm' 2
    rwa [mul_pow, Real.sq_sqrt hs0, Real.sq_sqrt hS0] at this
  rw [LiftReconstruct_sum_sq_mulVec, LiftReconstruct_sum_sq, ← hP, ← hθ, h3]
  have hτ1 : min c₁ 1 ≤ c₁ := min_le_left _ _
  have hτ2 : min c₁ 1 ≤ 1 := min_le_right _ _
  have hτ0 : 0 < min c₁ 1 := lt_min hc₁ one_pos
  have hs0 : 0 ≤ hsSq (a • E + P) := by
    rw [← LiftReconstruct_sum_sq_reCoord]; positivity
  have hθ0 : 0 ≤ θ ^ 2 / W := by positivity
  have hτc : min c₁ 1 ^ 2 ≤ c₁ ^ 2 := pow_le_pow_left₀ hτ0.le hτ1 2
  have hτ1' : min c₁ 1 ^ 2 ≤ 1 := by
    exact pow_le_one₀ hτ0.le hτ2
  nlinarith [mul_le_mul_of_nonneg_right hτc hs0, mul_le_mul_of_nonneg_right hτ1' hθ0]

end LiftReconstructAux

/-- The left inverse on `{S_W(G) ≥ c₁}` (Section 10 [sec:compact-proof], (10.14)
[eq:c-main-coercivity]): for Hermitian `G_j` and `0 < c₁ ≤ S_W(G)`, `𝒥 𝓛 P = P` on `𝒬_W`,
`𝒥` maps into `𝒬_W`, `‖𝒥 D‖ ≤ min{c₁, 1}⁻¹ ‖D‖`, and the real matrix is bounded below by
`min{c₁, 1}`. -/
theorem cohLeftInv_spec {m W : ℕ} {G : Fin m → Matrix (Fin W) (Fin W) ℂ}
    (hG : ∀ j, (G j).IsHermitian) {c₁ : ℝ} (hc₁ : 0 < c₁) (hc : c₁ ≤ coerMin G) :
    (∀ P : Matrix (Fin W) (Fin W) ℂ, P.trace.im = 0 → cohLeftInv G (cohMap G P) = P) ∧
      (∀ D : Fin m → Matrix (Fin W) (Fin W) ℂ, (cohLeftInv G D).trace.im = 0 ∧
        hsSq (cohLeftInv G D) ≤ (min c₁ 1 ^ 2)⁻¹ * ∑ j, hsSq (D j)) ∧
      ∀ x : Fin 2 × Fin W × Fin W → ℝ,
        min c₁ 1 ^ 2 * ∑ r, x r ^ 2 ≤ ∑ p, (cohRealMat G *ᵥ x) p ^ 2 := by
  have _ := hG
  have hτ0 : 0 < min c₁ 1 := lt_min hc₁ one_pos
  have hA := LiftReconstruct_lower (G := G) hc₁ hc
  obtain ⟨hJA, hJ, -⟩ := lsqInv_spec hτ0 hA
  have hW := LiftReconstruct_W_ne hc₁ hc
  have hWpos : (0 : ℝ) < W := lt_of_le_of_ne (Nat.cast_nonneg W) (Ne.symm hW)
  refine ⟨?_, fun D => ⟨?_, ?_⟩, hA⟩
  · intro P hP
    have hy : cohRealMat G *ᵥ reCoord P =
        fun p => Option.elim p 0 fun s => reCoord (cohMap G P s.1) s.2 := by
      rw [LiftReconstruct_mulVec, (hsInner_reCoord P P 0).2.2.1, hP, zero_div]
    unfold cohLeftInv
    rw [← hy, Matrix.mulVec_mulVec, hJA, Matrix.one_mulVec, (hsInner_reCoord P P 0).2.2.1]
  · unfold cohLeftInv
    set A := cohRealMat G with hAdef
    set y : Option (Fin m × Fin 2 × Fin W × Fin W) → ℝ :=
      fun p => Option.elim p 0 fun s => reCoord (D s.1) s.2 with hy
    set e := reCoord (Complex.I • (1 : Matrix (Fin W) (Fin W) ℂ)) with he
    have htr : ∀ v : Fin 2 × Fin W × Fin W → ℝ,
        (ofReCoord v : Matrix (Fin W) (Fin W) ℂ).trace.im = v ⬝ᵥ e := by
      intro v
      rw [← LiftReconstruct_hsInner_I, ← (hsInner_reCoord _ _ v).2.2.2.2,
        (hsInner_reCoord (0 : Matrix (Fin W) (Fin W) ℂ) 0 v).2.2.2.1]
      rfl
    have hAe : A *ᵥ e = fun p => Option.elim p (Real.sqrt W) fun _ => 0 := by
      rw [hAdef, LiftReconstruct_mulVec, he,
        (hsInner_reCoord (Complex.I • (1 : Matrix (Fin W) (Fin W) ℂ)) 0 0).2.2.1,
        LiftReconstruct_cohMap_I]
      funext p
      cases p with
      | none =>
        simp only [Option.elim_none]
        rw [show (Complex.I • (1 : Matrix (Fin W) (Fin W) ℂ)).trace.im = W by
          simp [Matrix.trace_smul], Real.div_sqrt]
      | some s => simp [reCoord]
    have hGe : (Aᵀ * A) *ᵥ e = e := by
      funext r
      rw [← Matrix.mulVec_mulVec, hAe]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fintype.sum_option,
        Option.elim_none, Option.elim_some, mul_zero, Finset.sum_const_zero, add_zero]
      simp only [hAdef, cohRealMat, Matrix.of_apply, Option.elim_none]
      rw [div_mul_cancel₀ _ (Real.sqrt_pos.2 hWpos).ne', htr]
      simp [dotProduct, Pi.single_apply]
    have hinv : (Aᵀ * A)⁻¹ * (Aᵀ * A) = 1 := by
      rw [← Matrix.mul_assoc]; exact hJA
    have hMe : (Aᵀ * A)⁻¹ *ᵥ e = e := by
      conv_lhs => rw [← hGe]
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    have hsym : ((Aᵀ * A)⁻¹)ᵀ = (Aᵀ * A)⁻¹ := by
      rw [Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [htr, dotProduct_comm, lsqInv, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← hsym,
      Matrix.vecMul_transpose, hMe, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hAe]
    simp [dotProduct, Fintype.sum_option, hy]
  · unfold cohLeftInv
    rw [← LiftReconstruct_sum_sq, ← LiftReconstruct_sum_sq_data]
    exact hJ _

/-- `𝒦_P R = 2^{-1/2} g 𝒥 𝓕 R` of Section 10 [sec:compact-proof] for `q = 1000` and the pairs of
`liftLayout`. -/
def liftKP {W : ℕ} (g z : ℝ) (V R : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin W) (Fin W) ℂ :=
  ((((Real.sqrt 2)⁻¹ * g : ℝ)) : ℂ) • cohLeftInv (layoutBlocks liftLayout V) (pairData g z V R)

/-- `𝒦₀ R = [[P, P C_q + C_q P* + C_q R_q C_q - R_{q-1}], [R_q, -P*]]` with `P = 𝒦_P R`,
(10.15) [eq:c-main-reconstruction] and (G.20) [eq:c-reconstruction]; input `999` is the
paper's `q = 1000`. -/
def liftK0 {W : ℕ} (g z : ℝ) (V R : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  blockMat (liftKP g z V R)
    (liftKP g z V R * liftC g z V 999 + liftC g z V 999 * (liftKP g z V R)ᴴ +
      liftC g z V 999 * R 999 * liftC g z V 999 - R 998)
    (R 999) (-(liftKP g z V R)ᴴ)

section LiftReconstructAux2

private lemma LiftReconstruct_cohLeftInv_add {m W : ℕ} (G : Fin m → Matrix (Fin W) (Fin W) ℂ)
    (a : ℝ) (D D' : Fin m → Matrix (Fin W) (Fin W) ℂ) :
    cohLeftInv G (a • D + D') = a • cohLeftInv G D + cohLeftInv G D' := by
  unfold cohLeftInv
  rw [← LiftReconstruct_ofReCoord_add, ← Matrix.mulVec_smul, ← Matrix.mulVec_add]
  congr 2
  funext p
  cases p with
  | none => simp
  | some s =>
    have h := congrFun (LiftReconstruct_reCoord_add a (D s.1) (D' s.1)) s.2
    simpa using h

private lemma LiftReconstruct_cohLeftInv_smul {m W : ℕ} (G : Fin m → Matrix (Fin W) (Fin W) ℂ)
    (a : ℝ) (D : Fin m → Matrix (Fin W) (Fin W) ℂ) :
    cohLeftInv G (a • D) = a • cohLeftInv G D := by
  have h0 : cohLeftInv G 0 = 0 := by
    unfold cohLeftInv
    have e : (fun p : Option (Fin m × Fin 2 × Fin W × Fin W) => Option.elim p 0
        fun s => reCoord ((0 : Fin m → Matrix (Fin W) (Fin W) ℂ) s.1) s.2) = 0 := by
      funext p
      cases p with
      | none => rfl
      | some s => simp [reCoord]
    rw [e, Matrix.mulVec_zero]
    ext i j
    apply Complex.ext <;> simp [ofReCoord]
  simpa [h0] using LiftReconstruct_cohLeftInv_add G a D 0

private lemma LiftReconstruct_liftSeq_add {W q : ℕ} (a : ℝ)
    (R R' : Fin q → Matrix (Fin W) (Fin W) ℂ) :
    liftSeq (a • R + R') = a • liftSeq R + liftSeq R' := by
  funext k
  unfold liftSeq
  by_cases h : k < q <;> simp [h]

private lemma LiftReconstruct_liftEAux_add {W : ℕ} (C R R' : ℕ → Matrix (Fin W) (Fin W) ℂ)
    (a : ℝ) (top : ℕ) : ∀ n,
    liftEAux C (a • R + R') top n = a • liftEAux C R top n + liftEAux C R' top n
  | 0 => by simp [liftEAux]
  | n + 1 => by
    simp only [liftEAux, LiftReconstruct_liftEAux_add C R R' a top n, Pi.add_apply,
      Pi.smul_apply, Matrix.add_mul, Matrix.smul_mul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_smul, star_trivial]
    module

private lemma LiftReconstruct_pairData_add {W : ℕ} (g z a : ℝ)
    (V R R' : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) :
    pairData g z V (a • R + R') = a • pairData g z V R + pairData g z V R' := by
  have hF : ∀ k, liftF g z V (a • R + R') k = a • liftF g z V R k + liftF g z V R' k := by
    intro k
    unfold liftF liftE
    rw [LiftReconstruct_liftSeq_add, LiftReconstruct_liftEAux_add]
    simp only [Pi.add_apply, Pi.smul_apply, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, star_trivial]
    module
  funext j
  simp only [pairData, hF, Pi.add_apply, Pi.smul_apply]
  module

private lemma LiftReconstruct_blockMat_add {W : ℕ} (a : ℝ)
    (A B C D A' B' C' D' : Matrix (Fin W) (Fin W) ℂ) :
    blockMat (a • A + A') (a • B + B') (a • C + C') (a • D + D') =
      a • blockMat A B C D + blockMat A' B' C' D' := by
  ext ⟨i, α⟩ ⟨j, β⟩
  fin_cases i <;> fin_cases j <;> simp [blockMat]

private lemma LiftReconstruct_herm_layout {m n W : ℕ} (d : Matrix (Fin m) (Fin n) ℝ)
    {V : Fin n → Matrix (Fin W) (Fin W) ℂ} (hV : ∀ i, (V i).IsHermitian) (j : Fin m) :
    (layoutBlocks d V j).IsHermitian := by
  unfold layoutBlocks Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_smul, (hV i).eq, Complex.star_def, Complex.conj_ofReal]

private lemma LiftReconstruct_herm_liftC {W q : ℕ} (g z : ℝ)
    {V : Fin q → Matrix (Fin W) (Fin W) ℂ} (hV : ∀ i, (V i).IsHermitian) (i : Fin q) :
    (liftC g z V i)ᴴ = liftC g z V i := by
  unfold liftC
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, (hV i).eq]
  simp [Complex.conj_ofReal]

private lemma LiftReconstruct_hsInner_tr {k l : Type*} [Fintype k] [Fintype l]
    (X Y : Matrix k l ℂ) :
    hsInner X Y = (Xᴴ * Y).trace.re :=
  (hsInner_reCoord X Y 0).1

private lemma LiftReconstruct_pair {W : ℕ} (A B₁ B₂ P C R₈ R₉ : Matrix (Fin W) (Fin W) ℂ)
    (hB : B₁ᴴ = B₁) (hC : Cᴴ = C) :
    hsInner (blockMat A B₁ B₂ (-Aᴴ)) (blockMat P (P * C + C * Pᴴ + C * R₉ * C - R₈) R₉ (-Pᴴ)) =
      2 * hsInner (A + B₁ * C) P + hsInner (C * B₁ * C + B₂) R₉ - hsInner B₁ R₈ := by
  have hb := blockMat_algebra Aᴴ B₂ᴴ B₁ᴴ (-Aᴴ)ᴴ P (P * C + C * Pᴴ + C * R₉ * C - R₈) R₉ (-Pᴴ)
  rw [LiftReconstruct_hsInner_tr (blockMat A B₁ B₂ (-Aᴴ)),
    (blockMat_algebra A B₁ B₂ (-Aᴴ) 0 0 0 0).2.1, hb.1, (blockMat_algebra _ _ _ _ 0 0 0 0).2.2.1]
  simp only [LiftReconstruct_hsInner_tr, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose, hB, hC]
  have k1 : (-A * -Pᴴ).trace.re = (Aᴴ * P).trace.re := by
    rw [neg_mul_neg, Matrix.trace_mul_comm, ← Matrix.conjTranspose_conjTranspose (Pᴴ * A),
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.trace_conjTranspose,
      Complex.star_def, Complex.conj_re]
  have k2 : (B₁ * (P * C)).trace = (C * B₁ * P).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have k3 : (B₁ * (C * Pᴴ)).trace.re = (C * B₁ * P).trace.re := by
    rw [← Matrix.conjTranspose_conjTranspose (B₁ * (C * Pᴴ)), Matrix.trace_conjTranspose,
      Complex.star_def, Complex.conj_re]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hB, hC]
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have k4 : (B₁ * (C * R₉ * C)).trace = (C * B₁ * C * R₉).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.trace_add, Matrix.trace_sub,
    Complex.add_re, Complex.sub_re, k1, k2, k3, k4]
  rw [show C * (B₁ * C) * R₉ = C * B₁ * C * R₉ by simp only [Matrix.mul_assoc]]
  ring

end LiftReconstructAux2

/-- (10.10) [eq:c-main-left-inverse], (G.21) [eq:c-right-inverse]: where `S_W(G) ≥ c₁ > 0` for
`G = liftLayout V`, `𝒦₀` recovers every target `Z` of the algebra (10.3) [eq:c-Lie] from its data
`R = g 𝒜* Z`. -/
theorem liftK0_liftConj {W : ℕ} {g z c₁ : ℝ} (hg : 0 < g) (hc₁ : 0 < c₁)
    {V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ} (hV : ∀ i, (V i).IsHermitian)
    (hc : c₁ ≤ coerMin (layoutBlocks liftLayout V)) {Z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hZ : Z ∈ lieOmega W) :
    liftK0 g z V (fun i => blockPart (liftConj g z V Z i) 1 0) = Z := by
  have hG := LiftReconstruct_herm_layout liftLayout hV
  obtain ⟨hZb, -⟩ := blockMat_blockPart Z 0 0 0 0
  have hZ' := hZ
  rw [← hZb, mem_lieOmega_iff] at hZ'
  obtain ⟨-, -, hD, hP⟩ := hZ'
  have hL := cohMap_liftLayout (z := z) hg hV hZ
  rw [Complex.coe_smul] at hL
  have hKP : liftKP g z V (fun i => blockPart (liftConj g z V Z i) 1 0) = blockPart Z 0 0 := by
    unfold liftKP
    rw [Complex.coe_smul, ← LiftReconstruct_cohLeftInv_smul, ← hL]
    exact (cohLeftInv_spec hG hc₁ hc).1 _ hP
  obtain ⟨htop, hrec⟩ := liftConj_recursion (g := g) (z := z) hV hZ
  have h999 : liftConj g z V Z 999 = Z := htop 999 rfl
  have h998 := (hrec 999 998 rfl).2.2
  unfold liftK0
  rw [hKP]
  simp only []
  rw [h998, h999, sub_sub_cancel, ← hD, hZb]

/-- (G.20) [eq:c-reconstruction] and (10.25) [eq:c-K0-adjoint]: `R ↦ 𝒦₀ R` is real-linear and,
where `S_W(G) ≥ c₁ > 0`, maps Hermitian data into the algebra (10.3) [eq:c-Lie]; for
`M = [[A, B₁], [B₂, -A*]]` in the algebra,
`⟨M, 𝒦₀ R⟩ = 2 ⟨A + B₁ C_q, 𝒦_P R⟩ + ⟨C_q B₁ C_q + B₂, R_q⟩ - ⟨B₁, R_{q-1}⟩`. -/
theorem liftK0_spec {W : ℕ} {g z c₁ : ℝ} (hc₁ : 0 < c₁) {V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ i, (V i).IsHermitian) (hc : c₁ ≤ coerMin (layoutBlocks liftLayout V)) :
    (∀ (a : ℝ) (R R' : Fin 1000 → Matrix (Fin W) (Fin W) ℂ),
      liftK0 g z V (a • R + R') = (a : ℂ) • liftK0 g z V R + liftK0 g z V R') ∧
      (∀ R : Fin 1000 → Matrix (Fin W) (Fin W) ℂ, (∀ i, (R i).IsHermitian) →
        liftK0 g z V R ∈ lieOmega W) ∧
      ∀ (R : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ),
        M ∈ lieOmega W → hsInner M (liftK0 g z V R) =
          2 * hsInner (blockPart M 0 0 + blockPart M 0 1 * liftC g z V 999) (liftKP g z V R) +
            hsInner (liftC g z V 999 * blockPart M 0 1 * liftC g z V 999 + blockPart M 1 0)
              (R 999) -
            hsInner (blockPart M 0 1) (R 998) := by
  have hG := LiftReconstruct_herm_layout liftLayout hV
  have hJ := cohLeftInv_spec hG hc₁ hc
  have hC := LiftReconstruct_herm_liftC g z hV 999
  have hKP : ∀ (a : ℝ) (R R' : Fin 1000 → Matrix (Fin W) (Fin W) ℂ),
      liftKP g z V (a • R + R') = a • liftKP g z V R + liftKP g z V R' := by
    intro a R R'
    unfold liftKP
    rw [Complex.coe_smul, Complex.coe_smul, Complex.coe_smul, LiftReconstruct_pairData_add,
      LiftReconstruct_cohLeftInv_add, smul_add, smul_comm]
  refine ⟨?_, ?_, ?_⟩
  · intro a R R'
    rw [Complex.coe_smul]
    unfold liftK0
    rw [hKP, ← LiftReconstruct_blockMat_add]
    congr 1 <;>
      simp only [Pi.add_apply, Pi.smul_apply, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, star_trivial] <;>
      module
  · intro R hR
    unfold liftK0
    rw [mem_lieOmega_iff]
    refine ⟨?_, hR 999, rfl, ?_⟩
    · unfold Matrix.IsHermitian
      simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hC, (hR 998).eq, (hR 999).eq, Matrix.mul_assoc]
      abel
    · unfold liftKP
      rw [Matrix.trace_smul, smul_eq_mul, Complex.im_ofReal_mul, (hJ.2.1 _).1, mul_zero]
  · intro R M hM
    obtain ⟨hMb, -⟩ := blockMat_blockPart M 0 0 0 0
    rw [← hMb, mem_lieOmega_iff] at hM
    obtain ⟨hB, -, hD, -⟩ := hM
    unfold liftK0
    conv_lhs => rw [← hMb, hD]
    exact LiftReconstruct_pair _ _ _ _ _ _ _ hB.eq hC

end LSBA
