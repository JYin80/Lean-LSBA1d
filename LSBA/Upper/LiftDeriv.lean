import LSBA.Upper.LiftSize
import LSBA.Upper.LiftDataDeriv
import LSBA.Gauss.HermCoord

/-!
# Smoothness and input derivatives of the general lift

In the standard coordinates `ω` of the inputs (`V = gueBlock ω`), the general lift
`Y = hermCoord X` is `C^∞` on the open set `{S_W(G) > 0}`, `G = liftLayout V`; and on the
cutoff neighbourhood `S_W(G) ≥ c₁`, `max_i ‖V_i‖ ≤ K₁`, `|E| ≤ E₀`, its Jacobian satisfies
`‖∇_V X‖²_HS ≤ C W max{g⁻², g⁴} ‖M‖²`, which is (10.26) [eq:c-lift-cost]; the proof goes through
(10.22) [eq:c-lift-derivative], (10.23) [eq:c-J-bound] and (10.24) [eq:c-KP-bound]
(Section 10 [sec:compact-proof]).
-/

open Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

section LiftDerivSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every entry of the matrix family `F` is `C^∞` on `U`. -/
private def LiftDeriv_Sm {m n 𝕜 : Type*} [NormedRing 𝕜] [NormedAlgebra ℝ 𝕜] (U : Set E)
    (F : E → Matrix m n 𝕜) : Prop :=
  ∀ a b, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => F x a b) U

/-- Every entry of the vector family `v` is `C^∞` on `U`. -/
private def LiftDeriv_SmV {ι : Type*} (U : Set E) (v : E → ι → ℝ) : Prop :=
  ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => v x i) U

variable {U : Set E} {m n l 𝕜 : Type*} [NormedRing 𝕜] [NormedAlgebra ℝ 𝕜]

private lemma LiftDeriv_Sm_const (A : Matrix m n 𝕜) : LiftDeriv_Sm U (fun _ => A) :=
  fun _ _ => contDiffOn_const

private lemma LiftDeriv_Sm_add {F G : E → Matrix m n 𝕜} (hF : LiftDeriv_Sm U F)
    (hG : LiftDeriv_Sm U G) : LiftDeriv_Sm U (fun x => F x + G x) :=
  fun a b => (hF a b).add (hG a b)

private lemma LiftDeriv_Sm_sub {F G : E → Matrix m n 𝕜} (hF : LiftDeriv_Sm U F)
    (hG : LiftDeriv_Sm U G) : LiftDeriv_Sm U (fun x => F x - G x) :=
  fun a b => (hF a b).sub (hG a b)

private lemma LiftDeriv_Sm_neg {F : E → Matrix m n 𝕜} (hF : LiftDeriv_Sm U F) :
    LiftDeriv_Sm U (fun x => -F x) :=
  fun a b => (hF a b).neg

private lemma LiftDeriv_Sm_smul {F : E → Matrix m n 𝕜} (c : 𝕜) (hF : LiftDeriv_Sm U F) :
    LiftDeriv_Sm U (fun x => c • F x) :=
  fun a b => by simpa only [Matrix.smul_apply, smul_eq_mul] using contDiffOn_const.mul (hF a b)

private lemma LiftDeriv_Sm_mul [Fintype n] {F : E → Matrix m n 𝕜} {G : E → Matrix n l 𝕜}
    (hF : LiftDeriv_Sm U F) (hG : LiftDeriv_Sm U G) : LiftDeriv_Sm U (fun x => F x * G x) :=
  fun a b => by
    simp only [Matrix.mul_apply]
    exact ContDiffOn.sum fun k _ => (hF a k).mul (hG k b)

private lemma LiftDeriv_Sm_transpose {F : E → Matrix m n 𝕜} (hF : LiftDeriv_Sm U F) :
    LiftDeriv_Sm U (fun x => (F x)ᵀ) :=
  fun a b => hF b a

private lemma LiftDeriv_Sm_conjTranspose {F : E → Matrix m n ℂ} (hF : LiftDeriv_Sm U F) :
    LiftDeriv_Sm U (fun x => (F x)ᴴ) :=
  fun a b => by
    simp only [Matrix.conjTranspose_apply, Complex.star_def]
    exact Complex.conjCLE.toContinuousLinearMap.contDiff.comp_contDiffOn (hF b a)

private lemma LiftDeriv_Sm_sum {ι : Type*} (s : Finset ι) {F : ι → E → Matrix m n 𝕜}
    (hF : ∀ i, LiftDeriv_Sm U (F i)) : LiftDeriv_Sm U (fun x => ∑ i ∈ s, F i x) :=
  fun a b => by
    simp only [Matrix.sum_apply]
    exact ContDiffOn.sum fun i _ => hF i a b

private lemma LiftDeriv_det [Fintype n] [DecidableEq n] {F : E → Matrix n n ℝ}
    (hF : LiftDeriv_Sm U F) : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (F x).det) U := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => hF _ _)

private lemma LiftDeriv_Sm_inv [Fintype n] [DecidableEq n] {F : E → Matrix n n ℝ}
    (hF : LiftDeriv_Sm U F) (hdet : ∀ x ∈ U, (F x).det ≠ 0) :
    LiftDeriv_Sm U (fun x => (F x)⁻¹) := by
  intro a b
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  refine ((LiftDeriv_det hF).inv hdet).mul (LiftDeriv_det fun c d => ?_)
  simp only [Matrix.updateRow_apply]
  by_cases h : c = b
  · simp only [h, ite_true]; exact contDiffOn_const
  · simp only [h, ite_false]; exact hF c d

private lemma LiftDeriv_SmV_mulVec [Fintype n] {F : E → Matrix m n ℝ} {v : E → n → ℝ}
    (hF : LiftDeriv_Sm U F) (hv : LiftDeriv_SmV U v) :
    LiftDeriv_SmV U (fun x => F x *ᵥ v x) :=
  fun a => by
    simp only [Matrix.mulVec, dotProduct]
    exact ContDiffOn.sum fun k _ => (hF a k).mul (hv k)

private lemma LiftDeriv_Sm_ofReCoord {v : E → Fin 2 × m × n → ℝ} (hv : LiftDeriv_SmV U v) :
    LiftDeriv_Sm U (fun x => (ofReCoord (v x) : Matrix m n ℂ)) :=
  fun a b => by
    simp only [ofReCoord, Matrix.of_apply, Complex.mk_eq_add_mul_I]
    exact (Complex.ofRealCLM.contDiff.comp_contDiffOn (hv _)).add
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn (hv _)).mul contDiffOn_const)

private lemma LiftDeriv_SmV_reCoord {F : E → Matrix m n ℂ} (hF : LiftDeriv_Sm U F) :
    LiftDeriv_SmV U (fun x => reCoord (F x)) :=
  fun p => by
    by_cases h : p.1 = 0
    · simp only [reCoord, h, ite_true]
      exact Complex.reCLM.contDiff.comp_contDiffOn (hF _ _)
    · simp only [reCoord, h, ite_false]
      exact Complex.imCLM.contDiff.comp_contDiffOn (hF _ _)

end LiftDerivSmooth

section LiftDerivSmoothLift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E}

private lemma LiftDeriv_Sm_gue {W L : ℕ} (U : Set (Ω W L)) (i : Fin L) :
    LiftDeriv_Sm U (fun x => gueBlock W L x i) := by
  have hc : ∀ p, ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Ω W L => ((x p : ℝ) : ℂ)) U := fun p =>
    (Complex.ofRealCLM.contDiff.comp
      (contDiff_apply ℝ (fun _ : Fin L × Fin W × Fin W => ℝ) p)).contDiffOn
  intro α β
  simp only [gueBlock, Matrix.of_apply]
  by_cases h1 : α = β
  · simp only [h1, ite_true]
    exact (hc _).div_const _
  · by_cases h2 : α < β
    · simp only [h1, h2, ite_true, ite_false]
      exact ((hc _).add (contDiffOn_const.mul (hc _))).div_const _
    · simp only [h1, h2, ite_false]
      exact ((hc _).sub (contDiffOn_const.mul (hc _))).div_const _

private lemma LiftDeriv_Sm_liftC {W q : ℕ} (g z : ℝ) {V : E → Fin q → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ i, LiftDeriv_Sm U (fun x => V x i)) (i : Fin q) :
    LiftDeriv_Sm U (fun x => liftC g z (V x) i) :=
  LiftDeriv_Sm_sub (LiftDeriv_Sm_const _) (LiftDeriv_Sm_smul _ (hV i))

private lemma LiftDeriv_Sm_liftSeq {W q : ℕ} {R : E → Fin q → Matrix (Fin W) (Fin W) ℂ}
    (hR : ∀ i, LiftDeriv_Sm U (fun x => R x i)) (k : ℕ) :
    LiftDeriv_Sm U (fun x => liftSeq (R x) k) := by
  by_cases h : k < q
  · simp only [liftSeq, h, dite_true]; exact hR _
  · simp only [liftSeq, h, dite_false]; exact LiftDeriv_Sm_const _

private lemma LiftDeriv_Sm_liftEAux {W : ℕ} {C R : E → ℕ → Matrix (Fin W) (Fin W) ℂ}
    (hC : ∀ k, LiftDeriv_Sm U (fun x => C x k)) (hR : ∀ k, LiftDeriv_Sm U (fun x => R x k))
    (top : ℕ) : ∀ n, LiftDeriv_Sm U (fun x => liftEAux (C x) (R x) top n)
  | 0 => by simp only [liftEAux]; exact LiftDeriv_Sm_const _
  | n + 1 => by
    simp only [liftEAux]
    exact LiftDeriv_Sm_sub (LiftDeriv_Sm_neg (LiftDeriv_Sm_mul (hR _) (hC _)))
      (LiftDeriv_Sm_conjTranspose (LiftDeriv_Sm_liftEAux hC hR top n))

private lemma LiftDeriv_Sm_pairData {W : ℕ} (g z : ℝ)
    {V R : E → Fin 1000 → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ i, LiftDeriv_Sm U (fun x => V x i)) (hR : ∀ i, LiftDeriv_Sm U (fun x => R x i))
    (j : Fin 128) : LiftDeriv_Sm U (fun x => pairData g z (V x) (R x) j) := by
  have hC := LiftDeriv_Sm_liftSeq (LiftDeriv_Sm_liftC g z hV)
  have hS := LiftDeriv_Sm_liftSeq hR
  have hF : ∀ k, LiftDeriv_Sm U (fun x => liftF g z (V x) (R x) k) := by
    intro k
    unfold liftF liftE
    have hE := LiftDeriv_Sm_liftEAux hC hS (1000 - 1) (1000 - 1 - k)
    exact LiftDeriv_Sm_sub (LiftDeriv_Sm_add (LiftDeriv_Sm_add (LiftDeriv_Sm_add
      (LiftDeriv_Sm_mul hE (hC k)) (LiftDeriv_Sm_mul (hC k) (LiftDeriv_Sm_conjTranspose hE)))
      (LiftDeriv_Sm_mul (LiftDeriv_Sm_mul (hC k) (hS k)) (hC k))) (hS (k + 1))) (hS (k - 1))
  unfold pairData
  exact LiftDeriv_Sm_sub (hF _) (hF _)

private lemma LiftDeriv_Sm_layout {W m n : ℕ} (d : Matrix (Fin m) (Fin n) ℝ)
    {V : E → Fin n → Matrix (Fin W) (Fin W) ℂ} (hV : ∀ i, LiftDeriv_Sm U (fun x => V x i))
    (j : Fin m) : LiftDeriv_Sm U (fun x => layoutBlocks d (V x) j) :=
  LiftDeriv_Sm_sum _ fun i => LiftDeriv_Sm_smul _ (hV i)

private lemma LiftDeriv_Sm_cohRealMat {W m : ℕ} {G : E → Fin m → Matrix (Fin W) (Fin W) ℂ}
    (hG : ∀ j, LiftDeriv_Sm U (fun x => G x j)) :
    LiftDeriv_Sm U (fun x => cohRealMat (G x)) := by
  intro p r
  cases p with
  | none => exact contDiffOn_const
  | some s =>
    simp only [cohRealMat, Matrix.of_apply, Option.elim]
    refine LiftDeriv_SmV_reCoord (F := fun x => cohMap (G x) (ofReCoord (Pi.single r 1)) s.1)
      ?_ s.2
    exact LiftDeriv_Sm_add (LiftDeriv_Sm_mul (hG _) (LiftDeriv_Sm_const _))
      (LiftDeriv_Sm_mul (LiftDeriv_Sm_const _) (hG _))

private lemma LiftDeriv_SmV_data {W m : ℕ} {D : E → Fin m → Matrix (Fin W) (Fin W) ℂ}
    (hD : ∀ j, LiftDeriv_Sm U (fun x => D x j)) :
    LiftDeriv_SmV U (fun x (p : Option (Fin m × Fin 2 × Fin W × Fin W)) =>
      Option.elim p 0 fun s => reCoord (D x s.1) s.2) := by
  intro p
  cases p with
  | none => exact contDiffOn_const
  | some s => exact LiftDeriv_SmV_reCoord (hD s.1) s.2

private lemma LiftDeriv_Sm_cohLeftInv {W m : ℕ} {G D : E → Fin m → Matrix (Fin W) (Fin W) ℂ}
    (hG : ∀ j, LiftDeriv_Sm U (fun x => G x j)) (hD : ∀ j, LiftDeriv_Sm U (fun x => D x j))
    (hdet : ∀ x ∈ U, ((cohRealMat (G x))ᵀ * cohRealMat (G x)).det ≠ 0) :
    LiftDeriv_Sm U (fun x => cohLeftInv (G x) (D x)) := by
  have hA := LiftDeriv_Sm_cohRealMat hG
  have hL : LiftDeriv_Sm U (fun x => lsqInv (cohRealMat (G x))) :=
    LiftDeriv_Sm_mul (LiftDeriv_Sm_inv (LiftDeriv_Sm_mul (LiftDeriv_Sm_transpose hA) hA) hdet)
      (LiftDeriv_Sm_transpose hA)
  exact LiftDeriv_Sm_ofReCoord (LiftDeriv_SmV_mulVec hL (LiftDeriv_SmV_data hD))

private lemma LiftDeriv_Sm_blockMat {W : ℕ} {A B C D : E → Matrix (Fin W) (Fin W) ℂ}
    (hA : LiftDeriv_Sm U A) (hB : LiftDeriv_Sm U B) (hC : LiftDeriv_Sm U C)
    (hD : LiftDeriv_Sm U D) : LiftDeriv_Sm U (fun x => blockMat (A x) (B x) (C x) (D x)) := by
  rintro ⟨a, α⟩ ⟨b, β⟩
  fin_cases a <;> fin_cases b
  · exact hA α β
  · exact hB α β
  · exact hC α β
  · exact hD α β

private lemma LiftDeriv_Sm_liftK0 {W : ℕ} (g z : ℝ)
    {V R : E → Fin 1000 → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ i, LiftDeriv_Sm U (fun x => V x i)) (hR : ∀ i, LiftDeriv_Sm U (fun x => R x i))
    (hdet : ∀ x ∈ U, ((cohRealMat (layoutBlocks liftLayout (V x)))ᵀ *
      cohRealMat (layoutBlocks liftLayout (V x))).det ≠ 0) :
    LiftDeriv_Sm U (fun x => liftK0 g z (V x) (R x)) := by
  have hP : LiftDeriv_Sm U (fun x => liftKP g z (V x) (R x)) :=
    LiftDeriv_Sm_smul _ (LiftDeriv_Sm_cohLeftInv (LiftDeriv_Sm_layout liftLayout hV)
      (LiftDeriv_Sm_pairData g z hV hR) hdet)
  have hC := LiftDeriv_Sm_liftC g z hV 999
  have hPh := LiftDeriv_Sm_conjTranspose hP
  exact LiftDeriv_Sm_blockMat hP (LiftDeriv_Sm_sub (LiftDeriv_Sm_add (LiftDeriv_Sm_add
    (LiftDeriv_Sm_mul hP hC) (LiftDeriv_Sm_mul hC hPh))
    (LiftDeriv_Sm_mul (LiftDeriv_Sm_mul hC (hR 999)) hC)) (hR 998)) (hR 999)
    (LiftDeriv_Sm_neg hPh)

private lemma LiftDeriv_hsInner_smooth {k l : Type*} [Fintype k] [Fintype l] (M : Matrix k l ℂ)
    {F : E → Matrix k l ℂ} (hF : LiftDeriv_Sm U F) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => hsInner M (F x)) U := by
  unfold hsInner
  exact ContDiffOn.sum fun a _ => ContDiffOn.sum fun b _ =>
    Complex.reCLM.contDiff.comp_contDiffOn (contDiffOn_const.mul (hF a b))

end LiftDerivSmoothLift

section LiftDerivTarget1

/-- The layout of Hermitian inputs with real coefficients is Hermitian. -/
private lemma LiftDeriv_herm_layout {m n W : ℕ} (d : Matrix (Fin m) (Fin n) ℝ)
    {V : Fin n → Matrix (Fin W) (Fin W) ℂ} (hV : ∀ i, (V i).IsHermitian) (j : Fin m) :
    (layoutBlocks d V j).IsHermitian := by
  unfold layoutBlocks Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_smul, (hV i).eq, Complex.star_def, Complex.conj_ofReal]

/-- The standard coordinates of the general lift:
`Y_{(i, α)} = √W · √2 g ⟨M, 𝒦₀(ι_i H_α)⟩`. -/
private lemma LiftDeriv_hermCoord_liftField {W : ℕ} (g z : ℝ)
    (V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (p : Fin 1000 × Fin W × Fin W) :
    hermCoord W 1000 (liftField g z V M) p = Real.sqrt W *
      (Real.sqrt 2 * g * hsInner M (liftK0 g z V (Pi.single p.1 (hermBasis W p.2)))) := by
  unfold hermCoord liftField
  congr 1
  simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul,
    trace_hermBasis_mul, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Complex.ofReal_re]

/-- Where `S_W(G) > 0`, the Gram matrix `AᵀA` of the realified map is invertible. -/
private lemma LiftDeriv_det_ne {W : ℕ} {V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ i, (V i).IsHermitian) (hS : 0 < coerMin (layoutBlocks liftLayout V)) :
    ((cohRealMat (layoutBlocks liftLayout V))ᵀ *
      cohRealMat (layoutBlocks liftLayout V)).det ≠ 0 := by
  have hA := (cohLeftInv_spec (LiftDeriv_herm_layout liftLayout hV) hS le_rfl).2.2
  have h1 := (lsqInv_spec (lt_min hS one_pos) hA).1
  rw [lsqInv, Matrix.mul_assoc] at h1
  exact (Matrix.isUnit_det_of_left_inverse h1).ne_zero

/-- `ω ↦ S_W(G(ω))` is continuous. -/
private lemma LiftDeriv_continuous_coerMin (W : ℕ) :
    Continuous fun ω : Ω W 1000 => coerMin (layoutBlocks liftLayout (gueBlock W 1000 ω)) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  set G : Ω W 1000 → Fin 128 → Matrix (Fin W) (Fin W) ℂ :=
    fun x => layoutBlocks liftLayout (gueBlock W 1000 x) with hGdef
  set h : Ω W 1000 → ℝ := fun x => 2 * Real.sqrt (∑ j, hsSq (G x j - G x₀ j)) with hhdef
  have hsm : ∀ j, LiftDeriv_Sm (Set.univ : Set (Ω W 1000)) (fun x => G x j - G x₀ j) :=
    fun j => LiftDeriv_Sm_sub (LiftDeriv_Sm_layout liftLayout
      (fun i => LiftDeriv_Sm_gue Set.univ i) j) (LiftDeriv_Sm_const _)
  have hcont : Continuous h := by
    refine continuous_const.mul (Real.continuous_sqrt.comp ?_)
    refine continuous_finsetSum _ fun j _ => ?_
    unfold hsSq
    refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
    exact (continuous_norm.comp (continuousOn_univ.1 (hsm j a b).continuousOn)).pow 2
  have h0 : h x₀ = 0 := by simp [h, hsSq]
  unfold ContinuousAt
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero_norm (a := h) (fun x => ?_) ?_)
  · rw [norm_norm, Real.norm_eq_abs]
    exact abs_coerMin_sub_le (G x) (G x₀)
  · have := hcont.tendsto x₀
    rwa [h0] at this

end LiftDerivTarget1

section LiftDerivAlg

private lemma LiftDeriv_hsSq_nonneg {k l : Type*} [Fintype k] [Fintype l] (A : Matrix k l ℂ) :
    0 ≤ hsSq A := by
  unfold hsSq; positivity

private lemma LiftDeriv_hsSq_add_le {k l : Type*} [Fintype k] [Fintype l] (A B : Matrix k l ℂ) :
    hsSq (A + B) ≤ 2 * hsSq A + 2 * hsSq B := by
  unfold hsSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  have h := norm_add_le (A a b) (B a b)
  have h0 : 0 ≤ ‖A a b + B a b‖ := norm_nonneg _
  simp only [Matrix.add_apply]
  nlinarith [sq_nonneg (‖A a b‖ - ‖B a b‖), norm_nonneg (A a b), norm_nonneg (B a b)]

private lemma LiftDeriv_hsSq_neg {k l : Type*} [Fintype k] [Fintype l] (A : Matrix k l ℂ) :
    hsSq (-A) = hsSq A := by
  simp [hsSq]

private lemma LiftDeriv_hsSq_sub_le {k l : Type*} [Fintype k] [Fintype l] (A B : Matrix k l ℂ) :
    hsSq (A - B) ≤ 2 * hsSq A + 2 * hsSq B := by
  rw [sub_eq_add_neg, ← LiftDeriv_hsSq_neg B]
  exact LiftDeriv_hsSq_add_le A (-B)

private lemma LiftDeriv_hsSq_conjTranspose {n : Type*} [Fintype n] (A : Matrix n n ℂ) :
    hsSq Aᴴ = hsSq A := by
  simp only [hsSq, Matrix.conjTranspose_apply, norm_star]
  exact Finset.sum_comm

private lemma LiftDeriv_hsSq_smul {k l : Type*} [Fintype k] [Fintype l] (c : ℂ)
    (A : Matrix k l ℂ) : hsSq (c • A) = ‖c‖ ^ 2 * hsSq A := by
  simp [hsSq, mul_pow, Finset.mul_sum]

/-- `‖A B‖² ≤ |A|²_op ‖B‖²`. -/
private lemma LiftDeriv_hsSq_mul_le {n : Type*} [Fintype n] (A B : Matrix n n ℂ) :
    hsSq (A * B) ≤ ‖A‖ ^ 2 * hsSq B := by
  have hcol : ∀ b : n, ∑ a, ‖(A * B) a b‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ a, ‖B a b‖ ^ 2 := by
    intro b
    have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 (fun a => B a b))
    have h1 : ‖(EuclideanSpace.equiv n ℂ).symm (A *ᵥ (fun a => B a b))‖ ^ 2 =
        ∑ a, ‖(A * B) a b‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      rfl
    have h2 : ‖(WithLp.toLp 2 (fun a => B a b) : EuclideanSpace ℂ n)‖ ^ 2 = ∑ a, ‖B a b‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
    have h0 : 0 ≤ ‖(EuclideanSpace.equiv n ℂ).symm (A *ᵥ (fun a => B a b))‖ := norm_nonneg _
    rw [← h1, ← h2, ← mul_pow]
    exact pow_le_pow_left₀ h0 h 2
  unfold hsSq
  rw [Finset.sum_comm, Finset.sum_comm (f := fun a b => ‖B a b‖ ^ 2), Finset.mul_sum]
  exact Finset.sum_le_sum fun b _ => hcol b

/-- `‖B A‖² ≤ |A|²_op ‖B‖²`. -/
private lemma LiftDeriv_hsSq_mul_le' {n : Type*} [Fintype n] (A B : Matrix n n ℂ) :
    hsSq (B * A) ≤ ‖A‖ ^ 2 * hsSq B := by
  rw [← LiftDeriv_hsSq_conjTranspose, Matrix.conjTranspose_mul,
    ← Matrix.l2_opNorm_conjTranspose A, ← LiftDeriv_hsSq_conjTranspose B]
  exact LiftDeriv_hsSq_mul_le _ _

private lemma LiftDeriv_hsInner_tr {k l : Type*} [Fintype k] [Fintype l] (X Y : Matrix k l ℂ) :
    hsInner X Y = (Xᴴ * Y).trace.re :=
  (hsInner_reCoord X Y 0).1

private lemma LiftDeriv_hsInner_add_right {k l : Type*} [Fintype k] [Fintype l]
    (X A B : Matrix k l ℂ) : hsInner X (A + B) = hsInner X A + hsInner X B := by
  simp only [hsInner, Matrix.add_apply, mul_add, Complex.add_re, Finset.sum_add_distrib]

private lemma LiftDeriv_hsInner_add_left {k l : Type*} [Fintype k] [Fintype l]
    (A B X : Matrix k l ℂ) : hsInner (A + B) X = hsInner A X + hsInner B X := by
  simp only [hsInner, Matrix.add_apply, star_add, add_mul, Complex.add_re, Finset.sum_add_distrib]

private lemma LiftDeriv_hsInner_neg_right {k l : Type*} [Fintype k] [Fintype l]
    (X A : Matrix k l ℂ) : hsInner X (-A) = -hsInner X A := by
  simp only [hsInner, Matrix.neg_apply, mul_neg, Complex.neg_re, Finset.sum_neg_distrib]

private lemma LiftDeriv_hsInner_neg_left {k l : Type*} [Fintype k] [Fintype l]
    (A X : Matrix k l ℂ) : hsInner (-A) X = -hsInner A X := by
  simp only [hsInner, Matrix.neg_apply, star_neg, neg_mul, Complex.neg_re, Finset.sum_neg_distrib]

private lemma LiftDeriv_hsInner_sub_right {k l : Type*} [Fintype k] [Fintype l]
    (X A B : Matrix k l ℂ) : hsInner X (A - B) = hsInner X A - hsInner X B := by
  rw [sub_eq_add_neg, LiftDeriv_hsInner_add_right, LiftDeriv_hsInner_neg_right, ← sub_eq_add_neg]

private lemma LiftDeriv_hsInner_sub_left {k l : Type*} [Fintype k] [Fintype l]
    (A B X : Matrix k l ℂ) : hsInner (A - B) X = hsInner A X - hsInner B X := by
  rw [sub_eq_add_neg, LiftDeriv_hsInner_add_left, LiftDeriv_hsInner_neg_left, ← sub_eq_add_neg]

private lemma LiftDeriv_hsInner_smul_right {k l : Type*} [Fintype k] [Fintype l]
    (X A : Matrix k l ℂ) (r : ℝ) : hsInner X ((r : ℂ) • A) = r * hsInner X A := by
  simp only [hsInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [mul_left_comm, Complex.re_ofReal_mul]

private lemma LiftDeriv_hsInner_smul_left {k l : Type*} [Fintype k] [Fintype l]
    (A X : Matrix k l ℂ) (r : ℝ) : hsInner ((r : ℂ) • A) X = r * hsInner A X := by
  simp only [hsInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, star_mul',
    Complex.star_def, Complex.conj_ofReal]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [mul_assoc, Complex.re_ofReal_mul]

private lemma LiftDeriv_hsInner_sum_right {k l ι : Type*} [Fintype k] [Fintype l]
    (X : Matrix k l ℂ) (s : Finset ι) (A : ι → Matrix k l ℂ) :
    hsInner X (∑ x ∈ s, A x) = ∑ x ∈ s, hsInner X (A x) := by
  simp only [LiftDeriv_hsInner_tr, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]

private lemma LiftDeriv_hsInner_comm {k l : Type*} [Fintype k] [Fintype l] (A B : Matrix k l ℂ) :
    hsInner A B = hsInner B A := by
  simp only [hsInner]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Complex.star_def]
  rw [← Complex.conj_re, map_mul, Complex.conj_conj, mul_comm]

/-- `⟨X, P C⟩ = ⟨X C*, P⟩`. -/
private lemma LiftDeriv_hsInner_mul_right {n : Type*} [Fintype n] (X P C : Matrix n n ℂ) :
    hsInner X (P * C) = hsInner (X * Cᴴ) P := by
  rw [LiftDeriv_hsInner_tr, LiftDeriv_hsInner_tr, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc, Matrix.trace_mul_comm,
    Matrix.mul_assoc]

/-- `⟨X, C P⟩ = ⟨C* X, P⟩`. -/
private lemma LiftDeriv_hsInner_mul_left {n : Type*} [Fintype n] (X C P : Matrix n n ℂ) :
    hsInner X (C * P) = hsInner (Cᴴ * X) P := by
  rw [LiftDeriv_hsInner_tr, LiftDeriv_hsInner_tr, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- `⟨X, P*⟩ = ⟨X*, P⟩`. -/
private lemma LiftDeriv_hsInner_conj {n : Type*} [Fintype n] (X P : Matrix n n ℂ) :
    hsInner X Pᴴ = hsInner Xᴴ P := by
  rw [LiftDeriv_hsInner_tr, LiftDeriv_hsInner_tr, Matrix.conjTranspose_conjTranspose,
    ← Matrix.conjTranspose_mul, Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re,
    Matrix.trace_mul_comm]

/-- `‖Σ_k c_k H_k‖² = Σ_k c_k²` for real `c_k`. -/
private lemma LiftDeriv_hsSq_basis (W : ℕ) (c : Fin W × Fin W → ℝ) :
    hsSq (∑ k, ((c k : ℝ) : ℂ) • hermBasis W k) = ∑ k, c k ^ 2 := by
  have hon : ∀ k l, hsInner (hermBasis W k) (hermBasis W l) = if k = l then 1 else 0 := by
    intro k l
    rw [LiftDeriv_hsInner_tr, (hermBasis_isHermitian W k).eq, trace_hermBasis_mul]
    split_ifs <;> simp
  rw [← (hsInner_reCoord (∑ k, ((c k : ℝ) : ℂ) • hermBasis W k) 0 0).2.1,
    LiftDeriv_hsInner_sum_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LiftDeriv_hsInner_smul_right, LiftDeriv_hsInner_comm, LiftDeriv_hsInner_sum_right]
  simp only [LiftDeriv_hsInner_smul_right, hon, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  ring

end LiftDerivAlg

section LiftDerivCoord

/-- The real coordinates `(0, reCoord D_j)` of an array of `m` matrices. -/
private def LiftDeriv_dv {m W : ℕ} (D : Fin m → Matrix (Fin W) (Fin W) ℂ) :
    Option (Fin m × Fin 2 × Fin W × Fin W) → ℝ :=
  fun p => Option.elim p 0 fun s => reCoord (D s.1) s.2

/-- The array of matrices whose real coordinates are those of `u` (trace slot dropped). -/
private def LiftDeriv_arr {m W : ℕ} (u : Option (Fin m × Fin 2 × Fin W × Fin W) → ℝ) :
    Fin m → Matrix (Fin W) (Fin W) ℂ :=
  fun j => ofReCoord fun r => u (some (j, r))

/-- The derivative `x ↦ (0, 𝓛_{G'} x)` of the realified map along the layout `G'`. -/
private def LiftDeriv_dA {m W : ℕ} (G' : Fin m → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Option (Fin m × Fin 2 × Fin W × Fin W)) (Fin 2 × Fin W × Fin W) ℝ :=
  Matrix.of fun p r => Option.elim p 0 fun s =>
    reCoord (cohMap G' (ofReCoord (Pi.single r 1)) s.1) s.2

private lemma LiftDeriv_ofReCoord_add {k l : Type*} (a : ℝ) (x y : Fin 2 × k × l → ℝ) :
    (ofReCoord (a • x + y) : Matrix k l ℂ) = a • ofReCoord x + ofReCoord y := by
  ext i j
  apply Complex.ext <;> simp [ofReCoord]

private lemma LiftDeriv_reCoord_add {k l : Type*} (a : ℝ) (A B : Matrix k l ℂ) :
    reCoord (a • A + B) = a • reCoord A + reCoord B := by
  funext p
  by_cases h : p.1 = 0 <;> simp [reCoord, h]

private lemma LiftDeriv_cohMap_add {m W : ℕ} (G : Fin m → Matrix (Fin W) (Fin W) ℂ)
    (a : ℝ) (P Q : Matrix (Fin W) (Fin W) ℂ) :
    cohMap G (a • P + Q) = a • cohMap G P + cohMap G Q := by
  funext j
  simp only [cohMap, Pi.add_apply, Pi.smul_apply, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, star_trivial, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_add]
  abel

private lemma LiftDeriv_sum_sq_ofReCoord {k l : Type*} [Fintype k] [Fintype l]
    (x : Fin 2 × k × l → ℝ) : ∑ r, x r ^ 2 = hsSq (ofReCoord x : Matrix k l ℂ) := by
  obtain ⟨-, h2, -, -, h5⟩ := hsInner_reCoord (ofReCoord x : Matrix k l ℂ) (ofReCoord x) 0
  rw [← h2, ← h5, (hsInner_reCoord (0 : Matrix k l ℂ) 0 x).2.2.2.1]
  simp only [sq]

private lemma LiftDeriv_sum_sq_reCoord {k l : Type*} [Fintype k] [Fintype l]
    (A : Matrix k l ℂ) : ∑ p, reCoord A p ^ 2 = hsSq A := by
  rw [LiftDeriv_sum_sq_ofReCoord, (hsInner_reCoord A A 0).2.2.1]

private lemma LiftDeriv_sum_sq_dv {m W : ℕ} (D : Fin m → Matrix (Fin W) (Fin W) ℂ) :
    ∑ p, LiftDeriv_dv D p ^ 2 = ∑ j, hsSq (D j) := by
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [LiftDeriv_dv, Option.elim_none, Option.elim_some]
  rw [sq, zero_mul, zero_add]
  exact Finset.sum_congr rfl fun j _ => LiftDeriv_sum_sq_reCoord _

private lemma LiftDeriv_hsInner_ofReCoord {k l : Type*} [Fintype k] [Fintype l]
    (X : Matrix k l ℂ) (v : Fin 2 × k × l → ℝ) :
    hsInner X (ofReCoord v) = reCoord X ⬝ᵥ v := by
  rw [← (hsInner_reCoord X (ofReCoord v) 0).2.2.2.2, (hsInner_reCoord X X v).2.2.2.1]
  rfl

private lemma LiftDeriv_dot_dv {m W : ℕ} (u : Option (Fin m × Fin 2 × Fin W × Fin W) → ℝ)
    (D : Fin m → Matrix (Fin W) (Fin W) ℂ) :
    u ⬝ᵥ LiftDeriv_dv D = ∑ j, hsInner (LiftDeriv_arr u j) (D j) := by
  simp only [dotProduct]
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [LiftDeriv_dv, Option.elim_none, Option.elim_some, mul_zero, zero_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LiftDeriv_hsInner_comm]
  unfold LiftDeriv_arr
  rw [LiftDeriv_hsInner_ofReCoord]
  simp only [dotProduct]
  exact Finset.sum_congr rfl fun r _ => mul_comm _ _

private lemma LiftDeriv_sum_hsSq_arr {m W : ℕ} (u : Option (Fin m × Fin 2 × Fin W × Fin W) → ℝ) :
    ∑ j, hsSq (LiftDeriv_arr u j) ≤ ∑ p, u p ^ 2 := by
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [LiftDeriv_arr, ← LiftDeriv_sum_sq_ofReCoord]
  linarith [sq_nonneg (u none)]

private lemma LiftDeriv_dv_line {m W : ℕ} (A B Q : Fin m → Matrix (Fin W) (Fin W) ℂ) (t : ℝ) :
    LiftDeriv_dv (A + t • B + (t * t) • Q) =
      LiftDeriv_dv A + t • LiftDeriv_dv B + (t * t) • LiftDeriv_dv Q := by
  funext p
  cases p with
  | none => simp [LiftDeriv_dv]
  | some s =>
    simp only [LiftDeriv_dv, Option.elim_some, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := congrFun (LiftDeriv_reCoord_add t (B s.1) (A s.1)) s.2
    have h2 := congrFun (LiftDeriv_reCoord_add (t * t) (Q s.1) (A s.1 + t • B s.1)) s.2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
    rw [show A s.1 + t • B s.1 + (t * t) • Q s.1 = (t * t) • Q s.1 + (A s.1 + t • B s.1) by abel,
      h2, show A s.1 + t • B s.1 = t • B s.1 + A s.1 by abel, h1]
    ring

/-- `x = Σ_r x_r e_r` turned into a linear form: `Σ_r f(e_r) x_r = f(x)`. -/
private lemma LiftDeriv_sum_single {κ : Type*} [Fintype κ] [DecidableEq κ] (f : (κ → ℝ) → ℝ)
    (hf : ∀ (a : ℝ) x y, f (a • x + y) = a * f x + f y) (x : κ → ℝ) :
    ∑ r, f (Pi.single r 1) * x r = f x := by
  have h0 : f 0 = 0 := by
    have := hf 1 0 0
    simp only [smul_zero, add_zero, one_mul] at this
    linarith
  have hs : ∀ s : Finset κ,
      f (∑ r ∈ s, x r • Pi.single r 1) = ∑ r ∈ s, f (Pi.single r 1) * x r := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hf, ih, mul_comm]
  have hx : x = ∑ r, x r • (Pi.single r 1 : κ → ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [← hs, ← hx]

private lemma LiftDeriv_dA_mulVec {m W : ℕ} (G' : Fin m → Matrix (Fin W) (Fin W) ℂ)
    (x : Fin 2 × Fin W × Fin W → ℝ) :
    LiftDeriv_dA G' *ᵥ x = LiftDeriv_dv (cohMap G' (ofReCoord x)) := by
  funext p
  cases p with
  | none => simp [Matrix.mulVec, dotProduct, LiftDeriv_dA, LiftDeriv_dv]
  | some s =>
    simp only [Matrix.mulVec, dotProduct, LiftDeriv_dA, LiftDeriv_dv, Matrix.of_apply,
      Option.elim_some]
    refine LiftDeriv_sum_single (fun x => reCoord (cohMap G' (ofReCoord x) s.1) s.2) ?_ x
    intro a x y
    rw [LiftDeriv_ofReCoord_add, LiftDeriv_cohMap_add, Pi.add_apply, Pi.smul_apply,
      LiftDeriv_reCoord_add]
    rfl

/-- The adjoint of `𝓛_{G'}` for Hermitian `G'_j`: `𝓛_{G'}* Y = Σ_j G'_j (Y_j + Y_j*)`. -/
private lemma LiftDeriv_dA_transpose_mulVec {m W : ℕ} {G' : Fin m → Matrix (Fin W) (Fin W) ℂ}
    (hG : ∀ j, (G' j).IsHermitian) (y : Option (Fin m × Fin 2 × Fin W × Fin W) → ℝ) :
    (LiftDeriv_dA G')ᵀ *ᵥ y = reCoord (∑ j, G' j * (LiftDeriv_arr y j + (LiftDeriv_arr y j)ᴴ)) := by
  funext r
  have e1 : ((LiftDeriv_dA G')ᵀ *ᵥ y) r =
      y ⬝ᵥ LiftDeriv_dv (cohMap G' (ofReCoord (Pi.single r 1))) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [mul_comm]
    rfl
  rw [e1, LiftDeriv_dot_dv]
  have e2 : ∀ j, hsInner (LiftDeriv_arr y j) (cohMap G' (ofReCoord (Pi.single r 1)) j) =
      hsInner (G' j * (LiftDeriv_arr y j + (LiftDeriv_arr y j)ᴴ)) (ofReCoord (Pi.single r 1)) := by
    intro j
    rw [cohMap, LiftDeriv_hsInner_add_right, LiftDeriv_hsInner_mul_left,
      LiftDeriv_hsInner_mul_right, LiftDeriv_hsInner_conj, Matrix.mul_add,
      LiftDeriv_hsInner_add_left, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      (hG j).eq]
  simp only [e2]
  have e3 : ∑ j, hsInner (G' j * (LiftDeriv_arr y j + (LiftDeriv_arr y j)ᴴ))
      (ofReCoord (Pi.single r 1)) = hsInner (ofReCoord (Pi.single r 1))
        (∑ j, G' j * (LiftDeriv_arr y j + (LiftDeriv_arr y j)ᴴ)) := by
    rw [LiftDeriv_hsInner_sum_right]
    exact Finset.sum_congr rfl fun j _ => LiftDeriv_hsInner_comm _ _
  rw [e3, LiftDeriv_hsInner_comm, LiftDeriv_hsInner_ofReCoord]
  simp [dotProduct, Pi.single_apply]

end LiftDerivCoord

section LiftDerivLine

/-- `E` is real-linear in the sequence `C`. -/
private lemma LiftDeriv_liftEAux_lin {W : ℕ} (C D R : ℕ → Matrix (Fin W) (Fin W) ℂ)
    (t : ℝ) (top : ℕ) : ∀ n,
    liftEAux (C + t • D) R top n = liftEAux C R top n + t • liftEAux D R top n
  | 0 => by simp [liftEAux]
  | n + 1 => by
    simp only [liftEAux, LiftDeriv_liftEAux_lin C D R t top n, Pi.add_apply,
      Pi.smul_apply, Matrix.mul_add, Matrix.mul_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_smul, star_trivial]
    module

/-- The first-order part of `F_m` along `C ↦ C + t D`. -/
private def LiftDeriv_dF {W : ℕ} (C D R : ℕ → Matrix (Fin W) (Fin W) ℂ) (m : ℕ) :
    Matrix (Fin W) (Fin W) ℂ :=
  liftEAux D R (1000 - 1) (1000 - 1 - m) * C m + liftEAux C R (1000 - 1) (1000 - 1 - m) * D m +
    D m * (liftEAux C R (1000 - 1) (1000 - 1 - m))ᴴ +
    C m * (liftEAux D R (1000 - 1) (1000 - 1 - m))ᴴ + D m * R m * C m + C m * R m * D m

/-- The second-order part of `F_m` along `C ↦ C + t D`. -/
private def LiftDeriv_qF {W : ℕ} (D R : ℕ → Matrix (Fin W) (Fin W) ℂ) (m : ℕ) :
    Matrix (Fin W) (Fin W) ℂ :=
  liftEAux D R (1000 - 1) (1000 - 1 - m) * D m +
    D m * (liftEAux D R (1000 - 1) (1000 - 1 - m))ᴴ + D m * R m * D m

/-- `C_l(V + t ι_i H) = C_l(V) - t g⁻¹ δ_{il} H`. -/
private lemma LiftDeriv_liftC_pert {W : ℕ} (g z t : ℝ)
    (V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) (i : Fin 1000) (H : Matrix (Fin W) (Fin W) ℂ) :
    liftSeq (liftC g z (V + Pi.single i ((t : ℂ) • H))) =
      liftSeq (liftC g z V) + t • liftSeq (Pi.single i ((-g⁻¹) • H)) := by
  funext l
  simp only [Pi.add_apply, Pi.smul_apply]
  unfold liftSeq
  by_cases hl : l < 1000
  · simp only [hl, dite_true]
    ext a b
    by_cases hi : (⟨l, hl⟩ : Fin 1000) = i
    · subst hi
      simp [liftC]
      ring
    · simp [liftC, hi]
  · simp [hl]

/-- `F_m(V + t ι_i H) = F_m(V) + t dF_m + t² qF_m`. -/
private lemma LiftDeriv_liftF_pert {W : ℕ} (g z t : ℝ)
    (V R : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) (i : Fin 1000) (H : Matrix (Fin W) (Fin W) ℂ)
    (m : ℕ) :
    liftF g z (V + Pi.single i ((t : ℂ) • H)) R m = liftF g z V R m +
      t • LiftDeriv_dF (liftSeq (liftC g z V)) (liftSeq (Pi.single i ((-g⁻¹) • H)))
        (liftSeq R) m +
      (t * t) • LiftDeriv_qF (liftSeq (Pi.single i ((-g⁻¹) • H))) (liftSeq R) m := by
  unfold liftF liftE LiftDeriv_dF LiftDeriv_qF
  rw [LiftDeriv_liftC_pert, LiftDeriv_liftEAux_lin]
  simp only [Pi.add_apply, Pi.smul_apply, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, star_trivial]
  module

/-- The data map is quadratic along `V ↦ V + t ι_i H`. -/
private lemma LiftDeriv_pairData_line {W : ℕ} (g z : ℝ)
    (V R : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) (i : Fin 1000) (H : Matrix (Fin W) (Fin W) ℂ) :
    ∃ B Q : Fin 128 → Matrix (Fin W) (Fin W) ℂ, ∀ t : ℝ,
      pairData g z (V + Pi.single i ((t : ℂ) • H)) R = pairData g z V R + t • B + (t * t) • Q := by
  refine ⟨fun j => LiftDeriv_dF (liftSeq (liftC g z V)) (liftSeq (Pi.single i ((-g⁻¹) • H)))
      (liftSeq R) (liftPairI j) - LiftDeriv_dF (liftSeq (liftC g z V))
      (liftSeq (Pi.single i ((-g⁻¹) • H))) (liftSeq R) (liftPairK j),
    fun j => LiftDeriv_qF (liftSeq (Pi.single i ((-g⁻¹) • H))) (liftSeq R) (liftPairI j) -
      LiftDeriv_qF (liftSeq (Pi.single i ((-g⁻¹) • H))) (liftSeq R) (liftPairK j), fun t => ?_⟩
  funext j
  simp only [pairData, LiftDeriv_liftF_pert, Pi.add_apply, Pi.smul_apply]
  module

private lemma LiftDeriv_hasDerivAt_quad {W m : ℕ} (A B Q : Fin m → Matrix (Fin W) (Fin W) ℂ)
    (j : Fin m) : HasDerivAt (fun t : ℝ => (A + t • B + (t * t) • Q) j) (B j) 0 := by
  have h := ((hasDerivAt_const (0 : ℝ) (A j)).add ((hasDerivAt_id (0 : ℝ)).smul_const (B j))).add
    (((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).smul_const (Q j))
  convert h using 1
  · funext t; simp
  · simp

private lemma LiftDeriv_hasDerivAt_quad_real {ι : Type*} (a b q : ι → ℝ) (p : ι) :
    HasDerivAt (fun t : ℝ => (a + t • b + (t * t) • q) p) (b p) 0 := by
  have h := ((hasDerivAt_const (0 : ℝ) (a p)).add ((hasDerivAt_id (0 : ℝ)).mul_const (b p))).add
    (((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).mul_const (q p))
  convert h using 1
  · funext t; simp [smul_eq_mul]
  · simp

private lemma LiftDeriv_layout_line {W m n : ℕ} (d : Matrix (Fin m) (Fin n) ℝ)
    (V : Fin n → Matrix (Fin W) (Fin W) ℂ) (i : Fin n) (H : Matrix (Fin W) (Fin W) ℂ) (t : ℝ) :
    layoutBlocks d (V + Pi.single i ((t : ℂ) • H)) =
      fun j => layoutBlocks d V j + (t : ℂ) • layoutBlocks d (Pi.single i H) j := by
  funext j
  unfold layoutBlocks
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Pi.add_apply, smul_add, Pi.single_smul', Pi.smul_apply, smul_comm]

private lemma LiftDeriv_reCoord_add' {k l : Type*} (t : ℝ) (A B : Matrix k l ℂ) :
    reCoord (A + (t : ℂ) • B) = reCoord A + t • reCoord B := by
  rw [Complex.coe_smul, add_comm, LiftDeriv_reCoord_add, add_comm]

/-- The realified map is affine along `V ↦ V + t ι_i H`. -/
private lemma LiftDeriv_cohRealMat_line {W : ℕ} (V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ)
    (i : Fin 1000) (H : Matrix (Fin W) (Fin W) ℂ) (t : ℝ) :
    cohRealMat (layoutBlocks liftLayout (V + Pi.single i ((t : ℂ) • H))) =
      cohRealMat (layoutBlocks liftLayout V) +
        t • LiftDeriv_dA (layoutBlocks liftLayout (Pi.single i H)) := by
  rw [LiftDeriv_layout_line]
  ext p r
  cases p with
  | none => simp [cohRealMat, LiftDeriv_dA]
  | some s =>
    simp only [cohRealMat, LiftDeriv_dA, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
      Option.elim_some, smul_eq_mul]
    have e : cohMap (fun j => layoutBlocks liftLayout V j +
        (t : ℂ) • layoutBlocks liftLayout (Pi.single i H) j) (ofReCoord (Pi.single r 1)) s.1 =
        cohMap (layoutBlocks liftLayout V) (ofReCoord (Pi.single r 1)) s.1 +
          (t : ℂ) • cohMap (layoutBlocks liftLayout (Pi.single i H))
            (ofReCoord (Pi.single r 1)) s.1 := by
      simp only [cohMap, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add]
      abel
    rw [e, LiftDeriv_reCoord_add']
    rfl

/-- `C_q(V + t ι_i H) = C_q(V) + t C'` with `C' = -g⁻¹ (ι_i H)_q`. -/
private lemma LiftDeriv_liftC_line {W : ℕ} (g z : ℝ) (V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ)
    (i : Fin 1000) (H : Matrix (Fin W) (Fin W) ℂ) (t : ℝ) :
    liftC g z (V + Pi.single i ((t : ℂ) • H)) 999 =
      liftC g z V 999 +
        (t : ℂ) • (-((g : ℂ)⁻¹ • (Pi.single i H : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) 999)) := by
  simp only [liftC, Pi.add_apply, Pi.single_smul', Pi.smul_apply, smul_add, smul_neg]
  rw [smul_comm]
  abel

end LiftDerivLine

section LiftDerivDeriv

/-- `⟨M, [[A, B], [C, D]]⟩` is the sum of the block products. -/
private lemma LiftDeriv_hsInner_blockMat {W : ℕ} (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (A B C D : Matrix (Fin W) (Fin W) ℂ) :
    hsInner M (blockMat A B C D) = hsInner (blockPart M 0 0) A + hsInner (blockPart M 0 1) B +
      hsInner (blockPart M 1 0) C + hsInner (blockPart M 1 1) D := by
  simp only [hsInner, blockMat, blockPart, Matrix.of_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Finset.sum_add_distrib]
  ring

/-- The pairing `⟨M, 𝒦₀ R⟩` written through `P = 𝒦_P R` and `C = C_q`:
`⟨M₁₁ + M₁₂ C* + M₁₂* C - M₂₂*, P⟩ + ⟨M₁₂, C R_q C⟩ - ⟨M₁₂, R_{q-1}⟩ + ⟨M₂₁, R_q⟩`. -/
private lemma LiftDeriv_pair_gen {W : ℕ} (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (P C R₈ R₉ : Matrix (Fin W) (Fin W) ℂ) :
    hsInner M (blockMat P (P * C + C * Pᴴ + C * R₉ * C - R₈) R₉ (-Pᴴ)) =
      hsInner (blockPart M 0 0 + blockPart M 0 1 * Cᴴ + (blockPart M 0 1)ᴴ * C -
          (blockPart M 1 1)ᴴ) P +
        hsInner (blockPart M 0 1) (C * R₉ * C) - hsInner (blockPart M 0 1) R₈ +
        hsInner (blockPart M 1 0) R₉ := by
  rw [LiftDeriv_hsInner_blockMat, LiftDeriv_hsInner_sub_right, LiftDeriv_hsInner_add_right,
    LiftDeriv_hsInner_add_right, LiftDeriv_hsInner_mul_right, LiftDeriv_hsInner_mul_left,
    LiftDeriv_hsInner_conj, LiftDeriv_hsInner_neg_right, LiftDeriv_hsInner_conj,
    LiftDeriv_hsInner_sub_left, LiftDeriv_hsInner_add_left, LiftDeriv_hsInner_add_left,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  ring

private lemma LiftDeriv_hasDerivAt_dot {ι : Type*} [Fintype ι] {u y : ℝ → ι → ℝ} {u' y' : ι → ℝ}
    (hu : HasDerivAt u u' 0) (hy : HasDerivAt y y' 0) :
    HasDerivAt (fun t => u t ⬝ᵥ y t) (u' ⬝ᵥ y 0 + u 0 ⬝ᵥ y') 0 := by
  have h := HasDerivAt.sum (u := Finset.univ) fun p _ =>
    (hasDerivAt_pi.1 hu p).mul (hasDerivAt_pi.1 hy p)
  simp only [dotProduct]
  convert h using 1
  · funext t; simp
  · rw [← Finset.sum_add_distrib]

/-- The continuous linear map `B ↦ B x` on real matrices. -/
private def LiftDeriv_mulVecCLM {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (x : n → ℝ) : Matrix m n ℝ →L[ℝ] (m → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun B => B *ᵥ x
      map_add' := fun B C => Matrix.add_mulVec B C x
      map_smul' := fun c B => Matrix.smul_mulVec c B x }

/-- `⟨X, 𝒦_P R⟩ = 2^{-1/2} g ⟨𝒥ᵀ x, y⟩` with `x = reCoord X` and `y` the coordinates of
`𝓕 R`. -/
private lemma LiftDeriv_hsInner_liftKP {W : ℕ} (g z : ℝ) (V R : Fin 1000 → Matrix (Fin W) (Fin W) ℂ)
    (X : Matrix (Fin W) (Fin W) ℂ) :
    hsInner X (liftKP g z V R) = (Real.sqrt 2)⁻¹ * g *
      (((lsqInv (cohRealMat (layoutBlocks liftLayout V)))ᵀ *ᵥ reCoord X) ⬝ᵥ
        LiftDeriv_dv (pairData g z V R)) := by
  unfold liftKP
  rw [LiftDeriv_hsInner_smul_right]
  congr 1
  unfold cohLeftInv
  rw [LiftDeriv_hsInner_ofReCoord, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  rfl

/-- The derivative `N = (I - A 𝒥) A' (AᵀA)⁻¹ - 𝒥ᵀ A'ᵀ 𝒥ᵀ` of `𝒥ᵀ` along `V ↦ V + t ι_i H`,
(10.22) [eq:c-lift-derivative]. -/
private def LiftDeriv_N {W : ℕ} (V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) (i : Fin 1000)
    (H : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Option (Fin 128 × Fin 2 × Fin W × Fin W)) (Fin 2 × Fin W × Fin W) ℝ :=
  (1 - cohRealMat (layoutBlocks liftLayout V) * lsqInv (cohRealMat (layoutBlocks liftLayout V))) *
      LiftDeriv_dA (layoutBlocks liftLayout (Pi.single i H)) *
      ((cohRealMat (layoutBlocks liftLayout V))ᵀ * cohRealMat (layoutBlocks liftLayout V))⁻¹ -
    (lsqInv (cohRealMat (layoutBlocks liftLayout V)))ᵀ *
      (LiftDeriv_dA (layoutBlocks liftLayout (Pi.single i H)))ᵀ *
      (lsqInv (cohRealMat (layoutBlocks liftLayout V)))ᵀ

/-- The derivative of `t ↦ ⟨X, 𝒦_P(V + t ι_i H) R⟩` at `0`. -/
private def LiftDeriv_dKP {W : ℕ} (g z : ℝ) (V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ)
    (i : Fin 1000) (H : Matrix (Fin W) (Fin W) ℂ) (R : Fin 1000 → Matrix (Fin W) (Fin W) ℂ)
    (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  (Real.sqrt 2)⁻¹ * g *
    ((LiftDeriv_N V i H *ᵥ reCoord X) ⬝ᵥ LiftDeriv_dv (pairData g z V R) +
      ((lsqInv (cohRealMat (layoutBlocks liftLayout V)))ᵀ *ᵥ reCoord X) ⬝ᵥ
        LiftDeriv_dv (fun j => deriv (fun t : ℝ =>
          pairData g z (V + Pi.single i ((t : ℂ) • H)) R j) 0))

/-- `C' = -g⁻¹ (ι_i H)_q`, the derivative of `C_q` along `V ↦ V + t ι_i H`. -/
private def LiftDeriv_Cd {W : ℕ} (g : ℝ) (i : Fin 1000) (H : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin W) (Fin W) ℂ :=
  -((g : ℂ)⁻¹ • (Pi.single i H : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) 999)

/-- `T = M₁₁ + M₁₂ C* + M₁₂* C - M₂₂*`, the matrix paired with `𝒦_P R` in `⟨M, 𝒦₀ R⟩`. -/
private def LiftDeriv_T {W : ℕ} (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (C : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  blockPart M 0 0 + blockPart M 0 1 * Cᴴ + (blockPart M 0 1)ᴴ * C - (blockPart M 1 1)ᴴ

/-- The linear part `M₁₂ C'* + M₁₂* C'` of `T` in `C`. -/
private def LiftDeriv_Td {W : ℕ} (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (C : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  blockPart M 0 1 * Cᴴ + (blockPart M 0 1)ᴴ * C

variable {W : ℕ} {g z c₁ : ℝ} {V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ}


/-- The derivative of `t ↦ ⟨X, 𝒦_P(V + t ι_i H) R⟩` at `0`: the product rule through (10.22)
[eq:c-lift-derivative] for `𝒥` and the derivative of the data map. -/
private lemma LiftDeriv_hasDerivAt_KP (hc₁ : 0 < c₁) (hV : ∀ i, (V i).IsHermitian)
    (hc : c₁ ≤ coerMin (layoutBlocks liftLayout V)) (i : Fin 1000) (H : Matrix (Fin W) (Fin W) ℂ)
    (R : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    HasDerivAt (fun t : ℝ => hsInner X (liftKP g z (V + Pi.single i ((t : ℂ) • H)) R))
      (LiftDeriv_dKP g z V i H R X) 0 := by
  unfold LiftDeriv_dKP LiftDeriv_N
  set A0 := cohRealMat (layoutBlocks liftLayout V) with hA0
  set A' := LiftDeriv_dA (layoutBlocks liftLayout (Pi.single i H)) with hA'
  obtain ⟨B, Q, hBQ⟩ := LiftDeriv_pairData_line g z V R i H
  have hdB : (fun j => deriv (fun t : ℝ => pairData g z (V + Pi.single i ((t : ℂ) • H)) R j) 0) =
      B := by
    funext j
    have e : (fun t : ℝ => pairData g z (V + Pi.single i ((t : ℂ) • H)) R j) =
        fun t : ℝ => (pairData g z V R + t • B + (t * t) • Q) j := funext fun t => by rw [hBQ]
    rw [e]
    exact (LiftDeriv_hasDerivAt_quad _ B Q j).deriv
  rw [hdB]
  have hfun : (fun t : ℝ => hsInner X (liftKP g z (V + Pi.single i ((t : ℂ) • H)) R)) =
      fun t : ℝ => (Real.sqrt 2)⁻¹ * g * (((lsqInv (A0 + t • A'))ᵀ *ᵥ reCoord X) ⬝ᵥ
        (LiftDeriv_dv (pairData g z V R) + t • LiftDeriv_dv B + (t * t) • LiftDeriv_dv Q)) := by
    funext t
    rw [LiftDeriv_hsInner_liftKP, LiftDeriv_cohRealMat_line, hBQ, LiftDeriv_dv_line]
  rw [hfun]
  have hA : HasDerivAt (fun t : ℝ => A0 + t • A') A' 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const A').const_add A0
  have hcl := (cohLeftInv_spec (LiftDeriv_herm_layout liftLayout hV) hc₁ hc).2.2
  have hcl' : ∀ x : Fin 2 × Fin W × Fin W → ℝ,
      min c₁ 1 ^ 2 * ∑ r, x r ^ 2 ≤ ∑ p, ((A0 + (0 : ℝ) • A') *ᵥ x) p ^ 2 := by
    simpa using hcl
  have hL := hasDerivAt_lsqInv_transpose (lt_min hc₁ one_pos) hA hcl'
  simp only [zero_smul, add_zero] at hL
  have hu : HasDerivAt (fun t : ℝ => (lsqInv (A0 + t • A'))ᵀ *ᵥ reCoord X)
      (((1 - A0 * lsqInv A0) * A' * (A0ᵀ * A0)⁻¹ - (lsqInv A0)ᵀ * A'ᵀ * (lsqInv A0)ᵀ) *ᵥ
        reCoord X) 0 :=
    (LiftDeriv_mulVecCLM (m := Option (Fin 128 × Fin 2 × Fin W × Fin W))
      (reCoord X)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hL
  have hy : HasDerivAt (fun t : ℝ => LiftDeriv_dv (pairData g z V R) + t • LiftDeriv_dv B +
      (t * t) • LiftDeriv_dv Q) (LiftDeriv_dv B) 0 :=
    hasDerivAt_pi.2 fun p => LiftDeriv_hasDerivAt_quad_real _ _ _ p
  have h := (LiftDeriv_hasDerivAt_dot hu hy).const_mul ((Real.sqrt 2)⁻¹ * g)
  simpa using h

end LiftDerivDeriv

section LiftDerivDeriv2

variable {W : ℕ} {g z c₁ : ℝ} {V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ}

/-- The derivative of `t ↦ ⟨M, 𝒦₀(V + t ι_i H) R⟩` at `0`:
`D⟨T, 𝒦_P R⟩ + ⟨T', 𝒦_P R⟩ + ⟨M₁₂, C' R_q C + C R_q C'⟩`. -/
private lemma LiftDeriv_hasDerivAt_K0 (hc₁ : 0 < c₁) (hV : ∀ i, (V i).IsHermitian)
    (hc : c₁ ≤ coerMin (layoutBlocks liftLayout V)) (i : Fin 1000) (H : Matrix (Fin W) (Fin W) ℂ)
    (R : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    HasDerivAt (fun t : ℝ => hsInner M (liftK0 g z (V + Pi.single i ((t : ℂ) • H)) R))
      (LiftDeriv_dKP g z V i H R (LiftDeriv_T M (liftC g z V 999)) +
        hsInner (LiftDeriv_Td M (LiftDeriv_Cd g i H)) (liftKP g z V R) +
        hsInner (blockPart M 0 1) (LiftDeriv_Cd g i H * R 999 * liftC g z V 999 +
          liftC g z V 999 * R 999 * LiftDeriv_Cd g i H)) 0 := by
  set C0 := liftC g z V 999 with hC0
  set Cd := LiftDeriv_Cd g i H with hCd
  set P : ℝ → Matrix (Fin W) (Fin W) ℂ := fun t => liftKP g z (V + Pi.single i ((t : ℂ) • H)) R
    with hP
  have hT : ∀ t : ℝ, LiftDeriv_T M (C0 + (t : ℂ) • Cd) =
      LiftDeriv_T M C0 + (t : ℂ) • LiftDeriv_Td M Cd := by
    intro t
    simp only [LiftDeriv_T, LiftDeriv_Td, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Complex.star_def, Complex.conj_ofReal, Matrix.mul_add, Matrix.mul_smul, smul_add]
    abel
  have hCC : ∀ t : ℝ, (C0 + (t : ℂ) • Cd) * R 999 * (C0 + (t : ℂ) • Cd) =
      C0 * R 999 * C0 + (t : ℂ) • (Cd * R 999 * C0 + C0 * R 999 * Cd) +
        ((t * t : ℝ) : ℂ) • (Cd * R 999 * Cd) := by
    intro t
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add,
      smul_smul, Complex.ofReal_mul]
    abel
  have hfun : (fun t : ℝ => hsInner M (liftK0 g z (V + Pi.single i ((t : ℂ) • H)) R)) =
      fun t : ℝ => hsInner (LiftDeriv_T M C0) (P t) + t * hsInner (LiftDeriv_Td M Cd) (P t) +
        (hsInner (blockPart M 0 1) (C0 * R 999 * C0) +
          t * hsInner (blockPart M 0 1) (Cd * R 999 * C0 + C0 * R 999 * Cd) +
          (t * t) * hsInner (blockPart M 0 1) (Cd * R 999 * Cd)) -
        hsInner (blockPart M 0 1) (R 998) + hsInner (blockPart M 1 0) (R 999) := by
    funext t
    have hl : liftC g z (V + Pi.single i ((t : ℂ) • H)) 999 = C0 + (t : ℂ) • Cd :=
      LiftDeriv_liftC_line g z V i H t
    unfold liftK0
    rw [LiftDeriv_pair_gen, hl, hCC]
    have e := hT t
    unfold LiftDeriv_T at e
    rw [e, LiftDeriv_hsInner_add_left, LiftDeriv_hsInner_smul_left, LiftDeriv_hsInner_add_right,
      LiftDeriv_hsInner_add_right, LiftDeriv_hsInner_smul_right, LiftDeriv_hsInner_smul_right]
    rfl
  rw [hfun]
  have h1 := LiftDeriv_hasDerivAt_KP (g := g) (z := z) hc₁ hV hc i H R (LiftDeriv_T M C0)
  have h2 := (hasDerivAt_id (0 : ℝ)).mul
    (LiftDeriv_hasDerivAt_KP (g := g) (z := z) hc₁ hV hc i H R (LiftDeriv_Td M Cd))
  have h3 := LiftDeriv_hasDerivAt_quad_real
    (fun _ : Unit => hsInner (blockPart M 0 1) (C0 * R 999 * C0))
    (fun _ => hsInner (blockPart M 0 1) (Cd * R 999 * C0 + C0 * R 999 * Cd))
    (fun _ => hsInner (blockPart M 0 1) (Cd * R 999 * Cd)) ()
  have h := ((h1.add h2).add h3).sub_const (hsInner (blockPart M 0 1) (R 998)) |>.add_const
    (hsInner (blockPart M 1 0) (R 999))
  convert h using 1
  · funext t; simp [P, smul_eq_mul]
  · simp

end LiftDerivDeriv2

section LiftDerivBound

/-- `‖𝒥ᵀ y‖ ≤ τ⁻¹ ‖y‖` for `‖A x‖ ≥ τ ‖x‖`. -/
private lemma LiftDeriv_lsqInv_transpose_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {A : Matrix m n ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hA : ∀ x : n → ℝ, τ ^ 2 * ∑ i, x i ^ 2 ≤ ∑ j, (A *ᵥ x) j ^ 2) (y : n → ℝ) :
    ∑ j, ((lsqInv A)ᵀ *ᵥ y) j ^ 2 ≤ (τ ^ 2)⁻¹ * ∑ j, y j ^ 2 := by
  set w := (lsqInv A)ᵀ *ᵥ y with hw
  set S := ∑ j, w j ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hy0 : 0 ≤ ∑ j, y j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have e : S = ∑ j, y j * (lsqInv A *ᵥ w) j := by
    have h1 : S = w ⬝ᵥ w := by simp [hS, dotProduct, sq]
    have h2 : y ⬝ᵥ (lsqInv A *ᵥ w) = w ⬝ᵥ w := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    rw [h1, ← h2]
    rfl
  have hcs : S ^ 2 ≤ (∑ j, y j ^ 2) * ∑ j, (lsqInv A *ᵥ w) j ^ 2 := by
    rw [e]; exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hJ := (lsqInv_spec hτ hA).2.1 w
  have h3 : S ^ 2 ≤ (∑ j, y j ^ 2) * ((τ ^ 2)⁻¹ * S) :=
    hcs.trans (mul_le_mul_of_nonneg_left hJ hy0)
  rcases hS0.lt_or_eq with hpos | hzero
  · have : S * S ≤ ((τ ^ 2)⁻¹ * ∑ j, y j ^ 2) * S := by nlinarith
    exact le_of_mul_le_mul_right this hpos
  · rw [← hzero]; positivity

/-- `Σ_{(i, α)} φ(ι_i H_α)² ≤ B` for a real-linear `φ` with `φ(R)² ≤ B ‖R‖²`. -/
private lemma LiftDeriv_adj_sum {W : ℕ} (φ : (Fin 1000 → Matrix (Fin W) (Fin W) ℂ) → ℝ)
    (hφ : ∀ (a : ℝ) R R', φ (a • R + R') = a * φ R + φ R') {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ R, φ R ^ 2 ≤ B * ∑ i, hsSq (R i)) :
    ∑ e : Fin 1000 × (Fin W × Fin W), φ (Pi.single e.1 (hermBasis W e.2)) ^ 2 ≤ B := by
  set c : Fin 1000 × (Fin W × Fin W) → ℝ := fun e => φ (Pi.single e.1 (hermBasis W e.2)) with hc
  have h0 : φ 0 = 0 := by
    have := hφ 1 0 0
    simp only [smul_zero, add_zero, one_mul] at this
    linarith
  have hlin : ∀ s : Finset (Fin 1000 × (Fin W × Fin W)),
      φ (∑ e ∈ s, c e • Pi.single e.1 (hermBasis W e.2)) = ∑ e ∈ s, c e * c e := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hφ, ih]
  set w := ∑ e, c e • (Pi.single e.1 (hermBasis W e.2) : Fin 1000 → Matrix (Fin W) (Fin W) ℂ)
    with hw
  have hwi : ∀ i, w i = ∑ b, ((c (i, b) : ℝ) : ℂ) • hermBasis W b := by
    intro i
    rw [hw, Finset.sum_apply, Fintype.sum_prod_type]
    simp only [Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero]
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
    simp [Complex.coe_smul]
  have hS : ∑ i, hsSq (w i) = ∑ e, c e ^ 2 := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => by rw [hwi, LiftDeriv_hsSq_basis]
  have hφw : φ w = ∑ e, c e ^ 2 := by
    rw [hw, hlin]; simp [sq]
  set S := ∑ e, c e ^ 2 with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun e _ => sq_nonneg _
  have h1 := hB w
  rw [hφw, hS] at h1
  rcases hS0.lt_or_eq with hpos | hzero
  · have : S * S ≤ B * S := by nlinarith
    exact le_of_mul_le_mul_right this hpos
  · rw [← hzero]; exact hB0

private lemma LiftDeriv_liftSeq_add {W q : ℕ} (a : ℝ) (R R' : Fin q → Matrix (Fin W) (Fin W) ℂ) :
    liftSeq (a • R + R') = a • liftSeq R + liftSeq R' := by
  funext k
  unfold liftSeq
  by_cases h : k < q <;> simp [h]

private lemma LiftDeriv_liftEAux_add {W : ℕ} (C R R' : ℕ → Matrix (Fin W) (Fin W) ℂ)
    (a : ℝ) (top : ℕ) : ∀ n,
    liftEAux C (a • R + R') top n = a • liftEAux C R top n + liftEAux C R' top n
  | 0 => by simp [liftEAux]
  | n + 1 => by
    simp only [liftEAux, LiftDeriv_liftEAux_add C R R' a top n, Pi.add_apply,
      Pi.smul_apply, Matrix.add_mul, Matrix.smul_mul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_smul, star_trivial]
    module

/-- The data map is real-linear in the data `R`. -/
private lemma LiftDeriv_pairData_add {W : ℕ} (g z a : ℝ)
    (V R R' : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) :
    pairData g z V (a • R + R') = a • pairData g z V R + pairData g z V R' := by
  have hF : ∀ k, liftF g z V (a • R + R') k = a • liftF g z V R k + liftF g z V R' k := by
    intro k
    unfold liftF liftE
    rw [LiftDeriv_liftSeq_add, LiftDeriv_liftEAux_add]
    simp only [Pi.add_apply, Pi.smul_apply, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, star_trivial]
    module
  funext j
  simp only [pairData, hF, Pi.add_apply, Pi.smul_apply]
  module

private lemma LiftDeriv_dv_add {m W : ℕ} (a : ℝ) (D D' : Fin m → Matrix (Fin W) (Fin W) ℂ) :
    LiftDeriv_dv (a • D + D') = a • LiftDeriv_dv D + LiftDeriv_dv D' := by
  funext p
  cases p with
  | none => simp [LiftDeriv_dv]
  | some s =>
    have h := congrFun (LiftDeriv_reCoord_add a (D s.1) (D' s.1)) s.2
    simpa [LiftDeriv_dv] using h

/-- `Σ_{(i, α)} ⟨u, 𝓕(ι_i H_α)⟩² ≤ F ‖u‖²` when `‖𝓕 R‖² ≤ F ‖R‖²`. -/
private lemma LiftDeriv_adj_pairData {W : ℕ} (g z : ℝ) (V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ)
    {F : ℝ} (hF0 : 0 ≤ F)
    (hF : ∀ R : Fin 1000 → Matrix (Fin W) (Fin W) ℂ,
      ∑ j, hsSq (pairData g z V R j) ≤ F * ∑ i, hsSq (R i))
    (u : Option (Fin 128 × Fin 2 × Fin W × Fin W) → ℝ) :
    ∑ e : Fin 1000 × (Fin W × Fin W),
        (u ⬝ᵥ LiftDeriv_dv (pairData g z V (Pi.single e.1 (hermBasis W e.2)))) ^ 2 ≤
      F * ∑ p, u p ^ 2 := by
  have hu0 : 0 ≤ ∑ p, u p ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  refine LiftDeriv_adj_sum (fun R => u ⬝ᵥ LiftDeriv_dv (pairData g z V R)) (fun a R R' => ?_)
    (mul_nonneg hF0 hu0) fun R => ?_
  · rw [LiftDeriv_pairData_add, LiftDeriv_dv_add, dotProduct_add, dotProduct_smul, smul_eq_mul]
  · have hcs : (u ⬝ᵥ LiftDeriv_dv (pairData g z V R)) ^ 2 ≤
        (∑ p, u p ^ 2) * ∑ p, LiftDeriv_dv (pairData g z V R) p ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    rw [LiftDeriv_sum_sq_dv] at hcs
    calc _ ≤ (∑ p, u p ^ 2) * (F * ∑ i, hsSq (R i)) :=
          hcs.trans (mul_le_mul_of_nonneg_left (hF R) hu0)
      _ = _ := by ring

end LiftDerivBound

section LiftDerivTerms

private lemma LiftDeriv_hsSq_one (W : ℕ) : hsSq (1 : Matrix (Fin W) (Fin W) ℂ) = W := by
  unfold hsSq
  have h : ∀ a b : Fin W, ‖(1 : Matrix (Fin W) (Fin W) ℂ) a b‖ ^ 2 = if a = b then 1 else 0 := by
    intro a b
    rw [Matrix.one_apply]
    split_ifs <;> simp
  simp only [h, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

private lemma LiftDeriv_sum_hsSq_mul_basis {W : ℕ} (Y : Matrix (Fin W) (Fin W) ℂ) :
    ∑ a, hsSq (hermBasis W a * Y) = W * hsSq Y ∧ ∑ a, hsSq (Y * hermBasis W a) = W * hsSq Y := by
  constructor
  · have h := (hermBasis_completeness W 1 Y).2
    simpa only [Matrix.one_mul, LiftDeriv_hsSq_one] using h
  · have h := (hermBasis_completeness W Y 1).2
    rw [LiftDeriv_hsSq_one, mul_comm] at h
    simpa only [Matrix.mul_one] using h

private lemma LiftDeriv_herm_single {W : ℕ} (i : Fin 1000) (a : Fin W × Fin W) (l : Fin 1000) :
    ((Pi.single i (hermBasis W a) : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) l).IsHermitian := by
  rw [Pi.single_apply]
  split_ifs
  · exact hermBasis_isHermitian W a
  · exact Matrix.isHermitian_zero

/-- Only the last input carries `C' ≠ 0`. -/
private lemma LiftDeriv_sum_Cd {W : ℕ} (g : ℝ) (f : Matrix (Fin W) (Fin W) ℂ → ℝ) (hf : f 0 = 0)
    (H : Matrix (Fin W) (Fin W) ℂ) :
    ∑ i : Fin 1000, f (LiftDeriv_Cd g i H) = f (-((g : ℂ)⁻¹ • H)) := by
  rw [Finset.sum_eq_single 999 (fun i _ hi => by
    simp [LiftDeriv_Cd, Ne.symm hi, hf]) (by simp)]
  simp [LiftDeriv_Cd]

/-- `Σ_{(i, α)} ⟨X, (ι_i H_α)_q⟩² ≤ ‖X‖²`. -/
private lemma LiftDeriv_sum_last {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) :
    ∑ e : Fin 1000 × (Fin W × Fin W),
        hsInner X ((Pi.single e.1 (hermBasis W e.2) : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) 999) ^ 2
      ≤ hsSq X := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single 999 (fun k _ hk => by
    simp [Ne.symm hk, hsInner]) (by simp)]
  simp only [Pi.single_eq_same]
  simpa only [LiftDeriv_hsInner_comm X] using (hermBasis_parseval W X).1

private lemma LiftDeriv_hK {W : ℕ} (x : Fin 2 × Fin W × Fin W → ℝ) :
    ∑ d : Fin 1000 × (Fin W × Fin W), ∑ p,
        (LiftDeriv_dA (layoutBlocks liftLayout (Pi.single d.1 (hermBasis W d.2))) *ᵥ x) p ^ 2 ≤
      512 * W * ∑ r, x r ^ 2 := by
  simp only [LiftDeriv_dA_mulVec, LiftDeriv_sum_sq_dv]
  rw [Fintype.sum_prod_type, LiftDeriv_sum_sq_ofReCoord]
  exact (sum_hsSq_cohMap_deriv_le (ofReCoord x) 0).1

private lemma LiftDeriv_hK' {W : ℕ} (y : Option (Fin 128 × Fin 2 × Fin W × Fin W) → ℝ) :
    ∑ d : Fin 1000 × (Fin W × Fin W), ∑ r,
        ((LiftDeriv_dA (layoutBlocks liftLayout (Pi.single d.1 (hermBasis W d.2))))ᵀ *ᵥ y) r ^ 2 ≤
      512 * W * ∑ p, y p ^ 2 := by
  have e : ∀ d : Fin 1000 × (Fin W × Fin W), ∑ r,
      ((LiftDeriv_dA (layoutBlocks liftLayout (Pi.single d.1 (hermBasis W d.2))))ᵀ *ᵥ y) r ^ 2 =
        hsSq (∑ j, layoutBlocks liftLayout (Pi.single d.1 (hermBasis W d.2)) j *
          (LiftDeriv_arr y j + (LiftDeriv_arr y j)ᴴ)) := by
    intro d
    rw [LiftDeriv_dA_transpose_mulVec (LiftDeriv_herm_layout liftLayout
      (LiftDeriv_herm_single d.1 d.2)), LiftDeriv_sum_sq_reCoord]
  simp only [e]
  rw [Fintype.sum_prod_type]
  have h := (sum_hsSq_cohMap_deriv_le 0 (LiftDeriv_arr y)).2
  have h2 := LiftDeriv_sum_hsSq_arr y
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have hy : 0 ≤ ∑ p, y p ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  calc _ ≤ 4 * W * ∑ j, hsSq (LiftDeriv_arr y j) := h
    _ ≤ 4 * W * ∑ p, y p ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ 512 * W * ∑ p, y p ^ 2 := by nlinarith

variable {W : ℕ} {g z c₁ : ℝ} {V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ}

/-- The `D𝒥` term, through (10.23) [eq:c-J-bound] with `K = 512 W`. -/
private lemma LiftDeriv_termA (hc₁ : 0 < c₁) (hV : ∀ i, (V i).IsHermitian)
    (hc : c₁ ≤ coerMin (layoutBlocks liftLayout V)) {F : ℝ} (hF0 : 0 ≤ F)
    (hF : ∀ R : Fin 1000 → Matrix (Fin W) (Fin W) ℂ,
      ∑ j, hsSq (pairData g z V R j) ≤ F * ∑ i, hsSq (R i))
    (x : Fin 2 × Fin W × Fin W → ℝ) :
    ∑ d : Fin 1000 × (Fin W × Fin W), ∑ e : Fin 1000 × (Fin W × Fin W),
        ((LiftDeriv_N V d.1 (hermBasis W d.2) *ᵥ x) ⬝ᵥ
          LiftDeriv_dv (pairData g z V (Pi.single e.1 (hermBasis W e.2)))) ^ 2 ≤
      F * (4 * (512 * W) * (min c₁ 1 ^ 4)⁻¹ * ∑ r, x r ^ 2) := by
  have hA := (cohLeftInv_spec (LiftDeriv_herm_layout liftLayout hV) hc₁ hc).2.2
  have h9 := sum_sq_lsqInv_deriv_le (lt_min hc₁ one_pos) hA
    (A' := fun d : Fin 1000 × (Fin W × Fin W) =>
      LiftDeriv_dA (layoutBlocks liftLayout (Pi.single d.1 (hermBasis W d.2))))
    LiftDeriv_hK LiftDeriv_hK' x
  calc _ ≤ ∑ d : Fin 1000 × (Fin W × Fin W),
        F * ∑ p, (LiftDeriv_N V d.1 (hermBasis W d.2) *ᵥ x) p ^ 2 :=
        Finset.sum_le_sum fun d _ => LiftDeriv_adj_pairData g z V hF0 hF _
    _ = F * ∑ d : Fin 1000 × (Fin W × Fin W),
        ∑ p, (LiftDeriv_N V d.1 (hermBasis W d.2) *ᵥ x) p ^ 2 := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left h9 hF0

/-- The `D𝓕` term, through (10.20) [eq:c-F-bounds]. -/
private lemma LiftDeriv_termB (hc₁ : 0 < c₁) (hV : ∀ i, (V i).IsHermitian)
    (hc : c₁ ≤ coerMin (layoutBlocks liftLayout V)) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ Z : Fin 128 → Matrix (Fin W) (Fin W) ℂ,
      ∑ i : Fin 1000, ∑ a : Fin W × Fin W, ∑ k : Fin 1000, ∑ b : Fin W × Fin W,
        (∑ j, hsInner (Z j) (deriv (fun t : ℝ => pairData g z
          (V + Pi.single i ((t : ℂ) • hermBasis W a)) (Pi.single k (hermBasis W b)) j) 0)) ^ 2 ≤
        D * ∑ j, hsSq (Z j))
    (x : Fin 2 × Fin W × Fin W → ℝ) :
    ∑ d : Fin 1000 × (Fin W × Fin W), ∑ e : Fin 1000 × (Fin W × Fin W),
        (((lsqInv (cohRealMat (layoutBlocks liftLayout V)))ᵀ *ᵥ x) ⬝ᵥ
          LiftDeriv_dv (fun j => deriv (fun t : ℝ => pairData g z
            (V + Pi.single d.1 ((t : ℂ) • hermBasis W d.2)) (Pi.single e.1 (hermBasis W e.2)) j)
              0)) ^ 2 ≤
      D * ((min c₁ 1 ^ 2)⁻¹ * ∑ r, x r ^ 2) := by
  have hA := (cohLeftInv_spec (LiftDeriv_herm_layout liftLayout hV) hc₁ hc).2.2
  set u := (lsqInv (cohRealMat (layoutBlocks liftLayout V)))ᵀ *ᵥ x with hu
  simp only [LiftDeriv_dot_dv]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type (f := fun e : Fin 1000 × (Fin W × Fin W) => _)]
  calc _ ≤ D * ∑ j, hsSq (LiftDeriv_arr u j) := hD _
    _ ≤ D * ∑ p, u p ^ 2 := mul_le_mul_of_nonneg_left (LiftDeriv_sum_hsSq_arr u) hD0
    _ ≤ _ := mul_le_mul_of_nonneg_left
        (LiftDeriv_lsqInv_transpose_le (lt_min hc₁ one_pos) hA x) hD0

/-- `Σ_{(i, α)} ⟨X, 𝒦_P(ι_i H_α)⟩² ≤ (g²/2) F τ⁻² ‖X‖²`. -/
private lemma LiftDeriv_termC (hc₁ : 0 < c₁) (hV : ∀ i, (V i).IsHermitian)
    (hc : c₁ ≤ coerMin (layoutBlocks liftLayout V)) {F : ℝ} (hF0 : 0 ≤ F)
    (hF : ∀ R : Fin 1000 → Matrix (Fin W) (Fin W) ℂ,
      ∑ j, hsSq (pairData g z V R j) ≤ F * ∑ i, hsSq (R i))
    (X : Matrix (Fin W) (Fin W) ℂ) :
    ∑ e : Fin 1000 × (Fin W × Fin W), hsInner X (liftKP g z V (Pi.single e.1 (hermBasis W e.2))) ^ 2
      ≤ g ^ 2 / 2 * (F * ((min c₁ 1 ^ 2)⁻¹ * hsSq X)) := by
  have hA := (cohLeftInv_spec (LiftDeriv_herm_layout liftLayout hV) hc₁ hc).2.2
  have hs : (Real.sqrt 2)⁻¹ ^ 2 = 1 / 2 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
  simp only [LiftDeriv_hsInner_liftKP, mul_pow]
  rw [← Finset.mul_sum, hs]
  have h1 := LiftDeriv_adj_pairData g z V hF0 hF
    ((lsqInv (cohRealMat (layoutBlocks liftLayout V)))ᵀ *ᵥ reCoord X)
  have h2 := LiftDeriv_lsqInv_transpose_le (lt_min hc₁ one_pos) hA (reCoord X)
  rw [LiftDeriv_sum_sq_reCoord] at h2
  have h3 := h1.trans (mul_le_mul_of_nonneg_left h2 hF0)
  calc 1 / 2 * g ^ 2 * _ ≤ 1 / 2 * g ^ 2 * (F * ((min c₁ 1 ^ 2)⁻¹ * hsSq X)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

/-- `Σ_{(i, α)} ‖T'‖² ≤ 4 g⁻² W ‖M₁₂‖²` for `T' = M₁₂ C'* + M₁₂* C'`. -/
private lemma LiftDeriv_sum_Td (g : ℝ) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ∑ d : Fin 1000 × (Fin W × Fin W), hsSq (LiftDeriv_Td M (LiftDeriv_Cd g d.1 (hermBasis W d.2)))
      ≤ 4 * g⁻¹ ^ 2 * W * hsSq (blockPart M 0 1) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have e : ∀ a : Fin W × Fin W, ∑ i : Fin 1000,
      hsSq (LiftDeriv_Td M (LiftDeriv_Cd g i (hermBasis W a))) =
        hsSq (LiftDeriv_Td M (-((g : ℂ)⁻¹ • hermBasis W a))) :=
    fun a => LiftDeriv_sum_Cd g (fun C => hsSq (LiftDeriv_Td M C)) (by simp [LiftDeriv_Td, hsSq])
      (hermBasis W a)
  simp only [e]
  set B := blockPart M 0 1
  have e2 : ∀ a : Fin W × Fin W, LiftDeriv_Td M (-((g : ℂ)⁻¹ • hermBasis W a)) =
      (-((g : ℂ)⁻¹)) • (B * hermBasis W a + Bᴴ * hermBasis W a) := by
    intro a
    simp only [LiftDeriv_Td, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul,
      (hermBasis_isHermitian W a).eq, star_inv₀, Complex.star_def, Complex.conj_ofReal,
      Matrix.mul_neg, Matrix.mul_smul, smul_add, neg_smul, B]
  have hg : ‖(-((g : ℂ)⁻¹))‖ ^ 2 = g⁻¹ ^ 2 := by
    rw [norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs, inv_pow, sq_abs, inv_pow]
  simp only [e2, LiftDeriv_hsSq_smul, hg]
  have h1 := (LiftDeriv_sum_hsSq_mul_basis B).2
  have h2 := (LiftDeriv_sum_hsSq_mul_basis Bᴴ).2
  rw [LiftDeriv_hsSq_conjTranspose] at h2
  have hg0 : 0 ≤ g⁻¹ ^ 2 := sq_nonneg _
  calc ∑ a, g⁻¹ ^ 2 * hsSq (B * hermBasis W a + Bᴴ * hermBasis W a)
      ≤ ∑ a, g⁻¹ ^ 2 * (2 * hsSq (B * hermBasis W a) + 2 * hsSq (Bᴴ * hermBasis W a)) :=
        Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (LiftDeriv_hsSq_add_le _ _) hg0
    _ = g⁻¹ ^ 2 * (2 * ∑ a, hsSq (B * hermBasis W a) + 2 * ∑ a, hsSq (Bᴴ * hermBasis W a)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = _ := by rw [h1, h2]; ring

/-- The `C'` term: `Σ ⟨M₁₂, C' R_q C + C R_q C'⟩² ≤ 4 g⁻² W |C|²_op ‖M₁₂‖²`. -/
private lemma LiftDeriv_termD (g : ℝ) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    {C0 : Matrix (Fin W) (Fin W) ℂ} (hC0 : C0ᴴ = C0) :
    ∑ d : Fin 1000 × (Fin W × Fin W), ∑ e : Fin 1000 × (Fin W × Fin W),
        hsInner (blockPart M 0 1)
          (LiftDeriv_Cd g d.1 (hermBasis W d.2) *
              (Pi.single e.1 (hermBasis W e.2) : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) 999 * C0 +
            C0 * (Pi.single e.1 (hermBasis W e.2) : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) 999 *
              LiftDeriv_Cd g d.1 (hermBasis W d.2)) ^ 2 ≤
      4 * g⁻¹ ^ 2 * W * ‖C0‖ ^ 2 * hsSq (blockPart M 0 1) := by
  set B := blockPart M 0 1
  have eX : ∀ (Cd Y : Matrix (Fin W) (Fin W) ℂ), hsInner B (Cd * Y * C0 + C0 * Y * Cd) =
      hsInner (Cdᴴ * (B * C0ᴴ) + C0ᴴ * (B * Cdᴴ)) Y := by
    intro Cd Y
    rw [LiftDeriv_hsInner_add_right, LiftDeriv_hsInner_mul_right, LiftDeriv_hsInner_mul_left,
      LiftDeriv_hsInner_mul_right B (C0 * Y), LiftDeriv_hsInner_mul_left,
      LiftDeriv_hsInner_add_left]
  simp only [eX]
  have h1 : ∀ d : Fin 1000 × (Fin W × Fin W), ∑ e : Fin 1000 × (Fin W × Fin W),
      hsInner ((LiftDeriv_Cd g d.1 (hermBasis W d.2))ᴴ * (B * C0ᴴ) +
        C0ᴴ * (B * (LiftDeriv_Cd g d.1 (hermBasis W d.2))ᴴ))
        ((Pi.single e.1 (hermBasis W e.2) : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) 999) ^ 2 ≤
      hsSq ((LiftDeriv_Cd g d.1 (hermBasis W d.2))ᴴ * (B * C0ᴴ) +
        C0ᴴ * (B * (LiftDeriv_Cd g d.1 (hermBasis W d.2))ᴴ)) := fun d => LiftDeriv_sum_last _
  refine (Finset.sum_le_sum fun d _ => h1 d).trans ?_
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have e : ∀ a : Fin W × Fin W, ∑ i : Fin 1000,
      hsSq ((LiftDeriv_Cd g i (hermBasis W a))ᴴ * (B * C0ᴴ) +
        C0ᴴ * (B * (LiftDeriv_Cd g i (hermBasis W a))ᴴ)) =
      hsSq ((-((g : ℂ)⁻¹ • hermBasis W a))ᴴ * (B * C0ᴴ) +
        C0ᴴ * (B * (-((g : ℂ)⁻¹ • hermBasis W a))ᴴ)) :=
    fun a => LiftDeriv_sum_Cd g (fun C => hsSq (Cᴴ * (B * C0ᴴ) + C0ᴴ * (B * Cᴴ)))
      (by simp [hsSq]) (hermBasis W a)
  simp only [e]
  have e2 : ∀ a : Fin W × Fin W, (-((g : ℂ)⁻¹ • hermBasis W a))ᴴ * (B * C0ᴴ) +
      C0ᴴ * (B * (-((g : ℂ)⁻¹ • hermBasis W a))ᴴ) =
      (-((g : ℂ)⁻¹)) • (hermBasis W a * (B * C0ᴴ) + (C0ᴴ * B) * hermBasis W a) := by
    intro a
    simp only [Matrix.conjTranspose_neg, Matrix.conjTranspose_smul,
      (hermBasis_isHermitian W a).eq, star_inv₀, Complex.star_def, Complex.conj_ofReal,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add, neg_smul,
      Matrix.mul_assoc]
  have hg : ‖(-((g : ℂ)⁻¹))‖ ^ 2 = g⁻¹ ^ 2 := by
    rw [norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs, inv_pow, sq_abs, inv_pow]
  simp only [e2, LiftDeriv_hsSq_smul, hg]
  have h3 := (LiftDeriv_sum_hsSq_mul_basis (B * C0ᴴ)).1
  have h4 := (LiftDeriv_sum_hsSq_mul_basis (C0ᴴ * B)).2
  have h5 : hsSq (B * C0ᴴ) ≤ ‖C0‖ ^ 2 * hsSq B := by
    rw [hC0]; exact LiftDeriv_hsSq_mul_le' C0 B
  have h6 : hsSq (C0ᴴ * B) ≤ ‖C0‖ ^ 2 * hsSq B := by
    rw [hC0]; exact LiftDeriv_hsSq_mul_le C0 B
  have hg0 : 0 ≤ g⁻¹ ^ 2 := sq_nonneg _
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  calc ∑ a, g⁻¹ ^ 2 * hsSq (hermBasis W a * (B * C0ᴴ) + (C0ᴴ * B) * hermBasis W a)
      ≤ ∑ a, g⁻¹ ^ 2 * (2 * hsSq (hermBasis W a * (B * C0ᴴ)) +
          2 * hsSq ((C0ᴴ * B) * hermBasis W a)) :=
        Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (LiftDeriv_hsSq_add_le _ _) hg0
    _ = g⁻¹ ^ 2 * (2 * ∑ a, hsSq (hermBasis W a * (B * C0ᴴ)) +
          2 * ∑ a, hsSq ((C0ᴴ * B) * hermBasis W a)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = g⁻¹ ^ 2 * (2 * (W * hsSq (B * C0ᴴ)) + 2 * (W * hsSq (C0ᴴ * B))) := by rw [h3, h4]
    _ ≤ g⁻¹ ^ 2 * (2 * (W * (‖C0‖ ^ 2 * hsSq B)) + 2 * (W * (‖C0‖ ^ 2 * hsSq B))) := by
        gcongr
    _ = _ := by ring

end LiftDerivTerms

section LiftDerivAssemble

variable {W : ℕ} {g z c₁ : ℝ} {V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ}

/-- The input derivative `ℓ(d, e) = D_d ⟨M, 𝒦₀(ι_k H_β)⟩` in the direction `d = (i, α)` at the
basis array `e = (k, β)`. -/
private def LiftDeriv_ell (g z : ℝ) (V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ)
    (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (d e : Fin 1000 × (Fin W × Fin W)) : ℝ :=
  LiftDeriv_dKP g z V d.1 (hermBasis W d.2) (Pi.single e.1 (hermBasis W e.2))
      (LiftDeriv_T M (liftC g z V 999)) +
    hsInner (LiftDeriv_Td M (LiftDeriv_Cd g d.1 (hermBasis W d.2)))
      (liftKP g z V (Pi.single e.1 (hermBasis W e.2))) +
    hsInner (blockPart M 0 1)
      (LiftDeriv_Cd g d.1 (hermBasis W d.2) *
          (Pi.single e.1 (hermBasis W e.2) : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) 999 *
          liftC g z V 999 +
        liftC g z V 999 *
          (Pi.single e.1 (hermBasis W e.2) : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) 999 *
          LiftDeriv_Cd g d.1 (hermBasis W d.2))

/-- The four-term bound for `Σ_{d, e} ℓ(d, e)²`, (10.24) [eq:c-KP-bound] and the paper's display
before (10.26) [eq:c-lift-cost]. -/
private lemma LiftDeriv_sum_ell_le (hc₁ : 0 < c₁) (hV : ∀ i, (V i).IsHermitian)
    (hc : c₁ ≤ coerMin (layoutBlocks liftLayout V)) (hC0 : (liftC g z V 999)ᴴ = liftC g z V 999)
    (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) {F D : ℝ} (hF0 : 0 ≤ F)
    (hF : ∀ R : Fin 1000 → Matrix (Fin W) (Fin W) ℂ,
      ∑ j, hsSq (pairData g z V R j) ≤ F * ∑ i, hsSq (R i)) (hD0 : 0 ≤ D)
    (hD : ∀ Z : Fin 128 → Matrix (Fin W) (Fin W) ℂ,
      ∑ i : Fin 1000, ∑ a : Fin W × Fin W, ∑ k : Fin 1000, ∑ b : Fin W × Fin W,
        (∑ j, hsInner (Z j) (deriv (fun t : ℝ => pairData g z
          (V + Pi.single i ((t : ℂ) • hermBasis W a)) (Pi.single k (hermBasis W b)) j) 0)) ^ 2 ≤
        D * ∑ j, hsSq (Z j)) :
    ∑ d, ∑ e, LiftDeriv_ell g z V M d e ^ 2 ≤
      4 * (g ^ 2 / 2 * (F * (4 * (512 * W) * (min c₁ 1 ^ 4)⁻¹ *
          hsSq (LiftDeriv_T M (liftC g z V 999)))) +
        g ^ 2 / 2 * (D * ((min c₁ 1 ^ 2)⁻¹ * hsSq (LiftDeriv_T M (liftC g z V 999)))) +
        g ^ 2 / 2 * (F * ((min c₁ 1 ^ 2)⁻¹ * (4 * g⁻¹ ^ 2 * W * hsSq (blockPart M 0 1)))) +
        4 * g⁻¹ ^ 2 * W * ‖liftC g z V 999‖ ^ 2 * hsSq (blockPart M 0 1)) := by
  set x := reCoord (LiftDeriv_T M (liftC g z V 999)) with hx
  have hxx : ∑ r, x r ^ 2 = hsSq (LiftDeriv_T M (liftC g z V 999)) := LiftDeriv_sum_sq_reCoord _
  have hs : (Real.sqrt 2)⁻¹ ^ 2 = 1 / 2 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
  set a : Fin 1000 × (Fin W × Fin W) → Fin 1000 × (Fin W × Fin W) → ℝ := fun d e =>
    (LiftDeriv_N V d.1 (hermBasis W d.2) *ᵥ x) ⬝ᵥ
      LiftDeriv_dv (pairData g z V (Pi.single e.1 (hermBasis W e.2))) with ha
  set b : Fin 1000 × (Fin W × Fin W) → Fin 1000 × (Fin W × Fin W) → ℝ := fun d e =>
    ((lsqInv (cohRealMat (layoutBlocks liftLayout V)))ᵀ *ᵥ x) ⬝ᵥ
      LiftDeriv_dv (fun j => deriv (fun t : ℝ => pairData g z
        (V + Pi.single d.1 ((t : ℂ) • hermBasis W d.2)) (Pi.single e.1 (hermBasis W e.2)) j) 0)
    with hb
  set c : Fin 1000 × (Fin W × Fin W) → Fin 1000 × (Fin W × Fin W) → ℝ := fun d e =>
    hsInner (LiftDeriv_Td M (LiftDeriv_Cd g d.1 (hermBasis W d.2)))
      (liftKP g z V (Pi.single e.1 (hermBasis W e.2))) with hcdef
  set f : Fin 1000 × (Fin W × Fin W) → Fin 1000 × (Fin W × Fin W) → ℝ := fun d e =>
    hsInner (blockPart M 0 1)
      (LiftDeriv_Cd g d.1 (hermBasis W d.2) *
          (Pi.single e.1 (hermBasis W e.2) : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) 999 *
          liftC g z V 999 +
        liftC g z V 999 *
          (Pi.single e.1 (hermBasis W e.2) : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) 999 *
          LiftDeriv_Cd g d.1 (hermBasis W d.2)) with hf
  have hell : ∀ d e, LiftDeriv_ell g z V M d e =
      (Real.sqrt 2)⁻¹ * g * a d e + (Real.sqrt 2)⁻¹ * g * b d e + c d e + f d e := by
    intro d e
    simp only [LiftDeriv_ell, LiftDeriv_dKP, ha, hb, hcdef, hf, hx]
    ring
  have hsq : ∀ d e, LiftDeriv_ell g z V M d e ^ 2 ≤
      4 * (g ^ 2 / 2 * a d e ^ 2 + g ^ 2 / 2 * b d e ^ 2 + c d e ^ 2 + f d e ^ 2) := by
    intro d e
    rw [hell]
    have e1 : ((Real.sqrt 2)⁻¹ * g * a d e) ^ 2 = g ^ 2 / 2 * a d e ^ 2 := by
      rw [mul_pow, mul_pow, hs]; ring
    have e2 : ((Real.sqrt 2)⁻¹ * g * b d e) ^ 2 = g ^ 2 / 2 * b d e ^ 2 := by
      rw [mul_pow, mul_pow, hs]; ring
    rw [← e1, ← e2]
    nlinarith [sq_nonneg ((Real.sqrt 2)⁻¹ * g * a d e - (Real.sqrt 2)⁻¹ * g * b d e),
      sq_nonneg ((Real.sqrt 2)⁻¹ * g * a d e - c d e),
      sq_nonneg ((Real.sqrt 2)⁻¹ * g * a d e - f d e),
      sq_nonneg ((Real.sqrt 2)⁻¹ * g * b d e - c d e),
      sq_nonneg ((Real.sqrt 2)⁻¹ * g * b d e - f d e), sq_nonneg (c d e - f d e)]
  have hA := LiftDeriv_termA (g := g) (z := z) hc₁ hV hc hF0 hF x
  have hB := LiftDeriv_termB (g := g) (z := z) hc₁ hV hc hD0 hD x
  have hC : ∑ d, ∑ e, c d e ^ 2 ≤
      g ^ 2 / 2 * (F * ((min c₁ 1 ^ 2)⁻¹ * (4 * g⁻¹ ^ 2 * W * hsSq (blockPart M 0 1)))) := by
    calc ∑ d, ∑ e, c d e ^ 2 ≤ ∑ d : Fin 1000 × (Fin W × Fin W), g ^ 2 / 2 * (F *
          ((min c₁ 1 ^ 2)⁻¹ * hsSq (LiftDeriv_Td M (LiftDeriv_Cd g d.1 (hermBasis W d.2))))) :=
          Finset.sum_le_sum fun d _ => LiftDeriv_termC (g := g) (z := z) hc₁ hV hc hF0 hF _
      _ = g ^ 2 / 2 * (F * ((min c₁ 1 ^ 2)⁻¹ * ∑ d : Fin 1000 × (Fin W × Fin W),
          hsSq (LiftDeriv_Td M (LiftDeriv_Cd g d.1 (hermBasis W d.2))))) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      _ ≤ _ := by
          gcongr
          exact LiftDeriv_sum_Td g M
  have hDD := LiftDeriv_termD g M (C0 := liftC g z V 999) hC0
  rw [hxx] at hA hB
  calc ∑ d, ∑ e, LiftDeriv_ell g z V M d e ^ 2
      ≤ ∑ d, ∑ e, 4 * (g ^ 2 / 2 * a d e ^ 2 + g ^ 2 / 2 * b d e ^ 2 + c d e ^ 2 + f d e ^ 2) :=
        Finset.sum_le_sum fun d _ => Finset.sum_le_sum fun e _ => hsq d e
    _ = 4 * (g ^ 2 / 2 * ∑ d, ∑ e, a d e ^ 2 + g ^ 2 / 2 * ∑ d, ∑ e, b d e ^ 2 +
          ∑ d, ∑ e, c d e ^ 2 + ∑ d, ∑ e, f d e ^ 2) := by
        simp only [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ _ := by
        have hg2 : 0 ≤ g ^ 2 / 2 := by positivity
        gcongr

end LiftDerivAssemble

/-- The general lift in the standard coordinates is `C^∞` on the open set where
`S_W(G) > 0` (Section 10 [sec:compact-proof]). -/
theorem contDiffOn_liftField {W : ℕ} (g z : ℝ) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    IsOpen {ω : Ω W 1000 | 0 < coerMin (layoutBlocks liftLayout (gueBlock W 1000 ω))} ∧
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun ω : Ω W 1000 => hermCoord W 1000 (liftField g z (gueBlock W 1000 ω) M))
        {ω : Ω W 1000 | 0 < coerMin (layoutBlocks liftLayout (gueBlock W 1000 ω))} := by
  refine ⟨isOpen_lt continuous_const (LiftDeriv_continuous_coerMin W), ?_⟩
  refine contDiffOn_pi.2 fun p => ?_
  simp only [LiftDeriv_hermCoord_liftField]
  refine contDiffOn_const.mul (contDiffOn_const.mul (LiftDeriv_hsInner_smooth M ?_))
  exact LiftDeriv_Sm_liftK0 g z (fun i => LiftDeriv_Sm_gue _ i) (fun i => LiftDeriv_Sm_const _)
    fun x hx => LiftDeriv_det_ne (fun i => gueBlock_isHermitian W 1000 x i) hx


section LiftDerivCoordDeriv

/-- `hermCoord(ι_i (W^{-1/2} H_α)) = e_{(i, α)}`. -/
private lemma LiftDeriv_hermCoord_single {W : ℕ} (hW : 0 < W) (j : Fin 1000 × Fin W × Fin W) :
    hermCoord W 1000 (Pi.single j.1 ((((Real.sqrt W)⁻¹ : ℝ) : ℂ) • hermBasis W j.2)) =
      Pi.single j 1 := by
  have hs : Real.sqrt W * (Real.sqrt W)⁻¹ = 1 :=
    mul_inv_cancel₀ (Real.sqrt_pos.2 (by exact_mod_cast hW)).ne'
  funext p
  obtain ⟨i, a⟩ := p
  obtain ⟨i', a'⟩ := j
  simp only [hermCoord]
  by_cases hi : i = i'
  · subst hi
    simp only [Pi.single_eq_same, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    rw [trace_hermBasis_mul]
    by_cases ha : a = a'
    · subst ha
      simp only [Complex.ofReal_inv, Prod.mk.eta, ↓reduceIte, mul_one, Complex.inv_re,
        Complex.ofReal_re, Complex.normSq_ofReal, Nat.cast_nonneg, Real.mul_self_sqrt,
        Pi.single_eq_same]
      rw [Real.sqrt_div_self, hs]
    · have : (i, a) ≠ (i, a') := fun h => ha (Prod.ext_iff.1 h).2
      simp [ha, this]
  · have h1 : (Pi.single i' ((((Real.sqrt W)⁻¹ : ℝ) : ℂ) • hermBasis W a') :
        Fin 1000 → Matrix (Fin W) (Fin W) ℂ) i = 0 := by simp [hi]
    have h2 : (i, a) ≠ (i', a') := fun h => hi (Prod.ext_iff.1 h).1
    rw [h1]
    simp [h2]

/-- Moving the standard coordinate `(i, α)` by `t` moves `V_i` by `t W^{-1/2} H_α`. -/
private lemma LiftDeriv_gueBlock_line {W : ℕ} (hW : 0 < W) (ω : Ω W 1000)
    (j : Fin 1000 × Fin W × Fin W) (t : ℝ) :
    gueBlock W 1000 (ω + t • Pi.single j 1) =
      gueBlock W 1000 ω + Pi.single j.1 (((t * (Real.sqrt W)⁻¹ : ℝ) : ℂ) • hermBasis W j.2) := by
  have hX : ∀ l, ((Pi.single j.1 ((((Real.sqrt W)⁻¹ : ℝ) : ℂ) • hermBasis W j.2) :
      Fin 1000 → Matrix (Fin W) (Fin W) ℂ) l).IsHermitian := by
    intro l
    rw [Pi.single_apply]
    split_ifs
    · unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_smul, (hermBasis_isHermitian W j.2).eq, Complex.star_def,
        Complex.conj_ofReal]
    · exact Matrix.isHermitian_zero
  funext i
  rw [← LiftDeriv_hermCoord_single hW j, gueBlock_add_smul_hermCoord hX, Pi.add_apply]
  by_cases hi : i = j.1
  · subst hi
    simp [smul_smul]
  · simp [hi]

private lemma LiftDeriv_W_pos {W : ℕ} {G : Fin 128 → Matrix (Fin W) (Fin W) ℂ} {c₁ : ℝ}
    (hc₁ : 0 < c₁) (hc : c₁ ≤ coerMin G) : 0 < W := by
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW
    have : IsEmpty {P : Matrix (Fin 0) (Fin 0) ℂ // P.trace.im = 0 ∧ hsSq P = 1} :=
      ⟨fun ⟨P, _, h⟩ => by simp [hsSq] at h⟩
    have h0 : coerMin G = 0 := Real.iInf_of_isEmpty _
    linarith
  · exact hW

variable {W : ℕ} {c₁ : ℝ}

/-- The partial derivatives of the standard coordinates of the lift:
`∂_{(i, α)} Y_{(k, β)} = √2 g ℓ((i, α), (k, β))`. -/
private lemma LiftDeriv_fderiv_eq (hc₁ : 0 < c₁) (ω : Ω W 1000)
    (hc : c₁ ≤ coerMin (layoutBlocks liftLayout (gueBlock W 1000 ω))) (g z : ℝ)
    (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (j p : Fin 1000 × Fin W × Fin W) :
    fderiv ℝ (fun η : Ω W 1000 => hermCoord W 1000 (liftField g z (gueBlock W 1000 η) M)) ω
        (Pi.single j 1) p =
      Real.sqrt 2 * g * LiftDeriv_ell g z (gueBlock W 1000 ω) M j p := by
  have hW := LiftDeriv_W_pos hc₁ hc
  have hV : ∀ i, (gueBlock W 1000 ω i).IsHermitian := gueBlock_isHermitian W 1000 ω
  have hU : ω ∈ {ω : Ω W 1000 | 0 < coerMin (layoutBlocks liftLayout (gueBlock W 1000 ω))} :=
    lt_of_lt_of_le hc₁ hc
  obtain ⟨hO, hS⟩ := contDiffOn_liftField (W := W) g z M
  have hdiff := ((hS.contDiffAt (hO.mem_nhds hU)).differentiableAt (by simp)).hasFDerivAt
  set f := fun η : Ω W 1000 => hermCoord W 1000 (liftField g z (gueBlock W 1000 η) M) with hf
  have hline : HasDerivAt (fun t : ℝ => ω + t • (Pi.single j 1 : Ω W 1000))
      (Pi.single j 1 : Ω W 1000) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single j 1 : Ω W 1000)).const_add ω
  have h1 := hasDerivAt_pi.1 (hdiff.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)) p
  set c := (Real.sqrt W)⁻¹ with hcdef
  have hψ := LiftDeriv_hasDerivAt_K0 (g := g) (z := z) hc₁ hV hc j.1 (hermBasis W j.2)
    (Pi.single p.1 (hermBasis W p.2)) M
  have hc' : HasDerivAt (fun t : ℝ => t * c) c 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const c
  have h2 := ((HasDerivAt.comp_of_eq (x := (0 : ℝ)) hψ hc' (by simp)).const_mul
    (Real.sqrt 2 * g)).const_mul (Real.sqrt W)
  have e : (fun t : ℝ => (f ∘ fun t : ℝ => ω + t • (Pi.single j 1 : Ω W 1000)) t p) =
      fun t : ℝ => Real.sqrt W * (Real.sqrt 2 * g *
        ((fun t : ℝ => hsInner M (liftK0 g z (gueBlock W 1000 ω +
          Pi.single j.1 ((t : ℂ) • hermBasis W j.2)) (Pi.single p.1 (hermBasis W p.2)))) ∘
          fun t : ℝ => t * c) t) := by
    funext t
    simp only [Function.comp, hf]
    rw [LiftDeriv_gueBlock_line hW, LiftDeriv_hermCoord_liftField]
  rw [e] at h1
  have := h1.unique h2
  rw [this]
  have hWs : Real.sqrt W * c = 1 := mul_inv_cancel₀ (Real.sqrt_pos.2 (by exact_mod_cast hW)).ne'
  have key : ∀ X : ℝ, Real.sqrt W * (Real.sqrt 2 * g * (X * c)) = Real.sqrt 2 * g * X := by
    intro X
    rw [show Real.sqrt W * (Real.sqrt 2 * g * (X * c)) =
      (Real.sqrt W * c) * (Real.sqrt 2 * g * X) by ring, hWs, one_mul]
  exact key _

end LiftDerivCoordDeriv

section LiftDerivFinal

/-- `|C_i|_op ≤ |z| + g⁻¹ |V_i|_op`. -/
private lemma LiftDeriv_norm_liftC_le {W q : ℕ} {g : ℝ} (hg : 0 < g) (z : ℝ)
    (V : Fin q → Matrix (Fin W) (Fin W) ℂ) (i : Fin q) :
    ‖liftC g z V i‖ ≤ |z| + g⁻¹ * ‖V i‖ := by
  unfold liftC
  have h1 : ‖(z : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ |z| := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (abs_nonneg z)).2 fun j => ?_
    simp
  have h2 : ‖((g : ℂ)⁻¹) • V i‖ = g⁻¹ * ‖V i‖ := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hg.le]
  calc _ ≤ ‖(z : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)‖ + ‖((g : ℂ)⁻¹) • V i‖ := norm_sub_le _ _
    _ ≤ _ := by rw [h2]; linarith

/-- `|C_i|_op ≤ (E₀ + K₁) max{1, g⁻¹}` for `z = max{1, g} E / g`. -/
private lemma LiftDeriv_norm_liftC_cut {W : ℕ} {g E E₀ K₁ : ℝ} (hg : 0 < g) (hE : |E| ≤ E₀)
    {V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ} (hV : ∀ i, ‖V i‖ ≤ K₁) (i : Fin 1000) :
    ‖liftC g (max 1 g * E / g) V i‖ ≤ (E₀ + K₁) * max 1 g⁻¹ := by
  have hE₀ : 0 ≤ E₀ := (abs_nonneg E).trans hE
  have hm : max 1 g / g ≤ max 1 g⁻¹ := by
    rcases le_total g 1 with h | h
    · rw [max_eq_left h, one_div]; exact le_max_right _ _
    · rw [max_eq_right h, div_self hg.ne']; exact le_max_left _ _
  have hz : |max 1 g * E / g| ≤ E₀ * max 1 g⁻¹ := by
    have hpos : 0 < max 1 g := lt_max_of_lt_left one_pos
    rw [abs_div, abs_mul, abs_of_pos hpos, abs_of_pos hg]
    calc max 1 g * |E| / g = (max 1 g / g) * |E| := by ring
      _ ≤ max 1 g⁻¹ * E₀ := mul_le_mul hm hE (abs_nonneg E) (by positivity)
      _ = E₀ * max 1 g⁻¹ := mul_comm _ _
  have hv : g⁻¹ * ‖V i‖ ≤ K₁ * max 1 g⁻¹ := by
    have hK : 0 ≤ K₁ := (norm_nonneg _).trans (hV i)
    calc g⁻¹ * ‖V i‖ ≤ max 1 g⁻¹ * K₁ :=
          mul_le_mul (le_max_right _ _) (hV i) (norm_nonneg _) (by positivity)
      _ = K₁ * max 1 g⁻¹ := mul_comm _ _
  calc _ ≤ |max 1 g * E / g| + g⁻¹ * ‖V i‖ := LiftDeriv_norm_liftC_le hg _ V i
    _ ≤ E₀ * max 1 g⁻¹ + K₁ * max 1 g⁻¹ := add_le_add hz hv
    _ = _ := by ring

private lemma LiftDeriv_herm_liftC {W q : ℕ} (g z : ℝ) {V : Fin q → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ i, (V i).IsHermitian) (i : Fin q) : (liftC g z V i)ᴴ = liftC g z V i := by
  unfold liftC
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, (hV i).eq]
  simp [Complex.conj_ofReal]

private lemma LiftDeriv_hsSq_blocks {W : ℕ} (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    hsSq M = hsSq (blockPart M 0 0) + hsSq (blockPart M 0 1) + hsSq (blockPart M 1 0) +
      hsSq (blockPart M 1 1) := by
  obtain ⟨hM, -⟩ := blockMat_blockPart M 0 0 0 0
  conv_lhs => rw [← hM]
  exact (blockMat_algebra _ _ _ _ 0 0 0 0).2.2.2

/-- `‖M₁₁ + M₁₂ C* + M₁₂* C - M₂₂*‖² ≤ 8 (1 + 2 |C|²_op) ‖M‖²` for Hermitian `C`. -/
private lemma LiftDeriv_hsSq_T_le {W : ℕ} (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    {C : Matrix (Fin W) (Fin W) ℂ} (hC : Cᴴ = C) :
    hsSq (LiftDeriv_T M C) ≤ 8 * (1 + 2 * ‖C‖ ^ 2) * hsSq M := by
  unfold LiftDeriv_T
  rw [hC, LiftDeriv_hsSq_blocks M]
  set A := blockPart M 0 0
  set B := blockPart M 0 1
  set B' := blockPart M 1 0
  set D := blockPart M 1 1
  have h1 := LiftDeriv_hsSq_sub_le (A + B * C + Bᴴ * C) Dᴴ
  have h2 := LiftDeriv_hsSq_add_le (A + B * C) (Bᴴ * C)
  have h3 := LiftDeriv_hsSq_add_le A (B * C)
  have h4 : hsSq (B * C) ≤ ‖C‖ ^ 2 * hsSq B := LiftDeriv_hsSq_mul_le' C B
  have h5 : hsSq (Bᴴ * C) ≤ ‖C‖ ^ 2 * hsSq B := by
    have := LiftDeriv_hsSq_mul_le' C Bᴴ
    rwa [LiftDeriv_hsSq_conjTranspose] at this
  rw [LiftDeriv_hsSq_conjTranspose] at h1
  have hA := LiftDeriv_hsSq_nonneg A
  have hB := LiftDeriv_hsSq_nonneg B
  have hB' := LiftDeriv_hsSq_nonneg B'
  have hD := LiftDeriv_hsSq_nonneg D
  have hC2 : 0 ≤ ‖C‖ ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hC2 hA, mul_nonneg hC2 hB', mul_nonneg hC2 hD]

/-- `g⁴ h⁶ ≤ max{g⁻², g⁴}`, `g² h⁴ ≤ max{g⁻², g⁴}` and `h² ≤ g² h⁴` for `h = max{1, g⁻¹}`. -/
private lemma LiftDeriv_max_bounds {g : ℝ} (hg : 0 < g) :
    g ^ 4 * max 1 g⁻¹ ^ 6 ≤ max (g⁻¹ ^ 2) (g ^ 4) ∧
      g ^ 2 * max 1 g⁻¹ ^ 4 ≤ max (g⁻¹ ^ 2) (g ^ 4) ∧
      max 1 g⁻¹ ^ 2 ≤ g ^ 2 * max 1 g⁻¹ ^ 4 := by
  rcases le_total g 1 with h | h
  · rw [max_eq_right ((one_le_inv₀ hg).2 h)]
    have e1 : g ^ 4 * g⁻¹ ^ 6 = g⁻¹ ^ 2 := by field_simp
    have e2 : g ^ 2 * g⁻¹ ^ 4 = g⁻¹ ^ 2 := by field_simp
    rw [e1, e2]
    exact ⟨le_max_left _ _, le_max_left _ _, le_rfl⟩
  · rw [max_eq_left (inv_le_one_of_one_le₀ h), one_pow, one_pow, one_pow, mul_one, mul_one]
    exact ⟨le_max_right _ _, (pow_le_pow_right₀ h (by norm_num)).trans (le_max_right _ _),
      one_le_pow₀ h⟩

end LiftDerivFinal
/-- (10.26) [eq:c-lift-cost] in the standard coordinates: on `S_W(G) ≥ c₁`,
`max_i ‖V_i‖ ≤ K₁`, `|E| ≤ E₀`, `Σ_{j,p} (∂_j Y_p)² = ‖∇_V X‖²_HS ≤ C W max{g⁻², g⁴} ‖M‖²`. -/
theorem sum_sq_fderiv_liftField_le (E₀ K₁ c₁ : ℝ) (hE₀ : 0 < E₀) (hK₁ : 0 < K₁) (hc₁ : 0 < c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ) (g E : ℝ) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
      (ω : Ω W 1000), 0 < g → |E| ≤ E₀ →
      c₁ ≤ coerMin (layoutBlocks liftLayout (gueBlock W 1000 ω)) →
      (∀ i, ‖gueBlock W 1000 ω i‖ ≤ K₁) →
        ∑ p, ∑ j, (fderiv ℝ (fun η : Ω W 1000 =>
            hermCoord W 1000 (liftField g (max 1 g * E / g) (gueBlock W 1000 η) M)) ω
              (Pi.single j 1) p) ^ 2 ≤
          C * W * max (g⁻¹ ^ 2) (g ^ 4) * hsSq M := by
  obtain ⟨C₁, hC₁, hF1⟩ := hsSq_liftF_le E₀ K₁ hE₀ hK₁
  obtain ⟨C₂, hC₂, hD1⟩ := sum_deriv_pairData_le E₀ K₁ hE₀ hK₁
  set K := E₀ + K₁ with hK
  set τ := min c₁ 1 with hτdef
  have hτ : 0 < τ := lt_min hc₁ one_pos
  refine ⟨65536 * C₁ * (τ ^ 4)⁻¹ * (1 + 2 * K ^ 2) + 32 * C₂ * (τ ^ 2)⁻¹ * (1 + 2 * K ^ 2) +
    16 * C₁ * (τ ^ 2)⁻¹ + 32 * K ^ 2, by positivity, ?_⟩
  intro W g E M ω hg hE hc hVn
  set V := gueBlock W 1000 ω with hVdef
  set z := max 1 g * E / g with hz
  have hV : ∀ i, (V i).IsHermitian := gueBlock_isHermitian W 1000 ω
  have hC0 := LiftDeriv_herm_liftC g z hV 999
  set h := max 1 g⁻¹ with hh
  have h1 : 1 ≤ h := le_max_left _ _
  set S := hsSq M with hS
  have hS0 : 0 ≤ S := LiftDeriv_hsSq_nonneg M
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  set F := C₁ * max 1 (g⁻¹ ^ 4) with hFdef
  set D := C₂ * W * max (g⁻¹ ^ 2) (g⁻¹ ^ 4) with hDdef
  have hF0 : 0 ≤ F := by positivity
  have hD0 : 0 ≤ D := by positivity
  have hsum := LiftDeriv_sum_ell_le (g := g) (z := z) hc₁ hV hc hC0 M hF0
    (fun R => (hF1 W g E V R hg hE hVn).2) hD0 (fun Z => hD1 W g E V Z hg hE hVn)
  have hLHS : ∑ p, ∑ j, (fderiv ℝ (fun η : Ω W 1000 =>
      hermCoord W 1000 (liftField g z (gueBlock W 1000 η) M)) ω (Pi.single j 1) p) ^ 2 =
      2 * g ^ 2 * ∑ d, ∑ e, LiftDeriv_ell g z V M d e ^ 2 := by
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    simp only [LiftDeriv_fderiv_eq hc₁ ω hc g z M, mul_pow, hs2]
    rw [Finset.sum_comm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by rw [Finset.mul_sum]
  rw [hLHS]
  -- the elementary bounds
  set κ := ‖liftC g z V 999‖ with hκ
  have hκK : κ ≤ K * h := LiftDeriv_norm_liftC_cut hg hE hVn 999
  have hκ0 : 0 ≤ κ := norm_nonneg _
  have hK0 : 0 ≤ K := by positivity
  have hκ2 : 1 + 2 * κ ^ 2 ≤ (1 + 2 * K ^ 2) * h ^ 2 := by
    have : κ ^ 2 ≤ K ^ 2 * h ^ 2 := by rw [← mul_pow]; exact pow_le_pow_left₀ hκ0 hκK 2
    have : 1 ≤ h ^ 2 := one_le_pow₀ h1
    nlinarith
  set Tt := hsSq (LiftDeriv_T M (liftC g z V 999)) with hTt
  have hT : Tt ≤ 8 * ((1 + 2 * K ^ 2) * h ^ 2) * S :=
    (LiftDeriv_hsSq_T_le M hC0).trans (by gcongr)
  have hB01 : hsSq (blockPart M 0 1) ≤ S := by
    rw [hS, LiftDeriv_hsSq_blocks M]
    linarith [LiftDeriv_hsSq_nonneg (blockPart M 0 0), LiftDeriv_hsSq_nonneg (blockPart M 1 0),
      LiftDeriv_hsSq_nonneg (blockPart M 1 1)]
  have hF : F ≤ C₁ * h ^ 4 := by
    refine mul_le_mul_of_nonneg_left (max_le (one_le_pow₀ h1) ?_) hC₁.le
    exact pow_le_pow_left₀ (by positivity) (le_max_right _ _) 4
  have hD : D ≤ C₂ * W * (g⁻¹ ^ 2 * h ^ 2) := by
    refine mul_le_mul_of_nonneg_left (max_le ?_ ?_) (by positivity)
    · exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ h1)
    · rw [show g⁻¹ ^ 4 = g⁻¹ ^ 2 * g⁻¹ ^ 2 by ring]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (le_max_right _ _) 2)
        (by positivity)
  have hgg : g ^ 2 * g⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hg.ne', one_pow]
  obtain ⟨m1, m2, m3⟩ := LiftDeriv_max_bounds hg
  set Mx := max (g⁻¹ ^ 2) (g ^ 4) with hMx
  have hτ4 : 0 ≤ (τ ^ 4)⁻¹ := by positivity
  have hτ2 : 0 ≤ (τ ^ 2)⁻¹ := by positivity
  have hTt0 : 0 ≤ Tt := LiftDeriv_hsSq_nonneg _
  have hB0 : 0 ≤ hsSq (blockPart M 0 1) := LiftDeriv_hsSq_nonneg _
  have hg2 : 0 ≤ g ^ 2 := sq_nonneg g
  have hgi : 0 ≤ g⁻¹ ^ 2 := sq_nonneg _
  have tA : 8 * g ^ 2 * (g ^ 2 / 2 * (F * (4 * (512 * W) * (τ ^ 4)⁻¹ * Tt))) ≤
      65536 * C₁ * (τ ^ 4)⁻¹ * (1 + 2 * K ^ 2) * W * Mx * S := by
    calc _ ≤ 8 * g ^ 2 * (g ^ 2 / 2 * (C₁ * h ^ 4 * (4 * (512 * W) * (τ ^ 4)⁻¹ *
          (8 * ((1 + 2 * K ^ 2) * h ^ 2) * S)))) := by gcongr
      _ = 65536 * C₁ * (τ ^ 4)⁻¹ * (1 + 2 * K ^ 2) * W * (g ^ 4 * h ^ 6) * S := by ring
      _ ≤ _ := by gcongr
  have tB : 8 * g ^ 2 * (g ^ 2 / 2 * (D * ((τ ^ 2)⁻¹ * Tt))) ≤
      32 * C₂ * (τ ^ 2)⁻¹ * (1 + 2 * K ^ 2) * W * Mx * S := by
    calc _ ≤ 8 * g ^ 2 * (g ^ 2 / 2 * (C₂ * W * (g⁻¹ ^ 2 * h ^ 2) * ((τ ^ 2)⁻¹ *
          (8 * ((1 + 2 * K ^ 2) * h ^ 2) * S)))) := by gcongr
      _ = 32 * C₂ * (τ ^ 2)⁻¹ * (1 + 2 * K ^ 2) * W * (g ^ 2 * h ^ 4) * (g ^ 2 * g⁻¹ ^ 2) * S := by
          ring
      _ = 32 * C₂ * (τ ^ 2)⁻¹ * (1 + 2 * K ^ 2) * W * (g ^ 2 * h ^ 4) * S := by rw [hgg, mul_one]
      _ ≤ _ := by gcongr
  have tC : 8 * g ^ 2 * (g ^ 2 / 2 * (F * ((τ ^ 2)⁻¹ * (4 * g⁻¹ ^ 2 * W *
      hsSq (blockPart M 0 1))))) ≤ 16 * C₁ * (τ ^ 2)⁻¹ * W * Mx * S := by
    calc _ ≤ 8 * g ^ 2 * (g ^ 2 / 2 * (C₁ * h ^ 4 * ((τ ^ 2)⁻¹ * (4 * g⁻¹ ^ 2 * W * S)))) := by
          gcongr
      _ = 16 * C₁ * (τ ^ 2)⁻¹ * W * (g ^ 2 * h ^ 4) * (g ^ 2 * g⁻¹ ^ 2) * S := by ring
      _ = 16 * C₁ * (τ ^ 2)⁻¹ * W * (g ^ 2 * h ^ 4) * S := by rw [hgg, mul_one]
      _ ≤ _ := by gcongr
  have tD : 8 * g ^ 2 * (4 * g⁻¹ ^ 2 * W * κ ^ 2 * hsSq (blockPart M 0 1)) ≤
      32 * K ^ 2 * W * Mx * S := by
    calc _ ≤ 8 * g ^ 2 * (4 * g⁻¹ ^ 2 * W * (K * h) ^ 2 * S) := by gcongr
      _ = 32 * K ^ 2 * W * h ^ 2 * (g ^ 2 * g⁻¹ ^ 2) * S := by ring
      _ = 32 * K ^ 2 * W * h ^ 2 * S := by rw [hgg, mul_one]
      _ ≤ 32 * K ^ 2 * W * (g ^ 2 * h ^ 4) * S := by gcongr
      _ ≤ _ := by gcongr
  calc 2 * g ^ 2 * ∑ d, ∑ e, LiftDeriv_ell g z V M d e ^ 2
      ≤ 2 * g ^ 2 * (4 * (g ^ 2 / 2 * (F * (4 * (512 * W) * (τ ^ 4)⁻¹ * Tt)) +
        g ^ 2 / 2 * (D * ((τ ^ 2)⁻¹ * Tt)) +
        g ^ 2 / 2 * (F * ((τ ^ 2)⁻¹ * (4 * g⁻¹ ^ 2 * W * hsSq (blockPart M 0 1)))) +
        4 * g⁻¹ ^ 2 * W * κ ^ 2 * hsSq (blockPart M 0 1))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 8 * g ^ 2 * (g ^ 2 / 2 * (F * (4 * (512 * W) * (τ ^ 4)⁻¹ * Tt))) +
        8 * g ^ 2 * (g ^ 2 / 2 * (D * ((τ ^ 2)⁻¹ * Tt))) +
        8 * g ^ 2 * (g ^ 2 / 2 * (F * ((τ ^ 2)⁻¹ * (4 * g⁻¹ ^ 2 * W *
          hsSq (blockPart M 0 1))))) +
        8 * g ^ 2 * (4 * g⁻¹ ^ 2 * W * κ ^ 2 * hsSq (blockPart M 0 1)) := by ring
    _ ≤ _ := by
        have := add_le_add (add_le_add (add_le_add tA tB) tC) tD
        refine this.trans (le_of_eq ?_)
        ring

end LSBA
