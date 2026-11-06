import LSBA.Transfer.StateChain
import LSBA.Gauss.GUEContract

/-!
# Contractions for the increment and the observables

The quadratic forms `A`, `B` in the expansion of the increment and the three contractions of (11.12)
[lg:eq:c2]; the direction terms `y₁, y₂, n₁, n₂` of (11.21) [uvg:eq:fmean], with `𝔼y₂` and `𝔼n₂`
exactly and `|𝔼n₁y₁ − f₁𝔼y₁²| ≤ K/W`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `A = -i (V C - C* V)`, the linear term of `F*F` in the proof of (11.12) [lg:eq:c2]. -/
def quadA {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  -Complex.I • (V * C - Cᴴ * V)

/-- `B = (I + C*) V² (I + C)`, the quadratic term of `F*F` in the proof of (11.12) [lg:eq:c2]. -/
def quadB {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  (1 + Cᴴ) * V ^ 2 * (1 + C)

/-- The coefficient `y_1` of `a = h/g` in `Y = v* F⁻¹ F^{-*} v` (proof of (11.21)
[uvg:eq:fmean]): `i (X - X*)` with `X = V (I + C)`. -/
def dirY1 {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  Complex.I • (V * (1 + C) - (1 + Cᴴ) * V)

/-- The coefficient `y_2` of `a²` in `Y` (proof of (11.21) [uvg:eq:fmean]):
`-X² + X X* - X*²`. -/
def dirY2 {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  -(V * (1 + C)) ^ 2 + V * (1 + C) * ((1 + Cᴴ) * V) - ((1 + Cᴴ) * V) ^ 2

/-- The coefficient `n_1` of `a` in `N = -e^{2iθ} v* F⁻¹ C' F^{-*} v` (proof of (11.21)
[uvg:eq:fmean]): `i (X C + U X - C X*)` with `U = I + C`. -/
def dirN1 {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  Complex.I • (V * (1 + C) * C + (1 + C) * (V * (1 + C)) - C * ((1 + Cᴴ) * V))

/-- The coefficient `n_2` of `a²` in `N` (proof of (11.21) [uvg:eq:fmean]):
`-X² C - U X² - C X*² - X U X + X C X* + U X X*`. -/
def dirN2 {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  -(V * (1 + C)) ^ 2 * C - (1 + C) * (V * (1 + C)) ^ 2 - C * ((1 + Cᴴ) * V) ^ 2 -
    V * (1 + C) * (1 + C) * (V * (1 + C)) + V * (1 + C) * C * ((1 + Cᴴ) * V) +
    (1 + C) * (V * (1 + C)) * ((1 + Cᴴ) * V)

/-- The quadratic form `v* A v` as a dot product of coordinate vectors. -/
private theorem LC_vecForm_eq {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W)) :
    vecForm A v = star (WithLp.ofLp v) ⬝ᵥ (A *ᵥ WithLp.ofLp v) := by
  unfold vecForm
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  simp [Matrix.toLpLin_apply]

/-- Each entry of a GUE block lies in `L²`. -/
private theorem LC_memLp_entry (W : ℕ) (α β : Fin W) :
    MemLp (fun ω => gueBlock W 1 ω 0 α β) 2 (μ W 1) := by
  have hc : ∀ x : Fin 1 × Fin W × Fin W, MemLp (fun ω : Ω W 1 => (ω x : ℂ)) 2 (μ W 1) := by
    intro x
    have h : MemLp id 2 (gaussianReal (0 : ℝ) 1) := memLp_id_gaussianReal' 2 ENNReal.ofNat_ne_top
    have h2 : MemLp (fun ω : Ω W 1 => ω x) 2 (μ W 1) :=
      h.comp_measurePreserving (measurePreserving_eval (fun _ : Fin 1 × Fin W × Fin W =>
        gaussianReal (0 : ℝ) 1) x)
    exact h2.ofReal
  have key : ∀ ω : Ω W 1, gueBlock W 1 ω 0 α β = ((Real.sqrt W : ℝ) : ℂ)⁻¹ *
      ∑ k : Fin W × Fin W, (ω (0, k.1, k.2) : ℂ) * hermBasis W k α β := by
    intro ω
    rw [gueBlock_eq_sum_hermBasis]
    simp [Matrix.smul_apply, Matrix.sum_apply]
  simp_rw [key]
  refine MemLp.const_mul ?_ _
  exact memLp_finsetSum _ fun (k : Fin W × Fin W) _ => (hc (0, k.1, k.2)).mul_const _

/-- The bilinear form `x* V w` of a GUE block lies in `L²`. -/
private theorem LC_memLp_bil (W : ℕ) (x w : Fin W → ℂ) :
    MemLp (fun ω => star x ⬝ᵥ (gueBlock W 1 ω 0 *ᵥ w)) 2 (μ W 1) := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
  exact memLp_finsetSum _ fun i _ => (memLp_finsetSum _ fun j _ =>
    (LC_memLp_entry W i j).mul_const (w j)).const_mul _

/-- The product of two bilinear forms `x* V w` of a GUE block is integrable. -/
private theorem LC_integrable_bil_mul (W : ℕ) (x w p q : Fin W → ℂ) :
    Integrable (fun ω => (star x ⬝ᵥ (gueBlock W 1 ω 0 *ᵥ w)) *
      (star p ⬝ᵥ (gueBlock W 1 ω 0 *ᵥ q))) (μ W 1) :=
  (LC_memLp_bil W x w).integrable_mul (LC_memLp_bil W p q)

/-- `x* V Z V w` as a sum over the standard basis of products of two bilinear forms `x* V w`. -/
private theorem LC_pointwise (W : ℕ) (Z : Matrix (Fin W) (Fin W) ℂ) (x w : Fin W → ℂ)
    (V : Matrix (Fin W) (Fin W) ℂ) :
    star x ⬝ᵥ (V *ᵥ (Z *ᵥ (V *ᵥ w))) =
      ∑ δ, (star x ⬝ᵥ (V *ᵥ (Z *ᵥ (fun j => if δ = j then (1 : ℂ) else 0)))) *
        (star (fun j => if δ = j then (1 : ℂ) else 0) ⬝ᵥ (V *ᵥ w)) := by
  conv_lhs => rw [pi_eq_sum_univ (V *ᵥ w)]
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [mul_comm]
  congr 1
  simp [dotProduct, Pi.star_apply]

/-- `𝔼 x* V Z V w = W⁻¹ Tr(Z) x* w` for one GUE block, together with integrability. -/
private theorem LC_core (W : ℕ) (Z : Matrix (Fin W) (Fin W) ℂ) (x w : Fin W → ℂ) :
    (∫ ω, star x ⬝ᵥ (gueBlock W 1 ω 0 *ᵥ (Z *ᵥ (gueBlock W 1 ω 0 *ᵥ w))) ∂(μ W 1)) =
      (W : ℂ)⁻¹ * Z.trace * (star x ⬝ᵥ w) ∧
    Integrable (fun ω => star x ⬝ᵥ (gueBlock W 1 ω 0 *ᵥ (Z *ᵥ (gueBlock W 1 ω 0 *ᵥ w))))
      (μ W 1) := by
  simp_rw [LC_pointwise W Z x w]
  refine ⟨?_, integrable_finsetSum _ fun δ _ => LC_integrable_bil_mul W _ _ _ _⟩
  rw [integral_finsetSum _ fun δ _ => LC_integrable_bil_mul W _ _ _ _]
  have h : ∀ δ : Fin W, ∫ ω, (star x ⬝ᵥ (gueBlock W 1 ω 0 *ᵥ
          (Z *ᵥ (fun j => if δ = j then (1 : ℂ) else 0)))) *
        (star (fun j => if δ = j then (1 : ℂ) else 0) ⬝ᵥ (gueBlock W 1 ω 0 *ᵥ w)) ∂(μ W 1) =
      (W : ℂ)⁻¹ * (star x ⬝ᵥ w) * Z δ δ := by
    intro δ
    rw [integral_dotProduct_gueBlock_mul]
    congr 1
    simp [dotProduct, Matrix.mulVec]
  simp_rw [h]
  rw [Matrix.trace]
  simp only [Matrix.diag, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun δ _ => by ring


/-- `𝔼 v* P V Z V R v = W⁻¹ Tr(Z) v* P R v` for one GUE block, together with integrability. -/
private theorem LC_integral_vecForm (W : ℕ) (P Z R : Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W)) :
    (∫ ω, vecForm (P * (gueBlock W 1 ω 0 * Z * gueBlock W 1 ω 0) * R) v ∂(μ W 1)) =
      (W : ℂ)⁻¹ * Z.trace * vecForm (P * R) v ∧
    Integrable (fun ω => vecForm (P * (gueBlock W 1 ω 0 * Z * gueBlock W 1 ω 0) * R) v)
      (μ W 1) := by
  have hpt : ∀ V : Matrix (Fin W) (Fin W) ℂ, vecForm (P * (V * Z * V) * R) v =
      star (Pᴴ *ᵥ WithLp.ofLp v) ⬝ᵥ (V *ᵥ (Z *ᵥ (V *ᵥ (R *ᵥ WithLp.ofLp v)))) := by
    intro V
    rw [LC_vecForm_eq, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose,
      Matrix.dotProduct_mulVec ]
    simp [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, mul_assoc]
  simp_rw [hpt]
  obtain ⟨h1, h2⟩ := LC_core W Z (Pᴴ *ᵥ WithLp.ofLp v) (R *ᵥ WithLp.ofLp v)
  refine ⟨h1.trans ?_, h2⟩
  rw [LC_vecForm_eq, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

/-- `v* (∑ A_k) v = ∑ v* A_k v`. -/
private theorem LC_vecForm_sum {W n : ℕ} (A : Fin n → Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W)) : vecForm (∑ k, A k) v = ∑ k, vecForm (A k) v := by
  simp [LC_vecForm_eq, Matrix.sum_mulVec, dotProduct_sum]

/-- `𝔼 v* F(V) v` for a matrix `F(V) = ∑_k P_k V Z_k V R_k`, from the one-term identity. -/
private theorem LC_integral_vecForm_sum {W n : ℕ} (P Z R : Fin n → Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W))
    (F : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ)
    (hF : ∀ V, F V = ∑ k, P k * (V * Z k * V) * R k) :
    ∫ ω, vecForm (F (gueBlock W 1 ω 0)) v ∂(μ W 1) =
      ∑ k, (W : ℂ)⁻¹ * (Z k).trace * vecForm (P k * R k) v := by
  simp_rw [hF, LC_vecForm_sum]
  rw [integral_finsetSum _ fun k _ => (LC_integral_vecForm W (P k) (Z k) (R k) v).2]
  exact Finset.sum_congr rfl fun k _ => (LC_integral_vecForm W (P k) (Z k) (R k) v).1

/-- `v* (A + B) v = v* A v + v* B v`. -/
private theorem LC_vecForm_add {W : ℕ} (A B : Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W)) : vecForm (A + B) v = vecForm A v + vecForm B v := by
  simp [LC_vecForm_eq, Matrix.add_mulVec, dotProduct_add]

/-- `v* (A - B) v = v* A v - v* B v`. -/
private theorem LC_vecForm_sub {W : ℕ} (A B : Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W)) : vecForm (A - B) v = vecForm A v - vecForm B v := by
  simp [LC_vecForm_eq, Matrix.sub_mulVec, dotProduct_sub]

/-- `v* (-A) v = -v* A v`. -/
private theorem LC_vecForm_neg {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W)) : vecForm (-A) v = -vecForm A v := by
  simp [LC_vecForm_eq, Matrix.neg_mulVec, dotProduct_neg]

/-- `v* v = 1` for a unit vector. -/
private theorem LC_vecForm_one {W : ℕ} {v : EuclideanSpace ℂ (Fin W)} (hv : ‖v‖ = 1) :
    vecForm (1 : Matrix (Fin W) (Fin W) ℂ) v = 1 := by
  unfold vecForm
  have h1 : Matrix.toEuclideanLin (1 : Matrix (Fin W) (Fin W) ℂ) v = v := by simp
  rw [h1, inner_self_eq_norm_sq_to_K, hv]
  simp


/-- A state matrix `C` satisfies `C C* = C* C = 1`. -/
private theorem LC_unitary {W : ℕ} {X : State W} (hX : IsState X) :
    X.1 * X.1ᴴ = 1 ∧ X.1ᴴ * X.1 = 1 := by
  have h1 := Matrix.mem_unitaryGroup_iff.mp hX.1
  have h2 := Matrix.mem_unitaryGroup_iff'.mp hX.1
  rw [Matrix.star_eq_conjTranspose] at h1 h2
  exact ⟨h1, h2⟩

/-- `C⁻¹ = C*` for a state matrix `C`. -/
private theorem LC_inv_eq {W : ℕ} {X : State W} (hX : IsState X) : X.1⁻¹ = X.1ᴴ := by
  apply Matrix.inv_eq_right_inv
  exact (LC_unitary hX).1

/-- The traces and quadratic forms of `C`, `C*`, `C²` at a state in terms of `m_k`, `f_k` of (11.10)
[lg:eq:observables]. -/
private theorem LC_obs {W : ℕ} (hW : 1 ≤ W) {X : State W} (hX : IsState X) :
    X.1.trace = W * obsM 1 X ∧ X.1ᴴ.trace = W * obsM (-1) X ∧
      (X.1 * X.1).trace = W * obsM 2 X ∧
      vecForm X.1 X.2 = obsF 1 X ∧ vecForm X.1ᴴ X.2 = obsF (-1) X ∧
      vecForm (X.1 * X.1) X.2 = obsF 2 X ∧ obsM (-1) X = star (obsM 1 X) ∧
      obsF (-1) X = star (obsF 1 X) := by
  have hW0 : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have e1 : X.1 ^ (1 : ℤ) = X.1 := zpow_one _
  have e2 : X.1 ^ (-1 : ℤ) = X.1ᴴ := by rw [zpow_neg_one, LC_inv_eq hX]
  have e3 : X.1 ^ (2 : ℤ) = X.1 * X.1 := zpow_two _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, (obsM_zero_neg hW hX 1).2, (obsF_zero_neg hX 1).2⟩
  · unfold obsM; rw [e1]; field_simp
  · unfold obsM; rw [e2]; field_simp
  · unfold obsM; rw [e3]; field_simp
  · unfold obsF; rw [e1]
  · unfold obsF; rw [e2]
  · unfold obsF; rw [e3]

/-- The bilinear form `x* V w` of a matrix `V`. -/
private def LC_bil {W : ℕ} (V : Matrix (Fin W) (Fin W) ℂ) (x w : EuclideanSpace ℂ (Fin W)) : ℂ :=
  star (WithLp.ofLp x) ⬝ᵥ (V *ᵥ WithLp.ofLp w)

/-- The coordinates of `A w` are `A` applied to the coordinates of `w`. -/
private theorem LC_ofLp_lin {W : ℕ} (M : Matrix (Fin W) (Fin W) ℂ) (w : EuclideanSpace ℂ (Fin W)) :
    WithLp.ofLp (Matrix.toEuclideanLin M w) = M *ᵥ WithLp.ofLp w := by
  simp [Matrix.toLpLin_apply]

/-- `v* P V Q v = (P* v)* V (Q v)`. -/
private theorem LC_vecForm_PVQ {W : ℕ} (P V Q : Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W)) :
    vecForm (P * V * Q) v =
      LC_bil V (Matrix.toEuclideanLin Pᴴ v) (Matrix.toEuclideanLin Q v) := by
  unfold LC_bil
  rw [LC_vecForm_eq, LC_ofLp_lin, LC_ofLp_lin, Matrix.star_mulVec,
    Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- The product of two bilinear forms of a GUE block is integrable. -/
private theorem LC_integrable_bil {W : ℕ} (x w p q : EuclideanSpace ℂ (Fin W)) :
    Integrable (fun ω => LC_bil (gueBlock W 1 ω 0) x w * LC_bil (gueBlock W 1 ω 0) p q)
      (μ W 1) :=
  LC_integrable_bil_mul W _ _ _ _

/-- `𝔼 (x* V w)(p* V q) = W⁻¹ (x* q)(p* w)` for one GUE block, in Euclidean vectors. -/
private theorem LC_integral_bil {W : ℕ} (x w p q : EuclideanSpace ℂ (Fin W)) :
    ∫ ω, LC_bil (gueBlock W 1 ω 0) x w * LC_bil (gueBlock W 1 ω 0) p q ∂(μ W 1) =
      (W : ℂ)⁻¹ * (star (WithLp.ofLp x) ⬝ᵥ WithLp.ofLp q) *
        (star (WithLp.ofLp p) ⬝ᵥ WithLp.ofLp w) :=
  integral_dotProduct_gueBlock_mul W _ _ _ _

/-- `|x* y| ≤ ‖x‖ ‖y‖`. -/
private theorem LC_norm_dot_le {W : ℕ} (x y : EuclideanSpace ℂ (Fin W)) :
    ‖star (WithLp.ofLp x) ⬝ᵥ WithLp.ofLp y‖ ≤ ‖x‖ * ‖y‖ := by
  have h := norm_inner_le_norm (𝕜 := ℂ) x y
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
  exact h

/-- `‖𝔼 (∑_i c_i x_i* V w_i)(∑_j d_j p_j* V q_j)‖ ≤ (∑ ‖c_i‖)(∑ ‖d_j‖) 16 / W` when all vectors
have norm at most `2`. -/
private theorem LC_bound {W m n : ℕ} (c : Fin m → ℂ) (x w : Fin m → EuclideanSpace ℂ (Fin W))
    (d : Fin n → ℂ) (p q : Fin n → EuclideanSpace ℂ (Fin W))
    (hx : ∀ i, ‖x i‖ ≤ 2) (hw : ∀ i, ‖w i‖ ≤ 2) (hp : ∀ j, ‖p j‖ ≤ 2) (hq : ∀ j, ‖q j‖ ≤ 2) :
    ‖∫ ω, (∑ i, c i * LC_bil (gueBlock W 1 ω 0) (x i) (w i)) *
        (∑ j, d j * LC_bil (gueBlock W 1 ω 0) (p j) (q j)) ∂(μ W 1)‖ ≤
      (∑ i, ‖c i‖) * (∑ j, ‖d j‖) * (16 / W) := by
  have hterm : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω =>
      (c i * LC_bil (gueBlock W 1 ω 0) (x i) (w i)) *
        (d j * LC_bil (gueBlock W 1 ω 0) (p j) (q j))) (μ W 1) := by
    intro i j
    have := (LC_integrable_bil (x i) (w i) (p j) (q j)).const_mul (c i * d j)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    ring
  simp_rw [Finset.sum_mul_sum]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hterm i j]
  simp_rw [integral_finsetSum _ fun j _ => hterm _ j]
  have hij : ∀ (i : Fin m) (j : Fin n), ‖∫ ω, (c i * LC_bil (gueBlock W 1 ω 0) (x i) (w i)) *
        (d j * LC_bil (gueBlock W 1 ω 0) (p j) (q j)) ∂(μ W 1)‖ ≤ ‖c i‖ * ‖d j‖ * (16 / W) := by
    intro i j
    have e : ∫ ω, (c i * LC_bil (gueBlock W 1 ω 0) (x i) (w i)) *
        (d j * LC_bil (gueBlock W 1 ω 0) (p j) (q j)) ∂(μ W 1) =
        (c i * d j) * ((W : ℂ)⁻¹ * (star (WithLp.ofLp (x i)) ⬝ᵥ WithLp.ofLp (q j)) *
          (star (WithLp.ofLp (p j)) ⬝ᵥ WithLp.ofLp (w i))) := by
      rw [← LC_integral_bil, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only
      ring
    rw [e, norm_mul, norm_mul, norm_mul, norm_mul, norm_inv, Complex.norm_natCast]
    have h1 := LC_norm_dot_le (x i) (q j)
    have h2 := LC_norm_dot_le (p j) (w i)
    have h3 : ‖star (WithLp.ofLp (x i)) ⬝ᵥ WithLp.ofLp (q j)‖ *
        ‖star (WithLp.ofLp (p j)) ⬝ᵥ WithLp.ofLp (w i)‖ ≤ 16 := by
      calc _ ≤ (‖x i‖ * ‖q j‖) * (‖p j‖ * ‖w i‖) := mul_le_mul h1 h2 (norm_nonneg _)
            (by positivity)
        _ ≤ (2 * 2) * (2 * 2) := by
          gcongr
          · exact hx i
          · exact hq j
          · exact hp j
          · exact hw i
        _ = 16 := by norm_num
    calc ‖c i‖ * ‖d j‖ * ((W : ℝ)⁻¹ * ‖star (WithLp.ofLp (x i)) ⬝ᵥ WithLp.ofLp (q j)‖ *
        ‖star (WithLp.ofLp (p j)) ⬝ᵥ WithLp.ofLp (w i)‖)
        = ‖c i‖ * ‖d j‖ * ((W : ℝ)⁻¹ * (‖star (WithLp.ofLp (x i)) ⬝ᵥ WithLp.ofLp (q j)‖ *
        ‖star (WithLp.ofLp (p j)) ⬝ᵥ WithLp.ofLp (w i)‖)) := by ring
      _ ≤ ‖c i‖ * ‖d j‖ * ((W : ℝ)⁻¹ * 16) := by gcongr
      _ = ‖c i‖ * ‖d j‖ * (16 / W) := by rw [div_eq_inv_mul]
  calc _ ≤ ∑ i, ‖∑ j, ∫ ω, (c i * LC_bil (gueBlock W 1 ω 0) (x i) (w i)) *
        (d j * LC_bil (gueBlock W 1 ω 0) (p j) (q j)) ∂(μ W 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖∫ ω, (c i * LC_bil (gueBlock W 1 ω 0) (x i) (w i)) *
        (d j * LC_bil (gueBlock W 1 ω 0) (p j) (q j)) ∂(μ W 1)‖ :=
      Finset.sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖c i‖ * ‖d j‖ * (16 / W) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hij i j
    _ = (∑ i, ∑ j, ‖c i‖ * ‖d j‖) * (16 / W) := by simp only [Finset.sum_mul]


/-- `v* (c A) v = c v* A v`. -/
private theorem LC_vecForm_smul {W : ℕ} (c : ℂ) (A : Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W)) : vecForm (c • A) v = c * vecForm A v := by
  simp [LC_vecForm_eq, Matrix.smul_mulVec, dotProduct_smul]



/-- `(A B) w = A (B w)`. -/
private theorem LC_lin_mul {W : ℕ} (A B : Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W)) :
    Matrix.toEuclideanLin (A * B) v = Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

/-- A unitary matrix preserves the Euclidean norm. -/
private theorem LC_norm_lin_unitary {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin W) ℂ) (v : EuclideanSpace ℂ (Fin W)) :
    ‖Matrix.toEuclideanLin U v‖ = ‖v‖ := by
  have hUU : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  have h : inner ℂ (Matrix.toEuclideanLin U v) (Matrix.toEuclideanLin U v) = inner ℂ v v := by
    rw [← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      ← LC_lin_mul, hUU]
    simp
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖Matrix.toEuclideanLin U v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h'

/-- `‖(1 + N) w‖ ≤ 2 ‖w‖` for unitary `N`. -/
private theorem LC_norm_one_add {W : ℕ} {N : Matrix (Fin W) (Fin W) ℂ}
    (hN : N ∈ Matrix.unitaryGroup (Fin W) ℂ) (w : EuclideanSpace ℂ (Fin W)) :
    ‖Matrix.toEuclideanLin (1 + N) w‖ ≤ 2 * ‖w‖ := by
  have h : Matrix.toEuclideanLin (1 + N) w = w + Matrix.toEuclideanLin N w := by simp
  rw [h]
  calc ‖w + Matrix.toEuclideanLin N w‖ ≤ ‖w‖ + ‖Matrix.toEuclideanLin N w‖ := norm_add_le _ _
    _ = 2 * ‖w‖ := by rw [LC_norm_lin_unitary hN]; ring

/-- `‖(1 + N) N' w‖ ≤ 2 ‖w‖` for unitary `N`, `N'`. -/
private theorem LC_norm_one_add_mul {W : ℕ} {N N' : Matrix (Fin W) (Fin W) ℂ}
    (hN : N ∈ Matrix.unitaryGroup (Fin W) ℂ) (hN' : N' ∈ Matrix.unitaryGroup (Fin W) ℂ)
    (w : EuclideanSpace ℂ (Fin W)) :
    ‖Matrix.toEuclideanLin ((1 + N) * N') w‖ ≤ 2 * ‖w‖ := by
  rw [LC_lin_mul]
  calc _ ≤ 2 * ‖Matrix.toEuclideanLin N' w‖ := LC_norm_one_add hN _
    _ = 2 * ‖w‖ := by rw [LC_norm_lin_unitary hN']

/-- The conjugate transpose of a unitary matrix is unitary. -/
private theorem LC_mem_conjTranspose {W : ℕ} {N : Matrix (Fin W) (Fin W) ℂ}
    (hN : N ∈ Matrix.unitaryGroup (Fin W) ℂ) : Nᴴ ∈ Matrix.unitaryGroup (Fin W) ℂ := by
  rw [← Matrix.star_eq_conjTranspose]
  exact Unitary.star_mem hN

/-- `v* n_1 v` as a combination of three bilinear forms `x* V w`. -/
private theorem LC_vf_n1 {W : ℕ} (V C : Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W)) :
    vecForm (dirN1 C V) v =
      ∑ i : Fin 3, ![Complex.I, Complex.I, -Complex.I] i *
        LC_bil V (![v, Matrix.toEuclideanLin (1 + Cᴴ) v,
          Matrix.toEuclideanLin ((1 + C) * Cᴴ) v] i)
          (![Matrix.toEuclideanLin ((1 + C) * C) v, Matrix.toEuclideanLin (1 + C) v, v] i) := by
  have e1 : vecForm (V * (1 + C) * C) v = LC_bil V v (Matrix.toEuclideanLin ((1 + C) * C) v) := by
    rw [show V * (1 + C) * C = 1 * V * ((1 + C) * C) by simp [mul_assoc], LC_vecForm_PVQ]
    simp
  have e2 : vecForm ((1 + C) * (V * (1 + C))) v =
      LC_bil V (Matrix.toEuclideanLin (1 + Cᴴ) v) (Matrix.toEuclideanLin (1 + C) v) := by
    rw [show (1 + C) * (V * (1 + C)) = (1 + C) * V * (1 + C) by simp [mul_assoc],
      LC_vecForm_PVQ]
    simp
  have e3 : vecForm (C * ((1 + Cᴴ) * V)) v =
      LC_bil V (Matrix.toEuclideanLin ((1 + C) * Cᴴ) v) v := by
    rw [show C * ((1 + Cᴴ) * V) = (C * (1 + Cᴴ)) * V * 1 by simp [mul_assoc],
      LC_vecForm_PVQ]
    simp
  rw [dirN1, LC_vecForm_smul, LC_vecForm_sub, LC_vecForm_add, e1, e2, e3]
  simp [Fin.sum_univ_succ]
  ring

/-- `v* y_1 v` as a combination of two bilinear forms `x* V w`. -/
private theorem LC_vf_y1 {W : ℕ} (V C : Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W)) :
    vecForm (dirY1 C V) v =
      ∑ i : Fin 2, ![Complex.I, -Complex.I] i *
        LC_bil V (![v, Matrix.toEuclideanLin (1 + C) v] i)
          (![Matrix.toEuclideanLin (1 + C) v, v] i) := by
  have e1 : vecForm (V * (1 + C)) v = LC_bil V v (Matrix.toEuclideanLin (1 + C) v) := by
    rw [show V * (1 + C) = 1 * V * (1 + C) by simp, LC_vecForm_PVQ]
    simp
  have e2 : vecForm ((1 + Cᴴ) * V) v = LC_bil V (Matrix.toEuclideanLin (1 + C) v) v := by
    rw [show (1 + Cᴴ) * V = (1 + Cᴴ) * V * 1 by simp, LC_vecForm_PVQ]
    simp
  rw [dirY1, LC_vecForm_smul, LC_vecForm_sub, e1, e2]
  simp [Fin.sum_univ_succ]
  ring

/-- `𝔼 v* B v = 2 + 2 Re f_1` (proof of (11.12) [lg:eq:c2]). -/
theorem integral_vecForm_quadB {W : ℕ} (hW : 1 ≤ W) {X : State W} (hX : IsState X) :
    ∫ ω, vecForm (quadB X.1 (gueBlock W 1 ω 0)) X.2 ∂(μ W 1) = 2 + 2 * ((obsF 1 X).re : ℂ) := by
  have hW0 : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨hCD, hDC⟩ := LC_unitary hX
  obtain ⟨-, -, -, hf1, hff, -, -, hfc⟩ := LC_obs hW hX
  have h1 := LC_vecForm_one hX.2
  have key := LC_integral_vecForm_sum (n := 1) ![1 + X.1ᴴ] ![1] ![1 + X.1] X.2 (quadB X.1)
    (fun V => by simp [quadB, pow_two])
  rw [key]
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Matrix.cons_val_zero, Matrix.trace_one, Fintype.card_fin]
  simp only [mul_one, add_mul, mul_add, one_mul, hDC, LC_vecForm_add, h1, hf1, hff, hfc]
  have hre : ((obsF 1 X).re : ℂ) = (obsF 1 X + star (obsF 1 X)) / 2 := by
    rw [Complex.star_def]; exact Complex.re_eq_add_conj _
  rw [hre]
  simp only [inv_mul_cancel₀ hW0]
  ring

/-- `𝔼 v* A² v = 2 - 2 Re(m_1 f_1)` (proof of (11.12) [lg:eq:c2]). -/
theorem integral_vecForm_quadA_sq {W : ℕ} (hW : 1 ≤ W) {X : State W} (hX : IsState X) :
    ∫ ω, vecForm (quadA X.1 (gueBlock W 1 ω 0) ^ 2) X.2 ∂(μ W 1) =
      2 - 2 * ((obsM 1 X * obsF 1 X).re : ℂ) := by
  have hW0 : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨hCD, hDC⟩ := LC_unitary hX
  obtain ⟨hm1, hmm, -, hf1, hff, -, hmc, hfc⟩ := LC_obs hW hX
  have h1 := LC_vecForm_one hX.2
  have hA : ∀ V : Matrix (Fin W) (Fin W) ℂ, quadA X.1 V ^ 2 =
      ∑ k : Fin 4, ![-1, 1, X.1ᴴ, -X.1ᴴ] k * (V * ![X.1, X.1 * X.1ᴴ, 1, X.1ᴴ] k * V) *
        ![X.1, 1, X.1, 1] k := by
    intro V
    simp only [quadA, pow_two, Matrix.smul_mul, Matrix.mul_smul, smul_smul, neg_mul_neg,
      Complex.I_mul_I]
    simp only [neg_smul, one_smul, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.sum_univ_succ,
      Finset.univ_eq_empty, Finset.sum_empty, add_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ]
    noncomm_ring
  have key := LC_integral_vecForm_sum (n := 4) ![-1, 1, X.1ᴴ, -X.1ᴴ] ![X.1, X.1 * X.1ᴴ, 1, X.1ᴴ]
    ![X.1, 1, X.1, 1] X.2 (fun V => quadA X.1 V ^ 2) hA
  rw [key]
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  simp only [neg_mul, one_mul, mul_one, hCD, hDC, LC_vecForm_neg, h1, hf1, hff, Matrix.trace_one,
    Fintype.card_fin, hm1, hmm, hmc, hfc, inv_mul_cancel_left₀ hW0, inv_mul_cancel₀ hW0]
  have hre : ((obsM 1 X * obsF 1 X).re : ℂ) =
      (obsM 1 X * obsF 1 X + star (obsM 1 X) * star (obsF 1 X)) / 2 := by
    rw [Complex.re_eq_add_conj]; simp
  rw [hre]
  ring

/-- `𝔼 (v* A v)² = 2 W⁻¹ (1 - Re f_1²)` (proof of (11.12) [lg:eq:c2]). -/
theorem integral_sq_vecForm_quadA {W : ℕ} (hW : 1 ≤ W) {X : State W} (hX : IsState X) :
    ∫ ω, vecForm (quadA X.1 (gueBlock W 1 ω 0)) X.2 ^ 2 ∂(μ W 1) =
      2 * (W : ℂ)⁻¹ * (1 - ((obsF 1 X ^ 2).re : ℂ)) := by
  obtain ⟨hCD, hDC⟩ := LC_unitary hX
  obtain ⟨-, -, -, hf1, -, -, -, -⟩ := LC_obs hW hX
  have h1 := LC_vecForm_one hX.2
  have hpt : ∀ V : Matrix (Fin W) (Fin W) ℂ, vecForm (quadA X.1 V) X.2 ^ 2 =
      -(LC_bil V X.2 (Matrix.toEuclideanLin X.1 X.2) *
          LC_bil V X.2 (Matrix.toEuclideanLin X.1 X.2)) +
        2 * (LC_bil V X.2 (Matrix.toEuclideanLin X.1 X.2) *
          LC_bil V (Matrix.toEuclideanLin X.1 X.2) X.2) -
        LC_bil V (Matrix.toEuclideanLin X.1 X.2) X.2 *
          LC_bil V (Matrix.toEuclideanLin X.1 X.2) X.2 := by
    intro V
    have e1 : vecForm (V * X.1) X.2 = LC_bil V X.2 (Matrix.toEuclideanLin X.1 X.2) := by
      have := LC_vecForm_PVQ 1 V X.1 X.2
      simpa using this
    have e2 : vecForm (X.1ᴴ * V) X.2 = LC_bil V (Matrix.toEuclideanLin X.1 X.2) X.2 := by
      have := LC_vecForm_PVQ X.1ᴴ V 1 X.2
      simpa using this
    rw [quadA, LC_vecForm_smul, LC_vecForm_sub, e1, e2]
    ring_nf
    simp [Complex.I_sq]
    ring
  simp_rw [hpt]
  have i1 := LC_integrable_bil (W := W) X.2 (Matrix.toEuclideanLin X.1 X.2) X.2
    (Matrix.toEuclideanLin X.1 X.2)
  have i2 := LC_integrable_bil (W := W) X.2 (Matrix.toEuclideanLin X.1 X.2)
    (Matrix.toEuclideanLin X.1 X.2) X.2
  have i3 := LC_integrable_bil (W := W) (Matrix.toEuclideanLin X.1 X.2) X.2
    (Matrix.toEuclideanLin X.1 X.2) X.2
  have i1' : Integrable (fun ω : Ω W 1 =>
      -(LC_bil (gueBlock W 1 ω 0) X.2 (Matrix.toEuclideanLin X.1 X.2) *
          LC_bil (gueBlock W 1 ω 0) X.2 (Matrix.toEuclideanLin X.1 X.2))) (μ W 1) := i1.neg
  have i12 : Integrable (fun ω : Ω W 1 =>
      -(LC_bil (gueBlock W 1 ω 0) X.2 (Matrix.toEuclideanLin X.1 X.2) *
          LC_bil (gueBlock W 1 ω 0) X.2 (Matrix.toEuclideanLin X.1 X.2)) +
        2 * (LC_bil (gueBlock W 1 ω 0) X.2 (Matrix.toEuclideanLin X.1 X.2) *
          LC_bil (gueBlock W 1 ω 0) (Matrix.toEuclideanLin X.1 X.2) X.2)) (μ W 1) :=
    i1'.add (i2.const_mul 2)
  rw [integral_sub i12 i3, integral_add i1' (i2.const_mul 2), integral_neg,
    integral_const_mul, LC_integral_bil, LC_integral_bil, LC_integral_bil]
  have eu : star (WithLp.ofLp X.2) ⬝ᵥ WithLp.ofLp X.2 = 1 := by
    have := h1
    rw [LC_vecForm_eq, Matrix.one_mulVec] at this
    exact this
  have ef : star (WithLp.ofLp X.2) ⬝ᵥ (X.1 *ᵥ WithLp.ofLp X.2) = obsF 1 X := by
    rw [← hf1, LC_vecForm_eq]
  have ep : star (X.1 *ᵥ WithLp.ofLp X.2) ⬝ᵥ (X.1 *ᵥ WithLp.ofLp X.2) = 1 := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hDC,
      Matrix.one_mulVec]
    exact eu
  have ec : star (X.1 *ᵥ WithLp.ofLp X.2) ⬝ᵥ WithLp.ofLp X.2 = star (obsF 1 X) := by
    rw [Matrix.star_dotProduct, ef]
  simp only [LC_ofLp_lin, eu, ef, ep, ec]
  have hre : ((obsF 1 X ^ 2).re : ℂ) = (obsF 1 X ^ 2 + star (obsF 1 X) ^ 2) / 2 := by
    rw [Complex.re_eq_add_conj]; simp
  rw [hre]
  ring

/-- `𝔼 y_2 = -[(1 + m_1) f_1 + (1 + m_{-1}) f_{-1}]` (proof of (11.21) [uvg:eq:fmean]). -/
theorem integral_vecForm_dirY2 {W : ℕ} (hW : 1 ≤ W) {X : State W} (hX : IsState X) :
    ∫ ω, vecForm (dirY2 X.1 (gueBlock W 1 ω 0)) X.2 ∂(μ W 1) =
      -((1 + obsM 1 X) * obsF 1 X + (1 + obsM (-1) X) * obsF (-1) X) := by
  have hW0 : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨hCD, hDC⟩ := LC_unitary hX
  obtain ⟨hm1, hmm, hm2, hf1, hff, hf2, hmc, hfc⟩ := LC_obs hW hX
  have h1 := LC_vecForm_one hX.2
  have hA : ∀ V : Matrix (Fin W) (Fin W) ℂ, dirY2 X.1 V =
      ∑ k : Fin 3, ![-1, 1, -(1 + X.1ᴴ)] k * (V * ![1 + X.1, (1 + X.1) * (1 + X.1ᴴ),
        1 + X.1ᴴ] k * V) * ![1 + X.1, 1, 1] k := by
    intro V
    simp only [dirY2, pow_two]
    simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Nat.succ_eq_add_one, Nat.reduceAdd, neg_add_rev]
    noncomm_ring
  have key := LC_integral_vecForm_sum (n := 3) ![-1, 1, -(1 + X.1ᴴ)]
    ![1 + X.1, (1 + X.1) * (1 + X.1ᴴ), 1 + X.1ᴴ] ![1 + X.1, 1, 1] X.2
    (dirY2 X.1) hA
  rw [key]
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  simp only [Matrix.trace_add, Matrix.trace_one, Fintype.card_fin, add_mul, mul_add, mul_one,
    one_mul, neg_mul, hCD, LC_vecForm_add, LC_vecForm_neg, h1, hf1, hff, hm1, hmm]
  field_simp
  ring

/-- `𝔼 n_2 = -(3 + 4 m_1 + m_2) f_1 - 2 (1 + m_1) f_2` (proof of (11.21) [uvg:eq:fmean]). -/
theorem integral_vecForm_dirN2 {W : ℕ} (hW : 1 ≤ W) {X : State W} (hX : IsState X) :
    ∫ ω, vecForm (dirN2 X.1 (gueBlock W 1 ω 0)) X.2 ∂(μ W 1) =
      -(3 + 4 * obsM 1 X + obsM 2 X) * obsF 1 X - 2 * (1 + obsM 1 X) * obsF 2 X := by
  have hW0 : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨hCD, hDC⟩ := LC_unitary hX
  obtain ⟨hm1, hmm, hm2, hf1, hff, hf2, hmc, hfc⟩ := LC_obs hW hX
  have h1 := LC_vecForm_one hX.2
  have hA : ∀ V : Matrix (Fin W) (Fin W) ℂ, dirN2 X.1 V =
      ∑ k : Fin 6, ![-1, -(1 + X.1), -(X.1 * (1 + X.1ᴴ)), -1, 1, 1 + X.1] k *
        (V * ![1 + X.1, 1 + X.1, 1 + X.1ᴴ, (1 + X.1) * (1 + X.1), (1 + X.1) * X.1 * (1 + X.1ᴴ),
          (1 + X.1) * (1 + X.1ᴴ)] k * V) *
        ![(1 + X.1) * X.1, 1 + X.1, 1, 1 + X.1, 1, 1] k := by
    intro V
    simp only [dirN2, pow_two]
    simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, neg_mul, Nat.succ_eq_add_one, Nat.reduceAdd,
      neg_add_rev]
    noncomm_ring
  have key := LC_integral_vecForm_sum (n := 6)
    ![-1, -(1 + X.1), -(X.1 * (1 + X.1ᴴ)), -1, 1, 1 + X.1]
    ![1 + X.1, 1 + X.1, 1 + X.1ᴴ, (1 + X.1) * (1 + X.1), (1 + X.1) * X.1 * (1 + X.1ᴴ),
      (1 + X.1) * (1 + X.1ᴴ)]
    ![(1 + X.1) * X.1, 1 + X.1, 1, 1 + X.1, 1, 1] X.2 (dirN2 X.1) hA
  rw [key]
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  simp only [Matrix.trace_add, Matrix.trace_one, Fintype.card_fin, mul_assoc, add_mul, mul_add,
    mul_one, one_mul, neg_mul, hCD, LC_vecForm_add, LC_vecForm_neg, h1, hf1, hf2, hm1, hmm,
    hm2]
  field_simp
  ring

/-- `𝔼(n_1 y_1) - f_1 𝔼 y_1² = O(W⁻¹)` (proof of (11.21) [uvg:eq:fmean]). -/
theorem norm_integral_dirN1_dirY1_sub_le :
    ∃ K : ℝ, 0 < K ∧ ∀ W : ℕ, 1 ≤ W → ∀ X : State W, IsState X →
      ‖(∫ ω, vecForm (dirN1 X.1 (gueBlock W 1 ω 0)) X.2 * vecForm (dirY1 X.1 (gueBlock W 1 ω 0)) X.2
          ∂(μ W 1)) -
        obsF 1 X * ∫ ω, vecForm (dirY1 X.1 (gueBlock W 1 ω 0)) X.2 ^ 2 ∂(μ W 1)‖ ≤ K / W := by
  refine ⟨160, by norm_num, fun W hW X hX => ?_⟩
  have hCu := hX.1
  have hCh := LC_mem_conjTranspose hCu
  have hv : ‖X.2‖ = 1 := hX.2
  have hn1 : ‖Matrix.toEuclideanLin (1 + X.1ᴴ) X.2‖ ≤ 2 := by
    simpa [hv] using LC_norm_one_add hCh X.2
  have hn2 : ‖Matrix.toEuclideanLin (1 + X.1) X.2‖ ≤ 2 := by
    simpa [hv] using LC_norm_one_add hCu X.2
  have hn3 : ‖Matrix.toEuclideanLin ((1 + X.1) * X.1ᴴ) X.2‖ ≤ 2 := by
    simpa [hv] using LC_norm_one_add_mul hCu hCh X.2
  have hn4 : ‖Matrix.toEuclideanLin ((1 + X.1) * X.1) X.2‖ ≤ 2 := by
    simpa [hv] using LC_norm_one_add_mul hCu hCu X.2
  have hv2 : ‖X.2‖ ≤ 2 := by rw [hv]; norm_num
  have hNY := LC_bound (W := W) ![Complex.I, Complex.I, -Complex.I]
    ![X.2, Matrix.toEuclideanLin (1 + X.1ᴴ) X.2, Matrix.toEuclideanLin ((1 + X.1) * X.1ᴴ) X.2]
    ![Matrix.toEuclideanLin ((1 + X.1) * X.1) X.2, Matrix.toEuclideanLin (1 + X.1) X.2, X.2]
    ![Complex.I, -Complex.I] ![X.2, Matrix.toEuclideanLin (1 + X.1) X.2]
    ![Matrix.toEuclideanLin (1 + X.1) X.2, X.2]
    (by intro i; fin_cases i; exacts [hv2, hn1, hn3])
    (by intro i; fin_cases i; exacts [hn4, hn2, hv2])
    (by intro j; fin_cases j; exacts [hv2, hn2])
    (by intro j; fin_cases j; exacts [hn2, hv2])
  have hYY := LC_bound (W := W) ![Complex.I, -Complex.I]
    ![X.2, Matrix.toEuclideanLin (1 + X.1) X.2] ![Matrix.toEuclideanLin (1 + X.1) X.2, X.2]
    ![Complex.I, -Complex.I] ![X.2, Matrix.toEuclideanLin (1 + X.1) X.2]
    ![Matrix.toEuclideanLin (1 + X.1) X.2, X.2]
    (by intro i; fin_cases i; exacts [hv2, hn2])
    (by intro i; fin_cases i; exacts [hn2, hv2])
    (by intro j; fin_cases j; exacts [hv2, hn2])
    (by intro j; fin_cases j; exacts [hn2, hv2])
  simp only [← LC_vf_n1, ← LC_vf_y1, ← sq] at hNY hYY
  have hs3 : ∑ i : Fin 3, ‖(![Complex.I, Complex.I, -Complex.I] : Fin 3 → ℂ) i‖ = 3 := by
    simp [Fin.sum_univ_succ]
    norm_num
  have hs2 : ∑ j : Fin 2, ‖(![Complex.I, -Complex.I] : Fin 2 → ℂ) j‖ = 2 := by
    simp [Fin.sum_univ_succ]
    norm_num
  rw [hs3, hs2] at hNY
  rw [hs2] at hYY
  have hf := norm_obsF_le_one 1 hX
  have hfy : ‖obsF 1 X * ∫ ω, vecForm (dirY1 X.1 (gueBlock W 1 ω 0)) X.2 ^ 2 ∂(μ W 1)‖ ≤
      1 * (2 ^ 2 * (16 / (W : ℝ))) := by
    rw [norm_mul]
    exact mul_le_mul hf hYY (norm_nonneg _) zero_le_one
  calc _ ≤ ‖∫ ω, vecForm (dirN1 X.1 (gueBlock W 1 ω 0)) X.2 *
        vecForm (dirY1 X.1 (gueBlock W 1 ω 0)) X.2 ∂(μ W 1)‖ +
        ‖obsF 1 X * ∫ ω, vecForm (dirY1 X.1 (gueBlock W 1 ω 0)) X.2 ^ 2 ∂(μ W 1)‖ :=
        norm_sub_le _ _
    _ ≤ 3 * 2 * (16 / (W : ℝ)) + 1 * (2 ^ 2 * (16 / (W : ℝ))) := add_le_add hNY hfy
    _ = 160 / W := by ring

end LSBA
