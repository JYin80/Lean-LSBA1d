import LSBA.Flow.LemmaN
import LSBA.Prop.Step1
import LSBA.Flow.Moment

/-!
# Step 2 of the one-step propagation

Step 2 of Appendix C.3 [sec:gc-one-step] at each deterministic time: the mixed pair after the
mixed-pair bound, with loss `R^6`, and the sharp local law.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Cyclic distance -/

private lemma step2_mod {L x y : ℕ} (hx : x < L) (hy : y < L) :
    (x + L - y) % L = if y ≤ x then x - y else x + L - y := by
  split_ifs with h
  · have : x + L - y = (x - y) + L := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

/-- The cyclic distance is symmetric. -/
private lemma step2_cycDist_comm {L : ℕ} (a b : Fin L) : cycDist a b = cycDist b a := by
  unfold cycDist; exact min_comm _ _

/-- A sum over `Fin L` along an injection into `{0, …, L-1}` is bounded by the full sum. -/
private lemma step2_sum_inj {L : ℕ} (g : Fin L → ℕ) (hg : Function.Injective g)
    (hlt : ∀ b, g b < L) (h : ℕ → ℝ) (h0 : ∀ j, 0 ≤ h j) :
    ∑ b, h (g b) ≤ ∑ j ∈ Finset.range L, h j := by
  rw [← Finset.sum_image (f := h) (s := Finset.univ) (g := g) (fun x _ y _ hxy => hg hxy)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hj
    obtain ⟨b, hb⟩ := hj
    rw [Finset.mem_range, ← hb]
    exact hlt b
  · intro i _ _
    exact h0 i

/-- For a nonnegative function of the distance, the sum over the cycle is at most twice the sum
over `{0, …, L-1}`. -/
private lemma step2_sum_dist {L : ℕ} (a : Fin L) (h : ℕ → ℝ) (h0 : ∀ j, 0 ≤ h j) :
    ∑ b, h (cycDist a b) ≤ 2 * ∑ j ∈ Finset.range L, h j := by
  have ha := a.isLt
  have h1 : ∑ b : Fin L, h ((a.val + L - b.val) % L) ≤ ∑ j ∈ Finset.range L, h j := by
    apply step2_sum_inj (fun b : Fin L => (a.val + L - b.val) % L) _ _ h h0
    · intro b b' hbb
      have hb := b.isLt
      have hb' := b'.isLt
      simp only [step2_mod ha hb, step2_mod ha hb'] at hbb
      apply Fin.ext
      split_ifs at hbb <;> omega
    · intro b
      exact Nat.mod_lt _ (by omega)
  have h2 : ∑ b : Fin L, h ((b.val + L - a.val) % L) ≤ ∑ j ∈ Finset.range L, h j := by
    apply step2_sum_inj (fun b : Fin L => (b.val + L - a.val) % L) _ _ h h0
    · intro b b' hbb
      have hb := b.isLt
      have hb' := b'.isLt
      simp only [step2_mod hb ha, step2_mod hb' ha] at hbb
      apply Fin.ext
      split_ifs at hbb <;> omega
    · intro b
      exact Nat.mod_lt _ (by omega)
  have h3 : ∀ b : Fin L, h (cycDist a b) ≤
      h ((a.val + L - b.val) % L) + h ((b.val + L - a.val) % L) := by
    intro b
    unfold cycDist
    rcases min_choice ((a.val + L - b.val) % L) ((b.val + L - a.val) % L) with e | e
    · rw [e]; linarith [h0 ((b.val + L - a.val) % L)]
    · rw [e]; linarith [h0 ((a.val + L - b.val) % L)]
  calc ∑ b, h (cycDist a b) ≤ ∑ b : Fin L, (h ((a.val + L - b.val) % L) +
        h ((b.val + L - a.val) % L)) := Finset.sum_le_sum fun b _ => h3 b
    _ ≤ 2 * ∑ j ∈ Finset.range L, h j := by
        rw [Finset.sum_add_distrib]; linarith

/-! ### Hilbert–Schmidt and operator norms of blocks -/

section LinAlg

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Squared Hilbert–Schmidt norm `Σ_{ij} |A_{ij}|²`. -/
private def step2_hs (A : Matrix n n ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

/-- `‖A u‖² ≤ ‖A‖² ‖u‖²` for the operator norm. -/
private lemma step2_nsq_le (A : Matrix n n ℂ) (u : n → ℂ) :
    ∑ i, ‖(A *ᵥ u) i‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ i, ‖u i‖ ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 u)
  have h1 : ‖(EuclideanSpace.equiv n ℂ).symm (A *ᵥ u)‖ ^ 2 = ∑ i, ‖(A *ᵥ u) i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  have h2 : ‖(WithLp.toLp 2 u : EuclideanSpace ℂ n)‖ ^ 2 = ∑ i, ‖u i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
  rw [← h1, ← h2, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- `‖Y X‖²_HS ≤ ‖Y‖² ‖X‖²_HS`. -/
private lemma step2_hs_mul_left (Y X : Matrix n n ℂ) :
    step2_hs (Y * X) ≤ ‖Y‖ ^ 2 * step2_hs X := by
  unfold step2_hs
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => ‖X i j‖ ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h := step2_nsq_le Y (fun i => X i j)
  have e : (Y *ᵥ fun i => X i j) = fun i => (Y * X) i j := by
    funext i; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  rw [e] at h
  exact h

omit [DecidableEq n] in
private lemma step2_hs_conjTranspose (X : Matrix n n ℂ) :
    step2_hs Xᴴ = step2_hs X := by
  unfold step2_hs
  rw [Finset.sum_comm]
  simp [Matrix.conjTranspose_apply]

omit [DecidableEq n] in
/-- `‖A + B‖²_HS ≤ 2‖A‖²_HS + 2‖B‖²_HS`. -/
private lemma step2_hs_add_le (A B : Matrix n n ℂ) :
    step2_hs (A + B) ≤ 2 * step2_hs A + 2 * step2_hs B := by
  unfold step2_hs
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Matrix.add_apply]
  have h := norm_add_le (A i j) (B i j)
  have h0 := norm_nonneg (A i j + B i j)
  nlinarith [sq_nonneg (‖A i j‖ - ‖B i j‖), norm_nonneg (A i j), norm_nonneg (B i j)]

omit [DecidableEq n] in
private lemma step2_hs_smul (k : ℂ) (A : Matrix n n ℂ) :
    step2_hs (k • A) = ‖k‖ ^ 2 * step2_hs A := by
  unfold step2_hs
  simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

omit [DecidableEq n] in
/-- `Tr(Z Z*) = ‖Z‖²_HS`. -/
private lemma step2_trace_mul_conjTranspose (Z : Matrix n n ℂ) :
    (Z * Zᴴ).trace = ((step2_hs Z : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    step2_hs]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj']

end LinAlg

section BlockAlg

variable {W L : ℕ}

/-- `(X E_a Y)_{cd} = W⁻¹ X_{ca} Y_{ad}`. -/
private lemma step2_blockOf_mul_blockE_mul (X Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a c d : Fin L) :
    blockOf (X * blockE W L a * Y) c d = (W : ℂ)⁻¹ • (blockOf X c a * blockOf Y a d) := by
  ext α β
  simp only [blockOf, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
  simp only [blockE, Matrix.mul_diagonal, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun γ _ => ?_
    simp only [ite_true, Matrix.of_apply]; ring
  · intro e _ he; simp [he]
  · simp

/-- `Tr(Y E_z) = W⁻¹ Tr Y_{zz}`. -/
private lemma step2_trace_mul_blockE (Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (z : Fin L) : (Y * blockE W L z).trace = (W : ℂ)⁻¹ * (blockOf Y z z).trace := by
  simp only [Matrix.trace, Matrix.diag, blockE, Matrix.mul_diagonal, blockOf, Matrix.of_apply,
    Fintype.sum_prod_type, Finset.mul_sum]
  rw [Finset.sum_eq_single z]
  · refine Finset.sum_congr rfl fun γ _ => ?_
    simp only [ite_true]; ring
  · intro e _ he; simp [he]
  · simp

private lemma step2_blockOf_conjTranspose (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (e f : Fin L) : blockOf Xᴴ e f = (blockOf X f e)ᴴ := by
  ext α β; simp [blockOf, Matrix.conjTranspose_apply]

private lemma step2_hs_blockOf (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (e f : Fin L) : step2_hs (blockOf X e f) = blockHS2 X e f := by
  simp [step2_hs, blockHS2, blockOf]

end BlockAlg

section Step2Near

variable {W L : ℕ}


/-- At most `2(H + 1)` labels lie within distance `H ≥ 0` of a given label. -/
private lemma step2_near_count (a : Fin L) {H : ℝ} (hH : 0 ≤ H) :
    ∑ c : Fin L, (if (cycDist a c : ℝ) ≤ H then (1 : ℝ) else 0) ≤ 2 * (H + 1) := by
  have h := step2_sum_dist a (fun j => if (j : ℝ) ≤ H then (1 : ℝ) else 0)
    (fun j => by split_ifs <;> norm_num)
  refine h.trans ?_
  have h2 : ∑ j ∈ Finset.range L, (if (j : ℝ) ≤ H then (1 : ℝ) else 0) ≤ H + 1 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hsub : (Finset.range L).filter (fun j : ℕ => (j : ℝ) ≤ H) ⊆
        Finset.range (⌊H⌋₊ + 1) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
      have := Nat.le_floor hj.2
      omega
    have h3 := Finset.card_le_card hsub
    rw [Finset.card_range] at h3
    have h4 : ((((Finset.range L).filter (fun j : ℕ => (j : ℝ) ≤ H)).card : ℕ) : ℝ) ≤
        (⌊H⌋₊ : ℝ) + 1 := by exact_mod_cast h3
    have h5 := Nat.floor_le hH
    linarith
  linarith

end Step2Near

/-! ### Bracket row -/

section BracketRow

open scoped Matrix.Norms.L2Operator

variable {W L : ℕ}

/-- `‖X Y‖²_HS ≤ ‖Y‖² ‖X‖²_HS`. -/
private lemma step2_hs_mul_right {n : Type*} [Fintype n] [DecidableEq n]
    (X Y : Matrix n n ℂ) : step2_hs (X * Y) ≤ ‖Y‖ ^ 2 * step2_hs X := by
  have h := step2_hs_mul_left Yᴴ Xᴴ
  rwa [← Matrix.conjTranspose_mul, step2_hs_conjTranspose, Matrix.l2_opNorm_conjTranspose,
    step2_hs_conjTranspose] at h

/-- `‖A B C‖²_HS ≤ ‖A‖² ‖C‖² ‖B‖²_HS`. -/
private lemma step2_hs_three {n : Type*} [Fintype n] [DecidableEq n]
    (A B C : Matrix n n ℂ) :
    step2_hs (A * (B * C)) ≤ ‖A‖ ^ 2 * ‖C‖ ^ 2 * step2_hs B := by
  calc step2_hs (A * (B * C)) ≤ ‖A‖ ^ 2 * step2_hs (B * C) :=
        step2_hs_mul_left _ _
    _ ≤ ‖A‖ ^ 2 * (‖C‖ ^ 2 * step2_hs B) :=
        mul_le_mul_of_nonneg_left (step2_hs_mul_right _ _) (by positivity)
    _ = _ := by ring

/-- The diagonal block of `X E_a (Y E_b Z)` is `W⁻² X_{ca} Y_{ab} Z_{bc}`. -/
private lemma step2_blockOf_five (X Y Z : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b c : Fin L) :
    blockOf (X * blockE W L a * (Y * blockE W L b * Z)) c c =
      ((W : ℂ)⁻¹ * (W : ℂ)⁻¹) • (blockOf X c a * (blockOf Y a b * blockOf Z b c)) := by
  rw [step2_blockOf_mul_blockE_mul, step2_blockOf_mul_blockE_mul, Matrix.mul_smul,
    smul_smul]

private lemma step2_blockOf_add (X Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (c d : Fin L) : blockOf (X + Y) c d = blockOf X c d + blockOf Y c d := by
  ext α β; simp [blockOf]

/-- `‖Z_{cc}‖²_HS ≤ 4W⁻⁴ ‖G_{ca}‖² ‖G_{bc}‖² ‖G_{ba}‖²_HS` for the bracket matrix `Z`. -/
private lemma step2_hs_Z (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b c : Fin L) :
    step2_hs (blockOf (G * blockE W L a * (Gᴴ * blockE W L b * G) +
        Gᴴ * blockE W L b * (G * blockE W L a * Gᴴ)) c c) ≤
      4 * ((W : ℝ)⁻¹) ^ 4 * (‖blockOf G c a‖ ^ 2 * ‖blockOf G b c‖ ^ 2 * blockHS2 G b a) := by
  rw [step2_blockOf_add, step2_blockOf_five, step2_blockOf_five]
  refine (step2_hs_add_le _ _).trans ?_
  rw [step2_hs_smul, step2_hs_smul]
  have hk : ‖(W : ℂ)⁻¹ * (W : ℂ)⁻¹‖ ^ 2 = ((W : ℝ)⁻¹) ^ 4 := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]; ring
  rw [hk]
  have h0 := step2_hs_three (blockOf G c a) (blockOf Gᴴ a b) (blockOf G b c)
  have h1 := step2_hs_three (blockOf Gᴴ c b) (blockOf G b a) (blockOf Gᴴ a c)
  have e0 : step2_hs (blockOf Gᴴ a b) = blockHS2 G b a := by
    rw [step2_blockOf_conjTranspose, step2_hs_conjTranspose, step2_hs_blockOf]
  have e1 : ∀ x y, ‖blockOf Gᴴ x y‖ = ‖blockOf G y x‖ := fun x y => by
    rw [step2_blockOf_conjTranspose, Matrix.l2_opNorm_conjTranspose]
  rw [e0] at h0
  rw [e1, e1, step2_hs_blockOf] at h1
  have hW4 : (0 : ℝ) ≤ ((W : ℝ)⁻¹) ^ 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h0 hW4, mul_le_mul_of_nonneg_left h1 hW4]

/-- `Tr(P_c Z P_c Z*) = ‖Z_{cc}‖²_HS` with `P_c = W E_c`. -/
private lemma step2_trace_proj (hW : 1 ≤ W) (c : Fin L)
    (Z : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    (((W : ℂ) • blockE W L c) * Z * ((W : ℂ) • blockE W L c) * Zᴴ).trace =
      ((step2_hs (blockOf Z c c) : ℝ) : ℂ) := by
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast (by omega : W ≠ 0)
  have e : ((W : ℂ) • blockE W L c) * Z * ((W : ℂ) • blockE W L c) * Zᴴ =
      ((W : ℂ) * W) • (blockE W L c * (Z * blockE W L c * Zᴴ)) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [e, Matrix.trace_smul, Matrix.trace_mul_comm, step2_trace_mul_blockE,
    step2_blockOf_mul_blockE_mul, Matrix.trace_smul, step2_blockOf_conjTranspose,
    step2_trace_mul_conjTranspose, smul_eq_mul, smul_eq_mul]
  field_simp

/-- The bracket of `ℒ₂(a,b;+,-)` with itself is `(γ/W) Σ_c ‖Z_{cc}‖²_HS` with
`Z = G E_a G* E_b G + G* E_b G E_a G*`. -/
private lemma step2_gamma_eq (g E : ℝ) (m : ℂ) (hm : 0 < m.im) (hW : 1 ≤ W) {u : ℝ}
    (hu : u < 1) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    (a b : Fin L) :
    blockGamma W L (gammaG g) (resLoop g E m ![a, b] ![true, false] u)
        (resLoop g E m ![a, b] ![true, false] u) M =
      ((gammaG g / W : ℝ) : ℂ) * ∑ c, ((step2_hs (blockOf
        (resolventMat M (zChar g E m u) * blockE W L a *
            ((resolventMat M (zChar g E m u))ᴴ * blockE W L b * resolventMat M (zChar g E m u)) +
          (resolventMat M (zChar g E m u))ᴴ * blockE W L b *
            (resolventMat M (zChar g E m u) * blockE W L a * (resolventMat M (zChar g E m u))ᴴ))
        c c) : ℝ) : ℂ) := by
  rw [blockGamma_loopTr g E m hm hu hM]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  set G := resolventMat M (zChar g E m u)
  have hB0 : loopB G ![a, b] ![true, false] 0 = G * blockE W L a * (Gᴴ * blockE W L b * G) := by
    simp [loopB, List.ofFn_succ, sgnMat, Matrix.mul_assoc]
  have hB1 : loopB G ![a, b] ![true, false] 1 = Gᴴ * blockE W L b * (G * blockE W L a * Gᴴ) := by
    simp [loopB, List.ofFn_succ, sgnMat, Matrix.mul_assoc]
  rw [← step2_trace_proj hW c]
  simp only [Fin.sum_univ_two, hB0, hB1, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul,
    Matrix.trace_add]
  ring

end BracketRow

private theorem step2_weight_pos (c θ F : ℝ) {W : ℕ} (hW : 1 ≤ W) (ℓ r : ℝ) :
    0 < weightFn c θ F W ℓ r := by
  unfold weightFn
  have : (0 : ℝ) < W := by exact_mod_cast hW
  positivity

private theorem step2_weight_ge (c θ F : ℝ) {W : ℕ} (ℓ r : ℝ) :
    (W : ℝ) ^ (-F) ≤ weightFn c θ F W ℓ r := by
  unfold weightFn
  linarith [Real.exp_pos (-(c * (r / ℓ) ^ θ))]

private theorem step2_weight_le_two {c θ F : ℝ} (hc : 0 ≤ c) (hF : 0 ≤ F) {W : ℕ} (hW : 1 ≤ W)
    {ℓ r : ℝ} (hℓ : 0 < ℓ) (hr : 0 ≤ r) : weightFn c θ F W ℓ r ≤ 2 := by
  unfold weightFn
  have h1 : Real.exp (-(c * (r / ℓ) ^ θ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (r / ℓ) ^ θ := Real.rpow_nonneg (div_nonneg hr hℓ.le) θ
    nlinarith
  have h2 : (W : ℝ) ^ (-F) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hW) (by linarith)
  linarith

/-- The weight decreases in the profile constant. -/
private theorem step2_weight_anti_c {c c' θ F : ℝ} (hcc : c ≤ c') {W : ℕ} {ℓ r : ℝ}
    (hℓ : 0 < ℓ) (hr : 0 ≤ r) :
    weightFn c' θ F W ℓ r ≤ weightFn c θ F W ℓ r := by
  unfold weightFn
  have h0 : 0 ≤ (r / ℓ) ^ θ := Real.rpow_nonneg (div_nonneg hr hℓ.le) θ
  have : c * (r / ℓ) ^ θ ≤ c' * (r / ℓ) ^ θ := mul_le_mul_of_nonneg_right hcc h0
  gcongr

/-- The weight decreases in the floor exponent. -/
private theorem step2_weight_anti_F {c θ F F' : ℝ} (hFF : F ≤ F') {W : ℕ} (hW : 1 ≤ W)
    (ℓ r : ℝ) : weightFn c θ F' W ℓ r ≤ weightFn c θ F W ℓ r := by
  unfold weightFn
  have : (W : ℝ) ^ (-F') ≤ (W : ℝ) ^ (-F) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hW) (by linarith)
  linarith

/-! ### Matrices -/

open scoped Matrix.Norms.L2Operator in
/-- The operator norm of a square block is at most its Hilbert–Schmidt norm. -/
private theorem step2_opNorm_le_hs {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : ‖A‖ ≤ Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [mul_pow, Real.sq_sqrt (by positivity), EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  simp only [Matrix.ofLp_toEuclideanCLM]
  have h : ∀ i, ‖(A *ᵥ x.ofLp) i‖ ^ 2 ≤ (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x.ofLp j‖ ^ 2 := by
    intro i
    have h1 : ‖(A *ᵥ x.ofLp) i‖ ≤ ∑ j, ‖A i j‖ * ‖x.ofLp j‖ := by
      simp only [Matrix.mulVec, dotProduct]
      exact (norm_sum_le _ _).trans (by simp)
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖A i j‖)
      (fun j => ‖x.ofLp j‖)
    calc _ ≤ (∑ j, ‖A i j‖ * ‖x.ofLp j‖) ^ 2 := by gcongr
      _ ≤ _ := h2
  calc ∑ i, ‖(A *ᵥ x.ofLp) i‖ ^ 2 ≤ ∑ i, (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x.ofLp j‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => h i
    _ = _ := by rw [Finset.sum_mul]

open scoped Matrix.Norms.L2Operator in
/-- `‖G_{xy}‖ ≤ ‖G_{xy}‖_HS`. -/
private theorem step2_blockOf_le_hs {W L : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : ‖blockOf X a b‖ ≤ Real.sqrt (blockHS2 X a b) := by
  refine (step2_opNorm_le_hs _).trans (le_of_eq ?_)
  rfl

/-- `ℒ₂(a, b; +, -) = W⁻² ‖G_{ba}‖²_HS`. -/
private theorem step2_loopTr_two_hs {W L : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) :
    loopTr X ![a, b] ![true, false] = ((((W : ℝ) ^ 2)⁻¹ * blockHS2 X b a : ℝ) : ℂ) := by
  rw [loopTr_two]
  rfl

/-- The length-one loops against `m^σ` are the centered block traces. -/
private theorem step2_loop_one_sub (g E : ℝ) (W L : ℕ) (hW : 1 ≤ W) (hL : 1 ≤ L) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (c : Fin L) (s : Bool) :
    ‖loopTr G ![c] ![s] - sgnScalar m s‖ =
      ‖blockTr (G - dysonMat (hopB g) (gammaG g) L E m ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) c c‖ := by
  have hM := loopTr_one_dysonMat g E W L hW hL m hm c true
  simp only [ite_true] at hM
  have hbt : ∀ X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ,
      blockTr X c c = loopTr X ![c] ![true] := by
    intro X; rw [loopTr_one]; rfl
  have hsub : blockTr (G - dysonMat (hopB g) (gammaG g) L E m ⊗ₖ
      (1 : Matrix (Fin W) (Fin W) ℂ)) c c = loopTr G ![c] ![true] - m := by
    have e : blockTr (G - dysonMat (hopB g) (gammaG g) L E m ⊗ₖ
        (1 : Matrix (Fin W) (Fin W) ℂ)) c c = blockTr G c c -
          blockTr (dysonMat (hopB g) (gammaG g) L E m ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) c c := by
      unfold blockTr
      simp only [Matrix.sub_apply, Finset.sum_sub_distrib, mul_sub]
    rw [e, hbt G, hbt, hM]
  rw [hsub]
  cases s
  · have h1 : loopTr G ![c] ![false] = star (loopTr G ![c] ![true]) := by
      rw [loopTr_one]
      have : loopTr G ![c] ![false] = loopTr Gᴴ ![c] ![true] := by simp [loopTr, sgnMat]
      rw [this, loopTr_one]
      simp [Matrix.conjTranspose_apply, star_sum]
    rw [h1, sgnScalar]
    simp only [Bool.false_eq_true, ite_false]
    rw [← star_sub, norm_star]
  · simp [sgnScalar]

/-- The Dyson matrix is symmetric. -/
private theorem step2_dysonMat_symm (b β : ℝ) (L : ℕ) (z m : ℂ) (i j : Fin L) :
    dysonMat b β L z m i j = dysonMat b β L z m j i := by
  have hA : (cycleAdj L).transpose = cycleAdj L := by
    ext i j
    simp only [Matrix.transpose_apply, cycleAdj, Matrix.of_apply]
    rw [add_comm]
  have h : (dysonMat b β L z m).transpose = dysonMat b β L z m := by
    unfold dysonMat
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_smul, Matrix.transpose_one, hA]
  conv_lhs => rw [← h]
  rfl

/-- The mixed kernel of a symmetric matrix is symmetric. -/
private theorem step2_mixedKer_symm {L : ℕ} (P : Matrix (Fin L) (Fin L) ℝ)
    (hP : ∀ a b, P a b = P b a) (u : ℝ) (a b : Fin L) :
    mixedKer P u a b = mixedKer P u b a := by
  have hPt : P.transpose = P := by ext i j; exact (hP j i)
  set B := (1 : Matrix (Fin L) (Fin L) ℝ) - u • P with hB
  have hBt : B.transpose = B := by
    rw [hB, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hPt]
  have hcomm : P * B = B * P := by
    rw [hB, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  have hinv : P * B⁻¹ = B⁻¹ * P := by
    by_cases hd : IsUnit B.det
    · calc P * B⁻¹ = B⁻¹ * B * (P * B⁻¹) := by rw [Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
        _ = B⁻¹ * (B * P) * B⁻¹ := by simp only [Matrix.mul_assoc]
        _ = B⁻¹ * (P * B) * B⁻¹ := by rw [hcomm]
        _ = B⁻¹ * P * (B * B⁻¹) := by simp only [Matrix.mul_assoc]
        _ = B⁻¹ * P := by rw [Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    · rw [Matrix.nonsing_inv_apply_not_isUnit _ hd, Matrix.mul_zero, Matrix.zero_mul]
  have hK : (mixedKer P u).transpose = mixedKer P u := by
    unfold mixedKer
    rw [← hB, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hBt, hPt, hinv]
  conv_lhs => rw [← hK]
  rfl

/-- `P_ab = γ|M_ab|²` is symmetric. -/
private theorem step2_pairP_symm (b β : ℝ) (L : ℕ) (z m : ℂ) (x y : Fin L) :
    pairP β (dysonMat b β L z m) x y = pairP β (dysonMat b β L z m) y x := by
  simp only [pairP, Matrix.of_apply, step2_dysonMat_symm b β L z m x y]

/-! ### Fields in the bounded `C^{1,2}` class -/

/-- At a time inside the class interval a field is continuous, `C²` in space and differentiable in
time. -/
private theorem step2_heat_slice {ι : Type*} [Fintype ι] {F : ℝ → (ι → ℝ) → ℂ} {a b : ℝ}
    (hF : HeatClass F a b) {u : ℝ} (hu : u ∈ Set.Ioo a b) :
    Continuous (F u) ∧ ContDiff ℝ 2 (F u) ∧ ∀ y, DifferentiableAt ℝ (fun r => F r y) u := by
  obtain ⟨hc, -, ⟨Fu, hFu, -, -⟩, ⟨DF, D2F, hD, hD2, -, hcD2, -⟩⟩ := hF
  have hc2 : Continuous (D2F u) :=
    hcD2.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hu, trivial⟩
  have h1 : ContDiff ℝ 1 (DF u) := contDiff_one_iff_hasFDerivAt.2 ⟨D2F u, hc2, hD2 u hu⟩
  have h2 : ContDiff ℝ (1 + 1) (F u) :=
    contDiff_succ_iff_hasFDerivAt (n := 1).2 ⟨DF u, h1, hD u hu⟩
  have h3 : ContDiff ℝ 2 (F u) := by rw [← one_add_one_eq_two]; exact h2
  exact ⟨h3.continuous, h3, fun y => (hFu u hu y).differentiableAt⟩

/-- The carré du champ `Γ(F, F)` is real and nonnegative: its real part is its norm. -/
private theorem step2_gamma_re_eq_norm {ι : Type*} [Fintype ι] {σ2 : ℝ} (hσ2 : 0 ≤ σ2)
    (F : (ι → ℝ) → ℂ) (y : ι → ℝ) :
    (coordGamma σ2 F F y).re = ‖coordGamma σ2 F F y‖ := by
  have e : coordGamma σ2 F F y =
      ((σ2 * ∑ i, ‖deriv (fun e : ℝ => F (y + e • Pi.single i 1)) 0‖ ^ 2 : ℝ) : ℂ) := by
    simp only [coordGamma, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  rw [e, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact mul_nonneg hσ2 (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-! ### Raw rows at a good point -/

section RawRows

open scoped Matrix.Norms.L2Operator

/-- The long-edge Hilbert–Schmidt bound from `ℒ₂ = 𝒦₂ + D₂`: if `|𝒦₂(y,x)| ≤ C'ζ²w` and
`|D₂(y,x)| ≤ Λζ²w`, then `‖G_{xy}‖²_HS ≤ W²(C'+Λ)ζ²w(x,y)`. -/
private theorem step2_hs_long {W L : ℕ} (hW : 1 ≤ W) (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (P : ℂ) {x y : Fin L} {C' Λ ζ w : ℝ}
    (hP : ‖P‖ ≤ C' * ζ ^ 2 * w) (hD : ‖loopTr G ![y, x] ![true, false] - P‖ ≤ Λ * ζ ^ 2 * w) :
    blockHS2 G x y ≤ (W : ℝ) ^ 2 * (C' + Λ) * ζ ^ 2 * w := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have e := step2_loopTr_two_hs G y x
  have hHS0 : 0 ≤ blockHS2 G x y := by unfold blockHS2; positivity
  have hn : ‖loopTr G ![y, x] ![true, false]‖ = ((W : ℝ) ^ 2)⁻¹ * blockHS2 G x y := by
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 : ‖loopTr G ![y, x] ![true, false]‖ ≤ (C' + Λ) * ζ ^ 2 * w := by
    calc _ ≤ ‖loopTr G ![y, x] ![true, false] - P‖ + ‖P‖ := norm_le_norm_sub_add _ _
      _ ≤ Λ * ζ ^ 2 * w + C' * ζ ^ 2 * w := add_le_add hD hP
      _ = _ := by ring
  rw [hn] at h1
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (W : ℝ) ^ 2)
  rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul] at h2
  linarith

/-- `√(Λζ²w) = √Λ ζ √w`. -/
private theorem step2_sqrt_split {Λ ζ w : ℝ} (hΛ : 0 ≤ Λ) (hζ : 0 ≤ ζ) (hw : 0 ≤ w) :
    Real.sqrt (Λ * ζ ^ 2 * w) = Real.sqrt Λ * ζ * Real.sqrt w := by
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hΛ, Real.sqrt_sq hζ]

/-- Weighted operator bound with the terminal weight: on short edges from the unweighted operator
bound and `w ≥ ω⁻¹`, on long edges from the Hilbert–Schmidt bound. -/
private theorem step2_hop_dist {W L : ℕ} (hW : 1 ≤ W) (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (w : Fin L → Fin L → ℝ) {o₁ ω h C' Λ ζ : ℝ} (ho₁ : 0 ≤ o₁) (hω : 1 ≤ ω) (hCΛ : 0 ≤ C' + Λ)
    (hζ : 0 ≤ ζ) (hw0 : ∀ x y, 0 ≤ w x y)
    (hop : ∀ x y, ‖blockOf G x y‖ ≤ W * o₁)
    (hshort : ∀ x y, (cycDist x y : ℝ) ≤ 2 * h → ω⁻¹ ≤ w x y)
    (hlong : ∀ x y, h < cycDist x y → blockHS2 G x y ≤ (W : ℝ) ^ 2 * (C' + Λ) * ζ ^ 2 * w x y)
    (hh : 0 ≤ h) (x y : Fin L) :
    ‖blockOf G x y‖ ≤ W * max (ω * o₁) (Real.sqrt (C' + Λ) * ζ) * Real.sqrt (w x y) := by
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  rcases le_or_gt (cycDist x y : ℝ) h with hxy | hxy
  · have hw := hshort x y (by linarith)
    have hω0 : 0 < ω := by linarith
    have h1 : ω * o₁ * Real.sqrt (w x y) ≥ o₁ := by
      have hs : Real.sqrt ω⁻¹ ≤ Real.sqrt (w x y) := Real.sqrt_le_sqrt hw
      have hs2 : Real.sqrt ω * Real.sqrt ω⁻¹ = 1 := by
        rw [← Real.sqrt_mul hω0.le, mul_inv_cancel₀ hω0.ne', Real.sqrt_one]
      have hs3 : 1 ≤ Real.sqrt ω := by rw [Real.one_le_sqrt]; exact hω
      have : o₁ ≤ o₁ * (Real.sqrt ω * (Real.sqrt ω * Real.sqrt ω⁻¹)) := by
        rw [hs2, mul_one]; exact le_mul_of_one_le_right ho₁ hs3
      have hsω : Real.sqrt ω * Real.sqrt ω = ω := Real.mul_self_sqrt hω0.le
      calc o₁ ≤ o₁ * (Real.sqrt ω * (Real.sqrt ω * Real.sqrt ω⁻¹)) := this
        _ = ω * o₁ * Real.sqrt ω⁻¹ := by rw [← mul_assoc (Real.sqrt ω), hsω]; ring
        _ ≤ ω * o₁ * Real.sqrt (w x y) := mul_le_mul_of_nonneg_left hs (by positivity)
    calc ‖blockOf G x y‖ ≤ W * o₁ := hop x y
      _ ≤ W * (ω * o₁ * Real.sqrt (w x y)) := mul_le_mul_of_nonneg_left h1 hW0
      _ ≤ W * (max (ω * o₁) (Real.sqrt (C' + Λ) * ζ) * Real.sqrt (w x y)) := by
          gcongr; exact le_max_left _ _
      _ = _ := by ring
  · have h1 := step2_blockOf_le_hs G x y
    have h2 : Real.sqrt (blockHS2 G x y) ≤ W * (Real.sqrt (C' + Λ) * ζ * Real.sqrt (w x y)) := by
      calc Real.sqrt (blockHS2 G x y) ≤ Real.sqrt ((W : ℝ) ^ 2 * ((C' + Λ) * ζ ^ 2 * w x y)) :=
            Real.sqrt_le_sqrt (by have := hlong x y hxy; linarith)
        _ = W * (Real.sqrt (C' + Λ) * ζ * Real.sqrt (w x y)) := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hW0,
              step2_sqrt_split hCΛ hζ (hw0 x y)]
    calc ‖blockOf G x y‖ ≤ W * (Real.sqrt (C' + Λ) * ζ * Real.sqrt (w x y)) := h1.trans h2
      _ ≤ W * (max (ω * o₁) (Real.sqrt (C' + Λ) * ζ) * Real.sqrt (w x y)) := by
          gcongr; exact le_max_right _ _
      _ = _ := by ring

/-- The capped weight `w̃ = min{2, K w}` of the near rows. -/
private def step2Cap (K₀ : ℝ) {L : ℕ} (w : Fin L → Fin L → ℝ) (x y : Fin L) : ℝ :=
  min 2 (K₀ * w x y)

/-- Weighted operator bound with the capped weight. -/
private theorem step2_hop_cap {W L : ℕ} (hW : 1 ≤ W) (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (w : Fin L → Fin L → ℝ) {o₁ ω h C' Λ ζ K₀ : ℝ} (ho₁ : 0 < o₁) (hω : 1 ≤ ω) (hCΛ : 0 ≤ C' + Λ)
    (hζ : 0 ≤ ζ) (hw0 : ∀ x y, 0 ≤ w x y) (hK₀ω : ω ≤ K₀)
    (hK₀ : (C' + Λ) * ζ ^ 2 ≤ o₁ ^ 2 * K₀)
    (hop : ∀ x y, ‖blockOf G x y‖ ≤ W * o₁)
    (hshort : ∀ x y, (cycDist x y : ℝ) ≤ 2 * h → ω⁻¹ ≤ w x y)
    (hlong : ∀ x y, h < cycDist x y → blockHS2 G x y ≤ (W : ℝ) ^ 2 * (C' + Λ) * ζ ^ 2 * w x y)
    (x y : Fin L) :
    ‖blockOf G x y‖ ≤ W * o₁ * Real.sqrt (step2Cap K₀ w x y) := by
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have hω0 : 0 < ω := by linarith
  have hK0 : 0 < K₀ := by linarith
  rcases le_or_gt 1 (K₀ * w x y) with h1 | h1
  · have hc : 1 ≤ step2Cap K₀ w x y := le_min (by norm_num) h1
    have hs : 1 ≤ Real.sqrt (step2Cap K₀ w x y) := by rw [Real.one_le_sqrt]; exact hc
    calc ‖blockOf G x y‖ ≤ W * o₁ := hop x y
      _ ≤ W * o₁ * Real.sqrt (step2Cap K₀ w x y) := le_mul_of_one_le_right (by positivity) hs
  · have hlong' : h < cycDist x y := by
      by_contra hc
      push Not at hc
      have := hshort x y (by linarith)
      have : 1 ≤ K₀ * w x y := by
        calc (1 : ℝ) = ω * ω⁻¹ := (mul_inv_cancel₀ hω0.ne').symm
          _ ≤ K₀ * w x y := mul_le_mul hK₀ω this (by positivity) hK0.le
      linarith
    have hcap : step2Cap K₀ w x y = K₀ * w x y := min_eq_right (by linarith)
    have h2 := step2_blockOf_le_hs G x y
    have h3 : blockHS2 G x y ≤ (W : ℝ) ^ 2 * (o₁ ^ 2 * (K₀ * w x y)) := by
      have := hlong x y hlong'
      have h4 : (C' + Λ) * ζ ^ 2 * w x y ≤ o₁ ^ 2 * K₀ * w x y :=
        mul_le_mul_of_nonneg_right hK₀ (hw0 x y)
      calc blockHS2 G x y ≤ (W : ℝ) ^ 2 * ((C' + Λ) * ζ ^ 2 * w x y) := by linarith
        _ ≤ (W : ℝ) ^ 2 * (o₁ ^ 2 * K₀ * w x y) := mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = _ := by ring
    rw [hcap]
    calc ‖blockOf G x y‖ ≤ Real.sqrt (blockHS2 G x y) := h2
      _ ≤ Real.sqrt ((W : ℝ) ^ 2 * (o₁ ^ 2 * (K₀ * w x y))) := Real.sqrt_le_sqrt h3
      _ = W * o₁ * Real.sqrt (K₀ * w x y) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hW0,
            Real.sqrt_sq ho₁.le, mul_assoc]

end RawRows

section PointRates

open scoped Matrix.Norms.L2Operator

end PointRates


section Bridge

/-- The block slice of `A_g ⊗ I` is Hermitian. -/
private theorem step2_slice_herm (g : ℝ) {W L : ℕ} (hW : 1 ≤ W) (y : Ω W L) :
    (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y).IsHermitian := by
  have hA : (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)).IsHermitian := by
    have h := flowH_isHermitian g W L 0 0
    simpa [flowH, blockFlow] using h
  have e := blockFlow_eq_blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
    (s := W) (Nat.cast_nonneg W) y
  have hW0 : (W : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [div_self hW0, Real.sqrt_one, one_smul] at e
  rw [← e]
  exact blockFlow_isHermitian W L hA _ y

/-- The coordinate generator of the mixed-pair field is the block generator at the slice. -/
private theorem step2_coordGen_eq (g E : ℝ) (m : ℂ) (W L : ℕ) (ab : Fin L × Fin L) (u : ℝ)
    (y : Ω W L) :
    coordGen (gammaG g / W) (fun r x => pairErrField g E m W L r x ab) u y =
      blockGen W L (gammaG g) (fun r N => resLoop g E m ![ab.1, ab.2] ![true, false] r N -
        primLoop g W L E m r ![ab.1, ab.2] ![true, false]) u
        (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y) := by
  rw [blockGen_slice]
  rfl

/-- The carré du champ of the mixed-pair field is the bracket of the loop at the slice. -/
private theorem step2_coordGamma_eq (g E : ℝ) (m : ℂ) (W L : ℕ) (ab : Fin L × Fin L) (u : ℝ)
    (y : Ω W L) :
    coordGamma (gammaG g / W) (fun x => pairErrField g E m W L u x ab)
        (fun x => pairErrField g E m W L u x ab) y =
      blockGamma W L (gammaG g) (resLoop g E m ![ab.1, ab.2] ![true, false] u)
        (resLoop g E m ![ab.1, ab.2] ![true, false] u)
        (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y) := by
  rw [← blockGamma_pairErr, blockGamma_slice]
  rfl

/-- The mixed-pair field at the slice is `D₂` at the slice matrix. -/
private theorem step2_pairErrField_eq (g E : ℝ) (m : ℂ) (W L : ℕ) (ab : Fin L × Fin L) (u : ℝ)
    (y : Ω W L) :
    pairErrField g E m W L u y ab = resLoop g E m ![ab.1, ab.2] ![true, false] u
        (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y) -
      primLoop g W L E m u ![ab.1, ab.2] ![true, false] := rfl

end Bridge

private theorem step2_flowH_eq (g : ℝ) (W L : ℕ) {u : ℝ} (hu : 0 ≤ u) (ω : Ω W L) :
    flowH g W L u ω = blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
      (Real.sqrt (u * (gammaG g / W)) • ω) := by
  have hγ : 0 ≤ gammaG g := by unfold gammaG; positivity
  unfold flowH
  rw [blockFlow_eq_blockSlice _ _ _ (mul_nonneg hu hγ), mul_div_assoc]

/-- `μ W L` is the standard Gaussian on the block coordinates. -/
private theorem step2_mu_eq (W L : ℕ) : μ W L = stdGauss (Fin L × Fin W × Fin W) := rfl

section Step2Flow


private theorem step2_flowG_eq (g E : ℝ) (W L : ℕ) {u : ℝ} (hu : 0 ≤ u) (ω : Ω W L) :
    flowG W ⟨g, E, L, u⟩ ω = resolventMat (blockSlice W L (Ag g L ⊗ₖ
      (1 : Matrix (Fin W) (Fin W) ℂ)) (Real.sqrt (u * (gammaG g / W)) • ω))
      (zChar g E (mRoot g L E) u) := by
  unfold flowG
  rw [step2_flowH_eq g W L hu]

/-- The mixed-pair error along the flow at the scaled coordinates. -/
private theorem step2_flowErr_eq (g E : ℝ) (W L : ℕ) {u : ℝ} (hu : 0 ≤ u) (l : Fin L × Fin L)
    (ω : Ω W L) :
    flowErr W ⟨g, E, L, u⟩ ![l.1, l.2] ![true, false] ω =
      pairErrField g E (mRoot g L E) W L u (Real.sqrt (u * (gammaG g / W)) • ω) l :=
  flowErr_eq_pairErrField W ⟨g, E, L, u⟩ hu l.1 l.2 ω

end Step2Flow


section Large

/-- `C ≤ W^a` for all large `W`. -/
private theorem step2_large_const (C : ℝ) {a : ℝ} (ha : 0 < a) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → C ≤ (W : ℝ) ^ a := by
  refine ⟨⌈(max C 1) ^ (1 / a)⌉₊ + 1, fun W hW => ?_⟩
  have hC1 : (1 : ℝ) ≤ max C 1 := le_max_right _ _
  have hb : (max C 1) ^ (1 / a) ≤ (W : ℝ) := by
    have := Nat.le_ceil ((max C 1) ^ (1 / a))
    have h2 : ((⌈(max C 1) ^ (1 / a)⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW
    push_cast at h2
    linarith
  have h0 : 0 ≤ (max C 1) ^ (1 / a) := by positivity
  calc C ≤ max C 1 := le_max_left _ _
    _ = ((max C 1) ^ (1 / a)) ^ a := by
        rw [← Real.rpow_mul (by linarith), one_div_mul_cancel ha.ne', Real.rpow_one]
    _ ≤ (W : ℝ) ^ a := Real.rpow_le_rpow h0 hb ha.le

/-- `log W ≤ W^a / K` for all large `W`. -/
private theorem step2_large_log (K : ℝ) {a : ℝ} (ha : 0 < a) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → K * Real.log W ≤ (W : ℝ) ^ a := by
  obtain ⟨W₁, hW₁⟩ := step2_large_const (2 * |K| / a) (half_pos ha)
  refine ⟨max W₁ 1, fun W hW => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_of_max_le_right hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hlog0 : 0 ≤ Real.log W := Real.log_nonneg hW1
  have h1 : Real.log W ≤ (W : ℝ) ^ (a / 2) / (a / 2) := Real.log_le_rpow_div hW0.le (half_pos ha)
  have h2 := hW₁ W (le_of_max_le_left hW)
  have hpos : 0 < (W : ℝ) ^ (a / 2) := Real.rpow_pos_of_pos hW0 _
  calc K * Real.log W ≤ |K| * Real.log W := mul_le_mul_of_nonneg_right (le_abs_self K) hlog0
    _ ≤ |K| * ((W : ℝ) ^ (a / 2) / (a / 2)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg K)
    _ = (2 * |K| / a) * (W : ℝ) ^ (a / 2) := by field_simp
    _ ≤ (W : ℝ) ^ (a / 2) * (W : ℝ) ^ (a / 2) := mul_le_mul_of_nonneg_right h2 hpos.le
    _ = (W : ℝ) ^ a := by rw [← Real.rpow_add hW0]; ring_nf

/-- `(log W)^k ≤ W^a` for all large `W`. -/
private theorem step2_large_logpow {k : ℝ} (hk : 0 < k) {a : ℝ} (ha : 0 < a) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → Real.log W ^ k ≤ (W : ℝ) ^ a := by
  obtain ⟨W₁, hW₁⟩ := step2_large_log 1 (div_pos ha hk)
  refine ⟨max W₁ 1, fun W hW => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_of_max_le_right hW
  have hlog0 : 0 ≤ Real.log W := Real.log_nonneg hW1
  have h1 := hW₁ W (le_of_max_le_left hW)
  rw [one_mul] at h1
  calc Real.log W ^ k ≤ ((W : ℝ) ^ (a / k)) ^ k := Real.rpow_le_rpow hlog0 h1 hk.le
    _ = (W : ℝ) ^ a := by
        rw [← Real.rpow_mul (by linarith)]; congr 1; field_simp

/-- `C exp(-c (log W)²) ≤ W^{-K}` for all large `W`. -/
private theorem step2_large_exp (C K : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → C * Real.exp (-(c * Real.log W ^ (2 : ℝ))) ≤ (W : ℝ) ^ (-K) := by
  set T := max 1 ((|K| + |Real.log (max C 1)| + 1) / c) with hT
  refine ⟨⌈Real.exp T⌉₊ + 1, fun W hW => ?_⟩
  have hb : Real.exp T ≤ (W : ℝ) := by
    have := Nat.le_ceil (Real.exp T)
    have h2 : ((⌈Real.exp T⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW
    push_cast at h2
    linarith
  have hW0 : (0 : ℝ) < W := lt_of_lt_of_le (Real.exp_pos _) hb
  set ℓ := Real.log W with hℓ
  have hℓT : T ≤ ℓ := by rw [hℓ, Real.le_log_iff_exp_le hW0]; exact hb
  have hℓ1 : 1 ≤ ℓ := le_trans (le_max_left _ _) hℓT
  have hℓb : (|K| + |Real.log (max C 1)| + 1) / c ≤ ℓ := le_trans (le_max_right _ _) hℓT
  have hsq : ℓ ^ (2 : ℝ) = ℓ * ℓ := by rw [Real.rpow_two, sq]
  have h1 : |K| + |Real.log (max C 1)| + 1 ≤ c * ℓ := by
    rw [div_le_iff₀ hc] at hℓb; linarith
  have key : Real.log (max C 1) + K * ℓ ≤ c * ℓ ^ (2 : ℝ) := by
    rw [hsq]
    have h2 : (|K| + |Real.log (max C 1)| + 1) * ℓ ≤ c * ℓ * ℓ :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    have h3 : Real.log (max C 1) ≤ |Real.log (max C 1)| * ℓ := by
      have := le_abs_self (Real.log (max C 1))
      have := mul_le_mul_of_nonneg_left hℓ1 (abs_nonneg (Real.log (max C 1)))
      linarith
    have h4 : K * ℓ ≤ |K| * ℓ := mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith)
    nlinarith
  have hC : C ≤ Real.exp (Real.log (max C 1)) := by
    rw [Real.exp_log (by positivity)]; exact le_max_left _ _
  have hWK : (W : ℝ) ^ (-K) = Real.exp (-(K * ℓ)) := by
    rw [Real.rpow_def_of_pos hW0, hℓ]; ring_nf
  rw [hWK]
  calc C * Real.exp (-(c * ℓ ^ (2 : ℝ))) ≤ Real.exp (Real.log (max C 1)) *
        Real.exp (-(c * ℓ ^ (2 : ℝ))) := mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le
    _ = Real.exp (Real.log (max C 1) - c * ℓ ^ (2 : ℝ)) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-(K * ℓ)) := Real.exp_le_exp.2 (by linarith)

end Large

section WeightThresholds

/-- Far beyond the halo `ℓ (log W)^{2/θ}` the weight is at most `e^{-c(log W)²} + W^{-F}`. -/
private theorem step2_weight_far {c θ F : ℝ} (hc : 0 ≤ c) (hθ : 0 < θ) {W : ℕ} (hW : 1 ≤ W)
    {ℓ d : ℝ}
    (hℓ : 0 < ℓ) (hd : ℓ * Real.log W ^ (2 / θ) < d) :
    weightFn c θ F W ℓ d ≤ Real.exp (-(c * Real.log W ^ (2 : ℝ))) + (W : ℝ) ^ (-F) := by
  unfold weightFn
  have hlog : 0 ≤ Real.log W := Real.log_nonneg (by exact_mod_cast hW)
  have h1 : Real.log W ^ (2 / θ) < d / ℓ := by rw [lt_div_iff₀ hℓ]; linarith
  have h2 : Real.log W ^ (2 : ℝ) ≤ (d / ℓ) ^ θ := by
    have e : Real.log W ^ (2 : ℝ) = (Real.log W ^ (2 / θ)) ^ θ := by
      rw [← Real.rpow_mul hlog]; congr 1; field_simp
    rw [e]
    exact Real.rpow_le_rpow (by positivity) h1.le hθ.le
  have h3 : c * Real.log W ^ (2 : ℝ) ≤ c * (d / ℓ) ^ θ := mul_le_mul_of_nonneg_left h2 hc
  gcongr

/-- Within twice the short range `ℓ (log W)^{3/2}` the weight is at least `W^{-a}`. -/
private theorem step2_weight_short {a : ℝ} (ha : 0 < a) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ c θ F : ℝ, 0 ≤ c → c ≤ 1 → 0 < θ → θ ≤ 1 / 2 →
      ∀ ℓ d : ℝ, 0 < ℓ → 0 ≤ d → d ≤ 2 * (ℓ * Real.log W ^ ((3 : ℝ) / 2)) →
        ((W : ℝ) ^ a)⁻¹ ≤ weightFn c θ F W ℓ d := by
  set T := max (2 / a) ((4 / a) ^ (4 : ℝ)) with hT
  refine ⟨⌈Real.exp T⌉₊ + 1, fun W hW c θ F hc0 hc1 hθ hθ2 ℓ d hℓ hd hdh => ?_⟩
  have hb : Real.exp T ≤ (W : ℝ) := by
    have := Nat.le_ceil (Real.exp T)
    have h2 : ((⌈Real.exp T⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW
    push_cast at h2
    linarith
  have hW0 : (0 : ℝ) < W := lt_of_lt_of_le (Real.exp_pos _) hb
  set lgW := Real.log W with hlgW
  have hlgT : T ≤ lgW := by rw [hlgW, Real.le_log_iff_exp_le hW0]; exact hb
  have hlg1 : 2 / a ≤ lgW := le_trans (le_max_left _ _) hlgT
  have hlg4 : (4 / a) ^ (4 : ℝ) ≤ lgW := le_trans (le_max_right _ _) hlgT
  have hlg0 : 0 < lgW := lt_of_lt_of_le (by positivity) hlg1
  -- `(d/ℓ)^θ ≤ 1 + 2 λ^{3/4}`
  set x := d / ℓ with hx
  have hx0 : 0 ≤ x := div_nonneg hd hℓ.le
  have hxb : x ≤ 2 * lgW ^ ((3 : ℝ) / 2) := by
    rw [hx, div_le_iff₀ hℓ]; linarith
  have hxθ : x ^ θ ≤ 1 + 2 * lgW ^ ((3 : ℝ) / 4) := by
    have hlg34 : 0 ≤ lgW ^ ((3 : ℝ) / 4) := by positivity
    rcases le_or_gt x 1 with h1 | h1
    · have : x ^ θ ≤ 1 := Real.rpow_le_one hx0 h1 hθ.le
      linarith
    · have h2 : x ^ θ ≤ x ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
      have h3 : x ^ ((1 : ℝ) / 2) ≤ (2 * lgW ^ ((3 : ℝ) / 2)) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow hx0 hxb (by norm_num)
      have h4 : (2 * lgW ^ ((3 : ℝ) / 2)) ^ ((1 : ℝ) / 2) ≤ 2 * lgW ^ ((3 : ℝ) / 4) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hlg0.le]
        have : (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 := by
          calc (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
        rw [show (3 : ℝ) / 2 * (1 / 2) = 3 / 4 by norm_num]
        gcongr
      linarith
  -- `1 + 2 λ^{3/4} ≤ a λ`
  have hkey : 1 + 2 * lgW ^ ((3 : ℝ) / 4) ≤ a * lgW := by
    have h1 : 1 ≤ a / 2 * lgW := by
      rw [div_le_iff₀ ha] at hlg1
      linarith
    have h2 : 2 * lgW ^ ((3 : ℝ) / 4) ≤ a / 2 * lgW := by
      have h14 : 4 / a ≤ lgW ^ ((1 : ℝ) / 4) := by
        have := Real.rpow_le_rpow (by positivity) hlg4 (by norm_num : (0 : ℝ) ≤ 1 / 4)
        rwa [← Real.rpow_mul (by positivity), show (4 : ℝ) * (1 / 4) = 1 by norm_num,
          Real.rpow_one] at this
      have hsplit : lgW = lgW ^ ((3 : ℝ) / 4) * lgW ^ ((1 : ℝ) / 4) := by
        rw [← Real.rpow_add hlg0]; norm_num
      have hp : 0 ≤ lgW ^ ((3 : ℝ) / 4) := by positivity
      calc 2 * lgW ^ ((3 : ℝ) / 4) = a / 2 * (lgW ^ ((3 : ℝ) / 4) * (4 / a)) := by
            field_simp; ring
        _ ≤ a / 2 * (lgW ^ ((3 : ℝ) / 4) * lgW ^ ((1 : ℝ) / 4)) := by gcongr
        _ = a / 2 * lgW := by rw [← hsplit]
    linarith
  -- the weight
  have hexp : ((W : ℝ) ^ a)⁻¹ = Real.exp (-(a * lgW)) := by
    rw [Real.rpow_def_of_pos hW0, ← Real.exp_neg, hlgW]; ring_nf
  rw [hexp]
  unfold weightFn
  have h1 : c * x ^ θ ≤ a * lgW := by
    have : c * x ^ θ ≤ 1 * x ^ θ := mul_le_mul_of_nonneg_right hc1 (by positivity)
    linarith
  have h2 : Real.exp (-(a * lgW)) ≤ Real.exp (-(c * x ^ θ)) := Real.exp_le_exp.2 (by linarith)
  have h3 : 0 ≤ (W : ℝ) ^ (-F) := by positivity
  rw [← hx]
  linarith

end WeightThresholds


/-- `Γ(F, F)` is the real number `σ² Σ_i ‖∂_i F‖²`. -/
private theorem step2_cgamma_eq {ι : Type*} [Fintype ι] (σ2 : ℝ) (F : (ι → ℝ) → ℂ) (y : ι → ℝ) :
    coordGamma σ2 F F y =
      ((σ2 * ∑ i, ‖deriv (fun e : ℝ => F (y + e • Pi.single i 1)) 0‖ ^ 2 : ℝ) : ℂ) := by
  simp only [coordGamma, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

/-- Along a line, `e ↦ G(y + e v)` has first derivative `DG(y) v` at `0`. -/
private theorem step2_deriv_line {ι : Type*} [Fintype ι] {G : (ι → ℝ) → ℂ}
    {DG : (ι → ℝ) → ((ι → ℝ) →L[ℝ] ℂ)} (hD : ∀ x, HasFDerivAt G (DG x) x) (y v : ι → ℝ) :
    deriv (fun e : ℝ => G (y + e • v)) 0 = DG y v := by
  have hl : HasDerivAt (fun e : ℝ => y + e • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have h := ((hD (y + (0 : ℝ) • v)).comp_hasDerivAt (0 : ℝ) hl)
  have h2 : HasDerivAt (fun e : ℝ => G (y + e • v)) (DG y v) 0 := by
    simpa [Function.comp_def] using h
  exact h2.deriv

/-- Along a line, `e ↦ G(y + e v)` has second derivative `D²G(y) v v` at `0`, when `G` has
derivative `DG` and `DG` has derivative `D²G` everywhere. -/
private theorem step2_iteratedDeriv_line {ι : Type*} [Fintype ι] {G : (ι → ℝ) → ℂ}
    {DG : (ι → ℝ) → ((ι → ℝ) →L[ℝ] ℂ)} {D2G : (ι → ℝ) → ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℂ)}
    (hD : ∀ x, HasFDerivAt G (DG x) x) (hD2 : ∀ x, HasFDerivAt DG (D2G x) x) (y v : ι → ℝ) :
    iteratedDeriv 2 (fun e : ℝ => G (y + e • v)) 0 = D2G y v v := by
  have hl : ∀ e : ℝ, HasDerivAt (fun e : ℝ => y + e • v) v e := fun e => by
    simpa using ((hasDerivAt_id e).smul_const v).const_add y
  have h1 : deriv (fun e : ℝ => G (y + e • v)) = fun e => DG (y + e • v) v :=
    funext fun e => ((hD _).comp_hasDerivAt e (hl e)).deriv
  have h2 : HasDerivAt (fun e : ℝ => DG (y + e • v) v) (D2G y v v) 0 := by
    have h := ((hD2 _).comp_hasDerivAt 0 (hl 0)).clm_apply (hasDerivAt_const (0 : ℝ) v)
    simpa using h
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1, h2.deriv]

/-- A function jointly continuous on `(a,b) × ℝ^ι` is continuous in `x` at each time in `(a,b)`. -/
private theorem step2_slice {ι E : Type*} [TopologicalSpace E] {g : ℝ → (ι → ℝ) → E}
    {a b : ℝ} (hg : ContinuousOn (Function.uncurry g) (Set.Ioo a b ×ˢ Set.univ)) {r : ℝ}
    (hr : r ∈ Set.Ioo a b) : Continuous (g r) :=
  hg.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hr, trivial⟩

/-- Jet data of a member of the class at a time `u ∈ (a,b)`: differentiability in time, `C²`
regularity in space, and continuity and boundedness of `F u`, `𝒢F u`, `Γ(F u, F u)`. -/
private theorem step2_class_jet {ι : Type*} [Fintype ι] {F : ℝ → (ι → ℝ) → ℂ} {a b : ℝ}
    (hF : HeatClass F a b) {u : ℝ} (hu : u ∈ Set.Ioo a b) (σ2 : ℝ) :
    (∀ y, DifferentiableAt ℝ (fun r => F r y) u) ∧ ContDiff ℝ 2 (F u) ∧
      (∃ C : ℝ, ∀ y, ‖F u y‖ ≤ C) ∧
      (Continuous (coordGen σ2 F u) ∧ ∃ C : ℝ, ∀ y, ‖coordGen σ2 F u y‖ ≤ C) ∧
      (Continuous (coordGamma σ2 (F u) (F u)) ∧
        ∃ C : ℝ, ∀ y, ‖coordGamma σ2 (F u) (F u) y‖ ≤ C) := by
  obtain ⟨hc, ⟨C₀, hC₀⟩, ⟨Fu, hu', hcu, C₁, hC₁⟩, ⟨DF, D2F, hD, hD2, hcD, hcD2, C₂, hC₂⟩⟩ := hF
  have hei : ∀ i : ι, ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖ ≤ 1 := fun i => by
    rw [Pi.norm_single]; simp
  have hDc : Continuous (DF u) := step2_slice hcD hu
  have hD2c : Continuous (D2F u) := step2_slice hcD2 hu
  have hFuc : Continuous (Fu u) := step2_slice hcu hu
  have hC₂0 : 0 ≤ C₂ := (norm_nonneg _).trans (hC₂ u hu 0).1
  have hC₁0 : 0 ≤ C₁ := (norm_nonneg _).trans (hC₁ u hu 0)
  have hb1 : ∀ (y : ι → ℝ) (i : ι), ‖DF u y (Pi.single i 1)‖ ≤ C₂ := fun y i =>
    calc ‖DF u y (Pi.single i 1)‖ ≤ ‖DF u y‖ * ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖ :=
          (DF u y).le_opNorm _
      _ ≤ C₂ * 1 := mul_le_mul (hC₂ u hu y).1 (hei i) (norm_nonneg _) hC₂0
      _ = C₂ := mul_one _
  have hb2 : ∀ (y : ι → ℝ) (i : ι), ‖D2F u y (Pi.single i 1) (Pi.single i 1)‖ ≤ C₂ := fun y i =>
    calc ‖D2F u y (Pi.single i 1) (Pi.single i 1)‖
        ≤ ‖D2F u y (Pi.single i 1)‖ * ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖ := (D2F u y _).le_opNorm _
      _ ≤ (‖D2F u y‖ * ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖) * 1 :=
          mul_le_mul ((D2F u y).le_opNorm _) (hei i) (norm_nonneg _) (by positivity)
      _ ≤ (C₂ * 1) * 1 := by
          gcongr
          · exact (hC₂ u hu y).2
          · exact hei i
      _ = C₂ := by ring
  have hgen : ∀ y, coordGen σ2 F u y =
      Fu u y + ((σ2 / 2 : ℝ) : ℂ) * ∑ i, D2F u y (Pi.single i 1) (Pi.single i 1) := by
    intro y
    simp only [coordGen, (hu' u hu y).deriv]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    exact step2_iteratedDeriv_line (hD u hu) (hD2 u hu) y _
  have hgam : ∀ y, coordGamma σ2 (F u) (F u) y =
      (σ2 : ℂ) * ∑ i, DF u y (Pi.single i 1) * star (DF u y (Pi.single i 1)) := by
    intro y
    simp only [coordGamma, step2_deriv_line (hD u hu)]
  have hFdiff : Differentiable ℝ (F u) := fun x => (hD u hu x).differentiableAt
  have hDdiff : Differentiable ℝ (DF u) := fun x => (hD2 u hu x).differentiableAt
  refine ⟨fun y => (hu' u hu y).differentiableAt, ?_, ⟨C₀, fun y => hC₀ u hu y⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩⟩
  · rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_fderiv]
    refine ⟨hFdiff, by simp, ?_⟩
    have hfd : fderiv ℝ (F u) = DF u := funext fun x => (hD u hu x).fderiv
    rw [hfd, contDiff_one_iff_fderiv]
    refine ⟨hDdiff, ?_⟩
    have : fderiv ℝ (DF u) = D2F u := funext fun x => (hD2 u hu x).fderiv
    rw [this]; exact hD2c
  · have : coordGen σ2 F u = fun y => Fu u y + ((σ2 / 2 : ℝ) : ℂ) *
        ∑ i, D2F u y (Pi.single i 1) (Pi.single i 1) := funext hgen
    rw [this]
    refine hFuc.add (continuous_const.mul (continuous_finsetSum _ fun i _ => ?_))
    exact (hD2c.clm_apply continuous_const).clm_apply continuous_const
  · refine ⟨C₁ + |σ2 / 2| * (Fintype.card ι * C₂), fun y => ?_⟩
    rw [hgen]
    refine (norm_add_le _ _).trans (add_le_add (hC₁ u hu y) ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖D2F u y (Pi.single i 1) (Pi.single i 1)‖ ≤ ∑ _i : ι, C₂ :=
          Finset.sum_le_sum fun i _ => hb2 y i
      _ = Fintype.card ι * C₂ := by simp
  · have : coordGamma σ2 (F u) (F u) = fun y => (σ2 : ℂ) *
        ∑ i, DF u y (Pi.single i 1) * star (DF u y (Pi.single i 1)) := funext hgam
    rw [this]
    refine continuous_const.mul (continuous_finsetSum _ fun i _ => ?_)
    exact (hDc.clm_apply continuous_const).mul
      (continuous_star.comp (hDc.clm_apply continuous_const))
  · refine ⟨|σ2| * (Fintype.card ι * (C₂ * C₂)), fun y => ?_⟩
    rw [hgam, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖DF u y (Pi.single i 1) * star (DF u y (Pi.single i 1))‖ ≤ ∑ _i : ι, C₂ * C₂ :=
          Finset.sum_le_sum fun i _ => by
            rw [norm_mul, norm_star]
            exact mul_le_mul (hb1 y i) (hb1 y i) (norm_nonneg _) hC₂0
      _ = Fintype.card ι * (C₂ * C₂) := by simp

/-! ### Rows of the propagated sources at a good point -/

section Step2Rows

open scoped Matrix.Norms.L2Operator

/-- The near bracket of (C.20) [fo:eq:pair-near-sources] for every pair: the bracket (5.9)
[gc:eq:bracket] of `ℒ₂(a,b;+,-)` is at most `4γW s₀((4H+4)o₁⁴ + L o₁² Λ ζ² ε)`, from the
operator bound `W⁻¹‖G_{xy}‖ ≤ o₁`, `W⁻²‖G_{ba}‖²_HS ≤ s₀`, the long-edge bound and a weight at
most `ε` beyond the halo `H`. -/
private theorem step2_bracket_near (g E : ℝ) (m : ℂ) (hm : 0 < m.im) {W L : ℕ} (hW : 1 ≤ W)
    {u : ℝ} (hu : u < 1) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    (w : Fin L → Fin L → ℝ) {o₁ s₀ h H Λ ζ εw : ℝ} (ho₁ : 0 ≤ o₁) (hs₀ : 0 ≤ s₀) (hH : 0 ≤ H)
    (hhH : h ≤ H) (hΛ : 0 ≤ Λ) (hεw : 0 ≤ εw)
    (hop : ∀ x y, ‖blockOf (resolventMat M (zChar g E m u)) x y‖ ≤ W * o₁)
    (hhs : ∀ x y, blockHS2 (resolventMat M (zChar g E m u)) x y ≤ (W : ℝ) ^ 2 * s₀)
    (hlong : ∀ x y, h < cycDist x y →
      blockHS2 (resolventMat M (zChar g E m u)) x y ≤ (W : ℝ) ^ 2 * Λ * ζ ^ 2 * w x y)
    (hfar : ∀ x y, H < cycDist x y → w x y ≤ εw) (a b : Fin L) :
    (blockGamma W L (gammaG g) (resLoop g E m ![a, b] ![true, false] u)
        (resLoop g E m ![a, b] ![true, false] u) M).re ≤
      4 * gammaG g * W * s₀ * ((4 * H + 4) * o₁ ^ 4 + L * (o₁ ^ 2 * (Λ * ζ ^ 2 * εw))) := by
  rw [step2_gamma_eq g E m hm hW hu hM a b, ← Complex.ofReal_sum, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  set G := resolventMat M (zChar g E m u) with hG
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hop2 : ∀ x y, ‖blockOf G x y‖ ^ 2 ≤ (W : ℝ) ^ 2 * o₁ ^ 2 := fun x y => by
    have := pow_le_pow_left₀ (norm_nonneg _) (hop x y) 2
    linarith [show ((W : ℝ) * o₁) ^ 2 = (W : ℝ) ^ 2 * o₁ ^ 2 by ring]
  have hP : 0 ≤ Λ * ζ ^ 2 * εw := by positivity
  set I : Fin L → Fin L → ℝ := fun x c => if (cycDist x c : ℝ) ≤ H then (1 : ℝ) else 0 with hI
  have hI0 : ∀ x c, 0 ≤ I x c := fun x c => by simp only [hI]; split_ifs <;> norm_num
  have hc : ∀ c, step2_hs (blockOf (G * blockE W L a * (Gᴴ * blockE W L b * G) +
        Gᴴ * blockE W L b * (G * blockE W L a * Gᴴ)) c c) ≤
      4 * (W : ℝ) ^ 2 * s₀ * (o₁ ^ 4 * (I a c + I b c) + o₁ ^ 2 * (Λ * ζ ^ 2 * εw)) := by
    intro c
    refine (step2_hs_Z G a b c).trans ?_
    have hba := hhs b a
    have hW4 : ((W : ℝ)⁻¹) ^ 4 * (W : ℝ) ^ 4 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hW0.ne', one_pow]
    by_cases hac : (cycDist a c : ℝ) ≤ H
    · have hIa : I a c = 1 := by simp only [hI, hac, ite_true]
      have h1 := mul_le_mul (hop2 c a) (hop2 b c) (sq_nonneg _) (by positivity)
      have h2 := mul_le_mul h1 hba (by unfold blockHS2; positivity) (by positivity)
      have hI1 : 0 ≤ I b c := hI0 b c
      calc 4 * ((W : ℝ)⁻¹) ^ 4 * (‖blockOf G c a‖ ^ 2 * ‖blockOf G b c‖ ^ 2 * blockHS2 G b a)
          ≤ 4 * ((W : ℝ)⁻¹) ^ 4 * ((W : ℝ) ^ 2 * o₁ ^ 2 * ((W : ℝ) ^ 2 * o₁ ^ 2) *
            ((W : ℝ) ^ 2 * s₀)) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 4 * (W : ℝ) ^ 2 * s₀ * (o₁ ^ 4 * 1) := by
            rw [show 4 * ((W : ℝ)⁻¹) ^ 4 * ((W : ℝ) ^ 2 * o₁ ^ 2 * ((W : ℝ) ^ 2 * o₁ ^ 2) *
              ((W : ℝ) ^ 2 * s₀)) = 4 * (((W : ℝ)⁻¹) ^ 4 * (W : ℝ) ^ 4) * (W : ℝ) ^ 2 * s₀ *
                o₁ ^ 4 by ring, hW4]; ring
        _ ≤ _ := by
            rw [hIa]
            have : 0 ≤ 4 * (W : ℝ) ^ 2 * s₀ := by positivity
            have : 0 ≤ o₁ ^ 4 * I b c := mul_nonneg (by positivity) hI1
            nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * (W : ℝ) ^ 2 * s₀)
              (add_nonneg this (mul_nonneg (sq_nonneg o₁) hP))]
    · by_cases hbc : (cycDist b c : ℝ) ≤ H
      · have hIb : I b c = 1 := by simp only [hI, hbc, ite_true]
        have h1 := mul_le_mul (hop2 c a) (hop2 b c) (sq_nonneg _) (by positivity)
        have h2 := mul_le_mul h1 hba (by unfold blockHS2; positivity) (by positivity)
        have hI1 : 0 ≤ I a c := hI0 a c
        calc 4 * ((W : ℝ)⁻¹) ^ 4 * (‖blockOf G c a‖ ^ 2 * ‖blockOf G b c‖ ^ 2 * blockHS2 G b a)
            ≤ 4 * ((W : ℝ)⁻¹) ^ 4 * ((W : ℝ) ^ 2 * o₁ ^ 2 * ((W : ℝ) ^ 2 * o₁ ^ 2) *
              ((W : ℝ) ^ 2 * s₀)) := mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = 4 * (W : ℝ) ^ 2 * s₀ * (o₁ ^ 4 * 1) := by
              rw [show 4 * ((W : ℝ)⁻¹) ^ 4 * ((W : ℝ) ^ 2 * o₁ ^ 2 * ((W : ℝ) ^ 2 * o₁ ^ 2) *
                ((W : ℝ) ^ 2 * s₀)) = 4 * (((W : ℝ)⁻¹) ^ 4 * (W : ℝ) ^ 4) * (W : ℝ) ^ 2 * s₀ *
                  o₁ ^ 4 by ring, hW4]; ring
          _ ≤ _ := by
              rw [hIb]
              have : 0 ≤ o₁ ^ 4 * I a c := mul_nonneg (by positivity) hI1
              nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * (W : ℝ) ^ 2 * s₀)
                (add_nonneg this (mul_nonneg (sq_nonneg o₁) hP))]
      · have hca : H < (cycDist c a : ℝ) := by
          rw [step2_cycDist_comm]; exact not_le.mp hac
        have hlg := hlong c a (lt_of_le_of_lt hhH hca)
        have hwf := hfar c a hca
        have hca2 : ‖blockOf G c a‖ ^ 2 ≤ (W : ℝ) ^ 2 * (Λ * ζ ^ 2 * εw) := by
          have h1 := step2_blockOf_le_hs G c a
          have h2 : ‖blockOf G c a‖ ^ 2 ≤ blockHS2 G c a := by
            have h0 : 0 ≤ blockHS2 G c a := by unfold blockHS2; positivity
            calc ‖blockOf G c a‖ ^ 2 ≤ Real.sqrt (blockHS2 G c a) ^ 2 :=
                  pow_le_pow_left₀ (norm_nonneg _) h1 2
              _ = blockHS2 G c a := Real.sq_sqrt h0
          have h3 : (W : ℝ) ^ 2 * Λ * ζ ^ 2 * w c a ≤ (W : ℝ) ^ 2 * Λ * ζ ^ 2 * εw :=
            mul_le_mul_of_nonneg_left hwf (by positivity)
          linarith
        have h1 := mul_le_mul hca2 (hop2 b c) (sq_nonneg _) (by positivity)
        have h2 := mul_le_mul h1 hba (by unfold blockHS2; positivity) (by positivity)
        have hIa : 0 ≤ I a c := hI0 a c
        have hIb : 0 ≤ I b c := hI0 b c
        calc 4 * ((W : ℝ)⁻¹) ^ 4 * (‖blockOf G c a‖ ^ 2 * ‖blockOf G b c‖ ^ 2 * blockHS2 G b a)
            ≤ 4 * ((W : ℝ)⁻¹) ^ 4 * ((W : ℝ) ^ 2 * (Λ * ζ ^ 2 * εw) * ((W : ℝ) ^ 2 * o₁ ^ 2) *
              ((W : ℝ) ^ 2 * s₀)) := mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = 4 * (W : ℝ) ^ 2 * s₀ * (o₁ ^ 2 * (Λ * ζ ^ 2 * εw)) := by
              rw [show 4 * ((W : ℝ)⁻¹) ^ 4 * ((W : ℝ) ^ 2 * (Λ * ζ ^ 2 * εw) *
                ((W : ℝ) ^ 2 * o₁ ^ 2) * ((W : ℝ) ^ 2 * s₀)) =
                  4 * (((W : ℝ)⁻¹) ^ 4 * (W : ℝ) ^ 4) * (W : ℝ) ^ 2 * s₀ *
                    (o₁ ^ 2 * (Λ * ζ ^ 2 * εw)) by ring, hW4]; ring
          _ ≤ _ := by
              have : 0 ≤ o₁ ^ 4 * (I a c + I b c) := mul_nonneg (by positivity) (by linarith)
              nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * (W : ℝ) ^ 2 * s₀) this]
  have hca := step2_near_count a hH
  have hcb := step2_near_count b hH
  have hsum : ∑ c, (I a c + I b c) ≤ 4 * H + 4 := by
    rw [Finset.sum_add_distrib]; simp only [hI]; linarith
  calc gammaG g / W * ∑ c, step2_hs (blockOf (G * blockE W L a * (Gᴴ * blockE W L b * G) +
        Gᴴ * blockE W L b * (G * blockE W L a * Gᴴ)) c c)
      ≤ gammaG g / W * ∑ c, 4 * (W : ℝ) ^ 2 * s₀ *
          (o₁ ^ 4 * (I a c + I b c) + o₁ ^ 2 * (Λ * ζ ^ 2 * εw)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => hc c) (by positivity)
    _ = gammaG g / W * (4 * (W : ℝ) ^ 2 * s₀) *
          (o₁ ^ 4 * ∑ c, (I a c + I b c) + L * (o₁ ^ 2 * (Λ * ζ ^ 2 * εw))) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
        ring
    _ ≤ gammaG g / W * (4 * (W : ℝ) ^ 2 * s₀) *
          (o₁ ^ 4 * (4 * H + 4) + L * (o₁ ^ 2 * (Λ * ζ ^ 2 * εw))) := by
        gcongr
    _ = _ := by field_simp

end Step2Rows

section Step2Rows2

open scoped Matrix.Norms.L2Operator

/-- The rows of the sources of the propagated mixed pair at a good point: the quadratic term, the
light term (C.18) [fo:eq:pair-far-light] at distant pairs and (C.20) [fo:eq:pair-near-sources] at
every pair, and the bracket (C.19) [fo:eq:pair-far-bracket] at distant pairs and (C.20)
[fo:eq:pair-near-sources] at every pair. -/
private theorem step2_point_rows (g E : ℝ) (m : ℂ) {W L : ℕ} (hW : 1 ≤ W) (hL : 3 ≤ L)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {u : ℝ} (hu1 : u < 1)
    {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    (w : Fin L → Fin L → ℝ) (hw0 : ∀ x y, 0 ≤ w x y) (hw2 : ∀ x y, w x y ≤ 2)
    (hws : ∀ x y, w x y = w y x) {wmin : ℝ} (hwmin0 : 0 < wmin) (hwmin : ∀ x y, wmin ≤ w x y)
    {Λ ζ Cc ℓ o₁ s₀ τ ω h H εw C' K₀ : ℝ} (hΛ : 0 ≤ Λ) (hζ : 0 ≤ ζ)
    (ho₁ : 0 < o₁) (hs₀ : 0 ≤ s₀) (hτ : 0 ≤ τ) (hω : 1 ≤ ω) (hh : 0 ≤ h) (hhH : h ≤ H)
    (hC' : 0 ≤ C') (hK₀ω : ω ≤ K₀) (hK₀ : (C' + Λ) * ζ ^ 2 ≤ o₁ ^ 2 * K₀) (hεw : 0 ≤ εw)
    (hD : ∀ x y, ‖resLoop g E m ![x, y] ![true, false] u M -
      primLoop g W L E m u ![x, y] ![true, false]‖ ≤ Λ * ζ ^ 2 * w x y)
    (hconv : ∀ x y, ∑ c, w x c * w c y ≤ Cc * ℓ * w x y ∧
      ∑ c, Real.sqrt (w x c * w c y) ≤ Cc * ℓ * Real.sqrt (w x y))
    (hop : ∀ x y, ‖blockOf (resolventMat M (zChar g E m u)) x y‖ ≤ W * o₁)
    (hhs : ∀ x y, blockHS2 (resolventMat M (zChar g E m u)) x y ≤ (W : ℝ) ^ 2 * s₀)
    (havg : ∀ c, ‖blockTr (resolventMat M (zChar g E m u) -
      dysonMat (hopB g) (gammaG g) L E m ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) c c‖ ≤ τ)
    (hprim : ∀ x y, h < cycDist x y →
      ‖primLoop g W L E m u ![x, y] ![true, false]‖ ≤ C' * ζ ^ 2 * w x y)
    (hshort : ∀ x y, (cycDist x y : ℝ) ≤ 2 * h → ω⁻¹ ≤ w x y)
    (hfar : ∀ x y, H < cycDist x y → w x y ≤ εw) (a b : Fin L) :
    ‖∑ c, (resLoop g E m ![a, c] ![true, false] u M - primLoop g W L E m u ![a, c] ![true, false]) *
        (resLoop g E m ![c, b] ![true, false] u M - primLoop g W L E m u ![c, b] ![true, false])‖ ≤
      (Λ * ζ ^ 2) ^ 2 * Cc * ℓ * w a b ∧
    (2 * h < cycDist a b → ‖lightW g E m ![a, b] ![true, false] u M‖ ≤
      2 * gammaG g * W * τ * (C' + Λ) * ζ ^ 2 * max (ω * o₁) (Real.sqrt (C' + Λ) * ζ) * Cc *
        ℓ * w a b) ∧
    ‖lightW g E m ![a, b] ![true, false] u M‖ ≤ 2 * Real.sqrt 2 * gammaG g * W * τ * o₁ *
      ((4 * H + 2) * s₀ + L * Real.sqrt (s₀ * max ((C' + Λ) * ζ ^ 2 / K₀) (s₀ / 2) * 1 ^ 2 *
        (K₀ * εw))) ∧
    (2 * h < cycDist a b → (blockGamma W L (gammaG g) (resLoop g E m ![a, b] ![true, false] u)
        (resLoop g E m ![a, b] ![true, false] u) M).re ≤
      4 * gammaG g * W * ((C' + Λ) * ζ ^ 2 * w a b) *
        max (ω * o₁) (Real.sqrt (C' + Λ) * ζ) ^ 4 * Cc * ℓ * w a b) ∧
    (blockGamma W L (gammaG g) (resLoop g E m ![a, b] ![true, false] u)
        (resLoop g E m ![a, b] ![true, false] u) M).re ≤
      4 * gammaG g * W * s₀ * ((4 * H + 4) * o₁ ^ 4 + L * (o₁ ^ 2 * ((C' + Λ) * ζ ^ 2 * εw))) := by
  set G := resolventMat M (zChar g E m u) with hG
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hL1 : 1 ≤ L := by omega
  have hK0 : 0 < K₀ := by linarith
  have hCΛ : 0 ≤ C' + Λ := by linarith
  have hlong : ∀ x y, h < cycDist x y →
      blockHS2 G x y ≤ (W : ℝ) ^ 2 * (C' + Λ) * ζ ^ 2 * w x y := by
    intro x y hxy
    have hyx : h < cycDist y x := by rw [step2_cycDist_comm]; exact hxy
    have hP := hprim y x hyx
    have hDyx := hD y x
    rw [hws y x] at hP hDyx
    exact step2_hs_long hW G _ hP hDyx
  have havg' : ∀ (c : Fin L) (s : Bool), ‖loopTr G ![c] ![s] - sgnScalar m s‖ ≤ τ := by
    intro c s
    rw [step2_loop_one_sub g E W L hW hL1 m hm G c s]
    exact havg c
  have hopd := step2_hop_dist hW G w ho₁.le hω hCΛ hζ hw0 hop hshort hlong hh
  set wc := step2Cap K₀ w with hwc
  have hwc0 : ∀ x y, 0 ≤ wc x y := fun x y => le_min (by norm_num) (mul_nonneg hK0.le (hw0 x y))
  have hwc2 : ∀ x y, wc x y ≤ 2 := fun x y => min_le_left _ _
  have hwcs : ∀ x y, wc x y = wc y x := fun x y => by simp only [hwc, step2Cap, hws x y]
  have hwcK : ∀ x y, wc x y ≤ K₀ * w x y := fun x y => min_le_right _ _
  have hopc := step2_hop_cap hW G w ho₁ hω hCΛ hζ hw0 hK₀ω hK₀ hop hshort hlong
  set Dm : Fin L → Fin L → ℂ := fun x y => resLoop g E m ![x, y] ![true, false] u M -
    primLoop g W L E m u ![x, y] ![true, false] with hDm
  have hquad := lemmaNRates_quad Dm w (mul_nonneg hΛ (sq_nonneg ζ)) hw0
    (fun x y => by have := hD x y; simp only [hDm]; linarith) (fun x y => (hconv x y).1) a b
  refine ⟨hquad, ?_, ?_, ?_, ?_⟩
  · intro hab
    have hl := (lemmaNRates_light g E m hW u M w hw0 hw2 hws (Cw := Cc) (ℓ := ℓ) (h := h) (H := h)
      (τ := τ) (o := max (ω * o₁) (Real.sqrt (C' + Λ) * ζ)) (s₀ := s₀) (Λ := C' + Λ) (ζ := ζ)
      (ε₀ := 2) hτ (le_max_of_le_left (by positivity)) hs₀ hCΛ hh le_rfl
      (fun x y => (hconv x y).2) havg' hopd hhs (fun x y hxy => hlong x y hxy)
      (fun x y _ => hw2 x y) a b).1 hab
    calc _ ≤ _ := hl
      _ = _ := by ring
  · set Λt := max ((C' + Λ) * ζ ^ 2 / K₀) (s₀ / 2) with hΛt
    have hΛt0 : 0 ≤ Λt := le_max_of_le_right (by positivity)
    have hwlow : ∀ x y, min 2 (K₀ * wmin) ≤ wc x y := fun x y =>
      min_le_min le_rfl (mul_le_mul_of_nonneg_left (hwmin x y) hK0.le)
    have hwl0 : 0 < min 2 (K₀ * wmin) := lt_min (by norm_num) (mul_pos hK0 hwmin0)
    have hconvc : ∀ x y, ∑ c, Real.sqrt (wc x c * wc c y) ≤
        (2 * L / Real.sqrt (min 2 (K₀ * wmin))) * 1 * Real.sqrt (wc x y) := by
      intro x y
      have hs : 0 < Real.sqrt (min 2 (K₀ * wmin)) := Real.sqrt_pos.2 hwl0
      have h1 : ∑ c, Real.sqrt (wc x c * wc c y) ≤ ∑ _c : Fin L, (2 : ℝ) := by
        refine Finset.sum_le_sum fun c _ => ?_
        rw [Real.sqrt_le_left (by norm_num)]
        nlinarith [hwc2 x c, hwc2 c y, hwc0 x c, hwc0 c y]
      have h2 : ∑ _c : Fin L, (2 : ℝ) = 2 * L := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      have h3 : Real.sqrt (min 2 (K₀ * wmin)) ≤ Real.sqrt (wc x y) := Real.sqrt_le_sqrt (hwlow x y)
      rw [h2] at h1
      calc _ ≤ 2 * (L : ℝ) := h1
        _ = 2 * L / Real.sqrt (min 2 (K₀ * wmin)) * 1 * Real.sqrt (min 2 (K₀ * wmin)) := by
            field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
    have hhsc : ∀ x y, h < cycDist x y → blockHS2 G x y ≤ (W : ℝ) ^ 2 * Λt * 1 ^ 2 * wc x y := by
      intro x y hxy
      rw [one_pow, mul_one]
      rcases le_or_gt (K₀ * w x y) 2 with h2 | h2
      · have hc : wc x y = K₀ * w x y := min_eq_right h2
        rw [hc]
        have h3 := hlong x y hxy
        have h5 : (C' + Λ) * ζ ^ 2 / K₀ ≤ Λt := le_max_left _ _
        calc blockHS2 G x y ≤ (W : ℝ) ^ 2 * ((C' + Λ) * ζ ^ 2) * w x y := by linarith
          _ = (W : ℝ) ^ 2 * ((C' + Λ) * ζ ^ 2 / K₀) * (K₀ * w x y) := by field_simp
          _ ≤ (W : ℝ) ^ 2 * Λt * (K₀ * w x y) := by gcongr; exact mul_nonneg hK0.le (hw0 x y)
      · have hc : wc x y = 2 := min_eq_left h2.le
        rw [hc]
        have h5 : s₀ / 2 ≤ Λt := le_max_right _ _
        calc blockHS2 G x y ≤ (W : ℝ) ^ 2 * s₀ := hhs x y
          _ = (W : ℝ) ^ 2 * (s₀ / 2) * 2 := by ring
          _ ≤ (W : ℝ) ^ 2 * Λt * 2 := by gcongr
    have hfarc : ∀ x y, H < cycDist x y → wc x y ≤ K₀ * εw := fun x y hxy =>
      (hwcK x y).trans (mul_le_mul_of_nonneg_left (hfar x y hxy) hK0.le)
    have hl := (lemmaNRates_light g E m hW u M wc hwc0 hwc2 hwcs
      (Cw := 2 * L / Real.sqrt (min 2 (K₀ * wmin))) (ℓ := 1) (h := h) (H := H) (τ := τ) (o := o₁)
      (s₀ := s₀) (Λ := Λt) (ζ := 1) (ε₀ := K₀ * εw) hτ ho₁.le hs₀ hΛt0 (hh.trans hhH) hhH
      hconvc havg' hopc hhs hhsc hfarc a b).2
    exact hl
  · intro hab
    have hab' : h < cycDist b a := by
      rw [step2_cycDist_comm]
      have : (0 : ℝ) ≤ 2 * h - h := by linarith
      linarith
    have hη := hlong b a hab'
    rw [hws b a] at hη
    have hb := lemmaNRates_bracket g E m hm.1 hW hu1 hM w hw0 hws
      (Cw := Cc) (ℓ := ℓ) (o := max (ω * o₁) (Real.sqrt (C' + Λ) * ζ))
      (η := (C' + Λ) * ζ ^ 2 * w a b) (le_max_of_le_left (by positivity))
      (fun x y => (hconv x y).1) hopd a b (by linarith)
    calc _ ≤ _ := hb
      _ = _ := by ring
  · exact step2_bracket_near g E m hm.1 hW hu1 hM w ho₁.le hs₀ (hh.trans hhH) hhH hCΛ hεw hop hhs
      hlong hfar a b

end Step2Rows2

/-! ### Linear combinations of fields with deterministic time coefficients -/

section Step2Lin

/-- A deterministic `C¹` function of the time is in the bounded `C^{1,2}` class. -/
private theorem step2_heatClass_time {ι : Type*} [Fintype ι] (f f' : ℝ → ℂ)
    (hf : ∀ r, HasDerivAt f (f' r) r) (hf' : Continuous f') (a b : ℝ) :
    HeatClass (fun r (_ : ι → ℝ) => f r) a b := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun r => (hf r).continuousAt
  obtain ⟨C₁, hC₁⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (hfc.continuousOn (s := Set.Icc a b))
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf'.continuousOn (s := Set.Icc a b))
  refine ⟨(hfc.comp continuous_fst).continuousOn, ⟨C₁, fun r hr _ => hC₁ r
      (Set.Ioo_subset_Icc_self hr)⟩,
    ⟨fun r _ => f' r, fun r _ _ => hf r, (hf'.comp continuous_fst).continuousOn,
      C₂, fun r hr _ => hC₂ r (Set.Ioo_subset_Icc_self hr)⟩,
    ⟨fun _ _ => 0, fun _ _ => 0, fun r _ x => hasFDerivAt_const (f r) x,
      fun _ _ x => hasFDerivAt_const (0 : (ι → ℝ) →L[ℝ] ℂ) x, continuousOn_const,
      continuousOn_const, 0, fun _ _ _ => ⟨le_of_eq (norm_zero (E := (ι → ℝ) →L[ℝ] ℂ)),
        le_of_eq (norm_zero (E := (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℂ))⟩⟩⟩

/-- Finite sums stay in the class. -/
private theorem step2_heatClass_sum {ι S : Type*} [Fintype ι] (s : Finset S)
    (F : S → ℝ → (ι → ℝ) → ℂ) {a b : ℝ} (hF : ∀ l ∈ s, HeatClass (F l) a b) :
    HeatClass (fun r y => ∑ l ∈ s, F l r y) a b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using step2_heatClass_time (ι := ι) (fun _ => (0 : ℂ)) (fun _ => 0)
        (fun r => hasDerivAt_const r (0 : ℂ)) continuous_const a b
  | insert l s hl ih =>
      have h1 := hF l (Finset.mem_insert_self l s)
      have h2 := ih (fun l' hl' => hF l' (Finset.mem_insert_of_mem hl'))
      simpa [Finset.sum_insert hl] using h1.add h2

/-- A linear combination with `C¹` deterministic time coefficients stays in the class. -/
private theorem step2_heatClass_lincomb {ι S : Type*} [Fintype ι] [Fintype S]
    (f f' : S → ℝ → ℂ) (hf : ∀ l r, HasDerivAt (f l) (f' l r) r) (hf' : ∀ l, Continuous (f' l))
    (F : S → ℝ → (ι → ℝ) → ℂ) {a b : ℝ} (hF : ∀ l, HeatClass (F l) a b) :
    HeatClass (fun r y => ∑ l, f l r * F l r y) a b :=
  step2_heatClass_sum Finset.univ (fun l r y => f l r * F l r y)
    fun l _ => (step2_heatClass_time (f l) (f' l) (hf l) (hf' l) a b).mul (hF l)

/-- The second derivative along a line of a finite combination with constant coefficients. -/
private theorem step2_iter2_lincomb {S : Type*} [Fintype S] (c : S → ℂ) (φ : S → ℝ → ℂ)
    (hφ : ∀ l, ContDiff ℝ 2 (φ l)) :
    iteratedDeriv 2 (fun e => ∑ l, c l * φ l e) 0 = ∑ l, c l * iteratedDeriv 2 (φ l) 0 := by
  have hd1 : ∀ l, Differentiable ℝ (φ l) := fun l => (hφ l).differentiable (by norm_num)
  have hd2 : ∀ l, Differentiable ℝ (deriv (φ l)) := fun l => (hφ l).differentiable_deriv_two
  have h1 : deriv (fun e => ∑ l, c l * φ l e) = fun e => ∑ l, c l * deriv (φ l) e :=
    funext fun e => (HasDerivAt.fun_sum (u := Finset.univ)
      fun l _ => ((hd1 l e).hasDerivAt.const_mul (c l))).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1, (HasDerivAt.fun_sum (u := Finset.univ)
    fun l _ => ((hd2 l 0).hasDerivAt.const_mul (c l))).deriv]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [iteratedDeriv_succ, iteratedDeriv_one]

/-- A line `e ↦ G(y + e v)` of a `C²` function is `C²`. -/
private theorem step2_line_contDiff {ι : Type*} [Fintype ι] {G : (ι → ℝ) → ℂ}
    (hG : ContDiff ℝ 2 G) (y v : ι → ℝ) : ContDiff ℝ 2 (fun e : ℝ => G (y + e • v)) :=
  hG.comp (contDiff_const.add (contDiff_id.smul contDiff_const))

/-- The generator of a linear combination with `C¹` deterministic time coefficients:
`𝒢(Σ_l f_l F_l) = Σ_l (f_l' F_l + f_l 𝒢F_l)`. -/
private theorem step2_coordGen_lincomb {ι S : Type*} [Fintype ι] [Fintype S] (σ2 : ℝ)
    (f f' : S → ℝ → ℂ) (F : S → ℝ → (ι → ℝ) → ℂ) (u : ℝ) (y : ι → ℝ)
    (hf : ∀ l, HasDerivAt (f l) (f' l u) u)
    (hFt : ∀ l, DifferentiableAt ℝ (fun r => F l r y) u) (hFx : ∀ l, ContDiff ℝ 2 (F l u)) :
    coordGen σ2 (fun r x => ∑ l, f l r * F l r x) u y =
      ∑ l, (f' l u * F l u y + f l u * coordGen σ2 (F l) u y) := by
  unfold coordGen
  have ht : deriv (fun r => ∑ l, f l r * F l r y) u =
      ∑ l, (f' l u * F l u y + f l u * deriv (fun r => F l r y) u) :=
    (HasDerivAt.fun_sum (u := Finset.univ)
      fun l _ => ((hf l).mul (hFt l).hasDerivAt)).deriv
  have hs : ∀ i : ι, iteratedDeriv 2 (fun e : ℝ => ∑ l, f l u * F l u (y + e • Pi.single i 1)) 0 =
      ∑ l, f l u * iteratedDeriv 2 (fun e : ℝ => F l u (y + e • Pi.single i 1)) 0 := fun i =>
    step2_iter2_lincomb (fun l => f l u) (fun l e => F l u (y + e • Pi.single i 1))
      fun l => step2_line_contDiff (hFx l) y _
  rw [ht]
  simp only [hs]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  have : ∀ x : S, ∀ i : ι, ((σ2 / 2 : ℝ) : ℂ) *
      (f x u * iteratedDeriv 2 (fun e : ℝ => F x u (y + e • Pi.single i 1)) 0) =
      f x u * (((σ2 / 2 : ℝ) : ℂ) * iteratedDeriv 2 (fun e : ℝ => F x u (y + e • Pi.single i 1)) 0)
      := fun x i => by ring
  simp only [this]
  ring

/-- `|Σ_i z_i|² ≤ (Σ_i |z_i|)²`-type Minkowski bound for a family of vectors:
`Σ_j |Σ_l c_l v_{lj}|² ≤ (Σ_l |c_l| (Σ_j |v_{lj}|²)^{1/2})²`. -/
private theorem step2_minkowski {ι S : Type*} [Fintype ι] [Fintype S] (c : S → ℂ)
    (v : S → ι → ℂ) :
    ∑ j, ‖∑ l, c l * v l j‖ ^ 2 ≤ (∑ l, ‖c l‖ * Real.sqrt (∑ j, ‖v l j‖ ^ 2)) ^ 2 := by
  have h1 : ∀ j, ‖∑ l, c l * v l j‖ ^ 2 ≤ (∑ l, ‖c l‖ * ‖v l j‖) ^ 2 := fun j => by
    have := (norm_sum_le Finset.univ (fun l => c l * v l j)).trans (le_of_eq
      (Finset.sum_congr rfl fun l _ => norm_mul (c l) (v l j)))
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  refine (Finset.sum_le_sum fun j _ => h1 j).trans ?_
  have e1 : ∀ j, (∑ l, ‖c l‖ * ‖v l j‖) ^ 2 =
      ∑ l, ∑ l', ‖c l‖ * ‖c l'‖ * (‖v l j‖ * ‖v l' j‖) := by
    intro j
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => by ring
  have e : ∑ j, (∑ l, ‖c l‖ * ‖v l j‖) ^ 2 =
      ∑ l, ∑ l', ‖c l‖ * ‖c l'‖ * ∑ j, ‖v l j‖ * ‖v l' j‖ := by
    simp only [e1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l' _ => by rw [Finset.mul_sum]
  rw [e, sq, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun l' _ => ?_
  have hcs : ∑ j, ‖v l j‖ * ‖v l' j‖ ≤
      Real.sqrt (∑ j, ‖v l j‖ ^ 2) * Real.sqrt (∑ j, ‖v l' j‖ ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have := mul_le_mul_of_nonneg_left hcs (mul_nonneg (norm_nonneg (c l)) (norm_nonneg (c l')))
  linarith [show ‖c l‖ * Real.sqrt (∑ j, ‖v l j‖ ^ 2) * (‖c l'‖ * Real.sqrt (∑ j, ‖v l' j‖ ^ 2)) =
    ‖c l‖ * ‖c l'‖ * (Real.sqrt (∑ j, ‖v l j‖ ^ 2) * Real.sqrt (∑ j, ‖v l' j‖ ^ 2)) by ring]

/-- The carré du champ of a linear combination:
`Γ(Σ_l c_l F_l) ≤ (Σ_l |c_l| Γ(F_l)^{1/2})²`, for `σ² ≥ 0` and `C²` fields. -/
private theorem step2_coordGamma_lincomb {ι S : Type*} [Fintype ι] [Fintype S] (σ2 : ℝ)
    (hσ2 : 0 ≤ σ2) (c : S → ℂ) (F : S → (ι → ℝ) → ℂ) (y : ι → ℝ)
    (hF : ∀ l, ContDiff ℝ 2 (F l)) :
    ‖coordGamma σ2 (fun x => ∑ l, c l * F l x) (fun x => ∑ l, c l * F l x) y‖ ≤
      (∑ l, ‖c l‖ * Real.sqrt ‖coordGamma σ2 (F l) (F l) y‖) ^ 2 := by
  have hd : ∀ i : ι, deriv (fun e : ℝ => ∑ l, c l * F l (y + e • Pi.single i 1)) 0 =
      ∑ l, c l * deriv (fun e : ℝ => F l (y + e • Pi.single i 1)) 0 := fun i =>
    (HasDerivAt.fun_sum (u := Finset.univ) fun l _ =>
      ((((step2_line_contDiff (hF l) y (Pi.single i 1)).differentiable (by norm_num))
        0).hasDerivAt.const_mul (c l))).deriv
  rw [step2_cgamma_eq]
  simp only [hd]
  have hl : ∀ l, ‖coordGamma σ2 (F l) (F l) y‖ =
      σ2 * ∑ i, ‖deriv (fun e : ℝ => F l (y + e • Pi.single i 1)) 0‖ ^ 2 := fun l => by
    rw [step2_cgamma_eq, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  simp only [hl]
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hm := step2_minkowski c (fun l i => deriv (fun e : ℝ => F l (y + e • Pi.single i 1)) 0)
  have hsq : ∀ l, Real.sqrt (σ2 * ∑ i, ‖deriv (fun e : ℝ => F l (y + e • Pi.single i 1)) 0‖ ^ 2) =
      Real.sqrt σ2 * Real.sqrt (∑ i, ‖deriv (fun e : ℝ => F l (y + e • Pi.single i 1)) 0‖ ^ 2) :=
    fun l => Real.sqrt_mul hσ2 _
  simp only [hsq]
  have e2 : (∑ l, ‖c l‖ * (Real.sqrt σ2 *
      Real.sqrt (∑ i, ‖deriv (fun e : ℝ => F l (y + e • Pi.single i 1)) 0‖ ^ 2))) ^ 2 =
      σ2 * (∑ l, ‖c l‖ *
        Real.sqrt (∑ i, ‖deriv (fun e : ℝ => F l (y + e • Pi.single i 1)) 0‖ ^ 2)) ^ 2 := by
    have : ∀ l, ‖c l‖ * (Real.sqrt σ2 *
        Real.sqrt (∑ i, ‖deriv (fun e : ℝ => F l (y + e • Pi.single i 1)) 0‖ ^ 2)) =
        Real.sqrt σ2 * (‖c l‖ *
          Real.sqrt (∑ i, ‖deriv (fun e : ℝ => F l (y + e • Pi.single i 1)) 0‖ ^ 2)) :=
      fun l => by ring
    simp only [this, ← Finset.mul_sum, mul_pow, Real.sq_sqrt hσ2]
  rw [e2]
  exact mul_le_mul_of_nonneg_left hm hσ2

end Step2Lin

/-! ### The pair propagator -/

section Step2Prop

variable {L : ℕ}

/-- `I - rP` is invertible for a probability kernel and `0 ≤ r < 1` (its mixed kernel has row
sums `(1 - r)⁻¹ ≠ 0`). -/
private theorem step2_isUnit (P : Matrix (Fin L) (Fin L) ℝ) (hP : ∀ a b, 0 ≤ P a b)
    (hrow : ∀ a, ∑ b, P a b = 1) (hL : 1 ≤ L) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    IsUnit (1 - r • P).det := by
  by_contra h
  have h0 : mixedKer P r = 0 := by
    unfold mixedKer; rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.mul_zero]
  have hr := (mixedKer_nonneg_row P hP hrow r hr0 hr1).2 ⟨0, by omega⟩
  rw [h0] at hr
  simp only [Matrix.zero_apply, Finset.sum_const_zero] at hr
  have : (0 : ℝ) < (1 - r)⁻¹ := inv_pos.mpr (by linarith)
  linarith

/-- `U^{+-}_{r,v} = (I - vP)⁻¹ - r P(I - vP)⁻¹`, affine in `r`. -/
private theorem step2_propPM_affine (P : Matrix (Fin L) (Fin L) ℝ) (r v : ℝ) :
    propPM P r v = (1 - v • P)⁻¹ - r • mixedKer P v := by
  unfold propPM mixedKer
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]

/-- `∂_r U^{+-}_{r,v} = -P(I - vP)⁻¹`. -/
private theorem step2_propPM_hasDerivAt (P : Matrix (Fin L) (Fin L) ℝ) (v : ℝ) (a c : Fin L)
    (r : ℝ) : HasDerivAt (fun r' => propPM P r' v a c) (-mixedKer P v a c) r := by
  have e : (fun r' => propPM P r' v a c) = fun r' => (1 - v • P)⁻¹ a c - r' * mixedKer P v a c := by
    funext r'
    rw [step2_propPM_affine]
    simp [Matrix.sub_apply, Matrix.smul_apply]
  rw [e]
  have := ((hasDerivAt_id r).mul_const (mixedKer P v a c)).const_sub ((1 - v • P)⁻¹ a c)
  simpa using this

/-- `U^{+-}_{v,v} = I`. -/
private theorem step2_propPM_self (P : Matrix (Fin L) (Fin L) ℝ) (v : ℝ)
    (h : IsUnit (1 - v • P).det) : propPM P v v = 1 := by
  unfold propPM; exact Matrix.mul_nonsing_inv _ h

/-- `U^{+-}_{r,v} P(I - rP)⁻¹ = P(I - vP)⁻¹`: the propagator removes the kernel term of (C.16)
[fo:eq:pair-error]. -/
private theorem step2_propPM_mul_mixedKer (P : Matrix (Fin L) (Fin L) ℝ) {r v : ℝ}
    (hr : IsUnit (1 - r • P).det) (hv : IsUnit (1 - v • P).det) :
    propPM P r v * mixedKer P r = mixedKer P v := by
  unfold propPM mixedKer
  set A := (1 : Matrix (Fin L) (Fin L) ℝ) - r • P with hA
  set B := (1 : Matrix (Fin L) (Fin L) ℝ) - v • P with hB
  have hAP : A * P = P * A := by
    rw [hA, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul]
  have hBP : B * P = P * B := by
    rw [hB, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul]
  have hAB : A * B = B * A := by
    rw [hA, hB]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul]
    module
  have hBiP : B⁻¹ * P = P * B⁻¹ := by
    calc B⁻¹ * P = B⁻¹ * P * (B * B⁻¹) := by rw [Matrix.mul_nonsing_inv _ hv, Matrix.mul_one]
      _ = B⁻¹ * (P * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = B⁻¹ * (B * P) * B⁻¹ := by rw [hBP]
      _ = (B⁻¹ * B) * P * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = P * B⁻¹ := by rw [Matrix.nonsing_inv_mul _ hv, Matrix.one_mul]
  have hBiA : B⁻¹ * A = A * B⁻¹ := by
    calc B⁻¹ * A = B⁻¹ * A * (B * B⁻¹) := by rw [Matrix.mul_nonsing_inv _ hv, Matrix.mul_one]
      _ = B⁻¹ * (A * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = B⁻¹ * (B * A) * B⁻¹ := by rw [hAB]
      _ = (B⁻¹ * B) * A * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = A * B⁻¹ := by rw [Matrix.nonsing_inv_mul _ hv, Matrix.one_mul]
  calc A * B⁻¹ * (P * A⁻¹) = B⁻¹ * (A * P) * A⁻¹ := by
        rw [← hBiA]; simp only [Matrix.mul_assoc]
    _ = B⁻¹ * P * (A * A⁻¹) := by rw [hAP]; simp only [Matrix.mul_assoc]
    _ = P * B⁻¹ := by rw [Matrix.mul_nonsing_inv _ hr, Matrix.mul_one, hBiP]

/-- Complex form of the cancellation, with `u K = k_v` and `K` symmetric. -/
private theorem step2_cancel_c (u K kv : Fin L → Fin L → ℂ)
    (hUK : ∀ x e, ∑ c, u x c * K c e = kv x e) (hKs : ∀ x y, K x y = K y x)
    (D : Fin L → Fin L → ℂ) (a b : Fin L) :
    ∑ c, ∑ d, (u a c * u b d) * ∑ e, (K c e * D e d + D c e * K e d) =
      ∑ c, ∑ d, (kv a c * u b d + u a c * kv b d) * D c d := by
  have h1 : ∑ c, ∑ d, (u a c * u b d) * ∑ e, K c e * D e d = ∑ c, ∑ d, kv a c * u b d * D c d := by
    calc ∑ c, ∑ d, (u a c * u b d) * ∑ e, K c e * D e d
        = ∑ d, ∑ c, ∑ e, u b d * (u a c * K c e * D e d) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun e _ => by ring
      _ = ∑ d, ∑ e, u b d * ((∑ c, u a c * K c e) * D e d) := by
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
      _ = ∑ e, ∑ d, kv a e * u b d * D e d := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun d _ => ?_
          rw [hUK]; ring
  have h2 : ∑ c, ∑ d, (u a c * u b d) * ∑ e, D c e * K e d = ∑ c, ∑ d, u a c * kv b d * D c d := by
    calc ∑ c, ∑ d, (u a c * u b d) * ∑ e, D c e * K e d
        = ∑ c, ∑ e, ∑ d, u a c * (D c e * (u b d * K d e)) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun d _ => ?_
          rw [hKs e d]; ring
      _ = ∑ c, ∑ e, u a c * (D c e * ∑ d, u b d * K d e) := by
          refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
      _ = ∑ c, ∑ e, u a c * kv b e * D c e := by
          refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
          rw [hUK]; ring
  simp only [Finset.sum_add_distrib, mul_add]
  rw [h1, h2]
  simp only [add_mul, Finset.sum_add_distrib]

/-- The cancellation of the kernel term against the time derivative of the propagators, in the
generator of `Y = (U^{+-}_{r,v})^{⊗2} D₂`: with `U K = K_v` and `K` symmetric,
`Σ_{cd} [-(K_v ⊗ U + U ⊗ K_v)_{ab,cd} D_{cd} + (U ⊗ U)_{ab,cd} (K D + D K)_{cd}] = 0`. -/
private theorem step2_cancel (U K Kv : Matrix (Fin L) (Fin L) ℝ)
    (hUK : U * K = Kv) (hKs : ∀ x y, K x y = K y x) (D : Fin L → Fin L → ℂ) (a b : Fin L) :
    ∑ l : Fin L × Fin L, (-(((Kv a l.1 * U b l.2 + U a l.1 * Kv b l.2 : ℝ) : ℂ)) * D l.1 l.2 +
      ((U a l.1 * U b l.2 : ℝ) : ℂ) *
        ∑ e, (((K l.1 e : ℝ) : ℂ) * D e l.2 + D l.1 e * ((K e l.2 : ℝ) : ℂ))) = 0 := by
  have hUK' : ∀ x e, ∑ c, ((U x c : ℝ) : ℂ) * ((K c e : ℝ) : ℂ) = ((Kv x e : ℝ) : ℂ) := by
    intro x e
    rw [← hUK, Matrix.mul_apply]; push_cast; rfl
  have h := step2_cancel_c (fun x y => ((U x y : ℝ) : ℂ)) (fun x y => ((K x y : ℝ) : ℂ))
    (fun x y => ((Kv x y : ℝ) : ℂ)) hUK' (fun x y => by rw [hKs x y]) D a b
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_add_distrib, Complex.ofReal_add, Complex.ofReal_mul]
  simp only [Finset.sum_add_distrib] at h
  rw [h]
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

end Step2Prop

/-! ### The propagated mixed pair -/

section Step2Field

variable {L : ℕ}

/-- The coefficients `U^{+-}_{r,v}(a, c) U^{+-}_{r,v}(b, d)` of `Y_r = (U^{+-}_{r,v})^{⊗2} D₂`. -/
private def step2Coef (P : Matrix (Fin L) (Fin L) ℝ) (v : ℝ) (a b : Fin L) (l : Fin L × Fin L)
    (r : ℝ) : ℝ :=
  propPM P r v a l.1 * propPM P r v b l.2

/-- The time derivative of `step2Coef`. -/
private def step2Coef' (P : Matrix (Fin L) (Fin L) ℝ) (v : ℝ) (a b : Fin L) (l : Fin L × Fin L)
    (r : ℝ) : ℝ :=
  -(mixedKer P v a l.1 * propPM P r v b l.2 + propPM P r v a l.1 * mixedKer P v b l.2)

/-- The propagated mixed pair `Y_r = Σ_{cd} U^{+-}_{r,v}(a,c) U^{+-}_{r,v}(b,d) D₂(r; c, d)` of
the proof of (C.17) [gc:eq:spatialstop], as a field of the Gaussian block coordinates. -/
private def step2Y (g E : ℝ) (m : ℂ) (W : ℕ) (P : Matrix (Fin L) (Fin L) ℝ) (v : ℝ)
    (a b : Fin L) (r : ℝ) (x : Ω W L) : ℂ :=
  ∑ l, ((step2Coef P v a b l r : ℝ) : ℂ) * pairErrField g E m W L r x l

private theorem step2_coef_hasDerivAt (P : Matrix (Fin L) (Fin L) ℝ) (v : ℝ) (a b : Fin L)
    (l : Fin L × Fin L) (r : ℝ) :
    HasDerivAt (fun r' => ((step2Coef P v a b l r' : ℝ) : ℂ))
      ((step2Coef' P v a b l r : ℝ) : ℂ) r := by
  have h := (step2_propPM_hasDerivAt P v a l.1 r).mul (step2_propPM_hasDerivAt P v b l.2 r)
  have h2 := h.ofReal_comp
  unfold step2Coef step2Coef'
  convert h2 using 1
  push_cast; ring

private theorem step2_coef'_cont (P : Matrix (Fin L) (Fin L) ℝ) (v : ℝ) (a b : Fin L)
    (l : Fin L × Fin L) : Continuous (fun r => ((step2Coef' P v a b l r : ℝ) : ℂ)) := by
  have hU : ∀ x y, Continuous (fun r => propPM P r v x y) := fun x y =>
    continuous_iff_continuousAt.2 fun r => (step2_propPM_hasDerivAt P v x y r).continuousAt
  unfold step2Coef'
  exact Complex.continuous_ofReal.comp ((((continuous_const.mul (hU b l.2)).add
    ((hU a l.1).mul continuous_const))).neg)

/-- `Y` is in the bounded `C^{1,2}` class on `(-1/2, (1+v)/2)`. -/
private theorem step2_heatClass_Y (g E : ℝ) (m : ℂ) (W : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ L)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (P : Matrix (Fin L) (Fin L) ℝ) {v : ℝ}
    (hv : v < 1) (a b : Fin L) :
    HeatClass (step2Y g E m W P v a b) (-1 / 2) ((1 + v) / 2) :=
  step2_heatClass_lincomb (fun l r => ((step2Coef P v a b l r : ℝ) : ℂ))
    (fun l r => ((step2Coef' P v a b l r : ℝ) : ℂ)) (fun l r => step2_coef_hasDerivAt P v a b l r)
    (fun l => step2_coef'_cont P v a b l) (fun l r x => pairErrField g E m W L r x l)
    fun l => heatClass_pairErrField g E m W L hW hL hm l (by norm_num) (by linarith)

/-- `Y_v = D₂(v; a, b)`. -/
private theorem step2_Y_self (g E : ℝ) (m : ℂ) (W : ℕ) (P : Matrix (Fin L) (Fin L) ℝ) {v : ℝ}
    (hv : IsUnit (1 - v • P).det) (a b : Fin L) (x : Ω W L) :
    step2Y g E m W P v a b v x = pairErrField g E m W L v x (a, b) := by
  unfold step2Y step2Coef
  rw [step2_propPM_self P v hv]
  rw [Finset.sum_eq_single (a, b)]
  · simp
  · intro l _ hl
    have : l.1 ≠ a ∨ l.2 ≠ b := by
      by_contra h; push Not at h; exact hl (Prod.ext h.1 h.2)
    rcases this with h | h
    · simp [Matrix.one_apply_ne' h]
    · simp [Matrix.one_apply_ne' h]
  · simp

/-- `|Y_r| ≤ Σ_{cd} U(a,c)U(b,d)|D₂(r; c, d)|` for `0 ≤ r ≤ v < 1`. -/
private theorem step2_Y_norm_le (g E : ℝ) (m : ℂ) (W : ℕ) (P : Matrix (Fin L) (Fin L) ℝ)
    (hP : ∀ a b, 0 ≤ P a b) (hrow : ∀ a, ∑ b, P a b = 1) {r v : ℝ} (hr : 0 ≤ r) (hrv : r ≤ v)
    (hv : v < 1) (a b : Fin L) (x : Ω W L) :
    ‖step2Y g E m W P v a b r x‖ ≤
      ∑ l, step2Coef P v a b l r * ‖pairErrField g E m W L r x l‖ := by
  have h0 := (propPM_nonneg_row P hP hrow r v hr hrv hv).1
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun l _ => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg]
  exact mul_nonneg (h0 _ _) (h0 _ _)

/-- The generator of `Y`: the kernel term of (C.16) [fo:eq:pair-error] cancels against the time
derivative of the propagators, `𝒢Y_r = Σ_{cd} U(a,c)U(b,d)(𝒲₂ + γ_gW D₂²)(c, d)`. -/
private theorem step2_gen_Y (g E : ℝ) (m : ℂ) (W : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ L)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {r v : ℝ} (hr0 : 0 ≤ r) (hrv : r ≤ v)
    (hv : v < 1) (a b : Fin L) (y : Ω W L) :
    coordGen (gammaG g / W) (step2Y g E m W (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))
        v a b) r y =
      ∑ l, ((step2Coef (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v a b l r : ℝ) : ℂ) *
        (lightW g E m ![l.1, l.2] ![true, false] r
            (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y) +
          ((gammaG g * W : ℝ) : ℂ) * ∑ e : Fin L,
            (resLoop g E m ![l.1, e] ![true, false] r
                (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y) -
              primLoop g W L E m r ![l.1, e] ![true, false]) *
            (resLoop g E m ![e, l.2] ![true, false] r
                (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y) -
              primLoop g W L E m r ![e, l.2] ![true, false])) := by
  set P := pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) with hPdef
  set M := blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y with hMdef
  have hL1 : 1 ≤ L := by omega
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  have hP0 : ∀ x z, 0 ≤ P x z := fun x z => by simp only [hPdef, pairP, Matrix.of_apply]; positivity
  have hProw : ∀ x, ∑ z, P x z = 1 := fun x => pairP_row_sum (hopB g) (gammaG g) hγ L hL1 E m hm x
  have hr1 : r < 1 := by linarith
  have hv0 : 0 ≤ v := hr0.trans hrv
  have hUr := step2_isUnit P hP0 hProw hL1 hr0 hr1
  have hUv := step2_isUnit P hP0 hProw hL1 hv0 hv
  have hrI : r ∈ Set.Ioo (-1 / 2 : ℝ) ((1 + v) / 2) := ⟨by linarith, by linarith⟩
  have hcls : ∀ l : Fin L × Fin L, HeatClass (fun r x => pairErrField g E m W L r x l) (-1 / 2)
      ((1 + v) / 2) := fun l =>
    heatClass_pairErrField g E m W L hW hL hm l (by norm_num) (by linarith)
  have hlin := step2_coordGen_lincomb (gammaG g / W)
    (fun l r => ((step2Coef P v a b l r : ℝ) : ℂ)) (fun l r => ((step2Coef' P v a b l r : ℝ) : ℂ))
    (fun l r x => pairErrField g E m W L r x l) r y
    (fun l => step2_coef_hasDerivAt P v a b l r)
    (fun l => (step2_heat_slice (hcls l) hrI).2.2 y) (fun l => (step2_heat_slice (hcls l) hrI).2.1)
  have hDl : ∀ l : Fin L × Fin L, coordGen (gammaG g / W)
      (fun r x => pairErrField g E m W L r x l) r y =
      lightW g E m ![l.1, l.2] ![true, false] r M +
        ∑ c : Fin L,
          ((((mixedKer P r l.1 c : ℝ) : ℂ) *
              (resLoop g E m ![c, l.2] ![true, false] r M -
                primLoop g W L E m r ![c, l.2] ![true, false])) +
            (resLoop g E m ![l.1, c] ![true, false] r M -
                primLoop g W L E m r ![l.1, c] ![true, false]) *
              ((mixedKer P r c l.2 : ℝ) : ℂ)) +
        ((gammaG g * W : ℝ) : ℂ) * ∑ c : Fin L,
          (resLoop g E m ![l.1, c] ![true, false] r M -
            primLoop g W L E m r ![l.1, c] ![true, false]) *
            (resLoop g E m ![c, l.2] ![true, false] r M -
              primLoop g W L E m r ![c, l.2] ![true, false]) := by
    intro l
    rw [step2_coordGen_eq]
    exact blockGen_pairErr g E m W L hW hL hm ⟨by linarith, hr1⟩ (step2_slice_herm g hW y) l.1 l.2
  have hKs : ∀ x z, mixedKer P r x z = mixedKer P r z x := fun x z =>
    step2_mixedKer_symm _ (step2_pairP_symm _ _ _ _ _) r x z
  have hcan := step2_cancel (propPM P r v) (mixedKer P r) (mixedKer P v)
    (step2_propPM_mul_mixedKer P hUr hUv) hKs (fun x z => resLoop g E m ![x, z] ![true, false] r M -
      primLoop g W L E m r ![x, z] ![true, false]) a b
  beta_reduce at hcan
  have e : ∀ l : Fin L × Fin L,
      ((step2Coef' P v a b l r : ℝ) : ℂ) * pairErrField g E m W L r y l +
        ((step2Coef P v a b l r : ℝ) : ℂ) *
          coordGen (gammaG g / W) (fun r x => pairErrField g E m W L r x l) r y =
      (-(((mixedKer P v a l.1 * propPM P r v b l.2 + propPM P r v a l.1 * mixedKer P v b l.2 :
          ℝ) : ℂ)) * (resLoop g E m ![l.1, l.2] ![true, false] r M -
            primLoop g W L E m r ![l.1, l.2] ![true, false]) +
        ((propPM P r v a l.1 * propPM P r v b l.2 : ℝ) : ℂ) *
          ∑ e, (((mixedKer P r l.1 e : ℝ) : ℂ) * (resLoop g E m ![e, l.2] ![true, false] r M -
            primLoop g W L E m r ![e, l.2] ![true, false]) +
            (resLoop g E m ![l.1, e] ![true, false] r M -
              primLoop g W L E m r ![l.1, e] ![true, false]) * ((mixedKer P r e l.2 : ℝ) : ℂ))) +
      ((step2Coef P v a b l r : ℝ) : ℂ) * (lightW g E m ![l.1, l.2] ![true, false] r M +
          ((gammaG g * W : ℝ) : ℂ) * ∑ e : Fin L,
            (resLoop g E m ![l.1, e] ![true, false] r M -
              primLoop g W L E m r ![l.1, e] ![true, false]) *
            (resLoop g E m ![e, l.2] ![true, false] r M -
              primLoop g W L E m r ![e, l.2] ![true, false])) := by
    intro l
    rw [hDl l, step2_pairErrField_eq]
    unfold step2Coef step2Coef'
    push_cast
    ring
  unfold step2Y
  rw [hlin, Finset.sum_congr rfl fun l _ => e l, Finset.sum_add_distrib, hcan, zero_add]

/-- The bracket of `Y`: `Γ(Y_r) ≤ (Σ_{cd} U(a,c)U(b,d) Γ(ℒ₂(c,d))^{1/2})²`. -/
private theorem step2_gamma_Y (g E : ℝ) (m : ℂ) (W : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ L)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (P : Matrix (Fin L) (Fin L) ℝ)
    (hP : ∀ a b, 0 ≤ P a b) (hrow : ∀ a, ∑ b, P a b = 1) {r v : ℝ} (hr0 : 0 ≤ r) (hrv : r ≤ v)
    (hv : v < 1) (a b : Fin L) (y : Ω W L) :
    ‖coordGamma (gammaG g / W) (step2Y g E m W P v a b r) (step2Y g E m W P v a b r) y‖ ≤
      (∑ l, step2Coef P v a b l r * Real.sqrt (blockGamma W L (gammaG g)
        (resLoop g E m ![l.1, l.2] ![true, false] r) (resLoop g E m ![l.1, l.2] ![true, false] r)
        (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y)).re) ^ 2 := by
  have hγ : 0 ≤ gammaG g / W := by unfold gammaG; positivity
  have hrI : r ∈ Set.Ioo (-1 / 2 : ℝ) ((1 + v) / 2) := ⟨by linarith, by linarith⟩
  have hcls : ∀ l : Fin L × Fin L, HeatClass (fun r x => pairErrField g E m W L r x l) (-1 / 2)
      ((1 + v) / 2) := fun l =>
    heatClass_pairErrField g E m W L hW hL hm l (by norm_num) (by linarith)
  have h0 := (propPM_nonneg_row P hP hrow r v hr0 hrv hv).1
  have h := step2_coordGamma_lincomb (gammaG g / W) hγ
    (fun l => ((step2Coef P v a b l r : ℝ) : ℂ)) (fun l x => pairErrField g E m W L r x l) y
    (fun l => (step2_heat_slice (hcls l) hrI).2.1)
  unfold step2Y
  refine h.trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ step2Coef P v a b l r from
    mul_nonneg (h0 _ _) (h0 _ _))]
  congr 2
  rw [← step2_gamma_re_eq_norm hγ, step2_coordGamma_eq]

end Step2Field

/-! ### Normalized sources at a good point -/

section Step2Good

open scoped Matrix.Norms.L2Operator

/-- The constant of the generator sources (C.18) [fo:eq:pair-far-light], (C.20)
[fo:eq:pair-near-sources] and of the quadratic term, normalized by `ζ_r² w_r/(1 - r)`. -/
private def step2Src (ω R Λ C' Cc lH ζt : ℝ) : ℝ :=
  ω * (2 * Real.sqrt 2 * ω ^ 3 * R ^ 4 * (4 * lH + 2) + 1) +
    2 * ω * R ^ 2 * (C' + Λ) * max (ω ^ 2 * R) (Real.sqrt (C' + Λ)) * Cc * ζt + Λ ^ 2 * Cc * ζt

/-- The constant of the bracket sources (C.19) [fo:eq:pair-far-bracket], (C.20)
[fo:eq:pair-near-sources], normalized by `ζ_r⁴ w_r²/(1 - r)`. -/
private def step2Brk (ω R Λ C' Cc lH ζt : ℝ) : ℝ :=
  ω ^ 2 * (4 * ω ^ 5 * R ^ 5 * (4 * lH + 4) + 4 * ω ^ 3 * R ^ 3) +
    4 * (C' + Λ) * max (ω ^ 2 * R) (Real.sqrt (C' + Λ)) ^ 4 * Cc * ζt

/-- `γWℓ = (ζ e)⁻¹` turns `γWℓ K ζ^{n+1}` into `K ζ^n e⁻¹`. -/
private theorem step2_scale_mul {γWℓ ζ e K : ℝ} (hζ : 0 < ζ) (he : 0 < e) (h : γWℓ = (ζ * e)⁻¹)
    (n : ℕ) : γWℓ * (K * ζ ^ (n + 1)) = K * ζ ^ n * e⁻¹ := by
  rw [h, mul_inv, pow_succ]
  field_simp

set_option maxHeartbeats 1000000 in
-- The rows combine many real inequalities at once.
/-- At a good point (Step 1 envelopes with loss `ω`, the mixed pair at `Λ ζ² w`, the regime rows
at the scale `ℓ = ℓ_r`, `γ_gWℓζ(1 - r) = 1`), the sources of the propagated pair satisfy
`|𝒲₂| + γ_gW|D₂²| ≤ Src ζ² w/(1 - r)` and `Γ(ℒ₂) ≤ Brk ζ⁴ w²/(1 - r)` at every pair. -/
private theorem step2_good_rows (g E : ℝ) (m : ℂ) {W L : ℕ} (hW : 1 ≤ W) (hL : 3 ≤ L)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {u : ℝ} (hu1 : u < 1)
    {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    (w : Fin L → Fin L → ℝ) (hw0 : ∀ x y, 0 ≤ w x y) (hw2 : ∀ x y, w x y ≤ 2)
    (hws : ∀ x y, w x y = w y x) {wmin : ℝ} (hwmin0 : 0 < wmin) (hwmin : ∀ x y, wmin ≤ w x y)
    {ω R Λ ζ ζt Cc ℓ h lH εw C' : ℝ} (hω : 2 ≤ ω) (hR : 1 ≤ R) (hΛ : 0 ≤ Λ) (hζ : 0 < ζ)
    (hζt : ζ ≤ ζt) (hCc : 0 ≤ Cc) (hℓ : 1 ≤ ℓ) (hh : 0 ≤ h) (hhH : h ≤ ℓ * lH) (hC' : 0 ≤ C')
    (hεw : 0 ≤ εw) (hΓ : gammaG g * W * ℓ * ζ * (1 - u) = 1)
    (hrem1 : 2 * Real.sqrt 2 * gammaG g * W * (ω * R ^ 2 * ζ) * (ω * R * ζ) *
      (L * Real.sqrt ((ω * R * ζ) * max ((C' + Λ) * ζ ^ 2 /
        max (ω ^ 2) ((C' + Λ) * ζ ^ 2 / (ω * R * ζ) ^ 2)) ((ω * R * ζ) / 2) * 1 ^ 2 *
        (max (ω ^ 2) ((C' + Λ) * ζ ^ 2 / (ω * R * ζ) ^ 2) * εw))) ≤ ζ ^ 2 / (1 - u))
    (hrem2 : (C' + Λ) * εw * (L / ℓ) ≤ 1)
    (hD : ∀ x y, ‖resLoop g E m ![x, y] ![true, false] u M -
      primLoop g W L E m u ![x, y] ![true, false]‖ ≤ Λ * ζ ^ 2 * w x y)
    (hconv : ∀ x y, ∑ c, w x c * w c y ≤ Cc * ℓ * w x y ∧
      ∑ c, Real.sqrt (w x c * w c y) ≤ Cc * ℓ * Real.sqrt (w x y))
    (hop : ∀ x y, ‖blockOf (resolventMat M (zChar g E m u)) x y‖ ≤ W * (ω * R * ζ))
    (hhs : ∀ x y, blockHS2 (resolventMat M (zChar g E m u)) x y ≤ (W : ℝ) ^ 2 * (ω * R * ζ))
    (havg : ∀ c, ‖blockTr (resolventMat M (zChar g E m u) -
      dysonMat (hopB g) (gammaG g) L E m ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) c c‖ ≤ ω * R ^ 2 * ζ)
    (hprim : ∀ x y, h < cycDist x y →
      ‖primLoop g W L E m u ![x, y] ![true, false]‖ ≤ C' * ζ ^ 2 * w x y)
    (hshort : ∀ x y, (cycDist x y : ℝ) ≤ 2 * h → ω⁻¹ ≤ w x y)
    (hfar : ∀ x y, ℓ * lH < cycDist x y → w x y ≤ εw) (a b : Fin L) :
    ‖lightW g E m ![a, b] ![true, false] u M‖ + gammaG g * W *
        ‖∑ c, (resLoop g E m ![a, c] ![true, false] u M -
            primLoop g W L E m u ![a, c] ![true, false]) *
          (resLoop g E m ![c, b] ![true, false] u M -
            primLoop g W L E m u ![c, b] ![true, false])‖ ≤
      step2Src ω R Λ C' Cc lH ζt * ζ ^ 2 * w a b / (1 - u) ∧
    (blockGamma W L (gammaG g) (resLoop g E m ![a, b] ![true, false] u)
        (resLoop g E m ![a, b] ![true, false] u) M).re ≤
      step2Brk ω R Λ C' Cc lH ζt * ζ ^ 4 * w a b ^ 2 / (1 - u) := by
  have hω0 : 0 < ω := by linarith
  have hω1 : 1 ≤ ω := by linarith
  have heu : 0 < 1 - u := by linarith
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hℓ0 : 0 < ℓ := by linarith
  have ho₁ : 0 < ω * R * ζ := by positivity
  set K₀ := max (ω ^ 2) ((C' + Λ) * ζ ^ 2 / (ω * R * ζ) ^ 2) with hK₀
  have hK₀ω : ω ≤ K₀ := le_max_of_le_left (by nlinarith)
  have hK₀b : (C' + Λ) * ζ ^ 2 ≤ (ω * R * ζ) ^ 2 * K₀ := by
    have : (C' + Λ) * ζ ^ 2 / (ω * R * ζ) ^ 2 ≤ K₀ := le_max_right _ _
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  obtain ⟨hq, hlf, hln, hbf, hbn⟩ := step2_point_rows g E m hW hL hm hu1 hM w hw0 hw2 hws hwmin0
    hwmin (Λ := Λ) (ζ := ζ) (Cc := Cc) (ℓ := ℓ) (o₁ := ω * R * ζ) (s₀ := ω * R * ζ)
    (τ := ω * R ^ 2 * ζ) (ω := ω) (h := h) (H := ℓ * lH) (εw := εw) (C' := C') (K₀ := K₀)
    hΛ hζ.le ho₁ ho₁.le (by positivity) hω1 hh hhH hC' hK₀ω hK₀b hεw hD hconv hop hhs havg hprim
    hshort hfar a b
  have hwab := hw0 a b
  have hγWℓ : gammaG g * W * ℓ = (ζ * (1 - u))⁻¹ := by
    have h1 : (gammaG g * W * ℓ) * (ζ * (1 - u)) = 1 := by
      calc _ = gammaG g * W * ℓ * ζ * (1 - u) := by ring
        _ = 1 := hΓ
    exact (mul_eq_one_iff_eq_inv₀ (mul_pos hζ heu).ne').mp h1
  have hCΛ : 0 ≤ C' + Λ := by linarith
  have hmx0 : 0 ≤ max (ω ^ 2 * R) (Real.sqrt (C' + Λ)) := le_max_of_le_right (Real.sqrt_nonneg _)
  generalize hmx : max (ω ^ 2 * R) (Real.sqrt (C' + Λ)) = mx at hmx0
  have hmax : max (ω * (ω * R * ζ)) (Real.sqrt (C' + Λ) * ζ) = ζ * mx := by
    rw [← hmx, mul_max_of_nonneg _ _ hζ.le]
    congr 1 <;> ring
  have hiu : 0 < (1 - u)⁻¹ := inv_pos.mpr heu
  -- the quadratic term
  have hquad : gammaG g * W * ‖∑ c, (resLoop g E m ![a, c] ![true, false] u M -
      primLoop g W L E m u ![a, c] ![true, false]) *
        (resLoop g E m ![c, b] ![true, false] u M - primLoop g W L E m u ![c, b] ![true, false])‖ ≤
      Λ ^ 2 * Cc * ζt * ζ ^ 2 * w a b / (1 - u) := by
    calc _ ≤ gammaG g * W * ((Λ * ζ ^ 2) ^ 2 * Cc * ℓ * w a b) :=
          mul_le_mul_of_nonneg_left hq (by positivity)
      _ = Λ ^ 2 * Cc * ζ * ζ ^ 2 * w a b * (1 - u)⁻¹ := by
          rw [show gammaG g * W * ((Λ * ζ ^ 2) ^ 2 * Cc * ℓ * w a b) =
            (gammaG g * W * ℓ) * ((Λ ^ 2 * Cc * w a b) * ζ ^ (3 + 1)) by ring,
            step2_scale_mul hζ heu hγWℓ]
          ring
      _ ≤ Λ ^ 2 * Cc * ζt * ζ ^ 2 * w a b * (1 - u)⁻¹ := by
          gcongr
      _ = _ := by rw [div_eq_mul_inv]
  -- the light term
  generalize hA1 : 2 * Real.sqrt 2 * ω ^ 3 * R ^ 4 * (4 * lH + 2) = A1
  have hlH0 : 0 ≤ lH := by
    by_contra hc; push Not at hc
    nlinarith
  have hA10 : 0 ≤ A1 := by rw [← hA1]; positivity
  have hlight : ‖lightW g E m ![a, b] ![true, false] u M‖ ≤
      (ω * (A1 + 1) + 2 * ω * R ^ 2 * (C' + Λ) * mx * Cc * ζt) * ζ ^ 2 * w a b / (1 - u) := by
    have hζt0 : 0 ≤ ζt := hζ.le.trans hζt
    have hX0 : 0 ≤ 2 * ω * R ^ 2 * (C' + Λ) * mx * Cc :=
      mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hCΛ) hmx0) hCc
    have hfarb : 0 ≤ 2 * ω * R ^ 2 * (C' + Λ) * mx * Cc * ζt * ζ ^ 2 * w a b * (1 - u)⁻¹ :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hX0 hζt0) (sq_nonneg ζ)) hwab) hiu.le
    have hnearb : 0 ≤ ω * (A1 + 1) * ζ ^ 2 * w a b * (1 - u)⁻¹ :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hω0.le (by linarith)) (sq_nonneg ζ)) hwab)
        hiu.le
    have hsplit : (ω * (A1 + 1) + 2 * ω * R ^ 2 * (C' + Λ) * mx * Cc * ζt) * ζ ^ 2 * w a b / (1 - u)
        = ω * (A1 + 1) * ζ ^ 2 * w a b * (1 - u)⁻¹ +
          2 * ω * R ^ 2 * (C' + Λ) * mx * Cc * ζt * ζ ^ 2 * w a b * (1 - u)⁻¹ := by
      rw [div_eq_mul_inv]; ring
    rw [hsplit]
    rcases lt_or_ge (2 * h) (cycDist a b : ℝ) with hd | hd
    · have h1 := hlf hd
      rw [hmax] at h1
      have h2 : 2 * gammaG g * W * (ω * R ^ 2 * ζ) * (C' + Λ) * ζ ^ 2 * (ζ * mx) * Cc * ℓ * w a b =
          2 * ω * R ^ 2 * (C' + Λ) * mx * Cc * ζ * ζ ^ 2 * w a b * (1 - u)⁻¹ := by
        rw [show 2 * gammaG g * W * (ω * R ^ 2 * ζ) * (C' + Λ) * ζ ^ 2 * (ζ * mx) * Cc * ℓ * w a b =
          (gammaG g * W * ℓ) * ((2 * ω * R ^ 2 * (C' + Λ) * mx * Cc * w a b) * ζ ^ (3 + 1)) by ring,
          step2_scale_mul hζ heu hγWℓ]
        ring
      have h3 : 2 * ω * R ^ 2 * (C' + Λ) * mx * Cc * ζ * ζ ^ 2 * w a b * (1 - u)⁻¹ ≤
          2 * ω * R ^ 2 * (C' + Λ) * mx * Cc * ζt * ζ ^ 2 * w a b * (1 - u)⁻¹ := by
        have h0 := hX0
        have := mul_le_mul_of_nonneg_left hζt h0
        have h5 : 0 ≤ ζ ^ 2 * w a b * (1 - u)⁻¹ := mul_nonneg (mul_nonneg (sq_nonneg ζ) hwab) hiu.le
        have := mul_le_mul_of_nonneg_right this h5
        calc _ = 2 * ω * R ^ 2 * (C' + Λ) * mx * Cc * ζ * (ζ ^ 2 * w a b * (1 - u)⁻¹) := by ring
          _ ≤ 2 * ω * R ^ 2 * (C' + Λ) * mx * Cc * ζt * (ζ ^ 2 * w a b * (1 - u)⁻¹) := this
          _ = _ := by ring
      calc ‖lightW g E m ![a, b] ![true, false] u M‖ ≤ _ := h1
        _ = _ := h2
        _ ≤ 2 * ω * R ^ 2 * (C' + Λ) * mx * Cc * ζt * ζ ^ 2 * w a b * (1 - u)⁻¹ := h3
        _ ≤ _ := le_add_of_nonneg_left hnearb
    · have hwl := hshort a b hd
      have hωw : 1 ≤ ω * w a b := by
        have := mul_le_mul_of_nonneg_left hwl hω0.le
        rwa [mul_inv_cancel₀ hω0.ne'] at this
      have hmain : 2 * Real.sqrt 2 * gammaG g * W * (ω * R ^ 2 * ζ) * (ω * R * ζ) *
          ((4 * (ℓ * lH) + 2) * (ω * R * ζ)) ≤ A1 * ζ ^ 2 * (1 - u)⁻¹ := by
        have e : 2 * Real.sqrt 2 * gammaG g * W * (ω * R ^ 2 * ζ) * (ω * R * ζ) *
            ((4 * (ℓ * lH) + 2) * (ω * R * ζ)) =
            (gammaG g * W * ℓ) * (2 * Real.sqrt 2 * ω ^ 3 * R ^ 4 * ζ ^ 3 * (4 * lH + 2 / ℓ)) := by
          field_simp
        rw [e, hγWℓ, ← hA1]
        have h2l : 2 / ℓ ≤ 2 := by rw [div_le_iff₀ hℓ0]; linarith
        have : 2 * Real.sqrt 2 * ω ^ 3 * R ^ 4 * ζ ^ 3 * (4 * lH + 2 / ℓ) ≤
            2 * Real.sqrt 2 * ω ^ 3 * R ^ 4 * ζ ^ 3 * (4 * lH + 2) := by gcongr
        calc (ζ * (1 - u))⁻¹ * (2 * Real.sqrt 2 * ω ^ 3 * R ^ 4 * ζ ^ 3 * (4 * lH + 2 / ℓ))
            ≤ (ζ * (1 - u))⁻¹ * (2 * Real.sqrt 2 * ω ^ 3 * R ^ 4 * ζ ^ 3 * (4 * lH + 2)) :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = (ζ * (1 - u))⁻¹ *
              ((2 * Real.sqrt 2 * ω ^ 3 * R ^ 4 * (4 * lH + 2)) * ζ ^ (2 + 1)) := by
              ring
          _ = _ := step2_scale_mul hζ heu rfl 2
      have h1 : ‖lightW g E m ![a, b] ![true, false] u M‖ ≤ (A1 + 1) * ζ ^ 2 * (1 - u)⁻¹ := by
        refine hln.trans ?_
        rw [mul_add]
        have : (A1 + 1) * ζ ^ 2 * (1 - u)⁻¹ = A1 * ζ ^ 2 * (1 - u)⁻¹ + ζ ^ 2 / (1 - u) := by
          rw [div_eq_mul_inv]; ring
        rw [this]
        exact add_le_add hmain hrem1
      have h4 : (A1 + 1) * ζ ^ 2 * (1 - u)⁻¹ ≤ ω * (A1 + 1) * ζ ^ 2 * w a b * (1 - u)⁻¹ := by
        have h0 : 0 ≤ (A1 + 1) * ζ ^ 2 * (1 - u)⁻¹ :=
          mul_nonneg (mul_nonneg (by linarith) (sq_nonneg ζ)) hiu.le
        have : ω * (A1 + 1) * ζ ^ 2 * w a b * (1 - u)⁻¹ =
            (ω * w a b) * ((A1 + 1) * ζ ^ 2 * (1 - u)⁻¹) := by ring
        rw [this]
        exact le_mul_of_one_le_left h0 hωw
      exact (h1.trans h4).trans (le_add_of_nonneg_right hfarb)
  refine ⟨?_, ?_⟩
  · have : step2Src ω R Λ C' Cc lH ζt * ζ ^ 2 * w a b / (1 - u) =
        (ω * (A1 + 1) + 2 * ω * R ^ 2 * (C' + Λ) * mx * Cc * ζt) * ζ ^ 2 * w a b / (1 - u) +
        Λ ^ 2 * Cc * ζt * ζ ^ 2 * w a b / (1 - u) := by
      unfold step2Src; rw [hmx, hA1]; ring
    rw [this]
    exact add_le_add hlight hquad
  · generalize hB1 : 4 * ω ^ 5 * R ^ 5 * (4 * lH + 4) + 4 * ω ^ 3 * R ^ 3 = B1
    have hB10 : 0 ≤ B1 := by rw [← hB1]; positivity
    have hζt0 : 0 ≤ ζt := hζ.le.trans hζt
    have hY0 : 0 ≤ 4 * (C' + Λ) * mx ^ 4 * Cc :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCΛ) (pow_nonneg hmx0 4)) hCc
    have hfarb : 0 ≤ 4 * (C' + Λ) * mx ^ 4 * Cc * ζt * ζ ^ 4 * w a b ^ 2 * (1 - u)⁻¹ :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hY0 hζt0) (pow_nonneg hζ.le 4))
        (sq_nonneg (w a b))) hiu.le
    have hnearb : 0 ≤ ω ^ 2 * B1 * ζ ^ 4 * w a b ^ 2 * (1 - u)⁻¹ :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg ω) hB10) (pow_nonneg hζ.le 4))
        (sq_nonneg (w a b))) hiu.le
    have hsplit : step2Brk ω R Λ C' Cc lH ζt * ζ ^ 4 * w a b ^ 2 / (1 - u) =
        ω ^ 2 * B1 * ζ ^ 4 * w a b ^ 2 * (1 - u)⁻¹ +
          4 * (C' + Λ) * mx ^ 4 * Cc * ζt * ζ ^ 4 * w a b ^ 2 * (1 - u)⁻¹ := by
      unfold step2Brk; rw [hmx, hB1, div_eq_mul_inv]; ring
    rw [hsplit]
    rcases lt_or_ge (2 * h) (cycDist a b : ℝ) with hd | hd
    · have h1 := hbf hd
      rw [hmax] at h1
      have h2 : 4 * gammaG g * W * ((C' + Λ) * ζ ^ 2 * w a b) * (ζ * mx) ^ 4 * Cc * ℓ * w a b =
          4 * (C' + Λ) * mx ^ 4 * Cc * ζ * ζ ^ 4 * w a b ^ 2 * (1 - u)⁻¹ := by
        rw [show 4 * gammaG g * W * ((C' + Λ) * ζ ^ 2 * w a b) * (ζ * mx) ^ 4 * Cc * ℓ * w a b =
          (gammaG g * W * ℓ) * ((4 * (C' + Λ) * mx ^ 4 * Cc * w a b ^ 2) * ζ ^ (5 + 1)) by ring,
          step2_scale_mul hζ heu hγWℓ]
        ring
      have h3 : 4 * (C' + Λ) * mx ^ 4 * Cc * ζ * ζ ^ 4 * w a b ^ 2 * (1 - u)⁻¹ ≤
          4 * (C' + Λ) * mx ^ 4 * Cc * ζt * ζ ^ 4 * w a b ^ 2 * (1 - u)⁻¹ := by
        have h0 := hY0
        have h5 : 0 ≤ ζ ^ 4 * w a b ^ 2 * (1 - u)⁻¹ :=
          mul_nonneg (mul_nonneg (pow_nonneg hζ.le 4) (sq_nonneg _)) hiu.le
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hζt h0) h5
        calc _ = 4 * (C' + Λ) * mx ^ 4 * Cc * ζ * (ζ ^ 4 * w a b ^ 2 * (1 - u)⁻¹) := by ring
          _ ≤ 4 * (C' + Λ) * mx ^ 4 * Cc * ζt * (ζ ^ 4 * w a b ^ 2 * (1 - u)⁻¹) := this
          _ = _ := by ring
      calc _ ≤ _ := h1
        _ = _ := h2
        _ ≤ _ := h3
        _ ≤ _ := le_add_of_nonneg_left hnearb
    · have hwl := hshort a b hd
      have hωw : 1 ≤ ω * w a b := by
        have := mul_le_mul_of_nonneg_left hwl hω0.le
        rwa [mul_inv_cancel₀ hω0.ne'] at this
      have hωw2 : 1 ≤ ω ^ 2 * w a b ^ 2 := by nlinarith
      have h1 : (blockGamma W L (gammaG g) (resLoop g E m ![a, b] ![true, false] u)
          (resLoop g E m ![a, b] ![true, false] u) M).re ≤ B1 * ζ ^ 4 * (1 - u)⁻¹ := by
        refine hbn.trans ?_
        have e : 4 * gammaG g * W * (ω * R * ζ) * ((4 * (ℓ * lH) + 4) * (ω * R * ζ) ^ 4 +
            L * ((ω * R * ζ) ^ 2 * ((C' + Λ) * ζ ^ 2 * εw))) =
            (gammaG g * W * ℓ) * (4 * ω ^ 5 * R ^ 5 * ζ ^ 5 * (4 * lH + 4 / ℓ) +
              4 * ω ^ 3 * R ^ 3 * ζ ^ 5 * ((C' + Λ) * εw * (L / ℓ))) := by
          field_simp
        rw [e, hγWℓ, ← hB1]
        have h4l : 4 / ℓ ≤ 4 := by rw [div_le_iff₀ hℓ0]; linarith
        have hA : 4 * ω ^ 5 * R ^ 5 * ζ ^ 5 * (4 * lH + 4 / ℓ) ≤
            4 * ω ^ 5 * R ^ 5 * ζ ^ 5 * (4 * lH + 4) := by gcongr
        have hB : 4 * ω ^ 3 * R ^ 3 * ζ ^ 5 * ((C' + Λ) * εw * (L / ℓ)) ≤
            4 * ω ^ 3 * R ^ 3 * ζ ^ 5 * 1 := mul_le_mul_of_nonneg_left hrem2 (by positivity)
        calc (ζ * (1 - u))⁻¹ * (4 * ω ^ 5 * R ^ 5 * ζ ^ 5 * (4 * lH + 4 / ℓ) +
              4 * ω ^ 3 * R ^ 3 * ζ ^ 5 * ((C' + Λ) * εw * (L / ℓ)))
            ≤ (ζ * (1 - u))⁻¹ * (4 * ω ^ 5 * R ^ 5 * ζ ^ 5 * (4 * lH + 4) +
              4 * ω ^ 3 * R ^ 3 * ζ ^ 5 * 1) :=
              mul_le_mul_of_nonneg_left (add_le_add hA hB) (by positivity)
          _ = (ζ * (1 - u))⁻¹ * ((4 * ω ^ 5 * R ^ 5 * (4 * lH + 4) + 4 * ω ^ 3 * R ^ 3) *
              ζ ^ (4 + 1)) := by ring
          _ = _ := step2_scale_mul hζ heu rfl 4
      have h4 : B1 * ζ ^ 4 * (1 - u)⁻¹ ≤ ω ^ 2 * B1 * ζ ^ 4 * w a b ^ 2 * (1 - u)⁻¹ := by
        have h0 : 0 ≤ B1 * ζ ^ 4 * (1 - u)⁻¹ :=
          mul_nonneg (mul_nonneg hB10 (pow_nonneg hζ.le 4)) hiu.le
        have : ω ^ 2 * B1 * ζ ^ 4 * w a b ^ 2 * (1 - u)⁻¹ =
            (ω ^ 2 * w a b ^ 2) * (B1 * ζ ^ 4 * (1 - u)⁻¹) := by ring
        rw [this]
        exact le_mul_of_one_le_left h0 hωw2
      exact (h1.trans h4).trans (le_add_of_nonneg_right hfarb)

end Step2Good

/-! ### Moments split along a good event -/

section Step2Moments

/-- A moment split along a good event: if `0 ≤ f ≤ A₀` off a measurable set `T` with
`ℙ(T) ≤ δ` and `E f^{2q} ≤ M`, then `‖f‖_q ≤ A₀ + (M^{1/2} δ^{1/2})^{1/q}`. -/
private theorem step2_moment_split {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] (f : Ω' → ℝ) (hfm : AEStronglyMeasurable f P) (hf0 : ∀ x, 0 ≤ f x)
    (q : ℕ) (hq : 1 ≤ q) {T : Set Ω'} (hT : MeasurableSet T) {δ A₀ Mf : ℝ} (hδ : 0 ≤ δ)
    (hTδ : P T ≤ ENNReal.ofReal δ) (hA₀ : 0 ≤ A₀) (hgood : ∀ x, x ∉ T → f x ≤ A₀)
    (hint : Integrable (fun x => f x ^ (2 * q)) P) (hM : ∫ x, f x ^ (2 * q) ∂P ≤ Mf) :
    (∫ x, f x ^ q ∂P) ^ (1 / (q : ℝ)) ≤ A₀ + (Real.sqrt Mf * Real.sqrt δ) ^ (1 / (q : ℝ)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hfq_m : AEStronglyMeasurable (fun x => f x ^ q) P := hfm.pow q
  have hfq0 : ∀ x, 0 ≤ f x ^ q := fun x => pow_nonneg (hf0 x) q
  have hsq : ∀ x, (f x ^ q) ^ 2 = f x ^ (2 * q) := fun x => by rw [← pow_mul, mul_comm]
  have hfq_int : Integrable (fun x => f x ^ q) P := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hint) hfq_m ?_
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_of_nonneg (hfq0 x), Pi.add_apply, ← hsq x]
    nlinarith [hfq0 x, sq_nonneg (f x ^ q - 1)]
  have hmem : MemLp (fun x => f x ^ q) 2 P := by
    rw [memLp_two_iff_integrable_sq hfq_m]
    simpa only [hsq] using hint
  have hM0 : 0 ≤ Mf := (integral_nonneg fun x => pow_nonneg (hf0 x) _).trans hM
  have hcs := lemmaNOffset_cs P (fun x => f x ^ q) hmem hT (K := Real.sqrt Mf) (δ := δ)
    (Real.sqrt_nonneg _) (by rw [Real.sq_sqrt hM0]; simpa only [hsq] using hM)
    (by rw [measureReal_def]; exact ENNReal.toReal_le_of_le_ofReal hδ hTδ)
  have hind_int : Integrable (T.indicator fun x => |f x ^ q|) P :=
    (hfq_int.abs).indicator hT
  have hpt : ∀ x, f x ^ q ≤ A₀ ^ q + T.indicator (fun x => |f x ^ q|) x := by
    intro x
    by_cases hx : x ∈ T
    · rw [Set.indicator_of_mem hx, abs_of_nonneg (hfq0 x)]
      have : 0 ≤ A₀ ^ q := pow_nonneg hA₀ q
      linarith
    · rw [Set.indicator_of_notMem hx, add_zero]
      exact pow_le_pow_left₀ (hf0 x) (hgood x hx) q
  have hbound : ∫ x, f x ^ q ∂P ≤ A₀ ^ q + Real.sqrt Mf * Real.sqrt δ := by
    calc ∫ x, f x ^ q ∂P ≤ ∫ x, (A₀ ^ q + T.indicator (fun x => |f x ^ q|) x) ∂P :=
          integral_mono hfq_int ((integrable_const _).add hind_int) hpt
      _ = A₀ ^ q + ∫ x, T.indicator (fun x => |f x ^ q|) x ∂P := by
          rw [integral_add (integrable_const _) hind_int, integral_const]; simp
      _ ≤ _ := by linarith
  have hI0 : 0 ≤ ∫ x, f x ^ q ∂P := integral_nonneg hfq0
  have hq1 : 1 / (q : ℝ) ≤ 1 := by rw [div_le_one hq0]; exact_mod_cast hq
  calc (∫ x, f x ^ q ∂P) ^ (1 / (q : ℝ)) ≤ (A₀ ^ q + Real.sqrt Mf * Real.sqrt δ) ^ (1 / (q : ℝ)) :=
        Real.rpow_le_rpow hI0 hbound (by positivity)
    _ ≤ (A₀ ^ q) ^ (1 / (q : ℝ)) + (Real.sqrt Mf * Real.sqrt δ) ^ (1 / (q : ℝ)) :=
        Real.rpow_add_le_add_rpow (pow_nonneg hA₀ q) (by positivity) (by positivity) hq1
    _ = A₀ + (Real.sqrt Mf * Real.sqrt δ) ^ (1 / (q : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hA₀, mul_one_div_cancel hq0.ne', Real.rpow_one]

/-- Markov's inequality in moment form: `ℙ(T < f) ≤ E f^q / T^q` for `f ≥ 0`, `T > 0`. -/
private theorem step2_markov {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] (f : Ω' → ℝ) (hf0 : ∀ x, 0 ≤ f x) (q : ℕ)
    (hint : Integrable (fun x => f x ^ q) P) {T : ℝ} (hT : 0 < T) :
    P {x | T < f x} ≤ ENNReal.ofReal ((∫ x, f x ^ q ∂P) / T ^ q) := by
  have hTq : 0 < T ^ q := pow_pos hT q
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := P)
    (Eventually.of_forall fun x => pow_nonneg (hf0 x) q) hint (T ^ q)
  have hsub : {x | T < f x} ⊆ {x | T ^ q ≤ f x ^ q} := fun x hx =>
    pow_le_pow_left₀ hT.le (le_of_lt hx) q
  calc P {x | T < f x} ≤ P {x | T ^ q ≤ f x ^ q} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {x | T ^ q ≤ f x ^ q}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal ((∫ x, f x ^ q ∂P) / T ^ q) := by
        apply ENNReal.ofReal_le_ofReal
        rw [le_div_iff₀ hTq]
        linarith

end Step2Moments

/-! ### The moment comparison along the good events -/

section Step2Core

/-- `∫_s^v (K(1 - r)^n + ρ) dr ≤ K(1 - s)^{n+1}/(n+1) + ρ` for `0 ≤ s ≤ v ≤ 1`, `K, ρ ≥ 0`. -/
private theorem step2_integral_poly {s v K ρ : ℝ} (hs : 0 ≤ s) (hsv : s ≤ v) (hv : v ≤ 1)
    (hK : 0 ≤ K) (hρ : 0 ≤ ρ) (n : ℕ) :
    ∫ r in s..v, (K * (1 - r) ^ n + ρ) ≤ K * (1 - s) ^ (n + 1) / (n + 1) + ρ := by
  have h1 : ∫ r in s..v, (1 - r) ^ n = ((1 - s) ^ (n + 1) - (1 - v) ^ (n + 1)) / (n + 1) := by
    rw [intervalIntegral.integral_comp_sub_left (fun x => x ^ n) 1, integral_pow]
  have hi1 : IntervalIntegrable (fun r : ℝ => K * (1 - r) ^ n) MeasureTheory.volume s v :=
    Continuous.intervalIntegrable (by fun_prop) s v
  have hi2 : IntervalIntegrable (fun _ : ℝ => ρ) MeasureTheory.volume s v :=
    intervalIntegrable_const
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul, h1,
    intervalIntegral.integral_const, smul_eq_mul]
  have hv0 : 0 ≤ (1 - v) ^ (n + 1) := pow_nonneg (by linarith) _
  have hn : (0 : ℝ) < n + 1 := by positivity
  have h2 : K * (((1 - s) ^ (n + 1) - (1 - v) ^ (n + 1)) / (n + 1)) ≤
      K * (1 - s) ^ (n + 1) / (n + 1) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) hn.le) hK
  have h3 : (v - s) * ρ ≤ ρ := by nlinarith
  linarith

/-- The moment comparison along the good events: for a field `Y` of the class, the bounds
`|𝒢Y_r| ≤ A₁(1 - r)`, `|Γ(Y_r)| ≤ B₁(1 - r)³` off sets of probability `≤ δ`, `|Y_s| ≤ I₀` off a set
of probability `≤ δ`, and the crude moments `M_A, M_B, M_I` give
`‖Y_v‖_{2p} ≤ I₀ + ρ_I + ((2p - 1)(B₁(1-s)⁴/4 + ρ_B))^{1/2} + A₁(1-s)²/2 + ρ_A`. -/
private theorem step2_lemmaM_core {ι : Type*} [Fintype ι] (σ2 : ℝ) (hσ2 : 0 ≤ σ2)
    (Y : ℝ → (ι → ℝ) → ℂ) {a' b' s v : ℝ} (ha : a' < 0) (hs : 0 ≤ s) (hsv : s ≤ v)
    (hvb : v < b') (hv1 : v ≤ 1) (hY : HeatClass Y a' b') (p : ℕ) (hp : 1 ≤ p)
    (T : ℝ → Set (ι → ℝ)) (hTm : ∀ r, MeasurableSet (T r)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hTδ : ∀ r ∈ Set.Ioo s v, stdGauss ι (T r) ≤ ENNReal.ofReal δ) (T0 : Set (ι → ℝ))
    (hT0m : MeasurableSet T0) (hT0δ : stdGauss ι T0 ≤ ENNReal.ofReal δ)
    {A₁ B₁ I₀ MA MB MI : ℝ} (hA₁ : 0 ≤ A₁) (hB₁ : 0 ≤ B₁) (hI₀ : 0 ≤ I₀)
    (hGgood : ∀ r ∈ Set.Ioo s v, ∀ x, x ∉ T r →
      ‖coordGen σ2 Y r (Real.sqrt (r * σ2) • x)‖ ≤ A₁ * (1 - r))
    (hΓgood : ∀ r ∈ Set.Ioo s v, ∀ x, x ∉ T r →
      ‖coordGamma σ2 (Y r) (Y r) (Real.sqrt (r * σ2) • x)‖ ≤ B₁ * (1 - r) ^ 3)
    (hIgood : ∀ x, x ∉ T0 → ‖Y s (Real.sqrt (s * σ2) • x)‖ ≤ I₀)
    (hMA : ∀ r ∈ Set.Ioo s v,
      ∫ x, ‖coordGen σ2 Y r (Real.sqrt (r * σ2) • x)‖ ^ (2 * (2 * p)) ∂(stdGauss ι) ≤ MA)
    (hMB : ∀ r ∈ Set.Ioo s v,
      ∫ x, ‖coordGamma σ2 (Y r) (Y r) (Real.sqrt (r * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι) ≤ MB)
    (hMI : ∫ x, ‖Y s (Real.sqrt (s * σ2) • x)‖ ^ (2 * (2 * p)) ∂(stdGauss ι) ≤ MI) :
    (∫ x, ‖Y v (Real.sqrt (v * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι)) ^ (1 / (2 * (p : ℝ))) ≤
      I₀ + (Real.sqrt MI * Real.sqrt δ) ^ (1 / (2 * (p : ℝ))) +
        Real.sqrt ((2 * p - 1) *
          (B₁ * (1 - s) ^ 4 / 4 + (Real.sqrt MB * Real.sqrt δ) ^ (1 / (p : ℝ)))) +
        (A₁ * (1 - s) ^ 2 / 2 + (Real.sqrt MA * Real.sqrt δ) ^ (1 / (2 * (p : ℝ)))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hcast : ((2 * p : ℕ) : ℝ) = 2 * (p : ℝ) := by push_cast; ring
  set ρA := (Real.sqrt MA * Real.sqrt δ) ^ (1 / (2 * (p : ℝ))) with hρA
  set ρB := (Real.sqrt MB * Real.sqrt δ) ^ (1 / (p : ℝ)) with hρB
  have hρA0 : 0 ≤ ρA := by positivity
  have hρB0 : 0 ≤ ρB := by positivity
  set A : ℝ → ℝ := fun r => A₁ * (1 - r) ^ 1 + ρA with hA
  set B : ℝ → ℝ := fun r => B₁ * (1 - r) ^ 3 + ρB with hB
  have hAc : ContinuousOn A (Set.Icc s v) :=
    (continuous_const.mul ((continuous_const.sub continuous_id).pow 1)).add continuous_const
      |>.continuousOn
  have hBc : ContinuousOn B (Set.Icc s v) :=
    (continuous_const.mul ((continuous_const.sub continuous_id).pow 3)).add continuous_const
      |>.continuousOn
  have hA0 : ∀ r ∈ Set.Icc s v, 0 ≤ A r := fun r hr => by
    have : 0 ≤ 1 - r := by linarith [hr.2]
    simp only [hA]; positivity
  have hB0 : ∀ r ∈ Set.Icc s v, 0 ≤ B r := fun r hr => by
    have : 0 ≤ 1 - r := by linarith [hr.2]
    simp only [hB]; positivity
  -- the jets at a time of `(s, v)`
  have hjet : ∀ r ∈ Set.Ioo s v, _ := fun r hr =>
    step2_class_jet hY (⟨ha.trans_le (hs.trans hr.1.le), hr.2.trans hvb⟩ : r ∈ Set.Ioo a' b') σ2
  have hAg : ∀ r ∈ Set.Ioo s v, (∫ x, ‖coordGen σ2 Y r (Real.sqrt (r * σ2) • x)‖ ^ (2 * p)
      ∂(stdGauss ι)) ^ (1 / (2 * (p : ℝ))) ≤ A r := by
    intro r hr
    obtain ⟨-, -, -, ⟨hGc, CG, hCG⟩, -⟩ := hjet r hr
    have hfc : Continuous (fun x : ι → ℝ => ‖coordGen σ2 Y r (Real.sqrt (r * σ2) • x)‖) :=
      continuous_norm.comp (hGc.comp (continuous_const_smul _))
    have hint : Integrable (fun x => ‖coordGen σ2 Y r (Real.sqrt (r * σ2) • x)‖ ^ (2 * (2 * p)))
        (stdGauss ι) :=
      Integrable.of_bound ((hfc.pow _).aestronglyMeasurable) (max CG 0 ^ (2 * (2 * p)))
        (Eventually.of_forall fun x => by
          rw [Real.norm_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) ((hCG _).trans (le_max_left _ _)) _)
    have h1r : 0 ≤ 1 - r := by linarith [hr.2]
    have h := step2_moment_split (stdGauss ι) _ hfc.aestronglyMeasurable (fun x => norm_nonneg _)
      (2 * p) (by omega) (hTm r) hδ (hTδ r hr) (mul_nonneg hA₁ h1r)
      (fun x hx => hGgood r hr x hx) hint (hMA r hr)
    rw [hcast] at h
    simp only [hA, pow_one]
    exact h
  have hBg : ∀ r ∈ Set.Ioo s v, (∫ x, ‖coordGamma σ2 (Y r) (Y r) (Real.sqrt (r * σ2) • x)‖ ^ p
      ∂(stdGauss ι)) ^ (1 / (p : ℝ)) ≤ B r := by
    intro r hr
    obtain ⟨-, -, -, -, ⟨hΓc, CΓ, hCΓ⟩⟩ := hjet r hr
    have hfc : Continuous (fun x : ι → ℝ => ‖coordGamma σ2 (Y r) (Y r) (Real.sqrt (r * σ2) • x)‖) :=
      continuous_norm.comp (hΓc.comp (continuous_const_smul _))
    have hint : Integrable (fun x => ‖coordGamma σ2 (Y r) (Y r) (Real.sqrt (r * σ2) • x)‖ ^ (2 * p))
        (stdGauss ι) :=
      Integrable.of_bound ((hfc.pow _).aestronglyMeasurable) (max CΓ 0 ^ (2 * p))
        (Eventually.of_forall fun x => by
          rw [Real.norm_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) ((hCΓ _).trans (le_max_left _ _)) _)
    have h1r : 0 ≤ 1 - r := by linarith [hr.2]
    have h := step2_moment_split (stdGauss ι) _ hfc.aestronglyMeasurable (fun x => norm_nonneg _)
      p hp (hTm r) hδ (hTδ r hr) (mul_nonneg hB₁ (pow_nonneg h1r 3))
      (fun x hx => hΓgood r hr x hx) hint (hMB r hr)
    simp only [hB]
    exact h
  -- the initial value
  have hIs : (∫ x, ‖Y s (Real.sqrt (s * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι)) ^ (1 / (2 * (p : ℝ))) ≤
      I₀ + (Real.sqrt MI * Real.sqrt δ) ^ (1 / (2 * (p : ℝ))) := by
    rcases eq_or_lt_of_le hsv with hsv' | hsv'
    · -- `s = v`: use the class at `v`
      have hsI : s ∈ Set.Ioo a' b' := ⟨ha.trans_le hs, hsv' ▸ hvb⟩
      obtain ⟨-, hc2, ⟨CY, hCY⟩, -, -⟩ := step2_class_jet hY hsI σ2
      have hfc : Continuous (fun x : ι → ℝ => ‖Y s (Real.sqrt (s * σ2) • x)‖) :=
        continuous_norm.comp (hc2.continuous.comp (continuous_const_smul _))
      have hint : Integrable (fun x => ‖Y s (Real.sqrt (s * σ2) • x)‖ ^ (2 * (2 * p)))
          (stdGauss ι) :=
        Integrable.of_bound ((hfc.pow _).aestronglyMeasurable) (max CY 0 ^ (2 * (2 * p)))
          (Eventually.of_forall fun x => by
            rw [Real.norm_of_nonneg (by positivity)]
            exact pow_le_pow_left₀ (norm_nonneg _) ((hCY _).trans (le_max_left _ _)) _)
      have h := step2_moment_split (stdGauss ι) _ hfc.aestronglyMeasurable
        (fun x => norm_nonneg _) (2 * p) (by omega) hT0m hδ hT0δ hI₀ hIgood hint hMI
      rw [hcast] at h
      exact h
    · have hsI : s ∈ Set.Ioo a' b' := ⟨ha.trans_le hs, hsv'.trans hvb⟩
      obtain ⟨-, hc2, ⟨CY, hCY⟩, -, -⟩ := step2_class_jet hY hsI σ2
      have hfc : Continuous (fun x : ι → ℝ => ‖Y s (Real.sqrt (s * σ2) • x)‖) :=
        continuous_norm.comp (hc2.continuous.comp (continuous_const_smul _))
      have hint : Integrable (fun x => ‖Y s (Real.sqrt (s * σ2) • x)‖ ^ (2 * (2 * p)))
          (stdGauss ι) :=
        Integrable.of_bound ((hfc.pow _).aestronglyMeasurable) (max CY 0 ^ (2 * (2 * p)))
          (Eventually.of_forall fun x => by
            rw [Real.norm_of_nonneg (by positivity)]
            exact pow_le_pow_left₀ (norm_nonneg _) ((hCY _).trans (le_max_left _ _)) _)
      have h := step2_moment_split (stdGauss ι) _ hfc.aestronglyMeasurable
        (fun x => norm_nonneg _) (2 * p) (by omega) hT0m hδ hT0δ hI₀ hIgood hint hMI
      rw [hcast] at h
      exact h
  have hM := lemmaM_gaussian σ2 hσ2 Y ha hs hsv hvb hY p hp A B hAc hBc hA0 hB0 hAg hBg
  -- the integrals of the rates
  have hv1' : v ≤ 1 := hv1
  have hiA : ∫ r in s..v, A r ≤ A₁ * (1 - s) ^ 2 / 2 + ρA := by
    have := step2_integral_poly hs hsv hv1 hA₁ hρA0 1
    simp only [hA]
    norm_num at this ⊢
    linarith
  have hiB : ∫ r in s..v, B r ≤ B₁ * (1 - s) ^ 4 / 4 + ρB := by
    have := step2_integral_poly hs hsv hv1 hB₁ hρB0 3
    simp only [hB]
    norm_num at this ⊢
    linarith
  -- the initial moment in squared form
  set I := (∫ x, ‖Y s (Real.sqrt (s * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι)) with hI
  have hI0 : 0 ≤ I := integral_nonneg fun x => by positivity
  have hIsq : I ^ (1 / (p : ℝ)) = (I ^ (1 / (2 * (p : ℝ)))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hI0]
    congr 1; push_cast; field_simp
  have hIb0 : 0 ≤ I ^ (1 / (2 * (p : ℝ))) := by positivity
  have hp1 : (0 : ℝ) ≤ 2 * p - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hB4 : 0 ≤ B₁ * (1 - s) ^ 4 / 4 + ρB := by
    have : 0 ≤ (1 - s) ^ 4 := by positivity
    positivity
  calc (∫ x, ‖Y v (Real.sqrt (v * σ2) • x)‖ ^ (2 * p) ∂(stdGauss ι)) ^ (1 / (2 * (p : ℝ)))
      ≤ Real.sqrt (I ^ (1 / (p : ℝ)) + (2 * p - 1) * ∫ r in s..v, B r) + ∫ r in s..v, A r := hM
    _ ≤ Real.sqrt ((I ^ (1 / (2 * (p : ℝ)))) ^ 2 + (2 * p - 1) * (B₁ * (1 - s) ^ 4 / 4 + ρB)) +
          (A₁ * (1 - s) ^ 2 / 2 + ρA) := by
        rw [hIsq]
        gcongr
    _ ≤ (I ^ (1 / (2 * (p : ℝ))) + Real.sqrt ((2 * p - 1) * (B₁ * (1 - s) ^ 4 / 4 + ρB))) +
          (A₁ * (1 - s) ^ 2 / 2 + ρA) := by
        gcongr
        rw [Real.sqrt_le_left (by positivity)]
        have := Real.sq_sqrt (mul_nonneg hp1 hB4)
        nlinarith [Real.sqrt_nonneg ((2 * p - 1) * (B₁ * (1 - s) ^ 4 / 4 + ρB))]
    _ ≤ _ := by gcongr

end Step2Core

/-! ### The propagated sources at a good point and the crude moments -/

section Step2Prop2

variable {L : ℕ}

/-- At a good point the generator of the propagated pair is at most `A₁(1 - r)`,
`A₁ = Src C ζ_v² w_v/(1 - v)²`, by the propagated weight (A.53) [da:eq:propagated-weight]. -/
private theorem step2_gen_good (g E : ℝ) (m : ℂ) (W : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ L)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {r v : ℝ} (hr0 : 0 ≤ r) (hrv : r ≤ v)
    (hv : v < 1) (a b : Fin L) (y : Ω W L) (w : Fin L → Fin L → ℝ) (hw0 : ∀ x z, 0 ≤ w x z)
    {Src Cpw ζr ζv wv : ℝ} (hSrc : 0 ≤ Src) (hζr : 0 ≤ ζr) (hζrv : ζr ≤ ζv)
    (hsrc : ∀ l : Fin L × Fin L,
      ‖lightW g E m ![l.1, l.2] ![true, false] r
          (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y)‖ + gammaG g * W *
        ‖∑ e : Fin L, (resLoop g E m ![l.1, e] ![true, false] r
              (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y) -
            primLoop g W L E m r ![l.1, e] ![true, false]) *
          (resLoop g E m ![e, l.2] ![true, false] r
              (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y) -
            primLoop g W L E m r ![e, l.2] ![true, false])‖ ≤ Src * ζr ^ 2 * w l.1 l.2 / (1 - r))
    (hprop : ∑ l : Fin L × Fin L,
        step2Coef (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v a b l r * w l.1 l.2 ≤
      Cpw * ((1 - r) / (1 - v)) ^ 2 * wv) :
    ‖coordGen (gammaG g / W) (step2Y g E m W (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))
        v a b) r y‖ ≤ Src * Cpw * ζv ^ 2 * wv / (1 - v) ^ 2 * (1 - r) := by
  set P := pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) with hPdef
  have hL1 : 1 ≤ L := by omega
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  have hP0 : ∀ x z, 0 ≤ P x z := fun x z => by simp only [hPdef, pairP, Matrix.of_apply]; positivity
  have hProw : ∀ x, ∑ z, P x z = 1 := fun x => pairP_row_sum (hopB g) (gammaG g) hγ L hL1 E m hm x
  have h0 := (propPM_nonneg_row P hP0 hProw r v hr0 hrv hv).1
  have hc0 : ∀ l, 0 ≤ step2Coef P v a b l r := fun l => mul_nonneg (h0 _ _) (h0 _ _)
  have heu : 0 < 1 - r := by linarith
  have hev : 0 < 1 - v := by linarith
  rw [step2_gen_Y g E m W hW hL hm hr0 hrv hv a b y]
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  calc _ ≤ ∑ l : Fin L × Fin L, step2Coef P v a b l r * (Src * ζr ^ 2 * w l.1 l.2 / (1 - r)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc0 l)]
        refine mul_le_mul_of_nonneg_left ?_ (hc0 l)
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        exact hsrc l
    _ = Src * ζr ^ 2 / (1 - r) * ∑ l : Fin L × Fin L, step2Coef P v a b l r * w l.1 l.2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ ≤ Src * ζr ^ 2 / (1 - r) * (Cpw * ((1 - r) / (1 - v)) ^ 2 * wv) :=
        mul_le_mul_of_nonneg_left hprop (by positivity)
    _ = Src * ζr ^ 2 * Cpw * wv / (1 - v) ^ 2 * (1 - r) := by
        field_simp
    _ ≤ _ := by
        have hC : 0 ≤ Cpw * wv := by
          have := (le_trans (Finset.sum_nonneg fun l _ => mul_nonneg (hc0 l) (hw0 l.1 l.2)) hprop)
          have h2 : 0 < ((1 - r) / (1 - v)) ^ 2 := by positivity
          nlinarith
        have h1 : ζr ^ 2 ≤ ζv ^ 2 := pow_le_pow_left₀ hζr hζrv 2
        have : Src * ζr ^ 2 * Cpw * wv / (1 - v) ^ 2 * (1 - r) =
            (Src * (Cpw * wv) / (1 - v) ^ 2 * (1 - r)) * ζr ^ 2 := by ring
        rw [this]
        have : Src * Cpw * ζv ^ 2 * wv / (1 - v) ^ 2 * (1 - r) =
            (Src * (Cpw * wv) / (1 - v) ^ 2 * (1 - r)) * ζv ^ 2 := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- At a good point the bracket of the propagated pair is at most `B₁(1 - r)³`,
`B₁ = Brk C² ζ_v⁴ w_v²/(1 - v)⁴`. -/
private theorem step2_gam_good (g E : ℝ) (m : ℂ) (W : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ L)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {r v : ℝ} (hr0 : 0 ≤ r) (hrv : r ≤ v)
    (hv : v < 1) (a b : Fin L) (y : Ω W L) (w : Fin L → Fin L → ℝ) (hw0 : ∀ x z, 0 ≤ w x z)
    {Brk Cpw ζr ζv wv : ℝ} (hBrk : 0 ≤ Brk) (hζr : 0 ≤ ζr) (hζrv : ζr ≤ ζv)
    (hbrk : ∀ l : Fin L × Fin L,
      (blockGamma W L (gammaG g) (resLoop g E m ![l.1, l.2] ![true, false] r)
        (resLoop g E m ![l.1, l.2] ![true, false] r)
        (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y)).re ≤
        Brk * ζr ^ 4 * w l.1 l.2 ^ 2 / (1 - r))
    (hprop : ∑ l : Fin L × Fin L,
        step2Coef (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v a b l r * w l.1 l.2 ≤
      Cpw * ((1 - r) / (1 - v)) ^ 2 * wv) :
    ‖coordGamma (gammaG g / W)
        (step2Y g E m W (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v a b r)
        (step2Y g E m W (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v a b r) y‖ ≤
      Brk * Cpw ^ 2 * ζv ^ 4 * wv ^ 2 / (1 - v) ^ 4 * (1 - r) ^ 3 := by
  set P := pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) with hPdef
  have hL1 : 1 ≤ L := by omega
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  have hP0 : ∀ x z, 0 ≤ P x z := fun x z => by simp only [hPdef, pairP, Matrix.of_apply]; positivity
  have hProw : ∀ x, ∑ z, P x z = 1 := fun x => pairP_row_sum (hopB g) (gammaG g) hγ L hL1 E m hm x
  have h0 := (propPM_nonneg_row P hP0 hProw r v hr0 hrv hv).1
  have hc0 : ∀ l, 0 ≤ step2Coef P v a b l r := fun l => mul_nonneg (h0 _ _) (h0 _ _)
  have heu : 0 < 1 - r := by linarith
  have hev : 0 < 1 - v := by linarith
  refine (step2_gamma_Y g E m W hW hL hm P hP0 hProw hr0 hrv hv a b y).trans ?_
  set κ := Real.sqrt (Brk / (1 - r)) * ζr ^ 2 with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hs : ∀ l : Fin L × Fin L, Real.sqrt (blockGamma W L (gammaG g)
      (resLoop g E m ![l.1, l.2] ![true, false] r) (resLoop g E m ![l.1, l.2] ![true, false] r)
      (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y)).re ≤ κ * w l.1 l.2 := by
    intro l
    calc _ ≤ Real.sqrt (Brk * ζr ^ 4 * w l.1 l.2 ^ 2 / (1 - r)) := Real.sqrt_le_sqrt (hbrk l)
      _ = κ * w l.1 l.2 := by
          rw [hκ, show Brk * ζr ^ 4 * w l.1 l.2 ^ 2 / (1 - r) =
            (Brk / (1 - r)) * (ζr ^ 2 * w l.1 l.2) ^ 2 by ring, Real.sqrt_mul (by positivity),
            Real.sqrt_sq (mul_nonneg (by positivity) (hw0 _ _))]
          ring
  have hsum : ∑ l : Fin L × Fin L, step2Coef P v a b l r * Real.sqrt (blockGamma W L (gammaG g)
      (resLoop g E m ![l.1, l.2] ![true, false] r) (resLoop g E m ![l.1, l.2] ![true, false] r)
      (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y)).re ≤
      κ * (Cpw * ((1 - r) / (1 - v)) ^ 2 * wv) := by
    calc _ ≤ ∑ l : Fin L × Fin L, step2Coef P v a b l r * (κ * w l.1 l.2) :=
          Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hs l) (hc0 l)
      _ = κ * ∑ l : Fin L × Fin L, step2Coef P v a b l r * w l.1 l.2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hprop hκ0
  have hL0 : 0 ≤ ∑ l : Fin L × Fin L, step2Coef P v a b l r * Real.sqrt (blockGamma W L (gammaG g)
      (resLoop g E m ![l.1, l.2] ![true, false] r) (resLoop g E m ![l.1, l.2] ![true, false] r)
      (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y)).re :=
    Finset.sum_nonneg fun l _ => mul_nonneg (hc0 l) (Real.sqrt_nonneg _)
  calc _ ≤ (κ * (Cpw * ((1 - r) / (1 - v)) ^ 2 * wv)) ^ 2 := pow_le_pow_left₀ hL0 hsum 2
    _ = Brk / (1 - r) * ζr ^ 4 * (Cpw * ((1 - r) / (1 - v)) ^ 2 * wv) ^ 2 := by
        rw [hκ, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
    _ = Brk * Cpw ^ 2 * ζr ^ 4 * wv ^ 2 / (1 - v) ^ 4 * (1 - r) ^ 3 := by
        field_simp
    _ ≤ _ := by
        have h1 : ζr ^ 4 ≤ ζv ^ 4 := pow_le_pow_left₀ hζr hζrv 4
        have : Brk * Cpw ^ 2 * ζr ^ 4 * wv ^ 2 / (1 - v) ^ 4 * (1 - r) ^ 3 =
            (Brk * Cpw ^ 2 * wv ^ 2 / (1 - v) ^ 4 * (1 - r) ^ 3) * ζr ^ 4 := by ring
        rw [this]
        have : Brk * Cpw ^ 2 * ζv ^ 4 * wv ^ 2 / (1 - v) ^ 4 * (1 - r) ^ 3 =
            (Brk * Cpw ^ 2 * wv ^ 2 / (1 - v) ^ 4 * (1 - r) ^ 3) * ζv ^ 4 := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- The moment of a nonnegative combination: `E(Σ_l α_l X_l)^k ≤ (Σ_l α_l)^k max_l E X_l^k`. -/
private theorem step2_jensen_moment {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] {S : Type*} [Fintype S] (k : ℕ) (hk : 1 ≤ k) (f : Ω' → ℝ)
    (hf : Integrable (fun x => f x ^ k) P) (hf0 : ∀ x, 0 ≤ f x) (α : S → ℝ) (hα : ∀ l, 0 ≤ α l)
    (X : S → Ω' → ℝ) (hX0 : ∀ l x, 0 ≤ X l x) (hXi : ∀ l, Integrable (fun x => X l x ^ k) P)
    {M : ℝ} (hXM : ∀ l, ∫ x, X l x ^ k ∂P ≤ M) (hfX : ∀ x, f x ≤ ∑ l, α l * X l x) :
    ∫ x, f x ^ k ∂P ≤ (∑ l, α l) ^ k * M := by
  set A := ∑ l, α l with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun l _ => hα l
  rcases eq_or_lt_of_le hA0 with hA0' | hApos
  · have hα0 : ∀ l, α l = 0 := fun l =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => hα l)).mp hA0'.symm l (Finset.mem_univ l)
    have hf00 : ∀ x, f x = 0 := fun x => le_antisymm ((hfX x).trans (by simp [hα0])) (hf0 x)
    rw [← hA0', zero_pow (by omega), zero_mul]
    simp [hf00, zero_pow (show k ≠ 0 by omega)]
  · have hpt : ∀ x, f x ^ k ≤ A ^ (k - 1) * ∑ l, α l * X l x ^ k := by
      intro x
      have h1 : f x ^ k ≤ (∑ l, α l * X l x) ^ k := pow_le_pow_left₀ (hf0 x) (hfX x) k
      have e : ∑ l, α l * X l x = A * ∑ l, (α l / A) * X l x := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by field_simp
      have hj := Real.pow_arith_mean_le_arith_mean_pow Finset.univ (fun l => α l / A)
        (fun l => X l x) (fun l _ => div_nonneg (hα l) hA0)
        (by rw [← Finset.sum_div, ← hA, div_self hApos.ne']) (fun l _ => hX0 l x) k
      calc f x ^ k ≤ (∑ l, α l * X l x) ^ k := h1
        _ = A ^ k * (∑ l, (α l / A) * X l x) ^ k := by rw [e, mul_pow]
        _ ≤ A ^ k * ∑ l, (α l / A) * X l x ^ k := mul_le_mul_of_nonneg_left hj (by positivity)
        _ = A ^ (k - 1) * ∑ l, α l * X l x ^ k := by
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            have : A ^ k = A ^ (k - 1) * A := by rw [← pow_succ]; congr 1; omega
            rw [this]; field_simp
    have hint : Integrable (fun x => A ^ (k - 1) * ∑ l, α l * X l x ^ k) P :=
      (integrable_finsetSum _ fun l _ => (hXi l).const_mul (α l)).const_mul _
    calc ∫ x, f x ^ k ∂P ≤ ∫ x, A ^ (k - 1) * ∑ l, α l * X l x ^ k ∂P :=
          integral_mono hf hint hpt
      _ = A ^ (k - 1) * ∑ l, α l * ∫ x, X l x ^ k ∂P := by
          rw [integral_const_mul, integral_finsetSum _ fun l _ => (hXi l).const_mul (α l)]
          congr 1
          exact Finset.sum_congr rfl fun l _ => integral_const_mul _ _
      _ ≤ A ^ (k - 1) * ∑ l, α l * M := by
          gcongr with l
          · exact hα l
          · exact hXM l
      _ = A ^ k * M := by
          rw [← Finset.sum_mul, ← hA, ← mul_assoc, ← pow_succ]
          congr 2; omega

end Step2Prop2

/-! ### Numeric facts for the remainders and the coefficients -/

section Step2Num

/-- The remainder of the near light row is at most `ζ²/(1 - u)` once
`2√2 ω²R³(L/ℓ)(Q ε)^{1/2} · 2W ≤ 1`, `Q = ωR((C'+Λ) + ωR(ω² + C' + Λ))`, `(2W)⁻¹ ≤ ζ ≤ 1`. -/
private theorem step2_rem1 {g : ℝ} {W L : ℕ} (hW : 1 ≤ W) {ω R Λ C' ζ ℓ u εw : ℝ} (hω : 1 ≤ ω)
    (hR : 1 ≤ R) (hΛ : 0 ≤ Λ) (hC' : 0 ≤ C') (hζ0 : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hζW : (2 * (W : ℝ))⁻¹ ≤ ζ) (hℓ : 0 < ℓ) (hu : u < 1) (hεw : 0 ≤ εw)
    (hΓ : gammaG g * W * ℓ * ζ * (1 - u) = 1)
    (hsmall : 2 * Real.sqrt 2 * ω ^ 2 * R ^ 3 * (L / ℓ) *
      Real.sqrt (ω * R * ((C' + Λ) + ω * R * (ω ^ 2 + C' + Λ)) * εw) * (2 * W) ≤ 1) :
    2 * Real.sqrt 2 * gammaG g * W * (ω * R ^ 2 * ζ) * (ω * R * ζ) *
      (L * Real.sqrt ((ω * R * ζ) * max ((C' + Λ) * ζ ^ 2 /
        max (ω ^ 2) ((C' + Λ) * ζ ^ 2 / (ω * R * ζ) ^ 2)) ((ω * R * ζ) / 2) * 1 ^ 2 *
        (max (ω ^ 2) ((C' + Λ) * ζ ^ 2 / (ω * R * ζ) ^ 2) * εw))) ≤ ζ ^ 2 / (1 - u) := by
  have heu : 0 < 1 - u := by linarith
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  have hs₀ : 0 < ω * R * ζ := by positivity
  set K₀ := max (ω ^ 2) ((C' + Λ) * ζ ^ 2 / (ω * R * ζ) ^ 2) with hK₀
  have hK₀pos : 0 < K₀ := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hCΛ : 0 ≤ C' + Λ := by linarith
  have hK₀le : K₀ ≤ ω ^ 2 + (C' + Λ) := by
    refine max_le (by linarith) ?_
    rw [div_le_iff₀ (pow_pos hs₀ 2)]
    have h1 : 1 ≤ (ω * R) ^ 2 := one_le_pow₀ (by nlinarith)
    have : (C' + Λ) * ζ ^ 2 ≤ (C' + Λ) * ζ ^ 2 * (ω * R) ^ 2 :=
      le_mul_of_one_le_right (by positivity) h1
    nlinarith [sq_nonneg ζ, mul_nonneg (sq_nonneg ω) (sq_nonneg (ω * R * ζ))]
  set Λt := max ((C' + Λ) * ζ ^ 2 / K₀) ((ω * R * ζ) / 2) with hΛt
  have hΛtK : Λt * K₀ ≤ (C' + Λ) * ζ ^ 2 + (ω * R * ζ) / 2 * K₀ := by
    rcases le_total ((C' + Λ) * ζ ^ 2 / K₀) ((ω * R * ζ) / 2) with h | h
    · rw [hΛt, max_eq_right h]; have : 0 ≤ (C' + Λ) * ζ ^ 2 := by positivity
      linarith
    · rw [hΛt, max_eq_left h, div_mul_cancel₀ _ hK₀pos.ne']
      have : 0 ≤ (ω * R * ζ) / 2 * K₀ := by positivity
      linarith
  set Q := ω * R * ((C' + Λ) + ω * R * (ω ^ 2 + C' + Λ)) with hQ
  have hQb : (ω * R * ζ) * Λt * 1 ^ 2 * (K₀ * εw) ≤ Q * εw := by
    have h1 : (ω * R * ζ) * Λt * 1 ^ 2 * (K₀ * εw) = (ω * R * ζ) * (Λt * K₀) * εw := by ring
    rw [h1]
    have h2 : (ω * R * ζ) * (Λt * K₀) ≤ (ω * R * ζ) * ((C' + Λ) * ζ ^ 2 + (ω * R * ζ) / 2 * K₀) :=
      mul_le_mul_of_nonneg_left hΛtK hs₀.le
    have hζ2 : ζ ^ 2 ≤ 1 := by nlinarith
    have h3 : (ω * R * ζ) * ((C' + Λ) * ζ ^ 2 + (ω * R * ζ) / 2 * K₀) ≤ Q := by
      have hωR : 0 ≤ ω * R := by positivity
      have e1 : (ω * R * ζ) * ((C' + Λ) * ζ ^ 2) ≤ ω * R * (C' + Λ) := by
        have : ζ * ζ ^ 2 ≤ 1 := by nlinarith
        nlinarith [mul_nonneg hωR hCΛ]
      have e2 : (ω * R * ζ) * ((ω * R * ζ) / 2 * K₀) ≤ ω * R * (ω * R * (ω ^ 2 + C' + Λ)) := by
        have hK : K₀ ≤ ω ^ 2 + C' + Λ := by linarith
        have : (ω * R * ζ) * ((ω * R * ζ) / 2 * K₀) = (ω * R) * (ω * R) * (ζ ^ 2 / 2) * K₀ := by
          ring
        rw [this]
        have hζ' : ζ ^ 2 / 2 ≤ 1 := by linarith
        calc (ω * R) * (ω * R) * (ζ ^ 2 / 2) * K₀ ≤ (ω * R) * (ω * R) * 1 * (ω ^ 2 + C' + Λ) := by
              gcongr
          _ = _ := by ring
      calc (ω * R * ζ) * ((C' + Λ) * ζ ^ 2 + (ω * R * ζ) / 2 * K₀) =
          (ω * R * ζ) * ((C' + Λ) * ζ ^ 2) + (ω * R * ζ) * ((ω * R * ζ) / 2 * K₀) := by ring
        _ ≤ _ := by rw [hQ]; nlinarith [e1, e2]
    exact mul_le_mul_of_nonneg_right (h2.trans h3) hεw
  have hsq : Real.sqrt ((ω * R * ζ) * Λt * 1 ^ 2 * (K₀ * εw)) ≤ Real.sqrt (Q * εw) :=
    Real.sqrt_le_sqrt hQb
  have hγWℓ : gammaG g * W = (ℓ * ζ * (1 - u))⁻¹ := by
    have h1 : (gammaG g * W) * (ℓ * ζ * (1 - u)) = 1 := by
      calc _ = gammaG g * W * ℓ * ζ * (1 - u) := by ring
        _ = 1 := hΓ
    exact (mul_eq_one_iff_eq_inv₀ (by positivity)).mp h1
  have hkey : 2 * Real.sqrt 2 * ω ^ 2 * R ^ 3 * (L / ℓ) * Real.sqrt (Q * εw) ≤ ζ := by
    have h1 := hsmall
    rw [← le_div_iff₀ (by positivity), one_div] at h1
    linarith
  calc 2 * Real.sqrt 2 * gammaG g * W * (ω * R ^ 2 * ζ) * (ω * R * ζ) *
        (L * Real.sqrt ((ω * R * ζ) * Λt * 1 ^ 2 * (K₀ * εw)))
      ≤ 2 * Real.sqrt 2 * gammaG g * W * (ω * R ^ 2 * ζ) * (ω * R * ζ) *
        (L * Real.sqrt (Q * εw)) := by gcongr
    _ = (2 * Real.sqrt 2 * (ω * R ^ 2 * ζ) * (ω * R * ζ) * (L * Real.sqrt (Q * εw))) *
          (gammaG g * W) := by ring
    _ = (2 * Real.sqrt 2 * (ω * R ^ 2 * ζ) * (ω * R * ζ) * (L * Real.sqrt (Q * εw))) *
          (ℓ * ζ * (1 - u))⁻¹ := by rw [hγWℓ]
    _ = (2 * Real.sqrt 2 * ω ^ 2 * R ^ 3 * (L / ℓ) * Real.sqrt (Q * εw)) * ζ / (1 - u) := by
        field_simp
    _ ≤ ζ * ζ / (1 - u) := by gcongr
    _ = ζ ^ 2 / (1 - u) := by ring

end Step2Num

section Step2Coef

variable {L : ℕ}

private theorem step2_coef_sum (P : Matrix (Fin L) (Fin L) ℝ) (hP : ∀ a b, 0 ≤ P a b)
    (hrow : ∀ a, ∑ b, P a b = 1) {r v : ℝ} (hr : 0 ≤ r) (hrv : r ≤ v) (hv : v < 1) (a b : Fin L) :
    (∀ l, 0 ≤ step2Coef P v a b l r) ∧
      ∑ l : Fin L × Fin L, step2Coef P v a b l r = ((1 - r) / (1 - v)) ^ 2 := by
  obtain ⟨h0, hr1⟩ := propPM_nonneg_row P hP hrow r v hr hrv hv
  refine ⟨fun l => mul_nonneg (h0 _ _) (h0 _ _), ?_⟩
  unfold step2Coef
  rw [Fintype.sum_prod_type, ← Finset.sum_mul_sum, hr1, hr1, sq]

private theorem step2_coef'_sum (P : Matrix (Fin L) (Fin L) ℝ) (hP : ∀ a b, 0 ≤ P a b)
    (hrow : ∀ a, ∑ b, P a b = 1) {r v : ℝ} (hr : 0 ≤ r) (hrv : r ≤ v) (hv : v < 1) (a b : Fin L) :
    ∑ l : Fin L × Fin L, ‖step2Coef' P v a b l r‖ = 2 * (1 - v)⁻¹ * ((1 - r) / (1 - v)) := by
  obtain ⟨h0, hr1⟩ := propPM_nonneg_row P hP hrow r v hr hrv hv
  obtain ⟨k0, kr1⟩ := mixedKer_nonneg_row P hP hrow v (hr.trans hrv) hv
  have e : ∀ l : Fin L × Fin L, ‖step2Coef' P v a b l r‖ =
      mixedKer P v a l.1 * propPM P r v b l.2 + propPM P r v a l.1 * mixedKer P v b l.2 := by
    intro l
    unfold step2Coef'
    rw [norm_neg, Real.norm_of_nonneg (add_nonneg (mul_nonneg (k0 _ _) (h0 _ _))
      (mul_nonneg (h0 _ _) (k0 _ _)))]
  simp only [e]
  rw [Finset.sum_add_distrib, Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_mul_sum,
    ← Finset.sum_mul_sum, kr1, kr1, hr1, hr1]
  ring

end Step2Coef

/-! ### The propagated pair estimate at fixed `W` -/

section Step2AtW

open scoped Matrix.Norms.L2Operator

/-- The good event at a time `r`: the Step 1 envelopes of (C.5) [fo:eq:step1] with loss `ω` and
the mixed pair at `Λ ζ_r² w_r`. -/
private def step2Good (W L : ℕ) (g E r R ω Λ cw θ F₁ : ℝ) (x : Ω W L) : Prop :=
  (∀ l : Fin L × Fin L, ‖blockOf (flowG W ⟨g, E, L, r⟩ x) l.1 l.2‖ ≤
      ω * (W * R * zetaProp g W L r)) ∧
  (∀ l : Fin L × Fin L, blockHS2 (flowG W ⟨g, E, L, r⟩ x) l.1 l.2 ≤
      ω * ((W : ℝ) ^ 2 * R * zetaProp g W L r)) ∧
  (∀ c : Fin L, ‖blockTr (flowG W ⟨g, E, L, r⟩ x - flowM W ⟨g, E, L, r⟩) c c‖ ≤
      ω * (R ^ 2 * zetaProp g W L r)) ∧
  (∀ l : Fin L × Fin L, ‖flowErr W ⟨g, E, L, r⟩ ![l.1, l.2] ![true, false] x‖ ≤
      Λ * zetaProp g W L r ^ 2 * weightFn cw θ F₁ W (ellProp g L r) (cycDist l.1 l.2))

end Step2AtW

section Step2Core2

variable {L : ℕ}

/-- The propagated pair estimate at fixed `W`: the moment comparison for
`Y_r = (U^{+-}_{r,v})^{⊗2} D₂(r)` along the good events, with the source rows
`Src ζ_r² w_r/(1 - r)`, the bracket rows `Brk ζ_r⁴ w_r²/(1 - r)`, the propagated weight (A.53)
[da:eq:propagated-weight] and the input at the start `|D₂(s)| ≤ I₁ ζ_s² w_s`. -/
private theorem step2_pair_core (g E : ℝ) {W : ℕ} (hW : 1 ≤ W) (hL : 3 ≤ L)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E (mRoot g L E)) {s v : ℝ} (hs : 0 ≤ s)
    (hsv : s ≤ v) (hv : v < 1) (a b : Fin L) (p : ℕ) (hp : 1 ≤ p)
    (w : ℝ → Fin L → Fin L → ℝ) (hw0 : ∀ r x y, 0 ≤ w r x y)
    (ζ : ℝ → ℝ) (hζ0 : ∀ r ∈ Set.Icc s v, 0 ≤ ζ r) (hζv : ∀ r ∈ Set.Icc s v, ζ r ≤ ζ v)
    {Src Brk Cpw wv I₁ : ℝ} (hSrc : 0 ≤ Src) (hBrk : 0 ≤ Brk) (hI₁ : 0 ≤ I₁)
    (hprop : ∀ r ∈ Set.Icc s v, ∑ l : Fin L × Fin L,
        step2Coef (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E (mRoot g L E))) v a b l r *
          w r l.1 l.2 ≤ Cpw * ((1 - r) / (1 - v)) ^ 2 * wv)
    (T : ℝ → Set (Ω W L)) (hTm : ∀ r, MeasurableSet (T r)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hTδ : ∀ r ∈ Set.Ioo s v, μ W L (T r) ≤ ENNReal.ofReal δ) (T0 : Set (Ω W L))
    (hT0m : MeasurableSet T0) (hT0δ : μ W L T0 ≤ ENNReal.ofReal δ)
    (hsrc : ∀ r ∈ Set.Ioo s v, ∀ x, x ∉ T r → ∀ l : Fin L × Fin L,
      ‖lightW g E (mRoot g L E) ![l.1, l.2] ![true, false] r
          (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
            (Real.sqrt (r * (gammaG g / W)) • x))‖ + gammaG g * W *
        ‖∑ e : Fin L, (resLoop g E (mRoot g L E) ![l.1, e] ![true, false] r
              (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
                (Real.sqrt (r * (gammaG g / W)) • x)) -
            primLoop g W L E (mRoot g L E) r ![l.1, e] ![true, false]) *
          (resLoop g E (mRoot g L E) ![e, l.2] ![true, false] r
              (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
                (Real.sqrt (r * (gammaG g / W)) • x)) -
            primLoop g W L E (mRoot g L E) r ![e, l.2] ![true, false])‖ ≤
        Src * ζ r ^ 2 * w r l.1 l.2 / (1 - r))
    (hbrk : ∀ r ∈ Set.Ioo s v, ∀ x, x ∉ T r → ∀ l : Fin L × Fin L,
      (blockGamma W L (gammaG g) (resLoop g E (mRoot g L E) ![l.1, l.2] ![true, false] r)
        (resLoop g E (mRoot g L E) ![l.1, l.2] ![true, false] r)
        (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
          (Real.sqrt (r * (gammaG g / W)) • x))).re ≤
        Brk * ζ r ^ 4 * w r l.1 l.2 ^ 2 / (1 - r))
    (hinit : ∀ x, x ∉ T0 → ∀ l : Fin L × Fin L,
      ‖flowErr W ⟨g, E, L, s⟩ ![l.1, l.2] ![true, false] x‖ ≤ I₁ * ζ s ^ 2 * w s l.1 l.2)
    {MA MB MI : ℝ}
    (hMA : ∀ r ∈ Set.Ioo s v, ∫ x, ‖coordGen (gammaG g / W)
        (step2Y g E (mRoot g L E) W (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E
          (mRoot g L E))) v a b) r (Real.sqrt (r * (gammaG g / W)) • x)‖ ^ (2 * (2 * p))
        ∂(μ W L) ≤ MA)
    (hMB : ∀ r ∈ Set.Ioo s v, ∫ x, ‖coordGamma (gammaG g / W)
        (step2Y g E (mRoot g L E) W (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E
          (mRoot g L E))) v a b r)
        (step2Y g E (mRoot g L E) W (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E
          (mRoot g L E))) v a b r) (Real.sqrt (r * (gammaG g / W)) • x)‖ ^ (2 * p) ∂(μ W L) ≤ MB)
    (hMI : ∫ x, ‖step2Y g E (mRoot g L E) W (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E
          (mRoot g L E))) v a b s (Real.sqrt (s * (gammaG g / W)) • x)‖ ^ (2 * (2 * p))
        ∂(μ W L) ≤ MI) :
    (∫ x, ‖flowErr W ⟨g, E, L, v⟩ ![a, b] ![true, false] x‖ ^ (2 * p) ∂(μ W L)) ^
        (1 / (2 * (p : ℝ))) ≤
      I₁ * Cpw * ((1 - s) / (1 - v)) ^ 2 * ζ v ^ 2 * wv +
        (Real.sqrt MI * Real.sqrt δ) ^ (1 / (2 * (p : ℝ))) +
        Real.sqrt ((2 * p - 1) * (Brk * Cpw ^ 2 * ζ v ^ 4 * wv ^ 2 * ((1 - s) / (1 - v)) ^ 4 / 4 +
          (Real.sqrt MB * Real.sqrt δ) ^ (1 / (p : ℝ)))) +
        (Src * Cpw * ζ v ^ 2 * wv * ((1 - s) / (1 - v)) ^ 2 / 2 +
          (Real.sqrt MA * Real.sqrt δ) ^ (1 / (2 * (p : ℝ)))) := by
  set m := mRoot g L E with hmdef
  set P := pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) with hPdef
  set σ2 := gammaG g / W with hσ2def
  have hL1 : 1 ≤ L := by omega
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  have hσ2 : 0 ≤ σ2 := by rw [hσ2def]; positivity
  have hP0 : ∀ x z, 0 ≤ P x z := fun x z => by
    simp only [hPdef, pairP, Matrix.of_apply]; positivity
  have hProw : ∀ x, ∑ z, P x z = 1 := fun x => pairP_row_sum (hopB g) (gammaG g) hγ L hL1 E m hm x
  have hv0 : 0 ≤ v := hs.trans hsv
  have hUv := step2_isUnit P hP0 hProw hL1 hv0 hv
  have hev : 0 < 1 - v := by linarith
  set Y := step2Y g E m W P v a b with hYdef
  have hY : HeatClass Y (-1 / 2) ((1 + v) / 2) := step2_heatClass_Y g E m W hW hL hm P hv a b
  -- the left side is the moment of `Y_v`
  have hlhs : ∀ x : Ω W L, ‖flowErr W ⟨g, E, L, v⟩ ![a, b] ![true, false] x‖ =
      ‖Y v (Real.sqrt (v * σ2) • x)‖ := by
    intro x
    rw [step2_flowErr_eq g E W L hv0 (a, b) x, hYdef, step2_Y_self g E m W P hUv a b]
  have hR0 : 0 ≤ (1 - s) / (1 - v) := div_nonneg (by linarith) hev.le
  -- the rates on the good events
  set A₁ := Src * Cpw * ζ v ^ 2 * wv / (1 - v) ^ 2 with hA₁
  set B₁ := Brk * Cpw ^ 2 * ζ v ^ 4 * wv ^ 2 / (1 - v) ^ 4 with hB₁
  have hCw0 : 0 ≤ Cpw * wv := by
    have h1 := (Finset.sum_nonneg fun l (_ : l ∈ (Finset.univ : Finset (Fin L × Fin L))) =>
      mul_nonneg ((step2_coef_sum P hP0 hProw hv0 le_rfl hv a b).1 l) (hw0 v l.1 l.2)).trans
      (hprop v ⟨hsv, le_rfl⟩)
    have h2 : ((1 - v) / (1 - v)) ^ 2 = 1 := by rw [div_self hev.ne', one_pow]
    rw [h2] at h1
    linarith
  have hA₁0 : 0 ≤ A₁ := by
    rw [hA₁]
    have := hζ0 v ⟨hsv, le_rfl⟩
    have : 0 ≤ Src * (Cpw * wv) * ζ v ^ 2 := by positivity
    have e : Src * Cpw * ζ v ^ 2 * wv = Src * (Cpw * wv) * ζ v ^ 2 := by ring
    rw [e]; positivity
  have hB₁0 : 0 ≤ B₁ := by
    rw [hB₁]
    have e : Brk * Cpw ^ 2 * ζ v ^ 4 * wv ^ 2 = Brk * (Cpw * wv) ^ 2 * ζ v ^ 4 := by ring
    rw [e]
    have := hζ0 v ⟨hsv, le_rfl⟩
    positivity
  have hGgood : ∀ r ∈ Set.Ioo s v, ∀ x, x ∉ T r →
      ‖coordGen σ2 Y r (Real.sqrt (r * σ2) • x)‖ ≤ A₁ * (1 - r) := by
    intro r hr x hx
    have hr0 : 0 ≤ r := hs.trans hr.1.le
    have hrv : r ≤ v := hr.2.le
    have h := step2_gen_good g E m W hW hL hm hr0 hrv hv a b (Real.sqrt (r * σ2) • x) (w r)
      (hw0 r) hSrc (hζ0 r ⟨hr.1.le, hrv⟩) (hζv r ⟨hr.1.le, hrv⟩) (hsrc r hr x hx)
      (hprop r ⟨hr.1.le, hrv⟩)
    rw [hA₁]
    exact h
  have hΓgood : ∀ r ∈ Set.Ioo s v, ∀ x, x ∉ T r →
      ‖coordGamma σ2 (Y r) (Y r) (Real.sqrt (r * σ2) • x)‖ ≤ B₁ * (1 - r) ^ 3 := by
    intro r hr x hx
    have hr0 : 0 ≤ r := hs.trans hr.1.le
    have hrv : r ≤ v := hr.2.le
    have h := step2_gam_good g E m W hW hL hm hr0 hrv hv a b (Real.sqrt (r * σ2) • x) (w r)
      (hw0 r) hBrk (hζ0 r ⟨hr.1.le, hrv⟩) (hζv r ⟨hr.1.le, hrv⟩) (hbrk r hr x hx)
      (hprop r ⟨hr.1.le, hrv⟩)
    rw [hB₁]
    exact h
  -- the start
  set I₀ := I₁ * Cpw * ((1 - s) / (1 - v)) ^ 2 * ζ v ^ 2 * wv with hI₀
  have hI₀0 : 0 ≤ I₀ := by
    rw [hI₀]
    have e : I₁ * Cpw * ((1 - s) / (1 - v)) ^ 2 * ζ v ^ 2 * wv =
        I₁ * (Cpw * wv) * ((1 - s) / (1 - v)) ^ 2 * ζ v ^ 2 := by ring
    rw [e]
    have := hζ0 v ⟨hsv, le_rfl⟩
    positivity
  have hIgood : ∀ x, x ∉ T0 → ‖Y s (Real.sqrt (s * σ2) • x)‖ ≤ I₀ := by
    intro x hx
    have h1 := step2_Y_norm_le g E m W P hP0 hProw hs hsv hv a b (Real.sqrt (s * σ2) • x)
    have hc0 := (step2_coef_sum P hP0 hProw hs hsv hv a b).1
    have h2 : ∀ l : Fin L × Fin L, step2Coef P v a b l s * ‖pairErrField g E m W L s
        (Real.sqrt (s * σ2) • x) l‖ ≤ step2Coef P v a b l s * (I₁ * ζ s ^ 2 * w s l.1 l.2) := by
      intro l
      refine mul_le_mul_of_nonneg_left ?_ (hc0 l)
      have := hinit x hx l
      rwa [step2_flowErr_eq g E W L hs l x] at this
    have hζs := hζ0 s ⟨le_rfl, hsv⟩
    have hζsv : ζ s ^ 2 ≤ ζ v ^ 2 := pow_le_pow_left₀ hζs (hζv s ⟨le_rfl, hsv⟩) 2
    calc ‖Y s (Real.sqrt (s * σ2) • x)‖
        ≤ ∑ l, step2Coef P v a b l s * ‖pairErrField g E m W L s (Real.sqrt (s * σ2) • x) l‖ := h1
      _ ≤ ∑ l : Fin L × Fin L, step2Coef P v a b l s * (I₁ * ζ s ^ 2 * w s l.1 l.2) :=
          Finset.sum_le_sum fun l _ => h2 l
      _ = I₁ * ζ s ^ 2 * ∑ l : Fin L × Fin L, step2Coef P v a b l s * w s l.1 l.2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
      _ ≤ I₁ * ζ s ^ 2 * (Cpw * ((1 - s) / (1 - v)) ^ 2 * wv) :=
          mul_le_mul_of_nonneg_left (hprop s ⟨le_rfl, hsv⟩) (by positivity)
      _ = (I₁ * (Cpw * wv) * ((1 - s) / (1 - v)) ^ 2) * ζ s ^ 2 := by ring
      _ ≤ (I₁ * (Cpw * wv) * ((1 - s) / (1 - v)) ^ 2) * ζ v ^ 2 :=
          mul_le_mul_of_nonneg_left hζsv (by positivity)
      _ = I₀ := by rw [hI₀]; ring
  have hcore := step2_lemmaM_core σ2 hσ2 Y (a' := -1 / 2) (b' := (1 + v) / 2) (by norm_num) hs hsv
    (by linarith) hv.le hY p hp T hTm hδ hTδ T0 hT0m hT0δ hA₁0 hB₁0 hI₀0 hGgood hΓgood hIgood
    hMA hMB hMI
  have hint_eq : (∫ x, ‖flowErr W ⟨g, E, L, v⟩ ![a, b] ![true, false] x‖ ^ (2 * p) ∂(μ W L)) =
      ∫ x, ‖Y v (Real.sqrt (v * σ2) • x)‖ ^ (2 * p) ∂(stdGauss (Fin L × Fin W × Fin W)) := by
    rw [step2_mu_eq]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only [hlhs x])
  rw [hint_eq]
  refine hcore.trans (le_of_eq ?_)
  have e1 : A₁ * (1 - s) ^ 2 / 2 = Src * Cpw * ζ v ^ 2 * wv * ((1 - s) / (1 - v)) ^ 2 / 2 := by
    rw [hA₁]; field_simp
  have e2 : B₁ * (1 - s) ^ 4 / 4 =
      Brk * Cpw ^ 2 * ζ v ^ 4 * wv ^ 2 * ((1 - s) / (1 - v)) ^ 4 / 4 := by
    rw [hB₁]; field_simp
  rw [e1, e2]

end Step2Core2

section Step2Crude

variable {L : ℕ}

/-- A continuous bounded nonnegative function has integrable powers under a finite measure. -/
private theorem step2_int_pow {ι : Type*} [Fintype ι] {P : Measure (ι → ℝ)} [IsFiniteMeasure P]
    {f : (ι → ℝ) → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) {C : ℝ} (hC : ∀ x, f x ≤ C)
    (k : ℕ) : Integrable (fun x => f x ^ k) P := by
  refine Integrable.of_bound ((hf.pow k).aestronglyMeasurable) (max C 0 ^ k)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (pow_nonneg (hf0 x) k)]
  exact pow_le_pow_left₀ (hf0 x) ((hC x).trans (le_max_left _ _)) k

/-- The crude moments of the propagated pair, its generator and its bracket, from moments of
`D₂`, of its generator and of the bracket of `ℒ₂` at the times of the step: with
`Σ_l |∂_r U U| ≤ 2(1 - v)⁻²` and `Σ_l U U ≤ (1 - v)⁻²`. -/
private theorem step2_moments (g E : ℝ) {W : ℕ} (hW : 1 ≤ W) (hL : 3 ≤ L)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E (mRoot g L E)) {s v : ℝ} (hs : 0 ≤ s)
    (hsv : s ≤ v) (hv : v < 1) (a b : Fin L) (p : ℕ) (hp : 1 ≤ p) {M₀ : ℝ}
    (hD : ∀ r ∈ Set.Icc s v, ∀ l : Fin L × Fin L,
      ∫ x, ‖flowErr W ⟨g, E, L, r⟩ ![l.1, l.2] ![true, false] x‖ ^ (2 * (2 * p)) ∂(μ W L) ≤ M₀)
    (hG : ∀ r ∈ Set.Ioo s v, ∀ l : Fin L × Fin L,
      ∫ x, ‖blockGen W L (gammaG g) (fun r N =>
          resLoop g E (mRoot g L E) ![l.1, l.2] ![true, false] r N -
            primLoop g W L E (mRoot g L E) r ![l.1, l.2] ![true, false]) r
          (flowH g W L r x)‖ ^ (2 * (2 * p)) ∂(μ W L) ≤ M₀)
    (hΓ : ∀ r ∈ Set.Ioo s v, ∀ l : Fin L × Fin L,
      Integrable (fun x => ‖blockGamma W L (gammaG g)
          (resLoop g E (mRoot g L E) ![l.1, l.2] ![true, false] r)
          (resLoop g E (mRoot g L E) ![l.1, l.2] ![true, false] r)
          (flowH g W L r x)‖ ^ (2 * p)) (μ W L) ∧
      ∫ x, ‖blockGamma W L (gammaG g)
          (resLoop g E (mRoot g L E) ![l.1, l.2] ![true, false] r)
          (resLoop g E (mRoot g L E) ![l.1, l.2] ![true, false] r)
          (flowH g W L r x)‖ ^ (2 * p) ∂(μ W L) ≤ M₀) :
    (∀ r ∈ Set.Ioo s v, ∫ x, ‖coordGen (gammaG g / W)
        (step2Y g E (mRoot g L E) W (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E
          (mRoot g L E))) v a b) r (Real.sqrt (r * (gammaG g / W)) • x)‖ ^ (2 * (2 * p))
        ∂(μ W L) ≤ (3 * ((1 - v) ^ 2)⁻¹) ^ (2 * (2 * p)) * M₀) ∧
    (∀ r ∈ Set.Ioo s v, ∫ x, ‖coordGamma (gammaG g / W)
        (step2Y g E (mRoot g L E) W (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E
          (mRoot g L E))) v a b r)
        (step2Y g E (mRoot g L E) W (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E
          (mRoot g L E))) v a b r) (Real.sqrt (r * (gammaG g / W)) • x)‖ ^ (2 * p) ∂(μ W L) ≤
        (((1 - v) ^ 2)⁻¹) ^ (2 * (2 * p)) * M₀) ∧
    ∫ x, ‖step2Y g E (mRoot g L E) W (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E
          (mRoot g L E))) v a b s (Real.sqrt (s * (gammaG g / W)) • x)‖ ^ (2 * (2 * p))
        ∂(μ W L) ≤ (((1 - v) ^ 2)⁻¹) ^ (2 * (2 * p)) * M₀ := by
  set m := mRoot g L E with hmdef
  set P := pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) with hPdef
  set σ2 := gammaG g / W with hσ2def
  have hL1 : 1 ≤ L := by omega
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  have hσ2 : 0 ≤ σ2 := by rw [hσ2def]; positivity
  have hP0 : ∀ x z, 0 ≤ P x z := fun x z => by
    simp only [hPdef, pairP, Matrix.of_apply]; positivity
  have hProw : ∀ x, ∑ z, P x z = 1 := fun x => pairP_row_sum (hopB g) (gammaG g) hγ L hL1 E m hm x
  have hv0 : 0 ≤ v := hs.trans hsv
  have hev : 0 < 1 - v := by linarith
  set k := 2 * (2 * p) with hk
  have hk1 : 1 ≤ k := by omega
  have hM₀ : 0 ≤ M₀ := (integral_nonneg fun x => by positivity).trans (hD s ⟨le_rfl, hsv⟩ (a, b))
  set Y := step2Y g E m W P v a b with hYdef
  have hY : HeatClass Y (-1 / 2) ((1 + v) / 2) := step2_heatClass_Y g E m W hW hL hm P hv a b
  have hcls : ∀ l : Fin L × Fin L, HeatClass (fun r x => pairErrField g E m W L r x l) (-1 / 2)
      ((1 + v) / 2) := fun l =>
    heatClass_pairErrField g E m W L hW hL hm l (by norm_num) (by linarith)
  have hIoo : ∀ r, 0 ≤ r → r ≤ v → r ∈ Set.Ioo (-1 / 2 : ℝ) ((1 + v) / 2) := fun r hr0 hrv =>
    ⟨by linarith, by linarith⟩
  have hsc : Continuous (fun x : Ω W L => fun r : ℝ => Real.sqrt (r * σ2) • x) := by fun_prop
  -- coefficient sums
  have hcoef : ∀ r, 0 ≤ r → r ≤ v →
      ∑ l : Fin L × Fin L, step2Coef P v a b l r ≤ ((1 - v) ^ 2)⁻¹ := by
    intro r hr0 hrv
    rw [(step2_coef_sum P hP0 hProw hr0 hrv hv a b).2, div_pow, div_eq_mul_inv]
    have h1 : (1 - r) ^ 2 ≤ 1 := by
      have : 0 ≤ 1 - r := by linarith
      have : 1 - r ≤ 1 := by linarith
      nlinarith
    calc (1 - r) ^ 2 * ((1 - v) ^ 2)⁻¹ ≤ 1 * ((1 - v) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := one_mul _
  have hcoef' : ∀ r, 0 ≤ r → r ≤ v →
      ∑ l : Fin L × Fin L, ‖step2Coef' P v a b l r‖ ≤ 2 * ((1 - v) ^ 2)⁻¹ := by
    intro r hr0 hrv
    rw [step2_coef'_sum P hP0 hProw hr0 hrv hv a b]
    have h1 : 1 - r ≤ 1 := by linarith
    have h0 : 0 ≤ 1 - r := by linarith
    rw [show 2 * (1 - v)⁻¹ * ((1 - r) / (1 - v)) = 2 * (1 - r) * ((1 - v) ^ 2)⁻¹ by
      field_simp]
    have : 2 * (1 - r) ≤ 2 := by linarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  -- (1) the generator
  have h1 : ∀ r ∈ Set.Ioo s v, ∫ x, ‖coordGen σ2 Y r (Real.sqrt (r * σ2) • x)‖ ^ k ∂(μ W L) ≤
      (3 * ((1 - v) ^ 2)⁻¹) ^ k * M₀ := by
    intro r hr
    have hr0 : 0 ≤ r := hs.trans hr.1.le
    have hrv : r ≤ v := hr.2.le
    have hrI := hIoo r hr0 hrv
    have hlin : ∀ y : Ω W L, coordGen σ2 Y r y = ∑ l : Fin L × Fin L,
        (((step2Coef' P v a b l r : ℝ) : ℂ) * pairErrField g E m W L r y l +
          ((step2Coef P v a b l r : ℝ) : ℂ) *
            coordGen σ2 (fun r x => pairErrField g E m W L r x l) r y) := fun y =>
      step2_coordGen_lincomb σ2 (fun l r => ((step2Coef P v a b l r : ℝ) : ℂ))
        (fun l r => ((step2Coef' P v a b l r : ℝ) : ℂ)) (fun l r x => pairErrField g E m W L r x l)
        r y (fun l => step2_coef_hasDerivAt P v a b l r)
        (fun l => (step2_heat_slice (hcls l) hrI).2.2 y)
        (fun l => (step2_heat_slice (hcls l) hrI).2.1)
    -- the family and its weights
    set α : Bool × (Fin L × Fin L) → ℝ := fun i =>
      if i.1 then ‖step2Coef' P v a b i.2 r‖ else step2Coef P v a b i.2 r with hα
    set X : Bool × (Fin L × Fin L) → Ω W L → ℝ := fun i x =>
      if i.1 then ‖pairErrField g E m W L r (Real.sqrt (r * σ2) • x) i.2‖
      else ‖coordGen σ2 (fun r x => pairErrField g E m W L r x i.2) r (Real.sqrt (r * σ2) • x)‖
      with hX
    have hc0 := (step2_coef_sum P hP0 hProw hr0 hrv hv a b).1
    have hα0 : ∀ i, 0 ≤ α i := fun i => by
      simp only [hα]; split_ifs
      · exact norm_nonneg _
      · exact hc0 _
    have hX0 : ∀ i x, 0 ≤ X i x := fun i x => by simp only [hX]; split_ifs <;> exact norm_nonneg _
    have hjetl : ∀ l, _ := fun l => step2_class_jet (hcls l) hrI σ2
    have hjetY := step2_class_jet hY hrI σ2
    have hXi : ∀ i, Integrable (fun x => X i x ^ k) (μ W L) := by
      intro ⟨b', l⟩
      obtain ⟨-, hc2, ⟨CY, hCY⟩, ⟨hGc, CG, hCG⟩, -⟩ := hjetl l
      cases b'
      · simp only [hX, Bool.false_eq_true, ite_false]
        exact step2_int_pow (continuous_norm.comp (hGc.comp (continuous_const_smul _)))
          (fun _ => norm_nonneg _) (fun x => hCG _) k
      · simp only [hX, ite_true]
        exact step2_int_pow (continuous_norm.comp (hc2.continuous.comp (continuous_const_smul _)))
          (fun _ => norm_nonneg _) (fun x => hCY _) k
    have hXM : ∀ i, ∫ x, X i x ^ k ∂(μ W L) ≤ M₀ := by
      intro ⟨b', l⟩
      cases b'
      · simp only [hX, Bool.false_eq_true, ite_false]
        have e : ∀ x : Ω W L, ‖coordGen σ2 (fun r x => pairErrField g E m W L r x l) r
            (Real.sqrt (r * σ2) • x)‖ = ‖blockGen W L (gammaG g) (fun r N =>
              resLoop g E m ![l.1, l.2] ![true, false] r N -
                primLoop g W L E m r ![l.1, l.2] ![true, false]) r (flowH g W L r x)‖ := by
          intro x
          rw [step2_coordGen_eq, step2_flowH_eq g W L hr0]
        simp only [e]
        exact hG r hr l
      · simp only [hX, ite_true]
        have e : ∀ x : Ω W L, ‖pairErrField g E m W L r (Real.sqrt (r * σ2) • x) l‖ =
            ‖flowErr W ⟨g, E, L, r⟩ ![l.1, l.2] ![true, false] x‖ := by
          intro x
          rw [step2_flowErr_eq g E W L hr0 l x]
        simp only [e]
        exact hD r ⟨hr.1.le, hrv⟩ l
    obtain ⟨-, -, -, ⟨hGYc, CGY, hCGY⟩, -⟩ := hjetY
    have hf : Integrable (fun x => ‖coordGen σ2 Y r (Real.sqrt (r * σ2) • x)‖ ^ k) (μ W L) :=
      step2_int_pow (continuous_norm.comp (hGYc.comp (continuous_const_smul _)))
        (fun _ => norm_nonneg _) (fun x => hCGY _) k
    have hfX : ∀ x, ‖coordGen σ2 Y r (Real.sqrt (r * σ2) • x)‖ ≤ ∑ i, α i * X i x := by
      intro x
      have hR : ∑ i, α i * X i x = ∑ l : Fin L × Fin L,
          (‖step2Coef' P v a b l r‖ * ‖pairErrField g E m W L r (Real.sqrt (r * σ2) • x) l‖ +
            step2Coef P v a b l r * ‖coordGen σ2 (fun r x => pairErrField g E m W L r x l) r
              (Real.sqrt (r * σ2) • x)‖) := by
        rw [Fintype.sum_prod_type (f := fun i => α i * X i x), Fintype.sum_bool,
          ← Finset.sum_add_distrib]
        simp only [hα, hX, ite_true, Bool.false_eq_true, ite_false]
      rw [hR, hlin]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (hc0 l)]
    have hj := step2_jensen_moment (μ W L) k hk1 _ hf (fun _ => norm_nonneg _) α hα0 X hX0 hXi hXM
      hfX
    have hsum : ∑ i, α i ≤ 3 * ((1 - v) ^ 2)⁻¹ := by
      rw [Fintype.sum_prod_type (f := α), Fintype.sum_bool]
      simp only [hα, ite_true, Bool.false_eq_true, ite_false]
      have := hcoef' r hr0 hrv
      have := hcoef r hr0 hrv
      linarith
    refine hj.trans (mul_le_mul_of_nonneg_right ?_ hM₀)
    exact pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => hα0 i) hsum k
  -- (2) the bracket
  have h2 : ∀ r ∈ Set.Ioo s v, ∫ x, ‖coordGamma σ2 (Y r) (Y r) (Real.sqrt (r * σ2) • x)‖ ^ (2 * p)
      ∂(μ W L) ≤ (((1 - v) ^ 2)⁻¹) ^ k * M₀ := by
    intro r hr
    have hr0 : 0 ≤ r := hs.trans hr.1.le
    have hrv : r ≤ v := hr.2.le
    have hrI := hIoo r hr0 hrv
    have hc0 := (step2_coef_sum P hP0 hProw hr0 hrv hv a b).1
    set Γl : Fin L × Fin L → Ω W L → ℂ := fun l x => blockGamma W L (gammaG g)
      (resLoop g E m ![l.1, l.2] ![true, false] r) (resLoop g E m ![l.1, l.2] ![true, false] r)
      (flowH g W L r x) with hΓl
    set X : Fin L × Fin L → Ω W L → ℝ := fun l x => Real.sqrt ‖Γl l x‖ with hX
    set f : Ω W L → ℝ := fun x =>
      Real.sqrt ‖coordGamma σ2 (Y r) (Y r) (Real.sqrt (r * σ2) • x)‖ with hf
    have hpow : ∀ t : ℝ, 0 ≤ t → Real.sqrt t ^ k = t ^ (2 * p) := fun t ht => by
      rw [hk, pow_mul, Real.sq_sqrt ht]
    have hXi : ∀ l, Integrable (fun x => X l x ^ k) (μ W L) := fun l => by
      simp only [hX, hpow _ (norm_nonneg _)]
      exact (hΓ r hr l).1
    have hXM : ∀ l, ∫ x, X l x ^ k ∂(μ W L) ≤ M₀ := fun l => by
      simp only [hX, hpow _ (norm_nonneg _)]
      exact (hΓ r hr l).2
    obtain ⟨-, -, -, -, ⟨hΓc, CΓ, hCΓ⟩⟩ := step2_class_jet hY hrI σ2
    have hfi : Integrable (fun x => f x ^ k) (μ W L) := by
      refine step2_int_pow ?_ (fun _ => Real.sqrt_nonneg _) (C := Real.sqrt (max CΓ 0)) ?_ k
      · exact Real.continuous_sqrt.comp (continuous_norm.comp (hΓc.comp (continuous_const_smul _)))
      · intro x
        exact Real.sqrt_le_sqrt ((hCΓ _).trans (le_max_left _ _))
    have hfX : ∀ x, f x ≤ ∑ l, step2Coef P v a b l r * X l x := by
      intro x
      have hg := step2_gamma_Y g E m W hW hL hm P hP0 hProw hr0 hrv hv a b
        (Real.sqrt (r * σ2) • x)
      rw [← step2_flowH_eq g W L hr0] at hg
      have hS0 : 0 ≤ ∑ l, step2Coef P v a b l r * Real.sqrt (Γl l x).re :=
        Finset.sum_nonneg fun l _ => mul_nonneg (hc0 l) (Real.sqrt_nonneg _)
      calc f x ≤ Real.sqrt ((∑ l, step2Coef P v a b l r * Real.sqrt (Γl l x).re) ^ 2) :=
            Real.sqrt_le_sqrt hg
        _ = ∑ l, step2Coef P v a b l r * Real.sqrt (Γl l x).re := Real.sqrt_sq hS0
        _ ≤ ∑ l, step2Coef P v a b l r * X l x := by
            refine Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left ?_ (hc0 l)
            exact Real.sqrt_le_sqrt ((le_abs_self _).trans (Complex.abs_re_le_norm _))
    have hj := step2_jensen_moment (μ W L) k hk1 f hfi (fun _ => Real.sqrt_nonneg _)
      (fun l => step2Coef P v a b l r) hc0 X (fun l x => Real.sqrt_nonneg _) hXi hXM hfX
    have e : ∀ x, ‖coordGamma σ2 (Y r) (Y r) (Real.sqrt (r * σ2) • x)‖ ^ (2 * p) = f x ^ k :=
      fun x => by simp only [hf]; rw [hpow _ (norm_nonneg _)]
    simp only [e]
    refine hj.trans (mul_le_mul_of_nonneg_right ?_ hM₀)
    exact pow_le_pow_left₀ (Finset.sum_nonneg fun l _ => hc0 l) (hcoef r hr0 hrv) k
  -- (3) the start
  have h3 : ∫ x, ‖Y s (Real.sqrt (s * σ2) • x)‖ ^ k ∂(μ W L) ≤ (((1 - v) ^ 2)⁻¹) ^ k * M₀ := by
    have hc0 := (step2_coef_sum P hP0 hProw hs hsv hv a b).1
    set X : Fin L × Fin L → Ω W L → ℝ := fun l x =>
      ‖pairErrField g E m W L s (Real.sqrt (s * σ2) • x) l‖ with hX
    have hsI' : s ∈ Set.Ioo (-1 / 2 : ℝ) ((1 + v) / 2) := ⟨by linarith, by linarith⟩
    have hXi : ∀ l, Integrable (fun x => X l x ^ k) (μ W L) := fun l => by
      obtain ⟨-, hc2, ⟨CY, hCY⟩, -, -⟩ := step2_class_jet (hcls l) hsI' σ2
      exact step2_int_pow (continuous_norm.comp (hc2.continuous.comp (continuous_const_smul _)))
        (fun _ => norm_nonneg _) (fun x => hCY _) k
    have hXM : ∀ l, ∫ x, X l x ^ k ∂(μ W L) ≤ M₀ := fun l => by
      have e : ∀ x : Ω W L, X l x = ‖flowErr W ⟨g, E, L, s⟩ ![l.1, l.2] ![true, false] x‖ :=
        fun x => by simp only [hX]; rw [step2_flowErr_eq g E W L hs l x]
      simp only [e]
      exact hD s ⟨le_rfl, hsv⟩ l
    obtain ⟨-, hc2Y, ⟨CY, hCY⟩, -, -⟩ := step2_class_jet hY hsI' σ2
    have hfi : Integrable (fun x => ‖Y s (Real.sqrt (s * σ2) • x)‖ ^ k) (μ W L) :=
      step2_int_pow (continuous_norm.comp (hc2Y.continuous.comp (continuous_const_smul _)))
        (fun _ => norm_nonneg _) (fun x => hCY _) k
    have hfX : ∀ x, ‖Y s (Real.sqrt (s * σ2) • x)‖ ≤ ∑ l, step2Coef P v a b l s * X l x :=
      fun x => step2_Y_norm_le g E m W P hP0 hProw hs hsv hv a b _
    have hj := step2_jensen_moment (μ W L) k hk1 _ hfi (fun _ => norm_nonneg _)
      (fun l => step2Coef P v a b l s) hc0 X (fun l x => norm_nonneg _) hXi hXM hfX
    refine hj.trans (mul_le_mul_of_nonneg_right ?_ hM₀)
    exact pow_le_pow_left₀ (Finset.sum_nonneg fun l _ => hc0 l) (hcoef s hs hsv) k
  exact ⟨h1, h2, h3⟩

end Step2Crude

section Step2D2Moment

open scoped Matrix.Norms.L2Operator

/-- An entry is at most the operator norm. -/
private theorem step2_norm_entry_le {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (i j : n) : ‖X i j‖ ≤ ‖X‖ := by
  have h := Matrix.l2_opNorm_mulVec X ((EuclideanSpace.equiv n ℂ).symm (Pi.single j 1))
  have hx : ‖(EuclideanSpace.equiv n ℂ).symm (Pi.single j (1 : ℂ))‖ = 1 := by simp
  rw [hx, mul_one] at h
  refine le_trans (le_of_eq ?_) ((PiLp.norm_apply_le _ i).trans h)
  simp [Matrix.mulVec_single]

/-- `W⁻² ‖X_{ab}‖²_HS ≤ ‖X_{ab}‖²`. -/
private theorem step2_hs_le_op {W L : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) :
    ((W : ℝ) ^ 2)⁻¹ * blockHS2 X a b ≤ ‖blockOf X a b‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW; simp
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  rw [inv_mul_le_iff₀ (by positivity)]
  unfold blockHS2
  calc ∑ α : Fin W, ∑ β : Fin W, ‖X (a, α) (b, β)‖ ^ 2
      ≤ ∑ _α : Fin W, ∑ _β : Fin W, ‖blockOf X a b‖ ^ 2 := by
        refine Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ => ?_
        have := step2_norm_entry_le (blockOf X a b) α β
        exact pow_le_pow_left₀ (norm_nonneg _) this 2
    _ = (W : ℝ) ^ 2 * ‖blockOf X a b‖ ^ 2 := by simp; ring

/-- `‖D₂(a, b; +, -)‖ ≤ ‖G_{ba}‖² + ‖𝒦₂‖`. -/
private theorem step2_flowErr_le (W : ℕ) (p : FlowPt) (a b : Fin p.L) (ω : Ω W p.L) :
    ‖flowErr W p ![a, b] ![true, false] ω‖ ≤ ‖blockOf (flowG W p ω) b a‖ ^ 2 +
      ‖primLoop p.g W p.L p.E (mRoot p.g p.L p.E) p.u ![a, b] ![true, false]‖ := by
  unfold flowErr
  refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
  rw [step2_loopTr_two_hs, Complex.norm_real, Real.norm_of_nonneg (by unfold blockHS2; positivity)]
  exact step2_hs_le_op _ _ _

/-- On the characteristic, the resolvent of a pair `(p, η_u)` is the resolvent of the flow. -/
private theorem step2_segG_eta (W : ℕ) (p : FlowPt) (ω : Ω W p.L) :
    segG W (p, etaChar p.g (mRoot p.g p.L p.E) p.u) ω = flowG W p ω := by
  unfold segG flowG
  congr 1
  apply Complex.ext
  · simp
  · simp [zChar, etaChar]

/-- `(x + y)^k ≤ 2^{k-1}(x^k + y^k)` for `x, y ≥ 0`. -/
private theorem step2_add_pow_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (k : ℕ) :
    (x + y) ^ k ≤ 2 ^ (k - 1) * (x ^ k + y ^ k) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; norm_num
  have h := Real.pow_arith_mean_le_arith_mean_pow Finset.univ (fun _ : Fin 2 => (1 / 2 : ℝ))
    ![x, y] (fun _ _ => by norm_num) (by simp) (fun i _ => by fin_cases i <;> simpa) k
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  have e : 1 / 2 * x + 1 / 2 * y = (x + y) / 2 := by ring
  rw [e, div_pow] at h
  have h2 : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [div_le_iff₀ (by positivity)] at h
  calc (x + y) ^ k ≤ (1 / 2 * x ^ k + 1 / 2 * y ^ k) * 2 ^ k := h
    _ = 2 ^ (k - 1) * (x ^ k + y ^ k) := by rw [h2]; ring

/-- Moments of the mixed two-loop error at a pair `(p, η_u)` of the crude moments
(5.33) [fo:eq:coarse-time-input]: `E‖D₂‖^k ≤ 2^{k-1}(E‖G_{ba}‖^{2k} + K^k)` for `‖𝒦₂‖ ≤ K`. -/
private theorem step2_flowErr_moment (W : ℕ) (p : FlowPt) (a b : Fin p.L) (k : ℕ) {K : ℝ}
    (hK : 0 ≤ K)
    (hprim : ‖primLoop p.g W p.L p.E (mRoot p.g p.L p.E) p.u ![a, b] ![true, false]‖ ≤ K)
    (hint : Integrable (fun ω => ‖blockOf (flowG W p ω) b a‖ ^ (2 * k)) (μ W p.L)) :
    ∫ ω, ‖flowErr W p ![a, b] ![true, false] ω‖ ^ k ∂(μ W p.L) ≤
      2 ^ (k - 1) * (∫ ω, ‖blockOf (flowG W p ω) b a‖ ^ (2 * k) ∂(μ W p.L) + K ^ k) := by
  have hpt : ∀ ω, ‖flowErr W p ![a, b] ![true, false] ω‖ ^ k ≤
      2 ^ (k - 1) * (‖blockOf (flowG W p ω) b a‖ ^ (2 * k) + K ^ k) := by
    intro ω
    have h1 := step2_flowErr_le W p a b ω
    have h2 : ‖flowErr W p ![a, b] ![true, false] ω‖ ≤ ‖blockOf (flowG W p ω) b a‖ ^ 2 + K :=
      h1.trans (add_le_add le_rfl hprim)
    calc ‖flowErr W p ![a, b] ![true, false] ω‖ ^ k
        ≤ (‖blockOf (flowG W p ω) b a‖ ^ 2 + K) ^ k := pow_le_pow_left₀ (norm_nonneg _) h2 k
      _ ≤ 2 ^ (k - 1) * ((‖blockOf (flowG W p ω) b a‖ ^ 2) ^ k + K ^ k) :=
          step2_add_pow_le (by positivity) hK k
      _ = _ := by rw [← pow_mul]
  have hint2 : Integrable (fun ω => 2 ^ (k - 1) * (‖blockOf (flowG W p ω) b a‖ ^ (2 * k) + K ^ k))
      (μ W p.L) := (hint.add (integrable_const _)).const_mul _
  calc ∫ ω, ‖flowErr W p ![a, b] ![true, false] ω‖ ^ k ∂(μ W p.L)
      ≤ ∫ ω, 2 ^ (k - 1) * (‖blockOf (flowG W p ω) b a‖ ^ (2 * k) + K ^ k) ∂(μ W p.L) :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => by positivity) hint2
          (Eventually.of_forall hpt)
    _ = _ := by
        rw [integral_const_mul, integral_add hint (integrable_const _), integral_const]
        simp

end Step2D2Moment

section Step2NumSrc

/-- The source and bracket constants at the loss `ω`, with `Λ = ωA²`, `A = R^{M/2}`, under
`A³ζ_t ≤ R²`, `A⁴ζ_t ≤ R⁴`, `A⁶ζ_t ≤ R⁸`: `Src ≤ ω⁶R⁴` and `Brk ≤ ω¹¹R⁸`. -/
private theorem step2_num_srcA {ω R A Λ C' Cc lH ζt : ℝ} (hω : 64 ≤ ω) (hR : 1 ≤ R) (hRA : R ≤ A)
    (hΛ : Λ = ω * A ^ 2) (hC'0 : 0 ≤ C') (hC' : C' ≤ ω) (hCc0 : 0 ≤ Cc) (hCc : Cc ≤ ω)
    (hlH0 : 0 ≤ lH) (hlH : lH ≤ ω) (hζt : 0 ≤ ζt) (hA3 : A ^ 3 * ζt ≤ R ^ 2)
    (hA4 : A ^ 4 * ζt ≤ R ^ 4) (hA6 : A ^ 6 * ζt ≤ R ^ 8) :
    step2Src ω R Λ C' Cc lH ζt ≤ ω ^ 6 * R ^ 4 ∧ step2Brk ω R Λ C' Cc lH ζt ≤ ω ^ 11 * R ^ 8 := by
  have hω0 : 0 < ω := by linarith
  have hω1 : 1 ≤ ω := by linarith
  have hA1 : 1 ≤ A := hR.trans hRA
  have hA0 : 0 < A := by linarith
  have hR0 : 0 < R := by linarith
  have hCΛ0 : 0 ≤ C' + Λ := by rw [hΛ]; positivity
  have hCΛ : C' + Λ ≤ 2 * ω * A ^ 2 := by
    rw [hΛ]
    have : 1 ≤ A ^ 2 := one_le_pow₀ hA1
    nlinarith
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hmx : max (ω ^ 2 * R) (Real.sqrt (C' + Λ)) ≤ ω ^ 2 * A := by
    refine max_le (mul_le_mul_of_nonneg_left hRA (by positivity)) ?_
    rw [Real.sqrt_le_left (by positivity)]
    calc C' + Λ ≤ 2 * ω * A ^ 2 := hCΛ
      _ ≤ (ω ^ 2 * A) ^ 2 := by
          have h1 : 2 * ω ≤ ω ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 64) hω 3]
          calc 2 * ω * A ^ 2 ≤ ω ^ 4 * A ^ 2 := mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = (ω ^ 2 * A) ^ 2 := by ring
  have hmx0 : 0 ≤ max (ω ^ 2 * R) (Real.sqrt (C' + Λ)) := le_max_of_le_right (Real.sqrt_nonneg _)
  constructor
  · unfold step2Src
    have t1 : ω * (2 * Real.sqrt 2 * ω ^ 3 * R ^ 4 * (4 * lH + 2) + 1) ≤ 19 * ω ^ 5 * R ^ 4 := by
      have h4 : 4 * lH + 2 ≤ 6 * ω := by linarith
      have hR4 : 1 ≤ R ^ 4 := one_le_pow₀ hR
      have h1 : 2 * Real.sqrt 2 * ω ^ 3 * R ^ 4 * (4 * lH + 2) ≤ 3 * ω ^ 3 * R ^ 4 * (6 * ω) := by
        have : 2 * Real.sqrt 2 ≤ 3 := by linarith
        have h0 : 0 ≤ 4 * lH + 2 := by linarith
        calc 2 * Real.sqrt 2 * ω ^ 3 * R ^ 4 * (4 * lH + 2)
            ≤ 3 * ω ^ 3 * R ^ 4 * (4 * lH + 2) := by gcongr
          _ ≤ 3 * ω ^ 3 * R ^ 4 * (6 * ω) := by gcongr
      have h2 : ω * 1 ≤ ω ^ 5 * R ^ 4 := by
        have : ω ≤ ω ^ 5 := le_self_pow₀ hω1 (by norm_num)
        nlinarith
      nlinarith
    have t2 : 2 * ω * R ^ 2 * (C' + Λ) * max (ω ^ 2 * R) (Real.sqrt (C' + Λ)) * Cc * ζt ≤
        4 * ω ^ 5 * R ^ 4 := by
      calc 2 * ω * R ^ 2 * (C' + Λ) * max (ω ^ 2 * R) (Real.sqrt (C' + Λ)) * Cc * ζt
          ≤ 2 * ω * R ^ 2 * (2 * ω * A ^ 2) * (ω ^ 2 * A) * ω * ζt := by gcongr
        _ = 4 * ω ^ 5 * R ^ 2 * (A ^ 3 * ζt) := by ring
        _ ≤ 4 * ω ^ 5 * R ^ 2 * R ^ 2 := by gcongr
        _ = 4 * ω ^ 5 * R ^ 4 := by ring
    have t3 : Λ ^ 2 * Cc * ζt ≤ ω ^ 3 * R ^ 4 := by
      rw [hΛ]
      calc (ω * A ^ 2) ^ 2 * Cc * ζt ≤ (ω * A ^ 2) ^ 2 * ω * ζt := by gcongr
        _ = ω ^ 3 * (A ^ 4 * ζt) := by ring
        _ ≤ ω ^ 3 * R ^ 4 := by gcongr
    have h35 : ω ^ 3 * R ^ 4 ≤ ω ^ 5 * R ^ 4 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hω1 (by norm_num)) (by positivity)
    have h56 : 24 * ω ^ 5 * R ^ 4 ≤ ω ^ 6 * R ^ 4 := by
      have : 24 * ω ^ 5 ≤ ω ^ 6 := by
        have : ω ^ 6 = ω * ω ^ 5 := by ring
        rw [this]; nlinarith [pow_pos hω0 5]
      exact mul_le_mul_of_nonneg_right this (by positivity)
    linarith
  · unfold step2Brk
    have t1 : ω ^ 2 * (4 * ω ^ 5 * R ^ 5 * (4 * lH + 4) + 4 * ω ^ 3 * R ^ 3) ≤
        36 * ω ^ 8 * R ^ 8 := by
      have h4 : 4 * lH + 4 ≤ 8 * ω := by linarith
      have hR58 : R ^ 5 ≤ R ^ 8 := pow_le_pow_right₀ hR (by norm_num)
      have hR38 : R ^ 3 ≤ R ^ 8 := pow_le_pow_right₀ hR (by norm_num)
      have hω38 : ω ^ 3 ≤ ω ^ 6 := pow_le_pow_right₀ hω1 (by norm_num)
      calc ω ^ 2 * (4 * ω ^ 5 * R ^ 5 * (4 * lH + 4) + 4 * ω ^ 3 * R ^ 3)
          ≤ ω ^ 2 * (4 * ω ^ 5 * R ^ 8 * (8 * ω) + 4 * ω ^ 6 * R ^ 8) := by gcongr
        _ = 32 * ω ^ 8 * R ^ 8 + 4 * ω ^ 8 * R ^ 8 := by ring
        _ = 36 * ω ^ 8 * R ^ 8 := by ring
    have t2 : 4 * (C' + Λ) * max (ω ^ 2 * R) (Real.sqrt (C' + Λ)) ^ 4 * Cc * ζt ≤
        8 * ω ^ 10 * R ^ 8 := by
      calc 4 * (C' + Λ) * max (ω ^ 2 * R) (Real.sqrt (C' + Λ)) ^ 4 * Cc * ζt
          ≤ 4 * (2 * ω * A ^ 2) * (ω ^ 2 * A) ^ 4 * ω * ζt := by gcongr
        _ = 8 * ω ^ 10 * (A ^ 6 * ζt) := by ring
        _ ≤ 8 * ω ^ 10 * R ^ 8 := by gcongr
    have h810 : 36 * ω ^ 8 * R ^ 8 ≤ 36 * ω ^ 10 * R ^ 8 := by
      have : ω ^ 8 ≤ ω ^ 10 := pow_le_pow_right₀ hω1 (by norm_num)
      gcongr
    have h1011 : 44 * ω ^ 10 * R ^ 8 ≤ ω ^ 11 * R ^ 8 := by
      have : 44 * ω ^ 10 ≤ ω ^ 11 := by
        have : ω ^ 11 = ω * ω ^ 10 := by ring
        rw [this]; nlinarith [pow_pos hω0 10]
      exact mul_le_mul_of_nonneg_right this (by positivity)
    linarith

/-- `A = R^{M/2}` satisfies the three conditions of `step2_num_srcA` under `R^N ζ_t ≤ 1`,
`3M - 8 ≤ N`, `M ≥ 4`, and `R ≤ A`, `A² = R^M`. -/
private theorem step2_num_A {R M N ζt : ℝ} (hR : 1 ≤ R) (hM4 : 4 ≤ M) (hNM : 3 * M - 8 ≤ N)
    (hζt : 0 ≤ ζt) (hRN : R ^ N * ζt ≤ 1) :
    R ≤ R ^ (M / 2) ∧ (R ^ (M / 2)) ^ 2 = R ^ M ∧ (R ^ (M / 2)) ^ 3 * ζt ≤ R ^ 2 ∧
      (R ^ (M / 2)) ^ 4 * ζt ≤ R ^ 4 ∧ (R ^ (M / 2)) ^ 6 * ζt ≤ R ^ 8 := by
  have hR0 : 0 < R := by linarith
  have hpow : ∀ n : ℕ, (R ^ (M / 2)) ^ n = R ^ (n * (M / 2)) := fun n => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR0.le, mul_comm]
  have hle : ∀ x : ℝ, x ≤ N → R ^ x * ζt ≤ 1 := fun x hx =>
    (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hR hx) hζt).trans hRN
  have key : ∀ (n k : ℕ), (n : ℝ) * (M / 2) - k ≤ N →
      (R ^ (M / 2)) ^ n * ζt ≤ R ^ k := by
    intro n k hnk
    have h1 := hle _ hnk
    rw [hpow]
    have e : R ^ ((n : ℝ) * (M / 2)) = R ^ ((n : ℝ) * (M / 2) - k) * R ^ k := by
      rw [← Real.rpow_natCast R k, ← Real.rpow_add hR0]; ring_nf
    rw [e]
    have hk : 0 < R ^ k := pow_pos hR0 k
    calc R ^ ((n : ℝ) * (M / 2) - k) * R ^ k * ζt = (R ^ ((n : ℝ) * (M / 2) - k) * ζt) * R ^ k := by
          ring
      _ ≤ 1 * R ^ k := mul_le_mul_of_nonneg_right h1 hk.le
      _ = R ^ k := one_mul _
  refine ⟨?_, ?_, key 3 2 (by push_cast; linarith), key 4 4 (by push_cast; linarith),
    key 6 8 (by push_cast; linarith)⟩
  · calc R = R ^ (1 : ℝ) := (Real.rpow_one R).symm
      _ ≤ R ^ (M / 2) := Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  · rw [hpow]; push_cast; ring_nf

end Step2NumSrc

section Step2AtW2

open scoped Matrix.Norms.L2Operator

/-- A loop error along the flow at the slice of the scaled coordinates. -/
private theorem step2_flowErr_slice (g E : ℝ) (W L : ℕ) {r : ℝ} (hr : 0 ≤ r) {k : ℕ}
    (a : Fin k → Fin L) (σ : Fin k → Bool) (x : Ω W L) :
    flowErr W ⟨g, E, L, r⟩ a σ x = resLoop g E (mRoot g L E) a σ r
        (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
          (Real.sqrt (r * (gammaG g / W)) • x)) - primLoop g W L E (mRoot g L E) r a σ := by
  unfold flowErr resLoop
  rw [step2_flowG_eq g E W L hr]

/-- The source and bracket rows of the propagated pair at a point of the good event at a time
`r ≤ t`, from `step2_good_rows` with the regime rows at the scale `ℓ_r`. -/
private theorem step2_rows_of_good (g E : ℝ) {W L : ℕ} (hW : 3 ≤ W) (hL : 3 ≤ L) (hg : 0 ≤ g)
    (hroot : IsDysonRootV (hopB g) (gammaG g) L E (mRoot g L E)) {r t : ℝ} (hr0 : 0 ≤ r)
    (hrt : r ≤ t) (ht1 : t < 1)
    {cw θ F₁ ω R Λ C' Cc C0 : ℝ} (hcw0 : 0 ≤ cw) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2) (hF₁ : 0 ≤ F₁)
    (hω : 2 ≤ ω) (hR : 1 ≤ R) (hΛ : 0 ≤ Λ) (hC'0 : 0 ≤ C') (hCc0 : 0 ≤ Cc)
    (hζt1 : zetaProp g W L t ≤ 1)
    (hLℓ : (L : ℝ) / ellProp g L r ≤ (W : ℝ) ^ C0)
    (hsm1 : 2 * Real.sqrt 2 * ω ^ 2 * R ^ 3 * (W : ℝ) ^ C0 *
      Real.sqrt (ω * R * ((C' + Λ) + ω * R * (ω ^ 2 + C' + Λ)) *
        (Real.exp (-(cw * Real.log W ^ (2 : ℝ))) + (W : ℝ) ^ (-F₁))) * (2 * W) ≤ 1)
    (hsm2 : (C' + Λ) * (Real.exp (-(cw * Real.log W ^ (2 : ℝ))) + (W : ℝ) ^ (-F₁)) *
      (W : ℝ) ^ C0 ≤ 1)
    (hsh : ∀ ℓ d : ℝ, 0 < ℓ → 0 ≤ d → d ≤ 2 * (ℓ * Real.log W ^ ((3 : ℝ) / 2)) →
      ω⁻¹ ≤ weightFn cw θ F₁ W ℓ d)
    (hconv : ∀ x y : Fin L,
      ∑ c, weightFn cw θ F₁ W (ellProp g L r) (cycDist x c) *
          weightFn cw θ F₁ W (ellProp g L r) (cycDist c y) ≤
        Cc * ellProp g L r * weightFn cw θ F₁ W (ellProp g L r) (cycDist x y) ∧
      ∑ c, Real.sqrt (weightFn cw θ F₁ W (ellProp g L r) (cycDist x c) *
          weightFn cw θ F₁ W (ellProp g L r) (cycDist c y)) ≤
        Cc * ellProp g L r * Real.sqrt (weightFn cw θ F₁ W (ellProp g L r) (cycDist x y)))
    (hprim : ∀ x y : Fin L, ellProp g L r * Real.log W ^ ((3 : ℝ) / 2) < cycDist x y →
      ‖primLoop g W L E (mRoot g L E) r ![x, y] ![true, false]‖ ≤
        C' * zetaProp g W L r ^ 2 * weightFn cw θ F₁ W (ellProp g L r) (cycDist x y))
    (x : Ω W L) (hx : step2Good W L g E r R ω Λ cw θ F₁ x) (l : Fin L × Fin L) :
    ‖lightW g E (mRoot g L E) ![l.1, l.2] ![true, false] r
          (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
            (Real.sqrt (r * (gammaG g / W)) • x))‖ + gammaG g * W *
        ‖∑ e : Fin L, (resLoop g E (mRoot g L E) ![l.1, e] ![true, false] r
              (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
                (Real.sqrt (r * (gammaG g / W)) • x)) -
            primLoop g W L E (mRoot g L E) r ![l.1, e] ![true, false]) *
          (resLoop g E (mRoot g L E) ![e, l.2] ![true, false] r
              (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
                (Real.sqrt (r * (gammaG g / W)) • x)) -
            primLoop g W L E (mRoot g L E) r ![e, l.2] ![true, false])‖ ≤
        step2Src ω R Λ C' Cc (Real.log W ^ (2 / θ)) (zetaProp g W L t) *
          zetaProp g W L r ^ 2 * weightFn cw θ F₁ W (ellProp g L r) (cycDist l.1 l.2) / (1 - r) ∧
    (blockGamma W L (gammaG g) (resLoop g E (mRoot g L E) ![l.1, l.2] ![true, false] r)
        (resLoop g E (mRoot g L E) ![l.1, l.2] ![true, false] r)
        (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
          (Real.sqrt (r * (gammaG g / W)) • x))).re ≤
        step2Brk ω R Λ C' Cc (Real.log W ^ (2 / θ)) (zetaProp g W L t) *
          zetaProp g W L r ^ 4 * weightFn cw θ F₁ W (ellProp g L r) (cycDist l.1 l.2) ^ 2 /
            (1 - r) := by
  have hW1 : 1 ≤ W := by omega
  have hL1 : 1 ≤ L := by omega
  have hr1 : r < 1 := lt_of_le_of_lt hrt ht1
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  obtain ⟨hℓr1, -, hℓrL, hζrW, hζrt, -, -⟩ := scale_facts g hg W L hW1 hL1 r t hr0 hrt ht1
  obtain ⟨-, -, -, -, -, -, hΓr⟩ := scale_facts g hg W L hW1 hL1 r r hr0 le_rfl hr1
  set y := Real.sqrt (r * (gammaG g / W)) • x with hy
  set M := blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y with hM
  have hMh : M.IsHermitian := step2_slice_herm g hW1 y
  set ζ := zetaProp g W L r with hζ
  set ℓ := ellProp g L r with hℓ
  have hℓ0 : 0 < ℓ := by linarith
  have hζ0 : 0 < ζ := lt_of_lt_of_le (by positivity) hζrW
  set w : Fin L → Fin L → ℝ := fun a b => weightFn cw θ F₁ W ℓ (cycDist a b) with hw
  have hw0 : ∀ a b, 0 ≤ w a b := fun a b => (step2_weight_pos cw θ F₁ hW1 _ _).le
  have hw2 : ∀ a b, w a b ≤ 2 := fun a b =>
    step2_weight_le_two hcw0 hF₁ hW1 hℓ0 (Nat.cast_nonneg _)
  have hws : ∀ a b, w a b = w b a := fun a b => by simp only [hw, step2_cycDist_comm a b]
  have hwmin : ∀ a b, (W : ℝ) ^ (-F₁) ≤ w a b := fun a b => step2_weight_ge cw θ F₁ _ _
  have hwmin0 : 0 < (W : ℝ) ^ (-F₁) := Real.rpow_pos_of_pos hW0 _
  set εw := Real.exp (-(cw * Real.log W ^ (2 : ℝ))) + (W : ℝ) ^ (-F₁) with hεw
  have hεw0 : 0 ≤ εw := by positivity
  have hlog1 : 1 ≤ Real.log W := by
    rw [Real.le_log_iff_exp_le hW0]
    have h3 : (3 : ℝ) ≤ W := by exact_mod_cast hW
    linarith [Real.exp_one_lt_d9]
  have h32 : Real.log W ^ ((3 : ℝ) / 2) ≤ Real.log W ^ (2 / θ) :=
    Real.rpow_le_rpow_of_exponent_le hlog1 (by rw [le_div_iff₀ hθ]; linarith)
  have hζt0 : ζ ≤ zetaProp g W L t := hζrt
  have hζ1 : ζ ≤ 1 := hζrt.trans hζt1
  obtain ⟨hgop, hghs, hgavg, hgD⟩ := hx
  have eG : flowG W ⟨g, E, L, r⟩ x = resolventMat M (zChar g E (mRoot g L E) r) :=
    step2_flowG_eq g E W L hr0 x
  have hLℓ' : (L : ℝ) / ℓ ≤ (W : ℝ) ^ C0 := hLℓ
  have hrem1 := step2_rem1 (g := g) (L := L) hW1 (by linarith : (1 : ℝ) ≤ ω) hR hΛ hC'0 hζ0 hζ1
    hζrW hℓ0 hr1 hεw0 (by rw [mul_assoc (gammaG g * W) ℓ ζ, ← mul_assoc, hΓr,
      inv_mul_cancel₀ (by linarith)])
    (le_trans (by
      have h0 : 0 ≤ Real.sqrt (ω * R * ((C' + Λ) + ω * R * (ω ^ 2 + C' + Λ)) * εw) :=
        Real.sqrt_nonneg _
      gcongr) hsm1)
  have hrem2 : (C' + Λ) * εw * (L / ℓ) ≤ 1 := le_trans (by gcongr) hsm2
  refine step2_good_rows g E (mRoot g L E) hW1 hL hroot hr1 hMh w hw0 hw2 hws hwmin0 hwmin
    (ω := ω) (R := R) (Λ := Λ) (ζ := ζ) (ζt := zetaProp g W L t) (Cc := Cc) (ℓ := ℓ)
    (h := ℓ * Real.log W ^ ((3 : ℝ) / 2)) (lH := Real.log W ^ (2 / θ)) (εw := εw) (C' := C')
    hω hR hΛ hζ0 hζt0 hCc0 hℓr1 (by positivity) (mul_le_mul_of_nonneg_left h32 hℓ0.le) hC'0 hεw0
    (by rw [mul_assoc (gammaG g * W) ℓ ζ, ← mul_assoc, hΓr, inv_mul_cancel₀ (by linarith)])
    hrem1 hrem2 ?_ hconv ?_ ?_ ?_ (fun a b hab => hprim a b hab) ?_ ?_ l.1 l.2
  · intro a b
    have := hgD (a, b)
    rwa [step2_flowErr_slice g E W L hr0] at this
  · intro a b
    have := hgop (a, b)
    rw [eG] at this
    calc _ ≤ ω * (W * R * ζ) := this
      _ = _ := by ring
  · intro a b
    have := hghs (a, b)
    rw [eG] at this
    calc _ ≤ ω * ((W : ℝ) ^ 2 * R * ζ) := this
      _ = _ := by ring
  · intro c
    have := hgavg c
    rw [eG] at this
    calc _ ≤ ω * (R ^ 2 * ζ) := this
      _ = _ := by ring
  · intro a b hab
    exact hsh ℓ _ hℓ0 (Nat.cast_nonneg _) (by linarith)
  · intro a b hab
    exact step2_weight_far hcw0 hθ hW1 hℓ0 hab

end Step2AtW2

section Step2AtW3

open scoped Matrix.Norms.L2Operator

/-- The bad set of the good event at a time `r` is covered by the failures of the four inputs. -/
private theorem step2_bad_measure (g E : ℝ) (W L : ℕ) (r R ω Λ cw θ F₁ : ℝ) {δ₁ : ℝ}
    (hop : μ W L {x | ∃ l : Fin L × Fin L, ω * (W * R * zetaProp g W L r) <
      ‖((‖blockOf (flowG W ⟨g, E, L, r⟩ x) l.1 l.2‖ : ℝ) : ℂ)‖} ≤ ENNReal.ofReal δ₁)
    (hhs : μ W L {x | ∃ l : Fin L × Fin L, ω * ((W : ℝ) ^ 2 * R * zetaProp g W L r) <
      ‖((blockHS2 (flowG W ⟨g, E, L, r⟩ x) l.1 l.2 : ℝ) : ℂ)‖} ≤ ENNReal.ofReal δ₁)
    (havg : μ W L {x | ∃ c : Fin L, ω * (R ^ 2 * zetaProp g W L r) <
      ‖blockTr (flowG W ⟨g, E, L, r⟩ x - flowM W ⟨g, E, L, r⟩) c c‖} ≤ ENNReal.ofReal δ₁)
    (hD : μ W L {x | ∃ l : Fin L × Fin L, Λ * zetaProp g W L r ^ 2 *
        weightFn cw θ F₁ W (ellProp g L r) (cycDist l.1 l.2) <
      ‖flowErr W ⟨g, E, L, r⟩ ![l.1, l.2] ![true, false] x‖} ≤ ENNReal.ofReal δ₁) :
    μ W L {x | ¬ step2Good W L g E r R ω Λ cw θ F₁ x} ≤ ENNReal.ofReal (4 * δ₁) := by
  have hsub : {x | ¬ step2Good W L g E r R ω Λ cw θ F₁ x} ⊆
      (({x | ∃ l : Fin L × Fin L, ω * (W * R * zetaProp g W L r) <
        ‖((‖blockOf (flowG W ⟨g, E, L, r⟩ x) l.1 l.2‖ : ℝ) : ℂ)‖} ∪
      {x | ∃ l : Fin L × Fin L, ω * ((W : ℝ) ^ 2 * R * zetaProp g W L r) <
        ‖((blockHS2 (flowG W ⟨g, E, L, r⟩ x) l.1 l.2 : ℝ) : ℂ)‖}) ∪
      {x | ∃ c : Fin L, ω * (R ^ 2 * zetaProp g W L r) <
        ‖blockTr (flowG W ⟨g, E, L, r⟩ x - flowM W ⟨g, E, L, r⟩) c c‖}) ∪
      {x | ∃ l : Fin L × Fin L, Λ * zetaProp g W L r ^ 2 *
          weightFn cw θ F₁ W (ellProp g L r) (cycDist l.1 l.2) <
        ‖flowErr W ⟨g, E, L, r⟩ ![l.1, l.2] ![true, false] x‖} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, step2Good, not_and_or, not_forall, not_le] at hx
    rcases hx with ⟨l, hl⟩ | ⟨l, hl⟩ | ⟨c, hc⟩ | ⟨l, hl⟩
    · left; left; left
      exact ⟨l, by rwa [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]⟩
    · left; left; right
      exact ⟨l, by rwa [Complex.norm_real, Real.norm_of_nonneg (by unfold blockHS2; positivity)]⟩
    · left; right; exact ⟨c, hc⟩
    · right; exact ⟨l, hl⟩
  calc μ W L {x | ¬ step2Good W L g E r R ω Λ cw θ F₁ x} ≤ μ W L _ := measure_mono hsub
    _ ≤ ENNReal.ofReal δ₁ + ENNReal.ofReal δ₁ + ENNReal.ofReal δ₁ + ENNReal.ofReal δ₁ := by
        refine (measure_union_le _ _).trans (add_le_add ?_ hD)
        refine (measure_union_le _ _).trans (add_le_add ?_ havg)
        exact (measure_union_le _ _).trans (add_le_add hop hhs)
    _ ≤ ENNReal.ofReal (4 * δ₁) := by
        rcases le_or_gt 0 δ₁ with hδ | hδ
        · rw [← ENNReal.ofReal_add hδ hδ, ← ENNReal.ofReal_add (by linarith) hδ,
            ← ENNReal.ofReal_add (by linarith) hδ]
          exact le_of_eq (by congr 1; ring)
        · rw [ENNReal.ofReal_of_nonpos hδ.le]; simp

/-- The final simplification of the propagated pair estimate. -/
private theorem step2_final_simp {ω Cpw Rv R ζv wv Mb δ ρ Src Brk : ℝ} {p : ℕ} (hp : 1 ≤ p)
    (hω : 1 ≤ ω) (hR1 : 1 ≤ R) (hRv1 : 1 ≤ Rv) (hRvR : Rv ≤ R) (hCpw : 0 ≤ Cpw) (hζv0 : 0 ≤ ζv)
    (hwv0 : 0 ≤ wv) (hρ : 0 ≤ ρ) (hBrk0 : 0 ≤ Brk) (hSrc : Src ≤ ω ^ 6 * R ^ 4)
    (hBrk : Brk ≤ ω ^ 11 * R ^ 8)
    (hX1 : (Real.sqrt Mb * Real.sqrt δ) ^ (1 / (2 * (p : ℝ))) ≤ ρ)
    (hX2 : (Real.sqrt Mb * Real.sqrt δ) ^ (1 / (p : ℝ)) ≤ ρ ^ 2) :
    ω * Cpw * Rv ^ 2 * ζv ^ 2 * wv + (Real.sqrt Mb * Real.sqrt δ) ^ (1 / (2 * (p : ℝ))) +
        Real.sqrt ((2 * p - 1) * (Brk * Cpw ^ 2 * ζv ^ 4 * wv ^ 2 * Rv ^ 4 / 4 +
          (Real.sqrt Mb * Real.sqrt δ) ^ (1 / (p : ℝ)))) +
        (Src * Cpw * ζv ^ 2 * wv * Rv ^ 2 / 2 +
          (Real.sqrt Mb * Real.sqrt δ) ^ (1 / (2 * (p : ℝ)))) ≤
      Cpw * (1 + Real.sqrt (2 * p)) * ω ^ 6 * R ^ 6 * ζv ^ 2 * wv +
        (2 + Real.sqrt (2 * p)) * ρ := by
  have hR0 : 0 ≤ R := by linarith
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hsq0 : 0 ≤ Real.sqrt (2 * p) := Real.sqrt_nonneg _
  set X := Real.sqrt Mb * Real.sqrt δ with hXdef
  have hX0 : 0 ≤ X := by positivity
  set Q := ω ^ 6 * R ^ 4 * Cpw * ζv ^ 2 * wv * Rv ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hB : Real.sqrt ((2 * p - 1) * (Brk * Cpw ^ 2 * ζv ^ 4 * wv ^ 2 * Rv ^ 4 / 4 +
      X ^ (1 / (p : ℝ)))) ≤ Real.sqrt (2 * p) * (Q / 2) + Real.sqrt (2 * p) * ρ := by
    have hBk : Brk * Cpw ^ 2 * ζv ^ 4 * wv ^ 2 * Rv ^ 4 / 4 ≤ (Q / 2) ^ 2 := by
      have h11 : ω ^ 11 ≤ ω ^ 12 := pow_le_pow_right₀ hω (by norm_num)
      have hB12 : Brk ≤ ω ^ 12 * R ^ 8 := hBrk.trans
        (mul_le_mul_of_nonneg_right h11 (by positivity))
      have hC : 0 ≤ Cpw ^ 2 * ζv ^ 4 * wv ^ 2 * Rv ^ 4 / 4 := by positivity
      calc Brk * Cpw ^ 2 * ζv ^ 4 * wv ^ 2 * Rv ^ 4 / 4
          = Brk * (Cpw ^ 2 * ζv ^ 4 * wv ^ 2 * Rv ^ 4 / 4) := by ring
        _ ≤ (ω ^ 12 * R ^ 8) * (Cpw ^ 2 * ζv ^ 4 * wv ^ 2 * Rv ^ 4 / 4) :=
            mul_le_mul_of_nonneg_right hB12 hC
        _ = (Q / 2) ^ 2 := by rw [hQ]; ring
    have h0 : 0 ≤ Brk * Cpw ^ 2 * ζv ^ 4 * wv ^ 2 * Rv ^ 4 / 4 + X ^ (1 / (p : ℝ)) := by
      positivity
    have h1 : (2 * p - 1) * (Brk * Cpw ^ 2 * ζv ^ 4 * wv ^ 2 * Rv ^ 4 / 4 + X ^ (1 / (p : ℝ))) ≤
        (2 * p) * ((Q / 2) ^ 2 + ρ ^ 2) := by
      calc _ ≤ (2 * p) * (Brk * Cpw ^ 2 * ζv ^ 4 * wv ^ 2 * Rv ^ 4 / 4 + X ^ (1 / (p : ℝ))) :=
            mul_le_mul_of_nonneg_right (by linarith) h0
        _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hBk hX2) (by positivity)
    calc _ ≤ Real.sqrt ((2 * p) * ((Q / 2) ^ 2 + ρ ^ 2)) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt (2 * p) * Real.sqrt ((Q / 2) ^ 2 + ρ ^ 2) := Real.sqrt_mul (by positivity) _
      _ ≤ Real.sqrt (2 * p) * (Q / 2 + ρ) := by
          refine mul_le_mul_of_nonneg_left ?_ hsq0
          rw [Real.sqrt_le_left (by positivity)]
          nlinarith [mul_nonneg hQ0 hρ]
      _ = _ := by ring
  have hA : Src * Cpw * ζv ^ 2 * wv * Rv ^ 2 / 2 ≤ Q / 2 := by
    have hC : 0 ≤ Cpw * ζv ^ 2 * wv * Rv ^ 2 / 2 := by positivity
    calc Src * Cpw * ζv ^ 2 * wv * Rv ^ 2 / 2 = Src * (Cpw * ζv ^ 2 * wv * Rv ^ 2 / 2) := by ring
      _ ≤ (ω ^ 6 * R ^ 4) * (Cpw * ζv ^ 2 * wv * Rv ^ 2 / 2) := mul_le_mul_of_nonneg_right hSrc hC
      _ = Q / 2 := by rw [hQ]; ring
  have hI : ω * Cpw * Rv ^ 2 * ζv ^ 2 * wv ≤ Q := by
    have h1 : ω ≤ ω ^ 6 * R ^ 4 := by
      have h6 : ω ≤ ω ^ 6 := le_self_pow₀ hω (by norm_num)
      have h4 : 1 ≤ R ^ 4 := one_le_pow₀ hR1
      calc ω ≤ ω ^ 6 := h6
        _ = ω ^ 6 * 1 := (mul_one _).symm
        _ ≤ ω ^ 6 * R ^ 4 := mul_le_mul_of_nonneg_left h4 (by positivity)
    have h2 : 0 ≤ Cpw * Rv ^ 2 * ζv ^ 2 * wv := by positivity
    calc ω * Cpw * Rv ^ 2 * ζv ^ 2 * wv = ω * (Cpw * Rv ^ 2 * ζv ^ 2 * wv) := by ring
      _ ≤ (ω ^ 6 * R ^ 4) * (Cpw * Rv ^ 2 * ζv ^ 2 * wv) := mul_le_mul_of_nonneg_right h1 h2
      _ = Q := by rw [hQ]; ring
  have hQ6 : Q ≤ ω ^ 6 * R ^ 6 * Cpw * ζv ^ 2 * wv := by
    have h1 : Rv ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (by linarith) hRvR 2
    have h0 : 0 ≤ ω ^ 6 * R ^ 4 * Cpw * ζv ^ 2 * wv := by positivity
    calc Q = (ω ^ 6 * R ^ 4 * Cpw * ζv ^ 2 * wv) * Rv ^ 2 := by rw [hQ]
      _ ≤ (ω ^ 6 * R ^ 4 * Cpw * ζv ^ 2 * wv) * R ^ 2 := mul_le_mul_of_nonneg_left h1 h0
      _ = _ := by ring
  have h2p : 1 ≤ Real.sqrt (2 * p) := by rw [Real.one_le_sqrt]; linarith
  have hY0 : 0 ≤ ω ^ 6 * R ^ 6 * Cpw * ζv ^ 2 * wv := by positivity
  have hfin : (3 / 2 + Real.sqrt (2 * p) / 2) * Q ≤
      Cpw * (1 + Real.sqrt (2 * p)) * ω ^ 6 * R ^ 6 * ζv ^ 2 * wv := by
    have hc : 3 / 2 + Real.sqrt (2 * p) / 2 ≤ 1 + Real.sqrt (2 * p) := by linarith
    calc (3 / 2 + Real.sqrt (2 * p) / 2) * Q ≤ (1 + Real.sqrt (2 * p)) * Q :=
          mul_le_mul_of_nonneg_right hc hQ0
      _ ≤ (1 + Real.sqrt (2 * p)) * (ω ^ 6 * R ^ 6 * Cpw * ζv ^ 2 * wv) :=
          mul_le_mul_of_nonneg_left hQ6 (by positivity)
      _ = _ := by ring
  linarith [hB, hA, hI, hX1, hfin]

set_option maxHeartbeats 1000000 in
-- The final simplification of the moment bound is a long chain of real inequalities.
/-- The `2p`-th moment of the mixed pair at the terminal time of a step at fixed `W`:
`‖D₂(v; a, b)‖_{2p} ≤ C_pw(1 + √(2p)) ω⁶ R⁶ ζ_v² w_v + (2 + √(2p)) ρ`, from the propagated
pair estimate along the good events of probability `1 - 4δ₁`. -/
private theorem step2_pair_mom_atW (g E : ℝ) {W L : ℕ} (hW : 3 ≤ W) (hL : 3 ≤ L) (hg : 0 ≤ g)
    (hroot : IsDysonRootV (hopB g) (gammaG g) L E (mRoot g L E))
    {s t v : ℝ} (hs : 1 / 2 ≤ s) (hsv : s ≤ v) (hvt : v ≤ t) (ht1 : t < 1)
    {cw θ F₁ ω Λ C' Cc M N Cpw ρ C0 δ₁ : ℝ} (p : ℕ) (hp : 1 ≤ p)
    (hcw0 : 0 ≤ cw) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2) (hF₁ : 0 ≤ F₁)
    (hω : 64 ≤ ω) (hΛ : Λ = ω * ((1 - s) / (1 - t)) ^ M) (hM4 : 4 ≤ M)
    (hNM : 3 * M - 8 ≤ N) (hRN : ((1 - s) / (1 - t)) ^ N * zetaProp g W L t ≤ 1)
    (hC'0 : 0 ≤ C') (hC' : C' ≤ ω) (hCc0 : 0 ≤ Cc) (hCc : Cc ≤ ω)
    (hlH : Real.log W ^ (2 / θ) ≤ ω) (hCpw : 0 ≤ Cpw) (hρ : 0 ≤ ρ) (hδ₁ : 0 ≤ δ₁)
    (hLℓ : ∀ r ∈ Set.Icc s v, (L : ℝ) / ellProp g L r ≤ (W : ℝ) ^ C0)
    (hsm1 : 2 * Real.sqrt 2 * ω ^ 2 * ((1 - s) / (1 - t)) ^ 3 * (W : ℝ) ^ C0 *
      Real.sqrt (ω * ((1 - s) / (1 - t)) * ((C' + Λ) + ω * ((1 - s) / (1 - t)) *
        (ω ^ 2 + C' + Λ)) * (Real.exp (-(cw * Real.log W ^ (2 : ℝ))) + (W : ℝ) ^ (-F₁))) *
        (2 * W) ≤ 1)
    (hsm2 : (C' + Λ) * (Real.exp (-(cw * Real.log W ^ (2 : ℝ))) + (W : ℝ) ^ (-F₁)) *
      (W : ℝ) ^ C0 ≤ 1)
    (hsh : ∀ ℓ d : ℝ, 0 < ℓ → 0 ≤ d → d ≤ 2 * (ℓ * Real.log W ^ ((3 : ℝ) / 2)) →
      ω⁻¹ ≤ weightFn cw θ F₁ W ℓ d)
    (hconv : ∀ r ∈ Set.Icc s v, ∀ x y : Fin L,
      ∑ c, weightFn cw θ F₁ W (ellProp g L r) (cycDist x c) *
          weightFn cw θ F₁ W (ellProp g L r) (cycDist c y) ≤
        Cc * ellProp g L r * weightFn cw θ F₁ W (ellProp g L r) (cycDist x y) ∧
      ∑ c, Real.sqrt (weightFn cw θ F₁ W (ellProp g L r) (cycDist x c) *
          weightFn cw θ F₁ W (ellProp g L r) (cycDist c y)) ≤
        Cc * ellProp g L r * Real.sqrt (weightFn cw θ F₁ W (ellProp g L r) (cycDist x y)))
    (hprim : ∀ r ∈ Set.Icc s v, ∀ x y : Fin L,
      ellProp g L r * Real.log W ^ ((3 : ℝ) / 2) < cycDist x y →
      ‖primLoop g W L E (mRoot g L E) r ![x, y] ![true, false]‖ ≤
        C' * zetaProp g W L r ^ 2 * weightFn cw θ F₁ W (ellProp g L r) (cycDist x y))
    (hprop : ∀ a b : Fin L, ∀ r ∈ Set.Icc s v, ∑ l : Fin L × Fin L,
        step2Coef (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E (mRoot g L E))) v a b l r *
          weightFn cw θ F₁ W (ellProp g L r) (cycDist l.1 l.2) ≤
        Cpw * ((1 - r) / (1 - v)) ^ 2 * weightFn cw θ F₁ W (ellProp g L v) (cycDist a b))
    (hopP : ∀ r ∈ Set.Ioo s v, μ W L {x | ∃ l : Fin L × Fin L,
      ω * (W * ((1 - s) / (1 - t)) * zetaProp g W L r) <
        ‖((‖blockOf (flowG W ⟨g, E, L, r⟩ x) l.1 l.2‖ : ℝ) : ℂ)‖} ≤ ENNReal.ofReal δ₁)
    (hhsP : ∀ r ∈ Set.Ioo s v, μ W L {x | ∃ l : Fin L × Fin L,
      ω * ((W : ℝ) ^ 2 * ((1 - s) / (1 - t)) * zetaProp g W L r) <
        ‖((blockHS2 (flowG W ⟨g, E, L, r⟩ x) l.1 l.2 : ℝ) : ℂ)‖} ≤ ENNReal.ofReal δ₁)
    (havgP : ∀ r ∈ Set.Ioo s v, μ W L {x | ∃ c : Fin L,
      ω * (((1 - s) / (1 - t)) ^ 2 * zetaProp g W L r) <
        ‖blockTr (flowG W ⟨g, E, L, r⟩ x - flowM W ⟨g, E, L, r⟩) c c‖} ≤ ENNReal.ofReal δ₁)
    (hD2P : ∀ r ∈ Set.Ioo s v, μ W L {x | ∃ l : Fin L × Fin L, Λ * zetaProp g W L r ^ 2 *
        weightFn cw θ F₁ W (ellProp g L r) (cycDist l.1 l.2) <
      ‖flowErr W ⟨g, E, L, r⟩ ![l.1, l.2] ![true, false] x‖} ≤ ENNReal.ofReal δ₁)
    (hinP : μ W L {x | ∃ l : Fin L × Fin L, ω * (zetaProp g W L s ^ 2 *
        weightFn cw θ F₁ W (ellProp g L s) (cycDist l.1 l.2)) <
      ‖flowErr W ⟨g, E, L, s⟩ ![l.1, l.2] ![true, false] x‖} ≤ ENNReal.ofReal δ₁)
    {M₀ : ℝ}
    (hD : ∀ r ∈ Set.Icc s v, ∀ l : Fin L × Fin L,
      ∫ x, ‖flowErr W ⟨g, E, L, r⟩ ![l.1, l.2] ![true, false] x‖ ^ (2 * (2 * p)) ∂(μ W L) ≤ M₀)
    (hG : ∀ r ∈ Set.Ioo s v, ∀ l : Fin L × Fin L,
      ∫ x, ‖blockGen W L (gammaG g) (fun r N =>
          resLoop g E (mRoot g L E) ![l.1, l.2] ![true, false] r N -
            primLoop g W L E (mRoot g L E) r ![l.1, l.2] ![true, false]) r
          (flowH g W L r x)‖ ^ (2 * (2 * p)) ∂(μ W L) ≤ M₀)
    (hΓ : ∀ r ∈ Set.Ioo s v, ∀ l : Fin L × Fin L,
      Integrable (fun x => ‖blockGamma W L (gammaG g)
          (resLoop g E (mRoot g L E) ![l.1, l.2] ![true, false] r)
          (resLoop g E (mRoot g L E) ![l.1, l.2] ![true, false] r)
          (flowH g W L r x)‖ ^ (2 * p)) (μ W L) ∧
      ∫ x, ‖blockGamma W L (gammaG g)
          (resLoop g E (mRoot g L E) ![l.1, l.2] ![true, false] r)
          (resLoop g E (mRoot g L E) ![l.1, l.2] ![true, false] r)
          (flowH g W L r x)‖ ^ (2 * p) ∂(μ W L) ≤ M₀)
    (hrem1 : (Real.sqrt ((3 * ((1 - v) ^ 2)⁻¹) ^ (2 * (2 * p)) * M₀) * Real.sqrt (4 * δ₁)) ^
      (1 / (2 * (p : ℝ))) ≤ ρ)
    (hrem2 : (Real.sqrt ((3 * ((1 - v) ^ 2)⁻¹) ^ (2 * (2 * p)) * M₀) * Real.sqrt (4 * δ₁)) ^
      (1 / (p : ℝ)) ≤ ρ ^ 2)
    (a b : Fin L) :
    (∫ x, ‖flowErr W ⟨g, E, L, v⟩ ![a, b] ![true, false] x‖ ^ (2 * p) ∂(μ W L)) ^
        (1 / (2 * (p : ℝ))) ≤
      Cpw * (1 + Real.sqrt (2 * p)) * ω ^ 6 * ((1 - s) / (1 - t)) ^ 6 * zetaProp g W L v ^ 2 *
        weightFn cw θ F₁ W (ellProp g L v) (cycDist a b) + (2 + Real.sqrt (2 * p)) * ρ := by
  have hW1 : 1 ≤ W := by omega
  have hL1 : 1 ≤ L := by omega
  have hs0 : 0 ≤ s := by linarith
  have hv1 : v < 1 := lt_of_le_of_lt hvt ht1
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  set R := (1 - s) / (1 - t) with hRdef
  have h1t : 0 < 1 - t := by linarith
  have hR1 : 1 ≤ R := by rw [hRdef, le_div_iff₀ h1t]; linarith
  have hζt0 : 0 ≤ zetaProp g W L t := by
    have := (scale_facts g hg W L hW1 hL1 t t (by linarith) le_rfl ht1).2.2.2.1
    exact le_trans (by positivity) this
  have hζt1 : zetaProp g W L t ≤ 1 := by
    have h1 : 1 ≤ R ^ N := Real.one_le_rpow hR1 (by linarith)
    nlinarith
  obtain ⟨hRA, hA2, hA3, hA4, hA6⟩ := step2_num_A hR1 hM4 hNM hζt0 hRN
  have hΛ' : Λ = ω * (R ^ (M / 2)) ^ 2 := by rw [hA2]; exact hΛ
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ R) M; positivity
  have hlH0 : 0 ≤ Real.log W ^ (2 / θ) :=
    Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hW1)) _
  obtain ⟨hSrc, hBrk⟩ := step2_num_srcA hω hR1 hRA hΛ' hC'0 hC' hCc0 hCc hlH0 hlH hζt0 hA3 hA4 hA6
  set Src := step2Src ω R Λ C' Cc (Real.log W ^ (2 / θ)) (zetaProp g W L t) with hSrcdef
  set Brk := step2Brk ω R Λ C' Cc (Real.log W ^ (2 / θ)) (zetaProp g W L t) with hBrkdef
  have hSrc0 : 0 ≤ Src := by
    rw [hSrcdef]; unfold step2Src
    have : 0 ≤ C' + Λ := by linarith
    have : 0 ≤ max (ω ^ 2 * R) (Real.sqrt (C' + Λ)) := le_max_of_le_right (Real.sqrt_nonneg _)
    have : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have : (0:ℝ) ≤ ω := by linarith
    have : (0:ℝ) ≤ R := by linarith
    positivity
  have hBrk0 : 0 ≤ Brk := by
    rw [hBrkdef]; unfold step2Brk
    have : 0 ≤ C' + Λ := by linarith
    have : (0:ℝ) ≤ ω := by linarith
    have : (0:ℝ) ≤ R := by linarith
    positivity
  -- the good events
  set T : ℝ → Set (Ω W L) := fun r =>
    toMeasurable (μ W L) {x | ¬ step2Good W L g E r R ω Λ cw θ F₁ x} with hT
  set T0 : Set (Ω W L) := toMeasurable (μ W L) {x | ∃ l : Fin L × Fin L, ω *
      (zetaProp g W L s ^ 2 * weightFn cw θ F₁ W (ellProp g L s) (cycDist l.1 l.2)) <
    ‖flowErr W ⟨g, E, L, s⟩ ![l.1, l.2] ![true, false] x‖} with hT0
  have hTm : ∀ r, MeasurableSet (T r) := fun r => measurableSet_toMeasurable _ _
  have hTδ : ∀ r ∈ Set.Ioo s v, μ W L (T r) ≤ ENNReal.ofReal (4 * δ₁) := fun r hr => by
    rw [hT, measure_toMeasurable]
    exact step2_bad_measure g E W L r R ω Λ cw θ F₁ (hopP r hr) (hhsP r hr) (havgP r hr)
      (hD2P r hr)
  have hT0δ : μ W L T0 ≤ ENNReal.ofReal (4 * δ₁) := by
    rw [hT0, measure_toMeasurable]
    refine hinP.trans (ENNReal.ofReal_le_ofReal (by linarith))
  have hgoodT : ∀ r x, x ∉ T r → step2Good W L g E r R ω Λ cw θ F₁ x := fun r x hx => by
    by_contra h
    exact hx (subset_toMeasurable _ _ h)
  have hinit : ∀ x, x ∉ T0 → ∀ l : Fin L × Fin L,
      ‖flowErr W ⟨g, E, L, s⟩ ![l.1, l.2] ![true, false] x‖ ≤
        ω * zetaProp g W L s ^ 2 * weightFn cw θ F₁ W (ellProp g L s) (cycDist l.1 l.2) := by
    intro x hx l
    by_contra h
    push Not at h
    exact hx (subset_toMeasurable _ _ ⟨l, by linarith⟩)
  -- the rows
  have hsrc : ∀ r ∈ Set.Ioo s v, ∀ x, x ∉ T r → ∀ l : Fin L × Fin L, _ := fun r hr x hx l =>
    (step2_rows_of_good g E hW hL hg hroot (hs0.trans hr.1.le) (hr.2.le.trans hvt) ht1 hcw0 hθ
      hθ2 hF₁ (by linarith) hR1 hΛ0 hC'0 hCc0 hζt1 (hLℓ r ⟨hr.1.le, hr.2.le⟩) hsm1 hsm2 hsh
      (hconv r ⟨hr.1.le, hr.2.le⟩) (hprim r ⟨hr.1.le, hr.2.le⟩) x (hgoodT r x hx) l).1
  have hbrk : ∀ r ∈ Set.Ioo s v, ∀ x, x ∉ T r → ∀ l : Fin L × Fin L, _ := fun r hr x hx l =>
    (step2_rows_of_good g E hW hL hg hroot (hs0.trans hr.1.le) (hr.2.le.trans hvt) ht1 hcw0 hθ
      hθ2 hF₁ (by linarith) hR1 hΛ0 hC'0 hCc0 hζt1 (hLℓ r ⟨hr.1.le, hr.2.le⟩) hsm1 hsm2 hsh
      (hconv r ⟨hr.1.le, hr.2.le⟩) (hprim r ⟨hr.1.le, hr.2.le⟩) x (hgoodT r x hx) l).2
  -- the moments
  obtain ⟨hMA, hMB, hMI⟩ := step2_moments g E hW1 hL hroot hs0 hsv hv1 a b p hp hD hG hΓ
  have hM₀ : 0 ≤ M₀ := (integral_nonneg fun x => by positivity).trans (hD s ⟨le_rfl, hsv⟩ (a, b))
  set Mb := (3 * ((1 - v) ^ 2)⁻¹) ^ (2 * (2 * p)) * M₀ with hMb
  have hev : 0 < 1 - v := by linarith
  have hle3 : (((1 - v) ^ 2)⁻¹) ^ (2 * (2 * p)) * M₀ ≤ Mb := by
    rw [hMb]
    refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ _) hM₀
    have : 0 ≤ ((1 - v) ^ 2)⁻¹ := by positivity
    linarith
  have hζ0 : ∀ r ∈ Set.Icc s v, 0 ≤ zetaProp g W L r := fun r hr =>
    le_trans (by positivity)
      (scale_facts g hg W L hW1 hL1 r v (hs0.trans hr.1) hr.2 hv1).2.2.2.1
  have hζv : ∀ r ∈ Set.Icc s v, zetaProp g W L r ≤ zetaProp g W L v := fun r hr =>
    (scale_facts g hg W L hW1 hL1 r v (hs0.trans hr.1) hr.2 hv1).2.2.2.2.1
  have hcore := step2_pair_core g E hW1 hL hroot hs0 hsv hv1 a b p hp
    (fun r x y => weightFn cw θ F₁ W (ellProp g L r) (cycDist x y))
    (fun r x y => (step2_weight_pos cw θ F₁ hW1 _ _).le) (fun r => zetaProp g W L r) hζ0 hζv
    (Src := Src) (Brk := Brk) (I₁ := ω) hSrc0 hBrk0 (by linarith) (hprop a b) T hTm
    (by linarith : (0 : ℝ) ≤ 4 * δ₁) hTδ T0 (measurableSet_toMeasurable _ _) hT0δ hsrc hbrk hinit
    (MA := Mb) (MB := Mb) (MI := Mb) (fun r hr => (hMA r hr).trans le_rfl)
    (fun r hr => (hMB r hr).trans hle3) (hMI.trans hle3)
  refine hcore.trans (step2_final_simp (p := p) hp (by linarith) hR1 ?_ ?_ hCpw
    (hζ0 v ⟨hsv, le_rfl⟩) (step2_weight_pos cw θ F₁ hW1 _ _).le hρ hBrk0 hSrc hBrk hrem1 hrem2)
  · rw [le_div_iff₀ hev]; linarith
  · exact div_le_div_of_nonneg_left (by linarith) h1t (by linarith)

end Step2AtW3

section Step2Sample

/-- Markov's inequality at the sampled labels and the sampling inequality (5.34)
[fo:eq:weighted-sampling-input]: if `‖X_l‖_{2p} ≤ B w_l` with `w ≤ w_F`, then the maximum over
all labels of `‖X_l‖/w_{F,l}` exceeds `T ≥ C_s T₀ + δ` with probability at most
`η + |S| (B/T₀)^{2p}`. -/
private theorem step2_sample_markov {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] {Λ : Type*} [Fintype Λ] (X : Λ → Ω' → ℂ) (w wF : Λ → ℝ)
    (hw : ∀ l, 0 < w l) (hwF : ∀ l, w l ≤ wF l) (S₀ : Finset Λ) {Cs δ η B T₀ T : ℝ} (p : ℕ)
    (hp : 1 ≤ p) (hCs : 0 ≤ Cs) (hB : 0 ≤ B) (hT₀ : 0 < T₀)
    (hsb : SampleBound P X wF S₀ Cs δ η)
    (hint : ∀ l, Integrable (fun x => ‖X l x‖ ^ (2 * p)) P)
    (hmom : ∀ l, (∫ x, ‖X l x‖ ^ (2 * p) ∂P) ^ (1 / (2 * (p : ℝ))) ≤ B * w l)
    (hsmall : Cs * T₀ + δ ≤ T) :
    P {x | ∃ l, T * wF l < ‖X l x‖} ≤
      ENNReal.ofReal η + (S₀.card : ENNReal) * ENNReal.ofReal ((B / T₀) ^ (2 * p)) := by
  have hwF0 : ∀ l, 0 < wF l := fun l => lt_of_lt_of_le (hw l) (hwF l)
  set Bad := {x | ∃ l, Cs * (⨆ s : S₀, ‖X s x‖ / wF s) + δ < ‖X l x‖ / wF l} with hBad
  set E : Λ → Set Ω' := fun s => {x | T₀ * wF s < ‖X s x‖} with hE
  have hsub : {x | ∃ l, T * wF l < ‖X l x‖} ⊆ Bad ∪ ⋃ s ∈ S₀, E s := by
    rintro x ⟨l, hl⟩
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hcon
    obtain ⟨hnb, hns⟩ := hcon
    have hs : ∀ s ∈ S₀, ‖X s x‖ / wF s ≤ T₀ := by
      intro s hs
      have := hns s hs
      simp only [hE, Set.mem_ofPred_eq, not_lt] at this
      rw [div_le_iff₀ (hwF0 s)]; linarith
    have hsup : (⨆ s : S₀, ‖X s x‖ / wF s) ≤ T₀ :=
      Real.iSup_le (fun s => hs s s.2) hT₀.le
    have hnb' : ‖X l x‖ / wF l ≤ Cs * (⨆ s : S₀, ‖X s x‖ / wF s) + δ := by
      simp only [hBad, Set.mem_ofPred_eq, not_exists, not_lt] at hnb
      exact hnb l
    have h1 : ‖X l x‖ / wF l ≤ T := by
      have : Cs * (⨆ s : S₀, ‖X s x‖ / wF s) ≤ Cs * T₀ := mul_le_mul_of_nonneg_left hsup hCs
      linarith
    rw [div_le_iff₀ (hwF0 l)] at h1
    linarith
  have hEs : ∀ s, P (E s) ≤ ENNReal.ofReal ((B / T₀) ^ (2 * p)) := by
    intro s
    have hTs : 0 < T₀ * wF s := mul_pos hT₀ (hwF0 s)
    have hm := step2_markov P (fun x => ‖X s x‖) (fun x => norm_nonneg _) (2 * p) (hint s) hTs
    refine hm.trans (ENNReal.ofReal_le_ofReal ?_)
    have hI0 : 0 ≤ ∫ x, ‖X s x‖ ^ (2 * p) ∂P := integral_nonneg fun x => by positivity
    have hp0 : (0 : ℝ) < 2 * p := by
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    have hI : ∫ x, ‖X s x‖ ^ (2 * p) ∂P ≤ (B * w s) ^ (2 * p) := by
      have h1 := hmom s
      have h2 : ((∫ x, ‖X s x‖ ^ (2 * p) ∂P) ^ (1 / (2 * (p : ℝ)))) ^ ((2 * p : ℕ) : ℝ) =
          ∫ x, ‖X s x‖ ^ (2 * p) ∂P := by
        rw [← Real.rpow_mul hI0]
        have : 1 / (2 * (p : ℝ)) * ((2 * p : ℕ) : ℝ) = 1 := by
          push_cast; field_simp
        rw [this, Real.rpow_one]
      rw [← h2, Real.rpow_natCast]
      exact pow_le_pow_left₀ (by positivity) h1 _
    have hwle : B * w s ≤ B * wF s := mul_le_mul_of_nonneg_left (hwF s) hB
    calc (∫ x, ‖X s x‖ ^ (2 * p) ∂P) / (T₀ * wF s) ^ (2 * p)
        ≤ (B * w s) ^ (2 * p) / (T₀ * wF s) ^ (2 * p) := by gcongr
      _ = (B * w s / (T₀ * wF s)) ^ (2 * p) := by rw [div_pow]
      _ ≤ (B * wF s / (T₀ * wF s)) ^ (2 * p) := by
          have h0 : 0 ≤ B * w s / (T₀ * wF s) := div_nonneg (mul_nonneg hB (hw s).le) hTs.le
          exact pow_le_pow_left₀ h0 (div_le_div_of_nonneg_right hwle hTs.le) _
      _ = (B / T₀) ^ (2 * p) := by
          congr 1; field_simp [(hwF0 s).ne']
  calc P {x | ∃ l, T * wF l < ‖X l x‖} ≤ P (Bad ∪ ⋃ s ∈ S₀, E s) := measure_mono hsub
    _ ≤ P Bad + ∑ s ∈ S₀, P (E s) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_biUnion_finset_le _ _))
    _ ≤ ENNReal.ofReal η + ∑ _s ∈ S₀, ENNReal.ofReal ((B / T₀) ^ (2 * p)) := by
        gcongr with s hs
        · exact hsb
        · exact hEs s
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end Step2Sample

section Step2NumSm

/-- The smallness of the remainders of the near rows: with `ω ≤ W`, `R ≤ W³`, `C' ≤ W`,
`C' + Λ ≤ 2X`, `L/ℓ ≤ Y` and `ε_w ≤ 2/(W^{40} X Y²)`. -/
private theorem step2_num_sm {Wr ω R Λ C' X Y εw : ℝ} (hW : 4 ≤ Wr) (hω1 : 1 ≤ ω) (hωW : ω ≤ Wr)
    (hR1 : 1 ≤ R) (hRW : R ≤ Wr ^ 3) (hC'0 : 0 ≤ C') (hΛ0 : 0 ≤ Λ) (hC'W : C' ≤ Wr)
    (hCΛ : C' + Λ ≤ 2 * X) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hεw0 : 0 ≤ εw)
    (hεw : εw ≤ 2 / (Wr ^ 40 * X * Y ^ 2)) :
    2 * Real.sqrt 2 * ω ^ 2 * R ^ 3 * Y * Real.sqrt (ω * R * ((C' + Λ) + ω * R *
        (ω ^ 2 + C' + Λ)) * εw) * (2 * Wr) ≤ 1 ∧ (C' + Λ) * εw * Y ≤ 1 := by
  have hW0 : 0 < Wr := by linarith
  have hW1 : 1 ≤ Wr := by linarith
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hD : 0 < Wr ^ 40 * X * Y ^ 2 := by positivity
  constructor
  · -- the inner quantity
    have hin : ω * R * ((C' + Λ) + ω * R * (ω ^ 2 + C' + Λ)) ≤ 5 * Wr ^ 10 * X := by
      have hωR : ω * R ≤ Wr ^ 4 := by
        calc ω * R ≤ Wr * Wr ^ 3 := mul_le_mul hωW hRW (by linarith) hW0.le
          _ = Wr ^ 4 := by ring
      have hωR0 : 0 ≤ ω * R := by positivity
      have h2 : ω ^ 2 + C' + Λ ≤ Wr ^ 2 + 2 * X := by
        have : ω ^ 2 ≤ Wr ^ 2 := pow_le_pow_left₀ (by linarith) hωW 2
        linarith
      have h3 : (C' + Λ) + ω * R * (ω ^ 2 + C' + Λ) ≤ 2 * X + Wr ^ 4 * (Wr ^ 2 + 2 * X) := by
        have h0 : 0 ≤ ω ^ 2 + C' + Λ := by positivity
        have := mul_le_mul hωR h2 h0 (by positivity)
        linarith
      have h4 : 2 * X + Wr ^ 4 * (Wr ^ 2 + 2 * X) ≤ 5 * Wr ^ 6 * X := by
        have h41 : 1 ≤ Wr ^ 4 := one_le_pow₀ hW1
        have h61 : 1 ≤ Wr ^ 6 := one_le_pow₀ hW1
        have e : Wr ^ 4 * (Wr ^ 2 + 2 * X) = Wr ^ 6 + 2 * Wr ^ 4 * X := by ring
        have h46 : Wr ^ 4 ≤ Wr ^ 6 := pow_le_pow_right₀ hW1 (by norm_num)
        nlinarith
      have h0 : 0 ≤ (C' + Λ) + ω * R * (ω ^ 2 + C' + Λ) := by positivity
      calc ω * R * ((C' + Λ) + ω * R * (ω ^ 2 + C' + Λ))
          ≤ Wr ^ 4 * (5 * Wr ^ 6 * X) := mul_le_mul hωR (h3.trans h4) h0 (by positivity)
        _ = 5 * Wr ^ 10 * X := by ring
    have hin2 : ω * R * ((C' + Λ) + ω * R * (ω ^ 2 + C' + Λ)) * εw ≤ 10 / (Wr ^ 30 * Y ^ 2) := by
      have h0 : 0 ≤ ω * R * ((C' + Λ) + ω * R * (ω ^ 2 + C' + Λ)) := by positivity
      calc ω * R * ((C' + Λ) + ω * R * (ω ^ 2 + C' + Λ)) * εw
          ≤ 5 * Wr ^ 10 * X * (2 / (Wr ^ 40 * X * Y ^ 2)) := mul_le_mul hin hεw hεw0 (by positivity)
        _ = 10 / (Wr ^ 30 * Y ^ 2) := by field_simp; ring
    have hsq : Real.sqrt (ω * R * ((C' + Λ) + ω * R * (ω ^ 2 + C' + Λ)) * εw) ≤
        4 / (Wr ^ 15 * Y) := by
      rw [Real.sqrt_le_left (by positivity)]
      calc _ ≤ 10 / (Wr ^ 30 * Y ^ 2) := hin2
        _ ≤ (4 / (Wr ^ 15 * Y)) ^ 2 := by
            rw [div_pow, mul_pow, ← pow_mul]
            gcongr; norm_num
    have hpre : 2 * Real.sqrt 2 * ω ^ 2 * R ^ 3 * Y * (2 * Wr) ≤ 6 * Wr ^ 12 * Y := by
      have hs2 : Real.sqrt 2 ≤ 3 / 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
      have h1 : ω ^ 2 ≤ Wr ^ 2 := pow_le_pow_left₀ (by linarith) hωW 2
      have h2 : R ^ 3 ≤ (Wr ^ 3) ^ 3 := pow_le_pow_left₀ (by linarith) hRW 3
      have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
      calc 2 * Real.sqrt 2 * ω ^ 2 * R ^ 3 * Y * (2 * Wr)
          ≤ 2 * (3 / 2) * Wr ^ 2 * (Wr ^ 3) ^ 3 * Y * (2 * Wr) := by gcongr
        _ = 6 * Wr ^ 12 * Y := by ring
    have hpre0 : 0 ≤ 2 * Real.sqrt 2 * ω ^ 2 * R ^ 3 * Y := by positivity
    calc 2 * Real.sqrt 2 * ω ^ 2 * R ^ 3 * Y * Real.sqrt (ω * R * ((C' + Λ) + ω * R *
          (ω ^ 2 + C' + Λ)) * εw) * (2 * Wr)
        = (2 * Real.sqrt 2 * ω ^ 2 * R ^ 3 * Y * (2 * Wr)) * Real.sqrt (ω * R * ((C' + Λ) +
            ω * R * (ω ^ 2 + C' + Λ)) * εw) := by ring
      _ ≤ (6 * Wr ^ 12 * Y) * (4 / (Wr ^ 15 * Y)) :=
          mul_le_mul hpre hsq (Real.sqrt_nonneg _) (by positivity)
      _ = 24 / Wr ^ 3 := by field_simp; ring
      _ ≤ 1 := by
          rw [div_le_one (by positivity)]
          nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hW 3]
  · calc (C' + Λ) * εw * Y ≤ 2 * X * (2 / (Wr ^ 40 * X * Y ^ 2)) * Y := by gcongr
      _ = 4 / (Wr ^ 40 * Y) := by field_simp; ring
      _ ≤ 1 := by
          rw [div_le_one (by positivity)]
          have : 4 ≤ Wr ^ 40 := le_trans hW (le_self_pow₀ hW1 (by norm_num))
          nlinarith

end Step2NumSm

section Step2NumRem

/-- `W^x W^y = W^{x+y}` for `W > 0` (real exponents). -/
private theorem step2_rpow_add' {W : ℝ} (hW : 0 < W) (x y : ℝ) : W ^ x * W ^ y = W ^ (x + y) :=
  (Real.rpow_add hW x y).symm

/-- The remainder of the moment bound: with `1 - v ≥ W^{-3}`, `M₀ ≤ K₀ W^{E}`,
`δ₁ = W^{-D'}`, `D' = 32p + E + 4pF₁ + 2` and `2(3^{4p}K₀)^{1/2} 4^{2p} ≤ W`:
`(Mb)^{1/2} (4δ₁)^{1/2} ≤ ρ^{2p}`, `Mb = (3(1 - v)⁻²)^{4p} M₀`, `ρ = (4W²)⁻¹ W^{-F₁}`. -/
private theorem step2_num_rem {W : ℕ} (hW : 1 ≤ W) {v M₀ K₀ E F₁ : ℝ} (p : ℕ)
    (hv : (W : ℝ) ^ (-3 : ℝ) ≤ 1 - v) (hM₀0 : 0 ≤ M₀) (hK₀ : 0 ≤ K₀)
    (hM₀ : M₀ ≤ K₀ * (W : ℝ) ^ E)
    (hbig : 2 * Real.sqrt (3 ^ (4 * p) * K₀) * 4 ^ (2 * p) ≤ W) :
    Real.sqrt ((3 * ((1 - v) ^ 2)⁻¹) ^ (2 * (2 * p)) * M₀) *
        Real.sqrt (4 * (W : ℝ) ^ (-(32 * p + E + 4 * p * F₁ + 2))) ≤
      ((4 * (W : ℝ) ^ 2)⁻¹ * (W : ℝ) ^ (-F₁)) ^ (2 * p) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hv0 : 0 < 1 - v := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) hv
  -- `(1 - v)⁻² ≤ W⁶`
  have hinv : ((1 - v) ^ 2)⁻¹ ≤ (W : ℝ) ^ 6 := by
    have h3 : (W : ℝ) ^ (-3 : ℝ) = ((W : ℝ) ^ 3)⁻¹ := by
      rw [Real.rpow_neg hW0.le]; norm_cast
    rw [h3] at hv
    have h1 : (1 - v)⁻¹ ≤ (W : ℝ) ^ 3 := by
      rw [inv_le_comm₀ hv0 (by positivity)]; exact hv
    rw [← inv_pow, show (W : ℝ) ^ 6 = ((W : ℝ) ^ 3) ^ 2 by ring]
    exact pow_le_pow_left₀ (by positivity) h1 2
  set G := (W : ℝ) ^ (-(4 * p + 2 * p * F₁ : ℝ)) with hG
  have hG0 : 0 < G := Real.rpow_pos_of_pos hW0 _
  set D' := (32 * p + E + 4 * p * F₁ + 2 : ℝ) with hD'
  -- the product under the root
  have hprod : (3 * ((1 - v) ^ 2)⁻¹) ^ (2 * (2 * p)) * M₀ * (4 * (W : ℝ) ^ (-D')) ≤
      (2 * Real.sqrt (3 ^ (4 * p) * K₀) * (W : ℝ)⁻¹ * G) ^ 2 := by
    have h1 : (3 * ((1 - v) ^ 2)⁻¹) ^ (2 * (2 * p)) ≤ 3 ^ (4 * p) * (W : ℝ) ^ (24 * p) := by
      calc (3 * ((1 - v) ^ 2)⁻¹) ^ (2 * (2 * p)) = 3 ^ (4 * p) * (((1 - v) ^ 2)⁻¹) ^ (4 * p) := by
            rw [show 2 * (2 * p) = 4 * p by ring, mul_pow]
        _ ≤ 3 ^ (4 * p) * ((W : ℝ) ^ 6) ^ (4 * p) := by
            gcongr
        _ = 3 ^ (4 * p) * (W : ℝ) ^ (24 * p) := by rw [← pow_mul]; ring_nf
    have h2 : (3 * ((1 - v) ^ 2)⁻¹) ^ (2 * (2 * p)) * M₀ ≤
        3 ^ (4 * p) * K₀ * ((W : ℝ) ^ (24 * p) * (W : ℝ) ^ E) := by
      calc _ ≤ 3 ^ (4 * p) * (W : ℝ) ^ (24 * p) * (K₀ * (W : ℝ) ^ E) :=
            mul_le_mul h1 hM₀ hM₀0 (by positivity)
        _ = _ := by ring
    have h3 : (W : ℝ) ^ (24 * p) * (W : ℝ) ^ E * (W : ℝ) ^ (-D') = (W : ℝ) ^ (-2 : ℝ) * G ^ 2 := by
      rw [← Real.rpow_natCast, step2_rpow_add' hW0, step2_rpow_add' hW0, hG,
        ← Real.rpow_natCast _ 2, ← Real.rpow_mul hW0.le, step2_rpow_add' hW0, hD']
      congr 1
      push_cast; ring
    have h4 : (2 * Real.sqrt (3 ^ (4 * p) * K₀) * (W : ℝ)⁻¹ * G) ^ 2 =
        4 * (3 ^ (4 * p) * K₀) * ((W : ℝ) ^ (-2 : ℝ) * G ^ 2) := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      have : ((W : ℝ)⁻¹) ^ 2 = (W : ℝ) ^ (-2 : ℝ) := by
        rw [Real.rpow_neg hW0.le, Real.rpow_two, inv_pow]
      rw [this]; ring
    rw [h4]
    calc (3 * ((1 - v) ^ 2)⁻¹) ^ (2 * (2 * p)) * M₀ * (4 * (W : ℝ) ^ (-D'))
        ≤ 3 ^ (4 * p) * K₀ * ((W : ℝ) ^ (24 * p) * (W : ℝ) ^ E) * (4 * (W : ℝ) ^ (-D')) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = 4 * (3 ^ (4 * p) * K₀) * ((W : ℝ) ^ (24 * p) * (W : ℝ) ^ E * (W : ℝ) ^ (-D')) := by ring
      _ = _ := by rw [h3]
  have hrhs : ((4 * (W : ℝ) ^ 2)⁻¹ * (W : ℝ) ^ (-F₁)) ^ (2 * p) = (4 ^ (2 * p))⁻¹ * G := by
    have e : (4 * (W : ℝ) ^ 2)⁻¹ * (W : ℝ) ^ (-F₁) = 4⁻¹ * (W : ℝ) ^ (-2 - F₁ : ℝ) := by
      rw [mul_inv, show (-2 - F₁ : ℝ) = -2 + -F₁ by ring, ← step2_rpow_add' hW0,
        Real.rpow_neg hW0.le 2, Real.rpow_two]
      ring
    rw [e, mul_pow, inv_pow, ← Real.rpow_natCast ((W : ℝ) ^ (-2 - F₁ : ℝ)),
      ← Real.rpow_mul hW0.le, hG]
    congr 2
    push_cast; ring
  have hlhs : Real.sqrt ((3 * ((1 - v) ^ 2)⁻¹) ^ (2 * (2 * p)) * M₀) *
      Real.sqrt (4 * (W : ℝ) ^ (-D')) ≤ 2 * Real.sqrt (3 ^ (4 * p) * K₀) * (W : ℝ)⁻¹ * G := by
    rw [← Real.sqrt_mul (by positivity)]
    calc _ ≤ Real.sqrt ((2 * Real.sqrt (3 ^ (4 * p) * K₀) * (W : ℝ)⁻¹ * G) ^ 2) :=
          Real.sqrt_le_sqrt hprod
      _ = _ := Real.sqrt_sq (by positivity)
  rw [hrhs]
  refine hlhs.trans ?_
  have h4 : (0 : ℝ) < 4 ^ (2 * p) := by positivity
  rw [mul_comm _ G, mul_comm _ G]
  refine mul_le_mul_of_nonneg_left ?_ hG0.le
  have e : 2 * Real.sqrt (3 ^ (4 * p) * K₀) * (W : ℝ)⁻¹ =
      (2 * Real.sqrt (3 ^ (4 * p) * K₀) * 4 ^ (2 * p)) * ((W : ℝ)⁻¹ * (4 ^ (2 * p))⁻¹) := by
    field_simp
  rw [e]
  calc (2 * Real.sqrt (3 ^ (4 * p) * K₀) * 4 ^ (2 * p)) * ((W : ℝ)⁻¹ * (4 ^ (2 * p))⁻¹)
      ≤ (W : ℝ) * ((W : ℝ)⁻¹ * (4 ^ (2 * p))⁻¹) := mul_le_mul_of_nonneg_right hbig (by positivity)
    _ = (4 ^ (2 * p))⁻¹ := by field_simp

end Step2NumRem

section Step2PairPrec

/-- `2 W^{-(D+1)} ≤ W^{-D}` for `W ≥ 2`. -/
private theorem step2_two (W : ℕ) (hW : 2 ≤ W) (D : ℝ) :
    ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) ≤
      ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hW2 : (2 : ℝ) ≤ W := by exact_mod_cast hW
  rw [← ENNReal.ofReal_add (Real.rpow_nonneg hW0.le _) (Real.rpow_nonneg hW0.le _)]
  apply ENNReal.ofReal_le_ofReal
  have e : (W : ℝ) ^ (-(D + 1)) = (W : ℝ) ^ (-D) * (W : ℝ)⁻¹ := by
    rw [show -(D + 1) = -D + (-1) by ring, Real.rpow_add hW0, Real.rpow_neg_one]
  have hpos : 0 < (W : ℝ) ^ (-D) := Real.rpow_pos_of_pos hW0 _
  have hinv : (W : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hW2
  rw [e]; nlinarith

/-- The final count: `|S| (B/T₀)^{2p} ≤ W^{-(D+1)}` from `B/T₀ ≤ W^{-ε/8}`, `|S| ≤ W^{C}` and
`εp/4 ≥ D + C + 2`. -/
private theorem step2_num_count {W : ℕ} (hW : 1 ≤ W) {n x ε C D : ℝ} (p : ℕ) (hn0 : 0 ≤ n)
    (hn : n ≤ (W : ℝ) ^ C) (hx0 : 0 ≤ x) (hx : x ≤ (W : ℝ) ^ (-(ε / 8)))
    (hp : D + C + 2 ≤ ε * p / 4) :
    n * x ^ (2 * p) ≤ (W : ℝ) ^ (-(D + 1)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have h1 : x ^ (2 * p) ≤ (W : ℝ) ^ (-(ε / 8) * ((2 * p : ℕ) : ℝ)) := by
    rw [Real.rpow_mul hW0.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ hx0 hx _
  calc n * x ^ (2 * p) ≤ (W : ℝ) ^ C * (W : ℝ) ^ (-(ε / 8) * ((2 * p : ℕ) : ℝ)) :=
        mul_le_mul hn h1 (by positivity) (by positivity)
    _ = (W : ℝ) ^ (C + -(ε / 8) * ((2 * p : ℕ) : ℝ)) := (Real.rpow_add hW0 _ _).symm
    _ ≤ (W : ℝ) ^ (-(D + 1)) := by
        apply Real.rpow_le_rpow_of_exponent_le hW1
        push_cast
        nlinarith

end Step2PairPrec

section Step2PairConclude

/-- `Cw T₀ + W^{-4} ≤ T` for `T₀ = eAζ²`, `T = e²Aζ²`, `e ≥ Cw + 1`, `A ≥ 1`, `ζ² ≥ (4W²)⁻¹`. -/
private theorem step2_num_small {Wr Cw e A z : ℝ} (hW : 4 ≤ Wr) (hCw : 0 ≤ Cw) (he : Cw + 1 ≤ e)
    (hA : 1 ≤ A) (hz : (4 * Wr ^ 2)⁻¹ ≤ z) :
    Cw * (e * A * z) + Wr ^ (-(4 : ℝ)) ≤ e * e * A * z := by
  have hW0 : 0 < Wr := by linarith
  have he1 : 1 ≤ e := by linarith
  have hz0 : 0 < z := lt_of_lt_of_le (by positivity) hz
  have h4 : Wr ^ (-(4 : ℝ)) ≤ (4 * Wr ^ 2)⁻¹ := by
    have e4 : Wr ^ (4 : ℝ) = Wr ^ (4 : ℕ) := by norm_cast
    rw [Real.rpow_neg hW0.le, e4]
    apply inv_anti₀ (by positivity)
    have h16 : (16 : ℝ) ≤ Wr ^ 2 := by nlinarith
    have : Wr ^ 4 = Wr ^ 2 * Wr ^ 2 := by ring
    rw [this]
    have h2 : (0 : ℝ) ≤ Wr ^ 2 := by positivity
    nlinarith
  have h5 : (4 * Wr ^ 2)⁻¹ ≤ e * A * z := by
    calc (4 * Wr ^ 2)⁻¹ ≤ z := hz
      _ = 1 * 1 * z := by ring
      _ ≤ e * A * z := by gcongr
  have h0 : 0 ≤ e * A * z := by positivity
  have h6 : Cw * (e * A * z) + e * A * z ≤ e * e * A * z := by
    have : (Cw + 1) * (e * A * z) ≤ e * (e * A * z) := mul_le_mul_of_nonneg_right he h0
    linarith
  linarith

/-- The ratio `B/T₀ ≤ W^{-ε₁/8}` of the moment constant to the sampled threshold. -/
private theorem step2_num_ratio {Wr Cpw ω Rr z sp ε₁ : ℝ} (hW : 1 ≤ Wr) (hCpw : 0 ≤ Cpw)
    (hω1 : 1 ≤ ω)
    (hR1 : 1 ≤ Rr) (hz : 0 < z) (hsp : 0 ≤ sp) (hω6 : ω ^ 6 = Wr ^ (ε₁ / 4))
    (hfin : Cpw * (1 + sp) + 2 + sp ≤ Wr ^ (ε₁ / 8)) :
    (Cpw * (1 + sp) * ω ^ 6 * Rr ^ 6 + (2 + sp)) * z ^ 2 / (Wr ^ (ε₁ / 2) * Rr ^ 6 * z ^ 2) ≤
      Wr ^ (-(ε₁ / 8)) := by
  have hW0 : 0 < Wr := by linarith
  have hR6 : 1 ≤ Rr ^ 6 := one_le_pow₀ hR1
  have hω6' : 1 ≤ ω ^ 6 := one_le_pow₀ hω1
  have hT₀ : 0 < Wr ^ (ε₁ / 2) * Rr ^ 6 * z ^ 2 := by positivity
  rw [div_le_iff₀ hT₀]
  have h1 : Cpw * (1 + sp) * ω ^ 6 * Rr ^ 6 + (2 + sp) ≤
      (Cpw * (1 + sp) + 2 + sp) * (ω ^ 6 * Rr ^ 6) := by
    have h11 : 1 ≤ ω ^ 6 * Rr ^ 6 := one_le_mul_of_one_le_of_one_le hω6' hR6
    have h0 : 0 ≤ 2 + sp := by linarith
    calc Cpw * (1 + sp) * ω ^ 6 * Rr ^ 6 + (2 + sp) =
        Cpw * (1 + sp) * (ω ^ 6 * Rr ^ 6) + (2 + sp) * 1 := by ring
      _ ≤ Cpw * (1 + sp) * (ω ^ 6 * Rr ^ 6) + (2 + sp) * (ω ^ 6 * Rr ^ 6) := by gcongr
      _ = _ := by ring
  have e : Wr ^ (ε₁ / 8) * Wr ^ (ε₁ / 4) = Wr ^ (-(ε₁ / 8)) * Wr ^ (ε₁ / 2) := by
    rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]; ring_nf
  calc (Cpw * (1 + sp) * ω ^ 6 * Rr ^ 6 + (2 + sp)) * z ^ 2
      ≤ (Cpw * (1 + sp) + 2 + sp) * (ω ^ 6 * Rr ^ 6) * z ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ Wr ^ (ε₁ / 8) * (ω ^ 6 * Rr ^ 6) * z ^ 2 := by gcongr
    _ = (Wr ^ (ε₁ / 8) * Wr ^ (ε₁ / 4)) * (Rr ^ 6 * z ^ 2) := by rw [hω6]; ring
    _ = Wr ^ (-(ε₁ / 8)) * (Wr ^ (ε₁ / 2) * Rr ^ 6 * z ^ 2) := by rw [e]; ring

set_option maxHeartbeats 1000000 in
-- A long instantiation of the sampling and Markov bound.
/-- The conclusion of the pair estimate at a fixed `W` and a fixed step point, from the moment
bound at every pair, Markov's inequality, the weighted sampling (5.34)
[fo:eq:weighted-sampling-input] and the counting. -/
private theorem step2_pair_conclude {W L : ℕ} (hW : 4 ≤ W) (g E v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1)
    (hL : 3 ≤ L) (hroot : IsDysonRootV (hopB g) (gammaG g) L E (mRoot g L E))
    {cw θ F F₁ Cw Cpw ω Rr ρ ε ε₁ D CS' : ℝ} (p : ℕ) (hp : 1 ≤ p)
    (hFF₁ : F ≤ F₁) (hCw0 : 0 ≤ Cw) (hCpw0 : 0 ≤ Cpw) (hω1 : 1 ≤ ω) (hR1 : 1 ≤ Rr)
    (hε₁ε : ε₁ ≤ ε)
    (hζv : (2 * (W : ℝ))⁻¹ ≤ zetaProp g W L v)
    (hρ : ρ = (4 * (W : ℝ) ^ 2)⁻¹ * (W : ℝ) ^ (-F₁))
    (hω6 : ω ^ 6 = (W : ℝ) ^ (ε₁ / 4))
    (hcwW : Cw + 1 ≤ (W : ℝ) ^ (ε₁ / 2))
    (hfin : Cpw * (1 + Real.sqrt (2 * p)) + 2 + Real.sqrt (2 * p) ≤ (W : ℝ) ^ (ε₁ / 8))
    (S₀ : Finset (Fin L × Fin L)) (hcard : ((S₀.card : ℕ) : ℝ) ≤ (W : ℝ) ^ CS')
    (hpε : D + CS' + 2 ≤ ε₁ * p / 4)
    (hsb : SampleBound (μ W L)
      (fun ab ω => flowErr W ⟨g, E, L, v⟩ ![ab.1, ab.2] ![true, false] ω)
      (fun ab => weightFn cw θ F W (ellProp g L v) (cycDist ab.1 ab.2)) S₀ Cw
      ((W : ℝ) ^ (-(4 : ℝ))) ((W : ℝ) ^ (-(D + 1))))
    (hmom : ∀ a b : Fin L,
      (∫ x, ‖flowErr W ⟨g, E, L, v⟩ ![a, b] ![true, false] x‖ ^ (2 * p) ∂(μ W L)) ^
          (1 / (2 * (p : ℝ))) ≤
        Cpw * (1 + Real.sqrt (2 * p)) * ω ^ 6 * Rr ^ 6 * zetaProp g W L v ^ 2 *
          weightFn cw θ F₁ W (ellProp g L v) (cycDist a b) + (2 + Real.sqrt (2 * p)) * ρ) :
    μ W L {x | ∃ ab : Fin L × Fin L, (W : ℝ) ^ ε * (Rr ^ 6 * zetaProp g W L v ^ 2 *
        weightFn cw θ F W (ellProp g L v) (cycDist ab.1 ab.2)) <
      ‖flowErr W ⟨g, E, L, v⟩ ![ab.1, ab.2] ![true, false] x‖} ≤
      ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  have hW1 : 1 ≤ W := by omega
  have hW2 : 2 ≤ W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW4r : (4 : ℝ) ≤ W := by exact_mod_cast hW
  set ζv := zetaProp g W L v with hζvdef
  have hζv0 : 0 < ζv := lt_of_lt_of_le (by positivity) hζv
  have hζv2 : (4 * (W : ℝ) ^ 2)⁻¹ ≤ ζv ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hζv 2
    calc (4 * (W : ℝ) ^ 2)⁻¹ = ((2 * (W : ℝ))⁻¹) ^ 2 := by ring
      _ ≤ ζv ^ 2 := this
  have hsq0 : 0 ≤ Real.sqrt (2 * p) := Real.sqrt_nonneg _
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  set B := (Cpw * (1 + Real.sqrt (2 * p)) * ω ^ 6 * Rr ^ 6 + (2 + Real.sqrt (2 * p))) * ζv ^ 2
    with hBdef
  have hB0 : 0 ≤ B := by
    have : 0 ≤ Rr := by linarith
    have : 0 ≤ ω := by linarith
    positivity
  set T₀ := (W : ℝ) ^ (ε₁ / 2) * Rr ^ 6 * ζv ^ 2 with hT₀def
  have hT₀0 : 0 < T₀ := by
    have : 0 < Rr := by linarith
    positivity
  set T := (W : ℝ) ^ ε₁ * Rr ^ 6 * ζv ^ 2 with hTdef
  have hmom' : ∀ l : Fin L × Fin L,
      (∫ x, ‖flowErr W ⟨g, E, L, v⟩ ![l.1, l.2] ![true, false] x‖ ^ (2 * p) ∂(μ W L)) ^
        (1 / (2 * (p : ℝ))) ≤ B * weightFn cw θ F₁ W (ellProp g L v) (cycDist l.1 l.2) := by
    intro l
    refine (hmom l.1 l.2).trans ?_
    have hwge := step2_weight_ge cw θ F₁ (W := W) (ellProp g L v) (cycDist l.1 l.2)
    have hρw : ρ ≤ ζv ^ 2 * weightFn cw θ F₁ W (ellProp g L v) (cycDist l.1 l.2) := by
      rw [hρ]
      exact mul_le_mul hζv2 hwge (by positivity) (by positivity)
    have h2 : (2 + Real.sqrt (2 * p)) * ρ ≤
        (2 + Real.sqrt (2 * p)) * (ζv ^ 2 * weightFn cw θ F₁ W (ellProp g L v) (cycDist l.1 l.2)) :=
      mul_le_mul_of_nonneg_left hρw (by positivity)
    rw [hBdef]
    linarith only [h2]
  have hcls : ∀ l : Fin L × Fin L, HeatClass (fun r x => pairErrField g E (mRoot g L E) W L r x l)
      (-1 / 2) ((1 + v) / 2) := fun l =>
    heatClass_pairErrField g E (mRoot g L E) W L hW1 hL hroot l (by norm_num) (by linarith)
  have hint : ∀ l : Fin L × Fin L,
      Integrable (fun x => ‖flowErr W ⟨g, E, L, v⟩ ![l.1, l.2] ![true, false] x‖ ^ (2 * p))
        (μ W L) := by
    intro l
    obtain ⟨-, hc2, ⟨CY, hCY⟩, -, -⟩ := step2_class_jet (hcls l)
      (⟨by linarith, by linarith⟩ : v ∈ Set.Ioo (-1 / 2 : ℝ) ((1 + v) / 2)) (gammaG g / W)
    have e : (fun x => ‖flowErr W ⟨g, E, L, v⟩ ![l.1, l.2] ![true, false] x‖ ^ (2 * p)) =
        fun x => ‖pairErrField g E (mRoot g L E) W L v (Real.sqrt (v * (gammaG g / W)) • x) l‖ ^
          (2 * p) := by
      funext x; rw [step2_flowErr_eq g E W L hv0 l x]
    rw [e]
    exact step2_int_pow (continuous_norm.comp (hc2.continuous.comp (continuous_const_smul _)))
      (fun _ => norm_nonneg _) (fun x => hCY _) _
  have hsmall : Cw * T₀ + (W : ℝ) ^ (-(4 : ℝ)) ≤ T := by
    have hsplit : (W : ℝ) ^ ε₁ = (W : ℝ) ^ (ε₁ / 2) * (W : ℝ) ^ (ε₁ / 2) := by
      rw [← Real.rpow_add hW0]; ring_nf
    rw [hTdef, hT₀def, hsplit]
    exact step2_num_small hW4r hCw0 hcwW (one_le_pow₀ hR1) hζv2
  have hmk := step2_sample_markov (μ W L) (Λ := Fin L × Fin L)
    (fun (l : Fin L × Fin L) (x : Ω W L) => flowErr W ⟨g, E, L, v⟩ ![l.1, l.2] ![true, false] x)
    (fun (l : Fin L × Fin L) => weightFn cw θ F₁ W (ellProp g L v) (cycDist l.1 l.2))
    (fun (l : Fin L × Fin L) => weightFn cw θ F W (ellProp g L v) (cycDist l.1 l.2))
    (fun l => step2_weight_pos cw θ F₁ hW1 _ _)
    (fun l => step2_weight_anti_F hFF₁ hW1 _ _) S₀ p hp hCw0 hB0 hT₀0 hsb hint hmom' hsmall
  have hratio : B / T₀ ≤ (W : ℝ) ^ (-(ε₁ / 8)) :=
    step2_num_ratio hW1r hCpw0 hω1 hR1 hζv0 hsq0 hω6 hfin
  have hcnt := step2_num_count hW1 p (Nat.cast_nonneg _) hcard (div_nonneg hB0 hT₀0.le) hratio hpε
  have hsub : {x : Ω W L | ∃ ab : Fin L × Fin L, (W : ℝ) ^ ε * (Rr ^ 6 * ζv ^ 2 *
      weightFn cw θ F W (ellProp g L v) (cycDist ab.1 ab.2)) <
      ‖flowErr W ⟨g, E, L, v⟩ ![ab.1, ab.2] ![true, false] x‖} ⊆
      {x | ∃ l : Fin L × Fin L, T * weightFn cw θ F W (ellProp g L v) (cycDist l.1 l.2) <
        ‖flowErr W ⟨g, E, L, v⟩ ![l.1, l.2] ![true, false] x‖} := by
    rintro x ⟨l, hl⟩
    refine ⟨l, lt_of_le_of_lt ?_ hl⟩
    have hWε : (W : ℝ) ^ ε₁ ≤ (W : ℝ) ^ ε := Real.rpow_le_rpow_of_exponent_le hW1r hε₁ε
    have h0 : 0 ≤ Rr ^ 6 * ζv ^ 2 * weightFn cw θ F W (ellProp g L v) (cycDist l.1 l.2) :=
      mul_nonneg (by positivity) (step2_weight_pos cw θ F hW1 _ _).le
    calc T * weightFn cw θ F W (ellProp g L v) (cycDist l.1 l.2) =
        (W : ℝ) ^ ε₁ * (Rr ^ 6 * ζv ^ 2 * weightFn cw θ F W (ellProp g L v) (cycDist l.1 l.2)) := by
          rw [hTdef]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hWε h0
  refine (measure_mono hsub).trans (hmk.trans ?_)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  exact le_trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hcnt)) (step2_two W hW2 D)

end Step2PairConclude

section Step2PairMain

open scoped Matrix.Norms.L2Operator

set_option maxHeartbeats 4000000 in
-- The thresholds in `W` and the instantiation of the fixed-`W` estimate are long.
/-- The propagated mixed-pair estimate of Step 2 with loss `R^6`: the mixed-pair bound at the
intermediate times, the Step 1 envelopes, the input at the start, the moment comparison for the
propagated pair, Markov's inequality and the weighted sampling (5.34)
[fo:eq:weighted-sampling-input]. -/
private theorem step2_pair (R : PropRegime) (I : PropInputs R.base R.J) (c cp θ N : ℝ) (hc : 0 < c)
    (hcp : 0 < cp) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2) (hN : lemmaNN0 I.Cw ≤ N) :
    ∃ cp₂ : ℝ, 0 < cp₂ ∧ cp₂ ≤ cp ∧ cp₂ ≤ 1 ∧ ∀ S : ℕ → Set StepPt,
      (∀ W, S W ⊆ {q | StepAdm R c N W q}) →
      (∀ W, ∀ q ∈ S W, ∀ v : ℝ, q.s ≤ v → v ≤ q.u →
        (⟨q.g, q.E, q.L, q.s, q.t, v⟩ : StepPt) ∈ S W) →
      OneStepInput cp θ (fun q : StepPt => q.at q.s) S → Step1Out S →
      ∀ F : ℝ, 0 < F → PrecMax StepPt.L S (Λ := fun _ q => Fin q.L × Fin q.L)
        (fun W q ab ω => flowErr W (q.at q.u) ![ab.1, ab.2] ![true, false] ω)
        (fun W q ab => q.ratio ^ 6 * zetaProp q.g W q.L q.u ^ 2 *
          weightFn cp₂ θ F W (ellProp q.g q.L q.u) (cycDist ab.1 ab.2)) := by
  obtain ⟨cpN, hcpN0, hcpNcp, hLN⟩ := lemmaN_mixed R I c cp θ N hc hcp hθ hθ2 hN
  set cw := min cpN 1 with hcwdef
  have hcw0 : 0 < cw := lt_min hcpN0 one_pos
  have hcwN : cw ≤ cpN := min_le_left _ _
  have hcw1 : cw ≤ 1 := min_le_right _ _
  have hcwcp : cw ≤ cp := hcwN.trans hcpNcp
  refine ⟨cw, hcw0, hcwcp, hcw1, ?_⟩
  intro S hS hSu hin h1 F hF ε D hε hD
  -- constants fixed with the data
  set Cw := I.Cw with hCwdef
  have hCw : 1 ≤ Cw := I.one_le_Cw
  have hRC : 1 ≤ R.C := R.one_le_C
  have hRC0 : 0 < R.C := lt_of_lt_of_le one_pos hRC
  set M := lemmaNM Cw with hMdef
  have hcst : 0 ≤ cstarN Cw := by unfold cstarN; positivity
  have hM4 : 4 ≤ M := by simp only [hMdef, lemmaNM]; linarith
  have hNM : 3 * M - 8 ≤ N := by
    have h1 : 3 * cstarN Cw / 2 + 7 ≤ N := le_trans (le_max_right _ _) hN
    simp only [hMdef, lemmaNM]; linarith
  have hN20 : (20 : ℝ) ≤ N := le_trans (le_max_left _ _) hN
  set K := 1 + 3 * M with hKdef
  set F₁ := max F (2 * R.C + K + 40) with hF₁def
  have hFF₁ : F ≤ F₁ := le_max_left _ _
  have hF₁0 : 0 < F₁ := lt_of_lt_of_le hF hFF₁
  have hF₁K : 2 * R.C + K + 40 ≤ F₁ := le_max_right _ _
  set ε₁ := min ε 1 with hε₁def
  have hε₁0 : 0 < ε₁ := lt_min hε one_pos
  have hε₁ε : ε₁ ≤ ε := min_le_left _ _
  have hε₁1 : ε₁ ≤ 1 := min_le_right _ _
  set a := ε₁ / 24 with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by rw [ha]; linarith
  -- the regime, the weights and the inputs
  obtain ⟨Cc, hCc0, hconvAll⟩ := weight_convolution cw θ F₁ hcw0 hθ hθ2 hF₁0
  obtain ⟨C'₀, Wlp, hlp⟩ := R.longPair θ cw F₁ hθ hθ2 hcw0 hF₁0
  set C' := max C'₀ 0 with hC'def
  have hC'0 : 0 ≤ C' := le_max_right _ _
  obtain ⟨Cpw, hCpw0, hpw⟩ := propagated_weight R.C R.c cw θ R.C F₁ hRC0 R.c_pos hcw0 hθ hθ2
    hRC0.le hF₁0
  obtain ⟨Wdy, hdy⟩ := R.dyson
  obtain ⟨Wker, hker⟩ := R.kernel (R.C + F₁ + 1) (by positivity)
  obtain ⟨Wbud, hbud⟩ := R.budget
  obtain ⟨Wpr, hpr⟩ := R.prim 2 1 one_pos
  obtain ⟨C₀, hcrude⟩ := I.crude
  obtain ⟨C₁, hgm⟩ := lemmaNOffset_gen_moment R I
  obtain ⟨CS, Wsw, hsw⟩ := I.sw cw θ F 4 (D + 1) hcw0 hcw1 hθ hθ2 hF (by norm_num) (by linarith)
  set CS' := max CS 0 with hCS'
  have hCS'0 : 0 ≤ CS' := le_max_right _ _
  -- the moment order
  set p : ℕ := ⌈4 * (D + CS' + 2) / ε₁⌉₊ + 1 with hpdef
  have hp : 1 ≤ p := by omega
  have hpε : D + CS' + 2 ≤ ε₁ * p / 4 := by
    have h1 := Nat.le_ceil (4 * (D + CS' + 2) / ε₁)
    have h2 : 4 * (D + CS' + 2) / ε₁ ≤ p := by simp only [hpdef]; push_cast; linarith
    rw [div_le_iff₀ hε₁0] at h2
    linarith
  obtain ⟨Cp8, Wcr, hcr⟩ := hcrude (2 * (2 * (2 * p))) (by omega)
  obtain ⟨Cg, Wg, hgg⟩ := hgm (2 * (2 * p)) (by omega)
  obtain ⟨CΓ, WΓ, hgΓ⟩ := hgm (2 * p) (by omega)
  set C₀' := max C₀ 0 with hC₀'
  set C₁' := max C₁ 0 with hC₁'
  set K₀ := 2 ^ (2 * (2 * p) - 1) * (max Cp8 0 + 1) + max Cg 0 + max CΓ 0 with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  set E₁ := C₀' * (2 * (2 * (2 * p)) : ℕ) + C₁' * (2 * (2 * p) : ℕ) + (2 * (2 * p) : ℕ) with hE₁
  have hE₁0 : 0 ≤ E₁ := by positivity
  set D' := (32 * p + E₁ + 4 * p * F₁ + 2 : ℝ) with hD'
  have hD'0 : 0 < D' := by positivity
  -- the events at loss `W^a` and failure `W^{-D'}`
  obtain ⟨Wop, hopW⟩ := h1.op a D' ha0 hD'0
  obtain ⟨Whs, hhsW⟩ := h1.hs a D' ha0 hD'0
  obtain ⟨Wavg, havgW⟩ := h1.avg a D' ha0 hD'0
  obtain ⟨WLN, hLNW⟩ := hLN S hS hSu hin h1 F₁ hF₁0 a D' ha0 hD'0
  obtain ⟨Win, hinW⟩ := hin.pair F₁ hF₁0 a D' ha0 hD'0
  -- thresholds
  obtain ⟨Wbig, hbig⟩ := step2_large_const (max 64 (max C' Cc)) ha0
  obtain ⟨Wlg, hlg⟩ := step2_large_logpow (k := 2 / θ) (by positivity) ha0
  obtain ⟨Wsh, hsh⟩ := step2_weight_short ha0
  obtain ⟨Wex, hex⟩ := step2_large_exp 1 F₁ hcw0
  obtain ⟨Wrem, hrem⟩ := step2_large_const (2 * Real.sqrt (3 ^ (4 * p) * K₀) * 4 ^ (2 * p))
    one_pos
  set K₂ := Cpw * (1 + Real.sqrt (2 * p)) + 2 + Real.sqrt (2 * p) with hK₂
  obtain ⟨Wfin, hfin⟩ := step2_large_const K₂ (by positivity : 0 < ε₁ / 8)
  obtain ⟨Wcw, hcwW⟩ := step2_large_const (Cw + 1) (by positivity : 0 < ε₁ / 2)
  refine ⟨max (max (max 4 Wbig) (max Wlg (max Wsh Wex))) (max (max Wrem (max Wfin Wcw))
    (max (max Wlp (max Wdy (max Wker (max Wbud Wpr)))) (max (max Wcr (max Wg WΓ))
      (max Wsw (max Wop (max Whs (max Wavg (max WLN Win)))))))), fun W hW q hq => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hW4, hWbig⟩, hWlg, hWsh, hWex⟩, ⟨hWrem, hWfin, hWcw⟩,
    ⟨hWlp, hWdy, hWker, hWbud, hWpr⟩, ⟨hWcr, hWg, hWΓ⟩, hWsw, hWop, hWhs, hWavg, hWLN, hWin⟩ := hW
  -- the step point
  have hadmq := hS W hq
  rcases q with ⟨g, E, L, s, t, v⟩
  obtain ⟨⟨d, hdJ, hreach⟩, hs, hsv, hvt, hst, ht3, hRN⟩ := hadmq
  change 1 / 2 ≤ s at hs
  change s ≤ v at hsv
  change v ≤ t at hvt
  change s < t at hst
  change (W : ℝ) ^ (-3 : ℝ) ≤ 1 - t at ht3
  change ((1 - s) / (1 - t)) ^ N * zetaProp g W L t ≤ (W : ℝ) ^ (-c) at hRN
  change CmpReach R.base W d ⟨g, E, L, t⟩ at hreach
  have hW1 : 1 ≤ W := by omega
  have hW3 : 3 ≤ W := by omega
  have hW2 : 2 ≤ W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW4r : (4 : ℝ) ≤ W := by exact_mod_cast hW4
  have ht1 : t < 1 := by
    have : 0 < (W : ℝ) ^ (-3 : ℝ) := Real.rpow_pos_of_pos hW0 _
    linarith
  have hv1 : v < 1 := lt_of_le_of_lt hvt ht1
  have hs0 : 0 ≤ s := by linarith
  have hreachu : ∀ u : ℝ, 1 / 2 ≤ u → u ≤ t → CmpReach R.base W d ⟨g, E, L, u⟩ :=
    fun u hu1 hu2 => CmpReach.earlier u hreach hu1 hu2
  obtain ⟨hL, hg, hroot, -⟩ := hdy W hWdy d ⟨g, E, L, t⟩ hdJ.le hreach
  change 3 ≤ L at hL
  change 0 ≤ g at hg
  have hL1 : 1 ≤ L := by omega
  set Rr := (1 - s) / (1 - t) with hRrdef
  have h1t : 0 < 1 - t := by linarith
  have hR1 : 1 ≤ Rr := by rw [hRrdef, le_div_iff₀ h1t]; linarith
  have hR3 : Rr ≤ (W : ℝ) ^ 3 := by
    have hW3' : (W : ℝ) ^ (-3 : ℝ) = ((W : ℝ) ^ 3)⁻¹ := by
      rw [Real.rpow_neg hW0.le]; norm_cast
    rw [hW3'] at ht3
    rw [hRrdef, div_le_iff₀ h1t]
    have h1 : 1 ≤ (W : ℝ) ^ 3 * (1 - t) := by
      have := mul_le_mul_of_nonneg_left ht3 (by positivity : (0 : ℝ) ≤ (W : ℝ) ^ 3)
      rwa [mul_inv_cancel₀ (by positivity)] at this
    linarith
  have hζt0 : 0 ≤ zetaProp g W L t :=
    le_trans (by positivity) (scale_facts g hg W L hW1 hL1 t t (by linarith) le_rfl ht1).2.2.2.1
  have hRN1 : Rr ^ N * zetaProp g W L t ≤ 1 :=
    hRN.trans (Real.rpow_le_one_of_one_le_of_nonpos hW1r (by linarith))
  have hζt1 : zetaProp g W L t ≤ 1 := by
    have h1 : 1 ≤ Rr ^ N := Real.one_le_rpow hR1 (by linarith)
    nlinarith
  -- the loss `ω = W^a`
  set ω := (W : ℝ) ^ a with hωdef
  have hbigW := hbig W hWbig
  have hω64 : 64 ≤ ω := le_trans (le_max_left _ _) hbigW
  have hωC' : C' ≤ ω := le_trans ((le_max_left _ _).trans (le_max_right _ _)) hbigW
  have hωCc : Cc ≤ ω := le_trans ((le_max_right _ _).trans (le_max_right _ _)) hbigW
  have hωW : ω ≤ W := by
    calc ω = (W : ℝ) ^ a := rfl
      _ ≤ (W : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hW1r ha1
      _ = W := Real.rpow_one _
  have hω1 : 1 ≤ ω := by linarith
  have hlgW : Real.log W ^ (2 / θ) ≤ ω := hlg W hWlg
  set Λ := ω * Rr ^ M with hΛdef
  have hRM0 : 0 ≤ Rr ^ M := Real.rpow_nonneg (by linarith) _
  have hΛ0 : 0 ≤ Λ := by positivity
  -- the exponent bounds
  have hRMW : Rr ^ M ≤ (W : ℝ) ^ (3 * M) := by
    calc Rr ^ M ≤ ((W : ℝ) ^ (3 : ℝ)) ^ M := by
          refine Real.rpow_le_rpow (by linarith) ?_ (by linarith)
          rw [show ((W : ℝ) ^ (3 : ℝ)) = (W : ℝ) ^ (3 : ℕ) by norm_cast]; exact hR3
      _ = (W : ℝ) ^ (3 * M) := by rw [← Real.rpow_mul hW0.le]
  set X := (W : ℝ) ^ K with hXdef
  set Y := (W : ℝ) ^ R.C with hYdef
  have hX1 : 1 ≤ X := Real.one_le_rpow hW1r (by rw [hKdef]; linarith)
  have hY1 : 1 ≤ Y := Real.one_le_rpow hW1r (by linarith)
  have hΛX : Λ ≤ X := by
    calc Λ = ω * Rr ^ M := rfl
      _ ≤ (W : ℝ) * (W : ℝ) ^ (3 * M) := mul_le_mul hωW hRMW hRM0 hW0.le
      _ = (W : ℝ) ^ (1 + 3 * M) := by rw [Real.rpow_add hW0, Real.rpow_one]
      _ = X := by rw [hXdef, hKdef]
  have hWX : (W : ℝ) ≤ X := by
    calc (W : ℝ) = (W : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ X := Real.rpow_le_rpow_of_exponent_le hW1r (by rw [hKdef]; linarith)
  have hCΛX : C' + Λ ≤ 2 * X := by linarith
  set εw := Real.exp (-(cw * Real.log W ^ (2 : ℝ))) + (W : ℝ) ^ (-F₁) with hεwdef
  have hεw0 : 0 ≤ εw := by positivity
  have hεw : εw ≤ 2 / ((W : ℝ) ^ 40 * X * Y ^ 2) := by
    have he := hex W hWex
    rw [one_mul] at he
    have h1 : (W : ℝ) ^ (-F₁) ≤ ((W : ℝ) ^ 40 * X * Y ^ 2)⁻¹ := by
      have e : (W : ℝ) ^ 40 * X * Y ^ 2 = (W : ℝ) ^ (40 + K + 2 * R.C) := by
        rw [hXdef, hYdef, ← Real.rpow_natCast (W : ℝ) 40, ← Real.rpow_natCast ((W : ℝ) ^ R.C) 2,
          ← Real.rpow_mul hW0.le, ← Real.rpow_add hW0, ← Real.rpow_add hW0]
        congr 1; push_cast; ring
      rw [e, ← Real.rpow_neg hW0.le]
      exact Real.rpow_le_rpow_of_exponent_le hW1r (by linarith)
    calc εw ≤ (W : ℝ) ^ (-F₁) + (W : ℝ) ^ (-F₁) := by rw [hεwdef]; linarith
      _ ≤ ((W : ℝ) ^ 40 * X * Y ^ 2)⁻¹ + ((W : ℝ) ^ 40 * X * Y ^ 2)⁻¹ := by linarith
      _ = 2 / ((W : ℝ) ^ 40 * X * Y ^ 2) := by ring
  obtain ⟨hsm1, hsm2⟩ := step2_num_sm hW4r hω1 hωW hR1 hR3 hC'0 hΛ0 (hωC'.trans hωW) hCΛX hX1
    hY1 hεw0 hεw
  -- facts on the reach at the times of the step
  have hLℓ : ∀ r ∈ Set.Icc s v, (L : ℝ) / ellProp g L r ≤ Y := by
    intro r hr
    have hb := hbud W hWbud d ⟨g, E, L, r⟩ hdJ.le (hreachu r (by linarith [hr.1]) (hr.2.trans hvt))
    change gammaG g * L + L / ellProp g L r ≤ (W : ℝ) ^ R.C at hb
    have : 0 ≤ gammaG g * L := by
      have : 0 < gammaG g := by unfold gammaG; positivity
      positivity
    linarith
  have hconv : ∀ r ∈ Set.Icc s v, ∀ x y : Fin L, _ := fun r hr x y => by
    obtain ⟨hℓ1, -, hℓL, -, -, -, -⟩ :=
      scale_facts g hg W L hW1 hL1 r r (by linarith [hr.1]) le_rfl (by linarith [hr.2])
    have hℓ0 : 0 < ellProp g L r := by linarith
    have hLW : (L : ℝ) * (W : ℝ) ^ (-(F₁ / 2)) ≤ ellProp g L r := by
      have h1 := hLℓ r hr
      rw [div_le_iff₀ hℓ0] at h1
      have h2 : (W : ℝ) ^ R.C * (W : ℝ) ^ (-(F₁ / 2)) ≤ 1 := by
        rw [← Real.rpow_add hW0]
        exact Real.rpow_le_one_of_one_le_of_nonpos hW1r (by linarith)
      calc (L : ℝ) * (W : ℝ) ^ (-(F₁ / 2)) ≤ Y * ellProp g L r * (W : ℝ) ^ (-(F₁ / 2)) := by
            gcongr
        _ = ((W : ℝ) ^ R.C * (W : ℝ) ^ (-(F₁ / 2))) * ellProp g L r := by rw [hYdef]; ring
        _ ≤ 1 * ellProp g L r := by gcongr
        _ = _ := one_mul _
    exact hconvAll W L hW1 hL1 (ellProp g L r) hℓ1 hℓL hLW x y
  have hprim : ∀ r ∈ Set.Icc s v, ∀ x y : Fin L,
      ellProp g L r * Real.log W ^ ((3 : ℝ) / 2) < cycDist x y →
      ‖primLoop g W L E (mRoot g L E) r ![x, y] ![true, false]‖ ≤
        C' * zetaProp g W L r ^ 2 * weightFn cw θ F₁ W (ellProp g L r) (cycDist x y) := by
    intro r hr x y hxy
    have h1 := hlp W hWlp d ⟨g, E, L, r⟩ hdJ.le
      (hreachu r (by linarith [hr.1]) (hr.2.trans hvt)) x y true false hxy.le
    refine h1.trans ?_
    have : 0 ≤ zetaProp g W L r ^ 2 * weightFn cw θ F₁ W (ellProp g L r) (cycDist x y) :=
      mul_nonneg (sq_nonneg _) (step2_weight_pos cw θ F₁ hW1 _ _).le
    calc C'₀ * zetaProp g W L r ^ 2 * weightFn cw θ F₁ W (ellProp g L r) (cycDist x y) =
        C'₀ * (zetaProp g W L r ^ 2 * weightFn cw θ F₁ W (ellProp g L r) (cycDist x y)) := by
          ring
      _ ≤ C' * (zetaProp g W L r ^ 2 * weightFn cw θ F₁ W (ellProp g L r) (cycDist x y)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) this
      _ = _ := by ring
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  set P := pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E (mRoot g L E)) with hPdef
  have hP0 : ∀ x z, 0 ≤ P x z := fun x z => by
    simp only [hPdef, pairP, Matrix.of_apply]; positivity
  have hProw : ∀ x, ∑ z, P x z = 1 := fun x =>
    pairP_row_sum (hopB g) (gammaG g) hγ L hL1 E (mRoot g L E) hroot x
  have hprop : ∀ a b : Fin L, ∀ r ∈ Set.Icc s v, ∑ l : Fin L × Fin L,
      step2Coef P v a b l r * weightFn cw θ F₁ W (ellProp g L r) (cycDist l.1 l.2) ≤
      Cpw * ((1 - r) / (1 - v)) ^ 2 * weightFn cw θ F₁ W (ellProp g L v) (cycDist a b) := by
    intro a b r hr
    obtain ⟨hℓr1, hℓrv, -, -, -, -, -⟩ :=
      scale_facts g hg W L hW1 hL1 r v (by linarith [hr.1]) hr.2 hv1
    have hkv := fun x y => (hker W hWker d ⟨g, E, L, v⟩ hdJ.le
      (hreachu v (by linarith) hvt) x y).2
    have h := hpw W L hW1 hL1 P r v (ellProp g L r) (ellProp g L v) hP0 hProw
      (by linarith [hr.1]) hr.2 hv1 hℓr1 hℓrv (hLℓ r hr) hkv a b
    calc ∑ l : Fin L × Fin L, step2Coef P v a b l r *
          weightFn cw θ F₁ W (ellProp g L r) (cycDist l.1 l.2)
        = ∑ a', ∑ b', propPM P r v a a' * propPM P r v b b' *
            weightFn cw θ F₁ W (ellProp g L r) (cycDist a' b') := by
          rw [Fintype.sum_prod_type]; rfl
      _ ≤ _ := h
  -- the intermediate step points
  have hqr : ∀ r ∈ Set.Icc s v, (⟨g, E, L, s, t, r⟩ : StepPt) ∈ S W := fun r hr =>
    hSu W _ hq r hr.1 hr.2
  set δ₁ := (W : ℝ) ^ (-D') with hδ₁def
  have hδ₁0 : 0 ≤ δ₁ := by positivity
  have hopP : ∀ r ∈ Set.Ioo s v, μ W L {x | ∃ l : Fin L × Fin L,
      ω * (W * Rr * zetaProp g W L r) <
        ‖((‖blockOf (flowG W ⟨g, E, L, r⟩ x) l.1 l.2‖ : ℝ) : ℂ)‖} ≤ ENNReal.ofReal δ₁ :=
    fun r hr => hopW W hWop _ (hqr r ⟨hr.1.le, hr.2.le⟩)
  have hhsP : ∀ r ∈ Set.Ioo s v, μ W L {x | ∃ l : Fin L × Fin L,
      ω * ((W : ℝ) ^ 2 * Rr * zetaProp g W L r) <
        ‖((blockHS2 (flowG W ⟨g, E, L, r⟩ x) l.1 l.2 : ℝ) : ℂ)‖} ≤ ENNReal.ofReal δ₁ :=
    fun r hr => hhsW W hWhs _ (hqr r ⟨hr.1.le, hr.2.le⟩)
  have havgP : ∀ r ∈ Set.Ioo s v, μ W L {x | ∃ c : Fin L,
      ω * (Rr ^ 2 * zetaProp g W L r) <
        ‖blockTr (flowG W ⟨g, E, L, r⟩ x - flowM W ⟨g, E, L, r⟩) c c‖} ≤ ENNReal.ofReal δ₁ :=
    fun r hr => havgW W hWavg _ (hqr r ⟨hr.1.le, hr.2.le⟩)
  have hD2P : ∀ r ∈ Set.Ioo s v, μ W L {x | ∃ l : Fin L × Fin L, Λ * zetaProp g W L r ^ 2 *
        weightFn cw θ F₁ W (ellProp g L r) (cycDist l.1 l.2) <
      ‖flowErr W ⟨g, E, L, r⟩ ![l.1, l.2] ![true, false] x‖} ≤ ENNReal.ofReal δ₁ := by
    intro r hr
    refine le_trans (measure_mono ?_) (hLNW W hWLN _ (hqr r ⟨hr.1.le, hr.2.le⟩))
    rintro x ⟨l, hl⟩
    refine ⟨l, lt_of_le_of_lt ?_ hl⟩
    obtain ⟨hℓ1, -, -, -, -, -, -⟩ :=
      scale_facts g hg W L hW1 hL1 r r (by linarith [hr.1]) le_rfl (by linarith [hr.2])
    have hw : weightFn cpN θ F₁ W (ellProp g L r) (cycDist l.1 l.2) ≤
        weightFn cw θ F₁ W (ellProp g L r) (cycDist l.1 l.2) :=
      step2_weight_anti_c hcwN (by linarith) (Nat.cast_nonneg _)
    change ω * (Rr ^ M * zetaProp g W L r ^ 2 *
      weightFn cpN θ F₁ W (ellProp g L r) (cycDist l.1 l.2)) ≤ _
    have h0 : 0 ≤ ω * Rr ^ M * zetaProp g W L r ^ 2 := by positivity
    calc ω * (Rr ^ M * zetaProp g W L r ^ 2 * weightFn cpN θ F₁ W (ellProp g L r)
          (cycDist l.1 l.2)) = (ω * Rr ^ M * zetaProp g W L r ^ 2) *
            weightFn cpN θ F₁ W (ellProp g L r) (cycDist l.1 l.2) := by ring
      _ ≤ (ω * Rr ^ M * zetaProp g W L r ^ 2) *
            weightFn cw θ F₁ W (ellProp g L r) (cycDist l.1 l.2) :=
          mul_le_mul_of_nonneg_left hw h0
      _ = _ := by rw [hΛdef]
  have hinP : μ W L {x | ∃ l : Fin L × Fin L, ω * (zetaProp g W L s ^ 2 *
        weightFn cw θ F₁ W (ellProp g L s) (cycDist l.1 l.2)) <
      ‖flowErr W ⟨g, E, L, s⟩ ![l.1, l.2] ![true, false] x‖} ≤ ENNReal.ofReal δ₁ := by
    refine le_trans (measure_mono ?_) (hinW W hWin _ hq)
    rintro x ⟨l, hl⟩
    refine ⟨l, lt_of_le_of_lt ?_ hl⟩
    obtain ⟨hℓ1, -, -, -, -, -, -⟩ :=
      scale_facts g hg W L hW1 hL1 s s hs0 le_rfl (by linarith)
    have hw : weightFn cp θ F₁ W (ellProp g L s) (cycDist l.1 l.2) ≤
        weightFn cw θ F₁ W (ellProp g L s) (cycDist l.1 l.2) :=
      step2_weight_anti_c hcwcp (by linarith) (Nat.cast_nonneg _)
    change ω * (zetaProp g W L s ^ 2 * weightFn cp θ F₁ W (ellProp g L s) (cycDist l.1 l.2)) ≤ _
    gcongr
  -- the crude moments
  set M₀ := K₀ * (W : ℝ) ^ E₁ with hM₀def
  have hWE : ∀ x : ℝ, x ≤ E₁ → (W : ℝ) ^ x ≤ (W : ℝ) ^ E₁ := fun x hx =>
    Real.rpow_le_rpow_of_exponent_le hW1r hx
  have hζr1 : ∀ r ∈ Set.Icc s v, zetaProp g W L r ≤ 1 := fun r hr =>
    ((scale_facts g hg W L hW1 hL1 r t (by linarith [hr.1]) (hr.2.trans hvt) ht1).2.2.2.2.1).trans
      hζt1
  have hD : ∀ r ∈ Set.Icc s v, ∀ l : Fin L × Fin L,
      ∫ x, ‖flowErr W ⟨g, E, L, r⟩ ![l.1, l.2] ![true, false] x‖ ^ (2 * (2 * p)) ∂(μ W L) ≤
        M₀ := by
    intro r hr l
    have hreach_r := hreachu r (by linarith [hr.1]) (hr.2.trans hvt)
    have hseg : SegAdm R.base R.J W (⟨g, E, L, r⟩, etaChar g (mRoot g L E) r) :=
      ⟨d, hdJ.le, hreach_r, Or.inl rfl⟩
    obtain ⟨hcint, hcbd⟩ := hcr W hWcr _ hseg l.2 l.1
    have hprim2 : ‖primLoop g W L E (mRoot g L E) r ![l.1, l.2] ![true, false]‖ ≤ W := by
      have h := hpr W hWpr d ⟨g, E, L, r⟩ hdJ.le hreach_r 2 le_rfl le_rfl ![l.1, l.2]
        ![true, false]
      refine h.trans ?_
      rw [Real.rpow_one, pow_one]
      calc (W : ℝ) * zetaProp g W L r ≤ W * 1 := by
            gcongr; exact hζr1 r hr
        _ = W := mul_one _
    have eG : ∀ ω' : Ω W L, segG W (⟨g, E, L, r⟩, etaChar g (mRoot g L E) r) ω' =
        flowG W ⟨g, E, L, r⟩ ω' := fun ω' => step2_segG_eta W ⟨g, E, L, r⟩ ω'
    simp only [eG] at hcint hcbd
    have hm := step2_flowErr_moment W ⟨g, E, L, r⟩ l.1 l.2 (2 * (2 * p)) hW0.le hprim2 hcint
    refine hm.trans ?_
    have hCp : Cp8 * (W : ℝ) ^ (C₀ * ((2 * (2 * (2 * p)) : ℕ) : ℝ)) ≤
        max Cp8 0 * (W : ℝ) ^ E₁ := by
      refine mul_le_mul (le_max_left _ _) (hWE _ ?_) (by positivity) (le_max_right _ _)
      rw [hE₁]
      have : C₀ * ((2 * (2 * (2 * p)) : ℕ) : ℝ) ≤ C₀' * ((2 * (2 * (2 * p)) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
      have : 0 ≤ C₁' * ((2 * (2 * p) : ℕ) : ℝ) := by positivity
      have : (0 : ℝ) ≤ ((2 * (2 * p) : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have hWk : (W : ℝ) ^ (2 * (2 * p)) ≤ (W : ℝ) ^ E₁ := by
      rw [← Real.rpow_natCast]
      refine hWE _ ?_
      rw [hE₁]
      have : 0 ≤ C₀' * ((2 * (2 * (2 * p)) : ℕ) : ℝ) := by positivity
      have : 0 ≤ C₁' * ((2 * (2 * p) : ℕ) : ℝ) := by positivity
      linarith
    calc (2 : ℝ) ^ (2 * (2 * p) - 1) * (∫ ω', ‖blockOf (flowG W ⟨g, E, L, r⟩ ω') l.2 l.1‖ ^
          (2 * (2 * (2 * p))) ∂(μ W L) + (W : ℝ) ^ (2 * (2 * p)))
        ≤ 2 ^ (2 * (2 * p) - 1) * (max Cp8 0 * (W : ℝ) ^ E₁ + (W : ℝ) ^ E₁) := by
          gcongr
          exact hcbd.trans hCp
      _ = 2 ^ (2 * (2 * p) - 1) * (max Cp8 0 + 1) * (W : ℝ) ^ E₁ := by ring
      _ ≤ K₀ * (W : ℝ) ^ E₁ := by
          gcongr
          rw [hK₀]
          have : 0 ≤ max Cg 0 := le_max_right _ _
          have : 0 ≤ max CΓ 0 := le_max_right _ _
          linarith
  have hG : ∀ r ∈ Set.Ioo s v, ∀ l : Fin L × Fin L,
      ∫ x, ‖blockGen W L (gammaG g) (fun r N =>
          resLoop g E (mRoot g L E) ![l.1, l.2] ![true, false] r N -
            primLoop g W L E (mRoot g L E) r ![l.1, l.2] ![true, false]) r
          (flowH g W L r x)‖ ^ (2 * (2 * p)) ∂(μ W L) ≤ M₀ := by
    intro r hr l
    have hreach_r := hreachu r (by linarith [hr.1]) (hr.2.le.trans hvt)
    obtain ⟨-, h, -, -⟩ := hgg W hWg d ⟨g, E, L, r⟩ hdJ.le hreach_r
      (hζr1 r ⟨hr.1.le, hr.2.le⟩) l.1 l.2
    refine h.trans ?_
    refine mul_le_mul (le_trans (le_max_left Cg 0) ?_) (hWE _ ?_) (by positivity) hK₀0
    · rw [hK₀]
      have : 0 ≤ 2 ^ (2 * (2 * p) - 1) * (max Cp8 0 + 1) := by positivity
      have : 0 ≤ max CΓ 0 := le_max_right _ _
      linarith
    · rw [hE₁]
      have : C₁ * ((2 * (2 * p) : ℕ) : ℝ) ≤ C₁' * ((2 * (2 * p) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
      have : 0 ≤ C₀' * ((2 * (2 * (2 * p)) : ℕ) : ℝ) := by positivity
      have : (0 : ℝ) ≤ ((2 * (2 * p) : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
  have hΓ : ∀ r ∈ Set.Ioo s v, ∀ l : Fin L × Fin L,
      Integrable (fun x => ‖blockGamma W L (gammaG g)
          (resLoop g E (mRoot g L E) ![l.1, l.2] ![true, false] r)
          (resLoop g E (mRoot g L E) ![l.1, l.2] ![true, false] r)
          (flowH g W L r x)‖ ^ (2 * p)) (μ W L) ∧
      ∫ x, ‖blockGamma W L (gammaG g)
          (resLoop g E (mRoot g L E) ![l.1, l.2] ![true, false] r)
          (resLoop g E (mRoot g L E) ![l.1, l.2] ![true, false] r)
          (flowH g W L r x)‖ ^ (2 * p) ∂(μ W L) ≤ M₀ := by
    intro r hr l
    have hreach_r := hreachu r (by linarith [hr.1]) (hr.2.le.trans hvt)
    obtain ⟨-, -, hi, h⟩ := hgΓ W hWΓ d ⟨g, E, L, r⟩ hdJ.le hreach_r
      (hζr1 r ⟨hr.1.le, hr.2.le⟩) l.1 l.2
    refine ⟨hi, h.trans ?_⟩
    refine mul_le_mul (le_trans (le_max_left CΓ 0) ?_) (hWE _ ?_) (by positivity) hK₀0
    · rw [hK₀]
      have : 0 ≤ 2 ^ (2 * (2 * p) - 1) * (max Cp8 0 + 1) := by positivity
      have : 0 ≤ max Cg 0 := le_max_right _ _
      linarith
    · rw [hE₁]
      have : C₁ * ((2 * p : ℕ) : ℝ) ≤ C₁' * ((2 * (2 * p) : ℕ) : ℝ) := by
        have h1 : C₁ * ((2 * p : ℕ) : ℝ) ≤ C₁' * ((2 * p : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
        have h2 : C₁' * ((2 * p : ℕ) : ℝ) ≤ C₁' * ((2 * (2 * p) : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left (by push_cast; linarith) (le_max_right _ _)
        linarith
      have : 0 ≤ C₀' * ((2 * (2 * (2 * p)) : ℕ) : ℝ) := by positivity
      have : (0 : ℝ) ≤ ((2 * (2 * p) : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
  -- the remainder
  set ρ := (4 * (W : ℝ) ^ 2)⁻¹ * (W : ℝ) ^ (-F₁) with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  have hv3 : (W : ℝ) ^ (-3 : ℝ) ≤ 1 - v := by linarith
  have hremX := step2_num_rem (W := W) hW1 (v := v) (M₀ := M₀) (K₀ := K₀) (E := E₁) (F₁ := F₁) p
    hv3 (by positivity) hK₀0 le_rfl (by
      have := hrem W hWrem
      rwa [Real.rpow_one] at this)
  have hX0 : 0 ≤ Real.sqrt ((3 * ((1 - v) ^ 2)⁻¹) ^ (2 * (2 * p)) * M₀) *
      Real.sqrt (4 * δ₁) := by positivity
  have hrem1 : (Real.sqrt ((3 * ((1 - v) ^ 2)⁻¹) ^ (2 * (2 * p)) * M₀) * Real.sqrt (4 * δ₁)) ^
      (1 / (2 * (p : ℝ))) ≤ ρ := by
    have hp0 : (0 : ℝ) < 2 * p := by
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    calc _ ≤ (ρ ^ (2 * p)) ^ (1 / (2 * (p : ℝ))) := Real.rpow_le_rpow hX0 hremX (by positivity)
      _ = ρ := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hρ0]
          have : ((2 * p : ℕ) : ℝ) * (1 / (2 * (p : ℝ))) = 1 := by push_cast; field_simp
          rw [this, Real.rpow_one]
  have hrem2 : (Real.sqrt ((3 * ((1 - v) ^ 2)⁻¹) ^ (2 * (2 * p)) * M₀) * Real.sqrt (4 * δ₁)) ^
      (1 / (p : ℝ)) ≤ ρ ^ 2 := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
    calc _ ≤ (ρ ^ (2 * p)) ^ (1 / (p : ℝ)) := Real.rpow_le_rpow hX0 hremX (by positivity)
      _ = ρ ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hρ0]
          have : ((2 * p : ℕ) : ℝ) * (1 / (p : ℝ)) = ((2 : ℕ) : ℝ) := by push_cast; field_simp
          rw [this, Real.rpow_natCast]
  -- the moment bound at every pair
  have hmom := step2_pair_mom_atW g E hW3 hL hg hroot hs hsv hvt ht1 p hp hcw0.le hθ hθ2
    hF₁0.le hω64 rfl hM4 hNM hRN1 hC'0 hωC' hCc0.le hωCc hlgW hCpw0.le hρ0 hδ₁0 hLℓ hsm1 hsm2
    (hsh W hWsh cw θ F₁ hcw0.le hcw1 hθ hθ2) hconv hprim hprop hopP hhsP havgP hD2P hinP hD hG hΓ
    hrem1 hrem2
  -- the conclusion
  obtain ⟨S₀, hS₀card, hS₀⟩ := hsw W hWsw d ⟨g, E, L, t⟩ hdJ.le hreach
  obtain ⟨-, -, -, hζvW, -, -, -⟩ :=
    scale_facts g hg W L hW1 hL1 v v (hs0.trans hsv) le_rfl hv1
  have hω6 : ω ^ 6 = (W : ℝ) ^ (ε₁ / 4) := by
    rw [hωdef, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le, ha]; congr 1; push_cast; ring
  have hcard : ((S₀.card : ℕ) : ℝ) ≤ (W : ℝ) ^ CS' :=
    hS₀card.trans (Real.rpow_le_rpow_of_exponent_le hW1r (le_max_left _ _))
  exact step2_pair_conclude hW4 g E v (hs0.trans hsv) hv1 hL hroot p hp hFF₁
    (by linarith only [hCw]) hCpw0.le hω1 hR1 hε₁ε hζvW hρdef hω6 (hcwW W hWcw) (hfin W hWfin) S₀
    hcard hpε (hS₀ v v (by linarith only [hs, hsv]) le_rfl hvt) hmom

end Step2PairMain

section Step2Closure

private lemma step2c_smul_cycleAdj_isHermitian (b : ℝ) (L : ℕ) :
    (((b : ℝ) : ℂ) • cycleAdj L).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, (cycleAdj_isHermitian L).eq, Complex.star_def, Complex.conj_ofReal]

/-- Ward's identity for the Dyson matrix: `Σ_c |M_ac|² = Im M_aa / Im(z + βm)`. -/
private theorem step2_dysonMat_ward (b β : ℝ) (L : ℕ) (z m : ℂ) (hw : 0 < (z + β * m).im)
    (a : Fin L) :
    ∑ c, ‖dysonMat b β L z m a c‖ ^ 2 = (dysonMat b β L z m a a).im / (z + β * m).im := by
  have h := ward (step2c_smul_cycleAdj_isHermitian b L) (z + β * m).re hw.ne' a
  rw [Complex.re_add_im] at h
  exact h

/-- `1 - Q` is invertible when every row sum of `|Q|` is at most `θ < 1`. -/
private theorem step2_isUnit_one_sub {L : ℕ} (Q : Matrix (Fin L) (Fin L) ℂ) {θ : ℝ} (hθ : θ < 1)
    (h : ∀ a, ∑ c, ‖Q a c‖ ≤ θ) : IsUnit (1 - Q) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hfix : ∀ a, v a = ∑ c, Q a c * v c := by
    intro a
    have := congrFun hv a
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.zero_apply,
      sub_eq_zero] at this
    rw [this]; rfl
  set V := ⨆ a, ‖v a‖ with hV
  have hle : ∀ a, ‖v a‖ ≤ V := fun a =>
    le_ciSup (f := fun a => ‖v a‖) (Set.finite_range _).bddAbove a
  have hV0 : 0 ≤ V := Real.iSup_nonneg fun a => norm_nonneg _
  have hθ0 : 0 ≤ θ := by
    rcases isEmpty_or_nonempty (Fin L) with hL | ⟨⟨a⟩⟩
    · exact absurd (funext fun a => (hL.false a).elim) hv0
    · exact (Finset.sum_nonneg fun c _ => norm_nonneg _).trans (h a)
  have hVθ : V ≤ θ * V := by
    refine Real.iSup_le (fun a => ?_) (mul_nonneg hθ0 hV0)
    rw [hfix a]
    calc ‖∑ c, Q a c * v c‖ ≤ ∑ c, ‖Q a c‖ * V :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => by
            rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hle c) (norm_nonneg _))
      _ = (∑ c, ‖Q a c‖) * V := (Finset.sum_mul _ _ _).symm
      _ ≤ θ * V := mul_le_mul_of_nonneg_right (h a) hV0
  have hV00 : V = 0 := by nlinarith
  apply hv0
  funext a
  have := hle a
  rw [hV00] at this
  exact norm_le_zero_iff.mp this

/-- The rows of `Q = pairQ β M` above the real axis: `Σ_c |Q_ac| = β Im m / (Im z + β Im m)`. -/
private theorem step2_pairQ_row (b β : ℝ) (hβ : 0 ≤ β) (L : ℕ) (z m : ℂ) (hz : 0 < z.im)
    (hm : 0 < m.im) (hdiag : ∀ c, dysonMat b β L z m c c = m) (a : Fin L) :
    ∑ c, ‖pairQ β (dysonMat b β L z m) a c‖ = β * m.im / (z.im + β * m.im) := by
  have hw : 0 < (z + β * m).im := by
    have : (z + (β : ℂ) * m).im = z.im + β * m.im := by simp
    rw [this]; positivity
  have hward := step2_dysonMat_ward b β L z m hw a
  rw [hdiag a] at hward
  have : (z + (β : ℂ) * m).im = z.im + β * m.im := by simp
  rw [this] at hward
  simp only [pairQ, Matrix.of_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ,
    norm_pow, ← Finset.mul_sum, hward]
  ring

/-- The closure inequalities at one point: with `v_ab = ⟨G - M⟩_ab`, `|R| ≤ ρ`, `|⟨G⟩| ≤ Γ`,
`βΣ_c|M_ac| ≤ C`, rows of `(1 - Q)⁻¹` at most `C` and `|v_cc| ≤ U`:
`|v_aa| ≤ C(ρ + C U (ρ + C Γ U))` and `|v_ab| ≤ ρ + C U Γ`. -/
private theorem step2_closure {L : ℕ} (M : Matrix (Fin L) (Fin L) ℂ)
    (hMs : ∀ a c, M a c = M c a) (β : ℝ) (hβ : 0 ≤ β) (v g R : Fin L → Fin L → ℂ)
    (hid : ∀ a b, v a b = -R a b + (β : ℂ) * ∑ c, M a c * v c c * g c b)
    (hg : ∀ c b, g c b = M c b + v c b) {ρ Γ C U : ℝ} (hρ : ∀ a b, ‖R a b‖ ≤ ρ)
    (hΓ : ∀ a b, ‖g a b‖ ≤ Γ) (hrow : ∀ a, β * ∑ c, ‖M a c‖ ≤ C)
    (hinv : IsUnit (1 - pairQ β M)) (hrowinv : ∀ a, ∑ c, ‖(1 - pairQ β M)⁻¹ a c‖ ≤ C)
    (hU : ∀ c, ‖v c c‖ ≤ U) (hU0 : 0 ≤ U) (hΓ0 : 0 ≤ Γ) :
    (∀ a, ‖v a a‖ ≤ C * (ρ + C * U * (ρ + C * Γ * U))) ∧ ∀ a b, ‖v a b‖ ≤ ρ + C * U * Γ := by
  have hoff : ∀ a b, ‖v a b‖ ≤ ρ + C * U * Γ := by
    intro a b
    rw [hid]
    have h1 : ‖(β : ℂ) * ∑ c, M a c * v c c * g c b‖ ≤ C * U * Γ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ]
      calc β * ‖∑ c, M a c * v c c * g c b‖ ≤ β * ∑ c, ‖M a c‖ * (U * Γ) := by
            refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
              (Finset.sum_le_sum fun c _ => ?_)) hβ
            rw [norm_mul, norm_mul, mul_assoc]
            exact mul_le_mul_of_nonneg_left (mul_le_mul (hU c) (hΓ c b) (norm_nonneg _) hU0)
              (norm_nonneg _)
        _ = (β * ∑ c, ‖M a c‖) * (U * Γ) := by rw [← Finset.sum_mul]; ring
        _ ≤ C * (U * Γ) := mul_le_mul_of_nonneg_right (hrow a) (mul_nonneg hU0 hΓ0)
        _ = C * U * Γ := by ring
    calc ‖-R a b + (β : ℂ) * ∑ c, M a c * v c c * g c b‖
        ≤ ‖R a b‖ + ‖(β : ℂ) * ∑ c, M a c * v c c * g c b‖ := by
          rw [← norm_neg (R a b)]; exact norm_add_le _ _
      _ ≤ ρ + C * U * Γ := add_le_add (hρ a b) h1
  refine ⟨?_, hoff⟩
  set Q := pairQ β M with hQ
  set d : Fin L → ℂ := fun a => v a a with hd
  set e : Fin L → ℂ := fun a => (β : ℂ) * ∑ c, M a c * v c c * v c a with he
  have hlin : (1 - Q) *ᵥ d = fun a => -R a a + e a := by
    funext a
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, hd, he]
    have h := hid a a
    simp only [hg] at h
    have hQd : (Q *ᵥ fun a => v a a) a = (β : ℂ) * ∑ c, M a c * v c c * M c a := by
      simp only [Matrix.mulVec, dotProduct, hQ, pairQ, Matrix.of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hMs c a]; ring
    rw [hQd]
    conv_lhs => rw [h]
    simp only [mul_add, Finset.sum_add_distrib]
    ring
  have hdinv : d = (1 - Q)⁻¹ *ᵥ ((1 - Q) *ᵥ d) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hinv),
      Matrix.one_mulVec]
  have hf : ∀ c, ‖-R c c + e c‖ ≤ ρ + C * U * (ρ + C * Γ * U) := by
    intro c
    have he1 : ‖e c‖ ≤ C * U * (ρ + C * Γ * U) := by
      simp only [he]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ]
      have hb : ∀ c', ‖v c' c‖ ≤ ρ + C * Γ * U := fun c' => by
        have := hoff c' c; linarith [mul_comm (C * U) Γ, show C * U * Γ = C * Γ * U by ring]
      have hpos : 0 ≤ ρ + C * Γ * U := (norm_nonneg _).trans (hb c)
      calc β * ‖∑ c', M c c' * v c' c' * v c' c‖ ≤ β * ∑ c', ‖M c c'‖ * (U * (ρ + C * Γ * U)) := by
            refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
              (Finset.sum_le_sum fun c' _ => ?_)) hβ
            rw [norm_mul, norm_mul, mul_assoc]
            exact mul_le_mul_of_nonneg_left (mul_le_mul (hU c') (hb c') (norm_nonneg _) hU0)
              (norm_nonneg _)
        _ = (β * ∑ c', ‖M c c'‖) * (U * (ρ + C * Γ * U)) := by rw [← Finset.sum_mul]; ring
        _ ≤ C * (U * (ρ + C * Γ * U)) :=
            mul_le_mul_of_nonneg_right (hrow c) (mul_nonneg hU0 hpos)
        _ = _ := by ring
    calc ‖-R c c + e c‖ ≤ ‖R c c‖ + ‖e c‖ := by rw [← norm_neg (R c c)]; exact norm_add_le _ _
      _ ≤ _ := add_le_add (hρ c c) he1
  intro a
  have hda : v a a = ((1 - Q)⁻¹ *ᵥ fun c => -R c c + e c) a := by
    have := congrFun hdinv a
    rw [hlin] at this
    exact this
  have hpos : 0 ≤ ρ + C * U * (ρ + C * Γ * U) := (norm_nonneg _).trans (hf a)
  rw [hda]
  simp only [Matrix.mulVec, dotProduct]
  calc ‖∑ c, (1 - Q)⁻¹ a c * (-R c c + e c)‖
      ≤ ∑ c, ‖(1 - Q)⁻¹ a c‖ * (ρ + C * U * (ρ + C * Γ * U)) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hf c) (norm_nonneg _))
    _ = (∑ c, ‖(1 - Q)⁻¹ a c‖) * (ρ + C * U * (ρ + C * Γ * U)) := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (hrowinv a) hpos

/-- `⟨X - Y⟩_{ab} = ⟨X⟩_{ab} - ⟨Y⟩_{ab}`. -/
private theorem step2_blockTr_sub {W L : ℕ} (X Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : blockTr (X - Y) a b = blockTr X a b - blockTr Y a b := by
  unfold blockTr
  simp only [Matrix.sub_apply, Finset.sum_sub_distrib, mul_sub]

/-- `⟨M ⊗ I_W⟩_{ab} = M_{ab}` for `W ≥ 1`. -/
private theorem step2_blockTr_kron (W L : ℕ) (hW : 1 ≤ W) (M : Matrix (Fin L) (Fin L) ℂ)
    (a b : Fin L) : blockTr (M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) a b = M a b := by
  have hW0 : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold blockTr
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

private lemma step2c_hopB_nonneg {g : ℝ} (hg : 0 ≤ g) : 0 ≤ hopB g :=
  div_nonneg hg (le_trans zero_le_one (le_max_left _ _))

/-- On the characteristic `y = η_u` the segment objects are those of the point:
`G = G_u(g, E)`, `M_u(z_u) = M_B ⊗ I` (the root at `(uγ_g, z_u)` is `m`). -/
private theorem step2_seg_lower (W : ℕ) (p : FlowPt) (hL : 3 ≤ p.L) (hg : 0 ≤ p.g)
    (hroot : IsDysonRootV (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E)) (hu0 : 0 < p.u)
    (hu : p.u < 1) :
    (∀ ω, segG W (p, etaChar p.g (mRoot p.g p.L p.E) p.u) ω = flowG W p ω) ∧
      segM W (p, etaChar p.g (mRoot p.g p.L p.E) p.u) = flowM W p := by
  set m := mRoot p.g p.L p.E with hm
  set zu := zChar p.g p.E m p.u with hzu
  have hγ : 0 < gammaG p.g := by unfold gammaG; positivity
  have hz1 : ((zu.re : ℝ) : ℂ) + ((etaChar p.g m p.u : ℝ) : ℂ) * Complex.I = zu := by
    rw [← im_zChar p.g p.E m p.u, ← hzu, Complex.re_add_im]
  have hz2 : ((zu.re : ℝ) : ℂ) +
      ((gammaG p.g * (etaChar p.g m p.u / gammaG p.g) : ℝ) : ℂ) * Complex.I = zu := by
    rw [mul_div_cancel₀ _ hγ.ne', hz1]
  have hsum : zu + ((p.u * gammaG p.g : ℝ) : ℂ) * m = (p.E : ℂ) + ((gammaG p.g : ℝ) : ℂ) * m := by
    rw [hzu]; unfold zChar; push_cast; ring
  have hroot' : IsDysonRootV (hopB p.g) (p.u * gammaG p.g) p.L zu m := by
    refine ⟨hroot.1, ?_⟩
    unfold dysonRHSV
    rw [hsum]
    exact hroot.2
  have hzim : 0 ≤ zu.im := by
    rw [hzu, im_zChar]; exact (etaChar_pos p.g m hroot.1 hu).le
  have hsel : mRootV (hopB p.g) (p.u * gammaG p.g) p.L zu = m :=
    (mRootV_spec (hopB p.g) (p.u * gammaG p.g) (step2c_hopB_nonneg hg) (by positivity) p.L hL zu
      hzim).2 m hroot'
  refine ⟨fun ω => ?_, ?_⟩
  · unfold segG flowG
    simp only
    rw [hz1]
  · unfold segM flowM segMat
    simp only
    rw [hz2, hsel]
    congr 1
    unfold dysonMat
    rw [hsum]

end Step2Closure

section Step2Facts

open scoped Matrix.Norms.L2Operator

/-- The deterministic facts at an admissible step point for `W ≥ W₀` that enter the sharp local
law: the reach, the Dyson bounds (6.2) [fo:eq:propagation-dyson] at the time `u` and at the
comparison point, Lemma 5.11 [fo:lem:families] for the block traces, and admissibility. -/
private structure Step2Facts (R : PropRegime) (c N : ℝ) (W : ℕ) (q : StepPt) : Prop where
  four_le : 4 ≤ W
  reach : ∃ d : ℕ, d < R.J ∧ CmpReach R.base W d (q.at q.u)
  L3 : 3 ≤ q.L
  g0 : 0 ≤ q.g
  root : IsDysonRootV (hopB q.g) (gammaG q.g) q.L q.E (mRoot q.g q.L q.E)
  mlo : R.C⁻¹ ≤ (mRoot q.g q.L q.E).im
  Mbd : ∀ a b, ‖dysonMat (hopB q.g) (gammaG q.g) q.L q.E (mRoot q.g q.L q.E) a b‖ ≤ R.C
  Mrow : ∀ a, gammaG q.g * ∑ b,
    (‖dysonMat (hopB q.g) (gammaG q.g) q.L q.E (mRoot q.g q.L q.E) a b‖ +
      ‖dysonMat (hopB q.g) (gammaG q.g) q.L q.E (mRoot q.g q.L q.E) a b‖ ^ 2) ≤ R.C
  Minv : ∀ a, ∑ b, ‖(1 - (q.u : ℂ) • pairQ (gammaG q.g)
    (dysonMat (hopB q.g) (gammaG q.g) q.L q.E (mRoot q.g q.L q.E)))⁻¹ a b‖ ≤ R.C
  Mbd' : ∀ a b, ‖dysonMat (hopB (cmpPt (q.at q.u) q.s).g) (gammaG (cmpPt (q.at q.u) q.s).g) q.L
    (cmpPt (q.at q.u) q.s).E (mRoot (cmpPt (q.at q.u) q.s).g q.L (cmpPt (q.at q.u) q.s).E) a b‖ ≤
      R.C
  s12 : 1 / 2 ≤ q.s
  su : q.s ≤ q.u
  ut : q.u ≤ q.t
  st : q.s < q.t
  t1 : (W : ℝ) ^ (-3 : ℝ) ≤ 1 - q.t
  adm : q.ratio ^ N * zetaProp q.g W q.L q.t ≤ (W : ℝ) ^ (-c)
  cmp411 : ∀ ω : Ω W q.L, ∀ a b : Fin q.L, ‖blockTr (flowG W (q.at q.u) ω) a b‖ ≤
    R.C * ((1 - q.s) / (1 - q.u)) *
      ⨆ c : Fin q.L, ⨆ e : Fin q.L, ‖blockTr (flowG W (cmpPt (q.at q.u) q.s) ω) c e‖
  zcmp : zetaProp (cmpPt (q.at q.u) q.s).g W q.L q.s ≤ zetaProp q.g W q.L q.u

private theorem step2_facts (R : PropRegime) : ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ (c N : ℝ) (q : StepPt),
    StepAdm R c N W q → Step2Facts R c N W q := by
  obtain ⟨W₁, h₁⟩ := R.dyson
  obtain ⟨W₄, h₄⟩ := lemma411 R
  refine ⟨max 4 (max W₁ W₄), fun W hW c N q hq => ?_⟩
  have hW4 : 4 ≤ W := (le_max_left _ _).trans hW
  have hW1 : W₁ ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
  have hW4' : W₄ ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans hW)
  obtain ⟨⟨d, hd, hreach⟩, hs12, hsu, hut, hst, ht1, hadm⟩ := hq
  have hreach' : CmpReach R.base W d (q.at q.u) := CmpReach.earlier q.u hreach (hs12.trans hsu) hut
  obtain ⟨hL3, hg0, hroot, hmlo, -, hMbd, hMrow, hMinv⟩ := h₁ W hW1 d (q.at q.u) hd.le hreach'
  have hreach2 : CmpReach R.base W (d + 1) (cmpPt (q.at q.u) q.s) :=
    CmpReach.cmp q.s hreach' hs12 hsu
  obtain ⟨-, -, -, -, -, hMbd', -, -⟩ := h₁ W hW1 (d + 1) (cmpPt (q.at q.u) q.s) (by omega)
    hreach2
  have h411 := h₄ W hW4' d (q.at q.u) q.s hd hreach' hs12 hsu
  have hu0 : 0 ≤ q.u := by linarith
  have hu1 : q.u ≤ 1 := by
    have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
    have : 0 < (W : ℝ) ^ (-3 : ℝ) := Real.rpow_pos_of_pos hW0 _
    linarith
  refine ⟨hW4, ⟨d, hd, hreach'⟩, hL3, hg0, hroot, hmlo, hMbd, hMrow, hMinv q.u hu0 hu1, hMbd',
    hs12, hsu, hut, hst, ht1, hadm, fun ω => (h411 ω).2.2.2.1, (h411 (fun _ => 0)).2.2.2.2.1⟩

/-- Times, the ratio and the scales at an admissible step point: `1 ≤ R ≤ W³`,
`(1-s)/(1-u) ≤ R`, `(2W)⁻¹ ≤ ζ_u`, `ζ_u ≤ ζ_t`, `R⁶ ζ_u ≤ W^{-c}` and `0 < u < 1`. -/
private theorem step2_num {R : PropRegime} {c N : ℝ} {W : ℕ} {q : StepPt} (F : Step2Facts R c N W q)
    (hN : 20 ≤ N) (hc : 0 < c) :
    0 < q.u ∧ q.u < 1 ∧ 1 ≤ q.ratio ∧ q.ratio ≤ (W : ℝ) ^ 3 ∧
      (1 - q.s) / (1 - q.u) ≤ q.ratio ∧ (2 * (W : ℝ))⁻¹ ≤ zetaProp q.g W q.L q.u ∧
      q.ratio ^ 6 * zetaProp q.g W q.L q.u ≤ (W : ℝ) ^ (-c) ∧ zetaProp q.g W q.L q.u ≤ 1 ∧
      (2 * (W : ℝ))⁻¹ ≤ zetaProp (cmpPt (q.at q.u) q.s).g W q.L q.s := by
  have hW4 := F.four_le
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (by omega : 1 ≤ W)
  have hW3 : (W : ℝ) ^ (-3 : ℝ) = ((W : ℝ) ^ 3)⁻¹ := by
    rw [Real.rpow_neg hW0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have ht := F.t1
  rw [hW3] at ht
  have hWp : 0 < (W : ℝ) ^ 3 := by positivity
  have ht0 : 0 < 1 - q.t := lt_of_lt_of_le (inv_pos.mpr hWp) ht
  have hs0 : 0 < q.s := by linarith [F.s12]
  have hu1 : q.u < 1 := by linarith [F.ut]
  have hs1 : 0 < 1 - q.s := by linarith [F.st]
  have hR1 : 1 ≤ q.ratio := by
    unfold StepPt.ratio; rw [le_div_iff₀ ht0]; linarith [F.st]
  have hR3 : q.ratio ≤ (W : ℝ) ^ 3 := by
    unfold StepPt.ratio
    rw [div_le_iff₀ ht0]
    have : (W : ℝ) ^ 3 * ((W : ℝ) ^ 3)⁻¹ = 1 := mul_inv_cancel₀ hWp.ne'
    nlinarith
  have hRu : (1 - q.s) / (1 - q.u) ≤ q.ratio := by
    unfold StepPt.ratio
    exact div_le_div_of_nonneg_left hs1.le ht0 (by linarith [F.ut])
  have hL1 : 1 ≤ q.L := by have := F.L3; omega
  have hsf := scale_facts q.g F.g0 W q.L (by omega) hL1 q.u q.t (by linarith [F.s12, F.su])
    F.ut (by linarith)
  have hR6 : q.ratio ^ 6 ≤ q.ratio ^ N := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hR1 (by push_cast; linarith)
  have hz0 : 0 ≤ zetaProp q.g W q.L q.u := (inv_nonneg.mpr (by positivity)).trans hsf.2.2.2.1
  have hzt : q.ratio ^ 6 * zetaProp q.g W q.L q.u ≤ (W : ℝ) ^ (-c) := by
    calc q.ratio ^ 6 * zetaProp q.g W q.L q.u ≤ q.ratio ^ N * zetaProp q.g W q.L q.t :=
          mul_le_mul hR6 hsf.2.2.2.2.1 hz0 (Real.rpow_nonneg (by linarith) _)
      _ ≤ _ := F.adm
  have hz1 : zetaProp q.g W q.L q.u ≤ 1 := by
    have h1 : 1 ≤ q.ratio ^ 6 := one_le_pow₀ hR1
    have h2 : (W : ℝ) ^ (-c) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
    nlinarith
  have hg' : 0 ≤ (cmpPt (q.at q.u) q.s).g := by
    change 0 ≤ gCmp q.g q.s q.u
    unfold gCmp; exact mul_nonneg F.g0 (Real.sqrt_nonneg _)
  have hsf' := scale_facts (cmpPt (q.at q.u) q.s).g hg' W q.L (by omega) hL1 q.s q.s hs0.le le_rfl
    (by linarith [F.st, F.ut])
  exact ⟨by linarith [F.s12, F.su], hu1, hR1, hR3, hRu, hsf.2.2.2.1, hzt, hz1, hsf'.2.2.2.1⟩

end Step2Facts

/-! ### The domain of the averaging inputs at the characteristic -/

section Step2Dom

/-- `x = (q.at q.u, η_u)` for a step point `q ∈ S W`. -/
private def step2Gen (S : ℕ → Set StepPt) (W : ℕ) (x : FlowPt × ℝ) (q : StepPt) : Prop :=
  q ∈ S W ∧ x = (q.at q.u, etaChar q.g (mRoot q.g q.L q.E) q.u)

/-- The characteristic pairs of the step points of `S W`, for `W ≥ W₀`. -/
private def step2Dom (S : ℕ → Set StepPt) (W₀ W : ℕ) : Set (FlowPt × ℝ) :=
  {x | W₀ ≤ W ∧ ∃ q, step2Gen S W x q}

/-- The smallest ratio `R` of a step point at the pair `x` (at least `1`). -/
private def step2Rinf (S : ℕ → Set StepPt) (W : ℕ) (x : FlowPt × ℝ) : ℝ :=
  max 1 (sInf {r | ∃ q, step2Gen S W x q ∧ r = q.ratio})

private theorem step2_ratio_ge {R : PropRegime} {c N : ℝ} {W : ℕ} (hW : 1 ≤ W) {q : StepPt}
    (hq : StepAdm R c N W q) : 1 ≤ q.ratio := by
  obtain ⟨-, -, -, -, hst, ht, -⟩ := hq
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have ht0 : 0 < 1 - q.t := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) ht
  unfold StepPt.ratio; rw [le_div_iff₀ ht0]; linarith

private theorem step2_rinf {R : PropRegime} {c N : ℝ} {S : ℕ → Set StepPt}
    (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q}) {W : ℕ} (hW : 1 ≤ W) {x : FlowPt × ℝ} {q : StepPt}
    (hq : step2Gen S W x q) :
    1 ≤ step2Rinf S W x ∧ step2Rinf S W x ≤ q.ratio ∧
      ∃ q', step2Gen S W x q' ∧ q'.ratio ≤ 2 * step2Rinf S W x := by
  set T := {r | ∃ q, step2Gen S W x q ∧ r = q.ratio} with hT
  have hge : ∀ r ∈ T, 1 ≤ r := by
    rintro r ⟨q', hq', rfl⟩; exact step2_ratio_ge hW (hS W hq'.1)
  have hne : T.Nonempty := ⟨q.ratio, q, hq, rfl⟩
  have hbdd : BddBelow T := ⟨1, hge⟩
  have hinf1 : 1 ≤ sInf T := le_csInf hne hge
  have hR : step2Rinf S W x = sInf T := max_eq_right hinf1
  refine ⟨le_max_left _ _, ?_, ?_⟩
  · rw [hR]; exact csInf_le hbdd ⟨q, hq, rfl⟩
  · obtain ⟨r, ⟨q', hq', rfl⟩, hr⟩ := exists_lt_of_csInf_lt hne (show sInf T < 2 * sInf T by
      linarith)
    exact ⟨q', hq', by rw [hR]; exact hr.le⟩

private theorem step2_dom_segAdm {R : PropRegime} {c N : ℝ} {S : ℕ → Set StepPt}
    (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q}) (Wt W : ℕ) (x : FlowPt × ℝ)
    (hx : x ∈ step2Dom S Wt W) : SegAdm R.base R.J W x := by
  obtain ⟨-, q, hqS, rfl⟩ := hx
  obtain ⟨⟨d, hd, hreach⟩, hs12, hsu, hut, -, -, -⟩ := hS W hqS
  exact ⟨d, hd.le, CmpReach.earlier q.u hreach (hs12.trans hsu) hut, Or.inl rfl⟩

/-- `2 W^{-(D+1)} ≤ W^{-D}` for `W ≥ 2`. -/
private theorem step2_two' (W : ℕ) (hW : 2 ≤ W) (D : ℝ) :
    ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) ≤
      ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hW2 : (2 : ℝ) ≤ W := by exact_mod_cast hW
  rw [← ENNReal.ofReal_add (Real.rpow_nonneg hW0.le _) (Real.rpow_nonneg hW0.le _)]
  apply ENNReal.ofReal_le_ofReal
  have e : (W : ℝ) ^ (-(D + 1)) = (W : ℝ) ^ (-D) * (W : ℝ)⁻¹ := by
    rw [show -(D + 1) = -D + (-1) by ring, Real.rpow_add hW0, Real.rpow_neg_one]
  have hpos : 0 < (W : ℝ) ^ (-D) := Real.rpow_pos_of_pos hW0 _
  have hinv : (W : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hW2
  rw [e]; nlinarith

/-- `n` events of probability at most `W^{-(D+C)}`, `n ≤ W^C`, `W ≥ 1`. -/
private theorem step2_card_bound (W : ℕ) (hW : 1 ≤ W) (C D : ℝ) (n : ℝ) (hn : n ≤ (W : ℝ) ^ C) :
    n * (W : ℝ) ^ (-(D + C)) ≤ (W : ℝ) ^ (-D) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  calc n * (W : ℝ) ^ (-(D + C)) ≤ (W : ℝ) ^ C * (W : ℝ) ^ (-(D + C)) :=
        mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hW0.le _)
    _ = (W : ℝ) ^ (-D) := by rw [← Real.rpow_add hW0]; ring_nf

/-- Traceless entries from (5.30) [gc:eq:haar] per pair of blocks and the sampling of
Lemma 5.10(b) [fo:lem:sampling-continuity]: the maximum over all entries inside the probability. -/
private theorem step2_traceless (base : ℕ → Set FlowPt) (J : ℕ) (hsamp : SamplingInput base J)
    (Dom : ℕ → Set (FlowPt × ℝ)) (hDom : ∀ W x, x ∈ Dom W → SegAdm base J W x)
    (Ψ K χ : ℕ → FlowPt × ℝ → ℝ) (hΨK : ∀ W x, x ∈ Dom W → Ψ W x ≤ K W x * χ W x)
    (hKχ : ∀ W x, x ∈ Dom W → (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ K W x * χ W x)
    (hii : ∀ ε D : ℝ, 0 < ε → 0 < D → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ x ∈ Dom W,
      ∀ a b : Fin x.1.L, μ W x.1.L {ω | ∃ i j : Fin W, (W : ℝ) ^ ε * Ψ W x <
        ‖segG W x ω (a, i) (b, j) - if i = j then blockTr (segG W x ω) a b else 0‖} ≤
        ENNReal.ofReal ((W : ℝ) ^ (-D))) :
    PrecMax (fun x : FlowPt × ℝ => x.1.L) Dom
      (Λ := fun W x => (Fin x.1.L × Fin W) × (Fin x.1.L × Fin W))
      (fun W x e ω => segG W x ω e.1 e.2 -
        if e.1.2 = e.2.2 then blockTr (segG W x ω) e.1.1 e.2.1 else 0)
      (fun W x _ => K W x * χ W x) := by
  intro ε D hε hD
  obtain ⟨CS, Cs, W₂, hW₂⟩ := hsamp.2 1 (D + 1) one_pos (by linarith)
  set C' := max CS 0 with hC'
  set Cs' := max Cs 0 with hCs'
  obtain ⟨W₁, hW₁⟩ := hii (ε / 2) (D + 1 + C') (by positivity)
    (by have := le_max_right CS 0; linarith)
  have ht : Tendsto (fun W : ℕ => (W : ℝ) ^ (ε / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  obtain ⟨W₃, hW₃⟩ := eventually_atTop.mp (ht.eventually_ge_atTop (Cs' + 1))
  refine ⟨max (max W₁ W₂) (max W₃ 2), fun W hW x hx => ?_⟩
  have hW1 : W₁ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hW2 : W₂ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hW3 : W₃ ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
  have hW4 : 2 ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans hW)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hWr1 : (1 : ℝ) ≤ W := by exact_mod_cast (by omega : 1 ≤ W)
  obtain ⟨S₁, S₂, -, hS₂, -, hsb, -⟩ := hW₂ W hW2 x (hDom W x hx)
  set X : (Fin x.1.L × Fin W) × (Fin x.1.L × Fin W) → Ω W x.1.L → ℂ := fun e ω =>
    segG W x ω e.1 e.2 - if e.1.2 = e.2.2 then blockTr (segG W x ω) e.1.1 e.2.1 else 0 with hX
  set Bad := {ω : Ω W x.1.L | ∃ l, Cs * (⨆ s : S₂, ‖X s ω‖ / 1) + (W : ℝ) ^ (-(1 : ℝ)) <
    ‖X l ω‖ / 1} with hBad
  set B : (Fin x.1.L × Fin W) × (Fin x.1.L × Fin W) → Set (Ω W x.1.L) := fun s =>
    {ω | ∃ i j : Fin W, (W : ℝ) ^ (ε / 2) * Ψ W x <
      ‖segG W x ω (s.1.1, i) (s.2.1, j) - if i = j then blockTr (segG W x ω) s.1.1 s.2.1 else 0‖}
    with hB
  have hKχ0 : 0 < K W x * χ W x := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) (hKχ W x hx)
  have hWε2 := hW₃ W hW3
  have hWε : (W : ℝ) ^ ε = (W : ℝ) ^ (ε / 2) * (W : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_add hW0]; ring_nf
  have hdel : (W : ℝ) ^ (-(1 : ℝ)) ≤ K W x * χ W x := by
    refine le_trans ?_ (hKχ W x hx)
    exact Real.rpow_le_rpow_of_exponent_le hWr1 (by norm_num)
  have hsub : {ω | ∃ l, (W : ℝ) ^ ε * (K W x * χ W x) < ‖X l ω‖} ⊆
      Bad ∪ ⋃ s ∈ S₂, B s := by
    rintro ω ⟨l, hl⟩
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hcon
    obtain ⟨hnb, hns⟩ := hcon
    have hs : ∀ s ∈ S₂, ‖X s ω‖ ≤ (W : ℝ) ^ (ε / 2) * Ψ W x := by
      intro s hs
      have := hns s hs
      simp only [hB, Set.mem_ofPred_eq, not_exists, not_lt] at this
      exact this s.1.2 s.2.2
    have hsup0 : 0 ≤ ⨆ s : S₂, ‖X s ω‖ / 1 := Real.iSup_nonneg fun _ => by positivity
    have hsup : (⨆ s : S₂, ‖X s ω‖ / 1) ≤ (W : ℝ) ^ (ε / 2) * (K W x * χ W x) := by
      refine Real.iSup_le (fun s => ?_) (by positivity)
      rw [div_one]
      exact (hs s s.2).trans (mul_le_mul_of_nonneg_left (hΨK W x hx) (by positivity))
    have hnb' : ‖X l ω‖ / 1 ≤ Cs * (⨆ s : S₂, ‖X s ω‖ / 1) + (W : ℝ) ^ (-(1 : ℝ)) := by
      simp only [hBad, Set.mem_ofPred_eq, not_exists, not_lt] at hnb
      exact hnb l
    rw [div_one] at hnb'
    have h1 : Cs * (⨆ s : S₂, ‖X s ω‖ / 1) ≤ Cs' * ((W : ℝ) ^ (ε / 2) * (K W x * χ W x)) :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hsup0).trans
        (mul_le_mul_of_nonneg_left hsup (le_max_right _ _))
    have h2 : Cs' * ((W : ℝ) ^ (ε / 2) * (K W x * χ W x)) + K W x * χ W x ≤
        (W : ℝ) ^ ε * (K W x * χ W x) := by
      rw [hWε]
      have : Cs' * (W : ℝ) ^ (ε / 2) + 1 ≤ (W : ℝ) ^ (ε / 2) * (W : ℝ) ^ (ε / 2) := by
        have h1' : (1 : ℝ) ≤ (W : ℝ) ^ (ε / 2) := Real.one_le_rpow hWr1 (by positivity)
        nlinarith [le_max_right Cs 0]
      nlinarith
    linarith
  calc μ W x.1.L {ω | ∃ l, (W : ℝ) ^ ε * (K W x * χ W x) < ‖X l ω‖}
      ≤ μ W x.1.L (Bad ∪ ⋃ s ∈ S₂, B s) := measure_mono hsub
    _ ≤ μ W x.1.L Bad + ∑ s ∈ S₂, μ W x.1.L (B s) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_biUnion_finset_le _ _))
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) +
          ∑ _s ∈ S₂, ENNReal.ofReal ((W : ℝ) ^ (-(D + 1 + C'))) := by
        gcongr with s hs
        · exact hsb
        · exact hW₁ W hW1 x hx s.1.1 s.2.1
    _ = ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) +
          ENNReal.ofReal ((S₂.card : ℝ) * (W : ℝ) ^ (-(D + 1 + C'))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) := by
        gcongr
        exact step2_card_bound W (by omega) C' (D + 1) _ (hS₂.trans
          (Real.rpow_le_rpow_of_exponent_le hWr1 (le_max_left _ _)))
    _ ≤ _ := step2_two' W hW4 D

end Step2Dom

section Step2LocalDet

/-- `pairQ (uγ) M = u • pairQ γ M`. -/
private theorem step2_pairQ_smul {L : ℕ} (u γ : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) :
    pairQ (u * γ) M = (u : ℂ) • pairQ γ M := by
  ext a b
  simp only [pairQ, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast; ring

/-- The two identities of (5.32) [gc:eq:scalar] with the Dyson bounds (6.2)
[fo:eq:propagation-dyson] at a step point: with `|R| ≤ ρ`, `|⟨G⟩| ≤ Γ`, `|⟨G - M⟩_cc| ≤ U`,
`|⟨G - M⟩_aa| ≤ C(ρ + CU(ρ + CΓU))` and `|⟨G - M⟩_ab| ≤ ρ + CUΓ`. -/
private theorem step2_local_det {R : PropRegime} {c N : ℝ} {W : ℕ} {q : StepPt}
    (F : Step2Facts R c N W q)
    (hN : 20 ≤ N) (hc : 0 < c) (ω : Ω W q.L) {ρ Γ U : ℝ}
    (hρ : ∀ a b, ‖flowRes W (q.at q.u) ω a b‖ ≤ ρ)
    (hΓ : ∀ a b, ‖blockTr (flowG W (q.at q.u) ω) a b‖ ≤ Γ)
    (hU : ∀ e, ‖blockTr (flowG W (q.at q.u) ω - flowM W (q.at q.u)) e e‖ ≤ U) (hU0 : 0 ≤ U)
    (hΓ0 : 0 ≤ Γ) :
    (∀ a, ‖blockTr (flowG W (q.at q.u) ω - flowM W (q.at q.u)) a a‖ ≤
      R.C * (ρ + R.C * U * (ρ + R.C * Γ * U))) ∧
    ∀ a b, ‖blockTr (flowG W (q.at q.u) ω - flowM W (q.at q.u)) a b‖ ≤ ρ + R.C * U * Γ := by
  obtain ⟨hu0, hu1, -, -, -, -, -, -, -⟩ := step2_num F hN hc
  have hW1 : 1 ≤ W := by have := F.four_le; omega
  have hL1 : 1 ≤ q.L := by have := F.L3; omega
  have hγ : 0 < gammaG q.g := by unfold gammaG; positivity
  have hC1 := R.one_le_C
  set m := mRoot q.g q.L q.E with hmdef
  have hmpos : 0 < m.im := lt_of_lt_of_le (inv_pos.mpr (lt_of_lt_of_le one_pos hC1)) F.mlo
  set M := dysonMat (hopB q.g) (gammaG q.g) q.L q.E m with hMdef
  set β := q.u * gammaG q.g with hβdef
  have hβ : 0 ≤ β := by positivity
  set zu := zChar q.g q.E m q.u with hzu
  have hsum : zu + ((β : ℝ) : ℂ) * m = (q.E : ℂ) + ((gammaG q.g : ℝ) : ℂ) * m := by
    rw [hzu, hβdef]; unfold zChar; push_cast; ring
  have hMz : dysonMat (hopB q.g) β q.L zu m = M := by
    rw [hMdef]; unfold dysonMat; rw [hsum]
  have hzim : 0 < zu.im := by rw [hzu, im_zChar]; exact etaChar_pos q.g m hmpos hu1
  have hroot' : IsDysonRootV (hopB q.g) β q.L zu m := by
    refine ⟨F.root.1, ?_⟩
    unfold dysonRHSV
    have h2 := F.root.2
    unfold dysonRHSV at h2
    rw [hsum]
    simpa using h2
  have hw : 0 < (zu + (β : ℂ) * m).im := by
    have : (zu + (β : ℂ) * m).im = zu.im + β * m.im := by simp
    rw [this]; positivity
  have hdiag : ∀ e, dysonMat (hopB q.g) β q.L zu m e e = m := fun e => by
    rw [dysonMat_diag _ _ _ hL1 _ _ hw e]; exact hroot'.2.symm
  have hθ : β * m.im / (zu.im + β * m.im) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  have hinv : IsUnit (1 - pairQ β M) := by
    rw [← hMz]
    exact step2_isUnit_one_sub _ hθ fun a => le_of_eq (step2_pairQ_row _ _ hβ _ zu m hzim hmpos
      hdiag a)
  have hrowinv : ∀ a, ∑ e, ‖(1 - pairQ β M)⁻¹ a e‖ ≤ R.C := by
    intro a
    rw [hβdef, step2_pairQ_smul]
    exact F.Minv a
  have hrowM : ∀ a, β * ∑ e, ‖M a e‖ ≤ R.C := by
    intro a
    have h := F.Mrow a
    have h1 : gammaG q.g * ∑ e, ‖M a e‖ ≤ gammaG q.g * ∑ e, (‖M a e‖ + ‖M a e‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun e _ => by nlinarith [norm_nonneg (M a e)])
        hγ.le
    have h2 : q.u * (gammaG q.g * ∑ e, ‖M a e‖) ≤ gammaG q.g * ∑ e, ‖M a e‖ :=
      mul_le_of_le_one_left (mul_nonneg hγ.le (Finset.sum_nonneg fun _ _ => norm_nonneg _))
        (by linarith)
    calc β * ∑ e, ‖M a e‖ = q.u * (gammaG q.g * ∑ e, ‖M a e‖) := by rw [hβdef]; ring
      _ ≤ _ := h2.trans (h1.trans h)
  set G := flowG W (q.at q.u) ω with hG
  have hid : ∀ a b, blockTr (G - flowM W (q.at q.u)) a b = -flowRes W (q.at q.u) ω a b +
      (β : ℂ) * ∑ e, M a e * blockTr (G - flowM W (q.at q.u)) e e * blockTr G e b := by
    intro a b
    have h := scalar_identity W hW1 (q.at q.u) hmpos hu1 ω a b
    rw [hβdef]
    push_cast at h ⊢
    exact h
  have hgg : ∀ e b, blockTr G e b = M e b + blockTr (G - flowM W (q.at q.u)) e b := by
    intro e b
    have hk : blockTr (flowM W (q.at q.u)) e b = M e b := step2_blockTr_kron W q.L hW1 M e b
    rw [step2_blockTr_sub, hk]; ring
  exact step2_closure M (step2_dysonMat_symm _ _ _ _ _) β hβ
    (fun a b => blockTr (G - flowM W (q.at q.u)) a b) (fun a b => blockTr G a b)
    (fun a b => flowRes W (q.at q.u) ω a b) hid hgg hρ hΓ hrowM hinv hrowinv hU hU0 hΓ0

end Step2LocalDet

section Step2LocalProb

/-- Domination at all small accuracies `ε ≤ ε₀` gives domination. -/
private theorem step2_prec_of_small {ι : Type*} {vol : ι → ℕ} {Dom : ℕ → Set ι} {Λ : ℕ → ι → Type*}
    {X : (W : ℕ) → (p : ι) → Λ W p → Ω W (vol p) → ℂ} {Y : (W : ℕ) → (p : ι) → Λ W p → ℝ}
    (hY : ∃ Wy : ℕ, ∀ W : ℕ, Wy ≤ W → ∀ p ∈ Dom W, ∀ l, 0 ≤ Y W p l) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (h : ∀ ε D : ℝ, 0 < ε → ε ≤ ε₀ → 0 < D → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ p ∈ Dom W,
      μ W (vol p) {ω | ∃ l : Λ W p, (W : ℝ) ^ ε * Y W p l < ‖X W p l ω‖} ≤
        ENNReal.ofReal ((W : ℝ) ^ (-D))) :
    PrecMax vol Dom X Y := by
  intro ε D hε hD
  obtain ⟨Wy, hWy⟩ := hY
  obtain ⟨W₀, hW⟩ := h (min ε ε₀) D (lt_min hε hε₀) (min_le_right _ _) hD
  refine ⟨max (max W₀ Wy) 1, fun W hW' p hp => (measure_mono ?_).trans
    (hW W ((le_max_left _ _).trans (le_of_max_le_left hW')) p hp)⟩
  rintro ω ⟨l, hl⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_of_max_le_right hW'
  refine ⟨l, lt_of_le_of_lt (mul_le_mul_of_nonneg_right ?_
    (hWy W ((le_max_right _ _).trans (le_of_max_le_left hW')) p hp l)) hl⟩
  exact Real.rpow_le_rpow_of_exponent_le hW1 (min_le_left _ _)

/-- A fixed constant is eventually below `W^ε`. -/
private theorem step2_eventually_ge (A ε : ℝ) (hε : 0 < ε) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → A ≤ (W : ℝ) ^ ε := by
  have ht : Tendsto (fun W : ℕ => (W : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  exact eventually_atTop.mp (ht.eventually_ge_atTop A)

/-- The sharp Hilbert–Schmidt bound of (C.15) [fo:eq:step2]: `W⁻²‖G_{ab}‖²_HS = 𝒦₂ + D₂ ≺ ζ_u`,
from the mixed pair with loss `R⁶` and the primitive loop of length two. -/
private theorem step2_hs_out (R : PropRegime) (c N : ℝ) (hc : 0 < c) (hN : 20 ≤ N)
    (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q}) {cw θ : ℝ} (hcw0 : 0 ≤ cw)
    (hpair : PrecMax StepPt.L S (Λ := fun _ q => Fin q.L × Fin q.L)
      (fun W q ab ω => flowErr W (q.at q.u) ![ab.1, ab.2] ![true, false] ω)
      (fun W q ab => q.ratio ^ 6 * zetaProp q.g W q.L q.u ^ 2 *
        weightFn cw θ 1 W (ellProp q.g q.L q.u) (cycDist ab.1 ab.2))) :
    PrecMax StepPt.L S (Λ := fun _ q => Fin q.L × Fin q.L)
      (fun W q ab ω => ((blockHS2 (flowG W (q.at q.u) ω) ab.1 ab.2 : ℝ) : ℂ))
      (fun W q _ => (W : ℝ) ^ 2 * zetaProp q.g W q.L q.u) := by
  intro ε D hε hD
  obtain ⟨Wf, hf⟩ := step2_facts R
  obtain ⟨W₁, hW₁⟩ := hpair (ε / 2) D (by positivity) hD
  obtain ⟨W₂, hW₂⟩ := R.prim 2 (ε / 2) (by positivity)
  obtain ⟨W₃, hW₃⟩ := step2_eventually_ge 3 (ε / 2) (by positivity)
  refine ⟨max (max Wf W₁) (max W₂ W₃), fun W hW q hq => ?_⟩
  have hWf : Wf ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hW1' : W₁ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hW2' : W₂ ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
  have hW3' : W₃ ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans hW)
  have F := hf W hWf c N q (hS W hq)
  obtain ⟨hu0, hu1, hR1, -, -, hζW, hR6, hζ1, -⟩ := step2_num F hN hc
  have hW1 : 1 ≤ W := by have := F.four_le; omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  obtain ⟨d, hd, hreach⟩ := F.reach
  set ζ := zetaProp q.g W q.L q.u with hζ
  have hζ0 : 0 < ζ := lt_of_lt_of_le (by positivity) hζW
  refine le_trans (measure_mono ?_) (hW₁ W hW1' q hq)
  intro ω hω
  obtain ⟨ab, hab⟩ := hω
  by_contra hcon
  simp only [Set.mem_ofPred_eq, not_exists, not_lt] at hcon
  have hD₂ := hcon (ab.2, ab.1)
  have hprim := hW₂ W hW2' d (q.at q.u) hd.le hreach 2 le_rfl le_rfl ![ab.2, ab.1] ![true, false]
  have hℓ : 0 < ellProp q.g q.L q.u := lt_of_lt_of_le one_pos
    (scale_facts q.g F.g0 W q.L hW1 (by have := F.L3; omega) q.u q.u hu0.le le_rfl hu1).1
  have hw2 : weightFn cw θ 1 W (ellProp q.g q.L q.u) (cycDist ab.2 ab.1) ≤ 2 :=
    step2_weight_le_two hcw0 zero_le_one hW1 hℓ (Nat.cast_nonneg _)
  have hWc : (W : ℝ) ^ (-c) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1r (by linarith)
  have hR6' : q.ratio ^ 6 * ζ ≤ 1 := hR6.trans hWc
  have hWe : 0 ≤ (W : ℝ) ^ (ε / 2) := by positivity
  -- `ℒ₂(b, a) = D₂ + 𝒦₂`
  have hL2 : ‖loopTr (flowG W (q.at q.u) ω) ![ab.2, ab.1] ![true, false]‖ ≤
      (W : ℝ) ^ (ε / 2) * (3 * ζ) := by
    have e : loopTr (flowG W (q.at q.u) ω) ![ab.2, ab.1] ![true, false] =
        flowErr W (q.at q.u) ![ab.2, ab.1] ![true, false] ω +
          primLoop (q.at q.u).g W (q.at q.u).L (q.at q.u).E
            (mRoot (q.at q.u).g (q.at q.u).L (q.at q.u).E) (q.at q.u).u ![ab.2, ab.1]
            ![true, false] := by
      unfold flowErr; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖flowErr W (q.at q.u) ![ab.2, ab.1] ![true, false] ω‖ ≤
        (W : ℝ) ^ (ε / 2) * (2 * ζ) := by
      refine hD₂.trans (mul_le_mul_of_nonneg_left ?_ hWe)
      change q.ratio ^ 6 * ζ ^ 2 * weightFn cw θ 1 W (ellProp q.g q.L q.u) (cycDist ab.2 ab.1) ≤ _
      have h0 : 0 ≤ q.ratio ^ 6 * ζ ^ 2 := by positivity
      calc q.ratio ^ 6 * ζ ^ 2 * weightFn cw θ 1 W (ellProp q.g q.L q.u) (cycDist ab.2 ab.1)
          ≤ q.ratio ^ 6 * ζ ^ 2 * 2 := mul_le_mul_of_nonneg_left hw2 h0
        _ = (q.ratio ^ 6 * ζ) * ζ * 2 := by ring
        _ ≤ 1 * ζ * 2 := by gcongr
        _ = 2 * ζ := by ring
    have h2 : ‖primLoop (q.at q.u).g W (q.at q.u).L (q.at q.u).E
        (mRoot (q.at q.u).g (q.at q.u).L (q.at q.u).E) (q.at q.u).u ![ab.2, ab.1]
          ![true, false]‖ ≤ (W : ℝ) ^ (ε / 2) * ζ := by
      have := hprim
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one] at this
      exact this
    linarith
  have hhs : ((W : ℝ) ^ 2)⁻¹ * blockHS2 (flowG W (q.at q.u) ω) ab.1 ab.2 ≤
      (W : ℝ) ^ (ε / 2) * (3 * ζ) := by
    have e := step2_loopTr_two_hs (flowG W (q.at q.u) ω) ab.2 ab.1
    rw [e, Complex.norm_real, Real.norm_of_nonneg (by unfold blockHS2; positivity)] at hL2
    exact hL2
  have hW3 := hW₃ W hW3'
  have hsplit : (W : ℝ) ^ ε = (W : ℝ) ^ (ε / 2) * (W : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_add hW0]; ring_nf
  have hfin : blockHS2 (flowG W (q.at q.u) ω) ab.1 ab.2 ≤ (W : ℝ) ^ ε * ((W : ℝ) ^ 2 * ζ) := by
    rw [inv_mul_le_iff₀ (by positivity)] at hhs
    calc blockHS2 (flowG W (q.at q.u) ω) ab.1 ab.2 ≤ (W : ℝ) ^ 2 * ((W : ℝ) ^ (ε / 2) * (3 * ζ)) :=
          hhs
      _ ≤ (W : ℝ) ^ 2 * ((W : ℝ) ^ (ε / 2) * ((W : ℝ) ^ (ε / 2) * ζ)) := by gcongr
      _ = _ := by rw [hsplit]; ring
  rw [Complex.norm_real, Real.norm_of_nonneg (by unfold blockHS2; positivity)] at hab
  exact absurd hab (not_lt.mpr hfin)

/-- The a priori bound `|⟨G_u⟩_{ab}| ≤ 2C² R` from Lemma 5.11 [fo:lem:families] and the
centered block traces (5.22) [gc:eq:one-step-input] at the comparison point. -/
private theorem step2_apriori (R : PropRegime) (c N : ℝ) (hc : 0 < c) (hN : 20 ≤ N)
    (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q}) {cp θ : ℝ}
    (hcmp : OneStepInput cp θ (fun q : StepPt => cmpPt (q.at q.u) q.s) S) :
    ∀ ε D : ℝ, 0 < ε → ε ≤ c → 0 < D → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ q ∈ S W,
      μ W q.L {ω | ∃ ab : Fin q.L × Fin q.L, (W : ℝ) ^ ε * (2 * R.C ^ 2 * q.ratio) <
        ‖blockTr (flowG W (q.at q.u) ω) ab.1 ab.2‖} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  intro ε D hε hεc hD
  obtain ⟨Wf, hf⟩ := step2_facts R
  obtain ⟨W₁, hW₁⟩ := hcmp.avg ε D hε hD
  refine ⟨max Wf W₁, fun W hW q hq => ?_⟩
  have F := hf W (le_of_max_le_left hW) c N q (hS W hq)
  obtain ⟨hu0, hu1, hR1, -, hRu, hζW, hR6, hζ1, -⟩ := step2_num F hN hc
  have hW1 : 1 ≤ W := by have := F.four_le; omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hC1 := R.one_le_C
  refine le_trans (measure_mono ?_) (hW₁ W (le_of_max_le_right hW) q hq)
  intro ω hω
  obtain ⟨ab, hab⟩ := hω
  by_contra hcon0
  have hcon : ∀ l : Fin q.L × Fin q.L, ‖blockTr (flowG W (cmpPt (q.at q.u) q.s) ω -
      flowM W (cmpPt (q.at q.u) q.s)) l.1 l.2‖ ≤ (W : ℝ) ^ ε * flowZeta W (cmpPt (q.at q.u) q.s) :=
    fun l => not_lt.mp fun h => hcon0 ⟨l, h⟩
  -- the comparison traces
  have hcm : ∀ c' e : Fin q.L, ‖blockTr (flowG W (cmpPt (q.at q.u) q.s) ω) c' e‖ ≤ 2 * R.C := by
    intro c' e
    have h1 := hcon (c', e)
    have hk : blockTr (flowM W (cmpPt (q.at q.u) q.s)) c' e =
        dysonMat (hopB (cmpPt (q.at q.u) q.s).g) (gammaG (cmpPt (q.at q.u) q.s).g) q.L
          (cmpPt (q.at q.u) q.s).E (mRoot (cmpPt (q.at q.u) q.s).g q.L (cmpPt (q.at q.u) q.s).E)
          c' e := step2_blockTr_kron W q.L hW1 _ c' e
    have hsub := step2_blockTr_sub (flowG W (cmpPt (q.at q.u) q.s) ω)
      (flowM W (cmpPt (q.at q.u) q.s)) c' e
    rw [hk] at hsub
    have hz : (W : ℝ) ^ ε * flowZeta W (cmpPt (q.at q.u) q.s) ≤ 1 := by
      change (W : ℝ) ^ ε * zetaProp (cmpPt (q.at q.u) q.s).g W q.L q.s ≤ 1
      have h2 : zetaProp (cmpPt (q.at q.u) q.s).g W q.L q.s ≤ (W : ℝ) ^ (-c) := by
        have h3 : 1 ≤ q.ratio ^ 6 := one_le_pow₀ hR1
        have hz0 : 0 ≤ zetaProp q.g W q.L q.u := le_trans (by positivity) hζW
        calc zetaProp (cmpPt (q.at q.u) q.s).g W q.L q.s ≤ zetaProp q.g W q.L q.u := F.zcmp
          _ ≤ q.ratio ^ 6 * zetaProp q.g W q.L q.u := le_mul_of_one_le_left hz0 h3
          _ ≤ _ := hR6
      calc (W : ℝ) ^ ε * zetaProp (cmpPt (q.at q.u) q.s).g W q.L q.s ≤
          (W : ℝ) ^ ε * (W : ℝ) ^ (-c) := by gcongr
        _ = (W : ℝ) ^ (ε - c) := by rw [← Real.rpow_add hW0]; ring_nf
        _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1r (by linarith)
    have h4 : blockTr (flowG W (cmpPt (q.at q.u) q.s) ω) c' e =
        blockTr (flowG W (cmpPt (q.at q.u) q.s) ω - flowM W (cmpPt (q.at q.u) q.s)) c' e +
          dysonMat (hopB (cmpPt (q.at q.u) q.s).g) (gammaG (cmpPt (q.at q.u) q.s).g) q.L
            (cmpPt (q.at q.u) q.s).E (mRoot (cmpPt (q.at q.u) q.s).g q.L (cmpPt (q.at q.u) q.s).E)
            c' e := by rw [hsub]; ring
    rw [h4]
    refine (norm_add_le _ _).trans ?_
    have := F.Mbd' c' e
    linarith
  have hsup : (⨆ c' : Fin q.L, ⨆ e : Fin q.L,
      ‖blockTr (flowG W (cmpPt (q.at q.u) q.s) ω) c' e‖) ≤ 2 * R.C :=
    Real.iSup_le (fun c' => Real.iSup_le (fun e => hcm c' e) (by positivity)) (by positivity)
  have hb := F.cmp411 ω ab.1 ab.2
  have hRu0 : 0 ≤ (1 - q.s) / (1 - q.u) := div_nonneg (by linarith [F.su]) (by linarith)
  have hfin : ‖blockTr (flowG W (q.at q.u) ω) ab.1 ab.2‖ ≤
      (W : ℝ) ^ ε * (2 * R.C ^ 2 * q.ratio) := by
    calc ‖blockTr (flowG W (q.at q.u) ω) ab.1 ab.2‖ ≤ R.C * ((1 - q.s) / (1 - q.u)) * (2 * R.C) :=
          hb.trans (mul_le_mul_of_nonneg_left hsup (by positivity))
      _ ≤ R.C * q.ratio * (2 * R.C) := by gcongr
      _ = 2 * R.C ^ 2 * q.ratio := by ring
      _ ≤ (W : ℝ) ^ ε * (2 * R.C ^ 2 * q.ratio) :=
          le_mul_of_one_le_left (by positivity) (Real.one_le_rpow hW1r hε.le)
  exact absurd hab (not_lt.mpr hfin)

end Step2LocalProb

section Step2LocalAvg

/-- On the characteristic the residual (5.28) [gc:eq:residual-input] of the pair `(p, η_u)` is the
residual of the point. -/
private theorem step2_segRes_eq (W : ℕ) (p : FlowPt) (hL : 3 ≤ p.L) (hg : 0 ≤ p.g)
    (hroot : IsDysonRootV (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E)) (hu0 : 0 < p.u)
    (hu : p.u < 1) (ω : Ω W p.L) (a b : Fin p.L) :
    segRes W (p, etaChar p.g (mRoot p.g p.L p.E) p.u) ω a b = flowRes W p ω a b := by
  obtain ⟨hG, hM⟩ := step2_seg_lower W p hL hg hroot hu0 hu
  have hz : (((zChar p.g p.E (mRoot p.g p.L p.E) p.u).re : ℝ) : ℂ) +
      ((etaChar p.g (mRoot p.g p.L p.E) p.u : ℝ) : ℂ) * Complex.I =
      zChar p.g p.E (mRoot p.g p.L p.E) p.u := by
    rw [← im_zChar p.g p.E (mRoot p.g p.L p.E) p.u, Complex.re_add_im]
  unfold segRes flowRes
  simp only
  rw [hM, hG ω, hz]

/-- The pair `(q.at q.u, η_u)` of a step point. -/
private def step2X (q : StepPt) : FlowPt × ℝ := (q.at q.u, etaChar q.g (mRoot q.g q.L q.E) q.u)

/-- The scale `ζ_u` at a pair. -/
private def step2ZetaX (W : ℕ) (x : FlowPt × ℝ) : ℝ := zetaProp x.1.g W x.1.L x.1.u

/-- The averaging inputs at the characteristic: the traceless entries `≺ 2ζ_u^{1/2}` (5.30)
[gc:eq:haar], the residual of the first use of (5.29) [gc:eq:averaging-input] with
`K = 4C² R`, and the off-diagonal traces `|⟨G⟩_{ab}| ≤ C + 1` from the scalar identity (5.32)
[gc:eq:scalar]. -/
private theorem step2_avg1 (R : PropRegime) (I : PropInputs R.base R.J) (c N : ℝ) (hc : 0 < c)
    (hN : 20 ≤ N) (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q}) {cp θ : ℝ}
    (hcmp : OneStepInput cp θ (fun q : StepPt => cmpPt (q.at q.u) q.s) S) (h1 : Step1Out S)
    (hHS : PrecMax StepPt.L S (Λ := fun _ q => Fin q.L × Fin q.L)
      (fun W q ab ω => ((blockHS2 (flowG W (q.at q.u) ω) ab.1 ab.2 : ℝ) : ℂ))
      (fun W q _ => (W : ℝ) ^ 2 * zetaProp q.g W q.L q.u)) :
    ∃ Wt : ℕ,
      PrecMax (fun x : FlowPt × ℝ => x.1.L) (step2Dom S Wt)
        (Λ := fun W x => (Fin x.1.L × Fin W) × (Fin x.1.L × Fin W))
        (fun W x e ω => segG W x ω e.1 e.2 -
          if e.1.2 = e.2.2 then blockTr (segG W x ω) e.1.1 e.2.1 else 0)
        (fun W x _ => 1 * (2 * Real.sqrt (step2ZetaX W x))) ∧
      (∀ x W, x ∈ step2Dom S Wt W → ∃ q, step2Gen S W x q ∧ Step2Facts R c N W q) ∧
      (∀ D : ℝ, 0 < D → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ q ∈ S W,
        μ W q.L {ω | ∃ ab : Fin q.L × Fin q.L, R.C + 1 <
          ‖blockTr (flowG W (q.at q.u) ω) ab.1 ab.2‖} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D))) ∧
      (∀ W x, x ∈ step2Dom S Wt W → R.C + 1 ≤ (W : ℝ) ∧
        (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 2 * Real.sqrt (step2ZetaX W x)) := by
  obtain ⟨Wf, hf⟩ := step2_facts R
  have hC1 := R.one_le_C
  have hC0 : 0 < R.C := lt_of_lt_of_le one_pos hC1
  set Wt : ℕ := max Wf (⌈4 * R.C ^ 2⌉₊ + ⌈R.C + 1⌉₊ + 4) with hWt
  set Dom := step2Dom S Wt with hDom
  set ζX := step2ZetaX with hζX
  set χ : ℕ → FlowPt × ℝ → ℝ := fun W x => 2 * Real.sqrt (ζX W x) with hχ
  set Ψ : ℕ → FlowPt × ℝ → ℝ := fun W x => Real.sqrt (ζX W x) with hΨ
  have hDomA : ∀ W x, x ∈ Dom W → SegAdm R.base R.J W x := fun W x hx =>
    step2_dom_segAdm hS Wt W x hx
  have hWbig : ∀ W x, x ∈ Dom W → 4 * R.C ^ 2 ≤ W ∧ R.C + 1 ≤ W := by
    intro W x hx
    have h1 : (⌈4 * R.C ^ 2⌉₊ + ⌈R.C + 1⌉₊ + 4 : ℕ) ≤ W := (le_max_right _ _).trans hx.1
    have h2 : ((⌈4 * R.C ^ 2⌉₊ + ⌈R.C + 1⌉₊ + 4 : ℕ) : ℝ) ≤ W := by exact_mod_cast h1
    push_cast at h2
    have h3 := Nat.le_ceil (4 * R.C ^ 2)
    have h4 := Nat.le_ceil (R.C + 1)
    have h5 : (0 : ℝ) ≤ ⌈4 * R.C ^ 2⌉₊ := Nat.cast_nonneg _
    have h6 : (0 : ℝ) ≤ ⌈R.C + 1⌉₊ := Nat.cast_nonneg _
    constructor <;> linarith
  have hpt : ∀ W x, x ∈ Dom W → ∃ q, step2Gen S W x q ∧ q.ratio ≤ 2 * step2Rinf S W x ∧
      Step2Facts R c N W q ∧ 1 ≤ step2Rinf S W x := by
    intro W x hx
    obtain ⟨hWt', q0, hq0⟩ := hx
    have hW1 : 1 ≤ W := le_trans (by omega) hWt'
    obtain ⟨hr1, -, q, hq, hqR⟩ := step2_rinf hS hW1 hq0
    exact ⟨q, hq, hqR, hf W ((le_max_left _ _).trans hWt') c N q (hS W hq.1), hr1⟩
  have hζpos : ∀ W x, x ∈ Dom W → (2 * (W : ℝ))⁻¹ ≤ ζX W x := by
    intro W x hx
    obtain ⟨q, ⟨hqS, rfl⟩, -, F, -⟩ := hpt W x hx
    exact (step2_num F hN hc).2.2.2.2.2.1
  -- (5.30) [gc:eq:haar]: the traceless entries
  have hΨpos : ∀ W x, x ∈ Dom W → 0 < Ψ W x := by
    intro W x hx
    have hW0 : (0 : ℝ) < W := by
      have := (hWbig W x hx).2; linarith
    exact Real.sqrt_pos.mpr (lt_of_lt_of_le (by positivity) (hζpos W x hx))
  have hHSx : ∀ ε D : ℝ, 0 < ε → 0 < D → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ x ∈ Dom W,
      ∀ a b : Fin x.1.L, μ W x.1.L {ω | (W : ℝ) ^ ε * Ψ W x ^ 2 <
        ((W : ℝ) ^ 2)⁻¹ * blockHS2 (segG W x ω) a b} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
    intro ε D hε hD
    obtain ⟨W₁, hW₁⟩ := hHS ε D hε hD
    refine ⟨W₁, fun W hW x hx a b => ?_⟩
    obtain ⟨q, ⟨hqS, rfl⟩, -, F, -⟩ := hpt W x hx
    have hW0 : (0 : ℝ) < W := by have := F.four_le; exact_mod_cast (by omega : 0 < W)
    have hζ0 : 0 ≤ ζX W (step2X q) := le_trans (by positivity) (hζpos W _ hx)
    refine le_trans (measure_mono ?_) (hW₁ W hW q hqS)
    intro ω hω
    refine ⟨(a, b), ?_⟩
    have hΨ2 : Ψ W (step2X q) ^ 2 = zetaProp q.g W q.L q.u := Real.sq_sqrt hζ0
    have e : segG W (step2X q) ω = flowG W (q.at q.u) ω := step2_segG_eta W (q.at q.u) ω
    change (W : ℝ) ^ ε * Ψ W (step2X q) ^ 2 < ((W : ℝ) ^ 2)⁻¹ *
      blockHS2 (segG W (step2X q) ω) a b at hω
    rw [hΨ2, e, lt_inv_mul_iff₀ (by positivity)] at hω
    rw [Complex.norm_real, Real.norm_of_nonneg (by unfold blockHS2; positivity)]
    calc (W : ℝ) ^ ε * ((W : ℝ) ^ 2 * zetaProp q.g W q.L q.u) =
        (W : ℝ) ^ 2 * ((W : ℝ) ^ ε * zetaProp q.g W q.L q.u) := by ring
      _ < _ := hω
  have hΨχ : ∀ W x, x ∈ Dom W → Ψ W x ≤ 1 * χ W x := by
    intro W x hx
    simp only [hΨ, hχ, one_mul]
    have := Real.sqrt_nonneg (ζX W x)
    linarith
  have hχ0 : ∀ W x, x ∈ Dom W → (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ χ W x := by
    intro W x hx
    have hW0 : (0 : ℝ) < W := by have := (hWbig W x hx).2; linarith
    simp only [hχ]
    have hz := hζpos W x hx
    rw [Real.rpow_neg hW0.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_inv]
    have h1 : Real.sqrt ((W : ℝ)⁻¹) ≤ Real.sqrt (4 * ζX W x) := by
      apply Real.sqrt_le_sqrt
      have : (W : ℝ)⁻¹ = 2 * (2 * (W : ℝ))⁻¹ := by field_simp
      have h0 : 0 ≤ (2 * (W : ℝ))⁻¹ := by positivity
      rw [this]; linarith
    calc Real.sqrt ((W : ℝ)⁻¹) ≤ Real.sqrt (4 * ζX W x) := h1
      _ = 2 * Real.sqrt (ζX W x) := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  have hTL1 := step2_traceless R.base R.J I.sampling Dom hDomA Ψ (fun _ _ => 1) χ hΨχ
    (fun W x hx => by rw [one_mul]; exact hχ0 W x hx)
    (I.averaging.2.1 Dom hDomA Ψ hΨpos hHSx)
  -- the first use of (5.29) [gc:eq:averaging-input] with `K = 4C²R`
  set K₁ : ℕ → FlowPt × ℝ → ℝ := fun W x => 4 * R.C ^ 2 * step2Rinf S W x with hK₁
  have hK₁prec : PrecMax (fun x : FlowPt × ℝ => x.1.L) Dom
      (Λ := fun _ x => Fin x.1.L × Fin x.1.L)
      (fun W x ab ω => blockTr (segG W x ω) ab.1 ab.2) (fun W x _ => K₁ W x) := by
    refine step2_prec_of_small ⟨0, fun W _ x _ _ => mul_nonneg (by positivity)
      (le_trans zero_le_one (le_max_left _ _))⟩ (ε₀ := c) hc ?_
    intro ε D hε hεc hD
    obtain ⟨Wa, hWa⟩ := step2_apriori R c N hc hN S hS hcmp ε D hε hεc hD
    refine ⟨Wa, fun W hW x hx => ?_⟩
    obtain ⟨q, ⟨hqS, rfl⟩, hqR, F, hr1⟩ := hpt W x hx
    refine le_trans (measure_mono ?_) (hWa W hW q hqS)
    rintro ω ⟨ab, hab⟩
    have e : segG W (q.at q.u, etaChar q.g (mRoot q.g q.L q.E) q.u) ω = flowG W (q.at q.u) ω :=
      step2_segG_eta W (q.at q.u) ω
    rw [e] at hab
    refine ⟨ab, lt_of_le_of_lt ?_ hab⟩
    have hK : 2 * R.C ^ 2 * q.ratio ≤ K₁ W (q.at q.u, etaChar q.g (mRoot q.g q.L q.E) q.u) := by
      simp only [hK₁]
      nlinarith [mul_le_mul_of_nonneg_left hqR (by positivity : (0 : ℝ) ≤ 2 * R.C ^ 2)]
    exact mul_le_mul_of_nonneg_left hK (by positivity)
  have hTL₁ : PrecMax (fun x : FlowPt × ℝ => x.1.L) Dom
      (Λ := fun W x => (Fin x.1.L × Fin W) × (Fin x.1.L × Fin W))
      (fun W x e ω => segG W x ω e.1 e.2 -
        if e.1.2 = e.2.2 then blockTr (segG W x ω) e.1.1 e.2.1 else 0)
      (fun W x _ => K₁ W x * χ W x) := by
    refine hTL1.mono fun W x hx _ => ?_
    obtain ⟨-, -, -, -, hr1⟩ := hpt W x hx
    have hK1 : 1 ≤ K₁ W x := by
      simp only [hK₁]
      have : 1 ≤ R.C ^ 2 := one_le_pow₀ hC1
      nlinarith
    have hχp : 0 ≤ χ W x := by simp only [hχ]; positivity
    exact mul_le_mul_of_nonneg_right hK1 hχp
  have hKb₁ : ∀ W x, x ∈ Dom W →
      1 ≤ K₁ W x ∧ K₁ W x ≤ (W : ℝ) ^ (4 : ℝ) ∧ (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ χ W x := by
    intro W x hx
    obtain ⟨q, hq, -, F, hr1⟩ := hpt W x hx
    obtain ⟨-, -, -, hR3, -, -, -, -, -⟩ := step2_num F hN hc
    obtain ⟨-, hrq, -⟩ := step2_rinf hS (by have := F.four_le; omega) hq
    have hW0 : (0 : ℝ) < W := by have := F.four_le; exact_mod_cast (by omega : 0 < W)
    obtain ⟨hW4, -⟩ := hWbig W x hx
    refine ⟨?_, ?_, hχ0 W x hx⟩
    · simp only [hK₁]
      have : 1 ≤ R.C ^ 2 := one_le_pow₀ hC1
      nlinarith
    · simp only [hK₁]
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      calc 4 * R.C ^ 2 * step2Rinf S W x ≤ (W : ℝ) * (W : ℝ) ^ 3 :=
            mul_le_mul hW4 (hrq.trans hR3) (by linarith) hW0.le
        _ = (W : ℝ) ^ 4 := by ring
  have hRes1 := I.averaging.1 Dom hDomA K₁ χ 4 hKb₁ hK₁prec hTL₁
  refine ⟨Wt, hTL1, fun x W hx => ?_, ?_, fun W x hx => ⟨(hWbig W x hx).2, hχ0 W x hx⟩⟩
  · obtain ⟨q, hq, -, F, -⟩ := hpt W x hx
    exact ⟨q, hq, F⟩
  -- the off-diagonal traces are bounded
  intro D hD
  set ε := c / 8 with hεdef
  have hε0 : 0 < ε := by positivity
  obtain ⟨W₁, hW₁⟩ := h1.avg ε (D + 2) hε0 (by linarith)
  obtain ⟨W₂, hW₂⟩ := step2_apriori R c N hc hN S hS hcmp ε (D + 2) hε0 (by linarith) (by linarith)
  obtain ⟨W₃, hW₃⟩ := hRes1 ε (D + 2) hε0 (by linarith)
  obtain ⟨W₄, hW₄⟩ := step2_eventually_ge (66 * R.C ^ 4) (c / 4) (by positivity)
  refine ⟨max (max Wt W₁) (max W₂ (max W₃ W₄)), fun W hW q hq => ?_⟩
  have hWt' : Wt ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hW1' : W₁ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hW2' : W₂ ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
  have hW3' : W₃ ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans hW))
  have hW4' : W₄ ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans hW))
  have F := hf W ((le_max_left _ _).trans hWt') c N q (hS W hq)
  obtain ⟨hu0, hu1, hR1, hR3, -, hζW, hR6, hζ1, -⟩ := step2_num F hN hc
  have hW4 := F.four_le
  have hW1 : 1 ≤ W := by omega
  have hW2 : 2 ≤ W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hxq : step2X q ∈ Dom W := ⟨hWt', q, hq, rfl⟩
  set ζ := zetaProp q.g W q.L q.u with hζdef
  have hζ0 : 0 < ζ := lt_of_lt_of_le (by positivity) hζW
  set Rq := q.ratio with hRq
  -- the three events
  set E₁ := {ω : Ω W q.L | ∃ c' : Fin q.L, (W : ℝ) ^ ε * (Rq ^ 2 * ζ) <
    ‖blockTr (flowG W (q.at q.u) ω - flowM W (q.at q.u)) c' c'‖} with hE₁
  set E₂ := {ω : Ω W q.L | ∃ ab : Fin q.L × Fin q.L, (W : ℝ) ^ ε * (2 * R.C ^ 2 * Rq) <
    ‖blockTr (flowG W (q.at q.u) ω) ab.1 ab.2‖} with hE₂
  set E₃ := {ω : Ω W q.L | ∃ ab : Fin q.L × Fin q.L,
    (W : ℝ) ^ ε * (K₁ W (step2X q) * χ W (step2X q)) ^ 2 <
      ‖segRes W (step2X q) ω ab.1 ab.2‖} with hE₃
  have h₁ : μ W q.L E₁ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 2))) := hW₁ W hW1' q hq
  have h₂ : μ W q.L E₂ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 2))) := hW₂ W hW2' q hq
  have h₃ : μ W q.L E₃ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 2))) := hW₃ W hW3' _ hxq
  have hKχ : (K₁ W (step2X q) * χ W (step2X q)) ^ 2 ≤ 64 * R.C ^ 4 * Rq ^ 2 * ζ := by
    obtain ⟨-, hrq, -⟩ := step2_rinf hS hW1 (x := step2X q) ⟨hq, rfl⟩
    have hr1 : 1 ≤ step2Rinf S W (step2X q) := le_max_left _ _
    simp only [hK₁, hχ]
    have hzx : ζX W (step2X q) = ζ := rfl
    rw [hzx, mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hζ0.le]
    have : step2Rinf S W (step2X q) ^ 2 ≤ Rq ^ 2 := pow_le_pow_left₀ (by linarith) hrq 2
    have hC4 : 0 ≤ R.C ^ 4 := by positivity
    calc (4 : ℝ) ^ 2 * (R.C ^ 2) ^ 2 * step2Rinf S W (step2X q) ^ 2 * (2 ^ 2 * ζ)
        = 64 * R.C ^ 4 * step2Rinf S W (step2X q) ^ 2 * ζ := by ring
      _ ≤ 64 * R.C ^ 4 * Rq ^ 2 * ζ := by gcongr
  have hsub : {ω : Ω W q.L | ∃ ab : Fin q.L × Fin q.L, R.C + 1 <
      ‖blockTr (flowG W (q.at q.u) ω) ab.1 ab.2‖} ⊆ E₁ ∪ E₂ ∪ E₃ := by
    rintro ω ⟨ab, hab⟩
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨⟨n1, n2⟩, n3⟩ := hcon
    have hU : ∀ e, ‖blockTr (flowG W (q.at q.u) ω - flowM W (q.at q.u)) e e‖ ≤
        (W : ℝ) ^ ε * (Rq ^ 2 * ζ) := fun e => not_lt.mp fun h => n1 ⟨e, h⟩
    have hΓ : ∀ a b, ‖blockTr (flowG W (q.at q.u) ω) a b‖ ≤ (W : ℝ) ^ ε * (2 * R.C ^ 2 * Rq) :=
      fun a b => not_lt.mp fun h => n2 ⟨(a, b), h⟩
    have hρ : ∀ a b, ‖flowRes W (q.at q.u) ω a b‖ ≤ (W : ℝ) ^ ε * (64 * R.C ^ 4 * Rq ^ 2 * ζ) := by
      intro a b
      have h3 : ‖segRes W (step2X q) ω a b‖ ≤
          (W : ℝ) ^ ε * (K₁ W (step2X q) * χ W (step2X q)) ^ 2 :=
        not_lt.mp fun h => n3 ⟨(a, b), h⟩
      have e3 : segRes W (step2X q) ω a b = flowRes W (q.at q.u) ω a b :=
        step2_segRes_eq W (q.at q.u) F.L3 F.g0 F.root hu0 hu1 ω a b
      rw [e3] at h3
      exact h3.trans (mul_le_mul_of_nonneg_left hKχ (by positivity))
    have hdet := (step2_local_det F hN hc ω hρ hΓ hU (by positivity) (by positivity)).2 ab.1 ab.2
    -- the numerics
    have hWε : (W : ℝ) ^ ε * (W : ℝ) ^ ε = (W : ℝ) ^ (c / 4) := by
      rw [← Real.rpow_add hW0, hεdef]; ring_nf
    have hR3ζ : Rq ^ 3 * ζ ≤ (W : ℝ) ^ (-c) := by
      have : Rq ^ 3 ≤ Rq ^ 6 := pow_le_pow_right₀ hR1 (by norm_num)
      calc Rq ^ 3 * ζ ≤ Rq ^ 6 * ζ := mul_le_mul_of_nonneg_right this hζ0.le
        _ ≤ _ := hR6
    have hsmall : (W : ℝ) ^ ε * (64 * R.C ^ 4 * Rq ^ 2 * ζ) +
        R.C * ((W : ℝ) ^ ε * (Rq ^ 2 * ζ)) * ((W : ℝ) ^ ε * (2 * R.C ^ 2 * Rq)) ≤ 1 := by
      have hW4c := hW₄ W hW4'
      have hWe1 : 1 ≤ (W : ℝ) ^ ε := Real.one_le_rpow hW1r hε0.le
      have hR2 : Rq ^ 2 ≤ Rq ^ 3 := pow_le_pow_right₀ hR1 (by norm_num)
      have hC3 : R.C ^ 3 ≤ R.C ^ 4 := pow_le_pow_right₀ hC1 (by norm_num)
      have hA : (W : ℝ) ^ ε * (64 * R.C ^ 4 * Rq ^ 2 * ζ) ≤
          64 * R.C ^ 4 * ((W : ℝ) ^ (c / 4) * (Rq ^ 3 * ζ)) := by
        rw [← hWε]
        have : Rq ^ 2 * ζ ≤ Rq ^ 3 * ζ := mul_le_mul_of_nonneg_right hR2 hζ0.le
        have h0 : 0 ≤ (W : ℝ) ^ ε := by positivity
        calc (W : ℝ) ^ ε * (64 * R.C ^ 4 * Rq ^ 2 * ζ) = 64 * R.C ^ 4 * ((W : ℝ) ^ ε * 1 *
              (Rq ^ 2 * ζ)) := by ring
          _ ≤ 64 * R.C ^ 4 * ((W : ℝ) ^ ε * (W : ℝ) ^ ε * (Rq ^ 3 * ζ)) := by gcongr
      have hB : R.C * ((W : ℝ) ^ ε * (Rq ^ 2 * ζ)) * ((W : ℝ) ^ ε * (2 * R.C ^ 2 * Rq)) ≤
          2 * R.C ^ 4 * ((W : ℝ) ^ (c / 4) * (Rq ^ 3 * ζ)) := by
        rw [← hWε]
        calc R.C * ((W : ℝ) ^ ε * (Rq ^ 2 * ζ)) * ((W : ℝ) ^ ε * (2 * R.C ^ 2 * Rq)) =
            2 * R.C ^ 3 * ((W : ℝ) ^ ε * (W : ℝ) ^ ε * (Rq ^ 3 * ζ)) := by ring
          _ ≤ 2 * R.C ^ 4 * ((W : ℝ) ^ ε * (W : ℝ) ^ ε * (Rq ^ 3 * ζ)) := by gcongr
      have hC : (W : ℝ) ^ (c / 4) * (Rq ^ 3 * ζ) ≤ (W : ℝ) ^ (-(3 * c / 4)) := by
        calc (W : ℝ) ^ (c / 4) * (Rq ^ 3 * ζ) ≤ (W : ℝ) ^ (c / 4) * (W : ℝ) ^ (-c) := by gcongr
          _ = (W : ℝ) ^ (-(3 * c / 4)) := by rw [← Real.rpow_add hW0]; ring_nf
      have hD' : 66 * R.C ^ 4 * (W : ℝ) ^ (-(3 * c / 4)) ≤ 1 := by
        have h1 : 66 * R.C ^ 4 ≤ (W : ℝ) ^ (c / 4) := hW4c
        have h2 : (W : ℝ) ^ (c / 4) * (W : ℝ) ^ (-(3 * c / 4)) ≤ 1 := by
          rw [← Real.rpow_add hW0]
          exact Real.rpow_le_one_of_one_le_of_nonpos hW1r (by linarith)
        calc 66 * R.C ^ 4 * (W : ℝ) ^ (-(3 * c / 4)) ≤
            (W : ℝ) ^ (c / 4) * (W : ℝ) ^ (-(3 * c / 4)) := by gcongr
          _ ≤ 1 := h2
      have hC0' : 0 ≤ R.C ^ 4 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hC (show (0:ℝ) ≤ 66 * R.C ^ 4 by positivity)]
    have hM := F.Mbd ab.1 ab.2
    have hk : blockTr (flowM W (q.at q.u)) ab.1 ab.2 =
        dysonMat (hopB q.g) (gammaG q.g) q.L q.E (mRoot q.g q.L q.E) ab.1 ab.2 :=
      step2_blockTr_kron W q.L hW1 _ ab.1 ab.2
    have e : blockTr (flowG W (q.at q.u) ω) ab.1 ab.2 =
        blockTr (flowG W (q.at q.u) ω - flowM W (q.at q.u)) ab.1 ab.2 +
          dysonMat (hopB q.g) (gammaG q.g) q.L q.E (mRoot q.g q.L q.E) ab.1 ab.2 := by
      have hs := step2_blockTr_sub (flowG W (q.at q.u) ω) (flowM W (q.at q.u)) ab.1 ab.2
      rw [hk] at hs
      rw [hs]; ring
    have : ‖blockTr (flowG W (q.at q.u) ω) ab.1 ab.2‖ ≤ 1 + R.C := by
      rw [e]
      exact (norm_add_le _ _).trans (add_le_add (hdet.trans hsmall) hM)
    linarith
  calc μ W q.L {ω | ∃ ab : Fin q.L × Fin q.L, R.C + 1 <
        ‖blockTr (flowG W (q.at q.u) ω) ab.1 ab.2‖} ≤ μ W q.L (E₁ ∪ E₂ ∪ E₃) := measure_mono hsub
    _ ≤ μ W q.L E₁ + μ W q.L E₂ + μ W q.L E₃ :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 2))) + ENNReal.ofReal ((W : ℝ) ^ (-(D + 2))) +
          ENNReal.ofReal ((W : ℝ) ^ (-(D + 2))) := add_le_add (add_le_add h₁ h₂) h₃
    _ ≤ _ := by
        have hn := Real.rpow_nonneg hW0.le (-(D + 2))
        rw [← ENNReal.ofReal_add hn hn, ← ENNReal.ofReal_add (by positivity) hn]
        apply ENNReal.ofReal_le_ofReal
        have e : (W : ℝ) ^ (-(D + 2)) = (W : ℝ) ^ (-D) * ((W : ℝ) ^ 2)⁻¹ := by
          rw [show -(D + 2) = -D + (-2) by ring, Real.rpow_add hW0]
          congr 1
          rw [Real.rpow_neg hW0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        have hpos : 0 < (W : ℝ) ^ (-D) := Real.rpow_pos_of_pos hW0 _
        have hW2r : (2 : ℝ) ≤ W := by exact_mod_cast hW2
        have hinv : ((W : ℝ) ^ 2)⁻¹ ≤ 1 / 4 := by
          rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
        rw [e]; nlinarith

end Step2LocalAvg

section Step2Local

/-- The numerics of the second closure: with `A ≥ 1`, `R²ζ ≤ 1`, `R⁴ζ ≤ 1`,
`ρ = 4(C+1)²Aζ`, `U = AR²ζ`, `Γ = C + 1`:
`ρ + C (C(ρ + CU(ρ + CΓU))) Γ ≤ K A² ζ` with
`K = 4(C+1)² + C²(C+1)(4(C+1)² + 4C(C+1)² + C²(C+1))`. -/
private theorem step2_num_close {C A R ζ : ℝ} (hC : 1 ≤ C) (hA : 1 ≤ A) (hR : 1 ≤ R) (hζ : 0 ≤ ζ)
    (hR2 : R ^ 2 * ζ ≤ 1) (hR4 : R ^ 4 * ζ ≤ 1) :
    4 * (C + 1) ^ 2 * A * ζ + C * (C * (4 * (C + 1) ^ 2 * A * ζ + C * (A * (R ^ 2 * ζ)) *
        (4 * (C + 1) ^ 2 * A * ζ + C * (C + 1) * (A * (R ^ 2 * ζ))))) * (C + 1) ≤
      (4 * (C + 1) ^ 2 + C ^ 2 * (C + 1) * (4 * (C + 1) ^ 2 + 4 * C * (C + 1) ^ 2 +
        C ^ 2 * (C + 1))) * A ^ 2 * ζ := by
  have hC0 : 0 ≤ C := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hAA : A ≤ A ^ 2 := by nlinarith
  set ρ := 4 * (C + 1) ^ 2 * A * ζ with hρ
  set U := A * (R ^ 2 * ζ) with hU
  have hρ0 : 0 ≤ ρ := by positivity
  have hU0 : 0 ≤ U := by positivity
  have hUρ : U * ρ ≤ 4 * (C + 1) ^ 2 * A ^ 2 * ζ := by
    calc U * ρ = 4 * (C + 1) ^ 2 * A ^ 2 * ζ * (R ^ 2 * ζ) := by rw [hU, hρ]; ring
      _ ≤ 4 * (C + 1) ^ 2 * A ^ 2 * ζ * 1 := by gcongr
      _ = _ := by ring
  have hUU : U * U ≤ A ^ 2 * ζ := by
    calc U * U = A ^ 2 * ζ * (R ^ 4 * ζ) := by rw [hU]; ring
      _ ≤ A ^ 2 * ζ * 1 := by gcongr
      _ = _ := by ring
  have hρA : ρ ≤ 4 * (C + 1) ^ 2 * A ^ 2 * ζ := by
    rw [hρ]
    have : 0 ≤ 4 * (C + 1) ^ 2 * ζ := by positivity
    nlinarith
  have hin : ρ + C * U * (ρ + C * (C + 1) * U) ≤
      (4 * (C + 1) ^ 2 + 4 * C * (C + 1) ^ 2 + C ^ 2 * (C + 1)) * A ^ 2 * ζ := by
    have e : ρ + C * U * (ρ + C * (C + 1) * U) = ρ + C * (U * ρ) + C ^ 2 * (C + 1) * (U * U) := by
      ring
    rw [e]
    have h1 : C * (U * ρ) ≤ C * (4 * (C + 1) ^ 2 * A ^ 2 * ζ) := mul_le_mul_of_nonneg_left hUρ hC0
    have h2 : C ^ 2 * (C + 1) * (U * U) ≤ C ^ 2 * (C + 1) * (A ^ 2 * ζ) :=
      mul_le_mul_of_nonneg_left hUU (by positivity)
    nlinarith
  have e2 : C * (C * (ρ + C * U * (ρ + C * (C + 1) * U))) * (C + 1) =
      C ^ 2 * (C + 1) * (ρ + C * U * (ρ + C * (C + 1) * U)) := by ring
  rw [e2]
  have h3 := mul_le_mul_of_nonneg_left hin (by positivity : (0 : ℝ) ≤ C ^ 2 * (C + 1))
  nlinarith

/-- An entry of `G - M ⊗ I` is its traceless part plus the centered block trace on the
diagonal of the orbitals. -/
private theorem step2_entry_decomp {W L : ℕ} (hW : 1 ≤ W)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (M : Matrix (Fin L) (Fin L) ℂ) (e₁ e₂ : Fin L × Fin W) :
    (G - M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) e₁ e₂ =
      (G e₁ e₂ - if e₁.2 = e₂.2 then blockTr G e₁.1 e₂.1 else 0) +
        if e₁.2 = e₂.2 then blockTr (G - M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) e₁.1 e₂.1
          else 0 := by
  obtain ⟨a, i⟩ := e₁
  obtain ⟨b, j⟩ := e₂
  have hs := step2_blockTr_sub G (M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) a b
  rw [step2_blockTr_kron W L hW M a b] at hs
  simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.one_apply_eq, mul_one, ite_true]
    rw [hs]; ring
  · simp only [Matrix.one_apply_ne hij, mul_zero, hij, ite_false, sub_zero, add_zero]

/-- The sharp local law of (C.15) [fo:eq:step2]: the second use of (5.29)
[gc:eq:averaging-input] with `K = C + 1` and the scalar identities (5.32) [gc:eq:scalar] give
`max_{ab} |⟨G̃_u⟩_{ab}| ≺ ζ_u`, and with (5.30) [gc:eq:haar] `‖G̃_u‖_max ≺ ζ_u^{1/2}`. -/
private theorem step2_local (R : PropRegime) (I : PropInputs R.base R.J) (c N : ℝ) (hc : 0 < c)
    (hN : 20 ≤ N) (S : ℕ → Set StepPt) (hS : ∀ W, S W ⊆ {q | StepAdm R c N W q}) {cp θ : ℝ}
    (hcmp : OneStepInput cp θ (fun q : StepPt => cmpPt (q.at q.u) q.s) S) (h1 : Step1Out S)
    (hHS : PrecMax StepPt.L S (Λ := fun _ q => Fin q.L × Fin q.L)
      (fun W q ab ω => ((blockHS2 (flowG W (q.at q.u) ω) ab.1 ab.2 : ℝ) : ℂ))
      (fun W q _ => (W : ℝ) ^ 2 * zetaProp q.g W q.L q.u)) :
    PrecMax StepPt.L S (Λ := fun W q => (Fin q.L × Fin W) × (Fin q.L × Fin W))
      (fun W q e ω => (flowG W (q.at q.u) ω - flowM W (q.at q.u)) e.1 e.2)
      (fun W q _ => Real.sqrt (zetaProp q.g W q.L q.u)) ∧
    PrecMax StepPt.L S (Λ := fun _ q => Fin q.L × Fin q.L)
      (fun W q ab ω => blockTr (flowG W (q.at q.u) ω - flowM W (q.at q.u)) ab.1 ab.2)
      (fun W q _ => zetaProp q.g W q.L q.u) := by
  obtain ⟨Wt, hTL1, hptx, hX, hbd⟩ := step2_avg1 R I c N hc hN S hS hcmp h1 hHS
  obtain ⟨Wf, hf⟩ := step2_facts R
  have hC1 := R.one_le_C
  set Dom := step2Dom S Wt with hDom
  set χ : ℕ → FlowPt × ℝ → ℝ := fun W x => 2 * Real.sqrt (step2ZetaX W x) with hχ
  have hDomA : ∀ W x, x ∈ Dom W → SegAdm R.base R.J W x := fun W x hx =>
    step2_dom_segAdm hS Wt W x hx
  -- the second use of (5.29) [gc:eq:averaging-input] with `K = C + 1`
  set K₂ : ℕ → FlowPt × ℝ → ℝ := fun _ _ => R.C + 1 with hK₂
  have hK₂prec : PrecMax (fun x : FlowPt × ℝ => x.1.L) Dom
      (Λ := fun _ x => Fin x.1.L × Fin x.1.L)
      (fun W x ab ω => blockTr (segG W x ω) ab.1 ab.2) (fun W x _ => K₂ W x) := by
    intro ε D hε hD
    obtain ⟨W₁, hW₁⟩ := hX D hD
    refine ⟨W₁, fun W hW x hx => ?_⟩
    obtain ⟨q, ⟨hqS, rfl⟩, F⟩ := hptx x W hx
    have hW1r : (1 : ℝ) ≤ W := by have := F.four_le; exact_mod_cast (by omega : 1 ≤ W)
    refine le_trans (measure_mono ?_) (hW₁ W hW q hqS)
    rintro ω ⟨ab, hab⟩
    have e : segG W (q.at q.u, etaChar q.g (mRoot q.g q.L q.E) q.u) ω = flowG W (q.at q.u) ω :=
      step2_segG_eta W (q.at q.u) ω
    beta_reduce at hab
    rw [e] at hab
    refine ⟨ab, lt_of_le_of_lt ?_ hab⟩
    exact le_mul_of_one_le_left (by positivity) (Real.one_le_rpow hW1r hε.le)
  have hTL₂ : PrecMax (fun x : FlowPt × ℝ => x.1.L) Dom
      (Λ := fun W x => (Fin x.1.L × Fin W) × (Fin x.1.L × Fin W))
      (fun W x e ω => segG W x ω e.1 e.2 -
        if e.1.2 = e.2.2 then blockTr (segG W x ω) e.1.1 e.2.1 else 0)
      (fun W x _ => K₂ W x * χ W x) := by
    refine hTL1.mono fun W x hx _ => ?_
    have hχp : 0 ≤ χ W x := by simp only [hχ]; positivity
    exact mul_le_mul_of_nonneg_right (by simp only [hK₂]; linarith) hχp
  have hKb₂ : ∀ W x, x ∈ Dom W →
      1 ≤ K₂ W x ∧ K₂ W x ≤ (W : ℝ) ^ (1 : ℝ) ∧ (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ χ W x := by
    intro W x hx
    obtain ⟨h1', h2'⟩ := hbd W x hx
    refine ⟨by simp only [hK₂]; linarith, by rw [Real.rpow_one]; exact h1', h2'⟩
  have hRes2 := I.averaging.1 Dom hDomA K₂ χ 1 hKb₂ hK₂prec hTL₂
  -- the centered block traces
  have havg : PrecMax StepPt.L S (Λ := fun _ q => Fin q.L × Fin q.L)
      (fun W q ab ω => blockTr (flowG W (q.at q.u) ω - flowM W (q.at q.u)) ab.1 ab.2)
      (fun W q _ => zetaProp q.g W q.L q.u) := by
    intro ε D hε hD
    set K := 4 * (R.C + 1) ^ 2 + R.C ^ 2 * (R.C + 1) * (4 * (R.C + 1) ^ 2 +
      4 * R.C * (R.C + 1) ^ 2 + R.C ^ 2 * (R.C + 1)) with hKdef
    obtain ⟨W₁, hW₁⟩ := h1.avg (ε / 4) (D + 2) (by positivity) (by linarith)
    obtain ⟨W₂, hW₂⟩ := hX (D + 2) (by linarith)
    obtain ⟨W₃, hW₃⟩ := hRes2 (ε / 4) (D + 2) (by positivity) (by linarith)
    obtain ⟨W₄, hW₄⟩ := step2_eventually_ge K (ε / 2) (by positivity)
    refine ⟨max (max (max Wt Wf) W₁) (max W₂ (max W₃ W₄)), fun W hW q hq => ?_⟩
    simp only [max_le_iff] at hW
    obtain ⟨⟨⟨hWt', hWf'⟩, hW1'⟩, hW2', hW3', hW4'⟩ := hW
    have F := hf W hWf' c N q (hS W hq)
    obtain ⟨hu0, hu1, hR1, -, -, hζW, hR6, hζ1, -⟩ := step2_num F hN hc
    have hW4 := F.four_le
    have hW1 : 1 ≤ W := by omega
    have hW2 : 2 ≤ W := by omega
    have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
    have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
    have hxq : step2X q ∈ Dom W := ⟨hWt', q, hq, rfl⟩
    set ζ := zetaProp q.g W q.L q.u with hζdef
    have hζ0 : 0 < ζ := lt_of_lt_of_le (by positivity) hζW
    set Rq := q.ratio with hRq
    set A := (W : ℝ) ^ (ε / 4) with hAdef
    have hA1 : 1 ≤ A := Real.one_le_rpow hW1r (by positivity)
    have hWc : (W : ℝ) ^ (-c) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1r (by linarith)
    have hR6' : Rq ^ 6 * ζ ≤ 1 := hR6.trans hWc
    have hR2 : Rq ^ 2 * ζ ≤ 1 := le_trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hR1 (by norm_num)) hζ0.le) hR6'
    have hR4 : Rq ^ 4 * ζ ≤ 1 := le_trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hR1 (by norm_num)) hζ0.le) hR6'
    set E₁ := {ω : Ω W q.L | ∃ c' : Fin q.L, (W : ℝ) ^ (ε / 4) * (Rq ^ 2 * ζ) <
      ‖blockTr (flowG W (q.at q.u) ω - flowM W (q.at q.u)) c' c'‖} with hE₁
    set E₂ := {ω : Ω W q.L | ∃ ab : Fin q.L × Fin q.L, R.C + 1 <
      ‖blockTr (flowG W (q.at q.u) ω) ab.1 ab.2‖} with hE₂
    set E₃ := {ω : Ω W q.L | ∃ ab : Fin q.L × Fin q.L,
      (W : ℝ) ^ (ε / 4) * (K₂ W (step2X q) * χ W (step2X q)) ^ 2 <
        ‖segRes W (step2X q) ω ab.1 ab.2‖} with hE₃
    have h₁ : μ W q.L E₁ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 2))) := hW₁ W hW1' q hq
    have h₂ : μ W q.L E₂ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 2))) := hW₂ W hW2' q hq
    have h₃ : μ W q.L E₃ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 2))) := hW₃ W hW3' _ hxq
    have hKχ : (K₂ W (step2X q) * χ W (step2X q)) ^ 2 = 4 * (R.C + 1) ^ 2 * ζ := by
      simp only [hK₂, hχ]
      have hzx : step2ZetaX W (step2X q) = ζ := rfl
      rw [hzx, mul_pow, mul_pow, Real.sq_sqrt hζ0.le]; ring
    have hsub : {ω : Ω W q.L | ∃ ab : Fin q.L × Fin q.L, (W : ℝ) ^ ε * ζ <
        ‖blockTr (flowG W (q.at q.u) ω - flowM W (q.at q.u)) ab.1 ab.2‖} ⊆ E₁ ∪ E₂ ∪ E₃ := by
      rintro ω ⟨ab, hab⟩
      by_contra hcon
      simp only [Set.mem_union, not_or] at hcon
      obtain ⟨⟨n1, n2⟩, n3⟩ := hcon
      have hU : ∀ e, ‖blockTr (flowG W (q.at q.u) ω - flowM W (q.at q.u)) e e‖ ≤
          A * (Rq ^ 2 * ζ) := fun e => not_lt.mp fun h => n1 ⟨e, h⟩
      have hΓ : ∀ a b, ‖blockTr (flowG W (q.at q.u) ω) a b‖ ≤ R.C + 1 :=
        fun a b => not_lt.mp fun h => n2 ⟨(a, b), h⟩
      have hρ : ∀ a b, ‖flowRes W (q.at q.u) ω a b‖ ≤ 4 * (R.C + 1) ^ 2 * A * ζ := by
        intro a b
        have h3 : ‖segRes W (step2X q) ω a b‖ ≤
            (W : ℝ) ^ (ε / 4) * (K₂ W (step2X q) * χ W (step2X q)) ^ 2 :=
          not_lt.mp fun h => n3 ⟨(a, b), h⟩
        have e3 : segRes W (step2X q) ω a b = flowRes W (q.at q.u) ω a b :=
          step2_segRes_eq W (q.at q.u) F.L3 F.g0 F.root hu0 hu1 ω a b
        rw [e3, hKχ] at h3
        calc _ ≤ (W : ℝ) ^ (ε / 4) * (4 * (R.C + 1) ^ 2 * ζ) := h3
          _ = 4 * (R.C + 1) ^ 2 * A * ζ := by rw [hAdef]; ring
      have hU0 : 0 ≤ A * (Rq ^ 2 * ζ) := by positivity
      have hdiag := (step2_local_det F hN hc ω hρ hΓ hU hU0 (by positivity)).1
      have hdet := (step2_local_det F hN hc ω hρ hΓ hdiag (by positivity) (by positivity)).2
        ab.1 ab.2
      have hnum := step2_num_close hC1 hA1 hR1 hζ0.le hR2 hR4
      have hA2 : A ^ 2 = (W : ℝ) ^ (ε / 2) := by
        rw [hAdef, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
      have hK := hW₄ W hW4'
      have hfin : K * A ^ 2 * ζ ≤ (W : ℝ) ^ ε * ζ := by
        rw [hA2]
        have hsplit : (W : ℝ) ^ ε = (W : ℝ) ^ (ε / 2) * (W : ℝ) ^ (ε / 2) := by
          rw [← Real.rpow_add hW0]; ring_nf
        rw [hsplit]
        have h0 : 0 ≤ (W : ℝ) ^ (ε / 2) * ζ := by positivity
        calc K * (W : ℝ) ^ (ε / 2) * ζ = K * ((W : ℝ) ^ (ε / 2) * ζ) := by ring
          _ ≤ (W : ℝ) ^ (ε / 2) * ((W : ℝ) ^ (ε / 2) * ζ) := mul_le_mul_of_nonneg_right hK h0
          _ = _ := by ring
      have : ‖blockTr (flowG W (q.at q.u) ω - flowM W (q.at q.u)) ab.1 ab.2‖ ≤ (W : ℝ) ^ ε * ζ :=
        hdet.trans (hnum.trans hfin)
      linarith
    calc μ W q.L {ω | ∃ ab : Fin q.L × Fin q.L, (W : ℝ) ^ ε * ζ <
          ‖blockTr (flowG W (q.at q.u) ω - flowM W (q.at q.u)) ab.1 ab.2‖}
        ≤ μ W q.L (E₁ ∪ E₂ ∪ E₃) := measure_mono hsub
      _ ≤ μ W q.L E₁ + μ W q.L E₂ + μ W q.L E₃ :=
          (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 2))) + ENNReal.ofReal ((W : ℝ) ^ (-(D + 2))) +
            ENNReal.ofReal ((W : ℝ) ^ (-(D + 2))) := add_le_add (add_le_add h₁ h₂) h₃
      _ ≤ _ := by
          have hn := Real.rpow_nonneg hW0.le (-(D + 2))
          rw [← ENNReal.ofReal_add hn hn, ← ENNReal.ofReal_add (by positivity) hn]
          apply ENNReal.ofReal_le_ofReal
          have e : (W : ℝ) ^ (-(D + 2)) = (W : ℝ) ^ (-D) * ((W : ℝ) ^ 2)⁻¹ := by
            rw [show -(D + 2) = -D + (-2) by ring, Real.rpow_add hW0]
            congr 1
            rw [Real.rpow_neg hW0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          have hpos : 0 < (W : ℝ) ^ (-D) := Real.rpow_pos_of_pos hW0 _
          have hW2r : (2 : ℝ) ≤ W := by exact_mod_cast hW2
          have hinv : ((W : ℝ) ^ 2)⁻¹ ≤ 1 / 4 := by
            rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
          rw [e]; nlinarith
  refine ⟨?_, havg⟩
  -- the entries
  intro ε D hε hD
  obtain ⟨W₁, hW₁⟩ := hTL1 (ε / 2) (D + 1) (by positivity) (by linarith)
  obtain ⟨W₂, hW₂⟩ := havg (ε / 2) (D + 1) (by positivity) (by linarith)
  obtain ⟨W₃, hW₃⟩ := step2_eventually_ge 3 (ε / 2) (by positivity)
  refine ⟨max (max Wt Wf) (max W₁ (max W₂ W₃)), fun W hW q hq => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWt', hWf'⟩, hW1', hW2', hW3'⟩ := hW
  have F := hf W hWf' c N q (hS W hq)
  obtain ⟨hu0, hu1, hR1, -, -, hζW, hR6, hζ1, -⟩ := step2_num F hN hc
  have hW4 := F.four_le
  have hW1 : 1 ≤ W := by omega
  have hW2 : 2 ≤ W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hxq : step2X q ∈ Dom W := ⟨hWt', q, hq, rfl⟩
  set ζ := zetaProp q.g W q.L q.u with hζdef
  have hζ0 : 0 < ζ := lt_of_lt_of_le (by positivity) hζW
  set E₁ := {ω : Ω W q.L | ∃ e : (Fin q.L × Fin W) × (Fin q.L × Fin W),
    (W : ℝ) ^ (ε / 2) * (1 * χ W (step2X q)) <
      ‖segG W (step2X q) ω e.1 e.2 -
        if e.1.2 = e.2.2 then blockTr (segG W (step2X q) ω) e.1.1 e.2.1 else 0‖} with hE₁
  set E₂ := {ω : Ω W q.L | ∃ ab : Fin q.L × Fin q.L, (W : ℝ) ^ (ε / 2) * ζ <
    ‖blockTr (flowG W (q.at q.u) ω - flowM W (q.at q.u)) ab.1 ab.2‖} with hE₂
  have h₁ : μ W q.L E₁ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) := hW₁ W hW1' _ hxq
  have h₂ : μ W q.L E₂ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) := hW₂ W hW2' q hq
  have hsub : {ω : Ω W q.L | ∃ e : (Fin q.L × Fin W) × (Fin q.L × Fin W),
      (W : ℝ) ^ ε * Real.sqrt ζ < ‖(flowG W (q.at q.u) ω - flowM W (q.at q.u)) e.1 e.2‖} ⊆
      E₁ ∪ E₂ := by
    rintro ω ⟨e, he⟩
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨n1, n2⟩ := hcon
    have hT : ‖segG W (step2X q) ω e.1 e.2 -
        if e.1.2 = e.2.2 then blockTr (segG W (step2X q) ω) e.1.1 e.2.1 else 0‖ ≤
        (W : ℝ) ^ (ε / 2) * (1 * χ W (step2X q)) := not_lt.mp fun h => n1 ⟨e, h⟩
    have hA : ‖blockTr (flowG W (q.at q.u) ω - flowM W (q.at q.u)) e.1.1 e.2.1‖ ≤
        (W : ℝ) ^ (ε / 2) * ζ := not_lt.mp fun h => n2 ⟨(e.1.1, e.2.1), h⟩
    have eG : segG W (step2X q) ω = flowG W (q.at q.u) ω := step2_segG_eta W (q.at q.u) ω
    rw [eG] at hT
    have hχ' : χ W (step2X q) = 2 * Real.sqrt ζ := rfl
    rw [hχ', one_mul] at hT
    -- the decomposition of an entry
    have hk : blockTr (flowM W (q.at q.u)) e.1.1 e.2.1 =
        dysonMat (hopB q.g) (gammaG q.g) q.L q.E (mRoot q.g q.L q.E) e.1.1 e.2.1 :=
      step2_blockTr_kron W q.L hW1 _ e.1.1 e.2.1
    have hs := step2_blockTr_sub (flowG W (q.at q.u) ω) (flowM W (q.at q.u)) e.1.1 e.2.1
    rw [hk] at hs
    have hdec : (flowG W (q.at q.u) ω - flowM W (q.at q.u)) e.1 e.2 =
        (flowG W (q.at q.u) ω e.1 e.2 -
          if e.1.2 = e.2.2 then blockTr (flowG W (q.at q.u) ω) e.1.1 e.2.1 else 0) +
        if e.1.2 = e.2.2 then blockTr (flowG W (q.at q.u) ω - flowM W (q.at q.u)) e.1.1 e.2.1
          else 0 :=
      step2_entry_decomp hW1 (flowG W (q.at q.u) ω)
        (dysonMat (hopB q.g) (gammaG q.g) q.L q.E (mRoot q.g q.L q.E)) e.1 e.2
    have hsq : ζ ≤ Real.sqrt ζ := by
      rw [Real.le_sqrt hζ0.le hζ0.le]
      nlinarith
    have hb : ‖(flowG W (q.at q.u) ω - flowM W (q.at q.u)) e.1 e.2‖ ≤
        (W : ℝ) ^ (ε / 2) * (2 * Real.sqrt ζ) + (W : ℝ) ^ (ε / 2) * ζ := by
      rw [hdec]
      refine (norm_add_le _ _).trans (add_le_add hT ?_)
      split_ifs
      · exact hA
      · simp only [norm_zero]; positivity
    have hW3 := hW₃ W hW3'
    have hsplit : (W : ℝ) ^ ε = (W : ℝ) ^ (ε / 2) * (W : ℝ) ^ (ε / 2) := by
      rw [← Real.rpow_add hW0]; ring_nf
    have hfin : (W : ℝ) ^ (ε / 2) * (2 * Real.sqrt ζ) + (W : ℝ) ^ (ε / 2) * ζ ≤
        (W : ℝ) ^ ε * Real.sqrt ζ := by
      rw [hsplit]
      have h0 : 0 ≤ (W : ℝ) ^ (ε / 2) := by positivity
      have h1 : (W : ℝ) ^ (ε / 2) * ζ ≤ (W : ℝ) ^ (ε / 2) * Real.sqrt ζ :=
        mul_le_mul_of_nonneg_left hsq h0
      have h2 : 3 * ((W : ℝ) ^ (ε / 2) * Real.sqrt ζ) ≤
          (W : ℝ) ^ (ε / 2) * ((W : ℝ) ^ (ε / 2) * Real.sqrt ζ) :=
        mul_le_mul_of_nonneg_right hW3 (by positivity)
      nlinarith
    linarith
  calc μ W q.L {ω | ∃ e : (Fin q.L × Fin W) × (Fin q.L × Fin W),
        (W : ℝ) ^ ε * Real.sqrt ζ < ‖(flowG W (q.at q.u) ω - flowM W (q.at q.u)) e.1 e.2‖}
      ≤ μ W q.L (E₁ ∪ E₂) := measure_mono hsub
    _ ≤ μ W q.L E₁ + μ W q.L E₂ := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) :=
        add_le_add h₁ h₂
    _ ≤ _ := step2_two' W hW2 D

end Step2Local

/-- Step 2 of Appendix C.3 [sec:gc-one-step] at fixed times: the mixed-pair bound, then the
propagated mixed-pair estimate (`Y_v = (U^{+-}_{u,v})^{⊗2} D₂`, the moment comparison) bring the
loss to `R^6`; with the Haar bound (5.30) [gc:eq:haar] and two uses of (5.29)
[gc:eq:averaging-input], the sharp local law of (C.15) [fo:eq:step2]. -/
theorem step2 (R : PropRegime) (I : PropInputs R.base R.J) (c cp θ N : ℝ) (hc : 0 < c)
    (hcp : 0 < cp) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2) (hN : lemmaNN0 I.Cw ≤ N) :
    ∃ cp₂ : ℝ, 0 < cp₂ ∧ cp₂ ≤ cp ∧ ∀ S : ℕ → Set StepPt, (∀ W, S W ⊆ {q | StepAdm R c N W q}) →
      (∀ W, ∀ q ∈ S W, ∀ v : ℝ, q.s ≤ v → v ≤ q.u →
        (⟨q.g, q.E, q.L, q.s, q.t, v⟩ : StepPt) ∈ S W) →
      OneStepInput cp θ (fun q : StepPt => q.at q.s) S →
      OneStepInput cp θ (fun q : StepPt => cmpPt (q.at q.u) q.s) S → Step1Out S →
      Step2Out cp₂ θ S := by
  obtain ⟨cw, hcw0, hcwcp, -, hpair⟩ := step2_pair R I c cp θ N hc hcp hθ hθ2 hN
  refine ⟨cw, hcw0, hcwcp, fun S hS hSu hin hcmp h1 => ?_⟩
  have hN20 : (20 : ℝ) ≤ N := le_trans (le_max_left _ _) hN
  have hP := hpair S hS hSu hin h1
  have hHS := step2_hs_out R c N hc hN20 S hS hcw0.le (hP 1 one_pos)
  obtain ⟨hent, havg⟩ := step2_local R I c N hc hN20 S hS hcmp h1 hHS
  exact ⟨hP, hHS, hent, havg⟩

end LSBA
