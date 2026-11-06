import LSBA.Averaging.Vertical

/-!
# Branch selection in Lemma 5.6 [fo:prop:inputs]

The deterministic dichotomy and contraction for the averaged residual combination (the scalar
equations (5.32) [gc:eq:scalar] as a max-norm contraction), the Lipschitz bound of block traces
along vertical lines, and the bounds on centered block traces and traceless entries of Lemma 5.6
[fo:prop:inputs] at each fixed time.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Entries, blocks and Ward identities -/

/-- An entry is bounded by the operator norm. -/
private lemma branch_entry_le {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (i j : n) : ‖M i j‖ ≤ ‖M‖ := by
  have h := Matrix.l2_opNorm_mulVec M (EuclideanSpace.single j (1 : ℂ))
  have hn : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  rw [hn, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le ((EuclideanSpace.equiv n ℂ).symm
    (M.mulVec (EuclideanSpace.single j (1 : ℂ)).ofLp)) i
  convert this using 2
  simp

/-- `Σ_α ‖G_{aα,aα}‖ ≤ W ‖G_{aa}‖`. -/
private lemma branch_sum_diag_le {W L : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a : Fin L) : ∑ α : Fin W, ‖X (a, α) (a, α)‖ ≤ W * ‖blockOf X a a‖ := by
  calc ∑ α : Fin W, ‖X (a, α) (a, α)‖ ≤ ∑ _α : Fin W, ‖blockOf X a a‖ :=
        Finset.sum_le_sum fun α _ => branch_entry_le (blockOf X a a) α α
    _ = W * ‖blockOf X a a‖ := by simp

/-- Column Ward identity `Σ_v |G_{vx}|² = Im G_{xx} / Im z`. -/
private lemma branch_ward_col {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) {z : ℂ} (hz : 0 < z.im) (x : n) :
    ∑ v, ‖resolventMat A z v x‖ ^ 2 = (resolventMat A z x x).im / z.im := by
  have hz0 : z.im ≠ 0 := hz.ne'
  have hx := congrFun (congrFun (ward_matrix hA hz0) x) x
  rw [Matrix.mul_apply] at hx
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply] at hx
  have e : ∑ v, star (resolventMat A z v x) * resolventMat A z v x =
      ((∑ v, ‖resolventMat A z v x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  rw [e, smul_eq_mul] at hx
  have hw : ∀ w : ℂ, w - star w = ((2 * w.im : ℝ) : ℂ) * Complex.I := fun w => by
    apply Complex.ext <;> simp [two_mul]
  rw [hw] at hx
  apply Complex.ofReal_injective
  rw [hx]
  push_cast
  have : (z.im : ℂ) ≠ 0 := by exact_mod_cast hz0
  field_simp

/-- Row Ward identity `Σ_v |G_{xv}|² = Im G_{xx} / Im z`. -/
private lemma branch_ward_row {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) {z : ℂ} (hz : 0 < z.im) (x : n) :
    ∑ v, ‖resolventMat A z x v‖ ^ 2 = (resolventMat A z x x).im / z.im := by
  have h := ward hA z.re hz.ne' x
  rwa [Complex.re_add_im] at h

/-- `Im G_{xx}(E + iy') / y' ≤ Im G_{xx}(E + iy) / y` for `0 < y ≤ y'`. -/
private lemma branch_im_div_anti {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (E : ℝ) {y y' : ℝ} (hy : 0 < y) (hyy : y ≤ y') (x : n) :
    (resolventMat A (E + y' * Complex.I) x x).im / y' ≤
      (resolventMat A (E + y * Complex.I) x x).im / y := by
  have hy' : 0 < y' := lt_of_lt_of_le hy hyy
  rw [im_resolventMat_diag hA E hy'.ne' x, im_resolventMat_diag hA E hy.ne' x,
    Finset.sum_div, Finset.sum_div]
  refine Finset.sum_le_sum fun k _ => ?_
  have e : ∀ t : ℝ, 0 < t → t * ‖hA.eigenvectorBasis k x‖ ^ 2 /
      ((hA.eigenvalues k - E) ^ 2 + t ^ 2) / t =
      ‖hA.eigenvectorBasis k x‖ ^ 2 / ((hA.eigenvalues k - E) ^ 2 + t ^ 2) := by
    intro t ht
    have : (hA.eigenvalues k - E) ^ 2 + t ^ 2 ≠ 0 := by positivity
    field_simp
  rw [e y' hy', e y hy]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (by nlinarith [sq_nonneg (hA.eigenvalues k - E)])

/-- The resolvent identity in the spectral parameter. -/
private lemma branch_resolvent_sub {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) {z z' : ℂ} (hz : z.im ≠ 0) (hz' : z'.im ≠ 0) :
    resolventMat A z' - resolventMat A z =
      (z' - z) • (resolventMat A z' * resolventMat A z) := by
  have h1 := sub_smul_mul_resolventMat hA hz
  have h2 := mul_eq_one_comm.mp (sub_smul_mul_resolventMat hA hz')
  calc resolventMat A z' - resolventMat A z
      = resolventMat A z' * ((A - z • (1 : Matrix n n ℂ)) * resolventMat A z) -
          (resolventMat A z' * (A - z' • (1 : Matrix n n ℂ))) * resolventMat A z := by
        rw [h1, h2, Matrix.mul_one, Matrix.one_mul]
    _ = resolventMat A z' * ((A - z • (1 : Matrix n n ℂ)) - (A - z' • (1 : Matrix n n ℂ))) *
          resolventMat A z := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    _ = (z' - z) • (resolventMat A z' * resolventMat A z) := by
        have : (A - z • (1 : Matrix n n ℂ)) - (A - z' • (1 : Matrix n n ℂ)) =
            (z' - z) • (1 : Matrix n n ℂ) := by
          rw [sub_smul]; abel
        rw [this, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- `‖Σ_v p_v q_v‖ ≤ (Σ_v ‖p_v‖² + Σ_v ‖q_v‖²)/2`. -/
private lemma branch_norm_sum_mul_le {ι : Type*} (s : Finset ι) (p q : ι → ℂ) :
    ‖∑ v ∈ s, p v * q v‖ ≤ (∑ v ∈ s, ‖p v‖ ^ 2 + ∑ v ∈ s, ‖q v‖ ^ 2) / 2 := by
  calc ‖∑ v ∈ s, p v * q v‖ ≤ ∑ v ∈ s, ‖p v * q v‖ := norm_sum_le _ _
    _ ≤ ∑ v ∈ s, (‖p v‖ ^ 2 + ‖q v‖ ^ 2) / 2 := by
        refine Finset.sum_le_sum fun v _ => ?_
        rw [norm_mul]
        nlinarith [sq_nonneg (‖p v‖ - ‖q v‖)]
    _ = _ := by rw [← Finset.sum_div, Finset.sum_add_distrib]

/-- `D_{ab} = -resComb_{ab} + β Σ_c M_{ac} D_{cc} ⟨G⟩_{cb}` gives the norm bound. -/
private lemma branch_resComb_bound {W L : ℕ} (β : ℝ) (hβ : 0 ≤ β)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (M : Matrix (Fin L) (Fin L) ℂ) (a b : Fin L) :
    ‖blockTr G a b - M a b‖ ≤ ‖resComb β G M a b‖ +
      β * ∑ c, ‖M a c‖ * ‖blockTr G c c - M c c‖ * ‖blockTr G c b‖ := by
  have e : blockTr G a b - M a b = -resComb β G M a b +
      (β : ℂ) * ∑ c, M a c * (blockTr G c c - M c c) * blockTr G c b := by
    unfold resComb; ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add (le_of_eq (norm_neg _)) ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hβ]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (le_of_eq ?_)) hβ
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [norm_mul, norm_mul]

/-! ### The deterministic statements -/

/-- The scalar equations (5.32) [gc:eq:scalar] as a deterministic dichotomy: for a symmetric `M`
with `β Σ_c |M_{ac}| ≤ Γ` and `β Σ_c |M_{ac}|² ≤ θ < 1`, if `|resComb_{ab}| ≤ r` and
`|⟨G⟩_{ab} - M_{ab}| ≤ V` for all `a, b`, then `|⟨G⟩_{ab} - M_{ab}| ≤ (r + ΓV²)/(1 - θ)`. -/
theorem resComb_dichotomy {W L : ℕ} (β Γ θ r V : ℝ) (hβ : 0 ≤ β) (hθ : θ < 1)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (M : Matrix (Fin L) (Fin L) ℂ) (hM : Mᵀ = M)
    (hΓ : ∀ a, β * ∑ c, ‖M a c‖ ≤ Γ) (hθM : ∀ a, β * ∑ c, ‖M a c‖ ^ 2 ≤ θ)
    (hr : ∀ a b, ‖resComb β G M a b‖ ≤ r) (hV : ∀ a b, ‖blockTr G a b - M a b‖ ≤ V) :
    ∀ a b, ‖blockTr G a b - M a b‖ ≤ (r + Γ * V ^ 2) / (1 - θ) := by
  intro a b
  have : Nonempty (Fin L) := ⟨a⟩
  set D : Fin L → Fin L → ℂ := fun a b => blockTr G a b - M a b with hD
  obtain ⟨c₀, hc₀⟩ := Finite.exists_max (fun c : Fin L => ‖D c c‖)
  set U := ‖D c₀ c₀‖ with hU
  have hU0 : 0 ≤ U := norm_nonneg _
  have hV0 : 0 ≤ V := (norm_nonneg _).trans (hV a a)
  have hUV : U ≤ V := hV c₀ c₀
  have hθ0 : 0 ≤ θ := (mul_nonneg hβ (Finset.sum_nonneg fun _ _ => by positivity)).trans (hθM a)
  have hMs : ∀ c b, M c b = M b c := fun c b => by
    have := congrFun (congrFun hM b) c
    rw [Matrix.transpose_apply] at this
    exact this
  -- the basic bound `|D_{ab}| ≤ r + θU + ΓV²`
  have key : ∀ a b, ‖D a b‖ ≤ r + θ * U + Γ * V ^ 2 := by
    intro a b
    have h0 := branch_resComb_bound β hβ G M a b
    have hsplit : ∀ c, ‖M a c‖ * ‖D c c‖ * ‖blockTr G c b‖ ≤
        U * (‖M a c‖ * ‖M c b‖) + V ^ 2 * ‖M a c‖ := by
      intro c
      have hT : ‖blockTr G c b‖ ≤ ‖M c b‖ + ‖D c b‖ := by
        have : blockTr G c b = M c b + D c b := by simp [hD]
        rw [this]; exact norm_add_le _ _
      have h1 : ‖D c c‖ ≤ U := hc₀ c
      have h2 : ‖D c b‖ ≤ V := hV c b
      have h3 : ‖D c c‖ ≤ V := hV c c
      have hn1 := norm_nonneg (M a c)
      have hn2 := norm_nonneg (D c c)
      have hn3 := norm_nonneg (M c b)
      have hn4 := norm_nonneg (D c b)
      calc ‖M a c‖ * ‖D c c‖ * ‖blockTr G c b‖
          ≤ ‖M a c‖ * ‖D c c‖ * (‖M c b‖ + ‖D c b‖) :=
            mul_le_mul_of_nonneg_left hT (by positivity)
        _ = ‖D c c‖ * (‖M a c‖ * ‖M c b‖) + ‖M a c‖ * (‖D c c‖ * ‖D c b‖) := by ring
        _ ≤ U * (‖M a c‖ * ‖M c b‖) + ‖M a c‖ * (V * V) := by
            gcongr
        _ = U * (‖M a c‖ * ‖M c b‖) + V ^ 2 * ‖M a c‖ := by ring
    have hsum : β * ∑ c, ‖M a c‖ * ‖D c c‖ * ‖blockTr G c b‖ ≤
        U * (β * ∑ c, ‖M a c‖ * ‖M c b‖) + V ^ 2 * (β * ∑ c, ‖M a c‖) := by
      calc β * ∑ c, ‖M a c‖ * ‖D c c‖ * ‖blockTr G c b‖
          ≤ β * ∑ c, (U * (‖M a c‖ * ‖M c b‖) + V ^ 2 * ‖M a c‖) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => hsplit c) hβ
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring
    have hMM : β * ∑ c, ‖M a c‖ * ‖M c b‖ ≤ θ := by
      have h1 : ∑ c, ‖M a c‖ * ‖M c b‖ ≤ (∑ c, ‖M a c‖ ^ 2 + ∑ c, ‖M b c‖ ^ 2) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_le_sum fun c _ => ?_
        rw [hMs c b]
        nlinarith [sq_nonneg (‖M a c‖ - ‖M b c‖)]
      calc β * ∑ c, ‖M a c‖ * ‖M c b‖ ≤ β * ((∑ c, ‖M a c‖ ^ 2 + ∑ c, ‖M b c‖ ^ 2) / 2) :=
            mul_le_mul_of_nonneg_left h1 hβ
        _ = (β * ∑ c, ‖M a c‖ ^ 2 + β * ∑ c, ‖M b c‖ ^ 2) / 2 := by ring
        _ ≤ (θ + θ) / 2 := by linarith [hθM a, hθM b]
        _ = θ := by ring
    have hG := hΓ a
    calc ‖D a b‖ ≤ ‖resComb β G M a b‖ +
          β * ∑ c, ‖M a c‖ * ‖D c c‖ * ‖blockTr G c b‖ := h0
      _ ≤ r + (U * (β * ∑ c, ‖M a c‖ * ‖M c b‖) + V ^ 2 * (β * ∑ c, ‖M a c‖)) :=
          add_le_add (hr a b) hsum
      _ ≤ r + (U * θ + V ^ 2 * Γ) := by
          gcongr
      _ = r + θ * U + Γ * V ^ 2 := by ring
  have h1θ : 0 < 1 - θ := by linarith
  have hUle : U ≤ (r + Γ * V ^ 2) / (1 - θ) := by
    rw [le_div_iff₀ h1θ]
    have := key c₀ c₀
    linarith
  have := key a b
  rw [le_div_iff₀ h1θ] at hUle ⊢
  change ‖D a b‖ * (1 - θ) ≤ r + Γ * V ^ 2
  have h2 := mul_le_mul_of_nonneg_left hUle hθ0
  have h3 := mul_le_mul_of_nonneg_right this h1θ.le
  nlinarith

/-- `Σ_c |⟨G⟩_{cb}|² ≤ X / Im z` for `G = (H - z)⁻¹` with `‖G_{bb}‖ ≤ X`. -/
private lemma branch_ward_blockTr {W L : ℕ} (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (X : ℝ) (b : Fin L)
    (hX : ‖blockOf (resolventMat H z) b b‖ ≤ X) :
    ∑ c, ‖blockTr (resolventMat H z) c b‖ ^ 2 ≤ X / z.im := by
  set G := resolventMat H z with hG
  have hX0 : 0 ≤ X := (norm_nonneg _).trans hX
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW
    simp only [blockTr, Finset.univ_eq_empty, Finset.sum_empty, mul_zero, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    positivity
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have h1 : ∀ c, ‖blockTr G c b‖ ^ 2 ≤ (W : ℝ)⁻¹ * ∑ α, ‖G (c, α) (b, α)‖ ^ 2 := by
    intro c
    unfold blockTr
    rw [norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
    have hs : ‖∑ α, G (c, α) (b, α)‖ ^ 2 ≤ (W : ℝ) * ∑ α, ‖G (c, α) (b, α)‖ ^ 2 := by
      calc ‖∑ α, G (c, α) (b, α)‖ ^ 2 ≤ (∑ α, ‖G (c, α) (b, α)‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
        _ ≤ _ := by
            have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin W)))
              (f := fun α => ‖G (c, α) (b, α)‖)
            simpa using this
    calc (W : ℝ)⁻¹ ^ 2 * ‖∑ α, G (c, α) (b, α)‖ ^ 2 ≤
          (W : ℝ)⁻¹ ^ 2 * ((W : ℝ) * ∑ α, ‖G (c, α) (b, α)‖ ^ 2) := by gcongr
      _ = _ := by field_simp
  have h2 : ∑ c, ∑ α, ‖G (c, α) (b, α)‖ ^ 2 ≤ ∑ α, (G (b, α) (b, α)).im / z.im := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun α _ => ?_
    rw [← branch_ward_col hH hz (b, α), Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun c _ => ?_
    exact Finset.single_le_sum (f := fun β => ‖G (c, β) (b, α)‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ α)
  have h3 : ∑ α, (G (b, α) (b, α)).im / z.im ≤ W * X / z.im := by
    rw [← Finset.sum_div]
    refine div_le_div_of_nonneg_right ?_ hz.le
    calc ∑ α, (G (b, α) (b, α)).im ≤ ∑ α, ‖G (b, α) (b, α)‖ :=
          Finset.sum_le_sum fun α _ => Complex.im_le_norm _
      _ ≤ W * ‖blockOf G b b‖ := branch_sum_diag_le G b
      _ ≤ W * X := by gcongr
  calc ∑ c, ‖blockTr G c b‖ ^ 2 ≤ ∑ c, (W : ℝ)⁻¹ * ∑ α, ‖G (c, α) (b, α)‖ ^ 2 :=
        Finset.sum_le_sum fun c _ => h1 c
    _ = (W : ℝ)⁻¹ * ∑ c, ∑ α, ‖G (c, α) (b, α)‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (W : ℝ)⁻¹ * (W * X / z.im) := by gcongr; exact h2.trans h3
    _ = X / z.im := by field_simp

/-- Contraction at a large height: for `G = (H - z)⁻¹`, `H` Hermitian, the Ward bound
`Σ_c |⟨G⟩_{cb}|² ≤ Im⟨G⟩_{bb}/Im z` and `θβX/Im z ≤ 1/4` (with `β Σ_c |M_{ac}|² ≤ θ` and
`‖G_{bb}‖ ≤ X`) give `|⟨G⟩_{ab} - M_{ab}| ≤ 2 max |resComb|`. -/
theorem resComb_contraction {W L : ℕ} (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im) (β θ X r : ℝ) (hβ : 0 ≤ β)
    (M : Matrix (Fin L) (Fin L) ℂ) (hθM : ∀ a, β * ∑ c, ‖M a c‖ ^ 2 ≤ θ)
    (hX : ∀ b, ‖blockOf (resolventMat H z) b b‖ ≤ X)
    (hr : ∀ a b, ‖resComb β (resolventMat H z) M a b‖ ≤ r) (hκ : θ * β * X / z.im ≤ 1 / 4) :
    ∀ a b, ‖blockTr (resolventMat H z) a b - M a b‖ ≤ 2 * r := by
  intro a b
  have : Nonempty (Fin L) := ⟨a⟩
  set G := resolventMat H z with hG
  set D : Fin L → Fin L → ℂ := fun a b => blockTr G a b - M a b with hD
  obtain ⟨c₀, hc₀⟩ := Finite.exists_max (fun c : Fin L => ‖D c c‖)
  set U := ‖D c₀ c₀‖ with hU
  have hU0 : 0 ≤ U := norm_nonneg _
  have hθ0 : 0 ≤ θ := (mul_nonneg hβ (Finset.sum_nonneg fun _ _ => by positivity)).trans (hθM a)
  have hX0 : 0 ≤ X := (norm_nonneg _).trans (hX a)
  have hhalf : ∀ a b, β * ∑ c, ‖M a c‖ * ‖blockTr G c b‖ ≤ 1 / 2 := by
    intro a b
    have hS := branch_ward_blockTr H hH hz X b (hX b)
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun c => ‖M a c‖)
      (fun c => ‖blockTr G c b‖)
    have hs0 : 0 ≤ β * ∑ c, ‖M a c‖ * ‖blockTr G c b‖ :=
      mul_nonneg hβ (Finset.sum_nonneg fun _ _ => by positivity)
    have hsq : (β * ∑ c, ‖M a c‖ * ‖blockTr G c b‖) ^ 2 ≤ 1 / 4 := by
      rw [mul_pow]
      calc β ^ 2 * (∑ c, ‖M a c‖ * ‖blockTr G c b‖) ^ 2
          ≤ β ^ 2 * ((∑ c, ‖M a c‖ ^ 2) * ∑ c, ‖blockTr G c b‖ ^ 2) := by gcongr
        _ = β * (β * ∑ c, ‖M a c‖ ^ 2) * ∑ c, ‖blockTr G c b‖ ^ 2 := by ring
        _ ≤ β * θ * (X / z.im) := by
            have h1 : β * (β * ∑ c, ‖M a c‖ ^ 2) ≤ β * θ := mul_le_mul_of_nonneg_left (hθM a) hβ
            exact mul_le_mul h1 hS (Finset.sum_nonneg fun _ _ => by positivity)
              (mul_nonneg hβ hθ0)
        _ = θ * β * X / z.im := by ring
        _ ≤ 1 / 4 := hκ
    nlinarith
  have key : ∀ a b, ‖D a b‖ ≤ r + U / 2 := by
    intro a b
    have h0 := branch_resComb_bound β hβ G M a b
    have h1 : β * ∑ c, ‖M a c‖ * ‖D c c‖ * ‖blockTr G c b‖ ≤
        U * (β * ∑ c, ‖M a c‖ * ‖blockTr G c b‖) := by
      calc β * ∑ c, ‖M a c‖ * ‖D c c‖ * ‖blockTr G c b‖ ≤
            β * ∑ c, U * (‖M a c‖ * ‖blockTr G c b‖) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => ?_) hβ
            have := hc₀ c
            calc ‖M a c‖ * ‖D c c‖ * ‖blockTr G c b‖ = ‖D c c‖ * (‖M a c‖ * ‖blockTr G c b‖) := by
                  ring
              _ ≤ U * (‖M a c‖ * ‖blockTr G c b‖) :=
                  mul_le_mul_of_nonneg_right this (by positivity)
        _ = U * (β * ∑ c, ‖M a c‖ * ‖blockTr G c b‖) := by rw [← Finset.mul_sum]; ring
    have h2 := mul_le_mul_of_nonneg_left (hhalf a b) hU0
    have h3 := hr a b
    change ‖D a b‖ ≤ r + U / 2
    linarith
  have hU2 : U ≤ 2 * r := by
    have := key c₀ c₀
    linarith
  have := key a b
  change ‖D a b‖ ≤ 2 * r
  linarith

/-- Height continuity of block traces on a vertical line: for `H` Hermitian and
`0 < y ≤ y'`, `|⟨G(x + iy')⟩_{ab} - ⟨G(x + iy)⟩_{ab}| ≤ ((y' - y)/y) max_c ‖G_{cc}(x + iy)‖`. -/
theorem blockTr_vert_lip {W L : ℕ} (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hH : H.IsHermitian) (x y y' X : ℝ) (hy : 0 < y) (hyy : y ≤ y')
    (hX : ∀ c, ‖blockOf (resolventMat H ((x : ℂ) + (y : ℂ) * Complex.I)) c c‖ ≤ X) (a b : Fin L) :
    ‖blockTr (resolventMat H ((x : ℂ) + (y' : ℂ) * Complex.I)) a b -
        blockTr (resolventMat H ((x : ℂ) + (y : ℂ) * Complex.I)) a b‖ ≤ (y' - y) / y * X := by
  set z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I with hzdef
  set z' : ℂ := (x : ℂ) + (y' : ℂ) * Complex.I with hz'def
  set G := resolventMat H z with hG
  set G' := resolventMat H z' with hG'
  have hy' : 0 < y' := lt_of_lt_of_le hy hyy
  have hzim : z.im = y := by simp [z]
  have hz'im : z'.im = y' := by simp [z']
  have hX0 : 0 ≤ X := (norm_nonneg _).trans (hX a)
  have hdiff := branch_resolvent_sub hH (z := z) (z' := z') (by rw [hzim]; exact hy.ne')
    (by rw [hz'im]; exact hy'.ne')
  have hzz : ‖z' - z‖ = y' - y := by
    have : z' - z = ((y' - y : ℝ) : ℂ) * Complex.I := by
      simp only [z, z']; push_cast; ring
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  have hα : ∀ α : Fin W, ‖(G' * G) (a, α) (b, α)‖ ≤
      ((G (a, α) (a, α)).im / y + (G (b, α) (b, α)).im / y) / 2 := by
    intro α
    rw [Matrix.mul_apply]
    refine (branch_norm_sum_mul_le _ _ _).trans ?_
    have h1 : ∑ v, ‖G' (a, α) v‖ ^ 2 ≤ (G (a, α) (a, α)).im / y := by
      rw [hG', branch_ward_row hH (by rw [hz'im]; exact hy') (a, α), hz'im]
      exact branch_im_div_anti hH x hy hyy (a, α)
    have h2 : ∑ v, ‖G v (b, α)‖ ^ 2 = (G (b, α) (b, α)).im / y := by
      rw [hG, branch_ward_col hH (by rw [hzim]; exact hy) (b, α), hzim]
    linarith
  have hdiag : ∀ c, ∑ α : Fin W, (G (c, α) (c, α)).im ≤ W * X := by
    intro c
    calc ∑ α : Fin W, (G (c, α) (c, α)).im ≤ ∑ α, ‖G (c, α) (c, α)‖ :=
          Finset.sum_le_sum fun α _ => Complex.im_le_norm _
      _ ≤ W * ‖blockOf G c c‖ := branch_sum_diag_le G c
      _ ≤ W * X := by gcongr; exact hX c
  have hsum : ∑ α : Fin W, ‖(G' * G) (a, α) (b, α)‖ ≤ W * X / y := by
    calc ∑ α : Fin W, ‖(G' * G) (a, α) (b, α)‖ ≤
          ∑ α : Fin W, ((G (a, α) (a, α)).im / y + (G (b, α) (b, α)).im / y) / 2 :=
          Finset.sum_le_sum fun α _ => hα α
      _ = ((∑ α : Fin W, (G (a, α) (a, α)).im) / y + (∑ α : Fin W, (G (b, α) (b, α)).im) / y) /
            2 := by
          rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div]
      _ ≤ (W * X / y + W * X / y) / 2 := by
          gcongr
          · exact hdiag a
          · exact hdiag b
      _ = W * X / y := by ring
  have e : blockTr G' a b - blockTr G a b =
      (W : ℂ)⁻¹ * ((z' - z) * ∑ α, (G' * G) (a, α) (b, α)) := by
    unfold blockTr
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    have : G' (a, α) (b, α) - G (a, α) (b, α) = (G' - G) (a, α) (b, α) := rfl
    rw [this, hdiff, Matrix.smul_apply, smul_eq_mul]
  rw [e, norm_mul, norm_mul, norm_inv, Complex.norm_natCast, hzz]
  have hn : ‖∑ α, (G' * G) (a, α) (b, α)‖ ≤ W * X / y := (norm_sum_le _ _).trans hsum
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW
    simp only [Nat.cast_zero, inv_zero, zero_mul]
    exact mul_nonneg (div_nonneg (by linarith) hy.le) hX0
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  calc (W : ℝ)⁻¹ * ((y' - y) * ‖∑ α, (G' * G) (a, α) (b, α)‖) ≤
        (W : ℝ)⁻¹ * ((y' - y) * (W * X / y)) := by
        gcongr
    _ = (y' - y) / y * X := by field_simp

/-! ### Branch selection along a mesh of heights -/

/-- The small branch of the dichotomy: if `|⟨G⟩_{ab} - M_{ab}| ≤ c/(2Γ)` for all `a, b`, then
`|⟨G⟩_{ab} - M_{ab}| ≤ 2r/c`. -/
private lemma branch_small {W L : ℕ} (β Γ c r : ℝ) (hβ : 0 ≤ β) (hc : 0 < c) (hΓ0 : 0 < Γ)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (M : Matrix (Fin L) (Fin L) ℂ) (hM : Mᵀ = M)
    (hΓ : ∀ a, β * ∑ c', ‖M a c'‖ ≤ Γ) (hθM : ∀ a, β * ∑ c', ‖M a c'‖ ^ 2 ≤ 1 - c)
    (hr : ∀ a b, ‖resComb β G M a b‖ ≤ r) (hV : ∀ a b, ‖blockTr G a b - M a b‖ ≤ c / (2 * Γ)) :
    ∀ a b, ‖blockTr G a b - M a b‖ ≤ 2 * r / c := by
  intro a b
  have : Nonempty (Fin L × Fin L) := ⟨(a, b)⟩
  obtain ⟨p₀, hp₀⟩ :=
    Finite.exists_max (fun p : Fin L × Fin L => ‖blockTr G p.1 p.2 - M p.1 p.2‖)
  set V := ‖blockTr G p₀.1 p₀.2 - M p₀.1 p₀.2‖ with hVdef
  have h := resComb_dichotomy β Γ (1 - c) r V hβ (by linarith) G M hM hΓ hθM hr
    (fun a b => hp₀ (a, b)) p₀.1 p₀.2
  have hc' : 1 - (1 - c) = c := by ring
  rw [hc', le_div_iff₀ hc] at h
  have hV0 : 0 ≤ V := norm_nonneg _
  have hVs : V ≤ c / (2 * Γ) := hV _ _
  have hΓV : Γ * V ≤ c / 2 := by
    rw [le_div_iff₀ (by positivity)] at hVs
    linarith
  have hVle : V ≤ 2 * r / c := by
    rw [le_div_iff₀ hc]
    nlinarith [mul_le_mul_of_nonneg_right hΓV hV0]
  exact (hp₀ (a, b)).trans hVle

/-- Descent along heights `y_N ≥ … ≥ y_0`: a contraction start at `y_N`, the dichotomy at each
height, and steps smaller than the gap keep the small branch down to `y_0`. -/
private lemma branch_descent {W L : ℕ} (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hH : H.IsHermitian) (x : ℝ) (y : ℕ → ℝ) (N : ℕ) (Mk : ℕ → Matrix (Fin L) (Fin L) ℂ)
    (β c Γ A r h : ℝ) (hβ : 0 ≤ β) (hc : 0 < c) (hc1 : c ≤ 1) (hΓ0 : 0 < Γ) (hr0 : 0 ≤ r)
    (hy : ∀ k ≤ N, 0 < y k)
    (hstep : ∀ k < N, y k ≤ y (k + 1) ∧ (y (k + 1) - y k) / y k ≤ h)
    (hsym : ∀ k ≤ N, (Mk k)ᵀ = Mk k)
    (hΓ : ∀ k ≤ N, ∀ a, β * ∑ c', ‖Mk k a c'‖ ≤ Γ)
    (hθ : ∀ k ≤ N, ∀ a, β * ∑ c', ‖Mk k a c'‖ ^ 2 ≤ 1 - c)
    (hX : ∀ k ≤ N, ∀ a, ‖blockOf (resolventMat H ((x : ℂ) + (y k : ℂ) * Complex.I)) a a‖ ≤ A)
    (hr : ∀ k ≤ N, ∀ a b,
      ‖resComb β (resolventMat H ((x : ℂ) + (y k : ℂ) * Complex.I)) (Mk k) a b‖ ≤ r)
    (hlip : ∀ k < N, ∀ a b, ‖Mk (k + 1) a b - Mk k a b‖ ≤ Γ * h)
    (htop : (1 - c) * β * A / y N ≤ 1 / 4)
    (hgap : 2 * r / c + h * A + Γ * h ≤ c / (2 * Γ)) :
    ∀ a b, ‖blockTr (resolventMat H ((x : ℂ) + (y 0 : ℂ) * Complex.I)) a b - Mk 0 a b‖ ≤
      2 * r / c := by
  have hsmall : 2 * r ≤ 2 * r / c := by
    rw [le_div_iff₀ hc]; nlinarith
  have hN : ∀ a b, ‖blockTr (resolventMat H ((x : ℂ) + (y N : ℂ) * Complex.I)) a b -
      Mk N a b‖ ≤ 2 * r / c := by
    intro a b
    have hzim : ((x : ℂ) + (y N : ℂ) * Complex.I).im = y N := by simp
    have hz : 0 < ((x : ℂ) + (y N : ℂ) * Complex.I).im := by rw [hzim]; exact hy N le_rfl
    have := resComb_contraction H hH _ hz β (1 - c) A r hβ (Mk N) (hθ N le_rfl) (hX N le_rfl)
      (hr N le_rfl) (by rw [hzim]; exact htop) a b
    exact this.trans hsmall
  have hstepP : ∀ k < N, (∀ a b, ‖blockTr (resolventMat H ((x : ℂ) + (y (k + 1) : ℂ) *
      Complex.I)) a b - Mk (k + 1) a b‖ ≤ 2 * r / c) → ∀ a b, ‖blockTr (resolventMat H
      ((x : ℂ) + (y k : ℂ) * Complex.I)) a b - Mk k a b‖ ≤ 2 * r / c := by
    intro k hk hP
    refine branch_small β Γ c r hβ hc hΓ0 _ (Mk k) (hsym k hk.le) (hΓ k hk.le) (hθ k hk.le)
      (hr k hk.le) ?_
    intro a b
    have hlipG := blockTr_vert_lip H hH x (y k) (y (k + 1)) A (hy k hk.le) (hstep k hk).1
      (hX k hk.le) a b
    have hA0 : 0 ≤ A := (norm_nonneg _).trans (hX k hk.le a)
    have h1 : (y (k + 1) - y k) / y k * A ≤ h * A :=
      mul_le_mul_of_nonneg_right (hstep k hk).2 hA0
    set G1 := blockTr (resolventMat H ((x : ℂ) + (y (k + 1) : ℂ) * Complex.I)) a b with hG1
    set G0 := blockTr (resolventMat H ((x : ℂ) + (y k : ℂ) * Complex.I)) a b with hG0
    have e : G0 - Mk k a b =
        (G1 - Mk (k + 1) a b) - (G1 - G0) + (Mk (k + 1) a b - Mk k a b) := by ring
    rw [e]
    calc ‖(G1 - Mk (k + 1) a b) - (G1 - G0) + (Mk (k + 1) a b - Mk k a b)‖ ≤
          ‖G1 - Mk (k + 1) a b‖ + ‖G1 - G0‖ + ‖Mk (k + 1) a b - Mk k a b‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ 2 * r / c + h * A + Γ * h := by
          gcongr
          · exact hP a b
          · exact hlipG.trans h1
          · exact hlip k hk a b
      _ ≤ c / (2 * Γ) := hgap
  have key : ∀ j ≤ N, ∀ a b, ‖blockTr (resolventMat H ((x : ℂ) + (y (N - j) : ℂ) *
      Complex.I)) a b - Mk (N - j) a b‖ ≤ 2 * r / c := by
    intro j
    induction j with
    | zero => intro _; simpa using hN
    | succ j ih =>
      intro hj
      have h1 : N - (j + 1) + 1 = N - j := by omega
      apply hstepP (N - (j + 1)) (by omega)
      rw [h1]
      exact ih (by omega)
  simpa using key N le_rfl

/-- A height-Lipschitz bound from `|t ∂_t f(t/γ)| ≤ C` on `t ≥ η`:
`|f(y'/γ) - f(y/γ)| ≤ C (y' - y)/y` for `η ≤ y ≤ y'`. -/
private lemma branch_lip_of_deriv (f : ℝ → ℂ) (γ C η : ℝ) (hγ : 0 < γ) (hη : 0 < η)
    (hd : ∀ t, η ≤ t → DifferentiableAt ℝ f (t / γ) ∧ ‖((t / γ : ℝ) : ℂ) * deriv f (t / γ)‖ ≤ C)
    {y y' : ℝ} (hy : η ≤ y) (hyy : y ≤ y') : ‖f (y' / γ) - f (y / γ)‖ ≤ C * ((y' - y) / y) := by
  have hy0 : 0 < y := lt_of_lt_of_le hη hy
  have hC : 0 ≤ C := (norm_nonneg _).trans (hd y hy).2
  have hs0 : 0 < y / γ := by positivity
  have hmem : ∀ s ∈ Set.Icc (y / γ) (y' / γ), η ≤ γ * s ∧ γ * s / γ = s := by
    intro s hs
    refine ⟨?_, by field_simp⟩
    have := hs.1
    calc η ≤ y := hy
      _ = γ * (y / γ) := by field_simp
      _ ≤ γ * s := by gcongr
  have hdiff : ∀ s ∈ Set.Icc (y / γ) (y' / γ), DifferentiableAt ℝ f s := by
    intro s hs
    obtain ⟨h1, h2⟩ := hmem s hs
    have := (hd (γ * s) h1).1
    rwa [h2] at this
  have hbound : ∀ s ∈ Set.Icc (y / γ) (y' / γ), ‖deriv f s‖ ≤ C / (y / γ) := by
    intro s hs
    obtain ⟨h1, h2⟩ := hmem s hs
    have h := (hd (γ * s) h1).2
    rw [h2, norm_mul, Complex.norm_real, Real.norm_eq_abs] at h
    have hs1 : y / γ ≤ s := hs.1
    have hspos : 0 < s := lt_of_lt_of_le hs0 hs1
    rw [abs_of_pos hspos] at h
    rw [le_div_iff₀ hs0]
    calc ‖deriv f s‖ * (y / γ) ≤ ‖deriv f s‖ * s := by gcongr
      _ = s * ‖deriv f s‖ := by ring
      _ ≤ C := h
  have hle : y / γ ≤ y' / γ := by gcongr
  have hmain := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_Icc _ _)
    (Set.left_mem_Icc.2 hle) (Set.right_mem_Icc.2 hle)
  calc ‖f (y' / γ) - f (y / γ)‖ ≤ C / (y / γ) * ‖y' / γ - y / γ‖ := hmain
    _ = C * ((y' - y) / y) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        field_simp

private lemma branch_hopB {g : ℝ} (hg : 1 ≤ g) : hopB g = 1 := by
  unfold hopB; rw [max_eq_right hg, div_self (by linarith)]

private lemma branch_gammaG {g : ℝ} (hg : 1 ≤ g) : gammaG g = (g ^ 2)⁻¹ := by
  unfold gammaG; rw [max_eq_right hg]

private lemma branch_gammaG_pos (g : ℝ) : 0 < gammaG g := by
  have : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  unfold gammaG
  positivity

/-- `A_L` is symmetric. -/
private lemma branch_cycleAdj_transpose (L : ℕ) : (cycleAdj L)ᵀ = cycleAdj L := by
  ext a b
  simp only [Matrix.transpose_apply, cycleAdj, Matrix.of_apply]
  exact add_comm _ _

/-- `M_{B,u}(z)` is symmetric. -/
private lemma branch_segMat_symm (g : ℝ) (L : ℕ) (x u r : ℝ) :
    (segMat g L x u r)ᵀ = segMat g L x u r := by
  unfold segMat dysonMat
  rw [Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_smul, Matrix.transpose_one, branch_cycleAdj_transpose]

/-- `⟨X - Y⟩_{ab} = ⟨X⟩_{ab} - ⟨Y⟩_{ab}`. -/
private lemma branch_blockTr_sub {W L : ℕ} (X Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : blockTr (X - Y) a b = blockTr X a b - blockTr Y a b := by
  unfold blockTr
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  rfl

/-- The entries of `M = M_B ⊗ I_W`: `M_{ai,bj} = δ_{ij} ⟨M⟩_{ab}`. -/
private lemma branch_flowM_entry (W : ℕ) (hW : 1 ≤ W) (p : FlowPt) (a : Fin p.L) (i : Fin W)
    (b : Fin p.L) (j : Fin W) :
    flowM W p (a, i) (b, j) = if i = j then blockTr (flowM W p) a b else 0 := by
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast (show W ≠ 0 by omega)
  have htr : blockTr (flowM W p) a b =
      dysonMat (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E) a b := by
    unfold blockTr flowM
    simp only [Matrix.kronecker_apply, Matrix.one_apply_eq, mul_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [htr]
  unfold flowM
  rw [Matrix.kronecker_apply, Matrix.one_apply]
  split_ifs <;> simp

/-- `ζ_u ≥ (2W)⁻¹` for `g ≥ 1`, `u ∈ [0, 1/2]`, `L ≥ 1` ((5.18) [fo:eq:scale]). -/
private lemma branch_zeta_lower (W : ℕ) (hW : 1 ≤ W) (p : FlowPt) (hg : 1 ≤ p.g)
    (hu0 : 0 ≤ p.u) (hu1 : p.u ≤ 1 / 2) (hL : 1 ≤ p.L) : ((2 : ℝ) * W)⁻¹ ≤ flowZeta W p := by
  unfold flowZeta zetaProp ellProp
  rw [branch_gammaG hg]
  have hg0 : 0 < p.g := by linarith
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  have hL1 : (1 : ℝ) ≤ p.L := by exact_mod_cast hL
  set s : ℝ := Real.sqrt ((p.g ^ 2)⁻¹ * (1 - p.u)) with hs
  have hin : 0 < (p.g ^ 2)⁻¹ * (1 - p.u) := by
    have : 0 < 1 - p.u := by linarith
    positivity
  have hs0 : 0 < s := Real.sqrt_pos.2 hin
  have hss : s ^ 2 = (p.g ^ 2)⁻¹ * (1 - p.u) := Real.sq_sqrt hin.le
  have hs2 : s ^ 2 ≤ 1 := by
    rw [hss]
    have : (p.g ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hg)
    nlinarith
  have hgs : p.g * s ≤ 1 := by
    have h1 : (p.g * s) ^ 2 ≤ 1 := by
      rw [mul_pow, hss]
      have : p.g ^ 2 * ((p.g ^ 2)⁻¹ * (1 - p.u)) = 1 - p.u := by field_simp
      rw [this]; linarith
    nlinarith [mul_pos hg0 hs0]
  set ℓ : ℝ := min (p.L : ℝ) (1 + p.g / s) with hℓ
  have hℓ0 : 0 < ℓ := lt_min (by linarith) (by positivity)
  have hℓ1 : ℓ ≤ 1 + p.g / s := min_le_right _ _
  have hP : ℓ * (1 - p.u) * (p.g ^ 2)⁻¹ ≤ 2 := by
    calc ℓ * (1 - p.u) * (p.g ^ 2)⁻¹ = ℓ * s ^ 2 := by rw [hss]; ring
      _ ≤ (1 + p.g / s) * s ^ 2 := by gcongr
      _ = s ^ 2 + p.g * s := by field_simp
      _ ≤ 2 := by linarith
  have hP0 : 0 < ℓ * (1 - p.u) * (p.g ^ 2)⁻¹ := by
    have : 0 < 1 - p.u := by linarith
    positivity
  have e : (W : ℝ) * ℓ * (1 - p.u) * (p.g ^ 2)⁻¹ = W * (ℓ * (1 - p.u) * (p.g ^ 2)⁻¹) := by ring
  rw [e]
  refine inv_anti₀ (by positivity) ?_
  nlinarith

/-- The averaged and entrywise bounds at `y = η_u` on the event where the maxima of `vert_max` hold
at every height of the mesh `y_k = η_u (1 + k/W)`, `0 ≤ k ≤ N`, from `η_u` up to `2W^ε/g²`. -/
private theorem branch_core (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) :
    ∃ c : ℝ, 0 < c ∧ ∃ Cκ₀ : ℝ, 1 ≤ Cκ₀ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ,
      Tendsto ρ atTop atTop → ∀ ε D : ℝ, 0 < ε → ε ≤ 1 / 16 → 0 < D → ∃ W₀ : ℕ, ∀ W : ℕ,
        W₀ ≤ W → ∀ p ∈ initLarge κ Cκ CV ρ W,
        μ W p.L {ω | ∃ a b : Fin p.L,
          2 * ((W : ℝ) ^ ε / W) / c < ‖blockTr (flowG W p ω - flowM W p) a b‖ ∨
          ∃ i j : Fin W, (W : ℝ) ^ (ε - 1 / 2) <
            ‖flowG W p ω (a, i) (b, j) - if i = j then blockTr (flowG W p ω) a b else 0‖} ≤
          ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  obtain ⟨Cκ₁, R₁, c, C', hCκ₁, hR₁, hc, hC', HV⟩ := dysonVert_large κ hκ hκ2
  obtain ⟨Cκ₂, R₂, c₂, C₂, hCκ₂, hR₂, hc₂, hC₂, HP⟩ := large_periodic_comparison κ hκ hκ2
  obtain ⟨Cκ₃, hCκ₃, HM⟩ := vert_max κ CV hκ hκ2 hCV
  set c₀ : ℝ := min c 1 with hc₀def
  have hc₀ : 0 < c₀ := lt_min hc one_pos
  have hc₀1 : c₀ ≤ 1 := min_le_right _ _
  have hc₀c : c₀ ≤ c := min_le_left _ _
  refine ⟨c₀, hc₀, max Cκ₁ (max Cκ₂ Cκ₃), le_trans hCκ₁ (le_max_left _ _), ?_⟩
  intro Cκ hCκ ρ hρ ε D hε hε16 hD
  have hCκ1 : Cκ₁ ≤ Cκ := le_trans (le_max_left _ _) hCκ
  have hCκ2 : Cκ₂ ≤ Cκ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCκ
  have hCκ3 : Cκ₃ ≤ Cκ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCκ
  obtain ⟨W₃, HW₃⟩ := HM Cκ hCκ3 ρ hρ ε (D + 3) hε (by linarith)
  set Kq : ℝ := max 1 (max (2 * C₂ + 2) ((2 / c₀ + 1 + C') * (2 * C' / c₀))) with hKq
  have hmax3 : (3 : ℝ) ≤ max R₁ (max R₂ 3) := le_trans (le_max_right _ _) (le_max_right _ _)
  set Kρ : ℝ := max R₁ (max R₂ 3) / Real.log 2 with hKρ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKρ0 : 0 ≤ Kρ := div_nonneg (by linarith) hlog2.le
  have ev1 : ∀ᶠ W : ℕ in atTop, Kq ≤ (W : ℝ) ^ (1 / 16 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 16)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop Kq
  have ev2 : ∀ᶠ W : ℕ in atTop, Kρ ≤ ρ W := hρ.eventually_ge_atTop Kρ
  have ev3 : ∀ᶠ W : ℕ in atTop, max W₃ (max 2 ⌈4 * C₂ + 2⌉₊) ≤ W := eventually_ge_atTop _
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.1 (ev1.and (ev2.and ev3))
  refine ⟨W₀, fun W hW p hp => ?_⟩
  obtain ⟨hq, hρW, hWb⟩ := hW₀ W hW
  have hW3 : W₃ ≤ W := le_trans (le_max_left _ _) hWb
  have hW2 : 2 ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hWb
  have hWC : 4 * C₂ + 2 ≤ (W : ℝ) := le_trans (Nat.le_ceil _)
    (by exact_mod_cast le_trans (le_max_right _ _) (le_max_right _ _) |>.trans hWb)
  have hW2r : (2 : ℝ) ≤ W := by exact_mod_cast hW2
  have hW0 : (0 : ℝ) < W := by linarith
  have hW1 : (1 : ℝ) ≤ W := by linarith
  have hp' := hp
  obtain ⟨hgC, hE, hLlow, -, hu0, hu1⟩ := hp'
  have hg1 : 1 ≤ p.g := le_trans (le_trans hCκ₁ hCκ1) hgC
  have hg0 : 0 < p.g := by linarith
  have hgg : 1 ≤ p.g ^ 2 := one_le_pow₀ hg1
  -- volume
  have hlogW : Real.log 2 ≤ Real.log W := Real.log_le_log (by norm_num) hW2r
  have hρlog : max R₁ (max R₂ 3) ≤ ρ W * Real.log W := by
    calc max R₁ (max R₂ 3) = Kρ * Real.log 2 := by rw [hKρ, div_mul_cancel₀ _ hlog2.ne']
      _ ≤ ρ W * Real.log W := mul_le_mul hρW hlogW hlog2.le (le_trans hKρ0 hρW)
  have hLR : ∀ R, R ≤ max R₁ (max R₂ 3) → R * p.g ^ 2 ≤ p.L := fun R hR => by
    calc R * p.g ^ 2 ≤ (ρ W * Real.log W) * p.g ^ 2 :=
          mul_le_mul_of_nonneg_right (hR.trans hρlog) (by positivity)
      _ = ρ W * p.g ^ 2 * Real.log W := by ring
      _ ≤ p.L := hLlow
  have hLR₁ := hLR R₁ (le_max_left _ _)
  have hLR₂ := hLR R₂ (le_trans (le_max_left _ _) (le_max_right _ _))
  have hL3 : 3 ≤ p.L := by
    have h := hLR 3 hmax3
    have : (3 : ℝ) ≤ p.L :=
      le_trans (by linarith [mul_le_mul_of_nonneg_left hgg (by norm_num : (0 : ℝ) ≤ 3)]) h
    exact_mod_cast this
  -- the root
  obtain ⟨m, -, hm, -, hmim, hmC, -⟩ := HP p.g (le_trans hCκ2 hgC) p.L hLR₂ p.E hE
  have hb0 : 0 ≤ hopB p.g := by rw [branch_hopB hg1]; norm_num
  have hmR : mRoot p.g p.L p.E = m :=
    (mRootV_spec (hopB p.g) (gammaG p.g) hb0 (branch_gammaG_pos _) p.L hL3 ((p.E : ℝ) : ℂ)
      (by simp)).2 m hm
  have hm' : IsDysonRootV (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E) := by
    rw [hmR]; exact hm
  rcases hu0.eq_or_lt with hu | hupos
  · -- `u = 0`: `G = M`
    have hG : ∀ ω, flowG W p ω = flowM W p := by
      intro ω
      unfold flowG flowM
      rw [← hu]
      exact resolvent_flow_zero p.g p.E W p.L _ ω
    have hempty : {ω : Ω W p.L | ∃ a b : Fin p.L,
        2 * ((W : ℝ) ^ ε / W) / c₀ < ‖blockTr (flowG W p ω - flowM W p) a b‖ ∨
        ∃ i j : Fin W, (W : ℝ) ^ (ε - 1 / 2) <
          ‖flowG W p ω (a, i) (b, j) - if i = j then blockTr (flowG W p ω) a b else 0‖} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      intro a b h
      rw [hG ω] at h
      rcases h with h | ⟨i, j, h⟩
      · rw [sub_self] at h
        simp only [blockTr, Matrix.zero_apply, Finset.sum_const_zero, mul_zero, norm_zero] at h
        have : 0 < 2 * ((W : ℝ) ^ ε / W) / c₀ := by positivity
        linarith
      · rw [← branch_flowM_entry W (by omega) p a i b j, sub_self, norm_zero] at h
        have : 0 < (W : ℝ) ^ (ε - 1 / 2) := by positivity
        linarith
    rw [hempty, measure_empty]
    exact bot_le
  -- `u > 0`
  have hγ : gammaG p.g = (p.g ^ 2)⁻¹ := branch_gammaG hg1
  have hγ0 : 0 < gammaG p.g := branch_gammaG_pos _
  set η : ℝ := etaChar p.g (mRoot p.g p.L p.E) p.u with hηdef
  have hgη : p.g ^ 2 * η = (1 - p.u) * m.im := by
    rw [hηdef]; unfold etaChar; rw [hγ, hmR]; field_simp
  have hη0 : 0 < η := by
    rw [hηdef]; unfold etaChar; rw [hmR]
    have : 0 < 1 - p.u := by linarith
    have := hm.1
    positivity
  have hgη_lo : (2 * C₂)⁻¹ ≤ p.g ^ 2 * η := by
    rw [hgη]
    have h1 : (1 : ℝ) / 2 ≤ 1 - p.u := by linarith
    calc (2 * C₂)⁻¹ = (1 / 2) * C₂⁻¹ := by field_simp
      _ ≤ (1 - p.u) * m.im := mul_le_mul h1 hmim (inv_nonneg.2 hC₂.le) (by linarith)
  have hgη_hi : p.g ^ 2 * η ≤ C₂ := by
    rw [hgη]
    have h1 : m.im ≤ C₂ := (Complex.im_le_norm m).trans hmC
    have h2 : 0 < m.im := hm.1
    have h3 : (1 - p.u) * m.im ≤ 1 * m.im := mul_le_mul_of_nonneg_right (by linarith) h2.le
    linarith
  have hgη0 : 0 < p.g ^ 2 * η := by positivity
  set x₀ : ℝ := (zChar p.g p.E (mRoot p.g p.L p.E) p.u).re with hx₀
  -- powers of `W`
  set A : ℝ := (W : ℝ) ^ ε with hAdef
  set q : ℝ := (W : ℝ) ^ (1 / 16 : ℝ) with hqdef
  have hA0 : 0 < A := Real.rpow_pos_of_pos hW0 _
  have hAq : A ≤ q := Real.rpow_le_rpow_of_exponent_le hW1 hε16
  have hq1 : 1 ≤ q := le_trans (le_max_left _ _) hq
  have hq16 : q ^ 16 = W := by
    rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; norm_num
  have hq8 : q ^ 8 = (W : ℝ) ^ (1 / 2 : ℝ) := by
    rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; norm_num
  have hqW : q ≤ W := by rw [← hq16]; exact le_self_pow₀ hq1 (by norm_num)
  have hq28 : q ^ 2 ≤ q ^ 8 := pow_le_pow_right₀ hq1 (by norm_num)
  have hq216 : q ^ 2 ≤ q ^ 16 := pow_le_pow_right₀ hq1 (by norm_num)
  have hrp1 : (W : ℝ) ^ (ε - 1) = A / W := by rw [Real.rpow_sub hW0, Real.rpow_one]
  -- the mesh
  set N : ℕ := ⌈2 * A * W / (p.g ^ 2 * η)⌉₊ with hNdef
  have hN_lo : 2 * A * W / (p.g ^ 2 * η) ≤ N := Nat.le_ceil _
  have hN_hi : (N : ℝ) < 2 * A * W / (p.g ^ 2 * η) + 1 := Nat.ceil_lt_add_one (by positivity)
  set y : ℕ → ℝ := fun k => η * (1 + (k : ℝ) / W) with hydef
  have hy_pos : ∀ k, 0 < y k := fun k => by simp only [hydef]; positivity
  have hy_ge : ∀ k, η ≤ y k := fun k => by
    simp only [hydef]
    have : 0 ≤ (k : ℝ) / W := by positivity
    exact le_mul_of_one_le_right hη0.le (by linarith)
  have hy_mono : ∀ k ≤ N, y k ≤ y N := fun k hk => by
    simp only [hydef]
    have : (k : ℝ) ≤ N := by exact_mod_cast hk
    gcongr
  have hy0 : y 0 = η := by simp [hydef]
  have hyN_eq : p.g ^ 2 * y N = p.g ^ 2 * η + p.g ^ 2 * η * N / W := by
    simp only [hydef]; ring
  have hyN_lo : 2 * A ≤ p.g ^ 2 * y N := by
    have h1 : 2 * A ≤ p.g ^ 2 * η * N / W := by
      rw [le_div_iff₀ hW0]
      have := mul_le_mul_of_nonneg_left hN_lo hgη0.le
      have e : p.g ^ 2 * η * (2 * A * W / (p.g ^ 2 * η)) = 2 * A * W := by field_simp
      linarith
    rw [hyN_eq]; linarith
  have hyN_hi : p.g ^ 2 * y N ≤ 2 * C₂ + 2 * A := by
    have h1 : p.g ^ 2 * η * N ≤ 2 * A * W + p.g ^ 2 * η := by
      have := mul_le_mul_of_nonneg_left hN_hi.le hgη0.le
      have e : p.g ^ 2 * η * (2 * A * W / (p.g ^ 2 * η) + 1) = 2 * A * W + p.g ^ 2 * η := by
        field_simp
      linarith
    have h2 : p.g ^ 2 * η * N / W ≤ 2 * A + p.g ^ 2 * η := by
      rw [div_le_iff₀ hW0]
      have := mul_le_mul_of_nonneg_left hW1 hgη0.le
      linarith
    rw [hyN_eq]; linarith
  have hyk : ∀ k ≤ N, p.g ^ 2 * y k ≤ (W : ℝ) ^ (1 / 2 : ℝ) := by
    intro k hk
    rw [← hq8]
    have hK : 2 * C₂ + 2 ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hq
    calc p.g ^ 2 * y k ≤ p.g ^ 2 * y N := by gcongr; exact hy_mono k hk
      _ ≤ 2 * C₂ + 2 * A := hyN_hi
      _ ≤ 2 * C₂ + 2 * q := by linarith
      _ ≤ (2 * C₂ + 2) * q := by
          have := mul_le_mul_of_nonneg_left hq1 (by positivity : (0 : ℝ) ≤ 2 * C₂)
          linarith
      _ ≤ q * q := mul_le_mul_of_nonneg_right hK (by linarith)
      _ = q ^ 2 := by ring
      _ ≤ q ^ 8 := hq28
  have hN1 : (N : ℝ) + 1 ≤ (W : ℝ) ^ 3 := by
    have h1 : 2 * A * W / (p.g ^ 2 * η) ≤ 2 * A * W * (2 * C₂) := by
      rw [div_le_iff₀ hgη0]
      have : 1 ≤ (2 * C₂) * (p.g ^ 2 * η) := by
        have := mul_le_mul_of_nonneg_left hgη_lo (by positivity : (0 : ℝ) ≤ 2 * C₂)
        rwa [mul_inv_cancel₀ (by positivity)] at this
      calc 2 * A * W = 2 * A * W * 1 := by ring
        _ ≤ 2 * A * W * ((2 * C₂) * (p.g ^ 2 * η)) := by gcongr
        _ = _ := by ring
    have h2 : A ≤ W := hAq.trans hqW
    have h3 : 2 * A * W * (2 * C₂) ≤ 4 * C₂ * W ^ 2 := by
      linarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * C₂ * W)]
    calc (N : ℝ) + 1 ≤ 2 * A * W * (2 * C₂) + 2 := by linarith
      _ ≤ 4 * C₂ * W ^ 2 + 2 := by linarith
      _ ≤ (4 * C₂ + 2) * W ^ 2 := by
          have : (1 : ℝ) ≤ W ^ 2 := one_le_pow₀ hW1
          linarith
      _ ≤ W * W ^ 2 := by gcongr
      _ = W ^ 3 := by ring
  -- the Dyson matrices along the mesh
  have hΓk : ∀ k ≤ N, ∀ a, p.u * gammaG p.g *
      ∑ c', ‖segMat p.g p.L x₀ p.u (y k / gammaG p.g) a c'‖ ≤ C' := by
    intro k _ a
    obtain ⟨-, -, -, hrow, -, -, -⟩ :=
      HV p.g (le_trans hCκ1 hgC) p.L hLR₁ p.E hE _ hm' p.u hu0 hu1 (y k) (hy_ge k)
    refine le_trans ?_ (hrow a)
    gcongr with b
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hθk : ∀ k ≤ N, ∀ a, p.u * gammaG p.g *
      ∑ c', ‖segMat p.g p.L x₀ p.u (y k / gammaG p.g) a c'‖ ^ 2 ≤ 1 - c₀ := by
    intro k _ a
    obtain ⟨-, -, -, -, hθ, -, -⟩ :=
      HV p.g (le_trans hCκ1 hgC) p.L hLR₁ p.E hE _ hm' p.u hu0 hu1 (y k) (hy_ge k)
    exact (hθ a).trans (by linarith)
  have hstep : ∀ k < N, y k ≤ y (k + 1) ∧ (y (k + 1) - y k) / y k ≤ 1 / W := by
    intro k _
    have hd : y (k + 1) - y k = η / W := by simp only [hydef]; push_cast; field_simp; ring
    refine ⟨by linarith [div_pos hη0 hW0], ?_⟩
    rw [hd, div_le_iff₀ (hy_pos k)]
    calc η / W ≤ y k / W := div_le_div_of_nonneg_right (hy_ge k) hW0.le
      _ = 1 / W * y k := by ring
  have hlipk : ∀ k < N, ∀ a b, ‖segMat p.g p.L x₀ p.u (y (k + 1) / gammaG p.g) a b -
      segMat p.g p.L x₀ p.u (y k / gammaG p.g) a b‖ ≤ C' * (1 / W) := by
    intro k hk a b
    have hd : ∀ t, η ≤ t → DifferentiableAt ℝ (fun r => segMat p.g p.L x₀ p.u r a b)
        (t / gammaG p.g) ∧ ‖((t / gammaG p.g : ℝ) : ℂ) *
          deriv (fun r => segMat p.g p.L x₀ p.u r a b) (t / gammaG p.g)‖ ≤ C' := by
      intro t ht
      obtain ⟨-, -, -, -, -, hdiff, hder⟩ :=
        HV p.g (le_trans hCκ1 hgC) p.L hLR₁ p.E hE _ hm' p.u hu0 hu1 t ht
      exact ⟨hdiff a b, hder a b⟩
    have h := branch_lip_of_deriv _ (gammaG p.g) C' η hγ0 hη0 hd (hy_ge k) (hstep k hk).1
    calc _ ≤ C' * ((y (k + 1) - y k) / y k) := h
      _ ≤ C' * (1 / W) := mul_le_mul_of_nonneg_left (hstep k hk).2 hC'.le
  have htop : (1 - c₀) * (p.u * gammaG p.g) * A / y N ≤ 1 / 4 := by
    rw [div_le_iff₀ (hy_pos N)]
    have h1 : p.u * gammaG p.g * A ≤ A * gammaG p.g / 2 := by
      have := mul_le_mul_of_nonneg_right hu1 (mul_pos hA0 hγ0).le
      linarith
    have h2 : A * gammaG p.g ≤ y N / 2 := by
      have := mul_le_mul_of_nonneg_left hyN_lo hγ0.le
      have e : gammaG p.g * (p.g ^ 2 * y N) = y N := by rw [hγ]; field_simp
      linarith
    have h3 : (1 - c₀) * (p.u * gammaG p.g * A) ≤ p.u * gammaG p.g * A := by
      have : 0 ≤ p.u * gammaG p.g * A := by positivity
      have := mul_le_mul_of_nonneg_right (by linarith : 1 - c₀ ≤ 1) this
      linarith
    calc (1 - c₀) * (p.u * gammaG p.g) * A = (1 - c₀) * (p.u * gammaG p.g * A) := by ring
      _ ≤ 1 / 4 * y N := by linarith
  have hgap : 2 * (A / W) / c₀ + 1 / W * A + C' * (1 / W) ≤ c₀ / (2 * C') := by
    have hK : (2 / c₀ + 1 + C') * (2 * C' / c₀) ≤ q :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hq
    have hX : ((2 / c₀ + 1) * A + C') * (2 * C' / c₀) ≤ W := by
      have h1 : (2 / c₀ + 1) * A + C' ≤ (2 / c₀ + 1 + C') * q := by
        have : 0 ≤ 2 / c₀ + 1 := by positivity
        linarith [mul_le_mul_of_nonneg_left hAq this, mul_le_mul_of_nonneg_left hq1 hC'.le]
      calc ((2 / c₀ + 1) * A + C') * (2 * C' / c₀) ≤
            (2 / c₀ + 1 + C') * q * (2 * C' / c₀) := by gcongr
        _ = (2 / c₀ + 1 + C') * (2 * C' / c₀) * q := by ring
        _ ≤ q * q := by gcongr
        _ = q ^ 2 := by ring
        _ ≤ q ^ 16 := hq216
        _ = W := hq16
    have e : 2 * (A / W) / c₀ + 1 / W * A + C' * (1 / W) = ((2 / c₀ + 1) * A + C') / W := by
      field_simp
    rw [e, div_le_div_iff₀ hW0 (by positivity)]
    have e2 : ((2 / c₀ + 1) * A + C') * (2 * C') =
        c₀ * (((2 / c₀ + 1) * A + C') * (2 * C' / c₀)) := by field_simp
    rw [e2]
    exact mul_le_mul_of_nonneg_left hX hc₀.le
  -- the bad events of `vert_max` along the mesh
  let S : ℕ → Set (Ω W p.L) := fun k => {ω | ∃ a b : Fin p.L,
    (W : ℝ) ^ ε < ‖blockOf (segG W (p, y k) ω) a b‖ ∨
      (W : ℝ) ^ (ε - 1) < ‖segRes W (p, y k) ω a b‖ ∨ ∃ i j : Fin W, (W : ℝ) ^ (ε - 1 / 2) <
        ‖segG W (p, y k) ω (a, i) (b, j) - if i = j then blockTr (segG W (p, y k) ω) a b else 0‖}
  have hS : ∀ k ≤ N, μ W p.L (S k) ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 3))) := fun k hk =>
    HW₃ W hW3 (p, y k) hp (hy_ge k) (hyk k hk)
  have hz0 : ((x₀ : ℂ) + ((y 0 : ℝ) : ℂ) * Complex.I) =
      zChar p.g p.E (mRoot p.g p.L p.E) p.u := by
    rw [hy0, hηdef, ← im_zChar]
    exact Complex.re_add_im _
  have hM0 : segMat p.g p.L x₀ p.u (y 0 / gammaG p.g) =
      dysonMat (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E) := by
    rw [hy0]
    exact segMat_char p.g p.E hg0.le p.L hL3 _ hm' p.u hu0 (by linarith)
  have hsub : {ω : Ω W p.L | ∃ a b : Fin p.L,
      2 * (A / W) / c₀ < ‖blockTr (flowG W p ω - flowM W p) a b‖ ∨
      ∃ i j : Fin W, (W : ℝ) ^ (ε - 1 / 2) <
        ‖flowG W p ω (a, i) (b, j) - if i = j then blockTr (flowG W p ω) a b else 0‖} ⊆
      ⋃ k ∈ Finset.range (N + 1), S k := by
    intro ω hω
    by_contra hno
    simp only [Set.mem_iUnion, Finset.mem_range, not_exists] at hno
    have hgood : ∀ k ≤ N, ∀ a b : Fin p.L, ‖blockOf (segG W (p, y k) ω) a b‖ ≤ A ∧
        ‖segRes W (p, y k) ω a b‖ ≤ A / W ∧ ∀ i j : Fin W,
          ‖segG W (p, y k) ω (a, i) (b, j) - if i = j then blockTr (segG W (p, y k) ω) a b
            else 0‖ ≤ (W : ℝ) ^ (ε - 1 / 2) := by
      intro k hk a b
      have h := hno k (by omega)
      simp only [S, Set.mem_ofPred_eq, not_exists, not_or, not_lt] at h
      obtain ⟨h1, h2, h3⟩ := h a b
      exact ⟨h1, hrp1 ▸ h2, h3⟩
    have hdesc := branch_descent (flowH p.g W p.L p.u ω) (flowH_isHermitian _ _ _ _ ω) x₀ y N
      (fun k => segMat p.g p.L x₀ p.u (y k / gammaG p.g)) (p.u * gammaG p.g) c₀ C' A (A / W)
      (1 / W) (by positivity) hc₀ hc₀1 hC' (by positivity) (fun k _ => hy_pos k) hstep
      (fun k _ => branch_segMat_symm _ _ _ _ _) hΓk hθk (fun k hk a => (hgood k hk a a).1)
      (fun k hk a b => by
        have h := (hgood k hk a b).2.1
        rw [segRes_identity W (by omega) (p, y k) hg0.le hL3 hupos (hy_pos k) ω a b] at h
        exact h)
      hlipk htop (by linarith [hgap])
    have hG0 : resolventMat (flowH p.g W p.L p.u ω) ((x₀ : ℂ) + ((y 0 : ℝ) : ℂ) * Complex.I) =
        flowG W p ω := by rw [hz0]; rfl
    obtain ⟨a, b, hab⟩ := hω
    rcases hab with h1 | ⟨i, j, h2⟩
    · have hd := hdesc a b
      rw [hG0, hM0] at hd
      have htr : blockTr (flowG W p ω - flowM W p) a b = blockTr (flowG W p ω) a b -
          dysonMat (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E) a b := by
        rw [branch_blockTr_sub]
        congr 1
        have := branch_flowM_entry W (by omega) p a ⟨0, by omega⟩ b ⟨0, by omega⟩
        simp only [↓reduceIte] at this
        rw [← this]
        unfold flowM
        rw [Matrix.kronecker_apply, Matrix.one_apply_eq, mul_one]
      rw [htr] at h1
      linarith
    · have h := (hgood 0 (Nat.zero_le _) a b).2.2 i j
      have hsg : segG W (p, y 0) ω = flowG W p ω := hG0
      rw [hsg] at h
      linarith
  calc μ W p.L _ ≤ μ W p.L (⋃ k ∈ Finset.range (N + 1), S k) := measure_mono hsub
    _ ≤ ∑ k ∈ Finset.range (N + 1), μ W p.L (S k) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range (N + 1), ENNReal.ofReal ((W : ℝ) ^ (-(D + 3))) :=
        Finset.sum_le_sum fun k hk => hS k (by simp only [Finset.mem_range] at hk; omega)
    _ = ENNReal.ofReal (((N : ℝ) + 1) * (W : ℝ) ^ (-(D + 3))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [show ((N : ℝ) + 1) = ((N + 1 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e : (W : ℝ) ^ (-(D + 3)) = (W : ℝ) ^ (-D) / (W : ℝ) ^ 3 := by
          rw [show -(D + 3) = -D - ((3 : ℕ) : ℝ) by push_cast; ring, Real.rpow_sub hW0,
            Real.rpow_natCast]
        rw [e]
        have hP : 0 ≤ (W : ℝ) ^ (-D) := by positivity
        have hW3' : (0 : ℝ) < (W : ℝ) ^ 3 := by positivity
        have : ((N : ℝ) + 1) / (W : ℝ) ^ 3 ≤ 1 := (div_le_one hW3').2 hN1
        calc ((N : ℝ) + 1) * ((W : ℝ) ^ (-D) / (W : ℝ) ^ 3) =
              (W : ℝ) ^ (-D) * (((N : ℝ) + 1) / (W : ℝ) ^ 3) := by ring
          _ ≤ (W : ℝ) ^ (-D) * 1 := by gcongr
          _ = (W : ℝ) ^ (-D) := mul_one _

/-- `K W^{ε'} ≤ W^ε` for `W ≥ 1`, `ε' ≤ ε/2` and `K ≤ W^{ε/2}`. -/
private lemma branch_pow_gain {W : ℝ} (hW : 1 ≤ W) {ε ε' K : ℝ} (hε' : ε' ≤ ε / 2)
    (hK : K ≤ W ^ (ε / 2)) : K * W ^ ε' ≤ W ^ ε := by
  have hW0 : 0 < W := by linarith
  have e : W ^ ε = W ^ (ε / 2) * W ^ (ε / 2) := by rw [← Real.rpow_add hW0]; ring_nf
  rw [e]
  have h1 : W ^ ε' ≤ W ^ (ε / 2) := Real.rpow_le_rpow_of_exponent_le hW hε'
  exact mul_le_mul hK h1 (by positivity) (by positivity)

/-! ### Lemma 5.6 [fo:prop:inputs]: the averaged and entrywise components -/

/-- Lemma 5.6 [fo:prop:inputs], the averaged component of (5.22) [gc:eq:one-step-input] at each
fixed `u ∈ [0, 1/2]`: `max_{a,b} |⟨G_u - M⟩_{ab}| ≺ ζ_u`, the small branch being selected by
continuity in `Im z` at fixed `u`. -/
theorem lemma46_avg (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) :
    ∃ Cκ₀ : ℝ, 1 ≤ Cκ₀ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      PrecMax (fun p : FlowPt => p.L) (initLarge κ Cκ CV ρ) (Λ := fun _ p => Fin p.L × Fin p.L)
        (fun W p ab ω => blockTr (flowG W p ω - flowM W p) ab.1 ab.2) (fun W p _ => flowZeta W p) := by
  obtain ⟨c, hc, Cκ₀, hCκ₀, H⟩ := branch_core κ CV hκ hκ2 hCV
  refine ⟨Cκ₀, hCκ₀, fun Cκ hCκ ρ hρ => ?_⟩
  intro ε D hε hD
  set ε' : ℝ := min (ε / 2) (1 / 16) with hε'
  have hε'0 : 0 < ε' := lt_min (by linarith) (by norm_num)
  obtain ⟨W₁, HW₁⟩ := H Cκ hCκ ρ hρ ε' D hε'0 (min_le_right _ _) hD
  obtain ⟨W₂, hW₂⟩ := eventually_atTop.1 (((tendsto_rpow_atTop (half_pos hε)).comp
    tendsto_natCast_atTop_atTop).eventually_ge_atTop (2 + 4 / c))
  refine ⟨max W₁ (max W₂ 1), fun W hW p hp => ?_⟩
  have hW1n : 1 ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1n
  have hW0 : (0 : ℝ) < W := by linarith
  have hK : 2 + 4 / c ≤ (W : ℝ) ^ (ε / 2) :=
    hW₂ W (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW)
  have hgain := branch_pow_gain hW1 (min_le_left (ε / 2) (1 / 16) : ε' ≤ ε / 2) hK
  have hg1 : 1 ≤ p.g := le_trans hCκ₀ (le_trans hCκ hp.1)
  refine le_trans (measure_mono ?_) (HW₁ W (le_trans (le_max_left _ _) hW) p hp)
  rintro ω ⟨ab, hab⟩
  refine ⟨ab.1, ab.2, Or.inl (lt_of_le_of_lt ?_ hab)⟩
  have hL : 1 ≤ p.L := Nat.one_le_iff_ne_zero.2 (fun h => by have := ab.1.2; omega)
  have hζ := branch_zeta_lower W hW1n p hg1 hp.2.2.2.2.1 hp.2.2.2.2.2 hL
  have h4 : 4 / c * (W : ℝ) ^ ε' ≤ (W : ℝ) ^ ε :=
    le_trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) hgain
  calc 2 * ((W : ℝ) ^ ε' / W) / c = (4 / c * (W : ℝ) ^ ε') * ((2 : ℝ) * W)⁻¹ := by
        field_simp; ring
    _ ≤ (W : ℝ) ^ ε * ((2 : ℝ) * W)⁻¹ := mul_le_mul_of_nonneg_right h4 (by positivity)
    _ ≤ (W : ℝ) ^ ε * flowZeta W p := by gcongr

/-- Lemma 5.6 [fo:prop:inputs], the entrywise component of (5.22) [gc:eq:one-step-input] at each
fixed `u ∈ [0, 1/2]`: `max |(G_u - M)_{ai,bj}| ≺ ζ_u^{1/2}`. -/
theorem lemma46_entry (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) :
    ∃ Cκ₀ : ℝ, 1 ≤ Cκ₀ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      PrecMax (fun p : FlowPt => p.L) (initLarge κ Cκ CV ρ)
        (Λ := fun W p => (Fin p.L × Fin W) × (Fin p.L × Fin W))
        (fun W p e ω => (flowG W p ω - flowM W p) e.1 e.2)
        (fun W p _ => Real.sqrt (flowZeta W p)) := by
  obtain ⟨c, hc, Cκ₀, hCκ₀, H⟩ := branch_core κ CV hκ hκ2 hCV
  refine ⟨Cκ₀, hCκ₀, fun Cκ hCκ ρ hρ => ?_⟩
  intro ε D hε hD
  set ε' : ℝ := min (ε / 2) (1 / 16) with hε'
  have hε'0 : 0 < ε' := lt_min (by linarith) (by norm_num)
  obtain ⟨W₁, HW₁⟩ := H Cκ hCκ ρ hρ ε' D hε'0 (min_le_right _ _) hD
  obtain ⟨W₂, hW₂⟩ := eventually_atTop.1 (((tendsto_rpow_atTop (half_pos hε)).comp
    tendsto_natCast_atTop_atTop).eventually_ge_atTop (2 + 4 / c))
  refine ⟨max W₁ (max W₂ 1), fun W hW p hp => ?_⟩
  have hW1n : 1 ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1n
  have hW0 : (0 : ℝ) < W := by linarith
  have hK : 2 + 4 / c ≤ (W : ℝ) ^ (ε / 2) :=
    hW₂ W (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW)
  have hgain := branch_pow_gain hW1 (min_le_left (ε / 2) (1 / 16) : ε' ≤ ε / 2) hK
  have hg1 : 1 ≤ p.g := le_trans hCκ₀ (le_trans hCκ hp.1)
  refine le_trans (measure_mono ?_) (HW₁ W (le_trans (le_max_left _ _) hW) p hp)
  rintro ω ⟨⟨⟨a, i⟩, ⟨b, j⟩⟩, hab⟩
  have hab' : (W : ℝ) ^ ε * Real.sqrt (flowZeta W p) <
      ‖(flowG W p ω - flowM W p) (a, i) (b, j)‖ := hab
  by_contra hno
  simp only [Set.mem_ofPred_eq, not_exists, not_or, not_lt] at hno
  have h1 := (hno a b).1
  have h2 := (hno a b).2 i j
  have hL : 1 ≤ p.L := Nat.one_le_iff_ne_zero.2 (fun h => by have := a.2; omega)
  have hζ := branch_zeta_lower W hW1n p hg1 hp.2.2.2.2.1 hp.2.2.2.2.2 hL
  have e : (flowG W p ω - flowM W p) (a, i) (b, j) =
      (flowG W p ω (a, i) (b, j) - if i = j then blockTr (flowG W p ω) a b else 0) +
        (if i = j then blockTr (flowG W p ω - flowM W p) a b else 0) := by
    rw [Matrix.sub_apply, branch_flowM_entry W hW1n p a i b j, branch_blockTr_sub]
    split_ifs <;> ring
  set X : ℝ := (W : ℝ) ^ ε' with hX
  have hX0 : 0 < X := Real.rpow_pos_of_pos hW0 _
  have hn : ‖(flowG W p ω - flowM W p) (a, i) (b, j)‖ ≤
      (W : ℝ) ^ (ε' - 1 / 2) + 2 * (X / W) / c := by
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add h2 ?_)
    split_ifs
    · exact h1
    · rw [norm_zero]; positivity
  set sW : ℝ := Real.sqrt W with hsW
  have hs0 : 0 < sW := Real.sqrt_pos.2 hW0
  have hs1 : 1 ≤ sW := by rw [hsW, ← Real.sqrt_one]; exact Real.sqrt_le_sqrt hW1
  have hss : sW ^ 2 = W := Real.sq_sqrt hW0.le
  have hsle : sW ≤ W := by nlinarith
  have hpow : (W : ℝ) ^ (ε' - 1 / 2) = X / sW := by
    rw [Real.rpow_sub hW0, hsW, Real.sqrt_eq_rpow]
  have hb1 : (W : ℝ) ^ (ε' - 1 / 2) + 2 * (X / W) / c ≤ (2 + 4 / c) * X * (2 * sW)⁻¹ := by
    rw [hpow]
    have h3 : X / W ≤ X / sW := div_le_div_of_nonneg_left hX0.le hs0 hsle
    have h4 : 2 * (X / W) / c ≤ 2 * (X / sW) / c := by gcongr
    have e2 : (2 + 4 / c) * X * (2 * sW)⁻¹ = X / sW + 2 * (X / sW) / c := by field_simp; ring
    rw [e2]
    linarith
  have hb2 : (2 * sW)⁻¹ ≤ Real.sqrt (flowZeta W p) := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (2 * sW)⁻¹)]
    refine Real.sqrt_le_sqrt (le_trans ?_ hζ)
    rw [inv_pow, mul_pow, hss]
    refine inv_anti₀ (by positivity) ?_
    linarith
  have hb : (W : ℝ) ^ (ε' - 1 / 2) + 2 * (X / W) / c ≤ (W : ℝ) ^ ε * Real.sqrt (flowZeta W p) :=
    calc _ ≤ (2 + 4 / c) * X * (2 * sW)⁻¹ := hb1
      _ ≤ (W : ℝ) ^ ε * (2 * sW)⁻¹ := mul_le_mul_of_nonneg_right hgain (by positivity)
      _ ≤ (W : ℝ) ^ ε * Real.sqrt (flowZeta W p) := by gcongr
  linarith

end LSBA
