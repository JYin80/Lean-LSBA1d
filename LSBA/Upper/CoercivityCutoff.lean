import LSBA.Upper.CoercivityTail
import LSBA.Analysis.Mollify
import LSBA.Gauss.NormTail
import LSBA.Gauss.GUELayout

/-!
# Coercivity cutoff (G.12) [cg:eq:cutoff], (10.5) [eq:c-main-cutoff], (10.14) [eq:c-main-coercivity]

For `n` independent GUE inputs `V` with the covariance (1.2) [eq:covariance] and an orthonormal
layout `G = d V` (`d dᵀ = I`, e.g. disjoint normalized differences), a `C^∞` cutoff
`0 ≤ χ ≤ 1` of compact support in the standard coordinates with `P(χ ≠ 1) ≤ C e^{-cW}`,
Hilbert–Schmidt gradient at most `L` (that is, `Σ_k (∂_k χ)² ≤ L²/W` in the standard
coordinates), and the fixed margin: on the Hilbert–Schmidt `ρ`-neighbourhood of the support,
`S_W(d V') ≥ c₁` and `‖V'_i‖ ≤ K₁`. This is (G.12) [cg:eq:cutoff] of Lemma G.4
[lem:c-gaussian] together with (10.5) [eq:c-main-cutoff] and (10.14) [eq:c-main-coercivity].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The properties of the cutoff `χ` in (G.12) [cg:eq:cutoff], (10.5) [eq:c-main-cutoff] and
(10.14) [eq:c-main-coercivity] for `n` GUE inputs, the layout `d` and the constants
`c₁, ρ, K₁, L, c, C`: `χ` is `C^∞` with compact support, `0 ≤ χ ≤ 1`, `P(χ ≠ 1) ≤ C e^{-cW}`,
`‖∇_V χ‖ ≤ L` (Hilbert–Schmidt), and on the Hilbert–Schmidt `ρ`-neighbourhood of the support
`S_W(d V') ≥ c₁` and `max_i ‖V'_i‖ ≤ K₁`. -/
def IsCoercivityCutoff (W n : ℕ) (d : Matrix (Fin 128) (Fin n) ℝ) (c₁ ρ K₁ L c C : ℝ)
    (χ : Ω W n → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ (∀ ω, 0 ≤ χ ω ∧ χ ω ≤ 1) ∧
    μ W n {ω | χ ω ≠ 1} ≤ ENNReal.ofReal (C * Real.exp (-c * W)) ∧
    (∀ ω, ∑ k, (fderiv ℝ χ ω (Pi.single k 1)) ^ 2 ≤ L ^ 2 / W) ∧
    ∀ ω ∈ tsupport χ, ∀ ω' : Ω W n, ∑ k, (ω' k - ω k) ^ 2 ≤ W * ρ ^ 2 →
      c₁ ≤ coerMin (layoutBlocks d (gueBlock W n ω')) ∧ ∀ i, ‖gueBlock W n ω' i‖ ≤ K₁

section CoercivityCutoffAux

/-! ### Coordinates, Hilbert–Schmidt norms and the layout -/

/-- The squared modulus of an entry of a block is `(x² + y²) / (2W)` for its two coordinates. -/
private lemma CoercivityCutoff_norm_sq_entry (W m : ℕ) (ω : Ω W m) (a : Fin m) (α β : Fin W) :
    ‖gueBlock W m ω a α β‖ ^ 2 = (ω (a, α, β) ^ 2 + ω (a, β, α) ^ 2) / (2 * W) := by
  have hW : (0 : ℝ) < W := by exact_mod_cast Fin.pos α
  have h2 : Real.sqrt (2 * (W : ℝ)) ^ 2 = 2 * W := Real.sq_sqrt (by positivity)
  have h1 : Real.sqrt (W : ℝ) ^ 2 = W := Real.sq_sqrt hW.le
  simp only [gueBlock, Matrix.of_apply]
  split_ifs with hab hlt
  · subst hab
    rw [norm_div, Complex.norm_real, Complex.norm_real, div_pow, Real.norm_eq_abs,
      Real.norm_eq_abs, sq_abs, sq_abs, h1]
    field_simp
    ring
  · rw [norm_div, Complex.norm_real, div_pow, Real.norm_eq_abs, sq_abs, h2]
    have : ‖(ω (a, α, β) : ℂ) + Complex.I * (ω (a, β, α) : ℂ)‖ ^ 2 =
        ω (a, α, β) ^ 2 + ω (a, β, α) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    rw [this]
  · rw [norm_div, Complex.norm_real, div_pow, Real.norm_eq_abs, sq_abs, h2]
    have : ‖(ω (a, β, α) : ℂ) - Complex.I * (ω (a, α, β) : ℂ)‖ ^ 2 =
        ω (a, α, β) ^ 2 + ω (a, β, α) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    rw [this]

/-- `Σ_j ‖V_j‖_HS² = W⁻¹ Σ_x ω_x²` in the standard coordinates. -/
private lemma CoercivityCutoff_sum_hsSq (W m : ℕ) (ω : Ω W m) :
    ∑ j, hsSq (gueBlock W m ω j) = (∑ x : Fin m × Fin W × Fin W, ω x ^ 2) / W := by
  unfold hsSq
  simp only [CoercivityCutoff_norm_sq_entry, Fintype.sum_prod_type]
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · simp
  have hW' : (W : ℝ) ≠ 0 := by positivity
  have hsw : ∀ j : Fin m, ∑ α : Fin W, ∑ β : Fin W, ω (j, β, α) ^ 2 =
      ∑ α : Fin W, ∑ β : Fin W, ω (j, α, β) ^ 2 := fun j => Finset.sum_comm
  simp only [← Finset.sum_div, Finset.sum_add_distrib, hsw]
  field_simp
  ring

/-- The block map is real-linear. -/
private lemma CoercivityCutoff_gueBlock_sub (W m : ℕ) (ω ω' : Ω W m) (j : Fin m) :
    gueBlock W m (ω - ω') j = gueBlock W m ω j - gueBlock W m ω' j := by
  ext α β
  simp only [gueBlock, Matrix.of_apply, Matrix.sub_apply, Pi.sub_apply]
  split_ifs <;> push_cast <;> ring

/-- The layout `G = d V` is real-linear in the sample. -/
private lemma CoercivityCutoff_layout_sub {m n W : ℕ} (d : Matrix (Fin m) (Fin n) ℝ)
    (ω ω' : Ω W n) (j : Fin m) :
    layoutBlocks d (gueBlock W n ω) j - layoutBlocks d (gueBlock W n ω') j =
      layoutBlocks d (gueBlock W n (ω - ω')) j := by
  simp only [layoutBlocks, CoercivityCutoff_gueBlock_sub, smul_sub, Finset.sum_sub_distrib]

/-- The standard coordinates of `G = d V` are `Σ_i d_{ji} ω_{(i, x)}`. -/
private lemma CoercivityCutoff_gueCoord_layout {m n W : ℕ} (d : Matrix (Fin m) (Fin n) ℝ)
    (ω : Ω W n) (p : Fin m × Fin W × Fin W) :
    gueCoord W m (layoutBlocks d (gueBlock W n ω)) p = ∑ i, d p.1 i * ω (i, p.2) := by
  have h := gueCoord_gueBlock W n ω
  obtain ⟨j, α, β⟩ := p
  simp only [gueCoord, layoutBlocks, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.re_sum, Complex.im_sum, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  conv_rhs => rw [← h]
  simp only [gueCoord]
  split_ifs <;> simp only [Finset.mul_sum] <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> ring

/-- Orthonormal rows `d dᵀ = I` give `‖d v‖ ≤ ‖v‖`. -/
private lemma CoercivityCutoff_sum_sq_mulVec_le {m n : ℕ} {d : Matrix (Fin m) (Fin n) ℝ}
    (hd : d * dᵀ = 1) (v : Fin n → ℝ) : ∑ j, (∑ i, d j i * v i) ^ 2 ≤ ∑ i, v i ^ 2 := by
  set u : Fin m → ℝ := d *ᵥ v with hu
  have hu' : ∀ j, ∑ i, d j i * v i = u j := fun j => rfl
  simp only [hu']
  set w : Fin n → ℝ := u ᵥ* d with hw
  have hS : ∑ j, u j ^ 2 = ∑ i, w i * v i := by
    have h := Matrix.dotProduct_mulVec u d v
    rw [← hu] at h
    simpa [dotProduct, sq] using h
  have hdw : d *ᵥ w = u := by
    rw [hw, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hd, Matrix.one_mulVec]
  have hww : ∑ i, w i ^ 2 = ∑ j, u j ^ 2 := by
    have h := Matrix.dotProduct_mulVec u d w
    rw [hdw, ← hw] at h
    simpa [dotProduct, sq] using h.symm
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w v
  rw [← hS, hww] at hcs
  have h0 : 0 ≤ ∑ j, u j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have h1 : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  nlinarith

/-- `Σ_j ‖(d V)_j‖_HS² ≤ W⁻¹ Σ_x ω_x²` for an orthonormal layout. -/
private lemma CoercivityCutoff_sum_hsSq_layout_le {n W : ℕ} {d : Matrix (Fin 128) (Fin n) ℝ}
    (hd : d * dᵀ = 1) (z : Ω W n) :
    ∑ j, hsSq (layoutBlocks d (gueBlock W n z) j) ≤ (∑ p, z p ^ 2) / W := by
  rw [← gueBlock_gueCoord_layoutBlocks d z, CoercivityCutoff_sum_hsSq]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg W)
  simp only [CoercivityCutoff_gueCoord_layout]
  calc ∑ p : Fin 128 × Fin W × Fin W, (∑ i, d p.1 i * z (i, p.2)) ^ 2
      = ∑ j : Fin 128, ∑ q : Fin W × Fin W, (∑ i, d j i * z (i, q)) ^ 2 :=
        Fintype.sum_prod_type _
    _ = ∑ q : Fin W × Fin W, ∑ j : Fin 128, (∑ i, d j i * z (i, q)) ^ 2 := Finset.sum_comm
    _ ≤ ∑ q : Fin W × Fin W, ∑ i : Fin n, z (i, q) ^ 2 :=
        Finset.sum_le_sum fun q _ => CoercivityCutoff_sum_sq_mulVec_le hd fun i => z (i, q)
    _ = ∑ i : Fin n, ∑ q : Fin W × Fin W, z (i, q) ^ 2 := Finset.sum_comm
    _ = ∑ p, z p ^ 2 := (Fintype.sum_prod_type (f := fun p => z p ^ 2)).symm

/-- `S_W(d V)` is `2 W^{-1/2}`-Lipschitz in the Euclidean distance of the standard
coordinates. -/
private lemma CoercivityCutoff_S_le {n W : ℕ} {d : Matrix (Fin 128) (Fin n) ℝ}
    (hd : d * dᵀ = 1) (x y : Ω W n) :
    coerMin (layoutBlocks d (gueBlock W n x)) ≤ coerMin (layoutBlocks d (gueBlock W n y)) +
      2 / Real.sqrt W * Real.sqrt (∑ p, (x p - y p) ^ 2) := by
  have h := abs_coerMin_sub_le (layoutBlocks d (gueBlock W n x))
    (layoutBlocks d (gueBlock W n y))
  have hs : ∑ j, hsSq (layoutBlocks d (gueBlock W n x) j - layoutBlocks d (gueBlock W n y) j) ≤
      (∑ p, (x p - y p) ^ 2) / W := by
    simp only [CoercivityCutoff_layout_sub]
    simpa only [Pi.sub_apply] using CoercivityCutoff_sum_hsSq_layout_le hd (x - y)
  have h2 : 2 * Real.sqrt (∑ j, hsSq (layoutBlocks d (gueBlock W n x) j -
      layoutBlocks d (gueBlock W n y) j)) ≤
      2 / Real.sqrt W * Real.sqrt (∑ p, (x p - y p) ^ 2) := by
    calc _ ≤ 2 * Real.sqrt ((∑ p, (x p - y p) ^ 2) / W) := by gcongr
      _ = _ := by
        rw [Real.sqrt_div (Finset.sum_nonneg fun p _ => sq_nonneg _)]
        ring
  linarith [le_abs_self (coerMin (layoutBlocks d (gueBlock W n x)) -
    coerMin (layoutBlocks d (gueBlock W n y)))]

/-- Every entry of a matrix is bounded by its operator norm. -/
private lemma CoercivityCutoff_norm_entry_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℂ) (i j : ι) : ‖X i j‖ ≤ ‖X‖ := by
  have h := Matrix.l2_opNorm_mulVec X (WithLp.toLp 2 (Pi.single j (1 : ℂ)))
  have h1 : ‖(WithLp.toLp 2 (Pi.single j (1 : ℂ)) : EuclideanSpace ℂ ι)‖ = 1 := by
    simp
  rw [h1, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le ((EuclideanSpace.equiv ι ℂ).symm (X *ᵥ Pi.single j (1 : ℂ))) i
  simpa [Matrix.mulVec_single_one] using this

/-- The operator norm of a square matrix is at most its Hilbert–Schmidt norm. -/
private lemma CoercivityCutoff_opNorm_le_hs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : ‖A‖ ≤ Real.sqrt (hsSq A) := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [mul_pow, Real.sq_sqrt (by unfold hsSq; positivity), EuclideanSpace.norm_sq_eq,
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
    _ = _ := by rw [← Finset.sum_mul]; rfl

/-- `‖V_i‖ ≤ W^{-1/2} (Σ_x ω_x²)^{1/2}` for every block. -/
private lemma CoercivityCutoff_norm_block_le {n W : ℕ} (z : Ω W n) (i : Fin n) :
    ‖gueBlock W n z i‖ ≤ Real.sqrt (∑ p, z p ^ 2) / Real.sqrt W := by
  refine (CoercivityCutoff_opNorm_le_hs _).trans ?_
  rw [← Real.sqrt_div (Finset.sum_nonneg fun p _ => sq_nonneg _), ← CoercivityCutoff_sum_hsSq]
  refine Real.sqrt_le_sqrt ?_
  exact Finset.single_le_sum (f := fun j => hsSq (gueBlock W n z j))
    (fun j _ => by unfold hsSq; positivity) (Finset.mem_univ i)

/-- `max_i ‖V_i‖`. -/
private def CoercivityCutoff_N {n W : ℕ} (ω : Ω W n) : ℝ := ⨆ i, ‖gueBlock W n ω i‖

private lemma CoercivityCutoff_N_nonneg {n W : ℕ} (ω : Ω W n) : 0 ≤ CoercivityCutoff_N ω :=
  Real.iSup_nonneg fun _ => norm_nonneg _

private lemma CoercivityCutoff_le_N {n W : ℕ} (ω : Ω W n) (i : Fin n) :
    ‖gueBlock W n ω i‖ ≤ CoercivityCutoff_N ω :=
  le_ciSup (f := fun i => ‖gueBlock W n ω i‖) (Set.finite_range _).bddAbove i

/-- `max_i ‖V_i‖` is `W^{-1/2}`-Lipschitz in the Euclidean distance of the standard
coordinates. -/
private lemma CoercivityCutoff_N_le {n W : ℕ} (x y : Ω W n) :
    CoercivityCutoff_N x ≤ CoercivityCutoff_N y +
      1 / Real.sqrt W * Real.sqrt (∑ p, (x p - y p) ^ 2) := by
  refine Real.iSup_le (fun i => ?_) (by
    have := CoercivityCutoff_N_nonneg y; positivity)
  have h1 := norm_sub_norm_le (gueBlock W n x i) (gueBlock W n y i)
  rw [← CoercivityCutoff_gueBlock_sub] at h1
  have h2 := CoercivityCutoff_norm_block_le (x - y) i
  simp only [Pi.sub_apply] at h2
  have h3 := CoercivityCutoff_le_N y i
  have h4 : Real.sqrt (∑ p, (x p - y p) ^ 2) / Real.sqrt W =
      1 / Real.sqrt W * Real.sqrt (∑ p, (x p - y p) ^ 2) := by ring
  linarith

/-- Each coordinate is bounded by `(2W)^{1/2} max_i ‖V_i‖`. -/
private lemma CoercivityCutoff_abs_le {n W : ℕ} (ω : Ω W n) (p : Fin n × Fin W × Fin W) :
    |ω p| ≤ Real.sqrt (2 * W) * CoercivityCutoff_N ω := by
  have h := congrFun (gueCoord_gueBlock W n ω) p
  obtain ⟨a, α, β⟩ := p
  have hN := CoercivityCutoff_le_N ω a
  have hs : Real.sqrt W ≤ Real.sqrt (2 * W) := Real.sqrt_le_sqrt (by
    have : (0 : ℝ) ≤ W := Nat.cast_nonneg W
    linarith)
  have hs0 : 0 ≤ Real.sqrt (2 * W) := Real.sqrt_nonneg _
  have he : ∀ x y, ‖gueBlock W n ω a x y‖ ≤ CoercivityCutoff_N ω :=
    fun x y => (CoercivityCutoff_norm_entry_le _ x y).trans hN
  rw [← h]
  simp only [gueCoord]
  split_ifs
  · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul hs ((Complex.abs_re_le_norm _).trans (he _ _)) (abs_nonneg _) hs0
  · rw [abs_mul, abs_of_nonneg hs0]
    exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (he _ _)) hs0
  · rw [abs_mul, abs_of_nonneg hs0]
    exact mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans (he _ _)) hs0

/-! ### The Lipschitz cutoff before mollification -/

/-- The clamp `t ↦ max 0 (min 1 t)`. -/
private def CoercivityCutoff_clamp (t : ℝ) : ℝ := max 0 (min 1 t)

private lemma CoercivityCutoff_clamp_nonneg (t : ℝ) : 0 ≤ CoercivityCutoff_clamp t :=
  le_max_left _ _

private lemma CoercivityCutoff_clamp_le_one (t : ℝ) : CoercivityCutoff_clamp t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

private lemma CoercivityCutoff_clamp_eq_one {t : ℝ} (ht : 1 ≤ t) :
    CoercivityCutoff_clamp t = 1 := by
  simp [CoercivityCutoff_clamp, min_eq_left ht]

private lemma CoercivityCutoff_pos_of_clamp_pos {t : ℝ} (ht : 0 < CoercivityCutoff_clamp t) :
    0 < t := by
  by_contra h
  rw [not_lt] at h
  have : CoercivityCutoff_clamp t = 0 := by
    simp only [CoercivityCutoff_clamp]
    exact max_eq_left ((min_le_right _ _).trans h)
  linarith

private lemma CoercivityCutoff_clamp_le_add (a b : ℝ) :
    CoercivityCutoff_clamp a ≤ CoercivityCutoff_clamp b + |a - b| := by
  have h1 := le_abs_self (a - b)
  have h2 := abs_nonneg (a - b)
  simp only [CoercivityCutoff_clamp, max_def, min_def]
  split_ifs <;> linarith

/-- The Lipschitz cutoff `F = min(ψ₁(S_W(d V)), ψ₂(max_i ‖V_i‖))`: `ψ₁ = 0` below `25/16`,
`ψ₁ = 1` above `35/16`; `ψ₂ = 1` below `517/32`, `ψ₂ = 0` above `549/32`; both linear
between. -/
private def CoercivityCutoff_F {n W : ℕ} (d : Matrix (Fin 128) (Fin n) ℝ) (ω : Ω W n) : ℝ :=
  min (CoercivityCutoff_clamp (8 / 5 * (coerMin (layoutBlocks d (gueBlock W n ω)) - 25 / 16)))
    (CoercivityCutoff_clamp (549 / 32 - CoercivityCutoff_N ω))

private lemma CoercivityCutoff_F_le {n W : ℕ} {d : Matrix (Fin 128) (Fin n) ℝ}
    (hd : d * dᵀ = 1) (x y : Ω W n) :
    CoercivityCutoff_F d x ≤ CoercivityCutoff_F d y +
      16 / (5 * Real.sqrt W) * Real.sqrt (∑ p, (x p - y p) ^ 2) := by
  set D := Real.sqrt (∑ p, (x p - y p) ^ 2) with hD
  have hDs : Real.sqrt (∑ p, (y p - x p) ^ 2) = D := by
    rw [hD]
    congr 1
    exact Finset.sum_congr rfl fun p _ => by ring
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hs0 : 0 ≤ Real.sqrt W := Real.sqrt_nonneg _
  have hSxy := CoercivityCutoff_S_le hd x y
  have hSyx := CoercivityCutoff_S_le hd y x
  have hNxy := CoercivityCutoff_N_le x y
  have hNyx := CoercivityCutoff_N_le y x
  rw [hDs] at hSyx hNyx
  rw [← hD] at hSxy hNxy
  have e1 : 8 / 5 * (2 / Real.sqrt W * D) = 16 / (5 * Real.sqrt W) * D := by
    rcases eq_or_lt_of_le hs0 with h | h
    · rw [← h]; simp
    · field_simp
      ring
  have e2 : 1 / Real.sqrt W * D ≤ 16 / (5 * Real.sqrt W) * D := by
    rcases eq_or_lt_of_le hs0 with h | h
    · rw [← h]; simp
    · refine mul_le_mul_of_nonneg_right ?_ hD0
      rw [div_le_div_iff₀ h (by positivity)]
      linarith
  have ha := CoercivityCutoff_clamp_le_add
    (8 / 5 * (coerMin (layoutBlocks d (gueBlock W n x)) - 25 / 16))
    (8 / 5 * (coerMin (layoutBlocks d (gueBlock W n y)) - 25 / 16))
  have hb := CoercivityCutoff_clamp_le_add (549 / 32 - CoercivityCutoff_N x)
    (549 / 32 - CoercivityCutoff_N y)
  have ha' : |8 / 5 * (coerMin (layoutBlocks d (gueBlock W n x)) - 25 / 16) -
      8 / 5 * (coerMin (layoutBlocks d (gueBlock W n y)) - 25 / 16)| ≤
      16 / (5 * Real.sqrt W) * D := by
    rw [abs_sub_le_iff]
    constructor <;> nlinarith
  have hb' : |(549 / 32 - CoercivityCutoff_N x) - (549 / 32 - CoercivityCutoff_N y)| ≤
      16 / (5 * Real.sqrt W) * D := by
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have h := le_min ((min_le_left _ _).trans (ha.trans (add_le_add le_rfl ha')))
    ((min_le_right _ _).trans (hb.trans (add_le_add le_rfl hb')))
  rw [min_add_add_right] at h
  exact h

private lemma CoercivityCutoff_F_nonneg {n W : ℕ} (d : Matrix (Fin 128) (Fin n) ℝ)
    (ω : Ω W n) : 0 ≤ CoercivityCutoff_F d ω :=
  le_min (CoercivityCutoff_clamp_nonneg _) (CoercivityCutoff_clamp_nonneg _)

private lemma CoercivityCutoff_F_le_one {n W : ℕ} (d : Matrix (Fin 128) (Fin n) ℝ)
    (ω : Ω W n) : CoercivityCutoff_F d ω ≤ 1 :=
  (min_le_left _ _).trans (CoercivityCutoff_clamp_le_one _)

/-- The Euclidean distance on the standard coordinates. -/
private lemma CoercivityCutoff_dist_eq {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℝ ι) :
    dist x y = Real.sqrt (∑ p, (x.ofLp p - y.ofLp p) ^ 2) := by
  rw [EuclideanSpace.dist_eq]
  simp [Real.dist_eq, sq_abs]

/-- `Σ_k (D e_k)² ≤ ‖D‖²` for a linear functional on a Euclidean space. -/
private lemma CoercivityCutoff_sum_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : EuclideanSpace ℝ ι →L[ℝ] ℝ) :
    ∑ k, (D (EuclideanSpace.single k 1)) ^ 2 ≤ ‖D‖ ^ 2 := by
  set x := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm D with hx
  have hk : ∀ k, D (EuclideanSpace.single k 1) = x k := by
    intro k
    rw [← InnerProductSpace.toDual_symm_apply, ← hx, EuclideanSpace.inner_single_right]
    simp
  have hn : ‖x‖ = ‖D‖ := LinearIsometryEquiv.norm_map _ _
  rw [← hn, EuclideanSpace.real_norm_sq_eq]
  simp only [hk]
  exact le_rfl

/-- The scaled distance bound `k/s · D ≤ k c` from `D ≤ c s`. -/
private lemma CoercivityCutoff_div_mul_le {s D c k : ℝ} (hs : 0 < s) (hk : 0 ≤ k)
    (hD : D ≤ c * s) : k / s * D ≤ k * c := by
  rw [div_mul_eq_mul_div, div_le_iff₀ hs]
  nlinarith

/-! ### The cutoff with explicit constants -/

/-- The cutoff with `c₁ = 5/8`, `ρ = 5/16`, `K₁ = 141/8`, `L = 16/5`, `c = 25/(8π²)`,
`C = n + 2`, for every orthonormal layout and `W ≥ W₀`, where `W₀ ≥ 32`. -/
private theorem CoercivityCutoff_explicit (n : ℕ) :
    ∃ W₀ : ℕ, 32 ≤ W₀ ∧ ∀ d : Matrix (Fin 128) (Fin n) ℝ, d * dᵀ = 1 → ∀ W, W₀ ≤ W →
      ∃ χ : Ω W n → ℝ, IsCoercivityCutoff W n d (5 / 8) (5 / 16) (141 / 8) (16 / 5)
        (25 / (8 * π ^ 2)) (n + 2) χ := by
  obtain ⟨Wt, hWt⟩ := coerMin_lt_prob_le
  refine ⟨max Wt 32, le_max_right _ _, fun d hd W hW => ?_⟩
  have hW32 : 32 ≤ W := (le_max_right _ _).trans hW
  have hWt' : Wt ≤ W := (le_max_left _ _).trans hW
  have hWpos : (0 : ℝ) < W := by
    have : (32 : ℝ) ≤ W := by exact_mod_cast hW32
    linarith
  set s := Real.sqrt W with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 hWpos
  set E := EuclideanSpace ℝ (Fin n × Fin W × Fin W)
  set e : Ω W n ≃L[ℝ] E := (EuclideanSpace.equiv (Fin n × Fin W × Fin W) ℝ).symm with he
  have heω : ∀ ω : Ω W n, (e ω).ofLp = ω := fun ω => rfl
  set S : Ω W n → ℝ := fun ω => coerMin (layoutBlocks d (gueBlock W n ω)) with hS_def
  set N : Ω W n → ℝ := fun ω => CoercivityCutoff_N ω with hN_def
  set f : E → ℝ := fun x => CoercivityCutoff_F d x.ofLp with hf_def
  -- distances in `E`
  have hSd : ∀ x y : E, S x.ofLp ≤ S y.ofLp + 2 / s * dist x y := by
    intro x y
    rw [CoercivityCutoff_dist_eq]
    exact CoercivityCutoff_S_le hd _ _
  have hNd : ∀ x y : E, N x.ofLp ≤ N y.ofLp + 1 / s * dist x y := by
    intro x y
    rw [CoercivityCutoff_dist_eq]
    exact CoercivityCutoff_N_le _ _
  have hK0 : 0 ≤ 16 / (5 * s) := by positivity
  have hf : LipschitzWith (Real.toNNReal (16 / (5 * s))) f := by
    refine LipschitzWith.of_le_add_mul _ fun x y => ?_
    rw [Real.coe_toNNReal _ hK0, CoercivityCutoff_dist_eq]
    exact CoercivityCutoff_F_le hd _ _
  have hr : (0 : ℝ) < 5 / 32 * s := by positivity
  obtain ⟨g, hg, hgL, hg1, hg2⟩ := exists_contDiff_lipschitz_near hf hr
  -- continuity of `S` and `N`
  have hSc : Continuous S := by
    have hL : LipschitzWith (Real.toNNReal (2 / s)) (fun x : E => S x.ofLp) := by
      refine LipschitzWith.of_le_add_mul _ fun x y => ?_
      rw [Real.coe_toNNReal _ (by positivity)]
      exact hSd x y
    exact hL.continuous.comp e.continuous
  have hNc : Continuous N := by
    have hL : LipschitzWith (Real.toNNReal (1 / s)) (fun x : E => N x.ofLp) := by
      refine LipschitzWith.of_le_add_mul _ fun x y => ?_
      rw [Real.coe_toNNReal _ (by positivity)]
      exact hNd x y
    exact hL.continuous.comp e.continuous
  -- values of `g`
  have hg01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1 := by
    intro x
    obtain ⟨y, -, hy⟩ := hg1 x
    obtain ⟨y', -, hy'⟩ := hg2 x
    exact ⟨(CoercivityCutoff_F_nonneg d _).trans hy', hy.trans (CoercivityCutoff_F_le_one d _)⟩
  have hone : ∀ ω : Ω W n, 5 / 2 ≤ S ω → N ω ≤ 16 → g (e ω) = 1 := by
    intro ω hSω hNω
    obtain ⟨y, hy, hgy⟩ := hg2 (e ω)
    have h1 := hSd (e ω) y
    have h2 := hNd y (e ω)
    rw [dist_comm] at h1
    have h3 := CoercivityCutoff_div_mul_le hs (by norm_num : (0 : ℝ) ≤ 2) hy
    have h4 := CoercivityCutoff_div_mul_le hs (by norm_num : (0 : ℝ) ≤ 1) hy
    rw [heω] at h1 h2
    have hF : CoercivityCutoff_F d y.ofLp = 1 := by
      simp only [CoercivityCutoff_F]
      rw [CoercivityCutoff_clamp_eq_one, CoercivityCutoff_clamp_eq_one, min_self]
      · change 1 ≤ 549 / 32 - N y.ofLp
        linarith
      · change 1 ≤ 8 / 5 * (S y.ofLp - 25 / 16)
        linarith
    exact le_antisymm (hg01 _).2 (hF ▸ hgy)
  have hsupp : ∀ ω : Ω W n, g (e ω) ≠ 0 → 5 / 4 ≤ S ω ∧ N ω ≤ 277 / 16 := by
    intro ω hω
    have hpos : 0 < g (e ω) := lt_of_le_of_ne (hg01 _).1 (Ne.symm hω)
    obtain ⟨y, hy, hgy⟩ := hg1 (e ω)
    have hFy : 0 < CoercivityCutoff_F d y.ofLp := hpos.trans_le hgy
    have ha := CoercivityCutoff_pos_of_clamp_pos (hFy.trans_le (min_le_left _ _))
    have hb := CoercivityCutoff_pos_of_clamp_pos (hFy.trans_le (min_le_right _ _))
    have h1 := hSd y (e ω)
    have h2 := hNd (e ω) y
    rw [dist_comm] at h2
    have h3 := CoercivityCutoff_div_mul_le hs (by norm_num : (0 : ℝ) ≤ 2) hy
    have h4 := CoercivityCutoff_div_mul_le hs (by norm_num : (0 : ℝ) ≤ 1) hy
    rw [heω] at h1 h2
    change 0 < 8 / 5 * (S y.ofLp - 25 / 16) at ha
    change 0 < 549 / 32 - N y.ofLp at hb
    constructor <;> linarith
  -- the closed set containing the support
  set A : Set (Ω W n) := {ω | 5 / 4 ≤ S ω} ∩ {ω | N ω ≤ 277 / 16} with hA
  have hAc : IsClosed A :=
    (isClosed_le continuous_const hSc).inter (isClosed_le hNc continuous_const)
  set χ : Ω W n → ℝ := fun ω => g (e ω) with hχ
  have htsupp : tsupport χ ⊆ A := by
    refine closure_minimal (fun ω hω => ?_) hAc
    exact hsupp ω hω
  refine ⟨χ, ?_, ?_, fun ω => hg01 _, ?_, ?_, ?_⟩
  · -- smoothness
    exact hg.comp e.contDiff
  · -- compact support
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Ω W n)
      (Real.sqrt (2 * W) * (277 / 16))) (isClosed_tsupport _) fun ω hω => ?_
    have hωA := htsupp hω
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
    intro p
    rw [Real.norm_eq_abs]
    exact (CoercivityCutoff_abs_le ω p).trans
      (mul_le_mul_of_nonneg_left hωA.2 (Real.sqrt_nonneg _))
  · -- probability
    have hsub : {ω | χ ω ≠ 1} ⊆
        {ω | S ω < 5 / 2} ∪ ⋃ i, {ω | 16 < ‖gueBlock W n ω i‖} := by
      intro ω hω
      by_contra hcon
      simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, not_or, not_lt,
        not_exists] at hcon
      have hN : N ω ≤ 16 := Real.iSup_le (fun i => hcon.2 i) (by norm_num)
      exact hω (hone ω hcon.1 hN)
    have hT := measurePreserving_layout (W := W) hd
    have hpre : {ω | S ω < 5 / 2} = (fun ω => gueCoord W 128 (layoutBlocks d (gueBlock W n ω))) ⁻¹'
        {ω' | coerMin (gueBlock W 128 ω') < 5 / 2} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, gueBlock_gueCoord_layoutBlocks, S]
    have h1 : μ W n {ω | S ω < 5 / 2} ≤
        ENNReal.ofReal (2 * Real.exp (-(25 * W) / (8 * π ^ 2))) := by
      rw [hpre]
      refine (Measure.le_map_apply hT.measurable.aemeasurable _).trans ?_
      rw [hT.map_eq]
      exact hWt W hWt'
    set c : ℝ := 25 / (8 * π ^ 2) with hc
    have hc2 : c ≤ 1 / 2 := by
      rw [hc, div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_gt_three]
    have he1 : -(25 * (W : ℝ)) / (8 * π ^ 2) = -c * W := by
      rw [hc]
      ring
    have he2 : Real.exp (-(W : ℝ) / 2) ≤ Real.exp (-c * W) := by
      rw [Real.exp_le_exp]
      nlinarith
    rw [he1] at h1
    calc μ W n {ω | χ ω ≠ 1}
        ≤ μ W n ({ω | S ω < 5 / 2} ∪ ⋃ i, {ω | 16 < ‖gueBlock W n ω i‖}) := measure_mono hsub
      _ ≤ μ W n {ω | S ω < 5 / 2} + μ W n (⋃ i, {ω | 16 < ‖gueBlock W n ω i‖}) :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (2 * Real.exp (-c * W)) + ∑ _i : Fin n,
            ENNReal.ofReal (Real.exp (-c * W)) := by
          refine add_le_add h1 ((measure_iUnion_fintype_le _ _).trans ?_)
          exact Finset.sum_le_sum fun i _ =>
            (gueBlock_norm_tail hW32 i).trans (ENNReal.ofReal_le_ofReal he2)
      _ = ENNReal.ofReal ((n + 2) * Real.exp (-c * W)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
  · -- gradient
    intro ω
    have hD : fderiv ℝ χ ω = (fderiv ℝ g (e ω)).comp (e : Ω W n →L[ℝ] E) :=
      e.comp_right_fderiv
    have hnorm : ‖fderiv ℝ g (e ω)‖ ≤ 16 / (5 * s) := by
      have := norm_fderiv_le_of_lipschitz ℝ (x₀ := e ω) hgL
      rwa [Real.coe_toNNReal _ hK0] at this
    have hsq : ‖fderiv ℝ g (e ω)‖ ^ 2 ≤ (16 / (5 * s)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hval : (16 / (5 * s)) ^ 2 = (16 / 5) ^ 2 / W := by
      rw [div_pow, mul_pow, hs_def, Real.sq_sqrt hWpos.le]
      ring
    have hk : ∀ k, fderiv ℝ χ ω (Pi.single k 1) =
        fderiv ℝ g (e ω) (EuclideanSpace.single k 1) := by
      intro k
      rw [hD]
      rfl
    simp only [hk]
    exact (CoercivityCutoff_sum_sq_le _).trans (hsq.trans hval.le)
  · -- margin
    intro ω hω ω' hω'
    have hωA := htsupp hω
    have hD : Real.sqrt (∑ p, (ω' p - ω p) ^ 2) ≤ 5 / 16 * s := by
      calc Real.sqrt (∑ p, (ω' p - ω p) ^ 2) ≤ Real.sqrt (W * (5 / 16) ^ 2) :=
            Real.sqrt_le_sqrt hω'
        _ = 5 / 16 * s := by
          rw [Real.sqrt_mul hWpos.le, Real.sqrt_sq (by norm_num), hs_def]
          ring
    have hD' : Real.sqrt (∑ p, (ω p - ω' p) ^ 2) ≤ 5 / 16 * s := by
      refine le_of_eq_of_le ?_ hD
      congr 1
      exact Finset.sum_congr rfl fun p _ => by ring
    have h1 := CoercivityCutoff_S_le hd ω ω'
    have h2 := CoercivityCutoff_N_le ω' ω
    have h3 := CoercivityCutoff_div_mul_le hs (by norm_num : (0 : ℝ) ≤ 2) hD'
    have h4 := CoercivityCutoff_div_mul_le hs (by norm_num : (0 : ℝ) ≤ 1) hD
    have hA1 : 5 / 4 ≤ S ω := hωA.1
    have hA2 : N ω ≤ 277 / 16 := hωA.2
    change 5 / 4 ≤ coerMin (layoutBlocks d (gueBlock W n ω)) at hA1
    change CoercivityCutoff_N ω ≤ 277 / 16 at hA2
    refine ⟨by linarith, fun i => ?_⟩
    have := CoercivityCutoff_le_N ω' i
    linarith

end CoercivityCutoffAux

/-- The cutoff of (G.12) [cg:eq:cutoff], (10.5) [eq:c-main-cutoff] and (10.14)
[eq:c-main-coercivity]: absolute margins `c₁, ρ, K₁` and gradient bound `L`; for every number
`n` of inputs, rates `c, C` and a width `W₀`; then for every orthonormal layout `d` and
`W ≥ W₀` a cutoff. -/
theorem coercivity_cutoff :
    ∃ c₁ ρ K₁ L : ℝ, 0 < c₁ ∧ 0 < ρ ∧ 0 < K₁ ∧ 0 < L ∧
      ∀ n : ℕ, ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ W₀ : ℕ,
        ∀ d : Matrix (Fin 128) (Fin n) ℝ, d * dᵀ = 1 → ∀ W, W₀ ≤ W →
          ∃ χ : Ω W n → ℝ, IsCoercivityCutoff W n d c₁ ρ K₁ L c C χ := by
  refine ⟨5 / 8, 5 / 16, 141 / 8, 16 / 5, by norm_num, by norm_num, by norm_num, by norm_num,
    fun n => ?_⟩
  obtain ⟨W₀, -, h⟩ := CoercivityCutoff_explicit n
  exact ⟨25 / (8 * π ^ 2), n + 2, by positivity, by positivity, W₀, h⟩

end LSBA
