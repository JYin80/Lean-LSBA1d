import LSBA.Gauss.Concentration
import LSBA.Gauss.GUELaw
import LSBA.Spectral.ResolventBounds

/-!
# Gaussian tools for the rough density law

Block traces, the normalized trace, entrywise expectations, and the Gaussian inputs of Appendix
D.2 [sec:rough-density-proof] for `H = A + √s V` with any deterministic Hermitian `A`: complex
integration by parts in block form, the mean identity (D.3) [rd:eq:mean] for every constant `m`,
the Lipschitz constants of the block and normalized traces of the resolvent in the Gaussian
coordinates, the variance bound (D.2) [rd:eq:poincare] with `C = π²/8`, and the concentration
bound (D.6) [eq:rough-density] with exponent `W² L η⁴ u² / (π² s)`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

noncomputable section

open scoped Classical

namespace LSBA

/-- `⟨X⟩_{ab} = W⁻¹ Tr X_{ab}`. -/
def blockTr {W L : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) : ℂ :=
  (W : ℂ)⁻¹ * ∑ α, X (a, α) (b, α)

/-- `N⁻¹ Tr X`, `N = WL`. -/
def trN {W L : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) : ℂ :=
  ((W * L : ℕ) : ℂ)⁻¹ * X.trace

/-- Entrywise expectation of a matrix-valued function. -/
def matInt {n Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') (F : Ω' → Matrix n n ℂ) :
    Matrix n n ℂ := Matrix.of fun p q => ∫ ω, F ω p q ∂P

/-- `diag(d_a I_W)`. -/
def blockScalar {W L : ℕ} (d : Fin L → ℂ) : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  Matrix.diagonal fun p => d p.1

/-! ### The resolvent as a function of the Gaussian coordinates -/

/-- `blockV` is linear along lines in the coordinates. -/
private lemma roughDensity_blockV_add_smul (W L : ℕ) (ω v : Ω W L) (t : ℝ) :
    blockV W L (ω + t • v) = blockV W L ω + (t : ℂ) • blockV W L v := by
  ext ⟨a, α⟩ ⟨b, β⟩
  simp only [blockV, blockDiagOp, gueBlock, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

/-- `√s V(v)` is Hermitian. -/
private lemma roughDensity_isHermitian_dir (W L : ℕ) (s : ℝ) (v : Ω W L) :
    (((Real.sqrt s : ℝ) : ℂ) • blockV W L v).IsHermitian := by
  have hV := blockV_isHermitian W L v
  unfold Matrix.IsHermitian at hV ⊢
  rw [Matrix.conjTranspose_smul, hV, Complex.star_def, Complex.conj_ofReal]

private lemma roughDensity_blockFlow_line (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (s : ℝ) (ω v : Ω W L) (t : ℝ) :
    blockFlow W L A s (ω + t • v) =
      blockFlow W L A s ω + (t : ℂ) • (((Real.sqrt s : ℝ) : ℂ) • blockV W L v) := by
  rw [blockFlow, blockFlow, roughDensity_blockV_add_smul, smul_add, smul_comm, add_assoc]

section Smooth

open scoped Matrix.Norms.L2Operator

variable {W L : ℕ} {A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}

/-- Derivative of the resolvent along a line `t ↦ ω + t v` in the coordinates. -/
private lemma roughDensity_hasDerivAt_line (hA : A.IsHermitian) (s : ℝ) {z : ℂ} (hz : 0 < z.im)
    (ω v : Ω W L) :
    HasDerivAt (fun t : ℝ => resolventMat (blockFlow W L A s (ω + t • v)) z)
      (-(resolventMat (blockFlow W L A s ω) z * (((Real.sqrt s : ℝ) : ℂ) • blockV W L v) *
        resolventMat (blockFlow W L A s ω) z)) 0 := by
  have h := hasDerivAt_resolventMat_line (blockFlow_isHermitian W L hA s ω)
    (roughDensity_isHermitian_dir W L s v) hz.ne' 0
  simp only [Complex.ofReal_zero, zero_smul, add_zero] at h
  convert h using 2 with t
  rw [roughDensity_blockFlow_line]

/-- The coordinate map `ω ↦ A + √s V(ω) - z` is smooth. -/
private lemma roughDensity_contDiff_shift (s : ℝ) (z : ℂ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun ω : Ω W L => blockFlow W L A s ω - z • (1 : Matrix _ _ ℂ)) := by
  have h : (fun ω : Ω W L => blockFlow W L A s ω - z • (1 : Matrix _ _ ℂ)) = fun ω =>
      (A - z • (1 : Matrix _ _ ℂ)) + ((Real.sqrt s : ℝ) : ℂ) • (((Real.sqrt W : ℝ) : ℂ)⁻¹ •
        ∑ c : Fin L, ∑ k : Fin W × Fin W, (ω (c, k.1, k.2) : ℂ) • blockBasis W L c k) := by
    funext ω
    rw [blockFlow, blockV_eq_sum_blockBasis]
    abel
  rw [h]
  refine contDiff_const.add (ContDiff.const_smul _ (ContDiff.const_smul _ ?_))
  refine ContDiff.sum fun c _ => ContDiff.sum fun k _ => ?_
  exact (Complex.ofRealCLM.contDiff.comp (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin L × Fin W × Fin W => ℝ) (c, k.1, k.2)).contDiff).smul contDiff_const

/-- The resolvent is a smooth function of the coordinates. -/
private lemma roughDensity_contDiff_resolvent (hA : A.IsHermitian) (s : ℝ) {z : ℂ}
    (hz : 0 < z.im) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun ω : Ω W L => resolventMat (blockFlow W L A s ω) z) := by
  have h : (fun ω : Ω W L => resolventMat (blockFlow W L A s ω) z) =
      Ring.inverse ∘ (fun ω : Ω W L => blockFlow W L A s ω - z • (1 : Matrix _ _ ℂ)) := by
    funext ω
    exact Matrix.nonsing_inv_eq_ringInverse _
  rw [h, contDiff_iff_contDiffAt]
  intro ω
  have hu := isUnit_sub_smul_one (blockFlow_isHermitian W L hA s ω) hz.ne'
  have h1 := contDiffAt_ringInverse ℝ (n := n) hu.unit
  rw [hu.unit_spec] at h1
  exact h1.comp ω (roughDensity_contDiff_shift s z).contDiffAt

/-- A linear functional of the resolvent is a smooth function of the coordinates. -/
private lemma roughDensity_contDiff_lin (hA : A.IsHermitian) (s : ℝ) {z : ℂ} (hz : 0 < z.im)
    (φ : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ →ₗ[ℝ] ℂ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun ω : Ω W L => φ (resolventMat (blockFlow W L A s ω) z)) :=
  (LinearMap.toContinuousLinearMap φ).contDiff.comp (roughDensity_contDiff_resolvent hA s hz)

/-- Directional derivative of a linear functional of the resolvent:
`D_v φ(G) = -φ(G (√s V(v)) G)`. -/
private lemma roughDensity_fderiv_lin (hA : A.IsHermitian) (s : ℝ) {z : ℂ} (hz : 0 < z.im)
    (φ : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ →ₗ[ℝ] ℂ) (ω v : Ω W L) :
    fderiv ℝ (fun ω : Ω W L => φ (resolventMat (blockFlow W L A s ω) z)) ω v =
      φ (-(resolventMat (blockFlow W L A s ω) z * (((Real.sqrt s : ℝ) : ℂ) • blockV W L v) *
        resolventMat (blockFlow W L A s ω) z)) := by
  set f := fun ω : Ω W L => φ (resolventMat (blockFlow W L A s ω) z) with hf
  have hd : DifferentiableAt ℝ f ω :=
    ((roughDensity_contDiff_lin hA s hz φ (n := 1)).differentiable one_ne_zero) ω
  have hline : HasDerivAt (fun t : ℝ => ω + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add ω
  have h1 := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have h2 := (LinearMap.toContinuousLinearMap φ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (roughDensity_hasDerivAt_line hA s hz ω v)
  exact h1.unique h2

/-- An entry is bounded by the operator norm. -/
private lemma roughDensity_norm_entry_le {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (i j : n) : ‖M i j‖ ≤ ‖M‖ := by
  have h := Matrix.l2_opNorm_mulVec M (EuclideanSpace.single j (1 : ℂ))
  have hn : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  rw [hn, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le ((EuclideanSpace.equiv n ℂ).symm
    (M.mulVec (EuclideanSpace.single j (1 : ℂ)).ofLp)) i
  convert this using 2
  simp

/-- `|G_{pq}| ≤ η⁻¹`. -/
private lemma roughDensity_norm_resolvent_entry_le (hA : A.IsHermitian) (s : ℝ) {z : ℂ}
    (hz : 0 < z.im) (ω : Ω W L) (p q : Fin L × Fin W) :
    ‖resolventMat (blockFlow W L A s ω) z p q‖ ≤ z.im⁻¹ :=
  (roughDensity_norm_entry_le _ p q).trans
    (norm_resolventMat_le (blockFlow_isHermitian W L hA s ω) hz (abs_of_pos hz).ge)

end Smooth

/-! ### Hilbert–Schmidt increments and Lipschitz constants -/

/-- The squared Euclidean distance of two samples. -/
private lemma roughDensity_dist_toLp_sq {W L : ℕ} (ω ω' : Ω W L) :
    dist (WithLp.toLp 2 ω) (WithLp.toLp 2 ω') ^ 2 = ∑ k, (ω k - ω' k) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [Real.dist_eq, sq_abs]

/-- `|ω - ω'|₂ ≤ √|ι| |ω - ω'|_∞`. -/
private lemma roughDensity_dist_toLp_le {W L : ℕ} (ω ω' : Ω W L) :
    dist (WithLp.toLp 2 ω) (WithLp.toLp 2 ω') ≤
      Real.sqrt (Fintype.card (Fin L × Fin W × Fin W)) * dist ω ω' := by
  rw [EuclideanSpace.dist_eq]
  have h : ∑ i, dist ((WithLp.toLp 2 ω).ofLp i) ((WithLp.toLp 2 ω').ofLp i) ^ 2 ≤
      ∑ _i : Fin L × Fin W × Fin W, dist ω ω' ^ 2 :=
    Finset.sum_le_sum fun i _ => pow_le_pow_left₀ dist_nonneg (dist_le_pi_dist ω ω' i) 2
  refine (Real.sqrt_le_sqrt h).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.sqrt_mul (Nat.cast_nonneg _),
    Real.sqrt_sq dist_nonneg]

/-- A function with Euclidean Lipschitz constant `K` has `‖Df‖ ≤ K √|ι|` in the sup norm. -/
private lemma roughDensity_norm_fderiv_le {W L : ℕ} {f : Ω W L → ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hf : ∀ ω ω', ‖f ω - f ω'‖ ≤ K * dist (WithLp.toLp 2 ω) (WithLp.toLp 2 ω')) (ω : Ω W L) :
    ‖fderiv ℝ f ω‖ ≤ K * Real.sqrt (Fintype.card (Fin L × Fin W × Fin W)) := by
  have hC : 0 ≤ K * Real.sqrt (Fintype.card (Fin L × Fin W × Fin W)) :=
    mul_nonneg hK (Real.sqrt_nonneg _)
  have hL : LipschitzWith ⟨K * Real.sqrt (Fintype.card (Fin L × Fin W × Fin W)), hC⟩ f := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm]
    change ‖f x - f y‖ ≤ K * Real.sqrt (Fintype.card (Fin L × Fin W × Fin W)) * dist x y
    rw [mul_assoc]
    exact (hf x y).trans (mul_le_mul_of_nonneg_left (roughDensity_dist_toLp_le x y) hK)
  exact norm_fderiv_le_of_lipschitz ℝ hL

/-- From a squared bound to a Lipschitz bound in the Euclidean distance. -/
private lemma roughDensity_le_of_sq_le {W L : ℕ} {x K : ℝ} (hx : 0 ≤ x) (hK : 0 ≤ K)
    (ω ω' : Ω W L) (h : x ^ 2 ≤ K ^ 2 * ∑ k, (ω k - ω' k) ^ 2) :
    x ≤ K * dist (WithLp.toLp 2 ω) (WithLp.toLp 2 ω') := by
  rw [← pow_le_pow_iff_left₀ hx (mul_nonneg hK dist_nonneg) two_ne_zero, mul_pow,
    roughDensity_dist_toLp_sq]
  exact h

/-- Cauchy–Schwarz for a finite sum of complex numbers. -/
private lemma roughDensity_norm_sum_sq_le {β : Type*} (S : Finset β) (y : β → ℂ) :
    ‖∑ i ∈ S, y i‖ ^ 2 ≤ S.card * ∑ i ∈ S, ‖y i‖ ^ 2 :=
  (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans sq_sum_le_card_mul_sum_sq

/-- `‖G(ω) - G(ω')‖²_HS ≤ s W⁻¹ η⁻⁴ |ω - ω'|₂²`. -/
private lemma roughDensity_sum_sq_sub_le {W L : ℕ} {A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hA : A.IsHermitian) {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : 0 < z.im) (ω ω' : Ω W L) :
    ∑ i, ∑ j, ‖(resolventMat (blockFlow W L A s ω) z -
        resolventMat (blockFlow W L A s ω') z) i j‖ ^ 2 ≤
      s / (W * z.im ^ 4) * ∑ k, (ω k - ω' k) ^ 2 := by
  rw [resolventMat_sub_resolventMat (blockFlow_isHermitian W L hA s ω)
    (blockFlow_isHermitian W L hA s ω') hz.ne']
  have hdiff : blockFlow W L A s ω' - blockFlow W L A s ω =
      ((Real.sqrt s : ℝ) : ℂ) • blockV W L (ω' - ω) := by
    rw [blockFlow, blockFlow, blockV_sub, smul_sub]
    abel
  rw [hdiff]
  refine (sum_norm_sq_resolventMat_mul_mul_le (blockFlow_isHermitian W L hA s ω)
    (blockFlow_isHermitian W L hA s ω') hz (abs_of_pos hz).ge _).trans (le_of_eq ?_)
  have h1 : ∑ i, ∑ j, ‖(((Real.sqrt s : ℝ) : ℂ) • blockV W L (ω' - ω)) i j‖ ^ 2 =
      s * ((W : ℝ)⁻¹ * ∑ k, (ω' - ω) k ^ 2) := by
    rw [← sum_norm_sq_blockV, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, Real.sq_sqrt hs]
  have h2 : ∑ k, (ω' - ω) k ^ 2 = ∑ k, (ω k - ω' k) ^ 2 :=
    Finset.sum_congr rfl fun k _ => by rw [Pi.sub_apply]; ring
  rw [h1, h2]
  ring

/-- `⟨X⟩_{aa} - ⟨Y⟩_{aa} = ⟨X - Y⟩_{aa}`. -/
private lemma roughDensity_blockTr_sub {W L : ℕ} (X Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a : Fin L) : blockTr X a a - blockTr Y a a = blockTr (X - Y) a a := by
  simp only [blockTr, Matrix.sub_apply, Finset.sum_sub_distrib, mul_sub]

private lemma roughDensity_trN_sub {W L : ℕ} (X Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    trN X - trN Y = trN (X - Y) := by
  simp only [trN, Matrix.trace_sub, mul_sub]

/-- The diagonal of block `a` is part of the Hilbert–Schmidt sum. -/
private lemma roughDensity_sum_blockDiag_le {W L : ℕ}
    (Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a : Fin L) :
    ∑ α, ‖Y (a, α) (a, α)‖ ^ 2 ≤ ∑ i, ∑ j, ‖Y i j‖ ^ 2 := by
  calc ∑ α, ‖Y (a, α) (a, α)‖ ^ 2 ≤ ∑ α, ∑ j, ‖Y (a, α) j‖ ^ 2 :=
        Finset.sum_le_sum fun α _ => Finset.single_le_sum (f := fun j => ‖Y (a, α) j‖ ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ _)
    _ ≤ ∑ b, ∑ α, ∑ j, ‖Y (b, α) j‖ ^ 2 :=
        Finset.single_le_sum (f := fun b => ∑ α, ∑ j, ‖Y (b, α) j‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
          (Finset.mem_univ a)
    _ = ∑ i, ∑ j, ‖Y i j‖ ^ 2 := by
        rw [Fintype.sum_prod_type (f := fun i => ∑ j, ‖Y i j‖ ^ 2)]

/-- The diagonal is part of the Hilbert–Schmidt sum. -/
private lemma roughDensity_sum_diag_le {n : Type*} [Fintype n] (Y : Matrix n n ℂ) :
    ∑ i, ‖Y i i‖ ^ 2 ≤ ∑ i, ∑ j, ‖Y i j‖ ^ 2 :=
  Finset.sum_le_sum fun i _ => Finset.single_le_sum (f := fun j => ‖Y i j‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

/-- `N⁻² N = N⁻¹`, also at `N = 0`. -/
private lemma roughDensity_inv_sq_mul (x : ℝ) : x⁻¹ ^ 2 * x = x⁻¹ := by
  rcases eq_or_ne x 0 with h | h
  · simp [h]
  · field_simp

/-! ### Block integration by parts -/

/-- Block products of the basis: `B_{c,k} X B_{c,l}` lives in block `c`. -/
private lemma roughDensity_blockBasis_mul_mul {W L : ℕ} (c : Fin L) (k l : Fin W × Fin W)
    (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    blockBasis W L c k * X * blockBasis W L c l = Matrix.of fun P Q =>
      if P.1 = c ∧ Q.1 = c then
        (hermBasis W k * Matrix.of (fun i j => X (c, i) (c, j)) * hermBasis W l) P.2 Q.2
      else 0 := by
  ext ⟨b, β⟩ ⟨d, δ⟩
  simp only [Matrix.mul_apply, blockBasis, Matrix.of_apply, Fintype.sum_prod_type]
  by_cases hb : b = c <;> by_cases hd : d = c
  · subst hb; subst hd
    simp [Finset.sum_mul, ite_mul]
  · simp [hd]
  · simp [hb]
  · simp [hb]

/-- Completeness in block form: `Σ_{c,k} B_{c,k} X B_{c,k} = diag((Tr X_{cc}) I_W)`. -/
private lemma roughDensity_sum_blockBasis_mul_mul {W L : ℕ}
    (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    ∑ c : Fin L, ∑ k : Fin W × Fin W, blockBasis W L c k * X * blockBasis W L c k =
      blockScalar (fun b => ∑ β, X (b, β) (b, β)) := by
  simp_rw [roughDensity_blockBasis_mul_mul]
  ext P Q
  have h : ∀ c : Fin L, ∑ k : Fin W × Fin W,
      (hermBasis W k * Matrix.of (fun i j => X (c, i) (c, j)) * hermBasis W k) P.2 Q.2 =
      (Matrix.of (fun i j => X (c, i) (c, j))).trace * (1 : Matrix (Fin W) (Fin W) ℂ) P.2 Q.2 := by
    intro c
    rw [← Matrix.sum_apply, sum_hermBasis_mul_mul]
    simp
  simp only [Matrix.sum_apply, Matrix.of_apply]
  have h2 : ∀ c : Fin L, ∑ k : Fin W × Fin W, (if P.1 = c ∧ Q.1 = c then
      (hermBasis W k * Matrix.of (fun i j => X (c, i) (c, j)) * hermBasis W k) P.2 Q.2 else 0) =
      if P.1 = c ∧ Q.1 = c then
        (Matrix.of (fun i j => X (c, i) (c, j))).trace * (1 : Matrix (Fin W) (Fin W) ℂ) P.2 Q.2
      else 0 := by
    intro c
    split_ifs
    · exact h c
    · simp
  simp only [h2]
  rw [Finset.sum_eq_single P.1 (fun c _ hc => by simp [Ne.symm hc]) (by simp)]
  simp only [blockScalar, Matrix.diagonal_apply, Matrix.one_apply, Matrix.trace, Matrix.diag,
    Matrix.of_apply, Prod.ext_iff]
  by_cases h1 : P.1 = Q.1 <;> by_cases h3 : P.2 = Q.2 <;> simp [h1, h3, eq_comm (a := Q.1)]

/-- `V(e_{c,k}) = W^{-1/2} B_{c,k}`. -/
private lemma roughDensity_blockV_single {W L : ℕ} (c : Fin L) (k : Fin W × Fin W) :
    blockV W L (Pi.single (c, k.1, k.2) 1) = ((Real.sqrt W : ℝ) : ℂ)⁻¹ • blockBasis W L c k := by
  rw [blockV_eq_sum_blockBasis]
  congr 1
  rw [Finset.sum_eq_single c, Finset.sum_eq_single k]
  · simp
  · intro k' _ hk'
    rw [Pi.single_eq_of_ne (fun h => hk' (Prod.ext (congrArg (fun x => x.2.1) h)
      (congrArg (fun x => x.2.2) h))), Complex.ofReal_zero, zero_smul]
  · simp
  · intro c' _ hc'
    refine Finset.sum_eq_zero fun k' _ => ?_
    rw [Pi.single_eq_of_ne (fun h => hc' (congrArg Prod.fst h)), Complex.ofReal_zero,
      zero_smul]
  · simp

section Entries

variable {W L : ℕ} {A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}

private lemma roughDensity_contDiff_entry (hA : A.IsHermitian) (s : ℝ) {z : ℂ} (hz : 0 < z.im)
    (r q : Fin L × Fin W) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun ω : Ω W L => resolventMat (blockFlow W L A s ω) z r q) := by
  simpa using roughDensity_contDiff_lin hA s hz (Matrix.entryLinearMap ℝ ℂ r q) (n := n)

private lemma roughDensity_fderiv_entry (hA : A.IsHermitian) (s : ℝ) {z : ℂ} (hz : 0 < z.im)
    (r q : Fin L × Fin W) (ω v : Ω W L) :
    fderiv ℝ (fun ω : Ω W L => resolventMat (blockFlow W L A s ω) z r q) ω v =
      (-(resolventMat (blockFlow W L A s ω) z * (((Real.sqrt s : ℝ) : ℂ) • blockV W L v) *
        resolventMat (blockFlow W L A s ω) z)) r q := by
  simpa using roughDensity_fderiv_lin hA s hz (Matrix.entryLinearMap ℝ ℂ r q) ω v

/-- Entries of the resolvent have Euclidean Lipschitz constant `(s W⁻¹ η⁻⁴)^{1/2}`. -/
private lemma roughDensity_lipschitz_entry (hA : A.IsHermitian) {s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz : 0 < z.im) (r q : Fin L × Fin W) (ω ω' : Ω W L) :
    ‖resolventMat (blockFlow W L A s ω) z r q - resolventMat (blockFlow W L A s ω') z r q‖ ≤
      Real.sqrt (s / (W * z.im ^ 4)) * dist (WithLp.toLp 2 ω) (WithLp.toLp 2 ω') := by
  refine roughDensity_le_of_sq_le (norm_nonneg _) (Real.sqrt_nonneg _) ω ω' ?_
  rw [Real.sq_sqrt (by positivity)]
  refine le_trans ?_ (roughDensity_sum_sq_sub_le hA hs hz ω ω')
  set Y := resolventMat (blockFlow W L A s ω) z - resolventMat (blockFlow W L A s ω') z
  calc ‖Y r q‖ ^ 2 ≤ ∑ j, ‖Y r j‖ ^ 2 :=
        Finset.single_le_sum (f := fun j => ‖Y r j‖ ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ q)
    _ ≤ ∑ i, ∑ j, ‖Y i j‖ ^ 2 :=
        Finset.single_le_sum (f := fun i => ∑ j, ‖Y i j‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ r)

/-- A uniform bound on the derivative of an entry. -/
private lemma roughDensity_norm_fderiv_entry_le (hA : A.IsHermitian) {s : ℝ} (hs : 0 ≤ s)
    {z : ℂ} (hz : 0 < z.im) (r q : Fin L × Fin W) (ω : Ω W L) :
    ‖fderiv ℝ (fun ω : Ω W L => resolventMat (blockFlow W L A s ω) z r q) ω‖ ≤
      Real.sqrt (s / (W * z.im ^ 4)) * Real.sqrt (Fintype.card (Fin L × Fin W × Fin W)) :=
  roughDensity_norm_fderiv_le (Real.sqrt_nonneg _) (roughDensity_lipschitz_entry hA hs hz r q) ω

/-- The Gaussian coordinates are integrable. -/
private lemma roughDensity_integrable_coord (x : Fin L × Fin W × Fin W) :
    Integrable (fun ω : Ω W L => ω x) (μ W L) := by
  have h : MemLp id 1 (gaussianReal (0 : ℝ) 1) := memLp_id_gaussianReal' 1 ENNReal.one_ne_top
  exact (h.comp_measurePreserving (measurePreserving_eval (fun _ : Fin L × Fin W × Fin W =>
    gaussianReal (0 : ℝ) 1) x)).integrable le_rfl

private lemma roughDensity_integrable_coord_mul_entry (hA : A.IsHermitian) (s : ℝ) {z : ℂ}
    (hz : 0 < z.im) (x : Fin L × Fin W × Fin W) (r q : Fin L × Fin W) :
    Integrable (fun ω : Ω W L => (ω x : ℂ) * resolventMat (blockFlow W L A s ω) z r q)
      (μ W L) := by
  have h := (roughDensity_integrable_coord (W := W) (L := L) x).ofReal (𝕜 := ℂ) |>.bdd_mul
    (roughDensity_contDiff_entry hA s hz r q (n := 0)).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => roughDensity_norm_resolvent_entry_le hA s hz ω r q)
  simpa [mul_comm] using h

private lemma roughDensity_integrable_fderiv_entry (hA : A.IsHermitian) {s : ℝ} (hs : 0 ≤ s)
    {z : ℂ} (hz : 0 < z.im) (r q : Fin L × Fin W) (v : Ω W L) :
    Integrable (fun ω : Ω W L =>
      fderiv ℝ (fun ω : Ω W L => resolventMat (blockFlow W L A s ω) z r q) ω v) (μ W L) := by
  have hc : Continuous fun ω : Ω W L =>
      fderiv ℝ (fun ω : Ω W L => resolventMat (blockFlow W L A s ω) z r q) ω v :=
    ((roughDensity_contDiff_entry hA s hz r q (n := 1)).continuous_fderiv one_ne_zero).clm_apply
      continuous_const
  refine Integrable.of_bound hc.aestronglyMeasurable
    (Real.sqrt (s / (W * z.im ^ 4)) * Real.sqrt (Fintype.card (Fin L × Fin W × Fin W)) * ‖v‖)
    (Filter.Eventually.of_forall fun ω => ?_)
  exact (ContinuousLinearMap.le_opNorm _ v).trans
    (mul_le_mul_of_nonneg_right (roughDensity_norm_fderiv_entry_le hA hs hz r q ω)
      (norm_nonneg v))

/-- Gaussian integration by parts for an entry of the resolvent. -/
private lemma roughDensity_ibp_entry (hA : A.IsHermitian) {s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz : 0 < z.im) (x : Fin L × Fin W × Fin W) (r q : Fin L × Fin W) :
    ∫ ω, (ω x : ℂ) * resolventMat (blockFlow W L A s ω) z r q ∂(μ W L) =
      ∫ ω, fderiv ℝ (fun ω : Ω W L => resolventMat (blockFlow W L A s ω) z r q) ω
        (Pi.single x 1) ∂(μ W L) := by
  set C := max z.im⁻¹
    (Real.sqrt (s / (W * z.im ^ 4)) * Real.sqrt (Fintype.card (Fin L × Fin W × Fin W)))
  exact integral_coord_mul_stdGauss (fun ω : Ω W L => resolventMat (blockFlow W L A s ω) z r q)
    (roughDensity_contDiff_entry hA s hz r q) (C := C) (k := 0)
    (fun ω => by
      rw [pow_zero, mul_one]
      exact (roughDensity_norm_resolvent_entry_le hA s hz ω r q).trans (le_max_left _ _))
    (fun ω => by
      rw [pow_zero, mul_one]
      exact (roughDensity_norm_fderiv_entry_le hA hs hz r q ω).trans (le_max_right _ _)) x

private lemma roughDensity_integrable_entry (hA : A.IsHermitian) (s : ℝ) {z : ℂ}
    (hz : 0 < z.im) (r q : Fin L × Fin W) :
    Integrable (fun ω : Ω W L => resolventMat (blockFlow W L A s ω) z r q) (μ W L) :=
  Integrable.of_bound
    (roughDensity_contDiff_entry hA s hz r q (n := 0)).continuous.aestronglyMeasurable
    z.im⁻¹ (Filter.Eventually.of_forall fun ω => roughDensity_norm_resolvent_entry_le hA s hz ω r q)

private lemma roughDensity_continuous_blockTr (hA : A.IsHermitian) (s : ℝ) {z : ℂ}
    (hz : 0 < z.im) (a : Fin L) :
    Continuous (fun ω : Ω W L => blockTr (resolventMat (blockFlow W L A s ω) z) a a) :=
  continuous_const.mul (continuous_finsetSum _ fun α _ =>
    (roughDensity_contDiff_entry hA s hz (a, α) (a, α) (n := 0)).continuous)

private lemma roughDensity_norm_blockTr_le (hA : A.IsHermitian) (s : ℝ) {z : ℂ}
    (hz : 0 < z.im) (a : Fin L) (ω : Ω W L) :
    ‖blockTr (resolventMat (blockFlow W L A s ω) z) a a‖ ≤ (W : ℝ)⁻¹ * (W * z.im⁻¹) := by
  rw [blockTr, norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
  refine (Finset.sum_le_sum fun α _ =>
    roughDensity_norm_resolvent_entry_le hA s hz ω (a, α) (a, α)).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private lemma roughDensity_integrable_blockTr_mul_entry (hA : A.IsHermitian) (s : ℝ) {z : ℂ}
    (hz : 0 < z.im) (a : Fin L) (r q : Fin L × Fin W) :
    Integrable (fun ω : Ω W L => blockTr (resolventMat (blockFlow W L A s ω) z) a a *
      resolventMat (blockFlow W L A s ω) z r q) (μ W L) :=
  (roughDensity_integrable_entry hA s hz r q).bdd_mul
    (roughDensity_continuous_blockTr hA s hz a).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => roughDensity_norm_blockTr_le hA s hz a ω)

end Entries

/-- `(√s W^{-1/2})² = s W⁻¹`. -/
private lemma roughDensity_coeff_sq {W : ℕ} {s : ℝ} (hs : 0 ≤ s) :
    ((Real.sqrt s : ℝ) : ℂ) * ((Real.sqrt W : ℝ) : ℂ)⁻¹ *
        (((Real.sqrt s : ℝ) : ℂ) * ((Real.sqrt W : ℝ) : ℂ)⁻¹) = (s : ℂ) * (W : ℂ)⁻¹ := by
  have h1 : ((Real.sqrt s : ℝ) : ℂ) * ((Real.sqrt s : ℝ) : ℂ) = (s : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hs]
  have h2 : ((Real.sqrt W : ℝ) : ℂ)⁻¹ * ((Real.sqrt W : ℝ) : ℂ)⁻¹ = (W : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg W)]
    simp
  rw [← h1, ← h2]
  ring

/-- Block form of complex GUE integration by parts, Appendix D.2 [sec:rough-density-proof]:
`E(√s V G)_{pq} = -s E(⟨G⟩_{aa} G_{pq})`, `a = p.1`. -/
theorem integral_blockV_mul_resolvent (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hA : A.IsHermitian) {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : 0 < z.im) (p q : Fin L × Fin W) :
    ∫ ω, (((Real.sqrt s : ℝ) : ℂ) • blockV W L ω * resolventMat (blockFlow W L A s ω) z) p q
        ∂(μ W L) =
      -(s : ℂ) * ∫ ω, blockTr (resolventMat (blockFlow W L A s ω) z) p.1 p.1 *
        resolventMat (blockFlow W L A s ω) z p q ∂(μ W L) := by
  set G : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
    fun ω => resolventMat (blockFlow W L A s ω) z with hG
  set c0 : ℂ := ((Real.sqrt s : ℝ) : ℂ) * ((Real.sqrt W : ℝ) : ℂ)⁻¹ with hc0
  -- the integrand as a combination of `ω_{c,k} G_{rq}`
  have hpt : ∀ ω : Ω W L, (((Real.sqrt s : ℝ) : ℂ) • blockV W L ω * G ω) p q =
      ∑ c : Fin L, ∑ k : Fin W × Fin W, ∑ r,
        c0 * blockBasis W L c k p r * ((ω (c, k.1, k.2) : ℂ) * G ω r q) := by
    intro ω
    have hm : ((Real.sqrt s : ℝ) : ℂ) • blockV W L ω * G ω = ∑ c : Fin L, ∑ k : Fin W × Fin W,
        (c0 * (ω (c, k.1, k.2) : ℂ)) • (blockBasis W L c k * G ω) := by
      rw [blockV_eq_sum_blockBasis, smul_smul, Matrix.smul_mul, Matrix.sum_mul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Matrix.sum_mul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.smul_mul, smul_smul]
    rw [hm, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  -- the recombined derivative terms
  have hpt2 : ∀ ω : Ω W L, ∑ c : Fin L, ∑ k : Fin W × Fin W, ∑ r,
      c0 * blockBasis W L c k p r *
        fderiv ℝ (fun ω : Ω W L => G ω r q) ω (Pi.single (c, k.1, k.2) 1) =
      -(s : ℂ) * (blockTr (G ω) p.1 p.1 * G ω p q) := by
    intro ω
    have h1 : ∀ (c : Fin L) (k : Fin W × Fin W), ∑ r,
        c0 * blockBasis W L c k p r *
          fderiv ℝ (fun ω : Ω W L => G ω r q) ω (Pi.single (c, k.1, k.2) 1) =
        -(c0 * c0) * (blockBasis W L c k * G ω * blockBasis W L c k * G ω) p q := by
      intro c k
      simp only [hG, roughDensity_fderiv_entry hA s hz, roughDensity_blockV_single]
      have e : -(resolventMat (blockFlow W L A s ω) z *
          (((Real.sqrt s : ℝ) : ℂ) • ((Real.sqrt W : ℝ) : ℂ)⁻¹ • blockBasis W L c k) *
          resolventMat (blockFlow W L A s ω) z) =
          (-c0) • (resolventMat (blockFlow W L A s ω) z * blockBasis W L c k *
            resolventMat (blockFlow W L A s ω) z) := by
        rw [hc0, smul_smul, Matrix.mul_smul, Matrix.smul_mul, neg_smul]
      rw [e]
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [show blockBasis W L c k * resolventMat (blockFlow W L A s ω) z * blockBasis W L c k *
          resolventMat (blockFlow W L A s ω) z = blockBasis W L c k *
          (resolventMat (blockFlow W L A s ω) z * blockBasis W L c k *
            resolventMat (blockFlow W L A s ω) z) by simp only [Matrix.mul_assoc],
        Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    simp only [h1, ← Finset.mul_sum]
    have h2 : ∑ c : Fin L, ∑ k : Fin W × Fin W,
        (blockBasis W L c k * G ω * blockBasis W L c k * G ω) p q =
        ((∑ c : Fin L, ∑ k : Fin W × Fin W, blockBasis W L c k * G ω * blockBasis W L c k) *
          G ω) p q := by
      simp only [Matrix.sum_mul, Matrix.sum_apply]
    rw [h2, roughDensity_sum_blockBasis_mul_mul, blockScalar, Matrix.diagonal_mul,
      blockTr, roughDensity_coeff_sq hs]
    ring
  have hint1 : ∀ (c : Fin L) (k : Fin W × Fin W) (r : Fin L × Fin W), Integrable
      (fun ω : Ω W L => c0 * blockBasis W L c k p r * ((ω (c, k.1, k.2) : ℂ) * G ω r q))
      (μ W L) := fun c k r =>
    (roughDensity_integrable_coord_mul_entry hA s hz (c, k.1, k.2) r q).const_mul _
  have hint2 : ∀ (c : Fin L) (k : Fin W × Fin W) (r : Fin L × Fin W), Integrable
      (fun ω : Ω W L => c0 * blockBasis W L c k p r *
        fderiv ℝ (fun ω : Ω W L => G ω r q) ω (Pi.single (c, k.1, k.2) 1)) (μ W L) :=
    fun c k r => (roughDensity_integrable_fderiv_entry hA hs hz r q _).const_mul _
  calc ∫ ω, (((Real.sqrt s : ℝ) : ℂ) • blockV W L ω * G ω) p q ∂(μ W L)
      = ∫ ω, ∑ c : Fin L, ∑ k : Fin W × Fin W, ∑ r,
          c0 * blockBasis W L c k p r * ((ω (c, k.1, k.2) : ℂ) * G ω r q) ∂(μ W L) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∑ c : Fin L, ∑ k : Fin W × Fin W, ∑ r, c0 * blockBasis W L c k p r *
          ∫ ω, (ω (c, k.1, k.2) : ℂ) * G ω r q ∂(μ W L) := by
        rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun k _ =>
          integrable_finsetSum _ fun r _ => hint1 c k r]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun r _ => hint1 c k r]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_finsetSum _ fun r _ => hint1 c k r]
        refine Finset.sum_congr rfl fun r _ => ?_
        exact integral_const_mul _ _
    _ = ∑ c : Fin L, ∑ k : Fin W × Fin W, ∑ r, c0 * blockBasis W L c k p r *
          ∫ ω, fderiv ℝ (fun ω : Ω W L => G ω r q) ω (Pi.single (c, k.1, k.2) 1) ∂(μ W L) := by
        simp only [hG, roughDensity_ibp_entry hA hs hz]
    _ = ∫ ω, ∑ c : Fin L, ∑ k : Fin W × Fin W, ∑ r, c0 * blockBasis W L c k p r *
          fderiv ℝ (fun ω : Ω W L => G ω r q) ω (Pi.single (c, k.1, k.2) 1) ∂(μ W L) := by
        rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun k _ =>
          integrable_finsetSum _ fun r _ => hint2 c k r]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun r _ => hint2 c k r]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_finsetSum _ fun r _ => hint2 c k r]
        refine Finset.sum_congr rfl fun r _ => ?_
        exact (integral_const_mul _ _).symm
    _ = ∫ ω, -(s : ℂ) * (blockTr (G ω) p.1 p.1 * G ω p q) ∂(μ W L) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt2)
    _ = _ := integral_const_mul _ _

/-- (D.3) [rd:eq:mean], for every constant `m`. -/
theorem rough_mean_identity (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hA : A.IsHermitian) {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : 0 < z.im) (m : ℂ) :
    (A - (z + s * m) • (1 : Matrix _ _ ℂ)) *
        matInt (μ W L) (fun ω => resolventMat (blockFlow W L A s ω) z) =
      1 + (s : ℂ) • matInt (μ W L) (fun ω =>
        blockScalar (fun a => blockTr (resolventMat (blockFlow W L A s ω) z) a a - m) *
          resolventMat (blockFlow W L A s ω) z) := by
  set G : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
    fun ω => resolventMat (blockFlow W L A s ω) z with hG
  set E := matInt (μ W L) G with hE
  set D := matInt (μ W L) (fun ω => blockScalar (fun a => blockTr (G ω) a a) * G ω) with hD
  set M0 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ := A - z • (1 : Matrix _ _ ℂ) with hM0
  have hdiag : ∀ (d : Fin L → ℂ) (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
      (p q : Fin L × Fin W), (blockScalar (W := W) d * M) p q = d p.1 * M p q := by
    intro d M p q
    rw [blockScalar, Matrix.diagonal_mul]
  -- `E[√s V G] = 1 - (A - z) E`
  have hVG : ∀ p q, ∫ ω, (((Real.sqrt s : ℝ) : ℂ) • blockV W L ω * G ω) p q ∂(μ W L) =
      (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) p q - (M0 * E) p q := by
    intro p q
    have hpt : ∀ ω, (((Real.sqrt s : ℝ) : ℂ) • blockV W L ω * G ω) p q =
        (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) p q - ∑ r, M0 p r * G ω r q := by
      intro ω
      have h : M0 * G ω + ((Real.sqrt s : ℝ) : ℂ) • blockV W L ω * G ω = 1 := by
        have h0 := sub_smul_mul_resolventMat (blockFlow_isHermitian W L hA s ω) hz.ne'
        rw [show blockFlow W L A s ω - z • (1 : Matrix _ _ ℂ) =
            M0 + ((Real.sqrt s : ℝ) : ℂ) • blockV W L ω by
          rw [blockFlow, hM0]; abel, Matrix.add_mul] at h0
        exact h0
      rw [← h, Matrix.add_apply, Matrix.mul_apply (M := M0)]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_sub (integrable_const _)
      (integrable_finsetSum _ fun r _ => (roughDensity_integrable_entry hA s hz r q).const_mul _),
      integral_const, integral_finsetSum _ fun r _ =>
        (roughDensity_integrable_entry hA s hz r q).const_mul _]
    simp only [probReal_univ, one_smul, integral_const_mul, Matrix.mul_apply, hE, matInt,
      Matrix.of_apply]
    rfl
  -- `E[√s V G] = -s E[diag(⟨G⟩) G]`
  have hT1 : ∀ p q, ∫ ω, (((Real.sqrt s : ℝ) : ℂ) • blockV W L ω * G ω) p q ∂(μ W L) =
      -(s : ℂ) * D p q := by
    intro p q
    rw [integral_blockV_mul_resolvent W L A hA hs hz p q, hD, matInt, Matrix.of_apply]
    simp only [hdiag]
    rfl
  have hmean : M0 * E = 1 + (s : ℂ) • D := by
    ext p q
    have h1 := hVG p q
    rw [hT1] at h1
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination h1
  have hshift : matInt (μ W L) (fun ω => blockScalar (fun a => blockTr (G ω) a a - m) * G ω) =
      D - m • E := by
    ext p q
    simp only [matInt, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, hD, hE,
      hdiag, sub_mul]
    rw [integral_sub (roughDensity_integrable_blockTr_mul_entry hA s hz p.1 p q)
      ((roughDensity_integrable_entry hA s hz p q).const_mul m), integral_const_mul]
  rw [hshift, show (A - (z + s * m) • (1 : Matrix _ _ ℂ)) =
      M0 - ((s : ℂ) * m) • (1 : Matrix _ _ ℂ) by
    rw [hM0, add_smul]; abel, Matrix.sub_mul, hmean, Matrix.smul_mul, Matrix.one_mul, smul_sub,
    smul_smul]
  abel

theorem lipschitz_blockTr_resolvent (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hA : A.IsHermitian) {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : 0 < z.im) (a : Fin L) (ω ω' : Ω W L) :
    ‖blockTr (resolventMat (blockFlow W L A s ω) z) a a -
        blockTr (resolventMat (blockFlow W L A s ω') z) a a‖ ≤
      Real.sqrt s / (W * z.im ^ 2) * dist (WithLp.toLp 2 ω) (WithLp.toLp 2 ω') := by
  rw [roughDensity_blockTr_sub]
  set Y := resolventMat (blockFlow W L A s ω) z - resolventMat (blockFlow W L A s ω') z
  have hK : 0 ≤ Real.sqrt s / (W * z.im ^ 2) := by positivity
  refine roughDensity_le_of_sq_le (norm_nonneg _) hK ω ω' ?_
  have h1 : ‖blockTr Y a a‖ ^ 2 ≤ (W : ℝ)⁻¹ ^ 2 * (W * ∑ i, ∑ j, ‖Y i j‖ ^ 2) := by
    rw [blockTr, norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
    gcongr
    refine (roughDensity_norm_sum_sq_le _ _).trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
    gcongr
    exact roughDensity_sum_blockDiag_le Y a
  have h2 := roughDensity_sum_sq_sub_le hA hs hz ω ω'
  calc _ ≤ _ := h1
    _ ≤ (W : ℝ)⁻¹ ^ 2 * (W * (s / (W * z.im ^ 4) * ∑ k, (ω k - ω' k) ^ 2)) := by gcongr
    _ = _ := by
      rw [div_pow, Real.sq_sqrt hs, ← mul_assoc, roughDensity_inv_sq_mul]
      ring

theorem lipschitz_trN_resolvent (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hA : A.IsHermitian) {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : 0 < z.im) (ω ω' : Ω W L) :
    ‖trN (resolventMat (blockFlow W L A s ω) z) - trN (resolventMat (blockFlow W L A s ω') z)‖ ≤
      Real.sqrt s / (W * Real.sqrt L * z.im ^ 2) * dist (WithLp.toLp 2 ω) (WithLp.toLp 2 ω') := by
  rw [roughDensity_trN_sub]
  set Y := resolventMat (blockFlow W L A s ω) z - resolventMat (blockFlow W L A s ω') z
  have hK : 0 ≤ Real.sqrt s / (W * Real.sqrt L * z.im ^ 2) := by positivity
  refine roughDensity_le_of_sq_le (norm_nonneg _) hK ω ω' ?_
  have h1 : ‖trN Y‖ ^ 2 ≤
      ((W * L : ℕ) : ℝ)⁻¹ ^ 2 * ((W * L : ℕ) * ∑ i, ∑ j, ‖Y i j‖ ^ 2) := by
    rw [trN, norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
    gcongr
    rw [Matrix.trace]
    refine (roughDensity_norm_sum_sq_le _ _).trans ?_
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, mul_comm L W]
    exact mul_le_mul_of_nonneg_left (roughDensity_sum_diag_le Y) (by positivity)
  have h2 := roughDensity_sum_sq_sub_le hA hs hz ω ω'
  calc _ ≤ _ := h1
    _ ≤ ((W * L : ℕ) : ℝ)⁻¹ ^ 2 * ((W * L : ℕ) * (s / (W * z.im ^ 4) * ∑ k, (ω k - ω' k) ^ 2)) := by
        gcongr
    _ = _ := by
      rw [← mul_assoc, roughDensity_inv_sq_mul, div_pow, mul_pow, mul_pow, Real.sq_sqrt hs,
        Real.sq_sqrt (Nat.cast_nonneg L)]
      push_cast
      ring

/-! ### The variance bound (D.2) [rd:eq:poincare] -/

/-- `Σ_α Y_{(a,α),(a,α)} = Tr(P_a Y)`, `P_a` the projection on block `a`. -/
private lemma roughDensity_sum_blockDiag_eq_trace {W L : ℕ}
    (Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a : Fin L) :
    ∑ α, Y (a, α) (a, α) =
      (Matrix.diagonal (fun P : Fin L × Fin W => if P.1 = a then (1 : ℂ) else 0) * Y).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Fintype.sum_prod_type, ite_mul,
    one_mul, zero_mul]
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-- `Tr(B_{c,k} M) = Tr(T_k M_{cc})`. -/
private lemma roughDensity_trace_blockBasis_mul {W L : ℕ} (c : Fin L) (k : Fin W × Fin W)
    (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    (blockBasis W L c k * M).trace =
      (hermBasis W k * Matrix.of (fun i j => M (c, i) (c, j))).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, blockBasis, Matrix.of_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single c]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single c]
    · simp
    · intro d _ hd; simp [hd]
    · simp
  · intro b _ hb; simp [hb]
  · simp

/-- Parseval for the Hilbert–Schmidt orthonormal basis `T_k` of the Hermitian matrices:
`Σ_k |Tr(T_k X)|² = ‖X‖²_HS` for every complex `X`. -/
private lemma roughDensity_parseval {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) :
    ∑ k : Fin W × Fin W, ‖(hermBasis W k * X).trace‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  apply Complex.ofReal_injective
  have hn : ∀ w : ℂ, ((‖w‖ ^ 2 : ℝ) : ℂ) = w * star w := fun w => by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hT : ∀ k l m, star (hermBasis W k l m) = hermBasis W k m l := fun k l m => by
    have := congrFun (congrFun (hermBasis_isHermitian W k) m) l
    simpa [Matrix.conjTranspose_apply] using this
  simp only [Complex.ofReal_sum, hn, Matrix.trace, Matrix.diag, Matrix.mul_apply, star_sum,
    star_mul', hT, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hk : ∀ x1 i1, ∑ k, hermBasis W k x1 i1 * X i1 x1 * (hermBasis W k j i * star (X j i)) =
      X i1 x1 * star (X j i) * (if x1 = i ∧ i1 = j then 1 else 0) := by
    intro x1 i1
    rw [← sum_hermBasis_apply_mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  calc _ = ∑ x1, ∑ i1, ∑ k, hermBasis W k x1 i1 * X i1 x1 * (hermBasis W k j i * star (X j i)) := by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun x1 _ => Finset.sum_comm
    _ = ∑ x1, ∑ i1, X i1 x1 * star (X j i) * (if x1 = i ∧ i1 = j then 1 else 0) := by
          simp only [hk]
    _ = X j i * star (X j i) := by simp [ite_and]
/-- The diagonal blocks are part of the Hilbert–Schmidt sum. -/
private lemma roughDensity_sum_blocks_le {W L : ℕ} (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    ∑ c : Fin L, ∑ i, ∑ j, ‖M (c, i) (c, j)‖ ^ 2 ≤ ∑ P, ∑ Q, ‖M P Q‖ ^ 2 := by
  rw [Fintype.sum_prod_type (f := fun P => ∑ Q, ‖M P Q‖ ^ 2)]
  refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun i _ => ?_
  rw [Fintype.sum_prod_type (f := fun Q => ‖M (c, i) Q‖ ^ 2)]
  exact Finset.single_le_sum (f := fun d => ∑ j, ‖M (c, i) (d, j)‖ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ c)

/-- `‖P_a‖²_HS = W`. -/
private lemma roughDensity_sum_proj {W L : ℕ} (a : Fin L) :
    ∑ P, ∑ Q, ‖(Matrix.diagonal (fun P : Fin L × Fin W => if P.1 = a then (1 : ℂ) else 0)) P Q‖ ^ 2
      = W := by
  have h1 : ∀ P : Fin L × Fin W, ∑ Q, ‖(Matrix.diagonal
      (fun P : Fin L × Fin W => if P.1 = a then (1 : ℂ) else 0)) P Q‖ ^ 2 =
      if P.1 = a then 1 else 0 := by
    intro P
    rw [Finset.sum_eq_single P (fun Q _ hQ => by simp [Matrix.diagonal_apply_ne _ (Ne.symm hQ)])
      (by simp)]
    by_cases h : P.1 = a <;> simp [h]
  simp only [h1]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-- The block trace as a real-linear functional. -/
private def roughDensity_blockTrLin {W L : ℕ} (a : Fin L) :
    Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ →ₗ[ℝ] ℂ where
  toFun M := blockTr M a a
  map_add' M N := by simp only [blockTr, Matrix.add_apply, Finset.sum_add_distrib, mul_add]
  map_smul' c M := by
    simp only [blockTr, Matrix.smul_apply, Complex.real_smul, RingHom.id_apply, ← Finset.mul_sum]
    ring

/-- `|∇⟨G⟩_{aa}|² ≤ s W⁻² η⁻⁴`. -/
private lemma roughDensity_grad_blockTr_le {W L : ℕ} {A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hA : A.IsHermitian) {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : 0 < z.im) (a : Fin L) (ω : Ω W L) :
    ∑ i, ‖fderiv ℝ (fun ω : Ω W L => blockTr (resolventMat (blockFlow W L A s ω) z) a a) ω
      (Pi.single i 1)‖ ^ 2 ≤ s / ((W : ℝ) ^ 2 * z.im ^ 4) := by
  set Gm := resolventMat (blockFlow W L A s ω) z with hGm
  set Pa : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
    Matrix.diagonal (fun P : Fin L × Fin W => if P.1 = a then (1 : ℂ) else 0) with hPa
  set M := Gm * Pa * Gm with hM
  set c0 : ℂ := ((Real.sqrt s : ℝ) : ℂ) * ((Real.sqrt W : ℝ) : ℂ)⁻¹ with hc0
  have hc0n : ‖c0‖ ^ 2 = s * (W : ℝ)⁻¹ := by
    rw [hc0, norm_mul, norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, inv_pow, Real.sq_sqrt hs, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hterm : ∀ (c : Fin L) (k : Fin W × Fin W),
      ‖fderiv ℝ (fun ω : Ω W L => blockTr (resolventMat (blockFlow W L A s ω) z) a a) ω
        (Pi.single (c, k) 1)‖ ^ 2 =
      s * (W : ℝ)⁻¹ * ((W : ℝ)⁻¹ ^ 2 *
        ‖(hermBasis W k * Matrix.of (fun i j => M (c, i) (c, j))).trace‖ ^ 2) := by
    intro c k
    have hd := roughDensity_fderiv_lin hA s hz (roughDensity_blockTrLin a) ω (Pi.single (c, k) 1)
    have hv : blockV W L (Pi.single (c, k) 1) = ((Real.sqrt W : ℝ) : ℂ)⁻¹ • blockBasis W L c k :=
      roughDensity_blockV_single c k
    change fderiv ℝ (fun ω : Ω W L => blockTr (resolventMat (blockFlow W L A s ω) z) a a) ω
      (Pi.single (c, k) 1) = blockTr (-(Gm * (((Real.sqrt s : ℝ) : ℂ) •
        blockV W L (Pi.single (c, k) 1)) * Gm)) a a at hd
    have e : -(Gm * (((Real.sqrt s : ℝ) : ℂ) • blockV W L (Pi.single (c, k) 1)) * Gm) =
        (-c0) • (Gm * blockBasis W L c k * Gm) := by
      rw [hv, hc0, smul_smul, Matrix.mul_smul, Matrix.smul_mul, neg_smul]
    have htr : blockTr ((-c0) • (Gm * blockBasis W L c k * Gm)) a a =
        -c0 * (W : ℂ)⁻¹ * (hermBasis W k * Matrix.of (fun i j => M (c, i) (c, j))).trace := by
      rw [← roughDensity_trace_blockBasis_mul, blockTr]
      simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      rw [roughDensity_sum_blockDiag_eq_trace, hM,
        show Pa * (Gm * blockBasis W L c k * Gm) = (Pa * Gm) * blockBasis W L c k * Gm by
          simp only [Matrix.mul_assoc],
        Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
      ring
    rw [hd, e, htr, norm_mul, norm_mul, norm_neg, norm_inv, Complex.norm_natCast, mul_pow,
      mul_pow, hc0n]
    ring
  rw [Fintype.sum_prod_type]
  simp only [hterm, ← Finset.mul_sum, roughDensity_parseval, Matrix.of_apply]
  have hHS := sum_norm_sq_resolventMat_mul_mul_le (blockFlow_isHermitian W L hA s ω)
    (blockFlow_isHermitian W L hA s ω) hz (abs_of_pos hz).ge Pa
  rw [roughDensity_sum_proj] at hHS
  calc s * (W : ℝ)⁻¹ * ((W : ℝ)⁻¹ ^ 2 * ∑ c : Fin L, ∑ i, ∑ j, ‖M (c, i) (c, j)‖ ^ 2)
      ≤ s * (W : ℝ)⁻¹ * ((W : ℝ)⁻¹ ^ 2 * (z.im⁻¹ ^ 4 * W)) := by
        gcongr
        exact (roughDensity_sum_blocks_le M).trans hHS
    _ = s / ((W : ℝ) ^ 2 * z.im ^ 4) * ((W : ℝ)⁻¹ * W) := by ring
    _ ≤ s / ((W : ℝ) ^ 2 * z.im ^ 4) := by
        refine mul_le_of_le_one_right (by positivity) ?_
        rcases eq_or_ne (W : ℝ) 0 with h | h
        · simp [h]
        · rw [inv_mul_cancel₀ h]

/-- (D.2) [rd:eq:poincare] with `C = π²/8`. -/
theorem blockTr_resolvent_variance (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hA : A.IsHermitian) {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : 0 < z.im) (a : Fin L) :
    ∫ ω, ‖blockTr (resolventMat (blockFlow W L A s ω) z) a a -
        ∫ ω', blockTr (resolventMat (blockFlow W L A s ω') z) a a ∂(μ W L)‖ ^ 2 ∂(μ W L) ≤
      π ^ 2 / 8 * s / ((W : ℝ) ^ 2 * z.im ^ 4) := by
  set f : Ω W L → ℂ := fun ω => blockTr (resolventMat (blockFlow W L A s ω) z) a a with hf
  have hcd : ContDiff ℝ 1 f := roughDensity_contDiff_lin hA s hz (roughDensity_blockTrLin a)
  have hK : 0 ≤ Real.sqrt s / (W * z.im ^ 2) := by positivity
  have hb := roughDensity_norm_fderiv_le hK (lipschitz_blockTr_resolvent W L A hA hs hz a)
  have hP := poincare_grad (ι := Fin L × Fin W × Fin W) f hcd hb
  have hint : ∫ ω, ∑ i, ‖fderiv ℝ f ω (Pi.single i 1)‖ ^ 2 ∂(μ W L) ≤
      s / ((W : ℝ) ^ 2 * z.im ^ 4) := by
    by_cases hi : Integrable (fun ω => ∑ i, ‖fderiv ℝ f ω (Pi.single i 1)‖ ^ 2) (μ W L)
    · calc _ ≤ ∫ _ω, s / ((W : ℝ) ^ 2 * z.im ^ 4) ∂(μ W L) :=
            integral_mono hi (integrable_const _) (roughDensity_grad_blockTr_le hA hs hz a)
        _ = s / ((W : ℝ) ^ 2 * z.im ^ 4) := by simp
    · rw [integral_undef hi]
      positivity
  calc _ ≤ π ^ 2 / 8 * ∫ ω, ∑ i, ‖fderiv ℝ f ω (Pi.single i 1)‖ ^ 2 ∂(μ W L) := hP
    _ ≤ π ^ 2 / 8 * (s / ((W : ℝ) ^ 2 * z.im ^ 4)) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = π ^ 2 / 8 * s / ((W : ℝ) ^ 2 * z.im ^ 4) := by ring

/-! ### The concentration bound (D.6) [eq:rough-density] -/

/-- The normalized trace as a real-linear functional. -/
private def roughDensity_trNLin {W L : ℕ} :
    Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ →ₗ[ℝ] ℂ where
  toFun M := trN M
  map_add' M N := by simp only [trN, Matrix.trace_add, mul_add]
  map_smul' c M := by
    simp only [trN, Matrix.trace_smul, Complex.real_smul, RingHom.id_apply]
    ring

/-- (D.6) [eq:rough-density] with the exponent `W² L η⁴ u² / (π² s)`. -/
theorem trN_resolvent_concentration (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hA : A.IsHermitian) {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : 0 < z.im) (u : ℝ) (hu : 0 ≤ u) :
    μ W L {ω | u < ‖trN (resolventMat (blockFlow W L A s ω) z) -
        ∫ ω', trN (resolventMat (blockFlow W L A s ω') z) ∂(μ W L)‖} ≤
      ENNReal.ofReal (4 * Real.exp (-((W : ℝ) ^ 2 * L * z.im ^ 4 * u ^ 2) / (π ^ 2 * s))) := by
  set f : Ω W L → ℂ := fun ω => trN (resolventMat (blockFlow W L A s ω) z) with hf
  have hcd : ContDiff ℝ 1 f := roughDensity_contDiff_lin hA s hz roughDensity_trNLin
  set K : ℝ≥0 := ⟨Real.sqrt s / (W * Real.sqrt L * z.im ^ 2), by positivity⟩ with hK
  have hKc : (K : ℝ) = Real.sqrt s / (W * Real.sqrt L * z.im ^ 2) := rfl
  have hL : LipschitzWith K
      (fun x : EuclideanSpace ℝ (Fin L × Fin W × Fin W) => f x.ofLp) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h1 := lipschitz_trN_resolvent W L A hA hs hz x.ofLp y.ofLp
    simp only [WithLp.toLp_ofLp] at h1
    rw [dist_eq_norm, hKc]
    exact h1
  have h := concentration_complex (ι := Fin L × Fin W × Fin W) f hcd K hL u hu
  have hK2 : (K : ℝ) ^ 2 = s / ((W : ℝ) ^ 2 * L * z.im ^ 4) := by
    rw [hKc, div_pow, mul_pow, mul_pow, Real.sq_sqrt hs,
      Real.sq_sqrt (Nat.cast_nonneg L), ← pow_mul]
  refine le_trans h (le_of_eq ?_)
  rw [hK2, show π ^ 2 * (s / ((W : ℝ) ^ 2 * L * z.im ^ 4)) =
      (π ^ 2 * s) / ((W : ℝ) ^ 2 * L * z.im ^ 4) by ring, div_div_eq_mul_div]
  ring_nf

end LSBA
