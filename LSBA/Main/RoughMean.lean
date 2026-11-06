import LSBA.Gauss.RoughDensity
import LSBA.Gauss.GUELaw
import LSBA.Spectral.ResolventBounds
import LSBA.Dyson.RoughStability
import LSBA.Kernel.Root

/-!
# The mean comparison of Appendix D.2 [sec:rough-density-proof]

`m̄(z) = E N⁻¹ Tr G(z)`; translation invariance `E⟨G⟩_{aa} = m̄`; `m̄ ∈ ℂ_+` with `|m̄| ≤ (Im z)⁻¹`;
the first half of (D.4) [rd:eq:approximate] through the finite Fourier average with constant
`π/(2√2)`; and (D.5) [rd:eq:bias] with explicit constants under `roughErr W L η ≤ η/2`
(Appendix D.2 [sec:rough-density-proof]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- `m̄(z) = E N⁻¹ Tr G(z)`, Appendix D.2 [sec:rough-density-proof]. -/
def mBar (g : ℝ) (W L : ℕ) (z : ℂ) : ℂ :=
  ∫ ω, trN (resolventMat (Hmat g W L ω) z) ∂(μ W L)

/-- The error `(π/(2√2)) W⁻¹ η⁻⁴ + 2π L⁻¹ η⁻²` of (D.4) [rd:eq:approximate]. -/
def roughErr (W L : ℕ) (η : ℝ) : ℝ :=
  π / (2 * Real.sqrt 2) / (W * η ^ 4) + 2 * π / (L * η ^ 2)

/-- `H = A_g ⊗ I_W + √γ_g V`, (1.3) [eq:model] in the form used in Appendix D.2
[sec:rough-density-proof]. -/
theorem Hmat_eq_blockFlow (g : ℝ) (W L : ℕ) (ω : Ω W L) :
    Hmat g W L ω = blockFlow W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) (gammaG g) ω := by
  rw [Hmat, Hdet_eq_normalized, blockFlow, blockV]

/-- `b = (a + 1) mod L` is `b = a + 1` in `Fin (n + 1)`. -/
private lemma roughMean_val_eq_succ_mod {n : ℕ} (a b : Fin (n + 1)) :
    (b.val = (a.val + 1) % (n + 1)) ↔ b = a + 1 := by
  rw [Fin.ext_iff, Fin.val_add, Fin.val_one', Nat.add_mod_mod]

/-- The cycle adjacency matrix is invariant under the rotation of `ℤ_L`. -/
private lemma roughMean_cycleAdj_finRotate (L : ℕ) (a b : Fin L) :
    cycleAdj L (finRotate L a) (finRotate L b) = cycleAdj L a b := by
  cases L with
  | zero => exact a.elim0
  | succ n =>
    simp only [cycleAdj, Matrix.of_apply, finRotate_apply, roughMean_val_eq_succ_mod,
      add_left_inj]

/-- Cyclic relabelling of the blocks conjugates `H` by the block rotation. -/
theorem Hmat_shiftMap_finRotate (g : ℝ) (W L : ℕ) (ω : Ω W L) (p q : Fin L × Fin W) :
    Hmat g W L (shiftMap W L (finRotate L) ω) p q =
      Hmat g W L ω (finRotate L p.1, p.2) (finRotate L q.1, q.2) := by
  rcases p with ⟨a, α⟩
  rcases q with ⟨b, β⟩
  simp only [Hmat, Hdet, Matrix.smul_apply, Matrix.add_apply, Matrix.kroneckerMap_apply,
    blockDiagOp, Matrix.of_apply, gueBlock_shiftMap, roughMean_cycleAdj_finRotate,
    (finRotate L).apply_eq_iff_eq]

/-- Conjugating by a relabelling of the index set conjugates the resolvent. -/
private lemma roughMean_resolventMat_submatrix {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (e : n ≃ n) (z : ℂ) :
    resolventMat (M.submatrix e e) z = (resolventMat M z).submatrix e e := by
  unfold resolventMat
  rw [show M.submatrix e e - z • (1 : Matrix n n ℂ) = (M - z • (1 : Matrix n n ℂ)).submatrix e e by
    ext i j
    simp [Matrix.one_apply]]
  exact Matrix.inv_submatrix_equiv _ _ _

/-- The block trace of the resolvent of the relabelled sample. -/
private lemma roughMean_blockTr_shiftMap (g : ℝ) (W L : ℕ) (z : ℂ) (ω : Ω W L) (a : Fin L) :
    blockTr (resolventMat (Hmat g W L (shiftMap W L (finRotate L) ω)) z) a a =
      blockTr (resolventMat (Hmat g W L ω) z) (finRotate L a) (finRotate L a) := by
  have hH : Hmat g W L (shiftMap W L (finRotate L) ω) =
      (Hmat g W L ω).submatrix (Equiv.prodCongr (finRotate L) (Equiv.refl (Fin W)))
        (Equiv.prodCongr (finRotate L) (Equiv.refl (Fin W))) := by
    ext p q
    rw [Hmat_shiftMap_finRotate]
    rfl
  rw [hH, roughMean_resolventMat_submatrix]
  rfl

/-- Block relabelling as a measurable equivalence. -/
private def roughMean_shiftEquiv (W L : ℕ) (σ : Equiv.Perm (Fin L)) : Ω W L ≃ᵐ Ω W L where
  toFun := shiftMap W L σ
  invFun := shiftMap W L σ.symm
  left_inv ω := by funext x; simp [shiftMap]
  right_inv ω := by funext x; simp [shiftMap]
  measurable_toFun := measurable_pi_iff.mpr fun _ => measurable_pi_apply _
  measurable_invFun := measurable_pi_iff.mpr fun _ => measurable_pi_apply _

/-- `ω ↦ H(ω)` is continuous. -/
private lemma roughMean_continuous_Hmat (g : ℝ) (W L : ℕ) :
    Continuous fun ω : Ω W L => Hmat g W L ω := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  simp only [Hmat, Hdet, Matrix.smul_apply, Matrix.add_apply, blockDiagOp, gueBlock,
    Matrix.of_apply, smul_eq_mul]
  split_ifs <;> fun_prop

/-- The entries of the resolvent are continuous in the sample. -/
private lemma roughMean_continuous_entry (g : ℝ) (W L : ℕ) {z : ℂ} (hz : 0 < z.im)
    (p q : Fin L × Fin W) :
    Continuous fun ω : Ω W L => resolventMat (Hmat g W L ω) z p q := by
  have hc : Continuous fun ω : Ω W L => Hmat g W L ω - z • (1 : Matrix _ _ ℂ) :=
    (roughMean_continuous_Hmat g W L).sub continuous_const
  have hdet : ∀ ω : Ω W L, (Hmat g W L ω - z • (1 : Matrix _ _ ℂ)).det ≠ 0 := fun ω =>
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (isUnit_sub_smul_one (Hmat_isHermitian g W L ω) hz.ne')).ne_zero
  have h : (fun ω : Ω W L => resolventMat (Hmat g W L ω) z p q) = fun ω =>
      (Hmat g W L ω - z • (1 : Matrix _ _ ℂ)).det⁻¹ *
        (Hmat g W L ω - z • (1 : Matrix _ _ ℂ)).adjugate p q := by
    funext ω
    rw [resolventMat, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [h]
  exact (hc.matrix_det.inv₀ hdet).mul (hc.matrix_adjugate.matrix_elem p q)

section Norms

open scoped Matrix.Norms.L2Operator

/-- An entry is bounded by the operator norm. -/
private lemma roughMean_norm_entry_le {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (i j : n) : ‖M i j‖ ≤ ‖M‖ := by
  have h := Matrix.l2_opNorm_mulVec M (EuclideanSpace.single j (1 : ℂ))
  have hn : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  rw [hn, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le ((EuclideanSpace.equiv n ℂ).symm
    (M.mulVec (EuclideanSpace.single j (1 : ℂ)).ofLp)) i
  convert this using 2
  simp

/-- `|G_{pq}| ≤ (Im z)⁻¹`. -/
private lemma roughMean_norm_resolvent_entry_le {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : 0 < z.im) (p q : n) :
    ‖resolventMat A z p q‖ ≤ z.im⁻¹ :=
  (roughMean_norm_entry_le _ p q).trans (norm_resolventMat_le hA hz (abs_of_pos hz).ge)

/-- `|(G(z) G(w))_{pp}| ≤ η⁻²` when `Im z, Im w ≥ η`. -/
private lemma roughMean_norm_resolvent_mul_entry_le {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) {z w : ℂ} {η : ℝ}
    (hη : 0 < η) (hz : η ≤ z.im) (hw : η ≤ w.im) (p q : n) :
    ‖(resolventMat A z * resolventMat B w) p q‖ ≤ (η⁻¹) ^ 2 := by
  refine (roughMean_norm_entry_le _ p q).trans ((norm_mul_le _ _).trans ?_)
  rw [sq]
  exact mul_le_mul (norm_resolventMat_le hA hη (hz.trans (le_abs_self _)))
    (norm_resolventMat_le hB hη (hw.trans (le_abs_self _))) (norm_nonneg _) (by positivity)

end Norms

/-- An average of `card ι` terms of norm at most `C` has norm at most `C`. -/
private lemma roughMean_norm_avg_le {ι : Type*} [Fintype ι] (f : ι → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖f i‖ ≤ C) : ‖((Fintype.card ι : ℂ))⁻¹ * ∑ i, f i‖ ≤ C := by
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · simp [h0, hC]
  · have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hpos
    rw [inv_mul_le_iff₀ hc]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖f i‖ ≤ ∑ _i : ι, C := Finset.sum_le_sum fun i _ => h i
      _ = Fintype.card ι * C := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

private lemma roughMean_blockTr_eq_avg {W L : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a : Fin L) : blockTr X a a = ((Fintype.card (Fin W) : ℂ))⁻¹ * ∑ α, X (a, α) (a, α) := by
  rw [blockTr, Fintype.card_fin]

private lemma roughMean_trN_eq_avg {W L : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    trN X = ((Fintype.card (Fin L × Fin W) : ℂ))⁻¹ * ∑ p, X p p := by
  rw [trN, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.mul_comm]
  rfl

/-- `N⁻¹ Tr X = L⁻¹ Σ_a ⟨X⟩_{aa}`. -/
private lemma roughMean_trN_eq_sum_blockTr {W L : ℕ}
    (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    trN X = (L : ℂ)⁻¹ * ∑ a, blockTr X a a := by
  simp only [trN, blockTr, Matrix.trace, Matrix.diag, Fintype.sum_prod_type, ← Finset.mul_sum]
  push_cast
  rw [mul_inv]
  ring

private lemma roughMean_norm_blockTr_le {W L : ℕ} {X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ p q, ‖X p q‖ ≤ C) (a : Fin L) : ‖blockTr X a a‖ ≤ C := by
  rw [roughMean_blockTr_eq_avg]
  exact roughMean_norm_avg_le _ hC fun α => h _ _

private lemma roughMean_norm_trN_le {W L : ℕ} {X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ p q, ‖X p q‖ ≤ C) : ‖trN X‖ ≤ C := by
  rw [roughMean_trN_eq_avg]
  exact roughMean_norm_avg_le _ hC fun p => h _ _

private lemma roughMean_integrable {W L : ℕ} {E : Type*} [NormedAddCommGroup E]
    {f : Ω W L → E} (hf : Continuous f) (C : ℝ) (h : ∀ ω, ‖f ω‖ ≤ C) :
    Integrable f (μ W L) :=
  Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall h)

private lemma roughMean_continuous_blockTr (g : ℝ) (W L : ℕ) {z : ℂ} (hz : 0 < z.im)
    (a : Fin L) : Continuous fun ω : Ω W L => blockTr (resolventMat (Hmat g W L ω) z) a a :=
  continuous_const.mul (continuous_finsetSum _ fun α _ =>
    roughMean_continuous_entry g W L hz (a, α) (a, α))

private lemma roughMean_continuous_trN (g : ℝ) (W L : ℕ) {z : ℂ} (hz : 0 < z.im) :
    Continuous fun ω : Ω W L => trN (resolventMat (Hmat g W L ω) z) :=
  continuous_const.mul (continuous_finsetSum _ fun p _ =>
    roughMean_continuous_entry g W L hz p p)

/-- Translation invariance: `E⟨G⟩_{aa} = m̄` for every block `a` (Appendix D.2
[sec:rough-density-proof]). -/
theorem integral_blockTr_resolvent_Hmat (g : ℝ) (W L : ℕ) {z : ℂ} (hz : 0 < z.im) (a : Fin L) :
    ∫ ω, blockTr (resolventMat (Hmat g W L ω) z) a a ∂(μ W L) = mBar g W L z := by
  set c : Fin L → ℂ := fun b => ∫ ω, blockTr (resolventMat (Hmat g W L ω) z) b b ∂(μ W L)
    with hc
  have hrot : ∀ b, c (finRotate L b) = c b := by
    intro b
    have hmp : MeasurePreserving (roughMean_shiftEquiv W L (finRotate L)) (μ W L) (μ W L) :=
      measurePreserving_shiftMap W L (finRotate L)
    rw [hc]
    dsimp only
    rw [← hmp.integral_comp' (fun ω => blockTr (resolventMat (Hmat g W L ω) z) b b)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    exact (roughMean_blockTr_shiftMap g W L z ω b).symm
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := Nat.exists_eq_succ_of_ne_zero (Fin.pos a).ne'
  have hconst : ∀ b, c b = c 0 := by
    have hk : ∀ k : ℕ, ∀ hk : k < n + 1, c ⟨k, hk⟩ = c 0 := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        have hkn : k < n := Nat.lt_of_succ_lt_succ hk
        rw [← ih (hkn.trans n.lt_succ_self), ← hrot ⟨k, hkn.trans n.lt_succ_self⟩,
          finRotate_of_lt hkn]
    intro b
    exact hk b.val b.isLt
  have hint : ∀ b, Integrable (fun ω : Ω W (n + 1) =>
      blockTr (resolventMat (Hmat g W (n + 1) ω) z) b b) (μ W (n + 1)) := fun b =>
    roughMean_integrable (roughMean_continuous_blockTr g W (n + 1) hz b) z.im⁻¹ fun ω =>
      roughMean_norm_blockTr_le (by positivity)
        (roughMean_norm_resolvent_entry_le (Hmat_isHermitian g W (n + 1) ω) hz) b
  rw [mBar]
  simp only [roughMean_trN_eq_sum_blockTr]
  rw [integral_const_mul, integral_finsetSum _ fun b _ => hint b]
  change c a = ((n + 1 : ℕ) : ℂ)⁻¹ * ∑ b, c b
  simp only [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [← mul_assoc, inv_mul_cancel₀ this, one_mul]

/-- `Im G_{xx}(z) > 0` for `Im z > 0`, by Ward's identity. -/
private lemma roughMean_im_resolvent_diag_pos {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : 0 < z.im) (x : n) :
    0 < (resolventMat A z x x).im := by
  have hw := ward hA z.re hz.ne' x
  rw [Complex.re_add_im] at hw
  obtain ⟨y, hy⟩ : ∃ y, resolventMat A z x y ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : resolventMat A z * (A - z • (1 : Matrix n n ℂ)) = 1 :=
      mul_eq_one_comm.mp (sub_smul_mul_resolventMat hA hz.ne')
    have h1 := congrFun (congrFun h0 x) x
    simp [Matrix.mul_apply, h] at h1
  have hpos : 0 < ∑ y, ‖resolventMat A z x y‖ ^ 2 :=
    lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hy) 2)
      (Finset.single_le_sum (fun y _ => sq_nonneg ‖resolventMat A z x y‖) (Finset.mem_univ y))
  rw [hw] at hpos
  exact (div_pos_iff_of_pos_right hz).mp hpos

/-- `m̄(z) ∈ ℂ_+` (Appendix D.2 [sec:rough-density-proof]). -/
theorem mBar_im_pos (g : ℝ) (W L : ℕ) (hW : 1 ≤ W) (hL : 1 ≤ L) {z : ℂ} (hz : 0 < z.im) :
    0 < (mBar g W L z).im := by
  have hpt : ∀ ω : Ω W L, 0 < (trN (resolventMat (Hmat g W L ω) z)).im := by
    intro ω
    have hN : (0 : ℝ) < ((W * L : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hW hL
    rw [trN, show (((W * L : ℕ) : ℂ))⁻¹ = (((W * L : ℕ) : ℝ)⁻¹ : ℝ) by push_cast; rfl,
      Complex.im_ofReal_mul, Matrix.trace, Complex.im_sum]
    refine mul_pos (inv_pos.mpr hN) (Finset.sum_pos (fun p _ =>
      roughMean_im_resolvent_diag_pos (Hmat_isHermitian g W L ω) hz p) ?_)
    have : Nonempty (Fin L × Fin W) := ⟨(⟨0, hL⟩, ⟨0, hW⟩)⟩
    exact Finset.univ_nonempty
  have hint : Integrable (fun ω : Ω W L => trN (resolventMat (Hmat g W L ω) z)) (μ W L) :=
    roughMean_integrable (roughMean_continuous_trN g W L hz) z.im⁻¹ fun ω =>
      roughMean_norm_trN_le (by positivity)
        (roughMean_norm_resolvent_entry_le (Hmat_isHermitian g W L ω) hz)
  have him := integral_im hint
  simp only [RCLike.im_to_complex] at him
  rw [mBar, ← him, integral_pos_iff_support_of_nonneg (fun ω => (hpt ω).le) hint.im]
  have hsupp : Function.support (fun ω : Ω W L => (trN (resolventMat (Hmat g W L ω) z)).im) =
      Set.univ := Set.eq_univ_of_forall fun ω => (hpt ω).ne'
  rw [hsupp, measure_univ]
  exact one_pos

/-- `|m̄(z)| ≤ (Im z)⁻¹` (Appendix D.2 [sec:rough-density-proof]). -/
theorem norm_mBar_le (g : ℝ) (W L : ℕ) {z : ℂ} (hz : 0 < z.im) : ‖mBar g W L z‖ ≤ z.im⁻¹ := by
  have h := norm_integral_le_of_norm_le_const (μ := μ W L)
    (f := fun ω => trN (resolventMat (Hmat g W L ω) z)) (C := z.im⁻¹)
    (Filter.Eventually.of_forall fun ω => roughMean_norm_trN_le (by positivity)
      (roughMean_norm_resolvent_entry_le (Hmat_isHermitian g W L ω) hz))
  rwa [probReal_univ, mul_one] at h

private lemma roughMean_gammaG_pos (g : ℝ) : 0 < gammaG g := by
  have := lt_of_lt_of_le one_pos (le_max_left 1 g)
  unfold gammaG
  positivity

private lemma roughMean_gammaG_le_one (g : ℝ) : gammaG g ≤ 1 :=
  inv_le_one_of_one_le₀ (one_le_pow₀ (le_max_left _ _))

/-- `A_g ⊗ I_W` is Hermitian. -/
private lemma roughMean_kron_isHermitian (g : ℝ) (W L : ℕ) :
    (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, Ag, Matrix.conjTranspose_smul,
    (cycleAdj_isHermitian L).eq, Complex.star_def, Complex.conj_ofReal]

/-- `N⁻¹ Tr (X + c Y) = N⁻¹ Tr X + c N⁻¹ Tr Y`. -/
private lemma roughMean_trN_add_smul {W L : ℕ} (X Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (c : ℂ) : trN (X + c • Y) = trN X + c * trN Y := by
  simp only [trN, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  ring

/-- `N⁻¹ Tr (C · E F) = E N⁻¹ Tr (C F)` for integrable entries. -/
private lemma roughMean_trN_mul_matInt {W L : ℕ} (C : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (F : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hF : ∀ p q, Integrable (fun ω => F ω p q) (μ W L)) :
    trN (C * matInt (μ W L) F) = ∫ ω, trN (C * F ω) ∂(μ W L) := by
  simp only [trN, Matrix.trace, Matrix.diag, Matrix.mul_apply, matInt, Matrix.of_apply]
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun r _ => (hF r p).const_mul (C p r)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_finsetSum _ fun r _ => (hF r p).const_mul (C p r)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [integral_const_mul]

/-- `N⁻¹ Tr (A_g ⊗ I_W - w)⁻¹` is the finite Fourier average at `w = z + γ_g m`, by (A.1)
[bl:eq:physical]. -/
private lemma roughMean_trN_inv_kron (g : ℝ) (W L : ℕ) (hW : 1 ≤ W) (hL : 1 ≤ L) (z m : ℂ)
    (hw : 0 < (z + (gammaG g : ℂ) * m).im) :
    trN (W := W) (L := L) ((Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) -
        (z + (gammaG g : ℂ) * m) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ))⁻¹) =
      freeTL (hopB g) L (z + gammaG g * m) := by
  have hK : Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) -
      (z + (gammaG g : ℂ) * m) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) =
      (Ag g L - (z + (gammaG g : ℂ) * m) • (1 : Matrix (Fin L) (Fin L) ℂ)) ⊗ₖ
        (1 : Matrix (Fin W) (Fin W) ℂ) := by
    ext p q
    simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.one_apply,
      Prod.ext_iff, smul_eq_mul]
    split_ifs <;> simp_all
  have hdiag : ∀ a : Fin L,
      (Ag g L - (z + (gammaG g : ℂ) * m) • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹ a a =
        freeTL (hopB g) L (z + gammaG g * m) := fun a =>
    dysonMat_diag (hopB g) (gammaG g) L hL z m hw a
  rw [hK, Matrix.inv_kronecker, inv_one]
  simp only [trN, Matrix.trace, Matrix.diag, Matrix.kroneckerMap_apply, Matrix.one_apply_eq,
    mul_one, hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul]
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hW)
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hL)
  push_cast
  field_simp

/-- `|N⁻¹ Tr (C diag(d_a I_W) S)| ≤ K L⁻¹ Σ_a |d_a|` when `|(S C)_{pp}| ≤ K`. -/
private lemma roughMean_norm_trN_mul_blockScalar_le {W L : ℕ} (hW : 1 ≤ W) (hL : 1 ≤ L)
    (C S : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (d : Fin L → ℂ) {K : ℝ}
    (hK : ∀ p, ‖(S * C) p p‖ ≤ K) :
    ‖trN (C * (blockScalar d * S))‖ ≤ K * ((L : ℝ)⁻¹ * ∑ a, ‖d a‖) := by
  rw [trN, Matrix.trace_mul_comm, Matrix.mul_assoc, norm_mul, norm_inv, Complex.norm_natCast]
  have htr : (blockScalar d * (S * C)).trace = ∑ a, ∑ α, d a * (S * C) (a, α) (a, α) := by
    simp only [Matrix.trace, Matrix.diag, blockScalar, Matrix.diagonal_mul, Fintype.sum_prod_type]
  rw [htr]
  have h1 : ‖∑ a, ∑ α, d a * (S * C) (a, α) (a, α)‖ ≤ ∑ a : Fin L, (W : ℝ) * K * ‖d a‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans ?_)
    calc ∑ α, ‖d a * (S * C) (a, α) (a, α)‖ ≤ ∑ _α : Fin W, K * ‖d a‖ :=
          Finset.sum_le_sum fun α _ => by
            rw [norm_mul, mul_comm]
            exact mul_le_mul_of_nonneg_right (hK _) (norm_nonneg _)
      _ = W * K * ‖d a‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hW0 : (W : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hW)
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hL)
  calc ((W * L : ℕ) : ℝ)⁻¹ * ‖∑ a, ∑ α, d a * (S * C) (a, α) (a, α)‖
      ≤ ((W * L : ℕ) : ℝ)⁻¹ * ∑ a : Fin L, (W : ℝ) * K * ‖d a‖ :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = K * ((L : ℝ)⁻¹ * ∑ a, ‖d a‖) := by
        rw [← Finset.mul_sum]
        push_cast
        field_simp

/-- `|x| ≤ (2t)⁻¹ |x|² + t/2` for `t > 0`. -/
private lemma roughMean_le_sq_add {x t : ℝ} (ht : 0 < t) : x ≤ (2 * t)⁻¹ * x ^ 2 + t / 2 := by
  rw [← sub_nonneg]
  have h : (2 * t)⁻¹ * x ^ 2 + t / 2 - x = (2 * t)⁻¹ * (x - t) ^ 2 := by
    field_simp
    ring
  rw [h]
  positivity

/-- The normalized trace of (D.3) [rd:eq:mean] at `m = m̄`: first half of (D.4)
[rd:eq:approximate], with the finite Fourier average and constant `π/(2√2)`. -/
theorem norm_mBar_sub_freeTL_le (g : ℝ) (W L : ℕ) (hW : 1 ≤ W) (hL : 1 ≤ L) (E η : ℝ)
    (hη : 0 < η) :
    ‖mBar g W L (E + η * Complex.I) -
        freeTL (hopB g) L (E + η * Complex.I + gammaG g * mBar g W L (E + η * Complex.I))‖ ≤
      π / (2 * Real.sqrt 2) / (W * η ^ 4) := by
  set z : ℂ := E + η * Complex.I with hzdef
  have hzim : z.im = η := by simp [hzdef]
  have hz : 0 < z.im := hzim ▸ hη
  set m := mBar g W L z with hmdef
  have hγ0 := roughMean_gammaG_pos g
  have hγ1 := roughMean_gammaG_le_one g
  have hm := mBar_im_pos g W L hW hL hz
  have hmn := norm_mBar_le g W L hz
  set w : ℂ := z + (gammaG g : ℂ) * m with hwdef
  have hwim : η ≤ w.im := by
    simp only [hwdef, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, hzim]
    nlinarith
  have hw0 : 0 < w.im := hη.trans_le hwim
  have hA := roughMean_kron_isHermitian g W L
  set D := Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) -
    w • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) with hDdef
  have hDu : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_sub_smul_one hA hw0.ne')
  -- the mean identity (D.3) [rd:eq:mean] at `m = m̄`
  have hmean := rough_mean_identity W L _ hA hγ0.le hz m
  simp only [← Hmat_eq_blockFlow] at hmean
  set G : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
    fun ω => resolventMat (Hmat g W L ω) z with hGdef
  set d : Ω W L → Fin L → ℂ := fun ω a => blockTr (G ω) a a - m with hddef
  set F : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
    fun ω => blockScalar (d ω) * G ω with hFdef
  -- bounds and integrability
  have hGe : ∀ ω p q, ‖G ω p q‖ ≤ η⁻¹ := fun ω p q => by
    rw [← hzim]; exact roughMean_norm_resolvent_entry_le (Hmat_isHermitian g W L ω) hz p q
  have hdb : ∀ ω a, ‖d ω a‖ ≤ 2 * η⁻¹ := fun ω a => by
    refine (norm_sub_le _ _).trans ?_
    have h1 := roughMean_norm_blockTr_le (by positivity) (hGe ω) a
    rw [hzim] at hmn
    linarith
  have hdc : ∀ a, Continuous fun ω => d ω a := fun a =>
    (roughMean_continuous_blockTr g W L hz a).sub continuous_const
  have hGint : ∀ p q, Integrable (fun ω => G ω p q) (μ W L) := fun p q =>
    roughMean_integrable (roughMean_continuous_entry g W L hz p q) η⁻¹ fun ω => hGe ω p q
  have hFe : ∀ ω p q, F ω p q = d ω p.1 * G ω p q := fun ω p q => by
    simp only [hFdef, blockScalar, Matrix.diagonal_mul]
  have hFint : ∀ p q, Integrable (fun ω => F ω p q) (μ W L) := fun p q => by
    simp only [hFe]
    refine roughMean_integrable ((hdc p.1).mul (roughMean_continuous_entry g W L hz p q))
      (2 * η⁻¹ * η⁻¹) fun ω => ?_
    rw [norm_mul]
    exact mul_le_mul (hdb ω p.1) (hGe ω p q) (norm_nonneg _) (by positivity)
  -- `E G = D⁻¹ + γ D⁻¹ R`
  have hEG : matInt (μ W L) G = D⁻¹ + ((gammaG g : ℝ) : ℂ) • (D⁻¹ * matInt (μ W L) F) := by
    calc matInt (μ W L) G = D⁻¹ * (D * matInt (μ W L) G) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hDu, Matrix.one_mul]
      _ = _ := by rw [hmean, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  have htrEG : trN (matInt (μ W L) G) = m := by
    have h := roughMean_trN_mul_matInt 1 G hGint
    simp only [Matrix.one_mul] at h
    rw [h]
    rfl
  have htrD : trN D⁻¹ = freeTL (hopB g) L w := roughMean_trN_inv_kron g W L hW hL z m hw0
  have hdiff : m - freeTL (hopB g) L w =
      ((gammaG g : ℝ) : ℂ) * ∫ ω, trN (D⁻¹ * F ω) ∂(μ W L) := by
    rw [← roughMean_trN_mul_matInt D⁻¹ F hFint, ← htrD]
    conv_lhs => rw [← htrEG, hEG, roughMean_trN_add_smul]
    ring
  -- pointwise trace bound
  have hpt : ∀ ω, ‖trN (D⁻¹ * F ω)‖ ≤ (η⁻¹) ^ 2 * ((L : ℝ)⁻¹ * ∑ a, ‖d ω a‖) := fun ω =>
    roughMean_norm_trN_mul_blockScalar_le hW hL D⁻¹ (G ω) (d ω) fun p =>
      roughMean_norm_resolvent_mul_entry_le (Hmat_isHermitian g W L ω) hA hη hzim.ge hwim p p
  -- `E|d_a| ≤ t` from the variance bound (D.2) [rd:eq:poincare]
  set t : ℝ := π / (2 * Real.sqrt 2) / (W * η ^ 2) with htdef
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2p : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have ht : 0 < t := by positivity
  have ht2 : t ^ 2 = π ^ 2 / 8 / ((W : ℝ) ^ 2 * η ^ 4) := by
    rw [htdef, div_pow, div_pow, mul_pow, hs2, mul_pow, ← pow_mul]
    ring
  have hE1 : ∀ a, ∫ ω, ‖d ω a‖ ∂(μ W L) ≤ t := by
    intro a
    have hvar := blockTr_resolvent_variance W L _ hA hγ0.le hz a
    simp only [← Hmat_eq_blockFlow] at hvar
    rw [integral_blockTr_resolvent_Hmat g W L hz a, hzim] at hvar
    have hv : ∫ ω, ‖d ω a‖ ^ 2 ∂(μ W L) ≤ t ^ 2 := by
      refine hvar.trans ?_
      rw [ht2]
      have : 0 < π ^ 2 / 8 / ((W : ℝ) ^ 2 * η ^ 4) := by positivity
      calc π ^ 2 / 8 * gammaG g / ((W : ℝ) ^ 2 * η ^ 4)
          = gammaG g * (π ^ 2 / 8 / ((W : ℝ) ^ 2 * η ^ 4)) := by ring
        _ ≤ 1 * (π ^ 2 / 8 / ((W : ℝ) ^ 2 * η ^ 4)) := mul_le_mul_of_nonneg_right hγ1 this.le
        _ = π ^ 2 / 8 / ((W : ℝ) ^ 2 * η ^ 4) := one_mul _
    have hi1 : Integrable (fun ω => ‖d ω a‖) (μ W L) :=
      roughMean_integrable (hdc a).norm (2 * η⁻¹) fun ω => by
        rw [norm_norm]; exact hdb ω a
    have hi2 : Integrable (fun ω => ‖d ω a‖ ^ 2) (μ W L) :=
      roughMean_integrable ((hdc a).norm.pow 2) ((2 * η⁻¹) ^ 2) fun ω => by
        rw [Real.norm_eq_abs, abs_pow, abs_norm]
        exact pow_le_pow_left₀ (norm_nonneg _) (hdb ω a) 2
    calc ∫ ω, ‖d ω a‖ ∂(μ W L) ≤ ∫ ω, ((2 * t)⁻¹ * ‖d ω a‖ ^ 2 + t / 2) ∂(μ W L) :=
          integral_mono hi1 ((hi2.const_mul _).add (integrable_const _))
            fun ω => roughMean_le_sq_add ht
      _ = (2 * t)⁻¹ * ∫ ω, ‖d ω a‖ ^ 2 ∂(μ W L) + t / 2 := by
          rw [integral_add (hi2.const_mul _) (integrable_const _), integral_const_mul,
            integral_const, probReal_univ, one_smul]
      _ ≤ (2 * t)⁻¹ * t ^ 2 + t / 2 := by gcongr
      _ = t := by field_simp; ring
  -- assembling
  have hint : Integrable (fun ω => (η⁻¹) ^ 2 * ((L : ℝ)⁻¹ * ∑ a, ‖d ω a‖)) (μ W L) :=
    ((integrable_finsetSum _ fun a _ =>
      roughMean_integrable (hdc a).norm (2 * η⁻¹) fun ω => by
        rw [norm_norm]; exact hdb ω a).const_mul _).const_mul _
  have hbound : ‖∫ ω, trN (D⁻¹ * F ω) ∂(μ W L)‖ ≤ (η⁻¹) ^ 2 * t := by
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => norm_nonneg _) hint
      (Filter.Eventually.of_forall hpt)).trans ?_
    rw [integral_const_mul, integral_const_mul, integral_finsetSum _ fun a _ =>
      roughMean_integrable (hdc a).norm (2 * η⁻¹) fun ω => by rw [norm_norm]; exact hdb ω a]
    have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
    have hsum : ∑ a : Fin L, ∫ ω, ‖d ω a‖ ∂(μ W L) ≤ L * t := by
      calc ∑ a : Fin L, ∫ ω, ‖d ω a‖ ∂(μ W L) ≤ ∑ _a : Fin L, t :=
            Finset.sum_le_sum fun a _ => hE1 a
        _ = L * t := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (L : ℝ)⁻¹ * ∑ a : Fin L, ∫ ω, ‖d ω a‖ ∂(μ W L) ≤ t := by
      rw [inv_mul_le_iff₀ hL0]; exact hsum
    exact mul_le_mul_of_nonneg_left this (by positivity)
  rw [hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hγ0]
  calc gammaG g * ‖∫ ω, trN (D⁻¹ * F ω) ∂(μ W L)‖ ≤ 1 * ((η⁻¹) ^ 2 * t) :=
        mul_le_mul hγ1 hbound (norm_nonneg _) zero_le_one
    _ = π / (2 * Real.sqrt 2) / (W * η ^ 4) := by
        rw [htdef]
        field_simp

/-- (D.5) [rd:eq:bias] with explicit constants, under `roughErr W L η ≤ η/2`. -/
theorem norm_mBar_sub_mDyson_le (g : ℝ) (hg : 0 ≤ g) (W L : ℕ) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (E η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hρ : roughErr W L η ≤ η / 2) :
    ‖mBar g W L (E + η * Complex.I) - mDyson g (E + η * Complex.I)‖ ≤
      8 * (η⁻¹) ^ 2 * roughErr W L η := by
  set z : ℂ := E + η * Complex.I with hzdef
  have hzim : z.im = η := by simp [hzdef]
  have hz : 0 < z.im := hzim ▸ hη
  set u := mBar g W L z with hudef
  have hu : 0 < u.im := mBar_im_pos g W L hW hL hz
  have hu1 : ‖u‖ ≤ η⁻¹ := hzim ▸ norm_mBar_le g W L hz
  set w : ℂ := z + (gammaG g : ℂ) * u with hwdef
  have hwim : η ≤ w.im := by
    have hγ0 := roughMean_gammaG_pos g
    simp only [hwdef, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, hzim]
    nlinarith
  set r := u - freeT (hopB g) w with hrdef
  have h1 := norm_mBar_sub_freeTL_le g W L hW hL E η hη
  have h2 := freeTL_sub_freeT g hg L hL η hη w hwim
  have hr : ‖r‖ ≤ roughErr W L η := by
    have hsplit : r = (u - freeTL (hopB g) L w) + (freeTL (hopB g) L w - freeT (hopB g) w) := by
      rw [hrdef]; ring
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hL)
    have he : 2 * π / L * (η⁻¹) ^ 2 = 2 * π / (L * η ^ 2) := by
      field_simp
    rw [hsplit, roughErr]
    refine (norm_add_le _ _).trans ?_
    rw [← he]
    exact add_le_add h1 h2
  have hur : u = freeT (hopB g) (E + η * Complex.I + gammaG g * u) + r := by
    rw [hrdef]; ring
  refine (rough_stability g hg E η hη hη1 u r hu hu1 hur (hr.trans hρ)).trans ?_
  exact mul_le_mul_of_nonneg_left hr (by positivity)

end LSBA
