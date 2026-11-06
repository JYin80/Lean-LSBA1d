import LSBA.Gauss.GUE
import LSBA.Spectral.ResolventBounds
import LSBA.Kernel.Root
import LSBA.Loop.Basic

/-!
# The single-time realization of the flow

`H_u(g) = A_g ⊗ I + √(uγ_g) V`, the single-time realization of (5.1) [fo:eq:flow], equal to the
model (1.3) [eq:model] at `u = 1`; its scaling; the characteristic `z_u` of (5.3)
[fo:eq:characteristic] with `Im z_u = η_u`; the bound `‖G_u‖ ≤ η_u⁻¹`; `G_0 = M_B ⊗ I`; and
`⟨M^σ⟩_{cc} = m^σ` at a root.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- `H_u(g) = A_g ⊗ I + √(uγ_g) V`, the single-time realization of (5.1) [fo:eq:flow]. -/
def flowH (g : ℝ) (W L : ℕ) (u : ℝ) (ω : Ω W L) : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  blockFlow W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) (u * gammaG g) ω

theorem flowH_isHermitian (g : ℝ) (W L : ℕ) (u : ℝ) (ω : Ω W L) : (flowH g W L u ω).IsHermitian := by
  refine blockFlow_isHermitian W L ?_ _ ω
  have hA : (Ag g L).IsHermitian := by
    unfold Matrix.IsHermitian Ag
    rw [Matrix.conjTranspose_smul, (cycleAdj_isHermitian L).eq]
    simp
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_kronecker, hA.eq, Matrix.conjTranspose_one]

/-- At `u = 1` the realization is the model (1.3) [eq:model]. -/
theorem flowH_one (g : ℝ) (W L : ℕ) (ω : Ω W L) : flowH g W L 1 ω = Hmat g W L ω := by
  rw [Hmat, Hdet_eq_normalized]
  simp [flowH, blockFlow, blockV]

/-- Pointwise scaling of the realization (the identity behind `H_{t_*}(g_*) = c_* H`). -/
theorem flowH_scaling (g g' : ℝ) (W L : ℕ) {u u' c : ℝ} (hc : 0 ≤ c) (hu : 0 ≤ u)
    (hA : Ag g' L = (c : ℂ) • Ag g L) (hγ : u' * gammaG g' = c ^ 2 * (u * gammaG g)) (ω : Ω W L) :
    flowH g' W L u' ω = (c : ℂ) • flowH g W L u ω := by
  have hγpos : 0 < gammaG g := by
    unfold gammaG
    have : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
    positivity
  unfold flowH
  rw [smul_blockFlow W L _ hc (mul_nonneg hu hγpos.le), hγ, hA, Matrix.smul_kronecker]

theorem im_zChar (g E : ℝ) (m : ℂ) (u : ℝ) : (zChar g E m u).im = etaChar g m u := by
  simp [zChar, etaChar]

theorem etaChar_pos (g : ℝ) (m : ℂ) (hm : 0 < m.im) {u : ℝ} (hu : u < 1) : 0 < etaChar g m u := by
  have hγpos : 0 < gammaG g := by
    unfold gammaG
    have : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
    positivity
  unfold etaChar
  have : 0 < 1 - u := by linarith
  positivity

open scoped Matrix.Norms.L2Operator in
/-- `‖G_u‖ ≤ η_u⁻¹` for every Hermitian matrix, (5.3) [fo:eq:characteristic]. -/
theorem norm_resolvent_zChar_le {n : Type*} [Fintype n] [DecidableEq n] (g E : ℝ) (m : ℂ)
    (hm : 0 < m.im) {u : ℝ} (hu : u < 1) {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    ‖resolventMat M (zChar g E m u)‖ ≤ (etaChar g m u)⁻¹ := by
  have hη := etaChar_pos g m hm hu
  refine norm_resolventMat_le hM hη ?_
  rw [im_zChar, abs_of_pos hη]

/-- `G_0 = M_B ⊗ I`, (5.3) [fo:eq:characteristic]. -/
theorem resolvent_flow_zero (g E : ℝ) (W L : ℕ) (m : ℂ) (ω : Ω W L) :
    resolventMat (flowH g W L 0 ω) (zChar g E m 0) =
      dysonMat (hopB g) (gammaG g) L E m ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) := by
  have h : flowH g W L 0 ω - zChar g E m 0 • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) =
      ((hopB g : ℂ) • cycleAdj L - ((E : ℂ) + (gammaG g : ℂ) * m) • (1 : Matrix (Fin L) (Fin L) ℂ))
        ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) := by
    have h1 : (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) =
        (1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) :=
      (Matrix.one_kronecker_one).symm
    rw [h1]
    have hsub : ∀ P Q : Matrix (Fin L) (Fin L) ℂ,
        (P - Q) ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) =
          P ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) - Q ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) := by
      intro P Q
      ext ⟨a, α⟩ ⟨b, β⟩
      simp [Matrix.kroneckerMap_apply, sub_mul]
    rw [hsub, Matrix.smul_kronecker, Matrix.smul_kronecker]
    simp only [flowH, blockFlow, Ag, Matrix.smul_kronecker, zero_mul, Real.sqrt_zero,
      Complex.ofReal_zero, zero_smul, add_zero, hopB, zChar, sub_zero, one_mul]
  unfold resolventMat dysonMat
  rw [h, Matrix.inv_kronecker, inv_one]

/-- The diagonal entry of `M ⊗ I` averaged over the `W` copies is `M_{cc}`. -/
private theorem loopTr_kron_one_true (W L : ℕ) (hW : 1 ≤ W) (M : Matrix (Fin L) (Fin L) ℂ)
    (c : Fin L) :
    loopTr (M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) ![c] ![true] = M c c := by
  rw [loopTr_one]
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (W : ℂ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hW)
  field_simp

/-- `⟨M^σ⟩_{cc} = m^σ` at a root, (5.3) [fo:eq:characteristic]. -/
theorem loopTr_one_dysonMat (g E : ℝ) (W L : ℕ) (hW : 1 ≤ W) (hL : 1 ≤ L) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (c : Fin L) (s : Bool) :
    loopTr (dysonMat (hopB g) (gammaG g) L E m ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) ![c] ![s] =
      if s then m else star m := by
  have hγpos : 0 < gammaG g := by
    unfold gammaG
    have : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
    positivity
  have hw : 0 < ((E : ℂ) + (gammaG g : ℝ) * m).im := by
    simpa using mul_pos hγpos hm.1
  have hdiag : dysonMat (hopB g) (gammaG g) L E m c c = m := by
    rw [dysonMat_diag (hopB g) (gammaG g) L hL (E : ℂ) m hw c]
    exact hm.2.symm
  cases s
  · have h : loopTr (dysonMat (hopB g) (gammaG g) L E m ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
        ![c] ![false] =
        loopTr ((dysonMat (hopB g) (gammaG g) L E m ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))ᴴ)
          ![c] ![true] := by
      simp [loopTr, sgnMat]
    rw [h, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      loopTr_kron_one_true W L hW, Matrix.conjTranspose_apply, hdiag]
    simp
  · rw [loopTr_kron_one_true W L hW, hdiag]
    simp

end LSBA
