import LSBA.Upper.ConversionInterval
import LSBA.Kernel.Defs

/-!
# Decay on the cycle

(E.16) [eq:c-cycle]: fractional moments of the cycle resolvent blocks decay like
`exp(−(log W/(n₀+1))‖a − b‖_L)`, from (E.15) [eq:c-cycle-Schur], (8.7) [eq:c-apriori] and (E.14)
[eq:c-interval] (proof of Proposition 8.2 [up:prop:fr-concentration], Appendix E.2
[app:finite-volume-criterion]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The path index of `b` seen from `a` on the cycle: `b = a + 1 + j`, and both path distances
`j` and `L - 2 - j` are at least `‖a - b‖_L - 1`. -/
private lemma cycle_index {L : ℕ} {a b : Fin L} (hab : a ≠ b) :
    ∃ j : Fin (L - 1), cycPathBlock a j = b ∧ cycDist a b ≤ j.val + 1 ∧
      cycDist a b + j.val + 1 ≤ L := by
  have ha := a.isLt
  have hb := b.isLt
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · have h1 : (a.val + L - b.val) % L = a.val + L - b.val := Nat.mod_eq_of_lt (by omega)
    have h2 : (b.val + L - a.val) % L = b.val - a.val := by
      rw [show b.val + L - a.val = (b.val - a.val) + L by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    refine ⟨⟨b.val - a.val - 1, by omega⟩, Fin.ext ?_, ?_, ?_⟩
    · simp only [cycPathBlock]
      rw [show a.val + 1 + (b.val - a.val - 1) = b.val by omega, Nat.mod_eq_of_lt hb]
    · simp only [cycDist, h1, h2]
      omega
    · simp only [cycDist, h1, h2]
      omega
  · have h1 : (a.val + L - b.val) % L = a.val - b.val := by
      rw [show a.val + L - b.val = (a.val - b.val) + L by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    have h2 : (b.val + L - a.val) % L = b.val + L - a.val := Nat.mod_eq_of_lt (by omega)
    refine ⟨⟨b.val + L - a.val - 1, by omega⟩, Fin.ext ?_, ?_, ?_⟩
    · simp only [cycPathBlock]
      rw [show a.val + 1 + (b.val + L - a.val - 1) = b.val + L by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hb]
    · simp only [cycDist, h1, h2]
      omega
    · simp only [cycDist, h1, h2]
      omega

/-- The map `j ↦ a + 1 + j` of the path `ℤ_L ∖ {a}` into `ℤ_L` is injective. -/
private lemma cycle_injective {L : ℕ} (a : Fin L) :
    Function.Injective (cycPathBlock a : Fin (L - 1) → Fin L) := by
  intro j k h
  have h1 : (a.val + 1 + j.val) % L = (a.val + 1 + k.val) % L := congrArg Fin.val h
  have h2 : j.val ≡ k.val [MOD L] := Nat.ModEq.add_left_cancel' (a.val + 1) h1
  have := j.isLt
  have := k.isLt
  exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt h2 (by omega) (by omega))

/-- The blocks of the sample along the path `ℤ_L ∖ {a}` are the blocks of the window sample. -/
private lemma cycle_gueBlock_window (W L : ℕ) (a : Fin L) (ω : Ω W L) :
    gueBlock W L ω ∘ cycPathBlock a = gueBlock W (L - 1) (windowSample (cycPathBlock a) ω) :=
  funext fun i => (gueBlock_windowSample _ ω i).symm

/-- The block diagonal operator with zero blocks is zero. -/
private lemma cycle_blockDiagOp_zero {W n : ℕ} :
    blockDiagOp (fun _ : Fin n => (0 : Matrix (Fin W) (Fin W) ℂ)) = 0 := by
  ext p q
  simp [blockDiagOp]

/-- The cycle operator is the deterministic part plus the scaled diagonal block potential. -/
private lemma cycle_Hmat_decomp (g : ℝ) {W L : ℕ} (ω : Ω W L) :
    Hmat g W L ω = Hdet g (fun _ : Fin L => (0 : Matrix (Fin W) (Fin W) ℂ)) +
      (((max 1 g)⁻¹ : ℝ) : ℂ) • blockDiagOp (gueBlock W L ω) := by
  simp only [Hmat, Hdet, cycle_blockDiagOp_zero, add_zero, smul_add, Complex.ofReal_inv]

/-- The path operator with zero shifts is the free part plus the scaled diagonal block
potential. -/
private lemma cycle_pathOp_decomp (g : ℝ) {W n : ℕ} (ω : Ω W n) :
    pathOp g (gueBlock W n ω) 0 0 =
      pathOp g (fun _ : Fin n => (0 : Matrix (Fin W) (Fin W) ℂ)) 0 0 +
        (((max 1 g)⁻¹ : ℝ) : ℂ) • blockDiagOp (gueBlock W n ω) := by
  simp only [pathOp, cycle_blockDiagOp_zero, add_zero, smul_add, Complex.ofReal_inv, ite_self]

/-- The `x, y` block norm to the power `t` of the cycle resolvent is a measurable function of the
sample. -/
private lemma cycle_measurable_Hmat_enorm {W L : ℕ} (g t E : ℝ) (x y : Fin L) :
    Measurable fun ω : Ω W L => ‖blockOf (resolventMat (Hmat g W L ω) E) x y‖ₑ ^ t := by
  have h := measurable_resolventMat_gueBlock (W := W) (n := L)
    (Hdet g (fun _ : Fin L => (0 : Matrix (Fin W) (Fin W) ℂ))) ((max 1 g)⁻¹) (E : ℂ)
  have hblk : Measurable fun X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ => blockOf X x y := by
    refine Measurable.of_eval_matrix _ fun α β => ?_
    exact measurable_id.eval_matrix (i := (x, α)) (j := (y, β))
  simp only [cycle_Hmat_decomp]
  exact (continuous_enorm.measurable.comp (hblk.comp h)).pow_const t

/-- The `x, y` block norm to the power `t` of the resolvent of the path operator is a measurable
function of the sample. -/
private lemma cycle_measurable_path_enorm {W n : ℕ} (g t E : ℝ) (x y : Fin n) :
    Measurable fun ω : Ω W n =>
      ‖blockOf (resolventMat (pathOp g (gueBlock W n ω) 0 0) E) x y‖ₑ ^ t := by
  have h := measurable_resolventMat_gueBlock (W := W) (n := n)
    (pathOp g (fun _ : Fin n => (0 : Matrix (Fin W) (Fin W) ℂ)) 0 0) ((max 1 g)⁻¹) (E : ℂ)
  have hblk : Measurable fun X : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ => blockOf X x y := by
    refine Measurable.of_eval_matrix _ fun α β => ?_
    exact measurable_id.eval_matrix (i := (x, α)) (j := (y, β))
  simp only [cycle_pathOp_decomp]
  exact (continuous_enorm.measurable.comp (hblk.comp h)).pow_const t

/-- The determinant of `pathOp - E` over the Dirichlet path of GUE blocks is a.s. nonzero. -/
private lemma cycle_ae_det (g : ℝ) (W n : ℕ) (E : ℝ) :
    ∀ᵐ ω ∂(μ W n), (pathOp g (gueBlock W n ω) 0 0 -
      (E : ℂ) • (1 : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ)).det ≠ 0 := by
  have hm : (max 1 g)⁻¹ ≠ 0 := inv_ne_zero (lt_of_lt_of_le one_pos (le_max_left 1 g)).ne'
  filter_upwards [ae_det_ne_zero_gueBlock
    (pathOp g (fun _ : Fin n => (0 : Matrix (Fin W) (Fin W) ℂ)) 0 0) hm (E : ℂ)] with ω hω
  rwa [cycle_pathOp_decomp]

/-- The constant `C_p` of (8.7) [eq:c-apriori] is positive for `p < 1`. -/
private lemma cycle_aprioriConst_pos {p : ℝ} (h1 : p < 1) : 0 < aprioriConst p := by
  unfold aprioriConst
  have : 0 < 1 - p := by linarith
  positivity

/-- `(max{1, g} w²)^t ≤ w^{(B+2) t}` when `max{1, g} ≤ w^B` and `w ≥ 1`. -/
private lemma cycle_X_rpow_le {t B g w : ℝ} (ht0 : 0 < t) (hw1 : 1 ≤ w)
    (hgB : max 1 g ≤ w ^ B) : (max 1 g * w ^ 2) ^ t ≤ w ^ ((B + 2) * t) := by
  have hw0 : 0 < w := by linarith
  have hX : max 1 g * w ^ 2 ≤ w ^ (B + 2) := by
    rw [Real.rpow_add hw0, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_right hgB (by positivity)
  have hX0 : 0 ≤ max 1 g * w ^ 2 := by positivity
  calc (max 1 g * w ^ 2) ^ t ≤ (w ^ (B + 2)) ^ t := Real.rpow_le_rpow hX0 hX ht0.le
    _ = w ^ ((B + 2) * t) := (Real.rpow_mul hw0.le _ _).symm

/-- Pointwise form of (E.15) [eq:c-cycle-Schur]: the block norm to the power `u ≤ 1` is at most
`‖G_{aa}‖^u (‖G^{(a)}_{0,j}‖^u + ‖G^{(a)}_{L-2,j}‖^u)`, since `g / max{1, g} ≤ 1`. -/
private lemma cycle_pointwise {u g : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) (hg0 : 0 ≤ g) {W L : ℕ}
    (hL : 3 ≤ L) (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (E : ℝ) (a : Fin L)
    (hdet : (pathOp g (V ∘ cycPathBlock a) 0 0 -
      (E : ℂ) • (1 : Matrix (Fin (L - 1) × Fin W) (Fin (L - 1) × Fin W) ℂ)).det ≠ 0)
    (j : Fin (L - 1)) :
    ‖blockOf (resolventMat (Hdet g V) E) a (cycPathBlock a j)‖ₑ ^ u ≤
      ‖blockOf (resolventMat (Hdet g V) E) a a‖ₑ ^ u *
        (‖blockOf (resolventMat (pathOp g (V ∘ cycPathBlock a) 0 0) E) ⟨0, by omega⟩ j‖ₑ ^ u +
          ‖blockOf (resolventMat (pathOp g (V ∘ cycPathBlock a) 0 0) E) ⟨L - 2, by omega⟩ j‖ₑ ^
            u) := by
  rw [cycle_schur' g hL V E a hdet j]
  set G := blockOf (resolventMat (Hdet g V) E) a a with hG
  set X := blockOf (resolventMat (pathOp g (V ∘ cycPathBlock a) 0 0) E) ⟨0, by omega⟩ j with hX
  set Y := blockOf (resolventMat (pathOp g (V ∘ cycPathBlock a) 0 0) E) ⟨L - 2, by omega⟩ j
    with hY
  have hm : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left 1 g)
  have hr0 : 0 ≤ g / max 1 g := div_nonneg hg0 hm.le
  have hr1 : g / max 1 g ≤ 1 := (div_le_one hm).mpr (le_max_right 1 g)
  have hnorm : ‖-((g / max 1 g : ℝ) : ℂ) • (G * (X + Y))‖ ≤ ‖G‖ * (‖X‖ + ‖Y‖) := by
    rw [norm_smul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hr0]
    calc g / max 1 g * ‖G * (X + Y)‖ ≤ 1 * ‖G * (X + Y)‖ :=
          mul_le_mul_of_nonneg_right hr1 (norm_nonneg _)
      _ ≤ ‖G‖ * ‖X + Y‖ := by rw [one_mul]; exact norm_mul_le _ _
      _ ≤ ‖G‖ * (‖X‖ + ‖Y‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
  have h2 : ‖-((g / max 1 g : ℝ) : ℂ) • (G * (X + Y))‖ₑ ≤ ‖G‖ₑ * (‖X‖ₑ + ‖Y‖ₑ) := by
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
      ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hnorm
  calc ‖-((g / max 1 g : ℝ) : ℂ) • (G * (X + Y))‖ₑ ^ u ≤ (‖G‖ₑ * (‖X‖ₑ + ‖Y‖ₑ)) ^ u :=
        ENNReal.rpow_le_rpow h2 hu0.le
    _ = ‖G‖ₑ ^ u * (‖X‖ₑ + ‖Y‖ₑ) ^ u := ENNReal.mul_rpow_of_nonneg _ _ hu0.le
    _ ≤ ‖G‖ₑ ^ u * (‖X‖ₑ ^ u + ‖Y‖ₑ ^ u) :=
        mul_le_mul_right (ENNReal.rpow_add_le_add_rpow _ _ hu0.le hu1) _

/-- Cauchy–Schwarz for the product of two measurable functions from the second moments. -/
private lemma cycle_holder {α : Type*} [MeasurableSpace α] {μ : Measure α} {f h : α → ℝ≥0∞}
    (hf : Measurable f) (hh : Measurable h) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hfx : ∫⁻ ω, f ω ^ (2 : ℝ) ∂μ ≤ ENNReal.ofReal x)
    (hhy : ∫⁻ ω, h ω ^ (2 : ℝ) ∂μ ≤ ENNReal.ofReal y) :
    ∫⁻ ω, f ω * h ω ∂μ ≤ ENNReal.ofReal (Real.sqrt x * Real.sqrt y) := by
  have key := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    hf.aemeasurable hh.aemeasurable
  refine key.trans ?_
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  refine mul_le_mul' ?_ ?_
  · calc (∫⁻ ω, f ω ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤ (ENNReal.ofReal x) ^ (1 / (2 : ℝ)) :=
          ENNReal.rpow_le_rpow hfx (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt x) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hx (by norm_num), Real.sqrt_eq_rpow]
  · calc (∫⁻ ω, h ω ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤ (ENNReal.ofReal y) ^ (1 / (2 : ℝ)) :=
          ENNReal.rpow_le_rpow hhy (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt y) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hy (by norm_num), Real.sqrt_eq_rpow]

/-- (E.15) [eq:c-cycle-Schur] and (E.16) [eq:c-cycle] from an abstract path bound: for `0 < p < 1`,
`g ≥ 0`, `L ≥ 3` and `κ ≥ 0`, the bound `𝔼‖G^{(a)}(x, y; E)‖^p ≤ A exp(-2κ |x - y|)` on the
Dirichlet path of `L - 1` blocks and (8.7) [eq:c-apriori] give, for `a ≠ c`,
`𝔼‖G(a, c; E)‖^{p/2} ≤ 2 (C_p (max{1, g} W²)^p)^{1/2} A^{1/2} e^κ exp(-κ ‖a - c‖_L)`. -/
theorem cycle_moment_of_path {p g : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hg0 : 0 ≤ g) {W L : ℕ}
    (hL : 3 ≤ L) {E A κ : ℝ} (hA : 0 ≤ A) (hκ : 0 ≤ κ)
    (hP : ∀ x y : Fin (L - 1),
      ∫⁻ ω, ‖blockOf (resolventMat (pathOp g (gueBlock W (L - 1) ω) 0 0) E) x y‖ₑ ^ p
          ∂(μ W (L - 1)) ≤
        ENNReal.ofReal (A * Real.exp (-(2 * κ) * |((x : ℕ) : ℝ) - (y : ℕ)|)))
    {a c : Fin L} (hac : a ≠ c) :
    ∫⁻ ω, ‖blockOf (resolventMat (Hmat g W L ω) E) a c‖ₑ ^ (p / 2) ∂(μ W L) ≤
      ENNReal.ofReal (2 * Real.sqrt (aprioriConst p * (max 1 g * (W : ℝ) ^ 2) ^ p) *
        Real.sqrt A * Real.exp κ * Real.exp (-κ * cycDist a c)) := by
  obtain ⟨j, rfl, hj1, hj2⟩ := cycle_index hac
  have hc : 0 < aprioriConst p := cycle_aprioriConst_pos hp1
  have hu0 : 0 < p / 2 := by positivity
  have hu1 : p / 2 ≤ 1 := by linarith
  have hup : p / 2 * 2 = p := by ring
  set F : ℝ := aprioriConst p * (max 1 g * (W : ℝ) ^ 2) ^ p with hF
  have hF0 : 0 ≤ F := by positivity
  have hmp := measurePreserving_windowSample W L (L - 1) (cycle_injective a)
  have hf2 : ∫⁻ ω, (‖blockOf (resolventMat (Hmat g W L ω) E) a a‖ₑ ^ (p / 2)) ^ (2 : ℝ)
      ∂(μ W L) ≤ ENNReal.ofReal F := by
    have h1 : ∀ ω : Ω W L, (‖blockOf (resolventMat (Hmat g W L ω) E) a a‖ₑ ^ (p / 2)) ^
        (2 : ℝ) = ‖blockOf (resolventMat (Hmat g W L ω) E) a a‖ₑ ^ p := fun ω => by
      rw [← ENNReal.rpow_mul, hup]
    simp_rw [h1]
    exact Hmat_moment_le g hp0 hp1 E a a
  have hR2 : ∀ x y : Fin (L - 1),
      ∫⁻ ω, (‖blockOf (resolventMat (pathOp g (gueBlock W (L - 1)
          (windowSample (cycPathBlock a) ω)) 0 0) E) x y‖ₑ ^ (p / 2)) ^ (2 : ℝ) ∂(μ W L) ≤
        ENNReal.ofReal (A * Real.exp (-(2 * κ) * |((x : ℕ) : ℝ) - (y : ℕ)|)) := by
    intro x y
    have hm : Measurable fun ω' : Ω W (L - 1) => (‖blockOf (resolventMat
        (pathOp g (gueBlock W (L - 1) ω') 0 0) E) x y‖ₑ ^ (p / 2)) ^ (2 : ℝ) :=
      (cycle_measurable_path_enorm g (p / 2) E x y).pow_const 2
    calc ∫⁻ ω, (‖blockOf (resolventMat (pathOp g (gueBlock W (L - 1)
          (windowSample (cycPathBlock a) ω)) 0 0) E) x y‖ₑ ^ (p / 2)) ^ (2 : ℝ) ∂(μ W L)
        = ∫⁻ ω', (‖blockOf (resolventMat (pathOp g (gueBlock W (L - 1) ω') 0 0) E) x y‖ₑ ^
            (p / 2)) ^ (2 : ℝ) ∂(μ W (L - 1)) := hmp.lintegral_comp hm
      _ = ∫⁻ ω', ‖blockOf (resolventMat (pathOp g (gueBlock W (L - 1) ω') 0 0) E) x y‖ₑ ^ p
            ∂(μ W (L - 1)) := by
          simp_rw [← ENNReal.rpow_mul, hup]
      _ ≤ _ := hP x y
  have hstep : ∀ d e : ℝ, d - 1 ≤ e →
      Real.sqrt F * Real.sqrt (A * Real.exp (-(2 * κ) * e)) ≤
        Real.sqrt F * Real.sqrt A * Real.exp κ * Real.exp (-κ * d) := by
    intro d e hde
    have hs : Real.sqrt (A * Real.exp (-(2 * κ) * e)) ≤
        Real.sqrt A * (Real.exp κ * Real.exp (-κ * d)) := by
      rw [Real.sqrt_mul hA]
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      rw [← Real.exp_add, Real.sqrt_le_left (by positivity), ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left (show d - e ≤ 1 by linarith) hκ]
    calc _ ≤ Real.sqrt F * (Real.sqrt A * (Real.exp κ * Real.exp (-κ * d))) :=
          mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
      _ = _ := by ring
  have hterm : ∀ x : Fin (L - 1), ∀ e : ℝ, |((x : ℕ) : ℝ) - (j : ℕ)| = e →
      (cycDist a (cycPathBlock a j) : ℝ) - 1 ≤ e →
      ∫⁻ ω, ‖blockOf (resolventMat (Hmat g W L ω) E) a a‖ₑ ^ (p / 2) *
          ‖blockOf (resolventMat (pathOp g (gueBlock W (L - 1)
            (windowSample (cycPathBlock a) ω)) 0 0) E) x j‖ₑ ^ (p / 2) ∂(μ W L) ≤
        ENNReal.ofReal (Real.sqrt F * Real.sqrt A * Real.exp κ *
          Real.exp (-κ * (cycDist a (cycPathBlock a j) : ℝ))) := by
    intro x e hxe hde
    have hm1 : Measurable fun ω : Ω W L => ‖blockOf (resolventMat (Hmat g W L ω) E) a a‖ₑ ^
        (p / 2) := cycle_measurable_Hmat_enorm g (p / 2) E a a
    have hm2 : Measurable fun ω : Ω W L => ‖blockOf (resolventMat (pathOp g (gueBlock W (L - 1)
        (windowSample (cycPathBlock a) ω)) 0 0) E) x j‖ₑ ^ (p / 2) :=
      (cycle_measurable_path_enorm g (p / 2) E x j).comp hmp.measurable
    have hy := hR2 x j
    rw [hxe] at hy
    exact (cycle_holder hm1 hm2 hF0 (by positivity) hf2 hy).trans
      (ENNReal.ofReal_le_ofReal (hstep _ e hde))
  have hae : ∀ᵐ ω ∂(μ W L),
      ‖blockOf (resolventMat (Hmat g W L ω) E) a (cycPathBlock a j)‖ₑ ^ (p / 2) ≤
        ‖blockOf (resolventMat (Hmat g W L ω) E) a a‖ₑ ^ (p / 2) *
            ‖blockOf (resolventMat (pathOp g (gueBlock W (L - 1)
              (windowSample (cycPathBlock a) ω)) 0 0) E) ⟨0, by omega⟩ j‖ₑ ^ (p / 2) +
          ‖blockOf (resolventMat (Hmat g W L ω) E) a a‖ₑ ^ (p / 2) *
            ‖blockOf (resolventMat (pathOp g (gueBlock W (L - 1)
              (windowSample (cycPathBlock a) ω)) 0 0) E) ⟨L - 2, by omega⟩ j‖ₑ ^ (p / 2) := by
    filter_upwards [hmp.quasiMeasurePreserving.ae (cycle_ae_det g W (L - 1) E)] with ω hω
    have hω' : (pathOp g (gueBlock W L ω ∘ cycPathBlock a) 0 0 -
        (E : ℂ) • (1 : Matrix (Fin (L - 1) × Fin W) (Fin (L - 1) × Fin W) ℂ)).det ≠ 0 := by
      rw [cycle_gueBlock_window]
      exact hω
    have key := cycle_pointwise hu0 hu1 hg0 hL (gueBlock W L ω) E a hω' j
    rw [cycle_gueBlock_window, mul_add] at key
    exact key
  have hm1 : Measurable fun ω : Ω W L => ‖blockOf (resolventMat (Hmat g W L ω) E) a a‖ₑ ^
      (p / 2) := cycle_measurable_Hmat_enorm g (p / 2) E a a
  have hm2 : Measurable fun ω : Ω W L => ‖blockOf (resolventMat (pathOp g (gueBlock W (L - 1)
      (windowSample (cycPathBlock a) ω)) 0 0) E) ⟨0, by omega⟩ j‖ₑ ^ (p / 2) :=
    (cycle_measurable_path_enorm g (p / 2) E _ j).comp hmp.measurable
  have hx0 : |(((⟨0, by omega⟩ : Fin (L - 1)) : ℕ) : ℝ) - (j : ℕ)| = (j : ℕ) := by
    simp
  have hx1 : |(((⟨L - 2, by omega⟩ : Fin (L - 1)) : ℕ) : ℝ) - (j : ℕ)| =
      ((L - 2 - j : ℕ) : ℝ) := by
    have hjle : (j : ℕ) ≤ L - 2 := by have := j.isLt; omega
    simp only
    rw [abs_of_nonneg (by rw [sub_nonneg]; exact_mod_cast hjle), Nat.cast_sub hjle]
  have hdX : (cycDist a (cycPathBlock a j) : ℝ) - 1 ≤ ((j : ℕ) : ℝ) := by
    have : (cycDist a (cycPathBlock a j) : ℝ) ≤ ((j : ℕ) : ℝ) + 1 := by exact_mod_cast hj1
    linarith
  have hdY : (cycDist a (cycPathBlock a j) : ℝ) - 1 ≤ ((L - 2 - j : ℕ) : ℝ) := by
    have hjl := j.isLt
    have h3 : cycDist a (cycPathBlock a j) ≤ (L - 2 - j) + 1 := by omega
    have : (cycDist a (cycPathBlock a j) : ℝ) ≤ ((L - 2 - j : ℕ) : ℝ) + 1 := by
      exact_mod_cast h3
    linarith
  have hX := hterm ⟨0, by omega⟩ _ hx0 hdX
  have hY := hterm ⟨L - 2, by omega⟩ _ hx1 hdY
  have hz : 0 ≤ Real.sqrt F * Real.sqrt A * Real.exp κ *
      Real.exp (-κ * (cycDist a (cycPathBlock a j) : ℝ)) := by
    positivity
  calc ∫⁻ ω, ‖blockOf (resolventMat (Hmat g W L ω) E) a (cycPathBlock a j)‖ₑ ^ (p / 2) ∂(μ W L)
      ≤ ∫⁻ ω, (‖blockOf (resolventMat (Hmat g W L ω) E) a a‖ₑ ^ (p / 2) *
            ‖blockOf (resolventMat (pathOp g (gueBlock W (L - 1)
              (windowSample (cycPathBlock a) ω)) 0 0) E) ⟨0, by omega⟩ j‖ₑ ^ (p / 2) +
          ‖blockOf (resolventMat (Hmat g W L ω) E) a a‖ₑ ^ (p / 2) *
            ‖blockOf (resolventMat (pathOp g (gueBlock W (L - 1)
              (windowSample (cycPathBlock a) ω)) 0 0) E) ⟨L - 2, by omega⟩ j‖ₑ ^ (p / 2))
          ∂(μ W L) := lintegral_mono_ae hae
    _ = ∫⁻ ω, ‖blockOf (resolventMat (Hmat g W L ω) E) a a‖ₑ ^ (p / 2) *
            ‖blockOf (resolventMat (pathOp g (gueBlock W (L - 1)
              (windowSample (cycPathBlock a) ω)) 0 0) E) ⟨0, by omega⟩ j‖ₑ ^ (p / 2) ∂(μ W L) +
        ∫⁻ ω, ‖blockOf (resolventMat (Hmat g W L ω) E) a a‖ₑ ^ (p / 2) *
            ‖blockOf (resolventMat (pathOp g (gueBlock W (L - 1)
              (windowSample (cycPathBlock a) ω)) 0 0) E) ⟨L - 2, by omega⟩ j‖ₑ ^ (p / 2)
          ∂(μ W L) := lintegral_add_left (hm1.mul hm2) _
    _ ≤ _ + _ := add_le_add hX hY
    _ = _ := by
      rw [← ENNReal.ofReal_add hz hz]
      congr 1
      ring

/-- (E.16) [eq:c-cycle] at one width `W`, with `u = t/2`:
`𝔼‖G_{ab}‖^u ≤ 2 C_t W^{(B+2)t+2} exp(-(log W/(n₀+1)) ‖a - b‖_L)`. -/
theorem cycle_moment_decay {t B : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hB : 0 < B) {W : ℕ}
    (hW : 1 ≤ W) {g : ℝ} (hg0 : 0 < g) (hgB : g ≤ (W : ℝ) ^ B) {J : Set ℝ} {n₀ : ℕ}
    (hEP : EndpointMomentAt W g J t n₀ ((W : ℝ) ^ (-2 : ℝ))) {L : ℕ} (hL : 3 ≤ L) {E : ℝ}
    (hE : E ∈ J) {a b : Fin L} (hab : a ≠ b) :
    ∫⁻ ω, ‖blockOf (resolventMat (Hmat g W L ω) E) a b‖ₑ ^ (t / 2) ∂(μ W L) ≤
      ENNReal.ofReal (2 * aprioriConst t * (W : ℝ) ^ ((B + 2) * t + 2) *
        Real.exp (-(Real.log W / (n₀ + 1)) * cycDist a b)) := by
  have hw1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hw0 : (0 : ℝ) < W := by linarith
  have hc : 0 < aprioriConst t := cycle_aprioriConst_pos ht1
  have hmB : max 1 g ≤ (W : ℝ) ^ B := max_le (Real.one_le_rpow hw1 hB.le) hgB
  have hn1 : (1 : ℝ) ≤ (n₀ : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg n₀
    linarith
  have hlog : 0 ≤ Real.log W := Real.log_nonneg hw1
  set κ : ℝ := Real.log W / ((n₀ : ℝ) + 1) with hκdef
  have hκ0 : 0 ≤ κ := div_nonneg hlog (by linarith)
  have hκ : κ ≤ Real.log W := div_le_self hlog hn1
  have hPW : (W : ℝ) ^ ((B + 2) * t + 2) = (W : ℝ) ^ ((B + 2) * t) * (W : ℝ) ^ 2 := by
    rw [Real.rpow_add hw0, Real.rpow_two]
  have hs : 0 < (W : ℝ) ^ ((B + 2) * t) := Real.rpow_pos_of_pos hw0 _
  have hP : ∀ x y : Fin (L - 1),
      ∫⁻ ω, ‖blockOf (resolventMat (pathOp g (gueBlock W (L - 1) ω) 0 0) E) x y‖ₑ ^ t
          ∂(μ W (L - 1)) ≤
        ENNReal.ofReal (aprioriConst t * (W : ℝ) ^ ((B + 2) * t + 2) *
          Real.exp (-(2 * κ) * |((x : ℕ) : ℝ) - (y : ℕ)|)) := fun x y => by
    have e1 : 2 * Real.log W / ((n₀ : ℝ) + 1) = 2 * κ := mul_div_assoc _ _ _
    have key := interval_moment_decay ht0 ht1 hB hW hg0 hgB hEP (L - 1) hE x y
    rwa [e1] at key
  refine (cycle_moment_of_path ht0 ht1 hg0.le hL (by positivity) hκ0 hP hab).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hF : Real.sqrt (aprioriConst t * (max 1 g * (W : ℝ) ^ 2) ^ t) ≤
      Real.sqrt (aprioriConst t * (W : ℝ) ^ ((B + 2) * t)) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (cycle_X_rpow_le ht0 hw1 hmB) hc.le)
  have hexp : Real.exp κ ≤ W := by
    calc Real.exp κ ≤ Real.exp (Real.log W) := Real.exp_le_exp.mpr hκ
      _ = W := Real.exp_log hw0
  have hsq : Real.sqrt (aprioriConst t * (W : ℝ) ^ ((B + 2) * t)) *
      Real.sqrt (aprioriConst t * (W : ℝ) ^ ((B + 2) * t + 2)) * W =
      aprioriConst t * (W : ℝ) ^ ((B + 2) * t + 2) := by
    rw [hPW, ← mul_assoc, Real.sqrt_mul (by positivity) ((W : ℝ) ^ 2), Real.sqrt_sq hw0.le,
      ← mul_assoc, Real.mul_self_sqrt (by positivity)]
    ring
  have h2 : 2 * Real.sqrt (aprioriConst t * (max 1 g * (W : ℝ) ^ 2) ^ t) *
      Real.sqrt (aprioriConst t * (W : ℝ) ^ ((B + 2) * t + 2)) * Real.exp κ ≤
      2 * aprioriConst t * (W : ℝ) ^ ((B + 2) * t + 2) := by
    calc _ ≤ 2 * Real.sqrt (aprioriConst t * (W : ℝ) ^ ((B + 2) * t)) *
          Real.sqrt (aprioriConst t * (W : ℝ) ^ ((B + 2) * t + 2)) * W := by gcongr
      _ = 2 * (Real.sqrt (aprioriConst t * (W : ℝ) ^ ((B + 2) * t)) *
          Real.sqrt (aprioriConst t * (W : ℝ) ^ ((B + 2) * t + 2)) * W) := by ring
      _ = _ := by rw [hsq]; ring
  exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le

/-- (E.16) [eq:c-cycle] with `n₀ + 1 ≤ C′ 𝔟 log W`: decay `exp(-(1/C′) ‖a - b‖_L / 𝔟)`. -/
theorem cycle_moment_decay_scale {t B b C' : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hB : 0 < B)
    (hb : 0 < b) (hC' : 0 < C') {W : ℕ} (hW : 1 ≤ W) {g : ℝ} (hg0 : 0 < g)
    (hgB : g ≤ (W : ℝ) ^ B) {J : Set ℝ} {n₀ : ℕ} (hn₀ : (n₀ : ℝ) + 1 ≤ C' * b * Real.log W)
    (hEP : EndpointMomentAt W g J t n₀ ((W : ℝ) ^ (-2 : ℝ))) {L : ℕ} (hL : 3 ≤ L) {E : ℝ}
    (hE : E ∈ J) {a c : Fin L} (hac : a ≠ c) :
    ∫⁻ ω, ‖blockOf (resolventMat (Hmat g W L ω) E) a c‖ₑ ^ (t / 2) ∂(μ W L) ≤
      ENNReal.ofReal (2 * aprioriConst t * (W : ℝ) ^ ((B + 2) * t + 2) *
        Real.exp (-(1 / C') * cycDist a c / b)) := by
  refine (cycle_moment_decay ht0 ht1 hB hW hg0 hgB hEP hL hE hac).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ ?_))
  · have hn : (0 : ℝ) < (n₀ : ℝ) + 1 := by positivity
    have hCb : 0 < C' * b := mul_pos hC' hb
    have hL0 : 0 < Real.log W := by
      by_contra hc
      have h0 : Real.log W ≤ 0 := not_lt.mp hc
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hCb.le h0]
    have hrate : 1 / C' / b ≤ Real.log W / ((n₀ : ℝ) + 1) := by
      rw [div_div, div_le_div_iff₀ hCb hn]
      nlinarith
    apply Real.exp_le_exp.mpr
    have hd : (0 : ℝ) ≤ (cycDist a c : ℝ) := Nat.cast_nonneg _
    have e : -(1 / C') * (cycDist a c : ℝ) / b = -(1 / C' / b) * (cycDist a c : ℝ) := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_right hrate hd]
  · have := cycle_aprioriConst_pos ht1
    positivity

end LSBA
