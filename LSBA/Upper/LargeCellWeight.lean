import LSBA.Upper.LargeCells
import LSBA.Transfer.WeightLipschitz

/-!
# Weighted suprema of the cell weight along the scalar direction

(E.13) [uva:eq:weight-audit]: write `v = v° + u e` with `e` the scalar direction of the cell
sample and `u ~ N(0, 1)`. For every fixed exterior configuration and every `|E| ≤ E₀ < 2`,
`𝔼_∘ Σ_ℓ (sup_{I_ℓ} φ)(sup_{u ∈ I_ℓ} K_A(E)^h) ≤ C_h`, `I_ℓ = [ℓ, ℓ+1]`, `φ` the standard Gaussian
density, from (E.12) [uva:eq:sobolev-audit] and the moments of Lemma 7.2
[uvs:lem:transfer-moments].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Block `i` of a cell sample of `n ≥ 1` blocks, read cyclically in `i`. -/
private def lcwSel {n : ℕ} (hn : 1 ≤ n) (i : ℕ) : Fin n := ⟨i % n, Nat.mod_lt _ hn⟩

private lemma lcw_transferProd_congr {W : ℕ} (g : ℝ) (z : ℂ)
    {V V' : ℕ → Matrix (Fin W) (Fin W) ℂ} {n : ℕ} (hV : ∀ j < n, V j = V' j) :
    ∀ j ≤ n, transferProd g z V j = transferProd g z V' j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [transferProd, transferProd, ih (by omega), hV j (by omega)]

/-- The weight of a block sequence depends only on its first `n` blocks. -/
private lemma lcw_transferWeight_congr {g E : ℝ} {W : ℕ} {V V' : ℕ → Matrix (Fin W) (Fin W) ℂ}
    {n : ℕ} (hV : ∀ j < n, V j = V' j) : transferWeight g E V n = transferWeight g E V' n := by
  unfold transferWeight
  congr 1
  funext j
  rw [lcw_transferProd_congr g _ hV j (Nat.lt_succ_iff.mp j.2)]

/-- The weight `K_A` of the cell of `windowJoin (cellWindow a n) w e` is the weight of the blocks
of `w`. -/
private lemma lcw_cellWeight_join (g E : ℝ) {W L n : ℕ} (hn : 1 ≤ n) (hnL : n ≤ L) (a : Fin L)
    (w : Ω W n) (e : {p : Fin L × Fin W × Fin W // p.1 ∉ Set.range (cellWindow a n)} → ℝ) :
    cellWeight g E (windowJoin (cellWindow a n) w e) a n =
      transferWeight g E (fun i => gueBlock W n w (lcwSel hn i)) n := by
  unfold cellWeight
  refine lcw_transferWeight_congr fun j hj => ?_
  have h1 := gueBlock_windowJoin_apply (cellWindow_injective a hnL) w e ⟨j, hj⟩
  have h2 : lcwSel hn j = ⟨j, hj⟩ := Fin.ext (Nat.mod_eq_of_lt hj)
  rw [h2]
  exact h1

/-- Moving the cell sample by `t` along the scalar direction moves the energy of the weight by
`t / (g W √n)`, for `g ≥ 1`. -/
private lemma lcw_cellWeight_line {g : ℝ} (hg : 1 ≤ g) (E : ℝ) {W L n : ℕ} (hn : 1 ≤ n)
    (hnL : n ≤ L) (a : Fin L) (w : Ω W n)
    (e : {p : Fin L × Fin W × Fin W // p.1 ∉ Set.range (cellWindow a n)} → ℝ) (t : ℝ) :
    cellWeight g E (windowJoin (cellWindow a n) (w + t • scalarDir W n univ) e) a n =
      transferWeight g (E - t / ((W : ℝ) * Real.sqrt n) / g)
        (fun i => gueBlock W n w (lcwSel hn i)) n := by
  rw [lcw_cellWeight_join g E hn hnL]
  have hmax : max 1 g = g := max_eq_right hg
  have hfun : (fun i => gueBlock W n (w + t • scalarDir W n univ) (lcwSel hn i)) =
      fun i => gueBlock W n w (lcwSel hn i) +
        ((t / ((W : ℝ) * Real.sqrt n) : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) := by
    funext i
    rw [gueBlock_add_smul_scalarDir]
    simp only [Finset.mem_univ, ite_true, Finset.card_univ, Fintype.card_fin]
  rw [hfun, transferWeight_add_smul_one (by linarith) E _ _ n, hmax]

private lemma lcw_continuous_gueBlock {W L : ℕ} (b : Fin L) :
    Continuous fun ω : Ω W L => gueBlock W L ω b := by
  refine continuous_matrix fun α β => ?_
  simp only [gueBlock, Matrix.of_apply]
  split_ifs <;> fun_prop

private lemma lcw_continuous_kronecker_left {W : ℕ} (P : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous fun V : Matrix (Fin W) (Fin W) ℂ => P ⊗ₖ V := by
  refine continuous_matrix fun i j => ?_
  simp only [Matrix.kroneckerMap_apply]
  exact continuous_const.mul (continuous_id.matrix_elem i.2 j.2)

private lemma lcw_continuous_transferMat {W : ℕ} (g : ℝ) (z : ℂ) :
    Continuous fun V : Matrix (Fin W) (Fin W) ℂ => transferMat g z V := by
  unfold transferMat
  exact continuous_const.sub ((continuous_const_smul _).comp (lcw_continuous_kronecker_left _))

private lemma lcw_continuous_transferInv {W : ℕ} (g : ℝ) (z : ℂ) :
    Continuous fun V : Matrix (Fin W) (Fin W) ℂ => transferInv g z V := by
  unfold transferInv
  exact continuous_const.sub ((continuous_const_smul _).comp (lcw_continuous_kronecker_left _))

private lemma lcw_continuous_prod {W n : ℕ} (hn : 1 ≤ n) (g : ℝ) (z : ℂ) (j : ℕ) :
    Continuous fun w : Ω W n =>
      transferProd g z (fun i => gueBlock W n w (lcwSel hn i)) j := by
  induction j with
  | zero => exact continuous_const
  | succ j ih =>
    exact ((lcw_continuous_transferMat g z).comp (lcw_continuous_gueBlock (lcwSel hn j))).mul ih

private lemma lcw_continuous_prod_inv {W n : ℕ} (hn : 1 ≤ n) (g : ℝ) (z : ℂ) (j : ℕ) :
    Continuous fun w : Ω W n =>
      (transferProd g z (fun i => gueBlock W n w (lcwSel hn i)) j)⁻¹ := by
  induction j with
  | zero => simpa [transferProd] using continuous_const
  | succ j ih =>
    have heq : ∀ w : Ω W n,
        (transferProd g z (fun i => gueBlock W n w (lcwSel hn i)) (j + 1))⁻¹ =
          (transferProd g z (fun i => gueBlock W n w (lcwSel hn i)) j)⁻¹ *
            transferInv g z (gueBlock W n w (lcwSel hn j)) := fun w => by
      rw [transferProd, Matrix.mul_inv_rev, inv_transferMat]
    refine Continuous.congr ?_ fun w => (heq w).symm
    exact ih.mul ((lcw_continuous_transferInv g z).comp (lcw_continuous_gueBlock (lcwSel hn j)))

private lemma lcw_measurable_weight (g E : ℝ) {W n : ℕ} (hn : 1 ≤ n) :
    Measurable fun w : Ω W n => transferWeight g E (fun i => gueBlock W n w (lcwSel hn i)) n := by
  unfold transferWeight
  refine Measurable.iSup fun j => ?_
  exact measurable_const.max
    (((continuous_norm.comp (lcw_continuous_prod hn g _ j)).measurable).max
      ((continuous_norm.comp (lcw_continuous_prod_inv hn g _ j)).measurable))

private lemma lcw_measurable_cellWeight (g E : ℝ) {W L n : ℕ} (hn : 1 ≤ n) (hnL : n ≤ L)
    (a : Fin L) (e : {p : Fin L × Fin W × Fin W // p.1 ∉ Set.range (cellWindow a n)} → ℝ) :
    Measurable fun w : Ω W n => cellWeight g E (windowJoin (cellWindow a n) w e) a n := by
  simp only [lcw_cellWeight_join g E hn hnL a _ e]
  exact lcw_measurable_weight g E hn

/-- The standard Gaussian density at `t` is at most `e^{|s|}` times its value at `s`, for
`|t − s| ≤ 1`. -/
private lemma lcw_gaussian_sup_le (ℓ : ℤ) {s : ℝ} (hs : s ∈ Set.Icc (ℓ : ℝ) (ℓ + 1)) :
    (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (gaussianPDFReal 0 1 t)) ≤
      ENNReal.ofReal (gaussianPDFReal 0 1 s * Real.exp |s|) := by
  refine iSup₂_le fun t ht => ENNReal.ofReal_le_ofReal ?_
  simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨ht1, ht2⟩ := ht
  have hd1 : t - s ≤ 1 := by linarith
  have hd2 : s - t ≤ 1 := by linarith
  rcases abs_cases s with ⟨h, h0⟩ | ⟨h, h0⟩
  · rw [h]
    nlinarith [sq_nonneg (s - t), mul_nonneg h0 (sub_nonneg.2 hd2)]
  · rw [h]
    nlinarith [sq_nonneg (s - t), mul_nonneg (neg_nonneg.2 h0.le) (by linarith : 0 ≤ s - t + 1)]

/-- Change of variables `x = E − α s` in a supremum and an integral over a unit interval. -/
private lemma lcw_affine_sup {F G : ℝ → ℝ≥0∞} {α E : ℝ} (hα : 0 < α) (ℓ : ℤ) {c : ℝ≥0∞}
    (h : (⨆ x ∈ Set.Icc (E - α * (ℓ + 1)) (E - α * (ℓ + 1) + α), F x) ≤
      c * ∫⁻ x in Set.Icc (E - α * (ℓ + 1)) (E - α * (ℓ + 1) + α), G x) :
    (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), F (E - α * t)) ≤
      c * (ENNReal.ofReal α * ∫⁻ s in Set.Icc (ℓ : ℝ) (ℓ + 1), G (E - α * s)) := by
  have himg : (fun s : ℝ => E - α * s) '' Set.Icc (ℓ : ℝ) (ℓ + 1) =
      Set.Icc (E - α * (ℓ + 1)) (E - α * (ℓ + 1) + α) := by
    ext x
    constructor
    · rintro ⟨s, ⟨h1, h2⟩, rfl⟩
      constructor <;> nlinarith
    · rintro ⟨h1, h2⟩
      refine ⟨(E - x) / α, ⟨?_, ?_⟩, ?_⟩
      · rw [le_div_iff₀ hα]
        nlinarith
      · rw [div_le_iff₀ hα]
        nlinarith
      · field_simp
        ring
  have hint : ∫⁻ x in Set.Icc (E - α * (ℓ + 1)) (E - α * (ℓ + 1) + α), G x =
      ENNReal.ofReal α * ∫⁻ s in Set.Icc (ℓ : ℝ) (ℓ + 1), G (E - α * s) := by
    rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc
      (f := fun s : ℝ => E - α * s) (f' := fun _ => -α)]
    · simp only [abs_neg, abs_of_pos hα]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    · intro x _
      exact (((hasDerivAt_id x).const_mul α).const_sub E).hasDerivWithinAt.congr_deriv (by simp)
    · intro x _ y _ hxy
      have : α * x = α * y := by simpa using hxy
      exact mul_left_cancel₀ hα.ne' this
  rw [← hint]
  refine le_trans (iSup₂_le fun t ht => ?_) h
  refine le_iSup₂ (f := fun x _ => F x) (E - α * t) ?_
  obtain ⟨h1, h2⟩ := ht
  constructor <;> nlinarith

/-- The unit intervals `[ℓ, ℓ+1]`, `ℓ ∈ ℤ`, cover `ℝ`, overlapping in null sets. -/
private lemma lcw_tsum_Icc (G : ℝ → ℝ≥0∞) :
    ∑' ℓ : ℤ, ∫⁻ s in Set.Icc (ℓ : ℝ) (ℓ + 1), G s = ∫⁻ s, G s := by
  have h1 : ∀ ℓ : ℤ, ∫⁻ s in Set.Icc (ℓ : ℝ) (ℓ + 1), G s = ∫⁻ s in Set.Ico (ℓ : ℝ) (ℓ + 1), G s :=
    fun ℓ => (setLIntegral_congr Ico_ae_eq_Icc).symm
  simp_rw [h1]
  rw [← lintegral_iUnion (fun ℓ => measurableSet_Ico) (Set.pairwise_disjoint_Ico_intCast ℝ),
    iUnion_Ico_intCast, Measure.restrict_univ]

/-- Integration against the standard Gaussian density. -/
private lemma lcw_lintegral_gaussian {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ s, ENNReal.ofReal (gaussianPDFReal 0 1 s) * G s = ∫⁻ s, G s ∂(gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1) hG]
  rfl

/-- The coordinate of `ω − ⟨ω, e⟩ e + t e` along a unit vector `e` is `t`. -/
private lemma lcw_inner_line {ι : Type*} [Fintype ι] (e : ι → ℝ) (he : ∑ i, e i ^ 2 = 1)
    (ω : ι → ℝ) (t : ℝ) : ∑ i, (ω - (∑ i, ω i * e i) • e + t • e) i * e i = t := by
  have h1 : ∑ i, (ω - (∑ i, ω i * e i) • e + t • e) i * e i =
      ∑ i, ω i * e i - (∑ i, ω i * e i) * ∑ i, e i ^ 2 + t * ∑ i, e i ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h1, he]
  ring

/-- `𝔼 exp (c N) = exp (c² / 2)` for `N ~ N(0, 1)`, as a lower integral. -/
private lemma lcw_lintegral_exp (c : ℝ) :
    ∫⁻ t, ENNReal.ofReal (Real.exp (c * t)) ∂(gaussianReal 0 1) =
      ENNReal.ofReal (Real.exp (c ^ 2 / 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal c)
    (Filter.Eventually.of_forall fun t => (Real.exp_pos _).le)]
  congr 1
  have h := mgf_gaussianReal (X := id) (p := gaussianReal 0 1) (μ := 0) (v := 1)
    (by simp) c
  simp only [mgf, id] at h
  rw [h]
  simp


/-- (E.12) [uva:eq:sobolev-audit] applied on each unit interval along the scalar direction, and
summed: `Σ_ℓ (sup_{I_ℓ} φ)(sup_{u ∈ I_ℓ} K_A^h)` is at most `(1 + h n α) 𝔼 e^{|u|} K_A^{h+4}` with
`α = (g W √n)⁻¹`. -/
private lemma lcw_line_bound {g : ℝ} (hg : 1 ≤ g) (E : ℝ) {W L n : ℕ} (hW : 1 ≤ W) (hn : 1 ≤ n)
    (hnL : n ≤ L) (a : Fin L)
    (e : {p : Fin L × Fin W × Fin W // p.1 ∉ Set.range (cellWindow a n)} → ℝ)
    {h : ℝ} (hh : 0 ≤ h) (w : Ω W n) :
    ∑' ℓ : ℤ, (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (gaussianPDFReal 0 1 t)) *
        (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (cellWeight g E
          (windowJoin (cellWindow a n) (w + t • scalarDir W n univ) e) a n ^ h)) ≤
      ENNReal.ofReal (1 + h * n * (g * W * Real.sqrt n)⁻¹) *
        ∫⁻ s, ENNReal.ofReal (Real.exp |s|) * ENNReal.ofReal (cellWeight g E
          (windowJoin (cellWindow a n) (w + s • scalarDir W n univ) e) a n ^ (h + 4))
          ∂(gaussianReal 0 1) := by
  have hmeas : Measurable fun s : ℝ => ENNReal.ofReal (Real.exp |s|) *
      ENNReal.ofReal (cellWeight g E
        (windowJoin (cellWindow a n) (w + s • scalarDir W n univ) e) a n ^ (h + 4)) :=
    (Real.continuous_exp.comp continuous_abs).measurable.ennreal_ofReal.mul
      (((lcw_measurable_cellWeight g E hn hnL a e).comp
        (measurable_const.add (measurable_id.smul_const _))).pow_const _).ennreal_ofReal
  set V : ℕ → Matrix (Fin W) (Fin W) ℂ := fun i => gueBlock W n w (lcwSel hn i) with hV
  set α : ℝ := (g * W * Real.sqrt n)⁻¹ with hαdef
  have hg0 : 0 < g := by linarith
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hn0 : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hα : 0 < α := by positivity
  have hline : ∀ t : ℝ, cellWeight g E
      (windowJoin (cellWindow a n) (w + t • scalarDir W n univ) e) a n =
        transferWeight g (E - α * t) V n := by
    intro t
    rw [lcw_cellWeight_line hg E hn hnL a w e t]
    congr 2
    rw [hαdef]
    field_simp
  simp only [hline] at hmeas ⊢
  have hB : ∀ ℓ : ℤ, (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1),
      ENNReal.ofReal (transferWeight g (E - α * t) V n ^ h)) ≤
      ENNReal.ofReal (1 + h * n * α) *
        ∫⁻ s in Set.Icc (ℓ : ℝ) (ℓ + 1),
          ENNReal.ofReal (transferWeight g (E - α * s) V n ^ (h + 4)) := by
    intro ℓ
    have h1 := lcw_affine_sup (F := fun x => ENNReal.ofReal (transferWeight g x V n ^ h))
      (G := fun x => ENNReal.ofReal (transferWeight g x V n ^ (h + 4))) (α := α) (E := E) hα ℓ
      (c := ENNReal.ofReal (α⁻¹ + h * n)) (transferWeight_sup_le hg V n hh _ hα)
    refine h1.trans (le_of_eq ?_)
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [add_mul, inv_mul_cancel₀ hα.ne']
  have hper : ∀ ℓ : ℤ, (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (gaussianPDFReal 0 1 t)) *
      (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (transferWeight g (E - α * t) V n ^ h)) ≤
      ENNReal.ofReal (1 + h * n * α) * ∫⁻ s in Set.Icc (ℓ : ℝ) (ℓ + 1),
        ENNReal.ofReal (gaussianPDFReal 0 1 s) * (ENNReal.ofReal (Real.exp |s|) *
          ENNReal.ofReal (transferWeight g (E - α * s) V n ^ (h + 4))) := by
    intro ℓ
    calc _ ≤ (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (gaussianPDFReal 0 1 t)) *
          (ENNReal.ofReal (1 + h * n * α) * ∫⁻ s in Set.Icc (ℓ : ℝ) (ℓ + 1),
            ENNReal.ofReal (transferWeight g (E - α * s) V n ^ (h + 4))) := by
          gcongr
          exact hB ℓ
      _ = ENNReal.ofReal (1 + h * n * α) * ((⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1),
          ENNReal.ofReal (gaussianPDFReal 0 1 t)) * ∫⁻ s in Set.Icc (ℓ : ℝ) (ℓ + 1),
            ENNReal.ofReal (transferWeight g (E - α * s) V n ^ (h + 4))) := by
          rw [mul_left_comm]
      _ ≤ ENNReal.ofReal (1 + h * n * α) * ∫⁻ s in Set.Icc (ℓ : ℝ) (ℓ + 1),
          (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (gaussianPDFReal 0 1 t)) *
            ENNReal.ofReal (transferWeight g (E - α * s) V n ^ (h + 4)) := by
          gcongr
          exact lintegral_const_mul_le _ _
      _ ≤ _ := by
          refine mul_le_mul' le_rfl ?_
          refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
          calc _ ≤ ENNReal.ofReal (gaussianPDFReal 0 1 s * Real.exp |s|) *
                ENNReal.ofReal (transferWeight g (E - α * s) V n ^ (h + 4)) :=
                mul_le_mul' (lcw_gaussian_sup_le ℓ hs) le_rfl
            _ = _ := by
                rw [ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 s), mul_assoc]
  calc _ ≤ ∑' ℓ : ℤ, ENNReal.ofReal (1 + h * n * α) * ∫⁻ s in Set.Icc (ℓ : ℝ) (ℓ + 1),
        ENNReal.ofReal (gaussianPDFReal 0 1 s) * (ENNReal.ofReal (Real.exp |s|) *
          ENNReal.ofReal (transferWeight g (E - α * s) V n ^ (h + 4))) :=
        ENNReal.tsum_le_tsum hper
    _ = ENNReal.ofReal (1 + h * n * α) * ∫⁻ s,
        ENNReal.ofReal (gaussianPDFReal 0 1 s) * (ENNReal.ofReal (Real.exp |s|) *
          ENNReal.ofReal (transferWeight g (E - α * s) V n ^ (h + 4))) := by
        rw [ENNReal.tsum_mul_left, lcw_tsum_Icc]
    _ = _ := by rw [lcw_lintegral_gaussian hmeas]


/-- `e^{|x|} y^{h+4} ≤ e^{2x} + e^{-2x} + y^{2h+8}` for `y ≥ 0`. -/
private lemma lcw_young (x K h : ℝ) (hK : 0 ≤ K) :
    Real.exp |x| * K ^ (h + 4) ≤ Real.exp (2 * x) + Real.exp (-2 * x) + K ^ (2 * h + 8) := by
  have hy : (K ^ (h + 4)) ^ 2 = K ^ (2 * h + 8) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK]
    congr 1
    push_cast
    ring
  have hx : Real.exp |x| ^ 2 ≤ Real.exp (2 * x) + Real.exp (-2 * x) := by
    rw [← Real.exp_nat_mul]
    push_cast
    rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]
      linarith [Real.exp_pos (-2 * x)]
    · rw [h1]
      have : 2 * -x = -2 * x := by ring
      rw [this]
      linarith [Real.exp_pos (2 * x)]
  have hy0 : 0 ≤ K ^ (h + 4) := Real.rpow_nonneg hK _
  have hab : 0 ≤ Real.exp |x| * K ^ (h + 4) := mul_nonneg (Real.exp_pos _).le hy0
  nlinarith [sq_nonneg (Real.exp |x| - K ^ (h + 4))]

private lemma lcw_measurable_inner {ι : Type*} [Fintype ι] (e : ι → ℝ) :
    Measurable fun w : ι → ℝ => ∑ i, w i * e i :=
  Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).mul_const _

/-- `𝔼 exp (c ⟨ω, e⟩) = exp (c² / 2)` under the standard Gaussian, for a unit vector `e`. -/
private lemma lcw_lintegral_exp_line {ι : Type*} [Fintype ι] (e : ι → ℝ) (he : ∑ i, e i ^ 2 = 1)
    (c : ℝ) :
    ∫⁻ w, ENNReal.ofReal (Real.exp (c * ∑ i, w i * e i)) ∂(stdGauss ι) =
      ENNReal.ofReal (Real.exp (c ^ 2 / 2)) := by
  rw [lintegral_stdGauss_line e he
    (F := fun w => ENNReal.ofReal (Real.exp (c * ∑ i, w i * e i)))
    (((Real.continuous_exp.measurable.comp
      ((lcw_measurable_inner e).const_mul c))).ennreal_ofReal)]
  simp only [lcw_inner_line e he, lcw_lintegral_exp, lintegral_const, measure_univ, mul_one]

/-- `𝔼 e^{|⟨v, e⟩|} K_A^{h+4}` is at most `2 e² + 𝔼 K_A^{2h+8}`, for the unit direction `e` of the
cell sample. -/
private lemma lcw_exp_weight_bound {g : ℝ} (E : ℝ) {W L n : ℕ} (hW : 1 ≤ W) (hn : 1 ≤ n)
    (hnL : n ≤ L) (a : Fin L)
    (e : {p : Fin L × Fin W × Fin W // p.1 ∉ Set.range (cellWindow a n)} → ℝ) {h Cm : ℝ}
    (hCm : 0 ≤ Cm)
    (hmom : ∫⁻ w, ENNReal.ofReal (cellWeight g E (windowJoin (cellWindow a n) w e) a n ^
      (2 * h + 8)) ∂(μ W n) ≤ ENNReal.ofReal Cm) :
    ∫⁻ w, ENNReal.ofReal (Real.exp |∑ i, w i * scalarDir W n univ i|) *
      ENNReal.ofReal (cellWeight g E (windowJoin (cellWindow a n) w e) a n ^ (h + 4))
        ∂(μ W n) ≤ ENNReal.ofReal (2 * Real.exp 2 + Cm) := by
  have hsd : ∑ i, scalarDir W n univ i ^ 2 = 1 :=
    sum_sq_scalarDir hW ⟨⟨0, by omega⟩, mem_univ _⟩
  have hX := lcw_measurable_inner (scalarDir W n univ)
  have hcw := lcw_measurable_cellWeight g E hn hnL a e
  have hcw0 : ∀ w : Ω W n, 0 ≤ cellWeight g E (windowJoin (cellWindow a n) w e) a n :=
    fun w => by
      have := (transferWeight_bounds g E (fun j => gueBlock W L (windowJoin (cellWindow a n) w e)
        (cellBlock a j)) n).1
      unfold cellWeight
      linarith
  have hm1 : Measurable fun w : Ω W n =>
      ENNReal.ofReal (Real.exp (2 * ∑ i, w i * scalarDir W n univ i)) :=
    (Real.continuous_exp.measurable.comp (hX.const_mul 2)).ennreal_ofReal
  have hm2 : Measurable fun w : Ω W n =>
      ENNReal.ofReal (Real.exp (-2 * ∑ i, w i * scalarDir W n univ i)) :=
    (Real.continuous_exp.measurable.comp (hX.const_mul (-2))).ennreal_ofReal
  have hpt : ∀ w : Ω W n, ENNReal.ofReal (Real.exp |∑ i, w i * scalarDir W n univ i|) *
      ENNReal.ofReal (cellWeight g E (windowJoin (cellWindow a n) w e) a n ^ (h + 4)) ≤
      (ENNReal.ofReal (Real.exp (2 * ∑ i, w i * scalarDir W n univ i)) +
        ENNReal.ofReal (Real.exp (-2 * ∑ i, w i * scalarDir W n univ i))) +
          ENNReal.ofReal (cellWeight g E (windowJoin (cellWindow a n) w e) a n ^ (2 * h + 8)) := by
    intro w
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine (ENNReal.ofReal_le_ofReal (lcw_young _ _ h (hcw0 w))).trans ?_
    refine ENNReal.ofReal_add_le.trans ?_
    gcongr
    exact ENNReal.ofReal_add_le
  have hμ : μ W n = stdGauss (Fin n × Fin W × Fin W) := rfl
  have h2 : ∫⁻ w, ENNReal.ofReal (Real.exp (2 * ∑ i, w i * scalarDir W n univ i)) ∂(μ W n) =
      ENNReal.ofReal (Real.exp 2) := by
    rw [hμ, lcw_lintegral_exp_line _ hsd 2]
    norm_num
  have h3 : ∫⁻ w, ENNReal.ofReal (Real.exp (-2 * ∑ i, w i * scalarDir W n univ i)) ∂(μ W n) =
      ENNReal.ofReal (Real.exp 2) := by
    rw [hμ, lcw_lintegral_exp_line _ hsd (-2)]
    norm_num
  calc _ ≤ ∫⁻ w, (ENNReal.ofReal (Real.exp (2 * ∑ i, w i * scalarDir W n univ i)) +
        ENNReal.ofReal (Real.exp (-2 * ∑ i, w i * scalarDir W n univ i))) +
          ENNReal.ofReal (cellWeight g E (windowJoin (cellWindow a n) w e) a n ^ (2 * h + 8))
          ∂(μ W n) := lintegral_mono hpt
    _ = (∫⁻ w, ENNReal.ofReal (Real.exp (2 * ∑ i, w i * scalarDir W n univ i)) ∂(μ W n) +
        ∫⁻ w, ENNReal.ofReal (Real.exp (-2 * ∑ i, w i * scalarDir W n univ i)) ∂(μ W n)) +
          ∫⁻ w, ENNReal.ofReal (cellWeight g E (windowJoin (cellWindow a n) w e) a n ^
            (2 * h + 8)) ∂(μ W n) := by
        have hm12 : Measurable fun w : Ω W n =>
            ENNReal.ofReal (Real.exp (2 * ∑ i, w i * scalarDir W n univ i)) +
              ENNReal.ofReal (Real.exp (-2 * ∑ i, w i * scalarDir W n univ i)) := hm1.add hm2
        rw [lintegral_add_left hm12, lintegral_add_left hm1]
    _ ≤ (ENNReal.ofReal (Real.exp 2) + ENNReal.ofReal (Real.exp 2)) + ENNReal.ofReal Cm := by
        rw [h2, h3]
        gcongr
    _ = ENNReal.ofReal (2 * Real.exp 2 + Cm) := by
        have h0 : (0 : ℝ) ≤ Real.exp 2 := (Real.exp_pos _).le
        rw [← ENNReal.ofReal_add h0 h0, ← ENNReal.ofReal_add (by positivity) hCm]
        congr 1
        ring

/-- (E.13) [uva:eq:weight-audit]:
`∫ Σ_ℓ (sup_{I_ℓ} φ)(sup_{u ∈ I_ℓ} K_A(E; v° + u e)^h) dμ(v) ≤ C_h` for `|E| ≤ E₀ < 2`, `h ≥ 0`,
`g ≥ 2/√(2 − E₀)`, `1 ≤ n ≤ 2g²`, `n ≤ L`, uniformly in the exterior configuration. -/
theorem cellWeight_line_average {E₀ : ℝ} (hE₀ : E₀ < 2) {h : ℝ} (hh : 0 ≤ h) :
    ∃ C : ℝ, 0 < C ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, 2 / Real.sqrt (2 - E₀) ≤ g →
      ∀ L n : ℕ, 1 ≤ n → (n : ℝ) ≤ 2 * g ^ 2 → n ≤ L → ∀ a : Fin L, ∀ E : ℝ, |E| ≤ E₀ →
      ∀ e : {p : Fin L × Fin W × Fin W // p.1 ∉ Set.range (cellWindow a n)} → ℝ,
        ∫⁻ v, ∑' ℓ : ℤ,
          (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (gaussianPDFReal 0 1 t)) *
            (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (cellWeight g E
              (windowJoin (cellWindow a n) (v - (∑ i, v i * scalarDir W n univ i) •
                scalarDir W n univ + t • scalarDir W n univ) e) a n ^ h)) ∂(μ W n) ≤
          ENNReal.ofReal C := by
  obtain ⟨Cm, hCm, hmom⟩ :=
    transferWeight_moment (κ := 2 - E₀) (p := 2 * h + 8) (by linarith) (by linarith)
  refine ⟨(1 + 2 * h) * (2 * Real.exp 2 + Cm), by positivity, max 1 ⌈2 * (2 * h + 8)⌉₊, ?_⟩
  intro W hW g hg L n hn hng hnL a E hE e
  have hW1 : 1 ≤ W := le_trans (le_max_left _ _) hW
  have hWp : 2 * (2 * h + 8) ≤ (W : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hW)
  have hE₀0 : 0 ≤ E₀ := le_trans (abs_nonneg E) hE
  have hg1 : 1 ≤ g := by
    have hsq0 : 0 < Real.sqrt (2 - E₀) := Real.sqrt_pos.mpr (by linarith)
    have hsq : Real.sqrt (2 - E₀) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
    exact le_trans ((le_div_iff₀ hsq0).mpr (by linarith)) hg
  have hsd : ∑ i, scalarDir W n univ i ^ 2 = 1 :=
    sum_sq_scalarDir hW1 ⟨⟨0, by omega⟩, mem_univ _⟩
  have hmomE : ∫⁻ w, ENNReal.ofReal (cellWeight g E (windowJoin (cellWindow a n) w e) a n ^
      (2 * h + 8)) ∂(μ W n) ≤ ENNReal.ofReal Cm := by
    simp only [lcw_cellWeight_join g E hn hnL a _ e]
    refine hmom W n hWp (lcwSel hn) n ?_ g hg hng E ?_
    · intro i hi j hj hij
      simp only [Set.mem_Iio] at hi hj
      have := congrArg Fin.val hij
      simpa [lcwSel, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using this
    · have : 2 - (2 - E₀) = E₀ := by ring
      rw [this]
      exact hE
  have hc1 : 1 + h * n * (g * W * Real.sqrt n)⁻¹ ≤ 1 + 2 * h := by
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
    have hg0 : 0 < g := by linarith
    have hsq : Real.sqrt n ≤ 2 * g * W := by
      refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
      nlinarith [mul_nonneg (sq_nonneg g) (sub_nonneg.2 hWr),
        mul_nonneg (sq_nonneg g) (mul_nonneg (sub_nonneg.2 hWr) (sub_nonneg.2 hWr)),
        mul_nonneg (sq_nonneg g) (sq_nonneg (W : ℝ))]
    have hnr : (n : ℝ) * (g * W * Real.sqrt n)⁻¹ ≤ 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hsq hsn.le
      nlinarith [Real.mul_self_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have : h * n * (g * W * Real.sqrt n)⁻¹ ≤ h * 2 := by
      calc h * n * (g * W * Real.sqrt n)⁻¹ = h * ((n : ℝ) * (g * W * Real.sqrt n)⁻¹) := by ring
        _ ≤ h * 2 := mul_le_mul_of_nonneg_left hnr hh
    linarith
  set F : Ω W n → ℝ≥0∞ := fun w => ENNReal.ofReal (Real.exp |∑ i, w i * scalarDir W n univ i|) *
    ENNReal.ofReal (cellWeight g E (windowJoin (cellWindow a n) w e) a n ^ (h + 4)) with hF
  have hFm : Measurable F :=
    ((Real.continuous_exp.measurable.comp
      (lcw_measurable_inner (scalarDir W n univ)).abs).ennreal_ofReal).mul
      (((lcw_measurable_cellWeight g E hn hnL a e).pow_const _).ennreal_ofReal)
  have hμ : μ W n = stdGauss (Fin n × Fin W × Fin W) := rfl
  calc _ ≤ ∫⁻ v, ENNReal.ofReal (1 + h * n * (g * W * Real.sqrt n)⁻¹) *
        ∫⁻ s, F (v - (∑ i, v i * scalarDir W n univ i) • scalarDir W n univ +
          s • scalarDir W n univ) ∂(gaussianReal 0 1) ∂(μ W n) := by
        refine lintegral_mono fun v => ?_
        refine (lcw_line_bound hg1 E hW1 hn hnL a e hh
          (v - (∑ i, v i * scalarDir W n univ i) • scalarDir W n univ)).trans ?_
        refine mul_le_mul' le_rfl (le_of_eq ?_)
        refine lintegral_congr fun s => ?_
        simp only [hF, lcw_inner_line _ hsd v s]
    _ = ENNReal.ofReal (1 + h * n * (g * W * Real.sqrt n)⁻¹) *
        ∫⁻ v, ∫⁻ s, F (v - (∑ i, v i * scalarDir W n univ i) • scalarDir W n univ +
          s • scalarDir W n univ) ∂(gaussianReal 0 1) ∂(μ W n) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (1 + h * n * (g * W * Real.sqrt n)⁻¹) * ∫⁻ w, F w ∂(μ W n) := by
        rw [hμ, ← lintegral_stdGauss_line _ hsd hFm]
    _ ≤ ENNReal.ofReal (1 + 2 * h) * ENNReal.ofReal (2 * Real.exp 2 + Cm) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hc1)
          (lcw_exp_weight_bound E hW1 hn hnL a e hCm.le hmomE)
    _ = ENNReal.ofReal ((1 + 2 * h) * (2 * Real.exp 2 + Cm)) :=
        (ENNReal.ofReal_mul (by linarith)).symm

end LSBA
