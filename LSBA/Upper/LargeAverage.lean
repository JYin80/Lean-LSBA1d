import LSBA.Upper.LargeCellCross
import LSBA.Upper.LargeCellWeight
import LSBA.Spectral.LineArea

/-!
# Weighted averaging over one cell

The Claim (E.6) [uva:eq:average] in the proof of Lemma 8.1(ii) [uva:thm:upper-audit], for every
power `r ≥ 0` of `K_A` (the paper has `r = 1`): for `E₀ < 2`, `r ≥ 0`, large `W`,
`g ≥ 2/√(2 − E₀)` and a cell `A` of `n` consecutive blocks with `2 ≤ n`, `g²/2 ≤ n ≤ 2g²` and
`n < L`, `𝔼_A Σ_{λ_k ∈ J} m_A(k) K_A(λ_k)^r f(λ_k) ≤ C_r n W² ∫_J f(E) dE` for every fixed exterior
configuration and every measurable `f ≥ 0`; and the same bound integrated over the exterior for
`f(E, H_{A^c})` depending only on the exterior blocks.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Block `i` of a cell sample of `n ≥ 1` blocks, read cyclically in `i`. -/
private def lavSel {n : ℕ} (hn : 1 ≤ n) (i : ℕ) : Fin n := ⟨i % n, Nat.mod_lt _ hn⟩

private lemma lav_transferProd_congr {W : ℕ} (g : ℝ) (z : ℂ)
    {V V' : ℕ → Matrix (Fin W) (Fin W) ℂ} {n : ℕ} (hV : ∀ j < n, V j = V' j) :
    ∀ j ≤ n, transferProd g z V j = transferProd g z V' j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [transferProd, transferProd, ih (by omega), hV j (by omega)]

/-- The weight of a block sequence depends only on its first `n` blocks. -/
private lemma lav_transferWeight_congr {g E : ℝ} {W : ℕ} {V V' : ℕ → Matrix (Fin W) (Fin W) ℂ}
    {n : ℕ} (hV : ∀ j < n, V j = V' j) : transferWeight g E V n = transferWeight g E V' n := by
  unfold transferWeight
  congr 1
  funext j
  rw [lav_transferProd_congr g _ hV j (Nat.lt_succ_iff.mp j.2)]

/-- The weight `K_A` of the cell of `windowJoin (cellWindow a n) w e` is the weight of the blocks
of `w`. -/
private lemma lav_cellWeight_join (g E : ℝ) {W L n : ℕ} (hn : 1 ≤ n) (hnL : n ≤ L) (a : Fin L)
    (w : Ω W n) (e : {p : Fin L × Fin W × Fin W // p.1 ∉ Set.range (cellWindow a n)} → ℝ) :
    cellWeight g E (windowJoin (cellWindow a n) w e) a n =
      transferWeight g E (fun i => gueBlock W n w (lavSel hn i)) n := by
  unfold cellWeight
  refine lav_transferWeight_congr fun j hj => ?_
  have h1 := gueBlock_windowJoin_apply (cellWindow_injective a hnL) w e ⟨j, hj⟩
  have h2 : lavSel hn j = ⟨j, hj⟩ := Fin.ext (Nat.mod_eq_of_lt hj)
  rw [h2]
  exact h1

/-- Moving the cell sample by `t` along the scalar direction moves the energy of the weight by
`t / (g W √n)`, for `g ≥ 1`. -/
private lemma lav_cellWeight_line {g : ℝ} (hg : 1 ≤ g) (E : ℝ) {W L n : ℕ} (hn : 1 ≤ n)
    (hnL : n ≤ L) (a : Fin L) (w : Ω W n)
    (e : {p : Fin L × Fin W × Fin W // p.1 ∉ Set.range (cellWindow a n)} → ℝ) (t : ℝ) :
    cellWeight g E (windowJoin (cellWindow a n) (w + t • scalarDir W n univ) e) a n =
      transferWeight g (E - t / ((W : ℝ) * Real.sqrt n) / g)
        (fun i => gueBlock W n w (lavSel hn i)) n := by
  rw [lav_cellWeight_join g E hn hnL]
  have hmax : max 1 g = g := max_eq_right hg
  have hfun : (fun i => gueBlock W n (w + t • scalarDir W n univ) (lavSel hn i)) =
      fun i => gueBlock W n w (lavSel hn i) +
        ((t / ((W : ℝ) * Real.sqrt n) : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) := by
    funext i
    rw [gueBlock_add_smul_scalarDir]
    simp only [Finset.mem_univ, ite_true, Finset.card_univ, Fintype.card_fin]
  rw [hfun, transferWeight_add_smul_one (by linarith) E _ _ n, hmax]

private lemma lav_continuous_gueBlock {W L : ℕ} (b : Fin L) :
    Continuous fun ω : Ω W L => gueBlock W L ω b := by
  refine continuous_matrix fun α β => ?_
  simp only [gueBlock, Matrix.of_apply]
  split_ifs <;> fun_prop

private lemma lav_continuous_windowJoin {W L q : ℕ} (s : Fin q → Fin L)
    (e : {p : Fin L × Fin W × Fin W // p.1 ∉ Set.range s} → ℝ) :
    Continuous fun v : Ω W q => windowJoin s v e := by
  refine continuous_pi fun p => ?_
  by_cases h : p.1 ∈ Set.range s
  · simp only [windowJoin, h, ↓reduceDIte]
    exact continuous_apply _
  · simp only [windowJoin, h, ↓reduceDIte]
    exact continuous_const

private lemma lav_continuous_kronecker {X : Type*} [TopologicalSpace X] {W : ℕ}
    {P : X → Matrix (Fin 2) (Fin 2) ℂ} (hP : Continuous P)
    {V : X → Matrix (Fin W) (Fin W) ℂ} (hV : Continuous V) :
    Continuous fun x => P x ⊗ₖ V x := by
  refine continuous_matrix fun i j => ?_
  simp only [Matrix.kroneckerMap_apply]
  exact (hP.matrix_elem i.1 j.1).mul (hV.matrix_elem i.2 j.2)

private lemma lav_continuous_transferMat {X : Type*} [TopologicalSpace X] {W : ℕ} (g : ℝ)
    {z : X → ℂ} (hz : Continuous z) {V : X → Matrix (Fin W) (Fin W) ℂ} (hV : Continuous V) :
    Continuous fun x => transferMat g (z x) (V x) := by
  unfold transferMat transferFree
  have hP : (fun x => !![z x, -1; 1, 0]) =
      fun x => z x • !![1, 0; 0, 0] + !![0, -1; 1, (0 : ℂ)] := by
    funext x
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine (lav_continuous_kronecker ?_ continuous_const).sub
    ((continuous_const_smul _).comp (lav_continuous_kronecker continuous_const hV))
  rw [hP]
  exact (hz.smul continuous_const).add continuous_const

private lemma lav_continuous_transferInv {X : Type*} [TopologicalSpace X] {W : ℕ} (g : ℝ)
    {z : X → ℂ} (hz : Continuous z) {V : X → Matrix (Fin W) (Fin W) ℂ} (hV : Continuous V) :
    Continuous fun x => transferInv g (z x) (V x) := by
  unfold transferInv
  have hP : (fun x => !![0, 1; -1, z x]) =
      fun x => z x • !![0, 0; 0, 1] + !![0, 1; -1, (0 : ℂ)] := by
    funext x
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine (lav_continuous_kronecker ?_ continuous_const).sub
    ((continuous_const_smul _).comp (lav_continuous_kronecker continuous_const hV))
  rw [hP]
  exact (hz.smul continuous_const).add continuous_const

private lemma lav_continuous_prod {X : Type*} [TopologicalSpace X] {W : ℕ} (g : ℝ)
    {z : X → ℂ} (hz : Continuous z) {V : ℕ → X → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ i, Continuous (V i)) (j : ℕ) :
    Continuous fun x => transferProd g (z x) (fun i => V i x) j := by
  induction j with
  | zero => exact continuous_const
  | succ j ih => exact (lav_continuous_transferMat g hz (hV j)).mul ih

private lemma lav_continuous_prod_inv {X : Type*} [TopologicalSpace X] {W : ℕ} (g : ℝ)
    {z : X → ℂ} (hz : Continuous z) {V : ℕ → X → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ i, Continuous (V i)) (j : ℕ) :
    Continuous fun x => (transferProd g (z x) (fun i => V i x) j)⁻¹ := by
  induction j with
  | zero => simpa [transferProd] using continuous_const
  | succ j ih =>
    have heq : ∀ x, (transferProd g (z x) (fun i => V i x) (j + 1))⁻¹ =
        (transferProd g (z x) (fun i => V i x) j)⁻¹ * transferInv g (z x) (V j x) := fun x => by
      rw [transferProd, Matrix.mul_inv_rev, inv_transferMat]
    refine Continuous.congr ?_ fun x => (heq x).symm
    exact ih.mul (lav_continuous_transferInv g hz (hV j))

/-- `K^h` is the maximum over `j ≤ n` of `max{1, ‖F_j‖, ‖F_j⁻¹‖}^h`. -/
private lemma lav_ofReal_weight_rpow (g E : ℝ) {W : ℕ} (V : ℕ → Matrix (Fin W) (Fin W) ℂ)
    (n : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    ENNReal.ofReal (transferWeight g E V n ^ h) =
      ⨆ j : Fin (n + 1), ENNReal.ofReal (max 1 (max ‖transferProd g ((max 1 g * E / g : ℝ) : ℂ) V j‖
        ‖(transferProd g ((max 1 g * E / g : ℝ) : ℂ) V j)⁻¹‖) ^ h) := by
  unfold transferWeight
  set m : Fin (n + 1) → ℝ := fun j => max 1 (max ‖transferProd g ((max 1 g * E / g : ℝ) : ℂ) V j‖
    ‖(transferProd g ((max 1 g * E / g : ℝ) : ℂ) V j)⁻¹‖) with hm
  obtain ⟨j₀, hj₀⟩ := exists_eq_ciSup_of_finite (f := m)
  rw [← hj₀]
  refine le_antisymm (le_iSup_of_le j₀ le_rfl) (iSup_le fun j => ?_)
  refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (le_trans zero_le_one (le_max_left _ _)) ?_ hh)
  rw [hj₀]
  exact le_ciSup (Finite.bddAbove_range m) j

/-- `x ↦ K_A(E(x); ω(x))^h` is lower semicontinuous for continuous `E` and `ω`. -/
private lemma lav_lsc_cellWeight {X : Type*} [TopologicalSpace X] (g : ℝ) {E : X → ℝ}
    (hE : Continuous E) {W L : ℕ} {ω : X → Ω W L} (hω : Continuous ω) (a : Fin L) (n : ℕ)
    {h : ℝ} (hh : 0 ≤ h) :
    LowerSemicontinuous fun x => ENNReal.ofReal (cellWeight g (E x) (ω x) a n ^ h) := by
  unfold cellWeight
  simp only [lav_ofReal_weight_rpow _ _ _ _ hh]
  refine lowerSemicontinuous_iSup fun j => Continuous.lowerSemicontinuous ?_
  have hz : Continuous fun x => ((max 1 g * E x / g : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((continuous_const.mul hE).div_const _)
  have hV : ∀ i, Continuous fun x => gueBlock W L (ω x) (cellBlock a i) :=
    fun i => (lav_continuous_gueBlock _).comp hω
  refine ENNReal.continuous_ofReal.comp (Continuous.rpow_const ?_ fun _ => Or.inr hh)
  exact continuous_const.max ((continuous_norm.comp (lav_continuous_prod g hz hV j)).max
    (continuous_norm.comp (lav_continuous_prod_inv g hz hV j)))

private lemma lav_measurable_cellWeight {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (g : ℝ) {E : X → ℝ} (hE : Continuous E) {W L : ℕ} {ω : X → Ω W L}
    (hω : Continuous ω) (a : Fin L) (n : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    Measurable fun x => ENNReal.ofReal (cellWeight g (E x) (ω x) a n ^ h) :=
  (lav_lsc_cellWeight g hE hω a n hh).measurable

/-- Joint measurability of the weighted integrand `1_J(E) K_A(E)^r F`. -/
private lemma lav_measurable_integrand {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (g : ℝ) {J : Set ℝ} (hJ : MeasurableSet J) {E : X → ℝ}
    (hE : Continuous E) {W L : ℕ} {ω : X → Ω W L} (hω : Continuous ω) (a : Fin L) (n : ℕ)
    {r : ℝ} (hr : 0 ≤ r) {F : X → ℝ≥0∞} (hF : Measurable F) :
    Measurable fun x => if E x ∈ J then ENNReal.ofReal (cellWeight g (E x) (ω x) a n ^ r) * F x
      else 0 :=
  Measurable.ite (hE.measurable hJ) ((lav_measurable_cellWeight g hE hω a n hr).mul hF)
    measurable_const

/-- The zeros of `E ↦ det(M − E)` on the real line form a finite set. -/
private lemma lav_finite_det {N : Type*} [Fintype N] [DecidableEq N] (M : Matrix N N ℂ) :
    {E : ℝ | (M - (E : ℂ) • (1 : Matrix N N ℂ)).det = 0}.Finite := by
  have hp : M.charpoly ≠ 0 := M.charpoly_monic.ne_zero
  refine ((Polynomial.finite_setOfPred_isRoot hp).preimage
    Complex.ofReal_injective.injOn).subset fun E hE => ?_
  simp only [Set.mem_ofPred_eq] at hE
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Polynomial.IsRoot.def, Matrix.eval_charpoly]
  have h : Matrix.scalar N (E : ℂ) - M = -(M - (E : ℂ) • (1 : Matrix N N ℂ)) := by
    rw [neg_sub, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
  rw [h, Matrix.det_neg, hE, mul_zero]

private lemma lav_mul_eigMassSum {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (T : Finset ι) (G : ℝ → ℝ≥0∞) (c : ℝ≥0∞) :
    c * eigMassSum A T G = eigMassSum A T (fun E => c * G E) := by
  unfold eigMassSum
  split_ifs
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  · rw [mul_zero]

private lemma lav_eigMassSum_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (T : Finset ι) : eigMassSum A T (fun _ => 0) = 0 := by
  unfold eigMassSum
  split_ifs <;> simp

/-- Integration against the standard Gaussian density. -/
private lemma lav_lintegral_gaussian {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ s, ENNReal.ofReal (gaussianPDFReal 0 1 s) * G s = ∫⁻ s, G s ∂(gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1) hG]
  rfl

/-- `x² y^r ≤ max{x, y}^{r+2}` for `x, y ≥ 1`, `r ≥ 0`. -/
private lemma lav_sq_mul_rpow_le {x y r : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hr : 0 ≤ r) :
    x ^ 2 * y ^ r ≤ x ^ (r + 2) ∨ x ^ 2 * y ^ r ≤ y ^ (r + 2) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  rw [Real.rpow_add hx0, Real.rpow_add hy0, Real.rpow_two, Real.rpow_two]
  rcases le_total x y with h | h
  · right
    rw [mul_comm (y ^ r)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx0.le h 2) (Real.rpow_nonneg hy0.le r)
  · left
    rw [mul_comm (x ^ r)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hy0.le h hr) (pow_nonneg hx0.le 2)

/-- `(sup_I K²)(sup_I K^r) ≤ sup_I K^{r+2}` for `K ≥ 1`, `r ≥ 0`. -/
private lemma lav_iSup_mul_le {I : Set ℝ} {K : ℝ → ℝ} (hK : ∀ u, 1 ≤ K u) {r : ℝ} (hr : 0 ≤ r) :
    (⨆ u ∈ I, ENNReal.ofReal (K u ^ 2)) * (⨆ u ∈ I, ENNReal.ofReal (K u ^ r)) ≤
      ⨆ u ∈ I, ENNReal.ofReal (K u ^ (r + 2)) := by
  have key : ∀ x ∈ I, ∀ y ∈ I, ENNReal.ofReal (K x ^ 2) * ENNReal.ofReal (K y ^ r) ≤
      ⨆ u ∈ I, ENNReal.ofReal (K u ^ (r + 2)) := by
    intro x hx y hy
    rw [← ENNReal.ofReal_mul (pow_nonneg (le_trans zero_le_one (hK x)) 2)]
    rcases lav_sq_mul_rpow_le (hK x) (hK y) hr with h | h
    · exact le_iSup₂_of_le (f := fun t (_ : t ∈ I) => ENNReal.ofReal (K t ^ (r + 2))) x hx
        (ENNReal.ofReal_le_ofReal h)
    · exact le_iSup₂_of_le (f := fun t (_ : t ∈ I) => ENNReal.ofReal (K t ^ (r + 2))) y hy
        (ENNReal.ofReal_le_ofReal h)
  simp only [ENNReal.iSup_mul, ENNReal.mul_iSup]
  exact iSup₂_le fun x hx => iSup₂_le fun y hy => key _ ‹_› _ ‹_›

/-- (E.11) [uva:eq:cross-audit] inserted in the right side of (E.7) [uva:eq:coarea-audit] along
the scalar line of the cell, for `E` off the spectrum of the exterior: the sum over the unit
intervals is at most `(2 + 2√2) W 1_J(E) f(E) Σ_ℓ (sup_{I_ℓ} φ)(sup_{u ∈ I_ℓ} K_A(E)^{r+2})`. -/
private lemma lav_pointwise {g : ℝ} (hg : 1 ≤ g) {W L n : ℕ} (hW : 1 ≤ W) (hn : 2 ≤ n)
    (hnL : n < L) (hng : (n : ℝ) ≤ 2 * g ^ 2) (a : Fin L) (w : Ω W n)
    (e : {p : Fin L × Fin W × Fin W // p.1 ∉ Set.range (cellWindow a n)} → ℝ)
    {r : ℝ} (hr : 0 ≤ r) (J : Set ℝ) (f : ℝ → ℝ≥0∞) {E : ℝ}
    (hE : (pathOp g (fun j : Fin (L - n) =>
      gueBlock W L (windowJoin (cellWindow a n) w e) (cellBlock a (n + j))) 0 0 -
      (E : ℂ) • (1 : Matrix (Fin (L - n) × Fin W) (Fin (L - n) × Fin W) ℂ)).det ≠ 0) :
    ∑' ℓ : ℤ, crossCount (fun u => Hmat g W L (windowJoin (cellWindow a n) w e) +
        (((g * W * Real.sqrt n)⁻¹ * u : ℝ) : ℂ) • coordProj (cellCoords a n)) E
        (Set.Icc (ℓ : ℝ) (ℓ + 1)) *
      (⨆ u ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (gaussianPDFReal 0 1 u) *
        J.indicator (fun E => ENNReal.ofReal (cellWeight g E
          (windowJoin (cellWindow a n) (w + u • scalarDir W n univ) e) a n ^ r) * f E) E) ≤
    ENNReal.ofReal ((2 + 2 * Real.sqrt 2) * W) * J.indicator (fun E => f E *
      ∑' ℓ : ℤ, (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (gaussianPDFReal 0 1 t)) *
        (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (cellWeight g E
          (windowJoin (cellWindow a n) (w + t • scalarDir W n univ) e) a n ^ (r + 2)))) E := by
  by_cases hEJ : E ∉ J
  · simp [Set.indicator_of_notMem hEJ]
  rw [not_not] at hEJ
  set c : ℝ := (g * W * Real.sqrt n)⁻¹ with hc
  have hg0 : 0 < g := by linarith
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hc0 : 0 < c := by positivity
  have hK1 : ∀ u : ℝ, 1 ≤ cellWeight g E
      (windowJoin (cellWindow a n) (w + u • scalarDir W n univ) e) a n :=
    fun u => (transferWeight_bounds _ _ _ _).1
  have hline : ∀ u : ℝ, transferWeight g (E - c * u)
      (fun j => gueBlock W L (windowJoin (cellWindow a n) w e) (cellBlock a j)) n =
        cellWeight g E (windowJoin (cellWindow a n) (w + u • scalarDir W n univ) e) a n := by
    intro u
    have h1 : transferWeight g (E - c * u)
        (fun j => gueBlock W L (windowJoin (cellWindow a n) w e) (cellBlock a j)) n =
          cellWeight g (E - c * u) (windowJoin (cellWindow a n) w e) a n := rfl
    rw [h1, lav_cellWeight_join _ _ (by omega : 1 ≤ n) hnL.le,
      lav_cellWeight_line hg E (by omega : 1 ≤ n) hnL.le]
    congr 2
    rw [hc]
    field_simp
  have hkey : (n : ℝ) ≤ Real.sqrt 2 * g * Real.sqrt n := by
    have h1 : Real.sqrt n ≤ Real.sqrt 2 * g := by
      refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
      exact hng
    have h2 : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
    nlinarith
  have hcn : 2 * c * n * W ≤ 2 * Real.sqrt 2 * W := by
    have h1 : c * n ≤ Real.sqrt 2 := by
      rw [hc, inv_mul_le_iff₀ (by positivity)]
      have h2 : Real.sqrt 2 * g * Real.sqrt n ≤ Real.sqrt 2 * g * Real.sqrt n * W :=
        le_mul_of_one_le_right (by positivity) (by exact_mod_cast hW)
      nlinarith
    nlinarith
  rw [Set.indicator_of_mem hEJ, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun ℓ => ?_
  simp only [Set.indicator_of_mem hEJ]
  have hcc := cell_crossCount_le hg hn hnL (gueBlock W L (windowJoin (cellWindow a n) w e))
    (fun b => gueBlock_isHermitian _ _ _ b) a hc0 hE ℓ
  simp only [hline] at hcc
  have hℓ : (ℓ : ℝ) ∈ Set.Icc (ℓ : ℝ) (ℓ + 1) := ⟨le_rfl, by linarith⟩
  have hS2 : 1 ≤ ⨆ u ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (cellWeight g E
      (windowJoin (cellWindow a n) (w + u • scalarDir W n univ) e) a n ^ 2) :=
    le_iSup₂_of_le (ℓ : ℝ) hℓ (ENNReal.one_le_ofReal.mpr (one_le_pow₀ (hK1 _)))
  have hcc' : crossCount (fun u => Hmat g W L (windowJoin (cellWindow a n) w e) +
      ((c * u : ℝ) : ℂ) • coordProj (cellCoords a n)) E (Set.Icc (ℓ : ℝ) (ℓ + 1)) ≤
      ENNReal.ofReal ((2 + 2 * Real.sqrt 2) * W) *
        ⨆ u ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (cellWeight g E
          (windowJoin (cellWindow a n) (w + u • scalarDir W n univ) e) a n ^ 2) := by
    refine le_trans hcc (le_trans (add_le_add (le_mul_of_one_le_right' hS2)
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal hcn) _)) (le_of_eq ?_))
    rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 2
    ring
  have hsup : (⨆ u ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (gaussianPDFReal 0 1 u) *
      (ENNReal.ofReal (cellWeight g E
        (windowJoin (cellWindow a n) (w + u • scalarDir W n univ) e) a n ^ r) * f E)) ≤
      (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (gaussianPDFReal 0 1 t)) *
        ((⨆ u ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (cellWeight g E
          (windowJoin (cellWindow a n) (w + u • scalarDir W n univ) e) a n ^ r)) * f E) :=
    iSup₂_le fun u hu => mul_le_mul'
      (le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1)) =>
        ENNReal.ofReal (gaussianPDFReal 0 1 t)) u hu)
      (mul_le_mul_left (le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1)) =>
        ENNReal.ofReal (cellWeight g E
          (windowJoin (cellWindow a n) (w + t • scalarDir W n univ) e) a n ^ r)) u hu) _)
  have hmul : (⨆ u ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (cellWeight g E
        (windowJoin (cellWindow a n) (w + u • scalarDir W n univ) e) a n ^ 2)) *
      (⨆ u ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (cellWeight g E
        (windowJoin (cellWindow a n) (w + u • scalarDir W n univ) e) a n ^ r)) ≤
      ⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (cellWeight g E
        (windowJoin (cellWindow a n) (w + t • scalarDir W n univ) e) a n ^ (r + 2)) :=
    lav_iSup_mul_le (K := fun u => cellWeight g E
      (windowJoin (cellWindow a n) (w + u • scalarDir W n univ) e) a n) hK1 hr
  calc _ ≤ (ENNReal.ofReal ((2 + 2 * Real.sqrt 2) * W) *
        ⨆ u ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (cellWeight g E
          (windowJoin (cellWindow a n) (w + u • scalarDir W n univ) e) a n ^ 2)) *
        ((⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (gaussianPDFReal 0 1 t)) *
        ((⨆ u ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (cellWeight g E
          (windowJoin (cellWindow a n) (w + u • scalarDir W n univ) e) a n ^ r)) * f E)) :=
        mul_le_mul' hcc' hsup
    _ = ENNReal.ofReal ((2 + 2 * Real.sqrt 2) * W) * (f E *
        ((⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (gaussianPDFReal 0 1 t)) *
        ((⨆ u ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (cellWeight g E
          (windowJoin (cellWindow a n) (w + u • scalarDir W n univ) e) a n ^ 2)) *
        (⨆ u ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (cellWeight g E
          (windowJoin (cellWindow a n) (w + u • scalarDir W n univ) e) a n ^ r))))) := by ring
    _ ≤ _ := by gcongr

/-- The integrand of (E.6) [uva:eq:average] at a fixed exterior configuration is measurable in the
cell sample. -/
private lemma lav_measurable_fixed (g : ℝ) {W L n : ℕ} (a : Fin L)
    (e : {p : Fin L × Fin W × Fin W // p.1 ∉ Set.range (cellWindow a n)} → ℝ) {r : ℝ}
    (hr : 0 ≤ r) {J : Set ℝ} (hJ : MeasurableSet J) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun v : Ω W n => eigMassSum (Hmat g W L (windowJoin (cellWindow a n) v e))
      (cellCoords a n) (J.indicator fun E => ENNReal.ofReal
        (cellWeight g E (windowJoin (cellWindow a n) v e) a n ^ r) * f E) := by
  have hG : Measurable fun x : Ω W n × ℝ => J.indicator (fun E => ENNReal.ofReal
      (cellWeight g E (windowJoin (cellWindow a n) x.1 e) a n ^ r) * f E) x.2 := by
    simp only [Set.indicator_apply]
    exact lav_measurable_integrand g hJ continuous_snd
      ((lav_continuous_windowJoin _ e).comp continuous_fst) a n hr (hf.comp measurable_snd)
  exact measurable_eigMassSum (A := fun v : Ω W n => Hmat g W L (windowJoin (cellWindow a n) v e))
    ((continuous_Hmat g W L).comp (lav_continuous_windowJoin _ e)).measurable (cellCoords a n)
    (G := fun v E => J.indicator (fun E => ENNReal.ofReal
      (cellWeight g E (windowJoin (cellWindow a n) v e) a n ^ r) * f E) E) hG

/-- (E.7) [uva:eq:coarea-audit] and (E.11) [uva:eq:cross-audit] along the scalar line through `w`:
`𝔼_u Σ_{λ_k ∈ J} m_A(k) K_A(λ_k)^r f(λ_k) ≤ g W √n (2 + 2√2) W ∫_J f(E) Σ_ℓ (sup_{I_ℓ} φ)
(sup_{u ∈ I_ℓ} K_A(E)^{r+2}) dE`, `u ~ N(0, 1)`. -/
private lemma lav_line_bound {g : ℝ} (hg : 1 ≤ g) {W L n : ℕ} (hW : 1 ≤ W) (hn : 2 ≤ n)
    (hnL : n < L) (hng : (n : ℝ) ≤ 2 * g ^ 2) (a : Fin L) (w : Ω W n)
    (e : {p : Fin L × Fin W × Fin W // p.1 ∉ Set.range (cellWindow a n)} → ℝ)
    {r : ℝ} (hr : 0 ≤ r) {J : Set ℝ} (hJ : MeasurableSet J) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ t, eigMassSum (Hmat g W L (windowJoin (cellWindow a n) (w + t • scalarDir W n univ) e))
        (cellCoords a n) (J.indicator fun E => ENNReal.ofReal (cellWeight g E
          (windowJoin (cellWindow a n) (w + t • scalarDir W n univ) e) a n ^ r) * f E)
        ∂(gaussianReal 0 1) ≤
      ENNReal.ofReal (g * W * Real.sqrt n) * ENNReal.ofReal ((2 + 2 * Real.sqrt 2) * W) *
        ∫⁻ E, J.indicator (fun E => f E *
          ∑' ℓ : ℤ, (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (gaussianPDFReal 0 1 t)) *
            (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (cellWeight g E
              (windowJoin (cellWindow a n) (w + t • scalarDir W n univ) e) a n ^ (r + 2)))) E := by
  have hg0 : 0 < g := by linarith
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hc0 : 0 < (g * W * Real.sqrt n)⁻¹ := by positivity
  have hF := lav_measurable_fixed (L := L) g a e hr hJ hf
  have hFt : Measurable fun t : ℝ => eigMassSum
      (Hmat g W L (windowJoin (cellWindow a n) (w + t • scalarDir W n univ) e))
      (cellCoords a n) (J.indicator fun E => ENNReal.ofReal (cellWeight g E
        (windowJoin (cellWindow a n) (w + t • scalarDir W n univ) e) a n ^ r) * f E) :=
    hF.comp (measurable_const.add (measurable_id.smul_const _))
  have hGl : Measurable (Function.uncurry fun E u => ENNReal.ofReal (gaussianPDFReal 0 1 u) *
      J.indicator (fun E => ENNReal.ofReal (cellWeight g E
        (windowJoin (cellWindow a n) (w + u • scalarDir W n univ) e) a n ^ r) * f E) E) := by
    have h2 : Measurable fun x : ℝ × ℝ => J.indicator (fun E => ENNReal.ofReal (cellWeight g E
        (windowJoin (cellWindow a n) (w + x.2 • scalarDir W n univ) e) a n ^ r) * f E) x.1 := by
      simp only [Set.indicator_apply]
      exact lav_measurable_integrand g hJ continuous_fst ((lav_continuous_windowJoin _ e).comp
        (continuous_const.add (continuous_snd.smul continuous_const))) a n hr
        (hf.comp measurable_fst)
    exact ((measurable_gaussianPDFReal 0 1).comp measurable_snd).ennreal_ofReal.mul h2
  set M := Hmat g W L (windowJoin (cellWindow a n) w e) with hM
  have hae : ∀ᵐ E : ℝ, (pathOp g (fun j : Fin (L - n) =>
      gueBlock W L (windowJoin (cellWindow a n) w e) (cellBlock a (n + j))) 0 0 -
      (E : ℂ) • (1 : Matrix (Fin (L - n) × Fin W) (Fin (L - n) × Fin W) ℂ)).det ≠ 0 :=
    measure_eq_zero_iff_ae_notMem.mp ((lav_finite_det _).measure_zero _)
  rw [← lav_lintegral_gaussian hFt]
  calc _ = ∫⁻ t, eigMassSum (M + (((g * W * Real.sqrt n)⁻¹ * t : ℝ) : ℂ) •
        coordProj (cellCoords a n)) (cellCoords a n) (fun E =>
          ENNReal.ofReal (gaussianPDFReal 0 1 t) * J.indicator (fun E => ENNReal.ofReal
            (cellWeight g E (windowJoin (cellWindow a n) (w + t • scalarDir W n univ) e) a n ^ r) *
              f E) E) := by
        refine lintegral_congr fun t => ?_
        have hdiv : t / (g * W * Real.sqrt n) = (g * W * Real.sqrt n)⁻¹ * t := div_eq_inv_mul _ _
        rw [Hmat_windowJoin_line hg (by omega) hnL.le, hdiv, lav_mul_eigMassSum]
    _ ≤ ENNReal.ofReal (g * W * Real.sqrt n)⁻¹⁻¹ * ∫⁻ E, ∑' ℓ : ℤ,
        crossCount (fun u => M + (((g * W * Real.sqrt n)⁻¹ * u : ℝ) : ℂ) •
          coordProj (cellCoords a n)) E (Set.Icc (ℓ : ℝ) (ℓ + 1)) *
          (⨆ u ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (gaussianPDFReal 0 1 u) *
            J.indicator (fun E => ENNReal.ofReal (cellWeight g E
              (windowJoin (cellWindow a n) (w + u • scalarDir W n univ) e) a n ^ r) * f E) E) :=
        lintegral_eigMassSum_line_le (Hmat_isHermitian g W L _) (cellCoords a n) hc0 hGl
    _ ≤ ENNReal.ofReal (g * W * Real.sqrt n)⁻¹⁻¹ * ∫⁻ E,
        ENNReal.ofReal ((2 + 2 * Real.sqrt 2) * W) * J.indicator (fun E => f E *
          ∑' ℓ : ℤ, (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (gaussianPDFReal 0 1 t)) *
            (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (cellWeight g E
              (windowJoin (cellWindow a n) (w + t • scalarDir W n univ) e) a n ^ (r + 2)))) E := by
        refine mul_le_mul_right (lintegral_mono_ae ?_) _
        filter_upwards [hae] with E hE
        exact lav_pointwise hg hW hn hnL hng a w e hr J f hE
    _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, inv_inv]
        exact (mul_assoc _ _ _).symm

/-- The Claim (E.6) [uva:eq:average], for a fixed exterior configuration
`e`: the cell blocks are a fresh sample `v` of `n` GUE blocks. -/
theorem cell_average_fixed {E₀ : ℝ} (hE₀ : E₀ < 2) {r : ℝ} (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, 2 / Real.sqrt (2 - E₀) ≤ g →
      ∀ L n : ℕ, 2 ≤ n → g ^ 2 / 2 ≤ n → (n : ℝ) ≤ 2 * g ^ 2 → n < L → ∀ a : Fin L,
      ∀ J : Set ℝ, MeasurableSet J → J ⊆ Set.Icc (-E₀) E₀ → ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∀ e : {p : Fin L × Fin W × Fin W // p.1 ∉ Set.range (cellWindow a n)} → ℝ,
        ∫⁻ v, eigMassSum (Hmat g W L (windowJoin (cellWindow a n) v e)) (cellCoords a n)
            (J.indicator fun E => ENNReal.ofReal
              (cellWeight g E (windowJoin (cellWindow a n) v e) a n ^ r) * f E) ∂(μ W n) ≤
          ENNReal.ofReal (C * n * (W : ℝ) ^ 2) * ∫⁻ E in J, f E := by
  obtain ⟨Ch, hCh, W₁, hav⟩ := cellWeight_line_average hE₀ (h := r + 2) (by linarith)
  refine ⟨Real.sqrt 2 * (2 + 2 * Real.sqrt 2) * Ch, by positivity, max W₁ 1, ?_⟩
  intro W hW g hg L n hn2 hng1 hng2 hnL a J hJ hJE f hf e
  rcases lt_or_ge E₀ 0 with hE0 | hE0
  · have hJ0 : J = ∅ := Set.eq_empty_of_subset_empty
      (hJE.trans (Set.Icc_eq_empty (by linarith)).subset)
    subst hJ0
    simp [lav_eigMassSum_zero]
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  have hg1 : 1 ≤ g := by
    have hsq0 : 0 < Real.sqrt (2 - E₀) := Real.sqrt_pos.mpr (by linarith)
    have hsq : Real.sqrt (2 - E₀) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
    exact le_trans ((le_div_iff₀ hsq0).mpr (by linarith)) hg
  have hg0 : 0 < g := by linarith
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hμ : μ W n = stdGauss (Fin n × Fin W × Fin W) := rfl
  have hsd : ∑ i, scalarDir W n univ i ^ 2 = 1 :=
    sum_sq_scalarDir hW1 ⟨⟨0, by omega⟩, mem_univ _⟩
  have hF := lav_measurable_fixed (L := L) g a e hr hJ hf
  have hΦ : Measurable fun x : Ω W n × ℝ => ∑' ℓ : ℤ,
      (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (gaussianPDFReal 0 1 t)) *
        (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (cellWeight g x.2
          (windowJoin (cellWindow a n) (x.1 - (∑ i, x.1 i * scalarDir W n univ i) •
            scalarDir W n univ + t • scalarDir W n univ) e) a n ^ (r + 2))) := by
    refine Measurable.tsum fun ℓ => measurable_const.mul ?_
    refine LowerSemicontinuous.measurable (lowerSemicontinuous_iSup fun t =>
      lowerSemicontinuous_iSup fun _ => ?_)
    have hc : Continuous fun x : Ω W n × ℝ => x.1 - (∑ i, x.1 i * scalarDir W n univ i) •
        scalarDir W n univ + t • scalarDir W n univ := by fun_prop
    exact lav_lsc_cellWeight g continuous_snd ((lav_continuous_windowJoin _ e).comp hc) a n
      (by linarith)
  have hΨ : Measurable (Function.uncurry fun (v : Ω W n) (E : ℝ) => J.indicator (fun E => f E *
      ∑' ℓ : ℤ, (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (gaussianPDFReal 0 1 t)) *
        (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (cellWeight g E
          (windowJoin (cellWindow a n) (v - (∑ i, v i * scalarDir W n univ i) •
            scalarDir W n univ + t • scalarDir W n univ) e) a n ^ (r + 2)))) E) := by
    simp only [Function.uncurry_def, Set.indicator_apply]
    exact Measurable.ite (measurable_snd hJ) ((hf.comp measurable_snd).mul hΦ) measurable_const
  have hreal : g * W * Real.sqrt n * ((2 + 2 * Real.sqrt 2) * W) * Ch ≤
      Real.sqrt 2 * (2 + 2 * Real.sqrt 2) * Ch * n * (W : ℝ) ^ 2 := by
    have h1 : g ≤ Real.sqrt 2 * Real.sqrt n := by
      rw [← Real.sqrt_mul (by norm_num)]
      exact (le_abs_self g).trans (Real.abs_le_sqrt (by linarith))
    have h2 : g * Real.sqrt n ≤ Real.sqrt 2 * n := by
      have h3 : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
      calc g * Real.sqrt n ≤ Real.sqrt 2 * Real.sqrt n * Real.sqrt n :=
            mul_le_mul_of_nonneg_right h1 hsn.le
        _ = Real.sqrt 2 * n := by rw [mul_assoc, h3]
    calc g * W * Real.sqrt n * ((2 + 2 * Real.sqrt 2) * W) * Ch =
          (g * Real.sqrt n) * ((2 + 2 * Real.sqrt 2) * Ch * (W : ℝ) ^ 2) := by ring
      _ ≤ (Real.sqrt 2 * n) * ((2 + 2 * Real.sqrt 2) * Ch * (W : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = _ := by ring
  rw [hμ, lintegral_stdGauss_line _ hsd hF]
  calc _ ≤ ∫⁻ v, (ENNReal.ofReal (g * W * Real.sqrt n) *
        ENNReal.ofReal ((2 + 2 * Real.sqrt 2) * W) * ∫⁻ E, J.indicator (fun E => f E *
          ∑' ℓ : ℤ, (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (gaussianPDFReal 0 1 t)) *
            (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (cellWeight g E
              (windowJoin (cellWindow a n) (v - (∑ i, v i * scalarDir W n univ i) •
                scalarDir W n univ + t • scalarDir W n univ) e) a n ^ (r + 2)))) E)
          ∂(stdGauss (Fin n × Fin W × Fin W)) :=
        lintegral_mono fun v => lav_line_bound hg1 hW1 hn2 hnL hng2 a _ e hr hJ hf
    _ = ENNReal.ofReal (g * W * Real.sqrt n) * ENNReal.ofReal ((2 + 2 * Real.sqrt 2) * W) *
        ∫⁻ E, ∫⁻ v, J.indicator (fun E => f E *
          ∑' ℓ : ℤ, (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (gaussianPDFReal 0 1 t)) *
            (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (cellWeight g E
              (windowJoin (cellWindow a n) (v - (∑ i, v i * scalarDir W n univ i) •
                scalarDir W n univ + t • scalarDir W n univ) e) a n ^ (r + 2)))) E
          ∂(stdGauss (Fin n × Fin W × Fin W)) := by
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          ENNReal.ofReal_ne_top), lintegral_lintegral_swap hΨ.aemeasurable]
    _ ≤ ENNReal.ofReal (g * W * Real.sqrt n) * ENNReal.ofReal ((2 + 2 * Real.sqrt 2) * W) *
        ∫⁻ E, J.indicator (fun E => f E * ENNReal.ofReal Ch) E := by
        refine mul_le_mul_right (lintegral_mono fun E => ?_) _
        by_cases hEJ : E ∈ J
        · simp only [Set.indicator_of_mem hEJ]
          have hm : Measurable fun v : Ω W n => ∑' ℓ : ℤ,
              (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (gaussianPDFReal 0 1 t)) *
                (⨆ t ∈ Set.Icc (ℓ : ℝ) (ℓ + 1), ENNReal.ofReal (cellWeight g E
                  (windowJoin (cellWindow a n) (v - (∑ i, v i * scalarDir W n univ i) •
                    scalarDir W n univ + t • scalarDir W n univ) e) a n ^ (r + 2))) :=
            by
            refine Measurable.tsum fun ℓ => measurable_const.mul ?_
            refine LowerSemicontinuous.measurable (lowerSemicontinuous_iSup fun t =>
              lowerSemicontinuous_iSup fun _ => ?_)
            have hc : Continuous fun v : Ω W n => v - (∑ i, v i * scalarDir W n univ i) •
                scalarDir W n univ + t • scalarDir W n univ := by fun_prop
            exact lav_lsc_cellWeight g continuous_const
              ((lav_continuous_windowJoin _ e).comp hc) a n (by linarith)
          rw [lintegral_const_mul _ hm]
          refine mul_le_mul_right ?_ _
          have hE : |E| ≤ E₀ := abs_le.mpr ⟨by linarith [(hJE hEJ).1], (hJE hEJ).2⟩
          exact hav W (le_trans (le_max_left _ _) hW) g hg L n (by omega) hng2 hnL.le a E hE e
        · simp [Set.indicator_of_notMem hEJ]
    _ = ENNReal.ofReal (g * W * Real.sqrt n * ((2 + 2 * Real.sqrt 2) * W) * Ch) *
        ∫⁻ E in J, f E := by
        rw [lintegral_indicator hJ, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
          ENNReal.ofReal_mul (p := g * W * Real.sqrt n * ((2 + 2 * Real.sqrt 2) * W))
            (by positivity), ENNReal.ofReal_mul (p := g * W * Real.sqrt n) (by positivity)]
        ring
    _ ≤ _ := mul_le_mul_left (ENNReal.ofReal_le_ofReal hreal) _

/-- The Claim (E.6) [uva:eq:average] integrated over the exterior: for `f(E, ω)` depending only on
the blocks outside the cell, `𝔼 Σ_{λ_k ∈ J} m_A(k) K_A(λ_k)^r f(λ_k) ≤ C_r n W² 𝔼 ∫_J f(E) dE`. -/
theorem cell_average {E₀ : ℝ} (hE₀ : E₀ < 2) {r : ℝ} (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, 2 / Real.sqrt (2 - E₀) ≤ g →
      ∀ L n : ℕ, 2 ≤ n → g ^ 2 / 2 ≤ n → (n : ℝ) ≤ 2 * g ^ 2 → n < L → ∀ a : Fin L,
      ∀ J : Set ℝ, MeasurableSet J → J ⊆ Set.Icc (-E₀) E₀ →
      ∀ f : ℝ → Ω W L → ℝ≥0∞, Measurable (Function.uncurry f) →
      (∀ E (ω ω' : Ω W L), (∀ p : Fin L × Fin W × Fin W, p.1 ∉ Set.range (cellWindow a n) →
        ω p = ω' p) → f E ω = f E ω') →
        ∫⁻ ω, eigMassSum (Hmat g W L ω) (cellCoords a n)
            (J.indicator fun E => ENNReal.ofReal (cellWeight g E ω a n ^ r) * f E ω) ∂(μ W L) ≤
          ENNReal.ofReal (C * n * (W : ℝ) ^ 2) * ∫⁻ ω, (∫⁻ E in J, f E ω) ∂(μ W L) := by
  obtain ⟨C, hC, W₀, hfix⟩ := cell_average_fixed hE₀ hr
  refine ⟨C, hC, W₀, ?_⟩
  intro W hW g hg L n hn2 hng1 hng2 hnL a J hJ hJE f hf hext
  have hinj := cellWindow_injective a hnL.le
  have hF : Measurable fun ω : Ω W L => eigMassSum (Hmat g W L ω) (cellCoords a n)
      (J.indicator fun E => ENNReal.ofReal (cellWeight g E ω a n ^ r) * f E ω) := by
    have hG : Measurable fun x : Ω W L × ℝ => J.indicator (fun E => ENNReal.ofReal
        (cellWeight g E x.1 a n ^ r) * f E x.1) x.2 := by
      simp only [Set.indicator_apply]
      exact lav_measurable_integrand g hJ continuous_snd continuous_fst a n hr
        (hf.comp (measurable_snd.prodMk measurable_fst))
    exact measurable_eigMassSum (A := Hmat g W L) (continuous_Hmat g W L).measurable
      (cellCoords a n)
      (G := fun ω E => J.indicator (fun E => ENNReal.ofReal (cellWeight g E ω a n ^ r) * f E ω) E)
      hG
  have hR : Measurable fun ω : Ω W L => ∫⁻ E in J, f E ω :=
    Measurable.lintegral_prod_left (μ := volume.restrict J) hf
  rw [lintegral_windowJoin W L n hinj hF, lintegral_windowJoin W L n hinj hR]
  have hjoin : ∀ e, ∃ fe : ℝ → ℝ≥0∞, Measurable fe ∧
      ∀ (v : Ω W n) (E : ℝ), f E (windowJoin (cellWindow a n) v e) = fe E := fun e =>
    ⟨fun E => f E (windowJoin (cellWindow a n) 0 e),
      hf.comp (measurable_id.prodMk measurable_const), fun v E =>
        hext E _ _ fun p hp => by simp only [windowJoin, hp, ↓reduceDIte]⟩
  calc _ ≤ ∫⁻ e, ENNReal.ofReal (C * n * (W : ℝ) ^ 2) *
        (∫⁻ v, (∫⁻ E in J, f E (windowJoin (cellWindow a n) v e)) ∂(μ W n))
        ∂(stdGauss {p : Fin L × Fin W × Fin W // p.1 ∉ Set.range (cellWindow a n)}) := by
        refine lintegral_mono fun e => ?_
        obtain ⟨fe, hfe, hfe'⟩ := hjoin e
        simp only [hfe']
        rw [lintegral_const, measure_univ (μ := μ W n), mul_one]
        exact hfix W hW g hg L n hn2 hng1 hng2 hnL a J hJ hJE fe hfe e
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end LSBA
