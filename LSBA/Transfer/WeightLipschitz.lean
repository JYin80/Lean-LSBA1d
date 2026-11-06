import LSBA.Transfer.Weight

/-!
# Suprema of the transfer weight on an energy interval

(E.12) [uva:eq:sobolev-audit] in the energy variable: for `g ≥ 1`, the weight `K` of a block
sequence satisfies `|dK/dE| ≤ n K⁵` almost everywhere, hence on every interval `I` of length `δ`,
`sup_I K^h ≤ (δ⁻¹ + h n) ∫_I K^{h+4}` for `h ≥ 0`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### The energy derivative of a transfer matrix -/

/-- The projection `diag(1, 0) ⊗ I`, the energy derivative of a transfer matrix. -/
private def wlP (W : ℕ) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  Matrix.diagonal fun p => if p.1 = 0 then 1 else 0

/-- The projection `diag(0, 1) ⊗ I`, the energy derivative of the inverse of a transfer matrix. -/
private def wlQ (W : ℕ) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  Matrix.diagonal fun p => if p.1 = 1 then 1 else 0

private lemma wlP_norm_le (W : ℕ) : ‖wlP W‖ ≤ 1 := by
  unfold wlP
  rw [Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun p => ?_
  by_cases h : p.1 = 0 <;> simp [h]

private lemma transferMat_sub {W : ℕ} (g : ℝ) (z z' : ℂ) (V : Matrix (Fin W) (Fin W) ℂ) :
    transferMat g z V - transferMat g z' V = (z - z') • wlP W := by
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases b <;> by_cases h : i = j <;>
    simp [transferMat, transferFree, wlP, Matrix.kroneckerMap_apply, Matrix.sub_apply,
      Matrix.smul_apply, h]

private lemma transferInv_sub {W : ℕ} (g : ℝ) (z z' : ℂ) (V : Matrix (Fin W) (Fin W) ℂ) :
    transferInv g z V - transferInv g z' V = (z - z') • wlQ W := by
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases b <;> by_cases h : i = j <;>
    simp [transferInv, wlQ, Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.smul_apply, h]


/-- The inverse prefix products `T(V_0)⁻¹ ⋯ T(V_{j-1})⁻¹`. -/
private def wlInvProd {W : ℕ} (g : ℝ) (z : ℂ) (V : ℕ → Matrix (Fin W) (Fin W) ℂ) :
    ℕ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ
  | 0 => 1
  | j + 1 => wlInvProd g z V j * transferInv g z (V j)

private lemma inv_transferProd {W : ℕ} (g : ℝ) (z : ℂ) (V : ℕ → Matrix (Fin W) (Fin W) ℂ)
    (j : ℕ) : (transferProd g z V j)⁻¹ = wlInvProd g z V j := by
  induction j with
  | zero => simp [transferProd, wlInvProd]
  | succ j ih => rw [transferProd, Matrix.mul_inv_rev, inv_transferMat, ih, wlInvProd]

private lemma transferProd_mul_inv {W : ℕ} (g : ℝ) (z : ℂ) (V : ℕ → Matrix (Fin W) (Fin W) ℂ)
    (j : ℕ) : transferProd g z V j * (transferProd g z V j)⁻¹ = 1 := by
  rw [inv_transferProd]
  induction j with
  | zero => simp [transferProd, wlInvProd]
  | succ j ih =>
    rw [transferProd, wlInvProd, Matrix.mul_assoc, ← Matrix.mul_assoc (transferProd g z V j),
      ih, Matrix.one_mul, transferMat_mul_transferInv]

private lemma continuous_transferMat_re {W : ℕ} (g : ℝ) (V : Matrix (Fin W) (Fin W) ℂ) :
    Continuous fun x : ℝ => transferMat g (x : ℂ) V := by
  have h : ∀ x : ℝ, transferMat g (x : ℂ) V = transferMat g 0 V + (x : ℂ) • wlP W := fun x => by
    rw [← sub_eq_iff_eq_add', transferMat_sub, sub_zero]
  simp only [h]
  exact continuous_const.add (Complex.continuous_ofReal.smul continuous_const)

private lemma continuous_transferInv_re {W : ℕ} (g : ℝ) (V : Matrix (Fin W) (Fin W) ℂ) :
    Continuous fun x : ℝ => transferInv g (x : ℂ) V := by
  have h : ∀ x : ℝ, transferInv g (x : ℂ) V = transferInv g 0 V + (x : ℂ) • wlQ W := fun x => by
    rw [← sub_eq_iff_eq_add', transferInv_sub, sub_zero]
  simp only [h]
  exact continuous_const.add (Complex.continuous_ofReal.smul continuous_const)

private lemma continuous_transferProd_re {W : ℕ} (g : ℝ) (V : ℕ → Matrix (Fin W) (Fin W) ℂ)
    (j : ℕ) : Continuous fun x : ℝ => transferProd g (x : ℂ) V j := by
  induction j with
  | zero => exact continuous_const
  | succ j ih => exact (continuous_transferMat_re g (V j)).mul ih

private lemma continuous_inv_transferProd_re {W : ℕ} (g : ℝ) (V : ℕ → Matrix (Fin W) (Fin W) ℂ)
    (j : ℕ) : Continuous fun x : ℝ => (transferProd g (x : ℂ) V j)⁻¹ := by
  simp only [inv_transferProd]
  induction j with
  | zero => exact continuous_const
  | succ j ih => exact ih.mul (continuous_transferInv_re g (V j))


/-- The telescoping identity `F_j(x) - F_j(y) = (x - y) ∑_{k<j} F_j(x) F_{k+1}(x)⁻¹ (P ⊗ I) F_k(y)`
for the prefix products at two real energies. -/
private lemma transferProd_sub_sum {W : ℕ} (g : ℝ) (V : ℕ → Matrix (Fin W) (Fin W) ℂ) (x y : ℝ)
    (j : ℕ) :
    transferProd g (x : ℂ) V j - transferProd g (y : ℂ) V j =
      ((x - y : ℝ) : ℂ) • ∑ k ∈ Finset.range j,
        transferProd g (x : ℂ) V j * (transferProd g (x : ℂ) V (k + 1))⁻¹ * wlP W *
          transferProd g (y : ℂ) V k := by
  induction j with
  | zero => simp [transferProd]
  | succ j ih =>
    have hT : transferMat g (x : ℂ) (V j) - transferMat g (y : ℂ) (V j) =
        ((x - y : ℝ) : ℂ) • wlP W := by
      rw [transferMat_sub]; push_cast; rfl
    have hd : transferProd g (x : ℂ) V (j + 1) - transferProd g (y : ℂ) V (j + 1) =
        transferMat g (x : ℂ) (V j) *
            (transferProd g (x : ℂ) V j - transferProd g (y : ℂ) V j) +
          (transferMat g (x : ℂ) (V j) - transferMat g (y : ℂ) (V j)) *
            transferProd g (y : ℂ) V j := by
      rw [transferProd, transferProd, Matrix.mul_sub, Matrix.sub_mul]; abel
    rw [hd, hT, ih, Finset.sum_range_succ, smul_add, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc _ _ (transferProd g (y : ℂ) V j), mul_assoc, Finset.mul_sum]
    rw [← Matrix.mul_assoc, transferProd_mul_inv, Matrix.one_mul]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    have hx : transferProd g (x : ℂ) V (j + 1) =
        transferMat g (x : ℂ) (V j) * transferProd g (x : ℂ) V j := rfl
    rw [hx]
    simp only [Matrix.mul_assoc]


private lemma transferWeight_eq {g : ℝ} (hg : 1 ≤ g) (x : ℝ) {W : ℕ}
    (V : ℕ → Matrix (Fin W) (Fin W) ℂ) (n : ℕ) :
    transferWeight g x V n = ⨆ j : Fin (n + 1), max 1 (max ‖transferProd g (x : ℂ) V j‖
      ‖(transferProd g (x : ℂ) V j)⁻¹‖) := by
  have hz : max 1 g * x / g = x := by
    rw [max_eq_right hg]; field_simp [(by linarith : g ≠ 0)]
  unfold transferWeight
  rw [hz]

private lemma transferWeight_bounds_re {g : ℝ} (hg : 1 ≤ g) (x : ℝ) {W : ℕ}
    (V : ℕ → Matrix (Fin W) (Fin W) ℂ) (n : ℕ) :
    1 ≤ transferWeight g x V n ∧ ∀ j ≤ n,
      ‖transferProd g (x : ℂ) V j‖ ≤ transferWeight g x V n ∧
        ‖(transferProd g (x : ℂ) V j)⁻¹‖ ≤ transferWeight g x V n := by
  have hz : max 1 g * x / g = x := by
    rw [max_eq_right hg]; field_simp [(by linarith : g ≠ 0)]
  have h := transferWeight_bounds g x V n
  simpa only [hz] using h

/-- `‖F_j(x) - F_j(y)‖ ≤ n |x - y| K(x)² K(y)` for `j ≤ n`. -/
private lemma norm_transferProd_sub_le {g : ℝ} (hg : 1 ≤ g) {W : ℕ}
    (V : ℕ → Matrix (Fin W) (Fin W) ℂ) (n : ℕ) (x y : ℝ) {j : ℕ} (hj : j ≤ n) :
    ‖transferProd g (x : ℂ) V j - transferProd g (y : ℂ) V j‖ ≤
      n * |x - y| * (transferWeight g x V n) ^ 2 * transferWeight g y V n := by
  obtain ⟨hx1, hxb⟩ := transferWeight_bounds_re hg x V n
  obtain ⟨hy1, hyb⟩ := transferWeight_bounds_re hg y V n
  set Kx := transferWeight g x V n
  set Ky := transferWeight g y V n
  rw [transferProd_sub_sum, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have hterm : ∀ k ∈ Finset.range j,
      ‖transferProd g (x : ℂ) V j * (transferProd g (x : ℂ) V (k + 1))⁻¹ * wlP W *
        transferProd g (y : ℂ) V k‖ ≤ Kx * Kx * 1 * Ky := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    refine le_trans (norm_mul_le _ _) ?_
    refine mul_le_mul (le_trans (norm_mul_le _ _) ?_) (hyb k (by omega)).1 (norm_nonneg _)
      (by positivity)
    refine mul_le_mul (le_trans (norm_mul_le _ _) ?_) (wlP_norm_le W) (norm_nonneg _)
      (by positivity)
    exact mul_le_mul (hxb j hj).1 (hxb (k + 1) (by omega)).2 (norm_nonneg _) (by linarith)
  have hsum := le_trans (norm_sum_le _ _) (Finset.sum_le_sum hterm)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hjn : (j : ℝ) ≤ n := by exact_mod_cast hj
  calc |x - y| * ‖∑ k ∈ Finset.range j,
        transferProd g (x : ℂ) V j * (transferProd g (x : ℂ) V (k + 1))⁻¹ * wlP W *
          transferProd g (y : ℂ) V k‖
      ≤ |x - y| * (j * (Kx * Kx * 1 * Ky)) := by gcongr
    _ ≤ |x - y| * (n * (Kx * Kx * 1 * Ky)) := by gcongr
    _ = n * |x - y| * Kx ^ 2 * Ky := by ring


/-- `‖F_j(x)⁻¹ - F_j(y)⁻¹‖ ≤ n |x - y| K(x)³ K(y)²` for `j ≤ n`. -/
private lemma norm_inv_transferProd_sub_le {g : ℝ} (hg : 1 ≤ g) {W : ℕ}
    (V : ℕ → Matrix (Fin W) (Fin W) ℂ) (n : ℕ) (x y : ℝ) {j : ℕ} (hj : j ≤ n) :
    ‖(transferProd g (x : ℂ) V j)⁻¹ - (transferProd g (y : ℂ) V j)⁻¹‖ ≤
      n * |x - y| * (transferWeight g x V n) ^ 3 * (transferWeight g y V n) ^ 2 := by
  obtain ⟨hx1, hxb⟩ := transferWeight_bounds_re hg x V n
  obtain ⟨hy1, hyb⟩ := transferWeight_bounds_re hg y V n
  have hid : (transferProd g (x : ℂ) V j)⁻¹ - (transferProd g (y : ℂ) V j)⁻¹ =
      (transferProd g (x : ℂ) V j)⁻¹ *
        (transferProd g (y : ℂ) V j - transferProd g (x : ℂ) V j) *
          (transferProd g (y : ℂ) V j)⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, transferProd_mul_inv,
      Matrix.mul_one, mul_eq_one_comm.1 (transferProd_mul_inv g (x : ℂ) V j),
      Matrix.one_mul]
  have hA := norm_transferProd_sub_le hg V n x y hj
  set Kx := transferWeight g x V n
  set Ky := transferWeight g y V n
  rw [hid]
  refine le_trans (norm_mul_le _ _) ?_
  refine le_trans (mul_le_mul (norm_mul_le _ _) (hyb j hj).2 (norm_nonneg _) (by positivity)) ?_
  rw [norm_sub_rev] at hA
  calc ‖(transferProd g (x : ℂ) V j)⁻¹‖ * ‖transferProd g (y : ℂ) V j -
          transferProd g (x : ℂ) V j‖ * Ky
      ≤ Kx * (n * |x - y| * Kx ^ 2 * Ky) * Ky := by
        gcongr
        · exact (hxb j hj).2
    _ = n * |x - y| * Kx ^ 3 * Ky ^ 2 := by ring


private lemma transferWeight_le_add {g : ℝ} (hg : 1 ≤ g) {W : ℕ}
    (V : ℕ → Matrix (Fin W) (Fin W) ℂ) (n : ℕ) (x y : ℝ) :
    transferWeight g x V n ≤ transferWeight g y V n +
      n * |x - y| * (max (transferWeight g x V n) (transferWeight g y V n)) ^ 5 := by
  obtain ⟨hx1, hxb⟩ := transferWeight_bounds_re hg x V n
  obtain ⟨hy1, hyb⟩ := transferWeight_bounds_re hg y V n
  have hAd := fun j (hj : j ≤ n) => norm_transferProd_sub_le hg V n x y hj
  have hBd := fun j (hj : j ≤ n) => norm_inv_transferProd_sub_le hg V n x y hj
  set Kx := transferWeight g x V n with hKx
  set Ky := transferWeight g y V n with hKy
  set m := max Kx Ky with hm
  have hm1 : 1 ≤ m := le_trans hx1 (le_max_left _ _)
  have hxm : Kx ≤ m := le_max_left _ _
  have hym : Ky ≤ m := le_max_right _ _
  have hc : 0 ≤ (n : ℝ) * |x - y| := by positivity
  have h3 : Kx ^ 2 * Ky ≤ m ^ 5 :=
    calc Kx ^ 2 * Ky ≤ m ^ 2 * m := by gcongr
      _ = m ^ 3 := by ring
      _ ≤ m ^ 5 := pow_le_pow_right₀ hm1 (by norm_num)
  have h5 : Kx ^ 3 * Ky ^ 2 ≤ m ^ 5 := by
    calc Kx ^ 3 * Ky ^ 2 ≤ m ^ 3 * m ^ 2 := by gcongr
      _ = m ^ 5 := by ring
  calc Kx = ⨆ j : Fin (n + 1), max 1 (max ‖transferProd g (x : ℂ) V j‖
        ‖(transferProd g (x : ℂ) V j)⁻¹‖) := transferWeight_eq hg x V n
    _ ≤ Ky + n * |x - y| * m ^ 5 := by
      refine ciSup_le fun j => ?_
      have hj : (j : ℕ) ≤ n := Nat.lt_succ_iff.mp j.2
      have hA := norm_le_norm_add_norm_sub' (u := transferProd g (x : ℂ) V j)
        (v := transferProd g (y : ℂ) V j)
      have hB := norm_le_norm_add_norm_sub' (u := (transferProd g (x : ℂ) V j)⁻¹)
        (v := (transferProd g (y : ℂ) V j)⁻¹)
      have e1 : (n : ℝ) * |x - y| * Kx ^ 2 * Ky ≤ n * |x - y| * m ^ 5 := by
        calc (n : ℝ) * |x - y| * Kx ^ 2 * Ky = (n * |x - y|) * (Kx ^ 2 * Ky) := by ring
          _ ≤ n * |x - y| * m ^ 5 := mul_le_mul_of_nonneg_left h3 hc
      have e2 : (n : ℝ) * |x - y| * Kx ^ 3 * Ky ^ 2 ≤ n * |x - y| * m ^ 5 := by
        calc (n : ℝ) * |x - y| * Kx ^ 3 * Ky ^ 2 = (n * |x - y|) * (Kx ^ 3 * Ky ^ 2) := by ring
          _ ≤ n * |x - y| * m ^ 5 := mul_le_mul_of_nonneg_left h5 hc
      refine max_le (by nlinarith [mul_nonneg hc (pow_nonneg (by linarith : (0 : ℝ) ≤ m) 5)])
        (max_le ?_ ?_)
      · linarith [(hyb j hj).1, hAd j hj]
      · linarith [(hyb j hj).2, hBd j hj]


private lemma transferWeight_abs_sub_le {g : ℝ} (hg : 1 ≤ g) {W : ℕ}
    (V : ℕ → Matrix (Fin W) (Fin W) ℂ) (n : ℕ) (x y : ℝ) :
    |transferWeight g x V n - transferWeight g y V n| ≤
      n * |x - y| * (max (transferWeight g x V n) (transferWeight g y V n)) ^ 5 := by
  have h1 := transferWeight_le_add hg V n x y
  have h2 := transferWeight_le_add hg V n y x
  rw [max_comm, abs_sub_comm] at h2
  rw [abs_le]
  constructor <;> linarith

private lemma continuous_transferWeight {g : ℝ} (hg : 1 ≤ g) {W : ℕ}
    (V : ℕ → Matrix (Fin W) (Fin W) ℂ) (n : ℕ) :
    Continuous fun x : ℝ => transferWeight g x V n := by
  have h : (fun x : ℝ => transferWeight g x V n) = fun x : ℝ =>
      Finset.univ.sup' Finset.univ_nonempty fun j : Fin (n + 1) =>
        max 1 (max ‖transferProd g (x : ℂ) V j‖ ‖(transferProd g (x : ℂ) V j)⁻¹‖) := by
    funext x
    rw [transferWeight_eq hg, Finset.sup'_univ_eq_ciSup]
  rw [h]
  refine Continuous.finset_sup'_apply Finset.univ_nonempty fun j _ => ?_
  exact continuous_const.max
    ((continuous_transferProd_re g V j).norm.max (continuous_inv_transferProd_re g V j).norm)


/-! ### Real-variable core -/

/-- At a point of differentiability, `|K'(x)| ≤ N K(x)⁵` for a continuous `K` with
`|K x - K y| ≤ N |x - y| max{K x, K y}⁵`. -/
private lemma abs_deriv_le_of_key {K : ℝ → ℝ} (hcont : Continuous K) {N : ℝ}
    (hkey : ∀ x y, |K x - K y| ≤ N * |x - y| * (max (K x) (K y)) ^ 5) {x D : ℝ}
    (hD : HasDerivAt K D x) : |D| ≤ N * K x ^ 5 := by
  have hn := hD.tendsto_slope_zero.norm
  have hc : Continuous fun t : ℝ => N * (max (K (x + t)) (K x)) ^ 5 :=
    continuous_const.mul (((hcont.comp (continuous_const.add continuous_id)).max
      continuous_const).pow 5)
  have hb : Filter.Tendsto (fun t : ℝ => N * (max (K (x + t)) (K x)) ^ 5)
      (nhdsWithin 0 {0}ᶜ) (nhds (N * K x ^ 5)) := by
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
    simpa using this
  rw [← Real.norm_eq_abs]
  refine le_of_tendsto_of_tendsto hn hb ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  have hk := hkey (x + t) x
  rw [show x + t - x = t by ring] at hk
  have habs : 0 < |t| := abs_pos.2 ht0
  rw [norm_smul, norm_inv, Real.norm_eq_abs, Real.norm_eq_abs]
  calc |t|⁻¹ * |K (x + t) - K x| ≤ |t|⁻¹ * (N * |t| * (max (K (x + t)) (K x)) ^ 5) := by gcongr
    _ = N * (max (K (x + t)) (K x)) ^ 5 := by field_simp


/-- `sup_{[a, a+δ]} K^h ≤ (δ⁻¹ + h N) ∫_a^{a+δ} K^{h+4}` for a continuous `K ≥ 1` with
`|K x - K y| ≤ N |x - y| max{K x, K y}⁵`. -/
private lemma rpow_le_of_key {K : ℝ → ℝ} (hcont : Continuous K) (h1 : ∀ x, 1 ≤ K x) {N : ℝ}
    (hN : 0 ≤ N) (hkey : ∀ x y, |K x - K y| ≤ N * |x - y| * (max (K x) (K y)) ^ 5)
    {h : ℝ} (hh : 0 ≤ h) (a : ℝ) {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : x ∈ Set.Icc a (a + δ)) :
    K x ^ h ≤ (δ⁻¹ + h * N) * ∫ t in a..a + δ, K t ^ (h + 4) := by
  have hab : a ≤ a + δ := by linarith
  have hu : Set.uIcc a (a + δ) = Set.Icc a (a + δ) := Set.uIcc_of_le hab
  have hpos : ∀ t, 0 < K t := fun t => lt_of_lt_of_le one_pos (h1 t)
  obtain ⟨M, hM⟩ : ∃ M, ∀ y ∈ Set.Icc a (a + δ), K y ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_Icc.bddAbove_image hcont.continuousOn)
    exact ⟨M, fun y hy => hM ⟨y, hy, rfl⟩⟩
  have hM1 : 1 ≤ M := le_trans (h1 a) (hM a ⟨le_rfl, hab⟩)
  have hLip : LipschitzOnWith (Real.toNNReal (N * M ^ 5)) K (Set.uIcc a (a + δ)) := by
    rw [hu]
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
    calc |K y - K z| ≤ N * |y - z| * (max (K y) (K z)) ^ 5 := hkey y z
      _ ≤ N * |y - z| * M ^ 5 := by
        gcongr
        · exact le_trans (hpos y).le (le_max_left _ _)
        · exact max_le (hM y hy) (hM z hz)
      _ = N * M ^ 5 * |y - z| := by ring
  have hAC : AbsolutelyContinuousOnInterval K a (a + δ) := hLip.absolutelyContinuousOnInterval
  have hdiff := hAC.ae_differentiableAt
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0, LipschitzOnWith C (fun t : ℝ => t ^ h) (Set.Icc 1 M) := by
    have hcd : ContDiffOn ℝ 1 (fun t : ℝ => t ^ h) (Set.Icc 1 M) :=
      contDiffOn_id.rpow_const_of_ne fun t ht => (lt_of_lt_of_le one_pos ht.1).ne'
    exact hcd.exists_lipschitzOnWith one_ne_zero (convex_Icc _ _) isCompact_Icc
  have hzAC : AbsolutelyContinuousOnInterval (fun t => K t ^ h) a (a + δ) :=
    hC.comp_absolutelyContinuousOnInterval (g := K)
      (fun y hy => by rw [hu] at hy; exact ⟨h1 y, hM y hy⟩) hAC
  have hae : ∀ᵐ t, t ∈ Set.uIcc a (a + δ) →
      ‖deriv (fun s => K s ^ h) t‖ ≤ h * N * K t ^ (h + 4) := by
    filter_upwards [hdiff] with t ht htm
    have hd := (ht htm).hasDerivAt
    have hz := hd.rpow_const (p := h) (Or.inl (hpos t).ne')
    rw [hz.deriv, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hh,
      abs_of_nonneg (Real.rpow_nonneg (hpos t).le _)]
    have hD := abs_deriv_le_of_key hcont hkey hd
    have hpow : K t ^ 5 * K t ^ (h - 1) = K t ^ (h + 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (hpos t)]
      congr 1; push_cast; ring
    calc |deriv K t| * h * K t ^ (h - 1) ≤ N * K t ^ 5 * h * K t ^ (h - 1) := by
          gcongr
          exact Real.rpow_nonneg (hpos t).le _
      _ = h * N * (K t ^ 5 * K t ^ (h - 1)) := by ring
      _ = h * N * K t ^ (h + 4) := by rw [hpow]
  have hcp : ∀ p : ℝ, Continuous fun t => K t ^ p := fun p =>
    hcont.rpow_const fun t => Or.inl (hpos t).ne'
  have hG : Continuous fun t => h * N * K t ^ (h + 4) := continuous_const.mul (hcp _)
  have hFTC : ∀ p q, p ≤ q → p ∈ Set.Icc a (a + δ) → q ∈ Set.Icc a (a + δ) →
      |K q ^ h - K p ^ h| ≤ ∫ t in a..a + δ, h * N * K t ^ (h + 4) := by
    intro p q hpq hp hq
    have hsub : Set.uIcc p q ⊆ Set.uIcc a (a + δ) := by
      rw [hu]; exact Set.uIcc_subset_Icc hp hq
    have hF := (hzAC.mono hsub).integral_deriv_eq_sub
    rw [← hF, ← Real.norm_eq_abs]
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le hpq ?_
      (hG.intervalIntegrable _ _)) ?_
    · filter_upwards [hae] with t ht htm
      exact ht (hsub (by rw [Set.uIcc_of_le hpq]; exact Set.Ioc_subset_Icc_self htm))
    · refine intervalIntegral.integral_mono_interval hp.1 hpq hq.2 ?_ (hG.intervalIntegrable _ _)
      exact ae_of_all _ fun t => mul_nonneg (mul_nonneg hh hN) (Real.rpow_nonneg (hpos t).le _)
  have hJ' : ∫ t in a..a + δ, h * N * K t ^ (h + 4) = h * N * ∫ t in a..a + δ, K t ^ (h + 4) :=
    intervalIntegral.integral_const_mul _ _
  have hbd : ∀ y ∈ Set.Icc a (a + δ),
      K x ^ h ≤ K y ^ h + h * N * ∫ t in a..a + δ, K t ^ (h + 4) := by
    intro y hy
    rw [← hJ']
    rcases le_total y x with hyx | hxy
    · have := (abs_le.1 (hFTC y x hyx hy hx)).2
      linarith
    · have := (abs_le.1 (hFTC x y hxy hx hy)).1
      linarith
  have hint1 : IntervalIntegrable (fun t => K t ^ h) volume a (a + δ) :=
    (hcp h).intervalIntegrable _ _
  have hint4 : IntervalIntegrable (fun t => K t ^ (h + 4)) volume a (a + δ) :=
    (hcp _).intervalIntegrable _ _
  have hle : ∫ t in a..a + δ, K t ^ h ≤ ∫ t in a..a + δ, K t ^ (h + 4) :=
    intervalIntegral.integral_mono_on hab hint1 hint4 fun t _ =>
      Real.rpow_le_rpow_of_exponent_le (h1 t) (by linarith)
  have havg : ∫ _ in a..a + δ, K x ^ h ≤
      ∫ t in a..a + δ, (K t ^ h + h * N * ∫ t in a..a + δ, K t ^ (h + 4)) :=
    intervalIntegral.integral_mono_on hab intervalIntegrable_const
      (hint1.add intervalIntegrable_const) hbd
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add hint1 intervalIntegrable_const,
    intervalIntegral.integral_const] at havg
  simp only [smul_eq_mul, add_sub_cancel_left] at havg
  calc K x ^ h = δ⁻¹ * (δ * K x ^ h) := by field_simp
    _ ≤ δ⁻¹ * ((∫ t in a..a + δ, K t ^ (h + 4)) +
          δ * (h * N * ∫ t in a..a + δ, K t ^ (h + 4))) := by gcongr; linarith
    _ = (δ⁻¹ + h * N) * ∫ t in a..a + δ, K t ^ (h + 4) := by field_simp

/-- (E.12) [uva:eq:sobolev-audit]: `sup_{[x₀, x₀+δ]} K^h ≤ (δ⁻¹ + h n) ∫_{[x₀, x₀+δ]} K^{h+4}` for
`g ≥ 1`, `h ≥ 0`, `δ > 0`. -/
theorem transferWeight_sup_le {g : ℝ} (hg : 1 ≤ g) {W : ℕ} (V : ℕ → Matrix (Fin W) (Fin W) ℂ)
    (n : ℕ) {h : ℝ} (hh : 0 ≤ h) (x₀ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (⨆ x ∈ Set.Icc x₀ (x₀ + δ), ENNReal.ofReal (transferWeight g x V n ^ h)) ≤
      ENNReal.ofReal (δ⁻¹ + h * n) *
        ∫⁻ x in Set.Icc x₀ (x₀ + δ), ENNReal.ofReal (transferWeight g x V n ^ (h + 4)) := by
  have hcont := continuous_transferWeight hg V n
  have h1 : ∀ x : ℝ, 1 ≤ transferWeight g x V n := fun x => (transferWeight_bounds_re hg x V n).1
  have hmain := fun x (hx : x ∈ Set.Icc x₀ (x₀ + δ)) =>
    rpow_le_of_key (K := fun x => transferWeight g x V n) hcont h1 (Nat.cast_nonneg n)
      (transferWeight_abs_sub_le hg V n) hh x₀ hδ hx
  have hcI : Continuous fun x => transferWeight g x V n ^ (h + 4) :=
    hcont.rpow_const fun x => Or.inl (by linarith [h1 x])
  have hJ : ∫⁻ x in Set.Icc x₀ (x₀ + δ), ENNReal.ofReal (transferWeight g x V n ^ (h + 4)) =
      ENNReal.ofReal (∫ t in x₀..x₀ + δ, transferWeight g t V n ^ (h + 4)) := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
      ofReal_integral_eq_lintegral_ofReal hcI.integrableOn_Icc
        (ae_of_all _ fun x => Real.rpow_nonneg (by linarith [h1 x]) _)]
  rw [hJ, ← ENNReal.ofReal_mul (by positivity)]
  exact iSup₂_le fun x hx => ENNReal.ofReal_le_ofReal (hmain x hx)

end LSBA
