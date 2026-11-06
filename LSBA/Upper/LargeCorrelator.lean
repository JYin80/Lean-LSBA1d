import LSBA.Upper.LargeAverage
import LSBA.Upper.LargeCellRatio
import LSBA.Upper.LargeGreenPath
import LSBA.Transfer.PathSchur
import LSBA.Model.Cycle

/-!
# Cell correlators

(E.3) [uva:eq:cell-correlator] from the path bound (8.3) [uva:eq:conversion-input]: for `n = ⌊g²⌋`,
two cells `A, B` of the cycle `ℤ_L` with lengths in `[n, 2n]` and every `d` at most the cyclic
distance of their blocks, `𝔼 Σ_{λ_k ∈ J} (m_A(k) m_B(k))^{1/2} ≤ C n W^P exp(−c d/(Wg²))` at every
`g` where the path bound holds.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Continuity and measurability of the weights and the path resolvents -/

/-- The matrix inverse is measurable. -/
private lemma lcor_measurable_inv {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable fun A : Matrix ι ι ℂ => A⁻¹ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  have hd : Measurable fun A : Matrix ι ι ℂ => A.det := (continuous_id.matrix_det).measurable
  have ha : Measurable fun A : Matrix ι ι ℂ => A.adjugate i j :=
    (continuous_id.matrix_adjugate).measurable.eval_matrix
  exact hd.inv.mul ha

/-- Each block of the GUE sample (1.2) [eq:covariance] is continuous in the sample. -/
private lemma lcor_continuous_gueBlock {W L : ℕ} (c : Fin L) :
    Continuous fun ω : Ω W L => gueBlock W L ω c := by
  refine continuous_matrix fun α β => ?_
  simp only [gueBlock, Matrix.of_apply]
  split_ifs <;> fun_prop

private lemma lcor_continuous_kronecker {X : Type*} [TopologicalSpace X] {W : ℕ}
    {P : X → Matrix (Fin 2) (Fin 2) ℂ} (hP : Continuous P)
    {V : X → Matrix (Fin W) (Fin W) ℂ} (hV : Continuous V) :
    Continuous fun x => P x ⊗ₖ V x := by
  refine continuous_matrix fun i j => ?_
  simp only [Matrix.kroneckerMap_apply]
  exact (hP.matrix_elem i.1 j.1).mul (hV.matrix_elem i.2 j.2)

/-- The transfer matrix of Definition 7.1 [def:transfer-matrices] is continuous in the energy and
the block. -/
private lemma lcor_continuous_transferMat {X : Type*} [TopologicalSpace X] {W : ℕ} (g : ℝ)
    {z : X → ℂ} (hz : Continuous z) {V : X → Matrix (Fin W) (Fin W) ℂ} (hV : Continuous V) :
    Continuous fun x => transferMat g (z x) (V x) := by
  unfold transferMat transferFree
  have hP : (fun x => !![z x, -1; 1, 0]) =
      fun x => z x • !![1, 0; 0, 0] + !![0, -1; 1, (0 : ℂ)] := by
    funext x
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine (lcor_continuous_kronecker ?_ continuous_const).sub
    ((continuous_const_smul _).comp (lcor_continuous_kronecker continuous_const hV))
  rw [hP]
  exact (hz.smul continuous_const).add continuous_const

private lemma lcor_continuous_prod {X : Type*} [TopologicalSpace X] {W : ℕ} (g : ℝ)
    {z : X → ℂ} (hz : Continuous z) {V : ℕ → X → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ i, Continuous (V i)) (j : ℕ) :
    Continuous fun x => transferProd g (z x) (fun i => V i x) j := by
  induction j with
  | zero => exact continuous_const
  | succ j ih => exact (lcor_continuous_transferMat g hz (hV j)).mul ih

/-- `x ↦ K_c(E(x); ω(x))^h` is measurable for continuous `E` and `ω`. -/
private lemma lcor_measurable_weight {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (g : ℝ) {E : X → ℝ} (hE : Continuous E) {W L : ℕ}
    {ω : X → Ω W L} (hω : Continuous ω) (c : Fin L) (n : ℕ) (h : ℝ) :
    Measurable fun x => ENNReal.ofReal (cellWeight g (E x) (ω x) c n ^ h) := by
  have hz : Continuous fun x => ((max 1 g * E x / g : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((continuous_const.mul hE).div_const _)
  have hV : ∀ i, Continuous fun x => gueBlock W L (ω x) (cellBlock c i) :=
    fun i => (lcor_continuous_gueBlock _).comp hω
  refine ENNReal.measurable_ofReal.comp (Measurable.pow_const ?_ h)
  unfold cellWeight transferWeight
  refine Measurable.iSup fun j => ?_
  have hF := lcor_continuous_prod g hz hV j
  exact measurable_const.max ((continuous_norm.comp hF).measurable.max
    (continuous_norm.measurable.comp (lcor_measurable_inv.comp hF.measurable)))

private lemma lcor_continuous_blockDiagOp {W m : ℕ} :
    Continuous fun V : Fin m → Matrix (Fin W) (Fin W) ℂ => blockDiagOp V := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  simp only [blockDiagOp, Matrix.of_apply]
  split_ifs
  · exact ((continuous_apply p.1).matrix_elem p.2 q.2)
  · exact continuous_const

/-- The path operator (8.5) [up:eq:shifted-resolvent] is continuous in its blocks. -/
private lemma lcor_continuous_pathOp (g : ℝ) {W m : ℕ} (L₀ R₀ : Matrix (Fin W) (Fin W) ℂ) :
    Continuous fun V : Fin m → Matrix (Fin W) (Fin W) ℂ => pathOp g V L₀ R₀ := by
  unfold pathOp
  exact ((continuous_const.add (lcor_continuous_blockDiagOp (W := W) (m := m))).const_smul
    ((max 1 g : ℝ)⁻¹ : ℂ)).add continuous_const

/-- `x ↦ ‖G_Λ(y, x'; E(x))‖^p` of a Dirichlet path with continuous blocks is measurable. -/
private lemma lcor_measurable_green {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (g : ℝ) {E : X → ℝ} (hE : Continuous E) {W m : ℕ}
    {V : X → Fin m → Matrix (Fin W) (Fin W) ℂ} (hV : Continuous V) (y x : Fin m) (p : ℝ) :
    Measurable fun z => ‖blockOf (resolventMat (pathOp g (V z) 0 0) (E z)) y x‖ₑ ^ p := by
  unfold resolventMat
  have hA : Continuous fun z => pathOp g (V z) 0 0 -
      ((E z : ℂ)) • (1 : Matrix (Fin m × Fin W) (Fin m × Fin W) ℂ) :=
    ((lcor_continuous_pathOp g 0 0).comp hV).sub
      ((Complex.continuous_ofReal.comp hE).smul continuous_const)
  have hb : Continuous fun X : Matrix (Fin m × Fin W) (Fin m × Fin W) ℂ => blockOf X y x :=
    continuous_pi fun _ => continuous_pi fun _ => continuous_id.matrix_elem _ _
  exact (continuous_enorm.measurable.comp (hb.measurable.comp
    (lcor_measurable_inv.comp hA.measurable))).pow_const p

/-! ### Dependence on the exterior of a cell -/

private lemma lcor_gueBlock_ext {W L : ℕ} {S : Set (Fin L)} {ω ω' : Ω W L}
    (h : ∀ p : Fin L × Fin W × Fin W, p.1 ∉ S → ω p = ω' p) {c : Fin L} (hc : c ∉ S) :
    gueBlock W L ω c = gueBlock W L ω' c := by
  ext α β
  simp only [gueBlock, Matrix.of_apply, h (c, α, α) hc, h (c, α, β) hc, h (c, β, α) hc]

private lemma lcor_transferProd_congr {W : ℕ} (g : ℝ) (z : ℂ)
    {V V' : ℕ → Matrix (Fin W) (Fin W) ℂ} {n : ℕ} (hV : ∀ j < n, V j = V' j) :
    ∀ j ≤ n, transferProd g z V j = transferProd g z V' j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [transferProd, transferProd, ih (by omega), hV j (by omega)]

/-- The weight of a block sequence depends only on its first `n` blocks. -/
private lemma lcor_transferWeight_congr {g E : ℝ} {W : ℕ} {V V' : ℕ → Matrix (Fin W) (Fin W) ℂ}
    {n : ℕ} (hV : ∀ j < n, V j = V' j) : transferWeight g E V n = transferWeight g E V' n := by
  unfold transferWeight
  congr 1
  funext j
  rw [lcor_transferProd_congr g _ hV j (Nat.lt_succ_iff.mp j.2)]

private lemma lcor_weight_nonneg (g E : ℝ) {W L : ℕ} (ω : Ω W L) (c : Fin L) (n : ℕ) :
    0 ≤ cellWeight g E ω c n :=
  le_trans zero_le_one (transferWeight_bounds g E _ n).1

/-! ### Cyclic geometry of two cells -/

private lemma lcor_cellBlock_zero {L : ℕ} (a : Fin L) : cellBlock a 0 = a := by
  apply Fin.ext
  simp [cellBlock, Nat.mod_eq_of_lt a.isLt]

private lemma lcor_cellBlock_add_L {L : ℕ} (a : Fin L) (k : ℕ) :
    cellBlock a (k + L) = cellBlock a k := by
  apply Fin.ext
  simp only [cellBlock]
  rw [← Nat.add_assoc, Nat.add_mod_right]

private lemma lcor_cellBlock_L {L : ℕ} (a : Fin L) : cellBlock a L = a := by
  have h := lcor_cellBlock_add_L a 0
  rw [Nat.zero_add] at h
  rw [h, lcor_cellBlock_zero]

private lemma lcor_cellBlock_cellBlock {L : ℕ} (a : Fin L) (m j : ℕ) :
    cellBlock (cellBlock a m) j = cellBlock a (m + j) := by
  apply Fin.ext
  simp only [cellBlock]
  rw [Nat.mod_add_mod, Nat.add_assoc]

private lemma lcor_cellBlock_inj {L : ℕ} (a : Fin L) {i k : ℕ} (hi : i < L) (hk : k < L)
    (h : cellBlock a i = cellBlock a k) : i = k := by
  have h' : cellWindow a L ⟨i, hi⟩ = cellWindow a L ⟨k, hk⟩ := h
  exact congrArg Fin.val (cellWindow_injective a le_rfl h')

/-- A block `a + k` with `n ≤ k < L` is outside the cell `a, …, a+n−1`. -/
private lemma lcor_not_mem_range {L : ℕ} (a : Fin L) {n k : ℕ} (hnk : n ≤ k) (hk : k < L) :
    cellBlock a k ∉ Set.range (cellWindow a n) := by
  rintro ⟨i, hi⟩
  have := lcor_cellBlock_inj a (by omega) hk hi
  omega

private lemma lcor_dist_core {L : ℕ} (a : Fin L) (k m : ℕ) :
    ((cellBlock a (k + m)).val + L - (cellBlock a k).val) % L ≤ m := by
  have hx : (cellBlock a k).val < L := (cellBlock a k).isLt
  have h1 : ((cellBlock a (k + m)).val + L - (cellBlock a k).val + (cellBlock a k).val) % L =
      (m + (cellBlock a k).val) % L := by
    rw [Nat.sub_add_cancel (by omega), Nat.add_mod_right]
    simp only [cellBlock]
    rw [Nat.mod_mod, Nat.add_mod_mod]
    congr 1
    ring
  have h2 : (cellBlock a (k + m)).val + L - (cellBlock a k).val ≡ m [MOD L] :=
    Nat.ModEq.add_right_cancel' _ h1
  calc _ = m % L := h2
    _ ≤ m := Nat.mod_le _ _

private lemma lcor_cycDist_le {L : ℕ} (a : Fin L) (k m : ℕ) :
    cycDist (cellBlock a k) (cellBlock a (k + m)) ≤ m ∧
      cycDist (cellBlock a (k + m)) (cellBlock a k) ≤ m :=
  ⟨(min_le_right _ _).trans (lcor_dist_core a k m), (min_le_left _ _).trans (lcor_dist_core a k m)⟩

private lemma lcor_cycDist_self {L : ℕ} (x : Fin L) : cycDist x x = 0 := by
  unfold cycDist
  simp

private lemma lcor_cycDist_comm {L : ℕ} (x y : Fin L) : cycDist x y = cycDist y x := by
  unfold cycDist
  exact min_comm _ _

/-- Two cells `A = a, …, a+n_A−1` and `B` with every block distance at least `d ≥ 1`: `B` is the
cell `a+n_A+j₀, …` inside `Λ = ℤ_L ∖ A`, and the blocks next to `B` are at distance at least
`d − 1` from the endpoints of `Λ`. -/
private lemma lcor_geom {L : ℕ} (a b : Fin L) {nA nB d : ℕ} (hnA : 1 ≤ nA) (hnB : 2 ≤ nB)
    (hd1 : 1 ≤ d) (hd : ∀ i < nA, ∀ j < nB, d ≤ cycDist (cellBlock a i) (cellBlock b j)) :
    ∃ j₀ : ℕ, nA + j₀ + nB ≤ L ∧ b = cellBlock a (nA + j₀) ∧ d ≤ j₀ + 1 ∧
      d + nA + j₀ + 1 ≤ L := by
  have hL : 0 < L := a.pos
  have hrL : (a.val + nA) % L < L := Nat.mod_lt _ hL
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, j₀ = (b.val + L - (a.val + nA) % L) % L := ⟨_, rfl⟩
  have hj₀L : j₀ < L := hj₀ ▸ Nat.mod_lt _ hL
  have hb : cellBlock a (nA + j₀) = b := by
    apply Fin.ext
    change (a.val + (nA + j₀)) % L = b.val
    rw [← Nat.add_assoc, ← Nat.mod_add_mod, hj₀, Nat.add_mod_mod,
      show (a.val + nA) % L + (b.val + L - (a.val + nA) % L) = b.val + L by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt b.isLt]
  have hcell : ∀ j, cellBlock b j = cellBlock a (nA + j₀ + j) := fun j => by
    rw [← hb, lcor_cellBlock_cellBlock]
  have hfit : nA + j₀ + nB ≤ L := by
    by_contra hlt
    replace hlt := Nat.lt_of_not_le hlt
    rcases Nat.lt_or_ge (nA + j₀) L with h1 | h1
    · have h2 := hd 0 (by omega) (L - (nA + j₀)) (by omega)
      rw [hcell, show nA + j₀ + (L - (nA + j₀)) = L by omega, lcor_cellBlock_L,
        lcor_cellBlock_zero, lcor_cycDist_self] at h2
      omega
    · have h2 := hd (nA + j₀ - L) (by omega) 0 (by omega)
      have h3 : cellBlock a (nA + j₀ - L) = cellBlock b 0 := by
        rw [hcell, Nat.add_zero, ← lcor_cellBlock_add_L a (nA + j₀ - L),
          show nA + j₀ - L + L = nA + j₀ by omega]
      rw [h3, lcor_cycDist_self] at h2
      omega
  refine ⟨j₀, hfit, hb.symm, ?_, ?_⟩
  · have h4 := hd (nA - 1) (by omega) 0 (by omega)
    rw [hcell, show nA + j₀ + 0 = (nA - 1) + (j₀ + 1) by omega] at h4
    exact h4.trans (lcor_cycDist_le a (nA - 1) (j₀ + 1)).1
  · have h5 := hd 0 (by omega) 1 (by omega)
    have e : cellBlock a 0 = cellBlock a ((nA + j₀ + 1) + (L - (nA + j₀ + 1))) := by
      rw [show (nA + j₀ + 1) + (L - (nA + j₀ + 1)) = L by omega, lcor_cellBlock_L,
        lcor_cellBlock_zero]
    rw [e, hcell] at h5
    have := h5.trans (lcor_cycDist_le a (nA + j₀ + 1) (L - (nA + j₀ + 1))).2
    omega

private lemma lcor_card_cellCoords {W L : ℕ} (a : Fin L) (n : ℕ) :
    (cellCoords (W := W) a n).card ≤ n * W := by
  calc (cellCoords (W := W) a n).card ≤ ((cellSet a n) ×ˢ (univ : Finset (Fin W))).card := by
        refine Finset.card_le_card fun p hp => ?_
        simp only [cellCoords, Finset.mem_filter] at hp
        exact Finset.mem_product.mpr ⟨hp.2, Finset.mem_univ _⟩
    _ = (cellSet a n).card * W := by rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    _ ≤ n * W := Nat.mul_le_mul_right _
        (Finset.card_image_le.trans (Finset.card_range n).le)

/-! ### Pointwise inequalities -/

/-- `m_A^{1−t} m_B^t ≤ 32^t m_A K_A^{4t} K_B^{4t} S^t` from (E.4) [uva:eq:ratio-audit] and
`n_B ≤ 2 n_A`. -/
private lemma lcor_ratio_rpow {mA mB KA KB S nA nB t : ℝ} (hmA : 0 ≤ mA) (hmB : 0 ≤ mB)
    (hKA : 0 ≤ KA) (hKB : 0 ≤ KB) (hS : 0 ≤ S) (hnA : 0 < nA) (hnB : nB ≤ 2 * nA)
    (ht0 : 0 ≤ t) (h : nA * mB ≤ 16 * KA ^ 4 * KB ^ 4 * nB * mA * S) :
    mA ^ (1 - t) * mB ^ t ≤ 32 ^ t * (mA * (KA ^ (4 * t) * (KB ^ (4 * t) * S ^ t))) := by
  have hX : 0 ≤ KA ^ 4 * KB ^ 4 * mA * S := by positivity
  have hmB' : mB ≤ 32 * (KA ^ 4 * KB ^ 4 * mA * S) := by
    have h2 : 16 * KA ^ 4 * KB ^ 4 * nB * mA * S ≤ nA * (32 * (KA ^ 4 * KB ^ 4 * mA * S)) :=
      calc 16 * KA ^ 4 * KB ^ 4 * nB * mA * S = 16 * (KA ^ 4 * KB ^ 4 * mA * S) * nB := by ring
        _ ≤ 16 * (KA ^ 4 * KB ^ 4 * mA * S) * (2 * nA) :=
          mul_le_mul_of_nonneg_left hnB (by positivity)
        _ = _ := by ring
    exact le_of_mul_le_mul_left (h.trans h2) hnA
  have h1 : mB ^ t ≤ (32 * (KA ^ 4 * KB ^ 4 * mA * S)) ^ t := Real.rpow_le_rpow hmB hmB' ht0
  have hK : ∀ K : ℝ, 0 ≤ K → (K ^ 4) ^ t = K ^ (4 * t) := fun K hK => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK]
    norm_num
  have hsplit : (32 * (KA ^ 4 * KB ^ 4 * mA * S)) ^ t =
      32 ^ t * (KA ^ (4 * t) * KB ^ (4 * t) * mA ^ t * S ^ t) := by
    rw [Real.mul_rpow (by norm_num) hX, Real.mul_rpow (by positivity) hS,
      Real.mul_rpow (by positivity) hmA, Real.mul_rpow (by positivity) (by positivity),
      hK KA hKA, hK KB hKB]
  have hm : mA ^ (1 - t) * mA ^ t = mA := by
    rw [← Real.rpow_add' hmA (by norm_num), sub_add_cancel, Real.rpow_one]
  calc mA ^ (1 - t) * mB ^ t ≤ mA ^ (1 - t) * (32 * (KA ^ 4 * KB ^ 4 * mA * S)) ^ t :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hmA _)
    _ = 32 ^ t * ((mA ^ (1 - t) * mA ^ t) * (KA ^ (4 * t) * (KB ^ (4 * t) * S ^ t))) := by
        rw [hsplit]
        ring
    _ = _ := by rw [hm]

private lemma lcor_sum_rpow_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (u : Fin 2 → Fin 2 → ℝ≥0∞) :
    (∑ i, ∑ x, u i x) ^ t ≤ ∑ i, ∑ x, u i x ^ t := by
  simp only [Fin.sum_univ_two]
  calc _ ≤ (u 0 0 + u 0 1) ^ t + (u 1 0 + u 1 1) ^ t := ENNReal.rpow_add_le_add_rpow _ _ ht0 ht1
    _ ≤ _ := add_le_add (ENNReal.rpow_add_le_add_rpow _ _ ht0 ht1)
        (ENNReal.rpow_add_le_add_rpow _ _ ht0 ht1)

/-- (E.4) [uva:eq:ratio-audit] raised to the power `t = q/4` and multiplied by `m_A`. -/
private lemma lcor_pointwise {W : ℕ} {mA mB KA KB nA nB q : ℝ} (hmA : 0 ≤ mA) (hmB : 0 ≤ mB)
    (hKA : 0 ≤ KA) (hKB : 0 ≤ KB) (hnA : 0 < nA) (hnB : nB ≤ 2 * nA) (hq0 : 0 < q)
    (hq1 : q < 1) (G : Fin 2 → Fin 2 → Matrix (Fin W) (Fin W) ℂ)
    (h : nA * mB ≤ 16 * KA ^ 4 * KB ^ 4 * nB * mA * ∑ i, ∑ x, ‖G i x‖ ^ 2) :
    ENNReal.ofReal (mA ^ (1 - q / 4) * mB ^ (q / 4)) ≤
      ENNReal.ofReal (32 ^ (q / 4)) * (ENNReal.ofReal mA * (ENNReal.ofReal (KA ^ q) *
        (ENNReal.ofReal (KB ^ q) * ∑ i, ∑ x, ‖G i x‖ₑ ^ (q / 2)))) := by
  have hS : 0 ≤ ∑ i, ∑ x, ‖G i x‖ ^ 2 := by positivity
  have hr := lcor_ratio_rpow hmA hmB hKA hKB hS hnA hnB (by positivity : (0 : ℝ) ≤ q / 4) h
  rw [show 4 * (q / 4) = q by ring] at hr
  have hSt : ENNReal.ofReal ((∑ i, ∑ x, ‖G i x‖ ^ 2) ^ (q / 4)) ≤
      ∑ i, ∑ x, ‖G i x‖ₑ ^ (q / 2) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg hS (by positivity),
      ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity]
    have hi : ∀ i : Fin 2, ENNReal.ofReal (∑ x, ‖G i x‖ ^ 2) = ∑ x, ENNReal.ofReal (‖G i x‖ ^ 2) :=
      fun i => ENNReal.ofReal_sum_of_nonneg fun x _ => by positivity
    simp_rw [hi]
    refine (lcor_sum_rpow_le (by positivity) (by linarith) _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ← ENNReal.rpow_natCast,
      ← ENNReal.rpow_mul]
    norm_num
    ring_nf
  calc _ ≤ ENNReal.ofReal (32 ^ (q / 4) * (mA * (KA ^ q * (KB ^ q *
        (∑ i, ∑ x, ‖G i x‖ ^ 2) ^ (q / 4))))) := ENNReal.ofReal_le_ofReal hr
    _ = ENNReal.ofReal (32 ^ (q / 4)) * (ENNReal.ofReal mA * (ENNReal.ofReal (KA ^ q) *
        (ENNReal.ofReal (KB ^ q) * ENNReal.ofReal ((∑ i, ∑ x, ‖G i x‖ ^ 2) ^ (q / 4))))) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hmA,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := by gcongr

/-- `√(xy) = √(x^{1−t} y^t) √(y^{1−t} x^t)` for `x, y ≥ 0`. -/
private lemma lcor_sqrt_split {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (t : ℝ) :
    Real.sqrt (x * y) = Real.sqrt (x ^ (1 - t) * y ^ t) * Real.sqrt (y ^ (1 - t) * x ^ t) := by
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  have h1 : x ^ (1 - t) * x ^ t = x := by
    rw [← Real.rpow_add' hx (by norm_num), sub_add_cancel, Real.rpow_one]
  have h2 : y ^ t * y ^ (1 - t) = y := by
    rw [← Real.rpow_add' hy (by norm_num), add_sub_cancel, Real.rpow_one]
  calc x * y = (x ^ (1 - t) * x ^ t) * (y ^ t * y ^ (1 - t)) := by rw [h1, h2]
    _ = _ := by ring

/-- Cauchy–Schwarz on a product measure, with the squares given as iterated integrals. -/
private lemma lcor_cs {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {m : Measure α} {n : Measure β} [SFinite m] [SFinite n] {f h : α × β → ℝ≥0∞}
    (hf : Measurable f) (hh : Measurable h) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hfx : ∫⁻ s, ∫⁻ t, f (s, t) ^ (2 : ℝ) ∂n ∂m ≤ ENNReal.ofReal x)
    (hhy : ∫⁻ s, ∫⁻ t, h (s, t) ^ (2 : ℝ) ∂n ∂m ≤ ENNReal.ofReal y) :
    ∫⁻ z, f z * h z ∂(m.prod n) ≤ ENNReal.ofReal (Real.sqrt x * Real.sqrt y) := by
  have e2 : ∫⁻ z, f z ^ (2 : ℝ) ∂(m.prod n) = ∫⁻ s, ∫⁻ t, f (s, t) ^ (2 : ℝ) ∂n ∂m :=
    lintegral_prod (fun z => f z ^ (2 : ℝ)) (hf.pow_const 2).aemeasurable
  have e3 : ∫⁻ z, h z ^ (2 : ℝ) ∂(m.prod n) = ∫⁻ s, ∫⁻ t, h (s, t) ^ (2 : ℝ) ∂n ∂m :=
    lintegral_prod (fun z => h z ^ (2 : ℝ)) (hh.pow_const 2).aemeasurable
  rw [← e2] at hfx
  rw [← e3] at hhy
  refine (ENNReal.lintegral_mul_le_Lp_mul_Lq (m.prod n) Real.HolderConjugate.two_two
    hf.aemeasurable hh.aemeasurable).trans ?_
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  refine mul_le_mul' ?_ ?_
  · calc (∫⁻ z, f z ^ (2 : ℝ) ∂(m.prod n)) ^ (1 / (2 : ℝ)) ≤ (ENNReal.ofReal x) ^ (1 / (2 : ℝ)) :=
          ENNReal.rpow_le_rpow hfx (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt x) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hx (by norm_num), Real.sqrt_eq_rpow]
  · calc (∫⁻ z, h z ^ (2 : ℝ) ∂(m.prod n)) ^ (1 / (2 : ℝ)) ≤ (ENNReal.ofReal y) ^ (1 / (2 : ℝ)) :=
          ENNReal.rpow_le_rpow hhy (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt y) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hy (by norm_num), Real.sqrt_eq_rpow]

/-- The mass `m_T(k) = ‖P_T ψ_k‖²` of the `k`-th eigenvector of the model (1.3) [eq:model]. -/
private def lcorMass (g : ℝ) {W L : ℕ} (ω : Ω W L) (T : Finset (Fin L × Fin W))
    (k : Fin L × Fin W) : ℝ :=
  ∑ p ∈ T, ‖(Hmat_isHermitian g W L ω).eigenvectorBasis k p‖ ^ 2

private lemma lcorMass_nonneg (g : ℝ) {W L : ℕ} (ω : Ω W L) (T : Finset (Fin L × Fin W))
    (k : Fin L × Fin W) : 0 ≤ lcorMass g ω T k :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `Q(A, B) ≤ Q_t(A, B)^{1/2} Q_t(B, A)^{1/2}` (Cauchy–Schwarz over the eigenpairs). -/
private lemma lcor_corr_le {g : ℝ} {W L : ℕ} (ω : Ω W L) (T₁ T₂ : Finset (Fin L × Fin W))
    (J : Set ℝ) (t : ℝ) {Y₁ Y₂ : ℝ≥0∞}
    (h₁ : ENNReal.ofReal (∑ k ∈ univ.filter (fun k => (Hmat_isHermitian g W L ω).eigenvalues k ∈ J),
      lcorMass g ω T₁ k ^ (1 - t) * lcorMass g ω T₂ k ^ t) ≤ Y₁)
    (h₂ : ENNReal.ofReal (∑ k ∈ univ.filter (fun k => (Hmat_isHermitian g W L ω).eigenvalues k ∈ J),
      lcorMass g ω T₂ k ^ (1 - t) * lcorMass g ω T₁ k ^ t) ≤ Y₂) :
    ENNReal.ofReal (eigMassCorr (Hmat g W L ω) T₁ T₂ J) ≤ Y₁ ^ (1 / 2 : ℝ) * Y₂ ^ (1 / 2 : ℝ) := by
  have hH := Hmat_isHermitian g W L ω
  set F := univ.filter (fun k => (Hmat_isHermitian g W L ω).eigenvalues k ∈ J) with hF
  have h0 : ∀ k, 0 ≤ lcorMass g ω T₁ k ^ (1 - t) * lcorMass g ω T₂ k ^ t := fun k =>
    mul_nonneg (Real.rpow_nonneg (lcorMass_nonneg _ _ _ _) _)
      (Real.rpow_nonneg (lcorMass_nonneg _ _ _ _) _)
  have h0' : ∀ k, 0 ≤ lcorMass g ω T₂ k ^ (1 - t) * lcorMass g ω T₁ k ^ t := fun k =>
    mul_nonneg (Real.rpow_nonneg (lcorMass_nonneg _ _ _ _) _)
      (Real.rpow_nonneg (lcorMass_nonneg _ _ _ _) _)
  have hQ : eigMassCorr (Hmat g W L ω) T₁ T₂ J ≤
      Real.sqrt (∑ k ∈ F, lcorMass g ω T₁ k ^ (1 - t) * lcorMass g ω T₂ k ^ t) *
        Real.sqrt (∑ k ∈ F, lcorMass g ω T₂ k ^ (1 - t) * lcorMass g ω T₁ k ^ t) := by
    simp only [eigMassCorr, hH, ↓reduceDIte]
    calc _ = ∑ k ∈ F, Real.sqrt (lcorMass g ω T₁ k ^ (1 - t) * lcorMass g ω T₂ k ^ t) *
          Real.sqrt (lcorMass g ω T₂ k ^ (1 - t) * lcorMass g ω T₁ k ^ t) :=
          Finset.sum_congr rfl fun k _ =>
            lcor_sqrt_split (lcorMass_nonneg _ _ _ _) (lcorMass_nonneg _ _ _ _) t
      _ ≤ _ := Real.sum_sqrt_mul_sqrt_le _ h0 h0'
  have hs : ∀ (S : ℝ) (Y : ℝ≥0∞), 0 ≤ S → ENNReal.ofReal S ≤ Y →
      ENNReal.ofReal (Real.sqrt S) ≤ Y ^ (1 / 2 : ℝ) := fun S Y hS hY => by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hS (by norm_num)]
    exact ENNReal.rpow_le_rpow hY (by norm_num)
  calc _ ≤ ENNReal.ofReal (Real.sqrt (∑ k ∈ F, lcorMass g ω T₁ k ^ (1 - t) *
        lcorMass g ω T₂ k ^ t) * Real.sqrt (∑ k ∈ F, lcorMass g ω T₂ k ^ (1 - t) *
          lcorMass g ω T₁ k ^ t)) := ENNReal.ofReal_le_ofReal hQ
    _ = _ * _ := ENNReal.ofReal_mul (Real.sqrt_nonneg _)
    _ ≤ _ := mul_le_mul' (hs _ _ (Finset.sum_nonneg fun k _ => h0 k) h₁)
        (hs _ _ (Finset.sum_nonneg fun k _ => h0' k) h₂)

/-! ### The bound on `𝔼 Q_t(A, B)` -/

/-- The proof of (E.3) [uva:eq:cell-correlator] for one ordered pair of cells at distance
`d ≥ 1`: with `t = q/4`, `Q_t(A, B) = Σ_{λ_k ∈ J} m_A(k)^{1−t} m_B(k)^t` is almost surely at most a
measurable `Y` with `𝔼 Y ≤ C n W^P exp(−c d/(W g²))`. -/
private lemma lcor_half {E₀ q CG cG PG : ℝ} (hE₀ : E₀ < 2) (hq0 : 0 < q) (hq1 : q < 1)
    (hCG : 0 < CG) (hcG : 0 < cG) (hPG : 0 ≤ PG) :
    ∃ C c P : ℝ, 0 < C ∧ 0 < c ∧ 2 ≤ P ∧ ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, 0 < g → 2 + 4 / (2 - E₀) ≤ g ^ 2 →
      (∀ m : ℕ, ∀ x y : Fin m,
        ∫⁻ E in Set.Icc (-E₀) E₀, ∫⁻ ω,
            ‖blockOf (resolventMat (pathOp g (gueBlock W m ω) 0 0) E) x y‖ₑ ^ q ∂(μ W m) ≤
          ENNReal.ofReal (CG * (W : ℝ) ^ PG *
            Real.exp (-cG * |((x : ℕ) : ℝ) - (y : ℕ)| / (W * g ^ 2)))) →
      ∀ L : ℕ, ∀ a b : Fin L, ∀ nA nB d : ℕ,
        ⌊g ^ 2⌋₊ ≤ nA → nA ≤ 2 * ⌊g ^ 2⌋₊ → ⌊g ^ 2⌋₊ ≤ nB → nB ≤ 2 * ⌊g ^ 2⌋₊ → 1 ≤ d →
        (∀ i < nA, ∀ j < nB, d ≤ cycDist (cellBlock a i) (cellBlock b j)) →
        ∀ J : Set ℝ, MeasurableSet J → J ⊆ Set.Icc (-E₀) E₀ →
        ∃ Y : Ω W L → ℝ≥0∞, Measurable Y ∧
          (∀ᵐ ω ∂(μ W L), ENNReal.ofReal (∑ k ∈ univ.filter
              (fun k => (Hmat_isHermitian g W L ω).eigenvalues k ∈ J),
              lcorMass g ω (cellCoords a nA) k ^ (1 - q / 4) *
                lcorMass g ω (cellCoords b nB) k ^ (q / 4)) ≤ Y ω) ∧
          ∫⁻ ω, Y ω ∂(μ W L) ≤
            ENNReal.ofReal (C * ⌊g ^ 2⌋₊ * (W : ℝ) ^ P * Real.exp (-c * d / (W * g ^ 2))) := by
  obtain ⟨Cr, hCr, Wr, havg⟩ := cell_average hE₀ (r := q) hq0.le
  have hκ : 0 < 2 - E₀ := by linarith
  obtain ⟨CK, hCK, hmom⟩ := transferWeight_moment hκ (p := 2 * q) (by positivity)
  refine ⟨32 ^ (q / 4) * Cr * 2 * 4 * Real.sqrt (4 * CK) * Real.sqrt CG *
    Real.exp (cG / 2), cG / 2, 2 + PG / 2, by positivity, by positivity, by linarith,
    max Wr 4, ?_⟩
  intro W hW g hg0 hgM hpath L a b nA nB d hnA1 hnAu hnB1 hnBu hd1 hd J hJ hJE
  -- thresholds
  have hWr : Wr ≤ W := le_trans (le_max_left _ _) hW
  have hW4 : 4 ≤ W := le_trans (le_max_right _ _) hW
  have hW4' : (4 : ℝ) ≤ W := by exact_mod_cast hW4
  have hW0 : (0 : ℝ) < W := by linarith
  have h4κ : 0 ≤ 4 / (2 - E₀) := by positivity
  have hgg : 2 ≤ g ^ 2 := by linarith
  have hg1 : 1 ≤ g := by nlinarith
  have hgκ : 2 / Real.sqrt (2 - E₀) ≤ g := by
    have hs : 0 < Real.sqrt (2 - E₀) := Real.sqrt_pos.mpr hκ
    rw [div_le_iff₀ hs]
    have h1 : 4 ≤ g ^ 2 * (2 - E₀) := by
      have h2 : 4 / (2 - E₀) ≤ g ^ 2 := by linarith
      rw [div_le_iff₀ hκ] at h2
      linarith
    have h2 : (g * Real.sqrt (2 - E₀)) ^ 2 = g ^ 2 * (2 - E₀) := by
      rw [mul_pow, Real.sq_sqrt hκ.le]
    nlinarith [mul_pos hg0 hs]
  have hn2 : 2 ≤ ⌊g ^ 2⌋₊ := Nat.le_floor (by exact_mod_cast hgg)
  have hnle : (⌊g ^ 2⌋₊ : ℝ) ≤ g ^ 2 := Nat.floor_le (by positivity)
  have hnlt : g ^ 2 < ⌊g ^ 2⌋₊ + 1 := Nat.lt_floor_add_one _
  have hn2' : (2 : ℝ) ≤ ⌊g ^ 2⌋₊ := by exact_mod_cast hn2
  have hnA2 : 2 ≤ nA := le_trans hn2 hnA1
  have hnB2 : 2 ≤ nB := le_trans hn2 hnB1
  have hgA : g ^ 2 / 2 ≤ nA := by
    have : (⌊g ^ 2⌋₊ : ℝ) ≤ nA := by exact_mod_cast hnA1
    linarith
  have hAg : (nA : ℝ) ≤ 2 * g ^ 2 := by
    have : (nA : ℝ) ≤ 2 * ⌊g ^ 2⌋₊ := by exact_mod_cast hnAu
    linarith
  have hBg : (nB : ℝ) ≤ 2 * g ^ 2 := by
    have : (nB : ℝ) ≤ 2 * ⌊g ^ 2⌋₊ := by exact_mod_cast hnBu
    linarith
  have hb1 : 1 ≤ (W : ℝ) * g ^ 2 := by nlinarith
  have hJ4 : volume J ≤ ENNReal.ofReal 4 :=
    (measure_mono hJE).trans
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_le_ofReal (by linarith))
  -- the cell `B` inside `Λ = ℤ_L ∖ A`
  obtain ⟨j₀, hL, rfl, hdj, hdL⟩ := lcor_geom a b (by omega) hnB2 hd1 hd
  have hnAL : nA < L := by omega
  have hsinj : Function.Injective fun j : Fin (L - nA) => cellBlock a (nA + j) := by
    intro i j hij
    have := lcor_cellBlock_inj a (by have := i.isLt; omega) (by have := j.isLt; omega) hij
    exact Fin.ext (by omega)
  -- the exterior weight `f(E) = K_B(E)^{4t} Σ_{b, x} ‖G_Λ(b, x; E)‖^{2t}`, `t = q/4`
  obtain ⟨f, hfdef⟩ : ∃ f : ℝ → Ω W L → ℝ≥0∞, f = fun E ω =>
      ENNReal.ofReal (cellWeight g E ω (cellBlock a (nA + j₀)) nB ^ q) *
        ∑ i : Fin 2, ∑ x : Fin 2, ‖blockOf (resolventMat (pathOp g
          (fun j : Fin (L - nA) => gueBlock W L ω (cellBlock a (nA + j))) 0 0) E)
          ⟨j₀ + i, by have := i.isLt; omega⟩
          (if x = 0 then ⟨0, by omega⟩ else ⟨L - nA - 1, by omega⟩)‖ₑ ^ (q / 2) := ⟨_, rfl⟩
  have hfm : ∀ {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
      {Ef : X → ℝ} {ωf : X → Ω W L}, Continuous Ef → Continuous ωf →
        Measurable fun x => f (Ef x) (ωf x) := by
    intro X _ _ _ Ef ωf hE hω
    rw [hfdef]
    exact (lcor_measurable_weight g hE hω _ nB q).mul (Finset.measurable_sum _ fun i _ =>
      Finset.measurable_sum _ fun x _ => lcor_measurable_green g hE
        (V := fun z => fun j : Fin (L - nA) => gueBlock W L (ωf z) (cellBlock a (nA + j)))
        (continuous_pi fun j => (lcor_continuous_gueBlock _).comp hω) _ _ _)
  have hext : ∀ E (ω ω' : Ω W L), (∀ p : Fin L × Fin W × Fin W,
      p.1 ∉ Set.range (cellWindow a nA) → ω p = ω' p) → f E ω = f E ω' := by
    intro E ω ω' h
    have h1 : cellWeight g E ω (cellBlock a (nA + j₀)) nB =
        cellWeight g E ω' (cellBlock a (nA + j₀)) nB := by
      unfold cellWeight
      refine lcor_transferWeight_congr fun j hj => lcor_gueBlock_ext h ?_
      rw [lcor_cellBlock_cellBlock]
      exact lcor_not_mem_range a (by omega) (by omega)
    have h2 : (fun j : Fin (L - nA) => gueBlock W L ω (cellBlock a (nA + j))) =
        fun j : Fin (L - nA) => gueBlock W L ω' (cellBlock a (nA + j)) := by
      funext j
      exact lcor_gueBlock_ext h (lcor_not_mem_range a (by omega) (by have := j.isLt; omega))
    rw [hfdef]
    simp only [h1, h2]
  refine ⟨fun ω => ENNReal.ofReal (32 ^ (q / 4)) * eigMassSum (Hmat g W L ω) (cellCoords a nA)
      (J.indicator fun E => ENNReal.ofReal (cellWeight g E ω a nA ^ q) * f E ω), ?_, ?_, ?_⟩
  · -- measurability
    have hG : Measurable (Function.uncurry fun (ω : Ω W L) (E : ℝ) => J.indicator
        (fun E => ENNReal.ofReal (cellWeight g E ω a nA ^ q) * f E ω) E) := by
      simp only [Function.uncurry_def, Set.indicator_apply]
      exact Measurable.ite (measurable_snd hJ)
        ((lcor_measurable_weight g continuous_snd continuous_fst a nA q).mul
          (hfm continuous_snd continuous_fst)) measurable_const
    exact measurable_const.mul (measurable_eigMassSum (continuous_Hmat g W L).measurable _ hG)
  · -- (E.4) [uva:eq:ratio-audit] for every eigenpair, almost surely
    filter_upwards [ae_cellExterior_det_ne_zero hg0 hnA2 hnAL a] with ω hω
    have hH := Hmat_isHermitian g W L ω
    rw [ENNReal.ofReal_sum_of_nonneg fun k _ => mul_nonneg
      (Real.rpow_nonneg (lcorMass_nonneg _ _ _ _) _) (Real.rpow_nonneg (lcorMass_nonneg _ _ _ _) _)]
    simp only [eigMassSum, hH, ↓reduceDIte]
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_le_sum fun k _ => ?_
    split_ifs with hk
    · rw [Set.indicator_of_mem hk, hfdef]
      have hψ : Hdet g (gueBlock W L ω) *ᵥ (hH.eigenvectorBasis k).ofLp =
          ((hH.eigenvalues k : ℝ) : ℂ) • (hH.eigenvectorBasis k).ofLp := by
        rw [show Hdet g (gueBlock W L ω) = Hmat g W L ω from rfl, hH.mulVec_eigenvectorBasis k]
        exact (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _)
      have hr := cell_mass_ratio hg1 (gueBlock W L ω) a hnA2 hnB2 hL hψ (hω k)
      exact lcor_pointwise (lcorMass_nonneg _ _ _ _) (lcorMass_nonneg _ _ _ _)
        (lcor_weight_nonneg _ _ _ _ _) (lcor_weight_nonneg _ _ _ _ _)
        (by exact_mod_cast (show 0 < nA by omega))
        (by exact_mod_cast (show nB ≤ 2 * nA by omega)) hq0 hq1
        (fun i x => blockOf (resolventMat (pathOp g
          (fun j : Fin (L - nA) => gueBlock W L ω (cellBlock a (nA + j))) 0 0) (hH.eigenvalues k))
          ⟨j₀ + i, by have := i.isLt; omega⟩
          (if x = 0 then ⟨0, by omega⟩ else ⟨L - nA - 1, by omega⟩)) hr
    · exact zero_le
  · -- the expectation: (E.6) [uva:eq:average], then Cauchy–Schwarz on `J × Ω`
    beta_reduce
    have hf_meas : Measurable (Function.uncurry f) := hfm continuous_fst continuous_snd
    have hca := havg W hWr g hgκ L nA hnA2 hgA hAg hnAL a J hJ hJE f hf_meas hext
    set D : ℝ := Real.sqrt (4 * CK) * Real.sqrt (CG * (W : ℝ) ^ PG *
      Real.exp (-cG * ((d : ℝ) - 1) / (W * g ^ 2))) with hD
    have hterm : ∀ i x : Fin 2, ∫⁻ z, ENNReal.ofReal
        (cellWeight g z.1 z.2 (cellBlock a (nA + j₀)) nB ^ q) *
        ‖blockOf (resolventMat (pathOp g
          (fun j : Fin (L - nA) => gueBlock W L z.2 (cellBlock a (nA + j))) 0 0) z.1)
          ⟨j₀ + i, by have := i.isLt; omega⟩
          (if x = 0 then ⟨0, by omega⟩ else ⟨L - nA - 1, by omega⟩)‖ₑ ^ (q / 2)
          ∂((volume.restrict J).prod (μ W L)) ≤ ENNReal.ofReal D := by
      intro i x
      set yI : Fin (L - nA) := ⟨j₀ + i, by have := i.isLt; omega⟩ with hyI
      set xI : Fin (L - nA) := if x = 0 then ⟨0, by omega⟩ else ⟨L - nA - 1, by omega⟩ with hxI
      refine lcor_cs (lcor_measurable_weight g continuous_fst continuous_snd _ nB q)
        (lcor_measurable_green g continuous_fst
          (V := fun z : ℝ × Ω W L => fun j : Fin (L - nA) =>
            gueBlock W L z.2 (cellBlock a (nA + j)))
          (continuous_pi fun j => (lcor_continuous_gueBlock _).comp continuous_snd) _ _ _)
        (by positivity) (by positivity) ?_ ?_
      · -- the moment of `K_B`, Lemma 7.2 [uvs:lem:transfer-moments]
        calc _ = ∫⁻ E in J, ∫⁻ ω, ENNReal.ofReal
              (cellWeight g E ω (cellBlock a (nA + j₀)) nB ^ (2 * q)) ∂(μ W L) := by
              refine lintegral_congr fun E => lintegral_congr fun ω => ?_
              have h0 := lcor_weight_nonneg g E ω (cellBlock a (nA + j₀)) nB
              rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
                ← Real.rpow_mul h0, mul_comm]
          _ ≤ ∫⁻ E in J, ENNReal.ofReal CK := by
              refine setLIntegral_mono measurable_const fun E hE => ?_
              refine hmom W L (by linarith) (cellBlock (cellBlock a (nA + j₀))) nB ?_ g hgκ hBg E ?_
              · intro i hi j hj hij
                have hi' : i < nB := hi
                have hj' : j < nB := hj
                exact lcor_cellBlock_inj _ (by omega) (by omega) hij
              · have := hJE hE
                rw [abs_le]
                constructor <;> linarith [this.1, this.2]
          _ ≤ ENNReal.ofReal (4 * CK) := by
              rw [setLIntegral_const, ENNReal.ofReal_mul (p := 4) (by norm_num),
                mul_comm (ENNReal.ofReal 4)]
              exact mul_le_mul_right hJ4 _
      · -- the path bound on `Λ`, through the window of its blocks
        have hG := (lintegral_mono_set hJE).trans (hpath (L - nA) yI xI)
        have hdist : (d : ℝ) - 1 ≤ |((yI : ℕ) : ℝ) - ((xI : ℕ) : ℝ)| := by
          have hy : (yI : ℕ) = j₀ + i := rfl
          have hi1 : (i : ℕ) ≤ 1 := by have := i.isLt; omega
          have h3 : ((i : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hi1
          have h4 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
          rw [hy]
          by_cases hx : x = 0
          · have hx' : (xI : ℕ) = 0 := by simp [hxI, hx]
            rw [hx']
            have : (d : ℝ) ≤ j₀ + 1 := by exact_mod_cast hdj
            rw [Nat.cast_zero, sub_zero, abs_of_nonneg (by positivity)]
            push_cast
            linarith
          · have hx' : (xI : ℕ) = L - nA - 1 := by simp [hxI, hx]
            rw [hx']
            have h1 : ((L - nA - 1 : ℕ) : ℝ) = (L : ℝ) - nA - 1 := by
              rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
              push_cast
              ring
            have h2 : (d : ℝ) + nA + j₀ + 1 ≤ L := by exact_mod_cast hdL
            have h5 : (1 : ℝ) ≤ d := by exact_mod_cast hd1
            rw [h1, abs_sub_comm, abs_of_nonneg (by push_cast; linarith)]
            push_cast
            linarith
        have hexp : Real.exp (-cG * |((yI : ℕ) : ℝ) - ((xI : ℕ) : ℝ)| / (W * g ^ 2)) ≤
            Real.exp (-cG * ((d : ℝ) - 1) / (W * g ^ 2)) := by
          have h1 : -cG * |((yI : ℕ) : ℝ) - ((xI : ℕ) : ℝ)| ≤ -cG * ((d : ℝ) - 1) := by nlinarith
          exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right h1 (by positivity))
        calc _ = ∫⁻ E in J, ∫⁻ v, ‖blockOf (resolventMat (pathOp g (gueBlock W (L - nA) v) 0 0) E)
              yI xI‖ₑ ^ q ∂(μ W (L - nA)) := by
              refine lintegral_congr fun E => ?_
              refine Eq.trans ?_ ((measurePreserving_windowSample W L (L - nA) hsinj).lintegral_comp
                (lcor_measurable_green g continuous_const
                  (V := fun v : Ω W (L - nA) => gueBlock W (L - nA) v)
                  (continuous_pi fun j => lcor_continuous_gueBlock j) yI xI q))
              refine lintegral_congr fun ω => ?_
              rw [← ENNReal.rpow_mul, show q / 2 * 2 = q by ring]
              rfl
          _ ≤ _ := hG
          _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hexp (by positivity))
    have hmeas : ∀ i x : Fin 2, Measurable fun z : ℝ × Ω W L => ENNReal.ofReal
        (cellWeight g z.1 z.2 (cellBlock a (nA + j₀)) nB ^ q) *
        ‖blockOf (resolventMat (pathOp g
          (fun j : Fin (L - nA) => gueBlock W L z.2 (cellBlock a (nA + j))) 0 0) z.1)
          ⟨j₀ + i, by have := i.isLt; omega⟩
          (if x = 0 then ⟨0, by omega⟩ else ⟨L - nA - 1, by omega⟩)‖ₑ ^ (q / 2) := fun i x =>
      (lcor_measurable_weight g continuous_fst continuous_snd _ nB q).mul
        (lcor_measurable_green g continuous_fst
          (V := fun z : ℝ × Ω W L => fun j : Fin (L - nA) =>
            gueBlock W L z.2 (cellBlock a (nA + j)))
          (continuous_pi fun j => (lcor_continuous_gueBlock _).comp continuous_snd) _ _ _)
    have hint : ∫⁻ ω, (∫⁻ E in J, f E ω) ∂(μ W L) ≤ ENNReal.ofReal (4 * D) := by
      calc ∫⁻ ω, (∫⁻ E in J, f E ω) ∂(μ W L) = ∫⁻ E in J, ∫⁻ ω, f E ω ∂(μ W L) :=
            lintegral_lintegral_swap (hfm continuous_snd continuous_fst).aemeasurable
        _ = ∫⁻ z, f z.1 z.2 ∂((volume.restrict J).prod (μ W L)) :=
            (lintegral_prod _ hf_meas.aemeasurable).symm
        _ = ∑ i : Fin 2, ∑ x : Fin 2, ∫⁻ z, ENNReal.ofReal
              (cellWeight g z.1 z.2 (cellBlock a (nA + j₀)) nB ^ q) *
              ‖blockOf (resolventMat (pathOp g
                (fun j : Fin (L - nA) => gueBlock W L z.2 (cellBlock a (nA + j))) 0 0) z.1)
                ⟨j₀ + i, by have := i.isLt; omega⟩
                (if x = 0 then ⟨0, by omega⟩ else ⟨L - nA - 1, by omega⟩)‖ₑ ^ (q / 2)
                ∂((volume.restrict J).prod (μ W L)) := by
            rw [hfdef]
            simp only [Finset.mul_sum]
            refine (lintegral_finsetSum _ fun i _ => ?_).trans
              (Finset.sum_congr rfl fun i _ => ?_)
            · exact Finset.measurable_sum _ fun x _ => hmeas i x
            · exact lintegral_finsetSum _ fun x _ => hmeas i x
        _ ≤ ∑ i : Fin 2, ∑ x : Fin 2, ENNReal.ofReal D :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun x _ => hterm i x
        _ = ENNReal.ofReal (4 * D) := by
            rw [ENNReal.ofReal_mul (p := 4) (by norm_num), ENNReal.ofReal_ofNat]
            simp only [Fin.sum_univ_two]
            ring
    have hsqrt : Real.sqrt (CG * (W : ℝ) ^ PG * Real.exp (-cG * ((d : ℝ) - 1) / (W * g ^ 2))) ≤
        Real.sqrt CG * (W : ℝ) ^ (PG / 2) *
          (Real.exp (cG / 2) * Real.exp (-(cG / 2) * d / (W * g ^ 2))) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hCG.le]
      have h1 : Real.sqrt ((W : ℝ) ^ PG) = (W : ℝ) ^ (PG / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hW0.le]
        ring_nf
      have h2 : Real.sqrt (Real.exp (-cG * ((d : ℝ) - 1) / (W * g ^ 2))) ≤
          Real.exp (cG / 2) * Real.exp (-(cG / 2) * d / (W * g ^ 2)) := by
        rw [Real.sqrt_eq_rpow, ← Real.exp_mul, ← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have h3 : cG / (W * g ^ 2) ≤ cG := div_le_self hcG.le hb1
        have e : -cG * ((d : ℝ) - 1) / (W * g ^ 2) * (1 / 2) =
            cG / (W * g ^ 2) / 2 + -(cG / 2) * d / (W * g ^ 2) := by ring
        rw [e]
        linarith
      rw [h1]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have hnA' : (nA : ℝ) ≤ 2 * ⌊g ^ 2⌋₊ := by exact_mod_cast hnAu
    have hreal : 32 ^ (q / 4) * (Cr * nA * (W : ℝ) ^ 2) * (4 * D) ≤
        32 ^ (q / 4) * Cr * 2 * 4 * Real.sqrt (4 * CK) * Real.sqrt CG * Real.exp (cG / 2) *
          ⌊g ^ 2⌋₊ * (W : ℝ) ^ (2 + PG / 2) * Real.exp (-(cG / 2) * d / (W * g ^ 2)) := by
      rw [hD]
      calc _ ≤ 32 ^ (q / 4) * (Cr * (2 * ⌊g ^ 2⌋₊) * (W : ℝ) ^ 2) * (4 * (Real.sqrt (4 * CK) *
            (Real.sqrt CG * (W : ℝ) ^ (PG / 2) *
              (Real.exp (cG / 2) * Real.exp (-(cG / 2) * d / (W * g ^ 2)))))) := by gcongr
        _ = _ := by
            rw [Real.rpow_add hW0, Real.rpow_two]
            ring
    calc ∫⁻ ω, ENNReal.ofReal (32 ^ (q / 4)) * eigMassSum (Hmat g W L ω) (cellCoords a nA)
          (J.indicator fun E => ENNReal.ofReal (cellWeight g E ω a nA ^ q) * f E ω) ∂(μ W L)
        = ENNReal.ofReal (32 ^ (q / 4)) * ∫⁻ ω, eigMassSum (Hmat g W L ω) (cellCoords a nA)
          (J.indicator fun E => ENNReal.ofReal (cellWeight g E ω a nA ^ q) * f E ω) ∂(μ W L) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (32 ^ (q / 4)) * (ENNReal.ofReal (Cr * nA * (W : ℝ) ^ 2) *
          ENNReal.ofReal (4 * D)) := mul_le_mul_right (hca.trans (mul_le_mul_right hint _)) _
      _ = ENNReal.ofReal (32 ^ (q / 4) * (Cr * nA * (W : ℝ) ^ 2) * (4 * D)) := by
          rw [ENNReal.ofReal_mul (p := 32 ^ (q / 4) * (Cr * nA * (W : ℝ) ^ 2)) (by positivity),
            ENNReal.ofReal_mul (p := 32 ^ (q / 4)) (by positivity)]
          exact (mul_assoc _ _ _).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-- The cell-correlator bound of Appendix E.1 [app:fr-concentration-proof], (E.3)
[uva:eq:cell-correlator] to (E.13) [uva:eq:weight-audit], from the path bound (8.3)
[uva:eq:conversion-input] at the exponent `q`: for fixed `E₀ < 2`,
`q ∈ (0, 1)` and path constants, `𝔼 Q(A, B) ≤ C n W^P exp(−c d/(W g²))` for cells
`A = a, …, a+n_A−1` and `B = b, …, b+n_B−1` with `n ≤ n_A, n_B ≤ 2n`, `n = ⌊g²⌋`, and
`d ≤ ‖a′ − b′‖_L` for all blocks `a′ ∈ A`, `b′ ∈ B`, at every `g > 0` with
`g² ≥ 2 + 4/(2 − E₀)` where the path bound holds. -/
theorem cell_correlator_of_path {E₀ q CG cG PG : ℝ} (hE₀ : E₀ < 2) (hq0 : 0 < q) (hq1 : q < 1)
    (hCG : 0 < CG) (hcG : 0 < cG) (hPG : 0 ≤ PG) :
    ∃ C c P : ℝ, 0 < C ∧ 0 < c ∧ 0 < P ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ g : ℝ, 0 < g → 2 + 4 / (2 - E₀) ≤ g ^ 2 →
      (∀ m : ℕ, ∀ x y : Fin m,
        ∫⁻ E in Set.Icc (-E₀) E₀, ∫⁻ ω,
            ‖blockOf (resolventMat (pathOp g (gueBlock W m ω) 0 0) E) x y‖ₑ ^ q ∂(μ W m) ≤
          ENNReal.ofReal (CG * (W : ℝ) ^ PG *
            Real.exp (-cG * |((x : ℕ) : ℝ) - (y : ℕ)| / (W * g ^ 2)))) →
      ∀ L : ℕ, ∀ a b : Fin L, ∀ nA nB d : ℕ,
        ⌊g ^ 2⌋₊ ≤ nA → nA ≤ 2 * ⌊g ^ 2⌋₊ → ⌊g ^ 2⌋₊ ≤ nB → nB ≤ 2 * ⌊g ^ 2⌋₊ →
        (∀ i < nA, ∀ j < nB, d ≤ cycDist (cellBlock a i) (cellBlock b j)) →
        ∀ J : Set ℝ, MeasurableSet J → J ⊆ Set.Icc (-E₀) E₀ →
          ∫⁻ ω, ENNReal.ofReal
              (eigMassCorr (Hmat g W L ω) (cellCoords a nA) (cellCoords b nB) J) ∂(μ W L) ≤
            ENNReal.ofReal (C * ⌊g ^ 2⌋₊ * (W : ℝ) ^ P * Real.exp (-c * d / (W * g ^ 2))) := by
  obtain ⟨C, c, P, hC, hc, hP, W₀, hH⟩ := lcor_half hE₀ hq0 hq1 hCG hcG hPG
  refine ⟨C + 2, c, P, by linarith, hc, by linarith, max W₀ 1, ?_⟩
  intro W hW g hg0 hgM hpath L a b nA nB d hnA1 hnA2 hnB1 hnB2 hd J hJ hJE
  have hW₀ : W₀ ≤ W := le_trans (le_max_left _ _) hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_trans (le_max_right _ _) hW
  have hWP : (W : ℝ) ≤ (W : ℝ) ^ P := by
    calc (W : ℝ) = (W : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (W : ℝ) ^ P := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  rcases Nat.eq_zero_or_pos d with rfl | hd1
  · -- `d = 0`: the deterministic bound `Q ≤ 2 n W`
    have hn : (0 : ℝ) ≤ ⌊g ^ 2⌋₊ := Nat.cast_nonneg _
    have hcard : ∀ (c : Fin L) (m : ℕ), m ≤ 2 * ⌊g ^ 2⌋₊ →
        ((cellCoords (W := W) c m).card : ℝ) ≤ 2 * ⌊g ^ 2⌋₊ * W := fun c m hm => by
      have h1 := lcor_card_cellCoords (W := W) c m
      have h2 : m * W ≤ 2 * ⌊g ^ 2⌋₊ * W := Nat.mul_le_mul_right _ hm
      exact_mod_cast h1.trans h2
    have hQ : ∀ ω, eigMassCorr (Hmat g W L ω) (cellCoords a nA) (cellCoords b nB) J ≤
        2 * ⌊g ^ 2⌋₊ * W := fun ω => by
      refine (eigMassCorr_le_sqrt_card _ _ _ _).trans ?_
      calc Real.sqrt ((cellCoords (W := W) a nA).card * (cellCoords (W := W) b nB).card)
          ≤ Real.sqrt ((2 * ⌊g ^ 2⌋₊ * W) * (2 * ⌊g ^ 2⌋₊ * W)) :=
            Real.sqrt_le_sqrt (mul_le_mul (hcard a nA hnA2) (hcard b nB hnB2) (Nat.cast_nonneg _)
              (by positivity))
        _ = 2 * ⌊g ^ 2⌋₊ * W := Real.sqrt_mul_self (by positivity)
    calc ∫⁻ ω, ENNReal.ofReal (eigMassCorr (Hmat g W L ω) (cellCoords a nA) (cellCoords b nB) J)
          ∂(μ W L) ≤ ∫⁻ _, ENNReal.ofReal (2 * ⌊g ^ 2⌋₊ * W) ∂(μ W L) :=
          lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hQ ω)
      _ = ENNReal.ofReal (2 * ⌊g ^ 2⌋₊ * W) := by rw [lintegral_const, measure_univ, mul_one]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Nat.cast_zero, mul_zero, zero_div, Real.exp_zero, mul_one]
          have h1 : 2 * (⌊g ^ 2⌋₊ : ℝ) * W ≤ 2 * ⌊g ^ 2⌋₊ * W ^ P :=
            mul_le_mul_of_nonneg_left hWP (by positivity)
          have h2 : 0 ≤ C * (⌊g ^ 2⌋₊ : ℝ) * W ^ P := by positivity
          nlinarith
  · -- `d ≥ 1`: `Q(A, B) ≤ Q_t(A, B)^{1/2} Q_t(B, A)^{1/2}` and Cauchy–Schwarz in probability
    obtain ⟨Y₁, hY₁, hY₁ae, hY₁int⟩ := hH W hW₀ g hg0 hgM hpath L a b nA nB d hnA1 hnA2 hnB1
      hnB2 hd1 hd J hJ hJE
    obtain ⟨Y₂, hY₂, hY₂ae, hY₂int⟩ := hH W hW₀ g hg0 hgM hpath L b a nB nA d hnB1 hnB2 hnA1
      hnA2 hd1 (fun j hj i hi => (hd i hi j hj).trans_eq (lcor_cycDist_comm _ _)) J hJ hJE
    set B := ENNReal.ofReal (C * ⌊g ^ 2⌋₊ * (W : ℝ) ^ P * Real.exp (-c * d / (W * g ^ 2)))
      with hB
    calc ∫⁻ ω, ENNReal.ofReal (eigMassCorr (Hmat g W L ω) (cellCoords a nA) (cellCoords b nB) J)
          ∂(μ W L) ≤ ∫⁻ ω, (fun ω => Y₁ ω ^ (1 / 2 : ℝ)) ω * (fun ω => Y₂ ω ^ (1 / 2 : ℝ)) ω
            ∂(μ W L) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hY₁ae, hY₂ae] with ω h1 h2
          exact lcor_corr_le ω _ _ J (q / 4) h1 h2
      _ ≤ (∫⁻ ω, (Y₁ ω ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂(μ W L)) ^ (1 / (2 : ℝ)) *
          (∫⁻ ω, (Y₂ ω ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂(μ W L)) ^ (1 / (2 : ℝ)) :=
          ENNReal.lintegral_mul_le_Lp_mul_Lq _ Real.HolderConjugate.two_two
            (hY₁.pow_const _).aemeasurable (hY₂.pow_const _).aemeasurable
      _ = (∫⁻ ω, Y₁ ω ∂(μ W L)) ^ (1 / (2 : ℝ)) * (∫⁻ ω, Y₂ ω ∂(μ W L)) ^ (1 / (2 : ℝ)) := by
          simp_rw [← ENNReal.rpow_mul]
          norm_num
      _ ≤ B ^ (1 / (2 : ℝ)) * B ^ (1 / (2 : ℝ)) := by
          gcongr
      _ = B := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
          norm_num
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          gcongr
          linarith

end LSBA
