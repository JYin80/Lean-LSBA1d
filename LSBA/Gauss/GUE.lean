import LSBA.Model.Basic

/-!
# Coordinates of the GUE blocks

The block-diagonal GUE part `V = diag(V_a)` of (1.3) [eq:model], a Hilbert–Schmidt orthonormal
basis of the Hermitian `W × W` matrices matching the real coordinates of `gueBlock` (1.2)
[eq:covariance], the inverse coordinate map, the matrix `A + √s V` of the single-time
realization of (5.1) [fo:eq:flow], and the trace identities used in (C.1) [gc:eq:divergence] and
Appendix D.2 [sec:rough-density-proof].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

noncomputable section

open scoped Classical

namespace LSBA

/-- Block-diagonal GUE part `V = diag(V_a)`. -/
def blockV (W L : ℕ) (ω : Ω W L) : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  blockDiagOp (gueBlock W L ω)

/-- `A + √s V`; at `s = tγ_g` and `A = A_g ⊗ I` this is the single-time matrix `H_t` of (5.1)
[fo:eq:flow]. -/
def blockFlow (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (s : ℝ) (ω : Ω W L) :
    Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  A + ((Real.sqrt s : ℝ) : ℂ) • blockV W L ω

/-- Hilbert–Schmidt orthonormal basis of Hermitian `W × W` matrices matching `gueBlock`. -/
def hermBasis (W : ℕ) (k : Fin W × Fin W) : Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun i j =>
    if k.1 = k.2 then (if i = k.1 ∧ j = k.1 then 1 else 0)
    else if k.1 < k.2 then
      (if (i = k.1 ∧ j = k.2) ∨ (i = k.2 ∧ j = k.1) then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0)
    else
      (if i = k.2 ∧ j = k.1 then Complex.I * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
       else if i = k.1 ∧ j = k.2 then -Complex.I * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0)

/-- `hermBasis W k` placed in block `c`. -/
def blockBasis (W L : ℕ) (c : Fin L) (k : Fin W × Fin W) :
    Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  Matrix.of fun p q => if p.1 = c ∧ q.1 = c then hermBasis W k p.2 q.2 else 0

/-- Inverse coordinate map: reads the Gaussian coordinates off Hermitian blocks. -/
def gueCoord (W L : ℕ) (V : Fin L → Matrix (Fin W) (Fin W) ℂ) : Ω W L := fun x =>
  if x.2.1 = x.2.2 then Real.sqrt W * (V x.1 x.2.1 x.2.1).re
  else if x.2.1 < x.2.2 then Real.sqrt (2 * W) * (V x.1 x.2.1 x.2.2).re
  else Real.sqrt (2 * W) * (V x.1 x.2.2 x.2.1).im

/-- Entries of `hermBasis` on the diagonal. -/
private theorem hermBasis_apply_diag (W : ℕ) (k : Fin W × Fin W) (i : Fin W) :
    hermBasis W k i i = if k = (i, i) then 1 else 0 := by
  obtain ⟨a, b⟩ := k
  simp only [hermBasis, Matrix.of_apply, Prod.mk.injEq]
  by_cases ha : i = a <;> by_cases hb : i = b <;> rcases lt_trichotomy a b with h | h | h <;>
    simp_all [eq_comm]

/-- Entries of `hermBasis` above the diagonal. -/
private theorem hermBasis_apply_lt (W : ℕ) (k : Fin W × Fin W) {i j : Fin W} (hij : i < j) :
    hermBasis W k i j = (if k = (i, j) then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0) +
      (if k = (j, i) then Complex.I * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0) := by
  by_cases h1 : k = (i, j)
  · subst h1; simp [hermBasis, hij.ne, hij.ne', hij]
  by_cases h2 : k = (j, i)
  · subst h2; simp [hermBasis, hij.ne, hij.ne', not_lt_of_gt hij]
  obtain ⟨a, b⟩ := k
  simp only [Prod.mk.injEq] at h1 h2
  simp only [hermBasis, Matrix.of_apply, Prod.mk.injEq, h1, h2, ite_false, add_zero]
  have := hij.ne
  split_ifs <;> simp_all
  omega

/-- Entries of `hermBasis` below the diagonal. -/
private theorem hermBasis_apply_gt (W : ℕ) (k : Fin W × Fin W) {i j : Fin W} (hij : j < i) :
    hermBasis W k i j = (if k = (j, i) then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0) +
      (if k = (i, j) then -Complex.I * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0) := by
  by_cases h1 : k = (j, i)
  · subst h1; simp [hermBasis, hij.ne, hij.ne', hij]
  by_cases h2 : k = (i, j)
  · subst h2; simp [hermBasis, hij.ne, hij.ne', not_lt_of_gt hij]
  obtain ⟨a, b⟩ := k
  simp only [Prod.mk.injEq] at h1 h2
  simp only [hermBasis, Matrix.of_apply, Prod.mk.injEq, h1, h2, ite_false, add_zero]
  have := hij.ne
  split_ifs <;> simp_all
  omega

private theorem sqrt_two_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem hermBasis_isHermitian (W : ℕ) (k : Fin W × Fin W) : (hermBasis W k).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [hermBasis_apply_lt _ _ h, hermBasis_apply_gt _ _ h]
    split_ifs <;> simp [Complex.conj_ofReal]
  · rw [hermBasis_apply_diag]; split_ifs <;> simp
  · rw [hermBasis_apply_lt _ _ h, hermBasis_apply_gt _ _ h]
    split_ifs <;> simp [Complex.conj_ofReal]

/-- Completeness in entries: `Σ_k (T_k)_{ij} (T_k)_{lm} = δ_{im} δ_{jl}`. -/
theorem sum_hermBasis_apply_mul_apply (W : ℕ) (i j l m : Fin W) :
    ∑ k : Fin W × Fin W, hermBasis W k i j * hermBasis W k l m =
      if i = m ∧ j = l then 1 else 0 := by
  rcases lt_trichotomy i j with h | h | h <;> rcases lt_trichotomy l m with h' | h' | h' <;>
  simp only [hermBasis_apply_lt, hermBasis_apply_gt, hermBasis_apply_diag, *, mul_add, add_mul,
      ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, Prod.mk.injEq] <;>
  by_cases a1 : l = i <;> by_cases a2 : l = j <;> by_cases a3 : m = i <;> by_cases a4 : m = j <;>
    by_cases a5 : i = j <;>
    first | (exfalso; omega) |
      (simp [a1, a2, a3, a4, a5, eq_comm (a := i), eq_comm (a := j) (b := i)]
       <;> first | omega | (ring_nf; simp [Complex.I_sq, sqrt_two_sq]; try norm_num))

theorem trace_hermBasis_mul (W : ℕ) (k l : Fin W × Fin W) :
    (hermBasis W k * hermBasis W l).trace = if k = l then 1 else 0 := by
  let M : Matrix (Fin W × Fin W) (Fin W × Fin W) ℂ :=
    Matrix.of fun k ij => hermBasis W k ij.1 ij.2
  let P : Matrix (Fin W × Fin W) (Fin W × Fin W) ℂ :=
    Matrix.of fun ij lm => if ij.1 = lm.2 ∧ ij.2 = lm.1 then 1 else 0
  have hMM : M.transpose * M = P := by
    ext ⟨i, j⟩ ⟨l, m⟩
    simp only [Matrix.mul_apply, Matrix.transpose_apply, M, P, Matrix.of_apply]
    exact sum_hermBasis_apply_mul_apply W i j l m
  have hPP : P * P = 1 := by
    ext ⟨i, j⟩ ⟨l, m⟩
    simp only [Matrix.mul_apply, P, Matrix.of_apply, Matrix.one_apply, Fintype.sum_prod_type]
    simp [ite_and, Prod.ext_iff]
  have h1 : (P * M.transpose) * M = 1 := by rw [Matrix.mul_assoc, hMM, hPP]
  have h2 : M * (P * M.transpose) = 1 := mul_eq_one_comm.mp h1
  have h3 := congrFun (congrFun h2 k) l
  simp only [Matrix.mul_apply, Matrix.transpose_apply, M, P, Matrix.of_apply, Matrix.one_apply,
    Fintype.sum_prod_type] at h3
  simp [ite_and] at h3
  simpa [Matrix.trace, Matrix.mul_apply] using h3

theorem gueBlock_eq_sum_hermBasis (W L : ℕ) (ω : Ω W L) (a : Fin L) :
    gueBlock W L ω a =
      ((Real.sqrt W : ℝ) : ℂ)⁻¹ • ∑ k : Fin W × Fin W, (ω (a, k.1, k.2) : ℂ) • hermBasis W k := by
  ext α β
  have hW : (0 : ℝ) < W := by exact_mod_cast Fin.pos α
  have hsW : ((Real.sqrt W : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hW).ne'
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 two_pos).ne'
  have h2W : Real.sqrt (2 * W) = Real.sqrt 2 * Real.sqrt W := Real.sqrt_mul (by norm_num) W
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, gueBlock, Matrix.of_apply, h2W]
  rcases lt_trichotomy α β with h | rfl | h
  · simp only [hermBasis_apply_lt W _ h, mul_add, Finset.sum_add_distrib]
    simp [h.ne, h]
    field_simp
  · simp only [hermBasis_apply_diag]
    simp
    field_simp
  · simp only [hermBasis_apply_gt W _ h, mul_add, Finset.sum_add_distrib]
    simp [h.ne', not_lt_of_gt h]
    field_simp
    ring

theorem blockV_isHermitian (W L : ℕ) (ω : Ω W L) : (blockV W L ω).IsHermitian :=
  blockDiagOp_isHermitian (gueBlock_isHermitian W L ω)

theorem blockFlow_isHermitian (W L : ℕ) {A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hA : A.IsHermitian) (s : ℝ) (ω : Ω W L) : (blockFlow W L A s ω).IsHermitian := by
  have hV := blockV_isHermitian W L ω
  unfold Matrix.IsHermitian at hA hV ⊢
  simp [blockFlow, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hA, hV]

theorem blockBasis_isHermitian (W L : ℕ) (c : Fin L) (k : Fin W × Fin W) :
    (blockBasis W L c k).IsHermitian := by
  ext p q
  have h := congrFun (congrFun (hermBasis_isHermitian W k) p.2) q.2
  simp only [Matrix.conjTranspose_apply] at h ⊢
  simp only [blockBasis, Matrix.of_apply]
  split_ifs with h1 h2 h2
  · exact h
  · exact absurd ⟨h1.2, h1.1⟩ h2
  · exact absurd ⟨h2.2, h2.1⟩ h1
  · simp

theorem blockV_eq_sum_blockBasis (W L : ℕ) (ω : Ω W L) :
    blockV W L ω = ((Real.sqrt W : ℝ) : ℂ)⁻¹ •
      ∑ c : Fin L, ∑ k : Fin W × Fin W, (ω (c, k.1, k.2) : ℂ) • blockBasis W L c k := by
  ext ⟨a, α⟩ ⟨b, β⟩
  have key := congrFun (congrFun (gueBlock_eq_sum_hermBasis W L ω a) α) β
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul] at key
  simp only [blockV, blockDiagOp, Matrix.of_apply, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, blockBasis]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, key, Finset.sum_eq_single a]
    · simp
    · intro c _ hc; simp [Ne.symm hc]
    · simp
  · rw [if_neg hab]
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_eq_zero]
    · simp
    · intro c _
      rw [Finset.sum_eq_zero]
      intro k _
      split_ifs with h1
      · exact absurd (h1.1.trans h1.2.symm) hab
      · rfl

/-- Completeness `Σ_k T_k A T_k = (Tr A) I`, used in (C.1) [gc:eq:divergence]. -/
theorem sum_hermBasis_mul_mul (W : ℕ) (A : Matrix (Fin W) (Fin W) ℂ) :
    ∑ k : Fin W × Fin W, hermBasis W k * A * hermBasis W k = A.trace • (1 : Matrix _ _ ℂ) := by
  ext i m
  have h : ∀ k : Fin W × Fin W, (hermBasis W k * A * hermBasis W k) i m =
      ∑ j, ∑ l, A j l * (hermBasis W k i j * hermBasis W k l m) := by
    intro k
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  simp only [Matrix.sum_apply, h]
  have h2 : ∑ k : Fin W × Fin W, ∑ j, ∑ l, A j l * (hermBasis W k i j * hermBasis W k l m) =
      ∑ j, ∑ l, ∑ k : Fin W × Fin W, A j l * (hermBasis W k i j * hermBasis W k l m) := by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
  rw [h2]
  simp only [← Finset.mul_sum, sum_hermBasis_apply_mul_apply]
  by_cases him : i = m
  · simp [him, Matrix.trace, Matrix.one_apply, mul_ite, eq_comm]
  · simp [him, Matrix.one_apply]

theorem gueCoord_gueBlock (W L : ℕ) (ω : Ω W L) : gueCoord W L (gueBlock W L ω) = ω := by
  funext ⟨a, α, β⟩
  have hW : (0 : ℝ) < W := by exact_mod_cast Fin.pos α
  have hsW : Real.sqrt W ≠ 0 := (Real.sqrt_pos.2 hW).ne'
  have hs2W : Real.sqrt (2 * W) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  simp only [gueCoord]
  rcases lt_trichotomy α β with h | rfl | h
  · simp only [h.ne, h, gueBlock, Matrix.of_apply, ite_true, ite_false]
    rw [Complex.div_ofReal_re]
    simp
    field_simp
  · simp only [gueBlock, Matrix.of_apply, ite_true]
    rw [Complex.div_ofReal_re]
    simp
    field_simp
  · simp only [h.ne', not_lt_of_gt h, h.ne, h, gueBlock, Matrix.of_apply, ite_true, ite_false]
    rw [Complex.div_ofReal_im]
    simp
    field_simp

theorem gueBlock_gueCoord (W L : ℕ) (V : Fin L → Matrix (Fin W) (Fin W) ℂ)
    (hV : ∀ a, (V a).IsHermitian) : gueBlock W L (gueCoord W L V) = V := by
  funext a
  ext α β
  have hW : (0 : ℝ) < W := by exact_mod_cast Fin.pos α
  have hsW : ((Real.sqrt W : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hW).ne'
  have hs2W : ((Real.sqrt (2 * W) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (mul_pos two_pos hW)).ne'
  have hH : ∀ x y, star (V a y x) = V a x y := fun x y => congrFun (congrFun (hV a) x) y
  have hri : ∀ x y, V a x y = ((V a x y).re : ℂ) + Complex.I * (V a x y).im := by
    intro x y; apply Complex.ext <;> simp
  simp only [gueBlock, gueCoord, Matrix.of_apply]
  rcases lt_trichotomy α β with h | rfl | h
  · simp only [h.ne, h, not_lt_of_gt h, h.ne', ite_true, ite_false]
    conv_rhs => rw [hri α β]
    push_cast
    field_simp
  · have him : (V a α α).im = 0 := by
      have := hH α α
      have h2 := congrArg Complex.im this
      simp at h2
      linarith
    simp only [ite_true]
    conv_rhs => rw [hri α α, him]
    push_cast
    field_simp
    simp
  · simp only [h.ne, h.ne', h, not_lt_of_gt h, ite_true, ite_false]
    conv_rhs => rw [← hH α β, hri β α]
    simp only [Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    field_simp
    ring

theorem blockV_sub (W L : ℕ) (ω ω' : Ω W L) :
    blockV W L (ω - ω') = blockV W L ω - blockV W L ω' := by
  ext ⟨a, α⟩ ⟨b, β⟩
  simp only [blockV, blockDiagOp, gueBlock, Matrix.of_apply, Matrix.sub_apply, Pi.sub_apply]
  by_cases hab : a = b
  · simp only [hab, ite_true]
    split_ifs <;> push_cast <;> ring
  · simp [hab]

private theorem trace_blockDiagOp_mul_self {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ) :
    (blockDiagOp V * blockDiagOp V).trace = ∑ c, (V c * V c).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, blockDiagOp, Matrix.of_apply,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun α _ => ?_
  simp

private theorem trace_gueBlock_mul_self (W L : ℕ) (ω : Ω W L) (a : Fin L) :
    (gueBlock W L ω a * gueBlock W L ω a).trace =
      (W : ℂ)⁻¹ * ∑ k : Fin W × Fin W, (ω (a, k) : ℂ) ^ 2 := by
  rw [gueBlock_eq_sum_hermBasis]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Finset.sum_mul_sum,
    Matrix.trace_sum, smul_eq_mul, trace_hermBasis_mul]
  have hs : ((Real.sqrt W : ℝ) : ℂ)⁻¹ * ((Real.sqrt W : ℝ) : ℂ)⁻¹ = (W : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg W)]
    simp
  rw [← mul_assoc, hs]
  congr 1
  simp [mul_ite, sq]

theorem trace_blockV_mul_self (W L : ℕ) (ω : Ω W L) :
    (blockV W L ω * blockV W L ω).trace = (W : ℂ)⁻¹ * ∑ k, (ω k : ℂ) ^ 2 := by
  rw [blockV, trace_blockDiagOp_mul_self]
  simp_rw [trace_gueBlock_mul_self]
  rw [← Finset.mul_sum, Fintype.sum_prod_type]

/-- Hilbert–Schmidt norm of `V` in the coordinates: `‖V‖²_HS = W⁻¹ Σ ω²`. -/
theorem sum_norm_sq_blockV (W L : ℕ) (ω : Ω W L) :
    ∑ p, ∑ q, ‖blockV W L ω p q‖ ^ 2 = (W : ℝ)⁻¹ * ∑ k, ω k ^ 2 := by
  apply Complex.ofReal_injective
  have hH := blockV_isHermitian W L ω
  have h1 : ∀ p q, ((‖blockV W L ω p q‖ ^ 2 : ℝ) : ℂ) = blockV W L ω p q * blockV W L ω q p := by
    intro p q
    have := congrFun (congrFun hH q) p
    simp only [Matrix.conjTranspose_apply] at this
    rw [← this]
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h2 : ((∑ p, ∑ q, ‖blockV W L ω p q‖ ^ 2 : ℝ) : ℂ) =
      ∑ p, ∑ q, blockV W L ω p q * blockV W L ω q p := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun q _ => h1 p q
  rw [h2]
  have h3 := trace_blockV_mul_self W L ω
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply] at h3
  rw [h3]
  push_cast
  rfl

/-- Pointwise scaling behind the identity in law of the single-time realization of (5.1)
[fo:eq:flow]. -/
theorem smul_blockFlow (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) {c s : ℝ}
    (hc : 0 ≤ c) (hs : 0 ≤ s) (ω : Ω W L) :
    (c : ℂ) • blockFlow W L A s ω = blockFlow W L ((c : ℂ) • A) (c ^ 2 * s) ω := by
  have h : ((Real.sqrt (c ^ 2 * s) : ℝ) : ℂ) = (c : ℂ) * ((Real.sqrt s : ℝ) : ℂ) := by
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]; push_cast; rfl
  simp only [blockFlow, h, smul_add, smul_smul]

/-- The successor on `Fin L` read cyclically. -/
private def cycleStep {L : ℕ} (a : Fin L) : Fin L := ⟨(a.val + 1) % L, Nat.mod_lt _ (Fin.pos a)⟩

private theorem cycleAdj_eq_step (L : ℕ) (a b : Fin L) :
    cycleAdj L a b = (if b = cycleStep a then 1 else 0) + (if a = cycleStep b then 1 else 0) := by
  simp [cycleAdj, cycleStep, Fin.ext_iff]

private theorem cycleStep_ne_self {L : ℕ} (hL : 3 ≤ L) (a : Fin L) : a ≠ cycleStep a := by
  intro h
  have h1 : a.val = (a.val + 1) % L := congrArg Fin.val h
  by_cases c1 : a.val + 1 < L
  · rw [Nat.mod_eq_of_lt c1] at h1; omega
  · have h2 : a.val + 1 = L := by have := a.isLt; omega
    rw [h2, Nat.mod_self] at h1; omega

private theorem cycleStep_no_two_cycle {L : ℕ} (hL : 3 ≤ L) {a b : Fin L} (h1 : b = cycleStep a)
    (h2 : a = cycleStep b) : False := by
  have e1 : b.val = (a.val + 1) % L := congrArg Fin.val h1
  have e2 : a.val = (b.val + 1) % L := congrArg Fin.val h2
  by_cases c1 : a.val + 1 < L
  · rw [Nat.mod_eq_of_lt c1] at e1
    by_cases c2 : b.val + 1 < L
    · rw [Nat.mod_eq_of_lt c2] at e2; omega
    · have h3 : b.val + 1 = L := by have := b.isLt; omega
      rw [h3, Nat.mod_self] at e2; omega
  · have h3 : a.val + 1 = L := by have := a.isLt; omega
    rw [h3, Nat.mod_self] at e1
    rw [e1, Nat.zero_add, Nat.mod_eq_of_lt (by omega)] at e2
    omega

private theorem cycleAdj_mul_comm {L : ℕ} (hL : 3 ≤ L) (a b : Fin L) :
    cycleAdj L a b * cycleAdj L b a =
      (if b = cycleStep a then 1 else 0) + (if a = cycleStep b then 1 else 0) := by
  rw [cycleAdj_eq_step, cycleAdj_eq_step]
  by_cases h1 : b = cycleStep a <;> by_cases h2 : a = cycleStep b
  · exact (cycleStep_no_two_cycle hL h1 h2).elim
  · simp only [eq_true h1, eq_false h2, ite_true, ite_false]; norm_num
  · simp only [eq_false h1, eq_true h2, ite_true, ite_false]; norm_num
  · simp only [eq_false h1, eq_false h2, ite_false]; norm_num

private theorem sum_cycleAdj_mul_comm {L : ℕ} (hL : 3 ≤ L) :
    ∑ a, ∑ b, cycleAdj L a b * cycleAdj L b a = 2 * L := by
  simp only [cycleAdj_mul_comm hL, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun a b => if a = cycleStep b then (1 : ℂ) else 0)]
  simp
  ring

private theorem cycleAdj_diag {L : ℕ} (hL : 3 ≤ L) (a : Fin L) : cycleAdj L a a = 0 := by
  rw [cycleAdj_eq_step]
  simp [cycleStep_ne_self hL a]

open scoped Kronecker in
private theorem trace_kron_mul_self {W L : ℕ} (hL : 3 ≤ L) :
    ((cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) *
      (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))).trace = (W : ℂ) * (2 * L) := by
  rw [← sum_cycleAdj_mul_comm hL]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.one_apply]
  have h : ∀ (a : Fin L) (α : Fin W) (b : Fin L), ∑ β : Fin W,
      (cycleAdj L a b * (if α = β then (1 : ℂ) else 0)) * (cycleAdj L b a * if β = α then 1 else 0)
      = cycleAdj L a b * cycleAdj L b a := by
    intro a α b
    simp [mul_mul_mul_comm, eq_comm]
  simp only [h]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp

open scoped Kronecker in
private theorem trace_kron_mul_blockDiag {W L : ℕ} (hL : 3 ≤ L)
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) :
    ((cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) * blockDiagOp V).trace = 0 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    blockDiagOp, Matrix.of_apply, Fintype.sum_prod_type, Matrix.one_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  simp [cycleAdj_diag hL]

open scoped Kronecker in
private theorem trace_Hmat_mul_self_aux (g : ℝ) (W L : ℕ) (hL : 3 ≤ L) (ω : Ω W L) :
    (Hmat g W L ω * Hmat g W L ω).trace =
      (((max 1 g : ℝ) : ℂ)⁻¹) ^ 2 *
        ((g : ℂ) ^ 2 * ((W : ℂ) * (2 * L)) + (W : ℂ)⁻¹ * ∑ k, (ω k : ℂ) ^ 2) := by
  have hH : Hmat g W L ω = (((max 1 g : ℝ) : ℂ)⁻¹) •
      ((g : ℂ) • (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) + blockV W L ω) := rfl
  have hKD := trace_kron_mul_blockDiag hL (gueBlock W L ω)
  have hDK : (blockV W L ω * (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))).trace = 0 := by
    rw [Matrix.trace_mul_comm]; exact hKD
  rw [hH]
  simp only [Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, Matrix.trace_add,
    Matrix.trace_smul, smul_eq_mul, trace_kron_mul_self hL, trace_blockV_mul_self, hDK]
  rw [blockV, hKD]
  ring

/-- The identity `N⁻¹ Tr H² = 2γg² + γ χ²_{LW²}/(LW²)` of Appendix D.2
[sec:rough-density-proof], times `N`. -/
theorem trace_Hmat_mul_self (g : ℝ) (W L : ℕ) (hL : 3 ≤ L) (ω : Ω W L) :
    (Hmat g W L ω * Hmat g W L ω).trace =
      (((max 1 g)⁻¹ ^ 2 * (2 * g ^ 2 * W * L + (W : ℝ)⁻¹ * ∑ k, ω k ^ 2) : ℝ) : ℂ) := by
  rw [trace_Hmat_mul_self_aux g W L hL ω]
  push_cast
  ring

end LSBA
