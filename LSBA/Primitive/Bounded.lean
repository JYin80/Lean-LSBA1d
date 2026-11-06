import LSBA.Primitive.Molecule
import LSBA.Primitive.Early
import LSBA.Kernel.Scales

/-!
# Primitive loops at bounded coupling

Lemma 5.2(a) [fo:lem:deterministic] at bounded coupling and the long-pair bound (B.16)
[b:eq:primitive-long-pair] on the bounded branch of (6.1) [da:eq:propagation-domain].
-/

open MeasureTheory Real Filter Topology Complex Finset
open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ## Grid characters and the normalized transform

The characters `e^{-2πinx/L}` of `ℤ_L`, the product form of `tensorFourier`, orthogonality,
Fourier inversion, and the support of the transform of a translation-invariant tensor. -/

section Characters

variable {L : ℕ}

/-- `e^{-2πia/L}` for `a ∈ ℕ`. -/
private def bnd_e (L : ℕ) (a : ℕ) : ℂ := Complex.exp (-(2 * π * I * ((a : ℂ) / L)))

/-- The grid character `e^{-2πinx/L}`. -/
def bnd_chi (L : ℕ) (n x : Fin L) : ℂ :=
  Complex.exp (-(2 * π * I * (((n : ℕ) : ℂ) * ((x : ℕ) : ℂ) / L)))

private lemma bnd_chi_eq (n x : Fin L) : bnd_chi L n x = bnd_e L ((n : ℕ) * (x : ℕ)) := by
  unfold bnd_chi bnd_e
  push_cast
  ring_nf

private lemma bnd_e_add (a b : ℕ) : bnd_e L (a + b) = bnd_e L a * bnd_e L b := by
  unfold bnd_e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma bnd_e_zero : bnd_e L 0 = 1 := by simp [bnd_e]

private lemma bnd_e_L_mul [NeZero L] (q : ℕ) : bnd_e L (L * q) = 1 := by
  unfold bnd_e
  have hL : (L : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have h : -(2 * π * I * (((L * q : ℕ) : ℂ) / L)) = ((-(q : ℤ) : ℤ) : ℂ) * (2 * π * I) := by
    push_cast
    field_simp
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

private lemma bnd_e_mod [NeZero L] (a : ℕ) : bnd_e L (a % L) = bnd_e L a := by
  conv_rhs => rw [← Nat.mod_add_div a L]
  rw [bnd_e_add, bnd_e_L_mul, mul_one]

private lemma bnd_e_mul_mod [NeZero L] (n s : ℕ) : bnd_e L (n * (s % L)) = bnd_e L (n * s) := by
  rw [← bnd_e_mod (n * (s % L)), ← bnd_e_mod (n * s), Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

private lemma bnd_chi_add [NeZero L] (n x y : Fin L) :
    bnd_chi L n (x + y) = bnd_chi L n x * bnd_chi L n y := by
  rw [bnd_chi_eq, bnd_chi_eq, bnd_chi_eq, Fin.val_add, bnd_e_mul_mod, mul_add, bnd_e_add]

private lemma bnd_chi_comm (n x : Fin L) : bnd_chi L n x = bnd_chi L x n := by
  rw [bnd_chi_eq, bnd_chi_eq, mul_comm]

private lemma bnd_chi_zero_right [NeZero L] (n : Fin L) : bnd_chi L n 0 = 1 := by
  rw [bnd_chi_eq, Fin.val_zero, mul_zero, bnd_e_zero]

private lemma bnd_chi_zero_left [NeZero L] (x : Fin L) : bnd_chi L 0 x = 1 := by
  rw [bnd_chi_comm, bnd_chi_zero_right]

private lemma bnd_chi_add_left [NeZero L] (n n' x : Fin L) :
    bnd_chi L (n + n') x = bnd_chi L n x * bnd_chi L n' x := by
  rw [bnd_chi_comm, bnd_chi_add, bnd_chi_comm x n, bnd_chi_comm x n']

private lemma bnd_chi_neg_mul [NeZero L] (n x : Fin L) : bnd_chi L n (-x) * bnd_chi L n x = 1 := by
  rw [← bnd_chi_add, neg_add_cancel, bnd_chi_zero_right]

private lemma bnd_chi_neg_left [NeZero L] (n x : Fin L) :
    bnd_chi L (-n) x = bnd_chi L n (-x) := by
  rw [bnd_chi_comm, bnd_chi_comm n]
  have h1 := bnd_chi_neg_mul x n
  have h2 : bnd_chi L (-x) n * bnd_chi L x n = 1 := by
    rw [← bnd_chi_add_left, neg_add_cancel, bnd_chi_zero_left]
  have hne : bnd_chi L x n ≠ 0 := by
    intro h; rw [h, mul_zero] at h1; exact zero_ne_one h1
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

private lemma bnd_norm_chi (n x : Fin L) : ‖bnd_chi L n x‖ = 1 := by
  unfold bnd_chi
  rw [Complex.norm_exp]
  have : (-(2 * π * I * (((n : ℕ) : ℂ) * ((x : ℕ) : ℂ) / L))).re = 0 := by
    simp [Complex.mul_re, Complex.div_re, Complex.mul_im, Complex.div_im]
  rw [this, Real.exp_zero]

private lemma bnd_chi_neg_eq_inv [NeZero L] (n x : Fin L) :
    bnd_chi L n (-x) = (bnd_chi L n x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (bnd_chi_neg_mul n x)

private lemma bnd_star_chi [NeZero L] (n x : Fin L) : star (bnd_chi L n x) = bnd_chi L n (-x) := by
  rw [bnd_chi_neg_eq_inv]
  have h := bnd_norm_chi n x
  have h2 : Complex.normSq (bnd_chi L n x) = 1 := by
    rw [Complex.normSq_eq_norm_sq, h, one_pow]
  rw [Complex.inv_def, h2, inv_one, Complex.ofReal_one, mul_one]
  rfl

/-- `e^{-2πin/L} ≠ 1` for `0 < n < L`. -/
private lemma bnd_e_ne_one [NeZero L] {n : ℕ} (h0 : 0 < n) (h1 : n < L) : bnd_e L n ≠ 1 := by
  unfold bnd_e
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨z, hz⟩ := h
  have hL : (L : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hpi : (2 * π * I : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [this, Complex.I_ne_zero]
  have h2 : ((n : ℂ)) = -(z : ℂ) * L := by
    have h3 : (2 * π * I) * (-(n : ℂ) / L) = (2 * π * I) * (z : ℂ) := by
      rw [mul_comm (2 * π * I) (z : ℂ), ← hz]; ring
    have h4 := mul_left_cancel₀ hpi h3
    field_simp at h4
    linear_combination -h4
  have h5 : (n : ℤ) = -z * L := by exact_mod_cast h2
  have hz' : z < 0 := by
    by_contra hc
    have hc : 0 ≤ z := by omega
    have : -z * (L : ℤ) ≤ 0 := by
      have : (0 : ℤ) ≤ L := by positivity
      nlinarith
    omega
  have : (L : ℤ) ≤ -z * L := by
    have : (1 : ℤ) ≤ -z := by omega
    have hL0 : (0 : ℤ) ≤ L := by positivity
    nlinarith
  omega

/-- Orthogonality: `Σ_x e^{-2πinx/L} = L·1[n = 0]`. -/
private lemma bnd_sum_chi [NeZero L] (n : Fin L) :
    ∑ x : Fin L, bnd_chi L n x = if n = 0 then (L : ℂ) else 0 := by
  split_ifs with hn
  · subst hn
    simp [bnd_chi_zero_left]
  · have hn0 : 0 < (n : ℕ) := by
      rcases Nat.eq_zero_or_pos (n : ℕ) with h | h
      · exact absurd (Fin.ext h) hn
      · exact h
    set ω := bnd_e L (n : ℕ) with hω
    have hpow : ∀ x : ℕ, bnd_e L ((n : ℕ) * x) = ω ^ x := by
      intro x
      induction x with
      | zero => simp [bnd_e_zero]
      | succ x ih => rw [Nat.mul_succ, bnd_e_add, ih, pow_succ]
    have hsum : ∑ x : Fin L, bnd_chi L n x = ∑ i ∈ Finset.range L, ω ^ i := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => ω ^ i) L]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [bnd_chi_eq, hpow]
    have hω1 : ω ≠ 1 := bnd_e_ne_one hn0 n.isLt
    have hωL : ω ^ L = 1 := by
      rw [← hpow, mul_comm, bnd_e_L_mul]
    rw [hsum, geom_sum_eq hω1, hωL, sub_self, zero_div]

/-- The normalized transform as a sum against products of grid characters. -/
private lemma bnd_tf_eq {k : ℕ} (S : (Fin k → Fin L) → ℂ) (n : Fin k → Fin L) :
    tensorFourier S n = (L : ℂ)⁻¹ * ∑ x, S x * ∏ j, bnd_chi L (n j) (x j) := by
  unfold tensorFourier bnd_chi
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]

/-- Fourier inversion on `ℤ_L^k`: `L^{k-1} S(x) = Σ_n Ŝ(n) Π_j e^{2πin_jx_j/L}`. -/
private lemma bnd_inversion [NeZero L] {k : ℕ} (hk : 1 ≤ k) (S : (Fin k → Fin L) → ℂ)
    (x : Fin k → Fin L) :
    (L : ℂ) ^ (k - 1) * S x = ∑ n, tensorFourier S n * ∏ j, bnd_chi L (n j) (-x j) := by
  have hL : (L : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne L
  simp only [bnd_tf_eq, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  have key : ∀ y : Fin k → Fin L, ∑ n : Fin k → Fin L,
      (∏ j, bnd_chi L (n j) (y j)) * ∏ j, bnd_chi L (n j) (-x j) =
        if y = x then (L : ℂ) ^ k else 0 := by
    intro y
    have h1 : ∀ n : Fin k → Fin L, (∏ j, bnd_chi L (n j) (y j)) * ∏ j, bnd_chi L (n j) (-x j) =
        ∏ j, bnd_chi L (y j - x j) (n j) := by
      intro n
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← bnd_chi_add, bnd_chi_comm, sub_eq_add_neg]
    simp only [h1]
    rw [← Fintype.prod_sum (fun j q => bnd_chi L (y j - x j) q)]
    simp only [bnd_sum_chi, sub_eq_zero]
    rw [Finset.prod_ite_zero]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    exact propext ⟨fun h => funext fun j => h j (Finset.mem_univ _),
      fun h j _ => congrFun h j⟩
  calc (L : ℂ) ^ (k - 1) * S x
      = ∑ y, (L : ℂ)⁻¹ * (S y * if y = x then (L : ℂ) ^ k else 0) := by
        rw [Finset.sum_eq_single x (fun y _ hy => by simp [hy]) (fun h => absurd
          (Finset.mem_univ x) h)]
        simp only [ite_true]
        have : (L : ℂ) ^ k = L * L ^ (k - 1) := by
          rw [← pow_succ']; congr 1; omega
        rw [this]
        field_simp
    _ = _ := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← key y, Finset.mul_sum, Finset.mul_sum]

/-- The value of a sum in `Fin L` is the sum of the values modulo `L`. -/
lemma bnd_val_sum [NeZero L] {k : ℕ} (n : Fin k → Fin L) :
    ((∑ j, n j : Fin L) : ℕ) = (∑ j, (n j : ℕ)) % L := by
  have h : ∀ s : Finset (Fin k), ((∑ j ∈ s, n j : Fin L) : ℕ) = (∑ j ∈ s, (n j : ℕ)) % L := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Fin.val_add, ih, Nat.add_mod_mod]
  exact h Finset.univ

/-- The transform of a translation-invariant tensor vanishes unless `Σ_j n_j ≡ 0`. -/
lemma bnd_tf_support [NeZero L] {k : ℕ} (S : (Fin k → Fin L) → ℂ)
    (hS : ∀ (y : Fin k → Fin L) (c : Fin L), S (fun i => y i + c) = S y) (n : Fin k → Fin L)
    (hn : ∑ j, n j ≠ 0) : tensorFourier S n = 0 := by
  rw [bnd_tf_eq]
  set T := ∑ x, S x * ∏ j, bnd_chi L (n j) (x j) with hT
  have hshift : T = bnd_chi L 1 (∑ j, n j) * T := by
    rw [hT, Finset.mul_sum]
    let e : (Fin k → Fin L) ≃ (Fin k → Fin L) :=
      Equiv.piCongrRight fun _ => Equiv.addRight (1 : Fin L)
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx : e x = fun i => x i + 1 := rfl
    rw [hx, hS x 1]
    have hprod : ∏ j, bnd_chi L (n j) (x j + 1) =
        bnd_chi L 1 (∑ j, n j) * ∏ j, bnd_chi L (n j) (x j) := by
      have h1 : bnd_chi L 1 (∑ j, n j) = ∏ j, bnd_chi L (n j) 1 := by
        have : ∀ s : Finset (Fin k), bnd_chi L 1 (∑ j ∈ s, n j) = ∏ j ∈ s, bnd_chi L (n j) 1 := by
          intro s
          induction s using Finset.induction_on with
          | empty => simp [bnd_chi_zero_right]
          | insert a s ha ih =>
            rw [Finset.sum_insert ha, Finset.prod_insert ha, bnd_chi_add, ih, bnd_chi_comm]
        exact this Finset.univ
      rw [h1, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [bnd_chi_add, mul_comm]
    rw [hprod]
    ring
  have hne : bnd_chi L 1 (∑ j, n j) ≠ 1 := by
    rw [bnd_chi_eq]
    have hs0 : 0 < ((∑ j, n j : Fin L) : ℕ) := by
      rcases Nat.eq_zero_or_pos ((∑ j, n j : Fin L) : ℕ) with h | h
      · exact absurd (Fin.ext h) hn
      · exact h
    have h1 : ((1 : Fin L) : ℕ) * ((∑ j, n j : Fin L) : ℕ) = ((∑ j, n j : Fin L) : ℕ) := by
      rcases Nat.lt_or_ge 1 L with hL1 | hL1
      · rw [Fin.val_one', Nat.mod_eq_of_lt hL1, one_mul]
      · exfalso
        have := (∑ j, n j : Fin L).isLt
        omega
    rw [h1]
    exact bnd_e_ne_one hs0 (Fin.isLt _)
  have hT0 : T = 0 := by
    have h2 : (1 - bnd_chi L 1 (∑ j, n j)) * T = 0 := by
      rw [sub_mul, one_mul, ← hshift, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (sub_eq_zero.mp h).symm hne
    · exact h
  rw [hT0, mul_zero]

end Characters

/-! ## Weighted norms of transforms

`N(w, T) = Σ_n Π_j w_j(n_j) |T̂(n)|` with leg weights `w_j`; with the weight of the leg `v`
replaced by the indicator of `q` it is the leg marginal `A_v(q)` of the proof of Proposition
B.2 [ba:prop:primitive], up to the factor `L^{k-2}`. -/

section Norms

variable {L : ℕ}

/-- The weighted `ℓ¹` norm of the normalized transform. -/
def bnd_N {k : ℕ} (w : Fin k → Fin L → ℝ) (T : (Fin k → Fin L) → ℂ) : ℝ :=
  ∑ n, (∏ j, w j (n j)) * ‖tensorFourier T n‖

/-- The indicator of the momentum `q`. -/
def bnd_del (q : Fin L) : Fin L → ℝ := fun x => if x = q then 1 else 0

lemma bnd_del_nonneg (q x : Fin L) : 0 ≤ bnd_del q x := by
  unfold bnd_del; split_ifs <;> norm_num

private lemma bnd_N_nonneg {k : ℕ} {w : Fin k → Fin L → ℝ} (hw : ∀ j x, 0 ≤ w j x)
    (T : (Fin k → Fin L) → ℂ) : 0 ≤ bnd_N w T :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Finset.prod_nonneg fun j _ => hw j _) (norm_nonneg _)

private lemma bnd_N_mono {k : ℕ} {w w' : Fin k → Fin L → ℝ} (hw : ∀ j x, 0 ≤ w j x)
    (hle : ∀ j x, w j x ≤ w' j x) (T : (Fin k → Fin L) → ℂ) : bnd_N w T ≤ bnd_N w' T := by
  unfold bnd_N
  refine Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  exact Finset.prod_le_prod₀ (fun j _ => hw j _) (fun j _ => hle j _)

/-- A pointwise domination of transforms gives the domination of the norms. -/
lemma bnd_N_le_sum {k : ℕ} {ι : Type*} (s : Finset ι) {w : Fin k → Fin L → ℝ}
    (hw : ∀ j x, 0 ≤ w j x) (T : (Fin k → Fin L) → ℂ) (Ti : ι → (Fin k → Fin L) → ℂ)
    (h : ∀ n, ‖tensorFourier T n‖ ≤ ∑ i ∈ s, ‖tensorFourier (Ti i) n‖) :
    bnd_N w T ≤ ∑ i ∈ s, bnd_N w (Ti i) := by
  unfold bnd_N
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (h n) (Finset.prod_nonneg fun j _ => hw j _)

/-- The transform is linear: finite sums. -/
lemma bnd_tf_sum {k : ℕ} {ι : Type*} (s : Finset ι) (Ti : ι → (Fin k → Fin L) → ℂ)
    (n : Fin k → Fin L) :
    tensorFourier (fun y => ∑ i ∈ s, Ti i y) n = ∑ i ∈ s, tensorFourier (Ti i) n := by
  unfold tensorFourier
  rw [← Finset.mul_sum]
  congr 1
  simp only [Finset.sum_mul]
  exact Finset.sum_comm

/-- The transform is linear: scalars. -/
lemma bnd_tf_smul {k : ℕ} (c : ℂ) (T : (Fin k → Fin L) → ℂ) (n : Fin k → Fin L) :
    tensorFourier (fun y => c * T y) n = c * tensorFourier T n := by
  unfold tensorFourier
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- Replacing one leg weight by a nonnegative function keeps the weights nonnegative. -/
lemma bnd_update_nonneg {k : ℕ} {w : Fin k → Fin L → ℝ} (hw : ∀ j x, 0 ≤ w j x)
    {v : Fin k} {f : Fin L → ℝ} (hf : ∀ x, 0 ≤ f x) (j : Fin k) (x : Fin L) :
    0 ≤ Function.update w v f j x := by
  by_cases hj : j = v
  · subst hj; simp only [Function.update_self]; exact hf x
  · simp only [Function.update_of_ne hj]; exact hw j x

/-- The product with the weight of one leg replaced. -/
private lemma bnd_prod_update {k : ℕ} (w : Fin k → Fin L → ℝ) (v : Fin k) (f : Fin L → ℝ)
    (n : Fin k → Fin L) :
    ∏ j, Function.update w v f j (n j) = f (n v) * ∏ j ∈ Finset.univ.erase v, w j (n j) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- The weight of one leg enters linearly. -/
lemma bnd_N_update_sum {k : ℕ} (w : Fin k → Fin L → ℝ) (v : Fin k) (c : Fin L → ℝ)
    (T : (Fin k → Fin L) → ℂ) :
    ∑ q, c q * bnd_N (Function.update w v (bnd_del q)) T = bnd_N (Function.update w v c) T := by
  unfold bnd_N
  simp only [bnd_prod_update, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  have : ∀ q, c q * (bnd_del q (n v) * (∏ j ∈ Finset.univ.erase v, w j (n j)) *
      ‖tensorFourier T n‖) = if n v = q then c (n v) * ((∏ j ∈ Finset.univ.erase v, w j (n j)) *
      ‖tensorFourier T n‖) else 0 := by
    intro q
    unfold bnd_del
    split_ifs with h
    · rw [h]; ring
    · ring
  simp only [this, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- `Σ_x 1[x = q] f(x) = f(q)`. -/
lemma bnd_sum_del (q : Fin L) (f : Fin L → ℝ) : ∑ x, bnd_del q x * f x = f q := by
  unfold bnd_del
  simp

/-- The dressing of a core by leg kernels: `L^{k-1} |Σ_y Π_j D_j(a_j, y_j) C(y)| ≤ N(w, C)` when
`w_j` dominates the multiplier of `D_j`. -/
lemma bnd_dress [NeZero L] {k : ℕ} (hk : 1 ≤ k) (D : Fin k → Fin L → Fin L → ℂ)
    (C : (Fin k → Fin L) → ℂ) (w : Fin k → Fin L → ℝ)
    (hw : ∀ j a q, ‖∑ x, D j a x * bnd_chi L q (-x)‖ ≤ w j q) (a : Fin k → Fin L) :
    (L : ℝ) ^ (k - 1) * ‖∑ y, (∏ j, D j (a j) (y j)) * C y‖ ≤ bnd_N w C := by
  have key : (L : ℂ) ^ (k - 1) * ∑ y, (∏ j, D j (a j) (y j)) * C y =
      ∑ n, tensorFourier C n * ∏ j, ∑ x, D j (a j) x * bnd_chi L (n j) (-x) := by
    rw [Finset.mul_sum]
    have h1 : ∀ y : Fin k → Fin L, (L : ℂ) ^ (k - 1) * ((∏ j, D j (a j) (y j)) * C y) =
        ∑ n, tensorFourier C n * ∏ j, (D j (a j) (y j) * bnd_chi L (n j) (-y j)) := by
      intro y
      rw [mul_left_comm, bnd_inversion hk, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.prod_mul_distrib]
      ring
    simp only [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    exact (Fintype.prod_sum (fun j x => D j (a j) x * bnd_chi L (n j) (-x))).symm
  have hL : (0 : ℝ) ≤ (L : ℝ) ^ (k - 1) := by positivity
  calc (L : ℝ) ^ (k - 1) * ‖∑ y, (∏ j, D j (a j) (y j)) * C y‖
      = ‖(L : ℂ) ^ (k - 1) * ∑ y, (∏ j, D j (a j) (y j)) * C y‖ := by
        rw [norm_mul, norm_pow, Complex.norm_natCast]
    _ = ‖∑ n, tensorFourier C n * ∏ j, ∑ x, D j (a j) x * bnd_chi L (n j) (-x)‖ := by rw [key]
    _ ≤ ∑ n, ‖tensorFourier C n * ∏ j, ∑ x, D j (a j) x * bnd_chi L (n j) (-x)‖ :=
        norm_sum_le _ _
    _ ≤ bnd_N w C := by
        unfold bnd_N
        refine Finset.sum_le_sum fun n _ => ?_
        rw [norm_mul, norm_prod, mul_comm]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => hw j _ _)

/-- A sum over all momenta restricted to `Σ_j n_j = 0` of a function that does not depend on
the coordinate `s` is `L⁻¹` times the unrestricted sum. -/
private lemma bnd_sum_constraint [NeZero L] {k : ℕ} (s : Fin k) (G : (Fin k → Fin L) → ℝ)
    (hG : ∀ n c, G (n + Pi.single s c) = G n) :
    ∑ n, (if ∑ j, n j = 0 then G n else 0) = (L : ℝ)⁻¹ * ∑ n, G n := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hshift : ∀ c : Fin L, ∑ n, (if ∑ j, n j = c then G n else 0) =
      ∑ n, (if ∑ j, n j = 0 then G n else 0) := by
    intro c
    let e : (Fin k → Fin L) ≃ (Fin k → Fin L) := Equiv.addRight (Pi.single s c)
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun n _ => ?_
    have he : e n = n + Pi.single s c := rfl
    have hsum : ∑ j, (n + Pi.single s c : Fin k → Fin L) j = ∑ j, n j + c := by
      simp only [Pi.add_apply, Finset.sum_add_distrib]
      congr 1
      simp
    rw [he, hsum, hG]
    simp
  have htot : ∑ c : Fin L, ∑ n, (if ∑ j, n j = c then G n else 0) = ∑ n, G n := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp
  rw [Finset.sum_congr rfl fun c _ => hshift c, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at htot
  rw [← htot]
  field_simp

/-- `Σ_n Π_j f_j(n_j) = Π_j Σ_x f_j(x)`. -/
private lemma bnd_sum_prod {k : ℕ} (f : Fin k → Fin L → ℝ) :
    ∑ n : Fin k → Fin L, ∏ j, f j (n j) = ∏ j, ∑ x, f j x :=
  (Fintype.prod_sum f).symm

/-- The restricted sum of a product in which the factor of the leg `s` is one. -/
lemma bnd_sum_constraint_prod [NeZero L] {k : ℕ} (s : Fin k) (f : Fin k → Fin L → ℝ) :
    ∑ n : Fin k → Fin L, (if ∑ j, n j = 0 then ∏ j, (if j = s then 1 else f j (n j)) else 0) =
      ∏ j ∈ Finset.univ.erase s, ∑ x, f j x := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  rw [bnd_sum_constraint s]
  · rw [bnd_sum_prod (fun j x => if j = s then 1 else f j x)]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ s)]
    simp only [ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
    rw [← mul_assoc, inv_mul_cancel₀ hL, one_mul]
    refine Finset.prod_congr rfl fun j hj => ?_
    simp only [Finset.ne_of_mem_erase hj, ite_false]
  · intro n c
    refine Finset.prod_congr rfl fun j _ => ?_
    by_cases hj : j = s
    · simp [hj]
    · simp [hj]

end Norms

/-! ## The two polygons cut off by a diagonal

For a diagonal `(i, j)` of the `k`-gon, the vertices `0, …, i, j, …, k-1` form the polygon of
Cut_L and the vertices `i, …, j` the polygon of Cut_R of (5.6) [fo:eq:cuts]. -/

section Polygon

variable {k : ℕ}

/-- The cyclic offset without `mod`. -/
private lemma bnd_polyOff_eq {n : ℕ} (v w : Fin n) :
    polyOff v w = if v.val ≤ w.val then w.val - v.val else w.val + n - v.val := by
  have := v.isLt
  have := w.isLt
  unfold polyOff
  split_ifs with h
  · rw [show w.val + n - v.val = (w.val - v.val) + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

private lemma bnd_polyOff_cases {n : ℕ} (v w : Fin n) :
    (v.val ≤ w.val ∧ polyOff v w = w.val - v.val) ∨
      (w.val < v.val ∧ polyOff v w = w.val + n - v.val) := by
  rw [bnd_polyOff_eq]
  split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨by omega, rfl⟩

/-- The value of the cyclic successor. -/
private lemma bnd_finRotate_val {n : ℕ} (v : Fin n) :
    (finRotate n v).val = if v.val + 1 = n then 0 else v.val + 1 := by
  rcases n with _ | n
  · exact v.elim0
  · rw [coe_finRotate]
    by_cases h : v = Fin.last n
    · subst h; simp
    · have h' : v.val ≠ n := fun e => h (Fin.ext e)
      simp [h, h']

/-- The vertex map of the polygon of `Cut_{L,i,j}`. -/
private def bnd_vL (i j : Fin k) (p : Fin (k + i - j + 1)) : Fin k :=
  ⟨if p.val ≤ i.val then p.val else p.val + j.val - i.val - 1, by
    have := p.isLt; have := i.isLt; have := j.isLt; split_ifs <;> omega⟩

/-- The vertex map of the polygon of `Cut_{R,i,j}`. -/
private def bnd_vR (i j : Fin k) (q : Fin (j - i + 1)) : Fin k :=
  ⟨i.val + q.val, by have := q.isLt; have := i.isLt; have := j.isLt; omega⟩

private lemma bnd_vL_val (i j : Fin k) (p : Fin (k + i - j + 1)) :
    (bnd_vL i j p).val = if p.val ≤ i.val then p.val else p.val + j.val - i.val - 1 := rfl

private lemma bnd_vR_val (i j : Fin k) (q : Fin (j - i + 1)) :
    (bnd_vR i j q).val = i.val + q.val := rfl

private lemma bnd_vL_cases (i j : Fin k) (p : Fin (k + i - j + 1)) :
    (p.val ≤ i.val ∧ (bnd_vL i j p).val = p.val) ∨
      (i.val < p.val ∧ (bnd_vL i j p).val = p.val + j.val - i.val - 1) := by
  rw [bnd_vL_val]
  split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨by omega, rfl⟩

private lemma bnd_vL_strictMono {i j : Fin k} (hij : i.val < j.val) :
    StrictMono (bnd_vL i j) := by
  intro p p' h
  rw [Fin.lt_def, bnd_vL_val, bnd_vL_val]
  rw [Fin.lt_def] at h
  split_ifs <;> omega

private lemma bnd_vR_strictMono (i j : Fin k) : StrictMono (bnd_vR i j) := by
  intro q q' h
  rw [Fin.lt_def, bnd_vR_val, bnd_vR_val]
  rw [Fin.lt_def] at h
  omega

/-- The inverse of `bnd_vL` on its range. -/
private def bnd_uL (i j : Fin k) (v : Fin k) : Fin (k + i - j + 1) :=
  ⟨if v.val ≤ i.val then v.val else v.val + i.val + 1 - j.val, by
    have := v.isLt; have := i.isLt; have := j.isLt; split_ifs <;> omega⟩

/-- The inverse of `bnd_vR` on its range. -/
private def bnd_uR (i j : Fin k) (v : Fin k) : Fin (j - i + 1) :=
  ⟨if v.val ≤ j.val then v.val - i.val else 0, by split_ifs <;> omega⟩

private lemma bnd_uL_val (i j v : Fin k) :
    (bnd_uL i j v).val = if v.val ≤ i.val then v.val else v.val + i.val + 1 - j.val := rfl

private lemma bnd_uR_val (i j v : Fin k) :
    (bnd_uR i j v).val = if v.val ≤ j.val then v.val - i.val else 0 := rfl

private lemma bnd_vL_uL {i j : Fin k} {v : Fin k}
    (hv : v.val ≤ i.val ∨ j.val ≤ v.val) : bnd_vL i j (bnd_uL i j v) = v := by
  apply Fin.ext
  rw [bnd_vL_val, bnd_uL_val]
  split_ifs <;> omega

private lemma bnd_vR_uR {i j : Fin k} {v : Fin k} (hv : i.val ≤ v.val ∧ v.val ≤ j.val) :
    bnd_vR i j (bnd_uR i j v) = v := by
  apply Fin.ext
  rw [bnd_vR_val, bnd_uR_val]
  split_ifs <;> omega

private lemma bnd_uL_vL {i j : Fin k} (hij : i.val < j.val) (p : Fin (k + i - j + 1)) :
    bnd_uL i j (bnd_vL i j p) = p := by
  have := p.isLt; have := j.isLt
  apply Fin.ext
  rw [bnd_uL_val, bnd_vL_val]
  split_ifs <;> omega

private lemma bnd_uR_vR (i j : Fin k) (q : Fin (j - i + 1)) :
    bnd_uR i j (bnd_vR i j q) = q := by
  have := q.isLt; have := j.isLt
  apply Fin.ext
  rw [bnd_uR_val, bnd_vR_val]
  split_ifs <;> omega

private lemma bnd_vL_inj {i j : Fin k} (hij : i.val < j.val) {p p' : Fin (k + i - j + 1)}
    (h : bnd_vL i j p = bnd_vL i j p') : p = p' :=
  (bnd_vL_strictMono hij).injective h

private lemma bnd_vR_inj {i j : Fin k} {q q' : Fin (j - i + 1)}
    (h : bnd_vR i j q = bnd_vR i j q') : q = q' :=
  (bnd_vR_strictMono i j).injective h

/-- The cyclic order seen from a vertex is preserved by `bnd_vL`. -/
private lemma bnd_off_vL {i j : Fin k} (hij : i.val < j.val) (v w w' : Fin (k + i - j + 1)) :
    polyOff v w < polyOff v w' ↔
      polyOff (bnd_vL i j v) (bnd_vL i j w) < polyOff (bnd_vL i j v) (bnd_vL i j w') := by
  have := v.isLt; have := w.isLt; have := w'.isLt; have := j.isLt
  simp only [bnd_polyOff_eq, bnd_vL_val]
  split_ifs <;> omega

/-- The cyclic order seen from a vertex is preserved by `bnd_vR`. -/
private lemma bnd_off_vR (i j : Fin k) (v w w' : Fin (j - i + 1)) :
    polyOff v w < polyOff v w' ↔
      polyOff (bnd_vR i j v) (bnd_vR i j w) < polyOff (bnd_vR i j v) (bnd_vR i j w') := by
  have := v.isLt; have := w.isLt; have := w'.isLt; have := j.isLt
  simp only [bnd_polyOff_eq, bnd_vR_val, Nat.add_le_add_iff_left]
  split_ifs <;> omega

private lemma bnd_cutLSgn_eq (σ : Fin k → Bool) (i j : Fin k) (p : Fin (k + i - j + 1)) :
    cutLSgn σ i j p = σ (bnd_vL i j p) := by
  unfold cutLSgn
  split_ifs with h1 <;> (congr 1; apply Fin.ext; simp [bnd_vL_val, h1])

private lemma bnd_cutRSgn_eq (σ : Fin k → Bool) (i j : Fin k) (q : Fin (j - i + 1)) :
    cutRSgn σ i j q = σ (bnd_vR i j q) := rfl

end Polygon

/-! ## Splitting a dissection along a diagonal -/

section Split

variable {k : ℕ}

lemma bnd_mem_polyDiags {n : ℕ} (e : Fin n × Fin n) :
    e ∈ polyDiags n ↔ e.1.val + 2 ≤ e.2.val ∧ ¬(e.1.val = 0 ∧ e.2.val + 1 = n) := by
  simp [polyDiags, IsPolyDiag]

private lemma bnd_mem_dissections {n : ℕ} (F : Finset (Fin n × Fin n)) :
    F ∈ dissections n ↔ F ⊆ polyDiags n ∧ ∀ d ∈ F, ∀ e ∈ F, ¬DiagCross d e := by
  simp [dissections]

private lemma bnd_diagCross_iff {n : ℕ} (d e : Fin n × Fin n) :
    DiagCross d e ↔ (d.1.val < e.1.val ∧ e.1.val < d.2.val ∧ d.2.val < e.2.val) ∨
      (e.1.val < d.1.val ∧ d.1.val < e.2.val ∧ e.2.val < d.2.val) := by
  unfold DiagCross
  simp only [Fin.lt_def]

private lemma bnd_prod_ne {n : ℕ} {e d : Fin n × Fin n} (h : e ≠ d) :
    ¬(e.1.val = d.1.val ∧ e.2.val = d.2.val) :=
  fun h' => h (Prod.ext (Fin.ext h'.1) (Fin.ext h'.2))

/-- The dissection of the polygon of `Cut_{L,i,j}` induced by `F`. -/
private def bnd_splitL (i j : Fin k) (F : Finset (Fin k × Fin k)) :
    Finset (Fin (k + i - j + 1) × Fin (k + i - j + 1)) :=
  Finset.univ.filter fun e =>
    (bnd_vL i j e.1, bnd_vL i j e.2) ∈ F ∧ (bnd_vL i j e.1, bnd_vL i j e.2) ≠ (i, j)

/-- The dissection of the polygon of `Cut_{R,i,j}` induced by `F`. -/
private def bnd_splitR (i j : Fin k) (F : Finset (Fin k × Fin k)) :
    Finset (Fin (j - i + 1) × Fin (j - i + 1)) :=
  Finset.univ.filter fun e =>
    (bnd_vR i j e.1, bnd_vR i j e.2) ∈ F ∧ (bnd_vR i j e.1, bnd_vR i j e.2) ≠ (i, j)

/-- The dissection of the `k`-gon glued from dissections of the two polygons and `(i, j)`. -/
private def bnd_glue (i j : Fin k) (FL : Finset (Fin (k + i - j + 1) × Fin (k + i - j + 1)))
    (FR : Finset (Fin (j - i + 1) × Fin (j - i + 1))) : Finset (Fin k × Fin k) :=
  insert (i, j) (FL.image (fun e => (bnd_vL i j e.1, bnd_vL i j e.2)) ∪
    FR.image (fun e => (bnd_vR i j e.1, bnd_vR i j e.2)))

private lemma bnd_mem_splitL {i j : Fin k} {F : Finset (Fin k × Fin k)}
    (e : Fin (k + i - j + 1) × Fin (k + i - j + 1)) :
    e ∈ bnd_splitL i j F ↔
      (bnd_vL i j e.1, bnd_vL i j e.2) ∈ F ∧ (bnd_vL i j e.1, bnd_vL i j e.2) ≠ (i, j) := by
  simp [bnd_splitL]

private lemma bnd_mem_splitR {i j : Fin k} {F : Finset (Fin k × Fin k)}
    (e : Fin (j - i + 1) × Fin (j - i + 1)) :
    e ∈ bnd_splitR i j F ↔
      (bnd_vR i j e.1, bnd_vR i j e.2) ∈ F ∧ (bnd_vR i j e.1, bnd_vR i j e.2) ≠ (i, j) := by
  simp [bnd_splitR]

/-- Every other diagonal of a dissection containing `(i, j)` lies on one side of it. -/
private lemma bnd_cover {i j : Fin k} {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k)
    (hd : (i, j) ∈ F) {e : Fin k × Fin k} (he : e ∈ F) (hne : e ≠ (i, j)) :
    ((e.1.val ≤ i.val ∨ j.val ≤ e.1.val) ∧ (e.2.val ≤ i.val ∨ j.val ≤ e.2.val)) ∨
      ((i.val ≤ e.1.val ∧ e.1.val ≤ j.val) ∧ (i.val ≤ e.2.val ∧ e.2.val ≤ j.val)) := by
  rw [bnd_mem_dissections] at hF
  have h0 := (bnd_mem_polyDiags _).mp (hF.1 he)
  have h1 := hF.2 _ hd _ he
  have h2 := hF.2 _ he _ hd
  have h3 := bnd_prod_ne hne
  rw [bnd_diagCross_iff] at h1 h2
  simp only at h1 h2 h3
  omega

private lemma bnd_splitL_mem {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) :
    bnd_splitL i j F ∈ dissections (k + i - j + 1) := by
  have hdv := (bnd_mem_polyDiags _).mp hd
  simp only at hdv
  rw [bnd_mem_dissections] at hF ⊢
  refine ⟨fun e he => ?_, fun d' hd' e he => ?_⟩
  · rw [bnd_mem_splitL] at he
    have h1 := (bnd_mem_polyDiags _).mp (hF.1 he.1)
    have h2 := bnd_prod_ne he.2
    rw [bnd_mem_polyDiags]
    simp only [bnd_vL_val] at h1 h2
    have := e.1.isLt; have := e.2.isLt; have := j.isLt
    split_ifs at h1 h2 <;> omega
  · rw [bnd_mem_splitL] at hd' he
    have h := hF.2 _ hd'.1 _ he.1
    rw [bnd_diagCross_iff] at h ⊢
    simp only [bnd_vL_val] at h
    split_ifs at h <;> omega

private lemma bnd_splitR_mem {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) :
    bnd_splitR i j F ∈ dissections (j - i + 1) := by
  have hdv := (bnd_mem_polyDiags _).mp hd
  simp only at hdv
  rw [bnd_mem_dissections] at hF ⊢
  refine ⟨fun e he => ?_, fun d' hd' e he => ?_⟩
  · rw [bnd_mem_splitR] at he
    have h1 := (bnd_mem_polyDiags _).mp (hF.1 he.1)
    have h2 := bnd_prod_ne he.2
    rw [bnd_mem_polyDiags]
    simp only [bnd_vR_val] at h1 h2
    have := e.1.isLt; have := e.2.isLt; have := j.isLt
    omega
  · rw [bnd_mem_splitR] at hd' he
    have h := hF.2 _ hd'.1 _ he.1
    rw [bnd_diagCross_iff] at h ⊢
    simp only [bnd_vR_val] at h
    omega

private lemma bnd_glue_mem {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {FL : Finset (Fin (k + i - j + 1) × Fin (k + i - j + 1))}
    {FR : Finset (Fin (j - i + 1) × Fin (j - i + 1))}
    (hL : FL ∈ dissections (k + i - j + 1)) (hR : FR ∈ dissections (j - i + 1)) :
    bnd_glue i j FL FR ∈ dissections k := by
  have hdv := (bnd_mem_polyDiags _).mp hd
  simp only at hdv
  have hj := j.isLt
  rw [bnd_mem_dissections] at hL hR ⊢
  refine ⟨fun e he => ?_, fun e he f hf => ?_⟩
  · simp only [bnd_glue, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at he
    rcases he with rfl | ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
    · exact hd
    · have h1 := (bnd_mem_polyDiags _).mp (hL.1 ha)
      have := a.1.isLt; have := a.2.isLt
      rw [bnd_mem_polyDiags]
      simp only [bnd_vL_val]
      split_ifs <;> omega
    · have h1 := (bnd_mem_polyDiags _).mp (hR.1 hb)
      have := b.1.isLt; have := b.2.isLt
      rw [bnd_mem_polyDiags]
      simp only [bnd_vR_val]
      omega
  · simp only [bnd_glue, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at he hf
    rw [bnd_diagCross_iff]
    rcases he with rfl | ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩ <;>
      rcases hf with rfl | ⟨a', ha', rfl⟩ | ⟨b', hb', rfl⟩
    · omega
    · have h1 := (bnd_mem_polyDiags _).mp (hL.1 ha')
      have := a'.1.isLt; have := a'.2.isLt
      simp only [bnd_vL_val]
      split_ifs <;> omega
    · have h1 := (bnd_mem_polyDiags _).mp (hR.1 hb')
      have := b'.1.isLt; have := b'.2.isLt
      simp only [bnd_vR_val]
      omega
    · have h1 := (bnd_mem_polyDiags _).mp (hL.1 ha)
      have := a.1.isLt; have := a.2.isLt
      simp only [bnd_vL_val]
      split_ifs <;> omega
    · have h1 := (bnd_mem_polyDiags _).mp (hL.1 ha)
      have h2 := (bnd_mem_polyDiags _).mp (hL.1 ha')
      have h3 := hL.2 _ ha _ ha'
      rw [bnd_diagCross_iff] at h3
      have := a.1.isLt; have := a.2.isLt; have := a'.1.isLt; have := a'.2.isLt
      simp only [bnd_vL_val]
      split_ifs <;> omega
    · have h1 := (bnd_mem_polyDiags _).mp (hL.1 ha)
      have h2 := (bnd_mem_polyDiags _).mp (hR.1 hb')
      have := a.1.isLt; have := a.2.isLt; have := b'.1.isLt; have := b'.2.isLt
      simp only [bnd_vL_val, bnd_vR_val]
      split_ifs <;> omega
    · have h1 := (bnd_mem_polyDiags _).mp (hR.1 hb)
      have := b.1.isLt; have := b.2.isLt
      simp only [bnd_vR_val]
      omega
    · have h1 := (bnd_mem_polyDiags _).mp (hR.1 hb)
      have h2 := (bnd_mem_polyDiags _).mp (hL.1 ha')
      have := b.1.isLt; have := b.2.isLt; have := a'.1.isLt; have := a'.2.isLt
      simp only [bnd_vL_val, bnd_vR_val]
      split_ifs <;> omega
    · have h1 := (bnd_mem_polyDiags _).mp (hR.1 hb)
      have h2 := (bnd_mem_polyDiags _).mp (hR.1 hb')
      have h3 := hR.2 _ hb _ hb'
      rw [bnd_diagCross_iff] at h3
      have := b.1.isLt; have := b.2.isLt; have := b'.1.isLt; have := b'.2.isLt
      simp only [bnd_vR_val]
      omega

private lemma bnd_glue_split {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F) :
    bnd_glue i j (bnd_splitL i j F) (bnd_splitR i j F) = F := by
  have hdv := (bnd_mem_polyDiags _).mp hd
  simp only at hdv
  ext e
  simp only [bnd_glue, Finset.mem_insert, Finset.mem_union, Finset.mem_image, bnd_mem_splitL,
    bnd_mem_splitR]
  constructor
  · rintro (rfl | ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
    · exact hdF
    · exact ha.1
    · exact hb.1
  · intro he
    by_cases hne : e = (i, j)
    · exact Or.inl hne
    right
    rcases bnd_cover hF hdF he hne with h | h
    · left
      refine ⟨(bnd_uL i j e.1, bnd_uL i j e.2), ?_, ?_⟩ <;>
        simp only [bnd_vL_uL h.1, bnd_vL_uL h.2]
      exact ⟨he, hne⟩
    · right
      refine ⟨(bnd_uR i j e.1, bnd_uR i j e.2), ?_, ?_⟩ <;>
        simp only [bnd_vR_uR h.1, bnd_vR_uR h.2]
      exact ⟨he, hne⟩

private lemma bnd_splitL_glue {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {FL : Finset (Fin (k + i - j + 1) × Fin (k + i - j + 1))}
    {FR : Finset (Fin (j - i + 1) × Fin (j - i + 1))}
    (hL : FL ∈ dissections (k + i - j + 1)) (hR : FR ∈ dissections (j - i + 1)) :
    bnd_splitL i j (bnd_glue i j FL FR) = FL := by
  have hdv := (bnd_mem_polyDiags _).mp hd
  simp only at hdv
  have hj := j.isLt
  rw [bnd_mem_dissections] at hL hR
  ext e
  rw [bnd_mem_splitL]
  simp only [bnd_glue, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨h | ⟨a, ha, he⟩ | ⟨b, hb, he⟩, hne⟩
    · exact absurd h hne
    · have h1 : a = e := by
        have := congrArg Prod.fst he; have := congrArg Prod.snd he
        exact Prod.ext (bnd_vL_inj (by omega) (by assumption))
          (bnd_vL_inj (by omega) (by assumption))
      exact h1 ▸ ha
    · exfalso
      have h1 := (bnd_mem_polyDiags _).mp (hR.1 hb)
      have h2 := bnd_prod_ne hne
      have e1 := congrArg (fun x => x.1.val) he
      have e2 := congrArg (fun x => x.2.val) he
      have := b.1.isLt; have := b.2.isLt; have := e.1.isLt; have := e.2.isLt
      simp only [bnd_vL_val, bnd_vR_val] at e1 e2 h2
      split_ifs at e1 e2 h2 <;> omega
  · intro he
    have h1 := (bnd_mem_polyDiags _).mp (hL.1 he)
    refine ⟨Or.inr (Or.inl ⟨e, he, rfl⟩), fun h => ?_⟩
    have e1 := congrArg (fun x => x.1.val) h
    have e2 := congrArg (fun x => x.2.val) h
    have := e.1.isLt; have := e.2.isLt
    simp only [bnd_vL_val] at e1 e2
    split_ifs at e1 e2 <;> omega

private lemma bnd_splitR_glue {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {FL : Finset (Fin (k + i - j + 1) × Fin (k + i - j + 1))}
    {FR : Finset (Fin (j - i + 1) × Fin (j - i + 1))}
    (hL : FL ∈ dissections (k + i - j + 1)) (hR : FR ∈ dissections (j - i + 1)) :
    bnd_splitR i j (bnd_glue i j FL FR) = FR := by
  have hdv := (bnd_mem_polyDiags _).mp hd
  simp only at hdv
  have hj := j.isLt
  rw [bnd_mem_dissections] at hL hR
  ext e
  rw [bnd_mem_splitR]
  simp only [bnd_glue, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨h | ⟨a, ha, he⟩ | ⟨b, hb, he⟩, hne⟩
    · exact absurd h hne
    · exfalso
      have h1 := (bnd_mem_polyDiags _).mp (hL.1 ha)
      have h2 := bnd_prod_ne hne
      have e1 := congrArg (fun x => x.1.val) he
      have e2 := congrArg (fun x => x.2.val) he
      have := a.1.isLt; have := a.2.isLt; have := e.1.isLt; have := e.2.isLt
      simp only [bnd_vL_val, bnd_vR_val] at e1 e2 h2
      split_ifs at e1 e2 h2 <;> omega
    · have h1 : b = e := by
        have := congrArg Prod.fst he; have := congrArg Prod.snd he
        exact Prod.ext (bnd_vR_inj (by assumption)) (bnd_vR_inj (by assumption))
      exact h1 ▸ hb
  · intro he
    have h1 := (bnd_mem_polyDiags _).mp (hR.1 he)
    refine ⟨Or.inr (Or.inr ⟨e, he, rfl⟩), fun h => ?_⟩
    have e1 := congrArg (fun x => x.1.val) h
    have e2 := congrArg (fun x => x.2.val) h
    have := e.1.isLt; have := e.2.isLt
    simp only [bnd_vR_val] at e1 e2
    omega

/-- Marking the diagonal `(i, j)` in a dissection is a bijection onto the pairs of dissections
of the two polygons of the cut. -/
private lemma bnd_sum_split {i j : Fin k} (hd : (i, j) ∈ polyDiags k) {γ : Type*}
    [AddCommMonoid γ]
    (H : Finset (Fin (k + i - j + 1) × Fin (k + i - j + 1)) →
      Finset (Fin (j - i + 1) × Fin (j - i + 1)) → γ) :
    ∑ F ∈ (dissections k).filter (fun F => (i, j) ∈ F), H (bnd_splitL i j F) (bnd_splitR i j F)
      = ∑ FL ∈ dissections (k + i - j + 1), ∑ FR ∈ dissections (j - i + 1), H FL FR := by
  rw [← Finset.sum_product']
  apply Finset.sum_nbij' (fun F => (bnd_splitL i j F, bnd_splitR i j F))
    (fun p => bnd_glue i j p.1 p.2)
  · intro F hF
    rw [Finset.mem_filter] at hF
    rw [Finset.mem_product]
    exact ⟨bnd_splitL_mem hd hF.1, bnd_splitR_mem hd hF.1⟩
  · intro p hp
    rw [Finset.mem_product] at hp
    rw [Finset.mem_filter]
    exact ⟨bnd_glue_mem hd hp.1 hp.2, Finset.mem_insert_self _ _⟩
  · intro F hF
    rw [Finset.mem_filter] at hF
    exact bnd_glue_split hd hF.1 hF.2
  · intro p hp
    rw [Finset.mem_product] at hp
    exact Prod.ext (bnd_splitL_glue hd hp.1 hp.2) (bnd_splitR_glue hd hp.1 hp.2)
  · intro F _
    rfl

end Split

/-! ## Face corners of the two polygons of a cut -/

section Corners

variable {k : ℕ}

private lemma bnd_minmax {n : ℕ} {v u : Fin n} (h : u ≠ v) :
    ((min v u).val = v.val ∧ (max v u).val = u.val ∧ v.val < u.val) ∨
      ((min v u).val = u.val ∧ (max v u).val = v.val ∧ u.val < v.val) := by
  rcases lt_or_gt_of_ne h with h' | h'
  · right
    rw [min_eq_right h'.le, max_eq_left h'.le]
    exact ⟨rfl, rfl, h'⟩
  · left
    rw [min_eq_left h'.le, max_eq_right h'.le]
    exact ⟨rfl, rfl, h'⟩

private lemma bnd_mem_polyCorners {n : ℕ} (F : Finset (Fin n × Fin n)) (v : Fin n)
    (p : Fin n × Fin n) :
    p ∈ polyCorners F v ↔ PolyNbr F v p.1 ∧ PolyNbr F v p.2 ∧ polyOff v p.1 < polyOff v p.2 ∧
      ∀ u, PolyNbr F v u → ¬(polyOff v p.1 < polyOff v u ∧ polyOff v u < polyOff v p.2) := by
  simp [polyCorners]

/-- Neighbours in a dissection containing `(i, j)` lie on a common side of it. -/
private lemma bnd_nbr_side {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F) {v u : Fin k}
    (h : PolyNbr F v u) :
    ((v.val ≤ i.val ∨ j.val ≤ v.val) ∧ (u.val ≤ i.val ∨ j.val ≤ u.val)) ∨
      ((i.val ≤ v.val ∧ v.val ≤ j.val) ∧ (i.val ≤ u.val ∧ u.val ≤ j.val)) := by
  have hdv := (bnd_mem_polyDiags _).mp hd
  simp only at hdv
  have := v.isLt; have := u.isLt
  obtain ⟨hne, h⟩ := h
  have hmm := bnd_minmax hne
  rcases h with h | h | h
  · rw [bnd_polyOff_eq] at h; split_ifs at h <;> omega
  · rw [bnd_polyOff_eq] at h; split_ifs at h <;> omega
  · by_cases he : (min v u, max v u) = (i, j)
    · have e1 := congrArg (fun x => x.1.val) he
      have e2 := congrArg (fun x => x.2.val) he
      simp only at e1 e2
      omega
    · have := bnd_cover hF hdF h he
      simp only at this
      omega

/-- `bnd_vL` preserves and reflects neighbours. -/
private lemma bnd_nbr_vL {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) (v w : Fin (k + i - j + 1)) :
    PolyNbr F (bnd_vL i j v) (bnd_vL i j w) ↔ PolyNbr (bnd_splitL i j F) v w := by
  have hdv := (bnd_mem_polyDiags _).mp hd
  simp only at hdv
  have hmono := (bnd_vL_strictMono (i := i) (j := j) (by omega)).monotone
  unfold PolyNbr
  rw [← hmono.map_min, ← hmono.map_max, bnd_mem_splitL]
  by_cases hw : w = v
  · subst hw; simp
  have hw' : bnd_vL i j w ≠ bnd_vL i j v := fun h => hw (bnd_vL_inj (by omega) h)
  have hmm := bnd_minmax hw
  have := v.isLt; have := w.isLt; have := j.isLt
  have key : ((bnd_vL i j (min v w), bnd_vL i j (max v w)) = (i, j) →
      (polyOff v w = 1 ∨ polyOff v w + 1 = k + i - j + 1)) ∧
      ((bnd_vL i j (min v w), bnd_vL i j (max v w)) ≠ (i, j) →
        ((polyOff (bnd_vL i j v) (bnd_vL i j w) = 1 ∨
          polyOff (bnd_vL i j v) (bnd_vL i j w) + 1 = k) ↔
        (polyOff v w = 1 ∨ polyOff v w + 1 = k + i - j + 1))) := by
    constructor
    · intro he
      have e1 := congrArg (fun x => x.1.val) he
      have e2 := congrArg (fun x => x.2.val) he
      simp only [bnd_vL_val] at e1 e2
      simp only [bnd_polyOff_eq]
      split_ifs at e1 e2 ⊢ <;> omega
    · intro he
      have he' := bnd_prod_ne he
      simp only [bnd_vL_val] at he'
      simp only [bnd_polyOff_eq, bnd_vL_val]
      split_ifs at he' ⊢ <;> omega
  by_cases hq : (bnd_vL i j (min v w), bnd_vL i j (max v w)) = (i, j)
  · have hB := key.1 hq
    rw [hq]
    exact ⟨fun _ => ⟨hw, hB.elim Or.inl (fun h => Or.inr (Or.inl h))⟩,
      fun _ => ⟨hw', Or.inr (Or.inr hdF)⟩⟩
  · have hAB := key.2 hq
    constructor
    · rintro ⟨-, h⟩
      refine ⟨hw, ?_⟩
      rcases h with h | h | h
      · exact (hAB.mp (Or.inl h)).elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact (hAB.mp (Or.inr h)).elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact Or.inr (Or.inr ⟨h, hq⟩)
    · rintro ⟨-, h⟩
      refine ⟨hw', ?_⟩
      rcases h with h | h | h
      · exact (hAB.mpr (Or.inl h)).elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact (hAB.mpr (Or.inr h)).elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact Or.inr (Or.inr h.1)

/-- `bnd_vR` preserves and reflects neighbours. -/
private lemma bnd_nbr_vR {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) (v w : Fin (j - i + 1)) :
    PolyNbr F (bnd_vR i j v) (bnd_vR i j w) ↔ PolyNbr (bnd_splitR i j F) v w := by
  have hdv := (bnd_mem_polyDiags _).mp hd
  simp only at hdv
  have hmono := (bnd_vR_strictMono i j).monotone
  unfold PolyNbr
  rw [← hmono.map_min, ← hmono.map_max, bnd_mem_splitR]
  by_cases hw : w = v
  · subst hw; simp
  have hw' : bnd_vR i j w ≠ bnd_vR i j v := fun h => hw (bnd_vR_inj h)
  have hmm := bnd_minmax hw
  have := v.isLt; have := w.isLt; have := j.isLt
  have key : ((bnd_vR i j (min v w), bnd_vR i j (max v w)) = (i, j) →
      (polyOff v w = 1 ∨ polyOff v w + 1 = j - i + 1)) ∧
      ((bnd_vR i j (min v w), bnd_vR i j (max v w)) ≠ (i, j) →
        ((polyOff (bnd_vR i j v) (bnd_vR i j w) = 1 ∨
          polyOff (bnd_vR i j v) (bnd_vR i j w) + 1 = k) ↔
        (polyOff v w = 1 ∨ polyOff v w + 1 = j - i + 1))) := by
    constructor
    · intro he
      have e1 := congrArg (fun x => x.1.val) he
      have e2 := congrArg (fun x => x.2.val) he
      simp only [bnd_vR_val] at e1 e2
      simp only [bnd_polyOff_eq]
      split_ifs <;> omega
    · intro he
      have he' := bnd_prod_ne he
      simp only [bnd_vR_val] at he'
      simp only [bnd_polyOff_eq, bnd_vR_val, Nat.add_le_add_iff_left]
      split_ifs <;> omega
  by_cases hq : (bnd_vR i j (min v w), bnd_vR i j (max v w)) = (i, j)
  · have hB := key.1 hq
    rw [hq]
    exact ⟨fun _ => ⟨hw, hB.elim Or.inl (fun h => Or.inr (Or.inl h))⟩,
      fun _ => ⟨hw', Or.inr (Or.inr hdF)⟩⟩
  · have hAB := key.2 hq
    constructor
    · rintro ⟨-, h⟩
      refine ⟨hw, ?_⟩
      rcases h with h | h | h
      · exact (hAB.mp (Or.inl h)).elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact (hAB.mp (Or.inr h)).elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact Or.inr (Or.inr ⟨h, hq⟩)
    · rintro ⟨-, h⟩
      refine ⟨hw', ?_⟩
      rcases h with h | h | h
      · exact (hAB.mpr (Or.inl h)).elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact (hAB.mpr (Or.inr h)).elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact Or.inr (Or.inr h.1)

/-- The face corners of a dissection as a set of triples `(v, w, w')`. -/
private def bnd_cornerP {n : ℕ} (F : Finset (Fin n × Fin n)) : Finset (Fin n × (Fin n × Fin n)) :=
  Finset.univ.filter fun x => x.2 ∈ polyCorners F x.1

private lemma bnd_prod_corners {n : ℕ} (F : Finset (Fin n × Fin n))
    (f : Fin n → Fin n × Fin n → ℂ) :
    ∏ v, ∏ p ∈ polyCorners F v, f v p = ∏ x ∈ bnd_cornerP F, f x.1 x.2 := by
  rw [bnd_cornerP, Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun v _ => ?_
  dsimp only
  rw [Finset.prod_ite_mem, Finset.univ_inter]

private lemma bnd_nbr_diag {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) : PolyNbr F i j ∧ PolyNbr F j i := by
  have hdv := (bnd_mem_polyDiags _).mp hd
  simp only at hdv
  have hle : i ≤ j := by rw [Fin.le_def]; omega
  have hne : j ≠ i := fun h => by rw [h] at hdv; omega
  refine ⟨⟨hne, Or.inr (Or.inr ?_)⟩, ⟨hne.symm, Or.inr (Or.inr ?_)⟩⟩
  · rwa [min_eq_left hle, max_eq_right hle]
  · rwa [min_eq_right hle, max_eq_left hle]

private lemma bnd_corner_toL {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) {v w w' : Fin k}
    (hv : v.val ≤ i.val ∨ j.val ≤ v.val) (hw : w.val ≤ i.val ∨ j.val ≤ w.val)
    (hw' : w'.val ≤ i.val ∨ j.val ≤ w'.val) (h : (w, w') ∈ polyCorners F v) :
    (bnd_uL i j w, bnd_uL i j w') ∈ polyCorners (bnd_splitL i j F) (bnd_uL i j v) := by
  have hdv := (bnd_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  rw [← bnd_vL_uL hv, ← bnd_vL_uL hw, ← bnd_vL_uL hw'] at h
  rw [bnd_mem_polyCorners] at h ⊢
  dsimp only at h ⊢
  obtain ⟨n1, n2, o, nb⟩ := h
  refine ⟨(bnd_nbr_vL hd hdF _ _).mp n1, (bnd_nbr_vL hd hdF _ _).mp n2,
    (bnd_off_vL hij _ _ _).mpr o, fun u hu => ?_⟩
  rw [bnd_off_vL hij _ _ u, bnd_off_vL hij _ u _]
  exact nb _ ((bnd_nbr_vL hd hdF _ _).mpr hu)

private lemma bnd_corner_toR {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) {v w w' : Fin k}
    (hv : i.val ≤ v.val ∧ v.val ≤ j.val) (hw : i.val ≤ w.val ∧ w.val ≤ j.val)
    (hw' : i.val ≤ w'.val ∧ w'.val ≤ j.val) (h : (w, w') ∈ polyCorners F v) :
    (bnd_uR i j w, bnd_uR i j w') ∈ polyCorners (bnd_splitR i j F) (bnd_uR i j v) := by
  rw [← bnd_vR_uR hv, ← bnd_vR_uR hw, ← bnd_vR_uR hw'] at h
  rw [bnd_mem_polyCorners] at h ⊢
  dsimp only at h ⊢
  obtain ⟨n1, n2, o, nb⟩ := h
  refine ⟨(bnd_nbr_vR hd hdF _ _).mp n1, (bnd_nbr_vR hd hdF _ _).mp n2,
    (bnd_off_vR i j _ _ _).mpr o, fun u hu => ?_⟩
  rw [bnd_off_vR i j _ _ u, bnd_off_vR i j _ u _]
  exact nb _ ((bnd_nbr_vR hd hdF _ _).mpr hu)

private lemma bnd_corner_fromL {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F)
    {v w w' : Fin (k + i - j + 1)} (h : (w, w') ∈ polyCorners (bnd_splitL i j F) v) :
    (bnd_vL i j w, bnd_vL i j w') ∈ polyCorners F (bnd_vL i j v) := by
  have hdv := (bnd_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  rw [bnd_mem_polyCorners] at h ⊢
  dsimp only at h ⊢
  obtain ⟨n1, n2, o, nb⟩ := h
  refine ⟨(bnd_nbr_vL hd hdF _ _).mpr n1, (bnd_nbr_vL hd hdF _ _).mpr n2,
    (bnd_off_vL hij _ _ _).mp o, fun u hu => ?_⟩
  by_cases huL : u.val ≤ i.val ∨ j.val ≤ u.val
  · rw [← bnd_vL_uL huL] at hu ⊢
    rw [← bnd_off_vL hij, ← bnd_off_vL hij]
    exact nb _ ((bnd_nbr_vL hd hdF _ _).mp hu)
  · have hs := bnd_nbr_side hd hF hdF hu
    have h1 : w ≠ v := n1.1
    have h2 : w' ≠ v := n2.1
    have h1' : w.val ≠ v.val := fun e => h1 (Fin.ext e)
    have h2' : w'.val ≠ v.val := fun e => h2 (Fin.ext e)
    have := v.isLt; have := w.isLt; have := w'.isLt; have := u.isLt
    simp only [bnd_vL_val] at hs
    simp only [bnd_polyOff_eq, bnd_vL_val]
    split_ifs at hs ⊢ <;> omega

private lemma bnd_corner_fromR {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F)
    {v w w' : Fin (j - i + 1)} (h : (w, w') ∈ polyCorners (bnd_splitR i j F) v) :
    (bnd_vR i j w, bnd_vR i j w') ∈ polyCorners F (bnd_vR i j v) := by
  have hdv := (bnd_mem_polyDiags _).mp hd
  simp only at hdv
  rw [bnd_mem_polyCorners] at h ⊢
  dsimp only at h ⊢
  obtain ⟨n1, n2, o, nb⟩ := h
  refine ⟨(bnd_nbr_vR hd hdF _ _).mpr n1, (bnd_nbr_vR hd hdF _ _).mpr n2,
    (bnd_off_vR i j _ _ _).mp o, fun u hu => ?_⟩
  by_cases huR : i.val ≤ u.val ∧ u.val ≤ j.val
  · rw [← bnd_vR_uR huR] at hu ⊢
    rw [← bnd_off_vR, ← bnd_off_vR]
    exact nb _ ((bnd_nbr_vR hd hdF _ _).mp hu)
  · have hs := bnd_nbr_side hd hF hdF hu
    have h1 : w ≠ v := n1.1
    have h2 : w' ≠ v := n2.1
    have h1' : w.val ≠ v.val := fun e => h1 (Fin.ext e)
    have h2' : w'.val ≠ v.val := fun e => h2 (Fin.ext e)
    have := v.isLt; have := w.isLt; have := w'.isLt; have := u.isLt; have := j.isLt
    simp only [bnd_vR_val] at hs
    have c1 := bnd_polyOff_cases (bnd_vR i j v) (bnd_vR i j w)
    have c2 := bnd_polyOff_cases (bnd_vR i j v) u
    have c3 := bnd_polyOff_cases (bnd_vR i j v) (bnd_vR i j w')
    simp only [bnd_vR_val] at c1 c2 c3
    omega

/-- Every face corner lies in one of the two polygons of the cut. -/
private lemma bnd_corner_sides {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F) {v w w' : Fin k}
    (h : (w, w') ∈ polyCorners F v) :
    ((v.val ≤ i.val ∨ j.val ≤ v.val) ∧ (w.val ≤ i.val ∨ j.val ≤ w.val) ∧
        (w'.val ≤ i.val ∨ j.val ≤ w'.val)) ∨
      ((i.val ≤ v.val ∧ v.val ≤ j.val) ∧ (i.val ≤ w.val ∧ w.val ≤ j.val) ∧
        (i.val ≤ w'.val ∧ w'.val ≤ j.val)) := by
  have hdv := (bnd_mem_polyDiags _).mp hd
  simp only at hdv
  rw [bnd_mem_polyCorners] at h
  dsimp only at h
  obtain ⟨n1, n2, o, nb⟩ := h
  have s1 := bnd_nbr_side hd hF hdF n1
  have s2 := bnd_nbr_side hd hF hdF n2
  have h1' : w.val ≠ v.val := fun e => n1.1 (Fin.ext e)
  have h2' : w'.val ≠ v.val := fun e => n2.1 (Fin.ext e)
  have := v.isLt; have := w.isLt; have := w'.isLt; have := j.isLt
  by_cases hvi : v = i
  · subst hvi
    have hb := nb j (bnd_nbr_diag hd hdF).1
    have c1 := bnd_polyOff_cases v w
    have c2 := bnd_polyOff_cases v w'
    have c3 := bnd_polyOff_cases v j
    omega
  by_cases hvj : v = j
  · subst hvj
    have hb := nb i (bnd_nbr_diag hd hdF).2
    have c1 := bnd_polyOff_cases v w
    have c2 := bnd_polyOff_cases v w'
    have c3 := bnd_polyOff_cases v i
    omega
  have hvi' : v.val ≠ i.val := fun e => hvi (Fin.ext e)
  have hvj' : v.val ≠ j.val := fun e => hvj (Fin.ext e)
  omega

/-- The face corners of `F` are those of the two polygons of the cut, transported by the vertex
maps. -/
private lemma bnd_prod_cornerP_split {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F)
    (g : Fin k × (Fin k × Fin k) → ℂ) :
    ∏ x ∈ bnd_cornerP F, g x =
      (∏ x ∈ bnd_cornerP (bnd_splitL i j F),
        g (bnd_vL i j x.1, (bnd_vL i j x.2.1, bnd_vL i j x.2.2))) *
      ∏ x ∈ bnd_cornerP (bnd_splitR i j F),
        g (bnd_vR i j x.1, (bnd_vR i j x.2.1, bnd_vR i j x.2.2)) := by
  have hdv := (bnd_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  set ψL : Fin (k + i - j + 1) × (Fin (k + i - j + 1) × Fin (k + i - j + 1)) →
      Fin k × (Fin k × Fin k) := fun x => (bnd_vL i j x.1, (bnd_vL i j x.2.1, bnd_vL i j x.2.2))
  set ψR : Fin (j - i + 1) × (Fin (j - i + 1) × Fin (j - i + 1)) →
      Fin k × (Fin k × Fin k) := fun x => (bnd_vR i j x.1, (bnd_vR i j x.2.1, bnd_vR i j x.2.2))
  have hS : bnd_cornerP F = (bnd_cornerP (bnd_splitL i j F)).image ψL ∪
      (bnd_cornerP (bnd_splitR i j F)).image ψR := by
    ext ⟨v, w, w'⟩
    simp only [bnd_cornerP, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro h
      rcases bnd_corner_sides hd hF hdF h with ⟨hv, hw, hw'⟩ | ⟨hv, hw, hw'⟩
      · left
        refine ⟨(bnd_uL i j v, (bnd_uL i j w, bnd_uL i j w')),
          bnd_corner_toL hd hdF hv hw hw' h, ?_⟩
        simp only [ψL, bnd_vL_uL hv, bnd_vL_uL hw, bnd_vL_uL hw']
      · right
        refine ⟨(bnd_uR i j v, (bnd_uR i j w, bnd_uR i j w')),
          bnd_corner_toR hd hdF hv hw hw' h, ?_⟩
        simp only [ψR, bnd_vR_uR hv, bnd_vR_uR hw, bnd_vR_uR hw']
    · rintro (⟨x, hx, hxe⟩ | ⟨x, hx, hxe⟩)
      · simp only [ψL, Prod.mk.injEq] at hxe
        obtain ⟨rfl, rfl, rfl⟩ := hxe
        exact bnd_corner_fromL hd hF hdF hx
      · simp only [ψR, Prod.mk.injEq] at hxe
        obtain ⟨rfl, rfl, rfl⟩ := hxe
        exact bnd_corner_fromR hd hF hdF hx
  have hinjL : Set.InjOn ψL (bnd_cornerP (bnd_splitL i j F)) := by
    intro x _ y _ hxy
    simp only [ψL, Prod.mk.injEq] at hxy
    exact Prod.ext (bnd_vL_inj hij hxy.1)
      (Prod.ext (bnd_vL_inj hij hxy.2.1) (bnd_vL_inj hij hxy.2.2))
  have hinjR : Set.InjOn ψR (bnd_cornerP (bnd_splitR i j F)) := by
    intro x _ y _ hxy
    simp only [ψR, Prod.mk.injEq] at hxy
    exact Prod.ext (bnd_vR_inj hxy.1) (Prod.ext (bnd_vR_inj hxy.2.1) (bnd_vR_inj hxy.2.2))
  have hdisj : Disjoint ((bnd_cornerP (bnd_splitL i j F)).image ψL)
      ((bnd_cornerP (bnd_splitR i j F)).image ψR) := by
    rw [Finset.disjoint_left]
    rintro z hzL hzR
    simp only [Finset.mem_image, bnd_cornerP, Finset.mem_filter, Finset.mem_univ,
      true_and] at hzL hzR
    obtain ⟨x, hx, rfl⟩ := hzL
    obtain ⟨y, hy, hxy⟩ := hzR
    simp only [ψL, ψR, Prod.mk.injEq] at hxy
    obtain ⟨e1, e2, e3⟩ := hxy
    rw [bnd_mem_polyCorners] at hx
    obtain ⟨n1, n2, o, -⟩ := hx
    have h1 : x.2.1.val ≠ x.1.val := fun e => n1.1 (Fin.ext e)
    have h2 : x.2.2.val ≠ x.1.val := fun e => n2.1 (Fin.ext e)
    have h3 : x.2.1.val ≠ x.2.2.val := by
      intro e
      have : x.2.1 = x.2.2 := Fin.ext e
      rw [this] at o
      exact lt_irrefl _ o
    have f1 := congrArg Fin.val e1
    have f2 := congrArg Fin.val e2
    have f3 := congrArg Fin.val e3
    have := y.1.isLt; have := y.2.1.isLt; have := y.2.2.isLt; have := j.isLt
    have := x.1.isLt; have := x.2.1.isLt; have := x.2.2.isLt
    simp only [bnd_vL_val, bnd_vR_val] at f1 f2 f3
    split_ifs at f1 f2 f3 <;> omega
  rw [hS, Finset.prod_union hdisj, Finset.prod_image hinjL, Finset.prod_image hinjR]


private lemma bnd_corner_conds {n : ℕ} {F : Finset (Fin n × Fin n)} {v : Fin n}
    {p : Fin n × Fin n} (h : p ∈ polyCorners F v) :
    PolyNbr F v p.1 ∧ PolyNbr F v p.2 ∧ polyOff v p.1 + 1 ≠ n ∧ polyOff v p.2 ≠ 1 := by
  rw [bnd_mem_polyCorners] at h
  obtain ⟨n1, n2, o, -⟩ := h
  have h1 : p.1.val ≠ v.val := fun e => n1.1 (Fin.ext e)
  have h2 : p.2.val ≠ v.val := fun e => n2.1 (Fin.ext e)
  have c1 := bnd_polyOff_cases v p.1
  have c2 := bnd_polyOff_cases v p.2
  have := v.isLt; have := p.1.isLt; have := p.2.isLt
  exact ⟨n1, n2, by omega, by omega⟩

/-- The diagonals of the polygon of Cut_L as diagonals of `F`. -/
private def bnd_ιL (i j : Fin k) (F : Finset (Fin k × Fin k)) (e : ↥(bnd_splitL i j F)) : ↥F :=
  ⟨(bnd_vL i j e.1.1, bnd_vL i j e.1.2), ((bnd_mem_splitL _).mp e.2).1⟩

/-- The diagonals of the polygon of Cut_R as diagonals of `F`. -/
private def bnd_ιR (i j : Fin k) (F : Finset (Fin k × Fin k)) (e : ↥(bnd_splitR i j F)) : ↥F :=
  ⟨(bnd_vR i j e.1.1, bnd_vR i j e.1.2), ((bnd_mem_splitR _).mp e.2).1⟩

/-- The edge labels of the polygon of Cut_L: the side `i` carries the outer copy of the
label of `(i, j)`. -/
private lemma bnd_edgeLab_L {L : ℕ} {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) (y : Fin k → Fin L) (cIn cOut : ↥F → Fin L)
    {v w : Fin (k + i - j + 1)} (hn : PolyNbr (bnd_splitL i j F) v w) (small : Bool)
    (hs : if small then polyOff v w ≠ 1 else polyOff v w + 1 ≠ k + i - j + 1) :
    edgeLab (bnd_splitL i j F)
        (fun p => if p.val = i.val then cOut ⟨(i, j), hdF⟩ else y (bnd_vL i j p))
        (fun e => cIn (bnd_ιL i j F e)) (fun e => cOut (bnd_ιL i j F e)) v w small =
      edgeLab F y cIn cOut (bnd_vL i j v) (bnd_vL i j w) small := by
  have hdv := (bnd_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  have hsm := bnd_vL_strictMono (i := i) (j := j) hij
  have hmono := hsm.monotone
  simp only [edgeLab, ← hmono.map_min, ← hmono.map_max]
  obtain ⟨hne, hside⟩ := hn
  have hmm := bnd_minmax hne
  have cv := bnd_vL_cases i j v
  have cw := bnd_vL_cases i j w
  have co := bnd_polyOff_cases v w
  have co' := bnd_polyOff_cases (bnd_vL i j v) (bnd_vL i j w)
  have := v.isLt; have := w.isLt; have := j.isLt
  have hlt : decide (v < w) = decide (bnd_vL i j v < bnd_vL i j w) := by
    simp only [hsm.lt_iff_lt]
  by_cases h' : (min v w, max v w) ∈ bnd_splitL i j F
  · have h1 : (bnd_vL i j (min v w), bnd_vL i j (max v w)) ∈ F :=
      ((bnd_mem_splitL _).mp h').1
    rw [dite_eq_left h', dite_eq_left h1, hlt]
    rfl
  · rw [dite_eq_right h']
    have hside' : polyOff v w = 1 ∨ polyOff v w + 1 = k + i - j + 1 := by
      rcases hside with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h h'
    by_cases hq : (bnd_vL i j (min v w), bnd_vL i j (max v w)) = (i, j)
    · have h1 : (bnd_vL i j (min v w), bnd_vL i j (max v w)) ∈ F := hq ▸ hdF
      rw [dite_eq_left h1]
      have e1 := congrArg (fun x => x.1.val) hq
      have e2 := congrArg (fun x => x.2.val) hq
      have cmin := bnd_vL_cases i j (min v w)
      have cmax := bnd_vL_cases i j (max v w)
      simp only at e1 e2
      have hsub : (⟨(bnd_vL i j (min v w), bnd_vL i j (max v w)), h1⟩ : ↥F) = ⟨(i, j), hdF⟩ :=
        Subtype.ext hq
      cases small
      · simp only [Bool.false_eq_true, ite_false] at hs
        have hv : v.val = i.val := by omega
        have hw : ¬ bnd_vL i j v < bnd_vL i j w → False := by
          intro h; rw [Fin.lt_def] at h; omega
        have hpos : polyOff v w = 1 := by omega
        rw [ite_eq_left hpos, ite_eq_left hv, hsub]
        have : decide (bnd_vL i j v < bnd_vL i j w) = true := by
          by_contra hc; exact hw (by simpa using hc)
        rw [this]
        rfl
      · simp only [ite_true] at hs
        have hw : w.val = i.val := by omega
        have hv : ¬ bnd_vL i j v < bnd_vL i j w := by
          rw [Fin.lt_def]; omega
        rw [ite_eq_right hs, ite_eq_left hw, hsub]
        simp [hv]
    · have h1 : (bnd_vL i j (min v w), bnd_vL i j (max v w)) ∉ F :=
        fun h => h' ((bnd_mem_splitL _).mpr ⟨h, hq⟩)
      rw [dite_eq_right h1]
      clear hmm
      by_cases h1 : polyOff v w = 1
      · have h2 : polyOff (bnd_vL i j v) (bnd_vL i j w) = 1 := by
          have hq' := bnd_prod_ne hq
          simp only at hq'
          have hw1 : (w.val = v.val + 1) ∨ (v.val + 1 = k + i - j + 1 ∧ w.val = 0) := by omega
          rcases hw1 with hw1 | hw1
          · have hvw : v < w := by rw [Fin.lt_def]; omega
            rw [min_eq_left hvw.le, max_eq_right hvw.le] at hq'
            omega
          · have hvw : w < v := by rw [Fin.lt_def]; omega
            rw [min_eq_right hvw.le, max_eq_left hvw.le] at hq'
            omega
        have h3 : v.val ≠ i.val := by
          clear co'
          have hmm := bnd_minmax hne
          have hq' := bnd_prod_ne hq
          have cmin := bnd_vL_cases i j (min v w)
          have cmax := bnd_vL_cases i j (max v w)
          simp only at hq'
          omega
        rw [ite_eq_left h1, ite_eq_left h2, ite_eq_right h3]
      · have h2 : polyOff (bnd_vL i j v) (bnd_vL i j w) ≠ 1 := by omega
        have h3 : w.val ≠ i.val := by
          clear co'
          have hmm := bnd_minmax hne
          have hq' := bnd_prod_ne hq
          have cmin := bnd_vL_cases i j (min v w)
          have cmax := bnd_vL_cases i j (max v w)
          simp only at hq'
          omega
        rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]

/-- The edge labels of the polygon of Cut_R: the last side carries the inner copy of the
label of `(i, j)`. -/
private lemma bnd_edgeLab_R {L : ℕ} {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hdF : (i, j) ∈ F) (y : Fin k → Fin L) (cIn cOut : ↥F → Fin L)
    {v w : Fin (j - i + 1)} (hn : PolyNbr (bnd_splitR i j F) v w) (small : Bool)
    (hs : if small then polyOff v w ≠ 1 else polyOff v w + 1 ≠ j - i + 1) :
    edgeLab (bnd_splitR i j F)
        (fun q => if q.val = j.val - i.val then cIn ⟨(i, j), hdF⟩ else y (bnd_vR i j q))
        (fun e => cIn (bnd_ιR i j F e)) (fun e => cOut (bnd_ιR i j F e)) v w small =
      edgeLab F y cIn cOut (bnd_vR i j v) (bnd_vR i j w) small := by
  have hdv := (bnd_mem_polyDiags _).mp hd
  simp only at hdv
  have hsm := bnd_vR_strictMono i j
  have hmono := hsm.monotone
  simp only [edgeLab, ← hmono.map_min, ← hmono.map_max]
  obtain ⟨hne, hside⟩ := hn
  have hmm := bnd_minmax hne
  have cv := bnd_vR_val i j v
  have cw := bnd_vR_val i j w
  have co := bnd_polyOff_cases v w
  have co' := bnd_polyOff_cases (bnd_vR i j v) (bnd_vR i j w)
  have := v.isLt; have := w.isLt; have := j.isLt
  have hlt : decide (v < w) = decide (bnd_vR i j v < bnd_vR i j w) := by
    simp only [hsm.lt_iff_lt]
  by_cases h' : (min v w, max v w) ∈ bnd_splitR i j F
  · have h1 : (bnd_vR i j (min v w), bnd_vR i j (max v w)) ∈ F :=
      ((bnd_mem_splitR _).mp h').1
    rw [dite_eq_left h', dite_eq_left h1, hlt]
    rfl
  · rw [dite_eq_right h']
    have hside' : polyOff v w = 1 ∨ polyOff v w + 1 = j - i + 1 := by
      rcases hside with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h h'
    by_cases hq : (bnd_vR i j (min v w), bnd_vR i j (max v w)) = (i, j)
    · have h1 : (bnd_vR i j (min v w), bnd_vR i j (max v w)) ∈ F := hq ▸ hdF
      rw [dite_eq_left h1]
      have e1 := congrArg (fun x => x.1.val) hq
      have e2 := congrArg (fun x => x.2.val) hq
      have cmin := bnd_vR_val i j (min v w)
      have cmax := bnd_vR_val i j (max v w)
      simp only at e1 e2
      have hsub : (⟨(bnd_vR i j (min v w), bnd_vR i j (max v w)), h1⟩ : ↥F) = ⟨(i, j), hdF⟩ :=
        Subtype.ext hq
      cases small
      · simp only [Bool.false_eq_true, ite_false] at hs
        have hv : v.val = j.val - i.val := by omega
        have hw : ¬ bnd_vR i j v < bnd_vR i j w := by
          rw [Fin.lt_def]; omega
        have hpos : polyOff v w = 1 := by omega
        rw [ite_eq_left hpos, ite_eq_left hv, hsub]
        simp [hw]
      · simp only [ite_true] at hs
        have hw : w.val = j.val - i.val := by omega
        have hv : bnd_vR i j v < bnd_vR i j w := by
          rw [Fin.lt_def]; omega
        rw [ite_eq_right hs, ite_eq_left hw, hsub]
        simp [hv]
    · have h1 : (bnd_vR i j (min v w), bnd_vR i j (max v w)) ∉ F :=
        fun h => h' ((bnd_mem_splitR _).mpr ⟨h, hq⟩)
      rw [dite_eq_right h1]
      clear hmm
      by_cases h1 : polyOff v w = 1
      · have h2 : polyOff (bnd_vR i j v) (bnd_vR i j w) = 1 := by
          have hq' := bnd_prod_ne hq
          simp only at hq'
          have hw1 : (w.val = v.val + 1) ∨ (v.val + 1 = j - i + 1 ∧ w.val = 0) := by omega
          rcases hw1 with hw1 | hw1
          · have hvw : v < w := by rw [Fin.lt_def]; omega
            rw [min_eq_left hvw.le, max_eq_right hvw.le] at hq'
            omega
          · have hvw : w < v := by rw [Fin.lt_def]; omega
            rw [min_eq_right hvw.le, max_eq_left hvw.le] at hq'
            omega
        have h3 : v.val ≠ j.val - i.val := by
          clear co'
          have hmm := bnd_minmax hne
          have hq' := bnd_prod_ne hq
          have cmin := bnd_vR_val i j (min v w)
          have cmax := bnd_vR_val i j (max v w)
          simp only at hq'
          omega
        rw [ite_eq_left h1, ite_eq_left h2, ite_eq_right h3]
      · have h2 : polyOff (bnd_vR i j v) (bnd_vR i j w) ≠ 1 := by omega
        have h3 : w.val ≠ j.val - i.val := by
          clear co'
          have hmm := bnd_minmax hne
          have hq' := bnd_prod_ne hq
          have cmin := bnd_vR_val i j (min v w)
          have cmax := bnd_vR_val i j (max v w)
          simp only at hq'
          omega
        rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]


/-- The corner product of `F` splits into the corner products of the two polygons of the cut,
with the outer copy of the label of `(i, j)` on the side `i` of Cut_L and its inner copy on
the last side of Cut_R. -/
private lemma bnd_corners_split {L : ℕ} {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F)
    (M : Matrix (Fin L) (Fin L) ℂ) (σ : Fin k → Bool) (y : Fin k → Fin L)
    (cIn cOut : ↥F → Fin L) :
    (∏ v : Fin k, ∏ p ∈ polyCorners F v,
        sgnMat M (σ v) (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false)) =
      (∏ v : Fin (k + i - j + 1), ∏ p ∈ polyCorners (bnd_splitL i j F) v,
        sgnMat M (cutLSgn σ i j v)
          (edgeLab (bnd_splitL i j F)
            (fun p => if p.val = i.val then cOut ⟨(i, j), hdF⟩ else y (bnd_vL i j p))
            (fun e => cIn (bnd_ιL i j F e)) (fun e => cOut (bnd_ιL i j F e)) v p.2 true)
          (edgeLab (bnd_splitL i j F)
            (fun p => if p.val = i.val then cOut ⟨(i, j), hdF⟩ else y (bnd_vL i j p))
            (fun e => cIn (bnd_ιL i j F e)) (fun e => cOut (bnd_ιL i j F e)) v p.1 false)) *
      (∏ v : Fin (j - i + 1), ∏ p ∈ polyCorners (bnd_splitR i j F) v,
        sgnMat M (cutRSgn σ i j v)
          (edgeLab (bnd_splitR i j F)
            (fun q => if q.val = j.val - i.val then cIn ⟨(i, j), hdF⟩ else y (bnd_vR i j q))
            (fun e => cIn (bnd_ιR i j F e)) (fun e => cOut (bnd_ιR i j F e)) v p.2 true)
          (edgeLab (bnd_splitR i j F)
            (fun q => if q.val = j.val - i.val then cIn ⟨(i, j), hdF⟩ else y (bnd_vR i j q))
            (fun e => cIn (bnd_ιR i j F e)) (fun e => cOut (bnd_ιR i j F e)) v p.1 false)) := by
  rw [bnd_prod_corners, bnd_prod_corners, bnd_prod_corners,
    bnd_prod_cornerP_split hd hF hdF]
  congr 1
  · refine Finset.prod_congr rfl fun x hx => ?_
    simp only [bnd_cornerP, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨n1, n2, c1, c2⟩ := bnd_corner_conds hx
    rw [bnd_cutLSgn_eq, bnd_edgeLab_L hd hdF y cIn cOut n2 true (by simpa using c2),
      bnd_edgeLab_L hd hdF y cIn cOut n1 false (by simpa using c1)]
  · refine Finset.prod_congr rfl fun x hx => ?_
    simp only [bnd_cornerP, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨n1, n2, c1, c2⟩ := bnd_corner_conds hx
    rw [bnd_cutRSgn_eq, bnd_edgeLab_R hd hdF y cIn cOut n2 true (by simpa using c2),
      bnd_edgeLab_R hd hdF y cIn cOut n1 false (by simpa using c1)]

end Corners

/-! ## The core of a dissection with one link replaced -/

section Glue

variable {k L : ℕ}

private lemma bnd_sum_pair {T Y : Type*} [Fintype T] [DecidableEq T] [Fintype Y]
    (G : (T → Y) → (T → Y) → ℂ) :
    ∑ cIn : T → Y, ∑ cOut : T → Y, G cIn cOut =
      ∑ c : T → Y × Y, G (fun t => (c t).1) (fun t => (c t).2) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow T (fun _ => Y) (fun _ => Y)) _ _
    (fun c => rfl)).symm

private lemma bnd_sum_option {A B T X : Type} [Fintype A] [Fintype B] [Fintype T]
    [DecidableEq A] [DecidableEq B] [DecidableEq T] [Fintype X] (e : Option (A ⊕ B) ≃ T)
    (G : (T → X) → ℂ) :
    ∑ c : T → X, G c = ∑ x : X, ∑ f : A → X, ∑ g : B → X,
      G (fun t => Option.elim (e.symm t) x (Sum.elim f g)) := by
  let E : X × ((A → X) × (B → X)) ≃ (T → X) :=
    ((Equiv.prodCongr (Equiv.refl X) (Equiv.sumArrowEquivProdArrow A B X).symm).trans
      (Equiv.piOptionEquivProd (α := A ⊕ B) (β := fun _ => X)).symm).trans
      (Equiv.arrowCongr e (Equiv.refl X))
  rw [← E.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun g _ => ?_
  congr 1
  funext t
  simp only [E, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.prodCongr_apply,
    Equiv.coe_refl, Prod.map, id, Function.comp_apply, Equiv.refl_apply]
  cases e.symm t with
  | none => rfl
  | some a => cases a <;> rfl

/-- The diagonals of `F`: `(i, j)` and those of the two polygons of the cut. -/
private def bnd_eqvFun (i j : Fin k) (F : Finset (Fin k × Fin k)) (hdF : (i, j) ∈ F) :
    Option (↥(bnd_splitL i j F) ⊕ ↥(bnd_splitR i j F)) → ↥F
  | none => ⟨(i, j), hdF⟩
  | some (Sum.inl a) => bnd_ιL i j F a
  | some (Sum.inr b) => bnd_ιR i j F b

private lemma bnd_eqvFun_bij {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F) :
    Function.Bijective (bnd_eqvFun i j F hdF) := by
  have hdv := (bnd_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  have hFL := bnd_splitL_mem hd hF
  have hFR := bnd_splitR_mem hd hF
  rw [bnd_mem_dissections] at hFL hFR
  have hj := j.isLt
  constructor
  · intro o o' h
    rcases o with _ | a | b <;> rcases o' with _ | a' | b'
    · rfl
    · exfalso
      have := ((bnd_mem_splitL _).mp a'.2).2
      exact this (congrArg Subtype.val h).symm
    · exfalso
      have := ((bnd_mem_splitR _).mp b'.2).2
      exact this (congrArg Subtype.val h).symm
    · exfalso
      have := ((bnd_mem_splitL _).mp a.2).2
      exact this (congrArg Subtype.val h)
    · have h1 := congrArg Subtype.val h
      simp only [bnd_eqvFun, bnd_ιL, Prod.mk.injEq] at h1
      have e1 := bnd_vL_inj hij h1.1
      have e2 := bnd_vL_inj hij h1.2
      rw [Subtype.ext (Prod.ext e1 e2)]
    · exfalso
      have h1 := congrArg Subtype.val h
      simp only [bnd_eqvFun, bnd_ιL, bnd_ιR, Prod.mk.injEq] at h1
      have ha := (bnd_mem_polyDiags _).mp (hFL.1 a.2)
      have f1 := congrArg Fin.val h1.1
      have f2 := congrArg Fin.val h1.2
      have ca1 := bnd_vL_cases i j a.1.1
      have ca2 := bnd_vL_cases i j a.1.2
      have hne := bnd_prod_ne ((bnd_mem_splitL _).mp a.2).2
      simp only [bnd_vR_val] at f1 f2
      simp only at hne
      have := a.1.1.isLt; have := a.1.2.isLt; have := b'.1.1.isLt; have := b'.1.2.isLt
      omega
    · exfalso
      have := ((bnd_mem_splitR _).mp b.2).2
      exact this (congrArg Subtype.val h)
    · exfalso
      have h1 := congrArg Subtype.val h
      simp only [bnd_eqvFun, bnd_ιL, bnd_ιR, Prod.mk.injEq] at h1
      have ha := (bnd_mem_polyDiags _).mp (hFL.1 a'.2)
      have f1 := congrArg Fin.val h1.1
      have f2 := congrArg Fin.val h1.2
      have ca1 := bnd_vL_cases i j a'.1.1
      have ca2 := bnd_vL_cases i j a'.1.2
      have hne := bnd_prod_ne ((bnd_mem_splitL _).mp a'.2).2
      simp only [bnd_vR_val] at f1 f2
      simp only at hne
      have := a'.1.1.isLt; have := a'.1.2.isLt; have := b.1.1.isLt; have := b.1.2.isLt
      omega
    · have h1 := congrArg Subtype.val h
      simp only [bnd_eqvFun, bnd_ιR, Prod.mk.injEq] at h1
      have e1 := bnd_vR_inj h1.1
      have e2 := bnd_vR_inj h1.2
      rw [Subtype.ext (Prod.ext e1 e2)]
  · intro e
    by_cases he : e.1 = (i, j)
    · exact ⟨none, Subtype.ext he.symm⟩
    rcases bnd_cover hF hdF e.2 he with h | h
    · refine ⟨some (Sum.inl ⟨(bnd_uL i j e.1.1, bnd_uL i j e.1.2), ?_⟩), ?_⟩
      · rw [bnd_mem_splitL]
        simp only [bnd_vL_uL h.1, bnd_vL_uL h.2]
        exact ⟨e.2, he⟩
      · apply Subtype.ext
        simp only [bnd_eqvFun, bnd_ιL, bnd_vL_uL h.1, bnd_vL_uL h.2]
    · refine ⟨some (Sum.inr ⟨(bnd_uR i j e.1.1, bnd_uR i j e.1.2), ?_⟩), ?_⟩
      · rw [bnd_mem_splitR]
        simp only [bnd_vR_uR h.1, bnd_vR_uR h.2]
        exact ⟨e.2, he⟩
      · apply Subtype.ext
        simp only [bnd_eqvFun, bnd_ιR, bnd_vR_uR h.1, bnd_vR_uR h.2]

/-- The core of `F` in which the link of the diagonal `d` is replaced by the matrix `X`. -/
private def bnd_coreD (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) (σ : Fin k → Bool)
    (F : Finset (Fin k × Fin k)) (d : Fin k × Fin k) (X : Matrix (Fin L) (Fin L) ℂ)
    (y : Fin k → Fin L) : ℂ :=
  ∑ cIn : ↥F → Fin L, ∑ cOut : ↥F → Fin L,
    (∏ e : ↥F, if e.1 = d then X (cOut e) (cIn e)
      else ((β * t : ℝ) : ℂ) * pairV β M t (σ e.1.1) (σ e.1.2) (cOut e) (cIn e)) *
      ∏ v : Fin k, ∏ p ∈ polyCorners F v,
        sgnMat M (σ v) (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false)

/-- The link `X` of `(i, j)` glues the cores of the two polygons of the cut. -/
private lemma bnd_coreD_split {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {t : ℝ}
    {σ : Fin k → Bool} {i j : Fin k} (hd : (i, j) ∈ polyDiags k) {F : Finset (Fin k × Fin k)}
    (hF : F ∈ dissections k) (hdF : (i, j) ∈ F) (X : Matrix (Fin L) (Fin L) ℂ)
    (y : Fin k → Fin L) :
    bnd_coreD β M t σ F (i, j) X y =
      ∑ xo : Fin L, ∑ xi : Fin L, X xo xi *
          dissCore β M t (cutLSgn σ i j) (bnd_splitL i j F)
            (fun p => if p.val = i.val then xo else y (bnd_vL i j p)) *
          dissCore β M t (cutRSgn σ i j) (bnd_splitR i j F)
            (fun q => if q.val = j.val - i.val then xi else y (bnd_vR i j q)) := by
  set e := Equiv.ofBijective _ (bnd_eqvFun_bij hd hF hdF) with he_def
  have he0 : e none = ⟨(i, j), hdF⟩ := rfl
  have heL : ∀ a, e (some (Sum.inl a)) = bnd_ιL i j F a := fun a => rfl
  have heR : ∀ b, e (some (Sum.inr b)) = bnd_ιR i j F b := fun b => rfl
  have hs0 : e.symm ⟨(i, j), hdF⟩ = none := by rw [← he0, Equiv.symm_apply_apply]
  have hsL : ∀ a, e.symm (bnd_ιL i j F a) = some (Sum.inl a) := fun a => by
    rw [← heL, Equiv.symm_apply_apply]
  have hsR : ∀ b, e.symm (bnd_ιR i j F b) = some (Sum.inr b) := fun b => by
    rw [← heR, Equiv.symm_apply_apply]
  have hL : ∀ a : ↥(bnd_splitL i j F), ¬(bnd_ιL i j F a).1 = (i, j) :=
    fun a => ((bnd_mem_splitL _).mp a.2).2
  have hR : ∀ b : ↥(bnd_splitR i j F), ¬(bnd_ιR i j F b).1 = (i, j) :=
    fun b => ((bnd_mem_splitR _).mp b.2).2
  unfold bnd_coreD
  rw [bnd_sum_pair, bnd_sum_option e, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun xo _ => Finset.sum_congr rfl fun xi _ => ?_
  unfold dissCore
  rw [bnd_sum_pair, bnd_sum_pair, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [bnd_corners_split hd hF hdF M σ y]
  rw [← e.prod_comp, Fintype.prod_option, Fintype.prod_sum_type]
  simp only [he0, heL, heR, hs0, hsL, hsR, Option.elim, Sum.elim_inl,
    Sum.elim_inr, ite_true, hL, hR, ite_false]
  have hvL : ∀ a : ↥(bnd_splitL i j F),
      (bnd_ιL i j F a).1 = (bnd_vL i j a.1.1, bnd_vL i j a.1.2) := fun a => rfl
  have hvR : ∀ b : ↥(bnd_splitR i j F),
      (bnd_ιR i j F b).1 = (bnd_vR i j b.1.1, bnd_vR i j b.1.2) := fun b => rfl
  simp only [hvL, hvR, bnd_cutLSgn_eq, bnd_cutRSgn_eq]
  ring

end Glue

/-! ## The external labels of the two polygons of a cut -/

section Sides

variable {k L : ℕ}

/-- The side `i` of the polygon of Cut_L. -/
private def bnd_iL (i j : Fin k) : Fin (k + i - j + 1) := ⟨i.val, by have := j.isLt; omega⟩

/-- The last side of the polygon of Cut_R. -/
private def bnd_lastR (i j : Fin k) : Fin (j - i + 1) := ⟨j.val - i.val, by omega⟩

private lemma bnd_vL_rot {i j : Fin k} (hd : (i, j) ∈ polyDiags k) {p : Fin (k + i - j + 1)}
    (hp : p.val ≠ i.val) : bnd_vL i j (finRotate _ p) = finRotate k (bnd_vL i j p) := by
  have hdv := (bnd_mem_polyDiags _).mp hd
  simp only at hdv
  have := p.isLt; have := j.isLt
  apply Fin.ext
  rw [bnd_finRotate_val, bnd_vL_val, bnd_vL_val, bnd_finRotate_val]
  split_ifs <;> omega

private lemma bnd_vL_rot_iL {i j : Fin k} (hd : (i, j) ∈ polyDiags k) :
    bnd_vL i j (finRotate _ (bnd_iL i j)) = j := by
  have hdv := (bnd_mem_polyDiags _).mp hd
  simp only at hdv
  have := j.isLt
  have hr : (finRotate _ (bnd_iL i j)).val = i.val + 1 := by
    have h1 := bnd_finRotate_val (bnd_iL i j)
    have h0 : (bnd_iL i j).val = i.val := rfl
    split_ifs at h1 <;> omega
  have h2 := bnd_vL_cases i j (finRotate _ (bnd_iL i j))
  apply Fin.ext
  omega

private lemma bnd_vR_rot {i j : Fin k} (hd : (i, j) ∈ polyDiags k) {q : Fin (j - i + 1)}
    (hq : q.val ≠ j.val - i.val) : bnd_vR i j (finRotate _ q) = finRotate k (bnd_vR i j q) := by
  have hdv := (bnd_mem_polyDiags _).mp hd
  simp only at hdv
  have := q.isLt; have := j.isLt
  apply Fin.ext
  rw [bnd_finRotate_val, bnd_vR_val, bnd_vR_val, bnd_finRotate_val]
  split_ifs <;> omega

private lemma bnd_vR_rot_lastR {i j : Fin k} (hd : (i, j) ∈ polyDiags k) :
    bnd_vR i j (finRotate _ (bnd_lastR i j)) = i := by
  have hdv := (bnd_mem_polyDiags _).mp hd
  simp only at hdv
  apply Fin.ext
  rw [bnd_vR_val, bnd_finRotate_val]
  simp only [bnd_lastR]
  split_ifs <;> omega

/-- The sides of the `k`-gon are the sides of the two polygons other than the side `(i, j)`. -/
private lemma bnd_prod_sides {i j : Fin k} (hd : (i, j) ∈ polyDiags k) {R : Type*} [CommMonoid R]
    (h : Fin k → R) :
    ∏ s, h s = (∏ p ∈ Finset.univ.erase (bnd_iL i j), h (bnd_vL i j p)) *
      ∏ q ∈ Finset.univ.erase (bnd_lastR i j), h (bnd_vR i j q) := by
  have hdv := (bnd_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  have hj := j.isLt
  have hU : (Finset.univ : Finset (Fin k)) =
      (Finset.univ.erase (bnd_iL i j)).image (bnd_vL i j) ∪
        (Finset.univ.erase (bnd_lastR i j)).image (bnd_vR i j) := by
    ext s
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_image, Finset.mem_erase, ne_eq,
      and_true, true_iff]
    by_cases hs : s.val < i.val ∨ j.val ≤ s.val
    · left
      refine ⟨bnd_uL i j s, fun h => ?_, bnd_vL_uL (by omega)⟩
      have := congrArg Fin.val h
      simp only [bnd_uL_val, bnd_iL] at this
      split_ifs at this <;> omega
    · right
      refine ⟨bnd_uR i j s, fun h => ?_, bnd_vR_uR (by omega)⟩
      have := congrArg Fin.val h
      simp only [bnd_uR_val, bnd_lastR] at this
      split_ifs at this <;> omega
  have hdisj : Disjoint ((Finset.univ.erase (bnd_iL i j)).image (bnd_vL i j))
      ((Finset.univ.erase (bnd_lastR i j)).image (bnd_vR i j)) := by
    rw [Finset.disjoint_left]
    intro s h1 h2
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true] at h1 h2
    obtain ⟨p, hp, rfl⟩ := h1
    obtain ⟨q, hq, hpq⟩ := h2
    have e := congrArg Fin.val hpq
    have hp' : p.val ≠ i.val := fun h => hp (Fin.ext h)
    have hq' : q.val ≠ j.val - i.val := fun h => hq (Fin.ext h)
    have := p.isLt; have := q.isLt
    have cp := bnd_vL_cases i j p
    rw [bnd_vR_val] at e
    omega
  rw [hU, Finset.prod_union hdisj,
    Finset.prod_image (fun p _ q _ h => bnd_vL_inj hij h),
    Finset.prod_image (fun p _ q _ h => bnd_vR_inj h)]

/-- The external pre-labels of `F` and the two copies of the label of `(i, j)` are the external
pre-labels of the two polygons of the cut. -/
private lemma bnd_sum_labels {i j : Fin k} (hd : (i, j) ∈ polyDiags k) {R : Type*}
    [AddCommMonoid R] (G : (Fin (k + i - j + 1) → Fin L) → (Fin (j - i + 1) → Fin L) → R) :
    ∑ zL : Fin (k + i - j + 1) → Fin L, ∑ zR : Fin (j - i + 1) → Fin L, G zL zR =
      ∑ y : Fin k → Fin L, ∑ xo : Fin L, ∑ xi : Fin L,
        G (fun p => if p.val = i.val then xo else y (bnd_vL i j p))
          (fun q => if q.val = j.val - i.val then xi else y (bnd_vR i j q)) := by
  have hdv := (bnd_mem_polyDiags _).mp hd
  simp only at hdv
  have hij : i.val < j.val := by omega
  have hj := j.isLt
  let E : (Fin k → Fin L) × (Fin L × Fin L) ≃
      (Fin (k + i - j + 1) → Fin L) × (Fin (j - i + 1) → Fin L) :=
    { toFun := fun x => (fun p => if p.val = i.val then x.2.1 else x.1 (bnd_vL i j p),
        fun q => if q.val = j.val - i.val then x.2.2 else x.1 (bnd_vR i j q))
      invFun := fun z => (fun s => if s.val < i.val ∨ j.val ≤ s.val then z.1 (bnd_uL i j s)
          else z.2 (bnd_uR i j s), (z.1 (bnd_iL i j), z.2 (bnd_lastR i j)))
      left_inv := by
        rintro ⟨y, xo, xi⟩
        simp only [bnd_iL, bnd_lastR, ite_true, Prod.mk.injEq, and_true]
        funext s
        by_cases hs : s.val < i.val ∨ j.val ≤ s.val
        · rw [ite_eq_left hs]
          have : (bnd_uL i j s).val ≠ i.val := by
            rw [bnd_uL_val]; split_ifs <;> omega
          rw [ite_eq_right this, bnd_vL_uL (by omega)]
        · rw [ite_eq_right hs]
          have : (bnd_uR i j s).val ≠ j.val - i.val := by
            rw [bnd_uR_val]; split_ifs <;> omega
          rw [ite_eq_right this, bnd_vR_uR (by omega)]
      right_inv := by
        rintro ⟨zL, zR⟩
        simp only [Prod.mk.injEq]
        constructor
        · funext p
          by_cases hp : p.val = i.val
          · rw [ite_eq_left hp]
            congr 1
            exact Fin.ext hp.symm
          · rw [ite_eq_right hp]
            have cp := bnd_vL_cases i j p
            have hs : (bnd_vL i j p).val < i.val ∨ j.val ≤ (bnd_vL i j p).val := by omega
            rw [ite_eq_left hs, bnd_uL_vL hij]
        · funext q
          by_cases hq : q.val = j.val - i.val
          · rw [ite_eq_left hq]
            congr 1
            exact Fin.ext hq.symm
          · rw [ite_eq_right hq]
            have := q.isLt
            have hs : ¬((bnd_vR i j q).val < i.val ∨ j.val ≤ (bnd_vR i j q).val) := by
              rw [bnd_vR_val]; omega
            rw [ite_eq_right hs, bnd_uR_vR] }
  rw [← Fintype.sum_prod_type', ← E.sum_comp, Fintype.sum_prod_type, Fintype.sum_congr]
  intro y
  rw [Fintype.sum_prod_type]
  rfl

end Sides

/-! ## Circulant kernels and their multipliers

`M_B` of (5.3) [fo:eq:characteristic] is circulant, hence so are `P` and the mixed inverse
`V = (I - tP)⁻¹` of Appendix B.2 [sec:bl-primitives]; the multiplier of `V` at the grid
momentum `q` has modulus at most `(1 - t P̂(q))⁻¹`, with the symbol `P̂ = kerSymbol P` of (A.25)
[ba:eq:coercivity]. -/

section Circulant

variable {L : ℕ}

/-- `cycleAdj L` is the adjacency of `a ↦ a + 1` on `Fin L`. -/
private lemma bnd_cycleAdj_eq [NeZero L] (a b : Fin L) :
    cycleAdj L a b = (if b = a + 1 then 1 else 0) + (if a = b + 1 then 1 else 0) := by
  have h1 : ∀ x : Fin L, (x + 1).val = (x.val + 1) % L := by
    intro x
    rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  simp only [cycleAdj, Matrix.of_apply, Fin.ext_iff, h1]

/-- The cycle adjacency is invariant under translations. -/
private lemma bnd_cycleAdj_add [NeZero L] (c a b : Fin L) :
    cycleAdj L (a + c) (b + c) = cycleAdj L a b := by
  have h1 : ∀ x y : Fin L, (y + c = x + c + 1) ↔ (y = x + 1) := by
    intro x y
    rw [add_right_comm x c 1, add_left_inj]
  rw [bnd_cycleAdj_eq, bnd_cycleAdj_eq]
  simp only [h1]

/-- `M_B` is circulant. -/
private lemma bnd_dysonMat_add [NeZero L] (b β : ℝ) (z m : ℂ) (a a' c : Fin L) :
    dysonMat b β L z m (a + c) (a' + c) = dysonMat b β L z m a a' := by
  have h : (dysonMat b β L z m).submatrix (Equiv.addRight c) (Equiv.addRight c) =
      dysonMat b β L z m := by
    unfold dysonMat
    rw [← Matrix.inv_submatrix_equiv]
    congr 1
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Equiv.coe_addRight, bnd_cycleAdj_add, add_left_inj]
  exact congrFun (congrFun h a) a'

/-- `P` is circulant when `M` is. -/
private lemma bnd_pairP_add [NeZero L] {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ}
    (hM : ∀ a a' c : Fin L, M (a + c) (a' + c) = M a a') (a a' c : Fin L) :
    pairP β M (a + c) (a' + c) = pairP β M a a' := by
  simp only [pairP, Matrix.of_apply, hM]

/-- `(I - tP)⁻¹` is circulant when `P` is. -/
private lemma bnd_inv_add [NeZero L] {P : Matrix (Fin L) (Fin L) ℝ}
    (hP : ∀ a a' c : Fin L, P (a + c) (a' + c) = P a a') (t : ℝ) (a a' c : Fin L) :
    (1 - t • P)⁻¹ (a + c) (a' + c) = (1 - t • P)⁻¹ a a' := by
  have h1 : (1 - t • P).submatrix (Equiv.addRight c) (Equiv.addRight c) = 1 - t • P := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Equiv.coe_addRight, hP, add_left_inj]
  have h2 : ((1 - t • P)⁻¹).submatrix (Equiv.addRight c) (Equiv.addRight c) = (1 - t • P)⁻¹ := by
    rw [← Matrix.inv_submatrix_equiv, h1]
  exact congrFun (congrFun h2 a) a'

/-- The mixed one-label inverse is the real matrix `(I - tP)⁻¹`. -/
private lemma bnd_pairV_mixed (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) {s s' : Bool}
    (h : s ≠ s') : pairV β M t s s' = ((1 - t • pairP β M)⁻¹).map ((↑) : ℝ → ℂ) := by
  unfold pairV
  rw [ite_eq_right_iff.mpr (fun h' => absurd h' h)]

/-- `I - tP` is invertible for `0 ≤ t < 1` when `P ≥ 0` has unit row sums. -/
private lemma bnd_inv_mul {P : Matrix (Fin L) (Fin L) ℝ} (hP0 : ∀ a b, 0 ≤ P a b)
    (hrow : ∀ a, ∑ b, P a b = 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (1 - t • P) * (1 - t • P)⁻¹ = 1 := by
  apply Matrix.mul_nonsing_inv
  rw [isUnit_iff_ne_zero]
  apply det_ne_zero_of_sum_row_lt_diag
  intro a
  have hPaa : P a a ≤ 1 := by
    rw [← hrow a]
    exact Finset.single_le_sum (fun b _ => hP0 a b) (Finset.mem_univ a)
  have hoff : ∀ b ∈ Finset.univ.erase a, ‖(1 - t • P) a b‖ = t * P a b := by
    intro b hb
    rw [Matrix.sub_apply, Matrix.one_apply_ne' (Finset.ne_of_mem_erase hb), Matrix.smul_apply,
      smul_eq_mul, zero_sub, norm_neg, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht0 (hP0 a b))]
  rw [Finset.sum_congr rfl hoff, ← Finset.mul_sum]
  have hs : ∑ b ∈ Finset.univ.erase a, P a b = 1 - P a a := by
    rw [← hrow a, ← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
    ring
  rw [hs, Matrix.sub_apply, Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul,
    Real.norm_eq_abs, abs_of_pos (by nlinarith)]
  nlinarith

/-- A circulant matrix acts on a character by its multiplier. -/
private lemma bnd_circ_chi [NeZero L] (X : Matrix (Fin L) (Fin L) ℂ)
    (hX : ∀ a a' c : Fin L, X (a + c) (a' + c) = X a a') (q a : Fin L) :
    ∑ x, X a x * bnd_chi L q x = bnd_chi L q a * ∑ u, X 0 u * bnd_chi L q u := by
  rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.addRight a) (fun x => X a x * bnd_chi L q x)]
  refine Finset.sum_congr rfl fun u _ => ?_
  have h := hX 0 u a
  rw [zero_add] at h
  simp only [Equiv.coe_addRight, h, bnd_chi_add]
  ring

/-- The real part of the multiplier of a circulant `P` is `kerSymbol P`. -/
private lemma bnd_re_symbol [NeZero L] {P : Matrix (Fin L) (Fin L) ℝ}
    (hP : ∀ a a' c : Fin L, P (a + c) (a' + c) = P a a') (q : Fin L) :
    (∑ u, (P 0 u : ℂ) * bnd_chi L q u).re = kerSymbol P q := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hre : ∀ u : Fin L, ((P 0 u : ℂ) * bnd_chi L q u).re =
      P 0 u * Real.cos (2 * π * ((q : ℕ) : ℝ) * ((u : ℕ) : ℝ) / L) := by
    intro u
    rw [Complex.re_ofReal_mul]
    congr 1
    have hc : bnd_chi L q u =
        Complex.exp (((-(2 * π * ((q : ℕ) : ℝ) * ((u : ℕ) : ℝ) / L)) : ℝ) * I) := by
      unfold bnd_chi
      congr 1
      push_cast
      ring
    rw [hc, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  have hrow : ∀ a : Fin L, ∑ x, P a x * Real.cos (2 * π * ((q : ℕ) : ℝ) *
      (((x : ℕ) : ℝ) - ((a : ℕ) : ℝ)) / L) =
      ∑ u, P 0 u * Real.cos (2 * π * ((q : ℕ) : ℝ) * ((u : ℕ) : ℝ) / L) := by
    intro a
    rw [← Equiv.sum_comp (Equiv.addRight a)]
    refine Finset.sum_congr rfl fun u _ => ?_
    have h := hP 0 u a
    rw [zero_add] at h
    simp only [Equiv.coe_addRight, h]
    congr 1
    have hv := Fin.val_add u a
    have hu := u.isLt
    have ha := a.isLt
    rcases Nat.lt_or_ge ((u : ℕ) + (a : ℕ)) L with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hv
      rw [hv]
      push_cast
      ring_nf
    · have : ((u : ℕ) + (a : ℕ)) % L = (u : ℕ) + (a : ℕ) - L := by
        rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
      rw [this] at hv
      rw [hv, Nat.cast_sub hge, Nat.cast_add]
      have e : 2 * π * ((q : ℕ) : ℝ) * (((u : ℕ) : ℝ) + ((a : ℕ) : ℝ) - (L : ℝ) -
          ((a : ℕ) : ℝ)) / L = 2 * π * ((q : ℕ) : ℝ) * ((u : ℕ) : ℝ) / L +
            ((-((q : ℕ) : ℤ) : ℤ) : ℝ) * (2 * π) := by
        push_cast
        field_simp
        ring
      rw [e, Real.cos_add_int_mul_two_pi]
  unfold kerSymbol
  rw [Complex.re_sum]
  simp only [hre, hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- `|kerSymbol P| ≤ 1` for `P ≥ 0` with unit row sums. -/
private lemma bnd_symbol_abs_le [NeZero L] {P : Matrix (Fin L) (Fin L) ℝ}
    (hP0 : ∀ a b, 0 ≤ P a b) (hrow : ∀ a, ∑ b, P a b = 1) (q : Fin L) :
    |kerSymbol P q| ≤ 1 := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  unfold kerSymbol
  rw [abs_mul, abs_inv, abs_of_pos hL]
  rw [inv_mul_le_iff₀ hL, mul_one]
  calc |∑ a : Fin L, ∑ x : Fin L, P a x * Real.cos (2 * π * ((q : ℕ) : ℝ) *
        (((x : ℕ) : ℝ) - ((a : ℕ) : ℝ)) / L)|
      ≤ ∑ a : Fin L, ∑ x : Fin L, P a x := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
        rw [abs_mul, abs_of_nonneg (hP0 a x)]
        exact mul_le_of_le_one_right (hP0 a x) (Real.abs_cos_le_one _)
    _ = L := by simp [hrow]

/-- The multiplier of the mixed inverse: `|V̂(q)| ≤ (1 - t kerSymbol P q)⁻¹`. -/
private lemma bnd_mult_le [NeZero L] {P : Matrix (Fin L) (Fin L) ℝ}
    (hP : ∀ a a' c : Fin L, P (a + c) (a' + c) = P a a') (hP0 : ∀ a b, 0 ≤ P a b)
    (hrow : ∀ a, ∑ b, P a b = 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (q : Fin L) :
    ‖∑ u, (((1 - t • P)⁻¹ 0 u : ℝ) : ℂ) * bnd_chi L q u‖ ≤ (1 - t * kerSymbol P q)⁻¹ := by
  set V := (1 - t • P)⁻¹ with hV
  have hVc : ∀ a a' c : Fin L, ((V.map ((↑) : ℝ → ℂ)) (a + c) (a' + c)) =
      (V.map ((↑) : ℝ → ℂ)) a a' := by
    intro a a' c
    simp only [Matrix.map_apply, hV, bnd_inv_add hP]
  set v := ∑ u, ((V 0 u : ℝ) : ℂ) * bnd_chi L q u with hv
  set p := ∑ u, ((P 0 u : ℝ) : ℂ) * bnd_chi L q u with hp
  have hmul := bnd_inv_mul hP0 hrow ht0 ht1
  have key : (1 - (t : ℂ) * p) * v = 1 := by
    have h0 : ∀ x : Fin L, ∑ z, ((1 - t • P) 0 z : ℂ) * (V z x : ℂ) =
        if x = 0 then 1 else 0 := by
      intro x
      have := congrFun (congrFun hmul 0) x
      rw [Matrix.mul_apply] at this
      have h2 : ((∑ z, (1 - t • P) 0 z * V z x : ℝ) : ℂ) =
          ((1 : Matrix (Fin L) (Fin L) ℝ) 0 x : ℂ) := by
        rw [this]
      push_cast at h2
      rw [h2, Matrix.one_apply]
      split_ifs with h1 h2' h2' <;>
        first | rfl | (exfalso; exact h2' h1.symm) | (exfalso; exact h1 h2'.symm)
    have h1 : ∑ x, (∑ z, ((1 - t • P) 0 z : ℂ) * (V z x : ℂ)) * bnd_chi L q x = 1 := by
      simp only [h0, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
        bnd_chi_zero_right]
    have hA : ∑ z, ((1 - t • P) 0 z : ℂ) * bnd_chi L q z = 1 - (t : ℂ) * p := by
      have h4 : ∀ z, ((1 - t • P) 0 z : ℂ) * bnd_chi L q z =
          (if (0 : Fin L) = z then bnd_chi L q z else 0) -
            (t : ℂ) * ((P 0 z : ℂ) * bnd_chi L q z) := by
        intro z
        rw [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
        split_ifs <;> push_cast <;> ring
      simp only [h4, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
        bnd_chi_zero_right, ← Finset.mul_sum, hp]
    have hcirc : ∀ z, ∑ x, (V z x : ℂ) * bnd_chi L q x = bnd_chi L q z * v := by
      intro z
      have := bnd_circ_chi (V.map ((↑) : ℝ → ℂ)) hVc q z
      simpa only [Matrix.map_apply] using this
    calc (1 - (t : ℂ) * p) * v = (∑ z, ((1 - t • P) 0 z : ℂ) * bnd_chi L q z) * v := by rw [hA]
      _ = ∑ z, ((1 - t • P) 0 z : ℂ) * ∑ x, (V z x : ℂ) * bnd_chi L q x := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [hcirc z]
          ring
      _ = ∑ x, (∑ z, ((1 - t • P) 0 z : ℂ) * (V z x : ℂ)) * bnd_chi L q x := by
          simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
          exact Finset.sum_comm
      _ = 1 := h1
  have hre : (1 - (t : ℂ) * p).re = 1 - t * kerSymbol P q := by
    rw [Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul, hp, bnd_re_symbol hP]
  have hpos : 0 < 1 - t * kerSymbol P q := by
    have := bnd_symbol_abs_le hP0 hrow q
    have h1 : kerSymbol P q ≤ 1 := (abs_le.mp this).2
    nlinarith
  have hnorm : 1 - t * kerSymbol P q ≤ ‖1 - (t : ℂ) * p‖ := by
    rw [← hre]
    exact Complex.re_le_norm _
  have hv : ‖v‖ = ‖1 - (t : ℂ) * p‖⁻¹ := by
    have h := congrArg norm key
    rw [norm_mul, norm_one] at h
    have hn : ‖1 - (t : ℂ) * p‖ ≠ 0 := by
      intro h0; rw [h0, zero_mul] at h; exact zero_ne_one h
    field_simp
    linarith
  rw [hv]
  exact inv_anti₀ hpos hnorm

end Circulant

/-! ## The transform of a glued tensor

Gluing two tensors along the diagonal `(i, j)` with a circulant link `X`: the transform of the
glued tensor is the momentum sum of the product of the transforms, with opposite momenta on the
two copies of the cut label (Appendix B.2 [sec:bl-primitives], after (B.1) [ba:eq:dissection]).
-/

section GlueFourier

variable {k L : ℕ}

/-- The labels of the polygon of Cut_L with the cut label `x`. -/
private def bnd_yL (i j : Fin k) (y : Fin k → Fin L) (x : Fin L) : Fin (k + i - j + 1) → Fin L :=
  fun p => if p.val = i.val then x else y (bnd_vL i j p)

/-- The labels of the polygon of Cut_R with the cut label `x`. -/
private def bnd_yR (i j : Fin k) (y : Fin k → Fin L) (x : Fin L) : Fin (j - i + 1) → Fin L :=
  fun q => if q.val = j.val - i.val then x else y (bnd_vR i j q)

/-- The tensor glued from `A` and `B` along `(i, j)` with the link `X`. -/
def bnd_glueT (i j : Fin k) (X : Matrix (Fin L) (Fin L) ℂ)
    (A : (Fin (k + i - j + 1) → Fin L) → ℂ) (B : (Fin (j - i + 1) → Fin L) → ℂ)
    (y : Fin k → Fin L) : ℂ :=
  ∑ xo : Fin L, ∑ xi : Fin L, X xo xi * A (bnd_yL i j y xo) * B (bnd_yR i j y xi)

/-- The multiplier `X̂(q) = Σ_u X_{0u} e^{-2πiqu/L}`. -/
private def bnd_hat [NeZero L] (X : Matrix (Fin L) (Fin L) ℂ) (q : Fin L) : ℂ :=
  ∑ u, X 0 u * bnd_chi L q u

/-- `bnd_sum_labels` in terms of the label maps of the two polygons. -/
private lemma bnd_sum_labels' {i j : Fin k} (hd : (i, j) ∈ polyDiags k) {R : Type*}
    [AddCommMonoid R] (G : (Fin (k + i - j + 1) → Fin L) → (Fin (j - i + 1) → Fin L) → R) :
    ∑ zL : Fin (k + i - j + 1) → Fin L, ∑ zR : Fin (j - i + 1) → Fin L, G zL zR =
      ∑ y : Fin k → Fin L, ∑ xo : Fin L, ∑ xi : Fin L, G (bnd_yL i j y xo) (bnd_yR i j y xi) :=
  bnd_sum_labels hd G

private lemma bnd_yL_iL (i j : Fin k) (y : Fin k → Fin L) (x : Fin L) :
    bnd_yL i j y x (bnd_iL i j) = x := by
  simp [bnd_yL, bnd_iL]

private lemma bnd_yL_ne {i j : Fin k} (y : Fin k → Fin L) (x : Fin L) {p : Fin (k + i - j + 1)}
    (hp : p ≠ bnd_iL i j) : bnd_yL i j y x p = y (bnd_vL i j p) := by
  have : p.val ≠ i.val := fun h => hp (Fin.ext h)
  simp [bnd_yL, this]

private lemma bnd_yR_lastR (i j : Fin k) (y : Fin k → Fin L) (x : Fin L) :
    bnd_yR i j y x (bnd_lastR i j) = x := by
  simp [bnd_yR, bnd_lastR]

private lemma bnd_yR_ne {i j : Fin k} (y : Fin k → Fin L) (x : Fin L) {q : Fin (j - i + 1)}
    (hq : q ≠ bnd_lastR i j) : bnd_yR i j y x q = y (bnd_vR i j q) := by
  have : q.val ≠ j.val - i.val := fun h => hq (Fin.ext h)
  simp [bnd_yR, this]

/-- The vertices of the two polygons other than the cut side are distinct. -/
private lemma bnd_vL_ne_vR {i j : Fin k} (hd : (i, j) ∈ polyDiags k) {p : Fin (k + i - j + 1)}
    (hp : p ≠ bnd_iL i j) {q : Fin (j - i + 1)} (hq : q ≠ bnd_lastR i j) :
    bnd_vL i j p ≠ bnd_vR i j q := by
  have hdv := (bnd_mem_polyDiags _).mp hd
  simp only at hdv
  intro e
  have e' := congrArg Fin.val e
  have hp' : p.val ≠ i.val := fun h => hp (Fin.ext h)
  have hq' : q.val ≠ j.val - i.val := fun h => hq (Fin.ext h)
  have := p.isLt; have := q.isLt
  have cp := bnd_vL_cases i j p
  rw [bnd_vR_val] at e'
  omega

/-- Every side of the `k`-gon is a side of one of the two polygons of the cut. -/
private lemma bnd_side_cases {i j : Fin k} (hd : (i, j) ∈ polyDiags k) (s : Fin k) :
    (∃ p, p ≠ bnd_iL i j ∧ bnd_vL i j p = s) ∨ (∃ q, q ≠ bnd_lastR i j ∧ bnd_vR i j q = s) := by
  have hdv := (bnd_mem_polyDiags _).mp hd
  simp only at hdv
  have hj := j.isLt
  by_cases hs : s.val < i.val ∨ j.val ≤ s.val
  · left
    refine ⟨bnd_uL i j s, fun h => ?_, bnd_vL_uL (by omega)⟩
    have := congrArg Fin.val h
    simp only [bnd_uL_val, bnd_iL] at this
    split_ifs at this <;> omega
  · right
    refine ⟨bnd_uR i j s, fun h => ?_, bnd_vR_uR (by omega)⟩
    have := congrArg Fin.val h
    simp only [bnd_uR_val, bnd_lastR] at this
    split_ifs at this <;> omega

/-- The character product of the labels of Cut_L. -/
private lemma bnd_prodL [NeZero L] (i j : Fin k) (n : Fin k → Fin L) (q : Fin L)
    (z : Fin (k + i - j + 1) → Fin L) :
    ∏ p, bnd_chi L (bnd_yL i j n q p) (z p) = bnd_chi L q (z (bnd_iL i j)) *
      ∏ p ∈ Finset.univ.erase (bnd_iL i j), bnd_chi L (n (bnd_vL i j p)) (z p) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (bnd_iL i j)), bnd_yL_iL]
  congr 1
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [bnd_yL_ne _ _ (Finset.ne_of_mem_erase hp)]

/-- The character product of the labels of Cut_R. -/
private lemma bnd_prodR [NeZero L] (i j : Fin k) (n : Fin k → Fin L) (q : Fin L)
    (z : Fin (j - i + 1) → Fin L) :
    ∏ p, bnd_chi L (bnd_yR i j n q p) (z p) = bnd_chi L q (z (bnd_lastR i j)) *
      ∏ p ∈ Finset.univ.erase (bnd_lastR i j), bnd_chi L (n (bnd_vR i j p)) (z p) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (bnd_lastR i j)), bnd_yR_lastR]
  congr 1
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [bnd_yR_ne _ _ (Finset.ne_of_mem_erase hp)]

/-- `Σ_q X̂(q) e^{-2πiqa/L} e^{2πiqb/L} = L X_{ab}` for a circulant `X`. -/
private lemma bnd_hat_sum [NeZero L] (X : Matrix (Fin L) (Fin L) ℂ)
    (hX : ∀ a a' c : Fin L, X (a + c) (a' + c) = X a a') (a b : Fin L) :
    ∑ q, bnd_hat X q * bnd_chi L q a * bnd_chi L (-q) b = L * X a b := by
  unfold bnd_hat
  have h1 : ∀ q, (∑ u, X 0 u * bnd_chi L q u) * bnd_chi L q a * bnd_chi L (-q) b =
      ∑ u, X 0 u * bnd_chi L (u + a - b) q := by
    intro q
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [bnd_chi_neg_left, bnd_chi_comm (u + a - b), sub_eq_add_neg, bnd_chi_add, bnd_chi_add]
    ring
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, bnd_sum_chi, mul_ite, mul_zero]
  have h2 : ∀ u : Fin L, (u + a - b = 0) ↔ u = b - a := by
    intro u
    constructor
    · intro h
      calc u = u + a - b + (b - a) := by abel
        _ = b - a := by rw [h, zero_add]
    · intro h; rw [h]; abel
  simp only [h2, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have h3 := hX 0 (b - a) a
  rw [zero_add, sub_add_cancel] at h3
  rw [← h3]
  ring

/-- The transform of the glued tensor. -/
private lemma bnd_tf_glue [NeZero L] {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    (X : Matrix (Fin L) (Fin L) ℂ) (hX : ∀ a a' c : Fin L, X (a + c) (a' + c) = X a a')
    (A : (Fin (k + i - j + 1) → Fin L) → ℂ) (B : (Fin (j - i + 1) → Fin L) → ℂ)
    (n : Fin k → Fin L) :
    tensorFourier (bnd_glueT i j X A B) n = ∑ q, bnd_hat X q *
      tensorFourier A (bnd_yL i j n q) * tensorFourier B (bnd_yR i j n (-q)) := by
  have hL : (L : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne L
  set ψL : (Fin (k + i - j + 1) → Fin L) → ℂ := fun z =>
    ∏ p ∈ Finset.univ.erase (bnd_iL i j), bnd_chi L (n (bnd_vL i j p)) (z p) with hψL
  set ψR : (Fin (j - i + 1) → Fin L) → ℂ := fun z =>
    ∏ p ∈ Finset.univ.erase (bnd_lastR i j), bnd_chi L (n (bnd_vR i j p)) (z p) with hψR
  have hside : ∀ (y : Fin k → Fin L) (xo xi : Fin L),
      ψL (bnd_yL i j y xo) * ψR (bnd_yR i j y xi) = ∏ s, bnd_chi L (n s) (y s) := by
    intro y xo xi
    rw [bnd_prod_sides hd (fun s => bnd_chi L (n s) (y s))]
    congr 1
    · refine Finset.prod_congr rfl fun p hp => ?_
      rw [bnd_yL_ne _ _ (Finset.ne_of_mem_erase hp)]
    · refine Finset.prod_congr rfl fun p hp => ?_
      rw [bnd_yR_ne _ _ (Finset.ne_of_mem_erase hp)]
  -- left side through the labels of the two polygons
  have hlhs : tensorFourier (bnd_glueT i j X A B) n = (L : ℂ)⁻¹ *
      ∑ zL : Fin (k + i - j + 1) → Fin L, ∑ zR : Fin (j - i + 1) → Fin L,
        X (zL (bnd_iL i j)) (zR (bnd_lastR i j)) * A zL * B zR * (ψL zL * ψR zR) := by
    rw [bnd_tf_eq, bnd_sum_labels hd]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    unfold bnd_glueT
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun xo _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun xi _ => ?_
    have e1 : (fun p : Fin (k + i - j + 1) => if p.val = i.val then xo else y (bnd_vL i j p)) =
        bnd_yL i j y xo := rfl
    have e2 : (fun q : Fin (j - i + 1) => if q.val = j.val - i.val then xi else y (bnd_vR i j q)) =
        bnd_yR i j y xi := rfl
    rw [e1, e2, bnd_yL_iL, bnd_yR_lastR, hside]
  rw [hlhs]
  simp only [bnd_tf_eq, bnd_prodL, bnd_prodR]
  have hX' : ∀ zL : Fin (k + i - j + 1) → Fin L, ∀ zR : Fin (j - i + 1) → Fin L,
      X (zL (bnd_iL i j)) (zR (bnd_lastR i j)) = (L : ℂ)⁻¹ * ∑ q, bnd_hat X q *
        bnd_chi L q (zL (bnd_iL i j)) * bnd_chi L (-q) (zR (bnd_lastR i j)) := by
    intro zL zR
    rw [bnd_hat_sum X hX]
    field_simp
  simp only [hX']
  calc (L : ℂ)⁻¹ * ∑ zL : Fin (k + i - j + 1) → Fin L, ∑ zR : Fin (j - i + 1) → Fin L,
        (L : ℂ)⁻¹ * (∑ q, bnd_hat X q * bnd_chi L q (zL (bnd_iL i j)) *
          bnd_chi L (-q) (zR (bnd_lastR i j))) * A zL * B zR * (ψL zL * ψR zR)
      = ∑ zL : Fin (k + i - j + 1) → Fin L, ∑ zR : Fin (j - i + 1) → Fin L, ∑ q,
          (L : ℂ)⁻¹ * (L : ℂ)⁻¹ * bnd_hat X q * (A zL * (bnd_chi L q (zL (bnd_iL i j)) * ψL zL)) *
            (B zR * (bnd_chi L (-q) (zR (bnd_lastR i j)) * ψR zR)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun zL _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun zR _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        ring
    _ = ∑ q, ∑ zL : Fin (k + i - j + 1) → Fin L, ∑ zR : Fin (j - i + 1) → Fin L,
          (L : ℂ)⁻¹ * (L : ℂ)⁻¹ * bnd_hat X q * (A zL * (bnd_chi L q (zL (bnd_iL i j)) * ψL zL)) *
            (B zR * (bnd_chi L (-q) (zR (bnd_lastR i j)) * ψR zR)) := by
        exact (Finset.sum_congr rfl fun zL _ => Finset.sum_comm).trans Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [mul_assoc, mul_assoc, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul_sum,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun zL _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun zR _ => ?_
        ring

/-- The norm of a glued tensor at fixed opposite cut momenta factors. -/
private lemma bnd_sum_glue_norm [NeZero L] {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    (w : Fin k → Fin L → ℝ) (wL : Fin (k + i - j + 1) → Fin L → ℝ)
    (wR : Fin (j - i + 1) → Fin L → ℝ)
    (hL : ∀ p, p ≠ bnd_iL i j → w (bnd_vL i j p) = wL p)
    (hR : ∀ q, q ≠ bnd_lastR i j → w (bnd_vR i j q) = wR q)
    (A : (Fin (k + i - j + 1) → Fin L) → ℂ) (B : (Fin (j - i + 1) → Fin L) → ℂ) (q q' : Fin L) :
    ∑ n : Fin k → Fin L, (∏ s, w s (n s)) * (‖tensorFourier A (bnd_yL i j n q)‖ *
        ‖tensorFourier B (bnd_yR i j n q')‖) =
      bnd_N (Function.update wL (bnd_iL i j) (bnd_del q)) A *
        bnd_N (Function.update wR (bnd_lastR i j) (bnd_del q')) B := by
  unfold bnd_N
  rw [Finset.sum_mul_sum, bnd_sum_labels' hd]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [bnd_prod_update, bnd_yL_iL, bnd_yR_lastR]
  set aL : Fin L → ℝ := fun xo => (∏ p ∈ Finset.univ.erase (bnd_iL i j),
    wL p (bnd_yL i j n xo p)) * ‖tensorFourier A (bnd_yL i j n xo)‖ with haL
  set bR : Fin L → ℝ := fun xi => (∏ p ∈ Finset.univ.erase (bnd_lastR i j),
    wR p (bnd_yR i j n xi p)) * ‖tensorFourier B (bnd_yR i j n xi)‖ with hbR
  have hprod : (∏ p ∈ Finset.univ.erase (bnd_iL i j), wL p (bnd_yL i j n q p)) *
      ∏ p ∈ Finset.univ.erase (bnd_lastR i j), wR p (bnd_yR i j n q' p) = ∏ s, w s (n s) := by
    rw [bnd_prod_sides hd (fun s => w s (n s))]
    congr 1
    · refine Finset.prod_congr rfl fun p hp => ?_
      have hp' := Finset.ne_of_mem_erase hp
      rw [bnd_yL_ne _ _ hp', hL p hp']
    · refine Finset.prod_congr rfl fun p hp => ?_
      have hp' := Finset.ne_of_mem_erase hp
      rw [bnd_yR_ne _ _ hp', hR p hp']
  rw [eq_comm]
  calc _ = ∑ xo, ∑ xi, (bnd_del q xo * aL xo) * (bnd_del q' xi * bR xi) :=
        Finset.sum_congr rfl fun xo _ => Finset.sum_congr rfl fun xi _ => by
          simp only [haL, hbR]; ring
    _ = aL q * bR q' := by rw [← Finset.sum_mul_sum, bnd_sum_del, bnd_sum_del]
    _ = _ := by
        simp only [haL, hbR]
        rw [← hprod]
        ring

/-- The weighted norm of a glued tensor. -/
private lemma bnd_N_glue [NeZero L] {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    (X : Matrix (Fin L) (Fin L) ℂ) (hX : ∀ a a' c : Fin L, X (a + c) (a' + c) = X a a')
    (A : (Fin (k + i - j + 1) → Fin L) → ℂ) (B : (Fin (j - i + 1) → Fin L) → ℂ)
    (w : Fin k → Fin L → ℝ) (wL : Fin (k + i - j + 1) → Fin L → ℝ)
    (wR : Fin (j - i + 1) → Fin L → ℝ)
    (hw : ∀ s x, 0 ≤ w s x)
    (hL : ∀ p, p ≠ bnd_iL i j → w (bnd_vL i j p) = wL p)
    (hR : ∀ q, q ≠ bnd_lastR i j → w (bnd_vR i j q) = wR q) :
    bnd_N w (bnd_glueT i j X A B) ≤ ∑ q, ‖bnd_hat X q‖ *
      (bnd_N (Function.update wL (bnd_iL i j) (bnd_del q)) A *
        bnd_N (Function.update wR (bnd_lastR i j) (bnd_del (-q))) B) := by
  simp only [← bnd_sum_glue_norm hd w wL wR hL hR A B, Finset.mul_sum]
  unfold bnd_N
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun n _ => ?_
  have hp : 0 ≤ ∏ s, w s (n s) := Finset.prod_nonneg fun s _ => hw s _
  rw [bnd_tf_glue hd X hX]
  calc (∏ s, w s (n s)) * ‖∑ q, bnd_hat X q * tensorFourier A (bnd_yL i j n q) *
        tensorFourier B (bnd_yR i j n (-q))‖
      ≤ (∏ s, w s (n s)) * ∑ q, ‖bnd_hat X q * tensorFourier A (bnd_yL i j n q) *
        tensorFourier B (bnd_yR i j n (-q))‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) hp
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [norm_mul, norm_mul]
        ring

/-- The glued norm with the left child bounded uniformly in the cut momentum. -/
private lemma bnd_N_glue_left [NeZero L] {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    (X : Matrix (Fin L) (Fin L) ℂ) (hX : ∀ a a' c : Fin L, X (a + c) (a' + c) = X a a')
    (A : (Fin (k + i - j + 1) → Fin L) → ℂ) (B : (Fin (j - i + 1) → Fin L) → ℂ)
    (w : Fin k → Fin L → ℝ) (wL : Fin (k + i - j + 1) → Fin L → ℝ)
    (wR : Fin (j - i + 1) → Fin L → ℝ)
    (hw : ∀ s x, 0 ≤ w s x) (hwL : ∀ s x, 0 ≤ wL s x) (hwR : ∀ s x, 0 ≤ wR s x)
    (hL : ∀ p, p ≠ bnd_iL i j → w (bnd_vL i j p) = wL p)
    (hR : ∀ q, q ≠ bnd_lastR i j → w (bnd_vR i j q) = wR q)
    (hXw : ∀ x, ‖bnd_hat X (-x)‖ ≤ wR (bnd_lastR i j) x) (aL : ℝ)
    (haL : ∀ q, bnd_N (Function.update wL (bnd_iL i j) (bnd_del q)) A ≤ aL) :
    bnd_N w (bnd_glueT i j X A B) ≤ aL * bnd_N wR B := by
  refine (bnd_N_glue hd X hX A B w wL wR hw hL hR).trans ?_
  have hB : ∀ q, 0 ≤ bnd_N (Function.update wR (bnd_lastR i j) (bnd_del (-q))) B :=
    fun q => bnd_N_nonneg (bnd_update_nonneg hwR (bnd_del_nonneg _)) B
  calc ∑ q, ‖bnd_hat X q‖ * (bnd_N (Function.update wL (bnd_iL i j) (bnd_del q)) A *
        bnd_N (Function.update wR (bnd_lastR i j) (bnd_del (-q))) B)
      ≤ ∑ q, ‖bnd_hat X q‖ * (aL * bnd_N (Function.update wR (bnd_lastR i j) (bnd_del (-q))) B) :=
        Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (haL q) (hB q)) (norm_nonneg _)
    _ = aL * ∑ x, ‖bnd_hat X (-x)‖ *
          bnd_N (Function.update wR (bnd_lastR i j) (bnd_del x)) B := by
        rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.neg (Fin L))]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [Equiv.neg_apply, neg_neg]
        ring
    _ = aL * bnd_N (Function.update wR (bnd_lastR i j) (fun x => ‖bnd_hat X (-x)‖)) B := by
        rw [bnd_N_update_sum]
    _ ≤ aL * bnd_N wR B := by
        have haL0 : 0 ≤ aL :=
          le_trans (bnd_N_nonneg (bnd_update_nonneg hwL (bnd_del_nonneg 0)) A) (haL 0)
        refine mul_le_mul_of_nonneg_left (bnd_N_mono (bnd_update_nonneg hwR
          (fun x => norm_nonneg _)) ?_ B) haL0
        intro s x
        by_cases hs : s = bnd_lastR i j
        · subst hs; simp only [Function.update_self]; exact hXw x
        · simp only [Function.update_of_ne hs, le_refl]

/-- The glued norm with the right child bounded uniformly in the cut momentum. -/
private lemma bnd_N_glue_right [NeZero L] {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    (X : Matrix (Fin L) (Fin L) ℂ) (hX : ∀ a a' c : Fin L, X (a + c) (a' + c) = X a a')
    (A : (Fin (k + i - j + 1) → Fin L) → ℂ) (B : (Fin (j - i + 1) → Fin L) → ℂ)
    (w : Fin k → Fin L → ℝ) (wL : Fin (k + i - j + 1) → Fin L → ℝ)
    (wR : Fin (j - i + 1) → Fin L → ℝ)
    (hw : ∀ s x, 0 ≤ w s x) (hwL : ∀ s x, 0 ≤ wL s x) (hwR : ∀ s x, 0 ≤ wR s x)
    (hL : ∀ p, p ≠ bnd_iL i j → w (bnd_vL i j p) = wL p)
    (hR : ∀ q, q ≠ bnd_lastR i j → w (bnd_vR i j q) = wR q)
    (hXw : ∀ x, ‖bnd_hat X x‖ ≤ wL (bnd_iL i j) x) (bR : ℝ)
    (hbR : ∀ q, bnd_N (Function.update wR (bnd_lastR i j) (bnd_del q)) B ≤ bR) :
    bnd_N w (bnd_glueT i j X A B) ≤ bnd_N wL A * bR := by
  refine (bnd_N_glue hd X hX A B w wL wR hw hL hR).trans ?_
  have hA : ∀ q, 0 ≤ bnd_N (Function.update wL (bnd_iL i j) (bnd_del q)) A :=
    fun q => bnd_N_nonneg (bnd_update_nonneg hwL (bnd_del_nonneg _)) A
  have hbR0 : 0 ≤ bR := le_trans (bnd_N_nonneg (bnd_update_nonneg hwR (bnd_del_nonneg 0)) B) (hbR 0)
  calc ∑ q, ‖bnd_hat X q‖ * (bnd_N (Function.update wL (bnd_iL i j) (bnd_del q)) A *
        bnd_N (Function.update wR (bnd_lastR i j) (bnd_del (-q))) B)
      ≤ ∑ q, ‖bnd_hat X q‖ * (bnd_N (Function.update wL (bnd_iL i j) (bnd_del q)) A * bR) :=
        Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hbR _) (hA q)) (norm_nonneg _)
    _ = (∑ q, ‖bnd_hat X q‖ * bnd_N (Function.update wL (bnd_iL i j) (bnd_del q)) A) * bR := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun q _ => ?_
        ring
    _ = bnd_N (Function.update wL (bnd_iL i j) (fun x => ‖bnd_hat X x‖)) A * bR := by
        rw [bnd_N_update_sum]
    _ ≤ bnd_N wL A * bR := by
        refine mul_le_mul_of_nonneg_right (bnd_N_mono (bnd_update_nonneg hwL
          (fun x => norm_nonneg _)) ?_ A) hbR0
        intro s x
        by_cases hs : s = bnd_iL i j
        · subst hs; simp only [Function.update_self]; exact hXw x
        · simp only [Function.update_of_ne hs, le_refl]

end GlueFourier

/-! ## Cores graded by the number of mixed diagonals

The molecule decomposition after (B.1) [ba:eq:dissection]: grading the dissection sum by the
number `r` of mixed diagonals, `r` times the graded core is the sum over the mixed diagonals of
the cores of the two polygons of the cut, glued by the mixed link `β t V_t`. -/

section Graded

variable {k L : ℕ}

/-- The number of mixed diagonals (joining opposite signs) of `F`. -/
private def bnd_cnt (σ : Fin k → Bool) (F : Finset (Fin k × Fin k)) : ℕ :=
  (F.filter (fun d => σ d.1 ≠ σ d.2)).card

/-- The core summed over the dissections with exactly `r` mixed diagonals. -/
def bnd_Cr (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) (σ : Fin k → Bool) (r : ℕ)
    (y : Fin k → Fin L) : ℂ :=
  ∑ F ∈ (dissections k).filter (fun F => bnd_cnt σ F = r), dissCore β M t σ F y

/-- The number of mixed diagonals of `F ∋ (i, j)`, `(i, j)` mixed, is one plus those of the two
polygons of the cut. -/
private lemma bnd_cnt_split {i j : Fin k} (hd : (i, j) ∈ polyDiags k) {σ : Fin k → Bool}
    (hmix : σ i ≠ σ j) {F : Finset (Fin k × Fin k)} (hF : F ∈ dissections k) (hdF : (i, j) ∈ F) :
    bnd_cnt σ F = 1 + bnd_cnt (cutLSgn σ i j) (bnd_splitL i j F) +
      bnd_cnt (cutRSgn σ i j) (bnd_splitR i j F) := by
  set e := Equiv.ofBijective _ (bnd_eqvFun_bij hd hF hdF) with he_def
  unfold bnd_cnt
  simp only [Finset.card_filter]
  rw [← Finset.sum_coe_sort F, ← Finset.sum_coe_sort (bnd_splitL i j F),
    ← Finset.sum_coe_sort (bnd_splitR i j F), ← e.sum_comp, Fintype.sum_option,
    Fintype.sum_sum_type]
  have he0 : e none = ⟨(i, j), hdF⟩ := rfl
  have heL : ∀ a, e (some (Sum.inl a)) = bnd_ιL i j F a := fun a => rfl
  have heR : ∀ b, e (some (Sum.inr b)) = bnd_ιR i j F b := fun b => rfl
  simp only [he0, heL, heR, bnd_ιL, bnd_ιR, bnd_cutLSgn_eq, bnd_cutRSgn_eq]
  simp only [ne_eq, hmix, not_false_eq_true, ite_true]
  rw [add_assoc]
  congr

/-- The core of `F ∋ (i, j)` with the link of `(i, j)` written as the matrix `β t V_t`. -/
private lemma bnd_dissCore_eq_coreD (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ)
    (σ : Fin k → Bool) {i j : Fin k} (F : Finset (Fin k × Fin k)) (y : Fin k → Fin L) :
    dissCore β M t σ F y =
      bnd_coreD β M t σ F (i, j) (((β * t : ℝ) : ℂ) • pairV β M t (σ i) (σ j)) y := by
  unfold dissCore bnd_coreD
  refine Finset.sum_congr rfl fun cIn _ => Finset.sum_congr rfl fun cOut _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun e _ => ?_
  split_ifs with h
  · rw [h, Matrix.smul_apply, smul_eq_mul]
  · rfl

/-- Exchange of two pairs of finite sums. -/
private lemma bnd_sum_swap4 {α β γ δ : Type*} (s₁ : Finset α) (s₂ : Finset β) (s₃ : Finset γ)
    (s₄ : Finset δ) (f : α → β → γ → δ → ℂ) :
    ∑ a ∈ s₁, ∑ b ∈ s₂, ∑ c ∈ s₃, ∑ d ∈ s₄, f a b c d =
      ∑ c ∈ s₃, ∑ d ∈ s₄, ∑ a ∈ s₁, ∑ b ∈ s₂, f a b c d :=
  (Finset.sum_congr rfl fun _ _ => (Finset.sum_comm.trans
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm))).trans
    (Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm))

/-- Regrouping a double sum by the grades of the two factors. -/
private lemma bnd_regroup {α γ : Type*} (s : Finset α) (u : Finset γ) (cA : α → ℕ) (cB : γ → ℕ)
    (f : α → γ → ℂ) (r : ℕ) :
    ∑ a ∈ s, ∑ b ∈ u, (if 1 + cA a + cB b = r then f a b else 0) =
      ∑ rL ∈ Finset.range r, ∑ a ∈ s.filter (fun a => cA a = rL),
        ∑ b ∈ u.filter (fun b => cB b = r - 1 - rL), f a b := by
  symm
  calc ∑ rL ∈ Finset.range r, ∑ a ∈ s.filter (fun a => cA a = rL),
        ∑ b ∈ u.filter (fun b => cB b = r - 1 - rL), f a b
      = ∑ rL ∈ Finset.range r, ∑ a ∈ s, ∑ b ∈ u,
          (if cA a = rL ∧ cB b = r - 1 - rL then f a b else 0) := by
        refine Finset.sum_congr rfl fun rL _ => ?_
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_filter]
        by_cases h1 : cA a = rL
        · rw [ite_eq_left h1]
          refine Finset.sum_congr rfl fun b _ => ?_
          by_cases h2 : cB b = r - 1 - rL
          · rw [ite_eq_left h2, ite_eq_left ⟨h1, h2⟩]
          · rw [ite_eq_right h2, ite_eq_right (fun h => h2 h.2)]
        · rw [ite_eq_right h1]
          exact (Finset.sum_eq_zero fun b _ => ite_eq_right (fun h => h1 h.1)).symm
    _ = ∑ a ∈ s, ∑ b ∈ u, ∑ rL ∈ Finset.range r,
          (if cA a = rL ∧ cB b = r - 1 - rL then f a b else 0) :=
        Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm)
    _ = _ := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        by_cases h : 1 + cA a + cB b = r
        · rw [ite_eq_left h, Finset.sum_eq_single (cA a)]
          · rw [ite_eq_left ⟨rfl, by omega⟩]
          · intro rL _ hne
            rw [ite_eq_right (fun h' => hne h'.1.symm)]
          · intro hn
            exact absurd (Finset.mem_range.mpr (by omega)) hn
        · rw [ite_eq_right h]
          refine Finset.sum_eq_zero fun rL hrL => ?_
          rw [ite_eq_right]
          rintro ⟨h1, h2⟩
          have := Finset.mem_range.mp hrL
          omega

/-- The glued tensor is bilinear in the two factors. -/
private lemma bnd_glueT_sum {i j : Fin k} {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (X : Matrix (Fin L) (Fin L) ℂ) (A : ι → (Fin (k + i - j + 1) → Fin L) → ℂ)
    (B : κ → (Fin (j - i + 1) → Fin L) → ℂ) (y : Fin k → Fin L) :
    bnd_glueT i j X (fun z => ∑ a ∈ S, A a z) (fun z => ∑ b ∈ T, B b z) y =
      ∑ a ∈ S, ∑ b ∈ T, bnd_glueT i j X (A a) (B b) y := by
  unfold bnd_glueT
  beta_reduce
  rw [← bnd_sum_swap4]
  refine Finset.sum_congr rfl fun xo _ => Finset.sum_congr rfl fun xi _ => ?_
  rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- The graded core with the diagonal `(i, j)` marked: the glued graded cores of the two
polygons of the cut. -/
private lemma bnd_Cr_diag (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) {σ : Fin k → Bool}
    {i j : Fin k} (hd : (i, j) ∈ polyDiags k) (hmix : σ i ≠ σ j) (r : ℕ) (y : Fin k → Fin L) :
    ∑ F ∈ (dissections k).filter (fun F => bnd_cnt σ F = r ∧ (i, j) ∈ F), dissCore β M t σ F y =
      ∑ rL ∈ Finset.range r, bnd_glueT i j (((β * t : ℝ) : ℂ) • pairV β M t (σ i) (σ j))
        (bnd_Cr β M t (cutLSgn σ i j) rL) (bnd_Cr β M t (cutRSgn σ i j) (r - 1 - rL)) y := by
  set X := ((β * t : ℝ) : ℂ) • pairV β M t (σ i) (σ j) with hX
  have h1 : ∑ F ∈ (dissections k).filter (fun F => bnd_cnt σ F = r ∧ (i, j) ∈ F),
      dissCore β M t σ F y = ∑ F ∈ (dissections k).filter (fun F => (i, j) ∈ F),
        (if 1 + bnd_cnt (cutLSgn σ i j) (bnd_splitL i j F) +
            bnd_cnt (cutRSgn σ i j) (bnd_splitR i j F) = r then
          ∑ xo : Fin L, ∑ xi : Fin L, X xo xi *
            dissCore β M t (cutLSgn σ i j) (bnd_splitL i j F) (bnd_yL i j y xo) *
            dissCore β M t (cutRSgn σ i j) (bnd_splitR i j F) (bnd_yR i j y xi) else 0) := by
    rw [← Finset.filter_filter, Finset.filter_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl fun F hF => ?_
    rw [Finset.mem_filter] at hF
    rw [← bnd_cnt_split hd hmix hF.1 hF.2]
    split_ifs
    · rw [bnd_dissCore_eq_coreD β M t σ (i := i) (j := j), bnd_coreD_split hd hF.1 hF.2]
      rfl
    · rfl
  rw [h1, bnd_sum_split hd (fun FL FR => if 1 + bnd_cnt (cutLSgn σ i j) FL +
      bnd_cnt (cutRSgn σ i j) FR = r then ∑ xo : Fin L, ∑ xi : Fin L, X xo xi *
        dissCore β M t (cutLSgn σ i j) FL (bnd_yL i j y xo) *
        dissCore β M t (cutRSgn σ i j) FR (bnd_yR i j y xi) else 0)]
  rw [bnd_regroup]
  refine Finset.sum_congr rfl fun rL _ => ?_
  unfold bnd_Cr
  rw [bnd_glueT_sum]
  rfl

/-- `r C_r = Σ_{mixed (i,j)} Σ_{r_L + r_R = r - 1} glue(C_{r_L}, C_{r_R})`. -/
lemma bnd_Cr_rec (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) (σ : Fin k → Bool)
    (r : ℕ) (y : Fin k → Fin L) :
    (r : ℂ) * bnd_Cr β M t σ r y =
      ∑ d ∈ (polyDiags k).filter (fun d => σ d.1 ≠ σ d.2), ∑ rL ∈ Finset.range r,
        bnd_glueT d.1 d.2 (((β * t : ℝ) : ℂ) • pairV β M t (σ d.1) (σ d.2))
          (bnd_Cr β M t (cutLSgn σ d.1 d.2) rL) (bnd_Cr β M t (cutRSgn σ d.1 d.2) (r - 1 - rL))
          y := by
  have h1 : (r : ℂ) * bnd_Cr β M t σ r y = ∑ F ∈ (dissections k).filter
      (fun F => bnd_cnt σ F = r), ∑ d ∈ F.filter (fun d => σ d.1 ≠ σ d.2),
        dissCore β M t σ F y := by
    unfold bnd_Cr
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun F hF => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.mem_filter] at hF
    unfold bnd_cnt at hF
    rw [hF.2]
  rw [h1]
  rw [Finset.sum_comm' (t' := (polyDiags k).filter (fun d => σ d.1 ≠ σ d.2))
    (s' := fun d => (dissections k).filter (fun F => bnd_cnt σ F = r ∧ d ∈ F))]
  · refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_filter] at hd
    exact bnd_Cr_diag β M t (i := d.1) (j := d.2) hd.1 hd.2 r y
  · intro F d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hF, hr⟩, hdF, hmix⟩
      exact ⟨⟨hF, hr, hdF⟩, (bnd_mem_dissections F).mp hF |>.1 hdF, hmix⟩
    · rintro ⟨⟨hF, hr, hdF⟩, _, hmix⟩
      exact ⟨⟨hF, hr⟩, hdF, hmix⟩

end Graded

/-! ## The stable molecule: norms from (B.2) [ba:eq:moment] and (B.3) [ba:eq:cancel]

The single-molecule estimates of the proof of Proposition B.2 [ba:prop:primitive]: a stable
external leg is made dependent; for an alternating molecule (B.3) [ba:eq:cancel] and the
coercivity (A.25) [ba:eq:coercivity] cancel one mixed leg at the cost `k Ξ_g`,
`Ξ_g = 1 + g⁻²`. -/

section Base

variable {L : ℕ}

/-- The leg weights: a constant `C_s` on a stable leg, `U(q) = (1 - tP̂(q))⁻¹` on a mixed leg. -/
def bnd_w {k : ℕ} (U : Fin L → ℝ) (Cs : ℝ) (σ : Fin k → Bool) (j : Fin k) (q : Fin L) :
    ℝ :=
  if σ j = σ (finRotate k j) then Cs else U q

lemma bnd_w_nonneg {k : ℕ} {U : Fin L → ℝ} {Cs : ℝ} (hU : ∀ q, 0 ≤ U q) (hCs : 0 ≤ Cs)
    (σ : Fin k → Bool) (j : Fin k) (q : Fin L) : 0 ≤ bnd_w U Cs σ j q := by
  unfold bnd_w; split_ifs
  · exact hCs
  · exact hU q

/-- `∏_j (if j = i then 1 else f j) = ∏_{j ≠ i} f j`. -/
lemma bnd_prod_ite_one {k : ℕ} {R : Type*} [CommMonoid R] (f : Fin k → R) (i : Fin k) :
    ∏ j, (if j = i then 1 else f j) = ∏ j ∈ Finset.univ.erase i, f j := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [ite_true, one_mul]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [ite_eq_right (Finset.ne_of_mem_erase hj)]

/-- The cyclic distance to `0` on `ℤ_L`. -/
private def bnd_d (x : Fin L) : ℕ := min x.val (L - x.val)

private lemma bnd_d_neg [NeZero L] (x : Fin L) : bnd_d (-x) = bnd_d x := by
  unfold bnd_d
  rw [Fin.val_neg']
  have hx := x.isLt
  rcases Nat.eq_zero_or_pos x.val with h | h
  · rw [h]; simp
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

private lemma bnd_d_add [NeZero L] (x y : Fin L) : bnd_d (x + y) ≤ bnd_d x + bnd_d y := by
  unfold bnd_d
  rw [Fin.val_add]
  have hx := x.isLt
  have hy := y.isLt
  rcases Nat.lt_or_ge (x.val + y.val) L with h | h
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega

private lemma bnd_d_sum [NeZero L] {k : ℕ} (s : Finset (Fin k)) (n : Fin k → Fin L) :
    bnd_d (∑ j ∈ s, n j) ≤ ∑ j ∈ s, bnd_d (n j) := by
  induction s using Finset.induction_on with
  | empty => simp [bnd_d]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (bnd_d_add _ _).trans (by omega)

/-- Circular triangle inequality: `|n_v|_𝕋 ≤ Σ_{j ≠ v} |n_j|_𝕋` when `Σ_j n_j = 0`. -/
lemma bnd_torus_tri [NeZero L] {k : ℕ} (n : Fin k → Fin L) (hn : ∑ j, n j = 0)
    (v : Fin k) : torusAbs L (n v) ≤ ∑ j ∈ Finset.univ.erase v, torusAbs L (n j) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hv : n v = -∑ j ∈ Finset.univ.erase v, n j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)] at hn
    exact eq_neg_of_add_eq_zero_left hn
  have hd : bnd_d (n v) ≤ ∑ j ∈ Finset.univ.erase v, bnd_d (n j) := by
    rw [hv, bnd_d_neg]
    exact bnd_d_sum _ _
  have h1 : ∀ x : Fin L, torusAbs L x = 2 * π / L * (bnd_d x : ℝ) := by
    intro x; unfold torusAbs bnd_d; ring
  rw [h1, ← Finset.sum_congr rfl fun j _ => (h1 (n j)).symm, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact_mod_cast hd

/-- The coercivity step: `δ + Σ_j τ_j² ≤ k Ξ_g Σ_{j ≠ v} (δ + g²τ_j²)` when
`τ_v ≤ Σ_{j ≠ v} τ_j`. -/
private lemma bnd_coer {k : ℕ} (hk : 2 ≤ k) {g δ : ℝ} (hg : 0 < g) (hδ : 0 ≤ δ) (τ : Fin k → ℝ)
    (hτ : ∀ j, 0 ≤ τ j) (v : Fin k) (htri : τ v ≤ ∑ j ∈ Finset.univ.erase v, τ j) :
    δ + ∑ j, τ j ^ 2 ≤
      k * (1 + (g ^ 2)⁻¹) * ∑ j ∈ Finset.univ.erase v, (δ + g ^ 2 * τ j ^ 2) := by
  have hcard : ((Finset.univ.erase v).card : ℝ) = k - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
    have : 1 ≤ k := by omega
    push_cast [this]
    ring
  set T := ∑ j ∈ Finset.univ.erase v, τ j ^ 2 with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hsq : τ v ^ 2 ≤ (k - 1) * T := by
    have h0 : 0 ≤ τ v := hτ v
    calc τ v ^ 2 ≤ (∑ j ∈ Finset.univ.erase v, τ j) ^ 2 := pow_le_pow_left₀ h0 htri 2
      _ ≤ ((Finset.univ.erase v).card : ℝ) * T := sq_sum_le_card_mul_sum_sq
      _ = (k - 1) * T := by rw [hcard]
  have hsum : ∑ j, τ j ^ 2 = τ v ^ 2 + T :=
    (Finset.add_sum_erase _ (fun j => τ j ^ 2) (Finset.mem_univ v)).symm
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hg2 : 0 < g ^ 2 := by positivity
  have hΞ : (1 + (g ^ 2)⁻¹) * g ^ 2 = g ^ 2 + 1 := by field_simp
  have hR : ∑ j ∈ Finset.univ.erase v, (δ + g ^ 2 * τ j ^ 2) = (k - 1) * δ + g ^ 2 * T := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard, ← Finset.mul_sum]
  rw [hsum, hR]
  have hinv : 0 ≤ (g ^ 2)⁻¹ := by positivity
  have e : k * (1 + (g ^ 2)⁻¹) * ((k - 1) * δ + g ^ 2 * T) =
      k * (1 + (g ^ 2)⁻¹) * (k - 1) * δ + k * (g ^ 2 + 1) * T := by
    rw [← hΞ]; ring
  rw [e]
  have h1 : δ ≤ k * (1 + (g ^ 2)⁻¹) * (k - 1) * δ := by
    have hA : (1 : ℝ) ≤ 1 + (g ^ 2)⁻¹ := by linarith
    have hB : (2 : ℝ) ≤ k * (1 + (g ^ 2)⁻¹) := by nlinarith
    have hC : (1 : ℝ) ≤ k - 1 := by linarith
    have hD : 1 ≤ k * (1 + (g ^ 2)⁻¹) * (k - 1) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hD hδ]
  have h2 : τ v ^ 2 + T ≤ k * (g ^ 2 + 1) * T := by nlinarith
  linarith

/-- The constant of the single-molecule estimates. -/
def bnd_KB (k : ℕ) (Cs CU Kb : ℝ) : ℝ := Kb * ((k : ℝ) ^ 2 * CU + Cs * (2 * Cs) ^ k)

/-- The norm of a tensor supported on `Σ_j n_j = 0` with `|Ŝ| ≤ K_b` and a leg `s` of constant
weight `C_s`. -/
lemma bnd_N_stableLeg [NeZero L] {k : ℕ} (S : (Fin k → Fin L) → ℂ)
    (hsupp : ∀ n, ∑ j, n j ≠ 0 → tensorFourier S n = 0) {Kb Cs : ℝ}
    (hS1 : ∀ n, ‖tensorFourier S n‖ ≤ Kb) (w : Fin k → Fin L → ℝ) (hw : ∀ j x, 0 ≤ w j x)
    (s : Fin k) (hs : ∀ x, w s x = Cs) :
    bnd_N w S ≤ Cs * Kb * ∏ j ∈ Finset.univ.erase s, ∑ x, w j x := by
  have hCs : 0 ≤ Cs := by rw [← hs 0]; exact hw s 0
  rw [← bnd_sum_constraint_prod s w, Finset.mul_sum]
  unfold bnd_N
  refine Finset.sum_le_sum fun n _ => ?_
  by_cases hn : ∑ j, n j = 0
  · rw [ite_eq_left hn]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ s), hs, bnd_prod_ite_one]
    have hP : 0 ≤ ∏ j ∈ Finset.univ.erase s, w j (n j) := Finset.prod_nonneg fun j _ => hw j _
    calc Cs * (∏ j ∈ Finset.univ.erase s, w j (n j)) * ‖tensorFourier S n‖
        ≤ Cs * (∏ j ∈ Finset.univ.erase s, w j (n j)) * Kb :=
          mul_le_mul_of_nonneg_left (hS1 n) (mul_nonneg hCs hP)
      _ = Cs * Kb * ∏ j ∈ Finset.univ.erase s, w j (n j) := by ring
  · rw [ite_eq_right hn, hsupp n hn, norm_zero, mul_zero, mul_zero]

/-- A product of `m` factors each at most `c`. -/
lemma bnd_prod_le_pow {k : ℕ} (s : Finset (Fin k)) (f : Fin k → ℝ) (c : ℝ)
    (hf0 : ∀ j ∈ s, 0 ≤ f j) (hf : ∀ j ∈ s, f j ≤ c) : ∏ j ∈ s, f j ≤ c ^ s.card := by
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod₀ hf0 hf

/-- The marginal of an alternating molecule (B.3) [ba:eq:cancel]. -/
private lemma bnd_alt_marg [NeZero L] {k : ℕ} (hk : 3 ≤ k) (S : (Fin k → Fin L) → ℂ)
    (hsupp : ∀ n, ∑ j, n j ≠ 0 → tensorFourier S n = 0) {U : Fin L → ℝ} {CU Kb g δ : ℝ}
    (hU : ∀ q, 0 ≤ U q) (hKb : 0 ≤ Kb) (hg : 0 < g) (hδ : 0 ≤ δ)
    (hcoer : ∀ q, U q * (δ + g ^ 2 * torusAbs L q ^ 2) ≤ CU)
    (hS2 : ∀ n, ∑ j, n j = 0 → ‖tensorFourier S n‖ ≤ Kb * (δ + ∑ j, torusAbs L (n j) ^ 2))
    (v : Fin k) (q : Fin L) :
    bnd_N (Function.update (fun _ => U) v (bnd_del q)) S ≤
      Kb * k * (1 + (g ^ 2)⁻¹) * CU * ((k - 1) * (∑ x, U x) ^ (k - 2)) := by
  set wv : Fin k → Fin L → ℝ := Function.update (fun _ => U) v (bnd_del q) with hwv
  have hwv0 : ∀ j x, 0 ≤ wv j x := bnd_update_nonneg (fun _ => hU) (bnd_del_nonneg q)
  have hwv_ne : ∀ j, j ≠ v → wv j = U := fun j hj => by rw [hwv, Function.update_of_ne hj]
  have hwv_v : wv v = bnd_del q := by rw [hwv, Function.update_self]
  set Ξ := 1 + (g ^ 2)⁻¹ with hΞ
  have hΞ1 : 1 ≤ Ξ := by have : 0 ≤ (g ^ 2)⁻¹ := by positivity
                         linarith
  have hCU : 0 ≤ CU := le_trans (mul_nonneg (hU 0) (by positivity)) (hcoer 0)
  -- the pointwise estimate on `Σ_j n_j = 0`
  have hpt : ∀ n : Fin k → Fin L, ∑ j, n j = 0 →
      (∏ j, wv j (n j)) * ‖tensorFourier S n‖ ≤ Kb * k * Ξ * CU *
        ∑ i ∈ Finset.univ.erase v, ∏ j, (if j = i then 1 else wv j (n j)) := by
    intro n hn
    have hterm : ∀ i ∈ Finset.univ.erase v, ∏ j, (if j = i then 1 else wv j (n j)) =
        bnd_del q (n v) * ∏ j ∈ (Finset.univ.erase v).erase i, U (n j) := by
      intro i hi
      have hiv := Finset.ne_of_mem_erase hi
      rw [bnd_prod_ite_one, ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hiv,
        Finset.mem_univ v⟩), hwv_v, Finset.erase_right_comm]
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [hwv_ne j (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj))]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hlhs : ∏ j, wv j (n j) = bnd_del q (n v) * ∏ j ∈ Finset.univ.erase v, U (n j) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v), hwv_v]
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [hwv_ne j (Finset.ne_of_mem_erase hj)]
    rw [hlhs]
    have hd0 := bnd_del_nonneg q (n v)
    have hP0 : 0 ≤ ∏ j ∈ Finset.univ.erase v, U (n j) := Finset.prod_nonneg fun j _ => hU _
    -- `P ‖Ŝ‖ ≤ K_b k Ξ C_U Σ_i Π_{j ≠ v, i} U`
    have hτ0 : ∀ j, 0 ≤ torusAbs L (n j) := fun j => by unfold torusAbs; positivity
    have hco := bnd_coer (by omega) hg hδ (fun j => torusAbs L (n j)) hτ0 v (bnd_torus_tri n hn v)
    have hkey : (∏ j ∈ Finset.univ.erase v, U (n j)) * ‖tensorFourier S n‖ ≤
        Kb * k * Ξ * CU *
          ∑ i ∈ Finset.univ.erase v, ∏ j ∈ (Finset.univ.erase v).erase i, U (n j) := by
      calc (∏ j ∈ Finset.univ.erase v, U (n j)) * ‖tensorFourier S n‖
          ≤ (∏ j ∈ Finset.univ.erase v, U (n j)) * (Kb * (δ + ∑ j, torusAbs L (n j) ^ 2)) :=
            mul_le_mul_of_nonneg_left (hS2 n hn) hP0
        _ ≤ (∏ j ∈ Finset.univ.erase v, U (n j)) * (Kb * (k * Ξ *
              ∑ i ∈ Finset.univ.erase v, (δ + g ^ 2 * torusAbs L (n i) ^ 2))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hco hKb) hP0
        _ = Kb * k * Ξ * ∑ i ∈ Finset.univ.erase v, (∏ j ∈ Finset.univ.erase v, U (n j)) *
              (δ + g ^ 2 * torusAbs L (n i) ^ 2) := by
            rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
        _ ≤ Kb * k * Ξ * ∑ i ∈ Finset.univ.erase v, CU *
              ∏ j ∈ (Finset.univ.erase v).erase i, U (n j) := by
            have hk0 : (0 : ℝ) ≤ Kb * k * Ξ := by positivity
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) hk0
            rw [← Finset.mul_prod_erase _ _ hi]
            have hQ : 0 ≤ ∏ j ∈ (Finset.univ.erase v).erase i, U (n j) :=
              Finset.prod_nonneg fun j _ => hU _
            calc U (n i) * (∏ j ∈ (Finset.univ.erase v).erase i, U (n j)) *
                  (δ + g ^ 2 * torusAbs L (n i) ^ 2)
                = (U (n i) * (δ + g ^ 2 * torusAbs L (n i) ^ 2)) *
                    ∏ j ∈ (Finset.univ.erase v).erase i, U (n j) := by ring
              _ ≤ CU * ∏ j ∈ (Finset.univ.erase v).erase i, U (n j) :=
                  mul_le_mul_of_nonneg_right (hcoer _) hQ
        _ = Kb * k * Ξ * CU * ∑ i ∈ Finset.univ.erase v,
              ∏ j ∈ (Finset.univ.erase v).erase i, U (n j) := by
            rw [← Finset.mul_sum]; ring
    calc bnd_del q (n v) * (∏ j ∈ Finset.univ.erase v, U (n j)) * ‖tensorFourier S n‖
        = bnd_del q (n v) * ((∏ j ∈ Finset.univ.erase v, U (n j)) * ‖tensorFourier S n‖) := by
          ring
      _ ≤ bnd_del q (n v) * (Kb * k * Ξ * CU *
            ∑ i ∈ Finset.univ.erase v, ∏ j ∈ (Finset.univ.erase v).erase i, U (n j)) :=
          mul_le_mul_of_nonneg_left hkey hd0
      _ = _ := by ring
  -- summing over the momenta
  have hsum : bnd_N wv S ≤ Kb * k * Ξ * CU * ∑ i ∈ Finset.univ.erase v,
      ∑ n : Fin k → Fin L,
        (if ∑ j, n j = 0 then ∏ j, (if j = i then 1 else wv j (n j)) else 0) := by
    unfold bnd_N
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    by_cases hn : ∑ j, n j = 0
    · simp only [ite_eq_left hn]
      exact hpt n hn
    · simp only [ite_eq_right hn, Finset.sum_const_zero, mul_zero]
      rw [hsupp n hn, norm_zero, mul_zero]
  refine hsum.trans (le_of_eq ?_)
  have hval : ∀ i ∈ Finset.univ.erase v,
      ∑ n : Fin k → Fin L, (if ∑ j, n j = 0 then ∏ j, (if j = i then 1 else wv j (n j)) else 0) =
        (∑ x, U x) ^ (k - 2) := by
    intro i hi
    have hiv := Finset.ne_of_mem_erase hi
    rw [bnd_sum_constraint_prod i wv]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hiv, Finset.mem_univ v⟩),
      hwv_v]
    have h1 : ∑ x, bnd_del q x = 1 := by
      have := bnd_sum_del q (fun _ => 1); simpa using this
    rw [h1, one_mul]
    rw [Finset.prod_congr rfl fun j hj => by
      rw [hwv_ne j (Finset.ne_of_mem_erase hj)]]
    rw [Finset.prod_const]
    congr 1
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hiv, Finset.mem_univ v⟩),
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
  push_cast [show 1 ≤ k by omega]
  ring

/-- The norm and the mixed-leg marginals of a stable molecule, Proposition B.2
[ba:prop:primitive], single-molecule step. -/
private lemma bnd_base [NeZero L] {k : ℕ} (hk : 3 ≤ k) (S : (Fin k → Fin L) → ℂ)
    (hS : ∀ (y : Fin k → Fin L) (c : Fin L), S (fun i => y i + c) = S y) (σ : Fin k → Bool)
    {U : Fin L → ℝ} {Cs CU Kb g δ : ℝ} (hU : ∀ q, 1 / 2 ≤ U q) (hCs : 1 ≤ Cs) (hKb : 0 ≤ Kb)
    (hg : 0 < g) (hδ : 0 ≤ δ) (hcoer : ∀ q, U q * (δ + g ^ 2 * torusAbs L q ^ 2) ≤ CU)
    (hS1 : ∀ n, ‖tensorFourier S n‖ ≤ Kb)
    (hS2 : (∀ i, σ (finRotate k i) = !σ i) → ∀ n, ∑ j, n j = 0 →
      ‖tensorFourier S n‖ ≤ Kb * (δ + ∑ j, torusAbs L (n j) ^ 2)) :
    bnd_N (bnd_w U Cs σ) S ≤
        bnd_KB k Cs CU Kb * (1 + (g ^ 2)⁻¹) ^ (k - 2) * (∑ q, U q) ^ (k - 1) ∧
      ∀ v, σ v ≠ σ (finRotate k v) → ∀ q,
        bnd_N (Function.update (bnd_w U Cs σ) v (bnd_del q)) S ≤
          bnd_KB k Cs CU Kb * (1 + (g ^ 2)⁻¹) ^ (k - 2) * (∑ q, U q) ^ (k - 2) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hU0 : ∀ q, 0 ≤ U q := fun q => le_trans (by norm_num) (hU q)
  have hCU : 0 ≤ CU := le_trans (mul_nonneg (hU0 0) (by unfold torusAbs; positivity)) (hcoer 0)
  set H := ∑ q, U q with hH
  have hHL : (L : ℝ) / 2 ≤ H := by
    have : ∑ q : Fin L, (1 / 2 : ℝ) ≤ H := Finset.sum_le_sum fun q _ => hU q
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    linarith
  have hH0 : 0 ≤ H := le_trans (by positivity) hHL
  set Ξ := 1 + (g ^ 2)⁻¹ with hΞ
  have hΞ1 : 1 ≤ Ξ := by
    have : 0 ≤ (g ^ 2)⁻¹ := by positivity
    linarith
  have hΞk : Ξ ≤ Ξ ^ (k - 2) := by
    calc Ξ = Ξ ^ 1 := (pow_one Ξ).symm
      _ ≤ Ξ ^ (k - 2) := pow_le_pow_right₀ hΞ1 (by omega)
  have hΞk1 : 1 ≤ Ξ ^ (k - 2) := one_le_pow₀ hΞ1
  have hsupp : ∀ n, ∑ j, n j ≠ 0 → tensorFourier S n = 0 := bnd_tf_support S hS
  have hk2 : (2 : ℝ) ≤ (k : ℝ) - 1 + 1 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hw0 : ∀ j x, 0 ≤ bnd_w U Cs σ j x := bnd_w_nonneg hU0 (by linarith) σ
  have hKB0 : 0 ≤ Kb * ((k : ℝ) ^ 2 * CU) := by positivity
  have hKB1 : 0 ≤ Kb * (Cs * (2 * Cs) ^ k) := by
    have : 0 ≤ Cs := by linarith
    positivity
  have hKB : bnd_KB k Cs CU Kb = Kb * ((k : ℝ) ^ 2 * CU) + Kb * (Cs * (2 * Cs) ^ k) := by
    unfold bnd_KB; ring
  by_cases halt : ∀ i, σ (finRotate k i) = !σ i
  · -- alternating: every leg is mixed
    have hwU : bnd_w U Cs σ = fun _ => U := by
      funext j x
      unfold bnd_w
      rw [halt j]
      cases σ j <;> simp
    have hS2' := hS2 halt
    have hmarg : ∀ v q, bnd_N (Function.update (bnd_w U Cs σ) v (bnd_del q)) S ≤
        Kb * k * Ξ * CU * ((k - 1) * H ^ (k - 2)) := by
      intro v q
      rw [hwU]
      exact bnd_alt_marg hk S hsupp hU0 hKb hg hδ hcoer hS2' v q
    have hM0 : Kb * k * Ξ * CU * ((k - 1) * H ^ (k - 2)) ≤
        bnd_KB k Cs CU Kb * Ξ ^ (k - 2) * H ^ (k - 2) := by
      rw [hKB]
      have hk1 : (k : ℝ) * (k - 1) ≤ (k : ℝ) ^ 2 := by nlinarith
      have hHk : 0 ≤ H ^ (k - 2) := pow_nonneg hH0 _
      have h1 : Kb * k * Ξ * CU * ((k - 1) * H ^ (k - 2)) =
          (Kb * (k * (k - 1)) * CU) * Ξ * H ^ (k - 2) := by ring
      rw [h1]
      have h2 : (Kb * (k * (k - 1)) * CU) * Ξ * H ^ (k - 2) ≤
          (Kb * ((k : ℝ) ^ 2 * CU)) * Ξ ^ (k - 2) * H ^ (k - 2) := by
        have h3 : Kb * (k * (k - 1)) * CU ≤ Kb * ((k : ℝ) ^ 2 * CU) := by
          have := mul_le_mul_of_nonneg_right hk1 hCU
          nlinarith
        have h4 : 0 ≤ Kb * (k * (k - 1)) * CU := by
          have : (0 : ℝ) ≤ k * (k - 1) := by nlinarith
          positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul h3 hΞk (by linarith) hKB0) hHk
      refine h2.trans ?_
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by linarith)) hHk
      linarith
    refine ⟨?_, fun v _ q => (hmarg v q).trans hM0⟩
    have hv0 : 0 < k := by omega
    have hN : bnd_N (bnd_w U Cs σ) S = ∑ x, U x *
        bnd_N (Function.update (bnd_w U Cs σ) ⟨0, hv0⟩ (bnd_del x)) S := by
      rw [bnd_N_update_sum]
      congr 1
      rw [hwU]
      exact (Function.update_eq_self _ _).symm
    rw [hN]
    calc ∑ x, U x * bnd_N (Function.update (bnd_w U Cs σ) ⟨0, hv0⟩ (bnd_del x)) S
        ≤ ∑ x, U x * (bnd_KB k Cs CU Kb * Ξ ^ (k - 2) * H ^ (k - 2)) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
            ((hmarg _ x).trans hM0) (hU0 x)
      _ = bnd_KB k Cs CU Kb * Ξ ^ (k - 2) * H ^ (k - 1) := by
          rw [← Finset.sum_mul, ← hH]
          have : H ^ (k - 1) = H * H ^ (k - 2) := by
            rw [← pow_succ']; congr 1; omega
          rw [this]; ring
  · -- a stable leg `s`
    push Not at halt
    obtain ⟨s, hs⟩ := halt
    have hss : σ s = σ (finRotate k s) := by
      cases h1 : σ s <;> cases h2 : σ (finRotate k s) <;> simp_all
    have hws : ∀ x, bnd_w U Cs σ s x = Cs := fun x => by unfold bnd_w; rw [ite_eq_left hss]
    have hrow : ∀ j, ∑ x, bnd_w U Cs σ j x ≤ 2 * Cs * H := by
      intro j
      unfold bnd_w
      split_ifs
      · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        nlinarith
      · nlinarith
    have hrow0 : ∀ j, 0 ≤ ∑ x, bnd_w U Cs σ j x := fun j => Finset.sum_nonneg fun x _ => hw0 j x
    have hCs0 : 0 ≤ Cs := by linarith
    have hfin : ∀ m : ℕ, m ≤ k → Cs * Kb * (2 * Cs * H) ^ m ≤
        bnd_KB k Cs CU Kb * Ξ ^ (k - 2) * H ^ m := by
      intro m hm
      rw [hKB, mul_pow]
      have h1 : (2 * Cs) ^ m ≤ (2 * Cs) ^ k := pow_le_pow_right₀ (by linarith) hm
      have hHm : 0 ≤ H ^ m := pow_nonneg hH0 m
      have h2 : Cs * Kb * ((2 * Cs) ^ m * H ^ m) ≤ Kb * (Cs * (2 * Cs) ^ k) * H ^ m := by
        have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hCs0 hKb)
        nlinarith
      refine h2.trans ?_
      have : Kb * (Cs * (2 * Cs) ^ k) ≤ (Kb * ((k : ℝ) ^ 2 * CU) + Kb * (Cs * (2 * Cs) ^ k)) *
          Ξ ^ (k - 2) := by nlinarith
      exact mul_le_mul_of_nonneg_right this hHm
    refine ⟨?_, fun v hv q => ?_⟩
    · refine (bnd_N_stableLeg S hsupp hS1 _ hw0 s hws).trans ?_
      refine le_trans ?_ (hfin (k - 1) (by omega))
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCs0 hKb)
      have := bnd_prod_le_pow (Finset.univ.erase s) (fun j => ∑ x, bnd_w U Cs σ j x) (2 * Cs * H)
        (fun j _ => hrow0 j) (fun j _ => hrow j)
      rwa [Finset.card_erase_of_mem (Finset.mem_univ s), Finset.card_univ,
        Fintype.card_fin] at this
    · have hvs : v ≠ s := fun h => hv (h ▸ hss)
      have hw0' := bnd_update_nonneg hw0 (bnd_del_nonneg q) (v := v)
      have hws' : ∀ x, Function.update (bnd_w U Cs σ) v (bnd_del q) s x = Cs := fun x => by
        rw [Function.update_of_ne hvs.symm, hws]
      refine (bnd_N_stableLeg S hsupp hS1 _ hw0' s hws').trans ?_
      refine le_trans ?_ (hfin (k - 2) (by omega))
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCs0 hKb)
      have hvmem : v ∈ Finset.univ.erase s := Finset.mem_erase.mpr ⟨hvs, Finset.mem_univ v⟩
      rw [← Finset.mul_prod_erase _ _ hvmem, Function.update_self]
      have h1 : ∑ x, bnd_del q x = 1 := by
        have := bnd_sum_del q (fun _ => 1); simpa using this
      rw [h1, one_mul]
      have := bnd_prod_le_pow ((Finset.univ.erase s).erase v)
        (fun j => ∑ x, Function.update (bnd_w U Cs σ) v (bnd_del q) j x) (2 * Cs * H)
        (fun j _ => Finset.sum_nonneg fun x _ => hw0' j x)
        (fun j hj => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
          exact hrow j)
      rwa [Finset.card_erase_of_mem hvmem, Finset.card_erase_of_mem (Finset.mem_univ s),
        Finset.card_univ, Fintype.card_fin, show k - 1 - 1 = k - 2 by omega] at this

end Base

/-! ## Induction along the molecule tree

The norms of the graded cores by induction on the length: the base is the stable molecule; a
mixed diagonal glues two shorter graded cores with the link `β t V_t`, whose multiplier is at
most `U`. -/

section Induct

variable {L : ℕ}

/-- The mixed link `β t V_t` as a complex matrix. -/
private lemma bnd_link_eq (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) {s s' : Bool}
    (h : s ≠ s') (a b : Fin L) :
    (((β * t : ℝ) : ℂ) • pairV β M t s s') a b =
      (((β * t : ℝ) : ℂ)) * (((1 - t • pairP β M)⁻¹ a b : ℝ) : ℂ) := by
  rw [bnd_pairV_mixed β M t h, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]

private lemma bnd_link_circ [NeZero L] (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ)
    (hVc : ∀ a a' c : Fin L, (1 - t • pairP β M)⁻¹ (a + c) (a' + c) = (1 - t • pairP β M)⁻¹ a a')
    {s s' : Bool} (h : s ≠ s') (a a' c : Fin L) :
    (((β * t : ℝ) : ℂ) • pairV β M t s s') (a + c) (a' + c) =
      (((β * t : ℝ) : ℂ) • pairV β M t s s') a a' := by
  rw [bnd_link_eq β M t h, bnd_link_eq β M t h, hVc]

private lemma bnd_link_hat [NeZero L] (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ)
    {U : Fin L → ℝ} (hβt0 : 0 ≤ β * t) (hβt1 : β * t ≤ 1)
    (hVhat : ∀ q, ‖∑ u, (((1 - t • pairP β M)⁻¹ 0 u : ℝ) : ℂ) * bnd_chi L q u‖ ≤ U q)
    {s s' : Bool} (h : s ≠ s') (q : Fin L) :
    ‖bnd_hat (((β * t : ℝ) : ℂ) • pairV β M t s s') q‖ ≤ U q ∧
      ‖bnd_hat (((β * t : ℝ) : ℂ) • pairV β M t s s') (-q)‖ ≤ U q := by
  set X := ((β * t : ℝ) : ℂ) • pairV β M t s s' with hX
  have h1 : bnd_hat X q = ((β * t : ℝ) : ℂ) *
      ∑ u, (((1 - t • pairP β M)⁻¹ 0 u : ℝ) : ℂ) * bnd_chi L q u := by
    unfold bnd_hat
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [hX, bnd_link_eq β M t h]
    ring
  have h2 : bnd_hat X (-q) = star (bnd_hat X q) := by
    unfold bnd_hat
    rw [star_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [star_mul', bnd_star_chi, ← bnd_chi_neg_left, hX, bnd_link_eq β M t h]
    congr 1
    simp [Complex.conj_ofReal]
  have h3 : ‖bnd_hat X q‖ ≤ U q := by
    rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hβt0]
    calc β * t * ‖∑ u, (((1 - t • pairP β M)⁻¹ 0 u : ℝ) : ℂ) * bnd_chi L q u‖
        ≤ 1 * U q := mul_le_mul hβt1 (hVhat q) (norm_nonneg _) zero_le_one
      _ = U q := one_mul _
  refine ⟨h3, ?_⟩
  rw [h2, norm_star]
  exact h3

/-- The leg weights of the polygon of Cut_L agree with those of the `k`-gon. -/
private lemma bnd_wL_eq {k : ℕ} {i j : Fin k} (hd : (i, j) ∈ polyDiags k) (U : Fin L → ℝ)
    (Cs : ℝ) (σ : Fin k → Bool) (p : Fin (k + i - j + 1)) (hp : p ≠ bnd_iL i j) :
    bnd_w U Cs σ (bnd_vL i j p) = bnd_w U Cs (cutLSgn σ i j) p := by
  have hp' : p.val ≠ i.val := fun h => hp (Fin.ext h)
  unfold bnd_w
  rw [bnd_cutLSgn_eq, bnd_cutLSgn_eq, bnd_vL_rot hd hp']

/-- The leg weights of the polygon of Cut_R agree with those of the `k`-gon. -/
private lemma bnd_wR_eq {k : ℕ} {i j : Fin k} (hd : (i, j) ∈ polyDiags k) (U : Fin L → ℝ)
    (Cs : ℝ) (σ : Fin k → Bool) (q : Fin (j - i + 1)) (hq : q ≠ bnd_lastR i j) :
    bnd_w U Cs σ (bnd_vR i j q) = bnd_w U Cs (cutRSgn σ i j) q := by
  have hq' : q.val ≠ j.val - i.val := fun h => hq (Fin.ext h)
  unfold bnd_w
  rw [bnd_cutRSgn_eq, bnd_cutRSgn_eq, bnd_vR_rot hd hq']

/-- The cut side of the polygon of Cut_L is mixed when `(i, j)` is. -/
private lemma bnd_wL_iL {k : ℕ} {i j : Fin k} (hd : (i, j) ∈ polyDiags k) (U : Fin L → ℝ)
    (Cs : ℝ) {σ : Fin k → Bool} (hmix : σ i ≠ σ j) :
    bnd_w U Cs (cutLSgn σ i j) (bnd_iL i j) = U ∧
      cutLSgn σ i j (bnd_iL i j) ≠ cutLSgn σ i j (finRotate _ (bnd_iL i j)) := by
  have hvi : bnd_vL i j (bnd_iL i j) = i := by
    apply Fin.ext; rw [bnd_vL_val]; simp [bnd_iL]
  have h : cutLSgn σ i j (bnd_iL i j) ≠ cutLSgn σ i j (finRotate _ (bnd_iL i j)) := by
    rw [bnd_cutLSgn_eq, bnd_cutLSgn_eq, hvi, bnd_vL_rot_iL hd]
    exact hmix
  refine ⟨?_, h⟩
  funext x
  unfold bnd_w
  rw [ite_eq_right h]

/-- The cut side of the polygon of Cut_R is mixed when `(i, j)` is. -/
private lemma bnd_wR_lastR {k : ℕ} {i j : Fin k} (hd : (i, j) ∈ polyDiags k) (U : Fin L → ℝ)
    (Cs : ℝ) {σ : Fin k → Bool} (hmix : σ i ≠ σ j) :
    bnd_w U Cs (cutRSgn σ i j) (bnd_lastR i j) = U ∧
      cutRSgn σ i j (bnd_lastR i j) ≠ cutRSgn σ i j (finRotate _ (bnd_lastR i j)) := by
  have hdv := (bnd_mem_polyDiags _).mp hd
  simp only at hdv
  have hvj : bnd_vR i j (bnd_lastR i j) = j := by
    apply Fin.ext; rw [bnd_vR_val]; simp only [bnd_lastR]; omega
  have h : cutRSgn σ i j (bnd_lastR i j) ≠ cutRSgn σ i j (finRotate _ (bnd_lastR i j)) := by
    rw [bnd_cutRSgn_eq, bnd_cutRSgn_eq, hvj, bnd_vR_rot_lastR hd]
    exact Ne.symm hmix
  refine ⟨?_, h⟩
  funext x
  unfold bnd_w
  rw [ite_eq_right h]

/-- The graded core of grade zero is the stable molecule. -/
lemma bnd_Cr_zero {k : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ)
    (σ : Fin k → Bool) : bnd_Cr β M t σ 0 = stableMol β M t σ := by
  funext y
  unfold bnd_Cr stableMol
  congr 1
  refine Finset.filter_congr fun F _ => ?_
  unfold bnd_cnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp

/-- There are at most `k²` mixed diagonals. -/
lemma bnd_Cr_big {k : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ)
    (σ : Fin k → Bool) {r : ℕ} (hr : k * k < r) : bnd_Cr β M t σ r = fun _ => 0 := by
  funext y
  unfold bnd_Cr
  refine Finset.sum_eq_zero fun F hF => ?_
  exfalso
  rw [Finset.mem_filter] at hF
  have h1 : bnd_cnt σ F ≤ F.card := Finset.card_filter_le _ _
  have h2 : F.card ≤ k * k := by
    have := Finset.card_le_univ F
    simpa [Fintype.card_prod, Fintype.card_fin] using this
  omega

/-- One mixed diagonal: the norm and the mixed-leg marginals of the glued tensor from those of
the two polygons (the gluing step of the proof of Proposition B.2 [ba:prop:primitive]). -/
lemma bnd_glue_one [NeZero L] {k : ℕ} {i j : Fin k} (hd : (i, j) ∈ polyDiags k)
    {σ : Fin k → Bool} (hmix : σ i ≠ σ j) (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ)
    {U : Fin L → ℝ} {Cs : ℝ} (hU0 : ∀ q, 0 ≤ U q) (hCs : 0 ≤ Cs) (hβt0 : 0 ≤ β * t)
    (hβt1 : β * t ≤ 1)
    (hVc : ∀ a a' c : Fin L, (1 - t • pairP β M)⁻¹ (a + c) (a' + c) = (1 - t • pairP β M)⁻¹ a a')
    (hVhat : ∀ q, ‖∑ u, (((1 - t • pairP β M)⁻¹ 0 u : ℝ) : ℂ) * bnd_chi L q u‖ ≤ U q)
    (A : (Fin (k + i - j + 1) → Fin L) → ℂ) (B : (Fin (j - i + 1) → Fin L) → ℂ) {aM bN bM : ℝ}
    (hAm : ∀ p, cutLSgn σ i j p ≠ cutLSgn σ i j (finRotate _ p) → ∀ q,
      bnd_N (Function.update (bnd_w U Cs (cutLSgn σ i j)) p (bnd_del q)) A ≤ aM)
    (hBN : bnd_N (bnd_w U Cs (cutRSgn σ i j)) B ≤ bN)
    (hBm : ∀ p, cutRSgn σ i j p ≠ cutRSgn σ i j (finRotate _ p) → ∀ q,
      bnd_N (Function.update (bnd_w U Cs (cutRSgn σ i j)) p (bnd_del q)) B ≤ bM) :
    bnd_N (bnd_w U Cs σ) (bnd_glueT i j (((β * t : ℝ) : ℂ) • pairV β M t (σ i) (σ j)) A B) ≤
        aM * bN ∧
      ∀ v, σ v ≠ σ (finRotate k v) → ∀ q,
        bnd_N (Function.update (bnd_w U Cs σ) v (bnd_del q))
          (bnd_glueT i j (((β * t : ℝ) : ℂ) • pairV β M t (σ i) (σ j)) A B) ≤ aM * bM := by
  set X := ((β * t : ℝ) : ℂ) • pairV β M t (σ i) (σ j) with hX
  have hXc := bnd_link_circ β M t hVc hmix
  have hXh := bnd_link_hat β M t hβt0 hβt1 hVhat (U := U) hmix
  obtain ⟨hwLi, hmixL⟩ := bnd_wL_iL hd U Cs hmix
  obtain ⟨hwRl, hmixR⟩ := bnd_wR_lastR hd U Cs hmix
  set w := bnd_w U Cs σ
  set wL := bnd_w U Cs (cutLSgn σ i j)
  set wR := bnd_w U Cs (cutRSgn σ i j)
  have hw0 : ∀ s x, 0 ≤ w s x := bnd_w_nonneg hU0 hCs σ
  have hwL0 : ∀ s x, 0 ≤ wL s x := bnd_w_nonneg hU0 hCs _
  have hwR0 : ∀ s x, 0 ≤ wR s x := bnd_w_nonneg hU0 hCs _
  have hL : ∀ p, p ≠ bnd_iL i j → w (bnd_vL i j p) = wL p := fun p hp => bnd_wL_eq hd U Cs σ p hp
  have hR : ∀ q, q ≠ bnd_lastR i j → w (bnd_vR i j q) = wR q :=
    fun q hq => bnd_wR_eq hd U Cs σ q hq
  refine ⟨?_, fun v hv q₀ => ?_⟩
  · refine (bnd_N_glue_left hd X hXc A B w wL wR hw0 hwL0 hwR0 hL hR
      (fun x => by rw [hwRl]; exact (hXh x).2) aM (hAm _ hmixL)).trans ?_
    have haM : 0 ≤ aM := le_trans (bnd_N_nonneg (bnd_update_nonneg hwL0 (bnd_del_nonneg 0)) A)
      (hAm _ hmixL 0)
    exact mul_le_mul_of_nonneg_left hBN haM
  · rcases bnd_side_cases hd v with ⟨p₀, hp₀, rfl⟩ | ⟨r₀, hr₀, rfl⟩
    · -- a leg of the polygon of Cut_L
      have hmixp : cutLSgn σ i j p₀ ≠ cutLSgn σ i j (finRotate _ p₀) := by
        intro h
        apply hv
        have hp' : p₀.val ≠ i.val := fun h' => hp₀ (Fin.ext h')
        rw [bnd_cutLSgn_eq, bnd_cutLSgn_eq, bnd_vL_rot hd hp'] at h
        exact h
      have hL' : ∀ p, p ≠ bnd_iL i j → Function.update w (bnd_vL i j p₀) (bnd_del q₀)
          (bnd_vL i j p) = Function.update wL p₀ (bnd_del q₀) p := by
        intro p hp
        by_cases hpp : p = p₀
        · subst hpp; simp
        · have hne : bnd_vL i j p ≠ bnd_vL i j p₀ := by
            have hdv := (bnd_mem_polyDiags _).mp hd
            simp only at hdv
            exact fun h => hpp (bnd_vL_inj (by omega) h)
          rw [Function.update_of_ne hne, Function.update_of_ne hpp, hL p hp]
      have hR' : ∀ q, q ≠ bnd_lastR i j → Function.update w (bnd_vL i j p₀) (bnd_del q₀)
          (bnd_vR i j q) = wR q := by
        intro q hq
        rw [Function.update_of_ne (Ne.symm (bnd_vL_ne_vR hd hp₀ hq)), hR q hq]
      have hXw : ∀ x, ‖bnd_hat X x‖ ≤ Function.update wL p₀ (bnd_del q₀) (bnd_iL i j) x := by
        intro x
        rw [Function.update_of_ne (Ne.symm hp₀), hwLi]
        exact (hXh x).1
      refine (bnd_N_glue_right hd X hXc A B _ _ wR (bnd_update_nonneg hw0 (bnd_del_nonneg q₀))
        (bnd_update_nonneg hwL0 (bnd_del_nonneg q₀)) hwR0 hL' hR' hXw bM (hBm _ hmixR)).trans ?_
      have hbM : 0 ≤ bM := le_trans (bnd_N_nonneg (bnd_update_nonneg hwR0 (bnd_del_nonneg 0)) B)
        (hBm _ hmixR 0)
      exact mul_le_mul_of_nonneg_right (hAm p₀ hmixp q₀) hbM
    · -- a leg of the polygon of Cut_R
      have hmixp : cutRSgn σ i j r₀ ≠ cutRSgn σ i j (finRotate _ r₀) := by
        intro h
        apply hv
        have hr' : r₀.val ≠ j.val - i.val := fun h' => hr₀ (Fin.ext h')
        rw [bnd_cutRSgn_eq, bnd_cutRSgn_eq, bnd_vR_rot hd hr'] at h
        exact h
      have hL' : ∀ p, p ≠ bnd_iL i j → Function.update w (bnd_vR i j r₀) (bnd_del q₀)
          (bnd_vL i j p) = wL p := by
        intro p hp
        rw [Function.update_of_ne (bnd_vL_ne_vR hd hp hr₀), hL p hp]
      have hR' : ∀ q, q ≠ bnd_lastR i j → Function.update w (bnd_vR i j r₀) (bnd_del q₀)
          (bnd_vR i j q) = Function.update wR r₀ (bnd_del q₀) q := by
        intro q hq
        by_cases hqq : q = r₀
        · subst hqq; simp
        · have hne : bnd_vR i j q ≠ bnd_vR i j r₀ := fun h => hqq (bnd_vR_inj h)
          rw [Function.update_of_ne hne, Function.update_of_ne hqq, hR q hq]
      have hXw : ∀ x, ‖bnd_hat X (-x)‖ ≤ Function.update wR r₀ (bnd_del q₀) (bnd_lastR i j) x := by
        intro x
        rw [Function.update_of_ne (Ne.symm hr₀), hwRl]
        exact (hXh x).2
      refine (bnd_N_glue_left hd X hXc A B _ wL _ (bnd_update_nonneg hw0 (bnd_del_nonneg q₀))
        hwL0 (bnd_update_nonneg hwR0 (bnd_del_nonneg q₀)) hL' hR' hXw aM (hAm _ hmixL)).trans ?_
      have haM : 0 ≤ aM := le_trans (bnd_N_nonneg (bnd_update_nonneg hwL0 (bnd_del_nonneg 0)) A)
        (hAm _ hmixL 0)
      exact mul_le_mul_of_nonneg_left (hBm r₀ hmixp q₀) haM

/-- The constants of the induction: `K_{n+1} = max(K_n, A_{n+1} + (n+1)⁴ K_n²)`. -/
def bnd_Kseq (A : ℕ → ℝ) : ℕ → ℝ
  | 0 => A 0
  | n + 1 => max (bnd_Kseq A n) (A (n + 1) + ((n + 1 : ℕ) : ℝ) ^ 4 * bnd_Kseq A n ^ 2)

lemma bnd_Kseq_mono (A : ℕ → ℝ) {m n : ℕ} (h : m ≤ n) : bnd_Kseq A m ≤ bnd_Kseq A n := by
  induction n with
  | zero => rw [Nat.le_zero.mp h]
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h' | h'
    · exact (ih (by omega)).trans (le_max_left _ _)
    · rw [show m = n + 1 by omega]

lemma bnd_Kseq_base (A : ℕ → ℝ) (n : ℕ) : A n ≤ bnd_Kseq A n := by
  cases n with
  | zero => exact le_rfl
  | succ n =>
    refine le_trans ?_ (le_max_right _ _)
    have : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ 4 * bnd_Kseq A n ^ 2 := by positivity
    linarith

lemma bnd_Kseq_step (A : ℕ → ℝ) (hA : ∀ n, 0 ≤ A n) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) ^ 4 * bnd_Kseq A n ^ 2 ≤ bnd_Kseq A (n + 1) := by
  refine le_trans ?_ (le_max_right _ _)
  linarith [hA (n + 1)]

lemma bnd_Kseq_nonneg (A : ℕ → ℝ) (hA : ∀ n, 0 ≤ A n) (n : ℕ) : 0 ≤ bnd_Kseq A n :=
  (hA n).trans (bnd_Kseq_base A n)

lemma bnd_N_zero {k : ℕ} (w : Fin k → Fin L → ℝ) : bnd_N w (fun _ => (0 : ℂ)) = 0 := by
  unfold bnd_N tensorFourier
  simp

/-- The norms of the graded cores, by induction on the length (Proposition B.2
[ba:prop:primitive], norms (B.4) [ba:eq:norms]). -/
private lemma bnd_induct [NeZero L] (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ)
    {U : Fin L → ℝ} {Cs CU Kb g δ : ℝ} (hU : ∀ q, 1 / 2 ≤ U q) (hCs : 1 ≤ Cs) (hKb : 0 ≤ Kb)
    (hg : 0 < g) (hδ : 0 ≤ δ) (hcoer : ∀ q, U q * (δ + g ^ 2 * torusAbs L q ^ 2) ≤ CU)
    (hβt0 : 0 ≤ β * t) (hβt1 : β * t ≤ 1)
    (hVc : ∀ a a' c : Fin L, (1 - t • pairP β M)⁻¹ (a + c) (a' + c) = (1 - t • pairP β M)⁻¹ a a')
    (hVhat : ∀ q, ‖∑ u, (((1 - t • pairP β M)⁻¹ 0 u : ℝ) : ℂ) * bnd_chi L q u‖ ≤ U q)
    (kmax : ℕ)
    (hST : ∀ (k : ℕ) (σ : Fin k → Bool) (y : Fin k → Fin L) (c : Fin L),
      stableMol β M t σ (fun i => y i + c) = stableMol β M t σ y)
    (hS1 : ∀ k, 3 ≤ k → k ≤ kmax → ∀ (σ : Fin k → Bool) n,
      ‖tensorFourier (stableMol β M t σ) n‖ ≤ Kb)
    (hS2 : ∀ k, 3 ≤ k → k ≤ kmax → ∀ σ : Fin k → Bool, (∀ i, σ (finRotate k i) = !σ i) →
      ∀ n, ∑ j, n j = 0 →
        ‖tensorFourier (stableMol β M t σ) n‖ ≤ Kb * (δ + ∑ j, torusAbs L (n j) ^ 2)) :
    ∀ k, 3 ≤ k → k ≤ kmax → ∀ (σ : Fin k → Bool) (r : ℕ),
      bnd_N (bnd_w U Cs σ) (bnd_Cr β M t σ r) ≤ bnd_Kseq (fun n => bnd_KB n Cs CU Kb) k *
          (1 + (g ^ 2)⁻¹) ^ (k - 2) * (∑ q, U q) ^ (k - 1) ∧
        ∀ v, σ v ≠ σ (finRotate k v) → ∀ q,
          bnd_N (Function.update (bnd_w U Cs σ) v (bnd_del q)) (bnd_Cr β M t σ r) ≤
            bnd_Kseq (fun n => bnd_KB n Cs CU Kb) k * (1 + (g ^ 2)⁻¹) ^ (k - 2) *
              (∑ q, U q) ^ (k - 2) := by
  set A : ℕ → ℝ := fun n => bnd_KB n Cs CU Kb with hA
  have hU0 : ∀ q, 0 ≤ U q := fun q => le_trans (by norm_num) (hU q)
  have hCU : 0 ≤ CU := le_trans (mul_nonneg (hU0 0) (by unfold torusAbs; positivity)) (hcoer 0)
  have hA0 : ∀ n, 0 ≤ A n := fun n => by
    simp only [hA, bnd_KB]
    have : 0 ≤ Cs := by linarith
    positivity
  set H := ∑ q, U q with hH
  have hH0 : 0 ≤ H := Finset.sum_nonneg fun q _ => hU0 q
  set Ξ := 1 + (g ^ 2)⁻¹ with hΞ
  have hΞ0 : 0 ≤ Ξ := by positivity
  have hCs0 : 0 ≤ Cs := by linarith
  have hw0 : ∀ {k : ℕ} (σ : Fin k → Bool) s x, 0 ≤ bnd_w U Cs σ s x :=
    fun σ => bnd_w_nonneg hU0 hCs0 σ
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  intro hk hkmax σ r
  have hK0 := bnd_Kseq_nonneg A hA0
  have hbound0 : ∀ m, 0 ≤ bnd_Kseq A k * Ξ ^ (k - 2) * H ^ m := fun m => by
    have := hK0 k; positivity
  -- grade zero: the stable molecule
  rcases Nat.eq_zero_or_pos r with hr0 | hr1
  · subst hr0
    rw [bnd_Cr_zero]
    obtain ⟨h1, h2⟩ := bnd_base hk (stableMol β M t σ) (hST k σ) σ hU hCs hKb hg hδ hcoer
      (hS1 k hk hkmax σ) (hS2 k hk hkmax σ)
    have hle : ∀ m, bnd_KB k Cs CU Kb * Ξ ^ (k - 2) * H ^ m ≤
        bnd_Kseq A k * Ξ ^ (k - 2) * H ^ m := fun m =>
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (bnd_Kseq_base A k)
        (by positivity)) (pow_nonneg hH0 _)
    exact ⟨h1.trans (hle _), fun v hv q => (h2 v hv q).trans (hle _)⟩
  -- grades beyond `k²` vanish
  rcases Nat.lt_or_ge (k * k) r with hbig | hsmall
  · rw [bnd_Cr_big β M t σ hbig]
    exact ⟨by rw [bnd_N_zero]; exact hbound0 _, fun _ _ _ => by rw [bnd_N_zero]; exact hbound0 _⟩
  -- the gluing step
  set K' := bnd_Kseq A (k - 1) with hK'
  have hK'0 : 0 ≤ K' := hK0 _
  set D := (polyDiags k).filter (fun d => σ d.1 ≠ σ d.2) with hD
  set T : (Fin k × Fin k) × ℕ → (Fin k → Fin L) → ℂ := fun x =>
    bnd_glueT x.1.1 x.1.2 (((β * t : ℝ) : ℂ) • pairV β M t (σ x.1.1) (σ x.1.2))
      (bnd_Cr β M t (cutLSgn σ x.1.1 x.1.2) x.2)
      (bnd_Cr β M t (cutRSgn σ x.1.1 x.1.2) (r - 1 - x.2)) with hT
  have hdom : ∀ n, ‖tensorFourier (bnd_Cr β M t σ r) n‖ ≤
      ∑ x ∈ D ×ˢ Finset.range r, ‖tensorFourier (T x) n‖ := by
    intro n
    have hrec := bnd_Cr_rec β M t σ r
    have h1 : (r : ℂ) * tensorFourier (bnd_Cr β M t σ r) n =
        ∑ d ∈ D, ∑ rL ∈ Finset.range r, tensorFourier (T (d, rL)) n := by
      rw [← bnd_tf_smul, funext hrec, bnd_tf_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [bnd_tf_sum]
    have h2 : ‖tensorFourier (bnd_Cr β M t σ r) n‖ ≤
        ‖(r : ℂ) * tensorFourier (bnd_Cr β M t σ r) n‖ := by
      rw [norm_mul, Complex.norm_natCast]
      have : (1 : ℝ) ≤ r := by exact_mod_cast hr1
      nlinarith [norm_nonneg (tensorFourier (bnd_Cr β M t σ r) n)]
    refine h2.trans ?_
    rw [h1, Finset.sum_product]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => norm_sum_le _ _)
  have hcard : ((D ×ˢ Finset.range r).card : ℝ) ≤ (k : ℝ) ^ 4 := by
    rw [Finset.card_product, Finset.card_range]
    have h1 : D.card ≤ k * k := by
      refine (Finset.card_filter_le _ _).trans ?_
      have := Finset.card_le_univ (polyDiags k)
      simpa [Fintype.card_prod, Fintype.card_fin] using this
    have h2 : D.card * r ≤ k ^ 4 := by
      calc D.card * r ≤ (k * k) * (k * k) := Nat.mul_le_mul h1 hsmall
        _ = k ^ 4 := by ring
    exact_mod_cast h2
  -- each glued term
  have hterm : ∀ x ∈ D ×ˢ Finset.range r,
      bnd_N (bnd_w U Cs σ) (T x) ≤ K' ^ 2 * Ξ ^ (k - 2) * H ^ (k - 1) ∧
        ∀ v, σ v ≠ σ (finRotate k v) → ∀ q,
          bnd_N (Function.update (bnd_w U Cs σ) v (bnd_del q)) (T x) ≤
            K' ^ 2 * Ξ ^ (k - 2) * H ^ (k - 2) := by
    rintro ⟨⟨i, j⟩, rL⟩ hx
    rw [Finset.mem_product, hD, Finset.mem_filter] at hx
    obtain ⟨⟨hd, hmix⟩, -⟩ := hx
    have hdv := (bnd_mem_polyDiags _).mp hd
    simp only at hdv hmix
    have hj := j.isLt
    have hkL3 : 3 ≤ k + (i : ℕ) - (j : ℕ) + 1 := by omega
    have hkLk : k + (i : ℕ) - (j : ℕ) + 1 < k := by omega
    have hkR3 : 3 ≤ (j : ℕ) - (i : ℕ) + 1 := by omega
    have hkRk : (j : ℕ) - (i : ℕ) + 1 < k := by omega
    obtain ⟨hLN, hLm⟩ := IH _ hkLk hkL3 (by omega) (cutLSgn σ i j) rL
    obtain ⟨hRN, hRm⟩ := IH _ hkRk hkR3 (by omega) (cutRSgn σ i j) (r - 1 - rL)
    have hKL : bnd_Kseq A (k + (i : ℕ) - (j : ℕ) + 1) ≤ K' := bnd_Kseq_mono A (by omega)
    have hKR : bnd_Kseq A ((j : ℕ) - (i : ℕ) + 1) ≤ K' := bnd_Kseq_mono A (by omega)
    have hmono : ∀ m e e', bnd_Kseq A m ≤ K' →
        bnd_Kseq A m * Ξ ^ e * H ^ e' ≤ K' * Ξ ^ e * H ^ e' := fun m e e' h =>
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (pow_nonneg hΞ0 _))
        (pow_nonneg hH0 _)
    obtain ⟨g1, g2⟩ := bnd_glue_one hd hmix β M t hU0 hCs0 hβt0 hβt1 hVc hVhat
      (bnd_Cr β M t (cutLSgn σ i j) rL) (bnd_Cr β M t (cutRSgn σ i j) (r - 1 - rL))
      (aM := K' * Ξ ^ (k + (i : ℕ) - (j : ℕ) + 1 - 2) * H ^ (k + (i : ℕ) - (j : ℕ) + 1 - 2))
      (bN := K' * Ξ ^ ((j : ℕ) - (i : ℕ) + 1 - 2) * H ^ ((j : ℕ) - (i : ℕ) + 1 - 1))
      (bM := K' * Ξ ^ ((j : ℕ) - (i : ℕ) + 1 - 2) * H ^ ((j : ℕ) - (i : ℕ) + 1 - 2))
      (fun p hp q => (hLm p hp q).trans (hmono _ _ _ hKL)) (hRN.trans (hmono _ _ _ hKR))
      (fun p hp q => (hRm p hp q).trans (hmono _ _ _ hKR))
    have e1 : K' * Ξ ^ (k + (i : ℕ) - (j : ℕ) + 1 - 2) * H ^ (k + (i : ℕ) - (j : ℕ) + 1 - 2) *
        (K' * Ξ ^ ((j : ℕ) - (i : ℕ) + 1 - 2) * H ^ ((j : ℕ) - (i : ℕ) + 1 - 1)) =
          K' ^ 2 * Ξ ^ (k - 2) * H ^ (k - 1) := by
      rw [show k - 2 = (k + (i : ℕ) - (j : ℕ) + 1 - 2) + ((j : ℕ) - (i : ℕ) + 1 - 2) by omega,
        show k - 1 = (k + (i : ℕ) - (j : ℕ) + 1 - 2) + ((j : ℕ) - (i : ℕ) + 1 - 1) by omega,
        pow_add, pow_add]
      ring
    have e2 : K' * Ξ ^ (k + (i : ℕ) - (j : ℕ) + 1 - 2) * H ^ (k + (i : ℕ) - (j : ℕ) + 1 - 2) *
        (K' * Ξ ^ ((j : ℕ) - (i : ℕ) + 1 - 2) * H ^ ((j : ℕ) - (i : ℕ) + 1 - 2)) =
          K' ^ 2 * Ξ ^ (k - 2) * H ^ (k - 2) := by
      rw [show k - 2 = (k + (i : ℕ) - (j : ℕ) + 1 - 2) + ((j : ℕ) - (i : ℕ) + 1 - 2) by omega,
        pow_add, pow_add]
      ring
    exact ⟨g1.trans e1.le, fun v hv q => (g2 v hv q).trans e2.le⟩
  have hfin : ∀ m, (k : ℝ) ^ 4 * (K' ^ 2 * Ξ ^ (k - 2) * H ^ m) ≤
      bnd_Kseq A k * Ξ ^ (k - 2) * H ^ m := by
    intro m
    have hstep := bnd_Kseq_step A hA0 (k - 1)
    rw [show k - 1 + 1 = k by omega] at hstep
    have : ((k : ℝ)) ^ 4 * K' ^ 2 ≤ bnd_Kseq A k := hstep
    have hp : 0 ≤ Ξ ^ (k - 2) * H ^ m := by positivity
    calc (k : ℝ) ^ 4 * (K' ^ 2 * Ξ ^ (k - 2) * H ^ m) = ((k : ℝ) ^ 4 * K' ^ 2) *
          (Ξ ^ (k - 2) * H ^ m) := by ring
      _ ≤ bnd_Kseq A k * (Ξ ^ (k - 2) * H ^ m) := mul_le_mul_of_nonneg_right this hp
      _ = _ := by ring
  have hsum : ∀ (w : Fin k → Fin L → ℝ), (∀ s x, 0 ≤ w s x) → ∀ m,
      (∀ x ∈ D ×ˢ Finset.range r, bnd_N w (T x) ≤ K' ^ 2 * Ξ ^ (k - 2) * H ^ m) →
      bnd_N w (bnd_Cr β M t σ r) ≤ bnd_Kseq A k * Ξ ^ (k - 2) * H ^ m := by
    intro w hw m hb
    refine (bnd_N_le_sum _ hw _ T hdom).trans ?_
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hb0 : 0 ≤ K' ^ 2 * Ξ ^ (k - 2) * H ^ m := by positivity
    exact (mul_le_mul_of_nonneg_right hcard hb0).trans (hfin m)
  exact ⟨hsum _ (hw0 σ) _ fun x hx => (hterm x hx).1,
    fun v hv q => hsum _ (bnd_update_nonneg (hw0 σ) (bnd_del_nonneg q)) _
      fun x hx => (hterm x hx).2 v hv q⟩

/-- The external dressing: the multiplier of the leg `j` is at most its weight. -/
lemma bnd_dress_w [NeZero L] (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ)
    {U : Fin L → ℝ} {Cs : ℝ}
    (hVc : ∀ a a' c : Fin L, (1 - t • pairP β M)⁻¹ (a + c) (a' + c) = (1 - t • pairP β M)⁻¹ a a')
    (hVhat : ∀ q, ‖∑ u, (((1 - t • pairP β M)⁻¹ 0 u : ℝ) : ℂ) * bnd_chi L q u‖ ≤ U q)
    (hrowS : ∀ (s : Bool) (a : Fin L), ∑ x, ‖pairV β M t s s a x‖ ≤ Cs)
    {k : ℕ} (σ : Fin k → Bool) (j : Fin k) (a q : Fin L) :
    ‖∑ x, pairV β M t (σ j) (σ (finRotate k j)) a x * bnd_chi L q (-x)‖ ≤ bnd_w U Cs σ j q := by
  unfold bnd_w
  split_ifs with h
  · rw [← h]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun x _ => ?_).trans (hrowS (σ j) a))
    rw [norm_mul, bnd_norm_chi, mul_one]
  · set V := (1 - t • pairP β M)⁻¹ with hV
    have hVc' : ∀ a a' c : Fin L, (V.map ((↑) : ℝ → ℂ)) (a + c) (a' + c) =
        (V.map ((↑) : ℝ → ℂ)) a a' := by
      intro a a' c
      simp only [Matrix.map_apply]
      rw [hVc]
    have h1 : ∑ x, pairV β M t (σ j) (σ (finRotate k j)) a x * bnd_chi L q (-x) =
        star (∑ x, (V a x : ℂ) * bnd_chi L q x) := by
      rw [star_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [bnd_pairV_mixed β M t h, Matrix.map_apply, star_mul', bnd_star_chi]
      simp [Complex.conj_ofReal, hV]
    have h2 := bnd_circ_chi (V.map ((↑) : ℝ → ℂ)) hVc' q a
    simp only [Matrix.map_apply] at h2
    rw [h1, norm_star, h2, norm_mul, bnd_norm_chi, one_mul]
    exact hVhat q

/-- The dissection sum of `F_k`, `k ≥ 3`, as the dressing of the sum of the graded cores. -/
lemma bnd_primF_eq {k : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (t : ℝ)
    (σ : Fin (k + 3) → Bool) (a : Fin (k + 3) → Fin L) :
    primF β M m t a σ = ∑ y, (∏ j, pairV β M t (σ j) (σ (finRotate (k + 3) j)) (a j) (y j)) *
      (fun y => ∑ r ∈ Finset.range ((k + 3) * (k + 3) + 1), bnd_Cr β M t σ r y) y := by
  change ∑ F ∈ dissections (k + 3), dissVal β M t σ F a = _
  unfold dissVal bnd_Cr
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.mul_sum]
  beta_reduce
  congr 1
  refine (Finset.sum_fiberwise_of_maps_to (g := bnd_cnt σ)
    (t := Finset.range ((k + 3) * (k + 3) + 1))
    (fun F hF => ?_) (fun F => dissCore β M t σ F y)).symm
  rw [Finset.mem_range]
  have h1 : bnd_cnt σ F ≤ F.card := Finset.card_filter_le _ _
  have h2 : F.card ≤ (k + 3) * (k + 3) := by
    have := Finset.card_le_univ F
    simpa [Fintype.card_prod, Fintype.card_fin] using this
  omega

/-- Proposition B.2 [ba:prop:primitive] for fixed data: `L^{k-1} |F_k| ≤ (k²+1) K_k Ξ_g^{k-2}
(Σ_q U(q))^{k-1}` for `3 ≤ k ≤ k_max`. -/
private lemma bnd_primF_bound [NeZero L] (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (t : ℝ)
    {U : Fin L → ℝ} {Cs CU Kb g δ : ℝ} (hU : ∀ q, 1 / 2 ≤ U q) (hCs : 1 ≤ Cs) (hKb : 0 ≤ Kb)
    (hg : 0 < g) (hδ : 0 ≤ δ) (hcoer : ∀ q, U q * (δ + g ^ 2 * torusAbs L q ^ 2) ≤ CU)
    (hβt0 : 0 ≤ β * t) (hβt1 : β * t ≤ 1)
    (hVc : ∀ a a' c : Fin L, (1 - t • pairP β M)⁻¹ (a + c) (a' + c) = (1 - t • pairP β M)⁻¹ a a')
    (hVhat : ∀ q, ‖∑ u, (((1 - t • pairP β M)⁻¹ 0 u : ℝ) : ℂ) * bnd_chi L q u‖ ≤ U q)
    (hrowS : ∀ (s : Bool) (a : Fin L), ∑ x, ‖pairV β M t s s a x‖ ≤ Cs)
    (kmax : ℕ)
    (hST : ∀ (k : ℕ) (σ : Fin k → Bool) (y : Fin k → Fin L) (c : Fin L),
      stableMol β M t σ (fun i => y i + c) = stableMol β M t σ y)
    (hS1 : ∀ k, 3 ≤ k → k ≤ kmax → ∀ (σ : Fin k → Bool) n,
      ‖tensorFourier (stableMol β M t σ) n‖ ≤ Kb)
    (hS2 : ∀ k, 3 ≤ k → k ≤ kmax → ∀ σ : Fin k → Bool, (∀ i, σ (finRotate k i) = !σ i) →
      ∀ n, ∑ j, n j = 0 →
        ‖tensorFourier (stableMol β M t σ) n‖ ≤ Kb * (δ + ∑ j, torusAbs L (n j) ^ 2))
    (k : ℕ) (hk : 3 ≤ k) (hkmax : k ≤ kmax) (σ : Fin k → Bool) (a : Fin k → Fin L) :
    (L : ℝ) ^ (k - 1) * ‖primF β M m t a σ‖ ≤ ((k * k + 1 : ℕ) : ℝ) *
      bnd_Kseq (fun n => bnd_KB n Cs CU Kb) k * (1 + (g ^ 2)⁻¹) ^ (k - 2) *
        (∑ q, U q) ^ (k - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
  have hU0 : ∀ q, 0 ≤ U q := fun q => le_trans (by norm_num) (hU q)
  have hw0 := bnd_w_nonneg hU0 (by linarith : (0 : ℝ) ≤ Cs) σ
  rw [bnd_primF_eq]
  refine (bnd_dress (by omega) _ _ (bnd_w U Cs σ) (fun j a' q => bnd_dress_w β M t hVc hVhat
    hrowS σ j a' q) a).trans ?_
  have hind := bnd_induct β M t hU hCs hKb hg hδ hcoer hβt0 hβt1 hVc hVhat kmax hST hS1 hS2
    (n + 3) hk hkmax σ
  refine (bnd_N_le_sum (Finset.range ((n + 3) * (n + 3) + 1)) hw0 _ (fun r => bnd_Cr β M t σ r)
    (fun x => by
      rw [bnd_tf_sum]
      exact norm_sum_le _ _)).trans ?_
  refine (Finset.sum_le_sum fun r _ => (hind r).1).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring_nf
  exact le_rfl

end Induct

/-! ## The model at bounded coupling

The data `(γ_g, M_B(g, E), m)` of a root of (5.2) [fo:eq:dyson-family] satisfy the hypotheses
of the induction, with `U(q) = (1 - t kerSymbol P q)⁻¹` and the constants of Lemma A.5
[ba:lem:kernels], Lemma 6.1 [da:lem:scales-propagators] and Lemma B.1 [ba:lem:moment]. -/

section Model

variable {L : ℕ}

lemma bnd_gamma_pos (g : ℝ) : 0 < gammaG g := by
  unfold gammaG; positivity

lemma bnd_gamma_le_one (g : ℝ) : gammaG g ≤ 1 := by
  unfold gammaG
  have h : (1 : ℝ) ≤ (max 1 g) ^ 2 := one_le_pow₀ (le_max_left _ _)
  exact inv_le_one_of_one_le₀ h

/-- `U(q) = (1 - t P̂(q))⁻¹` of the model. -/
def bnd_U (g : ℝ) (L : ℕ) (E : ℝ) (m : ℂ) (t : ℝ) (q : Fin L) : ℝ :=
  (1 - t * kerSymbol (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) q)⁻¹

private lemma bnd_model_Pcirc [NeZero L] (g E : ℝ) (m : ℂ) (a a' c : Fin L) :
    pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) (a + c) (a' + c) =
      pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) a a' :=
  bnd_pairP_add (fun a a' c => bnd_dysonMat_add _ _ _ _ a a' c) a a' c

private lemma bnd_model_P0 (g E : ℝ) (m : ℂ) (a b : Fin L) :
    0 ≤ pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) a b := by
  unfold pairP
  simp only [Matrix.of_apply]
  exact mul_nonneg (bnd_gamma_pos g).le (sq_nonneg _)

/-- The model data satisfy the kernel hypotheses of the induction. -/
lemma bnd_model [NeZero L] (g : ℝ) (hL : 3 ≤ L) (E : ℝ) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (∀ q, 1 / 2 ≤ bnd_U g L E m t q) ∧
    (0 ≤ gammaG g * t ∧ gammaG g * t ≤ 1) ∧
    (∀ a a' c : Fin L,
      (1 - t • pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))⁻¹ (a + c) (a' + c) =
        (1 - t • pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))⁻¹ a a') ∧
    (∀ q, ‖∑ u, (((1 - t • pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))⁻¹ 0 u : ℝ) :
      ℂ) * bnd_chi L q u‖ ≤ bnd_U g L E m t q) ∧
    (∀ (k : ℕ) (σ : Fin k → Bool) (y : Fin k → Fin L) (c : Fin L),
      stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ (fun i => y i + c) =
        stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ y) := by
  set P := pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) with hP
  have hD := primData_of_root g L hL E m hm
  have hPc : ∀ a a' c : Fin L, P (a + c) (a' + c) = P a a' := bnd_model_Pcirc g E m
  have hP0 : ∀ a b, 0 ≤ P a b := bnd_model_P0 g E m
  have hrow : ∀ a, ∑ b, P a b = 1 := hD.row_sum
  have hγ0 := bnd_gamma_pos g
  have hγ1 := bnd_gamma_le_one g
  refine ⟨fun q => ?_, ⟨by positivity, by nlinarith⟩, bnd_inv_add hPc t,
    bnd_mult_le hPc hP0 hrow ht0 ht1, fun k σ y c => (stableMol_symm g L hL E m hm t σ y c).1⟩
  have habs := bnd_symbol_abs_le hP0 hrow q
  have h1 : 0 < 1 - t * kerSymbol P q := by
    have := (abs_le.mp habs).2; nlinarith
  have h2 : 1 - t * kerSymbol P q ≤ 2 := by
    have := (abs_le.mp habs).1; nlinarith
  unfold bnd_U
  rw [← hP, le_inv_comm₀ (by norm_num) h1]
  linarith

/-- The transform of a tensor whose anchored rows are bounded by `C'` is bounded by `C'`. -/
lemma bnd_tf_le_rows [NeZero L] {k : ℕ} (hk : 1 ≤ k) (S : (Fin k → Fin L) → ℂ) {C' : ℝ}
    (h : ∀ b : Fin L, ∑ y ∈ Finset.univ.filter (fun y : Fin k → Fin L => y ⟨0, hk⟩ = b),
      ‖S y‖ ≤ C') (n : Fin k → Fin L) : ‖tensorFourier S n‖ ≤ C' := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  rw [bnd_tf_eq, norm_mul, norm_inv, Complex.norm_natCast]
  have h1 : ‖∑ x, S x * ∏ j, bnd_chi L (n j) (x j)‖ ≤ ∑ x, ‖S x‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [norm_mul, norm_prod]
    simp [bnd_norm_chi]
  have h2 : ∑ x, ‖S x‖ ≤ L * C' := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun y : Fin k → Fin L => y ⟨0, hk⟩)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    calc ∑ b : Fin L, ∑ y ∈ Finset.univ.filter (fun y : Fin k → Fin L => y ⟨0, hk⟩ = b), ‖S y‖
        ≤ ∑ b : Fin L, C' := Finset.sum_le_sum fun b _ => h b
      _ = L * C' := by simp
  rw [inv_mul_le_iff₀ hL]
  exact h1.trans h2

/-- Proposition B.2 [ba:prop:primitive] for `F_k = W^{k-1} 𝒦_k`, `3 ≤ k ≤ k_max`:
`|F_k| ≤ K Ξ_g^{k-2} ((1-t)ℓ_t)^{-(k-1)}` on `0 < g ≤ C`. -/
private lemma bnd_propB2 (C B₀ c' : ℝ) (hC : 0 < C) (hB₀ : 0 < B₀) (hc' : 0 < c') (kmax : ℕ) :
    ∃ K : ℝ, ∃ L₀ : ℕ, 0 < K ∧ ∀ g : ℝ, 0 < g → g ≤ C → ∀ L : ℕ, 3 ≤ L → L₀ ≤ L →
      ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m → c' ≤ m.im →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ k : ℕ, 3 ≤ k → k ≤ kmax →
      ∀ (a : Fin k → Fin L) (σ : Fin k → Bool),
        ‖primLoopF g L E m t a σ‖ ≤
          K * (1 + (g ^ 2)⁻¹) ^ (k - 2) * ((1 - t) * ellProp g L t)⁻¹ ^ (k - 1) := by
  obtain ⟨cs, Csym, Ls, hcs, hCsym, Hs⟩ := bdd_symbol C B₀ c' hC hB₀ hc'
  obtain ⟨cp, Cp, Lp, hcp, hCp, Hp⟩ := scalesProp_bdd C B₀ c' hC hB₀ hc'
  have h1 : ∀ k : ℕ, ∃ C1 : ℝ, ∃ L1 : ℕ, 0 ≤ C1 ∧ (3 ≤ k → ∀ g : ℝ, 0 ≤ g → g ≤ C →
      ∀ L : ℕ, 3 ≤ L → L1 ≤ L → ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ,
      IsDysonRootV (hopB g) (gammaG g) L E m → c' ≤ m.im → ∀ t : ℝ, 0 ≤ t → t < 1 →
      ∀ (σ : Fin k → Bool) (n : Fin k → Fin L),
        ‖tensorFourier (stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ) n‖ ≤
          C1) := by
    intro k
    by_cases hk : 3 ≤ k
    · obtain ⟨c, C', L₀, hc, hC', H⟩ := stableMol_bdd C B₀ c' hC hB₀ hc' k 0 hk
      refine ⟨C', L₀, hC'.le, fun _ g hg hgC L hL hL₀ E hE m hm hcm t ht0 ht1 σ n => ?_⟩
      have : NeZero L := ⟨by omega⟩
      refine bnd_tf_le_rows (by omega) _ (fun b => ?_) n
      refine le_trans (Finset.sum_le_sum fun y _ => ?_)
        (H g hg hgC L hL hL₀ E hE m hm hcm t ht0 ht1.le σ ⟨0, by omega⟩ b).1
      have : 1 ≤ Real.exp (c * wordDiam y) := Real.one_le_exp (by positivity)
      nlinarith [norm_nonneg (stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ y)]
    · exact ⟨0, 0, le_rfl, fun h => absurd h hk⟩
  have h2 : ∀ k : ℕ, ∃ C2 : ℝ, ∃ L2 : ℕ, 0 ≤ C2 ∧ (4 ≤ k → ∀ g : ℝ, 0 ≤ g → g ≤ C →
      ∀ L : ℕ, 3 ≤ L → L2 ≤ L → ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ,
      IsDysonRootV (hopB g) (gammaG g) L E m → c' ≤ m.im → ∀ t : ℝ, 0 ≤ t → t < 1 →
      ∀ σ : Fin k → Bool, (∀ i, σ (finRotate k i) = !σ i) →
      ∀ n : Fin k → Fin L, (∑ j, (n j : ℕ)) % L = 0 →
        ‖tensorFourier (stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ) n‖ ≤
          C2 * ((1 - t) + ∑ j, torusAbs L (n j) ^ 2)) := by
    intro k
    by_cases hk : 4 ≤ k
    · obtain ⟨C', L₀, hC', H⟩ := stableMol_bdd_cancel C B₀ c' hC hB₀ hc' k hk
      exact ⟨C', L₀, hC'.le, fun _ => H⟩
    · exact ⟨0, 0, le_rfl, fun h => absurd h hk⟩
  choose C1 L1 hC1 H1 using h1
  choose C2 L2 hC2 H2 using h2
  set Kb : ℝ := ∑ k ∈ Finset.range (kmax + 1), (C1 k + C2 k) with hKb
  have hKb0 : 0 ≤ Kb := Finset.sum_nonneg fun k _ => add_nonneg (hC1 k) (hC2 k)
  have hC1K : ∀ k, k ≤ kmax → C1 k ≤ Kb := fun k hk => by
    have := Finset.single_le_sum (f := fun k => C1 k + C2 k)
      (fun k _ => add_nonneg (hC1 k) (hC2 k)) (Finset.mem_range.mpr (by omega : k < kmax + 1))
    linarith [hC2 k]
  have hC2K : ∀ k, k ≤ kmax → C2 k ≤ Kb := fun k hk => by
    have := Finset.single_le_sum (f := fun k => C1 k + C2 k)
      (fun k _ => add_nonneg (hC1 k) (hC2 k)) (Finset.mem_range.mpr (by omega : k < kmax + 1))
    linarith [hC1 k]
  set L₀ : ℕ := Ls + Lp + ∑ k ∈ Finset.range (kmax + 1), (L1 k + L2 k) with hL₀
  have hL1K : ∀ k, k ≤ kmax → L1 k ≤ L₀ := fun k hk => by
    have := Finset.single_le_sum (f := fun k => L1 k + L2 k) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega : k < kmax + 1))
    omega
  have hL2K : ∀ k, k ≤ kmax → L2 k ≤ L₀ := fun k hk => by
    have := Finset.single_le_sum (f := fun k => L1 k + L2 k) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega : k < kmax + 1))
    omega
  set Cs : ℝ := max Cp 1 with hCs
  set Kq : ℝ := bnd_Kseq (fun n => bnd_KB n Cs Csym Kb) kmax with hKq
  set K : ℝ := ((kmax * kmax + 1 : ℕ) : ℝ) * Kq * (max Csym 1) ^ kmax + 1 with hK
  have hA0 : ∀ n, 0 ≤ bnd_KB n Cs Csym Kb := fun n => by
    unfold bnd_KB
    have : 0 ≤ Cs := le_trans zero_le_one (le_max_right _ _)
    positivity
  have hKq0 : 0 ≤ Kq := bnd_Kseq_nonneg _ hA0 kmax
  refine ⟨K, L₀, by positivity, ?_⟩
  intro g hg hgC L hL hLL₀ E hE m hm hcm t ht0 ht1 k hk hkmax a σ
  have : NeZero L := ⟨by omega⟩
  have hLs : Ls ≤ L := by omega
  have hLp : Lp ≤ L := by omega
  obtain ⟨hU, ⟨hβt0, hβt1⟩, hVc, hVhat, hST⟩ := bnd_model g hL E m hm ht0 ht1
  obtain ⟨-, Hs2⟩ := Hs g hg.le hgC L hL hLs E hE m hm hcm
  obtain ⟨Hcoer, Havg⟩ := Hs2 t ht0 ht1
  obtain ⟨-, -, -, Hrow, -⟩ := Hp g hg.le hgC L hL hLp E hE m hm hcm
  have hδ : 0 < 1 - t := by linarith
  have hcoer : ∀ q, bnd_U g L E m t q * ((1 - t) + g ^ 2 * torusAbs L q ^ 2) ≤ Csym := by
    intro q
    have h := (Hcoer q).2
    have hpos : 0 < (1 - t) + g ^ 2 * torusAbs L q ^ 2 := by positivity
    unfold bnd_U
    rwa [le_div_iff₀ hpos] at h
  have hrowS : ∀ (s : Bool) (a : Fin L),
      ∑ x, ‖pairV (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t s s a x‖ ≤ Cs := by
    intro s a
    have h := Hrow t ht0 ht1.le a
    refine le_trans ?_ (h.trans (le_max_left _ _))
    cases s <;> simp [pairV, Matrix.map_apply]
  have hS1 : ∀ k, 3 ≤ k → k ≤ kmax → ∀ (σ : Fin k → Bool) n,
      ‖tensorFourier (stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ) n‖ ≤ Kb :=
    fun k hk hkm σ n => (H1 k hk g hg.le hgC L hL (by linarith [hL1K k hkm]) E hE m hm hcm t
      ht0 ht1 σ n).trans (hC1K k hkm)
  have hS2 : ∀ k, 3 ≤ k → k ≤ kmax → ∀ σ : Fin k → Bool, (∀ i, σ (finRotate k i) = !σ i) →
      ∀ n, ∑ j, n j = 0 →
        ‖tensorFourier (stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ) n‖ ≤
          Kb * ((1 - t) + ∑ j, torusAbs L (n j) ^ 2) := by
    intro k hk hkm σ halt n hn
    rcases Nat.lt_or_ge k 4 with h3 | h4
    · exfalso
      have hk3 : k = 3 := by omega
      subst hk3
      have e0 := halt 0
      have e1 := halt 1
      have e2 := halt 2
      have r0 : finRotate 3 0 = 1 := by decide
      have r1 : finRotate 3 1 = 2 := by decide
      have r2 : finRotate 3 2 = 0 := by decide
      rw [r0] at e0; rw [r1] at e1; rw [r2] at e2
      cases h : σ 0 <;> simp_all
    · have hn' : (∑ j, (n j : ℕ)) % L = 0 := by
        rw [← bnd_val_sum, hn, Fin.val_zero]
      have hX : 0 ≤ (1 - t) + ∑ j, torusAbs L (n j) ^ 2 :=
        add_nonneg hδ.le (Finset.sum_nonneg fun j _ => sq_nonneg _)
      exact (H2 k h4 g hg.le hgC L hL (by linarith [hL2K k hkm]) E hE m hm hcm t ht0 ht1 σ halt
        n hn').trans (mul_le_mul_of_nonneg_right (hC2K k hkm) hX)
  have hmain := bnd_primF_bound (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) m t hU
    (le_max_right Cp 1) hKb0 hg hδ.le hcoer hβt0 hβt1 hVc hVhat hrowS kmax hST hS1 hS2 k hk hkmax
    σ a
  -- the average of `U`
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hell : 0 < ellProp g L t := by
    have := (scale_facts g hg.le 1 L le_rfl (by omega) t t ht0 le_rfl ht1).1
    linarith
  have havg : ∑ q, bnd_U g L E m t q ≤ L * (Csym * ((1 - t) * ellProp g L t)⁻¹) := by
    obtain ⟨he, -, hle⟩ := Havg ⟨0, by omega⟩
    have : (L : ℝ)⁻¹ * ∑ q, bnd_U g L E m t q ≤ Csym / ((1 - t) * ellProp g L t) := by
      unfold bnd_U; rw [he]; exact hle
    rw [inv_mul_le_iff₀ hLpos] at this
    rwa [div_eq_mul_inv] at this
  set Ξ := 1 + (g ^ 2)⁻¹ with hΞ
  have hΞ0 : 0 ≤ Ξ := by positivity
  set R := ((1 - t) * ellProp g L t)⁻¹ with hR
  have hR0 : 0 ≤ R := by positivity
  have hU0 : 0 ≤ ∑ q, bnd_U g L E m t q :=
    Finset.sum_nonneg fun q _ => le_trans (by norm_num) (hU q)
  have hKk : bnd_Kseq (fun n => bnd_KB n Cs Csym Kb) k ≤ Kq := bnd_Kseq_mono _ hkmax
  have hKk0 : 0 ≤ bnd_Kseq (fun n => bnd_KB n Cs Csym Kb) k := bnd_Kseq_nonneg _ hA0 k
  have hkk : ((k * k + 1 : ℕ) : ℝ) ≤ ((kmax * kmax + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul hkmax hkmax) 1
  have hCpow : Csym ^ (k - 1) ≤ (max Csym 1) ^ kmax := by
    calc Csym ^ (k - 1) ≤ (max Csym 1) ^ (k - 1) :=
          pow_le_pow_left₀ hCsym.le (le_max_left _ _) _
      _ ≤ (max Csym 1) ^ kmax := pow_le_pow_right₀ (le_max_right _ _) (by omega)
  have hLk : (0 : ℝ) < (L : ℝ) ^ (k - 1) := by positivity
  have hstep : (L : ℝ) ^ (k - 1) * ‖primLoopF g L E m t a σ‖ ≤
      (L : ℝ) ^ (k - 1) * (((kmax * kmax + 1 : ℕ) : ℝ) * Kq * (max Csym 1) ^ kmax * Ξ ^ (k - 2) *
        R ^ (k - 1)) := by
    refine hmain.trans ?_
    have hpow : (∑ q, bnd_U g L E m t q) ^ (k - 1) ≤ (L : ℝ) ^ (k - 1) * (Csym ^ (k - 1) *
        R ^ (k - 1)) := by
      rw [← mul_pow, ← mul_pow]
      exact pow_le_pow_left₀ hU0 havg _
    calc ((k * k + 1 : ℕ) : ℝ) * bnd_Kseq (fun n => bnd_KB n Cs Csym Kb) k * Ξ ^ (k - 2) *
          (∑ q, bnd_U g L E m t q) ^ (k - 1)
        ≤ ((k * k + 1 : ℕ) : ℝ) * bnd_Kseq (fun n => bnd_KB n Cs Csym Kb) k * Ξ ^ (k - 2) *
          ((L : ℝ) ^ (k - 1) * (Csym ^ (k - 1) * R ^ (k - 1))) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ ((kmax * kmax + 1 : ℕ) : ℝ) * Kq * Ξ ^ (k - 2) *
          ((L : ℝ) ^ (k - 1) * ((max Csym 1) ^ kmax * R ^ (k - 1))) := by
          gcongr
      _ = _ := by ring
  have hfin := le_of_mul_le_mul_left hstep hLk
  refine hfin.trans ?_
  gcongr
  linarith

/-- `(1 - t) ℓ_t ≤ 1 + g max{1, g}`. -/
private lemma bnd_ell_le (g : ℝ) (hg : 0 ≤ g) (L : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (1 - t) * ellProp g L t ≤ 1 + g * max 1 g := by
  have hM : (1 : ℝ) ≤ max 1 g := le_max_left _ _
  have hM0 : 0 < max 1 g := by linarith
  have hδ : 0 < 1 - t := by linarith
  set s := Real.sqrt (1 - t) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hδ
  have hs2 : s ^ 2 = 1 - t := Real.sq_sqrt hδ.le
  have hs1 : s ≤ 1 := by nlinarith [sq_nonneg (s - 1)]
  have hsq : Real.sqrt (gammaG g * (1 - t)) = s / max 1 g := by
    rw [Real.sqrt_mul (bnd_gamma_pos g).le, ← hs]
    unfold gammaG
    rw [Real.sqrt_inv, Real.sqrt_sq hM0.le]
    field_simp
  have hell : ellProp g L t ≤ 1 + g / Real.sqrt (gammaG g * (1 - t)) := min_le_right _ _
  calc (1 - t) * ellProp g L t ≤ (1 - t) * (1 + g / Real.sqrt (gammaG g * (1 - t))) :=
        mul_le_mul_of_nonneg_left hell hδ.le
    _ = (1 - t) + g * max 1 g * s := by
        rw [hsq, ← hs2]
        field_simp
    _ ≤ 1 + g * max 1 g := by
        have : 0 ≤ g * max 1 g := by positivity
        nlinarith

/-- `ζ_t = (γ_g W (1-t) ℓ_t)⁻¹`. -/
lemma bnd_zeta_eq (g : ℝ) (W L : ℕ) (t : ℝ) :
    zetaProp g W L t = (W : ℝ)⁻¹ * (gammaG g)⁻¹ * ((1 - t) * ellProp g L t)⁻¹ := by
  unfold zetaProp
  rw [mul_inv, mul_inv, mul_inv, mul_inv]
  ring

/-- `‖𝒦_k‖ = W^{1-k} ‖F_k‖`. -/
lemma bnd_norm_primLoop (g : ℝ) (W L : ℕ) (E : ℝ) (m : ℂ) (t : ℝ) {k : ℕ}
    (hk : 1 ≤ k) (a : Fin k → Fin L) (σ : Fin k → Bool) :
    ‖primLoop g W L E m t a σ‖ = ((W : ℝ)⁻¹) ^ (k - 1) * ‖primLoopF g L E m t a σ‖ := by
  have h : primLoop g W L E m t a σ = (W : ℂ) ^ (1 - (k : ℤ)) * primLoopF g L E m t a σ := rfl
  rw [h, norm_mul, norm_zpow, Complex.norm_natCast]
  congr 1
  rw [show (1 - (k : ℤ)) = -((k - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, inv_pow]

/-- The pair kernels at bounded coupling: `|F_2| ≤ C ((1-t)ℓ_t)⁻¹`. -/
private lemma bnd_two (C B₀ c' : ℝ) (hC : 0 < C) (hB₀ : 0 < B₀) (hc' : 0 < c') :
    ∃ C₂ : ℝ, ∃ L₀ : ℕ, 0 < C₂ ∧ ∀ g : ℝ, 0 ≤ g → g ≤ C → ∀ L : ℕ, 3 ≤ L → L₀ ≤ L →
      ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m → c' ≤ m.im →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (a : Fin 2 → Fin L) (σ : Fin 2 → Bool),
        ‖primLoopF g L E m t a σ‖ ≤ C₂ * (gammaG g)⁻¹ * ((1 - t) * ellProp g L t)⁻¹ := by
  obtain ⟨cp, Cp, Lp, hcp, hCp, Hp⟩ := scalesProp_bdd C B₀ c' hC hB₀ hc'
  set Cℓ : ℝ := 1 + C * max 1 C with hCℓ
  have hCℓ : 1 ≤ Cℓ := by
    have : 0 ≤ C * max 1 C := by positivity
    linarith
  refine ⟨Cp * Cℓ, Lp, by positivity, ?_⟩
  intro g hg hgC L hL hLp E hE m hm hcm t ht0 ht1 a σ
  have hD := primData_of_root g L hL E m hm
  obtain ⟨-, -, -, Hrow, Hmix⟩ := Hp g hg hgC L hL hLp E hE m hm hcm
  set M := dysonMat (hopB g) (gammaG g) L E m with hM
  set P := pairP (gammaG g) M with hP
  have hγ0 := bnd_gamma_pos g
  have hδ : 0 < 1 - t := by linarith
  have hell0 : 0 < ellProp g L t := by
    have := (scale_facts g hg 1 L le_rfl (by omega) t t ht0 le_rfl ht1).1
    linarith
  set R := ((1 - t) * ellProp g L t)⁻¹ with hR
  have hR0 : 0 < R := by positivity
  have hRℓ : 1 ≤ Cℓ * R := by
    have h1 := bnd_ell_le g hg L ht0 ht1
    have h2 : 1 + g * max 1 g ≤ Cℓ := by
      have : g * max 1 g ≤ C * max 1 C :=
        mul_le_mul hgC (max_le_max le_rfl hgC) (by positivity) hC.le
      linarith
    rw [hR, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
    linarith
  have hF : primLoopF g L E m t a σ = ((gammaG g : ℝ) : ℂ)⁻¹ *
      pairK (gammaG g) M t (σ 0) (σ 1) (a 0) (a 1) := rfl
  rw [hF, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hγ0]
  have hK : ‖pairK (gammaG g) M t (σ 0) (σ 1) (a 0) (a 1)‖ ≤ Cp * Cℓ * R := by
    by_cases hs : σ 0 = σ 1
    · -- equal signs: `|Q (I - tQ)⁻¹| ≤ C_p`
      have hQV : ∀ x y : Fin L, ‖(pairQ (gammaG g) M * (1 - (t : ℂ) • pairQ (gammaG g) M)⁻¹) x y‖
          ≤ Cp := by
        intro x y
        rw [Matrix.mul_apply]
        refine (norm_sum_le _ _).trans ?_
        have hQ : ∀ c, ‖pairQ (gammaG g) M x c‖ = P x c := by
          intro c
          simp only [pairQ, hP, pairP, Matrix.of_apply, norm_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hγ0, norm_pow]
        have hV : ∀ c, ‖(1 - (t : ℂ) • pairQ (gammaG g) M)⁻¹ c y‖ ≤ Cp := by
          intro c
          refine le_trans ?_ (Hrow t ht0 ht1.le c)
          exact Finset.single_le_sum (f := fun b => ‖(1 - (t : ℂ) • pairQ (gammaG g) M)⁻¹ c b‖)
            (fun b _ => norm_nonneg _) (Finset.mem_univ y)
        calc ∑ c, ‖pairQ (gammaG g) M x c * (1 - (t : ℂ) • pairQ (gammaG g) M)⁻¹ c y‖
            ≤ ∑ c, P x c * Cp := Finset.sum_le_sum fun c _ => by
              rw [norm_mul, hQ]
              exact mul_le_mul_of_nonneg_left (hV c) (bnd_model_P0 g E m x c)
          _ = Cp := by rw [← Finset.sum_mul, hD.row_sum, one_mul]
      have h1 : ‖pairK (gammaG g) M t (σ 0) (σ 1) (a 0) (a 1)‖ ≤ Cp := by
        unfold pairK
        rw [ite_eq_left hs]
        split_ifs
        · exact hQV _ _
        · rw [Matrix.map_apply, norm_star]; exact hQV _ _
      calc ‖pairK (gammaG g) M t (σ 0) (σ 1) (a 0) (a 1)‖ ≤ Cp * 1 := by rw [mul_one]; exact h1
        _ ≤ Cp * (Cℓ * R) := mul_le_mul_of_nonneg_left hRℓ hCp.le
        _ = Cp * Cℓ * R := by ring
    · -- opposite signs: the mixed kernel
      have h1 : pairK (gammaG g) M t (σ 0) (σ 1) (a 0) (a 1) = (mixedKer P t (a 0) (a 1) : ℂ) := by
        unfold pairK
        rw [ite_eq_right hs, Matrix.map_apply]
      obtain ⟨h0, hle⟩ := Hmix t ht0 ht1 (a 0) (a 1)
      rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
      have hexp : Real.exp (-(cp * cycDist (a 0) (a 1) / ellProp g L t)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by
          have : 0 ≤ cp * cycDist (a 0) (a 1) / ellProp g L t := by positivity
          linarith)
      calc mixedKer P t (a 0) (a 1) ≤ Cp / ((1 - t) * ellProp g L t) * 1 :=
            hle.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
        _ = Cp * 1 * R := by rw [hR, div_eq_mul_inv]; ring
        _ ≤ Cp * Cℓ * R := by gcongr
  calc (gammaG g)⁻¹ * ‖pairK (gammaG g) M t (σ 0) (σ 1) (a 0) (a 1)‖
      ≤ (gammaG g)⁻¹ * (Cp * Cℓ * R) := mul_le_mul_of_nonneg_left hK (by positivity)
    _ = Cp * Cℓ * (gammaG g)⁻¹ * R := by ring

end Model

/-- Lemma 5.2 [fo:lem:deterministic](a) and Proposition B.2 [ba:prop:primitive], fixed-rate
form: every `0 < g ≤ C`, `L ≥ L₀`, `W ≥ 1`, `0 ≤ t < 1`; the length-two case is
`k = 2`. -/
theorem primLoop_bdd (C B₀ c' : ℝ) (hC : 0 < C) (hB₀ : 0 < B₀) (hc' : 0 < c') (k : ℕ)
    (hk : 2 ≤ k) :
    ∃ C' : ℝ, ∃ L₀ : ℕ, 0 < C' ∧ ∀ g : ℝ, 0 < g → g ≤ C → ∀ L : ℕ, 3 ≤ L → L₀ ≤ L →
      ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m → c' ≤ m.im →
      ∀ W : ℕ, 1 ≤ W → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (a : Fin k → Fin L) (σ : Fin k → Bool),
        ‖primLoop g W L E m t a σ‖ ≤
          C' * (1 + (g ^ 2)⁻¹) ^ (k - 2) * zetaProp g W L t ^ (k - 1) := by
  rcases Nat.lt_or_ge k 3 with hk2 | hk3
  · -- `k = 2`
    obtain rfl : k = 2 := by omega
    obtain ⟨C₂, L₀, hC₂, H⟩ := bnd_two C B₀ c' hC hB₀ hc'
    refine ⟨C₂, L₀, hC₂, ?_⟩
    intro g hg hgC L hL hL₀ E hE m hm hcm W hW t ht0 ht1 a σ
    rw [bnd_norm_primLoop g W L E m t (by norm_num), bnd_zeta_eq]
    have h := H g hg.le hgC L hL hL₀ E hE m hm hcm t ht0 ht1 a σ
    have hW0 : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
    calc ((W : ℝ)⁻¹) ^ (2 - 1) * ‖primLoopF g L E m t a σ‖
        ≤ ((W : ℝ)⁻¹) ^ (2 - 1) * (C₂ * (gammaG g)⁻¹ * ((1 - t) * ellProp g L t)⁻¹) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by simp; ring
  · -- `k ≥ 3`
    obtain ⟨K, L₀, hK, H⟩ := bnd_propB2 C B₀ c' hC hB₀ hc' k
    refine ⟨K, L₀, hK, ?_⟩
    intro g hg hgC L hL hL₀ E hE m hm hcm W hW t ht0 ht1 a σ
    rw [bnd_norm_primLoop g W L E m t (by omega), bnd_zeta_eq]
    have h := H g hg hgC L hL hL₀ E hE m hm hcm t ht0 ht1 k hk3 le_rfl a σ
    have hγ1 : 1 ≤ (gammaG g)⁻¹ := one_le_inv₀ (bnd_gamma_pos g) |>.mpr (bnd_gamma_le_one g)
    have hδ : 0 < 1 - t := by linarith
    have hell0 : 0 < ellProp g L t := by
      have := (scale_facts g hg.le 1 L le_rfl (by omega) t t ht0 le_rfl ht1).1
      linarith
    set R := ((1 - t) * ellProp g L t)⁻¹ with hR
    have hR0 : 0 ≤ R := by positivity
    have hW0 : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
    calc ((W : ℝ)⁻¹) ^ (k - 1) * ‖primLoopF g L E m t a σ‖
        ≤ ((W : ℝ)⁻¹) ^ (k - 1) * (K * (1 + (g ^ 2)⁻¹) ^ (k - 2) * R ^ (k - 1)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = K * (1 + (g ^ 2)⁻¹) ^ (k - 2) * ((W : ℝ)⁻¹ * 1 * R) ^ (k - 1) := by
          rw [mul_one, mul_pow]; ring
      _ ≤ K * (1 + (g ^ 2)⁻¹) ^ (k - 2) * ((W : ℝ)⁻¹ * (gammaG g)⁻¹ * R) ^ (k - 1) := by
          gcongr

/-- The cyclic distance of two labels is at most the diameter of the word they form. -/
private lemma bnd_cd_le_diam {L : ℕ} (a b : Fin L) : cycDist a b ≤ wordDiam ![a, b] := by
  unfold wordDiam
  exact Finset.le_sup (f := fun p : Fin 2 × Fin 2 => cycDist (![a, b] p.1) (![a, b] p.2))
    (Finset.mem_univ ((0, 1) : Fin 2 × Fin 2))

/-- The exponent inequality of (B.16) [b:eq:primitive-long-pair]: `(3C₁ + 1) λ + c_p ρ^θ ≤ c₁ ρ` for
`ρ ≥ λ^{3/2}` and `λ ≥ T`. -/
private lemma bnd_longPair_exp {C₁ c₁ cp θ lam ρ : ℝ} (hc₁ : 0 < c₁)
    (hcp : 0 < cp) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2)
    (hlam : max 1 (max ((2 * (3 * C₁ + 1) / c₁) ^ 2) ((2 * cp / c₁) ^ 2)) ≤ lam)
    (hρ : lam ^ ((3 : ℝ) / 2) ≤ ρ) :
    (3 * C₁ + 1) * lam + cp * ρ ^ θ ≤ c₁ * ρ := by
  have hl1 : 1 ≤ lam := le_trans (le_max_left _ _) hlam
  have hlA : (2 * (3 * C₁ + 1) / c₁) ^ 2 ≤ lam :=
    le_trans ((le_max_left _ _).trans (le_max_right _ _)) hlam
  have hlB : (2 * cp / c₁) ^ 2 ≤ lam := le_trans ((le_max_right _ _).trans (le_max_right _ _)) hlam
  have hl0 : 0 < lam := by linarith
  have hsl : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hl0.le
  have h32 : lam ^ ((3 : ℝ) / 2) = lam * Real.sqrt lam := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hl0.le (by norm_num)]
    norm_num
  have hsqA : 2 * (3 * C₁ + 1) / c₁ ≤ Real.sqrt lam :=
    Real.le_sqrt_of_sq_le hlA
  have hlρ : lam ≤ ρ := by
    have : lam ≤ lam * Real.sqrt lam := by
      have : 1 ≤ Real.sqrt lam := by rw [Real.one_le_sqrt]; exact hl1
      nlinarith
    linarith [h32 ▸ hρ]
  have hρ1 : 1 ≤ ρ := le_trans hl1 hlρ
  have hρ0 : 0 < ρ := by linarith
  -- `c_p ρ^θ ≤ c_p √ρ ≤ (c₁/2) ρ`
  have hθρ : ρ ^ θ ≤ Real.sqrt ρ := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hρ1 (by linarith)
  have hsqB : 2 * cp / c₁ ≤ Real.sqrt ρ := Real.le_sqrt_of_sq_le (hlB.trans hlρ)
  have hsr : Real.sqrt ρ ^ 2 = ρ := Real.sq_sqrt hρ0.le
  have hB : cp * Real.sqrt ρ ≤ c₁ / 2 * ρ := by
    have h1 : 2 * cp ≤ c₁ * Real.sqrt ρ := by
      rw [div_le_iff₀ hc₁] at hsqB; linarith
    have h2 : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg _
    nlinarith
  -- `(3C₁ + 1) λ ≤ (c₁/2) λ^{3/2} ≤ (c₁/2) ρ`
  have hA : (3 * C₁ + 1) * lam ≤ c₁ / 2 * ρ := by
    have h1 : 2 * (3 * C₁ + 1) ≤ c₁ * Real.sqrt lam := by
      rw [div_le_iff₀ hc₁] at hsqA; linarith
    have h2 : (3 * C₁ + 1) * lam ≤ c₁ / 2 * (lam * Real.sqrt lam) := by nlinarith
    have h3 : lam * Real.sqrt lam ≤ ρ := h32 ▸ hρ
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hθρ hcp.le]

/-- (B.16) [b:eq:primitive-long-pair], Lemma B.11 [b:lem:primitive-pair], on `0 ≤ g ≤ C`. -/
theorem primLoop_longPair (C B₀ c' θ cp F : ℝ) (hC : 0 < C) (hB₀ : 0 < B₀) (hc' : 0 < c')
    (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2) (hcp : 0 < cp) (hF : 0 < F) :
    ∃ C' : ℝ, ∃ W₀ L₀ : ℕ, 0 < C' ∧ ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, 0 ≤ g → g ≤ C →
      ∀ L : ℕ, 3 ≤ L → L₀ ≤ L → ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ,
      IsDysonRootV (hopB g) (gammaG g) L E m → c' ≤ m.im →
      ∀ v : ℝ, 1 / 2 ≤ v → (W : ℝ) ^ (-3 : ℝ) ≤ 1 - v → ∀ (a b : Fin L) (σ₁ σ₂ : Bool),
        ellProp g L v * Real.log W ^ ((3 : ℝ) / 2) ≤ cycDist a b →
        ‖primLoop g W L E m v ![a, b] ![σ₁, σ₂]‖ ≤
          C' * zetaProp g W L v ^ 2 * weightFn cp θ F W (ellProp g L v) (cycDist a b) := by
  have _hF := hF
  obtain ⟨C₁, c₁, L₀, hC₁, hc₁, H⟩ := primLoopF_bdd_weighted C B₀ c' hC hB₀ hc' 2 le_rfl
  set T : ℝ := max 1 (max ((2 * (3 * C₁ + 1) / c₁) ^ 2) ((2 * cp / c₁) ^ 2)) with hT
  refine ⟨4 * C₁, ⌈Real.exp T⌉₊, L₀, by positivity, ?_⟩
  intro W hW g hg hgC L hL hL₀ E hE m hm hcm v hv hWv a b σ₁ σ₂ hdist
  have hT1 : 1 ≤ T := le_max_left _ _
  have hWT : Real.exp T ≤ W := le_trans (Nat.le_ceil _) (by exact_mod_cast hW)
  have hW1' : (1 : ℝ) ≤ W := le_trans (Real.one_le_exp (by linarith)) hWT
  have hW0 : (0 : ℝ) < W := by linarith
  have hW1 : 1 ≤ W := by exact_mod_cast hW1'
  set lam := Real.log W with hlam
  have hlamT : T ≤ lam := (Real.le_log_iff_exp_le hW0).mpr hWT
  have hWe : (W : ℝ) = Real.exp lam := (Real.exp_log hW0).symm
  have hW3 : 0 < (W : ℝ) ^ (-3 : ℝ) := Real.rpow_pos_of_pos hW0 _
  have hv1 : v < 1 := by linarith
  have hv0 : 0 ≤ v := by linarith
  have hδ : 0 < 1 - v := by linarith
  have hsf := scale_facts g hg W L hW1 (by omega) v v hv0 le_rfl hv1
  have hell1 : 1 ≤ ellProp g L v := hsf.1
  have hell0 : 0 < ellProp g L v := by linarith
  set r : ℝ := (cycDist a b : ℝ) with hr
  set ρ : ℝ := r / ellProp g L v with hρ
  have hlam1 : 1 ≤ lam := le_trans hT1 hlamT
  have hρlam : lam ^ ((3 : ℝ) / 2) ≤ ρ := by
    rw [hρ, le_div_iff₀ hell0, mul_comm]; exact hdist
  have hexp := bnd_longPair_exp hc₁ hcp hθ hθ2 hlamT hρlam
  -- the weighted bound of `F_2`
  have hFb := H g hg hgC L hL hL₀ E hE m hm hcm v hv0 hv1 ![a, b] ![σ₁, σ₂]
  have hdiam : c₁ * ρ ≤ c₁ * (wordDiam ![a, b] : ℝ) / ellProp g L v := by
    rw [hρ, hr, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hc₁.le
    exact div_le_div_of_nonneg_right (by exact_mod_cast bnd_cd_le_diam a b) hell0.le
  have hpow : (1 - v) ^ (-C₁) ≤ Real.exp (3 * C₁ * lam) := by
    have h1 : (1 - v) ^ (-C₁) ≤ ((W : ℝ) ^ (-3 : ℝ)) ^ (-C₁) :=
      Real.rpow_le_rpow_of_nonpos hW3 hWv (by linarith)
    rw [← Real.rpow_mul hW0.le, Real.rpow_def_of_pos hW0] at h1
    refine h1.trans (le_of_eq ?_)
    congr 1; ring
  have hF2 : ‖primLoopF g L E m v ![a, b] ![σ₁, σ₂]‖ ≤
      C₁ * Real.exp (3 * C₁ * lam) * Real.exp (-(c₁ * ρ)) := by
    refine hFb.trans ?_
    have he : Real.exp (-(c₁ * (wordDiam ![a, b] : ℝ) / ellProp g L v)) ≤ Real.exp (-(c₁ * ρ)) :=
      Real.exp_le_exp.mpr (by linarith)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hC₁.le) he (Real.exp_pos _).le
      (by positivity)
  -- the lower bounds of `ζ_v²` and of the weight
  have hζ : (2 * (W : ℝ))⁻¹ ≤ zetaProp g W L v := hsf.2.2.2.1
  have hζ2 : (2 * (W : ℝ))⁻¹ ^ 2 ≤ zetaProp g W L v ^ 2 :=
    pow_le_pow_left₀ (by positivity) hζ 2
  have hw : Real.exp (-(cp * ρ ^ θ)) ≤ weightFn cp θ F W (ellProp g L v) r := by
    unfold weightFn
    have : 0 ≤ (W : ℝ) ^ (-F) := Real.rpow_nonneg hW0.le _
    rw [← hρ]
    linarith
  have h12 : 1 ≤ 2 := by norm_num
  rw [bnd_norm_primLoop g W L E m v h12]
  have hW2 : (2 * (W : ℝ))⁻¹ ^ 2 = Real.exp (-(2 * lam)) / 4 := by
    rw [hWe, inv_pow, mul_pow, ← Real.exp_nat_mul, Real.exp_neg]
    push_cast
    ring
  calc ((W : ℝ)⁻¹) ^ (2 - 1) * ‖primLoopF g L E m v ![a, b] ![σ₁, σ₂]‖
      ≤ (W : ℝ)⁻¹ * (C₁ * Real.exp (3 * C₁ * lam) * Real.exp (-(c₁ * ρ))) := by
        rw [show 2 - 1 = 1 by rfl, pow_one]
        exact mul_le_mul_of_nonneg_left hF2 (by positivity)
    _ = C₁ * Real.exp (-lam + 3 * C₁ * lam - c₁ * ρ) := by
        rw [hWe, ← Real.exp_neg, show -lam + 3 * C₁ * lam - c₁ * ρ =
          -lam + (3 * C₁ * lam + -(c₁ * ρ)) by ring, Real.exp_add, Real.exp_add]
        ring
    _ ≤ C₁ * Real.exp (-(2 * lam) + -(cp * ρ ^ θ)) := by
        gcongr
        linarith
    _ = 4 * C₁ * (Real.exp (-(2 * lam)) / 4) * Real.exp (-(cp * ρ ^ θ)) := by
        rw [Real.exp_add]; ring
    _ ≤ 4 * C₁ * zetaProp g W L v ^ 2 * weightFn cp θ F W (ellProp g L v) r := by
        rw [← hW2]
        gcongr

end LSBA
