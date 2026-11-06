import LSBA.Transfer.Coarse
import LSBA.Flow.Realization

/-!
# Weighted Ward identity and seed tails

Lemma 7.3 [uvc:lem:weighted-ward]: the exact weighted Ward identity and the weighted Ward
inequality for block operators with Hermitian onsite blocks and nearest-neighbour hopping on the
cycle, and the seed tails (7.9) [uvc:eq:seed-tails] at each fixed time.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

private theorem ward_val_finRotate {L : ℕ} (x : Fin L) :
    (finRotate L x).val = (x.val + 1) % L := by
  cases L with
  | zero => exact x.elim0
  | succ n =>
    rw [coe_finRotate]
    by_cases h : x = Fin.last n
    · subst h
      simp
    · simp only [h, ↓reduceIte]
      have : x.val < n := by
        have h1 := x.isLt
        have h2 : x.val ≠ n := fun h' => h (Fin.ext (by simpa using h'))
        omega
      rw [Nat.mod_eq_of_lt (by omega)]

private theorem ward_cycleAdj_apply {L : ℕ} (x y : Fin L) :
    cycleAdj L x y = (if y = finRotate L x then 1 else 0) +
      (if y = (finRotate L)⁻¹ x then 1 else 0) := by
  unfold cycleAdj
  simp only [Matrix.of_apply]
  have h1 : (y.val = (x.val + 1) % L) ↔ y = finRotate L x := by
    rw [← ward_val_finRotate, Fin.ext_iff]
  have h2 : (x.val = (y.val + 1) % L) ↔ y = (finRotate L)⁻¹ x := by
    rw [← ward_val_finRotate, ← Fin.ext_iff, eq_comm, Equiv.Perm.eq_inv_iff_eq]
  simp only [h1, h2]

private theorem ward_mulVec_cycle {W L : ℕ} (F : Fin L × Fin W → ℂ) (x : Fin L) (α : Fin W) :
    ((cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) *ᵥ F) (x, α) =
      F (finRotate L x, α) + F ((finRotate L)⁻¹ x, α) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.one_apply, ward_cycleAdj_apply]
  simp [add_mul, Finset.sum_add_distrib, ite_mul]

private theorem ward_mulVec_blockDiagOp {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ)
    (F : Fin L × Fin W → ℂ) (x : Fin L) (α : Fin W) :
    (blockDiagOp V *ᵥ F) (x, α) = (V x *ᵥ fun γ => F (x, γ)) α := by
  simp [Matrix.mulVec, dotProduct, blockDiagOp, Fintype.sum_prod_type]

/-- The vector supported on the block `b`. -/
private def ward_embed {W L : ℕ} (b : Fin L) (u : Fin W → ℂ) : Fin L × Fin W → ℂ :=
  fun p => if p.1 = b then u p.2 else 0

private theorem ward_blockOf_mulVec {W L : ℕ}
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (b : Fin L) (u : Fin W → ℂ) (y : Fin L) :
    blockOf G y b *ᵥ u = fun γ => (G *ᵥ ward_embed b u) (y, γ) := by
  funext α
  simp [Matrix.mulVec, dotProduct, blockOf, ward_embed, Fintype.sum_prod_type]

private theorem ward_isHermitian_op {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ)
    (hV : ∀ r, (V r).IsHermitian) :
    (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V).IsHermitian := by
  have hK : (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, (cycleAdj_isHermitian L).eq,
      Matrix.conjTranspose_one]
  exact hK.add (blockDiagOp_isHermitian hV)

/-- Row `x` of `(A - z) G ι_b u = ι_b u`. -/
private theorem ward_row {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ)
    (hV : ∀ r, (V r).IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (b : Fin L) (u : Fin W → ℂ)
    (x : Fin L) :
    let G := resolventMat (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V) z
    blockOf G (finRotate L x) b *ᵥ u + blockOf G ((finRotate L)⁻¹ x) b *ᵥ u +
      V x *ᵥ (blockOf G x b *ᵥ u) - z • (blockOf G x b *ᵥ u) = if x = b then u else 0 := by
  intro G
  have hH := ward_isHermitian_op V hV
  have h1 := sub_smul_mul_resolventMat hH hz
  set F := G *ᵥ ward_embed b u with hF
  have h2 : (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V -
      z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) *ᵥ F = ward_embed b u := by
    rw [hF, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  funext α
  have h3 := congrFun h2 (x, α)
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply,
    Matrix.add_mulVec, Pi.add_apply, ward_mulVec_cycle, ward_mulVec_blockDiagOp] at h3
  simp only [ward_blockOf_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  rw [← hF]
  simp only [ward_embed] at h3
  by_cases hxb : x = b
  · simp only [hxb, ↓reduceIte] at h3 ⊢
    simpa [smul_eq_mul] using h3
  · simp only [hxb, ↓reduceIte] at h3 ⊢
    simpa [smul_eq_mul] using h3


private theorem ward_perm_inv_apply {α : Type*} (σ : Equiv.Perm α) (x : α) : σ⁻¹ (σ x) = x := by
  rw [Equiv.Perm.inv_def]
  exact σ.symm_apply_apply x

private theorem ward_dot_conj {n : Type*} [Fintype n] (x y : n → ℂ) :
    star y ⬝ᵥ x = star (star x ⬝ᵥ y) := by
  simp [dotProduct, star_sum, mul_comm]

private theorem ward_dot_self {n : Type*} [Fintype n] (x : n → ℂ) :
    star x ⬝ᵥ x = ((∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem ward_quad {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ)
    (hV : ∀ r, (V r).IsHermitian) (f : Fin L → Fin W → ℂ) (wt : Fin L → ℝ) (z : ℂ)
    (b : Fin L) (v : Fin W → ℂ) (hwb : wt b = 1)
    (hrow : ∀ x, f (finRotate L x) + f ((finRotate L)⁻¹ x) + V x *ᵥ f x - z • f x =
      if x = b then v else 0) :
    z.im * ∑ c, wt c * ∑ i, ‖f c i‖ ^ 2 =
      (star v ⬝ᵥ f b).im +
        ∑ c, (wt c - wt (finRotate L c)) * (star (f c) ⬝ᵥ f (finRotate L c)).im := by
  have key : ∀ c, wt c * ((star (f c) ⬝ᵥ f (finRotate L c)).im +
      (star (f c) ⬝ᵥ f ((finRotate L)⁻¹ c)).im - z.im * ∑ i, ‖f c i‖ ^ 2) =
      wt c * (if c = b then (star (f c) ⬝ᵥ v).im else 0) := by
    intro c
    have h := congrArg (fun y => star (f c) ⬝ᵥ y) (hrow c)
    simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul] at h
    have h2 := congrArg Complex.im h
    have h3 : (star (f c) ⬝ᵥ V c *ᵥ f c).im = 0 := (hV c).im_star_dotProduct_mulVec_self (f c)
    rw [Complex.sub_im, Complex.add_im, Complex.add_im, h3, ward_dot_self, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im] at h2
    by_cases hcb : c = b
    · simp only [hcb, ↓reduceIte] at h2 ⊢
      rw [← h2]; ring
    · simp only [hcb, ↓reduceIte, dotProduct_zero, Complex.zero_im] at h2 ⊢
      rw [← h2]; ring
  have hsum := Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) => key c
  have hR : ∑ c, wt c * (if c = b then (star (f c) ⬝ᵥ v).im else 0) = (star (f b) ⬝ᵥ v).im := by
    rw [Finset.sum_eq_single b (fun c _ hc => by simp [hc]) (by simp)]
    simp [hwb]
  rw [hR] at hsum
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  have hreidx : ∑ c, wt c * (star (f c) ⬝ᵥ f ((finRotate L)⁻¹ c)).im =
      -∑ c, wt (finRotate L c) * (star (f c) ⬝ᵥ f (finRotate L c)).im := by
    rw [← Equiv.sum_comp (finRotate L) (fun c => wt c * (star (f c) ⬝ᵥ f ((finRotate L)⁻¹ c)).im),
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ward_perm_inv_apply]
    rw [ward_dot_conj (f c) (f (finRotate L c)), Complex.star_def, Complex.conj_im]
    ring
  have hmul : ∑ c, wt c * (z.im * ∑ i, ‖f c i‖ ^ 2) = z.im * ∑ c, wt c * ∑ i, ‖f c i‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  have hdiff : ∑ c, (wt c - wt (finRotate L c)) * (star (f c) ⬝ᵥ f (finRotate L c)).im =
      ∑ c, wt c * (star (f c) ⬝ᵥ f (finRotate L c)).im -
        ∑ c, wt (finRotate L c) * (star (f c) ⬝ᵥ f (finRotate L c)).im := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  have hbv : (star (f b) ⬝ᵥ v).im = -(star v ⬝ᵥ f b).im := by
    rw [ward_dot_conj (f b) v, Complex.star_def, Complex.conj_im, neg_neg]
  rw [hdiff, ← hmul]
  linarith


/-- The exact identity of the proof of Lemma 7.3 [uvc:lem:weighted-ward]: for Hermitian onsite
blocks, `f_c = G_{cb} v` and `w_c = e^{α d(c, b)}`,
`η Σ_c w_c² ‖f_c‖² = Im⟨v, G_{bb} v⟩ + Σ_c (w_c² - w_{c+1}²) Im⟨f_c, f_{c+1}⟩`. -/
theorem weighted_ward_identity {W L : ℕ} (hL : 3 ≤ L) (V : Fin L → Matrix (Fin W) (Fin W) ℂ)
    (hV : ∀ r, (V r).IsHermitian) (E η α : ℝ) (hη : 0 < η) (b : Fin L) (v : Fin W → ℂ) :
    let G := resolventMat (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V)
      ((E : ℂ) + (η : ℂ) * Complex.I)
    let f := fun c : Fin L => (blockOf G c b).mulVec v
    let w := fun c : Fin L => Real.exp (α * cycDist c b)
    η * ∑ c, w c ^ 2 * ∑ i, ‖f c i‖ ^ 2 =
      (star v ⬝ᵥ (blockOf G b b).mulVec v).im +
        ∑ c, (w c ^ 2 - w (finRotate L c) ^ 2) * (star (f c) ⬝ᵥ f (finRotate L c)).im := by
  intro G f w
  have _ := hL
  have hz : ((E : ℂ) + (η : ℂ) * Complex.I).im ≠ 0 := by simpa using hη.ne'
  have hzim : ((E : ℂ) + (η : ℂ) * Complex.I).im = η := by simp
  have hwb : w b ^ 2 = 1 := by simp [w, cycDist]
  have hq := ward_quad V hV f (fun c => w c ^ 2) ((E : ℂ) + (η : ℂ) * Complex.I) b v hwb
    (fun x => ward_row V hV hz b v x)
  rw [hzim] at hq
  exact hq

private theorem ward_mod {L x y : ℕ} (hx : x < L) (hy : y < L) :
    (x + L - y) % L = if y ≤ x then x - y else x + L - y := by
  split_ifs with h
  · have : x + L - y = (x - y) + L := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

private theorem ward_cd_comm {L : ℕ} (a b : Fin L) : cycDist a b = cycDist b a := by
  unfold cycDist; exact min_comm _ _

private theorem ward_cd_tri {L : ℕ} (a b c : Fin L) :
    cycDist a c ≤ cycDist a b + cycDist b c := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  simp only [cycDist, ward_mod ha hb, ward_mod hb ha, ward_mod ha hc, ward_mod hc ha,
    ward_mod hb hc, ward_mod hc hb]
  split_ifs <;> omega

/-- The `j`-th power of the cyclic shift moves the block index by `j` modulo `L`. -/
private theorem ward_pow_val {L : ℕ} (a : Fin L) (j : ℕ) :
    ((finRotate L ^ j) a).val = (a.val + j) % L := by
  induction j with
  | zero => simp [Nat.mod_eq_of_lt a.isLt]
  | succ j ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ward_val_finRotate, ih, Nat.mod_add_mod]
    rfl

private theorem ward_cd_pow {L : ℕ} (a : Fin L) {j : ℕ} (hj : j < L) :
    cycDist a ((finRotate L ^ j) a) ≤ j := by
  have ha := a.isLt
  have hx := ((finRotate L ^ j) a).isLt
  have hv := ward_pow_val a j
  simp only [cycDist, ward_mod ha hx, ward_mod hx ha]
  by_cases h1 : a.val + j < L
  · rw [Nat.mod_eq_of_lt h1] at hv
    split_ifs <;> omega
  · rw [Nat.mod_eq_sub_mod (not_lt.mp h1), Nat.mod_eq_of_lt (by omega)] at hv
    split_ifs <;> omega

private theorem ward_cd_rot {L : ℕ} (hL : 3 ≤ L) (c : Fin L) : cycDist c (finRotate L c) ≤ 1 := by
  have := ward_cd_pow c (j := 1) (by omega)
  simpa using this

private theorem ward_pow_injOn {L : ℕ} (a : Fin L) {n : ℕ} (hn : n + 1 ≤ L) :
    Set.InjOn (fun j : ℕ => (finRotate L ^ j) a) ↑(Finset.range (n + 1)) := by
  intro j hj j' hj' h
  simp only [Finset.coe_range, Set.mem_Iio] at hj hj'
  have h1 : (a.val + j) % L = (a.val + j') % L := by
    rw [← ward_pow_val, ← ward_pow_val]
    exact congrArg Fin.val h
  have h2 : j ≡ j' [MOD L] := Nat.ModEq.add_left_cancel' a.val h1
  exact Nat.ModEq.eq_of_lt_of_lt h2 (by omega) (by omega)

private theorem ward_sum_arc_le {L : ℕ} (a : Fin L) {n : ℕ} (hn : n + 1 ≤ L)
    (s : Fin L → ℝ) (hs : ∀ c, 0 ≤ s c) :
    ∑ j ∈ Finset.range (n + 1), s ((finRotate L ^ j) a) ≤ ∑ c, s c := by
  rw [← Finset.sum_image (f := s) (g := fun j : ℕ => (finRotate L ^ j) a) (fun j hj j' hj' h =>
    ward_pow_injOn a hn hj hj' h)]
  exact Finset.sum_le_univ_sum_of_nonneg hs

/-- The sum of squared moduli of the entries of a vector. -/
private def ward_nsq {n : Type*} [Fintype n] (v : n → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

private theorem ward_nsq_nonneg {n : Type*} [Fintype n] (v : n → ℂ) : 0 ≤ ward_nsq v :=
  Finset.sum_nonneg fun _ _ => by positivity

private theorem ward_cauchy {n : Type*} [Fintype n] (x y : n → ℂ) :
    ‖star x ⬝ᵥ y‖ ^ 2 ≤ ward_nsq x * ward_nsq y := by
  have h1 : ‖star x ⬝ᵥ y‖ ≤ ∑ i, ‖x i‖ * ‖y i‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    simp
  calc ‖star x ⬝ᵥ y‖ ^ 2 ≤ (∑ i, ‖x i‖ * ‖y i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

private theorem ward_nsq_mulVec_le {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (u : n → ℂ) :
    ward_nsq (A *ᵥ u) ≤ ‖A‖ ^ 2 * ward_nsq u := by
  have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 u)
  have h1 : ‖(EuclideanSpace.equiv n ℂ).symm (A *ᵥ u)‖ ^ 2 = ward_nsq (A *ᵥ u) := by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  have h2 : ‖(WithLp.toLp 2 u : EuclideanSpace ℂ n)‖ ^ 2 = ward_nsq u := by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  rw [← h1, ← h2, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

private theorem ward_opNorm_le {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ u : n → ℂ, ward_nsq (A *ᵥ u) ≤ c ^ 2 * ward_nsq u) :
    ‖A‖ ≤ c := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  have h1 : ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A x‖ ^ 2 = ward_nsq (A *ᵥ x.ofLp) := by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  have h2 : ‖x‖ ^ 2 = ward_nsq x.ofLp := by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  have h3 := h x.ofLp
  rw [← h1, ← h2] at h3
  have h4 : ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A x‖ ^ 2 ≤ (c * ‖x‖) ^ 2 := by
    rw [mul_pow]; exact h3
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h4

/-- `Im⟨u, M u⟩ ≤ ‖M‖ ‖u‖²`. -/
private theorem ward_im_le {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ)
    (u : n → ℂ) : (star u ⬝ᵥ (M *ᵥ u)).im ≤ ‖M‖ * ward_nsq u := by
  have h1 : (star u ⬝ᵥ (M *ᵥ u)).im ≤ ‖star u ⬝ᵥ (M *ᵥ u)‖ :=
    (Complex.im_le_norm _)
  have h2 := ward_cauchy u (M *ᵥ u)
  have h3 := ward_nsq_mulVec_le M u
  have h4 : ‖star u ⬝ᵥ (M *ᵥ u)‖ ^ 2 ≤ (‖M‖ * ward_nsq u) ^ 2 := by
    calc _ ≤ ward_nsq u * ward_nsq (M *ᵥ u) := h2
      _ ≤ ward_nsq u * (‖M‖ ^ 2 * ward_nsq u) :=
          mul_le_mul_of_nonneg_left h3 (ward_nsq_nonneg u)
      _ = _ := by ring
  have h5 : ‖star u ⬝ᵥ (M *ᵥ u)‖ ≤ ‖M‖ * ward_nsq u :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (ward_nsq_nonneg u))
      two_ne_zero).mp h4
  exact h1.trans h5


/-- Two positive weights within a factor `q` of each other satisfy
`|x² - y²| ≤ (q - r) x y` when `q r = 1`. -/
private theorem ward_wt_diff {q r x y : ℝ} (hr : 0 < r) (hqr : q * r = 1) (hx : 0 < x)
    (hy : 0 < y) (h1 : x ≤ q * y) (h2 : y ≤ q * x) :
    |x ^ 2 - y ^ 2| ≤ (q - r) * (x * y) := by
  have e1 : (x - q * y) * (x + r * y) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have e2 : (y - q * x) * (y + r * x) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  rw [abs_le]
  constructor <;> nlinarith

/-- `e^α - e^{-α} ≤ (16/7) α` for `0 ≤ α ≤ 1/8`. -/
private theorem ward_exp_diff {α : ℝ} (hα : 0 ≤ α) (hα8 : α ≤ 1 / 8) :
    Real.exp α - Real.exp (-α) ≤ 16 / 7 * α := by
  have h1 : -α + 1 ≤ Real.exp (-α) := Real.add_one_le_exp (-α)
  have h2 : Real.exp (-α) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hqr : Real.exp α * Real.exp (-α) = 1 := by rw [← Real.exp_add]; simp
  have hr : 0 < Real.exp (-α) := Real.exp_pos _
  by_contra hcon
  have hcon := not_le.mp hcon
  nlinarith [mul_pos hr hr]

/-- `x y |Im⟨p, q⟩| ≤ (x² ‖p‖² + y² ‖q‖²) / 2` for `x, y ≥ 0`. -/
private theorem ward_cs_bound {W : ℕ} {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (p q : Fin W → ℂ) :
    x * y * |(star p ⬝ᵥ q).im| ≤ (x ^ 2 * ward_nsq p + y ^ 2 * ward_nsq q) / 2 := by
  have hA := ward_nsq_nonneg p
  have hB := ward_nsq_nonneg q
  have h1 : |(star p ⬝ᵥ q).im| ≤ ‖star p ⬝ᵥ q‖ := Complex.abs_im_le_norm _
  have h2 : |(star p ⬝ᵥ q).im| ^ 2 ≤ ward_nsq p * ward_nsq q :=
    (pow_le_pow_left₀ (abs_nonneg _) h1 2).trans (ward_cauchy p q)
  have h3 : (x * y * |(star p ⬝ᵥ q).im|) ^ 2 ≤
      ((x ^ 2 * ward_nsq p + y ^ 2 * ward_nsq q) / 2) ^ 2 := by
    calc (x * y * |(star p ⬝ᵥ q).im|) ^ 2 = (x * y) ^ 2 * |(star p ⬝ᵥ q).im| ^ 2 := by ring
      _ ≤ (x * y) ^ 2 * (ward_nsq p * ward_nsq q) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ ≤ _ := by nlinarith [sq_nonneg (x ^ 2 * ward_nsq p - y ^ 2 * ward_nsq q)]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h3

/-- The error term of the weighted Ward identity is at most `(e^α - e^{-α}) S` when the weight
exponent changes by at most `1` along the cycle. -/
private theorem ward_err_le {W L : ℕ} (f : Fin L → Fin W → ℂ) {α : ℝ} (hα : 0 ≤ α)
    (d : Fin L → ℕ) (hd : ∀ c, d (finRotate L c) ≤ d c + 1 ∧ d c ≤ d (finRotate L c) + 1) :
    |∑ c, (Real.exp (α * d c) ^ 2 - Real.exp (α * d (finRotate L c)) ^ 2) *
        (star (f c) ⬝ᵥ f (finRotate L c)).im| ≤
      (Real.exp α - Real.exp (-α)) * ∑ c, Real.exp (α * d c) ^ 2 * ward_nsq (f c) := by
  set s : ℝ := Real.exp α - Real.exp (-α) with hs
  have hqr : Real.exp α * Real.exp (-α) = 1 := by rw [← Real.exp_add]; simp
  have hr : 0 < Real.exp (-α) := Real.exp_pos _
  have hs0 : 0 ≤ s := by
    rw [hs, sub_nonneg]
    exact Real.exp_le_exp.mpr (by linarith)
  have hterm : ∀ c, |(Real.exp (α * d c) ^ 2 - Real.exp (α * d (finRotate L c)) ^ 2) *
      (star (f c) ⬝ᵥ f (finRotate L c)).im| ≤
      s / 2 * (Real.exp (α * d c) ^ 2 * ward_nsq (f c) +
        Real.exp (α * d (finRotate L c)) ^ 2 * ward_nsq (f (finRotate L c))) := by
    intro c
    set x := Real.exp (α * d c) with hx
    set y := Real.exp (α * d (finRotate L c)) with hy
    have hx0 : 0 < x := Real.exp_pos _
    have hy0 : 0 < y := Real.exp_pos _
    have h1 : x ≤ Real.exp α * y := by
      rw [hx, hy, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have : (d c : ℝ) ≤ d (finRotate L c) + 1 := by exact_mod_cast (hd c).2
      nlinarith
    have h2 : y ≤ Real.exp α * x := by
      rw [hx, hy, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have : (d (finRotate L c) : ℝ) ≤ d c + 1 := by exact_mod_cast (hd c).1
      nlinarith
    have h3 := ward_wt_diff hr hqr hx0 hy0 h1 h2
    have h4 := ward_cs_bound hx0.le hy0.le (f c) (f (finRotate L c))
    rw [abs_mul]
    calc |x ^ 2 - y ^ 2| * |(star (f c) ⬝ᵥ f (finRotate L c)).im|
        ≤ (s * (x * y)) * |(star (f c) ⬝ᵥ f (finRotate L c)).im| :=
          mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
      _ = s * (x * y * |(star (f c) ⬝ᵥ f (finRotate L c)).im|) := by ring
      _ ≤ s * ((x ^ 2 * ward_nsq (f c) + y ^ 2 * ward_nsq (f (finRotate L c))) / 2) :=
          mul_le_mul_of_nonneg_left h4 hs0
      _ = _ := by ring
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun c _ => hterm c).trans ?_)
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have hre : ∑ c, Real.exp (α * d (finRotate L c)) ^ 2 * ward_nsq (f (finRotate L c)) =
      ∑ c, Real.exp (α * d c) ^ 2 * ward_nsq (f c) :=
    Equiv.sum_comp (finRotate L) (fun c => Real.exp (α * d c) ^ 2 * ward_nsq (f c))
  rw [hre]
  linarith

/-- Lemma 7.3 [uvc:lem:weighted-ward], pathwise, for every family of Hermitian onsite blocks:
for `0 < η ≤ 1` and `0 ≤ α ≤ η/8`, `η Σ_c e^{2α d(c, b)} ‖G_{cb} v‖² ≤ 2 Im⟨v, G_{bb} v⟩`. -/
theorem weighted_ward {W L : ℕ} (hL : 3 ≤ L) (V : Fin L → Matrix (Fin W) (Fin W) ℂ)
    (hV : ∀ r, (V r).IsHermitian) (E η α : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hα : 0 ≤ α)
    (hαη : α ≤ η / 8) (b : Fin L) (v : Fin W → ℂ) :
    let G := resolventMat (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V)
      ((E : ℂ) + (η : ℂ) * Complex.I)
    η * ∑ c, Real.exp (α * cycDist c b) ^ 2 * ∑ i, ‖(blockOf G c b).mulVec v i‖ ^ 2 ≤
      2 * (star v ⬝ᵥ (blockOf G b b).mulVec v).im := by
  intro G
  have hid := weighted_ward_identity hL V hV E η α hη b v
  have herr := ward_err_le (fun c => (blockOf G c b).mulVec v) hα (fun c => cycDist c b)
    (fun c => ⟨by
      have := (ward_cd_tri (finRotate L c) c b)
      have h2 := ward_cd_rot hL c
      rw [ward_cd_comm (finRotate L c) c] at this
      omega, by
      have := (ward_cd_tri c (finRotate L c) b)
      have h2 := ward_cd_rot hL c
      omega⟩)
  have hS : 0 ≤ ∑ c, Real.exp (α * cycDist c b) ^ 2 * ∑ i, ‖(blockOf G c b).mulVec v i‖ ^ 2 :=
    Finset.sum_nonneg fun c _ => by positivity
  have hs : Real.exp α - Real.exp (-α) ≤ η / 2 := by
    have := ward_exp_diff hα (by linarith)
    linarith
  simp only [ward_nsq] at herr
  have h1 := (abs_le.mp herr).2
  have h2 : (Real.exp α - Real.exp (-α)) *
      ∑ c, Real.exp (α * cycDist c b) ^ 2 * ∑ i, ‖(blockOf G c b).mulVec v i‖ ^ 2 ≤
      η / 2 * ∑ c, Real.exp (α * cycDist c b) ^ 2 * ∑ i, ‖(blockOf G c b).mulVec v i‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hs hS
  simp only [] at hid
  linarith


private theorem ward_Hdet_eq {W L : ℕ} {g : ℝ} (hg : 1 ≤ g)
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) :
    Hdet g V = cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) +
      blockDiagOp (fun c => ((g⁻¹ : ℝ) : ℂ) • V c) := by
  have hm : max 1 g = g := max_eq_right hg
  have hg0 : (g : ℂ) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le one_pos hg).ne'
  have hb : blockDiagOp (fun c => ((g⁻¹ : ℝ) : ℂ) • V c) = ((g⁻¹ : ℝ) : ℂ) • blockDiagOp V := by
    ext ⟨a, α⟩ ⟨b, β⟩
    by_cases h : a = b <;> simp [blockDiagOp, h]
  unfold Hdet
  rw [hm, hb, smul_add, smul_smul, Complex.ofReal_inv, inv_mul_cancel₀ hg0, one_smul]

private theorem ward_isHermitian_smul_real {n : Type*} {M : Matrix n n ℂ} (hM : M.IsHermitian)
    (r : ℝ) : (((r : ℝ) : ℂ) • M).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hM.eq, Complex.star_def, Complex.conj_ofReal]

/-- The pathwise decay of a Green block away from the source, from the arc inequality and the
weighted Ward inequality with `α = η/8`: for `d(a, b) > n`,
`‖G_{ab}‖ ≤ 2 K_a e^{ηn/8} e^{-η d(a,b)/8} (‖G_{bb}‖ / (n η))^{1/2}`. -/
private theorem ward_green_decay {W L : ℕ} (hL : 3 ≤ L) {g : ℝ} (hg : 1 ≤ g)
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (hV : ∀ a, (V a).IsHermitian) (E η : ℝ)
    (hη : 0 < η) (hη1 : η ≤ 1) {n : ℕ} (hn : 1 ≤ n) (hnL : 2 * n + 1 ≤ L) (a b : Fin L)
    (hd : n < cycDist a b) :
    ‖blockOf (resolventMat (Hdet g V) (↑E + ↑η * Complex.I)) a b‖ ≤
      2 * arcK g (↑E + ↑η * Complex.I) V a true n * Real.exp (η / 8 * n) *
        Real.exp (-(η / 8 * cycDist a b)) *
        Real.sqrt (‖blockOf (resolventMat (Hdet g V) (↑E + ↑η * Complex.I)) b b‖ / (n * η)) := by
  set z : ℂ := ↑E + ↑η * Complex.I with hzdef
  have hz : z.im ≠ 0 := by simpa [hzdef] using hη.ne'
  set α : ℝ := η / 8 with hα
  have hα0 : 0 ≤ α := by positivity
  set U : Fin L → Matrix (Fin W) (Fin W) ℂ := fun c => ((g⁻¹ : ℝ) : ℂ) • V c with hU
  have hUh : ∀ c, (U c).IsHermitian := fun c => ward_isHermitian_smul_real (hV c) _
  have hHd : Hdet g V = cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp U :=
    ward_Hdet_eq hg V
  set G := resolventMat (Hdet g V) z with hG
  set K := arcK g z V a true n with hK
  have hK0 : 0 ≤ K := Real.iSup_nonneg fun _ => norm_nonneg _
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnη : 0 < (n : ℝ) * η := mul_pos hn' hη
  set X : ℝ := ‖blockOf G b b‖ with hX
  have hX0 : 0 ≤ X := norm_nonneg _
  have hnL' : n + 1 ≤ L := by omega
  refine ward_opNorm_le _ (by positivity) fun u => ?_
  set f : Fin L → Fin W → ℂ := fun y => blockOf G y b *ᵥ u with hf
  set N : ℝ := ward_nsq u with hN
  set S : ℝ := ∑ c, Real.exp (α * cycDist c b) ^ 2 * ward_nsq (f c) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun c _ => by
    have := ward_nsq_nonneg (f c)
    positivity
  -- the arc avoids `b`
  have harc : ∀ j, j ≤ n → (finRotate L ^ j) a ≠ b := by
    intro j hj h
    have := ward_cd_pow a (j := j) (by omega)
    rw [h] at this
    omega
  have hb : ∀ i, 1 ≤ i → i < n → arcBlock a true i ≠ b := fun i _ hi => by
    simpa [arcBlock] using harc i hi.le
  have h1 := norm_sq_le_arc hL hg V hV hz b u a true hn hb
  -- the sum over the arc
  set E0 : ℝ := Real.exp (-(2 * α * ((cycDist a b : ℝ) - n))) with hE0
  have h2 : ∑ j ∈ Finset.range (n + 1), ward_nsq (f ((finRotate L ^ j) a)) ≤ E0 * S := by
    have hpt : ∀ j ∈ Finset.range (n + 1), ward_nsq (f ((finRotate L ^ j) a)) ≤
        E0 * (Real.exp (α * cycDist ((finRotate L ^ j) a) b) ^ 2 *
          ward_nsq (f ((finRotate L ^ j) a))) := by
      intro j hj
      have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have h5 := ward_cd_tri a ((finRotate L ^ j) a) b
      have h6 := ward_cd_pow a (j := j) (by omega)
      have h7 : (cycDist a b : ℝ) ≤ cycDist ((finRotate L ^ j) a) b + n := by
        have : cycDist a b ≤ cycDist ((finRotate L ^ j) a) b + n := by omega
        exact_mod_cast this
      have h8 : 1 ≤ E0 * Real.exp (α * cycDist ((finRotate L ^ j) a) b) ^ 2 := by
        rw [hE0, sq, ← Real.exp_add, ← Real.exp_add]
        refine Real.one_le_exp ?_
        nlinarith
      have h9 := ward_nsq_nonneg (f ((finRotate L ^ j) a))
      calc ward_nsq (f ((finRotate L ^ j) a))
          = 1 * ward_nsq (f ((finRotate L ^ j) a)) := (one_mul _).symm
        _ ≤ (E0 * Real.exp (α * cycDist ((finRotate L ^ j) a) b) ^ 2) *
            ward_nsq (f ((finRotate L ^ j) a)) := mul_le_mul_of_nonneg_right h8 h9
        _ = _ := by ring
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    exact ward_sum_arc_le a hnL' (fun c => Real.exp (α * cycDist c b) ^ 2 * ward_nsq (f c))
      (fun c => by have := ward_nsq_nonneg (f c); positivity)
  -- the weighted Ward inequality
  have h3 : η * S ≤ 2 * (star u ⬝ᵥ (blockOf G b b *ᵥ u)).im := by
    have h := weighted_ward hL U hUh E η α hη hη1 hα0 le_rfl b u
    dsimp only at h
    rw [← hHd] at h
    exact h
  have h4 := ward_im_le (blockOf G b b) u
  have h5 : S ≤ 2 * X * N / η := by
    rw [le_div_iff₀ hη]
    nlinarith
  have h6 : ward_nsq (f a) ≤ 2 * K ^ 2 / n * (E0 * (2 * X * N / η)) := by
    have h := h1
    change ward_nsq (f a) ≤ 2 * K ^ 2 / n *
      ∑ j ∈ Finset.range (n + 1), ward_nsq (f ((finRotate L ^ j) a)) at h
    refine h.trans (mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h5
      (Real.exp_pos _).le)) (by positivity))
  have hE0' : E0 = Real.exp (α * n) ^ 2 * Real.exp (-(α * cycDist a b)) ^ 2 := by
    rw [hE0, sq, sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h7 : (2 * K * Real.exp (η / 8 * n) * Real.exp (-(η / 8 * cycDist a b)) *
      Real.sqrt (X / (n * η))) ^ 2 * N = 2 * K ^ 2 / n * (E0 * (2 * X * N / η)) := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), hE0']
    simp only [← hα]
    field_simp
  rw [← h7] at h6
  exact h6


/-- From `Y ≤ r K √X` to `Y^p ≤ (r^p / 2) (K^{2p} + X^p)`. -/
private theorem ward_pow_bound {Y K X r : ℝ} (hY : 0 ≤ Y) (hX : 0 ≤ X)
    (hr : 0 ≤ r) (h : Y ≤ r * K * Real.sqrt X) (p : ℕ) :
    Y ^ p ≤ r ^ p / 2 * (K ^ (2 * p) + X ^ p) := by
  have h1 : Y ^ p ≤ (r * K * Real.sqrt X) ^ p := pow_le_pow_left₀ hY h p
  have h2 : (r * K * Real.sqrt X) ^ p = r ^ p * (K ^ p * Real.sqrt X ^ p) := by
    rw [mul_pow, mul_pow]; ring
  have h3 : K ^ (2 * p) = (K ^ p) ^ 2 := by rw [← pow_mul, mul_comm]
  have h4 : X ^ p = (Real.sqrt X ^ p) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hX]
  have h5 : K ^ p * Real.sqrt X ^ p ≤ ((K ^ p) ^ 2 + (Real.sqrt X ^ p) ^ 2) / 2 := by
    nlinarith [sq_nonneg (K ^ p - Real.sqrt X ^ p)]
  calc Y ^ p ≤ (r * K * Real.sqrt X) ^ p := h1
    _ = r ^ p * (K ^ p * Real.sqrt X ^ p) := h2
    _ ≤ r ^ p * (((K ^ p) ^ 2 + (Real.sqrt X ^ p) ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left h5 (pow_nonneg hr p)
    _ = r ^ p / 2 * (K ^ (2 * p) + X ^ p) := by rw [h3, h4]; ring

/-- The rate row of the seed tails: with `c₀ ≤ g² η ≤ C₀`, `g²/2 ≤ n ≤ g²`,
`2 e^{ηn/8} e^{-η d/8} / √(nη) ≤ (2 e^{C₀/8} / √(c₀/2)) e^{-(c₀/8) d / g²}`. -/
private theorem ward_rate_bound {g η c₀ C₀ : ℝ} {n d : ℕ} (hg0 : 0 < g ^ 2) (hc₀ : 0 < c₀)
    (hη : 0 < η) (hlo : c₀ ≤ g ^ 2 * η) (hhi : g ^ 2 * η ≤ C₀) (hn : (n : ℝ) ≤ g ^ 2)
    (hn2 : g ^ 2 / 2 ≤ n) :
    2 * Real.exp (η / 8 * n) * Real.exp (-(η / 8 * d)) / Real.sqrt (n * η) ≤
      2 * Real.exp (C₀ / 8) / Real.sqrt (c₀ / 2) * Real.exp (-(c₀ / 8 * d / g ^ 2)) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have h1 : Real.exp (η / 8 * n) ≤ Real.exp (C₀ / 8) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have h2 : Real.exp (-(η / 8 * d)) ≤ Real.exp (-(c₀ / 8 * d / g ^ 2)) := by
    refine Real.exp_le_exp.mpr ?_
    have : c₀ / 8 * d / g ^ 2 ≤ η / 8 * d := by
      rw [div_le_iff₀ hg0]
      nlinarith
    linarith
  have h3 : c₀ / 2 ≤ n * η := by nlinarith
  have h4 : Real.sqrt (c₀ / 2) ≤ Real.sqrt (n * η) := Real.sqrt_le_sqrt h3
  have h5 : 0 < Real.sqrt (c₀ / 2) := Real.sqrt_pos.mpr (by positivity)
  have h6 : 2 * Real.exp (η / 8 * n) * Real.exp (-(η / 8 * d)) ≤
      2 * Real.exp (C₀ / 8) * Real.exp (-(c₀ / 8 * d / g ^ 2)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 (Real.exp_pos _).le (by positivity)
  calc 2 * Real.exp (η / 8 * n) * Real.exp (-(η / 8 * d)) / Real.sqrt (n * η)
      ≤ 2 * Real.exp (C₀ / 8) * Real.exp (-(c₀ / 8 * d / g ^ 2)) / Real.sqrt (n * η) :=
        div_le_div_of_nonneg_right h6 (Real.sqrt_nonneg _)
    _ ≤ 2 * Real.exp (C₀ / 8) * Real.exp (-(c₀ / 8 * d / g ^ 2)) / Real.sqrt (c₀ / 2) :=
        div_le_div_of_nonneg_left (by positivity) h5 h4
    _ = _ := by ring


/-- (7.9) [uvc:eq:seed-tails] at each fixed time `t ∈ [0, 1]`: for `g ≥ C_κ`, `L ≥ 4g²`,
`|E| ≤ 2 - κ` and `c₀/g² ≤ η ≤ C₀/g²`, `E‖G_{ab}(E + iη)‖^p ≤ C_p e^{-pc d(a,b)/g²}`, with `c`
independent of `p` and no upper bound on `g` or `L`. -/
theorem seed_tails (κ c₀ C₀ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hc₀ : 0 < c₀) (hC₀ : c₀ ≤ C₀) :
    ∃ Cκ c : ℝ, 1 ≤ Cκ ∧ 0 < c ∧ ∀ p : ℕ, 1 ≤ p → ∃ Cp : ℝ, 0 < Cp ∧ ∀ W : ℕ, 4 * p ≤ W →
      ∀ g : ℝ, Cκ ≤ g → ∀ L : ℕ, 4 * g ^ 2 ≤ L → ∀ E η t : ℝ, |E| ≤ 2 - κ → c₀ / g ^ 2 ≤ η →
      η ≤ C₀ / g ^ 2 → 0 ≤ t → t ≤ 1 → ∀ a b : Fin L,
        Integrable (fun ω => ‖blockOf (resolventMat (flowH g W L t ω)
          ((E : ℂ) + (η : ℂ) * Complex.I)) a b‖ ^ p) (μ W L) ∧
        ∫ ω, ‖blockOf (resolventMat (flowH g W L t ω) ((E : ℂ) + (η : ℂ) * Complex.I)) a b‖ ^ p
          ∂(μ W L) ≤ Cp * Real.exp (-(p * c * cycDist a b / g ^ 2)) := by
  have _ := hκ2
  have hC₀0 : 0 < C₀ := lt_of_lt_of_le hc₀ hC₀
  refine ⟨max (max (2 / Real.sqrt κ) (Real.sqrt C₀)) 1, c₀ / 8, le_max_right _ _, by positivity, ?_⟩
  intro p hp1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
  obtain ⟨Cres, hCres0, hres⟩ := resolvent_moments κ (p : ℝ) C₀ hκ hp0 hC₀0
  obtain ⟨Carc, hCarc0, harc⟩ := arcK_moments κ C₀ ((2 * p : ℕ) : ℝ) hκ hC₀0.le (by positivity)
  set q : ℝ := 2 * Real.exp (C₀ / 8) / Real.sqrt (c₀ / 2) with hq
  have hq0 : 0 < q := by positivity
  set R : ℝ := Cres * (c₀ ^ p)⁻¹ with hR
  have hR0 : 0 < R := by positivity
  refine ⟨R * Real.exp (p * (c₀ / 8)) + q ^ p * (Carc + R), by positivity, ?_⟩
  intro W hW g hg L hL E η t hE hηlo hηhi ht0 ht1 a b
  have hg1 : 2 / Real.sqrt κ ≤ g := (le_max_left _ _).trans ((le_max_left _ _).trans hg)
  have hg2 : Real.sqrt C₀ ≤ g := (le_max_right _ _).trans ((le_max_left _ _).trans hg)
  have hg3 : 1 ≤ g := (le_max_right _ _).trans hg
  have hgsq : 1 ≤ g ^ 2 := one_le_pow₀ hg3
  have hg0 : 0 < g ^ 2 := by linarith
  have hlo : c₀ ≤ g ^ 2 * η := by rwa [div_le_iff₀ hg0, mul_comm] at hηlo
  have hhi : g ^ 2 * η ≤ C₀ := by rwa [le_div_iff₀ hg0, mul_comm] at hηhi
  have hη0 : 0 < η := (mul_pos_iff_of_pos_left hg0).mp (lt_of_lt_of_le hc₀ hlo)
  have hC₀g : C₀ ≤ g ^ 2 := by
    have := Real.sq_sqrt hC₀0.le
    nlinarith [Real.sqrt_nonneg C₀]
  have hη1 : η ≤ 1 := by
    by_contra h
    have h' := not_le.mp h
    nlinarith
  -- the moments of the resolvent entries
  have hres' : ∀ a' b' : Fin L,
      Integrable (fun ω => ‖blockOf (resolventMat (flowH g W L t ω)
        ((E : ℂ) + (η : ℂ) * Complex.I)) a' b'‖ ^ p) (μ W L) ∧
      ∫ ω, ‖blockOf (resolventMat (flowH g W L t ω) ((E : ℂ) + (η : ℂ) * Complex.I)) a' b'‖ ^ p
        ∂(μ W L) ≤ R := by
    intro a' b'
    have h := hres W (by exact_mod_cast hW) L g hg1 hL E η t hE hη0 hηhi ht0 ht1 a' b'
    simp only [Real.rpow_natCast] at h
    refine ⟨h.1, h.2.trans ?_⟩
    have h1 : (g ^ 2 * η) ^ (-(p : ℝ)) ≤ (c₀ ^ p)⁻¹ := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
      exact inv_anti₀ (pow_pos hc₀ p) (pow_le_pow_left₀ hc₀.le hlo p)
    exact mul_le_mul_of_nonneg_left h1 hCres0.le
  by_cases hd : cycDist a b ≤ ⌊g ^ 2⌋₊
  · -- near the diagonal: Lemma 5.5 [fo:lem:resolvent-moments]
    refine ⟨(hres' a b).1, (hres' a b).2.trans ?_⟩
    have hdg : (cycDist a b : ℝ) ≤ g ^ 2 := (Nat.cast_le.mpr hd).trans (Nat.floor_le hg0.le)
    have hexp : 1 ≤ Real.exp (p * (c₀ / 8)) *
        Real.exp (-(p * (c₀ / 8) * cycDist a b / g ^ 2)) := by
      rw [← Real.exp_add]
      refine Real.one_le_exp ?_
      have : (p : ℝ) * (c₀ / 8) * cycDist a b / g ^ 2 ≤ p * (c₀ / 8) := by
        rw [div_le_iff₀ hg0]
        have : (0 : ℝ) ≤ p * (c₀ / 8) := by positivity
        nlinarith
      linarith
    have hE1 := Real.exp_pos (-(p * (c₀ / 8) * cycDist a b / g ^ 2))
    calc R ≤ R * (Real.exp (p * (c₀ / 8)) * Real.exp (-(p * (c₀ / 8) * cycDist a b / g ^ 2))) :=
          le_mul_of_one_le_right hR0.le hexp
      _ = R * Real.exp (p * (c₀ / 8)) * Real.exp (-(p * (c₀ / 8) * cycDist a b / g ^ 2)) := by
          ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ hE1.le
          have : 0 ≤ q ^ p * (Carc + R) := by positivity
          linarith
  · -- far from the diagonal: the arc inequality and the weighted Ward inequality
    have hd' := not_le.mp hd
    set n : ℕ := ⌊g ^ 2⌋₊ with hn
    have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hgsq)
    have hnle : (n : ℝ) ≤ g ^ 2 := Nat.floor_le hg0.le
    have hhalf : g ^ 2 / 2 ≤ n := by
      have h1 := Nat.lt_floor_add_one (g ^ 2)
      have h2 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      linarith
    have h4n : 4 * n ≤ L := by
      have : ((4 * n : ℕ) : ℝ) ≤ L := by push_cast; linarith
      exact_mod_cast this
    have hL3 : 3 ≤ L := by omega
    have h2n : 2 * n + 1 ≤ L := by omega
    refine ⟨(hres' a b).1, ?_⟩
    have hK := harc W L (by
      have : 2 * (2 * p) ≤ W := by omega
      exact_mod_cast this) g hg1 n (by omega) hnle E η t hE
      (by rw [abs_of_pos hη0]; exact hη1)
      (by rw [abs_of_pos hη0]; nlinarith) ht0 ht1 a true
    simp only [Real.rpow_natCast] at hK
    set Bc : ℝ := q ^ p * Real.exp (-(p * (c₀ / 8) * cycDist a b / g ^ 2)) / 2 with hBc
    have hBc0 : 0 ≤ Bc := by positivity
    have hpt : ∀ ω : Ω W L, ‖blockOf (resolventMat (flowH g W L t ω)
        ((E : ℂ) + (η : ℂ) * Complex.I)) a b‖ ^ p ≤
        Bc * (arcK g ((E : ℂ) + (η : ℂ) * Complex.I)
          (fun c => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω c) a true n ^ (2 * p) +
          ‖blockOf (resolventMat (flowH g W L t ω) ((E : ℂ) + (η : ℂ) * Complex.I)) b b‖ ^ p) := by
      intro ω
      have hflow : flowH g W L t ω = Hdet g (fun c => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω c) :=
        blockFlow_Ag_eq_Hdet g t W L ω
      rw [hflow]
      have hVh : ∀ c, ((((Real.sqrt t : ℝ) : ℂ)) • gueBlock W L ω c).IsHermitian := fun c =>
        ward_isHermitian_smul_real (gueBlock_isHermitian W L ω c) _
      have hdec := ward_green_decay hL3 hg3 (fun c => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω c)
        hVh E η hη0 hη1 hn1 h2n a b hd'
      set K := arcK g ((E : ℂ) + (η : ℂ) * Complex.I)
        (fun c => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω c) a true n with hKdef
      set Xn := ‖blockOf (resolventMat
        (Hdet g (fun c => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω c))
        ((E : ℂ) + (η : ℂ) * Complex.I)) b b‖ with hXn
      have hK0 : 0 ≤ K := Real.iSup_nonneg fun _ => norm_nonneg _
      have hrate := ward_rate_bound (d := cycDist a b) hg0 hc₀ hη0 hlo hhi hnle hhalf
      set r : ℝ := q * Real.exp (-(c₀ / 8 * cycDist a b / g ^ 2)) with hr
      have hr0 : 0 ≤ r := by positivity
      have hY : ‖blockOf (resolventMat (Hdet g (fun c => ((Real.sqrt t : ℝ) : ℂ) •
          gueBlock W L ω c)) ((E : ℂ) + (η : ℂ) * Complex.I)) a b‖ ≤ r * K * Real.sqrt Xn := by
        refine hdec.trans ?_
        have hnη : (0 : ℝ) ≤ n * η := by positivity
        have : 2 * K * Real.exp (η / 8 * n) * Real.exp (-(η / 8 * cycDist a b)) *
            Real.sqrt (Xn / (n * η)) =
            (2 * Real.exp (η / 8 * n) * Real.exp (-(η / 8 * cycDist a b)) /
              Real.sqrt (n * η)) * (K * Real.sqrt Xn) := by
          rw [Real.sqrt_div (norm_nonneg _)]
          ring
        rw [this]
        calc _ ≤ r * (K * Real.sqrt Xn) :=
              mul_le_mul_of_nonneg_right hrate (mul_nonneg hK0 (Real.sqrt_nonneg _))
          _ = r * K * Real.sqrt Xn := by ring
      have hp := ward_pow_bound (norm_nonneg _) (norm_nonneg _) hr0 hY p
      have hrp : r ^ p = q ^ p * Real.exp (-(p * (c₀ / 8) * cycDist a b / g ^ 2)) := by
        rw [hr, mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring
      rw [hrp] at hp
      exact hp.trans (le_of_eq (by rw [hBc]))
    have hXint := (hres' b b).1
    have hdom : Integrable (fun ω : Ω W L => Bc * (arcK g ((E : ℂ) + (η : ℂ) * Complex.I)
        (fun c => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω c) a true n ^ (2 * p) +
        ‖blockOf (resolventMat (flowH g W L t ω) ((E : ℂ) + (η : ℂ) * Complex.I)) b b‖ ^ p))
        (μ W L) := (hK.1.add hXint).const_mul Bc
    have hI := integral_mono (hres' a b).1 hdom hpt
    rw [integral_const_mul, integral_add hK.1 hXint] at hI
    have hsum := add_le_add hK.2 (hres' b b).2
    have hE1 := Real.exp_pos (-(p * (c₀ / 8) * cycDist a b / g ^ 2))
    refine hI.trans ?_
    calc Bc * (_ + _) ≤ Bc * (Carc + R) := mul_le_mul_of_nonneg_left hsum hBc0
      _ ≤ (q ^ p * (Carc + R)) * Real.exp (-(p * (c₀ / 8) * cycDist a b / g ^ 2)) := by
          rw [hBc]
          have : 0 ≤ q ^ p * (Carc + R) * Real.exp (-(p * (c₀ / 8) * cycDist a b / g ^ 2)) := by
            positivity
          nlinarith
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ hE1.le
          have : 0 ≤ R * Real.exp (p * (c₀ / 8)) := by positivity
          linarith

end LSBA
