import LSBA.Upper.SmallGenerator

/-!
# The active-chain matrix

Section 9.4.2 [su:sec:discarded-output]. The active-chain matrix `H` on `ℂ^{q-5} ⊗ ℂ^W` has
diagonal blocks `V_5 - E - g² R_4, V_6 - E, …, V_{q-1} - E` and blocks `g I` between neighbours.
Eliminating from the first block gives the forward Schur complements `R_j⁻¹` (`5 ≤ j ≤ q - 1`);
eliminating from the last gives the right-cavity complements `R←_j⁻¹` and `R̃⁻¹`. The exact Schur
identities give `R̃ = (H⁻¹)_{11}`, `R_{q-1} = (H⁻¹)_{q-5, q-5}` and
`(H⁻¹)_{q-5, 1} = (-g)^{q-6} R_{q-1} ⋯ R_5`, hence (9.66) [su:eq:active-chain-inverse] with
`‖H⁻¹‖` in place of `W³`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The active-chain matrix of Section 9.4.2 [su:sec:discarded-output]: block `(k, k)` is
`V_{k+5} - E - [k = 0] g² R_4`, blocks `(k, k ± 1)` are `g I`, the others vanish. -/
def activeMat (W : ℕ) (g E : ℝ) (q : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) :
    Matrix (Fin (q - 5) × Fin W) (Fin (q - 5) × Fin W) ℂ :=
  Matrix.of fun x y =>
    if x.1 = y.1 then
      (blockSeq W q ω ((x.1 : ℕ) + 4) - (E : ℂ) • 1 -
        (if (x.1 : ℕ) = 0 then ((g : ℂ) ^ 2) • R else 0)) x.2 y.2
    else if (x.1 : ℕ) + 1 = (y.1 : ℕ) ∨ (y.1 : ℕ) + 1 = (x.1 : ℕ) then
      (if x.2 = y.2 then (g : ℂ) else 0)
    else 0

/-- The embedding of block `l` of `ℂ^n ⊗ ℂ^W`; it vanishes for `l ≥ n`. -/
private def activeChain_emb (n W l : ℕ) : Matrix (Fin n × Fin W) (Fin W) ℂ :=
  Matrix.of fun x j => if (x.1 : ℕ) = l ∧ x.2 = j then 1 else 0

/-- The diagonal block `l` of the active-chain matrix. -/
private def activeChain_diag (W : ℕ) (g E : ℝ) (q : ℕ) (R : Matrix (Fin W) (Fin W) ℂ)
    (ω : Ω W q) (l : ℕ) : Matrix (Fin W) (Fin W) ℂ :=
  blockSeq W q ω (l + 4) - (E : ℂ) • 1 - (if l = 0 then ((g : ℂ) ^ 2) • R else 0)

private lemma activeChain_mul_emb {ι : Type} {n W l : ℕ} (hl : l < n)
    (A : Matrix ι (Fin n × Fin W) ℂ) (i : ι) (j : Fin W) :
    (A * activeChain_emb n W l) i j = A i (⟨l, hl⟩, j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨l, hl⟩, j)]
  · simp [activeChain_emb]
  · rintro ⟨⟨a, ha⟩, b⟩ _ hne
    simp only [activeChain_emb, Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_eq_right_iff,
      and_imp]
    rintro rfl rfl
    exact absurd rfl hne
  · simp

private lemma activeChain_emb_eq_zero {n W l : ℕ} (hl : n ≤ l) : activeChain_emb n W l = 0 := by
  ext x j
  simp only [activeChain_emb, Matrix.of_apply, Matrix.zero_apply, ite_eq_right_iff, and_imp]
  intro h
  omega

private lemma activeChain_emb_mul {ι : Type} {n W l : ℕ} (hl : l < n)
    (A : Matrix (Fin n × Fin W) ι ℂ) (i : Fin W) (j : ι) :
    ((activeChain_emb n W l)ᴴ * A) i j = A (⟨l, hl⟩, i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨l, hl⟩, i)]
  · simp [activeChain_emb]
  · rintro ⟨⟨a, ha⟩, b⟩ _ hne
    have h : ¬ (a = l ∧ b = i) := by
      rintro ⟨rfl, rfl⟩
      exact hne rfl
    simp [activeChain_emb, h]
  · simp

private lemma activeChain_emb_emb {n W a b : ℕ} (ha : a < n) :
    (activeChain_emb n W a)ᴴ * activeChain_emb n W b = if a = b then 1 else 0 := by
  ext i j
  rw [activeChain_emb_mul ha]
  split_ifs with h
  · subst h; simp [activeChain_emb, Matrix.one_apply]
  · simp [activeChain_emb, h]

private lemma activeChain_norm_emb {n W l : ℕ} : ‖activeChain_emb n W l‖ ≤ 1 := by
  rcases lt_or_ge l n with hl | hl
  · have h1 := Matrix.l2_opNorm_conjTranspose_mul_self (activeChain_emb n W l)
    rw [activeChain_emb_emb hl] at h1
    simp only [↓reduceIte] at h1
    have h2 : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := by
      rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp
    nlinarith [norm_nonneg (activeChain_emb n W l)]
  · rw [activeChain_emb_eq_zero hl, norm_zero]
    exact zero_le_one

private lemma activeChain_emb_mul_apply {n W l : ℕ} (B : Matrix (Fin W) (Fin W) ℂ) (a : Fin n)
    (i j : Fin W) :
    (activeChain_emb n W l * B) (a, i) j = if (a : ℕ) = l then B i j else 0 := by
  by_cases h : (a : ℕ) = l <;> simp [activeChain_emb, Matrix.mul_apply, h]

private lemma activeChain_embT {n W l : ℕ} :
    (activeChain_emb n W l)ᴴ = Matrix.of fun j x => if (x.1 : ℕ) = l ∧ x.2 = j then 1 else 0 := by
  ext j x
  simp only [activeChain_emb, Matrix.conjTranspose_apply, Matrix.of_apply]
  split_ifs <;> simp

private lemma activeChain_mul_embT_apply {n W l : ℕ} (B : Matrix (Fin W) (Fin W) ℂ) (a : Fin n)
    (i j : Fin W) :
    (B * (activeChain_emb n W l)ᴴ) i (a, j) = if (a : ℕ) = l then B i j else 0 := by
  rw [activeChain_embT]
  by_cases h : (a : ℕ) = l <;> simp [Matrix.mul_apply, h]

private lemma activeChain_H_emb {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ} {ω : Ω W q}
    {l : ℕ} (hl : l < q - 5) :
    activeMat W g E q R ω * activeChain_emb (q - 5) W l =
      activeChain_emb (q - 5) W l * activeChain_diag W g E q R ω l +
        (g : ℂ) • ((if 1 ≤ l then activeChain_emb (q - 5) W (l - 1) else 0) +
          activeChain_emb (q - 5) W (l + 1)) := by
  split_ifs with h0 <;>
  · ext ⟨⟨a, ha⟩, i⟩ j
    rw [activeChain_mul_emb hl, Matrix.add_apply, activeChain_emb_mul_apply]
    simp only [activeMat, activeChain_diag, activeChain_emb, Matrix.of_apply, Matrix.smul_apply,
      Matrix.add_apply, Fin.mk.injEq, smul_eq_mul, Matrix.zero_apply]
    split_ifs <;> first | (exfalso; omega) | (subst_vars; simp)

private lemma activeChain_emb_H {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ} {ω : Ω W q}
    {l : ℕ} (hl : l < q - 5) :
    (activeChain_emb (q - 5) W l)ᴴ * activeMat W g E q R ω =
      activeChain_diag W g E q R ω l * (activeChain_emb (q - 5) W l)ᴴ +
        (g : ℂ) • ((if 1 ≤ l then (activeChain_emb (q - 5) W (l - 1))ᴴ else 0) +
          (activeChain_emb (q - 5) W (l + 1))ᴴ) := by
  split_ifs with h0 <;>
  · ext i ⟨⟨a, ha⟩, j⟩
    rw [activeChain_emb_mul hl, Matrix.add_apply, activeChain_mul_embT_apply]
    simp only [activeChain_embT, activeMat, activeChain_diag, Matrix.of_apply, Matrix.smul_apply,
      Matrix.add_apply, Fin.mk.injEq, smul_eq_mul, Matrix.zero_apply]
    split_ifs <;> first | (exfalso; omega) | (subst_vars; simp)

/-- The forward Schur complement `V_{l+5} - E - g² R_{l+4}`, so that `R_{l+5}` is its inverse. -/
private def activeChain_fwd (W : ℕ) (g E : ℝ) (q : ℕ) (R : Matrix (Fin W) (Fin W) ℂ)
    (ω : Ω W q) (l : ℕ) : Matrix (Fin W) (Fin W) ℂ :=
  blockSeq W q ω (l + 4) - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • chartR W g E q R ω (l + 4)

private lemma activeChain_chartR_eq {W : ℕ} {g E : ℝ} {q : ℕ} {R : Matrix (Fin W) (Fin W) ℂ}
    {ω : Ω W q} (l : ℕ) :
    chartR W g E q R ω (l + 5) = (activeChain_fwd W g E q R ω l)⁻¹ := by
  change chartR W g E q R ω (l + 4 + 1) = _
  rw [chartR, ite_eq_right (by omega)]
  rfl

private lemma activeChain_chartR_four {W : ℕ} {g E : ℝ} {q : ℕ} {R : Matrix (Fin W) (Fin W) ℂ}
    {ω : Ω W q} : chartR W g E q R ω 4 = R := by
  change chartR W g E q R ω (3 + 1) = R
  rw [chartR, ite_eq_left (by omega)]

private lemma activeChain_chartProd_succ {W : ℕ} {g E : ℝ} {q : ℕ}
    {R : Matrix (Fin W) (Fin W) ℂ} {ω : Ω W q} (l : ℕ) :
    chartProd W g E q R ω (l + 5) = chartR W g E q R ω (l + 5) * chartProd W g E q R ω (l + 4) := by
  change chartProd W g E q R ω (l + 4 + 1) = _
  rw [chartProd, ite_eq_right (by omega)]

private lemma activeChain_chartProd_four {W : ℕ} {g E : ℝ} {q : ℕ}
    {R : Matrix (Fin W) (Fin W) ℂ} {ω : Ω W q} : chartProd W g E q R ω 4 = 1 := by
  change chartProd W g E q R ω (3 + 1) = 1
  rw [chartProd, ite_eq_left (by omega)]

private lemma activeChain_diag_eq {W : ℕ} {g E : ℝ} {q : ℕ} {R : Matrix (Fin W) (Fin W) ℂ}
    {ω : Ω W q} (l : ℕ) :
    activeChain_diag W g E q R ω l = activeChain_fwd W g E q R ω l +
      (if l = 0 then 0 else ((g : ℂ) ^ 2) • chartR W g E q R ω (l + 4)) := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp [activeChain_diag, activeChain_fwd, activeChain_chartR_four]
  · simp only [activeChain_diag, activeChain_fwd, ite_eq_right hl.ne']
    abel

/-- Forward elimination: a block row `Z` with `Z H = c ⊗ e_{q-6}ᵀ` has blocks
`Z_{q-6} = c R_{q-1}` and `Z_l = -g Z_{l+1} R_{l+5}`. -/
private lemma activeChain_fwd_rec {ι : Type} {W q : ℕ} (hq : 7 ≤ q) {g E : ℝ}
    {R : Matrix (Fin W) (Fin W) ℂ} {ω : Ω W q}
    (hC : ∀ j, 5 ≤ j → j ≤ q - 1 → IsUnit (chartR W g E q R ω j))
    (Z : Matrix ι (Fin (q - 5) × Fin W) ℂ) (c : Matrix ι (Fin W) ℂ)
    (hZ : ∀ l, l < q - 5 → Z * activeMat W g E q R ω * activeChain_emb (q - 5) W l =
      if l = q - 6 then c else 0) :
    Z * activeChain_emb (q - 5) W (q - 6) = c * chartR W g E q R ω (q - 1) ∧
    ∀ l, l + 1 < q - 5 → Z * activeChain_emb (q - 5) W l =
      -(g : ℂ) • (Z * activeChain_emb (q - 5) W (l + 1)) * chartR W g E q R ω (l + 5) := by
  have hU : ∀ l, l < q - 5 →
      activeChain_fwd W g E q R ω l * chartR W g E q R ω (l + 5) = 1 := by
    intro l hl
    have h := hC (l + 5) (by omega) (by omega)
    rw [activeChain_chartR_eq, Matrix.isUnit_nonsing_inv_iff] at h
    rw [activeChain_chartR_eq]
    exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 h)
  have hcol : ∀ l, l < q - 5 →
      Z * activeChain_emb (q - 5) W l * activeChain_diag W g E q R ω l +
        (g : ℂ) • ((if 1 ≤ l then Z * activeChain_emb (q - 5) W (l - 1) else 0) +
          Z * activeChain_emb (q - 5) W (l + 1)) = if l = q - 6 then c else 0 := by
    intro l hl
    rw [← hZ l hl, Matrix.mul_assoc Z (activeMat W g E q R ω), activeChain_H_emb hl]
    split_ifs <;> simp [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc]
  have hstep : ∀ l, l < q - 5 →
      Z * activeChain_emb (q - 5) W l * activeChain_fwd W g E q R ω l +
        (g : ℂ) • (Z * activeChain_emb (q - 5) W (l + 1)) = 0 →
      Z * activeChain_emb (q - 5) W l =
        -(g : ℂ) • (Z * activeChain_emb (q - 5) W (l + 1)) * chartR W g E q R ω (l + 5) := by
    intro l hl h
    calc Z * activeChain_emb (q - 5) W l
        = Z * activeChain_emb (q - 5) W l * activeChain_fwd W g E q R ω l *
            chartR W g E q R ω (l + 5) := by
              rw [Matrix.mul_assoc (Z * activeChain_emb (q - 5) W l), hU l hl, Matrix.mul_one]
      _ = _ := by rw [eq_neg_of_add_eq_zero_left h, neg_smul]
  have hQ : ∀ l, l < q - 5 →
      Z * activeChain_emb (q - 5) W l * activeChain_fwd W g E q R ω l +
        (g : ℂ) • (Z * activeChain_emb (q - 5) W (l + 1)) = if l = q - 6 then c else 0 := by
    intro l
    induction l with
    | zero =>
      intro hl
      have h := hcol 0 hl
      rw [activeChain_diag_eq] at h
      simpa using h
    | succ l ih =>
      intro hl
      have h1 := ih (by omega)
      rw [ite_eq_right (by omega)] at h1
      have h2 := hstep l (by omega) h1
      have h3 := hcol (l + 1) hl
      rw [activeChain_diag_eq, ite_eq_right (by omega), ite_eq_left (by omega),
        show l + 1 - 1 = l by omega, h2] at h3
      rw [← h3]
      simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_assoc, smul_add, smul_smul]
      module
  refine ⟨?_, fun l hl => hstep l (by omega) (by rw [hQ l (by omega), ite_eq_right (by omega)])⟩
  have h := hQ (q - 6) (by omega)
  rw [show q - 6 + 1 = q - 5 by omega, activeChain_emb_eq_zero le_rfl, Matrix.mul_zero,
    smul_zero, add_zero, ite_eq_left rfl] at h
  rw [← h, Matrix.mul_assoc, show q - 1 = q - 6 + 5 by omega, hU _ (by omega), Matrix.mul_one]

/-- The right-cavity Schur complements: `cavR … m` is the inverse of `activeChain_bwd … m`. -/
private def activeChain_bwd (W : ℕ) (g E : ℝ) (q : ℕ) (ω : Ω W q) :
    ℕ → Matrix (Fin W) (Fin W) ℂ
  | 0 => blockSeq W q ω (q - 2) - (E : ℂ) • 1
  | m + 1 => blockSeq W q ω (q - 3 - m) - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • cavR W g E q ω m

private lemma activeChain_cavR_eq {W : ℕ} {g E : ℝ} {q : ℕ} {ω : Ω W q} (m : ℕ) :
    cavR W g E q ω m = (activeChain_bwd W g E q ω m)⁻¹ := by
  cases m <;> rfl

/-- Backward elimination: a block column `X` with `H X = e_0 ⊗ I` has block `X_0 = R̃`. -/
private lemma activeChain_bwd_rec {W q : ℕ} (hq : 7 ≤ q) {g E : ℝ}
    {R : Matrix (Fin W) (Fin W) ℂ} {ω : Ω W q}
    (hK : ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω m))
    (X : Matrix (Fin (q - 5) × Fin W) (Fin W) ℂ)
    (hX : activeMat W g E q R ω * X = activeChain_emb (q - 5) W 0) :
    (activeChain_emb (q - 5) W 0)ᴴ * X = cavRes W g E q R ω := by
  set Xb : ℕ → Matrix (Fin W) (Fin W) ℂ := fun l => (activeChain_emb (q - 5) W l)ᴴ * X with hXb
  have hXn : Xb (q - 5) = 0 := by
    simp only [hXb, activeChain_emb_eq_zero le_rfl, Matrix.conjTranspose_zero, Matrix.zero_mul]
  have hU : ∀ m, m ≤ q - 7 → cavR W g E q ω m * activeChain_bwd W g E q ω m = 1 := by
    intro m hm
    have h := hK m hm
    rw [activeChain_cavR_eq, Matrix.isUnit_nonsing_inv_iff] at h
    rw [activeChain_cavR_eq]
    exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 h)
  have hrow : ∀ l, l < q - 5 →
      activeChain_diag W g E q R ω l * Xb l +
        (g : ℂ) • ((if 1 ≤ l then Xb (l - 1) else 0) + Xb (l + 1)) =
        if l = 0 then 1 else 0 := by
    intro l hl
    rw [← activeChain_emb_emb hl, ← hX, ← Matrix.mul_assoc (activeChain_emb (q - 5) W l)ᴴ,
      activeChain_emb_H hl]
    split_ifs <;> simp [hXb, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc]
  have hstep : ∀ m, m ≤ q - 7 →
      activeChain_bwd W g E q ω m * Xb (q - 6 - m) + (g : ℂ) • Xb (q - 7 - m) = 0 →
      Xb (q - 6 - m) = -(g : ℂ) • (cavR W g E q ω m * Xb (q - 7 - m)) := by
    intro m hm h
    calc Xb (q - 6 - m) = cavR W g E q ω m * (activeChain_bwd W g E q ω m * Xb (q - 6 - m)) := by
          rw [← Matrix.mul_assoc, hU m hm, Matrix.one_mul]
      _ = _ := by rw [eq_neg_of_add_eq_zero_left h, Matrix.mul_neg, Matrix.mul_smul, neg_smul]
  have hQ : ∀ m, m ≤ q - 7 →
      activeChain_bwd W g E q ω m * Xb (q - 6 - m) + (g : ℂ) • Xb (q - 7 - m) = 0 := by
    intro m
    induction m with
    | zero =>
      intro _
      have h := hrow (q - 6) (by omega)
      rw [ite_eq_right (show ¬ (q - 6 = 0) by omega), ite_eq_left (show 1 ≤ q - 6 by omega),
        show q - 6 - 1 = q - 7 by omega,
        show q - 6 + 1 = q - 5 by omega, hXn, add_zero] at h
      rw [← h]
      simp only [activeChain_bwd, activeChain_diag, ite_eq_right (show ¬ (q - 6 = 0) by omega),
        show q - 6 + 4 = q - 2 by omega, sub_zero, Nat.sub_zero]
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have h2 := hstep m (by omega) h1
      have h3 := hrow (q - 7 - m) (by omega)
      rw [ite_eq_right (show ¬ (q - 7 - m = 0) by omega), ite_eq_left (show 1 ≤ q - 7 - m by omega),
        show q - 7 - m - 1 = q - 7 - (m + 1) by omega,
        show q - 7 - m + 1 = q - 6 - m by omega, h2] at h3
      rw [show q - 6 - (m + 1) = q - 7 - m by omega, ← h3]
      simp only [activeChain_bwd, activeChain_diag, ite_eq_right (show ¬ (q - 7 - m = 0) by omega),
        show q - 7 - m + 4 = q - 3 - m by omega, sub_zero, Matrix.sub_mul, smul_add, smul_smul,
        Matrix.smul_mul]
      module
  have h1 := hstep (q - 7) le_rfl (hQ (q - 7) le_rfl)
  have h0 := hrow 0 (by omega)
  rw [show q - 6 - (q - 7) = 1 by omega, show q - 7 - (q - 7) = 0 by omega] at h1
  rw [ite_eq_right (show ¬ (1 ≤ 0) by omega), ite_eq_left (rfl : (0 : ℕ) = 0), zero_add,
    zero_add] at h0
  rw [h1] at h0
  have hM : (blockSeq W q ω 4 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R -
      ((g : ℂ) ^ 2) • cavR W g E q ω (q - 7)) * Xb 0 = 1 := by
    conv_rhs => rw [← h0]
    simp only [activeChain_diag, ↓reduceIte, Nat.zero_add, Matrix.sub_mul, smul_smul,
      Matrix.smul_mul, Matrix.one_mul]
    module
  exact (Matrix.inv_eq_right_inv hM).symm

/-- A block `(a, b)` of a matrix on `ℂ^n ⊗ ℂ^W` has norm at most that of the matrix. -/
private lemma activeChain_norm_block {n W : ℕ}
    (G : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) (a b : ℕ) :
    ‖(activeChain_emb n W a)ᴴ * G * activeChain_emb n W b‖ ≤ ‖G‖ := by
  calc ‖(activeChain_emb n W a)ᴴ * G * activeChain_emb n W b‖
      ≤ ‖(activeChain_emb n W a)ᴴ * G‖ * ‖activeChain_emb n W b‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖(activeChain_emb n W a)ᴴ‖ * ‖G‖) * 1 := by
        gcongr
        · exact Matrix.l2_opNorm_mul _ _
        · exact activeChain_norm_emb
    _ ≤ (1 * ‖G‖) * 1 := by
        gcongr
        rw [Matrix.l2_opNorm_conjTranspose]
        exact activeChain_norm_emb
    _ = ‖G‖ := by ring

/-- (9.66) [su:eq:active-chain-inverse], Schur form: where `R_5, …, R_{q-1}`, the right-cavity
inverses and `R̃` exist, `H` is invertible and `‖R̃‖`, `‖R_{q-1}‖` and
`g^{q-6} ‖R_{[q-1,5]}‖` are at most `‖H⁻¹‖`. -/
theorem activeMat_schur {W q : ℕ} (hq : 7 ≤ q) {g E : ℝ} (hg : 0 ≤ g)
    {R : Matrix (Fin W) (Fin W) ℂ} (hR : R.IsHermitian) (ω : Ω W q)
    (hC : ∀ j, 5 ≤ j → j ≤ q - 1 → IsUnit (chartR W g E q R ω j))
    (hK : ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω m)) (hT : IsUnit (cavRes W g E q R ω)) :
    IsUnit (activeMat W g E q R ω) ∧
      ‖cavRes W g E q R ω‖ ≤ ‖(activeMat W g E q R ω)⁻¹‖ ∧
      ‖chartR W g E q R ω (q - 1)‖ ≤ ‖(activeMat W g E q R ω)⁻¹‖ ∧
      g ^ (q - 6) * ‖chartProd W g E q R ω (q - 1)‖ ≤ ‖(activeMat W g E q R ω)⁻¹‖ := by
  set H := activeMat W g E q R ω with hH
  -- invertibility: the left kernel of `H` is trivial
  have hunit : IsUnit H := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
    apply hv0
    set Z : Matrix Unit (Fin (q - 5) × Fin W) ℂ := Matrix.of fun _ x => v x with hZ
    have hZH : Z * H = 0 := by
      ext u y
      have := congr_fun hv y
      simpa [hZ, Matrix.mul_apply, Matrix.vecMul, dotProduct] using this
    obtain ⟨h1, h2⟩ := activeChain_fwd_rec hq hC Z 0 fun l _ => by
      rw [hZH, Matrix.zero_mul]
      split_ifs <;> rfl
    rw [Matrix.zero_mul] at h1
    have hzero : ∀ m, m < q - 5 → Z * activeChain_emb (q - 5) W (q - 6 - m) = 0 := by
      intro m
      induction m with
      | zero => intro _; simpa using h1
      | succ m ih =>
        intro hm
        rw [h2 (q - 6 - (m + 1)) (by omega), show q - 6 - (m + 1) + 1 = q - 6 - m by omega,
          ih (by omega)]
        simp
    ext ⟨⟨a, ha⟩, i⟩
    have := congr_fun₂ (hzero (q - 6 - a) (by omega)) () i
    rw [show q - 6 - (q - 6 - a) = a by omega, activeChain_mul_emb ha] at this
    simpa [hZ] using this
  have hdet := (Matrix.isUnit_iff_isUnit_det H).1 hunit
  have hGH : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H hdet
  have hHG : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hdet
  -- the last block row of `H⁻¹`
  set Z := (activeChain_emb (q - 5) W (q - 6))ᴴ * H⁻¹ with hZ
  obtain ⟨h1, h2⟩ := activeChain_fwd_rec hq hC Z 1 fun l hl => by
    rw [hZ, Matrix.mul_assoc _ H⁻¹ H, hGH, Matrix.mul_one, activeChain_emb_emb (by omega)]
    by_cases h : l = q - 6
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
  rw [Matrix.one_mul] at h1
  have hchain : ∀ l, l ≤ q - 6 → Z * activeChain_emb (q - 5) W 0 =
      (-(g : ℂ)) ^ l • (Z * activeChain_emb (q - 5) W l) * chartProd W g E q R ω (l + 4) := by
    intro l
    induction l with
    | zero => intro _; simp [activeChain_chartProd_four]
    | succ l ih =>
      intro hl
      rw [ih (by omega), h2 l (by omega), show l + 1 + 4 = l + 5 by omega,
        activeChain_chartProd_succ, pow_succ]
      simp only [Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
  have h0 := hchain (q - 6) le_rfl
  rw [h1, Matrix.smul_mul, show q - 1 = q - 6 + 5 by omega, ← activeChain_chartProd_succ] at h0
  -- the first block column of `H⁻¹`
  have hT' := activeChain_bwd_rec hq (R := R) hK (H⁻¹ * activeChain_emb (q - 5) W 0)
    (by rw [← Matrix.mul_assoc, hHG, Matrix.one_mul])
  refine ⟨hunit, ?_, ?_, ?_⟩
  · rw [← hT', ← Matrix.mul_assoc]
    exact activeChain_norm_block _ _ _
  · rw [← h1, hZ]
    exact activeChain_norm_block _ _ _
  · have hn : ‖(-(g : ℂ)) ^ (q - 6)‖ = g ^ (q - 6) := by
      rw [norm_pow, norm_neg, Complex.norm_real, Real.norm_of_nonneg hg]
    rw [← hn, ← norm_smul, show q - 1 = q - 6 + 5 by omega, ← h0, hZ]
    exact activeChain_norm_block _ _ _

end LSBA
