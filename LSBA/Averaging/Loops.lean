import LSBA.Averaging.Branch
import LSBA.Primitive.Large
import LSBA.Loop.ErrorHierarchy
import LSBA.Flow.Moment
import LSBA.Prop.Domination
import LSBA.Flow.Comparison
import LSBA.Prop.Ward
import LSBA.Averaging.LoopsStep

/-!
# Loops in Lemma 5.6 [fo:prop:inputs]

The loop and loop-error fields of Lemma 5.6 [fo:prop:inputs] with the sampling of Lemma 5.8
[uvc:thm:ordinary-sampling].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Scales on the range of Lemma 5.6 [fo:prop:inputs] -/

/-- `γ_g > 0`. -/
private lemma loops_gammaG_pos (g : ℝ) : 0 < gammaG g := by
  have : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  unfold gammaG
  positivity

/-- `γ_g = g⁻²` for `g ≥ 1`. -/
private lemma loops_gammaG_eq {g : ℝ} (hg : 1 ≤ g) : gammaG g = (g ^ 2)⁻¹ := by
  unfold gammaG; rw [max_eq_right hg]

/-- `ζ_u ≥ (2W)⁻¹` for `g ≥ 1`, `u ∈ [0, 1/2]`, `L ≥ 1` ((5.18) [fo:eq:scale]). -/
private lemma loops_zeta_lower (W : ℕ) (hW : 1 ≤ W) (p : FlowPt) (hg : 1 ≤ p.g)
    (hu0 : 0 ≤ p.u) (hu1 : p.u ≤ 1 / 2) (hL : 1 ≤ p.L) : ((2 : ℝ) * W)⁻¹ ≤ flowZeta W p := by
  unfold flowZeta zetaProp ellProp
  rw [loops_gammaG_eq hg]
  have hg0 : 0 < p.g := by linarith
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  have hL1 : (1 : ℝ) ≤ p.L := by exact_mod_cast hL
  set s : ℝ := Real.sqrt ((p.g ^ 2)⁻¹ * (1 - p.u)) with hs
  have hin : 0 < (p.g ^ 2)⁻¹ * (1 - p.u) := by
    have : 0 < 1 - p.u := by linarith
    positivity
  have hs0 : 0 < s := Real.sqrt_pos.2 hin
  have hss : s ^ 2 = (p.g ^ 2)⁻¹ * (1 - p.u) := Real.sq_sqrt hin.le
  have hs2 : s ^ 2 ≤ 1 := by
    rw [hss]
    have : (p.g ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hg)
    nlinarith
  have hgs : p.g * s ≤ 1 := by
    have h1 : (p.g * s) ^ 2 ≤ 1 := by
      rw [mul_pow, hss]
      have : p.g ^ 2 * ((p.g ^ 2)⁻¹ * (1 - p.u)) = 1 - p.u := by field_simp
      rw [this]; linarith
    nlinarith [mul_pos hg0 hs0]
  set ℓ : ℝ := min (p.L : ℝ) (1 + p.g / s) with hℓ
  have hℓ0 : 0 < ℓ := lt_min (by linarith) (by positivity)
  have hℓ1 : ℓ ≤ 1 + p.g / s := min_le_right _ _
  have hP : ℓ * (1 - p.u) * (p.g ^ 2)⁻¹ ≤ 2 := by
    calc ℓ * (1 - p.u) * (p.g ^ 2)⁻¹ = ℓ * s ^ 2 := by rw [hss]; ring
      _ ≤ (1 + p.g / s) * s ^ 2 := by gcongr
      _ = s ^ 2 + p.g * s := by field_simp
      _ ≤ 2 := by linarith
  have hP0 : 0 < ℓ * (1 - p.u) * (p.g ^ 2)⁻¹ := by
    have : 0 < 1 - p.u := by linarith
    positivity
  have e : (W : ℝ) * ℓ * (1 - p.u) * (p.g ^ 2)⁻¹ = W * (ℓ * (1 - p.u) * (p.g ^ 2)⁻¹) := by ring
  rw [e]
  refine inv_anti₀ (by positivity) ?_
  nlinarith

/-- On the range of Lemma 5.6 [fo:prop:inputs], for `W` large, the anchor `m = m_{g,L}(E)`
satisfies `|m| ≤ C`, with `C` depending on `κ` only. -/
private lemma loops_root (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ₀ C : ℝ, 1 ≤ Cκ₀ ∧ 0 ≤ C ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ,
      Tendsto ρ atTop atTop → ∀ᶠ W : ℕ in atTop, ∀ CV : ℝ,
        ∀ p ∈ initLarge κ Cκ CV ρ W, ‖mRoot p.g p.L p.E‖ ≤ C := by
  obtain ⟨Cκl, Rl, cl, Cl, hCκl, hRl, hcl, hCl, Hl⟩ := large_periodic_comparison κ hκ hκ2
  refine ⟨Cκl, Cl, hCκl, hCl.le, fun Cκ hCκ ρ hρ => ?_⟩
  set R : ℝ := max Rl 3 with hR
  filter_upwards [hρ.eventually_ge_atTop R,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
    with W hρW hlog CV p hp
  obtain ⟨hgC, hE, hLlog, -, -, -⟩ := hp
  have hgl : Cκl ≤ p.g := hCκ.trans hgC
  have hg1 : 1 ≤ p.g := hCκl.trans hgl
  have hg0 : 0 < p.g := by linarith
  have hgg : 1 ≤ p.g ^ 2 := one_le_pow₀ hg1
  have hR3 : (3 : ℝ) ≤ R := le_max_right _ _
  have hρ0 : 0 ≤ ρ W := by linarith
  have hlog' : (1 : ℝ) ≤ Real.log W := hlog
  have hLR : R * p.g ^ 2 ≤ p.L := by
    have h1 : 0 ≤ ρ W * p.g ^ 2 := mul_nonneg hρ0 (by positivity)
    calc R * p.g ^ 2 ≤ ρ W * p.g ^ 2 := mul_le_mul_of_nonneg_right hρW (by positivity)
      _ ≤ ρ W * p.g ^ 2 * Real.log W := le_mul_of_one_le_right h1 hlog'
      _ ≤ _ := hLlog
  have hRlL : Rl * p.g ^ 2 ≤ p.L :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hLR
  have hL3 : 3 ≤ p.L := by
    have : (3 : ℝ) ≤ p.L := by nlinarith
    exact_mod_cast this
  obtain ⟨m, -, hroot, -, -, hmC, -⟩ := Hl p.g hgl p.L hRlL p.E hE
  have hb0 : 0 ≤ hopB p.g := by
    unfold hopB; rw [max_eq_right hg1, div_self hg0.ne']; norm_num
  have hmR : mRoot p.g p.L p.E = m :=
    (mRootV_spec (hopB p.g) (gammaG p.g) hb0 (loops_gammaG_pos _) p.L hL3
      (p.E : ℂ) (by simp)).2 m hroot
  rw [hmR]
  exact hmC

/-! ### The loop-error field -/

/-- The loop-error component of (5.22) [gc:eq:one-step-input] at each fixed `u ∈ [0, 1/2]`, for
every loop length, by strong induction on the length. -/
private theorem loops_err_all (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) :
    ∃ Cκ₀ : ℝ, 1 ≤ Cκ₀ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      ∀ k : ℕ, 1 ≤ k → PrecMax (fun p : FlowPt => p.L) (initLarge κ Cκ CV ρ)
        (Λ := fun _ p => Word k p.L) (fun W p w ω => flowErr W p w.1 w.2 ω)
        (fun W p _ => flowZeta W p ^ k) := by
  obtain ⟨C1, hC1, H1⟩ := lemma46_err_one κ CV hκ hκ2 hCV
  obtain ⟨C2, -, H2⟩ := lemma46_err_step κ CV hκ hκ2 hCV
  refine ⟨max C1 C2, hC1.trans (le_max_left _ _), fun Cκ hCκ ρ hρ => ?_⟩
  have h1 := H1 Cκ ((le_max_left _ _).trans hCκ) ρ hρ
  have h2 := H2 Cκ ((le_max_right _ _).trans hCκ) ρ hρ
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · obtain rfl : k = 1 := by omega
      exact h1
    · exact h2 k hk2 fun k' hk' hlt => ih k' hlt hk'

/-- Lemma 5.6 [fo:prop:inputs], the loop-error component of (5.22) [gc:eq:one-step-input] at each
fixed `u ∈ [0, 1/2]`: `max_{a,σ} |D_k| ≺ ζ_u^k` (Lemma 5.8 [uvc:thm:ordinary-sampling] for the
maximum). -/
theorem lemma46_err (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) :
    ∃ Cκ₀ : ℝ, 1 ≤ Cκ₀ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      ∀ k : ℕ, 1 ≤ k → PrecMax (fun p : FlowPt => p.L) (initLarge κ Cκ CV ρ)
        (Λ := fun _ p => Word k p.L) (fun W p w ω => flowErr W p w.1 w.2 ω)
        (fun W p _ => flowZeta W p ^ k) :=
  loops_err_all κ CV hκ hκ2 hCV

/-! ### The envelope of a loop by its block norms -/

section Envelope

variable {W L : ℕ}

/-- An entry of a matrix is at most its operator norm. -/
private lemma loops_norm_entry_le {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (i j : n) : ‖M i j‖ ≤ ‖M‖ := by
  have h := Matrix.l2_opNorm_mulVec M (EuclideanSpace.single j (1 : ℂ))
  have hn : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  rw [hn, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le ((EuclideanSpace.equiv n ℂ).symm
    (M.mulVec (EuclideanSpace.single j (1 : ℂ)).ofLp)) i
  convert this using 2
  simp

/-- The unnormalized projection onto block `x`. -/
private def loopsP (W L : ℕ) (x : Fin L) : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  Matrix.diagonal fun p => if p.1 = x then 1 else 0

/-- The inclusion of `ℂ^W` as block `x` of `ℂ^L ⊗ ℂ^W`. -/
private def loopsJ (W L : ℕ) (x : Fin L) : Matrix (Fin L × Fin W) (Fin W) ℂ :=
  Matrix.of fun p α => if p = (x, α) then 1 else 0

private lemma loops_blockE_eq (a : Fin L) :
    blockE W L a = (W : ℂ)⁻¹ • loopsP W L a := by
  ext p q
  by_cases h : p = q
  · subst h
    by_cases h1 : p.1 = a <;> simp [blockE, loopsP, h1]
  · simp [blockE, loopsP, h]

private lemma loopsP_mul_self (x : Fin L) : loopsP W L x * loopsP W L x = loopsP W L x := by
  unfold loopsP
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  by_cases h : p.1 = x <;> simp [h]

private lemma loopsP_conjTranspose (x : Fin L) : (loopsP W L x)ᴴ = loopsP W L x := by
  unfold loopsP
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  by_cases h : p.1 = x <;> simp [h]

private lemma loopsJ_conjTranspose_mul (x : Fin L) : (loopsJ W L x)ᴴ * loopsJ W L x = 1 := by
  ext α β
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, loopsJ, Matrix.of_apply,
    Matrix.one_apply]
  rw [Finset.sum_eq_single (x, α)]
  · by_cases h : α = β <;> simp [h]
  · intro p _ hp
    simp [hp]
  · simp

private lemma loopsP_sandwich (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (x y : Fin L) :
    loopsP W L x * A * loopsP W L y = loopsJ W L x * blockOf A x y * (loopsJ W L y)ᴴ := by
  ext ⟨p1, p2⟩ ⟨q1, q2⟩
  simp only [loopsP, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, loopsJ, blockOf, Matrix.of_apply, Matrix.conjTranspose_apply,
    Prod.mk.injEq]
  by_cases h1 : p1 = x <;> by_cases h2 : q1 = y <;> simp [h1, h2]

private lemma loopsJ_norm_le (x : Fin L) : ‖loopsJ W L x‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (loopsJ W L x)
  rw [loopsJ_conjTranspose_mul] at h
  have h1 : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simp
  nlinarith [norm_nonneg (loopsJ W L x)]

/-- The operator norm of a block sandwich is at most the operator norm of the block. -/
private lemma loops_norm_sandwich_le (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (x y : Fin L) : ‖loopsP W L x * A * loopsP W L y‖ ≤ ‖blockOf A x y‖ := by
  rw [loopsP_sandwich]
  have h1 := Matrix.l2_opNorm_mul (loopsJ W L x * blockOf A x y) (loopsJ W L y)ᴴ
  have h2 := Matrix.l2_opNorm_mul (loopsJ W L x) (blockOf A x y)
  rw [Matrix.l2_opNorm_conjTranspose] at h1
  have hJx := loopsJ_norm_le (W := W) x
  have hJy := loopsJ_norm_le (W := W) y
  have hB := norm_nonneg (blockOf A x y)
  calc _ ≤ ‖loopsJ W L x * blockOf A x y‖ * ‖loopsJ W L y‖ := h1
    _ ≤ (‖loopsJ W L x‖ * ‖blockOf A x y‖) * ‖loopsJ W L y‖ := by gcongr
    _ ≤ 1 * ‖blockOf A x y‖ * 1 := by gcongr
    _ = ‖blockOf A x y‖ := by ring

private lemma loops_norm_P_le (x : Fin L) : ‖loopsP W L x‖ ≤ 1 := by
  unfold loopsP
  rw [Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun p => ?_
  by_cases h : p.1 = x <;> simp [h]

private lemma loops_hXs (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (X : ℝ)
    (hX : ∀ c d, ‖blockOf G c d‖ ≤ X) (s : Bool) (c d : Fin L) :
    ‖loopsP W L c * sgnMat G s * loopsP W L d‖ ≤ X := by
  cases s
  · have h := loops_norm_sandwich_le G d c
    have e : loopsP W L c * sgnMat G false * loopsP W L d = (loopsP W L d * G * loopsP W L c)ᴴ := by
      simp only [sgnMat, Bool.false_eq_true, ite_false, Matrix.conjTranspose_mul,
        loopsP_conjTranspose, Matrix.mul_assoc]
    rw [e, Matrix.l2_opNorm_conjTranspose]
    exact h.trans (hX d c)
  · exact (loops_norm_sandwich_le G c d).trans (hX c d)

private lemma loops_prod_E : ∀ (n : ℕ) (S : Fin n → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (x : Fin n → Fin L), (List.ofFn fun p => S p * blockE W L (x p)).prod =
      ((W : ℂ)⁻¹) ^ n • (List.ofFn fun p => S p * loopsP W L (x p)).prod
  | 0, S, x => by simp
  | n + 1, S, x => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons,
      loops_prod_E n (fun p => S p.succ) (fun p => x p.succ), loops_blockE_eq]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    congr 1

private lemma loops_idem_split {n : Type*} [Fintype n] (P0 S0 P1 R : Matrix n n ℂ)
    (h : P1 * P1 = P1) : P0 * (S0 * P1 * R) = (P0 * S0 * P1) * (P1 * R) := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P1 P1 R, h]

private lemma loops_chain_norm (X : ℝ) (hX0 : 0 ≤ X) : ∀ (n : ℕ)
    (S : Fin n → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (x : Fin (n + 1) → Fin L),
    (∀ p : Fin n, ‖loopsP W L (x p.castSucc) * S p * loopsP W L (x p.succ)‖ ≤ X) →
    ‖loopsP W L (x 0) * (List.ofFn fun p : Fin n => S p * loopsP W L (x p.succ)).prod‖ ≤ X ^ n
  | 0, S, x, _ => by
    simpa using loops_norm_P_le (W := W) (x 0)
  | n + 1, S, x, h => by
    rw [List.ofFn_succ, List.prod_cons]
    have ih := loops_chain_norm X hX0 n (fun p => S p.succ) (fun p => x p.succ) (fun p => by
      have := h p.succ
      change ‖loopsP W L (x p.castSucc.succ) * S p.succ * loopsP W L (x p.succ.succ)‖ ≤ X
      rw [Fin.succ_castSucc]
      exact this)
    rw [loops_idem_split _ _ _ _ (loopsP_mul_self _)]
    have h0 := h 0
    rw [Fin.castSucc_zero] at h0
    calc _ ≤ ‖loopsP W L (x 0) * S 0 * loopsP W L (x (Fin.succ 0))‖ *
          ‖loopsP W L (x (Fin.succ 0)) *
            (List.ofFn fun i : Fin n => S i.succ * loopsP W L (x i.succ.succ)).prod‖ :=
          Matrix.l2_opNorm_mul _ _
      _ ≤ X * X ^ n := by gcongr
      _ = X ^ (n + 1) := by ring

/-- A product of factors `S_p P_{a_p}` absorbs the last projection on the right. -/
private lemma loops_prod_absorb (n : ℕ) (S : Fin (n + 1) → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a : Fin (n + 1) → Fin L) :
    (List.ofFn fun p => S p * loopsP W L (a p)).prod * loopsP W L (a (Fin.last n)) =
      (List.ofFn fun p => S p * loopsP W L (a p)).prod := by
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]
  simp only [Matrix.mul_assoc, loopsP_mul_self]

/-- `|Tr(P_c M)| ≤ W ‖P_c M‖`. -/
private lemma loops_trace_P_le (c : Fin L) (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    ‖(loopsP W L c * M).trace‖ ≤ W * ‖loopsP W L c * M‖ := by
  rw [Matrix.trace]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ q, ‖Matrix.diag (loopsP W L c * M) q‖ ≤
        ∑ q : Fin L × Fin W, (if q.1 = c then ‖loopsP W L c * M‖ else 0) :=
        Finset.sum_le_sum fun q _ => by
          by_cases hq : q.1 = c
          · simp only [hq, ite_true, Matrix.diag]
            exact loops_norm_entry_le _ q q
          · simp [Matrix.diag, loopsP, Matrix.diagonal_mul, hq]
    _ = W * ‖loopsP W L c * M‖ := by
        rw [Fintype.sum_prod_type]
        have h : ∀ x : Fin L, ∑ _y : Fin W, (if x = c then ‖loopsP W L c * M‖ else 0) =
            if x = c then (W : ℝ) * ‖loopsP W L c * M‖ else 0 := fun x => by
          split_ifs <;> simp
        simp only [h]
        simp

/-- The envelope of a loop by its block norms: if `‖G_{cd}‖ ≤ X` for all blocks, then
`W^{k-1} |ℒ_k(a, σ)| ≤ X^k` for `k ≥ 1`. -/
private lemma loops_loopTr_envelope (hW : 1 ≤ W) {k : ℕ} (hk : 1 ≤ k)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (X : ℝ) (hX0 : 0 ≤ X)
    (hX : ∀ c d, ‖blockOf G c d‖ ≤ X) (a : Fin k → Fin L) (σ : Fin k → Bool) :
    (W : ℝ) ^ (k - 1) * ‖loopTr G a σ‖ ≤ X ^ k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hchain := loops_chain_norm X hX0 (n + 1) (fun p => sgnMat G (σ p))
    (Fin.cons (a (Fin.last n)) a) (fun p => loops_hXs G X hX (σ p) _ _)
  simp only [Fin.cons_zero, Fin.cons_succ] at hchain
  have htr : (List.ofFn fun p => sgnMat G (σ p) * loopsP W L (a p)).prod.trace =
      (loopsP W L (a (Fin.last n)) *
        (List.ofFn fun p => sgnMat G (σ p) * loopsP W L (a p)).prod).trace := by
    rw [Matrix.trace_mul_comm, loops_prod_absorb]
  have hT := loops_trace_P_le (a (Fin.last n))
    (List.ofFn fun p => sgnMat G (σ p) * loopsP W L (a p)).prod
  unfold loopTr
  rw [loops_prod_E (n + 1) (fun p => sgnMat G (σ p)) a, Matrix.trace_smul, smul_eq_mul, norm_mul,
    norm_pow, norm_inv, Complex.norm_natCast, htr, Nat.add_sub_cancel]
  calc (W : ℝ) ^ n * ((W : ℝ)⁻¹ ^ (n + 1) * ‖(loopsP W L (a (Fin.last n)) *
        (List.ofFn fun p => sgnMat G (σ p) * loopsP W L (a p)).prod).trace‖) ≤
      (W : ℝ) ^ n * ((W : ℝ)⁻¹ ^ (n + 1) * (W * X ^ (n + 1))) := by
        gcongr
        exact hT.trans (mul_le_mul_of_nonneg_left hchain hW0.le)
    _ = X ^ (n + 1) := by
        rw [inv_pow]
        field_simp
        ring

end Envelope

/-- Lemma 5.6 [fo:prop:inputs], the loop component of (5.22) [gc:eq:one-step-input] at each fixed
`u ∈ [0, 1/2]`: `max_{a,σ} |ℒ_k| ≺ ζ_u^{k-1}`. -/
theorem lemma46_loop (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) :
    ∃ Cκ₀ : ℝ, 1 ≤ Cκ₀ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      ∀ k : ℕ, 1 ≤ k → PrecMax (fun p : FlowPt => p.L) (initLarge κ Cκ CV ρ)
        (Λ := fun _ p => Word k p.L) (fun W p w ω => loopTr (flowG W p ω) w.1 w.2)
        (fun W p _ => flowZeta W p ^ (k - 1)) := by
  obtain ⟨Cv, hCv, Hv⟩ := vert_max κ CV hκ hκ2 hCV
  obtain ⟨Cr, C, hCr, hC0, Hr⟩ := loops_root κ hκ hκ2
  refine ⟨max Cv Cr, hCv.trans (le_max_left _ _), fun Cκ hCκ ρ hρ k hk => ?_⟩
  intro ε D hε hD
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨W₁, HW₁⟩ := Hv Cκ ((le_max_left _ _).trans hCκ) ρ hρ (ε / (2 * k)) D (by positivity) hD
  have ev1 := Hr Cκ ((le_max_right _ _).trans hCκ) ρ hρ
  have ev2 : ∀ᶠ W : ℕ in atTop, (2 : ℝ) ^ (k - 1) ≤ (W : ℝ) ^ (ε / 2) :=
    ((tendsto_rpow_atTop (half_pos hε)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have ev3 : ∀ᶠ W : ℕ in atTop, C ≤ (W : ℝ) ^ (1 / 2 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  obtain ⟨W₂, HW₂⟩ := eventually_atTop.1
    (ev1.and (ev2.and (ev3.and (eventually_ge_atTop (max W₁ 1)))))
  refine ⟨W₂, fun W hW p hp => ?_⟩
  obtain ⟨hR, h2k, hCW, hWb⟩ := HW₂ W hW
  have hW₁ : W₁ ≤ W := (le_max_left _ _).trans hWb
  have hW1n : 1 ≤ W := (le_max_right _ _).trans hWb
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1n
  have hW0 : (0 : ℝ) < W := by linarith
  have hg1 : 1 ≤ p.g := (hCv.trans ((le_max_left _ _).trans hCκ)).trans hp.1
  have hu0 : 0 ≤ p.u := hp.2.2.2.2.1
  have hu1 : p.u ≤ 1 / 2 := hp.2.2.2.2.2
  have hmC := hR CV p hp
  set m : ℂ := mRoot p.g p.L p.E with hm
  set η : ℝ := etaChar p.g m p.u with hη
  have hγ : gammaG p.g = (p.g ^ 2)⁻¹ := loops_gammaG_eq hg1
  have hgη : p.g ^ 2 * η ≤ (W : ℝ) ^ (1 / 2 : ℝ) := by
    have e : p.g ^ 2 * η = (1 - p.u) * m.im := by
      rw [hη]; unfold etaChar; rw [hγ]
      have : p.g ≠ 0 := by linarith
      field_simp
    rw [e]
    have him : m.im ≤ C := (Complex.im_le_norm _).trans hmC
    refine le_trans ?_ hCW
    rcases le_or_gt 0 m.im with h | h
    · nlinarith
    · nlinarith
  have hseg : ∀ ω, segG W (p, η) ω = flowG W p ω := by
    intro ω
    have him : (zChar p.g p.E m p.u).im = η := by
      simp [zChar, etaChar, hη]
    simp only [segG, flowG]
    congr 1
    rw [← him]
    exact Complex.re_add_im _
  refine (measure_mono ?_).trans (HW₁ W hW₁ (p, η) hp le_rfl hgη)
  rintro ω ⟨w, hw⟩
  have hw' : (W : ℝ) ^ ε * flowZeta W p ^ (k - 1) < ‖loopTr (flowG W p ω) w.1 w.2‖ := hw
  by_contra hno
  have hX : ∀ c d, ‖blockOf (flowG W p ω) c d‖ ≤ (W : ℝ) ^ (ε / (2 * k)) := fun c d => by
    have h := not_lt.1 fun h => hno ⟨c, d, Or.inl h⟩
    rwa [hseg ω] at h
  have hL : 1 ≤ p.L := Nat.one_le_iff_ne_zero.2 fun h => by
    have := (w.1 ⟨0, hk⟩).2; omega
  have henv := loops_loopTr_envelope hW1n hk (flowG W p ω) _ (by positivity) hX w.1 w.2
  have hpow : ((W : ℝ) ^ (ε / (2 * k))) ^ k = (W : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
    congr 1
    field_simp
  rw [hpow] at henv
  have hζ := loops_zeta_lower W hW1n p hg1 hu0 hu1 hL
  have hA : 0 < (W : ℝ) ^ (k - 1) := by positivity
  have h1 : ‖loopTr (flowG W p ω) w.1 w.2‖ ≤ (W : ℝ) ^ (ε / 2) / (W : ℝ) ^ (k - 1) := by
    rw [le_div_iff₀ hA]; linarith
  have hZ : ((2 : ℝ) ^ (k - 1) * (W : ℝ) ^ (k - 1))⁻¹ ≤ flowZeta W p ^ (k - 1) := by
    rw [← mul_pow, ← inv_pow]
    exact pow_le_pow_left₀ (by positivity) hζ _
  have hε2 : (W : ℝ) ^ ε = (W : ℝ) ^ (ε / 2) * (W : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_add hW0]; ring_nf
  have h2 : (W : ℝ) ^ (ε / 2) / (W : ℝ) ^ (k - 1) ≤ (W : ℝ) ^ ε * flowZeta W p ^ (k - 1) := by
    calc (W : ℝ) ^ (ε / 2) / (W : ℝ) ^ (k - 1) =
          (W : ℝ) ^ (ε / 2) * (2 : ℝ) ^ (k - 1) * ((2 : ℝ) ^ (k - 1) * (W : ℝ) ^ (k - 1))⁻¹ := by
          field_simp
      _ ≤ (W : ℝ) ^ (ε / 2) * (W : ℝ) ^ (ε / 2) *
          ((2 : ℝ) ^ (k - 1) * (W : ℝ) ^ (k - 1))⁻¹ := by gcongr
      _ ≤ (W : ℝ) ^ (ε / 2) * (W : ℝ) ^ (ε / 2) * flowZeta W p ^ (k - 1) := by gcongr
      _ = _ := by rw [hε2]
  exact absurd (h1.trans h2) (not_le.2 hw')

end LSBA
