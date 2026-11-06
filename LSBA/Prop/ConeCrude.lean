import LSBA.Loop.ProjField
import LSBA.Prop.Inputs

/-!
# Crude moments of the propagated loop-error fields of Step 3

The generator and the bracket of the propagated projected field (C.35)
[fo:eq:projected-error-equation] and of the propagated field at the scaled Gaussian coordinates,
and their crude moments `E|·|^p ≤ C_p W^{C p}` at the points reached in a regime, from the crude
block moments (5.33) [fo:eq:coarse-time-input], the polynomial budget (6.6)
[fo:eq:spatial-sum-budget] and the kernel profile (6.3) [fo:eq:kernel-bounds]: the inputs of the
moment iteration off the good set in Step 3 of Appendix C.3 [sec:gc-one-step].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The generator of a field `Σ_b c_r(b) D_k(r; b)` of loop errors (5.17)
[fo:eq:error-hierarchy], at the scaled Gaussian coordinates `√(uγ_g/W) ω`, is the block generator
of the corresponding functional at the matrix `H_u(ω)` of (5.1) [fo:eq:flow]. -/
theorem coneCrude_coordGen_eq (g E : ℝ) (m : ℂ) {W L k : ℕ} (c : ℝ → (Fin k → Fin L) → ℂ)
    (σ : Fin k → Bool) {u : ℝ} (hu : 0 ≤ u) (ω : Ω W L) :
    coordGen (gammaG g / W) (fun r y => ∑ b, c r b * loopErrField g E m W L b σ r y) u
        (Real.sqrt (u * (gammaG g / W)) • ω) =
      blockGen W L (gammaG g)
        (fun r N => ∑ b, c r b * (resLoop g E m b σ r N - primLoop g W L E m r b σ)) u
        (flowH g W L u ω) := by
  have hγ : 0 ≤ gammaG g := by unfold gammaG; positivity
  have h : flowH g W L u ω = blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
      (Real.sqrt (u * (gammaG g / W)) • ω) := by
    unfold flowH; rw [blockFlow_eq_blockSlice _ _ _ (mul_nonneg hu hγ), mul_div_assoc]
  rw [h, blockGen_slice]
  rfl

/-- The bracket (5.9) [gc:eq:bracket] of a field `Σ_b c(b) D_k(u; b)` of loop errors at the
scaled Gaussian coordinates `√(uγ_g/W) ω` is the block bracket of the corresponding functional at
`H_u(ω)`. -/
theorem coneCrude_coordGamma_eq (g E : ℝ) (m : ℂ) {W L k : ℕ} (c : (Fin k → Fin L) → ℂ)
    (σ : Fin k → Bool) {u : ℝ} (hu : 0 ≤ u) (ω : Ω W L) :
    coordGamma (gammaG g / W) (fun y => ∑ b, c b * loopErrField g E m W L b σ u y)
        (fun y => ∑ b, c b * loopErrField g E m W L b σ u y)
        (Real.sqrt (u * (gammaG g / W)) • ω) =
      blockGamma W L (gammaG g)
        (fun N => ∑ b, c b * (resLoop g E m b σ u N - primLoop g W L E m u b σ))
        (fun N => ∑ b, c b * (resLoop g E m b σ u N - primLoop g W L E m u b σ))
        (flowH g W L u ω) := by
  have hγ : 0 ≤ gammaG g := by unfold gammaG; positivity
  have h : flowH g W L u ω = blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
      (Real.sqrt (u * (gammaG g / W)) • ω) := by
    unfold flowH; rw [blockFlow_eq_blockSlice _ _ _ (mul_nonneg hu hγ), mul_div_assoc]
  rw [h, blockGamma_slice]
  rfl

section CrudeHelpers

open scoped Matrix.Norms.L2Operator

/-! ### Moments of finite combinations -/

/-- `X` is a.e. strongly measurable with `E‖X‖^p ≤ B`. -/
private def coneCrudeMom {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') (p : ℕ)
    (X : Ω' → ℂ) (B : ℝ) : Prop :=
  AEStronglyMeasurable X P ∧ Integrable (fun ω => ‖X ω‖ ^ p) P ∧ ∫ ω, ‖X ω‖ ^ p ∂P ≤ B

/-- Jensen for weighted sums: `(Σ w_i f_i)^n ≤ (Σ w_i)^{n-1} Σ w_i f_i^n`. -/
private lemma coneCrude_wsum_pow_le {ι : Type*} [Fintype ι] (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) {n : ℕ} (hn : 1 ≤ n) :
    (∑ i, w i * f i) ^ n ≤ (∑ i, w i) ^ (n - 1) * ∑ i, w i * f i ^ n := by
  set S := ∑ i, w i with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hw i
  rcases hS0.eq_or_lt with h0 | hpos
  · have hw0 : ∀ i, w i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hw i)).1 h0.symm i (Finset.mem_univ i)
    simp [hw0, zero_pow (by omega : n ≠ 0)]
  · have hw1 : ∑ i, w i / S = 1 := by rw [← Finset.sum_div]; exact div_self hpos.ne'
    have h := Real.pow_arith_mean_le_arith_mean_pow Finset.univ (fun i => w i / S) f
      (fun i _ => div_nonneg (hw i) hS0) hw1 (fun i _ => hf i) n
    have e1 : ∑ i, w i / S * f i = (∑ i, w i * f i) / S := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ i, w i / S * f i ^ n = (∑ i, w i * f i ^ n) / S := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, e2, div_pow] at h
    have hSn : 0 < S ^ n := pow_pos hpos n
    rw [div_le_div_iff₀ hSn hpos] at h
    have : S ^ n = S ^ (n - 1) * S := by rw [← pow_succ]; congr 1; omega
    rw [this] at h
    nlinarith [h, pow_pos hpos (n - 1)]

/-- A nonnegative function dominated by a weighted sum of nonnegative functions with
integrable `n`-th powers has an integrable `n`-th power, with the weighted moment bound. -/
private lemma coneCrude_wsum_moment {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (f : ι → Ω' → ℝ) (hf0 : ∀ i x, 0 ≤ f i x) {n : ℕ} (hn : 1 ≤ n) {B : ℝ}
    (hfi : ∀ i, Integrable (fun x => f i x ^ n) P ∧ ∫ x, f i x ^ n ∂P ≤ B)
    (Q : Ω' → ℝ) (hQm : AEStronglyMeasurable Q P) (hQ0 : ∀ x, 0 ≤ Q x)
    (hQ : ∀ x, Q x ≤ ∑ i, w i * f i x) :
    Integrable (fun x => Q x ^ n) P ∧ ∫ x, Q x ^ n ∂P ≤ (∑ i, w i) ^ n * B := by
  set S := ∑ i, w i with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hw i
  have hpt : ∀ x, Q x ^ n ≤ S ^ (n - 1) * ∑ i, w i * f i x ^ n := fun x =>
    (pow_le_pow_left₀ (hQ0 x) (hQ x) n).trans
      (coneCrude_wsum_pow_le w (fun i => f i x) hw (fun i => hf0 i x) hn)
  have hRi : Integrable (fun x => S ^ (n - 1) * ∑ i, w i * f i x ^ n) P :=
    (integrable_finsetSum Finset.univ fun i _ => (hfi i).1.const_mul (w i)).const_mul _
  refine ⟨Integrable.mono' hRi (hQm.pow n) (Filter.Eventually.of_forall fun x => ?_), ?_⟩
  · rw [Real.norm_of_nonneg (pow_nonneg (hQ0 x) n)]
    exact hpt x
  · calc ∫ x, Q x ^ n ∂P ≤ ∫ x, S ^ (n - 1) * ∑ i, w i * f i x ^ n ∂P :=
          integral_mono (Integrable.mono' hRi (hQm.pow n)
            (Filter.Eventually.of_forall fun x => by
              rw [Real.norm_of_nonneg (pow_nonneg (hQ0 x) n)]; exact hpt x)) hRi hpt
      _ = S ^ (n - 1) * ∑ i, w i * ∫ x, f i x ^ n ∂P := by
          rw [integral_const_mul, integral_finsetSum Finset.univ fun i _ =>
            (hfi i).1.const_mul (w i)]
          congr 1
          exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
      _ ≤ S ^ (n - 1) * ∑ i, w i * B := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (pow_nonneg hS0 _)
          exact mul_le_mul_of_nonneg_left (hfi i).2 (hw i)
      _ = S ^ n * B := by
          rw [← Finset.sum_mul]
          have : S ^ n = S ^ (n - 1) * S := by rw [← pow_succ]; congr 1; omega
          rw [this]; ring

private lemma coneCrude_mom_congr {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'} {p : ℕ}
    {X Y : Ω' → ℂ} {B : ℝ} (h : ∀ ω, X ω = Y ω) (hX : coneCrudeMom P p X B) :
    coneCrudeMom P p Y B := by
  have e : X = Y := funext h
  rw [← e]; exact hX

private lemma coneCrude_mom_mono {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'} {p : ℕ}
    {X : Ω' → ℂ} {B B' : ℝ} (hX : coneCrudeMom P p X B) (hB : B ≤ B') :
    coneCrudeMom P p X B' :=
  ⟨hX.1, hX.2.1, hX.2.2.trans hB⟩

private lemma coneCrude_mom_nonneg {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'} {p : ℕ}
    {X : Ω' → ℂ} {B : ℝ} (hX : coneCrudeMom P p X B) : 0 ≤ B :=
  (integral_nonneg fun _ => pow_nonneg (norm_nonneg _) _).trans hX.2.2

/-- Minkowski for a finite combination with a uniform moment bound:
`E‖Σ w_i X_i‖^p ≤ (Σ ‖w_i‖)^p B`. -/
private lemma coneCrude_mom_sum {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] {p : ℕ} (hp : 1 ≤ p) {ι : Type*} [Fintype ι] (w : ι → ℂ)
    (X : ι → Ω' → ℂ) {B : ℝ} (hX : ∀ i, coneCrudeMom P p (X i) B) :
    coneCrudeMom P p (fun ω => ∑ i, w i * X i ω) ((∑ i, ‖w i‖) ^ p * B) := by
  have hm : AEStronglyMeasurable (fun ω => ∑ i, w i * X i ω) P :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hX i).1.const_mul (w i)
  have h := coneCrude_wsum_moment P (fun i => ‖w i‖) (fun i => norm_nonneg _)
    (fun i ω => ‖X i ω‖) (fun i ω => norm_nonneg _) hp (fun i => (hX i).2)
    (fun ω => ‖∑ i, w i * X i ω‖) hm.norm (fun ω => norm_nonneg _) (fun ω => by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun i _ => norm_mul _ _)
  exact ⟨hm, h⟩

/-- Minkowski with a bound `A` on the total weight. -/
private lemma coneCrude_mom_sum_le {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] {p : ℕ} (hp : 1 ≤ p) {ι : Type*} [Fintype ι] (w : ι → ℂ)
    (X : ι → Ω' → ℂ) {A B : ℝ} (hB : 0 ≤ B) (hX : ∀ i, coneCrudeMom P p (X i) B)
    (hA : ∑ i, ‖w i‖ ≤ A) :
    coneCrudeMom P p (fun ω => ∑ i, w i * X i ω) (A ^ p * B) :=
  coneCrude_mom_mono (coneCrude_mom_sum P hp w X hX)
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ =>
      norm_nonneg _) hA p) hB)

/-- `E‖X + Y‖^p ≤ 2^p (B₁ + B₂)`. -/
private lemma coneCrude_mom_add {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] {p : ℕ} (hp : 1 ≤ p) {X Y : Ω' → ℂ} {B₁ B₂ : ℝ}
    (hX : coneCrudeMom P p X B₁) (hY : coneCrudeMom P p Y B₂) :
    coneCrudeMom P p (fun ω => X ω + Y ω) (2 ^ p * (B₁ + B₂)) := by
  have h1 := coneCrude_mom_nonneg hX
  have h2 := coneCrude_mom_nonneg hY
  have hZ : ∀ i : Fin 2, coneCrudeMom P p (![X, Y] i) (B₁ + B₂) := by
    intro i
    fin_cases i
    · exact coneCrude_mom_mono hX (by simp; linarith)
    · exact coneCrude_mom_mono hY (by simp; linarith)
  have h := coneCrude_mom_sum P hp (fun _ => (1 : ℂ)) (fun i => ![X, Y] i) hZ
  have e : (∑ _i : Fin 2, ‖(1 : ℂ)‖) = 2 := by norm_num
  rw [e] at h
  exact coneCrude_mom_congr (fun ω => by simp [Fin.sum_univ_two]) h

/-! ### Entry bounds for loops of every length -/

section LoopEntry

variable {W L : ℕ}

/-- The number of sites in a block: `∑_{r} 1_{r.1 = a} f = W f`. -/
private lemma coneCrude_sum_block (a : Fin L) (f : ℝ) :
    ∑ r : Fin L × Fin W, (if r.1 = a then f else 0) = (W : ℝ) * f := by
  rw [Fintype.sum_prod_type]
  have h : ∀ x : Fin L, ∑ _y : Fin W, (if x = a then f else 0) =
      if x = a then (W : ℝ) * f else 0 := fun x => by split_ifs <;> simp
  simp only [h]
  simp

/-- Bounds on the entries of a product of loop factors `S_i E_{a_i}`: supported on the columns of
block `a`, with entries on rows of the labels `Lab` at most `B / W`. -/
private def coneCrudeBd (Lab : Finset (Fin L)) (P : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a : Fin L) (B : ℝ) : Prop :=
  (∀ p q : Fin L × Fin W, q.1 ≠ a → P p q = 0) ∧
    ∀ p q : Fin L × Fin W, p.1 ∈ Lab → ‖P p q‖ ≤ B * (W : ℝ)⁻¹

/-- One loop factor `S E_a`. -/
private lemma coneCrudeBd.factor {Lab : Finset (Fin L)}
    {S : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hS : ∀ p q : Fin L × Fin W, p.1 ∈ Lab → q.1 ∈ Lab → ‖S p q‖ ≤ K)
    {a : Fin L} (ha : a ∈ Lab) : coneCrudeBd Lab (S * blockE W L a) a K := by
  refine ⟨fun p q hq => ?_, fun p q hp => ?_⟩
  · simp [blockE, Matrix.mul_diagonal, hq]
  · simp only [blockE, Matrix.mul_diagonal]
    by_cases hq : q.1 = a
    · simp only [hq, ite_true, norm_mul, norm_inv, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_right (hS p q hp (hq ▸ ha)) (by positivity) |>.trans_eq (by ring)
    · simp only [hq, ite_false, mul_zero, norm_zero]
      positivity

/-- Product of two loop-factor products. -/
private lemma coneCrudeBd.mul {Lab : Finset (Fin L)}
    {P Q : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    {a b : Fin L} {B C : ℝ} (hW : 1 ≤ W) (hB : 0 ≤ B) (hP : coneCrudeBd Lab P a B)
    (ha : a ∈ Lab) (hQ : coneCrudeBd Lab Q b C) : coneCrudeBd Lab (P * Q) b (B * C) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  refine ⟨fun p q hq => ?_, fun p q hp => ?_⟩
  · rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun r _ => by rw [hQ.1 r q hq, mul_zero]
  · rw [Matrix.mul_apply]
    calc ‖∑ r, P p r * Q r q‖ ≤ ∑ r : Fin L × Fin W,
          (if r.1 = a then B * (W : ℝ)⁻¹ * (C * (W : ℝ)⁻¹) else 0) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
          by_cases hr : r.1 = a
          · simp only [hr, ite_true, norm_mul]
            exact mul_le_mul (hP.2 p r hp) (hQ.2 r q (hr ▸ ha)) (norm_nonneg _)
              (by positivity)
          · simp [hP.1 p r hr, hr]
      _ = B * C * (W : ℝ)⁻¹ := by
          rw [coneCrude_sum_block]
          field_simp

/-- The trace of a loop-factor product. -/
private lemma coneCrudeBd.trace_le {Lab : Finset (Fin L)}
    {P : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} {a : Fin L} {B : ℝ} (hW : 1 ≤ W)
    (hP : coneCrudeBd Lab P a B) (ha : a ∈ Lab) : ‖P.trace‖ ≤ B := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  rw [Matrix.trace]
  calc ‖∑ p, P.diag p‖ ≤ ∑ p : Fin L × Fin W, (if p.1 = a then B * (W : ℝ)⁻¹ else 0) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
        by_cases hp : p.1 = a
        · simp only [hp, ite_true, Matrix.diag]
          exact hP.2 p p (hp ▸ ha)
        · simp [Matrix.diag, hP.1 p p hp, hp]
    _ = B := by
        rw [coneCrude_sum_block]
        field_simp

/-- A loop-factor product times a matrix bounded on the blocks `Lab`. -/
private lemma coneCrudeBd.mul_bdd {Lab : Finset (Fin L)}
    {P S : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} {a : Fin L} {B K : ℝ} (hW : 1 ≤ W)
    (hB : 0 ≤ B) (hP : coneCrudeBd Lab P a B) (ha : a ∈ Lab)
    (hS : ∀ p q : Fin L × Fin W, p.1 ∈ Lab → q.1 ∈ Lab → ‖S p q‖ ≤ K) {p q : Fin L × Fin W}
    (hp : p.1 ∈ Lab) (hq : q.1 ∈ Lab) : ‖(P * S) p q‖ ≤ B * K := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  rw [Matrix.mul_apply]
  calc ‖∑ r, P p r * S r q‖ ≤ ∑ r : Fin L × Fin W,
        (if r.1 = a then B * (W : ℝ)⁻¹ * K else 0) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
        by_cases hr : r.1 = a
        · simp only [hr, ite_true, norm_mul]
          exact mul_le_mul (hP.2 p r hp) (hS r q (hr ▸ ha) hq) (norm_nonneg _) (by positivity)
        · simp [hP.1 p r hr, hr]
    _ = B * K := by
        rw [coneCrude_sum_block]
        field_simp

/-- Bounds on the entries of `G` on the blocks `Lab` pass to `G^σ`. -/
private lemma coneCrude_sgn_bound {Lab : Finset (Fin L)}
    {G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} {K : ℝ}
    (hG : ∀ p q : Fin L × Fin W, p.1 ∈ Lab → q.1 ∈ Lab → ‖G p q‖ ≤ K) (σ : Bool) :
    ∀ p q : Fin L × Fin W, p.1 ∈ Lab → q.1 ∈ Lab → ‖sgnMat G σ p q‖ ≤ K := by
  intro p q hp hq
  cases σ
  · simp only [sgnMat, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply, norm_star]
    exact hG q p hq hp
  · simpa [sgnMat] using hG p q hp hq

/-- A product of `n + 1` loop factors with labels in `Lab`. -/
private lemma coneCrude_prod_bd {Lab : Finset (Fin L)}
    {G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} {K : ℝ} (hW : 1 ≤ W) (hK : 0 ≤ K)
    (hG : ∀ p q : Fin L × Fin W, p.1 ∈ Lab → q.1 ∈ Lab → ‖G p q‖ ≤ K) :
    ∀ (n : ℕ) (a : Fin (n + 1) → Fin L) (σ : Fin (n + 1) → Bool), (∀ i, a i ∈ Lab) →
      coneCrudeBd Lab (List.ofFn fun i => sgnMat G (σ i) * blockE W L (a i)).prod
        (a (Fin.last n)) (K ^ (n + 1))
  | 0, a, σ, ha => by
      simpa [List.ofFn_succ] using coneCrudeBd.factor hK (coneCrude_sgn_bound hG (σ 0)) (ha 0)
  | n + 1, a, σ, ha => by
      rw [List.ofFn_succ, List.prod_cons]
      have ih := coneCrude_prod_bd hW hK hG n (fun i => a i.succ) (fun i => σ i.succ)
        (fun i => ha _)
      have h0 := coneCrudeBd.factor hK (coneCrude_sgn_bound hG (σ 0)) (ha 0)
      have h := h0.mul hW hK (ha 0) ih
      rw [Fin.succ_last, ← pow_succ'] at h
      exact h

/-- A loop of length `n ≥ 1` with labels in `Lab` is at most `K^n`. -/
private lemma coneCrude_loopTr_le {Lab : Finset (Fin L)}
    {G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} {K : ℝ} (hW : 1 ≤ W) (hK : 0 ≤ K)
    (hG : ∀ p q : Fin L × Fin W, p.1 ∈ Lab → q.1 ∈ Lab → ‖G p q‖ ≤ K) {n : ℕ} (hn : 1 ≤ n)
    (a : Fin n → Fin L) (σ : Fin n → Bool) (ha : ∀ i, a i ∈ Lab) : ‖loopTr G a σ‖ ≤ K ^ n := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  exact (coneCrude_prod_bd hW hK hG n a σ ha).trace_le hW (ha _)

/-- The cut loops `B_i` of a loop of length `k` have entries at most `K^{k+1}` on the blocks
`Lab`. -/
private lemma coneCrude_loopB_le {Lab : Finset (Fin L)}
    {G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} {K : ℝ} (hW : 1 ≤ W) (hK : 0 ≤ K)
    (hG : ∀ p q : Fin L × Fin W, p.1 ∈ Lab → q.1 ∈ Lab → ‖G p q‖ ≤ K) {k : ℕ}
    (a : Fin k → Fin L) (σ : Fin k → Bool) (ha : ∀ i, a i ∈ Lab) (i : Fin k)
    {p q : Fin L × Fin W} (hp : p.1 ∈ Lab) (hq : q.1 ∈ Lab) :
    ‖loopB G a σ i p q‖ ≤ K ^ (k + 1) := by
  obtain ⟨n, rfl⟩ : ∃ n', k = n' + 1 := ⟨k - 1, by have := i.2; omega⟩
  have h := coneCrude_prod_bd hW hK hG n (fun t => a (i + t)) (fun t => σ (i + t))
    (fun t => ha _)
  have := h.mul_bdd hW (pow_nonneg hK _) (ha _) (coneCrude_sgn_bound hG (σ i)) hp hq
  rw [pow_succ]
  simpa [loopB] using this

/-- The trace in the carré du champ of a loop (5.9) [gc:eq:bracket] on entries of the block
`c`. -/
private lemma coneCrude_gamma_trace_le (hW : 1 ≤ W) {c : Fin L}
    {X Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} {KX KY : ℝ} (hKX : 0 ≤ KX)
    (hX : ∀ p q : Fin L × Fin W, p.1 = c → q.1 = c → ‖X p q‖ ≤ KX)
    (hY : ∀ p q : Fin L × Fin W, p.1 = c → q.1 = c → ‖Y p q‖ ≤ KY) :
    ‖(((W : ℂ) • blockE W L c) * X * ((W : ℂ) • blockE W L c) * Yᴴ).trace‖ ≤
      (W : ℝ) ^ 2 * (KX * KY) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hD : ((W : ℂ) • blockE W L c) = Matrix.diagonal
      (fun p : Fin L × Fin W => if p.1 = c then (1 : ℂ) else 0) := by
    ext p q
    by_cases hpq : p = q
    · subst hpq
      by_cases hp : p.1 = c
      · simp only [blockE, hp, ite_true, Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
        exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 (by omega))
      · simp [blockE, hp]
    · simp [blockE, Matrix.diagonal_apply_ne _ hpq]
  rw [hD, Matrix.trace]
  calc ‖∑ p, ((Matrix.diagonal (fun p : Fin L × Fin W => if p.1 = c then (1 : ℂ) else 0)) * X *
          (Matrix.diagonal (fun p : Fin L × Fin W => if p.1 = c then (1 : ℂ) else 0)) * Yᴴ).diag p‖
      ≤ ∑ p : Fin L × Fin W, (if p.1 = c then (W : ℝ) * (KX * KY) else 0) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
        by_cases hp : p.1 = c
        · simp only [Matrix.diag, hp, ite_true]
          rw [Matrix.mul_apply]
          calc ‖∑ q, ((Matrix.diagonal (fun p : Fin L × Fin W => if p.1 = c then (1 : ℂ) else 0)) *
                  X * (Matrix.diagonal (fun p : Fin L × Fin W => if p.1 = c then (1 : ℂ) else 0)))
                  p q * Yᴴ q p‖
              ≤ ∑ q : Fin L × Fin W, (if q.1 = c then KX * KY else 0) := by
                refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
                by_cases hq : q.1 = c
                · simp only [hq, ite_true, Matrix.diagonal_mul, Matrix.mul_diagonal, norm_mul,
                    Matrix.conjTranspose_apply, norm_star, hp]
                  simp only [norm_one, one_mul, mul_one]
                  exact mul_le_mul (hX p q hp hq) (hY p q hp hq) (norm_nonneg _) hKX
                · simp [Matrix.mul_diagonal, hq]
            _ = (W : ℝ) * (KX * KY) := coneCrude_sum_block c _
        · simp only [Matrix.diag]
          rw [Matrix.mul_apply]
          have h0 : ∑ q, ((Matrix.diagonal
              (fun p : Fin L × Fin W => if p.1 = c then (1 : ℂ) else 0)) * X *
              (Matrix.diagonal (fun p : Fin L × Fin W => if p.1 = c then (1 : ℂ) else 0)))
              p q * Yᴴ q p = 0 :=
            Finset.sum_eq_zero fun q _ => by
              simp [Matrix.mul_diagonal, Matrix.diagonal_mul, hp]
          rw [h0]
          simp [hp]
    _ = (W : ℝ) ^ 2 * (KX * KY) := by
        rw [coneCrude_sum_block]; ring

end LoopEntry

/-! ### Pointwise bounds of the sources and of the brackets of loops -/

section Pointwise

variable {W L : ℕ}

private lemma coneCrude_gammaG_pos (g : ℝ) : 0 < gammaG g := by
  unfold gammaG
  have : (1 : ℝ) ≤ max 1 g := le_max_left _ _
  positivity

/-- `‖m^σ‖ = ‖m‖`. -/
private lemma coneCrude_norm_sgnScalar (m : ℂ) (s : Bool) : ‖sgnScalar m s‖ = ‖m‖ := by
  cases s <;> simp [sgnScalar]

/-- The labels of an insertion lie in any set containing the labels and the inserted label. -/
private lemma coneCrude_insLab_mem {k : ℕ} {Lab : Finset (Fin L)} (a : Fin k → Fin L)
    (i : Fin k) {c : Fin L} (ha : ∀ j, a j ∈ Lab) (hc : c ∈ Lab) (t : Fin (k + 1)) :
    insLab a i c t ∈ Lab := by
  unfold insLab
  rcases Fin.eq_self_or_eq_succAbove i.castSucc t with h | ⟨j, rfl⟩
  · rw [h, Fin.insertNth_apply_same]; exact hc
  · rw [Fin.insertNth_apply_succAbove]; exact ha j

/-- The labels of a left cut lie in any set containing the labels and the cut label. -/
private lemma coneCrude_cutLLab_mem {k : ℕ} {Lab : Finset (Fin L)} (a : Fin k → Fin L)
    (i j : Fin k) {c : Fin L} (ha : ∀ j, a j ∈ Lab) (hc : c ∈ Lab)
    (t : Fin (k + i - j + 1)) : cutLLab a i j c t ∈ Lab := by
  unfold cutLLab
  split_ifs
  exacts [ha _, hc, ha _]

/-- The labels of a right cut lie in any set containing the labels and the cut label. -/
private lemma coneCrude_cutRLab_mem {k : ℕ} {Lab : Finset (Fin L)} (a : Fin k → Fin L)
    (i j : Fin k) {c : Fin L} (ha : ∀ j, a j ∈ Lab) (hc : c ∈ Lab)
    (t : Fin (j - i + 1)) : cutRLab a i j c t ∈ Lab := by
  unfold cutRLab
  split_ifs
  exacts [ha _, hc]

/-- The sources of (C.32) [gc:eq:sourcetable] of a loop error of length `k`, the light term
(5.7) [fo:eq:light] plus `γ_g W` times the linear and quadratic cut terms of (5.17)
[fo:eq:error-hierarchy], are bounded by a weighted sum of powers of the entry bounds `K_c`,
pointwise in the matrix. -/
private lemma coneCrude_src_pointwise (g E : ℝ) (m : ℂ) (hW : 1 ≤ W) (u : ℝ)
    (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) {k : ℕ} (a : Fin k → Fin L)
    (σ : Fin k → Bool) {B : ℝ} (hB : 1 ≤ B) (hmB : ‖m‖ ≤ B)
    (hpr : ∀ n : ℕ, 2 ≤ n → n ≤ k → ∀ (b : Fin n → Fin L) (τ : Fin n → Bool),
      ‖primLoop g W L E m u b τ‖ ≤ B)
    (Lab : Fin L → Finset (Fin L)) (hLa : ∀ c i, a i ∈ Lab c) (hLc : ∀ c, c ∈ Lab c)
    (K : Fin L → ℝ) (hK : ∀ c, 1 ≤ K c)
    (hG : ∀ c, ∀ p q : Fin L × Fin W, p.1 ∈ Lab c → q.1 ∈ Lab c →
      ‖resolventMat M (zChar g E m u) p q‖ ≤ K c) :
    ‖lightW g E m a σ u M + ((gammaG g * W : ℝ) : ℂ) *
        (cutSrcLin (fun n b τ => primLoop g W L E m u (k := n) b τ)
            (errFam g E m (fun n b τ => primLoop g W L E m u (k := n) b τ) u M) a σ +
          cutSrcQuad (errFam g E m (fun n b τ => primLoop g W L E m u (k := n) b τ) u M) a σ)‖ ≤
      ∑ c : Fin L, (10 * (k : ℝ) ^ 2 * B ^ 2 * (gammaG g * W)) * K c ^ (2 * k + 2) := by
  set G := resolventMat M (zChar g E m u) with hGdef
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hγW : 0 ≤ gammaG g * W := mul_nonneg (coneCrude_gammaG_pos g).le hW0.le
  have hK0 : ∀ c, 0 ≤ K c := fun c => by linarith [hK c]
  have hB0 : 0 ≤ B := by linarith
  have hKk : ∀ c, 1 ≤ K c ^ k := fun c => one_le_pow₀ (hK c)
  set D := errFam g E m (fun n b τ => primLoop g W L E m u (k := n) b τ) u M with hDdef
  have hD : ∀ c {n : ℕ}, 2 ≤ n → n ≤ k → ∀ (b : Fin n → Fin L) (τ : Fin n → Bool),
      (∀ t, b t ∈ Lab c) → ‖D n b τ‖ ≤ 2 * B * K c ^ k := by
    intro c n hn hnk b τ hb
    have h1 := (coneCrude_loopTr_le hW (hK0 c) (hG c) (by omega : 1 ≤ n) b τ hb).trans
      (pow_le_pow_right₀ (hK c) hnk)
    have h2 := hpr n hn hnk b τ
    have h3 := hKk c
    change ‖loopTr G b τ - primLoop g W L E m u b τ‖ ≤ _
    calc ‖loopTr G b τ - primLoop g W L E m u b τ‖
        ≤ ‖loopTr G b τ‖ + ‖primLoop g W L E m u b τ‖ := norm_sub_le _ _
      _ ≤ K c ^ k + B := add_le_add h1 h2
      _ ≤ 2 * B * K c ^ k := by nlinarith
  set X : Fin L → ℝ := fun c => B ^ 2 * K c ^ (2 * k + 2) with hXdef
  have hX0 : ∀ c, 0 ≤ X c := fun c => by have := hK0 c; simp only [hXdef]; positivity
  -- the light term
  have hlight : ‖lightW g E m a σ u M‖ ≤ (gammaG g * W) * ((k : ℝ) * ∑ c, 2 * X c) := by
    unfold lightW
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hγW]
    refine mul_le_mul_of_nonneg_left ?_ hγW
    have hterm : ∀ (i : Fin k) (c : Fin L), ‖(loopTr G ![c] ![σ i] - sgnScalar m (σ i)) *
        loopTr G (insLab a i c) (insSgn σ i)‖ ≤ 2 * X c := by
      intro i c
      have h1 : ‖loopTr G ![c] ![σ i]‖ ≤ K c ^ 1 :=
        coneCrude_loopTr_le hW (hK0 c) (hG c) le_rfl _ _ (fun t => by
          fin_cases t; exact hLc c)
      have h2 : ‖loopTr G (insLab a i c) (insSgn σ i)‖ ≤ K c ^ (k + 1) :=
        coneCrude_loopTr_le hW (hK0 c) (hG c) (by omega) _ _
          (coneCrude_insLab_mem a i (hLa c) (hLc c))
      have h3 : ‖loopTr G ![c] ![σ i] - sgnScalar m (σ i)‖ ≤ K c + B := by
        refine (norm_sub_le _ _).trans ?_
        rw [coneCrude_norm_sgnScalar]
        rw [pow_one] at h1
        linarith
      have hKc := hK c
      have h4 : K c ^ (k + 1) * K c ≤ K c ^ (2 * k + 2) := by
        rw [← pow_succ]; exact pow_le_pow_right₀ hKc (by omega)
      have h5 : 0 ≤ K c ^ (k + 1) := by positivity
      rw [norm_mul]
      calc _ ≤ (K c + B) * K c ^ (k + 1) := mul_le_mul h3 h2 (norm_nonneg _) (by linarith [hK0 c])
        _ ≤ (2 * B * K c) * K c ^ (k + 1) := by
            refine mul_le_mul_of_nonneg_right ?_ h5
            nlinarith
        _ = 2 * B * (K c ^ (k + 1) * K c) := by ring
        _ ≤ 2 * B * K c ^ (2 * k + 2) := by
            refine mul_le_mul_of_nonneg_left h4 (by positivity)
        _ ≤ 2 * X c := by
            simp only [hXdef]
            have : B ≤ B ^ 2 := by nlinarith
            have h6 : 0 ≤ K c ^ (2 * k + 2) := by positivity
            nlinarith
    calc ‖∑ i : Fin k, ∑ c : Fin L, (loopTr G ![c] ![σ i] - sgnScalar m (σ i)) *
          loopTr G (insLab a i c) (insSgn σ i)‖
        ≤ ∑ _i : Fin k, ∑ c : Fin L, 2 * X c := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => hterm i c)
      _ = (k : ℝ) * ∑ c, 2 * X c := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the bounds on one cut
  have hcutc : ∀ (i j : Fin k), i < j → ∀ c : Fin L,
      ‖primLoop g W L E m u (cutLLab a i j c) (cutLSgn σ i j)‖ ≤ B ∧
      ‖primLoop g W L E m u (cutRLab a i j c) (cutRSgn σ i j)‖ ≤ B ∧
      ‖D _ (cutLLab a i j c) (cutLSgn σ i j)‖ ≤ 2 * B * K c ^ k ∧
      ‖D _ (cutRLab a i j c) (cutRSgn σ i j)‖ ≤ 2 * B * K c ^ k := by
    intro i j hij c
    have hij' : i.val < j.val := hij
    have hi := i.2
    have hj := j.2
    have hLl : 2 ≤ k + (i : ℕ) - (j : ℕ) + 1 := by omega
    have hLu : k + (i : ℕ) - (j : ℕ) + 1 ≤ k := by omega
    have hRl : 2 ≤ (j : ℕ) - (i : ℕ) + 1 := by omega
    have hRu : (j : ℕ) - (i : ℕ) + 1 ≤ k := by omega
    exact ⟨hpr _ hLl hLu _ _, hpr _ hRl hRu _ _,
      hD c hLl hLu _ _ (coneCrude_cutLLab_mem a i j (hLa c) (hLc c)),
      hD c hRl hRu _ _ (coneCrude_cutRLab_mem a i j (hLa c) (hLc c))⟩
  have hKD : ∀ c, B * (2 * B * K c ^ k) ≤ 2 * X c := by
    intro c
    have hk2 : K c ^ k ≤ K c ^ (2 * k + 2) := pow_le_pow_right₀ (hK c) (by omega)
    simp only [hXdef]
    nlinarith [mul_le_mul_of_nonneg_left hk2 (by positivity : (0 : ℝ) ≤ B ^ 2)]
  have hDD : ∀ c, (2 * B * K c ^ k) * (2 * B * K c ^ k) ≤ 4 * X c := by
    intro c
    have h2k : K c ^ k * K c ^ k ≤ K c ^ (2 * k + 2) := by
      rw [← pow_add]; exact pow_le_pow_right₀ (hK c) (by omega)
    simp only [hXdef]
    nlinarith [mul_le_mul_of_nonneg_left h2k (by positivity : (0 : ℝ) ≤ B ^ 2)]
  -- the linear cut terms
  have hlin : ‖cutSrcLin (fun n b τ => primLoop g W L E m u (k := n) b τ) D a σ‖ ≤
      (k : ℝ) ^ 2 * ∑ c, 4 * X c := by
    have hS0 : 0 ≤ ∑ c, 4 * X c := Finset.sum_nonneg fun c _ => by linarith [hX0 c]
    unfold cutSrcLin
    split_ifs with hk
    · rw [norm_zero]; positivity
    · have hpair : ∀ i j : Fin k, ‖(if i < j then ∑ c : Fin L,
          (if j.val = i.val + 1 then
              primLoop g W L E m u (cutLLab a i j c) (cutLSgn σ i j) *
                D _ (cutRLab a i j c) (cutRSgn σ i j)
            else if i.val = 0 ∧ j.val = k - 1 then
              D _ (cutLLab a i j c) (cutLSgn σ i j) *
                primLoop g W L E m u (cutRLab a i j c) (cutRSgn σ i j)
            else
              primLoop g W L E m u (cutLLab a i j c) (cutLSgn σ i j) *
                  D _ (cutRLab a i j c) (cutRSgn σ i j) +
                D _ (cutLLab a i j c) (cutLSgn σ i j) *
                  primLoop g W L E m u (cutRLab a i j c) (cutRSgn σ i j)) else 0)‖ ≤
          ∑ c, 4 * X c := by
        intro i j
        by_cases hij : i < j
        · simp only [hij, ↓reduceIte]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
          obtain ⟨kl, kr, dl, dr⟩ := hcutc i j hij c
          have e1 : ‖primLoop g W L E m u (cutLLab a i j c) (cutLSgn σ i j) *
              D _ (cutRLab a i j c) (cutRSgn σ i j)‖ ≤ 2 * X c := by
            rw [norm_mul]
            exact (mul_le_mul kl dr (norm_nonneg _) hB0).trans (hKD c)
          have e2 : ‖D _ (cutLLab a i j c) (cutLSgn σ i j) *
              primLoop g W L E m u (cutRLab a i j c) (cutRSgn σ i j)‖ ≤ 2 * X c := by
            rw [norm_mul]
            calc _ ≤ (2 * B * K c ^ k) * B :=
                  mul_le_mul dl kr (norm_nonneg _) (by have := hKk c; positivity)
              _ = B * (2 * B * K c ^ k) := by ring
              _ ≤ 2 * X c := hKD c
          have hXc := hX0 c
          split_ifs
          · linarith
          · linarith
          · exact (norm_add_le _ _).trans (by linarith)
        · simp only [hij, ↓reduceIte, norm_zero]
          exact Finset.sum_nonneg fun c _ => by linarith [hX0 c]
      calc _ ≤ ∑ _i : Fin k, ∑ _j : Fin k, ∑ c, 4 * X c := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hpair i j)
        _ = (k : ℝ) ^ 2 * ∑ c, 4 * X c := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  -- the quadratic cut terms
  have hquad : ‖cutSrcQuad D a σ‖ ≤ (k : ℝ) ^ 2 * ∑ c, 4 * X c := by
    unfold cutSrcQuad cutSumFam
    have hpair : ∀ i j : Fin k, ‖(if i < j then ∑ c : Fin L,
        D _ (cutLLab a i j c) (cutLSgn σ i j) * D _ (cutRLab a i j c) (cutRSgn σ i j)
          else 0)‖ ≤ ∑ c, 4 * X c := by
      intro i j
      split_ifs with hij
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
        obtain ⟨-, -, dl, dr⟩ := hcutc i j hij c
        rw [norm_mul]
        exact (mul_le_mul dl dr (norm_nonneg _) (by have := hKk c; positivity)).trans (hDD c)
      · rw [norm_zero]
        exact Finset.sum_nonneg fun c _ => by linarith [hX0 c]
    calc _ ≤ ∑ _i : Fin k, ∑ _j : Fin k, ∑ c, 4 * X c := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hpair i j)
      _ = (k : ℝ) ^ 2 * ∑ c, 4 * X c := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hS : 0 ≤ ∑ c, X c := Finset.sum_nonneg fun c _ => hX0 c
  have hk2 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ k := by exact_mod_cast h
      nlinarith
  have hfin : ∑ c : Fin L, (10 * (k : ℝ) ^ 2 * B ^ 2 * (gammaG g * W)) * K c ^ (2 * k + 2) =
      10 * (k : ℝ) ^ 2 * (gammaG g * W) * ∑ c, X c := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [hXdef]; ring
  rw [hfin]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hγW]
  have e1 : ∑ c, 2 * X c = 2 * ∑ c, X c := by rw [Finset.mul_sum]
  have e2 : ∑ c, 4 * X c = 4 * ∑ c, X c := by rw [Finset.mul_sum]
  rw [e1] at hlight
  rw [e2] at hlin hquad
  have hcut := (norm_add_le _ _).trans (add_le_add hlin hquad)
  have h3 := mul_le_mul_of_nonneg_left hcut hγW
  have h4 : (gammaG g * W) * ((k : ℝ) * (2 * ∑ c, X c)) ≤
      (gammaG g * W) * ((k : ℝ) ^ 2 * (2 * ∑ c, X c)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk2 (by positivity)) hγW
  nlinarith

/-- The bracket (5.9) [gc:eq:bracket] of two loops of length `k` is bounded by a weighted sum of
powers of the entry bounds `K_c`, pointwise in the matrix. -/
private lemma coneCrude_gamma_pointwise (g E : ℝ) (m : ℂ) (hm : 0 < m.im) (hW : 1 ≤ W)
    {u : ℝ} (hu : u < 1) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    {k : ℕ} (a a' : Fin k → Fin L) (σ : Fin k → Bool)
    (Lab : Fin L → Finset (Fin L)) (hLa : ∀ c i, a i ∈ Lab c) (hLa' : ∀ c i, a' i ∈ Lab c)
    (hLc : ∀ c, c ∈ Lab c) (K : Fin L → ℝ) (hK : ∀ c, 1 ≤ K c)
    (hG : ∀ c, ∀ p q : Fin L × Fin W, p.1 ∈ Lab c → q.1 ∈ Lab c →
      ‖resolventMat M (zChar g E m u) p q‖ ≤ K c) :
    ‖blockGamma W L (gammaG g) (resLoop g E m a σ u) (resLoop g E m a' σ u) M‖ ≤
      ∑ c : Fin L, ((k : ℝ) ^ 2 * (gammaG g * W)) * K c ^ (2 * k + 2) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hγ := coneCrude_gammaG_pos g
  have hK0 : ∀ c, 0 ≤ K c := fun c => by linarith [hK c]
  rw [blockGamma_loopTr g E m hm hu hM a σ a' σ, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hterm : ∀ (c : Fin L) (i j : Fin k),
      ‖(((W : ℂ) • blockE W L c) * loopB (resolventMat M (zChar g E m u)) a σ i *
          ((W : ℂ) • blockE W L c) *
          (loopB (resolventMat M (zChar g E m u)) a' σ j)ᴴ).trace‖ ≤
        (W : ℝ) ^ 2 * (K c ^ (k + 1) * K c ^ (k + 1)) := fun c i j => by
    refine coneCrude_gamma_trace_le hW (pow_nonneg (hK0 c) _) ?_ ?_
    · intro p q hp hq
      exact coneCrude_loopB_le hW (hK0 c) (hG c) a σ (hLa c) i (by rw [hp]; exact hLc c)
        (by rw [hq]; exact hLc c)
    · intro p q hp hq
      exact coneCrude_loopB_le hW (hK0 c) (hG c) a' σ (hLa' c) j (by rw [hp]; exact hLc c)
        (by rw [hq]; exact hLc c)
  calc (gammaG g / W) * ‖∑ c : Fin L, ∑ i : Fin k, ∑ j : Fin k,
        (((W : ℂ) • blockE W L c) * loopB (resolventMat M (zChar g E m u)) a σ i *
          ((W : ℂ) • blockE W L c) *
          (loopB (resolventMat M (zChar g E m u)) a' σ j)ᴴ).trace‖
      ≤ (gammaG g / W) * ∑ c : Fin L, ∑ _i : Fin k, ∑ _j : Fin k,
          (W : ℝ) ^ 2 * (K c ^ (k + 1) * K c ^ (k + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hterm c i j)
    _ = ∑ c : Fin L, ((k : ℝ) ^ 2 * (gammaG g * W)) * K c ^ (2 * k + 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← pow_add, show k + 1 + (k + 1) = 2 * k + 2 by ring]
        field_simp

end Pointwise

/-! ### Continuity in the sample and smoothness along the block directions -/

section Cont

variable {W L : ℕ}

/-- The resolvent of the single-time realization is continuous in the sample off the real
axis. -/
private lemma coneCrude_continuous_resolvent (g u : ℝ) (W L : ℕ) {z : ℂ} (hz : z.im ≠ 0) :
    Continuous fun ω : Ω W L => resolventMat (flowH g W L u ω) z := by
  have hF : Continuous fun ω : Ω W L => flowH g W L u ω := by
    unfold flowH blockFlow
    simp only [blockV_eq_sum_blockBasis]
    fun_prop
  have hc : Continuous fun ω : Ω W L => flowH g W L u ω - z • (1 : Matrix _ _ ℂ) :=
    hF.sub continuous_const
  refine continuous_iff_continuousAt.2 fun ω => ?_
  have hu := isUnit_sub_smul_one (flowH_isHermitian g W L u ω) hz
  have hdet : (flowH g W L u ω - z • (1 : Matrix _ _ ℂ)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  refine (continuousAt_matrix_inv _ ?_).comp hc.continuousAt
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ hdet

/-- A loop of a continuous family of matrices is continuous. -/
private lemma coneCrude_continuous_loopTr
    {X : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hX : Continuous X) {k : ℕ} (a : Fin k → Fin L) (σ : Fin k → Bool) :
    Continuous fun ω => loopTr (X ω) a σ := by
  unfold loopTr
  refine Continuous.matrix_trace ?_
  rw [show (fun ω => (List.ofFn fun i : Fin k => sgnMat (X ω) (σ i) * blockE W L (a i)).prod) =
    fun ω => ((List.finRange k).map fun i => sgnMat (X ω) (σ i) * blockE W L (a i)).prod from by
      funext ω; rw [List.ofFn_eq_map]]
  refine continuous_list_prod _ fun i _ => ?_
  refine Continuous.matrix_mul ?_ continuous_const
  cases σ i
  · exact hX.matrix_conjTranspose
  · exact hX

/-- The cut loops of a continuous family of matrices are continuous. -/
private lemma coneCrude_continuous_loopB
    {X : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hX : Continuous X) {k : ℕ} (a : Fin k → Fin L) (σ : Fin k → Bool) (i : Fin k) :
    Continuous fun ω => loopB (X ω) a σ i := by
  unfold loopB
  refine Continuous.matrix_mul ?_ ?_
  · rw [show (fun ω => (List.ofFn fun p : Fin k => sgnMat (X ω) (σ (i + p)) *
        blockE W L (a (i + p))).prod) = fun ω => ((List.finRange k).map fun p =>
        sgnMat (X ω) (σ (i + p)) * blockE W L (a (i + p))).prod from by
      funext ω; rw [List.ofFn_eq_map]]
    refine continuous_list_prod _ fun p _ => ?_
    refine Continuous.matrix_mul ?_ continuous_const
    cases σ (i + p)
    · exact hX.matrix_conjTranspose
    · exact hX
  · cases σ i
    · exact hX.matrix_conjTranspose
    · exact hX

/-- The sources of (C.32) [gc:eq:sourcetable] are continuous in the sample. -/
private lemma coneCrude_src_continuous (g E : ℝ) (m : ℂ) (u : ℝ) {k : ℕ}
    (a : Fin k → Fin L) (σ : Fin k → Bool)
    {M : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hM : Continuous fun ω => resolventMat (M ω) (zChar g E m u)) :
    Continuous fun ω => lightW g E m a σ u (M ω) + ((gammaG g * W : ℝ) : ℂ) *
        (cutSrcLin (fun n b τ => primLoop g W L E m u (k := n) b τ)
            (errFam g E m (fun n b τ => primLoop g W L E m u (k := n) b τ) u (M ω)) a σ +
          cutSrcQuad (errFam g E m (fun n b τ => primLoop g W L E m u (k := n) b τ) u (M ω))
            a σ) := by
  have hl : ∀ {n : ℕ} (b : Fin n → Fin L) (τ : Fin n → Bool),
      Continuous fun ω => loopTr (resolventMat (M ω) (zChar g E m u)) b τ := fun b τ =>
    coneCrude_continuous_loopTr hM b τ
  refine Continuous.add ?_ (continuous_const.mul (Continuous.add ?_ ?_))
  · unfold lightW
    exact continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_finsetSum _
      fun c _ => ((hl _ _).sub continuous_const).mul (hl _ _))
  · unfold cutSrcLin errFam
    split_ifs
    · exact continuous_const
    · refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
      by_cases hij : i < j
      · simp only [hij, ↓reduceIte]
        refine continuous_finsetSum _ fun c _ => ?_
        split_ifs
        · exact continuous_const.mul ((hl _ _).sub continuous_const)
        · exact ((hl _ _).sub continuous_const).mul continuous_const
        · exact (continuous_const.mul ((hl _ _).sub continuous_const)).add
            (((hl _ _).sub continuous_const).mul continuous_const)
      · simp only [hij, ↓reduceIte]
        exact continuous_const
  · unfold cutSrcQuad cutSumFam errFam
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    by_cases hij : i < j
    · simp only [hij, ↓reduceIte]
      exact continuous_finsetSum _ fun c _ =>
        ((hl _ _).sub continuous_const).mul ((hl _ _).sub continuous_const)
    · simp only [hij, ↓reduceIte]
      exact continuous_const

/-- The bracket of two loops in the form of (5.9) [gc:eq:bracket] is continuous in the sample. -/
private lemma coneCrude_gamma_continuous (g E : ℝ) (m : ℂ) (u : ℝ) {k : ℕ}
    (a a' : Fin k → Fin L) (σ : Fin k → Bool)
    {M : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hM : Continuous fun ω => resolventMat (M ω) (zChar g E m u)) :
    Continuous fun ω => ((gammaG g / W : ℝ) : ℂ) * ∑ c : Fin L, ∑ i : Fin k, ∑ j : Fin k,
        (((W : ℂ) • blockE W L c) * loopB (resolventMat (M ω) (zChar g E m u)) a σ i *
          ((W : ℂ) • blockE W L c) *
          (loopB (resolventMat (M ω) (zChar g E m u)) a' σ j)ᴴ).trace := by
  refine continuous_const.mul (continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => ?_)
  refine Continuous.matrix_trace ?_
  refine Continuous.matrix_mul (Continuous.matrix_mul (Continuous.matrix_mul continuous_const ?_)
    continuous_const) ?_
  · exact coneCrude_continuous_loopB hM _ _ i
  · exact (coneCrude_continuous_loopB hM _ _ j).matrix_conjTranspose

/-- Moving along a block direction from `M`: the slice at `e • δ_{(c,κ)}` is `M + e T_{c,κ}`. -/
private lemma coneCrude_slice_line
    (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (c : Fin L) (κ : Fin W × Fin W) (e : ℝ) :
    blockSlice W L M (e • Pi.single (c, κ.1, κ.2) 1) = M + (e : ℂ) • blockBasis W L c κ := by
  unfold blockSlice
  congr 1
  rw [Finset.sum_eq_single c, Finset.sum_eq_single κ]
  · simp
  · intro κ' _ hκ'
    have : (c, κ'.1, κ'.2) ≠ (c, κ.1, κ.2) := by
      intro h; apply hκ'; simp only [Prod.mk.injEq, true_and] at h; exact Prod.ext h.1 h.2
    simp [this]
  · simp
  · intro c' _ hc'
    refine Finset.sum_eq_zero fun κ' _ => ?_
    have : (c', κ'.1, κ'.2) ≠ (c, κ.1, κ.2) := by
      intro h; apply hc'; simp only [Prod.mk.injEq] at h; exact h.1
    simp [this]
  · simp

/-- A resolvent loop at the characteristic is differentiable along every block direction. -/
private lemma coneCrude_loop_diff (g E : ℝ) (m : ℂ) (hm : 0 < m.im) {u : ℝ}
    (hu : u < 1) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian) {k : ℕ}
    (a : Fin k → Fin L) (σ : Fin k → Bool) (c : Fin L) (κ : Fin W × Fin W) :
    DifferentiableAt ℝ
      (fun e : ℝ => resLoop g E m a σ u (M + (e : ℂ) • blockBasis W L c κ)) 0 := by
  have hC := heatClass_loopTr W L k M hM g E m hm a σ (a' := u - 1) (b' := (u + 1) / 2)
    (by linarith)
  have hu' : u ∈ Set.Ioo (u - 1) ((u + 1) / 2) := ⟨by linarith, by linarith⟩
  obtain ⟨DF, D2F, hD, -⟩ := hC.dx
  set v : Ω W L := Pi.single (c, κ.1, κ.2) 1 with hv
  have hφ : HasDerivAt (fun e : ℝ => e • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hf : (fun e : ℝ => resLoop g E m a σ u (M + (e : ℂ) • blockBasis W L c κ)) =
      (fun x => loopTr (resolventMat (blockSlice W L M x) (zChar g E m u)) a σ) ∘
        (fun e : ℝ => e • v) := by
    funext e
    simp only [Function.comp, hv, coneCrude_slice_line, resLoop]
  rw [hf]
  exact ((hD u hu' ((0 : ℝ) • v)).comp_hasDerivAt (0 : ℝ) hφ).differentiableAt

/-- A loop error at the characteristic is differentiable along every block direction. -/
private lemma coneCrude_err_diff (g E : ℝ) (m : ℂ) (hm : 0 < m.im) {u : ℝ}
    (hu : u < 1) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian) {k : ℕ}
    (K : ℂ) (σ : Fin k → Bool) (a : Fin k → Fin L) (c : Fin L) (κ : Fin W × Fin W) :
    DifferentiableAt ℝ
      (fun e : ℝ => resLoop g E m a σ u (M + (e : ℂ) • blockBasis W L c κ) - K) 0 :=
  (coneCrude_loop_diff g E m hm hu hM a σ c κ).sub_const K

end Cont

/-! ### Entry bounds from the block norms and their moments -/

section Atoms

/-- A constant plus a finite sum of nonnegative functions with integrable `n`-th powers. -/
private lemma coneCrude_const_sum_moment {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] {ι : Type*} [Fintype ι] {A : ℝ} (hA : 0 ≤ A) (z : ι → Ω' → ℝ)
    (hz0 : ∀ i x, 0 ≤ z i x) {n : ℕ} (hn : 1 ≤ n) {B : ℝ}
    (hzi : ∀ i, Integrable (fun x => z i x ^ n) P ∧ ∫ x, z i x ^ n ∂P ≤ B)
    (hm : AEStronglyMeasurable (fun x => A + ∑ i, z i x) P) :
    Integrable (fun x => (A + ∑ i, z i x) ^ n) P ∧
      ∫ x, (A + ∑ i, z i x) ^ n ∂P ≤ 2 ^ (n - 1) * (A ^ n + (Fintype.card ι : ℝ) ^ n * B) := by
  have hZ0 : ∀ x, 0 ≤ ∑ i, z i x := fun x => Finset.sum_nonneg fun i _ => hz0 i x
  have hpt : ∀ x, (A + ∑ i, z i x) ^ n ≤
      2 ^ (n - 1) * (A ^ n + (Fintype.card ι : ℝ) ^ (n - 1) * ∑ i, z i x ^ n) := by
    intro x
    refine (add_pow_le hA (hZ0 x) n).trans ?_
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by positivity)
    have h := coneCrude_wsum_pow_le (fun _ : ι => (1 : ℝ)) (fun i => z i x)
      (fun _ => zero_le_one) (fun i => hz0 i x) hn
    simpa using h
  have hRi : Integrable (fun x => 2 ^ (n - 1) *
      (A ^ n + (Fintype.card ι : ℝ) ^ (n - 1) * ∑ i, z i x ^ n)) P :=
    ((integrable_const _).add
      ((integrable_finsetSum Finset.univ fun i _ => (hzi i).1).const_mul _)).const_mul _
  have hI : Integrable (fun x => (A + ∑ i, z i x) ^ n) P :=
    Integrable.mono' hRi (hm.pow n) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (pow_nonneg (add_nonneg hA (hZ0 x)) n)]; exact hpt x)
  refine ⟨hI, ?_⟩
  calc ∫ x, (A + ∑ i, z i x) ^ n ∂P
      ≤ ∫ x, 2 ^ (n - 1) * (A ^ n + (Fintype.card ι : ℝ) ^ (n - 1) * ∑ i, z i x ^ n) ∂P :=
        integral_mono hI hRi hpt
    _ = 2 ^ (n - 1) * (A ^ n + (Fintype.card ι : ℝ) ^ (n - 1) * ∑ i, ∫ x, z i x ^ n ∂P) := by
        rw [integral_const_mul, integral_add (integrable_const _)
          ((integrable_finsetSum Finset.univ fun i _ => (hzi i).1).const_mul _),
          integral_const_mul, integral_finsetSum Finset.univ fun i _ => (hzi i).1]
        simp
    _ ≤ 2 ^ (n - 1) * (A ^ n + (Fintype.card ι : ℝ) ^ (n - 1) * ∑ _i : ι, B) := by
        refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => (hzi i).2) (by positivity)
    _ = 2 ^ (n - 1) * (A ^ n + (Fintype.card ι : ℝ) ^ n * B) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have : (Fintype.card ι : ℝ) ^ n = (Fintype.card ι : ℝ) ^ (n - 1) * Fintype.card ι := by
          rw [← pow_succ]; congr 1; omega
        rw [this]; ring

/-- An entry is bounded by the operator norm. -/
private lemma coneCrude_norm_entry_le {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (i j : n) : ‖X i j‖ ≤ ‖X‖ := by
  have h := Matrix.l2_opNorm_mulVec X ((EuclideanSpace.equiv n ℂ).symm (Pi.single j 1))
  have hx : ‖(EuclideanSpace.equiv n ℂ).symm (Pi.single j (1 : ℂ))‖ = 1 := by simp
  rw [hx, mul_one] at h
  refine le_trans (le_of_eq ?_) ((PiLp.norm_apply_le _ i).trans h)
  simp [Matrix.mulVec_single]

/-- The entry bound `K = 1 + Σ_{s,t} ‖G_{lab_s lab_t}‖` of `G` on the blocks `lab`. -/
private def coneCrudeK (W : ℕ) (x : FlowPt) {M : ℕ} (lab : Fin M → Fin x.L) (ω : Ω W x.L) : ℝ :=
  1 + ∑ st : Fin M × Fin M, ‖blockOf (flowG W x ω) (lab st.1) (lab st.2)‖

private lemma coneCrudeK_ge (W : ℕ) (x : FlowPt) {M : ℕ} (lab : Fin M → Fin x.L)
    (ω : Ω W x.L) : 1 ≤ coneCrudeK W x lab ω := by
  unfold coneCrudeK
  have : 0 ≤ ∑ st : Fin M × Fin M, ‖blockOf (flowG W x ω) (lab st.1) (lab st.2)‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  linarith

private lemma coneCrudeK_entry (W : ℕ) (x : FlowPt) {M : ℕ} (lab : Fin M → Fin x.L)
    (ω : Ω W x.L) {p q : Fin x.L × Fin W} (hp : p.1 ∈ Finset.univ.image lab)
    (hq : q.1 ∈ Finset.univ.image lab) :
    ‖flowG W x ω p q‖ ≤ coneCrudeK W x lab ω := by
  rw [Finset.mem_image] at hp hq
  obtain ⟨i, -, hi⟩ := hp
  obtain ⟨j, -, hj⟩ := hq
  have h1 : ‖flowG W x ω p q‖ ≤ ‖blockOf (flowG W x ω) p.1 q.1‖ :=
    coneCrude_norm_entry_le (blockOf (flowG W x ω) p.1 q.1) p.2 q.2
  have h2 : ‖blockOf (flowG W x ω) p.1 q.1‖ ≤ ∑ st : Fin M × Fin M,
      ‖blockOf (flowG W x ω) (lab st.1) (lab st.2)‖ := by
    have := Finset.single_le_sum (f := fun st : Fin M × Fin M =>
      ‖blockOf (flowG W x ω) (lab st.1) (lab st.2)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ (i, j))
    simpa [hi, hj] using this
  unfold coneCrudeK
  linarith

/-- `G` is continuous in the sample at a point with `Im m > 0` and `u < 1`. -/
private lemma coneCrude_flowG_continuous (W : ℕ) (x : FlowPt) (hm : 0 < (mRoot x.g x.L x.E).im)
    (hu1 : x.u < 1) : Continuous fun ω : Ω W x.L => flowG W x ω := by
  have hz : (zChar x.g x.E (mRoot x.g x.L x.E) x.u).im ≠ 0 := by
    rw [im_zChar]; exact (etaChar_pos x.g _ hm hu1).ne'
  exact coneCrude_continuous_resolvent x.g x.u W x.L hz

/-- The moments of `K^N` from the moments of the blocks of `G`. -/
private lemma coneCrudeK_moment (x : FlowPt) (W : ℕ) (hm : 0 < (mRoot x.g x.L x.E).im)
    (hu1 : x.u < 1) {M : ℕ} (lab : Fin M → Fin x.L) {N : ℕ} (hN : 1 ≤ N) {Bc : ℝ}
    (hcr : ∀ y z : Fin x.L, Integrable (fun ω => ‖blockOf (flowG W x ω) y z‖ ^ N)
        (μ W x.L) ∧ ∫ ω, ‖blockOf (flowG W x ω) y z‖ ^ N ∂(μ W x.L) ≤ Bc) :
    Continuous (fun ω => coneCrudeK W x lab ω) ∧
    Integrable (fun ω => coneCrudeK W x lab ω ^ N) (μ W x.L) ∧
      ∫ ω, coneCrudeK W x lab ω ^ N ∂(μ W x.L) ≤
        2 ^ (N - 1) * (1 + (((M * M : ℕ) : ℝ)) ^ N * Bc) := by
  have hGc := coneCrude_flowG_continuous W x hm hu1
  have hbc : ∀ y z : Fin x.L, Continuous fun ω : Ω W x.L => ‖blockOf (flowG W x ω) y z‖ := by
    intro y z
    refine Continuous.norm (continuous_matrix fun α β => ?_)
    exact (continuous_apply (z, β)).comp ((continuous_apply (y, α)).comp hGc)
  have hKc : Continuous (fun ω : Ω W x.L => coneCrudeK W x lab ω) := by
    unfold coneCrudeK
    exact continuous_const.add (continuous_finsetSum _ fun st _ => hbc _ _)
  have h := coneCrude_const_sum_moment (μ W x.L) (A := 1) zero_le_one
    (fun (st : Fin M × Fin M) ω => ‖blockOf (flowG W x ω) (lab st.1) (lab st.2)‖)
    (fun _ _ => norm_nonneg _) hN (B := Bc) (fun st => hcr _ _) hKc.aestronglyMeasurable
  refine ⟨hKc, h.1, h.2.trans (le_of_eq ?_)⟩
  simp [Fintype.card_prod]

/-- The anchor point of the flow: the segment pair at the characteristic height has the resolvent
of the flow. -/
private lemma coneCrude_segG_eq (W : ℕ) (x : FlowPt) (ω : Ω W x.L) :
    segG W (x, etaChar x.g (mRoot x.g x.L x.E) x.u) ω = flowG W x ω := by
  unfold segG flowG
  simp only
  rw [← im_zChar x.g x.E (mRoot x.g x.L x.E) x.u, Complex.re_add_im]

end Atoms

/-! ### Moments of the sources, loop errors and brackets at one point -/

section Leaves

/-- The common bound `2^{Np-1}(1 + ((2k+1)²)^{Np} B_c)` of the moments of `K^{(2k+2)p}`. -/
private def coneCrudeBk (k p : ℕ) (Bc : ℝ) : ℝ :=
  2 ^ ((2 * k + 2) * p - 1) * (1 + ((((2 * k + 1) * (2 * k + 1) : ℕ) : ℝ)) ^ ((2 * k + 2) * p) * Bc)

/-- The moments of `(K^{2k+2})^p` for at most `2k + 1` labels. -/
private lemma coneCrudeK_pow_moment (x : FlowPt) (W : ℕ) (hm : 0 < (mRoot x.g x.L x.E).im)
    (hu1 : x.u < 1) {k M : ℕ} (hM : M ≤ 2 * k + 1) (lab : Fin M → Fin x.L) {p : ℕ}
    (hp : 1 ≤ p) {Bc : ℝ} (hBc : 0 ≤ Bc)
    (hcr : ∀ y z : Fin x.L,
      Integrable (fun ω => ‖blockOf (flowG W x ω) y z‖ ^ ((2 * k + 2) * p)) (μ W x.L) ∧
        ∫ ω, ‖blockOf (flowG W x ω) y z‖ ^ ((2 * k + 2) * p) ∂(μ W x.L) ≤ Bc) :
    Continuous (fun ω => coneCrudeK W x lab ω) ∧
    Integrable (fun ω => (coneCrudeK W x lab ω ^ (2 * k + 2)) ^ p) (μ W x.L) ∧
      ∫ ω, (coneCrudeK W x lab ω ^ (2 * k + 2)) ^ p ∂(μ W x.L) ≤ coneCrudeBk k p Bc := by
  have hN : 1 ≤ (2 * k + 2) * p := by nlinarith
  have h := coneCrudeK_moment x W hm hu1 lab hN hcr
  have e : ∀ ω, (coneCrudeK W x lab ω ^ (2 * k + 2)) ^ p =
      coneCrudeK W x lab ω ^ ((2 * k + 2) * p) := fun ω => (pow_mul _ _ _).symm
  simp only [e]
  refine ⟨h.1, h.2.1, h.2.2.trans ?_⟩
  unfold coneCrudeBk
  refine mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_right ?_ hBc))
    (by positivity)
  refine pow_le_pow_left₀ (by positivity) ?_ _
  exact_mod_cast Nat.mul_le_mul hM hM

/-- Moments of the sources of (C.32) [gc:eq:sourcetable] of a loop error of length `k` at the
flow point `x`. -/
private lemma coneCrude_src_mom (x : FlowPt) (W : ℕ) (hW : 1 ≤ W)
    (hm : 0 < (mRoot x.g x.L x.E).im) (hu1 : x.u < 1) {k : ℕ} {B : ℝ} (hB : 1 ≤ B)
    (hmB : ‖mRoot x.g x.L x.E‖ ≤ B)
    (hpr : ∀ n : ℕ, 2 ≤ n → n ≤ k → ∀ (b : Fin n → Fin x.L) (τ : Fin n → Bool),
      ‖primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b τ‖ ≤ B)
    {p : ℕ} (hp : 1 ≤ p) {Bc : ℝ} (hBc : 0 ≤ Bc)
    (hcr : ∀ y z : Fin x.L,
      Integrable (fun ω => ‖blockOf (flowG W x ω) y z‖ ^ ((2 * k + 2) * p)) (μ W x.L) ∧
        ∫ ω, ‖blockOf (flowG W x ω) y z‖ ^ ((2 * k + 2) * p) ∂(μ W x.L) ≤ Bc)
    (σ : Fin k → Bool) (b : Fin k → Fin x.L) :
    coneCrudeMom (μ W x.L) p (fun ω =>
      lightW x.g x.E (mRoot x.g x.L x.E) b σ x.u (flowH x.g W x.L x.u ω) +
        ((gammaG x.g * W : ℝ) : ℂ) *
          (cutSrcLin (fun n c τ => primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u (k := n) c τ)
              (errFam x.g x.E (mRoot x.g x.L x.E)
                (fun n c τ => primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u (k := n) c τ) x.u
                (flowH x.g W x.L x.u ω)) b σ +
            cutSrcQuad (errFam x.g x.E (mRoot x.g x.L x.E)
                (fun n c τ => primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u (k := n) c τ) x.u
                (flowH x.g W x.L x.u ω)) b σ))
      (((x.L : ℝ) * (10 * (k : ℝ) ^ 2 * B ^ 2 * (gammaG x.g * W))) ^ p * coneCrudeBk k p Bc) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hγW : 0 ≤ gammaG x.g * W := mul_nonneg (coneCrude_gammaG_pos x.g).le hW0.le
  have hGc := coneCrude_flowG_continuous W x hm hu1
  set lab : Fin x.L → Fin (k + 1) → Fin x.L := fun c => Fin.cons c b with hlab
  have hmom := fun c => coneCrudeK_pow_moment x W hm hu1 (M := k + 1) (by omega) (lab c) hp hBc
    hcr
  have hcont := coneCrude_src_continuous (W := W) x.g x.E (mRoot x.g x.L x.E) x.u b σ
    (M := fun ω => flowH x.g W x.L x.u ω) hGc
  set w : ℝ := 10 * (k : ℝ) ^ 2 * B ^ 2 * (gammaG x.g * W) with hwdef
  have hw0 : 0 ≤ w := by positivity
  have h := coneCrude_wsum_moment (μ W x.L) (fun _ : Fin x.L => w) (fun _ => hw0)
    (fun c ω => coneCrudeK W x (lab c) ω ^ (2 * k + 2))
    (fun c ω => pow_nonneg (by linarith [coneCrudeK_ge W x (lab c) ω]) _) hp
    (fun c => (hmom c).2) _ hcont.norm.aestronglyMeasurable (fun ω => norm_nonneg _)
    (fun ω => coneCrude_src_pointwise x.g x.E (mRoot x.g x.L x.E) hW x.u _ b σ hB hmB hpr
      (fun c => Finset.univ.image (lab c))
      (fun c i => Finset.mem_image.2 ⟨i.succ, Finset.mem_univ _, by simp [hlab]⟩)
      (fun c => Finset.mem_image.2 ⟨0, Finset.mem_univ _, by simp [hlab]⟩)
      (fun c => coneCrudeK W x (lab c) ω) (fun c => coneCrudeK_ge W x (lab c) ω)
      (fun c p q hp hq => coneCrudeK_entry W x (lab c) ω hp hq))
  have hsumw : ∑ _c : Fin x.L, w = (x.L : ℝ) * w := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsumw] at h
  exact ⟨hcont.aestronglyMeasurable, h⟩

/-- Moments of the loop error `D_k(b)` at the flow point `x`. -/
private lemma coneCrude_err_mom (x : FlowPt) (W : ℕ) (hW : 1 ≤ W)
    (hm : 0 < (mRoot x.g x.L x.E).im) (hu1 : x.u < 1) {k : ℕ} (hk : 1 ≤ k) {B : ℝ}
    (hB : 1 ≤ B)
    (hprk : ∀ (b : Fin k → Fin x.L) (τ : Fin k → Bool),
      ‖primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b τ‖ ≤ B)
    {p : ℕ} (hp : 1 ≤ p) {Bc : ℝ} (hBc : 0 ≤ Bc)
    (hcr : ∀ y z : Fin x.L,
      Integrable (fun ω => ‖blockOf (flowG W x ω) y z‖ ^ ((2 * k + 2) * p)) (μ W x.L) ∧
        ∫ ω, ‖blockOf (flowG W x ω) y z‖ ^ ((2 * k + 2) * p) ∂(μ W x.L) ≤ Bc)
    (σ : Fin k → Bool) (b : Fin k → Fin x.L) :
    coneCrudeMom (μ W x.L) p (fun ω => flowErr W x b σ ω) ((2 * B) ^ p * coneCrudeBk k p Bc) := by
  have hGc := coneCrude_flowG_continuous W x hm hu1
  have hmom := coneCrudeK_pow_moment x W hm hu1 (M := k) (by omega) b hp hBc hcr
  have hcont : Continuous fun ω => flowErr W x b σ ω := by
    unfold flowErr
    exact (coneCrude_continuous_loopTr hGc b σ).sub continuous_const
  have hB0 : 0 ≤ 2 * B := by linarith
  have h := coneCrude_wsum_moment (μ W x.L) (fun _ : Unit => 2 * B) (fun _ => hB0)
    (fun _ ω => coneCrudeK W x b ω ^ (2 * k + 2))
    (fun _ ω => pow_nonneg (by linarith [coneCrudeK_ge W x b ω]) _) hp (fun _ => hmom.2) _
    hcont.norm.aestronglyMeasurable (fun ω => norm_nonneg _) (fun ω => by
      have hK := coneCrudeK_ge W x b ω
      have hl : ‖loopTr (flowG W x ω) b σ‖ ≤ coneCrudeK W x b ω ^ k :=
        coneCrude_loopTr_le hW (by linarith) (fun p q hp hq => coneCrudeK_entry W x b ω hp hq)
          hk b σ (fun i => Finset.mem_image_of_mem b (Finset.mem_univ i))
      have hKk : 1 ≤ coneCrudeK W x b ω ^ k := one_le_pow₀ hK
      have hk2 : coneCrudeK W x b ω ^ k ≤ coneCrudeK W x b ω ^ (2 * k + 2) :=
        pow_le_pow_right₀ hK (by omega)
      simp only [Finset.univ_unique, Finset.sum_singleton]
      unfold flowErr
      calc ‖loopTr (flowG W x ω) b σ - primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b σ‖
          ≤ ‖loopTr (flowG W x ω) b σ‖ +
              ‖primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b σ‖ := norm_sub_le _ _
        _ ≤ coneCrudeK W x b ω ^ k + B := add_le_add hl (hprk b σ)
        _ ≤ 2 * B * coneCrudeK W x b ω ^ k := by nlinarith
        _ ≤ 2 * B * coneCrudeK W x b ω ^ (2 * k + 2) :=
            mul_le_mul_of_nonneg_left hk2 hB0)
  simp only [Finset.univ_unique, Finset.sum_singleton] at h
  exact ⟨hcont.aestronglyMeasurable, h⟩

/-- Moments of the bracket (5.9) [gc:eq:bracket] of two loops of length `k` at the flow
point `x`. -/
private lemma coneCrude_gamma_mom (x : FlowPt) (W : ℕ) (hW : 1 ≤ W)
    (hm : 0 < (mRoot x.g x.L x.E).im) (hu1 : x.u < 1) {k : ℕ} {p : ℕ} (hp : 1 ≤ p) {Bc : ℝ}
    (hBc : 0 ≤ Bc)
    (hcr : ∀ y z : Fin x.L,
      Integrable (fun ω => ‖blockOf (flowG W x ω) y z‖ ^ ((2 * k + 2) * p)) (μ W x.L) ∧
        ∫ ω, ‖blockOf (flowG W x ω) y z‖ ^ ((2 * k + 2) * p) ∂(μ W x.L) ≤ Bc)
    (σ : Fin k → Bool) (b b' : Fin k → Fin x.L) :
    coneCrudeMom (μ W x.L) p (fun ω => blockGamma W x.L (gammaG x.g)
        (resLoop x.g x.E (mRoot x.g x.L x.E) b σ x.u)
        (resLoop x.g x.E (mRoot x.g x.L x.E) b' σ x.u) (flowH x.g W x.L x.u ω))
      (((x.L : ℝ) * ((k : ℝ) ^ 2 * (gammaG x.g * W))) ^ p * coneCrudeBk k p Bc) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hGc := coneCrude_flowG_continuous W x hm hu1
  set lab : Fin x.L → Fin (k + k + 1) → Fin x.L := fun c => Fin.cons c (Fin.append b b')
    with hlab
  have hmom := fun c => coneCrudeK_pow_moment x W hm hu1 (M := k + k + 1) (by omega) (lab c) hp
    hBc hcr
  have heq : ∀ ω : Ω W x.L, blockGamma W x.L (gammaG x.g)
      (resLoop x.g x.E (mRoot x.g x.L x.E) b σ x.u)
      (resLoop x.g x.E (mRoot x.g x.L x.E) b' σ x.u) (flowH x.g W x.L x.u ω) =
      ((gammaG x.g / W : ℝ) : ℂ) * ∑ c : Fin x.L, ∑ i : Fin k, ∑ j : Fin k,
        (((W : ℂ) • blockE W x.L c) * loopB (resolventMat (flowH x.g W x.L x.u ω)
          (zChar x.g x.E (mRoot x.g x.L x.E) x.u)) b σ i * ((W : ℂ) • blockE W x.L c) *
          (loopB (resolventMat (flowH x.g W x.L x.u ω)
            (zChar x.g x.E (mRoot x.g x.L x.E) x.u)) b' σ j)ᴴ).trace := fun ω =>
    blockGamma_loopTr x.g x.E (mRoot x.g x.L x.E) hm hu1
      (flowH_isHermitian x.g W x.L x.u ω) b σ b' σ
  have hcont0 := coneCrude_gamma_continuous (W := W) x.g x.E (mRoot x.g x.L x.E) x.u b b' σ
    (M := fun ω => flowH x.g W x.L x.u ω) hGc
  have hcont : Continuous fun ω : Ω W x.L => blockGamma W x.L (gammaG x.g)
      (resLoop x.g x.E (mRoot x.g x.L x.E) b σ x.u)
      (resLoop x.g x.E (mRoot x.g x.L x.E) b' σ x.u) (flowH x.g W x.L x.u ω) := by
    simp only [heq]; exact hcont0
  set w : ℝ := (k : ℝ) ^ 2 * (gammaG x.g * W) with hwdef
  have hw0 : 0 ≤ w := by have := coneCrude_gammaG_pos x.g; positivity
  have h := coneCrude_wsum_moment (μ W x.L) (fun _ : Fin x.L => w) (fun _ => hw0)
    (fun c ω => coneCrudeK W x (lab c) ω ^ (2 * k + 2))
    (fun c ω => pow_nonneg (by linarith [coneCrudeK_ge W x (lab c) ω]) _) hp
    (fun c => (hmom c).2) _ hcont.norm.aestronglyMeasurable (fun ω => norm_nonneg _)
    (fun ω => coneCrude_gamma_pointwise x.g x.E (mRoot x.g x.L x.E) hm hW hu1
      (flowH_isHermitian x.g W x.L x.u ω) b b' σ
      (fun c => Finset.univ.image (lab c))
      (fun c i => Finset.mem_image.2 ⟨(Fin.castAdd k i).succ, Finset.mem_univ _, by simp [hlab]⟩)
      (fun c i => Finset.mem_image.2 ⟨(Fin.natAdd k i).succ, Finset.mem_univ _, by
        simp only [hlab, Fin.cons_succ, Fin.append_right]⟩)
      (fun c => Finset.mem_image.2 ⟨0, Finset.mem_univ _, by simp [hlab]⟩)
      (fun c => coneCrudeK W x (lab c) ω) (fun c => coneCrudeK_ge W x (lab c) ω)
      (fun c p q hp hq => coneCrudeK_entry W x (lab c) ω hp hq))
  have hsumw : ∑ _c : Fin x.L, w = (x.L : ℝ) * w := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsumw] at h
  exact ⟨hcont.aestronglyMeasurable, h⟩

end Leaves

/-! ### Deterministic weights -/

section Weights

/-- The number of words of length `n + 1` with a given first label is `L^n`. -/
private lemma coneCrude_count {L n : ℕ} (c : Fin L) :
    ∑ b : Fin (n + 1) → Fin L, (if b 0 = c then (1 : ℝ) else 0) = (L : ℝ) ^ n := by
  rw [← (Fin.consEquiv fun _ => Fin L).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.cons_zero]
  rw [Finset.sum_eq_single c (fun x _ hx => by simp [hx]) (by simp)]
  simp

/-- The projection before (C.33) [fo:eq:ward-projection] as a combination of the values. -/
private lemma coneCrude_projQ_eq {L n : ℕ} (θ : Fin L → ℝ) (F : (Fin (n + 1) → Fin L) → ℂ)
    (b : Fin (n + 1) → Fin L) :
    projQ θ F b = ∑ b', ((if b' = b then 1 else 0) -
      (if b' 0 = b 0 then ∏ j : Fin n, ((θ (b 0 - b j.succ) : ℝ) : ℂ) else 0)) * F b' := by
  unfold projQ rowSum
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [Finset.sum_mul]
  refine congrArg _ (Finset.sum_congr rfl fun b' _ => ?_)
  split_ifs <;> ring

/-- `Σ_{b'} |δ_{b'b} - δ_{b'_0 b_0} t| ≤ 1 + |t| L^n`. -/
private lemma coneCrude_projQ_weight {L n : ℕ} (b : Fin (n + 1) → Fin L) (t : ℂ) :
    ∑ b' : Fin (n + 1) → Fin L,
      ‖(if b' = b then (1 : ℂ) else 0) - (if b' 0 = b 0 then t else 0)‖ ≤
      1 + ‖t‖ * (L : ℝ) ^ n := by
  calc _ ≤ ∑ b' : Fin (n + 1) → Fin L, ((if b' = b then (1 : ℝ) else 0) +
        ‖t‖ * (if b' 0 = b 0 then (1 : ℝ) else 0)) := by
        refine Finset.sum_le_sum fun b' _ => (norm_sub_le _ _).trans (le_of_eq ?_)
        split_ifs <;> simp
    _ = 1 + ‖t‖ * (L : ℝ) ^ n := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, coneCrude_count]
        simp

/-- The same bound with the roles of the two words exchanged. -/
private lemma coneCrude_projQ_weight' {L n : ℕ} (b : Fin (n + 1) → Fin L) (t : ℂ) :
    ∑ b' : Fin (n + 1) → Fin L,
      ‖(if b = b' then (1 : ℂ) else 0) - (if b 0 = b' 0 then t else 0)‖ ≤
      1 + ‖t‖ * (L : ℝ) ^ n := by
  have h := coneCrude_projQ_weight b t
  simp only [eq_comm (a := b), eq_comm (a := b 0)] at h ⊢
  exact h

/-- Products of rows: `Σ_b |Π_j U_j(a_j, b_j)| ≤ R^k` when every row has absolute sum `≤ R`. -/
private lemma coneCrude_prod_rows {L k : ℕ} (U : Fin k → Fin L → Fin L → ℂ) (a : Fin k → Fin L)
    {R : ℝ} (hR : ∀ j, ∑ y, ‖U j (a j) y‖ ≤ R) :
    ∑ b : Fin k → Fin L, ‖∏ j, U j (a j) (b j)‖ ≤ R ^ k := by
  have e : ∑ b : Fin k → Fin L, ‖∏ j, U j (a j) (b j)‖ = ∏ j, ∑ y, ‖U j (a j) y‖ := by
    rw [Fintype.prod_sum]
    exact Finset.sum_congr rfl fun b _ => norm_prod _ _
  rw [e]
  calc ∏ j, ∑ y, ‖U j (a j) y‖ ≤ ∏ _j : Fin k, R :=
        Finset.prod_le_prod₀ (fun j _ => Finset.sum_nonneg fun y _ => norm_nonneg _)
          fun j _ => hR j
    _ = R ^ k := by simp

/-- Rows of a product: `Σ_y |(AB)_{xy}| ≤ (Σ_c |A_{xc}|) R` when the rows of `B` are `≤ R`. -/
private lemma coneCrude_mul_row {L : ℕ} (A B : Matrix (Fin L) (Fin L) ℂ) (x : Fin L) {R : ℝ}
    (hB : ∀ c, ∑ y, ‖B c y‖ ≤ R) :
    ∑ y, ‖(A * B) x y‖ ≤ (∑ c, ‖A x c‖) * R := by
  calc ∑ y, ‖(A * B) x y‖ ≤ ∑ y, ∑ c, ‖A x c‖ * ‖B c y‖ := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [Matrix.mul_apply]
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun c _ => norm_mul _ _
    _ = ∑ c, ‖A x c‖ * ∑ y, ‖B c y‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => by rw [Finset.mul_sum]
    _ ≤ ∑ c, ‖A x c‖ * R :=
        Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hB c) (norm_nonneg _)
    _ = (∑ c, ‖A x c‖) * R := by rw [Finset.sum_mul]

/-- The Ward profile is at most `(1 - r)κ` and nonnegative when the kernel lies in `[0, κ]`. -/
private lemma coneCrude_wardProfile_le {L : ℕ} (hL : 1 ≤ L) (P : Matrix (Fin L) (Fin L) ℝ)
    {r κ : ℝ} (hr : r ≤ 1) (hK0 : ∀ a b, 0 ≤ mixedKer P r a b) (hK : ∀ a b, mixedKer P r a b ≤ κ)
    (d : Fin L) : 0 ≤ wardProfile P r d ∧ wardProfile P r d ≤ (1 - r) * κ := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hr0 : 0 ≤ 1 - r := by linarith
  unfold wardProfile
  refine ⟨mul_nonneg (div_nonneg hr0 hL0.le) (Finset.sum_nonneg fun x _ => hK0 _ _), ?_⟩
  calc (1 - r) / L * ∑ x : Fin L, mixedKer P r x (x + d) ≤ (1 - r) / L * ∑ _x : Fin L, κ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hK _ _)
          (div_nonneg hr0 hL0.le)
    _ = (1 - r) * κ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- `Σ_b |coef_{r,v}(a, b)| ≤ (Σ_b Π_j U_{a_j b_j})(1 + T L^n)` for nonnegative `U` and
`Π_j θ_r ≤ T`. -/
private lemma coneCrude_projCoef_weight {L n : ℕ} (P : Matrix (Fin L) (Fin L) ℝ) (v r : ℝ)
    (a : Fin (n + 1) → Fin L) {T : ℝ}
    (hU : ∀ x y, 0 ≤ (1 + (v - r) • mixedKer P v) x y)
    (hθ0 : ∀ d, 0 ≤ wardProfile P r d)
    (hT : ∀ b : Fin (n + 1) → Fin L, ∏ j : Fin n, wardProfile P r (b 0 - b j.succ) ≤ T) :
    ∑ b, ‖projCoef P v r a b‖ ≤
      (∑ b' : Fin (n + 1) → Fin L, ∏ j, (1 + (v - r) • mixedKer P v) (a j) (b' j)) *
        (1 + T * (L : ℝ) ^ n) := by
  set U := 1 + (v - r) • mixedKer P v with hUdef
  unfold projCoef
  calc ∑ b, ‖∑ b' : Fin (n + 1) → Fin L, (∏ j, ((U (a j) (b' j) : ℝ) : ℂ)) *
        ((if b' = b then 1 else 0) -
          if b' 0 = b 0 then ∏ j : Fin n, ((wardProfile P r (b' 0 - b' j.succ) : ℝ) : ℂ)
            else 0)‖
      ≤ ∑ b, ∑ b' : Fin (n + 1) → Fin L, (∏ j, U (a j) (b' j)) *
        ‖(if b' = b then (1 : ℂ) else 0) -
          if b' 0 = b 0 then ∏ j : Fin n, ((wardProfile P r (b' 0 - b' j.succ) : ℝ) : ℂ)
            else 0‖ := by
        refine Finset.sum_le_sum fun b _ => (norm_sum_le _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun b' _ => ?_
        rw [norm_mul, norm_prod]
        congr 1
        exact Finset.prod_congr rfl fun j _ => by
          rw [Complex.norm_real, Real.norm_of_nonneg (hU _ _)]
    _ = ∑ b' : Fin (n + 1) → Fin L, (∏ j, U (a j) (b' j)) * ∑ b,
        ‖(if b' = b then (1 : ℂ) else 0) -
          if b' 0 = b 0 then ∏ j : Fin n, ((wardProfile P r (b' 0 - b' j.succ) : ℝ) : ℂ)
            else 0‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b' _ => by rw [Finset.mul_sum]
    _ ≤ ∑ b' : Fin (n + 1) → Fin L, (∏ j, U (a j) (b' j)) * (1 + T * (L : ℝ) ^ n) := by
        refine Finset.sum_le_sum fun b' _ => mul_le_mul_of_nonneg_left ?_
          (Finset.prod_nonneg fun j _ => hU _ _)
        refine (coneCrude_projQ_weight' b' _).trans ?_
        have hn : ‖∏ j : Fin n, ((wardProfile P r (b' 0 - b' j.succ) : ℝ) : ℂ)‖ ≤ T := by
          rw [norm_prod]
          refine le_trans (le_of_eq (Finset.prod_congr rfl fun j _ => ?_)) (hT b')
          rw [Complex.norm_real, Real.norm_of_nonneg (hθ0 _)]
        have := mul_le_mul_of_nonneg_right hn (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ n)
        linarith
    _ = _ := by rw [Finset.sum_mul]

end Weights

/-! ### The generators at one point -/

section GenPoint

private lemma coneCrudeBk_nonneg (k p : ℕ) {Bc : ℝ} (hBc : 0 ≤ Bc) : 0 ≤ coneCrudeBk k p Bc := by
  unfold coneCrudeBk; positivity

/-- The primitive loops satisfy (5.10) [fo:eq:primitive] at every `u ∈ (-1, 1)`, all lengths. -/
private lemma coneCrude_primDeriv (g : ℝ) (W L : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ L) (E : ℝ) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (u : ℝ) (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    IsPrimDeriv (gammaG g) W L (fun r n b τ => primLoop g W L E m r (k := n) b τ) u := by
  intro n a σ
  rcases n with _ | _ | n
  · have h0 : cutSumFam (fun n b τ => primLoop g W L E m u (k := n) b τ) a σ = 0 := by
      simp [cutSumFam]
    rw [h0, mul_zero]
    exact hasDerivAt_const u (primLoop g W L E m 0 a σ)
  · have h1 : cutSumFam (fun n b τ => primLoop g W L E m u (k := n) b τ) a σ = 0 := by
      simp [cutSumFam]
    rw [h1, mul_zero]
    exact hasDerivAt_const u (primLoop g W L E m 0 a σ)
  · exact primLoop_hasDerivAt g W L hW hL E m hm u hu (by omega) a σ

/-- Moments of the generator of the propagated field (all words, `k = n + 1 ≥ 2`) at one point,
with rows of the propagators at most `R₂`. -/
private lemma coneCrude_genStable_point (x : FlowPt) (W : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ x.L)
    (hroot : IsDysonRootV (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))
    (hu : x.u ∈ Set.Ioo (-1 : ℝ) 1) {v : ℝ} (hv : v ∈ Set.Ioo (-1 : ℝ) 1) {n : ℕ} (hn : 1 ≤ n)
    {B : ℝ} (hB : 1 ≤ B) (hmB : ‖mRoot x.g x.L x.E‖ ≤ B)
    (hpr : ∀ j : ℕ, 2 ≤ j → j ≤ n + 1 → ∀ (b : Fin j → Fin x.L) (τ : Fin j → Bool),
      ‖primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b τ‖ ≤ B)
    {p : ℕ} (hp : 1 ≤ p) {Bc : ℝ} (hBc : 0 ≤ Bc)
    (hcr : ∀ y z : Fin x.L,
      Integrable (fun ω => ‖blockOf (flowG W x ω) y z‖ ^ ((2 * (n + 1) + 2) * p)) (μ W x.L) ∧
        ∫ ω, ‖blockOf (flowG W x ω) y z‖ ^ ((2 * (n + 1) + 2) * p) ∂(μ W x.L) ≤ Bc)
    (σ : Fin (n + 1) → Bool) {R₂ : ℝ}
    (hR₂ : ∀ j y, ∑ z, ‖pairU (gammaG x.g)
      (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E)) x.u v (σ j)
      (σ (finRotate (n + 1) j)) y z‖ ≤ R₂)
    (a : Fin (n + 1) → Fin x.L) :
    coneCrudeMom (μ W x.L) p (fun ω => blockGen W x.L (gammaG x.g) (fun r N => ∑ b,
            (∏ j, pairU (gammaG x.g)
              (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E)) r v (σ j)
              (σ (finRotate (n + 1) j)) (a j) (b j)) *
            (resLoop x.g x.E (mRoot x.g x.L x.E) b σ r N -
              primLoop x.g W x.L x.E (mRoot x.g x.L x.E) r b σ)) x.u
            (flowH x.g W x.L x.u ω))
      ((R₂ ^ (n + 1)) ^ p * (((x.L : ℝ) * (10 * ((n + 1 : ℕ) : ℝ) ^ 2 * B ^ 2 *
        (gammaG x.g * W))) ^ p * coneCrudeBk (n + 1) p Bc)) := by
  have hγ := coneCrude_gammaG_pos x.g
  have hS := coneCrude_src_mom x W hW hroot.1 hu.2 hB hmB hpr hp hBc hcr σ
  have heq : ∀ ω : Ω W x.L, blockGen W x.L (gammaG x.g) (fun r N => ∑ b,
            (∏ j, pairU (gammaG x.g)
              (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E)) r v (σ j)
              (σ (finRotate (n + 1) j)) (a j) (b j)) *
            (resLoop x.g x.E (mRoot x.g x.L x.E) b σ r N -
              primLoop x.g W x.L x.E (mRoot x.g x.L x.E) r b σ)) x.u
            (flowH x.g W x.L x.u ω) =
      ∑ b, (∏ j, pairU (gammaG x.g)
              (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E)) x.u v (σ j)
              (σ (finRotate (n + 1) j)) (a j) (b j)) *
        (lightW x.g x.E (mRoot x.g x.L x.E) b σ x.u (flowH x.g W x.L x.u ω) +
          ((gammaG x.g * W : ℝ) : ℂ) *
            (cutSrcLin (fun n c τ => primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u (k := n) c τ)
                (errFam x.g x.E (mRoot x.g x.L x.E)
                  (fun n c τ => primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u (k := n) c τ) x.u
                  (flowH x.g W x.L x.u ω)) b σ +
              cutSrcQuad (errFam x.g x.E (mRoot x.g x.L x.E)
                  (fun n c τ => primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u (k := n) c τ) x.u
                  (flowH x.g W x.L x.u ω)) b σ)) := fun ω =>
    blockGen_propagated x.g x.E (mRoot x.g x.L x.E) hroot.1 (k := n + 1) (by omega) hu.2
      (flowH_isHermitian x.g W x.L x.u ω)
      (fun r n b τ => primLoop x.g W x.L x.E (mRoot x.g x.L x.E) r (k := n) b τ)
      (coneCrude_primDeriv x.g W x.L hW hL x.E _ hroot x.u hu)
      (fun y z s t => primLoop_two_swap x.g W x.L x.E _ x.u y z s t) σ
      (fun j r => pairU (gammaG x.g)
        (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E)) r v (σ j)
        (σ (finRotate (n + 1) j)))
      (fun j y z => pairU_hasDerivAt x.g W x.L hW hL x.E _ hroot (σ j) (σ (finRotate (n + 1) j))
        hu hv y z) a
  refine coneCrude_mom_congr (fun ω => (heq ω).symm) ?_
  exact coneCrude_mom_sum_le (μ W x.L) hp _ _
    (mul_nonneg (by positivity) (coneCrudeBk_nonneg _ _ hBc)) (fun b => hS b)
    (coneCrude_prod_rows _ a fun j => hR₂ j (a j))

/-- Moments of the projected combination `𝒬F(b)` from uniform moments of `F`. -/
private lemma coneCrude_projQ_mom {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] {p : ℕ} (hp : 1 ≤ p) {L n : ℕ} (θ : Fin L → ℝ)
    (hθ0 : ∀ d, 0 ≤ θ d) {T : ℝ} (hT : ∀ b : Fin (n + 1) → Fin L,
      ∏ j : Fin n, θ (b 0 - b j.succ) ≤ T)
    (F : Ω' → (Fin (n + 1) → Fin L) → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ b, coneCrudeMom P p (fun ω => F ω b) B) (b : Fin (n + 1) → Fin L) :
    coneCrudeMom P p (fun ω => projQ θ (F ω) b) ((1 + T * (L : ℝ) ^ n) ^ p * B) := by
  refine coneCrude_mom_congr (fun ω => (coneCrude_projQ_eq θ (F ω) b).symm) ?_
  refine coneCrude_mom_sum_le P hp _ (fun b' ω => F ω b') hB hF ?_
  refine (coneCrude_projQ_weight b _).trans ?_
  have hn : ‖∏ j : Fin n, ((θ (b 0 - b j.succ) : ℝ) : ℂ)‖ ≤ T := by
    rw [norm_prod]
    refine le_trans (le_of_eq (Finset.prod_congr rfl fun j _ => ?_)) (hT b)
    rw [Complex.norm_real, Real.norm_of_nonneg (hθ0 _)]
  have := mul_le_mul_of_nonneg_right hn (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ n)
  linarith

/-- Moments of the signed row `h(c) = Σ_{b₀ = c} F(b)` from uniform moments of `F`. -/
private lemma coneCrude_rowSum_mom {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] {p : ℕ} (hp : 1 ≤ p) {L n : ℕ}
    (F : Ω' → (Fin (n + 1) → Fin L) → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ b, coneCrudeMom P p (fun ω => F ω b) B) (c : Fin L) :
    coneCrudeMom P p (fun ω => rowSum (F ω) c) (((L : ℝ) ^ n) ^ p * B) := by
  refine coneCrude_mom_congr (fun ω => ?_) (coneCrude_mom_sum_le P hp
    (fun b : Fin (n + 1) → Fin L => if b 0 = c then (1 : ℂ) else 0) (fun b ω => F ω b) hB hF
    (le_of_eq ?_))
  · unfold rowSum
    exact Finset.sum_congr rfl fun b _ => by split_ifs <;> simp
  · rw [← coneCrude_count c]
    exact Finset.sum_congr rfl fun b _ => by split_ifs <;> simp

/-- Moments of the generator of the propagated projected field (C.35)
[fo:eq:projected-error-equation] (cyclically alternating words) at one point. -/
private lemma coneCrude_genProj_point (x : FlowPt) (W : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ x.L)
    (hroot : IsDysonRootV (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))
    (hu : x.u ∈ Set.Ioo (-1 : ℝ) 1) {v : ℝ} (hv : v ∈ Set.Ioo (-1 : ℝ) 1) {n : ℕ} (hn : 1 ≤ n)
    {B : ℝ} (hB : 1 ≤ B) (hmB : ‖mRoot x.g x.L x.E‖ ≤ B)
    (hpr : ∀ j : ℕ, 2 ≤ j → j ≤ n + 1 → ∀ (b : Fin j → Fin x.L) (τ : Fin j → Bool),
      ‖primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b τ‖ ≤ B)
    (hprk : ∀ (b : Fin (n + 1) → Fin x.L) (τ : Fin (n + 1) → Bool),
      ‖primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b τ‖ ≤ B)
    {p : ℕ} (hp : 1 ≤ p) {Bc : ℝ} (hBc : 0 ≤ Bc)
    (hcr : ∀ y z : Fin x.L,
      Integrable (fun ω => ‖blockOf (flowG W x ω) y z‖ ^ ((2 * (n + 1) + 2) * p)) (μ W x.L) ∧
        ∫ ω, ‖blockOf (flowG W x ω) y z‖ ^ ((2 * (n + 1) + 2) * p) ∂(μ W x.L) ≤ Bc)
    {T ρ κ : ℝ}
    (hθ0 : ∀ d, 0 ≤ wardProfile (pairP (gammaG x.g)
      (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) x.u d)
    (hT : ∀ b : Fin (n + 1) → Fin x.L, ∏ j : Fin n, wardProfile (pairP (gammaG x.g)
      (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) x.u (b 0 - b j.succ) ≤ T)
    (hK0 : ∀ y z, 0 ≤ mixedKer (pairP (gammaG x.g)
      (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) x.u y z)
    (hKr : ∀ y, ∑ z, mixedKer (pairP (gammaG x.g)
      (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) x.u y z ≤ κ)
    (hU0 : ∀ y z, 0 ≤ (1 + (v - x.u) • mixedKer (pairP (gammaG x.g)
      (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) v) y z)
    (hUr : ∀ y, ∑ z, (1 + (v - x.u) • mixedKer (pairP (gammaG x.g)
      (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) v) y z ≤ ρ)
    (σ : Fin (n + 1) → Bool) (hσ : ∀ j, σ (finRotate (n + 1) j) = !σ j)
    (a : Fin (n + 1) → Fin x.L) :
    coneCrudeMom (μ W x.L) p (fun ω => blockGen W x.L (gammaG x.g) (fun r N => ∑ b,
              projCoef (pairP (gammaG x.g)
                (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) v r a b *
              (resLoop x.g x.E (mRoot x.g x.L x.E) b σ r N -
                primLoop x.g W x.L x.E (mRoot x.g x.L x.E) r b σ)) x.u
              (flowH x.g W x.L x.u ω))
      ((ρ ^ (n + 1)) ^ p * (2 ^ p * ((1 + T * (x.L : ℝ) ^ n) ^ p *
        (((x.L : ℝ) * (10 * ((n + 1 : ℕ) : ℝ) ^ 2 * B ^ 2 * (gammaG x.g * W))) ^ p *
          coneCrudeBk (n + 1) p Bc) +
        (2 * T * κ) ^ p * (((x.L : ℝ) ^ n) ^ p * ((2 * B) ^ p * coneCrudeBk (n + 1) p Bc))))) := by
  have hγ := coneCrude_gammaG_pos x.g
  have hBk := coneCrudeBk_nonneg (n + 1) p hBc
  have hB0 : 0 ≤ B := by linarith
  have hT0 : 0 ≤ T := by
    have h0 := hT (fun _ => a 0)
    exact le_trans (Finset.prod_nonneg fun j _ => hθ0 _) h0
  set P := pairP (gammaG x.g) (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))
    with hPdef
  set S : Ω W x.L → (Fin (n + 1) → Fin x.L) → ℂ := fun ω b =>
    lightW x.g x.E (mRoot x.g x.L x.E) b σ x.u (flowH x.g W x.L x.u ω) +
        ((gammaG x.g * W : ℝ) : ℂ) *
          (cutSrcLin (fun n c τ => primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u (k := n) c τ)
              (errFam x.g x.E (mRoot x.g x.L x.E)
                (fun n c τ => primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u (k := n) c τ) x.u
                (flowH x.g W x.L x.u ω)) b σ +
            cutSrcQuad (errFam x.g x.E (mRoot x.g x.L x.E)
                (fun n c τ => primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u (k := n) c τ) x.u
                (flowH x.g W x.L x.u ω)) b σ) with hSdef
  set D : Ω W x.L → (Fin (n + 1) → Fin x.L) → ℂ := fun ω b => flowErr W x b σ ω with hDdef
  have hS : ∀ b, coneCrudeMom (μ W x.L) p (fun ω => S ω b)
      (((x.L : ℝ) * (10 * ((n + 1 : ℕ) : ℝ) ^ 2 * B ^ 2 * (gammaG x.g * W))) ^ p *
        coneCrudeBk (n + 1) p Bc) := fun b =>
    coneCrude_src_mom x W hW hroot.1 hu.2 hB hmB hpr hp hBc hcr σ b
  have hD : ∀ b, coneCrudeMom (μ W x.L) p (fun ω => D ω b)
      ((2 * B) ^ p * coneCrudeBk (n + 1) p Bc) := fun b =>
    coneCrude_err_mom x W hW hroot.1 hu.2 (by omega) hB hprk hp hBc hcr σ b
  have heq : ∀ ω : Ω W x.L, blockGen W x.L (gammaG x.g) (fun r N => ∑ b,
              projCoef P v r a b *
              (resLoop x.g x.E (mRoot x.g x.L x.E) b σ r N -
                primLoop x.g W x.L x.E (mRoot x.g x.L x.E) r b σ)) x.u
              (flowH x.g W x.L x.u ω) =
      ∑ b, (∏ j, (((1 + (v - x.u) • mixedKer P v) (a j) (b j) : ℝ) : ℂ)) *
        (projQ (wardProfile P x.u) (S ω) b +
          ∑ c, ((mixedKer P x.u (b 0) c : ℝ) : ℂ) * rowSum (D ω) c *
            (∏ j : Fin n, ((wardProfile P x.u (c - b j.succ) : ℝ) : ℂ) -
              ∏ j : Fin n, ((wardProfile P x.u (b 0 - b j.succ) : ℝ) : ℂ))) := fun ω =>
    blockGen_projField x.g x.E (mRoot x.g x.L x.E) hW hL hn hroot hu hv
      (flowH_isHermitian x.g W x.L x.u ω) σ hσ a
  refine coneCrude_mom_congr (fun ω => (heq ω).symm) ?_
  -- the bracket at each word
  have hQ : ∀ b, coneCrudeMom (μ W x.L) p (fun ω => projQ (wardProfile P x.u) (S ω) b)
      ((1 + T * (x.L : ℝ) ^ n) ^ p *
        (((x.L : ℝ) * (10 * ((n + 1 : ℕ) : ℝ) ^ 2 * B ^ 2 * (gammaG x.g * W))) ^ p *
          coneCrudeBk (n + 1) p Bc)) := fun b =>
    coneCrude_projQ_mom (μ W x.L) hp _ hθ0 hT S (by positivity) hS b
  have hR : ∀ c, coneCrudeMom (μ W x.L) p (fun ω => rowSum (D ω) c)
      (((x.L : ℝ) ^ n) ^ p * ((2 * B) ^ p * coneCrudeBk (n + 1) p Bc)) := fun c =>
    coneCrude_rowSum_mom (μ W x.L) hp D (by positivity) hD c
  have hC : ∀ b : Fin (n + 1) → Fin x.L, coneCrudeMom (μ W x.L) p (fun ω =>
      ∑ c, ((mixedKer P x.u (b 0) c : ℝ) : ℂ) * rowSum (D ω) c *
        (∏ j : Fin n, ((wardProfile P x.u (c - b j.succ) : ℝ) : ℂ) -
          ∏ j : Fin n, ((wardProfile P x.u (b 0 - b j.succ) : ℝ) : ℂ)))
      ((2 * T * κ) ^ p * (((x.L : ℝ) ^ n) ^ p * ((2 * B) ^ p * coneCrudeBk (n + 1) p Bc))) := by
    intro b
    refine coneCrude_mom_congr (fun ω => Finset.sum_congr rfl fun c _ => by ring)
      (coneCrude_mom_sum_le (μ W x.L) hp (fun c => ((mixedKer P x.u (b 0) c : ℝ) : ℂ) *
        (∏ j : Fin n, ((wardProfile P x.u (c - b j.succ) : ℝ) : ℂ) -
          ∏ j : Fin n, ((wardProfile P x.u (b 0 - b j.succ) : ℝ) : ℂ)))
        (fun c ω => rowSum (D ω) c) (by positivity) hR ?_)
    have hn : ∀ c' : Fin x.L, ∀ b' : Fin (n + 1) → Fin x.L, b' 0 = c' →
        ‖∏ j : Fin n, ((wardProfile P x.u (c' - b' j.succ) : ℝ) : ℂ)‖ ≤ T := by
      intro c' b' hb'
      rw [norm_prod, ← hb']
      refine le_trans (le_of_eq (Finset.prod_congr rfl fun j _ => ?_)) (hT b')
      rw [Complex.norm_real, Real.norm_of_nonneg (hθ0 _)]
    calc ∑ c, ‖((mixedKer P x.u (b 0) c : ℝ) : ℂ) *
          (∏ j : Fin n, ((wardProfile P x.u (c - b j.succ) : ℝ) : ℂ) -
            ∏ j : Fin n, ((wardProfile P x.u (b 0 - b j.succ) : ℝ) : ℂ))‖
        ≤ ∑ c, mixedKer P x.u (b 0) c * (2 * T) := by
          refine Finset.sum_le_sum fun c _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hK0 _ _)]
          refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (hK0 _ _)
          have h1 := hn c (Fin.cons c (fun j => b j.succ)) (by simp)
          have h2 := hn (b 0) b rfl
          simp only [Fin.cons_succ] at h1
          linarith
      _ = (∑ c, mixedKer P x.u (b 0) c) * (2 * T) := by rw [Finset.sum_mul]
      _ ≤ κ * (2 * T) := mul_le_mul_of_nonneg_right (hKr _) (by positivity)
      _ = 2 * T * κ := by ring
  have hκ : 0 ≤ κ := le_trans (Finset.sum_nonneg fun z _ => hK0 _ z) (hKr (a 0))
  have hZ := fun b => coneCrude_mom_add (μ W x.L) hp (hQ b) (hC b)
  refine coneCrude_mom_sum_le (μ W x.L) hp _ _ (by positivity) hZ ?_
  refine (le_of_eq ?_).trans (coneCrude_prod_rows
    (fun j y z => (((1 + (v - x.u) • mixedKer P v) y z : ℝ) : ℂ)) a (R := ρ) fun j => ?_)
  · exact Finset.sum_congr rfl fun b _ => rfl
  · refine le_trans (le_of_eq (Finset.sum_congr rfl fun z _ => ?_)) (hUr (a j))
    rw [Complex.norm_real, Real.norm_of_nonneg (hU0 _ _)]

/-- Moments of the bracket (5.9) [gc:eq:bracket] of a combination `Σ_b α(b) D(b)` of loop errors
of length `k` at one point, for total weight `Σ_b |α(b)| ≤ A`. -/
private lemma coneCrude_gamma_point (x : FlowPt) (W : ℕ) (hW : 1 ≤ W)
    (hm : 0 < (mRoot x.g x.L x.E).im) (hu1 : x.u < 1) {k : ℕ} {p : ℕ} (hp : 1 ≤ p) {Bc : ℝ}
    (hBc : 0 ≤ Bc)
    (hcr : ∀ y z : Fin x.L,
      Integrable (fun ω => ‖blockOf (flowG W x ω) y z‖ ^ ((2 * k + 2) * p)) (μ W x.L) ∧
        ∫ ω, ‖blockOf (flowG W x ω) y z‖ ^ ((2 * k + 2) * p) ∂(μ W x.L) ≤ Bc)
    (σ : Fin k → Bool) (α : (Fin k → Fin x.L) → ℂ) {A : ℝ} (hA : ∑ b, ‖α b‖ ≤ A) :
    coneCrudeMom (μ W x.L) p (fun ω => blockGamma W x.L (gammaG x.g)
        (fun N => ∑ b, α b * (resLoop x.g x.E (mRoot x.g x.L x.E) b σ x.u N -
          primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b σ))
        (fun N => ∑ b, α b * (resLoop x.g x.E (mRoot x.g x.L x.E) b σ x.u N -
          primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b σ))
        (flowH x.g W x.L x.u ω))
      (A ^ p * (A ^ p * (((x.L : ℝ) * ((k : ℝ) ^ 2 * (gammaG x.g * W))) ^ p *
        coneCrudeBk k p Bc))) := by
  have hγ := coneCrude_gammaG_pos x.g
  have hBk := coneCrudeBk_nonneg k p hBc
  have hV := coneCrude_gamma_mom x W hW hm hu1 hp hBc hcr σ
  have heq : ∀ ω : Ω W x.L, blockGamma W x.L (gammaG x.g)
        (fun N => ∑ b, α b * (resLoop x.g x.E (mRoot x.g x.L x.E) b σ x.u N -
          primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b σ))
        (fun N => ∑ b, α b * (resLoop x.g x.E (mRoot x.g x.L x.E) b σ x.u N -
          primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b σ))
        (flowH x.g W x.L x.u ω) =
      ∑ b, α b * ∑ b', star (α b') * blockGamma W x.L (gammaG x.g)
        (resLoop x.g x.E (mRoot x.g x.L x.E) b σ x.u)
        (resLoop x.g x.E (mRoot x.g x.L x.E) b' σ x.u) (flowH x.g W x.L x.u ω) := by
    intro ω
    have hdiff := fun (b : Fin k → Fin x.L) c κ => coneCrude_err_diff (W := W) x.g x.E
      (mRoot x.g x.L x.E) hm hu1 (flowH_isHermitian x.g W x.L x.u ω)
      (primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b σ) σ b c κ
    rw [blockGamma_tensor (gammaG x.g) α α
      (fun b N => resLoop x.g x.E (mRoot x.g x.L x.E) b σ x.u N -
        primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b σ)
      (fun b N => resLoop x.g x.E (mRoot x.g x.L x.E) b σ x.u N -
        primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b σ) _ hdiff hdiff]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b' _ => ?_
    have e : blockGamma W x.L (gammaG x.g)
        (fun N => resLoop x.g x.E (mRoot x.g x.L x.E) b σ x.u N -
          primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b σ)
        (fun N => resLoop x.g x.E (mRoot x.g x.L x.E) b' σ x.u N -
          primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b' σ) (flowH x.g W x.L x.u ω) =
        blockGamma W x.L (gammaG x.g) (resLoop x.g x.E (mRoot x.g x.L x.E) b σ x.u)
          (resLoop x.g x.E (mRoot x.g x.L x.E) b' σ x.u) (flowH x.g W x.L x.u ω) := by
      simp only [blockGamma, deriv_sub_const]
    rw [e]; ring
  refine coneCrude_mom_congr (fun ω => (heq ω).symm) ?_
  have hA0 : 0 ≤ A := (Finset.sum_nonneg fun b _ => norm_nonneg _).trans hA
  have hin : ∀ b, coneCrudeMom (μ W x.L) p (fun ω => ∑ b', star (α b') *
      blockGamma W x.L (gammaG x.g) (resLoop x.g x.E (mRoot x.g x.L x.E) b σ x.u)
        (resLoop x.g x.E (mRoot x.g x.L x.E) b' σ x.u) (flowH x.g W x.L x.u ω))
      (A ^ p * (((x.L : ℝ) * ((k : ℝ) ^ 2 * (gammaG x.g * W))) ^ p * coneCrudeBk k p Bc)) :=
    fun b => coneCrude_mom_sum_le (μ W x.L) hp (fun b' => star (α b')) _ (by positivity)
      (fun b' => hV b b') (by simpa only [norm_star] using hA)
  exact coneCrude_mom_sum_le (μ W x.L) hp α _ (by positivity) hin hA

/-- `E‖X c‖^p ≤ ‖c‖^p B`. -/
private lemma coneCrude_mom_mul_const {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] {p : ℕ} (hp : 1 ≤ p) {X : Ω' → ℂ} {B : ℝ} (c : ℂ)
    (hX : coneCrudeMom P p X B) : coneCrudeMom P p (fun ω => X ω * c) (‖c‖ ^ p * B) := by
  have h := coneCrude_mom_sum P hp (fun _ : Unit => c) (fun _ => X) (fun _ => hX)
  simp only [Finset.univ_unique, Finset.sum_singleton] at h
  exact coneCrude_mom_congr (fun ω => mul_comm _ _) h

/-- `Σ_b Π_j U_{a_j b_j} ≤ R^k` for nonnegative real propagators with rows `≤ R`. -/
private lemma coneCrude_prod_rows_real {L k : ℕ} (U : Matrix (Fin L) (Fin L) ℝ)
    (a : Fin k → Fin L) {R : ℝ} (hU0 : ∀ y z, 0 ≤ U y z) (hR : ∀ y, ∑ z, U y z ≤ R) :
    ∑ b : Fin k → Fin L, ∏ j, U (a j) (b j) ≤ R ^ k := by
  have h := coneCrude_prod_rows (fun _ y z => ((U y z : ℝ) : ℂ)) a (R := R) fun j => by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun z _ => ?_)) (hR (a j))
    rw [Complex.norm_real, Real.norm_of_nonneg (hU0 _ _)]
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_)) h
  rw [← Complex.ofReal_prod, Complex.norm_real,
    Real.norm_of_nonneg (Finset.prod_nonneg fun j _ => hU0 _ _)]

end GenPoint

/-! ### The regime at the reached points -/

section Regime

/-- `B = C W^{1 + |C_ζ|(n + 1)}`, the bound on `|m|` and on the primitive loops. -/
private def coneCrudeB (C Cζ : ℝ) (n W : ℕ) : ℝ := C * (W : ℝ) ^ (1 + |Cζ| * (n + 1))

/-- The exponent `2(1 + |C_ζ|(n + 1)) + C(n + 1) + 4` of the common polynomial scale. -/
private def coneCrudeE (C Cζ : ℝ) (n : ℕ) : ℝ := 2 * (1 + |Cζ| * (n + 1)) + C * (n + 1) + 4

/-- `Λ = W^{2(1 + |C_ζ|(n + 1)) + C(n + 1) + 4}`, the common polynomial scale. -/
private def coneCrudeLam (C Cζ : ℝ) (n W : ℕ) : ℝ := (W : ℝ) ^ coneCrudeE C Cζ n

/-- The deterministic facts at a reached point `x` with terminal time `v`. -/
private structure coneCrudeAt (n : ℕ) (C Cζ : ℝ) (W : ℕ) (x : FlowPt) (v : ℝ) : Prop where
  hW : 1 ≤ W
  hL : 3 ≤ x.L
  root : IsDysonRootV (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E)
  hu : x.u ∈ Set.Ioo (-1 : ℝ) 1
  hv : v ∈ Set.Ioo (-1 : ℝ) 1
  hℓ : 0 < ellProp x.g x.L x.u
  hB : 1 ≤ coneCrudeB C Cζ n W
  hmB : ‖mRoot x.g x.L x.E‖ ≤ coneCrudeB C Cζ n W
  hpr : ∀ j : ℕ, 2 ≤ j → j ≤ n + 1 → ∀ (b : Fin j → Fin x.L) (τ : Fin j → Bool),
    ‖primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b τ‖ ≤ coneCrudeB C Cζ n W
  hprk : ∀ (b : Fin (n + 1) → Fin x.L) (τ : Fin (n + 1) → Bool),
    ‖primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b τ‖ ≤ coneCrudeB C Cζ n W
  hθ0 : ∀ d, 0 ≤ wardProfile (pairP (gammaG x.g)
    (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) x.u d
  hT : ∀ b : Fin (n + 1) → Fin x.L, ∏ j : Fin n, wardProfile (pairP (gammaG x.g)
    (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) x.u (b 0 - b j.succ) ≤
      ((C + 1) / ellProp x.g x.L x.u) ^ n
  hK0 : ∀ y z, 0 ≤ mixedKer (pairP (gammaG x.g)
    (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) x.u y z
  hKr : ∀ y, ∑ z, mixedKer (pairP (gammaG x.g)
    (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) x.u y z ≤ (1 - x.u)⁻¹
  hU0 : ∀ y z, 0 ≤ (1 + (v - x.u) • mixedKer (pairP (gammaG x.g)
    (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) v) y z
  hUr : ∀ y, ∑ z, (1 + (v - x.u) • mixedKer (pairP (gammaG x.g)
    (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) v) y z ≤
      (1 - x.u) / (1 - v)
  hR₂ : ∀ (s s' : Bool) (y : Fin x.L), ∑ z, ‖pairU (gammaG x.g)
    (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E)) x.u v s s' y z‖ ≤
      (1 - x.u) / (1 - v) + (1 + C) * C
  hΛ : 1 ≤ coneCrudeLam C Cζ n W
  hρΛ : (1 - x.u) / (1 - v) ≤ coneCrudeLam C Cζ n W
  hTΛ : 1 + ((C + 1) / ellProp x.g x.L x.u) ^ n * (x.L : ℝ) ^ n ≤
    (1 + (C + 1) ^ n) * coneCrudeLam C Cζ n W
  hwΛ : (x.L : ℝ) * (10 * ((n + 1 : ℕ) : ℝ) ^ 2 * coneCrudeB C Cζ n W ^ 2 * (gammaG x.g * W)) ≤
    10 * ((n + 1 : ℕ) : ℝ) ^ 2 * C ^ 2 * coneCrudeLam C Cζ n W
  hcΛ : 2 * ((C + 1) / ellProp x.g x.L x.u) ^ n * (1 - x.u)⁻¹ * (x.L : ℝ) ^ n ≤
    2 * (C + 1) ^ n * coneCrudeLam C Cζ n W
  hBΛ : 2 * coneCrudeB C Cζ n W ≤ 2 * C * coneCrudeLam C Cζ n W
  hR₂Λ : (1 - x.u) / (1 - v) + (1 + C) * C ≤ (1 + (1 + C) * C) * coneCrudeLam C Cζ n W
  hgΛ : (x.L : ℝ) * (((n + 1 : ℕ) : ℝ) ^ 2 * (gammaG x.g * W)) ≤
    ((n + 1 : ℕ) : ℝ) ^ 2 * coneCrudeLam C Cζ n W

/-- A primitive loop of length one is `m^σ`. -/
private lemma coneCrude_primLoop_one (g : ℝ) (W L : ℕ) (E : ℝ) (m : ℂ) (t : ℝ)
    (a : Fin 1 → Fin L) (σ : Fin 1 → Bool) : ‖primLoop g W L E m t a σ‖ = ‖m‖ := by
  unfold primLoop primK primF
  cases h : σ 0 <;> simp [h]

/-- The kernel facts at a root: the Ward profile at time `u` in `[0, (C+1)/ℓ]`, `K_u ≥ 0` with
row `(1 - u)⁻¹`, and `U = I + (v - u)K_v ≥ 0` with row `(1 - u)/(1 - v)`. -/
private lemma coneCrude_kernelFacts {L : ℕ} (hL1 : 1 ≤ L) (P : Matrix (Fin L) (Fin L) ℝ)
    (hP0 : ∀ y z, 0 ≤ P y z) (hProw : ∀ y, ∑ z, P y z = 1) {u v C ℓ : ℝ} (hu0 : 0 ≤ u)
    (huv : u ≤ v) (hv1 : v < 1) (hℓ0 : 0 < ℓ) (hKle : ∀ y z, mixedKer P u y z ≤
      C / ((1 - u) * ℓ) + ℓ⁻¹) (n : ℕ) :
    (∀ d, 0 ≤ wardProfile P u d) ∧
    (∀ b : Fin (n + 1) → Fin L, ∏ j : Fin n, wardProfile P u (b 0 - b j.succ) ≤
      ((C + 1) / ℓ) ^ n) ∧
    (∀ y z, 0 ≤ mixedKer P u y z) ∧ (∀ y, ∑ z, mixedKer P u y z ≤ (1 - u)⁻¹) ∧
    (∀ y z, 0 ≤ (1 + (v - u) • mixedKer P v) y z) ∧
    (∀ y, ∑ z, (1 + (v - u) • mixedKer P v) y z ≤ (1 - u) / (1 - v)) := by
  have h1v : 0 < 1 - v := by linarith
  have h1u : 0 < 1 - u := by linarith
  have hv0 : 0 ≤ v := le_trans hu0 huv
  obtain ⟨hKu0, hKur⟩ := mixedKer_nonneg_row P hP0 hProw u hu0 (by linarith)
  obtain ⟨hKv0, hKvr⟩ := mixedKer_nonneg_row P hP0 hProw v hv0 hv1
  have hθ : ∀ d', 0 ≤ wardProfile P u d' ∧ wardProfile P u d' ≤ (C + 1) / ℓ := by
    intro d'
    obtain ⟨h0, h1⟩ := coneCrude_wardProfile_le hL1 P (by linarith) hKu0 hKle d'
    refine ⟨h0, h1.trans ?_⟩
    rw [show (1 - u) * (C / ((1 - u) * ℓ) + ℓ⁻¹) = (C + (1 - u)) / ℓ by field_simp]
    exact div_le_div_of_nonneg_right (by linarith) hℓ0.le
  refine ⟨fun d => (hθ d).1, fun b => ?_, hKu0, fun y => (hKur y).le, fun y z => ?_,
    fun y => le_of_eq ?_⟩
  · calc ∏ j : Fin n, wardProfile P u (b 0 - b j.succ) ≤ ∏ _j : Fin n, (C + 1) / ℓ :=
          Finset.prod_le_prod₀ (fun j _ => (hθ _).1) fun j _ => (hθ _).2
      _ = ((C + 1) / ℓ) ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    have : 0 ≤ (if y = z then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    nlinarith [hKv0 y z, sub_nonneg.mpr huv]
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hKvr y, Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    field_simp
    ring

/-- Rows of the propagators `U^{σσ'}_{u,v}` of (5.15) [fo:eq:propagators] at a root: at most
`(1 - u)/(1 - v) + (1 + C)C` under the Dyson bounds (6.2) [fo:eq:propagation-dyson]. -/
private lemma coneCrude_pairU_rows {L : ℕ} (β : ℝ) (hβ : 0 < β) (M : Matrix (Fin L) (Fin L) ℂ)
    (hP0 : ∀ y z, 0 ≤ pairP β M y z) (hProw : ∀ y, ∑ z, pairP β M y z = 1) {u v C : ℝ}
    (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1) (hC0 : 0 ≤ C)
    (hMrow : ∀ y, β * ∑ z, (‖M y z‖ + ‖M y z‖ ^ 2) ≤ C)
    (hQinv : ∀ y, ∑ z, ‖(1 - (v : ℂ) • pairQ β M)⁻¹ y z‖ ≤ C)
    (s s' : Bool) (y : Fin L) :
    ∑ z, ‖pairU β M u v s s' y z‖ ≤ (1 - u) / (1 - v) + (1 + C) * C := by
  have h1v : 0 < 1 - v := by linarith
  have h1u : 0 < 1 - u := by linarith
  have hρ0 : 0 ≤ (1 - u) / (1 - v) := div_nonneg h1u.le h1v.le
  have hQrow : ∀ y, ∑ c, ‖(1 - (u : ℂ) • pairQ β M) y c‖ ≤ 1 + C := by
    intro y
    have hM2 : β * ∑ c, ‖M y c‖ ^ 2 ≤ C := by
      refine le_trans ?_ (hMrow y)
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => ?_) hβ.le
      have := norm_nonneg (M y c)
      linarith
    have hX0 : 0 ≤ β * ∑ c, ‖M y c‖ ^ 2 := by positivity
    have hu1 : u ≤ 1 := by linarith
    calc ∑ c, ‖(1 - (u : ℂ) • pairQ β M) y c‖
        ≤ ∑ c, ((if y = c then (1 : ℝ) else 0) + u * (β * ‖M y c‖ ^ 2)) := by
          refine Finset.sum_le_sum fun c _ => ?_
          rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
          refine (norm_sub_le _ _).trans (add_le_add ?_ (le_of_eq ?_))
          · rw [Matrix.one_apply]; split_ifs <;> simp
          · simp only [pairQ, Matrix.of_apply, norm_mul, Complex.norm_real, norm_pow,
              Real.norm_eq_abs, abs_of_nonneg hu0, abs_of_pos hβ]
      _ = 1 + u * (β * ∑ c, ‖M y c‖ ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
          simp [Finset.mul_sum]
      _ ≤ 1 + C := by
          have : u * (β * ∑ c, ‖M y c‖ ^ 2) ≤ β * ∑ c, ‖M y c‖ ^ 2 :=
            mul_le_of_le_one_left hX0 hu1
          linarith
  have hPP : ∑ z, ‖propPP (pairQ β M) u v y z‖ ≤ (1 + C) * C := by
    have h1 := coneCrude_mul_row (1 - (u : ℂ) • pairQ β M) ((1 - (v : ℂ) • pairQ β M)⁻¹) y hQinv
    exact h1.trans (mul_le_mul_of_nonneg_right (hQrow y) hC0)
  obtain ⟨hpm0, hpmr⟩ := propPM_nonneg_row (pairP β M) hP0 hProw u v hu0 huv hv1
  have hCC : 0 ≤ (1 + C) * C := by positivity
  unfold pairU
  split_ifs with h1 h2
  · exact hPP.trans (by linarith)
  · simp only [Matrix.map_apply, norm_star]
    exact hPP.trans (by linarith)
  · simp only [Matrix.map_apply, Complex.norm_real, Real.norm_of_nonneg (hpm0 _ _), hpmr y]
    linarith

/-- The polynomial scales at a reached point. -/
private lemma coneCrude_scales (n : ℕ) {C Cζ : ℝ} (hC1 : 1 ≤ C) {W L : ℕ} (hW1 : 1 ≤ W)
    {u v γ ℓ : ℝ} (hu12 : 1 / 2 ≤ u) (huv : u ≤ v) (hv3 : ((W : ℝ) ^ 3)⁻¹ ≤ 1 - v)
    (hℓ0 : 0 < ℓ) (hγL : γ * L ≤ (W : ℝ) ^ C) (hLℓ : L / ℓ ≤ (W : ℝ) ^ C) :
    1 ≤ coneCrudeLam C Cζ n W ∧
    (1 - u) / (1 - v) ≤ coneCrudeLam C Cζ n W ∧
    1 + ((C + 1) / ℓ) ^ n * (L : ℝ) ^ n ≤ (1 + (C + 1) ^ n) * coneCrudeLam C Cζ n W ∧
    (L : ℝ) * (10 * ((n + 1 : ℕ) : ℝ) ^ 2 * coneCrudeB C Cζ n W ^ 2 * (γ * W)) ≤
      10 * ((n + 1 : ℕ) : ℝ) ^ 2 * C ^ 2 * coneCrudeLam C Cζ n W ∧
    2 * ((C + 1) / ℓ) ^ n * (1 - u)⁻¹ * (L : ℝ) ^ n ≤ 2 * (C + 1) ^ n * coneCrudeLam C Cζ n W ∧
    2 * coneCrudeB C Cζ n W ≤ 2 * C * coneCrudeLam C Cζ n W ∧
    (1 - u) / (1 - v) + (1 + C) * C ≤ (1 + (1 + C) * C) * coneCrudeLam C Cζ n W ∧
    (L : ℝ) * (((n + 1 : ℕ) : ℝ) ^ 2 * (γ * W)) ≤
      ((n + 1 : ℕ) : ℝ) ^ 2 * coneCrudeLam C Cζ n W := by
  set Wr : ℝ := (W : ℝ) with hWr
  have hWr1 : (1 : ℝ) ≤ Wr := by rw [hWr]; exact_mod_cast hW1
  have hWr0 : (0 : ℝ) < Wr := by linarith
  have hC0 : 0 ≤ C := le_trans zero_le_one hC1
  set b₀ : ℝ := 1 + |Cζ| * (n + 1) with hb₀
  set E₀ : ℝ := 2 * b₀ + C * (n + 1) + 4 with hE₀
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hb₀1 : 1 ≤ b₀ := by
    have := mul_nonneg (abs_nonneg Cζ) (by positivity : (0 : ℝ) ≤ n + 1)
    simp only [hb₀]; linarith
  have hCn : 0 ≤ C * n := mul_nonneg hC0 hn0
  have hE₀' : E₀ = 2 * b₀ + C * n + C + 4 := by simp only [hE₀]; ring
  have hLam : coneCrudeLam C Cζ n W = Wr ^ E₀ := rfl
  have hBdef : coneCrudeB C Cζ n W = C * Wr ^ b₀ := rfl
  have hpow : ∀ a b : ℝ, a ≤ b → Wr ^ a ≤ Wr ^ b := fun a b h =>
    Real.rpow_le_rpow_of_exponent_le hWr1 h
  have hW3 : Wr ^ (3 : ℝ) = Wr ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hWp3 : 0 < Wr ^ 3 := by positivity
  have hv1 : v < 1 := by
    have : 0 < (Wr ^ 3)⁻¹ := inv_pos.2 hWp3
    linarith
  have h1v : 0 < 1 - v := by linarith
  have h1u : 0 < 1 - u := by linarith
  have hLam1 : 1 ≤ Wr ^ E₀ := Real.one_le_rpow hWr1 (by linarith)
  -- `W³`, `(1 - u)⁻¹` and `ρ`
  have h3Λ : Wr ^ 3 ≤ Wr ^ E₀ := by
    rw [← hW3]; exact hpow _ _ (by linarith)
  have hinv : (1 - v)⁻¹ ≤ Wr ^ 3 := by
    rw [inv_le_comm₀ h1v hWp3]; exact hv3
  have hκ : (1 - u)⁻¹ ≤ Wr ^ 3 :=
    le_trans (inv_anti₀ h1v (by linarith)) hinv
  have hρ : (1 - u) / (1 - v) ≤ Wr ^ 3 := by
    rw [div_eq_mul_inv]
    calc (1 - u) * (1 - v)⁻¹ ≤ 1 * (1 - v)⁻¹ :=
          mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 h1v.le)
      _ ≤ Wr ^ 3 := by rw [one_mul]; exact hinv
  -- `T L^n`
  have hTL : ((C + 1) / ℓ) ^ n * (L : ℝ) ^ n ≤ (C + 1) ^ n * Wr ^ (C * n) := by
    rw [← mul_pow, Real.rpow_mul_natCast hWr0.le, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ n
    rw [div_mul_eq_mul_div, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hLℓ (by linarith)
  have hCnΛ : Wr ^ (C * n) ≤ Wr ^ E₀ := hpow _ _ (by linarith)
  have hCn3 : Wr ^ (C * n) * Wr ^ 3 ≤ Wr ^ E₀ := by
    rw [← hW3, ← Real.rpow_add hWr0]; exact hpow _ _ (by linarith)
  have hC1n : 0 ≤ (C + 1) ^ n := by positivity
  have hTL0 : 0 ≤ ((C + 1) / ℓ) ^ n * (L : ℝ) ^ n := by positivity
  rw [hLam, hBdef]
  refine ⟨hLam1, hρ.trans h3Λ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left hCnΛ hC1n
    linarith
  · -- `L · 10k²B²γW`
    have hB2 : (C * Wr ^ b₀) ^ 2 = C ^ 2 * Wr ^ (2 * b₀) := by
      rw [mul_pow, mul_comm (2 : ℝ) b₀, show b₀ * 2 = b₀ * ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_mul_natCast hWr0.le]
    have hexp : Wr ^ (2 * b₀) * Wr ^ C * Wr ≤ Wr ^ E₀ := by
      rw [← Real.rpow_add hWr0]
      calc Wr ^ (2 * b₀ + C) * Wr = Wr ^ (2 * b₀ + C) * Wr ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = Wr ^ (2 * b₀ + C + 1) := by rw [← Real.rpow_add hWr0]
        _ ≤ Wr ^ E₀ := hpow _ _ (by linarith)
    have hk0 : (0 : ℝ) ≤ 10 * ((n + 1 : ℕ) : ℝ) ^ 2 * C ^ 2 := by positivity
    calc (L : ℝ) * (10 * ((n + 1 : ℕ) : ℝ) ^ 2 * (C * Wr ^ b₀) ^ 2 * (γ * Wr))
        = 10 * ((n + 1 : ℕ) : ℝ) ^ 2 * C ^ 2 * (Wr ^ (2 * b₀) * (γ * L) * Wr) := by
          rw [hB2]; ring
      _ ≤ 10 * ((n + 1 : ℕ) : ℝ) ^ 2 * C ^ 2 * (Wr ^ (2 * b₀) * Wr ^ C * Wr) := by
          refine mul_le_mul_of_nonneg_left ?_ hk0
          refine mul_le_mul_of_nonneg_right ?_ hWr0.le
          exact mul_le_mul_of_nonneg_left hγL (by positivity)
      _ ≤ 10 * ((n + 1 : ℕ) : ℝ) ^ 2 * C ^ 2 * Wr ^ E₀ := mul_le_mul_of_nonneg_left hexp hk0
  · -- `2 T κ L^n`
    have hκ0 : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 h1u.le
    calc 2 * ((C + 1) / ℓ) ^ n * (1 - u)⁻¹ * (L : ℝ) ^ n
        = 2 * (((C + 1) / ℓ) ^ n * (L : ℝ) ^ n) * (1 - u)⁻¹ := by ring
      _ ≤ 2 * ((C + 1) ^ n * Wr ^ (C * n)) * Wr ^ 3 := by
          gcongr
      _ = 2 * (C + 1) ^ n * (Wr ^ (C * n) * Wr ^ 3) := by ring
      _ ≤ 2 * (C + 1) ^ n * Wr ^ E₀ := mul_le_mul_of_nonneg_left hCn3 (by positivity)
  · have : C * Wr ^ b₀ ≤ C * Wr ^ E₀ :=
      mul_le_mul_of_nonneg_left (hpow _ _ (by linarith)) hC0
    linarith
  · have h1 : (1 - u) / (1 - v) ≤ Wr ^ E₀ := hρ.trans h3Λ
    have h2 : (1 + C) * C ≤ (1 + C) * C * Wr ^ E₀ := le_mul_of_one_le_right (by positivity) hLam1
    linarith
  · have hexp : Wr ^ C * Wr ≤ Wr ^ E₀ := by
      calc Wr ^ C * Wr = Wr ^ C * Wr ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = Wr ^ (C + 1) := by rw [← Real.rpow_add hWr0]
        _ ≤ Wr ^ E₀ := hpow _ _ (by linarith)
    have hk0 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
    calc (L : ℝ) * (((n + 1 : ℕ) : ℝ) ^ 2 * (γ * Wr))
        = ((n + 1 : ℕ) : ℝ) ^ 2 * ((γ * L) * Wr) := by ring
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * (Wr ^ C * Wr) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hγL hWr0.le) hk0
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * Wr ^ E₀ := mul_le_mul_of_nonneg_left hexp hk0

/-- The primitive loops at a reached point are at most `B`. -/
private lemma coneCrude_prim_le (n : ℕ) {C Cζ : ℝ} (hC1 : 1 ≤ C) {W : ℕ} (hW1 : 1 ≤ W)
    (x : FlowPt) (hζ0 : 0 ≤ zetaProp x.g W x.L x.u) (hζ : zetaProp x.g W x.L x.u ≤ (W : ℝ) ^ Cζ)
    (hmC : ‖mRoot x.g x.L x.E‖ ≤ C)
    (hP : ∀ j : ℕ, 2 ≤ j → j ≤ n + 1 → ∀ (b : Fin j → Fin x.L) (τ : Fin j → Bool),
      ‖primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b τ‖ ≤
        (W : ℝ) ^ (1 : ℝ) * zetaProp x.g W x.L x.u ^ (j - 1)) :
    1 ≤ coneCrudeB C Cζ n W ∧ ‖mRoot x.g x.L x.E‖ ≤ coneCrudeB C Cζ n W ∧
    (∀ j : ℕ, 2 ≤ j → j ≤ n + 1 → ∀ (b : Fin j → Fin x.L) (τ : Fin j → Bool),
      ‖primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b τ‖ ≤ coneCrudeB C Cζ n W) ∧
    ∀ (b : Fin (n + 1) → Fin x.L) (τ : Fin (n + 1) → Bool),
      ‖primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b τ‖ ≤ coneCrudeB C Cζ n W := by
  set Wr : ℝ := (W : ℝ) with hWr
  have hWr1 : (1 : ℝ) ≤ Wr := by rw [hWr]; exact_mod_cast hW1
  have hWr0 : (0 : ℝ) < Wr := by linarith
  have hC0 : 0 ≤ C := le_trans zero_le_one hC1
  set b₀ : ℝ := 1 + |Cζ| * (n + 1) with hb₀
  have hb₀0 : 0 ≤ b₀ := by
    have := mul_nonneg (abs_nonneg Cζ) (by positivity : (0 : ℝ) ≤ n + 1)
    simp only [hb₀]; linarith
  have hBdef : coneCrudeB C Cζ n W = C * Wr ^ b₀ := rfl
  rw [hBdef]
  have hWb : 1 ≤ Wr ^ b₀ := Real.one_le_rpow hWr1 hb₀0
  have hCB : C ≤ C * Wr ^ b₀ := le_mul_of_one_le_right hC0 hWb
  have hpr : ∀ j : ℕ, 2 ≤ j → j ≤ n + 1 → ∀ (b : Fin j → Fin x.L) (τ : Fin j → Bool),
      ‖primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b τ‖ ≤ C * Wr ^ b₀ := by
    intro j hj2 hjn b τ
    have h := hP j hj2 hjn b τ
    have hz : zetaProp x.g W x.L x.u ^ (j - 1) ≤ Wr ^ (|Cζ| * (n + 1)) := by
      calc zetaProp x.g W x.L x.u ^ (j - 1) ≤ (Wr ^ Cζ) ^ (j - 1) :=
            pow_le_pow_left₀ hζ0 hζ _
        _ = Wr ^ (Cζ * ((j - 1 : ℕ) : ℝ)) := (Real.rpow_mul_natCast hWr0.le _ _).symm
        _ ≤ Wr ^ (|Cζ| * (n + 1)) := by
            refine Real.rpow_le_rpow_of_exponent_le hWr1 ?_
            have hj : ((j - 1 : ℕ) : ℝ) ≤ n + 1 := by
              have : j - 1 ≤ n + 1 := by omega
              exact_mod_cast this
            have hj0 : (0 : ℝ) ≤ ((j - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
            calc Cζ * ((j - 1 : ℕ) : ℝ) ≤ |Cζ| * ((j - 1 : ℕ) : ℝ) :=
                  mul_le_mul_of_nonneg_right (le_abs_self _) hj0
              _ ≤ |Cζ| * (n + 1) := mul_le_mul_of_nonneg_left hj (abs_nonneg _)
    calc ‖primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b τ‖
        ≤ Wr ^ (1 : ℝ) * zetaProp x.g W x.L x.u ^ (j - 1) := h
      _ ≤ Wr ^ (1 : ℝ) * Wr ^ (|Cζ| * (n + 1)) :=
          mul_le_mul_of_nonneg_left hz (by positivity)
      _ = Wr ^ b₀ := by rw [← Real.rpow_add hWr0]
      _ ≤ C * Wr ^ b₀ := by
          have : Wr ^ b₀ ≤ C * Wr ^ b₀ := le_mul_of_one_le_left (by positivity) hC1
          exact this
  refine ⟨le_trans hC1 hCB, hmC.trans hCB, hpr, fun b τ => ?_⟩
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    rw [coneCrude_primLoop_one]
    exact hmC.trans hCB
  · exact hpr (n + 1) (by omega) le_rfl b τ

/-- The deterministic facts hold at every reached point for `W ≥ W₀`. -/
private lemma coneCrude_at (R : PropRegime) (n : ℕ) (Cζ : ℝ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ (d : ℕ) (x : FlowPt) (v : ℝ), d ≤ R.J →
      CmpReach R.base W d x → 1 / 2 ≤ x.u → x.u ≤ v → (W : ℝ) ^ (-3 : ℝ) ≤ 1 - v →
      zetaProp x.g W x.L x.u ≤ (W : ℝ) ^ Cζ → coneCrudeAt n R.C Cζ W x v := by
  obtain ⟨Wd, Hd⟩ := R.dyson
  obtain ⟨Wk, Hk⟩ := R.kernel 1 one_pos
  obtain ⟨Wb, Hb⟩ := R.budget
  obtain ⟨Wp, Hp⟩ := R.prim (n + 1) 1 one_pos
  refine ⟨max (max Wd Wk) (max Wb (max Wp 1)), fun W hW d x v hd hx hu12 huv hv3 hζ => ?_⟩
  have hWd : Wd ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hWk : Wk ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWb : Wb ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hWp : Wp ≤ W := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) hW
  have hW1 : 1 ≤ W := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) hW
  obtain ⟨hL3, hg0, hroot, -, -, hMC, hMrow, hQinv⟩ := Hd W hWd d x hd hx
  have hC1 : 1 ≤ R.C := R.one_le_C
  have hC0 : 0 ≤ R.C := le_trans zero_le_one hC1
  have hWr1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWr0 : (0 : ℝ) < W := by linarith
  have hγ := coneCrude_gammaG_pos x.g
  have hW3 : (W : ℝ) ^ (3 : ℝ) = (W : ℝ) ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hv3' : ((W : ℝ) ^ 3)⁻¹ ≤ 1 - v := by
    rw [← hW3, ← Real.rpow_neg hWr0.le]; exact hv3
  have hv1 : v < 1 := by
    have : 0 < ((W : ℝ) ^ 3)⁻¹ := by positivity
    linarith
  have hu0 : 0 ≤ x.u := by linarith
  have hL1 : 1 ≤ x.L := by omega
  -- the scale `ℓ` and `ζ`
  have hℓ1 : 1 ≤ ellProp x.g x.L x.u := by
    unfold ellProp
    refine le_min (by exact_mod_cast hL1) ?_
    have : 0 ≤ x.g / Real.sqrt (gammaG x.g * (1 - x.u)) :=
      div_nonneg hg0 (Real.sqrt_nonneg _)
    linarith
  have hℓ0 : 0 < ellProp x.g x.L x.u := by linarith
  have hζ0 : 0 ≤ zetaProp x.g W x.L x.u := by
    unfold zetaProp
    refine inv_nonneg.2 ?_
    have : 0 ≤ ellProp x.g x.L x.u := hℓ0.le
    have : 0 ≤ 1 - x.u := by linarith
    positivity
  -- `|m| ≤ C`
  have hmC : ‖mRoot x.g x.L x.E‖ ≤ R.C := by
    have hw : 0 < ((x.E : ℂ) + (gammaG x.g : ℝ) * mRoot x.g x.L x.E).im := by
      simpa using mul_pos hγ hroot.1
    have hd := dysonMat_diag (hopB x.g) (gammaG x.g) x.L hL1 (x.E : ℂ) (mRoot x.g x.L x.E) hw
      ⟨0, by omega⟩
    rw [← hroot.2] at hd
    rw [← hd]
    exact hMC _ _
  obtain ⟨hB, hmB, hpr, hprk⟩ := coneCrude_prim_le n (Cζ := Cζ) hC1 hW1 x hζ0 hζ hmC
    (fun j hj2 hjn b τ => Hp W hWp d x hd hx j hj2 hjn b τ)
  -- the kernels
  have hP0 : ∀ y z, 0 ≤ pairP (gammaG x.g)
      (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E)) y z := fun y z => by
    simp only [pairP, Matrix.of_apply]; positivity
  have hProw : ∀ y, ∑ z, pairP (gammaG x.g)
      (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E)) y z = 1 := fun y =>
    pairP_row_sum (hopB x.g) (gammaG x.g) hγ x.L hL1 x.E _ hroot y
  have hKle : ∀ y z, mixedKer (pairP (gammaG x.g)
      (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) x.u y z ≤
      R.C / ((1 - x.u) * ellProp x.g x.L x.u) + (ellProp x.g x.L x.u)⁻¹ := by
    intro y z
    have h := (Hk W hWk d x hd hx y z).2
    have he : Real.exp (-(R.c * cycDist y z / ellProp x.g x.L x.u)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_nonpos]
      exact div_nonneg (mul_nonneg R.c_pos.le (Nat.cast_nonneg _)) hℓ0.le
    have hw : (W : ℝ) ^ (-1 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hWr1 (by norm_num)
    have h1u : 0 < 1 - x.u := by linarith
    have h1 : R.C / ((1 - x.u) * ellProp x.g x.L x.u) *
        Real.exp (-(R.c * cycDist y z / ellProp x.g x.L x.u)) ≤
        R.C / ((1 - x.u) * ellProp x.g x.L x.u) :=
      mul_le_of_le_one_right (by positivity) he
    have h2 : (ellProp x.g x.L x.u)⁻¹ * (W : ℝ) ^ (-1 : ℝ) ≤ (ellProp x.g x.L x.u)⁻¹ :=
      mul_le_of_le_one_right (by positivity) hw
    linarith
  obtain ⟨hθ0, hT, hK0, hKr, hU0, hUr⟩ := coneCrude_kernelFacts hL1 _ hP0 hProw hu0 huv hv1
    hℓ0 hKle n
  -- the budget and the scales
  obtain ⟨hΛ, hρΛ, hTΛ, hwΛ, hcΛ, hBΛ, hR₂Λ, hgΛ⟩ := by
    have hbud := Hb W hWb d x hd hx
    have hγL : gammaG x.g * x.L ≤ (W : ℝ) ^ R.C := by
      have : 0 ≤ (x.L : ℝ) / ellProp x.g x.L x.u := div_nonneg (Nat.cast_nonneg _) hℓ0.le
      linarith
    have hLℓ : (x.L : ℝ) / ellProp x.g x.L x.u ≤ (W : ℝ) ^ R.C := by
      have : 0 ≤ gammaG x.g * x.L := by positivity
      linarith
    exact coneCrude_scales n (Cζ := Cζ) hC1 hW1 hu12 huv hv3' hℓ0 hγL hLℓ
  exact {
    hW := hW1, hL := hL3, root := hroot, hu := ⟨by linarith, by linarith⟩,
    hv := ⟨by linarith, hv1⟩, hℓ := hℓ0, hB := hB, hmB := hmB, hpr := hpr, hprk := hprk,
    hθ0 := hθ0, hT := hT, hK0 := hK0, hKr := hKr, hU0 := hU0, hUr := hUr,
    hR₂ := fun s s' y => coneCrude_pairU_rows (gammaG x.g) hγ _ hP0 hProw hu0 huv hv1 hC0
      hMrow (hQinv v (le_trans hu0 huv) hv1.le) s s' y,
    hΛ := hΛ, hρΛ := hρΛ, hTΛ := hTΛ, hwΛ := hwΛ, hcΛ := hcΛ, hBΛ := hBΛ, hR₂Λ := hR₂Λ,
    hgΛ := hgΛ }

/-- The crude block moments (5.33) [fo:eq:coarse-time-input] of `G` at the reached points. -/
private lemma coneCrude_crude (R : PropRegime) (I : PropInputs R.base R.J) :
    ∃ C₀ : ℝ, ∀ N : ℕ, 1 ≤ N → ∃ Cc : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ (d : ℕ) (x : FlowPt),
      d ≤ R.J → CmpReach R.base W d x → ∀ y z : Fin x.L,
        Integrable (fun ω => ‖blockOf (flowG W x ω) y z‖ ^ N) (μ W x.L) ∧
          ∫ ω, ‖blockOf (flowG W x ω) y z‖ ^ N ∂(μ W x.L) ≤ Cc * (W : ℝ) ^ (C₀ * N) := by
  obtain ⟨C₀, H⟩ := I.crude
  refine ⟨C₀, fun N hN => ?_⟩
  obtain ⟨Cc, W₀, HW⟩ := H N hN
  refine ⟨Cc, W₀, fun W hW d x hd hx y z => ?_⟩
  have h := HW W hW (x, etaChar x.g (mRoot x.g x.L x.E) x.u) ⟨d, hd, hx, Or.inl rfl⟩ y z
  simp only [coneCrude_segG_eq] at h
  exact h

/-- The constant `2^{Np}(1 + ((2k+1)²)^{Np}|C_c|)` of the bound on `coneCrudeBk`. -/
private def coneCrudeD (k p : ℕ) (Cc : ℝ) : ℝ :=
  2 ^ ((2 * k + 2) * p) * (1 + ((((2 * k + 1) * (2 * k + 1) : ℕ) : ℝ)) ^ ((2 * k + 2) * p) * |Cc|)

private lemma coneCrudeD_nonneg (k p : ℕ) (Cc : ℝ) : 0 ≤ coneCrudeD k p Cc := by
  unfold coneCrudeD; positivity

/-- `coneCrudeBk ≤ D W^{max(C₀,0)(2k+2)p}`. -/
private lemma coneCrudeBk_le (k p : ℕ) (Cc C₀ : ℝ) {W : ℕ} (hW : 1 ≤ W) :
    coneCrudeBk k p (Cc * (W : ℝ) ^ (C₀ * (((2 * k + 2) * p : ℕ) : ℝ))) ≤
      coneCrudeD k p Cc * (W : ℝ) ^ (max C₀ 0 * ((2 * k + 2 : ℕ) : ℝ) * p) := by
  have hWr1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  set N : ℕ := (2 * k + 2) * p with hN
  set Mp : ℝ := ((((2 * k + 1) * (2 * k + 1) : ℕ) : ℝ)) ^ N with hMp
  have hMp0 : 0 ≤ Mp := by positivity
  set X : ℝ := (W : ℝ) ^ (max C₀ 0 * ((2 * k + 2 : ℕ) : ℝ) * p) with hX
  have hX1 : 1 ≤ X := Real.one_le_rpow hWr1 (by positivity)
  have hexp : C₀ * ((N : ℕ) : ℝ) ≤ max C₀ 0 * ((2 * k + 2 : ℕ) : ℝ) * p := by
    rw [hN, Nat.cast_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hbc : Cc * (W : ℝ) ^ (C₀ * ((N : ℕ) : ℝ)) ≤ |Cc| * X := by
    calc Cc * (W : ℝ) ^ (C₀ * ((N : ℕ) : ℝ)) ≤ |Cc| * (W : ℝ) ^ (C₀ * ((N : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |Cc| * X := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hWr1 hexp) (abs_nonneg _)
  unfold coneCrudeBk coneCrudeD
  rw [← hN, ← hMp]
  have h2 : (2 : ℝ) ^ (N - 1) ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have h1 : 1 + Mp * (Cc * (W : ℝ) ^ (C₀ * ((N : ℕ) : ℝ))) ≤ (1 + Mp * |Cc|) * X := by
    have := mul_le_mul_of_nonneg_left hbc hMp0
    have h3 : Mp * (|Cc| * X) = Mp * |Cc| * X := by ring
    nlinarith [mul_nonneg hMp0 (abs_nonneg Cc)]
  have hpos : 0 ≤ (1 + Mp * |Cc|) * X := by positivity
  calc (2 : ℝ) ^ (N - 1) * (1 + Mp * (Cc * (W : ℝ) ^ (C₀ * ((N : ℕ) : ℝ))))
      ≤ 2 ^ N * ((1 + Mp * |Cc|) * X) := by
        rcases le_or_gt 0 (1 + Mp * (Cc * (W : ℝ) ^ (C₀ * ((N : ℕ) : ℝ)))) with h0 | h0
        · exact mul_le_mul h2 h1 h0 (by positivity)
        · have : (2 : ℝ) ^ (N - 1) * (1 + Mp * (Cc * (W : ℝ) ^ (C₀ * ((N : ℕ) : ℝ)))) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by positivity) h0.le
          exact this.trans (by positivity)
    _ = 2 ^ N * (1 + Mp * |Cc|) * X := by ring

/-- A crude bound that dominates a moment is nonnegative. -/
private lemma coneCrude_Bc_nonneg {W : ℕ} {x : FlowPt} (hL : 0 < x.L) {N : ℕ} {Bc : ℝ}
    (hcr : ∀ y z : Fin x.L, Integrable (fun ω => ‖blockOf (flowG W x ω) y z‖ ^ N) (μ W x.L) ∧
      ∫ ω, ‖blockOf (flowG W x ω) y z‖ ^ N ∂(μ W x.L) ≤ Bc) : 0 ≤ Bc :=
  (integral_nonneg fun _ => pow_nonneg (norm_nonneg _) _).trans (hcr ⟨0, hL⟩ ⟨0, hL⟩).2

/-- The polynomial bookkeeping of the generator of the propagated projected field. -/
private lemma coneCrude_arith_proj {ρ T w c L B Λ Bk c₂ c₃ c₄ c₅ : ℝ} {n p : ℕ} (hρ0 : 0 ≤ ρ)
    (hT0 : 0 ≤ T) (hw0 : 0 ≤ w) (hc0 : 0 ≤ c) (hL0 : 0 ≤ L) (hB0 : 0 ≤ B) (hBk : 0 ≤ Bk)
    (hρ : ρ ≤ Λ) (hT : T ≤ c₄ * Λ) (hw : w ≤ c₂ * Λ) (hc : c * L ≤ c₃ * Λ) (hB : B ≤ c₅ * Λ) :
    (ρ ^ (n + 1)) ^ p * (2 ^ p * (T ^ p * (w ^ p * Bk) + c ^ p * (L ^ p * (B ^ p * Bk)))) ≤
      2 ^ p * ((c₄ * c₂) ^ p + (c₃ * c₅) ^ p) * (Λ ^ (n + 3)) ^ p * Bk := by
  have e : c ^ p * (L ^ p * (B ^ p * Bk)) = (c * L) ^ p * (B ^ p * Bk) := by
    rw [mul_pow]; ring
  rw [e]
  have hΛ0 : 0 ≤ Λ := hρ0.trans hρ
  have h1 := pow_le_pow_left₀ (pow_nonneg hρ0 _) (pow_le_pow_left₀ hρ0 hρ (n + 1)) p
  have h2 := pow_le_pow_left₀ hT0 hT p
  have h3 := pow_le_pow_left₀ hw0 hw p
  have h4 := pow_le_pow_left₀ (mul_nonneg hc0 hL0) hc p
  have h5 := pow_le_pow_left₀ hB0 hB p
  have hc₄ : 0 ≤ c₄ * Λ := hT0.trans hT
  have hc₂ : 0 ≤ c₂ * Λ := hw0.trans hw
  have hc₃ : 0 ≤ c₃ * Λ := (mul_nonneg hc0 hL0).trans hc
  have hc₅ : 0 ≤ c₅ * Λ := hB0.trans hB
  calc (ρ ^ (n + 1)) ^ p * (2 ^ p * (T ^ p * (w ^ p * Bk) + (c * L) ^ p * (B ^ p * Bk)))
      ≤ (Λ ^ (n + 1)) ^ p * (2 ^ p * ((c₄ * Λ) ^ p * ((c₂ * Λ) ^ p * Bk) +
          (c₃ * Λ) ^ p * ((c₅ * Λ) ^ p * Bk))) := by
        refine mul_le_mul h1 (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity))
          (by positivity) (by positivity)
        · exact mul_le_mul h2 (mul_le_mul_of_nonneg_right h3 hBk) (by positivity) (by positivity)
        · exact mul_le_mul h4 (mul_le_mul_of_nonneg_right h5 hBk) (by positivity) (by positivity)
    _ = 2 ^ p * ((c₄ * c₂) ^ p + (c₃ * c₅) ^ p) * (Λ ^ (n + 3)) ^ p * Bk := by ring

/-- The polynomial bookkeeping of a weight `A^p` times a leaf bound `w^p B_k`. -/
private lemma coneCrude_arith_two {A w Λ Bk a c : ℝ} {i p : ℕ} (hA0 : 0 ≤ A) (hw0 : 0 ≤ w)
    (hBk : 0 ≤ Bk) (hA : A ≤ a * Λ ^ i) (hw : w ≤ c * Λ) :
    A ^ p * (w ^ p * Bk) ≤ (a * c) ^ p * (Λ ^ (i + 1)) ^ p * Bk := by
  have h1 := pow_le_pow_left₀ hA0 hA p
  have h2 := pow_le_pow_left₀ hw0 hw p
  calc A ^ p * (w ^ p * Bk) ≤ (a * Λ ^ i) ^ p * ((c * Λ) ^ p * Bk) :=
        mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 hBk) (by positivity)
          (pow_nonneg (hA0.trans hA) _)
    _ = (a * c) ^ p * (Λ ^ (i + 1)) ^ p * Bk := by ring

/-- The polynomial bookkeeping of a bracket: `A^p A^p w^p B_k`. -/
private lemma coneCrude_arith_three {A w Λ Bk a c : ℝ} {i p : ℕ} (hA0 : 0 ≤ A) (hw0 : 0 ≤ w)
    (hBk : 0 ≤ Bk) (hA : A ≤ a * Λ ^ i) (hw : w ≤ c * Λ) :
    A ^ p * (A ^ p * (w ^ p * Bk)) ≤ (a * a * c) ^ p * (Λ ^ (2 * i + 1)) ^ p * Bk := by
  have h1 := pow_le_pow_left₀ hA0 hA p
  have h2 := pow_le_pow_left₀ hw0 hw p
  have hA1 : 0 ≤ (a * Λ ^ i) ^ p := pow_nonneg (hA0.trans hA) _
  calc A ^ p * (A ^ p * (w ^ p * Bk)) ≤ (a * Λ ^ i) ^ p * ((a * Λ ^ i) ^ p * ((c * Λ) ^ p * Bk)) :=
        mul_le_mul h1 (mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 hBk) (by positivity) hA1)
          (by positivity) hA1
    _ = (a * a * c) ^ p * (Λ ^ (2 * i + 1)) ^ p * Bk := by ring

/-- The final bound: `K (Λ^j)^p B_k ≤ K D W^{(EJ + e)p}` for `Λ = W^E ≥ 1`, `j ≤ J`. -/
private lemma coneCrude_conclude {W : ℕ} (hW : 1 ≤ W) {E e K D Bk : ℝ} (hE : 0 ≤ E)
    {j J p : ℕ} (hj : j ≤ J) (hK : 0 ≤ K) (hBk0 : 0 ≤ Bk)
    (hBk : Bk ≤ D * (W : ℝ) ^ (e * p)) :
    K * (((W : ℝ) ^ E) ^ j) ^ p * Bk ≤ K * D * (W : ℝ) ^ ((E * J + e) * p) := by
  have hWr1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hWr0 : (0 : ℝ) < W := by linarith
  have hΛ1 : 1 ≤ (W : ℝ) ^ E := Real.one_le_rpow hWr1 hE
  have h1 : (((W : ℝ) ^ E) ^ j) ^ p ≤ (W : ℝ) ^ (E * J * p) := by
    rw [Real.rpow_mul_natCast hWr0.le, Real.rpow_mul_natCast hWr0.le]
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hΛ1 hj) p
  have hD : 0 ≤ D * (W : ℝ) ^ (e * p) := hBk0.trans hBk
  calc K * (((W : ℝ) ^ E) ^ j) ^ p * Bk ≤ K * (W : ℝ) ^ (E * J * p) * (D * (W : ℝ) ^ (e * p)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hK) hBk hBk0 (by positivity)
    _ = K * D * ((W : ℝ) ^ (E * J * p) * (W : ℝ) ^ (e * p)) := by ring
    _ = K * D * (W : ℝ) ^ ((E * J + e) * p) := by
        rw [← Real.rpow_add hWr0]; congr 2; ring

end Regime

end CrudeHelpers

/-- Crude moments of the generators: at every point `x` reached with depth at most `J`, with
`1/2 ≤ x.u ≤ v`, `1 - v ≥ W^{-3}` and `ζ_{x.u} ≤ W^{C_ζ}`, the generator at `H_{x.u}` of the
propagated projected field (C.35) [fo:eq:projected-error-equation] (cyclically alternating words
of length `n + 1`) and of the propagated field (all words) has `E|𝒢|^p ≤ C_p W^{C_K p}`, with
`C_K` independent of `p`, of the point and of `v`. The sums over labels enter only through the
budget `γ_g L + L/ℓ ≤ W^C` and the rows of the propagators. -/
theorem coneCrude_gen (R : PropRegime) (I : PropInputs R.base R.J) (n : ℕ) (hn : 1 ≤ n)
    (Cζ : ℝ) :
    ∃ CK : ℝ, ∀ p : ℕ, 1 ≤ p → ∃ Cp : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ (d : ℕ) (x : FlowPt) (v : ℝ), d ≤ R.J → CmpReach R.base W d x → 1 / 2 ≤ x.u → x.u ≤ v →
      (W : ℝ) ^ (-3 : ℝ) ≤ 1 - v → zetaProp x.g W x.L x.u ≤ (W : ℝ) ^ Cζ →
      ∀ (σ : Fin (n + 1) → Bool) (a : Fin (n + 1) → Fin x.L),
        ((∀ j, σ (finRotate (n + 1) j) = !σ j) →
          Integrable (fun ω => ‖blockGen W x.L (gammaG x.g) (fun r N => ∑ b,
              projCoef (pairP (gammaG x.g)
                (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) v r a b *
              (resLoop x.g x.E (mRoot x.g x.L x.E) b σ r N -
                primLoop x.g W x.L x.E (mRoot x.g x.L x.E) r b σ)) x.u
              (flowH x.g W x.L x.u ω)‖ ^ p) (μ W x.L) ∧
          ∫ ω, ‖blockGen W x.L (gammaG x.g) (fun r N => ∑ b,
              projCoef (pairP (gammaG x.g)
                (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) v r a b *
              (resLoop x.g x.E (mRoot x.g x.L x.E) b σ r N -
                primLoop x.g W x.L x.E (mRoot x.g x.L x.E) r b σ)) x.u
              (flowH x.g W x.L x.u ω)‖ ^ p ∂(μ W x.L) ≤ Cp * (W : ℝ) ^ (CK * p)) ∧
        Integrable (fun ω => ‖blockGen W x.L (gammaG x.g) (fun r N => ∑ b,
            (∏ j, pairU (gammaG x.g)
              (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E)) r v (σ j)
              (σ (finRotate (n + 1) j)) (a j) (b j)) *
            (resLoop x.g x.E (mRoot x.g x.L x.E) b σ r N -
              primLoop x.g W x.L x.E (mRoot x.g x.L x.E) r b σ)) x.u
            (flowH x.g W x.L x.u ω)‖ ^ p) (μ W x.L) ∧
        ∫ ω, ‖blockGen W x.L (gammaG x.g) (fun r N => ∑ b,
            (∏ j, pairU (gammaG x.g)
              (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E)) r v (σ j)
              (σ (finRotate (n + 1) j)) (a j) (b j)) *
            (resLoop x.g x.E (mRoot x.g x.L x.E) b σ r N -
              primLoop x.g W x.L x.E (mRoot x.g x.L x.E) r b σ)) x.u
            (flowH x.g W x.L x.u ω)‖ ^ p ∂(μ W x.L) ≤ Cp * (W : ℝ) ^ (CK * p) := by
  obtain ⟨W₁, H₁⟩ := coneCrude_at R n Cζ
  obtain ⟨C₀, Hc⟩ := coneCrude_crude R I
  refine ⟨coneCrudeE R.C Cζ n * ((2 * n + 5 : ℕ) : ℝ) +
    max C₀ 0 * ((2 * (n + 1) + 2 : ℕ) : ℝ), fun p hp => ?_⟩
  obtain ⟨Cc, W₂, H₂⟩ := Hc ((2 * (n + 1) + 2) * p) (by nlinarith)
  have hC1 : 1 ≤ R.C := R.one_le_C
  have hC0 : 0 ≤ R.C := le_trans zero_le_one hC1
  set Ki : ℝ := 2 ^ p * (((1 + (R.C + 1) ^ n) * (10 * ((n + 1 : ℕ) : ℝ) ^ 2 * R.C ^ 2)) ^ p +
    ((2 * (R.C + 1) ^ n) * (2 * R.C)) ^ p) with hKi
  set Kii : ℝ := ((1 + (1 + R.C) * R.C) ^ (n + 1) *
    (10 * ((n + 1 : ℕ) : ℝ) ^ 2 * R.C ^ 2)) ^ p with hKii
  have hKi0 : 0 ≤ Ki := by positivity
  have hKii0 : 0 ≤ Kii := by positivity
  refine ⟨(Ki + Kii) * coneCrudeD (n + 1) p Cc, max W₁ W₂,
    fun W hW d x v hd hx hu12 huv hv3 hζ σ a => ?_⟩
  have F := H₁ W (le_trans (le_max_left _ _) hW) d x v hd hx hu12 huv hv3 hζ
  have hcr := H₂ W (le_trans (le_max_right _ _) hW) d x hd hx
  have hBc := coneCrude_Bc_nonneg (by have := F.hL; omega) hcr
  have hBk0 := coneCrudeBk_nonneg (n + 1) p hBc
  have hBk := coneCrudeBk_le (n + 1) p Cc C₀ F.hW
  have hD0 := coneCrudeD_nonneg (n + 1) p Cc
  have hE0 : 0 ≤ coneCrudeE R.C Cζ n := by unfold coneCrudeE; positivity
  have hLam : coneCrudeLam R.C Cζ n W = (W : ℝ) ^ coneCrudeE R.C Cζ n := rfl
  have hγ := coneCrude_gammaG_pos x.g
  have h1u : 0 < 1 - x.u := by linarith [F.hu.2]
  have h1v : 0 < 1 - v := by linarith [F.hv.2]
  have hρ0 : 0 ≤ (1 - x.u) / (1 - v) := div_nonneg h1u.le h1v.le
  have hB0 : 0 ≤ coneCrudeB R.C Cζ n W := le_trans zero_le_one F.hB
  have hℓ := F.hℓ
  have hfin : ∀ {K B : ℝ} {j : ℕ}, 0 ≤ K → K ≤ Ki + Kii → j ≤ 2 * n + 5 →
      B ≤ K * (coneCrudeLam R.C Cζ n W ^ j) ^ p *
        coneCrudeBk (n + 1) p (Cc * (W : ℝ) ^ (C₀ * (((2 * (n + 1) + 2) * p : ℕ) : ℝ))) →
      B ≤ (Ki + Kii) * coneCrudeD (n + 1) p Cc * (W : ℝ) ^ ((coneCrudeE R.C Cζ n *
        ((2 * n + 5 : ℕ) : ℝ) + max C₀ 0 * ((2 * (n + 1) + 2 : ℕ) : ℝ)) * p) := by
    intro K B j hK hKK hj hB
    refine hB.trans ?_
    rw [hLam]
    refine (coneCrude_conclude F.hW hE0 hj hK hBk0 hBk).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKK hD0) (by positivity)
  refine ⟨fun hσ => ?_, ?_⟩
  · -- cyclically alternating words
    have M1 := coneCrude_genProj_point x W F.hW F.hL F.root F.hu F.hv hn F.hB F.hmB F.hpr F.hprk
      hp hBc hcr F.hθ0 F.hT F.hK0 F.hKr F.hU0 F.hUr σ hσ a
    exact ⟨M1.2.1, hfin hKi0 (le_add_of_nonneg_right hKii0) (j := n + 3) (by omega)
      (M1.2.2.trans (coneCrude_arith_proj hρ0 (by positivity) (by positivity) (by positivity)
        (by positivity) (by positivity) hBk0 F.hρΛ F.hTΛ F.hwΛ F.hcΛ F.hBΛ))⟩
  · -- all words
    have M2 := coneCrude_genStable_point x W F.hW F.hL F.root F.hu F.hv hn F.hB F.hmB F.hpr hp
      hBc hcr σ (fun j y => F.hR₂ _ _ y) a
    have hR : ((1 - x.u) / (1 - v) + (1 + R.C) * R.C) ^ (n + 1) ≤
        (1 + (1 + R.C) * R.C) ^ (n + 1) * coneCrudeLam R.C Cζ n W ^ (n + 1) := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) F.hR₂Λ _
    exact ⟨M2.2.1, hfin hKii0 (le_add_of_nonneg_left hKi0) (j := n + 1 + 1) (by omega)
      (M2.2.2.trans (coneCrude_arith_two (by positivity) (by positivity) hBk0 hR F.hwΛ))⟩


/-- Crude moments of the brackets (5.9) [gc:eq:bracket] of the propagated projected field and of
the propagated field, under the hypotheses of `coneCrude_gen`: `E|Γ|^p ≤ C_p W^{C_K p}`. -/
theorem coneCrude_gamma (R : PropRegime) (I : PropInputs R.base R.J) (n : ℕ) (hn : 1 ≤ n)
    (Cζ : ℝ) :
    ∃ CK : ℝ, ∀ p : ℕ, 1 ≤ p → ∃ Cp : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ (d : ℕ) (x : FlowPt) (v : ℝ), d ≤ R.J → CmpReach R.base W d x → 1 / 2 ≤ x.u → x.u ≤ v →
      (W : ℝ) ^ (-3 : ℝ) ≤ 1 - v → zetaProp x.g W x.L x.u ≤ (W : ℝ) ^ Cζ →
      ∀ (σ : Fin (n + 1) → Bool) (a : Fin (n + 1) → Fin x.L),
        (Integrable (fun ω => ‖blockGamma W x.L (gammaG x.g)
            (fun N => ∑ b, projCoef (pairP (gammaG x.g)
                (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) v x.u a b *
              (resLoop x.g x.E (mRoot x.g x.L x.E) b σ x.u N -
                primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b σ))
            (fun N => ∑ b, projCoef (pairP (gammaG x.g)
                (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) v x.u a b *
              (resLoop x.g x.E (mRoot x.g x.L x.E) b σ x.u N -
                primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b σ))
            (flowH x.g W x.L x.u ω)‖ ^ p) (μ W x.L) ∧
        ∫ ω, ‖blockGamma W x.L (gammaG x.g)
            (fun N => ∑ b, projCoef (pairP (gammaG x.g)
                (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) v x.u a b *
              (resLoop x.g x.E (mRoot x.g x.L x.E) b σ x.u N -
                primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b σ))
            (fun N => ∑ b, projCoef (pairP (gammaG x.g)
                (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) v x.u a b *
              (resLoop x.g x.E (mRoot x.g x.L x.E) b σ x.u N -
                primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b σ))
            (flowH x.g W x.L x.u ω)‖ ^ p ∂(μ W x.L) ≤ Cp * (W : ℝ) ^ (CK * p)) ∧
        Integrable (fun ω => ‖blockGamma W x.L (gammaG x.g)
            (fun N => ∑ b, (∏ j, pairU (gammaG x.g)
                (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E)) x.u v (σ j)
                (σ (finRotate (n + 1) j)) (a j) (b j)) *
              (resLoop x.g x.E (mRoot x.g x.L x.E) b σ x.u N -
                primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b σ))
            (fun N => ∑ b, (∏ j, pairU (gammaG x.g)
                (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E)) x.u v (σ j)
                (σ (finRotate (n + 1) j)) (a j) (b j)) *
              (resLoop x.g x.E (mRoot x.g x.L x.E) b σ x.u N -
                primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b σ))
            (flowH x.g W x.L x.u ω)‖ ^ p) (μ W x.L) ∧
        ∫ ω, ‖blockGamma W x.L (gammaG x.g)
            (fun N => ∑ b, (∏ j, pairU (gammaG x.g)
                (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E)) x.u v (σ j)
                (σ (finRotate (n + 1) j)) (a j) (b j)) *
              (resLoop x.g x.E (mRoot x.g x.L x.E) b σ x.u N -
                primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b σ))
            (fun N => ∑ b, (∏ j, pairU (gammaG x.g)
                (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E)) x.u v (σ j)
                (σ (finRotate (n + 1) j)) (a j) (b j)) *
              (resLoop x.g x.E (mRoot x.g x.L x.E) b σ x.u N -
                primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b σ))
            (flowH x.g W x.L x.u ω)‖ ^ p ∂(μ W x.L) ≤ Cp * (W : ℝ) ^ (CK * p) := by
  obtain ⟨W₁, H₁⟩ := coneCrude_at R n Cζ
  obtain ⟨C₀, Hc⟩ := coneCrude_crude R I
  refine ⟨coneCrudeE R.C Cζ n * ((2 * n + 5 : ℕ) : ℝ) +
    max C₀ 0 * ((2 * (n + 1) + 2 : ℕ) : ℝ), fun p hp => ?_⟩
  obtain ⟨Cc, W₂, H₂⟩ := Hc ((2 * (n + 1) + 2) * p) (by nlinarith)
  have hC1 : 1 ≤ R.C := R.one_le_C
  have hC0 : 0 ≤ R.C := le_trans zero_le_one hC1
  set Ki : ℝ := ((1 + (R.C + 1) ^ n) * (1 + (R.C + 1) ^ n) * ((n + 1 : ℕ) : ℝ) ^ 2) ^ p
    with hKi
  set Kii : ℝ := ((1 + (1 + R.C) * R.C) ^ (n + 1) * (1 + (1 + R.C) * R.C) ^ (n + 1) *
    ((n + 1 : ℕ) : ℝ) ^ 2) ^ p with hKii
  have hKi0 : 0 ≤ Ki := by positivity
  have hKii0 : 0 ≤ Kii := by positivity
  set Ks : ℝ := Ki + Kii with hKs
  refine ⟨Ks * coneCrudeD (n + 1) p Cc, max W₁ W₂,
    fun W hW d x v hd hx hu12 huv hv3 hζ σ a => ?_⟩
  have F := H₁ W (le_trans (le_max_left _ _) hW) d x v hd hx hu12 huv hv3 hζ
  have hcr := H₂ W (le_trans (le_max_right _ _) hW) d x hd hx
  have hBc := coneCrude_Bc_nonneg (by have := F.hL; omega) hcr
  have hBk0 := coneCrudeBk_nonneg (n + 1) p hBc
  have hBk := coneCrudeBk_le (n + 1) p Cc C₀ F.hW
  have hD0 := coneCrudeD_nonneg (n + 1) p Cc
  have hE0 : 0 ≤ coneCrudeE R.C Cζ n := by unfold coneCrudeE; positivity
  have hLam : coneCrudeLam R.C Cζ n W = (W : ℝ) ^ coneCrudeE R.C Cζ n := rfl
  have hγ := coneCrude_gammaG_pos x.g
  have h1u : 0 < 1 - x.u := by linarith [F.hu.2]
  have h1v : 0 < 1 - v := by linarith [F.hv.2]
  have hρ0 : 0 ≤ (1 - x.u) / (1 - v) := div_nonneg h1u.le h1v.le
  have hB0 : 0 ≤ coneCrudeB R.C Cζ n W := le_trans zero_le_one F.hB
  have hℓ := F.hℓ
  have hΛ0 : 0 ≤ coneCrudeLam R.C Cζ n W := le_trans zero_le_one F.hΛ
  have hfin : ∀ {K B : ℝ} {j : ℕ}, 0 ≤ K → K ≤ Ks → j ≤ 2 * n + 5 →
      B ≤ K * (coneCrudeLam R.C Cζ n W ^ j) ^ p *
        coneCrudeBk (n + 1) p (Cc * (W : ℝ) ^ (C₀ * (((2 * (n + 1) + 2) * p : ℕ) : ℝ))) →
      B ≤ Ks * coneCrudeD (n + 1) p Cc * (W : ℝ) ^ ((coneCrudeE R.C Cζ n *
        ((2 * n + 5 : ℕ) : ℝ) + max C₀ 0 * ((2 * (n + 1) + 2 : ℕ) : ℝ)) * p) := by
    intro K B j hK hKK hj hB
    refine hB.trans ?_
    rw [hLam]
    refine (coneCrude_conclude F.hW hE0 hj hK hBk0 hBk).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKK hD0) (by positivity)
  -- the total weights of the two coefficient families
  have hA₁ : ∑ b, ‖projCoef (pairP (gammaG x.g)
      (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) v x.u a b‖ ≤
      ((1 - x.u) / (1 - v)) ^ (n + 1) *
        (1 + ((R.C + 1) / ellProp x.g x.L x.u) ^ n * (x.L : ℝ) ^ n) :=
    (coneCrude_projCoef_weight _ v x.u a F.hU0 F.hθ0 F.hT).trans
      (mul_le_mul_of_nonneg_right (coneCrude_prod_rows_real _ a F.hU0 F.hUr) (by positivity))
  have hA₁Λ : ((1 - x.u) / (1 - v)) ^ (n + 1) *
        (1 + ((R.C + 1) / ellProp x.g x.L x.u) ^ n * (x.L : ℝ) ^ n) ≤
      (1 + (R.C + 1) ^ n) * coneCrudeLam R.C Cζ n W ^ (n + 1 + 1) := by
    calc ((1 - x.u) / (1 - v)) ^ (n + 1) *
          (1 + ((R.C + 1) / ellProp x.g x.L x.u) ^ n * (x.L : ℝ) ^ n)
        ≤ coneCrudeLam R.C Cζ n W ^ (n + 1) *
          ((1 + (R.C + 1) ^ n) * coneCrudeLam R.C Cζ n W) :=
          mul_le_mul (pow_le_pow_left₀ hρ0 F.hρΛ _) F.hTΛ (by positivity) (by positivity)
      _ = (1 + (R.C + 1) ^ n) * coneCrudeLam R.C Cζ n W ^ (n + 1 + 1) := by ring
  have hA₂ : ∑ b : Fin (n + 1) → Fin x.L, ‖∏ j, pairU (gammaG x.g)
      (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E)) x.u v (σ j)
      (σ (finRotate (n + 1) j)) (a j) (b j)‖ ≤
      ((1 - x.u) / (1 - v) + (1 + R.C) * R.C) ^ (n + 1) :=
    coneCrude_prod_rows (fun j y z => pairU (gammaG x.g)
      (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E)) x.u v (σ j)
      (σ (finRotate (n + 1) j)) y z) a fun j => F.hR₂ _ _ (a j)
  have hA₂Λ : ((1 - x.u) / (1 - v) + (1 + R.C) * R.C) ^ (n + 1) ≤
      (1 + (1 + R.C) * R.C) ^ (n + 1) * coneCrudeLam R.C Cζ n W ^ (n + 1) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) F.hR₂Λ _
  have G1 := coneCrude_gamma_point x W F.hW F.root.1 F.hu.2 (k := n + 1) hp hBc hcr σ _ hA₁
  have G2 := coneCrude_gamma_point x W F.hW F.root.1 F.hu.2 (k := n + 1) hp hBc hcr σ _ hA₂
  refine ⟨⟨G1.2.1, hfin hKi0 (le_add_of_nonneg_right hKii0) (j := 2 * (n + 1 + 1) + 1)
    (by omega) (G1.2.2.trans (coneCrude_arith_three (by positivity) (by positivity) hBk0 hA₁Λ
      F.hgΛ))⟩, G2.2.1, hfin hKii0 (le_add_of_nonneg_left hKi0) (j := 2 * (n + 1) + 1)
    (by omega) (G2.2.2.trans (coneCrude_arith_three (by positivity) (by positivity) hBk0 hA₂Λ
      F.hgΛ))⟩


/-- Crude moments of the fields, under the hypotheses of `coneCrude_gen`: the propagated
projected field `Σ_b coef_{x.u,v}(a, b)D(b)`, the propagated field `Σ_b Π_j U(a_j, b_j)D(b)`,
the row term `h(a₀)Π_j θ(a₀ - a_j)` of the projection before (C.33) [fo:eq:ward-projection]
(the restored Ward row), and the loop error `D_{n+1}(a)` itself, at the point `x`, all with
`E|·|^p ≤ C_p W^{C_K p}`. -/
theorem coneCrude_field (R : PropRegime) (I : PropInputs R.base R.J) (n : ℕ) (Cζ : ℝ) :
    ∃ CK : ℝ, ∀ p : ℕ, 1 ≤ p → ∃ Cp : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ (d : ℕ) (x : FlowPt) (v : ℝ), d ≤ R.J → CmpReach R.base W d x → 1 / 2 ≤ x.u → x.u ≤ v →
      (W : ℝ) ^ (-3 : ℝ) ≤ 1 - v → zetaProp x.g W x.L x.u ≤ (W : ℝ) ^ Cζ →
      ∀ (σ : Fin (n + 1) → Bool) (a : Fin (n + 1) → Fin x.L),
        (Integrable (fun ω => ‖∑ b, projCoef (pairP (gammaG x.g)
            (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) v x.u a b *
              flowErr W x b σ ω‖ ^ p) (μ W x.L) ∧
          ∫ ω, ‖∑ b, projCoef (pairP (gammaG x.g)
            (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) v x.u a b *
              flowErr W x b σ ω‖ ^ p ∂(μ W x.L) ≤ Cp * (W : ℝ) ^ (CK * p)) ∧
        (Integrable (fun ω => ‖∑ b, (∏ j, pairU (gammaG x.g)
            (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E)) x.u v (σ j)
            (σ (finRotate (n + 1) j)) (a j) (b j)) * flowErr W x b σ ω‖ ^ p) (μ W x.L) ∧
          ∫ ω, ‖∑ b, (∏ j, pairU (gammaG x.g)
            (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E)) x.u v (σ j)
            (σ (finRotate (n + 1) j)) (a j) (b j)) * flowErr W x b σ ω‖ ^ p ∂(μ W x.L) ≤
            Cp * (W : ℝ) ^ (CK * p)) ∧
        (Integrable (fun ω => ‖rowSum (fun b => flowErr W x b σ ω) (a 0) *
            ∏ j : Fin n, ((wardProfile (pairP (gammaG x.g)
              (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) x.u
              (a 0 - a j.succ) : ℝ) : ℂ)‖ ^ p) (μ W x.L) ∧
          ∫ ω, ‖rowSum (fun b => flowErr W x b σ ω) (a 0) *
            ∏ j : Fin n, ((wardProfile (pairP (gammaG x.g)
              (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) x.u
              (a 0 - a j.succ) : ℝ) : ℂ)‖ ^ p ∂(μ W x.L) ≤ Cp * (W : ℝ) ^ (CK * p)) ∧
        Integrable (fun ω => ‖flowErr W x a σ ω‖ ^ p) (μ W x.L) ∧
        ∫ ω, ‖flowErr W x a σ ω‖ ^ p ∂(μ W x.L) ≤ Cp * (W : ℝ) ^ (CK * p) := by
  obtain ⟨W₁, H₁⟩ := coneCrude_at R n Cζ
  obtain ⟨C₀, Hc⟩ := coneCrude_crude R I
  refine ⟨coneCrudeE R.C Cζ n * ((2 * n + 5 : ℕ) : ℝ) +
    max C₀ 0 * ((2 * (n + 1) + 2 : ℕ) : ℝ), fun p hp => ?_⟩
  obtain ⟨Cc, W₂, H₂⟩ := Hc ((2 * (n + 1) + 2) * p) (by nlinarith)
  have hC1 : 1 ≤ R.C := R.one_le_C
  have hC0 : 0 ≤ R.C := le_trans zero_le_one hC1
  set K₁ : ℝ := ((1 + (R.C + 1) ^ n) * (2 * R.C)) ^ p with hK₁
  set K₂ : ℝ := ((1 + (1 + R.C) * R.C) ^ (n + 1) * (2 * R.C)) ^ p with hK₂
  set K₃ : ℝ := ((1 + (R.C + 1) ^ n) * (2 * R.C)) ^ p with hK₃
  set K₄ : ℝ := (2 * R.C) ^ p with hK₄
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₂0 : 0 ≤ K₂ := by positivity
  have hK₃0 : 0 ≤ K₃ := by positivity
  have hK₄0 : 0 ≤ K₄ := by positivity
  set Ks : ℝ := K₁ + K₂ + K₃ + K₄ with hKs
  refine ⟨Ks * coneCrudeD (n + 1) p Cc, max W₁ W₂,
    fun W hW d x v hd hx hu12 huv hv3 hζ σ a => ?_⟩
  have F := H₁ W (le_trans (le_max_left _ _) hW) d x v hd hx hu12 huv hv3 hζ
  have hcr := H₂ W (le_trans (le_max_right _ _) hW) d x hd hx
  have hBc := coneCrude_Bc_nonneg (by have := F.hL; omega) hcr
  have hBk0 := coneCrudeBk_nonneg (n + 1) p hBc
  have hBk := coneCrudeBk_le (n + 1) p Cc C₀ F.hW
  have hD0 := coneCrudeD_nonneg (n + 1) p Cc
  have hE0 : 0 ≤ coneCrudeE R.C Cζ n := by unfold coneCrudeE; positivity
  have hLam : coneCrudeLam R.C Cζ n W = (W : ℝ) ^ coneCrudeE R.C Cζ n := rfl
  have hγ := coneCrude_gammaG_pos x.g
  have h1u : 0 < 1 - x.u := by linarith [F.hu.2]
  have h1v : 0 < 1 - v := by linarith [F.hv.2]
  have hρ0 : 0 ≤ (1 - x.u) / (1 - v) := div_nonneg h1u.le h1v.le
  have hB0 : 0 ≤ coneCrudeB R.C Cζ n W := le_trans zero_le_one F.hB
  have hℓ := F.hℓ
  have hΛ0 : 0 ≤ coneCrudeLam R.C Cζ n W := le_trans zero_le_one F.hΛ
  have hfin : ∀ {K B : ℝ} {j : ℕ}, 0 ≤ K → K ≤ Ks → j ≤ 2 * n + 5 →
      B ≤ K * (coneCrudeLam R.C Cζ n W ^ j) ^ p *
        coneCrudeBk (n + 1) p (Cc * (W : ℝ) ^ (C₀ * (((2 * (n + 1) + 2) * p : ℕ) : ℝ))) →
      B ≤ Ks * coneCrudeD (n + 1) p Cc * (W : ℝ) ^ ((coneCrudeE R.C Cζ n *
        ((2 * n + 5 : ℕ) : ℝ) + max C₀ 0 * ((2 * (n + 1) + 2 : ℕ) : ℝ)) * p) := by
    intro K B j hK hKK hj hB
    refine hB.trans ?_
    rw [hLam]
    refine (coneCrude_conclude F.hW hE0 hj hK hBk0 hBk).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKK hD0) (by positivity)
  -- the total weights of the two coefficient families
  have hA₁ : ∑ b, ‖projCoef (pairP (gammaG x.g)
      (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) v x.u a b‖ ≤
      ((1 - x.u) / (1 - v)) ^ (n + 1) *
        (1 + ((R.C + 1) / ellProp x.g x.L x.u) ^ n * (x.L : ℝ) ^ n) :=
    (coneCrude_projCoef_weight _ v x.u a F.hU0 F.hθ0 F.hT).trans
      (mul_le_mul_of_nonneg_right (coneCrude_prod_rows_real _ a F.hU0 F.hUr) (by positivity))
  have hA₁Λ : ((1 - x.u) / (1 - v)) ^ (n + 1) *
        (1 + ((R.C + 1) / ellProp x.g x.L x.u) ^ n * (x.L : ℝ) ^ n) ≤
      (1 + (R.C + 1) ^ n) * coneCrudeLam R.C Cζ n W ^ (n + 1 + 1) := by
    calc ((1 - x.u) / (1 - v)) ^ (n + 1) *
          (1 + ((R.C + 1) / ellProp x.g x.L x.u) ^ n * (x.L : ℝ) ^ n)
        ≤ coneCrudeLam R.C Cζ n W ^ (n + 1) *
          ((1 + (R.C + 1) ^ n) * coneCrudeLam R.C Cζ n W) :=
          mul_le_mul (pow_le_pow_left₀ hρ0 F.hρΛ _) F.hTΛ (by positivity) (by positivity)
      _ = (1 + (R.C + 1) ^ n) * coneCrudeLam R.C Cζ n W ^ (n + 1 + 1) := by ring
  have hA₂ : ∑ b : Fin (n + 1) → Fin x.L, ‖∏ j, pairU (gammaG x.g)
      (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E)) x.u v (σ j)
      (σ (finRotate (n + 1) j)) (a j) (b j)‖ ≤
      ((1 - x.u) / (1 - v) + (1 + R.C) * R.C) ^ (n + 1) :=
    coneCrude_prod_rows (fun j y z => pairU (gammaG x.g)
      (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E)) x.u v (σ j)
      (σ (finRotate (n + 1) j)) y z) a fun j => F.hR₂ _ _ (a j)
  have hA₂Λ : ((1 - x.u) / (1 - v) + (1 + R.C) * R.C) ^ (n + 1) ≤
      (1 + (1 + R.C) * R.C) ^ (n + 1) * coneCrudeLam R.C Cζ n W ^ (n + 1) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) F.hR₂Λ _
  have hDm := fun b => coneCrude_err_mom x W F.hW F.root.1 F.hu.2 (k := n + 1) (by omega) F.hB
    F.hprk hp hBc hcr σ b
  have hDB : 0 ≤ (2 * coneCrudeB R.C Cζ n W) ^ p *
      coneCrudeBk (n + 1) p (Cc * (W : ℝ) ^ (C₀ * (((2 * (n + 1) + 2) * p : ℕ) : ℝ))) := by
    positivity
  -- the propagated projected field
  have X1 := coneCrude_mom_sum_le (μ W x.L) hp _ (fun b ω => flowErr W x b σ ω) hDB hDm hA₁
  -- the propagated field
  have X2 := coneCrude_mom_sum_le (μ W x.L) hp _ (fun b ω => flowErr W x b σ ω) hDB hDm hA₂
  -- the restored row
  have X3 := coneCrude_mom_mul_const (μ W x.L) hp (∏ j : Fin n, ((wardProfile (pairP
      (gammaG x.g) (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) x.u
      (a 0 - a j.succ) : ℝ) : ℂ))
    (coneCrude_rowSum_mom (μ W x.L) hp (fun ω b => flowErr W x b σ ω) hDB hDm (a 0))
  have hc : ‖∏ j : Fin n, ((wardProfile (pairP (gammaG x.g)
      (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) x.u
      (a 0 - a j.succ) : ℝ) : ℂ)‖ * (x.L : ℝ) ^ n ≤
      (1 + (R.C + 1) ^ n) * coneCrudeLam R.C Cζ n W ^ 0 * coneCrudeLam R.C Cζ n W ^ 1 := by
    have h1 : ‖∏ j : Fin n, ((wardProfile (pairP (gammaG x.g)
        (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) x.u
        (a 0 - a j.succ) : ℝ) : ℂ)‖ ≤ ((R.C + 1) / ellProp x.g x.L x.u) ^ n := by
      rw [norm_prod]
      refine le_trans (le_of_eq (Finset.prod_congr rfl fun j _ => ?_)) (F.hT a)
      rw [Complex.norm_real, Real.norm_of_nonneg (F.hθ0 _)]
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ (x.L : ℝ) ^ n)
    have h3 := F.hTΛ
    simp only [pow_zero, mul_one, pow_one]
    linarith
  have e3 : ∀ y : ℝ, ‖∏ j : Fin n, ((wardProfile (pairP (gammaG x.g)
      (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) x.u
      (a 0 - a j.succ) : ℝ) : ℂ)‖ ^ p * (((x.L : ℝ) ^ n) ^ p * y) =
      (‖∏ j : Fin n, ((wardProfile (pairP (gammaG x.g)
      (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) x.u
      (a 0 - a j.succ) : ℝ) : ℂ)‖ * (x.L : ℝ) ^ n) ^ p * y := fun y => by
    rw [mul_pow]; ring
  have hw4 : 2 * coneCrudeB R.C Cζ n W ≤ 2 * R.C * coneCrudeLam R.C Cζ n W := F.hBΛ
  refine ⟨⟨X1.2.1, hfin hK₁0 (by linarith) (j := n + 1 + 1 + 1) (by omega)
      (X1.2.2.trans (coneCrude_arith_two (by positivity) (by positivity) hBk0 hA₁Λ hw4))⟩,
    ⟨X2.2.1, hfin hK₂0 (by linarith) (j := n + 1 + 1) (by omega)
      (X2.2.2.trans (coneCrude_arith_two (by positivity) (by positivity) hBk0 hA₂Λ hw4))⟩,
    ⟨X3.2.1, hfin hK₃0 (by linarith) (j := 0 + 1 + 1) (by omega) ?_⟩, (hDm a).2.1,
    hfin hK₄0 (by linarith) (j := 1) (by omega) ((hDm a).2.2.trans ?_)⟩
  · refine X3.2.2.trans ?_
    rw [e3]
    have := coneCrude_arith_two (p := p) (A := ‖∏ j : Fin n, ((wardProfile (pairP (gammaG x.g)
      (dysonMat (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))) x.u
      (a 0 - a j.succ) : ℝ) : ℂ)‖ * (x.L : ℝ) ^ n) (by positivity) (by positivity) hBk0 hc hw4
    refine this.trans (le_of_eq ?_)
    rw [hK₃]; ring
  · have h := pow_le_pow_left₀ (by positivity) hw4 p
    calc (2 * coneCrudeB R.C Cζ n W) ^ p *
          coneCrudeBk (n + 1) p (Cc * (W : ℝ) ^ (C₀ * (((2 * (n + 1) + 2) * p : ℕ) : ℝ)))
        ≤ (2 * R.C * coneCrudeLam R.C Cζ n W) ^ p *
          coneCrudeBk (n + 1) p (Cc * (W : ℝ) ^ (C₀ * (((2 * (n + 1) + 2) * p : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right h hBk0
      _ = K₄ * (coneCrudeLam R.C Cζ n W ^ 1) ^ p *
          coneCrudeBk (n + 1) p (Cc * (W : ℝ) ^ (C₀ * (((2 * (n + 1) + 2) * p : ℕ) : ℝ))) := by
          rw [hK₄]; ring

end LSBA
