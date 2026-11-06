import LSBA.Averaging.Vertical
import LSBA.Flow.SurrField
import LSBA.Primitive.Large

/-!
# The loop-error field on the Gaussian slice

The loop error `D_k = ℒ_k − 𝒦_k` of (5.17) [fo:eq:error-hierarchy] as a field of the block
coordinates, its heat class in time, and crude moments of its generator and bracket uniform in the
coupling on the large-coupling family of Lemma 5.6 [fo:prop:inputs].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The loop error `D_k = ℒ_k - 𝒦_k` of (5.17) [fo:eq:error-hierarchy] at time `r` as a field of
the block coordinates `x` of the slice `A_g ⊗ I + Σ x_{c,k} T_{c,k}`. -/
def loopErrField (g E : ℝ) (m : ℂ) (W L : ℕ) {k : ℕ} (a : Fin k → Fin L) (σ : Fin k → Bool)
    (r : ℝ) (x : Ω W L) : ℂ :=
  loopTr (resolventMat (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) x)
      (zChar g E m r)) a σ -
    primLoop g W L E m r a σ

/-- The loop error at a flow point is the field `loopErrField` at the scaled Gaussian coordinates
`√(uγ_g/W) ω`, the single-time realization of (5.1) [fo:eq:flow]. -/
theorem flowErr_eq_loopErrField (W : ℕ) (p : FlowPt) (hu : 0 ≤ p.u) {k : ℕ}
    (a : Fin k → Fin p.L) (σ : Fin k → Bool) (ω : Ω W p.L) :
    flowErr W p a σ ω =
      loopErrField p.g p.E (mRoot p.g p.L p.E) W p.L a σ p.u
        (Real.sqrt (p.u * (gammaG p.g / W)) • ω) := by
  have hγ : 0 ≤ gammaG p.g := by unfold gammaG; positivity
  unfold flowErr flowG flowH loopErrField
  rw [blockFlow_eq_blockSlice _ _ _ (mul_nonneg hu hγ), mul_div_assoc]

/-- `A_g ⊗ I` is Hermitian. -/
private theorem loopField_herm (g : ℝ) (W L : ℕ) :
    (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)).IsHermitian := by
  have hA : (Ag g L).IsHermitian := by
    unfold Matrix.IsHermitian Ag
    rw [Matrix.conjTranspose_smul, (cycleAdj_isHermitian L).eq]
    simp
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_kronecker, hA.eq, Matrix.conjTranspose_one]

/-- Primitive loops of every length are continuous in time on `(-1, 1)` at a root. -/
private theorem loopField_primLoop_contOn (g : ℝ) (W L : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ L) (E : ℝ)
    (m : ℂ) (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {n : ℕ} (a : Fin n → Fin L)
    (σ : Fin n → Bool) : ContinuousOn (fun r => primLoop g W L E m r a σ) (Set.Ioo (-1) 1) := by
  rcases n with _ | _ | n
  · exact continuousOn_const (c := primLoop g W L E m 0 a σ)
  · exact continuousOn_const (c := primLoop g W L E m 0 a σ)
  · exact fun r hr => (primLoop_hasDerivAt g W L hW hL E m hm r hr (by omega) a σ).continuousAt
      |>.continuousWithinAt

/-- The primitive loops satisfy (5.10) [fo:eq:primitive] at every `u ∈ (-1, 1)`, all lengths. -/
private theorem loopField_primDeriv (g : ℝ) (W L : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ L) (E : ℝ) (m : ℂ)
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

/-- The loop-error field lies in the heat class on every time window `(a', b')` with
`-1 < a'` and `b' < 1`. -/
theorem heatClass_loopErrField (g E : ℝ) (m : ℂ) (W L : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ L)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {k : ℕ} (a : Fin k → Fin L)
    (σ : Fin k → Bool) {a' b' : ℝ} (ha' : -1 < a') (hb' : b' < 1) :
    HeatClass (fun r x => loopErrField g E m W L a σ r x) a' b' := by
  have hsub : Set.Ioo a' b' ⊆ Set.Ioo (-1) 1 := fun r hr => ⟨ha'.trans hr.1, hr.2.trans hb'⟩
  have hIcc : Set.Icc a' b' ⊆ Set.Ioo (-1) 1 := fun r hr =>
    ⟨ha'.trans_le hr.1, hr.2.trans_lt hb'⟩
  set κ : ℝ → ℂ := fun r => primLoop g W L E m r a σ with hκdef
  set κ' : ℝ → ℂ := fun r => ((gammaG g * W : ℝ) : ℂ) *
    cutSumFam (fun n c τ => primLoop g W L E m r (k := n) c τ) a σ with hκ'def
  have hc : ContinuousOn κ (Set.Ioo (-1) 1) :=
    loopField_primLoop_contOn g W L hW hL E m hm _ _
  have hc' : ContinuousOn κ' (Set.Ioo (-1) 1) := by
    refine continuousOn_const.mul ?_
    unfold cutSumFam
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    split_ifs
    · exact continuousOn_finsetSum _ fun c _ =>
        (loopField_primLoop_contOn g W L hW hL E m hm _ _).mul
          (loopField_primLoop_contOn g W L hW hL E m hm _ _)
    · exact continuousOn_const
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc.mono hIcc)
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc'.mono hIcc)
  have h := (heatClass_loopTr W L k _ (loopField_herm g W L) g E m hm.1 a σ
    (a' := a') hb').sub_time κ κ'
    (fun r hr => loopField_primDeriv g W L hW hL E m hm r (hsub hr) k a σ)
    (hc'.mono hsub)
    ⟨max C₁ C₂, fun r hr => ⟨(hC₁ r (Set.Ioo_subset_Icc_self hr)).trans (le_max_left _ _),
      (hC₂ r (Set.Ioo_subset_Icc_self hr)).trans (le_max_right _ _)⟩⟩
  exact h

/-! ### Entry bounds for loops of every length -/

section LoopEntry

variable {W L : ℕ}

/-- The number of sites in a block: `∑_{r} 1_{r.1 = a} f = W f`. -/
private lemma loopField_sum_block (a : Fin L) (f : ℝ) :
    ∑ r : Fin L × Fin W, (if r.1 = a then f else 0) = (W : ℝ) * f := by
  rw [Fintype.sum_prod_type]
  have h : ∀ x : Fin L, ∑ _y : Fin W, (if x = a then f else 0) =
      if x = a then (W : ℝ) * f else 0 := fun x => by split_ifs <;> simp
  simp only [h]
  simp

/-- Bounds on the entries of a product of loop factors `S_i E_{a_i}`: supported on the columns of
block `a`, with entries on rows of the labels `Lab` at most `B / W`. -/
private def loopFieldBd (Lab : Finset (Fin L)) (P : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a : Fin L) (B : ℝ) : Prop :=
  (∀ p q : Fin L × Fin W, q.1 ≠ a → P p q = 0) ∧
    ∀ p q : Fin L × Fin W, p.1 ∈ Lab → ‖P p q‖ ≤ B * (W : ℝ)⁻¹

/-- One loop factor `S E_a`. -/
private lemma loopFieldBd.factor {Lab : Finset (Fin L)}
    {S : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hS : ∀ p q : Fin L × Fin W, p.1 ∈ Lab → q.1 ∈ Lab → ‖S p q‖ ≤ K)
    {a : Fin L} (ha : a ∈ Lab) : loopFieldBd Lab (S * blockE W L a) a K := by
  refine ⟨fun p q hq => ?_, fun p q hp => ?_⟩
  · simp [blockE, Matrix.mul_diagonal, hq]
  · simp only [blockE, Matrix.mul_diagonal]
    by_cases hq : q.1 = a
    · simp only [hq, ite_true, norm_mul, norm_inv, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_right (hS p q hp (hq ▸ ha)) (by positivity) |>.trans_eq (by ring)
    · simp only [hq, ite_false, mul_zero, norm_zero]
      positivity

/-- Product of two loop-factor products. -/
private lemma loopFieldBd.mul {Lab : Finset (Fin L)}
    {P Q : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    {a b : Fin L} {B C : ℝ} (hW : 1 ≤ W) (hB : 0 ≤ B) (hP : loopFieldBd Lab P a B)
    (ha : a ∈ Lab) (hQ : loopFieldBd Lab Q b C) : loopFieldBd Lab (P * Q) b (B * C) := by
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
          rw [loopField_sum_block]
          field_simp

/-- The trace of a loop-factor product. -/
private lemma loopFieldBd.trace_le {Lab : Finset (Fin L)}
    {P : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} {a : Fin L} {B : ℝ} (hW : 1 ≤ W)
    (hP : loopFieldBd Lab P a B) (ha : a ∈ Lab) : ‖P.trace‖ ≤ B := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  rw [Matrix.trace]
  calc ‖∑ p, P.diag p‖ ≤ ∑ p : Fin L × Fin W, (if p.1 = a then B * (W : ℝ)⁻¹ else 0) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
        by_cases hp : p.1 = a
        · simp only [hp, ite_true, Matrix.diag]
          exact hP.2 p p (hp ▸ ha)
        · simp [Matrix.diag, hP.1 p p hp, hp]
    _ = B := by
        rw [loopField_sum_block]
        field_simp

/-- A loop-factor product times a matrix bounded on the blocks `Lab`. -/
private lemma loopFieldBd.mul_bdd {Lab : Finset (Fin L)}
    {P S : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} {a : Fin L} {B K : ℝ} (hW : 1 ≤ W)
    (hB : 0 ≤ B) (hP : loopFieldBd Lab P a B) (ha : a ∈ Lab)
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
        rw [loopField_sum_block]
        field_simp

/-- Bounds on the entries of `G` on the blocks `Lab` pass to `G^σ`. -/
private lemma loopField_sgn_bound {Lab : Finset (Fin L)}
    {G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} {K : ℝ}
    (hG : ∀ p q : Fin L × Fin W, p.1 ∈ Lab → q.1 ∈ Lab → ‖G p q‖ ≤ K) (σ : Bool) :
    ∀ p q : Fin L × Fin W, p.1 ∈ Lab → q.1 ∈ Lab → ‖sgnMat G σ p q‖ ≤ K := by
  intro p q hp hq
  cases σ
  · simp only [sgnMat, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply, norm_star]
    exact hG q p hq hp
  · simpa [sgnMat] using hG p q hp hq

/-- A product of `n + 1` loop factors with labels in `Lab`. -/
private lemma loopField_prod_bd {Lab : Finset (Fin L)}
    {G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} {K : ℝ} (hW : 1 ≤ W) (hK : 0 ≤ K)
    (hG : ∀ p q : Fin L × Fin W, p.1 ∈ Lab → q.1 ∈ Lab → ‖G p q‖ ≤ K) :
    ∀ (n : ℕ) (a : Fin (n + 1) → Fin L) (σ : Fin (n + 1) → Bool), (∀ i, a i ∈ Lab) →
      loopFieldBd Lab (List.ofFn fun i => sgnMat G (σ i) * blockE W L (a i)).prod
        (a (Fin.last n)) (K ^ (n + 1))
  | 0, a, σ, ha => by
      simpa [List.ofFn_succ] using loopFieldBd.factor hK (loopField_sgn_bound hG (σ 0)) (ha 0)
  | n + 1, a, σ, ha => by
      rw [List.ofFn_succ, List.prod_cons]
      have ih := loopField_prod_bd hW hK hG n (fun i => a i.succ) (fun i => σ i.succ)
        (fun i => ha _)
      have h0 := loopFieldBd.factor hK (loopField_sgn_bound hG (σ 0)) (ha 0)
      have h := h0.mul hW hK (ha 0) ih
      rw [Fin.succ_last, ← pow_succ'] at h
      exact h

/-- A loop of length `n ≥ 1` with labels in `Lab` is at most `K^n`. -/
private lemma loopField_loopTr_le {Lab : Finset (Fin L)}
    {G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} {K : ℝ} (hW : 1 ≤ W) (hK : 0 ≤ K)
    (hG : ∀ p q : Fin L × Fin W, p.1 ∈ Lab → q.1 ∈ Lab → ‖G p q‖ ≤ K) {n : ℕ} (hn : 1 ≤ n)
    (a : Fin n → Fin L) (σ : Fin n → Bool) (ha : ∀ i, a i ∈ Lab) : ‖loopTr G a σ‖ ≤ K ^ n := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  exact (loopField_prod_bd hW hK hG n a σ ha).trace_le hW (ha _)

/-- The cut loops `B_i` of a loop of length `k` have entries at most `K^{k+1}` on the blocks
`Lab`. -/
private lemma loopField_loopB_le {Lab : Finset (Fin L)}
    {G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} {K : ℝ} (hW : 1 ≤ W) (hK : 0 ≤ K)
    (hG : ∀ p q : Fin L × Fin W, p.1 ∈ Lab → q.1 ∈ Lab → ‖G p q‖ ≤ K) {k : ℕ}
    (a : Fin k → Fin L) (σ : Fin k → Bool) (ha : ∀ i, a i ∈ Lab) (i : Fin k)
    {p q : Fin L × Fin W} (hp : p.1 ∈ Lab) (hq : q.1 ∈ Lab) :
    ‖loopB G a σ i p q‖ ≤ K ^ (k + 1) := by
  obtain ⟨n, rfl⟩ : ∃ n', k = n' + 1 := ⟨k - 1, by have := i.2; omega⟩
  have h := loopField_prod_bd hW hK hG n (fun t => a (i + t)) (fun t => σ (i + t))
    (fun t => ha _)
  have := h.mul_bdd hW (pow_nonneg hK _) (ha _) (loopField_sgn_bound hG (σ i)) hp hq
  rw [pow_succ]
  simpa [loopB] using this

/-- The trace in the carré du champ of a loop (5.9) [gc:eq:bracket] on entries of the block
`c`. -/
private lemma loopField_gamma_trace_le (hW : 1 ≤ W) {c : Fin L}
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
            _ = (W : ℝ) * (KX * KY) := loopField_sum_block c _
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
        rw [loopField_sum_block]; ring

end LoopEntry

/-! ### Pointwise bounds of the generator and bracket of a loop error -/

section Pointwise

variable {W L : ℕ}

private lemma loopField_gammaG_pos (g : ℝ) : 0 < gammaG g := by
  unfold gammaG
  have : (1 : ℝ) ≤ max 1 g := le_max_left _ _
  positivity

/-- `‖m^σ‖ = ‖m‖`. -/
private lemma loopField_norm_sgnScalar (m : ℂ) (s : Bool) : ‖sgnScalar m s‖ = ‖m‖ := by
  cases s <;> simp [sgnScalar]

/-- The labels of an insertion lie in any set containing the labels and the inserted label. -/
private lemma loopField_insLab_mem {k : ℕ} {Lab : Finset (Fin L)} (a : Fin k → Fin L)
    (i : Fin k) {c : Fin L} (ha : ∀ j, a j ∈ Lab) (hc : c ∈ Lab) (t : Fin (k + 1)) :
    insLab a i c t ∈ Lab := by
  unfold insLab
  rcases Fin.eq_self_or_eq_succAbove i.castSucc t with h | ⟨j, rfl⟩
  · rw [h, Fin.insertNth_apply_same]; exact hc
  · rw [Fin.insertNth_apply_succAbove]; exact ha j

/-- The labels of a left cut lie in any set containing the labels and the cut label. -/
private lemma loopField_cutLLab_mem {k : ℕ} {Lab : Finset (Fin L)} (a : Fin k → Fin L)
    (i j : Fin k) {c : Fin L} (ha : ∀ j, a j ∈ Lab) (hc : c ∈ Lab)
    (t : Fin (k + i - j + 1)) : cutLLab a i j c t ∈ Lab := by
  unfold cutLLab
  split_ifs
  exacts [ha _, hc, ha _]

/-- The labels of a right cut lie in any set containing the labels and the cut label. -/
private lemma loopField_cutRLab_mem {k : ℕ} {Lab : Finset (Fin L)} (a : Fin k → Fin L)
    (i j : Fin k) {c : Fin L} (ha : ∀ j, a j ∈ Lab) (hc : c ∈ Lab)
    (t : Fin (j - i + 1)) : cutRLab a i j c t ∈ Lab := by
  unfold cutRLab
  split_ifs
  exacts [ha _, hc]

/-- The right side of (5.17) [fo:eq:error-hierarchy] for a loop error of length `k` is bounded
by a weighted sum of powers of the entry bounds `K_c`, pointwise in the matrix. -/
private lemma loopField_gen_pointwise (g E : ℝ) (m : ℂ) (hW : 1 ≤ W) (u : ℝ)
    (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) {k : ℕ} (a : Fin k → Fin L)
    (σ : Fin k → Bool) {B : ℝ} (hB : 1 ≤ B) (hmB : ‖m‖ ≤ B)
    (hpr : ∀ n : ℕ, 2 ≤ n → n ≤ k → ∀ (b : Fin n → Fin L) (τ : Fin n → Bool),
      ‖primLoop g W L E m u b τ‖ ≤ B)
    (Lab : Fin L → Finset (Fin L)) (hLa : ∀ c i, a i ∈ Lab c) (hLc : ∀ c, c ∈ Lab c)
    (K : Fin L → ℝ) (hK : ∀ c, 1 ≤ K c)
    (hG : ∀ c, ∀ p q : Fin L × Fin W, p.1 ∈ Lab c → q.1 ∈ Lab c →
      ‖resolventMat M (zChar g E m u) p q‖ ≤ K c) :
    ‖lightW g E m a σ u M + ((gammaG g * W : ℝ) : ℂ) *
        cutErrSum (fun n b τ => primLoop g W L E m u (k := n) b τ)
          (errFam g E m (fun n b τ => primLoop g W L E m u (k := n) b τ) u M) a σ‖ ≤
      ∑ c : Fin L, (10 * (k : ℝ) ^ 2 * B ^ 2 * (gammaG g * W)) * K c ^ (2 * k + 2) := by
  set G := resolventMat M (zChar g E m u) with hGdef
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hγW : 0 ≤ gammaG g * W := mul_nonneg (loopField_gammaG_pos g).le hW0.le
  have hK0 : ∀ c, 0 ≤ K c := fun c => by linarith [hK c]
  have hB0 : 0 ≤ B := by linarith
  have hKk : ∀ c, 1 ≤ K c ^ k := fun c => one_le_pow₀ (hK c)
  have hD : ∀ c {n : ℕ}, 2 ≤ n → n ≤ k → ∀ (b : Fin n → Fin L) (τ : Fin n → Bool),
      (∀ t, b t ∈ Lab c) →
      ‖errFam g E m (fun n b τ => primLoop g W L E m u (k := n) b τ) u M n b τ‖ ≤
        2 * B * K c ^ k := by
    intro c n hn hnk b τ hb
    have h1 := (loopField_loopTr_le hW (hK0 c) (hG c) (by omega : 1 ≤ n) b τ hb).trans
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
        loopField_loopTr_le hW (hK0 c) (hG c) le_rfl _ _ (fun t => by
          fin_cases t; exact hLc c)
      have h2 : ‖loopTr G (insLab a i c) (insSgn σ i)‖ ≤ K c ^ (k + 1) :=
        loopField_loopTr_le hW (hK0 c) (hG c) (by omega) _ _
          (loopField_insLab_mem a i (hLa c) (hLc c))
      have h3 : ‖loopTr G ![c] ![σ i] - sgnScalar m (σ i)‖ ≤ K c + B := by
        refine (norm_sub_le _ _).trans ?_
        rw [loopField_norm_sgnScalar]
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
  -- the cut terms
  have hcut : ‖cutErrSum (fun n b τ => primLoop g W L E m u (k := n) b τ)
      (errFam g E m (fun n b τ => primLoop g W L E m u (k := n) b τ) u M) a σ‖ ≤
      (k : ℝ) ^ 2 * ∑ c, 8 * X c := by
    unfold cutErrSum
    have hpair : ∀ i j : Fin k, ‖(if i < j then ∑ c : Fin L,
        (primLoop g W L E m u (cutLLab a i j c) (cutLSgn σ i j) *
            errFam g E m (fun n b τ => primLoop g W L E m u (k := n) b τ) u M _
              (cutRLab a i j c) (cutRSgn σ i j) +
          errFam g E m (fun n b τ => primLoop g W L E m u (k := n) b τ) u M _
              (cutLLab a i j c) (cutLSgn σ i j) *
            primLoop g W L E m u (cutRLab a i j c) (cutRSgn σ i j) +
          errFam g E m (fun n b τ => primLoop g W L E m u (k := n) b τ) u M _
              (cutLLab a i j c) (cutLSgn σ i j) *
            errFam g E m (fun n b τ => primLoop g W L E m u (k := n) b τ) u M _
              (cutRLab a i j c) (cutRSgn σ i j)) else 0)‖ ≤ ∑ c, 8 * X c := by
      intro i j
      split_ifs with hij
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
        have hij' : i.val < j.val := hij
        have hi := i.2
        have hj := j.2
        have hLl : 2 ≤ k + (i : ℕ) - (j : ℕ) + 1 := by omega
        have hLu : k + (i : ℕ) - (j : ℕ) + 1 ≤ k := by omega
        have hRl : 2 ≤ (j : ℕ) - (i : ℕ) + 1 := by omega
        have hRu : (j : ℕ) - (i : ℕ) + 1 ≤ k := by omega
        have kl := hpr _ hLl hLu (cutLLab a i j c) (cutLSgn σ i j)
        have kr := hpr _ hRl hRu (cutRLab a i j c) (cutRSgn σ i j)
        have dl := hD c hLl hLu (cutLLab a i j c) (cutLSgn σ i j)
          (loopField_cutLLab_mem a i j (hLa c) (hLc c))
        have dr := hD c hRl hRu (cutRLab a i j c) (cutRSgn σ i j)
          (loopField_cutRLab_mem a i j (hLa c) (hLc c))
        have hKc := hK c
        have hk1 := hKk c
        have h2k : K c ^ k * K c ^ k ≤ K c ^ (2 * k + 2) := by
          rw [← pow_add]; exact pow_le_pow_right₀ hKc (by omega)
        have hk2 : K c ^ k ≤ K c ^ (2 * k + 2) := pow_le_pow_right₀ hKc (by omega)
        refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
        rw [norm_mul, norm_mul, norm_mul]
        have e1 := mul_le_mul kl dr (norm_nonneg _) hB0
        have e2 := mul_le_mul dl kr (norm_nonneg _) (by positivity)
        have e3 := mul_le_mul dl dr (norm_nonneg _) (by positivity)
        have hB2 : B ≤ B ^ 2 := by nlinarith
        simp only [hXdef]
        have hpos : 0 ≤ K c ^ k := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hk2 (by positivity : (0 : ℝ) ≤ B ^ 2),
          mul_le_mul_of_nonneg_left h2k (by positivity : (0 : ℝ) ≤ B ^ 2)]
      · rw [norm_zero]
        exact Finset.sum_nonneg fun c _ => by linarith [hX0 c]
    calc _ ≤ ∑ _i : Fin k, ∑ _j : Fin k, ∑ c, 8 * X c := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hpair i j)
      _ = (k : ℝ) ^ 2 * ∑ c, 8 * X c := by
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
  have e2 : ∑ c, 8 * X c = 8 * ∑ c, X c := by rw [Finset.mul_sum]
  rw [e1] at hlight
  rw [e2] at hcut
  have h3 := mul_le_mul_of_nonneg_left hcut hγW
  have h4 : (gammaG g * W) * ((k : ℝ) * (2 * ∑ c, X c)) ≤
      (gammaG g * W) * ((k : ℝ) ^ 2 * (2 * ∑ c, X c)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk2 (by positivity)) hγW
  nlinarith

/-- The bracket (5.9) [gc:eq:bracket] of a loop of length `k` is bounded by a weighted sum of
powers of the entry bounds `K_c`, pointwise in the matrix. -/
private lemma loopField_gamma_pointwise (g E : ℝ) (m : ℂ) (hm : 0 < m.im) (hW : 1 ≤ W)
    {u : ℝ} (hu : u < 1) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    {k : ℕ} (a : Fin k → Fin L) (σ : Fin k → Bool)
    (Lab : Fin L → Finset (Fin L)) (hLa : ∀ c i, a i ∈ Lab c) (hLc : ∀ c, c ∈ Lab c)
    (K : Fin L → ℝ) (hK : ∀ c, 1 ≤ K c)
    (hG : ∀ c, ∀ p q : Fin L × Fin W, p.1 ∈ Lab c → q.1 ∈ Lab c →
      ‖resolventMat M (zChar g E m u) p q‖ ≤ K c) :
    ‖blockGamma W L (gammaG g) (resLoop g E m a σ u) (resLoop g E m a σ u) M‖ ≤
      ∑ c : Fin L, ((k : ℝ) ^ 2 * (gammaG g * W)) * K c ^ (2 * k + 2) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hγ := loopField_gammaG_pos g
  have hK0 : ∀ c, 0 ≤ K c := fun c => by linarith [hK c]
  rw [blockGamma_loopTr g E m hm hu hM a σ a σ, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hterm : ∀ (c : Fin L) (i j : Fin k),
      ‖(((W : ℂ) • blockE W L c) * loopB (resolventMat M (zChar g E m u)) a σ i *
          ((W : ℂ) • blockE W L c) *
          (loopB (resolventMat M (zChar g E m u)) a σ j)ᴴ).trace‖ ≤
        (W : ℝ) ^ 2 * (K c ^ (k + 1) * K c ^ (k + 1)) := fun c i j => by
    refine loopField_gamma_trace_le hW (pow_nonneg (hK0 c) _) ?_ ?_
    · intro p q hp hq
      exact loopField_loopB_le hW (hK0 c) (hG c) a σ (hLa c) i (by rw [hp]; exact hLc c)
        (by rw [hq]; exact hLc c)
    · intro p q hp hq
      exact loopField_loopB_le hW (hK0 c) (hG c) a σ (hLa c) j (by rw [hp]; exact hLc c)
        (by rw [hq]; exact hLc c)
  calc (gammaG g / W) * ‖∑ c : Fin L, ∑ i : Fin k, ∑ j : Fin k,
        (((W : ℂ) • blockE W L c) * loopB (resolventMat M (zChar g E m u)) a σ i *
          ((W : ℂ) • blockE W L c) *
          (loopB (resolventMat M (zChar g E m u)) a σ j)ᴴ).trace‖
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

/-! ### Continuity in the sample -/

section Cont

variable {W L : ℕ}

/-- The resolvent of the single-time realization is continuous in the sample off the real
axis. -/
private lemma loopField_continuous_resolvent (g u : ℝ) (W L : ℕ) {z : ℂ} (hz : z.im ≠ 0) :
    Continuous fun ω : Ω W L => resolventMat (flowH g W L u ω) z := by
  have hV : Continuous fun ω : Ω W L => blockV W L ω := by
    simp only [blockV_eq_sum_blockBasis]
    fun_prop
  have hF : Continuous fun ω : Ω W L => flowH g W L u ω := by
    unfold flowH blockFlow
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
private lemma loopField_continuous_loopTr
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
private lemma loopField_continuous_loopB
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

/-- The right side of (5.17) [fo:eq:error-hierarchy] is continuous in the sample. -/
private lemma loopField_gen_expr_continuous (g E : ℝ) (m : ℂ) (u : ℝ) {k : ℕ}
    (a : Fin k → Fin L) (σ : Fin k → Bool)
    {M : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hM : Continuous fun ω => resolventMat (M ω) (zChar g E m u)) :
    Continuous fun ω => lightW g E m a σ u (M ω) + ((gammaG g * W : ℝ) : ℂ) *
        cutErrSum (fun n b τ => primLoop g W L E m u (k := n) b τ)
          (errFam g E m (fun n b τ => primLoop g W L E m u (k := n) b τ) u (M ω)) a σ := by
  have hl : ∀ {n : ℕ} (b : Fin n → Fin L) (τ : Fin n → Bool),
      Continuous fun ω => loopTr (resolventMat (M ω) (zChar g E m u)) b τ := fun b τ =>
    loopField_continuous_loopTr hM b τ
  refine Continuous.add ?_ (continuous_const.mul ?_)
  · unfold lightW
    exact continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_finsetSum _
      fun c _ => ((hl _ _).sub continuous_const).mul (hl _ _))
  · unfold cutErrSum errFam
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    by_cases hij : i < j
    · simp only [hij, ↓reduceIte]
      exact continuous_finsetSum _ fun c _ =>
        ((continuous_const.mul ((hl _ _).sub continuous_const)).add
          (((hl _ _).sub continuous_const).mul continuous_const)).add
          (((hl _ _).sub continuous_const).mul ((hl _ _).sub continuous_const))
    · simp only [hij, ↓reduceIte]
      exact continuous_const

/-- The bracket of a loop in the form of (5.9) [gc:eq:bracket] is continuous in the sample. -/
private lemma loopField_gamma_expr_continuous (g E : ℝ) (m : ℂ) (u : ℝ) {k : ℕ}
    (a : Fin k → Fin L) (σ : Fin k → Bool)
    {M : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hM : Continuous fun ω => resolventMat (M ω) (zChar g E m u)) :
    Continuous fun ω => ((gammaG g / W : ℝ) : ℂ) * ∑ c : Fin L, ∑ i : Fin k, ∑ j : Fin k,
        (((W : ℂ) • blockE W L c) * loopB (resolventMat (M ω) (zChar g E m u)) a σ i *
          ((W : ℂ) • blockE W L c) *
          (loopB (resolventMat (M ω) (zChar g E m u)) a σ j)ᴴ).trace := by
  refine continuous_const.mul (continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => ?_)
  refine Continuous.matrix_trace ?_
  refine Continuous.matrix_mul (Continuous.matrix_mul (Continuous.matrix_mul continuous_const ?_)
    continuous_const) ?_
  · exact loopField_continuous_loopB hM _ _ i
  · exact (loopField_continuous_loopB hM _ _ j).matrix_conjTranspose

end Cont

/-! ### Moments of weighted sums -/

section WSum

/-- Jensen for weighted sums: `(Σ w_i f_i)^n ≤ (Σ w_i)^{n-1} Σ w_i f_i^n`. -/
private lemma loopField_wsum_pow_le {ι : Type*} [Fintype ι] (w f : ι → ℝ)
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

/-- A weighted sum of nonnegative functions with integrable `n`-th powers has an integrable
`n`-th power, with the weighted moment bound. -/
private lemma loopField_wsum_moment {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
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
      (loopField_wsum_pow_le w (fun i => f i x) hw (fun i => hf0 i x) hn)
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

/-- A constant plus a finite sum of nonnegative functions with integrable `n`-th powers. -/
private lemma loopField_const_sum_moment {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
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
    have h := loopField_wsum_pow_le (fun _ : ι => (1 : ℝ)) (fun i => z i x)
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

end WSum

/-! ### The entry bounds `K_c` and their moments -/

section KMoment

/-- An entry is bounded by the operator norm. -/
private lemma loopField_norm_entry_le {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (i j : n) : ‖X i j‖ ≤ ‖X‖ := by
  have h := Matrix.l2_opNorm_mulVec X ((EuclideanSpace.equiv n ℂ).symm (Pi.single j 1))
  have hx : ‖(EuclideanSpace.equiv n ℂ).symm (Pi.single j (1 : ℂ))‖ = 1 := by simp
  rw [hx, mul_one] at h
  refine le_trans (le_of_eq ?_) ((PiLp.norm_apply_le _ i).trans h)
  simp [Matrix.mulVec_single]

/-- The labels `c, a_0, …, a_{k-1}`. -/
private def loopFieldLab {L k : ℕ} (a : Fin k → Fin L) (c : Fin L) : Finset (Fin L) :=
  Finset.univ.image (Fin.cons c a : Fin (k + 1) → Fin L)

private lemma loopFieldLab_a {L k : ℕ} (a : Fin k → Fin L) (c : Fin L) (i : Fin k) :
    a i ∈ loopFieldLab a c := by
  unfold loopFieldLab
  rw [Finset.mem_image]
  exact ⟨i.succ, Finset.mem_univ _, by simp⟩

private lemma loopFieldLab_c {L k : ℕ} (a : Fin k → Fin L) (c : Fin L) :
    c ∈ loopFieldLab a c := by
  unfold loopFieldLab
  rw [Finset.mem_image]
  exact ⟨0, Finset.mem_univ _, by simp⟩

/-- The bound `K_c = 1 + Σ_{y,z ∈ {c, a_0, …, a_{k-1}}} ‖G_{yz}‖` on the entries of `G` between the
labels. -/
private def loopFieldK (W : ℕ) (x : FlowPt) {k : ℕ} (a : Fin k → Fin x.L) (c : Fin x.L)
    (ω : Ω W x.L) : ℝ :=
  1 + ∑ st : Fin (k + 1) × Fin (k + 1),
    ‖blockOf (flowG W x ω) ((Fin.cons c a : Fin (k + 1) → Fin x.L) st.1)
      ((Fin.cons c a : Fin (k + 1) → Fin x.L) st.2)‖

private lemma loopFieldK_ge (W : ℕ) (x : FlowPt) {k : ℕ} (a : Fin k → Fin x.L) (c : Fin x.L)
    (ω : Ω W x.L) : 1 ≤ loopFieldK W x a c ω := by
  unfold loopFieldK
  have : 0 ≤ ∑ st : Fin (k + 1) × Fin (k + 1),
      ‖blockOf (flowG W x ω) ((Fin.cons c a : Fin (k + 1) → Fin x.L) st.1)
        ((Fin.cons c a : Fin (k + 1) → Fin x.L) st.2)‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  linarith

private lemma loopFieldK_entry (W : ℕ) (x : FlowPt) {k : ℕ} (a : Fin k → Fin x.L) (c : Fin x.L)
    (ω : Ω W x.L) {p q : Fin x.L × Fin W} (hp : p.1 ∈ loopFieldLab a c)
    (hq : q.1 ∈ loopFieldLab a c) :
    ‖flowG W x ω p q‖ ≤ loopFieldK W x a c ω := by
  unfold loopFieldLab at hp hq
  rw [Finset.mem_image] at hp hq
  obtain ⟨i, -, hi⟩ := hp
  obtain ⟨j, -, hj⟩ := hq
  have h1 : ‖flowG W x ω p q‖ ≤ ‖blockOf (flowG W x ω) p.1 q.1‖ :=
    loopField_norm_entry_le (blockOf (flowG W x ω) p.1 q.1) p.2 q.2
  have h2 : ‖blockOf (flowG W x ω) p.1 q.1‖ ≤ ∑ st : Fin (k + 1) × Fin (k + 1),
      ‖blockOf (flowG W x ω) ((Fin.cons c a : Fin (k + 1) → Fin x.L) st.1)
        ((Fin.cons c a : Fin (k + 1) → Fin x.L) st.2)‖ := by
    have := Finset.single_le_sum (f := fun st : Fin (k + 1) × Fin (k + 1) =>
      ‖blockOf (flowG W x ω) ((Fin.cons c a : Fin (k + 1) → Fin x.L) st.1)
        ((Fin.cons c a : Fin (k + 1) → Fin x.L) st.2)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ (i, j))
    simpa [hi, hj] using this
  unfold loopFieldK
  linarith

/-- The moments of `K_c^N` from the moments of the blocks of `G`. -/
private lemma loopFieldK_moment (x : FlowPt) (W : ℕ) (hm : 0 < (mRoot x.g x.L x.E).im)
    (hu1 : x.u < 1) {k : ℕ} (a : Fin k → Fin x.L) {N : ℕ} (hN : 1 ≤ N) {Bc : ℝ}
    (hcr : ∀ y z : Fin x.L, Integrable (fun ω => ‖blockOf (flowG W x ω) y z‖ ^ N)
        (μ W x.L) ∧ ∫ ω, ‖blockOf (flowG W x ω) y z‖ ^ N ∂(μ W x.L) ≤ Bc)
    (c : Fin x.L) :
    Continuous (fun ω => loopFieldK W x a c ω) ∧
    Integrable (fun ω => loopFieldK W x a c ω ^ N) (μ W x.L) ∧
      ∫ ω, loopFieldK W x a c ω ^ N ∂(μ W x.L) ≤
        2 ^ (N - 1) * (1 + (((k + 1) * (k + 1) : ℕ) : ℝ) ^ N * Bc) := by
  have hz : (zChar x.g x.E (mRoot x.g x.L x.E) x.u).im ≠ 0 := by
    rw [im_zChar]; exact (etaChar_pos x.g _ hm hu1).ne'
  have hGc : Continuous fun ω : Ω W x.L => flowG W x ω :=
    loopField_continuous_resolvent x.g x.u W x.L hz
  have hbc : ∀ y z : Fin x.L, Continuous fun ω : Ω W x.L => ‖blockOf (flowG W x ω) y z‖ := by
    intro y z
    refine Continuous.norm (continuous_matrix fun α β => ?_)
    exact (continuous_apply (z, β)).comp ((continuous_apply (y, α)).comp hGc)
  have hKc : Continuous (fun ω : Ω W x.L => loopFieldK W x a c ω) := by
    unfold loopFieldK
    exact continuous_const.add (continuous_finsetSum _ fun st _ => hbc _ _)
  have h := loopField_const_sum_moment (μ W x.L) (A := 1) zero_le_one
    (fun (st : Fin (k + 1) × Fin (k + 1)) ω =>
      ‖blockOf (flowG W x ω) ((Fin.cons c a : Fin (k + 1) → Fin x.L) st.1)
        ((Fin.cons c a : Fin (k + 1) → Fin x.L) st.2)‖)
    (fun _ _ => norm_nonneg _) hN (B := Bc) (fun st => hcr _ _) hKc.aestronglyMeasurable
  refine ⟨hKc, h.1, h.2.trans (le_of_eq ?_)⟩
  simp [Fintype.card_prod]

/-- The anchor point of the flow: the segment pair at the characteristic height has the resolvent
of the flow. -/
private lemma loopField_segG_eq (W : ℕ) (x : FlowPt) (ω : Ω W x.L) :
    segG W (x, etaChar x.g (mRoot x.g x.L x.E) x.u) ω = flowG W x ω := by
  unfold segG flowG
  simp only
  rw [← im_zChar x.g x.E (mRoot x.g x.L x.E) x.u, Complex.re_add_im]

end KMoment

/-! ### Moments at one point -/

section PointMoment

/-- Moments of `𝒢D_k` and `Γ(ℒ_k, ℒ_k)` at one point from the moments of the blocks of `G`,
the primitive-loop bound and `|m| ≤ B`. -/
private lemma loopField_gen_point (x : FlowPt) (W : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ x.L)
    (hm : IsDysonRootV (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E))
    (hu0 : -1 < x.u) (hu1 : x.u < 1) {k : ℕ} {B : ℝ} (hB : 1 ≤ B)
    (hmB : ‖mRoot x.g x.L x.E‖ ≤ B)
    (hpr : ∀ n : ℕ, 2 ≤ n → n ≤ k → ∀ (b : Fin n → Fin x.L) (τ : Fin n → Bool),
      ‖primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b τ‖ ≤ B)
    {p : ℕ} (hp : 1 ≤ p) {Bc : ℝ}
    (hcr : ∀ y z : Fin x.L,
      Integrable (fun ω => ‖blockOf (flowG W x ω) y z‖ ^ ((2 * k + 2) * p)) (μ W x.L) ∧
        ∫ ω, ‖blockOf (flowG W x ω) y z‖ ^ ((2 * k + 2) * p) ∂(μ W x.L) ≤ Bc)
    (a : Fin k → Fin x.L) (σ : Fin k → Bool) :
    (Integrable (fun ω => ‖blockGen W x.L (gammaG x.g)
        (fun r N => resLoop x.g x.E (mRoot x.g x.L x.E) a σ r N -
          primLoop x.g W x.L x.E (mRoot x.g x.L x.E) r a σ) x.u
        (flowH x.g W x.L x.u ω)‖ ^ p) (μ W x.L) ∧
      ∫ ω, ‖blockGen W x.L (gammaG x.g)
        (fun r N => resLoop x.g x.E (mRoot x.g x.L x.E) a σ r N -
          primLoop x.g W x.L x.E (mRoot x.g x.L x.E) r a σ) x.u
        (flowH x.g W x.L x.u ω)‖ ^ p ∂(μ W x.L) ≤
        ((x.L : ℝ) * (10 * (k : ℝ) ^ 2 * B ^ 2 * (gammaG x.g * W))) ^ p *
          (2 ^ ((2 * k + 2) * p - 1) *
            (1 + (((k + 1) * (k + 1) : ℕ) : ℝ) ^ ((2 * k + 2) * p) * Bc))) ∧
    (Integrable (fun ω => ‖blockGamma W x.L (gammaG x.g)
        (resLoop x.g x.E (mRoot x.g x.L x.E) a σ x.u)
        (resLoop x.g x.E (mRoot x.g x.L x.E) a σ x.u) (flowH x.g W x.L x.u ω)‖ ^ p)
        (μ W x.L) ∧
      ∫ ω, ‖blockGamma W x.L (gammaG x.g)
        (resLoop x.g x.E (mRoot x.g x.L x.E) a σ x.u)
        (resLoop x.g x.E (mRoot x.g x.L x.E) a σ x.u) (flowH x.g W x.L x.u ω)‖ ^ p
        ∂(μ W x.L) ≤
        ((x.L : ℝ) * (10 * (k : ℝ) ^ 2 * B ^ 2 * (gammaG x.g * W))) ^ p *
          (2 ^ ((2 * k + 2) * p - 1) *
            (1 + (((k + 1) * (k + 1) : ℕ) : ℝ) ^ ((2 * k + 2) * p) * Bc))) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hγ := loopField_gammaG_pos x.g
  have hγW : 0 ≤ gammaG x.g * W := mul_nonneg hγ.le hW0.le
  have hz : (zChar x.g x.E (mRoot x.g x.L x.E) x.u).im ≠ 0 := by
    rw [im_zChar]; exact (etaChar_pos x.g _ hm.1 hu1).ne'
  have hGc : Continuous fun ω : Ω W x.L => flowG W x ω :=
    loopField_continuous_resolvent x.g x.u W x.L hz
  have hN : 1 ≤ (2 * k + 2) * p := by nlinarith
  have hMom := fun c => loopFieldK_moment x W hm.1 hu1 a hN hcr c
  set w : ℝ := 10 * (k : ℝ) ^ 2 * B ^ 2 * (gammaG x.g * W) with hwdef
  have hw0 : 0 ≤ w := by positivity
  have hK1 : ∀ (c : Fin x.L) (ω : Ω W x.L), 1 ≤ loopFieldK W x a c ω := fun c ω =>
    loopFieldK_ge W x a c ω
  have hf0 : ∀ (c : Fin x.L) (ω : Ω W x.L), 0 ≤ loopFieldK W x a c ω ^ (2 * k + 2) :=
    fun c ω => pow_nonneg (by linarith [hK1 c ω]) _
  have hfi : ∀ c : Fin x.L, Integrable (fun ω => (loopFieldK W x a c ω ^ (2 * k + 2)) ^ p)
      (μ W x.L) ∧ ∫ ω, (loopFieldK W x a c ω ^ (2 * k + 2)) ^ p ∂(μ W x.L) ≤
        2 ^ ((2 * k + 2) * p - 1) *
          (1 + (((k + 1) * (k + 1) : ℕ) : ℝ) ^ ((2 * k + 2) * p) * Bc) := by
    intro c
    have e : ∀ ω, (loopFieldK W x a c ω ^ (2 * k + 2)) ^ p =
        loopFieldK W x a c ω ^ ((2 * k + 2) * p) := fun ω => (pow_mul _ _ _).symm
    simp only [e]
    exact ⟨(hMom c).2.1, (hMom c).2.2⟩
  have hsumw : ∑ _c : Fin x.L, w = (x.L : ℝ) * w := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hG : ∀ (ω : Ω W x.L) (c : Fin x.L) (p q : Fin x.L × Fin W),
      p.1 ∈ loopFieldLab a c → q.1 ∈ loopFieldLab a c →
      ‖resolventMat (flowH x.g W x.L x.u ω) (zChar x.g x.E (mRoot x.g x.L x.E) x.u) p q‖ ≤
        loopFieldK W x a c ω := fun ω c p q hp hq => loopFieldK_entry W x a c ω hp hq
  constructor
  · -- the generator
    have heq : ∀ ω : Ω W x.L, blockGen W x.L (gammaG x.g)
        (fun r N => resLoop x.g x.E (mRoot x.g x.L x.E) a σ r N -
          primLoop x.g W x.L x.E (mRoot x.g x.L x.E) r a σ) x.u (flowH x.g W x.L x.u ω) =
        lightW x.g x.E (mRoot x.g x.L x.E) a σ x.u (flowH x.g W x.L x.u ω) +
          ((gammaG x.g * W : ℝ) : ℂ) *
            cutErrSum (fun n b τ => primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u (k := n) b τ)
              (errFam x.g x.E (mRoot x.g x.L x.E)
                (fun n b τ => primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u (k := n) b τ) x.u
                (flowH x.g W x.L x.u ω)) a σ := fun ω =>
      blockGen_errorLoop x.g x.E (mRoot x.g x.L x.E) hm.1 hu1
        (flowH_isHermitian x.g W x.L x.u ω)
        (fun r n b τ => primLoop x.g W x.L x.E (mRoot x.g x.L x.E) r (k := n) b τ)
        (loopField_primDeriv x.g W x.L hW hL x.E _ hm x.u ⟨hu0, hu1⟩) a σ
    have hcont := loopField_gen_expr_continuous (W := W) x.g x.E (mRoot x.g x.L x.E) x.u a σ
      (M := fun ω => flowH x.g W x.L x.u ω) hGc
    have hQm : AEStronglyMeasurable (fun ω => ‖blockGen W x.L (gammaG x.g)
        (fun r N => resLoop x.g x.E (mRoot x.g x.L x.E) a σ r N -
          primLoop x.g W x.L x.E (mRoot x.g x.L x.E) r a σ) x.u
        (flowH x.g W x.L x.u ω)‖) (μ W x.L) := by
      simp only [heq]
      exact hcont.norm.aestronglyMeasurable
    have h := loopField_wsum_moment (μ W x.L) (fun _ : Fin x.L => w) (fun _ => hw0)
      (fun c ω => loopFieldK W x a c ω ^ (2 * k + 2)) hf0 hp hfi _ hQm
      (fun ω => norm_nonneg _) (fun ω => by
        rw [heq]
        exact loopField_gen_pointwise x.g x.E (mRoot x.g x.L x.E) hW x.u _ a σ hB hmB hpr
          (loopFieldLab a) (fun c i => loopFieldLab_a a c i) (fun c => loopFieldLab_c a c)
          (fun c => loopFieldK W x a c ω) (fun c => hK1 c ω) (hG ω))
    rw [hsumw] at h
    exact h
  · -- the bracket
    have heq : ∀ ω : Ω W x.L, blockGamma W x.L (gammaG x.g)
        (resLoop x.g x.E (mRoot x.g x.L x.E) a σ x.u)
        (resLoop x.g x.E (mRoot x.g x.L x.E) a σ x.u) (flowH x.g W x.L x.u ω) =
        ((gammaG x.g / W : ℝ) : ℂ) * ∑ c : Fin x.L, ∑ i : Fin k, ∑ j : Fin k,
          (((W : ℂ) • blockE W x.L c) * loopB (resolventMat (flowH x.g W x.L x.u ω)
            (zChar x.g x.E (mRoot x.g x.L x.E) x.u)) a σ i * ((W : ℂ) • blockE W x.L c) *
            (loopB (resolventMat (flowH x.g W x.L x.u ω)
              (zChar x.g x.E (mRoot x.g x.L x.E) x.u)) a σ j)ᴴ).trace := fun ω =>
      blockGamma_loopTr x.g x.E (mRoot x.g x.L x.E) hm.1 hu1
        (flowH_isHermitian x.g W x.L x.u ω) a σ a σ
    have hcont := loopField_gamma_expr_continuous (W := W) x.g x.E (mRoot x.g x.L x.E) x.u a σ
      (M := fun ω => flowH x.g W x.L x.u ω) hGc
    have hQm : AEStronglyMeasurable (fun ω => ‖blockGamma W x.L (gammaG x.g)
        (resLoop x.g x.E (mRoot x.g x.L x.E) a σ x.u)
        (resLoop x.g x.E (mRoot x.g x.L x.E) a σ x.u) (flowH x.g W x.L x.u ω)‖) (μ W x.L) := by
      simp only [heq]
      exact hcont.norm.aestronglyMeasurable
    have h := loopField_wsum_moment (μ W x.L) (fun _ : Fin x.L => w) (fun _ => hw0)
      (fun c ω => loopFieldK W x a c ω ^ (2 * k + 2)) hf0 hp hfi _ hQm
      (fun ω => norm_nonneg _) (fun ω => by
        refine (loopField_gamma_pointwise x.g x.E (mRoot x.g x.L x.E) hm.1 hW hu1
          (flowH_isHermitian x.g W x.L x.u ω) a σ
          (loopFieldLab a) (fun c i => loopFieldLab_a a c i) (fun c => loopFieldLab_c a c)
          (fun c => loopFieldK W x a c ω) (fun c => hK1 c ω) (hG ω)).trans ?_
        refine Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_right ?_ (hf0 c ω)
        have hB2 : 1 ≤ B ^ 2 := one_le_pow₀ hB
        have hk0 : 0 ≤ (k : ℝ) ^ 2 * (gammaG x.g * W) := by positivity
        simp only [hwdef]
        nlinarith)
    rw [hsumw] at h
    exact h

end PointMoment

/-! ### The large-coupling family -/

section Family

/-- A primitive loop of length one is `m^σ`. -/
private lemma loopField_primLoop_one (g : ℝ) (W L : ℕ) (E : ℝ) (m : ℂ) (t : ℝ)
    (a : Fin 1 → Fin L) (σ : Fin 1 → Bool) : ‖primLoop g W L E m t a σ‖ = ‖m‖ := by
  unfold primLoop primK primF
  cases h : σ 0 <;> simp [h]

/-- `ζ_t ≤ 1` on the large-coupling family: `g ≥ 1`, `L ≥ g²`, `W ≥ 2`, `t ∈ [0, 1/2]`. -/
private lemma loopField_zeta_le {g : ℝ} (hg : 1 ≤ g) {W L : ℕ} (hW : 2 ≤ W)
    (hL : g ^ 2 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    0 ≤ zetaProp g W L t ∧ zetaProp g W L t ≤ 1 := by
  have hγ : gammaG g = (g ^ 2)⁻¹ := by unfold gammaG; rw [max_eq_right hg]
  have hg0 : 0 < g := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hℓ : g ^ 2 ≤ ellProp g L t := by
    unfold ellProp
    refine le_min hL ?_
    have hs : Real.sqrt (gammaG g * (1 - t)) ≤ g⁻¹ := by
      rw [show g⁻¹ = Real.sqrt ((g ^ 2)⁻¹) by rw [Real.sqrt_inv, Real.sqrt_sq hg0.le]]
      apply Real.sqrt_le_sqrt
      rw [hγ]
      have : 0 < (g ^ 2)⁻¹ := by positivity
      nlinarith
    have hs0 : 0 < Real.sqrt (gammaG g * (1 - t)) := Real.sqrt_pos.2 (by rw [hγ]; positivity)
    have : g ^ 2 ≤ g / Real.sqrt (gammaG g * (1 - t)) := by
      rw [le_div_iff₀ hs0]
      calc g ^ 2 * Real.sqrt (gammaG g * (1 - t)) ≤ g ^ 2 * g⁻¹ :=
            mul_le_mul_of_nonneg_left hs (by positivity)
        _ = g := by field_simp
    linarith
  have hX : 1 ≤ (W : ℝ) * ellProp g L t * (1 - t) * gammaG g := by
    rw [hγ]
    have hW2 : (2 : ℝ) ≤ W := by exact_mod_cast hW
    have hg2 : 0 < g ^ 2 := by positivity
    have hℓ0 : 0 ≤ ellProp g L t := by linarith
    have h1 : 2 * g ^ 2 ≤ (W : ℝ) * ellProp g L t := mul_le_mul hW2 hℓ (by positivity) (by linarith)
    have h2 : 2 * g ^ 2 * (1 / 2) ≤ (W : ℝ) * ellProp g L t * (1 - t) :=
      mul_le_mul h1 (by linarith) (by norm_num) (by positivity)
    calc (1 : ℝ) = 2 * g ^ 2 * (1 / 2) * (g ^ 2)⁻¹ := by field_simp
      _ ≤ (W : ℝ) * ellProp g L t * (1 - t) * (g ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
  unfold zetaProp
  exact ⟨inv_nonneg.2 (by linarith), inv_le_one_of_one_le₀ hX⟩

/-- The primitive loops of lengths `2, …, k` are bounded on the large-coupling family where
`ζ_t ≤ 1` (Lemma 5.2 [fo:lem:deterministic](b), (5.20) [fo:eq:primitivebound]), with the
coupling threshold depending on `κ` only. -/
private lemma loopField_prim_uniform (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ : ℝ, 1 ≤ Cκ ∧ ∀ k : ℕ, ∃ Cs C' : ℝ, 0 < Cs ∧ 1 ≤ C' ∧
      ∀ W : ℕ, 3 ≤ W → ∀ g : ℝ, Cκ ≤ g → ∀ L : ℕ, 3 ≤ L → Cs * g ^ 2 * Real.log W ≤ L →
      ∀ E : ℝ, |E| ≤ 2 - κ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m →
      ∀ t : ℝ, 0 ≤ t → (W : ℝ) ^ (-3 : ℝ) ≤ 1 - t → 0 ≤ zetaProp g W L t →
      zetaProp g W L t ≤ 1 → ∀ n : ℕ, 2 ≤ n → n ≤ k →
      ∀ (a : Fin n → Fin L) (σ : Fin n → Bool), ‖primLoop g W L E m t a σ‖ ≤ C' := by
  obtain ⟨Cκ, hCκ, H⟩ := primLoop_large' κ hκ hκ2
  refine ⟨Cκ, hCκ, fun k => ?_⟩
  induction k with
  | zero =>
    exact ⟨1, 1, one_pos, le_rfl, fun W _ g _ L _ _ E _ m _ t _ _ _ _ n hn2 hn0 => by omega⟩
  | succ k ih =>
    obtain ⟨Cs, C', hCs, hC', Hk⟩ := ih
    by_cases hk : 2 ≤ k + 1
    · obtain ⟨Cs1, C1, hCs1, hC1, H1⟩ := H (k + 1) hk
      refine ⟨max Cs Cs1, max C' C1, lt_max_of_lt_left hCs, le_max_of_le_left hC', ?_⟩
      intro W hW g hg L hL hCsL E hE m hm t ht0 ht hz0 hz1 n hn2 hnk a σ
      have hlog : 0 ≤ Real.log W := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ W))
      have hg2 : 0 ≤ g ^ 2 := sq_nonneg g
      have hCsL' : ∀ c, c ≤ max Cs Cs1 → c * g ^ 2 * Real.log W ≤ L := fun c hc =>
        le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hg2) hlog) hCsL
      rcases (show n ≤ k ∨ n = k + 1 by omega) with h | rfl
      · exact (Hk W hW g hg L hL (hCsL' Cs (le_max_left _ _)) E hE m hm t ht0 ht hz0 hz1 n hn2 h
          a σ).trans (le_max_left _ _)
      · have := H1 W hW g hg L hL (hCsL' Cs1 (le_max_right _ _)) E hE m hm t ht0 ht a σ
        calc ‖primLoop g W L E m t a σ‖ ≤ C1 * zetaProp g W L t ^ (k + 1 - 1) := this
          _ ≤ C1 * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hz0 hz1) hC1.le
          _ ≤ max C' C1 := by rw [mul_one]; exact le_max_right _ _
    · exact ⟨Cs, C', hCs, hC', fun W hW g hg L hL hCsL E hE m hm t ht0 ht hz0 hz1 n hn2 hnk =>
        Hk W hW g hg L hL hCsL E hE m hm t ht0 ht hz0 hz1 n hn2 (by omega)⟩

/-- `W^{3p}` as a natural power. -/
private lemma loopField_rpow {W : ℝ} (hW : 0 ≤ W) (p : ℕ) : W ^ ((3 : ℝ) * p) = (W ^ 3) ^ p := by
  rw [Real.rpow_mul hW, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    Real.rpow_natCast]

/-- The inputs on the range of Lemma 5.6 [fo:prop:inputs]: the root, `|m| ≤ B`, the primitive
loops of lengths `1, …, k` at most `B`, `γ_g L ≤ C_V W²`, and the block-resolvent moments of order
`N` (Lemma 5.5 [fo:lem:resolvent-moments]), with `B` depending on `κ` and `k` only. -/
private lemma loopField_setup (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ₀ : ℝ, 1 ≤ Cκ₀ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      ∀ k : ℕ, ∃ B : ℝ, 1 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ∃ Bc : ℝ, 0 ≤ Bc ∧ ∃ W₀ : ℕ,
        ∀ W : ℕ, W₀ ≤ W → ∀ x ∈ initLarge κ Cκ CV ρ W,
          1 ≤ W ∧ 3 ≤ x.L ∧ IsDysonRootV (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E) ∧
          -1 < x.u ∧ x.u < 1 ∧ ‖mRoot x.g x.L x.E‖ ≤ B ∧
          (∀ n : ℕ, 1 ≤ n → n ≤ k → ∀ (b : Fin n → Fin x.L) (τ : Fin n → Bool),
            ‖primLoop x.g W x.L x.E (mRoot x.g x.L x.E) x.u b τ‖ ≤ B) ∧
          gammaG x.g * x.L ≤ CV * (W : ℝ) ^ 2 ∧
          (∀ y z : Fin x.L,
            Integrable (fun ω => ‖blockOf (flowG W x ω) y z‖ ^ N) (μ W x.L) ∧
              ∫ ω, ‖blockOf (flowG W x ω) y z‖ ^ N ∂(μ W x.L) ≤ Bc) := by
  obtain ⟨Cκl, Rl, cl, Cl, hCκl, hRl, hcl, hCl, Hl⟩ := large_periodic_comparison κ hκ hκ2
  set C : ℝ := max 1 Cl with hCdef
  have hC1 : 1 ≤ C := le_max_left _ _
  obtain ⟨Cκr, hCκr, Hr⟩ := resolvent_moments_vert κ C hκ hκ2 hC1
  obtain ⟨Cκp, hCκp, Hp⟩ := loopField_prim_uniform κ hκ hκ2
  refine ⟨max (max Cκl Cκr) Cκp, le_trans hCκl (le_trans (le_max_left _ _) (le_max_left _ _)),
    fun Cκ hCκ ρ hρ k => ?_⟩
  obtain ⟨Cs, C', hCs, hC', HP⟩ := Hp k
  refine ⟨max C C', le_trans hC1 (le_max_left _ _), fun N hN => ?_⟩
  obtain ⟨Bc, hBc, HBc⟩ := Hr N hN
  refine ⟨Bc, hBc.le, ?_⟩
  set Rst : ℝ := max (max Rl 4) Cs with hRst
  have hev : ∀ᶠ W : ℕ in atTop, 4 * N ≤ W ∧ 3 ≤ W ∧ Rst ≤ ρ W ∧ 1 ≤ Real.log W :=
    (eventually_ge_atTop (4 * N)).and ((eventually_ge_atTop 3).and
      ((hρ.eventually_ge_atTop Rst).and
        ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1)))
  obtain ⟨W₀, HW₀⟩ := eventually_atTop.1 hev
  refine ⟨W₀, fun W hW x hx => ?_⟩
  obtain ⟨h4N, hW3, hρW, hlog⟩ := HW₀ W hW
  obtain ⟨hgC, hE, hLlog, hLV, hu0, hu1⟩ := hx
  have hg0' : max (max Cκl Cκr) Cκp ≤ x.g := hCκ.trans hgC
  obtain ⟨⟨hgl, hgr⟩, hgp⟩ : (Cκl ≤ x.g ∧ Cκr ≤ x.g) ∧ Cκp ≤ x.g := by
    simpa only [max_le_iff] using hg0'
  have hg1 : 1 ≤ x.g := hCκl.trans hgl
  have hg0 : 0 < x.g := by linarith
  have hgg : 0 < x.g ^ 2 := by positivity
  have hRst4 : 4 ≤ Rst := le_trans (le_max_right _ _) (le_max_left _ _)
  have hρ0 : 0 ≤ ρ W := by linarith
  have hLR : Rst * x.g ^ 2 ≤ x.L := by
    have h1 : 0 ≤ ρ W * x.g ^ 2 := mul_nonneg hρ0 hgg.le
    calc Rst * x.g ^ 2 ≤ ρ W * x.g ^ 2 := mul_le_mul_of_nonneg_right hρW hgg.le
      _ ≤ ρ W * x.g ^ 2 * Real.log W := le_mul_of_one_le_right h1 hlog
      _ ≤ _ := hLlog
  have hRL : ∀ R' : ℝ, R' ≤ Rst → R' * x.g ^ 2 ≤ x.L := fun R' h =>
    le_trans (mul_le_mul_of_nonneg_right h hgg.le) hLR
  have hRlL := hRL Rl (le_trans (le_max_left _ _) (le_max_left _ _))
  have h4L := hRL 4 hRst4
  have hCsL : Cs * x.g ^ 2 * Real.log W ≤ x.L := by
    have hCsρ : Cs ≤ ρ W := le_trans (le_max_right _ _) hρW
    calc Cs * x.g ^ 2 * Real.log W ≤ ρ W * x.g ^ 2 * Real.log W := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCsρ hgg.le) ?_
          linarith
      _ ≤ _ := hLlog
  have hL3 : 3 ≤ x.L := by
    have h1 : (1 : ℝ) ≤ x.g ^ 2 := one_le_pow₀ hg1
    have : (3 : ℝ) ≤ x.L := by linarith
    exact_mod_cast this
  have hW1 : 1 ≤ W := by omega
  -- the root
  obtain ⟨m, -, hroot, -, hmim, hmC, -⟩ := Hl x.g hgl x.L hRlL x.E hE
  have hb0 : 0 ≤ hopB x.g := by
    unfold hopB; rw [max_eq_right hg1, div_self hg0.ne']; norm_num
  have hmR : mRoot x.g x.L x.E = m :=
    (mRootV_spec (hopB x.g) (gammaG x.g) hb0 (loopField_gammaG_pos _) x.L hL3
      (x.E : ℂ) (by simp)).2 m hroot
  have hroot' : IsDysonRootV (hopB x.g) (gammaG x.g) x.L x.E (mRoot x.g x.L x.E) := by
    rw [hmR]; exact hroot
  have hmC' : ‖mRoot x.g x.L x.E‖ ≤ C := by rw [hmR]; exact hmC.trans (le_max_right _ _)
  have hmim' : C⁻¹ ≤ (mRoot x.g x.L x.E).im := by
    rw [hmR]; exact le_trans (inv_anti₀ hCl (le_max_right _ _)) hmim
  -- `ζ_u ≤ 1` and `W^{-3} ≤ 1 - u`
  have hζ := loopField_zeta_le hg1 (W := W) (L := x.L) (by omega) (by linarith) hu0 hu1
  have hWt : (W : ℝ) ^ (-3 : ℝ) ≤ 1 - x.u := by
    have hW3r : (3 : ℝ) ≤ W := by exact_mod_cast hW3
    rw [Real.rpow_neg (by positivity), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    have h27 : (2 : ℝ) ≤ (W : ℝ) ^ 3 := by nlinarith
    have : ((W : ℝ) ^ 3)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
    linarith
  refine ⟨hW1, hL3, hroot', by linarith, by linarith, hmC'.trans (le_max_left _ _), ?_, ?_, ?_⟩
  · intro n hn1 hnk b τ
    rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
    · rw [loopField_primLoop_one]
      exact hmC'.trans (le_max_left _ _)
    · exact (HP W hW3 x.g hgp x.L hL3 hCsL x.E hE _ hroot' x.u hu0 hWt hζ.1 hζ.2 n hn2 hnk
        b τ).trans (le_max_right _ _)
  · have hγ : gammaG x.g = (x.g ^ 2)⁻¹ := by unfold gammaG; rw [max_eq_right hg1]
    rw [hγ, inv_mul_le_iff₀ hgg]
    calc (x.L : ℝ) ≤ CV * x.g ^ 2 * (W : ℝ) ^ 2 := hLV
      _ = x.g ^ 2 * (CV * (W : ℝ) ^ 2) := by ring
  · intro y z
    have h := HBc W h4N (x, etaChar x.g (mRoot x.g x.L x.E) x.u) hgr h4L hE hroot' hmC' hmim'
      hu0 hu1 le_rfl y z
    simp only [loopField_segG_eq] at h
    exact h

end Family

/-- Crude moments, uniform in `g`, of the generator (5.4) [fo:eq:ito] of a loop error and of the
bracket (5.9) [gc:eq:bracket] of a loop at each point of the range of Lemma 5.6
[fo:prop:inputs]: `E|𝒢D_k|^p ≤ C_p W^{C_1 p}` and `E|Γ(ℒ_k, ℒ_k)|^p ≤ C_p W^{C_1 p}`. -/
theorem loops_gen_crude (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) :
    ∃ Cκ₀ : ℝ, 1 ≤ Cκ₀ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      ∀ k : ℕ, 1 ≤ k → ∃ C₁ : ℝ, ∀ p : ℕ, 1 ≤ p → ∃ Cp : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        ∀ x ∈ initLarge κ Cκ CV ρ W, ∀ (a : Fin k → Fin x.L) (σ : Fin k → Bool),
          (Integrable (fun ω => ‖blockGen W x.L (gammaG x.g)
              (fun r N => resLoop x.g x.E (mRoot x.g x.L x.E) a σ r N -
                primLoop x.g W x.L x.E (mRoot x.g x.L x.E) r a σ) x.u
              (flowH x.g W x.L x.u ω)‖ ^ p) (μ W x.L) ∧
            ∫ ω, ‖blockGen W x.L (gammaG x.g)
              (fun r N => resLoop x.g x.E (mRoot x.g x.L x.E) a σ r N -
                primLoop x.g W x.L x.E (mRoot x.g x.L x.E) r a σ) x.u
              (flowH x.g W x.L x.u ω)‖ ^ p ∂(μ W x.L) ≤ Cp * (W : ℝ) ^ (C₁ * p)) ∧
          (Integrable (fun ω => ‖blockGamma W x.L (gammaG x.g)
              (resLoop x.g x.E (mRoot x.g x.L x.E) a σ x.u)
              (resLoop x.g x.E (mRoot x.g x.L x.E) a σ x.u) (flowH x.g W x.L x.u ω)‖ ^ p)
              (μ W x.L) ∧
            ∫ ω, ‖blockGamma W x.L (gammaG x.g)
              (resLoop x.g x.E (mRoot x.g x.L x.E) a σ x.u)
              (resLoop x.g x.E (mRoot x.g x.L x.E) a σ x.u) (flowH x.g W x.L x.u ω)‖ ^ p
              ∂(μ W x.L) ≤ Cp * (W : ℝ) ^ (C₁ * p)) := by
  -- `hCV` is not needed: `C_V > 0` follows from `1 ≤ L ≤ C_V g² W²` on the family.
  have _ := hCV
  obtain ⟨Cκ₀, hCκ₀, H⟩ := loopField_setup κ CV hκ hκ2
  refine ⟨Cκ₀, hCκ₀, fun Cκ hCκ ρ hρ k hk => ?_⟩
  obtain ⟨B, hB, HB⟩ := H Cκ hCκ ρ hρ k
  refine ⟨3, fun p hp => ?_⟩
  obtain ⟨Bc, hBc, W₀, HW⟩ := HB ((2 * k + 2) * p) (by nlinarith)
  set Bk : ℝ := 2 ^ ((2 * k + 2) * p - 1) *
    (1 + (((k + 1) * (k + 1) : ℕ) : ℝ) ^ ((2 * k + 2) * p) * Bc) with hBkdef
  have hBk0 : 0 ≤ Bk := by positivity
  set A : ℝ := 10 * (k : ℝ) ^ 2 * B ^ 2 with hAdef
  have hA0 : 0 ≤ A := by positivity
  refine ⟨(A * CV) ^ p * Bk, W₀, fun W hW x hx a σ => ?_⟩
  obtain ⟨hW1, hL3, hroot, hu0, hu1, hmB, hpr, hγL, hcr⟩ := HW W hW x hx
  have hpt := loopField_gen_point x W hW1 hL3 hroot hu0 hu1 hB hmB
    (fun n hn2 hnk => hpr n (by omega) hnk) hp hcr a σ
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have hγ := loopField_gammaG_pos x.g
  have hbound : ((x.L : ℝ) * (A * (gammaG x.g * W))) ^ p * Bk ≤
      (A * CV) ^ p * Bk * (W : ℝ) ^ ((3 : ℝ) * p) := by
    rw [loopField_rpow hW0]
    have h1 : (x.L : ℝ) * (A * (gammaG x.g * W)) ≤ (A * CV) * (W : ℝ) ^ 3 := by
      calc (x.L : ℝ) * (A * (gammaG x.g * W)) = A * (gammaG x.g * x.L) * W := by ring
        _ ≤ A * (CV * (W : ℝ) ^ 2) * W := by gcongr
        _ = (A * CV) * (W : ℝ) ^ 3 := by ring
    calc ((x.L : ℝ) * (A * (gammaG x.g * W))) ^ p * Bk ≤ ((A * CV) * (W : ℝ) ^ 3) ^ p * Bk :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h1 p) hBk0
      _ = (A * CV) ^ p * Bk * ((W : ℝ) ^ 3) ^ p := by rw [mul_pow]; ring
  exact ⟨⟨hpt.1.1, hpt.1.2.trans hbound⟩, ⟨hpt.2.1, hpt.2.2.trans hbound⟩⟩

end LSBA
