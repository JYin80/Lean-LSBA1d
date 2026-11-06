import LSBA.Transfer.OneStep
import LSBA.Gauss.BlockSplit
import LSBA.Gauss.Net

/-!
# Transfer moments on scattering-length windows

Lemma 7.2 [uvs:lem:transfer-moments], (7.1) [uvs:eq:transfer-moments]: tail bounds and maximal
moments of products of transfer matrices and of their inverses along any injective block
sequence, at large coupling, uniformly in the coupling, the length `n ≤ C₀g²` and the spectral
parameter.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Vector moments, resampling of one block, and products along a block sequence -/

/-- The vector moment `‖x‖^W = (∑ ‖x_p‖²)^{W/2}` on `ℂ^{2W}`, as in (7.2)
[uvs:eq:one-step-moment]. -/
private def momentsN {W : ℕ} (x : Fin 2 × Fin W → ℂ) : ℝ := (∑ p, ‖x p‖ ^ 2) ^ ((W : ℝ) / 2)

private lemma momentsN_nonneg {W : ℕ} (x : Fin 2 × Fin W → ℂ) : 0 ≤ momentsN x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) _

private lemma continuous_momentsN {W : ℕ} :
    Continuous (momentsN : (Fin 2 × Fin W → ℂ) → ℝ) :=
  (continuous_finsetSum _ fun p _ => (continuous_norm.comp (continuous_apply p)).pow 2).rpow_const
    fun _ => Or.inr (by positivity)

/-- `ω` with the coordinates of block `a` replaced by those of `ω'`. -/
private def momentsMix {W L : ℕ} (a : Fin L) (ω ω' : Ω W L) : Ω W L :=
  fun x => if x.1 = a then ω' x else ω x

private lemma measurable_momentsMix {W L : ℕ} (a : Fin L) :
    Measurable (fun q : Ω W L × Ω W L => momentsMix a q.1 q.2) := by
  refine Measurable.of_eval fun x => ?_
  by_cases h : x.1 = a
  · simp only [momentsMix, h, ite_true]
    exact (measurable_pi_apply x).comp measurable_snd
  · simp only [momentsMix, h, ite_false]
    exact (measurable_pi_apply x).comp measurable_fst

/-- Resampling block `a` from an independent copy preserves `μ W L` (the product structure of
(1.2) [eq:covariance]). -/
private lemma map_momentsMix {W L : ℕ} (a : Fin L) :
    ((μ W L).prod (μ W L)).map (fun q => momentsMix a q.1 q.2) = μ W L := by
  have hμ : μ W L = Measure.pi fun _ => gaussianReal 0 1 := rfl
  symm
  conv_lhs => rw [hμ]
  refine Measure.pi_eq fun S hS => ?_
  rw [Measure.map_apply (measurable_momentsMix a) (MeasurableSet.univ_pi hS)]
  have hpre : (fun q : Ω W L × Ω W L => momentsMix a q.1 q.2) ⁻¹' Set.univ.pi S =
      Set.univ.pi (fun x => if x.1 = a then Set.univ else S x) ×ˢ
        Set.univ.pi (fun x => if x.1 = a then S x else Set.univ) := by
    ext q
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod, momentsMix]
    constructor
    · intro h
      refine ⟨fun x => ?_, fun x => ?_⟩ <;> by_cases hx : x.1 = a <;> simp [hx] <;> simpa [hx] using h x
    · rintro ⟨h1, h2⟩ x
      by_cases hx : x.1 = a
      · simpa [hx] using h2 x
      · simpa [hx] using h1 x
  rw [hpre, Measure.prod_prod, hμ, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  by_cases hx : x.1 = a <;> simp [hx]

private lemma lintegral_momentsMix {W L : ℕ} (a : Fin L) {F : Ω W L → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F ω ∂μ W L = ∫⁻ ω, ∫⁻ ω', F (momentsMix a ω ω') ∂μ W L ∂μ W L := by
  conv_lhs => rw [← map_momentsMix a]
  rw [lintegral_map hF (measurable_momentsMix a),
    lintegral_prod (fun q : Ω W L × Ω W L => F (momentsMix a q.1 q.2))
      (hF.comp (measurable_momentsMix a)).aemeasurable]

private lemma gueBlock_momentsMix_of_ne {W L : ℕ} {a b : Fin L} (h : b ≠ a) (ω ω' : Ω W L) :
    gueBlock W L (momentsMix a ω ω') b = gueBlock W L ω b := by
  ext α β
  simp [gueBlock, momentsMix, h]

private lemma gueBlock_momentsMix_self {W L : ℕ} (a : Fin L) (ω ω' : Ω W L) :
    gueBlock W L (momentsMix a ω ω') a = gueBlock W L ω' a := by
  ext α β
  simp [gueBlock, momentsMix]

private lemma continuous_gueBlock {W L : ℕ} (b : Fin L) :
    Continuous fun ω : Ω W L => gueBlock W L ω b := by
  refine continuous_matrix fun α β => ?_
  simp only [gueBlock, Matrix.of_apply]
  split_ifs <;> fun_prop

/-- Products `R_0 = 1`, `R_{j+1} = F(V_{s j}) R_j` of a block function `F` along `s`. -/
private def momentsProd {W L : ℕ}
    (F : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (s : ℕ → Fin L) (ω : Ω W L) : ℕ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ
  | 0 => 1
  | j + 1 => F (gueBlock W L ω (s j)) * momentsProd F s ω j

private lemma continuous_momentsProd {W L : ℕ}
    {F : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hF : Continuous F) (s : ℕ → Fin L) (j : ℕ) :
    Continuous fun ω : Ω W L => momentsProd F s ω j := by
  induction j with
  | zero => exact continuous_const
  | succ j ih => exact (hF.comp (continuous_gueBlock (s j))).mul ih

private lemma momentsProd_momentsMix {W L : ℕ}
    {F : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {s : ℕ → Fin L} {k : ℕ} (hs : ∀ i < k, s i ≠ s k) (ω ω' : Ω W L) :
    ∀ j ≤ k, momentsProd F s (momentsMix (s k) ω ω') j = momentsProd F s ω j := by
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [momentsProd]
    rw [ih (by omega), gueBlock_momentsMix_of_ne (hs j (by omega))]

/-! ### First passage -/

/-- First-passage maximal bound: if the moments `Y` grow by at most `r` per step on the event
that no earlier value exceeded `c`, then `c · ν(max_{j ≤ n} Y_j > c) ≤ r^n ∫ Y_0`
(maximal inequality in the proof of Lemma 7.2 [uvs:lem:transfer-moments]). -/
private lemma moments_first_passage {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (Y : ℕ → α → ℝ≥0∞) (hY : ∀ j, Measurable (Y j)) (c r : ℝ≥0∞) (hr : 1 ≤ r) (n : ℕ)
    (hstep : ∀ k < n, ∫⁻ ω in {ω | ∀ j ≤ k, Y j ω ≤ c}, Y (k + 1) ω ∂ν ≤
      r * ∫⁻ ω in {ω | ∀ j ≤ k, Y j ω ≤ c}, Y k ω ∂ν) :
    c * ν {ω | ∃ j ≤ n, c < Y j ω} ≤ r ^ n * ∫⁻ ω, Y 0 ω ∂ν := by
  have hA : ∀ k, MeasurableSet {ω | ∀ j ≤ k, Y j ω ≤ c} := fun k => by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_le (hY j) measurable_const
  have hT : ∀ k, MeasurableSet {ω | c < Y k ω} := fun k => measurableSet_lt measurable_const (hY k)
  have key : ∀ k ≤ n, c * ν {ω | ∃ j ≤ k, c < Y j ω} +
      ∫⁻ ω in {ω | ∀ j ≤ k, Y j ω ≤ c}, Y k ω ∂ν ≤ r ^ k * ∫⁻ ω, Y 0 ω ∂ν := by
    intro k hk
    induction k with
    | zero =>
      have e1 : {ω | ∃ j ≤ 0, c < Y j ω} = {ω | c < Y 0 ω} := by ext; simp
      have e2 : {ω | ∀ j ≤ 0, Y j ω ≤ c} = {ω | c < Y 0 ω}ᶜ := by ext; simp
      rw [e1, e2, pow_zero, one_mul]
      conv_rhs => rw [← lintegral_add_compl (fun ω => Y 0 ω) (hT 0)]
      gcongr
      rw [← setLIntegral_const]
      exact setLIntegral_mono' (hT 0) fun ω hω => le_of_lt hω
    | succ k ih =>
      set A := {ω | ∀ j ≤ k, Y j ω ≤ c}
      set T := {ω | c < Y (k + 1) ω}
      have hB : {ω | ∃ j ≤ k + 1, c < Y j ω} ⊆ {ω | ∃ j ≤ k, c < Y j ω} ∪ (A ∩ T) := by
        rintro ω ⟨j, hj, hlt⟩
        by_cases hω : ∃ j ≤ k, c < Y j ω
        · exact Or.inl hω
        · simp only [not_exists, not_and, not_lt] at hω
          have hjk : j = k + 1 := by
            by_contra hne
            exact absurd hlt (not_lt.mpr (hω j (by omega)))
          subst hjk
          exact Or.inr ⟨hω, hlt⟩
      have hA' : {ω | ∀ j ≤ k + 1, Y j ω ≤ c} ⊆ A \ T := by
        intro ω hω
        exact ⟨fun j hj => hω j (by omega), not_lt.mpr (hω (k + 1) le_rfl)⟩
      have h1 : c * ν {ω | ∃ j ≤ k + 1, c < Y j ω} ≤
          c * ν {ω | ∃ j ≤ k, c < Y j ω} + ∫⁻ ω in A ∩ T, Y (k + 1) ω ∂ν := by
        calc c * ν {ω | ∃ j ≤ k + 1, c < Y j ω}
            ≤ c * (ν {ω | ∃ j ≤ k, c < Y j ω} + ν (A ∩ T)) :=
              by gcongr; exact (measure_mono hB).trans (measure_union_le _ _)
          _ = c * ν {ω | ∃ j ≤ k, c < Y j ω} + c * ν (A ∩ T) := mul_add _ _ _
          _ ≤ _ := by
              gcongr
              rw [← setLIntegral_const]
              exact setLIntegral_mono' ((hA k).inter (hT (k + 1))) fun ω hω => le_of_lt hω.2
      have h2 : ∫⁻ ω in {ω | ∀ j ≤ k + 1, Y j ω ≤ c}, Y (k + 1) ω ∂ν ≤
          ∫⁻ ω in A \ T, Y (k + 1) ω ∂ν := lintegral_mono_set hA'
      calc c * ν {ω | ∃ j ≤ k + 1, c < Y j ω} +
            ∫⁻ ω in {ω | ∀ j ≤ k + 1, Y j ω ≤ c}, Y (k + 1) ω ∂ν
          ≤ (c * ν {ω | ∃ j ≤ k, c < Y j ω} + ∫⁻ ω in A ∩ T, Y (k + 1) ω ∂ν) +
              ∫⁻ ω in A \ T, Y (k + 1) ω ∂ν := add_le_add h1 h2
        _ = c * ν {ω | ∃ j ≤ k, c < Y j ω} + ∫⁻ ω in A, Y (k + 1) ω ∂ν := by
              rw [add_assoc, lintegral_inter_add_sdiff _ _ (hT (k + 1))]
        _ ≤ c * ν {ω | ∃ j ≤ k, c < Y j ω} + r * ∫⁻ ω in A, Y k ω ∂ν :=
              by gcongr; exact hstep k (by omega)
        _ ≤ r * (c * ν {ω | ∃ j ≤ k, c < Y j ω} + ∫⁻ ω in A, Y k ω ∂ν) := by
              rw [mul_add]
              exact add_le_add (le_mul_of_one_le_left' hr) le_rfl
        _ ≤ r * (r ^ k * ∫⁻ ω, Y 0 ω ∂ν) := by gcongr; exact ih (by omega)
        _ = r ^ (k + 1) * ∫⁻ ω, Y 0 ω ∂ν := by rw [pow_succ]; ring
  exact le_trans le_self_add (key n le_rfl)

/-! ### Tails of products along an injective block sequence -/

/-- Maximal tail of `‖R_j v‖^W` for one vector `‖v‖ ≤ 1`, from the one-step bound (7.2)
[uvs:eq:one-step-moment] in test-function form. -/
private lemma moments_vec_tail {W L : ℕ}
    {F : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hF : Continuous F) {a : ℝ} (ha : 0 ≤ a)
    (hstep : ∀ (b : Fin L) (v : Fin 2 × Fin W → ℂ),
      ∫⁻ ω, ENNReal.ofReal (momentsN (F (gueBlock W L ω b) *ᵥ v)) ∂μ W L ≤
        ENNReal.ofReal (Real.exp a * momentsN v))
    {s : ℕ → Fin L} {n : ℕ} (hs : Set.InjOn s (Set.Iio n)) (v : Fin 2 × Fin W → ℂ)
    (hv : ∑ p, ‖v p‖ ^ 2 ≤ 1) {c : ℝ} (hc : 0 < c) :
    μ W L {ω | ∃ j ≤ n, c < momentsN (momentsProd F s ω j *ᵥ v)} ≤
      ENNReal.ofReal (Real.exp a ^ n / c) := by
  set Y : ℕ → Ω W L → ℝ≥0∞ := fun j ω => ENNReal.ofReal (momentsN (momentsProd F s ω j *ᵥ v))
    with hYdef
  have hYm : ∀ j, Measurable (Y j) := fun j =>
    ENNReal.measurable_ofReal.comp (continuous_momentsN.comp
      ((continuous_momentsProd hF s j).matrix_mulVec continuous_const)).measurable
  have hset : {ω | ∃ j ≤ n, c < momentsN (momentsProd F s ω j *ᵥ v)} =
      {ω | ∃ j ≤ n, ENNReal.ofReal c < Y j ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hYdef, ENNReal.ofReal_lt_ofReal_iff']
    constructor
    · rintro ⟨j, hj, h⟩
      exact ⟨j, hj, h, hc.trans h⟩
    · rintro ⟨j, hj, h, -⟩
      exact ⟨j, hj, h⟩
  have hfp := moments_first_passage (μ W L) Y hYm (ENNReal.ofReal c) (ENNReal.ofReal (Real.exp a))
    (by rw [ENNReal.one_le_ofReal]; exact Real.one_le_exp ha) n ?_
  · have h0 : ∫⁻ ω, Y 0 ω ∂μ W L ≤ 1 := by
      have hle : ∀ ω, Y 0 ω ≤ 1 := fun ω => by
        simp only [hYdef, momentsProd, Matrix.one_mulVec]
        rw [ENNReal.ofReal_le_one]
        exact Real.rpow_le_one (Finset.sum_nonneg fun _ _ => sq_nonneg _) hv (by positivity)
      calc ∫⁻ ω, Y 0 ω ∂μ W L ≤ ∫⁻ _, 1 ∂μ W L := lintegral_mono hle
        _ = 1 := by simp
    rw [hset, ENNReal.ofReal_div_of_pos hc,
      ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hc)) (Or.inl ENNReal.ofReal_ne_top),
      mul_comm, ENNReal.ofReal_pow (Real.exp_pos a).le]
    calc _ ≤ _ := hfp
      _ ≤ ENNReal.ofReal (Real.exp a) ^ n * 1 := by gcongr
      _ = _ := mul_one _
  · intro k hk
    set A := {ω | ∀ j ≤ k, Y j ω ≤ ENNReal.ofReal c} with hAdef
    have hAm : MeasurableSet A := by
      simp only [hAdef, Set.ofPred_forall]
      exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
        measurableSet_le (hYm j) measurable_const
    have hsk : ∀ i < k, s i ≠ s k := fun i hi h => by
      have := hs (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega) h
      omega
    have hinv := momentsProd_momentsMix (F := F) hsk
    have hYinv : ∀ ω ω', ∀ j ≤ k, Y j (momentsMix (s k) ω ω') = Y j ω := fun ω ω' j hj => by
      simp only [hYdef, hinv ω ω' j hj]
    have hmemA : ∀ ω ω', momentsMix (s k) ω ω' ∈ A ↔ ω ∈ A := fun ω ω' => by
      simp only [hAdef, Set.mem_ofPred_eq]
      constructor
      · intro h j hj
        rw [← hYinv ω ω' j hj]
        exact h j hj
      · intro h j hj
        rw [hYinv ω ω' j hj]
        exact h j hj
    rw [← lintegral_indicator hAm, ← lintegral_indicator hAm,
      lintegral_momentsMix (s k) ((hYm (k + 1)).indicator hAm),
      ← lintegral_const_mul _ ((hYm k).indicator hAm)]
    refine lintegral_mono fun ω => ?_
    by_cases hω : ω ∈ A
    · have hY1 : ∀ ω', A.indicator (Y (k + 1)) (momentsMix (s k) ω ω') =
          ENNReal.ofReal (momentsN (F (gueBlock W L ω' (s k)) *ᵥ
            (momentsProd F s ω k *ᵥ v))) := fun ω' => by
        rw [Set.indicator_of_mem ((hmemA ω ω').mpr hω)]
        simp only [hYdef, momentsProd, hinv ω ω' k le_rfl, gueBlock_momentsMix_self,
          Matrix.mulVec_mulVec]
      simp only [hY1, Set.indicator_of_mem hω]
      calc _ ≤ ENNReal.ofReal (Real.exp a * momentsN (momentsProd F s ω k *ᵥ v)) :=
            hstep (s k) _
        _ = _ := by rw [ENNReal.ofReal_mul (Real.exp_pos a).le]
    · have hY1 : ∀ ω', A.indicator (Y (k + 1)) (momentsMix (s k) ω ω') = 0 := fun ω' =>
        Set.indicator_of_notMem (fun h => hω ((hmemA ω ω').mp h)) _
      simp only [hY1, lintegral_zero]
      exact bot_le

/-- Maximal operator-norm tail of the products `R_j`, through a `1/2`-net of the unit ball of
`ℂ^{2W}` (proof of (7.3) [uvs:eq:transfer-tail]). -/
private lemma moments_prod_tail {W L : ℕ}
    {F : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hF : Continuous F) {a : ℝ} (ha : 0 ≤ a)
    (hstep : ∀ (b : Fin L) (v : Fin 2 × Fin W → ℂ),
      ∫⁻ ω, ENNReal.ofReal (momentsN (F (gueBlock W L ω b) *ᵥ v)) ∂μ W L ≤
        ENNReal.ofReal (Real.exp a * momentsN v))
    {s : ℕ → Fin L} {n : ℕ} (hs : Set.InjOn s (Set.Iio n)) {u : ℝ} (hu : 0 < u) :
    μ W L {ω | ∃ j ≤ n, u < ‖momentsProd F s ω j‖} ≤
      ENNReal.ofReal (5 ^ (4 * W) * Real.exp a ^ n * (2 / u) ^ W) := by
  rcases Nat.eq_zero_or_pos W with hW | hW
  · refine prob_le_one.trans ?_
    rw [ENNReal.one_le_ofReal, hW]
    simpa using one_le_pow₀ (n := n) (Real.one_le_exp ha)
  obtain ⟨N, hNcard, hNball, hNnet⟩ := exists_half_net (Fin 2 × Fin W)
  have hcard : N.card ≤ 5 ^ (4 * W) := by
    simp only [Fintype.card_prod, Fintype.card_fin] at hNcard
    rwa [show 2 * (2 * W) = 4 * W by ring] at hNcard
  have hsub : {ω | ∃ j ≤ n, u < ‖momentsProd F s ω j‖} ⊆
      ⋃ v ∈ N, {ω | ∃ j ≤ n, (u / 2) ^ W < momentsN (momentsProd F s ω j *ᵥ v)} := by
    rintro ω ⟨j, hj, hlt⟩
    obtain ⟨v, hvN, hv⟩ := hNnet (momentsProd F s ω j)
    refine Set.mem_biUnion hvN ⟨j, hj, ?_⟩
    have h1 : u / 2 < Real.sqrt (∑ i, ‖(momentsProd F s ω j *ᵥ v) i‖ ^ 2) := by linarith
    calc (u / 2) ^ W < Real.sqrt (∑ i, ‖(momentsProd F s ω j *ᵥ v) i‖ ^ 2) ^ W :=
          pow_lt_pow_left₀ h1 (by positivity) hW.ne'
      _ = _ := by
        rw [momentsN, Real.sqrt_eq_rpow,
          ← Real.rpow_mul_natCast (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
        congr 1
        ring
  have hpos : 0 < (u / 2) ^ W := by positivity
  calc μ W L {ω | ∃ j ≤ n, u < ‖momentsProd F s ω j‖}
      ≤ μ W L (⋃ v ∈ N, {ω | ∃ j ≤ n, (u / 2) ^ W < momentsN (momentsProd F s ω j *ᵥ v)}) :=
        measure_mono hsub
    _ ≤ ∑ v ∈ N, μ W L {ω | ∃ j ≤ n, (u / 2) ^ W < momentsN (momentsProd F s ω j *ᵥ v)} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _v ∈ N, ENNReal.ofReal (Real.exp a ^ n / (u / 2) ^ W) :=
        Finset.sum_le_sum fun v hv => moments_vec_tail hF ha hstep hs v (hNball v hv) hpos
    _ = (N.card : ℝ≥0∞) * ENNReal.ofReal (Real.exp a ^ n / (u / 2) ^ W) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((5 ^ (4 * W) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp a ^ n / (u / 2) ^ W) := by
        gcongr
    _ = ENNReal.ofReal (5 ^ (4 * W) * Real.exp a ^ n * (2 / u) ^ W) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [div_pow, div_pow]
        push_cast
        field_simp

/-! ### Conjugation by `S_E` -/

private lemma moments_conj_mul {W : ℕ} {S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hS : IsUnit S.det) (T P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    S⁻¹ * (T * P) * S = (S⁻¹ * T * S) * (S⁻¹ * P * S) := by
  have h1 : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv _ hS
  calc S⁻¹ * (T * P) * S = S⁻¹ * T * (S * S⁻¹) * P * S := by
        rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

private lemma moments_norm_le {W : ℕ} {S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hS : IsUnit S.det) (P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ‖P‖ ≤ ‖S‖ * ‖S⁻¹‖ * ‖S⁻¹ * P * S‖ := by
  have h1 : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv _ hS
  have hP : P = S * (S⁻¹ * P * S) * S⁻¹ := by
    calc P = (S * S⁻¹) * P * (S * S⁻¹) := by rw [h1, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  calc ‖P‖ = ‖S * (S⁻¹ * P * S) * S⁻¹‖ := congrArg _ hP
    _ ≤ ‖S‖ * ‖S⁻¹ * P * S‖ * ‖S⁻¹‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = _ := by ring

private lemma moments_inv_conj {W : ℕ} {S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hS : IsUnit S.det) (P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    S⁻¹ * P⁻¹ * S = (S⁻¹ * P * S)⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hS,
    Matrix.mul_assoc]

private lemma continuous_kronecker_left {W : ℕ} (P : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous fun V : Matrix (Fin W) (Fin W) ℂ => P ⊗ₖ V := by
  refine continuous_matrix fun i j => ?_
  simp only [Matrix.kroneckerMap_apply]
  exact continuous_const.mul (continuous_id.matrix_elem i.2 j.2)

private lemma continuous_transferMat' {W : ℕ} (g : ℝ) (z : ℂ) :
    Continuous fun V : Matrix (Fin W) (Fin W) ℂ => transferMat g z V := by
  unfold transferMat
  exact continuous_const.sub ((continuous_const_smul _).comp (continuous_kronecker_left _))

private lemma continuous_transferInv' {W : ℕ} (g : ℝ) (z : ℂ) :
    Continuous fun V : Matrix (Fin W) (Fin W) ℂ => transferInv g z V := by
  unfold transferInv
  exact continuous_const.sub ((continuous_const_smul _).comp (continuous_kronecker_left _))

private lemma continuous_transferConj' {W : ℕ} (g E η : ℝ) (c : ℂ) :
    Continuous fun V : Matrix (Fin W) (Fin W) ℂ => transferConj g E η (c • V) := by
  unfold transferConj
  exact (continuous_const.mul ((continuous_transferMat' g _).comp (continuous_const_smul c))).mul
    continuous_const

private lemma continuous_inv_transferConj {W : ℕ} {E : ℝ} (hE : |E| < 2) (g η : ℝ) (c : ℂ) :
    Continuous fun V : Matrix (Fin W) (Fin W) ℂ => ((transferConj g E η (c • V))⁻¹)ᴴ := by
  have hS : IsUnit (freeConj W E).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_freeConj W hE)
  have heq : ∀ V : Matrix (Fin W) (Fin W) ℂ, ((transferConj g E η (c • V))⁻¹)ᴴ =
      ((freeConj W E)⁻¹ * (transferInv g (↑E + ↑η * Complex.I) (c • V) * freeConj W E))ᴴ :=
    fun V => by
      rw [transferConj, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
        Matrix.nonsing_inv_nonsing_inv _ hS, inv_transferMat]
  refine Continuous.congr ?_ fun V => (heq V).symm
  exact (continuous_const.mul (((continuous_transferInv' g _).comp
    (continuous_const_smul c)).mul continuous_const)).matrix_conjTranspose

private lemma moments_conj_transferProd {W L : ℕ} {E : ℝ} (hE : |E| < 2) (g η t : ℝ)
    (s : ℕ → Fin L) (ω : Ω W L) (j : ℕ) :
    (freeConj W E)⁻¹ * transferProd g (↑E + ↑η * Complex.I)
        (fun i => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω (s i)) j * freeConj W E =
      momentsProd (fun V => transferConj g E η (((Real.sqrt t : ℝ) : ℂ) • V)) s ω j := by
  have hS : IsUnit (freeConj W E).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_freeConj W hE)
  induction j with
  | zero => simp [transferProd, momentsProd, Matrix.nonsing_inv_mul _ hS]
  | succ j ih =>
    rw [transferProd, momentsProd, moments_conj_mul hS, ih]
    rfl

private lemma moments_conj_transferProd_inv {W L : ℕ} {E : ℝ} (hE : |E| < 2) (g η t : ℝ)
    (s : ℕ → Fin L) (ω : Ω W L) (j : ℕ) :
    (((freeConj W E)⁻¹ * transferProd g (↑E + ↑η * Complex.I)
        (fun i => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω (s i)) j * freeConj W E)⁻¹)ᴴ =
      momentsProd (fun V => ((transferConj g E η (((Real.sqrt t : ℝ) : ℂ) • V))⁻¹)ᴴ) s ω j := by
  have hS : IsUnit (freeConj W E).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_freeConj W hE)
  induction j with
  | zero => simp [transferProd, momentsProd, Matrix.nonsing_inv_mul _ hS]
  | succ j ih =>
    rw [transferProd, momentsProd, moments_conj_mul hS, Matrix.mul_inv_rev,
      Matrix.conjTranspose_mul, ih]
    rfl

/-- The final form of the tail: from the product tail of `R_j` to `X_j` with
`‖X_j‖ ≤ 2K ‖R_j‖`, and `an ≤ W B`. -/
private lemma moments_tail_of_le {W L : ℕ}
    {F : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hF : Continuous F) {a : ℝ} (ha : 0 ≤ a)
    (hstep : ∀ (b : Fin L) (v : Fin 2 × Fin W → ℂ),
      ∫⁻ ω, ENNReal.ofReal (momentsN (F (gueBlock W L ω b) *ᵥ v)) ∂μ W L ≤
        ENNReal.ofReal (Real.exp a * momentsN v))
    {s : ℕ → Fin L} {n : ℕ} (hs : Set.InjOn s (Set.Iio n)) {K B : ℝ} (hK : 0 < K)
    (han : (n : ℝ) * a ≤ W * B)
    (X : Ω W L → ℕ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hX : ∀ ω j, ‖X ω j‖ ≤ 2 * K * ‖momentsProd F s ω j‖) {u : ℝ} (hu : 0 < u) :
    μ W L {ω | u < ⨆ j : Fin (n + 1), ‖X ω j‖} ≤
      ENNReal.ofReal (min 1 ((2500 * K * Real.exp B / u) ^ W)) := by
  rw [ENNReal.ofReal_min, ENNReal.ofReal_one]
  refine le_min prob_le_one ?_
  have hsub : {ω | u < ⨆ j : Fin (n + 1), ‖X ω j‖} ⊆
      {ω | ∃ j ≤ n, u / (2 * K) < ‖momentsProd F s ω j‖} := by
    intro ω hω
    obtain ⟨j, hj⟩ := exists_lt_of_lt_ciSup (show u < ⨆ j : Fin (n + 1), ‖X ω j‖ from hω)
    refine ⟨j, Nat.lt_succ_iff.mp j.2, ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    linarith [hX ω j]
  refine (measure_mono hsub).trans ((moments_prod_tail hF ha hstep hs (by positivity)).trans ?_)
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : Real.exp a ^ n ≤ Real.exp B ^ W := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr han
  calc 5 ^ (4 * W) * Real.exp a ^ n * (2 / (u / (2 * K))) ^ W
      ≤ 5 ^ (4 * W) * Real.exp B ^ W * (2 / (u / (2 * K))) ^ W := by gcongr
    _ = (2500 * K * Real.exp B / u) ^ W := by
      rw [pow_mul, ← mul_pow, ← mul_pow]
      congr 1
      field_simp
      ring

/-- `an ≤ W A (C₀ + C₁)` for `a = A W (|η| + g⁻²)`, `n ≤ C₀ g²`, `n|η| ≤ C₁` (proof of (7.3)
[uvs:eq:transfer-tail]). -/
private lemma moments_an_le {A C₀ C₁ g η : ℝ} {W n : ℕ} (hA : 0 < A) (hg : 0 < g)
    (hn : (n : ℝ) ≤ C₀ * g ^ 2) (hnη : (n : ℝ) * |η| ≤ C₁) :
    (n : ℝ) * (A * W * (|η| + g⁻¹ ^ 2)) ≤ W * (A * (C₀ + C₁)) := by
  have h1 : (n : ℝ) * g⁻¹ ^ 2 ≤ C₀ := by
    rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    exact hn
  calc (n : ℝ) * (A * W * (|η| + g⁻¹ ^ 2)) = A * W * ((n : ℝ) * |η| + n * g⁻¹ ^ 2) := by ring
    _ ≤ A * W * (C₁ + C₀) := mul_le_mul_of_nonneg_left (add_le_add hnη h1) (by positivity)
    _ = W * (A * (C₀ + C₁)) := by ring

private lemma moments_hstep {W L : ℕ} {a : ℝ}
    {F : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (h : ∀ (b : Fin L) (v : Fin 2 × Fin W → ℂ),
      Integrable (fun ω => momentsN (F (gueBlock W L ω b) *ᵥ v)) (μ W L) ∧
      ∫ ω, momentsN (F (gueBlock W L ω b) *ᵥ v) ∂(μ W L) ≤ Real.exp a * momentsN v)
    (b : Fin L) (v : Fin 2 × Fin W → ℂ) :
    ∫⁻ ω, ENNReal.ofReal (momentsN (F (gueBlock W L ω b) *ᵥ v)) ∂μ W L ≤
      ENNReal.ofReal (Real.exp a * momentsN v) := by
  obtain ⟨hint, hle⟩ := h b v
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => momentsN_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hle

/-! ### Layer cake -/

/-- Integrating the tail `min{1, (C/u)^W}` gives `E f^p ≤ 2 C^p` for `W ≥ 2p` (last step of the
proof of Lemma 7.2 [uvs:lem:transfer-moments]). -/
private lemma moments_layer_cake {W L : ℕ} {f : Ω W L → ℝ} (hf0 : ∀ ω, 0 ≤ f ω)
    (hfm : Measurable f) {C p : ℝ} (hC : 0 < C) (hp : 0 < p) (hW : 2 * p ≤ W)
    (htail : ∀ u : ℝ, 0 < u → μ W L {ω | u < f ω} ≤ ENNReal.ofReal (min 1 ((C / u) ^ W))) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ W L ≤ ENNReal.ofReal (2 * C ^ p) := by
  have hWp : 0 < (W : ℝ) - p := by linarith
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul (μ W L) (ae_of_all _ hf0) hfm.aemeasurable hp,
    ← Set.Ioc_union_Ioi_eq_Ioi hC.le,
    lintegral_union measurableSet_Ioi (Set.Ioc_disjoint_Ioi le_rfl)]
  have hI1 : ∫⁻ t in Set.Ioc 0 C, μ W L {ω | t < f ω} * ENNReal.ofReal (t ^ (p - 1)) ≤
      ENNReal.ofReal (C ^ p / p) := by
    have hint : IntegrableOn (fun t : ℝ => t ^ (p - 1)) (Set.Ioc 0 C) :=
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < p - 1)).1
    calc ∫⁻ t in Set.Ioc 0 C, μ W L {ω | t < f ω} * ENNReal.ofReal (t ^ (p - 1))
        ≤ ∫⁻ t in Set.Ioc 0 C, ENNReal.ofReal (t ^ (p - 1)) :=
          setLIntegral_mono' measurableSet_Ioc fun t _ =>
            (mul_le_mul_left prob_le_one _).trans (one_mul _).le
      _ = ENNReal.ofReal (∫ t in Set.Ioc 0 C, t ^ (p - 1)) :=
          (ofReal_integral_eq_lintegral_ofReal hint ((ae_restrict_iff' measurableSet_Ioc).mpr
            (ae_of_all _ fun t ht => Real.rpow_nonneg ht.1.le _))).symm
      _ = ENNReal.ofReal (C ^ p / p) := by
          rw [← intervalIntegral.integral_of_le hC.le, integral_rpow (Or.inl (by linarith)),
            sub_add_cancel, Real.zero_rpow hp.ne', sub_zero]
  have hI2 : ∫⁻ t in Set.Ioi C, μ W L {ω | t < f ω} * ENNReal.ofReal (t ^ (p - 1)) ≤
      ENNReal.ofReal (C ^ p / (W - p)) := by
    have hint : IntegrableOn (fun t : ℝ => C ^ W * t ^ (p - 1 - W)) (Set.Ioi C) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith : p - 1 - W < -1) hC).const_mul _
    calc ∫⁻ t in Set.Ioi C, μ W L {ω | t < f ω} * ENNReal.ofReal (t ^ (p - 1))
        ≤ ∫⁻ t in Set.Ioi C, ENNReal.ofReal (C ^ W * t ^ (p - 1 - W)) := by
          refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
          have ht0 : 0 < t := hC.trans ht
          calc μ W L {ω | t < f ω} * ENNReal.ofReal (t ^ (p - 1))
              ≤ ENNReal.ofReal ((C / t) ^ W) * ENNReal.ofReal (t ^ (p - 1)) :=
                mul_le_mul_left ((htail t ht0).trans
                  (ENNReal.ofReal_le_ofReal (min_le_right _ _))) _
            _ = ENNReal.ofReal (C ^ W * t ^ (p - 1 - W)) := by
                rw [← ENNReal.ofReal_mul (by positivity)]
                congr 1
                rw [show p - 1 - (W : ℝ) = (p - 1) + -(W : ℝ) by ring, Real.rpow_add ht0,
                  Real.rpow_neg ht0.le, Real.rpow_natCast, div_pow]
                field_simp
      _ = ENNReal.ofReal (∫ t in Set.Ioi C, C ^ W * t ^ (p - 1 - W)) :=
          (ofReal_integral_eq_lintegral_ofReal hint ((ae_restrict_iff' measurableSet_Ioi).mpr
            (ae_of_all _ fun t ht => by
              have := Real.rpow_nonneg (hC.trans ht).le (p - 1 - W)
              positivity))).symm
      _ = ENNReal.ofReal (C ^ p / (W - p)) := by
          rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hC]
          congr 1
          rw [show p - 1 - (W : ℝ) + 1 = p - W by ring, ← Real.rpow_natCast,
            show -C ^ (p - W) / (p - W) = C ^ (p - W) / (W - p) by
              rw [neg_div, ← div_neg, neg_sub],
            ← mul_div_assoc, ← Real.rpow_add hC]
          congr 2
          ring
  calc _ ≤ ENNReal.ofReal p * (ENNReal.ofReal (C ^ p / p) + ENNReal.ofReal (C ^ p / (W - p))) := by
        gcongr
    _ = ENNReal.ofReal (C ^ p + C ^ p * (p / (W - p))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul hp.le]
        congr 1
        field_simp
    _ ≤ ENNReal.ofReal (2 * C ^ p) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : p / (W - p) ≤ 1 := (div_le_one hWp).mpr (by linarith)
        nlinarith [Real.rpow_pos_of_pos hC p]

/-! ### Continuity of the transfer products and their inverses -/

private lemma continuous_transferProd {W L : ℕ} (g : ℝ) (z : ℂ) (c : ℂ) (s : ℕ → Fin L)
    (j : ℕ) : Continuous fun ω : Ω W L =>
      transferProd g z (fun i => c • gueBlock W L ω (s i)) j := by
  induction j with
  | zero => exact continuous_const
  | succ j ih =>
    exact ((continuous_transferMat' g z).comp ((continuous_gueBlock (s j)).const_smul c)).mul ih

private lemma continuous_transferProd_inv {W L : ℕ} (g : ℝ) (z : ℂ) (c : ℂ) (s : ℕ → Fin L)
    (j : ℕ) : Continuous fun ω : Ω W L =>
      (transferProd g z (fun i => c • gueBlock W L ω (s i)) j)⁻¹ := by
  induction j with
  | zero => simpa [transferProd] using continuous_const
  | succ j ih =>
    have heq : ∀ ω : Ω W L, (transferProd g z (fun i => c • gueBlock W L ω (s i)) (j + 1))⁻¹ =
        (transferProd g z (fun i => c • gueBlock W L ω (s i)) j)⁻¹ *
          transferInv g z (c • gueBlock W L ω (s j)) := fun ω => by
      rw [transferProd, Matrix.mul_inv_rev, inv_transferMat]
    refine Continuous.congr ?_ fun ω => (heq ω).symm
    exact ih.mul ((continuous_transferInv' g z).comp ((continuous_gueBlock (s j)).const_smul c))

/-! ### Lemma 7.2 [uvs:lem:transfer-moments] -/

/-- (7.3) [uvs:eq:transfer-tail] for the prefix products along an injective block sequence,
onsite variance `t ∈ [0, 1]`. -/
theorem transfer_tail (κ C₀ C₁ : ℝ) (hκ : 0 < κ) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W L : ℕ) (s : ℕ → Fin L) (n : ℕ), Set.InjOn s (Set.Iio n) →
      ∀ g : ℝ, 2 / Real.sqrt κ ≤ g → (n : ℝ) ≤ C₀ * g ^ 2 → ∀ E η t : ℝ, |E| ≤ 2 - κ →
      |η| ≤ 1 → (n : ℝ) * |η| ≤ C₁ → 0 ≤ t → t ≤ 1 → ∀ u : ℝ, 0 < u →
      μ W L {ω | u < ⨆ j : Fin (n + 1), ‖transferProd g (↑E + ↑η * Complex.I)
          (fun i => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω (s i)) j‖} ≤
        ENNReal.ofReal (min 1 ((C / u) ^ W)) := by
  obtain ⟨A, hA, hstep⟩ := one_step_moment κ hκ
  have hK : 0 < Real.sqrt (2 / κ) := Real.sqrt_pos.mpr (by positivity)
  refine ⟨2500 * Real.sqrt (2 / κ) * Real.exp (A * (C₀ + C₁)), by positivity, ?_⟩
  intro W L s n hs g hg hn E η t hE hη hnη ht0 ht1 u hu
  have hE2 : |E| < 2 := by linarith
  have hg0 : 0 < g := lt_of_lt_of_le (by positivity) hg
  have hS : IsUnit (freeConj W E).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_freeConj W hE2)
  set F : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
    fun V => transferConj g E η (((Real.sqrt t : ℝ) : ℂ) • V) with hFdef
  have hFc : Continuous F := continuous_transferConj' g E η _
  have ha : 0 ≤ A * W * (|η| + g⁻¹ ^ 2) := by positivity
  have hst : ∀ (b : Fin L) (v : Fin 2 × Fin W → ℂ),
      ∫⁻ ω, ENNReal.ofReal (momentsN (F (gueBlock W L ω b) *ᵥ v)) ∂μ W L ≤
        ENNReal.ofReal (Real.exp (A * W * (|η| + g⁻¹ ^ 2)) * momentsN v) :=
    moments_hstep fun b v => hstep W L b g hg E η t hE hη ht0 ht1 v
  have hX : ∀ ω j, ‖transferProd g (↑E + ↑η * Complex.I)
      (fun i => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω (s i)) j‖ ≤
        2 * Real.sqrt (2 / κ) * ‖momentsProd F s ω j‖ := fun ω j => by
    rw [hFdef, ← moments_conj_transferProd hE2 g η t s ω j]
    exact (moments_norm_le hS _).trans (mul_le_mul_of_nonneg_right
      (norm_freeConj_mul_norm_inv_le W hκ hE) (norm_nonneg _))
  exact moments_tail_of_le hFc ha hst hs hK (moments_an_le hA hg0 hn hnη)
    (fun ω j => transferProd g (↑E + ↑η * Complex.I)
      (fun i => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω (s i)) j) hX hu

/-- The inverse-product version of (7.3) [uvs:eq:transfer-tail]. -/
theorem transfer_inv_tail (κ C₀ C₁ : ℝ) (hκ : 0 < κ) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W L : ℕ) (s : ℕ → Fin L) (n : ℕ), Set.InjOn s (Set.Iio n) →
      ∀ g : ℝ, 2 / Real.sqrt κ ≤ g → (n : ℝ) ≤ C₀ * g ^ 2 → ∀ E η t : ℝ, |E| ≤ 2 - κ →
      |η| ≤ 1 → (n : ℝ) * |η| ≤ C₁ → 0 ≤ t → t ≤ 1 → ∀ u : ℝ, 0 < u →
      μ W L {ω | u < ⨆ j : Fin (n + 1), ‖(transferProd g (↑E + ↑η * Complex.I)
          (fun i => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω (s i)) j)⁻¹‖} ≤
        ENNReal.ofReal (min 1 ((C / u) ^ W)) := by
  obtain ⟨A, hA, hstep⟩ := one_step_moment_inv κ hκ
  have hK : 0 < Real.sqrt (2 / κ) := Real.sqrt_pos.mpr (by positivity)
  refine ⟨2500 * Real.sqrt (2 / κ) * Real.exp (A * (C₀ + C₁)), by positivity, ?_⟩
  intro W L s n hs g hg hn E η t hE hη hnη ht0 ht1 u hu
  have hE2 : |E| < 2 := by linarith
  have hg0 : 0 < g := lt_of_lt_of_le (by positivity) hg
  have hS : IsUnit (freeConj W E).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_freeConj W hE2)
  set F : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
    fun V => ((transferConj g E η (((Real.sqrt t : ℝ) : ℂ) • V))⁻¹)ᴴ with hFdef
  have hFc : Continuous F := continuous_inv_transferConj hE2 g η _
  have ha : 0 ≤ A * W * (|η| + g⁻¹ ^ 2) := by positivity
  have hst : ∀ (b : Fin L) (v : Fin 2 × Fin W → ℂ),
      ∫⁻ ω, ENNReal.ofReal (momentsN (F (gueBlock W L ω b) *ᵥ v)) ∂μ W L ≤
        ENNReal.ofReal (Real.exp (A * W * (|η| + g⁻¹ ^ 2)) * momentsN v) :=
    moments_hstep fun b v => hstep W L b g hg E η t hE hη ht0 ht1 v
  have hX : ∀ ω j, ‖(transferProd g (↑E + ↑η * Complex.I)
      (fun i => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω (s i)) j)⁻¹‖ ≤
        2 * Real.sqrt (2 / κ) * ‖momentsProd F s ω j‖ := fun ω j => by
    rw [hFdef, ← moments_conj_transferProd_inv hE2 g η t s ω j, Matrix.l2_opNorm_conjTranspose,
      ← moments_inv_conj hS]
    exact (moments_norm_le hS _).trans (mul_le_mul_of_nonneg_right
      (norm_freeConj_mul_norm_inv_le W hκ hE) (norm_nonneg _))
  exact moments_tail_of_le hFc ha hst hs hK (moments_an_le hA hg0 hn hnη)
    (fun ω j => (transferProd g (↑E + ↑η * Complex.I)
      (fun i => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω (s i)) j)⁻¹) hX hu

/-- Lemma 7.2 [uvs:lem:transfer-moments], (7.1) [uvs:eq:transfer-moments]: uniform maximal
moments of the prefix products and their inverses, for `W ≥ 2p`. -/
theorem transfer_moments (κ C₀ C₁ p : ℝ) (hκ : 0 < κ) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W L : ℕ), 2 * p ≤ W → ∀ (s : ℕ → Fin L) (n : ℕ),
      Set.InjOn s (Set.Iio n) → ∀ g : ℝ, 2 / Real.sqrt κ ≤ g → (n : ℝ) ≤ C₀ * g ^ 2 →
      ∀ E η t : ℝ, |E| ≤ 2 - κ → |η| ≤ 1 → (n : ℝ) * |η| ≤ C₁ → 0 ≤ t → t ≤ 1 →
      Integrable (fun ω => ⨆ j : Fin (n + 1),
          (‖transferProd g (↑E + ↑η * Complex.I)
              (fun i => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω (s i)) j‖ ^ p +
            ‖(transferProd g (↑E + ↑η * Complex.I)
              (fun i => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω (s i)) j)⁻¹‖ ^ p)) (μ W L) ∧
      ∫ ω, (⨆ j : Fin (n + 1),
          (‖transferProd g (↑E + ↑η * Complex.I)
              (fun i => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω (s i)) j‖ ^ p +
            ‖(transferProd g (↑E + ↑η * Complex.I)
              (fun i => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω (s i)) j)⁻¹‖ ^ p)) ∂(μ W L) ≤
        C := by
  obtain ⟨Ca, hCa, ha⟩ := transfer_tail κ C₀ C₁ hκ hC₀ hC₁
  obtain ⟨Cb, hCb, hb⟩ := transfer_inv_tail κ C₀ C₁ hκ hC₀ hC₁
  set Cm := max Ca Cb with hCm
  have hCm0 : 0 < Cm := lt_max_of_lt_left hCa
  refine ⟨4 * Cm ^ p, by positivity, ?_⟩
  intro W L hW s n hs g hg hn E η t hE hη hnη ht0 ht1
  set P : Ω W L → ℕ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := fun ω j =>
    transferProd g (↑E + ↑η * Complex.I)
      (fun i => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω (s i)) j with hPdef
  have hPc : ∀ j, Continuous fun ω => ‖P ω j‖ := fun j =>
    continuous_norm.comp (continuous_transferProd g _ _ s j)
  have hPic : ∀ j, Continuous fun ω => ‖(P ω j)⁻¹‖ := fun j =>
    continuous_norm.comp (continuous_transferProd_inv g _ _ s j)
  set f₁ : Ω W L → ℝ := fun ω => ⨆ j : Fin (n + 1), ‖P ω j‖ with hf₁
  set f₂ : Ω W L → ℝ := fun ω => ⨆ j : Fin (n + 1), ‖(P ω j)⁻¹‖ with hf₂
  have hf₁0 : ∀ ω, 0 ≤ f₁ ω := fun ω => Real.iSup_nonneg fun _ => norm_nonneg _
  have hf₂0 : ∀ ω, 0 ≤ f₂ ω := fun ω => Real.iSup_nonneg fun _ => norm_nonneg _
  have hf₁m : Measurable f₁ := Measurable.iSup fun j => (hPc j).measurable
  have hf₂m : Measurable f₂ := Measurable.iSup fun j => (hPic j).measurable
  have hmono : ∀ {C' : ℝ}, 0 < C' → C' ≤ Cm → ∀ u : ℝ, 0 < u →
      ENNReal.ofReal (min 1 ((C' / u) ^ W)) ≤ ENNReal.ofReal (min 1 ((Cm / u) ^ W)) :=
    fun hC0 hC' u hu => ENNReal.ofReal_le_ofReal (min_le_min_left _ (by gcongr))
  have hL₁ : ∫⁻ ω, ENNReal.ofReal (f₁ ω ^ p) ∂μ W L ≤ ENNReal.ofReal (2 * Cm ^ p) :=
    moments_layer_cake hf₁0 hf₁m hCm0 hp hW fun u hu =>
      (ha W L s n hs g hg hn E η t hE hη hnη ht0 ht1 u hu).trans
        (hmono hCa (le_max_left _ _) u hu)
  have hL₂ : ∫⁻ ω, ENNReal.ofReal (f₂ ω ^ p) ∂μ W L ≤ ENNReal.ofReal (2 * Cm ^ p) :=
    moments_layer_cake hf₂0 hf₂m hCm0 hp hW fun u hu =>
      (hb W L s n hs g hg hn E η t hE hη hnη ht0 ht1 u hu).trans
        (hmono hCb (le_max_right _ _) u hu)
  set G : Ω W L → ℝ := fun ω => ⨆ j : Fin (n + 1), (‖P ω j‖ ^ p + ‖(P ω j)⁻¹‖ ^ p) with hGdef
  have hG0 : ∀ ω, 0 ≤ G ω := fun ω => Real.iSup_nonneg fun _ => by positivity
  have hGm : Measurable G := Measurable.iSup fun j =>
    (((hPc j).rpow_const fun _ => Or.inr hp.le).add
      ((hPic j).rpow_const fun _ => Or.inr hp.le)).measurable
  have hGle : ∀ ω, G ω ≤ f₁ ω ^ p + f₂ ω ^ p := fun ω =>
    ciSup_le fun j => add_le_add
      (Real.rpow_le_rpow (norm_nonneg _)
        (le_ciSup (f := fun j : Fin (n + 1) => ‖P ω j‖) (Finite.bddAbove_range _) j) hp.le)
      (Real.rpow_le_rpow (norm_nonneg _)
        (le_ciSup (f := fun j : Fin (n + 1) => ‖(P ω j)⁻¹‖) (Finite.bddAbove_range _) j) hp.le)
  have hlint : ∫⁻ ω, ENNReal.ofReal (G ω) ∂μ W L ≤ ENNReal.ofReal (4 * Cm ^ p) := by
    calc ∫⁻ ω, ENNReal.ofReal (G ω) ∂μ W L
        ≤ ∫⁻ ω, (ENNReal.ofReal (f₁ ω ^ p) + ENNReal.ofReal (f₂ ω ^ p)) ∂μ W L :=
          lintegral_mono fun ω => by
            rw [← ENNReal.ofReal_add (Real.rpow_nonneg (hf₁0 ω) _)
              (Real.rpow_nonneg (hf₂0 ω) _)]
            exact ENNReal.ofReal_le_ofReal (hGle ω)
      _ = ∫⁻ ω, ENNReal.ofReal (f₁ ω ^ p) ∂μ W L + ∫⁻ ω, ENNReal.ofReal (f₂ ω ^ p) ∂μ W L :=
          lintegral_add_left (ENNReal.measurable_ofReal.comp (hf₁m.pow_const p)) _
      _ ≤ ENNReal.ofReal (2 * Cm ^ p) + ENNReal.ofReal (2 * Cm ^ p) := add_le_add hL₁ hL₂
      _ = ENNReal.ofReal (4 * Cm ^ p) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          ring_nf
  have hint : Integrable G (μ W L) :=
    ⟨hGm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hG0)).mpr
      (lt_of_le_of_lt hlint ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  show ∫ ω, G ω ∂μ W L ≤ 4 * Cm ^ p
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hG0) hGm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlint

end LSBA
