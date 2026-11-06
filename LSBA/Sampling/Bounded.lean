import LSBA.Sampling.Reach

/-!
# Inputs at bounded coupling

The sampling bound (5.34) [fo:eq:weighted-sampling-input] with the full label set, its
consequence from a deterministic norming inequality, and the inputs of Lemma 5.10
[fo:lem:sampling-continuity] and the weighted sampling (5.34) [fo:eq:weighted-sampling-input] at
bounded coupling, where `L ≤ W²` makes exact sampling polynomial in `W` and `‖G‖ ≤ (Im z)⁻¹ ≤ C W³`
gives the crude moments.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- Exact sampling: with all labels sampled, `C ≥ 1`, `δ ≥ 0` and nonnegative weights, the
event of (5.34) [fo:eq:weighted-sampling-input] is empty. -/
theorem sampleBound_univ {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') {Λ : Type*}
    [Fintype Λ] (X : Λ → Ω' → ℂ) (w : Λ → ℝ) (hw : ∀ l, 0 ≤ w l) {C δ : ℝ} (hC : 1 ≤ C)
    (hδ : 0 ≤ δ) (η : ℝ) : SampleBound P X w Finset.univ C δ η := by
  unfold SampleBound
  have hempty : {ω | ∃ l, C * (⨆ s : (Finset.univ : Finset Λ), ‖X s ω‖ / w s) + δ <
      ‖X l ω‖ / w l} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
    intro l
    have hbdd : BddAbove (Set.range fun s : (Finset.univ : Finset Λ) => ‖X s ω‖ / w s) :=
      (Set.finite_range _).bddAbove
    have h1 : ‖X l ω‖ / w l ≤ ⨆ s : (Finset.univ : Finset Λ), ‖X s ω‖ / w s :=
      le_ciSup hbdd (⟨l, Finset.mem_univ l⟩ : (Finset.univ : Finset Λ))
    have h0 : 0 ≤ ⨆ s : (Finset.univ : Finset Λ), ‖X s ω‖ / w s :=
      le_trans (div_nonneg (norm_nonneg _) (hw l)) h1
    nlinarith
  rw [hempty]
  simp

/-- A deterministic norming inequality outside an event of probability at most `η` gives
(5.34) [fo:eq:weighted-sampling-input]. -/
theorem sampleBound_of_norming {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') {Λ : Type*}
    (X : Λ → Ω' → ℂ) (w : Λ → ℝ) (S : Finset Λ) (C δ η : ℝ) (A : Set Ω')
    (hA : P A ≤ ENNReal.ofReal η)
    (hX : ∀ ω, ω ∉ A → ∀ l, ‖X l ω‖ / w l ≤ C * (⨆ s : S, ‖X s ω‖ / w s) + δ) :
    SampleBound P X w S C δ η := by
  unfold SampleBound
  refine (measure_mono ?_).trans hA
  intro ω hω
  by_contra hωA
  obtain ⟨l, hl⟩ := hω
  exact absurd (hX ω hωA l) (not_le.mpr hl)

open scoped Matrix.Norms.L2Operator in
/-- A block of a matrix on `ℂ^L ⊗ ℂ^W` has operator norm at most that of the matrix. -/
private lemma bounded_norm_blockOf_le {W L : ℕ}
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) :
    ‖blockOf G a b‖ ≤ ‖G‖ := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  set u : EuclideanSpace ℂ (Fin L × Fin W) :=
    WithLp.toLp 2 (fun x => if x.1 = b then v.ofLp x.2 else 0) with hu
  have h := Matrix.l2_opNorm_mulVec G u
  have hnu : ‖u‖ = ‖v‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
    · simp [hu]
    · intro c _ hc; simp [hu, hc]
    · intro h; exact absurd (Finset.mem_univ b) h
  have key : ‖(Matrix.toEuclideanLin (𝕜 := ℂ) (blockOf G a b)) v‖ ≤
      ‖(EuclideanSpace.equiv (Fin L × Fin W) ℂ).symm (G *ᵥ u)‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    have hentry : ∀ α : Fin W, (Matrix.toEuclideanLin (𝕜 := ℂ) (blockOf G a b)) v α =
        (G *ᵥ ⇑u) (a, α) := by
      intro α
      change (blockOf G a b *ᵥ v.ofLp) α = _
      simp only [Matrix.mulVec, dotProduct, blockOf, Matrix.of_apply, Fintype.sum_prod_type, hu]
      rw [Finset.sum_eq_single b]
      · simp
      · intro c _ hc; simp [hc]
      · intro h; exact absurd (Finset.mem_univ b) h
    calc _ = ∑ α : Fin W, ‖(G *ᵥ ⇑u) (a, α)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [hentry α]
      _ ≤ ∑ c : Fin L, ∑ α : Fin W, ‖(G *ᵥ ⇑u) (c, α)‖ ^ 2 :=
          Finset.single_le_sum (f := fun c : Fin L => ∑ α : Fin W, ‖(G *ᵥ ⇑u) (c, α)‖ ^ 2)
            (fun c _ => Finset.sum_nonneg fun α _ => by positivity) (Finset.mem_univ a)
      _ = _ := by rw [Fintype.sum_prod_type]; rfl
  calc _ ≤ _ := key
    _ ≤ _ := h
    _ = _ := by rw [hnu]

/-- Every height of an admissible pair lies above the characteristic height `η_u`. -/
private lemma bounded_etaChar_le {J d : ℕ} {p : FlowPt} {y : ℝ} (hh : SegHeight J d p y) :
    etaChar p.g (mRoot p.g p.L p.E) p.u ≤ y := by
  rcases hh with h | ⟨-, s, -, -, h, -⟩
  · exact h.ge
  · exact h

open scoped Matrix.Norms.L2Operator in
/-- (5.3) [fo:eq:characteristic]: `‖G‖ ≤ y⁻¹ ≤ η_u⁻¹` at every height of an admissible pair. -/
private lemma bounded_norm_segG_le_eta {J d W : ℕ} {x : FlowPt × ℝ}
    (hm : 0 < (mRoot x.1.g x.1.L x.1.E).im) (hu : x.1.u < 1) (hh : SegHeight J d x.1 x.2)
    (ω : Ω W x.1.L) :
    ‖segG W x ω‖ ≤ (etaChar x.1.g (mRoot x.1.g x.1.L x.1.E) x.1.u)⁻¹ := by
  have hη := etaChar_pos x.1.g _ hm hu
  have hy : etaChar x.1.g (mRoot x.1.g x.1.L x.1.E) x.1.u ≤ x.2 := bounded_etaChar_le hh
  have hy0 : 0 < x.2 := hη.trans_le hy
  have hz : x.2 ≤ |((((zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re : ℂ)) +
      (x.2 : ℂ) * Complex.I).im| := by
    simp [abs_of_pos hy0]
  exact (norm_resolventMat_le (flowH_isHermitian _ _ _ _ ω) hy0 hz).trans
    (inv_anti₀ hη hy)

/-- At the bounded range, `η_u⁻¹ ≤ max(1,C)² c⁻¹ W³`. -/
private lemma bounded_etaChar_inv_le {C c : ℝ} {W : ℕ} {p : FlowPt} (hc : 0 < c)
    (hW : 1 ≤ W) (hgC : p.g ≤ C) (hm : c ≤ (mRoot p.g p.L p.E).im)
    (hu : (W : ℝ) ^ (-3 : ℝ) ≤ 1 - p.u) :
    (etaChar p.g (mRoot p.g p.L p.E) p.u)⁻¹ ≤ (max 1 C) ^ 2 / c * (W : ℝ) ^ 3 := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have h3 : (0 : ℝ) < (W : ℝ) ^ 3 := by positivity
  have hrp : (W : ℝ) ^ (-3 : ℝ) = ((W : ℝ) ^ 3)⁻¹ := by
    rw [Real.rpow_neg hW0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hmax : (0 : ℝ) < max 1 C := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hγ : ((max 1 C) ^ 2)⁻¹ ≤ gammaG p.g := by
    unfold gammaG
    refine inv_anti₀ (by positivity) ?_
    exact pow_le_pow_left₀ (by positivity) (max_le_max le_rfl hgC) 2
  have hlow : ((W : ℝ) ^ 3)⁻¹ * (((max 1 C) ^ 2)⁻¹ * c) ≤
      etaChar p.g (mRoot p.g p.L p.E) p.u := by
    unfold etaChar
    rw [hrp] at hu
    have hγ0 : 0 ≤ ((max 1 C) ^ 2)⁻¹ := by positivity
    have h1u : 0 ≤ 1 - p.u := le_trans (by positivity) hu
    calc ((W : ℝ) ^ 3)⁻¹ * (((max 1 C) ^ 2)⁻¹ * c)
        ≤ (1 - p.u) * (gammaG p.g * (mRoot p.g p.L p.E).im) :=
          mul_le_mul hu (mul_le_mul hγ hm hc.le (hγ0.trans hγ)) (by positivity)
            h1u
      _ = _ := by ring
  have hpos : 0 < ((W : ℝ) ^ 3)⁻¹ * (((max 1 C) ^ 2)⁻¹ * c) := by positivity
  refine (inv_anti₀ hpos hlow).trans (le_of_eq ?_)
  field_simp

/-- The resolvent of the single-time realization is continuous in the sample off the real axis. -/
private lemma bounded_continuous_resolvent (g u : ℝ) (W L : ℕ) {z : ℂ} (hz : z.im ≠ 0) :
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

open scoped Matrix.Norms.L2Operator in
/-- `ω ↦ ‖G_{ab}‖^p` is continuous at a positive height. -/
private lemma bounded_continuous_norm_pow {W : ℕ} {x : FlowPt × ℝ} (hy : 0 < x.2) (a b : Fin x.1.L)
    (p : ℕ) :
    Continuous fun ω : Ω W x.1.L => ‖blockOf (segG W x ω) a b‖ ^ p := by
  have hz : ((((zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re : ℂ)) +
      (x.2 : ℂ) * Complex.I).im ≠ 0 := by
    simpa using hy.ne'
  have h := bounded_continuous_resolvent x.1.g x.1.u W x.1.L hz
  have h2 : Continuous fun ω : Ω W x.1.L => blockOf (segG W x ω) a b := by
    refine continuous_matrix fun α β => ?_
    exact (continuous_apply (b, β)).comp ((continuous_apply (a, α)).comp h)
  exact (h2.norm).pow p

open scoped Matrix.Norms.L2Operator in
/-- The `p`-th moment of an entry block of `G` at an admissible pair is integrable and at most
`K^p` whenever `η_u⁻¹ ≤ K`, (5.33) [fo:eq:coarse-time-input]. -/
private lemma bounded_moment_le {J d W : ℕ} {x : FlowPt × ℝ}
    (hm : 0 < (mRoot x.1.g x.1.L x.1.E).im) (hu : x.1.u < 1) (hh : SegHeight J d x.1 x.2)
    {K : ℝ} (hK : (etaChar x.1.g (mRoot x.1.g x.1.L x.1.E) x.1.u)⁻¹ ≤ K) (a b : Fin x.1.L)
    (p : ℕ) :
    Integrable (fun ω : Ω W x.1.L => ‖blockOf (segG W x ω) a b‖ ^ p) (μ W x.1.L) ∧
      ∫ ω, ‖blockOf (segG W x ω) a b‖ ^ p ∂(μ W x.1.L) ≤ K ^ p := by
  have hbound : ∀ ω : Ω W x.1.L, ‖blockOf (segG W x ω) a b‖ ≤ K :=
    fun ω => (bounded_norm_blockOf_le _ a b).trans
      ((bounded_norm_segG_le_eta hm hu hh ω).trans hK)
  have hy : 0 < x.2 := (etaChar_pos x.1.g _ hm hu).trans_le (bounded_etaChar_le hh)
  have hcont := bounded_continuous_norm_pow (W := W) hy a b p
  have hpow : ∀ ω : Ω W x.1.L, ‖blockOf (segG W x ω) a b‖ ^ p ≤ K ^ p :=
    fun ω => pow_le_pow_left₀ (norm_nonneg _) (hbound ω) p
  have hint : Integrable (fun ω : Ω W x.1.L => ‖blockOf (segG W x ω) a b‖ ^ p) (μ W x.1.L) :=
    Integrable.of_bound hcont.aestronglyMeasurable (K ^ p)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (by positivity)]; exact hpow ω)
  refine ⟨hint, ?_⟩
  calc ∫ ω, ‖blockOf (segG W x ω) a b‖ ^ p ∂(μ W x.1.L)
      ≤ ∫ _ω, K ^ p ∂(μ W x.1.L) := integral_mono hint (integrable_const _) hpow
    _ = K ^ p := by simp

open scoped Matrix.Norms.L2Operator in
/-- The crude moments at bounded coupling, `‖G‖ ≤ η⁻¹ ≤ C W³`, for every base family inside the
bounded-coupling range. -/
theorem crudeInput_of_bdd (C B c' : ℝ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c')
    (gmin ρ : ℕ → ℝ) (hgmin : ∀ W, 0 < gmin W) (hρ : Tendsto ρ atTop atTop) (J : ℕ)
    (base : ℕ → Set FlowPt)
    (hbase : ∀ W p, p ∈ base W → gmin W ≤ p.g ∧ RegBdd C B c' p.L p.g p.E ∧
      ρ W * Real.log W ≤ p.L ∧ (p.L : ℝ) ≤ (W : ℝ) ^ 2 ∧ 1 / 2 ≤ p.u ∧
      (W : ℝ) ^ (-3 : ℝ) ≤ 1 - p.u) :
    CrudeInput base J := by
  obtain ⟨BJ, cJ, hcJ, W₀, H⟩ := cmpReach_bdd C B c' hC hB hc' gmin ρ hgmin hρ J
  have H' := H base hbase
  refine ⟨3, fun p _ => ⟨((max 1 C) ^ 2 / cJ) ^ p, max W₀ 1, fun W hW x hx a b => ?_⟩⟩
  obtain ⟨d, hd, hreach, hh⟩ := hx
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  obtain ⟨hreg, -, -, -, -, hut⟩ := H' W (le_trans (le_max_left _ _) hW) d x.1 hd hreach
  have hu1 : x.1.u < 1 := by
    have := Real.rpow_pos_of_pos hW0 (-3 : ℝ)
    linarith
  have hm : cJ ≤ (mRoot x.1.g x.1.L x.1.E).im := hreg.2.2.2.2
  obtain ⟨hint, hle⟩ := bounded_moment_le (W := W) (hcJ.trans_le hm) hu1 hh
    (bounded_etaChar_inv_le hcJ hW1 hreg.2.1 hm hut) a b p
  refine ⟨hint, hle.trans (le_of_eq ?_)⟩
  rw [mul_pow, show (3 : ℝ) * p = ((3 * p : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
    pow_mul]

/-- The weight of Lemma 6.2 [da:lem:scale-budgets] is nonnegative. -/
private lemma bounded_weightFn_nonneg (c₁ θ F : ℝ) (W : ℕ) (ℓ r : ℝ) :
    0 ≤ weightFn c₁ θ F W ℓ r := by
  unfold weightFn
  positivity

/-- `W^{-D} ≥ 0`. -/
private lemma bounded_rpow_nonneg (W : ℕ) (D : ℝ) : 0 ≤ (W : ℝ) ^ (-D) :=
  Real.rpow_nonneg (Nat.cast_nonneg W) _

/-- Counting `k`-tuples of labels with `L ≤ W²`: `L^k ≤ W^{2k}`. -/
private lemma bounded_card_words_le {W L : ℕ} (hL : (L : ℝ) ≤ (W : ℝ) ^ 2) (k : ℕ) :
    ((Finset.univ : Finset (Fin k → Fin L)).card : ℝ) ≤ (W : ℝ) ^ ((2 * k : ℕ) : ℝ) := by
  rw [Real.rpow_natCast, pow_mul, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin]
  push_cast
  exact pow_le_pow_left₀ (Nat.cast_nonneg L) hL k

/-- Counting pairs of blocks with `L ≤ W²`: `L² ≤ W⁴`. -/
private lemma bounded_card_pairs_le {W L : ℕ} (hL : (L : ℝ) ≤ (W : ℝ) ^ 2) :
    ((Finset.univ : Finset (Fin L × Fin L)).card : ℝ) ≤ (W : ℝ) ^ ((4 : ℕ) : ℝ) := by
  rw [Real.rpow_natCast, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  push_cast
  calc (L : ℝ) * L ≤ (W : ℝ) ^ 2 * (W : ℝ) ^ 2 :=
        mul_le_mul hL hL (Nat.cast_nonneg L) (by positivity)
    _ = (W : ℝ) ^ 4 := by ring

/-- Counting pairs of entries with `L ≤ W²`: `(LW)² ≤ W⁶`. -/
private lemma bounded_card_entries_le {W L : ℕ} (hL : (L : ℝ) ≤ (W : ℝ) ^ 2) :
    ((Finset.univ : Finset ((Fin L × Fin W) × (Fin L × Fin W))).card : ℝ) ≤
      (W : ℝ) ^ ((6 : ℕ) : ℝ) := by
  rw [Real.rpow_natCast, Finset.card_univ, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin]
  push_cast
  have h : (L : ℝ) * W ≤ (W : ℝ) ^ 3 :=
    calc (L : ℝ) * W ≤ (W : ℝ) ^ 2 * W := mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg W)
      _ = (W : ℝ) ^ 3 := by ring
  calc (L : ℝ) * W * (L * W) ≤ (W : ℝ) ^ 3 * (W : ℝ) ^ 3 :=
        mul_le_mul h h (by positivity) (by positivity)
    _ = (W : ℝ) ^ 6 := by ring

/-- `L² ≤ W⁶` for `W ≥ 1`. -/
private lemma bounded_card_pairs_le_six {W L : ℕ} (hW : 1 ≤ W) (hL : (L : ℝ) ≤ (W : ℝ) ^ 2) :
    ((Finset.univ : Finset (Fin L × Fin L)).card : ℝ) ≤ (W : ℝ) ^ ((6 : ℕ) : ℝ) := by
  refine (bounded_card_pairs_le hL).trans ?_
  rw [Real.rpow_natCast, Real.rpow_natCast]
  exact pow_le_pow_right₀ (by exact_mod_cast hW) (by norm_num)

/-- Exact sampling at bounded coupling (all tuples, `L ≤ W²`), for every base family inside the
bounded-coupling range. -/
theorem samplingInput_of_bdd (C B c' : ℝ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c')
    (gmin ρ : ℕ → ℝ) (hgmin : ∀ W, 0 < gmin W) (hρ : Tendsto ρ atTop atTop) (J : ℕ)
    (base : ℕ → Set FlowPt)
    (hbase : ∀ W p, p ∈ base W → gmin W ≤ p.g ∧ RegBdd C B c' p.L p.g p.E ∧
      ρ W * Real.log W ≤ p.L ∧ (p.L : ℝ) ≤ (W : ℝ) ^ 2 ∧ 1 / 2 ≤ p.u ∧
      (W : ℝ) ^ (-3 : ℝ) ≤ 1 - p.u) :
    SamplingInput base J := by
  obtain ⟨BJ, cJ, hcJ, W₀, H⟩ := cmpReach_bdd C B c' hC hB hc' gmin ρ hgmin hρ J
  have H' := H base hbase
  refine ⟨fun k _ cw θ F _ _ _ _ D D' _ _ => ⟨((2 * k : ℕ) : ℝ), 1, max W₀ 1,
    fun W hW d p hd hreach => ?_⟩, fun D D' _ _ => ⟨((6 : ℕ) : ℝ), 1, max W₀ 1,
    fun W hW x hx => ?_⟩⟩
  · obtain ⟨-, -, -, hLW, -⟩ := H' W (le_trans (le_max_left _ _) hW) d p hd hreach
    refine ⟨Finset.univ, bounded_card_words_le hLW k, fun σ u _ _ => ?_⟩
    exact ⟨sampleBound_univ _ _ _ (fun _ => zero_le_one) le_rfl (bounded_rpow_nonneg W D) _,
      sampleBound_univ _ _ _ (fun _ => zero_le_one) le_rfl (bounded_rpow_nonneg W D) _,
      sampleBound_univ _ _ _ (fun _ => bounded_weightFn_nonneg _ _ _ _ _ _) le_rfl
        (bounded_rpow_nonneg W D) _,
      sampleBound_univ _ _ _ (fun _ => bounded_weightFn_nonneg _ _ _ _ _ _) le_rfl
        (bounded_rpow_nonneg W D) _⟩
  · obtain ⟨d, hd, hreach, -⟩ := hx
    obtain ⟨-, -, -, hLW, -⟩ := H' W (le_trans (le_max_left _ _) hW) d x.1 hd hreach
    have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
    exact ⟨Finset.univ, Finset.univ, bounded_card_pairs_le_six hW1 hLW,
      bounded_card_entries_le hLW,
      sampleBound_univ _ _ _ (fun _ => zero_le_one) le_rfl (bounded_rpow_nonneg W D) _,
      sampleBound_univ _ _ _ (fun _ => zero_le_one) le_rfl (bounded_rpow_nonneg W D) _,
      sampleBound_univ _ _ _ (fun _ => zero_le_one) le_rfl (bounded_rpow_nonneg W D) _⟩

/-- The weighted sampling (5.34) [fo:eq:weighted-sampling-input] with `C_w = 1` (all pairs) at
bounded coupling, for every base family inside the bounded-coupling range. -/
theorem swInput_of_bdd (C B c' : ℝ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c')
    (gmin ρ : ℕ → ℝ) (hgmin : ∀ W, 0 < gmin W) (hρ : Tendsto ρ atTop atTop) (J : ℕ)
    (base : ℕ → Set FlowPt)
    (hbase : ∀ W p, p ∈ base W → gmin W ≤ p.g ∧ RegBdd C B c' p.L p.g p.E ∧
      ρ W * Real.log W ≤ p.L ∧ (p.L : ℝ) ≤ (W : ℝ) ^ 2 ∧ 1 / 2 ≤ p.u ∧
      (W : ℝ) ^ (-3 : ℝ) ≤ 1 - p.u) :
    SwInput base J 1 := by
  obtain ⟨BJ, cJ, hcJ, W₀, H⟩ := cmpReach_bdd C B c' hC hB hc' gmin ρ hgmin hρ J
  have H' := H base hbase
  intro cp θ F D D' _ _ _ _ _ _ _
  refine ⟨((4 : ℕ) : ℝ), W₀, fun W hW d p hd hreach => ?_⟩
  obtain ⟨-, -, -, hLW, -⟩ := H' W hW d p hd hreach
  exact ⟨Finset.univ, bounded_card_pairs_le hLW, fun u v _ _ _ =>
    sampleBound_univ _ _ _ (fun _ => bounded_weightFn_nonneg _ _ _ _ _ _) le_rfl
      (bounded_rpow_nonneg W D) _⟩

end LSBA
