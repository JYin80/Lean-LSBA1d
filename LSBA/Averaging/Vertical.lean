import LSBA.Averaging.Haar
import LSBA.Averaging.Expansion
import LSBA.Kernel.Vertical
import LSBA.Sampling.Residual
import LSBA.Prop.Domination
import LSBA.Flow.Comparison

/-!
# Moments on vertical lines

The initial family of Lemma 5.6 [fo:prop:inputs] at large coupling, block-resolvent moments on
the vertical line above the characteristic point at a fixed time (Lemma 5.5
[fo:lem:resolvent-moments] at the rescaled coupling `g′ = (c₀/y)^{1/2}`), the moments of the
centered traces, traceless entries and residuals there, and their maximum over the heights of the
segment with the anchor sampling of Section 7.3 [app:uniform-compression].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Coupling, norms of blocks and continuity -/

private lemma vertical_hopB {g : ℝ} (hg : 1 ≤ g) : hopB g = 1 := by
  unfold hopB; rw [max_eq_right hg, div_self (by linarith)]

private lemma vertical_gammaG {g : ℝ} (hg : 1 ≤ g) : gammaG g = (g ^ 2)⁻¹ := by
  unfold gammaG; rw [max_eq_right hg]

private lemma vertical_gammaG_pos (g : ℝ) : 0 < gammaG g := by
  have : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  unfold gammaG
  positivity

private lemma vertical_Ag {g : ℝ} (hg : 1 ≤ g) (L : ℕ) : Ag g L = cycleAdj L := by
  rw [Ag, max_eq_right hg, div_self (by linarith : g ≠ 0)]
  simp

/-- A column of a matrix has Euclidean norm at most the operator norm. -/
private lemma vertical_col_sq_le {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ)
    (β : n) : ∑ α, ‖X α β‖ ^ 2 ≤ ‖X‖ ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec X (EuclideanSpace.single β 1)
  rw [PiLp.norm_single, norm_one, mul_one] at h
  have hcol : (EuclideanSpace.equiv n ℂ).symm (X *ᵥ (EuclideanSpace.single β (1 : ℂ))) =
      WithLp.toLp 2 (fun α => X α β) := by
    ext α
    simp [EuclideanSpace.equiv]
  rw [hcol, EuclideanSpace.norm_eq] at h
  have h0 : 0 ≤ Real.sqrt (∑ α, ‖X α β‖ ^ 2) := Real.sqrt_nonneg _
  have := pow_le_pow_left₀ h0 h 2
  rwa [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at this

private lemma vertical_entry_le {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ)
    (α β : n) : ‖X α β‖ ≤ ‖X‖ := by
  have h1 : ‖X α β‖ ^ 2 ≤ ∑ α', ‖X α' β‖ ^ 2 :=
    Finset.single_le_sum (f := fun α' => ‖X α' β‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ α)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
    (h1.trans (vertical_col_sq_le X β))

/-- `‖G_{ab}‖_HS² ≤ W ‖G_{ab}‖²`. -/
private lemma vertical_blockHS2_le {W L : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : blockHS2 X a b ≤ W * ‖blockOf X a b‖ ^ 2 := by
  unfold blockHS2
  rw [Finset.sum_comm]
  calc ∑ β : Fin W, ∑ α : Fin W, ‖X (a, α) (b, β)‖ ^ 2
      ≤ ∑ _β : Fin W, ‖blockOf X a b‖ ^ 2 :=
        Finset.sum_le_sum fun β _ => vertical_col_sq_le (blockOf X a b) β
    _ = W * ‖blockOf X a b‖ ^ 2 := by simp

/-- `|⟨G⟩_{ab}| ≤ ‖G_{ab}‖`. -/
private lemma vertical_blockTr_le {W L : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : ‖blockTr X a b‖ ≤ ‖blockOf X a b‖ := by
  unfold blockTr
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW; simp
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (W : ℝ)⁻¹ * ‖∑ α, X (a, α) (b, α)‖ ≤ (W : ℝ)⁻¹ * ∑ _α : Fin W, ‖blockOf X a b‖ := by
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
        exact vertical_entry_le (blockOf X a b) α α
    _ = ‖blockOf X a b‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

private lemma vertical_continuous_gueBlock {W L : ℕ} (b : Fin L) :
    Continuous fun ω : Ω W L => gueBlock W L ω b := by
  refine continuous_matrix fun α β => ?_
  simp only [gueBlock, Matrix.of_apply]
  split_ifs <;> fun_prop

private lemma vertical_continuous_flowH (g : ℝ) (W L : ℕ) (u : ℝ) :
    Continuous fun ω : Ω W L => flowH g W L u ω := by
  refine continuous_matrix fun x y => ?_
  simp only [flowH, blockFlow, blockV, blockDiagOp, Matrix.add_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul]
  refine continuous_const.add (continuous_const.mul ?_)
  by_cases hxy : x.1 = y.1
  · simp only [hxy, ite_true]
    exact (vertical_continuous_gueBlock y.1).matrix_elem x.2 y.2
  · simp only [hxy, ite_false]
    exact continuous_const

/-- The resolvent of the flow is continuous in the sample off the real axis. -/
private lemma vertical_continuous_resolvent (g : ℝ) (W L : ℕ) (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    Continuous fun ω : Ω W L => resolventMat (flowH g W L u ω) z := by
  have hc : Continuous fun ω : Ω W L => flowH g W L u ω - z • (1 : Matrix _ _ ℂ) :=
    (vertical_continuous_flowH g W L u).sub continuous_const
  refine continuous_iff_continuousAt.2 fun ω => ?_
  have hu := isUnit_sub_smul_one (flowH_isHermitian g W L u ω) hz
  have hdet : (flowH g W L u ω - z • (1 : Matrix _ _ ℂ)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  refine (continuousAt_matrix_inv _ ?_).comp hc.continuousAt
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ hdet

private lemma vertical_continuous_segG (W : ℕ) (x : FlowPt × ℝ) (hy : 0 < x.2) :
    Continuous fun ω => segG W x ω :=
  vertical_continuous_resolvent _ _ _ _ (by simpa using hy.ne')

private lemma vertical_continuous_blockOf {W L : ℕ} {X : Type*} [TopologicalSpace X]
    {F : X → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hF : Continuous F) (a b : Fin L) :
    Continuous fun ω => blockOf (F ω) a b :=
  continuous_matrix fun α β => hF.matrix_elem (a, α) (b, β)

private lemma vertical_continuous_blockTr {W L : ℕ} {X : Type*} [TopologicalSpace X]
    {F : X → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hF : Continuous F) (a b : Fin L) :
    Continuous fun ω => blockTr (F ω) a b := by
  unfold blockTr
  exact continuous_const.mul (continuous_finsetSum _ fun α _ => hF.matrix_elem _ _)

/-- `‖G(Re z_u + iy)‖ ≤ y⁻¹`. -/
private lemma vertical_norm_segG_le (W : ℕ) (x : FlowPt × ℝ) (hy : 0 < x.2) (ω : Ω W x.1.L) :
    ‖segG W x ω‖ ≤ x.2⁻¹ :=
  norm_resolventMat_le (flowH_isHermitian _ _ _ _ ω) hy (by simp [abs_of_pos hy])

private lemma vertical_norm_blockOf_le {W L : ℕ}
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

private lemma vertical_norm_block_le (W : ℕ) (x : FlowPt × ℝ) (hy : 0 < x.2) (ω : Ω W x.1.L)
    (a b : Fin x.1.L) : ‖blockOf (segG W x ω) a b‖ ≤ x.2⁻¹ :=
  (vertical_norm_blockOf_le _ a b).trans (vertical_norm_segG_le W x hy ω)

/-- The range of Lemma 5.6 [fo:prop:inputs] at fixed time: `g ≥ C_κ`, `|E| ≤ 2 - κ`,
`ρ(W) g² log W ≤ L ≤ C_V g² W²` and `u ∈ [0, 1/2]`. -/
def initLarge (κ Cκ CV : ℝ) (ρ : ℕ → ℝ) (W : ℕ) : Set FlowPt :=
  {p | Cκ ≤ p.g ∧ |p.E| ≤ 2 - κ ∧ ρ W * p.g ^ 2 * Real.log W ≤ p.L ∧
    (p.L : ℝ) ≤ CV * p.g ^ 2 * (W : ℝ) ^ 2 ∧ 0 ≤ p.u ∧ p.u ≤ 1 / 2}

/-- (5.25) [fo:eq:coarse-resolvent-moments] on the vertical half-line `z = Re z_u + iy`,
`y ≥ η_u`, at early times `u ∈ [0, 1/2]`: `E‖G_{ab}(z)‖^p ≤ C_p` (Lemma 5.5
[fo:lem:resolvent-moments] at the coupling `g' = (c₀/y)^{1/2}`, which gives the same matrix). -/
theorem resolvent_moments_vert (κ C : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hC : 1 ≤ C) :
    ∃ Cκ : ℝ, 1 ≤ Cκ ∧ ∀ p : ℕ, 1 ≤ p → ∃ Cp : ℝ, 0 < Cp ∧ ∀ W : ℕ, 4 * p ≤ W →
      ∀ x : FlowPt × ℝ, Cκ ≤ x.1.g → 4 * x.1.g ^ 2 ≤ x.1.L → |x.1.E| ≤ 2 - κ →
      IsDysonRootV (hopB x.1.g) (gammaG x.1.g) x.1.L x.1.E (mRoot x.1.g x.1.L x.1.E) →
      ‖mRoot x.1.g x.1.L x.1.E‖ ≤ C → C⁻¹ ≤ (mRoot x.1.g x.1.L x.1.E).im → 0 ≤ x.1.u →
      x.1.u ≤ 1 / 2 → etaChar x.1.g (mRoot x.1.g x.1.L x.1.E) x.1.u ≤ x.2 → ∀ a b : Fin x.1.L,
        Integrable (fun ω => ‖blockOf (segG W x ω) a b‖ ^ p) (μ W x.1.L) ∧
        ∫ ω, ‖blockOf (segG W x ω) a b‖ ^ p ∂(μ W x.1.L) ≤ Cp := by
  obtain ⟨Cκχ, Cχ, hCκχ, hCχ, Hχ⟩ := char_large κ C hκ hκ2 hC
  set c₀ : ℝ := (2 * Cχ)⁻¹ with hc₀
  have hCχ0 : 0 < Cχ := by linarith
  have hc₀0 : 0 < c₀ := by positivity
  refine ⟨Cκχ, hCκχ, fun p hp => ?_⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  obtain ⟨Cm, hCm, Hm⟩ := resolvent_moments (κ / 2) (p : ℝ) c₀ (by linarith) hp0 hc₀0
  refine ⟨Cm * c₀ ^ (-(p : ℝ)) + (8 / (c₀ * κ)) ^ p, by positivity, ?_⟩
  intro W hW x hgC h4L hE _ hmC hmim hu0 hu1 hyη a b
  have hg1 : 1 ≤ x.1.g := hCκχ.trans hgC
  obtain ⟨hre, -, hη0, -, hgη⟩ := Hχ x.1.g hgC x.1.E (mRoot x.1.g x.1.L x.1.E) hE hmC hmim
    x.1.u hu0 (by linarith)
  have hy0 : 0 < x.2 := hη0.trans_le hyη
  have hgg : 0 < x.1.g ^ 2 := by positivity
  have hc₀y : c₀ ≤ x.1.g ^ 2 * x.2 := by
    have h1 : c₀ ≤ (1 - x.1.u) / Cχ := by
      rw [hc₀, mul_inv, div_eq_mul_inv]
      have : (2 : ℝ)⁻¹ ≤ 1 - x.1.u := by linarith
      have h0 : 0 ≤ Cχ⁻¹ := by positivity
      nlinarith
    exact h1.trans (hgη.trans (mul_le_mul_of_nonneg_left hyη hgg.le))
  by_cases hwin : x.2 ≤ c₀ * κ / 8
  · -- the reparametrized coupling `g'² = c₀/y`
    set g' : ℝ := Real.sqrt (c₀ / x.2) with hg'
    have hq0 : 0 < c₀ / x.2 := by positivity
    have hg'sq : g' ^ 2 = c₀ / x.2 := Real.sq_sqrt hq0.le
    have h8 : 8 / κ ≤ c₀ / x.2 := by
      rw [div_le_div_iff₀ hκ hy0]
      nlinarith
    have hg'2 : 2 / Real.sqrt (κ / 2) ≤ g' := by
      rw [hg', Real.le_sqrt (by positivity) hq0.le, div_pow,
        Real.sq_sqrt (by linarith : (0 : ℝ) ≤ κ / 2)]
      calc (2 : ℝ) ^ 2 / (κ / 2) = 8 / κ := by field_simp; norm_num
        _ ≤ _ := h8
    have hg'1 : 1 ≤ g' := by
      rw [hg', Real.one_le_sqrt]
      refine le_trans ?_ h8
      rw [le_div_iff₀ hκ]
      linarith
    have hg'g : g' ^ 2 ≤ x.1.g ^ 2 := by
      rw [hg'sq, div_le_iff₀ hy0]
      linarith
    have h4' : 4 * g' ^ 2 ≤ x.1.L := le_trans (by linarith) h4L
    set t : ℝ := x.1.u * g' ^ 2 / x.1.g ^ 2 with ht
    have ht0 : 0 ≤ t := by positivity
    have ht1 : t ≤ 1 := by
      rw [ht, div_le_iff₀ hgg]
      have : x.1.u * g' ^ 2 ≤ 1 * g' ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      linarith
    have hηC : x.2 ≤ c₀ / g' ^ 2 := by
      rw [hg'sq]
      field_simp
      rfl
    have hW' : 4 * (p : ℝ) ≤ W := by exact_mod_cast hW
    obtain ⟨hint, hbd⟩ := Hm W hW' x.1.L g' hg'2 h4' (zChar x.1.g x.1.E
      (mRoot x.1.g x.1.L x.1.E) x.1.u).re x.2 t hre hy0 hηC ht0 ht1 a b
    have hts : x.1.u * gammaG x.1.g = t * gammaG g' := by
      rw [vertical_gammaG hg1, vertical_gammaG hg'1, ht]
      have : g' ^ 2 ≠ 0 := by positivity
      field_simp
    have hmat : (fun ω => ‖blockOf (segG W x ω) a b‖ ^ p) = fun ω =>
        ‖blockOf (resolventMat (blockFlow W x.1.L (Ag g' x.1.L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
          (t * gammaG g') ω) (↑(zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re +
            ↑x.2 * Complex.I)) a b‖ ^ (p : ℝ) := by
      funext ω
      rw [Real.rpow_natCast]
      change ‖blockOf (resolventMat (flowH x.1.g W x.1.L x.1.u ω) _) a b‖ ^ p = _
      unfold flowH
      rw [vertical_Ag hg1, vertical_Ag hg'1, hts]
    have hc : g' ^ 2 * x.2 = c₀ := by rw [hg'sq]; field_simp
    rw [hmat]
    refine ⟨hint, hbd.trans ?_⟩
    rw [hc]
    exact le_add_of_nonneg_right (by positivity)
  · -- above the window: `‖G_{ab}‖ ≤ 1/y`
    replace hwin := not_le.mp hwin
    have hyinv : x.2⁻¹ ≤ 8 / (c₀ * κ) := by
      rw [inv_eq_one_div, div_le_div_iff₀ hy0 (by positivity)]
      linarith
    have hb : ∀ ω, ‖blockOf (segG W x ω) a b‖ ^ p ≤ (8 / (c₀ * κ)) ^ p := fun ω =>
      pow_le_pow_left₀ (norm_nonneg _) ((vertical_norm_block_le W x hy0 ω a b).trans hyinv) p
    have hint : Integrable (fun ω => ‖blockOf (segG W x ω) a b‖ ^ p) (μ W x.1.L) :=
      Integrable.of_bound (((vertical_continuous_blockOf (vertical_continuous_segG W x hy0) a
        b).norm.pow p).aestronglyMeasurable) ((8 / (c₀ * κ)) ^ p) (ae_of_all _ fun ω => by
          rw [Real.norm_of_nonneg (by positivity)]; exact hb ω)
    refine ⟨hint, ?_⟩
    calc ∫ ω, ‖blockOf (segG W x ω) a b‖ ^ p ∂(μ W x.1.L) ≤ ∫ _ω, (8 / (c₀ * κ)) ^ p ∂(μ W x.1.L) :=
          integral_mono hint (integrable_const _) hb
      _ = (8 / (c₀ * κ)) ^ p := by simp
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

/-! ### Equivariance, residuals at time zero and elementary inequalities -/

private lemma vertical_star_kron (W L : ℕ) (U : Matrix (Fin W) (Fin W) ℂ) :
    star ((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ U) = (1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ star U := by
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.star_eq_conjTranspose]

private lemma vertical_resolventMat_conj {n : Type*} [Fintype n] [DecidableEq n]
    (K B : Matrix n n ℂ) (z : ℂ) (h1 : K * star K = 1) (h2 : star K * K = 1) :
    resolventMat (K * B * star K) z = K * resolventMat B z * star K := by
  have e : K * B * star K - z • (1 : Matrix n n ℂ) = K * (B - z • (1 : Matrix n n ℂ)) * star K := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h1]
  have hK : K⁻¹ = star K := Matrix.inv_eq_left_inv h2
  have hK' : (star K)⁻¹ = K := Matrix.inv_eq_left_inv h1
  unfold resolventMat
  rw [e, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hK, hK']
  simp only [Matrix.mul_assoc]

/-- `G(Re z_u + iy)` is equivariant under common conjugation of the blocks. -/
private lemma vertical_segG_equiv (W : ℕ) (x : FlowPt × ℝ)
    (U : Matrix.unitaryGroup (Fin W) ℂ) (ω : Ω W x.1.L) :
    segG W x (conjMap W x.1.L U ω) =
      ((1 : Matrix (Fin x.1.L) (Fin x.1.L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ)) * segG W x ω *
        star ((1 : Matrix (Fin x.1.L) (Fin x.1.L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ)) := by
  have hUU : (U : Matrix (Fin W) (Fin W) ℂ) * star (U : Matrix (Fin W) (Fin W) ℂ) = 1 :=
    Unitary.coe_mul_star_self U
  have hUU' : star (U : Matrix (Fin W) (Fin W) ℂ) * (U : Matrix (Fin W) (Fin W) ℂ) = 1 :=
    Unitary.coe_star_mul_self U
  unfold segG
  rw [flowH_conjMap]
  refine vertical_resolventMat_conj _ _ _ ?_ ?_
  · rw [vertical_star_kron, ← Matrix.mul_kronecker_mul, Matrix.mul_one, hUU,
      Matrix.one_kronecker_one]
  · rw [vertical_star_kron, ← Matrix.mul_kronecker_mul, Matrix.mul_one, hUU',
      Matrix.one_kronecker_one]

/-- At `u = 0` the flow is `A_g ⊗ I`. -/
private lemma vertical_flowH_zero (g : ℝ) (W L : ℕ) (ω : Ω W L) :
    flowH g W L 0 ω = Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) := by
  simp [flowH, blockFlow]

/-- At `u = 0` the residual vanishes: `Π(G) = 1 + (z - A_g ⊗ I) G = 0`. -/
private lemma vertical_segRes_zero (W : ℕ) (x : FlowPt × ℝ) (hu : x.1.u = 0) (hy : 0 < x.2)
    (ω : Ω W x.1.L) (a b : Fin x.1.L) : segRes W x ω a b = 0 := by
  set z : ℂ := ((zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re : ℂ) +
    (x.2 : ℂ) * Complex.I with hz
  have hzim : z.im ≠ 0 := by simp [hz, hy.ne']
  set F := flowH x.1.g W x.1.L x.1.u ω with hFdef
  have hF : F = Ag x.1.g x.1.L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) := by
    rw [hFdef, hu]; exact vertical_flowH_zero _ _ _ _
  have h1 := sub_smul_mul_resolventMat (flowH_isHermitian x.1.g W x.1.L x.1.u ω) hzim
  rw [← hFdef] at h1
  have hG : segG W x ω = resolventMat F z := rfl
  have hP : resPi x.1.g x.1.u z (segG W x ω) = 0 := by
    unfold resPi
    rw [hG, hu, zero_mul, Complex.ofReal_zero, zero_smul, add_zero]
    have e : (z • (1 : Matrix (Fin x.1.L × Fin W) (Fin x.1.L × Fin W) ℂ) -
        Ag x.1.g x.1.L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) =
          -(F - z • (1 : Matrix (Fin x.1.L × Fin W) (Fin x.1.L × Fin W) ℂ)) := by
      rw [hF]; abel
    rw [e, Matrix.neg_mul, h1]
    abel
  unfold segRes
  rw [← hz, hP, Matrix.mul_zero]
  simp [blockTr]

/-- `(x + y)^n ≤ 2^n (x^n + y^n)` for `x, y ≥ 0`. -/
private lemma vertical_add_pow_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ) :
    (x + y) ^ n ≤ 2 ^ n * (x ^ n + y ^ n) := by
  have hm : x + y ≤ 2 * max x y := by
    have := le_max_left x y; have := le_max_right x y; linarith
  have h1 : (x + y) ^ n ≤ (2 * max x y) ^ n := pow_le_pow_left₀ (by positivity) hm n
  have h2 : max x y ^ n ≤ x ^ n + y ^ n := by
    rcases le_total x y with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg hx n]
    · rw [max_eq_left h]; linarith [pow_nonneg hy n]
  rw [mul_pow] at h1
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n]

/-- `(xy)^n ≤ x^{2n} + y^{2n}` for `x, y ≥ 0`. -/
private lemma vertical_mul_pow_le (x y : ℝ) (n : ℕ) :
    (x * y) ^ n ≤ x ^ (2 * n) + y ^ (2 * n) := by
  have ex : x ^ (2 * n) = (x ^ n) ^ 2 := by rw [← pow_mul, mul_comm]
  have ey : y ^ (2 * n) = (y ^ n) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [mul_pow, ex, ey]
  nlinarith [sq_nonneg (x ^ n - y ^ n)]

/-- The weighted power mean: `(Σ w_c Y_c)^p ≤ S^{p-1} Σ w_c Y_c^p` when `Σ w_c ≤ S`. -/
private lemma vertical_wsum_pow_le {ι : Type*} (s : Finset ι) (w Y : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hY : ∀ i, 0 ≤ Y i) {S : ℝ} (hS : ∑ i ∈ s, w i ≤ S) (p : ℕ)
    (hp : 1 ≤ p) : (∑ i ∈ s, w i * Y i) ^ p ≤ S ^ (p - 1) * ∑ i ∈ s, w i * Y i ^ p := by
  set T := ∑ i ∈ s, w i with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => hw i
  have hsum0 : 0 ≤ ∑ i ∈ s, w i * Y i ^ p :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (pow_nonneg (hY i) _)
  rcases eq_or_lt_of_le hT0 with h0 | hpos
  · have hw0 : ∀ i ∈ s, w i = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hw i).mp h0.symm
    rw [Finset.sum_eq_zero fun i hi => by rw [hw0 i hi, zero_mul], zero_pow (by omega)]
    exact mul_nonneg (pow_nonneg (hT0.trans hS) _) hsum0
  have key := Real.pow_arith_mean_le_arith_mean_pow s (fun i => w i / T) Y
    (fun i _ => div_nonneg (hw i) hT0) (by rw [← Finset.sum_div, div_self hpos.ne'])
    (fun i _ => hY i) p
  have e1 : ∑ i ∈ s, w i / T * Y i = T⁻¹ * ∑ i ∈ s, w i * Y i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i ∈ s, w i / T * Y i ^ p = T⁻¹ * ∑ i ∈ s, w i * Y i ^ p := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, mul_pow] at key
  have hTp : 0 < T ^ p := pow_pos hpos p
  have hTp' : T ^ p = T ^ (p - 1) * T := by rw [← pow_succ]; congr 1; omega
  have h3 : (∑ i ∈ s, w i * Y i) ^ p ≤ T ^ (p - 1) * ∑ i ∈ s, w i * Y i ^ p := by
    calc (∑ i ∈ s, w i * Y i) ^ p = T ^ p * (T⁻¹ ^ p * (∑ i ∈ s, w i * Y i) ^ p) := by
          rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hpos.ne', one_pow, one_mul]
      _ ≤ T ^ p * (T⁻¹ * ∑ i ∈ s, w i * Y i ^ p) := mul_le_mul_of_nonneg_left key hTp.le
      _ = T ^ (p - 1) * ∑ i ∈ s, w i * Y i ^ p := by
          rw [hTp', mul_assoc, mul_inv_cancel_left₀ hpos.ne']
  exact h3.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hT0 hS _) hsum0)


/-- The crude bound on the averaged residual combination of Proposition 7.10
[uvc:prop:residual-compression]: `|R_{ab}|^p` by block norms, with `|M_{ab}| ≤ Γ` and
`β Σ_c |M_{ac}| ≤ Γ`. -/
private lemma vertical_resComb_pow_le {W L : ℕ} (p : ℕ) (hp : 1 ≤ p) (β Γ : ℝ) (hβ : 0 ≤ β)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (M : Matrix (Fin L) (Fin L) ℂ)
    (hMe : ∀ a b, ‖M a b‖ ≤ Γ) (hMr : ∀ a, β * ∑ b, ‖M a b‖ ≤ Γ) (a b : Fin L) :
    ‖resComb β G M a b‖ ^ p ≤ 4 ^ p * (‖blockOf G a b‖ ^ p + Γ ^ p) +
      2 ^ p * Γ ^ (p - 1) * ∑ c, β * ‖M a c‖ * (4 ^ p * (‖blockOf G c c‖ ^ (2 * p) +
        Γ ^ (2 * p)) + ‖blockOf G c b‖ ^ (2 * p)) := by
  have hΓ : 0 ≤ Γ := (norm_nonneg _).trans (hMe a a)
  set N : Fin L → Fin L → ℝ := fun c d => ‖blockOf G c d‖ with hN
  have hN0 : ∀ c d, 0 ≤ N c d := fun c d => norm_nonneg _
  set w : Fin L → ℝ := fun c => β * ‖M a c‖ with hw
  have hw0 : ∀ c, 0 ≤ w c := fun c => mul_nonneg hβ (norm_nonneg _)
  set Y : Fin L → ℝ := fun c => (N c c + Γ) * N c b with hY
  have hY0 : ∀ c, 0 ≤ Y c := fun c => mul_nonneg (add_nonneg (hN0 c c) hΓ) (hN0 c b)
  have hwS : ∑ c, w c ≤ Γ := by rw [hw, ← Finset.mul_sum]; exact hMr a
  have hR : ‖resComb β G M a b‖ ≤ (N a b + Γ) + ∑ c, w c * Y c := by
    unfold resComb
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_neg]
      exact (norm_sub_le _ _).trans (add_le_add (vertical_blockTr_le G a b) (hMe a b))
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ]
      refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hβ).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun c _ => ?_
      rw [norm_mul, norm_mul]
      simp only [hw, hY]
      have h1 : ‖blockTr G c c - M c c‖ ≤ N c c + Γ :=
        (norm_sub_le _ _).trans (add_le_add (vertical_blockTr_le G c c) (hMe c c))
      have h2 : ‖blockTr G c b‖ ≤ N c b := vertical_blockTr_le G c b
      calc β * (‖M a c‖ * ‖blockTr G c c - M c c‖ * ‖blockTr G c b‖)
          ≤ β * (‖M a c‖ * (N c c + Γ) * N c b) := by gcongr
        _ = β * ‖M a c‖ * ((N c c + Γ) * N c b) := by ring
  have hA0 : 0 ≤ N a b + Γ := add_nonneg (hN0 a b) hΓ
  have hS0 : 0 ≤ ∑ c, w c * Y c := Finset.sum_nonneg fun c _ => mul_nonneg (hw0 c) (hY0 c)
  have h1 : ‖resComb β G M a b‖ ^ p ≤ 2 ^ p * ((N a b + Γ) ^ p + (∑ c, w c * Y c) ^ p) :=
    (pow_le_pow_left₀ (norm_nonneg _) hR p).trans (vertical_add_pow_le hA0 hS0 p)
  have h2 : (N a b + Γ) ^ p ≤ 2 ^ p * (N a b ^ p + Γ ^ p) := vertical_add_pow_le (hN0 a b) hΓ p
  have h3 := vertical_wsum_pow_le Finset.univ w Y hw0 hY0 hwS p hp
  have h4 : ∀ c, Y c ^ p ≤ 4 ^ p * (N c c ^ (2 * p) + Γ ^ (2 * p)) + N c b ^ (2 * p) := by
    intro c
    refine (vertical_mul_pow_le _ _ p).trans ?_
    have := vertical_add_pow_le (hN0 c c) hΓ (2 * p)
    rw [pow_mul (2 : ℝ), show (2 : ℝ) ^ 2 = 4 by norm_num] at this
    linarith
  have h5 : ∑ c, w c * Y c ^ p ≤ ∑ c, w c * (4 ^ p * (N c c ^ (2 * p) + Γ ^ (2 * p)) +
      N c b ^ (2 * p)) := Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (h4 c) (hw0 c)
  have hΓp : 0 ≤ Γ ^ (p - 1) := pow_nonneg hΓ _
  have h2p : (0 : ℝ) ≤ 2 ^ p := by positivity
  calc ‖resComb β G M a b‖ ^ p ≤ 2 ^ p * ((N a b + Γ) ^ p + (∑ c, w c * Y c) ^ p) := h1
    _ ≤ 2 ^ p * (2 ^ p * (N a b ^ p + Γ ^ p) + Γ ^ (p - 1) * ∑ c, w c * (4 ^ p *
        (N c c ^ (2 * p) + Γ ^ (2 * p)) + N c b ^ (2 * p))) := by
        gcongr
        exact h3.trans (mul_le_mul_of_nonneg_left h5 hΓp)
    _ = 4 ^ p * (N a b ^ p + Γ ^ p) + 2 ^ p * Γ ^ (p - 1) * ∑ c, w c * (4 ^ p *
        (N c c ^ (2 * p) + Γ ^ (2 * p)) + N c b ^ (2 * p)) := by
        rw [show (4 : ℝ) ^ p = 2 ^ p * 2 ^ p by rw [← mul_pow]; norm_num]
        ring

/-- The Dyson matrix at `Re z_u + iy` in the parametrization `r = y/γ_g`. -/
private lemma vertical_segMat_eq (g : ℝ) (L : ℕ) (x u y : ℝ) :
    segMat g L x u (y / gammaG g) = dysonMat (hopB g) (u * gammaG g) L
      ((x : ℂ) + (y : ℂ) * Complex.I)
      (mRootV (hopB g) (u * gammaG g) L ((x : ℂ) + (y : ℂ) * Complex.I)) := by
  unfold segMat
  rw [mul_div_cancel₀ _ (vertical_gammaG_pos g).ne']

private lemma vertical_continuous_resPi {W L : ℕ} (g u : ℝ) (z : ℂ) {X : Type*}
    [TopologicalSpace X] {F : X → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hF : Continuous F) :
    Continuous fun ω => resPi g u z (F ω) := by
  unfold resPi
  have hd : Continuous fun ω => (Matrix.diagonal fun x : Fin L × Fin W => blockTr (F ω) x.1 x.1) :=
    continuous_matrix fun i j => by
      simp only [Matrix.diagonal_apply]
      split_ifs
      · exact vertical_continuous_blockTr hF _ _
      · exact continuous_const
  have h2 : Continuous fun ω => ((u * gammaG g : ℝ) : ℂ) •
      ((Matrix.diagonal fun x : Fin L × Fin W => blockTr (F ω) x.1 x.1) * F ω) :=
    continuous_matrix fun i j => by
      simp only [Matrix.smul_apply, smul_eq_mul]
      exact continuous_const.mul ((hd.matrix_mul hF).matrix_elem i j)
  exact (continuous_const.add (continuous_const.matrix_mul hF)).add h2

private lemma vertical_continuous_segRes (W : ℕ) (x : FlowPt × ℝ) (hy : 0 < x.2)
    (a b : Fin x.1.L) : Continuous fun ω => segRes W x ω a b := by
  unfold segRes
  exact vertical_continuous_blockTr (continuous_const.matrix_mul
    (vertical_continuous_resPi _ _ _ (vertical_continuous_segG W x hy))) a b


private lemma vertical_rpow_le_max {X K r : ℝ} (hX : 0 ≤ X) (hXK : X ≤ K) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) : X ^ r ≤ max 1 K := by
  rcases le_total X 1 with h | h
  · exact (Real.rpow_le_one hX h hr0).trans (le_max_left _ _)
  · calc X ^ r ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hr1
      _ = X := Real.rpow_one X
      _ ≤ max 1 K := hXK.trans (le_max_right _ _)

private lemma vertical_root_le {X K : ℝ} (W : ℕ) (hW : 1 ≤ W) (p : ℕ) (hp : 1 ≤ p) (hX : 0 ≤ X)
    (hK : 0 ≤ K) (h : X ≤ K * ((W : ℝ) ^ (2 * p))⁻¹) :
    X ^ (1 / (2 * ((2 * p : ℕ) : ℝ))) ≤
      K ^ (1 / (2 * ((2 * p : ℕ) : ℝ))) * (W : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  set r : ℝ := 1 / (2 * ((2 * p : ℕ) : ℝ)) with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  calc X ^ r ≤ (K * ((W : ℝ) ^ (2 * p))⁻¹) ^ r := Real.rpow_le_rpow hX h hr0
    _ = K ^ r * (((W : ℝ) ^ (2 * p)) ^ r)⁻¹ := by
        rw [Real.mul_rpow hK (by positivity), Real.inv_rpow (by positivity)]
    _ = K ^ r * (W : ℝ) ^ (-(1 / 2 : ℝ)) := by
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le, Real.rpow_neg hW0.le]
        congr 2
        rw [hr]
        push_cast
        field_simp

/-- `a ≤ (t a² + t⁻¹)/2` for `t > 0`. -/
private lemma vertical_amgm (a t : ℝ) (ht : 0 < t) : a ≤ (t * a ^ 2 + t⁻¹) / 2 := by
  have h := sq_nonneg (t * a - 1)
  have : 2 * t * a ≤ t ^ 2 * a ^ 2 + 1 := by nlinarith
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have ht' : t * (t * a ^ 2 + t⁻¹) = t ^ 2 * a ^ 2 + 1 := by field_simp
  nlinarith

/-- (7.27) [gc:eq:haar-fixed-moment] on the vertical half-line at early times, at every order. -/
private lemma vertical_Z_moment (κ C : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hC : 1 ≤ C) :
    ∃ Cκ : ℝ, 1 ≤ Cκ ∧ ∀ p : ℕ, 1 ≤ p → ∃ Cp : ℝ, 0 < Cp ∧ ∀ W : ℕ, 8 * p ≤ W →
      ∀ x : FlowPt × ℝ, Cκ ≤ x.1.g → 4 * x.1.g ^ 2 ≤ x.1.L → |x.1.E| ≤ 2 - κ →
      IsDysonRootV (hopB x.1.g) (gammaG x.1.g) x.1.L x.1.E (mRoot x.1.g x.1.L x.1.E) →
      ‖mRoot x.1.g x.1.L x.1.E‖ ≤ C → C⁻¹ ≤ (mRoot x.1.g x.1.L x.1.E).im → 0 ≤ x.1.u →
      x.1.u ≤ 1 / 2 → etaChar x.1.g (mRoot x.1.g x.1.L x.1.E) x.1.u ≤ x.2 → ∀ a b : Fin x.1.L,
      ∀ i j : Fin W,
        Integrable (fun ω => ‖segG W x ω (a, i) (b, j) -
          if i = j then blockTr (segG W x ω) a b else 0‖ ^ (2 * p)) (μ W x.1.L) ∧
        ∫ ω, ‖segG W x ω (a, i) (b, j) - if i = j then blockTr (segG W x ω) a b else 0‖ ^ (2 * p)
          ∂(μ W x.1.L) ≤ Cp * ((W : ℝ) ^ p)⁻¹ := by
  obtain ⟨Cκ, hCκ, H⟩ := resolvent_moments_vert κ C hκ hκ2 hC
  refine ⟨Cκ, hCκ, fun p hp => ?_⟩
  obtain ⟨C2, hC2, H2⟩ := H (2 * p) (by omega)
  obtain ⟨CH, hCH, HH⟩ := haar_traceless_moment p
  refine ⟨CH * C2, by positivity, ?_⟩
  intro W hW x hgC h4L hE hroot hmC hmim hu0 hu1 hyη a b i j
  have hW1 : 1 ≤ W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hC0 : 0 < C⁻¹ := by positivity
  have hmpos : 0 < (mRoot x.1.g x.1.L x.1.E).im := lt_of_lt_of_le hC0 hmim
  have hy0 : 0 < x.2 := (etaChar_pos _ _ hmpos (by linarith)).trans_le hyη
  have hcont := vertical_continuous_segG W x hy0
  have hFm : ∀ p q, Measurable fun ω => segG W x ω p q := fun p q =>
    (hcont.matrix_elem p q).measurable
  have hHS0 : ∀ ω, 0 ≤ blockHS2 (segG W x ω) a b := fun ω => by unfold blockHS2; positivity
  have hHSc : Continuous fun ω => blockHS2 (segG W x ω) a b := by
    unfold blockHS2
    exact continuous_finsetSum _ fun α _ => continuous_finsetSum _ fun β _ =>
      (hcont.matrix_elem _ _).norm.pow 2
  have hHSb : ∀ ω, blockHS2 (segG W x ω) a b ^ p ≤ ((W : ℝ) * (x.2⁻¹) ^ 2) ^ p := fun ω =>
    pow_le_pow_left₀ (hHS0 ω) ((vertical_blockHS2_le _ a b).trans (by
      gcongr; exact vertical_norm_block_le W x hy0 ω a b)) p
  have hint : Integrable (fun ω => blockHS2 (segG W x ω) a b ^ p) (μ W x.1.L) :=
    Integrable.of_bound (hHSc.pow p).aestronglyMeasurable _ (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (pow_nonneg (hHS0 ω) _)]; exact hHSb ω)
  obtain ⟨hZi, hZb⟩ := HH W x.1.L hW1 (segG W x) hFm (vertical_segG_equiv W x) a b hint i j
  obtain ⟨hGi, hGb⟩ := H2 W (by omega) x hgC h4L hE hroot hmC hmim hu0 hu1 hyη a b
  refine ⟨hZi, hZb.trans ?_⟩
  have hHS : ∫ ω, blockHS2 (segG W x ω) a b ^ p ∂(μ W x.1.L) ≤ (W : ℝ) ^ p * C2 := by
    calc _ ≤ ∫ ω, (W : ℝ) ^ p * ‖blockOf (segG W x ω) a b‖ ^ (2 * p) ∂(μ W x.1.L) := by
          refine integral_mono hint (hGi.const_mul _) fun ω => ?_
          calc blockHS2 (segG W x ω) a b ^ p ≤ ((W : ℝ) * ‖blockOf (segG W x ω) a b‖ ^ 2) ^ p :=
                pow_le_pow_left₀ (hHS0 ω) (vertical_blockHS2_le _ a b) p
            _ = _ := by rw [mul_pow, ← pow_mul, mul_comm 2 p]
      _ = (W : ℝ) ^ p * ∫ ω, ‖blockOf (segG W x ω) a b‖ ^ (2 * p) ∂(μ W x.1.L) :=
          integral_const_mul _ _
      _ ≤ (W : ℝ) ^ p * C2 := mul_le_mul_of_nonneg_left hGb (by positivity)
  have hWp : (0 : ℝ) < (W : ℝ) ^ p := by positivity
  calc CH / (W : ℝ) ^ (2 * p) * ∫ ω, blockHS2 (segG W x ω) a b ^ p ∂(μ W x.1.L)
      ≤ CH / (W : ℝ) ^ (2 * p) * ((W : ℝ) ^ p * C2) :=
        mul_le_mul_of_nonneg_left hHS (by positivity)
    _ = CH * C2 * ((W : ℝ) ^ p)⁻¹ := by
        rw [show (W : ℝ) ^ (2 * p) = ((W : ℝ) ^ p) ^ 2 by rw [← pow_mul, mul_comm]]
        field_simp

/-- Moments on the vertical half-line at early times: traceless entries
`E|G_{ai,bj} - δ_{ij}⟨G⟩_{ab}|^{2p} ≤ C_p W^{-p}` ((7.27) [gc:eq:haar-fixed-moment]) and
residuals `E|R_{ab}|^p ≤ C_p W^{-p}` ((7.26) [gc:eq:residual-fixed-moment] with `K = C`,
`χ = W^{-1/2}`). -/
theorem vert_moments (κ C : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hC : 1 ≤ C) :
    ∃ Cκ R : ℝ, 1 ≤ Cκ ∧ 0 < R ∧ ∀ p : ℕ, 1 ≤ p → ∃ Cp : ℝ, 0 < Cp ∧ ∀ W : ℕ, 8 * p ≤ W →
      ∀ x : FlowPt × ℝ, Cκ ≤ x.1.g → R * x.1.g ^ 2 ≤ x.1.L → |x.1.E| ≤ 2 - κ →
      IsDysonRootV (hopB x.1.g) (gammaG x.1.g) x.1.L x.1.E (mRoot x.1.g x.1.L x.1.E) →
      ‖mRoot x.1.g x.1.L x.1.E‖ ≤ C → C⁻¹ ≤ (mRoot x.1.g x.1.L x.1.E).im → 0 ≤ x.1.u →
      x.1.u ≤ 1 / 2 → etaChar x.1.g (mRoot x.1.g x.1.L x.1.E) x.1.u ≤ x.2 → ∀ a b : Fin x.1.L,
        (∀ i j : Fin W,
          Integrable (fun ω => ‖segG W x ω (a, i) (b, j) -
            if i = j then blockTr (segG W x ω) a b else 0‖ ^ (2 * p)) (μ W x.1.L) ∧
          ∫ ω, ‖segG W x ω (a, i) (b, j) - if i = j then blockTr (segG W x ω) a b else 0‖ ^ (2 * p)
            ∂(μ W x.1.L) ≤ Cp * ((W : ℝ) ^ p)⁻¹) ∧
        Integrable (fun ω => ‖segRes W x ω a b‖ ^ p) (μ W x.1.L) ∧
        ∫ ω, ‖segRes W x ω a b‖ ^ p ∂(μ W x.1.L) ≤ Cp * ((W : ℝ) ^ p)⁻¹ := by
  obtain ⟨Cκ₁, hCκ₁, H₁⟩ := resolvent_moments_vert κ C hκ hκ2 hC
  obtain ⟨Cκ₂, hCκ₂, H₂⟩ := vertical_Z_moment κ C hκ hκ2 hC
  obtain ⟨Cκ₃, R₃, c₃, Γ, hCκ₃, hR₃, -, hΓ, H₃⟩ := dysonVert_large κ hκ hκ2
  refine ⟨max (max Cκ₁ Cκ₂) Cκ₃, max R₃ 4, le_trans hCκ₁ (le_trans (le_max_left _ _)
    (le_max_left _ _)), lt_of_lt_of_le (by norm_num) (le_max_right _ _), fun p hp => ?_⟩
  obtain ⟨Cp1, hCp1, Hp1⟩ := H₁ p hp
  obtain ⟨C2p1, hC2p1, H2p1⟩ := H₁ (2 * p) (by omega)
  obtain ⟨C4p1, hC4p1, H4p1⟩ := H₁ (4 * p) (by omega)
  obtain ⟨CZp, hCZp, HZp⟩ := H₂ p hp
  obtain ⟨CZ2p, hCZ2p, HZ2p⟩ := H₂ (2 * p) (by omega)
  set CK : ℝ := max (max 1 C4p1) (CZ2p ^ (1 / (2 * ((2 * p : ℕ) : ℝ)))) with hCK
  have hCK1 : 1 ≤ CK := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCK0 : 0 < CK := lt_of_lt_of_le one_pos hCK1
  obtain ⟨Cres, hCres, Hres⟩ :=
    residual_moment (2 * p) (by omega) (even_two_mul p) CK Γ hCK0 hΓ
  set Kc : ℝ := 4 ^ p * (Cp1 + Γ ^ p) +
    2 ^ p * Γ ^ (p - 1) * (Γ * (4 ^ p * (C2p1 + Γ ^ (2 * p)) + C2p1)) with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  refine ⟨CZp + ((Cres + 1) / 2 + Kc * (16 * p) ^ p), by positivity, ?_⟩
  intro W hW x hgC hRL hE hroot hmC hmim hu0 hu1 hyη a b
  have hgC₁ : Cκ₁ ≤ x.1.g := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hgC
  have hgC₂ : Cκ₂ ≤ x.1.g := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hgC
  have hgC₃ : Cκ₃ ≤ x.1.g := le_trans (le_max_right _ _) hgC
  have hg1 : 1 ≤ x.1.g := hCκ₁.trans hgC₁
  have h4L : 4 * x.1.g ^ 2 ≤ x.1.L := le_trans (by gcongr; exact le_max_right _ _) hRL
  have hR3L : R₃ * x.1.g ^ 2 ≤ x.1.L := le_trans (by gcongr; exact le_max_left _ _) hRL
  have hW1 : 1 ≤ W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hC0 : 0 < C⁻¹ := by positivity
  have hmpos : 0 < (mRoot x.1.g x.1.L x.1.E).im := lt_of_lt_of_le hC0 hmim
  have hy0 : 0 < x.2 := (etaChar_pos _ _ hmpos (by linarith)).trans_le hyη
  have hWp : (0 : ℝ) < (W : ℝ) ^ p := by positivity
  have hle : ∀ X : ℝ, 0 ≤ X → X ≤ (CZp + ((Cres + 1) / 2 + X)) := fun X hX => by
    have : 0 ≤ CZp + (Cres + 1) / 2 := by positivity
    linarith
  refine ⟨fun i j => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := HZp W hW x hgC₂ h4L hE hroot hmC hmim hu0 hu1 hyη a b i j
    refine ⟨h1, h2.trans (mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr hWp.le))⟩
    have : 0 ≤ (Cres + 1) / 2 + Kc * (16 * p) ^ p := by positivity
    linarith
  -- the residual
  obtain ⟨hmu0, hmuC, hMe, hMr, -, -, -⟩ := H₃ x.1.g hgC₃ x.1.L hR3L x.1.E hE
    (mRoot x.1.g x.1.L x.1.E) hroot x.1.u hu0 hu1 x.2 hyη
  have hγy : gammaG x.1.g * (x.2 / gammaG x.1.g) = x.2 :=
    mul_div_cancel₀ _ (vertical_gammaG_pos x.1.g).ne'
  set re : ℝ := (zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re with hre
  set z : ℂ := (re : ℂ) + (x.2 : ℂ) * Complex.I with hz
  have hzim : 0 < z.im := by simp [hz, hy0]
  set mu : ℂ := mRootV (hopB x.1.g) (x.1.u * gammaG x.1.g) x.1.L z with hmu
  set M : Matrix (Fin x.1.L) (Fin x.1.L) ℂ :=
    dysonMat (hopB x.1.g) (x.1.u * gammaG x.1.g) x.1.L z mu with hM
  have hseg : segMat x.1.g x.1.L re x.1.u (x.2 / gammaG x.1.g) = M :=
    vertical_segMat_eq _ _ _ _ _
  simp only [hγy] at hmu0 hmuC
  rw [hseg] at hMe hMr
  have hcR := vertical_continuous_segRes W x hy0 a b
  have hRc : Continuous fun ω => ‖segRes W x ω a b‖ ^ p := hcR.norm.pow p
  by_cases hW16 : 16 * p ≤ W
  · -- the Gaussian expansion at order `2p`
    have hb1 : ∀ c d : Fin x.1.L, (∫ ω, ‖blockTr (resolventMat (flowH x.1.g W x.1.L x.1.u ω) z)
        c d‖ ^ (2 * (2 * p)) ∂(μ W x.1.L)) ^ (1 / (2 * ((2 * p : ℕ) : ℝ))) ≤ CK * 1 := by
      intro c d
      obtain ⟨hi, hb⟩ := H4p1 W (by omega) x hgC₁ h4L hE hroot hmC hmim hu0 hu1 hyη c d
      rw [show 2 * (2 * p) = 4 * p by ring, mul_one]
      have hI : ∫ ω, ‖blockTr (resolventMat (flowH x.1.g W x.1.L x.1.u ω) z) c d‖ ^ (4 * p)
          ∂(μ W x.1.L) ≤ C4p1 :=
        (integral_mono_of_nonneg (ae_of_all _ fun ω => by positivity) hi
          (ae_of_all _ fun ω => pow_le_pow_left₀ (norm_nonneg _)
            (vertical_blockTr_le _ c d) _)).trans hb
      refine (vertical_rpow_le_max (integral_nonneg fun ω => by positivity) hI (by positivity)
        ?_).trans (le_max_left _ _)
      rw [div_le_one (by positivity)]
      push_cast
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    have hb2 : ∀ e₁ e₂ : Fin x.1.L × Fin W, (∫ ω, ‖resolventMat (flowH x.1.g W x.1.L x.1.u ω) z
        e₁ e₂ - if e₁.2 = e₂.2 then blockTr (resolventMat (flowH x.1.g W x.1.L x.1.u ω) z) e₁.1
          e₂.1 else 0‖ ^ (2 * (2 * p)) ∂(μ W x.1.L)) ^ (1 / (2 * ((2 * p : ℕ) : ℝ))) ≤
          CK * 1 * (W : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rintro ⟨c, i⟩ ⟨d, j⟩
      obtain ⟨-, hb⟩ := HZ2p W (by omega) x hgC₂ h4L hE hroot hmC hmim hu0 hu1 hyη c d i j
      refine (vertical_root_le W hW1 p hp (integral_nonneg fun ω => by positivity) hCZ2p.le
        hb).trans ?_
      rw [mul_one]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    obtain ⟨hRi, hRb⟩ := Hres W x.1.L hW1 x.1.g x.1.u hu0 z mu hzim hmu0 hmuC hMe hMr 1
      ((W : ℝ) ^ (-(1 / 2 : ℝ))) le_rfl le_rfl hb1 hb2 a b
    have hfun : (fun ω => ‖segRes W x ω a b‖) = fun ω => ‖blockTr ((M ⊗ₖ
        (1 : Matrix (Fin W) (Fin W) ℂ)) * resPi x.1.g x.1.u z
          (resolventMat (flowH x.1.g W x.1.L x.1.u ω) z)) a b‖ := by
      funext ω
      unfold segRes segM
      rw [hseg]
      rfl
    have hχ : (1 : ℝ) ^ 2 * ((W : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (W : ℝ)⁻¹ := by
      rw [one_pow, one_mul, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
      norm_num
      exact Real.rpow_neg_one _
    rw [hχ] at hRb
    set t : ℝ := (W : ℝ) ^ p with ht
    have hdom : ∀ ω, ‖segRes W x ω a b‖ ^ p ≤ (t * ‖segRes W x ω a b‖ ^ (2 * p) + t⁻¹) / 2 :=
      fun ω => by
        have := vertical_amgm (‖segRes W x ω a b‖ ^ p) t hWp
        rwa [← pow_mul, mul_comm p 2] at this
    have hRi' : Integrable (fun ω => ‖segRes W x ω a b‖ ^ (2 * p)) (μ W x.1.L) := by
      have : (fun ω => ‖segRes W x ω a b‖ ^ (2 * p)) = fun ω => ‖blockTr ((M ⊗ₖ
          (1 : Matrix (Fin W) (Fin W) ℂ)) * resPi x.1.g x.1.u z
            (resolventMat (flowH x.1.g W x.1.L x.1.u ω) z)) a b‖ ^ (2 * p) := by
        funext ω; rw [congrFun hfun ω]
      rw [this]; exact hRi
    have hRb' : ∫ ω, ‖segRes W x ω a b‖ ^ (2 * p) ∂(μ W x.1.L) ≤ Cres * ((W : ℝ)⁻¹) ^ (2 * p) := by
      have : (fun ω => ‖segRes W x ω a b‖ ^ (2 * p)) = fun ω => ‖blockTr ((M ⊗ₖ
          (1 : Matrix (Fin W) (Fin W) ℂ)) * resPi x.1.g x.1.u z
            (resolventMat (flowH x.1.g W x.1.L x.1.u ω) z)) a b‖ ^ (2 * p) := by
        funext ω; rw [congrFun hfun ω]
      rw [this]; exact hRb
    have hgi : Integrable (fun ω => (t * ‖segRes W x ω a b‖ ^ (2 * p) + t⁻¹) / 2) (μ W x.1.L) :=
      ((hRi'.const_mul t).add (integrable_const _)).div_const 2
    have hint : Integrable (fun ω => ‖segRes W x ω a b‖ ^ p) (μ W x.1.L) :=
      Integrable.mono' hgi hRc.aestronglyMeasurable (ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (by positivity)]; exact hdom ω)
    refine ⟨hint, ?_⟩
    calc ∫ ω, ‖segRes W x ω a b‖ ^ p ∂(μ W x.1.L)
        ≤ ∫ ω, (t * ‖segRes W x ω a b‖ ^ (2 * p) + t⁻¹) / 2 ∂(μ W x.1.L) :=
          integral_mono hint hgi hdom
      _ = (t * ∫ ω, ‖segRes W x ω a b‖ ^ (2 * p) ∂(μ W x.1.L) + t⁻¹) / 2 := by
          rw [integral_div, integral_add (hRi'.const_mul t) (integrable_const _),
            integral_const_mul]
          simp
      _ ≤ (t * (Cres * ((W : ℝ)⁻¹) ^ (2 * p)) + t⁻¹) / 2 := by gcongr
      _ = (Cres + 1) / 2 * t⁻¹ := by
          rw [show ((W : ℝ)⁻¹) ^ (2 * p) = (t⁻¹) ^ 2 by rw [ht, ← inv_pow, ← pow_mul, mul_comm]]
          field_simp
      _ ≤ (CZp + ((Cres + 1) / 2 + Kc * (16 * p) ^ p)) * ((W : ℝ) ^ p)⁻¹ := by
          rw [← ht]
          refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr hWp.le)
          have : 0 ≤ Kc * (16 * (p : ℝ)) ^ p := by positivity
          linarith
  · -- the crude bound `E|R|^p ≤ K` for `8p ≤ W < 16p`
    replace hW16 := not_le.mp hW16
    have hWl : (W : ℝ) ^ p ≤ (16 * p : ℝ) ^ p :=
      pow_le_pow_left₀ hW0.le (by exact_mod_cast hW16.le) p
    have hfin : Kc ≤ Kc * (16 * p : ℝ) ^ p * ((W : ℝ) ^ p)⁻¹ := by
      rw [mul_assoc]
      refine le_mul_of_one_le_right hKc0 ?_
      rw [le_mul_inv_iff₀ hWp, one_mul]
      exact hWl
    have hfin' : Kc ≤ (CZp + ((Cres + 1) / 2 + Kc * (16 * p) ^ p)) * ((W : ℝ) ^ p)⁻¹ := by
      refine hfin.trans (mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr hWp.le))
      have : 0 ≤ CZp + (Cres + 1) / 2 := by positivity
      linarith
    rcases eq_or_lt_of_le hu0 with hu | hu
    · have h0 : (fun ω => ‖segRes W x ω a b‖ ^ p) = fun _ => (0 : ℝ) := by
        funext ω
        rw [vertical_segRes_zero W x hu.symm hy0 ω a b, norm_zero, zero_pow (by omega)]
      rw [h0]
      refine ⟨integrable_const _, ?_⟩
      rw [integral_zero]
      exact hKc0.trans hfin'
    -- `u > 0`: the residual is `resComb`
    have hL3 : 3 ≤ x.1.L := by
      have h1 : (1 : ℝ) ≤ x.1.g ^ 2 := one_le_pow₀ hg1
      have : (3 : ℝ) ≤ x.1.L := by linarith
      exact_mod_cast this
    have hβ : 0 ≤ x.1.u * gammaG x.1.g := mul_nonneg hu0 (vertical_gammaG_pos _).le
    have hMr' : ∀ a, x.1.u * gammaG x.1.g * ∑ b, ‖M a b‖ ≤ Γ := fun a =>
      le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ =>
        le_add_of_nonneg_right (sq_nonneg _)) hβ) (hMr a)
    have hid : ∀ ω, segRes W x ω a b = resComb (x.1.u * gammaG x.1.g) (segG W x ω) M a b := by
      intro ω
      rw [segRes_identity W hW1 x (by linarith) hL3 hu hy0 ω a b, hseg]
    set N : Fin x.1.L → Fin x.1.L → Ω W x.1.L → ℝ := fun c d ω => ‖blockOf (segG W x ω) c d‖
      with hN
    have hNp : Integrable (N a b · ^ p) (μ W x.1.L) :=
      (Hp1 W (by omega) x hgC₁ h4L hE hroot hmC hmim hu0 hu1 hyη a b).1
    have hNpb : ∫ ω, N a b ω ^ p ∂(μ W x.1.L) ≤ Cp1 :=
      (Hp1 W (by omega) x hgC₁ h4L hE hroot hmC hmim hu0 hu1 hyη a b).2
    have hN2 : ∀ c d, Integrable (N c d · ^ (2 * p)) (μ W x.1.L) := fun c d =>
      (H2p1 W (by omega) x hgC₁ h4L hE hroot hmC hmim hu0 hu1 hyη c d).1
    have hN2b : ∀ c d, ∫ ω, N c d ω ^ (2 * p) ∂(μ W x.1.L) ≤ C2p1 := fun c d =>
      (H2p1 W (by omega) x hgC₁ h4L hE hroot hmC hmim hu0 hu1 hyη c d).2
    set w : Fin x.1.L → ℝ := fun c => x.1.u * gammaG x.1.g * ‖M a c‖ with hw
    have hw0 : ∀ c, 0 ≤ w c := fun c => mul_nonneg hβ (norm_nonneg _)
    have hwS : ∑ c, w c ≤ Γ := by rw [hw, ← Finset.mul_sum]; exact hMr' a
    set F : Fin x.1.L → Ω W x.1.L → ℝ := fun c ω =>
      4 ^ p * (N c c ω ^ (2 * p) + Γ ^ (2 * p)) + N c b ω ^ (2 * p) with hF
    have hF1 : ∀ c, Integrable (fun ω => 4 ^ p * (N c c ω ^ (2 * p) + Γ ^ (2 * p)))
        (μ W x.1.L) := fun c => ((hN2 c c).add (integrable_const _)).const_mul _
    have hFi : ∀ c, Integrable (F c) (μ W x.1.L) := fun c => (hF1 c).add (hN2 c b)
    have hFb : ∀ c, ∫ ω, F c ω ∂(μ W x.1.L) ≤ 4 ^ p * (C2p1 + Γ ^ (2 * p)) + C2p1 := by
      intro c
      simp only [hF]
      rw [integral_add (hF1 c) (hN2 c b), integral_const_mul,
        integral_add (hN2 c c) (integrable_const _)]
      simp only [integral_const, probReal_univ, one_smul]
      gcongr
      · exact hN2b c c
      · exact hN2b c b
    set B : Ω W x.1.L → ℝ := fun ω => 4 ^ p * (N a b ω ^ p + Γ ^ p) +
      2 ^ p * Γ ^ (p - 1) * ∑ c, w c * F c ω with hB
    have hB1 : Integrable (fun ω => 4 ^ p * (N a b ω ^ p + Γ ^ p)) (μ W x.1.L) :=
      (hNp.add (integrable_const _)).const_mul _
    have hB2' : Integrable (fun ω => ∑ c, w c * F c ω) (μ W x.1.L) :=
      integrable_finsetSum _ fun c _ => (hFi c).const_mul (w c)
    have hB2 : Integrable (fun ω => 2 ^ p * Γ ^ (p - 1) * ∑ c, w c * F c ω) (μ W x.1.L) :=
      hB2'.const_mul _
    have hBi : Integrable B (μ W x.1.L) := hB1.add hB2
    have hBb : ∫ ω, B ω ∂(μ W x.1.L) ≤ Kc := by
      simp only [hB]
      rw [integral_add hB1 hB2, integral_const_mul, integral_const_mul,
        integral_add hNp (integrable_const _),
        integral_finsetSum _ fun c _ => (hFi c).const_mul (w c)]
      simp only [integral_const_mul, integral_const, probReal_univ, one_smul]
      rw [hKc]
      have hsum : ∑ c, w c * ∫ ω, F c ω ∂(μ W x.1.L) ≤
          Γ * (4 ^ p * (C2p1 + Γ ^ (2 * p)) + C2p1) := by
        calc ∑ c, w c * ∫ ω, F c ω ∂(μ W x.1.L) ≤
              ∑ c, w c * (4 ^ p * (C2p1 + Γ ^ (2 * p)) + C2p1) :=
              Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hFb c) (hw0 c)
          _ = (∑ c, w c) * (4 ^ p * (C2p1 + Γ ^ (2 * p)) + C2p1) := by rw [Finset.sum_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_right hwS (by positivity)
      have h2 : (0 : ℝ) ≤ 2 ^ p * Γ ^ (p - 1) := by positivity
      gcongr
    have hdom : ∀ ω, ‖segRes W x ω a b‖ ^ p ≤ B ω := by
      intro ω
      rw [hid ω]
      exact vertical_resComb_pow_le p hp _ Γ hβ (segG W x ω) M hMe hMr' a b
    have hint : Integrable (fun ω => ‖segRes W x ω a b‖ ^ p) (μ W x.1.L) :=
      Integrable.mono' hBi hRc.aestronglyMeasurable (ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (by positivity)]; exact hdom ω)
    exact ⟨hint, (integral_mono hint hBi hdom).trans (hBb.trans hfin')⟩

/-! ### The free coefficients and the anchor interpolation -/

/-- `sin ϑ ≥ κ/2` for `2 cos ϑ = E`, `|E| ≤ 2 - κ`. -/
private lemma vertical_sin_ge {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ) :
    κ / 2 ≤ Real.sin (Real.arccos (E / 2)) := by
  rw [Real.sin_arccos]
  have hE2 : (E / 2) ^ 2 ≤ (1 - κ / 2) ^ 2 := by
    rw [div_pow, ← sq_abs]
    have : |E| / 2 ≤ 1 - κ / 2 := by linarith
    have h0 : 0 ≤ |E| / 2 := by positivity
    calc |E| ^ 2 / 2 ^ 2 = (|E| / 2) ^ 2 := by ring
      _ ≤ _ := pow_le_pow_left₀ h0 this 2
  have h1 : (κ / 2) ^ 2 ≤ 1 - (E / 2) ^ 2 := by nlinarith
  calc κ / 2 = Real.sqrt ((κ / 2) ^ 2) := (Real.sqrt_sq (by linarith)).symm
    _ ≤ _ := Real.sqrt_le_sqrt h1

private lemma vertical_inv_sin_le {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ) :
    (Real.sin (Real.arccos (E / 2)))⁻¹ ≤ 2 / κ := by
  have h := vertical_sin_ge hκ hκ2 hE
  rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) hκ]
  linarith

private lemma vertical_coef_abs_le {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (n : ℕ) {L : ℕ} (a α : Fin L) : |cellCoef n E a α| ≤ 2 / κ := by
  have hs := vertical_sin_ge hκ hκ2 hE
  have hs0 : 0 < Real.sin (Real.arccos (E / 2)) := by linarith
  have hk := vertical_inv_sin_le hκ hκ2 hE
  have hb : ∀ t : ℝ, |Real.sin t / Real.sin (Real.arccos (E / 2))| ≤ 2 / κ := fun t => by
    rw [abs_div, abs_of_pos hs0, div_eq_mul_inv]
    calc |Real.sin t| * (Real.sin (Real.arccos (E / 2)))⁻¹ ≤ 1 * (2 / κ) :=
          mul_le_mul (Real.abs_sin_le_one t) hk (by positivity) zero_le_one
      _ = 2 / κ := one_mul _
  unfold cellCoef
  split_ifs
  · exact hb _
  · rw [abs_neg]; exact hb _
  · simp; positivity

private lemma vertical_src_abs_le {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (n : ℕ) {L : ℕ} (a b : Fin L) : |cellSrc n E a b| ≤ 2 / κ := by
  have hs := vertical_sin_ge hκ hκ2 hE
  have hs0 : 0 < Real.sin (Real.arccos (E / 2)) := by linarith
  have hk := vertical_inv_sin_le hκ hκ2 hE
  unfold cellSrc
  split_ifs
  · rw [abs_div, abs_of_pos hs0, div_eq_mul_inv]
    calc _ ≤ 1 * (2 / κ) := mul_le_mul (Real.abs_sin_le_one _) hk (by positivity) zero_le_one
      _ = 2 / κ := one_mul _
  · simp; positivity

private lemma vertical_coef_sum_le {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (n : ℕ) {L : ℕ} (a : Fin L) : ∑ α : Fin L, |cellCoef n E a α| ≤ 4 / κ := by
  have h : ∀ α : Fin L, |cellCoef n E a α| ≤
      (if α = cellStart n a then 2 / κ else 0) + (if α = cellPrev n a then 2 / κ else 0) := by
    intro α
    have hc := vertical_coef_abs_le hκ hκ2 hE n a α
    have hk : (0 : ℝ) ≤ 2 / κ := by positivity
    by_cases h1 : α = cellStart n a
    · rw [if_pos h1]
      have : (0 : ℝ) ≤ if α = cellPrev n a then 2 / κ else 0 := by split_ifs <;> linarith
      linarith
    · by_cases h2 : α = cellPrev n a
      · rw [if_neg h1, if_pos h2]
        linarith
      · have h0 : cellCoef n E a α = 0 := by unfold cellCoef; rw [if_neg h1, if_neg h2]
        rw [h0, if_neg h1, if_neg h2]
        simp
  calc ∑ α, |cellCoef n E a α| ≤ ∑ α : Fin L, ((if α = cellStart n a then 2 / κ else 0) +
        (if α = cellPrev n a then 2 / κ else 0)) := Finset.sum_le_sum fun α _ => h α
    _ = 4 / κ := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
        simp only [Finset.mem_univ, ite_true]
        ring

private lemma vertical_cellD_abs_le {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (n : ℕ) {L : ℕ} (a b : Fin L) : |cellD n E a b| ≤ 2 / κ + 4 / κ * (2 / κ) := by
  unfold cellD
  refine (abs_add_le _ _).trans (add_le_add (vertical_src_abs_le hκ hκ2 hE n a b) ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ α, |cellCoef n E a α * cellSrc n E b α| ≤ ∑ α, |cellCoef n E a α| * (2 / κ) := by
        refine Finset.sum_le_sum fun α _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (vertical_src_abs_le hκ hκ2 hE n b α) (abs_nonneg _)
    _ = (∑ α, |cellCoef n E a α|) * (2 / κ) := by rw [Finset.sum_mul]
    _ ≤ 4 / κ * (2 / κ) :=
        mul_le_mul_of_nonneg_right (vertical_coef_sum_le hκ hκ2 hE n a) (by positivity)

private lemma vertical_isAnchor_start (n : ℕ) {L : ℕ} (a : Fin L) : IsAnchor n (cellStart n a) := by
  left
  simp [cellStart]

private lemma vertical_isAnchor_prev (n : ℕ) {L : ℕ} (a : Fin L) : IsAnchor n (cellPrev n a) := by
  right
  unfold cellPrev
  rw [Equiv.apply_symm_apply]
  simp [cellStart]

private lemma vertical_coef_anchor (n : ℕ) (E : ℝ) {L : ℕ} (a α : Fin L)
    (h : cellCoef n E a α ≠ 0) : IsAnchor n α := by
  unfold cellCoef at h
  by_cases h1 : α = cellStart n a
  · rw [h1]; exact vertical_isAnchor_start n a
  · by_cases h2 : α = cellPrev n a
    · rw [h2]; exact vertical_isAnchor_prev n a
    · simp [h1, h2] at h

/-- The interpolation through the anchor pairs is bounded by `(4/κ)²` times the largest anchor
value. -/
private lemma vertical_norming {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {κ E : ℝ}
    (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ) (n : ℕ) {L : ℕ} (X : Fin L → Fin L → F)
    (A : ℝ) (hA : 0 ≤ A) (hX : ∀ α β, IsAnchor n α → IsAnchor n β → ‖X α β‖ ≤ A) (a b : Fin L) :
    ‖∑ α : Fin L, ∑ β : Fin L, ((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) • X α β‖ ≤
      (4 / κ) ^ 2 * A := by
  have hterm : ∀ α β : Fin L, ‖((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) • X α β‖ ≤
      |cellCoef n E a α| * |cellCoef n E b β| * A := by
    intro α β
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    by_cases h1 : cellCoef n E a α = 0
    · simp [h1]
    by_cases h2 : cellCoef n E b β = 0
    · simp [h2]
    exact mul_le_mul_of_nonneg_left (hX α β (vertical_coef_anchor n E a α h1)
      (vertical_coef_anchor n E b β h2)) (by positivity)
  calc _ ≤ ∑ α : Fin L, ∑ β : Fin L, ‖((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) • X α β‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => norm_sum_le _ _)
    _ ≤ ∑ α : Fin L, ∑ β : Fin L, |cellCoef n E a α| * |cellCoef n E b β| * A :=
        Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ => hterm α β
    _ = (∑ α, |cellCoef n E a α|) * (∑ β, |cellCoef n E b β|) * A := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ (4 / κ) * (4 / κ) * A := by
        have h1 := vertical_coef_sum_le hκ hκ2 hE n a
        have h2 := vertical_coef_sum_le hκ hκ2 hE n b
        have h0 : 0 ≤ ∑ β, |cellCoef n E b β| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        exact mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 h0 (by positivity)) hA
    _ = (4 / κ) ^ 2 * A := by ring

private lemma vertical_anchorEnv_le (n : ℕ) {W L : ℕ}
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (e : ℝ) (he : 0 ≤ e)
    (hG : ∀ α β, IsAnchor n α → IsAnchor n β → ‖blockOf G α β‖ ≤ e) : anchorEnv n G ≤ e := by
  refine Real.iSup_le (fun ab => ?_) he
  unfold anchorNorm
  exact max_le (max_le (hG _ _ (vertical_isAnchor_start n _) (vertical_isAnchor_start n _))
      (hG _ _ (vertical_isAnchor_start n _) (vertical_isAnchor_prev n _)))
    (max_le (hG _ _ (vertical_isAnchor_prev n _) (vertical_isAnchor_start n _))
      (hG _ _ (vertical_isAnchor_prev n _) (vertical_isAnchor_prev n _)))

private lemma vertical_anchorNorm_le (n : ℕ) {W L : ℕ}
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (e : ℝ)
    (hG : ∀ α β, IsAnchor n α → IsAnchor n β → ‖blockOf G α β‖ ≤ e) (a b : Fin L) :
    anchorNorm n G a b ≤ e := by
  unfold anchorNorm
  exact max_le (max_le (hG _ _ (vertical_isAnchor_start n _) (vertical_isAnchor_start n _))
      (hG _ _ (vertical_isAnchor_start n _) (vertical_isAnchor_prev n _)))
    (max_le (hG _ _ (vertical_isAnchor_prev n _) (vertical_isAnchor_start n _))
      (hG _ _ (vertical_isAnchor_prev n _) (vertical_isAnchor_prev n _)))

private lemma vertical_norm_one_le (W : ℕ) : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by simp

/-! ### Markov bounds and the union over anchor pairs -/

private lemma vertical_cellClose_mono {W L n : ℕ} {E ε ε' : ℝ} {z : ℂ}
    {V : Fin L → Matrix (Fin W) (Fin W) ℂ} (h : CellClose n E z V ε) (hε : ε ≤ ε') :
    CellClose n E z V ε' :=
  fun b j h1 h2 => (h b j h1 h2).trans hε

/-- Real multiples of the GUE blocks are Hermitian. -/
private lemma vertical_herm (W L : ℕ) (ω : Ω W L) (b : ℝ) (r : Fin L) :
    (((b : ℝ) : ℂ) • gueBlock W L ω r).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, (gueBlock_isHermitian W L ω r).eq, Complex.star_def,
    Complex.conj_ofReal]

/-- `A_L` is symmetric. -/
private lemma vertical_cycleAdj_transpose (L : ℕ) : (cycleAdj L)ᵀ = cycleAdj L := by
  ext a b
  simp only [Matrix.transpose_apply, cycleAdj, Matrix.of_apply]
  exact add_comm _ _

/-- Markov's inequality for the `p`-th moment: `P(f > t) ≤ K t^{-p}` when `E f^p ≤ K`. -/
private lemma vertical_markov {X : Type*} [MeasurableSpace X] (P : Measure X) [IsFiniteMeasure P]
    (f : X → ℝ) (p : ℕ) (t K : ℝ) (ht : 0 < t) (hf0 : ∀ ω, 0 ≤ f ω)
    (hf : Integrable (fun ω => f ω ^ p) P) (hK : ∫ ω, f ω ^ p ∂P ≤ K) :
    P {ω | t < f ω} ≤ ENNReal.ofReal (K / t ^ p) := by
  have htp : 0 < t ^ p := pow_pos ht p
  have hsub : {ω | t < f ω} ⊆ {ω | t ^ p ≤ f ω ^ p} := fun ω hω =>
    pow_le_pow_left₀ ht.le (le_of_lt hω) p
  have hM := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => pow_nonneg (hf0 ω) p) hf (t ^ p)
  refine (measure_mono hsub).trans ?_
  have hK0 : 0 ≤ K := (integral_nonneg fun ω => pow_nonneg (hf0 ω) p).trans hK
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity), le_div_iff₀ htp]
  rw [measureReal_def] at hM
  nlinarith

/-- The moment bounds at one pair of blocks give, by Markov's inequality, the probability that
`‖G_{ab}‖ > T`, `|R_{ab}| > T s²` or `|G_{ai,bj} - δ_{ij}⟨G⟩_{ab}| > T s` for some `i, j`, where
`s² = W^{-1}`. -/
private lemma vertical_pair_bound (W : ℕ) (x : FlowPt × ℝ) (a b : Fin x.1.L) (p : ℕ)
    (Cp T s : ℝ) (hT : 1 ≤ T) (hs0 : 0 < s) (hs : s ^ 2 = (W : ℝ)⁻¹) (hW : 1 ≤ W)
    (hG : Integrable (fun ω => ‖blockOf (segG W x ω) a b‖ ^ p) (μ W x.1.L) ∧
      ∫ ω, ‖blockOf (segG W x ω) a b‖ ^ p ∂(μ W x.1.L) ≤ Cp)
    (hZ : ∀ i j : Fin W,
      Integrable (fun ω => ‖segG W x ω (a, i) (b, j) -
        if i = j then blockTr (segG W x ω) a b else 0‖ ^ (2 * p)) (μ W x.1.L) ∧
      ∫ ω, ‖segG W x ω (a, i) (b, j) - if i = j then blockTr (segG W x ω) a b else 0‖ ^ (2 * p)
        ∂(μ W x.1.L) ≤ Cp * ((W : ℝ) ^ p)⁻¹)
    (hR : Integrable (fun ω => ‖segRes W x ω a b‖ ^ p) (μ W x.1.L) ∧
      ∫ ω, ‖segRes W x ω a b‖ ^ p ∂(μ W x.1.L) ≤ Cp * ((W : ℝ) ^ p)⁻¹) :
    μ W x.1.L {ω | T < ‖blockOf (segG W x ω) a b‖ ∨ T * s ^ 2 < ‖segRes W x ω a b‖ ∨
      ∃ i j : Fin W, T * s < ‖segG W x ω (a, i) (b, j) -
        if i = j then blockTr (segG W x ω) a b else 0‖} ≤
      ENNReal.ofReal (((W : ℝ) ^ 2 + 2) * (Cp / T ^ p)) := by
  have hT0 : 0 < T := by linarith
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hWp : (0 : ℝ) < (W : ℝ) ^ p := by positivity
  have hCp : 0 ≤ Cp := (integral_nonneg fun ω => by positivity).trans hG.2
  set r : ℝ := Cp / T ^ p with hr
  have hr0 : 0 ≤ r := by positivity
  have h1 : μ W x.1.L {ω | T < ‖blockOf (segG W x ω) a b‖} ≤ ENNReal.ofReal r :=
    vertical_markov _ (fun ω => ‖blockOf (segG W x ω) a b‖) p T Cp hT0
      (fun ω => norm_nonneg _) hG.1 hG.2
  have h2 : μ W x.1.L {ω | T * s ^ 2 < ‖segRes W x ω a b‖} ≤ ENNReal.ofReal r := by
    refine (vertical_markov _ (fun ω => ‖segRes W x ω a b‖) p (T * s ^ 2) _ (by positivity)
      (fun ω => norm_nonneg _) hR.1 hR.2).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [hs, mul_pow, inv_pow, hr]
    field_simp
  have h3 : ∀ i j : Fin W, μ W x.1.L {ω | T * s < ‖segG W x ω (a, i) (b, j) -
      if i = j then blockTr (segG W x ω) a b else 0‖} ≤ ENNReal.ofReal r := by
    intro i j
    refine (vertical_markov _ (fun ω => ‖segG W x ω (a, i) (b, j) -
      if i = j then blockTr (segG W x ω) a b else 0‖) (2 * p) (T * s) _ (by positivity)
      (fun ω => norm_nonneg _) (hZ i j).1 (hZ i j).2).trans (ENNReal.ofReal_le_ofReal ?_)
    have e : (T * s) ^ (2 * p) = T ^ (2 * p) * ((W : ℝ) ^ p)⁻¹ := by
      rw [mul_pow, pow_mul s, hs, inv_pow]
    rw [e, hr]
    have hTp : T ^ p ≤ T ^ (2 * p) := pow_le_pow_right₀ hT (by omega)
    calc Cp * ((W : ℝ) ^ p)⁻¹ / (T ^ (2 * p) * ((W : ℝ) ^ p)⁻¹) = Cp / T ^ (2 * p) := by
          field_simp
      _ ≤ Cp / T ^ p := div_le_div_of_nonneg_left hCp (by positivity) hTp
  have hset : {ω | T < ‖blockOf (segG W x ω) a b‖ ∨ T * s ^ 2 < ‖segRes W x ω a b‖ ∨
      ∃ i j : Fin W, T * s < ‖segG W x ω (a, i) (b, j) -
        if i = j then blockTr (segG W x ω) a b else 0‖} =
      {ω | T < ‖blockOf (segG W x ω) a b‖} ∪ ({ω | T * s ^ 2 < ‖segRes W x ω a b‖} ∪
        ⋃ i : Fin W, ⋃ j : Fin W, {ω | T * s < ‖segG W x ω (a, i) (b, j) -
          if i = j then blockTr (segG W x ω) a b else 0‖}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion]
  have h3' : μ W x.1.L (⋃ i : Fin W, ⋃ j : Fin W, {ω | T * s < ‖segG W x ω (a, i) (b, j) -
      if i = j then blockTr (segG W x ω) a b else 0‖}) ≤ ENNReal.ofReal ((W : ℝ) ^ 2 * r) := by
    refine (measure_iUnion_fintype_le _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => (measure_iUnion_fintype_le _ _).trans
      (Finset.sum_le_sum fun j _ => h3 i j)).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    ring
  rw [hset]
  refine (measure_union_le _ _).trans ((add_le_add h1 ((measure_union_le _ _).trans
    (add_le_add h2 h3'))).trans (le_of_eq ?_))
  rw [← ENNReal.ofReal_add hr0 (by positivity), ← ENNReal.ofReal_add hr0 (by positivity)]
  congr 1
  ring

/-- The interpolation of a block through the anchor pairs: if `‖G_{ab} - interp‖ ≤ X` and the
anchor blocks are at most `A`, then `‖G_{ab}‖ ≤ (4/κ)² A + |d| + X`. -/
private lemma vertical_interp_G {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ) (n : ℕ)
    {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (A X : ℝ) (hA : 0 ≤ A)
    (hX : ∀ α β, IsAnchor n α → IsAnchor n β → ‖blockOf G α β‖ ≤ A) (a b : Fin L)
    (h : ‖blockOf G a b - interpBlock n E G a b‖ ≤ X) :
    ‖blockOf G a b‖ ≤ (4 / κ) ^ 2 * A + (2 / κ + 4 / κ * (2 / κ)) + X := by
  have h1 := vertical_norming hκ hκ2 hE n (fun α β => blockOf G α β) A hA hX a b
  have h2 : ‖((cellD n E a b : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤
      2 / κ + 4 / κ * (2 / κ) := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc |cellD n E a b| * ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ (2 / κ + 4 / κ * (2 / κ)) * 1 :=
          mul_le_mul (vertical_cellD_abs_le hκ hκ2 hE n a b) (vertical_norm_one_le W)
            (norm_nonneg _) (by positivity)
      _ = _ := mul_one _
  have h3 : ‖interpBlock n E G a b‖ ≤ (4 / κ) ^ 2 * A + (2 / κ + 4 / κ * (2 / κ)) := by
    unfold interpBlock
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  calc ‖blockOf G a b‖ = ‖(blockOf G a b - interpBlock n E G a b) + interpBlock n E G a b‖ := by
        rw [sub_add_cancel]
    _ ≤ X + ((4 / κ) ^ 2 * A + (2 / κ + 4 / κ * (2 / κ))) :=
        (norm_add_le _ _).trans (add_le_add h h3)
    _ = _ := by ring

/-- The scalar interpolation through the anchor pairs: if `|y₀ - Σ c_{aα} c_{bβ} Y_{αβ}| ≤ X` and
the anchor values are at most `A`, then `|y₀| ≤ (4/κ)² A + X`. -/
private lemma vertical_interp_scalar {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (n : ℕ) {L : ℕ} (Y : Fin L → Fin L → ℂ) (y₀ : ℂ) (A X : ℝ) (hA : 0 ≤ A)
    (hY : ∀ α β, IsAnchor n α → IsAnchor n β → ‖Y α β‖ ≤ A) (a b : Fin L)
    (h : ‖y₀ - ∑ α : Fin L, ∑ β : Fin L,
      ((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) * Y α β‖ ≤ X) :
    ‖y₀‖ ≤ (4 / κ) ^ 2 * A + X := by
  have h1 := vertical_norming hκ hκ2 hE n Y A hA hY a b
  simp only [smul_eq_mul] at h1
  calc ‖y₀‖ = ‖(y₀ - ∑ α : Fin L, ∑ β : Fin L,
        ((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) * Y α β) + ∑ α : Fin L, ∑ β : Fin L,
        ((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) * Y α β‖ := by rw [sub_add_cancel]
    _ ≤ X + (4 / κ) ^ 2 * A := (norm_add_le _ _).trans (add_le_add h h1)
    _ = _ := by ring

private lemma vertical_anchorEnv_nonneg (n : ℕ) {W L : ℕ}
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) : 0 ≤ anchorEnv n G :=
  Real.iSup_nonneg fun _ => le_max_of_le_left (le_max_of_le_left (norm_nonneg _))

/-- The block bound through the anchor pairs, deterministic form: anchor blocks at most `T` and
the error of Proposition 7.4 [uvc:prop:green] give `‖G_{ab}‖ ≤ T²`. -/
private lemma vertical_det_G {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ) (n : ℕ)
    {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (Cg e T : ℝ) (hCg : 0 ≤ Cg)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hT : 1 ≤ T)
    (hK : (4 / κ) ^ 2 + (2 / κ + 4 / κ * (2 / κ)) + 2 * Cg ≤ T)
    (hGa : ∀ α β, IsAnchor n α → IsAnchor n β → ‖blockOf G α β‖ ≤ T) (a b : Fin L)
    (hGi : ‖blockOf G a b - interpBlock n E G a b‖ ≤ Cg * e * (1 + anchorNorm n G a b)) :
    ‖blockOf G a b‖ ≤ T * T := by
  have hT0 : 0 < T := by linarith
  have hA := vertical_anchorNorm_le n G T hGa a b
  have h' : ‖blockOf G a b - interpBlock n E G a b‖ ≤ Cg * e * (1 + T) :=
    hGi.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have h2 := vertical_interp_G hκ hκ2 hE n G T _ hT0.le hGa a b h'
  have h3 : Cg * e * (1 + T) ≤ 2 * Cg * T := by
    have : Cg * e ≤ Cg := mul_le_of_le_one_right hCg he1
    nlinarith
  have hd0 : (0 : ℝ) ≤ 2 / κ + 4 / κ * (2 / κ) := by positivity
  have h4 : 2 / κ + 4 / κ * (2 / κ) ≤ (2 / κ + 4 / κ * (2 / κ)) * T :=
    le_mul_of_one_le_right hd0 hT
  have h5 : ((4 / κ) ^ 2 + (2 / κ + 4 / κ * (2 / κ)) + 2 * Cg) * T ≤ T * T :=
    mul_le_mul_of_nonneg_right hK hT0.le
  nlinarith [h2, h3, h4, h5]

/-- The traceless entries through the anchor pairs, deterministic form: anchor entries at most
`Ts` and the error of the Remark of Section 7.4 [sec:sampling-propagation-extensions] give
`|G_{ai,bj} - δ_{ij}⟨G⟩_{ab}| ≤ T²s`. -/
private lemma vertical_det_Z {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ) (n : ℕ)
    {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (Cc Ct e T s : ℝ) (hCc : 0 ≤ Cc)
    (hCt : 0 ≤ Ct) (he0 : 0 ≤ e) (he : e ≤ (1 + Ct) * s) (hT : 1 ≤ T) (hs0 : 0 < s)
    (hK : (4 / κ) ^ 2 + 2 * Cc * (1 + Ct) ≤ T)
    (hGa : ∀ α β, IsAnchor n α → IsAnchor n β → ‖blockOf G α β‖ ≤ T)
    (hZa : ∀ α β, IsAnchor n α → IsAnchor n β → ∀ i j : Fin W,
      ‖G (α, i) (β, j) - (if i = j then blockTr G α β else 0)‖ ≤ T * s)
    (a b : Fin L) (i j : Fin W)
    (hZi : ‖G (a, i) (b, j) - (if i = j then blockTr G a b else 0) - ∑ α : Fin L, ∑ β : Fin L,
      ((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) *
        (G (α, i) (β, j) - if i = j then blockTr G α β else 0)‖ ≤
      Cc * e * (1 + anchorEnv n G)) :
    ‖G (a, i) (b, j) - (if i = j then blockTr G a b else 0)‖ ≤ T * T * s := by
  have hT0 : 0 < T := by linarith
  have hEnv := vertical_anchorEnv_le n G T hT0.le hGa
  have h' : ‖G (a, i) (b, j) - (if i = j then blockTr G a b else 0) - ∑ α : Fin L, ∑ β : Fin L,
      ((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) *
        (G (α, i) (β, j) - if i = j then blockTr G α β else 0)‖ ≤ Cc * e * (1 + T) :=
    hZi.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have h2 := vertical_interp_scalar hκ hκ2 hE n
    (fun α β => G (α, i) (β, j) - if i = j then blockTr G α β else 0)
    (G (a, i) (b, j) - if i = j then blockTr G a b else 0) (T * s) _ (by positivity)
    (fun α β hα hβ => hZa α β hα hβ i j) a b h'
  have h3 : Cc * e * (1 + T) ≤ 2 * Cc * (1 + Ct) * (T * s) := by
    calc Cc * e * (1 + T) ≤ Cc * ((1 + Ct) * s) * (2 * T) := by
          gcongr
          linarith
      _ = _ := by ring
  have h5 : ((4 / κ) ^ 2 + 2 * Cc * (1 + Ct)) * (T * s) ≤ T * (T * s) :=
    mul_le_mul_of_nonneg_right hK (by positivity)
  nlinarith [h2, h3, h5]

/-- The residual combinations through the anchor pairs, deterministic form: anchor values at most
`Ts²` and the error `Q(1 + 𝒢)² X` of Proposition 7.10 [uvc:prop:residual-compression] with
`X ≤ K s⁴` give `|R_{ab}| ≤ T²s²`. -/
private lemma vertical_det_R {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ) (n : ℕ)
    {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (Rc : Fin L → Fin L → ℂ)
    (Q K X T s : ℝ) (hQ : 0 ≤ Q) (hK0 : 0 ≤ K) (hX0 : 0 ≤ X) (hX : X ≤ K * s ^ 4) (hT : 1 ≤ T)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hKT : 2 * (4 / κ) ^ 2 ≤ T) (hKs : 8 * Q * K * s ≤ 1)
    (hGa : ∀ α β, IsAnchor n α → IsAnchor n β → ‖blockOf G α β‖ ≤ T)
    (hRa : ∀ α β, IsAnchor n α → IsAnchor n β → ‖Rc α β‖ ≤ T * s ^ 2) (a b : Fin L)
    (hRi : ‖Rc a b - ∑ α : Fin L, ∑ β : Fin L,
      ((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) * Rc α β‖ ≤
      Q * (1 + anchorEnv n G) ^ 2 * X) :
    ‖Rc a b‖ ≤ T * T * s ^ 2 := by
  have hT0 : 0 < T := by linarith
  have hEnv := vertical_anchorEnv_le n G T hT0.le hGa
  have hEnv0 := vertical_anchorEnv_nonneg n G
  have h' : ‖Rc a b - ∑ α : Fin L, ∑ β : Fin L,
      ((cellCoef n E a α * cellCoef n E b β : ℝ) : ℂ) * Rc α β‖ ≤ Q * (1 + T) ^ 2 * X :=
    hRi.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith) (by linarith) 2) hQ) hX0)
  have h2 := vertical_interp_scalar hκ hκ2 hE n Rc (Rc a b) (T * s ^ 2) _ (by positivity) hRa a b h'
  have hX1 : (1 + T) ^ 2 ≤ 4 * T ^ 2 := by nlinarith
  have hX3 : Q * (1 + T) ^ 2 * X ≤ Q * (4 * T ^ 2) * (K * s ^ 4) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hX1 hQ) hX hX0 (by positivity)
  have hX4 : Q * (4 * T ^ 2) * (K * s ^ 4) ≤ 1 / 2 * (T * T * s ^ 2) := by
    have e1 : Q * (4 * T ^ 2) * (K * s ^ 4) = (8 * Q * K * s) * (T * T * s ^ 2) * s / 2 := by
      ring
    rw [e1]
    have hTs : 0 ≤ T * T * s ^ 2 := by positivity
    have h8 : 0 ≤ 8 * Q * K * s := by positivity
    calc (8 * Q * K * s) * (T * T * s ^ 2) * s / 2 ≤ 1 * (T * T * s ^ 2) * 1 / 2 := by
          gcongr
      _ = 1 / 2 * (T * T * s ^ 2) := by ring
  have hX5 : (4 / κ) ^ 2 * (T * s ^ 2) ≤ 1 / 2 * (T * T * s ^ 2) := by
    have hTs : 0 ≤ T * s ^ 2 := by positivity
    nlinarith
  linarith

/-- The count of the union bound: `W^{-D-1} + N (W² + 2) C_p T^{-p} ≤ W^{-D}` for
`N ≤ 36 W^{22}`, `T^p ≥ W^{D+26}` and `W ≥ max(2, 108 C_p)`. -/
private lemma vertical_count (W D Cp Tp N : ℝ) (hW : 2 ≤ W) (hCp : 0 ≤ Cp)
    (hWCp : 108 * Cp ≤ W) (hTp : W ^ (D + 26) ≤ Tp) (hN0 : 0 ≤ N)
    (hN : N ≤ 36 * W ^ (22 : ℕ)) :
    W ^ (-(D + 1)) + N * ((W ^ 2 + 2) * (Cp / Tp)) ≤ W ^ (-D) := by
  have hW0 : 0 < W := by linarith
  set X : ℝ := W ^ (D + 1) with hX
  have hX0 : 0 < X := Real.rpow_pos_of_pos hW0 _
  have e1 : W ^ (D + 26) = X * W ^ (25 : ℕ) := by
    rw [hX, ← Real.rpow_natCast, ← Real.rpow_add hW0]
    congr 1
    push_cast
    ring
  have e2 : W ^ (-(D + 1)) = X⁻¹ := Real.rpow_neg hW0.le _
  have e3 : W ^ (-D) = W * X⁻¹ := by
    rw [← e2, show -D = 1 + -(D + 1) by ring, Real.rpow_add hW0, Real.rpow_one]
  have hW25 : 0 < W ^ (25 : ℕ) := by positivity
  have hTp0 : 0 < Tp := lt_of_lt_of_le (by rw [e1]; positivity) hTp
  have h1 : N * (W ^ 2 + 2) ≤ 108 * W ^ (24 : ℕ) := by
    have h3 : W ^ 2 + 2 ≤ 3 * W ^ 2 := by nlinarith
    calc N * (W ^ 2 + 2) ≤ 36 * W ^ (22 : ℕ) * (3 * W ^ 2) :=
          mul_le_mul hN h3 (by positivity) (by positivity)
      _ = 108 * W ^ (24 : ℕ) := by ring
  have h2 : Cp / Tp ≤ Cp / (X * W ^ (25 : ℕ)) :=
    div_le_div_of_nonneg_left hCp (by positivity) (e1 ▸ hTp)
  have h3 : N * ((W ^ 2 + 2) * (Cp / Tp)) ≤ X⁻¹ := by
    calc N * ((W ^ 2 + 2) * (Cp / Tp)) = (N * (W ^ 2 + 2)) * (Cp / Tp) := by ring
      _ ≤ (108 * W ^ (24 : ℕ)) * (Cp / (X * W ^ (25 : ℕ))) :=
          mul_le_mul h1 h2 (div_nonneg hCp hTp0.le) (by positivity)
      _ = 108 * Cp / (X * W) := by field_simp
      _ ≤ W / (X * W) := by gcongr
      _ = X⁻¹ := by field_simp
  rw [e2, e3]
  have := mul_le_mul_of_nonneg_right hW (inv_pos.mpr hX0).le
  linarith

set_option maxHeartbeats 1000000 in
/-- The maxima over all blocks on the vertical half-line (the statement of `vert_max`). -/
private lemma vertical_max_aux (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) :
    ∃ Cκ₀ : ℝ, 1 ≤ Cκ₀ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      ∀ ε D : ℝ, 0 < ε → 0 < D → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ x : FlowPt × ℝ,
        x.1 ∈ initLarge κ Cκ CV ρ W → etaChar x.1.g (mRoot x.1.g x.1.L x.1.E) x.1.u ≤ x.2 →
        x.1.g ^ 2 * x.2 ≤ (W : ℝ) ^ (1 / 2 : ℝ) →
        μ W x.1.L {ω | ∃ a b : Fin x.1.L, (W : ℝ) ^ ε < ‖blockOf (segG W x ω) a b‖ ∨
          (W : ℝ) ^ (ε - 1) < ‖segRes W x ω a b‖ ∨ ∃ i j : Fin W, (W : ℝ) ^ (ε - 1 / 2) <
            ‖segG W x ω (a, i) (b, j) - if i = j then blockTr (segG W x ω) a b else 0‖} ≤
          ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  obtain ⟨Cκl, Rl, cl, Cl, hCκl, hRl, hcl, hCl, Hl⟩ := large_periodic_comparison κ hκ hκ2
  set C : ℝ := max 1 Cl with hCdef
  have hC1 : 1 ≤ C := le_max_left _ _
  obtain ⟨Cκr, hCκr, Hr⟩ := resolvent_moments_vert κ C hκ hκ2 hC1
  obtain ⟨Cκv, Rv, hCκv, hRv, Hv⟩ := vert_moments κ C hκ hκ2 hC1
  obtain ⟨CκD, RD, cD, Γ, hCκD, hRD, hcD, hΓ, HD⟩ := dysonVert_large κ hκ hκ2
  obtain ⟨Cκχ, Cχ, hCκχ, hCχ, Hχ⟩ := char_large κ C hκ hκ2 hC1
  have hk : 0 < κ / 2 := by linarith
  have hk2 : κ / 2 < 2 := by linarith
  obtain ⟨Ct, hCt, Ht⟩ := cellClose_perturb (κ / 2) hk hk2
  obtain ⟨Cg, hCg, Hg⟩ := green_interp (κ / 2) hk hk2
  obtain ⟨Cc, hCc, Hc⟩ := centered_interp (κ / 2) hk hk2
  obtain ⟨Cr, hCr, Hres⟩ := residual_interp (κ / 2) hk hk2
  have hCχ0 : 0 < Cχ := by linarith
  set c₁ : ℝ := (2 * Cχ)⁻¹ with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  obtain ⟨Cκw, Cw, cw, hCκw, hCw, hcw, Hw⟩ :=
    rowInterp_dyson (κ / 2) (c₁ + Γ) c₁ hk hk2 (by positivity) hc₁0
  refine ⟨max (max (max Cκl Cκr) (max Cκv CκD)) Cκχ,
    le_trans hCκl (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))), ?_⟩
  intro Cκ hCκ ρ hρ ε D hε hD
  -- the moment order `p` with `pε/2 ≥ D + 26`
  set p : ℕ := ⌈2 * (D + 26) / ε⌉₊ + 1 with hpdef
  have hp1 : 1 ≤ p := Nat.le_add_left 1 _
  have hpε : D + 26 ≤ ε / 2 * p := by
    have h1 : 2 * (D + 26) / ε ≤ (⌈2 * (D + 26) / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (p : ℝ) = (⌈2 * (D + 26) / ε⌉₊ : ℝ) + 1 := by simp [hpdef]
    have h3 : 2 * (D + 26) ≤ (⌈2 * (D + 26) / ε⌉₊ : ℝ) * ε := (div_le_iff₀ hε).mp h1
    nlinarith
  obtain ⟨Cp1, hCp1, Hp1⟩ := Hr p hp1
  obtain ⟨Cp2, hCp2, Hp2⟩ := Hv p hp1
  obtain ⟨Wc, HWc⟩ := cells_prefix (κ / 2) 8 3 (D + 1) hk hk2 (by norm_num) (by norm_num)
    (by linarith)
  set Cp : ℝ := Cp1 + Cp2 with hCpdef
  have hCp0 : 0 ≤ Cp := by positivity
  set K3 : ℝ := (1 + Ct) + Cw / c₁ * (1 + CV) + 1 with hK3
  set Kt : ℝ := 2 * (4 / (κ / 2)) ^ 2 + (2 / (κ / 2) + 4 / (κ / 2) * (2 / (κ / 2))) + 2 * Cg +
    2 * Cc * (1 + Ct) with hKt
  set Ks : ℝ := (1 + Ct) + 8 * (Cr * (1 + Γ) ^ 2) * K3 + (cw * c₁)⁻¹ + Cκw ^ 2 / c₁ with hKs
  set Rst : ℝ := max (max Rl Rv) (max RD 4) with hRst
  have hev : ∀ᶠ W : ℕ in atTop, 8 * p ≤ W ∧ Wc ≤ W ∧ 2 ≤ W ∧ CV ≤ (W : ℝ) ∧ Rst ≤ ρ W ∧
      1 ≤ Real.log W ∧ 108 * Cp ≤ (W : ℝ) ∧ Kt ≤ (W : ℝ) ^ (ε / 2) ∧
      Ks * (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    have hs := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop).const_mul Ks
    rw [mul_zero] at hs
    exact (eventually_ge_atTop (8 * p)).and ((eventually_ge_atTop Wc).and
      ((eventually_ge_atTop 2).and ((tendsto_natCast_atTop_atTop.eventually_ge_atTop CV).and
      ((hρ.eventually_ge_atTop Rst).and (((Real.tendsto_log_atTop.comp
        tendsto_natCast_atTop_atTop).eventually_ge_atTop 1).and
      ((tendsto_natCast_atTop_atTop.eventually_ge_atTop (108 * Cp)).and
      ((((tendsto_rpow_atTop (half_pos hε)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
        Kt).and (hs.eventually (Iic_mem_nhds (by norm_num))))))))))
  obtain ⟨W₀, HW₀⟩ := eventually_atTop.1 hev
  refine ⟨W₀, fun W hW x hx hyη hgy => ?_⟩
  obtain ⟨h8p, hWc, hW2, hWCV, hρW, hlog, hWCp, hTK, hsK⟩ := HW₀ W hW
  have hW1 : 1 ≤ W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW2r : (2 : ℝ) ≤ W := by exact_mod_cast hW2
  obtain ⟨hgC, hE, hLlog, hLV, hu0, hu1⟩ := hx
  have hg0' : max (max (max Cκl Cκr) (max Cκv CκD)) Cκχ ≤ x.1.g := hCκ.trans hgC
  obtain ⟨⟨⟨hgl, hgr⟩, hgv, hgD⟩, hgχ⟩ :
      ((Cκl ≤ x.1.g ∧ Cκr ≤ x.1.g) ∧ Cκv ≤ x.1.g ∧ CκD ≤ x.1.g) ∧ Cκχ ≤ x.1.g := by
    simpa only [max_le_iff] using hg0'
  have hg1 : 1 ≤ x.1.g := hCκl.trans hgl
  have hg0 : 0 < x.1.g := by linarith
  have hgg : 0 < x.1.g ^ 2 := by positivity
  have hRst0 : 0 < Rst := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _)
    (le_max_right _ _))
  have hLR : Rst * x.1.g ^ 2 ≤ x.1.L := by
    have h1 : 0 ≤ ρ W * x.1.g ^ 2 := mul_nonneg (by linarith) hgg.le
    calc Rst * x.1.g ^ 2 ≤ ρ W * x.1.g ^ 2 := mul_le_mul_of_nonneg_right hρW hgg.le
      _ ≤ ρ W * x.1.g ^ 2 * Real.log W := le_mul_of_one_le_right h1 hlog
      _ ≤ _ := hLlog
  have hRL : ∀ R' : ℝ, R' ≤ Rst → R' * x.1.g ^ 2 ≤ x.1.L := fun R' h =>
    le_trans (mul_le_mul_of_nonneg_right h hgg.le) hLR
  have hRlL := hRL Rl (le_trans (le_max_left _ _) (le_max_left _ _))
  have hRvL := hRL Rv (le_trans (le_max_right _ _) (le_max_left _ _))
  have hRDL := hRL RD (le_trans (le_max_left _ _) (le_max_right _ _))
  have h4L := hRL 4 (le_trans (le_max_right _ _) (le_max_right _ _))
  have hL3 : 3 ≤ x.1.L := by
    have h1 : (1 : ℝ) ≤ x.1.g ^ 2 := one_le_pow₀ hg1
    have : (3 : ℝ) ≤ x.1.L := by linarith
    exact_mod_cast this
  -- the root
  obtain ⟨m, -, hroot, -, hmim, hmC, -⟩ := Hl x.1.g hgl x.1.L hRlL x.1.E hE
  have hb0 : 0 ≤ hopB x.1.g := by rw [vertical_hopB hg1]; norm_num
  have hmR : mRoot x.1.g x.1.L x.1.E = m :=
    (mRootV_spec (hopB x.1.g) (gammaG x.1.g) hb0 (vertical_gammaG_pos _) x.1.L hL3
      (x.1.E : ℂ) (by simp)).2 m hroot
  have hroot' : IsDysonRootV (hopB x.1.g) (gammaG x.1.g) x.1.L x.1.E
      (mRoot x.1.g x.1.L x.1.E) := by rw [hmR]; exact hroot
  have hmC' : ‖mRoot x.1.g x.1.L x.1.E‖ ≤ C := by rw [hmR]; exact hmC.trans (le_max_right _ _)
  have hmim' : C⁻¹ ≤ (mRoot x.1.g x.1.L x.1.E).im := by
    rw [hmR]; exact le_trans (inv_anti₀ hCl (le_max_right _ _)) hmim
  obtain ⟨hre, -, hη0, -, hgη⟩ := Hχ x.1.g hgχ x.1.E (mRoot x.1.g x.1.L x.1.E) hE hmC' hmim'
    x.1.u hu0 (by linarith)
  have hy0 : 0 < x.2 := hη0.trans_le hyη
  have hc₁y : c₁ ≤ x.1.g ^ 2 * x.2 := by
    have h1 : c₁ ≤ (1 - x.1.u) / Cχ := by
      rw [hc₁, mul_inv, div_eq_mul_inv]
      have : (2 : ℝ)⁻¹ ≤ 1 - x.1.u := by linarith
      have h0 : 0 ≤ Cχ⁻¹ := by positivity
      exact mul_le_mul_of_nonneg_right this h0
    exact h1.trans (hgη.trans (mul_le_mul_of_nonneg_left hyη hgg.le))
  -- the scales `s = W^{-1/2}` and `T = W^{ε/2}`
  set s : ℝ := (W : ℝ) ^ (-(1 / 2 : ℝ)) with hsdef
  have hs0 : 0 < s := Real.rpow_pos_of_pos hW0 _
  have hs1 : s ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1r (by norm_num)
  have hs2 : s ^ 2 = (W : ℝ)⁻¹ := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le,
      show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  have hsW : (W : ℝ) ^ (1 / 2 : ℝ) * s = 1 := by
    rw [hsdef, ← Real.rpow_add hW0]; norm_num
  have hs16 : (W : ℝ) ^ (-(8 : ℝ)) = s ^ 16 := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; norm_num
  have hs4 : (W : ℝ) ^ (-((8 : ℝ) / 4)) = s ^ 4 := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; norm_num
  have hW2s : (W : ℝ) ^ 2 * s ^ 4 = 1 := by
    rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2]; field_simp
  have hs15 : s ^ 15 ≤ s := pow_le_of_le_one hs0.le hs1 (by norm_num)
  have hs4s : s ^ 4 ≤ s := pow_le_of_le_one hs0.le hs1 (by norm_num)
  have hs2s : s ^ 2 ≤ s := pow_le_of_le_one hs0.le hs1 (by norm_num)
  have hKse : Ks * s = (1 + Ct) * s + 8 * (Cr * (1 + Γ) ^ 2) * K3 * s + (cw * c₁)⁻¹ * s +
      Cκw ^ 2 / c₁ * s := by rw [hKs]; ring
  have hK30 : 0 ≤ K3 := by positivity
  have hKs1 : (1 + Ct) * s ≤ 1 := by
    have : 0 ≤ 8 * (Cr * (1 + Γ) ^ 2) * K3 * s + (cw * c₁)⁻¹ * s + Cκw ^ 2 / c₁ * s := by
      positivity
    linarith
  have hKs2 : 8 * (Cr * (1 + Γ) ^ 2) * K3 * s ≤ 1 := by
    have : 0 ≤ (1 + Ct) * s + (cw * c₁)⁻¹ * s + Cκw ^ 2 / c₁ * s := by positivity
    linarith
  have hKs3 : s ≤ cw * c₁ := by
    have : 0 ≤ (1 + Ct) * s + 8 * (Cr * (1 + Γ) ^ 2) * K3 * s + Cκw ^ 2 / c₁ * s := by
      positivity
    have h : (cw * c₁)⁻¹ * s ≤ 1 := by linarith
    rwa [inv_mul_le_iff₀ (by positivity), mul_one] at h
  have hKs4 : Cκw ^ 2 * s ≤ c₁ := by
    have : 0 ≤ (1 + Ct) * s + 8 * (Cr * (1 + Γ) ^ 2) * K3 * s + (cw * c₁)⁻¹ * s := by
      positivity
    have h : Cκw ^ 2 / c₁ * s ≤ 1 := by linarith
    rwa [div_mul_eq_mul_div, div_le_one hc₁0] at h
  set T : ℝ := (W : ℝ) ^ (ε / 2) with hTdef
  have hT1 : 1 ≤ T := Real.one_le_rpow hW1r (by positivity)
  have hT0 : 0 < T := by linarith
  have hTT : (W : ℝ) ^ ε = T * T := by rw [hTdef, ← Real.rpow_add hW0, add_halves]
  have hTε1 : (W : ℝ) ^ (ε - 1) = T * T * s ^ 2 := by
    rw [Real.rpow_sub hW0, Real.rpow_one, hTT, hs2, div_eq_mul_inv]
  have hTε2 : (W : ℝ) ^ (ε - 1 / 2) = T * T * s := by
    rw [show ε - 1 / 2 = ε + -(1 / 2) by ring, Real.rpow_add hW0, hTT]
  have hTp : (W : ℝ) ^ (D + 26) ≤ T ^ p := by
    rw [hTdef, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
    exact Real.rpow_le_rpow_of_exponent_le hW1r hpε
  have hgys : x.1.g ^ 2 * x.2 * s ≤ 1 := by
    calc x.1.g ^ 2 * x.2 * s ≤ (W : ℝ) ^ (1 / 2 : ℝ) * s :=
          mul_le_mul_of_nonneg_right hgy hs0.le
      _ = 1 := hsW
  have hTle : T ≤ T * T := le_mul_of_one_le_right hT0.le hT1
  -- the union bound at each pair
  set Bad : Fin x.1.L → Fin x.1.L → Set (Ω W x.1.L) := fun a b =>
    {ω | T < ‖blockOf (segG W x ω) a b‖ ∨ T * s ^ 2 < ‖segRes W x ω a b‖ ∨
      ∃ i j : Fin W, T * s < ‖segG W x ω (a, i) (b, j) -
        if i = j then blockTr (segG W x ω) a b else 0‖} with hBad
  set rB : ℝ := ((W : ℝ) ^ 2 + 2) * (Cp / T ^ p) with hrB
  have hPB : ∀ a b : Fin x.1.L, μ W x.1.L (Bad a b) ≤ ENNReal.ofReal rB := by
    intro a b
    obtain ⟨hG1, hG2⟩ := Hp1 W (by omega) x hgr h4L hE hroot' hmC' hmim' hu0 hu1 hyη a b
    obtain ⟨hZ, hR1, hR2⟩ := Hp2 W h8p x hgv hRvL hE hroot' hmC' hmim' hu0 hu1 hyη a b
    have hWp : (0 : ℝ) ≤ ((W : ℝ) ^ p)⁻¹ := by positivity
    exact vertical_pair_bound W x a b p Cp T s hT1 hs0 hs2 hW1 ⟨hG1, hG2.trans (by linarith)⟩
      (fun i j => ⟨(hZ i j).1, (hZ i j).2.trans
        (mul_le_mul_of_nonneg_right (by linarith) hWp)⟩)
      ⟨hR1, hR2.trans (mul_le_mul_of_nonneg_right (by linarith) hWp)⟩
  suffices key : ∃ N : ℕ, (N : ℝ) ≤ 36 * (W : ℝ) ^ (22 : ℕ) ∧
      μ W x.1.L {ω | ∃ a b : Fin x.1.L, (W : ℝ) ^ ε < ‖blockOf (segG W x ω) a b‖ ∨
          (W : ℝ) ^ (ε - 1) < ‖segRes W x ω a b‖ ∨ ∃ i j : Fin W, (W : ℝ) ^ (ε - 1 / 2) <
            ‖segG W x ω (a, i) (b, j) - if i = j then blockTr (segG W x ω) a b else 0‖} ≤
        ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) + N * ENNReal.ofReal rB by
    obtain ⟨N, hN, hμ⟩ := key
    have hrB0 : 0 ≤ rB := by positivity
    calc _ ≤ _ := hμ
      _ = ENNReal.ofReal ((W : ℝ) ^ (-(D + 1)) + N * rB) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal
          (vertical_count W D Cp (T ^ p) N hW2r hCp0 hWCp hTp (Nat.cast_nonneg _) hN)
  by_cases hbig : (W : ℝ) ^ (8 : ℝ) ≤ x.1.g ^ 2
  swap
  · -- `g² < W^8`: all pairs
    refine ⟨x.1.L * x.1.L, ?_, ?_⟩
    · have h8 : x.1.g ^ 2 ≤ (W : ℝ) ^ (8 : ℕ) := by
        have := (not_le.mp hbig).le
        rwa [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
      have hL11 : (x.1.L : ℝ) ≤ (W : ℝ) ^ (11 : ℕ) := by
        calc (x.1.L : ℝ) ≤ CV * x.1.g ^ 2 * (W : ℝ) ^ 2 := hLV
          _ ≤ (W : ℝ) * (W : ℝ) ^ (8 : ℕ) * (W : ℝ) ^ 2 := by gcongr
          _ = (W : ℝ) ^ (11 : ℕ) := by ring
      push_cast
      calc (x.1.L : ℝ) * x.1.L ≤ (W : ℝ) ^ (11 : ℕ) * (W : ℝ) ^ (11 : ℕ) :=
            mul_le_mul hL11 hL11 (by positivity) (by positivity)
        _ = (W : ℝ) ^ (22 : ℕ) := by ring
        _ ≤ 36 * (W : ℝ) ^ (22 : ℕ) := by
            have : (0 : ℝ) ≤ (W : ℝ) ^ (22 : ℕ) := by positivity
            linarith
    · have hsub : {ω | ∃ a b : Fin x.1.L, (W : ℝ) ^ ε < ‖blockOf (segG W x ω) a b‖ ∨
          (W : ℝ) ^ (ε - 1) < ‖segRes W x ω a b‖ ∨ ∃ i j : Fin W, (W : ℝ) ^ (ε - 1 / 2) <
            ‖segG W x ω (a, i) (b, j) - if i = j then blockTr (segG W x ω) a b else 0‖} ⊆
          ⋃ ab ∈ (Finset.univ : Finset (Fin x.1.L × Fin x.1.L)), Bad ab.1 ab.2 := by
        intro ω hω
        obtain ⟨a, b, h⟩ := hω
        refine Set.mem_iUnion₂.2 ⟨(a, b), Finset.mem_univ _, ?_⟩
        rcases h with h | h | ⟨i, j, h⟩
        · rw [hTT] at h
          exact Or.inl (lt_of_le_of_lt hTle h)
        · rw [hTε1] at h
          exact Or.inr (Or.inl (lt_of_le_of_lt
            (mul_le_mul_of_nonneg_right hTle (by positivity)) h))
        · rw [hTε2] at h
          exact Or.inr (Or.inr ⟨i, j, lt_of_le_of_lt
            (mul_le_mul_of_nonneg_right hTle hs0.le) h⟩)
      refine (measure_mono hsub).trans (le_trans ?_ le_add_self)
      refine (measure_biUnion_finset_le _ _).trans ((Finset.sum_le_sum fun ab _ =>
        hPB ab.1 ab.2).trans (le_of_eq ?_))
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  -- `g² ≥ W^8`: the anchor pairs
  obtain ⟨hmu0, hmuC, hMe, hMr, -, -, -⟩ := HD x.1.g hgD x.1.L hRDL x.1.E hE
    (mRoot x.1.g x.1.L x.1.E) hroot' x.1.u hu0 hu1 x.2 hyη
  have hγy : gammaG x.1.g * (x.2 / gammaG x.1.g) = x.2 :=
    mul_div_cancel₀ _ (vertical_gammaG_pos x.1.g).ne'
  simp only [hγy] at hmu0 hmuC
  set E' : ℝ := (zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re with hE'
  set β : ℝ := x.1.u * gammaG x.1.g with hβdef
  set z : ℂ := (E' : ℂ) + (x.2 : ℂ) * Complex.I with hz
  set mu : ℂ := mRootV (hopB x.1.g) β x.1.L z with hmu
  set w : ℂ := z + (β : ℂ) * mu with hw
  have hseg : segMat x.1.g x.1.L E' x.1.u (x.2 / gammaG x.1.g) =
      (cycleAdj x.1.L - w • (1 : Matrix (Fin x.1.L) (Fin x.1.L) ℂ))⁻¹ := by
    rw [vertical_segMat_eq]
    unfold dysonMat
    rw [show ((hopB x.1.g : ℝ) : ℂ) • cycleAdj x.1.L = cycleAdj x.1.L by
      rw [vertical_hopB hg1, Complex.ofReal_one, one_smul]]
  rw [hseg] at hMe hMr
  set M : Matrix (Fin x.1.L) (Fin x.1.L) ℂ :=
    (cycleAdj x.1.L - w • (1 : Matrix (Fin x.1.L) (Fin x.1.L) ℂ))⁻¹ with hM
  have hβ0 : 0 ≤ β := mul_nonneg hu0 (vertical_gammaG_pos _).le
  have hβle : β ≤ (x.1.g ^ 2)⁻¹ := by
    rw [hβdef, vertical_gammaG hg1]
    exact mul_le_of_le_one_left (by positivity) (by linarith)
  have hβg : β * x.1.g ^ 2 ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hβle hgg.le
    rwa [inv_mul_cancel₀ hgg.ne'] at this
  have hMr' : ∀ a, β * ∑ b, ‖M a b‖ ≤ Γ := fun a =>
    le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ =>
      le_add_of_nonneg_right (sq_nonneg _)) hβ0) (hMr a)
  have hMs : Mᵀ = M := by
    rw [hM, Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_one, vertical_cycleAdj_transpose]
  have hwim : x.2 ≤ w.im := by
    have e : w.im = x.2 + β * mu.im := by
      simp only [hw, hz, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, add_zero, zero_add]
    rw [e]
    have := mul_nonneg hβ0 hmu0
    linarith
  have hwE : ‖w - (E' : ℂ)‖ ≤ x.2 + β * Γ := by
    have e : w - (E' : ℂ) = (x.2 : ℂ) * Complex.I + (β : ℂ) * mu := by rw [hw, hz]; ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) ?_)
    · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hy0.le]
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ0]
      exact mul_le_mul_of_nonneg_left hmuC hβ0
  -- the cell length
  set n : ℕ := cellLen x.1.g W 8 with hndef
  have hn1 : 1 ≤ n := le_max_left _ _
  have hnb : (n : ℝ) ≤ x.1.g ^ 2 * s ^ 16 := by
    have := (cellLen_bounds x.1.g 8 W hW1 hbig).2
    rwa [hs16] at this
  have hg2s : 1 ≤ x.1.g ^ 2 * s ^ 16 := by
    have h1 : (W : ℝ) ^ (8 : ℝ) * s ^ 16 = 1 := by
      rw [← hs16, ← Real.rpow_add hW0, add_neg_cancel, Real.rpow_zero]
    have := mul_le_mul_of_nonneg_right hbig (by positivity : (0 : ℝ) ≤ s ^ 16)
    linarith
  have hny : (n : ℝ) * x.2 ≤ s ^ 15 := by
    calc (n : ℝ) * x.2 ≤ x.1.g ^ 2 * s ^ 16 * x.2 := mul_le_mul_of_nonneg_right hnb hy0.le
      _ = (x.1.g ^ 2 * x.2 * s) * s ^ 15 := by ring
      _ ≤ 1 * s ^ 15 := mul_le_mul_of_nonneg_right hgys (by positivity)
      _ = s ^ 15 := one_mul _
  -- the free interpolation of `M` at the coupling `g̃² = c₁/y`
  set gt : ℝ := Real.sqrt (c₁ / x.2) with hgt
  have hq0 : 0 < c₁ / x.2 := by positivity
  have hgt2 : gt ^ 2 = c₁ / x.2 := Real.sq_sqrt hq0.le
  have hgtC : Cκw ≤ gt := by
    rw [hgt, Real.le_sqrt (by linarith) hq0.le, le_div_iff₀ hy0]
    have h1 : Cκw ^ 2 * x.2 ≤ Cκw ^ 2 * x.2 * (x.1.g ^ 2 * s ^ 16) :=
      le_mul_of_one_le_right (by positivity) hg2s
    have h2 : Cκw ^ 2 * x.2 * (x.1.g ^ 2 * s ^ 16) = Cκw ^ 2 * s ^ 15 * (x.1.g ^ 2 * x.2 * s) := by
      ring
    have h3 : Cκw ^ 2 * s ^ 15 * (x.1.g ^ 2 * x.2 * s) ≤ Cκw ^ 2 * s * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hs15 (by positivity)) hgys (by positivity)
        (by positivity)
    linarith
  have hgtL : 4 * gt ^ 2 ≤ x.1.L := by
    rw [hgt2]
    have : c₁ / x.2 ≤ x.1.g ^ 2 := by rw [div_le_iff₀ hy0]; linarith
    linarith
  have hwim' : c₁ / gt ^ 2 ≤ w.im := by rw [hgt2, div_div_cancel₀ hc₁0.ne']; exact hwim
  have hwE' : ‖w - (E' : ℂ)‖ ≤ (c₁ + Γ) / gt ^ 2 := by
    rw [hgt2]
    have hβy : β ≤ x.2 / c₁ := by
      rw [le_div_iff₀ hc₁0]
      calc β * c₁ ≤ (x.1.g ^ 2)⁻¹ * (x.1.g ^ 2 * x.2) := mul_le_mul hβle hc₁y hc₁0.le (by positivity)
        _ = x.2 := by field_simp
    calc ‖w - (E' : ℂ)‖ ≤ x.2 + β * Γ := hwE
      _ ≤ x.2 + x.2 / c₁ * Γ := by gcongr
      _ = (c₁ + Γ) / (c₁ / x.2) := by field_simp
  have hnc : (n : ℝ) ≤ cw * gt ^ 2 := by
    rw [hgt2, mul_div_assoc', le_div_iff₀ hy0]
    linarith
  obtain ⟨hRI, -, -⟩ := Hw gt hgtC x.1.L hgtL E' hre w hwim' hwE' n hn1 hnc
  set δ : ℝ := Cw * n / gt ^ 2 with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hδb : δ * (1 + β * x.1.L) ≤ Cw / c₁ * (1 + CV) * s ^ 4 := by
    have e : δ = Cw / c₁ * (n * x.2) := by rw [hδ, hgt2]; field_simp
    rw [e]
    have hβL : β * x.1.L ≤ CV * (W : ℝ) ^ 2 := by
      calc β * x.1.L ≤ β * (CV * x.1.g ^ 2 * (W : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hLV hβ0
        _ = (β * x.1.g ^ 2) * (CV * (W : ℝ) ^ 2) := by ring
        _ ≤ 1 * (CV * (W : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hβg (by positivity)
        _ = CV * (W : ℝ) ^ 2 := one_mul _
    have h1 : (n : ℝ) * x.2 * (1 + β * x.1.L) ≤ s ^ 15 * (1 + CV * (W : ℝ) ^ 2) :=
      mul_le_mul hny (by linarith) (by positivity) (by positivity)
    have h2 : s ^ 15 * (1 + CV * (W : ℝ) ^ 2) = s ^ 15 + CV * s ^ 11 := by
      have : s ^ 15 * (W : ℝ) ^ 2 = s ^ 11 := by
        rw [show s ^ 15 = s ^ 11 * s ^ 4 by ring, mul_assoc, mul_comm (s ^ 4), hW2s, mul_one]
      linear_combination CV * this
    have h3 : s ^ 15 ≤ s ^ 4 := pow_le_pow_of_le_one hs0.le hs1 (by norm_num)
    have h4 : s ^ 11 ≤ s ^ 4 := pow_le_pow_of_le_one hs0.le hs1 (by norm_num)
    have h5 : (n : ℝ) * x.2 * (1 + β * x.1.L) ≤ (1 + CV) * s ^ 4 := by
      have := mul_le_mul_of_nonneg_left h4 hCV.le
      linarith
    calc Cw / c₁ * (n * x.2) * (1 + β * x.1.L) = Cw / c₁ * ((n : ℝ) * x.2 * (1 + β * x.1.L)) := by
          ring
      _ ≤ Cw / c₁ * ((1 + CV) * s ^ 4) := mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = _ := by ring
  have hβn : β * n ≤ s ^ 4 := by
    calc β * n ≤ (x.1.g ^ 2)⁻¹ * (x.1.g ^ 2 * s ^ 16) :=
          mul_le_mul hβle hnb (Nat.cast_nonneg _) (by positivity)
      _ = s ^ 16 := by field_simp
      _ ≤ s ^ 4 := pow_le_pow_of_le_one hs0.le hs1 (by norm_num)
  -- the cell event
  have hL3' : (x.1.L : ℝ) ≤ x.1.g ^ 2 * (W : ℝ) ^ (3 : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (x.1.L : ℝ) ≤ CV * x.1.g ^ 2 * (W : ℝ) ^ 2 := hLV
      _ ≤ (W : ℝ) * x.1.g ^ 2 * (W : ℝ) ^ 2 := by gcongr
      _ = _ := by ring
  have hcell := HWc W hWc x.1.g x.1.L E' β hbig hL3' hre hβ0 (by linarith)
  set V : Ω W x.1.L → Fin x.1.L → Matrix (Fin W) (Fin W) ℂ := fun ω r =>
    ((Real.sqrt β : ℝ) : ℂ) • gueBlock W x.1.L ω r with hV
  set S : Finset (Fin x.1.L × Fin x.1.L) :=
    (Finset.univ.filter fun α : Fin x.1.L => IsAnchor n α) ×ˢ
      (Finset.univ.filter fun α : Fin x.1.L => IsAnchor n α) with hS
  refine ⟨S.card, ?_, ?_⟩
  · have hc := (card_cells_le_pow x.1.g 8 3 W x.1.L hW1 (by norm_num) (by norm_num) hbig hL3').2
    have e : (W : ℝ) ^ ((8 : ℝ) + 3) = (W : ℝ) ^ (11 : ℕ) := by
      rw [show (8 : ℝ) + 3 = ((11 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e] at hc
    rw [hS, Finset.card_product, Nat.cast_mul]
    calc _ ≤ (6 * (W : ℝ) ^ (11 : ℕ)) * (6 * (W : ℝ) ^ (11 : ℕ)) :=
          mul_le_mul hc hc (by positivity) (by positivity)
      _ = 36 * (W : ℝ) ^ (22 : ℕ) := by ring
  -- the event outside the cell event and the anchor events
  set e : ℝ := (1 + Ct) * s ^ 4 with he
  have he0 : 0 ≤ e := by positivity
  have he1 : e ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hs4s (by positivity)) hKs1
  have hzE : ‖z - (E' : ℂ)‖ = x.2 := by
    rw [hz, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hy0.le]
  have hzE' : ‖(starRingEnd ℂ) z - (E' : ℂ)‖ = x.2 := by
    rw [show (starRingEnd ℂ) z - (E' : ℂ) = (starRingEnd ℂ) (z - (E' : ℂ)) by
      rw [map_sub, Complex.conj_ofReal], Complex.norm_conj, hzE]
  have hnz : (n : ℝ) * x.2 ≤ s ^ 4 := hny.trans (pow_le_pow_of_le_one hs0.le hs1 (by norm_num))
  have hzim : z.im ≠ 0 := by rw [hz]; simp [hy0.ne']
  have hsub : {ω | ∃ a b : Fin x.1.L, (W : ℝ) ^ ε < ‖blockOf (segG W x ω) a b‖ ∨
      (W : ℝ) ^ (ε - 1) < ‖segRes W x ω a b‖ ∨ ∃ i j : Fin W, (W : ℝ) ^ (ε - 1 / 2) <
        ‖segG W x ω (a, i) (b, j) - if i = j then blockTr (segG W x ω) a b else 0‖} ⊆
      {ω | ¬ CellClose n E' (E' : ℂ) (V ω) ((W : ℝ) ^ (-((8 : ℝ) / 4)))} ∪
        ⋃ ab ∈ S, Bad ab.1 ab.2 := by
    intro ω hω
    by_contra hcon
    have hcl : CellClose n E' (E' : ℂ) (V ω) (s ^ 4) := by
      rw [← hs4]
      by_contra h
      exact hcon (Or.inl h)
    have hanc : ∀ α α' : Fin x.1.L, IsAnchor n α → IsAnchor n α' → ω ∉ Bad α α' := by
      intro α α' hα hα' hmem
      exact hcon (Or.inr (Set.mem_iUnion₂.2 ⟨(α, α'), by simp [hS, hα, hα'], hmem⟩))
    have hGa : ∀ α α', IsAnchor n α → IsAnchor n α' → ‖blockOf (segG W x ω) α α'‖ ≤ T :=
      fun α α' hα hα' => by
        by_contra h
        exact hanc α α' hα hα' (Or.inl (not_le.mp h))
    have hRa : ∀ α α', IsAnchor n α → IsAnchor n α' → ‖segRes W x ω α α'‖ ≤ T * s ^ 2 :=
      fun α α' hα hα' => by
        by_contra h
        exact hanc α α' hα hα' (Or.inr (Or.inl (not_le.mp h)))
    have hZa : ∀ α α', IsAnchor n α → IsAnchor n α' → ∀ i j : Fin W,
        ‖segG W x ω (α, i) (α', j) - (if i = j then blockTr (segG W x ω) α α' else 0)‖ ≤
          T * s := fun α α' hα hα' i j => by
      by_contra h
      exact hanc α α' hα hα' (Or.inr (Or.inr ⟨i, j, not_le.mp h⟩))
    -- the resolvent as a block operator
    set Gr := resolventMat (cycleAdj x.1.L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) +
      blockDiagOp (V ω)) z with hGr
    have hGeq : segG W x ω = Gr := by
      unfold segG
      rw [flowH_cycle _ hg1]
    rw [hGeq] at hGa hZa
    have hVh : ∀ r, (V ω r).IsHermitian := fun r => vertical_herm W x.1.L ω _ r
    have hclz : CellClose n E' z (V ω) e := by
      have h := Ht W x.1.L n E' (s ^ 4) z (V ω) hre (by positivity) (pow_le_one₀ hs0.le hs1)
        (by rw [hzE]; linarith) hcl
      refine vertical_cellClose_mono h ?_
      rw [hzE, he]
      have : Ct * ↑n * x.2 ≤ Ct * s ^ 4 := by
        have := mul_le_mul_of_nonneg_left hnz hCt.le
        rwa [← mul_assoc] at this
      linarith
    have hclz' : CellClose n E' ((starRingEnd ℂ) z) (V ω) e := by
      have h := Ht W x.1.L n E' (s ^ 4) ((starRingEnd ℂ) z) (V ω) hre (by positivity)
        (pow_le_one₀ hs0.le hs1) (by rw [hzE']; linarith) hcl
      refine vertical_cellClose_mono h ?_
      rw [hzE', he]
      have : Ct * ↑n * x.2 ≤ Ct * s ^ 4 := by
        have := mul_le_mul_of_nonneg_left hnz hCt.le
        rwa [← mul_assoc] at this
      linarith
    have hEnv : anchorEnv n Gr ≤ T := vertical_anchorEnv_le n Gr T hT0.le hGa
    have hKt' : 2 * (4 / (κ / 2)) ^ 2 + (2 / (κ / 2) + 4 / (κ / 2) * (2 / (κ / 2))) + 2 * Cg +
        2 * Cc * (1 + Ct) ≤ T := hTK
    have hk1 : 0 ≤ (4 / (κ / 2)) ^ 2 := by positivity
    have hk3 : 0 ≤ 2 / (κ / 2) + 4 / (κ / 2) * (2 / (κ / 2)) := by positivity
    have hk4 : 0 ≤ 2 * Cc * (1 + Ct) := by positivity
    have hk5 : 0 ≤ 2 * Cg := by positivity
    have hKG : (4 / (κ / 2)) ^ 2 + (2 / (κ / 2) + 4 / (κ / 2) * (2 / (κ / 2))) + 2 * Cg ≤ T := by
      linarith
    have hKZ : (4 / (κ / 2)) ^ 2 + 2 * Cc * (1 + Ct) ≤ T := by linarith
    have hKR : 2 * (4 / (κ / 2)) ^ 2 ≤ T := by linarith
    have hGall : ∀ a b, ‖blockOf Gr a b‖ ≤ T * T := fun a b =>
      vertical_det_G hk hk2 hre n Gr Cg e T hCg.le he0 he1 hT1 hKG hGa a b
        (Hg W x.1.L n E' e z (V ω) hL3 hn1 hre hVh hzim he0 he1 hclz hclz' a b)
    have hRI0 : RowInterp n E' (0 : Matrix (Fin x.1.L) (Fin x.1.L) ℂ) (2 / (κ / 2)) := by
      intro a b
      simp only [Matrix.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, zero_sub,
        norm_neg, Complex.norm_real, Real.norm_eq_abs]
      exact vertical_src_abs_le hk hk2 hre n a b
    have he' : e ≤ (1 + Ct) * s := by rw [he]; exact mul_le_mul_of_nonneg_left hs4s (by positivity)
    have hZall : ∀ a b (i j : Fin W),
        ‖Gr (a, i) (b, j) - (if i = j then blockTr Gr a b else 0)‖ ≤ T * T * s :=
      fun a b i j => vertical_det_Z hk hk2 hre n Gr Cc Ct e T s hCc.le hCt.le he0 he' hT1 hs0
        hKZ hGa hZa a b i j
        ((Hc W x.1.L n E' e (2 / (κ / 2)) z (V ω) 0 hW1 hL3 hn1 hre hVh hzim he0 he1
          hclz hclz' Matrix.transpose_zero hRI0 a b).2 i j)
    have hRall : ∀ a b, ‖segRes W x ω a b‖ ≤ T * T * s ^ 2 := by
      rcases eq_or_lt_of_le hu0 with hu | hu
      · intro a b
        rw [vertical_segRes_zero W x hu.symm hy0 ω a b, norm_zero]
        positivity
      have hid : ∀ a b, segRes W x ω a b = resComb β Gr M a b := by
        intro a b
        rw [segRes_identity W hW1 x hg0.le hL3 hu hy0 ω a b, hGeq]
        exact congrArg (fun M' => resComb β Gr M' a b) hseg
      have hRa' : ∀ α α', IsAnchor n α → IsAnchor n α' → ‖resComb β Gr M α α'‖ ≤ T * s ^ 2 :=
        fun α α' hα hα' => by rw [← hid]; exact hRa α α' hα hα'
      have hX2 : e + δ * (1 + β * x.1.L) + β * n ≤ K3 * s ^ 4 := by
        have : K3 * s ^ 4 = (1 + Ct) * s ^ 4 + Cw / c₁ * (1 + CV) * s ^ 4 + s ^ 4 := by
          rw [hK3]; ring
        rw [this, he]
        linarith
      intro a b
      rw [hid]
      exact vertical_det_R hk hk2 hre n Gr (fun α α' => resComb β Gr M α α') (Cr * (1 + Γ) ^ 2)
        K3 (e + δ * (1 + β * x.1.L) + β * n) T s (by positivity) hK30 (by positivity) hX2 hT1
        hs0 hs1 hKR hKs2 hGa hRa' a b
        (Hres W x.1.L n E' e δ β Γ z (V ω) M hW1 hL3 hn1 hre hVh hzim he0 he1 hδ0 hβ0
          hclz hclz' hMs hRI hMe hMr' a b)
    obtain ⟨a, b, h⟩ := hω
    rcases h with h | h | ⟨i, j, h⟩
    · rw [hTT, hGeq] at h
      linarith [hGall a b]
    · rw [hTε1] at h
      linarith [hRall a b]
    · rw [hTε2, hGeq] at h
      linarith [hZall a b i j]
  calc _ ≤ μ W x.1.L ({ω | ¬ CellClose n E' (E' : ℂ) (V ω) ((W : ℝ) ^ (-((8 : ℝ) / 4)))} ∪
        ⋃ ab ∈ S, Bad ab.1 ab.2) := measure_mono hsub
    _ ≤ μ W x.1.L {ω | ¬ CellClose n E' (E' : ℂ) (V ω) ((W : ℝ) ^ (-((8 : ℝ) / 4)))} +
        ∑ ab ∈ S, μ W x.1.L (Bad ab.1 ab.2) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_biUnion_finset_le _ _))
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) + ∑ ab ∈ S, ENNReal.ofReal rB :=
        add_le_add hcell (Finset.sum_le_sum fun ab _ => hPB ab.1 ab.2)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The maxima over all blocks on the vertical half-line at early times, at heights
`η_u ≤ y ≤ W^{1/2}/g²`: with probability at least `1 - W^{-D}`, `max ‖G_{ab}‖ ≤ W^ε`,
`max |R_{ab}| ≤ W^{ε-1}` and `max |G_{ai,bj} - δ_{ij}⟨G⟩_{ab}| ≤ W^{ε-1/2}` (anchor pairs of
Definition 5.7 [def:cells-anchors] with Proposition 7.4 [uvc:prop:green] and Proposition 7.10
[uvc:prop:residual-compression], or all blocks when `g² < W^B`). -/
theorem vert_max (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) :
    ∃ Cκ₀ : ℝ, 1 ≤ Cκ₀ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      ∀ ε D : ℝ, 0 < ε → 0 < D → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ x : FlowPt × ℝ,
        x.1 ∈ initLarge κ Cκ CV ρ W → etaChar x.1.g (mRoot x.1.g x.1.L x.1.E) x.1.u ≤ x.2 →
        x.1.g ^ 2 * x.2 ≤ (W : ℝ) ^ (1 / 2 : ℝ) →
        μ W x.1.L {ω | ∃ a b : Fin x.1.L, (W : ℝ) ^ ε < ‖blockOf (segG W x ω) a b‖ ∨
          (W : ℝ) ^ (ε - 1) < ‖segRes W x ω a b‖ ∨ ∃ i j : Fin W, (W : ℝ) ^ (ε - 1 / 2) <
            ‖segG W x ω (a, i) (b, j) - if i = j then blockTr (segG W x ω) a b else 0‖} ≤
          ENNReal.ofReal ((W : ℝ) ^ (-D)) :=
  vertical_max_aux κ CV hκ hκ2 hCV

end LSBA
