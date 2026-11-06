import LSBA.Upper.PathWalk
import LSBA.Upper.FracMoment
import LSBA.Gauss.FreshBlock

/-!
# The path form of [PSSS, Theorem 1]

The bound on the Dirichlet path used in the proof of Theorem 3.1 [thm:strong-upper], for the
operator (8.5) [up:eq:shifted-resolvent] at zero endpoint shifts with `0 ≤ g ≤ 1`. Along the walk
from `x` to `y`, each factor `G_{Λ_i}(γ_i, γ_i) = (V_{γ_i} - E - Σ_{γ_i})⁻¹` has a self-energy and
an incoming vector that depend only on the blocks of `Λ_{i+1} ∌ γ_i`, so the one-block half
moment ([PSSS, (2.6)]) applies at each step. This gives
`𝔼‖G(x, y; E) v‖^{1/2} ≤ C₁ W^{1/4} (C₁ (g √W)^{1/2})^{|x-y|} ‖v‖^{1/2}`, and summation over the
`W` coordinate vectors gives (8.2) [up:eq:fmr-pointwise] on every path at `q = 1/2`, `𝔟 = 1`, for
`0 ≤ g ≤ c_* W^{-1/2}`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The model `K + diag(V_a)`, for a deterministic `K`. -/
private def pathMoment_H {W L : ℕ} (K : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (ω : Ω W L) :
    Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  K + blockDiagOp (gueBlock W L ω)

/-- The product of `n` consecutive factors of a walk product, starting at step `i`. -/
private def pathMoment_tail {W L : ℕ} (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (E : ℝ)
    (γ : ℕ → Fin L) (i n : ℕ) : Matrix (Fin W) (Fin W) ℂ :=
  ((List.range n).map fun l =>
    blockOf (maskRes H (walkRest γ (i + l)) E) (γ (i + l)) (γ (i + l))).prod

private theorem pathMoment_walkProd_eq {W L : ℕ} (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (E : ℝ) (γ : ℕ → Fin L) (k : ℕ) : walkProd H E γ k = pathMoment_tail H E γ 0 (k + 1) := by
  simp only [walkProd, pathMoment_tail, zero_add]

private theorem pathMoment_tail_succ {W L : ℕ} (H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (E : ℝ) (γ : ℕ → Fin L) (i n : ℕ) :
    pathMoment_tail H E γ i (n + 1) =
      blockOf (maskRes H (walkRest γ i) E) (γ i) (γ i) * pathMoment_tail H E γ (i + 1) n := by
  unfold pathMoment_tail
  rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map, add_zero]
  refine congrArg _ (congrArg List.prod (List.map_congr_left fun l _ => ?_))
  simp only [Function.comp_apply]
  rw [show i + (l + 1) = i + 1 + l by omega]

private theorem pathMoment_not_mem_rest {L : ℕ} (γ : ℕ → Fin L) {i j : ℕ} (hji : j < i) :
    γ j ∉ walkRest γ i := by
  simp only [walkRest, Finset.mem_filter, Finset.mem_univ, true_and, not_forall]
  exact ⟨j, hji, fun h => h rfl⟩

private theorem pathMoment_blockOf_diag {W L : ℕ} (K : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (ω : Ω W L) (x : Fin L) :
    blockOf (pathMoment_H K ω) x x = blockOf K x x + gueBlock W L ω x := by
  ext α β
  simp [blockOf, pathMoment_H, blockDiagOp]

private theorem pathMoment_blockOf_off {W L : ℕ} (K : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (ω ω' : Ω W L) {x c : Fin L} (hxc : x ≠ c) :
    blockOf (pathMoment_H K ω) x c = blockOf (pathMoment_H K ω') x c := by
  ext α β
  simp [blockOf, pathMoment_H, blockDiagOp, hxc]

private theorem pathMoment_isHermitian {W L : ℕ} {K : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hK : K.IsHermitian) (ω : Ω W L) : (pathMoment_H K ω).IsHermitian :=
  hK.add (blockDiagOp_isHermitian fun a => gueBlock_isHermitian W L ω a)

private theorem pathMoment_blockOf_isHermitian {W L : ℕ}
    {X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hX : X.IsHermitian) (x : Fin L) :
    (blockOf X x x).IsHermitian := by
  ext α β
  simpa [blockOf, Matrix.conjTranspose_apply] using congrFun (congrFun hX (x, α)) (x, β)

private theorem pathMoment_real_smul_one_isHermitian (W : ℕ) (E : ℝ) :
    ((E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)).IsHermitian :=
  Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint, Complex.conj_ofReal])

private theorem pathMoment_continuous_H {W L : ℕ}
    (K : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) : Continuous (pathMoment_H K) := by
  refine continuous_matrix fun p q => ?_
  simp only [pathMoment_H, gueBlock, blockDiagOp, Matrix.add_apply, Matrix.of_apply]
  split_ifs <;> fun_prop

private theorem pathMoment_measurable_inv {m : Type*} [Fintype m] [DecidableEq m] :
    Measurable fun A : Matrix m m ℂ => A⁻¹ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  have hd : Measurable fun A : Matrix m m ℂ => A.det :=
    (continuous_id.matrix_det).measurable
  have ha : Measurable fun A : Matrix m m ℂ => A.adjugate i j :=
    (continuous_id.matrix_adjugate).measurable.eval_matrix
  exact (hd.inv).mul ha

/-- Almost surely, for every set `Λ` of blocks, the masked operator of `K + diag(V_a)` is
invertible. -/
private theorem pathMoment_ae_det {W L : ℕ} (K : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (E : ℝ) :
    ∀ᵐ ω ∂(μ W L), ∀ Λ : Finset (Fin L), (maskMat {p | p.1 ∈ Λ}
      (pathMoment_H K ω - (E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ))).det ≠ 0 :=
  ae_det_maskMat_add_gueBlock_ne_zero K E

private theorem pathMoment_gueBlock_congr {W L : ℕ} {ω ω' : Ω W L} {a : Fin L}
    (h : ∀ α β : Fin W, ω (a, α, β) = ω' (a, α, β)) : gueBlock W L ω a = gueBlock W L ω' a := by
  ext α β
  simp only [gueBlock, Matrix.of_apply, h]

/-- `G_Λ(E)` depends only on the blocks in `Λ`. -/
private theorem pathMoment_maskRes_congr {W L : ℕ}
    (K : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (Λ : Finset (Fin L)) (E : ℝ) {ω ω' : Ω W L}
    (h : ∀ x : Fin L × Fin W × Fin W, x.1 ∈ Λ → ω x = ω' x) :
    maskRes (pathMoment_H K ω) Λ E = maskRes (pathMoment_H K ω') Λ E := by
  unfold maskRes
  congr 1
  ext p q
  by_cases hpq : p.1 ∈ Λ ∧ q.1 ∈ Λ
  · have hb' : gueBlock W L ω p.1 = gueBlock W L ω' p.1 :=
      pathMoment_gueBlock_congr fun α β => h _ hpq.1
    simp only [maskMat, Matrix.of_apply, Set.mem_ofPred_eq, hpq, and_self, ite_true,
      Matrix.sub_apply, pathMoment_H, Matrix.add_apply, blockDiagOp, hb']
  · simp only [maskMat, Matrix.of_apply, Set.mem_ofPred_eq, hpq, ite_false]

private theorem pathMoment_measurable_maskRes {W L : ℕ}
    (K : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (Λ : Finset (Fin L)) (E : ℝ) :
    Measurable fun ω : Ω W L => maskRes (pathMoment_H K ω) Λ E := by
  have hc : Continuous fun ω : Ω W L => maskMat {p | p.1 ∈ Λ}
      (pathMoment_H K ω - (E : ℂ) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) := by
    refine continuous_matrix fun p q => ?_
    simp only [maskMat, Matrix.of_apply]
    split_ifs
    · exact (((pathMoment_continuous_H K).sub continuous_const).matrix_elem p q)
    · exact continuous_const
    · exact continuous_const
  exact pathMoment_measurable_inv.comp hc.measurable

private theorem pathMoment_measurable_blockOf {α : Type*} [MeasurableSpace α] {W L : ℕ}
    {F : α → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hF : Measurable F) (a b : Fin L) :
    Measurable fun ω => blockOf (F ω) a b :=
  Measurable.of_eval_matrix _ fun _ _ => hF.eval_matrix

private theorem pathMoment_measurable_mul {α : Type*} [MeasurableSpace α] {W : ℕ}
    {F G : α → Matrix (Fin W) (Fin W) ℂ} (hF : Measurable F) (hG : Measurable G) :
    Measurable fun ω => F ω * G ω :=
  Measurable.of_eval_matrix _ fun i j => by
    simp only [Matrix.mul_apply]
    exact Finset.measurable_sum _ fun k _ => hF.eval_matrix.mul hG.eval_matrix

private theorem pathMoment_measurable_sum {α ι : Type*} [MeasurableSpace α] {W : ℕ}
    (s : Finset ι) {F : ι → α → Matrix (Fin W) (Fin W) ℂ} (hF : ∀ i ∈ s, Measurable (F i)) :
    Measurable fun ω => ∑ i ∈ s, F i ω :=
  Measurable.of_eval_matrix _ fun α β => by
    simp only [Matrix.sum_apply]
    exact Finset.measurable_sum _ fun i hi => (hF i hi).eval_matrix

private theorem pathMoment_measurable_mulVec {α : Type*} [MeasurableSpace α] {W : ℕ}
    {M : α → Matrix (Fin W) (Fin W) ℂ} (hM : Measurable M) (v : Fin W → ℂ) :
    Measurable fun ω => M ω *ᵥ v := by
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.measurable_sum _ fun j _ => hM.eval_matrix.mul measurable_const

private theorem pathMoment_measurable_sqrt {α : Type*} [MeasurableSpace α] {W : ℕ}
    {M : α → Matrix (Fin W) (Fin W) ℂ} (hM : Measurable M) (v : Fin W → ℂ) :
    Measurable fun ω => Real.sqrt (l2Norm (M ω *ᵥ v)) := by
  have hc : Continuous fun u : Fin W → ℂ => Real.sqrt (l2Norm u) := by
    unfold l2Norm
    fun_prop
  exact hc.measurable.comp (pathMoment_measurable_mulVec hM v)

private theorem pathMoment_measurable_tail {W L : ℕ}
    (K : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (E : ℝ) (γ : ℕ → Fin L)
    (n : ℕ) : ∀ i, Measurable fun ω : Ω W L => pathMoment_tail (pathMoment_H K ω) E γ i n := by
  induction n with
  | zero =>
    intro i
    simp only [pathMoment_tail, List.range_zero, List.map_nil, List.prod_nil]
    exact measurable_const
  | succ n ih =>
    intro i
    simp only [pathMoment_tail_succ]
    exact pathMoment_measurable_mul
      (pathMoment_measurable_blockOf (pathMoment_measurable_maskRes K _ E) _ _) (ih (i + 1))

private theorem pathMoment_measurable_selfEnergy {W L : ℕ}
    (K : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (Λ : Finset (Fin L))
    (x : Fin L) (E : ℝ) : Measurable fun ω : Ω W L => selfEnergy (pathMoment_H K ω) Λ x E := by
  have hH : Measurable (pathMoment_H (W := W) (L := L) K) :=
    (pathMoment_continuous_H K).measurable
  unfold selfEnergy
  refine pathMoment_measurable_sum _ fun c _ => pathMoment_measurable_sum _ fun c' _ => ?_
  exact pathMoment_measurable_mul (pathMoment_measurable_mul
    (pathMoment_measurable_blockOf hH _ _)
    (pathMoment_measurable_blockOf (pathMoment_measurable_maskRes K _ E) _ _))
    (pathMoment_measurable_blockOf hH _ _)

/-- The self-energy of block `x` does not depend on block `x` of the sample. -/
private theorem pathMoment_selfEnergy_congr {W L : ℕ}
    (K : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (Λ : Finset (Fin L))
    (x : Fin L) (E : ℝ) {ω ω' : Ω W L} (h : ∀ y : Fin L × Fin W × Fin W, y.1 ≠ x → ω y = ω' y) :
    selfEnergy (pathMoment_H K ω) Λ x E = selfEnergy (pathMoment_H K ω') Λ x E := by
  have hG : maskRes (pathMoment_H K ω) (Λ.erase x) E = maskRes (pathMoment_H K ω') (Λ.erase x) E :=
    pathMoment_maskRes_congr K _ E fun y hy => h y (Finset.ne_of_mem_erase hy)
  unfold selfEnergy
  refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun c' hc' => ?_
  rw [hG, pathMoment_blockOf_off K ω ω' (Finset.ne_of_mem_erase hc).symm,
    pathMoment_blockOf_off K ω ω' (Finset.ne_of_mem_erase hc')]

/-- The factors `T_{i+1}^n` do not depend on block `γ_i` of the sample. -/
private theorem pathMoment_tail_congr {W L : ℕ} (K : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (E : ℝ) (γ : ℕ → Fin L) (i n : ℕ)
    {ω ω' : Ω W L} (h : ∀ y : Fin L × Fin W × Fin W, y.1 ≠ γ i → ω y = ω' y) :
    pathMoment_tail (pathMoment_H K ω) E γ (i + 1) n =
      pathMoment_tail (pathMoment_H K ω') E γ (i + 1) n := by
  unfold pathMoment_tail
  refine congrArg List.prod (List.map_congr_left fun l _ => ?_)
  rw [pathMoment_maskRes_congr K _ E fun y hy => h y fun he =>
    pathMoment_not_mem_rest γ (show i < i + 1 + l by omega) (he ▸ hy)]

/-- The half moment along a walk visiting distinct blocks ([PSSS, (2.6)] applied successively),
for `K + diag(V_a)` with a deterministic Hermitian `K`:
`𝔼‖G_{Λ_0}(γ_0, γ_0) ⋯ G_{Λ_k}(γ_k, γ_k) v‖^{1/2} ≤ (C W^{1/4})^{k+1} ‖v‖^{1/2}` for every real
`E` and every deterministic `v`. -/
theorem lintegral_walkProd_add_halfMoment : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (W L : ℕ) (K : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ), K.IsHermitian →
      ∀ (γ : ℕ → Fin L) (k : ℕ), (∀ i ≤ k, ∀ j < i, γ j ≠ γ i) →
      ∀ (E : ℝ) (v : Fin W → ℂ),
        ∫⁻ ω, ENNReal.ofReal (Real.sqrt
            (l2Norm (walkProd (K + blockDiagOp (gueBlock W L ω)) E γ k *ᵥ v))) ∂(μ W L) ≤
          ENNReal.ofReal ((C * (W : ℝ) ^ (1 / 4 : ℝ)) ^ (k + 1) * Real.sqrt (l2Norm v)) := by
  obtain ⟨CF, hCF, hF⟩ := gueBlock_shift_halfMoment
  refine ⟨max 1 CF, le_max_left _ _, fun W L K hK γ k hγ E v => ?_⟩
  have hdet := pathMoment_ae_det (W := W) (L := L) K E
  have key : ∀ n i, i + n ≤ k + 1 →
      ∫⁻ ω, ENNReal.ofReal (Real.sqrt
          (l2Norm (pathMoment_tail (pathMoment_H K ω) E γ i n *ᵥ v))) ∂(μ W L) ≤
        ENNReal.ofReal (CF * (W : ℝ) ^ (1 / 4 : ℝ)) ^ n *
          ENNReal.ofReal (Real.sqrt (l2Norm v)) := by
    intro n
    induction n with
    | zero =>
      intro i _
      simp [pathMoment_tail]
    | succ n ih =>
      intro i hin
      have hxΛ : γ i ∈ walkRest γ i := by
        simp only [walkRest, Finset.mem_filter, Finset.mem_univ, true_and]
        exact fun j hj => (hγ i (by omega) j hj).symm
      obtain ⟨A, hA⟩ : ∃ A : Ω W L → Matrix (Fin W) (Fin W) ℂ, A = fun ω =>
          blockOf K (γ i) (γ i) - (E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) -
            selfEnergy (pathMoment_H K ω) (walkRest γ i) (γ i) E := ⟨_, rfl⟩
      obtain ⟨u, hu⟩ : ∃ u : Ω W L → Fin W → ℂ,
          u = fun ω => pathMoment_tail (pathMoment_H K ω) E γ (i + 1) n *ᵥ v := ⟨_, rfl⟩
      have hAm : Measurable A := Measurable.of_eval_matrix _ fun α β => by
        simp only [hA, Matrix.sub_apply]
        exact measurable_const.sub
          (pathMoment_measurable_selfEnergy K _ (γ i) E).eval_matrix
      have hum : Measurable u := by
        rw [hu]
        exact pathMoment_measurable_mulVec (pathMoment_measurable_tail K E γ n (i + 1)) v
      have hAh : ∀ ω, (A ω).IsHermitian := fun ω => by
        rw [hA]
        exact ((pathMoment_blockOf_isHermitian hK (γ i)).sub
          (pathMoment_real_smul_one_isHermitian W E)).sub
          (selfEnergy_isHermitian (pathMoment_isHermitian hK ω) _ (γ i) E)
      have hoff : ∀ ω ω' : Ω W L, (∀ y, y.1 ≠ γ i → ω y = ω' y) → A ω = A ω' ∧ u ω = u ω' :=
        fun ω ω' h => ⟨by rw [hA]; simp only [pathMoment_selfEnergy_congr K _ (γ i) E h],
          by rw [hu]; simp only [pathMoment_tail_congr K E γ i n h]⟩
      have hae : ∀ᵐ ω ∂(μ W L),
          ENNReal.ofReal (Real.sqrt
              (l2Norm (pathMoment_tail (pathMoment_H K ω) E γ i (n + 1) *ᵥ v))) =
            ENNReal.ofReal (Real.sqrt (l2Norm ((A ω + gueBlock W L ω (γ i))⁻¹ *ᵥ u ω))) := by
        filter_upwards [hdet] with ω hω
        have hsplit : blockOf K (γ i) (γ i) + gueBlock W L ω (γ i) -
            (E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) -
            selfEnergy (pathMoment_H K ω) (walkRest γ i) (γ i) E =
            A ω + gueBlock W L ω (γ i) := by
          simp only [hA]
          abel
        rw [pathMoment_tail_succ, ← Matrix.mulVec_mulVec,
          blockOf_maskRes_self _ hxΛ E (hω _), pathMoment_blockOf_diag, hsplit, hu]
      rw [lintegral_congr_ae hae]
      refine (hF W L (γ i) A u hAm hum hAh hoff).trans ?_
      rw [pow_succ', mul_assoc, hu]
      gcongr
      exact ih (i + 1) (by omega)
  have h := key (k + 1) 0 (by omega)
  simp only [pathMoment_walkProd_eq] at h ⊢
  refine h.trans ?_
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  gcongr
  exact le_max_right _ _

/-- `K = g P_m ⊗ I_W` is Hermitian. -/
private theorem pathMoment_pathOp_zero_isHermitian (g : ℝ) (W m : ℕ) :
    (pathOp g (fun _ : Fin m => (0 : Matrix (Fin W) (Fin W) ℂ)) 0 0).IsHermitian :=
  pathOp_isHermitian g (fun _ => Matrix.isHermitian_zero) Matrix.isHermitian_zero
    Matrix.isHermitian_zero

/-- `(g √W)^{1/2} = g^{1/2} W^{1/4}` for `g ≥ 0`. -/
private theorem pathMoment_rpow_half {g : ℝ} (hg : 0 ≤ g) (W : ℕ) :
    (g * Real.sqrt W) ^ (1 / 2 : ℝ) = Real.sqrt g * (W : ℝ) ^ (1 / 4 : ℝ) := by
  rw [Real.mul_rpow hg (Real.sqrt_nonneg _), ← Real.sqrt_eq_rpow g, Real.sqrt_eq_rpow (W : ℝ),
    ← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num

/-- `‖a w‖₂ = |a| ‖w‖₂`. -/
private theorem pathMoment_l2Norm_smul {ι : Type*} [Fintype ι] (a : ℂ) (w : ι → ℂ) :
    l2Norm (a • w) = ‖a‖ * l2Norm w := by
  unfold l2Norm
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg a)]

/-- The path form of [PSSS, Theorem 1] at `d = 1`, `s = 1/2`, vector form: for `0 ≤ g ≤ 1`, all
blocks `x, y` of the Dirichlet path of `m` blocks, every real `E` and every deterministic `v`,
`𝔼‖G(x, y; E) v‖^{1/2} ≤ C₁ W^{1/4} (C₁ (g √W)^{1/2})^{|x-y|} ‖v‖^{1/2}`. No threshold on `g √W`
is needed, since the walk from `x` to `y` is unique. -/
theorem path_halfMoment : ∃ C₁ : ℝ, 1 ≤ C₁ ∧
    ∀ (W m : ℕ) (g : ℝ), 0 ≤ g → g ≤ 1 → ∀ (x y : Fin m) (E : ℝ) (v : Fin W → ℂ),
      ∫⁻ ω, ENNReal.ofReal (Real.sqrt (l2Norm
          (blockOf (resolventMat (pathOp g (gueBlock W m ω) 0 0) E) x y *ᵥ v))) ∂(μ W m) ≤
        ENNReal.ofReal (C₁ * (W : ℝ) ^ (1 / 4 : ℝ) *
          (C₁ * (g * Real.sqrt W) ^ (1 / 2 : ℝ)) ^ Nat.dist x y * Real.sqrt (l2Norm v)) := by
  obtain ⟨C, hC, hwalk⟩ := lintegral_walkProd_add_halfMoment
  refine ⟨C, hC, fun W m g hg0 hg1 x y E v => ?_⟩
  set K := pathOp g (fun _ : Fin m => (0 : Matrix (Fin W) (Fin W) ℂ)) 0 0 with hK
  have hKh : K.IsHermitian := pathMoment_pathOp_zero_isHermitian g W m
  set k := Nat.dist x y with hk
  have hc : ‖(-((g / max 1 g : ℝ) : ℂ)) ^ k‖ = g ^ k := by
    rw [norm_pow, max_eq_left hg1, div_one, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hg0]
  have hsq : Real.sqrt (g ^ k) = Real.sqrt g ^ k := by
    rw [show g ^ k = (Real.sqrt g ^ k) ^ 2 by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hg0], Real.sqrt_sq (by positivity)]
  have hpt : ∀ᵐ ω ∂(μ W m),
      ENNReal.ofReal (Real.sqrt (l2Norm
          (blockOf (resolventMat (pathOp g (gueBlock W m ω) 0 0) E) x y *ᵥ v))) =
        ENNReal.ofReal (Real.sqrt g ^ k) * ENNReal.ofReal (Real.sqrt (l2Norm
          (walkProd (K + blockDiagOp (gueBlock W m ω)) E (pathWalk x y) k *ᵥ v))) := by
    filter_upwards [pathMoment_ae_det (W := W) (L := m) K E] with ω hω
    have hdet : ∀ Λ : Finset (Fin m), (maskMat {p | p.1 ∈ Λ}
        (pathOp g (gueBlock W m ω) 0 0 -
          (E : ℂ) • (1 : Matrix (Fin m × Fin W) (Fin m × Fin W) ℂ))).det ≠ 0 := fun Λ => by
      rw [pathOp_eq_add_blockDiagOp hg1]
      exact hω Λ
    rw [blockOf_resolventMat_pathOp_eq_walkProd g _ E hdet x y, Matrix.smul_mulVec,
      pathMoment_l2Norm_smul, Real.sqrt_mul (norm_nonneg _), hc, hsq,
      ENNReal.ofReal_mul (by positivity), pathOp_eq_add_blockDiagOp hg1]
  rw [lintegral_congr_ae hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul_right (hwalk W m K hKh (pathWalk x y) k
    (fun i hi j hj => pathWalk_ne x y hi hj) E v) _).trans_eq ?_
  rw [← ENNReal.ofReal_mul (by positivity), pathMoment_rpow_half hg0]
  congr 1
  ring

/-- The operator norm of a square matrix is at most the sum of the norms of its columns. -/
private theorem pathMoment_opNorm_le_sum {W : ℕ} (M : Matrix (Fin W) (Fin W) ℂ) :
    ‖M‖ ≤ ∑ β, l2Norm (M *ᵥ Pi.single β 1) := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _) fun x => ?_
  have hdec : M *ᵥ x.ofLp = ∑ β, x.ofLp β • (M *ᵥ Pi.single β 1) := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have h1 : ‖Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) M x‖ = l2Norm (M *ᵥ x.ofLp) := by
    rw [l2Norm_eq_norm_toLp]
    rfl
  have h2 : l2Norm (∑ β, x.ofLp β • (M *ᵥ Pi.single β 1)) ≤
      ∑ β, ‖x.ofLp β‖ * l2Norm (M *ᵥ Pi.single β 1) := by
    rw [l2Norm_eq_norm_toLp, WithLp.toLp_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_)
    rw [← l2Norm_eq_norm_toLp, pathMoment_l2Norm_smul]
  rw [h1, hdec, Finset.sum_mul]
  refine h2.trans (Finset.sum_le_sum fun β _ => ?_)
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x β) (Real.sqrt_nonneg _)

/-- `‖M‖^{1/2} ≤ Σ_β ‖M e_β‖^{1/2}`, the summation over the `W` coordinate vectors in the proof
of Theorem 3.1 [thm:strong-upper]. -/
private theorem pathMoment_enorm_le_sum {W : ℕ} (M : Matrix (Fin W) (Fin W) ℂ) :
    ‖M‖ₑ ^ (1 / 2 : ℝ) ≤
      ∑ β, ENNReal.ofReal (Real.sqrt (l2Norm (M *ᵥ Pi.single β 1))) := by
  have hnn : ∀ β, 0 ≤ Real.sqrt (l2Norm (M *ᵥ Pi.single β 1)) := fun _ => Real.sqrt_nonneg _
  rw [← ENNReal.ofReal_sum_of_nonneg fun β _ => hnn β, ← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), ← Real.sqrt_eq_rpow]
  refine ENNReal.ofReal_le_ofReal ?_
  refine (Real.sqrt_le_sqrt (pathMoment_opNorm_le_sum M)).trans ?_
  rw [Real.sqrt_le_left (Finset.sum_nonneg fun β _ => hnn β)]
  have hsum : ∀ s : Finset (Fin W), ∑ β ∈ s, l2Norm (M *ᵥ Pi.single β 1) ≤
      (∑ β ∈ s, Real.sqrt (l2Norm (M *ᵥ Pi.single β 1))) ^ 2 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have h := Real.sq_sqrt (show 0 ≤ l2Norm (M *ᵥ Pi.single a 1) from Real.sqrt_nonneg _)
      have h0 := hnn a
      have h1 : 0 ≤ ∑ β ∈ s, Real.sqrt (l2Norm (M *ᵥ Pi.single β 1)) :=
        Finset.sum_nonneg fun β _ => hnn β
      nlinarith [mul_nonneg h0 h1]
  exact hsum univ

/-- `‖e_β‖₂ = 1`. -/
private theorem pathMoment_l2Norm_single {W : ℕ} (β : Fin W) :
    l2Norm (Pi.single β 1 : Fin W → ℂ) = 1 := by
  simp [l2Norm, Pi.single_apply, apply_ite]

/-- The path form of [PSSS, Theorem 1] as stated in the proof of Theorem 3.1 [thm:strong-upper]:
there are `c_* ∈ (0, 1)` and a width threshold such that (8.2) [up:eq:fmr-pointwise] holds at
exponent `1/2`, with `C = 9/4`, `c = 𝔟 = 1`, on the Dirichlet path of every number of blocks and
at every real energy, for `0 ≤ g ≤ c_* W^{-1/2}`. -/
theorem fracPath_strong : ∃ cs : ℝ, 0 < cs ∧ cs < 1 ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ (m : ℕ) (g : ℝ),
    0 ≤ g → g ≤ cs * (W : ℝ) ^ (-(1 / 2 : ℝ)) → FracPath W m g Set.univ (1 / 2) (9 / 4) 1 1 := by
  obtain ⟨C₁, hC₁, hP⟩ := path_halfMoment
  have hC₁p : 0 < C₁ := by linarith
  have he : 1 < Real.exp 1 := by
    simp
  have hcs0 : 0 < (Real.exp 1 * C₁)⁻¹ ^ 2 := by positivity
  have hcs1 : (Real.exp 1 * C₁)⁻¹ ^ 2 < 1 := by
    have h1 : 1 < Real.exp 1 * C₁ := by nlinarith
    exact pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ h1) two_ne_zero
  refine ⟨_, hcs0, hcs1, ⌈C₁⌉₊, fun W hW m g hg0 hg E _ x y => ?_⟩
  have hWC : C₁ ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hW)
  have hW1 : (1 : ℝ) ≤ W := hC₁.trans hWC
  have hW0 : (0 : ℝ) < W := by linarith
  set cs := (Real.exp 1 * C₁)⁻¹ ^ 2 with hcs
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.2 hW0
  have hneg : (W : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt W)⁻¹ := by
    rw [Real.rpow_neg hW0.le, Real.sqrt_eq_rpow]
  have hgs : g * Real.sqrt W ≤ cs := by
    rw [hneg] at hg
    calc g * Real.sqrt W ≤ cs * (Real.sqrt W)⁻¹ * Real.sqrt W := by gcongr
      _ = cs := by field_simp
  have hs1 : 1 ≤ Real.sqrt W := Real.one_le_sqrt.mpr hW1
  have hg1 : g ≤ 1 := by nlinarith
  have hq : C₁ * (g * Real.sqrt W) ^ (1 / 2 : ℝ) ≤ (Real.exp 1)⁻¹ := by
    have h1 : (g * Real.sqrt W) ^ (1 / 2 : ℝ) ≤ cs ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hgs (by norm_num)
    have e : cs ^ (1 / 2 : ℝ) = (Real.exp 1 * C₁)⁻¹ := by
      rw [hcs, ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
    rw [e] at h1
    calc C₁ * (g * Real.sqrt W) ^ (1 / 2 : ℝ) ≤ C₁ * (Real.exp 1 * C₁)⁻¹ :=
          mul_le_mul_of_nonneg_left h1 hC₁p.le
      _ = (Real.exp 1)⁻¹ := by field_simp
  have hq0 : 0 ≤ C₁ * (g * Real.sqrt W) ^ (1 / 2 : ℝ) :=
    mul_nonneg hC₁p.le (Real.rpow_nonneg (by positivity) _)
  set k := Nat.dist x y with hk
  have hdist : |((x : ℕ) : ℝ) - (y : ℕ)| = (k : ℝ) := by
    rcases le_total (x : ℕ) (y : ℕ) with h | h
    · rw [hk, Nat.dist_eq_sub_of_le h, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by
        exact_mod_cast h)), Nat.cast_sub h]
    · rw [hk, Nat.dist_eq_sub_of_le_right h, abs_of_nonneg (sub_nonneg.mpr (by
        exact_mod_cast h)), Nat.cast_sub h]
  set K := pathOp g (fun _ : Fin m => (0 : Matrix (Fin W) (Fin W) ℂ)) 0 0 with hK
  have hm : ∀ β : Fin W, Measurable fun ω : Ω W m => ENNReal.ofReal (Real.sqrt (l2Norm
      (blockOf (resolventMat (pathOp g (gueBlock W m ω) 0 0) E) x y *ᵥ Pi.single β 1))) := by
    intro β
    have hH : ∀ ω, pathOp g (gueBlock W m ω) 0 0 = pathMoment_H K ω :=
      fun ω => pathOp_eq_add_blockDiagOp hg1 _
    simp only [hH, ← maskRes_univ]
    exact ENNReal.measurable_ofReal.comp (pathMoment_measurable_sqrt
      (pathMoment_measurable_blockOf (pathMoment_measurable_maskRes K univ E) x y) _)
  calc ∫⁻ ω, ‖blockOf (resolventMat (pathOp g (gueBlock W m ω) 0 0) E) x y‖ₑ ^ (1 / 2 : ℝ) ∂(μ W m)
      ≤ ∫⁻ ω, ∑ β, ENNReal.ofReal (Real.sqrt (l2Norm
          (blockOf (resolventMat (pathOp g (gueBlock W m ω) 0 0) E) x y *ᵥ Pi.single β 1)))
          ∂(μ W m) := lintegral_mono fun ω => pathMoment_enorm_le_sum _
    _ = ∑ β, ∫⁻ ω, ENNReal.ofReal (Real.sqrt (l2Norm
          (blockOf (resolventMat (pathOp g (gueBlock W m ω) 0 0) E) x y *ᵥ Pi.single β 1)))
          ∂(μ W m) := lintegral_finsetSum _ fun β _ => hm β
    _ ≤ ∑ _β : Fin W, ENNReal.ofReal (C₁ * (W : ℝ) ^ (1 / 4 : ℝ) * Real.exp (-1) ^ k) := by
        refine Finset.sum_le_sum fun β _ => (hP W m g hg0 hg1 x y E _).trans
          (ENNReal.ofReal_le_ofReal ?_)
        rw [pathMoment_l2Norm_single, Real.sqrt_one, mul_one, Real.exp_neg]
        gcongr
    _ = ENNReal.ofReal ((W : ℝ) * (C₁ * (W : ℝ) ^ (1 / 4 : ℝ) * Real.exp (-1) ^ k)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul hW0.le, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (9 / 4 : ℝ) *
          Real.exp (-1 * |((x : ℕ) : ℝ) - (y : ℕ)| / 1)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hpow : (W : ℝ) ^ (9 / 4 : ℝ) = W * (W * (W : ℝ) ^ (1 / 4 : ℝ)) := by
          rw [show (9 / 4 : ℝ) = 1 + (1 + 1 / 4) by norm_num, Real.rpow_add hW0,
            Real.rpow_add hW0, Real.rpow_one]
        have hexp : Real.exp (-1 * |((x : ℕ) : ℝ) - (y : ℕ)| / 1) = Real.exp (-1) ^ k := by
          rw [hdist, ← Real.exp_nat_mul]
          congr 1
          ring
        rw [hpow, hexp]
        have hX : 0 ≤ (W : ℝ) * ((W : ℝ) ^ (1 / 4 : ℝ) * Real.exp (-1) ^ k) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hWC hX]

end LSBA
