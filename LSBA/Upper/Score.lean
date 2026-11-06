import LSBA.Upper.ScoreActive
import LSBA.Gauss.BlockSplit

/-!
# Lemma 9.4 [us:lem:score]: the Gaussian divergence of the constructed field

Lemma 9.4 [us:lem:score]: conditionally on the four preparation blocks, so that `R_4, v_4, P`
are fixed, the field `χ X` of (9.10) [us:eq:physical] built from the families of Lemma 9.3
[su:lem:chosen-generator] satisfies (9.31) [us:eq:score]
`𝔼|δ_G(χ X)|² ≤ C 𝔼[‖P v_4‖² Σ_a ‖(e_a · ∇_{v_4})(χ̂ K̂)‖²_HS] + C W (1 + M₀²) 𝔼 ‖χ̂ K̂‖²_HS
+ W g⁴ 𝔼 ‖[χ̂ L̂, R_{q-1}]‖²_HS + C W M₀ e^{-c W}`, where the last input contributes
`δ_last = W g² ⟨V_q, [χ L, R_{q-1}]⟩` with the conditional moments (9.36)
[su:eq:last-divergence-moments]. The constants `C, c` depend only on the pointwise bound `C_K`
of `‖K‖²_HS`. Expectations are over the sample of `Ω W q`; at a fixed preparation the field
depends only on the inputs `V_5, …, V_q`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Second moment of an affine function of a standard Gaussian vector. -/
private lemma Score_gauss_sq {ι : Type*} [Fintype ι] (F c : ℝ) (h : ι → ℝ) :
    ∫⁻ u, ‖F + c * ∑ k, h k * u k‖ₑ ^ 2 ∂(stdGauss ι) =
      ENNReal.ofReal (F ^ 2 + c ^ 2 * ∑ k, h k ^ 2) := by
  have hμ : stdGauss ι = Measure.pi fun _ : ι => gaussianReal (0 : ℝ) 1 := rfl
  set ℓ : (ι → ℝ) → ℝ := fun u => ∑ k, h k * u k with hℓ
  have hmem : ∀ k, MemLp (fun u : ι → ℝ => h k * u k) 2 (stdGauss ι) := fun k => by
    rw [hμ]
    exact (IsGaussian.memLp_two_id.const_mul (h k)).comp_measurePreserving
      (measurePreserving_eval (fun _ : ι => gaussianReal (0 : ℝ) 1) k)
  have hℓm : MemLp ℓ 2 (stdGauss ι) := memLp_finsetSum _ fun k _ => hmem k
  have hmean : ∫ u, ℓ u ∂(stdGauss ι) = 0 := by
    have hk : ∀ k, ∫ u, u k ∂(stdGauss ι) = 0 := fun k => by
      have hmp := measurePreserving_eval (fun _ : ι => gaussianReal (0 : ℝ) 1) k
      have := integral_map (μ := stdGauss ι) (φ := Function.eval k) (f := id)
        hmp.measurable.aemeasurable aestronglyMeasurable_id
      rw [hμ, hmp.map_eq] at this
      simpa [stdGauss, integral_id_gaussianReal] using this.symm
    rw [hℓ]
    simp only
    rw [integral_finsetSum _ fun k _ => (hmem k).integrable one_le_two]
    simp [integral_const_mul, hk]
  have hvar : Var[ℓ; stdGauss ι] = ∑ k, h k ^ 2 := by
    have : ℓ = ∑ k, fun u : ι → ℝ => (fun x : ℝ => h k * x) (u k) := by
      funext u; simp [hℓ, Finset.sum_apply]
    rw [this, hμ, variance_sum_pi]
    · refine Finset.sum_congr rfl fun k _ => ?_
      change Var[fun x : ℝ => h k * id x; gaussianReal 0 1] = _
      rw [variance_const_mul, variance_id_gaussianReal]
      simp
    · exact fun k => IsGaussian.memLp_two_id.const_mul _
  have hX : MemLp (fun u : ι → ℝ => F + c * ℓ u) 2 (stdGauss ι) :=
    (memLp_const F).add (hℓm.const_mul c)
  have hXmean : ∫ u, (F + c * ℓ u) ∂(stdGauss ι) = F := by
    rw [integral_add (integrable_const F) ((hℓm.integrable one_le_two).const_mul c),
      integral_const_mul, hmean]
    simp
  have hXvar : Var[fun u : ι → ℝ => F + c * ℓ u; stdGauss ι] = c ^ 2 * ∑ k, h k ^ 2 := by
    rw [variance_const_add ((hℓm.const_mul c).aestronglyMeasurable), 
      variance_const_mul, hvar]
  have h2 := variance_eq_sub hX
  rw [hXvar, hXmean] at h2
  have hint : Integrable (fun u : ι → ℝ => (F + c * ℓ u) ^ 2) (stdGauss ι) := hX.integrable_sq
  have hint2 : ∫ u, (F + c * ℓ u) ^ 2 ∂(stdGauss ι) = F ^ 2 + c ^ 2 * ∑ k, h k ^ 2 := by
    simp only [Pi.pow_apply] at h2
    linarith
  rw [← hint2, ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun u =>
    sq_nonneg _)]
  refine lintegral_congr fun u => ?_
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-- The sample with block `a` equal to `u` and the other blocks equal to `r`. -/
private def Score_unsplit (W q : ℕ) (a : Fin q)
    (z : (Fin W × Fin W → ℝ) × ({x : Fin q × Fin W × Fin W // x.1 ≠ a} → ℝ)) : Ω W q :=
  fun x => if h : x.1 = a then z.1 x.2 else z.2 ⟨x, h⟩

private lemma Score_unsplit_blockSplit (W q : ℕ) (a : Fin q) (ω : Ω W q) :
    Score_unsplit W q a (blockSplit W q a ω) = ω := by
  funext x
  by_cases h : x.1 = a
  · obtain ⟨i, k⟩ := x
    simp only at h
    subst h
    simp [Score_unsplit, blockSplit]
  · simp [Score_unsplit, blockSplit, h]

private lemma Score_blockSplit_unsplit (W q : ℕ) (a : Fin q)
    (z : (Fin W × Fin W → ℝ) × ({x : Fin q × Fin W × Fin W // x.1 ≠ a} → ℝ)) :
    blockSplit W q a (Score_unsplit W q a z) = z := by
  refine Prod.ext ?_ ?_
  · funext k
    simp [blockSplit, Score_unsplit]
  · funext x
    simp [blockSplit, Score_unsplit, x.2]

private lemma Score_measurable_unsplit (W q : ℕ) (a : Fin q) :
    Measurable (Score_unsplit W q a) := by
  refine measurable_pi_iff.2 fun x => ?_
  by_cases h : x.1 = a
  · simp only [Score_unsplit, h, dite_true]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [Score_unsplit, h, dite_false]
    exact (measurable_pi_apply _).comp measurable_snd

private lemma Score_measurable_blockSplit (W q : ℕ) (a : Fin q) :
    Measurable (blockSplit W q a) :=
  Measurable.prodMk (measurable_pi_iff.2 fun _ => measurable_pi_apply _)
    (measurable_pi_iff.2 fun _ => measurable_pi_apply _)

private lemma Score_embedding_blockSplit (W q : ℕ) (a : Fin q) :
    MeasurableEmbedding (blockSplit W q a) :=
  (MeasurableEquiv.mk ⟨blockSplit W q a, Score_unsplit W q a,
    Score_unsplit_blockSplit W q a, Score_blockSplit_unsplit W q a⟩
    (Score_measurable_blockSplit W q a) (Score_measurable_unsplit W q a)).measurableEmbedding

/-- The second marginal of a product with a probability measure does not increase the integral. -/
private lemma Score_lintegral_le_prod_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ₁ : Measure α) [IsProbabilityMeasure μ₁] (ν₂ : Measure β) [SFinite ν₂] (φ : β → ℝ≥0∞) :
    ∫⁻ r, φ r ∂ν₂ ≤ ∫⁻ z, φ z.2 ∂(μ₁.prod ν₂) := by
  obtain ⟨g, hg, hgφ, hint⟩ := exists_measurable_le_lintegral_eq ν₂ φ
  rw [hint]
  calc ∫⁻ r, g r ∂ν₂ = ∫⁻ z, g z.2 ∂(μ₁.prod ν₂) := by
        rw [lintegral_prod (fun z : α × β => g z.2) (hg.comp measurable_snd).aemeasurable]
        simp
    _ ≤ ∫⁻ z, φ z.2 ∂(μ₁.prod ν₂) := lintegral_mono fun z => hgφ z.2

/-- Pythagoras over the independent block `a`: if `A` and `h` do not depend on block `a`, then
`𝔼 (A + c Σ_k h_k ω_{(a,k)})² ≤ 𝔼 A² + c² 𝔼 Σ_k h_k²`. -/
private lemma Score_split_bound (W q : ℕ) (a : Fin q) (c : ℝ) (A : Ω W q → ℝ)
    (h : Ω W q → Fin W × Fin W → ℝ) (hA : Measurable A)
    (hag : ∀ ω ω' : Ω W q, (∀ x : Fin q × Fin W × Fin W, x.1 ≠ a → ω x = ω' x) →
      A ω = A ω' ∧ h ω = h ω') :
    ∫⁻ ω, ‖A ω + c * ∑ k, h ω k * ω (a, k)‖ₑ ^ 2 ∂(μ W q) ≤
      ∫⁻ ω, ‖A ω‖ₑ ^ 2 ∂(μ W q) +
        ENNReal.ofReal (c ^ 2) * ∫⁻ ω, ENNReal.ofReal (∑ k, h ω k ^ 2) ∂(μ W q) := by
  set ν₂ := stdGauss {x : Fin q × Fin W × Fin W // x.1 ≠ a} with hν₂
  set μ₁ := stdGauss (Fin W × Fin W) with hμ₁
  have hmp := measurePreserving_blockSplit W q a
  have hemb := Score_embedding_blockSplit W q a
  -- the data at the sample with block `a` set to zero
  set A₀ : ({x : Fin q × Fin W × Fin W // x.1 ≠ a} → ℝ) → ℝ :=
    fun r => A (Score_unsplit W q a (0, r)) with hA₀
  set h₀ : ({x : Fin q × Fin W × Fin W // x.1 ≠ a} → ℝ) → Fin W × Fin W → ℝ :=
    fun r => h (Score_unsplit W q a (0, r)) with hh₀
  have hag' : ∀ ω : Ω W q, A ω = A₀ (blockSplit W q a ω).2 ∧ h ω = h₀ (blockSplit W q a ω).2 :=
    fun ω => hag _ _ fun x hx => by simp [Score_unsplit, blockSplit, hx]
  have hA₀m : Measurable A₀ :=
    hA.comp ((Score_measurable_unsplit W q a).comp (measurable_const.prodMk measurable_id))
  -- the integrand as a function of the split sample
  set G : (Fin W × Fin W → ℝ) × ({x : Fin q × Fin W × Fin W // x.1 ≠ a} → ℝ) → ℝ≥0∞ :=
    fun z => ‖A₀ z.2 + c * ∑ k, h₀ z.2 k * z.1 k‖ₑ ^ 2 with hG
  have h1 : ∫⁻ ω, ‖A ω + c * ∑ k, h ω k * ω (a, k)‖ₑ ^ 2 ∂(μ W q) =
      ∫⁻ z, G z ∂(μ₁.prod ν₂) := by
    rw [← hmp.lintegral_comp_emb hemb G]
    refine lintegral_congr fun ω => ?_
    rw [(hag' ω).1, (hag' ω).2]
    rfl
  -- integrate the block `a` first
  have h2 : ∫⁻ z, G z ∂(μ₁.prod ν₂) ≤
      ∫⁻ r, ENNReal.ofReal (A₀ r ^ 2 + c ^ 2 * ∑ k, h₀ r k ^ 2) ∂ν₂ := by
    rw [← lintegral_prod_swap (fun z => G z)]
    refine (lintegral_prod_le _).trans (le_of_eq (lintegral_congr fun r => ?_))
    exact Score_gauss_sq (A₀ r) c (h₀ r)
  have h3 : ∫⁻ r, ENNReal.ofReal (A₀ r ^ 2 + c ^ 2 * ∑ k, h₀ r k ^ 2) ∂ν₂ =
      ∫⁻ r, ENNReal.ofReal (A₀ r ^ 2) ∂ν₂ +
        ENNReal.ofReal (c ^ 2) * ∫⁻ r, ENNReal.ofReal (∑ k, h₀ r k ^ 2) ∂ν₂ := by
    have hmeas : Measurable fun r => ENNReal.ofReal (A₀ r ^ 2) :=
      ((hA₀m.pow_const 2)).ennreal_ofReal
    have hsum : ∀ r, 0 ≤ ∑ k, h₀ r k ^ 2 := fun r => Finset.sum_nonneg fun k _ => sq_nonneg _
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_add_left hmeas]
    refine lintegral_congr fun r => ?_
    rw [← ENNReal.ofReal_mul (sq_nonneg c), ← ENNReal.ofReal_add (sq_nonneg _)
      (mul_nonneg (sq_nonneg c) (hsum r))]
  -- return to the original sample space
  have h4 : ∫⁻ r, ENNReal.ofReal (A₀ r ^ 2) ∂ν₂ ≤ ∫⁻ ω, ‖A ω‖ₑ ^ 2 ∂(μ W q) := by
    refine (Score_lintegral_le_prod_snd μ₁ ν₂ _).trans (le_of_eq ?_)
    rw [← hmp.lintegral_comp_emb hemb (fun z => ENNReal.ofReal (A₀ z.2 ^ 2))]
    refine lintegral_congr fun ω => ?_
    rw [← (hag' ω).1, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have h5 : ∫⁻ r, ENNReal.ofReal (∑ k, h₀ r k ^ 2) ∂ν₂ ≤
      ∫⁻ ω, ENNReal.ofReal (∑ k, h ω k ^ 2) ∂(μ W q) := by
    refine (Score_lintegral_le_prod_snd μ₁ ν₂ _).trans (le_of_eq ?_)
    rw [← hmp.lintegral_comp_emb hemb (fun z => ENNReal.ofReal (∑ k, h₀ z.2 k ^ 2))]
    refine lintegral_congr fun ω => ?_
    rw [← (hag' ω).2]
  rw [h1]
  exact h2.trans (h3.le.trans (add_le_add h4 (by gcongr)))

/-! ### Locality in the last block -/

/-- Samples that agree outside block `a` have the same blocks `V_i`, `i ≠ a`. -/
private lemma Score_block_eq {W q : ℕ} {a : Fin q} {ω ω' : Ω W q}
    (hag : ∀ x : Fin q × Fin W × Fin W, x.1 ≠ a → ω x = ω' x) {i : Fin q} (hi : i ≠ a) :
    gueBlock W q ω i = gueBlock W q ω' i := by
  have h : ∀ α β, ω (i, α, β) = ω' (i, α, β) := fun α β => hag (i, α, β) hi
  ext α β
  simp only [gueBlock, Matrix.of_apply, h]

/-- `R_j` and `R_{[j,5]}` depend only on the inputs of index `< j`. -/
private lemma Score_chart_congr {W q : ℕ} (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ)
    {ω ω' : Ω W q} {m : ℕ} (h : ∀ k < m, blockSeq W q ω k = blockSeq W q ω' k) :
    ∀ j ≤ m, chartR W g E q R ω j = chartR W g E q R ω' j ∧
      chartProd W g E q R ω j = chartProd W g E q R ω' j := by
  intro j
  induction j with
  | zero => intro _; simp [chartR, chartProd]
  | succ j ih =>
    intro hj
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hR : chartR W g E q R ω (j + 1) = chartR W g E q R ω' (j + 1) := by
      simp only [chartR]
      split_ifs with hj4
      · rfl
      · rw [h (j) (by omega), h1]
    refine ⟨hR, ?_⟩
    simp only [chartProd]
    split_ifs with hj4
    · rfl
    · rw [hR, h2]

/-- Samples that agree outside the last block `a = q - 1` have the same cutoff `χ̂(·, v)`, generator
`K̂(·, v)`, matrix `R_{q-1}` and correction `L` (9.9) [us:eq:L]. -/
private lemma Score_frozen {W q : ℕ} {g E : ℝ} {R P : Matrix (Fin W) (Fin W) ℂ} {v : Fin W → ℂ}
    {Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ} {χh : Ω W q → (Fin W → ℂ) → ℝ}
    (hF : GenFamily W q g E P R Kh χh) {a : Fin q} (ha : (a : ℕ) + 1 = q) {ω ω' : Ω W q}
    (hag : ∀ x : Fin q × Fin W × Fin W, x.1 ≠ a → ω x = ω' x) :
    Kh ω v = Kh ω' v ∧ χh ω v = χh ω' v ∧
      chartR W g E q R ω (q - 1) = chartR W g E q R ω' (q - 1) ∧
      smallCorr W g E q R v (Kh ω v) ω = smallCorr W g E q R v (Kh ω' v) ω' := by
  have hKχ := hF.1 ω ω' (fun i _ hi2 => Score_block_eq hag (fun h => by
    have : (i : ℕ) = a := by rw [h]
    omega)) v
  have hbs : ∀ k < q - 1, blockSeq W q ω k = blockSeq W q ω' k := fun k hk => by
    have hkq : k < q := by omega
    simp only [blockSeq, hkq, dite_true]
    exact Score_block_eq hag (fun h => by
      have : k = (a : ℕ) := congrArg Fin.val h
      omega)
  obtain ⟨hR, hP⟩ := Score_chart_congr g E R hbs (q - 1) le_rfl
  refine ⟨hKχ.1, hKχ.2, hR, ?_⟩
  simp only [smallCorr, hP, hKχ.1]

/-! ### Hermiticity -/

/-- `R_j` is Hermitian for Hermitian `R`. -/
private lemma Score_chartR_isHermitian {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    (hR : R.IsHermitian) (ω : Ω W q) (j : ℕ) : (chartR W g E q R ω j).IsHermitian := by
  have hB : ∀ k, (blockSeq W q ω k).IsHermitian := by
    intro k
    unfold blockSeq
    split_ifs
    · exact gueBlock_isHermitian W q ω _
    · exact Matrix.isHermitian_zero
  have hs : ∀ (r : ℝ) (A : Matrix (Fin W) (Fin W) ℂ), A.IsHermitian →
      (((r : ℂ)) • A).IsHermitian := by
    intro r A hA
    unfold Matrix.IsHermitian at hA ⊢
    rw [Matrix.conjTranspose_smul, hA]
    simp
  have hs2 : ∀ A : Matrix (Fin W) (Fin W) ℂ, A.IsHermitian →
      (((g : ℂ) ^ 2) • A).IsHermitian := by
    intro A hA
    have := hs (g ^ 2) A hA
    simpa using this
  have hE : ((E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)).IsHermitian := by
    exact hs E 1 Matrix.isHermitian_one
  induction j with
  | zero => simpa [chartR] using hR
  | succ j ih =>
    simp only [chartR]
    split_ifs
    · exact hR
    · exact ((hB j).sub hE |>.sub (hs2 _ ih)).inv

/-- Under (9.8) [su:eq:generator-normalization], `L* = -L` (9.12) [su:eq:correction-identities]. -/
private lemma Score_smallCorr_skew {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    {v : Fin W → ℂ} {K : Matrix (Fin W) (Fin W) ℂ} {ω : Ω W q}
    (hn : IsGenNormalized W g E q R v K ω) :
    (smallCorr W g E q R v K ω)ᴴ = -smallCorr W g E q R v K ω := by
  apply (rotCorr_spec _).1
  set P := chartProd W g E q R ω (q - 1)
  have h1 : (star (P *ᵥ v) ⬝ᵥ (P *ᵥ (K *ᵥ v) - P *ᵥ v)).re = 0 := by
    rw [dotProduct_sub, Complex.sub_re]
    have h2 : star (P *ᵥ v) ⬝ᵥ (P *ᵥ v) = ((∑ i, ‖(P *ᵥ v) i‖ ^ 2 : ℝ) : ℂ) := by
      simp [dotProduct, Complex.conj_mul', Complex.ofReal_sum]
    rw [h2, Complex.ofReal_re]
    have hn' := hn
    unfold IsGenNormalized at hn'
    rw [hn']
    ring
  exact h1

/-- The commutator of a skew-Hermitian matrix with a Hermitian one is Hermitian. -/
private lemma Score_comm_isHermitian {W : ℕ} {A B : Matrix (Fin W) (Fin W) ℂ}
    (hA : Aᴴ = -A) (hB : B.IsHermitian) : (A * B - B * A).IsHermitian := by
  have hB' : Bᴴ = B := hB
  change (A * B - B * A)ᴴ = A * B - B * A
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hA, hB']
  noncomm_ring

/-- `(χ K)* = -(χ K)` and `(χ L)* = -(χ L)` for the real cutoff value `χ`: on `{χ ≠ 0}` by
`K* = -K` and (9.12) [su:eq:correction-identities], on `{χ = 0}` trivially. -/
private lemma Score_cut_skew {W q : ℕ} {g E M₀ CK : ℝ} {R P : Matrix (Fin W) (Fin W) ℂ}
    {v : Fin W → ℂ} {Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ}
    {χh : Ω W q → (Fin W → ℂ) → ℝ} (hD : ScoreData W q g E M₀ CK R P v Kh χh) (ω : Ω W q) :
    (((χh ω v : ℝ) : ℂ) • Kh ω v)ᴴ = -(((χh ω v : ℝ) : ℂ) • Kh ω v) ∧
    (((χh ω v : ℝ) : ℂ) • smallCorr W g E q R v (Kh ω v) ω)ᴴ =
      -(((χh ω v : ℝ) : ℂ) • smallCorr W g E q R v (Kh ω v) ω) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hK, -⟩ := hD
  by_cases hχ : χh ω v = 0
  · simp [hχ]
  · obtain ⟨hk1, -, hk3, -⟩ := hK ω hχ
    have hL := Score_smallCorr_skew hk3
    refine ⟨?_, ?_⟩
    · rw [Matrix.conjTranspose_smul, hk1]
      simp
    · rw [Matrix.conjTranspose_smul, hL]
      simp

/-! ### Splitting the field -/

/-- The part of the field `χ X` of (9.10) [us:eq:physical], in standard coordinates, on the blocks
`0, …, q - 2` (the inputs `V_1, …, V_{q-1}`). -/
private def Score_Yact (W q : ℕ) (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ)
    (Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ) (χh : Ω W q → (Fin W → ℂ) → ℝ)
    (η : Ω W q) : Ω W q :=
  χh η v • hermCoord W q fun i =>
    if (i : ℕ) + 1 < q then smallField W g E q R v (Kh η v) η i else 0

/-- The part of the field `χ X` of (9.10) [us:eq:physical], in standard coordinates, on the last
block `q - 1` (the input `V_q`). -/
private def Score_Ylast (W q : ℕ) (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ)
    (Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ) (χh : Ω W q → (Fin W → ℂ) → ℝ)
    (η : Ω W q) : Ω W q :=
  χh η v • hermCoord W q fun i =>
    if (i : ℕ) + 1 < q then 0 else smallField W g E q R v (Kh η v) η i

private lemma Score_field_split (W q : ℕ) (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ)
    (v : Fin W → ℂ) (Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ)
    (χh : Ω W q → (Fin W → ℂ) → ℝ) (η : Ω W q) :
    χh η v • hermCoord W q (smallField W g E q R v (Kh η v) η) =
      Score_Yact W q g E R v Kh χh η + Score_Ylast W q g E R v Kh χh η := by
  unfold Score_Yact Score_Ylast
  rw [← smul_add, ← (hermCoord_isLinearMap W q).map_add]
  congr 2
  funext i
  by_cases h : (i : ℕ) + 1 < q <;> simp [h]

private lemma Score_lineDeriv_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (x v : E) : lineDeriv ℝ (fun _ : E => c) x v = 0 := by
  unfold lineDeriv
  simp

private lemma Score_lineDeriv_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x v : E} (hf : LineDifferentiableAt ℝ f x v)
    (hg : LineDifferentiableAt ℝ g x v) :
    lineDeriv ℝ (fun y => f y + g y) x v = lineDeriv ℝ f x v + lineDeriv ℝ g x v := by
  have h1 := hf.hasLineDerivAt
  have h2 := hg.hasLineDerivAt
  unfold HasLineDerivAt at h1 h2
  exact (h1.add h2).deriv

/-- `δ_G Y` at `x` depends only on the values of `Y_i` along the `i`-th coordinate line. -/
private lemma Score_gaussDiv_congr_lines {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Y Y' : (ι → ℝ) → ι → ℝ} (x : ι → ℝ)
    (h : ∀ (i : ι) (t : ℝ), Y (x + t • Pi.single i 1) i = Y' (x + t • Pi.single i 1) i) :
    gaussDiv Y x = gaussDiv Y' x := by
  unfold gaussDiv
  refine Finset.sum_congr rfl fun i _ => ?_
  have h0 := h i 0
  simp only [zero_smul, add_zero] at h0
  rw [h0]
  congr 1
  unfold lineDeriv
  congr 1
  funext t
  exact h i t

/-- `δ_G (Y₁ + Y₂)` when each component is zero in one of the two fields. -/
private lemma Score_gaussDiv_add_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Y₁ Y₂ : (ι → ℝ) → ι → ℝ} (x : ι → ℝ)
    (hsplit : ∀ i, (∀ y, Y₁ y i = 0) ∨ (∀ y, Y₂ y i = 0)) :
    gaussDiv (fun y => Y₁ y + Y₂ y) x = gaussDiv Y₁ x + gaussDiv Y₂ x := by
  unfold gaussDiv
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases hsplit i with h | h
  · have hf : (fun y => Y₁ y i + Y₂ y i) = fun y => Y₂ y i := by
      funext y; simp [h y]
    have hf1 : (fun y => Y₁ y i) = fun _ => 0 := funext h
    simp only [Pi.add_apply]
    rw [hf, hf1, Score_lineDeriv_const, h x]
    ring
  · have hf : (fun y => Y₁ y i + Y₂ y i) = fun y => Y₁ y i := by
      funext y; simp [h y]
    have hf1 : (fun y => Y₂ y i) = fun _ => 0 := funext h
    simp only [Pi.add_apply]
    rw [hf, hf1, Score_lineDeriv_const, h x]
    ring

/-- `δ_G (Y₁ + Y₂)` for fields whose components are line differentiable along their own
coordinate. -/
private lemma Score_gaussDiv_add_diff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Y₁ Y₂ : (ι → ℝ) → ι → ℝ} (x : ι → ℝ)
    (h₁ : ∀ i, LineDifferentiableAt ℝ (fun y => Y₁ y i) x (Pi.single i 1))
    (h₂ : ∀ i, LineDifferentiableAt ℝ (fun y => Y₂ y i) x (Pi.single i 1)) :
    gaussDiv (fun y => Y₁ y + Y₂ y) x = gaussDiv Y₁ x + gaussDiv Y₂ x := by
  unfold gaussDiv
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := Score_lineDeriv_add (h₁ i) (h₂ i)
  simp only [Pi.add_apply]
  rw [this]
  ring

/-- `ω ↦ V_i(ω)` as a continuous real-linear map. -/
private def Score_gueBlockL (W q : ℕ) (i : Fin q) :
    Ω W q →L[ℝ] Matrix (Fin W) (Fin W) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ω => gueBlock W q ω i
      map_add' := fun ω ω' => by
        ext α β
        simp only [gueBlock, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
        split_ifs <;> push_cast <;> ring
      map_smul' := fun c ω => by
        ext α β
        simp only [gueBlock, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
          Complex.real_smul, RingHom.id_apply]
        split_ifs <;> push_cast <;> ring }

/-- `hermCoord` as a continuous real-linear map. -/
private def Score_hermCoordL (W q : ℕ) :
    (Fin q → Matrix (Fin W) (Fin W) ℂ) →L[ℝ] Ω W q :=
  LinearMap.toContinuousLinearMap (IsLinearMap.mk' (hermCoord W q) (hermCoord_isLinearMap W q))

/-- The conjugation fields `V_i ↦ [A, V_i - c_i]` of Lemma 9.4 [us:lem:score] are differentiable. -/
private lemma Score_comm_field_differentiable (W q : ℕ) (S : Finset (Fin q))
    (A : Matrix (Fin W) (Fin W) ℂ) (c : Fin q → Matrix (Fin W) (Fin W) ℂ) :
    Differentiable ℝ (fun η : Ω W q => hermCoord W q fun i => if i ∈ S then
      A * (gueBlock W q η i - c i) - (gueBlock W q η i - c i) * A else 0) := by
  have hV : ∀ i, Differentiable ℝ fun η : Ω W q => gueBlock W q η i :=
    fun i => (Score_gueBlockL W q i).differentiable
  have h : (fun η : Ω W q => hermCoord W q fun i => if i ∈ S then
      A * (gueBlock W q η i - c i) - (gueBlock W q η i - c i) * A else 0) =
      fun η => Score_hermCoordL W q (fun i => if i ∈ S then
      A * (gueBlock W q η i - c i) - (gueBlock W q η i - c i) * A else 0) := rfl
  rw [h]
  refine (Score_hermCoordL W q).differentiable.comp (differentiable_pi.2 fun i => ?_)
  by_cases hi : i ∈ S
  · simp only [hi, ite_true]
    exact ((differentiable_const A).mul ((hV i).sub (differentiable_const _))).sub
      (((hV i).sub (differentiable_const _)).mul (differentiable_const A))
  · simp only [hi, ite_false]
    exact differentiable_const _

/-! ### The last block -/

/-- The matrix `[χ L, R_{q-1}]` of (9.36) [su:eq:last-divergence-moments]. -/
private def Score_Hm (W q : ℕ) (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ)
    (Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ) (χh : Ω W q → (Fin W → ℂ) → ℝ)
    (ω : Ω W q) : Matrix (Fin W) (Fin W) ℂ :=
  (χh ω v : ℂ) • smallCorr W g E q R v (Kh ω v) ω * chartR W g E q R ω (q - 1) -
    chartR W g E q R ω (q - 1) * (χh ω v : ℂ) • smallCorr W g E q R v (Kh ω v) ω

private lemma Score_Hm_isHermitian {W q : ℕ} {g E M₀ CK : ℝ} {R P : Matrix (Fin W) (Fin W) ℂ}
    {v : Fin W → ℂ} {Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ}
    {χh : Ω W q → (Fin W → ℂ) → ℝ} (hD : ScoreData W q g E M₀ CK R P v Kh χh) (ω : Ω W q) :
    (Score_Hm W q g E R v Kh χh ω).IsHermitian :=
  Score_comm_isHermitian (Score_cut_skew hD ω).2
    (Score_chartR_isHermitian hD.2.2.2.2.2.1 ω (q - 1))

/-- The conjugation field `V_q ↦ [A, V_q - c]` of the last block, in standard coordinates. -/
private def Score_Z (W q : ℕ) (a : Fin q) (A c : Matrix (Fin W) (Fin W) ℂ) (η : Ω W q) : Ω W q :=
  hermCoord W q fun i => if i ∈ ({a} : Finset (Fin q)) then
    A * (gueBlock W q η i - c) - (gueBlock W q η i - c) * A else 0

private lemma Score_Z_differentiable (W q : ℕ) (a : Fin q) (A c : Matrix (Fin W) (Fin W) ℂ) :
    Differentiable ℝ (Score_Z W q a A c) :=
  Score_comm_field_differentiable W q {a} A (fun _ => c)

private lemma Score_gaussDiv_Z {W q : ℕ} (a : Fin q) {A c : Matrix (Fin W) (Fin W) ℂ}
    (hA : Aᴴ = -A) (hc : c.IsHermitian) (ω : Ω W q) :
    gaussDiv (Score_Z W q a A c) ω = -(W : ℝ) * (gueBlock W q ω a * (A * c - c * A)).trace.re := by
  have := gaussDiv_hermCoord_comm (W := W) ({a} : Finset (Fin q)) hA (c := fun _ => c)
    (fun _ => hc) ω
  rw [Finset.sum_singleton] at this
  exact this

/-- Samples that agree with `ω` outside the last block: the last part of the field `χ X` is the
sum of the conjugation fields `[χ K, V_q]` and `-[χ L, V_q - g² R_{q-1}]` with the coefficients
evaluated at `ω`. -/
private lemma Score_last_eq {W q : ℕ} {g E M₀ CK : ℝ} {R P : Matrix (Fin W) (Fin W) ℂ}
    {v : Fin W → ℂ} {Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ}
    {χh : Ω W q → (Fin W → ℂ) → ℝ} (hD : ScoreData W q g E M₀ CK R P v Kh χh) {a : Fin q}
    (ha : (a : ℕ) + 1 = q) {ω η : Ω W q}
    (hag : ∀ x : Fin q × Fin W × Fin W, x.1 ≠ a → ω x = η x) :
    Score_Ylast W q g E R v Kh χh η =
      Score_Z W q a (((χh ω v : ℝ) : ℂ) • Kh ω v) 0 η +
        Score_Z W q a (-(((χh ω v : ℝ) : ℂ) • smallCorr W g E q R v (Kh ω v) ω))
          (((g : ℂ) ^ 2) • chartR W g E q R ω (q - 1)) η := by
  have hq : 7 ≤ q := hD.2.1
  obtain ⟨hKω, hχω, hRω, hLω⟩ := Score_frozen hD.2.2.2.2.2.2.2.2.2.2.1 ha hag
  unfold Score_Ylast Score_Z
  rw [← (hermCoord_isLinearMap W q).map_add, ← (hermCoord_isLinearMap W q).map_smul]
  congr 1
  funext i
  by_cases hi : i = a
  · subst hi
    have h1 : ¬ ((i : ℕ) < 4) := by omega
    have h2 : (i : ℕ) ≠ 4 := by omega
    have h3 : ¬ ((i : ℕ) + 1 < q) := by omega
    simp only [Pi.smul_apply, Pi.add_apply, Finset.mem_singleton, ite_true, smallField, h1, h2, h3,
      ite_false]
    rw [← hLω, ← hRω, ← hKω, ← hχω]
    simp only [Complex.coe_smul, smul_sub, smul_mul_assoc, mul_smul_comm, neg_mul, mul_neg,
      sub_zero]
    abel
  · have h3 : (i : ℕ) + 1 < q := by
      have : (i : ℕ) ≠ a := fun h => hi (Fin.ext h)
      have := i.isLt
      omega
    simp [h3, hi]

/-- The last part of the field vanishes on the coordinates of the other blocks. -/
private lemma Score_Ylast_apply_of_ne {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    {v : Fin W → ℂ} {Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ}
    {χh : Ω W q → (Fin W → ℂ) → ℝ} {a : Fin q} (ha : (a : ℕ) + 1 = q) (η : Ω W q)
    {p : Fin q × Fin W × Fin W} (hp : p.1 ≠ a) : Score_Ylast W q g E R v Kh χh η p = 0 := by
  have h3 : (p.1 : ℕ) + 1 < q := by
    have : (p.1 : ℕ) ≠ a := fun h => hp (Fin.ext h)
    have := p.1.isLt
    omega
  simp [Score_Ylast, hermCoord, h3]

private lemma Score_Z_apply_of_ne {W q : ℕ} {a : Fin q} (A c : Matrix (Fin W) (Fin W) ℂ)
    (η : Ω W q) {p : Fin q × Fin W × Fin W} (hp : p.1 ≠ a) : Score_Z W q a A c η p = 0 := by
  simp [Score_Z, hermCoord, hp]

/-- The guarded part of the field vanishes on the coordinates of the last block. -/
private lemma Score_Yact_apply_of_eq {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    {v : Fin W → ℂ} {Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ}
    {χh : Ω W q → (Fin W → ℂ) → ℝ} {a : Fin q} (ha : (a : ℕ) + 1 = q) (η : Ω W q)
    {p : Fin q × Fin W × Fin W} (hp : p.1 = a) : Score_Yact W q g E R v Kh χh η p = 0 := by
  have h3 : ¬ ((p.1 : ℕ) + 1 < q) := by rw [hp]; omega
  simp [Score_Yact, hermCoord, h3]

/-- (9.36) [su:eq:last-divergence-moments]: the divergence of the last input is
`W g² Re Tr(V_q [χ L, R_{q-1}])`. -/
private lemma Score_gaussDiv_last {W q : ℕ} {g E M₀ CK : ℝ} {R P : Matrix (Fin W) (Fin W) ℂ}
    {v : Fin W → ℂ} {Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ}
    {χh : Ω W q → (Fin W → ℂ) → ℝ} (hD : ScoreData W q g E M₀ CK R P v Kh χh) {a : Fin q}
    (ha : (a : ℕ) + 1 = q) (ω : Ω W q) :
    gaussDiv (Score_Ylast W q g E R v Kh χh) ω =
      (W : ℝ) * g ^ 2 *
        (gueBlock W q ω a * Score_Hm W q g E R v Kh χh ω).trace.re := by
  set A : Matrix (Fin W) (Fin W) ℂ := ((χh ω v : ℝ) : ℂ) • Kh ω v with hA
  set B : Matrix (Fin W) (Fin W) ℂ :=
    ((χh ω v : ℝ) : ℂ) • smallCorr W g E q R v (Kh ω v) ω with hB
  set R' : Matrix (Fin W) (Fin W) ℂ := chartR W g E q R ω (q - 1) with hR'
  obtain ⟨hA1, hB1⟩ := Score_cut_skew hD ω
  have hR'h : R'.IsHermitian := Score_chartR_isHermitian hD.2.2.2.2.2.1 ω (q - 1)
  have hc : (((g : ℂ) ^ 2) • R').IsHermitian := by
    change (((g : ℂ) ^ 2) • R')ᴴ = ((g : ℂ) ^ 2) • R'
    rw [Matrix.conjTranspose_smul, hR'h.eq]
    congr 1
    simp
  have hnegB : (-B)ᴴ = -(-B) := by rw [Matrix.conjTranspose_neg, hB1]
  have hsplit : gaussDiv (Score_Ylast W q g E R v Kh χh) ω =
      gaussDiv (fun η => Score_Z W q a A 0 η + Score_Z W q a (-B) (((g : ℂ) ^ 2) • R') η) ω := by
    refine Score_gaussDiv_congr_lines ω fun p t => ?_
    by_cases hp : p.1 = a
    · have hag : ∀ x : Fin q × Fin W × Fin W, x.1 ≠ a →
          ω x = (ω + t • (Pi.single p (1 : ℝ) : Ω W q)) x :=
        fun x hx => by
          have : x ≠ p := fun h => hx (h ▸ hp)
          simp [this]
      rw [Score_last_eq hD ha hag]
    · rw [Score_Ylast_apply_of_ne ha _ hp]
      simp only [Pi.add_apply, Score_Z_apply_of_ne _ _ _ hp, add_zero]
  rw [hsplit, Score_gaussDiv_add_diff ω
    (fun i => (differentiableAt_pi.1 (Score_Z_differentiable W q a A 0 ω) i).lineDifferentiableAt)
    (fun i => (differentiableAt_pi.1 (Score_Z_differentiable W q a (-B)
      (((g : ℂ) ^ 2) • R') ω) i).lineDifferentiableAt),
    Score_gaussDiv_Z a hA1 Matrix.isHermitian_zero, Score_gaussDiv_Z a hnegB hc]
  have hmat : -B * (((g : ℂ) ^ 2) • R') - (((g : ℂ) ^ 2) • R') * -B =
      -(((g : ℂ) ^ 2) • Score_Hm W q g E R v Kh χh ω) := by
    simp only [Score_Hm, ← hB, ← hR', Matrix.mul_smul, Matrix.smul_mul, neg_mul, mul_neg,
      smul_sub]
    abel
  rw [hmat]
  simp only [mul_zero, zero_mul, sub_self, Matrix.trace_zero, Complex.zero_re,
    mul_zero, zero_add, Matrix.mul_neg, Matrix.mul_smul, Matrix.trace_neg, Matrix.trace_smul,
    Complex.neg_re, smul_eq_mul]
  have : ((g : ℂ) ^ 2) = ((g ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.re_ofReal_mul]
  ring

/-! ### The coordinates of the last block -/

/-- `W Re Tr(V_a H) = Σ_k ω_{(a,k)} · √W Re Tr(T_k H)`. -/
private lemma Score_trace_coord {W q : ℕ} (hW : 1 ≤ W) (ω : Ω W q) (a : Fin q)
    (H : Matrix (Fin W) (Fin W) ℂ) :
    (W : ℝ) * (gueBlock W q ω a * H).trace.re =
      ∑ k : Fin W × Fin W, (Real.sqrt W * (hermBasis W k * H).trace.re) * ω (a, k) := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hsW : Real.sqrt W ≠ 0 := (Real.sqrt_pos.2 hW').ne'
  have hs : Real.sqrt W * Real.sqrt W = W := Real.mul_self_sqrt hW'.le
  have key : (gueBlock W q ω a * H).trace.re =
      (Real.sqrt W)⁻¹ * ∑ k : Fin W × Fin W, ω (a, k.1, k.2) * (hermBasis W k * H).trace.re := by
    rw [gueBlock_eq_sum_hermBasis, Matrix.smul_mul, Matrix.sum_mul, Matrix.trace_smul,
      Matrix.trace_sum, smul_eq_mul, ← Complex.ofReal_inv, Complex.re_ofReal_mul,
      Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  rw [key, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h2 : (W : ℝ) * (Real.sqrt W)⁻¹ = Real.sqrt W :=
    calc (W : ℝ) * (Real.sqrt W)⁻¹ = (Real.sqrt W * Real.sqrt W) * (Real.sqrt W)⁻¹ := by rw [hs]
      _ = Real.sqrt W := by field_simp
  rw [← mul_assoc, h2]
  ring

/-- `Σ_k (√W Re Tr(T_k H))² = W ‖H‖²_HS` for Hermitian `H`. -/
private lemma Score_sum_sq {W q : ℕ} (a : Fin q) {H : Matrix (Fin W) (Fin W) ℂ}
    (hH : H.IsHermitian) :
    ∑ k : Fin W × Fin W, (Real.sqrt W * (hermBasis W k * H).trace.re) ^ 2 = W * hsSq H := by
  set X : Fin q → Matrix (Fin W) (Fin W) ℂ := fun i => if i = a then H else 0 with hX
  have hXh : ∀ i, (X i).IsHermitian := fun i => by
    by_cases h : i = a
    · simp [hX, h, hH]
    · simp [hX, h]
  have h1 := sum_sq_hermCoord (q := q) hXh
  rw [Fintype.sum_prod_type] at h1
  rw [Finset.sum_eq_single a] at h1
  · rw [Finset.sum_eq_single a] at h1
    · simpa [hX, hermCoord, hsSq] using h1
    · intro i _ hi
      simp [hX, hi]
    · intro h; exact absurd (Finset.mem_univ a) h
  · intro i _ hi
    refine Finset.sum_eq_zero fun k _ => ?_
    simp [hermCoord, hX, hi]
  · intro h; exact absurd (Finset.mem_univ a) h

/-! ### The active part -/

/-- The guarded part of the field takes the same value at samples that agree outside the last
block. -/
private lemma Score_Yact_eq_of_agree {W q : ℕ} {g E M₀ CK : ℝ} {R P : Matrix (Fin W) (Fin W) ℂ}
    {v : Fin W → ℂ} {Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ}
    {χh : Ω W q → (Fin W → ℂ) → ℝ} (hD : ScoreData W q g E M₀ CK R P v Kh χh) {a : Fin q}
    (ha : (a : ℕ) + 1 = q) {ω η : Ω W q}
    (hag : ∀ x : Fin q × Fin W × Fin W, x.1 ≠ a → ω x = η x) :
    Score_Yact W q g E R v Kh χh ω = Score_Yact W q g E R v Kh χh η := by
  obtain ⟨hK, hχ, -, -⟩ := Score_frozen hD.2.2.2.2.2.2.2.2.2.2.1 ha hag
  unfold Score_Yact
  rw [hK, hχ]
  congr 2
  funext i
  by_cases hi : (i : ℕ) + 1 < q
  · have hne : i ≠ a := fun h => by subst h; omega
    have hb := Score_block_eq hag hne
    simp only [hi, ite_true, smallField, hb]
  · simp [hi]

/-- `δ_G Y` at two points `x`, `x'`, when each component either vanishes identically or agrees
with its value at the other point along the coordinate line. -/
private lemma Score_gaussDiv_point_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Y : (ι → ℝ) → ι → ℝ) {x x' : ι → ℝ}
    (h : ∀ i, (∀ y, Y y i = 0) ∨ (x i = x' i ∧ ∀ t : ℝ,
      Y (x + t • Pi.single i 1) i = Y (x' + t • Pi.single i 1) i)) :
    gaussDiv Y x = gaussDiv Y x' := by
  unfold gaussDiv
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases h i with h0 | ⟨hx, hl⟩
  · simp only [h0, Score_lineDeriv_const]
    ring
  · have h1 := hl 0
    simp only [zero_smul, add_zero] at h1
    rw [hx, h1]
    congr 1
    unfold lineDeriv
    congr 1
    funext t
    exact hl t

/-- The divergence of the guarded part takes the same value at samples that agree outside the last
block. -/
private lemma Score_gaussDiv_Yact_congr {W q : ℕ} {g E M₀ CK : ℝ}
    {R P : Matrix (Fin W) (Fin W) ℂ} {v : Fin W → ℂ}
    {Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ} {χh : Ω W q → (Fin W → ℂ) → ℝ}
    (hD : ScoreData W q g E M₀ CK R P v Kh χh) {a : Fin q} (ha : (a : ℕ) + 1 = q)
    {ω ω' : Ω W q} (hag : ∀ x : Fin q × Fin W × Fin W, x.1 ≠ a → ω x = ω' x) :
    gaussDiv (Score_Yact W q g E R v Kh χh) ω = gaussDiv (Score_Yact W q g E R v Kh χh) ω' := by
  refine Score_gaussDiv_point_congr _ fun p => ?_
  by_cases hp : p.1 = a
  · exact Or.inl fun y => Score_Yact_apply_of_eq ha y hp
  · refine Or.inr ⟨hag p hp, fun t => ?_⟩
    have h := Score_Yact_eq_of_agree hD ha
      (ω := ω + t • (Pi.single p (1 : ℝ) : Ω W q)) (η := ω' + t • (Pi.single p (1 : ℝ) : Ω W q))
      (fun x hx => by simp only [Pi.add_apply, hag x hx])
    exact congrFun h p

/-- `χ̂ K̂` is differentiable at every `(ω, w)` with `w ≠ 0`: near the support of `χ̂` it is a
product of `C²` maps, away from it it vanishes. -/
private lemma Score_diff {W q : ℕ} {g E : ℝ} {P R : Matrix (Fin W) (Fin W) ℂ}
    {Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ} {χh : Ω W q → (Fin W → ℂ) → ℝ}
    (hF : GenFamily W q g E P R Kh χh) (ω : Ω W q) {w : Fin W → ℂ} (hw : w ≠ 0) :
    DifferentiableAt ℝ (fun p : Ω W q × (Fin W → ℂ) => χh p.1 p.2 • Kh p.1 p.2) (ω, w) := by
  obtain ⟨-, -, -, -, hχ, ⟨G, hGo, hK, hG⟩, -⟩ := hF
  by_cases hp : (ω, w) ∈ tsupport (fun p : Ω W q × (Fin W → ℂ) => χh p.1 p.2)
  · have hpG := (hG _ hp hw).1
    have h1 : ContDiffAt ℝ 2 (fun p : Ω W q × (Fin W → ℂ) => Kh p.1 p.2) (ω, w) :=
      hK.contDiffAt (hGo.mem_nhds hpG)
    have hopen : IsOpen {p : Ω W q × (Fin W → ℂ) | p.2 ≠ 0} :=
      isOpen_ne_fun continuous_snd continuous_const
    have h2 : ContDiffAt ℝ 2 (fun p : Ω W q × (Fin W → ℂ) => χh p.1 p.2) (ω, w) :=
      hχ.contDiffAt (hopen.mem_nhds hw)
    exact (h2.smul h1).differentiableAt (by norm_num)
  · rw [notMem_tsupport_iff_eventuallyEq] at hp
    have h0 : (fun p : Ω W q × (Fin W → ℂ) => χh p.1 p.2 • Kh p.1 p.2) =ᶠ[nhds (ω, w)]
        fun _ => 0 := by
      filter_upwards [hp] with p hp'
      have : χh p.1 p.2 = 0 := hp'
      simp [this]
    exact (differentiableAt_const _).congr_of_eventuallyEq h0

/-- The cut field `ω ↦ χ̂ K̂(ω, v)` is continuous. -/
private lemma Score_cut_continuous {W q : ℕ} {g E : ℝ} {P R : Matrix (Fin W) (Fin W) ℂ}
    {v : Fin W → ℂ} {Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ}
    {χh : Ω W q → (Fin W → ℂ) → ℝ} (hF : GenFamily W q g E P R Kh χh) (hv : v ≠ 0) :
    Continuous fun η : Ω W q => χh η v • Kh η v := by
  refine continuous_iff_continuousAt.2 fun η => ?_
  have h2 : DifferentiableAt ℝ (fun η : Ω W q => ((η, v) : Ω W q × (Fin W → ℂ))) η :=
    differentiableAt_id.prodMk (differentiableAt_const v)
  exact ((Score_diff hF η hv).comp η h2).continuousAt

/-- The guarded part of the field is the conjugation of the blocks `4, …, q - 2` by the cut field
`χ̂ K̂`: `V_5 ↦ [χ̂ K̂, V_5 - g² R]`, `V_i ↦ [χ̂ K̂, V_i]`. -/
private lemma Score_Yact_eq {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ} {v : Fin W → ℂ}
    {Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ} {χh : Ω W q → (Fin W → ℂ) → ℝ}
    (η : Ω W q) :
    Score_Yact W q g E R v Kh χh η =
      hermCoord W q fun i => if 4 ≤ (i : ℕ) ∧ (i : ℕ) + 1 < q then
        (χh η v • Kh η v) * (gueBlock W q η i - (if (i : ℕ) = 4 then ((g : ℂ) ^ 2) • R else 0)) -
          (gueBlock W q η i - (if (i : ℕ) = 4 then ((g : ℂ) ^ 2) • R else 0)) *
            (χh η v • Kh η v) else 0 := by
  unfold Score_Yact
  rw [← (hermCoord_isLinearMap W q).map_smul]
  congr 1
  funext i
  by_cases h : (i : ℕ) + 1 < q
  · by_cases h4 : (i : ℕ) < 4
    · have : ¬ 4 ≤ (i : ℕ) := by omega
      simp [smallField, h, h4, this]
    · have h4' : 4 ≤ (i : ℕ) := by omega
      by_cases h5 : (i : ℕ) = 4
      · simp [smallField, h5, smul_sub]
      · simp [smallField, h, h4, h5, h4', smul_sub]
  · simp [h]

/-- Every coordinate of the guarded part of the field is continuous. -/
private lemma Score_Yact_continuous {W q : ℕ} {g E : ℝ} {P R : Matrix (Fin W) (Fin W) ℂ}
    {v : Fin W → ℂ} {Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ}
    {χh : Ω W q → (Fin W → ℂ) → ℝ} (hF : GenFamily W q g E P R Kh χh) (hv : v ≠ 0)
    (p : Fin q × Fin W × Fin W) :
    Continuous fun η : Ω W q => Score_Yact W q g E R v Kh χh η p := by
  have hFc := Score_cut_continuous hF hv
  have hV : ∀ i, Continuous fun η : Ω W q => gueBlock W q η i :=
    fun i => (Score_gueBlockL W q i).continuous
  simp only [Score_Yact_eq, hermCoord]
  by_cases hg : 4 ≤ (p.1 : ℕ) ∧ (p.1 : ℕ) + 1 < q
  · simp only [hg, and_self, ite_true]
    refine continuous_const.mul (Complex.continuous_re.comp (Continuous.matrix_trace
      (continuous_const.matrix_mul ?_)))
    exact (hFc.matrix_mul ((hV p.1).sub continuous_const)).sub
      (((hV p.1).sub continuous_const).matrix_mul hFc)
  · simp only [hg, ite_false]
    exact continuous_const

/-- The Gaussian divergence of a field with continuous components is measurable. -/
private lemma Score_measurable_gaussDiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Y : (ι → ℝ) → ι → ℝ} (hY : ∀ i, Continuous fun y => Y y i) : Measurable (gaussDiv Y) := by
  unfold gaussDiv
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((measurable_pi_apply i).mul (hY i).measurable).sub (measurable_lineDeriv (hY i))

/-- Lemma 9.4 [us:lem:score], (9.31) [us:eq:score], at a fixed preparation `(R_4, v_4) = (R, v)`. -/
theorem score_bound (CK : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (W q : ℕ) (g E M₀ : ℝ) (R P : Matrix (Fin W) (Fin W) ℂ)
      (v : Fin W → ℂ) (Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ)
      (χh : Ω W q → (Fin W → ℂ) → ℝ), ScoreData W q g E M₀ CK R P v Kh χh →
      ∫⁻ ω, ‖gaussDiv (fun η => χh η v • hermCoord W q (smallField W g E q R v (Kh η v) η)) ω‖ₑ
          ^ 2 ∂(μ W q) ≤
        ENNReal.ofReal C * ∫⁻ ω, ENNReal.ofReal
            (srcEnergy P v (fun w => χh ω w • Kh ω w)) ∂(μ W q) +
          ENNReal.ofReal (C * W * (1 + M₀ ^ 2)) *
            ∫⁻ ω, ENNReal.ofReal (hsSq (χh ω v • Kh ω v)) ∂(μ W q) +
          ENNReal.ofReal ((W : ℝ) * g ^ 4) *
            ∫⁻ ω, ENNReal.ofReal (hsSq
              ((χh ω v : ℂ) • smallCorr W g E q R v (Kh ω v) ω * chartR W g E q R ω (q - 1) -
                chartR W g E q R ω (q - 1) * (χh ω v : ℂ) • smallCorr W g E q R v (Kh ω v) ω))
              ∂(μ W q) +
          ENNReal.ofReal (C * W * M₀ * Real.exp (-c * W)) := by
  obtain ⟨C, c, hC, hc, hact⟩ := active_div_sq_le CK
  refine ⟨C, c, hC, hc, fun W q g E M₀ R P v Kh χh hD => ?_⟩
  have hbase := hact W q g E M₀ R P v Kh χh hD
  have hD0 := hD
  obtain ⟨hW, hq, -, -, -, -, hv, -, -, -, hF, -, -⟩ := hD
  set a : Fin q := ⟨q - 1, by omega⟩ with ha_def
  have ha : (a : ℕ) + 1 = q := by simp [ha_def]; omega
  set Aδ : Ω W q → ℝ := fun ω => gaussDiv (Score_Yact W q g E R v Kh χh) ω with hAδ
  set hh : Ω W q → Fin W × Fin W → ℝ := fun ω k =>
    Real.sqrt W * (hermBasis W k * Score_Hm W q g E R v Kh χh ω).trace.re with hhh
  -- the divergence is `δ_act + g² Σ_k ω_{(a,k)} h_k`
  have hpt : ∀ ω, gaussDiv (fun η => χh η v • hermCoord W q (smallField W g E q R v (Kh η v) η))
      ω = Aδ ω + g ^ 2 * ∑ k, hh ω k * ω (a, k) := by
    intro ω
    have e1 : (fun η => χh η v • hermCoord W q (smallField W g E q R v (Kh η v) η)) =
        fun η => Score_Yact W q g E R v Kh χh η + Score_Ylast W q g E R v Kh χh η :=
      funext (Score_field_split W q g E R v Kh χh)
    have hs := Score_gaussDiv_add_split (Y₁ := Score_Yact W q g E R v Kh χh)
      (Y₂ := Score_Ylast W q g E R v Kh χh) ω (fun p => by
        by_cases hp : p.1 = a
        · exact Or.inl fun y => Score_Yact_apply_of_eq ha y hp
        · exact Or.inr fun y => Score_Ylast_apply_of_ne ha y hp)
    rw [e1, hs, Score_gaussDiv_last hD0 ha ω]
    have hco := Score_trace_coord (q := q) hW ω a (Score_Hm W q g E R v Kh χh ω)
    have : (W : ℝ) * g ^ 2 * (gueBlock W q ω a * Score_Hm W q g E R v Kh χh ω).trace.re =
        g ^ 2 * ((W : ℝ) * (gueBlock W q ω a * Score_Hm W q g E R v Kh χh ω).trace.re) := by ring
    rw [this, hco]
  -- `δ_act` and `h` do not depend on the last block
  have hag : ∀ ω ω' : Ω W q, (∀ x : Fin q × Fin W × Fin W, x.1 ≠ a → ω x = ω' x) →
      Aδ ω = Aδ ω' ∧ hh ω = hh ω' := by
    intro ω ω' hag
    refine ⟨Score_gaussDiv_Yact_congr hD0 ha hag, ?_⟩
    obtain ⟨-, hχ', hR', hL'⟩ := Score_frozen hF ha hag
    have hHm : Score_Hm W q g E R v Kh χh ω = Score_Hm W q g E R v Kh χh ω' := by
      unfold Score_Hm
      rw [hχ', hL', hR']
    funext k
    simp only [hhh, hHm]
  have hAm : Measurable Aδ :=
    Score_measurable_gaussDiv (fun p => Score_Yact_continuous hF hv p)
  have hsplit := Score_split_bound W q a (g ^ 2) Aδ hh hAm hag
  have hsum : ∀ ω, ∑ k, hh ω k ^ 2 = (W : ℝ) * hsSq
      ((χh ω v : ℂ) • smallCorr W g E q R v (Kh ω v) ω * chartR W g E q R ω (q - 1) -
        chartR W g E q R ω (q - 1) * (χh ω v : ℂ) • smallCorr W g E q R v (Kh ω v) ω) :=
    fun ω => Score_sum_sq a (Score_Hm_isHermitian hD0 ω)
  have h3 : ENNReal.ofReal ((g ^ 2) ^ 2) * ∫⁻ ω, ENNReal.ofReal (∑ k, hh ω k ^ 2) ∂(μ W q) =
      ENNReal.ofReal ((W : ℝ) * g ^ 4) * ∫⁻ ω, ENNReal.ofReal (hsSq
        ((χh ω v : ℂ) • smallCorr W g E q R v (Kh ω v) ω * chartR W g E q R ω (q - 1) -
          chartR W g E q R ω (q - 1) * (χh ω v : ℂ) • smallCorr W g E q R v (Kh ω v) ω))
        ∂(μ W q) := by
    have e : ∀ ω, ENNReal.ofReal (∑ k, hh ω k ^ 2) = ENNReal.ofReal (W : ℝ) *
        ENNReal.ofReal (hsSq
          ((χh ω v : ℂ) • smallCorr W g E q R v (Kh ω v) ω * chartR W g E q R ω (q - 1) -
            chartR W g E q R ω (q - 1) * (χh ω v : ℂ) • smallCorr W g E q R v (Kh ω v) ω)) :=
      fun ω => by rw [hsum ω, ENNReal.ofReal_mul (Nat.cast_nonneg W)]
    simp only [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 2
    ring
  have hlhs : ∫⁻ ω, ‖gaussDiv (fun η => χh η v • hermCoord W q
      (smallField W g E q R v (Kh η v) η)) ω‖ₑ ^ 2 ∂(μ W q) =
      ∫⁻ ω, ‖Aδ ω + g ^ 2 * ∑ k, hh ω k * ω (a, k)‖ₑ ^ 2 ∂(μ W q) :=
    lintegral_congr fun ω => by rw [hpt ω]
  rw [hlhs]
  refine hsplit.trans ?_
  rw [h3]
  have hbase' : ∫⁻ ω, ‖Aδ ω‖ₑ ^ 2 ∂(μ W q) ≤
      ENNReal.ofReal C * ∫⁻ ω, ENNReal.ofReal
            (srcEnergy P v (fun w => χh ω w • Kh ω w)) ∂(μ W q) +
          ENNReal.ofReal (C * W * (1 + M₀ ^ 2)) *
            ∫⁻ ω, ENNReal.ofReal (hsSq (χh ω v • Kh ω v)) ∂(μ W q) +
          ENNReal.ofReal (C * W * M₀ * Real.exp (-c * W)) := hbase
  refine (add_le_add hbase' le_rfl).trans (le_of_eq ?_)
  ring



end LSBA
