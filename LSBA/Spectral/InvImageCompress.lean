import LSBA.Spectral.CompressSpectrum
import LSBA.Gauss.BlockCompress

/-!
# Compression of inverse images of a fresh GUE matrix

Let `V` be the `W × W` GUE matrix, `B` a deterministic Hermitian matrix and `P_𝒬` the orthogonal
projection onto a deterministic space `𝒬` of dimension `d`, `W^δ ≤ d ≤ ε₀ W`, such that the
complementary block `(1 - P_𝒬) B (1 - P_𝒬)` has norm at most `ε₀`; the block `P_𝒬 B P_𝒬` and the
cross blocks are arbitrary. Then (9.50) [us:eq:absolute] holds in operator form: every `x` with
`(V - E - B) x ∈ 𝒬` has `‖P_𝒬 x‖ ≤ C √(d/W) ‖x‖`, with failure `W^{-D} + C e^{-c d}`. The
proof writes `x = x_𝒬 + x_c`, so that `x_c = -Γ_c⁻¹ Y x_𝒬` for the complementary block `Γ_c` and
the cross block `Y`; on the near-zero spectral space of `Γ_c` given by (9.48)
[us:eq:complement-spectrum], the Gaussian part of `Y` with its deterministic mean removed has
least singular value `≥ c √(d/W)`.

Corollary 9.7 [nc:lem:compression], (9.52) [nc:eq:compression], follows by choosing `𝒬` to
contain `U`, `v` and `ran B_bad`: for `B = B_small + B_bad` with `‖B_small‖ ≤ ε₀` and
`rank B_bad + dim U + 1 ≤ d`, `|v* x|² ≤ C (d/W) ‖v‖² ‖x‖²` for every `x` with
`(V - E - B) x ∈ U`. No norm bound on B_bad is used.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Vectors and matrices -/

/-- Two matrices with the same action on every vector are equal. -/
private lemma invImageCompress_ext {m n : ℕ} {A B : Matrix (Fin m) (Fin n) ℂ}
    (h : ∀ u, A *ᵥ u = B *ᵥ u) : A = B :=
  Matrix.toLin'.injective
    (LinearMap.ext fun u => by rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h])

private lemma invImageCompress_l2Norm_nonneg {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    0 ≤ l2Norm v :=
  Real.sqrt_nonneg _

private lemma invImageCompress_l2Norm_smul {ι : Type*} [Fintype ι] (c : ℂ) (v : ι → ℂ) :
    l2Norm (c • v) = ‖c‖ * l2Norm v := by
  rw [l2Norm_eq_norm_toLp, l2Norm_eq_norm_toLp, WithLp.toLp_smul, norm_smul]

private lemma invImageCompress_l2Norm_neg {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    l2Norm (-v) = l2Norm v := by
  rw [l2Norm_eq_norm_toLp, l2Norm_eq_norm_toLp, WithLp.toLp_neg, norm_neg]

/-- Cauchy–Schwarz: `|v* y| ≤ ‖v‖₂ ‖y‖₂`. -/
private lemma invImageCompress_dot_le {ι : Type*} [Fintype ι] (v y : ι → ℂ) :
    ‖star v ⬝ᵥ y‖ ≤ l2Norm v * l2Norm y := by
  rw [l2Norm_eq_norm_toLp, l2Norm_eq_norm_toLp, dotProduct_comm,
    ← EuclideanSpace.inner_toLp_toLp]
  exact norm_inner_le_norm _ _

/-- The `ℓ²` operator norm of `X` is at most `1` if `‖X* X‖ ≤ 1` or `‖X* X‖ ≤ ‖X‖`. -/
private lemma invImageCompress_norm_le_one {m n : ℕ} {X : Matrix (Fin m) (Fin n) ℂ}
    (h : ‖Xᴴ * X‖ ≤ 1 ∨ ‖Xᴴ * X‖ ≤ ‖X‖) : ‖X‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at h
  have := norm_nonneg X
  rcases h with h | h <;> nlinarith

private lemma invImageCompress_norm_one (k : ℕ) : ‖(1 : Matrix (Fin k) (Fin k) ℂ)‖ ≤ 1 :=
  invImageCompress_norm_le_one (Or.inr (by rw [Matrix.conjTranspose_one, Matrix.one_mul]))

/-- A matrix with orthonormal columns has norm at most `1`. -/
private lemma invImageCompress_norm_isometry {m n : ℕ} {X : Matrix (Fin m) (Fin n) ℂ}
    (h : Xᴴ * X = 1) : ‖X‖ ≤ 1 :=
  invImageCompress_norm_le_one (Or.inl (by rw [h]; exact invImageCompress_norm_one n))

/-- An orthogonal projection has norm at most `1`. -/
private lemma invImageCompress_norm_proj {n : ℕ} {X : Matrix (Fin n) (Fin n) ℂ}
    (hH : X.IsHermitian) (hI : X * X = X) : ‖X‖ ≤ 1 :=
  invImageCompress_norm_le_one (Or.inr (by rw [hH.eq, hI]))

/-! ### Orthonormal frames -/

/-- An orthonormal frame of a subspace `K ⊆ ℂⁿ`: the rows of `N` are orthonormal, the columns of
`N*` lie in `K`, and `N* N` fixes `K`. -/
private lemma invImageCompress_frame {n h : ℕ} (K : Submodule ℂ (Fin n → ℂ))
    (hK : Module.finrank ℂ K = h) :
    ∃ N : Matrix (Fin h) (Fin n) ℂ, N * Nᴴ = 1 ∧ (∀ u, Nᴴ *ᵥ u ∈ K) ∧
      ∀ w ∈ K, Nᴴ *ᵥ (N *ᵥ w) = w := by
  subst hK
  let e : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] (Fin n → ℂ) := WithLp.linearEquiv 2 ℂ (Fin n → ℂ)
  let K' : Submodule ℂ (EuclideanSpace ℂ (Fin n)) := K.map e.symm.toLinearMap
  have hK' : Module.finrank ℂ K' = Module.finrank ℂ K := LinearEquiv.finrank_map_eq e.symm K
  let b : OrthonormalBasis (Fin (Module.finrank ℂ K)) ℂ K' :=
    (stdOrthonormalBasis ℂ K').reindex (finCongr hK')
  let f : Fin (Module.finrank ℂ K) → Fin n → ℂ := fun i => e (b i : EuclideanSpace ℂ (Fin n))
  have hf : ∀ i, f i ∈ K := by
    intro i
    obtain ⟨y, hy, hy'⟩ := Submodule.mem_map.1 (b i).2
    have : f i = y := by
      change e (b i : EuclideanSpace ℂ (Fin n)) = y
      rw [← hy']
      exact e.apply_symm_apply y
    rw [this]
    exact hy
  have hinner : ∀ i (w : EuclideanSpace ℂ (Fin n)),
      inner ℂ (b i : EuclideanSpace ℂ (Fin n)) w = ∑ j, star (f i j) * e w j := by
    intro i w
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    rfl
  have hNc : ∀ c : Fin (Module.finrank ℂ K) → ℂ,
      (Matrix.of fun i j => star (f i j))ᴴ *ᵥ c = ∑ i, c i • f i := by
    intro c
    ext j
    simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Finset.sum_apply, mul_comm]
  refine ⟨Matrix.of fun i j => star (f i j), ?_, ?_, ?_⟩
  · ext i i'
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h := (orthonormal_iff_ite.1 b.orthonormal) i i'
    rw [Submodule.coe_inner, hinner] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Matrix.conjTranspose_apply, f]
  · intro u
    rw [hNc]
    exact Submodule.sum_mem _ fun i _ => K.smul_mem _ (hf i)
  · intro w hw
    let w' : K' := ⟨e.symm w, Submodule.mem_map_of_mem hw⟩
    have hw' : e (w' : EuclideanSpace ℂ (Fin n)) = w := e.apply_symm_apply w
    have h := congrArg (fun z : K' => e (z : EuclideanSpace ℂ (Fin n))) (b.sum_repr' w')
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, hw'] at h
    have hNw : (Matrix.of fun i j => star (f i j)) *ᵥ w = fun i => inner ℂ (b i) w' := by
      ext i
      rw [Submodule.coe_inner, hinner, hw']
      rfl
    rw [hNw, hNc]
    exact h

/-- An orthogonal projection `P` is `N* N` for `N` with orthonormal rows, `rank P` of them;
`tr P = rank P`. -/
private lemma invImageCompress_projFrame_rank {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ}
    (hH : P.IsHermitian) (hI : P * P = P) :
    P.trace = P.rank ∧ ∃ N : Matrix (Fin P.rank) (Fin n) ℂ, N * Nᴴ = 1 ∧ Nᴴ * N = P := by
  obtain ⟨N, hN1, hN2, hN3⟩ := invImageCompress_frame (LinearMap.range P.mulVecLin) rfl
  have hfix : ∀ w ∈ LinearMap.range P.mulVecLin, P *ᵥ w = w := by
    rintro w ⟨z, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hI]
  have hPN : P * Nᴴ = Nᴴ := invImageCompress_ext fun u => by
    rw [← Matrix.mulVec_mulVec]
    exact hfix _ (hN2 u)
  have hNP : N * P = N := by
    have := congrArg Matrix.conjTranspose hPN
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH.eq] at this
  have h1 : Nᴴ * N * P = P := invImageCompress_ext fun u => by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hN3 _ (LinearMap.mem_range_self _ u)
  have hNN : Nᴴ * N = P :=
    calc Nᴴ * N = Nᴴ * (N * P) := by rw [hNP]
      _ = P := by rw [← Matrix.mul_assoc, h1]
  refine ⟨?_, N, hN1, hNN⟩
  calc P.trace = (Nᴴ * N).trace := by rw [hNN]
    _ = (N * Nᴴ).trace := Matrix.trace_mul_comm _ _
    _ = _ := by rw [hN1, Matrix.trace_one, Fintype.card_fin]; rfl

/-- An orthogonal projection of trace `d` is `N* N` for `N` with `d` orthonormal rows. -/
private lemma invImageCompress_projFrame {n d : ℕ} {P : Matrix (Fin n) (Fin n) ℂ}
    (hH : P.IsHermitian) (hI : P * P = P) (htr : P.trace = d) :
    ∃ N : Matrix (Fin d) (Fin n) ℂ, N * Nᴴ = 1 ∧ Nᴴ * N = P := by
  obtain ⟨hr, N, hN1, hN2⟩ := invImageCompress_projFrame_rank hH hI
  have : P.rank = d := by
    rw [htr] at hr
    exact_mod_cast hr.symm
  subst this
  exact ⟨N, hN1, hN2⟩

/-- Every subspace of `ℂⁿ` of dimension `f` lies in a subspace of dimension `f + k ≤ n`. -/
private lemma invImageCompress_extend {n : ℕ} (K₀ : Submodule ℂ (Fin n → ℂ)) (k : ℕ) :
    Module.finrank ℂ K₀ + k ≤ n →
      ∃ K : Submodule ℂ (Fin n → ℂ), K₀ ≤ K ∧ Module.finrank ℂ K = Module.finrank ℂ K₀ + k := by
  induction k with
  | zero => exact fun _ => ⟨K₀, le_rfl, rfl⟩
  | succ k ih =>
    intro hk
    obtain ⟨K₁, hle, hK₁⟩ := ih (by omega)
    have hne : K₁ ≠ ⊤ := by
      intro htop
      have := congrArg (fun K : Submodule ℂ (Fin n → ℂ) => Module.finrank ℂ K) htop
      simp only [finrank_top, Module.finrank_fin_fun] at this
      omega
    obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hne)
    refine ⟨K₁ ⊔ Submodule.span ℂ {v}, hle.trans le_sup_left, ?_⟩
    rw [Submodule.finrank_sup_span_singleton hv, hK₁]
    ring

/-! ### The complementary block -/

/-- The scalar matrix `E 1` is Hermitian for real `E`. -/
private lemma invImageCompress_isHermitian_shift {n : ℕ} (E : ℝ) :
    ((E : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  simp [Complex.conj_ofReal]

/-- The GUE matrix is measurable in the sample. -/
private lemma invImageCompress_measurable_gueMat (n : ℕ) :
    Measurable fun ω : Ω n 1 => gueMat n ω := by
  refine Matrix.measurable_iff.2 fun a b => ?_
  unfold gueMat gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

/-- The count clause of (9.43) [us:eq:spectrum] for `M⁻¹` gives at least as many eigenvalues of
`M` in `[-η, η]`; a singular `M` has `M⁻¹ = 0` and count `0`. -/
private lemma invImageCompress_count {k : ℕ} {M : Matrix (Fin k) (Fin k) ℂ} (hM : M.IsHermitian)
    {η r : ℝ} (hη : 0 < η) (hr : 0 < r) (h : r ≤ countIn M⁻¹ {x | η⁻¹ ≤ |x|}) :
    r ≤ (specProj M (Set.Icc (-η) η)).trace.re := by
  rw [(specProj_spec hM _).2.2.2, Complex.natCast_re]
  by_cases hu : IsUnit M
  · rw [countIn_inv hM hu] at h
    refine h.trans ?_
    have hmono : countIn M {x | x⁻¹ ∈ {x : ℝ | η⁻¹ ≤ |x|}} ≤ countIn M (Set.Icc (-η) η) := by
      simp only [countIn, hM, ↓reduceDIte]
      refine Finset.card_le_card fun j hj => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hj ⊢
      rw [abs_inv] at hj
      have hx : hM.eigenvalues j ≠ 0 := by
        intro h0
        rw [h0, abs_zero, inv_zero] at hj
        exact absurd hj (not_le.2 (inv_pos.2 hη))
      have habs : |hM.eigenvalues j| ≤ η :=
        (inv_le_inv₀ hη (abs_pos.2 hx)).1 hj
      exact ⟨by linarith [neg_abs_le (hM.eigenvalues j)], (le_abs_self _).trans habs⟩
    exact_mod_cast hmono
  · exfalso
    rw [Matrix.nonsing_inv_apply_not_isUnit M
      (fun h' => hu ((Matrix.isUnit_iff_isUnit_det M).2 h'))] at h
    have h0 : countIn (0 : Matrix (Fin k) (Fin k) ℂ) {x | η⁻¹ ≤ |x|} = 0 := by
      have hz : (0 : Matrix (Fin k) (Fin k) ℂ).IsHermitian := Matrix.isHermitian_zero
      simp only [countIn, hz, ↓reduceDIte]
      have hev := (Matrix.IsHermitian.eigenvalues_eq_zero_iff hz).2 rfl
      refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun j _ => ?_)
      rw [hev]
      simp only [Pi.zero_apply, Set.mem_ofPred_eq, abs_zero, not_le]
      exact inv_pos.2 hη
    rw [h0] at h
    norm_num at h
    linarith

/-- The complementary row of `Γ x ∈ ran P_𝒬` in an adapted frame: with `a = Φ* x`, `b = Ψ* x`,
`(Ψ* Γ Ψ) b + (Ψ* Γ Φ) a = 0`. -/
private lemma invImageCompress_row {W d m : ℕ} {Pq : Matrix (Fin W) (Fin W) ℂ}
    {Φ : Matrix (Fin W) (Fin d) ℂ} {Ψ : Matrix (Fin W) (Fin m) ℂ} (hΨ : Ψᴴ * Ψ = 1)
    (hΦΦ : Φ * Φᴴ = Pq) (hΨΨ : Ψ * Ψᴴ = 1 - Pq) (Γ : Matrix (Fin W) (Fin W) ℂ) (x : Fin W → ℂ)
    (hx : (1 - Pq) *ᵥ (Γ *ᵥ x) = 0) :
    (Ψᴴ * Γ * Ψ) *ᵥ (Ψᴴ *ᵥ x) + (Ψᴴ * Γ * Φ) *ᵥ (Φᴴ *ᵥ x) = 0 := by
  have h1 : Ψᴴ *ᵥ (Γ *ᵥ x) = 0 := by
    have : Ψᴴ = Ψᴴ * (1 - Pq) := by rw [← hΨΨ, ← Matrix.mul_assoc, hΨ, Matrix.one_mul]
    rw [this, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec]
  have : Ψᴴ * Γ * Ψ * Ψᴴ + Ψᴴ * Γ * Φ * Φᴴ = Ψᴴ * Γ := by
    rw [Matrix.mul_assoc _ Ψ, Matrix.mul_assoc _ Φ, hΦΦ, hΨΨ, ← Matrix.mul_add, sub_add_cancel,
      Matrix.mul_one]
  rw [this, ← Matrix.mulVec_mulVec, h1]

/-! ### The Gaussian fibre -/

/-- The fibre bound for a fixed complementary block (proof of (9.50) [us:eq:absolute]): if the
orthogonal projection `P` has rank `≥ (C₀ + 1) d`, then
`‖P (s⁻¹ G - Y) a‖ ≥ θ ‖a‖` for all `a ∈ ℂ^d`, for a standard complex Gaussian `G` and
`s θ ≤ c √(C₀ d)`, except with probability `e^{-c C₀ d}`; the frame `N` of
`ran P ∩ ker Y*` removes the mean `Y`. -/
private lemma invImageCompress_fiber {C₀ c : ℝ} (hc : 0 < c)
    (hsm : ∀ (h n k : ℕ) (N : Matrix (Fin h) (Fin n) ℂ) (lam : ℝ), 0 ≤ lam →
      (∀ u, lam * l2Norm u ≤ l2Norm (Nᴴ *ᵥ u)) → C₀ * k ≤ h →
      stdCGauss (Fin n × Fin k)
          {x | ∃ b, l2Norm (N *ᵥ (cgMat x *ᵥ b)) < c * lam * Real.sqrt h * l2Norm b} ≤
        ENNReal.ofReal (Real.exp (-(c * h))))
    {m d : ℕ} {P : Matrix (Fin m) (Fin m) ℂ} (hH : P.IsHermitian) (hI : P * P = P)
    (hrank : C₀ * d + d ≤ P.rank) (Y : Matrix (Fin m) (Fin d) ℂ) {s θ : ℝ} (hs : 0 < s)
    (hθ : s * θ ≤ c * Real.sqrt (C₀ * d)) :
    stdCGauss (Fin m × Fin d)
        {x | ∃ a, l2Norm ((P * (((s⁻¹ : ℝ) : ℂ) • cgMat x - Y)) *ᵥ a) < θ * l2Norm a} ≤
      ENNReal.ofReal (Real.exp (-(c * (C₀ * d)))) := by
  -- the dimension of `ran P ∩ ker Y*`
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range P.mulVecLin)
    (LinearMap.ker Yᴴ.mulVecLin)
  have h2 := Submodule.finrank_le (LinearMap.range P.mulVecLin ⊔ LinearMap.ker Yᴴ.mulVecLin)
  have h3 := LinearMap.finrank_range_add_finrank_ker Yᴴ.mulVecLin
  have h4 := Submodule.finrank_le (LinearMap.range Yᴴ.mulVecLin)
  rw [Module.finrank_fin_fun] at h2 h3 h4
  have hdim' : P.rank ≤ Module.finrank ℂ
      ↥(LinearMap.range P.mulVecLin ⊓ LinearMap.ker Yᴴ.mulVecLin) + d := by
    unfold Matrix.rank
    omega
  obtain ⟨h, hhdef⟩ : ∃ h, Module.finrank ℂ
      ↥(LinearMap.range P.mulVecLin ⊓ LinearMap.ker Yᴴ.mulVecLin) = h := ⟨_, rfl⟩
  rw [hhdef] at hdim'
  obtain ⟨N, hN1, hN2, -⟩ :=
    invImageCompress_frame (LinearMap.range P.mulVecLin ⊓ LinearMap.ker Yᴴ.mulVecLin) hhdef
  have hdim : (P.rank : ℝ) ≤ h + d := by exact_mod_cast hdim'
  have hh : C₀ * d ≤ h := by linarith
  -- `N P = N` and `N Y = 0`
  have hPN : P * Nᴴ = Nᴴ := invImageCompress_ext fun u => by
    obtain ⟨z, hz⟩ := (Submodule.mem_inf.1 (hN2 u)).1
    rw [← Matrix.mulVec_mulVec, ← hz, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hI]
  have hYN : Yᴴ * Nᴴ = 0 := invImageCompress_ext fun u => by
    have := (Submodule.mem_inf.1 (hN2 u)).2
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at this
    rw [← Matrix.mulVec_mulVec, this, Matrix.zero_mulVec]
  have hNP : N * P = N := by
    have := congrArg Matrix.conjTranspose hPN
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH.eq] at this
  have hNY : N * Y = 0 := by
    have := congrArg Matrix.conjTranspose hYN
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] at this
  have hNn : ‖N‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose]
    exact invImageCompress_norm_isometry (by rw [Matrix.conjTranspose_conjTranspose, hN1])
  have hlam : ∀ u, 1 * l2Norm u ≤ l2Norm (Nᴴ *ᵥ u) := by
    intro u
    have hu : u = N *ᵥ (Nᴴ *ᵥ u) := by rw [Matrix.mulVec_mulVec, hN1, Matrix.one_mulVec]
    calc 1 * l2Norm u = l2Norm (N *ᵥ (Nᴴ *ᵥ u)) := by rw [one_mul, ← hu]
      _ ≤ ‖N‖ * l2Norm (Nᴴ *ᵥ u) := l2Norm_mulVec_le _ _
      _ ≤ 1 * l2Norm (Nᴴ *ᵥ u) :=
          mul_le_mul_of_nonneg_right hNn (invImageCompress_l2Norm_nonneg _)
      _ = l2Norm (Nᴴ *ᵥ u) := one_mul _
  have hb := hsm h m d N 1 zero_le_one hlam hh
  refine le_trans (measure_mono ?_) (hb.trans (ENNReal.ofReal_le_ofReal ?_))
  · rintro x ⟨a, ha⟩
    refine ⟨a, ?_⟩
    set Z : Matrix (Fin m) (Fin d) ℂ := P * (((s⁻¹ : ℝ) : ℂ) • cgMat x - Y) with hZ
    have hNZ : N * Z = ((s⁻¹ : ℝ) : ℂ) • (N * cgMat x) := by
      rw [hZ, ← Matrix.mul_assoc, hNP, Matrix.mul_sub, hNY, sub_zero, Matrix.mul_smul]
    have hkey : N *ᵥ (cgMat x *ᵥ a) = ((s : ℝ) : ℂ) • ((N * Z) *ᵥ a) := by
      rw [hNZ, Matrix.smul_mulVec, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hs.ne',
        Complex.ofReal_one, one_smul, Matrix.mulVec_mulVec]
    have hsqh : Real.sqrt (C₀ * d) ≤ Real.sqrt h := Real.sqrt_le_sqrt hh
    have hna := invImageCompress_l2Norm_nonneg a
    calc l2Norm (N *ᵥ (cgMat x *ᵥ a)) = s * l2Norm (N *ᵥ (Z *ᵥ a)) := by
          rw [hkey, invImageCompress_l2Norm_smul, Complex.norm_real, Real.norm_of_nonneg hs.le,
            Matrix.mulVec_mulVec]
      _ ≤ s * (‖N‖ * l2Norm (Z *ᵥ a)) :=
          mul_le_mul_of_nonneg_left (l2Norm_mulVec_le _ _) hs.le
      _ ≤ s * (1 * l2Norm (Z *ᵥ a)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hNn (invImageCompress_l2Norm_nonneg _)) hs.le
      _ < s * (θ * l2Norm a) := by rw [one_mul]; exact mul_lt_mul_of_pos_left ha hs
      _ = (s * θ) * l2Norm a := by ring
      _ ≤ (c * Real.sqrt (C₀ * d)) * l2Norm a := mul_le_mul_of_nonneg_right hθ hna
      _ ≤ c * 1 * Real.sqrt h * l2Norm a := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqh hc.le) hna
  · exact Real.exp_le_exp.2 (by nlinarith)

/-- The event of the fibre bound is Borel in the pair (cross block, complementary block). -/
private lemma invImageCompress_measurableSet {m d : ℕ}
    (F : Matrix (Fin m) (Fin m) ℂ → Matrix (Fin m) (Fin m) ℂ) (hF : Measurable F)
    (Y : Matrix (Fin m) (Fin d) ℂ) (r θ : ℝ) :
    MeasurableSet {p : Matrix (Fin m) (Fin d) ℂ × Matrix (Fin m) (Fin m) ℂ |
      r ≤ (F p.2).trace.re ∧ ∃ a, l2Norm ((F p.2 * (p.1 - Y)) *ᵥ a) < θ * l2Norm a} := by
  have hsc1 : SecondCountableTopology (Matrix (Fin m) (Fin d) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin d → ℂ))
  have hsc2 : SecondCountableTopology (Matrix (Fin m) (Fin m) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin m → ℂ))
  have hl2 : ∀ k : ℕ, Continuous fun v : Fin k → ℂ => l2Norm v := by
    intro k
    unfold l2Norm
    fun_prop
  refine MeasurableSet.inter (s₁ := {p : Matrix (Fin m) (Fin d) ℂ × Matrix (Fin m) (Fin m) ℂ |
      r ≤ (F p.2).trace.re})
    (s₂ := {p : Matrix (Fin m) (Fin d) ℂ × Matrix (Fin m) (Fin m) ℂ |
      ∃ a, l2Norm ((F p.2 * (p.1 - Y)) *ᵥ a) < θ * l2Norm a}) ?_ ?_
  · exact measurableSet_le measurable_const
      (Complex.measurable_re.comp ((continuous_id.matrix_trace).measurable.comp
        (hF.comp measurable_snd)))
  · have hO : IsOpen {Z : Matrix (Fin m) (Fin d) ℂ | ∃ a, l2Norm (Z *ᵥ a) < θ * l2Norm a} := by
      have : {Z : Matrix (Fin m) (Fin d) ℂ | ∃ a, l2Norm (Z *ᵥ a) < θ * l2Norm a} =
          ⋃ a, {Z | l2Norm (Z *ᵥ a) < θ * l2Norm a} := by
        ext Z
        simp
      rw [this]
      exact isOpen_iUnion fun a =>
        isOpen_lt ((hl2 m).comp (continuous_id.matrix_mulVec continuous_const)) continuous_const
    have hg : Measurable fun p : Matrix (Fin m) (Fin d) ℂ × Matrix (Fin m) (Fin m) ℂ =>
        F p.2 * (p.1 - Y) :=
      (continuous_fst.matrix_mul continuous_snd).measurable.comp
        ((hF.comp measurable_snd).prodMk (measurable_fst.sub_const Y))
    exact hO.measurableSet.preimage hg

/-- The inverse-image compression (9.50) [us:eq:absolute] in operator form: for a projection
`P_𝒬` of rank `d` with `W^δ ≤ d ≤ ε₀ W` and `‖(1 - P_𝒬) B (1 - P_𝒬)‖ ≤ ε₀`, every `x` with
`(V - E - B) x ∈ ran P_𝒬` has `‖P_𝒬 x‖ ≤ C √(d/W) ‖x‖`, with failure `W^{-D} + C e^{-c d}`. -/
theorem invImage_compress_le (κ₀ δ : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hδ : 0 < δ) :
    ∃ ε₀ C c : ℝ, 0 < ε₀ ∧ 0 < C ∧ 0 < c ∧ ∀ D : ℝ, 0 < D → ∃ W₀ : ℕ, ∀ W d : ℕ, W₀ ≤ W →
      (W : ℝ) ^ δ ≤ d → (d : ℝ) ≤ ε₀ * W →
      ∀ (Pq B : Matrix (Fin W) (Fin W) ℂ) (E : ℝ), Pq.IsHermitian → Pq * Pq = Pq →
        Pq.trace = d → B.IsHermitian → ‖(1 - Pq) * B * (1 - Pq)‖ ≤ ε₀ → |E| ≤ 2 - κ₀ →
        μ W 1 {ω | ∃ x, (1 - Pq) *ᵥ ((gueMat W ω - (E : ℂ) • 1 - B) *ᵥ x) = 0 ∧
            C * Real.sqrt (d / W) * l2Norm x < l2Norm (Pq *ᵥ x)} ≤
          ENNReal.ofReal ((W : ℝ) ^ (-D) + C * Real.exp (-(c * d))) := by
  obtain ⟨C₀r, cr, hC₀r, hcr, hsm⟩ := cgMat_sminor
  obtain ⟨ε₀, A, Cs, C₁s, hε₀, hA, -, -, hcs⟩ :=
    compress_specInput κ₀ hκ₀ hκ₀' (C₀r + 1) (by linarith)
  set C : ℝ := max 1 (A / (cr * Real.sqrt C₀r)) with hCdef
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC0 : 0 < C := by linarith
  have hsC₀ : 0 < Real.sqrt C₀r := Real.sqrt_pos.2 hC₀r
  have hCA : A ≤ C * (cr * Real.sqrt C₀r) := by
    have h := le_max_right 1 (A / (cr * Real.sqrt C₀r))
    rw [div_le_iff₀ (by positivity)] at h
    rw [← hCdef] at h
    exact h
  refine ⟨ε₀, C, cr * C₀r, hε₀, hC0, by positivity, fun D hD => ?_⟩
  obtain ⟨W₁, hW₁⟩ := hcs δ D hδ hD
  refine ⟨max W₁ 1, fun W d hW hdW hdε Pq B E hPH hPI hPtr hBH hBn hE => ?_⟩
  have hW1 : W₁ ≤ W := (le_max_left _ _).trans hW
  have hWpos : (0 : ℝ) < W := by
    have : 1 ≤ W := (le_max_right _ _).trans hW
    exact_mod_cast this
  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos δ) hdW
  -- the frames `Φ` of `𝒬` and `Ψ` of its complement
  obtain ⟨N₁, hN₁1, hN₁2⟩ := invImageCompress_projFrame hPH hPI hPtr
  have hQH : (1 - Pq).IsHermitian := Matrix.isHermitian_one.sub hPH
  have hQI : (1 - Pq) * (1 - Pq) = 1 - Pq := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hPI, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, sub_self, sub_zero]
  have htrQ := (invImageCompress_projFrame_rank hQH hQI).1
  obtain ⟨m, hm⟩ : ∃ m, (1 - Pq).rank = m := ⟨_, rfl⟩
  rw [hm] at htrQ
  obtain ⟨N₂, hN₂1, hN₂2⟩ := invImageCompress_projFrame hQH hQI htrQ
  have hdm : d + m = W := by
    have h1 : (1 - Pq).trace = (W : ℂ) - d := by
      rw [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, hPtr]
    rw [htrQ] at h1
    have : ((d + m : ℕ) : ℂ) = W := by push_cast; rw [h1]; ring
    exact_mod_cast this
  have hΦ : N₁ᴴᴴ * N₁ᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose, hN₁1]
  have hΨ : N₂ᴴᴴ * N₂ᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose, hN₂1]
  have hΦΦ : N₁ᴴ * N₁ᴴᴴ = Pq := by rw [Matrix.conjTranspose_conjTranspose, hN₁2]
  have hΨΨ : N₂ᴴ * N₂ᴴᴴ = 1 - Pq := by rw [Matrix.conjTranspose_conjTranspose, hN₂2]
  set Φ : Matrix (Fin W) (Fin d) ℂ := N₁ᴴ with hΦdef
  set Ψ : Matrix (Fin W) (Fin m) ℂ := N₂ᴴ with hΨdef
  have hΦΨ : Φᴴ * Ψ = 0 :=
    calc Φᴴ * Ψ = Φᴴ * (Φ * Φᴴ) * ((Ψ * Ψᴴ) * Ψ) := by
          rw [← Matrix.mul_assoc Φᴴ Φ, hΦ, Matrix.one_mul, Matrix.mul_assoc Ψ, hΨ, Matrix.mul_one]
      _ = Φᴴ * (Pq * (1 - Pq)) * Ψ := by rw [hΦΦ, hΨΨ]; simp only [Matrix.mul_assoc]
      _ = 0 := by
          rw [Matrix.mul_sub, Matrix.mul_one, hPI, sub_self, Matrix.mul_zero, Matrix.zero_mul]
  have hΨΦ : Ψᴴ * Φ = 0 := by
    rw [← Matrix.conjTranspose_conjTranspose Φ, ← Matrix.conjTranspose_mul, hΦΨ,
      Matrix.conjTranspose_zero]
  have hΦn : ‖Φ‖ ≤ 1 := invImageCompress_norm_isometry hΦ
  have hΨn : ‖Ψᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact invImageCompress_norm_isometry hΨ
  -- the complementary block `Bc = Ψ* B Ψ` and the cross mean `Y = Ψ* B Φ`
  set Bc : Matrix (Fin m) (Fin m) ℂ := Ψᴴ * B * Ψ with hBcdef
  set Y : Matrix (Fin m) (Fin d) ℂ := Ψᴴ * B * Φ with hYdef
  have hBcH : Bc.IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul Ψ hBH
  have hBc : ‖Bc‖ ≤ ε₀ := by
    have h1 : Bc = Ψᴴ * ((1 - Pq) * B * (1 - Pq)) * Ψ := by
      have hl : Ψᴴ * (1 - Pq) = Ψᴴ := by rw [← hΨΨ, ← Matrix.mul_assoc, hΨ, Matrix.one_mul]
      have hr : (1 - Pq) * Ψ = Ψ := by rw [← hΨΨ, Matrix.mul_assoc, hΨ, Matrix.mul_one]
      have h2 : Ψᴴ * ((1 - Pq) * B * (1 - Pq)) * Ψ = (Ψᴴ * (1 - Pq)) * B * ((1 - Pq) * Ψ) := by
        simp only [Matrix.mul_assoc]
      rw [h2, hl, hr]
    rw [h1]
    calc ‖Ψᴴ * ((1 - Pq) * B * (1 - Pq)) * Ψ‖
        ≤ ‖Ψᴴ‖ * ‖(1 - Pq) * B * (1 - Pq)‖ * ‖Ψ‖ :=
          (Matrix.l2_opNorm_mul _ _).trans
            (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      _ ≤ 1 * ε₀ * 1 := by
          gcongr
          rw [← Matrix.l2_opNorm_conjTranspose]
          exact hΨn
      _ = ε₀ := by ring
  -- the scale `η = A d / W`, the spectral window and the threshold `θ`
  set η : ℝ := A * d / W with hηdef
  have hη : 0 < η := by positivity
  set F : Matrix (Fin m) (Fin m) ℂ → Matrix (Fin m) (Fin m) ℂ :=
    fun K => specProj (K - (E : ℂ) • 1 - Bc) (Set.Icc (-η) η) with hFdef
  have hF : Measurable F :=
    (measurable_specProj isClosed_Icc).comp
      ((continuous_id.sub continuous_const).sub continuous_const).measurable
  set θ : ℝ := A * Real.sqrt d / (C * Real.sqrt W) with hθdef
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.2 hWpos
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 hdpos
  have hθ : 0 < θ := by positivity
  have hθη : θ * C * Real.sqrt (d / W) = η := by
    rw [hθdef, hηdef, Real.sqrt_div' _ hWpos.le]
    field_simp
    rw [Real.sq_sqrt hdpos.le, Real.sq_sqrt hWpos.le]
    ring
  have hθs : Real.sqrt W * θ ≤ cr * Real.sqrt (C₀r * d) := by
    rw [hθdef, Real.sqrt_mul hC₀r.le]
    have : Real.sqrt W * (A * Real.sqrt d / (C * Real.sqrt W)) = A / C * Real.sqrt d := by
      field_simp
    rw [this]
    have hAC : A / C ≤ cr * Real.sqrt C₀r := by
      rw [div_le_iff₀ hC0]
      linarith
    nlinarith
  -- the two failure events
  set S₁ : Set (Ω W 1) := {ω | ¬ InvSpecInput (C₀r + 1) Cs C₁s W d (A * d / W)
      (Ψᴴ * gueMat W ω * Ψ - (E : ℂ) • 1 - Bc)⁻¹} with hS₁def
  have hS₁ : μ W 1 S₁ ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) :=
    hW₁ W m d hW1 (by omega) hdW hdε Ψ Bc E hΨ hBcH hBc hE
  set T : Set (Matrix (Fin m) (Fin d) ℂ × Matrix (Fin m) (Fin m) ℂ) :=
    {p | (C₀r + 1) * d ≤ (F p.2).trace.re ∧
      ∃ a, l2Norm ((F p.2 * (p.1 - Y)) *ᵥ a) < θ * l2Norm a} with hTdef
  have hT : MeasurableSet T := invImageCompress_measurableSet F hF Y _ θ
  set t : Ω W 1 → Matrix (Fin d) (Fin d) ℂ × Matrix (Fin m) (Fin d) ℂ ×
      Matrix (Fin m) (Fin m) ℂ :=
    fun ω => (Φᴴ * gueMat W ω * Φ, Ψᴴ * gueMat W ω * Φ, Ψᴴ * gueMat W ω * Ψ) with htdef
  have ht : Measurable t := by
    have hgm := invImageCompress_measurable_gueMat W
    refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_) <;>
      exact ((continuous_const.matrix_mul continuous_id).matrix_mul
        continuous_const).measurable.comp hgm
  -- the deterministic step: off `S₁`, the event lies in `t⁻¹ (univ × T)`
  have hsub : {ω | ∃ x, (1 - Pq) *ᵥ ((gueMat W ω - (E : ℂ) • 1 - B) *ᵥ x) = 0 ∧
      C * Real.sqrt (d / W) * l2Norm x < l2Norm (Pq *ᵥ x)} ⊆
      S₁ ∪ t ⁻¹' (Set.univ ×ˢ T) := by
    rintro ω ⟨x, hx1, hx2⟩
    by_cases hω : ω ∈ S₁
    · exact Or.inl hω
    right
    have hω' : InvSpecInput (C₀r + 1) Cs C₁s W d (A * d / W)
        (Ψᴴ * gueMat W ω * Ψ - (E : ℂ) • 1 - Bc)⁻¹ := not_not.1 hω
    set M : Matrix (Fin m) (Fin m) ℂ := Ψᴴ * gueMat W ω * Ψ - (E : ℂ) • 1 - Bc with hMdef
    have hM : M.IsHermitian :=
      ((Matrix.isHermitian_conjTranspose_mul_mul Ψ (gueBlock_isHermitian W 1 ω 0)).sub
        (invImageCompress_isHermitian_shift E)).sub hBcH
    refine ⟨trivial, ?_, ?_⟩
    · exact invImageCompress_count hM hη (by positivity) hω'.1
    · set a : Fin d → ℂ := Φᴴ *ᵥ x with hadef
      set b : Fin m → ℂ := Ψᴴ *ᵥ x with hbdef
      have hrow := invImageCompress_row hΨ hΦΦ hΨΨ (gueMat W ω - (E : ℂ) • 1 - B) x hx1
      have hΓΨ : Ψᴴ * (gueMat W ω - (E : ℂ) • 1 - B) * Ψ = M := by
        rw [hMdef, hBcdef, Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul,
          Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hΨ]
      have hΓΦ : Ψᴴ * (gueMat W ω - (E : ℂ) • 1 - B) * Φ = Ψᴴ * gueMat W ω * Φ - Y := by
        rw [hYdef, Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul,
          Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hΨΦ, smul_zero, sub_zero]
      rw [hΓΨ, hΓΦ] at hrow
      have hP := specProj_spec hM (Set.Icc (-η) η)
      have hFM : F (Ψᴴ * gueMat W ω * Ψ) = specProj M (Set.Icc (-η) η) := rfl
      have hkey : (F (Ψᴴ * gueMat W ω * Ψ) * (Ψᴴ * gueMat W ω * Φ - Y)) *ᵥ a =
          -((M * specProj M (Set.Icc (-η) η)) *ᵥ b) := by
        have h1 : (Ψᴴ * gueMat W ω * Φ - Y) *ᵥ a = -(M *ᵥ b) := eq_neg_of_add_eq_zero_right hrow
        rw [hFM, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_neg, Matrix.mulVec_mulVec, ← hP.2.2.1]
      have hMP : ‖M * specProj M (Set.Icc (-η) η)‖ ≤ η :=
        (norm_mul_specProj_le hM hη.le subset_rfl 0 le_rfl).1
      have hb : l2Norm b ≤ l2Norm x :=
        (l2Norm_mulVec_le _ _).trans
          ((mul_le_mul_of_nonneg_right hΨn (invImageCompress_l2Norm_nonneg _)).trans
            (one_mul _).le)
      have ha : l2Norm (Pq *ᵥ x) ≤ l2Norm a := by
        rw [← hΦΦ, ← Matrix.mulVec_mulVec]
        exact (l2Norm_mulVec_le _ _).trans
          ((mul_le_mul_of_nonneg_right hΦn (invImageCompress_l2Norm_nonneg _)).trans
            (one_mul _).le)
      refine ⟨a, ?_⟩
      rw [hkey, invImageCompress_l2Norm_neg]
      calc l2Norm ((M * specProj M (Set.Icc (-η) η)) *ᵥ b)
          ≤ ‖M * specProj M (Set.Icc (-η) η)‖ * l2Norm b := l2Norm_mulVec_le _ _
        _ ≤ η * l2Norm x :=
            mul_le_mul hMP hb (invImageCompress_l2Norm_nonneg _) hη.le
        _ = θ * (C * Real.sqrt (d / W) * l2Norm x) := by rw [← hθη]; ring
        _ < θ * l2Norm (Pq *ᵥ x) := mul_lt_mul_of_pos_left hx2 hθ
        _ ≤ θ * l2Norm a := mul_le_mul_of_nonneg_left ha hθ.le
  -- the Gaussian step: the law of the blocks and the fibre bound
  have hS₂ : μ W 1 (t ⁻¹' (Set.univ ×ˢ T)) ≤
      ENNReal.ofReal (Real.exp (-(cr * (C₀r * d)))) := by
    have hlaw := map_blockCompress_gueMat W d m hdm Φ Ψ hΦ hΨ hΦΨ
    have hg₁ : Measurable fun ω : Ω d 1 => ((Real.sqrt ((d : ℝ) / W) : ℝ) : ℂ) • gueMat d ω :=
      (continuous_const_smul _).measurable.comp (invImageCompress_measurable_gueMat d)
    have hg₃ : Measurable fun ω : Ω m 1 => ((Real.sqrt ((m : ℝ) / W) : ℝ) : ℂ) • gueMat m ω :=
      (continuous_const_smul _).measurable.comp (invImageCompress_measurable_gueMat m)
    have hcg : Measurable fun x : Fin m × Fin d → ℂ => cgMat x :=
      Matrix.measurable_iff.2 fun i j => measurable_pi_apply (i, j)
    have hg₂ : Measurable fun x : Fin m × Fin d → ℂ =>
        (((Real.sqrt W)⁻¹ : ℝ) : ℂ) • cgMat x :=
      (continuous_const_smul _).measurable.comp hcg
    rw [← Measure.map_apply ht (MeasurableSet.univ.prod hT), htdef, hlaw, Measure.prod_prod,
      Measure.map_apply hg₁ MeasurableSet.univ, Set.preimage_univ, measure_univ, one_mul,
      Measure.prod_apply_symm hT]
    calc ∫⁻ K, ((stdCGauss (Fin m × Fin d)).map fun x =>
            (((Real.sqrt W)⁻¹ : ℝ) : ℂ) • cgMat x) ((fun G => (G, K)) ⁻¹' T)
          ∂((μ m 1).map fun ω => ((Real.sqrt ((m : ℝ) / W) : ℝ) : ℂ) • gueMat m ω)
        ≤ ∫⁻ _K, ENNReal.ofReal (Real.exp (-(cr * (C₀r * d))))
          ∂((μ m 1).map fun ω => ((Real.sqrt ((m : ℝ) / W) : ℝ) : ℂ) • gueMat m ω) := by
          refine lintegral_mono fun K => ?_
          rw [Measure.map_apply hg₂ (measurable_prodMk_right hT)]
          by_cases hK : (C₀r + 1) * d ≤ (F K).trace.re
          · by_cases hMK : (K - (E : ℂ) • 1 - Bc).IsHermitian
            · have hP := specProj_spec hMK (Set.Icc (-η) η)
              have hrk : C₀r * d + d ≤ (F K).rank := by
                have h1 : ((F K).rank : ℝ) = (F K).trace.re := by
                  rw [hFdef]
                  dsimp only
                  rw [hP.2.2.2, rank_specProj hMK, Complex.natCast_re]
                rw [h1]
                linarith
              refine le_trans (measure_mono ?_)
                (invImageCompress_fiber hcr hsm hP.1 hP.2.1 hrk Y hsW hθs)
              rintro x ⟨-, a, ha⟩
              exact ⟨a, ha⟩
            · exfalso
              have h0 : F K = 0 := by
                rw [hFdef]
                dsimp only
                simp only [specProj, hMK, ↓reduceDIte]
              rw [h0, Matrix.trace_zero, Complex.zero_re] at hK
              have : 0 < (C₀r + 1) * d := by positivity
              linarith
          · refine le_trans (le_of_eq (measure_mono_null ?_ measure_empty)) zero_le
            intro x hx
            exact (hK hx.1).elim
      _ = ENNReal.ofReal (Real.exp (-(cr * (C₀r * d)))) := by
          rw [lintegral_const, Measure.map_apply hg₃ MeasurableSet.univ, Set.preimage_univ,
            measure_univ, mul_one]
  calc μ W 1 {ω | ∃ x, (1 - Pq) *ᵥ ((gueMat W ω - (E : ℂ) • 1 - B) *ᵥ x) = 0 ∧
        C * Real.sqrt (d / W) * l2Norm x < l2Norm (Pq *ᵥ x)}
      ≤ μ W 1 (S₁ ∪ t ⁻¹' (Set.univ ×ˢ T)) := measure_mono hsub
    _ ≤ μ W 1 S₁ + μ W 1 (t ⁻¹' (Set.univ ×ˢ T)) := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) + ENNReal.ofReal (Real.exp (-(cr * (C₀r * d)))) :=
        add_le_add hS₁ hS₂
    _ = ENNReal.ofReal ((W : ℝ) ^ (-D) + Real.exp (-(cr * (C₀r * d)))) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-D) + C * Real.exp (-(cr * C₀r * d))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [show cr * C₀r * (d : ℝ) = cr * (C₀r * d) by ring]
        nlinarith [Real.exp_pos (-(cr * (C₀r * d)))]

/-- Corollary 9.7 [nc:lem:compression], (9.52) [nc:eq:compression]: for `B = B_small + B_bad`
Hermitian with `‖B_small‖ ≤ ε₀`, an orthogonal projection `P_U` with
`rank B_bad + dim U + 1 ≤ d`, `W^δ ≤ d ≤ ε₀ W` and any `v`, every `x` with `(V - E - B) x ∈ U`
has `|v* x|² ≤ C (d/W) ‖v‖² ‖x‖²`, with failure `W^{-D} + C e^{-c d}`; the constants do not
depend on `‖B_bad‖` nor on the position of `U`, `v`, `ran B_bad`. -/
theorem invImage_overlap_le (κ₀ δ : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hδ : 0 < δ) :
    ∃ ε₀ C c : ℝ, 0 < ε₀ ∧ 0 < C ∧ 0 < c ∧ ∀ D : ℝ, 0 < D → ∃ W₀ : ℕ, ∀ W d : ℕ, W₀ ≤ W →
      (W : ℝ) ^ δ ≤ d → (d : ℝ) ≤ ε₀ * W →
      ∀ (B Bs Bb Pu : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ) (E : ℝ), B.IsHermitian →
        B = Bs + Bb → ‖Bs‖ ≤ ε₀ → Pu.IsHermitian → Pu * Pu = Pu →
        (Bb.rank : ℝ) + Pu.trace.re + 1 ≤ d → |E| ≤ 2 - κ₀ →
        μ W 1 {ω | ∃ x, (1 - Pu) *ᵥ ((gueMat W ω - (E : ℂ) • 1 - B) *ᵥ x) = 0 ∧
            C * (d / W) * l2Norm v ^ 2 * l2Norm x ^ 2 < ‖star v ⬝ᵥ x‖ ^ 2} ≤
          ENNReal.ofReal ((W : ℝ) ^ (-D) + C * Real.exp (-(c * d))) := by
  obtain ⟨ε₁, C₁, c, hε₁, hC₁, hc, h1⟩ := invImage_compress_le κ₀ δ hκ₀ hκ₀' hδ
  refine ⟨min ε₁ (1 / 2), C₁ ^ 2 + C₁, c, lt_min hε₁ (by norm_num), by positivity, hc,
    fun D hD => ?_⟩
  obtain ⟨W₀, hW₀⟩ := h1 D hD
  refine ⟨W₀, fun W d hW hdW hdε B Bs Bb Pu v E hBH hB hBs hPuH hPuI hrank hE => ?_⟩
  have hWr : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have hdε₁ : (d : ℝ) ≤ ε₁ * W := hdε.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hWr)
  have hdW' : d ≤ W := by
    have : (d : ℝ) ≤ W := by
      have := hdε.trans (mul_le_mul_of_nonneg_right (min_le_right ε₁ (1 / 2)) hWr)
      linarith
    exact_mod_cast this
  -- the space `𝒬 ⊇ U + ran B_bad + span v` of dimension `d`
  set K₀ : Submodule ℂ (Fin W → ℂ) := LinearMap.range Pu.mulVecLin ⊔
    LinearMap.range Bb.mulVecLin ⊔ Submodule.span ℂ {v} with hK₀def
  have hK₀ : Module.finrank ℂ K₀ ≤ d := by
    have h1 := Submodule.finrank_add_le_finrank_add_finrank
      (LinearMap.range Pu.mulVecLin ⊔ LinearMap.range Bb.mulVecLin) (Submodule.span ℂ {v})
    have h2 := Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range Pu.mulVecLin)
      (LinearMap.range Bb.mulVecLin)
    have h3 : Module.finrank ℂ (Submodule.span ℂ ({v} : Set (Fin W → ℂ))) ≤ 1 := by
      have := finrank_span_le_card (R := ℂ) ({v} : Set (Fin W → ℂ))
      simpa using this
    have h4 : (Pu.rank : ℝ) = Pu.trace.re := by
      rw [(invImageCompress_projFrame_rank hPuH hPuI).1, Complex.natCast_re]
    have h5 : Pu.rank + Bb.rank + 1 ≤ d := by
      have : ((Pu.rank + Bb.rank + 1 : ℕ) : ℝ) ≤ d := by push_cast; linarith
      exact_mod_cast this
    rw [← hK₀def] at h1
    unfold Matrix.rank at h5
    omega
  obtain ⟨K, hK₀K, hKd⟩ := invImageCompress_extend K₀ (d - Module.finrank ℂ K₀) (by omega)
  have hKd' : Module.finrank ℂ K = d := by omega
  obtain ⟨N, hN1, -, hN3⟩ := invImageCompress_frame K hKd'
  set Pq : Matrix (Fin W) (Fin W) ℂ := Nᴴ * N with hPqdef
  have hPqH : Pq.IsHermitian := by
    rw [hPqdef, Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hPqI : Pq * Pq = Pq := by
    rw [hPqdef, Matrix.mul_assoc, ← Matrix.mul_assoc N, hN1, Matrix.one_mul]
  have hPqtr : Pq.trace = d := by
    rw [hPqdef, Matrix.trace_mul_comm, hN1, Matrix.trace_one, Fintype.card_fin]
  have hfix : ∀ w ∈ K, Pq *ᵥ w = w := fun w hw => by
    rw [hPqdef, ← Matrix.mulVec_mulVec]
    exact hN3 w hw
  have hPu : (1 - Pq) * Pu = 0 := invImageCompress_ext fun u => by
    have hm : Pu *ᵥ u ∈ K := hK₀K (Submodule.mem_sup_left (Submodule.mem_sup_left
      (LinearMap.mem_range.2 ⟨u, Matrix.mulVecLin_apply Pu u⟩)))
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hfix _ hm,
      sub_self, Matrix.zero_mulVec]
  have hBb : (1 - Pq) * Bb = 0 := invImageCompress_ext fun u => by
    have hm : Bb *ᵥ u ∈ K := hK₀K (Submodule.mem_sup_left (Submodule.mem_sup_right
      (LinearMap.mem_range.2 ⟨u, Matrix.mulVecLin_apply Bb u⟩)))
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hfix _ hm,
      sub_self, Matrix.zero_mulVec]
  have hv : Pq *ᵥ v = v :=
    hfix v (hK₀K (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)))
  -- the hypotheses of (9.50) [us:eq:absolute] for `P_𝒬`
  have hQn : ‖1 - Pq‖ ≤ 1 :=
    invImageCompress_norm_proj (Matrix.isHermitian_one.sub hPqH) (by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hPqI, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul, sub_self, sub_zero])
  have hnorm : ‖(1 - Pq) * B * (1 - Pq)‖ ≤ ε₁ := by
    rw [hB, Matrix.mul_add, Matrix.add_mul, hBb, Matrix.zero_mul, add_zero]
    calc ‖(1 - Pq) * Bs * (1 - Pq)‖ ≤ ‖1 - Pq‖ * ‖Bs‖ * ‖1 - Pq‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * min ε₁ (1 / 2) * 1 := by gcongr
      _ ≤ ε₁ := by rw [mul_one, one_mul]; exact min_le_left _ _
  have hmain := hW₀ W d hW hdW hdε₁ Pq B E hPqH hPqI hPqtr hBH hnorm hE
  refine le_trans (measure_mono ?_) (hmain.trans (ENNReal.ofReal_le_ofReal ?_))
  · rintro ω ⟨x, hx1, hx2⟩
    refine ⟨x, ?_, ?_⟩
    · have hsplit : (gueMat W ω - (E : ℂ) • 1 - B) *ᵥ x =
          (1 - Pu) *ᵥ ((gueMat W ω - (E : ℂ) • 1 - B) *ᵥ x) +
            Pu *ᵥ ((gueMat W ω - (E : ℂ) • 1 - B) *ᵥ x) := by
        rw [← Matrix.add_mulVec, sub_add_cancel, Matrix.one_mulVec]
      rw [hsplit, Matrix.mulVec_add, hx1, Matrix.mulVec_zero, zero_add, Matrix.mulVec_mulVec, hPu,
        Matrix.zero_mulVec]
    · by_contra hle
      rw [not_lt] at hle
      have hdot : star v ⬝ᵥ (Pq *ᵥ x) = star v ⬝ᵥ x := by
        rw [Matrix.dotProduct_mulVec]
        congr 1
        have := Matrix.star_mulVec Pq v
        rw [hv, hPqH.eq] at this
        exact this.symm
      have hdW0 : (0 : ℝ) ≤ d / W := by positivity
      have hCS : ‖star v ⬝ᵥ x‖ ≤ l2Norm v * (C₁ * Real.sqrt (d / W) * l2Norm x) := by
        rw [← hdot]
        exact (invImageCompress_dot_le v _).trans
          (mul_le_mul_of_nonneg_left hle (invImageCompress_l2Norm_nonneg v))
      have hsq : ‖star v ⬝ᵥ x‖ ^ 2 ≤ C₁ ^ 2 * (d / W) * l2Norm v ^ 2 * l2Norm x ^ 2 := by
        calc ‖star v ⬝ᵥ x‖ ^ 2 ≤ (l2Norm v * (C₁ * Real.sqrt (d / W) * l2Norm x)) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hCS 2
          _ = C₁ ^ 2 * Real.sqrt (d / W) ^ 2 * l2Norm v ^ 2 * l2Norm x ^ 2 := by ring
          _ = C₁ ^ 2 * (d / W) * l2Norm v ^ 2 * l2Norm x ^ 2 := by rw [Real.sq_sqrt hdW0]
      have hq : 0 ≤ (d / W : ℝ) * l2Norm v ^ 2 * l2Norm x ^ 2 := by positivity
      have : C₁ ^ 2 * (d / W) * l2Norm v ^ 2 * l2Norm x ^ 2 ≤
          (C₁ ^ 2 + C₁) * (d / W) * l2Norm v ^ 2 * l2Norm x ^ 2 := by
        nlinarith [mul_nonneg hC₁.le hq]
      linarith
  · nlinarith [Real.exp_pos (-(c * d)), sq_nonneg C₁]


end LSBA
