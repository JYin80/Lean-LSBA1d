import LSBA.Spectral.InvImageCompress

/-!
# Compression of inverse images into a subspace of dimension at most `d`

The operator form of (9.50) [us:eq:absolute] for subspaces of dimension at most `d`: let `U` and
`ran Q₀` be deterministic subspaces with `dim U + rank Q₀ ≤ d`, `W^δ ≤ d ≤ min(ε₀ W, W)`, and let
`B` be Hermitian with `‖(1 - Q₀) B (1 - Q₀)‖ ≤ ε₀`. Every `x` with `(V - E - B) x ∈ U` has
`‖Q₀ x‖ ≤ C √(d/W) ‖x‖`, with failure `W^{-D} + C e^{-c d}`. It follows from the dimension-`d`
form by enlarging `U + ran Q₀` to a space `𝒬` of dimension exactly `d`: the complementary block of
`B` on `𝒬^⊥ ⊆ ker Q₀` is a compression of `(1 - Q₀) B (1 - Q₀)`. This is the bound
`‖(1 - P) Q‖² ≤ C d/W` of (9.60) [su:eq:geometry] with `ran (1 - P) ⊆ ran Q₀`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Vectors and matrices -/

/-- Two matrices with the same action on every vector are equal. -/
private lemma invImageCompressSub_ext {m n : ℕ} {A B : Matrix (Fin m) (Fin n) ℂ}
    (h : ∀ u, A *ᵥ u = B *ᵥ u) : A = B :=
  Matrix.toLin'.injective
    (LinearMap.ext fun u => by rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h])

/-- The `ℓ²` operator norm of `X` is at most `1` if `‖X* X‖ ≤ 1` or `‖X* X‖ ≤ ‖X‖`. -/
private lemma invImageCompressSub_norm_le_one {m n : ℕ} {X : Matrix (Fin m) (Fin n) ℂ}
    (h : ‖Xᴴ * X‖ ≤ 1 ∨ ‖Xᴴ * X‖ ≤ ‖X‖) : ‖X‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at h
  have := norm_nonneg X
  rcases h with h | h <;> nlinarith

/-- An orthogonal projection has norm at most `1`. -/
private lemma invImageCompressSub_norm_proj {n : ℕ} {X : Matrix (Fin n) (Fin n) ℂ}
    (hH : X.IsHermitian) (hI : X * X = X) : ‖X‖ ≤ 1 :=
  invImageCompressSub_norm_le_one (Or.inr (by rw [hH.eq, hI]))

/-! ### Orthonormal frames -/

/-- An orthonormal frame of a subspace `K ⊆ ℂⁿ`: the rows of `N` are orthonormal, the columns of
`N*` lie in `K`, and `N* N` fixes `K`. -/
private lemma invImageCompressSub_frame {n h : ℕ} (K : Submodule ℂ (Fin n → ℂ))
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
private lemma invImageCompressSub_projFrame_rank {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ}
    (hH : P.IsHermitian) (hI : P * P = P) :
    P.trace = P.rank ∧ ∃ N : Matrix (Fin P.rank) (Fin n) ℂ, N * Nᴴ = 1 ∧ Nᴴ * N = P := by
  obtain ⟨N, hN1, hN2, hN3⟩ := invImageCompressSub_frame (LinearMap.range P.mulVecLin) rfl
  have hfix : ∀ w ∈ LinearMap.range P.mulVecLin, P *ᵥ w = w := by
    rintro w ⟨z, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hI]
  have hPN : P * Nᴴ = Nᴴ := invImageCompressSub_ext fun u => by
    rw [← Matrix.mulVec_mulVec]
    exact hfix _ (hN2 u)
  have hNP : N * P = N := by
    have := congrArg Matrix.conjTranspose hPN
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH.eq] at this
  have h1 : Nᴴ * N * P = P := invImageCompressSub_ext fun u => by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hN3 _ (LinearMap.mem_range_self _ u)
  have hNN : Nᴴ * N = P :=
    calc Nᴴ * N = Nᴴ * (N * P) := by rw [hNP]
      _ = P := by rw [← Matrix.mul_assoc, h1]
  refine ⟨?_, N, hN1, hNN⟩
  calc P.trace = (Nᴴ * N).trace := by rw [hNN]
    _ = (N * Nᴴ).trace := Matrix.trace_mul_comm _ _
    _ = _ := by rw [hN1, Matrix.trace_one, Fintype.card_fin]; rfl

/-- Every subspace of `ℂⁿ` of dimension `f` lies in a subspace of dimension `f + k ≤ n`. -/
private lemma invImageCompressSub_extend {n : ℕ} (K₀ : Submodule ℂ (Fin n → ℂ)) (k : ℕ) :
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
/-- (9.50) [us:eq:absolute] for subspaces `U`, `ran Q₀` with `dim U + rank Q₀ ≤ d`: every `x`
with `(V - E - B) x ∈ U` has `‖Q₀ x‖ ≤ C √(d/W) ‖x‖`, when `‖(1 - Q₀) B (1 - Q₀)‖ ≤ ε₀`,
`W^δ ≤ d ≤ ε₀ W` and `d ≤ W`, with failure `W^{-D} + C e^{-c d}`. -/
theorem invImage_compress_sub_le (κ₀ δ : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hδ : 0 < δ) :
    ∃ ε₀ C c : ℝ, 0 < ε₀ ∧ 0 < C ∧ 0 < c ∧ ∀ D : ℝ, 0 < D → ∃ W₀ : ℕ, ∀ W d : ℕ, W₀ ≤ W →
      (W : ℝ) ^ δ ≤ d → (d : ℝ) ≤ ε₀ * W → d ≤ W →
      ∀ (Pu Q₀ B : Matrix (Fin W) (Fin W) ℂ) (E : ℝ), Pu.IsHermitian → Pu * Pu = Pu →
        Q₀.IsHermitian → Q₀ * Q₀ = Q₀ → Pu.trace.re + Q₀.trace.re ≤ d → B.IsHermitian →
        ‖(1 - Q₀) * B * (1 - Q₀)‖ ≤ ε₀ → |E| ≤ 2 - κ₀ →
        μ W 1 {ω | ∃ x, (1 - Pu) *ᵥ ((gueMat W ω - (E : ℂ) • 1 - B) *ᵥ x) = 0 ∧
            C * Real.sqrt (d / W) * l2Norm x < l2Norm (Q₀ *ᵥ x)} ≤
          ENNReal.ofReal ((W : ℝ) ^ (-D) + C * Real.exp (-(c * d))) := by
  obtain ⟨ε₀, C, c, hε₀, hC, hc, h1⟩ := invImage_compress_le κ₀ δ hκ₀ hκ₀' hδ
  refine ⟨ε₀, C, c, hε₀, hC, hc, fun D hD => ?_⟩
  obtain ⟨W₀, hW₀⟩ := h1 D hD
  refine ⟨W₀, fun W d hW hdW hdε hdW' Pu Q₀ B E hPuH hPuI hQH hQI htr hBH hBn hE => ?_⟩
  -- a space `𝒬 ⊇ U + ran Q₀` of dimension `d`
  set K₀ : Submodule ℂ (Fin W → ℂ) :=
    LinearMap.range Pu.mulVecLin ⊔ LinearMap.range Q₀.mulVecLin with hK₀def
  have hK₀ : Module.finrank ℂ K₀ ≤ d := by
    have h2 := Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range Pu.mulVecLin)
      (LinearMap.range Q₀.mulVecLin)
    have h4 : (Pu.rank : ℝ) = Pu.trace.re := by
      rw [(invImageCompressSub_projFrame_rank hPuH hPuI).1, Complex.natCast_re]
    have h4' : (Q₀.rank : ℝ) = Q₀.trace.re := by
      rw [(invImageCompressSub_projFrame_rank hQH hQI).1, Complex.natCast_re]
    have h5 : Pu.rank + Q₀.rank ≤ d := by
      have : ((Pu.rank + Q₀.rank : ℕ) : ℝ) ≤ d := by push_cast; linarith
      exact_mod_cast this
    rw [← hK₀def] at h2
    unfold Matrix.rank at h5
    omega
  obtain ⟨K, hK₀K, hKd⟩ := invImageCompressSub_extend K₀ (d - Module.finrank ℂ K₀) (by omega)
  have hKd' : Module.finrank ℂ K = d := by omega
  obtain ⟨N, hN1, -, hN3⟩ := invImageCompressSub_frame K hKd'
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
  -- `𝒬` contains `U` and `ran Q₀`
  have hPu : (1 - Pq) * Pu = 0 := invImageCompressSub_ext fun u => by
    have hm : Pu *ᵥ u ∈ K := hK₀K (Submodule.mem_sup_left
      (LinearMap.mem_range.2 ⟨u, Matrix.mulVecLin_apply Pu u⟩))
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hfix _ hm,
      sub_self, Matrix.zero_mulVec]
  have hQ0 : (1 - Pq) * Q₀ = 0 := invImageCompressSub_ext fun u => by
    have hm : Q₀ *ᵥ u ∈ K := hK₀K (Submodule.mem_sup_right
      (LinearMap.mem_range.2 ⟨u, Matrix.mulVecLin_apply Q₀ u⟩))
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hfix _ hm,
      sub_self, Matrix.zero_mulVec]
  have hQ0' : Q₀ * (1 - Pq) = 0 := by
    have := congrArg Matrix.conjTranspose hQ0
    rwa [Matrix.conjTranspose_mul, hQH.eq, (Matrix.isHermitian_one.sub hPqH).eq,
      Matrix.conjTranspose_zero] at this
  have hQP : Q₀ * Pq = Q₀ := by
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hQ0'
    exact hQ0'.symm
  -- the complementary block of `B` on `𝒬^⊥` is a compression of `(1 - Q₀) B (1 - Q₀)`
  have hQn : ‖1 - Pq‖ ≤ 1 :=
    invImageCompressSub_norm_proj (Matrix.isHermitian_one.sub hPqH) (by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hPqI, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul, sub_self, sub_zero])
  have hblk : (1 - Pq) * B * (1 - Pq) = (1 - Pq) * ((1 - Q₀) * B * (1 - Q₀)) * (1 - Pq) := by
    have e1 : (1 - Pq) * (1 - Q₀) = 1 - Pq := by
      rw [Matrix.mul_sub, Matrix.mul_one, hQ0, sub_zero]
    have e2 : (1 - Q₀) * (1 - Pq) = 1 - Pq := by
      rw [Matrix.sub_mul, Matrix.one_mul, hQ0', sub_zero]
    calc (1 - Pq) * B * (1 - Pq) = ((1 - Pq) * (1 - Q₀)) * B * ((1 - Q₀) * (1 - Pq)) := by
          rw [e1, e2]
      _ = (1 - Pq) * ((1 - Q₀) * B * (1 - Q₀)) * (1 - Pq) := by simp only [Matrix.mul_assoc]
  have hnorm : ‖(1 - Pq) * B * (1 - Pq)‖ ≤ ε₀ := by
    rw [hblk]
    calc ‖(1 - Pq) * ((1 - Q₀) * B * (1 - Q₀)) * (1 - Pq)‖
        ≤ ‖1 - Pq‖ * ‖(1 - Q₀) * B * (1 - Q₀)‖ * ‖1 - Pq‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * ε₀ * 1 := by gcongr
      _ = ε₀ := by ring
  have hmain := hW₀ W d hW hdW hdε Pq B E hPqH hPqI hPqtr hBH hnorm hE
  refine le_trans (measure_mono ?_) hmain
  rintro ω ⟨x, hx1, hx2⟩
  refine ⟨x, ?_, ?_⟩
  · have hsplit : (gueMat W ω - (E : ℂ) • 1 - B) *ᵥ x =
        (1 - Pu) *ᵥ ((gueMat W ω - (E : ℂ) • 1 - B) *ᵥ x) +
          Pu *ᵥ ((gueMat W ω - (E : ℂ) • 1 - B) *ᵥ x) := by
      rw [← Matrix.add_mulVec, sub_add_cancel, Matrix.one_mulVec]
    rw [hsplit, Matrix.mulVec_add, hx1, Matrix.mulVec_zero, zero_add, Matrix.mulVec_mulVec, hPu,
      Matrix.zero_mulVec]
  · calc C * Real.sqrt (d / W) * l2Norm x < l2Norm (Q₀ *ᵥ x) := hx2
      _ = l2Norm (Q₀ *ᵥ (Pq *ᵥ x)) := by rw [Matrix.mulVec_mulVec, hQP]
      _ ≤ ‖Q₀‖ * l2Norm (Pq *ᵥ x) := l2Norm_mulVec_le _ _
      _ ≤ 1 * l2Norm (Pq *ᵥ x) :=
          mul_le_mul_of_nonneg_right (invImageCompressSub_norm_proj hQH hQI) (Real.sqrt_nonneg _)
      _ = l2Norm (Pq *ᵥ x) := one_mul _

end LSBA
