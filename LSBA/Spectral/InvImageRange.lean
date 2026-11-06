import LSBA.Spectral.InvImageCompress
import LSBA.Gauss.NormTail

/-!
# Relative overlap of inverse images

Lemma 9.5 [us:lem:range]. Let `B_0` be Hermitian, `Q_0` an orthogonal projection commuting with
`B_0`, with `B_small = (1 - Q_0) B_0 (1 - Q_0)` of norm at most `ε₀` (so `B_bad = Q_0 B_0 Q_0` is
arbitrary), `B_1` Hermitian of norm at most `ε₀`, and `P_U` an orthogonal projection with the
transversality `‖Q_0 P_U‖ ≤ C_T √(d/W)`. If `W^δ ≤ d ≤ ε₀ W` and
`dim U + 2 rank Q_0 + 1 ≤ d`, then every `x` with `(V - E - B_0 - B_1) x ∈ U` satisfies
`|v* x|² ≤ C (d/W) (log W)² v*(1 + B_0²)⁻¹v ‖x‖²` (9.42) [us:eq:relative], with failure
`W^{-D} + C e^{-c d}`. The constants do not depend on `‖B_bad‖`.

The proof chooses `𝒬 ⊇ ran Q_0 + U + B_1 ran Q_0 + span (1 - Q_0) v` of dimension `d`. The
`Q_0`-columns of the cross block are centered and independent of the complementary block and of
the other columns; Lemma 9.6 [us:lem:self] with (9.48) [us:eq:complement-spectrum] gives (9.49)
[us:eq:Y0], (9.50) [us:eq:absolute] gives `‖x_𝒬‖ ≤ C √(d/W) ‖x‖`, the `Q_0`-row of the equation
gives (9.51) [us:eq:weightedcompression], and a weighted Cauchy–Schwarz inequality gives (9.42)
[us:eq:relative].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Vectors and matrices -/

/-- Two matrices with the same action on every vector are equal. -/
private lemma invImageRange_ext {m n : ℕ} {A B : Matrix (Fin m) (Fin n) ℂ}
    (h : ∀ u, A *ᵥ u = B *ᵥ u) : A = B :=
  Matrix.toLin'.injective
    (LinearMap.ext fun u => by rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h])

private lemma invImageRange_l2Norm_nonneg {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    0 ≤ l2Norm v :=
  Real.sqrt_nonneg _

/-- Cauchy–Schwarz: `|v* y| ≤ ‖v‖₂ ‖y‖₂`. -/
private lemma invImageRange_dot_le {ι : Type*} [Fintype ι] (v y : ι → ℂ) :
    ‖star v ⬝ᵥ y‖ ≤ l2Norm v * l2Norm y := by
  rw [l2Norm_eq_norm_toLp, l2Norm_eq_norm_toLp, dotProduct_comm,
    ← EuclideanSpace.inner_toLp_toLp]
  exact norm_inner_le_norm _ _

/-- The `ℓ²` operator norm of `X` is at most `1` if `‖X* X‖ ≤ 1` or `‖X* X‖ ≤ ‖X‖`. -/
private lemma invImageRange_norm_le_one {m n : ℕ} {X : Matrix (Fin m) (Fin n) ℂ}
    (h : ‖Xᴴ * X‖ ≤ 1 ∨ ‖Xᴴ * X‖ ≤ ‖X‖) : ‖X‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at h
  have := norm_nonneg X
  rcases h with h | h <;> nlinarith

private lemma invImageRange_norm_one (k : ℕ) : ‖(1 : Matrix (Fin k) (Fin k) ℂ)‖ ≤ 1 :=
  invImageRange_norm_le_one (Or.inr (by rw [Matrix.conjTranspose_one, Matrix.one_mul]))

/-- A matrix with orthonormal columns has norm at most `1`. -/
private lemma invImageRange_norm_isometry {m n : ℕ} {X : Matrix (Fin m) (Fin n) ℂ}
    (h : Xᴴ * X = 1) : ‖X‖ ≤ 1 :=
  invImageRange_norm_le_one (Or.inl (by rw [h]; exact invImageRange_norm_one n))

/-- An orthogonal projection has norm at most `1`. -/
private lemma invImageRange_norm_proj {n : ℕ} {X : Matrix (Fin n) (Fin n) ℂ}
    (hH : X.IsHermitian) (hI : X * X = X) : ‖X‖ ≤ 1 :=
  invImageRange_norm_le_one (Or.inr (by rw [hH.eq, hI]))

/-! ### Orthonormal frames -/

/-- An orthonormal frame of a subspace `K ⊆ ℂⁿ`: the rows of `N` are orthonormal, the columns of
`N*` lie in `K`, and `N* N` fixes `K`. -/
private lemma invImageRange_frame {n h : ℕ} (K : Submodule ℂ (Fin n → ℂ))
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
private lemma invImageRange_projFrame_rank {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ}
    (hH : P.IsHermitian) (hI : P * P = P) :
    P.trace = P.rank ∧ ∃ N : Matrix (Fin P.rank) (Fin n) ℂ, N * Nᴴ = 1 ∧ Nᴴ * N = P := by
  obtain ⟨N, hN1, hN2, hN3⟩ := invImageRange_frame (LinearMap.range P.mulVecLin) rfl
  have hfix : ∀ w ∈ LinearMap.range P.mulVecLin, P *ᵥ w = w := by
    rintro w ⟨z, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hI]
  have hPN : P * Nᴴ = Nᴴ := invImageRange_ext fun u => by
    rw [← Matrix.mulVec_mulVec]
    exact hfix _ (hN2 u)
  have hNP : N * P = N := by
    have := congrArg Matrix.conjTranspose hPN
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH.eq] at this
  have h1 : Nᴴ * N * P = P := invImageRange_ext fun u => by
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
private lemma invImageRange_projFrame {n d : ℕ} {P : Matrix (Fin n) (Fin n) ℂ}
    (hH : P.IsHermitian) (hI : P * P = P) (htr : P.trace = d) :
    ∃ N : Matrix (Fin d) (Fin n) ℂ, N * Nᴴ = 1 ∧ Nᴴ * N = P := by
  obtain ⟨hr, N, hN1, hN2⟩ := invImageRange_projFrame_rank hH hI
  have : P.rank = d := by
    rw [htr] at hr
    exact_mod_cast hr.symm
  subst this
  exact ⟨N, hN1, hN2⟩

/-- Every subspace of `ℂⁿ` of dimension `f` lies in a subspace of dimension `f + k ≤ n`. -/
private lemma invImageRange_extend {n : ℕ} (K₀ : Submodule ℂ (Fin n → ℂ)) (k : ℕ) :
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

/-! ### The GUE matrix and the complementary row -/

/-- The GUE matrix is measurable in the sample. -/
private lemma invImageRange_measurable_gueMat (n : ℕ) :
    Measurable fun ω : Ω n 1 => gueMat n ω := by
  refine Matrix.measurable_iff.2 fun a b => ?_
  unfold gueMat gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

/-- The complementary row of `Γ x ∈ ran P_𝒬` in an adapted frame: with `a = Φ* x`, `b = Ψ* x`,
`(Ψ* Γ Ψ) b + (Ψ* Γ Φ) a = 0`. -/
private lemma invImageRange_row {W d m : ℕ} {Pq : Matrix (Fin W) (Fin W) ℂ}
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

private lemma invImageRange_l2Norm_add {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    l2Norm (u + v) ≤ l2Norm u + l2Norm v := by
  rw [l2Norm_eq_norm_toLp, l2Norm_eq_norm_toLp, l2Norm_eq_norm_toLp, WithLp.toLp_add]
  exact norm_add_le _ _

private lemma invImageRange_l2Norm_sub {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    l2Norm (u - v) ≤ l2Norm u + l2Norm v := by
  rw [l2Norm_eq_norm_toLp, l2Norm_eq_norm_toLp, l2Norm_eq_norm_toLp, WithLp.toLp_sub]
  exact norm_sub_le _ _

private lemma invImageRange_eq_zero {ι : Type*} [Fintype ι] {v : ι → ℂ} (h : l2Norm v = 0) :
    v = 0 := by
  rw [l2Norm_eq_norm_toLp, norm_eq_zero] at h
  exact (WithLp.toLp_eq_zero 2).1 h

/-- `w* w = ‖w‖²`. -/
private lemma invImageRange_dot_self {ι : Type*} [Fintype ι] (w : ι → ℂ) :
    star w ⬝ᵥ w = ((l2Norm w ^ 2 : ℝ) : ℂ) := by
  rw [l2Norm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  push_cast
  simp only [dotProduct, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.star_def, Complex.conj_mul']

/-- For Hermitian `H`, `(H y)* z = y* (H z)`. -/
private lemma invImageRange_dot_herm {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    (y z : Fin n → ℂ) : star (H *ᵥ y) ⬝ᵥ z = star y ⬝ᵥ (H *ᵥ z) := by
  rw [Matrix.star_mulVec, hH.eq, Matrix.dotProduct_mulVec]

/-- The quadratic form of `1 + B²` for Hermitian `B`: `z* (1 + B²) z = ‖z‖² + ‖B z‖²`. -/
private lemma invImageRange_quad {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsHermitian)
    (z : Fin n → ℂ) :
    star z ⬝ᵥ ((1 + B * B) *ᵥ z) = ((l2Norm z ^ 2 + l2Norm (B *ᵥ z) ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, dotProduct_add,
    ← invImageRange_dot_herm hB, invImageRange_dot_self, invImageRange_dot_self]
  push_cast
  ring

/-- `1 + B²` is invertible for Hermitian `B`. -/
private lemma invImageRange_isUnit {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsHermitian) :
    IsUnit (1 + B * B).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro z w hzw
  have h : (1 + B * B) *ᵥ (z - w) = 0 := by rw [Matrix.mulVec_sub, hzw, sub_self]
  have hq := invImageRange_quad hB (z - w)
  rw [h, dotProduct_zero] at hq
  have h2 : l2Norm (z - w) ^ 2 + l2Norm (B *ᵥ (z - w)) ^ 2 = 0 := by exact_mod_cast hq.symm
  have h3 : l2Norm (z - w) = 0 := by
    nlinarith [sq_nonneg (l2Norm (z - w)), sq_nonneg (l2Norm (B *ᵥ (z - w)))]
  exact sub_eq_zero.1 (invImageRange_eq_zero h3)

/-- The weighted Cauchy–Schwarz inequality of the proof of Lemma 9.5 [us:lem:range]: for a
projection `Q` commuting with the Hermitian `B`, `‖(1 - Q) B (1 - Q)‖ ≤ ε ≤ 1`, and a Hermitian
`P` fixing `(1 - Q) v`, `|v* x|² ≤ v*(1 + B²)⁻¹v (‖Q x‖² + ‖B Q x‖² + 4 ‖P x‖²)`. -/
private lemma invImageRange_weighted {n : ℕ} {B Q P : Matrix (Fin n) (Fin n) ℂ} {ε : ℝ}
    (hB : B.IsHermitian) (hQ : Q.IsHermitian) (hQI : Q * Q = Q) (hQB : Q * B = B * Q)
    (hε : ε ≤ 1) (hBs : ‖(1 - Q) * B * (1 - Q)‖ ≤ ε) (hP : P.IsHermitian) (v x : Fin n → ℂ)
    (hPv : P *ᵥ ((1 - Q) *ᵥ v) = (1 - Q) *ᵥ v) :
    0 ≤ (star v ⬝ᵥ ((1 + B * B)⁻¹ *ᵥ v)).re ∧
      ‖star v ⬝ᵥ x‖ ^ 2 ≤ (star v ⬝ᵥ ((1 + B * B)⁻¹ *ᵥ v)).re *
        (l2Norm (Q *ᵥ x) ^ 2 + l2Norm (B *ᵥ (Q *ᵥ x)) ^ 2 + 4 * l2Norm (P *ᵥ x) ^ 2) := by
  set M : Matrix (Fin n) (Fin n) ℂ := 1 + B * B with hMdef
  have hMH : M.IsHermitian :=
    Matrix.isHermitian_one.add (by rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, hB.eq])
  have hMu : IsUnit M.det := invImageRange_isUnit hB
  have hMM : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hMu
  have hMM' : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hMu
  have hQM : Q * M = M * Q := by
    rw [hMdef, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      ← Matrix.mul_assoc, hQB, Matrix.mul_assoc, hQB, Matrix.mul_assoc]
  have hQMi : Q * M⁻¹ = M⁻¹ * Q :=
    calc Q * M⁻¹ = M⁻¹ * M * Q * M⁻¹ := by rw [hMM', Matrix.one_mul]
      _ = M⁻¹ * (Q * M) * M⁻¹ := by rw [hQM]; simp only [Matrix.mul_assoc]
      _ = M⁻¹ * Q := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hMM, Matrix.mul_one]
  set R : Matrix (Fin n) (Fin n) ℂ := 1 - Q with hRdef
  have hRH : R.IsHermitian := Matrix.isHermitian_one.sub hQ
  have hRI : R * R = R := by
    rw [hRdef, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hQI, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul, sub_self, sub_zero]
  have hRB : R * B = B * R := by
    rw [hRdef, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hQB]
  have hRM : R * M = M * R := by
    rw [hRdef, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hQM]
  -- `w = M⁻¹ v`, `z₁ = Q w`, `z₂ = (1 - Q) w`
  set w : Fin n → ℂ := M⁻¹ *ᵥ v with hwdef
  set z₁ : Fin n → ℂ := Q *ᵥ w with hz₁
  set z₂ : Fin n → ℂ := R *ᵥ w with hz₂
  have hw : M *ᵥ w = v := by rw [hwdef, Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec]
  have ha : M *ᵥ z₁ = Q *ᵥ v := by rw [hz₁, Matrix.mulVec_mulVec, ← hQM, ← Matrix.mulVec_mulVec, hw]
  have hb : M *ᵥ z₂ = R *ᵥ v := by rw [hz₂, Matrix.mulVec_mulVec, ← hRM, ← Matrix.mulVec_mulVec, hw]
  have hv : v = Q *ᵥ v + R *ᵥ v := by
    rw [← Matrix.add_mulVec, hRdef, add_sub_cancel, Matrix.one_mulVec]
  -- `v* M⁻¹ v = z₁* M z₁ + z₂* M z₂`
  have hidem : ∀ (S : Matrix (Fin n) (Fin n) ℂ), S.IsHermitian → S * S = S →
      ∀ y : Fin n → ℂ, star (S *ᵥ w) ⬝ᵥ (S *ᵥ y) = star w ⬝ᵥ (S *ᵥ y) := by
    intro S hS hSI y
    rw [invImageRange_dot_herm hS, Matrix.mulVec_mulVec, hSI]
  have hsum : star v ⬝ᵥ w = star z₁ ⬝ᵥ (M *ᵥ z₁) + star z₂ ⬝ᵥ (M *ᵥ z₂) := by
    rw [ha, hb, hz₁, hz₂, hidem Q hQ hQI, hidem R hRH hRI, ← dotProduct_add, ← hv]
    conv_lhs => rw [← hw]
    rw [invImageRange_dot_herm hMH, hw]
  set α : ℝ := l2Norm z₁ ^ 2 + l2Norm (B *ᵥ z₁) ^ 2 with hα
  set β : ℝ := l2Norm z₂ ^ 2 + l2Norm (B *ᵥ z₂) ^ 2 with hβ
  have hval : star v ⬝ᵥ w = ((α + β : ℝ) : ℂ) := by
    rw [hsum, invImageRange_quad hB, invImageRange_quad hB, hα, hβ]
    push_cast
    ring
  have hre : (star v ⬝ᵥ (M⁻¹ *ᵥ v)).re = α + β := by rw [← hwdef, hval, Complex.ofReal_re]
  rw [hre]
  have hα0 : 0 ≤ α := by positivity
  have hβ0 : 0 ≤ β := by positivity
  refine ⟨by linarith, ?_⟩
  -- the bound `‖(1 - Q) v‖ ≤ 2 ‖z₂‖`
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hBs
  have hBsBs : B * B * R = (R * B * R) * (R * B * R) := by
    have h1 : R * B * R = B * R := by rw [hRB, Matrix.mul_assoc, hRI]
    rw [h1, Matrix.mul_assoc B R, ← Matrix.mul_assoc R B, hRB, Matrix.mul_assoc B R R, hRI,
      Matrix.mul_assoc]
  have hz₂R : R *ᵥ z₂ = z₂ := by rw [hz₂, Matrix.mulVec_mulVec, hRI]
  have hBBz : B *ᵥ (B *ᵥ z₂) = ((R * B * R) * (R * B * R)) *ᵥ z₂ := by
    rw [← hBsBs, Matrix.mulVec_mulVec]
    conv_lhs => rw [← hz₂R]
    rw [Matrix.mulVec_mulVec]
  have hRv : l2Norm (R *ᵥ v) ≤ 2 * l2Norm z₂ := by
    have h1 : l2Norm (B *ᵥ (B *ᵥ z₂)) ≤ l2Norm z₂ := by
      rw [hBBz]
      calc l2Norm (((R * B * R) * (R * B * R)) *ᵥ z₂)
          ≤ ‖(R * B * R) * (R * B * R)‖ * l2Norm z₂ := l2Norm_mulVec_le _ _
        _ ≤ (ε * ε) * l2Norm z₂ := by
            refine mul_le_mul_of_nonneg_right ?_ (invImageRange_l2Norm_nonneg _)
            exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hBs hBs (norm_nonneg _) hε0)
        _ ≤ 1 * l2Norm z₂ := by
            refine mul_le_mul_of_nonneg_right ?_ (invImageRange_l2Norm_nonneg _)
            nlinarith
        _ = l2Norm z₂ := one_mul _
    rw [← hb, hMdef, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    linarith [invImageRange_l2Norm_add z₂ (B *ᵥ (B *ᵥ z₂))]
  -- `v* x = z₁* Q x + (B z₁)* (B Q x) + ((1 - Q) v)* (P x)`
  have hsplit : star v ⬝ᵥ x = star z₁ ⬝ᵥ (Q *ᵥ x) + star (B *ᵥ z₁) ⬝ᵥ (B *ᵥ (Q *ᵥ x)) +
      star (R *ᵥ v) ⬝ᵥ (P *ᵥ x) := by
    have h1 : star (Q *ᵥ v) ⬝ᵥ x = star z₁ ⬝ᵥ (Q *ᵥ x) +
        star (B *ᵥ z₁) ⬝ᵥ (B *ᵥ (Q *ᵥ x)) := by
      have : star (Q *ᵥ v) ⬝ᵥ x = star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ x) := by
        rw [invImageRange_dot_herm hQ, invImageRange_dot_herm hQ, Matrix.mulVec_mulVec, hQI]
      rw [this, ← ha, invImageRange_dot_herm hMH, hMdef, Matrix.add_mulVec, Matrix.one_mulVec,
        dotProduct_add, ← Matrix.mulVec_mulVec, ← invImageRange_dot_herm hB]
    have h2 : star (R *ᵥ v) ⬝ᵥ x = star (R *ᵥ v) ⬝ᵥ (P *ᵥ x) := by
      rw [← invImageRange_dot_herm hP, hRdef, hPv]
    conv_lhs => rw [hv]
    rw [star_add, add_dotProduct, h1, h2]
  -- Cauchy–Schwarz
  set p₁ := l2Norm z₁
  set p₂ := l2Norm (B *ᵥ z₁)
  set p₃ := l2Norm z₂
  set q₁ := l2Norm (Q *ᵥ x)
  set q₂ := l2Norm (B *ᵥ (Q *ᵥ x))
  set q₃ := l2Norm (P *ᵥ x)
  have hle : ‖star v ⬝ᵥ x‖ ≤ p₁ * q₁ + p₂ * q₂ + p₃ * (2 * q₃) := by
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans (add_le_add (invImageRange_dot_le _ _)
      (invImageRange_dot_le _ _))) ?_
    exact (invImageRange_dot_le _ _).trans ((mul_le_mul_of_nonneg_right hRv
      (invImageRange_l2Norm_nonneg _)).trans_eq (by ring))
  have hsq : ‖star v ⬝ᵥ x‖ ^ 2 ≤ (p₁ * q₁ + p₂ * q₂ + p₃ * (2 * q₃)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hCS : (p₁ * q₁ + p₂ * q₂ + p₃ * (2 * q₃)) ^ 2 ≤
      (p₁ ^ 2 + p₂ ^ 2 + p₃ ^ 2) * (q₁ ^ 2 + q₂ ^ 2 + 4 * q₃ ^ 2) := by
    nlinarith [sq_nonneg (p₁ * q₂ - p₂ * q₁), sq_nonneg (p₁ * (2 * q₃) - p₃ * q₁),
      sq_nonneg (p₂ * (2 * q₃) - p₃ * q₂)]
  have hpβ : p₁ ^ 2 + p₂ ^ 2 + p₃ ^ 2 ≤ α + β := by
    rw [hα, hβ]
    nlinarith [sq_nonneg (l2Norm (B *ᵥ z₂))]
  have hq0 : 0 ≤ q₁ ^ 2 + q₂ ^ 2 + 4 * q₃ ^ 2 := by positivity
  calc ‖star v ⬝ᵥ x‖ ^ 2 ≤ (p₁ ^ 2 + p₂ ^ 2 + p₃ ^ 2) * (q₁ ^ 2 + q₂ ^ 2 + 4 * q₃ ^ 2) :=
        hsq.trans hCS
    _ ≤ (α + β) * (q₁ ^ 2 + q₂ ^ 2 + 4 * q₃ ^ 2) := mul_le_mul_of_nonneg_right hpβ hq0

/-! ### The inverse of the complementary block -/

/-- The matrix inverse is measurable. -/
private lemma invImageRange_measurable_inv {k : ℕ} :
    Measurable fun A : Matrix (Fin k) (Fin k) ℂ => A⁻¹ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  have hd : Measurable fun A : Matrix (Fin k) (Fin k) ℂ => A.det :=
    (continuous_id.matrix_det).measurable
  have ha : Measurable fun A : Matrix (Fin k) (Fin k) ℂ => A.adjugate i j :=
    (continuous_id.matrix_adjugate).measurable.eval_matrix
  exact (hd.inv).mul ha

/-- If `M⁻¹` has a positive count `#{|r| ≥ η⁻¹}`, then `M` is invertible: a singular `M` has
`M⁻¹ = 0` and count `0`. -/
private lemma invImageRange_isUnit_of_count {k : ℕ} {M : Matrix (Fin k) (Fin k) ℂ} {η r : ℝ}
    (hη : 0 < η) (hr : 0 < r) (h : r ≤ countIn M⁻¹ {x | η⁻¹ ≤ |x|}) : IsUnit M.det := by
  by_contra hu
  rw [Matrix.nonsing_inv_apply_not_isUnit M hu] at h
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

/-- A matrix with a positive eigenvalue count is Hermitian. -/
private lemma invImageRange_isHermitian_of_count {k : ℕ} {R : Matrix (Fin k) (Fin k) ℂ}
    {S : Set ℝ} {r : ℝ} (hr : 0 < r) (h : r ≤ countIn R S) : R.IsHermitian := by
  by_contra hR
  simp only [countIn, hR, ↓reduceDIte, Nat.cast_zero] at h
  linarith

/-! ### The event of (9.49) [us:eq:Y0] -/

/-- The set of `(R, Y)` with `‖Y* y‖ > r ‖y‖` for some `y ∈ ran (R M) + ran (R Y)` is open. -/
private lemma invImageRange_isOpen {m d : ℕ} (Mc : Matrix (Fin m) (Fin d) ℂ) (r : ℝ) :
    IsOpen {q : Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin d) ℂ |
      ∃ y ∈ LinearMap.range (q.1 * Mc).mulVecLin ⊔ LinearMap.range (q.1 * q.2).mulVecLin,
        r * l2Norm y < l2Norm (q.2ᴴ *ᵥ y)} := by
  have hl2 : ∀ k : ℕ, Continuous fun v : Fin k → ℂ => l2Norm v := by
    intro k
    unfold l2Norm
    fun_prop
  have heq : {q : Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin d) ℂ |
      ∃ y ∈ LinearMap.range (q.1 * Mc).mulVecLin ⊔ LinearMap.range (q.1 * q.2).mulVecLin,
        r * l2Norm y < l2Norm (q.2ᴴ *ᵥ y)} =
      ⋃ a : (Fin d → ℂ) × (Fin d → ℂ), {q | r * l2Norm ((q.1 * Mc) *ᵥ a.1 + (q.1 * q.2) *ᵥ a.2) <
        l2Norm (q.2ᴴ *ᵥ ((q.1 * Mc) *ᵥ a.1 + (q.1 * q.2) *ᵥ a.2))} := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨y, hy, hlt⟩
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
      obtain ⟨a₁, rfl⟩ := LinearMap.mem_range.1 hy₁
      obtain ⟨a₂, rfl⟩ := LinearMap.mem_range.1 hy₂
      exact ⟨(a₁, a₂), hlt⟩
    · rintro ⟨a, hlt⟩
      exact ⟨_, Submodule.add_mem_sup (LinearMap.mem_range_self _ a.1)
        (LinearMap.mem_range_self _ a.2), hlt⟩
  rw [heq]
  refine isOpen_iUnion fun a => isOpen_lt ?_ ?_
  · exact continuous_const.mul ((hl2 m).comp
      (((continuous_fst.matrix_mul continuous_const).matrix_mulVec continuous_const).add
        ((continuous_fst.matrix_mul continuous_snd).matrix_mulVec continuous_const)))
  · exact (hl2 d).comp ((continuous_snd.matrix_conjTranspose).matrix_mulVec
      (((continuous_fst.matrix_mul continuous_const).matrix_mulVec continuous_const).add
        ((continuous_fst.matrix_mul continuous_snd).matrix_mulVec continuous_const)))

/-- The event of (9.49) [us:eq:Y0] is Borel in the pair (cross block, complementary block). -/
private lemma invImageRange_measurableSet {m d : ℕ}
    (F : Matrix (Fin m) (Fin m) ℂ → Matrix (Fin m) (Fin m) ℂ) (hF : Measurable F)
    (Mc : Matrix (Fin m) (Fin d) ℂ) (r : ℝ) :
    MeasurableSet {p : Matrix (Fin m) (Fin d) ℂ × Matrix (Fin m) (Fin m) ℂ |
      ∃ y ∈ LinearMap.range (F p.2 * Mc).mulVecLin ⊔ LinearMap.range (F p.2 * p.1).mulVecLin,
        r * l2Norm y < l2Norm (p.1ᴴ *ᵥ y)} := by
  have hsc1 : SecondCountableTopology (Matrix (Fin m) (Fin d) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin d → ℂ))
  have hsc2 : SecondCountableTopology (Matrix (Fin m) (Fin m) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin m → ℂ))
  have hg : Measurable fun p : Matrix (Fin m) (Fin d) ℂ × Matrix (Fin m) (Fin m) ℂ =>
      (F p.2, p.1) := (hF.comp measurable_snd).prodMk measurable_fst
  have hO := (invImageRange_isOpen Mc r).measurableSet
  have h2 := hO.preimage hg
  exact h2

/-! ### The deterministic step -/

/-- The deterministic step of the proof of Lemma 9.5 [us:lem:range] on the good event. In the
frames `Φ` of `𝒬 ⊇ ran Q_0 + U + ran (B_1 Q_0) + span (1 - Q_0) v` and `Ψ` of `𝒬^⊥`: if (9.50)
[us:eq:absolute] holds (`‖P_𝒬 x‖ ≤ C_K √(d/W) ‖x‖` on the inverse image of `𝒬`), the
complementary block `Γ_c` is invertible, (9.49) [us:eq:Y0] holds for the cross block `Y` on
`ran (Γ_c⁻¹ M) + ran (Γ_c⁻¹ Y)`, `‖V‖ ≤ 16` and `(V - E - B_0 - B_1) x ∈ ran P_U`, then the
`Q_0`-row gives (9.51) [us:eq:weightedcompression] and the weighted Cauchy–Schwarz inequality
gives (9.42) [us:eq:relative]. -/
private lemma invImageRange_core {W d m : ℕ} {B₀ Q₀ B₁ Pu Pq V : Matrix (Fin W) (Fin W) ℂ}
    {Φ : Matrix (Fin W) (Fin d) ℂ} {Ψ : Matrix (Fin W) (Fin m) ℂ} {Bc : Matrix (Fin m) (Fin m) ℂ}
    {Mc : Matrix (Fin m) (Fin d) ℂ} {v x : Fin W → ℂ} {E ε₀ CT CK C' A K₁ C : ℝ}
    (hB₀ : B₀.IsHermitian) (hQH : Q₀.IsHermitian) (hQI : Q₀ * Q₀ = Q₀) (hQB : Q₀ * B₀ = B₀ * Q₀)
    (hBs : ‖(1 - Q₀) * B₀ * (1 - Q₀)‖ ≤ ε₀) (hB₁n : ‖B₁‖ ≤ ε₀)
    (hQP : ‖Q₀ * Pu‖ ≤ CT * Real.sqrt (d / W)) (hE : ‖(E : ℂ)‖ ≤ 2) (hε₀h : ε₀ ≤ 1 / 2)
    (hCT : 0 < CT) (hCK : 0 < CK) (hC' : 0 < C') (hA : 0 < A)
    (hCTs : CT * Real.sqrt (d / W) ≤ 1 / 4) (hL1 : 1 ≤ Real.log W)
    (hK₁ : K₁ = 19 * CK + C' * Real.sqrt A + 27 * CT) (hCge : 5 * CK ^ 2 + K₁ ^ 2 ≤ C)
    (hPqH : Pq.IsHermitian) (hPqv : Pq *ᵥ ((1 - Q₀) *ᵥ v) = (1 - Q₀) *ᵥ v)
    (hQPq : Q₀ * Pq = Q₀) (hQc : Q₀ * (1 - Pq) = 0) (hQB₁c : Q₀ * B₁ * (1 - Pq) = 0)
    (hcPu : (1 - Pq) * Pu = 0) (hΨ : Ψᴴ * Ψ = 1) (hΦΦ : Φ * Φᴴ = Pq) (hΨΨ : Ψ * Ψᴴ = 1 - Pq)
    (hΨΦ : Ψᴴ * Φ = 0) (hΦn : ‖Φ‖ ≤ 1) (hΨn : ‖Ψᴴ‖ ≤ 1) (hQn : ‖Q₀‖ ≤ 1) (hQcn : ‖1 - Q₀‖ ≤ 1)
    (hBc : Bc = Ψᴴ * (B₀ + B₁) * Ψ) (hMc : Mc = Ψᴴ * (B₀ + B₁) * Φ)
    (hVH : V.IsHermitian) (hVn : ‖V‖ ≤ 16)
    (hSKω : ∀ x, (1 - Pq) *ᵥ ((V - (E : ℂ) • 1 - (B₀ + B₁)) *ᵥ x) = 0 →
      l2Norm (Pq *ᵥ x) ≤ CK * Real.sqrt (d / W) * l2Norm x)
    (hΓcu : IsUnit (Ψᴴ * V * Ψ - (E : ℂ) • 1 - Bc).det)
    (hY : ∀ y ∈ LinearMap.range ((Ψᴴ * V * Ψ - (E : ℂ) • 1 - Bc)⁻¹ * Mc).mulVecLin ⊔
        LinearMap.range ((Ψᴴ * V * Ψ - (E : ℂ) • 1 - Bc)⁻¹ * (Ψᴴ * V * Φ)).mulVecLin,
      l2Norm ((Ψᴴ * V * Φ)ᴴ *ᵥ y) ≤ C' * Real.sqrt (A * d / W) * Real.log W * l2Norm y)
    (hx1 : (1 - Pu) *ᵥ ((V - (E : ℂ) • 1 - B₀ - B₁) *ᵥ x) = 0) :
    ‖star v ⬝ᵥ x‖ ^ 2 ≤ C * (d / W) * Real.log W ^ 2 *
      (star v ⬝ᵥ ((1 + B₀ * B₀)⁻¹ *ᵥ v)).re * l2Norm x ^ 2 := by
  have hEn : ‖((E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ))‖ ≤ 2 := (norm_smul_le _ _).trans
    ((mul_le_mul hE (invImageRange_norm_one W) (norm_nonneg _) (by norm_num)).trans (by norm_num))
  have hG19 : ‖V - (E : ℂ) • 1 - B₁‖ ≤ 19 := by
    calc ‖V - (E : ℂ) • 1 - B₁‖ ≤ ‖V‖ + ‖(E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)‖ + ‖B₁‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ 16 + 2 + 1 := by linarith
      _ = 19 := by norm_num
  set u : Fin W → ℂ := (V - (E : ℂ) • 1 - B₀ - B₁) *ᵥ x with hudef
  have hPuu : Pu *ᵥ u = u := by
    have h := hx1
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
    exact h.symm
  have hΓB : V - (E : ℂ) • 1 - B₀ - B₁ = V - (E : ℂ) • 1 - (B₀ + B₁) := by rw [sub_sub]
  have hcomp : (1 - Pq) *ᵥ ((V - (E : ℂ) • 1 - (B₀ + B₁)) *ᵥ x) = 0 := by
    have : (V - (E : ℂ) • 1 - (B₀ + B₁)) *ᵥ x = u := by rw [hudef, hΓB]
    rw [this, ← hPuu, Matrix.mulVec_mulVec, hcPu, Matrix.zero_mulVec]
  have hPx : l2Norm (Pq *ᵥ x) ≤ CK * Real.sqrt (d / W) * l2Norm x := hSKω x hcomp
  -- the complementary row: `Ψ* x ∈ ran (Γ_c⁻¹ Mc) + ran (Γ_c⁻¹ Y)`
  have hrow := invImageRange_row hΨ hΦΦ hΨΨ (V - (E : ℂ) • 1 - (B₀ + B₁)) x hcomp
  have hΓΨ : Ψᴴ * (V - (E : ℂ) • 1 - (B₀ + B₁)) * Ψ = Ψᴴ * V * Ψ - (E : ℂ) • 1 - Bc := by
    rw [hBc, Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hΨ]
  have hΓΦ : Ψᴴ * (V - (E : ℂ) • 1 - (B₀ + B₁)) * Φ = Ψᴴ * V * Φ - Mc := by
    rw [hMc, Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hΨΦ, smul_zero, sub_zero]
  rw [hΓΨ, hΓΦ] at hrow
  have hb : Ψᴴ *ᵥ x = ((Ψᴴ * V * Ψ - (E : ℂ) • 1 - Bc)⁻¹ * Mc) *ᵥ (Φᴴ *ᵥ x) +
      ((Ψᴴ * V * Ψ - (E : ℂ) • 1 - Bc)⁻¹ * (Ψᴴ * V * Φ)) *ᵥ (-(Φᴴ *ᵥ x)) := by
    have h1 : (Ψᴴ * V * Ψ - (E : ℂ) • 1 - Bc) *ᵥ (Ψᴴ *ᵥ x) =
        Mc *ᵥ (Φᴴ *ᵥ x) - (Ψᴴ * V * Φ) *ᵥ (Φᴴ *ᵥ x) := by
      rw [eq_neg_of_add_eq_zero_left hrow, Matrix.sub_mulVec, neg_sub]
    have h2 : Ψᴴ *ᵥ x = (Ψᴴ * V * Ψ - (E : ℂ) • 1 - Bc)⁻¹ *ᵥ
        ((Ψᴴ * V * Ψ - (E : ℂ) • 1 - Bc) *ᵥ (Ψᴴ *ᵥ x)) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hΓcu, Matrix.one_mulVec]
    rw [h2, h1]
    generalize Φᴴ *ᵥ x = a
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_neg,
      sub_eq_add_neg]
  have hbmem : Ψᴴ *ᵥ x ∈ LinearMap.range ((Ψᴴ * V * Ψ - (E : ℂ) • 1 - Bc)⁻¹ * Mc).mulVecLin ⊔
      LinearMap.range ((Ψᴴ * V * Ψ - (E : ℂ) • 1 - Bc)⁻¹ * (Ψᴴ * V * Φ)).mulVecLin := by
    rw [hb]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)
  have hYb := hY _ hbmem
  -- the `Q_0`-row (9.51) [us:eq:weightedcompression]
  have hY : (Ψᴴ * V * Φ)ᴴ = Φᴴ * V * Ψ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hVH.eq,
      Matrix.mul_assoc]
  have e0 : Q₀ * V * (1 - Pq) = Q₀ * Φ * (Ψᴴ * V * Φ)ᴴ * Ψᴴ :=
    calc Q₀ * V * (1 - Pq) = (Q₀ * Pq) * V * (Ψ * Ψᴴ) := by rw [hQPq, hΨΨ]
      _ = Q₀ * (Φ * Φᴴ) * V * (Ψ * Ψᴴ) := by rw [hΦΦ]
      _ = Q₀ * Φ * (Φᴴ * V * Ψ) * Ψᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hY]
  have hQrow : Q₀ * (V - (E : ℂ) • 1 - B₁) =
      Q₀ * (V - (E : ℂ) • 1 - B₁) * Pq + Q₀ * Φ * (Ψᴴ * V * Φ)ᴴ * Ψᴴ := by
    have e1 : Q₀ * (V - (E : ℂ) • 1 - B₁) * (1 - Pq) = Q₀ * Φ * (Ψᴴ * V * Φ)ᴴ * Ψᴴ := by
      rw [Matrix.mul_sub Q₀, Matrix.mul_sub Q₀, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_smul,
        Matrix.mul_one, Matrix.smul_mul, hQc, smul_zero, sub_zero, hQB₁c, sub_zero, e0]
    calc Q₀ * (V - (E : ℂ) • 1 - B₁) = Q₀ * (V - (E : ℂ) • 1 - B₁) * (Pq + (1 - Pq)) := by
          rw [add_sub_cancel, Matrix.mul_one]
      _ = _ := by rw [Matrix.mul_add, e1]
  have e2 : V - (E : ℂ) • 1 - B₀ - B₁ = (V - (E : ℂ) • 1 - B₁) - B₀ := by abel
  have hQB₀x : Q₀ *ᵥ (B₀ *ᵥ x) = (Q₀ * (V - (E : ℂ) • 1 - B₁)) *ᵥ (Pq *ᵥ x) +
      (Q₀ * Φ) *ᵥ ((Ψᴴ * V * Φ)ᴴ *ᵥ (Ψᴴ *ᵥ x)) - Q₀ *ᵥ u := by
    have e3 : Q₀ *ᵥ u = (Q₀ * (V - (E : ℂ) • 1 - B₁)) *ᵥ x - Q₀ *ᵥ (B₀ *ᵥ x) := by
      rw [hudef, e2, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    have h4 : (Q₀ * (V - (E : ℂ) • 1 - B₁)) *ᵥ x = (Q₀ * (V - (E : ℂ) • 1 - B₁)) *ᵥ (Pq *ᵥ x) +
        (Q₀ * Φ) *ᵥ ((Ψᴴ * V * Φ)ᴴ *ᵥ (Ψᴴ *ᵥ x)) := by
      conv_lhs => rw [hQrow]
      rw [Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_assoc (Q₀ * Φ)]
    rw [e3, h4]
    abel
  -- transversality: `‖Q_0 u‖ ≤ 27 C_T √(d/W) ‖x‖`
  have f0 : (1 - Q₀) * Q₀ = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hQI, sub_self]
  have f1 : (1 - Q₀) * B₀ * (1 - Q₀) = (1 - Q₀) * B₀ := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, ← hQB, ← Matrix.mul_assoc, f0,
      Matrix.zero_mul, sub_zero]
  have hQcΓ : ‖(1 - Q₀) * (V - (E : ℂ) • 1 - B₀ - B₁)‖ ≤ 20 := by
    rw [e2, Matrix.mul_sub, ← f1]
    calc ‖(1 - Q₀) * (V - (E : ℂ) • 1 - B₁) - (1 - Q₀) * B₀ * (1 - Q₀)‖
        ≤ ‖(1 - Q₀) * (V - (E : ℂ) • 1 - B₁)‖ + ‖(1 - Q₀) * B₀ * (1 - Q₀)‖ := norm_sub_le _ _
      _ ≤ 1 * 19 + ε₀ := add_le_add ((Matrix.l2_opNorm_mul _ _).trans
          (mul_le_mul hQcn hG19 (norm_nonneg _) zero_le_one)) hBs
      _ ≤ 20 := by linarith
  have hX0 : 0 ≤ l2Norm x := invImageRange_l2Norm_nonneg x
  have hs0 : 0 ≤ Real.sqrt (d / W) := Real.sqrt_nonneg _
  have hu1 : l2Norm ((1 - Q₀) *ᵥ u) ≤ 20 * l2Norm x := by
    rw [hudef, Matrix.mulVec_mulVec]
    exact (l2Norm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right hQcΓ hX0)
  have hu0 : l2Norm (Q₀ *ᵥ u) ≤ CT * Real.sqrt (d / W) * l2Norm u := by
    have : Q₀ *ᵥ u = (Q₀ * Pu) *ᵥ u := by rw [← Matrix.mulVec_mulVec, hPuu]
    rw [this]
    exact (l2Norm_mulVec_le _ _).trans
      (mul_le_mul_of_nonneg_right hQP (invImageRange_l2Norm_nonneg _))
  have hus : l2Norm u ≤ l2Norm (Q₀ *ᵥ u) + l2Norm ((1 - Q₀) *ᵥ u) := by
    have : u = Q₀ *ᵥ u + (1 - Q₀) *ᵥ u := by
      rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
    conv_lhs => rw [this]
    exact invImageRange_l2Norm_add _ _
  have hQu : l2Norm (Q₀ *ᵥ u) ≤ 27 * CT * Real.sqrt (d / W) * l2Norm x := by
    have hU0 : 0 ≤ l2Norm u := invImageRange_l2Norm_nonneg u
    have hCTs0 : 0 ≤ CT * Real.sqrt (d / W) := mul_nonneg hCT.le hs0
    have h1 : CT * Real.sqrt (d / W) * l2Norm u ≤ 1 / 4 * l2Norm u :=
      mul_le_mul_of_nonneg_right hCTs hU0
    have h2 : l2Norm u ≤ 80 / 3 * l2Norm x := by linarith
    have h3 : CT * Real.sqrt (d / W) * l2Norm u ≤ CT * Real.sqrt (d / W) * (80 / 3 * l2Norm x) :=
      mul_le_mul_of_nonneg_left h2 hCTs0
    have e : 27 * CT * Real.sqrt (d / W) * l2Norm x -
        CT * Real.sqrt (d / W) * (80 / 3 * l2Norm x) =
        1 / 3 * (CT * Real.sqrt (d / W) * l2Norm x) := by ring
    have := mul_nonneg hCTs0 hX0
    linarith
  -- (9.51) [us:eq:weightedcompression] and the weighted Cauchy–Schwarz inequality
  have hr : C' * Real.sqrt (A * d / W) * Real.log W =
      C' * Real.sqrt A * Real.sqrt (d / W) * Real.log W := by
    rw [mul_div_assoc, Real.sqrt_mul hA.le]
    ring
  have hs2 : Real.sqrt (d / W) ^ 2 = d / W := Real.sq_sqrt (by positivity)
  have hbX : l2Norm (Ψᴴ *ᵥ x) ≤ l2Norm x :=
    (l2Norm_mulVec_le _ _).trans ((mul_le_mul_of_nonneg_right hΨn hX0).trans (one_mul _).le)
  have hQG : ‖Q₀ * (V - (E : ℂ) • 1 - B₁)‖ ≤ 19 :=
    (Matrix.l2_opNorm_mul _ _).trans
      ((mul_le_mul hQn hG19 (norm_nonneg _) zero_le_one).trans (by norm_num))
  have hQΦ : ‖Q₀ * Φ‖ ≤ 1 :=
    (Matrix.l2_opNorm_mul _ _).trans
      ((mul_le_mul hQn hΦn (norm_nonneg _) zero_le_one).trans (by norm_num))
  have hPQ : l2Norm (Q₀ *ᵥ x) ≤ l2Norm (Pq *ᵥ x) := by
    have : Q₀ *ᵥ x = Q₀ *ᵥ (Pq *ᵥ x) := by rw [Matrix.mulVec_mulVec, hQPq]
    rw [this]
    exact (l2Norm_mulVec_le _ _).trans
      ((mul_le_mul_of_nonneg_right hQn (invImageRange_l2Norm_nonneg _)).trans (one_mul _).le)
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (d / W) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log W := ⟨_, rfl⟩
  rw [← hs] at hr hs2 hPx hQu hs0
  rw [← hL] at hr hYb
  have hL1' : 1 ≤ L := hL ▸ hL1
  have hYb' : l2Norm ((Ψᴴ * V * Φ)ᴴ *ᵥ (Ψᴴ *ᵥ x)) ≤ C' * Real.sqrt A * s * L * l2Norm x := by
    rw [hr] at hYb
    refine hYb.trans (mul_le_mul_of_nonneg_left hbX ?_)
    exact mul_nonneg (mul_nonneg (mul_nonneg hC'.le (Real.sqrt_nonneg _)) hs0) (by linarith)
  have hZ1 : l2Norm (B₀ *ᵥ (Q₀ *ᵥ x)) ≤
      19 * l2Norm (Pq *ᵥ x) + C' * Real.sqrt A * s * L * l2Norm x + 27 * CT * s * l2Norm x := by
    have : B₀ *ᵥ (Q₀ *ᵥ x) = Q₀ *ᵥ (B₀ *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQB]
    rw [this, hQB₀x]
    refine (invImageRange_l2Norm_sub _ _).trans
      (add_le_add ((invImageRange_l2Norm_add _ _).trans (add_le_add ?_ ?_)) hQu)
    · exact (l2Norm_mulVec_le _ _).trans
        (mul_le_mul_of_nonneg_right hQG (invImageRange_l2Norm_nonneg _))
    · exact (l2Norm_mulVec_le _ _).trans ((mul_le_mul_of_nonneg_right hQΦ
        (invImageRange_l2Norm_nonneg _)).trans ((one_mul _).le.trans hYb'))
  have hsX : s * l2Norm x ≤ s * L * l2Norm x := by
    have h := mul_le_mul_of_nonneg_left hL1' (mul_nonneg hs0 hX0)
    have e : s * L * l2Norm x = s * l2Norm x * L := by ring
    rw [mul_one] at h
    rw [e]
    exact h
  have hP' : l2Norm (Pq *ᵥ x) ≤ CK * (s * L * l2Norm x) := by
    refine hPx.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hsX hCK.le
  have hX' : l2Norm (Q₀ *ᵥ x) ≤ CK * (s * L * l2Norm x) := hPQ.trans hP'
  have hZ' : l2Norm (B₀ *ᵥ (Q₀ *ᵥ x)) ≤ K₁ * (s * L * l2Norm x) := by
    have h27 : 27 * CT * s * l2Norm x ≤ 27 * CT * (s * L * l2Norm x) := by
      have := mul_le_mul_of_nonneg_left hsX (by positivity : (0 : ℝ) ≤ 27 * CT)
      have e : 27 * CT * s * l2Norm x = 27 * CT * (s * l2Norm x) := by ring
      linarith
    have hK : K₁ * (s * L * l2Norm x) = 19 * CK * (s * L * l2Norm x) +
        C' * Real.sqrt A * s * L * l2Norm x + 27 * CT * (s * L * l2Norm x) := by
      rw [hK₁]
      ring
    have h19 : 19 * l2Norm (Pq *ᵥ x) ≤ 19 * CK * (s * L * l2Norm x) := by linarith
    linarith
  obtain ⟨hw0, hwb⟩ := invImageRange_weighted hB₀ hQH hQI hQB (by linarith : ε₀ ≤ 1) hBs hPqH
    v x hPqv
  have hsq : l2Norm (Q₀ *ᵥ x) ^ 2 + l2Norm (B₀ *ᵥ (Q₀ *ᵥ x)) ^ 2 + 4 * l2Norm (Pq *ᵥ x) ^ 2 ≤
      (5 * CK ^ 2 + K₁ ^ 2) * (s * L * l2Norm x) ^ 2 := by
    have a1 := pow_le_pow_left₀ (invImageRange_l2Norm_nonneg _) hX' 2
    have a2 := pow_le_pow_left₀ (invImageRange_l2Norm_nonneg _) hZ' 2
    have a3 := pow_le_pow_left₀ (invImageRange_l2Norm_nonneg _) hP' 2
    rw [mul_pow] at a1 a2 a3
    linarith only [a1, a2, a3]
  rw [← hL]
  calc ‖star v ⬝ᵥ x‖ ^ 2 ≤ (star v ⬝ᵥ ((1 + B₀ * B₀)⁻¹ *ᵥ v)).re *
          (l2Norm (Q₀ *ᵥ x) ^ 2 + l2Norm (B₀ *ᵥ (Q₀ *ᵥ x)) ^ 2 + 4 * l2Norm (Pq *ᵥ x) ^ 2) := hwb
      _ ≤ (star v ⬝ᵥ ((1 + B₀ * B₀)⁻¹ *ᵥ v)).re *
          ((5 * CK ^ 2 + K₁ ^ 2) * (s * L * l2Norm x) ^ 2) := mul_le_mul_of_nonneg_left hsq hw0
      _ ≤ (star v ⬝ᵥ ((1 + B₀ * B₀)⁻¹ *ᵥ v)).re * (C * (s * L * l2Norm x) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCge (sq_nonneg _)) hw0
      _ = C * (d / W) * L ^ 2 * (star v ⬝ᵥ ((1 + B₀ * B₀)⁻¹ *ᵥ v)).re * l2Norm x ^ 2 := by
          rw [mul_pow, mul_pow, hs2]
          ring


/-- Lemma 9.5 [us:lem:range], (9.42) [us:eq:relative]: for every transversality constant `C_T`
there are `ε₀, C, c` such that, under the hypotheses above, every `x` with
`(V - E - B_0 - B_1) x ∈ ran P_U` has `|v* x|² ≤ C (d/W) (log W)² v*(1 + B_0²)⁻¹v ‖x‖²`, with
failure `W^{-D} + C e^{-c d}`, uniformly in `‖Q_0 B_0 Q_0‖`. -/
theorem invImage_relative_le (κ₀ δ CT : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hδ : 0 < δ)
    (hCT : 0 < CT) :
    ∃ ε₀ C c : ℝ, 0 < ε₀ ∧ 0 < C ∧ 0 < c ∧ ∀ D : ℝ, 0 < D → ∃ W₀ : ℕ, ∀ W d : ℕ, W₀ ≤ W →
      (W : ℝ) ^ δ ≤ d → (d : ℝ) ≤ ε₀ * W →
      ∀ (B₀ Q₀ B₁ Pu : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ) (E : ℝ), B₀.IsHermitian →
        Q₀.IsHermitian → Q₀ * Q₀ = Q₀ → Q₀ * B₀ = B₀ * Q₀ →
        ‖(1 - Q₀) * B₀ * (1 - Q₀)‖ ≤ ε₀ → B₁.IsHermitian → ‖B₁‖ ≤ ε₀ →
        Pu.IsHermitian → Pu * Pu = Pu → ‖Q₀ * Pu‖ ≤ CT * Real.sqrt (d / W) →
        Pu.trace.re + 2 * Q₀.trace.re + 1 ≤ d → |E| ≤ 2 - κ₀ →
        μ W 1 {ω | ∃ x, (1 - Pu) *ᵥ ((gueMat W ω - (E : ℂ) • 1 - B₀ - B₁) *ᵥ x) = 0 ∧
            C * (d / W) * Real.log W ^ 2 * (star v ⬝ᵥ ((1 + B₀ * B₀)⁻¹ *ᵥ v)).re *
              l2Norm x ^ 2 < ‖star v ⬝ᵥ x‖ ^ 2} ≤
          ENNReal.ofReal ((W : ℝ) ^ (-D) + C * Real.exp (-(c * d))) := by
  obtain ⟨C₀, hC₀, hgp⟩ := gaussProj_overlap_le
  obtain ⟨εS, A, CS, C₁, hεS, hA, hCS, hC₁, hcs⟩ := compress_specInput κ₀ hκ₀ hκ₀' C₀ hC₀
  obtain ⟨C', c', hC', hc', hgp'⟩ := hgp A CS C₁ hA hCS hC₁
  obtain ⟨εK, CK, cK, hεK, hCK, hcK, hK⟩ := invImage_compress_le κ₀ δ hκ₀ hκ₀' hδ
  set K₁ : ℝ := 19 * CK + C' * Real.sqrt A + 27 * CT with hK₁
  set C : ℝ := 5 * CK ^ 2 + K₁ ^ 2 + CK + C' + 1 with hCdef
  set ε₀ : ℝ := min (min (εK / 2) (εS / 2)) (min (1 / (16 * CT ^ 2)) (1 / 2)) with hε₀def
  have hε₀ : 0 < ε₀ :=
    lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by norm_num))
  have hε₀K : ε₀ ≤ εK / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hε₀S : ε₀ ≤ εS / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hε₀T : ε₀ ≤ 1 / (16 * CT ^ 2) := (min_le_right _ _).trans (min_le_left _ _)
  have hε₀h : ε₀ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  set c : ℝ := min (min cK c') (1 / 2) with hcdef
  have hc : 0 < c := lt_min (lt_min hcK hc') (by norm_num)
  have hccK : c ≤ cK := (min_le_left _ _).trans (min_le_left _ _)
  have hcc' : c ≤ c' := (min_le_left _ _).trans (min_le_right _ _)
  have hch : c ≤ 1 / 2 := min_le_right _ _
  refine ⟨ε₀, C, c, hε₀, by positivity, hc, fun D hD => ?_⟩
  obtain ⟨WS, hWS⟩ := hcs δ (D + 1) hδ (by linarith)
  obtain ⟨WK, hWK⟩ := hK (D + 1) (by linarith)
  refine ⟨max (max WS WK) 32, fun W d hW hdW hdε B₀ Q₀ B₁ Pu v E hB₀ hQH hQI hQB hBs hB₁
    hB₁n hPuH hPuI hQP htr hE => ?_⟩
  have hWS' : WS ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hWK' : WK ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hW32 : 32 ≤ W := (le_max_right _ _).trans hW
  have hW32r : (32 : ℝ) ≤ W := by exact_mod_cast hW32
  have hWpos : (0 : ℝ) < W := by linarith
  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos δ) hdW
  have hdW2 : (d : ℝ) ≤ W / 2 := hdε.trans (by nlinarith)
  have hdWn : d ≤ W := by
    have : (d : ℝ) ≤ W := by linarith
    exact_mod_cast this
  have hdεK : (d : ℝ) ≤ εK * W := hdε.trans (mul_le_mul_of_nonneg_right (by linarith) hWpos.le)
  have hdεS : (d : ℝ) ≤ εS * W := hdε.trans (mul_le_mul_of_nonneg_right (by linarith) hWpos.le)
  -- the space `𝒬 ⊇ ran Q_0 + U + ran (B_1 Q_0) + span (1 - Q_0) v` of dimension `d`
  have hQtr := (invImageRange_projFrame_rank hQH hQI).1
  have hPutr := (invImageRange_projFrame_rank hPuH hPuI).1
  set K₀ : Submodule ℂ (Fin W → ℂ) := LinearMap.range Q₀.mulVecLin ⊔
    LinearMap.range Pu.mulVecLin ⊔ LinearMap.range (B₁ * Q₀).mulVecLin ⊔
    Submodule.span ℂ {(1 - Q₀) *ᵥ v} with hK₀def
  have hK₀ : Module.finrank ℂ K₀ ≤ d := by
    have h1 := Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range Q₀.mulVecLin ⊔
      LinearMap.range Pu.mulVecLin ⊔ LinearMap.range (B₁ * Q₀).mulVecLin)
      (Submodule.span ℂ {(1 - Q₀) *ᵥ v})
    have h2 := Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range Q₀.mulVecLin ⊔
      LinearMap.range Pu.mulVecLin) (LinearMap.range (B₁ * Q₀).mulVecLin)
    have h3 := Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range Q₀.mulVecLin)
      (LinearMap.range Pu.mulVecLin)
    have h4 : Module.finrank ℂ (Submodule.span ℂ ({(1 - Q₀) *ᵥ v} : Set (Fin W → ℂ))) ≤ 1 := by
      have := finrank_span_le_card (R := ℂ) ({(1 - Q₀) *ᵥ v} : Set (Fin W → ℂ))
      simpa using this
    have h5 : (B₁ * Q₀).rank ≤ Q₀.rank := Matrix.rank_mul_le_right _ _
    have h6 : Pu.rank + 2 * Q₀.rank + 1 ≤ d := by
      have hQr : (Q₀.rank : ℝ) = Q₀.trace.re := by rw [hQtr, Complex.natCast_re]
      have hPr : (Pu.rank : ℝ) = Pu.trace.re := by rw [hPutr, Complex.natCast_re]
      have : ((Pu.rank + 2 * Q₀.rank + 1 : ℕ) : ℝ) ≤ d := by push_cast; linarith
      exact_mod_cast this
    rw [← hK₀def] at h1
    unfold Matrix.rank at h5 h6
    omega
  obtain ⟨K, hK₀K, hKd⟩ := invImageRange_extend K₀ (d - Module.finrank ℂ K₀) (by omega)
  have hKd' : Module.finrank ℂ K = d := by omega
  obtain ⟨N, hN1, -, hN3⟩ := invImageRange_frame K hKd'
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
  have hPqQ : Pq * Q₀ = Q₀ := invImageRange_ext fun u => by
    rw [← Matrix.mulVec_mulVec]
    exact hfix _ (hK₀K (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left
      (LinearMap.mem_range.2 ⟨u, Matrix.mulVecLin_apply Q₀ u⟩)))))
  have hPqPu : Pq * Pu = Pu := invImageRange_ext fun u => by
    rw [← Matrix.mulVec_mulVec]
    exact hfix _ (hK₀K (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right
      (LinearMap.mem_range.2 ⟨u, Matrix.mulVecLin_apply Pu u⟩)))))
  have hPqBQ : Pq * (B₁ * Q₀) = B₁ * Q₀ := invImageRange_ext fun u => by
    rw [← Matrix.mulVec_mulVec]
    exact hfix _ (hK₀K (Submodule.mem_sup_left (Submodule.mem_sup_right
      (LinearMap.mem_range.2 ⟨u, Matrix.mulVecLin_apply (B₁ * Q₀) u⟩))))
  have hPqv : Pq *ᵥ ((1 - Q₀) *ᵥ v) = (1 - Q₀) *ᵥ v :=
    hfix _ (hK₀K (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
  have hQPq : Q₀ * Pq = Q₀ := by
    have := congrArg Matrix.conjTranspose hPqQ
    rwa [Matrix.conjTranspose_mul, hPqH.eq, hQH.eq] at this
  have hQc : Q₀ * (1 - Pq) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hQPq, sub_self]
  have hcQ : (1 - Pq) * Q₀ = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hPqQ, sub_self]
  have hcPu : (1 - Pq) * Pu = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hPqPu, sub_self]
  have hQB₁c : Q₀ * B₁ * (1 - Pq) = 0 := by
    have h1 : (1 - Pq) * (B₁ * Q₀) = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hPqBQ, sub_self]
    have := congrArg Matrix.conjTranspose h1
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQH.eq, hB₁.eq,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPqH.eq, Matrix.conjTranspose_zero]
      at this
  -- the frames `Φ` of `𝒬` and `Ψ` of its complement
  have hRH : (1 - Pq).IsHermitian := Matrix.isHermitian_one.sub hPqH
  have hRI : (1 - Pq) * (1 - Pq) = 1 - Pq := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hPqI, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, sub_self, sub_zero]
  have htrQ := (invImageRange_projFrame_rank hRH hRI).1
  obtain ⟨m, hm⟩ : ∃ m, (1 - Pq).rank = m := ⟨_, rfl⟩
  rw [hm] at htrQ
  obtain ⟨N₂, hN₂1, hN₂2⟩ := invImageRange_projFrame hRH hRI htrQ
  have hdm : d + m = W := by
    have h1 : (1 - Pq).trace = (W : ℂ) - d := by
      rw [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, hPqtr]
    rw [htrQ] at h1
    have : ((d + m : ℕ) : ℂ) = W := by push_cast; rw [h1]; ring
    exact_mod_cast this
  have hΦ : Nᴴᴴ * Nᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose, hN1]
  have hΨ : N₂ᴴᴴ * N₂ᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose, hN₂1]
  have hΦΦ : Nᴴ * Nᴴᴴ = Pq := by rw [Matrix.conjTranspose_conjTranspose, hPqdef]
  have hΨΨ : N₂ᴴ * N₂ᴴᴴ = 1 - Pq := by rw [Matrix.conjTranspose_conjTranspose, hN₂2]
  set Φ : Matrix (Fin W) (Fin d) ℂ := Nᴴ with hΦdef
  set Ψ : Matrix (Fin W) (Fin m) ℂ := N₂ᴴ with hΨdef
  have hΦΨ : Φᴴ * Ψ = 0 :=
    calc Φᴴ * Ψ = Φᴴ * (Φ * Φᴴ) * ((Ψ * Ψᴴ) * Ψ) := by
          rw [← Matrix.mul_assoc Φᴴ Φ, hΦ, Matrix.one_mul, Matrix.mul_assoc Ψ, hΨ, Matrix.mul_one]
      _ = Φᴴ * (Pq * (1 - Pq)) * Ψ := by rw [hΦΦ, hΨΨ]; simp only [Matrix.mul_assoc]
      _ = 0 := by
          rw [Matrix.mul_sub, Matrix.mul_one, hPqI, sub_self, Matrix.mul_zero, Matrix.zero_mul]
  have hΨΦ : Ψᴴ * Φ = 0 := by
    rw [← Matrix.conjTranspose_conjTranspose Φ, ← Matrix.conjTranspose_mul, hΦΨ,
      Matrix.conjTranspose_zero]
  have hΦn : ‖Φ‖ ≤ 1 := invImageRange_norm_isometry hΦ
  have hΨn : ‖Ψᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact invImageRange_norm_isometry hΨ
  -- norms
  have hQn : ‖Q₀‖ ≤ 1 := invImageRange_norm_proj hQH hQI
  have hQcI : (1 - Q₀) * (1 - Q₀) = 1 - Q₀ := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hQI, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, sub_self, sub_zero]
  have hQcn : ‖1 - Q₀‖ ≤ 1 := invImageRange_norm_proj (Matrix.isHermitian_one.sub hQH) hQcI
  have hPcn : ‖1 - Pq‖ ≤ 1 := invImageRange_norm_proj hRH hRI
  set B : Matrix (Fin W) (Fin W) ℂ := B₀ + B₁ with hBdef
  have hBH : B.IsHermitian := hB₀.add hB₁
  have hBc2 : ‖(1 - Pq) * B * (1 - Pq)‖ ≤ 2 * ε₀ := by
    have e1 : (1 - Pq) * (1 - Q₀) = 1 - Pq := by rw [Matrix.mul_sub, Matrix.mul_one, hcQ, sub_zero]
    have e2 : (1 - Q₀) * (1 - Pq) = 1 - Pq := by rw [Matrix.sub_mul, Matrix.one_mul, hQc, sub_zero]
    have e3 : (1 - Pq) * B * (1 - Pq) = (1 - Pq) * ((1 - Q₀) * B₀ * (1 - Q₀) + B₁) * (1 - Pq) := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_add, Matrix.add_mul,
        show (1 - Pq) * ((1 - Q₀) * B₀ * (1 - Q₀)) * (1 - Pq) =
        ((1 - Pq) * (1 - Q₀)) * B₀ * ((1 - Q₀) * (1 - Pq)) by simp only [Matrix.mul_assoc], e1, e2]
    rw [e3]
    calc _ ≤ ‖1 - Pq‖ * ‖(1 - Q₀) * B₀ * (1 - Q₀) + B₁‖ * ‖1 - Pq‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * (ε₀ + ε₀) * 1 := by gcongr; exact (norm_add_le _ _).trans (add_le_add hBs hB₁n)
      _ = 2 * ε₀ := by ring
  have hnormK : ‖(1 - Pq) * B * (1 - Pq)‖ ≤ εK := hBc2.trans (by linarith)
  -- the complementary block `Bc = Ψ* B Ψ` and the cross mean `Mc = Ψ* B Φ`
  set Bc : Matrix (Fin m) (Fin m) ℂ := Ψᴴ * B * Ψ with hBcdef
  set Mc : Matrix (Fin m) (Fin d) ℂ := Ψᴴ * B * Φ with hMcdef
  have hBcH : Bc.IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul Ψ hBH
  have hBcn : ‖Bc‖ ≤ εS := by
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
      _ ≤ 1 * (2 * ε₀) * 1 := by
          gcongr
          rw [← Matrix.l2_opNorm_conjTranspose]
          exact hΨn
      _ ≤ εS := by linarith
  -- the event of (9.49) [us:eq:Y0] and its sections
  set Rf : Matrix (Fin m) (Fin m) ℂ → Matrix (Fin m) (Fin m) ℂ :=
    fun K => (K - (E : ℂ) • 1 - Bc)⁻¹ with hRfdef
  have hRf : Measurable Rf :=
    invImageRange_measurable_inv.comp ((measurable_id.sub_const _).sub_const _)
  set r : ℝ := C' * Real.sqrt (A * d / W) * Real.log W with hrdef
  set T₀ : Set (Matrix (Fin m) (Fin d) ℂ × Matrix (Fin m) (Fin m) ℂ) :=
    {p | ∃ y ∈ LinearMap.range (Rf p.2 * Mc).mulVecLin ⊔ LinearMap.range (Rf p.2 * p.1).mulVecLin,
      r * l2Norm y < l2Norm (p.1ᴴ *ᵥ y)} with hT₀def
  have hT₀ : MeasurableSet T₀ := invImageRange_measurableSet Rf hRf Mc r
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (Matrix (Fin m) (Fin d) ℂ),
      ν = (stdCGauss (Fin m × Fin d)).map fun x => (((Real.sqrt W)⁻¹ : ℝ) : ℂ) • cgMat x :=
    ⟨_, rfl⟩
  have hcg : Measurable fun x : Fin m × Fin d → ℂ => cgMat x :=
    Matrix.measurable_iff.2 fun i j => measurable_pi_apply (i, j)
  have hg₂ : Measurable fun x : Fin m × Fin d → ℂ => (((Real.sqrt W)⁻¹ : ℝ) : ℂ) • cgMat x :=
    (continuous_const_smul _).measurable.comp hcg
  have : IsFiniteMeasure ν := by rw [hν]; infer_instance
  set G : Set (Matrix (Fin m) (Fin m) ℂ) :=
    {K | ν ((fun Y => (Y, K)) ⁻¹' T₀) ≤ ENNReal.ofReal (C' * Real.exp (-(c' * d)))} with hGdef
  have hG : MeasurableSet G :=
    measurableSet_le (measurable_measure_prodMk_right hT₀) measurable_const
  set T : Set (Matrix (Fin m) (Fin d) ℂ × Matrix (Fin m) (Fin m) ℂ) := T₀ ∩ {p | p.2 ∈ G}
    with hTdef
  have hT : MeasurableSet T := hT₀.inter (measurable_snd hG)
  have hsec : ∀ K, InvSpecInput C₀ CS C₁ W d (A * d / W) (Rf K) → K ∈ G := by
    intro K hspec
    have hd0 : 0 < C₀ * d := by positivity
    have hRH : (Rf K).IsHermitian := invImageRange_isHermitian_of_count hd0 hspec.1
    have hF : Module.finrank ℂ (LinearMap.range (Rf K * Mc).mulVecLin) ≤ d := by
      have := LinearMap.finrank_range_le (Rf K * Mc).mulVecLin
      rwa [Module.finrank_fin_fun] at this
    have h := hgp' W m d d (by omega) (by omega) le_rfl (Rf K) hRH hspec _ hF
    change ν _ ≤ _
    rw [hν, Measure.map_apply hg₂ (measurable_prodMk_right hT₀)]
    exact h
  set t : Ω W 1 → Matrix (Fin d) (Fin d) ℂ × Matrix (Fin m) (Fin d) ℂ ×
      Matrix (Fin m) (Fin m) ℂ :=
    fun ω => (Φᴴ * gueMat W ω * Φ, Ψᴴ * gueMat W ω * Φ, Ψᴴ * gueMat W ω * Ψ) with htdef
  have ht : Measurable t := by
    have hgm := invImageRange_measurable_gueMat W
    refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_) <;>
      exact ((continuous_const.matrix_mul continuous_id).matrix_mul
        continuous_const).measurable.comp hgm
  have hSG : μ W 1 (t ⁻¹' (Set.univ ×ˢ T)) ≤ ENNReal.ofReal (C' * Real.exp (-(c' * d))) := by
    have hlaw := map_blockCompress_gueMat W d m hdm Φ Ψ hΦ hΨ hΦΨ
    have hg₁ : Measurable fun ω : Ω d 1 => ((Real.sqrt ((d : ℝ) / W) : ℝ) : ℂ) • gueMat d ω :=
      (continuous_const_smul _).measurable.comp (invImageRange_measurable_gueMat d)
    have hg₃ : Measurable fun ω : Ω m 1 => ((Real.sqrt ((m : ℝ) / W) : ℝ) : ℂ) • gueMat m ω :=
      (continuous_const_smul _).measurable.comp (invImageRange_measurable_gueMat m)
    rw [← Measure.map_apply ht (MeasurableSet.univ.prod hT), htdef, hlaw, ← hν, Measure.prod_prod,
      Measure.map_apply hg₁ MeasurableSet.univ, Set.preimage_univ, measure_univ, one_mul,
      Measure.prod_apply_symm hT]
    calc ∫⁻ K, ν ((fun Y => (Y, K)) ⁻¹' T)
          ∂((μ m 1).map fun ω => ((Real.sqrt ((m : ℝ) / W) : ℝ) : ℂ) • gueMat m ω)
        ≤ ∫⁻ _K, ENNReal.ofReal (C' * Real.exp (-(c' * d)))
          ∂((μ m 1).map fun ω => ((Real.sqrt ((m : ℝ) / W) : ℝ) : ℂ) • gueMat m ω) := by
          refine lintegral_mono fun K => ?_
          by_cases hK : K ∈ G
          · exact (measure_mono (Set.preimage_mono Set.inter_subset_left)).trans hK
          · exact (measure_mono_null (s := (fun Y => (Y, K)) ⁻¹' T) (t := ∅)
              (fun Y (hY : (Y, K) ∈ T) => (hK hY.2).elim) measure_empty).trans_le bot_le
      _ = ENNReal.ofReal (C' * Real.exp (-(c' * d))) := by
          rw [lintegral_const, Measure.map_apply hg₃ MeasurableSet.univ, Set.preimage_univ,
            measure_univ, mul_one]
  -- the other failure events
  set SK : Set (Ω W 1) := {ω | ∃ x, (1 - Pq) *ᵥ ((gueMat W ω - (E : ℂ) • 1 - B) *ᵥ x) = 0 ∧
      CK * Real.sqrt (d / W) * l2Norm x < l2Norm (Pq *ᵥ x)} with hSKdef
  have hSK : μ W 1 SK ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 1)) + CK * Real.exp (-(cK * d))) :=
    hWK W d hWK' hdW hdεK Pq B E hPqH hPqI hPqtr hBH hnormK hE
  set SV : Set (Ω W 1) := {ω | 16 < ‖gueBlock W 1 ω 0‖} with hSVdef
  have hSV : μ W 1 SV ≤ ENNReal.ofReal (Real.exp (-(W : ℝ) / 2)) := gueBlock_norm_tail hW32 0
  set SS : Set (Ω W 1) := {ω | ¬ InvSpecInput C₀ CS C₁ W d (A * d / W)
      (Ψᴴ * gueMat W ω * Ψ - (E : ℂ) • 1 - Bc)⁻¹} with hSSdef
  have hSS : μ W 1 SS ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) :=
    hWS W m d hWS' (by omega) hdW hdεS Ψ Bc E hΨ hBcH hBcn hE
  -- the deterministic step: the event lies in the union of the four failure events
  have hCTs : CT * Real.sqrt (d / W) ≤ 1 / 4 := by
    have hdW' : (d : ℝ) / W ≤ ε₀ := by rw [div_le_iff₀ hWpos]; exact hdε
    have h16 : ε₀ * (16 * CT ^ 2) ≤ 1 := (le_div_iff₀ (by positivity)).1 hε₀T
    have hs2 : Real.sqrt (d / W) ^ 2 = d / W := Real.sq_sqrt (by positivity)
    have h4 : (CT * Real.sqrt (d / W)) ^ 2 ≤ (1 / 4) ^ 2 := by
      rw [mul_pow, hs2]
      linarith [mul_le_mul_of_nonneg_left hdW' (sq_nonneg CT)]
    exact (pow_le_pow_iff_left₀ (mul_nonneg hCT.le (Real.sqrt_nonneg _)) (by norm_num)
      two_ne_zero).1 h4
  have hL1 : 1 ≤ Real.log W := by
    rw [Real.le_log_iff_exp_le hWpos]
    linarith [Real.exp_one_lt_d9]
  have hCge : 5 * CK ^ 2 + K₁ ^ 2 ≤ C := by
    rw [hCdef]
    linarith only [hCK, hC']
  have hsub : {ω | ∃ x, (1 - Pu) *ᵥ ((gueMat W ω - (E : ℂ) • 1 - B₀ - B₁) *ᵥ x) = 0 ∧
      C * (d / W) * Real.log W ^ 2 * (star v ⬝ᵥ ((1 + B₀ * B₀)⁻¹ *ᵥ v)).re *
        l2Norm x ^ 2 < ‖star v ⬝ᵥ x‖ ^ 2} ⊆ SK ∪ SV ∪ SS ∪ t ⁻¹' (Set.univ ×ˢ T) := by
    rintro ω ⟨x, hx1, hx2⟩
    by_cases h1 : ω ∈ SK
    · exact Or.inl (Or.inl (Or.inl h1))
    by_cases h2 : ω ∈ SV
    · exact Or.inl (Or.inl (Or.inr h2))
    by_cases h3 : ω ∈ SS
    · exact Or.inl (Or.inr h3)
    have hspec : InvSpecInput C₀ CS C₁ W d (A * d / W)
        (Ψᴴ * gueMat W ω * Ψ - (E : ℂ) • 1 - Bc)⁻¹ := not_not.1 h3
    have hVH : (gueMat W ω).IsHermitian := gueBlock_isHermitian W 1 ω 0
    have hVn : ‖gueMat W ω‖ ≤ 16 := not_lt.1 h2
    have hSKω : ∀ x, (1 - Pq) *ᵥ ((gueMat W ω - (E : ℂ) • 1 - B) *ᵥ x) = 0 →
        l2Norm (Pq *ᵥ x) ≤ CK * Real.sqrt (d / W) * l2Norm x :=
      fun x hx => not_lt.1 fun h => h1 ⟨x, hx, h⟩
    suffices hmem : (Ψᴴ * gueMat W ω * Φ, Ψᴴ * gueMat W ω * Ψ) ∈ T₀ from
      Or.inr (Set.mem_prod.2 ⟨Set.mem_univ _, hmem, hsec _ hspec⟩)
    clear_value t T G
    obtain ⟨V, hV⟩ : ∃ V, V = gueMat W ω := ⟨_, rfl⟩
    rw [← hV] at hx1 hspec hVH hVn hSKω ⊢
    by_contra hT₀ω
    have hΓcu : IsUnit (Ψᴴ * V * Ψ - (E : ℂ) • 1 - Bc).det :=
      invImageRange_isUnit_of_count (by positivity : (0 : ℝ) < A * d / W)
        (by positivity : (0 : ℝ) < C₀ * d) hspec.1
    have hY : ∀ y ∈ LinearMap.range ((Ψᴴ * V * Ψ - (E : ℂ) • 1 - Bc)⁻¹ * Mc).mulVecLin ⊔
        LinearMap.range ((Ψᴴ * V * Ψ - (E : ℂ) • 1 - Bc)⁻¹ * (Ψᴴ * V * Φ)).mulVecLin,
        l2Norm ((Ψᴴ * V * Φ)ᴴ *ᵥ y) ≤ C' * Real.sqrt (A * d / W) * Real.log W * l2Norm y :=
      fun y hy => not_lt.1 fun hlt => hT₀ω ⟨y, hy, hlt⟩
    have hE2 : ‖(E : ℂ)‖ ≤ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      linarith
    have hcore := invImageRange_core hB₀ hQH hQI hQB hBs hB₁n hQP hE2 hε₀h hCT hCK hC' hA hCTs hL1
      hK₁ hCge hPqH hPqv hQPq hQc hQB₁c hcPu hΨ hΦΦ hΨΨ hΨΦ hΦn hΨn hQn hQcn rfl rfl hVH hVn hSKω
      hΓcu hY hx1
    exact absurd hx2 (not_lt.2 hcore)
  -- the failure probabilities
  have hWD : (W : ℝ) ^ (-(D + 1)) ≤ (W : ℝ) ^ (-D) / 2 := by
    rw [show -(D + 1) = -D + -1 by ring, Real.rpow_add hWpos, Real.rpow_neg_one]
    have h1 : (W : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div, div_le_div_iff₀ hWpos (by norm_num)]
      linarith
    have h2 : 0 ≤ (W : ℝ) ^ (-D) := (Real.rpow_pos_of_pos hWpos _).le
    calc (W : ℝ) ^ (-D) * (W : ℝ)⁻¹ ≤ (W : ℝ) ^ (-D) * (1 / 2) := mul_le_mul_of_nonneg_left h1 h2
      _ = (W : ℝ) ^ (-D) / 2 := by ring
  have he1 : Real.exp (-(cK * d)) ≤ Real.exp (-(c * d)) :=
    Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right hccK hdpos.le))
  have he2 : Real.exp (-(W : ℝ) / 2) ≤ Real.exp (-(c * d)) := by
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_right hch hdpos.le
    linarith
  have he3 : Real.exp (-(c' * d)) ≤ Real.exp (-(c * d)) :=
    Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right hcc' hdpos.le))
  have hE0 := Real.exp_pos (-(c * d))
  have key : ∀ a₁ a₂ a₃ a₄ : ℝ, 0 ≤ a₁ → 0 ≤ a₂ → 0 ≤ a₃ → 0 ≤ a₄ →
      ENNReal.ofReal a₁ + ENNReal.ofReal a₂ + ENNReal.ofReal a₃ + ENNReal.ofReal a₄ =
        ENNReal.ofReal (a₁ + a₂ + a₃ + a₄) := by
    intro a₁ a₂ a₃ a₄ h₁ h₂ h₃ h₄
    rw [ENNReal.ofReal_add (add_nonneg (add_nonneg h₁ h₂) h₃) h₄,
      ENNReal.ofReal_add (add_nonneg h₁ h₂) h₃, ENNReal.ofReal_add h₁ h₂]
  refine (measure_mono hsub).trans ?_
  calc μ W 1 (SK ∪ SV ∪ SS ∪ t ⁻¹' (Set.univ ×ˢ T))
      ≤ μ W 1 SK + μ W 1 SV + μ W 1 SS + μ W 1 (t ⁻¹' (Set.univ ×ˢ T)) :=
        (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
          (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 1)) + CK * Real.exp (-(cK * d))) +
          ENNReal.ofReal (Real.exp (-(W : ℝ) / 2)) + ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) +
          ENNReal.ofReal (C' * Real.exp (-(c' * d))) :=
        add_le_add (add_le_add (add_le_add hSK hSV) hSS) hSG
    _ = ENNReal.ofReal ((W : ℝ) ^ (-(D + 1)) + CK * Real.exp (-(cK * d)) +
          Real.exp (-(W : ℝ) / 2) + (W : ℝ) ^ (-(D + 1)) + C' * Real.exp (-(c' * d))) :=
        key _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity)
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-D) + C * Real.exp (-(c * d))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : CK * Real.exp (-(cK * d)) ≤ CK * Real.exp (-(c * d)) :=
          mul_le_mul_of_nonneg_left he1 hCK.le
        have h3 : C' * Real.exp (-(c' * d)) ≤ C' * Real.exp (-(c * d)) :=
          mul_le_mul_of_nonneg_left he3 hC'.le
        have h4 : (CK + 1 + C') * Real.exp (-(c * d)) ≤ C * Real.exp (-(c * d)) := by
          refine mul_le_mul_of_nonneg_right ?_ hE0.le
          rw [hCdef]
          nlinarith only [sq_nonneg CK, sq_nonneg K₁]
        linarith only [h1, h3, h4, hWD, he2]

end LSBA
