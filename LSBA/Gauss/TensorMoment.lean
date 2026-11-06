import LSBA.Gauss.PairingMoment

/-!
# Conditional trace moments of GUE tensor sums

For `m` independent GUE blocks `G_j` with the covariance (1.2) [eq:covariance] and deterministic
Hermitian `D_j` of size `W'`: `𝔼 Tr(Σ_j G_j ⊗ D_j)^{2p} ≤ W' · 𝔼 Tr G^{2p} · ‖Σ_j D_j²‖^p`, from
the pairing expansion and the per-pairing bound; and `‖X‖^{2p} ≤ Tr X^{2p}` for Hermitian `X`.
These give the tensor bound replacing (G.15) [cg:eq:freebounds] in Appendix G.4
[app:compact-gaussian].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Words in a sum of matrices and in Kronecker products -/

/-- Noncommutative expansion: `(Σ_a A_a)^n = Σ_{j : Fin n → Fin m} A_{j_0} ⋯ A_{j_{n-1}}`. -/
private lemma TensorMoment_sum_pow {R : Type*} [Semiring R] {m : ℕ} (A : Fin m → R) (n : ℕ) :
    (∑ a, A a) ^ n = ∑ j : Fin n → Fin m, (List.ofFn fun i => A (j i)).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ih, Finset.sum_mul_sum, ← (Fin.consEquiv fun _ => Fin m).sum_comp,
      Fintype.sum_prod_type]
    simp [List.ofFn_succ]

/-- Mixed-product rule for words: `∏ (G_i ⊗ D_i) = (∏ G_i) ⊗ (∏ D_i)`. -/
private lemma TensorMoment_prod_kron {W W' n : ℕ} (G : Fin n → Matrix (Fin W) (Fin W) ℂ)
    (D : Fin n → Matrix (Fin W') (Fin W') ℂ) :
    (List.ofFn fun i => G i ⊗ₖ D i).prod = (List.ofFn G).prod ⊗ₖ (List.ofFn D).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons,
      List.prod_cons, ih (fun i => G i.succ) (fun i => D i.succ), Matrix.mul_kronecker_mul]

/-- An entry is bounded by the operator norm. -/
private lemma TensorMoment_norm_entry_le {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (i j : n) : ‖M i j‖ ≤ ‖M‖ := by
  have h := Matrix.l2_opNorm_mulVec M (EuclideanSpace.single j (1 : ℂ))
  have hn : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  rw [hn, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le ((EuclideanSpace.equiv n ℂ).symm
    (M.mulVec (EuclideanSpace.single j (1 : ℂ)).ofLp)) i
  convert this using 2
  simp

/-- `Re Tr M ≤ W' ‖M‖` for a matrix of size `W'`. -/
private lemma TensorMoment_re_trace_le {W' : ℕ} (M : Matrix (Fin W') (Fin W') ℂ) :
    (M.trace).re ≤ W' * ‖M‖ := by
  rw [Matrix.trace, Complex.re_sum]
  calc ∑ i, (M.diag i).re ≤ ∑ _i : Fin W', ‖M‖ :=
        Finset.sum_le_sum fun i _ =>
          (Complex.re_le_norm _).trans (TensorMoment_norm_entry_le M i i)
    _ = W' * ‖M‖ := by simp

/-! ### Integrability of the traces of GUE words -/

private lemma TensorMoment_integrable_poly (ι : Type*) [Fintype ι] (m : ℕ) :
    Integrable (fun x : ι → ℝ => (1 + ‖x‖) ^ m) (stdGauss ι) := by
  have hpow1 : Integrable (fun x : ℝ => (1 + |x|) ^ m) (gaussianReal 0 1) := by
    have hm : MemLp id (m : ENNReal) (gaussianReal (0 : ℝ) 1) :=
      memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := 1) m (ENNReal.natCast_ne_top m)
    have hm' : MemLp id (m : ℕ) (gaussianReal (0 : ℝ) 1) := by simpa using hm
    have h1 : Integrable (fun x : ℝ => ‖id x‖ ^ m) (gaussianReal 0 1) :=
      hm'.integrable_norm_pow'
    have h2 : Integrable (fun x : ℝ => (2 : ℝ) ^ m * (1 + |x| ^ m)) (gaussianReal 0 1) :=
      ((integrable_const (1 : ℝ)).add (by simpa using h1)).const_mul _
    refine h2.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (by fun_prop : Continuous fun x : ℝ => (1 + |x|) ^ m).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity)]
      have h2m : (0 : ℝ) ≤ 2 ^ m := by positivity
      have hx : (0 : ℝ) ≤ |x| ^ m := by positivity
      rcases le_total |x| 1 with h | h
      · calc (1 + |x|) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
          _ ≤ 2 ^ m * (1 + |x| ^ m) := by nlinarith
      · calc (1 + |x|) ^ m ≤ (2 * |x|) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
          _ = 2 ^ m * |x| ^ m := by rw [mul_pow]
          _ ≤ 2 ^ m * (1 + |x| ^ m) := by nlinarith
  have hprod : Integrable (fun x : ι → ℝ => ∏ j, (1 + |x j|) ^ m) (stdGauss ι) :=
    Integrable.fintype_prod (f := fun _ (t : ℝ) => (1 + |t|) ^ m) (fun _ => hpow1)
  refine hprod.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (by fun_prop : Continuous fun x : ι → ℝ => (1 + ‖x‖) ^ m).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity), Finset.prod_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ m
    have hone : ∀ s : Finset ι, (1 : ℝ) ≤ ∏ l ∈ s, (1 + |x l|) := fun s =>
      Finset.one_le_prod₀ fun l _ => by linarith [abs_nonneg (x l)]
    have : ‖x‖ ≤ (∏ j, (1 + |x j|)) - 1 := by
      refine (pi_norm_le_iff_of_nonneg (by linarith [hone Finset.univ])).mpr fun j => ?_
      have hj : 1 + |x j| ≤ ∏ l, (1 + |x l|) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
        exact le_mul_of_one_le_right (by positivity) (hone _)
      rw [Real.norm_eq_abs]
      linarith
    linarith

private lemma TensorMoment_norm_gueBlock_entry_le (W m : ℕ) (ω : Ω W m) (a : Fin m)
    (α β : Fin W) : ‖gueBlock W m ω a α β‖ ≤ 2 * (1 + ‖ω‖) := by
  have hW : (1 : ℝ) ≤ W := by exact_mod_cast Fin.pos α
  have h1 : 1 ≤ Real.sqrt W := Real.one_le_sqrt.2 hW
  have h2 : 1 ≤ Real.sqrt (2 * W) := Real.one_le_sqrt.2 (by linarith)
  have hc : ∀ c, |ω c| ≤ ‖ω‖ := fun c => by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm ω c
  have hdiv : ∀ (z : ℂ) (r : ℝ), 1 ≤ r → ‖z / (r : ℂ)‖ ≤ ‖z‖ := fun z r hr => by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    exact div_le_self (norm_nonneg _) hr
  have hn : 0 ≤ ‖ω‖ := norm_nonneg ω
  simp only [gueBlock, Matrix.of_apply]
  split_ifs
  · refine (hdiv _ _ h1).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith [hc (a, α, α)]
  · refine (hdiv _ _ h2).trans ?_
    calc ‖(ω (a, α, β) : ℂ) + Complex.I * ω (a, β, α)‖
        ≤ ‖(ω (a, α, β) : ℂ)‖ + ‖Complex.I * ω (a, β, α)‖ := norm_add_le _ _
      _ = |ω (a, α, β)| + |ω (a, β, α)| := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 2 * (1 + ‖ω‖) := by linarith [hc (a, α, β), hc (a, β, α)]
  · refine (hdiv _ _ h2).trans ?_
    calc ‖(ω (a, β, α) : ℂ) - Complex.I * ω (a, α, β)‖
        ≤ ‖(ω (a, β, α) : ℂ)‖ + ‖Complex.I * ω (a, α, β)‖ := norm_sub_le _ _
      _ = |ω (a, β, α)| + |ω (a, α, β)| := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 2 * (1 + ‖ω‖) := by linarith [hc (a, α, β), hc (a, β, α)]

private lemma TensorMoment_integrable_prod (W m n : ℕ) (j : Fin n → Fin m)
    (p q : Fin n → Fin W) :
    Integrable (fun ω => ∏ i, gueBlock W m ω (j i) (p i) (q i)) (μ W m) := by
  have hcont : Continuous fun ω : Ω W m => ∏ i, gueBlock W m ω (j i) (p i) (q i) := by
    refine continuous_finsetProd _ fun i _ => ?_
    simp only [gueBlock, Matrix.of_apply]
    split_ifs <;> fun_prop
  rw [μ_eq_stdGauss]
  refine ((TensorMoment_integrable_poly _ n).const_mul (2 ^ n)).mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [norm_prod]
  calc ∏ i, ‖gueBlock W m ω (j i) (p i) (q i)‖ ≤ ∏ _i : Fin n, 2 * (1 + ‖ω‖) :=
        Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
          (fun i _ => TensorMoment_norm_gueBlock_entry_le W m ω _ _ _)
    _ = 2 ^ n * (1 + ‖ω‖) ^ n := by simp [Finset.prod_const, mul_pow]

/-- Entries of a product of `k + 1` matrices as a sum over the `k` intermediate indices. -/
private lemma TensorMoment_prod_apply (W k : ℕ) (M : Fin (k + 1) → Matrix (Fin W) (Fin W) ℂ)
    (α β : Fin W) :
    (List.ofFn M).prod α β = ∑ b : Fin k → Fin W,
      ∏ i, M i ((Fin.cons α b : Fin (k + 1) → Fin W) i)
        ((Fin.snoc b β : Fin (k + 1) → Fin W) i) := by
  induction k generalizing α with
  | zero => simp [List.ofFn_succ, Fin.snoc]
  | succ k ih =>
    rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
    simp_rw [ih (fun i => M i.succ)]
    rw [← (Fin.consEquiv fun _ => Fin W).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Fin.prod_univ_succ (n := k + 1)]
    simp only [Fin.consEquiv_apply, ← Fin.cons_snoc_eq_snoc_cons, Fin.cons_zero, Fin.cons_succ]

/-- The trace of a product of `k + 1` matrices as a sum over closed index paths. -/
private lemma TensorMoment_trace_prod (W k : ℕ) (M : Fin (k + 1) → Matrix (Fin W) (Fin W) ℂ) :
    ((List.ofFn M).prod).trace = ∑ a : Fin W × (Fin k → Fin W),
      ∏ i, M i ((Fin.cons a.1 a.2 : Fin (k + 1) → Fin W) i)
        ((Fin.snoc a.2 a.1 : Fin (k + 1) → Fin W) i) := by
  rw [Matrix.trace, Fintype.sum_prod_type]
  simp only [Matrix.diag, TensorMoment_prod_apply]

/-- The trace of a word in GUE blocks is integrable. -/
private lemma TensorMoment_integrable_trace (W m n : ℕ) (j : Fin n → Fin m) :
    Integrable (fun ω => ((List.ofFn fun i => gueBlock W m ω (j i)).prod).trace) (μ W m) := by
  cases n with
  | zero => simp
  | succ k =>
    simp_rw [TensorMoment_trace_prod]
    exact integrable_finsetSum _ fun a _ => TensorMoment_integrable_prod W m (k + 1) j _ _

/-- The trace of a power of a Hermitian matrix is the sum of the powers of its eigenvalues. -/
private lemma TensorMoment_trace_pow_eq {k : Type*} [Fintype k] [DecidableEq k] {X : Matrix k k ℂ}
    (hX : X.IsHermitian) (n : ℕ) :
    (X ^ n).trace = ∑ i, ((hX.eigenvalues i ^ n : ℝ) : ℂ) := by
  conv_lhs => rw [hX.spectral_theorem, ← map_pow, Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.diagonal_pow,
    Matrix.trace_diagonal]
  simp

/-- Conditional tensor moment, (1.2) [eq:covariance]: for Hermitian `D_j` of size `W'`,
`Re 𝔼 Tr(Σ_j G_j ⊗ D_j)^{2p} ≤ W' · Re 𝔼 Tr G^{2p} · ‖Σ_j D_j²‖^p`. -/
theorem trace_pow_kron_gueBlock_le (W m p : ℕ) {W' : ℕ} (D : Fin m → Matrix (Fin W') (Fin W') ℂ)
    (hD : ∀ a, (D a).IsHermitian) :
    (∫ ω, ((∑ j, gueBlock W m ω j ⊗ₖ D j) ^ (2 * p)).trace ∂(μ W m)).re ≤
      W' * (∫ ω, ((gueBlock W 1 ω 0) ^ (2 * p)).trace ∂(μ W 1)).re *
        ‖∑ j, D j * D j‖ ^ p := by
  have hexp : ∀ ω, ((∑ j, gueBlock W m ω j ⊗ₖ D j) ^ (2 * p)).trace =
      ∑ j : Fin (2 * p) → Fin m, ((List.ofFn fun i => gueBlock W m ω (j i)).prod).trace *
        ((List.ofFn fun i => D (j i)).prod).trace := by
    intro ω
    rw [TensorMoment_sum_pow, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorMoment_prod_kron, Matrix.trace_kronecker]
  simp_rw [hexp]
  rw [integral_finsetSum _ fun j _ => (TensorMoment_integrable_trace W m _ j).mul_const _]
  simp_rw [integral_mul_const, integral_trace_prod_gueBlock]
  have hswap : ∑ j : Fin (2 * p) → Fin m,
      (∑ σ ∈ (pairings (2 * p)).filter (fun σ => ∀ i, j (σ i) = j i), pairWeight W σ) *
        ((List.ofFn fun i => D (j i)).prod).trace =
      ∑ σ ∈ pairings (2 * p), pairWeight W σ *
        (∑ j ∈ (Finset.univ : Finset (Fin (2 * p) → Fin m)).filter
          (fun j => ∀ i, j (σ i) = j i), (List.ofFn fun i => D (j i)).prod).trace := by
    simp_rw [Finset.sum_mul, Matrix.trace_sum, Finset.mul_sum]
    refine Finset.sum_comm' fun j σ => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hR : (∫ ω, ((gueBlock W 1 ω 0) ^ (2 * p)).trace ∂(μ W 1)) =
      ∑ σ ∈ pairings (2 * p), pairWeight W σ := by
    have := integral_trace_prod_gueBlock W 1 (2 * p) (fun _ => 0)
    simpa [List.ofFn_const, List.prod_replicate] using this
  rw [hswap, hR, Complex.re_sum, Complex.re_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun σ hσ => ?_
  obtain ⟨h0, h1⟩ := pairWeight_nonneg W hσ
  rw [Complex.mul_re, h1, zero_mul, sub_zero]
  calc (pairWeight W σ).re * _ ≤ (pairWeight W σ).re * (W' * ‖∑ j, D j * D j‖ ^ p) :=
        mul_le_mul_of_nonneg_left ((TensorMoment_re_trace_le _).trans
          (mul_le_mul_of_nonneg_left (norm_sum_pairing_prod_le D hD hσ)
            (Nat.cast_nonneg _))) h0
    _ = _ := by ring

/-- `‖X‖^{2p} ≤ Re Tr X^{2p}` for a Hermitian matrix `X` and `p ≥ 1` (operator norm). -/
theorem norm_pow_le_trace_pow {k : Type*} [Fintype k] [DecidableEq k] {X : Matrix k k ℂ}
    (hX : X.IsHermitian) {p : ℕ} (hp : 1 ≤ p) : ‖X‖ ^ (2 * p) ≤ ((X ^ (2 * p)).trace).re := by
  rw [TensorMoment_trace_pow_eq hX, Complex.re_sum]
  simp only [Complex.ofReal_re]
  rcases isEmpty_or_nonempty k with hk | hk
  · have : X = 0 := Subsingleton.elim _ _
    subst this
    simp [zero_pow (by omega : 2 * p ≠ 0)]
  · have hsa : IsSelfAdjoint X := hX
    obtain ⟨z, hz, hzr⟩ := spectrum.exists_nnnorm_eq_spectralRadius X
    rw [hsa.spectralRadius_eq_nnnorm] at hzr
    rw [hX.spectrum_eq_image_range] at hz
    obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := hz
    have h1 : ‖X‖ = |hX.eigenvalues i| := by
      have := congrArg (fun r : NNReal => (r : ℝ)) (ENNReal.coe_inj.1 hzr)
      simpa using this.symm
    rw [h1, pow_mul, sq_abs, ← pow_mul]
    exact Finset.single_le_sum (f := fun i => hX.eigenvalues i ^ (2 * p))
      (fun j _ => by rw [pow_mul]; positivity) (Finset.mem_univ i)

end LSBA
