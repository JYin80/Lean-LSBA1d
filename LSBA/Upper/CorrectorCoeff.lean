import LSBA.Upper.CenterCenters
import LSBA.Analysis.PolyEvalBound

/-!
# The coefficient equation of the corrector

The objects of (11.62) [lg:eq:corrector-linear-expansions] and (11.63) [lg:eq:Q-coefficients]:
the expansion of the mean increment `P_g c` through order `g^{−2R−4}` in the original
coordinates, and in the corrected coordinates after the inverse substitution `m^{[R+2]}(M)`,
`f^{[R+2]}(M, F)`; the substitution `M = a`, `W⁻¹ = 0`, `γ = g⁻²`, and the coefficient `[F_k]` of
exactly one factor `F_k`; the vector `b_k` and the matrix `A_{kr}` of (11.63)
[lg:eq:Q-coefficients], and the matrix
`A_0` of the orders `1` and `g⁻²`. Properties: the expansion of `P_g c` in the corrected
coordinates with remainder `O(g^{−2R−6})`, the absence of `F`-free `W⁰` terms, and the finite
supports of `b` and of the columns of `A`, `A_0`.
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `Σ_{r ≤ R+2} h_θ^{2r} γ^r c_r`, the expansion of `P_g c` through order `g^{−2R−4}` in the
original coordinates (continuing (11.12) [lg:eq:c2]). -/
def incPoly (E : ℝ) (R : ℕ) : ObsPoly :=
  ∑ r ∈ Finset.range (R + 3), C (((normalH E ^ (2 * r) : ℝ) : ℂ)) * X .γ ^ r * incWick r

/-- The expansion of `P_g c` in the corrected coordinates, truncated after `γ^{R+2}`
((11.62) [lg:eq:corrector-linear-expansions]). -/
def incCorr (E : ℝ) (R : ℕ) : ObsPoly := truncG (R + 2) (bind₁ (invCoord E R) (incPoly E R))

/-- The substitution `m_j ↦ a_j`, `w ↦ 0`, `γ ↦ g⁻²`, `f_j ↦ f_j`. -/
def centerSub (g : ℝ) (a : ℤ → ℂ) : ObsPoly →ₐ[ℂ] ObsPoly :=
  aeval fun v => match v with
    | .m k => C (a k.1)
    | .f k => X (.f k)
    | .w => 0
    | .γ => C (((g ^ 2)⁻¹ : ℝ) : ℂ)

/-- `[F_k] p|_{M = a}`: the coefficient of exactly one factor `F_k` and no other `F_j` in the
`W⁰` part of `p` at `M = a`, `γ = g⁻²` ((11.63) [lg:eq:Q-coefficients]). -/
def linCoeff (g : ℝ) (a : ℤ → ℂ) (k : NzInt) (p : ObsPoly) : ℂ :=
  (centerSub g a p).coeff (Finsupp.single (.f k) 1)

/-- The vector `b_k` of (11.63) [lg:eq:Q-coefficients]. -/
def driftCoeff (g E : ℝ) (R : ℕ) (k : NzInt) : ℂ := linCoeff g (center g E R) k (incCorr E R)

/-- The matrix `A_{kr}` of (11.63) [lg:eq:Q-coefficients]. -/
def corrMat (g E : ℝ) (R : ℕ) (k r : NzInt) : ℂ :=
  linCoeff g (center g E R) k (corrUpd E R (.f r) - X (.f r))

/-- The matrix `A_0` of the orders `1` and `g⁻²` of `A` (Section 11.3.4
[lg:sec:cocycle-correction]). -/
def corrMat0 (g E : ℝ) (R : ℕ) (k r : NzInt) : ℂ :=
  linCoeff g (center g E R) k (truncG 1 (corrUpd E R (.f r)) - X (.f r))

/-! ### A weighted `ℓ¹` norm of polynomials -/

/-- The weight `∏_v ρ_v^{d_v}` of a monomial `d`. -/
private def ccfWt {σ : Type*} (ρ : σ → ℝ) (d : σ →₀ ℕ) : ℝ := d.prod fun v n => ρ v ^ n

/-- The weighted `ℓ¹` norm `Σ_d |p_d| ρ^d` of a polynomial. -/
private def ccfNorm {σ : Type*} (ρ : σ → ℝ) (p : MvPolynomial σ ℂ) : ℝ :=
  ∑ d ∈ p.support, ‖p.coeff d‖ * ccfWt ρ d

private lemma ccfWt_nonneg {σ : Type*} {ρ : σ → ℝ} (hρ : ∀ v, 0 ≤ ρ v) (d : σ →₀ ℕ) :
    0 ≤ ccfWt ρ d :=
  Finset.prod_nonneg fun v _ => pow_nonneg (hρ v) _

private lemma ccfWt_add {σ : Type*} (ρ : σ → ℝ) (a b : σ →₀ ℕ) :
    ccfWt ρ (a + b) = ccfWt ρ a * ccfWt ρ b :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) fun _ _ _ => pow_add _ _ _

private lemma ccfWt_zero {σ : Type*} (ρ : σ → ℝ) : ccfWt ρ 0 = 1 :=
  Finsupp.prod_zero_index

private lemma ccfWt_single {σ : Type*} (ρ : σ → ℝ) (v : σ) :
    ccfWt ρ (Finsupp.single v 1) = ρ v := by
  unfold ccfWt
  rw [Finsupp.prod_single_index (by rw [pow_zero]), pow_one]

private lemma ccfWt_const {σ : Type*} (B : ℝ) (d : σ →₀ ℕ) :
    ccfWt (fun _ => B) d = B ^ Finsupp.degree d := by
  unfold ccfWt
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]

private lemma ccfNorm_eq {σ : Type*} (ρ : σ → ℝ) {p : MvPolynomial σ ℂ} {T : Finset (σ →₀ ℕ)}
    (hT : p.support ⊆ T) : ccfNorm ρ p = ∑ d ∈ T, ‖p.coeff d‖ * ccfWt ρ d := by
  unfold ccfNorm
  refine Finset.sum_subset hT fun d _ hd => ?_
  rw [notMem_support_iff.mp hd, norm_zero, zero_mul]

private lemma ccfNorm_nonneg {σ : Type*} {ρ : σ → ℝ} (hρ : ∀ v, 0 ≤ ρ v)
    (p : MvPolynomial σ ℂ) : 0 ≤ ccfNorm ρ p :=
  Finset.sum_nonneg fun d _ => mul_nonneg (norm_nonneg _) (ccfWt_nonneg hρ d)

private lemma ccfNorm_add_le {σ : Type*} {ρ : σ → ℝ} (hρ : ∀ v, 0 ≤ ρ v)
    (p q : MvPolynomial σ ℂ) : ccfNorm ρ (p + q) ≤ ccfNorm ρ p + ccfNorm ρ q := by
  classical
  rw [ccfNorm_eq ρ (support_add (p := p) (q := q)),
    ccfNorm_eq ρ (Finset.subset_union_left (s₁ := p.support) (s₂ := q.support)),
    ccfNorm_eq ρ (Finset.subset_union_right (s₁ := p.support) (s₂ := q.support)),
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun d _ => ?_
  rw [show (p + q).coeff d = p.coeff d + q.coeff d by simp, ← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (ccfWt_nonneg hρ d)

private lemma ccfNorm_sum_le {σ ι : Type*} {ρ : σ → ℝ} (hρ : ∀ v, 0 ≤ ρ v) (s : Finset ι)
    (f : ι → MvPolynomial σ ℂ) : ccfNorm ρ (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ccfNorm ρ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ccfNorm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (ccfNorm_add_le hρ _ _).trans (add_le_add le_rfl ih)

private lemma ccfNorm_monomial {σ : Type*} (ρ : σ → ℝ) (e : σ →₀ ℕ) (c : ℂ) :
    ccfNorm ρ (monomial e c) = ‖c‖ * ccfWt ρ e := by
  rw [ccfNorm_eq ρ support_monomial_subset, Finset.sum_singleton]
  simp [coeff_monomial]

private lemma ccfNorm_C {σ : Type*} (ρ : σ → ℝ) (c : ℂ) :
    ccfNorm ρ (C c : MvPolynomial σ ℂ) = ‖c‖ := by
  rw [C_apply, ccfNorm_monomial, ccfWt_zero, mul_one]

private lemma ccfNorm_X {σ : Type*} (ρ : σ → ℝ) (v : σ) :
    ccfNorm ρ (X v : MvPolynomial σ ℂ) = ρ v := by
  rw [X, ccfNorm_monomial, ccfWt_single, norm_one, one_mul]

private lemma ccfNorm_mul_le {σ : Type*} {ρ : σ → ℝ} (hρ : ∀ v, 0 ≤ ρ v)
    (p q : MvPolynomial σ ℂ) : ccfNorm ρ (p * q) ≤ ccfNorm ρ p * ccfNorm ρ q := by
  have h : p * q = ∑ a ∈ p.support, ∑ b ∈ q.support,
      monomial (a + b) (p.coeff a * q.coeff b) := by
    conv_lhs => rw [p.as_sum, q.as_sum]
    rw [Finset.sum_mul_sum]
    simp only [monomial_mul_monomial]
  rw [h]
  refine (ccfNorm_sum_le hρ _ _).trans ?_
  unfold ccfNorm
  rw [Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun a _ => (ccfNorm_sum_le hρ _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ccfNorm_monomial, norm_mul, ccfWt_add]
  ring

private lemma ccfNorm_one {σ : Type*} (ρ : σ → ℝ) : ccfNorm ρ (1 : MvPolynomial σ ℂ) = 1 := by
  rw [← C_1, ccfNorm_C, norm_one]

private lemma ccfNorm_pow_le {σ : Type*} {ρ : σ → ℝ} (hρ : ∀ v, 0 ≤ ρ v)
    (p : MvPolynomial σ ℂ) (n : ℕ) : ccfNorm ρ (p ^ n) ≤ ccfNorm ρ p ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, ccfNorm_one]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (ccfNorm_mul_le hρ _ _).trans
      (mul_le_mul_of_nonneg_right ih (ccfNorm_nonneg hρ p))

private lemma ccfNorm_prod_le {σ ι : Type*} {ρ : σ → ℝ} (hρ : ∀ v, 0 ≤ ρ v) (s : Finset ι)
    (f : ι → MvPolynomial σ ℂ) : ccfNorm ρ (∏ i ∈ s, f i) ≤ ∏ i ∈ s, ccfNorm ρ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, ccfNorm_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (ccfNorm_mul_le hρ _ _).trans
      (mul_le_mul_of_nonneg_left ih (ccfNorm_nonneg hρ _))

/-- Composition: `‖p(ψ)‖_ρ ≤ ‖p‖_{ρ'}` when `‖ψ_v‖_ρ ≤ ρ'_v` on the variables of `p`. -/
private lemma ccfNorm_bind₁_le {σ τ : Type*} {ρ : τ → ℝ} {ρ' : σ → ℝ} (hρ : ∀ v, 0 ≤ ρ v)
    (ψ : σ → MvPolynomial τ ℂ) (p : MvPolynomial σ ℂ)
    (h : ∀ v ∈ p.vars, ccfNorm ρ (ψ v) ≤ ρ' v) : ccfNorm ρ (bind₁ ψ p) ≤ ccfNorm ρ' p := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine (ccfNorm_sum_le hρ _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  rw [bind₁_monomial]
  refine (ccfNorm_mul_le hρ _ _).trans ?_
  rw [ccfNorm_C]
  refine mul_le_mul_of_nonneg_left ((ccfNorm_prod_le hρ _ _).trans ?_) (norm_nonneg _)
  refine Finset.prod_le_prod₀ (fun v _ => ccfNorm_nonneg hρ _) fun v hv => ?_
  have hvar : v ∈ p.vars := (mem_vars_iff_mem_support v).2 ⟨d, hd, hv⟩
  exact (ccfNorm_pow_le hρ _ _).trans
    (pow_le_pow_left₀ (ccfNorm_nonneg hρ _) (h v hvar) _)

/-- Evaluation: `|p(x)| ≤ ‖p‖_ρ` when `|x_v| ≤ ρ_v` on the variables of `p`. -/
private lemma ccf_norm_aeval_le {σ : Type*} {ρ : σ → ℝ} (p : MvPolynomial σ ℂ) {x : σ → ℂ}
    (hx : ∀ v ∈ p.vars, ‖x v‖ ≤ ρ v) : ‖aeval x p‖ ≤ ccfNorm ρ p := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  rw [aeval_monomial, Algebra.algebraMap_self, RingHom.id_apply, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [Finsupp.prod, norm_prod]
  refine Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v hv => ?_
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hx v ((mem_vars_iff_mem_support v).2 ⟨d, hd, hv⟩)) _

/-- Coefficientwise domination. -/
private lemma ccfNorm_mono {σ : Type*} {ρ : σ → ℝ} (hρ : ∀ v, 0 ≤ ρ v) {p q : MvPolynomial σ ℂ}
    (h : ∀ d, ‖q.coeff d‖ ≤ ‖p.coeff d‖) : ccfNorm ρ q ≤ ccfNorm ρ p := by
  have hs : q.support ⊆ p.support := fun d hd => by
    rw [mem_support_iff] at hd ⊢
    intro h0
    have := h d
    rw [h0, norm_zero] at this
    exact hd (norm_le_zero_iff.mp this)
  rw [ccfNorm_eq ρ hs]
  exact Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_right (h d) (ccfWt_nonneg hρ d)

/-- A bound from a support and a coefficient bound. -/
private lemma ccfNorm_le_of_support {σ : Type*} {ρ : σ → ℝ} (hρ : ∀ v, 0 ≤ ρ v)
    {p : MvPolynomial σ ℂ} {S : Finset (σ →₀ ℕ)} {K : ℝ} (hS : p.support ⊆ S)
    (hK : ∀ d, ‖p.coeff d‖ ≤ K) : ccfNorm ρ p ≤ ∑ d ∈ S, K * ccfWt ρ d := by
  rw [ccfNorm_eq ρ hS]
  exact Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_right (hK d) (ccfWt_nonneg hρ d)

/-! ### Truncation, the `W⁰` part and the fixed variables `w`, `γ` -/

private lemma ccf_coeff_truncG (N : ℕ) (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (truncG N p).coeff d = if d .γ ≤ N then p.coeff d else 0 := by
  have hw : Finsupp.weight ObsVar.gamWt d = d .γ := by
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_single ObsVar.γ]
    · simp [ObsVar.gamWt]
    · intro b _ hb
      cases b <;> simp_all [ObsVar.gamWt]
    · intro h
      simp [Finsupp.notMem_support_iff.mp h]
  unfold truncG
  rw [LinearMap.sum_apply, MvPolynomial.coeff_sum]
  simp only [coeff_weightedHomogeneousComponent, hw]
  rw [Finset.sum_ite_eq]
  simp

private lemma ccf_support_truncG (N : ℕ) (p : ObsPoly) : (truncG N p).support ⊆ p.support := by
  intro d hd
  rw [mem_support_iff, ccf_coeff_truncG] at hd
  rw [mem_support_iff]
  split_ifs at hd
  · exact hd
  · exact absurd rfl hd

private lemma ccf_vars_truncG (N : ℕ) (p : ObsPoly) : (truncG N p).vars ⊆ p.vars := by
  intro v hv
  obtain ⟨d, hd, hv⟩ := (mem_vars_iff_mem_support v).1 hv
  exact (mem_vars_iff_mem_support v).2 ⟨d, ccf_support_truncG N p hd, hv⟩

private lemma ccf_truncG_X {N : ℕ} {v : ObsVar} (h : v.gamWt ≤ N) : truncG N (X v) = X v := by
  ext d
  rw [ccf_coeff_truncG]
  split_ifs with hd
  · rfl
  · rw [coeff_X]
    split_ifs with h2
    · exfalso
      subst h2
      cases v <;> simp_all [ObsVar.gamWt]
    · rfl

private lemma ccf_zeroW_monomial (d : ObsVar →₀ ℕ) (c : ℂ) :
    zeroW (monomial d c) = if d .w = 0 then monomial d c else 0 := by
  unfold zeroW
  rw [aeval_monomial]
  split_ifs with h
  · rw [monomial_eq, MvPolynomial.algebraMap_eq]
    congr 1
    refine Finsupp.prod_congr fun v hv => ?_
    have : v ≠ .w := by
      rintro rfl
      exact (Finsupp.mem_support_iff.mp hv) h
    simp only [this, ite_false]
  · rw [Finsupp.prod, Finset.prod_eq_zero (i := ObsVar.w) (Finsupp.mem_support_iff.mpr h)
      (by simp only [ite_true, zero_pow h]), mul_zero]

private lemma ccf_coeff_zeroW (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (zeroW p).coeff d = if d .w = 0 then p.coeff d else 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial e c =>
    rw [ccf_zeroW_monomial]
    by_cases he : e = d
    · subst he
      split_ifs <;> simp [coeff_monomial]
    · split_ifs <;> simp [coeff_monomial, he]
  | add p q hp hq =>
    rw [map_add, show ∀ a b : ObsPoly, (a + b).coeff d = a.coeff d + b.coeff d from
      fun a b => by simp, hp, hq]
    split_ifs <;> simp

private lemma ccf_zeroW_truncG (N : ℕ) (p : ObsPoly) :
    zeroW (truncG N p) = truncG N (zeroW p) := by
  ext d
  simp only [ccf_coeff_zeroW, ccf_coeff_truncG]
  split_ifs <;> rfl

private lemma ccf_corrCoord_w (E : ℝ) (R : ℕ) : corrCoord E R .w = X .w := rfl

private lemma ccf_corrCoord_γ (E : ℝ) (R : ℕ) : corrCoord E R .γ = X .γ := rfl

private lemma ccf_invCoord_w (E : ℝ) (R : ℕ) : invCoord E R .w = X .w := by
  rw [invCoord, revCoord]
  beta_reduce
  rw [ccf_corrCoord_w, sub_self, map_zero, sub_zero]
  exact ccf_truncG_X (by simp [ObsVar.gamWt])

private lemma ccf_invCoord_γ (E : ℝ) (R : ℕ) : invCoord E R .γ = X .γ := by
  rw [invCoord, revCoord]
  beta_reduce
  rw [ccf_corrCoord_γ, sub_self, map_zero, sub_zero]
  exact ccf_truncG_X (by simp [ObsVar.gamWt])

/-- `fIdeal` is the monomial ideal of the variables `f_k`. -/
private lemma ccf_mem_fIdeal_iff (p : ObsPoly) :
    p ∈ fIdeal ↔ ∀ d ∈ p.support, ∃ k : NzInt, d (.f k) ≠ 0 := by
  have h : fIdeal = Ideal.span (X '' Set.range ObsVar.f) := by
    unfold fIdeal
    rw [← Set.range_comp]
    rfl
  rw [h, mem_ideal_span_X_image]
  constructor
  · intro H d hd
    obtain ⟨_, ⟨k, rfl⟩, hk⟩ := H d hd
    exact ⟨k, hk⟩
  · intro H d hd
    obtain ⟨k, hk⟩ := H d hd
    exact ⟨_, ⟨k, rfl⟩, hk⟩

private lemma ccf_mem_fIdeal_of_support {p q : ObsPoly} (hp : p ∈ fIdeal)
    (h : q.support ⊆ p.support) : q ∈ fIdeal := by
  rw [ccf_mem_fIdeal_iff] at hp ⊢
  exact fun d hd => hp d (h hd)

private lemma ccf_support_zeroW (p : ObsPoly) : (zeroW p).support ⊆ p.support := by
  intro d hd
  rw [mem_support_iff, ccf_coeff_zeroW] at hd
  rw [mem_support_iff]
  split_ifs at hd
  · exact hd
  · exact absurd rfl hd

/-- `bind₁ ψ` maps `fIdeal` into itself when every `ψ(f_k)` lies in it. -/
private lemma ccf_bind₁_mem_fIdeal {ψ : ObsVar → ObsPoly} (hψ : ∀ k : NzInt, ψ (.f k) ∈ fIdeal)
    {p : ObsPoly} (hp : p ∈ fIdeal) : bind₁ ψ p ∈ fIdeal := by
  have hle : Ideal.map (bind₁ ψ) fIdeal ≤ fIdeal := by
    show Ideal.map (bind₁ ψ) (Ideal.span _) ≤ fIdeal
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    simpa using hψ k
  exact hle (Ideal.mem_map_of_mem _ hp)

/-- `h_θ ≤ 1` on `|E| ≤ 1`. -/
private lemma ccf_normalH {E : ℝ} (hE : |E| ≤ 1) : 0 ≤ normalH E ∧ normalH E ≤ 1 := by
  unfold normalH freeAngle
  rw [Real.sin_arccos]
  have h1 : (E / 2) ^ 2 ≤ 3 / 4 := by
    have := sq_abs E
    nlinarith [abs_nonneg E]
  have h2 : (1 / 2 : ℝ) ≤ √(1 - (E / 2) ^ 2) := by
    rw [show (1 / 2 : ℝ) = √((1 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  refine ⟨by positivity, inv_le_one_of_one_le₀ (by linarith)⟩

/-- The indices of `m_k`, `f_k`. -/
private def ccfIdx : ObsVar → Finset NzInt
  | .m k => {k}
  | .f k => {k}
  | .w => ∅
  | .γ => ∅

/-- The variables of `c_r`, `r ≤ R + 2`. -/
private def ccfV₀ (R : ℕ) : Finset ObsVar :=
  (Finset.range (R + 3)).biUnion fun r => (incWick r).vars

private lemma ccf_vars_incPoly (E : ℝ) (R : ℕ) : (incPoly E R).vars ⊆ insert .γ (ccfV₀ R) := by
  intro v hv
  have h := vars_sum_subset _ _ hv
  simp only [Finset.mem_biUnion] at h
  obtain ⟨r, hr, hv⟩ := h
  have h1 := vars_mul _ _ hv
  rw [Finset.mem_union] at h1
  rcases h1 with h1 | h1
  · have h2 := vars_mul _ _ h1
    rw [Finset.mem_union, vars_C] at h2
    rcases h2 with h2 | h2
    · simp at h2
    · have h3 := vars_pow _ _ h2
      rw [vars_X] at h3
      rw [Finset.mem_singleton] at h3
      rw [h3]
      exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨r, hr, h1⟩)

private lemma ccf_zeroW_X (v : ObsVar) : zeroW (X v) = if v = .w then 0 else X v := by
  simp [zeroW]

/-- `linCoeff` vanishes when `f_k` is not a variable. -/
private lemma ccf_linCoeff_eq_zero (g : ℝ) (a : ℤ → ℂ) {k : NzInt} {p : ObsPoly}
    (hk : ObsVar.f k ∉ p.vars) : linCoeff g a k p = 0 := by
  unfold linCoeff centerSub
  rw [aeval_eq_bind₁]
  by_contra h
  have hmem : ObsVar.f k ∈ (bind₁ (fun v : ObsVar => match v with
      | .m k => C (a k.1)
      | .f k => X (.f k)
      | .w => 0
      | .γ => C (((g ^ 2)⁻¹ : ℝ) : ℂ)) p).vars :=
    (mem_vars_iff_mem_support _).2 ⟨Finsupp.single (.f k) 1, mem_support_iff.mpr h, by simp⟩
  obtain ⟨v, hv, hv'⟩ := Finset.mem_biUnion.mp (vars_bind₁ _ p hmem)
  cases v with
  | m j => simp at hv'
  | f j =>
    obtain rfl : k = j := by simpa using hv'
    exact hk hv
  | w => simp at hv'
  | γ => simp at hv'

/-! ### Bounds for the expansion in the corrected coordinates -/

private lemma ccf_coeff_sub_truncG (N : ℕ) (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (p - truncG N p).coeff d = if d .γ ≤ N then 0 else p.coeff d := by
  rw [show (p - truncG N p).coeff d = p.coeff d - (truncG N p).coeff d by simp, ccf_coeff_truncG]
  split_ifs <;> simp

/-- The weight with `ρ_γ = t` and `ρ_v = B` otherwise splits off `t^{d_γ}`. -/
private lemma ccfWt_split (t B : ℝ) (d : ObsVar →₀ ℕ) :
    ccfWt (fun v => if v = .γ then t else B) d =
      t ^ (d .γ) * ccfWt (fun v => if v = .γ then 1 else B) d := by
  unfold ccfWt
  rw [Finsupp.prod, Finsupp.prod]
  have h : ∀ v, (if v = ObsVar.γ then t else B) ^ (d v) =
      t ^ (if v = ObsVar.γ then d v else 0) * (if v = ObsVar.γ then 1 else B) ^ (d v) := by
    intro v
    split_ifs <;> simp
  rw [Finset.prod_congr rfl fun v _ => h v, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.sum_ite_eq']
  split_ifs with hγ
  · rfl
  · rw [Finsupp.notMem_support_iff.mp hγ]

/-- `‖Σ_r h^{2r} γ^r c_r‖ ≤ Σ_r c^r ‖c_r‖` for the constant weight `c` on `|E| ≤ 1`. -/
private lemma ccf_norm_incPoly_le {E : ℝ} (hE : |E| ≤ 1) (R : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    ccfNorm (fun _ => c) (incPoly E R) ≤
      ∑ r ∈ Finset.range (R + 3), c ^ r * ccfNorm (fun _ => c) (incWick r) := by
  have hρ : ∀ _ : ObsVar, 0 ≤ c := fun _ => hc
  obtain ⟨hh0, hh1⟩ := ccf_normalH hE
  unfold incPoly
  refine (ccfNorm_sum_le hρ _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  refine (ccfNorm_mul_le hρ _ _).trans
    (mul_le_mul_of_nonneg_right ?_ (ccfNorm_nonneg hρ _))
  refine (ccfNorm_mul_le hρ _ _).trans ?_
  rw [ccfNorm_C]
  have h1 : ‖(((normalH E ^ (2 * r) : ℝ)) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hh0 _)]
    exact pow_le_one₀ hh0 hh1
  have h2 : ccfNorm (fun _ => c) (X ObsVar.γ ^ r : ObsPoly) ≤ c ^ r :=
    (ccfNorm_pow_le hρ _ _).trans (by rw [ccfNorm_X])
  calc ‖(((normalH E ^ (2 * r) : ℝ)) : ℂ)‖ * ccfNorm (fun _ => c) (X ObsVar.γ ^ r : ObsPoly)
      ≤ 1 * c ^ r := mul_le_mul h1 h2 (ccfNorm_nonneg hρ _) zero_le_one
    _ = c ^ r := one_mul _

private lemma ccf_lip_le {B : ℝ} (hB : 1 ≤ B) (p : ObsPoly) :
    ∑ d ∈ p.support, ‖p.coeff d‖ * Finsupp.degree d * B ^ (Finsupp.degree d - 1) ≤
      ccfNorm (fun _ => 2 * B) p := by
  unfold ccfNorm
  refine Finset.sum_le_sum fun d _ => ?_
  rw [ccfWt_const, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  set n := Finsupp.degree d
  have h1 : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
  have h2 : B ^ (n - 1) ≤ B ^ n := pow_le_pow_right₀ hB (Nat.sub_le n 1)
  rw [mul_pow]
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-- The obvious evaluation bounds on states: `|m_k|, |f_k|, W⁻¹, g⁻² ≤ 1`. -/
private lemma ccf_norm_obsEval_X_le {W : ℕ} (hW : 1 ≤ W) {g : ℝ} (hg : 1 ≤ g) {X : State W}
    (hX : IsState X) (v : ObsVar) : ‖obsEval g X (MvPolynomial.X v)‖ ≤ 1 := by
  have h := norm_obsEval_le hW hg hX (MvPolynomial.X v)
  rw [support_X, Finset.sum_singleton] at h
  simpa using h

/-- The expansion of `P_g c` in the corrected coordinates ((11.62)
[lg:eq:corrector-linear-expansions] before the extraction): on a window fixed after `R`,
`|P_g c − incCorr(M, F)| ≤ K g^{−2R−6}`, uniformly in `W ≥ 1`, `g ≥ 1` and the state. -/
theorem incMean_corr_sub_le (R : ℕ) :
    ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ K : ℝ, 0 < K ∧ ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ E₁ →
      ∀ X : State W, IsState X →
        ‖((incMean g E X : ℝ) : ℂ) - obsEval g X (bind₁ (corrCoord E R) (incCorr E R))‖ ≤
          K / g ^ (2 * R + 6) := by
  set Ks₀ : Finset NzInt := (ccfV₀ R).biUnion ccfIdx with hKs₀
  obtain ⟨E₂, hE₂, S₀, K₀, -, h₀⟩ := corrCoeff_bounded R Ks₀
  set Ks₁ : Finset NzInt := Ks₀ ∪ (S₀.biUnion fun d => d.support).biUnion ccfIdx with hKs₁
  obtain ⟨E₄, hE₄, K₄, hK₄, h₄⟩ := norm_obsEval_corrObs_sub_le R Ks₁
  obtain ⟨K₁, hK₁, h₁⟩ := incMean_sub_le (E₀ := 1) (by norm_num) (R + 2)
  set B : ℝ := 1 + K₄ with hB
  have hB1 : 1 ≤ B := by linarith
  have hB0 : 0 ≤ B := by linarith
  set ρ' : ObsVar → ℝ := fun v => if v = .γ then 1 else B with hρ'
  have hρ'0 : ∀ v, 0 ≤ ρ' v := fun v => by
    simp only [hρ']
    split_ifs <;> linarith
  set B₂ : ℝ := max B (∑ d ∈ S₀, K₀ * ccfWt ρ' d) with hB₂
  have hB₂0 : 0 ≤ B₂ := hB0.trans (le_max_left _ _)
  set L₀ : ℝ := ∑ r ∈ Finset.range (R + 3), (2 * B) ^ r * ccfNorm (fun _ => 2 * B) (incWick r)
    with hL₀
  set K₃ : ℝ := ∑ r ∈ Finset.range (R + 3), B₂ ^ r * ccfNorm (fun _ => B₂) (incWick r) with hK₃
  have hL₀0 : 0 ≤ L₀ := Finset.sum_nonneg fun r _ =>
    mul_nonneg (pow_nonneg (by linarith) _) (ccfNorm_nonneg (fun _ => by linarith) _)
  have hK₃0 : 0 ≤ K₃ := Finset.sum_nonneg fun r _ =>
    mul_nonneg (pow_nonneg hB₂0 _) (ccfNorm_nonneg (fun _ => hB₂0) _)
  refine ⟨min 1 (min E₂ E₄), lt_min one_pos (lt_min hE₂ hE₄), K₁ + L₀ * K₄ + K₃ + 1,
    by positivity, fun W hW g hg E hE X hX => ?_⟩
  have hE1 : |E| ≤ 1 := hE.trans (min_le_left _ _)
  have hE2 : |E| ≤ E₂ := hE.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hE4 : |E| ≤ E₄ := hE.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hg0 : 0 < g := by linarith
  have hgn : 1 ≤ g ^ (2 * R + 6) := one_le_pow₀ hg
  have hgn0 : 0 < g ^ (2 * R + 6) := by positivity
  -- the polynomial and the evaluation points
  set p : ObsPoly := incPoly E R with hp
  set P' : ObsPoly := bind₁ (invCoord E R) p with hP'
  set z : ObsVar → ℂ := fun u => obsEval g X (corrCoord E R u) with hz
  set y : ObsVar → ℂ := fun v => aeval z (invCoord E R v) with hy
  set x : ObsVar → ℂ := fun v => obsEval g X (MvPolynomial.X v) with hx
  have hobs : ∀ Q : ObsPoly, obsEval g X (bind₁ (corrCoord E R) Q) = aeval z Q := fun Q => by
    unfold obsEval
    rw [aeval_bind₁]
    rfl
  have hxp : obsEval g X p = aeval x p :=
    DFunLike.congr_fun (MvPolynomial.aeval_unique (obsEval g X)) p
  have hyp : aeval z P' = aeval y p := by
    rw [hP', aeval_bind₁]
  have hxv : ∀ v, ‖x v‖ ≤ 1 := fun v => ccf_norm_obsEval_X_le hW hg hX v
  -- indices of the variables
  have hidx : ∀ v ∈ p.vars, ccfIdx v ⊆ Ks₀ := by
    intro v hv
    rcases Finset.mem_insert.mp (ccf_vars_incPoly E R hv) with h | h
    · subst h
      simp [ccfIdx]
    · exact Finset.subset_biUnion_of_mem ccfIdx h
  have hinvS : ∀ v ∈ p.vars, ∀ j : NzInt, (v = .m j ∨ v = .f j) →
      (invCoord E R v).support ⊆ S₀ ∧ ∀ d, ‖(invCoord E R v).coeff d‖ ≤ K₀ := by
    intro v hv j hj
    have hj0 : j ∈ Ks₀ := by
      apply hidx v hv
      rcases hj with rfl | rfl <;> simp [ccfIdx]
    have hvl : v ∈ [ObsVar.m j, ObsVar.f j] := by
      rcases hj with rfl | rfl <;> simp
    obtain ⟨-, hs, -, hc⟩ := h₀ E hE2 j hj0 v hvl
    exact ⟨hs, fun d => (hc d).2.1⟩
  -- step 1: the expansion of `P_g c` in the original coordinates
  have hBv : obsEval g X p = ∑ r ∈ Finset.range (R + 2 + 1),
      (((normalH E / g) ^ (2 * r) : ℝ) : ℂ) * obsEval g X (incWick r) := by
    rw [hp, incPoly, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_mul, map_mul, map_pow]
    congr 1
    simp only [obsEval, aeval_C, aeval_X, Algebra.algebraMap_self, RingHom.id_apply]
    push_cast
    ring
  have step1 : ‖((incMean g E X : ℝ) : ℂ) - obsEval g X p‖ ≤ K₁ / g ^ (2 * R + 6) := by
    have h := h₁ W hW g hg E hE1 X hX
    rw [← hBv, show 2 * (R + 2) + 2 = 2 * R + 6 by ring] at h
    exact h
  -- step 2: the inverse substitution
  set δ : ℝ := K₄ / g ^ (2 * R + 6) with hδ
  have hδ0 : 0 ≤ δ := div_nonneg hK₄.le hgn0.le
  have hδK : δ ≤ K₄ := div_le_self hK₄.le hgn
  have hxy : ∀ v ∈ p.vars, ‖x v - y v‖ ≤ δ ∧ ‖y v‖ ≤ B := by
    intro v hv
    have hfix : ∀ u, (u = ObsVar.w ∨ u = ObsVar.γ) → y u = x u := by
      rintro u (rfl | rfl)
      · simp only [hy, hx, hz, ccf_invCoord_w, aeval_X, ccf_corrCoord_w]
      · simp only [hy, hx, hz, ccf_invCoord_γ, aeval_X, ccf_corrCoord_γ]
    have hmf : ∀ j : NzInt, j ∈ Ks₀ → ∀ u, (u = .m j ∨ u = .f j) →
        ‖y u - x u‖ ≤ δ := by
      intro j hj u hu
      have hj1 : j ∈ Ks₁ := Finset.mem_union_left _ hj
      obtain ⟨-, -, h3, h4⟩ := h₄ W hW g hg E hE4 X hX j hj1
      rcases hu with rfl | rfl
      · have e1 : y (.m j) = obsEval g X (bind₁ (corrCoord E R) (invCoord E R (.m j))) :=
          (hobs _).symm
        have e2 : x (.m j) = obsM j.1 X := by simp [hx, obsEval]
        rw [e1, e2]
        exact h3
      · have e1 : y (.f j) = obsEval g X (bind₁ (corrCoord E R) (invCoord E R (.f j))) :=
          (hobs _).symm
        have e2 : x (.f j) = obsF j.1 X := by simp [hx, obsEval]
        rw [e1, e2]
        exact h4
    have hfin : ‖y v - x v‖ ≤ δ := by
      cases v with
      | m j => exact hmf j (hidx _ hv (by simp [ccfIdx])) _ (Or.inl rfl)
      | f j => exact hmf j (hidx _ hv (by simp [ccfIdx])) _ (Or.inr rfl)
      | w => rw [hfix _ (Or.inl rfl), sub_self, norm_zero]; exact hδ0
      | γ => rw [hfix _ (Or.inr rfl), sub_self, norm_zero]; exact hδ0
    refine ⟨by rw [norm_sub_rev]; exact hfin, ?_⟩
    calc ‖y v‖ = ‖x v + (y v - x v)‖ := by rw [add_sub_cancel]
      _ ≤ ‖x v‖ + ‖y v - x v‖ := norm_add_le _ _
      _ ≤ 1 + K₄ := add_le_add (hxv v) (hfin.trans hδK)
  have step2 : ‖obsEval g X p - aeval y p‖ ≤ L₀ * δ := by
    rw [hxp]
    refine (norm_aeval_sub_aeval_le p hB0 (fun v _ => (hxv v).trans hB1)
      (fun v hv => (hxy v hv).2) (fun v hv => (hxy v hv).1)).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hδ0
    exact (ccf_lip_le hB1 p).trans (ccf_norm_incPoly_le hE1 R (by linarith))
  -- step 3: the orders dropped by the truncation
  set q : ObsPoly := P' - truncG (R + 2) P' with hq
  set ρ : ObsVar → ℝ := fun v => if v = .γ then (g ^ 2)⁻¹ else B with hρ
  have hρ0 : ∀ v, 0 ≤ ρ v := fun v => by
    simp only [hρ]
    split_ifs
    · positivity
    · exact hB0
  have hvarsP' : ∀ u ∈ P'.vars, ccfIdx u ⊆ Ks₁ := by
    intro u hu
    obtain ⟨v, hv, hu'⟩ := Finset.mem_biUnion.mp (vars_bind₁ _ _ hu)
    have hS : ∀ j : NzInt, (v = .m j ∨ v = .f j) → ccfIdx u ⊆ Ks₁ := by
      intro j hj
      obtain ⟨d, hd, hud⟩ := (mem_vars_iff_mem_support u).1 hu'
      have hd0 := (hinvS v hv j hj).1 hd
      exact (Finset.subset_biUnion_of_mem ccfIdx
        (Finset.mem_biUnion.mpr ⟨d, hd0, hud⟩)).trans Finset.subset_union_right
    cases v with
    | m j => exact hS j (Or.inl rfl)
    | f j => exact hS j (Or.inr rfl)
    | w =>
      rw [ccf_invCoord_w, vars_X, Finset.mem_singleton] at hu'
      subst hu'
      simp [ccfIdx]
    | γ =>
      rw [ccf_invCoord_γ, vars_X, Finset.mem_singleton] at hu'
      subst hu'
      simp [ccfIdx]
  have hzu : ∀ u, ccfIdx u ⊆ Ks₁ → ‖z u‖ ≤ ρ u := by
    intro u hu
    cases u with
    | m k =>
      obtain ⟨h1, -, -, -⟩ := h₄ W hW g hg E hE4 X hX k (hu (by simp [ccfIdx]))
      have hk : ‖obsM k.1 X‖ ≤ 1 := norm_obsM_le_one k.1 hX
      have : ‖z (.m k)‖ ≤ 1 + K₄ := by
        calc ‖z (.m k)‖ = ‖obsM k.1 X + (obsEval g X (corrObsM E R k) - obsM k.1 X)‖ := by
              rw [add_sub_cancel]; rfl
          _ ≤ ‖obsM k.1 X‖ + ‖obsEval g X (corrObsM E R k) - obsM k.1 X‖ := norm_add_le _ _
          _ ≤ 1 + K₄ := add_le_add hk (h1.trans (div_le_self hK₄.le (one_le_pow₀ hg)))
      simpa [hρ] using this
    | f k =>
      obtain ⟨-, h2, -, -⟩ := h₄ W hW g hg E hE4 X hX k (hu (by simp [ccfIdx]))
      have hk : ‖obsF k.1 X‖ ≤ 1 := norm_obsF_le_one k.1 hX
      have : ‖z (.f k)‖ ≤ 1 + K₄ := by
        calc ‖z (.f k)‖ = ‖obsF k.1 X + (obsEval g X (corrObsF E R k) - obsF k.1 X)‖ := by
              rw [add_sub_cancel]; rfl
          _ ≤ ‖obsF k.1 X‖ + ‖obsEval g X (corrObsF E R k) - obsF k.1 X‖ := norm_add_le _ _
          _ ≤ 1 + K₄ := add_le_add hk (h2.trans (div_le_self hK₄.le (one_le_pow₀ hg)))
      simpa [hρ] using this
    | w =>
      have h := hxv .w
      simp only [hz, ccf_corrCoord_w, hρ]
      simp only [hx] at h
      simpa using h.trans hB1
    | γ =>
      simp only [hz, ccf_corrCoord_γ, hρ, obsEval, aeval_X, ite_true]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hq1 : ‖aeval z q‖ ≤ ccfNorm ρ q := by
    refine ccf_norm_aeval_le q fun u hu => hzu u (hvarsP' u ?_)
    have h := vars_sub_subset _ hu
    rcases Finset.mem_union.mp h with h | h
    · exact h
    · exact ccf_vars_truncG _ _ h
  have hq2 : ccfNorm ρ q ≤ ((g ^ 2)⁻¹) ^ (R + 3) * ccfNorm ρ' q := by
    unfold ccfNorm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    have hdγ : R + 3 ≤ d .γ := by
      rw [mem_support_iff, hq, ccf_coeff_sub_truncG] at hd
      split_ifs at hd with h
      · exact absurd rfl hd
      · omega
    rw [show ρ = fun v => if v = .γ then (g ^ 2)⁻¹ else B from rfl, ccfWt_split]
    have hg2 : (g ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hg)
    have hpow : ((g ^ 2)⁻¹) ^ (d .γ) ≤ ((g ^ 2)⁻¹) ^ (R + 3) :=
      pow_le_pow_of_le_one (by positivity) hg2 hdγ
    have hw0 : 0 ≤ ccfWt (fun v => if v = ObsVar.γ then 1 else B) d := ccfWt_nonneg hρ'0 d
    calc ‖q.coeff d‖ * ((g ^ 2)⁻¹ ^ d .γ * ccfWt (fun v => if v = ObsVar.γ then 1 else B) d)
        ≤ ‖q.coeff d‖ * ((g ^ 2)⁻¹ ^ (R + 3) *
          ccfWt (fun v => if v = ObsVar.γ then 1 else B) d) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hw0) (norm_nonneg _)
      _ = (g ^ 2)⁻¹ ^ (R + 3) * (‖q.coeff d‖ * ccfWt ρ' d) := by ring
  have hq3 : ccfNorm ρ' q ≤ ccfNorm ρ' P' := by
    refine ccfNorm_mono hρ'0 fun d => ?_
    rw [hq, ccf_coeff_sub_truncG]
    split_ifs
    · rw [norm_zero]
      exact norm_nonneg _
    · exact le_rfl
  have hq4 : ccfNorm ρ' P' ≤ ccfNorm (fun _ => B₂) p := by
    refine ccfNorm_bind₁_le hρ'0 _ p fun v hv => ?_
    have hS : ∀ j : NzInt, (v = .m j ∨ v = .f j) → ccfNorm ρ' (invCoord E R v) ≤ B₂ := by
      intro j hj
      obtain ⟨hs, hc⟩ := hinvS v hv j hj
      exact (ccfNorm_le_of_support hρ'0 hs hc).trans (le_max_right _ _)
    cases v with
    | m j => exact hS j (Or.inl rfl)
    | f j => exact hS j (Or.inr rfl)
    | w =>
      rw [ccf_invCoord_w, ccfNorm_X, show ρ' ObsVar.w = B by simp [hρ']]
      exact le_max_left _ _
    | γ =>
      rw [ccf_invCoord_γ, ccfNorm_X, show ρ' ObsVar.γ = 1 by simp [hρ']]
      exact hB1.trans (le_max_left _ _)
  have step3 : ‖aeval y p - obsEval g X (bind₁ (corrCoord E R) (incCorr E R))‖ ≤
      K₃ / g ^ (2 * R + 6) := by
    rw [hobs, ← hyp, ← map_sub]
    have e : P' - incCorr E R = q := rfl
    rw [e]
    refine hq1.trans (hq2.trans ?_)
    have h5 := (hq3.trans hq4).trans (ccf_norm_incPoly_le hE1 R hB₂0)
    have hg' : ((g ^ 2)⁻¹) ^ (R + 3) = 1 / g ^ (2 * R + 6) := by
      rw [inv_pow, ← pow_mul, one_div]
      ring_nf
    rw [hg', div_eq_mul_one_div K₃, mul_comm K₃]
    exact mul_le_mul_of_nonneg_left h5 (by positivity)
  -- conclusion
  calc ‖((incMean g E X : ℝ) : ℂ) - obsEval g X (bind₁ (corrCoord E R) (incCorr E R))‖
      = ‖(((incMean g E X : ℝ) : ℂ) - obsEval g X p) + (obsEval g X p - aeval y p) +
          (aeval y p - obsEval g X (bind₁ (corrCoord E R) (incCorr E R)))‖ := by ring_nf
    _ ≤ ‖((incMean g E X : ℝ) : ℂ) - obsEval g X p‖ + ‖obsEval g X p - aeval y p‖ +
          ‖aeval y p - obsEval g X (bind₁ (corrCoord E R) (incCorr E R))‖ := norm_add₃_le
    _ ≤ K₁ / g ^ (2 * R + 6) + L₀ * δ + K₃ / g ^ (2 * R + 6) :=
          add_le_add (add_le_add step1 step2) step3
    _ = (K₁ + L₀ * K₄ + K₃) / g ^ (2 * R + 6) := by rw [hδ]; ring
    _ ≤ (K₁ + L₀ * K₄ + K₃ + 1) / g ^ (2 * R + 6) :=
          div_le_div_of_nonneg_right (by linarith) hgn0.le

/-- The `W⁰` part of the expansion of `P_g c` in the corrected coordinates lies in the ideal
`(F_k : k ≠ 0)` (Section 11.3.4 [lg:sec:cocycle-correction]), for every energy. -/
theorem zeroW_incCorr_mem_fIdeal (E : ℝ) (R : ℕ) : zeroW (incCorr E R) ∈ fIdeal := by
  set ψ : ObsVar → ObsPoly := fun v => zeroW (invCoord E R v) with hψ
  have h1 : zeroW (bind₁ (invCoord E R) (incPoly E R)) = bind₁ ψ (incPoly E R) := by
    show aeval _ (bind₁ (invCoord E R) (incPoly E R)) = _
    rw [aeval_eq_bind₁, bind₁_bind₁]
    rfl
  have h2 : bind₁ ψ (incPoly E R) = bind₁ ψ (zeroW (incPoly E R)) := by
    have hext : (bind₁ ψ : ObsPoly →ₐ[ℂ] ObsPoly) = (bind₁ ψ).comp zeroW := by
      refine MvPolynomial.algHom_ext fun v => ?_
      rw [AlgHom.comp_apply, ccf_zeroW_X, bind₁_X_right]
      by_cases hv : v = .w
      · subst hv
        simp only [ite_true, map_zero, hψ, ccf_invCoord_w, ccf_zeroW_X]
      · simp only [hv, ite_false, bind₁_X_right]
    exact DFunLike.congr_fun hext _
  have h3 : zeroW (incPoly E R) ∈ fIdeal := by
    unfold incPoly
    rw [map_sum]
    refine Ideal.sum_mem _ fun r _ => ?_
    rw [map_mul]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · rw [(wickMap_zero_incWick_zero 0).2, map_zero, mul_zero]
      exact Ideal.zero_mem _
    · exact Ideal.mul_mem_left _ _ (zeroW_incWick_mem_fIdeal hr)
  have h4 : zeroW (bind₁ (invCoord E R) (incPoly E R)) ∈ fIdeal := by
    rw [h1, h2]
    refine ccf_bind₁_mem_fIdeal (fun k => ?_) h3
    exact ccf_mem_fIdeal_of_support (corrObs_form E R k).2.2.2.2.2.2.2 (ccf_support_zeroW _)
  unfold incCorr
  rw [ccf_zeroW_truncG]
  exact ccf_mem_fIdeal_of_support h4 (ccf_support_truncG _ _)

/-- Finite supports (Section 11.3.4 [lg:sec:cocycle-correction]): on a window fixed after `R` and
the index set, `b_k`, `A_{kr}` and `(A_0)_{kr}` (`r` in the index set) vanish for `k` outside one
finite set containing the index set. -/
theorem corrCoeff_support (R : ℕ) (Ks : Finset NzInt) :
    ∃ S : Finset NzInt, Ks ⊆ S ∧ ∃ E₁ : ℝ, 0 < E₁ ∧ ∀ g E : ℝ, |E| ≤ E₁ → ∀ k : NzInt, k ∉ S →
      driftCoeff g E R k = 0 ∧ ∀ r ∈ Ks, corrMat g E R k r = 0 ∧ corrMat0 g E R k r = 0 := by
  obtain ⟨E₂, hE₂, S₀, K₀, -, h₀⟩ := corrCoeff_bounded R ((ccfV₀ R).biUnion ccfIdx)
  obtain ⟨E₃, hE₃, S₁, K₁, -, h₁⟩ := corrCoeff_bounded R Ks
  refine ⟨Ks ∪ ((S₀ ∪ S₁).biUnion fun d => d.support).biUnion ccfIdx,
    Finset.subset_union_left, min E₂ E₃, lt_min hE₂ hE₃, fun g E hE k hk => ?_⟩
  have hk' : ∀ d ∈ S₀ ∪ S₁, ObsVar.f k ∉ d.support := fun d hd hkd =>
    hk (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨ObsVar.f k, Finset.mem_biUnion.mpr ⟨d, hd, hkd⟩, by simp [ccfIdx]⟩))
  have hkKs : k ∉ Ks := fun h => hk (Finset.mem_union_left _ h)
  have hvarS : ∀ p : ObsPoly, p.support ⊆ S₀ ∪ S₁ → ObsVar.f k ∉ p.vars := fun p hp hv => by
    obtain ⟨d, hd, hkd⟩ := (mem_vars_iff_mem_support _).1 hv
    exact hk' d (hp hd) hkd
  have hE₂' : |E| ≤ E₂ := hE.trans (min_le_left _ _)
  have hE₃' : |E| ≤ E₃ := hE.trans (min_le_right _ _)
  have hupd : ∀ r ∈ Ks, ∀ p : ObsPoly, p.vars ⊆ (corrUpd E R (.f r)).vars →
      ObsVar.f k ∉ (p - X (ObsVar.f r)).vars := by
    intro r hr p hp hv
    have := vars_sub_subset _ hv
    rw [Finset.mem_union, vars_X, Finset.mem_singleton] at this
    rcases this with h | h
    · exact hvarS _ ((h₁ E hE₃' r hr (.f r) (by simp)).2.2.1.trans Finset.subset_union_right)
        (hp h)
    · have hkr : k = r := by simpa using h
      exact hkKs (hkr ▸ hr)
  refine ⟨ccf_linCoeff_eq_zero _ _ ?_, fun r hr =>
    ⟨ccf_linCoeff_eq_zero _ _ (hupd r hr _ subset_rfl),
      ccf_linCoeff_eq_zero _ _ (hupd r hr _ (ccf_vars_truncG _ _))⟩⟩
  intro hv
  have hv2 := vars_bind₁ _ _ (ccf_vars_truncG _ _ hv)
  rw [Finset.mem_biUnion] at hv2
  obtain ⟨v, hv, hv'⟩ := hv2
  have hv0 := ccf_vars_incPoly E R hv
  have hinv : ∀ j : NzInt, ∀ u ∈ [ObsVar.m j, ObsVar.f j], u ∈ ccfV₀ R →
      ObsVar.f k ∉ (invCoord E R u).vars :=
    fun j u hu hu0 => hvarS _ ((h₀ E hE₂' j (Finset.mem_biUnion.mpr ⟨u, hu0, by
      rcases List.mem_cons.mp hu with rfl | hu
      · simp [ccfIdx]
      · rw [List.mem_singleton] at hu
        subst hu
        simp [ccfIdx]⟩) u hu).2.1.trans Finset.subset_union_left)
  cases v with
  | m j => exact hinv j _ (by simp) (by simpa using hv0) hv'
  | f j => exact hinv j _ (by simp) (by simpa using hv0) hv'
  | w =>
    rw [ccf_invCoord_w, vars_X] at hv'
    simp at hv'
  | γ =>
    rw [ccf_invCoord_γ, vars_X] at hv'
    simp at hv'

end LSBA
