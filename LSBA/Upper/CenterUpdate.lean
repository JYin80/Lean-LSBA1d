import LSBA.Upper.CenterParity
import LSBA.Upper.CenterLeadTrace
import LSBA.Upper.CenterLeadMarked

/-!
# The corrected transition: leading terms, remainders and bounds

For the corrected observables of (11.50) [lg:eq:corrected-observables] on a window `|E| ≤ E₁`
fixed after `R` and a finite index set: the leading retained map
`y_k ↦ (−e^{−2iθ})^k [y_k + h_θ² g⁻² 𝓛 y_k]` with `𝓛` of (11.51) [lg:eq:center-corner] and
(11.52) [lg:eq:center-trace]; the remainders (11.57) [lg:eq:widtherrors]
`|P_g M_k − [P_g M_k]_{≤R+2,0}(M)| ≤ K(g⁻²W⁻² + g^{−2R−2})` and the same for `F_k` with `W⁻¹`;
`M_k = m_k + O(g⁻²)`, `F_k = f_k + O(g⁻²)`; and the inverse substitution
`m_k = m_k^{[R+2]}(M) + O(g^{−2R−6})`, `f_k = f_k^{[R+2]}(M, F) + O(g^{−2R−6})`
(Section 11.3.1 [lg:sec:state-estimates]).
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Coefficients of the truncation, the parity part, the `W⁰` part and the rotation -/

private lemma cu_weight_one (w : ObsVar → ℕ) (v : ObsVar) (hv : w v = 1)
    (h0 : ∀ u, u ≠ v → w u = 0) (d : ObsVar →₀ ℕ) : Finsupp.weight w d = d v := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_single v]
  · simp [hv]
  · intro b _ hb
    simp [h0 b hb]
  · intro h
    simp [Finsupp.notMem_support_iff.mp h]

private lemma cu_weight_gam (d : ObsVar →₀ ℕ) : Finsupp.weight ObsVar.gamWt d = d .γ :=
  cu_weight_one _ _ rfl (fun u hu => by cases u <;> simp_all [ObsVar.gamWt]) d

private lemma cu_weight_w (d : ObsVar →₀ ℕ) : Finsupp.weight ObsVar.wWt d = d .w :=
  cu_weight_one _ _ rfl (fun u hu => by cases u <;> simp_all [ObsVar.wWt]) d

private lemma cu_coeff_add (p q : ObsPoly) (d : ObsVar →₀ ℕ) :
    (p + q).coeff d = p.coeff d + q.coeff d := by
  simp

private lemma cu_coeff_comp (s : ℕ) (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (weightedHomogeneousComponent ObsVar.gamWt s p).coeff d =
      if d .γ = s then p.coeff d else 0 := by
  rw [coeff_weightedHomogeneousComponent, cu_weight_gam]

private lemma cu_coeff_truncG (N : ℕ) (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (truncG N p).coeff d = if d .γ ≤ N then p.coeff d else 0 := by
  unfold truncG
  rw [LinearMap.sum_apply, MvPolynomial.coeff_sum]
  simp only [cu_coeff_comp]
  rw [Finset.sum_ite_eq]
  simp

private lemma cu_truncG_Xγ {N : ℕ} (hN : 1 ≤ N) : truncG N (X .γ) = X .γ := by
  ext d
  rw [cu_coeff_truncG]
  split_ifs with h1
  · rfl
  · rw [coeff_X, eq_comm, ite_eq_right_iff]
    rintro rfl
    simp at h1
    omega

private lemma cu_truncG_truncG {M N : ℕ} (h : M ≤ N) (p : ObsPoly) :
    truncG M (truncG N p) = truncG M p := by
  ext d
  simp only [cu_coeff_truncG]
  split_ifs with h1 h2 <;> first | rfl | omega

private lemma cu_support_oppDiv (E : ℝ) (k : ℤ) (p : ObsPoly) :
    ∀ d ∈ (oppDiv E k p).support, d ∈ p.support ∧ ¬Even (obsDeg d - k) := by
  intro d hd
  obtain ⟨d', hd', hmem⟩ := Finset.mem_biUnion.mp (support_sum hd)
  split_ifs at hmem with h
  · simp at hmem
  · obtain rfl := Finset.mem_singleton.mp (support_monomial_subset hmem)
    exact ⟨hd', h⟩

private lemma cu_coeff_parityPart (k : ℤ) (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (parityPart k p).coeff d = if Even (obsDeg d - k) then p.coeff d else 0 := by
  unfold parityPart
  rw [MvPolynomial.coeff_sum]
  by_cases hd : d ∈ p.support
  · rw [Finset.sum_eq_single d]
    · by_cases h : Even (obsDeg d - k) <;> simp [h]
    · intro b _ hb
      split_ifs <;> simp [coeff_monomial, hb]
    · intro h
      exact absurd hd h
  · rw [Finset.sum_eq_zero]
    · simp [MvPolynomial.notMem_support_iff.mp hd]
    · intro b hb
      split_ifs
      · have hbd : b ≠ d := fun h => hd (h ▸ hb)
        simp [coeff_monomial, hbd]
      · simp

private lemma cu_zeroW_monomial (d : ObsVar →₀ ℕ) (a : ℂ) :
    zeroW (monomial d a) = if d .w = 0 then monomial d a else 0 := by
  rw [zeroW, aeval_monomial, monomial_eq, MvPolynomial.algebraMap_eq]
  split_ifs with h
  · congr 1
    refine Finsupp.prod_congr fun v hv => ?_
    have hvw : v ≠ .w := by
      rintro rfl
      exact (Finsupp.mem_support_iff.mp hv) h
    simp [hvw]
  · rw [Finsupp.prod, Finset.prod_eq_zero (i := ObsVar.w) (Finsupp.mem_support_iff.mpr h)]
    · simp
    · simp [zero_pow h]

private lemma cu_coeff_zeroW (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (zeroW p).coeff d = if d .w = 0 then p.coeff d else 0 := by
  refine MvPolynomial.induction_on' p (fun u a => ?_) (fun p q hp hq => ?_)
  · rw [cu_zeroW_monomial]
    by_cases hu : u = d
    · subst hu
      split_ifs <;> simp
    · split_ifs <;> simp [coeff_monomial, hu]
  · rw [map_add, cu_coeff_add, hp, hq, cu_coeff_add]
    split_ifs <;> simp

private lemma cu_zeroW_C (a : ℂ) : zeroW (C a) = C a := by
  simp [zeroW]

private lemma cu_zeroW_X {v : ObsVar} (h : v ≠ .w) : zeroW (X v) = X v := by
  simp [zeroW, h]

private lemma cu_norm_normalPhase (E : ℝ) : ‖normalPhase E‖ = 1 := by
  unfold normalPhase
  rw [norm_neg, show (2 : ℂ) * ((freeAngle E : ℂ) * Complex.I) =
    ((2 * freeAngle E : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The factor by which the rotation multiplies a monomial. -/
private def cuMu (E : ℝ) (d : ObsVar →₀ ℕ) : ℂ :=
  d.prod fun v n => ((-normalPhase E) ^ v.idx) ^ n

private lemma cu_norm_mu (E : ℝ) (d : ObsVar →₀ ℕ) : ‖cuMu E d‖ = 1 := by
  unfold cuMu Finsupp.prod
  rw [norm_prod]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [norm_pow, norm_zpow, norm_neg, cu_norm_normalPhase, one_zpow, one_pow]

private lemma cu_rotPoly_monomial (E : ℝ) (d : ObsVar →₀ ℕ) (a : ℂ) :
    rotPoly E (monomial d a) = monomial d (cuMu E d * a) := by
  rw [rotPoly, aeval_monomial, MvPolynomial.algebraMap_eq]
  have h1 : (d.prod fun v n => (C ((-normalPhase E) ^ v.idx) * X v : ObsPoly) ^ n) =
      C (cuMu E d) * d.prod fun v n => (X v : ObsPoly) ^ n := by
    simp only [mul_pow, ← map_pow]
    rw [Finsupp.prod_mul, cuMu, map_finsuppProd]
  rw [h1, monomial_eq, map_mul]
  ring

private lemma cu_coeff_rotPoly (E : ℝ) (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (rotPoly E p).coeff d = cuMu E d * p.coeff d := by
  refine MvPolynomial.induction_on' p (fun u a => ?_) (fun p q hp hq => ?_)
  · rw [cu_rotPoly_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · rw [mul_zero]
  · rw [map_add, cu_coeff_add, hp, hq, cu_coeff_add, mul_add]

private lemma cu_support_rotPoly (E : ℝ) (p : ObsPoly) : (rotPoly E p).support ⊆ p.support := by
  intro d hd
  rw [mem_support_iff, cu_coeff_rotPoly] at hd
  exact mem_support_iff.mpr (right_ne_zero_of_mul hd)

private lemma cu_rotPoly_X (E : ℝ) (v : ObsVar) :
    rotPoly E (X v) = C ((-normalPhase E) ^ v.idx) * X v := by
  rw [rotPoly, aeval_X]

/-! ### The ideals `(γ^n)` -/

/-- The ideal of the polynomials of order at least `g^{−2n}`. -/
private def cuI (n : ℕ) : Ideal ObsPoly := Ideal.span {X .γ ^ n}

private lemma cu_mem_I {n : ℕ} {p : ObsPoly} : p ∈ cuI n ↔ ∀ d ∈ p.support, n ≤ d .γ := by
  have h : ({X .γ ^ n} : Set ObsPoly) =
      (fun s => monomial s (1 : ℂ)) '' {Finsupp.single ObsVar.γ n} := by
    simp [X_pow_eq_monomial]
  rw [cuI, h, mem_ideal_span_monomial_image]
  simp [Finsupp.single_le_iff]

private lemma cu_I_mono {m n : ℕ} (h : m ≤ n) {p : ObsPoly} (hp : p ∈ cuI n) : p ∈ cuI m := by
  rw [cu_mem_I] at hp ⊢
  exact fun d hd => h.trans (hp d hd)

private lemma cu_mem_I_zero (p : ObsPoly) : p ∈ cuI 0 :=
  Ideal.mem_span_singleton'.mpr ⟨p, by rw [pow_zero, mul_one]⟩

private lemma cu_pow_mem_I (n : ℕ) : (X .γ : ObsPoly) ^ n ∈ cuI n := Ideal.subset_span rfl

private lemma cu_mul_mem_I {a b : ℕ} {p q : ObsPoly} (hp : p ∈ cuI a) (hq : q ∈ cuI b) :
    p * q ∈ cuI (a + b) := by
  obtain ⟨p', rfl⟩ := Ideal.mem_span_singleton'.mp hp
  obtain ⟨q', rfl⟩ := Ideal.mem_span_singleton'.mp hq
  exact Ideal.mem_span_singleton'.mpr ⟨p' * q', by ring⟩

private lemma cu_sub_truncG_mem (N : ℕ) (p : ObsPoly) : p - truncG N p ∈ cuI (N + 1) := by
  rw [cu_mem_I]
  intro d hd
  rw [mem_support_iff, coeff_sub, cu_coeff_truncG] at hd
  split_ifs at hd with h
  · exact absurd (sub_self _) hd
  · omega

private lemma cu_truncG_eq_zero {N : ℕ} {p : ObsPoly} (hp : p ∈ cuI (N + 1)) : truncG N p = 0 := by
  ext d
  have h00 : (0 : ObsPoly).coeff d = 0 := by simp
  rw [cu_coeff_truncG, h00]
  split_ifs with h
  · by_contra h0
    have := (cu_mem_I.mp hp) d (mem_support_iff.mpr h0)
    omega
  · rfl

private lemma cu_truncG_congr {N : ℕ} {p q : ObsPoly} (h : p - q ∈ cuI (N + 1)) :
    truncG N p = truncG N q := by
  rw [← sub_eq_zero, ← map_sub]
  exact cu_truncG_eq_zero h

private lemma cu_map_mem_I (φ : ObsPoly →ₐ[ℂ] ObsPoly) (hφ : φ (X .γ) = X .γ) {n : ℕ}
    {p : ObsPoly} (hp : p ∈ cuI n) : φ p ∈ cuI n := by
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hp
  exact Ideal.mem_span_singleton'.mpr ⟨φ q, by rw [map_mul, map_pow, hφ]⟩

private lemma cu_rotPoly_γ (E : ℝ) : rotPoly E (X .γ) = X .γ := by
  rw [cu_rotPoly_X]
  simp [ObsVar.idx]

private lemma cu_zeroW_γ : zeroW (X .γ) = X .γ := cu_zeroW_X (fun h => ObsVar.noConfusion h)

/-- `q_r` as a `ℂ`-linear map. -/
private def cuW (r : ℕ) : ObsPoly →ₗ[ℂ] ObsPoly where
  toFun := wickMap r
  map_add' p q := by simpa using (wickMap_linear r 1 p q).1
  map_smul' a p := by
    have h0 : wickMap r 0 = 0 := by
      have := (wickMap_linear r 1 0 0).1
      simpa using this
    simpa [h0] using (wickMap_linear r a p 0).1

private lemma cuW_apply (r : ℕ) (p : ObsPoly) : cuW r p = wickMap r p := rfl

private lemma cu_wick_pow_mul (r n : ℕ) (q : ObsPoly) :
    wickMap r (X .γ ^ n * q) = X .γ ^ n * wickMap r q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, (wickMap_linear r 1 (X ObsVar.γ ^ n * q) 0).2, ih, mul_assoc]

private lemma cu_wick_mem_I (r : ℕ) {n : ℕ} {p : ObsPoly} (hp : p ∈ cuI n) :
    wickMap r p ∈ cuI n := by
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hp
  rw [mul_comm, cu_wick_pow_mul]
  exact Ideal.mul_mem_right _ _ (cu_pow_mem_I n)

private lemma cu_bind_sub_mem (J : Ideal ObsPoly) (τ : ObsVar → ObsPoly)
    (h : ∀ u, τ u - X u ∈ J) (p : ObsPoly) : bind₁ τ p - p ∈ J := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add, add_sub_add_comm]
    exact J.add_mem hp hq
  | mul_X p u hp =>
    rw [map_mul, bind₁_X_right]
    have e : bind₁ τ p * τ u - p * X u = (bind₁ τ p - p) * τ u + p * (τ u - X u) := by ring
    rw [e]
    exact J.add_mem (J.mul_mem_right _ hp) (J.mul_mem_left _ (h u))

private lemma cu_bind_sub_mem_I {a b : ℕ} {τ : ObsVar → ObsPoly} (h : ∀ u, τ u - X u ∈ cuI a)
    (hγ : τ .γ = X .γ) {p : ObsPoly} (hp : p ∈ cuI b) : bind₁ τ p - p ∈ cuI (a + b) := by
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hp
  rw [map_mul, map_pow, bind₁_X_right, hγ, ← sub_mul]
  exact cu_mul_mem_I (cu_bind_sub_mem _ τ h q) (cu_pow_mem_I b)

private lemma cu_bind_mem_I {τ : ObsVar → ObsPoly} (hγ : τ .γ = X .γ) {n : ℕ} {p : ObsPoly}
    (hp : p ∈ cuI n) : bind₁ τ p ∈ cuI n :=
  cu_map_mem_I (bind₁ τ) (by rw [bind₁_X_right, hγ]) hp

/-! ### The sum of the moduli of the coefficients -/

/-- `Σ_d |p_d|`. -/
private def cuL (p : ObsPoly) : ℝ := ∑ d ∈ p.support, ‖p.coeff d‖

private lemma cuL_nonneg (p : ObsPoly) : 0 ≤ cuL p := Finset.sum_nonneg fun _ _ => norm_nonneg _

private lemma cuL_eq {p : ObsPoly} {s : Finset (ObsVar →₀ ℕ)} (h : p.support ⊆ s) :
    cuL p = ∑ d ∈ s, ‖p.coeff d‖ := by
  unfold cuL
  refine Finset.sum_subset h fun d _ hd => ?_
  rw [mem_support_iff, not_not] at hd
  rw [hd, norm_zero]

private lemma cuL_le_of_coeff {p q : ObsPoly} (h : ∀ d, ‖q.coeff d‖ ≤ ‖p.coeff d‖) :
    cuL q ≤ cuL p := by
  have hs : q.support ⊆ p.support := fun d hd => by
    rw [mem_support_iff] at hd ⊢
    intro h0
    have := h d
    rw [h0, norm_zero] at this
    exact hd (norm_le_zero_iff.mp this)
  rw [cuL_eq hs]
  exact Finset.sum_le_sum fun d _ => h d

private lemma cuL_filter {P : (ObsVar →₀ ℕ) → Prop} [DecidablePred P] {p q : ObsPoly}
    (h : ∀ d, q.coeff d = if P d then p.coeff d else 0) : cuL q ≤ cuL p :=
  cuL_le_of_coeff fun d => by rw [h]; split_ifs <;> simp

private lemma cuL_add_le (p q : ObsPoly) : cuL (p + q) ≤ cuL p + cuL q := by
  rw [cuL_eq (support_add (p := p) (q := q)), cuL_eq (p := p) Finset.subset_union_left,
    cuL_eq (p := q) Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun d _ => by rw [cu_coeff_add]; exact norm_add_le _ _

private lemma cuL_sub_le (p q : ObsPoly) : cuL (p - q) ≤ cuL p + cuL q := by
  rw [cuL_eq (support_sub (p := p) (q := q)), cuL_eq (p := p) Finset.subset_union_left,
    cuL_eq (p := q) Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun d _ => by rw [coeff_sub]; exact norm_sub_le _ _

private lemma cuL_smul (a : ℂ) (p : ObsPoly) : cuL (a • p) ≤ ‖a‖ * cuL p := by
  rw [cuL_eq (support_smul (a := a) (f := p)), cuL, Finset.mul_sum]
  exact Finset.sum_le_sum fun d _ => by rw [coeff_smul, smul_eq_mul, norm_mul]

private lemma cuL_monomial (d : ObsVar →₀ ℕ) (a : ℂ) : cuL (monomial d a) ≤ ‖a‖ := by
  rw [cuL_eq support_monomial_subset, Finset.sum_singleton]
  simp

private lemma cuL_sum_le {ι : Type*} (s : Finset ι) (f : ι → ObsPoly) :
    cuL (∑ i ∈ s, f i) ≤ ∑ i ∈ s, cuL (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cuL]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (cuL_add_le _ _).trans (add_le_add le_rfl ih)

private lemma cuL_mul_le (p q : ObsPoly) : cuL (p * q) ≤ cuL p * cuL q := by
  conv_lhs => rw [p.as_sum, q.as_sum, Finset.sum_mul_sum]
  refine (cuL_sum_le _ _).trans ?_
  rw [cuL, cuL, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun a _ => (cuL_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [monomial_mul_monomial]
  exact (cuL_monomial _ _).trans (norm_mul _ _).le

private lemma cuL_one : cuL (1 : ObsPoly) ≤ 1 := by
  simpa using cuL_monomial 0 (1 : ℂ)

private lemma cuL_X (v : ObsVar) : cuL (X v : ObsPoly) ≤ 1 := by
  have h := cuL_monomial (Finsupp.single v 1) (1 : ℂ)
  rw [norm_one] at h
  exact h

private lemma cuL_pow_le (p : ObsPoly) (n : ℕ) : cuL (p ^ n) ≤ cuL p ^ n := by
  induction n with
  | zero => simpa using cuL_one
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (cuL_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (cuL_nonneg _))

private lemma cuL_prod_le {ι : Type*} (s : Finset ι) (f : ι → ObsPoly) :
    cuL (∏ i ∈ s, f i) ≤ ∏ i ∈ s, cuL (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cuL_one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (cuL_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (cuL_nonneg _))

private lemma cuL_C_mul (a : ℂ) (p : ObsPoly) : cuL (C a * p) ≤ ‖a‖ * cuL p := by
  rw [C_mul']
  exact cuL_smul a p

private lemma cuL_bind_monomial (τ : ObsVar → ObsPoly) (d : ObsVar →₀ ℕ) (a : ℂ) :
    cuL (bind₁ τ (monomial d a)) ≤ ‖a‖ * ∏ u ∈ d.support, cuL (τ u) ^ d u := by
  rw [bind₁_monomial]
  refine (cuL_C_mul _ _).trans (mul_le_mul_of_nonneg_left ((cuL_prod_le _ _).trans
    (Finset.prod_le_prod₀ (fun _ _ => cuL_nonneg _) fun u _ => cuL_pow_le _ _)) (norm_nonneg _))

private lemma cuL_le_card {p : ObsPoly} {S : Finset (ObsVar →₀ ℕ)} {K : ℝ} (hS : p.support ⊆ S)
    (hK : ∀ d, ‖p.coeff d‖ ≤ K) : cuL p ≤ S.card * K := by
  rw [cuL_eq hS]
  have := Finset.sum_le_card_nsmul S (fun d => ‖p.coeff d‖) K fun d _ => hK d
  rwa [nsmul_eq_mul] at this

private lemma cu_sum_monomial {p : ObsPoly} {S : Finset (ObsVar →₀ ℕ)} (hS : p.support ⊆ S) :
    p = ∑ d ∈ S, monomial d (p.coeff d) := by
  conv_lhs => rw [p.as_sum]
  refine Finset.sum_subset hS fun d _ hd => ?_
  rw [mem_support_iff, not_not] at hd
  rw [hd, monomial_zero]

private lemma cuL_bind_le {τ : ObsVar → ObsPoly} {p : ObsPoly} {S : Finset (ObsVar →₀ ℕ)}
    {K B : ℝ} (hS : p.support ⊆ S) (hK : ∀ d, ‖p.coeff d‖ ≤ K)
    (hB : ∀ d ∈ S, ∀ u ∈ d.support, cuL (τ u) ≤ B) :
    cuL (bind₁ τ p) ≤ K * ∑ d ∈ S, ∏ u ∈ d.support, B ^ d u := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  rw [cu_sum_monomial hS, map_sum, Finset.mul_sum]
  refine (cuL_sum_le _ _).trans (Finset.sum_le_sum fun d hd => (cuL_bind_monomial _ _ _).trans ?_)
  exact mul_le_mul (hK d) (Finset.prod_le_prod₀ (fun _ _ => pow_nonneg (cuL_nonneg _) _)
    fun u hu => pow_le_pow_left₀ (cuL_nonneg _) (hB d hd u hu) _)
    (Finset.prod_nonneg fun _ _ => pow_nonneg (cuL_nonneg _) _) hK0

/-! ### Evaluation bounds -/

private lemma cu_norm_eval_monomial {W : ℕ} (hW : 1 ≤ W) {g : ℝ} (hg : 1 ≤ g) {X : State W}
    (hX : IsState X) (d : ObsVar →₀ ℕ) (a : ℂ) :
    ‖obsEval g X (monomial d a)‖ ≤ ‖a‖ * ((W : ℝ)⁻¹) ^ d .w * ((g ^ 2)⁻¹) ^ d .γ := by
  have hg0 : 0 < g := by linarith
  have hv : ∀ v : ObsVar, ‖obsEval g X (MvPolynomial.X v)‖ ≤
      ((W : ℝ)⁻¹) ^ v.wWt * ((g ^ 2)⁻¹) ^ v.gamWt := by
    intro v
    cases v with
    | m k => simpa [obsEval, ObsVar.wWt, ObsVar.gamWt] using norm_obsM_le_one k.1 hX
    | f k => simpa [obsEval, ObsVar.wWt, ObsVar.gamWt] using norm_obsF_le_one k.1 hX
    | w => simp [obsEval, ObsVar.wWt, ObsVar.gamWt]
    | γ =>
      simp only [obsEval, aeval_X, Complex.norm_real, ObsVar.wWt, ObsVar.gamWt, pow_zero, pow_one,
        one_mul, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity)]
  rw [monomial_eq, map_mul, map_finsuppProd, norm_mul]
  have hC : ‖obsEval g X (C a)‖ = ‖a‖ := by simp [obsEval]
  rw [hC, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [Finsupp.prod, norm_prod]
  simp only [map_pow]
  have hA0 : 0 ≤ (W : ℝ)⁻¹ := by positivity
  have hB0 : 0 ≤ (g ^ 2)⁻¹ := by positivity
  calc ∏ v ∈ d.support, ‖obsEval g X (MvPolynomial.X v) ^ d v‖
      ≤ ∏ v ∈ d.support, (((W : ℝ)⁻¹) ^ v.wWt * ((g ^ 2)⁻¹) ^ v.gamWt) ^ d v :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun v _ => by
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (hv v) _
    _ = ((W : ℝ)⁻¹) ^ (∑ v ∈ d.support, d v * v.wWt) *
          ((g ^ 2)⁻¹) ^ (∑ v ∈ d.support, d v * v.gamWt) := by
        rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun v _ => ?_
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm v.wWt, mul_comm v.gamWt]
    _ = ((W : ℝ)⁻¹) ^ d .w * ((g ^ 2)⁻¹) ^ d .γ := by
        rw [← cu_weight_w, ← cu_weight_gam, Finsupp.weight_apply, Finsupp.weight_apply,
          Finsupp.sum, Finsupp.sum]
        simp only [smul_eq_mul]

private lemma cu_norm_eval_le {W : ℕ} (hW : 1 ≤ W) {g : ℝ} (hg : 1 ≤ g) {X : State W}
    (hX : IsState X) (a b : ℕ) {p : ObsPoly} (h : ∀ d ∈ p.support, a ≤ d .w ∧ b ≤ d .γ) :
    ‖obsEval g X p‖ ≤ cuL p * ((W : ℝ)⁻¹) ^ a * ((g ^ 2)⁻¹) ^ b := by
  have hA0 : 0 ≤ (W : ℝ)⁻¹ := by positivity
  have hA1 : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hW)
  have hB0 : 0 ≤ (g ^ 2)⁻¹ := by positivity
  have hB1 : (g ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  conv_lhs => rw [p.as_sum]
  rw [map_sum, cuL, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  refine (cu_norm_eval_monomial hW hg hX d _).trans ?_
  have h1 := pow_le_pow_of_le_one hA0 hA1 (h d hd).1
  have h2 := pow_le_pow_of_le_one hB0 hB1 (h d hd).2
  have := norm_nonneg (p.coeff d)
  gcongr

/-! ### The corrected coordinates and the inverse substitution modulo `(γ^n)` -/

private lemma cu_corrStep_eq (E : ℝ) (N s : ℕ) (σ : ObsVar → ObsPoly) {v : ObsVar}
    (hw : v ≠ .w) (hγ : v ≠ .γ) :
    corrStep E N s σ v = truncG N (σ v + bind₁ σ (oppDiv E v.idx
      (weightedHomogeneousComponent ObsVar.gamWt s
        (truncG N (bind₁ (revCoord N σ N) (updPoly E N (σ v))))))) := by
  cases v with
  | m k => rfl
  | f k => rfl
  | w => exact absurd rfl hw
  | γ => exact absurd rfl hγ

private lemma cu_aux_γ (E : ℝ) (N : ℕ) : ∀ s, corrCoordAux E N s .γ = X .γ
  | 0 => rfl
  | _ + 1 => rfl

private lemma cu_aux_w (E : ℝ) (N : ℕ) : ∀ s, corrCoordAux E N s .w = X .w
  | 0 => rfl
  | _ + 1 => rfl

private lemma cu_corr_γ (E : ℝ) (R : ℕ) : corrCoord E R .γ = X .γ := cu_aux_γ E (R + 2) (R + 2)

private lemma cu_rev_γ {N : ℕ} (hN : 1 ≤ N) {σ : ObsVar → ObsPoly} (hσ : σ .γ = X .γ) :
    ∀ r, revCoord N σ r .γ = X .γ
  | 0 => rfl
  | r + 1 => by
    rw [revCoord]
    dsimp only
    rw [hσ, sub_self, map_zero, sub_zero]
    exact cu_truncG_Xγ hN

private lemma cu_inv_γ (E : ℝ) (R : ℕ) : invCoord E R .γ = X .γ :=
  cu_rev_γ (by omega) (cu_corr_γ E R) (R + 2)

/-- `M_k − m_k`, `F_k − f_k` (and `0` for `w`, `γ`) are of order `g⁻²`. -/
private lemma cu_corr_sub_mem (E : ℝ) (R : ℕ) (u : ObsVar) : corrCoord E R u - X u ∈ cuI 1 := by
  cases u with
  | m k =>
    have h := cu_sub_truncG_mem 0 (corrObsM E R k)
    rw [(corrObs_form E R k).1] at h
    exact h
  | f k =>
    have h := cu_sub_truncG_mem 0 (corrObsF E R k)
    rw [(corrObs_form E R k).2.2.2.1] at h
    exact h
  | w =>
    rw [corrCoord, cu_aux_w, sub_self]
    exact Ideal.zero_mem _
  | γ =>
    rw [cu_corr_γ, sub_self]
    exact Ideal.zero_mem _

/-- The coordinate reversion (11.46) [lg:eq:coordinate-reversion] inverts `σ` to the order of
the step: `σ(x^{[r]}) = x + O(γ^{r+1})`. -/
private lemma cu_inv_subst {N : ℕ} (hN : 1 ≤ N) {σ : ObsVar → ObsPoly} (hγ : σ .γ = X .γ)
    (h1 : ∀ u, σ u - X u ∈ cuI 1) :
    ∀ r, r ≤ N → ∀ u, bind₁ σ (revCoord N σ r u) - X u ∈ cuI (r + 1) := by
  intro r
  induction r with
  | zero =>
    intro _ u
    simpa [revCoord] using h1 u
  | succ r ih =>
    intro hr u
    have ih' := ih (by omega)
    rw [revCoord]
    set Y := X u - bind₁ (revCoord N σ r) (σ u - X u) with hY
    have e1 : bind₁ σ (truncG N Y) - bind₁ σ Y ∈ cuI (r + 1 + 1) := by
      rw [← map_sub]
      refine cu_bind_mem_I hγ (cu_I_mono (n := N + 1) (by omega) ?_)
      have := cu_sub_truncG_mem N Y
      rw [← neg_sub]
      exact Submodule.neg_mem _ this
    have hτγ : (fun i => bind₁ σ (revCoord N σ r i)) .γ = X .γ := by
      simp only
      rw [cu_rev_γ hN hγ, bind₁_X_right, hγ]
    have e2 : bind₁ σ Y - X u ∈ cuI (r + 1 + 1) := by
      have h := cu_bind_sub_mem_I (fun i => ih' i) hτγ (h1 u)
      have e : bind₁ σ Y - X u = -((bind₁ fun i => bind₁ σ (revCoord N σ r i)) (σ u - X u) -
          (σ u - X u)) := by
        rw [hY, map_sub, bind₁_X_right, bind₁_bind₁]
        ring
      rw [e]
      exact Submodule.neg_mem _ h
    have e3 : bind₁ σ (truncG N Y) - X u =
        (bind₁ σ (truncG N Y) - bind₁ σ Y) + (bind₁ σ Y - X u) := by ring
    rw [e3]
    exact Ideal.add_mem _ e1 e2

/-- `σ(m^{[R+2]}(M)) = m + O(g^{−2R−6})` for the corrected coordinates. -/
private lemma cu_corr_inv (E : ℝ) (R : ℕ) (u : ObsVar) :
    bind₁ (corrCoord E R) (invCoord E R u) - X u ∈ cuI (R + 3) :=
  cu_inv_subst (by omega) (cu_corr_γ E R) (cu_corr_sub_mem E R) (R + 2) le_rfl u

/-- The corrected update in the original coordinates is `[P_g M_k]_{≤R+2,0} + O(g^{−2R−6})`. -/
private lemma cu_corrUpd_sub_mem (E : ℝ) (R : ℕ) (v : ObsVar) :
    bind₁ (corrCoord E R) (corrUpd E R v) - updPoly E (R + 2) (corrCoord E R v) ∈ cuI (R + 3) := by
  set U := updPoly E (R + 2) (corrCoord E R v)
  set Y := bind₁ (invCoord E R) U
  have e1 : bind₁ (corrCoord E R) (truncG (R + 2) Y) - bind₁ (corrCoord E R) Y ∈ cuI (R + 3) := by
    rw [← map_sub]
    refine cu_bind_mem_I (cu_corr_γ E R) ?_
    rw [← neg_sub]
    exact Submodule.neg_mem _ (cu_sub_truncG_mem _ Y)
  have hτγ : (fun i => bind₁ (corrCoord E R) (invCoord E R i)) .γ = X .γ := by
    simp only
    rw [cu_inv_γ, bind₁_X_right, cu_corr_γ]
  have e2 : bind₁ (corrCoord E R) Y - U ∈ cuI (R + 3) := by
    have h := cu_bind_sub_mem_I (fun i => cu_corr_inv E R i) hτγ (cu_mem_I_zero U)
    rw [add_zero] at h
    rw [bind₁_bind₁]
    exact h
  have e3 : bind₁ (corrCoord E R) (corrUpd E R v) - U =
      (bind₁ (corrCoord E R) (truncG (R + 2) Y) - bind₁ (corrCoord E R) Y) +
        (bind₁ (corrCoord E R) Y - U) := by
    rw [corrUpd]
    ring
  rw [e3]
  exact Ideal.add_mem _ e1 e2

/-! ### The leading terms modulo `γ²` -/

/-- The first correction of (11.49) [lg:eq:observable-correction]: the opposite-parity part of
the order-`g⁻²` update of `x_v`, divided. -/
private def cuD (E : ℝ) (N : ℕ) (v : ObsVar) : ObsPoly :=
  oppDiv E v.idx (weightedHomogeneousComponent ObsVar.gamWt 1
    (truncG N (bind₁ (revCoord N X N) (updPoly E N (X v)))))

private lemma cu_support_D (E : ℝ) (N : ℕ) (v : ObsVar) :
    ∀ d ∈ (cuD E N v).support, ¬Even (obsDeg d - v.idx) ∧ d .γ = 1 := by
  intro d hd
  obtain ⟨h1, h2⟩ := cu_support_oppDiv _ _ _ d hd
  refine ⟨h2, ?_⟩
  rw [mem_support_iff, cu_coeff_comp] at h1
  by_contra h
  exact h1 (by simp [h])

private lemma cu_aux_two (E : ℝ) {N : ℕ} (hN : 1 ≤ N) {v : ObsVar} (hw : v ≠ .w) (hγ : v ≠ .γ) :
    ∀ s, 1 ≤ s → corrCoordAux E N s v - (X v + cuD E N v) ∈ cuI 2 := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base =>
    change corrStep E N 1 X v - _ ∈ _
    rw [cu_corrStep_eq E N 1 X hw hγ, bind₁_X_left, AlgHom.id_apply]
    have h := cu_sub_truncG_mem N (X v + cuD E N v)
    rw [← neg_sub]
    exact Submodule.neg_mem _ (cu_I_mono (by omega) h)
  | succ s hs ih =>
    change corrStep E N (s + 1) (corrCoordAux E N s) v - _ ∈ _
    rw [cu_corrStep_eq E N (s + 1) _ hw hγ]
    set σ := corrCoordAux E N s
    set Z := σ v + bind₁ σ (oppDiv E v.idx (weightedHomogeneousComponent ObsVar.gamWt (s + 1)
      (truncG N (bind₁ (revCoord N σ N) (updPoly E N (σ v))))))
    have hin : bind₁ σ (oppDiv E v.idx (weightedHomogeneousComponent ObsVar.gamWt (s + 1)
        (truncG N (bind₁ (revCoord N σ N) (updPoly E N (σ v)))))) ∈ cuI 2 := by
      refine cu_bind_mem_I (cu_aux_γ E N s) (cu_mem_I.mpr fun d hd => ?_)
      obtain ⟨h1, -⟩ := cu_support_oppDiv _ _ _ d hd
      rw [mem_support_iff, cu_coeff_comp] at h1
      by_contra h
      exact h1 (by simp [show ¬d .γ = s + 1 by omega])
    have h := cu_sub_truncG_mem N Z
    have e : truncG N Z - (X v + cuD E N v) =
        -(Z - truncG N Z) + (σ v - (X v + cuD E N v)) + (Z - σ v) := by ring
    rw [e]
    refine Ideal.add_mem _ (Ideal.add_mem _ (Submodule.neg_mem _ (cu_I_mono (by omega) h)) ih) ?_
    simp only [Z, add_sub_cancel_left]
    exact hin

private lemma cu_corr_two (E : ℝ) (R : ℕ) {v : ObsVar} (hw : v ≠ .w) (hγ : v ≠ .γ) :
    corrCoord E R v - (X v + cuD E (R + 2) v) ∈ cuI 2 :=
  cu_aux_two E (by omega) hw hγ (R + 2) (by omega)

/-- The reversion to first order: `x^{[r]} = y − Δ(y) + O(γ²)` for `r ≥ 1`. -/
private lemma cu_rev_two {N : ℕ} (hN : 1 ≤ N) {σ : ObsVar → ObsPoly} (hσγ : σ .γ = X .γ)
    (h1 : ∀ u, σ u - X u ∈ cuI 1) :
    ∀ r, (∀ u, revCoord N σ r u - X u ∈ cuI 1) ∧
      (1 ≤ r → ∀ u, revCoord N σ r u - (X u - (σ u - X u)) ∈ cuI 2) := by
  intro r
  induction r with
  | zero =>
    refine ⟨fun u => ?_, fun h => absurd h (by omega)⟩
    simp only [revCoord, sub_self]
    exact Ideal.zero_mem _
  | succ r ih =>
    have hsec : ∀ u, revCoord N σ (r + 1) u - (X u - (σ u - X u)) ∈ cuI 2 := by
      intro u
      rw [revCoord]
      set Y := X u - bind₁ (revCoord N σ r) (σ u - X u)
      have hb := cu_bind_sub_mem_I ih.1 (cu_rev_γ hN hσγ r) (h1 u)
      have h := cu_sub_truncG_mem N Y
      have e : truncG N Y - (X u - (σ u - X u)) =
          -(Y - truncG N Y) - (bind₁ (revCoord N σ r) (σ u - X u) - (σ u - X u)) := by
        simp only [Y]
        ring
      rw [e]
      exact Ideal.sub_mem _ (Submodule.neg_mem _ (cu_I_mono (by omega) h)) hb
    refine ⟨fun u => ?_, fun _ => hsec⟩
    have e : revCoord N σ (r + 1) u - X u =
        (revCoord N σ (r + 1) u - (X u - (σ u - X u))) - (σ u - X u) := by ring
    rw [e]
    exact Ideal.sub_mem _ (cu_I_mono (by omega) (hsec u)) (h1 u)

/-! ### Parity parts -/

private lemma cu_par_ext {k : ℤ} {p q : ObsPoly}
    (h : ∀ d, (if Even (obsDeg d - k) then p.coeff d else 0) = q.coeff d) :
    parityPart k p = q := by
  ext d
  rw [cu_coeff_parityPart]
  exact h d

private lemma cu_par_add (k : ℤ) (p q : ObsPoly) :
    parityPart k (p + q) = parityPart k p + parityPart k q :=
  cu_par_ext fun d => by
    rw [cu_coeff_add, cu_coeff_add, cu_coeff_parityPart, cu_coeff_parityPart]
    split_ifs <;> simp

private lemma cu_par_sub (k : ℤ) (p q : ObsPoly) :
    parityPart k (p - q) = parityPart k p - parityPart k q :=
  cu_par_ext fun d => by
    rw [coeff_sub, coeff_sub, cu_coeff_parityPart, cu_coeff_parityPart]
    split_ifs <;> simp

private lemma cu_par_C_mul (k : ℤ) (a : ℂ) (p : ObsPoly) :
    parityPart k (C a * p) = C a * parityPart k p :=
  cu_par_ext fun d => by
    rw [coeff_C_mul, coeff_C_mul, cu_coeff_parityPart]
    split_ifs <;> simp

private lemma cu_obsDeg_sub_γ {d : ObsVar →₀ ℕ} (h : ObsVar.γ ∈ d.support) :
    obsDeg (d - Finsupp.single ObsVar.γ 1) = obsDeg d := by
  have hle : Finsupp.single ObsVar.γ 1 ≤ d :=
    Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp h))
  have e : obsDeg d =
      obsDeg (d - Finsupp.single ObsVar.γ 1) + obsDeg (Finsupp.single ObsVar.γ 1) := by
    unfold obsDeg
    rw [← map_add, tsub_add_cancel_of_le hle]
  rw [e]
  simp [obsDeg, Finsupp.weight_apply, Finsupp.sum_single_index, ObsVar.idx]

private lemma cu_par_γ_mul (k : ℤ) (p : ObsPoly) :
    parityPart k (X .γ * p) = X .γ * parityPart k p :=
  cu_par_ext fun d => by
    rw [mul_comm, coeff_mul_X', mul_comm, coeff_mul_X']
    split_ifs with h1 h2 h3 <;> simp_all [cu_coeff_parityPart, cu_obsDeg_sub_γ]

private lemma cu_par_X (v : ObsVar) : parityPart v.idx (X v) = X v :=
  cu_par_ext fun d => by
    by_cases hd : Finsupp.single v 1 = d
    · subst hd
      have : Even (obsDeg (Finsupp.single v 1) - v.idx) := by
        simp [obsDeg, Finsupp.weight_apply, Finsupp.sum_single_index]
      simp [this]
    · simp only [coeff_X, hd, ↓reduceIte, ite_self]

private lemma cu_par_eq_zero {k : ℤ} {p : ObsPoly}
    (h : ∀ d ∈ p.support, ¬Even (obsDeg d - k)) : parityPart k p = 0 :=
  cu_par_ext fun d => by
    have h00 : (0 : ObsPoly).coeff d = 0 := by simp
    rw [h00]
    split_ifs with he
    · by_contra h0
      exact h d (mem_support_iff.mpr h0) he
    · rfl

private lemma cu_par_truncG (k : ℤ) (N : ℕ) (p : ObsPoly) :
    parityPart k (truncG N p) = truncG N (parityPart k p) := by
  ext d
  rw [cu_coeff_parityPart, cu_coeff_truncG, cu_coeff_truncG, cu_coeff_parityPart]
  split_ifs <;> rfl

private lemma cu_zeroW_rot_support (E : ℝ) (p : ObsPoly) :
    (zeroW (rotPoly E p)).support ⊆ p.support := by
  intro d hd
  rw [mem_support_iff, cu_coeff_zeroW] at hd
  split_ifs at hd
  · exact cu_support_rotPoly E p (mem_support_iff.mpr hd)
  · exact absurd rfl hd

private lemma cu_truncG_γ_free {N : ℕ} (hN : 1 ≤ N) (a b : ℂ) (v : ObsVar) (hv : v.gamWt = 0)
    {P : ObsPoly} (hP : ∀ d ∈ P.support, d .γ = 0) :
    truncG N (C a * X v + C b * X .γ * P) = C a * X v + C b * X .γ * P := by
  ext d
  rw [cu_coeff_truncG]
  split_ifs with h
  · rfl
  · rw [show C b * X .γ * P = C b * (P * X .γ) by ring, cu_coeff_add, coeff_C_mul, coeff_X,
      coeff_C_mul, coeff_mul_X']
    have h1 : ¬Finsupp.single v 1 = d := by
      rintro rfl
      cases v <;> simp_all [ObsVar.gamWt]
    simp only [h1, ↓reduceIte]
    split_ifs with h2
    · have h3 : P.coeff (d - Finsupp.single ObsVar.γ 1) = 0 := by
        by_contra h0
        have := hP _ (mem_support_iff.mpr h0)
        simp at this
        omega
      simp [h3]
    · simp

/-! ### The leading retained map -/

private lemma cu_inv_two (E : ℝ) (R : ℕ) : (∀ u, invCoord E R u - X u ∈ cuI 1) ∧
    ∀ u, invCoord E R u - (X u - (corrCoord E R u - X u)) ∈ cuI 2 := by
  have h := cu_rev_two (N := R + 2) (by omega) (cu_corr_γ E R) (cu_corr_sub_mem E R) (R + 2)
  unfold invCoord
  exact ⟨h.1, h.2 (by omega)⟩

/-- Modulo `γ²`, an update `U = [ρ^*[P_g p]_{≤N,0}]_{≤N}` of `p = x_v + D + O(γ²)` with an
opposite-parity first correction `D` and `ρ = x − (p − x) + O(γ²)` has parity-`v` part
`λ_v x_v + h² γ λ_v [π₀ q₁(x_v)]_v` up to order `γ`. -/
private lemma cu_lead_abs (E : ℝ) {N : ℕ} (hN : 1 ≤ N) {v : ObsVar} (hw : v ≠ .w)
    {ρ : ObsVar → ObsPoly} {p D U : ObsPoly} (hργ : ρ .γ = X .γ) (hρ1 : ∀ u, ρ u - X u ∈ cuI 1)
    (hρ2 : ρ v - (X v - (p - X v)) ∈ cuI 2) (hΔI : p - X v ∈ cuI 1)
    (hpD : p - (X v + D) ∈ cuI 2) (hD : ∀ d ∈ D.support, ¬Even (obsDeg d - v.idx))
    (hU : U = truncG N (bind₁ ρ (updPoly E N p))) (hpar : parityPart v.idx U = U) :
    truncG 1 U = truncG 1 (C ((-normalPhase E) ^ v.idx) * X v +
      C (((normalH E ^ 2 : ℝ) : ℂ)) * X .γ *
        (C ((-normalPhase E) ^ v.idx) * parityPart v.idx (zeroW (wickMap 1 (X v))))) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  set c : ℂ := (-normalPhase E) ^ v.idx with hc
  set h2 : ℂ := ((normalH E ^ 2 : ℝ) : ℂ) with hh2
  set Δ := p - X v with hΔ
  set Dg := zeroW (wickMap 1 (X v)) with hDg
  set U0 := updPoly E (M + 1) p with hU0
  have hγI : (X .γ : ObsPoly) ∈ cuI 1 := by simpa using cu_pow_mem_I 1
  have hzr : ∀ {n : ℕ} {q : ObsPoly}, q ∈ cuI n → zeroW (rotPoly E q) ∈ cuI n := fun hq =>
    cu_map_mem_I zeroW cu_zeroW_γ (cu_map_mem_I (rotPoly E) (cu_rotPoly_γ E) hq)
  -- the update modulo `γ²`
  set f : ℕ → ObsPoly := fun r => C (((normalH E ^ (2 * r) : ℝ) : ℂ)) * X .γ ^ r *
    zeroW (wickMap r (rotPoly E p)) with hf
  have hU0f : U0 = truncG (M + 1) (∑ r ∈ Finset.range (M + 1 + 1), f r) := rfl
  have hrot : rotPoly E p = C c * X v + rotPoly E Δ := by
    rw [show p = X v + Δ by rw [hΔ]; ring, map_add, cu_rotPoly_X]
  have hf0 : f 0 = C c * X v + zeroW (rotPoly E Δ) := by
    simp only [hf, mul_zero, pow_zero, Complex.ofReal_one, map_one, one_mul,
      (wickMap_zero_incWick_zero _).1, hrot, map_add, map_mul, cu_zeroW_C, cu_zeroW_X hw]
  have hf1 : f 1 = C h2 * X .γ * (C c * Dg) + C h2 * X .γ * zeroW (wickMap 1 (rotPoly E Δ)) := by
    have hw1 : wickMap 1 (rotPoly E p) = c • wickMap 1 (X v) + wickMap 1 (rotPoly E Δ) := by
      rw [hrot, C_mul', ← cuW_apply, ← cuW_apply, ← cuW_apply, map_add, map_smul]
    simp only [hf, mul_one, pow_one, hw1, map_add, map_smul, C_mul', hDg]
    ring
  have hrest : ∀ i, f (i + 1 + 1) ∈ cuI 2 := by
    intro i
    simp only [hf]
    refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (cu_I_mono (n := i + 1 + 1)
      (by omega) (cu_pow_mem_I _)))
  have hstepU : U0 - (C c * X v + zeroW (rotPoly E Δ) + C h2 * X .γ * (C c * Dg)) ∈ cuI 2 := by
    have hT := cu_sub_truncG_mem (M + 1) (∑ r ∈ Finset.range (M + 1 + 1), f r)
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at hT
    rw [hU0f, Finset.sum_range_succ', Finset.sum_range_succ']
    set S2 := ∑ i ∈ Finset.range M, f (i + 1 + 1)
    have hS2 : S2 ∈ cuI 2 := Ideal.sum_mem _ fun i _ => hrest i
    have hz1 : C h2 * X .γ * zeroW (wickMap 1 (rotPoly E Δ)) ∈ cuI 2 :=
      cu_mul_mem_I (a := 1) (b := 1) (Ideal.mul_mem_left _ _ hγI) (cu_map_mem_I zeroW cu_zeroW_γ
        (cu_wick_mem_I 1 (cu_map_mem_I (rotPoly E) (cu_rotPoly_γ E) hΔI)))
    have e : truncG (M + 1) (S2 + f (0 + 1) + f 0) -
        (C c * X v + zeroW (rotPoly E Δ) + C h2 * X .γ * (C c * Dg)) =
        -((S2 + f (0 + 1) + f 0) - truncG (M + 1) (S2 + f (0 + 1) + f 0)) + S2 +
          C h2 * X .γ * zeroW (wickMap 1 (rotPoly E Δ)) := by
      rw [zero_add, hf0, hf1]
      ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.add_mem _ (Submodule.neg_mem _ (cu_I_mono (by omega) hT)) hS2) hz1
  -- substitution of the inverse coordinates
  set Q := C h2 * X .γ * (C c * Dg) with hQ
  have hQI : Q ∈ cuI 1 := by
    rw [hQ, mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hγI)
  set A := C c * (X v - Δ) + zeroW (rotPoly E Δ) + Q with hA
  have hstepρ : bind₁ ρ U0 - A ∈ cuI 2 := by
    have h1 : bind₁ ρ U0 - bind₁ ρ (C c * X v + zeroW (rotPoly E Δ) + Q) ∈ cuI 2 := by
      rw [← map_sub]
      exact cu_bind_mem_I hργ hstepU
    have h2' : bind₁ ρ (zeroW (rotPoly E Δ)) - zeroW (rotPoly E Δ) ∈ cuI (1 + 1) :=
      cu_bind_sub_mem_I hρ1 hργ (hzr hΔI)
    have h3 : bind₁ ρ Q - Q ∈ cuI (1 + 1) := cu_bind_sub_mem_I hρ1 hργ hQI
    have h4 : C c * (ρ v - (X v - Δ)) ∈ cuI 2 := Ideal.mul_mem_left _ _ hρ2
    have e : bind₁ ρ U0 - A = (bind₁ ρ U0 - bind₁ ρ (C c * X v + zeroW (rotPoly E Δ) + Q)) +
        C c * (ρ v - (X v - Δ)) + (bind₁ ρ (zeroW (rotPoly E Δ)) - zeroW (rotPoly E Δ)) +
          (bind₁ ρ Q - Q) := by
      rw [hA, map_add, map_add, map_mul, bind₁_C_right, bind₁_X_right]
      ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ h1 h4) h2') h3
  -- the first correction in place of `Δ`
  set A' := C c * (X v - D) + zeroW (rotPoly E D) + Q with hA'
  have hstepD : A - A' ∈ cuI 2 := by
    have hΔD : Δ - D ∈ cuI 2 := by
      convert hpD using 1
      rw [hΔ]
      ring
    have e : A - A' = -(C c * (Δ - D)) + zeroW (rotPoly E (Δ - D)) := by
      rw [hA, hA', map_sub (rotPoly E) Δ D, map_sub zeroW]
      ring
    rw [e]
    exact Ideal.add_mem _ (Submodule.neg_mem _ (Ideal.mul_mem_left _ _ hΔD)) (hzr hΔD)
  have htr : truncG 1 U = truncG 1 A' := by
    rw [hU, cu_truncG_truncG (by omega)]
    refine cu_truncG_congr ?_
    have e : bind₁ ρ (updPoly E (M + 1) p) - A' = (bind₁ ρ U0 - A) + (A - A') := by ring
    rw [e]
    exact Ideal.add_mem _ hstepρ hstepD
  -- the parity-`v` part
  have hDpar : parityPart v.idx D = 0 := cu_par_eq_zero hD
  have hzDpar : parityPart v.idx (zeroW (rotPoly E D)) = 0 :=
    cu_par_eq_zero fun d hd => hD d (cu_zeroW_rot_support E D hd)
  have hA'par : parityPart v.idx A' =
      C c * X v + C h2 * X .γ * (C c * parityPart v.idx Dg) := by
    rw [hA', hQ, show C h2 * X .γ * (C c * Dg) = C h2 * (X .γ * (C c * Dg)) by ring, cu_par_add,
      cu_par_add, cu_par_C_mul, cu_par_sub, cu_par_X, hDpar, hzDpar, cu_par_C_mul, cu_par_γ_mul,
      cu_par_C_mul]
    ring
  rw [← hpar, ← cu_par_truncG, htr, cu_par_truncG, hA'par]

/-- Polynomials in which the variable `v` does not occur. -/
private lemma cu_free {s : Set ObsVar} {v : ObsVar} (hv : v ∉ s) {P : ObsPoly}
    (h : P ∈ supported ℂ s) : ∀ d ∈ P.support, d v = 0 := by
  intro d hd
  by_contra h0
  rw [mem_supported] at h
  exact hv (h ((mem_vars_iff_mem_support _).mpr ⟨d, hd, Finsupp.mem_support_iff.mpr h0⟩))

private lemma cu_var_mem (a : ℤ) : mVar a ∈ supported ℂ {v : ObsVar | v ≠ .γ} ∧
    fVar a ∈ supported ℂ {v : ObsVar | v ≠ .γ} := by
  unfold mVar fVar
  split_ifs
  · exact ⟨Subalgebra.one_mem _, Subalgebra.one_mem _⟩
  · exact ⟨X_mem_supported.mpr (fun h => ObsVar.noConfusion h),
      X_mem_supported.mpr (fun h => ObsVar.noConfusion h)⟩

private lemma cu_C_mem (a : ℂ) : C a ∈ supported ℂ {v : ObsVar | v ≠ .γ} :=
  Subalgebra.algebraMap_mem _ a

private lemma cu_centerTrace_mem (k : ℕ) : centerTrace k ∈ supported ℂ {v : ObsVar | v ≠ .γ} := by
  unfold centerTrace
  exact Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (Subalgebra.sub_mem _
    (Subalgebra.mul_mem _ (Subalgebra.neg_mem _ (cu_C_mem _)) (cu_var_mem _).1)
    (Subalgebra.mul_mem _ (cu_C_mem _) (Subalgebra.sum_mem _ fun _ _ =>
      Subalgebra.mul_mem _ (cu_var_mem _).1 (cu_var_mem _).1)))
    (Subalgebra.mul_mem _ (cu_C_mem _) (Subalgebra.sum_mem _ fun _ _ =>
      Subalgebra.mul_mem _ (cu_var_mem _).1 (cu_var_mem _).1)))
    (Subalgebra.mul_mem _ (cu_C_mem _) (Subalgebra.sum_mem _ fun _ _ =>
      Subalgebra.mul_mem _ (cu_var_mem _).1 (cu_var_mem _).1))

private lemma cu_centerCorner_mem (k : ℕ) :
    centerCorner k ∈ supported ℂ {v : ObsVar | v ≠ .γ} := by
  have hS : ∀ s : Finset ℕ, ∀ e : ℕ → ℤ, (∑ n ∈ s, C (n : ℂ) * fVar n * mVar (e n)) ∈
      supported ℂ {v : ObsVar | v ≠ .γ} := fun s e => Subalgebra.sum_mem _ fun _ _ =>
    Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (cu_C_mem _) (cu_var_mem _).2) (cu_var_mem _).1
  have hB : (if 3 ≤ k then C ((k : ℂ) - 2) * fVar ((k : ℤ) - 2) else 0) ∈
      supported ℂ {v : ObsVar | v ≠ .γ} := by
    split_ifs
    · exact Subalgebra.mul_mem _ (cu_C_mem _) (cu_var_mem _).2
    · exact Subalgebra.zero_mem _
  unfold centerCorner
  exact Subalgebra.add_mem _ (Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (Subalgebra.sub_mem _
    (Subalgebra.sub_mem _ (Subalgebra.mul_mem _ (Subalgebra.neg_mem _ (cu_C_mem _))
      (cu_var_mem _).2) hB) (hS _ _)) (Subalgebra.mul_mem _ (cu_C_mem _) (hS _ _))) (hS _ _))
    (Subalgebra.mul_mem _ (cu_var_mem _).2 (Subalgebra.add_mem _
      (Subalgebra.mul_mem _ (cu_var_mem _).1 (cu_var_mem _).2)
      (Subalgebra.mul_mem _ (cu_var_mem _).1 (cu_var_mem _).2)))

private lemma cu_lead_final (E : ℝ) (R : ℕ) {v : ObsVar} (hw : v ≠ .w) (hγ : v ≠ .γ)
    (hpar : parityPart v.idx (corrUpd E R v) = corrUpd E R v) {P : ObsPoly}
    (hP : parityPart v.idx (zeroW (wickMap 1 (X v))) = P)
    (hPm : P ∈ supported ℂ {v : ObsVar | v ≠ .γ}) :
    truncG 1 (corrUpd E R v) = C ((-normalPhase E) ^ v.idx) *
      (X v + C (((normalH E ^ 2 : ℝ) : ℂ)) * X .γ * P) := by
  rw [cu_lead_abs E (N := R + 2) (U := corrUpd E R v) (by omega) hw (cu_inv_γ E R)
    (cu_inv_two E R).1 ((cu_inv_two E R).2 v) (cu_corr_sub_mem E R v) (cu_corr_two E R hw hγ)
    (fun d hd => (cu_support_D E _ v d hd).1) rfl hpar, hP, cu_truncG_γ_free le_rfl _ _ v
    (by cases v <;> simp_all [ObsVar.gamWt])
    (cu_free (by simp) (Subalgebra.mul_mem _ (cu_C_mem _) hPm))]
  ring

/-! ### Measurability and linearity of `P_g` on polynomials -/

private lemma cu_measurable_gb (W : ℕ) : Measurable fun ω : Ω W 1 => gueBlock W 1 ω 0 := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

private lemma cu_cont_vecForm {W : ℕ} :
    Continuous fun q : Matrix (Fin W) (Fin W) ℂ × EuclideanSpace ℂ (Fin W) => vecForm q.1 q.2 := by
  have hc : Continuous (fun q : Matrix (Fin W) (Fin W) ℂ × EuclideanSpace ℂ (Fin W) =>
      Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) q.1 q.2) :=
    Matrix.continuous_uncurry_toEuclideanCLM
  exact continuous_snd.inner hc

private lemma cu_measurable_inv {W : ℕ} :
    Measurable fun X : Matrix (Fin W) (Fin W) ℂ => X⁻¹ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  have h : (fun X : Matrix (Fin W) (Fin W) ℂ => X⁻¹ i j) =
      fun X => (X.det)⁻¹ * X.adjugate i j := by
    funext X
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [h]
  have hd : Continuous fun X : Matrix (Fin W) (Fin W) ℂ => X.det := continuous_id.matrix_det
  have ha : Continuous fun X : Matrix (Fin W) (Fin W) ℂ => X.adjugate i j :=
    (continuous_id.matrix_adjugate).matrix_elem i j
  exact hd.measurable.inv.mul ha.measurable

private lemma cu_measurable_zpow {W : ℕ} (k : ℤ) :
    Measurable fun A : Matrix (Fin W) (Fin W) ℂ => A ^ k := by
  cases k with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact (continuous_id.pow n).measurable
  | negSucc n =>
    simp only [zpow_negSucc]
    exact cu_measurable_inv.comp (continuous_id.pow _).measurable

private lemma cu_measurable_obsEval (g : ℝ) (W : ℕ) (p : ObsPoly) :
    Measurable fun X : State W => obsEval g X p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [obsEval, aeval_C]; exact measurable_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p v hp =>
    simp only [map_mul]
    refine hp.mul ?_
    cases v with
    | m k =>
      simp only [obsEval, aeval_X, obsM]
      exact measurable_const.mul ((continuous_id.matrix_trace).measurable.comp
        ((cu_measurable_zpow k.1).comp measurable_fst))
    | f k =>
      simp only [obsEval, aeval_X, obsF]
      have h1 : Measurable fun X : State W => (X.1 ^ k.1, X.2) :=
        ((cu_measurable_zpow k.1).comp measurable_fst).prodMk measurable_snd
      have h2 := (cu_cont_vecForm (W := W)).measurable.comp h1
      exact h2
    | w => simp only [obsEval, aeval_X]; exact measurable_const
    | γ => simp only [obsEval, aeval_X]; exact measurable_const

private lemma cu_integrable (g E : ℝ) {W : ℕ} (hW : 1 ≤ W) (hg : 1 ≤ g) {X : State W}
    (hX : IsState X) (p : ObsPoly) :
    Integrable (fun ω : Ω W 1 => obsEval g (stepState g E X (gueBlock W 1 ω 0)) p) (μ W 1) := by
  have hS : Measurable fun V : Matrix (Fin W) (Fin W) ℂ => (X, V) :=
    Measurable.prodMk measurable_const measurable_id
  have hm : Measurable fun ω : Ω W 1 => obsEval g (stepState g E X (gueBlock W 1 ω 0)) p :=
    (cu_measurable_obsEval g W p).comp (((measurable_stepState g E W).comp hS).comp
      (cu_measurable_gb W))
  exact Integrable.of_bound hm.aestronglyMeasurable (∑ d ∈ p.support, ‖p.coeff d‖)
    (Filter.Eventually.of_forall fun ω =>
      norm_obsEval_le hW hg (isState_stepState g E hX (gueBlock_isHermitian W 1 ω 0)) p)

private lemma cu_monomial_eq (d : ObsVar →₀ ℕ) (a : ℂ) :
    (monomial d a : ObsPoly) = a • monomial d 1 := by
  rw [smul_monomial, smul_eq_mul, mul_one]

private lemma cu_transOp_sum (g E : ℝ) {W : ℕ} (hW : 1 ≤ W) (hg : 1 ≤ g) {X : State W}
    (hX : IsState X) (S : Finset (ObsVar →₀ ℕ)) (c : (ObsVar →₀ ℕ) → ℂ) :
    transOp g E (fun Y => obsEval g Y (∑ d ∈ S, monomial d (c d))) X =
      ∑ d ∈ S, c d * transOp g E (fun Y => obsEval g Y (monomial d 1)) X := by
  unfold transOp
  have hm : ∀ d (Y : State W), obsEval g Y (monomial d (c d)) =
      c d * obsEval g Y (monomial d 1) := by
    intro d Y
    rw [cu_monomial_eq, map_smul, smul_eq_mul]
  simp only [map_sum, hm]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun d _ => integral_const_mul _ _
  · intro d _
    exact (cu_integrable g E hW hg hX _).const_mul _

/-! ### Uniform bounds on the window -/

private lemma cu_normalH {E : ℝ} (hE : |E| ≤ 1) : 0 ≤ normalH E ∧ normalH E ≤ 1 := by
  unfold normalH freeAngle
  rw [Real.sin_arccos]
  have h1 : (E / 2) ^ 2 ≤ 3 / 4 := by
    have := sq_abs E
    nlinarith [abs_nonneg E]
  have h2 : (1 / 2 : ℝ) ≤ √(1 - (E / 2) ^ 2) := by
    rw [show (1 / 2 : ℝ) = √((1 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  refine ⟨by positivity, inv_le_one_of_one_le₀ (by linarith)⟩

/-- The indices of a variable. -/
private def cuIdx : ObsVar → Finset NzInt
  | .m k => {k}
  | .f k => {k}
  | .w => ∅
  | .γ => ∅

/-- One window, one finite support, one coefficient bound for `M_k`, `F_k`, the inverse
polynomials and the corrected updates, and a bound for the corrected coordinates of every
variable that occurs. -/
private lemma cu_data (R : ℕ) (Ks : Finset NzInt) :
    ∃ E₁ : ℝ, 0 < E₁ ∧ E₁ ≤ 1 ∧ ∃ S : Finset (ObsVar →₀ ℕ), ∃ K B : ℝ, 0 ≤ K ∧ 0 ≤ B ∧
      ∀ E : ℝ, |E| ≤ E₁ →
        (∀ k ∈ Ks, ∀ v ∈ [ObsVar.m k, ObsVar.f k],
          (corrCoord E R v).support ⊆ S ∧ (invCoord E R v).support ⊆ S ∧
            (corrUpd E R v).support ⊆ S ∧
            ∀ d, ‖(corrCoord E R v).coeff d‖ ≤ K ∧ ‖(invCoord E R v).coeff d‖ ≤ K ∧
              ‖(corrUpd E R v).coeff d‖ ≤ K) ∧
        ∀ d ∈ S, ∀ u ∈ d.support, cuL (corrCoord E R u) ≤ B := by
  obtain ⟨E₁, hE₁, S, K, hK, h⟩ := corrCoeff_bounded R Ks
  set Ks' := Ks ∪ S.biUnion fun d => d.support.biUnion cuIdx
  obtain ⟨E₂, hE₂, S', K', hK', h'⟩ := corrCoeff_bounded R Ks'
  refine ⟨min (min E₁ E₂) 1, lt_min (lt_min hE₁ hE₂) one_pos, min_le_right _ _, S, K,
    max (S'.card * K') 1, hK.le, le_max_of_le_right zero_le_one, fun E hE => ⟨fun k hk v hv =>
      h E (hE.trans ((min_le_left _ _).trans (min_le_left _ _))) k hk v hv, fun d hd u hu => ?_⟩⟩
  have hE' : |E| ≤ E₂ := hE.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hmem : ∀ k : NzInt, k ∈ cuIdx u → k ∈ Ks' := fun k hk =>
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_biUnion.mpr ⟨u, hu, hk⟩⟩)
  cases u with
  | m k =>
    obtain ⟨hs, -, -, hc⟩ := h' E hE' k (hmem k (by simp [cuIdx])) (.m k) (by simp)
    exact (cuL_le_card hs fun d => (hc d).1).trans (le_max_left _ _)
  | f k =>
    obtain ⟨hs, -, -, hc⟩ := h' E hE' k (hmem k (by simp [cuIdx])) (.f k) (by simp)
    exact (cuL_le_card hs fun d => (hc d).1).trans (le_max_left _ _)
  | w =>
    rw [corrCoord, cu_aux_w]
    exact (cuL_X _).trans (le_max_right _ _)
  | γ =>
    rw [cu_corr_γ]
    exact (cuL_X _).trans (le_max_right _ _)

/-! ### The expansion of `P_g` for a polynomial with bounded coefficients -/

/-- `Σ_{r ≤ N} Σ_{d ∈ S} |q_r(x^d)|₁`. -/
private def cuA (N : ℕ) (S : Finset (ObsVar →₀ ℕ)) : ℝ :=
  ∑ r ∈ Finset.range (N + 1), ∑ d ∈ S, cuL (wickMap r (monomial d 1))

private lemma cuA_nonneg (N : ℕ) (S : Finset (ObsVar →₀ ℕ)) : 0 ≤ cuA N S :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => cuL_nonneg _

private lemma cuL_wick_rot (E : ℝ) {p : ObsPoly} {S : Finset (ObsVar →₀ ℕ)} {K : ℝ}
    (hS : p.support ⊆ S) (hK : ∀ d, ‖p.coeff d‖ ≤ K) (r : ℕ) :
    cuL (wickMap r (rotPoly E p)) ≤ K * ∑ d ∈ S, cuL (wickMap r (monomial d 1)) := by
  have e : wickMap r (rotPoly E p) =
      ∑ d ∈ S, (cuMu E d * p.coeff d) • wickMap r (monomial d 1) := by
    conv_lhs => rw [cu_sum_monomial hS]
    rw [map_sum, ← cuW_apply, map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [cu_rotPoly_monomial, cu_monomial_eq, map_smul, cuW_apply]
  rw [e, Finset.mul_sum]
  refine (cuL_sum_le _ _).trans (Finset.sum_le_sum fun d _ => (cuL_smul _ _).trans ?_)
  rw [norm_mul, cu_norm_mu, one_mul]
  exact mul_le_mul_of_nonneg_right (hK d) (cuL_nonneg _)

private lemma cuL_zeroW_le (q : ObsPoly) : cuL (zeroW q) ≤ cuL q :=
  cuL_filter fun d => cu_coeff_zeroW q d

private lemma cuL_sub_zeroW_le (q : ObsPoly) : cuL (q - zeroW q) ≤ cuL q :=
  cuL_filter (P := fun d => d .w ≠ 0) fun d => by
    rw [coeff_sub, cu_coeff_zeroW]
    split_ifs <;> simp_all

private lemma cuL_truncG_le (N : ℕ) (q : ObsPoly) : cuL (truncG N q) ≤ cuL q :=
  cuL_filter fun d => cu_coeff_truncG N q d

private lemma cuL_sub_truncG_le (N : ℕ) (q : ObsPoly) : cuL (q - truncG N q) ≤ cuL q :=
  cuL_filter (P := fun d => ¬d .γ ≤ N) fun d => by
    rw [coeff_sub, cu_coeff_truncG]
    split_ifs <;> simp_all

/-- The polynomial `Σ_r h^{2r} γ^r π₀ q_r(ρ_θ p)` before truncation. -/
private def cuT (E : ℝ) (N : ℕ) (p : ObsPoly) : ObsPoly :=
  ∑ r ∈ Finset.range (N + 1),
    C (((normalH E ^ (2 * r) : ℝ) : ℂ)) * X .γ ^ r * zeroW (wickMap r (rotPoly E p))

private lemma cuL_T {E : ℝ} (hE : |E| ≤ 1) (N : ℕ) {p : ObsPoly} {S : Finset (ObsVar →₀ ℕ)}
    {K : ℝ} (hS : p.support ⊆ S) (hK : ∀ d, ‖p.coeff d‖ ≤ K) : cuL (cuT E N p) ≤ K * cuA N S := by
  obtain ⟨hh0, hh1⟩ := cu_normalH hE
  rw [cuT, cuA, Finset.mul_sum]
  refine (cuL_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  refine (cuL_mul_le _ _).trans ((mul_le_mul_of_nonneg_left (cuL_zeroW_le _)
    (cuL_nonneg _)).trans ?_)
  have h1 : cuL (C (((normalH E ^ (2 * r) : ℝ) : ℂ)) * X .γ ^ r) ≤ 1 := by
    refine (cuL_C_mul _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h3 : cuL (X ObsVar.γ ^ r) ≤ 1 :=
      (cuL_pow_le _ _).trans (pow_le_one₀ (cuL_nonneg _) (cuL_X _))
    have h4 : normalH E ^ (2 * r) ≤ 1 := pow_le_one₀ hh0 hh1
    nlinarith [cuL_nonneg (X ObsVar.γ ^ r), pow_nonneg hh0 (2 * r)]
  calc _ ≤ 1 * cuL (wickMap r (rotPoly E p)) :=
        mul_le_mul_of_nonneg_right h1 (cuL_nonneg _)
    _ ≤ K * ∑ d ∈ S, cuL (wickMap r (monomial d 1)) := by
        rw [one_mul]
        exact cuL_wick_rot E hS hK r

/-- The expansion (E) of Lemma 11.7 [lg:lem:ideal] for a polynomial `p` with support in `S`
and coefficients bounded by `K`, compared with `[P_g p]_{≤N,0}`: the error is
`K Σ K_d g^{−2N−2}` from the expansion, `g⁻² W^{−a}` from the `W`-dependent terms (all of
`W`-degree `≥ a`) and `g^{−2N−2}` from the truncation. -/
private lemma cu_core {N : ℕ} {S : Finset (ObsVar →₀ ℕ)} {Kd : (ObsVar →₀ ℕ) → ℝ}
    (hKd : ∀ d, ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ 1 → ∀ X : State W, IsState X →
      ‖transOp g E (fun Y => obsEval g Y (monomial d 1)) X - ∑ r ∈ Finset.range (N + 1),
        (((normalH E / g) ^ (2 * r) : ℝ) : ℂ) *
          obsEval g X (wickMap r (rotPoly E (monomial d 1)))‖ ≤ Kd d / g ^ (2 * N + 2))
    {K : ℝ} {a W : ℕ} (hW : 1 ≤ W) {g : ℝ} (hg : 1 ≤ g) {E : ℝ} (hE : |E| ≤ 1) {X : State W}
    (hX : IsState X) {p : ObsPoly} (hS : p.support ⊆ S) (hK : ∀ d, ‖p.coeff d‖ ≤ K)
    (hw0 : ∀ d ∈ p.support, d .w = 0)
    (hwa : ∀ r, 1 ≤ r → ∀ d ∈ (wickMap r (rotPoly E p)).support, d .w ≠ 0 → a ≤ d .w) :
    ‖transOp g E (fun Y => obsEval g Y p) X - obsEval g X (updPoly E N p)‖ ≤
      K * (∑ d ∈ S, Kd d) / g ^ (2 * N + 2) +
        K * cuA N S * ((g ^ 2)⁻¹ * ((W : ℝ)⁻¹) ^ a + ((g ^ 2)⁻¹) ^ (N + 1)) := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hg0 : 0 < g := by linarith
  obtain ⟨hh0, hh1⟩ := cu_normalH hE
  set A : ℕ → ℂ := fun r => (((normalH E / g) ^ (2 * r) : ℝ) : ℂ) with hA
  set Q : ℕ → ObsPoly := fun r => wickMap r (rotPoly E p) with hQ
  set Ex : ℂ := ∑ r ∈ Finset.range (N + 1), A r * obsEval g X (Q r) with hEx
  -- the expansion
  have hP : transOp g E (fun Y => obsEval g Y p) X =
      ∑ d ∈ S, p.coeff d * transOp g E (fun Y => obsEval g Y (monomial d 1)) X := by
    conv_lhs => rw [cu_sum_monomial hS]
    exact cu_transOp_sum g E hW hg hX S _
  have hQd : ∀ r, obsEval g X (Q r) =
      ∑ d ∈ S, p.coeff d * obsEval g X (wickMap r (rotPoly E (monomial d 1))) := by
    intro r
    simp only [hQ]
    conv_lhs => rw [cu_sum_monomial hS]
    rw [map_sum, ← cuW_apply, map_sum, map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [cu_monomial_eq, map_smul, map_smul, map_smul, smul_eq_mul, cuW_apply]
  have hExd : Ex = ∑ d ∈ S, p.coeff d * ∑ r ∈ Finset.range (N + 1),
      A r * obsEval g X (wickMap r (rotPoly E (monomial d 1))) := by
    simp only [hEx, hQd, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun r _ => by ring
  have h1 : ‖transOp g E (fun Y => obsEval g Y p) X - Ex‖ ≤
      K * (∑ d ∈ S, Kd d) / g ^ (2 * N + 2) := by
    rw [hP, hExd, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
    rw [← mul_sub, norm_mul, mul_div_assoc]
    exact mul_le_mul (hK d) (hKd d W hW g hg E hE X hX) (norm_nonneg _) hK0
  -- the `W⁰` part and the truncation
  have hevT : obsEval g X (cuT E N p) =
      ∑ r ∈ Finset.range (N + 1), A r * obsEval g X (zeroW (Q r)) := by
    rw [cuT, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hA' : ((normalH E / g) ^ (2 * r) : ℝ) = normalH E ^ (2 * r) * ((g ^ 2)⁻¹) ^ r := by
      rw [div_pow, pow_mul g, inv_pow, div_eq_mul_inv]
    have hC : ∀ x : ℂ, obsEval g X (C x) = x := fun x => by simp [obsEval]
    have hγ : obsEval g X (MvPolynomial.X .γ) = (((g ^ 2)⁻¹ : ℝ) : ℂ) := by simp [obsEval]
    rw [map_mul, map_mul, map_pow, hC, hγ]
    simp only [hA, hA']
    push_cast
    ring
  have hid : Ex - obsEval g X (updPoly E N p) =
      ∑ r ∈ Finset.range (N + 1), A r * obsEval g X (Q r - zeroW (Q r)) +
        obsEval g X (cuT E N p - truncG N (cuT E N p)) := by
    have hu : updPoly E N p = truncG N (cuT E N p) := rfl
    rw [hu, map_sub (obsEval g X) (cuT E N p), hevT, hEx]
    simp only [map_sub, mul_sub, Finset.sum_sub_distrib]
    ring
  have hWa : ∀ r ∈ Finset.range (N + 1), ‖A r * obsEval g X (Q r - zeroW (Q r))‖ ≤
      (g ^ 2)⁻¹ * ((W : ℝ)⁻¹) ^ a * cuL (Q r) := by
    intro r _
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · have h0 : Q 0 - zeroW (Q 0) = 0 := by
        ext d
        have h00 : (0 : ObsPoly).coeff d = 0 := by simp
        rw [coeff_sub, cu_coeff_zeroW, h00]
        split_ifs with hd
        · exact sub_self _
        · simp only [hQ, (wickMap_zero_incWick_zero _).1, sub_zero]
          by_contra hne
          exact hd (hw0 d (cu_support_rotPoly E p (mem_support_iff.mpr hne)))
      rw [h0, map_zero, mul_zero, norm_zero]
      exact mul_nonneg (by positivity) (cuL_nonneg _)
    · rw [norm_mul]
      have hAr : ‖A r‖ ≤ (g ^ 2)⁻¹ := by
        simp only [hA, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity)]
        have hq0 : 0 ≤ normalH E / g := by positivity
        have hq1 : normalH E / g ≤ 1 / g := div_le_div_of_nonneg_right hh1 hg0.le
        have hq2 : 1 / g ≤ 1 := by rw [div_le_one hg0]; exact hg
        calc (normalH E / g) ^ (2 * r) ≤ (normalH E / g) ^ 2 :=
              pow_le_pow_of_le_one hq0 (hq1.trans hq2) (by omega)
          _ ≤ (1 / g) ^ 2 := pow_le_pow_left₀ hq0 hq1 2
          _ = (g ^ 2)⁻¹ := by rw [one_div, inv_pow]
      have hev : ‖obsEval g X (Q r - zeroW (Q r))‖ ≤ cuL (Q r) * ((W : ℝ)⁻¹) ^ a := by
        refine (cu_norm_eval_le hW hg hX a 0 fun d hd => ⟨?_, Nat.zero_le _⟩).trans ?_
        · rw [mem_support_iff, coeff_sub, cu_coeff_zeroW] at hd
          split_ifs at hd with hdw
          · exact absurd (sub_self _) hd
          · rw [sub_zero] at hd
            exact hwa r hr d (mem_support_iff.mpr hd) hdw
        · rw [pow_zero, mul_one]
          exact mul_le_mul_of_nonneg_right (cuL_sub_zeroW_le _) (by positivity)
      calc ‖A r‖ * ‖obsEval g X (Q r - zeroW (Q r))‖
          ≤ (g ^ 2)⁻¹ * (cuL (Q r) * ((W : ℝ)⁻¹) ^ a) :=
            mul_le_mul hAr hev (norm_nonneg _) (by positivity)
        _ = (g ^ 2)⁻¹ * ((W : ℝ)⁻¹) ^ a * cuL (Q r) := by ring
  have h2 : ‖∑ r ∈ Finset.range (N + 1), A r * obsEval g X (Q r - zeroW (Q r))‖ ≤
      (g ^ 2)⁻¹ * ((W : ℝ)⁻¹) ^ a * (K * cuA N S) := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hWa).trans ?_)
    rw [← Finset.mul_sum, cuA, Finset.mul_sum (s := Finset.range (N + 1)) (a := K)]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r _ => cuL_wick_rot E hS hK r)
      (by positivity)
  have h3 : ‖obsEval g X (cuT E N p - truncG N (cuT E N p))‖ ≤
      K * cuA N S * ((g ^ 2)⁻¹) ^ (N + 1) := by
    refine (cu_norm_eval_le hW hg hX 0 (N + 1) fun d hd =>
      ⟨Nat.zero_le _, cu_mem_I.mp (cu_sub_truncG_mem N _) d hd⟩).trans ?_
    rw [pow_zero, mul_one]
    exact mul_le_mul_of_nonneg_right ((cuL_sub_truncG_le _ _).trans (cuL_T hE N hS hK))
      (by positivity)
  have htri : ‖transOp g E (fun Y => obsEval g Y p) X - obsEval g X (updPoly E N p)‖ ≤
      ‖transOp g E (fun Y => obsEval g Y p) X - Ex‖ +
        (‖∑ r ∈ Finset.range (N + 1), A r * obsEval g X (Q r - zeroW (Q r))‖ +
          ‖obsEval g X (cuT E N p - truncG N (cuT E N p))‖) := by
    have e : transOp g E (fun Y => obsEval g Y p) X - obsEval g X (updPoly E N p) =
        (transOp g E (fun Y => obsEval g Y p) X - Ex) + (Ex - obsEval g X (updPoly E N p)) := by
      ring
    rw [e, hid]
    exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
  have hfin : (g ^ 2)⁻¹ * ((W : ℝ)⁻¹) ^ a * (K * cuA N S) + K * cuA N S * ((g ^ 2)⁻¹) ^ (N + 1) =
      K * cuA N S * ((g ^ 2)⁻¹ * ((W : ℝ)⁻¹) ^ a + ((g ^ 2)⁻¹) ^ (N + 1)) := by ring
  linarith

/-! ### The corrected transition -/

private lemma cu_supported_rot {s : Set ObsVar} {p : ObsPoly} (hp : p ∈ supported ℂ s) (E : ℝ) :
    rotPoly E p ∈ supported ℂ s := by
  rw [mem_supported] at hp ⊢
  intro i hi
  rw [Finset.mem_coe, mem_vars_iff_mem_support] at hi
  obtain ⟨d, hd, hid⟩ := hi
  exact hp ((mem_vars_iff_mem_support _).mpr ⟨d, cu_support_rotPoly E p hd, hid⟩)

/-- (11.57) [lg:eq:widtherrors] for one corrected coordinate `σ_v` whose `W`-dependent
expansion terms have `W`-degree at least `a`. -/
private lemma cu_upd_bound {R : ℕ} {S : Finset (ObsVar →₀ ℕ)} {K B : ℝ}
    {Kd : (ObsVar →₀ ℕ) → ℝ}
    (hKd : ∀ d, ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ 1 → ∀ X : State W, IsState X →
      ‖transOp g E (fun Y => obsEval g Y (monomial d 1)) X - ∑ r ∈ Finset.range (R + 2 + 1),
        (((normalH E / g) ^ (2 * r) : ℝ) : ℂ) *
          obsEval g X (wickMap r (rotPoly E (monomial d 1)))‖ ≤ Kd d / g ^ (2 * (R + 2) + 2))
    (hKd0 : ∀ d, 0 ≤ Kd d) (hB0 : 0 ≤ B) {a W : ℕ} (hW : 1 ≤ W) {g : ℝ} (hg : 1 ≤ g) {E : ℝ}
    (hE : |E| ≤ 1) {X : State W} (hX : IsState X) {v : ObsVar}
    (hs1 : (corrCoord E R v).support ⊆ S) (hs3 : (corrUpd E R v).support ⊆ S)
    (hc1 : ∀ d, ‖(corrCoord E R v).coeff d‖ ≤ K) (hc3 : ∀ d, ‖(corrUpd E R v).coeff d‖ ≤ K)
    (hB : ∀ d ∈ S, ∀ u ∈ d.support, cuL (corrCoord E R u) ≤ B)
    (hw0 : ∀ d ∈ (corrCoord E R v).support, d .w = 0)
    (hwa : ∀ r, 1 ≤ r → ∀ d ∈ (wickMap r (rotPoly E (corrCoord E R v))).support, d .w ≠ 0 →
      a ≤ d .w) :
    ‖transOp g E (fun Y => obsEval g Y (corrCoord E R v)) X -
        obsEval g X (bind₁ (corrCoord E R) (corrUpd E R v))‖ ≤
      (K * ∑ d ∈ S, Kd d + 2 * (K * cuA (R + 2) S) + K * ∑ d ∈ S, ∏ u ∈ d.support, B ^ d u) *
        ((g ^ 2)⁻¹ * ((W : ℝ)⁻¹) ^ a + 1 / g ^ (2 * R + 2)) := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hc1 0)
  have hg0 : 0 < g := by linarith
  set z : ℝ := ((g ^ 2)⁻¹) ^ (R + 3) with hz
  set x : ℝ := (g ^ 2)⁻¹ * ((W : ℝ)⁻¹) ^ a with hx
  set y : ℝ := 1 / g ^ (2 * R + 2) with hy
  have hz1 : 1 / g ^ (2 * (R + 2) + 2) = z := by
    rw [hz, inv_pow, ← pow_mul, one_div, show 2 * (R + 2) + 2 = 2 * (R + 3) by ring]
  have hzy : z ≤ y := by
    rw [← hz1, hy]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hg (by omega))
  have hz0 : 0 ≤ z := by positivity
  have hx0 : 0 ≤ x := by positivity
  have hcore := cu_core (N := R + 2) hKd hW hg hE hX hs1 hc1 hw0 hwa
  have hq : K * (∑ d ∈ S, Kd d) / g ^ (2 * (R + 2) + 2) = K * (∑ d ∈ S, Kd d) * z := by
    rw [← hz1, mul_one_div]
  rw [hq, show R + 2 + 1 = R + 3 from rfl, ← hz] at hcore
  set Bs := ∑ d ∈ S, ∏ u ∈ d.support, B ^ d u with hBs
  have hZb : ‖obsEval g X (bind₁ (corrCoord E R) (corrUpd E R v) -
      updPoly E (R + 2) (corrCoord E R v))‖ ≤ (K * Bs + K * cuA (R + 2) S) * z := by
    refine (cu_norm_eval_le hW hg hX 0 (R + 3) fun d hd =>
      ⟨Nat.zero_le _, cu_mem_I.mp (cu_corrUpd_sub_mem E R v) d hd⟩).trans ?_
    rw [pow_zero, mul_one]
    refine mul_le_mul_of_nonneg_right ((cuL_sub_le _ _).trans
      (add_le_add (cuL_bind_le hs3 hc3 hB) ?_)) hz0
    exact (cuL_truncG_le _ _).trans (cuL_T hE _ hs1 hc1)
  have e : transOp g E (fun Y => obsEval g Y (corrCoord E R v)) X -
      obsEval g X (bind₁ (corrCoord E R) (corrUpd E R v)) =
      (transOp g E (fun Y => obsEval g Y (corrCoord E R v)) X -
        obsEval g X (updPoly E (R + 2) (corrCoord E R v))) -
      obsEval g X (bind₁ (corrCoord E R) (corrUpd E R v) -
        updPoly E (R + 2) (corrCoord E R v)) := by
    rw [map_sub]
    ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have hA0 := cuA_nonneg (R + 2) S
  have h1 : 0 ≤ K * ∑ d ∈ S, Kd d := mul_nonneg hK0 (Finset.sum_nonneg fun d _ => hKd0 d)
  have h2 : 0 ≤ K * cuA (R + 2) S := mul_nonneg hK0 hA0
  have h3 : 0 ≤ K * Bs := mul_nonneg hK0 (Finset.sum_nonneg fun d _ =>
    Finset.prod_nonneg fun u _ => pow_nonneg hB0 _)
  nlinarith [mul_le_mul_of_nonneg_left hzy h1, mul_le_mul_of_nonneg_left hzy h2,
    mul_le_mul_of_nonneg_left hzy h3, mul_nonneg h1 hx0, mul_nonneg h2 hx0, mul_nonneg h3 hx0]


/-- The leading retained map in the corrected coordinates (Section 11.3.3
[lg:sec:general-state]): for `k > 0`, the terms of orders `1` and `g⁻²` of `[P_g M_k]_{≤R+2,0}`
and `[P_g F_k]_{≤R+2,0}` are `(−e^{−2iθ})^k [y_k + h_θ² g⁻² 𝓛 y_k]`. -/
theorem truncG_one_corrUpd (R : ℕ) (Ks : Finset NzInt) :
    ∃ E₁ : ℝ, 0 < E₁ ∧ ∀ E : ℝ, |E| ≤ E₁ → ∀ k ∈ Ks, ∀ hk : 0 < k.1,
      truncG 1 (corrUpd E R (.m k)) = C ((-normalPhase E) ^ k.1) *
          (X (.m k) + C (((normalH E ^ 2 : ℝ) : ℂ)) * X .γ * centerTrace k.1.toNat) ∧
        truncG 1 (corrUpd E R (.f k)) = C ((-normalPhase E) ^ k.1) *
          (X (.f k) + C (((normalH E ^ 2 : ℝ) : ℂ)) * X .γ * centerCorner k.1.toNat) := by
  obtain ⟨E₁, hE₁, h⟩ := parityPart_corrUpd R Ks
  refine ⟨E₁, hE₁, fun E hE k hk hk0 => ?_⟩
  obtain ⟨hm, hf⟩ := h E hE k hk
  have hkn : ((k.1.toNat : ℕ) : ℤ) = k.1 := Int.toNat_of_nonneg hk0.le
  have hk1 : 1 ≤ k.1.toNat := by omega
  have hmv : mVar (k.1.toNat : ℤ) = X (.m k) := by simp [hkn, mVar, k.2]
  have hfv : fVar (k.1.toNat : ℤ) = X (.f k) := by simp [hkn, fVar, k.2]
  have hPm : parityPart (ObsVar.m k).idx (zeroW (wickMap 1 (X (.m k)))) =
      centerTrace k.1.toNat := by
    rw [← hmv, zeroW_wickMap_one_mVar hk1,
      show (ObsVar.m k).idx = ((k.1.toNat : ℕ) : ℤ) from hkn.symm, parityPart_diffTrace hk1]
  have hPf : parityPart (ObsVar.f k).idx (zeroW (wickMap 1 (X (.f k)))) =
      centerCorner k.1.toNat := by
    rw [← hfv, zeroW_wickMap_one_fVar hk1,
      show (ObsVar.f k).idx = ((k.1.toNat : ℕ) : ℤ) from hkn.symm, parityPart_diffMarked hk1]
  exact ⟨cu_lead_final E R (fun h => ObsVar.noConfusion h) (fun h => ObsVar.noConfusion h) hm hPm
      (cu_centerTrace_mem _),
    cu_lead_final E R (fun h => ObsVar.noConfusion h) (fun h => ObsVar.noConfusion h) hf hPf
      (cu_centerCorner_mem _)⟩

/-- (11.57) [lg:eq:widtherrors]: the corrected updates hold with remainders
`K(g⁻²W⁻² + g^{−2R−2})` for `M_k` and `K(g⁻²W⁻¹ + g^{−2R−2})` for `F_k`. -/
theorem transOp_corrObs_sub_le (R : ℕ) (Ks : Finset NzInt) :
    ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ K : ℝ, 0 < K ∧ ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g →
      ∀ E : ℝ, |E| ≤ E₁ → ∀ X : State W, IsState X → ∀ k ∈ Ks,
        ‖transOp g E (fun Y => obsEval g Y (corrObsM E R k)) X -
            obsEval g X (bind₁ (corrCoord E R) (corrUpd E R (.m k)))‖ ≤
          K * (1 / (g ^ 2 * (W : ℝ) ^ 2) + 1 / g ^ (2 * R + 2)) ∧
        ‖transOp g E (fun Y => obsEval g Y (corrObsF E R k)) X -
            obsEval g X (bind₁ (corrCoord E R) (corrUpd E R (.f k)))‖ ≤
          K * (1 / (g ^ 2 * W) + 1 / g ^ (2 * R + 2)) := by
  obtain ⟨E₁, hE₁, hE₁1, S, K, B, hK0, hB0, hdat⟩ := cu_data R Ks
  choose Kd hKdpos hKd using fun d : ObsVar →₀ ℕ =>
    transOp_obsEval_sub_le (E₀ := 1) (by norm_num) (monomial d 1) (R + 2)
  set C₀ := K * ∑ d ∈ S, Kd d + 2 * (K * cuA (R + 2) S) +
    K * ∑ d ∈ S, ∏ u ∈ d.support, B ^ d u with hC₀
  have hC₀0 : 0 ≤ C₀ := by
    have := cuA_nonneg (R + 2) S
    have h1 : 0 ≤ ∑ d ∈ S, Kd d := Finset.sum_nonneg fun d _ => (hKdpos d).le
    have h3 : 0 ≤ ∑ d ∈ S, ∏ u ∈ d.support, B ^ d u :=
      Finset.sum_nonneg fun d _ => Finset.prod_nonneg fun u _ => pow_nonneg hB0 _
    positivity
  refine ⟨E₁, hE₁, C₀ + 1, by linarith, fun W hW g hg E hE X hX k hk => ?_⟩
  obtain ⟨hd, hB⟩ := hdat E hE
  have hE1 : |E| ≤ 1 := hE.trans hE₁1
  have hg0 : 0 < g := by linarith
  have hfin : ∀ {t : ℝ}, 0 ≤ t → ∀ {L : ℝ}, L ≤ C₀ * t → L ≤ (C₀ + 1) * t := fun ht _ hL =>
    hL.trans (mul_le_mul_of_nonneg_right (by linarith) ht)
  obtain ⟨hsM, -, hs3M, hcM⟩ := hd k hk (.m k) (by simp)
  obtain ⟨hsF, -, hs3F, hcF⟩ := hd k hk (.f k) (by simp)
  have hM := (corrObs_form E R k).2.2.1
  have hF := (corrObs_form E R k).2.2.2.2.2.1
  refine ⟨hfin (by positivity) ?_, hfin (by positivity) ?_⟩
  · have h := cu_upd_bound (a := 2) (fun d => hKd d) (fun d => (hKdpos d).le) hB0 hW hg hE1 hX
      hsM hs3M (fun d => (hcM d).1) (fun d => (hcM d).2.2) hB
      (cu_free (by simp [traceVars]) hM) (fun r _ d hd' hdw => by
        have h0 := (wickMap_traceVars r _ (cu_supported_rot hM E)).2 1 odd_one
        by_contra hlt
        have hd1 : d .w = 1 := by omega
        have h00 := congrArg (fun q : ObsPoly => q.coeff d) h0
        have hz : (0 : ObsPoly).coeff d = 0 := by simp
        simp only [coeff_weightedHomogeneousComponent, cu_weight_w, hd1, ↓reduceIte, hz] at h00
        exact (mem_support_iff.mp hd') h00)
    rwa [show (g ^ 2)⁻¹ * ((W : ℝ)⁻¹) ^ 2 = 1 / (g ^ 2 * (W : ℝ) ^ 2) by
      rw [one_div, mul_inv, inv_pow]] at h
  · have h := cu_upd_bound (a := 1) (fun d => hKd d) (fun d => (hKdpos d).le) hB0 hW hg hE1 hX
      hsF hs3F (fun d => (hcF d).1) (fun d => (hcF d).2.2) hB
      (cu_free (by simp) hF) (fun r _ d _ hdw => Nat.one_le_iff_ne_zero.mpr hdw)
    rwa [show (g ^ 2)⁻¹ * ((W : ℝ)⁻¹) ^ 1 = 1 / (g ^ 2 * W) by
      rw [pow_one, one_div, mul_inv]] at h

/-- `M_k = m_k + O(g⁻²)`, `F_k = f_k + O(g⁻²)`, and the inverse substitution
`m_k = m_k^{[R+2]}(M) + O(g^{−2R−6})`, `f_k = f_k^{[R+2]}(M, F) + O(g^{−2R−6})`, uniformly in
`W ≥ 1`, `g ≥ 1`, the window and the state (Section 11.3.1 [lg:sec:state-estimates]). -/
theorem norm_obsEval_corrObs_sub_le (R : ℕ) (Ks : Finset NzInt) :
    ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ K : ℝ, 0 < K ∧ ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g →
      ∀ E : ℝ, |E| ≤ E₁ → ∀ X : State W, IsState X → ∀ k ∈ Ks,
        ‖obsEval g X (corrObsM E R k) - obsM k.1 X‖ ≤ K / g ^ 2 ∧
          ‖obsEval g X (corrObsF E R k) - obsF k.1 X‖ ≤ K / g ^ 2 ∧
          ‖obsEval g X (bind₁ (corrCoord E R) (invCoord E R (.m k))) - obsM k.1 X‖ ≤
            K / g ^ (2 * R + 6) ∧
          ‖obsEval g X (bind₁ (corrCoord E R) (invCoord E R (.f k))) - obsF k.1 X‖ ≤
            K / g ^ (2 * R + 6) := by
  obtain ⟨E₁, hE₁, -, S, K, B, hK0, hB0, hdat⟩ := cu_data R Ks
  set Bs := ∑ d ∈ S, ∏ u ∈ d.support, B ^ d u with hBs
  have hBs0 : 0 ≤ Bs := Finset.sum_nonneg fun d _ => Finset.prod_nonneg fun u _ => pow_nonneg hB0 _
  refine ⟨E₁, hE₁, S.card * K + 1 + (K * Bs + 1), by positivity,
    fun W hW g hg E hE X hX k hk => ?_⟩
  obtain ⟨hd, hB⟩ := hdat E hE
  have hg0 : 0 < g := by linarith
  have hlow : ∀ v ∈ [ObsVar.m k, ObsVar.f k],
      ‖obsEval g X (corrCoord E R v) - obsEval g X (MvPolynomial.X v)‖ ≤
        (S.card * K + 1 + (K * Bs + 1)) / g ^ 2 := by
    intro v hv
    obtain ⟨hs1, -, -, hc⟩ := hd k hk v hv
    rw [← map_sub]
    refine (cu_norm_eval_le hW hg hX 0 1 fun d hd' =>
      ⟨Nat.zero_le _, cu_mem_I.mp (cu_corr_sub_mem E R v) d hd'⟩).trans ?_
    rw [pow_zero, mul_one, pow_one, ← div_eq_mul_inv]
    refine div_le_div_of_nonneg_right (((cuL_sub_le _ _).trans
      (add_le_add (cuL_le_card hs1 fun d => (hc d).1) (cuL_X _))).trans ?_) (by positivity)
    nlinarith [mul_nonneg hK0 hBs0]
  have hinv : ∀ v ∈ [ObsVar.m k, ObsVar.f k],
      ‖obsEval g X (bind₁ (corrCoord E R) (invCoord E R v)) - obsEval g X (MvPolynomial.X v)‖ ≤
        (S.card * K + 1 + (K * Bs + 1)) / g ^ (2 * R + 6) := by
    intro v hv
    obtain ⟨-, hs2, -, hc⟩ := hd k hk v hv
    rw [← map_sub]
    refine (cu_norm_eval_le hW hg hX 0 (R + 3) fun d hd' =>
      ⟨Nat.zero_le _, cu_mem_I.mp (cu_corr_inv E R v) d hd'⟩).trans ?_
    rw [pow_zero, mul_one, show ((g ^ 2)⁻¹) ^ (R + 3) = 1 / g ^ (2 * R + 6) by
      rw [inv_pow, ← pow_mul, one_div, show 2 * (R + 3) = 2 * R + 6 by ring], mul_one_div]
    refine div_le_div_of_nonneg_right (((cuL_sub_le _ _).trans
      (add_le_add (cuL_bind_le hs2 (fun d => (hc d).2.1) hB) (cuL_X _))).trans ?_)
      (by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) S.card, mul_nonneg (Nat.cast_nonneg (α := ℝ) S.card) hK0]
  have hm : obsEval g X (MvPolynomial.X (.m k)) = obsM k.1 X := by simp [obsEval]
  have hf : obsEval g X (MvPolynomial.X (.f k)) = obsF k.1 X := by simp [obsEval]
  have h1 := hlow (.m k) (by simp)
  have h2 := hlow (.f k) (by simp)
  have h3 := hinv (.m k) (by simp)
  have h4 := hinv (.f k) (by simp)
  rw [hm] at h1 h3
  rw [hf] at h2 h4
  exact ⟨h1, h2, h3, h4⟩

end LSBA
