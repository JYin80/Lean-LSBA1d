import LSBA.Upper.CenterCorrection

/-!
# The parity property of the corrected updates

(11.45) [lg:eq:required-parity-updates]: on an energy window fixed after the order `R` and a
finite index set, the corrections (11.49) [lg:eq:observable-correction] remove every monomial of
degree `≢ k (mod 2)` from `[P_g M_k]_{≤R+2,0}` and `[P_g F_k]_{≤R+2,0}` in the corrected
coordinates (the gap (11.48) [lg:eq:opposite-parity-gap]); and the corrections, the inverse
polynomials and the corrected updates are fixed polynomials with coefficients bounded on the window
(Lemma 11.8 [lg:lem:dynamic]).
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Coefficients of the truncation, the `γ`-components and the divided parts -/

private lemma cp_weight_gamWt (d : ObsVar →₀ ℕ) : Finsupp.weight ObsVar.gamWt d = d .γ := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_single ObsVar.γ]
  · simp [ObsVar.gamWt]
  · intro b _ hb
    cases b <;> simp_all [ObsVar.gamWt]
  · intro h
    simp [Finsupp.notMem_support_iff.mp h]

private lemma cp_coeff_comp (s : ℕ) (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (weightedHomogeneousComponent ObsVar.gamWt s p).coeff d =
      if d .γ = s then p.coeff d else 0 := by
  rw [coeff_weightedHomogeneousComponent, cp_weight_gamWt]

private lemma cp_coeff_truncG (N : ℕ) (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (truncG N p).coeff d = if d .γ ≤ N then p.coeff d else 0 := by
  unfold truncG
  rw [LinearMap.sum_apply, MvPolynomial.coeff_sum]
  simp only [cp_coeff_comp]
  rw [Finset.sum_ite_eq]
  simp

private lemma cp_coeff_oppDiv (E : ℝ) (k : ℤ) (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (oppDiv E k p).coeff d = if Even (obsDeg d - k) then 0 else
      p.coeff d / ((-normalPhase E) ^ k - (-normalPhase E) ^ obsDeg d) := by
  unfold oppDiv
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
      · simp
      · have hbd : b ≠ d := fun h => hd (h ▸ hb)
        simp [coeff_monomial, hbd]

private lemma cp_truncG_X {N : ℕ} (hN : 1 ≤ N) (v : ObsVar) : truncG N (X v) = X v := by
  ext d
  rw [cp_coeff_truncG]
  split_ifs with hd
  · rfl
  · rw [coeff_X]
    split_ifs with h2
    · exfalso
      apply hd
      rw [← h2, Finsupp.single_apply]
      split_ifs <;> omega
    · rfl

/-! ### Divisibility by powers of `γ` -/

private lemma cp_dvd_iff (t : ℕ) (p : ObsPoly) :
    X .γ ^ t ∣ p ↔ ∀ d : ObsVar →₀ ℕ, d .γ < t → p.coeff d = 0 := by
  constructor
  · rintro ⟨q, rfl⟩ d hd
    rw [X_pow_eq_monomial, coeff_monomial_mul']
    split_ifs with h
    · rw [Finsupp.single_le_iff] at h
      omega
    · rfl
  · intro h
    rw [p.as_sum]
    refine Finset.dvd_sum fun d hd => ?_
    have ht : t ≤ d .γ := by
      by_contra h'
      exact (mem_support_iff.mp hd) (h d (by omega))
    refine ⟨monomial (d - Finsupp.single ObsVar.γ t) (p.coeff d), ?_⟩
    rw [X_pow_eq_monomial, monomial_mul_monomial, one_mul, add_tsub_cancel_of_le]
    rw [Finsupp.single_le_iff]
    exact ht

private lemma cp_dvd_of_coeff {t : ℕ} {p q : ObsPoly}
    (h : ∀ d, p.coeff d = 0 → q.coeff d = 0) (hp : X .γ ^ t ∣ p) : X .γ ^ t ∣ q := by
  rw [cp_dvd_iff] at hp ⊢
  exact fun d hd => h d (hp d hd)

private lemma cp_coeff_of_dvd {t : ℕ} {p : ObsPoly} (hp : X .γ ^ t ∣ p) {d : ObsVar →₀ ℕ}
    (hd : d .γ < t) : p.coeff d = 0 :=
  (cp_dvd_iff t p).mp hp d hd

private lemma cp_dvd_mono {s t : ℕ} (h : s ≤ t) {p : ObsPoly} (hp : X .γ ^ t ∣ p) :
    X .γ ^ s ∣ p :=
  (pow_dvd_pow _ h).trans hp

private lemma cp_truncG_dvd (N : ℕ) {t : ℕ} {p : ObsPoly} (hp : X .γ ^ t ∣ p) :
    X .γ ^ t ∣ truncG N p :=
  cp_dvd_of_coeff (fun d hd => by rw [cp_coeff_truncG, hd]; simp) hp

private lemma cp_truncG_sub (N : ℕ) (p : ObsPoly) : X .γ ^ (N + 1) ∣ truncG N p - p := by
  rw [cp_dvd_iff]
  intro d hd
  rw [coeff_sub, cp_coeff_truncG]
  split_ifs with h
  · rw [sub_self]
  · omega

private lemma cp_alg_dvd (φ : ObsPoly →ₐ[ℂ] ObsPoly) (hφ : φ (X .γ) = X .γ) {t : ℕ}
    {p : ObsPoly} (hp : X .γ ^ t ∣ p) : X .γ ^ t ∣ φ p := by
  obtain ⟨q, rfl⟩ := hp
  rw [map_mul, map_pow, hφ]
  exact dvd_mul_right _ _

private lemma cp_bind_gamma_pow {τ : ObsVar → ObsPoly} (hτ : τ .γ = X .γ) (t : ℕ) (q : ObsPoly) :
    bind₁ τ (X .γ ^ t * q) = X .γ ^ t * bind₁ τ q := by
  rw [map_mul, map_pow, bind₁_X_right, hτ]

private lemma cp_bind_dvd {τ : ObsVar → ObsPoly} (hτ : τ .γ = X .γ) {t : ℕ} {p : ObsPoly}
    (hp : X .γ ^ t ∣ p) : X .γ ^ t ∣ bind₁ τ p :=
  cp_alg_dvd (bind₁ τ) (by rw [bind₁_X_right, hτ]) hp

private lemma cp_bind_congr {t : ℕ} {τ τ' : ObsVar → ObsPoly} (h : ∀ v, X .γ ^ t ∣ τ v - τ' v)
    (p : ObsPoly) : X .γ ^ t ∣ bind₁ τ p - bind₁ τ' p := by
  let I : Ideal ObsPoly := Ideal.span {(X ObsVar.γ : ObsPoly) ^ t}
  have key : (Ideal.Quotient.mkₐ ℂ I).comp (bind₁ τ) =
      (Ideal.Quotient.mkₐ ℂ I).comp (bind₁ τ') := by
    refine MvPolynomial.algHom_ext fun v => ?_
    simp only [AlgHom.comp_apply, bind₁_X_right, Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr (h v))
  have h2 := congrArg (fun φ : ObsPoly →ₐ[ℂ] ObsPoly ⧸ I => φ p) key
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h2
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h2)

private lemma cp_bind_shift {τ τ' : ObsVar → ObsPoly} (hτ : τ .γ = X .γ) (hτ' : τ' .γ = X .γ)
    {i j : ℕ} (h : ∀ v, X .γ ^ j ∣ τ v - τ' v) {p : ObsPoly} (hp : X .γ ^ i ∣ p) :
    X .γ ^ (i + j) ∣ bind₁ τ p - bind₁ τ' p := by
  obtain ⟨q, rfl⟩ := hp
  rw [cp_bind_gamma_pow hτ, cp_bind_gamma_pow hτ', ← mul_sub, pow_add]
  exact mul_dvd_mul_left _ (cp_bind_congr h q)

private lemma cp_bind_X (p : ObsPoly) : bind₁ (X : ObsVar → ObsPoly) p = p := by
  rw [bind₁_X_left, AlgHom.id_apply]

/-- `bind₁ τ p ≡ p` modulo `γ^{i+1}` when `τ ≡ X` modulo `γ` and `γ^i ∣ p`. -/
private lemma cp_bind_near_id {τ : ObsVar → ObsPoly} (hτ : τ .γ = X .γ)
    (h : ∀ v, X .γ ^ 1 ∣ τ v - X v) {i : ℕ} {p : ObsPoly} (hp : X .γ ^ i ∣ p) :
    X .γ ^ (i + 1) ∣ bind₁ τ p - p := by
  have := cp_bind_shift hτ rfl h hp
  rwa [cp_bind_X] at this

/-! ### The rotation, the `W⁰` part and the expansion maps -/

/-- The rotation factor `−e^{−2iθ}` of (11.45) [lg:eq:required-parity-updates]. -/
private def cpLam (E : ℝ) : ℂ := -normalPhase E

private lemma cp_lam_zpow (E : ℝ) (n : ℤ) :
    cpLam E ^ n = Complex.exp (n * (2 * (freeAngle E * Complex.I))) := by
  rw [Complex.exp_int_mul, cpLam, normalPhase, neg_neg]

private lemma cp_norm_lam_zpow (E : ℝ) (n : ℤ) : ‖cpLam E ^ n‖ = 1 := by
  rw [cp_lam_zpow, show (n : ℂ) * (2 * (freeAngle E * Complex.I)) =
    ((n * 2 * freeAngle E : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma cp_lam_obsDeg (E : ℝ) (u : ObsVar →₀ ℕ) :
    ∏ v ∈ u.support, (cpLam E ^ v.idx) ^ u v = cpLam E ^ obsDeg u := by
  simp only [cp_lam_zpow, ← Complex.exp_nat_mul, ← Complex.exp_sum]
  congr 1
  rw [obsDeg, Finsupp.weight_apply, Finsupp.sum]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [nsmul_eq_mul]
  push_cast
  ring

private lemma cp_coeff_add (p q : ObsPoly) (d : ObsVar →₀ ℕ) :
    (p + q).coeff d = p.coeff d + q.coeff d := by
  simp

private lemma cp_coeff_of_monomial (φ : ObsPoly →ₐ[ℂ] ObsPoly) (μ : (ObsVar →₀ ℕ) → ℂ)
    (h : ∀ u a, φ (monomial u a) = monomial u (μ u * a)) (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (φ p).coeff d = μ d * p.coeff d := by
  refine MvPolynomial.induction_on' p (fun u a => ?_) (fun p q hp hq => ?_)
  · rw [h, coeff_monomial, coeff_monomial]
    split_ifs with hud
    · rw [hud]
    · rw [mul_zero]
  · rw [map_add, cp_coeff_add, cp_coeff_add, hp, hq, mul_add]

private lemma cp_rot_monomial (E : ℝ) (u : ObsVar →₀ ℕ) (a : ℂ) :
    rotPoly E (monomial u a) = monomial u (cpLam E ^ obsDeg u * a) := by
  rw [rotPoly, aeval_monomial, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
  rw [show ∏ x ∈ u.support, ((-normalPhase E) ^ x.idx) ^ u x = cpLam E ^ obsDeg u from
    cp_lam_obsDeg E u]
  rw [monomial_eq, Finsupp.prod, algebraMap_eq, map_mul]
  ring

private lemma cp_coeff_rot (E : ℝ) (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (rotPoly E p).coeff d = cpLam E ^ obsDeg d * p.coeff d :=
  cp_coeff_of_monomial _ _ (cp_rot_monomial E) p d

private lemma cp_zeroW_monomial (u : ObsVar →₀ ℕ) (a : ℂ) :
    zeroW (monomial u a) = monomial u ((if u .w = 0 then 1 else 0) * a) := by
  rw [zeroW, aeval_monomial, Finsupp.prod]
  split_ifs with h
  · rw [one_mul, monomial_eq, Finsupp.prod, algebraMap_eq]
    congr 1
    refine Finset.prod_congr rfl fun v hv => ?_
    have : v ≠ .w := by
      rintro rfl
      exact (Finsupp.mem_support_iff.mp hv) h
    simp [this]
  · rw [Finset.prod_eq_zero (i := .w) (Finsupp.mem_support_iff.mpr h)]
    · simp
    · simp [zero_pow h]

private lemma cp_coeff_zeroW (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (zeroW p).coeff d = (if d .w = 0 then 1 else 0) * p.coeff d :=
  cp_coeff_of_monomial _ _ cp_zeroW_monomial p d

private lemma cp_rot_γ (E : ℝ) : rotPoly E (X .γ) = X .γ := by
  simp [rotPoly, ObsVar.idx]

private lemma cp_zeroW_γ : zeroW (X .γ) = X .γ := by
  simp [zeroW]

private lemma cp_wick_zero (r : ℕ) : wickMap r 0 = 0 := by
  have h := (wickMap_linear r 1 0 0).1
  simp only [smul_zero, add_zero, one_smul] at h
  linear_combination -h

/-- `q_r` as a linear map. -/
private def cpWick (r : ℕ) : ObsPoly →ₗ[ℂ] ObsPoly where
  toFun := wickMap r
  map_add' p q := by simpa using (wickMap_linear r 1 p q).1
  map_smul' a p := by simpa [cp_wick_zero] using (wickMap_linear r a p 0).1

private lemma cp_wick_gamma_pow (r t : ℕ) (q : ObsPoly) :
    wickMap r (X .γ ^ t * q) = X .γ ^ t * wickMap r q := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', mul_assoc, (wickMap_linear r 1 ((X ObsVar.γ : ObsPoly) ^ t * q) 0).2, ih,
      ← mul_assoc]

/-- The untruncated sum of `[P_g p]_{≤N,0}`. -/
private def cpPre (E : ℝ) (N : ℕ) (p : ObsPoly) : ObsPoly :=
  ∑ r ∈ Finset.range (N + 1),
    C (((normalH E ^ (2 * r) : ℝ) : ℂ)) * X .γ ^ r * zeroW (wickMap r (rotPoly E p))

private lemma cp_upd_eq (E : ℝ) (N : ℕ) (p : ObsPoly) : updPoly E N p = truncG N (cpPre E N p) :=
  rfl

private lemma cp_pre_sub (E : ℝ) (N : ℕ) (p q : ObsPoly) :
    cpPre E N (p - q) = cpPre E N p - cpPre E N q := by
  unfold cpPre
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_sub, show wickMap r (rotPoly E p - rotPoly E q) =
    cpWick r (rotPoly E p - rotPoly E q) from rfl, map_sub]
  change _ * zeroW (wickMap r _ - wickMap r _) = _
  rw [map_sub, mul_sub]

private lemma cp_upd_sub (E : ℝ) (N : ℕ) (p q : ObsPoly) :
    updPoly E N (p - q) = updPoly E N p - updPoly E N q := by
  rw [cp_upd_eq, cp_upd_eq, cp_upd_eq, cp_pre_sub, map_sub]

private lemma cp_upd_zero (E : ℝ) (N : ℕ) : updPoly E N 0 = 0 := by
  have h := cp_upd_sub E N 0 0
  rw [sub_self] at h
  linear_combination h

private lemma cp_upd_add (E : ℝ) (N : ℕ) (p q : ObsPoly) :
    updPoly E N (p + q) = updPoly E N p + updPoly E N q := by
  rw [show p + q = p - (0 - q) by ring, cp_upd_sub, cp_upd_sub, cp_upd_zero]
  ring

private lemma cp_pre_gamma_pow (E : ℝ) (N t : ℕ) (q : ObsPoly) :
    cpPre E N (X .γ ^ t * q) = X .γ ^ t * cpPre E N q := by
  unfold cpPre
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_mul, map_pow, cp_rot_γ, cp_wick_gamma_pow, map_mul, map_pow, cp_zeroW_γ]
  ring

private lemma cp_pre_lead (E : ℝ) (N : ℕ) (q : ObsPoly) :
    X .γ ^ 1 ∣ cpPre E N q - zeroW (rotPoly E q) := by
  unfold cpPre
  rw [Finset.sum_range_succ', (wickMap_zero_incWick_zero _).1]
  simp only [mul_zero, pow_zero, Complex.ofReal_one, map_one, one_mul, add_sub_cancel_right]
  refine Finset.dvd_sum fun r _ => ?_
  have h : (X ObsVar.γ : ObsPoly) ^ 1 ∣ X ObsVar.γ ^ (r + 1) := pow_dvd_pow _ (by omega)
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _

/-- `[P_g c]_{≤N,0} ≡ π₀ ρ_θ c` modulo `γ^{t+1}` when `γ^t ∣ c` (`t ≤ N`). -/
private lemma cp_upd_order (E : ℝ) {N t : ℕ} (ht : t ≤ N) {c : ObsPoly} (hc : X .γ ^ t ∣ c) :
    X .γ ^ (t + 1) ∣ updPoly E N c - zeroW (rotPoly E c) := by
  obtain ⟨q, rfl⟩ := hc
  have h1 : X .γ ^ (t + 1) ∣ cpPre E N (X .γ ^ t * q) - zeroW (rotPoly E (X .γ ^ t * q)) := by
    rw [cp_pre_gamma_pow, map_mul, map_pow, cp_rot_γ, map_mul, map_pow, cp_zeroW_γ, ← mul_sub,
      pow_add]
    exact mul_dvd_mul_left _ (cp_pre_lead E N q)
  have h2 := cp_dvd_mono (show t + 1 ≤ N + 1 by omega) (cp_truncG_sub N (cpPre E N (X .γ ^ t * q)))
  rw [cp_upd_eq]
  have e : truncG N (cpPre E N (X .γ ^ t * q)) - zeroW (rotPoly E (X .γ ^ t * q)) =
      (truncG N (cpPre E N (X .γ ^ t * q)) - cpPre E N (X .γ ^ t * q)) +
        (cpPre E N (X .γ ^ t * q) - zeroW (rotPoly E (X .γ ^ t * q))) := by ring
  rw [e]
  exact dvd_add h2 h1

private lemma cp_upd_dvd (E : ℝ) (N : ℕ) {t : ℕ} {c : ObsPoly} (hc : X .γ ^ t ∣ c) :
    X .γ ^ t ∣ updPoly E N c := by
  obtain ⟨q, rfl⟩ := hc
  rw [cp_upd_eq, cp_pre_gamma_pow]
  exact cp_truncG_dvd N (dvd_mul_right _ _)

/-! ### Polynomials without `w` -/

private lemma cp_noW_iff (p : ObsPoly) :
    p ∈ supported ℂ {v | v ≠ .w} ↔ ∀ d : ObsVar →₀ ℕ, d .w ≠ 0 → p.coeff d = 0 := by
  rw [mem_supported]
  constructor
  · intro hp d hd
    by_contra h
    exact hp (Finset.mem_coe.mpr ((mem_vars_iff_mem_support _).mpr
      ⟨d, mem_support_iff.mpr h, Finsupp.mem_support_iff.mpr hd⟩)) rfl
  · intro h v hv
    rw [Finset.mem_coe, mem_vars_iff_mem_support] at hv
    obtain ⟨d, hd, hvd⟩ := hv
    change v ≠ .w
    rintro rfl
    exact mem_support_iff.mp hd (h d (Finsupp.mem_support_iff.mp hvd))

private lemma cp_noW_of_coeff {p q : ObsPoly} (h : ∀ d, p.coeff d = 0 → q.coeff d = 0)
    (hp : p ∈ supported ℂ {v | v ≠ .w}) : q ∈ supported ℂ {v | v ≠ .w} := by
  rw [cp_noW_iff] at hp ⊢
  exact fun d hd => h d (hp d hd)

private lemma cp_bind₁_supported (τ : ObsVar → ObsPoly) {S T : Set ObsVar} {p : ObsPoly}
    (hp : p ∈ supported ℂ S) (hτ : ∀ v ∈ S, τ v ∈ supported ℂ T) :
    bind₁ τ p ∈ supported ℂ T := by
  rw [MvPolynomial.mem_supported] at hp ⊢
  intro i hi
  have h := MvPolynomial.vars_bind₁ τ p (Finset.mem_coe.mp hi)
  rw [Finset.mem_biUnion] at h
  obtain ⟨v, hv, hiv⟩ := h
  have h2 := hτ v (hp (Finset.mem_coe.mpr hv))
  rw [MvPolynomial.mem_supported] at h2
  exact h2 (Finset.mem_coe.mpr hiv)

private lemma cp_zeroW_noW (p : ObsPoly) : zeroW p ∈ supported ℂ {v | v ≠ .w} := by
  rw [cp_noW_iff]
  intro d hd
  simp [cp_coeff_zeroW, hd]

private lemma cp_truncG_noW (N : ℕ) {p : ObsPoly} (hp : p ∈ supported ℂ {v | v ≠ .w}) :
    truncG N p ∈ supported ℂ {v | v ≠ .w} :=
  cp_noW_of_coeff (fun d hd => by rw [cp_coeff_truncG, hd]; simp) hp

private lemma cp_upd_noW (E : ℝ) (N : ℕ) (p : ObsPoly) :
    updPoly E N p ∈ supported ℂ {v | v ≠ .w} := by
  rw [cp_upd_eq]
  refine cp_truncG_noW N (Subalgebra.sum_mem _ fun r _ => ?_)
  refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Subalgebra.pow_mem _ (X_mem_supported.mpr (fun h => ObsVar.noConfusion h)) _))
    (cp_zeroW_noW _)

/-! ### Coordinate systems and their reversions -/

/-- A coordinate system `x ↦ σ(x)` with `σ ≡ id` modulo `γ`, fixing `γ` and `w`, and without `w`
in the coordinates of the other variables. -/
private def cpCoord (σ : ObsVar → ObsPoly) : Prop :=
  σ .γ = X .γ ∧ σ .w = X .w ∧ (∀ u, X .γ ^ 1 ∣ σ u - X u) ∧
    ∀ u, u ≠ .w → σ u ∈ supported ℂ {v | v ≠ .w}

private lemma cp_rev_succ (N : ℕ) (σ : ObsVar → ObsPoly) (r : ℕ) (v : ObsVar) :
    revCoord N σ (r + 1) v = truncG N (X v - bind₁ (revCoord N σ r) (σ v - X v)) := by
  rw [revCoord]

private lemma cp_rev_zero (N : ℕ) (σ : ObsVar → ObsPoly) : revCoord N σ 0 = X := by
  rw [revCoord]

private lemma cp_rev_γ {N : ℕ} (hN : 1 ≤ N) {σ : ObsVar → ObsPoly} (hσ : σ .γ = X .γ) :
    ∀ r, revCoord N σ r .γ = X .γ
  | 0 => by rw [cp_rev_zero]
  | r + 1 => by rw [cp_rev_succ, hσ, sub_self, map_zero, sub_zero, cp_truncG_X hN]

private lemma cp_rev_noW {N : ℕ} {σ : ObsVar → ObsPoly}
    (hσ : ∀ u, u ≠ .w → σ u ∈ supported ℂ {v | v ≠ .w}) :
    ∀ r u, u ≠ .w → revCoord N σ r u ∈ supported ℂ {v | v ≠ .w}
  | 0, u, hu => by
    rw [cp_rev_zero]
    exact X_mem_supported.mpr hu
  | r + 1, u, hu => by
    rw [cp_rev_succ]
    refine cp_truncG_noW N (Subalgebra.sub_mem _ (X_mem_supported.mpr hu) ?_)
    exact cp_bind₁_supported _ (Subalgebra.sub_mem _ (hσ u hu) (X_mem_supported.mpr hu))
      (fun v hv => cp_rev_noW hσ r v hv)

/-- Successive reversions agree modulo `γ^{r+1}`. -/
private lemma cp_rev_step {N : ℕ} {σ : ObsVar → ObsPoly} (hN : 1 ≤ N) (hσγ : σ .γ = X .γ)
    (hσ : ∀ u, X .γ ^ 1 ∣ σ u - X u) :
    ∀ r u, X .γ ^ (r + 1) ∣ revCoord N σ (r + 1) u - revCoord N σ r u
  | 0, u => by
    rw [cp_rev_succ, cp_rev_zero, cp_bind_X]
    have e : truncG N (X u - (σ u - X u)) - X u =
        (truncG N (X u - (σ u - X u)) - (X u - (σ u - X u))) - (σ u - X u) := by ring
    rw [e]
    exact dvd_sub (cp_dvd_mono (by omega) (cp_truncG_sub N _)) (hσ u)
  | r + 1, u => by
    rw [cp_rev_succ, cp_rev_succ, ← map_sub]
    refine cp_truncG_dvd N ?_
    have h := cp_bind_shift (cp_rev_γ hN hσγ r) (cp_rev_γ hN hσγ (r + 1))
      (fun v => by rw [← neg_sub]; exact (dvd_neg).mpr (cp_rev_step hN hσγ hσ r v)) (hσ u)
    rw [show 1 + (r + 1) = r + 1 + 1 by omega] at h
    have e : X u - bind₁ (revCoord N σ (r + 1)) (σ u - X u) -
        (X u - bind₁ (revCoord N σ r) (σ u - X u)) =
        bind₁ (revCoord N σ r) (σ u - X u) - bind₁ (revCoord N σ (r + 1)) (σ u - X u) := by ring
    rw [e]
    exact h

/-- The reversion `revCoord N σ N` inverts `σ` modulo `γ^{N+1}`. -/
private lemma cp_rev_inv {N : ℕ} {σ : ObsVar → ObsPoly} (hN : 1 ≤ N) (hσγ : σ .γ = X .γ)
    (hσ : ∀ u, X .γ ^ 1 ∣ σ u - X u) (u : ObsVar) :
    X .γ ^ (N + 1) ∣ bind₁ (revCoord N σ N) (σ u) - X u := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have h := cp_bind_shift (cp_rev_γ hN hσγ (M + 1)) (cp_rev_γ hN hσγ M)
    (cp_rev_step hN hσγ hσ M) (hσ u)
  rw [show 1 + (M + 1) = M + 1 + 1 by omega] at h
  have e : bind₁ (revCoord (M + 1) σ (M + 1)) (σ u) - X u =
      (truncG (M + 1) (X u - bind₁ (revCoord (M + 1) σ M) (σ u - X u)) -
        (X u - bind₁ (revCoord (M + 1) σ M) (σ u - X u))) +
      (bind₁ (revCoord (M + 1) σ (M + 1)) (σ u - X u) -
        bind₁ (revCoord (M + 1) σ M) (σ u - X u)) := by
    rw [← cp_rev_succ]
    conv_lhs => rw [show σ u = X u + (σ u - X u) by ring, map_add, bind₁_X_right]
    ring
  rw [e]
  exact dvd_add (cp_truncG_sub _ _) h

/-- Two inverses of `σ` modulo `γ^t` agree modulo `γ^t`. -/
private lemma cp_inv_unique {σ τ τ' : ObsVar → ObsPoly} (hσ : ∀ u, X .γ ^ 1 ∣ σ u - X u)
    (hτ : τ .γ = X .γ) (hτ' : τ' .γ = X .γ) {t : ℕ}
    (h : ∀ u, X .γ ^ t ∣ bind₁ τ (σ u) - X u) (h' : ∀ u, X .γ ^ t ∣ bind₁ τ' (σ u) - X u) :
    ∀ u, X .γ ^ t ∣ τ u - τ' u := by
  have key : ∀ j, j ≤ t → ∀ u, X .γ ^ j ∣ τ u - τ' u := by
    intro j
    induction j with
    | zero => intro _ u; simp
    | succ j ih =>
      intro hj u
      have hs := cp_bind_shift hτ hτ' (ih (by omega)) (hσ u)
      rw [show 1 + j = j + 1 by omega] at hs
      have e : τ u - τ' u = (bind₁ τ (σ u) - X u) - (bind₁ τ' (σ u) - X u) -
          (bind₁ τ (σ u - X u) - bind₁ τ' (σ u - X u)) := by
        rw [map_sub, map_sub, bind₁_X_right, bind₁_X_right]
        ring
      rw [e]
      exact dvd_sub (dvd_sub (cp_dvd_mono hj (h u)) (cp_dvd_mono hj (h' u))) hs
  exact key t le_rfl

private lemma cp_rev_X {N : ℕ} {σ : ObsVar → ObsPoly} (hN : 1 ≤ N) (hσγ : σ .γ = X .γ)
    (hσ : ∀ u, X .γ ^ 1 ∣ σ u - X u) (u : ObsVar) : X .γ ^ 1 ∣ revCoord N σ N u - X u :=
  cp_inv_unique hσ (cp_rev_γ hN hσγ N) rfl
    (fun v => cp_dvd_mono (by omega) (cp_rev_inv hN hσγ hσ v))
    (fun v => by rw [cp_bind_X]; exact hσ v) u

/-! ### One correction step -/

/-- The update `[P_g σ(x_v)]_{≤N,0}` written in the coordinates `σ`. -/
private def cpU (E : ℝ) (N : ℕ) (σ : ObsVar → ObsPoly) (v : ObsVar) : ObsPoly :=
  truncG N (bind₁ (revCoord N σ N) (updPoly E N (σ v)))

/-- The correction of step `s` (zero for `w` and `γ`). -/
private def cpC (E : ℝ) (N s : ℕ) (σ : ObsVar → ObsPoly) : ObsVar → ObsPoly
  | .w => 0
  | .γ => 0
  | v => oppDiv E v.idx (weightedHomogeneousComponent ObsVar.gamWt s (cpU E N σ v))

private lemma cp_corrStep_eq (E : ℝ) (N s : ℕ) (σ : ObsVar → ObsPoly) {v : ObsVar}
    (hw : v ≠ .w) (hγ : v ≠ .γ) :
    corrStep E N s σ v = truncG N (σ v + bind₁ σ (cpC E N s σ v)) := by
  cases v with
  | m k => rfl
  | f k => rfl
  | w => exact absurd rfl hw
  | γ => exact absurd rfl hγ

private lemma cp_cpC_eq (E : ℝ) (N s : ℕ) (σ : ObsVar → ObsPoly) {v : ObsVar}
    (hw : v ≠ .w) (hγ : v ≠ .γ) :
    cpC E N s σ v = oppDiv E v.idx (weightedHomogeneousComponent ObsVar.gamWt s (cpU E N σ v)) := by
  cases v with
  | m k => rfl
  | f k => rfl
  | w => exact absurd rfl hw
  | γ => exact absurd rfl hγ

private lemma cp_cpC_dvd (E : ℝ) (N s : ℕ) (σ : ObsVar → ObsPoly) (v : ObsVar) :
    X .γ ^ s ∣ cpC E N s σ v := by
  cases v with
  | w => exact dvd_zero _
  | γ => exact dvd_zero _
  | m k =>
    rw [cp_dvd_iff]
    intro d hd
    change (oppDiv E _ _).coeff d = 0
    have hne : d .γ ≠ s := by omega
    rw [cp_coeff_oppDiv, cp_coeff_comp]
    simp [hne]
  | f k =>
    rw [cp_dvd_iff]
    intro d hd
    change (oppDiv E _ _).coeff d = 0
    have hne : d .γ ≠ s := by omega
    rw [cp_coeff_oppDiv, cp_coeff_comp]
    simp [hne]

private lemma cp_cpU_noW (E : ℝ) {N : ℕ} {σ : ObsVar → ObsPoly}
    (hσ : ∀ u, u ≠ .w → σ u ∈ supported ℂ {v | v ≠ .w}) (v : ObsVar) :
    cpU E N σ v ∈ supported ℂ {v | v ≠ .w} :=
  cp_truncG_noW N (cp_bind₁_supported _ (cp_upd_noW E N _) (fun u hu => cp_rev_noW hσ N u hu))

private lemma cp_cpC_noW (E : ℝ) (N s : ℕ) {σ : ObsVar → ObsPoly}
    (hσ : ∀ u, u ≠ .w → σ u ∈ supported ℂ {v | v ≠ .w}) (v : ObsVar) :
    cpC E N s σ v ∈ supported ℂ {v | v ≠ .w} := by
  cases v with
  | w => exact zero_mem _
  | γ => exact zero_mem _
  | m k =>
    refine cp_noW_of_coeff (fun d hd => ?_) (cp_cpU_noW E (N := N) hσ (.m k))
    change (oppDiv E _ _).coeff d = 0
    rw [cp_coeff_oppDiv, cp_coeff_comp, hd]
    simp
  | f k =>
    refine cp_noW_of_coeff (fun d hd => ?_) (cp_cpU_noW E (N := N) hσ (.f k))
    change (oppDiv E _ _).coeff d = 0
    rw [cp_coeff_oppDiv, cp_coeff_comp, hd]
    simp

/-- The leading term of `[P_g σ(x_u)]_{≤N,0}`: `(−e^{−2iθ})^{idx u} x_u` modulo `γ`. -/
private lemma cp_upd_lead (E : ℝ) {N : ℕ} {σ : ObsVar → ObsPoly} (hσ : cpCoord σ) {u : ObsVar}
    (hu : u ≠ .w) : X .γ ^ 1 ∣ updPoly E N (σ u) - C (cpLam E ^ u.idx) * X u := by
  have h1 := cp_upd_order E (Nat.zero_le N) (c := σ u) (by simp)
  have h2 : X .γ ^ 1 ∣ zeroW (rotPoly E (σ u)) - zeroW (rotPoly E (X u)) := by
    rw [← map_sub, ← map_sub]
    exact cp_alg_dvd _ cp_zeroW_γ (cp_alg_dvd _ (cp_rot_γ E) (hσ.2.2.1 u))
  have h3 : zeroW (rotPoly E (X u)) = C (cpLam E ^ u.idx) * X u := by
    simp [rotPoly, zeroW, hu, cpLam]
  rw [← h3]
  have e : updPoly E N (σ u) - zeroW (rotPoly E (X u)) =
      (updPoly E N (σ u) - zeroW (rotPoly E (σ u))) +
        (zeroW (rotPoly E (σ u)) - zeroW (rotPoly E (X u))) := by ring
  rw [e]
  exact dvd_add h1 h2

private lemma cp_cpU_lead (E : ℝ) {N : ℕ} (hN : 1 ≤ N) {σ : ObsVar → ObsPoly} (hσ : cpCoord σ)
    {u : ObsVar} (hu : u ≠ .w) : X .γ ^ 1 ∣ cpU E N σ u - C (cpLam E ^ u.idx) * X u := by
  have hρ := cp_rev_X hN hσ.1 hσ.2.2.1
  have hργ := cp_rev_γ hN hσ.1 N
  have e : cpU E N σ u - C (cpLam E ^ u.idx) * X u =
      (truncG N (bind₁ (revCoord N σ N) (updPoly E N (σ u))) -
        bind₁ (revCoord N σ N) (updPoly E N (σ u))) +
      bind₁ (revCoord N σ N) (updPoly E N (σ u) - C (cpLam E ^ u.idx) * X u) +
      C (cpLam E ^ u.idx) * (revCoord N σ N u - X u) := by
    simp only [cpU, map_sub, map_mul, bind₁_C_right, bind₁_X_right]
    ring
  rw [e]
  exact dvd_add (dvd_add (cp_dvd_mono (by omega) (cp_truncG_sub N _))
    (cp_bind_dvd hργ (cp_upd_lead E hσ hu))) (Dvd.dvd.mul_left (hρ u) _)

/-- One correction step: `σ' ≡ σ + σ(c)` with `γ^s ∣ c`. Then the updates in the coordinates of `σ'`
differ from those in the coordinates of `σ` by `π₀ ρ_θ c_u − (−e^{−2iθ})^{idx u} c_u` modulo
`γ^{s+1}`. -/
private lemma cp_main {N s : ℕ} (hN : 1 ≤ N) (hs1 : 1 ≤ s) (hsN : s ≤ N) (E : ℝ)
    {σ σ' c : ObsVar → ObsPoly} (hσ : cpCoord σ) (hσ'γ : σ' .γ = X .γ)
    (hc : ∀ u, X .γ ^ s ∣ c u) (hcγ : c .γ = 0)
    (hσ' : ∀ u, X .γ ^ (N + 1) ∣ σ' u - (σ u + bind₁ σ (c u)))
    {u : ObsVar} (hu : u ≠ .w) :
    X .γ ^ (s + 1) ∣ (bind₁ (revCoord N σ' N) (updPoly E N (σ' u)) -
      bind₁ (revCoord N σ N) (updPoly E N (σ u))) -
        (zeroW (rotPoly E (c u)) - C (cpLam E ^ u.idx) * c u) := by
  set ρ := revCoord N σ N with hρdef
  set ρ' := revCoord N σ' N with hρ'def
  have hργ : ρ .γ = X .γ := cp_rev_γ hN hσ.1 N
  have hσX := hσ.2.2.1
  have hσ'X : ∀ v, X .γ ^ 1 ∣ σ' v - X v := fun v => by
    have e : σ' v - X v = (σ' v - (σ v + bind₁ σ (c v))) + (σ v - X v) + bind₁ σ (c v) := by
      ring
    rw [e]
    exact dvd_add (dvd_add (cp_dvd_mono (by omega) (hσ' v)) (hσX v))
      (cp_dvd_mono hs1 (cp_bind_dvd hσ.1 (hc v)))
  have hρ'γ : ρ' .γ = X .γ := cp_rev_γ hN hσ'γ N
  have hρinv := cp_rev_inv hN hσ.1 hσX
  have hρ'inv := cp_rev_inv hN hσ'γ hσ'X
  set τ : ObsVar → ObsPoly := fun v => ρ v - c v with hτdef
  have hτγ : τ .γ = X .γ := by simp [τ, hργ, hcγ]
  have hτσ : ∀ v, X .γ ^ (s + 1) ∣ bind₁ τ (σ v) - X v + c v := by
    intro v
    have h1 := cp_bind_shift hτγ hργ (j := s)
      (fun x => by simp only [τ, sub_sub_cancel_left]; exact (dvd_neg).mpr (hc x)) (hσX v)
    rw [add_comm 1 s] at h1
    have e : bind₁ τ (σ v) - X v + c v = (bind₁ ρ (σ v) - X v) +
        (bind₁ τ (σ v - X v) - bind₁ ρ (σ v - X v)) := by
      rw [map_sub, map_sub, bind₁_X_right, bind₁_X_right]
      simp only [τ]
      ring
    rw [e]
    exact dvd_add (cp_dvd_mono (by omega) (hρinv v)) h1
  have hτinv : ∀ v, X .γ ^ (s + 1) ∣ bind₁ τ (σ' v) - X v := by
    intro v
    set κ : ObsVar → ObsPoly := fun x => bind₁ τ (σ x) with hκdef
    have hκγ : κ .γ = X .γ := by simp only [κ, hσ.1, bind₁_X_right, hτγ]
    have hκ : ∀ x, X .γ ^ 1 ∣ κ x - X x := fun x => by
      have e : κ x - X x = (bind₁ τ (σ x) - X x + c x) - c x := by simp only [κ]; ring
      rw [e]
      exact dvd_sub (cp_dvd_mono (by omega) (hτσ x)) (cp_dvd_mono hs1 (hc x))
    have h2 := cp_bind_near_id hκγ hκ (hc v)
    have h3 : bind₁ τ (bind₁ σ (c v)) = bind₁ κ (c v) := by rw [bind₁_bind₁]
    have e : bind₁ τ (σ' v) - X v = bind₁ τ (σ' v - (σ v + bind₁ σ (c v))) +
        (bind₁ τ (σ v) - X v + c v) + (bind₁ τ (bind₁ σ (c v)) - c v) := by
      rw [map_sub, map_add]
      ring
    rw [e, h3]
    exact dvd_add (dvd_add (cp_dvd_mono (by omega) (cp_bind_dvd hτγ (hσ' v))) (hτσ v)) h2
  have hρ'τ : ∀ v, X .γ ^ (s + 1) ∣ ρ' v - τ v :=
    cp_inv_unique hσ'X hρ'γ hτγ (fun v => cp_dvd_mono (by omega) (hρ'inv v)) hτinv
  have hρ'ρ : ∀ v, X .γ ^ s ∣ ρ' v - ρ v := fun v => by
    have e : ρ' v - ρ v = (ρ' v - τ v) - c v := by simp only [τ]; ring
    rw [e]
    exact dvd_sub (cp_dvd_mono (by omega) (hρ'τ v)) (hc v)
  have hρ'X : ∀ v, X .γ ^ 1 ∣ ρ' v - X v := cp_rev_X hN hσ'γ hσ'X
  -- the change of the update before the substitution
  have hA : X .γ ^ (s + 1) ∣ (updPoly E N (σ' u) - updPoly E N (σ u)) -
      zeroW (rotPoly E (c u)) := by
    rw [← cp_upd_sub]
    have h1 := cp_upd_dvd E N (hσ' u)
    have h2 := cp_upd_order E hsN (cp_bind_dvd hσ.1 (hc u))
    have h3 : X .γ ^ (s + 1) ∣ zeroW (rotPoly E (bind₁ σ (c u))) - zeroW (rotPoly E (c u)) := by
      rw [← map_sub, ← map_sub]
      exact cp_alg_dvd _ cp_zeroW_γ (cp_alg_dvd _ (cp_rot_γ E)
        (cp_bind_near_id hσ.1 hσX (hc u)))
    have e : σ' u - σ u = (σ' u - (σ u + bind₁ σ (c u))) + bind₁ σ (c u) := by ring
    have e2 : updPoly E N (σ' u - σ u) - zeroW (rotPoly E (c u)) =
        updPoly E N (σ' u - (σ u + bind₁ σ (c u))) +
        (updPoly E N (bind₁ σ (c u)) - zeroW (rotPoly E (bind₁ σ (c u)))) +
        (zeroW (rotPoly E (bind₁ σ (c u))) - zeroW (rotPoly E (c u))) := by
      rw [e, cp_upd_add]
      ring
    rw [e2]
    exact dvd_add (dvd_add (cp_dvd_mono (by omega) h1) h2) h3
  have hZ : X .γ ^ s ∣ zeroW (rotPoly E (c u)) :=
    cp_alg_dvd _ cp_zeroW_γ (cp_alg_dvd _ (cp_rot_γ E) (hc u))
  have hAs : X .γ ^ s ∣ updPoly E N (σ' u) - updPoly E N (σ u) := by
    have e : updPoly E N (σ' u) - updPoly E N (σ u) =
        ((updPoly E N (σ' u) - updPoly E N (σ u)) - zeroW (rotPoly E (c u))) +
          zeroW (rotPoly E (c u)) := by ring
    rw [e]
    exact dvd_add (cp_dvd_mono (by omega) hA) hZ
  have hY := cp_upd_lead E (N := N) hσ hu
  have hB1 := cp_bind_near_id hρ'γ hρ'X hAs
  have hB2 := cp_bind_shift hρ'γ hργ hρ'ρ hY
  rw [add_comm 1 s] at hB2
  set a := updPoly E N (σ' u)
  set b := updPoly E N (σ u)
  have e : bind₁ ρ' a - bind₁ ρ b - (zeroW (rotPoly E (c u)) - C (cpLam E ^ u.idx) * c u) =
      (bind₁ ρ' (a - b) - (a - b)) + ((a - b) - zeroW (rotPoly E (c u))) +
      (bind₁ ρ' (b - C (cpLam E ^ u.idx) * X u) - bind₁ ρ (b - C (cpLam E ^ u.idx) * X u)) +
      C (cpLam E ^ u.idx) * (ρ' u - τ u) := by
    simp only [map_sub, map_mul, bind₁_C_right, bind₁_X_right, τ]
    ring
  rw [e]
  exact dvd_add (dvd_add (dvd_add hB1 hA) hB2) (Dvd.dvd.mul_left (hρ'τ u) _)

/-- The coefficients of the update after step `s`: unchanged below order `s`; at order `s` the
correction contributes `((−e^{−2iθ})^{deg} − (−e^{−2iθ})^{idx u})` times its coefficient. -/
private lemma cp_step_coeff {N s : ℕ} (hN : 1 ≤ N) (hs1 : 1 ≤ s) (hsN : s ≤ N) (E : ℝ)
    {σ : ObsVar → ObsPoly} (hσ : cpCoord σ) {u : ObsVar} (hu : u ≠ .w) (d : ObsVar →₀ ℕ) :
    (d .γ < s → (cpU E N (corrStep E N s σ) u).coeff d = (cpU E N σ u).coeff d) ∧
    (d .γ = s → (cpU E N (corrStep E N s σ) u).coeff d = (cpU E N σ u).coeff d +
        (cpLam E ^ obsDeg d - cpLam E ^ u.idx) * (cpC E N s σ u).coeff d) := by
  have hσ' : ∀ v, X .γ ^ (N + 1) ∣ corrStep E N s σ v - (σ v + bind₁ σ (cpC E N s σ v)) := by
    intro v
    cases v with
    | w =>
      rw [show corrStep E N s σ .w = X .w from rfl, show cpC E N s σ .w = 0 from rfl, hσ.2.1,
        map_zero, add_zero, sub_self]
      exact dvd_zero _
    | γ =>
      rw [show corrStep E N s σ .γ = X .γ from rfl, show cpC E N s σ .γ = 0 from rfl, hσ.1,
        map_zero, add_zero, sub_self]
      exact dvd_zero _
    | m k =>
      rw [cp_corrStep_eq E N s σ (fun h => ObsVar.noConfusion h) (fun h => ObsVar.noConfusion h)]
      exact cp_truncG_sub N _
    | f k =>
      rw [cp_corrStep_eq E N s σ (fun h => ObsVar.noConfusion h) (fun h => ObsVar.noConfusion h)]
      exact cp_truncG_sub N _
  have hmain := cp_main (σ' := corrStep E N s σ) hN hs1 hsN E hσ rfl (cp_cpC_dvd E N s σ) rfl
    hσ' hu
  have hdiff : X .γ ^ (s + 1) ∣ cpU E N (corrStep E N s σ) u - cpU E N σ u -
      truncG N (zeroW (rotPoly E (cpC E N s σ u)) - C (cpLam E ^ u.idx) * cpC E N s σ u) := by
    unfold cpU
    rw [← map_sub, ← map_sub]
    exact cp_truncG_dvd N hmain
  have hcoef : ∀ d : ObsVar →₀ ℕ, d .γ ≤ s →
      (cpU E N (corrStep E N s σ) u).coeff d - (cpU E N σ u).coeff d -
        (cpLam E ^ obsDeg d - cpLam E ^ u.idx) * (cpC E N s σ u).coeff d = 0 := by
    intro d hds
    have hdN : d .γ ≤ N := hds.trans hsN
    have h := cp_coeff_of_dvd hdiff (show d .γ < s + 1 by omega)
    simp only [coeff_sub, cp_coeff_truncG, hdN, ite_true, cp_coeff_zeroW, cp_coeff_rot,
      coeff_C_mul] at h
    by_cases hw : d .w = 0
    · simp only [hw, ite_true, one_mul] at h
      linear_combination h
    · have h0 : (cpC E N s σ u).coeff d = 0 :=
        (cp_noW_iff _).mp (cp_cpC_noW E N s hσ.2.2.2 u) d hw
      simp only [h0, mul_zero, sub_zero] at h ⊢
      exact h
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · have h0 : (cpC E N s σ u).coeff d = 0 := cp_coeff_of_dvd (cp_cpC_dvd E N s σ u) hd
    have := hcoef d hd.le
    rw [h0, mul_zero, sub_zero] at this
    exact sub_eq_zero.mp this
  · linear_combination hcoef d hd.le

private lemma cp_aux_zero (E : ℝ) (N : ℕ) : corrCoordAux E N 0 = X := rfl

private lemma cp_aux_succ (E : ℝ) (N s : ℕ) :
    corrCoordAux E N (s + 1) = corrStep E N (s + 1) (corrCoordAux E N s) := rfl

private lemma cp_aux_coord (E : ℝ) {N : ℕ} (hN : 1 ≤ N) : ∀ s, cpCoord (corrCoordAux E N s)
  | 0 => by
    rw [cp_aux_zero]
    exact ⟨rfl, rfl, fun u => by simp, fun u hu => X_mem_supported.mpr hu⟩
  | s + 1 => by
    have ih := cp_aux_coord E hN s
    rw [cp_aux_succ]
    refine ⟨rfl, rfl, fun u => ?_, fun u hu => ?_⟩
    · by_cases hw : u = .w
      · subst hw
        rw [show corrStep E N (s + 1) (corrCoordAux E N s) .w = X .w from rfl, sub_self]
        exact dvd_zero _
      by_cases hγ : u = .γ
      · subst hγ
        rw [show corrStep E N (s + 1) (corrCoordAux E N s) .γ = X .γ from rfl, sub_self]
        exact dvd_zero _
      rw [cp_corrStep_eq E N _ _ hw hγ]
      set Y := corrCoordAux E N s u + bind₁ (corrCoordAux E N s)
        (cpC E N (s + 1) (corrCoordAux E N s) u)
      have e : truncG N Y - X u = (truncG N Y - Y) + (corrCoordAux E N s u - X u) +
          bind₁ (corrCoordAux E N s) (cpC E N (s + 1) (corrCoordAux E N s) u) := by
        simp only [Y]
        ring
      rw [e]
      exact dvd_add (dvd_add (cp_dvd_mono (by omega) (cp_truncG_sub N Y)) (ih.2.2.1 u))
        (cp_dvd_mono (by omega) (cp_bind_dvd ih.1 (cp_cpC_dvd E N (s + 1) _ u)))
    · by_cases hγ : u = .γ
      · subst hγ
        rw [show corrStep E N (s + 1) (corrCoordAux E N s) .γ = X .γ from rfl]
        exact X_mem_supported.mpr hu
      rw [cp_corrStep_eq E N _ _ hu hγ]
      exact cp_truncG_noW N (Subalgebra.add_mem _ (ih.2.2.2 u hu)
        (cp_bind₁_supported _ (cp_cpC_noW E N (s + 1) ih.2.2.2 u) (fun v hv => ih.2.2.2 v hv)))

/-- Induction over the correction steps: after step `s`, the opposite-parity coefficients of the
update of `u` of orders `1, …, s` vanish, provided the denominators of (11.49)
[lg:eq:observable-correction] met along the way are nonzero. -/
private lemma cp_par (E : ℝ) {N : ℕ} (hN : 1 ≤ N) {u : ObsVar} (hu : u ≠ .w) (huγ : u ≠ .γ)
    (hgap : ∀ s < N, ∀ d ∈ (cpU E N (corrCoordAux E N s) u).support,
      ¬Even (obsDeg d - u.idx) → cpLam E ^ u.idx - cpLam E ^ obsDeg d ≠ 0) :
    ∀ s ≤ N, ∀ d : ObsVar →₀ ℕ, 1 ≤ d .γ → d .γ ≤ s → ¬Even (obsDeg d - u.idx) →
      (cpU E N (corrCoordAux E N s) u).coeff d = 0 := by
  intro s
  induction s with
  | zero => intro _ d h1 h2; omega
  | succ s ih =>
    intro hs d h1 h2 hodd
    have hσ := cp_aux_coord E hN s
    have hstep := cp_step_coeff hN (by omega : 1 ≤ s + 1) hs E hσ hu d
    rw [cp_aux_succ]
    rcases Nat.lt_or_ge (d .γ) (s + 1) with hlt | hge
    · rw [hstep.1 hlt]
      exact ih (by omega) d h1 (by omega) hodd
    · have heq : d .γ = s + 1 := by omega
      rw [hstep.2 heq, cp_cpC_eq E N _ _ hu huγ, cp_coeff_oppDiv, cp_coeff_comp]
      simp only [hodd, heq, ite_true, ite_false]
      by_cases hb : (cpU E N (corrCoordAux E N s) u).coeff d = 0
      · rw [hb]
        simp
      · have hne := hgap s (by omega) d (mem_support_iff.mpr hb) hodd
        rw [show cpLam E = -normalPhase E from rfl] at hne ⊢
        field_simp
        ring

private lemma cp_obsDeg_single (u : ObsVar) : obsDeg (Finsupp.single u 1) = u.idx := by
  simp [obsDeg, Finsupp.weight_apply, Finsupp.sum_single_index]

private lemma cp_corrUpd_eq (E : ℝ) (R : ℕ) (v : ObsVar) :
    corrUpd E R v = cpU E (R + 2) (corrCoordAux E (R + 2) (R + 2)) v := rfl

private lemma cp_parity_of_gap (E : ℝ) (R : ℕ) {u : ObsVar} (hu : u ≠ .w) (huγ : u ≠ .γ)
    (hgap : ∀ s < R + 2, ∀ d ∈ (cpU E (R + 2) (corrCoordAux E (R + 2) s) u).support,
      ¬Even (obsDeg d - u.idx) → cpLam E ^ u.idx - cpLam E ^ obsDeg d ≠ 0) :
    ∀ d ∈ (corrUpd E R u).support, Even (obsDeg d - u.idx) := by
  have hN : 1 ≤ R + 2 := by omega
  intro d hd
  by_contra hodd
  apply mem_support_iff.mp hd
  rw [cp_corrUpd_eq]
  rcases Nat.eq_zero_or_pos (d .γ) with h0 | hpos
  · have hl := cp_coeff_of_dvd (cp_cpU_lead E hN (cp_aux_coord E hN (R + 2)) hu)
      (show d .γ < 1 by omega)
    rw [coeff_sub, coeff_C_mul, coeff_X] at hl
    split_ifs at hl with hdu
    · exfalso
      apply hodd
      rw [← hdu, cp_obsDeg_single, sub_self]
      exact ⟨0, by simp⟩
    · linear_combination hl
  · by_cases hdN : d .γ ≤ R + 2
    · exact cp_par E hN hu huγ hgap (R + 2) le_rfl d hpos hdN hodd
    · unfold cpU
      rw [cp_coeff_truncG]
      simp [hdN]

private lemma cp_parityPart_eq {k : ℤ} {p : ObsPoly} (h : ∀ d ∈ p.support, Even (obsDeg d - k)) :
    parityPart k p = p := by
  unfold parityPart
  conv_rhs => rw [p.as_sum]
  exact Finset.sum_congr rfl fun d hd => by simp [h d hd]

/-! ### The `ℓ¹` norm of the coefficients -/

/-- The sum of the moduli of the coefficients. -/
private def cpL (p : ObsPoly) : ℝ := ∑ d ∈ p.support, ‖p.coeff d‖

private lemma cp_L_eq {p : ObsPoly} {S : Finset (ObsVar →₀ ℕ)} (h : p.support ⊆ S) :
    cpL p = ∑ d ∈ S, ‖p.coeff d‖ :=
  Finset.sum_subset h fun d _ hd => by rw [notMem_support_iff.mp hd, norm_zero]

private lemma cp_L_nonneg (p : ObsPoly) : 0 ≤ cpL p :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

private lemma cp_coeff_le_L (p : ObsPoly) (d : ObsVar →₀ ℕ) : ‖p.coeff d‖ ≤ cpL p := by
  by_cases hd : d ∈ p.support
  · exact Finset.single_le_sum (f := fun d => ‖p.coeff d‖) (fun _ _ => norm_nonneg _) hd
  · rw [notMem_support_iff.mp hd, norm_zero]
    exact cp_L_nonneg p

private lemma cp_L_add (p q : ObsPoly) : cpL (p + q) ≤ cpL p + cpL q := by
  rw [cp_L_eq support_add, cp_L_eq (p := p) Finset.subset_union_left,
    cp_L_eq (p := q) Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun d _ => by rw [cp_coeff_add]; exact norm_add_le _ _

private lemma cp_L_sub (p q : ObsPoly) : cpL (p - q) ≤ cpL p + cpL q := by
  rw [cp_L_eq (support_sub _ p q), cp_L_eq (p := p) Finset.subset_union_left,
    cp_L_eq (p := q) Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun d _ => by rw [coeff_sub]; exact norm_sub_le _ _

private lemma cp_L_zero : cpL 0 = 0 := by
  simp [cpL]

private lemma cp_L_monomial (u : ObsVar →₀ ℕ) (a : ℂ) : cpL (monomial u a) ≤ ‖a‖ := by
  rw [cp_L_eq support_monomial_subset, Finset.sum_singleton]
  simp

private lemma cp_L_sum {ι : Type*} (s : Finset ι) (f : ι → ObsPoly) :
    cpL (∑ i ∈ s, f i) ≤ ∑ i ∈ s, cpL (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [cp_L_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (cp_L_add _ _).trans (add_le_add le_rfl ih)

private lemma cp_L_mul (p q : ObsPoly) : cpL (p * q) ≤ cpL p * cpL q := by
  have e : p * q = ∑ a ∈ p.support, ∑ b ∈ q.support,
      monomial (a + b) (p.coeff a * q.coeff b) := by
    conv_lhs => rw [p.as_sum, q.as_sum]
    rw [Finset.sum_mul_sum]
    simp only [monomial_mul_monomial]
  have h2 : cpL p * cpL q = ∑ a ∈ p.support, ∑ b ∈ q.support, ‖p.coeff a‖ * ‖q.coeff b‖ := by
    unfold cpL
    rw [Finset.sum_mul_sum]
  rw [e, h2]
  refine (cp_L_sum _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  refine (cp_L_sum _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  exact (cp_L_monomial _ _).trans (norm_mul_le _ _)

private lemma cp_L_C (a : ℂ) : cpL (C a) ≤ ‖a‖ := by
  rw [C_apply]
  exact cp_L_monomial _ _

/-! ### Families of polynomials with uniform supports and coefficient bounds near `E = 0` -/

/-- A family `E ↦ f E` whose supports lie in one finite set and whose coefficient sums are
bounded, for `E` near `0`. -/
private def CpTame (f : ℝ → ObsPoly) : Prop :=
  ∃ S : Finset (ObsVar →₀ ℕ), ∃ K : ℝ, ∀ᶠ E in nhds (0 : ℝ), (f E).support ⊆ S ∧ cpL (f E) ≤ K

private lemma cp_tame_const (p : ObsPoly) : CpTame fun _ => p :=
  ⟨p.support, cpL p, Filter.Eventually.of_forall fun _ => ⟨subset_rfl, le_rfl⟩⟩

private lemma cp_tame_congr {f g : ℝ → ObsPoly} (hfg : ∀ᶠ E in nhds (0 : ℝ), f E = g E)
    (hf : CpTame f) : CpTame g := by
  obtain ⟨S, K, h⟩ := hf
  exact ⟨S, K, (h.and hfg).mono fun E ⟨h1, h2⟩ => h2 ▸ h1⟩

private lemma cp_tame_add {f g : ℝ → ObsPoly} (hf : CpTame f) (hg : CpTame g) :
    CpTame fun E => f E + g E := by
  obtain ⟨S, K, h⟩ := hf
  obtain ⟨S', K', h'⟩ := hg
  refine ⟨S ∪ S', K + K', (h.and h').mono fun E ⟨h1, h2⟩ => ⟨?_, ?_⟩⟩
  · exact support_add.trans (Finset.union_subset_union h1.1 h2.1)
  · exact (cp_L_add _ _).trans (add_le_add h1.2 h2.2)

private lemma cp_tame_sub {f g : ℝ → ObsPoly} (hf : CpTame f) (hg : CpTame g) :
    CpTame fun E => f E - g E := by
  obtain ⟨S, K, h⟩ := hf
  obtain ⟨S', K', h'⟩ := hg
  refine ⟨S ∪ S', K + K', (h.and h').mono fun E ⟨h1, h2⟩ => ⟨?_, ?_⟩⟩
  · exact (support_sub _ _ _).trans (Finset.union_subset_union h1.1 h2.1)
  · exact (cp_L_sub _ _).trans (add_le_add h1.2 h2.2)

private lemma cp_tame_mul {f g : ℝ → ObsPoly} (hf : CpTame f) (hg : CpTame g) :
    CpTame fun E => f E * g E := by
  obtain ⟨S, K, h⟩ := hf
  obtain ⟨S', K', h'⟩ := hg
  refine ⟨Finset.image₂ (· + ·) S S', K * K', (h.and h').mono fun E ⟨h1, h2⟩ => ⟨?_, ?_⟩⟩
  · intro d hd
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul _ _ hd)
    exact Finset.mem_image₂_of_mem (h1.1 ha) (h2.1 hb)
  · exact (cp_L_mul _ _).trans (mul_le_mul h1.2 h2.2 (cp_L_nonneg _)
      ((cp_L_nonneg _).trans h1.2))

private lemma cp_tame_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ObsPoly)
    (h : ∀ i ∈ s, CpTame (f i)) : CpTame fun E => ∑ i ∈ s, f i E := by
  induction s using Finset.induction_on with
  | empty => simpa using cp_tame_const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact cp_tame_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private lemma cp_tame_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ → ObsPoly)
    (h : ∀ i ∈ s, CpTame (f i)) : CpTame fun E => ∏ i ∈ s, f i E := by
  induction s using Finset.induction_on with
  | empty => simpa using cp_tame_const 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact cp_tame_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private lemma cp_tame_pow {f : ℝ → ObsPoly} (hf : CpTame f) (n : ℕ) : CpTame fun E => f E ^ n := by
  have := cp_tame_prod (Finset.range n) (fun _ => f) (fun _ _ => hf)
  simpa using this

private lemma cp_tame_C {a : ℝ → ℂ} (ha : ∃ A, ∀ᶠ E in nhds (0 : ℝ), ‖a E‖ ≤ A) :
    CpTame fun E => C (a E) := by
  obtain ⟨A, hA⟩ := ha
  refine ⟨{0}, A, hA.mono fun E h => ⟨?_, (cp_L_C _).trans h⟩⟩
  change (C (a E)).support ⊆ {0}
  rw [C_apply]
  exact support_monomial_subset

private lemma cp_tame_coeff {f : ℝ → ObsPoly} (hf : CpTame f) (d : ObsVar →₀ ℕ) :
    CpTame fun E => C ((f E).coeff d) := by
  obtain ⟨S, K, h⟩ := hf
  exact cp_tame_C ⟨K, h.mono fun E h1 => (cp_coeff_le_L _ _).trans h1.2⟩

private lemma cp_tame_dom {f g : ℝ → ObsPoly} (hf : CpTame f)
    (h : ∀ᶠ E in nhds (0 : ℝ), ∀ d, ‖(g E).coeff d‖ ≤ ‖(f E).coeff d‖) : CpTame g := by
  obtain ⟨S, K, hS⟩ := hf
  refine ⟨S, K, (hS.and h).mono fun E ⟨h1, h2⟩ => ?_⟩
  have hsub : (g E).support ⊆ (f E).support := by
    intro d hd
    rw [mem_support_iff] at hd ⊢
    intro h0
    apply hd
    have := h2 d
    rw [h0, norm_zero] at this
    exact norm_le_zero_iff.mp this
  refine ⟨hsub.trans h1.1, ?_⟩
  rw [cp_L_eq hsub]
  exact (Finset.sum_le_sum fun d _ => h2 d).trans h1.2

private lemma cp_sum_monomial {p : ObsPoly} {S : Finset (ObsVar →₀ ℕ)} (h : p.support ⊆ S) :
    p = ∑ d ∈ S, monomial d (p.coeff d) := by
  conv_lhs => rw [p.as_sum]
  exact Finset.sum_subset h fun d _ hd => by rw [notMem_support_iff.mp hd, monomial_zero]

private lemma cp_tame_bind {τ : ℝ → ObsVar → ObsPoly} (hτ : ∀ v, CpTame fun E => τ E v)
    {f : ℝ → ObsPoly} (hf : CpTame f) : CpTame fun E => bind₁ (τ E) (f E) := by
  obtain ⟨S, K, hS⟩ := hf
  refine cp_tame_congr (f := fun E => ∑ d ∈ S,
    C ((f E).coeff d) * ∏ v ∈ d.support, τ E v ^ d v) (hS.mono fun E h => ?_) ?_
  · conv_rhs => rw [cp_sum_monomial h.1]
    simp only [map_sum, bind₁_monomial]
  · exact cp_tame_sum S _ fun d _ => cp_tame_mul (cp_tame_coeff ⟨S, K, hS⟩ d)
      (cp_tame_prod _ _ fun v _ => cp_tame_pow (hτ v) _)

private lemma cp_tame_wick (r : ℕ) {f : ℝ → ObsPoly} (hf : CpTame f) :
    CpTame fun E => wickMap r (f E) := by
  obtain ⟨S, K, hS⟩ := hf
  refine cp_tame_congr (f := fun E => ∑ d ∈ S, C ((f E).coeff d) * wickMap r (monomial d 1))
    (hS.mono fun E h => ?_) ?_
  · conv_rhs => rw [cp_sum_monomial h.1]
    change _ = cpWick r _
    rw [map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [show monomial d ((f E).coeff d) = (f E).coeff d • monomial d (1 : ℂ) by
      rw [smul_monomial, smul_eq_mul, mul_one], map_smul, smul_eq_C_mul]
    rfl
  · exact cp_tame_sum S _ fun d _ => cp_tame_mul (cp_tame_coeff ⟨S, K, hS⟩ d)
      (cp_tame_const _)

private lemma cp_tame_rot {f : ℝ → ObsPoly} (hf : CpTame f) : CpTame fun E => rotPoly E (f E) :=
  cp_tame_dom hf (Filter.Eventually.of_forall fun E d => by
    rw [cp_coeff_rot, norm_mul, cp_norm_lam_zpow, one_mul])

private lemma cp_tame_zeroW {f : ℝ → ObsPoly} (hf : CpTame f) : CpTame fun E => zeroW (f E) :=
  cp_tame_dom hf (Filter.Eventually.of_forall fun E d => by
    rw [cp_coeff_zeroW, norm_mul]
    split_ifs <;> simp)

private lemma cp_tame_truncG (N : ℕ) {f : ℝ → ObsPoly} (hf : CpTame f) :
    CpTame fun E => truncG N (f E) :=
  cp_tame_dom hf (Filter.Eventually.of_forall fun E d => by
    rw [cp_coeff_truncG]
    split_ifs <;> simp)

private lemma cp_tame_comp (s : ℕ) {f : ℝ → ObsPoly} (hf : CpTame f) :
    CpTame fun E => weightedHomogeneousComponent ObsVar.gamWt s (f E) :=
  cp_tame_dom hf (Filter.Eventually.of_forall fun E d => by
    rw [cp_coeff_comp]
    split_ifs <;> simp)

/-! ### The window and the bound on `h_θ`

The opposite-parity gap (11.48) [lg:eq:opposite-parity-gap]. -/

private lemma cp_normalH_bdd (r : ℕ) :
    ∃ A : ℝ, ∀ᶠ E in nhds (0 : ℝ), ‖(((normalH E ^ (2 * r) : ℝ) : ℂ))‖ ≤ A := by
  have hc : ContinuousAt normalH 0 := by
    change ContinuousAt (fun E : ℝ => (2 * Real.sin (Real.arccos (E / 2)))⁻¹) 0
    refine ContinuousAt.inv₀ (by fun_prop) ?_
    simp [Real.arccos_zero]
  have hg : ContinuousAt (fun E => ‖(((normalH E ^ (2 * r) : ℝ) : ℂ))‖) 0 :=
    (Complex.continuous_ofReal.continuousAt.comp (hc.pow _)).norm
  exact ⟨_, (hg.eventually_lt continuousAt_const (lt_add_one _)).mono fun E h => h.le⟩

/-- (11.48) [lg:eq:opposite-parity-gap] near `E = 0`: for `a − b` odd with `|a − b| ≤ D`,
`|(−e^{−2iθ})^a − (−e^{−2iθ})^b| ≥ 1`. -/
private lemma cp_gap (D : ℕ) : ∀ᶠ E in nhds (0 : ℝ), ∀ a b : ℤ, ¬Even (a - b) →
    (a - b).natAbs ≤ D → 1 ≤ ‖cpLam E ^ a - cpLam E ^ b‖ := by
  have key : ∀ n : ℤ, ¬Even n → ∀ᶠ E in nhds (0 : ℝ),
      1 < ‖Complex.exp (n * (2 * ((freeAngle E : ℂ) * Complex.I))) - 1‖ := by
    intro n hn
    have hc : ContinuousAt
        (fun E : ℝ => ‖Complex.exp (n * (2 * ((freeAngle E : ℂ) * Complex.I))) - 1‖) 0 := by
      unfold freeAngle
      fun_prop
    refine continuousAt_const.eventually_lt hc ?_
    have h0 : Complex.exp (n * (2 * ((freeAngle 0 : ℂ) * Complex.I))) = -1 := by
      rw [show (n : ℂ) * (2 * ((freeAngle 0 : ℂ) * Complex.I)) = n * (π * Complex.I) by
        simp only [freeAngle, zero_div, Real.arccos_zero]
        push_cast
        ring,
        Complex.exp_int_mul, Complex.exp_pi_mul_I, Odd.neg_one_zpow (Int.not_even_iff_odd.mp hn)]
    simp only [h0]
    norm_num
  have hall := (Filter.eventually_all_finset ((Finset.Icc (-(D : ℤ)) D).filter
    (fun n => ¬Even n))).mpr (fun n hn => key n (Finset.mem_filter.mp hn).2)
  refine hall.mono fun E hE a b hab hD => ?_
  have hmem : a - b ∈ (Finset.Icc (-(D : ℤ)) D).filter (fun n => ¬Even n) := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, hab⟩ <;> omega
  have h1 := hE _ hmem
  have e : cpLam E ^ a - cpLam E ^ b = cpLam E ^ b *
      (Complex.exp (((a - b : ℤ) : ℂ) * (2 * ((freeAngle E : ℂ) * Complex.I))) - 1) := by
    rw [cp_lam_zpow, cp_lam_zpow, mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [e, norm_mul, cp_norm_lam_zpow, one_mul]
  exact h1.le

private lemma cp_gap_tame {f : ℝ → ObsPoly} (hf : CpTame f) (k : ℤ) :
    ∀ᶠ E in nhds (0 : ℝ), ∀ d ∈ (f E).support, ¬Even (obsDeg d - k) →
      1 ≤ ‖cpLam E ^ k - cpLam E ^ obsDeg d‖ := by
  obtain ⟨S, K, hS⟩ := hf
  refine ((cp_gap (S.sup fun d => (k - obsDeg d).natAbs)).and hS).mono
    fun E ⟨hg, h1⟩ d hd hodd => ?_
  refine hg k (obsDeg d) (fun he => hodd ?_)
    (Finset.le_sup (f := fun d => (k - obsDeg d).natAbs) (h1.1 hd))
  rw [← neg_sub]
  exact he.neg

/-! ### Uniform supports and bounds for the corrections -/

private lemma cp_tame_oppDiv (k : ℤ) {f : ℝ → ObsPoly} (hf : CpTame f) :
    CpTame fun E => oppDiv E k (f E) :=
  cp_tame_dom hf ((cp_gap_tame hf k).mono fun E hg d => by
    rw [cp_coeff_oppDiv]
    split_ifs with he
    · simp
    · by_cases hd : (f E).coeff d = 0
      · simp [hd]
      · rw [norm_div]
        exact div_le_self (norm_nonneg _) (hg d (mem_support_iff.mpr hd) he))

private lemma cp_tame_upd (N : ℕ) {f : ℝ → ObsPoly} (hf : CpTame f) :
    CpTame fun E => updPoly E N (f E) :=
  cp_tame_truncG N (cp_tame_sum _ _ fun r _ => cp_tame_mul (cp_tame_mul
    (cp_tame_C (cp_normalH_bdd r)) (cp_tame_const _))
    (cp_tame_zeroW (cp_tame_wick r (cp_tame_rot hf))))

private lemma cp_tame_rev (N : ℕ) {σ : ℝ → ObsVar → ObsPoly} (hσ : ∀ v, CpTame fun E => σ E v) :
    ∀ r v, CpTame fun E => revCoord N (σ E) r v
  | 0, v => by
    simp only [cp_rev_zero]
    exact cp_tame_const _
  | r + 1, v => by
    simp only [cp_rev_succ]
    exact cp_tame_truncG N (cp_tame_sub (cp_tame_const _)
      (cp_tame_bind (cp_tame_rev N hσ r) (cp_tame_sub (hσ v) (cp_tame_const _))))

private lemma cp_tame_cpU (N : ℕ) {σ : ℝ → ObsVar → ObsPoly} (hσ : ∀ v, CpTame fun E => σ E v)
    (v : ObsVar) : CpTame fun E => cpU E N (σ E) v :=
  cp_tame_truncG N (cp_tame_bind (cp_tame_rev N hσ N) (cp_tame_upd N (hσ v)))

private lemma cp_tame_step (N s : ℕ) {σ : ℝ → ObsVar → ObsPoly}
    (hσ : ∀ v, CpTame fun E => σ E v) : ∀ v, CpTame fun E => corrStep E N s (σ E) v
  | .w => cp_tame_const _
  | .γ => cp_tame_const _
  | .m _ => cp_tame_truncG N (cp_tame_add (hσ _) (cp_tame_bind hσ
      (cp_tame_oppDiv _ (cp_tame_comp s (cp_tame_cpU N hσ _)))))
  | .f _ => cp_tame_truncG N (cp_tame_add (hσ _) (cp_tame_bind hσ
      (cp_tame_oppDiv _ (cp_tame_comp s (cp_tame_cpU N hσ _)))))

private lemma cp_tame_aux (N : ℕ) : ∀ s v, CpTame fun E => corrCoordAux E N s v
  | 0, _ => cp_tame_const _
  | s + 1, v => cp_tame_step N (s + 1) (cp_tame_aux N s) v

private lemma cp_tame_fin {ι : Type*} (s : Finset ι) (F : ι → ℝ → ObsPoly)
    (h : ∀ i ∈ s, CpTame (F i)) : ∃ S : Finset (ObsVar →₀ ℕ), ∃ K : ℝ,
      ∀ᶠ E in nhds (0 : ℝ), ∀ i ∈ s, (F i E).support ⊆ S ∧ cpL (F i E) ≤ K := by
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨∅, 0, Filter.Eventually.of_forall fun _ i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s ha ih =>
    obtain ⟨S, K, hev⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    obtain ⟨S', K', hev'⟩ := h a (Finset.mem_insert_self a s)
    refine ⟨S ∪ S', max K K', (hev.and hev').mono fun E ⟨h1, h2⟩ i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact ⟨h2.1.trans Finset.subset_union_right, h2.2.trans (le_max_right _ _)⟩
    · exact ⟨(h1 i hi).1.trans Finset.subset_union_left, (h1 i hi).2.trans (le_max_left _ _)⟩

private lemma cp_window {P : ℝ → Prop} (h : ∀ᶠ E in nhds (0 : ℝ), P E) :
    ∃ E₁ : ℝ, 0 < E₁ ∧ ∀ E : ℝ, |E| ≤ E₁ → P E := by
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨ε / 2, half_pos hε, fun E hE => h ?_⟩
  rw [Real.dist_eq, sub_zero]
  linarith

/-- (11.45) [lg:eq:required-parity-updates]: on a window `|E| ≤ E₁` fixed after `R` and the
finite index set, every monomial of `[P_g M_k]_{≤R+2,0}` and `[P_g F_k]_{≤R+2,0}` in the corrected
coordinates has degree `≡ k (mod 2)`. -/
theorem parityPart_corrUpd (R : ℕ) (Ks : Finset NzInt) :
    ∃ E₁ : ℝ, 0 < E₁ ∧ ∀ E : ℝ, |E| ≤ E₁ → ∀ k ∈ Ks,
      parityPart k.1 (corrUpd E R (.m k)) = corrUpd E R (.m k) ∧
        parityPart k.1 (corrUpd E R (.f k)) = corrUpd E R (.f k) := by
  have hev : ∀ᶠ E in nhds (0 : ℝ), ∀ k ∈ Ks, ∀ s ∈ Finset.range (R + 2),
      ∀ v ∈ ({ObsVar.m k, ObsVar.f k} : Finset ObsVar),
      ∀ d ∈ (cpU E (R + 2) (corrCoordAux E (R + 2) s) v).support,
        ¬Even (obsDeg d - v.idx) → 1 ≤ ‖cpLam E ^ v.idx - cpLam E ^ obsDeg d‖ := by
    rw [Filter.eventually_all_finset]
    intro k _
    rw [Filter.eventually_all_finset]
    intro s _
    rw [Filter.eventually_all_finset]
    intro v _
    exact cp_gap_tame (cp_tame_cpU _ (cp_tame_aux _ s) v) v.idx
  obtain ⟨E₁, hE₁, hw⟩ := cp_window hev
  refine ⟨E₁, hE₁, fun E hE k hk => ?_⟩
  have hgap : ∀ v ∈ ({ObsVar.m k, ObsVar.f k} : Finset ObsVar), ∀ s < R + 2,
      ∀ d ∈ (cpU E (R + 2) (corrCoordAux E (R + 2) s) v).support,
        ¬Even (obsDeg d - v.idx) → cpLam E ^ v.idx - cpLam E ^ obsDeg d ≠ 0 := by
    intro v hv s hs d hd hodd h0
    have := hw E hE k hk s (Finset.mem_range.mpr hs) v hv d hd hodd
    rw [h0, norm_zero] at this
    linarith
  exact ⟨cp_parityPart_eq (cp_parity_of_gap E R (u := .m k) (fun h => ObsVar.noConfusion h)
      (fun h => ObsVar.noConfusion h) (hgap _ (by simp))),
    cp_parityPart_eq (cp_parity_of_gap E R (u := .f k) (fun h => ObsVar.noConfusion h)
      (fun h => ObsVar.noConfusion h) (hgap _ (by simp)))⟩

/-- The corrections are fixed polynomials (Lemma 11.8 [lg:lem:dynamic]): on a window fixed after `R`
and the finite index set, the supports of `M_k`, `F_k`, of the inverse polynomials and of the
corrected updates lie in one finite set of monomials, with coefficients bounded uniformly. -/
theorem corrCoeff_bounded (R : ℕ) (Ks : Finset NzInt) :
    ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ S : Finset (ObsVar →₀ ℕ), ∃ K : ℝ, 0 < K ∧ ∀ E : ℝ, |E| ≤ E₁ →
      ∀ k ∈ Ks, ∀ v ∈ [ObsVar.m k, ObsVar.f k],
        (corrCoord E R v).support ⊆ S ∧ (invCoord E R v).support ⊆ S ∧
          (corrUpd E R v).support ⊆ S ∧
          ∀ d, ‖(corrCoord E R v).coeff d‖ ≤ K ∧ ‖(invCoord E R v).coeff d‖ ≤ K ∧
            ‖(corrUpd E R v).coeff d‖ ≤ K := by
  have hσ : ∀ v, CpTame fun E => corrCoord E R v := cp_tame_aux (R + 2) (R + 2)
  have hρ : ∀ v, CpTame fun E => invCoord E R v := cp_tame_rev (R + 2) hσ (R + 2)
  have hU : ∀ v, CpTame fun E => corrUpd E R v := cp_tame_cpU (R + 2) hσ
  set V : Finset ObsVar := Ks.biUnion fun k => {ObsVar.m k, ObsVar.f k}
  obtain ⟨S1, K1, h1⟩ := cp_tame_fin V _ (fun v _ => hσ v)
  obtain ⟨S2, K2, h2⟩ := cp_tame_fin V _ (fun v _ => hρ v)
  obtain ⟨S3, K3, h3⟩ := cp_tame_fin V _ (fun v _ => hU v)
  obtain ⟨E₁, hE₁, hw⟩ := cp_window ((h1.and h2).and h3)
  refine ⟨E₁, hE₁, S1 ∪ S2 ∪ S3, max (max K1 K2) (max K3 1),
    lt_max_of_lt_right (lt_max_of_lt_right one_pos), fun E hE k hk v hv => ?_⟩
  have hvV : v ∈ V := by
    simp only [V, Finset.mem_biUnion]
    refine ⟨k, hk, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;> simp
  obtain ⟨⟨a1, a2⟩, a3⟩ := hw E hE
  obtain ⟨b1, c1⟩ := a1 v hvV
  obtain ⟨b2, c2⟩ := a2 v hvV
  obtain ⟨b3, c3⟩ := a3 v hvV
  refine ⟨b1.trans (Finset.subset_union_left.trans Finset.subset_union_left),
    b2.trans (Finset.subset_union_right.trans Finset.subset_union_left),
    b3.trans Finset.subset_union_right, fun d => ⟨?_, ?_, ?_⟩⟩
  · exact (cp_coeff_le_L _ d).trans (c1.trans ((le_max_left _ _).trans (le_max_left _ _)))
  · exact (cp_coeff_le_L _ d).trans (c2.trans ((le_max_right _ _).trans (le_max_left _ _)))
  · exact (cp_coeff_le_L _ d).trans (c3.trans ((le_max_left _ _).trans (le_max_right _ _)))

end LSBA
