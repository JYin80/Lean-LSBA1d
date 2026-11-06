import LSBA.Upper.CenterIdeal

/-!
# The corrected observables

The polynomial corrections `M_k`, `F_k` of Section 11.3.3 [lg:sec:general-state]: the truncated
`W⁰` update `[P_g p]_{≤N,0}` in the original coordinates; the coordinate reversion (11.46)
[lg:eq:coordinate-reversion]; the opposite-parity corrections (11.49)
[lg:eq:observable-correction] with denominators `(−e^{−2iθ})^k − (−e^{−2iθ})^{deg p}` (and
`a/0 = 0`); the definitions (11.50) [lg:eq:corrected-observables] `M_k = M_k^{(R+2)}`,
`F_k = F_k^{(R+2)}`, made for every `k ≠ 0` at once; the inverse polynomials `m^{[R+2]}(M)`,
`f^{[R+2]}(M, F)`; the update `[P_g M_k]_{≤R+2,0}`, `[P_g F_k]_{≤R+2,0}` in the corrected
coordinates (11.47) [lg:eq:current-coordinate-updates]. Polynomials in the corrected coordinates use
the same formal variables `m_k`, `f_k`. Properties: the form of the corrections and conjugation.
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `[P_g p]_{≤N,0}`: the `W⁰` terms of orders `1, g⁻², …, g⁻²ᴺ` of the expansion of Lemma 11.7
[lg:lem:ideal], in the original coordinates, with `γ = g⁻²`. -/
def updPoly (E : ℝ) (N : ℕ) (p : ObsPoly) : ObsPoly :=
  truncG N (∑ r ∈ Finset.range (N + 1),
    C (((normalH E ^ (2 * r) : ℝ) : ℂ)) * X .γ ^ r * zeroW (wickMap r (rotPoly E p)))

/-- The coordinate reversion (11.46) [lg:eq:coordinate-reversion] for coordinates
`σ(x) = x + Δ(x)`: `x^{[0]} = y`, `x^{[r+1]} = y − Δ(x^{[r]})`, truncated after `γ^N`. -/
def revCoord (N : ℕ) (σ : ObsVar → ObsPoly) : ℕ → ObsVar → ObsPoly
  | 0 => X
  | r + 1 => fun v => truncG N (X v - bind₁ (revCoord N σ r) (σ v - X v))

/-- The opposite-parity part of `p` divided as in (11.49) [lg:eq:observable-correction]: each
monomial of degree `d ≢ k (mod 2)` is divided by `(−e^{−2iθ})^k − (−e^{−2iθ})^d`. -/
def oppDiv (E : ℝ) (k : ℤ) (p : ObsPoly) : ObsPoly :=
  ∑ d ∈ p.support, if Even (obsDeg d - k) then 0 else
    monomial d (p.coeff d / ((-normalPhase E) ^ k - (-normalPhase E) ^ obsDeg d))

/-- Correction step `s` of (11.49) [lg:eq:observable-correction] applied to the coordinates `σ`
of step `s − 1`. -/
def corrStep (E : ℝ) (N s : ℕ) (σ : ObsVar → ObsPoly) : ObsVar → ObsPoly
  | .w => X .w
  | .γ => X .γ
  | v => truncG N (σ v + bind₁ σ (oppDiv E v.idx (weightedHomogeneousComponent ObsVar.gamWt s
      (truncG N (bind₁ (revCoord N σ N) (updPoly E N (σ v)))))))

/-- The coordinates after `s` correction steps, with truncation order `N`. -/
def corrCoordAux (E : ℝ) (N : ℕ) : ℕ → ObsVar → ObsPoly
  | 0 => X
  | s + 1 => corrStep E N (s + 1) (corrCoordAux E N s)

/-- The corrected coordinates (11.50) [lg:eq:corrected-observables]: `R + 2` steps, orders
through `g^{−2R−4}`. -/
def corrCoord (E : ℝ) (R : ℕ) : ObsVar → ObsPoly := corrCoordAux E (R + 2) (R + 2)

/-- `M_k` of (11.50) [lg:eq:corrected-observables] as a polynomial in the `m_j` and `γ`. -/
def corrObsM (E : ℝ) (R : ℕ) (k : NzInt) : ObsPoly := corrCoord E R (.m k)

/-- `F_k` of (11.50) [lg:eq:corrected-observables] as a polynomial in the `m_j`, `f_j` and `γ`. -/
def corrObsF (E : ℝ) (R : ℕ) (k : NzInt) : ObsPoly := corrCoord E R (.f k)

/-- The inverse polynomials `m^{[R+2]}(M)`, `f^{[R+2]}(M, F)` (Section 11.3.1
[lg:sec:state-estimates], (11.46) [lg:eq:coordinate-reversion]). -/
def invCoord (E : ℝ) (R : ℕ) : ObsVar → ObsPoly := revCoord (R + 2) (corrCoord E R) (R + 2)

/-- `[P_g M_k]_{≤R+2,0}`, `[P_g F_k]_{≤R+2,0}` in the corrected coordinates (11.47)
[lg:eq:current-coordinate-updates]. -/
def corrUpd (E : ℝ) (R : ℕ) (v : ObsVar) : ObsPoly :=
  truncG (R + 2) (bind₁ (invCoord E R) (updPoly E (R + 2) (corrCoord E R v)))

/-! ### Coefficients of the truncation and of the `γ`-components -/

private lemma cc_weight_gamWt (d : ObsVar →₀ ℕ) : Finsupp.weight ObsVar.gamWt d = d .γ := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_single ObsVar.γ]
  · simp [ObsVar.gamWt]
  · intro b _ hb
    cases b <;> simp_all [ObsVar.gamWt]
  · intro h
    simp [Finsupp.notMem_support_iff.mp h]

private lemma cc_coeff_comp (s : ℕ) (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (weightedHomogeneousComponent ObsVar.gamWt s p).coeff d =
      if d .γ = s then p.coeff d else 0 := by
  rw [coeff_weightedHomogeneousComponent, cc_weight_gamWt]

private lemma cc_coeff_truncG (N : ℕ) (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (truncG N p).coeff d = if d .γ ≤ N then p.coeff d else 0 := by
  unfold truncG
  rw [LinearMap.sum_apply, MvPolynomial.coeff_sum]
  simp only [cc_coeff_comp]
  rw [Finset.sum_ite_eq]
  simp

private lemma cc_truncG_idem (N : ℕ) (p : ObsPoly) : truncG N (truncG N p) = truncG N p := by
  ext d
  simp only [cc_coeff_truncG]
  split_ifs <;> rfl

private lemma cc_truncG_zero_truncG (N : ℕ) (p : ObsPoly) :
    truncG 0 (truncG N p) = truncG 0 p := by
  ext d
  simp only [cc_coeff_truncG]
  split_ifs with h1 h2
  · rfl
  · omega
  · rfl

private lemma cc_truncG_X {N : ℕ} {v : ObsVar} (h : v.gamWt ≤ N) : truncG N (X v) = X v := by
  ext d
  rw [cc_coeff_truncG]
  split_ifs with hd
  · rfl
  · rw [coeff_X]
    split_ifs with h2
    · exfalso
      apply hd
      subst h2
      cases v <;> simp_all [ObsVar.gamWt]
    · rfl

private lemma cc_support_truncG (N : ℕ) (p : ObsPoly) : (truncG N p).support ⊆ p.support := by
  intro d hd
  rw [mem_support_iff, cc_coeff_truncG] at hd
  rw [mem_support_iff]
  intro h
  exact hd (by simp [h])

private lemma cc_support_comp (s : ℕ) (p : ObsPoly) :
    (weightedHomogeneousComponent ObsVar.gamWt s p).support ⊆ p.support := by
  intro d hd
  rw [mem_support_iff, cc_coeff_comp] at hd
  rw [mem_support_iff]
  intro h
  exact hd (by simp [h])

private lemma cc_gamma_of_mem_comp {s : ℕ} {p : ObsPoly} {d : ObsVar →₀ ℕ}
    (hd : d ∈ (weightedHomogeneousComponent ObsVar.gamWt s p).support) : d .γ = s := by
  rw [mem_support_iff, cc_coeff_comp] at hd
  by_contra h
  exact hd (by simp [h])

private lemma cc_coeff_oppDiv (E : ℝ) (k : ℤ) (p : ObsPoly) (d : ObsVar →₀ ℕ) :
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

private lemma cc_support_oppDiv (E : ℝ) (k : ℤ) (p : ObsPoly) :
    (oppDiv E k p).support ⊆ p.support := by
  intro d hd
  rw [mem_support_iff, cc_coeff_oppDiv] at hd
  rw [mem_support_iff]
  intro h
  exact hd (by simp [h])

/-! ### Classes of polynomials determined by their monomials -/

private lemma cc_supported_of_support_subset {S : Set ObsVar} {p q : ObsPoly}
    (h : q.support ⊆ p.support) (hp : p ∈ supported ℂ S) : q ∈ supported ℂ S := by
  rw [MvPolynomial.mem_supported] at hp ⊢
  intro i hi
  rw [Finset.mem_coe, MvPolynomial.mem_vars_iff_mem_support] at hi
  obtain ⟨d, hd, hid⟩ := hi
  exact hp (by rw [Finset.mem_coe, MvPolynomial.mem_vars_iff_mem_support]; exact ⟨d, h hd, hid⟩)

private lemma cc_fIdeal_iff (p : ObsPoly) :
    p ∈ fIdeal ↔ ∀ d ∈ p.support, ∃ k : NzInt, d (.f k) ≠ 0 := by
  have h : fIdeal = Ideal.span (MvPolynomial.X '' (Set.range ObsVar.f) : Set ObsPoly) := by
    unfold fIdeal
    congr 1
    ext x
    simp [Set.mem_image]
  rw [h, mem_ideal_span_X_image]
  constructor
  · intro H d hd
    obtain ⟨i, ⟨k, rfl⟩, hi⟩ := H d hd
    exact ⟨k, hi⟩
  · intro H d hd
    obtain ⟨k, hk⟩ := H d hd
    exact ⟨.f k, ⟨k, rfl⟩, hk⟩

private lemma cc_fIdeal_of_support_subset {p q : ObsPoly} (h : q.support ⊆ p.support)
    (hp : p ∈ fIdeal) : q ∈ fIdeal := by
  rw [cc_fIdeal_iff] at hp ⊢
  exact fun d hd => hp d (h hd)

private lemma cc_bind₁_supported (τ : ObsVar → ObsPoly) {S T : Set ObsVar} {p : ObsPoly}
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

private lemma cc_bind₁_fIdeal (τ : ObsVar → ObsPoly) (hτ : ∀ k : NzInt, τ (.f k) ∈ fIdeal)
    {p : ObsPoly} (hp : p ∈ fIdeal) : bind₁ τ p ∈ fIdeal := by
  have h : fIdeal ≤ Ideal.comap (bind₁ τ : ObsPoly →ₐ[ℂ] ObsPoly) fIdeal := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    change bind₁ τ (X (.f k)) ∈ fIdeal
    rw [bind₁_X_right]
    exact hτ k
  exact Ideal.mem_comap.mp (h hp)

private lemma cc_bind₁_gamma_dvd {τ : ObsVar → ObsPoly} (hτ : τ .γ = X .γ) {s : ℕ}
    {q : ObsPoly} (hq : ∀ d ∈ q.support, s ≤ d .γ) : X .γ ^ s ∣ bind₁ τ q := by
  rw [q.as_sum, map_sum]
  refine Finset.dvd_sum fun d hd => ?_
  rw [bind₁_monomial]
  refine Dvd.dvd.mul_left ?_ _
  have hdv : X .γ ^ (d .γ) ∣ ∏ i ∈ d.support, τ i ^ d i := by
    by_cases hγ : ObsVar.γ ∈ d.support
    · rw [← Finset.mul_prod_erase _ _ hγ, hτ]
      exact dvd_mul_right _ _
    · have h0 : d .γ = 0 := by simpa using hγ
      rw [h0, pow_zero]
      exact one_dvd _
  exact (pow_dvd_pow _ (hq d hd)).trans hdv

private lemma cc_truncG_zero_gamma_mul {s : ℕ} (hs : 1 ≤ s) (y : ObsPoly) :
    truncG 0 (X .γ ^ s * y) = 0 := by
  ext d
  rw [cc_coeff_truncG, X_pow_eq_monomial, coeff_monomial_mul']
  split_ifs with h1 h2
  · exfalso
    rw [Finsupp.single_le_iff] at h2
    omega
  · simp
  · simp

private lemma cc_truncG_zero_bind₁ {τ : ObsVar → ObsPoly} (hτ : τ .γ = X .γ) {s : ℕ}
    (hs : 1 ≤ s) {q : ObsPoly} (hq : ∀ d ∈ q.support, s ≤ d .γ) : truncG 0 (bind₁ τ q) = 0 := by
  obtain ⟨y, hy⟩ := cc_bind₁_gamma_dvd hτ hq
  rw [hy, cc_truncG_zero_gamma_mul hs]

private lemma cc_traceVars_cases {v : ObsVar} (h : v ∈ traceVars) :
    v = .γ ∨ ∃ k, v = .m k := by
  rcases h with ⟨h0, hw⟩ | ⟨k, rfl⟩
  · cases v with
    | m k => exact absurd h0 k.2
    | f k => exact absurd h0 k.2
    | w => exact absurd rfl hw
    | γ => exact Or.inl rfl
  · exact Or.inr ⟨k, rfl⟩

private lemma cc_gamma_mem_traceVars : ObsVar.γ ∈ traceVars :=
  Or.inl ⟨rfl, fun h => ObsVar.noConfusion h⟩

private lemma cc_m_mem_traceVars (k : NzInt) : ObsVar.m k ∈ traceVars := Or.inr ⟨k, rfl⟩

private lemma cc_traceVars_subset : traceVars ⊆ {v : ObsVar | v ≠ .w} := by
  intro v hv
  rcases cc_traceVars_cases hv with rfl | ⟨k, rfl⟩
  · exact fun h => ObsVar.noConfusion h
  · exact fun h => ObsVar.noConfusion h

private lemma cc_mem_supported_univ (p : ObsPoly) : p ∈ supported ℂ Set.univ := by
  rw [supported_univ]
  trivial

private lemma cc_X_mem {S : Set ObsVar} {v : ObsVar} (h : v ∈ S) :
    (X v : ObsPoly) ∈ supported ℂ S := X_mem_supported.mpr h

private lemma cc_C_mem {S : Set ObsVar} (a : ℂ) : (C a : ObsPoly) ∈ supported ℂ S :=
  Subalgebra.algebraMap_mem _ a

private lemma cc_zeroW_X (v : ObsVar) : zeroW (X v) = if v = .w then 0 else X v := by
  simp [zeroW]

private lemma cc_zeroW_supported (p : ObsPoly) : zeroW p ∈ supported ℂ {v | v ≠ .w} := by
  refine cc_bind₁_supported (fun v => if v = .w then 0 else X v) (cc_mem_supported_univ p) ?_
  intro v _
  by_cases h : v = .w
  · simp only [h, ite_true]
    exact zero_mem _
  · simp only [h, ite_false]
    exact cc_X_mem h

private lemma cc_zeroW_traceVars {p : ObsPoly} (hp : p ∈ supported ℂ (traceVars ∪ {.w})) :
    zeroW p ∈ supported ℂ traceVars := by
  refine cc_bind₁_supported (fun v : ObsVar => if v = .w then (0 : ObsPoly) else X v) hp ?_
  intro v hv
  by_cases h : v = .w
  · simp only [h, ite_true]
    exact zero_mem _
  · simp only [h, ite_false]
    refine cc_X_mem ?_
    rcases hv with hv | hv
    · exact hv
    · exact absurd (Set.mem_singleton_iff.mp hv) h

private lemma cc_fIdeal_le_obs : fIdeal ≤ obsIdeal := Ideal.span_mono Set.subset_union_right

private lemma cc_zeroW_obsIdeal {p : ObsPoly} (hp : p ∈ obsIdeal) : zeroW p ∈ fIdeal := by
  have h : obsIdeal ≤ Ideal.comap (zeroW : ObsPoly →ₐ[ℂ] ObsPoly) fIdeal := by
    refine Ideal.span_le.mpr ?_
    rintro _ (hx | ⟨k, rfl⟩)
    · rw [Set.mem_singleton_iff.mp hx]
      change zeroW (X .w) ∈ fIdeal
      rw [cc_zeroW_X]
      simp
    · change zeroW (X (.f k)) ∈ fIdeal
      rw [cc_zeroW_X]
      simp only [ite_false, reduceCtorEq]
      exact Ideal.subset_span ⟨k, rfl⟩
  exact Ideal.mem_comap.mp (h hp)

private lemma cc_rotPoly_supported (E : ℝ) {S : Set ObsVar} {p : ObsPoly}
    (hp : p ∈ supported ℂ S) : rotPoly E p ∈ supported ℂ S := by
  refine cc_bind₁_supported (fun v => C ((-normalPhase E) ^ v.idx) * X v) hp ?_
  intro v hv
  exact Subalgebra.mul_mem _ (cc_C_mem _) (cc_X_mem hv)

private lemma cc_rotPoly_fIdeal (E : ℝ) {p : ObsPoly} (hp : p ∈ fIdeal) :
    rotPoly E p ∈ fIdeal := by
  refine cc_bind₁_fIdeal (fun v => C ((-normalPhase E) ^ v.idx) * X v) ?_ hp
  intro k
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)

private lemma cc_updPoly_traceVars (E : ℝ) (N : ℕ) {p : ObsPoly} (hp : p ∈ supported ℂ traceVars) :
    updPoly E N p ∈ supported ℂ traceVars := by
  unfold updPoly
  refine cc_supported_of_support_subset (cc_support_truncG N _) ?_
  refine Subalgebra.sum_mem _ fun r _ => ?_
  refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (cc_C_mem _)
    (Subalgebra.pow_mem _ (cc_X_mem cc_gamma_mem_traceVars) _)) ?_
  exact cc_zeroW_traceVars (wickMap_traceVars r _ (cc_rotPoly_supported E hp)).1

private lemma cc_updPoly_fIdeal (E : ℝ) (N : ℕ) {p : ObsPoly} (hp : p ∈ fIdeal) :
    updPoly E N p ∈ fIdeal := by
  unfold updPoly
  refine cc_fIdeal_of_support_subset (cc_support_truncG N _) ?_
  refine Ideal.sum_mem _ fun r _ => Ideal.mul_mem_left _ _ ?_
  exact cc_zeroW_obsIdeal (wickMap_mem_obsIdeal r (cc_fIdeal_le_obs (cc_rotPoly_fIdeal E hp)))

private lemma cc_updPoly_noW (E : ℝ) (N : ℕ) (p : ObsPoly) :
    updPoly E N p ∈ supported ℂ {v | v ≠ .w} := by
  unfold updPoly
  refine cc_supported_of_support_subset (cc_support_truncG N _) ?_
  refine Subalgebra.sum_mem _ fun r _ => ?_
  exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (cc_C_mem _)
    (Subalgebra.pow_mem _ (cc_X_mem (fun h => ObsVar.noConfusion h)) _)) (cc_zeroW_supported _)

/-! ### Invariants of the coordinate systems -/

/-- The polynomial shape of a coordinate system: `γ` fixed, `m_k ↦` polynomials in the `m_j`, `γ`,
`f_k ↦` polynomials without `w` in the ideal `(f_j)`. -/
private def ccRev (τ : ObsVar → ObsPoly) : Prop :=
  τ .γ = X .γ ∧ (∀ k : NzInt, τ (.m k) ∈ supported ℂ traceVars) ∧
    ∀ k : NzInt, τ (.f k) ∈ supported ℂ {v | v ≠ .w} ∧ τ (.f k) ∈ fIdeal

/-- The shape of the corrected coordinates, with the leading term `x_k`. -/
private def ccGood (σ : ObsVar → ObsPoly) : Prop :=
  ccRev σ ∧ (∀ k : NzInt, truncG 0 (σ (.m k)) = X (.m k)) ∧
    ∀ k : NzInt, truncG 0 (σ (.f k)) = X (.f k)

private lemma cc_ccRev_X : ccRev (X : ObsVar → ObsPoly) :=
  ⟨rfl, fun k => cc_X_mem (cc_m_mem_traceVars k), fun k =>
    ⟨cc_X_mem (fun h => ObsVar.noConfusion h), Ideal.subset_span ⟨k, rfl⟩⟩⟩

private lemma ccRev.bind_traceVars {τ : ObsVar → ObsPoly} (h : ccRev τ) {p : ObsPoly}
    (hp : p ∈ supported ℂ traceVars) : bind₁ τ p ∈ supported ℂ traceVars := by
  refine cc_bind₁_supported τ hp (fun v hv => ?_)
  rcases cc_traceVars_cases hv with rfl | ⟨k, rfl⟩
  · rw [h.1]
    exact cc_X_mem cc_gamma_mem_traceVars
  · exact h.2.1 k

private lemma ccRev.bind_noW {τ : ObsVar → ObsPoly} (h : ccRev τ) {p : ObsPoly}
    (hp : p ∈ supported ℂ {v | v ≠ .w}) : bind₁ τ p ∈ supported ℂ {v | v ≠ .w} := by
  refine cc_bind₁_supported τ hp (fun v hv => ?_)
  cases v with
  | m k => exact supported_mono cc_traceVars_subset (h.2.1 k)
  | f k => exact (h.2.2 k).1
  | w => exact absurd rfl hv
  | γ =>
    rw [h.1]
    exact cc_X_mem hv

private lemma ccRev.bind_fIdeal {τ : ObsVar → ObsPoly} (h : ccRev τ) {p : ObsPoly}
    (hp : p ∈ fIdeal) : bind₁ τ p ∈ fIdeal :=
  cc_bind₁_fIdeal τ (fun k => (h.2.2 k).2) hp

private lemma cc_revCoord_succ (N : ℕ) (σ : ObsVar → ObsPoly) (r : ℕ) (v : ObsVar) :
    revCoord N σ (r + 1) v = truncG N (X v - bind₁ (revCoord N σ r) (σ v - X v)) := by
  rw [revCoord]

private lemma cc_revCoord_rev {N : ℕ} (hN : 1 ≤ N) {σ : ObsVar → ObsPoly} (hσ : ccRev σ) :
    ∀ r, ccRev (revCoord N σ r)
  | 0 => cc_ccRev_X
  | r + 1 => by
    have ih := cc_revCoord_rev hN hσ r
    refine ⟨?_, fun k => ?_, fun k => ⟨?_, ?_⟩⟩
    · rw [cc_revCoord_succ]
      rw [hσ.1, sub_self, map_zero, sub_zero]
      exact cc_truncG_X (by simp [ObsVar.gamWt]; omega)
    · rw [cc_revCoord_succ]
      exact cc_supported_of_support_subset (cc_support_truncG N _)
        (Subalgebra.sub_mem _ (cc_X_mem (cc_m_mem_traceVars k))
          (ih.bind_traceVars (Subalgebra.sub_mem _ (hσ.2.1 k) (cc_X_mem (cc_m_mem_traceVars k)))))
    · rw [cc_revCoord_succ]
      have hX : (X (.f k) : ObsPoly) ∈ supported ℂ {v | v ≠ .w} :=
        cc_X_mem (fun h => ObsVar.noConfusion h)
      exact cc_supported_of_support_subset (cc_support_truncG N _)
        (Subalgebra.sub_mem _ hX (ih.bind_noW (Subalgebra.sub_mem _ (hσ.2.2 k).1 hX)))
    · rw [cc_revCoord_succ]
      have hX : (X (.f k) : ObsPoly) ∈ fIdeal := Ideal.subset_span ⟨k, rfl⟩
      exact cc_fIdeal_of_support_subset (cc_support_truncG N _)
        (Ideal.sub_mem _ hX (ih.bind_fIdeal (Ideal.sub_mem _ (hσ.2.2 k).2 hX)))

/-! ### One correction step -/

/-- The correction term of step `s` for the variable `v` (before the substitution `bind₁ σ`). -/
private def ccInner (E : ℝ) (N s : ℕ) (σ : ObsVar → ObsPoly) (v : ObsVar) : ObsPoly :=
  oppDiv E v.idx (weightedHomogeneousComponent ObsVar.gamWt s
    (truncG N (bind₁ (revCoord N σ N) (updPoly E N (σ v)))))

private lemma cc_corrStep_eq (E : ℝ) (N s : ℕ) (σ : ObsVar → ObsPoly) {v : ObsVar}
    (hw : v ≠ .w) (hγ : v ≠ .γ) :
    corrStep E N s σ v = truncG N (σ v + bind₁ σ (ccInner E N s σ v)) := by
  cases v with
  | m k => rfl
  | f k => rfl
  | w => exact absurd rfl hw
  | γ => exact absurd rfl hγ

private lemma cc_corrStep_w (E : ℝ) (N s : ℕ) (σ : ObsVar → ObsPoly) :
    corrStep E N s σ .w = X .w := rfl

private lemma cc_corrStep_γ (E : ℝ) (N s : ℕ) (σ : ObsVar → ObsPoly) :
    corrStep E N s σ .γ = X .γ := rfl

private lemma cc_support_inner (E : ℝ) (N s : ℕ) (σ : ObsVar → ObsPoly) (v : ObsVar) :
    (ccInner E N s σ v).support ⊆
      (bind₁ (revCoord N σ N) (updPoly E N (σ v))).support :=
  (cc_support_oppDiv _ _ _).trans ((cc_support_comp _ _).trans (cc_support_truncG _ _))

private lemma cc_gamma_inner (E : ℝ) (N s : ℕ) (σ : ObsVar → ObsPoly) (v : ObsVar)
    {d : ObsVar →₀ ℕ} (hd : d ∈ (ccInner E N s σ v).support) : d .γ = s :=
  cc_gamma_of_mem_comp (cc_support_oppDiv _ _ _ hd)

private lemma cc_corrStep_trunc0 (E : ℝ) (N s : ℕ) (hs : 1 ≤ s) {σ : ObsVar → ObsPoly}
    (hγ : σ .γ = X .γ) {v : ObsVar} (hw : v ≠ .w) (hv : v ≠ .γ)
    (h0 : truncG 0 (σ v) = X v) : truncG 0 (corrStep E N s σ v) = X v := by
  rw [cc_corrStep_eq E N s σ hw hv, cc_truncG_zero_truncG, map_add, h0,
    cc_truncG_zero_bind₁ hγ hs (fun d hd => (cc_gamma_inner E N s σ v hd).ge), add_zero]

private lemma cc_corrStep_trunc (E : ℝ) (N s : ℕ) (hN : 1 ≤ N) (σ : ObsVar → ObsPoly)
    (v : ObsVar) : truncG N (corrStep E N s σ v) = corrStep E N s σ v := by
  cases v with
  | m k =>
    rw [cc_corrStep_eq E N s σ (fun h => ObsVar.noConfusion h) (fun h => ObsVar.noConfusion h)]
    exact cc_truncG_idem _ _
  | f k =>
    rw [cc_corrStep_eq E N s σ (fun h => ObsVar.noConfusion h) (fun h => ObsVar.noConfusion h)]
    exact cc_truncG_idem _ _
  | w =>
    rw [cc_corrStep_w]
    exact cc_truncG_X (by simp [ObsVar.gamWt])
  | γ =>
    rw [cc_corrStep_γ]
    exact cc_truncG_X (by simp [ObsVar.gamWt]; omega)

private lemma cc_corrStep_good (E : ℝ) (N s : ℕ) (hN : 1 ≤ N) (hs : 1 ≤ s)
    {σ : ObsVar → ObsPoly} (hσ : ccGood σ) : ccGood (corrStep E N s σ) := by
  have hrev := cc_revCoord_rev hN hσ.1 N
  have hm (k : NzInt) : (ObsVar.m k) ≠ .w := fun h => ObsVar.noConfusion h
  have hm' (k : NzInt) : (ObsVar.m k) ≠ .γ := fun h => ObsVar.noConfusion h
  have hf (k : NzInt) : (ObsVar.f k) ≠ .w := fun h => ObsVar.noConfusion h
  have hf' (k : NzInt) : (ObsVar.f k) ≠ .γ := fun h => ObsVar.noConfusion h
  refine ⟨⟨cc_corrStep_γ E N s σ, fun k => ?_, fun k => ⟨?_, ?_⟩⟩, fun k => ?_, fun k => ?_⟩
  · rw [cc_corrStep_eq E N s σ (hm k) (hm' k)]
    refine cc_supported_of_support_subset (cc_support_truncG N _)
      (Subalgebra.add_mem _ (hσ.1.2.1 k) (hσ.1.bind_traceVars ?_))
    exact cc_supported_of_support_subset (cc_support_inner E N s σ _)
      (hrev.bind_traceVars (cc_updPoly_traceVars E N (hσ.1.2.1 k)))
  · rw [cc_corrStep_eq E N s σ (hf k) (hf' k)]
    refine cc_supported_of_support_subset (cc_support_truncG N _)
      (Subalgebra.add_mem _ (hσ.1.2.2 k).1 (hσ.1.bind_noW ?_))
    exact cc_supported_of_support_subset (cc_support_inner E N s σ _)
      (hrev.bind_noW (cc_updPoly_noW E N _))
  · rw [cc_corrStep_eq E N s σ (hf k) (hf' k)]
    refine cc_fIdeal_of_support_subset (cc_support_truncG N _)
      (Ideal.add_mem _ (hσ.1.2.2 k).2 (hσ.1.bind_fIdeal ?_))
    exact cc_fIdeal_of_support_subset (cc_support_inner E N s σ _)
      (hrev.bind_fIdeal (cc_updPoly_fIdeal E N (hσ.1.2.2 k).2))
  · exact cc_corrStep_trunc0 E N s hs hσ.1.1 (hm k) (hm' k) (hσ.2.1 k)
  · exact cc_corrStep_trunc0 E N s hs hσ.1.1 (hf k) (hf' k) (hσ.2.2 k)

private lemma cc_ccGood_X : ccGood (X : ObsVar → ObsPoly) :=
  ⟨cc_ccRev_X, fun k => cc_truncG_X (by simp [ObsVar.gamWt]),
    fun k => cc_truncG_X (by simp [ObsVar.gamWt])⟩

private lemma cc_corrCoordAux_succ (E : ℝ) (N s : ℕ) :
    corrCoordAux E N (s + 1) = corrStep E N (s + 1) (corrCoordAux E N s) := rfl

private lemma cc_corrCoordAux_good (E : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∀ s, ccGood (corrCoordAux E N s)
  | 0 => cc_ccGood_X
  | s + 1 => by
    rw [cc_corrCoordAux_succ]
    exact cc_corrStep_good E N (s + 1) hN (by omega) (cc_corrCoordAux_good E N hN s)

private lemma cc_corrCoordAux_trunc (E : ℝ) (N : ℕ) (hN : 1 ≤ N) (s : ℕ) (hs : 1 ≤ s)
    (v : ObsVar) : truncG N (corrCoordAux E N s v) = corrCoordAux E N s v := by
  obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  rw [cc_corrCoordAux_succ]
  exact cc_corrStep_trunc E N _ hN _ v

/-! ### Conjugation -/

private lemma cc_neg_neg (v : ObsVar) : v.neg.neg = v := by
  cases v with
  | m k => exact congrArg ObsVar.m (Subtype.ext (neg_neg k.1))
  | f k => exact congrArg ObsVar.f (Subtype.ext (neg_neg k.1))
  | w => rfl
  | γ => rfl

private lemma cc_neg_injective : Function.Injective ObsVar.neg :=
  Function.LeftInverse.injective cc_neg_neg

private lemma cc_idx_neg (v : ObsVar) : v.neg.idx = -v.idx := by
  cases v <;> simp [ObsVar.neg, ObsVar.idx]

private lemma cc_conj_X (v : ObsVar) : conjPoly (X v) = X v.neg := by
  simp [conjPoly]

private lemma cc_conj_C (a : ℂ) : conjPoly (C a) = C (starRingEnd ℂ a) := by
  simp [conjPoly]

private lemma cc_conj_eq (p : ObsPoly) :
    conjPoly p = MvPolynomial.map (starRingEnd ℂ) (rename ObsVar.neg p) := by
  refine hom_eq_hom conjPoly
    ((MvPolynomial.map (starRingEnd ℂ)).comp (rename ObsVar.neg : ObsPoly →ₐ[ℂ] ObsPoly).toRingHom)
    ?_ ?_ p
  · ext r
    simp [cc_conj_C]
  · intro v
    simp [cc_conj_X]

private lemma cc_mapDomain_neg_neg (d : ObsVar →₀ ℕ) :
    (d.mapDomain ObsVar.neg).mapDomain ObsVar.neg = d := by
  rw [← Finsupp.mapDomain_comp]
  have : (ObsVar.neg ∘ ObsVar.neg : ObsVar → ObsVar) = id := funext cc_neg_neg
  rw [this, Finsupp.mapDomain_id]

private lemma cc_coeff_conj (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (conjPoly p).coeff d = starRingEnd ℂ (p.coeff (d.mapDomain ObsVar.neg)) := by
  rw [cc_conj_eq, MvPolynomial.coeff_map]
  congr 1
  have := coeff_rename_mapDomain ObsVar.neg cc_neg_injective p (d.mapDomain ObsVar.neg)
  rwa [cc_mapDomain_neg_neg] at this

private lemma cc_mapDomain_neg_gamma (d : ObsVar →₀ ℕ) : (d.mapDomain ObsVar.neg) .γ = d .γ := by
  exact Finsupp.mapDomain_apply_of_injective cc_neg_injective d ObsVar.γ

private lemma cc_obsDeg_mapDomain_neg (d : ObsVar →₀ ℕ) :
    obsDeg (d.mapDomain ObsVar.neg) = -obsDeg d := by
  unfold obsDeg
  rw [Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (h := fun i c => c • ObsVar.idx i) (fun _ => zero_smul _ _)
      (fun _ _ _ => add_smul _ _ _)]
  simp only [Finsupp.sum, cc_idx_neg, smul_neg, Finset.sum_neg_distrib]

private lemma cc_conj_bind₁ {τ : ObsVar → ObsPoly} (hτ : ∀ v, conjPoly (τ v) = τ v.neg)
    (p : ObsPoly) : conjPoly (bind₁ τ p) = bind₁ τ (conjPoly p) := by
  refine hom_eq_hom (conjPoly.comp (bind₁ τ : ObsPoly →ₐ[ℂ] ObsPoly).toRingHom)
    ((bind₁ τ : ObsPoly →ₐ[ℂ] ObsPoly).toRingHom.comp conjPoly) ?_ ?_ p
  · ext r
    simp [cc_conj_C]
  · intro v
    simp [hτ, cc_conj_X]

private lemma cc_conj_zpow (E : ℝ) (k : ℤ) :
    starRingEnd ℂ ((-normalPhase E) ^ k) = (-normalPhase E) ^ (-k) := by
  have h : starRingEnd ℂ (-normalPhase E) = (-normalPhase E)⁻¹ := by
    unfold normalPhase
    rw [neg_neg, ← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  rw [map_zpow₀, h, inv_zpow, zpow_neg]

private lemma cc_conj_rot (E : ℝ) (p : ObsPoly) :
    conjPoly (rotPoly E p) = rotPoly E (conjPoly p) := by
  refine hom_eq_hom (conjPoly.comp (rotPoly E : ObsPoly →ₐ[ℂ] ObsPoly).toRingHom)
    ((rotPoly E : ObsPoly →ₐ[ℂ] ObsPoly).toRingHom.comp conjPoly) ?_ ?_ p
  · ext r
    simp [cc_conj_C, rotPoly]
  · intro v
    have h1 : rotPoly E (X v) = C ((-normalPhase E) ^ v.idx) * X v := by simp [rotPoly]
    have h2 : rotPoly E (X v.neg) = C ((-normalPhase E) ^ v.neg.idx) * X v.neg := by
      simp [rotPoly]
    change conjPoly (rotPoly E (X v)) = rotPoly E (conjPoly (X v))
    rw [cc_conj_X, h1, h2, map_mul, cc_conj_C, cc_conj_X, cc_conj_zpow, cc_idx_neg]

private lemma cc_conj_zeroW (p : ObsPoly) : conjPoly (zeroW p) = zeroW (conjPoly p) := by
  refine hom_eq_hom (conjPoly.comp (zeroW : ObsPoly →ₐ[ℂ] ObsPoly).toRingHom)
    ((zeroW : ObsPoly →ₐ[ℂ] ObsPoly).toRingHom.comp conjPoly) ?_ ?_ p
  · ext r
    simp [cc_conj_C, zeroW]
  · intro v
    cases v <;> simp [zeroW, cc_conj_X, ObsVar.neg]

private lemma cc_conj_truncG (N : ℕ) (p : ObsPoly) :
    conjPoly (truncG N p) = truncG N (conjPoly p) := by
  ext d
  rw [cc_coeff_conj, cc_coeff_truncG, cc_coeff_truncG, cc_coeff_conj, cc_mapDomain_neg_gamma]
  split_ifs <;> simp

private lemma cc_conj_comp (s : ℕ) (p : ObsPoly) :
    conjPoly (weightedHomogeneousComponent ObsVar.gamWt s p) =
      weightedHomogeneousComponent ObsVar.gamWt s (conjPoly p) := by
  ext d
  rw [cc_coeff_conj, cc_coeff_comp, cc_coeff_comp, cc_coeff_conj, cc_mapDomain_neg_gamma]
  split_ifs <;> simp

private lemma cc_conj_oppDiv (E : ℝ) (k : ℤ) (p : ObsPoly) :
    conjPoly (oppDiv E k p) = oppDiv E (-k) (conjPoly p) := by
  ext d
  rw [cc_coeff_conj, cc_coeff_oppDiv, cc_coeff_oppDiv, cc_coeff_conj, cc_obsDeg_mapDomain_neg]
  have hE : Even (-obsDeg d - k) ↔ Even (obsDeg d - -k) := by
    simp only [Int.even_sub, even_neg]
  by_cases h : Even (obsDeg d - -k)
  · simp only [h, hE.mpr h, ite_true, map_zero]
  · have h' : ¬ Even (-obsDeg d - k) := fun h2 => h (hE.mp h2)
    simp only [h, h', ite_false, map_div₀, map_sub, cc_conj_zpow, neg_neg]

private lemma cc_conj_updPoly (E : ℝ) (N : ℕ) (p : ObsPoly) :
    conjPoly (updPoly E N p) = updPoly E N (conjPoly p) := by
  unfold updPoly
  rw [cc_conj_truncG, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_mul, map_mul, map_pow, cc_conj_C, Complex.conj_ofReal, cc_conj_X, cc_conj_zeroW,
    ← wickMap_conjPoly, cc_conj_rot]
  rfl

/-- Conjugation symmetry of a coordinate system: `\overline{σ(x_k)} = σ(x_{−k})`. -/
private def ccSym (σ : ObsVar → ObsPoly) : Prop := ∀ v, conjPoly (σ v) = σ v.neg

private lemma cc_sym_X : ccSym (X : ObsVar → ObsPoly) := fun v => cc_conj_X v

private lemma cc_revCoord_sym (N : ℕ) {σ : ObsVar → ObsPoly} (hσ : ccSym σ) :
    ∀ r, ccSym (revCoord N σ r)
  | 0 => cc_sym_X
  | r + 1 => by
    intro v
    have ih := cc_revCoord_sym N hσ r
    rw [cc_revCoord_succ, cc_revCoord_succ, cc_conj_truncG, map_sub conjPoly, cc_conj_X,
      cc_conj_bind₁ ih, map_sub conjPoly, hσ v, cc_conj_X]

private lemma cc_conj_inner (E : ℝ) (N s : ℕ) {σ : ObsVar → ObsPoly} (hσ : ccSym σ)
    (v : ObsVar) : conjPoly (ccInner E N s σ v) = ccInner E N s σ v.neg := by
  unfold ccInner
  rw [cc_conj_oppDiv, cc_conj_comp, cc_conj_truncG, cc_conj_bind₁ (cc_revCoord_sym N hσ N),
    cc_conj_updPoly, hσ v, cc_idx_neg]

private lemma cc_corrStep_sym (E : ℝ) (N s : ℕ) {σ : ObsVar → ObsPoly} (hσ : ccSym σ) :
    ccSym (corrStep E N s σ) := by
  intro v
  cases v with
  | m k =>
    rw [cc_corrStep_eq E N s σ (fun h => ObsVar.noConfusion h) (fun h => ObsVar.noConfusion h),
      cc_corrStep_eq E N s σ (v := (ObsVar.m k).neg) (fun h => ObsVar.noConfusion h)
        (fun h => ObsVar.noConfusion h),
      cc_conj_truncG, map_add conjPoly, cc_conj_bind₁ hσ, cc_conj_inner E N s hσ, hσ]
  | f k =>
    rw [cc_corrStep_eq E N s σ (fun h => ObsVar.noConfusion h) (fun h => ObsVar.noConfusion h),
      cc_corrStep_eq E N s σ (v := (ObsVar.f k).neg) (fun h => ObsVar.noConfusion h)
        (fun h => ObsVar.noConfusion h),
      cc_conj_truncG, map_add conjPoly, cc_conj_bind₁ hσ, cc_conj_inner E N s hσ, hσ]
  | w =>
    rw [cc_corrStep_w, cc_conj_X]
    rfl
  | γ =>
    rw [cc_corrStep_γ, cc_conj_X]
    rfl

private lemma cc_corrCoordAux_sym (E : ℝ) (N : ℕ) : ∀ s, ccSym (corrCoordAux E N s)
  | 0 => cc_sym_X
  | s + 1 => by
    rw [cc_corrCoordAux_succ]
    exact cc_corrStep_sym E N _ (cc_corrCoordAux_sym E N s)

/-- The form of the corrections (Lemma 11.8 [lg:lem:dynamic]): `M_k = m_k + Σ_{r=1}^{R+2} g^{−2r}
𝓜_{k,r}(m)` and `F_k = f_k + Σ_{r=1}^{R+2} g^{−2r} 𝓕_{k,r}(m, f)` with every monomial of `F_k`
containing some `f_j`; the inverse polynomials for `f` lie in the ideal of the `F_j`. -/
theorem corrObs_form (E : ℝ) (R : ℕ) (k : NzInt) :
    truncG 0 (corrObsM E R k) = X (.m k) ∧ truncG (R + 2) (corrObsM E R k) = corrObsM E R k ∧
      corrObsM E R k ∈ supported ℂ traceVars ∧
      truncG 0 (corrObsF E R k) = X (.f k) ∧ truncG (R + 2) (corrObsF E R k) = corrObsF E R k ∧
      corrObsF E R k ∈ supported ℂ ({v | v ≠ .w}) ∧ corrObsF E R k ∈ fIdeal ∧
      invCoord E R (.f k) ∈ fIdeal := by
  have hN : 1 ≤ R + 2 := by omega
  have hg : ccGood (corrCoord E R) := cc_corrCoordAux_good E (R + 2) hN (R + 2)
  have htr : ∀ v, truncG (R + 2) (corrCoord E R v) = corrCoord E R v :=
    fun v => cc_corrCoordAux_trunc E (R + 2) hN (R + 2) (by omega) v
  exact ⟨hg.2.1 k, htr _, hg.1.2.1 k, hg.2.2 k, htr _, (hg.1.2.2 k).1, (hg.1.2.2 k).2,
    ((cc_revCoord_rev hN hg.1 (R + 2)).2.2 k).2⟩

/-- `M_{−k} = \overline{M_k}`, `F_{−k} = \overline{F_k}` (Section 11.3.3
[lg:sec:general-state]). -/
theorem conjPoly_corrObs (E : ℝ) (R : ℕ) (k : NzInt) :
    conjPoly (corrObsM E R k) = corrObsM E R ⟨-k.1, neg_ne_zero.mpr k.2⟩ ∧
      conjPoly (corrObsF E R k) = corrObsF E R ⟨-k.1, neg_ne_zero.mpr k.2⟩ := by
  have hs : ccSym (corrCoord E R) := cc_corrCoordAux_sym E (R + 2) (R + 2)
  exact ⟨hs (.m k), hs (.f k)⟩

end LSBA
