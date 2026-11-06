import LSBA.Upper.CorrectorLinear
import LSBA.Upper.CorrectorQ

/-!
# The remainders of the linear expansions

The remainders `𝓡_0`, `𝓡_r` of (11.62) [lg:eq:corrector-linear-expansions] on the good set of
(11.44) [lg:eq:burnevent] with exponent `η` ((11.65) [lg:eq:corrector-remainder-bounds]):
`|P_g c − ½ h_θ² g⁻² W⁻¹ − Σ_k b_k F_k| ≤ K (W^{2η−3/2} g⁻² + W^{2η−1} g⁻⁴ + g^{−2R−6})` and
`|(P_g − I) F_r − Σ_k A_{kr} F_k| ≤ K (W^{2η−1} g⁻² + W⁻¹ g⁻² + g^{−2R−2})`. Each holds for every
finite index set containing one fixed finite set.
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### A weighted `ℓ¹` norm of polynomials -/

/-- The weight `∏_v ρ_v^{d_v}` of a monomial `d`. -/
private def crmWt (ρ : ObsVar → ℝ) (d : ObsVar →₀ ℕ) : ℝ := d.prod fun v n => ρ v ^ n

/-- The weighted `ℓ¹` norm `Σ_d |p_d| ρ^d` of a polynomial. -/
private def crmNorm (ρ : ObsVar → ℝ) (p : ObsPoly) : ℝ :=
  ∑ d ∈ p.support, ‖p.coeff d‖ * crmWt ρ d

private lemma crmWt_nonneg {ρ : ObsVar → ℝ} (hρ : ∀ v, 0 ≤ ρ v) (d : ObsVar →₀ ℕ) :
    0 ≤ crmWt ρ d :=
  Finset.prod_nonneg fun v _ => pow_nonneg (hρ v) _

private lemma crmWt_add (ρ : ObsVar → ℝ) (a b : ObsVar →₀ ℕ) :
    crmWt ρ (a + b) = crmWt ρ a * crmWt ρ b :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) fun _ _ _ => pow_add _ _ _

private lemma crmWt_zero (ρ : ObsVar → ℝ) : crmWt ρ 0 = 1 :=
  Finsupp.prod_zero_index

private lemma crmWt_single (ρ : ObsVar → ℝ) (v : ObsVar) :
    crmWt ρ (Finsupp.single v 1) = ρ v := by
  unfold crmWt
  rw [Finsupp.prod_single_index (by rw [pow_zero]), pow_one]

private lemma crmWt_const (B : ℝ) (d : ObsVar →₀ ℕ) :
    crmWt (fun _ => B) d = B ^ Finsupp.degree d := by
  unfold crmWt
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]

private lemma crmNorm_eq (ρ : ObsVar → ℝ) {p : ObsPoly} {T : Finset (ObsVar →₀ ℕ)}
    (hT : p.support ⊆ T) : crmNorm ρ p = ∑ d ∈ T, ‖p.coeff d‖ * crmWt ρ d := by
  unfold crmNorm
  refine Finset.sum_subset hT fun d _ hd => ?_
  rw [notMem_support_iff.mp hd, norm_zero, zero_mul]

private lemma crmNorm_nonneg {ρ : ObsVar → ℝ} (hρ : ∀ v, 0 ≤ ρ v) (p : ObsPoly) :
    0 ≤ crmNorm ρ p :=
  Finset.sum_nonneg fun d _ => mul_nonneg (norm_nonneg _) (crmWt_nonneg hρ d)

private lemma crmNorm_add_le {ρ : ObsVar → ℝ} (hρ : ∀ v, 0 ≤ ρ v) (p q : ObsPoly) :
    crmNorm ρ (p + q) ≤ crmNorm ρ p + crmNorm ρ q := by
  rw [crmNorm_eq ρ (support_add (p := p) (q := q)),
    crmNorm_eq ρ (Finset.subset_union_left (s₁ := p.support) (s₂ := q.support)),
    crmNorm_eq ρ (Finset.subset_union_right (s₁ := p.support) (s₂ := q.support)),
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun d _ => ?_
  rw [show (p + q).coeff d = p.coeff d + q.coeff d by simp, ← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (crmWt_nonneg hρ d)

private lemma crmNorm_neg (ρ : ObsVar → ℝ) (p : ObsPoly) : crmNorm ρ (-p) = crmNorm ρ p := by
  unfold crmNorm
  rw [support_neg]
  simp only [coeff_neg, norm_neg]

private lemma crmNorm_sub_le {ρ : ObsVar → ℝ} (hρ : ∀ v, 0 ≤ ρ v) (p q : ObsPoly) :
    crmNorm ρ (p - q) ≤ crmNorm ρ p + crmNorm ρ q := by
  rw [sub_eq_add_neg, ← crmNorm_neg ρ q]
  exact crmNorm_add_le hρ _ _

private lemma crmNorm_sum_le {ι : Type*} {ρ : ObsVar → ℝ} (hρ : ∀ v, 0 ≤ ρ v) (s : Finset ι)
    (f : ι → ObsPoly) : crmNorm ρ (∑ i ∈ s, f i) ≤ ∑ i ∈ s, crmNorm ρ (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [crmNorm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (crmNorm_add_le hρ _ _).trans (add_le_add le_rfl ih)

private lemma crmNorm_monomial (ρ : ObsVar → ℝ) (e : ObsVar →₀ ℕ) (c : ℂ) :
    crmNorm ρ (monomial e c) = ‖c‖ * crmWt ρ e := by
  rw [crmNorm_eq ρ support_monomial_subset, Finset.sum_singleton]
  simp [coeff_monomial]

private lemma crmNorm_C (ρ : ObsVar → ℝ) (c : ℂ) : crmNorm ρ (C c) = ‖c‖ := by
  rw [C_apply, crmNorm_monomial, crmWt_zero, mul_one]

private lemma crmNorm_X (ρ : ObsVar → ℝ) (v : ObsVar) : crmNorm ρ (X v) = ρ v := by
  rw [X, crmNorm_monomial, crmWt_single, norm_one, one_mul]

private lemma crmNorm_mul_le {ρ : ObsVar → ℝ} (hρ : ∀ v, 0 ≤ ρ v) (p q : ObsPoly) :
    crmNorm ρ (p * q) ≤ crmNorm ρ p * crmNorm ρ q := by
  have h : p * q = ∑ a ∈ p.support, ∑ b ∈ q.support,
      monomial (a + b) (p.coeff a * q.coeff b) := by
    conv_lhs => rw [p.as_sum, q.as_sum]
    rw [Finset.sum_mul_sum]
    simp only [monomial_mul_monomial]
  rw [h]
  refine (crmNorm_sum_le hρ _ _).trans ?_
  unfold crmNorm
  rw [Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun a _ => (crmNorm_sum_le hρ _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [crmNorm_monomial, norm_mul, crmWt_add]
  ring

private lemma crmNorm_one (ρ : ObsVar → ℝ) : crmNorm ρ 1 = 1 := by
  rw [← C_1, crmNorm_C, norm_one]

private lemma crmNorm_pow_le {ρ : ObsVar → ℝ} (hρ : ∀ v, 0 ≤ ρ v) (p : ObsPoly) (n : ℕ) :
    crmNorm ρ (p ^ n) ≤ crmNorm ρ p ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, crmNorm_one]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (crmNorm_mul_le hρ _ _).trans (mul_le_mul_of_nonneg_right ih (crmNorm_nonneg hρ p))

private lemma crmNorm_prod_le {ι : Type*} {ρ : ObsVar → ℝ} (hρ : ∀ v, 0 ≤ ρ v) (s : Finset ι)
    (f : ι → ObsPoly) : crmNorm ρ (∏ i ∈ s, f i) ≤ ∏ i ∈ s, crmNorm ρ (f i) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, crmNorm_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (crmNorm_mul_le hρ _ _).trans (mul_le_mul_of_nonneg_left ih (crmNorm_nonneg hρ _))

/-- Composition: `‖p(ψ)‖_ρ ≤ ‖p‖_{ρ'}` when `‖ψ_v‖_ρ ≤ ρ'_v` on the variables of `p`. -/
private lemma crmNorm_bind₁_le {ρ ρ' : ObsVar → ℝ} (hρ : ∀ v, 0 ≤ ρ v)
    (ψ : ObsVar → ObsPoly) (p : ObsPoly) (h : ∀ v ∈ p.vars, crmNorm ρ (ψ v) ≤ ρ' v) :
    crmNorm ρ (bind₁ ψ p) ≤ crmNorm ρ' p := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine (crmNorm_sum_le hρ _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  rw [bind₁_monomial]
  refine (crmNorm_mul_le hρ _ _).trans ?_
  rw [crmNorm_C]
  refine mul_le_mul_of_nonneg_left ((crmNorm_prod_le hρ _ _).trans ?_) (norm_nonneg _)
  refine Finset.prod_le_prod₀ (fun v _ => crmNorm_nonneg hρ _) fun v hv => ?_
  have hvar : v ∈ p.vars := (mem_vars_iff_mem_support v).2 ⟨d, hd, hv⟩
  exact (crmNorm_pow_le hρ _ _).trans (pow_le_pow_left₀ (crmNorm_nonneg hρ _) (h v hvar) _)

/-- Coefficientwise domination. -/
private lemma crmNorm_mono {ρ : ObsVar → ℝ} (hρ : ∀ v, 0 ≤ ρ v) {p q : ObsPoly}
    (h : ∀ d, ‖q.coeff d‖ ≤ ‖p.coeff d‖) : crmNorm ρ q ≤ crmNorm ρ p := by
  have hs : q.support ⊆ p.support := fun d hd => by
    rw [mem_support_iff] at hd ⊢
    intro h0
    have := h d
    rw [h0, norm_zero] at this
    exact hd (norm_le_zero_iff.mp this)
  rw [crmNorm_eq ρ hs]
  exact Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_right (h d) (crmWt_nonneg hρ d)

/-- A bound from a support and a coefficient bound. -/
private lemma crmNorm_le_of_support {ρ : ObsVar → ℝ} (hρ : ∀ v, 0 ≤ ρ v) {p : ObsPoly}
    {S : Finset (ObsVar →₀ ℕ)} {K : ℝ} (hS : p.support ⊆ S) (hK : ∀ d, ‖p.coeff d‖ ≤ K) :
    crmNorm ρ p ≤ ∑ d ∈ S, K * crmWt ρ d := by
  rw [crmNorm_eq ρ hS]
  exact Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_right (hK d) (crmWt_nonneg hρ d)

/-- Multiplication by a variable multiplies the norm by its weight. -/
private lemma crmNorm_X_mul (ρ : ObsVar → ℝ) (v : ObsVar) (p : ObsPoly) :
    crmNorm ρ (X v * p) = ρ v * crmNorm ρ p := by
  unfold crmNorm
  rw [support_X_mul, Finset.sum_map, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [addLeftEmbedding_apply, coeff_X_mul, crmWt_add, crmWt_single]
  ring

private lemma crm_vars_X_mul (v : ObsVar) (p : ObsPoly) : p.vars ⊆ (X v * p).vars := by
  intro u hu
  obtain ⟨d, hd, hud⟩ := (mem_vars_iff_mem_support u).1 hu
  refine (mem_vars_iff_mem_support u).2 ⟨Finsupp.single v 1 + d, ?_, ?_⟩
  · rw [support_X_mul]
    exact Finset.mem_map_of_mem _ hd
  · rw [Finsupp.mem_support_iff] at hud ⊢
    rw [Finsupp.add_apply]
    omega

/-- `Σ_d |p_d| |d| B^{|d|−1} ≤ ‖p‖_{2B}`. -/
private lemma crm_lip_le {B : ℝ} (hB : 1 ≤ B) (p : ObsPoly) :
    ∑ d ∈ p.support, ‖p.coeff d‖ * Finsupp.degree d * B ^ (Finsupp.degree d - 1) ≤
      crmNorm (fun _ => 2 * B) p := by
  unfold crmNorm
  refine Finset.sum_le_sum fun d _ => ?_
  rw [crmWt_const, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  set n := Finsupp.degree d
  have h1 : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
  have h2 : B ^ (n - 1) ≤ B ^ n := pow_le_pow_right₀ hB (Nat.sub_le n 1)
  rw [mul_pow]
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-! ### Truncation in `γ` and divisibility by `γ` -/

private lemma crm_coeff_truncG (N : ℕ) (p : ObsPoly) (d : ObsVar →₀ ℕ) :
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

private lemma crm_support_truncG (N : ℕ) (p : ObsPoly) : (truncG N p).support ⊆ p.support := by
  intro d hd
  rw [mem_support_iff, crm_coeff_truncG] at hd
  rw [mem_support_iff]
  split_ifs at hd
  · exact hd
  · exact absurd rfl hd

private lemma crm_coeff_sub_truncG (N : ℕ) (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (p - truncG N p).coeff d = if d .γ ≤ N then 0 else p.coeff d := by
  rw [coeff_sub, crm_coeff_truncG]
  split_ifs <;> simp

private lemma crm_support_sub_truncG (N : ℕ) (p : ObsPoly) :
    (p - truncG N p).support ⊆ p.support ∧ ∀ d ∈ (p - truncG N p).support, N + 1 ≤ d .γ := by
  refine ⟨fun d hd => ?_, fun d hd => ?_⟩ <;>
  · rw [mem_support_iff, crm_coeff_sub_truncG] at hd
    split_ifs at hd with h
    · exact absurd rfl hd
    · first
        | exact mem_support_iff.mpr hd
        | omega

private lemma crm_dvd_iff (n : ℕ) (p : ObsPoly) :
    X .γ ^ n ∣ p ↔ ∀ d ∈ p.support, n ≤ d .γ := by
  have h : ({X .γ ^ n} : Set ObsPoly) =
      (fun s => monomial s (1 : ℂ)) '' {Finsupp.single ObsVar.γ n} := by
    rw [Set.image_singleton, X_pow_eq_monomial]
  rw [← Ideal.mem_span_singleton, h, mem_ideal_span_monomial_image]
  simp [Finsupp.single_le_iff]

private lemma crm_dvd_truncG {n N : ℕ} {p : ObsPoly} (h : X .γ ^ n ∣ p) :
    X .γ ^ n ∣ truncG N p := by
  rw [crm_dvd_iff] at h ⊢
  exact fun d hd => h d (crm_support_truncG N p hd)

private lemma crm_dvd_sub_truncG (N : ℕ) (p : ObsPoly) : X .γ ^ (N + 1) ∣ p - truncG N p :=
  (crm_dvd_iff _ _).2 (crm_support_sub_truncG N p).2

private lemma crm_truncG_X {N : ℕ} {v : ObsVar} (h : v.gamWt ≤ N) : truncG N (X v) = X v := by
  ext d
  rw [crm_coeff_truncG]
  split_ifs with hd
  · rfl
  · rw [coeff_X]
    split_ifs with h2
    · exfalso
      subst h2
      cases v <;> simp_all [ObsVar.gamWt]
    · rfl

/-- `ψ ≡ X` modulo `γ` on every variable gives `p(ψ) ≡ p` modulo `γ`. -/
private lemma crm_bind₁_sub {ψ : ObsVar → ObsPoly} (hψ : ∀ v, X .γ ∣ ψ v - X v) (p : ObsPoly) :
    X .γ ∣ bind₁ ψ p - p := by
  set I : Ideal ObsPoly := Ideal.span {X .γ}
  have h : (Ideal.Quotient.mkₐ ℂ I).comp (bind₁ ψ) = Ideal.Quotient.mkₐ ℂ I := by
    refine MvPolynomial.algHom_ext fun v => ?_
    rw [AlgHom.comp_apply, bind₁_X_right, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact Ideal.mem_span_singleton.mpr (hψ v)
  have h' := DFunLike.congr_fun h p
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at h'
  exact Ideal.mem_span_singleton.mp h'

private lemma crm_revCoord_sub {N : ℕ} (hN : 1 ≤ N) {σ : ObsVar → ObsPoly}
    (hσ : ∀ v, X ObsVar.γ ∣ σ v - X v) (r : ℕ) :
    ∀ v, X ObsVar.γ ∣ revCoord N σ r v - X v := by
  induction r with
  | zero =>
    intro v
    rw [show revCoord N σ 0 v = X v from rfl, sub_self]
    exact dvd_zero _
  | succ r ih =>
    intro v
    have hγ : X ObsVar.γ ∣ revCoord N σ r ObsVar.γ := by
      have e : revCoord N σ r ObsVar.γ =
          (revCoord N σ r ObsVar.γ - X ObsVar.γ) + X ObsVar.γ := by ring
      rw [e]
      exact dvd_add (ih ObsVar.γ) dvd_rfl
    have hb : X ObsVar.γ ∣ bind₁ (revCoord N σ r) (σ v - X v) := by
      obtain ⟨q, hq⟩ := hσ v
      rw [hq, map_mul, bind₁_X_right]
      exact dvd_mul_of_dvd_left hγ _
    have e : revCoord N σ (r + 1) v = truncG N (X v - bind₁ (revCoord N σ r) (σ v - X v)) := rfl
    rw [e, map_sub, crm_truncG_X (by cases v <;> simp [ObsVar.gamWt]; omega),
      sub_sub_cancel_left]
    have h := crm_dvd_truncG (n := 1) (N := N) (p := bind₁ (revCoord N σ r) (σ v - X v))
      (by rw [pow_one]; exact hb)
    rw [pow_one] at h
    exact dvd_neg.mpr h

private lemma crm_corrCoord_sub (E : ℝ) (R : ℕ) (v : ObsVar) : X .γ ∣ corrCoord E R v - X v := by
  cases v with
  | m k =>
    have h := crm_dvd_sub_truncG 0 (corrObsM E R k)
    rw [(corrObs_form E R k).1, zero_add, pow_one] at h
    exact h
  | f k =>
    have h := crm_dvd_sub_truncG 0 (corrObsF E R k)
    rw [(corrObs_form E R k).2.2.2.1, zero_add, pow_one] at h
    exact h
  | w => exact ⟨0, by rw [mul_zero]; exact sub_eq_zero.mpr rfl⟩
  | γ => exact ⟨0, by rw [mul_zero]; exact sub_eq_zero.mpr rfl⟩

private lemma crm_invCoord_sub (E : ℝ) (R : ℕ) (v : ObsVar) : X .γ ∣ invCoord E R v - X v :=
  crm_revCoord_sub (by omega) (crm_corrCoord_sub E R) (R + 2) v

private lemma crm_invCoord_γ (E : ℝ) (R : ℕ) : invCoord E R .γ = X .γ := by
  rw [invCoord, revCoord]
  beta_reduce
  rw [show corrCoord E R .γ = X .γ from rfl, sub_self, map_zero, sub_zero]
  exact crm_truncG_X (by simp [ObsVar.gamWt])

private lemma crm_invCoord_w (E : ℝ) (R : ℕ) : invCoord E R .w = X .w := by
  rw [invCoord, revCoord]
  beta_reduce
  rw [show corrCoord E R .w = X .w from rfl, sub_self, map_zero, sub_zero]
  exact crm_truncG_X (by simp [ObsVar.gamWt])

/-- The term `h_θ² γ c_1` of the expansion. -/
private def crmZ (E : ℝ) : ObsPoly := C (((normalH E ^ (2 * 1) : ℝ) : ℂ)) * X .γ ^ 1 * incWick 1

private lemma crm_bind_incPoly_sub (E : ℝ) (R : ℕ) :
    X .γ ^ 2 ∣ bind₁ (invCoord E R) (incPoly E R) - crmZ E := by
  have hterm : ∀ (c : ℂ) (r : ℕ), bind₁ (invCoord E R) (C c * X .γ ^ r * incWick r) =
      C c * X .γ ^ r * bind₁ (invCoord E R) (incWick r) := by
    intro c r
    rw [map_mul, map_mul, map_pow, bind₁_C_right, bind₁_X_right, crm_invCoord_γ]
  unfold incPoly
  rw [map_sum, show R + 3 = R + 1 + 1 + 1 from rfl, Finset.sum_range_succ',
    Finset.sum_range_succ']
  simp only [hterm, (wickMap_zero_incWick_zero 0).2, map_zero, mul_zero, add_zero, zero_add]
  have e : ∑ i ∈ Finset.range (R + 1), C (((normalH E ^ (2 * (i + 1 + 1)) : ℝ) : ℂ)) *
        X .γ ^ (i + 1 + 1) * bind₁ (invCoord E R) (incWick (i + 1 + 1)) +
      C (((normalH E ^ (2 * 1) : ℝ) : ℂ)) * X .γ ^ 1 * bind₁ (invCoord E R) (incWick 1) -
      crmZ E = ∑ i ∈ Finset.range (R + 1), C (((normalH E ^ (2 * (i + 1 + 1)) : ℝ) : ℂ)) *
        X .γ ^ (i + 1 + 1) * bind₁ (invCoord E R) (incWick (i + 1 + 1)) +
      C (((normalH E ^ (2 * 1) : ℝ) : ℂ)) * X .γ ^ 1 *
        (bind₁ (invCoord E R) (incWick 1) - incWick 1) := by
    unfold crmZ
    ring
  rw [e]
  refine dvd_add (Finset.dvd_sum fun i _ => ?_) ?_
  · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow _ (by omega)) _) _
  · obtain ⟨q, hq⟩ := crm_bind₁_sub (crm_invCoord_sub E R) (incWick 1)
    rw [hq]
    exact ⟨C (((normalH E ^ (2 * 1) : ℝ) : ℂ)) * q, by ring⟩

private lemma crm_incCorr_sub (E : ℝ) (R : ℕ) : X .γ ^ 2 ∣ incCorr E R - crmZ E := by
  have e : incCorr E R - crmZ E = truncG (R + 2) (bind₁ (invCoord E R) (incPoly E R) - crmZ E) -
      (crmZ E - truncG (R + 2) (crmZ E)) := by
    unfold incCorr
    rw [map_sub]
    ring
  rw [e]
  exact dvd_sub (crm_dvd_truncG (crm_bind_incPoly_sub E R))
    ((pow_dvd_pow _ (by omega)).trans (crm_dvd_sub_truncG (R + 2) (crmZ E)))

/-! ### The ideal `(f_k)` -/

/-- `fIdeal` is the monomial ideal of the variables `f_k`. -/
private lemma crm_mem_fIdeal_iff (p : ObsPoly) :
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

/-- An algebra map fixing every `f_k` maps `fIdeal` into itself. -/
private lemma crm_map_mem_fIdeal (φ : ObsPoly →ₐ[ℂ] ObsPoly)
    (hφ : ∀ k : NzInt, φ (X (.f k)) = X (.f k))
    {p : ObsPoly} (hp : p ∈ fIdeal) : φ p ∈ fIdeal := by
  have hle : Ideal.map φ fIdeal ≤ fIdeal := by
    change Ideal.map φ (Ideal.span _) ≤ fIdeal
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    rw [hφ k]
    exact Ideal.subset_span ⟨k, rfl⟩
  exact hle (Ideal.mem_map_of_mem _ hp)

private lemma crm_coeff_zero_of_mem {p : ObsPoly} (hp : p ∈ fIdeal) : p.coeff 0 = 0 := by
  by_contra h
  obtain ⟨k, hk⟩ := (crm_mem_fIdeal_iff p).1 hp 0 (mem_support_iff.mpr h)
  exact hk rfl

private lemma crm_mem_fIdeal_of_γ_mul {p : ObsPoly} (hp : X .γ * p ∈ fIdeal) : p ∈ fIdeal := by
  rw [crm_mem_fIdeal_iff] at hp ⊢
  intro d hd
  obtain ⟨k, hk⟩ := hp (Finsupp.single .γ 1 + d) (by
    rw [support_X_mul]
    exact Finset.mem_map_of_mem _ hd)
  refine ⟨k, ?_⟩
  simpa using hk

private lemma crm_zeroW_X (v : ObsVar) : zeroW (X v) = if v = .w then 0 else X v := by
  simp [zeroW]

private lemma crm_zeroW_mem {p : ObsPoly} (hp : p ∈ fIdeal) : zeroW p ∈ fIdeal :=
  crm_map_mem_fIdeal zeroW (fun k => by rw [crm_zeroW_X]; simp) hp

private lemma crm_zeroW_monomial (d : ObsVar →₀ ℕ) (c : ℂ) :
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

private lemma crm_coeff_zeroW (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (zeroW p).coeff d = if d .w = 0 then p.coeff d else 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial e c =>
    rw [crm_zeroW_monomial]
    by_cases he : e = d
    · subst he
      split_ifs <;> simp [coeff_monomial]
    · split_ifs <;> simp [coeff_monomial, he]
  | add p q hp hq =>
    rw [map_add, show ∀ a b : ObsPoly, (a + b).coeff d = a.coeff d + b.coeff d from
      fun a b => by simp, hp, hq]
    split_ifs <;> simp

private lemma crm_support_zeroW (p : ObsPoly) : (zeroW p).support ⊆ p.support := by
  intro d hd
  rw [mem_support_iff, crm_coeff_zeroW] at hd
  rw [mem_support_iff]
  split_ifs at hd
  · exact hd
  · exact absurd rfl hd

/-- Evaluation at a point with `w = 0` does not see the `w`-terms. -/
private lemma crm_aeval_zeroW {x : ObsVar → ℂ} (hx : x .w = 0) (p : ObsPoly) :
    aeval x (zeroW p) = aeval x p := by
  unfold zeroW
  rw [comp_aeval_apply]
  have h : (fun v : ObsVar => (aeval x (if v = ObsVar.w then (0 : ObsPoly) else X v) : ℂ)) =
      x := by
    funext v
    by_cases hv : v = .w
    · subst hv
      simp [hx]
    · simp [hv]
  exact congrArg (fun φ : ObsVar → ℂ => aeval φ p) h

private lemma crm_centerSub_zeroW (g : ℝ) (a : ℤ → ℂ) (p : ObsPoly) :
    centerSub g a (zeroW p) = centerSub g a p := by
  have h : (centerSub g a).comp zeroW = centerSub g a := by
    refine MvPolynomial.algHom_ext fun v => ?_
    rw [AlgHom.comp_apply, crm_zeroW_X]
    by_cases hv : v = .w
    · subst hv
      simp [centerSub]
    · simp [hv]
  exact DFunLike.congr_fun h p

/-! ### The substitution `M = a`, `w = 0` -/

/-- The point `m_j ↦ a_j`, `f_j ↦ y_{f_j}`, `w ↦ 0`, `γ ↦ y_γ`. -/
private def crmPt (a : ℤ → ℂ) (y : ObsVar → ℂ) : ObsVar → ℂ
  | .m j => a j.1
  | .f j => y (.f j)
  | .w => 0
  | .γ => y .γ

private lemma crm_aeval_centerSub {g : ℝ} {a : ℤ → ℂ} {y : ObsVar → ℂ}
    (hγ : y .γ = (((g ^ 2)⁻¹ : ℝ) : ℂ)) (p : ObsPoly) :
    aeval y (centerSub g a p) = aeval (crmPt a y) p := by
  unfold centerSub
  rw [comp_aeval_apply]
  have h : (fun v => aeval y (match v with
      | .m k => C (a k.1)
      | .f k => X (.f k)
      | .w => 0
      | .γ => C (((g ^ 2)⁻¹ : ℝ) : ℂ))) = crmPt a y := by
    funext v
    cases v <;> simp [crmPt, hγ]
  exact congrArg (fun φ : ObsVar → ℂ => aeval φ p) h

private lemma crm_linCoeff_add (g : ℝ) (a : ℤ → ℂ) (k : NzInt) (p q : ObsPoly) :
    linCoeff g a k (p + q) = linCoeff g a k p + linCoeff g a k q := by
  unfold linCoeff
  rw [map_add]
  simp

private lemma crm_linCoeff_γ_mul (g : ℝ) (a : ℤ → ℂ) (k : NzInt) (p : ObsPoly) :
    linCoeff g a k (X .γ * p) = (((g ^ 2)⁻¹ : ℝ) : ℂ) * linCoeff g a k p := by
  unfold linCoeff
  rw [map_mul, show centerSub g a (X .γ) = C (((g ^ 2)⁻¹ : ℝ) : ℂ) by simp [centerSub],
    coeff_C_mul]

private lemma crm_linCoeff_C_X (g : ℝ) (a : ℤ → ℂ) (k r : NzInt) (c : ℂ) :
    linCoeff g a k (C c * X (.f r)) = if k = r then c else 0 := by
  unfold linCoeff
  rw [map_mul, show centerSub g a (C c) = C c by simp [centerSub],
    show centerSub g a (X (.f r)) = X (.f r) by simp [centerSub], coeff_C_mul, coeff_X]
  by_cases h : k = r
  · subst h
    simp
  · have h' : Finsupp.single (ObsVar.f r) 1 ≠ Finsupp.single (ObsVar.f k) 1 := fun h' => by
      have := (Finsupp.single_left_inj one_ne_zero).mp h'
      exact h (by simpa using this.symm)
    simp [h, h']

/-- The product formula `y^d = y_v · y^{d − e_v}` for `d_v ≠ 0`. -/
private lemma crm_prod_split (x : ObsVar → ℂ) {d : ObsVar →₀ ℕ} {v : ObsVar} (hv : d v ≠ 0) :
    (d.prod fun u n => x u ^ n) =
      x v * ((d - Finsupp.single v 1).prod fun u n => x u ^ n) := by
  have hle : Finsupp.single v 1 ≤ d := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hv)
  conv_lhs => rw [← add_tsub_cancel_of_le hle]
  rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  congr 1
  simp [Finsupp.prod_single_index]

/-- The variation in the `m_j` of a polynomial in `(f_k)`: `|J(y) − J(z)| ≤ ‖J‖_{2B} δ_M δ_F`. -/
private lemma crm_var_m {J : ObsPoly} (hJ : J ∈ fIdeal) {y z : ObsVar → ℂ} {B δM δF : ℝ}
    (hB : 1 ≤ B) (hδM : 0 ≤ δM) (hδF : 0 ≤ δF)
    (hyz : ∀ v ∈ J.vars, ‖y v‖ ≤ B ∧ ‖z v‖ ≤ B ∧ ‖y v - z v‖ ≤ δM)
    (hf : ∀ k : NzInt, ObsVar.f k ∈ J.vars → z (.f k) = y (.f k) ∧ ‖y (.f k)‖ ≤ δF) :
    ‖aeval y J - aeval z J‖ ≤ crmNorm (fun _ => 2 * B) J * (δM * δF) := by
  conv_lhs => rw [J.as_sum]
  rw [map_sum, map_sum, ← Finset.sum_sub_distrib]
  unfold crmNorm
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  obtain ⟨k, hk⟩ := (crm_mem_fIdeal_iff J).1 hJ d hd
  have hkv : ObsVar.f k ∈ J.vars :=
    (mem_vars_iff_mem_support _).2 ⟨d, hd, Finsupp.mem_support_iff.mpr hk⟩
  obtain ⟨hzk, hyk⟩ := hf k hkv
  set d' := d - Finsupp.single (ObsVar.f k) 1 with hd'
  have hle : Finsupp.single (ObsVar.f k) 1 ≤ d :=
    Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hk)
  have hdeg : Finsupp.degree d = Finsupp.degree d' + 1 := by
    conv_lhs => rw [← tsub_add_cancel_of_le hle]
    rw [map_add, Finsupp.degree_single]
  have hsub : d'.support ⊆ d.support := fun v hv => by
    rw [Finsupp.mem_support_iff] at hv ⊢
    rw [hd', Finsupp.tsub_apply] at hv
    omega
  have hmono : ∀ x : ObsVar → ℂ, aeval x (monomial d' (1 : ℂ)) = d'.prod fun u n => x u ^ n := by
    intro x
    rw [aeval_monomial, map_one, one_mul]
  rw [aeval_monomial, aeval_monomial, crm_prod_split y hk, crm_prod_split z hk, hzk,
    ← hmono y, ← hmono z, ← mul_sub, ← mul_sub, norm_mul, norm_mul, Algebra.algebraMap_self,
    RingHom.id_apply, crmWt_const]
  have hvars : (monomial d' (1 : ℂ)).vars = d'.support := vars_monomial one_ne_zero
  have hL := norm_aeval_sub_aeval_le (monomial d' (1 : ℂ)) (x := y) (y := z) (B := B) (δ := δM)
    (by linarith)
    (fun v hv => (hyz v ((mem_vars_iff_mem_support v).2 ⟨d, hd, hsub (hvars ▸ hv)⟩)).1)
    (fun v hv => (hyz v ((mem_vars_iff_mem_support v).2 ⟨d, hd, hsub (hvars ▸ hv)⟩)).2.1)
    (fun v hv => (hyz v ((mem_vars_iff_mem_support v).2 ⟨d, hd, hsub (hvars ▸ hv)⟩)).2.2)
  simp only [support_monomial, one_ne_zero, ↓reduceIte, Finset.sum_singleton, coeff_monomial,
    norm_one, one_mul] at hL
  have hn : ((Finsupp.degree d' : ℕ) : ℝ) * B ^ (Finsupp.degree d' - 1) ≤
      (2 * B) ^ Finsupp.degree d := by
    rw [mul_pow]
    have h1 : ((Finsupp.degree d' : ℕ) : ℝ) ≤ 2 ^ Finsupp.degree d := by
      have := (Nat.lt_two_pow_self (n := Finsupp.degree d')).le
      have h2 : 2 ^ Finsupp.degree d' ≤ 2 ^ Finsupp.degree d :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      exact_mod_cast this.trans h2
    have h2 : B ^ (Finsupp.degree d' - 1) ≤ B ^ Finsupp.degree d :=
      pow_le_pow_right₀ hB (by omega)
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  calc ‖J.coeff d‖ * (‖y (.f k)‖ * ‖aeval y (monomial d' (1 : ℂ)) - aeval z (monomial d' 1)‖)
      ≤ ‖J.coeff d‖ * (δF * (((Finsupp.degree d' : ℕ) : ℝ) * B ^ (Finsupp.degree d' - 1) * δM)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hyk hL (norm_nonneg _) hδF) (norm_nonneg _)
    _ ≤ ‖J.coeff d‖ * (δF * ((2 * B) ^ Finsupp.degree d * δM)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hn hδM) hδF) (norm_nonneg _)
    _ = ‖J.coeff d‖ * (2 * B) ^ Finsupp.degree d * (δM * δF) := by ring

/-- The terms of degree at least `2` in the `f_k`: for `Q` in the `f_k` only, with no constant
term, `|Q(y) − Σ_k [f_k]Q · y_{f_k}| ≤ Σ_d |Q_d| δ_F²`. -/
private lemma crm_quad {Q : ObsPoly} {T : Finset NzInt} {y : ObsVar → ℂ} {δF : ℝ}
    (hδF0 : 0 ≤ δF) (hδF : δF ≤ 1) (h0 : Q.coeff 0 = 0)
    (hvars : ∀ v ∈ Q.vars, ∃ k ∈ T, v = ObsVar.f k) (hf : ∀ k ∈ T, ‖y (.f k)‖ ≤ δF) :
    ‖aeval y Q - ∑ k ∈ T, Q.coeff (Finsupp.single (.f k) 1) * y (.f k)‖ ≤
      (∑ d ∈ Q.support, ‖Q.coeff d‖) * δF ^ 2 := by
  set Q₁ : ObsPoly := ∑ k ∈ T, C (Q.coeff (Finsupp.single (.f k) 1)) * X (.f k) with hQ₁
  have h1 : aeval y Q₁ = ∑ k ∈ T, Q.coeff (Finsupp.single (.f k) 1) * y (.f k) := by
    simp [hQ₁]
  rw [← h1, ← map_sub]
  set Q₂ := Q - Q₁ with hQ₂
  have hinj : ∀ j k : NzInt, Finsupp.single (ObsVar.f j) 1 = Finsupp.single (ObsVar.f k) 1 →
      j = k := fun j k h => by
    have := (Finsupp.single_left_inj one_ne_zero).mp h
    simpa using this
  have hc : ∀ d, Q₂.coeff d =
      if ∃ k ∈ T, d = Finsupp.single (.f k) 1 then 0 else Q.coeff d := by
    intro d
    rw [hQ₂, coeff_sub, hQ₁, coeff_sum]
    simp only [coeff_C_mul, coeff_X]
    split_ifs with h
    · obtain ⟨k, hk, rfl⟩ := h
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hjk
        simp only [show ¬(Finsupp.single (ObsVar.f j) 1 = Finsupp.single (ObsVar.f k) 1) from
          fun h => hjk (hinj j k h), ↓reduceIte, mul_zero]
      · intro hk'
        exact absurd hk hk'
    · rw [Finset.sum_eq_zero, sub_zero]
      intro j hj
      simp only [show ¬(Finsupp.single (ObsVar.f j) 1 = d) from fun h' => h ⟨j, hj, h'.symm⟩,
        ↓reduceIte, mul_zero]
  have hsupp : Q₂.support ⊆ Q.support := fun d hd => by
    rw [mem_support_iff, hc] at hd
    split_ifs at hd
    · exact absurd rfl hd
    · exact mem_support_iff.mpr hd
  have hvarQ : ∀ v ∈ Q₂.vars, ∃ k ∈ T, v = ObsVar.f k := fun v hv => by
    obtain ⟨d, hd, hvd⟩ := (mem_vars_iff_mem_support v).1 hv
    exact hvars v ((mem_vars_iff_mem_support v).2 ⟨d, hsupp hd, hvd⟩)
  have hdeg : ∀ d ∈ Q₂.support, 2 ≤ Finsupp.degree d := by
    intro d hd
    have hd' := hd
    rw [mem_support_iff, hc] at hd'
    split_ifs at hd' with hT
    · exact absurd rfl hd'
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hd' h0
    obtain ⟨v, hv⟩ := Finsupp.support_nonempty_iff.mpr hd0
    obtain ⟨k, hk, rfl⟩ := hvarQ v ((mem_vars_iff_mem_support v).2 ⟨d, hd, hv⟩)
    have hle : Finsupp.single (ObsVar.f k) 1 ≤ d :=
      Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv))
    have he : Finsupp.degree d = Finsupp.degree (d - Finsupp.single (ObsVar.f k) 1) + 1 := by
      conv_lhs => rw [← tsub_add_cancel_of_le hle]
      rw [map_add, Finsupp.degree_single]
    have hne : d - Finsupp.single (ObsVar.f k) 1 ≠ 0 := by
      intro h
      apply hT
      refine ⟨k, hk, ?_⟩
      rw [← tsub_add_cancel_of_le hle, h, zero_add]
    have := (Finsupp.degree_eq_zero_iff _).not.mpr hne
    omega
  refine (norm_aeval_le_sum_coeff Q₂ hδF0 fun v hv => ?_).trans ?_
  · obtain ⟨k, hk, rfl⟩ := hvarQ v hv
    exact hf k hk
  · rw [Finset.sum_mul]
    refine (Finset.sum_le_sum fun d hd => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg hsupp fun d _ _ => by positivity)
    have hQd : ‖Q₂.coeff d‖ ≤ ‖Q.coeff d‖ := by
      rw [hc]
      split_ifs
      · rw [norm_zero]; exact norm_nonneg _
      · exact le_rfl
    exact mul_le_mul hQd (pow_le_pow_of_le_one hδF0 hδF (hdeg d hd)) (by positivity)
      (norm_nonneg _)

/-- The basic estimate: for `H` whose `W⁰` part lies in `(f_k)`, at a point `y` with
`|y_{m_j} − a_j| ≤ δ_M`, `|y_{f_k}| ≤ δ_F`, `|y_w| ≤ ω`, `y_γ = g⁻²`,
`|H(y) − Σ_{k ∈ T} [F_k] H|_{M=a} · y_{f_k}| ≤ ‖H‖_{2B} (ω + δ_M δ_F + δ_F²)`. -/
private lemma crm_core {H : ObsPoly} (hH : zeroW H ∈ fIdeal) {g : ℝ} (hg : 1 ≤ g) {a : ℤ → ℂ}
    {y : ObsVar → ℂ} {T : Finset NzInt} {B δM δF ω : ℝ} (hB : 1 ≤ B) (hδM : 0 ≤ δM)
    (hδF0 : 0 ≤ δF) (hδF : δF ≤ 1) (hω : ω ≤ 1)
    (hT : ∀ k : NzInt, ObsVar.f k ∈ H.vars → k ∈ T)
    (hm : ∀ j : NzInt, ObsVar.m j ∈ H.vars →
      ‖y (.m j)‖ ≤ B ∧ ‖a j.1‖ ≤ B ∧ ‖y (.m j) - a j.1‖ ≤ δM)
    (hf : ∀ k ∈ T, ‖y (.f k)‖ ≤ δF) (hw : ‖y .w‖ ≤ ω) (hγ : y .γ = (((g ^ 2)⁻¹ : ℝ) : ℂ)) :
    ‖aeval y H - ∑ k ∈ T, linCoeff g a k H * y (.f k)‖ ≤
      crmNorm (fun _ => 2 * B) H * (ω + δM * δF + δF ^ 2) := by
  have hB0 : 0 ≤ B := by linarith
  have h2B : ∀ _ : ObsVar, (0 : ℝ) ≤ 2 * B := fun _ => by linarith
  have hω0 : 0 ≤ ω := (norm_nonneg _).trans hw
  have ht : ‖y .γ‖ ≤ 1 := by
    rw [hγ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (by nlinarith)
  set N := crmNorm (fun _ => 2 * B) H with hN
  have hN0 : 0 ≤ N := crmNorm_nonneg h2B H
  set y' : ObsVar → ℂ := fun v => if v = .w then 0 else y v with hy'
  set z : ObsVar → ℂ := crmPt a y with hz
  have hyB : ∀ v ∈ H.vars, ‖y v‖ ≤ B := by
    intro v hv
    cases v with
    | m j => exact (hm j hv).1
    | f k => exact (hf k (hT k hv)).trans (hδF.trans hB)
    | w => exact hw.trans (hω.trans hB)
    | γ => exact ht.trans hB
  -- the `w`-terms
  have hA1 : ‖aeval y H - aeval y' H‖ ≤ N * ω := by
    have h := norm_aeval_sub_aeval_le H (x := y) (y := y') hB0 hyB (fun v hv => by
        by_cases h : v = .w
        · simp [hy', h, hB0]
        · simpa [hy', h] using hyB v hv)
      (fun v _ => by
        by_cases h : v = .w
        · subst h
          simpa [hy'] using hw
        · simp [hy', h, hω0])
    exact h.trans (mul_le_mul_of_nonneg_right (crm_lip_le hB H) hω0)
  -- the variation in the `m_j`
  have hA2 : ‖aeval y' H - aeval z H‖ ≤ N * (δM * δF) := by
    rw [← crm_aeval_zeroW (x := y') (by simp [hy']) H,
      ← crm_aeval_zeroW (x := z) (by simp [hz, crmPt]) H]
    have hvz : (zeroW H).vars ⊆ H.vars := fun v hv => by
      obtain ⟨d, hd, hvd⟩ := (mem_vars_iff_mem_support v).1 hv
      exact (mem_vars_iff_mem_support v).2 ⟨d, crm_support_zeroW H hd, hvd⟩
    refine (crm_var_m hH hB hδM hδF0 (fun v hv => ?_) (fun k hk => ?_)).trans
      (mul_le_mul_of_nonneg_right (crmNorm_mono h2B fun d => ?_) (by positivity))
    · have hv' := hvz hv
      cases v with
      | m j =>
        obtain ⟨h1, h2, h3⟩ := hm j hv'
        exact ⟨by simpa [hy'] using h1, by simpa [hz, crmPt] using h2,
          by simpa [hy', hz, crmPt] using h3⟩
      | f k =>
        have h1 := hyB _ hv'
        exact ⟨by simpa [hy'] using h1, by simpa [hz, crmPt] using h1,
          by simp [hy', hz, crmPt, hδM]⟩
      | w => simp [hy', hz, crmPt, hB0, hδM]
      | γ => exact ⟨by simpa [hy'] using ht.trans hB, by simpa [hz, crmPt] using ht.trans hB,
          by simp [hy', hz, crmPt, hδM]⟩
    · exact ⟨by simp [hy', hz, crmPt], by simpa [hy'] using hf k (hT k (hvz hk))⟩
    · rw [crm_coeff_zeroW]
      split_ifs
      · exact le_rfl
      · rw [norm_zero]; exact norm_nonneg _
  -- the terms of degree at least `2` in the `f_k`
  have hB' : ‖aeval z H - ∑ k ∈ T, linCoeff g a k H * y (.f k)‖ ≤ N * δF ^ 2 := by
    set Q := centerSub g a H with hQ
    have hzQ : aeval z H = aeval y Q := (crm_aeval_centerSub hγ H).symm
    have hlin : ∀ k, linCoeff g a k H = Q.coeff (Finsupp.single (.f k) 1) := fun k => rfl
    rw [hzQ]
    simp only [hlin]
    have h0 : Q.coeff 0 = 0 := by
      rw [hQ, ← crm_centerSub_zeroW]
      exact crm_coeff_zero_of_mem (crm_map_mem_fIdeal _ (fun k => by simp [centerSub]) hH)
    have hvars : ∀ v ∈ Q.vars, ∃ k ∈ T, v = ObsVar.f k := by
      intro v hv
      rw [hQ, centerSub, aeval_eq_bind₁] at hv
      obtain ⟨u, hu, hvu⟩ := Finset.mem_biUnion.mp (vars_bind₁ _ H hv)
      cases u with
      | m j => simp at hvu
      | f j =>
        have : v = .f j := by simpa using hvu
        exact ⟨j, hT j hu, this⟩
      | w => simp at hvu
      | γ => simp at hvu
    refine (crm_quad hδF0 hδF h0 hvars hf).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have h1 : ∑ d ∈ Q.support, ‖Q.coeff d‖ = crmNorm (fun _ => 1) Q := by
      unfold crmNorm
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [crmWt_const, one_pow, mul_one]
    rw [h1, hQ, centerSub, aeval_eq_bind₁]
    refine crmNorm_bind₁_le (fun _ => zero_le_one) _ H fun v hv => ?_
    cases v with
    | m j =>
      simp only
      rw [crmNorm_C]
      linarith [(hm j hv).2.1]
    | f j =>
      simp only
      rw [crmNorm_X]
      linarith
    | w =>
      simp only
      rw [show (0 : ObsPoly) = C 0 from C_0.symm, crmNorm_C, norm_zero]
      linarith
    | γ =>
      simp only
      rw [crmNorm_C]
      have : ‖(((g ^ 2)⁻¹ : ℝ) : ℂ)‖ ≤ 1 := by rwa [← hγ]
      linarith
  calc ‖aeval y H - ∑ k ∈ T, linCoeff g a k H * y (.f k)‖
      = ‖(aeval y H - aeval y' H) + (aeval y' H - aeval z H) +
          (aeval z H - ∑ k ∈ T, linCoeff g a k H * y (.f k))‖ := by ring_nf
    _ ≤ ‖aeval y H - aeval y' H‖ + ‖aeval y' H - aeval z H‖ +
          ‖aeval z H - ∑ k ∈ T, linCoeff g a k H * y (.f k)‖ := norm_add₃_le
    _ ≤ N * ω + N * (δM * δF) + N * δF ^ 2 := add_le_add (add_le_add hA1 hA2) hB'
    _ = N * (ω + δM * δF + δF ^ 2) := by ring

/-! ### The order `1` of the updates of the `F_r` -/

private lemma crm_neg_neg (v : ObsVar) : v.neg.neg = v := by
  cases v <;> simp [ObsVar.neg]

private lemma crm_neg_inj : Function.Injective ObsVar.neg :=
  fun u v h => by rw [← crm_neg_neg u, h, crm_neg_neg]

private lemma crm_conjPoly_eq (p : ObsPoly) :
    conjPoly p = rename ObsVar.neg (map (starRingEnd ℂ) p) := by
  have h : conjPoly = (rename ObsVar.neg : ObsPoly →ₐ[ℂ] ObsPoly).toRingHom.comp
      (map (starRingEnd ℂ)) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) fun v => ?_
    · simp [conjPoly]
    · simp [conjPoly]
  rw [h]
  rfl

private lemma crm_coeff_conj (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (conjPoly p).coeff d = star (p.coeff (d.mapDomain ObsVar.neg)) := by
  have hd : d = (d.mapDomain ObsVar.neg).mapDomain ObsVar.neg := by
    rw [← Finsupp.mapDomain_comp]
    have : ObsVar.neg ∘ ObsVar.neg = id := funext crm_neg_neg
    rw [this, Finsupp.mapDomain_id]
  conv_lhs => rw [hd]
  rw [crm_conjPoly_eq, coeff_rename_mapDomain _ crm_neg_inj, coeff_map]
  rfl

private lemma crm_truncG_conj (N : ℕ) (p : ObsPoly) :
    truncG N (conjPoly p) = conjPoly (truncG N p) := by
  ext d
  have h : d.mapDomain ObsVar.neg ObsVar.γ = d ObsVar.γ :=
    Finsupp.mapDomain_apply_of_injective crm_neg_inj d ObsVar.γ
  rw [crm_coeff_truncG, crm_coeff_conj, crm_coeff_conj, crm_coeff_truncG, h]
  split_ifs <;> simp

/-- The order `1` of `C c (x_v + C h γ q)` is `C c x_v`. -/
private lemma crm_truncG_zero_of_one {p q : ObsPoly} {c h : ℂ} {v : ObsVar} (hv : v.gamWt = 0)
    (hp : truncG 1 p = C c * (X v + C h * X .γ * q)) : truncG 0 p = C c * X v := by
  have e : truncG 0 p = truncG 0 (truncG 1 p) := by
    ext d
    simp only [crm_coeff_truncG]
    split_ifs <;> first | rfl | omega
  have hvγ : v ≠ .γ := by
    rintro rfl
    simp [ObsVar.gamWt] at hv
  rw [e, hp, show C c * (X v + C h * X .γ * q) = C c * X v + X .γ * (C (c * h) * q) by
    rw [C_mul]; ring]
  ext d
  rw [crm_coeff_truncG]
  split_ifs with hd
  · have hγ : ObsVar.γ ∉ d.support := by
      rw [Finsupp.mem_support_iff]
      omega
    rw [show ∀ a b : ObsPoly, (a + b).coeff d = a.coeff d + b.coeff d from fun a b => by simp,
      coeff_X_mul']
    simp [hγ]
  · have hne : Finsupp.single v 1 ≠ d := by
      rintro rfl
      simp [hvγ.symm] at hd
    simp [coeff_C_mul, coeff_X, hne]

/-- The order `1` of `[P_g F_r]_{≤R+2,0}` is a multiple of `F_r` (the rotation of (11.45)
[lg:eq:required-parity-updates]). -/
private lemma crm_truncG_zero_corrUpd (R : ℕ) (Ks : Finset NzInt) :
    ∃ E₁ : ℝ, 0 < E₁ ∧ ∀ E : ℝ, |E| ≤ E₁ → ∀ r ∈ Ks, ∃ c : ℂ,
      truncG 0 (corrUpd E R (.f r)) = C c * X (.f r) := by
  set negK : NzInt → NzInt := fun k => ⟨-k.1, neg_ne_zero.mpr k.2⟩ with hnegK
  obtain ⟨E₁, hE₁, h⟩ := truncG_one_corrUpd R (Ks ∪ Ks.image negK)
  refine ⟨E₁, hE₁, fun E hE r hr => ?_⟩
  have hpos : ∀ k ∈ Ks ∪ Ks.image negK, 0 < k.1 →
      ∃ c : ℂ, truncG 0 (corrUpd E R (.f k)) = C c * X (.f k) :=
    fun k hk hk0 => ⟨_, crm_truncG_zero_of_one rfl (h E hE k hk hk0).2⟩
  rcases lt_or_gt_of_ne r.2 with hneg | hpos'
  · obtain ⟨c, hc⟩ := hpos (negK r) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hr))
      (by simp [negK]; omega)
    refine ⟨star c, ?_⟩
    have e1 : corrUpd E R (.f r) = conjPoly (corrUpd E R (.f (negK r))) := by
      rw [conjPoly_corrUpd]
      congr 1
      simp [ObsVar.neg, negK]
    rw [e1, crm_truncG_conj, hc, map_mul]
    simp [conjPoly, ObsVar.neg, negK]
  · exact hpos r (Finset.mem_union_left _ hr) hpos'

/-! ### Indices and rates -/

/-- The indices of `m_k`, `f_k`. -/
private def crmIdx : ObsVar → Finset NzInt
  | .m k => {k}
  | .f k => {k}
  | .w => ∅
  | .γ => ∅

/-- The indices of the variables of the monomials in `S`. -/
private def crmIdxS (S : Finset (ObsVar →₀ ℕ)) : Finset NzInt :=
  S.biUnion fun d => d.support.biUnion crmIdx

private lemma crm_mem_idxS {p : ObsPoly} {S : Finset (ObsVar →₀ ℕ)} (hS : p.support ⊆ S)
    {v : ObsVar} (hv : v ∈ p.vars) {j : NzInt} (hj : j ∈ crmIdx v) : j ∈ crmIdxS S := by
  obtain ⟨d, hd, hvd⟩ := (mem_vars_iff_mem_support v).1 hv
  exact Finset.mem_biUnion.mpr ⟨d, hS hd, Finset.mem_biUnion.mpr ⟨v, hvd, hj⟩⟩

/-- The rates on the good set, with `δ_M = W^{η−1}` and `δ_F = W^{η−1/2}`. -/
private lemma crm_rates {W : ℕ} (hW : 1 ≤ W) {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2) :
    0 ≤ (W : ℝ) ^ (η - 1) ∧ (W : ℝ) ^ (η - 1) ≤ 1 ∧ 0 ≤ (W : ℝ) ^ (η - 1 / 2) ∧
      (W : ℝ) ^ (η - 1 / 2) ≤ 1 ∧ (W : ℝ)⁻¹ ≤ 1 ∧
      (W : ℝ)⁻¹ + (W : ℝ) ^ (η - 1) * (W : ℝ) ^ (η - 1 / 2) + ((W : ℝ) ^ (η - 1 / 2)) ^ 2 ≤
        3 * (W : ℝ) ^ (2 * η - 1) ∧
      (W : ℝ) ^ (η - 1) * (W : ℝ) ^ (η - 1 / 2) + (W : ℝ)⁻¹ * ((W : ℝ) ^ (η - 1 / 2)) ^ 2 ≤
        2 * (W : ℝ) ^ (2 * η - 3 / 2) := by
  have hw1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hw0 : (0 : ℝ) < W := by linarith
  have hinv : (W : ℝ)⁻¹ = (W : ℝ) ^ (-1 : ℝ) := (Real.rpow_neg_one _).symm
  have hprod : (W : ℝ) ^ (η - 1) * (W : ℝ) ^ (η - 1 / 2) = (W : ℝ) ^ (2 * η - 3 / 2) := by
    rw [← Real.rpow_add hw0]
    congr 1
    ring
  have hsq : ((W : ℝ) ^ (η - 1 / 2)) ^ 2 = (W : ℝ) ^ (2 * η - 1) := by
    rw [sq, ← Real.rpow_add hw0]
    congr 1
    ring
  have hle : ∀ a b : ℝ, a ≤ b → (W : ℝ) ^ a ≤ (W : ℝ) ^ b :=
    fun a b hab => Real.rpow_le_rpow_of_exponent_le hw1 hab
  have h3 : (W : ℝ)⁻¹ * (W : ℝ) ^ (2 * η - 1) = (W : ℝ) ^ (2 * η - 2) := by
    rw [hinv, ← Real.rpow_add hw0]
    congr 1
    ring
  refine ⟨Real.rpow_nonneg hw0.le _, Real.rpow_le_one_of_one_le_of_nonpos hw1 (by linarith),
    Real.rpow_nonneg hw0.le _, Real.rpow_le_one_of_one_le_of_nonpos hw1 (by linarith),
    inv_le_one_of_one_le₀ hw1, ?_, ?_⟩
  · rw [hprod, hsq]
    have e1 : (W : ℝ)⁻¹ ≤ (W : ℝ) ^ (2 * η - 1) := by
      rw [hinv]
      exact hle _ _ (by linarith)
    have e2 := hle (2 * η - 3 / 2) (2 * η - 1) (by linarith)
    linarith
  · rw [hprod, hsq, h3]
    have e2 := hle (2 * η - 2) (2 * η - 3 / 2) (by linarith)
    linarith

/-- The evaluation point of the corrected observables. -/
private lemma crm_obs (g : ℝ) {W : ℕ} (X : State W) (E : ℝ) (R : ℕ) (Q : ObsPoly) :
    obsEval g X (bind₁ (corrCoord E R) Q) =
      aeval (fun v => obsEval g X (corrCoord E R v)) Q := by
  unfold obsEval
  rw [aeval_bind₁]

/-! ### The order `g⁻²` of the mean increment -/

private lemma crm_sub_C (g : ℝ) (a : ℤ → ℂ) (c : ℂ) : centerSub g a (C c) = C c := by
  simp [centerSub]

private lemma crm_sub_mVar {g : ℝ} {a : ℤ → ℂ} (ha : a 0 = 1) (j : ℤ) :
    centerSub g a (mVar j) = C (a j) := by
  unfold mVar
  split_ifs with h
  · subst h; simp [ha]
  · simp [centerSub]

private lemma crm_sub_fVar (g : ℝ) (a : ℤ → ℂ) (j : ℤ) : centerSub g a (fVar j) = fVar j := by
  unfold fVar
  split_ifs <;> simp [centerSub]

private lemma crm_sub_γ (g : ℝ) (a : ℤ → ℂ) :
    centerSub g a (X .γ) = C (((g ^ 2)⁻¹ : ℝ) : ℂ) := by
  simp [centerSub]

private lemma crm_coeff_fVar (k : NzInt) (n : ℤ) :
    (fVar n).coeff (Finsupp.single (.f k) 1) = if k.1 = n then 1 else 0 := by
  unfold fVar
  split_ifs with h1 h2 h2
  · exact absurd (h2.trans h1) k.2
  · rw [coeff_one]
    refine ite_eq_right_iff.mpr fun h => ?_
    have := congrArg (fun d : ObsVar →₀ ℕ => d (.f k)) h
    simp at this
  · rw [coeff_X]
    refine ite_eq_left_iff.mpr fun h => absurd ?_ h
    congr 2
    exact Subtype.ext h2.symm
  · rw [coeff_X]
    refine ite_eq_right_iff.mpr fun h => ?_
    have := congrArg (fun d : ObsVar →₀ ℕ => d (.f k)) h
    have hk : (⟨n, h1⟩ : NzInt) ≠ k := fun h' => h2 (by rw [← h'])
    simp [hk] at this

private lemma crm_center (g E : ℝ) (R : ℕ) :
    center g E R 0 = 1 ∧ center g E R 1 = 0 ∧ center g E R (-1) = 0 := by
  refine ⟨(center_zero_odd_neg g E R 0).1, (center_zero_odd_neg g E R 0).2.1,
    by simpa using (center_zero_odd_neg g E R (-1)).2.1⟩

/-- `[F_k]` of the term `h_θ² γ c_1` at `M = a` is `h_θ²/(2g²)` for `|k| = 1` and `0` otherwise
(from (11.12) [lg:eq:c2] and `a_{±1} = 0`). -/
private lemma crm_linCoeff_Z (g E : ℝ) (R : ℕ) (k : NzInt) :
    linCoeff g (center g E R) k (crmZ E) =
      if |k.1| = 1 then ((normalH E ^ 2 / (2 * g ^ 2) : ℝ) : ℂ) else 0 := by
  obtain ⟨h0, h1, hm1⟩ := crm_center g E R
  have hw : centerSub g (center g E R) (X .w) = 0 := by simp [centerSub]
  have hc1 : centerSub g (center g E R) (incWick 1) = C (1 / 2) * (fVar 1 + fVar (-1)) := by
    rw [incWick_one]
    simp only [map_add, map_sub, map_mul, map_pow, crm_sub_C, crm_sub_fVar, crm_sub_mVar h0, h1,
      hm1, hw, C_0]
    ring
  unfold linCoeff crmZ
  rw [map_mul, map_mul, crm_sub_C, map_pow, crm_sub_γ, hc1, ← C_pow, ← C_mul, ← mul_assoc,
    ← C_mul, coeff_C_mul]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.coe_add, Pi.add_apply, crm_coeff_fVar]
  by_cases hk : |k.1| = 1
  · simp only [hk, ↓reduceIte]
    rcases (abs_eq zero_le_one).mp hk with h | h
    all_goals
      simp only [h]
      norm_num
      ring
  · have h1 : k.1 ≠ 1 := fun h => hk (by rw [h]; rfl)
    have h2 : k.1 ≠ -1 := fun h => hk (by rw [h]; rfl)
    simp [hk, h1, h2]

/-- `h_θ ≤ 1` on `|E| ≤ 1`. -/
private lemma crm_normalH {E : ℝ} (hE : |E| ≤ 1) : 0 ≤ normalH E ∧ normalH E ≤ 1 := by
  unfold normalH freeAngle
  rw [Real.sin_arccos]
  have h1 : (E / 2) ^ 2 ≤ 3 / 4 := by
    have := sq_abs E
    nlinarith [abs_nonneg E]
  have h2 : (1 / 2 : ℝ) ≤ √(1 - (E / 2) ^ 2) := by
    rw [show (1 / 2 : ℝ) = √((1 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  refine ⟨by positivity, inv_le_one_of_one_le₀ (by linarith)⟩

/-- The variables of `c_r`, `r ≤ R + 2`. -/
private def crmV₀ (R : ℕ) : Finset ObsVar :=
  (Finset.range (R + 3)).biUnion fun r => (incWick r).vars

private lemma crm_vars_incPoly (E : ℝ) (R : ℕ) : (incPoly E R).vars ⊆ insert .γ (crmV₀ R) := by
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
      rw [vars_X, Finset.mem_singleton] at h3
      rw [h3]
      exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨r, hr, h1⟩)

/-- `‖Σ_r h^{2r} γ^r c_r‖ ≤ Σ_r c^r ‖c_r‖` for the constant weight `c` on `|E| ≤ 1`. -/
private lemma crm_norm_incPoly_le {E : ℝ} (hE : |E| ≤ 1) (R : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    crmNorm (fun _ => c) (incPoly E R) ≤
      ∑ r ∈ Finset.range (R + 3), c ^ r * crmNorm (fun _ => c) (incWick r) := by
  have hρ : ∀ _ : ObsVar, 0 ≤ c := fun _ => hc
  obtain ⟨hh0, hh1⟩ := crm_normalH hE
  unfold incPoly
  refine (crmNorm_sum_le hρ _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  refine (crmNorm_mul_le hρ _ _).trans (mul_le_mul_of_nonneg_right ?_ (crmNorm_nonneg hρ _))
  refine (crmNorm_mul_le hρ _ _).trans ?_
  rw [crmNorm_C]
  have h1 : ‖(((normalH E ^ (2 * r) : ℝ)) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hh0 _)]
    exact pow_le_one₀ hh0 hh1
  have h2 : crmNorm (fun _ => c) (X ObsVar.γ ^ r : ObsPoly) ≤ c ^ r :=
    (crmNorm_pow_le hρ _ _).trans (by rw [crmNorm_X])
  calc ‖(((normalH E ^ (2 * r) : ℝ)) : ℂ)‖ * crmNorm (fun _ => c) (X ObsVar.γ ^ r : ObsPoly)
      ≤ 1 * c ^ r := mul_le_mul h1 h2 (crmNorm_nonneg hρ _) zero_le_one
    _ = c ^ r := one_mul _

/-- The bound of the explicit part of order `g⁻²`. -/
private lemma crm_Zpart_le {M₁ M₂ F₁ F₂ u : ℂ} {δM δF ω : ℝ} (hM₁ : ‖M₁‖ ≤ δM)
    (hM₂ : ‖M₂‖ ≤ δM) (hF₁ : ‖F₁‖ ≤ δF) (hF₂ : ‖F₂‖ ≤ δF) (hu : ‖u‖ ≤ ω) :
    ‖(1 / 2 : ℂ) * (M₁ * F₁ + M₂ * F₂) - 1 / 4 * u * (F₁ ^ 2 + F₂ ^ 2)‖ ≤
      δM * δF + ω * δF ^ 2 := by
  have hδM : 0 ≤ δM := (norm_nonneg _).trans hM₁
  have hδF : 0 ≤ δF := (norm_nonneg _).trans hF₁
  have e1 : ‖(1 / 2 : ℂ) * (M₁ * F₁ + M₂ * F₂)‖ ≤ 1 / 2 * (δM * δF + δM * δF) := by
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (by norm_num)
    rw [norm_mul, norm_mul]
    exact add_le_add (mul_le_mul hM₁ hF₁ (norm_nonneg _) hδM)
      (mul_le_mul hM₂ hF₂ (norm_nonneg _) hδM)
  have hω : 0 ≤ ω := (norm_nonneg _).trans hu
  have e2 : ‖1 / 4 * u * (F₁ ^ 2 + F₂ ^ 2)‖ ≤ 1 / 4 * ω * (δF ^ 2 + δF ^ 2) := by
    rw [norm_mul, norm_mul, show ‖(1 / 4 : ℂ)‖ = 1 / 4 by norm_num]
    refine mul_le_mul (mul_le_mul_of_nonneg_left hu (by norm_num)) ((norm_add_le _ _).trans ?_)
      (norm_nonneg _) (mul_nonneg (by norm_num) hω)
    rw [norm_pow, norm_pow]
    exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) hF₁ 2)
      (pow_le_pow_left₀ (norm_nonneg _) hF₂ 2)
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ 1 / 2 * (δM * δF + δM * δF) + 1 / 4 * ω * (δF ^ 2 + δF ^ 2) := add_le_add e1 e2
    _ ≤ δM * δF + ω * δF ^ 2 := by nlinarith [mul_nonneg hω (sq_nonneg δF)]

private lemma crm_sum3_le {K₁ K₂ K₃ x y z : ℝ} (h1 : 0 ≤ K₁) (h2 : 0 ≤ K₂) (h3 : 0 ≤ K₃)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    K₁ * x + K₂ * y + K₃ * z ≤ (K₁ + K₂ + K₃) * (x + y + z) := by
  nlinarith [mul_nonneg h1 hy, mul_nonneg h1 hz, mul_nonneg h2 hx, mul_nonneg h2 hz,
    mul_nonneg h3 hx, mul_nonneg h3 hy]

/-- The remainder `𝓡_0` of (11.62) [lg:eq:corrector-linear-expansions] on the good set
((11.65) [lg:eq:corrector-remainder-bounds]). -/
theorem incMean_lin_sub_le (R : ℕ) :
    ∃ Ks : Finset NzInt, ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ K g₀ : ℝ, 0 < K ∧ 1 ≤ g₀ ∧
      ∀ Kt : Finset NzInt, Ks ⊆ Kt → ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, g₀ ≤ g → ∀ E : ℝ, |E| ≤ E₁ →
        ∀ η : ℝ, 0 ≤ η → η ≤ 1 / 2 → ∀ X : State W, IsState X → corrGood g E R Kt η X →
          ‖((incMean g E X : ℝ) : ℂ) - ((normalH E ^ 2 / (2 * W * g ^ 2) : ℝ) : ℂ) -
              ∑ k ∈ Kt, driftCoeff g E R k * obsEval g X (corrObsF E R k)‖ ≤
            K * ((W : ℝ) ^ (2 * η - 3 / 2) / g ^ 2 + (W : ℝ) ^ (2 * η - 1) / g ^ 4 +
              1 / g ^ (2 * R + 6)) := by
  obtain ⟨E₆, hE₆, K₆, hK₆, h₆⟩ := incMean_corr_sub_le R
  obtain ⟨E₃, hE₃, S₀, K₀, hK₀, h₀⟩ := corrCoeff_bounded R ((crmV₀ R).biUnion crmIdx)
  set VV : Finset ObsVar := insert .γ (insert .w (crmV₀ R)) ∪ S₀.biUnion fun d => d.support
    with hVV
  set one : NzInt := ⟨1, one_ne_zero⟩ with hone_def
  set mone : NzInt := ⟨-1, by norm_num⟩ with hmone_def
  set Ks : Finset NzInt := VV.biUnion crmIdx ∪ {one, mone} with hKs
  obtain ⟨E₂, hE₂, c₀, Kb, g₀, hc₀, hKb, hg₀, hb⟩ := center_bounds R Ks
  set B : ℝ := max Kb 1 + 1 with hB
  have hB1 : 1 ≤ B := by have := le_max_right Kb 1; linarith
  have h2B : ∀ _ : ObsVar, (0 : ℝ) ≤ 2 * B := fun _ => by linarith
  set ρ : ObsVar → ℝ := fun _ => 2 * B with hρ
  set cc : ℝ := max (2 * B) (∑ d ∈ S₀, K₀ * crmWt ρ d) with hcc
  have hcc0 : 0 ≤ cc := le_trans (by linarith) (le_max_left _ _)
  have hρc : ∀ _ : ObsVar, 0 ≤ cc := fun _ => hcc0
  set K₁ : ℝ := ∑ r ∈ Finset.range (R + 3), cc ^ r * crmNorm (fun _ => cc) (incWick r) +
    2 * B * crmNorm ρ (incWick 1) with hK₁
  have hK₁0 : 0 ≤ K₁ := add_nonneg (Finset.sum_nonneg fun r _ =>
    mul_nonneg (pow_nonneg hcc0 _) (crmNorm_nonneg hρc _))
    (mul_nonneg (by linarith) (crmNorm_nonneg h2B _))
  refine ⟨Ks, min (min E₆ E₃) (min E₂ 1), lt_min (lt_min hE₆ hE₃) (lt_min hE₂ one_pos),
    K₆ + 3 * K₁ + 2, g₀, by positivity, hg₀,
    fun Kt hKt W hW g hg E hE η hη0 hη X hX hgood => ?_⟩
  have hE6 : |E| ≤ E₆ := hE.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hE3 : |E| ≤ E₃ := hE.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hE2 : |E| ≤ E₂ := hE.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hE1 : |E| ≤ 1 := hE.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hg1 : 1 ≤ g := hg₀.trans hg
  have hg0 : 0 < g := by linarith
  obtain ⟨hδM0, hδM1, hδF0, hδF1, hω1, hrate, hrate2⟩ := crm_rates hW hη0 hη
  set t : ℝ := (g ^ 2)⁻¹ with ht
  have ht0 : 0 ≤ t := by positivity
  obtain ⟨hh0, hh1⟩ := crm_normalH hE1
  -- the evaluation point
  set y : ObsVar → ℂ := fun v => obsEval g X (corrCoord E R v) with hy
  have hyf : ∀ k, obsEval g X (corrObsF E R k) = y (.f k) := fun k => rfl
  have hyw : y .w = (W : ℂ)⁻¹ := by
    change obsEval g X (MvPolynomial.X .w) = _
    simp [obsEval]
  have hyγ : y .γ = ((t : ℝ) : ℂ) := by
    change obsEval g X (MvPolynomial.X .γ) = _
    simp [obsEval, ht]
  -- the decomposition `incCorr = h² γ c_1 + γ² H`
  obtain ⟨H, hH⟩ := crm_incCorr_sub E R
  have hΦ : incCorr E R = crmZ E + MvPolynomial.X .γ * (MvPolynomial.X .γ * H) := by
    rw [← mul_assoc, ← sq, ← hH]
    ring
  -- the `W⁰` part of `H` lies in `(f_k)`
  have hHf : zeroW H ∈ fIdeal := by
    refine crm_mem_fIdeal_of_γ_mul (crm_mem_fIdeal_of_γ_mul ?_)
    have e : MvPolynomial.X .γ * (MvPolynomial.X .γ * zeroW H) =
        zeroW (incCorr E R) - zeroW (crmZ E) := by
      rw [hΦ, map_add, map_mul, map_mul, crm_zeroW_X]
      simp
    rw [e]
    refine Ideal.sub_mem _ (zeroW_incCorr_mem_fIdeal E R) ?_
    unfold crmZ
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ (zeroW_incWick_mem_fIdeal le_rfl)
  -- variables of the expansion
  have hinv : ∀ u ∈ (incPoly E R).vars,
      (invCoord E R u).vars ⊆ VV ∧ crmNorm ρ (invCoord E R u) ≤ cc := by
    intro u hu
    have hu' := crm_vars_incPoly E R hu
    have hS : ∀ i : NzInt, ∀ v ∈ [ObsVar.m i, ObsVar.f i], v = u → u ∈ crmV₀ R →
        (invCoord E R u).vars ⊆ VV ∧ crmNorm ρ (invCoord E R u) ≤ cc := by
      intro i v hv hvu hu0
      have hi : i ∈ (crmV₀ R).biUnion crmIdx := by
        refine Finset.mem_biUnion.mpr ⟨u, hu0, ?_⟩
        rw [← hvu]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl <;> simp [crmIdx]
      obtain ⟨-, hsupp, -, hcoef⟩ := h₀ E hE3 i hi v hv
      rw [hvu] at hsupp hcoef
      refine ⟨fun x hx => ?_, ?_⟩
      · obtain ⟨d, hd, hxd⟩ := (mem_vars_iff_mem_support x).1 hx
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨d, hsupp hd, hxd⟩)
      · exact (crmNorm_le_of_support h2B hsupp fun d => (hcoef d).2.1).trans (le_max_right _ _)
    cases u with
    | m i => exact hS i _ (by simp) rfl (by simpa using hu')
    | f i => exact hS i _ (by simp) rfl (by simpa using hu')
    | w =>
      rw [crm_invCoord_w, vars_X, crmNorm_X]
      exact ⟨by simp [hVV], le_max_left _ _⟩
    | γ =>
      rw [crm_invCoord_γ, vars_X, crmNorm_X]
      exact ⟨by simp [hVV], le_max_left _ _⟩
  have hvars : (incCorr E R - crmZ E).vars ⊆ VV := by
    intro v hv
    rcases Finset.mem_union.mp (vars_sub_subset _ hv) with h | h
    · obtain ⟨d, hd, hvd⟩ := (mem_vars_iff_mem_support v).1 h
      have h' : v ∈ (bind₁ (invCoord E R) (incPoly E R)).vars :=
        (mem_vars_iff_mem_support v).2 ⟨d, crm_support_truncG _ _ hd, hvd⟩
      obtain ⟨u, hu, hvu⟩ := Finset.mem_biUnion.mp (vars_bind₁ _ _ h')
      exact (hinv u hu).1 hvu
    · unfold crmZ at h
      rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h
      · rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h
        · rw [vars_C] at h
          exact absurd h (Finset.notMem_empty _)
        · have := vars_pow _ _ h
          rw [vars_X, Finset.mem_singleton] at this
          rw [this]
          simp [hVV]
      · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_biUnion.mpr ⟨1, by simp, h⟩)))
  have hvarsH : ∀ v ∈ H.vars, crmIdx v ⊆ Ks := by
    intro v hv
    have hv1 : v ∈ (incCorr E R - crmZ E).vars := by
      rw [hH, pow_two, mul_assoc]
      exact crm_vars_X_mul _ _ (crm_vars_X_mul _ _ hv)
    exact fun j hj => Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨v, hvars hv1, hj⟩)
  -- the norm of `H`
  have hNH : crmNorm ρ H ≤ K₁ := by
    have hn : crmNorm ρ (incCorr E R - crmZ E) ≤ K₁ := by
      refine (crmNorm_sub_le h2B _ _).trans (add_le_add ?_ ?_)
      · have h1 : crmNorm ρ (incCorr E R) ≤ crmNorm ρ (bind₁ (invCoord E R) (incPoly E R)) :=
          crmNorm_mono h2B fun d => by
            unfold incCorr
            rw [crm_coeff_truncG]
            split_ifs
            · exact le_rfl
            · rw [norm_zero]; exact norm_nonneg _
        exact h1.trans ((crmNorm_bind₁_le h2B _ _ fun u hu => (hinv u hu).2).trans
          (crm_norm_incPoly_le hE1 R hcc0))
      · unfold crmZ
        refine (crmNorm_mul_le h2B _ _).trans ?_
        have h1 : crmNorm ρ (C (((normalH E ^ (2 * 1) : ℝ) : ℂ)) * MvPolynomial.X .γ ^ 1) ≤
            2 * B := by
          refine (crmNorm_mul_le h2B _ _).trans ?_
          rw [crmNorm_C, pow_one, crmNorm_X, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by positivity)]
          have : normalH E ^ (2 * 1) ≤ 1 := pow_le_one₀ hh0 hh1
          nlinarith
        exact mul_le_mul_of_nonneg_right h1 (crmNorm_nonneg h2B _)
    rw [hH, pow_two, mul_assoc, crmNorm_X_mul, crmNorm_X_mul] at hn
    have hn' : (2 * B) * ((2 * B) * crmNorm ρ H) ≤ K₁ := hn
    have h0 : 0 ≤ crmNorm ρ H := crmNorm_nonneg h2B H
    have h4 : 0 ≤ (2 * B) * (2 * B) - 1 := by nlinarith
    nlinarith [mul_nonneg h4 h0]
  -- the basic estimate for `H`
  have hcore := crm_core hHf hg1 (a := center g E R) (y := y) (T := Kt) hB1 hδM0 hδF0 hδF1 hω1
    (fun k hk => hKt (hvarsH _ hk (by simp [crmIdx])))
    (fun j hj => by
      have hj' : j ∈ Ks := hvarsH _ hj (by simp [crmIdx])
      have ha := ((hb g hg E hE2).2 j hj').2.1
      have hM := (hgood j (hKt hj')).1
      refine ⟨?_, ha.trans (by have := le_max_left Kb 1; linarith), hM⟩
      calc ‖y (.m j)‖ = ‖center g E R j.1 + (y (.m j) - center g E R j.1)‖ := by
            rw [add_sub_cancel]
        _ ≤ ‖center g E R j.1‖ + ‖y (.m j) - center g E R j.1‖ := norm_add_le _ _
        _ ≤ Kb + 1 := add_le_add ha (hM.trans hδM1)
        _ ≤ B := by have := le_max_left Kb 1; linarith)
    (fun k hk => (hgood k hk).2) (by rw [hyw, norm_inv, Complex.norm_natCast]) hyγ
  -- the explicit part of order `g⁻²`
  have hone : one ∈ Kt := hKt (Finset.mem_union_right _ (by simp))
  have hmone : mone ∈ Kt := hKt (Finset.mem_union_right _ (by simp))
  obtain ⟨-, hc1, hcm1⟩ := crm_center g E R
  have hM1 : ‖y (.m one)‖ ≤ (W : ℝ) ^ (η - 1) := by
    have := (hgood one hone).1
    rwa [show center g E R one.1 = 0 from hc1, sub_zero] at this
  have hMm1 : ‖y (.m mone)‖ ≤ (W : ℝ) ^ (η - 1) := by
    have := (hgood mone hmone).1
    rwa [show center g E R mone.1 = 0 from hcm1, sub_zero] at this
  have hZ := crm_Zpart_le hM1 hMm1 (hgood one hone).2 (hgood mone hmone).2
    (show ‖y .w‖ ≤ (W : ℝ)⁻¹ by rw [hyw, norm_inv, Complex.norm_natCast])
  have habs1 : |one.1| = 1 := by rw [hone_def]; rfl
  have habsm1 : |mone.1| = 1 := by rw [hmone_def]; rfl
  have hne : one ≠ mone := fun h => by
    have := congrArg Subtype.val h
    rw [hone_def, hmone_def] at this
    norm_num at this
  have hZsum : ∑ k ∈ Kt, linCoeff g (center g E R) k (crmZ E) * y (.f k) =
      ((normalH E ^ 2 / (2 * g ^ 2) : ℝ) : ℂ) * (y (.f one) + y (.f mone)) := by
    rw [Finset.sum_eq_add_of_mem one mone hone hmone hne]
    · simp only [crm_linCoeff_Z, habs1, habsm1, ↓reduceIte]
      ring
    · intro k _ hk
      have hk1 : ¬|k.1| = 1 := by
        intro h
        rcases (abs_eq zero_le_one).mp h with h | h
        · exact hk.1 (Subtype.ext (by rw [h, hone_def]))
        · exact hk.2 (Subtype.ext (by rw [h, hmone_def]))
      simp only [crm_linCoeff_Z, hk1, ↓reduceIte, zero_mul]
  have hZe : aeval y (crmZ E) = (((normalH E ^ (2 * 1) : ℝ) : ℂ)) * (t : ℂ) *
      (1 / 2 * y .w + 1 / 2 * (y (.f one) + y (.f mone)) +
        1 / 2 * (y (.m one) * y (.f one) + y (.m mone) * y (.f mone)) -
        1 / 4 * y .w * (y (.f one) ^ 2 + y (.f mone) ^ 2)) := by
    have hf1 : fVar 1 = MvPolynomial.X (.f one) := by simp [fVar, hone_def]
    have hfm1 : fVar (-1) = MvPolynomial.X (.f mone) := by simp [fVar, hmone_def]
    have hm1 : mVar 1 = MvPolynomial.X (.m one) := by simp [mVar, hone_def]
    have hmm1 : mVar (-1) = MvPolynomial.X (.m mone) := by simp [mVar, hmone_def]
    unfold crmZ
    rw [incWick_one, hf1, hfm1, hm1, hmm1]
    simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, Algebra.algebraMap_self,
      RingHom.id_apply, hyγ]
    ring
  -- the identity
  have hlin : ∀ k, driftCoeff g E R k = linCoeff g (center g E R) k (crmZ E) +
      (t : ℂ) * ((t : ℂ) * linCoeff g (center g E R) k H) := by
    intro k
    change linCoeff g (center g E R) k (incCorr E R) = _
    rw [hΦ, crm_linCoeff_add, crm_linCoeff_γ_mul, crm_linCoeff_γ_mul]
  have hsum : ∑ k ∈ Kt, driftCoeff g E R k * y (.f k) =
      ∑ k ∈ Kt, linCoeff g (center g E R) k (crmZ E) * y (.f k) +
      (t : ℂ) * ((t : ℂ) * ∑ k ∈ Kt, linCoeff g (center g E R) k H * y (.f k)) := by
    simp only [hlin, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  have hΦe : obsEval g X (bind₁ (corrCoord E R) (incCorr E R)) =
      aeval y (crmZ E) + (t : ℂ) * ((t : ℂ) * aeval y H) := by
    rw [crm_obs, hΦ]
    change aeval y _ = _
    simp only [map_add, map_mul, aeval_X, hyγ]
  have key : ((incMean g E X : ℝ) : ℂ) - ((normalH E ^ 2 / (2 * W * g ^ 2) : ℝ) : ℂ) -
      ∑ k ∈ Kt, driftCoeff g E R k * y (.f k) =
      (((incMean g E X : ℝ) : ℂ) - obsEval g X (bind₁ (corrCoord E R) (incCorr E R))) +
      (((normalH E ^ 2 : ℝ) : ℂ)) * (t : ℂ) *
        ((1 / 2 : ℂ) * (y (.m one) * y (.f one) + y (.m mone) * y (.f mone)) -
          1 / 4 * y .w * (y (.f one) ^ 2 + y (.f mone) ^ 2)) +
      (t : ℂ) ^ 2 * (aeval y H - ∑ k ∈ Kt, linCoeff g (center g E R) k H * y (.f k)) := by
    rw [hsum, hZsum, hΦe, hZe, hyw, ht]
    push_cast
    ring
  simp only [hyf]
  rw [key]
  have h6 := h₆ W hW g hg1 E hE6 X hX
  set δM := (W : ℝ) ^ (η - 1) with hδM
  set δF := (W : ℝ) ^ (η - 1 / 2) with hδF
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set w₁ := (W : ℝ) ^ (2 * η - 3 / 2) with hw₁
  set w₂ := (W : ℝ) ^ (2 * η - 1) with hw₂
  have hw₁0 : 0 ≤ w₁ := Real.rpow_nonneg hW0.le _
  have hw₂0 : 0 ≤ w₂ := Real.rpow_nonneg hW0.le _
  have hh2 : ‖(((normalH E ^ 2 : ℝ) : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_one₀ hh0 hh1
  calc _ ≤ ‖((incMean g E X : ℝ) : ℂ) - obsEval g X (bind₁ (corrCoord E R) (incCorr E R))‖ +
        ‖(((normalH E ^ 2 : ℝ) : ℂ))‖ * ‖(t : ℂ)‖ *
          ‖(1 / 2 : ℂ) * (y (.m one) * y (.f one) + y (.m mone) * y (.f mone)) -
            1 / 4 * y .w * (y (.f one) ^ 2 + y (.f mone) ^ 2)‖ +
        ‖(t : ℂ)‖ ^ 2 * ‖aeval y H - ∑ k ∈ Kt, linCoeff g (center g E R) k H * y (.f k)‖ := by
        rw [← norm_mul, ← norm_mul, ← norm_pow, ← norm_mul]
        exact norm_add₃_le
    _ ≤ K₆ / g ^ (2 * R + 6) + 1 * t * (2 * w₁) + t ^ 2 * (K₁ * (3 * w₂)) := by
        have htn : ‖((t : ℝ) : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_of_nonneg ht0]
        rw [htn]
        refine add_le_add (add_le_add h6 ?_) ?_
        · refine mul_le_mul (mul_le_mul_of_nonneg_right hh2 ht0) (hZ.trans hrate2)
            (norm_nonneg _) (by positivity)
        · refine mul_le_mul_of_nonneg_left (hcore.trans ?_) (by positivity)
          exact mul_le_mul hNH hrate (by positivity) hK₁0
    _ ≤ (K₆ + 3 * K₁ + 2) * (w₁ / g ^ 2 + w₂ / g ^ 4 + 1 / g ^ (2 * R + 6)) := by
        have e1 : 1 * t * (2 * w₁) = 2 * (w₁ / g ^ 2) := by rw [ht]; field_simp
        have e2 : t ^ 2 * (K₁ * (3 * w₂)) = 3 * K₁ * (w₂ / g ^ 4) := by rw [ht]; field_simp
        have e3 : K₆ / g ^ (2 * R + 6) = K₆ * (1 / g ^ (2 * R + 6)) := by ring
        rw [e1, e2, e3]
        have hA : 0 ≤ w₁ / g ^ 2 := by positivity
        have hB' : 0 ≤ w₂ / g ^ 4 := by positivity
        have hC : 0 ≤ 1 / g ^ (2 * R + 6) := by positivity
        calc K₆ * (1 / g ^ (2 * R + 6)) + 2 * (w₁ / g ^ 2) + 3 * K₁ * (w₂ / g ^ 4)
            = 2 * (w₁ / g ^ 2) + 3 * K₁ * (w₂ / g ^ 4) + K₆ * (1 / g ^ (2 * R + 6)) := by ring
          _ ≤ (2 + 3 * K₁ + K₆) * (w₁ / g ^ 2 + w₂ / g ^ 4 + 1 / g ^ (2 * R + 6)) :=
            crm_sum3_le (by norm_num) (by positivity) hK₆.le hA hB' hC
          _ = _ := by ring

/-- The remainders `𝓡_r` of (11.62) [lg:eq:corrector-linear-expansions] on the good set
((11.65) [lg:eq:corrector-remainder-bounds]), for `r` in a given finite index set. -/
theorem transOp_corrF_lin_sub_le (R : ℕ) (Ks : Finset NzInt) :
    ∃ Ks' : Finset NzInt, Ks ⊆ Ks' ∧ ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ K g₀ : ℝ, 0 < K ∧ 1 ≤ g₀ ∧
      ∀ Kt : Finset NzInt, Ks' ⊆ Kt → ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, g₀ ≤ g → ∀ E : ℝ, |E| ≤ E₁ →
        ∀ η : ℝ, 0 ≤ η → η ≤ 1 / 2 → ∀ X : State W, IsState X → corrGood g E R Kt η X →
          ∀ r ∈ Ks,
            ‖transOp g E (fun Y => obsEval g Y (corrObsF E R r)) X -
                obsEval g X (corrObsF E R r) -
                ∑ k ∈ Kt, corrMat g E R k r * obsEval g X (corrObsF E R k)‖ ≤
              K * ((W : ℝ) ^ (2 * η - 1) / g ^ 2 + 1 / (W * g ^ 2) + 1 / g ^ (2 * R + 2)) := by
  obtain ⟨E₂, hE₂, S, Kc, hKc, hS⟩ := corrCoeff_bounded R Ks
  set Ks' : Finset NzInt := Ks ∪ crmIdxS S with hKs'
  obtain ⟨E₃, hE₃, c₀, Kb, g₀, hc₀, hKb, hg₀, hb⟩ := center_bounds R Ks'
  obtain ⟨E₄, hE₄, K₄, hK₄, h₄⟩ := transOp_corrObs_sub_le R Ks
  obtain ⟨E₅, hE₅, h₅⟩ := crm_truncG_zero_corrUpd R Ks
  set B : ℝ := max Kb 1 + 1 with hB
  have hB1 : 1 ≤ B := by have := le_max_right Kb 1; linarith
  have h2B : ∀ _ : ObsVar, (0 : ℝ) ≤ 2 * B := fun _ => by linarith
  set K₀ : ℝ := ∑ d ∈ S, Kc * crmWt (fun _ => 2 * B) d + 2 * B with hK₀
  have hK₀0 : 0 ≤ K₀ := add_nonneg
    (Finset.sum_nonneg fun d _ => mul_nonneg hKc.le (crmWt_nonneg h2B d)) (by linarith)
  refine ⟨Ks', Finset.subset_union_left, min (min E₂ E₃) (min E₄ E₅),
    lt_min (lt_min hE₂ hE₃) (lt_min hE₄ hE₅), K₄ + 3 * K₀ + 1, g₀, by positivity, hg₀,
    fun Kt hKt W hW g hg E hE η hη0 hη X hX hgood r hr => ?_⟩
  have hE2 : |E| ≤ E₂ := hE.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hE3 : |E| ≤ E₃ := hE.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hE4 : |E| ≤ E₄ := hE.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hE5 : |E| ≤ E₅ := hE.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hg1 : 1 ≤ g := hg₀.trans hg
  have hg0 : 0 < g := by linarith
  obtain ⟨hδM0, hδM1, hδF0, hδF1, hω1, hrate, -⟩ := crm_rates hW hη0 hη
  set t : ℝ := (g ^ 2)⁻¹ with ht
  have ht0 : 0 ≤ t := by positivity
  -- the evaluation point
  set y : ObsVar → ℂ := fun v => obsEval g X (corrCoord E R v) with hy
  have hyf : ∀ k, obsEval g X (corrObsF E R k) = y (.f k) := fun k => rfl
  have hyw : y .w = (W : ℂ)⁻¹ := by
    change obsEval g X (MvPolynomial.X .w) = _
    simp [obsEval]
  have hyγ : y .γ = ((t : ℝ) : ℂ) := by
    change obsEval g X (MvPolynomial.X .γ) = _
    simp [obsEval, ht]
  -- the decomposition of the update
  set U := corrUpd E R (.f r) with hU
  set P := U - MvPolynomial.X (.f r) with hP
  obtain ⟨c, hc⟩ := h₅ E hE5 r hr
  have hP0 : truncG 0 P = C (c - 1) * MvPolynomial.X (.f r) := by
    rw [hP, map_sub, hc, crm_truncG_X (by simp [ObsVar.gamWt]), C_sub, C_1]
    ring
  obtain ⟨H, hH⟩ : MvPolynomial.X .γ ∣ P - truncG 0 P := by simpa using crm_dvd_sub_truncG 0 P
  have hPH : P = C (c - 1) * MvPolynomial.X (.f r) + MvPolynomial.X .γ * H := by
    rw [← hH, hP0]; ring
  -- the `W⁰` part of `H` lies in `(f_k)`
  have hfr : (MvPolynomial.X (.f r) : ObsPoly) ∈ fIdeal := Ideal.subset_span ⟨r, rfl⟩
  have hHf : zeroW H ∈ fIdeal := by
    refine crm_mem_fIdeal_of_γ_mul ?_
    have e : MvPolynomial.X .γ * zeroW H = zeroW (P - C (c - 1) * MvPolynomial.X (.f r)) := by
      rw [hPH, add_sub_cancel_left, map_mul, crm_zeroW_X]
      simp
    rw [e]
    exact crm_zeroW_mem (Ideal.sub_mem _ (Ideal.sub_mem _ (corrUpd_mem_fIdeal E R r) hfr)
      (Ideal.mul_mem_left _ _ hfr))
  -- variables and norm of `H`
  obtain ⟨-, -, hUS, hUK⟩ := hS E hE2 r hr (.f r) (by simp)
  have hvarsH : ∀ v ∈ H.vars, crmIdx v ⊆ Ks' := by
    intro v hv
    have hv1 : v ∈ (P - truncG 0 P).vars := hH ▸ crm_vars_X_mul _ _ hv
    have hv2 : v ∈ P.vars := by
      rcases Finset.mem_union.mp (vars_sub_subset _ hv1) with h | h
      · exact h
      · obtain ⟨d, hd, hvd⟩ := (mem_vars_iff_mem_support v).1 h
        exact (mem_vars_iff_mem_support v).2 ⟨d, crm_support_truncG _ _ hd, hvd⟩
    rcases Finset.mem_union.mp (vars_sub_subset _ hv2) with h | h
    · exact fun j hj => Finset.mem_union_right _ (crm_mem_idxS (hUS.trans le_rfl) h hj)
    · rw [vars_X, Finset.mem_singleton] at h
      subst h
      intro j hj
      simp only [crmIdx, Finset.mem_singleton] at hj
      subst hj
      exact Finset.mem_union_left _ hr
  have hNH : crmNorm (fun _ => 2 * B) H ≤ K₀ := by
    have h1 : crmNorm (fun _ => 2 * B) (MvPolynomial.X .γ * H) ≤ K₀ := by
      rw [← hH]
      have hm : crmNorm (fun _ => 2 * B) (P - truncG 0 P) ≤ crmNorm (fun _ => 2 * B) P := by
        refine crmNorm_mono h2B fun d => ?_
        rw [crm_coeff_sub_truncG]
        split_ifs
        · rw [norm_zero]; exact norm_nonneg _
        · exact le_rfl
      have hPn : crmNorm (fun _ => 2 * B) P ≤ K₀ := (crmNorm_sub_le h2B _ _).trans
        (add_le_add (crmNorm_le_of_support h2B hUS fun d => (hUK d).2.2) (crmNorm_X _ _).le)
      exact hm.trans hPn
    rw [crmNorm_X_mul] at h1
    have h0 := crmNorm_nonneg h2B H
    nlinarith
  -- the basic estimate for `H`
  have hcore := crm_core hHf hg1 (a := center g E R) (y := y) (T := Kt) hB1 hδM0 hδF0 hδF1 hω1
    (fun k hk => hKt (hvarsH _ hk (by simp [crmIdx])))
    (fun j hj => by
      have hj' : j ∈ Ks' := hvarsH _ hj (by simp [crmIdx])
      have ha := ((hb g hg E hE3).2 j hj').2.1
      have hM := (hgood j (hKt hj')).1
      refine ⟨?_, ha.trans (by have := le_max_left Kb 1; linarith), hM⟩
      calc ‖y (.m j)‖ = ‖center g E R j.1 + (y (.m j) - center g E R j.1)‖ := by
            rw [add_sub_cancel]
        _ ≤ ‖center g E R j.1‖ + ‖y (.m j) - center g E R j.1‖ := norm_add_le _ _
        _ ≤ Kb + 1 := add_le_add ha (hM.trans hδM1)
        _ ≤ B := by have := le_max_left Kb 1; linarith)
    (fun k hk => (hgood k hk).2) (by rw [hyw, norm_inv, Complex.norm_natCast])
    hyγ
  -- the identity
  have hlin : ∀ k, corrMat g E R k r = (if k = r then c - 1 else 0) +
      (t : ℂ) * linCoeff g (center g E R) k H := by
    intro k
    change linCoeff g (center g E R) k P = _
    rw [hPH, crm_linCoeff_add, crm_linCoeff_γ_mul, crm_linCoeff_C_X]
  have hsum : ∑ k ∈ Kt, corrMat g E R k r * y (.f k) = (c - 1) * y (.f r) +
      (t : ℂ) * ∑ k ∈ Kt, linCoeff g (center g E R) k H * y (.f k) := by
    have hrKt : r ∈ Kt := hKt (Finset.mem_union_left _ hr)
    simp only [hlin, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      hrKt, ↓reduceIte, Finset.mul_sum, mul_assoc]
  have hUe : obsEval g X (bind₁ (corrCoord E R) U) =
      (c - 1) * y (.f r) + (t : ℂ) * aeval y H + y (.f r) := by
    rw [crm_obs, show U = P + MvPolynomial.X (.f r) by rw [hP]; ring, hPH]
    change aeval y _ = _
    simp only [map_add, map_mul, aeval_C, aeval_X, hyγ, Algebra.algebraMap_self,
      RingHom.id_apply]
  have key : transOp g E (fun Y => obsEval g Y (corrObsF E R r)) X - y (.f r) -
      ∑ k ∈ Kt, corrMat g E R k r * y (.f k) =
      (transOp g E (fun Y => obsEval g Y (corrObsF E R r)) X -
        obsEval g X (bind₁ (corrCoord E R) U)) +
      (t : ℂ) * (aeval y H - ∑ k ∈ Kt, linCoeff g (center g E R) k H * y (.f k)) := by
    rw [hsum, hUe]
    ring
  simp only [hyf]
  rw [key]
  have h4 := (h₄ W hW g hg1 E hE4 X hX r hr).2
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set w := (W : ℝ) ^ (2 * η - 1) with hw
  have hw0 : 0 ≤ w := Real.rpow_nonneg hW0.le _
  calc _ ≤ ‖transOp g E (fun Y => obsEval g Y (corrObsF E R r)) X -
          obsEval g X (bind₁ (corrCoord E R) U)‖ +
        ‖(t : ℂ)‖ * ‖aeval y H - ∑ k ∈ Kt, linCoeff g (center g E R) k H * y (.f k)‖ := by
        rw [← norm_mul]
        exact norm_add_le _ _
    _ ≤ K₄ * (1 / (g ^ 2 * W) + 1 / g ^ (2 * R + 2)) + t * (K₀ * (3 * w)) := by
        refine add_le_add h4 ?_
        rw [Complex.norm_real, Real.norm_of_nonneg ht0]
        refine mul_le_mul_of_nonneg_left (hcore.trans ?_) ht0
        exact mul_le_mul hNH hrate (by positivity) hK₀0
    _ ≤ (K₄ + 3 * K₀ + 1) * (w / g ^ 2 + 1 / (W * g ^ 2) + 1 / g ^ (2 * R + 2)) := by
        have e1 : t * (K₀ * (3 * w)) = 3 * K₀ * (w / g ^ 2) := by rw [ht]; field_simp
        have e2 : 1 / (g ^ 2 * W) = 1 / (W * g ^ 2) := by rw [mul_comm]
        rw [e1, e2]
        have hA : 0 ≤ w / g ^ 2 := by positivity
        have hB' : 0 ≤ 1 / ((W : ℝ) * g ^ 2) := by positivity
        have hC : 0 ≤ 1 / g ^ (2 * R + 2) := by positivity
        nlinarith [mul_nonneg hK₄.le hA, mul_nonneg hK₀0 hB', mul_nonneg hK₀0 hC]

end LSBA
