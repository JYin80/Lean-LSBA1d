import LSBA.Gauss.HeatGenerator
import LSBA.Flow.Comparison
import LSBA.Flow.Cutoff

/-!
# The no-exit lemma with multiplicative rates

For a nonnegative field `X` in the bounded `C^{1,2}` class along the Gaussian flow: if on good
sets and in the band `[0, J(1 + 2β)]` the drift and the carré du champ of `X` satisfy
`|Re 𝒢X| ≤ κX/(1−u)` and `0 ≤ Re Γ(X) ≤ bX²/(1−u)`, and off the good sets the generator of the
cutoffs is controlled in `L²`, then the cooperative system for `F = E ψ(X_u)`, `e = E Φ(X_u)` has
no additive source in the band, and `ℙ(X_v ≥ J(1 + β))` is bounded by the initial row amplified
by `R^{ρ′}` plus the off-set term; the multiplicative cutoff rows and the Perron root `ρ′`.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- Bracket coefficient `c₁₂` of the `ψ` row with the multiplicative bracket rate `Γ ≤ bx²/(1-u)`:
the cross term `ψ'χ'` and the curvature term `ψχ''` on `[J(1+β), J(1+2β)]`, where `Φ = 1`. -/
def rateMulC12 (ε β : ℝ) (r : ℕ) : ℝ :=
  2 * r * (1 + 2 * β) ^ (2 * r + 1) * (1 - ε)⁻¹ / β +
    3 * (1 + 2 * β) ^ (2 * r + 2) / (4 * ε * (1 - ε) * β ^ 2)

/-- Bracket coefficient `c₂₁` of the `Φ` row with the multiplicative bracket rate, on
`[J, J(1+β)]`, where `ψ ≥ 1`. -/
def rateMulC21 (ε β : ℝ) : ℝ := 3 * (1 + β) ^ 2 / (4 * ε * (1 - ε) * β ^ 2)

/-- Diagonal rate `a₁₁ = 2rκ + r(2r-1)b` of the cutoff system with multiplicative rates. -/
def rateMulA11 (κ b : ℝ) (r : ℕ) : ℝ := 2 * r * κ + r * (2 * r - 1) * b

/-- Off-diagonal rate `a₁₂ + c₁₂ b` of the cutoff system with multiplicative rates. -/
def rateMulA12 (ε β κ b : ℝ) (r : ℕ) : ℝ := rateA12 ε β κ r + rateMulC12 ε β r * b

/-- Off-diagonal rate `a₂₁ + c₂₁ b` of the cutoff system with multiplicative rates. -/
def rateMulA21 (ε β κ b : ℝ) : ℝ := rateA21 ε β κ + rateMulC21 ε β * b

/-- Perron root `ρ' = a₁₁/2 + √(a₁₁²/4 + a₁₂a₂₁)` of the cutoff system with multiplicative rates
(`a₂₂ = 0`). -/
def perronMul (ε β κ b : ℝ) (r : ℕ) : ℝ :=
  rateMulA11 κ b r / 2 +
    Real.sqrt ((rateMulA11 κ b r / 2) ^ 2 + rateMulA12 ε β κ b r * rateMulA21 ε β κ b)

section MulHelpers

variable {ε : ℝ} {ρ : ℝ → ℝ}

private theorem mul_iteratedDeriv_two (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

private theorem mul_hasDerivAt_affine {F F' : ℝ → ℝ} (hF : ∀ t, HasDerivAt F (F' t) t)
    (c d x : ℝ) : HasDerivAt (fun x => F ((x - c) / d)) (F' ((x - c) / d) / d) x := by
  have h : HasDerivAt (fun x : ℝ => (x - c) / d) (1 / d) x :=
    ((hasDerivAt_id' x).sub_const c).div_const d
  exact ((hF _).comp x h).congr_deriv (by ring)

private theorem mul_zero_of_lt {g : ℝ → ℝ} (hg : Continuous g) {a : ℝ}
    (h : ∀ y < a, g y = 0) : ∀ y ≤ a, g y = 0 := by
  have hc : closure (Set.Iio a) ⊆ {y | g y = 0} :=
    (isClosed_eq hg continuous_const).closure_subset_iff.2 fun y hy => h y hy
  intro y hy
  exact hc (by rw [closure_Iio]; exact hy)

private theorem mul_zero_of_gt {g : ℝ → ℝ} (hg : Continuous g) {a : ℝ}
    (h : ∀ y > a, g y = 0) : ∀ y ≥ a, g y = 0 := by
  have hc : closure (Set.Ioi a) ⊆ {y | g y = 0} :=
    (isClosed_eq hg continuous_const).closure_subset_iff.2 fun y hy => h y hy
  intro y hy
  exact hc (by rw [closure_Ioi]; exact hy)

private theorem IsRamp.hasDerivAt (hρ : IsRamp ε ρ) (y : ℝ) : HasDerivAt ρ (deriv ρ y) y :=
  ((hρ.smooth.differentiable (by norm_num)) y).hasDerivAt

private theorem IsRamp.contDiff_deriv (hρ : IsRamp ε ρ) : ContDiff ℝ 1 (deriv ρ) := by
  have h2 : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
  have h : ContDiff ℝ (1 + 1) ρ := by rw [← h2]; exact hρ.smooth
  exact (contDiff_succ_iff_deriv.1 h).2.2

private theorem IsRamp.hasDerivAt_deriv (hρ : IsRamp ε ρ) (y : ℝ) :
    HasDerivAt (deriv ρ) (iteratedDeriv 2 ρ y) y := by
  rw [mul_iteratedDeriv_two]
  exact ((hρ.contDiff_deriv.differentiable (by norm_num)) y).hasDerivAt

private theorem IsRamp.deriv_zero (hρ : IsRamp ε ρ) {y : ℝ} (h : y ≤ 0 ∨ 1 ≤ y) :
    deriv ρ y = 0 := by
  have hc : Continuous (deriv ρ) := hρ.contDiff_deriv.continuous
  rcases h with h | h
  · refine mul_zero_of_lt hc (fun z hz => ?_) y h
    have : ρ =ᶠ[𝓝 z] fun _ => 0 :=
      Filter.eventually_of_mem (Iio_mem_nhds hz) fun w hw => hρ.zero w (le_of_lt hw)
    rw [this.deriv_eq]; simp
  · refine mul_zero_of_gt hc (fun z hz => ?_) y h
    have : ρ =ᶠ[𝓝 z] fun _ => 1 :=
      Filter.eventually_of_mem (Ioi_mem_nhds hz) fun w hw => hρ.one w (le_of_lt hw)
    rw [this.deriv_eq]; simp

private theorem IsRamp.deriv2_zero (hρ : IsRamp ε ρ) {y : ℝ} (h : y ≤ 0 ∨ 1 ≤ y) :
    iteratedDeriv 2 ρ y = 0 := by
  have hc : Continuous (iteratedDeriv 2 ρ) := hρ.smooth.continuous_iteratedDeriv 2 (by norm_num)
  rw [mul_iteratedDeriv_two] at hc ⊢
  rcases h with h | h
  · refine mul_zero_of_lt hc (fun z hz => ?_) y h
    have : deriv ρ =ᶠ[𝓝 z] fun _ => 0 :=
      Filter.eventually_of_mem (Iio_mem_nhds hz) fun w hw => hρ.deriv_zero (Or.inl (le_of_lt hw))
    rw [this.deriv_eq]; simp
  · refine mul_zero_of_gt hc (fun z hz => ?_) y h
    have : deriv ρ =ᶠ[𝓝 z] fun _ => 0 :=
      Filter.eventually_of_mem (Ioi_mem_nhds hz) fun w hw => hρ.deriv_zero (Or.inr (le_of_lt hw))
    rw [this.deriv_eq]; simp

private theorem IsRamp.mono (hρ : IsRamp ε ρ) : Monotone ρ :=
  monotone_of_deriv_nonneg (hρ.smooth.differentiable (by norm_num)) fun x => (hρ.slope x).1

private theorem IsRamp.mem (hρ : IsRamp ε ρ) (x : ℝ) : 0 ≤ ρ x ∧ ρ x ≤ 1 := by
  constructor
  · rcases le_or_gt x 0 with h | h
    · rw [hρ.zero x h]
    · rw [← hρ.zero 0 le_rfl]; exact hρ.mono h.le
  · rcases le_or_gt 1 x with h | h
    · rw [hρ.one x h]
    · rw [← hρ.one 1 le_rfl]; exact hρ.mono h.le

private theorem mul_cutPhi_hasDerivAt (hρ : IsRamp ε ρ) (J β x : ℝ) :
    HasDerivAt (cutPhi ρ J β) (deriv ρ ((x - J) / (β * J)) / (β * J)) x :=
  mul_hasDerivAt_affine hρ.hasDerivAt J (β * J) x

private theorem mul_deriv_cutPhi (hρ : IsRamp ε ρ) (J β : ℝ) :
    deriv (cutPhi ρ J β) = fun x => deriv ρ ((x - J) / (β * J)) / (β * J) :=
  funext fun x => (mul_cutPhi_hasDerivAt hρ J β x).deriv

private theorem mul_cutPhi_hasDerivAt_deriv (hρ : IsRamp ε ρ) (J β x : ℝ) :
    HasDerivAt (deriv (cutPhi ρ J β))
      (iteratedDeriv 2 ρ ((x - J) / (β * J)) / (β * J) / (β * J)) x := by
  rw [mul_deriv_cutPhi hρ]
  exact (mul_hasDerivAt_affine hρ.hasDerivAt_deriv J (β * J) x).div_const (β * J)

private theorem mul_iteratedDeriv_two_cutPhi (hρ : IsRamp ε ρ) (J β x : ℝ) :
    iteratedDeriv 2 (cutPhi ρ J β) x =
      iteratedDeriv 2 ρ ((x - J) / (β * J)) / (β * J) / (β * J) := by
  rw [mul_iteratedDeriv_two]
  exact (mul_cutPhi_hasDerivAt_deriv hρ J β x).deriv

/-- Product rule with the derivative data of both factors. -/
private theorem mul_prod {f g f1 f2 g1 g2 : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f1 x) x) (hf1 : ∀ x, HasDerivAt f1 (f2 x) x)
    (hg : ∀ x, HasDerivAt g (g1 x) x) (hg1 : ∀ x, HasDerivAt g1 (g2 x) x) :
    (∀ x, HasDerivAt (fun x => f x * g x) (f1 x * g x + f x * g1 x) x) ∧
      (∀ x, HasDerivAt (fun x => f1 x * g x + f x * g1 x)
        (f2 x * g x + 2 * (f1 x * g1 x) + f x * g2 x) x) := by
  refine ⟨fun x => (hf x).mul (hg x), fun x => ?_⟩
  exact (((hf1 x).mul (hg x)).add ((hf x).mul (hg1 x))).congr_deriv (by ring)

/-- `(x/J)^{2r}`. -/
private def mulP (J : ℝ) (r : ℕ) (x : ℝ) : ℝ := (x / J) ^ (2 * r)

/-- Derivative of `(x/J)^{2r}`. -/
private def mulP1 (J : ℝ) (r : ℕ) (x : ℝ) : ℝ := 2 * r / J * (x / J) ^ (2 * r - 1)

/-- Second derivative of `(x/J)^{2r}`. -/
private def mulP2 (J : ℝ) (r : ℕ) (x : ℝ) : ℝ :=
  2 * r * (2 * r - 1) / J ^ 2 * (x / J) ^ (2 * r - 2)

/-- The window factor `χ = 1 − ρ((x − J(1+β))/(βJ))`. -/
private def mulChi (ρ : ℝ → ℝ) (J β x : ℝ) : ℝ := 1 - ρ ((x - J * (1 + β)) / (β * J))

/-- Derivative of the window factor. -/
private def mulChi1 (ρ : ℝ → ℝ) (J β x : ℝ) : ℝ :=
  -(deriv ρ ((x - J * (1 + β)) / (β * J)) / (β * J))

/-- Second derivative of the window factor. -/
private def mulChi2 (ρ : ℝ → ℝ) (J β x : ℝ) : ℝ :=
  -(iteratedDeriv 2 ρ ((x - J * (1 + β)) / (β * J)) / (β * J) / (β * J))

private theorem mul_hasDerivAt_P (J : ℝ) (r : ℕ) (x : ℝ) :
    HasDerivAt (mulP J r) (mulP1 J r x) x := by
  have h : HasDerivAt (fun x : ℝ => x / J) (1 / J) x := (hasDerivAt_id' x).div_const J
  refine ((hasDerivAt_pow (2 * r) (x / J)).comp x h).congr_deriv ?_
  unfold mulP1
  push_cast
  ring

private theorem mul_hasDerivAt_P1 (J : ℝ) {r : ℕ} (hr : 1 ≤ r) (x : ℝ) :
    HasDerivAt (mulP1 J r) (mulP2 J r x) x := by
  have h : HasDerivAt (fun x : ℝ => x / J) (1 / J) x := (hasDerivAt_id' x).div_const J
  refine (((hasDerivAt_pow (2 * r - 1) (x / J)).comp x h).const_mul (2 * r / J)).congr_deriv ?_
  unfold mulP2
  have e1 : 2 * r - 1 - 1 = 2 * r - 2 := by omega
  have e2 : ((2 * r - 1 : ℕ) : ℝ) = 2 * r - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [e1, e2]
  ring

private theorem mul_hasDerivAt_chi (hρ : IsRamp ε ρ) (J β x : ℝ) :
    HasDerivAt (mulChi ρ J β) (mulChi1 ρ J β x) x := by
  have := (mul_hasDerivAt_affine hρ.hasDerivAt (J * (1 + β)) (β * J) x)
  exact ((hasDerivAt_const x (1 : ℝ)).sub this).congr_deriv (by unfold mulChi1; ring)

private theorem mul_hasDerivAt_chi1 (hρ : IsRamp ε ρ) (J β x : ℝ) :
    HasDerivAt (mulChi1 ρ J β) (mulChi2 ρ J β x) x := by
  have := (mul_hasDerivAt_affine hρ.hasDerivAt_deriv (J * (1 + β)) (β * J) x).div_const (β * J)
  exact this.neg

private theorem mul_hasDerivAt_shift (hρ : IsRamp ε ρ) (x : ℝ) :
    HasDerivAt (fun x => ρ (x + 1)) (deriv ρ (x + 1)) x :=
  HasDerivAt.comp_add_const x 1 (hρ.hasDerivAt (x + 1))

private theorem mul_hasDerivAt_shift1 (hρ : IsRamp ε ρ) (x : ℝ) :
    HasDerivAt (fun x => deriv ρ (x + 1)) (iteratedDeriv 2 ρ (x + 1)) x :=
  HasDerivAt.comp_add_const x 1 (hρ.hasDerivAt_deriv (x + 1))

/-- Value, first and second derivative of `ψ` at `x ≥ 0`, where the factor `ρ(x+1)` has value `1`
and vanishing first and second derivatives. -/
private theorem mul_cutPsi_derivs (hρ : IsRamp ε ρ) (J β : ℝ) {r : ℕ} (hr : 1 ≤ r) {x : ℝ}
    (hx : 0 ≤ x) :
    cutPsi ρ J β r x = mulP J r x * mulChi ρ J β x ∧
    deriv (cutPsi ρ J β r) x = mulP1 J r x * mulChi ρ J β x +
      mulP J r x * mulChi1 ρ J β x ∧
    iteratedDeriv 2 (cutPsi ρ J β r) x = mulP2 J r x * mulChi ρ J β x +
      2 * (mulP1 J r x * mulChi1 ρ J β x) + mulP J r x * mulChi2 ρ J β x := by
  obtain ⟨hF, hF1⟩ := mul_prod (mul_hasDerivAt_P J r) (mul_hasDerivAt_P1 J hr)
    (mul_hasDerivAt_chi hρ J β) (mul_hasDerivAt_chi1 hρ J β)
  obtain ⟨hG, hG1⟩ := mul_prod (f := fun x => mulP J r x * mulChi ρ J β x)
    (f1 := fun x => mulP1 J r x * mulChi ρ J β x + mulP J r x * mulChi1 ρ J β x)
    (g := fun x => ρ (x + 1)) (g1 := fun x => deriv ρ (x + 1))
    (g2 := fun x => iteratedDeriv 2 ρ (x + 1)) hF hF1 (mul_hasDerivAt_shift hρ)
    (mul_hasDerivAt_shift1 hρ)
  have hψ : cutPsi ρ J β r = fun x => mulP J r x * mulChi ρ J β x * ρ (x + 1) := rfl
  have h1 : ρ (x + 1) = 1 := hρ.one _ (by linarith)
  have h2 : deriv ρ (x + 1) = 0 := hρ.deriv_zero (Or.inr (by linarith))
  have h3 : iteratedDeriv 2 ρ (x + 1) = 0 := hρ.deriv2_zero (Or.inr (by linarith))
  refine ⟨by rw [hψ]; simp only [h1, mul_one], ?_, ?_⟩
  · rw [hψ, (hG x).deriv, h1, h2]; ring
  · rw [mul_iteratedDeriv_two]
    have : deriv (cutPsi ρ J β r) = fun x =>
        (mulP1 J r x * mulChi ρ J β x + mulP J r x * mulChi1 ρ J β x) * ρ (x + 1) +
          mulP J r x * mulChi ρ J β x * deriv ρ (x + 1) :=
      funext fun x => (hG x).deriv
    rw [this, (hG1 x).deriv, h1, h2, h3]; ring

/-- Bounds for `(x/J)^{2r}` and its first two derivatives on `0 ≤ x ≤ J(1+2β)`, and the
identities `x P′ = 2r P`, `x² P″ = 2r(2r-1) P`. -/
private theorem mul_P_facts {J β x : ℝ} {r : ℕ} (hr : 1 ≤ r) (hJ : 0 < J)
    (hx : 0 ≤ x) (hxJ : x ≤ J * (1 + 2 * β)) :
    0 ≤ mulP J r x ∧ mulP J r x ≤ (1 + 2 * β) ^ (2 * r) ∧ 0 ≤ mulP1 J r x ∧
      mulP1 J r x ≤ 2 * r / J * (1 + 2 * β) ^ (2 * r - 1) ∧ 0 ≤ mulP2 J r x ∧
      mulP2 J r x ≤ 2 * r * (2 * r - 1) / J ^ 2 * (1 + 2 * β) ^ (2 * r - 2) ∧
      x * mulP1 J r x = 2 * r * mulP J r x ∧
      x ^ 2 * mulP2 J r x = 2 * r * (2 * r - 1) * mulP J r x := by
  have hq0 : 0 ≤ x / J := div_nonneg hx hJ.le
  have hq1 : x / J ≤ 1 + 2 * β := (div_le_iff₀ hJ).2 (by linarith)
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h2r : (0 : ℝ) ≤ 2 * r - 1 := by linarith
  have hc1 : 0 ≤ 2 * (r : ℝ) / J := by positivity
  have hc2 : 0 ≤ 2 * (r : ℝ) * (2 * r - 1) / J ^ 2 := by positivity
  refine ⟨pow_nonneg hq0 _, pow_le_pow_left₀ hq0 hq1 _, mul_nonneg hc1 (pow_nonneg hq0 _),
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0 hq1 _) hc1,
    mul_nonneg hc2 (pow_nonneg hq0 _), mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0 hq1 _) hc2,
    ?_, ?_⟩
  · unfold mulP1 mulP
    have : (x / J) ^ (2 * r) = (x / J) ^ (2 * r - 1) * (x / J) := by
      rw [← pow_succ]; congr 1; omega
    rw [this]
    field_simp
  · unfold mulP2 mulP
    have : (x / J) ^ (2 * r) = (x / J) ^ (2 * r - 2) * (x / J) ^ 2 := by
      rw [← pow_add]; congr 1; omega
    rw [this]
    field_simp

end MulHelpers

section MulRates

/-- The rate constants are nonnegative, and the off-diagonal ones positive for `κ > 0`. -/
private theorem mul_rates_nonneg {ε β κ bΓ : ℝ} (r : ℕ) (hr : 1 ≤ r) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1 / 2) (hβ : 0 < β) (hκ : 0 ≤ κ) (hbΓ : 0 ≤ bΓ) :
    0 ≤ rateMulC12 ε β r ∧ 0 ≤ rateMulC21 ε β ∧ 0 ≤ rateMulA11 κ bΓ r ∧ 0 ≤ rateA12 ε β κ r ∧
      0 ≤ rateA21 ε β κ := by
  have h1 : 0 < 1 - ε := by linarith
  have h2 : (0 : ℝ) ≤ 2 * r - 1 := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  unfold rateMulC12 rateMulC21 rateMulA11 rateA12 rateA21
  generalize 1 - ε = e at h1 ⊢
  generalize (2 * (r : ℝ) - 1) = t at h2 ⊢
  refine ⟨by positivity, by positivity, by positivity, by positivity, by positivity⟩

private theorem mul_rates_pos {ε β κ bΓ : ℝ} (r : ℕ) (hr : 1 ≤ r) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1 / 2) (hβ : 0 < β) (hκ : 0 < κ) (hbΓ : 0 ≤ bΓ) :
    0 < rateMulA12 ε β κ bΓ r ∧ 0 < rateMulA21 ε β κ bΓ := by
  have h1 : 0 < 1 - ε := by linarith
  obtain ⟨hC12, hC21, -, -, -⟩ := mul_rates_nonneg (κ := κ) (bΓ := bΓ) r hr hε0 hε1 hβ hκ.le hbΓ
  have h12 : 0 < rateA12 ε β κ r := by unfold rateA12; positivity
  have h21 : 0 < rateA21 ε β κ := by unfold rateA21; positivity
  exact ⟨by unfold rateMulA12; positivity, by unfold rateMulA21; positivity⟩

end MulRates

section MulRows

variable {ε : ℝ} {ρ : ℝ → ℝ}

/-- The `ψ` row of `cutoff_rates_mul` for `0 ≤ x ≤ J(1+2β)`, in terms of the Leibniz expansion. -/
private theorem mul_row_psi (hρ : IsRamp ε ρ) {J β κ bΓ u : ℝ} {r : ℕ}
    (hr : 1 ≤ r) (hJ : 0 < J) (hβ : 0 < β) (hκ : 0 ≤ κ) (hbΓ : 0 ≤ bΓ) (hu : u < 1)
    {x g Γ : ℝ} (hx : 0 ≤ x) (hxJ : x ≤ J * (1 + 2 * β))
    (hg : |g| ≤ κ * x / (1 - u)) (hΓ0 : 0 ≤ Γ) (hΓ : Γ ≤ bΓ * x ^ 2 / (1 - u)) :
    (mulP1 J r x * mulChi ρ J β x + mulP J r x * mulChi1 ρ J β x) * g +
        (mulP2 J r x * mulChi ρ J β x + 2 * (mulP1 J r x * mulChi1 ρ J β x) +
          mulP J r x * mulChi2 ρ J β x) / 2 * Γ ≤
      (rateMulA11 κ bΓ r * (mulP J r x * mulChi ρ J β x) +
        rateMulA12 ε β κ bΓ r * cutPhi ρ J β x) / (1 - u) := by
  obtain ⟨hε0, hε1⟩ := hρ.eps
  have hm : 0 < β * J := mul_pos hβ hJ
  have hw : 0 < 1 - u := by linarith
  have h1ε : 0 < 1 - ε := by linarith
  obtain ⟨hC12, hC21, hA11, hA12, hA21⟩ :=
    mul_rates_nonneg (κ := κ) (bΓ := bΓ) r hr hε0 hε1 hβ hκ hbΓ
  obtain ⟨hP0, hPle, hP10, hP1le, hP20, hP2le, hxP1, hx2P2⟩ := mul_P_facts (β := β) hr hJ hx hxJ
  have hΦ0 := (cutPhi_props hρ hJ hβ r x).1
  have hcurv : 0 ≤ 3 / (2 * ε * (1 - ε)) := le_trans (abs_nonneg _) (hρ.curv 0)
  have ha : 0 ≤ (1 - ε)⁻¹ := inv_nonneg.2 h1ε.le
  have hQ : 0 ≤ (1 + 2 * β) ^ (2 * r) := by positivity
  set P := mulP J r x with hPdef
  set P1 := mulP1 J r x with hP1def
  set P2 := mulP2 J r x with hP2def
  set y := (x - J * (1 + β)) / (β * J) with hy
  have hχ : mulChi ρ J β x = 1 - ρ y := rfl
  have hχ1 : mulChi1 ρ J β x = -(deriv ρ y / (β * J)) := rfl
  have hχ2 : mulChi2 ρ J β x = -(iteratedDeriv 2 ρ y / (β * J) / (β * J)) := rfl
  rw [hχ, hχ1, hχ2]
  obtain ⟨hρ0, hρ1⟩ := hρ.mem y
  obtain ⟨hD10, hD1a⟩ := hρ.slope y
  have hD2 := abs_le.1 (hρ.curv y)
  set D1 := deriv ρ y with hD1
  set D2 := iteratedDeriv 2 ρ y with hD2def
  set w := (1 - u)⁻¹ with hwdef
  have hw0 : 0 ≤ w := inv_nonneg.2 hw.le
  have hg' : |g| ≤ κ * x * w := by rw [← div_eq_mul_inv]; exact hg
  have hΓ' : Γ ≤ bΓ * x ^ 2 * w := by rw [← div_eq_mul_inv]; exact hΓ
  have hgle : g ≤ κ * x * w := (le_abs_self g).trans hg'
  have hngle : -g ≤ κ * x * w := (neg_le_abs g).trans hg'
  have hχ0 : 0 ≤ 1 - ρ y := by linarith
  have hc0 : 0 ≤ P * (D1 / (β * J)) := mul_nonneg hP0 (div_nonneg hD10 hm.le)
  have T1 : P1 * (1 - ρ y) * g ≤ 2 * r * κ * (P * (1 - ρ y)) * w := by
    have h := mul_le_mul_of_nonneg_left hgle (mul_nonneg hP10 hχ0)
    have e : P1 * (1 - ρ y) * (κ * x * w) = 2 * r * κ * (P * (1 - ρ y)) * w := by
      linear_combination ((1 - ρ y) * κ * w) * hxP1
    linarith
  have T2 : P * -(D1 / (β * J)) * g ≤ P * (D1 / (β * J)) * (κ * x * w) := by
    have h := mul_le_mul_of_nonneg_left hngle hc0
    calc P * -(D1 / (β * J)) * g = P * (D1 / (β * J)) * (-g) := by ring
      _ ≤ P * (D1 / (β * J)) * (κ * x * w) := h
  have hΦ1 : 0 < y → cutPhi ρ J β x = 1 := by
    intro hy0
    have : (x - J) / (β * J) = y + 1 := by rw [hy]; field_simp; ring
    change ρ ((x - J) / (β * J)) = 1
    rw [this]; exact hρ.one _ (by linarith)
  have E2 : P * (D1 / (β * J)) * (κ * x) ≤ rateA12 ε β κ r * cutPhi ρ J β x := by
    rcases le_or_gt y 0 with hy0 | hy0
    · have : D1 = 0 := hρ.deriv_zero (Or.inl hy0)
      rw [this]
      simpa using mul_nonneg hA12 hΦ0
    · rw [hΦ1 hy0, mul_one]
      have hxa := mul_le_mul hPle hD1a hD10 hQ
      have hxb : κ * x ≤ κ * (J * (1 + 2 * β)) := mul_le_mul_of_nonneg_left hxJ hκ
      have hxc := mul_le_mul hxa hxb (mul_nonneg hκ hx) (mul_nonneg hQ ha)
      calc P * (D1 / (β * J)) * (κ * x) = P * D1 * (κ * x) / (β * J) := by ring
        _ ≤ (1 + 2 * β) ^ (2 * r) * (1 - ε)⁻¹ * (κ * (J * (1 + 2 * β))) / (β * J) :=
          div_le_div_of_nonneg_right hxc hm.le
        _ = rateA12 ε β κ r := by unfold rateA12; rw [pow_succ]; field_simp
  have E2w := mul_le_mul_of_nonneg_right E2 hw0
  have T3 : P2 * (1 - ρ y) / 2 * Γ ≤ r * (2 * r - 1) * bΓ * (P * (1 - ρ y)) * w := by
    have h := mul_le_mul_of_nonneg_left hΓ'
      (div_nonneg (mul_nonneg hP20 hχ0) (by norm_num : (0 : ℝ) ≤ 2))
    have e : P2 * (1 - ρ y) / 2 * (bΓ * x ^ 2 * w) =
        r * (2 * r - 1) * bΓ * (P * (1 - ρ y)) * w := by
      linear_combination ((1 - ρ y) * bΓ * w / 2) * hx2P2
    linarith
  have T4 : 2 * (P1 * -(D1 / (β * J))) / 2 * Γ ≤ 0 := by
    have : 0 ≤ P1 * (D1 / (β * J)) := mul_nonneg hP10 (div_nonneg hD10 hm.le)
    have h2 : 0 ≤ P1 * (D1 / (β * J)) * Γ := mul_nonneg this hΓ0
    have e : 2 * (P1 * -(D1 / (β * J))) / 2 * Γ = -(P1 * (D1 / (β * J)) * Γ) := by ring
    linarith
  have hS2 : 0 ≤ 3 * (1 + 2 * β) ^ (2 * r + 2) / (4 * ε * (1 - ε) * β ^ 2) := by positivity
  have T5 : P * -(D2 / (β * J) / (β * J)) / 2 * Γ ≤
      3 * (1 + 2 * β) ^ (2 * r + 2) / (4 * ε * (1 - ε) * β ^ 2) * bΓ * cutPhi ρ J β x * w := by
    rcases le_or_gt y 0 with hy0 | hy0
    · have : D2 = 0 := hρ.deriv2_zero (Or.inl hy0)
      rw [this]
      simp only [zero_div, neg_zero, mul_zero, zero_mul]
      positivity
    · rcases le_or_gt 1 y with hy1 | hy1
      · have : D2 = 0 := hρ.deriv2_zero (Or.inr hy1)
        rw [this]
        simp only [zero_div, neg_zero, mul_zero, zero_mul]
        positivity
      · rw [hΦ1 hy0, mul_one]
        set K := 3 / (2 * ε * (1 - ε)) / (β * J) ^ 2 / 2 with hK
        have hK0 : 0 ≤ K := by positivity
        have hv : -(D2 / (β * J) / (β * J)) / 2 ≤ K := by
          have : -(D2 / (β * J) / (β * J)) / 2 = (-D2) / (β * J) ^ 2 / 2 := by ring
          rw [this, hK]
          exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right
            (by linarith [hD2.2]) (sq_nonneg _)) (by norm_num)
        have h1 : P * -(D2 / (β * J) / (β * J)) / 2 ≤ (1 + 2 * β) ^ (2 * r) * K := by
          calc P * -(D2 / (β * J) / (β * J)) / 2 = P * (-(D2 / (β * J) / (β * J)) / 2) := by ring
            _ ≤ P * K := mul_le_mul_of_nonneg_left hv hP0
            _ ≤ (1 + 2 * β) ^ (2 * r) * K := mul_le_mul_of_nonneg_right hPle hK0
        have hx2 : x ^ 2 ≤ (J * (1 + 2 * β)) ^ 2 := pow_le_pow_left₀ hx hxJ 2
        have h2 : bΓ * x ^ 2 * w ≤ bΓ * (J * (1 + 2 * β)) ^ 2 * w :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx2 hbΓ) hw0
        calc P * -(D2 / (β * J) / (β * J)) / 2 * Γ
            ≤ (1 + 2 * β) ^ (2 * r) * K * (bΓ * x ^ 2 * w) :=
              mul_le_mul h1 hΓ' hΓ0 (mul_nonneg hQ hK0)
          _ ≤ (1 + 2 * β) ^ (2 * r) * K * (bΓ * (J * (1 + 2 * β)) ^ 2 * w) :=
              mul_le_mul_of_nonneg_left h2 (mul_nonneg hQ hK0)
          _ = 3 * (1 + 2 * β) ^ (2 * r + 2) / (4 * ε * (1 - ε) * β ^ 2) * bΓ * w := by
              rw [hK]; field_simp; ring
  have hS1 : 0 ≤ 2 * r * (1 + 2 * β) ^ (2 * r + 1) * (1 - ε)⁻¹ / β * bΓ * cutPhi ρ J β x * w := by
    positivity
  have hdiv : ∀ t : ℝ, t / (1 - u) = t * w := fun t => div_eq_mul_inv t _
  rw [hdiv]
  unfold rateMulA11 rateMulA12 rateMulC12
  linarith [T1, T2, E2w, T3, T4, T5, hS1]

/-- The `Φ` row of `cutoff_rates_mul` for `x ≥ 0`, in terms of the derivatives of the ramp. -/
private theorem mul_row_phi (hρ : IsRamp ε ρ) {J β κ bΓ u : ℝ} {r : ℕ}
    (hr : 1 ≤ r) (hJ : 0 < J) (hβ : 0 < β) (hκ : 0 ≤ κ) (hbΓ : 0 ≤ bΓ) (hu : u < 1)
    {x g Γ : ℝ} (hx : 0 ≤ x) (hg : x ≤ J * (1 + 2 * β) → |g| ≤ κ * x / (1 - u))
    (hΓ0 : 0 ≤ Γ) (hΓ : x ≤ J * (1 + 2 * β) → Γ ≤ bΓ * x ^ 2 / (1 - u)) :
    deriv ρ ((x - J) / (β * J)) / (β * J) * g +
        iteratedDeriv 2 ρ ((x - J) / (β * J)) / (β * J) / (β * J) / 2 * Γ ≤
      rateMulA21 ε β κ bΓ * (mulP J r x * mulChi ρ J β x) / (1 - u) := by
  obtain ⟨hε0, hε1⟩ := hρ.eps
  have hm : 0 < β * J := mul_pos hβ hJ
  have hw : 0 < 1 - u := by linarith
  have h1ε : 0 < 1 - ε := by linarith
  obtain ⟨hC12, hC21, hA11, hA12, hA21⟩ :=
    mul_rates_nonneg (κ := κ) (bΓ := bΓ) r hr hε0 hε1 hβ hκ hbΓ
  have hcurv : 0 ≤ 3 / (2 * ε * (1 - ε)) := le_trans (abs_nonneg _) (hρ.curv 0)
  have ha : 0 ≤ (1 - ε)⁻¹ := inv_nonneg.2 h1ε.le
  have hP0 : 0 ≤ mulP J r x := pow_nonneg (div_nonneg hx hJ.le) _
  have hχ : mulChi ρ J β x = 1 - ρ ((x - J * (1 + β)) / (β * J)) := rfl
  have hχ0 : 0 ≤ mulChi ρ J β x := by
    rw [hχ]; linarith [(hρ.mem ((x - J * (1 + β)) / (β * J))).2]
  have hdiv : ∀ t : ℝ, t / (1 - u) = t * (1 - u)⁻¹ := fun t => div_eq_mul_inv t _
  have hw0 : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 hw.le
  have hA21' : 0 ≤ rateMulA21 ε β κ bΓ := by
    unfold rateMulA21; positivity
  rw [hdiv]
  by_cases hzc : (x - J) / (β * J) ≤ 0 ∨ 1 ≤ (x - J) / (β * J)
  · rw [hρ.deriv_zero hzc, hρ.deriv2_zero hzc]
    have : 0 ≤ rateMulA21 ε β κ bΓ * (mulP J r x * mulChi ρ J β x) * (1 - u)⁻¹ :=
      mul_nonneg (mul_nonneg hA21' (mul_nonneg hP0 hχ0)) hw0
    simp only [zero_div, zero_mul, add_zero]
    linarith
  · push Not at hzc
    obtain ⟨hz0, hz1⟩ := hzc
    have hx1 : 0 < x - J := by simpa using (lt_div_iff₀ hm).1 hz0
    have hx2 : x - J < β * J := by simpa using (div_lt_iff₀ hm).1 hz1
    have hxJ : x ≤ J * (1 + 2 * β) := by nlinarith
    have hxb : x ≤ J * (1 + β) := by nlinarith
    have hyz : (x - J * (1 + β)) / (β * J) = (x - J) / (β * J) - 1 := by field_simp; ring
    have hρy : ρ ((x - J * (1 + β)) / (β * J)) = 0 := hρ.zero _ (by rw [hyz]; linarith)
    have hχ1 : mulChi ρ J β x = 1 := by rw [hχ, hρy]; norm_num
    have hP1 : 1 ≤ mulP J r x :=
      one_le_pow₀ ((le_div_iff₀ hJ).2 (by linarith))
    obtain ⟨hD10, hD1a⟩ := hρ.slope ((x - J) / (β * J))
    have hD2 := abs_le.1 (hρ.curv ((x - J) / (β * J)))
    set D1 := deriv ρ ((x - J) / (β * J)) with hD1
    set D2 := iteratedDeriv 2 ρ ((x - J) / (β * J)) with hD2def
    set w := (1 - u)⁻¹ with hwdef
    have hg' : |g| ≤ κ * x * w := by rw [← div_eq_mul_inv]; exact hg hxJ
    have hΓ' : Γ ≤ bΓ * x ^ 2 * w := by rw [← div_eq_mul_inv]; exact hΓ hxJ
    have hgle : g ≤ κ * x * w := (le_abs_self g).trans hg'
    have T := mul_le_mul_of_nonneg_left hgle (div_nonneg hD10 hm.le)
    have E1 : D1 / (β * J) * (κ * x) ≤ rateA21 ε β κ := by
      calc D1 / (β * J) * (κ * x) = D1 * (κ * x) / (β * J) := by ring
        _ ≤ (1 - ε)⁻¹ * (κ * (J * (1 + β))) / (β * J) :=
          div_le_div_of_nonneg_right
            (mul_le_mul hD1a (mul_le_mul_of_nonneg_left hxb hκ) (mul_nonneg hκ hx) ha) hm.le
        _ = rateA21 ε β κ := by unfold rateA21; field_simp
    have E1w : D1 / (β * J) * (κ * x * w) ≤ rateA21 ε β κ * w := by
      calc D1 / (β * J) * (κ * x * w) = D1 / (β * J) * (κ * x) * w := by ring
        _ ≤ rateA21 ε β κ * w := mul_le_mul_of_nonneg_right E1 hw0
    set K := 3 / (2 * ε * (1 - ε)) / (β * J) ^ 2 / 2 with hK
    have hK0 : 0 ≤ K := by positivity
    have hv : D2 / (β * J) / (β * J) / 2 ≤ K := by
      have : D2 / (β * J) / (β * J) / 2 = D2 / (β * J) ^ 2 / 2 := by ring
      rw [this, hK]
      exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hD2.2 (sq_nonneg _))
        (by norm_num)
    have hx2' : x ^ 2 ≤ (J * (1 + β)) ^ 2 := pow_le_pow_left₀ hx hxb 2
    have h2 : bΓ * x ^ 2 * w ≤ bΓ * (J * (1 + β)) ^ 2 * w :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx2' hbΓ) hw0
    have E3 : D2 / (β * J) / (β * J) / 2 * Γ ≤ rateMulC21 ε β * bΓ * w := by
      calc D2 / (β * J) / (β * J) / 2 * Γ ≤ K * (bΓ * x ^ 2 * w) :=
            mul_le_mul hv hΓ' hΓ0 hK0
        _ ≤ K * (bΓ * (J * (1 + β)) ^ 2 * w) := mul_le_mul_of_nonneg_left h2 hK0
        _ = rateMulC21 ε β * bΓ * w := by
            rw [hK]; unfold rateMulC21; field_simp; ring
    have hA : 0 ≤ rateA21 ε β κ + rateMulC21 ε β * bΓ := by
      have := mul_nonneg hC21 hbΓ
      linarith
    have hfin : (rateA21 ε β κ + rateMulC21 ε β * bΓ) * w ≤
        (rateA21 ε β κ + rateMulC21 ε β * bΓ) * mulP J r x * w :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hA hP1) hw0
    rw [hχ1, mul_one]
    unfold rateMulA21
    linarith [T, E1w, E3, hfin]

end MulRows

/-- Pointwise cutoff rates with multiplicative band rates: `|g| ≤ κx/(1-u)` and
`0 ≤ Γ ≤ bx²/(1-u)` on `[0, J(1+2β)]` give the two rows of the cooperative system without
additive sources. -/
theorem cutoff_rates_mul {ε : ℝ} {ρ : ℝ → ℝ} (hρ : IsRamp ε ρ) {J β κ bΓ u : ℝ} (r : ℕ)
    (hr : 1 ≤ r) (hJ : 0 < J) (hβ : 0 < β) (hκ : 0 ≤ κ) (hbΓ : 0 ≤ bΓ) (hu : u < 1)
    {x g Γ : ℝ} (hx : 0 ≤ x) (hg : x ≤ J * (1 + 2 * β) → |g| ≤ κ * x / (1 - u))
    (hΓ0 : 0 ≤ Γ) (hΓ : x ≤ J * (1 + 2 * β) → Γ ≤ bΓ * x ^ 2 / (1 - u)) :
    deriv (cutPsi ρ J β r) x * g + iteratedDeriv 2 (cutPsi ρ J β r) x / 2 * Γ ≤
        (rateMulA11 κ bΓ r * cutPsi ρ J β r x + rateMulA12 ε β κ bΓ r * cutPhi ρ J β x) /
          (1 - u) ∧
      deriv (cutPhi ρ J β) x * g + iteratedDeriv 2 (cutPhi ρ J β) x / 2 * Γ ≤
        rateMulA21 ε β κ bΓ * cutPsi ρ J β r x / (1 - u) := by
  obtain ⟨hε0, hε1⟩ := hρ.eps
  have hm : 0 < β * J := mul_pos hβ hJ
  have hw : 0 < 1 - u := by linarith
  obtain ⟨hψv, hψ1, hψ2⟩ := mul_cutPsi_derivs hρ J β hr hx
  have e1 : deriv (cutPhi ρ J β) x = deriv ρ ((x - J) / (β * J)) / (β * J) := by
    rw [mul_deriv_cutPhi hρ]
  rw [hψ1, hψ2, hψv, e1, mul_iteratedDeriv_two_cutPhi hρ J β x]
  refine ⟨?_, mul_row_phi hρ hr hJ hβ hκ hbΓ hu hx hg hΓ0 hΓ⟩
  rcases lt_or_ge x (J * (1 + 2 * β)) with hlt | hge
  · exact mul_row_psi hρ hr hJ hβ hκ hbΓ hu hx hlt.le (hg hlt.le) hΓ0 (hΓ hlt.le)
  · obtain ⟨hC12, hC21, hA11, hA12, hA21⟩ :=
      mul_rates_nonneg (κ := κ) (bΓ := bΓ) r hr hε0 hε1 hβ hκ hbΓ
    have hΦ0 := (cutPhi_props hρ hJ hβ r x).1
    have hy : 1 ≤ (x - J * (1 + β)) / (β * J) := (le_div_iff₀ hm).2 (by nlinarith)
    have hρy : ρ ((x - J * (1 + β)) / (β * J)) = 1 := hρ.one _ hy
    have hD1 : deriv ρ ((x - J * (1 + β)) / (β * J)) = 0 := hρ.deriv_zero (Or.inr hy)
    have hD2 : iteratedDeriv 2 ρ ((x - J * (1 + β)) / (β * J)) = 0 := hρ.deriv2_zero (Or.inr hy)
    have hχ : mulChi ρ J β x = 0 := by unfold mulChi; rw [hρy]; norm_num
    have hχ1 : mulChi1 ρ J β x = 0 := by unfold mulChi1; rw [hD1]; simp
    have hχ2 : mulChi2 ρ J β x = 0 := by unfold mulChi2; rw [hD2]; simp
    rw [hχ, hχ1, hχ2]
    have hA12' : 0 ≤ rateMulA12 ε β κ bΓ r := by unfold rateMulA12; positivity
    have h1 : 0 ≤ (rateMulA11 κ bΓ r * (mulP J r x * 0) + rateMulA12 ε β κ bΓ r * cutPhi ρ J β x) /
        (1 - u) :=
      div_nonneg (by rw [mul_zero, mul_zero, zero_add]; exact mul_nonneg hA12' hΦ0) hw.le
    linarith [h1]

section MulFlow

/-- A function equal to a constant near `x` has vanishing first and second derivative at `x`. -/
private theorem mul_deriv_zero {f : ℝ → ℝ} {x c : ℝ} (hf : f =ᶠ[𝓝 x] fun _ => c) :
    deriv f x = 0 ∧ iteratedDeriv 2 f x = 0 := by
  have h1 : deriv f =ᶠ[𝓝 x] deriv (fun _ : ℝ => c) := hf.deriv
  refine ⟨by rw [hf.deriv_eq, deriv_const], ?_⟩
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1.deriv_eq]
  simp

/-- The carré du champ `Γ(F, F)` has nonnegative real part for `σ² ≥ 0`. -/
private theorem mul_gamma_nonneg {ι : Type*} [Fintype ι] {σ2 : ℝ} (hσ2 : 0 ≤ σ2)
    (f : (ι → ℝ) → ℂ) (y : ι → ℝ) : 0 ≤ (coordGamma σ2 f f y).re := by
  unfold coordGamma
  rw [Complex.re_ofReal_mul, Complex.re_sum]
  refine mul_nonneg hσ2 (Finset.sum_nonneg fun i _ => ?_)
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

/-- At a time `u` inside the class interval, a real field in the class is continuous and `C²` in
space and differentiable in time. -/
private theorem mul_slice {ι : Type*} [Fintype ι] {X : ℝ → (ι → ℝ) → ℝ} {a b : ℝ}
    (hX : HeatClass (fun r y => ((X r y : ℝ) : ℂ)) a b) {u : ℝ} (hu : u ∈ Set.Ioo a b) :
    ContDiff ℝ 2 (X u) ∧ ∀ y, DifferentiableAt ℝ (fun r => X r y) u := by
  obtain ⟨-, -, ⟨Fu, hFu, -, -⟩, ⟨DF, D2F, hD, hD2, -, hcD2, -⟩⟩ := hX
  have hc2 : Continuous (D2F u) :=
    hcD2.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hu, trivial⟩
  have h1 : ContDiff ℝ 1 (DF u) := contDiff_one_iff_hasFDerivAt.2 ⟨D2F u, hc2, hD2 u hu⟩
  have h2 : ContDiff ℝ (1 + 1) (fun y => ((X u y : ℝ) : ℂ)) :=
    contDiff_succ_iff_hasFDerivAt (n := 1).2 ⟨DF u, h1, hD u hu⟩
  have h3 : ContDiff ℝ 2 (X u) := by
    have := Complex.reCLM.contDiff.comp h2
    simp only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re,
      one_add_one_eq_two] at this
    exact this
  refine ⟨h3, fun y => ?_⟩
  have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u (hFu u hu y)
  simpa [Function.comp_def] using this.differentiableAt

/-- Real part of the chain rule `𝒢(φ ∘ X) = φ'(X) 𝒢X + ½ φ''(X) Γ(X)`. -/
private theorem mul_gen_re {ι : Type*} [Fintype ι] (σ2 : ℝ) {X : ℝ → (ι → ℝ) → ℝ}
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) {u : ℝ} {y : ι → ℝ}
    (hXu : DifferentiableAt ℝ (fun r => X r y) u) (hXy : ContDiff ℝ 2 (X u)) :
    (coordGen σ2 (fun t z => ((φ (X t z) : ℝ) : ℂ)) u y).re =
      deriv φ (X u y) * (coordGen σ2 (fun t z => ((X t z : ℝ) : ℂ)) u y).re +
        iteratedDeriv 2 φ (X u y) / 2 *
          (coordGamma σ2 (fun z => ((X u z : ℝ) : ℂ)) (fun z => ((X u z : ℝ) : ℂ)) y).re := by
  rw [coordGen_comp σ2 φ hφ X u y hXu hXy, Complex.add_re, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul]

/-- A `C²_b` function of a continuous map is integrable for the standard Gaussian. -/
private theorem mul_integrable {ι : Type*} [Fintype ι] {φ : ℝ → ℝ} (hφ : C2b φ)
    {g : (ι → ℝ) → ℝ} (hg : Continuous g) : Integrable (fun x => φ (g x)) (stdGauss ι) := by
  obtain ⟨hc, C, hC⟩ := hφ
  exact Integrable.of_bound (hc.continuous.comp hg).aestronglyMeasurable C
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using (hC (g x)).1)

/-- One row of the cutoff system: a bound `B(X)` on the good set `G` and an integrated off-set
term `≤ K_off` give `Re E 𝒢(φ ∘ X) ≤ E B(X) + K_off`. -/
private theorem mul_row {ι : Type*} [Fintype ι] (σ2 : ℝ) (X : ℝ → (ι → ℝ) → ℝ) (u : ℝ)
    {G : Set (ι → ℝ)} (hG : MeasurableSet G) (φ B : ℝ → ℝ) {Koff : ℝ} (hKoff : 0 ≤ Koff)
    (hB : Integrable (fun x => B (X u (Real.sqrt (u * σ2) • x))) (stdGauss ι))
    (hB0 : ∀ t, 0 ≤ B t)
    (hgood : ∀ y ∈ G, (coordGen σ2 (fun t z => ((φ (X t z) : ℝ) : ℂ)) u y).re ≤ B (X u y))
    (hoff : ∫ x, Set.indicator {x | Real.sqrt (u * σ2) • x ∉ G}
          (fun x => |(coordGen σ2 (fun t z => ((φ (X t z) : ℝ) : ℂ)) u
            (Real.sqrt (u * σ2) • x)).re|) x ∂(stdGauss ι) ≤ Koff) :
    (∫ x, coordGen σ2 (fun t z => ((φ (X t z) : ℝ) : ℂ)) u (Real.sqrt (u * σ2) • x)
        ∂(stdGauss ι)).re ≤
      ∫ x, B (X u (Real.sqrt (u * σ2) • x)) ∂(stdGauss ι) + Koff := by
  set S := {x : ι → ℝ | Real.sqrt (u * σ2) • x ∉ G} with hSdef
  have hS : MeasurableSet S := hG.compl.preimage (measurable_const_smul _)
  set f : (ι → ℝ) → ℂ := fun x =>
    coordGen σ2 (fun t z => ((φ (X t z) : ℝ) : ℂ)) u (Real.sqrt (u * σ2) • x) with hf
  have hB1 : 0 ≤ ∫ x, B (X u (Real.sqrt (u * σ2) • x)) ∂(stdGauss ι) :=
    integral_nonneg fun x => hB0 _
  by_cases hfi : Integrable f (stdGauss ι)
  · have hre : Integrable (fun x => (f x).re) (stdGauss ι) := hfi.re
    have habs : Integrable (S.indicator (fun x => |(f x).re|)) (stdGauss ι) :=
      hre.abs.indicator hS
    have key : (∫ x, f x ∂(stdGauss ι)).re ≤
        ∫ x, (B (X u (Real.sqrt (u * σ2) • x)) + S.indicator (fun x => |(f x).re|) x)
          ∂(stdGauss ι) := by
      have := integral_re hfi
      simp only [RCLike.re_to_complex] at this
      rw [← this]
      refine integral_mono hfi.re (hB.add habs) fun x => ?_
      by_cases hx : Real.sqrt (u * σ2) • x ∈ G
      · have hxS : x ∉ S := fun h => h hx
        simp only [Set.indicator_of_notMem hxS, add_zero]
        exact hgood _ hx
      · have hxS : x ∈ S := hx
        simp only [Set.indicator_of_mem hxS]
        linarith [le_abs_self (f x).re, hB0 (X u (Real.sqrt (u * σ2) • x))]
    rw [integral_add hB habs] at key
    linarith
  · rw [integral_undef hfi, Complex.zero_re]
    linarith

end MulFlow

/-- No-exit lemma with multiplicative band rates: for a nonnegative field `X` in the bounded
`C^{1,2}` class, `|Re 𝒢X| ≤ κX/(1-u)` and `Re Γ(X) ≤ bX²/(1-u)` on the good sets inside the band
`[0, J(1+2β)]`, and an integrated off-set term `E|Re 𝒢(φ ∘ X)| 1_{bad} ≤ K_off` for
`φ ∈ {ψ, Φ}`, give `ℙ(X_v ≥ J(1+β)) ≤ E Φ(X_v)` and
`F(v) + λe(v) ≤ ((1-s)/(1-v))^{ρ'} (F(s) + λe(s) + (v-s)(1+λ)K_off)`, `λ = a₁₂'/ρ'`. -/
theorem noExit' {ι : Type*} [Fintype ι] (σ2 : ℝ) (hσ2 : 0 ≤ σ2) (X : ℝ → (ι → ℝ) → ℝ)
    {a b s v : ℝ} (ha : a < 0) (hs : 0 ≤ s) (hsv : s < v) (hvb : v < b) (hv1 : v < 1)
    (hX : HeatClass (fun r y => ((X r y : ℝ) : ℂ)) a b) (hX0 : ∀ r y, 0 ≤ X r y)
    {ε : ℝ} {ρ : ℝ → ℝ} (hρ : IsRamp ε ρ) {J β κ bΓ Koff : ℝ} (r : ℕ) (hr : 1 ≤ r) (hJ : 0 < J)
    (hβ : 0 < β) (hκ : 0 < κ) (hbΓ : 0 ≤ bΓ) (hKoff : 0 ≤ Koff) (G : ℝ → Set (ι → ℝ))
    (hGm : ∀ u, MeasurableSet (G u))
    (hrate : ∀ u ∈ Set.Ioo s v, ∀ y ∈ G u, X u y ≤ J * (1 + 2 * β) →
      |(coordGen σ2 (fun t z => ((X t z : ℝ) : ℂ)) u y).re| ≤ κ * X u y / (1 - u) ∧
        (coordGamma σ2 (fun z => ((X u z : ℝ) : ℂ)) (fun z => ((X u z : ℝ) : ℂ)) y).re ≤
          bΓ * X u y ^ 2 / (1 - u))
    (hoff : ∀ u ∈ Set.Ioo s v,
      ∫ x, Set.indicator {x | Real.sqrt (u * σ2) • x ∉ G u}
          (fun x => |(coordGen σ2 (fun t z => ((cutPsi ρ J β r (X t z) : ℝ) : ℂ)) u
            (Real.sqrt (u * σ2) • x)).re|) x ∂(stdGauss ι) ≤ Koff ∧
        ∫ x, Set.indicator {x | Real.sqrt (u * σ2) • x ∉ G u}
          (fun x => |(coordGen σ2 (fun t z => ((cutPhi ρ J β (X t z) : ℝ) : ℂ)) u
            (Real.sqrt (u * σ2) • x)).re|) x ∂(stdGauss ι) ≤ Koff) :
    stdGauss ι {x | J * (1 + β) ≤ X v (Real.sqrt (v * σ2) • x)} ≤
        ENNReal.ofReal (∫ x, cutPhi ρ J β (X v (Real.sqrt (v * σ2) • x)) ∂(stdGauss ι)) ∧
      (∫ x, cutPsi ρ J β r (X v (Real.sqrt (v * σ2) • x)) ∂(stdGauss ι)) +
          rateMulA12 ε β κ bΓ r / perronMul ε β κ bΓ r *
            ∫ x, cutPhi ρ J β (X v (Real.sqrt (v * σ2) • x)) ∂(stdGauss ι) ≤
        ((1 - s) / (1 - v)) ^ perronMul ε β κ bΓ r *
          ((∫ x, cutPsi ρ J β r (X s (Real.sqrt (s * σ2) • x)) ∂(stdGauss ι)) +
            rateMulA12 ε β κ bΓ r / perronMul ε β κ bΓ r *
              (∫ x, cutPhi ρ J β (X s (Real.sqrt (s * σ2) • x)) ∂(stdGauss ι)) +
            (v - s) * ((1 + rateMulA12 ε β κ bΓ r / perronMul ε β κ bΓ r) * Koff)) := by
  obtain ⟨hε0, hε1⟩ := hρ.eps
  have hψ := cutPsi_C2b hρ hJ hβ r
  have hΦ := cutPhi_C2b hρ hJ hβ
  have hpos := cutPhi_props hρ hJ hβ r
  obtain ⟨hA12, hA21⟩ := mul_rates_pos (κ := κ) (bΓ := bΓ) r hr hε0 hε1 hβ hκ hbΓ
  obtain ⟨-, -, hA11, -, -⟩ := mul_rates_nonneg (κ := κ) (bΓ := bΓ) r hr hε0 hε1 hβ hκ.le hbΓ
  have hsub : ∀ u ∈ Set.Icc s v, u ∈ Set.Ioo a b := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hcont : ∀ u ∈ Set.Icc s v,
      Continuous (fun x : ι → ℝ => X u (Real.sqrt (u * σ2) • x)) := fun u hu =>
    (mul_slice hX (hsub u hu)).1.continuous.comp (continuous_const_smul _)
  -- beyond `J(1+2β)` both cutoffs are locally constant
  have hfar : ∀ t, J * (1 + 2 * β) < t →
      (deriv (cutPsi ρ J β r) t = 0 ∧ iteratedDeriv 2 (cutPsi ρ J β r) t = 0) ∧
        (deriv (cutPhi ρ J β) t = 0 ∧ iteratedDeriv 2 (cutPhi ρ J β) t = 0) := by
    intro t ht
    have hev : ∀ᶠ z in 𝓝 t, J * (1 + 2 * β) < z := lt_mem_nhds ht
    refine ⟨mul_deriv_zero (c := 0) ?_, mul_deriv_zero (c := 1) ?_⟩
    · filter_upwards [hev] with z hz
      have hy : 1 ≤ (z - J * (1 + β)) / (β * J) :=
        (le_div_iff₀ (mul_pos hβ hJ)).2 (by nlinarith)
      simp [cutPsi, hρ.one _ hy]
    · filter_upwards [hev] with z hz
      exact (hpos z).2.2.1 (by nlinarith)
  -- the generator identity for `ψ ∘ X` and `Φ ∘ X`
  have hgψ := heat_generator σ2 hσ2 (fun t z => ((cutPsi ρ J β r (X t z) : ℝ) : ℂ)) ha
    (hs.trans hsv.le) hvb (hX.comp_real hψ)
  have hgΦ := heat_generator σ2 hσ2 (fun t z => ((cutPhi ρ J β (X t z) : ℝ) : ℂ)) ha
    (hs.trans hsv.le) hvb (hX.comp_real hΦ)
  have hIcc : Set.Icc s v ⊆ Set.Icc 0 v := Set.Icc_subset_Icc hs le_rfl
  have hFc : ContinuousOn
      (fun u => ∫ x, cutPsi ρ J β r (X u (Real.sqrt (u * σ2) • x)) ∂(stdGauss ι))
      (Set.Icc s v) := by
    have := Complex.continuous_re.comp_continuousOn (hgψ.1.mono hIcc)
    simpa only [Function.comp_def, integral_complex_ofReal, Complex.ofReal_re] using this
  have hec : ContinuousOn
      (fun u => ∫ x, cutPhi ρ J β (X u (Real.sqrt (u * σ2) • x)) ∂(stdGauss ι))
      (Set.Icc s v) := by
    have := Complex.continuous_re.comp_continuousOn (hgΦ.1.mono hIcc)
    simpa only [Function.comp_def, integral_complex_ofReal, Complex.ofReal_re] using this
  have hFd : ∀ u ∈ Set.Ioo s v,
      HasDerivAt (fun u => ∫ x, cutPsi ρ J β r (X u (Real.sqrt (u * σ2) • x)) ∂(stdGauss ι))
        ((∫ x, coordGen σ2 (fun t z => ((cutPsi ρ J β r (X t z) : ℝ) : ℂ)) u
          (Real.sqrt (u * σ2) • x) ∂(stdGauss ι)).re) u := by
    intro u hu
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u
      (hgψ.2 u ⟨by linarith [hu.1], hu.2⟩)
    simpa only [Function.comp_def, Complex.reCLM_apply, integral_complex_ofReal, Complex.ofReal_re]
      using this
  have hed : ∀ u ∈ Set.Ioo s v,
      HasDerivAt (fun u => ∫ x, cutPhi ρ J β (X u (Real.sqrt (u * σ2) • x)) ∂(stdGauss ι))
        ((∫ x, coordGen σ2 (fun t z => ((cutPhi ρ J β (X t z) : ℝ) : ℂ)) u
          (Real.sqrt (u * σ2) • x) ∂(stdGauss ι)).re) u := by
    intro u hu
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u
      (hgΦ.2 u ⟨by linarith [hu.1], hu.2⟩)
    simpa only [Function.comp_def, Complex.reCLM_apply, integral_complex_ofReal, Complex.ofReal_re]
      using this
  -- the `ψ` row
  have hFi : ∀ u ∈ Set.Ioo s v,
      (∫ x, coordGen σ2 (fun t z => ((cutPsi ρ J β r (X t z) : ℝ) : ℂ)) u
          (Real.sqrt (u * σ2) • x) ∂(stdGauss ι)).re ≤
        (rateMulA11 κ bΓ r * (∫ x, cutPsi ρ J β r (X u (Real.sqrt (u * σ2) • x)) ∂(stdGauss ι)) +
            rateMulA12 ε β κ bΓ r *
              (∫ x, cutPhi ρ J β (X u (Real.sqrt (u * σ2) • x)) ∂(stdGauss ι))) /
          (1 - u) + Koff := by
    intro u hu
    have huI := Set.Ioo_subset_Icc_self hu
    obtain ⟨hXc2, hXd⟩ := mul_slice hX (hsub u huI)
    have hw : 0 < 1 - u := by linarith [hu.2]
    have hu1 : u < 1 := by linarith [hu.2]
    have hIψ := mul_integrable hψ (hcont u huI)
    have hIΦ := mul_integrable hΦ (hcont u huI)
    have hB0 : ∀ t, 0 ≤ rateMulA11 κ bΓ r / (1 - u) * cutPsi ρ J β r t +
        rateMulA12 ε β κ bΓ r / (1 - u) * cutPhi ρ J β t := fun t =>
      add_nonneg (mul_nonneg (div_nonneg hA11 hw.le) (hpos t).2.2.2)
        (mul_nonneg (div_nonneg hA12.le hw.le) (hpos t).1)
    have hrow := mul_row σ2 X u (hGm u) (cutPsi ρ J β r)
      (fun t => rateMulA11 κ bΓ r / (1 - u) * cutPsi ρ J β r t +
        rateMulA12 ε β κ bΓ r / (1 - u) * cutPhi ρ J β t) hKoff
      ((hIψ.const_mul _).add (hIΦ.const_mul _)) hB0
      (fun y hy => by
        rw [mul_gen_re σ2 hψ.1 (hXd y) hXc2]
        rcases le_or_gt (X u y) (J * (1 + 2 * β)) with hle | hlt
        · obtain ⟨hg, hΓ⟩ := hrate u hu y hy hle
          have h := (cutoff_rates_mul hρ r hr hJ hβ hκ.le hbΓ hu1 (hX0 u y)
            (fun _ => hg) (mul_gamma_nonneg hσ2 _ y) (fun _ => hΓ)).1
          refine h.trans (le_of_eq ?_)
          ring
        · obtain ⟨⟨h1, h2⟩, -⟩ := hfar _ hlt
          rw [h1, h2]
          simp only [zero_mul, zero_div, add_zero]
          exact hB0 (X u y))
      (hoff u hu).1
    have hint : ∫ x, (rateMulA11 κ bΓ r / (1 - u) *
          cutPsi ρ J β r (X u (Real.sqrt (u * σ2) • x)) +
          rateMulA12 ε β κ bΓ r / (1 - u) * cutPhi ρ J β (X u (Real.sqrt (u * σ2) • x)))
            ∂(stdGauss ι) =
        rateMulA11 κ bΓ r / (1 - u) *
            (∫ x, cutPsi ρ J β r (X u (Real.sqrt (u * σ2) • x)) ∂(stdGauss ι)) +
          rateMulA12 ε β κ bΓ r / (1 - u) *
            (∫ x, cutPhi ρ J β (X u (Real.sqrt (u * σ2) • x)) ∂(stdGauss ι)) := by
      rw [integral_add (hIψ.const_mul _) (hIΦ.const_mul _), integral_const_mul,
        integral_const_mul]
    rw [hint] at hrow
    have he : (rateMulA11 κ bΓ r *
            (∫ x, cutPsi ρ J β r (X u (Real.sqrt (u * σ2) • x)) ∂(stdGauss ι)) +
          rateMulA12 ε β κ bΓ r *
            (∫ x, cutPhi ρ J β (X u (Real.sqrt (u * σ2) • x)) ∂(stdGauss ι))) / (1 - u) =
        rateMulA11 κ bΓ r / (1 - u) *
            (∫ x, cutPsi ρ J β r (X u (Real.sqrt (u * σ2) • x)) ∂(stdGauss ι)) +
          rateMulA12 ε β κ bΓ r / (1 - u) *
            (∫ x, cutPhi ρ J β (X u (Real.sqrt (u * σ2) • x)) ∂(stdGauss ι)) := by ring
    rw [he]
    exact hrow
  -- the `Φ` row
  have hei : ∀ u ∈ Set.Ioo s v,
      (∫ x, coordGen σ2 (fun t z => ((cutPhi ρ J β (X t z) : ℝ) : ℂ)) u
          (Real.sqrt (u * σ2) • x) ∂(stdGauss ι)).re ≤
        (rateMulA21 ε β κ bΓ * (∫ x, cutPsi ρ J β r (X u (Real.sqrt (u * σ2) • x)) ∂(stdGauss ι)) +
            0 * (∫ x, cutPhi ρ J β (X u (Real.sqrt (u * σ2) • x)) ∂(stdGauss ι))) /
          (1 - u) + Koff := by
    intro u hu
    have huI := Set.Ioo_subset_Icc_self hu
    obtain ⟨hXc2, hXd⟩ := mul_slice hX (hsub u huI)
    have hw : 0 < 1 - u := by linarith [hu.2]
    have hu1 : u < 1 := by linarith [hu.2]
    have hIψ := mul_integrable hψ (hcont u huI)
    have hB0 : ∀ t, 0 ≤ rateMulA21 ε β κ bΓ / (1 - u) * cutPsi ρ J β r t := fun t =>
      mul_nonneg (div_nonneg hA21.le hw.le) (hpos t).2.2.2
    have hrow := mul_row σ2 X u (hGm u) (cutPhi ρ J β)
      (fun t => rateMulA21 ε β κ bΓ / (1 - u) * cutPsi ρ J β r t) hKoff
      (hIψ.const_mul _) hB0
      (fun y hy => by
        rw [mul_gen_re σ2 hΦ.1 (hXd y) hXc2]
        rcases le_or_gt (X u y) (J * (1 + 2 * β)) with hle | hlt
        · obtain ⟨hg, hΓ⟩ := hrate u hu y hy hle
          have h := (cutoff_rates_mul hρ r hr hJ hβ hκ.le hbΓ hu1 (hX0 u y)
            (fun _ => hg) (mul_gamma_nonneg hσ2 _ y) (fun _ => hΓ)).2
          refine h.trans (le_of_eq ?_)
          ring
        · obtain ⟨-, ⟨h1, h2⟩⟩ := hfar _ hlt
          rw [h1, h2]
          simp only [zero_mul, zero_div, add_zero]
          exact hB0 (X u y))
      (hoff u hu).2
    rw [integral_const_mul] at hrow
    have he : (rateMulA21 ε β κ bΓ *
            (∫ x, cutPsi ρ J β r (X u (Real.sqrt (u * σ2) • x)) ∂(stdGauss ι)) +
          0 * (∫ x, cutPhi ρ J β (X u (Real.sqrt (u * σ2) • x)) ∂(stdGauss ι))) / (1 - u) =
        rateMulA21 ε β κ bΓ / (1 - u) *
          (∫ x, cutPsi ρ J β r (X u (Real.sqrt (u * σ2) • x)) ∂(stdGauss ι)) := by ring
    rw [he]
    exact hrow
  have hmain := coop2_comparison
    (F := fun u => ∫ x, cutPsi ρ J β r (X u (Real.sqrt (u * σ2) • x)) ∂(stdGauss ι))
    (e := fun u => ∫ x, cutPhi ρ J β (X u (Real.sqrt (u * σ2) • x)) ∂(stdGauss ι))
    (sF := fun _ => Koff) (se := fun _ => Koff)
    (a11 := rateMulA11 κ bΓ r) (a12 := rateMulA12 ε β κ bΓ r) (a21 := rateMulA21 ε β κ bΓ)
    (a22 := 0) hsv.le hv1 hA11 hA12 hA21 le_rfl hFc hec continuousOn_const continuousOn_const
    (fun _ _ => hKoff) (fun _ _ => hKoff) hFd hed hFi hei
  beta_reduce at hmain
  simp only [sub_zero, add_zero] at hmain
  set L := rateMulA12 ε β κ bΓ r /
    (rateMulA11 κ bΓ r / 2 + Real.sqrt ((rateMulA11 κ bΓ r / 2) ^ 2 +
      rateMulA12 ε β κ bΓ r * rateMulA21 ε β κ bΓ)) with hL
  have hI : (∫ _u in s..v, (Koff + L * Koff)) = (v - s) * ((1 + L) * Koff) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  rw [hI] at hmain
  refine ⟨?_, by unfold perronMul; exact hmain⟩
  -- `ℙ(X_v ≥ J(1+β)) ≤ E Φ(X_v)`
  have hv : v ∈ Set.Icc s v := ⟨hsv.le, le_rfl⟩
  have hA : MeasurableSet {x : ι → ℝ | J * (1 + β) ≤ X v (Real.sqrt (v * σ2) • x)} :=
    measurableSet_le measurable_const (hcont v hv).measurable
  calc stdGauss ι {x | J * (1 + β) ≤ X v (Real.sqrt (v * σ2) • x)}
      = ∫⁻ x, Set.indicator {x : ι → ℝ | J * (1 + β) ≤ X v (Real.sqrt (v * σ2) • x)} 1 x
          ∂(stdGauss ι) := (lintegral_indicator_one hA).symm
    _ ≤ ∫⁻ x, ENNReal.ofReal (cutPhi ρ J β (X v (Real.sqrt (v * σ2) • x))) ∂(stdGauss ι) := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ {x : ι → ℝ | J * (1 + β) ≤ X v (Real.sqrt (v * σ2) • x)}
        · rw [Set.indicator_of_mem hx, (hpos _).2.2.1 hx]; simp
        · rw [Set.indicator_of_notMem hx]; exact zero_le
    _ = ENNReal.ofReal (∫ x, cutPhi ρ J β (X v (Real.sqrt (v * σ2) • x)) ∂(stdGauss ι)) :=
        (ofReal_integral_eq_lintegral_ofReal (mul_integrable hΦ (hcont v hv))
          (Eventually.of_forall fun x => (hpos _).1)).symm

/-- The constant `B(r)` of the perturbation bound `ρ' - ρ ≤ r(2r-1)b/2 + √(bB(r))`. -/
def perronMulB (ε β κ : ℝ) (r : ℕ) : ℝ :=
  r ^ 2 * (2 * r - 1) * κ + r ^ 2 * (2 * r - 1) ^ 2 / 4 + rateMulC12 ε β r * rateA21 ε β κ +
    rateMulC21 ε β * rateA12 ε β κ r + rateMulC12 ε β r * rateMulC21 ε β

/-- A small multiplicative bracket rate moves the Perron root by at most one:
`b ≤ min{1, 1/(r(2r-1)), 1/(4B(r))}` gives `ρ' ≤ rκ + √((rκ)² + a₁₂a₂₁) + 1`. -/
theorem perronMul_le {ε β κ bΓ : ℝ} (r : ℕ) (hr : 1 ≤ r) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hβ : 0 < β) (hκ : 0 ≤ κ) (hb0 : 0 ≤ bΓ) (hb1 : bΓ ≤ 1) (hbr : r * (2 * r - 1) * bΓ ≤ 1)
    (hbB : 4 * perronMulB ε β κ r * bΓ ≤ 1) :
    perronMul ε β κ bΓ r ≤ r * κ + Real.sqrt ((r * κ) ^ 2 + rateA12 ε β κ r * rateA21 ε β κ) + 1 := by
  obtain ⟨hC12, hC21, hA11, hA12, hA21⟩ :=
    mul_rates_nonneg (κ := κ) (bΓ := bΓ) r hr hε0 hε1 hβ hκ hb0
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h2r : (1 : ℝ) ≤ 2 * r - 1 := by linarith
  have hB : 0 ≤ perronMulB ε β κ r := by
    unfold perronMulB
    have h1 : 0 ≤ (r : ℝ) ^ 2 * (2 * r - 1) * κ := by positivity
    have h2 : 0 ≤ (r : ℝ) ^ 2 * (2 * r - 1) ^ 2 / 4 := by positivity
    have h3 := mul_nonneg hC12 hA21
    have h4 := mul_nonneg hC21 hA12
    have h5 := mul_nonneg hC12 hC21
    linarith
  have hQ : 0 ≤ (r * κ) ^ 2 + rateA12 ε β κ r * rateA21 ε β κ := by positivity
  have hm0 : 0 ≤ (r : ℝ) * (2 * r - 1) * bΓ / 2 := by positivity
  have hm1 : (r : ℝ) * (2 * r - 1) * bΓ / 2 ≤ 1 / 2 := by linarith
  have hA : rateMulA11 κ bΓ r / 2 = r * κ + (r : ℝ) * (2 * r - 1) * bΓ / 2 := by
    unfold rateMulA11; ring
  have key : (rateMulA11 κ bΓ r / 2) ^ 2 + rateMulA12 ε β κ bΓ r * rateMulA21 ε β κ bΓ ≤
      ((r * κ) ^ 2 + rateA12 ε β κ r * rateA21 ε β κ) + bΓ * perronMulB ε β κ r := by
    have e : ((r * κ) ^ 2 + rateA12 ε β κ r * rateA21 ε β κ) + bΓ * perronMulB ε β κ r -
        ((rateMulA11 κ bΓ r / 2) ^ 2 + rateMulA12 ε β κ bΓ r * rateMulA21 ε β κ bΓ) =
        bΓ * (1 - bΓ) *
          ((r : ℝ) ^ 2 * (2 * r - 1) ^ 2 / 4 + rateMulC12 ε β r * rateMulC21 ε β) := by
      rw [hA]; unfold rateMulA12 rateMulA21 perronMulB; ring
    have hpos : 0 ≤ bΓ * (1 - bΓ) * ((r : ℝ) ^ 2 * (2 * r - 1) ^ 2 / 4 +
        rateMulC12 ε β r * rateMulC21 ε β) :=
      mul_nonneg (mul_nonneg hb0 (by linarith)) (by positivity)
    linarith
  have hbB' : bΓ * perronMulB ε β κ r ≤ (1 / 2) ^ 2 := by nlinarith
  have hs1 : Real.sqrt (bΓ * perronMulB ε β κ r) ≤ 1 / 2 :=
    Real.sqrt_le_iff.2 ⟨by norm_num, hbB'⟩
  have hs2 : Real.sqrt (((r * κ) ^ 2 + rateA12 ε β κ r * rateA21 ε β κ) +
      bΓ * perronMulB ε β κ r) ≤
      Real.sqrt ((r * κ) ^ 2 + rateA12 ε β κ r * rateA21 ε β κ) +
        Real.sqrt (bΓ * perronMulB ε β κ r) := by
    have h0 := Real.sqrt_nonneg ((r * κ) ^ 2 + rateA12 ε β κ r * rateA21 ε β κ)
    have h1 := Real.sqrt_nonneg (bΓ * perronMulB ε β κ r)
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have e1 := Real.sq_sqrt hQ
    have e2 := Real.sq_sqrt (mul_nonneg hb0 hB)
    nlinarith [mul_nonneg h0 h1]
  have hs3 := Real.sqrt_le_sqrt key
  unfold perronMul
  rw [hA] at hs3 ⊢
  linarith

/-- Excess of the finite-`r` Perron root over `c_* r` at `β = 1/(2r)`, uniform in `r`:
`rκ + √((rκ)² + a₁₂a₂₁) ≤ (1 + √(1 + 4e²/(1-ε)²))κr + (3/4)e^{3/2}(2e/(1-ε))κ`. -/
theorem perron_excess_le {ε κ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) (hκ : 0 ≤ κ) (r : ℕ)
    (hr : 1 ≤ r) :
    r * κ + Real.sqrt ((r * κ) ^ 2 +
        rateA12 ε (1 / (2 * r)) κ r * rateA21 ε (1 / (2 * r)) κ) ≤
      (1 + Real.sqrt (1 + 4 * Real.exp 2 / (1 - ε) ^ 2)) * κ * r +
        3 / 4 * Real.exp (3 / 2) * (2 * Real.exp 1 / (1 - ε)) * κ := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have h1ε : 0 < 1 - ε := by linarith
  set β : ℝ := 1 / (2 * r) with hβ
  have hβ0 : 0 < β := by positivity
  set x : ℝ := 3 / (2 * r) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx32 : x ≤ 3 / 2 := by
    rw [hx, div_le_iff₀ (by positivity)]; nlinarith
  set sA : ℝ := 2 * Real.exp 1 / (1 - ε) with hsA
  have hsA0 : 0 < sA := by positivity
  set A : ℝ := 4 * Real.exp 2 / (1 - ε) ^ 2 with hA
  have hAsq : sA ^ 2 = A := by
    have : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [hsA, hA, this]; field_simp; norm_num
  have hA0 : 0 < A := by positivity
  -- the product of the two rates
  have hP : (1 + 2 * β) ^ (2 * r + 1) * (1 + β) ≤ Real.exp 2 * Real.exp x := by
    have h1 : 1 + 2 * β ≤ Real.exp (2 * β) := by linarith [Real.add_one_le_exp (2 * β)]
    have h2 : 1 + β ≤ Real.exp β := by linarith [Real.add_one_le_exp β]
    have h3 : (1 + 2 * β) ^ (2 * r + 1) ≤ Real.exp (2 * β) ^ (2 * r + 1) :=
      pow_le_pow_left₀ (by positivity) h1 _
    rw [← Real.exp_nat_mul] at h3
    calc (1 + 2 * β) ^ (2 * r + 1) * (1 + β)
        ≤ Real.exp (((2 * r + 1 : ℕ) : ℝ) * (2 * β)) * Real.exp β :=
          mul_le_mul h3 h2 (by positivity) (by positivity)
      _ = Real.exp 2 * Real.exp x := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          rw [hβ, hx]; push_cast; field_simp; ring
  have hprod : rateA12 ε β κ r * rateA21 ε β κ ≤ (r * κ) ^ 2 * (A * Real.exp x) := by
    have e : rateA12 ε β κ r * rateA21 ε β κ =
        ((1 + 2 * β) ^ (2 * r + 1) * (1 + β)) * (4 * (r * κ) ^ 2 / (1 - ε) ^ 2) := by
      unfold rateA12 rateA21
      rw [hβ]; field_simp; ring
    rw [e]
    calc ((1 + 2 * β) ^ (2 * r + 1) * (1 + β)) * (4 * (r * κ) ^ 2 / (1 - ε) ^ 2)
        ≤ (Real.exp 2 * Real.exp x) * (4 * (r * κ) ^ 2 / (1 - ε) ^ 2) :=
          mul_le_mul_of_nonneg_right hP (by positivity)
      _ = (r * κ) ^ 2 * (A * Real.exp x) := by rw [hA]; field_simp
  -- the square root
  set T : ℝ := Real.sqrt (1 + A) with hT
  have hT2 : T ^ 2 = 1 + A := Real.sq_sqrt (by positivity)
  have hT0 : 0 ≤ T := Real.sqrt_nonneg _
  have hTs : sA ≤ T := by
    refine le_of_sq_le_sq ?_ hT0
    nlinarith
  set c : ℝ := sA * (Real.exp x - 1) / 2 with hc
  have hex1 : 1 ≤ Real.exp x := Real.one_le_exp hx0
  have hc0 : 0 ≤ c := by
    rw [hc]; have := sub_nonneg.2 hex1; positivity
  have hsq : 1 + A * Real.exp x ≤ (T + c) ^ 2 := by
    have : (T + c) ^ 2 = T ^ 2 + 2 * T * c + c ^ 2 := by ring
    rw [this, hT2]
    have h1 : 2 * sA * c ≤ 2 * T * c := by nlinarith
    have h2 : 2 * sA * c = A * (Real.exp x - 1) := by
      rw [hc, ← hAsq]; ring
    nlinarith [sq_nonneg c]
  have hrk : 0 ≤ (r : ℝ) * κ := by positivity
  have hQ : Real.sqrt ((r * κ) ^ 2 + rateA12 ε β κ r * rateA21 ε β κ) ≤ r * κ * (T + c) := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    calc (r * κ) ^ 2 + rateA12 ε β κ r * rateA21 ε β κ
        ≤ (r * κ) ^ 2 + (r * κ) ^ 2 * (A * Real.exp x) := by linarith
      _ = (r * κ) ^ 2 * (1 + A * Real.exp x) := by ring
      _ ≤ (r * κ) ^ 2 * (T + c) ^ 2 := mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = (r * κ * (T + c)) ^ 2 := by ring
  -- `e^x - 1 ≤ x e^x`
  have hexx : Real.exp x - 1 ≤ x * Real.exp x := by
    have h := Real.add_one_le_exp (-x)
    rw [Real.exp_neg] at h
    have hpos := Real.exp_pos x
    have : (-x + 1) * Real.exp x ≤ (Real.exp x)⁻¹ * Real.exp x :=
      mul_le_mul_of_nonneg_right h hpos.le
    rw [inv_mul_cancel₀ hpos.ne'] at this
    linarith
  have hexp : Real.exp x ≤ Real.exp (3 / 2) := Real.exp_le_exp.2 hx32
  have hrc : (r : ℝ) * c ≤ 3 / 4 * Real.exp (3 / 2) * sA := by
    calc (r : ℝ) * c = r * sA * (Real.exp x - 1) / 2 := by rw [hc]; ring
      _ ≤ r * sA * (x * Real.exp x) / 2 := by
          have := mul_le_mul_of_nonneg_left hexx (by positivity : (0 : ℝ) ≤ r * sA)
          linarith
      _ = 3 / 4 * Real.exp x * sA := by rw [hx]; field_simp; ring
      _ ≤ 3 / 4 * Real.exp (3 / 2) * sA := by
          have := mul_le_mul_of_nonneg_right hexp hsA0.le
          nlinarith
  have hfin : r * κ * c ≤ 3 / 4 * Real.exp (3 / 2) * sA * κ := by
    have := mul_le_mul_of_nonneg_right hrc hκ
    nlinarith
  have hlhs : r * κ * (T + c) = T * κ * r + r * κ * c := by ring
  linarith [hQ, hfin, hlhs]

end LSBA
