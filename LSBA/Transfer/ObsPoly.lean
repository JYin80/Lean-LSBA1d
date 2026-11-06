import LSBA.Transfer.StateChain

/-!
# Polynomials in the observables

The formal polynomial calculus of Section 11.3.1 [lg:sec:state-estimates]: complex polynomials in
formal variables `m_k`, `f_k` (`k ≠ 0`; positive and negative indices independent, `m_0 = f_0 = 1`),
`w = W⁻¹` and `γ = g⁻²`; evaluation at a state through `m_k`, `f_k` of (11.10) [lg:eq:observables];
the degree of a monomial (sum of the indices); the zero-noise rotation `x_k ↦ (−e^{−2iθ})^k x_k`;
the `W⁰` part; conjugation `x_k ↦ x_{−k}`; the ideal `𝒥 = (W⁻¹, f_k : k ≠ 0)` of Lemma 11.7
[lg:lem:ideal]; truncation in `γ`.
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Nonzero integers, the indices of the formal variables `m_k`, `f_k`. -/
abbrev NzInt : Type := {k : ℤ // k ≠ 0}

/-- The formal variables of Section 11.3.1 [lg:sec:state-estimates]: `m_k`, `f_k` (`k ≠ 0`),
`w = W⁻¹` and `γ = g⁻²`. -/
inductive ObsVar
  | m (k : NzInt)
  | f (k : NzInt)
  | w
  | γ

/-- Complex polynomials in the observables (Lemma 11.7 [lg:lem:ideal]). -/
abbrev ObsPoly : Type := MvPolynomial ObsVar ℂ

/-- The index `k` of `m_k`, `f_k`; `0` for `w`, `γ`. -/
def ObsVar.idx : ObsVar → ℤ
  | .m k => k
  | .f k => k
  | .w => 0
  | .γ => 0

/-- The power of `γ` carried by a variable. -/
def ObsVar.gamWt : ObsVar → ℕ
  | .γ => 1
  | _ => 0

/-- The power of `w` carried by a variable. -/
def ObsVar.wWt : ObsVar → ℕ
  | .w => 1
  | _ => 0

/-- Index reversal `m_k ↦ m_{−k}`, `f_k ↦ f_{−k}`. -/
def ObsVar.neg : ObsVar → ObsVar
  | .m k => .m ⟨-k.1, neg_ne_zero.mpr k.2⟩
  | .f k => .f ⟨-k.1, neg_ne_zero.mpr k.2⟩
  | .w => .w
  | .γ => .γ

/-- The degree of a monomial, the sum of its indices (Section 11.3.3 [lg:sec:general-state]). -/
def obsDeg (d : ObsVar →₀ ℕ) : ℤ := Finsupp.weight ObsVar.idx d

/-- `m_k` as a polynomial, with `m_0 = 1`. -/
def mVar (k : ℤ) : ObsPoly := if h : k = 0 then 1 else X (.m ⟨k, h⟩)

/-- `f_k` as a polynomial, with `f_0 = 1`. -/
def fVar (k : ℤ) : ObsPoly := if h : k = 0 then 1 else X (.f ⟨k, h⟩)

/-- Evaluation at a state: `m_k ↦ m_k(C)`, `f_k ↦ f_k(C, v)` of (11.10) [lg:eq:observables],
`w ↦ W⁻¹`, `γ ↦ g⁻²`. -/
def obsEval (g : ℝ) {W : ℕ} (X : State W) : ObsPoly →ₐ[ℂ] ℂ :=
  aeval fun v => match v with
    | .m k => obsM k.1 X
    | .f k => obsF k.1 X
    | .w => (W : ℂ)⁻¹
    | .γ => (((g ^ 2)⁻¹ : ℝ) : ℂ)

/-- The zero-noise rotation `x_k ↦ (−e^{−2iθ})^k x_k` (the leading rule of
(11.45) [lg:eq:required-parity-updates]). -/
def rotPoly (E : ℝ) : ObsPoly →ₐ[ℂ] ObsPoly :=
  aeval fun v => C ((-normalPhase E) ^ v.idx) * X v

/-- The `W⁰` part: `w ↦ 0`. -/
def zeroW : ObsPoly →ₐ[ℂ] ObsPoly :=
  aeval fun v => if v = .w then 0 else X v

/-- Conjugation: `x_k ↦ x_{−k}` with conjugated coefficients. -/
def conjPoly : ObsPoly →+* ObsPoly :=
  eval₂Hom (C.comp (starRingEnd ℂ)) fun v => X v.neg

/-- The ideal `𝒥 = (W⁻¹, f_k : k ≠ 0)` of Lemma 11.7 [lg:lem:ideal]. -/
def obsIdeal : Ideal ObsPoly :=
  Ideal.span ({X .w} ∪ Set.range fun k : NzInt => X (.f k))

/-- The ideal `(f_k : k ≠ 0)`. -/
def fIdeal : Ideal ObsPoly :=
  Ideal.span (Set.range fun k : NzInt => X (.f k))

/-- The variables `m_k` and `γ` (polynomials in the traces, Lemma 11.7 (iii) [lg:lem:ideal]). -/
def traceVars : Set ObsVar := {v | v.idx = 0 ∧ v ≠ .w} ∪ Set.range ObsVar.m

/-- Truncation in `γ`: the terms of orders `1, g⁻², …, g⁻²ᴺ`. -/
def truncG (N : ℕ) : ObsPoly →ₗ[ℂ] ObsPoly :=
  ∑ j ∈ Finset.range (N + 1), weightedHomogeneousComponent ObsVar.gamWt j

/-- The monomials of degree congruent to `k` modulo `2`. -/
def parityPart (k : ℤ) (p : ObsPoly) : ObsPoly :=
  ∑ d ∈ p.support, if Even (obsDeg d - k) then monomial d (p.coeff d) else 0

/-- Evaluation commutes with conjugation on states (`m_{−k} = \overline{m_k}`,
`f_{−k} = \overline{f_k}`). -/
theorem obsEval_conjPoly {W : ℕ} (hW : 1 ≤ W) (g : ℝ) {X : State W} (hX : IsState X)
    (p : ObsPoly) : obsEval g X (conjPoly p) = star (obsEval g X p) := by
  have h : ((obsEval g X : ObsPoly →ₐ[ℂ] ℂ) : ObsPoly →+* ℂ).comp conjPoly =
      (starRingEnd ℂ).comp (obsEval g X : ObsPoly →ₐ[ℂ] ℂ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [conjPoly, obsEval]
    · intro v
      cases v with
      | m k =>
        simp only [RingHom.comp_apply, conjPoly, obsEval, eval₂Hom_X', ObsVar.neg, aeval_X,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
        exact (obsM_zero_neg hW hX k.1).2
      | f k =>
        simp only [RingHom.comp_apply, conjPoly, obsEval, eval₂Hom_X', ObsVar.neg, aeval_X,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
        exact (obsF_zero_neg hX k.1).2
      | w =>
        simp [conjPoly, obsEval, ObsVar.neg]
      | γ =>
        simp [conjPoly, obsEval, ObsVar.neg]
  exact RingHom.congr_fun h p

/-- `|p(X)| ≤ Σ |coefficients|` on states, for `W ≥ 1`, `g ≥ 1` (`|m_k|, |f_k| ≤ 1`). -/
theorem norm_obsEval_le {W : ℕ} (hW : 1 ≤ W) {g : ℝ} (hg : 1 ≤ g) {X : State W} (hX : IsState X)
    (p : ObsPoly) : ‖obsEval g X p‖ ≤ ∑ d ∈ p.support, ‖p.coeff d‖ := by
  have hv : ∀ v : ObsVar, ‖obsEval g X (MvPolynomial.X v)‖ ≤ 1 := by
    intro v
    cases v with
    | m k => simpa [obsEval] using norm_obsM_le_one k.1 hX
    | f k => simpa [obsEval] using norm_obsF_le_one k.1 hX
    | w =>
      simp only [obsEval, aeval_X, norm_inv, Complex.norm_natCast]
      exact inv_le_one_of_one_le₀ (by exact_mod_cast hW : (1 : ℝ) ≤ W)
    | γ =>
      simp only [obsEval, aeval_X, Complex.norm_real, norm_inv, norm_pow, Real.norm_eq_abs]
      have : 1 ≤ |g| ^ 2 := by
        have := abs_of_pos (lt_of_lt_of_le one_pos hg)
        rw [this]; nlinarith
      exact inv_le_one_of_one_le₀ this
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [monomial_eq, map_mul, map_finsuppProd, norm_mul]
  have hprod : ‖d.prod fun n e => (obsEval g X (MvPolynomial.X n)) ^ e‖ ≤ 1 := by
    refine (Finset.norm_prod_le _ _).trans
      (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun n _ => ?_)
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (hv n)
  have hC : ‖obsEval g X (C (p.coeff d))‖ = ‖p.coeff d‖ := by simp
  rw [hC]
  calc ‖p.coeff d‖ * _ ≤ ‖p.coeff d‖ * 1 :=
        mul_le_mul_of_nonneg_left (by simpa [map_pow] using hprod) (norm_nonneg _)
    _ = ‖p.coeff d‖ := mul_one _

end LSBA
