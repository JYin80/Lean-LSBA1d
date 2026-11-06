import Mathlib

/-!
# Zero sets of polynomials

The real zero set of a multivariate polynomial that does not vanish identically on real points is
null for products of atomless σ-finite measures.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The real zeros of a nonzero complex univariate polynomial form a finite set. -/
private lemma polyNull_finite_realRoots {p : Polynomial ℂ} (hp : p ≠ 0) :
    {y : ℝ | Polynomial.eval (y : ℂ) p = 0}.Finite :=
  (Polynomial.finite_setOfPred_isRoot hp).preimage Complex.ofReal_injective.injOn

/-- Continuity of the real evaluation of a polynomial. -/
private lemma polyNull_continuous_eval {ι : Type*} (P : MvPolynomial ι ℂ) :
    Continuous fun x : ι → ℝ => MvPolynomial.eval (fun i => (x i : ℂ)) P :=
  (MvPolynomial.continuous_eval P).comp
    (continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i))

/-- The statement of `measure_zero_mvPolynomial` for the index types `Fin n`. -/
private lemma polyNull_fin (n : ℕ) :
    ∀ (ν : Fin n → Measure ℝ) [∀ i, SigmaFinite (ν i)] [∀ i, NullSingletonClass (ν i)]
      (P : MvPolynomial (Fin n) ℂ) (x₀ : Fin n → ℝ),
      MvPolynomial.eval (fun i => (x₀ i : ℂ)) P ≠ 0 →
      Measure.pi ν {x | MvPolynomial.eval (fun i => (x i : ℂ)) P = 0} = 0 := by
  induction n with
  | zero =>
    intro ν _ _ P x₀ h
    have : {x : Fin 0 → ℝ | MvPolynomial.eval (fun i => (x i : ℂ)) P = 0} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rwa [Subsingleton.elim x x₀]
    rw [this, measure_empty]
  | succ n ih =>
    intro ν _ _ P x₀ h
    set Q := MvPolynomial.finSuccEquiv ℂ n P with hQ
    have hcons : ∀ (y : ℝ) (x' : Fin n → ℝ),
        MvPolynomial.eval (Fin.cons (y : ℂ) (fun j => (x' j : ℂ)) : Fin (n + 1) → ℂ) P =
          Polynomial.eval (y : ℂ) (Polynomial.map (MvPolynomial.eval fun j => (x' j : ℂ)) Q) :=
      fun y x' => MvPolynomial.eval_eq_eval_mv_eval' _ _ _
    have hsplit : ∀ x : Fin (n + 1) → ℝ, (fun i => (x i : ℂ)) =
        (Fin.cons (x 0 : ℂ) (fun j => (x j.succ : ℂ)) : Fin (n + 1) → ℂ) := by
      intro x
      funext i
      refine Fin.cases ?_ ?_ i <;> simp
    -- a coefficient of `Q` that does not vanish at the tail of `x₀`
    have hmap : Polynomial.map (MvPolynomial.eval fun j => (x₀ j.succ : ℂ)) Q ≠ 0 := by
      intro h0
      apply h
      rw [hsplit, hcons, h0, Polynomial.eval_zero]
    obtain ⟨k, hk⟩ : ∃ k, MvPolynomial.eval (fun j => (x₀ j.succ : ℂ)) (Q.coeff k) ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hmap (Polynomial.ext fun k => by rw [Polynomial.coeff_map, hc k,
        Polynomial.coeff_zero])
    have hnull := ih (fun j => ν j.succ) (Q.coeff k) (fun j => x₀ j.succ) hk
    -- the zero set in the coordinates `(x 0, tail x)`
    set T : Set (ℝ × (Fin n → ℝ)) :=
      {p | MvPolynomial.eval (Fin.cons (p.1 : ℂ) (fun j => (p.2 j : ℂ)) : Fin (n + 1) → ℂ) P = 0}
      with hT
    have hTmeas : MeasurableSet T := by
      refine (isClosed_eq ?_ continuous_const).measurableSet
      refine (MvPolynomial.continuous_eval P).comp (continuous_pi fun i => ?_)
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        fun_prop
      · simp only [Fin.cons_succ]
        fun_prop
    have hmp := measurePreserving_piFinSuccAbove (fun i => ν i) 0
    have hpre : MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 ⁻¹' T =
        {x | MvPolynomial.eval (fun i => (x i : ℂ)) P = 0} := by
      ext x
      simp only [Set.mem_preimage, hT, Set.mem_ofPred_eq, MeasurableEquiv.piFinSuccAbove_apply]
      rw [hsplit x]
      rfl
    rw [← hpre, hmp.measure_preimage hTmeas.nullMeasurableSet,
      Measure.prod_apply_symm hTmeas]
    refine (lintegral_congr_ae ?_).trans (lintegral_zero)
    have hae : ∀ᵐ x' ∂(Measure.pi fun j : Fin n => ν (Fin.succAbove 0 j)),
        x' ∉ {x : Fin n → ℝ | MvPolynomial.eval (fun i => (x i : ℂ)) (Q.coeff k) = 0} := by
      simp only [Fin.succAbove_zero]
      exact measure_eq_zero_iff_ae_notMem.mp hnull
    filter_upwards [hae] with x' hx'
    have hne : Polynomial.map (MvPolynomial.eval fun j => (x' j : ℂ)) Q ≠ 0 := by
      intro h0
      apply hx'
      have := congrArg (fun p => Polynomial.coeff p k) h0
      simpa [Polynomial.coeff_map] using this
    change _ = 0
    refine measure_mono_null (fun y hy => ?_) ((polyNull_finite_realRoots hne).measure_zero _)
    simpa [hT, hcons] using hy

/-- The real zero set of a multivariate polynomial that is nonzero at one real point is null
for every product of σ-finite measures without atoms. -/
theorem measure_zero_mvPolynomial {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ)
    [∀ i, SigmaFinite (ν i)] [∀ i, NullSingletonClass (ν i)] (P : MvPolynomial ι ℂ)
    (x₀ : ι → ℝ) (h : MvPolynomial.eval (fun i => (x₀ i : ℂ)) P ≠ 0) :
    Measure.pi ν {x | MvPolynomial.eval (fun i => (x i : ℂ)) P = 0} = 0 := by
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hmp := measurePreserving_piCongrLeft ν e.symm
  have hS : MeasurableSet {x : ι → ℝ | MvPolynomial.eval (fun i => (x i : ℂ)) P = 0} :=
    (isClosed_eq (polyNull_continuous_eval P) continuous_const).measurableSet
  rw [← hmp.measure_preimage hS.nullMeasurableSet]
  have hpre : MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e.symm ⁻¹'
      {x : ι → ℝ | MvPolynomial.eval (fun i => (x i : ℂ)) P = 0} =
      {y : Fin (Fintype.card ι) → ℝ |
        MvPolynomial.eval (fun j => (y j : ℂ)) (MvPolynomial.rename e P) = 0} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, MvPolynomial.eval_rename]
    congr! 2
    refine congrArg _ (funext fun i => ?_)
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rw [hpre]
  refine polyNull_fin _ (fun j => ν (e.symm j)) (MvPolynomial.rename e P) (x₀ ∘ e.symm) ?_
  rw [MvPolynomial.eval_rename]
  convert h using 2
  refine congrArg _ (funext fun i => ?_)
  simp

end LSBA
