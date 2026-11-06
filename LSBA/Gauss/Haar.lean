import LSBA.Gauss.GUELaw

/-!
# Haar measure on the unitary group

Compactness of `U(W)`, its normalized Haar measure, left and right invariance, and the joint law
of the GUE blocks and an independent Haar unitary under common conjugation: Appendix D.1
[subsec:pf_thm31] and Section 7.5 [app:uniform-continuation] (ii).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

noncomputable section

open scoped Classical

namespace LSBA

/-- `U(W)` is compact (missing as an instance in Mathlib). -/
instance compactSpace_unitaryGroup (W : ℕ) : CompactSpace (Matrix.unitaryGroup (Fin W) ℂ) := by
  have h : IsCompact ((Matrix.unitaryGroup (Fin W) ℂ : Submonoid (Matrix (Fin W) (Fin W) ℂ)) :
      Set (Matrix (Fin W) (Fin W) ℂ)) := by
    have hc : IsCompact (Set.pi Set.univ fun _ : Fin W => Set.pi Set.univ fun _ : Fin W =>
        Metric.closedBall (0 : ℂ) 1) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
    refine hc.of_isClosed_subset ?_ ?_
    · exact isClosed_unitary (R := Matrix (Fin W) (Fin W) ℂ)
    · intro U hU i _ j _
      simpa using entry_norm_bound_of_unitary hU i j
  exact isCompact_iff_compactSpace.mp h

/-- Normalized Haar measure on `U(W)`. -/
def haarU (W : ℕ) : Measure (Matrix.unitaryGroup (Fin W) ℂ) := Measure.haarMeasure ⊤

instance isProbabilityMeasure_haarU (W : ℕ) : IsProbabilityMeasure (haarU W) :=
  ⟨Measure.haarMeasure_self⟩

/-- `haarU W` is a Haar measure. -/
instance haar_isHaarMeasure_haarU (W : ℕ) : (haarU W).IsHaarMeasure := by
  unfold haarU
  infer_instance

theorem isMulLeftInvariant_haarU (W : ℕ) : (haarU W).IsMulLeftInvariant :=
  inferInstance

theorem isMulRightInvariant_haarU (W : ℕ) : (haarU W).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

private theorem haar_continuous_gueBlock (W L : ℕ) (a : Fin L) :
    Continuous fun ω : Ω W L => gueBlock W L ω a := by
  refine continuous_matrix fun α β => ?_
  simp only [gueBlock, Matrix.of_apply]
  split_ifs <;> fun_prop

private theorem haar_continuous_conjMap_uncurry (W L : ℕ) :
    Continuous (fun p : Ω W L × Matrix.unitaryGroup (Fin W) ℂ => conjMap W L p.2 p.1) := by
  refine continuous_pi fun x => ?_
  obtain ⟨a, i, j⟩ := x
  have h1 : Continuous fun p : Ω W L × Matrix.unitaryGroup (Fin W) ℂ =>
      (p.2 : Matrix (Fin W) (Fin W) ℂ) := continuous_subtype_val.comp continuous_snd
  have h2 : Continuous fun p : Ω W L × Matrix.unitaryGroup (Fin W) ℂ => gueBlock W L p.1 a :=
    (haar_continuous_gueBlock W L a).comp continuous_fst
  have hB : Continuous fun p : Ω W L × Matrix.unitaryGroup (Fin W) ℂ =>
      (p.2 : Matrix (Fin W) (Fin W) ℂ) * gueBlock W L p.1 a *
        star (p.2 : Matrix (Fin W) (Fin W) ℂ) :=
    (h1.matrix_mul h2).matrix_mul (continuous_star.comp h1)
  simp only [conjMap, gueCoord]
  split_ifs
  · exact continuous_const.mul (Complex.continuous_re.comp (hB.matrix_elem i i))
  · exact continuous_const.mul (Complex.continuous_re.comp (hB.matrix_elem i j))
  · exact continuous_const.mul (Complex.continuous_im.comp (hB.matrix_elem j i))

theorem measurable_conjMap_uncurry (W L : ℕ) :
    Measurable (fun p : Ω W L × Matrix.unitaryGroup (Fin W) ℂ => conjMap W L p.2 p.1) :=
  (haar_continuous_conjMap_uncurry W L).measurable

/-- Common conjugation by an independent Haar unitary, Appendix D.1 [subsec:pf_thm31] and
Section 7.5 [app:uniform-continuation] (ii). -/
theorem measurePreserving_conj_haar (W L : ℕ) :
    MeasurePreserving (fun p : Ω W L × Matrix.unitaryGroup (Fin W) ℂ => (conjMap W L p.2 p.1, p.2))
      ((μ W L).prod (haarU W)) ((μ W L).prod (haarU W)) := by
  have hsw : Measurable (Prod.swap : Matrix.unitaryGroup (Fin W) ℂ × Ω W L →
      Ω W L × Matrix.unitaryGroup (Fin W) ℂ) := measurable_swap
  have hm := (measurable_conjMap_uncurry W L).comp hsw
  have hS : MeasurePreserving
      (fun p : Matrix.unitaryGroup (Fin W) ℂ × Ω W L => (p.1, conjMap W L p.1 p.2))
      ((haarU W).prod (μ W L)) ((haarU W).prod (μ W L)) :=
    (MeasurePreserving.id (haarU W)).skew_product
      (g := fun (U : Matrix.unitaryGroup (Fin W) ℂ) (ω : Ω W L) => conjMap W L U ω) hm
      (Filter.Eventually.of_forall fun U => (measurePreserving_conjMap W L U).map_eq)
  exact (Measure.measurePreserving_swap (μ := haarU W) (ν := μ W L)).comp
    (hS.comp (Measure.measurePreserving_swap (μ := μ W L) (ν := haarU W)))

end LSBA
