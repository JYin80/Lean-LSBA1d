import Mathlib

/-!
# A layer-cake bound from a bound on sets

If a measure `ν` is dominated on measurable sets by `A` times the supremum of a family of measures
of mass at most one, then `∫ |h| dν ≤ (4/3) A M` for every measurable `h` whose fourth moments
under the family are at most `M⁴`: by the layer-cake formula and Chebyshev's inequality,
`ν(|h| > s) ≤ A min{1, M⁴ s⁻⁴}`. This is the passage from sets to the angular `L⁴` norm in the
proof of Lemma F.3 [lem:c-operators].
-/

open MeasureTheory

open scoped ENNReal

noncomputable section

namespace LSBA

/-- `ν(S) ≤ A sup_i m_i(S)` on measurable sets, `m_i(X) ≤ 1` and `∫ |h|⁴ dm_i ≤ M⁴` give
`∫ |h| dν ≤ (4/3) A M`. -/
theorem lintegral_enorm_le_of_measure_le_iSup {X ι : Type*} [MeasurableSpace X] {ν : Measure X}
    {m : ι → Measure X} (hm : ∀ i, m i Set.univ ≤ 1) {A M : ℝ} (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hν : ∀ S, MeasurableSet S → ν S ≤ ENNReal.ofReal A * ⨆ i, m i S) {h : X → ℝ}
    (hh : Measurable h) (h4 : ∀ i, ∫⁻ x, ‖h x‖ₑ ^ 4 ∂(m i) ≤ ENNReal.ofReal M ^ 4) :
    ∫⁻ x, ‖h x‖ₑ ∂ν ≤ ENNReal.ofReal (4 / 3 * A * M) := by
  have hmeas : ∀ t : ℝ, MeasurableSet {a | t < |h a|} := fun t =>
    measurableSet_lt measurable_const hh.abs
  have hcheb : ∀ t : ℝ, 0 < t → ∀ i,
      m i {a | t < |h a|} ≤ ENNReal.ofReal M ^ 4 / ENNReal.ofReal t ^ 4 := by
    intro t ht i
    have hε : ENNReal.ofReal t ^ 4 ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.2 ht).ne'
    have hε' : ENNReal.ofReal t ^ 4 ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    calc m i {a | t < |h a|} ≤ m i {a | ENNReal.ofReal t ^ 4 ≤ ‖h a‖ₑ ^ 4} := by
          refine measure_mono fun a ha => ?_
          have h1 : ENNReal.ofReal t ≤ ‖h a‖ₑ := by
            rw [Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_ofReal (show t < |h a| from ha).le
          exact pow_le_pow_left' h1 4
      _ ≤ (∫⁻ a, ‖h a‖ₑ ^ 4 ∂(m i)) / ENNReal.ofReal t ^ 4 :=
          meas_ge_le_lintegral_div (hh.enorm.pow_const 4).aemeasurable hε hε'
      _ ≤ ENNReal.ofReal M ^ 4 / ENNReal.ofReal t ^ 4 := ENNReal.div_le_div_right (h4 i) _
  have hkey : ∀ t : ℝ, 0 < t → ν {a | t < |h a|} ≤
      ENNReal.ofReal A * min 1 (ENNReal.ofReal M ^ 4 / ENNReal.ofReal t ^ 4) := by
    intro t ht
    refine (hν _ (hmeas t)).trans (mul_le_mul_right (iSup_le fun i => le_min ?_ (hcheb t ht i)) _)
    exact (measure_mono (Set.subset_univ _)).trans (hm i)
  have hlc : ∫⁻ x, ‖h x‖ₑ ∂ν = ∫⁻ t in Set.Ioi (0 : ℝ), ν {a | t < |h a|} := by
    simp_rw [Real.enorm_eq_ofReal_abs]
    exact lintegral_eq_lintegral_meas_lt ν (ae_of_all _ fun x => abs_nonneg _)
      hh.abs.aemeasurable
  rw [hlc]
  rcases hM.eq_or_lt with rfl | hMpos
  · calc ∫⁻ t in Set.Ioi (0 : ℝ), ν {a | t < |h a|} ≤ ∫⁻ _t in Set.Ioi (0 : ℝ), 0 := by
          refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
          refine (hkey t ht).trans ?_
          simp
      _ ≤ _ := by simp
  · have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 M ∪ Set.Ioi M :=
      (Set.Ioc_union_Ioi_eq_Ioi hMpos.le).symm
    have hAtop : ENNReal.ofReal A ≠ ∞ := ENNReal.ofReal_ne_top
    have h1 : ∫⁻ t in Set.Ioc (0 : ℝ) M, ν {a | t < |h a|} ≤
        ENNReal.ofReal A * ENNReal.ofReal M := by
      calc ∫⁻ t in Set.Ioc (0 : ℝ) M, ν {a | t < |h a|}
          ≤ ∫⁻ _t in Set.Ioc (0 : ℝ) M, ENNReal.ofReal A := by
            refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
            refine (hkey t ht.1).trans ?_
            simpa using mul_le_mul_right (min_le_left (1 : ℝ≥0∞) _) (ENNReal.ofReal A)
        _ = ENNReal.ofReal A * ENNReal.ofReal M := by
            rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]
    have h2 : ∫⁻ t in Set.Ioi M, ν {a | t < |h a|} ≤
        ENNReal.ofReal A * ENNReal.ofReal (M / 3) := by
      have hint : MeasureTheory.IntegrableOn (fun t : ℝ => M ^ 4 * t ^ (-4 : ℝ)) (Set.Ioi M) :=
        (integrableOn_Ioi_rpow_of_lt (by norm_num) hMpos).const_mul _
      have hval : ∫ t in Set.Ioi M, M ^ 4 * t ^ (-4 : ℝ) = M / 3 := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hMpos]
        have h3 : M ^ 4 * M ^ (-4 + 1 : ℝ) = M := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hMpos]
          norm_num
        generalize M ^ (-4 + 1 : ℝ) = y at h3 ⊢
        calc M ^ 4 * (-y / (-4 + 1)) = (M ^ 4 * y) / 3 := by ring
          _ = M / 3 := by rw [h3]
      have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi M)] fun t : ℝ => M ^ 4 * t ^ (-4 : ℝ) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg (by positivity) (Real.rpow_nonneg (hMpos.le.trans ht.le) _)
      have hlint : ∫⁻ t in Set.Ioi M, ENNReal.ofReal (M ^ 4 * t ^ (-4 : ℝ)) =
          ENNReal.ofReal (M / 3) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, hval]
      calc ∫⁻ t in Set.Ioi M, ν {a | t < |h a|}
          ≤ ∫⁻ t in Set.Ioi M, ENNReal.ofReal A * ENNReal.ofReal (M ^ 4 * t ^ (-4 : ℝ)) := by
            refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
            have htpos : 0 < t := hMpos.trans ht
            have heq : ENNReal.ofReal M ^ 4 / ENNReal.ofReal t ^ 4 =
                ENNReal.ofReal (M ^ 4 * t ^ (-4 : ℝ)) := by
              rw [← ENNReal.ofReal_pow hM, ← ENNReal.ofReal_pow htpos.le,
                ← ENNReal.ofReal_div_of_pos (by positivity)]
              congr 1
              rw [Real.rpow_neg htpos.le, Real.rpow_ofNat, div_eq_mul_inv]
            exact (hkey t htpos).trans ((mul_le_mul_right (min_le_right _ _) _).trans (le_of_eq
              (by rw [heq])))
        _ = ENNReal.ofReal A * ENNReal.ofReal (M / 3) := by
            rw [lintegral_const_mul' _ _ hAtop, hlint]
    calc ∫⁻ t in Set.Ioi (0 : ℝ), ν {a | t < |h a|}
        ≤ (∫⁻ t in Set.Ioc (0 : ℝ) M, ν {a | t < |h a|}) +
            ∫⁻ t in Set.Ioi M, ν {a | t < |h a|} := by
          rw [hsplit]; exact lintegral_union_le _ _ _
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal M + ENNReal.ofReal A * ENNReal.ofReal (M / 3) :=
          add_le_add h1 h2
      _ = ENNReal.ofReal (4 / 3 * A * M) := by
          rw [← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_add]
          · congr 1; ring
          · positivity
          · positivity

end LSBA
