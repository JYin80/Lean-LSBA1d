import LSBA.Prop.Increment
import LSBA.Prop.RegimeBdd
import LSBA.Prop.RegimeLarge
import LSBA.Sampling.Reach
import LSBA.Kernel.LargeIncrement

/-!
# The increment input on the bounded- and large-coupling base families

(A.49) [da:eq:mixed-profile-increment] along the comparison chains of Lemma 6.3(b)
[da:lem:comparison-parameters], at bounded coupling from (A.29) [gc:eq:gradient] and at large
coupling from its large-coupling form.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- `RegBdd` is monotone in the energy bound. -/
private lemma incrementInputs_regBdd_mono {C B B' c' : ℝ} {L : ℕ} {g E : ℝ}
    (h : RegBdd C B c' L g E) (hB : B ≤ B') : RegBdd C B' c' L g E :=
  ⟨h.1, h.2.1, h.2.2.1.trans hB, h.2.2.2.1, h.2.2.2.2⟩

/-- (A.49) [da:eq:mixed-profile-increment] on the reach of the bounded-coupling base family, from
(A.29) [gc:eq:gradient] along the comparison chains of Lemma 6.3(b)
[da:lem:comparison-parameters]; no lower bound on the coupling is used. -/
theorem incrementInput_bdd (C B c' : ℝ) (hC : 0 < C) (hB : 0 < B) (hc' : 0 < c')
    (gmin ρ : ℕ → ℝ) (hρ : Tendsto ρ atTop atTop) (J : ℕ) :
    IncrementInput (baseBdd C B c' gmin ρ) J := by
  obtain ⟨BJ0, cJ, L₀, hcJ, hchain⟩ := cmpChain_bdd C B c' J hC hB hc'
  set BJ : ℝ := max BJ0 1 with hBJdef
  have hBJ : 0 < BJ := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨c, C', hc, hC', hgrad⟩ := bdd_gradient C BJ cJ 2 hC hBJ hcJ two_pos 0
  refine ⟨2 * C', by positivity, fun A hA => ?_⟩
  obtain ⟨CA, W₁, hCA, hW₁⟩ := hgrad (A + 2) (by linarith)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (hρ.eventually_ge_atTop (max 3 (max (L₀ : ℝ) CA)))
  refine ⟨max N (max 3 W₁), fun W hW d p hd hreach a b b' => ?_⟩
  have hWN : N ≤ W := (le_max_left _ _).trans hW
  have hW3 : 3 ≤ W := ((le_max_left _ _).trans (le_max_right _ _)).trans hW
  have hWW₁ : W₁ ≤ W := ((le_max_right _ _).trans (le_max_right _ _)).trans hW
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hlog : 1 ≤ Real.log W := by
    rw [Real.le_log_iff_exp_le hW0]
    have : (3 : ℝ) ≤ W := by exact_mod_cast hW3
    exact (Real.exp_one_lt_three.trans_le this).le
  obtain ⟨q, hq, steps, hlen, hadm, -, hpc, hL, hu, h12, -⟩ := cmpReach_chain _ W d p hreach
  obtain ⟨-, hreg, hLlog, hLW, hq12, hqt⟩ := hq
  have hρW := hN W hWN
  have hρ3 : (3 : ℝ) ≤ ρ W := (le_max_left _ _).trans hρW
  have hρL₀ : (L₀ : ℝ) ≤ ρ W := ((le_max_left _ _).trans (le_max_right _ _)).trans hρW
  have hρCA : CA ≤ ρ W := ((le_max_right _ _).trans (le_max_right _ _)).trans hρW
  have hρ0 : 0 ≤ ρ W := by linarith
  have hlog0 : 0 ≤ Real.log W := by linarith
  have hρL : ρ W ≤ q.L := by
    have : ρ W * 1 ≤ ρ W * Real.log W := mul_le_mul_of_nonneg_left hlog hρ0
    linarith
  have hL3 : 3 ≤ q.L := by exact_mod_cast hρ3.trans hρL
  have hLL₀ : L₀ ≤ q.L := by exact_mod_cast hρL₀.trans hρL
  have hCAL : CA * Real.log W ≤ (q.L : ℝ) :=
    (mul_le_mul_of_nonneg_right hρCA hlog0).trans hLlog
  have hqlt : q.u < 1 := by
    have := Real.rpow_pos_of_pos hW0 (-3 : ℝ)
    linarith
  obtain ⟨-, hregp⟩ := hchain q.g q.L hL3 hLL₀ q.E hreg steps (hlen.trans hd)
    (fun x hx => ⟨(hadm x hx).1, (hadm x hx).2.1, (hadm x hx).2.2.trans_lt hqlt⟩)
  have hg : p.g = (cmpChain q.L (q.g, q.E) steps).1 := congrArg Prod.fst hpc
  have hE' : p.E = (cmpChain q.L (q.g, q.E) steps).2 := congrArg Prod.snd hpc
  have hregp' : RegBdd C BJ cJ p.L p.g p.E := by
    rw [hL, hg, hE']
    exact incrementInputs_regBdd_mono hregp (le_max_left BJ0 1)
  obtain ⟨hg0, hgC, hE, hroot, hcm⟩ := hregp'
  have hpL3 : 3 ≤ p.L := hL ▸ hL3
  have hp12 : 1 / 2 ≤ p.u := h12 hq12
  have hpu : (W : ℝ) ^ (-3 : ℝ) ≤ 1 - p.u := by linarith
  have H := hW₁ W hWW₁ p.g hg0 hgC p.L hpL3 (by rw [hL]; exact hCAL)
    (by rw [Real.rpow_two, hL]; exact hLW) p.E hE (mRoot p.g p.L p.E) hroot hcm p.u
    (by linarith) hpu a b b'
  simp only [iteratedDeriv_zero] at H
  rw [abs_sub_comm] at H
  have hℓ1 : 1 ≤ ellProp p.g p.L p.u :=
    (scale_facts p.g hg0 W p.L (by omega) (by omega) p.u p.u (by linarith) le_rfl
      (by linarith [Real.rpow_pos_of_pos hW0 (-3 : ℝ)])).1
  have hℓL : ellProp p.g p.L p.u ≤ p.L := min_le_left _ _
  have hℓW : ellProp p.g p.L p.u ≤ (W : ℝ) ^ 2 := by
    have : (p.L : ℝ) ≤ (W : ℝ) ^ 2 := by rw [hL]; exact hLW
    linarith
  have hδ : 0 < 1 - p.u := by linarith [Real.rpow_pos_of_pos hW0 (-3 : ℝ)]
  have hℓ0 : 0 < ellProp p.g p.L p.u := by linarith
  set ℓ := ellProp p.g p.L p.u with hℓ
  have hd0 : (0 : ℝ) ≤ (cycDist b b' : ℝ) := Nat.cast_nonneg _
  have hexp : ∀ x : Fin p.L, Real.exp (-(c * cycDist a x / ℓ)) ≤ 1 := fun x => by
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ c * (cycDist a x : ℝ) / ℓ := by positivity
    linarith
  have hmin : min ((cycDist b b' : ℝ) / ℓ) 1 ≤ (cycDist b b' : ℝ) / ℓ := min_le_left _ _
  have hprefac : 0 ≤ C' / ((1 - p.u) ^ (0 + 1) * ℓ) := by positivity
  have hmain : C' / ((1 - p.u) ^ (0 + 1) * ℓ) * min ((cycDist b b' : ℝ) / ℓ) 1 *
      (Real.exp (-(c * cycDist a b / ℓ)) + Real.exp (-(c * cycDist a b' / ℓ))) ≤
      2 * C' / ((1 - p.u) * ℓ) * ((cycDist b b' : ℝ) / ℓ) := by
    have h2 : Real.exp (-(c * cycDist a b / ℓ)) + Real.exp (-(c * cycDist a b' / ℓ)) ≤ 2 := by
      linarith [hexp b, hexp b']
    have hm0 : 0 ≤ min ((cycDist b b' : ℝ) / ℓ) 1 := le_min (by positivity) zero_le_one
    calc _ ≤ C' / ((1 - p.u) ^ (0 + 1) * ℓ) * ((cycDist b b' : ℝ) / ℓ) * 2 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hmin hprefac) h2 (by positivity)
          positivity
      _ = _ := by rw [zero_add, pow_one]; ring
  have hrem : (W : ℝ) ^ (-(A + 2)) ≤ ℓ⁻¹ * (W : ℝ) ^ (-A) := by
    have hsplit : (W : ℝ) ^ (-(A + 2)) = (W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (-A) := by
      rw [← Real.rpow_add hW0]; ring_nf
    have hW2 : (W : ℝ) ^ (-2 : ℝ) = ((W : ℝ) ^ 2)⁻¹ := by
      rw [Real.rpow_neg hW0.le, Real.rpow_two]
    rw [hsplit, hW2]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hℓ0 hℓW) (Real.rpow_nonneg hW0.le _)
  calc _ ≤ _ := H
    _ ≤ _ := add_le_add hmain hrem

/-- (A.49) [da:eq:mixed-profile-increment] on the reach of the large-coupling base family. -/
theorem incrementInput_large (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) (J : ℕ) :
    ∃ Cκ₀ : ℝ, 1 ≤ Cκ₀ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      IncrementInput (baseLarge κ Cκ CV ρ) J := by
  obtain ⟨Cκ', C', hCκ', hC', hI⟩ := increment_large (κ / 2) (by linarith) (by linarith)
  obtain ⟨Cκc, C'', hCκc, hC''1, hR⟩ := cmpReach_large κ CV hκ hκ2 hCV J
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
  refine ⟨max (Real.sqrt 2 * Cκ') Cκc, hCκc.trans (le_max_right _ _), fun Cκ hCκ ρ hρ => ?_⟩
  refine ⟨C', hC', fun A hA => ?_⟩
  obtain ⟨CA, W₁, hCA, hW₁⟩ := hI A hA
  obtain ⟨W₂, hW₂⟩ := hR Cκ ((le_max_right _ _).trans hCκ) ρ hρ
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hρ.eventually_ge_atTop CA)
  refine ⟨max W₂ (max W₁ (max N 3)), fun W hW d p hd hreach a b b' => ?_⟩
  have hWW₂ : W₂ ≤ W := (le_max_left _ _).trans hW
  have hWW₁ : W₁ ≤ W := ((le_max_left _ _).trans (le_max_right _ _)).trans hW
  have hWN : N ≤ W := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hW
  have hW3 : 3 ≤ W := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hW
  obtain ⟨hg, hE, hroot, -, -, hρL, -, hu, hut⟩ :=
    hW₂ (baseLarge κ Cκ CV ρ) (fun W p hp => hp) W hWW₂ d p hd hreach
  have hgC : Cκ' ≤ p.g := by
    refine hg.trans' ?_
    rw [le_div_iff₀ hs2]
    have := (le_max_left _ _).trans hCκ
    linarith
  have hlog0 : 0 ≤ Real.log W :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ W))
  have hL : CA * p.g ^ 2 * Real.log W ≤ p.L :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hN W hWN) (sq_nonneg _)) hlog0).trans
      hρL
  have hE' : |p.E| ≤ 2 - κ / 2 := hE
  exact hW₁ W hWW₁ p.g hgC p.L hL p.E hE' (mRoot p.g p.L p.E) hroot p.u hu hut a b b'

end LSBA
