import LSBA.Kernel.Defs
import LSBA.Kernel.Scales

/-!
# The finite schedule

The schedule of Appendix C.4 [sec:gc-schedule] in the prefix-closed form (C.47)′
[gc:eq:finite-schedule]: the step times, the number of steps `J = ⌈12N/c₀⌉ + 1`, and the step
bounds.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The schedule (C.47)′ [gc:eq:finite-schedule], i.e. (C.47) [gc:eq:finite-schedule] with `c₀/(4N)`
in place of `c₀/80`:
`s_j = 1 - max{1 - t_*, W^{-jc₀/(4N)}/2}`. -/
def schedTime (W : ℕ) (c₀ N tstar : ℝ) (j : ℕ) : ℝ :=
  1 - max (1 - tstar) ((W : ℝ) ^ (-((j : ℝ) * c₀ / (4 * N))) / 2)

/-- The number of steps `J = ⌈12N/c₀⌉ + 1` of the schedule (C.47)′ [gc:eq:finite-schedule]. -/
def schedSteps (c₀ N : ℝ) : ℕ := ⌈12 * N / c₀⌉₊ + 1

/-- The schedule (C.47)′ [gc:eq:finite-schedule] is prefix-closed: the schedule of the endpoint
`s_i` is the schedule of `t_*` stopped at `i`. -/
theorem schedTime_prefix (W : ℕ) (hW : 1 ≤ W) (c₀ N tstar : ℝ) (hc₀ : 0 < c₀) (hN : 0 < N)
    (i j : ℕ) :
    schedTime W c₀ N (schedTime W c₀ N tstar i) j = schedTime W c₀ N tstar (min i j) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hpos : 0 < 4 * N := by linarith
  have hanti : ∀ k l : ℕ, k ≤ l →
      (W : ℝ) ^ (-((l : ℝ) * c₀ / (4 * N))) / 2 ≤ (W : ℝ) ^ (-((k : ℝ) * c₀ / (4 * N))) / 2 := by
    intro k l hkl
    have hkl' : (k : ℝ) ≤ l := by exact_mod_cast hkl
    have h1 : (k : ℝ) * c₀ / (4 * N) ≤ (l : ℝ) * c₀ / (4 * N) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hkl' hc₀.le) hpos.le
    have h2 := Real.rpow_le_rpow_of_exponent_le hW1 (show -((l : ℝ) * c₀ / (4 * N)) ≤
      -((k : ℝ) * c₀ / (4 * N)) by linarith)
    linarith
  unfold schedTime
  rw [sub_sub_cancel]
  rcases le_total i j with h | h
  · rw [min_eq_left h, max_eq_left (le_trans (hanti i j h) (le_max_right _ _))]
  · rw [min_eq_right h]
    have := hanti j i h
    rw [max_assoc, max_eq_right this]

/-- The schedule (C.47)′ [gc:eq:finite-schedule] runs from `s₀ = 1/2` to `s_J = t_*`, is
nondecreasing, and each step
satisfies `R_j ≤ W^{c₀/(4N)}` and `(5.38)′ [gc:eq:one-step]` with `c = 3c₀/4`, as in Appendix C.4
[sec:gc-schedule]. -/
theorem schedTime_step (W : ℕ) (hW : 2 ≤ W) (c₀ N tstar : ℝ) (hc₀ : 0 < c₀) (hN : 20 ≤ N)
    (ht₁ : 1 / 2 ≤ tstar) (ht₂ : (W : ℝ) ^ (-3 : ℝ) ≤ 1 - tstar) (g : ℝ) (hg : 0 ≤ g) (L : ℕ)
    (hL : 1 ≤ L) (hz : zetaProp g W L tstar ≤ (W : ℝ) ^ (-c₀)) :
    schedTime W c₀ N tstar 0 = 1 / 2 ∧ schedTime W c₀ N tstar (schedSteps c₀ N) = tstar ∧
    ∀ j : ℕ, 1 ≤ j → j ≤ schedSteps c₀ N →
      schedTime W c₀ N tstar (j - 1) ≤ schedTime W c₀ N tstar j ∧
      schedTime W c₀ N tstar j ≤ tstar ∧
      (1 - schedTime W c₀ N tstar (j - 1)) / (1 - schedTime W c₀ N tstar j) ≤
        (W : ℝ) ^ (c₀ / (4 * N)) ∧
      ((1 - schedTime W c₀ N tstar (j - 1)) / (1 - schedTime W c₀ N tstar j)) ^ N *
        zetaProp g W L (schedTime W c₀ N tstar j) ≤ (W : ℝ) ^ (-(3 * c₀ / 4)) := by
  have hN0 : 0 < N := by linarith
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (by omega : 1 ≤ W)
  have hW0 : (0 : ℝ) < W := by linarith
  have hpos : 0 < 4 * N := by linarith
  have hA : 0 < 1 - tstar := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) ht₂
  have hA2 : 1 - tstar ≤ 1 / 2 := by linarith
  -- the quantity `B k = W^{-k c₀/(4N)} / 2`
  have hBle : ∀ k : ℕ, (W : ℝ) ^ (-((k : ℝ) * c₀ / (4 * N))) ≤ 1 := by
    intro k
    apply Real.rpow_le_one_of_one_le_of_nonpos hW1
    have : 0 ≤ (k : ℝ) * c₀ / (4 * N) := by positivity
    linarith
  have hBpos : ∀ k : ℕ, 0 < (W : ℝ) ^ (-((k : ℝ) * c₀ / (4 * N))) := fun k =>
    Real.rpow_pos_of_pos hW0 _
  have hanti : ∀ k l : ℕ, k ≤ l →
      (W : ℝ) ^ (-((l : ℝ) * c₀ / (4 * N))) / 2 ≤ (W : ℝ) ^ (-((k : ℝ) * c₀ / (4 * N))) / 2 := by
    intro k l hkl
    have hkl' : (k : ℝ) ≤ l := by exact_mod_cast hkl
    have h1 : (k : ℝ) * c₀ / (4 * N) ≤ (l : ℝ) * c₀ / (4 * N) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hkl' hc₀.le) hpos.le
    have h2 := Real.rpow_le_rpow_of_exponent_le hW1 (show -((l : ℝ) * c₀ / (4 * N)) ≤
      -((k : ℝ) * c₀ / (4 * N)) by linarith)
    linarith
  have hmax_le : ∀ k : ℕ, max (1 - tstar) ((W : ℝ) ^ (-((k : ℝ) * c₀ / (4 * N))) / 2) ≤ 1 / 2 := by
    intro k
    exact max_le hA2 (by linarith [hBle k])
  have hmax_ge : ∀ k : ℕ, 1 - tstar ≤
      max (1 - tstar) ((W : ℝ) ^ (-((k : ℝ) * c₀ / (4 * N))) / 2) := fun k => le_max_left _ _
  refine ⟨?_, ?_, ?_⟩
  · unfold schedTime
    simp only [Nat.cast_zero, zero_mul, zero_div, neg_zero, Real.rpow_zero]
    rw [max_eq_right (by linarith)]
    norm_num
  · -- `s_J = t_*`
    have hJ : 12 * N / c₀ + 1 ≤ ((schedSteps c₀ N : ℕ) : ℝ) := by
      unfold schedSteps
      push_cast
      linarith [Nat.le_ceil (12 * N / c₀)]
    have hJa : 3 ≤ ((schedSteps c₀ N : ℕ) : ℝ) * c₀ / (4 * N) := by
      rw [le_div_iff₀ hpos]
      have h1 : 12 * N / c₀ * c₀ = 12 * N := by field_simp
      nlinarith [mul_le_mul_of_nonneg_right hJ hc₀.le]
    have h3 : (W : ℝ) ^ (-((schedSteps c₀ N : ℝ) * c₀ / (4 * N))) ≤ (W : ℝ) ^ (-3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
    unfold schedTime
    rw [max_eq_left (by linarith [hBpos (schedSteps c₀ N)])]
    ring
  · intro j hj1 hjJ
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hs : ∀ k : ℕ, schedTime W c₀ N tstar k =
        1 - max (1 - tstar) ((W : ℝ) ^ (-((k : ℝ) * c₀ / (4 * N))) / 2) := fun k => rfl
    set Bm := (W : ℝ) ^ (-((m : ℝ) * c₀ / (4 * N))) / 2 with hBm
    set Bm1 := (W : ℝ) ^ (-(((m + 1 : ℕ) : ℝ) * c₀ / (4 * N))) / 2 with hBm1
    have hBm1m : Bm1 ≤ Bm := hanti m (m + 1) (Nat.le_succ m)
    have hden : 1 - tstar ≤ max (1 - tstar) Bm1 := le_max_left _ _
    have hdenpos : 0 < max (1 - tstar) Bm1 := lt_of_lt_of_le hA hden
    have h1 : 1 - schedTime W c₀ N tstar m = max (1 - tstar) Bm := by rw [hs m]; ring
    have h2 : 1 - schedTime W c₀ N tstar (m + 1) = max (1 - tstar) Bm1 := by rw [hs (m + 1)]; ring
    have hratio_nonneg : 0 ≤ max (1 - tstar) Bm / max (1 - tstar) Bm1 :=
      div_nonneg (le_trans hA.le (le_max_left _ _)) hdenpos.le
    -- monotonicity
    have hmono : schedTime W c₀ N tstar m ≤ schedTime W c₀ N tstar (m + 1) := by
      rw [hs m, hs (m + 1)]
      have : max (1 - tstar) Bm1 ≤ max (1 - tstar) Bm := max_le_max le_rfl hBm1m
      linarith
    have hle_t : schedTime W c₀ N tstar (m + 1) ≤ tstar := by
      rw [hs (m + 1)]; linarith [hmax_ge (m + 1)]
    -- the one-step ratio
    have hrW : (1 : ℝ) ≤ (W : ℝ) ^ (c₀ / (4 * N)) :=
      Real.one_le_rpow hW1 (by positivity)
    have hB_eq : Bm = (W : ℝ) ^ (c₀ / (4 * N)) * Bm1 := by
      rw [hBm, hBm1]
      have : (W : ℝ) ^ (-((m : ℝ) * c₀ / (4 * N))) =
          (W : ℝ) ^ (c₀ / (4 * N)) * (W : ℝ) ^ (-(((m + 1 : ℕ) : ℝ) * c₀ / (4 * N))) := by
        rw [← Real.rpow_add hW0]
        congr 1
        push_cast
        ring
      rw [this]; ring
    have hratio : max (1 - tstar) Bm / max (1 - tstar) Bm1 ≤ (W : ℝ) ^ (c₀ / (4 * N)) := by
      rw [div_le_iff₀ hdenpos]
      refine max_le ?_ ?_
      · calc 1 - tstar ≤ max (1 - tstar) Bm1 := hden
          _ ≤ (W : ℝ) ^ (c₀ / (4 * N)) * max (1 - tstar) Bm1 :=
            le_mul_of_one_le_left hdenpos.le hrW
          _ = _ := by ring
      · rw [hB_eq]
        exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)
    refine ⟨hmono, hle_t, ?_, ?_⟩
    · rw [h1, h2]; exact hratio
    · rw [h1, h2]
      have hRN : (max (1 - tstar) Bm / max (1 - tstar) Bm1) ^ N ≤ (W : ℝ) ^ (c₀ / 4) := by
        calc (max (1 - tstar) Bm / max (1 - tstar) Bm1) ^ N
            ≤ ((W : ℝ) ^ (c₀ / (4 * N))) ^ N :=
              Real.rpow_le_rpow hratio_nonneg hratio hN0.le
          _ = (W : ℝ) ^ (c₀ / (4 * N) * N) := (Real.rpow_mul hW0.le _ _).symm
          _ = (W : ℝ) ^ (c₀ / 4) := by
            congr 1; field_simp
      have ht1 : tstar < 1 := by linarith
      have hsj0 : 0 ≤ schedTime W c₀ N tstar (m + 1) := by
        rw [hs (m + 1)]; linarith [hmax_le (m + 1)]
      obtain ⟨-, -, -, hζ0, hζmono, -⟩ :=
        scale_facts g hg W L (by omega) hL (schedTime W c₀ N tstar (m + 1)) tstar hsj0 hle_t ht1
      have hζ : zetaProp g W L (schedTime W c₀ N tstar (m + 1)) ≤ (W : ℝ) ^ (-c₀) :=
        le_trans hζmono hz
      have hζnn : 0 ≤ zetaProp g W L (schedTime W c₀ N tstar (m + 1)) :=
        le_trans (inv_nonneg.mpr (by positivity)) hζ0
      calc (max (1 - tstar) Bm / max (1 - tstar) Bm1) ^ N *
            zetaProp g W L (schedTime W c₀ N tstar (m + 1))
          ≤ (W : ℝ) ^ (c₀ / 4) * (W : ℝ) ^ (-c₀) :=
            mul_le_mul hRN hζ hζnn (Real.rpow_nonneg hW0.le _)
        _ = (W : ℝ) ^ (-(3 * c₀ / 4)) := by
          rw [← Real.rpow_add hW0]
          congr 1; ring

end LSBA
