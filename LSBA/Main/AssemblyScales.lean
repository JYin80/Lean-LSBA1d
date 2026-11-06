import LSBA.Volume.LowerVolume

/-!
# Scales of the lower-bound assembly

The deterministic bookkeeping of the proof of the lower bound in Theorem 1.4 [thm:main]: outside
the region (2.4) [uv:eq:haar-lower-region] the cycle is long and the coupling is at least
`W^{-1/2}`; in the region `g ≥ C`, `L ≤ c W^τ g²` the threshold of (2.12)
[uv:eq:lower-regions-output] is below that of Lemma 2.4 [uv:lem:short-spreading]; the cycle length
`L_c` and the height `η_c` of Theorem 2.2 [uv:lem:lower-volume], (2.5)
[uv:eq:lower-volume-scales], lie in the volume ranges of the moment bounds; the volume rates
diverge; and exponential tails are polynomially small.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- `W ≤ ℓ_{W,g}`, (1.7) [eq:scales]. -/
private lemma assemblyScales_ellScale_ge (W : ℕ) (g : ℝ) : (W : ℝ) ≤ ellScale W g :=
  le_max_left _ _

/-- `ℓ_{W,g,L} ≤ W L`, (1.7) [eq:scales]. -/
private lemma assemblyScales_ellStar_le (W L : ℕ) (g : ℝ) : ellStar W L g ≤ (W : ℝ) * L :=
  min_le_left _ _

/-- `W^{1+τ}/8 < ℓ_{W,g,L}` forces `W^τ/8 < L`. -/
private lemma assemblyScales_L_gt {W : ℕ} (hW : 1 ≤ W) (L : ℕ) {g τ : ℝ}
    (hout : (W : ℝ) ^ (1 + τ) / 8 < ellStar W L g) : (W : ℝ) ^ τ / 8 < L := by
  have hw : (0 : ℝ) < W := Nat.cast_pos.2 hW
  have h1 : (W : ℝ) ^ (1 + τ) = W * (W : ℝ) ^ τ := by
    rw [Real.rpow_add hw, Real.rpow_one]
  have h2 := lt_of_lt_of_le hout (assemblyScales_ellStar_le W L g)
  rw [h1] at h2
  have h3 : (W : ℝ) * ((W : ℝ) ^ τ / 8) < W * L := by
    calc (W : ℝ) * ((W : ℝ) ^ τ / 8) = W * (W : ℝ) ^ τ / 8 := by ring
      _ < _ := h2
  exact lt_of_mul_lt_mul_left h3 hw.le

/-- The two-sided bound `4ℓ_{W,g}/W^ν + 1 ≤ 2R + 1 < 4ℓ_{W,g}/W^ν + 3` for `R = ⌈2ℓ_{W,g}/W^ν⌉`,
(2.5) [uv:eq:lower-volume-scales]. -/
private lemma assemblyScales_R_bounds {W : ℕ} (hW : 1 ≤ W) (g ν : ℝ) :
    4 * ellScale W g / (W : ℝ) ^ ν + 1 ≤ ((2 * volR W g ν + 1 : ℕ) : ℝ) ∧
      ((2 * volR W g ν + 1 : ℕ) : ℝ) < 4 * ellScale W g / (W : ℝ) ^ ν + 3 := by
  have hw : (0 : ℝ) < W := Nat.cast_pos.2 hW
  have hq : 2 / ((W : ℝ) ^ ν / ellScale W g) = 2 * ellScale W g / (W : ℝ) ^ ν := by
    rw [div_div_eq_mul_div]
  have hwν : 0 < (W : ℝ) ^ ν := Real.rpow_pos_of_pos hw ν
  have hℓ : 0 < ellScale W g := lt_of_lt_of_le hw (assemblyScales_ellScale_ge W g)
  have h0 : 0 ≤ 2 / ((W : ℝ) ^ ν / ellScale W g) := by positivity
  have hlo : 2 / ((W : ℝ) ^ ν / ellScale W g) ≤ (volR W g ν : ℝ) := Nat.le_ceil _
  have hhi : (volR W g ν : ℝ) < 2 / ((W : ℝ) ^ ν / ellScale W g) + 1 := Nat.ceil_lt_add_one h0
  rw [hq] at hlo hhi
  have e : 4 * ellScale W g / (W : ℝ) ^ ν = 2 * (2 * ellScale W g / (W : ℝ) ^ ν) := by ring
  push_cast
  constructor <;> linarith

/-- `W^s/log W` tends to infinity for `s > 0`. -/
private lemma assemblyScales_tendsto_rpow_div_log {s : ℝ} (hs : 0 < s) :
    Tendsto (fun W : ℕ => (W : ℝ) ^ s / Real.log W) atTop atTop := by
  have h0 : Tendsto (fun x : ℝ => Real.log x / x ^ s) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨(isLittleO_log_rpow_atTop hs).tendsto_div_nhds_zero, ?_⟩
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact div_pos (Real.log_pos hx) (Real.rpow_pos_of_pos (by linarith) s)
  have h2 : Tendsto (fun x : ℝ => x ^ s / Real.log x) atTop atTop := by
    refine h0.inv_tendsto_nhdsGT_zero.congr (fun x => ?_)
    simp [inv_div]
  exact h2.comp tendsto_natCast_atTop_atTop

/-- Outside the region (2.4) [uv:eq:haar-lower-region] with `c₀ = 1/8`, and for `W^τ ≥ 8`:
`L > W^τ/8` and `g ≥ W^{-1/2}`. -/
theorem haar_exclusion {W : ℕ} (hW : 1 ≤ W) (L : ℕ) {g τ : ℝ} (hg : 0 ≤ g)
    (h8 : 8 ≤ (W : ℝ) ^ τ) (hout : (W : ℝ) ^ (1 + τ) / 8 < ellStar W L g) :
    (W : ℝ) ^ τ / 8 < L ∧ (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ g := by
  have hw : (0 : ℝ) < W := Nat.cast_pos.2 hW
  refine ⟨assemblyScales_L_gt hW L hout, ?_⟩
  have h1 : (W : ℝ) ^ (1 + τ) = W * (W : ℝ) ^ τ := by
    rw [Real.rpow_add hw, Real.rpow_one]
  have hW8 : (W : ℝ) ≤ (W : ℝ) ^ (1 + τ) / 8 := by
    rw [h1]; nlinarith
  have hlt : (W : ℝ) ^ (1 + τ) / 8 < ellScale W g := lt_of_lt_of_le hout (min_le_right _ _)
  have hsq : (W : ℝ) < (W : ℝ) ^ 2 * g ^ 2 := by
    by_contra hcon
    have hcon := not_lt.1 hcon
    have hmax : ellScale W g = W := max_eq_left hcon
    rw [hmax] at hlt
    linarith
  have hg2 : 1 ≤ (W : ℝ) * g ^ 2 := by
    have h3 : (W : ℝ) * 1 < W * ((W : ℝ) * g ^ 2) := by
      calc (W : ℝ) * 1 = W := mul_one _
        _ < (W : ℝ) ^ 2 * g ^ 2 := hsq
        _ = W * ((W : ℝ) * g ^ 2) := by ring
    exact (lt_of_mul_lt_mul_left h3 hw.le).le
  have hsqrt : ((W : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (W : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw.le]
    norm_num
    exact Real.rpow_neg_one _
  have hle : ((W : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 ≤ g ^ 2 := by
    rw [hsqrt, inv_eq_one_div, div_le_iff₀ hw]
    linarith
  exact (pow_le_pow_iff_left₀ (Real.rpow_nonneg hw.le _) hg (by norm_num)).1 hle

/-- In the region `L ≤ c W^τ g²` with `g ≥ 1` and `c W^τ ≥ 1`, the threshold
`W^{-τ} ℓ_{W,g,L}` in the definition of the count `B_−` of (2.12) [uv:eq:lower-regions-output]
is at most the threshold `c W min{L, g²}` of (2.10) [uv:eq:constant-scattering-outline]. -/
theorem shortRegion_threshold {W : ℕ} (hW : 1 ≤ W) (L : ℕ) {g τ c : ℝ} (hg : 1 ≤ g)
    (hc : 1 ≤ c * (W : ℝ) ^ τ) (hL : (L : ℝ) ≤ c * (W : ℝ) ^ τ * g ^ 2) :
    (W : ℝ) ^ (-τ) * ellStar W L g ≤ c * W * min (L : ℝ) (g ^ 2) := by
  have _ := hg
  have hw : (0 : ℝ) < W := Nat.cast_pos.2 hW
  have hwτ : 0 < (W : ℝ) ^ τ := Real.rpow_pos_of_pos hw τ
  have hc0 : 0 < c := by
    by_contra h
    have h' := not_lt.1 h
    nlinarith
  have hneg : (W : ℝ) ^ (-τ) * (W : ℝ) ^ τ = 1 := by
    rw [← Real.rpow_add hw]; simp
  have hnegpos : 0 < (W : ℝ) ^ (-τ) := Real.rpow_pos_of_pos hw _
  have hnegc : (W : ℝ) ^ (-τ) ≤ c := by
    calc (W : ℝ) ^ (-τ) = (W : ℝ) ^ (-τ) * 1 := (mul_one _).symm
      _ ≤ (W : ℝ) ^ (-τ) * (c * (W : ℝ) ^ τ) := by gcongr
      _ = c * ((W : ℝ) ^ (-τ) * (W : ℝ) ^ τ) := by ring
      _ = c := by rw [hneg, mul_one]
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have h0 : (W : ℝ) ^ (-τ) * ellStar W L g ≤ (W : ℝ) ^ (-τ) * ((W : ℝ) * L) := by
    gcongr
    exact assemblyScales_ellStar_le W L g
  have hcw : 0 ≤ c * (W : ℝ) := by positivity
  rw [mul_min_of_nonneg _ _ hcw]
  refine le_trans h0 (le_min ?_ ?_)
  · calc (W : ℝ) ^ (-τ) * ((W : ℝ) * L) ≤ c * ((W : ℝ) * L) := by gcongr
      _ = c * W * L := by ring
  · calc (W : ℝ) ^ (-τ) * ((W : ℝ) * L)
        ≤ (W : ℝ) ^ (-τ) * ((W : ℝ) * (c * (W : ℝ) ^ τ * g ^ 2)) := by gcongr
      _ = c * W * g ^ 2 * ((W : ℝ) ^ (-τ) * (W : ℝ) ^ τ) := by ring
      _ = c * W * g ^ 2 := by rw [hneg, mul_one]

/-- The cycle length `L_c` of Theorem 2.2 [uv:lem:lower-volume], (2.5)
[uv:eq:lower-volume-scales], outside the region (2.4) [uv:eq:haar-lower-region] and for
`0 ≤ g ≤ M`: `min{W^τ/8, 4W^{1-ν}} ≤ L_c ≤ W²`. -/
theorem volLc_small {W : ℕ} (hW : 3 ≤ W) (L : ℕ) {g τ ν M : ℝ} (hg : 0 ≤ g) (hgM : g ≤ M)
    (hM : 1 ≤ M) (hνM : 8 * M ^ 2 ≤ (W : ℝ) ^ ν)
    (hout : (W : ℝ) ^ (1 + τ) / 8 < ellStar W L g) :
    min ((W : ℝ) ^ τ / 8) (4 * (W : ℝ) ^ (1 - ν)) ≤ volLc W L g ν ∧
      (volLc W L g ν : ℝ) ≤ (W : ℝ) ^ 2 := by
  have hW1 : 1 ≤ W := by omega
  have hw : (0 : ℝ) < W := Nat.cast_pos.2 hW1
  have hw3 : (3 : ℝ) ≤ W := by exact_mod_cast hW
  have hwν : 0 < (W : ℝ) ^ ν := Real.rpow_pos_of_pos hw ν
  obtain ⟨hlo, hhi⟩ := assemblyScales_R_bounds hW1 g ν
  have hLc : (volLc W L g ν : ℝ) = min (L : ℝ) ((2 * volR W g ν + 1 : ℕ) : ℝ) := by
    unfold volLc
    rw [Nat.cast_min]
  constructor
  · rw [hLc]
    refine le_min (le_trans (min_le_left _ _) (assemblyScales_L_gt hW1 L hout).le)
      (le_trans (min_le_right _ _) (le_trans ?_ hlo))
    have h1 : (W : ℝ) ^ (1 - ν) = W / (W : ℝ) ^ ν := by
      rw [Real.rpow_sub hw, Real.rpow_one]
    have h2 : 4 * ((W : ℝ) / (W : ℝ) ^ ν) ≤ 4 * ellScale W g / (W : ℝ) ^ ν := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right
        (by linarith [assemblyScales_ellScale_ge W g]) hwν.le
    rw [h1]
    linarith
  · rw [hLc]
    refine le_trans (min_le_right _ _) (le_trans hhi.le ?_)
    have hℓ : ellScale W g ≤ (W : ℝ) ^ 2 * M ^ 2 := by
      refine max_le ?_ ?_
      · have hM2 : 1 ≤ M ^ 2 := one_le_pow₀ hM
        have hw1 : (1 : ℝ) ≤ W := by linarith
        nlinarith [mul_nonneg hw.le (sub_nonneg.2 hw1),
          mul_nonneg (sq_nonneg (W : ℝ)) (sub_nonneg.2 hM2)]
      · have : g ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hg hgM 2
        nlinarith [sq_nonneg (W : ℝ)]
    have hdiv : 4 * ellScale W g / (W : ℝ) ^ ν ≤ (W : ℝ) ^ 2 / 2 := by
      rw [div_le_iff₀ hwν]
      calc 4 * ellScale W g ≤ 4 * ((W : ℝ) ^ 2 * M ^ 2) := by linarith
        _ = (W : ℝ) ^ 2 / 2 * (8 * M ^ 2) := by ring
        _ ≤ (W : ℝ) ^ 2 / 2 * (W : ℝ) ^ ν := by gcongr
    nlinarith

/-- The cycle length `L_c` of Theorem 2.2 [uv:lem:lower-volume], (2.5)
[uv:eq:lower-volume-scales], outside the region `L ≤ c W^τ g²` and for
`g ≥ 1`: `g² W^{τ/2} ≤ L_c ≤ g² W²`. -/
theorem volLc_large {W : ℕ} (hW : 3 ≤ W) (L : ℕ) {g τ ν c : ℝ} (hg : 1 ≤ g)
    (hτ : 0 < τ ∧ τ < 1) (hν : 0 < ν ∧ ν < 1) (h8 : 8 ≤ (W : ℝ) ^ ν)
    (hc : 1 ≤ c * (W : ℝ) ^ (τ / 2)) (hout : c * (W : ℝ) ^ τ * g ^ 2 < L) :
    g ^ 2 * (W : ℝ) ^ (τ / 2) ≤ volLc W L g ν ∧ (volLc W L g ν : ℝ) ≤ g ^ 2 * (W : ℝ) ^ 2 := by
  have hW1 : 1 ≤ W := by omega
  have hw : (0 : ℝ) < W := Nat.cast_pos.2 hW1
  have hw3 : (3 : ℝ) ≤ W := by exact_mod_cast hW
  have hw1 : (1 : ℝ) ≤ W := by linarith
  have hwν : 0 < (W : ℝ) ^ ν := Real.rpow_pos_of_pos hw ν
  have hg2 : 1 ≤ g ^ 2 := one_le_pow₀ hg
  obtain ⟨hlo, hhi⟩ := assemblyScales_R_bounds hW1 g ν
  have hℓ : ellScale W g = (W : ℝ) ^ 2 * g ^ 2 := by
    apply max_eq_right
    nlinarith
  rw [hℓ] at hlo hhi
  have hLc : (volLc W L g ν : ℝ) = min (L : ℝ) ((2 * volR W g ν + 1 : ℕ) : ℝ) := by
    unfold volLc
    rw [Nat.cast_min]
  constructor
  · rw [hLc]
    refine le_min ?_ (le_trans ?_ hlo)
    · have hp : 0 < (W : ℝ) ^ (τ / 2) := Real.rpow_pos_of_pos hw _
      have hτ2 : (W : ℝ) ^ τ = (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (τ / 2) := by
        rw [← Real.rpow_add hw]; ring_nf
      have h1 : g ^ 2 * (W : ℝ) ^ (τ / 2) ≤ c * (W : ℝ) ^ τ * g ^ 2 := by
        rw [hτ2]
        have : (W : ℝ) ^ (τ / 2) * 1 ≤ (W : ℝ) ^ (τ / 2) * (c * (W : ℝ) ^ (τ / 2)) := by gcongr
        nlinarith [sq_nonneg g]
      linarith
    · have h1 : (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ ν ≤ (W : ℝ) ^ 2 := by
        rw [← Real.rpow_add hw]
        calc (W : ℝ) ^ (τ / 2 + ν) ≤ (W : ℝ) ^ (2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hw1 (by linarith [hτ.2, hν.2])
          _ = (W : ℝ) ^ 2 := by norm_cast
      have h2 : g ^ 2 * (W : ℝ) ^ (τ / 2) ≤ 4 * ((W : ℝ) ^ 2 * g ^ 2) / (W : ℝ) ^ ν := by
        rw [le_div_iff₀ hwν]
        have h3 := mul_le_mul_of_nonneg_left h1 (sq_nonneg g)
        nlinarith [mul_nonneg (sq_nonneg g) (sq_nonneg (W : ℝ))]
      linarith
  · rw [hLc]
    refine le_trans (min_le_right _ _) (le_trans hhi.le ?_)
    have hdiv : 4 * ((W : ℝ) ^ 2 * g ^ 2) / (W : ℝ) ^ ν ≤ g ^ 2 * (W : ℝ) ^ 2 / 2 := by
      rw [div_le_iff₀ hwν]
      calc 4 * ((W : ℝ) ^ 2 * g ^ 2) = g ^ 2 * (W : ℝ) ^ 2 / 2 * 8 := by ring
        _ ≤ g ^ 2 * (W : ℝ) ^ 2 / 2 * (W : ℝ) ^ ν := by gcongr
    nlinarith [mul_nonneg (sq_nonneg g) (sq_nonneg (W : ℝ))]

/-- The moment height `η_c = W^ν/ℓ_{W,g,L_c}` of Theorem 2.2 [uv:lem:lower-volume] satisfies
`0 < η_c ≤ W^{ν-1}`. -/
theorem volEta_pos_le {W : ℕ} (hW : 1 ≤ W) {L : ℕ} (hL : 1 ≤ L) (g ν : ℝ) :
    0 < volEta W L g ν ∧ volEta W L g ν ≤ (W : ℝ) ^ (ν - 1) := by
  have hw : (0 : ℝ) < W := Nat.cast_pos.2 hW
  have hwν : 0 < (W : ℝ) ^ ν := Real.rpow_pos_of_pos hw ν
  have hLc : 1 ≤ volLc W L g ν := by
    unfold volLc
    exact Nat.le_min.2 ⟨hL, by omega⟩
  have hstar : (W : ℝ) ≤ ellStar W (volLc W L g ν) g := by
    refine le_min ?_ (assemblyScales_ellScale_ge W g)
    have : (1 : ℝ) ≤ (volLc W L g ν : ℝ) := by exact_mod_cast hLc
    nlinarith
  unfold volEta
  refine ⟨div_pos hwν (lt_of_lt_of_le hw hstar), ?_⟩
  rw [Real.rpow_sub_one hw.ne']
  exact div_le_div_of_nonneg_left hwν.le hw hstar

/-- The volume rate `min{W^τ/8, 4W^{1-ν}}/log W` of the small and bounded coupling ranges tends
to infinity. -/
theorem tendsto_min_rpow_div_log {τ ν : ℝ} (hτ : 0 < τ) (hν : ν < 1) :
    Tendsto (fun W : ℕ => min ((W : ℝ) ^ τ / 8) (4 * (W : ℝ) ^ (1 - ν)) / Real.log W)
      atTop atTop := by
  have hs : 0 < min τ (1 - ν) := lt_min hτ (by linarith)
  have h1 := (assemblyScales_tendsto_rpow_div_log hs).atTop_div_const (r := 8) (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ h1
  filter_upwards [eventually_ge_atTop 2] with W hW
  have hw1 : (1 : ℝ) ≤ W := by exact_mod_cast (by omega : 1 ≤ W)
  have hlog : 0 < Real.log W := Real.log_pos (by exact_mod_cast (by omega : 1 < W))
  have hnn : 0 ≤ (W : ℝ) ^ min τ (1 - ν) := by positivity
  have hmin : (W : ℝ) ^ min τ (1 - ν) / 8 ≤ min ((W : ℝ) ^ τ / 8) (4 * (W : ℝ) ^ (1 - ν)) := by
    refine le_min ?_ ?_
    · have := Real.rpow_le_rpow_of_exponent_le hw1 (min_le_left τ (1 - ν))
      linarith
    · have := Real.rpow_le_rpow_of_exponent_le hw1 (min_le_right τ (1 - ν))
      linarith
  change (W : ℝ) ^ min τ (1 - ν) / Real.log W / 8 ≤
    min ((W : ℝ) ^ τ / 8) (4 * (W : ℝ) ^ (1 - ν)) / Real.log W
  rw [div_right_comm]
  exact div_le_div_of_nonneg_right hmin hlog.le

/-- `W^s/log W` tends to infinity for `s > 0`. -/
theorem tendsto_rpow_div_log {s : ℝ} (hs : 0 < s) :
    Tendsto (fun W : ℕ => (W : ℝ) ^ s / Real.log W) atTop atTop := by
  exact assemblyScales_tendsto_rpow_div_log hs

/-- An exponential tail `C e^{-cW}` is at most `W^{-D}` for large `W`. -/
theorem exp_tail_le_rpow (C c D : ℝ) (hc : 0 < c) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → C * Real.exp (-c * W) ≤ (W : ℝ) ^ (-D) := by
  have h0 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero D c hc).const_mul C
  rw [mul_zero] at h0
  have h1 : ∀ᶠ x : ℝ in atTop, C * (x ^ D * Real.exp (-c * x)) < 1 :=
    h0.eventually (Iio_mem_nhds one_pos)
  have h2 : ∀ᶠ W : ℕ in atTop, 1 ≤ W ∧ C * ((W : ℝ) ^ D * Real.exp (-c * W)) < 1 :=
    (eventually_ge_atTop 1).and (tendsto_natCast_atTop_atTop.eventually h1)
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.1 h2
  refine ⟨W₀, fun W hW => ?_⟩
  obtain ⟨hW1, hlt⟩ := hW₀ W hW
  have hw : (0 : ℝ) < W := Nat.cast_pos.2 hW1
  have hp : 0 < (W : ℝ) ^ (-D) := Real.rpow_pos_of_pos hw _
  have hD : (W : ℝ) ^ D ≠ 0 := (Real.rpow_pos_of_pos hw D).ne'
  have hid : C * Real.exp (-c * W) =
      (C * ((W : ℝ) ^ D * Real.exp (-c * W))) * (W : ℝ) ^ (-D) := by
    rw [Real.rpow_neg hw.le]
    field_simp
  rw [hid]
  calc (C * ((W : ℝ) ^ D * Real.exp (-c * W))) * (W : ℝ) ^ (-D) ≤ 1 * (W : ℝ) ^ (-D) := by
        gcongr
    _ = (W : ℝ) ^ (-D) := one_mul _

end LSBA
