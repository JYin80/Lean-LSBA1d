import Mathlib

/-!
# The parameters and levels of the construction

The fixed lengths and exponents of Section 9.4.1 [su:sec:retained-geometry] and the levels of the
cutoff of Section 9.4.4 [su:sec:cutoff-estimates]. Regime (i) of Lemma 8.12
[up:lem:small-contraction], (9.54) [su:eq:packet2] and (9.41) [su:eq:construction-threshold]:
`q = 5 + ⌈25600 ε⁻¹ (40 + β)⌉`, `p = 2 (1 - ε/6400)/(q - 5)`, `t = W^{-40} g^{-q}`, the output
scale `v_min = g^{-(q-5)} W^{-3ε/800} ‖P v_4‖` of (9.67) [su:eq:output-cutoff-scale], the overlap
level `g² W^{3ε/200}` of (9.79) [su:eq:cuts], the rank level `2 t^{-p} W^{1+ε/3200}` and the power
`k = ⌈1/α⌉` of the compatibility cut (9.83) [su:eq:compatibility-cutoff]. Regime (ii), (9.62)
[nc:eq:parameters] and (9.61) [nc:eq:buffer-scale]: `q = 5 + ⌈10/θ⌉`, `p = 2 (1 - θ/4)/(q - 5)`,
`t = W^{-30 + (1-2θ)(q-6)/2}`, `υ = W^{-1+2θ}`, `v_min = υ^{-(q-5)/2} W^{-4θ} ‖v_4‖`, the overlap
level `W^{-1+14θ}` of (9.80) [nc:eq:sourcecuts] and the rank level `2 t^{-p} W^{1+θ/4}`.

The level rows: the rank rows (9.55) [su:eq:rank] and (9.63) [nc:eq:dimension]; the matching
error (9.70) [su:eq:error] at the output scale; and the product of the error with the output
derivative ratio (9.72) [su:eq:output-derivative-ratio], which bounds (9.77)
[su:eq:normalization-derivative-bound].
-/

open Real

noncomputable section

namespace LSBA

/-- The levels of the cutoff: the threshold `t = t_cut`, the output factor `κ` with
`v_min = κ ‖P v_4‖`, the overlap level, the rank level, the gap level for `(A* A - t²)⁻¹` and the
power of the compatibility cut. -/
structure CutLevels where
  /-- the threshold of (9.41) [su:eq:construction-threshold] -/
  t : ℝ
  /-- the output factor `κ`, `v_min = κ ‖P v_4‖` -/
  kOut : ℝ
  /-- the level of `‖P v_4‖⁻² ‖Q v_4‖²` -/
  Lov : ℝ
  /-- the level of the rank surrogate -/
  Lrk : ℝ
  /-- the level of `‖(A* A - t²)⁻¹‖²_HS` -/
  Lgap : ℝ
  /-- the power of the compatibility cut -/
  kP : ℕ

/-- The local length of regime (i), (9.54) [su:eq:packet2]. -/
def qWeak (β ε : ℝ) : ℕ := 5 + ⌈25600 / ε * (40 + β)⌉₊

/-- The moment exponent of regime (i), (9.54) [su:eq:packet2]. -/
def pWeak (β ε : ℝ) : ℝ := 2 * (1 - ε / 6400) / (⌈25600 / ε * (40 + β)⌉₊ : ℝ)

/-- The levels of regime (i) at `g = W^{-a}`: `t = W^{-40} g^{-q}`, `κ = g^{-(q-5)} W^{-3ε/800}`,
`g² W^{3ε/200}`, `2 t^{-p} W^{1+ε/3200}`, the gap level `L`, and `k = ⌈1/α⌉`. -/
def levelsWeak (W : ℕ) (g α β ε L : ℝ) : CutLevels where
  t := (W : ℝ) ^ (-40 : ℝ) * (g ^ qWeak β ε)⁻¹
  kOut := (g ^ (qWeak β ε - 5))⁻¹ * (W : ℝ) ^ (-(3 * ε / 800))
  Lov := g ^ 2 * (W : ℝ) ^ (3 * ε / 200)
  Lrk := 2 * ((W : ℝ) ^ (-40 : ℝ) * (g ^ qWeak β ε)⁻¹) ^ (-pWeak β ε) * (W : ℝ) ^ (1 + ε / 3200)
  Lgap := L
  kP := ⌈1 / α⌉₊

/-- The local length of regime (ii), (9.62) [nc:eq:parameters]. -/
def qCrit (θ : ℝ) : ℕ := 5 + ⌈10 / θ⌉₊

/-- The moment exponent of regime (ii), (9.62) [nc:eq:parameters]. -/
def pCrit (θ : ℝ) : ℝ := 2 * (1 - θ / 4) / (⌈10 / θ⌉₊ : ℝ)

/-- The levels of regime (ii): `t = W^{-30 + (1-2θ)(q-6)/2}`, `κ = υ^{-(q-5)/2} W^{-4θ}` with
`υ = W^{-1+2θ}`, `W^{-1+14θ}`, `2 t^{-p} W^{1+θ/4}`, the gap level `L`, and `k = 1`. -/
def levelsCrit (W : ℕ) (θ L : ℝ) : CutLevels where
  t := (W : ℝ) ^ (-30 + (1 - 2 * θ) * ((qCrit θ : ℝ) - 6) / 2)
  kOut := ((W : ℝ) ^ (-1 + 2 * θ)) ^ (-((qCrit θ : ℝ) - 5) / 2) * (W : ℝ) ^ (-(4 * θ))
  Lov := (W : ℝ) ^ (-1 + 14 * θ)
  Lrk := 2 * ((W : ℝ) ^ (-30 + (1 - 2 * θ) * ((qCrit θ : ℝ) - 6) / 2)) ^ (-pCrit θ) *
    (W : ℝ) ^ (1 + θ / 4)
  Lgap := L
  kP := 1

/-- Eventually in `W` the power `W^c` is at least `K`, for `c > 0`. -/
private lemma cutLevels_eventually_ge (c K : ℝ) (hc : 0 < c) :
    ∀ᶠ W : ℕ in Filter.atTop, K ≤ (W : ℝ) ^ c :=
  ((tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop K

/-- A power `w^x` with `x ≤ -c` is at most `K⁻¹` when `K ≤ w^c`. -/
private lemma cutLevels_rpow_le_inv {w x c K : ℝ} (hw : 1 ≤ w) (hK : 0 < K) (hx : x ≤ -c)
    (hc : K ≤ w ^ c) : w ^ x ≤ K⁻¹ := by
  have hw0 : 0 < w := by linarith
  calc w ^ x ≤ w ^ (-c) := Real.rpow_le_rpow_of_exponent_le hw hx
    _ = (w ^ c)⁻¹ := Real.rpow_neg hw0.le c
    _ ≤ K⁻¹ := inv_anti₀ hK hc

/-- A natural power is the real power. -/
private lemma cutLevels_pow_eq (w : ℝ) (n : ℕ) : w ^ n = w ^ (n : ℝ) :=
  (Real.rpow_natCast w n).symm

/-- A square of a real power. -/
private lemma cutLevels_rpow_sq {w : ℝ} (hw : 0 ≤ w) (x : ℝ) : (w ^ x) ^ 2 = w ^ (2 * x) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hw]
  congr 1
  push_cast
  ring

/-- The three matching rows of both regimes, for `t = w^τ`, `κ = w^k` and a quantity `G` playing
`w⁶ g^{-2(q-6)}`. -/
private lemma cutLevels_core (w k τ r C G : ℝ) (hw : 64 ≤ w)
    (hG : G ≤ C * w ^ (r + 2 * k)) (hE : 32 * w ^ (2 * τ + 34) ≤ w ^ (2 * k))
    (hP : 2 * w ^ (2 * τ + 26 - 2 * k) * (1 + C * w ^ r) ≤ 1) (hR : C * w ^ r ≤ w ^ (26 : ℝ)) :
    32 * (w ^ τ) ^ 2 * w ^ 34 ≤ (w ^ k) ^ 2 ∧
    2 * (w ^ τ) ^ 2 * w ^ 26 * ((w ^ k) ^ 2 + G) ≤ (w ^ k) ^ 4 ∧
    G / (w ^ k) ^ 2 ≤ w ^ 26 := by
  have hw0 : 0 < w := by linarith
  have hA2 : (w ^ τ) ^ 2 = w ^ (2 * τ) := cutLevels_rpow_sq hw0.le τ
  have hB2 : (w ^ k) ^ 2 = w ^ (2 * k) := cutLevels_rpow_sq hw0.le k
  have hB4 : (w ^ k) ^ 4 = (w ^ (2 * k)) ^ 2 := by rw [← hB2]; ring
  have hBpos : 0 < w ^ (2 * k) := Real.rpow_pos_of_pos hw0 _
  have h34 : w ^ 34 = w ^ (34 : ℝ) := cutLevels_pow_eq w 34
  have h26 : w ^ 26 = w ^ (26 : ℝ) := cutLevels_pow_eq w 26
  have hGB : G / w ^ (2 * k) ≤ C * w ^ r := by
    calc G / w ^ (2 * k) ≤ C * w ^ (r + 2 * k) / w ^ (2 * k) := by gcongr
      _ = C * w ^ r := by
          rw [Real.rpow_add hw0]
          field_simp
  rw [hA2, hB2, hB4]
  refine ⟨?_, ?_, ?_⟩
  · rw [h34, mul_assoc, ← Real.rpow_add hw0]
    exact hE
  · have hGB' : G ≤ w ^ (2 * k) * (C * w ^ r) := by
      rwa [div_le_iff₀ hBpos, mul_comm] at hGB
    have hs : w ^ (2 * τ) * w ^ 26 = w ^ (2 * τ + 26 - 2 * k) * w ^ (2 * k) := by
      rw [h26, ← Real.rpow_add hw0, ← Real.rpow_add hw0]
      congr 1
      ring
    have hspos : 0 < w ^ (2 * τ + 26 - 2 * k) := Real.rpow_pos_of_pos hw0 _
    calc 2 * w ^ (2 * τ) * w ^ 26 * (w ^ (2 * k) + G)
        = (2 * w ^ (2 * τ + 26 - 2 * k)) * w ^ (2 * k) * (w ^ (2 * k) + G) := by
          rw [mul_assoc 2, hs]; ring
      _ ≤ (2 * w ^ (2 * τ + 26 - 2 * k)) * w ^ (2 * k) *
            (w ^ (2 * k) + w ^ (2 * k) * (C * w ^ r)) := by gcongr
      _ = (w ^ (2 * k)) ^ 2 * (2 * w ^ (2 * τ + 26 - 2 * k) * (1 + C * w ^ r)) := by ring
      _ ≤ (w ^ (2 * k)) ^ 2 * 1 := by gcongr
      _ = (w ^ (2 * k)) ^ 2 := mul_one _
  · rw [h26]
    exact hGB.trans hR

/-- `K * w^x ≤ w^y` when `K ≤ w` and `x ≤ y - 1`. -/
private lemma cutLevels_mul_le {w x y K : ℝ} (hw : 1 ≤ w) (hK : K ≤ w) (hx : x ≤ y - 1) :
    K * w ^ x ≤ w ^ y := by
  have hw0 : 0 < w := by linarith
  have h1 : w ^ x ≤ w ^ (y - 1) := Real.rpow_le_rpow_of_exponent_le hw hx
  have h2 : 0 ≤ w ^ x := (Real.rpow_pos_of_pos hw0 x).le
  calc K * w ^ x ≤ w * w ^ x := by gcongr
    _ ≤ w * w ^ (y - 1) := by gcongr
    _ = w ^ y := by
        have : w * w ^ (y - 1) = w ^ (1 : ℝ) * w ^ (y - 1) := by rw [Real.rpow_one]
        rw [this, ← Real.rpow_add hw0]
        congr 1
        ring

/-- `w^x ≤ 1/64` when `64 ≤ w` and `x ≤ -1`. -/
private lemma cutLevels_rpow_le_sixtyfourth {w x : ℝ} (hw : 64 ≤ w) (hx : x ≤ -1) :
    w ^ x ≤ 1 / 64 := by
  have := cutLevels_rpow_le_inv (w := w) (x := x) (c := 1) (K := 64) (by linarith) (by norm_num)
    hx (by rwa [Real.rpow_one])
  simpa using this

/-- The rows of regime (i): `q ≥ 7`, `0 < p < 2/(q - 5)`; and for `W ≥ W₀`, `a ∈ [α, β]`,
`g = W^{-a}`: the overlap level is in `(0, 1/64]`; the matching error (9.70) [su:eq:error]
`32 t² W^{34} ≤ κ²`; the error times the output ratio (9.72)
[su:eq:output-derivative-ratio], `2 t² W^{26} (κ² + W⁶ g^{-2(q-6)}) ≤ κ⁴`; and the rank row
(9.55) [su:eq:rank] in the form `4 L_rk + 1 ≤ 3 W g² W^{ε/4}`; and the output ratio (9.72)
[su:eq:output-derivative-ratio] `W⁶ g^{-2(q-6)} κ⁻² ≤ W^{26}`. -/
theorem levels_weak (α β ε : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 2) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hεα : ε ≤ 100 * α) :
    7 ≤ qWeak β ε ∧ 0 < pWeak β ε ∧ pWeak β ε < 2 / ((qWeak β ε : ℝ) - 5) ∧
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ a ∈ Set.Icc α β, ∀ L : ℝ,
      0 < (levelsWeak W ((W : ℝ) ^ (-a)) α β ε L).Lov ∧
      64 * (levelsWeak W ((W : ℝ) ^ (-a)) α β ε L).Lov ≤ 1 ∧
      0 < (levelsWeak W ((W : ℝ) ^ (-a)) α β ε L).kOut ∧
      32 * (levelsWeak W ((W : ℝ) ^ (-a)) α β ε L).t ^ 2 * (W : ℝ) ^ 34 ≤
        (levelsWeak W ((W : ℝ) ^ (-a)) α β ε L).kOut ^ 2 ∧
      2 * (levelsWeak W ((W : ℝ) ^ (-a)) α β ε L).t ^ 2 * (W : ℝ) ^ 26 *
          ((levelsWeak W ((W : ℝ) ^ (-a)) α β ε L).kOut ^ 2 +
            (W : ℝ) ^ 6 / ((W : ℝ) ^ (-a)) ^ (2 * (qWeak β ε - 6))) ≤
        (levelsWeak W ((W : ℝ) ^ (-a)) α β ε L).kOut ^ 4 ∧
      4 * (levelsWeak W ((W : ℝ) ^ (-a)) α β ε L).Lrk + 1 ≤
        3 * W * (((W : ℝ) ^ (-a)) ^ 2 * (W : ℝ) ^ (ε / 4)) ∧
      (W : ℝ) ^ 6 / (((W : ℝ) ^ (-a)) ^ (2 * (qWeak β ε - 6)) *
        (levelsWeak W ((W : ℝ) ^ (-a)) α β ε L).kOut ^ 2) ≤ (W : ℝ) ^ 26 := by
  have hβ0 : 0 < β := by linarith
  have hε6 : ε < 6400 := by linarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈25600 / ε * (40 + β)⌉₊ := ⟨_, rfl⟩
  have hq : qWeak β ε = 5 + N := by rw [hN]; rfl
  have hp : pWeak β ε = 2 * (1 - ε / 6400) / (N : ℝ) := by rw [hN]; rfl
  have hNge : 25600 / ε * (40 + β) ≤ (N : ℝ) := by rw [hN]; exact Nat.le_ceil _
  have hNε : 25600 * (40 + β) ≤ (N : ℝ) * ε := by
    calc 25600 * (40 + β) = 25600 / ε * (40 + β) * ε := by field_simp
      _ ≤ (N : ℝ) * ε := by gcongr
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNbig : 1024000 ≤ (N : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hε1 hN0]
  have hN2 : 2 ≤ N := by exact_mod_cast (by linarith : (2 : ℝ) ≤ N)
  have hNpos : (0 : ℝ) < N := by linarith
  have hpos : 0 < pWeak β ε := by
    rw [hp]; exact div_pos (by linarith) hNpos
  have hpN : pWeak β ε * N = 2 * (1 - ε / 6400) := by
    rw [hp]; field_simp
  have hpε : pWeak β ε ≤ ε / 512000 := by
    rw [hp, div_le_iff₀ hNpos]; nlinarith
  have hq7 : 7 ≤ qWeak β ε := by rw [hq]; omega
  have hplt : pWeak β ε < 2 / ((qWeak β ε : ℝ) - 5) := by
    rw [hp, hq]
    have h5 : ((5 + N : ℕ) : ℝ) - 5 = N := by push_cast; ring
    rw [h5]
    exact div_lt_div_of_pos_right (by linarith) hNpos
  have hev : ∀ᶠ W : ℕ in Filter.atTop, 64 ≤ (W : ℝ) ∧ 64 ≤ (W : ℝ) ^ (α / 2) ∧
      3 ≤ (W : ℝ) ^ (3193 * ε / 12800) :=
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop 64).and
      ((cutLevels_eventually_ge _ _ (by linarith)).and
        (cutLevels_eventually_ge _ _ (by positivity)))
  obtain ⟨W₀, hW₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨hq7, hpos, hplt, W₀, fun W hW a ha L => ?_⟩
  obtain ⟨h64, hα2, h3⟩ := hW₀ W hW
  obtain ⟨haα, haβ⟩ := ha
  have hw0 : 0 < (W : ℝ) := by linarith
  have hw1 : 1 ≤ (W : ℝ) := by linarith
  have ht : (levelsWeak W ((W : ℝ) ^ (-a)) α β ε L).t = (W : ℝ) ^ (-40 + a * (5 + N)) := by
    simp only [levelsWeak, hq]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw0.le, ← Real.rpow_neg hw0.le,
      ← Real.rpow_add hw0]
    congr 1
    push_cast
    ring
  have hk : (levelsWeak W ((W : ℝ) ^ (-a)) α β ε L).kOut =
      (W : ℝ) ^ (a * N - 3 * ε / 800) := by
    have h5 : 5 + N - 5 = N := by omega
    simp only [levelsWeak, hq, h5]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw0.le, ← Real.rpow_neg hw0.le,
      ← Real.rpow_add hw0]
    congr 1
    ring
  have hlov : (levelsWeak W ((W : ℝ) ^ (-a)) α β ε L).Lov =
      (W : ℝ) ^ (-2 * a + 3 * ε / 200) := by
    simp only [levelsWeak]
    rw [cutLevels_rpow_sq hw0.le, ← Real.rpow_add hw0]
    congr 1
    ring
  have hrk : (levelsWeak W ((W : ℝ) ^ (-a)) α β ε L).Lrk =
      2 * (W : ℝ) ^ ((-40 + a * (5 + N)) * (-pWeak β ε) + (1 + ε / 3200)) := by
    have : (levelsWeak W ((W : ℝ) ^ (-a)) α β ε L).Lrk =
        2 * ((levelsWeak W ((W : ℝ) ^ (-a)) α β ε L).t) ^ (-pWeak β ε) *
          (W : ℝ) ^ (1 + ε / 3200) := rfl
    rw [this, ht, ← Real.rpow_mul hw0.le, mul_assoc, ← Real.rpow_add hw0]
  have hGeq : (W : ℝ) ^ 6 / ((W : ℝ) ^ (-a)) ^ (2 * (qWeak β ε - 6)) =
      (W : ℝ) ^ (6 + 2 * a * ((N : ℝ) - 1)) := by
    have h6 : 5 + N - 6 = N - 1 := by omega
    have hm : ((2 * (qWeak β ε - 6) : ℕ) : ℝ) = 2 * ((N : ℝ) - 1) := by
      rw [hq, h6]
      have : 1 ≤ N := by omega
      push_cast [Nat.cast_sub this]
      ring
    rw [cutLevels_pow_eq (W : ℝ) 6,
      ← Real.rpow_natCast ((W : ℝ) ^ (-a)) (2 * (qWeak β ε - 6)),
      ← Real.rpow_mul hw0.le, ← Real.rpow_sub hw0, hm]
    congr 1
    push_cast
    ring
  have hcore := cutLevels_core (W : ℝ) (a * N - 3 * ε / 800) (-40 + a * (5 + N))
    (6 - 2 * a + 3 * ε / 400) 1 ((W : ℝ) ^ (6 + 2 * a * ((N : ℝ) - 1))) h64
    (by
      rw [one_mul]
      apply le_of_eq
      congr 1
      ring)
    (by
      apply cutLevels_mul_le hw1 (by linarith)
      nlinarith)
    (by
      have hs : (W : ℝ) ^ (2 * (-40 + a * (5 + N)) + 26 - 2 * (a * N - 3 * ε / 800)) ≤ 1 / 64 :=
        cutLevels_rpow_le_sixtyfourth h64 (by nlinarith)
      have hsr : (W : ℝ) ^ (2 * (-40 + a * (5 + N)) + 26 - 2 * (a * N - 3 * ε / 800)) *
          (W : ℝ) ^ (6 - 2 * a + 3 * ε / 400) ≤ 1 / 64 := by
        rw [← Real.rpow_add hw0]
        exact cutLevels_rpow_le_sixtyfourth h64 (by nlinarith)
      calc 2 * (W : ℝ) ^ (2 * (-40 + a * (5 + N)) + 26 - 2 * (a * N - 3 * ε / 800)) *
            (1 + 1 * (W : ℝ) ^ (6 - 2 * a + 3 * ε / 400))
          = 2 * (W : ℝ) ^ (2 * (-40 + a * (5 + N)) + 26 - 2 * (a * N - 3 * ε / 800)) +
            2 * ((W : ℝ) ^ (2 * (-40 + a * (5 + N)) + 26 - 2 * (a * N - 3 * ε / 800)) *
              (W : ℝ) ^ (6 - 2 * a + 3 * ε / 400)) := by ring
        _ ≤ 1 := by linarith)
    (by
      rw [one_mul]
      exact Real.rpow_le_rpow_of_exponent_le hw1 (by linarith))
  obtain ⟨c1, c2, c3⟩ := hcore
  rw [ht, hk, hlov, hrk]
  refine ⟨Real.rpow_pos_of_pos hw0 _, ?_, Real.rpow_pos_of_pos hw0 _, c1, by rw [hGeq]; exact c2,
    ?_, by rw [← div_div, hGeq]; exact c3⟩
  · have h1 : (W : ℝ) ^ (-2 * a + 3 * ε / 200) ≤ (64 : ℝ)⁻¹ :=
      cutLevels_rpow_le_inv hw1 (by norm_num) (by linarith) hα2
    calc 64 * (W : ℝ) ^ (-2 * a + 3 * ε / 200) ≤ 64 * (64 : ℝ)⁻¹ := by gcongr
      _ = 1 := by norm_num
  · have hapN : a * pWeak β ε * N = a * (2 * (1 - ε / 6400)) := by rw [mul_assoc, hpN]
    have hap0 : 0 ≤ a * pWeak β ε := mul_nonneg (by linarith) hpos.le
    have hap1 : a * pWeak β ε ≤ 1 / 2 * pWeak β ε :=
      mul_le_mul_of_nonneg_right (by linarith) hpos.le
    have hae0 : 0 ≤ a * ε := mul_nonneg (by linarith) hε.le
    have hae1 : a * ε ≤ 1 / 2 * ε := mul_le_mul_of_nonneg_right (by linarith) hε.le
    have hρeq : (-40 + a * (5 + N)) * (-pWeak β ε) + (1 + ε / 3200) =
        40 * pWeak β ε - 5 * (a * pWeak β ε) - a * pWeak β ε * N + 1 + ε / 3200 := by ring
    have hρup : (-40 + a * (5 + N)) * (-pWeak β ε) + (1 + ε / 3200) ≤
        1 - 2 * a + ε / 4 - 3193 * ε / 12800 := by
      rw [hρeq]; linarith
    have hρlo : 0 ≤ (-40 + a * (5 + N)) * (-pWeak β ε) + (1 + ε / 3200) := by
      rw [hρeq]; linarith
    have hone : 1 ≤ (W : ℝ) ^ ((-40 + a * (5 + N)) * (-pWeak β ε) + (1 + ε / 3200)) :=
      Real.one_le_rpow hw1 hρlo
    have hR6 : 3 * (W : ℝ) * (((W : ℝ) ^ (-a)) ^ 2 * (W : ℝ) ^ (ε / 4)) =
        3 * (W : ℝ) ^ (1 - 2 * a + ε / 4) := by
      have h1 : (W : ℝ) * (W : ℝ) ^ (2 * (-a) + ε / 4) = (W : ℝ) ^ (1 - 2 * a + ε / 4) := by
        have : (W : ℝ) * (W : ℝ) ^ (2 * (-a) + ε / 4) =
            (W : ℝ) ^ (1 : ℝ) * (W : ℝ) ^ (2 * (-a) + ε / 4) := by rw [Real.rpow_one]
        rw [this, ← Real.rpow_add hw0]
        congr 1
        ring
      rw [cutLevels_rpow_sq hw0.le, ← Real.rpow_add hw0, mul_assoc, h1]
    rw [hR6]
    have h2 : 3 * (W : ℝ) ^ ((-40 + a * (5 + N)) * (-pWeak β ε) + (1 + ε / 3200)) ≤
        (W : ℝ) ^ (1 - 2 * a + ε / 4) := by
      calc 3 * (W : ℝ) ^ ((-40 + a * (5 + N)) * (-pWeak β ε) + (1 + ε / 3200))
          ≤ (W : ℝ) ^ (3193 * ε / 12800) *
            (W : ℝ) ^ ((-40 + a * (5 + N)) * (-pWeak β ε) + (1 + ε / 3200)) := by gcongr
        _ = (W : ℝ) ^ ((-40 + a * (5 + N)) * (-pWeak β ε) + (1 + ε / 3200) + 3193 * ε / 12800) := by
          rw [mul_comm, ← Real.rpow_add hw0, add_comm]
        _ ≤ (W : ℝ) ^ (1 - 2 * a + ε / 4) :=
          Real.rpow_le_rpow_of_exponent_le hw1 (by linarith)
    linarith

/-- The rows of regime (ii): `q ≥ 7`, `0 < p < 2/(q - 5)`; and for `W ≥ W₀` and
`c_* W^{-1/2} ≤ g ≤ W^{-1/2+θ/2}`: the overlap level is in `(0, 1/64]`; `32 t² W^{34} ≤ κ²`;
`2 t² W^{26} (κ² + W⁶ g^{-2(q-6)}) ≤ κ⁴` with (9.72) [su:eq:output-derivative-ratio]; and the
rank row (9.63) [nc:eq:dimension] in the form `4 L_rk + 1 ≤ 3 W W^{-1+14θ}`; and the output
ratio (9.72) [su:eq:output-derivative-ratio] `W⁶ g^{-2(q-6)} κ⁻² ≤ W^{26}`. -/
theorem levels_crit (θ cs : ℝ) (hθ : 0 < θ) (hθ' : θ ≤ 1 / 100) (hcs : 0 < cs) :
    7 ≤ qCrit θ ∧ 0 < pCrit θ ∧ pCrit θ < 2 / ((qCrit θ : ℝ) - 5) ∧
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, cs * (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ g →
      g ≤ (W : ℝ) ^ (-(1 / 2 : ℝ) + θ / 2) → ∀ L : ℝ,
      0 < (levelsCrit W θ L).Lov ∧ 64 * (levelsCrit W θ L).Lov ≤ 1 ∧
      0 < (levelsCrit W θ L).kOut ∧
      32 * (levelsCrit W θ L).t ^ 2 * (W : ℝ) ^ 34 ≤ (levelsCrit W θ L).kOut ^ 2 ∧
      2 * (levelsCrit W θ L).t ^ 2 * (W : ℝ) ^ 26 *
          ((levelsCrit W θ L).kOut ^ 2 + (W : ℝ) ^ 6 / g ^ (2 * (qCrit θ - 6))) ≤
        (levelsCrit W θ L).kOut ^ 4 ∧
      4 * (levelsCrit W θ L).Lrk + 1 ≤ 3 * W * (W : ℝ) ^ (-1 + 14 * θ) ∧
      (W : ℝ) ^ 6 / (g ^ (2 * (qCrit θ - 6)) * (levelsCrit W θ L).kOut ^ 2) ≤ (W : ℝ) ^ 26 := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈10 / θ⌉₊ := ⟨_, rfl⟩
  have hq : qCrit θ = 5 + N := by rw [hN]; rfl
  have hp : pCrit θ = 2 * (1 - θ / 4) / (N : ℝ) := by rw [hN]; rfl
  have hqR : (qCrit θ : ℝ) = 5 + N := by rw [hq]; push_cast; ring
  have hNge : 10 / θ ≤ (N : ℝ) := by rw [hN]; exact Nat.le_ceil _
  have hNlt : (N : ℝ) < 10 / θ + 1 := by
    rw [hN]; exact Nat.ceil_lt_add_one (by positivity)
  have hNθ : 10 ≤ (N : ℝ) * θ := by
    have := mul_le_mul_of_nonneg_right hNge hθ.le
    rwa [div_mul_cancel₀ _ hθ.ne'] at this
  have hNθ' : (N : ℝ) * θ < 10 + θ := by
    have := mul_lt_mul_of_pos_right hNlt hθ
    rwa [add_mul, div_mul_cancel₀ _ hθ.ne', one_mul] at this
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNbig : 1000 ≤ (N : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hθ' hN0]
  have hN2 : 2 ≤ N := by exact_mod_cast (by linarith : (2 : ℝ) ≤ N)
  have hNpos : (0 : ℝ) < N := by linarith
  have hpos : 0 < pCrit θ := by
    rw [hp]; exact div_pos (by linarith) hNpos
  have hpN : pCrit θ * N = 2 * (1 - θ / 4) := by
    rw [hp]; field_simp
  have hpθ : pCrit θ ≤ θ / 5 := by
    rw [hp, div_le_iff₀ hNpos]; nlinarith
  have hq7 : 7 ≤ qCrit θ := by rw [hq]; omega
  have hplt : pCrit θ < 2 / ((qCrit θ : ℝ) - 5) := by
    rw [hp, hqR]
    have h5 : (5 : ℝ) + N - 5 = N := by ring
    rw [h5]
    exact div_lt_div_of_pos_right (by linarith) hNpos
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 2 * (qCrit θ - 6) := ⟨_, rfl⟩
  have hMR : (M : ℝ) = 2 * ((N : ℝ) - 1) := by
    have h6 : qCrit θ - 6 = N - 1 := by rw [hq]; omega
    have : 1 ≤ N := by omega
    rw [hM, h6]
    push_cast [Nat.cast_sub this]
    ring
  have hev : ∀ᶠ W : ℕ in Filter.atTop, 64 ≤ (W : ℝ) ∧ 64 ≤ (W : ℝ) ^ (1 / 2 : ℝ) ∧
      3 ≤ (W : ℝ) ^ (27 * θ / 5) ∧ 4 * (cs ^ M)⁻¹ ≤ (W : ℝ) ^ (9 / 10 : ℝ) :=
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop 64).and
      ((cutLevels_eventually_ge _ _ (by norm_num)).and
        ((cutLevels_eventually_ge _ _ (by positivity)).and
          (cutLevels_eventually_ge _ _ (by norm_num))))
  obtain ⟨W₀, hW₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨hq7, hpos, hplt, W₀, fun W hW g hg1 _ L => ?_⟩
  obtain ⟨h64, h64', h3, hC⟩ := hW₀ W hW
  have hw0 : 0 < (W : ℝ) := by linarith
  have hw1 : 1 ≤ (W : ℝ) := by linarith
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = -30 + (1 - 2 * θ) * ((5 + N : ℝ) - 6) / 2 := ⟨_, rfl⟩
  obtain ⟨k, hk'⟩ : ∃ k : ℝ, k = (-1 + 2 * θ) * (-((5 + N : ℝ) - 5) / 2) + -(4 * θ) :=
    ⟨_, rfl⟩
  have ht : (levelsCrit W θ L).t = (W : ℝ) ^ τ := by
    rw [hτ]
    simp only [levelsCrit, hqR]
  have hk : (levelsCrit W θ L).kOut = (W : ℝ) ^ k := by
    rw [hk']
    simp only [levelsCrit, hqR]
    rw [← Real.rpow_mul hw0.le, ← Real.rpow_add hw0]
  have hrk : (levelsCrit W θ L).Lrk = 2 * (W : ℝ) ^ (τ * (-pCrit θ) + (1 + θ / 4)) := by
    have : (levelsCrit W θ L).Lrk =
        2 * ((levelsCrit W θ L).t) ^ (-pCrit θ) * (W : ℝ) ^ (1 + θ / 4) := rfl
    rw [this, ht, ← Real.rpow_mul hw0.le, mul_assoc, ← Real.rpow_add hw0]
  have hgpos : 0 < g := lt_of_lt_of_le (by positivity) hg1
  have hGle : (W : ℝ) ^ 6 / g ^ (2 * (qCrit θ - 6)) ≤ (cs ^ M)⁻¹ * (W : ℝ) ^ ((N : ℝ) + 5) := by
    rw [← hM]
    have hgM : cs ^ M * (W : ℝ) ^ (-((N : ℝ) - 1)) ≤ g ^ M := by
      calc cs ^ M * (W : ℝ) ^ (-((N : ℝ) - 1)) = (cs * (W : ℝ) ^ (-(1 / 2 : ℝ))) ^ M := by
            rw [mul_pow, ← Real.rpow_natCast ((W : ℝ) ^ (-(1 / 2 : ℝ))) M,
              ← Real.rpow_mul hw0.le, hMR]
            congr 2
            ring
        _ ≤ g ^ M := by gcongr
    have hpos' : 0 < cs ^ M * (W : ℝ) ^ (-((N : ℝ) - 1)) := by positivity
    calc (W : ℝ) ^ 6 / g ^ M ≤ (W : ℝ) ^ 6 / (cs ^ M * (W : ℝ) ^ (-((N : ℝ) - 1))) :=
          div_le_div_of_nonneg_left (by positivity) hpos' hgM
      _ = (cs ^ M)⁻¹ * (W : ℝ) ^ ((N : ℝ) + 5) := by
          rw [cutLevels_pow_eq (W : ℝ) 6, Real.rpow_neg hw0.le, 
            show (N : ℝ) + 5 = ((6 : ℕ) : ℝ) + ((N : ℝ) - 1) by push_cast; ring,
            Real.rpow_add hw0]
          field_simp
  have hCnn : 0 ≤ (cs ^ M)⁻¹ := by positivity
  have hC' : (cs ^ M)⁻¹ ≤ (W : ℝ) ^ (9 / 10 : ℝ) := by linarith
  have hexp1 : (N : ℝ) + 5 ≤ 251 / 10 + 2 * k := by rw [hk']; linarith
  have hexp2 : 2 * τ + 34 ≤ 2 * k - 1 := by rw [hτ, hk']; linarith
  have hexp3 : 2 * τ + 26 - 2 * k ≤ -1 := by rw [hτ, hk']; linarith
  have hexp4 : 9 / 10 + (2 * τ + 26 - 2 * k + 251 / 10) ≤ 0 := by rw [hτ, hk']; linarith
  have hcore := cutLevels_core (W : ℝ) k τ (251 / 10) (cs ^ M)⁻¹
    ((W : ℝ) ^ 6 / g ^ (2 * (qCrit θ - 6))) h64
    (hGle.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hw1 hexp1) hCnn))
    (cutLevels_mul_le hw1 (by linarith) hexp2)
    (by
      have hs : (W : ℝ) ^ (2 * τ + 26 - 2 * k) ≤ 1 / 64 :=
        cutLevels_rpow_le_sixtyfourth h64 hexp3
      have h1 : (W : ℝ) ^ (9 / 10 : ℝ) * ((W : ℝ) ^ (2 * τ + 26 - 2 * k) *
          (W : ℝ) ^ (251 / 10 : ℝ)) ≤ 1 := by
        rw [← Real.rpow_add hw0, ← Real.rpow_add hw0]
        exact Real.rpow_le_one_of_one_le_of_nonpos hw1 hexp4
      have h2 : 0 ≤ (W : ℝ) ^ (2 * τ + 26 - 2 * k) * (W : ℝ) ^ (251 / 10 : ℝ) :=
        mul_nonneg (Real.rpow_pos_of_pos hw0 _).le (Real.rpow_pos_of_pos hw0 _).le
      have hsr : (cs ^ M)⁻¹ * ((W : ℝ) ^ (2 * τ + 26 - 2 * k) * (W : ℝ) ^ (251 / 10 : ℝ)) ≤
          1 / 4 := by
        calc (cs ^ M)⁻¹ * ((W : ℝ) ^ (2 * τ + 26 - 2 * k) * (W : ℝ) ^ (251 / 10 : ℝ))
            ≤ ((W : ℝ) ^ (9 / 10 : ℝ) / 4) *
              ((W : ℝ) ^ (2 * τ + 26 - 2 * k) * (W : ℝ) ^ (251 / 10 : ℝ)) := by
              gcongr; linarith
          _ ≤ 1 / 4 := by linarith
      calc 2 * (W : ℝ) ^ (2 * τ + 26 - 2 * k) * (1 + (cs ^ M)⁻¹ * (W : ℝ) ^ (251 / 10 : ℝ))
          = 2 * (W : ℝ) ^ (2 * τ + 26 - 2 * k) +
            2 * ((cs ^ M)⁻¹ * ((W : ℝ) ^ (2 * τ + 26 - 2 * k) *
              (W : ℝ) ^ (251 / 10 : ℝ))) := by ring
        _ ≤ 1 := by linarith)
    (calc (cs ^ M)⁻¹ * (W : ℝ) ^ (251 / 10 : ℝ)
        ≤ (W : ℝ) ^ (9 / 10 : ℝ) * (W : ℝ) ^ (251 / 10 : ℝ) := by gcongr
      _ = (W : ℝ) ^ (26 : ℝ) := by
        rw [← Real.rpow_add hw0]
        norm_num)
  obtain ⟨c1, c2, c3⟩ := hcore
  have hlov : (levelsCrit W θ L).Lov = (W : ℝ) ^ (-1 + 14 * θ) := rfl
  rw [ht, hk, hlov, hrk]
  refine ⟨Real.rpow_pos_of_pos hw0 _, ?_, Real.rpow_pos_of_pos hw0 _, c1, c2, ?_,
    by rw [← div_div]; exact c3⟩
  · have h1 : (W : ℝ) ^ (-1 + 14 * θ) ≤ (64 : ℝ)⁻¹ :=
      cutLevels_rpow_le_inv hw1 (by norm_num) (by linarith) h64'
    calc 64 * (W : ℝ) ^ (-1 + 14 * θ) ≤ 64 * (64 : ℝ)⁻¹ := by gcongr
      _ = 1 := by norm_num
  · have hθpN : θ * pCrit θ * N = θ * (2 * (1 - θ / 4)) := by rw [mul_assoc, hpN]
    have hθp0 : 0 ≤ θ * pCrit θ := mul_nonneg hθ.le hpos.le
    have hθp1 : θ * pCrit θ ≤ 1 / 100 * pCrit θ :=
      mul_le_mul_of_nonneg_right hθ' hpos.le
    have hθθ0 : 0 ≤ θ * θ := mul_nonneg hθ.le hθ.le
    have hθθ1 : θ * θ ≤ 1 / 100 * θ := mul_le_mul_of_nonneg_right hθ' hθ.le
    have hρup : τ * (-pCrit θ) + (1 + θ / 4) ≤ 43 * θ / 5 := by
      rw [hτ]; linarith
    have hρlo : 0 ≤ τ * (-pCrit θ) + (1 + θ / 4) := by
      rw [hτ]; linarith
    have hone : 1 ≤ (W : ℝ) ^ (τ * (-pCrit θ) + (1 + θ / 4)) := Real.one_le_rpow hw1 hρlo
    have hR6 : 3 * (W : ℝ) * (W : ℝ) ^ (-1 + 14 * θ) = 3 * (W : ℝ) ^ (14 * θ) := by
      have : (W : ℝ) * (W : ℝ) ^ (-1 + 14 * θ) = (W : ℝ) ^ (14 * θ) := by
        have h1 : (W : ℝ) * (W : ℝ) ^ (-1 + 14 * θ) =
            (W : ℝ) ^ (1 : ℝ) * (W : ℝ) ^ (-1 + 14 * θ) := by rw [Real.rpow_one]
        rw [h1, ← Real.rpow_add hw0]
        congr 1
        ring
      rw [mul_assoc, this]
    rw [hR6]
    have h2 : 3 * (W : ℝ) ^ (τ * (-pCrit θ) + (1 + θ / 4)) ≤ (W : ℝ) ^ (14 * θ) := by
      calc 3 * (W : ℝ) ^ (τ * (-pCrit θ) + (1 + θ / 4))
          ≤ (W : ℝ) ^ (27 * θ / 5) * (W : ℝ) ^ (τ * (-pCrit θ) + (1 + θ / 4)) := by gcongr
        _ = (W : ℝ) ^ (τ * (-pCrit θ) + (1 + θ / 4) + 27 * θ / 5) := by
          rw [mul_comm, ← Real.rpow_add hw0, add_comm]
        _ ≤ (W : ℝ) ^ (14 * θ) := Real.rpow_le_rpow_of_exponent_le hw1 (by linarith)
    linarith

end LSBA
