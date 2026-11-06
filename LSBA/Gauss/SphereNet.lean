import Mathlib

/-!
# Nets of the unit sphere of `ℂ^m`

For every `δ > 0` the unit sphere of `ℂ^m` has a `δ`-net of at most `(1 + 2/δ)^{2m}` unit
vectors, and the values of `‖A v‖` on a net bound `‖A y‖` on the whole sphere from above and
from below. These are the net inputs of the lower spectral bound in Appendix G.4
[app:compact-gaussian].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- A finite set of unit vectors of `ℂ^m` that are pairwise more than `δ` apart (in the Euclidean
norm) has at most `(1 + 2/δ)^{2m}` elements: the open balls of radius `δ/2` around the points are
disjoint and lie in the ball of radius `1 + δ/2`, and the Haar measure of a ball of radius `r` in
`ℝ^{2m}` is `r^{2m}` times that of the unit ball. -/
private lemma sphereNet_packing {m : Type*} [Fintype m] {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (EuclideanSpace ℂ m)) (hS : ∀ s ∈ S, ‖s‖ = 1)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → δ < dist s t) :
    (S.card : ℝ) ≤ (1 + 2 / δ) ^ (2 * Fintype.card m) := by
  have hd : Module.finrank ℝ (EuclideanSpace ℂ m) = 2 * Fintype.card m := by
    rw [finrank_real_of_complex]; simp
  have hdisj :
      (S : Set (EuclideanSpace ℂ m)).PairwiseDisjoint (fun s => Metric.ball s (δ / 2)) := by
    intro s hs t ht hst
    have := hsep s hs t ht hst
    exact Metric.ball_disjoint_ball (by linarith)
  have hsub : (⋃ s ∈ S, Metric.ball s (δ / 2)) ⊆
      Metric.ball (0 : EuclideanSpace ℂ m) (1 + δ / 2) := by
    intro y hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨s, hs, hy⟩ := hy
    rw [mem_ball_zero_iff]
    have h1 := hS s hs
    have h2 : ‖y - s‖ < δ / 2 := by simpa [dist_eq_norm] using hy
    calc ‖y‖ = ‖(y - s) + s‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - s‖ + ‖s‖ := norm_add_le _ _
      _ < 1 + δ / 2 := by linarith
  have hle := measure_mono (μ := (volume : Measure (EuclideanSpace ℂ m))) hsub
  rw [measure_biUnion_finset hdisj (fun s _ => measurableSet_ball)] at hle
  have hq : (0 : ℝ) < δ / 2 := by positivity
  have hp : (0 : ℝ) < 1 + δ / 2 := by positivity
  rw [Finset.sum_congr rfl
    (fun s _ => Measure.addHaar_ball_of_pos (volume : Measure (EuclideanSpace ℂ m)) s hq),
    Measure.addHaar_ball_of_pos (volume : Measure (EuclideanSpace ℂ m)) 0 hp,
    Finset.sum_const, nsmul_eq_mul, hd, ← mul_assoc] at hle
  have hc0 : (volume : Measure (EuclideanSpace ℂ m)) (Metric.ball 0 1) ≠ 0 :=
    (Metric.measure_ball_pos _ 0 one_pos).ne'
  have hctop : (volume : Measure (EuclideanSpace ℂ m)) (Metric.ball 0 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  rw [ENNReal.mul_le_mul_iff_left hc0 hctop] at hle
  have h3 : (S.card : ℝ) * (δ / 2) ^ (2 * Fintype.card m) ≤ (1 + δ / 2) ^ (2 * Fintype.card m) := by
    rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast]
    exact hle
  have h4 : (1 + δ / 2) ^ (2 * Fintype.card m) =
      (1 + 2 / δ) ^ (2 * Fintype.card m) * (δ / 2) ^ (2 * Fintype.card m) := by
    rw [← mul_pow]
    congr 1
    field_simp
    ring
  rw [h4] at h3
  exact le_of_mul_le_mul_right h3 (by positivity)

/-- A set of unit vectors of `ℂ^m` that are pairwise more than `δ` apart, of maximal cardinality,
is a `δ`-net of the unit sphere with at most `(1 + 2/δ)^{2m}` points. -/
private lemma sphereNet_exists_cover (m : Type*) [Fintype m] {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : Finset (EuclideanSpace ℂ m), (S.card : ℝ) ≤ (1 + 2 / δ) ^ (2 * Fintype.card m) ∧
      (∀ s ∈ S, ‖s‖ = 1) ∧ ∀ x : EuclideanSpace ℂ m, ‖x‖ = 1 → ∃ s ∈ S, ‖x - s‖ ≤ δ := by
  let P : Finset (EuclideanSpace ℂ m) → Prop := fun S =>
    (∀ s ∈ S, ‖s‖ = 1) ∧ ∀ s ∈ S, ∀ t ∈ S, s ≠ t → δ < dist s t
  let K : Set ℕ := {n | ∃ S, P S ∧ S.card = n}
  have hK0 : 0 ∈ K := ⟨∅, ⟨by simp, by simp⟩, by simp⟩
  have hKbdd : BddAbove K := by
    refine ⟨⌈(1 + 2 / δ) ^ (2 * Fintype.card m)⌉₊, ?_⟩
    rintro n ⟨S, ⟨h1, h2⟩, rfl⟩
    exact_mod_cast (sphereNet_packing hδ S h1 h2).trans (Nat.le_ceil _)
  obtain ⟨S, hPS, hcard⟩ := Nat.sSup_mem ⟨0, hK0⟩ hKbdd
  have hmax : ∀ T, P T → T.card ≤ S.card := fun T hT => by
    rw [hcard]; exact le_csSup hKbdd ⟨T, hT, rfl⟩
  refine ⟨S, sphereNet_packing hδ S hPS.1 hPS.2, hPS.1, fun x hx => ?_⟩
  by_contra hcon
  push Not at hcon
  have hxS : x ∉ S := fun h => by have := hcon x h; simp at this; linarith
  have hP : P (insert x S) := by
    refine ⟨?_, ?_⟩
    · intro s hs
      rcases Finset.mem_insert.1 hs with rfl | hs
      · exact hx
      · exact hPS.1 s hs
    · intro s hs t ht hst
      rcases Finset.mem_insert.1 hs with hsx | hsS <;> rcases Finset.mem_insert.1 ht with htx | htS
      · exact absurd (hsx.trans htx.symm) hst
      · rw [hsx, dist_eq_norm]; exact hcon t htS
      · rw [htx, dist_comm, dist_eq_norm]; exact hcon s hsS
      · exact hPS.2 s hsS t htS hst
  have := hmax _ hP
  rw [Finset.card_insert_of_notMem hxS] at this
  omega

/-- A `δ`-net of the unit sphere of `ℂ^m` with at most `(1 + 2/δ)^{2m}` unit vectors. -/
theorem exists_sphere_net (m : Type*) [Fintype m] {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : Finset (m → ℂ), (N.card : ℝ) ≤ (1 + 2 / δ) ^ (2 * Fintype.card m) ∧
      (∀ v ∈ N, ∑ i, ‖v i‖ ^ 2 = 1) ∧
      ∀ y : m → ℂ, ∑ i, ‖y i‖ ^ 2 = 1 → ∃ v ∈ N, ∑ i, ‖y i - v i‖ ^ 2 ≤ δ ^ 2 := by
  obtain ⟨S, hcard, hunit, hcover⟩ := sphereNet_exists_cover m hδ
  refine ⟨S.image (fun s => s.ofLp), ?_, ?_, ?_⟩
  · exact_mod_cast (Nat.cast_le.2 Finset.card_image_le).trans hcard
  · intro v hv
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hv
    have h := hunit s hs
    rw [EuclideanSpace.norm_eq] at h
    have h2 := congrArg (fun r => r ^ 2) h
    simp only [one_pow] at h2
    rwa [Real.sq_sqrt (by positivity)] at h2
  · intro y hy
    have hx : ‖(WithLp.toLp 2 y : EuclideanSpace ℂ m)‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      simpa using hy
    obtain ⟨s, hs, hxs⟩ := hcover _ hx
    refine ⟨s.ofLp, Finset.mem_image_of_mem _ hs, ?_⟩
    rw [EuclideanSpace.norm_eq] at hxs
    have hxs' : Real.sqrt (∑ i, ‖y i - s i‖ ^ 2) ≤ δ := by simpa using hxs
    calc (∑ i, ‖y i - s.ofLp i‖ ^ 2) = (Real.sqrt (∑ i, ‖y i - s i‖ ^ 2)) ^ 2 := by
          rw [Real.sq_sqrt (by positivity)]
      _ ≤ δ ^ 2 := by gcongr

/-- A matrix `A : k × m` acts as a continuous linear map `ℂ^m → ℂ^k` of Euclidean spaces whose
value at `v` has norm `‖A v‖ = (∑ a, |(A v) a|²)^{1/2}`. -/
private lemma sphereNet_clm {k m : Type*} [Fintype k] [Fintype m] (A : Matrix k m ℂ) :
    ∃ f : EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ k, ∀ v : m → ℂ,
      ‖f (WithLp.toLp 2 v)‖ = Real.sqrt (∑ a, ‖(A *ᵥ v) a‖ ^ 2) := by
  refine ⟨LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A), fun v => ?_⟩
  rw [EuclideanSpace.norm_eq]
  rfl

/-- If the squared distance of `x` and `v` is at most `δ ^ 2` with `0 ≤ δ`, then the Euclidean
distance is at most `δ`. -/
private lemma sphereNet_norm_sub_le {m : Type*} [Fintype m] {δ : ℝ} (hδ0 : 0 ≤ δ)
    (x v : m → ℂ) (h : ∑ i, ‖x i - v i‖ ^ 2 ≤ δ ^ 2) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℂ m) - WithLp.toLp 2 v‖ ≤ δ := by
  rw [EuclideanSpace.norm_eq]
  calc Real.sqrt (∑ i, ‖((WithLp.toLp 2 x : EuclideanSpace ℂ m) - WithLp.toLp 2 v) i‖ ^ 2)
      ≤ Real.sqrt (δ ^ 2) := Real.sqrt_le_sqrt (by simpa using h)
    _ = δ := Real.sqrt_sq hδ0

/-- The unit sphere of `ℂ^m` in coordinates is the unit sphere of the Euclidean norm. -/
private lemma sphereNet_norm_eq_one {m : Type*} [Fintype m] (x : m → ℂ)
    (hx : ∑ i, ‖x i‖ ^ 2 = 1) : ‖(WithLp.toLp 2 x : EuclideanSpace ℂ m)‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simpa using hx

/-- Operator-norm bound from a net: if every unit vector is within `δ < 1` of a point of the net
and `‖f v‖ ≤ β` on the net, then `‖f‖ ≤ β / (1 - δ)`. -/
private lemma sphereNet_opNorm_le {k m : Type*} [Fintype k] [Fintype m]
    (f : EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ k) {N : Finset (m → ℂ)} {δ β : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hN : ∀ y : m → ℂ, ∑ i, ‖y i‖ ^ 2 = 1 → ∃ v ∈ N, ∑ i, ‖y i - v i‖ ^ 2 ≤ δ ^ 2)
    (hβ : ∀ v ∈ N, ‖f (WithLp.toLp 2 v)‖ ≤ β) (hβ0 : 0 ≤ β) : ‖f‖ ≤ β / (1 - δ) := by
  have key : ‖f‖ ≤ β + δ * ‖f‖ := by
    refine ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) (fun x hx => ?_)
    have hx' : ∑ i, ‖x.ofLp i‖ ^ 2 = 1 := by
      have h := congrArg (fun r => r ^ 2) hx
      simp only [one_pow] at h
      rwa [EuclideanSpace.norm_sq_eq] at h
    obtain ⟨v, hv, hxv⟩ := hN x.ofLp hx'
    have h1 := sphereNet_norm_sub_le hδ0 x.ofLp v hxv
    have h2 : ‖f (x - WithLp.toLp 2 v)‖ ≤ ‖f‖ * ‖x - WithLp.toLp 2 v‖ := f.le_opNorm _
    have h3 : ‖f x‖ ≤ ‖f (WithLp.toLp 2 v)‖ + ‖f (x - WithLp.toLp 2 v)‖ := by
      calc ‖f x‖ = ‖f (WithLp.toLp 2 v) + f (x - WithLp.toLp 2 v)‖ := by
            rw [← map_add, add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have h4 : ‖f‖ * ‖x - WithLp.toLp 2 v‖ ≤ ‖f‖ * δ :=
      mul_le_mul_of_nonneg_left (by simpa using h1) (norm_nonneg _)
    have h5 := hβ v hv
    nlinarith
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- Upper bound from a net: if every unit `y` is within `δ < 1` of `N` and `‖A v‖ ≤ β` on `N`,
then `‖A y‖ ≤ β / (1 - δ)` for every unit `y`. -/
theorem sphere_net_upper {k m : Type*} [Fintype k] [Fintype m] (A : Matrix k m ℂ)
    {N : Finset (m → ℂ)} {δ β : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hN : ∀ y : m → ℂ, ∑ i, ‖y i‖ ^ 2 = 1 → ∃ v ∈ N, ∑ i, ‖y i - v i‖ ^ 2 ≤ δ ^ 2)
    (hβ : ∀ v ∈ N, Real.sqrt (∑ a, ‖(A *ᵥ v) a‖ ^ 2) ≤ β) (y : m → ℂ)
    (hy : ∑ i, ‖y i‖ ^ 2 = 1) :
    Real.sqrt (∑ a, ‖(A *ᵥ y) a‖ ^ 2) ≤ β / (1 - δ) := by
  obtain ⟨f, hf⟩ := sphereNet_clm A
  obtain ⟨v₀, hv₀, -⟩ := hN y hy
  have hβ0 : 0 ≤ β := (Real.sqrt_nonneg _).trans (hβ v₀ hv₀)
  have hop := sphereNet_opNorm_le f hδ0 hδ1 hN (fun v hv => by rw [hf]; exact hβ v hv) hβ0
  rw [← hf]
  calc ‖f (WithLp.toLp 2 y)‖ ≤ ‖f‖ * ‖(WithLp.toLp 2 y : EuclideanSpace ℂ m)‖ := f.le_opNorm _
    _ = ‖f‖ := by rw [sphereNet_norm_eq_one y hy, mul_one]
    _ ≤ β / (1 - δ) := hop

/-- Lower bound from a net: if moreover `α ≤ ‖A v‖` on `N`, then
`α - δ β / (1 - δ) ≤ ‖A y‖` for every unit `y`. -/
theorem sphere_net_lower {k m : Type*} [Fintype k] [Fintype m] (A : Matrix k m ℂ)
    {N : Finset (m → ℂ)} {δ α β : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hN : ∀ y : m → ℂ, ∑ i, ‖y i‖ ^ 2 = 1 → ∃ v ∈ N, ∑ i, ‖y i - v i‖ ^ 2 ≤ δ ^ 2)
    (hα : ∀ v ∈ N, α ≤ Real.sqrt (∑ a, ‖(A *ᵥ v) a‖ ^ 2))
    (hβ : ∀ v ∈ N, Real.sqrt (∑ a, ‖(A *ᵥ v) a‖ ^ 2) ≤ β) (y : m → ℂ)
    (hy : ∑ i, ‖y i‖ ^ 2 = 1) :
    α - δ * β / (1 - δ) ≤ Real.sqrt (∑ a, ‖(A *ᵥ y) a‖ ^ 2) := by
  obtain ⟨f, hf⟩ := sphereNet_clm A
  obtain ⟨v, hv, hyv⟩ := hN y hy
  have hβ0 : 0 ≤ β := (Real.sqrt_nonneg _).trans (hβ v hv)
  have hop := sphereNet_opNorm_le f hδ0 hδ1 hN (fun v hv => by rw [hf]; exact hβ v hv) hβ0
  have h1 := sphereNet_norm_sub_le hδ0 y v hyv
  have h6 := hα v hv
  rw [← hf] at h6 ⊢
  set x : EuclideanSpace ℂ m := WithLp.toLp 2 y
  set w : EuclideanSpace ℂ m := WithLp.toLp 2 v
  have h2 : ‖f (x - w)‖ ≤ ‖f‖ * ‖x - w‖ := f.le_opNorm _
  have h3 : ‖f w‖ ≤ ‖f x‖ + ‖f (x - w)‖ := by
    calc ‖f w‖ = ‖f x - f (x - w)‖ := by rw [← map_sub, sub_sub_cancel]
      _ ≤ _ := norm_sub_le _ _
  have h4 : ‖f‖ * ‖x - w‖ ≤ ‖f‖ * δ := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  have h5 : ‖f‖ * δ ≤ β / (1 - δ) * δ := mul_le_mul_of_nonneg_right hop hδ0
  have h7 : δ * β / (1 - δ) = β / (1 - δ) * δ := by ring
  rw [h7]
  linarith

end LSBA
