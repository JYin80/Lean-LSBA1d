import Mathlib

/-!
# Half-nets of the unit ball

A `1/2`-net of the unit ball of `ℂ^m` with at most `5^{2|m|}` points, so that every operator
norm is at most twice a value on the net; used in the proof of Lemma 7.2
[uvs:lem:transfer-moments].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- A finite subset of the closed unit ball of `ℂ^m` whose points are pairwise more than `1/2`
apart has at most `5^{2|m|}` points: the open balls of radius `1/4` around the points are disjoint
and lie in the ball of radius `5/4`, and the Haar measure of a ball of radius `r` is `r^{2|m|}`
times that of the unit ball (proof of Lemma 7.2 [uvs:lem:transfer-moments]). -/
private lemma halfNet_packing {m : Type*} [Fintype m] (S : Finset (EuclideanSpace ℂ m))
    (hS : ∀ s ∈ S, ‖s‖ ≤ 1) (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 / 2 < dist s t) :
    S.card ≤ 5 ^ (2 * Fintype.card m) := by
  have hd : Module.finrank ℝ (EuclideanSpace ℂ m) = 2 * Fintype.card m := by
    rw [finrank_real_of_complex]; simp
  have hdisj :
      (S : Set (EuclideanSpace ℂ m)).PairwiseDisjoint (fun s => Metric.ball s (1 / 4)) := by
    intro s hs t ht hst
    have := hsep s hs t ht hst
    exact Metric.ball_disjoint_ball (by linarith)
  have hsub : (⋃ s ∈ S, Metric.ball s (1 / 4)) ⊆ Metric.ball (0 : EuclideanSpace ℂ m) (5 / 4) := by
    intro y hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨s, hs, hy⟩ := hy
    rw [mem_ball_zero_iff]
    have h1 := hS s hs
    have h2 : ‖y - s‖ < 1 / 4 := by simpa [dist_eq_norm] using hy
    calc ‖y‖ = ‖(y - s) + s‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - s‖ + ‖s‖ := norm_add_le _ _
      _ < 5 / 4 := by linarith
  have hle := measure_mono (μ := (volume : Measure (EuclideanSpace ℂ m))) hsub
  rw [measure_biUnion_finset hdisj (fun s _ => measurableSet_ball)] at hle
  have hq : (0 : ℝ) < 1 / 4 := by norm_num
  have hp : (0 : ℝ) < 5 / 4 := by norm_num
  rw [Finset.sum_congr rfl
    (fun s _ => Measure.addHaar_ball_of_pos (volume : Measure (EuclideanSpace ℂ m)) s hq),
    Measure.addHaar_ball_of_pos (volume : Measure (EuclideanSpace ℂ m)) 0 hp,
    Finset.sum_const, nsmul_eq_mul, hd, ← mul_assoc] at hle
  have hc0 : (volume : Measure (EuclideanSpace ℂ m)) (Metric.ball 0 1) ≠ 0 :=
    (Metric.measure_ball_pos _ 0 one_pos).ne'
  have hctop : (volume : Measure (EuclideanSpace ℂ m)) (Metric.ball 0 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  rw [ENNReal.mul_le_mul_iff_left hc0 hctop] at hle
  have h3 : (S.card : ℝ) * (1 / 4) ^ (2 * Fintype.card m) ≤ (5 / 4) ^ (2 * Fintype.card m) := by
    rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast]
    exact hle
  have h4 : (S.card : ℝ) ≤ 5 ^ (2 * Fintype.card m) := by
    have h5 : (S.card : ℝ) * (1 / 4) ^ (2 * Fintype.card m) ≤
        5 ^ (2 * Fintype.card m) * (1 / 4) ^ (2 * Fintype.card m) := by
      rw [← mul_pow]; norm_num at h3 ⊢; exact h3
    exact le_of_mul_le_mul_right h5 (by positivity)
  exact_mod_cast h4


/-- A finite subset of the closed unit ball of `ℂ^m` that is pairwise more than `1/2` apart, of
maximal cardinality, is a `1/2`-net of the closed unit ball with at most `5^{2|m|}` points
(proof of Lemma 7.2 [uvs:lem:transfer-moments]). -/
private lemma halfNet_exists_cover (m : Type*) [Fintype m] :
    ∃ S : Finset (EuclideanSpace ℂ m), S.card ≤ 5 ^ (2 * Fintype.card m) ∧ (∀ s ∈ S, ‖s‖ ≤ 1) ∧
      ∀ x : EuclideanSpace ℂ m, ‖x‖ ≤ 1 → ∃ s ∈ S, ‖x - s‖ ≤ 1 / 2 := by
  let P : Finset (EuclideanSpace ℂ m) → Prop := fun S =>
    (∀ s ∈ S, ‖s‖ ≤ 1) ∧ ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 / 2 < dist s t
  let K : Set ℕ := {n | ∃ S, P S ∧ S.card = n}
  have hK0 : 1 ∈ K := ⟨{0}, ⟨by simp, by simp⟩, by simp⟩
  have hKbdd : BddAbove K := by
    refine ⟨5 ^ (2 * Fintype.card m), ?_⟩
    rintro n ⟨S, ⟨h1, h2⟩, rfl⟩
    exact halfNet_packing S h1 h2
  obtain ⟨S, hPS, hcard⟩ := Nat.sSup_mem ⟨1, hK0⟩ hKbdd
  have hmax : ∀ T, P T → T.card ≤ S.card := fun T hT => by
    rw [hcard]; exact le_csSup hKbdd ⟨T, hT, rfl⟩
  refine ⟨S, halfNet_packing S hPS.1 hPS.2, hPS.1, fun x hx => ?_⟩
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

/-- If a finite set `S` is a `1/2`-net of the closed unit ball of `ℂ^m`, then for every operator
`A` there is a point `v ∈ S` with `‖A‖ ≤ 2 ‖A v‖`: take `v` maximizing `‖A v‖` on `S`, so that
`‖A‖ ≤ ‖A v‖ + ‖A‖ / 2` (proof of Lemma 7.2 [uvs:lem:transfer-moments]). -/
private lemma halfNet_opNorm_le {m : Type*} [Fintype m] [DecidableEq m]
    (S : Finset (EuclideanSpace ℂ m))
    (hS : ∀ x : EuclideanSpace ℂ m, ‖x‖ ≤ 1 → ∃ s ∈ S, ‖x - s‖ ≤ 1 / 2)
    (A : Matrix m m ℂ) :
    ∃ v ∈ S, ‖A‖ ≤ 2 * ‖Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A v‖ := by
  set f := Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A with hf
  have hne : S.Nonempty := by
    obtain ⟨s, hs, -⟩ := hS 0 (by simp)
    exact ⟨s, hs⟩
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image S (fun s => ‖f s‖) hne
  refine ⟨v, hv, ?_⟩
  have key : ‖f‖ ≤ ‖f v‖ + ‖f‖ / 2 := by
    refine ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) (fun x hx => ?_)
    obtain ⟨s, hs, hxs⟩ := hS x hx.le
    have h1 : ‖f (x - s)‖ ≤ ‖f‖ * ‖x - s‖ := f.le_opNorm _
    have h2 : ‖f x‖ ≤ ‖f s‖ + ‖f (x - s)‖ := by
      calc ‖f x‖ = ‖f s + f (x - s)‖ := by rw [← map_add, add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have h3 : ‖f s‖ ≤ ‖f v‖ := hmax s hs
    have h4 : ‖f‖ * ‖x - s‖ ≤ ‖f‖ * (1 / 2) :=
      mul_le_mul_of_nonneg_left hxs (norm_nonneg _)
    linarith
  have : ‖A‖ = ‖f‖ := (Matrix.l2_opNorm_toEuclideanCLM A).symm
  linarith

/-- A `1/2`-net of the unit ball of `ℂ^m` with at most `5^{2|m|}` points: every operator norm is at
most twice a value on the net. -/
theorem exists_half_net (m : Type*) [Fintype m] [DecidableEq m] :
    ∃ N : Finset (m → ℂ), N.card ≤ 5 ^ (2 * Fintype.card m) ∧ (∀ v ∈ N, ∑ i, ‖v i‖ ^ 2 ≤ 1) ∧
      ∀ A : Matrix m m ℂ, ∃ v ∈ N, ‖A‖ ≤ 2 * Real.sqrt (∑ i, ‖(A *ᵥ v) i‖ ^ 2) := by
  obtain ⟨S, hcard, hball, hcover⟩ := halfNet_exists_cover m
  refine ⟨S.image (fun s => s.ofLp), (Finset.card_image_le).trans hcard, ?_, ?_⟩
  · intro v hv
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hv
    have h := hball s hs
    have h2 : ‖s‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg s]
    rwa [EuclideanSpace.norm_sq_eq] at h2
  · intro A
    obtain ⟨s, hs, h⟩ := halfNet_opNorm_le S hcover A
    refine ⟨s.ofLp, Finset.mem_image_of_mem _ hs, ?_⟩
    rw [EuclideanSpace.norm_eq] at h
    exact h

end LSBA
