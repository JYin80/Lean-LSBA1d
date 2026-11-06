import Mathlib

/-!
# Finite norming by Fekete points

Lemma 7.6 [uvc:lem:fekete], (7.13) [uvc:eq:finite-norming]: for a subspace `𝒱` of functions on a
finite set there is a set `S` of at most `dim 𝒱` points such that the sup norm of `Z − F` is
controlled by its maximum on `S` and the distances of `Z` and `F` to `𝒱`.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The evaluation matrix of a basis `b` of a space of functions at the points `ξ`. -/
private def feketeMat {X : Type*} {V : Submodule ℂ (X → ℂ)} {d : ℕ} (b : Module.Basis (Fin d) ℂ V)
    (ξ : Fin d → X) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => (b j : X → ℂ) (ξ i)

/-- Some point tuple has a nonvanishing evaluation determinant. -/
private theorem fekete_exists_det_ne {X : Type*} [Fintype X] {V : Submodule ℂ (X → ℂ)} {d : ℕ}
    (b : Module.Basis (Fin d) ℂ V) : ∃ ξ : Fin d → X, (feketeMat b ξ).det ≠ 0 := by
  let B : Matrix X (Fin d) ℂ := Matrix.of fun x j => (b j : X → ℂ) x
  have hinj : Function.Injective B.mulVecLin := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have hc' : B.mulVec c = 0 := hc
    have hzero : ∑ i, c i • b i = 0 := by
      apply Subtype.ext
      funext x
      have := congrFun hc' x
      simpa [B, Matrix.mulVec, dotProduct, Submodule.coe_sum, Finset.sum_apply, mul_comm]
        using this
    exact funext fun i => Fintype.linearIndependent_iff.mp b.linearIndependent c hzero i
  have hrank : B.rank = d := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]
  have htop : Submodule.span ℂ (Set.range B.row) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by
      rw [← Matrix.rank_eq_finrank_span_row, hrank, Module.finrank_fin_fun])
  obtain ⟨t, ht, hspan, hli⟩ := exists_linearIndependent ℂ (Set.range B.row)
  have hfin : t.Finite := (Set.finite_range _).subset ht
  have : Fintype t := hfin.fintype
  have hcard : Fintype.card t = d := by
    rw [← finrank_span_eq_card hli, Subtype.range_coe, hspan, htop, finrank_top,
      Module.finrank_fin_fun]
  let e : Fin d ≃ t := (Fintype.equivFinOfCardEq hcard).symm
  choose ξ hξ using fun i => Set.mem_range.mp (ht (e i).2)
  have hrow : (feketeMat b ξ).row = fun i => ((e i : t) : Fin d → ℂ) := by
    funext i
    rw [← hξ i]
    rfl
  have hind : LinearIndependent ℂ (feketeMat b ξ).row := by
    rw [hrow]
    exact hli.comp e e.injective
  refine ⟨ξ, ?_⟩
  have hu := Matrix.linearIndependent_row_iff_isUnit.mp hind
  exact (isUnit_iff_ne_zero).mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)

/-- Lagrange interpolation at the points of maximal evaluation determinant: the weights are
bounded by one. -/
private theorem fekete_lagrange {X : Type*} [Fintype X] (V : Submodule ℂ (X → ℂ)) :
    ∃ S : Finset X, S.card ≤ Module.finrank ℂ V ∧ ∀ h ∈ V, ∀ C : ℝ, (∀ s ∈ S, ‖h s‖ ≤ C) →
      ∀ x : X, ‖h x‖ ≤ (Module.finrank ℂ V : ℝ) * C := by
  set d := Module.finrank ℂ V with hd
  let b : Module.Basis (Fin d) ℂ V := Module.finBasis ℂ V
  obtain ⟨ξ₁, hξ₁⟩ := fekete_exists_det_ne b
  have : Nonempty (Fin d → X) := ⟨ξ₁⟩
  obtain ⟨ξ, hξ⟩ := Finite.exists_max (fun ξ : Fin d → X => ‖(feketeMat b ξ).det‖)
  have hdet : (feketeMat b ξ).det ≠ 0 := by
    intro h0
    have := hξ ξ₁
    rw [h0, norm_zero] at this
    exact hξ₁ (norm_le_zero_iff.mp this)
  refine ⟨Finset.univ.image ξ, ?_, ?_⟩
  · exact (Finset.card_image_le).trans (by simp)
  intro h hh C hC x
  set M := feketeMat b ξ with hM
  set c : Fin d → ℂ := fun j => b.repr ⟨h, hh⟩ j with hc
  have hexp : ∀ y, h y = ∑ j, c j * (b j : X → ℂ) y := by
    intro y
    have h1 : ((∑ j, b.repr ⟨h, hh⟩ j • b j : V) : X → ℂ) y = h y := by rw [b.sum_repr]
    rw [← h1, Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hc]
  set bx : Fin d → ℂ := fun j => (b j : X → ℂ) x with hbx
  set r : Fin d → ℂ := (M.det)⁻¹ • Matrix.cramer Mᵀ bx with hr
  have hrM : Mᵀ.mulVec r = bx := by
    rw [hr, Matrix.mulVec_smul, Matrix.mulVec_cramer, Matrix.det_transpose, smul_smul,
      inv_mul_cancel₀ hdet, one_smul]
  have hri : ∀ i, r i = (M.det)⁻¹ * (feketeMat b (Function.update ξ i x)).det := by
    intro i
    have hup : M.updateRow i bx = feketeMat b (Function.update ξ i x) := by
      ext k j
      by_cases hk : k = i
      · subst hk; simp [Matrix.updateRow_apply, feketeMat, hbx]
      · simp [Matrix.updateRow_apply, feketeMat, hk, hM]
    rw [hr, Pi.smul_apply, Matrix.cramer_transpose_apply, hup, smul_eq_mul]
  have hrle : ∀ i, ‖r i‖ ≤ 1 := by
    intro i
    rw [hri i, norm_mul, norm_inv]
    have hpos : 0 < ‖M.det‖ := norm_pos_iff.mpr hdet
    rw [inv_mul_le_iff₀ hpos, mul_one]
    exact hξ _
  have hsum : h x = ∑ i, r i * h (ξ i) := by
    have h1 : ∀ j, bx j = ∑ i, M i j * r i := by
      intro j
      have := congrFun hrM j
      simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm] using this.symm
    calc h x = ∑ j, c j * bx j := hexp x
      _ = ∑ j, c j * ∑ i, M i j * r i := by simp_rw [← h1]
      _ = ∑ i, r i * ∑ j, c j * M i j := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ i, r i * h (ξ i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hexp (ξ i)]
          rfl
  rw [hsum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖r i * h (ξ i)‖ ≤ ∑ _i : Fin d, (1 * C) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul]
        exact mul_le_mul (hrle i) (hC _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
          (norm_nonneg _) zero_le_one
    _ = (d : ℝ) * C := by simp

/-- Lemma 7.6 [uvc:lem:fekete], (7.13) [uvc:eq:finite-norming] in the form with arbitrary
approximants: for a space `𝒱` of functions on a finite set there are at most `d₀ = dim 𝒱` points
with `|Z - F| ≤ d₀ max_S |Z - F| + (d₀ + 1)(‖Z - v‖_∞ + ‖F - v'‖_∞)` for all `v, v' ∈ 𝒱`. -/
theorem fekete_norming {X : Type*} [Fintype X] (V : Submodule ℂ (X → ℂ)) :
    ∃ S : Finset X, S.card ≤ Module.finrank ℂ V ∧ ∀ (Z F v v' : X → ℂ), v ∈ V → v' ∈ V →
      ∀ x : X, ‖Z x - F x‖ ≤ (Module.finrank ℂ V : ℝ) * (⨆ s : S, ‖Z s - F s‖) +
        ((Module.finrank ℂ V : ℝ) + 1) * (‖Z - v‖ + ‖F - v'‖) := by
  obtain ⟨S, hS, hbound⟩ := fekete_lagrange V
  refine ⟨S, hS, ?_⟩
  intro Z F v v' hv hv' x
  set d : ℝ := (Module.finrank ℂ V : ℝ) with hd
  set M : ℝ := ⨆ s : S, ‖Z s - F s‖ with hM
  set e : ℝ := ‖Z - v‖ + ‖F - v'‖ with he
  have hZv : ∀ y, ‖Z y - v y‖ ≤ ‖Z - v‖ := fun y => by
    simpa using norm_le_pi_norm (Z - v) y
  have hFv : ∀ y, ‖F y - v' y‖ ≤ ‖F - v'‖ := fun y => by
    simpa using norm_le_pi_norm (F - v') y
  have hsplit : ∀ y, Z y - F y = (v - v') y + (Z y - v y) - (F y - v' y) := fun y => by
    simp only [Pi.sub_apply]; ring
  have hMs : ∀ s ∈ S, ‖Z s - F s‖ ≤ M := fun s hs =>
    le_ciSup (f := fun t : S => ‖Z t - F t‖) (Set.finite_range _).bddAbove (⟨s, hs⟩ : S)
  have hlag := hbound (v - v') (V.sub_mem hv hv') (M + e) (fun s hs => by
    have h1 := hsplit s
    have h2 : (v - v') s = (Z s - F s) - (Z s - v s) + (F s - v' s) := by
      simp only [Pi.sub_apply] at h1 ⊢
      linear_combination -h1
    rw [h2]
    calc ‖(Z s - F s) - (Z s - v s) + (F s - v' s)‖
        ≤ ‖Z s - F s‖ + ‖Z s - v s‖ + ‖F s - v' s‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ M + e := by
          have := hMs s hs
          have := hZv s
          have := hFv s
          simp only [he]; linarith) x
  rw [hsplit x]
  calc ‖(v - v') x + (Z x - v x) - (F x - v' x)‖
      ≤ ‖(v - v') x‖ + ‖Z x - v x‖ + ‖F x - v' x‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ d * M + (d + 1) * e := by
        have := hZv x
        have := hFv x
        simp only [he] at *
        nlinarith

/-- A choice of the sampling points of Lemma 7.6 [uvc:lem:fekete] for `𝒱`. -/
def feketeSet {X : Type*} [Fintype X] (V : Submodule ℂ (X → ℂ)) : Finset X :=
  (fekete_norming V).choose

/-- The defining property of `feketeSet`. -/
theorem feketeSet_spec {X : Type*} [Fintype X] (V : Submodule ℂ (X → ℂ)) :
    (feketeSet V).card ≤ Module.finrank ℂ V ∧ ∀ (Z F v v' : X → ℂ), v ∈ V → v' ∈ V →
      ∀ x : X, ‖Z x - F x‖ ≤ (Module.finrank ℂ V : ℝ) * (⨆ s : feketeSet V, ‖Z s - F s‖) +
        ((Module.finrank ℂ V : ℝ) + 1) * (‖Z - v‖ + ‖F - v'‖) :=
  (fekete_norming V).choose_spec

end LSBA
