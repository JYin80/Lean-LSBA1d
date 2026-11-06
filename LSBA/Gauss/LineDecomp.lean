import LSBA.Gauss.StdGauss
import LSBA.Model.Basic

/-!
# Decomposition of a Gaussian sample along a line

Tonelli along a unit direction of the standard Gaussian measure, and the scalar direction
`scalarDir W L S`: moving the sample along it adds a multiple of the identity to each block in `S`
(the trace part `V_x = V_x° + ξ_x I` of the proof of (8.7) [eq:c-apriori]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `x` with its `i`-th coordinate replaced by `t`, on pairs `(x, t)`. -/
private def lineDecomp_upd {ι : Type*} [DecidableEq ι] (i : ι) (p : (ι → ℝ) × ℝ) : ι → ℝ :=
  Function.update p.1 i p.2

private lemma lineDecomp_measurable_upd {ι : Type*} [DecidableEq ι] (i : ι) :
    Measurable (lineDecomp_upd i) := by
  refine measurable_pi_iff.mpr fun j => ?_
  by_cases h : j = i
  · subst h
    simpa [lineDecomp_upd] using measurable_snd
  · simp only [lineDecomp_upd, Function.update_of_ne h]
    exact (measurable_pi_apply j).comp measurable_fst

private lemma lineDecomp_map_upd {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    ((stdGauss ι).prod (gaussianReal 0 1)).map (lineDecomp_upd i) = stdGauss ι := by
  symm
  unfold stdGauss
  refine Measure.pi_eq fun s hs => ?_
  have hm : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [Measure.map_apply (lineDecomp_measurable_upd i) hm]
  have hpre : lineDecomp_upd i ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi (Function.update s i Set.univ)) ×ˢ s i := by
    ext ⟨ω, t⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod,
      lineDecomp_upd]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h i⟩
      by_cases hj : j = i
      · subst hj; simp
      · simpa [Function.update_of_ne hj] using h j
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h2
      · simpa [Function.update_of_ne hj] using h1 j
  have hfun : (Measure.pi fun _ : ι => gaussianReal 0 1)
        (Set.univ.pi (Function.update s i Set.univ)) =
      ∏ j ∈ Finset.univ.erase i, gaussianReal 0 1 (s j) := by
    rw [Measure.pi_pi, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [Function.update_self, measure_univ, one_mul]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hpre, Measure.prod_prod, hfun, mul_comm,
    Finset.mul_prod_erase Finset.univ (fun j => gaussianReal 0 1 (s j)) (Finset.mem_univ i)]

/-- A self-inverse linear isometry of `ℝ^ι` exchanging `e` and the `i₀`-th basis vector. -/
private lemma lineDecomp_exists_iso {ι : Type*} [Fintype ι] (e : ι → ℝ)
    (he : ∑ i, e i ^ 2 = 1) (i₀ : ι) :
    ∃ R : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι,
      (∀ x, R (R x) = x) ∧ R (WithLp.toLp 2 e) = EuclideanSpace.single i₀ 1 := by
  have hn : ‖(WithLp.toLp 2 e : EuclideanSpace ℝ ι)‖ = ‖(EuclideanSpace.single i₀ (1 : ℝ))‖ := by
    rw [EuclideanSpace.norm_eq]
    simp [he]
  refine ⟨(ℝ ∙ ((WithLp.toLp 2 e : EuclideanSpace ℝ ι) - EuclideanSpace.single i₀ 1))ᗮ.reflection,
    fun x => Submodule.reflection_reflection _ x, Submodule.reflection_sub hn⟩

private lemma lineDecomp_measurePreserving {ι : Type*} [Fintype ι] (e : ι → ℝ)
    (he : ∑ i, e i ^ 2 = 1) :
    MeasurePreserving
      (fun p : (ι → ℝ) × ℝ => p.1 - (∑ i, p.1 i * e i) • e + p.2 • e)
      ((stdGauss ι).prod (gaussianReal 0 1)) (stdGauss ι) := by
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at he
  obtain ⟨i₀⟩ := hne
  obtain ⟨R, hRR, hRe⟩ := lineDecomp_exists_iso e he i₀
  set f : (ι → ℝ) → (ι → ℝ) := fun x => (R (WithLp.toLp 2 x)).ofLp with hf
  have hfmp : MeasurePreserving f (stdGauss ι) (stdGauss ι) :=
    measurePreserving_stdGauss_linearIsometry R
  have hff : ∀ x, f (f x) = x := fun x => by simp [hf, hRR]
  have hfe : f (Pi.single i₀ 1) = e := by
    have : R (EuclideanSpace.single i₀ 1) = WithLp.toLp 2 e := by
      rw [← hRe, hRR]
    simp [hf, this]
  have hfadd : ∀ x y, f (x + y) = f x + f y := fun x y => by simp [hf]
  have hfsmul : ∀ (c : ℝ) x, f (c • x) = c • f x := fun c x => by simp [hf]
  have hcoord : ∀ x, f x i₀ = ∑ i, x i * e i := fun x => by
    have hR1 : R (EuclideanSpace.single i₀ 1) = WithLp.toLp 2 e := by rw [← hRe, hRR]
    have h1 := R.inner_map_map (EuclideanSpace.single i₀ (1 : ℝ)) (R (WithLp.toLp 2 x))
    rw [hR1, hRR] at h1
    rw [EuclideanSpace.inner_single_left] at h1
    simp only [hf]
    rw [← one_mul ((R (WithLp.toLp 2 x)).ofLp i₀)]
    simp only [PiLp.inner_apply] at h1
    simpa [mul_comm] using h1.symm
  have hcomp : (fun p : (ι → ℝ) × ℝ => p.1 - (∑ i, p.1 i * e i) • e + p.2 • e) =
      f ∘ lineDecomp_upd i₀ ∘ Prod.map f id := by
    funext ⟨ω, t⟩
    have hupd : lineDecomp_upd i₀ (f ω, t) = f ω + (t - f ω i₀) • Pi.single i₀ 1 := by
      funext j
      by_cases hj : j = i₀
      · subst hj; simp [lineDecomp_upd]
      · simp [lineDecomp_upd, hj]
    simp only [Function.comp, Prod.map, id, hupd, hfadd, hfsmul, hff, hfe, hcoord]
    rw [sub_smul]
    abel
  rw [hcomp]
  have hid : MeasurePreserving (id : ℝ → ℝ) (gaussianReal 0 1) (gaussianReal 0 1) :=
    MeasurePreserving.id _
  have hupd : MeasurePreserving (lineDecomp_upd i₀) ((stdGauss ι).prod (gaussianReal 0 1))
      (stdGauss ι) := ⟨lineDecomp_measurable_upd i₀, lineDecomp_map_upd i₀⟩
  exact hfmp.comp (hupd.comp (hfmp.prod hid))

/-- Gaussian line decomposition: along a unit vector `e`, `ω = ω - ⟨ω, e⟩ e + t e` with
`t ~ N(0, 1)` independent of the orthogonal part. -/
theorem lintegral_stdGauss_line {ι : Type*} [Fintype ι] (e : ι → ℝ) (he : ∑ i, e i ^ 2 = 1)
    {F : (ι → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F ω ∂(stdGauss ι) =
      ∫⁻ ω, ∫⁻ t, F (ω - (∑ i, ω i * e i) • e + t • e) ∂(gaussianReal 0 1) ∂(stdGauss ι) := by
  have hmp := lineDecomp_measurePreserving e he
  rw [← hmp.lintegral_comp hF]
  exact lintegral_prod _ (hF.comp hmp.measurable).aemeasurable

/-- The unit direction moving every block in `S` by the same multiple of the identity. -/
def scalarDir (W L : ℕ) (S : Finset (Fin L)) : Ω W L :=
  fun p => if p.1 ∈ S ∧ p.2.1 = p.2.2 then (Real.sqrt ((W : ℝ) * S.card))⁻¹ else 0

theorem sum_sq_scalarDir {W L : ℕ} (hW : 1 ≤ W) {S : Finset (Fin L)} (hS : S.Nonempty) :
    ∑ p, scalarDir W L S p ^ 2 = 1 := by
  have hpos : 0 < (W : ℝ) * S.card := by
    have : (0 : ℝ) < W := by exact_mod_cast hW
    have : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    positivity
  have hsq : (Real.sqrt ((W : ℝ) * S.card))⁻¹ ^ 2 = ((W : ℝ) * S.card)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hpos.le]
  simp only [scalarDir, Fintype.sum_prod_type, ite_pow, hsq]
  simp only [ite_and, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  have hin : ∀ (x : Fin L) (y : Fin W),
      ∑ z : Fin W, (if x ∈ S then (if y = z then ((W : ℝ) * S.card)⁻¹ else 0) else 0) =
        if x ∈ S then ((W : ℝ) * S.card)⁻¹ else 0 := by
    intro x y
    by_cases h : x ∈ S <;> simp [h]
  simp only [hin]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hW0 : (W : ℝ) ≠ 0 := by positivity
  have hS0 : (S.card : ℝ) ≠ 0 := by positivity
  field_simp

/-- Moving the sample along `scalarDir W L S` by `t` adds `t / (W √|S|)` times the identity
to each block in `S` (the scalar part `ξ_x I_W` in the proof of (8.7) [eq:c-apriori]). -/
theorem gueBlock_add_smul_scalarDir (W L : ℕ) (S : Finset (Fin L)) (ω : Ω W L) (t : ℝ)
    (a : Fin L) :
    gueBlock W L (ω + t • scalarDir W L S) a =
      gueBlock W L ω a +
        if a ∈ S then (((t / ((W : ℝ) * Real.sqrt S.card) : ℝ)) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)
        else 0 := by
  ext α β
  by_cases hαβ : α = β
  · subst hαβ
    by_cases ha : a ∈ S
    · simp only [gueBlock, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, scalarDir, ha, true_and, ite_true, Matrix.smul_apply, Matrix.one_apply_eq]
      have hWp : (0 : ℝ) < W := by exact_mod_cast α.pos
      have hSp : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr ⟨a, ha⟩
      have h1 : Real.sqrt W ≠ 0 := (Real.sqrt_pos.mpr hWp).ne'
      have h2 : Real.sqrt S.card ≠ 0 := (Real.sqrt_pos.mpr hSp).ne'
      have key : (ω (a, α, α) + t * (Real.sqrt ((W : ℝ) * S.card))⁻¹) / Real.sqrt W =
          ω (a, α, α) / Real.sqrt W + t / ((W : ℝ) * Real.sqrt S.card) := by
        rw [Real.sqrt_mul hWp.le]
        rw [show (W : ℝ) * Real.sqrt S.card = Real.sqrt W * Real.sqrt W * Real.sqrt S.card by
          rw [Real.mul_self_sqrt hWp.le]]
        field_simp
      have key' := congrArg (fun x : ℝ => (x : ℂ)) key
      simp only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_mul] at key' ⊢
      rw [mul_one]
      exact key'
    · simp [gueBlock, scalarDir, ha]
  · by_cases ha : a ∈ S
    · simp [gueBlock, scalarDir, hαβ, Ne.symm hαβ, ha]
    · simp [gueBlock, scalarDir, hαβ, ha]

end LSBA
