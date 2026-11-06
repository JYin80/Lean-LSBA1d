import LSBA.Upper.Operator

/-!
# The semigroup property of the operator

The operator of a batch of `q m` blocks is `P_{1/2}^m` on bounded measurable functions, and the
first line of (8.20) [cc:eq:iterate] `(P_{1/2}^k 1)(U, Y) = 𝔼 e^{−c(F_k ⋯ F_1; U, Y)/2}`, by
independence of the batches and the cocycle identity (Lemma 8.6 [up:lem:operator-reduction]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The operator of a batch of `q m` blocks is `P_{1/2}^m` (independence and the cocycle
identity; proofs of Lemma 8.6 [up:lem:operator-reduction] and of Theorems 3.2
[thm:sharp-small-upper] and 3.3 [thm:compact-upper]). -/
theorem halfOp_mul_eq_iterate {W : ℕ} (g E : ℝ) (q m : ℕ) {h : IsoFlag W → ℝ}
    (hh : IsBddMeas h) : halfOp W g E (q * m) h = (halfOp W g E q)^[m] h := by
  -- the operator of zero blocks is the identity
  have hbase : ∀ h : IsoFlag W → ℝ, halfOp W g E 0 h = h := by
    intro h
    funext x
    have hS : (freeConj W 0)ᴴ * freeConj W 0 = 1 := by
      have := Matrix.mem_unitaryGroup_iff'.mp (freeConj_zero_mem_unitaryGroup W)
      rwa [Matrix.star_eq_conjTranspose] at this
    have hB : ∀ ω : Ω W 0, batchMat W g E 0 ω = 1 := fun ω => by
      simp [batchMat, transferProd, hS]
    have hc : ∀ ω : Ω W 0, volCocycle (batchMat W g E 0 ω) x = 0 := fun ω => by
      rw [hB]
      exact volCocycle_of_mem_unitaryGroup (one_mem _) x
    have hf : ∀ ω : Ω W 0, flagAct (batchMat W g E 0 ω) x = x := fun ω => by
      rw [hB]
      obtain ⟨⟨-, hUU, -, -⟩, -, hYY, -⟩ := x.2
      apply Subtype.ext
      rw [flagAct_coe (by simp) x, flagProj_of_mem_unitaryGroup (one_mem _) hUU,
        flagProj_of_mem_unitaryGroup (one_mem _) hYY]
      simp
    unfold halfOp
    simp [hc, hf]
  -- the operator of `n + q` blocks is the operator of `n` blocks after that of `q` blocks
  have hstep : ∀ (n : ℕ) {h : IsoFlag W → ℝ}, IsBddMeas h → ∀ x : IsoFlag W,
      halfOp W g E (n + q) h x = halfOp W g E n (halfOp W g E q h) x := by
    intro n h hh x
    set F : Ω W n × Ω W q → ℝ := fun p =>
      Real.exp (-volCocycle (batchMat W g E n p.1) x / 2) *
        (Real.exp (-volCocycle (batchMat W g E q p.2) (flagAct (batchMat W g E n p.1) x) / 2) *
          h (flagAct (batchMat W g E q p.2) (flagAct (batchMat W g E n p.1) x))) with hF
    have hkey : ∀ ω : Ω W (n + q),
        Real.exp (-volCocycle (batchMat W g E (n + q) ω) x / 2) *
          h (flagAct (batchMat W g E (n + q) ω) x) = F (blockAppend W n q ω) := by
      intro ω
      have h1 := batchMat_mem_isoGroup W g E n (blockAppend W n q ω).1
      have h2 := batchMat_mem_isoGroup W g E q (blockAppend W n q ω).2
      have hu : IsUnit (batchMat W g E q (blockAppend W n q ω).2) :=
        (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [h2.2]; exact isUnit_one)
      rw [batchMat_add, volCocycle_mul h1.1 hu, flagAct_mul h1.1 h2.1]
      simp only [hF]
      rw [neg_add, add_div, Real.exp_add]
      ring
    have hFm : Measurable F := by
      obtain ⟨hm, -⟩ := hh
      have hBn : Measurable fun p : Ω W n × Ω W q => batchMat W g E n p.1 :=
        (measurable_batchMat W g E n).comp measurable_fst
      have hBq : Measurable fun p : Ω W n × Ω W q => batchMat W g E q p.2 :=
        (measurable_batchMat W g E q).comp measurable_snd
      have hp1 : Measurable fun p : Ω W n × Ω W q => (batchMat W g E n p.1, x) :=
        hBn.prodMk measurable_const
      have hy := (measurable_flagAct W).comp hp1
      have hp2 : Measurable fun p : Ω W n × Ω W q =>
          (batchMat W g E q p.2, flagAct (batchMat W g E n p.1) x) :=
        hBq.prodMk hy
      have h1 := (measurable_volCocycle W).comp hp1
      have h2 := (measurable_volCocycle W).comp hp2
      have h3 := (measurable_flagAct W).comp hp2
      exact (Real.measurable_exp.comp (h1.neg.div_const 2)).mul
        ((Real.measurable_exp.comp (h2.neg.div_const 2)).mul (hm.comp h3))
    have hint : Integrable F ((μ W n).prod (μ W q)) := by
      have h0 := integrable_halfOp g E (n + q) hh x
      have h0' : Integrable (F ∘ blockAppend W n q) (μ W (n + q)) :=
        h0.congr (Filter.Eventually.of_forall fun ω => hkey ω)
      exact ((measurePreserving_blockAppend W n q).integrable_comp
        hFm.aestronglyMeasurable).mp h0'
    have hmap : ∫ ω, F (blockAppend W n q ω) ∂(μ W (n + q)) =
        ∫ p, F p ∂((μ W n).prod (μ W q)) := by
      have := integral_map_of_stronglyMeasurable (μ := μ W (n + q))
        (measurePreserving_blockAppend W n q).measurable hFm.stronglyMeasurable
      rw [(measurePreserving_blockAppend W n q).map_eq] at this
      exact this.symm
    calc halfOp W g E (n + q) h x
        = ∫ ω, F (blockAppend W n q ω) ∂(μ W (n + q)) :=
          integral_congr_ae (Filter.Eventually.of_forall hkey)
      _ = ∫ p, F p ∂((μ W n).prod (μ W q)) := hmap
      _ = ∫ ω₁, ∫ ω₂, F (ω₁, ω₂) ∂(μ W q) ∂(μ W n) := integral_prod F hint
      _ = halfOp W g E n (halfOp W g E q h) x := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ω₁ => ?_)
          change ∫ ω₂, F (ω₁, ω₂) ∂(μ W q) =
            Real.exp (-volCocycle (batchMat W g E n ω₁) x / 2) *
              halfOp W g E q h (flagAct (batchMat W g E n ω₁) x)
          simp only [hF]
          rw [integral_const_mul]
          rfl
  induction m generalizing h with
  | zero =>
    rw [Nat.mul_zero]
    exact hbase h
  | succ m ih =>
    rw [Nat.mul_succ]
    funext x
    rw [hstep (q * m) hh x, Function.iterate_succ_apply,
      ← congrFun (ih (halfOp_isBddMeas g E q hh)) x]

/-- The first line of (8.20) [cc:eq:iterate]: `(P_{1/2}^k 1)(U, Y) = 𝔼 e^{-c(F_k ⋯ F_1; U, Y)/2}`.
-/
theorem iterate_halfOp_one (W : ℕ) (g E : ℝ) (q k : ℕ) (x : IsoFlag W) :
    (halfOp W g E q)^[k] (fun _ => 1) x =
      ∫ ω, Real.exp (-volCocycle (batchMat W g E (q * k) ω) x / 2) ∂(μ W (q * k)) := by
  have h := congrFun (halfOp_mul_eq_iterate g E q k (h := fun _ => (1 : ℝ))
    ⟨measurable_const, 1, by simp⟩) x
  rw [← h]
  unfold halfOp
  simp only [mul_one]

end LSBA
