import LSBA.Upper.ScoreFrame
import LSBA.Gauss.DivergenceMoment
import LSBA.Gauss.NormTail

/-!
# The active part of the Gaussian divergence

(9.35) [su:eq:matrix-source-derivative-comparison]–(9.34)
[su:eq:active-matrix-derivative-bound] in the proof of Lemma 9.4 [us:lem:score]: at a fixed
preparation, `𝔼 δ_act² ≤ C 𝔼[‖P v_4‖² Σ_a ‖(e_a · ∇_{v_4})(χ̂ K̂)‖²_HS] + C W (1 + M₀²) 𝔼 ‖χ K‖²_HS
+ C W M₀ e^{-c W}`, with `C, c` depending only on the pointwise bound `C_K` of `‖K‖²_HS`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Polynomial growth and Gaussian integrability -/

private lemma ScoreActive_pg_nonneg {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : E → F} {C : ℝ} {k : ℕ} (h : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k) : 0 ≤ C := by
  simpa using (norm_nonneg _).trans (h 0)

private lemma ScoreActive_pg_mono {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedAddCommGroup G] {f : E → F} {g : E → G} (h : ∀ x, ‖f x‖ ≤ ‖g x‖)
    (hg : PolyGrowth g) : PolyGrowth f := by
  obtain ⟨C, k, hC⟩ := hg
  exact ⟨C, k, fun x => (h x).trans (hC x)⟩

private lemma ScoreActive_pg_norm {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : E → F} (hf : PolyGrowth f) : PolyGrowth (fun x => ‖f x‖) :=
  ScoreActive_pg_mono (fun x => by rw [norm_norm]) hf

private lemma ScoreActive_pg_const {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (c : F) : PolyGrowth (fun _ : E => c) :=
  ⟨‖c‖, 0, fun x => by simp⟩

/-- A function of linear growth `‖f x‖ ≤ a ‖x‖ + b` has polynomial growth. -/
private lemma ScoreActive_pg_lin {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : E → F} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : ∀ x, ‖f x‖ ≤ a * ‖x‖ + b) :
    PolyGrowth f :=
  ⟨a + b, 1, fun x => by
    have := norm_nonneg x
    calc ‖f x‖ ≤ a * ‖x‖ + b := h x
      _ ≤ (a + b) * (1 + ‖x‖) ^ 1 := by nlinarith⟩

private lemma ScoreActive_pg_add {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f g : E → F} (hf : PolyGrowth f) (hg : PolyGrowth g) :
    PolyGrowth (fun x => f x + g x) := by
  obtain ⟨C₁, k₁, h₁⟩ := hf
  obtain ⟨C₂, k₂, h₂⟩ := hg
  have hC₁ := ScoreActive_pg_nonneg h₁
  have hC₂ := ScoreActive_pg_nonneg h₂
  refine ⟨C₁ + C₂, max k₁ k₂, fun x => ?_⟩
  have hs : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have e1 : (1 + ‖x‖) ^ k₁ ≤ (1 + ‖x‖) ^ max k₁ k₂ := pow_le_pow_right₀ hs (le_max_left _ _)
  have e2 : (1 + ‖x‖) ^ k₂ ≤ (1 + ‖x‖) ^ max k₁ k₂ := pow_le_pow_right₀ hs (le_max_right _ _)
  calc ‖f x + g x‖ ≤ ‖f x‖ + ‖g x‖ := norm_add_le _ _
    _ ≤ C₁ * (1 + ‖x‖) ^ k₁ + C₂ * (1 + ‖x‖) ^ k₂ := add_le_add (h₁ x) (h₂ x)
    _ ≤ (C₁ + C₂) * (1 + ‖x‖) ^ max k₁ k₂ := by rw [add_mul]; gcongr

private lemma ScoreActive_pg_sub {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f g : E → F} (hf : PolyGrowth f) (hg : PolyGrowth g) :
    PolyGrowth (fun x => f x - g x) := by
  have hng : PolyGrowth (fun x => -g x) := ScoreActive_pg_mono (fun x => by rw [norm_neg]) hg
  simpa only [sub_eq_add_neg] using ScoreActive_pg_add hf hng

private lemma ScoreActive_pg_mul {E : Type*} [NormedAddCommGroup E] {f g : E → ℝ}
    (hf : PolyGrowth f) (hg : PolyGrowth g) : PolyGrowth (fun x => f x * g x) := by
  obtain ⟨C₁, k₁, h₁⟩ := hf
  obtain ⟨C₂, k₂, h₂⟩ := hg
  have hC₁ := ScoreActive_pg_nonneg h₁
  refine ⟨C₁ * C₂, k₁ + k₂, fun x => ?_⟩
  calc ‖f x * g x‖ = ‖f x‖ * ‖g x‖ := norm_mul _ _
    _ ≤ (C₁ * (1 + ‖x‖) ^ k₁) * (C₂ * (1 + ‖x‖) ^ k₂) :=
        mul_le_mul (h₁ x) (h₂ x) (norm_nonneg _) (mul_nonneg hC₁ (by positivity))
    _ = C₁ * C₂ * (1 + ‖x‖) ^ (k₁ + k₂) := by ring

private lemma ScoreActive_pg_sum {E F κ : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (s : Finset κ) {f : κ → E → F} (hf : ∀ k ∈ s, PolyGrowth (f k)) :
    PolyGrowth (fun x => ∑ k ∈ s, f k x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (ScoreActive_pg_const (E := E) (0 : F))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact ScoreActive_pg_add (hf a (Finset.mem_insert_self _ _))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

/-- Polynomial moments of the sup norm are finite under the standard Gaussian on `ℝ^ι`. -/
private lemma ScoreActive_integrable_poly (ι : Type*) [Fintype ι] (m : ℕ) :
    Integrable (fun x : ι → ℝ => (1 + ‖x‖) ^ m) (stdGauss ι) := by
  classical
  have hpow1 : Integrable (fun x : ℝ => (1 + |x|) ^ m) (gaussianReal 0 1) := by
    have hm : MemLp id (m : ENNReal) (gaussianReal (0 : ℝ) 1) :=
      memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := 1) m (ENNReal.natCast_ne_top m)
    have hm' : MemLp id (m : ℕ) (gaussianReal (0 : ℝ) 1) := by simpa using hm
    have h1 : Integrable (fun x : ℝ => ‖id x‖ ^ m) (gaussianReal 0 1) := hm'.integrable_norm_pow'
    have h2 : Integrable (fun x : ℝ => (2 : ℝ) ^ m * (1 + |x| ^ m)) (gaussianReal 0 1) :=
      ((integrable_const (1 : ℝ)).add (by simpa using h1)).const_mul _
    refine h2.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (by fun_prop : Continuous fun x : ℝ => (1 + |x|) ^ m).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity)]
      have h2m : (0 : ℝ) ≤ 2 ^ m := by positivity
      have hx : (0 : ℝ) ≤ |x| ^ m := by positivity
      rcases le_total |x| 1 with h | h
      · calc (1 + |x|) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
          _ ≤ 2 ^ m * (1 + |x| ^ m) := by nlinarith
      · calc (1 + |x|) ^ m ≤ (2 * |x|) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
          _ = 2 ^ m * |x| ^ m := by rw [mul_pow]
          _ ≤ 2 ^ m * (1 + |x| ^ m) := by nlinarith
  have hprod : ∀ x : ι → ℝ, 1 + ‖x‖ ≤ ∏ j, (1 + |x j|) := by
    intro x
    have hone : ∀ s : Finset ι, (1 : ℝ) ≤ ∏ l ∈ s, (1 + |x l|) := fun s =>
      Finset.one_le_prod₀ fun l _ => by linarith [abs_nonneg (x l)]
    have : ‖x‖ ≤ (∏ j, (1 + |x j|)) - 1 := by
      refine (pi_norm_le_iff_of_nonneg (by linarith [hone Finset.univ])).mpr fun j => ?_
      have hj : 1 + |x j| ≤ ∏ l, (1 + |x l|) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
        exact le_mul_of_one_le_right (by positivity) (hone _)
      rw [Real.norm_eq_abs]
      linarith
    linarith
  have hp : Integrable (fun x : ι → ℝ => ∏ j, (1 + |x j|) ^ m) (stdGauss ι) :=
    Integrable.fintype_prod (f := fun _ (t : ℝ) => (1 + |t|) ^ m) (fun _ => hpow1)
  refine hp.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (by fun_prop : Continuous fun x : ι → ℝ => (1 + ‖x‖) ^ m).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity), Finset.prod_pow]
    exact pow_le_pow_left₀ (by positivity) (hprod x) m

/-- A continuous function of polynomial growth is integrable under the standard Gaussian. -/
private lemma ScoreActive_integrable {ι : Type*} [Fintype ι] {g : (ι → ℝ) → ℝ}
    (hc : Continuous g) (hg : PolyGrowth g) : Integrable g (stdGauss ι) := by
  obtain ⟨C, k, hC⟩ := hg
  refine ((ScoreActive_integrable_poly ι k).const_mul C).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, ← Real.norm_eq_abs]
  exact hC x

/-! ### Test functions -/

/-- `C¹` with the function and its derivative of polynomial growth. -/
private def ScoreActive_Good {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) : Prop :=
  ContDiff ℝ 1 f ∧ PolyGrowth f ∧ PolyGrowth (fderiv ℝ f)

private lemma ScoreActive_Good.diff {ι : Type*} [Fintype ι] {f : (ι → ℝ) → ℝ}
    (hf : ScoreActive_Good f) (x : ι → ℝ) : DifferentiableAt ℝ f x :=
  hf.1.differentiable one_ne_zero x

private lemma ScoreActive_Good.integrable_mul {ι : Type*} [Fintype ι] {f g : (ι → ℝ) → ℝ}
    (hf : ScoreActive_Good f) (hg : ScoreActive_Good g) :
    Integrable (fun x => f x * g x) (stdGauss ι) :=
  ScoreActive_integrable (hf.1.continuous.mul hg.1.continuous) (ScoreActive_pg_mul hf.2.1 hg.2.1)

private lemma ScoreActive_Good.mul {ι : Type*} [Fintype ι] {f g : (ι → ℝ) → ℝ}
    (hf : ScoreActive_Good f) (hg : ScoreActive_Good g) :
    ScoreActive_Good (fun x => f x * g x) := by
  refine ⟨hf.1.mul hg.1, ScoreActive_pg_mul hf.2.1 hg.2.1, ?_⟩
  have h : fderiv ℝ (fun x => f x * g x) =
      fun x => f x • fderiv ℝ g x + g x • fderiv ℝ f x :=
    funext fun x => fderiv_fun_mul (hf.diff x) (hg.diff x)
  rw [h]
  refine ScoreActive_pg_mono (g := fun x => ‖f x‖ * ‖fderiv ℝ g x‖ + ‖g x‖ * ‖fderiv ℝ f x‖)
    (fun x => ?_) (ScoreActive_pg_add
      (ScoreActive_pg_mul (ScoreActive_pg_norm hf.2.1) (ScoreActive_pg_norm hg.2.2))
      (ScoreActive_pg_mul (ScoreActive_pg_norm hg.2.1) (ScoreActive_pg_norm hf.2.2)))
  calc ‖f x • fderiv ℝ g x + g x • fderiv ℝ f x‖
      ≤ ‖f x • fderiv ℝ g x‖ + ‖g x • fderiv ℝ f x‖ := norm_add_le _ _
    _ = ‖f x‖ * ‖fderiv ℝ g x‖ + ‖g x‖ * ‖fderiv ℝ f x‖ := by rw [norm_smul, norm_smul]
    _ ≤ ‖‖f x‖ * ‖fderiv ℝ g x‖ + ‖g x‖ * ‖fderiv ℝ f x‖‖ := le_abs_self _

private lemma ScoreActive_Good.sub {ι : Type*} [Fintype ι] {f g : (ι → ℝ) → ℝ}
    (hf : ScoreActive_Good f) (hg : ScoreActive_Good g) :
    ScoreActive_Good (fun x => f x - g x) := by
  refine ⟨hf.1.sub hg.1, ScoreActive_pg_sub hf.2.1 hg.2.1, ?_⟩
  have h : fderiv ℝ (fun x => f x - g x) = fun x => fderiv ℝ f x - fderiv ℝ g x :=
    funext fun x => fderiv_fun_sub (hf.diff x) (hg.diff x)
  rw [h]
  exact ScoreActive_pg_sub hf.2.2 hg.2.2

private lemma ScoreActive_Good.sum {ι κ : Type*} [Fintype ι] (s : Finset κ)
    {f : κ → (ι → ℝ) → ℝ} (hf : ∀ k ∈ s, ScoreActive_Good (f k)) :
    ScoreActive_Good (fun x => ∑ k ∈ s, f k x) := by
  refine ⟨ContDiff.sum fun k hk => (hf k hk).1,
    ScoreActive_pg_sum s fun k hk => (hf k hk).2.1, ?_⟩
  have h : fderiv ℝ (fun x => ∑ k ∈ s, f k x) = fun x => ∑ k ∈ s, fderiv ℝ (f k) x :=
    funext fun x => fderiv_fun_sum fun k hk => (hf k hk).diff x
  rw [h]
  exact ScoreActive_pg_sum s fun k hk => (hf k hk).2.2

/-- An affine function `x ↦ B x + c` is a test function. -/
private lemma ScoreActive_Good.affine {ι : Type*} [Fintype ι] (B : (ι → ℝ) →L[ℝ] ℝ) (c : ℝ) :
    ScoreActive_Good (fun x => B x + c) := by
  refine ⟨B.contDiff.add contDiff_const,
    ScoreActive_pg_lin (norm_nonneg B) (norm_nonneg c) fun x =>
      (norm_add_le _ _).trans (by gcongr; exact B.le_opNorm x), ?_⟩
  have h : fderiv ℝ (fun x => B x + c) = fun _ => B :=
    funext fun x => (B.hasFDerivAt.add_const c).fderiv
  rw [h]
  exact ScoreActive_pg_const B

/-- A `C²` function with bounded first and second derivatives is a test function, and so is
`x ↦ D a(x) (A x + z)` for an affine `x ↦ A x + z`. -/
private lemma ScoreActive_Good.of_bdd {ι : Type*} [Fintype ι] {a : (ι → ℝ) → ℝ}
    (ha : ContDiff ℝ 2 a) {M : ℝ}
    (hM : ∀ x, |a x| ≤ M ∧ ‖fderiv ℝ a x‖ ≤ M ∧ ‖fderiv ℝ (fderiv ℝ a) x‖ ≤ M)
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) (z : ι → ℝ) :
    ScoreActive_Good a ∧ ScoreActive_Good (fun x => fderiv ℝ a x (A x + z)) ∧
      ∀ x, HasFDerivAt (fun y => fderiv ℝ a y (A y + z))
        ((fderiv ℝ a x).comp A + (fderiv ℝ (fderiv ℝ a) x).flip (A x + z)) x := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0).1
  have ha1 : ContDiff ℝ 1 (fderiv ℝ a) := ha.fderiv_right (by norm_num)
  have hlin : ∀ x, ‖A x + z‖ ≤ ‖A‖ * ‖x‖ + ‖z‖ := fun x =>
    (norm_add_le _ _).trans (by gcongr; exact A.le_opNorm x)
  have hd : ∀ x, HasFDerivAt (fun y => fderiv ℝ a y (A y + z))
      ((fderiv ℝ a x).comp A + (fderiv ℝ (fderiv ℝ a) x).flip (A x + z)) x := fun x =>
    ((ha1.differentiable one_ne_zero x).hasFDerivAt).clm_apply (A.hasFDerivAt.add_const z)
  refine ⟨⟨ha.of_le (by norm_num), ⟨M, 0, fun x => by simpa using (hM x).1⟩,
    ⟨M, 0, fun x => by simpa using (hM x).2.1⟩⟩, ⟨ha1.clm_apply (A.contDiff.add contDiff_const),
    ScoreActive_pg_lin (mul_nonneg hM0 (norm_nonneg A)) (mul_nonneg hM0 (norm_nonneg z))
      fun x => ?_, ?_⟩, hd⟩
  · calc ‖fderiv ℝ a x (A x + z)‖ ≤ ‖fderiv ℝ a x‖ * ‖A x + z‖ := (fderiv ℝ a x).le_opNorm _
      _ ≤ M * (‖A‖ * ‖x‖ + ‖z‖) :=
          mul_le_mul (hM x).2.1 (hlin x) (norm_nonneg _) hM0
      _ = M * ‖A‖ * ‖x‖ + M * ‖z‖ := by ring
  · have h : fderiv ℝ (fun y => fderiv ℝ a y (A y + z)) = fun x =>
        (fderiv ℝ a x).comp A + (fderiv ℝ (fderiv ℝ a) x).flip (A x + z) :=
      funext fun x => (hd x).fderiv
    rw [h]
    refine ScoreActive_pg_lin (mul_nonneg hM0 (norm_nonneg A))
      (add_nonneg (mul_nonneg hM0 (norm_nonneg A)) (mul_nonneg hM0 (norm_nonneg z))) fun x => ?_
    have h1 : ‖(fderiv ℝ (fderiv ℝ a) x).flip (A x + z)‖ ≤
        ‖fderiv ℝ (fderiv ℝ a) x‖ * ‖A x + z‖ := by
      calc _ ≤ ‖(fderiv ℝ (fderiv ℝ a) x).flip‖ * ‖A x + z‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = _ := by rw [ContinuousLinearMap.opNorm_flip]
    calc ‖(fderiv ℝ a x).comp A + (fderiv ℝ (fderiv ℝ a) x).flip (A x + z)‖
        ≤ ‖(fderiv ℝ a x).comp A‖ + ‖(fderiv ℝ (fderiv ℝ a) x).flip (A x + z)‖ :=
          norm_add_le _ _
      _ ≤ ‖fderiv ℝ a x‖ * ‖A‖ + ‖fderiv ℝ (fderiv ℝ a) x‖ * ‖A x + z‖ :=
          add_le_add ((fderiv ℝ a x).opNorm_comp_le A) h1
      _ ≤ M * ‖A‖ + M * (‖A‖ * ‖x‖ + ‖z‖) :=
          add_le_add (mul_le_mul_of_nonneg_right (hM x).2.1 (norm_nonneg _))
            (mul_le_mul (hM x).2.2 (hlin x) (norm_nonneg _) hM0)
      _ = M * ‖A‖ * ‖x‖ + (M * ‖A‖ + M * ‖z‖) := by ring

/-! ### Gaussian integration by parts along affine fields -/

/-- `𝔼[ψ δ_G Z] = 𝔼[D_Z ψ]` for a test function `ψ` and an affine field `Z x = A x + z`: the
field `ψ Z` is admissible, and its divergence is `ψ δ_G Z - D_Z ψ`. -/
private lemma ScoreActive_ibp {ι : Type*} [Fintype ι] [DecidableEq ι] {ψ : (ι → ℝ) → ℝ}
    (hψ : ScoreActive_Good ψ) (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) (z : ι → ℝ) :
    Integrable (fun x => ψ x * gaussDiv (fun y => A y + z) x - fderiv ℝ ψ x (A x + z))
      (stdGauss ι) ∧
    ∫ x, (ψ x * gaussDiv (fun y => A y + z) x - fderiv ℝ ψ x (A x + z)) ∂(stdGauss ι) = 0 := by
  have hlin : ∀ x, ‖A x + z‖ ≤ ‖A‖ * ‖x‖ + ‖z‖ := fun x =>
    (norm_add_le _ _).trans (by gcongr; exact A.le_opNorm x)
  have hZ : PolyGrowth (fun x => A x + z) :=
    ScoreActive_pg_lin (norm_nonneg A) (norm_nonneg z) hlin
  have hYd : ∀ x, HasFDerivAt (fun y => ψ y • (A y + z))
      (ψ x • A + (fderiv ℝ ψ x).smulRight (A x + z)) x := fun x =>
    (hψ.diff x).hasFDerivAt.smul (A.hasFDerivAt.add_const z)
  have hY : ContDiff ℝ 1 (fun y => ψ y • (A y + z)) := hψ.1.smul (A.contDiff.add contDiff_const)
  have hb : PolyGrowth (fun y => ψ y • (A y + z)) :=
    ScoreActive_pg_mono (g := fun x => ‖ψ x‖ * ‖A x + z‖)
      (fun x => by rw [norm_smul]; exact le_abs_self _)
      (ScoreActive_pg_mul (ScoreActive_pg_norm hψ.2.1) (ScoreActive_pg_norm hZ))
  have hb' : PolyGrowth (fderiv ℝ (fun y => ψ y • (A y + z))) := by
    have h : fderiv ℝ (fun y => ψ y • (A y + z)) =
        fun x => ψ x • A + (fderiv ℝ ψ x).smulRight (A x + z) := funext fun x => (hYd x).fderiv
    rw [h]
    refine ScoreActive_pg_mono (g := fun x => ‖ψ x‖ * ‖A‖ + ‖fderiv ℝ ψ x‖ * ‖A x + z‖)
      (fun x => ?_) (ScoreActive_pg_add
        (ScoreActive_pg_mul (ScoreActive_pg_norm hψ.2.1) (ScoreActive_pg_const _))
        (ScoreActive_pg_mul (ScoreActive_pg_norm hψ.2.2) (ScoreActive_pg_norm hZ)))
    calc ‖ψ x • A + (fderiv ℝ ψ x).smulRight (A x + z)‖
        ≤ ‖ψ x • A‖ + ‖(fderiv ℝ ψ x).smulRight (A x + z)‖ := norm_add_le _ _
      _ = ‖ψ x‖ * ‖A‖ + ‖fderiv ℝ ψ x‖ * ‖A x + z‖ := by
          rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
      _ ≤ ‖‖ψ x‖ * ‖A‖ + ‖fderiv ℝ ψ x‖ * ‖A x + z‖‖ := le_abs_self _
  have hI := ibpAdmissible_of_contDiff hY hb hb'
  have htest : IsIBPTest (fun _ : ι → ℝ => (1 : ℝ)) :=
    ⟨contDiff_const, ⟨1, fun _ => by simp⟩, ⟨0, 0, fun x => by simp⟩⟩
  obtain ⟨-, hi2, hi3⟩ := hI.2 _ htest
  have hdiv : ∀ x, gaussDiv (fun y => ψ y • (A y + z)) x =
      ψ x * gaussDiv (fun y => A y + z) x - fderiv ℝ ψ x (A x + z) := fun x =>
    gaussDiv_smul (hψ.diff x) fun i =>
      (differentiableAt_pi.1 (A.differentiableAt.add_const z) i).lineDifferentiableAt
  simp only [one_mul, hdiv] at hi2 hi3
  refine ⟨hi2, ?_⟩
  rw [← hi3]
  simp

/-- The Stein identity (9.32) [su:eq:active-divergence-decomposition] for abstract data: for
`C²` coefficients `a_k` with bounded derivatives, affine fields `Z_k x = A_k x + z_k` with linear
divergence `δ_G Z_k = B_k`, and `δ = Σ_k (a_k B_k - D_{Z_k} a_k)`,
`𝔼 δ² = 𝔼 Σ_{l,j} (D_{Z_j} a_l D_{Z_l} a_j + a_l a_j D_{Z_l} B_j
+ a_l D_{A_l Z_j - A_j Z_l} a_j)`. -/
private lemma ScoreActive_stein {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (a : κ → (ι → ℝ) → ℝ) (A : κ → (ι → ℝ) →L[ℝ] (ι → ℝ)) (z : κ → ι → ℝ)
    (B : κ → (ι → ℝ) →L[ℝ] ℝ) (ha : ∀ k, ContDiff ℝ 2 (a k)) {M : ℝ}
    (hM : ∀ k x, |a k x| ≤ M ∧ ‖fderiv ℝ (a k) x‖ ≤ M ∧ ‖fderiv ℝ (fderiv ℝ (a k)) x‖ ≤ M)
    (hb : ∀ k x, gaussDiv (fun y => A k y + z k) x = B k x) :
    ∫⁻ x, ENNReal.ofReal ((∑ k, (a k x * B k x - fderiv ℝ (a k) x (A k x + z k))) ^ 2)
      ∂(stdGauss ι) ≤
    ∫⁻ x, ENNReal.ofReal (∑ l, ∑ j, (fderiv ℝ (a l) x (A j x + z j) *
        fderiv ℝ (a j) x (A l x + z l) + a l x * a j x * B j (A l x + z l) +
        a l x * fderiv ℝ (a j) x (A l (A j x + z j) - A j (A l x + z l)))) ∂(stdGauss ι) := by
  -- the test functions
  have hGa : ∀ k, ScoreActive_Good (a k) := fun k =>
    (ScoreActive_Good.of_bdd (ha k) (hM k) (A k) (z k)).1
  have hGd : ∀ j l, ScoreActive_Good (fun x => fderiv ℝ (a j) x (A l x + z l)) := fun j l =>
    (ScoreActive_Good.of_bdd (ha j) (hM j) (A l) (z l)).2.1
  have hDd : ∀ j l x, HasFDerivAt (fun y => fderiv ℝ (a j) y (A l y + z l))
      ((fderiv ℝ (a j) x).comp (A l) + (fderiv ℝ (fderiv ℝ (a j)) x).flip (A l x + z l)) x :=
    fun j l => (ScoreActive_Good.of_bdd (ha j) (hM j) (A l) (z l)).2.2
  set δ : (ι → ℝ) → ℝ := fun x => ∑ k, (a k x * B k x - fderiv ℝ (a k) x (A k x + z k))
    with hδ
  have hGδ : ScoreActive_Good δ := ScoreActive_Good.sum _ fun k _ =>
    ((hGa k).mul (by simpa using ScoreActive_Good.affine (B k) 0)).sub (hGd k k)
  have hDa : ∀ k x, HasFDerivAt (a k) (fderiv ℝ (a k) x) x := fun k x =>
    ((hGa k).diff x).hasFDerivAt
  have hDδ : ∀ x, HasFDerivAt δ (∑ k, (a k x • B k + B k x • fderiv ℝ (a k) x -
      ((fderiv ℝ (a k) x).comp (A k) + (fderiv ℝ (fderiv ℝ (a k)) x).flip (A k x + z k)))) x := by
    intro x
    have h := HasFDerivAt.sum (u := Finset.univ) fun k _ =>
      ((hDa k x).mul (B k).hasFDerivAt).sub (hDd k k x)
    convert h using 1
    funext y
    simp [hδ, Finset.sum_apply]
  -- the integration by parts
  have hI1 := fun l => ScoreActive_ibp ((hGa l).mul hGδ) (A l) (z l)
  have hI2 := fun l j => ScoreActive_ibp ((hGa l).mul (hGd j l)) (A j) (z j)
  -- the pointwise identity
  set T : (ι → ℝ) → ℝ := fun x => ∑ l, ∑ j, (fderiv ℝ (a l) x (A j x + z j) *
      fderiv ℝ (a j) x (A l x + z l) + a l x * a j x * B j (A l x + z l) +
      a l x * fderiv ℝ (a j) x (A l (A j x + z j) - A j (A l x + z l))) with hT
  set S1 : (ι → ℝ) → ℝ := fun x => ∑ l, ((a l x * δ x) * gaussDiv (fun y => A l y + z l) x -
      fderiv ℝ (fun y => a l y * δ y) x (A l x + z l)) with hS1
  set S2 : (ι → ℝ) → ℝ := fun x => ∑ l, ∑ j, ((a l x * fderiv ℝ (a j) x (A l x + z l)) *
      gaussDiv (fun y => A j y + z j) x -
      fderiv ℝ (fun y => a l y * fderiv ℝ (a j) y (A l y + z l)) x (A j x + z j)) with hS2
  have hpt : ∀ x, δ x ^ 2 = T x + S1 x + S2 x := by
    intro x
    have hsym : ∀ j u w, fderiv ℝ (fderiv ℝ (a j)) x u w = fderiv ℝ (fderiv ℝ (a j)) x w u :=
      fun j u w => ((ha j).contDiffAt.isSymmSndFDerivAt (by simp)).eq u w
    have h1 : ∀ l, fderiv ℝ (fun y => a l y * δ y) x (A l x + z l) =
        a l x * ∑ j, (a j x * B j (A l x + z l) + B j x * fderiv ℝ (a j) x (A l x + z l) -
          (fderiv ℝ (a j) x (A j (A l x + z l)) +
            fderiv ℝ (fderiv ℝ (a j)) x (A l x + z l) (A j x + z j))) +
        δ x * fderiv ℝ (a l) x (A l x + z l) := by
      intro l
      rw [show (fun y => a l y * δ y) = a l * δ from rfl, ((hDa l x).mul (hDδ x)).fderiv]
      simp only [_root_.add_apply, _root_.smul_apply,
        _root_.sum_apply, _root_.sub_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
    have h2 : ∀ l j, fderiv ℝ (fun y => a l y * fderiv ℝ (a j) y (A l y + z l)) x
        (A j x + z j) = a l x * (fderiv ℝ (a j) x (A l (A j x + z j)) +
          fderiv ℝ (fderiv ℝ (a j)) x (A j x + z j) (A l x + z l)) +
        fderiv ℝ (a j) x (A l x + z l) * fderiv ℝ (a l) x (A j x + z j) := by
      intro l j
      rw [show (fun y => a l y * fderiv ℝ (a j) y (A l y + z l)) =
        a l * fun y => fderiv ℝ (a j) y (A l y + z l) from rfl, ((hDa l x).mul (hDd j l x)).fderiv]
      simp only [_root_.add_apply, _root_.smul_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
    simp only [hS1, hS2, hb, h1, h2]
    have key : ∀ l j, (fderiv ℝ (a l) x (A j x + z j) * fderiv ℝ (a j) x (A l x + z l) +
        a l x * a j x * B j (A l x + z l) +
        a l x * fderiv ℝ (a j) x (A l (A j x + z j) - A j (A l x + z l))) -
        a l x * (a j x * B j (A l x + z l) + B j x * fderiv ℝ (a j) x (A l x + z l) -
          (fderiv ℝ (a j) x (A j (A l x + z l)) +
            fderiv ℝ (fderiv ℝ (a j)) x (A l x + z l) (A j x + z j))) +
        (a l x * fderiv ℝ (a j) x (A l x + z l) * B j x -
          (a l x * (fderiv ℝ (a j) x (A l (A j x + z j)) +
            fderiv ℝ (fderiv ℝ (a j)) x (A j x + z j) (A l x + z l)) +
          fderiv ℝ (a j) x (A l x + z l) * fderiv ℝ (a l) x (A j x + z j))) = 0 := by
      intro l j
      rw [map_sub, hsym j (A l x + z l) (A j x + z j)]
      ring
    have hl : ∀ l, ∑ j, (fderiv ℝ (a l) x (A j x + z j) * fderiv ℝ (a j) x (A l x + z l) +
          a l x * a j x * B j (A l x + z l) +
          a l x * fderiv ℝ (a j) x (A l (A j x + z j) - A j (A l x + z l))) +
        (a l x * δ x * B l x - (a l x * ∑ j, (a j x * B j (A l x + z l) +
          B j x * fderiv ℝ (a j) x (A l x + z l) - (fderiv ℝ (a j) x (A j (A l x + z l)) +
            fderiv ℝ (fderiv ℝ (a j)) x (A l x + z l) (A j x + z j))) +
          δ x * fderiv ℝ (a l) x (A l x + z l))) +
        ∑ j, (a l x * fderiv ℝ (a j) x (A l x + z l) * B j x -
          (a l x * (fderiv ℝ (a j) x (A l (A j x + z j)) +
            fderiv ℝ (fderiv ℝ (a j)) x (A j x + z j) (A l x + z l)) +
          fderiv ℝ (a j) x (A l x + z l) * fderiv ℝ (a l) x (A j x + z j))) =
        δ x * (a l x * B l x - fderiv ℝ (a l) x (A l x + z l)) := by
      intro l
      have hs := Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => key l j
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
      simp only [Finset.sum_const_zero] at hs
      linear_combination hs
    calc δ x ^ 2 = ∑ l, δ x * (a l x * B l x - fderiv ℝ (a l) x (A l x + z l)) := by
          rw [sq, ← Finset.mul_sum]
      _ = _ := by
          rw [Finset.sum_congr rfl fun l _ => (hl l).symm]
          simp only [hT, Finset.sum_add_distrib]
  have hδ2 : Integrable (fun x => δ x ^ 2) (stdGauss ι) := by
    simpa only [sq] using hGδ.integrable_mul hGδ
  have hS1i : Integrable S1 (stdGauss ι) := integrable_finsetSum _ fun l _ => (hI1 l).1
  have hS2i : Integrable S2 (stdGauss ι) :=
    integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun j _ => (hI2 l j).1
  have hS1z : ∫ x, S1 x ∂(stdGauss ι) = 0 := by
    rw [hS1, integral_finsetSum _ fun l _ => (hI1 l).1]
    exact Finset.sum_eq_zero fun l _ => (hI1 l).2
  have hS2z : ∫ x, S2 x ∂(stdGauss ι) = 0 := by
    rw [hS2, integral_finsetSum _ fun l _ => integrable_finsetSum _ fun j _ => (hI2 l j).1]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [integral_finsetSum _ fun j _ => (hI2 l j).1]
    exact Finset.sum_eq_zero fun j _ => (hI2 l j).2
  have hTi : Integrable T (stdGauss ι) :=
    ((hδ2.sub hS1i).sub hS2i).congr (ae_of_all _ fun x => by
      simp only [Pi.sub_apply]
      rw [hpt x]
      ring)
  have hδT : ∫ x, δ x ^ 2 ∂(stdGauss ι) = ∫ x, T x ∂(stdGauss ι) := by
    calc ∫ x, δ x ^ 2 ∂(stdGauss ι) = ∫ x, (T x + S1 x + S2 x) ∂(stdGauss ι) :=
          integral_congr_ae (ae_of_all _ hpt)
      _ = ∫ x, T x ∂(stdGauss ι) := by
          rw [integral_add (f := fun x => T x + S1 x) (hTi.add hS1i) hS2i, integral_add hTi hS1i,
            hS1z, hS2z]
          ring
  rw [← ofReal_integral_eq_lintegral_ofReal hδ2 (ae_of_all _ fun x => sq_nonneg _), hδT,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hTi]
  exact (ENNReal.ofReal_le_ofReal (sub_le_self _ ENNReal.toReal_nonneg)).trans
    ENNReal.ofReal_toReal_le

/-! ### Matrix inequalities -/

private lemma ScoreActive_hsSq_nonneg {k l : Type*} [Fintype k] [Fintype l] (A : Matrix k l ℂ) :
    0 ≤ hsSq A := by
  unfold hsSq; positivity

private lemma ScoreActive_hsSq_real_smul {k l : Type*} [Fintype k] [Fintype l] (r : ℝ)
    (A : Matrix k l ℂ) : hsSq (r • A) = r ^ 2 * hsSq A := by
  unfold hsSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [mul_pow, sq_abs]

private lemma ScoreActive_hsSq_sub_le {k l : Type*} [Fintype k] [Fintype l]
    (A B : Matrix k l ℂ) : hsSq (A - B) ≤ 2 * hsSq A + 2 * hsSq B := by
  unfold hsSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  simp only [Matrix.sub_apply]
  have h := norm_sub_le (A a b) (B a b)
  nlinarith [norm_nonneg (A a b), norm_nonneg (B a b), sq_nonneg (‖A a b‖ - ‖B a b‖),
    norm_nonneg (A a b - B a b)]

private lemma ScoreActive_hsSq_conjTranspose {k l : Type*} [Fintype k] [Fintype l]
    (A : Matrix k l ℂ) : hsSq Aᴴ = hsSq A := by
  unfold hsSq
  rw [Finset.sum_comm]
  simp [Matrix.conjTranspose_apply]

/-- `‖A x‖² ≤ ‖A‖²_op ‖x‖²`. -/
private lemma ScoreActive_sum_sq_mulVec_le {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ)
    (x : Fin W → ℂ) : ∑ a, ‖(A *ᵥ x) a‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ c, ‖x c‖ ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec A ((EuclideanSpace.equiv (Fin W) ℂ).symm x)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)] at h2
  simpa using h2

/-- `|A_{ab}| ≤ ‖A‖_op`. -/
private lemma ScoreActive_entry_le {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) (a b : Fin W) :
    ‖A a b‖ ≤ ‖A‖ := by
  have h := ScoreActive_sum_sq_mulVec_le A (Pi.single b 1)
  have h1 : ∑ c, ‖(Pi.single b (1 : ℂ) : Fin W → ℂ) c‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single b (fun c _ hc => by simp [hc]) (by simp)]
    simp
  have h2 : ‖A a b‖ ^ 2 ≤ ∑ a', ‖(A *ᵥ Pi.single b 1) a'‖ ^ 2 := by
    have := Finset.single_le_sum (f := fun a' => ‖(A *ᵥ Pi.single b (1 : ℂ)) a'‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ a)
    simpa [Matrix.mulVec_single_one] using this
  rw [h1, mul_one] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (h2.trans h)

/-- `‖A B‖²_HS ≤ ‖A‖²_op ‖B‖²_HS`. -/
private lemma ScoreActive_hsSq_opNorm_mul_le {W : ℕ} (A B : Matrix (Fin W) (Fin W) ℂ) :
    hsSq (A * B) ≤ ‖A‖ ^ 2 * hsSq B := by
  have hB : ‖A‖ ^ 2 * hsSq B = ∑ b, ‖A‖ ^ 2 * ∑ c, ‖B c b‖ ^ 2 := by
    unfold hsSq; rw [Finset.sum_comm, Finset.mul_sum]
  rw [hB]
  unfold hsSq
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun b _ => ?_
  have := ScoreActive_sum_sq_mulVec_le A (fun c => B c b)
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

/-- `‖[F, M]‖²_HS ≤ 4 ‖M‖²_op ‖F‖²_HS`. -/
private lemma ScoreActive_hsSq_comm_le {W : ℕ} (F M : Matrix (Fin W) (Fin W) ℂ) :
    hsSq (F * M - M * F) ≤ 4 * ‖M‖ ^ 2 * hsSq F := by
  have h1 := ScoreActive_hsSq_sub_le (F * M) (M * F)
  have h2 := ScoreActive_hsSq_opNorm_mul_le Mᴴ Fᴴ
  rw [← Matrix.conjTranspose_mul, ScoreActive_hsSq_conjTranspose,
    ScoreActive_hsSq_conjTranspose, Matrix.l2_opNorm_conjTranspose] at h2
  have h3 := ScoreActive_hsSq_opNorm_mul_le M F
  nlinarith

/-- `‖P‖_op ≤ 1` for an orthogonal projection `P`. -/
private lemma ScoreActive_norm_proj_le {W : ℕ} {P : Matrix (Fin W) (Fin W) ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) : ‖P‖ ≤ 1 := by
  have h := CStarRing.norm_star_mul_self (x := P)
  rw [Matrix.star_eq_conjTranspose, hP.eq, hPP] at h
  nlinarith [norm_nonneg P]

/-- `‖X‖²_HS = Σ_p (reCoord X)_p²`. -/
private lemma ScoreActive_hsSq_reCoord {k l : Type*} [Fintype k] [Fintype l]
    (X : Matrix k l ℂ) : hsSq X = ∑ p, reCoord X p ^ 2 := by
  rw [← (hsInner_reCoord X X 0).2.1, ← (hsInner_reCoord X X 0).2.2.2.2]
  simp only [sq]

/-- Cauchy–Schwarz for the trace: `(Re Tr(X Y))² ≤ ‖X‖²_HS ‖Y‖²_HS`. -/
private lemma ScoreActive_re_trace_sq_le {W : ℕ} (X Y : Matrix (Fin W) (Fin W) ℂ) :
    ((X * Y).trace.re) ^ 2 ≤ hsSq X * hsSq Y := by
  have h1 : (X * Y).trace.re = ∑ p, reCoord Xᴴ p * reCoord Y p := by
    rw [(hsInner_reCoord Xᴴ Y 0).2.2.2.2, (hsInner_reCoord Xᴴ Y 0).1,
      Matrix.conjTranspose_conjTranspose]
  rw [h1, ← ScoreActive_hsSq_conjTranspose X, ScoreActive_hsSq_reCoord,
    ScoreActive_hsSq_reCoord]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- `⟨H, -i F⟩ = ⟨i H, F⟩`. -/
private lemma ScoreActive_hsInner_smul_I {W : ℕ} (H F : Matrix (Fin W) (Fin W) ℂ) :
    hsInner H ((-Complex.I) • F) = hsInner (Complex.I • H) F := by
  unfold hsInner
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul, star_mul', Complex.star_def, Complex.conj_I]
  congr 1
  ring

/-- Bessel's inequality for the frame directions `i H_k`: `Σ_k ⟨i H_k, M⟩² ≤ ‖M‖²_HS`. -/
private lemma ScoreActive_bessel {W : ℕ} (M : Matrix (Fin W) (Fin W) ℂ) :
    ∑ k, hsInner (Complex.I • hermBasis W k) M ^ 2 ≤ hsSq M := by
  have h := (hermBasis_parseval W ((-Complex.I) • M)).1
  have hs : hsSq ((-Complex.I) • M) = hsSq M := by unfold hsSq; simp
  simp only [ScoreActive_hsInner_smul_I, hs] at h
  exact h

/-- The frame expansion `F = Σ_k ⟨i H_k, F⟩ K_k` of a skew-Hermitian `F = P F P`, with
`K_k = P (i H_k) P`. -/
private lemma ScoreActive_frame {W : ℕ} {P F : Matrix (Fin W) (Fin W) ℂ} (hF : Fᴴ = -F)
    (hPF : P * F * P = F) :
    F = ∑ k, hsInner (Complex.I • hermBasis W k) F • skewProjBasis P k := by
  have hM : ((-Complex.I) • F).IsHermitian := by
    change ((-Complex.I) • F)ᴴ = (-Complex.I) • F
    rw [Matrix.conjTranspose_smul, hF]
    simp
  have h1 := (hermBasis_parseval W ((-Complex.I) • F)).2 hM
  have h2 : F = Complex.I • ((-Complex.I) • F) := by simp [smul_smul]
  have h3 : F = ∑ k, ((hsInner (Complex.I • hermBasis W k) F : ℝ) : ℂ) •
      (Complex.I • hermBasis W k) := by
    conv_lhs => rw [h2, h1]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_comm, ScoreActive_hsInner_smul_I]
  calc F = P * F * P := hPF.symm
    _ = ∑ k, ((hsInner (Complex.I • hermBasis W k) F : ℝ) : ℂ) •
        (P * (Complex.I • hermBasis W k) * P) := by
      conv_lhs => rw [h3]
      rw [Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = _ := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Complex.coe_smul]
      rfl

/-- The commutator is real-linear in its first argument: `[Σ_l a_l X_l, B] = Σ_l a_l [X_l, B]`. -/
private lemma ScoreActive_sum_comm {W : ℕ} {κ : Type*} [Fintype κ] (a : κ → ℝ)
    (X : κ → Matrix (Fin W) (Fin W) ℂ) (B : Matrix (Fin W) (Fin W) ℂ) :
    (∑ l, a l • X l) * B - B * ∑ l, a l • X l = ∑ l, a l • (X l * B - B * X l) := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_sub, Matrix.smul_mul, Matrix.mul_smul]

/-- For `F = P F P` with `P` an orthogonal projection and `K_k = P (i H_k) P`,
`⟨i H_m, [F, K_j]⟩ = ⟨i H_j, [K_m, F]⟩` (ad-invariance in the frame). -/
private lemma ScoreActive_frame_swap {W : ℕ} {P F : Matrix (Fin W) (Fin W) ℂ}
    (hPF : P * F = F) (hFP : F * P = F) (m j : Fin W × Fin W) :
    hsInner (Complex.I • hermBasis W m) (F * skewProjBasis P j - skewProjBasis P j * F) =
      hsInner (Complex.I • hermBasis W j) (skewProjBasis P m * F - F * skewProjBasis P m) := by
  rw [(hsInner_reCoord _ _ 0).1, (hsInner_reCoord _ _ 0).1]
  congr 1
  unfold skewProjBasis
  have hx : (hermBasis W m)ᴴ = hermBasis W m := (hermBasis_isHermitian W m).eq
  have hy : (hermBasis W j)ᴴ = hermBasis W j := (hermBasis_isHermitian W j).eq
  set x := hermBasis W m
  set y := hermBasis W j
  have e1 : ∀ z : Matrix (Fin W) (Fin W) ℂ, F * (P * z * P) = F * z * P := fun z => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hFP]
  have e2 : ∀ z : Matrix (Fin W) (Fin W) ℂ, P * z * P * F = P * z * F := fun z => by
    rw [Matrix.mul_assoc (P * z), hPF]
  simp only [Matrix.conjTranspose_smul, hx, hy, Matrix.mul_smul, Matrix.smul_mul, e1, e2,
    ← smul_sub, smul_smul, Complex.star_def, Complex.conj_I, Matrix.trace_smul, smul_eq_mul]
  congr 1
  have t1 : (x * (F * y * P)).trace = (y * (P * x * F)).trace := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc (x * F), Matrix.trace_mul_comm,
      Matrix.mul_assoc, Matrix.mul_assoc]
  have t2 : (x * (P * y * F)).trace = (y * (F * x * P)).trace := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc (x * P), Matrix.trace_mul_comm,
      Matrix.mul_assoc, Matrix.mul_assoc]
  rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub, t1, t2]

/-- `Re(a* b) = Re(b* a)`. -/
private lemma ScoreActive_ip_comm {W : ℕ} (a b : Fin W → ℂ) :
    (star a ⬝ᵥ b).re = (star b ⬝ᵥ a).re := by
  simp only [dotProduct, Complex.re_sum, Pi.star_apply, Complex.star_def, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `tangProj P v` is symmetric for `(a, b) ↦ Re(a* b)`. -/
private lemma ScoreActive_tangProj_symm {W : ℕ} {P : Matrix (Fin W) (Fin W) ℂ}
    (hP : P.IsHermitian) (v a b : Fin W → ℂ) :
    (star a ⬝ᵥ tangProj P v b).re = (star (tangProj P v a) ⬝ᵥ b).re := by
  have hm : ∀ x w : Fin W → ℂ, star (P *ᵥ x) ⬝ᵥ w = star x ⬝ᵥ (P *ᵥ w) := fun x w => by
    rw [Matrix.star_mulVec, hP.eq, Matrix.dotProduct_mulVec]
  have hTe : ∀ x w : Fin W → ℂ, (star x ⬝ᵥ tangProj P v w).re = (star x ⬝ᵥ P *ᵥ w).re -
      (star (P *ᵥ v) ⬝ᵥ w).re / (∑ i, ‖(P *ᵥ v) i‖ ^ 2) * (star x ⬝ᵥ P *ᵥ v).re := fun x w => by
    rw [tangProj, dotProduct_sub, dotProduct_smul, smul_eq_mul, Complex.sub_re,
      Complex.re_ofReal_mul]
  rw [hTe a b, ScoreActive_ip_comm (tangProj P v a) b, hTe b a, ScoreActive_ip_comm a (P *ᵥ v),
    ScoreActive_ip_comm b (P *ᵥ v)]
  have h1 : (star a ⬝ᵥ P *ᵥ b).re = (star b ⬝ᵥ P *ᵥ a).re := by
    rw [← hm, ScoreActive_ip_comm]
  rw [h1]
  ring

/-- The covariance step of (9.35) [su:eq:matrix-source-derivative-comparison] for one real
functional `ℓ`: `Σ_k ℓ(K_k v)² ≤ ‖P v‖² Σ_j (ℓ(Π_v e_j)² + ℓ(Π_v (i e_j))²)`. -/
private lemma ScoreActive_cov_one {W : ℕ} {P : Matrix (Fin W) (Fin W) ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (v : Fin W → ℂ) (ℓ : (Fin W → ℂ) →ₗ[ℝ] ℝ) :
    ∑ k, ℓ (skewProjBasis P k *ᵥ v) ^ 2 ≤ (∑ i, ‖(P *ᵥ v) i‖ ^ 2) *
      ∑ j, (ℓ (tangProj P v (Pi.single j 1)) ^ 2 +
        ℓ (tangProj P v (Pi.single j Complex.I)) ^ 2) := by
  set w : Fin W → ℂ := fun j => (ℓ (Pi.single j 1) : ℂ) + (ℓ (Pi.single j Complex.I) : ℂ) *
    Complex.I with hw
  have hdec : ∀ u : Fin W → ℂ, u = ∑ j, ((u j).re • (Pi.single j (1 : ℂ) : Fin W → ℂ) +
      (u j).im • (Pi.single j Complex.I : Fin W → ℂ)) := fun u => by
    funext i
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_ite,
      smul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    apply Complex.ext <;> simp
  have hrep : ∀ u, ℓ u = (star w ⬝ᵥ u).re := fun u => by
    conv_lhs => rw [hdec u]
    simp only [map_sum, map_add, map_smul, smul_eq_mul]
    simp only [hw, dotProduct, Complex.re_sum, Pi.star_apply, Complex.star_def, Complex.mul_re,
      Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h1 := sum_sq_re_skewProjBasis_le hP hPP v w
  simp only [← hrep] at h1
  refine h1.trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hrep, hrep, ScoreActive_tangProj_symm hP, ScoreActive_tangProj_symm hP]
  simp only [dotProduct_single, Pi.star_apply, Complex.star_def, mul_one, Complex.conj_re,
    Complex.mul_re, Complex.conj_im, Complex.I_re, Complex.I_im]
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- (9.35) [su:eq:matrix-source-derivative-comparison], covariance part: for a real-linear `L`,
`Σ_k ‖L(K_k v)‖²_HS ≤ ‖P v‖² Σ_j (‖L(Π_v e_j)‖²_HS + ‖L(Π_v (i e_j))‖²_HS)`. -/
private lemma ScoreActive_cov {W : ℕ} {P : Matrix (Fin W) (Fin W) ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (v : Fin W → ℂ)
    (L : (Fin W → ℂ) →ₗ[ℝ] Matrix (Fin W) (Fin W) ℂ) :
    ∑ k, hsSq (L (skewProjBasis P k *ᵥ v)) ≤ (∑ i, ‖(P *ᵥ v) i‖ ^ 2) *
      ∑ j, (hsSq (L (tangProj P v (Pi.single j 1))) +
        hsSq (L (tangProj P v (Pi.single j Complex.I)))) := by
  let ℓ : Fin 2 × Fin W × Fin W → (Fin W → ℂ) →ₗ[ℝ] ℝ := fun p =>
    { toFun := fun u => reCoord (L u) p
      map_add' := fun u u' => by
        simp only [map_add, reCoord, Matrix.add_apply]; split_ifs <;> simp
      map_smul' := fun c u => by
        simp only [map_smul, reCoord, Matrix.smul_apply, RingHom.id_apply, smul_eq_mul]
        split_ifs <;> simp }
  have hℓ : ∀ p u, ℓ p u = reCoord (L u) p := fun _ _ => rfl
  simp only [ScoreActive_hsSq_reCoord, ← hℓ]
  rw [Finset.sum_comm]
  calc ∑ p, ∑ k, ℓ p (skewProjBasis P k *ᵥ v) ^ 2
      ≤ ∑ p, (∑ i, ‖(P *ᵥ v) i‖ ^ 2) * ∑ j, (ℓ p (tangProj P v (Pi.single j 1)) ^ 2 +
          ℓ p (tangProj P v (Pi.single j Complex.I)) ^ 2) :=
        Finset.sum_le_sum fun p _ => ScoreActive_cov_one hP hPP v (ℓ p)
    _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_add_distrib]

/-- `Re Tr P ≤ W` for an orthogonal projection `P`. -/
private lemma ScoreActive_trace_le {W : ℕ} {P : Matrix (Fin W) (Fin W) ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) : P.trace.re ≤ W := by
  have h : ∀ i, (P i i).re ≤ 1 := fun i =>
    (Complex.re_le_norm _).trans ((ScoreActive_entry_le P i i).trans
      (ScoreActive_norm_proj_le hP hPP))
  calc P.trace.re = ∑ i, (P i i).re := by simp [Matrix.trace, Complex.re_sum]
    _ ≤ ∑ _i : Fin W, (1 : ℝ) := Finset.sum_le_sum fun i _ => h i
    _ = W := by simp

/-- (9.33) [su:eq:commutator-basis-bound]: `Σ_k ‖[K_k, F]‖²_HS ≤ 2 W ‖F‖²_HS`. -/
private lemma ScoreActive_comm_sum_le {W : ℕ} {P F : Matrix (Fin W) (Fin W) ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (hPF : P * F * P = F) :
    ∑ k, hsSq (skewProjBasis P k * F - F * skewProjBasis P k) ≤ 2 * W * hsSq F := by
  rw [sum_hsSq_comm_skewProjBasis hP hPP hPF]
  have := ScoreActive_trace_le hP hPP
  have := ScoreActive_hsSq_nonneg F
  nlinarith [sq_nonneg ‖F.trace‖]

/-! ### The active blocks and the rotation fields -/

/-- `ω ↦ V_i(ω)` as a continuous real-linear map. -/
private def ScoreActive_VL (W q : ℕ) (i : Fin q) : Ω W q →L[ℝ] Matrix (Fin W) (Fin W) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ω => gueBlock W q ω i
      map_add' := fun ω ω' => by
        ext α β
        simp only [gueBlock, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
        split_ifs <;> push_cast <;> ring
      map_smul' := fun c ω => by
        ext α β
        simp only [gueBlock, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
          Complex.real_smul, RingHom.id_apply]
        split_ifs <;> push_cast <;> ring }

private lemma ScoreActive_gueBlock_add (W q : ℕ) (x y : Ω W q) (i : Fin q) :
    gueBlock W q (x + y) i = gueBlock W q x i + gueBlock W q y i :=
  map_add (ScoreActive_VL W q i) x y

private lemma ScoreActive_gueBlock_smul (W q : ℕ) (c : ℝ) (x : Ω W q) (i : Fin q) :
    gueBlock W q (c • x) i = c • gueBlock W q x i :=
  map_smul (ScoreActive_VL W q i) c x

/-- `hermCoord` as a continuous real-linear map. -/
private def ScoreActive_hermCoordL (W q : ℕ) :
    (Fin q → Matrix (Fin W) (Fin W) ℂ) →L[ℝ] Ω W q :=
  LinearMap.toContinuousLinearMap (IsLinearMap.mk' (hermCoord W q) (hermCoord_isLinearMap W q))

private lemma ScoreActive_hermCoord_add (W q : ℕ) (X Y : Fin q → Matrix (Fin W) (Fin W) ℂ) :
    hermCoord W q (X + Y) = hermCoord W q X + hermCoord W q Y :=
  map_add (ScoreActive_hermCoordL W q) X Y

private lemma ScoreActive_hermCoord_sub (W q : ℕ) (X Y : Fin q → Matrix (Fin W) (Fin W) ℂ) :
    hermCoord W q (X - Y) = hermCoord W q X - hermCoord W q Y :=
  map_sub (ScoreActive_hermCoordL W q) X Y

private lemma ScoreActive_hermCoord_smul (W q : ℕ) (c : ℝ) (X : Fin q → Matrix (Fin W) (Fin W) ℂ) :
    hermCoord W q (c • X) = c • hermCoord W q X :=
  map_smul (ScoreActive_hermCoordL W q) c X

/-- `gueBlock (hermCoord X) = X` for Hermitian blocks `X`. -/
private lemma ScoreActive_gueBlock_hermCoord {W q : ℕ} {X : Fin q → Matrix (Fin W) (Fin W) ℂ}
    (hX : ∀ i, (X i).IsHermitian) (i : Fin q) : gueBlock W q (hermCoord W q X) i = X i := by
  have h := gueBlock_add_smul_hermCoord hX (0 : Ω W q) 1 i
  have h0 : gueBlock W q (0 : Ω W q) i = 0 := by
    simpa using ScoreActive_gueBlock_smul W q 0 0 i
  simpa [h0] using h

/-- The blocks moved by (9.24) [su:eq:cut-generator-equivariance]: `4` and `5, …, q - 2`. -/
private def ScoreActive_S (q : ℕ) : Finset (Fin q) :=
  Finset.univ.filter fun i => (i : ℕ) = 4 ∨ (5 ≤ (i : ℕ) ∧ (i : ℕ) + 2 ≤ q)

/-- The centers `c_i`: `g² R` on block `4`, `0` otherwise. -/
private def ScoreActive_c (W q : ℕ) (g : ℝ) (R : Matrix (Fin W) (Fin W) ℂ) (i : Fin q) :
    Matrix (Fin W) (Fin W) ℂ :=
  if (i : ℕ) = 4 then ((g : ℂ) ^ 2) • R else 0

private lemma ScoreActive_c_isHermitian {W q : ℕ} {g : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    (hR : R.IsHermitian) (i : Fin q) : (ScoreActive_c W q g R i).IsHermitian := by
  unfold ScoreActive_c
  split_ifs
  · change (((g : ℂ) ^ 2) • R)ᴴ = ((g : ℂ) ^ 2) • R
    rw [Matrix.conjTranspose_smul, hR.eq]
    simp
  · exact Matrix.isHermitian_zero

private lemma ScoreActive_rot_eq (W q : ℕ) (g : ℝ) (R A : Matrix (Fin W) (Fin W) ℂ) :
    rotFrame W q g R A = fun x => hermCoord W q fun i => if i ∈ ScoreActive_S q then
      A * (gueBlock W q x i - ScoreActive_c W q g R i) -
        (gueBlock W q x i - ScoreActive_c W q g R i) * A else 0 := by
  funext x
  unfold rotFrame
  refine congrArg (hermCoord W q) (funext fun i => ?_)
  by_cases h4 : (i : ℕ) = 4
  · simp [ScoreActive_S, ScoreActive_c, h4]
  · by_cases h5 : 5 ≤ (i : ℕ) ∧ (i : ℕ) + 2 ≤ q <;> simp [ScoreActive_S, ScoreActive_c, h4, h5]

/-- The blocks of `Z_A(ω)`: `[A, V_i - c_i]` on the moved blocks. -/
private lemma ScoreActive_gueBlock_rot {W q : ℕ} {g : ℝ} {R A : Matrix (Fin W) (Fin W) ℂ}
    (hR : R.IsHermitian) (hA : Aᴴ = -A) (x : Ω W q) (i : Fin q) :
    gueBlock W q (rotFrame W q g R A x) i = if i ∈ ScoreActive_S q then
      A * (gueBlock W q x i - ScoreActive_c W q g R i) -
        (gueBlock W q x i - ScoreActive_c W q g R i) * A else 0 := by
  rw [ScoreActive_rot_eq]
  refine ScoreActive_gueBlock_hermCoord (fun j => ?_) i
  split_ifs
  · have hB := (gueBlock_isHermitian W q x j).sub (ScoreActive_c_isHermitian (g := g) hR j)
    change (A * _ - _ * A)ᴴ = A * _ - _ * A
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hA, hB.eq]
    noncomm_ring
  · exact Matrix.isHermitian_zero

/-- The linear part `A_k` of the affine field `Z_A`. -/
private def ScoreActive_ZL (W q : ℕ) (A : Matrix (Fin W) (Fin W) ℂ) : Ω W q →L[ℝ] Ω W q :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => hermCoord W q fun i => if i ∈ ScoreActive_S q then
        A * gueBlock W q x i - gueBlock W q x i * A else 0
      map_add' := fun x y => by
        rw [← ScoreActive_hermCoord_add]
        refine congrArg (hermCoord W q) (funext fun i => ?_)
        simp only [Pi.add_apply, ScoreActive_gueBlock_add]
        split_ifs
        · noncomm_ring
        · simp
      map_smul' := fun c x => by
        rw [RingHom.id_apply, ← ScoreActive_hermCoord_smul]
        refine congrArg (hermCoord W q) (funext fun i => ?_)
        simp only [Pi.smul_apply, ScoreActive_gueBlock_smul]
        split_ifs
        · rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
        · simp }

private lemma ScoreActive_ZL_apply (W q : ℕ) (A : Matrix (Fin W) (Fin W) ℂ) (x : Ω W q) :
    ScoreActive_ZL W q A x = hermCoord W q fun i => if i ∈ ScoreActive_S q then
      A * gueBlock W q x i - gueBlock W q x i * A else 0 := by
  rw [ScoreActive_ZL, LinearMap.coe_toContinuousLinearMap']
  rfl

/-- `Z_A` is affine: `Z_A(x) = A_k x + Z_A(0)`. -/
private lemma ScoreActive_rot_affine (W q : ℕ) (g : ℝ) (R A : Matrix (Fin W) (Fin W) ℂ)
    (x : Ω W q) : rotFrame W q g R A x = ScoreActive_ZL W q A x + rotFrame W q g R A 0 := by
  have h0 : ∀ i, gueBlock W q (0 : Ω W q) i = 0 := fun i => by
    simpa using ScoreActive_gueBlock_smul W q 0 0 i
  simp only [ScoreActive_rot_eq, ScoreActive_ZL_apply, h0]
  rw [← ScoreActive_hermCoord_add]
  refine congrArg (hermCoord W q) (funext fun i => ?_)
  simp only [Pi.add_apply]
  split_ifs
  · noncomm_ring
  · simp

/-- The commutator of the fields: `A_A Z_B - A_B Z_A = Z_{[A, B]}`. -/
private lemma ScoreActive_jacobi {W q : ℕ} {g : ℝ} {R A B : Matrix (Fin W) (Fin W) ℂ}
    (hR : R.IsHermitian) (hA : Aᴴ = -A) (hB : Bᴴ = -B) (x : Ω W q) :
    ScoreActive_ZL W q A (rotFrame W q g R B x) - ScoreActive_ZL W q B (rotFrame W q g R A x) =
      rotFrame W q g R (A * B - B * A) x := by
  rw [ScoreActive_ZL_apply, ScoreActive_ZL_apply, ← ScoreActive_hermCoord_sub]
  simp only [ScoreActive_gueBlock_rot hR hA, ScoreActive_gueBlock_rot hR hB]
  rw [ScoreActive_rot_eq]
  refine congrArg (hermCoord W q) (funext fun i => ?_)
  simp only [Pi.sub_apply]
  split_ifs
  · noncomm_ring
  · simp

/-- `A ↦ Z_A(x)` is real-linear. -/
private def ScoreActive_rotL (W q : ℕ) (g : ℝ) (R : Matrix (Fin W) (Fin W) ℂ) (x : Ω W q) :
    Matrix (Fin W) (Fin W) ℂ →ₗ[ℝ] Ω W q where
  toFun A := rotFrame W q g R A x
  map_add' A A' := by
    simp only [ScoreActive_rot_eq, ← ScoreActive_hermCoord_add]
    refine congrArg (hermCoord W q) (funext fun i => ?_)
    simp only [Pi.add_apply]
    split_ifs
    · noncomm_ring
    · simp
  map_smul' c A := by
    simp only [ScoreActive_rot_eq, RingHom.id_apply, ← ScoreActive_hermCoord_smul]
    refine congrArg (hermCoord W q) (funext fun i => ?_)
    simp only [Pi.smul_apply]
    split_ifs
    · rw [Matrix.smul_mul, Matrix.mul_smul, smul_sub]
    · simp

/-- The divergence `b_A = δ_G Z_A` as a linear functional of the sample. -/
private def ScoreActive_BL (W q : ℕ) (g : ℝ) (R A : Matrix (Fin W) (Fin W) ℂ) :
    Ω W q →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => -(W : ℝ) * ∑ i ∈ ScoreActive_S q, (gueBlock W q x i *
        (A * ScoreActive_c W q g R i - ScoreActive_c W q g R i * A)).trace.re
      map_add' := fun x y => by
        simp only [ScoreActive_gueBlock_add, Matrix.add_mul, Matrix.trace_add, Complex.add_re,
          Finset.sum_add_distrib]
        ring
      map_smul' := fun c x => by
        simp only [ScoreActive_gueBlock_smul, Matrix.smul_mul, Matrix.trace_smul,
          Complex.smul_re, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
        ring }

private lemma ScoreActive_BL_apply (W q : ℕ) (g : ℝ) (R A : Matrix (Fin W) (Fin W) ℂ)
    (x : Ω W q) : ScoreActive_BL W q g R A x = -(W : ℝ) * ∑ i ∈ ScoreActive_S q,
      (gueBlock W q x i * (A * ScoreActive_c W q g R i -
        ScoreActive_c W q g R i * A)).trace.re := by
  rw [ScoreActive_BL, LinearMap.coe_toContinuousLinearMap']
  rfl

/-- `δ_G Z_A = b_A` for skew-Hermitian `A`. -/
private lemma ScoreActive_div_rot {W q : ℕ} {g : ℝ} {R A : Matrix (Fin W) (Fin W) ℂ}
    (hR : R.IsHermitian) (hA : Aᴴ = -A) (x : Ω W q) :
    gaussDiv (rotFrame W q g R A) x = ScoreActive_BL W q g R A x := by
  rw [ScoreActive_rot_eq]
  exact gaussDiv_hermCoord_comm _ hA (ScoreActive_c_isHermitian hR) x

/-! ### The cut field -/

/-- The projection onto the coordinates of the active blocks `4, …, q - 2`. -/
private def ScoreActive_proj (W q : ℕ) : Ω W q →L[ℝ] Ω W q :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x p => if 4 ≤ (p.1 : ℕ) ∧ (p.1 : ℕ) + 2 ≤ q then x p else 0
      map_add' := fun x y => by
        funext p
        simp only [Pi.add_apply]
        split_ifs <;> simp
      map_smul' := fun c x => by
        funext p
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        split_ifs <;> simp }

private lemma ScoreActive_proj_apply (W q : ℕ) (x : Ω W q) (p : Fin q × Fin W × Fin W) :
    ScoreActive_proj W q x p = if 4 ≤ (p.1 : ℕ) ∧ (p.1 : ℕ) + 2 ≤ q then x p else 0 := by
  rw [ScoreActive_proj, LinearMap.coe_toContinuousLinearMap']
  rfl

/-- `|ω_p| ≤ √(2W) ‖V_i‖` for the coordinates `p = (i, α, β)` of block `i`. -/
private lemma ScoreActive_coord_le {W q : ℕ} (x : Ω W q) (p : Fin q × Fin W × Fin W) :
    ‖x p‖ ≤ Real.sqrt (2 * W) * ‖gueBlock W q x p.1‖ := by
  have hs : Real.sqrt W ≤ Real.sqrt (2 * W) :=
    Real.sqrt_le_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) W])
  obtain ⟨i, α, β⟩ := p
  rw [← congrFun (gueCoord_gueBlock W q x) (i, α, β)]
  simp only [gueCoord, Real.norm_eq_abs]
  split_ifs
  · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul hs ((Complex.abs_re_le_norm _).trans (ScoreActive_entry_le _ _ _))
      (abs_nonneg _) (Real.sqrt_nonneg _)
  · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      ((Complex.abs_re_le_norm _).trans (ScoreActive_entry_le _ _ _)) (Real.sqrt_nonneg _)
  · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      ((Complex.abs_im_le_norm _).trans (ScoreActive_entry_le _ _ _)) (Real.sqrt_nonneg _)

/-- The bounds of a `C²` function that depends only on the active blocks and vanishes unless they
are bounded: its derivatives of order `≤ 2` are bounded. -/
private lemma ScoreActive_bdd {W q : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Ω W q → E} (hf : ContDiff ℝ 2 f) (hfp : ∀ x, f (ScoreActive_proj W q x) = f x) {B : ℝ}
    (hfC : ∀ x, f x ≠ 0 → ∀ i : Fin q, 4 ≤ (i : ℕ) → (i : ℕ) + 2 ≤ q → ‖gueBlock W q x i‖ ≤ B)
    (m : ℕ) (hm : m ≤ 2) : ∃ M, ∀ x, ‖iteratedFDeriv ℝ m f x‖ ≤ M := by
  set pr := ScoreActive_proj W q
  set C : Set (Ω W q) := {x | ∀ i : Fin q, 4 ≤ (i : ℕ) → (i : ℕ) + 2 ≤ q →
    ‖gueBlock W q x i‖ ≤ B}
  have hC : IsClosed C := by
    simp only [C, Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le (continuous_norm.comp (ScoreActive_VL W q i).continuous) continuous_const
  have hpp : ∀ x, pr (pr x) = pr x := fun x => by
    funext p
    simp only [pr, ScoreActive_proj_apply]
    split_ifs <;> rfl
  have hCr : ∀ x ∈ C, ‖pr x‖ ≤ Real.sqrt (2 * W) * |B| := fun x hx => by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun p => ?_
    simp only [pr, ScoreActive_proj_apply]
    split_ifs with h
    · exact (ScoreActive_coord_le x p).trans (mul_le_mul_of_nonneg_left
        ((hx p.1 h.1 h.2).trans (le_abs_self B)) (Real.sqrt_nonneg _))
    · simp only [norm_zero]; positivity
  have hcomp : f = f ∘ pr := funext fun x => (hfp x).symm
  have hcont : Continuous (iteratedFDeriv ℝ m f) :=
    hf.continuous_iteratedFDeriv (by exact_mod_cast hm)
  obtain ⟨M0, hM0⟩ := (isCompact_closedBall (0 : Ω W q) (Real.sqrt (2 * W) * |B|)
    ).exists_bound_of_continuousOn hcont.continuousOn
  have hts : tsupport f ⊆ C := closure_minimal (fun x hx => hfC x hx) hC
  refine ⟨max M0 0 * ‖pr‖ ^ m, fun x => ?_⟩
  have h1 : iteratedFDeriv ℝ m f x =
      (iteratedFDeriv ℝ m f (pr x)).compContinuousLinearMap fun _ => pr := by
    conv_lhs => rw [hcomp]
    exact pr.iteratedFDeriv_comp_right hf x (by exact_mod_cast hm)
  rw [h1]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  gcongr
  by_cases h0 : iteratedFDeriv ℝ m f (pr x) = 0
  · rw [h0, norm_zero]; exact le_max_right _ _
  · have hs : pr x ∈ tsupport f := support_iteratedFDeriv_subset m h0
    have hr : ‖pr x‖ ≤ Real.sqrt (2 * W) * |B| := by rw [← hpp x]; exact hCr _ (hts hs)
    exact (hM0 _ (mem_closedBall_zero_iff.2 hr)).trans (le_max_left _ _)

/-- `χ̂ K̂` is `C²` near every `(ω, w)` with `w ≠ 0`: near the support of `χ̂` it is a product of
`C²` maps, away from it it vanishes. -/
private lemma ScoreActive_jointAt {W q : ℕ} {g E : ℝ} {P R : Matrix (Fin W) (Fin W) ℂ}
    {Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ} {χh : Ω W q → (Fin W → ℂ) → ℝ}
    (hF : GenFamily W q g E P R Kh χh) (ω : Ω W q) {w : Fin W → ℂ} (hw : w ≠ 0) :
    ContDiffAt ℝ 2 (fun p : Ω W q × (Fin W → ℂ) => χh p.1 p.2 • Kh p.1 p.2) (ω, w) := by
  obtain ⟨-, -, -, -, hχ, ⟨G, hGo, hK, hG⟩, -⟩ := hF
  by_cases hp : (ω, w) ∈ tsupport (fun p : Ω W q × (Fin W → ℂ) => χh p.1 p.2)
  · have h1 : ContDiffAt ℝ 2 (fun p : Ω W q × (Fin W → ℂ) => Kh p.1 p.2) (ω, w) :=
      hK.contDiffAt (hGo.mem_nhds (hG _ hp hw).1)
    have hopen : IsOpen {p : Ω W q × (Fin W → ℂ) | p.2 ≠ 0} :=
      isOpen_ne_fun continuous_snd continuous_const
    exact (hχ.contDiffAt (hopen.mem_nhds hw)).smul h1
  · rw [notMem_tsupport_iff_eventuallyEq] at hp
    refine (contDiffAt_const (c := (0 : Matrix (Fin W) (Fin W) ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [hp] with p hp'
    have : χh p.1 p.2 = 0 := hp'
    simp [this]

/-! ### The pointwise estimate -/

/-- `B ↦ ⟨A, B⟩` as a continuous real-linear map. -/
private def ScoreActive_hsInnerL {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin W) (Fin W) ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun B => hsInner A B
      map_add' := fun B C => by
        simp only [hsInner, Matrix.add_apply, mul_add, Complex.add_re, Finset.sum_add_distrib]
      map_smul' := fun c B => by
        simp only [hsInner, Matrix.smul_apply, Complex.real_smul, RingHom.id_apply, smul_eq_mul,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [mul_left_comm, Complex.re_ofReal_mul] }

private lemma ScoreActive_hsInnerL_apply {W : ℕ} (A B : Matrix (Fin W) (Fin W) ℂ) :
    ScoreActive_hsInnerL A B = hsInner A B := by
  rw [ScoreActive_hsInnerL, LinearMap.coe_toContinuousLinearMap']
  rfl

/-- `Re Tr((Σ_l a_l X_l)(Σ_j a_j Y_j)) = Σ_{l,j} a_l a_j Re Tr(X_l Y_j)`. -/
private lemma ScoreActive_bilin {W : ℕ} {κ : Type*} [Fintype κ] (a : κ → ℝ)
    (X Y : κ → Matrix (Fin W) (Fin W) ℂ) :
    ((∑ l, a l • X l) * ∑ j, a j • Y j).trace.re = ∑ l, ∑ j, a l * a j * (X l * Y j).trace.re := by
  rw [Finset.sum_mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul, Complex.smul_re,
    smul_eq_mul]

/-- `Σ_{l,j} u_{lj} u_{jl} ≤ Σ_{l,j} u_{lj}²`. -/
private lemma ScoreActive_sum_mul_le {κ : Type*} [Fintype κ] (u : κ → κ → ℝ) :
    ∑ l, ∑ j, u l j * u j l ≤ ∑ l, ∑ j, u l j ^ 2 := by
  have h1 : ∑ l, ∑ j, u j l ^ 2 = ∑ l, ∑ j, u l j ^ 2 := Finset.sum_comm
  have h2 : 2 * ∑ l, ∑ j, u l j * u j l ≤ ∑ l, ∑ j, (u l j ^ 2 + u j l ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by nlinarith [sq_nonneg (u l j - u j l)]
  have h3 : ∑ l, ∑ j, (u l j ^ 2 + u j l ^ 2) = 2 * ∑ l, ∑ j, u l j ^ 2 := by
    simp only [Finset.sum_add_distrib, h1]; ring
  linarith

/-- `Σ_{j,m} u_{jm} w_{jm} ≤ ½ Σ_m (Σ_j u_{jm}² + Σ_j w_{jm}²)`. -/
private lemma ScoreActive_sum_mul_le' {κ : Type*} [Fintype κ] (u w : κ → κ → ℝ) :
    ∑ j, ∑ m, u j m * w j m ≤ (∑ m, ∑ j, u j m ^ 2 + ∑ m, ∑ j, w j m ^ 2) / 2 := by
  rw [Finset.sum_comm (f := fun m j => u j m ^ 2), Finset.sum_comm (f := fun m j => w j m ^ 2),
    ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  exact Finset.sum_le_sum fun m _ => by nlinarith [sq_nonneg (u j m - w j m)]

private lemma ScoreActive_rotL_apply (W q : ℕ) (g : ℝ) (R : Matrix (Fin W) (Fin W) ℂ)
    (x : Ω W q) (A : Matrix (Fin W) (Fin W) ℂ) :
    ScoreActive_rotL W q g R x A = rotFrame W q g R A x := rfl

/-- `K_k = P (i H_k) P` is skew-Hermitian and `P K_k P = K_k`. -/
private lemma ScoreActive_skew {W : ℕ} {P : Matrix (Fin W) (Fin W) ℂ} (hP : P.IsHermitian)
    (hPP : P * P = P) (k : Fin W × Fin W) :
    (skewProjBasis P k)ᴴ = -skewProjBasis P k ∧ P * skewProjBasis P k * P = skewProjBasis P k := by
  refine ⟨?_, ?_⟩
  · simp only [skewProjBasis, Matrix.conjTranspose_mul, Matrix.conjTranspose_smul,
      hP.eq, (hermBasis_isHermitian W k).eq, Complex.star_def, Complex.conj_I, neg_smul,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  · simp only [skewProjBasis, ← Matrix.mul_assoc, hPP]
    rw [Matrix.mul_assoc (P * _), hPP]

/-- The pointwise form of (9.32) [su:eq:active-divergence-decomposition]–(9.34)
[su:eq:active-matrix-derivative-bound]: when `D(Z_{K_m})(χ K) = [K_m, F] - L(K_m v)` (the chain
rule), the three terms of (9.32) [su:eq:active-divergence-decomposition] are at most
`3 ‖P v‖² Σ_j (‖L(Π_v e_j)‖² + ‖L(Π_v i e_j)‖²)
+ 7 W ‖F‖² + 4 W M₀ (‖V_5‖ + M₀) ‖F‖²`. -/
private lemma ScoreActive_pointwise {W q : ℕ} {g M₀ : ℝ} {R P : Matrix (Fin W) (Fin W) ℂ}
    {v : Fin W → ℂ} (hR : R.IsHermitian) (hP : P.IsHermitian) (hPP : P * P = P)
    (hPR : P * R = R * P) (hM : g ^ 2 * ‖P * R * P‖ ≤ M₀) (x : Ω W q)
    {F : Matrix (Fin W) (Fin W) ℂ} (hF : Fᴴ = -F) (hPF : P * F * P = F)
    (D : Ω W q →L[ℝ] Matrix (Fin W) (Fin W) ℂ) (L : (Fin W → ℂ) →L[ℝ] Matrix (Fin W) (Fin W) ℂ)
    (hD : ∀ A : Matrix (Fin W) (Fin W) ℂ, Aᴴ = -A → P * A * P = A →
      D (rotFrame W q g R A x) = A * F - F * A - L (A *ᵥ v))
    (i4 : Fin q) (hi4 : (i4 : ℕ) = 4) (e K : Fin W × Fin W → Matrix (Fin W) (Fin W) ℂ)
    (he : e = fun k => Complex.I • hermBasis W k) (hKd : K = skewProjBasis P) :
    ∑ l, ∑ j, (hsInner (e l) (D (rotFrame W q g R (K j) x)) *
        hsInner (e j) (D (rotFrame W q g R (K l) x)) +
      hsInner (e l) F * hsInner (e j) F * ScoreActive_BL W q g R (K j) (rotFrame W q g R (K l) x) +
      hsInner (e l) F * hsInner (e j) (D (rotFrame W q g R (K l * K j - K j * K l) x))) ≤
      3 * ((∑ i, ‖(P *ᵥ v) i‖ ^ 2) * ∑ j, (hsSq (L (tangProj P v (Pi.single j 1))) +
        hsSq (L (tangProj P v (Pi.single j Complex.I))))) + 7 * W * hsSq F +
      4 * W * M₀ * (‖gueBlock W q x i4‖ + M₀) * hsSq F := by
  have hPF' : P * F = F := by rw [← hPF, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP]
  have hFP' : F * P = F := by
    calc F * P = P * F * P * P := by rw [hPF]
      _ = F := by rw [Matrix.mul_assoc, hPP, hPF]
  have hK : ∀ k, (K k)ᴴ = -K k ∧ P * K k * P = K k := fun k => by
    subst hKd; exact ScoreActive_skew hP hPP k
  have hKP : ∀ k, K k * P = K k := fun k => by
    rw [← (hK k).2, Matrix.mul_assoc, hPP]
  have hPK : ∀ k, P * K k = K k := fun k => by
    rw [← (hK k).2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP]
  have hframe : F = ∑ l, hsInner (e l) F • K l := by
    subst he hKd; exact ScoreActive_frame hF hPF
  have hbes : ∀ M, ∑ k, hsInner (e k) M ^ 2 ≤ hsSq M := fun M => by
    subst he; exact ScoreActive_bessel M
  have hf0 := ScoreActive_hsSq_nonneg F
  have hM0 : 0 ≤ M₀ := le_trans (by positivity) hM
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  -- the source sum `S = Σ_m ‖D_m‖²`, (9.35) [su:eq:matrix-source-derivative-comparison]
  have hcomm : ∑ m, hsSq (K m * F - F * K m) ≤ 2 * W * hsSq F := by
    subst hKd; exact ScoreActive_comm_sum_le hP hPP hPF
  have hS : ∑ m, hsSq (D (rotFrame W q g R (K m) x)) ≤ 4 * W * hsSq F +
      2 * ((∑ i, ‖(P *ᵥ v) i‖ ^ 2) * ∑ j, (hsSq (L (tangProj P v (Pi.single j 1))) +
        hsSq (L (tangProj P v (Pi.single j Complex.I))))) := by
    have hcov := ScoreActive_cov hP hPP v L.toLinearMap
    simp only [ContinuousLinearMap.coe_coe, ← hKd] at hcov
    calc ∑ m, hsSq (D (rotFrame W q g R (K m) x))
        ≤ ∑ m, (2 * hsSq (K m * F - F * K m) + 2 * hsSq (L (K m *ᵥ v))) :=
          Finset.sum_le_sum fun m _ => by
            rw [hD _ (hK m).1 (hK m).2]; exact ScoreActive_hsSq_sub_le _ _
      _ ≤ _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          linarith
  -- the first term
  have hT1 : ∑ l, ∑ j, hsInner (e l) (D (rotFrame W q g R (K j) x)) *
      hsInner (e j) (D (rotFrame W q g R (K l) x)) ≤
        ∑ m, hsSq (D (rotFrame W q g R (K m) x)) := by
    refine (ScoreActive_sum_mul_le fun l j => hsInner (e l) (D (rotFrame W q g R (K j) x))).trans ?_
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun j _ => hbes _
  -- the second term
  have hc4 : ∀ i : Fin q, i ≠ i4 → ScoreActive_c W q g R i = 0 := fun i hi => by
    have : (i : ℕ) ≠ 4 := fun h => hi (Fin.ext (h.trans hi4.symm))
    simp [ScoreActive_c, this]
  have hi4S : i4 ∈ ScoreActive_S q := by simp [ScoreActive_S, hi4]
  have hc4e : ScoreActive_c W q g R i4 = ((g : ℂ) ^ 2) • R := by simp [ScoreActive_c, hi4]
  set c4 := ScoreActive_c W q g R i4 with hc4def
  set V := gueBlock W q x i4 with hV
  have hT2eq : ∑ l, ∑ j, hsInner (e l) F * hsInner (e j) F *
      ScoreActive_BL W q g R (K j) (rotFrame W q g R (K l) x) =
      -(W : ℝ) * ((F * (V - c4) - (V - c4) * F) * (F * c4 - c4 * F)).trace.re := by
    have h1 : ∀ l j, ScoreActive_BL W q g R (K j) (rotFrame W q g R (K l) x) =
        -(W : ℝ) * ((K l * (V - c4) - (V - c4) * K l) * (K j * c4 - c4 * K j)).trace.re := by
      intro l j
      rw [ScoreActive_BL_apply, Finset.sum_eq_single_of_mem i4 hi4S fun i _ hi => by
        simp [hc4 i hi], ScoreActive_gueBlock_rot hR (hK l).1]
      simp only [hi4S, ↓reduceIte]
      rfl
    have h2 : ∀ l j, hsInner (e l) F * hsInner (e j) F * (-(W : ℝ) *
        ((K l * (V - c4) - (V - c4) * K l) * (K j * c4 - c4 * K j)).trace.re) =
        -(W : ℝ) * (hsInner (e l) F * hsInner (e j) F *
          ((K l * (V - c4) - (V - c4) * K l) * (K j * c4 - c4 * K j)).trace.re) := by
      intros; ring
    simp only [h1, h2, ← Finset.mul_sum]
    rw [← ScoreActive_bilin, ← ScoreActive_sum_comm, ← ScoreActive_sum_comm, ← hframe]
  have hPc : P * c4 = c4 * P := by rw [hc4e, Matrix.mul_smul, Matrix.smul_mul, hPR]
  have hY : F * c4 - c4 * F = F * (P * c4 * P) - (P * c4 * P) * F := by
    have e1 : F * (P * c4 * P) = F * c4 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hFP', Matrix.mul_assoc, ← hPc,
        ← Matrix.mul_assoc, hFP']
    have e2 : P * c4 * P * F = c4 * F := by
      rw [Matrix.mul_assoc, hPF', hPc, Matrix.mul_assoc, hPF']
    rw [e1, e2]
  have hnc : ‖P * c4 * P‖ ≤ M₀ := by
    rw [hc4e, Matrix.mul_smul, Matrix.smul_mul, norm_smul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    exact hM
  have hYs : hsSq (F * c4 - c4 * F) ≤ 4 * M₀ ^ 2 * hsSq F := by
    rw [hY]
    refine (ScoreActive_hsSq_comm_le F _).trans ?_
    gcongr
  have hXs := ScoreActive_hsSq_comm_le F V
  have hT2 : -(W : ℝ) * ((F * (V - c4) - (V - c4) * F) * (F * c4 - c4 * F)).trace.re ≤
      4 * W * M₀ * (‖V‖ + M₀) * hsSq F := by
    have hX : F * (V - c4) - (V - c4) * F = (F * V - V * F) - (F * c4 - c4 * F) := by
      noncomm_ring
    rw [hX, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
    have ha : |((F * V - V * F) * (F * c4 - c4 * F)).trace.re| ≤ 4 * ‖V‖ * M₀ * hsSq F := by
      refine abs_le_of_sq_le_sq ((ScoreActive_re_trace_sq_le _ _).trans ?_) (by positivity)
      calc hsSq (F * V - V * F) * hsSq (F * c4 - c4 * F)
          ≤ (4 * ‖V‖ ^ 2 * hsSq F) * (4 * M₀ ^ 2 * hsSq F) :=
            mul_le_mul hXs hYs (ScoreActive_hsSq_nonneg _) (by positivity)
        _ = (4 * ‖V‖ * M₀ * hsSq F) ^ 2 := by ring
    have hb : |((F * c4 - c4 * F) * (F * c4 - c4 * F)).trace.re| ≤ 4 * M₀ ^ 2 * hsSq F := by
      refine (abs_le_of_sq_le_sq ((ScoreActive_re_trace_sq_le _ _).trans ?_)
        (ScoreActive_hsSq_nonneg _)).trans hYs
      rw [sq]
    have ha' := abs_le.mp ha
    have hb' := abs_le.mp hb
    nlinarith
  -- the third term
  have hΦ : ∀ j (c : Fin W × Fin W → ℝ) (M : Fin W × Fin W → Matrix (Fin W) (Fin W) ℂ),
      ∑ l, c l * hsInner (e j) (D (rotFrame W q g R (M l) x)) =
        hsInner (e j) (D (rotFrame W q g R (∑ l, c l • M l) x)) := by
    intro j c M
    have h := map_sum ((ScoreActive_hsInnerL (e j)).toLinearMap ∘ₗ D.toLinearMap ∘ₗ
      ScoreActive_rotL W q g R x) (fun l => c l • M l) Finset.univ
    simp only [map_smul, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      ScoreActive_hsInnerL_apply, ScoreActive_rotL_apply, smul_eq_mul] at h
    exact h.symm
  have hT3 : ∑ l, ∑ j, hsInner (e l) F *
      hsInner (e j) (D (rotFrame W q g R (K l * K j - K j * K l) x)) ≤
        (∑ m, hsSq (K m * F - F * K m) + ∑ m, hsSq (D (rotFrame W q g R (K m) x))) / 2 := by
    have hj : ∀ j, ∑ l, hsInner (e l) F *
        hsInner (e j) (D (rotFrame W q g R (K l * K j - K j * K l) x)) =
        ∑ m, hsInner (e j) (K m * F - F * K m) * hsInner (e j) (D (rotFrame W q g R (K m) x)) := by
      intro j
      rw [hΦ, ← ScoreActive_sum_comm, ← hframe]
      have hsk : (F * K j - K j * F)ᴴ = -(F * K j - K j * F) := by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hF,
          (hK j).1]
        noncomm_ring
      have hcp : P * (F * K j - K j * F) * P = F * K j - K j * F := by
        calc P * (F * K j - K j * F) * P = (P * F) * (K j * P) - (P * K j) * (F * P) := by
              noncomm_ring
          _ = F * K j - K j * F := by rw [hPF', hKP, hPK, hFP']
      have hfr : F * K j - K j * F = ∑ m, hsInner (e m) (F * K j - K j * F) • K m := by
        subst he hKd; exact ScoreActive_frame hsk hcp
      rw [hfr, ← hΦ]
      refine Finset.sum_congr rfl fun m _ => ?_
      subst he hKd
      rw [ScoreActive_frame_swap hPF' hFP']
    rw [Finset.sum_comm, Finset.sum_congr rfl fun j _ => hj j]
    refine (ScoreActive_sum_mul_le' (fun j m => hsInner (e j) (K m * F - F * K m))
      (fun j m => hsInner (e j) (D (rotFrame W q g R (K m) x)))).trans ?_
    gcongr with m
    · exact hbes _
    · exact hbes _
  simp only [Finset.sum_add_distrib] at hS ⊢
  rw [hT2eq]
  linarith

/-! ### The Gaussian tail -/

/-- The tail used for `𝔼[‖V_5‖ ‖χ K‖²]`: with `ε = e^{-W/4}`,
`𝔼[ε ‖V_5‖² + ε⁻¹ 1{‖V_5‖ > 16}] ≤ (8 + e^{16}) e^{-W/8}`, from `𝔼‖V_5‖² ≤ W` and the GUE norm
tail `P(‖V_5‖ > 16) ≤ e^{-W/2}` (`W ≥ 32`). -/
private lemma ScoreActive_tail (W q : ℕ) (i4 : Fin q) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-(W : ℝ) / 4) * ‖gueBlock W q x i4‖ ^ 2 +
      Real.exp ((W : ℝ) / 4) * {x : Ω W q | 16 < ‖gueBlock W q x i4‖}.indicator (fun _ => 1) x)
      ∂(μ W q) ≤ ENNReal.ofReal ((8 + Real.exp 16) * Real.exp (-(1 / 8) * W)) := by
  set A4 := {x : Ω W q | 16 < ‖gueBlock W q x i4‖} with hA4
  have hVc : Continuous fun x : Ω W q => gueBlock W q x i4 := (ScoreActive_VL W q i4).continuous
  have hA : MeasurableSet A4 := (isOpen_lt continuous_const hVc.norm).measurableSet
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have e1 : ∀ x, ENNReal.ofReal (Real.exp (-(W : ℝ) / 4) * ‖gueBlock W q x i4‖ ^ 2 +
      Real.exp ((W : ℝ) / 4) * A4.indicator (fun _ => 1) x) =
      ENNReal.ofReal (Real.exp (-(W : ℝ) / 4)) * ‖gueBlock W q x i4‖ₑ ^ 2 +
        A4.indicator (fun _ => ENNReal.ofReal (Real.exp ((W : ℝ) / 4))) x := fun x => by
    rw [ENNReal.ofReal_add (by positivity) (by
      by_cases hx : x ∈ A4 <;> simp [hx, (Real.exp_pos _).le]), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    by_cases hx : x ∈ A4 <;> simp [hx]
  simp only [e1]
  rw [lintegral_add_right _ (measurable_const.indicator hA), lintegral_const_mul' _ _
    ENNReal.ofReal_ne_top, lintegral_indicator_const hA]
  have hV2 : ∫⁻ x, ‖gueBlock W q x i4‖ₑ ^ 2 ∂(μ W q) ≤ ENNReal.ofReal W := by
    have h := lintegral_norm_gueBlock_rpow_le W q i4 two_pos le_rfl
    simp only [ENNReal.rpow_two, div_self (two_ne_zero' ℝ), Real.rpow_one] at h
    exact h
  have hmA : (μ W q) A4 ≤ ENNReal.ofReal (Real.exp 16 * Real.exp (-(W : ℝ) / 2)) := by
    by_cases h32 : 32 ≤ W
    · exact (gueBlock_norm_tail h32 i4).trans (ENNReal.ofReal_le_ofReal
        (le_mul_of_one_le_left (Real.exp_pos _).le (Real.one_le_exp (by norm_num))))
    · refine prob_le_one.trans ?_
      rw [← ENNReal.ofReal_one, ← Real.exp_add]
      refine ENNReal.ofReal_le_ofReal (Real.one_le_exp ?_)
      have : (W : ℝ) < 32 := by exact_mod_cast not_le.1 h32
      linarith
  have h1 : Real.exp ((W : ℝ) / 4) * (Real.exp 16 * Real.exp (-(W : ℝ) / 2)) =
      Real.exp 16 * Real.exp (-(W : ℝ) / 4) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (-(W : ℝ) / 4) ≤ Real.exp (-(1 / 8) * W) := Real.exp_le_exp.2 (by linarith)
  have h3 : Real.exp (-(W : ℝ) / 4) * W ≤ 8 * Real.exp (-(1 / 8) * W) := by
    have h4 := Real.add_one_le_exp ((W : ℝ) / 8)
    have e : Real.exp (-(W : ℝ) / 4) * Real.exp ((W : ℝ) / 8) = Real.exp (-(1 / 8) * W) := by
      rw [← Real.exp_add]; congr 1; ring
    nlinarith [Real.exp_pos (-(W : ℝ) / 4)]
  calc ENNReal.ofReal (Real.exp (-(W : ℝ) / 4)) * ∫⁻ x, ‖gueBlock W q x i4‖ₑ ^ 2 ∂(μ W q) +
        ENNReal.ofReal (Real.exp ((W : ℝ) / 4)) * (μ W q) A4
      ≤ ENNReal.ofReal (Real.exp (-(W : ℝ) / 4)) * ENNReal.ofReal W +
        ENNReal.ofReal (Real.exp ((W : ℝ) / 4)) *
          ENNReal.ofReal (Real.exp 16 * Real.exp (-(W : ℝ) / 2)) := by gcongr
    _ = ENNReal.ofReal (Real.exp (-(W : ℝ) / 4) * W +
          Real.exp 16 * Real.exp (-(W : ℝ) / 4)) := by
        rw [← h1, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [Real.exp_pos 16])

/-- `‖V‖ f ≤ 16 f + (K/2)(ε ‖V‖² + ε⁻¹ 1{‖V‖ > 16})` for `0 ≤ f ≤ K`, `ε = e^{-W/4}`. -/
private lemma ScoreActive_tail_pt (W : ℕ) {V f K : ℝ} (hV : 0 ≤ V) (hf0 : 0 ≤ f) (hfK : f ≤ K)
    (I : ℝ) (hI : I = if 16 < V then 1 else 0) :
    V * f ≤ 16 * f + K / 2 * (Real.exp (-(W : ℝ) / 4) * V ^ 2 + Real.exp ((W : ℝ) / 4) * I) := by
  have hε : Real.exp (-(W : ℝ) / 4) * Real.exp ((W : ℝ) / 4) = 1 := by
    rw [← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero]
  have hK : 0 ≤ K := hf0.trans hfK
  have hε0 := Real.exp_pos (-(W : ℝ) / 4)
  have hε1 := Real.exp_pos ((W : ℝ) / 4)
  by_cases h : 16 < V
  · simp only [hI, h, ↓reduceIte, mul_one]
    have hamgm : 2 * V ≤ Real.exp (-(W : ℝ) / 4) * V ^ 2 + Real.exp ((W : ℝ) / 4) := by
      nlinarith [sq_nonneg (Real.exp (-(W : ℝ) / 4) * V - 1)]
    nlinarith [mul_le_mul_of_nonneg_left hfK hV]
  · simp only [hI, h, ↓reduceIte, mul_zero, add_zero]
    have : V * f ≤ 16 * f := mul_le_mul_of_nonneg_right (not_lt.1 h) hf0
    have : 0 ≤ K / 2 * (Real.exp (-(W : ℝ) / 4) * V ^ 2) :=
      mul_nonneg (div_nonneg hK two_pos.le) (mul_nonneg hε0.le (sq_nonneg V))
    linarith

/-- (9.34) [su:eq:active-matrix-derivative-bound] with (9.35)
[su:eq:matrix-source-derivative-comparison]: the second moment of the active part of
`δ_G(χ X)` at a fixed preparation. -/
theorem active_div_sq_le (CK : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (W q : ℕ) (g E M₀ : ℝ) (R P : Matrix (Fin W) (Fin W) ℂ)
      (v : Fin W → ℂ) (Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ)
      (χh : Ω W q → (Fin W → ℂ) → ℝ), ScoreData W q g E M₀ CK R P v Kh χh →
      ∫⁻ ω, ‖gaussDiv (fun η => χh η v • hermCoord W q fun i =>
          if (i : ℕ) + 1 < q then smallField W g E q R v (Kh η v) η i else 0) ω‖ₑ ^ 2
          ∂(μ W q) ≤
        ENNReal.ofReal C * ∫⁻ ω, ENNReal.ofReal
            (srcEnergy P v (fun w => χh ω w • Kh ω w)) ∂(μ W q) +
          ENNReal.ofReal (C * W * (1 + M₀ ^ 2)) *
            ∫⁻ ω, ENNReal.ofReal (hsSq (χh ω v • Kh ω v)) ∂(μ W q) +
          ENNReal.ofReal (C * W * M₀ * Real.exp (-c * W)) := by
  refine ⟨39 + 2 * (8 + Real.exp 16) * max CK 0, 1 / 8, by positivity, by norm_num, ?_⟩
  intro W q g E M₀ R P v Kh χh hD
  have hD0 := hD
  obtain ⟨-, hq, -, -, hM0, hR, hv, hP, hPP, hPR, hF, hK, hM⟩ := hD
  set C := 39 + 2 * (8 + Real.exp 16) * max CK 0 with hC
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have hCK : 0 ≤ max CK 0 := le_max_right _ _
  -- the cut field `F = χ̂ K̂(·, v)`
  set Fm : Ω W q → Matrix (Fin W) (Fin W) ℂ := fun η => χh η v • Kh η v with hFm
  have hFs : ∀ η, (Fm η)ᴴ = -(Fm η) ∧ P * Fm η * P = Fm η := fun η => by
    by_cases hχ : χh η v = 0
    · simp [hFm, hχ]
    · obtain ⟨hk1, hk2, -, -⟩ := hK η hχ
      refine ⟨?_, ?_⟩
      · rw [hFm, Matrix.conjTranspose_smul, hk1]; simp
      · rw [hFm, Matrix.mul_smul, Matrix.smul_mul, hk2]
  have hf : ∀ η, hsSq (Fm η) ≤ max CK 0 := fun η => by
    by_cases hχ : χh η v = 0
    · simp [hFm, hχ, hsSq]
    · obtain ⟨-, -, -, hk⟩ := hK η hχ
      have h01 := hF.2.1 η v
      have hk0 := ScoreActive_hsSq_nonneg (Kh η v)
      rw [hFm, ScoreActive_hsSq_real_smul]
      calc χh η v ^ 2 * hsSq (Kh η v) ≤ 1 * hsSq (Kh η v) :=
            mul_le_mul_of_nonneg_right (by nlinarith [h01.1, h01.2]) hk0
        _ ≤ max CK 0 := by linarith [le_max_left CK 0]
  have hFc : ContDiff ℝ 2 Fm := contDiff_iff_contDiffAt.2 fun η =>
    (ScoreActive_jointAt hF η hv).comp η (contDiffAt_id.prodMk contDiffAt_const)
  have hFd : ∀ η, DifferentiableAt ℝ Fm η := fun η => hFc.differentiable (by norm_num) η
  have hJd : ∀ η, DifferentiableAt ℝ (fun w => χh η w • Kh η w) v := fun η =>
    ((ScoreActive_jointAt hF η hv).differentiableAt (by norm_num)).comp v
      ((differentiableAt_const η).prodMk differentiableAt_id)
  have hFproj : ∀ x, Fm (ScoreActive_proj W q x) = Fm x := fun x => by
    have h := hF.1 (ScoreActive_proj W q x) x (fun i h1 h2 => by
      ext α β; simp [gueBlock, ScoreActive_proj_apply, h1, h2]) v
    simp only [hFm, h.1, h.2]
  obtain ⟨B, hB⟩ := hF.2.2.2.2.2.2
  -- the frame `K_k = P (i H_k) P` and the coefficients `a_k = ⟨i H_k, F⟩`
  have hKs : ∀ k, (skewProjBasis P k)ᴴ = -skewProjBasis P k := fun k =>
    (ScoreActive_skew hP hPP k).1
  have haL : ∀ k, (fun x => hsInner (Complex.I • hermBasis W k) (Fm x)) =
      ⇑(ScoreActive_hsInnerL (Complex.I • hermBasis W k)) ∘ Fm := fun k =>
    funext fun x => (ScoreActive_hsInnerL_apply _ _).symm
  have ha2 : ∀ k, ContDiff ℝ 2 (fun x => hsInner (Complex.I • hermBasis W k) (Fm x)) :=
    fun k => by rw [haL]; exact (ScoreActive_hsInnerL _).contDiff.comp hFc
  have hda : ∀ k x h, fderiv ℝ (fun x => hsInner (Complex.I • hermBasis W k) (Fm x)) x h =
      hsInner (Complex.I • hermBasis W k) (fderiv ℝ Fm x h) := fun k x h => by
    rw [haL, ((ScoreActive_hsInnerL _).hasFDerivAt.comp x (hFd x).hasFDerivAt).fderiv,
      ContinuousLinearMap.comp_apply, ScoreActive_hsInnerL_apply]
  have hbd : ∀ k, ∃ M, ∀ x, |hsInner (Complex.I • hermBasis W k) (Fm x)| ≤ M ∧
      ‖fderiv ℝ (fun x => hsInner (Complex.I • hermBasis W k) (Fm x)) x‖ ≤ M ∧
      ‖fderiv ℝ (fderiv ℝ (fun x => hsInner (Complex.I • hermBasis W k) (Fm x))) x‖ ≤ M :=
    fun k => by
    have hp : ∀ x, hsInner (Complex.I • hermBasis W k) (Fm (ScoreActive_proj W q x)) =
        hsInner (Complex.I • hermBasis W k) (Fm x) := fun x => by rw [hFproj]
    have hs : ∀ x, hsInner (Complex.I • hermBasis W k) (Fm x) ≠ 0 → ∀ i : Fin q,
        4 ≤ (i : ℕ) → (i : ℕ) + 2 ≤ q → ‖gueBlock W q x i‖ ≤ B := fun x hx =>
      hB x v fun h => hx (by simp [hFm, h, hsInner])
    obtain ⟨M0, h0⟩ := ScoreActive_bdd (ha2 k) hp hs 0 (by norm_num)
    obtain ⟨M1, h1⟩ := ScoreActive_bdd (ha2 k) hp hs 1 (by norm_num)
    obtain ⟨M2, h2⟩ := ScoreActive_bdd (ha2 k) hp hs 2 (by norm_num)
    refine ⟨max M0 (max M1 M2), fun x => ⟨?_, ?_, ?_⟩⟩
    · have := h0 x
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)
    · have := h1 x
      rw [norm_iteratedFDeriv_one] at this
      exact this.trans ((le_max_left _ _).trans (le_max_right _ _))
    · have e2 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ)
        (f := fun x => hsInner (Complex.I • hermBasis W k) (Fm x)) (x := x) (n := 1)
      rw [norm_iteratedFDeriv_one] at e2
      rw [e2]
      exact (h2 x).trans ((le_max_right _ _).trans (le_max_right _ _))
  choose Mk hMk using hbd
  have hMb : ∀ k x, |hsInner (Complex.I • hermBasis W k) (Fm x)| ≤ ∑ k', |Mk k'| ∧
      ‖fderiv ℝ (fun x => hsInner (Complex.I • hermBasis W k) (Fm x)) x‖ ≤ ∑ k', |Mk k'| ∧
      ‖fderiv ℝ (fderiv ℝ (fun x => hsInner (Complex.I • hermBasis W k) (Fm x))) x‖ ≤
        ∑ k', |Mk k'| := fun k x => by
    have hle : Mk k ≤ ∑ k', |Mk k'| := (le_abs_self _).trans (Finset.single_le_sum
      (f := fun k' => |Mk k'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k))
    exact ⟨(hMk k x).1.trans hle, (hMk k x).2.1.trans hle, (hMk k x).2.2.trans hle⟩
  -- the Stein identity (9.32) [su:eq:active-divergence-decomposition]
  have hbdiv : ∀ k x, gaussDiv (fun y => ScoreActive_ZL W q (skewProjBasis P k) y +
      rotFrame W q g R (skewProjBasis P k) 0) x = ScoreActive_BL W q g R (skewProjBasis P k) x :=
    fun k x => by
    rw [show (fun y => ScoreActive_ZL W q (skewProjBasis P k) y +
        rotFrame W q g R (skewProjBasis P k) 0) = rotFrame W q g R (skewProjBasis P k) from
      funext fun y => (ScoreActive_rot_affine W q g R _ y).symm]
    exact ScoreActive_div_rot hR (hKs k) x
  have hst := ScoreActive_stein (fun k x => hsInner (Complex.I • hermBasis W k) (Fm x))
    (fun k => ScoreActive_ZL W q (skewProjBasis P k))
    (fun k => rotFrame W q g R (skewProjBasis P k) 0)
    (fun k => ScoreActive_BL W q g R (skewProjBasis P k)) ha2 hMb hbdiv
  simp only [← ScoreActive_rot_affine] at hst
  -- the pointwise bound
  set i4 : Fin q := ⟨4, by omega⟩ with hi4def
  have hi4 : (i4 : ℕ) = 4 := rfl
  set A4 := {x : Ω W q | 16 < ‖gueBlock W q x i4‖} with hA4
  set τ : Ω W q → ℝ := fun x => Real.exp (-(W : ℝ) / 4) * ‖gueBlock W q x i4‖ ^ 2 +
    Real.exp ((W : ℝ) / 4) * A4.indicator (fun _ => 1) x with hτ
  have hTle : ∀ x, ∑ l, ∑ j, (fderiv ℝ (fun x => hsInner (Complex.I • hermBasis W l) (Fm x)) x
        (rotFrame W q g R (skewProjBasis P j) x) *
      fderiv ℝ (fun x => hsInner (Complex.I • hermBasis W j) (Fm x)) x
        (rotFrame W q g R (skewProjBasis P l) x) +
      hsInner (Complex.I • hermBasis W l) (Fm x) * hsInner (Complex.I • hermBasis W j) (Fm x) *
        ScoreActive_BL W q g R (skewProjBasis P j) (rotFrame W q g R (skewProjBasis P l) x) +
      hsInner (Complex.I • hermBasis W l) (Fm x) *
        fderiv ℝ (fun x => hsInner (Complex.I • hermBasis W j) (Fm x)) x
          (ScoreActive_ZL W q (skewProjBasis P l) (rotFrame W q g R (skewProjBasis P j) x) -
            ScoreActive_ZL W q (skewProjBasis P j) (rotFrame W q g R (skewProjBasis P l) x))) ≤
      C * srcEnergy P v (fun w => χh x w • Kh x w) + C * W * (1 + M₀ ^ 2) * hsSq (Fm x) +
        2 * W * M₀ * max CK 0 * τ x := fun x => by
    have hchain : ∀ A : Matrix (Fin W) (Fin W) ℂ, Aᴴ = -A → P * A * P = A →
        fderiv ℝ Fm x (rotFrame W q g R A x) =
          A * Fm x - Fm x * A - fderiv ℝ (fun w => χh x w • Kh x w) v (A *ᵥ v) :=
      fun A hA hAP => by
      have h := rotFrame_chain hD0 hA hAP x
      rw [(hFd x).lineDeriv_eq_fderiv, (hJd x).lineDeriv_eq_fderiv] at h
      exact h
    have hp := ScoreActive_pointwise hR hP hPP hPR hM x (hFs x).1 (hFs x).2 (fderiv ℝ Fm x)
      (fderiv ℝ (fun w => χh x w • Kh x w) v) hchain i4 hi4
      (fun k => Complex.I • hermBasis W k) (skewProjBasis P) rfl rfl
    have hsrc : srcEnergy P v (fun w => χh x w • Kh x w) = (∑ i, ‖(P *ᵥ v) i‖ ^ 2) *
        ∑ j, (hsSq (fderiv ℝ (fun w => χh x w • Kh x w) v (tangProj P v (Pi.single j 1))) +
          hsSq (fderiv ℝ (fun w => χh x w • Kh x w) v (tangProj P v (Pi.single j Complex.I)))) := by
      simp only [srcEnergy, (hJd x).lineDeriv_eq_fderiv]
    rw [← hsrc] at hp
    have hjac : ∀ l j,
        ScoreActive_ZL W q (skewProjBasis P l) (rotFrame W q g R (skewProjBasis P j) x) -
        ScoreActive_ZL W q (skewProjBasis P j) (rotFrame W q g R (skewProjBasis P l) x) =
        rotFrame W q g R (skewProjBasis P l * skewProjBasis P j -
          skewProjBasis P j * skewProjBasis P l) x := fun l j =>
      ScoreActive_jacobi hR (hKs l) (hKs j) x
    simp only [hda, hjac]
    have hsrc0 : 0 ≤ srcEnergy P v (fun w => χh x w • Kh x w) := by
      rw [hsrc]
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ =>
        add_nonneg (ScoreActive_hsSq_nonneg _) (ScoreActive_hsSq_nonneg _))
    have hf0 := ScoreActive_hsSq_nonneg (Fm x)
    have htail := ScoreActive_tail_pt W (norm_nonneg (gueBlock W q x i4)) hf0 (hf x)
      (A4.indicator (fun _ => 1) x) (by simp [hA4, Set.indicator_apply])
    have a1 := mul_le_mul_of_nonneg_left htail (by positivity : (0 : ℝ) ≤ 4 * W * M₀)
    have a2 : 0 ≤ W * hsSq (Fm x) * (32 * (1 - M₀) ^ 2 + 3 * M₀ ^ 2) :=
      mul_nonneg (mul_nonneg hW0 hf0) (by positivity)
    have hC39 : 0 ≤ C - 39 := by
      rw [hC]; linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * (8 + Real.exp 16)) hCK]
    have a3 : 0 ≤ (C - 39) * (W * (1 + M₀ ^ 2) * hsSq (Fm x)) :=
      mul_nonneg hC39 (mul_nonneg (by positivity) hf0)
    have a4 : 0 ≤ (C - 3) * srcEnergy P v (fun w => χh x w • Kh x w) :=
      mul_nonneg (by linarith) hsrc0
    refine hp.trans ?_
    simp only [hτ]
    nlinarith [a1, a2, a3, a4]
  -- measurability
  have hfc : Continuous fun x => hsSq (Fm x) := by
    unfold hsSq
    exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
      ((hFc.continuous.matrix_elem a b).norm).pow 2
  have hVc : Continuous fun x : Ω W q => gueBlock W q x i4 := (ScoreActive_VL W q i4).continuous
  have hA : MeasurableSet A4 := (isOpen_lt continuous_const hVc.norm).measurableSet
  have hmf : Measurable fun x => ENNReal.ofReal (C * W * (1 + M₀ ^ 2) * hsSq (Fm x)) :=
    (continuous_const.mul hfc).measurable.ennreal_ofReal
  have hmτ : Measurable fun x => ENNReal.ofReal (2 * W * M₀ * max CK 0 * τ x) :=
    (measurable_const.mul ((continuous_const.mul (hVc.norm.pow 2)).measurable.add
      (measurable_const.mul (measurable_const.indicator hA)))).ennreal_ofReal
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  refine le_trans (le_of_eq (lintegral_congr fun x => ?_)) (hst.trans ?_)
  · rw [active_gaussDiv_eq hD0 x, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
      sq_abs]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ScoreActive_div_rot hR (hKs k),
      ((ha2 k).differentiable (by norm_num) x).lineDeriv_eq_fderiv]
  calc _ ≤ ∫⁻ x, (ENNReal.ofReal (C * srcEnergy P v (fun w => χh x w • Kh x w)) +
          ENNReal.ofReal (C * W * (1 + M₀ ^ 2) * hsSq (Fm x)) +
          ENNReal.ofReal (2 * W * M₀ * max CK 0 * τ x)) ∂(μ W q) :=
        lintegral_mono fun x => (ENNReal.ofReal_le_ofReal (hTle x)).trans
          (ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl))
    _ = ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (srcEnergy P v (fun w => χh x w • Kh x w))
          ∂(μ W q) + ENNReal.ofReal (C * W * (1 + M₀ ^ 2)) *
            ∫⁻ x, ENNReal.ofReal (hsSq (Fm x)) ∂(μ W q) +
          ENNReal.ofReal (2 * W * M₀ * max CK 0) * ∫⁻ x, ENNReal.ofReal (τ x) ∂(μ W q) := by
        rw [lintegral_add_right _ hmτ, lintegral_add_right _ hmf]
        simp only [ENNReal.ofReal_mul hC0, ENNReal.ofReal_mul (by positivity :
          (0 : ℝ) ≤ C * W * (1 + M₀ ^ 2)), ENNReal.ofReal_mul (by positivity :
          (0 : ℝ) ≤ 2 * W * M₀ * max CK 0)]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (srcEnergy P v (fun w => χh x w • Kh x w))
          ∂(μ W q) + ENNReal.ofReal (C * W * (1 + M₀ ^ 2)) *
            ∫⁻ x, ENNReal.ofReal (hsSq (Fm x)) ∂(μ W q) +
          ENNReal.ofReal (C * W * M₀ * Real.exp (-(1 / 8) * W)) := by
        gcongr
        calc ENNReal.ofReal (2 * W * M₀ * max CK 0) * ∫⁻ x, ENNReal.ofReal (τ x) ∂(μ W q)
            ≤ ENNReal.ofReal (2 * W * M₀ * max CK 0) *
              ENNReal.ofReal ((8 + Real.exp 16) * Real.exp (-(1 / 8) * W)) := by
              gcongr; exact ScoreActive_tail W q i4
          _ ≤ _ := ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hE := Real.exp_pos (-(1 / 8) * (W : ℝ))
        have : 0 ≤ 39 * W * M₀ * Real.exp (-(1 / 8) * W) := by positivity
        rw [hC]
        nlinarith

end LSBA
