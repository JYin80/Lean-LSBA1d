import LSBA.Gauss.Divergence

/-!
# Second moment of the Gaussian divergence

`𝔼|δ_G Y|² = 𝔼‖Y‖² + 𝔼 Σ_{i,j} ∂_j Y_i ∂_i Y_j` and (10.4) [up:eq:lift-divergence-reduction]
`𝔼|δ_G Y|² ≤ 𝔼‖Y‖² + 𝔼‖DY‖²_HS` for `C²` fields of polynomial growth, in standard coordinates.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

noncomputable section

namespace LSBA

/-! ### Polynomial growth and Gaussian integrability -/

private lemma divMoment_one_le {E : Type*} [NormedAddCommGroup E] (x : E) :
    (1 : ℝ) ≤ 1 + ‖x‖ := by
  linarith [norm_nonneg x]

private lemma divMoment_pg_nonneg {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : E → F} {C : ℝ} {k : ℕ} (h : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k) : 0 ≤ C := by
  simpa using (norm_nonneg _).trans (h 0)

private lemma divMoment_pg_mono {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedAddCommGroup G] {f : E → F} {g : E → G} (h : ∀ x, ‖f x‖ ≤ ‖g x‖)
    (hg : PolyGrowth g) : PolyGrowth f := by
  obtain ⟨C, k, hC⟩ := hg
  exact ⟨C, k, fun x => (h x).trans (hC x)⟩

private lemma divMoment_pg_norm {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : E → F} (hf : PolyGrowth f) : PolyGrowth (fun x => ‖f x‖) :=
  divMoment_pg_mono (fun x => by rw [norm_norm]) hf

private lemma divMoment_pg_const {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (c : F) : PolyGrowth (fun _ : E => c) :=
  ⟨‖c‖, 0, fun x => by simp⟩

private lemma divMoment_pg_add {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f g : E → F} (hf : PolyGrowth f) (hg : PolyGrowth g) :
    PolyGrowth (fun x => f x + g x) := by
  obtain ⟨C₁, k₁, h₁⟩ := hf
  obtain ⟨C₂, k₂, h₂⟩ := hg
  have hC₁ := divMoment_pg_nonneg h₁
  have hC₂ := divMoment_pg_nonneg h₂
  refine ⟨C₁ + C₂, max k₁ k₂, fun x => ?_⟩
  have hs := divMoment_one_le x
  have e1 : (1 + ‖x‖) ^ k₁ ≤ (1 + ‖x‖) ^ max k₁ k₂ := pow_le_pow_right₀ hs (le_max_left _ _)
  have e2 : (1 + ‖x‖) ^ k₂ ≤ (1 + ‖x‖) ^ max k₁ k₂ := pow_le_pow_right₀ hs (le_max_right _ _)
  calc ‖f x + g x‖ ≤ ‖f x‖ + ‖g x‖ := norm_add_le _ _
    _ ≤ C₁ * (1 + ‖x‖) ^ k₁ + C₂ * (1 + ‖x‖) ^ k₂ := add_le_add (h₁ x) (h₂ x)
    _ ≤ (C₁ + C₂) * (1 + ‖x‖) ^ max k₁ k₂ := by rw [add_mul]; gcongr

private lemma divMoment_pg_neg {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : E → F} (hf : PolyGrowth f) : PolyGrowth (fun x => -f x) :=
  divMoment_pg_mono (fun x => by rw [norm_neg]) hf

private lemma divMoment_pg_sub {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f g : E → F} (hf : PolyGrowth f) (hg : PolyGrowth g) :
    PolyGrowth (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using divMoment_pg_add hf (divMoment_pg_neg hg)

private lemma divMoment_pg_mul {E : Type*} [NormedAddCommGroup E] {f g : E → ℝ}
    (hf : PolyGrowth f) (hg : PolyGrowth g) : PolyGrowth (fun x => f x * g x) := by
  obtain ⟨C₁, k₁, h₁⟩ := hf
  obtain ⟨C₂, k₂, h₂⟩ := hg
  have hC₁ := divMoment_pg_nonneg h₁
  have hC₂ := divMoment_pg_nonneg h₂
  refine ⟨C₁ * C₂, k₁ + k₂, fun x => ?_⟩
  calc ‖f x * g x‖ = ‖f x‖ * ‖g x‖ := norm_mul _ _
    _ ≤ (C₁ * (1 + ‖x‖) ^ k₁) * (C₂ * (1 + ‖x‖) ^ k₂) :=
        mul_le_mul (h₁ x) (h₂ x) (norm_nonneg _) (mul_nonneg hC₁ (by positivity))
    _ = C₁ * C₂ * (1 + ‖x‖) ^ (k₁ + k₂) := by ring

private lemma divMoment_pg_sum {E F κ : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (s : Finset κ) {f : κ → E → F} (hf : ∀ k ∈ s, PolyGrowth (f k)) :
    PolyGrowth (fun x => ∑ k ∈ s, f k x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (divMoment_pg_const (E := E) (0 : F))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact divMoment_pg_add (hf a (Finset.mem_insert_self _ _))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

private lemma divMoment_pg_coord {ι : Type*} [Fintype ι] (i : ι) :
    PolyGrowth (fun x : ι → ℝ => x i) :=
  ⟨1, 1, fun x => by
    have := norm_le_pi_norm x i
    simp only [pow_one, one_mul]
    linarith [norm_nonneg x]⟩

/-- Polynomial moments of the sup norm are finite under the standard Gaussian on `ℝ^ι`. -/
private lemma divMoment_integrable_poly (ι : Type*) [Fintype ι] (m : ℕ) :
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
private lemma divMoment_integrable {ι : Type*} [Fintype ι] {g : (ι → ℝ) → ℝ}
    (hc : Continuous g) (hg : PolyGrowth g) : Integrable g (stdGauss ι) := by
  obtain ⟨C, k, hC⟩ := hg
  refine ((divMoment_integrable_poly ι k).const_mul C).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, ← Real.norm_eq_abs]
  exact hC x

/-! ### Test functions for Gaussian integration by parts -/

/-- `C¹` with the function and its derivative of polynomial growth. -/
private def DivMomentStd {ι : Type*} [Fintype ι] (g : (ι → ℝ) → ℝ) : Prop :=
  ContDiff ℝ 1 g ∧ PolyGrowth g ∧ PolyGrowth (fderiv ℝ g)

/-- Continuous with polynomial growth. -/
private def DivMomentGood {ι : Type*} [Fintype ι] (g : (ι → ℝ) → ℝ) : Prop :=
  Continuous g ∧ PolyGrowth g

private lemma DivMomentGood.integrable {ι : Type*} [Fintype ι] {g : (ι → ℝ) → ℝ}
    (hg : DivMomentGood g) : Integrable g (stdGauss ι) :=
  divMoment_integrable hg.1 hg.2

private lemma DivMomentGood.mul {ι : Type*} [Fintype ι] {f g : (ι → ℝ) → ℝ}
    (hf : DivMomentGood f) (hg : DivMomentGood g) : DivMomentGood (fun x => f x * g x) :=
  ⟨hf.1.mul hg.1, divMoment_pg_mul hf.2 hg.2⟩

private lemma DivMomentStd.good {ι : Type*} [Fintype ι] {g : (ι → ℝ) → ℝ}
    (hg : DivMomentStd g) : DivMomentGood g :=
  ⟨hg.1.continuous, hg.2.1⟩

private lemma DivMomentStd.integrable {ι : Type*} [Fintype ι] {g : (ι → ℝ) → ℝ}
    (hg : DivMomentStd g) : Integrable g (stdGauss ι) :=
  hg.good.integrable

private lemma DivMomentStd.differentiableAt {ι : Type*} [Fintype ι] {g : (ι → ℝ) → ℝ}
    (hg : DivMomentStd g) (x : ι → ℝ) : DifferentiableAt ℝ g x :=
  hg.1.differentiable one_ne_zero x

private lemma divMoment_std_coord {ι : Type*} [Fintype ι] (i : ι) :
    DivMomentStd (fun x : ι → ℝ => x i) := by
  refine ⟨contDiff_apply ℝ (fun _ : ι => ℝ) i, divMoment_pg_coord i, 1, 0, fun x => ?_⟩
  rw [(hasFDerivAt_apply i x).fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by simp) fun v => ?_
  simpa using norm_le_pi_norm v i

private lemma divMoment_fderiv_coord {ι : Type*} (i : ι) (x v : ι → ℝ) :
    fderiv ℝ (fun x : ι → ℝ => x i) x v = v i := by
  rw [(hasFDerivAt_apply i x).fderiv]; rfl

private lemma DivMomentStd.mul {ι : Type*} [Fintype ι] {f g : (ι → ℝ) → ℝ}
    (hf : DivMomentStd f) (hg : DivMomentStd g) : DivMomentStd (fun x => f x * g x) := by
  refine ⟨hf.1.mul hg.1, divMoment_pg_mul hf.2.1 hg.2.1, ?_⟩
  have h : fderiv ℝ (fun x => f x * g x) =
      fun x => f x • fderiv ℝ g x + g x • fderiv ℝ f x :=
    funext fun x => fderiv_fun_mul (hf.differentiableAt x) (hg.differentiableAt x)
  rw [h]
  refine divMoment_pg_mono (g := fun x => ‖f x‖ * ‖fderiv ℝ g x‖ + ‖g x‖ * ‖fderiv ℝ f x‖)
    (fun x => ?_) (divMoment_pg_add
      (divMoment_pg_mul (divMoment_pg_norm hf.2.1) (divMoment_pg_norm hg.2.2))
      (divMoment_pg_mul (divMoment_pg_norm hg.2.1) (divMoment_pg_norm hf.2.2)))
  calc ‖f x • fderiv ℝ g x + g x • fderiv ℝ f x‖
      ≤ ‖f x • fderiv ℝ g x‖ + ‖g x • fderiv ℝ f x‖ := norm_add_le _ _
    _ = ‖f x‖ * ‖fderiv ℝ g x‖ + ‖g x‖ * ‖fderiv ℝ f x‖ := by rw [norm_smul, norm_smul]
    _ ≤ ‖‖f x‖ * ‖fderiv ℝ g x‖ + ‖g x‖ * ‖fderiv ℝ f x‖‖ := le_abs_self _

private lemma DivMomentStd.sub {ι : Type*} [Fintype ι] {f g : (ι → ℝ) → ℝ}
    (hf : DivMomentStd f) (hg : DivMomentStd g) : DivMomentStd (fun x => f x - g x) := by
  refine ⟨hf.1.sub hg.1, divMoment_pg_sub hf.2.1 hg.2.1, ?_⟩
  have h : fderiv ℝ (fun x => f x - g x) = fun x => fderiv ℝ f x - fderiv ℝ g x :=
    funext fun x => fderiv_fun_sub (hf.differentiableAt x) (hg.differentiableAt x)
  rw [h]
  exact divMoment_pg_sub hf.2.2 hg.2.2

private lemma DivMomentStd.sum {ι κ : Type*} [Fintype ι] (s : Finset κ) {f : κ → (ι → ℝ) → ℝ}
    (hf : ∀ k ∈ s, DivMomentStd (f k)) : DivMomentStd (fun x => ∑ k ∈ s, f k x) := by
  refine ⟨ContDiff.sum fun k hk => (hf k hk).1, divMoment_pg_sum s fun k hk => (hf k hk).2.1, ?_⟩
  have h : fderiv ℝ (fun x => ∑ k ∈ s, f k x) = fun x => ∑ k ∈ s, fderiv ℝ (f k) x :=
    funext fun x => fderiv_fun_sum fun k hk => (hf k hk).differentiableAt x
  rw [h]
  exact divMoment_pg_sum s fun k hk => (hf k hk).2.2

/-- The derivative of a `C¹` map followed by a continuous linear form. -/
private lemma divMoment_fderiv_clm {ι E' : Type*} [Fintype ι] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] {F : (ι → ℝ) → E'} (hF : ContDiff ℝ 1 F) (L : E' →L[ℝ] ℝ)
    (x : ι → ℝ) : fderiv ℝ (fun x => L (F x)) x = L.comp (fderiv ℝ F x) :=
  (L.hasFDerivAt.comp x ((hF.differentiable one_ne_zero) x).hasFDerivAt).fderiv

/-- Composition with a continuous linear form keeps the class and commutes with `fderiv`. -/
private lemma divMoment_std_clm {ι E' : Type*} [Fintype ι] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] {F : (ι → ℝ) → E'} (hF : ContDiff ℝ 1 F) (hb : PolyGrowth F)
    (hb' : PolyGrowth (fderiv ℝ F)) (L : E' →L[ℝ] ℝ) :
    DivMomentStd (fun x => L (F x)) ∧
      ∀ x v, fderiv ℝ (fun x => L (F x)) x v = L (fderiv ℝ F x v) := by
  have hd : ∀ x, fderiv ℝ (fun x => L (F x)) x = L.comp (fderiv ℝ F x) :=
    divMoment_fderiv_clm hF L
  refine ⟨⟨L.contDiff.comp hF, ?_, ?_⟩, fun x v => by rw [hd]; rfl⟩
  · refine divMoment_pg_mono (g := fun x => ‖L‖ * ‖F x‖) (fun x => ?_)
      (divMoment_pg_mul (divMoment_pg_const _) (divMoment_pg_norm hb))
    calc ‖L (F x)‖ ≤ ‖L‖ * ‖F x‖ := L.le_opNorm _
      _ ≤ ‖‖L‖ * ‖F x‖‖ := le_abs_self _
  · have : fderiv ℝ (fun x => L (F x)) = fun x => L.comp (fderiv ℝ F x) := funext hd
    rw [this]
    refine divMoment_pg_mono (g := fun x => ‖L‖ * ‖fderiv ℝ F x‖) (fun x => ?_)
      (divMoment_pg_mul (divMoment_pg_const _) (divMoment_pg_norm hb'))
    calc ‖L.comp (fderiv ℝ F x)‖ ≤ ‖L‖ * ‖fderiv ℝ F x‖ := L.opNorm_comp_le _
      _ ≤ ‖‖L‖ * ‖fderiv ℝ F x‖‖ := le_abs_self _

/-- Composition with a continuous linear form keeps continuity and polynomial growth. -/
private lemma divMoment_good_clm {ι E' : Type*} [Fintype ι] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] {F : (ι → ℝ) → E'} (hF : Continuous F) (hb : PolyGrowth F)
    (L : E' →L[ℝ] ℝ) : DivMomentGood (fun x => L (F x)) := by
  refine ⟨L.continuous.comp hF, ?_⟩
  refine divMoment_pg_mono (g := fun x => ‖L‖ * ‖F x‖) (fun x => ?_)
    (divMoment_pg_mul (divMoment_pg_const _) (divMoment_pg_norm hb))
  calc ‖L (F x)‖ ≤ ‖L‖ * ‖F x‖ := L.le_opNorm _
    _ ≤ ‖‖L‖ * ‖F x‖‖ := le_abs_self _

/-- Gaussian integration by parts `𝔼[x_i g] = 𝔼[∂_i g]` for a `C¹` function `g` with `g` and
`Dg` of polynomial growth, from the complex-valued Stein identity. -/
private lemma divMoment_stein {ι : Type*} [Fintype ι] [DecidableEq ι] {g : (ι → ℝ) → ℝ}
    (hg : DivMomentStd g) (i : ι) :
    ∫ x, x i * g x ∂(stdGauss ι) = ∫ x, fderiv ℝ g x (Pi.single i 1) ∂(stdGauss ι) := by
  obtain ⟨hgc, hg1, hg2⟩ := hg
  obtain ⟨C, k, hC⟩ := divMoment_pg_add (divMoment_pg_norm hg1) (divMoment_pg_norm hg2)
  have hgb : ∀ x, |g x| ≤ C * (1 + ‖x‖) ^ k := fun x => by
    have := hC x
    rw [norm_eq_abs] at this
    rw [← Real.norm_eq_abs] at this ⊢
    exact (le_trans (by linarith [norm_nonneg (fderiv ℝ g x)]) (le_abs_self _)).trans this
  have hgb' : ∀ x, ‖fderiv ℝ g x‖ ≤ C * (1 + ‖x‖) ^ k := fun x => by
    have := hC x
    rw [norm_eq_abs] at this
    exact (le_trans (by linarith [norm_nonneg (g x)]) (le_abs_self _)).trans this
  have hF : ContDiff ℝ 1 (fun x => ((g x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hgc
  have hFd : ∀ x, fderiv ℝ (fun x => ((g x : ℝ) : ℂ)) x =
      Complex.ofRealCLM.comp (fderiv ℝ g x) := fun x =>
    (Complex.ofRealCLM.hasFDerivAt.comp x ((hgc.differentiable one_ne_zero) x).hasFDerivAt).fderiv
  have h := integral_coord_mul_stdGauss (fun x => ((g x : ℝ) : ℂ)) hF (C := C) (k := k)
    (fun x => by simpa using hgb x)
    (fun x => by
      rw [hFd x]
      refine ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans (hgb' x)) fun v => ?_
      rw [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real]
      calc ‖fderiv ℝ g x v‖ ≤ ‖fderiv ℝ g x‖ * ‖v‖ := (fderiv ℝ g x).le_opNorm v
        _ ≤ C * (1 + ‖x‖) ^ k * ‖v‖ := by gcongr; exact hgb' x) i
  simp only [hFd, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    ← Complex.ofReal_mul, integral_complex_ofReal] at h
  exact_mod_cast h

/-! ### The second-moment identity for abstract coefficients

`y i` stands for the components `Y_i`, `a i j` for `∂_j Y_i`, `b i j k` for `∂_i ∂_j Y_k`. -/

private lemma divMoment_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : ι → (ι → ℝ) → ℝ) (a : ι → ι → (ι → ℝ) → ℝ) (b : ι → ι → ι → (ι → ℝ) → ℝ)
    (hy : ∀ i, DivMomentStd (y i)) (ha : ∀ i j, DivMomentStd (a i j))
    (hb : ∀ i j k, DivMomentGood (b i j k))
    (hyd : ∀ i k x, fderiv ℝ (y i) x (Pi.single k 1) = a i k x)
    (had : ∀ i j k x, fderiv ℝ (a i j) x (Pi.single k 1) = b k j i x)
    (hsymm : ∀ i j k x, b i j k x = b j i k x)
    (D : (ι → ℝ) → ℝ) (hDx : ∀ x, D x = ∑ j, (x j * y j x - a j j x)) :
    ∫ x, D x ^ 2 ∂(stdGauss ι) =
      ∫ x, (∑ i, y i x ^ 2 + ∑ i, ∑ j, a i j x * a j i x) ∂(stdGauss ι) := by
  have hDfun : D = fun x => ∑ j, (x j * y j x - a j j x) := funext hDx
  have hterm : ∀ j, DivMomentStd (fun x => x j * y j x - a j j x) := fun j =>
    ((divMoment_std_coord j).mul (hy j)).sub (ha j j)
  have hD : DivMomentStd D := by
    rw [hDfun]; exact DivMomentStd.sum _ fun j _ => hterm j
  -- the partial derivatives of the divergence
  have hdD : ∀ i x, fderiv ℝ D x (Pi.single i 1) = y i x + ∑ j, (x j * a j i x - b i j j x) := by
    intro i x
    rw [hDfun, fderiv_fun_sum fun j _ => (hterm j).differentiableAt x,
      _root_.sum_apply]
    have hj : ∀ j, fderiv ℝ (fun x => x j * y j x - a j j x) x (Pi.single i 1) =
        (Pi.single i 1 : ι → ℝ) j * y j x + (x j * a j i x - b i j j x) := by
      intro j
      rw [fderiv_fun_sub (((divMoment_std_coord j).mul (hy j)).differentiableAt x)
        ((ha j j).differentiableAt x),
        fderiv_fun_mul ((divMoment_std_coord j).differentiableAt x) ((hy j).differentiableAt x)]
      simp only [sub_apply, add_apply,
        smul_apply, smul_eq_mul, divMoment_fderiv_coord, hyd, had]
      ring
    rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_add_distrib]
    congr 1
    simp [Pi.single_apply]
  have hI : ∀ i j, Integrable (fun x => x j * (y i x * a j i x)) (stdGauss ι) := fun i j =>
    ((divMoment_std_coord j).mul ((hy i).mul (ha j i))).integrable
  have hIb : ∀ i j, Integrable (fun x => y i x * b i j j x) (stdGauss ι) := fun i j =>
    ((hy i).good.mul (hb i j j)).integrable
  -- Gaussian integration by parts for the products `y_i a_{ji}`
  have hK : ∀ i j, ∫ x, (x j * (y i x * a j i x) - y i x * b i j j x) ∂(stdGauss ι) =
      ∫ x, a j i x * a i j x ∂(stdGauss ι) := by
    intro i j
    have s := divMoment_stein ((hy i).mul (ha j i)) j
    have hf : ∀ x, fderiv ℝ (fun x => y i x * a j i x) x (Pi.single j 1) =
        y i x * b i j j x + a j i x * a i j x := by
      intro x
      rw [fderiv_fun_mul ((hy i).differentiableAt x) ((ha j i).differentiableAt x)]
      simp only [add_apply, smul_apply, smul_eq_mul, hyd,
        had, hsymm j i j x]
    rw [integral_sub (hI i j) (hIb i j), s]
    simp only [hf]
    rw [integral_add (hIb i j) ((ha j i).mul (ha i j)).integrable]
    ring
  -- the integrand `y_i ∂_i D`
  have hG : ∀ i x, y i x * fderiv ℝ D x (Pi.single i 1) =
      y i x * y i x + ∑ j, (x j * (y i x * a j i x) - y i x * b i j j x) := by
    intro i x
    rw [hdD, mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  have hIj : ∀ i j, Integrable (fun x => x j * (y i x * a j i x) - y i x * b i j j x)
      (stdGauss ι) := fun i j => (hI i j).sub (hIb i j)
  have hGs : ∀ i, Integrable
      (fun x => ∑ j, (x j * (y i x * a j i x) - y i x * b i j j x)) (stdGauss ι) := fun i =>
    integrable_finsetSum _ fun j _ => hIj i j
  have hGint : ∀ i, Integrable (fun x => y i x * fderiv ℝ D x (Pi.single i 1)) (stdGauss ι) := by
    intro i
    have : (fun x => y i x * fderiv ℝ D x (Pi.single i 1)) = fun x =>
        y i x * y i x + ∑ j, (x j * (y i x * a j i x) - y i x * b i j j x) := funext (hG i)
    rw [this]
    exact ((hy i).mul (hy i)).integrable.add (hGs i)
  have hGval : ∀ i, ∫ x, y i x * fderiv ℝ D x (Pi.single i 1) ∂(stdGauss ι) =
      ∫ x, y i x * y i x ∂(stdGauss ι) + ∑ j, ∫ x, a j i x * a i j x ∂(stdGauss ι) := by
    intro i
    have : (fun x => y i x * fderiv ℝ D x (Pi.single i 1)) = fun x =>
        y i x * y i x + ∑ j, (x j * (y i x * a j i x) - y i x * b i j j x) := funext (hG i)
    rw [this, integral_add ((hy i).mul (hy i)).integrable (hGs i),
      integral_finsetSum _ fun j _ => hIj i j]
    congr 1
    exact Finset.sum_congr rfl fun j _ => hK i j
  -- Gaussian integration by parts for the products `y_i D`
  have hstep : ∀ i, ∫ x, (x i * (y i x * D x) - a i i x * D x) ∂(stdGauss ι) =
      ∫ x, y i x * fderiv ℝ D x (Pi.single i 1) ∂(stdGauss ι) := by
    intro i
    have s := divMoment_stein ((hy i).mul hD) i
    have hf : ∀ x, fderiv ℝ (fun x => y i x * D x) x (Pi.single i 1) =
        y i x * fderiv ℝ D x (Pi.single i 1) + D x * a i i x := by
      intro x
      rw [fderiv_fun_mul ((hy i).differentiableAt x) (hD.differentiableAt x)]
      simp only [add_apply, smul_apply, smul_eq_mul, hyd]
    rw [integral_sub ((divMoment_std_coord i).mul ((hy i).mul hD)).integrable
      ((ha i i).mul hD).integrable, s]
    simp only [hf]
    rw [integral_add (hGint i) (hD.mul (ha i i)).integrable]
    have e2 : ∫ x, D x * a i i x ∂(stdGauss ι) = ∫ x, a i i x * D x ∂(stdGauss ι) := by
      simp only [mul_comm]
    rw [e2]
    ring
  -- the left side as a sum over `i`
  have h0 : ∀ x, D x ^ 2 = ∑ i, (x i * (y i x * D x) - a i i x * D x) := by
    intro x
    have : D x ^ 2 = D x * ∑ i, (x i * y i x - a i i x) := by rw [← hDx x, sq]
    rw [this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hint_i : ∀ i, Integrable (fun x => x i * (y i x * D x) - a i i x * D x) (stdGauss ι) :=
    fun i => ((divMoment_std_coord i).mul ((hy i).mul hD)).integrable.sub
      ((ha i i).mul hD).integrable
  have hL : ∫ x, D x ^ 2 ∂(stdGauss ι) =
      ∑ i, (∫ x, y i x * y i x ∂(stdGauss ι) + ∑ j, ∫ x, a j i x * a i j x ∂(stdGauss ι)) := by
    have : (fun x => D x ^ 2) = fun x => ∑ i, (x i * (y i x * D x) - a i i x * D x) := funext h0
    rw [this, integral_finsetSum _ fun i _ => hint_i i]
    exact Finset.sum_congr rfl fun i _ => (hstep i).trans (hGval i)
  -- the right side
  have hy2 : ∀ i, Integrable (fun x => y i x * y i x) (stdGauss ι) := fun i =>
    ((hy i).mul (hy i)).integrable
  have haa : ∀ i j, Integrable (fun x => a i j x * a j i x) (stdGauss ι) := fun i j =>
    ((ha i j).mul (ha j i)).integrable
  have hr1 : Integrable (fun x => ∑ i, y i x ^ 2) (stdGauss ι) := by
    simp only [sq]
    exact integrable_finsetSum _ fun i _ => hy2 i
  have hr2 : Integrable (fun x => ∑ i, ∑ j, a i j x * a j i x) (stdGauss ι) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => haa i j
  rw [hL, integral_add hr1 hr2]
  simp only [sq]
  rw [integral_finsetSum _ fun i _ => hy2 i,
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => haa i j,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => haa i j]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [mul_comm]

/-! ### Second moment of the divergence -/

private lemma divMoment_sum_mul_le {ι : Type*} [Fintype ι] (a : ι → ι → ℝ) :
    ∑ i, ∑ j, a i j * a j i ≤ ∑ i, ∑ j, a i j ^ 2 := by
  have h1 : ∑ i, ∑ j, a j i ^ 2 = ∑ i, ∑ j, a i j ^ 2 := Finset.sum_comm
  have h2 : 2 * ∑ i, ∑ j, a i j * a j i ≤ ∑ i, ∑ j, (a i j ^ 2 + a j i ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by nlinarith [sq_nonneg (a i j - a j i)]
  have h3 : ∑ i, ∑ j, (a i j ^ 2 + a j i ^ 2) = 2 * ∑ i, ∑ j, a i j ^ 2 := by
    simp only [Finset.sum_add_distrib, h1]; ring
  linarith

/-- The components of a `C²` field of polynomial growth and their first derivatives are in the
class of test functions for integration by parts. -/
private lemma divMoment_std_comp {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : (ι → ℝ) → ι → ℝ}
    (hY : ContDiff ℝ 2 Y) (hb : PolyGrowth Y) (hb1 : PolyGrowth (fderiv ℝ Y))
    (hb2 : PolyGrowth (fderiv ℝ (fderiv ℝ Y))) :
    (∀ i, DivMomentStd (fun x => Y x i)) ∧
      ∀ i j, DivMomentStd (fun x => fderiv ℝ Y x (Pi.single j 1) i) := by
  have hY1 : ContDiff ℝ 1 Y := hY.of_le (by norm_num)
  have hG : ContDiff ℝ 1 (fderiv ℝ Y) := hY.fderiv_right (by norm_num)
  exact ⟨fun i => (divMoment_std_clm hY1 hb hb1 (ContinuousLinearMap.proj i)).1,
    fun i j => (divMoment_std_clm hG hb1 hb2 ((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.apply ℝ (ι → ℝ) (Pi.single j 1)))).1⟩

/-- For a `C¹` field the line derivatives in `δ_G` are the partial derivatives. -/
private lemma divMoment_gaussDiv_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Y : (ι → ℝ) → ι → ℝ} (hY : ContDiff ℝ 1 Y) (x : ι → ℝ) :
    gaussDiv Y x = ∑ j, (x j * Y x j - fderiv ℝ Y x (Pi.single j 1) j) := by
  unfold gaussDiv
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [((contDiff_pi.mp hY j).differentiable one_ne_zero x).lineDeriv_eq_fderiv]
  have h := congrArg (fun T => T (Pi.single j 1))
    (divMoment_fderiv_clm hY (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j) x)
  simpa using h

/-- The divergence of a `C²` field of polynomial growth is in the class of test functions. -/
private lemma divMoment_std_gaussDiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Y : (ι → ℝ) → ι → ℝ} (hY : ContDiff ℝ 2 Y) (hb : PolyGrowth Y)
    (hb1 : PolyGrowth (fderiv ℝ Y)) (hb2 : PolyGrowth (fderiv ℝ (fderiv ℝ Y))) :
    DivMomentStd (gaussDiv Y) := by
  obtain ⟨hy, ha⟩ := divMoment_std_comp hY hb hb1 hb2
  have hY1 : ContDiff ℝ 1 Y := hY.of_le (by norm_num)
  have : gaussDiv Y = fun x => ∑ j, (x j * Y x j - fderiv ℝ Y x (Pi.single j 1) j) :=
    funext (divMoment_gaussDiv_eq hY1)
  rw [this]
  exact DivMomentStd.sum _ fun j _ => ((divMoment_std_coord j).mul (hy j)).sub (ha j j)

/-- `∫⁻ ‖δ_G Y‖ₑ² = ofReal (𝔼 (δ_G Y)²)` for a `C²` field of polynomial growth. -/
private lemma divMoment_lintegral_sq_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Y : (ι → ℝ) → ι → ℝ} (hY : ContDiff ℝ 2 Y) (hb : PolyGrowth Y)
    (hb1 : PolyGrowth (fderiv ℝ Y)) (hb2 : PolyGrowth (fderiv ℝ (fderiv ℝ Y))) :
    ∫⁻ x, ‖gaussDiv Y x‖ₑ ^ 2 ∂(stdGauss ι) =
      ENNReal.ofReal (∫ x, gaussDiv Y x ^ 2 ∂(stdGauss ι)) := by
  have hD := divMoment_std_gaussDiv hY hb hb1 hb2
  have hD2 : Integrable (fun x => gaussDiv Y x ^ 2) (stdGauss ι) := by
    simpa only [sq] using (hD.mul hD).integrable
  rw [ofReal_integral_eq_lintegral_ofReal hD2 (Filter.Eventually.of_forall fun x => sq_nonneg _)]
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-- The second-moment identity in the proof of (10.4) [up:eq:lift-divergence-reduction]:
`𝔼|δ_G Y|² = 𝔼 Σ_i Y_i² + 𝔼 Σ_{i,j} ∂_j Y_i ∂_i Y_j`, for `C²` fields with polynomial growth
of the field and of its first two derivatives. -/
theorem integral_gaussDiv_sq {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : (ι → ℝ) → ι → ℝ}
    (hY : ContDiff ℝ 2 Y) (hb : PolyGrowth Y) (hb1 : PolyGrowth (fderiv ℝ Y))
    (hb2 : PolyGrowth (fderiv ℝ (fderiv ℝ Y))) :
    ∫ x, gaussDiv Y x ^ 2 ∂(stdGauss ι) =
      ∫ x, (∑ i, Y x i ^ 2 +
        ∑ i, ∑ j, fderiv ℝ Y x (Pi.single j 1) i * fderiv ℝ Y x (Pi.single i 1) j)
        ∂(stdGauss ι) := by
  have hY1 : ContDiff ℝ 1 Y := hY.of_le (by norm_num)
  have hG : ContDiff ℝ 1 (fderiv ℝ Y) := hY.fderiv_right (by norm_num)
  obtain ⟨hy, ha⟩ := divMoment_std_comp hY hb hb1 hb2
  have hsym : ∀ x v w, fderiv ℝ (fderiv ℝ Y) x v w = fderiv ℝ (fderiv ℝ Y) x w v := fun x v w =>
    (hY.contDiffAt.isSymmSndFDerivAt (by simp)).eq v w
  exact divMoment_identity (fun i x => Y x i) (fun i j x => fderiv ℝ Y x (Pi.single j 1) i)
    (fun i j k x => fderiv ℝ (fderiv ℝ Y) x (Pi.single i 1) (Pi.single j 1) k) hy ha
    (fun i j k => divMoment_good_clm (hG.continuous_fderiv one_ne_zero) hb2
      (((ContinuousLinearMap.proj k).comp
        (ContinuousLinearMap.apply ℝ (ι → ℝ) (Pi.single j 1))).comp
        (ContinuousLinearMap.apply ℝ ((ι → ℝ) →L[ℝ] (ι → ℝ)) (Pi.single i 1))))
    (fun i k x => by
      simpa using (divMoment_std_clm hY1 hb hb1 (ContinuousLinearMap.proj i)).2 x (Pi.single k 1))
    (fun i j k x => by
      simpa using (divMoment_std_clm hG hb1 hb2 ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.apply ℝ (ι → ℝ) (Pi.single j 1)))).2 x (Pi.single k 1))
    (fun i j k x => by rw [hsym x (Pi.single i 1) (Pi.single j 1)])
    (gaussDiv Y) (divMoment_gaussDiv_eq hY1)

/-- (10.4) [up:eq:lift-divergence-reduction] in standard coordinates:
`𝔼|δ_G Y|² ≤ 𝔼 Σ_i Y_i² + 𝔼 Σ_{i,j} (∂_j Y_i)²`. -/
theorem lintegral_gaussDiv_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Y : (ι → ℝ) → ι → ℝ} (hY : ContDiff ℝ 2 Y) (hb : PolyGrowth Y)
    (hb1 : PolyGrowth (fderiv ℝ Y)) (hb2 : PolyGrowth (fderiv ℝ (fderiv ℝ Y))) :
    ∫⁻ x, ‖gaussDiv Y x‖ₑ ^ 2 ∂(stdGauss ι) ≤
      ∫⁻ x, ENNReal.ofReal (∑ i, Y x i ^ 2 + ∑ i, ∑ j, (fderiv ℝ Y x (Pi.single j 1) i) ^ 2)
        ∂(stdGauss ι) := by
  obtain ⟨hy, ha⟩ := divMoment_std_comp hY hb hb1 hb2
  have hyy : ∀ i, Integrable (fun x => Y x i ^ 2) (stdGauss ι) := fun i => by
    simpa only [sq] using ((hy i).mul (hy i)).integrable
  have haa : ∀ i j, Integrable (fun x => (fderiv ℝ Y x (Pi.single j 1) i) ^ 2) (stdGauss ι) :=
    fun i j => by simpa only [sq] using ((ha i j).mul (ha i j)).integrable
  have hab : ∀ i j, Integrable (fun x => fderiv ℝ Y x (Pi.single j 1) i *
      fderiv ℝ Y x (Pi.single i 1) j) (stdGauss ι) := fun i j => ((ha i j).mul (ha j i)).integrable
  have hint1 : Integrable (fun x => ∑ i, Y x i ^ 2 +
      ∑ i, ∑ j, fderiv ℝ Y x (Pi.single j 1) i * fderiv ℝ Y x (Pi.single i 1) j) (stdGauss ι) :=
    (integrable_finsetSum _ fun i _ => hyy i).add
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hab i j)
  have hint2 : Integrable (fun x => ∑ i, Y x i ^ 2 +
      ∑ i, ∑ j, (fderiv ℝ Y x (Pi.single j 1) i) ^ 2) (stdGauss ι) :=
    (integrable_finsetSum _ fun i _ => hyy i).add
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => haa i j)
  have hle : ∫ x, gaussDiv Y x ^ 2 ∂(stdGauss ι) ≤ ∫ x, (∑ i, Y x i ^ 2 +
      ∑ i, ∑ j, (fderiv ℝ Y x (Pi.single j 1) i) ^ 2) ∂(stdGauss ι) := by
    rw [integral_gaussDiv_sq hY hb hb1 hb2]
    refine integral_mono hint1 hint2 fun x => ?_
    have := divMoment_sum_mul_le (fun i j => fderiv ℝ Y x (Pi.single j 1) i)
    linarith
  rw [divMoment_lintegral_sq_eq hY hb hb1 hb2,
    ← ofReal_integral_eq_lintegral_ofReal hint2
      (Filter.Eventually.of_forall fun x => by positivity)]
  exact ENNReal.ofReal_le_ofReal hle

end LSBA
