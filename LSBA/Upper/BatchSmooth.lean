import LSBA.Upper.Operator
import LSBA.Gauss.Divergence

/-!
# Smoothness of the batch cocycle and of the terminal flag in the inputs

For a fixed incoming flag, the cocycle `c(T(ω); U, Y)` and the terminal flag `(P_{TU}, P_{TY})`
of the batch `T(ω)` of Definition 8.5 [up:def:transfer-operator] are `C¹` functions of the
standard Gaussian coordinates `ω`, with polynomially bounded derivatives.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

section Toolkit

variable {E : Type*} [NormedAddCommGroup E]

private theorem batchSmooth_one_le (x : E) : (1 : ℝ) ≤ 1 + ‖x‖ := by
  linarith [norm_nonneg x]

private theorem batchSmooth_pow_le {x : E} {a b : ℕ} (h : a ≤ b) :
    (1 + ‖x‖) ^ a ≤ (1 + ‖x‖) ^ b :=
  pow_le_pow_right₀ (batchSmooth_one_le x) h

private theorem batchSmooth_pg_nonneg {F : Type*} [NormedAddCommGroup F] {f : E → F} {C : ℝ} {k : ℕ}
    (h : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k) : 0 ≤ C := by
  have := h 0
  simp only [norm_zero, add_zero, one_pow, mul_one] at this
  exact (norm_nonneg _).trans this

private theorem batchSmooth_pg_add {F : Type*} [NormedAddCommGroup F] {f g : E → F}
    (hf : PolyGrowth f) (hg : PolyGrowth g) : PolyGrowth (fun x => f x + g x) := by
  obtain ⟨C₁, k₁, h₁⟩ := hf
  obtain ⟨C₂, k₂, h₂⟩ := hg
  have c1 := batchSmooth_pg_nonneg h₁
  have c2 := batchSmooth_pg_nonneg h₂
  refine ⟨C₁ + C₂, max k₁ k₂, fun x => ?_⟩
  calc ‖f x + g x‖ ≤ ‖f x‖ + ‖g x‖ := norm_add_le _ _
    _ ≤ C₁ * (1 + ‖x‖) ^ k₁ + C₂ * (1 + ‖x‖) ^ k₂ := add_le_add (h₁ x) (h₂ x)
    _ ≤ C₁ * (1 + ‖x‖) ^ max k₁ k₂ + C₂ * (1 + ‖x‖) ^ max k₁ k₂ :=
        add_le_add (mul_le_mul_of_nonneg_left (batchSmooth_pow_le (le_max_left _ _)) c1)
          (mul_le_mul_of_nonneg_left (batchSmooth_pow_le (le_max_right _ _)) c2)
    _ = (C₁ + C₂) * (1 + ‖x‖) ^ max k₁ k₂ := by ring

private theorem batchSmooth_pg_mul {A : Type*} [NormedRing A] {f g : E → A}
    (hf : PolyGrowth f) (hg : PolyGrowth g) : PolyGrowth (fun x => f x * g x) := by
  obtain ⟨C₁, k₁, h₁⟩ := hf
  obtain ⟨C₂, k₂, h₂⟩ := hg
  have c1 := batchSmooth_pg_nonneg h₁
  refine ⟨C₁ * C₂, k₁ + k₂, fun x => ?_⟩
  calc ‖f x * g x‖ ≤ ‖f x‖ * ‖g x‖ := norm_mul_le _ _
    _ ≤ (C₁ * (1 + ‖x‖) ^ k₁) * (C₂ * (1 + ‖x‖) ^ k₂) :=
        mul_le_mul (h₁ x) (h₂ x) (norm_nonneg _) (by positivity)
    _ = C₁ * C₂ * (1 + ‖x‖) ^ (k₁ + k₂) := by ring

private theorem batchSmooth_pg_const {F : Type*} [NormedAddCommGroup F] (c : F) :
    PolyGrowth (fun _ : E => c) :=
  ⟨‖c‖, 0, fun x => by simp⟩

private theorem batchSmooth_pg_of_le {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    {f : E → F} {u : E → G} (hu : PolyGrowth u) (h : ∀ x, ‖f x‖ ≤ ‖u x‖) : PolyGrowth f := by
  obtain ⟨C, k, hC⟩ := hu
  exact ⟨C, k, fun x => (h x).trans (hC x)⟩

private theorem batchSmooth_pg_norm {F : Type*} [NormedAddCommGroup F] {f : E → F}
    (hf : PolyGrowth f) : PolyGrowth (fun x => ‖f x‖) := by
  obtain ⟨C, k, hC⟩ := hf
  exact ⟨C, k, fun x => by simpa using hC x⟩

private theorem batchSmooth_pg_clm {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → F} (L : F →L[ℝ] G) (hf : PolyGrowth f) :
    PolyGrowth (fun x => L (f x)) := by
  obtain ⟨C, k, hC⟩ := hf
  refine ⟨‖L‖ * C, k, fun x => ?_⟩
  calc ‖L (f x)‖ ≤ ‖L‖ * ‖f x‖ := L.le_opNorm _
    _ ≤ ‖L‖ * (C * (1 + ‖x‖) ^ k) := by gcongr; exact hC x
    _ = ‖L‖ * C * (1 + ‖x‖) ^ k := by ring

end Toolkit

/-- `C¹` with polynomially bounded values and derivative. -/
private def batchSmooth_PB {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) : Prop :=
  ContDiff ℝ 1 f ∧ PolyGrowth f ∧ PolyGrowth (fderiv ℝ f)

section Closure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem batchSmooth_PB_const (c : F) : batchSmooth_PB (fun _ : E => c) := by
  refine ⟨contDiff_const, batchSmooth_pg_const c, ?_⟩
  have : fderiv ℝ (fun _ : E => c) = fun _ => 0 := by
    funext x
    exact fderiv_const_apply c
  rw [this]
  exact batchSmooth_pg_const _

private theorem batchSmooth_PB_clm (L : E →L[ℝ] F) : batchSmooth_PB (fun x => L x) := by
  refine ⟨L.contDiff, ⟨‖L‖, 1, fun x => ?_⟩, ?_⟩
  · calc ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
      _ ≤ ‖L‖ * (1 + ‖x‖) ^ 1 := by
        rw [pow_one]
        exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
  · have : fderiv ℝ (fun x => L x) = fun _ => L := by
      funext x
      exact L.fderiv
    rw [this]
    exact batchSmooth_pg_const _

private theorem batchSmooth_PB_add {f g : E → F} (hf : batchSmooth_PB f)
    (hg : batchSmooth_PB g) : batchSmooth_PB (fun x => f x + g x) := by
  refine ⟨hf.1.add hg.1, batchSmooth_pg_add hf.2.1 hg.2.1, ?_⟩
  have : fderiv ℝ (fun x => f x + g x) = fun x => fderiv ℝ f x + fderiv ℝ g x := by
    funext x
    exact fderiv_add (hf.1.differentiable one_ne_zero x) (hg.1.differentiable one_ne_zero x)
  rw [this]
  exact batchSmooth_pg_add hf.2.2 hg.2.2

private theorem batchSmooth_PB_neg {f : E → F} (hf : batchSmooth_PB f) :
    batchSmooth_PB (fun x => -f x) := by
  refine ⟨hf.1.neg, ?_, ?_⟩
  · obtain ⟨C, k, h⟩ := hf.2.1
    exact ⟨C, k, fun x => by simpa using h x⟩
  · have : fderiv ℝ (fun x => -f x) = fun x => -fderiv ℝ f x := by
      funext x
      exact fderiv_neg
    rw [this]
    obtain ⟨C, k, h⟩ := hf.2.2
    exact ⟨C, k, fun x => by simpa using h x⟩

private theorem batchSmooth_PB_sub {f g : E → F} (hf : batchSmooth_PB f)
    (hg : batchSmooth_PB g) : batchSmooth_PB (fun x => f x - g x) := by
  have := batchSmooth_PB_add hf (batchSmooth_PB_neg hg)
  simpa only [sub_eq_add_neg] using this

private theorem batchSmooth_PB_comp_clm {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) {f : E → F} (hf : batchSmooth_PB f) :
    batchSmooth_PB (fun x => L (f x)) := by
  refine ⟨L.contDiff.comp hf.1, batchSmooth_pg_clm L hf.2.1, ?_⟩
  have : fderiv ℝ (fun x => L (f x)) = fun x => L.comp (fderiv ℝ f x) := by
    funext x
    exact (L.hasFDerivAt.comp x (hf.1.differentiable one_ne_zero x).hasFDerivAt).fderiv
  rw [this]
  obtain ⟨C, k, h⟩ := hf.2.2
  refine ⟨‖L‖ * C, k, fun x => ?_⟩
  calc ‖L.comp (fderiv ℝ f x)‖ ≤ ‖L‖ * ‖fderiv ℝ f x‖ := L.opNorm_comp_le _
    _ ≤ ‖L‖ * (C * (1 + ‖x‖) ^ k) := by gcongr; exact h x
    _ = ‖L‖ * C * (1 + ‖x‖) ^ k := by ring

private theorem batchSmooth_norm_mul_le {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (a b : A) (a' b' : E →L[ℝ] A) :
    ‖a • b' + MulOpposite.op b • a'‖ ≤ ‖a‖ * ‖b'‖ + ‖a'‖ * ‖b‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  simp only [add_apply, smul_apply,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  calc ‖a * b' v + a' v * b‖ ≤ ‖a * b' v‖ + ‖a' v * b‖ := norm_add_le _ _
    _ ≤ ‖a‖ * ‖b' v‖ + ‖a' v‖ * ‖b‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ ‖a‖ * (‖b'‖ * ‖v‖) + (‖a'‖ * ‖v‖) * ‖b‖ := by
        gcongr
        · exact b'.le_opNorm v
        · exact a'.le_opNorm v
    _ = (‖a‖ * ‖b'‖ + ‖a'‖ * ‖b‖) * ‖v‖ := by ring

private theorem batchSmooth_PB_mul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] {f g : E → A}
    (hf : batchSmooth_PB f) (hg : batchSmooth_PB g) :
    batchSmooth_PB (fun x => f x * g x) := by
  refine ⟨hf.1.mul hg.1, batchSmooth_pg_mul hf.2.1 hg.2.1, ?_⟩
  have hd : ∀ x, HasFDerivAt (fun y => f y * g y)
      (f x • fderiv ℝ g x + MulOpposite.op (g x) • fderiv ℝ f x) x := fun x =>
    (hf.1.differentiable one_ne_zero x).hasFDerivAt.mul'
      (hg.1.differentiable one_ne_zero x).hasFDerivAt
  have : fderiv ℝ (fun x => f x * g x) =
      fun x => f x • fderiv ℝ g x + MulOpposite.op (g x) • fderiv ℝ f x := by
    funext x
    exact (hd x).fderiv
  rw [this]
  refine batchSmooth_pg_of_le (u := fun x => ‖f x‖ * ‖fderiv ℝ g x‖ + ‖fderiv ℝ f x‖ * ‖g x‖)
    (batchSmooth_pg_add (batchSmooth_pg_mul (batchSmooth_pg_norm hf.2.1)
      (batchSmooth_pg_norm hg.2.2)) (batchSmooth_pg_mul (batchSmooth_pg_norm hf.2.2)
      (batchSmooth_pg_norm hg.2.1))) fun x => ?_
  exact (batchSmooth_norm_mul_le _ _ _ _).trans (by rw [Real.norm_eq_abs]; exact le_abs_self _)

private theorem batchSmooth_PB_prodMk {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {g : E → G} (hf : batchSmooth_PB f) (hg : batchSmooth_PB g) :
    batchSmooth_PB (fun x => (f x, g x)) := by
  refine ⟨hf.1.prodMk hg.1, ?_, ?_⟩
  · refine batchSmooth_pg_of_le (u := fun x => ‖f x‖ + ‖g x‖)
      (batchSmooth_pg_add (batchSmooth_pg_norm hf.2.1) (batchSmooth_pg_norm hg.2.1)) fun x => ?_
    rw [Prod.norm_def, Real.norm_eq_abs]
    exact (max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)).trans (le_abs_self _)
  · have : fderiv ℝ (fun x => (f x, g x)) = fun x => (fderiv ℝ f x).prod (fderiv ℝ g x) := by
      funext x
      exact ((hf.1.differentiable one_ne_zero x).hasFDerivAt.prodMk
        (hg.1.differentiable one_ne_zero x).hasFDerivAt).fderiv
    rw [this]
    refine batchSmooth_pg_of_le (u := fun x => ‖fderiv ℝ f x‖ + ‖fderiv ℝ g x‖)
      (batchSmooth_pg_add (batchSmooth_pg_norm hf.2.2) (batchSmooth_pg_norm hg.2.2)) fun x => ?_
    rw [ContinuousLinearMap.opNorm_prod, Prod.norm_def, Real.norm_eq_abs]
    exact (max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)).trans (le_abs_self _)

private theorem batchSmooth_PB_sum {ι : Type*} (s : Finset ι) {f : ι → E → F}
    (h : ∀ i ∈ s, batchSmooth_PB (f i)) : batchSmooth_PB (fun x => ∑ i ∈ s, f i x) := by
  induction s using Finset.induction_on with
  | empty => simpa using batchSmooth_PB_const (0 : F)
  | insert a s ha ih =>
    have h1 := batchSmooth_PB_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa only [Finset.sum_insert ha] using h1

private theorem batchSmooth_PB_prod {ι : Type*} (s : Finset ι) {f : ι → E → ℂ}
    (h : ∀ i ∈ s, batchSmooth_PB (f i)) : batchSmooth_PB (fun x => ∏ i ∈ s, f i x) := by
  induction s using Finset.induction_on with
  | empty => simpa using batchSmooth_PB_const (1 : ℂ)
  | insert a s ha ih =>
    have h1 := batchSmooth_PB_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa only [Finset.prod_insert ha] using h1

end Closure

section Matrices

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The conjugate transpose as a real-linear map on square matrices. -/
private def batchSmooth_conjTransposeCLM (n : Type*) [Fintype n] [DecidableEq n] :
    Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => Aᴴ
      map_add' := fun A B => Matrix.conjTranspose_add A B
      map_smul' := fun c A => by
        simp only [Matrix.conjTranspose_smul, RingHom.id_apply]
        rw [star_trivial] }

private theorem batchSmooth_PB_conjTranspose {f : E → Matrix n n ℂ} (hf : batchSmooth_PB f) :
    batchSmooth_PB (fun x => (f x)ᴴ) :=
  batchSmooth_PB_comp_clm (batchSmooth_conjTransposeCLM n) hf

private theorem batchSmooth_PB_entry {f : E → Matrix n n ℂ} (hf : batchSmooth_PB f) (i j : n) :
    batchSmooth_PB (fun x => f x i j) :=
  batchSmooth_PB_comp_clm (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)) hf

private theorem batchSmooth_PB_det {f : E → Matrix n n ℂ} (hf : batchSmooth_PB f) :
    batchSmooth_PB (fun x => (f x).det) := by
  simp only [Matrix.det_apply']
  refine batchSmooth_PB_sum _ fun σ _ => batchSmooth_PB_mul (batchSmooth_PB_const _) ?_
  exact batchSmooth_PB_prod _ fun i _ => batchSmooth_PB_entry hf _ _

private theorem batchSmooth_PB_inv {f : E → Matrix n n ℂ} (hf : batchSmooth_PB f)
    (hu : ∀ x, IsUnit (f x)) (hinv : PolyGrowth (fun x => (f x)⁻¹)) :
    batchSmooth_PB (fun x => (f x)⁻¹) := by
  have hd : ∀ x, HasFDerivAt (fun x => (f x)⁻¹)
      ((-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (f x)⁻¹ (f x)⁻¹).comp
        (fderiv ℝ f x)) x := by
    intro x
    obtain ⟨u, hux⟩ := hu x
    have h1 : HasFDerivAt Ring.inverse
        (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) ↑u⁻¹ ↑u⁻¹) (f x) :=
      hux ▸ hasFDerivAt_ringInverse (𝕜 := ℝ) u
    have e1 : ((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ) = (f x)⁻¹ := by
      rw [Matrix.nonsing_inv_eq_ringInverse, ← hux, Ring.inverse_unit]
    rw [e1] at h1
    have h2 := h1.comp x (hf.1.differentiable one_ne_zero x).hasFDerivAt
    simpa only [Function.comp_def, Matrix.nonsing_inv_eq_ringInverse] using h2
  have hcd : ContDiff ℝ 1 (fun x => (f x)⁻¹) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    obtain ⟨u, hux⟩ := hu x
    have h1 : ContDiffAt ℝ 1 Ring.inverse (f x) := hux ▸ contDiffAt_ringInverse ℝ u
    simp only [Matrix.nonsing_inv_eq_ringInverse]
    exact h1.comp x hf.1.contDiffAt
  refine ⟨hcd, hinv, ?_⟩
  have : fderiv ℝ (fun x => (f x)⁻¹) = fun x =>
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (f x)⁻¹ (f x)⁻¹).comp
        (fderiv ℝ f x) := by
    funext x
    exact (hd x).fderiv
  rw [this]
  refine batchSmooth_pg_of_le (u := fun x => ‖(f x)⁻¹‖ * ‖(f x)⁻¹‖ * ‖fderiv ℝ f x‖)
    (batchSmooth_pg_mul (batchSmooth_pg_mul (batchSmooth_pg_norm hinv)
      (batchSmooth_pg_norm hinv)) (batchSmooth_pg_norm hf.2.2)) fun x => ?_
  refine (ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_).trans
    (le_of_eq (Real.norm_of_nonneg (by positivity)).symm)
  simp only [ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, norm_neg]
  calc ‖(f x)⁻¹ * fderiv ℝ f x v * (f x)⁻¹‖
      ≤ ‖(f x)⁻¹ * fderiv ℝ f x v‖ * ‖(f x)⁻¹‖ := norm_mul_le _ _
    _ ≤ ‖(f x)⁻¹‖ * ‖fderiv ℝ f x v‖ * ‖(f x)⁻¹‖ := by
        gcongr; exact norm_mul_le _ _
    _ ≤ ‖(f x)⁻¹‖ * (‖fderiv ℝ f x‖ * ‖v‖) * ‖(f x)⁻¹‖ := by
        gcongr; exact (fderiv ℝ f x).le_opNorm v
    _ = ‖(f x)⁻¹‖ * ‖(f x)⁻¹‖ * ‖fderiv ℝ f x‖ * ‖v‖ := by ring

/-- `x ↦ log ‖d x‖` is `C¹` with polynomially bounded derivative when `d` is, `d` does not vanish
and `d⁻¹` grows polynomially. -/
private theorem batchSmooth_logNorm {d : E → ℂ} (hd : batchSmooth_PB d) (h0 : ∀ x, d x ≠ 0)
    (hinv : PolyGrowth (fun x => (d x)⁻¹)) :
    ContDiff ℝ 1 (fun x => Real.log ‖d x‖) ∧ PolyGrowth (fderiv ℝ (fun x => Real.log ‖d x‖)) := by
  have hpos : ∀ x, ‖d x‖ ≠ 0 := fun x => norm_ne_zero_iff.mpr (h0 x)
  refine ⟨(ContDiff.norm ℝ hd.1 h0).log hpos, ?_⟩
  have hfd : ∀ x, HasFDerivAt (fun x => Real.log ‖d x‖)
      ((‖d x‖)⁻¹ • ((fderiv ℝ (fun z : ℂ => ‖z‖) (d x)).comp (fderiv ℝ d x))) x := by
    intro x
    have hdn : DifferentiableAt ℝ (fun z : ℂ => ‖z‖) (d x) :=
      differentiableAt_id.norm ℝ (h0 x)
    have h1 : HasFDerivAt (fun x => ‖d x‖)
        ((fderiv ℝ (fun z : ℂ => ‖z‖) (d x)).comp (fderiv ℝ d x)) x :=
      hdn.hasFDerivAt.comp x (hd.1.differentiable one_ne_zero x).hasFDerivAt
    exact h1.log (hpos x)
  have : fderiv ℝ (fun x => Real.log ‖d x‖) = fun x =>
      (‖d x‖)⁻¹ • ((fderiv ℝ (fun z : ℂ => ‖z‖) (d x)).comp (fderiv ℝ d x)) := by
    funext x
    exact (hfd x).fderiv
  rw [this]
  refine batchSmooth_pg_of_le (u := fun x => ‖(d x)⁻¹‖ * ‖fderiv ℝ d x‖)
    (batchSmooth_pg_mul (batchSmooth_pg_norm hinv) (batchSmooth_pg_norm hd.2.2)) fun x => ?_
  have hlip : ‖fderiv ℝ (fun z : ℂ => ‖z‖) (d x)‖ ≤ 1 := by
    simpa using norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_one_norm (E := ℂ)) (x₀ := d x)
  rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ‖d x‖⁻¹),
    Real.norm_of_nonneg (by positivity : 0 ≤ ‖(d x)⁻¹‖ * ‖fderiv ℝ d x‖), norm_inv]
  calc ‖d x‖⁻¹ * ‖(fderiv ℝ (fun z : ℂ => ‖z‖) (d x)).comp (fderiv ℝ d x)‖
      ≤ ‖d x‖⁻¹ * (‖fderiv ℝ (fun z : ℂ => ‖z‖) (d x)‖ * ‖fderiv ℝ d x‖) := by
        gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖d x‖⁻¹ * (1 * ‖fderiv ℝ d x‖) := by gcongr
    _ = _ := by rw [one_mul]

end Matrices

section Gram

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped ComplexOrder in
/-- The Gram matrix `P T* T P + 1 - P` of an invertible `T` and an orthogonal projection `P` is
invertible. -/
private theorem batchSmooth_isUnit_gram {T P : Matrix ι ι ℂ}
    (hT : IsUnit T) (hP : Pᴴ = P) (hPP : P * P = P) :
    IsUnit (P * Tᴴ * T * P + (1 - P)) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  have hker : ∀ z : ι → ℂ, (P * Tᴴ * T * P + (1 - P)) *ᵥ z = 0 → z = 0 := by
    intro z hz
    have h1 : P *ᵥ ((P * Tᴴ * T * P + (1 - P)) *ᵥ z) = 0 := by rw [hz, Matrix.mulVec_zero]
    have h2 : P * (P * Tᴴ * T * P + (1 - P)) = P * Tᴴ * T * P := by
      simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hPP]
      abel
    rw [Matrix.mulVec_mulVec, h2] at h1
    set w : ι → ℂ := P *ᵥ z with hw
    have hPw : P *ᵥ w = w := by rw [hw, Matrix.mulVec_mulVec, hPP]
    have h3 : P *ᵥ (Tᴴ *ᵥ (T *ᵥ w)) = 0 := by
      rw [← h1, hw]; simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    have hs : star w = star w ᵥ* P := by
      conv_lhs => rw [← hPw]
      rw [Matrix.star_mulVec, hP]
    have h4 : star (T *ᵥ w) ⬝ᵥ (T *ᵥ w) = 0 := by
      calc star (T *ᵥ w) ⬝ᵥ (T *ᵥ w) = star w ⬝ᵥ (Tᴴ *ᵥ (T *ᵥ w)) := by
            rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
        _ = (star w ᵥ* P) ⬝ᵥ (Tᴴ *ᵥ (T *ᵥ w)) := by rw [← hs]
        _ = star w ⬝ᵥ (P *ᵥ (Tᴴ *ᵥ (T *ᵥ w))) := (Matrix.dotProduct_mulVec _ _ _).symm
        _ = 0 := by rw [h3, dotProduct_zero]
    have h5 : T *ᵥ w = 0 := dotProduct_star_self_eq_zero.mp h4
    have h6 : w = 0 := by
      obtain ⟨U, rfl⟩ := hT
      have := congrArg (fun v => (↑U⁻¹ : Matrix ι ι ℂ) *ᵥ v) h5
      simpa [Matrix.mulVec_mulVec] using this
    have h7 : (1 - P) *ᵥ z = 0 := by
      have : (P * Tᴴ * T * P + (1 - P)) *ᵥ z = (P * Tᴴ * T * P) *ᵥ z + (1 - P) *ᵥ z :=
        Matrix.add_mulVec _ _ _
      rw [hz, h1, zero_add] at this
      exact this.symm
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← hw, h6, sub_zero] at h7
    exact h7
  intro x y hxy
  have := hker (x - y) (by rw [Matrix.mulVec_sub, hxy, sub_self])
  exact sub_eq_zero.mp this

/-- `‖(P T* T P + 1 - P)⁻¹‖ ≤ ‖T⁻¹‖² + ‖1 - P‖` for invertible `T` and an orthogonal projection
`P`. -/
private theorem batchSmooth_norm_gram_inv_le {T P : Matrix ι ι ℂ}
    (hT : IsUnit T) (hP : Pᴴ = P) (hPP : P * P = P) :
    ‖(P * Tᴴ * T * P + (1 - P))⁻¹‖ ≤ ‖T⁻¹‖ * ‖T⁻¹‖ + ‖1 - P‖ := by
  set G : Matrix ι ι ℂ := P * Tᴴ * T * P + (1 - P) with hG
  have hGu : IsUnit G := batchSmooth_isUnit_gram hT hP hPP
  have hGd : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hGu
  have hGi1 : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hGd
  have hGi2 : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hGd
  have hGH : Gᴴ = G := by
    rw [hG, Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hP]
    simp only [Matrix.mul_assoc]
  have hPG : P * G = P * Tᴴ * T * P := by
    rw [hG]
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hPP]
    abel
  have hGP : G * P = P * Tᴴ * T * P := by
    rw [hG]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hPP]
    abel
  have hGQ : G * (1 - P) = 1 - P := by
    rw [hG]
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc, hPP]
    abel
  have hcomm : P * G⁻¹ = G⁻¹ * P := by
    calc P * G⁻¹ = (G⁻¹ * G) * P * G⁻¹ := by rw [hGi1, Matrix.one_mul]
      _ = G⁻¹ * (G * P) * G⁻¹ := by simp only [Matrix.mul_assoc]
      _ = G⁻¹ * (P * G) * G⁻¹ := by rw [hGP, hPG]
      _ = G⁻¹ * P * (G * G⁻¹) := by simp only [Matrix.mul_assoc]
      _ = G⁻¹ * P := by rw [hGi2, Matrix.mul_one]
  have hGiH : (G⁻¹)ᴴ = G⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hGH]
  set N : Matrix ι ι ℂ := G⁻¹ * P with hN
  have hNH : Nᴴ = N := by
    rw [hN, Matrix.conjTranspose_mul, hP, hGiH, hcomm]
  have hdecomp : G⁻¹ = N + (1 - P) := by
    have : G⁻¹ * (1 - P) = 1 - P := by
      calc G⁻¹ * (1 - P) = G⁻¹ * (G * (1 - P)) := by rw [hGQ]
        _ = (G⁻¹ * G) * (1 - P) := by rw [Matrix.mul_assoc]
        _ = 1 - P := by rw [hGi1, Matrix.one_mul]
    calc G⁻¹ = G⁻¹ * P + G⁻¹ * (1 - P) := by rw [← Matrix.mul_add]; simp
      _ = N + (1 - P) := by rw [this]
  have hNTN : N * Tᴴ * T * N = N := by
    calc N * Tᴴ * T * N = (G⁻¹ * P) * Tᴴ * T * (P * G⁻¹) := by rw [hcomm]
      _ = G⁻¹ * (P * Tᴴ * T * P) * G⁻¹ := by simp only [Matrix.mul_assoc]
      _ = G⁻¹ * (G * P) * G⁻¹ := by rw [hGP]
      _ = (G⁻¹ * G) * P * G⁻¹ := by simp only [Matrix.mul_assoc]
      _ = N := by rw [hGi1, Matrix.one_mul, hcomm]
  have hstar : star (T * N) * (T * N) = N := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, hNH]
    simpa only [Matrix.mul_assoc] using hNTN
  have h1 : ‖N‖ = ‖T * N‖ * ‖T * N‖ := by
    rw [← CStarRing.norm_star_mul_self, hstar]
  have hTi : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T ((Matrix.isUnit_iff_isUnit_det T).mp hT)
  have h2 : ‖N‖ ≤ ‖T⁻¹‖ * ‖T * N‖ := by
    calc ‖N‖ = ‖T⁻¹ * (T * N)‖ := by rw [← Matrix.mul_assoc, hTi, Matrix.one_mul]
      _ ≤ ‖T⁻¹‖ * ‖T * N‖ := norm_mul_le _ _
  have h3 : ‖N‖ ≤ ‖T⁻¹‖ * ‖T⁻¹‖ := by
    set a := ‖T * N‖ with ha
    have ha0 : 0 ≤ a := norm_nonneg _
    rcases ha0.eq_or_lt with h0 | hpos
    · rw [h1, ← h0, mul_zero]
      exact mul_self_nonneg _
    · have : a ≤ ‖T⁻¹‖ := by
        rw [h1] at h2
        nlinarith
      rw [h1]
      exact mul_self_le_mul_self ha0 this
  rw [hdecomp]
  exact (norm_add_le _ _).trans (add_le_add h3 le_rfl)

end Gram

section Batch

/-- The block `ω ↦ gueBlock W L ω a` as a real-linear map of the coordinates. -/
private def batchSmooth_gueCLM (W L : ℕ) (a : Fin L) : Ω W L →L[ℝ] Matrix (Fin W) (Fin W) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ω => gueBlock W L ω a
      map_add' := fun ω ω' => by
        ext α β
        simp only [gueBlock, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
        split_ifs <;> push_cast <;> ring
      map_smul' := fun c ω => by
        ext α β
        simp only [gueBlock, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, RingHom.id_apply,
          Complex.real_smul, smul_eq_mul]
        split_ifs <;> push_cast <;> ring }

/-- The map `V ↦ g⁻¹ (diag(1, 0) ⊗ V)`, the input-dependent part of `transferMat g z V`, as a
real-linear map. -/
private def batchSmooth_kronCLM (W : ℕ) (g : ℝ) :
    Matrix (Fin W) (Fin W) ℂ →L[ℝ] Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun V => ((g : ℂ)⁻¹) • ((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V)
      map_add' := fun V V' => by
        ext i j
        simp only [Matrix.smul_apply, Matrix.kroneckerMap_apply, Matrix.add_apply, smul_eq_mul]
        ring
      map_smul' := fun c V => by
        ext i j
        simp only [Matrix.smul_apply, Matrix.kroneckerMap_apply, RingHom.id_apply,
          Complex.real_smul, smul_eq_mul]
        ring }

private theorem batchSmooth_PB_transferProd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : ℕ} (g : ℝ) (z : ℂ) {V : E → ℕ → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ k, batchSmooth_PB (fun x => V x k)) (n : ℕ) :
    batchSmooth_PB (fun x => transferProd g z (V x) n) := by
  induction n with
  | zero =>
    simpa [transferProd] using
      batchSmooth_PB_const (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
  | succ n ih =>
    have h1 : batchSmooth_PB (fun x => transferMat g z (V x n)) := by
      have := batchSmooth_PB_sub (batchSmooth_PB_const (transferFree W z))
        (batchSmooth_PB_comp_clm (batchSmooth_kronCLM W g) (hV n))
      exact this
    exact batchSmooth_PB_mul h1 ih

/-- The batch `T(ω)` of (8.18) [up:eq:transfer-batches] has values and derivative of polynomial
growth in the coordinates `ω`, and is `C¹`. -/
private theorem batchSmooth_PB_batchMat (W : ℕ) (g E : ℝ) (q : ℕ) :
    batchSmooth_PB (fun ω : Ω W q => batchMat W g E q ω) := by
  unfold batchMat
  refine batchSmooth_PB_mul (batchSmooth_PB_mul (batchSmooth_PB_const _) ?_)
    (batchSmooth_PB_const _)
  refine batchSmooth_PB_transferProd g _ (fun k => ?_) q
  by_cases h : k < q
  · simp only [h, dite_true]
    exact batchSmooth_PB_clm (batchSmooth_gueCLM W q ⟨k, h⟩)
  · simp only [h, dite_false]
    exact batchSmooth_PB_const _

end Batch

section Combine

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {W : ℕ}

private theorem batchSmooth_cd1_sub {u v : E → ℝ} (hu : ContDiff ℝ 1 u ∧ PolyGrowth (fderiv ℝ u))
    (hv : ContDiff ℝ 1 v ∧ PolyGrowth (fderiv ℝ v)) :
    ContDiff ℝ 1 (fun x => u x - v x) ∧ PolyGrowth (fderiv ℝ (fun x => u x - v x)) := by
  refine ⟨hu.1.sub hv.1, ?_⟩
  have : fderiv ℝ (fun x => u x - v x) = fun x => fderiv ℝ u x - fderiv ℝ v x := by
    funext x
    exact fderiv_sub (hu.1.differentiable one_ne_zero x) (hv.1.differentiable one_ne_zero x)
  rw [this]
  refine batchSmooth_pg_of_le (u := fun x => ‖fderiv ℝ u x‖ + ‖fderiv ℝ v x‖)
    (batchSmooth_pg_add (batchSmooth_pg_norm hu.2) (batchSmooth_pg_norm hv.2)) fun x => ?_
  rw [Real.norm_of_nonneg (by positivity)]
  exact norm_sub_le _ _

private theorem batchSmooth_cd1_div {u : E → ℝ} (hu : ContDiff ℝ 1 u ∧ PolyGrowth (fderiv ℝ u))
    (c : ℝ) :
    ContDiff ℝ 1 (fun x => u x / c) ∧ PolyGrowth (fderiv ℝ (fun x => u x / c)) := by
  refine ⟨hu.1.div_const c, ?_⟩
  have : fderiv ℝ (fun x => u x / c) = fun x => c⁻¹ • fderiv ℝ u x := by
    funext x
    have e : (fun x => u x / c) = fun x => c⁻¹ * u x := funext fun y => div_eq_inv_mul _ _
    rw [e]
    exact ((hu.1.differentiable one_ne_zero x).hasFDerivAt.const_mul c⁻¹).fderiv
  rw [this]
  obtain ⟨C, k, h⟩ := hu.2
  refine ⟨|c⁻¹| * C, k, fun x => ?_⟩
  rw [norm_smul, Real.norm_eq_abs]
  calc |c⁻¹| * ‖fderiv ℝ u x‖ ≤ |c⁻¹| * (C * (1 + ‖x‖) ^ k) := by gcongr; exact h x
    _ = |c⁻¹| * C * (1 + ‖x‖) ^ k := by ring

/-- Every element of `𝒢` is invertible, as `det T = 1`. -/
private theorem batchSmooth_isUnit_of_mem {T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hT : T ∈ isoGroup W) : IsUnit T :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [hT.2]; exact isUnit_one)

/-- The Gram matrix `P T* T P + 1 - P` of a family `T x ∈ 𝒢` is `C¹` with polynomially bounded
values and derivative, is invertible, and so is its inverse. -/
private theorem batchSmooth_gram {T : E → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hT : batchSmooth_PB T) (hG : ∀ x, T x ∈ isoGroup W)
    {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hP : Pᴴ = P) (hPP : P * P = P) :
    batchSmooth_PB (fun x => P * (T x)ᴴ * T x * P + (1 - P)) ∧
      (∀ x, IsUnit (P * (T x)ᴴ * T x * P + (1 - P))) ∧
      batchSmooth_PB (fun x => (P * (T x)ᴴ * T x * P + (1 - P))⁻¹) := by
  have hgram : batchSmooth_PB (fun x => P * (T x)ᴴ * T x * P + (1 - P)) :=
    batchSmooth_PB_add (batchSmooth_PB_mul (batchSmooth_PB_mul (batchSmooth_PB_mul
      (batchSmooth_PB_const P) (batchSmooth_PB_conjTranspose hT)) hT) (batchSmooth_PB_const P))
      (batchSmooth_PB_const _)
  have hunit : ∀ x, IsUnit (P * (T x)ᴴ * T x * P + (1 - P)) := fun x =>
    batchSmooth_isUnit_gram (batchSmooth_isUnit_of_mem (hG x)) hP hPP
  refine ⟨hgram, hunit, batchSmooth_PB_inv hgram hunit ?_⟩
  refine batchSmooth_pg_of_le (u := fun x => ‖T x‖ * ‖T x‖ + ‖1 - P‖)
    (batchSmooth_pg_add (batchSmooth_pg_mul (batchSmooth_pg_norm hT.2.1)
      (batchSmooth_pg_norm hT.2.1)) (batchSmooth_pg_const _)) fun x => ?_
  have h := batchSmooth_norm_gram_inv_le (batchSmooth_isUnit_of_mem (hG x)) hP hPP
  rw [norm_inv_eq_of_isoJ (hG x).1] at h
  rw [Real.norm_of_nonneg (by positivity)]
  exact h

/-- `ω ↦ flagProj (T ω) P` is `C¹` with polynomially bounded values and derivative. -/
private theorem batchSmooth_PB_flagProj {T : E → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hT : batchSmooth_PB T) (hG : ∀ x, T x ∈ isoGroup W)
    {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hP : Pᴴ = P) (hPP : P * P = P) :
    batchSmooth_PB (fun x => flagProj (T x) P) := by
  obtain ⟨-, -, hinv⟩ := batchSmooth_gram hT hG hP hPP
  unfold flagProj
  exact batchSmooth_PB_mul (batchSmooth_PB_mul (batchSmooth_PB_mul (batchSmooth_PB_mul hT
    (batchSmooth_PB_const P)) hinv) (batchSmooth_PB_const P)) (batchSmooth_PB_conjTranspose hT)

/-- `ω ↦ log vol(T(ω)|_{ran P})` is `C¹` with polynomially bounded derivative. -/
private theorem batchSmooth_logVol {T : E → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hT : batchSmooth_PB T) (hG : ∀ x, T x ∈ isoGroup W)
    {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hP : Pᴴ = P) (hPP : P * P = P) :
    ContDiff ℝ 1 (fun x => logVol (T x) P) ∧ PolyGrowth (fderiv ℝ (fun x => logVol (T x) P)) := by
  obtain ⟨hgram, hunit, hinv⟩ := batchSmooth_gram hT hG hP hPP
  have hdet : batchSmooth_PB (fun x => (P * (T x)ᴴ * T x * P + (1 - P)).det) :=
    batchSmooth_PB_det hgram
  have h0 : ∀ x, (P * (T x)ᴴ * T x * P + (1 - P)).det ≠ 0 := fun x =>
    ((Matrix.isUnit_iff_isUnit_det _).mp (hunit x)).ne_zero
  have hdinv : PolyGrowth (fun x => ((P * (T x)ᴴ * T x * P + (1 - P)).det)⁻¹) := by
    have := (batchSmooth_PB_det hinv).2.1
    simpa only [Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] using this
  exact batchSmooth_cd1_div (batchSmooth_logNorm hdet h0 hdinv) 2

end Combine

/-- `ω ↦ c(T(ω); U, Y)` ((8.17) [eq:c-volume-cocycle]) is `C¹` with polynomially bounded
derivative. -/
theorem contDiff_volCocycle_batchMat (W : ℕ) (g E : ℝ) (q : ℕ) (x : IsoFlag W) :
    ContDiff ℝ 1 (fun ω : Ω W q => volCocycle (batchMat W g E q ω) x) ∧
      PolyGrowth (fderiv ℝ (fun ω : Ω W q => volCocycle (batchMat W g E q ω) x)) := by
  have hT := batchSmooth_PB_batchMat W g E q
  have hmem := batchMat_mem_isoGroup W g E q
  obtain ⟨⟨hUh, hUU, -, -⟩, hYh, hYY, -, -, -⟩ := x.2
  exact batchSmooth_cd1_sub (batchSmooth_logVol hT hmem hYh hYY)
    (batchSmooth_logVol hT hmem hUh hUU)

/-- `ω ↦ (P_{T(ω)U}, P_{T(ω)Y})` is `C¹` with polynomially bounded derivative. -/
theorem contDiff_flagAct_batchMat (W : ℕ) (g E : ℝ) (q : ℕ) (x : IsoFlag W) :
    ContDiff ℝ 1 (fun ω : Ω W q => ((flagAct (batchMat W g E q ω) x : IsoFlag W) :
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) ∧
    PolyGrowth (fderiv ℝ (fun ω : Ω W q => ((flagAct (batchMat W g E q ω) x : IsoFlag W) :
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ))) := by
  have hT := batchSmooth_PB_batchMat W g E q
  have hmem := batchMat_mem_isoGroup W g E q
  obtain ⟨⟨hUh, hUU, -, -⟩, hYh, hYY, -, -, -⟩ := x.2
  have heq : (fun ω : Ω W q => ((flagAct (batchMat W g E q ω) x : IsoFlag W) :
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) =
      fun ω => (flagProj (batchMat W g E q ω) x.1.1, flagProj (batchMat W g E q ω) x.1.2) :=
    funext fun ω => flagAct_coe (hmem ω).1 x
  rw [heq]
  have h := batchSmooth_PB_prodMk (batchSmooth_PB_flagProj hT hmem hUh hUU)
    (batchSmooth_PB_flagProj hT hmem hYh hYY)
  exact ⟨h.1, h.2.2⟩

end LSBA
