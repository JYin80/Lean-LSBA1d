import Mathlib

/-!
# The bounded `C^{1,2}` class and the coordinate generator

The class `HeatClass` of time-dependent functions on `ℝ^ι` used by the generator form of
Itô's formula; the generator `𝒢 = ∂_u + (σ²/2) Δ` and the carré du champ `Γ` in coordinates, the
generator forms of (5.4) [fo:eq:ito] and (5.9) [gc:eq:bracket]; closure of the class under the
operations used for loop polynomials and cutoffs; the chain rule for `φ ∘ X`.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

set_option maxSynthPendingDepth 3

namespace LSBA

/-- The bounded `C^{1,2}` class of the generator identity: `F`, `∂_u F`, `D_x F`, `D_x² F` exist,
are jointly continuous and bounded on `(a,b) × ℝ^ι`. -/
structure HeatClass {ι : Type*} [Fintype ι] (F : ℝ → (ι → ℝ) → ℂ) (a b : ℝ) : Prop where
  cont : ContinuousOn (Function.uncurry F) (Set.Ioo a b ×ˢ Set.univ)
  bdd : ∃ C : ℝ, ∀ r ∈ Set.Ioo a b, ∀ x, ‖F r x‖ ≤ C
  du : ∃ Fu : ℝ → (ι → ℝ) → ℂ,
    (∀ r ∈ Set.Ioo a b, ∀ x, HasDerivAt (fun r' => F r' x) (Fu r x) r) ∧
    ContinuousOn (Function.uncurry Fu) (Set.Ioo a b ×ˢ Set.univ) ∧
    ∃ C : ℝ, ∀ r ∈ Set.Ioo a b, ∀ x, ‖Fu r x‖ ≤ C
  dx : ∃ (DF : ℝ → (ι → ℝ) → ((ι → ℝ) →L[ℝ] ℂ))
      (D2F : ℝ → (ι → ℝ) → ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℂ)),
    (∀ r ∈ Set.Ioo a b, ∀ x, HasFDerivAt (F r) (DF r x) x) ∧
    (∀ r ∈ Set.Ioo a b, ∀ x, HasFDerivAt (DF r) (D2F r x) x) ∧
    ContinuousOn (Function.uncurry DF) (Set.Ioo a b ×ˢ Set.univ) ∧
    ContinuousOn (Function.uncurry D2F) (Set.Ioo a b ×ˢ Set.univ) ∧
    ∃ C : ℝ, ∀ r ∈ Set.Ioo a b, ∀ x, ‖DF r x‖ ≤ C ∧ ‖D2F r x‖ ≤ C

/-- Generator `∂_u + (σ²/2) Δ` in coordinates, the generator form of (5.4) [fo:eq:ito]. -/
def coordGen {ι : Type*} [Fintype ι] (σ2 : ℝ) (F : ℝ → (ι → ℝ) → ℂ) (u : ℝ) (y : ι → ℝ) : ℂ :=
  deriv (fun r => F r y) u +
    ((σ2 / 2 : ℝ) : ℂ) * ∑ i, iteratedDeriv 2 (fun e : ℝ => F u (y + e • Pi.single i 1)) 0

/-- Carré du champ `Γ(F₁, F₂) = σ² Σ_i ∂_i F₁ conj(∂_i F₂)`, the generator form of the bracket
(5.9) [gc:eq:bracket]. -/
def coordGamma {ι : Type*} [Fintype ι] (σ2 : ℝ) (F₁ F₂ : (ι → ℝ) → ℂ) (y : ι → ℝ) : ℂ :=
  (σ2 : ℂ) * ∑ i, deriv (fun e : ℝ => F₁ (y + e • Pi.single i 1)) 0 *
    star (deriv (fun e : ℝ => F₂ (y + e • Pi.single i 1)) 0)

theorem HeatClass.add {ι : Type*} [Fintype ι] {F₁ F₂ : ℝ → (ι → ℝ) → ℂ} {a b : ℝ}
    (h₁ : HeatClass F₁ a b) (h₂ : HeatClass F₂ a b) :
    HeatClass (fun r y => F₁ r y + F₂ r y) a b := by
  obtain ⟨hc₁, ⟨C₁, hC₁⟩, ⟨Fu₁, hu₁, hcu₁, Cu₁, hCu₁⟩,
    ⟨DF₁, D2F₁, hD₁, hD2₁, hcD₁, hcD2₁, Cd₁, hCd₁⟩⟩ := h₁
  obtain ⟨hc₂, ⟨C₂, hC₂⟩, ⟨Fu₂, hu₂, hcu₂, Cu₂, hCu₂⟩,
    ⟨DF₂, D2F₂, hD₂, hD2₂, hcD₂, hcD2₂, Cd₂, hCd₂⟩⟩ := h₂
  refine ⟨hc₁.add hc₂, ⟨C₁ + C₂, fun r hr x => ?_⟩,
    ⟨fun r x => Fu₁ r x + Fu₂ r x, fun r hr x => (hu₁ r hr x).add (hu₂ r hr x),
      hcu₁.add hcu₂, Cu₁ + Cu₂, fun r hr x => ?_⟩,
    ⟨fun r x => DF₁ r x + DF₂ r x, fun r x => D2F₁ r x + D2F₂ r x,
      fun r hr x => (hD₁ r hr x).add (hD₂ r hr x), fun r hr x => (hD2₁ r hr x).add (hD2₂ r hr x),
      hcD₁.add hcD₂, hcD2₁.add hcD2₂, Cd₁ + Cd₂, fun r hr x => ⟨?_, ?_⟩⟩⟩
  · exact (norm_add_le (F₁ r x) (F₂ r x)).trans (add_le_add (hC₁ r hr x) (hC₂ r hr x))
  · exact (norm_add_le (Fu₁ r x) (Fu₂ r x)).trans (add_le_add (hCu₁ r hr x) (hCu₂ r hr x))
  · exact (norm_add_le (DF₁ r x) (DF₂ r x)).trans (add_le_add (hCd₁ r hr x).1 (hCd₂ r hr x).1)
  · exact (norm_add_le (D2F₁ r x) (D2F₂ r x)).trans (add_le_add (hCd₁ r hr x).2 (hCd₂ r hr x).2)

/-- The bilinear map `(c, f) ↦ (v ↦ c v • f)` on `(E →L[ℝ] ℂ)²` is bounded. -/
private theorem heat_smulRight_bdd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    IsBoundedBilinearMap ℝ (fun p : (E →L[ℝ] ℂ) × (E →L[ℝ] ℂ) => p.1.smulRight p.2) where
  add_left c₁ c₂ f := by
    ext v w
    simp [ContinuousLinearMap.smulRight_apply, add_mul]
  smul_left c c₁ f := by
    ext v w
    simp [ContinuousLinearMap.smulRight_apply, mul_assoc]
  add_right c f₁ f₂ := by
    ext v w
    simp [ContinuousLinearMap.smulRight_apply]
  smul_right c c₁ f := by
    ext v w
    simp [ContinuousLinearMap.smulRight_apply]
    ring
  bound := by
    refine ⟨1, one_pos, fun c f => ?_⟩
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    simp only [ContinuousLinearMap.smulRight_apply]
    calc ‖c v • f‖ = ‖c v‖ * ‖f‖ := norm_smul _ _
      _ ≤ (‖c‖ * ‖v‖) * ‖f‖ := by gcongr; exact c.le_opNorm v
      _ = 1 * ‖c‖ * ‖f‖ * ‖v‖ := by ring

/-- `‖c.smulRight f‖ ≤ ‖c‖ ‖f‖` for `c, f : E →L[ℝ] ℂ`. -/
private theorem heat_norm_smulRight_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c f : E →L[ℝ] ℂ) : ‖c.smulRight f‖ ≤ ‖c‖ * ‖f‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  simp only [ContinuousLinearMap.smulRight_apply]
  calc ‖c v • f‖ = ‖c v‖ * ‖f‖ := norm_smul _ _
    _ ≤ (‖c‖ * ‖v‖) * ‖f‖ := by gcongr; exact c.le_opNorm v
    _ = ‖c‖ * ‖f‖ * ‖v‖ := by ring

theorem HeatClass.mul {ι : Type*} [Fintype ι] {F₁ F₂ : ℝ → (ι → ℝ) → ℂ} {a b : ℝ}
    (h₁ : HeatClass F₁ a b) (h₂ : HeatClass F₂ a b) :
    HeatClass (fun r y => F₁ r y * F₂ r y) a b := by
  obtain ⟨hc₁, ⟨C₁, hC₁⟩, ⟨Fu₁, hu₁, hcu₁, Cu₁, hCu₁⟩,
    ⟨DF₁, D2F₁, hD₁, hD2₁, hcD₁, hcD2₁, Cd₁, hCd₁⟩⟩ := h₁
  obtain ⟨hc₂, ⟨C₂, hC₂⟩, ⟨Fu₂, hu₂, hcu₂, Cu₂, hCu₂⟩,
    ⟨DF₂, D2F₂, hD₂, hD2₂, hcD₂, hcD2₂, Cd₂, hCd₂⟩⟩ := h₂
  have hB : ContinuousOn (fun p : ℝ × (ι → ℝ) =>
      (Function.uncurry DF₁ p).smulRight (Function.uncurry DF₂ p)) (Set.Ioo a b ×ˢ Set.univ) :=
    heat_smulRight_bdd.continuous.comp_continuousOn (hcD₁.prodMk hcD₂)
  have hB' : ContinuousOn (fun p : ℝ × (ι → ℝ) =>
      (Function.uncurry DF₂ p).smulRight (Function.uncurry DF₁ p)) (Set.Ioo a b ×ˢ Set.univ) :=
    heat_smulRight_bdd.continuous.comp_continuousOn (hcD₂.prodMk hcD₁)
  refine ⟨hc₁.mul hc₂, ⟨C₁ * C₂, fun r hr x => ?_⟩,
    ⟨fun r x => Fu₁ r x * F₂ r x + F₁ r x * Fu₂ r x,
      fun r hr x => (hu₁ r hr x).mul (hu₂ r hr x),
      (hcu₁.mul hc₂).add (hc₁.mul hcu₂), Cu₁ * C₂ + C₁ * Cu₂, fun r hr x => ?_⟩,
    ⟨fun r x => F₁ r x • DF₂ r x + F₂ r x • DF₁ r x,
      fun r x => (F₁ r x • D2F₂ r x + (DF₁ r x).smulRight (DF₂ r x)) +
        (F₂ r x • D2F₁ r x + (DF₂ r x).smulRight (DF₁ r x)),
      fun r hr x => (hD₁ r hr x).mul (hD₂ r hr x),
      fun r hr x => ((hD₁ r hr x).smul (hD2₂ r hr x)).add ((hD₂ r hr x).smul (hD2₁ r hr x)),
      (hc₁.smul hcD₂).add (hc₂.smul hcD₁),
      ((hc₁.smul hcD2₂).add hB).add ((hc₂.smul hcD2₁).add hB'),
      C₁ * Cd₂ + C₂ * Cd₁ + 2 * Cd₁ * Cd₂, fun r hr x => ⟨?_, ?_⟩⟩⟩
  · have n1 := hC₁ r hr x
    have n2 := hC₂ r hr x
    exact (norm_mul_le _ _).trans (mul_le_mul n1 n2 (norm_nonneg _) ((norm_nonneg _).trans n1))
  · have n1 := hC₁ r hr x
    have n2 := hC₂ r hr x
    have u1 := hCu₁ r hr x
    have u2 := hCu₂ r hr x
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (norm_mul_le _ _).trans (mul_le_mul u1 n2 (norm_nonneg _) ((norm_nonneg _).trans u1))
    · exact (norm_mul_le _ _).trans (mul_le_mul n1 u2 (norm_nonneg _) ((norm_nonneg _).trans n1))
  · have n1 := hC₁ r hr x
    have n2 := hC₂ r hr x
    have d1 := (hCd₁ r hr x).1
    have d2 := (hCd₂ r hr x).1
    have p1 : ‖F₁ r x • DF₂ r x‖ ≤ C₁ * Cd₂ := by
      rw [norm_smul]; exact mul_le_mul n1 d2 (norm_nonneg _) ((norm_nonneg _).trans n1)
    have p2 : ‖F₂ r x • DF₁ r x‖ ≤ C₂ * Cd₁ := by
      rw [norm_smul]; exact mul_le_mul n2 d1 (norm_nonneg _) ((norm_nonneg _).trans n2)
    have q : 0 ≤ Cd₁ * Cd₂ := mul_nonneg ((norm_nonneg _).trans d1) ((norm_nonneg _).trans d2)
    nlinarith [(norm_add_le (F₁ r x • DF₂ r x) (F₂ r x • DF₁ r x))]
  · have n1 := hC₁ r hr x
    have n2 := hC₂ r hr x
    have d1 := (hCd₁ r hr x).1
    have d2 := (hCd₂ r hr x).1
    have e1 := (hCd₁ r hr x).2
    have e2 := (hCd₂ r hr x).2
    have p1 : ‖F₁ r x • D2F₂ r x‖ ≤ C₁ * Cd₂ := by
      rw [norm_smul]; exact mul_le_mul n1 e2 (norm_nonneg _) ((norm_nonneg _).trans n1)
    have p2 : ‖F₂ r x • D2F₁ r x‖ ≤ C₂ * Cd₁ := by
      rw [norm_smul]; exact mul_le_mul n2 e1 (norm_nonneg _) ((norm_nonneg _).trans n2)
    have p3 : ‖(DF₁ r x).smulRight (DF₂ r x)‖ ≤ Cd₁ * Cd₂ :=
      (heat_norm_smulRight_le _ _).trans
        (mul_le_mul d1 d2 (norm_nonneg _) ((norm_nonneg _).trans d1))
    have p4 : ‖(DF₂ r x).smulRight (DF₁ r x)‖ ≤ Cd₂ * Cd₁ :=
      (heat_norm_smulRight_le _ _).trans
        (mul_le_mul d2 d1 (norm_nonneg _) ((norm_nonneg _).trans d2))
    have t1 := norm_add_le (F₁ r x • D2F₂ r x) ((DF₁ r x).smulRight (DF₂ r x))
    have t2 := norm_add_le (F₂ r x • D2F₁ r x) ((DF₂ r x).smulRight (DF₁ r x))
    have t3 := norm_add_le (F₁ r x • D2F₂ r x + (DF₁ r x).smulRight (DF₂ r x))
      (F₂ r x • D2F₁ r x + (DF₂ r x).smulRight (DF₁ r x))
    linarith

/-- The norm of postcomposition with `T` is at most `‖T‖`. -/
private theorem heat_norm_compL_le {E G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T : G →L[ℝ] H) : ‖ContinuousLinearMap.compL ℝ E G H T‖ ≤ ‖T‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun A => T.opNorm_comp_le A

/-- Postcomposition with a real-linear map `ℂ → ℂ` preserves the class. -/
private theorem heatClass_postcomp {ι : Type*} [Fintype ι] {F : ℝ → (ι → ℝ) → ℂ} {a b : ℝ}
    (h : HeatClass F a b) (T : ℂ →L[ℝ] ℂ) : HeatClass (fun r y => T (F r y)) a b := by
  obtain ⟨hc, ⟨C, hC⟩, ⟨Fu, hu, hcu, Cu, hCu⟩,
    ⟨DF, D2F, hD, hD2, hcD, hcD2, Cd, hCd⟩⟩ := h
  have hT0 : 0 ≤ ‖T‖ := norm_nonneg T
  set P1 := ContinuousLinearMap.compL ℝ (ι → ℝ) ℂ ℂ T with hP1def
  set P2 := ContinuousLinearMap.compL ℝ (ι → ℝ) ((ι → ℝ) →L[ℝ] ℂ) ((ι → ℝ) →L[ℝ] ℂ) P1 with hP2def
  have hP1 : ‖P1‖ ≤ ‖T‖ := heat_norm_compL_le T
  have hP2 : ‖P2‖ ≤ ‖T‖ := (heat_norm_compL_le P1).trans hP1
  refine ⟨T.continuous.comp_continuousOn hc, ⟨‖T‖ * C, fun r hr x => ?_⟩,
    ⟨fun r x => T (Fu r x), fun r hr x => T.hasFDerivAt.comp_hasDerivAt r (hu r hr x),
      T.continuous.comp_continuousOn hcu, ‖T‖ * Cu, fun r hr x => ?_⟩,
    ⟨fun r x => P1 (DF r x), fun r x => P2 (D2F r x),
      fun r hr x => T.hasFDerivAt.comp x (hD r hr x),
      fun r hr x => P1.hasFDerivAt.comp x (hD2 r hr x),
      P1.continuous.comp_continuousOn hcD, P2.continuous.comp_continuousOn hcD2,
      ‖T‖ * Cd, fun r hr x => ⟨?_, ?_⟩⟩⟩
  · exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC r hr x) hT0)
  · exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hCu r hr x) hT0)
  · exact (P1.le_opNorm _).trans
      (mul_le_mul hP1 (hCd r hr x).1 (norm_nonneg _) hT0)
  · exact (P2.le_opNorm _).trans
      (mul_le_mul hP2 (hCd r hr x).2 (norm_nonneg _) hT0)

theorem HeatClass.star {ι : Type*} [Fintype ι] {F : ℝ → (ι → ℝ) → ℂ} {a b : ℝ}
    (h : HeatClass F a b) : HeatClass (fun r y => star (F r y)) a b := by
  simpa [Complex.star_def] using heatClass_postcomp h Complex.conjCLE

/-- Subtracting a deterministic `C¹` function of the time keeps the class (the loop errors
`D_k = ℒ_k - 𝒦_k`). -/
theorem HeatClass.sub_time {ι : Type*} [Fintype ι] {F : ℝ → (ι → ℝ) → ℂ} {a b : ℝ}
    (h : HeatClass F a b) (κ κ' : ℝ → ℂ) (hκ : ∀ r ∈ Set.Ioo a b, HasDerivAt κ (κ' r) r)
    (hκ' : ContinuousOn κ' (Set.Ioo a b)) (hb : ∃ C : ℝ, ∀ r ∈ Set.Ioo a b, ‖κ r‖ ≤ C ∧ ‖κ' r‖ ≤ C) :
    HeatClass (fun r y => F r y - κ r) a b := by
  obtain ⟨hc, ⟨C, hC⟩, ⟨Fu, hu, hcu, Cu, hCu⟩,
    ⟨DF, D2F, hD, hD2, hcD, hcD2, Cd, hCd⟩⟩ := h
  obtain ⟨Ck, hCk⟩ := hb
  have hκ0 : ContinuousOn κ (Set.Ioo a b) := fun r hr => (hκ r hr).continuousAt.continuousWithinAt
  have hκc : ContinuousOn (fun p : ℝ × (ι → ℝ) => κ p.1) (Set.Ioo a b ×ˢ Set.univ) :=
    hκ0.comp continuousOn_fst (fun p hp => hp.1)
  have hκc' : ContinuousOn (fun p : ℝ × (ι → ℝ) => κ' p.1) (Set.Ioo a b ×ˢ Set.univ) :=
    hκ'.comp continuousOn_fst (fun p hp => hp.1)
  refine ⟨hc.sub hκc, ⟨C + Ck, fun r hr x => ?_⟩,
    ⟨fun r x => Fu r x - κ' r, fun r hr x => (hu r hr x).sub (hκ r hr), hcu.sub hκc', Cu + Ck,
      fun r hr x => ?_⟩,
    ⟨DF, D2F, fun r hr x => (hD r hr x).sub_const (κ r), hD2, hcD, hcD2, Cd, hCd⟩⟩
  · exact (norm_sub_le (F r x) (κ r)).trans (add_le_add (hC r hr x) (hCk r hr).1)
  · exact (norm_sub_le (Fu r x) (κ' r)).trans (add_le_add (hCu r hr x) (hCk r hr).2)

/-- `C²` with bounded value, first and second derivative. -/
def C2b (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 φ ∧ ∃ C : ℝ, ∀ x, |φ x| ≤ C ∧ |deriv φ x| ≤ C ∧ |iteratedDeriv 2 φ x| ≤ C

/-- Chain rule for `φ ∘ X` from real jet data of `X` (value, time derivative, first and second
space derivative, all jointly continuous, the last three bounded). -/
private theorem heatClass_chain {ι : Type*} [Fintype ι] {X Xu : ℝ → (ι → ℝ) → ℝ}
    {DX : ℝ → (ι → ℝ) → ((ι → ℝ) →L[ℝ] ℝ)}
    {D2X : ℝ → (ι → ℝ) → ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ)} {a b : ℝ}
    (hXc : ContinuousOn (Function.uncurry X) (Set.Ioo a b ×ˢ Set.univ))
    (hXu : ∀ r ∈ Set.Ioo a b, ∀ x, HasDerivAt (fun r' => X r' x) (Xu r x) r)
    (hXuc : ContinuousOn (Function.uncurry Xu) (Set.Ioo a b ×ˢ Set.univ))
    (hDX : ∀ r ∈ Set.Ioo a b, ∀ x, HasFDerivAt (X r) (DX r x) x)
    (hD2X : ∀ r ∈ Set.Ioo a b, ∀ x, HasFDerivAt (DX r) (D2X r x) x)
    (hDXc : ContinuousOn (Function.uncurry DX) (Set.Ioo a b ×ˢ Set.univ))
    (hD2Xc : ContinuousOn (Function.uncurry D2X) (Set.Ioo a b ×ˢ Set.univ))
    (CX : ℝ) (hCX : ∀ r ∈ Set.Ioo a b, ∀ x, |Xu r x| ≤ CX ∧ ‖DX r x‖ ≤ CX ∧ ‖D2X r x‖ ≤ CX)
    {φ : ℝ → ℝ} (hφ : C2b φ) :
    HeatClass (fun r y => ((φ (X r y) : ℝ) : ℂ)) a b := by
  obtain ⟨hφ2, Cφ, hCφ⟩ := hφ
  have hφ1 : ContDiff ℝ 1 (deriv φ) :=
    ((contDiff_succ_iff_deriv (n := 1)).1 hφ2).2.2
  have hφd : ∀ t, HasDerivAt φ (deriv φ t) t := fun t =>
    ((hφ2.differentiable (by norm_num)) t).hasDerivAt
  have hφ'd : ∀ t, HasDerivAt (deriv φ) (deriv (deriv φ) t) t := fun t =>
    ((hφ1.differentiable (by norm_num)) t).hasDerivAt
  have hφc : Continuous φ := hφ2.continuous
  have hφ'c : Continuous (deriv φ) := hφ1.continuous
  have hφ''c : Continuous (deriv (deriv φ)) := hφ1.continuous_deriv le_rfl
  have hit : iteratedDeriv 2 φ = deriv (deriv φ) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hb : ∀ t, |φ t| ≤ Cφ ∧ |deriv φ t| ≤ Cφ ∧ |deriv (deriv φ) t| ≤ Cφ := fun t => by
    have := hCφ t
    rwa [hit] at this
  have hCφ0 : 0 ≤ Cφ := (abs_nonneg _).trans (hb 0).1
  set P1 : (((ι → ℝ) →L[ℝ] ℝ) →L[ℝ] ((ι → ℝ) →L[ℝ] ℂ)) :=
    ContinuousLinearMap.compL ℝ (ι → ℝ) ℝ ℂ Complex.ofRealCLM with hP1
  set P2 := ContinuousLinearMap.compL ℝ (ι → ℝ) ((ι → ℝ) →L[ℝ] ℝ) ((ι → ℝ) →L[ℝ] ℂ) P1 with hP2
  have hP1n : ‖P1‖ ≤ 1 := (heat_norm_compL_le _).trans Complex.ofRealCLM_norm.le
  have hP2n : ‖P2‖ ≤ 1 := (heat_norm_compL_le _).trans hP1n
  set Δ : ℝ → (ι → ℝ) → ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ) := fun r x =>
    deriv φ (X r x) • D2X r x +
      (deriv (deriv φ) (X r x) • DX r x).smulRight (DX r x) with hΔ
  have hXc' : ContinuousOn (fun p : ℝ × (ι → ℝ) => X p.1 p.2) (Set.Ioo a b ×ˢ Set.univ) := hXc
  have hc1 : ContinuousOn (fun p : ℝ × (ι → ℝ) => deriv φ (X p.1 p.2))
      (Set.Ioo a b ×ˢ Set.univ) := hφ'c.comp_continuousOn hXc'
  have hc2 : ContinuousOn (fun p : ℝ × (ι → ℝ) => deriv (deriv φ) (X p.1 p.2))
      (Set.Ioo a b ×ˢ Set.univ) := hφ''c.comp_continuousOn hXc'
  refine ⟨Complex.continuous_ofReal.comp_continuousOn (hφc.comp_continuousOn hXc'),
    ⟨Cφ, fun r hr x => ?_⟩,
    ⟨fun r x => ((deriv φ (X r x) * Xu r x : ℝ) : ℂ),
      fun r hr x => ((hφd (X r x)).comp r (hXu r hr x)).ofReal_comp,
      Complex.continuous_ofReal.comp_continuousOn (hc1.mul hXuc), Cφ * CX, fun r hr x => ?_⟩,
    ⟨fun r x => P1 (deriv φ (X r x) • DX r x), fun r x => P2 (Δ r x),
      fun r hr x => Complex.ofRealCLM.hasFDerivAt.comp x
        ((hφd (X r x)).comp_hasFDerivAt x (hDX r hr x)),
      fun r hr x => P1.hasFDerivAt.comp x
        (((hφ'd (X r x)).comp_hasFDerivAt x (hDX r hr x)).smul (hD2X r hr x)),
      P1.continuous.comp_continuousOn (hc1.smul hDXc),
      P2.continuous.comp_continuousOn
        ((hc1.smul hD2Xc).add
          ((ContinuousLinearMap.smulRightL ℝ (ι → ℝ) ((ι → ℝ) →L[ℝ] ℝ)).continuous₂
            |>.comp_continuousOn ((hc2.smul hDXc).prodMk hDXc))),
      Cφ * CX * (1 + CX), fun r hr x => ⟨?_, ?_⟩⟩⟩
  · rw [Complex.norm_real, Real.norm_eq_abs]
    exact (hb _).1
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    obtain ⟨h1, -, -⟩ := hCX r hr x
    exact mul_le_mul (hb _).2.1 h1 (abs_nonneg _) hCφ0
  · obtain ⟨-, h2, -⟩ := hCX r hr x
    have hCX0 : 0 ≤ CX := (norm_nonneg _).trans h2
    have h3 : ‖deriv φ (X r x) • DX r x‖ ≤ Cφ * CX := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hb _).2.1 h2 (norm_nonneg _) hCφ0
    calc ‖P1 (deriv φ (X r x) • DX r x)‖ ≤ ‖P1‖ * ‖deriv φ (X r x) • DX r x‖ := P1.le_opNorm _
      _ ≤ 1 * (Cφ * CX) := mul_le_mul hP1n h3 (norm_nonneg _) zero_le_one
      _ ≤ Cφ * CX * (1 + CX) := by
        nlinarith [mul_nonneg hCφ0 hCX0, mul_nonneg (mul_nonneg hCφ0 hCX0) hCX0]
  · obtain ⟨-, h2, h3⟩ := hCX r hr x
    have hCX0 : 0 ≤ CX := (norm_nonneg _).trans h2
    have h4 : ‖deriv φ (X r x) • D2X r x‖ ≤ Cφ * CX := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hb _).2.1 h3 (norm_nonneg _) hCφ0
    have h5 : ‖deriv (deriv φ) (X r x) • DX r x‖ ≤ Cφ * CX := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hb _).2.2 h2 (norm_nonneg _) hCφ0
    have h6 : ‖(deriv (deriv φ) (X r x) • DX r x).smulRight (DX r x)‖ ≤ Cφ * CX * CX := by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul h5 h2 (norm_nonneg _) (mul_nonneg hCφ0 hCX0)
    have h7 : ‖Δ r x‖ ≤ Cφ * CX * (1 + CX) := by
      refine (norm_add_le _ _).trans ?_
      nlinarith
    calc ‖P2 (Δ r x)‖ ≤ ‖P2‖ * ‖Δ r x‖ := P2.le_opNorm _
      _ ≤ 1 * (Cφ * CX * (1 + CX)) := mul_le_mul hP2n h7 (norm_nonneg _) zero_le_one
      _ = Cφ * CX * (1 + CX) := one_mul _

theorem HeatClass.comp_real {ι : Type*} [Fintype ι] {X : ℝ → (ι → ℝ) → ℝ} {a b : ℝ}
    (hX : HeatClass (fun r y => ((X r y : ℝ) : ℂ)) a b) {φ : ℝ → ℝ} (hφ : C2b φ) :
    HeatClass (fun r y => ((φ (X r y) : ℝ) : ℂ)) a b := by
  obtain ⟨hc, -, ⟨Fu, hu, hcu, Cu, hCu⟩, ⟨DF, D2F, hD, hD2, hcD, hcD2, Cd, hCd⟩⟩ := hX
  set P : ((ι → ℝ) →L[ℝ] ℂ) →L[ℝ] ((ι → ℝ) →L[ℝ] ℝ) :=
    ContinuousLinearMap.compL ℝ (ι → ℝ) ℂ ℝ Complex.reCLM with hP
  set P2 := ContinuousLinearMap.compL ℝ (ι → ℝ) ((ι → ℝ) →L[ℝ] ℂ) ((ι → ℝ) →L[ℝ] ℝ) P with hP2
  have hPn : ‖P‖ ≤ 1 := (heat_norm_compL_le _).trans Complex.reCLM_norm.le
  have hP2n : ‖P2‖ ≤ 1 := (heat_norm_compL_le _).trans hPn
  refine heatClass_chain (X := X) (Xu := fun r x => (Fu r x).re) (DX := fun r x => P (DF r x))
    (D2X := fun r x => P2 (D2F r x)) (a := a) (b := b)
    (Complex.continuous_re.comp_continuousOn hc) ?_ ?_ ?_ ?_ ?_ ?_
    (max Cu Cd) ?_ hφ
  · intro r hr x
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt r (hu r hr x)
  · exact Complex.continuous_re.comp_continuousOn hcu
  · intro r hr x
    exact Complex.reCLM.hasFDerivAt.comp x (hD r hr x)
  · intro r hr x
    exact P.hasFDerivAt.comp x (hD2 r hr x)
  · exact (ContinuousLinearMap.compL ℝ (ι → ℝ) ℂ ℝ Complex.reCLM).continuous.comp_continuousOn hcD
  · exact P2.continuous.comp_continuousOn hcD2
  · intro r hr x
    refine ⟨?_, ?_, ?_⟩
    · exact (Complex.abs_re_le_norm _).trans ((hCu r hr x).trans (le_max_left _ _))
    · calc ‖P (DF r x)‖ ≤ ‖P‖ * ‖DF r x‖ := P.le_opNorm _
        _ ≤ 1 * Cd := mul_le_mul hPn (hCd r hr x).1 (norm_nonneg _) zero_le_one
        _ ≤ max Cu Cd := by rw [one_mul]; exact le_max_right _ _
    · calc ‖P2 (D2F r x)‖ ≤ ‖P2‖ * ‖D2F r x‖ := P2.le_opNorm _
        _ ≤ 1 * Cd := mul_le_mul hP2n (hCd r hr x).2 (norm_nonneg _) zero_le_one
        _ ≤ max Cu Cd := by rw [one_mul]; exact le_max_right _ _

/-- For a `C²` real function `g`, the complex-valued function `e ↦ (g e : ℂ)` has second
derivative `(g''(0) : ℂ)` at `0`. -/
private theorem heat_iter2_ofReal {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) :
    iteratedDeriv 2 (fun e : ℝ => ((g e : ℝ) : ℂ)) 0 = ((iteratedDeriv 2 g 0 : ℝ) : ℂ) := by
  have hg1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hdg : Differentiable ℝ (deriv g) := hg.differentiable_deriv_two
  have hd1 : deriv (fun e : ℝ => ((g e : ℝ) : ℂ)) = fun e => ((deriv g e : ℝ) : ℂ) :=
    funext fun e => (hg1 e).hasDerivAt.ofReal_comp.deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd1, iteratedDeriv_succ, iteratedDeriv_one]
  exact (hdg 0).hasDerivAt.ofReal_comp.deriv

/-- Second-order chain rule `(φ ∘ h)''(0) = φ''(h 0) h'(0)² + φ'(h 0) h''(0)` for `C²` functions. -/
private theorem heat_iter2_comp {φ h : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hh : ContDiff ℝ 2 h) :
    iteratedDeriv 2 (fun e : ℝ => φ (h e)) 0 =
      iteratedDeriv 2 φ (h 0) * (deriv h 0) ^ 2 + deriv φ (h 0) * iteratedDeriv 2 h 0 := by
  have hφ1 : ContDiff ℝ 1 (deriv φ) := ((contDiff_succ_iff_deriv (n := 1)).1 hφ).2.2
  have hφd : ∀ t, HasDerivAt φ (deriv φ t) t := fun t =>
    ((hφ.differentiable (by norm_num)) t).hasDerivAt
  have hφ'd : ∀ t, HasDerivAt (deriv φ) (deriv (deriv φ) t) t := fun t =>
    ((hφ1.differentiable (by norm_num)) t).hasDerivAt
  have hh1 : ∀ e, HasDerivAt h (deriv h e) e := fun e =>
    ((hh.differentiable (by norm_num)) e).hasDerivAt
  have hh'd : ∀ e, HasDerivAt (deriv h) (deriv (deriv h) e) e := fun e =>
    ((hh.differentiable_deriv_two) e).hasDerivAt
  have hd1 : deriv (fun e : ℝ => φ (h e)) = fun e => deriv φ (h e) * deriv h e :=
    funext fun e => ((hφd (h e)).comp e (hh1 e)).deriv
  have h2 : HasDerivAt (fun e => deriv φ (h e) * deriv h e)
      (deriv (deriv φ) (h 0) * deriv h 0 * deriv h 0 + deriv φ (h 0) * deriv (deriv h) 0) 0 :=
    ((hφ'd (h 0)).comp 0 (hh1 0)).mul (hh'd 0)
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd1, h2.deriv, iteratedDeriv_succ, iteratedDeriv_one,
    iteratedDeriv_succ, iteratedDeriv_one]
  ring

/-- Chain rule `𝒢(φ ∘ X) = φ'(X) 𝒢X + ½ φ''(X) Γ(X)` for a real field `X`. -/
theorem coordGen_comp {ι : Type*} [Fintype ι] (σ2 : ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (X : ℝ → (ι → ℝ) → ℝ) (u : ℝ) (y : ι → ℝ) (hXu : DifferentiableAt ℝ (fun r => X r y) u)
    (hXy : ContDiff ℝ 2 (X u)) :
    coordGen σ2 (fun r z => ((φ (X r z) : ℝ) : ℂ)) u y =
      ((deriv φ (X u y) : ℝ) : ℂ) * coordGen σ2 (fun r z => ((X r z : ℝ) : ℂ)) u y +
        ((iteratedDeriv 2 φ (X u y) / 2 : ℝ) : ℂ) *
          coordGamma σ2 (fun z => ((X u z : ℝ) : ℂ)) (fun z => ((X u z : ℝ) : ℂ)) y := by
  have hφd : DifferentiableAt ℝ φ (X u y) := (hφ.differentiable (by norm_num)) _
  have hT : deriv (fun r => ((φ (X r y) : ℝ) : ℂ)) u =
      ((deriv φ (X u y) * deriv (fun r => X r y) u : ℝ) : ℂ) :=
    ((hφd.hasDerivAt.comp u hXu.hasDerivAt).ofReal_comp).deriv
  have hT' : deriv (fun r => ((X r y : ℝ) : ℂ)) u = ((deriv (fun r => X r y) u : ℝ) : ℂ) :=
    hXu.hasDerivAt.ofReal_comp.deriv
  have hline : ∀ i : ι, ContDiff ℝ 2 (fun e : ℝ => X u (y + e • Pi.single i (1 : ℝ))) :=
    fun i => hXy.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hz : ∀ i : ι, y + (0 : ℝ) • (Pi.single i (1 : ℝ) : ι → ℝ) = y := fun i => by simp
  have hA : ∀ i : ι,
      iteratedDeriv 2 (fun e : ℝ => ((φ (X u (y + e • Pi.single i (1 : ℝ))) : ℝ) : ℂ)) 0 =
        ((iteratedDeriv 2 φ (X u y) *
            (deriv (fun e : ℝ => X u (y + e • Pi.single i (1 : ℝ))) 0) ^ 2 : ℝ) : ℂ) +
          ((deriv φ (X u y) : ℝ) : ℂ) *
            iteratedDeriv 2 (fun e : ℝ => ((X u (y + e • Pi.single i (1 : ℝ)) : ℝ) : ℂ)) 0 := by
    intro i
    have h1 := heat_iter2_ofReal (g := fun e : ℝ => φ (X u (y + e • Pi.single i (1 : ℝ))))
      (hφ.comp (hline i))
    have h2 := heat_iter2_comp hφ (hline i)
    have h3 := heat_iter2_ofReal (hline i)
    rw [h1, h2]
    simp only [hz i] at *
    rw [h3]
    push_cast
    ring
  have hB : ∀ i : ι,
      deriv (fun e : ℝ => ((X u (y + e • Pi.single i (1 : ℝ)) : ℝ) : ℂ)) 0 =
        ((deriv (fun e : ℝ => X u (y + e • Pi.single i (1 : ℝ))) 0 : ℝ) : ℂ) := fun i =>
    (((hline i).differentiable (by norm_num)) 0).hasDerivAt.ofReal_comp.deriv
  simp only [coordGen, coordGamma, hT, hT', hA, hB, Complex.star_def, Complex.conj_ofReal]
  push_cast
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  ring_nf

end LSBA
