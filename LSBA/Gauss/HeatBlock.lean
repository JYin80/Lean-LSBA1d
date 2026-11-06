import LSBA.Gauss.HeatGenerator
import LSBA.Gauss.GUE
import LSBA.Spectral.ResolventBounds
import LSBA.Loop.Basic
import LSBA.Kernel.Defs

/-!
# The generator form of Itô's formula on the Hermitian block slice

The slice `x ↦ A + Σ_{c,k} x_{c,k} T_{c,k}` in the GUE block coordinates, the block generator
`𝒢_u = ∂_u + (γ/(2W)) Σ ∂²_T` and bracket of (5.4) [fo:eq:ito] and (5.9) [gc:eq:bracket], the
generator form of Itô's formula for the single-time realization `A + √(uγ) V` of (5.1) [fo:eq:flow],
and the class membership of resolvent loops (5.5) [fo:eq:loops] and entries at the characteristic
`z_u` of (5.3) [fo:eq:characteristic].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The Hermitian block-coordinate slice `x ↦ A + Σ_{c,k} x_{c,k} T_{c,k}`. -/
def blockSlice (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (x : Ω W L) :
    Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  A + ∑ c : Fin L, ∑ k : Fin W × Fin W, ((x (c, k.1, k.2) : ℝ) : ℂ) • blockBasis W L c k

/-- Block generator `𝒢_u = ∂_u + (γ/(2W)) Σ_{c,k} ∂²_{T_{c,k}}`, the generator form of (5.4)
[fo:eq:ito]. -/
def blockGen (W L : ℕ) (γ : ℝ) (F : ℝ → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ → ℂ) (u : ℝ)
    (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) : ℂ :=
  deriv (fun r => F r M) u + ((γ / (2 * W) : ℝ) : ℂ) *
    ∑ c : Fin L, ∑ k : Fin W × Fin W,
      iteratedDeriv 2 (fun e : ℝ => F u (M + (e : ℂ) • blockBasis W L c k)) 0

/-- Block carré du champ `Γ(f₁, f₂) = (γ/W) Σ_{c,k} ∂_{T_{c,k}} f₁ conj(∂_{T_{c,k}} f₂)`, the
generator form of (5.9) [gc:eq:bracket]. -/
def blockGamma (W L : ℕ) (γ : ℝ) (f₁ f₂ : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ → ℂ)
    (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) : ℂ :=
  ((γ / W : ℝ) : ℂ) * ∑ c : Fin L, ∑ k : Fin W × Fin W,
    deriv (fun e : ℝ => f₁ (M + (e : ℂ) • blockBasis W L c k)) 0 *
      star (deriv (fun e : ℝ => f₂ (M + (e : ℂ) • blockBasis W L c k)) 0)

/-- The slice as `A` plus a single sum over the coordinates. -/
private theorem blockSlice_eq_sum (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (x : Ω W L) :
    blockSlice W L A x = A + ∑ i : Fin L × Fin W × Fin W,
      ((x i : ℝ) : ℂ) • blockBasis W L i.1 (i.2.1, i.2.2) := by
  unfold blockSlice
  rw [Fintype.sum_prod_type]

/-- Moving along a coordinate axis moves the slice along the corresponding basis matrix. -/
private theorem blockSlice_add_line (W L : ℕ) [DecidableEq (Fin L × Fin W × Fin W)]
    (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (x : Ω W L) (i : Fin L × Fin W × Fin W)
    (e : ℝ) :
    blockSlice W L A (x + e • Pi.single i 1) =
      blockSlice W L A x + (e : ℂ) • blockBasis W L i.1 (i.2.1, i.2.2) := by
  rw [blockSlice_eq_sum, blockSlice_eq_sum, add_assoc]
  congr 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_add, add_smul,
    Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem blockFlow_eq_blockSlice (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) {s : ℝ}
    (hs : 0 ≤ s) (ω : Ω W L) :
    blockFlow W L A s ω = blockSlice W L A (Real.sqrt (s / W) • ω) := by
  -- `hs` is not needed: both square roots vanish for negative `s`.
  have _ := hs
  unfold blockFlow blockSlice
  rw [blockV_eq_sum_blockBasis]
  congr 1
  have h1 : ∀ (c : Fin L) (k : Fin W × Fin W),
      ((((Real.sqrt (s / W) • ω) (c, k.1, k.2) : ℝ)) : ℂ) • blockBasis W L c k =
        ((Real.sqrt (s / W) : ℝ) : ℂ) • ((ω (c, k.1, k.2) : ℂ) • blockBasis W L c k) := by
    intro c k
    rw [smul_smul, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  have h2 : (∑ c : Fin L, ∑ k : Fin W × Fin W,
      ((((Real.sqrt (s / W) • ω) (c, k.1, k.2) : ℝ)) : ℂ) • blockBasis W L c k) =
      ((Real.sqrt (s / W) : ℝ) : ℂ) • ∑ c : Fin L, ∑ k : Fin W × Fin W,
        (ω (c, k.1, k.2) : ℂ) • blockBasis W L c k := by
    simp only [h1, Finset.smul_sum]
  rw [h2, smul_smul]
  congr 1
  rw [Real.sqrt_div' _ (Nat.cast_nonneg W), div_eq_mul_inv]
  push_cast
  ring

theorem blockGen_slice (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (γ : ℝ)
    (F : ℝ → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ → ℂ) (u : ℝ) (x : Ω W L) :
    blockGen W L γ F u (blockSlice W L A x) =
      coordGen (γ / W) (fun r y => F r (blockSlice W L A y)) u x := by
  unfold blockGen coordGen
  have hc : ((γ / (2 * W) : ℝ) : ℂ) = (((γ / W) / 2 : ℝ) : ℂ) := by
    congr 1; rw [div_div, mul_comm]
  rw [hc]
  simp only [blockSlice_add_line]
  simp only [Fintype.sum_prod_type]

theorem blockGamma_slice (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (γ : ℝ)
    (f₁ f₂ : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ → ℂ) (x : Ω W L) :
    blockGamma W L γ f₁ f₂ (blockSlice W L A x) =
      coordGamma (γ / W) (fun y => f₁ (blockSlice W L A y)) (fun y => f₂ (blockSlice W L A y))
        x := by
  unfold blockGamma coordGamma
  simp only [blockSlice_add_line]
  simp only [Fintype.sum_prod_type]

/-- The generator form of Itô's formula in block form for `A + √(uγ) V`, the single-time realization
of (5.1) [fo:eq:flow]. -/
theorem blockHeat_generator (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (γ : ℝ)
    (hγ : 0 ≤ γ) (f : ℝ → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ → ℂ) {a b v : ℝ}
    (ha : a < 0) (hv : 0 ≤ v) (hvb : v < b)
    (hf : HeatClass (fun r x => f r (blockSlice W L A x)) a b) :
    ContinuousOn (fun u => ∫ ω, f u (blockFlow W L A (u * γ) ω) ∂(μ W L)) (Set.Icc 0 v) ∧
      ∀ u ∈ Set.Ioo 0 v, HasDerivAt (fun r => ∫ ω, f r (blockFlow W L A (r * γ) ω) ∂(μ W L))
        (∫ ω, blockGen W L γ f u (blockFlow W L A (u * γ) ω) ∂(μ W L)) u := by
  have hσ : 0 ≤ γ / (W : ℝ) := div_nonneg hγ (Nat.cast_nonneg W)
  have hμ : μ W L = stdGauss (Fin L × Fin W × Fin W) := rfl
  obtain ⟨hcont, hderiv⟩ := heat_generator (ι := Fin L × Fin W × Fin W) (γ / W) hσ
    (fun r x => f r (blockSlice W L A x)) ha hv hvb hf
  have hflow : ∀ u : ℝ, 0 ≤ u → ∀ ω : Ω W L,
      blockFlow W L A (u * γ) ω = blockSlice W L A (Real.sqrt (u * (γ / W)) • ω) := by
    intro u hu ω
    rw [blockFlow_eq_blockSlice W L A (mul_nonneg hu hγ) ω, mul_div_assoc]
  rw [hμ]
  refine ⟨hcont.congr fun u hu => ?_, fun u hu => ?_⟩
  · refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [hflow u hu.1 ω]
  · have hu0 : 0 < u := hu.1
    refine ((hderiv u hu).congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [Ioi_mem_nhds hu0] with r hr
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [hflow r (le_of_lt hr) ω]
    · refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      beta_reduce
      rw [hflow u hu0.le ω, blockGen_slice]

section HeatBlockCore

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Inversion is continuous at every invertible matrix. -/
private theorem heatBlock_continuousAt_inverse {x : Matrix n n ℂ} (hx : IsUnit x) :
    ContinuousAt Ring.inverse x := by
  obtain ⟨u, rfl⟩ := hx
  exact NormedRing.inverse_continuousAt u

/-- The derivative of the inverse along a differentiable path of invertible matrices. -/
private theorem heatBlock_hasDerivAt_inverse {f : ℝ → Matrix n n ℂ} {f' : Matrix n n ℂ} {r : ℝ}
    (hf : HasDerivAt f f' r) (hu : IsUnit (f r)) :
    HasDerivAt (fun s => Ring.inverse (f s))
      (-(Ring.inverse (f r) * f' * Ring.inverse (f r))) r := by
  set u : (Matrix n n ℂ)ˣ := hu.unit
  have hus : (u : Matrix n n ℂ) = f r := IsUnit.unit_spec _
  have hinv : ((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ) = Ring.inverse (f r) := by
    rw [← hus, Ring.inverse_unit]
  have hF : HasFDerivAt (Ring.inverse (M₀ := Matrix n n ℂ))
      (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) ↑u⁻¹) ↑u⁻¹) (f r) := by
    rw [← hus]; exact hasFDerivAt_ringInverse u
  have hcomp := hF.comp_hasDerivAt r hf
  simpa [Function.comp_def, ContinuousLinearMap.mulLeftRight_apply, hinv] using hcomp

/-- The entry `(p, q)` as a continuous real-linear functional. -/
private def heatBlockEntry (p q : n) : Matrix n n ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M p q
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

omit [DecidableEq n] in
private theorem heatBlockEntry_apply (p q : n) (M : Matrix n n ℂ) : heatBlockEntry p q M = M p q :=
  rfl

/-- The product of five factors is bounded by the product of the norms. -/
private theorem heatBlock_norm_mul₅_le (a b c d e : Matrix n n ℂ) :
    ‖a * b * c * d * e‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ * ‖e‖ := by
  calc ‖a * b * c * d * e‖ ≤ ‖a * b * c * d‖ * ‖e‖ := norm_mul_le _ _
    _ ≤ ‖a * b * c‖ * ‖d‖ * ‖e‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ ‖a * b‖ * ‖c‖ * ‖d‖ * ‖e‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ * ‖e‖ := by gcongr; exact norm_mul_le _ _

/-- Core of the class membership of `(r, x) ↦ ℓ ((P r + T x)⁻¹)`: the shift `P` is differentiable
in `r` with a constant derivative, `T` is a continuous linear map, and the inverses exist and are
uniformly bounded on `(a, b) × ℝ^ι`. -/
private theorem heatBlock_core {ι : Type*} [Fintype ι] (T : (ι → ℝ) →L[ℝ] Matrix n n ℂ)
    (P : ℝ → Matrix n n ℂ) (P' : Matrix n n ℂ) (hP : ∀ r, HasDerivAt P P' r)
    (ℓ : Matrix n n ℂ →L[ℝ] ℂ) {a b K : ℝ}
    (hU : ∀ r ∈ Set.Ioo a b, ∀ x, IsUnit (P r + T x))
    (hK : ∀ r ∈ Set.Ioo a b, ∀ x, ‖Ring.inverse (P r + T x)‖ ≤ K) :
    HeatClass (fun r x => ℓ (Ring.inverse (P r + T x))) a b := by
  set G : ℝ → (ι → ℝ) → Matrix n n ℂ := fun r x => Ring.inverse (P r + T x) with hGdef
  set K₀ : ℝ := max K 0 with hK₀def
  have hK₀ : 0 ≤ K₀ := le_max_right _ _
  have hGK : ∀ r ∈ Set.Ioo a b, ∀ x, ‖G r x‖ ≤ K₀ := fun r hr x =>
    (hK r hr x).trans (le_max_left _ _)
  have hPc : Continuous P := continuous_iff_continuousAt.2 fun r => (hP r).continuousAt
  set F : ℝ → (ι → ℝ) → ℂ := fun r x => ℓ (G r x) with hFdef
  -- joint continuity of the inverse
  have hGc : ContinuousOn (fun w : ℝ × (ι → ℝ) => G w.1 w.2) (Set.Ioo a b ×ˢ Set.univ) := by
    intro w hw
    have hcont : ContinuousAt (fun w : ℝ × (ι → ℝ) => P w.1 + T w.2) w :=
      ((hPc.comp continuous_fst).add (T.continuous.comp continuous_snd)).continuousAt
    have hinv : ContinuousAt (Ring.inverse (M₀ := Matrix n n ℂ)) (P w.1 + T w.2) :=
      heatBlock_continuousAt_inverse (hU w.1 hw.1 w.2)
    exact (ContinuousAt.comp (g := Ring.inverse (M₀ := Matrix n n ℂ))
      (f := fun w : ℝ × (ι → ℝ) => P w.1 + T w.2) hinv hcont).continuousWithinAt
  -- derivatives of the inverse along lines in `x`
  have hline : ∀ (x h : ι → ℝ) (e : ℝ), HasDerivAt (fun e : ℝ => x + e • h) h e := fun x h e => by
    simpa using ((hasDerivAt_id e).smul_const h).const_add x
  have hGline : ∀ r ∈ Set.Ioo a b, ∀ (x h : ι → ℝ),
      HasDerivAt (fun e : ℝ => G r (x + e • h)) (-(G r x * T h * G r x)) 0 := by
    intro r hr x h
    have h1 : HasDerivAt (fun e : ℝ => P r + T (x + e • h)) (T h) 0 := by
      have := ((T.hasFDerivAt (x := x + (0 : ℝ) • h)).comp_hasDerivAt (0 : ℝ) (hline x h 0))
      exact this.const_add (P r)
    have h2 := heatBlock_hasDerivAt_inverse h1 (by simpa using hU r hr x)
    simp only [zero_smul, add_zero] at h2
    exact h2
  -- derivative in `r`
  have hGtime : ∀ r ∈ Set.Ioo a b, ∀ x,
      HasDerivAt (fun r' => G r' x) (-(G r x * P' * G r x)) r := by
    intro r hr x
    exact heatBlock_hasDerivAt_inverse ((hP r).add_const (T x)) (hU r hr x)
  -- smoothness in `x`
  have hcd : ∀ r ∈ Set.Ioo a b, ContDiff ℝ 2 (F r) := by
    intro r hr
    rw [contDiff_iff_contDiffAt]
    intro x
    set u : (Matrix n n ℂ)ˣ := (hU r hr x).unit
    have hus : (u : Matrix n n ℂ) = P r + T x := IsUnit.unit_spec _
    have h1 : ContDiffAt ℝ 2 (Ring.inverse (M₀ := Matrix n n ℂ)) (P r + T x) := by
      rw [← hus]; exact contDiffAt_ringInverse ℝ u
    have h2 : ContDiffAt ℝ 2 (fun y => P r + T y) x :=
      (contDiff_const.add T.contDiff).contDiffAt
    have h3 : ContDiffAt ℝ 2 (fun y => Ring.inverse (P r + T y)) x :=
      ContDiffAt.comp (g := Ring.inverse (M₀ := Matrix n n ℂ)) (f := fun y => P r + T y) x h1 h2
    exact ContDiffAt.comp (g := ℓ) (f := fun y => Ring.inverse (P r + T y)) x
      ℓ.contDiff.contDiffAt h3
  -- first and second derivatives in `x`
  set DF : ℝ → (ι → ℝ) → ((ι → ℝ) →L[ℝ] ℂ) := fun r x => fderiv ℝ (F r) x with hDFdef
  set D2F : ℝ → (ι → ℝ) → ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℂ) := fun r x => fderiv ℝ (DF r) x
    with hD2Fdef
  have hFx : ∀ r ∈ Set.Ioo a b, ∀ x, HasFDerivAt (F r) (DF r x) x := fun r hr x =>
    (((hcd r hr).differentiable (by norm_num)) x).hasFDerivAt
  have hDFc : ∀ r ∈ Set.Ioo a b, ContDiff ℝ 1 (DF r) := fun r hr =>
    (hcd r hr).fderiv_right (by norm_num)
  have hDFx : ∀ r ∈ Set.Ioo a b, ∀ x, HasFDerivAt (DF r) (D2F r x) x := fun r hr x =>
    (((hDFc r hr).differentiable (by norm_num)) x).hasFDerivAt
  have hDFapply : ∀ r ∈ Set.Ioo a b, ∀ x h, DF r x h = ℓ (-(G r x * T h * G r x)) := by
    intro r hr x h
    have h1 : HasDerivAt (fun e : ℝ => F r (x + e • h)) (DF r x h) 0 :=
      (hFx r hr x).comp_hasDerivAt_of_eq (0 : ℝ) (hline x h 0) (by simp)
    have h2 : HasDerivAt (fun e : ℝ => F r (x + e • h)) (ℓ (-(G r x * T h * G r x))) 0 := by
      exact ℓ.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hGline r hr x h)
    exact h1.unique h2
  have hD2apply : ∀ r ∈ Set.Ioo a b, ∀ x h h', D2F r x h h' =
      ℓ (G r x * T h * G r x * T h' * G r x + G r x * T h' * G r x * T h * G r x) := by
    intro r hr x h h'
    have hφ : HasFDerivAt (fun y => DF r y h')
        ((ContinuousLinearMap.apply ℝ ℂ h').comp (D2F r x)) x :=
      (ContinuousLinearMap.apply ℝ ℂ h').hasFDerivAt.comp x (hDFx r hr x)
    have h1 : HasDerivAt (fun e : ℝ => DF r (x + e • h) h') (D2F r x h h') 0 := by
      exact hφ.comp_hasDerivAt_of_eq (0 : ℝ) (hline x h 0) (by simp)
    have h2 : HasDerivAt (fun e : ℝ => DF r (x + e • h) h')
        (ℓ (G r x * T h * G r x * T h' * G r x + G r x * T h' * G r x * T h * G r x)) 0 := by
      have h3 := ((hGline r hr x h).mul_const (T h')).mul (hGline r hr x h)
      have h4 := ℓ.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3.neg
      simp only [zero_smul, add_zero] at h4
      have h5 : (fun e : ℝ => DF r (x + e • h) h') =
          ℓ ∘ fun e : ℝ => -(G r (x + e • h) * T h' * G r (x + e • h)) := by
        funext e
        exact hDFapply r hr _ h'
      rw [h5]
      refine h4.congr_deriv ?_
      congr 1
      noncomm_ring
    exact h1.unique h2
  -- bounds
  have hT : ∀ h, ‖T h‖ ≤ ‖T‖ * ‖h‖ := fun h => T.le_opNorm h
  have hTn : 0 ≤ ‖T‖ := norm_nonneg _
  have hℓn : 0 ≤ ‖ℓ‖ := norm_nonneg _
  have hDFb : ∀ r ∈ Set.Ioo a b, ∀ x, ‖DF r x‖ ≤ ‖ℓ‖ * (K₀ * ‖T‖ * K₀) := by
    intro r hr x
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
    rw [hDFapply r hr x h]
    calc ‖ℓ (-(G r x * T h * G r x))‖ ≤ ‖ℓ‖ * ‖-(G r x * T h * G r x)‖ := ℓ.le_opNorm _
      _ = ‖ℓ‖ * ‖G r x * T h * G r x‖ := by rw [norm_neg]
      _ ≤ ‖ℓ‖ * (‖G r x‖ * ‖T h‖ * ‖G r x‖) := by gcongr; exact norm_mul₃_le
      _ ≤ ‖ℓ‖ * (K₀ * (‖T‖ * ‖h‖) * K₀) := by
          gcongr
          · exact hGK r hr x
          · exact hT h
          · exact hGK r hr x
      _ = ‖ℓ‖ * (K₀ * ‖T‖ * K₀) * ‖h‖ := by ring
  have hD2b : ∀ r ∈ Set.Ioo a b, ∀ x,
      ‖D2F r x‖ ≤ ‖ℓ‖ * (2 * (K₀ * ‖T‖ * K₀ * ‖T‖ * K₀)) := by
    intro r hr x
    have hS : ∀ u v : Matrix n n ℂ, ‖G r x * u * G r x * v * G r x‖ ≤
        K₀ * ‖u‖ * K₀ * ‖v‖ * K₀ := fun u v =>
      (heatBlock_norm_mul₅_le _ _ _ _ _).trans (by
        have := hGK r hr x
        gcongr)
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h' => ?_
    rw [hD2apply r hr x h h']
    calc ‖ℓ (G r x * T h * G r x * T h' * G r x + G r x * T h' * G r x * T h * G r x)‖
        ≤ ‖ℓ‖ * ‖G r x * T h * G r x * T h' * G r x + G r x * T h' * G r x * T h * G r x‖ :=
          ℓ.le_opNorm _
      _ ≤ ‖ℓ‖ * (‖G r x * T h * G r x * T h' * G r x‖ + ‖G r x * T h' * G r x * T h * G r x‖) := by
          gcongr; exact norm_add_le _ _
      _ ≤ ‖ℓ‖ * (K₀ * ‖T h‖ * K₀ * ‖T h'‖ * K₀ + K₀ * ‖T h'‖ * K₀ * ‖T h‖ * K₀) := by
          gcongr
          · exact hS _ _
          · exact hS _ _
      _ ≤ ‖ℓ‖ * (K₀ * (‖T‖ * ‖h‖) * K₀ * (‖T‖ * ‖h'‖) * K₀
            + K₀ * (‖T‖ * ‖h'‖) * K₀ * (‖T‖ * ‖h‖) * K₀) := by
          gcongr <;> exact hT _
      _ = ‖ℓ‖ * (2 * (K₀ * ‖T‖ * K₀ * ‖T‖ * K₀)) * ‖h‖ * ‖h'‖ := by ring
  refine ⟨?_, ⟨‖ℓ‖ * K₀, fun r hr x => ?_⟩,
    ⟨fun r x => ℓ (-(G r x * P' * G r x)), fun r hr x => ?_, ?_,
      ‖ℓ‖ * (K₀ * ‖P'‖ * K₀), fun r hr x => ?_⟩,
    ⟨DF, D2F, hFx, hDFx, ?_, ?_, ‖ℓ‖ * (K₀ * ‖T‖ * K₀) + ‖ℓ‖ * (2 * (K₀ * ‖T‖ * K₀ * ‖T‖ * K₀)),
      fun r hr x => ⟨?_, ?_⟩⟩⟩
  · exact ℓ.continuous.comp_continuousOn hGc
  · calc ‖ℓ (G r x)‖ ≤ ‖ℓ‖ * ‖G r x‖ := ℓ.le_opNorm _
      _ ≤ ‖ℓ‖ * K₀ := by gcongr; exact hGK r hr x
  · exact ℓ.hasFDerivAt.comp_hasDerivAt r (hGtime r hr x)
  · exact ℓ.continuous.comp_continuousOn (((hGc.mul continuousOn_const).mul hGc).neg)
  · calc ‖ℓ (-(G r x * P' * G r x))‖ ≤ ‖ℓ‖ * ‖-(G r x * P' * G r x)‖ := ℓ.le_opNorm _
      _ = ‖ℓ‖ * ‖G r x * P' * G r x‖ := by rw [norm_neg]
      _ ≤ ‖ℓ‖ * (‖G r x‖ * ‖P'‖ * ‖G r x‖) := by gcongr; exact norm_mul₃_le
      _ ≤ ‖ℓ‖ * (K₀ * ‖P'‖ * K₀) := by
          gcongr
          · exact hGK r hr x
          · exact hGK r hr x
  · refine continuousOn_clm_apply.2 fun h => ?_
    have : ContinuousOn (fun w : ℝ × (ι → ℝ) => ℓ (-(G w.1 w.2 * T h * G w.1 w.2)))
        (Set.Ioo a b ×ˢ Set.univ) :=
      ℓ.continuous.comp_continuousOn (((hGc.mul continuousOn_const).mul hGc).neg)
    exact this.congr fun w hw => hDFapply w.1 hw.1 w.2 h
  · refine continuousOn_clm_apply.2 fun h => continuousOn_clm_apply.2 fun h' => ?_
    have : ContinuousOn (fun w : ℝ × (ι → ℝ) => ℓ (G w.1 w.2 * T h * G w.1 w.2 * T h' * G w.1 w.2
        + G w.1 w.2 * T h' * G w.1 w.2 * T h * G w.1 w.2)) (Set.Ioo a b ×ˢ Set.univ) :=
      ℓ.continuous.comp_continuousOn
        ((((((hGc.mul continuousOn_const).mul hGc).mul continuousOn_const).mul hGc)).add
          (((((hGc.mul continuousOn_const).mul hGc).mul continuousOn_const).mul hGc)))
    exact this.congr fun w hw => hD2apply w.1 hw.1 w.2 h h'
  · exact (hDFb r hr x).trans (le_add_of_nonneg_right (by positivity))
  · exact (hD2b r hr x).trans (le_add_of_nonneg_left (by positivity))

omit [Fintype n] [DecidableEq n] in
/-- A real combination of Hermitian matrices is Hermitian. -/
private theorem heatBlock_isHermitian_sum {ι : Type*} [Fintype ι] (Tb : ι → Matrix n n ℂ)
    (hTb : ∀ i, (Tb i).IsHermitian) (x : ι → ℝ) :
    (∑ i, ((x i : ℝ) : ℂ) • Tb i).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_smul, (hTb i).eq, Complex.star_def, Complex.conj_ofReal]

/-- Resolvent entries of `A + Σ_i x_i T_i` at a spectral parameter `ζ(r)` with `ζ' = c` and
`|Im ζ(r)| ≥ η > 0` on `(a, b)` lie in the class. -/
private theorem heatBlock_heatClass_entry {ι : Type*} [Fintype ι]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (Tb : ι → Matrix n n ℂ)
    (hTb : ∀ i, (Tb i).IsHermitian) (ζ : ℝ → ℂ) (c : ℂ) (hζ : ∀ r, HasDerivAt ζ c r)
    {a b η : ℝ} (hη : 0 < η) (hζim : ∀ r ∈ Set.Ioo a b, η ≤ |(ζ r).im|) (p q : n) :
    HeatClass (fun r (x : ι → ℝ) =>
      resolventMat (A + ∑ i, ((x i : ℝ) : ℂ) • Tb i) (ζ r) p q) a b := by
  let T : (ι → ℝ) →L[ℝ] Matrix n n ℂ := ∑ i, (ContinuousLinearMap.proj i).smulRight (Tb i)
  have hT : ∀ x, T x = ∑ i, ((x i : ℝ) : ℂ) • Tb i := by
    intro x
    simp [T, Complex.coe_smul]
  have hH : ∀ x, (A + T x).IsHermitian := fun x => by
    rw [hT]; exact hA.add (heatBlock_isHermitian_sum Tb hTb x)
  have him : ∀ r ∈ Set.Ioo a b, (ζ r).im ≠ 0 := fun r hr h => by
    have := hζim r hr
    rw [h, abs_zero] at this
    linarith
  have hres : ∀ r x, resolventMat (A + T x) (ζ r) =
      Ring.inverse ((A - ζ r • (1 : Matrix n n ℂ)) + T x) := by
    intro r x
    rw [resolventMat, Matrix.nonsing_inv_eq_ringInverse]
    congr 1
    abel
  have hfun : (fun r (x : ι → ℝ) => resolventMat (A + ∑ i, ((x i : ℝ) : ℂ) • Tb i) (ζ r) p q) =
      fun r x => heatBlockEntry p q (Ring.inverse ((A - ζ r • (1 : Matrix n n ℂ)) + T x)) := by
    funext r x
    rw [heatBlockEntry_apply, ← hres, hT]
  rw [hfun]
  refine heatBlock_core T (fun r => A - ζ r • (1 : Matrix n n ℂ)) (-(c • (1 : Matrix n n ℂ)))
    (fun r => ((hζ r).smul_const (1 : Matrix n n ℂ)).const_sub A) (heatBlockEntry p q)
    (K := η⁻¹) (fun r hr x => ?_) (fun r hr x => ?_)
  · have : (A - ζ r • (1 : Matrix n n ℂ)) + T x = (A + T x) - ζ r • (1 : Matrix n n ℂ) := by abel
    rw [this]
    exact isUnit_sub_smul_one (hH x) (him r hr)
  · rw [← hres]
    exact norm_resolventMat_le (hH x) hη (hζim r hr)

end HeatBlockCore

/-- A constant function lies in the class. -/
private theorem heatBlock_const {ι : Type*} [Fintype ι] (c : ℂ) (a b : ℝ) :
    HeatClass (fun (_ : ℝ) (_ : ι → ℝ) => c) a b := by
  refine ⟨continuousOn_const, ⟨‖c‖, fun _ _ _ => le_rfl⟩,
    ⟨fun _ _ => 0, fun r _ x => hasDerivAt_const r c, continuousOn_const, 0,
      fun _ _ _ => norm_zero.le⟩,
    ⟨fun _ _ => 0, fun _ _ => 0, fun r _ x => hasFDerivAt_const c x,
      fun r _ x => hasFDerivAt_const (0 : (ι → ℝ) →L[ℝ] ℂ) x, continuousOn_const,
      continuousOn_const, 0,
      fun _ _ _ => ⟨ContinuousLinearMap.opNorm_zero.le, ContinuousLinearMap.opNorm_zero.le⟩⟩⟩

/-- A finite sum of members of the class lies in the class. -/
private theorem heatBlock_sum {ι κ : Type*} [Fintype ι] (s : Finset κ) (F : κ → ℝ → (ι → ℝ) → ℂ)
    {a b : ℝ} (h : ∀ i ∈ s, HeatClass (F i) a b) :
    HeatClass (fun r x => ∑ i ∈ s, F i r x) a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using heatBlock_const (ι := ι) 0 a b
  | insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      exact (h j (Finset.mem_insert_self j s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Every entry of a matrix-valued function lies in the class. -/
private def HeatMat {ι n : Type*} [Fintype ι] (M : ℝ → (ι → ℝ) → Matrix n n ℂ) (a b : ℝ) : Prop :=
  ∀ p q, HeatClass (fun r x => M r x p q) a b

private theorem heatMat_const {ι n : Type*} [Fintype ι] (C : Matrix n n ℂ) (a b : ℝ) :
    HeatMat (fun (_ : ℝ) (_ : ι → ℝ) => C) a b := fun p q => heatBlock_const (C p q) a b

private theorem heatMat_mul {ι n : Type*} [Fintype ι] [Fintype n]
    {M N : ℝ → (ι → ℝ) → Matrix n n ℂ} {a b : ℝ} (hM : HeatMat M a b) (hN : HeatMat N a b) :
    HeatMat (fun r x => M r x * N r x) a b := by
  intro p q
  simp only [Matrix.mul_apply]
  exact heatBlock_sum _ _ fun s _ => (hM p s).mul (hN s q)

private theorem heatMat_conjTranspose {ι n : Type*} [Fintype ι]
    {M : ℝ → (ι → ℝ) → Matrix n n ℂ} {a b : ℝ} (hM : HeatMat M a b) :
    HeatMat (fun r x => (M r x)ᴴ) a b := fun p q => by
  simp only [Matrix.conjTranspose_apply]
  exact (hM q p).star

private theorem heatMat_sgnMat {ι n : Type*} [Fintype ι]
    {M : ℝ → (ι → ℝ) → Matrix n n ℂ} {a b : ℝ} (hM : HeatMat M a b) (σ : Bool) :
    HeatMat (fun r x => sgnMat (M r x) σ) a b := by
  cases σ
  · simpa [sgnMat] using heatMat_conjTranspose hM
  · simpa [sgnMat] using hM

private theorem heatMat_prod_ofFn {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
    {a b : ℝ} : ∀ (k : ℕ) (f : Fin k → ℝ → (ι → ℝ) → Matrix n n ℂ),
      (∀ i, HeatMat (f i) a b) → HeatMat (fun r x => (List.ofFn fun i => f i r x).prod) a b
  | 0, f, _ => by simpa using heatMat_const (ι := ι) (1 : Matrix n n ℂ) a b
  | k + 1, f, h => by
      simp only [List.ofFn_succ, List.prod_cons]
      exact heatMat_mul (h 0) (heatMat_prod_ofFn k (fun i => f i.succ) fun i => h i.succ)

private theorem heatClass_trace {ι n : Type*} [Fintype ι] [Fintype n]
    {M : ℝ → (ι → ℝ) → Matrix n n ℂ} {a b : ℝ} (hM : HeatMat M a b) :
    HeatClass (fun r x => (M r x).trace) a b := by
  simp only [Matrix.trace, Matrix.diag]
  exact heatBlock_sum _ _ fun i _ => hM i i

private theorem heatMat_loopTr {W L k : ℕ} {ι : Type*} [Fintype ι]
    {X : ℝ → (ι → ℝ) → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} {a b : ℝ}
    (hX : HeatMat X a b) (c : Fin k → Fin L) (σ : Fin k → Bool) :
    HeatClass (fun r x => loopTr (X r x) c σ) a b := by
  unfold loopTr
  refine heatClass_trace (M := fun r x => (List.ofFn fun i : Fin k =>
    sgnMat (X r x) (σ i) * blockE W L (c i)).prod) ?_
  refine heatMat_prod_ofFn k (fun i r x => sgnMat (X r x) (σ i) * blockE W L (c i)) fun i => ?_
  exact heatMat_mul (heatMat_sgnMat hX (σ i)) (heatMat_const (blockE W L (c i)) a b)

/-- The map `r ↦ z_r` of (5.3) [fo:eq:characteristic] has the constant derivative
`-γ_g m`. -/
private theorem heatBlock_hasDerivAt_zChar (g E : ℝ) (m : ℂ) (r : ℝ) :
    HasDerivAt (zChar g E m) (-((gammaG g : ℝ) : ℂ) * m) r := by
  have h1 : HasDerivAt (fun t : ℝ => (1 - t) * gammaG g) (-gammaG g) r := by
    simpa using ((hasDerivAt_id r).const_sub 1).mul_const (gammaG g)
  have h2 := ((h1.ofReal_comp).mul_const m).const_add (E : ℂ)
  refine h2.congr_deriv ?_
  push_cast
  ring

/-- `Im z_r = (1 - r) γ_g Im m` at the characteristic of (5.3) [fo:eq:characteristic]. -/
private theorem heatBlock_im_zChar (g E : ℝ) (m : ℂ) (r : ℝ) :
    (zChar g E m r).im = (1 - r) * gammaG g * m.im := by
  simp [zChar]

/-- Entries of the resolvent of the Hermitian slice at the characteristic `z_r` lie in the class
on every `(a', b')` with `b' < 1`. -/
private theorem heatBlock_slice_entry (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hA : A.IsHermitian) (g E : ℝ) (m : ℂ) (hm : 0 < m.im) (p q : Fin L × Fin W) {a' b' : ℝ}
    (hb' : b' < 1) :
    HeatClass (fun r x => resolventMat (blockSlice W L A x) (zChar g E m r) p q) a' b' := by
  have hγ : 0 < gammaG g := by
    have : 0 < max 1 g := lt_max_of_lt_left one_pos
    unfold gammaG
    positivity
  have hb1 : 0 < 1 - b' := by linarith
  have hη : 0 < (1 - b') * gammaG g * m.im := by positivity
  have h := heatBlock_heatClass_entry A hA
    (fun i : Fin L × Fin W × Fin W => blockBasis W L i.1 (i.2.1, i.2.2))
    (fun i => blockBasis_isHermitian W L _ _) (zChar g E m) (-((gammaG g : ℝ) : ℂ) * m)
    (heatBlock_hasDerivAt_zChar g E m) hη (a := a') (b := b') (fun r hr => by
      rw [heatBlock_im_zChar]
      have hr1 : 0 < 1 - r := by linarith [hr.2]
      rw [abs_of_pos (by positivity)]
      have : 1 - b' ≤ 1 - r := by linarith [hr.2]
      gcongr) p q
  have hfun : (fun r (x : Ω W L) => resolventMat (blockSlice W L A x) (zChar g E m r) p q) =
      fun r x => resolventMat (A + ∑ i : Fin L × Fin W × Fin W,
        ((x i : ℝ) : ℂ) • blockBasis W L i.1 (i.2.1, i.2.2)) (zChar g E m r) p q := by
    funext r x
    rw [blockSlice_eq_sum]
  rw [hfun]
  exact h

/-- Resolvent loops at the characteristic `z_u` of (5.3) [fo:eq:characteristic] lie in the class
on every `(a', b')` with `b' < 1`. -/
theorem heatClass_loopTr (W L k : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hA : A.IsHermitian) (g E : ℝ) (m : ℂ) (hm : 0 < m.im) (a : Fin k → Fin L) (σ : Fin k → Bool)
    {a' b' : ℝ} (hb' : b' < 1) :
    HeatClass (fun r x => loopTr (resolventMat (blockSlice W L A x) (zChar g E m r)) a σ) a' b' := by
  exact heatMat_loopTr (fun p q => heatBlock_slice_entry W L A hA g E m hm p q hb') a σ

/-- Resolvent entries at the characteristic `z_u` lie in the class on every `(a', b')` with
`b' < 1`. -/
theorem heatClass_resolventEntry (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hA : A.IsHermitian) (g E : ℝ) (m : ℂ) (hm : 0 < m.im) (p q : Fin L × Fin W) {a' b' : ℝ}
    (hb' : b' < 1) :
    HeatClass (fun r x => resolventMat (blockSlice W L A x) (zChar g E m r) p q) a' b' := by
  exact heatBlock_slice_entry W L A hA g E m hm p q hb'

end LSBA
