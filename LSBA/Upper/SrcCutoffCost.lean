import LSBA.Upper.SrcCutoffPoint

/-!
# The source-derivative cost of the cutoff

(9.84) [su:eq:construction-cutoff-goals], Section 9.4.4 [su:sec:cutoff-estimates]: the
pointwise bound for `‖P v‖² ‖K‖²_HS ‖∇_v χ̂‖²` along `𝓗_v`. The matrix factors and the factor
`‖v̂‖² ≤ 2 W^{20} ‖P v̂‖²` have zero derivative along `𝓗_v` (`P`, `Q`, `‖P v‖` and `‖v‖` are fixed
along `𝓗_v`). The overlap factor costs at most `C` by (9.81)
[su:eq:common-overlap-cutoff-cost] with `‖K‖²_HS ≤ 32 ‖P v‖⁻² ‖Q v‖²`; the `Q P v` factor costs
at most `C ‖K‖²_HS ≤ C`; the output factor costs at most `C v_min⁻² ‖P v‖² ‖R_{[q-1,5]}‖²` on its
transition `‖v_{q-1}‖² < 2 v_min²` by (9.82) [su:eq:common-norm-cutoff-cost], and with (9.66)
[su:eq:active-chain-inverse] this is at most `C W⁶ g^{-2(q-6)} κ⁻²`. The derivative vanishes off
the topological support, where the chain `R_5, …, R_{q-2}` is regular.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Auxiliary lemmas -/

/-- `‖z + t y‖² = ‖z‖² + 2 t Re(z̄ y) + t² ‖y‖²` for real `t`. -/
private lemma SrcCutoffCost_norm_add_smul_sq (z y : ℂ) (t : ℝ) :
    ‖z + (t : ℂ) * y‖ ^ 2 = ‖z‖ ^ 2 + t * (2 * (star z * y).re) + t ^ 2 * ‖y‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- `t ↦ Σ_i ‖(B (v + t d))_i‖²` is the polynomial `‖B v‖² + 2 t Re((B v)* (B d)) + t² ‖B d‖²`
in the real parameter `t`. -/
private lemma SrcCutoffCost_sumSq_add_smul {W : ℕ} (B : Matrix (Fin W) (Fin W) ℂ)
    (v d : Fin W → ℂ) (t : ℝ) :
    ∑ i, ‖(B *ᵥ (v + t • d)) i‖ ^ 2 = ∑ i, ‖(B *ᵥ v) i‖ ^ 2 +
      t * (2 * (star (B *ᵥ v) ⬝ᵥ (B *ᵥ d)).re) + t ^ 2 * ∑ i, ‖(B *ᵥ d) i‖ ^ 2 := by
  have h : B *ᵥ (v + t • d) = B *ᵥ v + (t : ℂ) • (B *ᵥ d) := by
    rw [Matrix.mulVec_add, Complex.coe_smul, Matrix.mulVec_smul]
  simp only [h, Pi.add_apply, Pi.smul_apply, smul_eq_mul, SrcCutoffCost_norm_add_smul_sq,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  simp [dotProduct, Complex.re_sum, Finset.mul_sum]

/-- The derivative at `t = 0` of `t ↦ ‖B (v + t d)‖²` is `2 Re((B v)* (B d))`. -/
private lemma SrcCutoffCost_hasDerivAt_sumSq {W : ℕ} (B : Matrix (Fin W) (Fin W) ℂ)
    (v d : Fin W → ℂ) :
    HasDerivAt (fun t : ℝ => ∑ i, ‖(B *ᵥ (v + t • d)) i‖ ^ 2)
      (2 * (star (B *ᵥ v) ⬝ᵥ (B *ᵥ d)).re) 0 := by
  simp only [SrcCutoffCost_sumSq_add_smul]
  have h := ((hasDerivAt_const (0 : ℝ) (∑ i, ‖(B *ᵥ v) i‖ ^ 2)).add
    ((hasDerivAt_id (0 : ℝ)).mul_const (2 * (star (B *ᵥ v) ⬝ᵥ (B *ᵥ d)).re))).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (∑ i, ‖(B *ᵥ d) i‖ ^ 2))
  convert h using 1
  · funext t
    simp
  · simp


/-- Quotient rule at `0` for a quotient whose denominator has zero derivative and value `a ≠ 0`
at `0`. -/
private lemma SrcCutoffCost_ratio {N Dn : ℝ → ℝ} {N' D' a : ℝ} (hN : HasDerivAt N N' 0)
    (hD : HasDerivAt Dn D' 0) (hD' : D' = 0) (h0 : Dn 0 = a) (ha : a ≠ 0) :
    HasDerivAt (fun t => N t / Dn t) (N' / a) 0 := by
  subst h0 hD'
  have h := hN.div hD ha
  convert h using 1
  field_simp
  ring

/-- Chain rule at `0` for a differentiable outer function `S`. -/
private lemma SrcCutoffCost_comp_step {f S : ℝ → ℝ} {s' : ℝ} (hf : HasDerivAt f s' 0)
    (hS : Differentiable ℝ S) : HasDerivAt (fun t => S (f t)) (deriv S (f 0) * s') 0 :=
  (hS (f 0)).hasDerivAt.comp 0 hf

/-- For `m, a, b, c, e ∈ [0, 1]` and `a' = 0`, the product rule expression for the derivative of
`m a b c e` is at most `|b'| + |c'| + |e'|` in absolute value. -/
private lemma SrcCutoffCost_prod_bound {m a a' b c e b' c' e' : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (ha' : a' = 0) :
    |m * (((a' * b + a * b') * c + a * b * c') * e + a * b * c * e')| ≤ |b'| + |c'| + |e'| := by
  subst ha'
  have h1 : |a * b' * c * e| ≤ |b'| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hc0, abs_of_nonneg he0]
    have := abs_nonneg b'
    calc a * |b'| * c * e ≤ 1 * |b'| * 1 * 1 := by gcongr
      _ = |b'| := by ring
  have h2 : |a * b * c' * e| ≤ |c'| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hb0, abs_of_nonneg he0]
    have := abs_nonneg c'
    calc a * b * |c'| * e ≤ 1 * 1 * |c'| * 1 := by gcongr
      _ = |c'| := by ring
  have h3 : |a * b * c * e'| ≤ |e'| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hb0, abs_of_nonneg hc0]
    have := abs_nonneg e'
    calc a * b * c * |e'| ≤ 1 * 1 * 1 * |e'| := by gcongr
      _ = |e'| := by ring
  have hX : ((0 * b + a * b') * c + a * b * c') * e + a * b * c * e' =
      a * b' * c * e + a * b * c' * e + a * b * c * e' := by ring
  rw [abs_mul, abs_of_nonneg hm0, hX]
  calc m * |a * b' * c * e + a * b * c' * e + a * b * c * e'|
      ≤ |a * b' * c * e + a * b * c' * e + a * b * c * e'| :=
        mul_le_of_le_one_left (abs_nonneg _) hm1
    _ ≤ |a * b' * c * e| + |a * b * c' * e| + |a * b * c * e'| := abs_add_three _ _ _
    _ ≤ |b'| + |c'| + |e'| := by linarith


/-- The derivative at `0` of `t ↦ m F₁(t) F₂(t) F₃(t) F₄(t)`, with `m` and the values `F_i(0)` in
`[0, 1]` and `F₁' = 0`, exists and is at most `|F₂'| + |F₃'| + |F₄'|` in absolute value. -/
private lemma SrcCutoffCost_prod4 {F1 F2 F3 F4 : ℝ → ℝ} {m f1 f2 f3 f4 : ℝ}
    (h1 : HasDerivAt F1 f1 0) (h2 : HasDerivAt F2 f2 0) (h3 : HasDerivAt F3 f3 0)
    (h4 : HasDerivAt F4 f4 0) (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hF1 : 0 ≤ F1 0 ∧ F1 0 ≤ 1)
    (hF2 : 0 ≤ F2 0 ∧ F2 0 ≤ 1) (hF3 : 0 ≤ F3 0 ∧ F3 0 ≤ 1) (hF4 : 0 ≤ F4 0 ∧ F4 0 ≤ 1)
    (hf1 : f1 = 0) :
    ∃ D, HasDerivAt (fun t => m * (F1 t * F2 t * F3 t * F4 t)) D 0 ∧
      |D| ≤ |f2| + |f3| + |f4| :=
  ⟨_, (((h1.mul h2).mul h3).mul h4).const_mul m,
    SrcCutoffCost_prod_bound hm0 hm1 hF1.1 hF1.2 hF2.1 hF2.2 hF3.1 hF3.2 hF4.1 hF4.2 hf1⟩

/-- `stepDown` takes values in `[0, 1]`. -/
private lemma SrcCutoffCost_stepDown_mem (s : ℝ) : 0 ≤ stepDown s ∧ stepDown s ≤ 1 := by
  obtain ⟨-, -, -, -, hr, -⟩ := step_spec
  exact ⟨(hr s).1, (hr s).2.1⟩

/-- `normCut L Y` takes values in `[0, 1]`. -/
private lemma SrcCutoffCost_normCut_mem {n : Type*} [Fintype n] [DecidableEq n] (L : ℝ)
    (Y : Matrix n n ℂ) : 0 ≤ normCut L Y ∧ normCut L Y ≤ 1 := by
  unfold normCut
  split_ifs
  · exact SrcCutoffCost_stepDown_mem _
  · exact ⟨le_rfl, zero_le_one⟩

/-- Products of numbers in `[0, 1]` lie in `[0, 1]`. -/
private lemma SrcCutoffCost_mem_mul {a b : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
    0 ≤ a * b ∧ a * b ≤ 1 :=
  ⟨mul_nonneg ha.1 hb.1, (mul_le_of_le_one_left hb.1 ha.2).trans hb.2⟩

/-- Finite products of numbers in `[0, 1]` lie in `[0, 1]`. -/
private lemma SrcCutoffCost_mem_prod {s : Finset ℕ} {f : ℕ → ℝ} (h : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) :
    0 ≤ ∏ i ∈ s, f i ∧ ∏ i ∈ s, f i ≤ 1 :=
  ⟨Finset.prod_nonneg fun i hi => (h i hi).1,
    Finset.prod_le_one₀ (fun i hi => (h i hi).1) fun i hi => (h i hi).2⟩

/-- The matrix cutoff of Section 9.4.4 [su:sec:cutoff-estimates] takes values in `[0, 1]`. -/
private lemma SrcCutoffCost_matCut_mem {W q : ℕ} {g E : ℝ} {R P : Matrix (Fin W) (Fin W) ℂ}
    {c : CutLevels} (ω : Ω W q) :
    0 ≤ matCut W g E q R P c ω ∧ matCut W g E q R P c ω ≤ 1 := by
  unfold matCut regCut
  repeat' first
    | exact SrcCutoffCost_normCut_mem _ _
    | exact SrcCutoffCost_stepDown_mem _
    | apply SrcCutoffCost_mem_mul
    | (apply SrcCutoffCost_mem_prod; intro i _)


/-- The derivative in `v` of the cutoff `χ̂` along a direction `d` with `P d = d` and
`Re(v* d) = 0`, by the product rule over the four source factors of Section 9.4.4
[su:sec:cutoff-estimates]: the factor `stepUp (2 W^{20} ‖P v‖² / ‖v‖²)` has zero derivative, the
overlap, `Q P v` and output factors contribute `C_φ` times the derivative of their argument, as in
(9.81) [su:eq:common-overlap-cutoff-cost] and (9.82) [su:eq:common-norm-cutoff-cost], and the
output step is constant for `‖v_{q-1}‖² ≥ 2 κ² ‖P v‖²`. -/
private lemma SrcCutoffCost_lineDeriv_le {W q : ℕ} {g E Cφ : ℝ} {R P : Matrix (Fin W) (Fin W) ℂ}
    {c : CutLevels} (ω : Ω W q) {v d : Fin W → ℂ} {Q M : Matrix (Fin W) (Fin W) ℂ}
    (hQ : retProj W g E q R c.t ω = Q) (hM : chartProd W g E q R ω (q - 1) = M)
    (hSd : Differentiable ℝ stepDown) (hSu : Differentiable ℝ stepUp)
    (hr : ∀ s, 0 ≤ stepDown s ∧ stepDown s ≤ 1 ∧ 0 ≤ stepUp s ∧ stepUp s ≤ 1)
    (hu : ∀ s, 2 ≤ s → stepUp s = 1)
    (hb : ∀ s, |deriv stepDown s| ≤ Cφ ∧ |deriv stepUp s| ≤ Cφ)
    (hLov : 0 < c.Lov) (hkOut : 0 < c.kOut) (hnP : 0 < ∑ i, ‖(P *ᵥ v) i‖ ^ 2)
    (hnV : 0 < ∑ i, ‖v i‖ ^ 2) (hdP : (star (P *ᵥ v) ⬝ᵥ (P *ᵥ d)).re = 0)
    (hdV : (star v ⬝ᵥ d).re = 0) :
    |lineDeriv ℝ (fun w => srcCut W g E q R P c ω w) v d| ≤
      Cφ * |2 * (star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ d)).re / (c.Lov * ∑ i, ‖(P *ᵥ v) i‖ ^ 2)| +
      Cφ * |16 * (2 * (star ((Q * P) *ᵥ v) ⬝ᵥ ((Q * P) *ᵥ d)).re) / ∑ i, ‖(P *ᵥ v) i‖ ^ 2| +
      (if ∑ i, ‖(M *ᵥ v) i‖ ^ 2 < 2 * c.kOut ^ 2 * ∑ i, ‖(P *ᵥ v) i‖ ^ 2 then
        Cφ * |2 * (star (M *ᵥ v) ⬝ᵥ (M *ᵥ d)).re / (c.kOut ^ 2 * ∑ i, ‖(P *ᵥ v) i‖ ^ 2)|
      else 0) := by
  subst hQ hM
  have hm := SrcCutoffCost_matCut_mem (g := g) (E := E) (R := R) (P := P) (c := c) ω
  have hkk : 0 < c.kOut ^ 2 := by positivity
  have hNP : HasDerivAt (fun t : ℝ => ∑ i, ‖(P *ᵥ (v + t • d)) i‖ ^ 2) 0 0 := by
    simpa [hdP] using SrcCutoffCost_hasDerivAt_sumSq P v d
  have hNV : HasDerivAt (fun t : ℝ => ∑ i, ‖(v + t • d) i‖ ^ 2) 0 0 := by
    simpa [hdV] using SrcCutoffCost_hasDerivAt_sumSq (1 : Matrix (Fin W) (Fin W) ℂ) v d
  have hNQ := SrcCutoffCost_hasDerivAt_sumSq (retProj W g E q R c.t ω) v d
  have hNQP : HasDerivAt (fun t : ℝ =>
      ∑ i, ‖(retProj W g E q R c.t ω *ᵥ (P *ᵥ (v + t • d))) i‖ ^ 2)
      (2 * (star ((retProj W g E q R c.t ω * P) *ᵥ v) ⬝ᵥ
        ((retProj W g E q R c.t ω * P) *ᵥ d)).re) 0 := by
    simpa only [Matrix.mulVec_mulVec] using
      SrcCutoffCost_hasDerivAt_sumSq (retProj W g E q R c.t ω * P) v d
  have hNM := SrcCutoffCost_hasDerivAt_sumSq (chartProd W g E q R ω (q - 1)) v d
  have hs1 := SrcCutoffCost_ratio (N := fun t : ℝ => 2 * (W : ℝ) ^ 20 *
    ∑ i, ‖(P *ᵥ (v + t • d)) i‖ ^ 2) (hNP.const_mul _) hNV rfl (by simp) hnV.ne'
  have hs2 := SrcCutoffCost_ratio (N := fun t : ℝ => ∑ i, ‖(retProj W g E q R c.t ω *ᵥ
    (v + t • d)) i‖ ^ 2) hNQ (hNP.const_mul c.Lov) (mul_zero _) (a := c.Lov * ∑ i, ‖(P *ᵥ v) i‖ ^ 2)
    (by simp) (mul_pos hLov hnP).ne'
  have hs3 := SrcCutoffCost_ratio (N := fun t : ℝ => 16 * ∑ i, ‖(retProj W g E q R c.t ω *ᵥ
    (P *ᵥ (v + t • d))) i‖ ^ 2) (hNQP.const_mul 16) hNP rfl (a := ∑ i, ‖(P *ᵥ v) i‖ ^ 2)
    (by simp) hnP.ne'
  have hs4 := SrcCutoffCost_ratio (N := fun t : ℝ => ∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ
    (v + t • d)) i‖ ^ 2) hNM (hNP.const_mul (c.kOut ^ 2)) (mul_zero _) (a := c.kOut ^ 2 *
    ∑ i, ‖(P *ᵥ v) i‖ ^ 2) (by simp) (mul_pos hkk hnP).ne'
  have hf1 := SrcCutoffCost_comp_step hs1 hSu
  have hf2 := SrcCutoffCost_comp_step hs2 hSd
  have hf3 := SrcCutoffCost_comp_step hs3 hSd
  have hf4 := SrcCutoffCost_comp_step hs4 hSu
  obtain ⟨D, hD, hDb⟩ := SrcCutoffCost_prod4 hf1 hf2 hf3 hf4 hm.1 hm.2 ⟨(hr _).2.2.1, (hr _).2.2.2⟩
    ⟨(hr _).1, (hr _).2.1⟩ ⟨(hr _).1, (hr _).2.1⟩ ⟨(hr _).2.2.1, (hr _).2.2.2⟩ (by simp)
  have hl : lineDeriv ℝ (fun w => srcCut W g E q R P c ω w) v d = D := by
    unfold lineDeriv srcCut srcCutV
    exact hD.deriv
  rw [hl]
  refine hDb.trans ?_
  simp only [zero_smul, add_zero]
  refine add_le_add (add_le_add ?_ ?_) ?_
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hb _).1 (abs_nonneg _)
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hb _).1 (abs_nonneg _)
  · set nP := ∑ i, ‖(P *ᵥ v) i‖ ^ 2 with hnPd
    set nO := ∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2 with hnOd
    split_ifs with h
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hb _).2 (abs_nonneg _)
    · have hs : 2 ≤ nO / (c.kOut ^ 2 * nP) := by
        rw [le_div_iff₀ (mul_pos hkk hnP)]
        linarith [not_lt.mp h]
      have hmax : IsLocalMax stepUp (nO / (c.kOut ^ 2 * nP)) :=
        Filter.Eventually.of_forall fun x => by
          rw [hu _ hs]
          exact (hr x).2.2.2
      rw [hmax.deriv_eq_zero, zero_mul, abs_zero]


/-- `Σ |x_i|²` is the square of `l2Norm x`. -/
private lemma SrcCutoffCost_l2Norm_sq {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    l2Norm x ^ 2 = ∑ i, ‖x i‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- `Re(a* a) = Σ_i ‖a_i‖²`. -/
private lemma SrcCutoffCost_re_dot_self {W : ℕ} (a : Fin W → ℂ) :
    (star a ⬝ᵥ a).re = ∑ i, ‖a i‖ ^ 2 := by
  simp [dotProduct, Complex.re_sum, Complex.sq_norm, Complex.normSq_apply]

/-- `Re(a* b) = Re(b* a)`. -/
private lemma SrcCutoffCost_ip_comm {W : ℕ} (a b : Fin W → ℂ) :
    (star a ⬝ᵥ b).re = (star b ⬝ᵥ a).re := by
  simp only [dotProduct, Complex.re_sum, Pi.star_apply, Complex.star_def, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `(P a)* b = a* (P b)` for Hermitian `P`. -/
private lemma SrcCutoffCost_ip_mulVec {W : ℕ} {P : Matrix (Fin W) (Fin W) ℂ}
    (hP : P.IsHermitian) (a b : Fin W → ℂ) : star (P *ᵥ a) ⬝ᵥ b = star a ⬝ᵥ (P *ᵥ b) := by
  rw [Matrix.star_mulVec, hP.eq, Matrix.dotProduct_mulVec]

/-- An orthogonal projection does not increase `Σ |x_i|²`. -/
private lemma SrcCutoffCost_sumSq_proj_le {W : ℕ} {P : Matrix (Fin W) (Fin W) ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (x : Fin W → ℂ) :
    ∑ i, ‖(P *ᵥ x) i‖ ^ 2 ≤ ∑ i, ‖x i‖ ^ 2 := by
  have hn : ‖P‖ * ‖P‖ = ‖P‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hP.eq, hPP]
  have h1 : ‖P‖ ≤ 1 := by nlinarith [norm_nonneg P]
  have hx : 0 ≤ l2Norm x := Real.sqrt_nonneg _
  have h2 : l2Norm (P *ᵥ x) ≤ l2Norm x :=
    (l2Norm_mulVec_le P x).trans (mul_le_of_le_one_left hx h1)
  have h3 : l2Norm (P *ᵥ x) ^ 2 ≤ l2Norm x ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
  simpa only [SrcCutoffCost_l2Norm_sq] using h3

/-- For `P v ≠ 0`, `tangProj P v w` lies in `ran P`, is orthogonal to `v` and to `P v` for
`Re(a* b)`, and has norm at most that of `w`. -/
private lemma SrcCutoffCost_tangProj_props {W : ℕ} {P : Matrix (Fin W) (Fin W) ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) {v : Fin W → ℂ} (hnP : 0 < ∑ i, ‖(P *ᵥ v) i‖ ^ 2)
    (w : Fin W → ℂ) :
    P *ᵥ tangProj P v w = tangProj P v w ∧ (star v ⬝ᵥ tangProj P v w).re = 0 ∧
      (star (P *ᵥ v) ⬝ᵥ (P *ᵥ tangProj P v w)).re = 0 ∧
      ∑ i, ‖(tangProj P v w) i‖ ^ 2 ≤ ∑ i, ‖w i‖ ^ 2 := by
  set Pv := P *ᵥ v with hPvdef
  set s : ℝ := ∑ i, ‖Pv i‖ ^ 2 with hsdef
  have hPvP : P *ᵥ Pv = Pv := by rw [hPvdef, Matrix.mulVec_mulVec, hPP]
  have hT : tangProj P v w = P *ᵥ w - (((star Pv ⬝ᵥ w).re / s : ℝ) : ℂ) • Pv := rfl
  have hPvs : (star Pv ⬝ᵥ Pv).re = s := SrcCutoffCost_re_dot_self Pv
  have hvPv : (star v ⬝ᵥ Pv).re = s := by
    have h := SrcCutoffCost_ip_mulVec hP v Pv
    rw [hPvP] at h
    rw [← h, hPvs]
  have hvP : ∀ x, (star v ⬝ᵥ (P *ᵥ x)).re = (star Pv ⬝ᵥ x).re := fun x => by
    rw [← SrcCutoffCost_ip_mulVec hP]
  have hPvPw : (star Pv ⬝ᵥ (P *ᵥ w)).re = (star Pv ⬝ᵥ w).re := by
    rw [← SrcCutoffCost_ip_mulVec hP, hPvP]
  have hsne : s ≠ 0 := hnP.ne'
  have h1 : P *ᵥ tangProj P v w = tangProj P v w := by
    rw [hT, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hPP, hPvP]
  have h3 : (star Pv ⬝ᵥ (P *ᵥ tangProj P v w)).re = 0 := by
    rw [h1, hT, dotProduct_sub, dotProduct_smul, Complex.sub_re, smul_eq_mul, Complex.re_ofReal_mul,
      hPvPw, hPvs]
    field_simp
    ring
  refine ⟨h1, ?_, h3, ?_⟩
  · rw [hT, dotProduct_sub, dotProduct_smul, Complex.sub_re, smul_eq_mul, Complex.re_ofReal_mul,
      hvP, hvPv]
    field_simp
    ring
  · have hex := SrcCutoffCost_sumSq_add_smul (1 : Matrix (Fin W) (Fin W) ℂ) (P *ᵥ w) Pv
      (-((star Pv ⬝ᵥ w).re / s))
    simp only [Matrix.one_mulVec] at hex
    have hcomm : (star (P *ᵥ w) ⬝ᵥ Pv).re = (star Pv ⬝ᵥ w).re := by
      rw [SrcCutoffCost_ip_comm, hPvPw]
    have hTe : tangProj P v w = P *ᵥ w + (-((star Pv ⬝ᵥ w).re / s)) • Pv := by
      rw [hT, sub_eq_add_neg, ← neg_smul, ← Complex.coe_smul]
      push_cast
      rfl
    have hpr := SrcCutoffCost_sumSq_proj_le hP hPP w
    have hc2 : 0 ≤ (star Pv ⬝ᵥ w).re ^ 2 / s := div_nonneg (sq_nonneg _) hnP.le
    have hid : (-((star Pv ⬝ᵥ w).re / s)) * (2 * (star Pv ⬝ᵥ w).re) +
        (-((star Pv ⬝ᵥ w).re / s)) ^ 2 * s = -((star Pv ⬝ᵥ w).re ^ 2 / s) := by
      field_simp
      ring
    rw [hTe, hex, hcomm]
    have hsum : ∑ i, ‖(Pv) i‖ ^ 2 = s := rfl
    rw [hsum]
    linarith


/-- `tangProj P v` is additive. -/
private lemma SrcCutoffCost_tangProj_add {W : ℕ} (P : Matrix (Fin W) (Fin W) ℂ)
    (v x y : Fin W → ℂ) :
    tangProj P v (x + y) = tangProj P v x + tangProj P v y := by
  unfold tangProj
  rw [Matrix.mulVec_add, dotProduct_add, Complex.add_re, add_div, Complex.ofReal_add, add_smul]
  abel

/-- `tangProj P v` is homogeneous for real scalars. -/
private lemma SrcCutoffCost_tangProj_smul {W : ℕ} (P : Matrix (Fin W) (Fin W) ℂ)
    (v x : Fin W → ℂ) (r : ℝ) : tangProj P v (r • x) = r • tangProj P v x := by
  unfold tangProj
  rw [Matrix.mulVec_smul, dotProduct_smul, Complex.smul_re, smul_eq_mul, mul_div_assoc,
    Complex.ofReal_mul, mul_smul, smul_sub, Complex.coe_smul]

/-- A real-linear functional `ℓ` with `ℓ(x)² ≤ β ‖x‖²` has `Σ_j (ℓ(e_j)² + ℓ(i e_j)²) ≤ β`. -/
private lemma SrcCutoffCost_sum_basis {W : ℕ} (ℓ : (Fin W → ℂ) →ₗ[ℝ] ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (h : ∀ x, ℓ x ^ 2 ≤ β * ∑ i, ‖x i‖ ^ 2) :
    ∑ j, (ℓ (Pi.single j 1) ^ 2 + ℓ (Pi.single j Complex.I) ^ 2) ≤ β := by
  set w : Fin W → ℂ := fun j => (ℓ (Pi.single j 1) : ℂ) + (ℓ (Pi.single j Complex.I) : ℂ) *
    Complex.I with hw
  have hdec : ∀ u : Fin W → ℂ, u = ∑ j, ((u j).re • (Pi.single j (1 : ℂ) : Fin W → ℂ) +
      (u j).im • (Pi.single j Complex.I : Fin W → ℂ)) := fun u => by
    funext i
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_ite,
      smul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    apply Complex.ext <;> simp
  set S : ℝ := ∑ j, (ℓ (Pi.single j 1) ^ 2 + ℓ (Pi.single j Complex.I) ^ 2) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => by positivity
  have hℓw : ℓ w = S := by
    conv_lhs => rw [hdec w]
    simp only [map_sum, map_add, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hw]
    ring
  have hnw : ∑ i, ‖w i‖ ^ 2 = S := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hw, Complex.sq_norm, Complex.normSq_apply]
    ring
  have h2 := h w
  rw [hℓw, hnw] at h2
  rcases hS0.eq_or_lt with h0 | h0
  · rw [← h0]; exact hβ
  · nlinarith


/-- Cauchy–Schwarz: `Re(a* y)² ≤ ‖a‖² ‖y‖²`. -/
private lemma SrcCutoffCost_dot_sq_le {W : ℕ} (a y : Fin W → ℂ) :
    (star a ⬝ᵥ y).re ^ 2 ≤ (∑ i, ‖a i‖ ^ 2) * ∑ i, ‖y i‖ ^ 2 := by
  have h1 : |(star a ⬝ᵥ y).re| ≤ ∑ i, ‖a i‖ * ‖y i‖ := by
    calc |(star a ⬝ᵥ y).re| ≤ ‖star a ⬝ᵥ y‖ := Complex.abs_re_le_norm _
      _ ≤ ∑ i, ‖(star a) i * y i‖ := norm_sum_le _ _
      _ = ∑ i, ‖a i‖ * ‖y i‖ := by simp
  calc (star a ⬝ᵥ y).re ^ 2 = |(star a ⬝ᵥ y).re| ^ 2 := (sq_abs _).symm
    _ ≤ (∑ i, ‖a i‖ * ‖y i‖) ^ 2 := by gcongr
    _ ≤ (∑ i, ‖a i‖ ^ 2) * ∑ i, ‖y i‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- The sum over the real orthonormal basis of the squares of the tangential derivatives of
`d ↦ Re(a* (B d))`, where `‖B x‖² ≤ β ‖x‖²`, is at most `β ‖a‖²`. -/
private lemma SrcCutoffCost_sum_dir {W : ℕ} {P : Matrix (Fin W) (Fin W) ℂ} (hP : P.IsHermitian)
    (hPP : P * P = P) {v : Fin W → ℂ} (hnP : 0 < ∑ i, ‖(P *ᵥ v) i‖ ^ 2)
    (B : Matrix (Fin W) (Fin W) ℂ) (a : Fin W → ℂ) {β : ℝ} (hβ : 0 ≤ β)
    (hB : ∀ x, ∑ i, ‖(B *ᵥ x) i‖ ^ 2 ≤ β * ∑ i, ‖x i‖ ^ 2) :
    ∑ j, ((star a ⬝ᵥ (B *ᵥ tangProj P v (Pi.single j 1))).re ^ 2 +
      (star a ⬝ᵥ (B *ᵥ tangProj P v (Pi.single j Complex.I))).re ^ 2) ≤
      β * ∑ i, ‖a i‖ ^ 2 := by
  let ℓ : (Fin W → ℂ) →ₗ[ℝ] ℝ :=
    { toFun := fun u => (star a ⬝ᵥ (B *ᵥ tangProj P v u)).re
      map_add' := fun x y => by
        simp only [SrcCutoffCost_tangProj_add, Matrix.mulVec_add, dotProduct_add, Complex.add_re]
      map_smul' := fun r x => by
        simp only [SrcCutoffCost_tangProj_smul, Matrix.mulVec_smul, dotProduct_smul,
          Complex.smul_re, smul_eq_mul, RingHom.id_apply] }
  have ha0 : 0 ≤ ∑ i, ‖a i‖ ^ 2 := by positivity
  refine SrcCutoffCost_sum_basis ℓ (β := β * ∑ i, ‖a i‖ ^ 2) (by positivity) fun x => ?_
  change (star a ⬝ᵥ (B *ᵥ tangProj P v x)).re ^ 2 ≤ _
  have h1 := SrcCutoffCost_dot_sq_le a (B *ᵥ tangProj P v x)
  have h2 := hB (tangProj P v x)
  have h3 := (SrcCutoffCost_tangProj_props hP hPP hnP x).2.2.2
  calc (star a ⬝ᵥ (B *ᵥ tangProj P v x)).re ^ 2
      ≤ (∑ i, ‖a i‖ ^ 2) * ∑ i, ‖(B *ᵥ tangProj P v x) i‖ ^ 2 := h1
    _ ≤ (∑ i, ‖a i‖ ^ 2) * (β * ∑ i, ‖(tangProj P v x) i‖ ^ 2) := by gcongr
    _ ≤ (∑ i, ‖a i‖ ^ 2) * (β * ∑ i, ‖x i‖ ^ 2) := by gcongr
    _ = β * (∑ i, ‖a i‖ ^ 2) * ∑ i, ‖x i‖ ^ 2 := by ring


/-- `‖M x‖² ≤ ‖M‖²_HS ‖x‖²` (Cauchy–Schwarz row by row). -/
private lemma SrcCutoffCost_sumSq_mulVec_le {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) (x : n → ℂ) :
    ∑ i, ‖(M *ᵥ x) i‖ ^ 2 ≤ hsSq M * ∑ j, ‖x j‖ ^ 2 := by
  unfold hsSq
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ‖(M *ᵥ x) i‖ ^ 2 ≤ (∑ j, ‖M i j‖ * ‖x j‖) ^ 2 := by
        gcongr
        simp only [Matrix.mulVec, dotProduct]
        exact (norm_sum_le _ _).trans (by simp)
    _ ≤ (∑ j, ‖M i j‖ ^ 2) * ∑ j, ‖x j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- If `‖A‖²_HS ≤ a⁶` with `a ≥ 0`, then the operator norm of `A` is at most `a³`. -/
private lemma SrcCutoffCost_norm_le_cube {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) {a : ℝ} (ha : 0 ≤ a) (h : hsSq A ≤ a ^ 6) : ‖A‖ ≤ a ^ 3 := by
  have h0 : 0 ≤ hsSq A := by unfold hsSq; positivity
  have hs : ‖A‖ ≤ Real.sqrt (hsSq A) := by
    rw [Matrix.l2_opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    change ‖Matrix.toEuclideanLin A x‖ ≤ _ * ‖x‖
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_mul h0]
    exact Real.sqrt_le_sqrt (SrcCutoffCost_sumSq_mulVec_le A x.ofLp)
  calc ‖A‖ ≤ Real.sqrt (hsSq A) := hs
    _ ≤ Real.sqrt ((a ^ 3) ^ 2) := Real.sqrt_le_sqrt (by rw [← pow_mul]; exact h)
    _ = a ^ 3 := Real.sqrt_sq (by positivity)

open scoped ComplexOrder in
/-- For a positive semidefinite `M`, `k ≥ 1` and `a ≥ 0`, `Re Tr M^k ≤ a^k` gives `‖M‖ ≤ a`: every
eigenvalue `λ ≥ 0` has `λ^k ≤ Σ_i λ_i^k = Re Tr M^k`. -/
private lemma SrcCutoffCost_norm_le_of_trace_pow {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.PosSemidef) {k : ℕ} (hk : k ≠ 0) {a : ℝ} (ha : 0 ≤ a)
    (h : (M ^ k).trace.re ≤ a ^ k) : ‖M‖ ≤ a := by
  have hl : ∀ i, 0 ≤ hM.1.eigenvalues i := hM.eigenvalues_nonneg
  have htr : (M ^ k).trace.re = ∑ i, hM.1.eigenvalues i ^ k := by
    conv_lhs => rw [hM.1.spectral_theorem, ← map_pow, Unitary.conjStarAlgAut_apply,
      Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul, Matrix.diagonal_pow,
      Matrix.trace_diagonal, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [← Complex.ofReal_pow]
  have hnorm : ‖M‖ = ‖(RCLike.ofReal ∘ hM.1.eigenvalues : n → ℂ)‖ := by
    conv_lhs => rw [hM.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
      Matrix.l2_opNorm_diagonal]
  rw [hnorm]
  refine (pi_norm_le_iff_of_nonneg ha).mpr fun i => ?_
  have hi : hM.1.eigenvalues i ^ k ≤ a ^ k := by
    rw [htr] at h
    exact (Finset.single_le_sum (fun j _ => pow_nonneg (hl j) k) (Finset.mem_univ i)).trans h
  have hi' := (pow_le_pow_iff_left₀ (hl i) ha hk).mp hi
  simpa [abs_of_nonneg (hl i)] using hi'


open scoped ComplexOrder in
/-- On `CutSupp`, for `0 < t`, `64 L_ov ≤ 1`, `k ≥ 1` and `32 t² W^{34} ≤ κ²`: `P v ≠ 0`; `Q` is an
orthogonal projection; `‖P v‖² ‖K‖²_HS ≤ 32 ‖Q v‖²` and `‖K‖²_HS ≤ 1`, from (9.19)
[su:eq:generator-admissibility] and (9.21) [su:eq:normalized-generator-costs]; and
`‖R_{[q-1,5]}‖² ≤ W⁶ g^{-2(q-6)}`, from (9.66) [su:eq:active-chain-inverse]. -/
private lemma SrcCutoffCost_core {W q : ℕ} {g E : ℝ} {R P : Matrix (Fin W) (Fin W) ℂ}
    {c : CutLevels} {ω : Ω W q} {v : Fin W → ℂ} (hW : 1 ≤ W) (hq : 7 ≤ q) (hg : 0 < g)
    (hR : R.IsHermitian) (hP : P.IsHermitian) (hPP : P * P = P) (hv : v ≠ 0) (ht : 0 < c.t)
    (hLov' : 64 * c.Lov ≤ 1) (hkP : 1 ≤ c.kP)
    (herr : 32 * c.t ^ 2 * (W : ℝ) ^ 34 ≤ c.kOut ^ 2) (h : CutSupp W g E q R P c ω v) :
    0 < ∑ i, ‖(P *ᵥ v) i‖ ^ 2 ∧
    (retProj W g E q R c.t ω).IsHermitian ∧
    retProj W g E q R c.t ω * retProj W g E q R c.t ω = retProj W g E q R c.t ω ∧
    hsSq (smallGen W g E q R c.t P ω v) * ∑ i, ‖(P *ᵥ v) i‖ ^ 2 ≤
      32 * ∑ i, ‖(retProj W g E q R c.t ω *ᵥ v) i‖ ^ 2 ∧
    hsSq (smallGen W g E q R c.t P ω v) ≤ 1 ∧
    ‖chartProd W g E q R ω (q - 1)‖ ^ 2 ≤ (W : ℝ) ^ 6 / g ^ (2 * (q - 6)) := by
  obtain ⟨h1, h2, h3, ⟨hT, hTs⟩, ⟨hHu, hHs⟩, -, -, hcomp, -, -, hvP, hQv, hQPv, hout⟩ := h
  have hRu : ∀ j, 5 ≤ j → j ≤ q - 1 → IsUnit (chartR W g E q R ω j) := fun j h5 hj => by
    rcases Nat.lt_or_ge j (q - 1) with hj' | hj'
    · exact (h1 j h5 (by omega)).1
    · obtain rfl : j = q - 1 := by omega
      exact h2.1
  have hC : ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω m) := fun m hm => (h3 m hm).1
  obtain ⟨hQh, hQQ, -⟩ := trace_retProj (g := g) (E := E) R c.t ω hT
  set Q := retProj W g E q R c.t ω with hQ
  set nP := ∑ i, ‖(P *ᵥ v) i‖ ^ 2 with hnP
  have hv0 : 0 < ∑ i, ‖v i‖ ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2)
      (Finset.single_le_sum (f := fun j => ‖v j‖ ^ 2) (fun j _ => by positivity)
        (Finset.mem_univ i))
  have hPv : P *ᵥ v ≠ 0 := by
    intro h0
    have : nP = 0 := by rw [hnP, h0]; simp
    rw [this, mul_zero] at hvP
    linarith
  have hnP0 : 0 < nP := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hPv
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2)
      (Finset.single_le_sum (f := fun j => ‖(P *ᵥ v) j‖ ^ 2) (fun j _ => by positivity)
        (Finset.mem_univ i))
  -- `‖(1 - P) Q‖² ≤ 1/8` from the compatibility cut
  have h1P : (1 - P)ᴴ = 1 - P := by rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP.eq]
  have h1PP : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, mul_sub, mul_sub, hPP, one_mul, mul_one, one_mul]
    abel
  have hBB : ((1 - P) * Q)ᴴ * ((1 - P) * Q) = Q * (1 - P) * Q := by
    rw [Matrix.conjTranspose_mul, h1P, hQh.eq, Matrix.mul_assoc, ← Matrix.mul_assoc (1 - P), h1PP,
      Matrix.mul_assoc]
  have hpsd : (Q * (1 - P) * Q).PosSemidef := hBB ▸ Matrix.posSemidef_conjTranspose_mul_self _
  have hM : ‖Q * (1 - P) * Q‖ ≤ 1 / 8 := by
    refine SrcCutoffCost_norm_le_of_trace_pow hpsd (k := c.kP) (by omega) (by norm_num) ?_
    rw [div_pow, one_pow, le_div_iff₀ (by positivity)]
    linarith
  have hD2 : ‖(1 - P) * Q‖ ^ 2 ≤ 1 / 8 := by
    rw [sq, ← Matrix.l2_opNorm_conjTranspose_mul_self, hBB]
    exact hM
  -- `B_Q ≥ 3/4`
  have hQP : l2Norm (Q *ᵥ (P *ᵥ v)) ^ 2 / l2Norm (P *ᵥ v) ^ 2 ≤ 1 / 8 := by
    rw [SrcCutoffCost_l2Norm_sq, SrcCutoffCost_l2Norm_sq, div_le_iff₀ hnP0]
    linarith
  have hBQl : ∀ u : Fin W → ℂ, Q *ᵥ u = u →
      (3 / 4 : ℝ) * l2Norm u ^ 2 ≤ (star u ⬝ᵥ (allowProj P v *ᵥ u)).re := fun u hu => by
    have hl := allowProj_lower hP hPP hQh hQQ hPv u hu
    have hu0 : 0 ≤ l2Norm u ^ 2 := by positivity
    have hc : (3 / 4 : ℝ) ≤
        1 - ‖(1 - P) * Q‖ ^ 2 - l2Norm (Q *ᵥ (P *ᵥ v)) ^ 2 / l2Norm (P *ᵥ v) ^ 2 := by linarith
    exact (mul_le_mul_of_nonneg_right hc hu0).trans hl
  have hBQ2 : ∀ u : Fin W → ℂ, Q *ᵥ u = u →
      (1 / 2 : ℝ) * ∑ i, ‖u i‖ ^ 2 ≤ (star u ⬝ᵥ (allowProj P v *ᵥ u)).re := fun u hu => by
    have h0 : 0 ≤ ∑ i, ‖u i‖ ^ 2 := by positivity
    have := hBQl u hu
    rw [SrcCutoffCost_l2Norm_sq] at this
    linarith
  -- the source vector
  obtain ⟨hX, hy⟩ := srcVec_sq_le R c.t hP hPP ω hT (b := 3 / 4) (by norm_num) hBQl
  rw [SrcCutoffCost_l2Norm_sq, SrcCutoffCost_l2Norm_sq] at hy
  have hQv' : ∑ i, ‖(Q *ᵥ v) i‖ ^ 2 ≤ nP / 32 := by
    have : 2 * c.Lov * nP ≤ nP / 32 := by nlinarith
    linarith
  have hPvv : nP ≤ ∑ i, ‖v i‖ ^ 2 := SrcCutoffCost_sumSq_proj_le hP hPP v
  have hy' : ∑ i, ‖srcVec W g E q R c.t P ω v i‖ ^ 2 ≤ ∑ i, ‖v i‖ ^ 2 := by
    have h43 : ((3 / 4 : ℝ)⁻¹) ^ 2 = 16 / 9 := by norm_num
    rw [h43] at hy
    nlinarith
  -- the matching error
  have hTn : ‖cavRes W g E q R ω‖ ≤ (W : ℝ) ^ 3 :=
    SrcCutoffCost_norm_le_cube _ (Nat.cast_nonneg W) hTs
  have hAS := (norm_mul_specProj_le (Matrix.isHermitian_one (n := Fin W) (α := ℂ)) le_rfl
    (Set.empty_subset _) (cavProd W g E q ω (q - 6)) ht.le).2
  have hN : ‖cavProd W g E q ω (q - 6) *
      specProj ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)) (Set.Iic (c.t ^ 2)) *
      cavRes W g E q R ω‖ ≤ c.t * (W : ℝ) ^ 3 :=
    (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hAS hTn (norm_nonneg _) ht.le)
  have hN2 : ‖cavProd W g E q ω (q - 6) *
      specProj ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)) (Set.Iic (c.t ^ 2)) *
      cavRes W g E q R ω‖ ^ 2 ≤ c.t ^ 2 * (W : ℝ) ^ 6 := by
    calc _ ≤ (c.t * (W : ℝ) ^ 3) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hN 2
      _ = c.t ^ 2 * (W : ℝ) ^ 6 := by ring
  have hE : ‖cavProd W g E q ω (q - 6) *
      specProj ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)) (Set.Iic (c.t ^ 2)) *
      cavRes W g E q R ω‖ ^ 2 * ∑ i, ‖v i‖ ^ 2 ≤ 2 * c.t ^ 2 * (W : ℝ) ^ 26 * nP := by
    calc _ ≤ c.t ^ 2 * (W : ℝ) ^ 6 * (2 * (W : ℝ) ^ 20 * nP) :=
          mul_le_mul hN2 hvP hv0.le (by positivity)
      _ = 2 * c.t ^ 2 * (W : ℝ) ^ 26 * nP := by ring
  have hW26 : (W : ℝ) ^ 26 ≤ (W : ℝ) ^ 34 :=
    pow_le_pow_right₀ (by exact_mod_cast hW) (by norm_num)
  have h32 : 32 * c.t ^ 2 * (W : ℝ) ^ 26 * nP ≤ c.kOut ^ 2 * nP := by
    refine mul_le_mul_of_nonneg_right ?_ hnP0.le
    calc 32 * c.t ^ 2 * (W : ℝ) ^ 26 ≤ 32 * c.t ^ 2 * (W : ℝ) ^ 34 := by gcongr
      _ ≤ c.kOut ^ 2 := herr
  have hA : ‖cavProd W g E q ω (q - 6) *
      specProj ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)) (Set.Iic (c.t ^ 2)) *
      cavRes W g E q R ω‖ ^ 2 * ∑ i, ‖v i‖ ^ 2 ≤
      (1 / 16 : ℝ) * ∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2 := by
    linarith
  -- the bounds on `K`
  obtain ⟨-, -, -, -, -, hK, -, -⟩ :=
    smallGen_bounds hq hR c.t hP hPP ω hRu hC hT hPv hBQ2 hy' hA
  have hK1 : hsSq (smallGen W g E q R c.t P ω v) ≤ 1 := by
    refine hK.trans ?_
    rw [div_le_iff₀ hnP0]
    linarith
  -- the active chain
  have hHn : ‖(activeMat W g E q R ω)⁻¹‖ ≤ (W : ℝ) ^ 3 :=
    SrcCutoffCost_norm_le_cube _ (Nat.cast_nonneg W) hHs
  have hsch := (activeMat_schur hq hg.le hR ω hRu hC hT).2.2.2
  have hgq : 0 < g ^ (2 * (q - 6)) := by positivity
  refine ⟨hnP0, hQh, hQQ, (le_div_iff₀ hnP0).mp hK, hK1, ?_⟩
  rw [le_div_iff₀ hgq, pow_mul', show (W : ℝ) ^ 6 = ((W : ℝ) ^ 3) ^ 2 by ring]
  have h0 : 0 ≤ g ^ (q - 6) * ‖chartProd W g E q R ω (q - 1)‖ := by positivity
  calc ‖chartProd W g E q R ω (q - 1)‖ ^ 2 * (g ^ (q - 6)) ^ 2
      = (g ^ (q - 6) * ‖chartProd W g E q R ω (q - 1)‖) ^ 2 := by ring
    _ ≤ ((W : ℝ) ^ 3) ^ 2 := pow_le_pow_left₀ h0 (hsch.trans hHn) 2


/-- `‖x‖² > 0` for a nonzero vector. -/
private lemma SrcCutoffCost_sumSq_pos {W : ℕ} {x : Fin W → ℂ} (hx : x ≠ 0) :
    0 < ∑ i, ‖x i‖ ^ 2 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hx
  have hj' : 0 < ‖x j‖ ^ 2 := by
    have : x j ≠ 0 := hj
    positivity
  exact lt_of_lt_of_le hj' (Finset.single_le_sum (f := fun i => ‖x i‖ ^ 2)
    (fun i _ => by positivity) (Finset.mem_univ j))

/-- `‖M x‖² ≤ ‖M‖² ‖x‖²` for the operator norm. -/
private lemma SrcCutoffCost_sumSq_mulVec_opNorm_le {W : ℕ} (M : Matrix (Fin W) (Fin W) ℂ)
    (x : Fin W → ℂ) : ∑ i, ‖(M *ᵥ x) i‖ ^ 2 ≤ ‖M‖ ^ 2 * ∑ i, ‖x i‖ ^ 2 := by
  have h := l2Norm_mulVec_le M x
  have h2 : l2Norm (M *ᵥ x) ^ 2 ≤ (‖M‖ * l2Norm x) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [mul_pow, SrcCutoffCost_l2Norm_sq, SrcCutoffCost_l2Norm_sq] at h2
  exact h2

/-- Off the topological support, the derivative of the cutoff in `v` vanishes. -/
private lemma SrcCutoffCost_lineDeriv_zero {W q : ℕ} {g E : ℝ} {R P : Matrix (Fin W) (Fin W) ℂ}
    {c : CutLevels} (ω : Ω W q) (v : Fin W → ℂ)
    (hnot : (ω, v) ∉ tsupport (fun p : Ω W q × (Fin W → ℂ) => srcCut W g E q R P c p.1 p.2))
    (d : Fin W → ℂ) : lineDeriv ℝ (fun w => srcCut W g E q R P c ω w) v d = 0 := by
  have h := notMem_tsupport_iff_eventuallyEq.1 hnot
  have hc : Continuous (fun t : ℝ => ((ω, v + t • d) : Ω W q × (Fin W → ℂ))) := by fun_prop
  have hev : ∀ᶠ t in nhds (0 : ℝ), srcCut W g E q R P c ω (v + t • d) = 0 := by
    have ht := hc.tendsto 0
    simp only [zero_smul, add_zero] at ht
    exact ht.eventually h
  unfold lineDeriv
  have h0 : (fun t : ℝ => srcCut W g E q R P c ω (v + t • d)) =ᶠ[nhds 0] fun _ => 0 := hev
  rw [h0.deriv_eq]
  simp


/-- `|D| ≤ x + y + z` gives `D² ≤ 3 (x² + y² + z²)`. -/
private lemma SrcCutoffCost_sq_le_three {D x y z : ℝ} (h : |D| ≤ x + y + z) :
    D ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  have h1 : D ^ 2 ≤ (x + y + z) ^ 2 := by
    rw [← sq_abs D]
    exact pow_le_pow_left₀ (abs_nonneg D) h 2
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]


/-- Linearity of the sum over the basis. -/
private lemma SrcCutoffCost_sum_comb {ι : Type*} [Fintype ι] (a b c : ι → ℝ) (A B C : ℝ) :
    ∑ j, (A * a j + B * b j + C * c j) = A * ∑ j, a j + B * ∑ j, b j + C * ∑ j, c j := by
  simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- (9.81) [su:eq:common-overlap-cutoff-cost] and (9.82) [su:eq:common-norm-cutoff-cost]: under
the level rows `0 < L_ov ≤ 1/64`, `k ≥ 1` and `32 t² W^{34} ≤ κ²`, at every `v ≠ 0`,
`‖P v‖² ‖K‖²_HS ‖∇_v χ̂‖² ≤ C₂ (1 + W⁶ g^{-2(q-6)} κ⁻² 1{reg, ‖v_{q-1}‖² < 2 κ² ‖P v‖²})`, where
`reg` is the regularity of `R_5, …, R_{q-2}`. -/
theorem srcCut_cost_le : ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ {W q : ℕ} {g E : ℝ}
    {R P : Matrix (Fin W) (Fin W) ℂ} {c : CutLevels} (ω : Ω W q) (v : Fin W → ℂ),
    1 ≤ W → 7 ≤ q → 0 < g → g ≤ 1 → R.IsHermitian → P.IsHermitian → P * P = P →
    v ≠ 0 → 0 < c.t → 0 < c.Lov → 64 * c.Lov ≤ 1 → 0 < c.kOut → 1 ≤ c.kP → 0 < c.Lrk →
    0 < c.Lgap → 32 * c.t ^ 2 * (W : ℝ) ^ 34 ≤ c.kOut ^ 2 →
    (∑ i, ‖(P *ᵥ v) i‖ ^ 2) * hsSq (smallGen W g E q R c.t P ω v) *
        tangGradSq P v (fun w => srcCut W g E q R P c ω w) ≤
      C₂ * (1 + if (∀ j, 5 ≤ j → j ≤ q - 2 → IsRegularState W g (chartR W g E q R ω j)) ∧
          ∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2 <
            2 * c.kOut ^ 2 * ∑ i, ‖(P *ᵥ v) i‖ ^ 2
        then (W : ℝ) ^ 6 / (g ^ (2 * (q - 6)) * c.kOut ^ 2) else 0) := by
  obtain ⟨Cφ, hCφ, hSdc, hSuc, hr, -, h2, hb⟩ := step_spec
  have hSd : Differentiable ℝ stepDown := hSdc.differentiable (by simp)
  have hSu : Differentiable ℝ stepUp := hSuc.differentiable (by simp)
  have hu : ∀ s, 2 ≤ s → stepUp s = 1 := fun s hs => (h2 s hs).2
  refine ⟨2000 * Cφ ^ 2, by positivity, ?_⟩
  intro W q g E R P c ω v hW hq hg hg1 hR hP hPP hv ht hLov hLov' hkOut hkP hLrk hLgap herr
  have hkk : 0 < c.kOut ^ 2 := by positivity
  have hXk : 0 ≤ (W : ℝ) ^ 6 / (g ^ (2 * (q - 6)) * c.kOut ^ 2) := by positivity
  by_cases hts : (ω, v) ∈ tsupport (fun p : Ω W q × (Fin W → ℂ) => srcCut W g E q R P c p.1 p.2)
  swap
  · have h0 : tangGradSq P v (fun w => srcCut W g E q R P c ω w) = 0 := by
      unfold tangGradSq
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [SrcCutoffCost_lineDeriv_zero ω v hts, SrcCutoffCost_lineDeriv_zero ω v hts]
      simp
    rw [h0, mul_zero]
    split_ifs <;> positivity
  have hCut : CutSupp W g E q R P c ω v :=
    srcCut_tsupport hW hq hg hR P hLov hLrk hLgap hkOut (ω, v) hts hv
  have hreg := cutSupp_regular hW hg hR hCut
  obtain ⟨hnP, hQh, hQQ, hKP, hK1, hMn⟩ :=
    SrcCutoffCost_core hW hq hg hR hP hPP hv ht hLov' hkP herr hCut
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hQv, hQPv, -⟩ := hCut
  have hnV := SrcCutoffCost_sumSq_pos hv
  have hK0 : 0 ≤ hsSq (smallGen W g E q R c.t P ω v) := by unfold hsSq; positivity
  have hQPe : ∑ i, ‖((retProj W g E q R c.t ω * P) *ᵥ v) i‖ ^ 2 =
      ∑ i, ‖(retProj W g E q R c.t ω *ᵥ (P *ᵥ v)) i‖ ^ 2 := by
    rw [← Matrix.mulVec_mulVec]
  have hS2 := SrcCutoffCost_sum_dir (v := v) hP hPP hnP (retProj W g E q R c.t ω)
    (retProj W g E q R c.t ω *ᵥ v) (β := 1) zero_le_one fun x => by
      rw [one_mul]
      exact SrcCutoffCost_sumSq_proj_le hQh hQQ x
  have hS3 := SrcCutoffCost_sum_dir (v := v) hP hPP hnP (retProj W g E q R c.t ω * P)
    ((retProj W g E q R c.t ω * P) *ᵥ v) (β := 1) zero_le_one fun x => by
      rw [one_mul, ← Matrix.mulVec_mulVec]
      exact (SrcCutoffCost_sumSq_proj_le hQh hQQ _).trans (SrcCutoffCost_sumSq_proj_le hP hPP x)
  have hS4 := SrcCutoffCost_sum_dir (v := v) hP hPP hnP (chartProd W g E q R ω (q - 1))
    (chartProd W g E q R ω (q - 1) *ᵥ v) (β := ‖chartProd W g E q R ω (q - 1)‖ ^ 2)
    (sq_nonneg _) (SrcCutoffCost_sumSq_mulVec_opNorm_le _)
  rw [hQPe] at hS3
  set nP := ∑ i, ‖(P *ᵥ v) i‖ ^ 2 with hnPd
  set nQ := ∑ i, ‖(retProj W g E q R c.t ω *ᵥ v) i‖ ^ 2 with hnQd
  set nQP := ∑ i, ‖(retProj W g E q R c.t ω *ᵥ (P *ᵥ v)) i‖ ^ 2 with hnQPd
  set nO := ∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2 with hnOd
  set K := hsSq (smallGen W g E q R c.t P ω v) with hKd
  set Q := retProj W g E q R c.t ω with hQd
  set M := chartProd W g E q R ω (q - 1) with hMd
  set ε4 : ℝ := if nO < 2 * c.kOut ^ 2 * nP then 1 else 0 with hε4
  have key : ∀ u : Fin W → ℂ,
      lineDeriv ℝ (fun w => srcCut W g E q R P c ω w) v (tangProj P v u) ^ 2 ≤
      3 * Cφ ^ 2 * (2 / (c.Lov * nP)) ^ 2 *
          (star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ tangProj P v u)).re ^ 2 +
        3 * Cφ ^ 2 * (32 / nP) ^ 2 *
          (star ((Q * P) *ᵥ v) ⬝ᵥ ((Q * P) *ᵥ tangProj P v u)).re ^ 2 +
        3 * Cφ ^ 2 * ε4 * (2 / (c.kOut ^ 2 * nP)) ^ 2 *
          (star (M *ᵥ v) ⬝ᵥ (M *ᵥ tangProj P v u)).re ^ 2 := by
    intro u
    obtain ⟨-, hvd, hPPd, -⟩ := SrcCutoffCost_tangProj_props hP hPP hnP u
    have hle : |lineDeriv ℝ (fun w => srcCut W g E q R P c ω w) v (tangProj P v u)| ≤
        Cφ * |2 * (star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ tangProj P v u)).re / (c.Lov * nP)| +
        Cφ * |16 * (2 * (star ((Q * P) *ᵥ v) ⬝ᵥ ((Q * P) *ᵥ tangProj P v u)).re) / nP| +
        (if nO < 2 * c.kOut ^ 2 * nP then
          Cφ * |2 * (star (M *ᵥ v) ⬝ᵥ (M *ᵥ tangProj P v u)).re / (c.kOut ^ 2 * nP)| else 0) :=
      SrcCutoffCost_lineDeriv_le (Q := Q) (M := M) ω rfl rfl hSd hSu hr hu hb hLov hkOut hnP hnV
        hPPd hvd
    refine (SrcCutoffCost_sq_le_three hle).trans (le_of_eq ?_)
    by_cases hc : nO < 2 * c.kOut ^ 2 * nP
    · have hε : ε4 = 1 := by rw [hε4]; simp [hc]
      simp only [hc, ite_true, hε, mul_pow, sq_abs]
      ring
    · have hε : ε4 = 0 := by rw [hε4]; simp [hc]
      simp only [hc, ite_false, hε]
      simp only [mul_pow, sq_abs]
      ring
  have hsum : tangGradSq P v (fun w => srcCut W g E q R P c ω w) ≤
      3 * Cφ ^ 2 * (2 / (c.Lov * nP)) ^ 2 * (1 * nQ) +
        3 * Cφ ^ 2 * (32 / nP) ^ 2 * (1 * nQP) +
        3 * Cφ ^ 2 * ε4 * (2 / (c.kOut ^ 2 * nP)) ^ 2 * (‖M‖ ^ 2 * nO) := by
    unfold tangGradSq
    have hj : ∀ j : Fin W, lineDeriv ℝ (fun w => srcCut W g E q R P c ω w) v
          (tangProj P v (Pi.single j 1)) ^ 2 +
        lineDeriv ℝ (fun w => srcCut W g E q R P c ω w) v
          (tangProj P v (Pi.single j Complex.I)) ^ 2 ≤
        3 * Cφ ^ 2 * (2 / (c.Lov * nP)) ^ 2 *
          ((star (Q *ᵥ v) ⬝ᵥ Q *ᵥ tangProj P v (Pi.single j 1)).re ^ 2 +
            (star (Q *ᵥ v) ⬝ᵥ Q *ᵥ tangProj P v (Pi.single j Complex.I)).re ^ 2) +
        3 * Cφ ^ 2 * (32 / nP) ^ 2 *
          ((star ((Q * P) *ᵥ v) ⬝ᵥ (Q * P) *ᵥ tangProj P v (Pi.single j 1)).re ^ 2 +
            (star ((Q * P) *ᵥ v) ⬝ᵥ (Q * P) *ᵥ tangProj P v (Pi.single j Complex.I)).re ^ 2) +
        3 * Cφ ^ 2 * ε4 * (2 / (c.kOut ^ 2 * nP)) ^ 2 *
          ((star (M *ᵥ v) ⬝ᵥ M *ᵥ tangProj P v (Pi.single j 1)).re ^ 2 +
            (star (M *ᵥ v) ⬝ᵥ M *ᵥ tangProj P v (Pi.single j Complex.I)).re ^ 2) := fun j => by
      linarith [key (Pi.single j 1), key (Pi.single j Complex.I)]
    refine (Finset.sum_le_sum fun j _ => hj j).trans ?_
    rw [SrcCutoffCost_sum_comb]
    have hA : 0 ≤ 3 * Cφ ^ 2 * (2 / (c.Lov * nP)) ^ 2 := by positivity
    have hB : 0 ≤ 3 * Cφ ^ 2 * (32 / nP) ^ 2 := by positivity
    have hε0 : 0 ≤ ε4 := by rw [hε4]; split_ifs <;> norm_num
    have hC : 0 ≤ 3 * Cφ ^ 2 * ε4 * (2 / (c.kOut ^ 2 * nP)) ^ 2 := by positivity
    gcongr
  have hnQ0 : 0 ≤ nQ := Finset.sum_nonneg fun i _ => by positivity
  have hnQP0 : 0 ≤ nQP := Finset.sum_nonneg fun i _ => by positivity
  have hnO0 : 0 ≤ nO := Finset.sum_nonneg fun i _ => by positivity
  have hε0 : 0 ≤ ε4 := by rw [hε4]; split_ifs <;> norm_num
  have hKnP : 0 ≤ nP * K := mul_nonneg hnP.le hK0
  have hCφ2 : 0 < Cφ ^ 2 := by positivity
  have hLn : 0 < c.Lov * nP := mul_pos hLov hnP
  have hKn : 0 < c.kOut ^ 2 * nP := mul_pos hkk hnP
  -- the overlap factor, (9.81) [su:eq:common-overlap-cutoff-cost]
  have e2 : nP * K * (3 * Cφ ^ 2 * (2 / (c.Lov * nP)) ^ 2 * (1 * nQ)) ≤ 3 * Cφ ^ 2 * 512 := by
    have hr2 : nQ / (c.Lov * nP) ≤ 2 := by
      rw [div_le_iff₀ hLn]
      linarith
    have hr2' : 0 ≤ nQ / (c.Lov * nP) := by positivity
    have hpos : 0 ≤ 3 * Cφ ^ 2 * (2 / (c.Lov * nP)) ^ 2 * (1 * nQ) := by positivity
    have h1 : nP * K * (3 * Cφ ^ 2 * (2 / (c.Lov * nP)) ^ 2 * (1 * nQ)) ≤
        32 * nQ * (3 * Cφ ^ 2 * (2 / (c.Lov * nP)) ^ 2 * (1 * nQ)) := by
      have := mul_le_mul_of_nonneg_right hKP hpos
      linarith
    have h2 : 32 * nQ * (3 * Cφ ^ 2 * (2 / (c.Lov * nP)) ^ 2 * (1 * nQ)) =
        3 * Cφ ^ 2 * (128 * (nQ / (c.Lov * nP)) ^ 2) := by
      field_simp
      ring
    have h3 : (nQ / (c.Lov * nP)) ^ 2 ≤ 4 := by
      have := pow_le_pow_left₀ hr2' hr2 2
      linarith
    calc _ ≤ _ := h1
      _ = _ := h2
      _ = (3 * Cφ ^ 2 * 128) * (nQ / (c.Lov * nP)) ^ 2 := by ring
      _ ≤ (3 * Cφ ^ 2 * 128) * 4 := by gcongr
      _ = 3 * Cφ ^ 2 * 512 := by ring
  -- the `Q P v` factor
  have e3 : nP * K * (3 * Cφ ^ 2 * (32 / nP) ^ 2 * (1 * nQP)) ≤ 3 * Cφ ^ 2 * 128 := by
    have hr3 : nQP / nP ≤ 1 / 8 := by
      rw [div_le_iff₀ hnP]
      linarith
    have hr3' : 0 ≤ nQP / nP := by positivity
    have hpos : 0 ≤ 3 * Cφ ^ 2 * (32 / nP) ^ 2 * (1 * nQP) := by positivity
    have h1 : nP * K * (3 * Cφ ^ 2 * (32 / nP) ^ 2 * (1 * nQP)) ≤
        nP * (3 * Cφ ^ 2 * (32 / nP) ^ 2 * (1 * nQP)) :=
      mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hnP.le hK1) hpos
    have h2 : nP * (3 * Cφ ^ 2 * (32 / nP) ^ 2 * (1 * nQP)) =
        3 * Cφ ^ 2 * (1024 * (nQP / nP)) := by
      field_simp
      ring
    calc _ ≤ _ := h1
      _ = _ := h2
      _ = (3 * Cφ ^ 2 * 1024) * (nQP / nP) := by ring
      _ ≤ (3 * Cφ ^ 2 * 1024) * (1 / 8) := by gcongr
      _ = 3 * Cφ ^ 2 * 128 := by ring
  -- the output factor, (9.82) [su:eq:common-norm-cutoff-cost] with (9.66)
  -- [su:eq:active-chain-inverse]
  have hXk' : (W : ℝ) ^ 6 / (g ^ (2 * (q - 6)) * c.kOut ^ 2) =
      ((W : ℝ) ^ 6 / g ^ (2 * (q - 6))) / c.kOut ^ 2 := (div_div _ _ _).symm
  have e4 : nP * K * (3 * Cφ ^ 2 * ε4 * (2 / (c.kOut ^ 2 * nP)) ^ 2 * (‖M‖ ^ 2 * nO)) ≤
      3 * Cφ ^ 2 * (8 * (ε4 * ((W : ℝ) ^ 6 / (g ^ (2 * (q - 6)) * c.kOut ^ 2)))) := by
    by_cases hc : nO < 2 * c.kOut ^ 2 * nP
    · have hε : ε4 = 1 := by rw [hε4]; simp [hc]
      rw [hε]
      have hr4 : nO / (c.kOut ^ 2 * nP) ≤ 2 := by
        rw [div_le_iff₀ hKn]
        linarith
      have hr4' : 0 ≤ nO / (c.kOut ^ 2 * nP) := by positivity
      have hMk : ‖M‖ ^ 2 / c.kOut ^ 2 ≤ (W : ℝ) ^ 6 / (g ^ (2 * (q - 6)) * c.kOut ^ 2) := by
        rw [hXk']
        exact div_le_div_of_nonneg_right hMn hkk.le
      have hMk' : 0 ≤ ‖M‖ ^ 2 / c.kOut ^ 2 := by positivity
      have hpos : 0 ≤ 3 * Cφ ^ 2 * 1 * (2 / (c.kOut ^ 2 * nP)) ^ 2 * (‖M‖ ^ 2 * nO) := by
        positivity
      have h1 : nP * K * (3 * Cφ ^ 2 * 1 * (2 / (c.kOut ^ 2 * nP)) ^ 2 * (‖M‖ ^ 2 * nO)) ≤
          nP * (3 * Cφ ^ 2 * 1 * (2 / (c.kOut ^ 2 * nP)) ^ 2 * (‖M‖ ^ 2 * nO)) :=
        mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hnP.le hK1) hpos
      have h2 : nP * (3 * Cφ ^ 2 * 1 * (2 / (c.kOut ^ 2 * nP)) ^ 2 * (‖M‖ ^ 2 * nO)) =
          3 * Cφ ^ 2 * (4 * (‖M‖ ^ 2 / c.kOut ^ 2) * (nO / (c.kOut ^ 2 * nP))) := by
        field_simp
        ring
      have h3 : 4 * (‖M‖ ^ 2 / c.kOut ^ 2) * (nO / (c.kOut ^ 2 * nP)) ≤
          8 * (1 * ((W : ℝ) ^ 6 / (g ^ (2 * (q - 6)) * c.kOut ^ 2))) := by
        linarith [mul_le_mul hMk hr4 hr4' hXk]
      calc _ ≤ _ := h1
        _ = _ := h2
        _ ≤ 3 * Cφ ^ 2 * (8 * (1 * ((W : ℝ) ^ 6 / (g ^ (2 * (q - 6)) * c.kOut ^ 2)))) := by
          gcongr
    · have hε : ε4 = 0 := by rw [hε4]; simp [hc]
      rw [hε]
      simp
  have hite : (if (∀ j, 5 ≤ j → j ≤ q - 2 → IsRegularState W g (chartR W g E q R ω j)) ∧
        nO < 2 * c.kOut ^ 2 * nP then (W : ℝ) ^ 6 / (g ^ (2 * (q - 6)) * c.kOut ^ 2) else 0) =
      ε4 * ((W : ℝ) ^ 6 / (g ^ (2 * (q - 6)) * c.kOut ^ 2)) := by
    by_cases hc : nO < 2 * c.kOut ^ 2 * nP
    · have hε : ε4 = 1 := by rw [hε4]; simp [hc]
      split_ifs with h1
      · rw [hε, one_mul]
      · exact absurd ⟨hreg, hc⟩ h1
    · have hε : ε4 = 0 := by rw [hε4]; simp [hc]
      split_ifs with h1
      · exact absurd h1.2 hc
      · rw [hε, zero_mul]
  rw [hite]
  have hfin := mul_le_mul_of_nonneg_left hsum hKnP
  have hε4X : 0 ≤ ε4 * ((W : ℝ) ^ 6 / (g ^ (2 * (q - 6)) * c.kOut ^ 2)) := mul_nonneg hε0 hXk
  calc nP * K * tangGradSq P v (fun w => srcCut W g E q R P c ω w)
      ≤ nP * K * (3 * Cφ ^ 2 * (2 / (c.Lov * nP)) ^ 2 * (1 * nQ) +
        3 * Cφ ^ 2 * (32 / nP) ^ 2 * (1 * nQP) +
        3 * Cφ ^ 2 * ε4 * (2 / (c.kOut ^ 2 * nP)) ^ 2 * (‖M‖ ^ 2 * nO)) := hfin
    _ = nP * K * (3 * Cφ ^ 2 * (2 / (c.Lov * nP)) ^ 2 * (1 * nQ)) +
        nP * K * (3 * Cφ ^ 2 * (32 / nP) ^ 2 * (1 * nQP)) +
        nP * K * (3 * Cφ ^ 2 * ε4 * (2 / (c.kOut ^ 2 * nP)) ^ 2 * (‖M‖ ^ 2 * nO)) := by ring
    _ ≤ 3 * Cφ ^ 2 * 512 + 3 * Cφ ^ 2 * 128 +
        3 * Cφ ^ 2 * (8 * (ε4 * ((W : ℝ) ^ 6 / (g ^ (2 * (q - 6)) * c.kOut ^ 2)))) := by
        linarith [e2, e3, e4]
    _ ≤ 2000 * Cφ ^ 2 * (1 + ε4 * ((W : ℝ) ^ 6 / (g ^ (2 * (q - 6)) * c.kOut ^ 2))) := by
        linarith [mul_nonneg hCφ2.le hε4X, hCφ2]

end LSBA
