import LSBA.Upper.CenterUpdate

/-!
# The trace centers

The deterministic centers `a_k = a_k(g, θ)` of Lemma 11.8 [lg:lem:dynamic] (Section 11.3.3
[lg:sec:general-state]): the expected increment `𝓔_k(M) = [(P_g − I)M_k]_{≤R+2,0}` and its leading
part `𝓔_k^{lead} = [(P_g − I)M_k]_{≤1,0}` in the corrected coordinates, evaluated at a vector of
centers (`a_0 = 1`, odd coordinates `0`, `a_{−k} = \overline{a_k}`, `f = 0`, `W⁻¹ = 0`); the small
root `a_2^{(0)}` of (11.53) [lg:eq:a2]; the leading centers `a_{2j}^{(0)}` from the triangular
leading equations; and the `R` corrections (11.54) [lg:eq:center-recursion]
`a^{(s+1)} = a^{(s)} − 𝖩⁻¹𝓔(a^{(s)})` with the leading Jacobian `𝖩` on the positive even
coordinates, solved by forward substitution. Properties: the symmetries and (11.53) [lg:eq:a2].
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The vector of centers from its positive even coordinates `x j = a_{2(j+1)}`: `a_0 = 1`, odd
coordinates `0`, `a_{−k} = \overline{a_k}`. -/
def centerVec (x : ℕ → ℂ) (k : ℤ) : ℂ :=
  if k = 0 then 1 else if Odd k then 0 else
    if 0 < k then x (k / 2 - 1).toNat else star (x (-k / 2 - 1).toNat)

/-- Evaluation at `M = a`, `F = 0`, `W⁻¹ = 0`, `γ = g⁻²`. -/
def centerEval (g : ℝ) (a : ℤ → ℂ) : ObsPoly →ₐ[ℂ] ℂ :=
  aeval fun v => match v with
    | .m k => a k.1
    | .f _ => 0
    | .w => 0
    | .γ => (((g ^ 2)⁻¹ : ℝ) : ℂ)

/-- `𝓔_k(M) = [(P_g − I)M_k]_{≤R+2,0}` in the corrected coordinates. -/
def centerInc (E : ℝ) (R : ℕ) (k : NzInt) : ObsPoly := corrUpd E R (.m k) - X (.m k)

/-- The positive even index `2(j+1)` as a nonzero integer. -/
def evenIdx (j : ℕ) : NzInt := ⟨2 * ((j : ℤ) + 1), by omega⟩

/-- `d = 6 − g² h_θ⁻² (1 − e^{4iθ})` of (11.53) [lg:eq:a2]. -/
def centerDisc (g E : ℝ) : ℂ :=
  6 - (((g ^ 2 / normalH E ^ 2 : ℝ) : ℂ)) * (1 - star (normalPhase E) ^ 2)

/-- `a_2^{(0)}`: the root of `a² + d a + 1 = 0` with `|a| < 1/4` (11.53) [lg:eq:a2]. -/
def centerA2 (g E : ℝ) : ℂ :=
  if h : ∃ a : ℂ, ‖a‖ < 1 / 4 ∧ a ^ 2 + centerDisc g E * a + 1 = 0 then h.choose else 0

/-- The solution `−φ(0)/(φ(1) − φ(0))` of an affine equation `φ(z) = 0`. -/
def affineSolve (φ : ℂ → ℂ) : ℂ := -φ 0 / (φ 1 - φ 0)

/-- The leading centers `a_{2(j+1)}^{(0)}`, `j ≤ n`: `a_2^{(0)}` from (11.53) [lg:eq:a2], then
the `2j`-th leading equation `𝓔_{2j}^{lead}(a) = 0`, affine in `a_{2j}`, in increasing `j`
(entries beyond `n` are `0`). -/
def centerLeadAux (g E : ℝ) (R : ℕ) : ℕ → ℕ → ℂ
  | 0 => fun j => if j = 0 then centerA2 g E else 0
  | n + 1 => Function.update (centerLeadAux g E R n) (n + 1)
      (affineSolve fun z =>
        centerEval g (centerVec (Function.update (centerLeadAux g E R n) (n + 1) z))
          (truncG 1 (centerInc E R (evenIdx (n + 1)))))

/-- The leading centers `a^{(0)}` on the positive even coordinates. -/
def centerLead (g E : ℝ) (R : ℕ) (j : ℕ) : ℂ := centerLeadAux g E R j j

/-- The leading Jacobian `𝖩_{ij} = ∂𝓔^{lead}_{2(i+1)}/∂a_{2(j+1)}` at `a^{(0)}`. -/
def centerJac (g E : ℝ) (R : ℕ) (i j : ℕ) : ℂ :=
  centerEval g (centerVec (centerLead g E R))
    (pderiv (ObsVar.m (evenIdx j)) (truncG 1 (centerInc E R (evenIdx i))))

/-- Forward substitution for a lower-triangular system, entries `≤ n`. -/
def triSolveAux (J : ℕ → ℕ → ℂ) (b : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0 => fun i => if i = 0 then b 0 / J 0 0 else 0
  | n + 1 => Function.update (triSolveAux J b n) (n + 1)
      ((b (n + 1) - ∑ j ∈ Finset.range (n + 1), J (n + 1) j * triSolveAux J b n j) /
        J (n + 1) (n + 1))

/-- The solution of the lower-triangular system `J x = b`. -/
def triSolve (J : ℕ → ℕ → ℂ) (b : ℕ → ℂ) (i : ℕ) : ℂ := triSolveAux J b i i

/-- The corrections (11.54) [lg:eq:center-recursion]: `a^{(s+1)} = a^{(s)} − 𝖩⁻¹𝓔(a^{(s)})` on the
positive even coordinates. -/
def centerNewton (g E : ℝ) (R : ℕ) : ℕ → ℕ → ℂ
  | 0 => centerLead g E R
  | s + 1 => fun i => centerNewton g E R s i - triSolve (centerJac g E R)
      (fun j => centerEval g (centerVec (centerNewton g E R s)) (centerInc E R (evenIdx j))) i

/-- The centers `a = a^{(R)}` of (11.54) [lg:eq:center-recursion]. -/
def center (g E : ℝ) (R : ℕ) : ℤ → ℂ := centerVec (centerNewton g E R R)

private lemma centerVec_zero (x : ℕ → ℂ) : centerVec x 0 = 1 := by simp [centerVec]

private lemma centerVec_odd (x : ℕ → ℂ) (k : ℤ) (h : Odd k) : centerVec x k = 0 := by
  have : k ≠ 0 := by rintro rfl; simp at h
  simp [centerVec, this, h]

private lemma centerVec_pos_even (x : ℕ → ℂ) (k : ℤ) (h0 : 0 < k) (ho : ¬Odd k) :
    centerVec x k = x (k / 2 - 1).toNat := by
  have : k ≠ 0 := by omega
  simp only [centerVec, this, ho, h0, ite_true, ite_false]

private lemma centerVec_neg_even (x : ℕ → ℂ) (k : ℤ) (h0 : k < 0) (ho : ¬Odd k) :
    centerVec x k = star (x (-k / 2 - 1).toNat) := by
  have : k ≠ 0 := by omega
  have h1 : ¬ 0 < k := by omega
  simp only [centerVec, this, ho, h1, ite_false]

private lemma centerVec_neg (x : ℕ → ℂ) (k : ℤ) : centerVec x (-k) = star (centerVec x k) := by
  by_cases h0 : k = 0
  · subst h0; simp [centerVec]
  by_cases ho : Odd k
  · rw [centerVec_odd x _ ho.neg, centerVec_odd x _ ho]; simp
  · have hne : ¬ Odd (-k) := fun h => ho (by simpa using h.neg)
    rcases lt_or_gt_of_ne h0 with hl | hg
    · rw [centerVec_pos_even x (-k) (by omega) hne, centerVec_neg_even x k hl ho, star_star]
    · rw [centerVec_neg_even x (-k) (by omega) hne, centerVec_pos_even x k hg ho, neg_neg]

private lemma centerEval_C (g : ℝ) (a : ℤ → ℂ) (c : ℂ) : centerEval g a (C c) = c := by
  simp [centerEval]

private lemma centerEval_Xm (g : ℝ) (a : ℤ → ℂ) (k : NzInt) :
    centerEval g a (X (.m k)) = a k.1 := by
  simp [centerEval]

private lemma centerEval_Xγ (g : ℝ) (a : ℤ → ℂ) :
    centerEval g a (X .γ) = (((g ^ 2)⁻¹ : ℝ) : ℂ) := by
  simp [centerEval]

private lemma centerEval_mVar (g : ℝ) (x : ℕ → ℂ) (k : ℤ) :
    centerEval g (centerVec x) (mVar k) = centerVec x k := by
  by_cases h : k = 0
  · subst h; simp [mVar, centerVec_zero]
  · simp [mVar, h, centerEval_Xm]

private lemma centerEval_trace_two (g : ℝ) (x : ℕ → ℂ) :
    centerEval g (centerVec x) (centerTrace 2) = -(x 0 ^ 2 + 6 * x 0 + 1) := by
  have h2 : centerVec x 2 = x 0 := by simp [centerVec]
  have h1 : centerVec x 1 = 0 := centerVec_odd x 1 (by decide)
  have h3 : centerVec x 3 = 0 := centerVec_odd x 3 (by decide)
  have h0 := centerVec_zero x
  have e1 : Finset.Icc (1 : ℕ) (2 - 1) = {1} := by decide
  have e3 : Finset.Icc (1 : ℕ) (2 + 1) = {1, 2, 3} := by decide
  simp only [centerTrace, map_sub, map_mul, map_neg, centerEval_C, e1, e3, Finset.sum_singleton,
    Finset.sum_range_succ, Finset.sum_range_zero, centerEval_mVar, map_sum]
  norm_num [h0, h1, h2, h3, centerEval_mVar]
  ring

private lemma centerCenters_star_phase_mul (E : ℝ) :
    star (normalPhase E) * normalPhase E = 1 := by
  unfold normalPhase
  rw [star_neg, neg_mul_neg, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat,
    show (2 : ℂ) * (↑(freeAngle E) * -Complex.I) + 2 * (↑(freeAngle E) * Complex.I) = 0 by ring,
    Complex.exp_zero]

private lemma centerCenters_norm_phase (E : ℝ) : ‖normalPhase E‖ = 1 := by
  unfold normalPhase
  rw [norm_neg, show 2 * ((freeAngle E : ℂ) * Complex.I) =
    ((2 * freeAngle E : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma centerCenters_normalH_pos {E : ℝ} (hE : |E| ≤ 1) : 0 < normalH E := by
  unfold normalH freeAngle
  have h : 0 < Real.sin (Real.arccos (E / 2)) := by
    rw [Real.sin_arccos]
    apply Real.sqrt_pos.mpr
    have := abs_le.mp hE
    nlinarith
  positivity

private lemma centerCenters_small_root (d : ℂ) (hd : 6 ≤ ‖d‖) :
    ∃ a : ℂ, ‖a‖ < 1 / 4 ∧ a ^ 2 + d * a + 1 = 0 := by
  obtain ⟨s, hs⟩ := IsAlgClosed.isSquare (d * d - 4)
  have core : ∀ r r' : ℂ, r * r' = 1 → r + r' = -d → ‖r‖ ≤ ‖r'‖ →
      ‖r‖ < 1 / 4 ∧ r ^ 2 + d * r + 1 = 0 := by
    intro r r' h1 h2 h3
    refine ⟨?_, ?_⟩
    · have hn : ‖r‖ * ‖r'‖ = 1 := by rw [← norm_mul, h1]; simp
      have hr1 : ‖r‖ ≤ 1 := by nlinarith [norm_nonneg r, norm_nonneg r']
      have hd' : ‖d‖ ≤ ‖r‖ + ‖r'‖ := by
        rw [← norm_neg, ← h2]; exact norm_add_le _ _
      have h5 : 5 ≤ ‖r'‖ := by linarith
      nlinarith [norm_nonneg r]
    · have : d = -(r + r') := by rw [h2]; ring
      rw [this]
      linear_combination (-1 : ℂ) * h1
  have e1 : ((-d + s) / 2) * ((-d - s) / 2) = 1 := by linear_combination (1 / 4 : ℂ) * hs
  have e2 : (-d + s) / 2 + (-d - s) / 2 = -d := by ring
  rcases le_total ‖(-d + s) / 2‖ ‖(-d - s) / 2‖ with h | h
  · exact ⟨_, core _ _ e1 e2 h⟩
  · exact ⟨_, core _ _ (by rw [mul_comm]; exact e1) (by rw [add_comm]; exact e2) h⟩

private lemma centerCenters_disc_norm (g E : ℝ) (hh : 0 < normalH E)
    (h6 : 6 * normalH E ^ 2 ≤ g ^ 2) : 6 ≤ ‖centerDisc g E‖ := by
  set X : ℝ := g ^ 2 / normalH E ^ 2 with hX
  have hX6 : 6 ≤ X := by
    rw [hX, le_div_iff₀ (by positivity)]; exact h6
  set u : ℂ := star (normalPhase E) ^ 2 with hu
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_pow, norm_star, centerCenters_norm_phase]; simp
  have hu2 : u.re * u.re + u.im * u.im = 1 := by
    have := Complex.sq_norm u
    rw [hun, Complex.normSq_apply] at this
    linarith
  have hure : u.re ≤ 1 := by nlinarith [mul_self_nonneg u.im]
  have hd : centerDisc g E = 6 - (X : ℂ) * (1 - u) := rfl
  have hsq : 36 ≤ ‖centerDisc g E‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hd]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.one_re,
      Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
    have h1 : X ^ 2 * (u.im * u.im) = X ^ 2 * (1 - u.re * u.re) := by rw [← hu2]; ring
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ X) (by linarith : (0 : ℝ) ≤ X - 6))
      (by linarith : (0 : ℝ) ≤ 1 - u.re)]
  by_contra hlt
  have hlt' := not_le.mp hlt
  nlinarith [norm_nonneg (centerDisc g E)]

private lemma centerCenters_truncG_Xm (k : NzInt) : truncG 1 (X (.m k)) = X (.m k) := by
  have hw : (X (.m k) : ObsPoly) ∈ weightedHomogeneousSubmodule ℂ ObsVar.gamWt
      (ObsVar.gamWt (.m k)) := isWeightedHomogeneous_X ℂ ObsVar.gamWt (.m k)
  simp [truncG, Finset.sum_range_succ, weightedHomogeneousComponent_of_mem hw, ObsVar.gamWt]

/-- `a_0 = 1`, `a_{2j+1} = 0`, `a_{−k} = \overline{a_k}` (Lemma 11.8 [lg:lem:dynamic]). -/
theorem center_zero_odd_neg (g E : ℝ) (R : ℕ) (k : ℤ) :
    center g E R 0 = 1 ∧ center g E R (2 * k + 1) = 0 ∧
      center g E R (-k) = star (center g E R k) := by
  exact ⟨centerVec_zero _, centerVec_odd _ _ (odd_two_mul_add_one k), centerVec_neg _ _⟩

/-- (11.53) [lg:eq:a2]: for `g² h_θ⁻² ≥ 6`, `a_2^{(0)}` is the root of `a² + da + 1 = 0` of modulus
`< 1/4`, and the second leading equation is this quadratic:
`𝓔_2^{lead}(a) = −(−e^{−2iθ})² h_θ² g⁻² (a_2² + d a_2 + 1)` at every center vector. -/
theorem centerA2_spec (R : ℕ) :
    ∃ E₁ : ℝ, 0 < E₁ ∧ ∀ E : ℝ, |E| ≤ E₁ → ∀ g : ℝ, 0 < g → 6 * normalH E ^ 2 ≤ g ^ 2 →
      ‖centerA2 g E‖ < 1 / 4 ∧ centerA2 g E ^ 2 + centerDisc g E * centerA2 g E + 1 = 0 ∧
        ∀ x : ℕ → ℂ, centerEval g (centerVec x) (truncG 1 (centerInc E R (evenIdx 0))) =
          -((-normalPhase E) ^ 2 * (((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ)) *
            (x 0 ^ 2 + centerDisc g E * x 0 + 1)) := by
  obtain ⟨E₁, hE₁, hT⟩ := truncG_one_corrUpd R {evenIdx 0}
  refine ⟨min E₁ 1, lt_min hE₁ one_pos, fun E hE g hg h6 => ?_⟩
  have hE1 : |E| ≤ E₁ := hE.trans (min_le_left _ _)
  have hE2 : |E| ≤ 1 := hE.trans (min_le_right _ _)
  have hh : 0 < normalH E := centerCenters_normalH_pos hE2
  have hex := centerCenters_small_root (centerDisc g E) (centerCenters_disc_norm g E hh h6)
  have hA2 : centerA2 g E = hex.choose := by
    simp only [centerA2, hex, ↓reduceDIte]
  refine ⟨?_, ?_, fun x => ?_⟩
  · rw [hA2]; exact hex.choose_spec.1
  · rw [hA2]; exact hex.choose_spec.2
  · have hk : (evenIdx 0) ∈ ({evenIdx 0} : Finset NzInt) := Finset.mem_singleton_self _
    have hk0 : 0 < (evenIdx 0).1 := by simp [evenIdx]
    have hm := (hT E hE1 (evenIdx 0) hk hk0).1
    have hq : star (normalPhase E) * normalPhase E = 1 := centerCenters_star_phase_mul E
    have hq2 : star (normalPhase E) ^ 2 * normalPhase E ^ 2 = 1 := by
      rw [← mul_pow, hq]; simp
    have hH : (normalH E : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    have hG : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
    have h2 : (evenIdx 0).1 = 2 := by simp [evenIdx]
    have ht : (2 : ℤ).toNat = 2 := rfl
    unfold centerInc
    rw [map_sub, hm, centerCenters_truncG_Xm, h2, ht]
    simp only [map_sub, map_mul, map_add, centerEval_C, centerEval_Xm, centerEval_Xγ,
      centerEval_trace_two, h2]
    have h2v : centerVec x 2 = x 0 := by simp [centerVec]
    rw [h2v]
    unfold centerDisc
    push_cast
    field_simp
    linear_combination (x 0 * (g : ℂ) ^ 2) * hq2

end LSBA
