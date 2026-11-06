import LSBA.Upper.CenterCenters

/-!
# Bounds for the trace centers

(11.55) [lg:eq:center-denominators] and (11.56) [lg:eq:centers] for the centers of (11.54)
[lg:eq:center-recursion]: on an energy window fixed after `R` and a finite index set, for large `g`,
the even diagonals satisfy `|d_k| ≥ c g⁻²`, `a = a^{(0)} + O(g⁻²)`, `𝓔(a) = O(g^{−2R−2})`, the
centers are bounded and `|a_2| < 1/4 + O(g⁻²)` (Section 11.3.3 [lg:sec:general-state]).
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Evaluation bounds for a fixed polynomial -/

private lemma cn_eval_bound (B : ℝ) (hB : 0 ≤ B) (p : ObsPoly) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ObsVar → ℂ, (∀ a, ‖u a‖ ≤ B) → ‖aeval u p‖ ≤ C := by
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨‖c‖, norm_nonneg _, fun u _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨C₁, h₁, hp⟩ := hp
    obtain ⟨C₂, h₂, hq⟩ := hq
    exact ⟨C₁ + C₂, by positivity, fun u hu => by
      rw [map_add]; exact (norm_add_le _ _).trans (add_le_add (hp u hu) (hq u hu))⟩
  | mul_X p a hp =>
    obtain ⟨C₁, h₁, hp⟩ := hp
    exact ⟨C₁ * B, by positivity, fun u hu => by
      rw [map_mul, aeval_X, norm_mul]
      exact mul_le_mul (hp u hu) (hu a) (norm_nonneg _) h₁⟩

private lemma cn_eval_lip (B : ℝ) (hB : 0 ≤ B) (p : ObsPoly) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : ObsVar → ℂ, (∀ a, ‖u a‖ ≤ B) → (∀ a, ‖v a‖ ≤ B) →
      ∀ ε : ℝ, (∀ a, ‖u a - v a‖ ≤ ε) → ‖aeval u p - aeval v p‖ ≤ C * ε := by
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨0, le_refl _, fun u v _ _ ε _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨C₁, h₁, hp⟩ := hp
    obtain ⟨C₂, h₂, hq⟩ := hq
    refine ⟨C₁ + C₂, by positivity, fun u v hu hv ε hε => ?_⟩
    rw [map_add, map_add, add_sub_add_comm, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hp u v hu hv ε hε) (hq u v hu hv ε hε))
  | mul_X p a hp =>
    obtain ⟨C₁, h₁, hp⟩ := hp
    obtain ⟨C₀, h₀, hp0⟩ := cn_eval_bound B hB p
    refine ⟨C₁ * B + C₀, by positivity, fun u v hu hv ε hε => ?_⟩
    have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε a)
    rw [map_mul, map_mul, aeval_X, aeval_X,
      show aeval u p * u a - aeval v p * v a =
        (aeval u p - aeval v p) * u a + aeval v p * (u a - v a) by ring]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 := mul_le_mul (hp u v hu hv ε hε) (hu a) (norm_nonneg _) (by positivity)
    have h2 := mul_le_mul (hp0 v hv) (hε a) (norm_nonneg _) h₀
    nlinarith

private lemma cn_eval_taylor (B : ℝ) (hB : 0 ≤ B) (V : Finset ObsVar) (p : ObsPoly) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v w : ObsVar → ℂ, (∀ a, ‖u a‖ ≤ B) → (∀ a, ‖v a‖ ≤ B) →
      (∀ a, ‖w a‖ ≤ B) → (∀ a ∉ V, u a = v a) → ∀ ε η : ℝ, (∀ a, ‖u a - v a‖ ≤ ε) →
      (∀ a, ‖v a - w a‖ ≤ η) →
      ‖aeval u p - aeval v p - ∑ a ∈ V, aeval w (pderiv a p) * (u a - v a)‖ ≤
        C * (ε * (ε + η)) := by
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨0, le_refl _, fun u v w _ _ _ _ ε η _ _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨C₁, h₁, hp⟩ := hp
    obtain ⟨C₂, h₂, hq⟩ := hq
    refine ⟨C₁ + C₂, by positivity, fun u v w hu hv hw hV ε η hε hη => ?_⟩
    have e : aeval u (p + q) - aeval v (p + q) -
        ∑ a ∈ V, aeval w (pderiv a (p + q)) * (u a - v a) =
        (aeval u p - aeval v p - ∑ a ∈ V, aeval w (pderiv a p) * (u a - v a)) +
        (aeval u q - aeval v q - ∑ a ∈ V, aeval w (pderiv a q) * (u a - v a)) := by
      simp only [map_add, add_mul, Finset.sum_add_distrib]
      ring
    rw [e, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hp u v w hu hv hw hV ε η hε hη)
      (hq u v w hu hv hw hV ε η hε hη))
  | mul_X p b hp =>
    obtain ⟨C₁, h₁, hp⟩ := hp
    obtain ⟨C₀, h₀, hp0⟩ := cn_eval_bound B hB p
    obtain ⟨L, hL0, hL⟩ := cn_eval_lip B hB p
    choose D hD0 hD using fun a : ObsVar => cn_eval_bound B hB (pderiv a p)
    refine ⟨C₁ * B + ∑ a ∈ V, D a + L, by
      have := Finset.sum_nonneg fun a (_ : a ∈ V) => hD0 a
      positivity, fun u v w hu hv hw hV ε η hε hη => ?_⟩
    have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε b)
    have hη0 : 0 ≤ η := (norm_nonneg _).trans (hη b)
    set Dp := ∑ a ∈ V, aeval w (pderiv a p) * (u a - v a) with hDp
    have hsum : ∑ a ∈ V, aeval w (pderiv a (p * X b)) * (u a - v a) =
        Dp * w b + aeval w p * (u b - v b) := by
      have h1 : ∀ a, aeval w (pderiv a (p * X b)) * (u a - v a) =
          aeval w (pderiv a p) * (u a - v a) * w b +
            (if a = b then aeval w p * (u b - v b) else 0) := by
        intro a
        rw [Derivation.leibniz, pderiv_X]
        by_cases hab : a = b
        · subst hab; simp; ring
        · simp [hab]; ring
      rw [Finset.sum_congr rfl fun a _ => h1 a, Finset.sum_add_distrib, ← Finset.sum_mul,
        Finset.sum_ite_eq']
      by_cases hb : b ∈ V
      · simp only [hb, ↓reduceIte, hDp]
      · simp only [hb, ↓reduceIte, hV b hb, sub_self, mul_zero, hDp]
    rw [hsum, map_mul, map_mul, aeval_X, aeval_X,
      show aeval u p * u b - aeval v p * v b - (Dp * w b + aeval w p * (u b - v b)) =
        (aeval u p - aeval v p - Dp) * u b + Dp * (u b - w b) +
          (aeval v p - aeval w p) * (u b - v b) by ring]
    have hDb : ‖Dp‖ ≤ (∑ a ∈ V, D a) * ε := by
      rw [hDp, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
      rw [norm_mul]
      exact mul_le_mul (hD a w hw) (hε a) (norm_nonneg _) (hD0 a)
    have hub : ‖u b - w b‖ ≤ ε + η := by
      rw [show u b - w b = (u b - v b) + (v b - w b) by ring]
      exact (norm_add_le _ _).trans (add_le_add (hε b) (hη b))
    have hvw : ‖aeval v p - aeval w p‖ ≤ L * η := hL v w hv hw η hη
    refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl) |>.trans ?_
    rw [norm_mul, norm_mul, norm_mul]
    have t1 := mul_le_mul (hp u v w hu hv hw hV ε η hε hη) (hu b) (norm_nonneg _)
      (by positivity)
    have hS : 0 ≤ ∑ a ∈ V, D a := Finset.sum_nonneg fun a _ => hD0 a
    have t2 := mul_le_mul hDb hub (norm_nonneg _) (by positivity)
    have t3 := mul_le_mul hvw (hε b) (norm_nonneg _) (by positivity)
    nlinarith [mul_nonneg hL0 (mul_nonneg hε0 hε0)]

/-! ### Variables of a polynomial -/

private lemma cn_aeval_congr {s : Set ObsVar} {p : ObsPoly} (hp : p ∈ supported ℂ s)
    {u v : ObsVar → ℂ} (h : ∀ a ∈ s, u a = v a) : aeval u p = aeval v p := by
  rw [aeval_def, aeval_def]
  refine eval₂_congr (p := p) (f := algebraMap ℂ ℂ) u v ?_
  intro i c hi hc
  refine h i ?_
  exact (mem_supported.mp hp) ((mem_vars_iff_mem_support i).mpr ⟨c, mem_support_iff.mpr hc, hi⟩)

private lemma cn_pderiv_supported {s : Set ObsVar} {p : ObsPoly} (hp : p ∈ supported ℂ s)
    (b : ObsVar) : pderiv b p ∈ supported ℂ s := by
  rw [mem_supported] at hp ⊢
  intro i hi
  obtain ⟨c, hc, hic⟩ := (mem_vars_iff_mem_support i).mp (Finset.mem_coe.mp hi)
  rw [mem_support_iff, coeff_pderiv] at hc
  apply hp
  rw [Finset.mem_coe, mem_vars_iff_mem_support]
  refine ⟨c + Finsupp.single b 1, mem_support_iff.mpr (left_ne_zero_of_mul hc), ?_⟩
  rw [Finsupp.mem_support_iff] at hic ⊢
  simp only [Finsupp.add_apply]
  omega

/-- The variables `m_a`, `0 < a ≤ K`. -/
private def cnW (K : ℕ) : Set ObsVar := {v | ∃ a : NzInt, v = .m a ∧ 0 < a.1 ∧ a.1 ≤ K}

private lemma cn_mVar_mem {K : ℕ} {a : ℤ} (h0 : 0 ≤ a) (h1 : a ≤ K) :
    mVar a ∈ supported ℂ (cnW K) := by
  unfold mVar
  split_ifs with h
  · exact one_mem _
  · exact X_mem_supported.mpr ⟨⟨a, h⟩, rfl, by simp only; omega, h1⟩

private lemma cn_trace_mem (k : ℕ) : centerTrace k ∈ supported ℂ (cnW (k + 1)) := by
  have hC : ∀ c : ℂ, (C c : ObsPoly) ∈ supported ℂ (cnW (k + 1)) := fun c =>
    Subalgebra.algebraMap_mem _ c
  unfold centerTrace
  refine Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (Subalgebra.sub_mem _ ?_ ?_) ?_) ?_
  · exact Subalgebra.mul_mem _ (Subalgebra.neg_mem _ (hC _)) (cn_mVar_mem (by omega) (by omega))
  · refine Subalgebra.mul_mem _ (hC _) (Subalgebra.sum_mem _ fun a ha => ?_)
    rw [Finset.mem_Icc] at ha
    exact Subalgebra.mul_mem _ (cn_mVar_mem (by omega) (by omega))
      (cn_mVar_mem (by omega) (by omega))
  · refine Subalgebra.mul_mem _ (hC _) (Subalgebra.sum_mem _ fun a ha => ?_)
    rw [Finset.mem_range] at ha
    exact Subalgebra.mul_mem _ (cn_mVar_mem (by omega) (by omega))
      (cn_mVar_mem (by omega) (by omega))
  · refine Subalgebra.mul_mem _ (hC _) (Subalgebra.sum_mem _ fun a ha => ?_)
    rw [Finset.mem_Icc] at ha
    exact Subalgebra.mul_mem _ (cn_mVar_mem (by omega) (by omega))
      (cn_mVar_mem (by omega) (by omega))

/-! ### The leading trace polynomial at a vector of centers -/

/-- The evaluation `m_a ↦ a_a` for `0 < a ≤ K`, all other variables `↦ 0`. -/
private def cnHv (K : ℕ) (y : ℕ → ℂ) : ObsVar → ℂ
  | .m a => if 0 < a.1 ∧ a.1 ≤ K then centerVec y a.1 else 0
  | _ => 0

private lemma cn_centerVec_pos (y : ℕ → ℂ) {k : ℤ} (hk : 0 < k) :
    centerVec y k = if Odd k then 0 else y (k / 2 - 1).toNat := by
  have : k ≠ 0 := by omega
  by_cases ho : Odd k <;> simp [centerVec, this, ho, hk]

private lemma cn_centerVec_even (y : ℕ → ℂ) (j : ℕ) : centerVec y (2 * ((j : ℤ) + 1)) = y j := by
  have ho : ¬ Odd (2 * ((j : ℤ) + 1)) := by
    rw [Int.not_odd_iff_even]; exact ⟨(j : ℤ) + 1, by ring⟩
  rw [cn_centerVec_pos y (by omega)]
  simp only [ho, ↓reduceIte]
  congr
  omega

private lemma cn_hv_cases (K : ℕ) (y : ℕ → ℂ) (v : ObsVar) :
    cnHv K y v = 0 ∨ ∃ j : ℕ, 2 * (j + 1) ≤ K ∧ v = .m (evenIdx j) ∧ cnHv K y v = y j := by
  rcases v with ⟨a, ha⟩ | a | _ | _
  · by_cases h : 0 < a ∧ a ≤ K
    · simp only [cnHv, h, and_self, ↓reduceIte]
      rw [cn_centerVec_pos y h.1]
      by_cases ho : Odd a
      · exact Or.inl (by simp [ho])
      · refine Or.inr ⟨(a / 2 - 1).toNat, ?_, ?_, by simp [ho]⟩
        · rw [Int.not_odd_iff_even, Int.even_iff] at ho; omega
        · rw [Int.not_odd_iff_even, Int.even_iff] at ho
          congr 1; apply Subtype.ext; simp only [evenIdx]; omega
    · exact Or.inl (by simp [cnHv, h])
  all_goals exact Or.inl rfl

private lemma cn_hv_even (K : ℕ) (y : ℕ → ℂ) {j : ℕ} (hj : 2 * (j + 1) ≤ K) :
    cnHv K y (.m (evenIdx j)) = y j := by
  have h : 0 < (evenIdx j).1 ∧ (evenIdx j).1 ≤ (K : ℤ) := by
    simp only [evenIdx]; constructor <;> omega
  simp only [cnHv, h, and_self, ↓reduceIte]
  exact cn_centerVec_even y j

private lemma cn_hv_bound (K : ℕ) (y : ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hy : ∀ j, 2 * (j + 1) ≤ K → ‖y j‖ ≤ B) (v : ObsVar) : ‖cnHv K y v‖ ≤ B := by
  rcases cn_hv_cases K y v with h | ⟨j, hj, -, h⟩ <;> rw [h]
  · simpa using hB
  · exact hy j hj

private lemma cn_hv_sub (K : ℕ) (y y' : ℕ → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hy : ∀ j, 2 * (j + 1) ≤ K → ‖y j - y' j‖ ≤ ε) (v : ObsVar) :
    ‖cnHv K y v - cnHv K y' v‖ ≤ ε := by
  rcases cn_hv_cases K y v with h | ⟨j, hj, rfl, -⟩
  · rcases cn_hv_cases K y' v with h' | ⟨j, hj, rfl, -⟩
    · rw [h, h', sub_zero, norm_zero]; exact hε
    · rw [cn_hv_even K y hj, cn_hv_even K y' hj]; exact hy j hj
  · rw [cn_hv_even K y hj, cn_hv_even K y' hj]; exact hy j hj

private lemma cn_hv_congr (K : ℕ) {y y' : ℕ → ℂ} (hy : ∀ j, 2 * (j + 1) ≤ K → y j = y' j) :
    cnHv K y = cnHv K y' := by
  funext v
  rcases cn_hv_cases K y v with h | ⟨j, hj, rfl, -⟩
  · rcases cn_hv_cases K y' v with h' | ⟨j, hj, rfl, -⟩
    · rw [h, h']
    · rw [cn_hv_even K y hj, cn_hv_even K y' hj, hy j hj]
  · rw [cn_hv_even K y hj, cn_hv_even K y' hj, hy j hj]

private lemma cn_centerEval_hv {K : ℕ} {p : ObsPoly} (hp : p ∈ supported ℂ (cnW K)) (g : ℝ)
    (y : ℕ → ℂ) : centerEval g (centerVec y) p = aeval (cnHv K y) p := by
  unfold centerEval
  refine cn_aeval_congr hp ?_
  rintro v ⟨a, rfl, h0, h1⟩
  simp [cnHv, h0, h1]

/-- (11.52) [lg:eq:center-trace] as a function of the values `m a` of the variables. -/
private def cnTf (k : ℕ) (m : ℤ → ℂ) : ℂ :=
  -(3 * (k : ℂ)) * m k - 3 * (k : ℂ) * ∑ x ∈ Finset.Icc 1 (k - 1), m x * m ((k : ℤ) - x) -
    (k : ℂ) / 2 * ∑ x ∈ Finset.range (k - 1), m x * m ((k : ℤ) - 2 - x) -
    (k : ℂ) / 2 * ∑ x ∈ Finset.Icc 1 (k + 1), m x * m ((k : ℤ) + 2 - x)

/-- The derivative of (11.52) [lg:eq:center-trace] in the direction `δ`. -/
private def cnTd (k : ℕ) (m δ : ℤ → ℂ) : ℂ :=
  -(3 * (k : ℂ)) * δ k -
    3 * (k : ℂ) * ∑ x ∈ Finset.Icc 1 (k - 1), (m x * δ ((k : ℤ) - x) + m ((k : ℤ) - x) * δ x) -
    (k : ℂ) / 2 * ∑ x ∈ Finset.range (k - 1),
      (m x * δ ((k : ℤ) - 2 - x) + m ((k : ℤ) - 2 - x) * δ x) -
    (k : ℂ) / 2 * ∑ x ∈ Finset.Icc 1 (k + 1),
      (m x * δ ((k : ℤ) + 2 - x) + m ((k : ℤ) + 2 - x) * δ x)

private lemma cn_aeval_trace (u : ObsVar → ℂ) (k : ℕ) :
    aeval u (centerTrace k) = cnTf k fun a => aeval u (mVar a) := by
  simp only [centerTrace, cnTf, map_sub, map_neg, map_mul, aeval_C, map_sum,
    Algebra.algebraMap_self, RingHom.id_apply]

private lemma cn_aeval_pderiv_trace (u : ObsVar → ℂ) (k : ℕ) (b : ObsVar) :
    aeval u (pderiv b (centerTrace k)) =
      cnTd k (fun a => aeval u (mVar a)) fun a => aeval u (pderiv b (mVar a)) := by
  simp only [centerTrace, cnTd, map_sub, map_neg, map_sum, Derivation.leibniz, smul_eq_mul,
    map_add, map_mul, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, pderiv_C,
    mul_zero, add_zero, neg_zero]

private lemma cn_Tf_affine (k : ℕ) (hk : 3 ≤ k) (m : ℤ → ℂ) (z : ℂ) :
    cnTf k (fun a => m a + if a = k then z else 0) =
      cnTf k m + z * (-(3 * (k : ℂ)) - k * m 2) := by
  unfold cnTf
  have e1 : ∑ x ∈ Finset.Icc 1 (k - 1), (m x + if (x : ℤ) = k then z else 0) *
      (m ((k : ℤ) - x) + if (k : ℤ) - x = k then z else 0) =
      ∑ x ∈ Finset.Icc 1 (k - 1), m x * m ((k : ℤ) - x) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mem_Icc] at hx
    simp only [show ¬ ((x : ℤ) = k) by omega, show ¬ ((k : ℤ) - x = k) by omega, ↓reduceIte,
      add_zero]
  have e2 : ∑ x ∈ Finset.range (k - 1), (m x + if (x : ℤ) = k then z else 0) *
      (m ((k : ℤ) - 2 - x) + if (k : ℤ) - 2 - x = k then z else 0) =
      ∑ x ∈ Finset.range (k - 1), m x * m ((k : ℤ) - 2 - x) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mem_range] at hx
    simp only [show ¬ ((x : ℤ) = k) by omega, show ¬ ((k : ℤ) - 2 - x = k) by omega,
      ↓reduceIte, add_zero]
  have e3 : ∑ x ∈ Finset.Icc 1 (k + 1), (m x + if (x : ℤ) = k then z else 0) *
      (m ((k : ℤ) + 2 - x) + if (k : ℤ) + 2 - x = k then z else 0) =
      ∑ x ∈ Finset.Icc 1 (k + 1), m x * m ((k : ℤ) + 2 - x) + z * m 2 + z * m 2 := by
    have h : ∀ x ∈ Finset.Icc 1 (k + 1), (m x + if (x : ℤ) = k then z else 0) *
        (m ((k : ℤ) + 2 - x) + if (k : ℤ) + 2 - x = k then z else 0) =
        m x * m ((k : ℤ) + 2 - x) + ((if x = k then z * m 2 else 0) +
          (if x = 2 then z * m 2 else 0)) := by
      intro x _
      by_cases hxk : x = k
      · subst hxk
        simp only [↓reduceIte, show ¬ (x = 2) by omega, show (x : ℤ) + 2 - x = 2 by omega,
          show ¬ ((2 : ℤ) = x) by omega]
        ring
      · by_cases hx2 : x = 2
        · subst hx2
          simp only [Nat.cast_ofNat, show ¬ ((2 : ℤ) = k) by omega,
            show (k : ℤ) + 2 - 2 = k by omega, hxk, ↓reduceIte]
          ring
        · simp only [show ¬ ((x : ℤ) = k) by omega, show ¬ ((k : ℤ) + 2 - x = k) by omega,
            hxk, hx2, ↓reduceIte]
          ring
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_Icc, show 1 ≤ k ∧ k ≤ k + 1 by omega, show 1 ≤ 2 ∧ 2 ≤ k + 1 by omega,
      and_self, ↓reduceIte]
    ring
  simp only [e1, e2, e3, ↓reduceIte]
  ring

private lemma cn_Td_diag (k : ℕ) (hk : 1 ≤ k) (m δ : ℤ → ℂ)
    (hδ : ∀ a, δ a = if a = k then 1 else 0) : cnTd k m δ = -(3 * (k : ℂ)) - k * m 2 := by
  unfold cnTd
  simp only [hδ]
  have e1 : ∑ x ∈ Finset.Icc 1 (k - 1), (m x * (if (k : ℤ) - x = k then 1 else 0) +
      m ((k : ℤ) - x) * (if (x : ℤ) = k then 1 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.mem_Icc] at hx
    simp only [show ¬ ((x : ℤ) = k) by omega, show ¬ ((k : ℤ) - x = k) by omega, ↓reduceIte,
      mul_zero, add_zero]
  have e2 : ∑ x ∈ Finset.range (k - 1), (m x * (if (k : ℤ) - 2 - x = k then 1 else 0) +
      m ((k : ℤ) - 2 - x) * (if (x : ℤ) = k then 1 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.mem_range] at hx
    simp only [show ¬ ((x : ℤ) = k) by omega, show ¬ ((k : ℤ) - 2 - x = k) by omega,
      ↓reduceIte, mul_zero, add_zero]
  have e3 : ∑ x ∈ Finset.Icc 1 (k + 1), (m x * (if (k : ℤ) + 2 - x = k then 1 else 0) +
      m ((k : ℤ) + 2 - x) * (if (x : ℤ) = k then 1 else 0)) = m 2 + m 2 := by
    have h : ∀ x ∈ Finset.Icc 1 (k + 1), (m x * (if (k : ℤ) + 2 - x = k then 1 else 0) +
        m ((k : ℤ) + 2 - x) * (if (x : ℤ) = k then 1 else 0)) =
        (if x = 2 then m 2 else 0) + (if x = k then m 2 else 0) := by
      intro x _
      by_cases hxk : x = k <;> by_cases hx2 : x = 2
      · subst hxk; subst hx2; simp
      · subst hxk
        simp only [↓reduceIte, hx2, show (x : ℤ) + 2 - x = 2 by omega,
          show ¬ ((2 : ℤ) = x) by omega, mul_zero, mul_one, zero_add]
      · subst hx2
        simp only [Nat.cast_ofNat, show ¬ ((2 : ℤ) = k) by omega,
          show (k : ℤ) + 2 - 2 = k by omega, hxk, ↓reduceIte, mul_one, mul_zero, add_zero]
      · simp only [show ¬ ((x : ℤ) = k) by omega, show ¬ ((k : ℤ) + 2 - x = k) by omega,
          hxk, hx2, ↓reduceIte, mul_zero, add_zero]
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_Icc, show 1 ≤ k ∧ k ≤ k + 1 by omega, show 1 ≤ 2 ∧ 2 ≤ k + 1 by omega,
      and_self, ↓reduceIte]
  rw [e1, e2, e3]
  simp only [↓reduceIte]
  ring

/-- `𝓛 m_{2(i+1)}` of (11.52) [lg:eq:center-trace] at the centers with even coordinates `y`. -/
private def cnT (i : ℕ) (y : ℕ → ℂ) : ℂ := aeval (cnHv (2 * i + 3) y) (centerTrace (2 * i + 2))

/-- `∂ 𝓛 m_{2(i+1)} / ∂ m_{2(j+1)}` at the centers with even coordinates `y`. -/
private def cnD (i j : ℕ) (y : ℕ → ℂ) : ℂ :=
  aeval (cnHv (2 * i + 3) y) (pderiv (.m (evenIdx j)) (centerTrace (2 * i + 2)))

private lemma cn_trace_mem' (i : ℕ) : centerTrace (2 * i + 2) ∈ supported ℂ (cnW (2 * i + 3)) := by
  have h := cn_trace_mem (2 * i + 2)
  rwa [show 2 * i + 2 + 1 = 2 * i + 3 by ring] at h

private lemma cn_D_zero {i j : ℕ} (hij : i < j) (y : ℕ → ℂ) : cnD i j y = 0 := by
  unfold cnD
  rw [pderiv_eq_zero_of_notMem_vars, map_zero]
  intro h
  obtain ⟨a, ha, h0, h1⟩ := mem_supported.mp (cn_trace_mem' i) (Finset.mem_coe.mpr h)
  have : (evenIdx j).1 = a.1 := by rw [ObsVar.m.inj ha]
  simp only [evenIdx] at this
  omega

private lemma cn_pderiv_mVar (i : ℕ) (u : ObsVar → ℂ) (a : ℤ) :
    aeval u (pderiv (.m (evenIdx i)) (mVar a)) = if a = ((2 * i + 2 : ℕ) : ℤ) then 1 else 0 := by
  unfold mVar
  split_ifs with h0 h1 h1
  · omega
  · simp
  · subst h1
    have : (⟨((2 * i + 2 : ℕ) : ℤ), h0⟩ : NzInt) = evenIdx i := by
      apply Subtype.ext; simp only [evenIdx]; push_cast; ring
    rw [this, pderiv_X_self, map_one]
  · have : ObsVar.m ⟨a, h0⟩ ≠ ObsVar.m (evenIdx i) := by
      intro he
      have := congrArg Subtype.val (ObsVar.m.inj he)
      simp only [evenIdx] at this
      omega
    rw [pderiv_X_of_ne this, map_zero]

private lemma cn_hv_two (K : ℕ) (hK : 2 ≤ K) (y : ℕ → ℂ) :
    aeval (cnHv K y) (mVar 2) = y 0 := by
  have h := cn_hv_even K y (j := 0) (by omega)
  have e : mVar 2 = X (ObsVar.m (evenIdx 0)) := by
    unfold mVar; simp only [show (2 : ℤ) ≠ 0 by norm_num, ↓reduceDIte]; rfl
  rw [e, aeval_X, h]

/-- The diagonal derivative `∂ 𝓛 m_k / ∂ m_k = −k(3 + a_2)`, `k = 2(i+1)`. -/
private lemma cn_D_diag (i : ℕ) (y : ℕ → ℂ) :
    cnD i i y = -(3 * ((2 * i + 2 : ℕ) : ℂ)) - ((2 * i + 2 : ℕ) : ℂ) * y 0 := by
  unfold cnD
  rw [cn_aeval_pderiv_trace, cn_Td_diag _ (by omega) _ _ (cn_pderiv_mVar i _),
    cn_hv_two _ (by omega)]

/-- `𝓛 m_k` with `k = 2(i+1) ≥ 4` is affine in `a_k` with slope `−k(3 + a_2)`. -/
private lemma cn_T_affine {i : ℕ} (hi : 1 ≤ i) (y : ℕ → ℂ) (z : ℂ) :
    cnT i (Function.update y i z) = cnT i (Function.update y i 0) +
      z * (-(3 * ((2 * i + 2 : ℕ) : ℂ)) - ((2 * i + 2 : ℕ) : ℂ) * y 0) := by
  unfold cnT
  rw [cn_aeval_trace, cn_aeval_trace]
  have key : (fun a => aeval (cnHv (2 * i + 3) (Function.update y i z)) (mVar a)) =
      fun a => aeval (cnHv (2 * i + 3) (Function.update y i 0)) (mVar a) +
        if a = ((2 * i + 2 : ℕ) : ℤ) then z else 0 := by
    funext a
    by_cases ha : a = 0
    · subst ha
      have : ¬ ((0 : ℤ) = ((2 * i + 2 : ℕ) : ℤ)) := by omega
      simp only [mVar, ↓reduceDIte, map_one, this, ↓reduceIte, add_zero]
    · simp only [mVar, ha, ↓reduceDIte, aeval_X, cnHv]
      split_ifs with h1 h2 h2
      · rw [cn_centerVec_pos _ h1.1, cn_centerVec_pos _ h1.1]
        have ho : ¬ Odd a := by
          rw [h2]; exact Int.not_odd_iff_even.mpr ⟨(i : ℤ) + 1, by push_cast; ring⟩
        have hj : (a / 2 - 1).toNat = i := by omega
        simp only [ho, ↓reduceIte]
        rw [hj, Function.update_self, Function.update_self, zero_add]
      · rw [cn_centerVec_pos _ h1.1, cn_centerVec_pos _ h1.1]
        by_cases ho : Odd a
        · simp only [ho, ↓reduceIte, add_zero]
        · simp only [ho, ↓reduceIte, add_zero]
          rw [Int.not_odd_iff_even, Int.even_iff] at ho
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      · exfalso; omega
      · rw [add_zero]
  rw [key, cn_Tf_affine _ (by omega), cn_hv_two _ (by omega)]
  rw [Function.update_of_ne (show (0 : ℕ) ≠ i by omega)]

private lemma cn_T_bounds (i : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℕ → ℂ, (∀ j ≤ i, ‖y j‖ ≤ B) →
      ‖cnT i y‖ ≤ C ∧ ∀ j, ‖cnD i j y‖ ≤ C := by
  obtain ⟨C₁, h₁, hC₁⟩ := cn_eval_bound B hB (centerTrace (2 * i + 2))
  choose D hD0 hD using fun j : ℕ =>
    cn_eval_bound B hB (pderiv (.m (evenIdx j)) (centerTrace (2 * i + 2)))
  have hS : 0 ≤ ∑ j ∈ Finset.range (i + 1), D j := Finset.sum_nonneg fun j _ => hD0 j
  refine ⟨C₁ + ∑ j ∈ Finset.range (i + 1), D j, by positivity, fun y hy => ?_⟩
  have hu := cn_hv_bound (2 * i + 3) y hB fun j hj => hy j (by omega)
  refine ⟨(hC₁ _ hu).trans (by linarith), fun j => ?_⟩
  by_cases hj : j ≤ i
  · exact (hD j _ hu).trans (by
      have := Finset.single_le_sum (fun j _ => hD0 j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
      linarith)
  · rw [cn_D_zero (by omega), norm_zero]; positivity

private lemma cn_T_taylor (i : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y y' w : ℕ → ℂ, (∀ j ≤ i, ‖y j‖ ≤ B ∧ ‖y' j‖ ≤ B ∧ ‖w j‖ ≤ B) →
      ∀ ε η : ℝ, 0 ≤ ε → 0 ≤ η → (∀ j ≤ i, ‖y' j - y j‖ ≤ ε) → (∀ j ≤ i, ‖y j - w j‖ ≤ η) →
      ‖cnT i y' - cnT i y - ∑ j ∈ Finset.range (i + 1), cnD i j w * (y' j - y j)‖ ≤
        C * (ε * (ε + η)) := by
  set V : Finset ObsVar := (Finset.range (i + 1)).image fun j => ObsVar.m (evenIdx j)
  obtain ⟨C, hC0, hC⟩ := cn_eval_taylor B hB V (centerTrace (2 * i + 2))
  refine ⟨C, hC0, fun y y' w hb ε η hε hη hε' hη' => ?_⟩
  have hinj : Set.InjOn (fun j => ObsVar.m (evenIdx j)) (Finset.range (i + 1)) := by
    intro j₁ _ j₂ _ h
    have := congrArg Subtype.val (ObsVar.m.inj h)
    simp only [evenIdx] at this
    omega
  have hsum : ∑ a ∈ V, aeval (cnHv (2 * i + 3) w) (pderiv a (centerTrace (2 * i + 2))) *
      (cnHv (2 * i + 3) y' a - cnHv (2 * i + 3) y a) =
      ∑ j ∈ Finset.range (i + 1), cnD i j w * (y' j - y j) := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [cn_hv_even _ y' (by omega), cn_hv_even _ y (by omega)]
    rfl
  have hout : ∀ a ∉ V, cnHv (2 * i + 3) y' a = cnHv (2 * i + 3) y a := by
    intro a ha
    rcases cn_hv_cases (2 * i + 3) y' a with h | ⟨j, hj, rfl, -⟩
    · rcases cn_hv_cases (2 * i + 3) y a with h' | ⟨j, hj, rfl, -⟩
      · rw [h, h']
      · exact absurd (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩) ha
    · exact absurd (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩) ha
  have h := hC (cnHv _ y') (cnHv _ y) (cnHv _ w)
    (cn_hv_bound _ y' hB fun j hj => (hb j (by omega)).2.1)
    (cn_hv_bound _ y hB fun j hj => (hb j (by omega)).1)
    (cn_hv_bound _ w hB fun j hj => (hb j (by omega)).2.2) hout ε η
    (cn_hv_sub _ y' y hε fun j hj => hε' j (by omega))
    (cn_hv_sub _ y w hη fun j hj => hη' j (by omega))
  rwa [hsum] at h

/-! ### The leading part of the increments on the window -/

private lemma cn_normalH {E : ℝ} (hE : |E| ≤ 1) :
    0 < normalH E ∧ 1 / 4 ≤ normalH E ^ 2 ∧ normalH E ^ 2 ≤ 1 / 3 := by
  have hE2 := abs_le.mp hE
  have h0 : 0 ≤ 1 - (E / 2) ^ 2 := by nlinarith
  have hs2 : Real.sqrt (1 - (E / 2) ^ 2) ^ 2 = 1 - (E / 2) ^ 2 := Real.sq_sqrt h0
  have hs : 0 < Real.sqrt (1 - (E / 2) ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hh : normalH E ^ 2 = 1 / (4 - E ^ 2) := by
    unfold normalH freeAngle
    rw [Real.sin_arccos, inv_pow, mul_pow, hs2]
    field_simp
    ring
  refine ⟨by unfold normalH freeAngle; rw [Real.sin_arccos]; positivity, ?_, ?_⟩ <;> rw [hh]
  · exact one_div_le_one_div_of_le (by nlinarith) (by nlinarith)
  · exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)

private lemma cn_norm_phase (E : ℝ) (k : ℤ) : ‖(-normalPhase E) ^ k‖ = 1 := by
  rw [norm_zpow, norm_neg]
  unfold normalPhase
  rw [norm_neg, show 2 * ((freeAngle E : ℂ) * Complex.I) =
    ((2 * freeAngle E : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I,
    one_zpow]

/-- `|λ(1 − t(3 + a)) − 1| ≥ 2t` for `|λ| = 1`, `|a| ≤ 1/2`, `0 ≤ t ≤ 4/49` (the bound behind
(11.55) [lg:eq:center-denominators]). -/
private lemma cn_diag_core (l a : ℂ) (t : ℝ) (hl : ‖l‖ = 1) (ha : ‖a‖ ≤ 1 / 2) (ht0 : 0 ≤ t)
    (ht : t ≤ 4 / 49) : 2 * t ≤ ‖l * (1 - (t : ℂ) * (3 + a)) - 1‖ := by
  set z : ℂ := 1 - (t : ℂ) * (3 + a) with hz
  have hzre : z.re = 1 - t * (3 + a.re) := by simp [hz]
  have hzim : z.im = -(t * a.im) := by simp [hz]
  have ha2 : a.re ^ 2 + a.im ^ 2 ≤ 1 / 4 := by
    have h := Complex.sq_norm a
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg a]
  have hre : -1 / 2 ≤ a.re := by nlinarith [sq_nonneg a.im, sq_nonneg (a.re + 1 / 2)]
  have hre' : a.re ≤ 1 / 2 := by nlinarith [sq_nonneg a.im, sq_nonneg (a.re - 1 / 2)]
  have hsq : ‖z‖ ^ 2 ≤ (1 - 2 * t) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hzre, hzim]
    nlinarith [mul_nonneg ht0 ht0, mul_nonneg ht0 (sub_nonneg.mpr ht),
      mul_nonneg (mul_nonneg ht0 ht0) (by linarith : (0 : ℝ) ≤ a.re + 1 / 2)]
  have hzn : ‖z‖ ≤ 1 - 2 * t := by
    by_contra h
    nlinarith [norm_nonneg z, not_le.mp h]
  have h1 := norm_sub_norm_le (1 : ℂ) (l * z)
  have h2 : ‖l * z - 1‖ = ‖1 - l * z‖ := norm_sub_rev _ _
  rw [norm_one, norm_mul, hl, one_mul] at h1
  linarith

private lemma cn_coeff_truncG (N : ℕ) (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (truncG N p).coeff d = if d .γ ≤ N then p.coeff d else 0 := by
  have hw : Finsupp.weight ObsVar.gamWt d = d .γ := by
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_single ObsVar.γ]
    · simp [ObsVar.gamWt]
    · intro b _ hb
      cases b <;> simp_all [ObsVar.gamWt]
    · intro h
      simp [Finsupp.notMem_support_iff.mp h]
  unfold truncG
  rw [LinearMap.sum_apply, MvPolynomial.coeff_sum]
  simp only [coeff_weightedHomogeneousComponent, hw]
  rw [Finset.sum_ite_eq]
  simp

private lemma cn_truncG_X (N : ℕ) (k : NzInt) : truncG N (X (.m k)) = X (.m k) := by
  ext d
  rw [cn_coeff_truncG, show (X (.m k) : ObsPoly) = monomial (Finsupp.single (.m k) 1) 1 from rfl,
    coeff_monomial]
  split_ifs with h1 h2 h3 <;> first | rfl | (subst_vars; simp at h1)

/-- The leading part `λ_k(y_k + h_θ² g⁻² 𝓛 y_k) − y_k` of the increment, `k = 2(i+1)`. -/
private def cnL (g E : ℝ) (i : ℕ) (y : ℕ → ℂ) : ℂ :=
  (-normalPhase E) ^ (evenIdx i).1 * (y i + ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) * cnT i y) - y i

/-- On a window fixed after `R` and `n`, the terms of orders `1` and `g⁻²` of the increments of
rows `≤ n` are `λ_k(m_k + h_θ² γ 𝓛 m_k) − m_k`, `k = 2(i+1)` (Section 11.3.3
[lg:sec:general-state]). -/
private lemma cn_window (R n : ℕ) : ∃ E₁ : ℝ, 0 < E₁ ∧ ∀ E : ℝ, |E| ≤ E₁ → |E| ≤ 1 ∧
    ∀ i ≤ n, truncG 1 (centerInc E R (evenIdx i)) =
      C ((-normalPhase E) ^ (evenIdx i).1) * (X (.m (evenIdx i)) +
        C (((normalH E ^ 2 : ℝ) : ℂ)) * X .γ * centerTrace (2 * i + 2)) - X (.m (evenIdx i)) := by
  obtain ⟨E₁, hE₁, h⟩ := truncG_one_corrUpd R ((Finset.range (n + 1)).image evenIdx)
  refine ⟨min E₁ 1, lt_min hE₁ one_pos, fun E hE => ⟨hE.trans (min_le_right _ _), fun i hi => ?_⟩⟩
  have hk : evenIdx i ∈ (Finset.range (n + 1)).image evenIdx :=
    Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
  have h1 := (h E (hE.trans (min_le_left _ _)) (evenIdx i) hk (by simp only [evenIdx]; omega)).1
  have ht : (evenIdx i).1.toNat = 2 * i + 2 := by simp only [evenIdx]; omega
  unfold centerInc
  rw [map_sub, h1, cn_truncG_X, ht]

private lemma cn_lead_eval {g E : ℝ} {R i : ℕ} (hw : truncG 1 (centerInc E R (evenIdx i)) =
      C ((-normalPhase E) ^ (evenIdx i).1) * (X (.m (evenIdx i)) +
        C (((normalH E ^ 2 : ℝ) : ℂ)) * X .γ * centerTrace (2 * i + 2)) - X (.m (evenIdx i)))
    (y : ℕ → ℂ) :
    centerEval g (centerVec y) (truncG 1 (centerInc E R (evenIdx i))) = cnL g E i y := by
  rw [hw]
  have hT := cn_centerEval_hv (cn_trace_mem' i) g y
  have hm : centerEval g (centerVec y) (X (.m (evenIdx i))) = y i := by
    simp only [centerEval, aeval_X]
    exact cn_centerVec_even y i
  simp only [map_sub, map_mul, map_add, hT, hm]
  simp only [centerEval, aeval_C, aeval_X, Algebra.algebraMap_self, RingHom.id_apply, cnL, cnT]
  push_cast
  ring

private lemma cn_jac_eval {g E : ℝ} {R i : ℕ} (hw : truncG 1 (centerInc E R (evenIdx i)) =
      C ((-normalPhase E) ^ (evenIdx i).1) * (X (.m (evenIdx i)) +
        C (((normalH E ^ 2 : ℝ) : ℂ)) * X .γ * centerTrace (2 * i + 2)) - X (.m (evenIdx i)))
    (j : ℕ) : centerJac g E R i j = (-normalPhase E) ^ (evenIdx i).1 * ((if i = j then 1 else 0) +
      ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) * cnD i j (centerLead g E R)) -
        (if i = j then 1 else 0) := by
  have hX : (pderiv (ObsVar.m (evenIdx j)) (X (.m (evenIdx i))) : ObsPoly) =
      if i = j then 1 else 0 := by
    by_cases hij : i = j
    · subst hij; simp
    · simp only [hij, ↓reduceIte]
      refine pderiv_X_of_ne fun h => ?_
      have := congrArg Subtype.val (ObsVar.m.inj h)
      simp only [evenIdx] at this
      omega
  have hγ : (pderiv (ObsVar.m (evenIdx j)) (X .γ) : ObsPoly) = 0 :=
    pderiv_X_of_ne (fun h => ObsVar.noConfusion h)
  have hT := cn_centerEval_hv (cn_pderiv_supported (cn_trace_mem' i) (.m (evenIdx j))) g
    (centerLead g E R)
  unfold centerJac
  rw [hw]
  simp only [map_sub, map_add, Derivation.leibniz, hX, hγ, smul_eq_mul, mul_zero,
    add_zero, map_mul, hT, pderiv_C]
  simp only [centerEval, aeval_C, aeval_X, Algebra.algebraMap_self, RingHom.id_apply, cnD,
    apply_ite (aeval _), map_one, map_zero]
  push_cast
  ring

/-! ### Forward substitution -/

private lemma cn_triSolveAux_eq (J : ℕ → ℕ → ℂ) (b : ℕ → ℂ) :
    ∀ n j, j ≤ n → triSolveAux J b n j = triSolve J b j := by
  intro n
  induction n with
  | zero => intro j hj; obtain rfl : j = 0 := by omega
            rfl
  | succ n ih =>
    intro j hj
    rcases Nat.lt_or_ge j (n + 1) with h | h
    · rw [triSolveAux, Function.update_of_ne (by omega), ih j (by omega)]
    · obtain rfl : j = n + 1 := by omega
      rfl

private lemma cn_triSolve_def (J : ℕ → ℕ → ℂ) (b : ℕ → ℂ) (i : ℕ) :
    triSolve J b i = (b i - ∑ j ∈ Finset.range i, J i j * triSolve J b j) / J i i := by
  rcases i with _ | i
  · simp [triSolve, triSolveAux]
  · rw [triSolve, triSolveAux, Function.update_self]
    congr 2
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [cn_triSolveAux_eq _ _ i j (by rw [Finset.mem_range] at hj; omega)]

private lemma cn_triSolve_eq (J : ℕ → ℕ → ℂ) (b : ℕ → ℂ) {i : ℕ} (hJ : J i i ≠ 0) :
    ∑ j ∈ Finset.range (i + 1), J i j * triSolve J b j = b i := by
  rw [Finset.sum_range_succ, cn_triSolve_def J b i]
  field_simp
  ring

private lemma cn_triSolve_le (J : ℕ → ℕ → ℂ) (b : ℕ → ℂ) (n : ℕ) {c D β : ℝ} (hc : 0 < c)
    (hD : 0 ≤ D) (hβ : 0 ≤ β) (hdiag : ∀ i ≤ n, c ≤ ‖J i i‖)
    (hoff : ∀ i ≤ n, ∀ j < i, ‖J i j‖ ≤ D * c) (hb : ∀ i ≤ n, ‖b i‖ ≤ β) :
    ∀ i ≤ n, ‖triSolve J b i‖ ≤ (1 + D) ^ i * β / c := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hi
  rw [cn_triSolve_def, norm_div]
  have hnum : ‖b i - ∑ j ∈ Finset.range i, J i j * triSolve J b j‖ ≤ (1 + D) ^ i * β := by
    refine (norm_sub_le _ _).trans ?_
    have hs : ‖∑ j ∈ Finset.range i, J i j * triSolve J b j‖ ≤
        ∑ j ∈ Finset.range i, D * ((1 + D) ^ j * β) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
      rw [Finset.mem_range] at hj
      rw [norm_mul]
      calc ‖J i j‖ * ‖triSolve J b j‖ ≤ (D * c) * ((1 + D) ^ j * β / c) :=
            mul_le_mul (hoff i hi j hj) (ih j hj (by omega)) (norm_nonneg _) (by positivity)
        _ = D * ((1 + D) ^ j * β) := by field_simp
    have hg := geom_sum_mul_add D i
    rw [show D + 1 = 1 + D by ring] at hg
    rw [← Finset.mul_sum, ← Finset.sum_mul] at hs
    nlinarith [hb i hi]
  calc ‖b i - ∑ j ∈ Finset.range i, J i j * triSolve J b j‖ / ‖J i i‖
      ≤ (1 + D) ^ i * β / ‖J i i‖ := div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ (1 + D) ^ i * β / c := div_le_div_of_nonneg_left (by positivity) hc (hdiag i hi)

/-! ### The leading centers -/

private lemma cn_t_small {E g : ℝ} {i : ℕ} (hE : |E| ≤ 1) (hg : 3 * ((i : ℝ) + 1) ≤ g) :
    0 < normalH E ^ 2 / g ^ 2 * ((evenIdx i).1 : ℝ) ∧
      normalH E ^ 2 / g ^ 2 * ((evenIdx i).1 : ℝ) ≤ 4 / 49 ∧
      (g ^ 2)⁻¹ ≤ 2 * (normalH E ^ 2 / g ^ 2 * ((evenIdx i).1 : ℝ)) := by
  obtain ⟨h0, h1, h2⟩ := cn_normalH hE
  have hk : ((evenIdx i).1 : ℝ) = 2 * ((i : ℝ) + 1) := by simp [evenIdx]
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hg0 : 0 < g := by linarith
  have hG : 9 * ((i : ℝ) + 1) ^ 2 ≤ g ^ 2 := by nlinarith
  rw [hk]
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  · rw [div_mul_eq_mul_div, inv_eq_one_div, div_le_iff₀ (by positivity)]
    field_simp
    nlinarith

private lemma cn_leadAux_eq (g E : ℝ) (R : ℕ) :
    ∀ n j, j ≤ n → centerLeadAux g E R n j = centerLead g E R j := by
  intro n
  induction n with
  | zero => intro j hj; obtain rfl : j = 0 := by omega
            rfl
  | succ n ih =>
    intro j hj
    rcases Nat.lt_or_ge j (n + 1) with h | h
    · rw [centerLeadAux, Function.update_of_ne (by omega), ih j (by omega)]
    · obtain rfl : j = n + 1 := by omega
      rfl

private lemma cn_cnL_congr (g E : ℝ) (i : ℕ) {y y' : ℕ → ℂ} (h : ∀ j ≤ i, y j = y' j) :
    cnL g E i y = cnL g E i y' := by
  unfold cnL cnT
  rw [cn_hv_congr (2 * i + 3) (fun j hj => h j (by omega)), h i le_rfl]

/-- The leading centers are bounded, `|a_2^{(0)}| < 1/4`, and they solve the leading equations
`𝓔^{lead}_{2(i+1)}(a^{(0)}) = 0` (Section 11.3.3 [lg:sec:general-state]). -/
private lemma cn_lead (R n : ℕ) : ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ C g₀ : ℝ, 0 ≤ C ∧ 1 ≤ g₀ ∧
    ∀ g : ℝ, g₀ ≤ g → ∀ E : ℝ, |E| ≤ E₁ → ‖centerLead g E R 0‖ < 1 / 4 ∧
      (∀ j ≤ n, ‖centerLead g E R j‖ ≤ C) ∧ ∀ i ≤ n, cnL g E i (centerLead g E R) = 0 := by
  induction n with
  | zero =>
    obtain ⟨E₀, hE₀, hA⟩ := centerA2_spec R
    obtain ⟨E₂, hE₂, hw⟩ := cn_window R 0
    refine ⟨min E₀ E₂, lt_min hE₀ hE₂, 1 / 4, 2, by norm_num, by norm_num,
      fun g hg E hE => ?_⟩
    obtain ⟨hE1, hw⟩ := hw E (hE.trans (min_le_right _ _))
    obtain ⟨-, -, h2⟩ := cn_normalH hE1
    obtain ⟨h1, hr, h3⟩ := hA E (hE.trans (min_le_left _ _)) g (by linarith) (by nlinarith)
    have hl : centerLead g E R 0 = centerA2 g E := by simp [centerLead, centerLeadAux]
    refine ⟨hl ▸ h1, fun j hj => ?_, fun i hi => ?_⟩
    · obtain rfl : j = 0 := by omega
      exact (hl ▸ h1).le
    · obtain rfl : i = 0 := by omega
      rw [← cn_lead_eval (hw 0 le_rfl), h3, hl, hr]
      simp
  | succ n ih =>
    obtain ⟨E₁, hE₁, C, g₀, hC, hg₀, h⟩ := ih
    obtain ⟨E₂, hE₂, hw⟩ := cn_window R (n + 1)
    obtain ⟨CT, hCT0, hCT⟩ := cn_T_bounds (n + 1) hC
    refine ⟨min E₁ E₂, lt_min hE₁ hE₂, max C CT, max g₀ (3 * ((n : ℝ) + 2)),
      le_max_of_le_left hC, le_max_of_le_left hg₀, fun g hg E hE => ?_⟩
    obtain ⟨h0, hb, heq⟩ := h g (le_of_max_le_left hg) E (hE.trans (min_le_left _ _))
    obtain ⟨hE1, hw⟩ := hw E (hE.trans (min_le_right _ _))
    set y := centerLeadAux g E R n with hy
    set l := (-normalPhase E) ^ (evenIdx (n + 1)).1 with hl
    set x : ℂ := ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) with hx
    set φ : ℂ → ℂ := fun z => centerEval g (centerVec (Function.update y (n + 1) z))
      (truncG 1 (centerInc E R (evenIdx (n + 1)))) with hφ
    have hy0 : y 0 = centerLead g E R 0 := cn_leadAux_eq g E R n 0 (Nat.zero_le _)
    set σ : ℂ := -(3 * ((2 * (n + 1) + 2 : ℕ) : ℂ)) - ((2 * (n + 1) + 2 : ℕ) : ℂ) * y 0 with hσ
    set dd : ℂ := l * (1 + x * σ) - 1 with hdd
    have hφz : ∀ z, φ z = φ 0 + z * dd := by
      intro z
      simp only [hφ, cn_lead_eval (hw (n + 1) le_rfl), cnL, Function.update_self]
      rw [cn_T_affine (by omega) y z, cn_T_affine (by omega) y 0]
      simp only [hdd, hl, hx]
      ring
    have hg3 : 3 * ((n : ℝ) + 2) ≤ g := le_of_max_le_right hg
    obtain ⟨ht0, ht1, -⟩ := cn_t_small (g := g) (i := n + 1) hE1 (by push_cast; linarith)
    set t := normalH E ^ 2 / g ^ 2 * ((evenIdx (n + 1)).1 : ℝ) with ht
    have hdd' : dd = l * (1 - (t : ℂ) * (3 + y 0)) - 1 := by
      simp only [hdd, ht, hx, hσ, evenIdx]
      push_cast
      ring
    have hddn : 2 * t ≤ ‖dd‖ := by
      rw [hdd']
      exact cn_diag_core _ _ _ (cn_norm_phase E _) (by rw [hy0]; linarith) ht0.le ht1
    have hdd0 : dd ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hddn; linarith
    have haff : affineSolve φ = -φ 0 / dd := by
      unfold affineSolve
      rw [hφz 1, one_mul, add_sub_cancel_left]
    have hlead : centerLead g E R (n + 1) = -φ 0 / dd := by
      rw [← haff]
      change centerLeadAux g E R (n + 1) (n + 1) = _
      rw [centerLeadAux, Function.update_self]
    have hroot : φ (-φ 0 / dd) = 0 := by
      rw [hφz]; field_simp; ring
    refine ⟨h0, fun j hj => ?_, fun i hi => ?_⟩
    · rcases Nat.lt_or_ge j (n + 1) with hj' | hj'
      · exact (hb j (by omega)).trans (le_max_left _ _)
      · obtain rfl : j = n + 1 := by omega
        rw [hlead, norm_div, norm_neg]
        have hb0 : ∀ j ≤ n + 1, ‖Function.update y (n + 1) 0 j‖ ≤ C := by
          intro j hj
          rcases Nat.lt_or_ge j (n + 1) with hj'' | hj''
          · rw [Function.update_of_ne (by omega), hy, cn_leadAux_eq g E R n j (by omega)]
            exact hb j (by omega)
          · obtain rfl : j = n + 1 := by omega
            rw [Function.update_self, norm_zero]; exact hC
        have hT := (hCT _ hb0).1
        have hφ0 : ‖φ 0‖ ≤ t * CT := by
          simp only [hφ, cn_lead_eval (hw (n + 1) le_rfl), cnL, Function.update_self, zero_add,
            sub_zero, norm_mul, cn_norm_phase, one_mul, Complex.norm_real, Real.norm_eq_abs]
          have hx0 : |normalH E ^ 2 / g ^ 2| ≤ t := by
            rw [abs_of_nonneg (by positivity), ht]
            have : (1 : ℝ) ≤ ((evenIdx (n + 1)).1 : ℝ) := by simp [evenIdx]; linarith
            have h00 : 0 ≤ normalH E ^ 2 / g ^ 2 := by positivity
            nlinarith
          exact mul_le_mul hx0 hT (norm_nonneg _) ht0.le
        rw [div_le_iff₀ (by linarith)]
        have : t * CT ≤ max C CT * (2 * t) := by
          nlinarith [le_max_right C CT]
        nlinarith [mul_le_mul_of_nonneg_left hddn (le_max_of_le_left hC : 0 ≤ max C CT)]
    · rcases Nat.lt_or_ge i (n + 1) with hi' | hi'
      · exact heq i (by omega)
      · obtain rfl : i = n + 1 := by omega
        have hc : cnL g E (n + 1) (centerLead g E R) =
            cnL g E (n + 1) (Function.update y (n + 1) (-φ 0 / dd)) := by
          refine cn_cnL_congr g E (n + 1) fun j hj => ?_
          rcases Nat.lt_or_ge j (n + 1) with hj' | hj'
          · rw [Function.update_of_ne (by omega), hy, cn_leadAux_eq g E R n j (by omega)]
          · obtain rfl : j = n + 1 := by omega
            rw [Function.update_self, hlead]
        rw [hc, ← cn_lead_eval (hw (n + 1) le_rfl)]
        exact hroot

/-- The leading Jacobian on rows `≤ n`: diagonal entries `≥ g⁻²` (11.55)
[lg:eq:center-denominators] and entries below the diagonal `O(g⁻²)`. -/
private lemma cn_jac (R n : ℕ) : ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ C g₀ : ℝ, 0 ≤ C ∧ 1 ≤ g₀ ∧
    ∀ g : ℝ, g₀ ≤ g → ∀ E : ℝ, |E| ≤ E₁ → (∀ i ≤ n, (g ^ 2)⁻¹ ≤ ‖centerJac g E R i i‖) ∧
      ∀ i ≤ n, ∀ j < i, ‖centerJac g E R i j‖ ≤ C * (g ^ 2)⁻¹ := by
  obtain ⟨E₁, hE₁, CA, gL, hCA, hgL, hL⟩ := cn_lead R n
  obtain ⟨E₂, hE₂, hw⟩ := cn_window R n
  choose CT hCT0 hCT using fun i : ℕ => cn_T_bounds i hCA
  have hS : 0 ≤ ∑ i ∈ Finset.range (n + 1), CT i := Finset.sum_nonneg fun i _ => hCT0 i
  refine ⟨min E₁ E₂, lt_min hE₁ hE₂, ∑ i ∈ Finset.range (n + 1), CT i,
    max gL (3 * ((n : ℝ) + 1)), hS, le_max_of_le_left hgL, fun g hg E hE => ?_⟩
  obtain ⟨h0, hb, -⟩ := hL g (le_of_max_le_left hg) E (hE.trans (min_le_left _ _))
  obtain ⟨hE1, hw⟩ := hw E (hE.trans (min_le_right _ _))
  have hg3 : 3 * ((n : ℝ) + 1) ≤ g := le_of_max_le_right hg
  have hg1 : 1 ≤ g := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  obtain ⟨-, -, hh2⟩ := cn_normalH hE1
  refine ⟨fun i hi => ?_, fun i hi j hj => ?_⟩
  · have hn : (i : ℝ) ≤ n := by exact_mod_cast hi
    obtain ⟨ht0, ht1, ht2⟩ := cn_t_small (g := g) (i := i) hE1 (by linarith)
    rw [cn_jac_eval (hw i hi), cn_D_diag]
    simp only [↓reduceIte]
    have e : (-normalPhase E) ^ (evenIdx i).1 * (1 + ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) *
        (-(3 * ((2 * i + 2 : ℕ) : ℂ)) - ((2 * i + 2 : ℕ) : ℂ) * centerLead g E R 0)) - 1 =
        (-normalPhase E) ^ (evenIdx i).1 * (1 - ((normalH E ^ 2 / g ^ 2 * ((evenIdx i).1 : ℝ) : ℝ) :
          ℂ) * (3 + centerLead g E R 0)) - 1 := by
      simp only [evenIdx]; push_cast; ring
    rw [e]
    exact ht2.trans (cn_diag_core _ _ _ (cn_norm_phase E _) (by linarith) ht0.le ht1)
  · have hij : ¬ i = j := by omega
    rw [cn_jac_eval (hw i hi)]
    simp only [hij, ↓reduceIte, zero_add, sub_zero, norm_mul, cn_norm_phase, one_mul,
      Complex.norm_real,
      Real.norm_eq_abs]
    have hx : |normalH E ^ 2 / g ^ 2| ≤ (g ^ 2)⁻¹ := by
      rw [abs_of_nonneg (by positivity), div_eq_mul_inv]
      have : 0 < (g ^ 2)⁻¹ := by positivity
      nlinarith
    have hD := (hCT i (centerLead g E R) fun j hj => hb j (by omega)).2 j
    have hle : CT i ≤ ∑ i ∈ Finset.range (n + 1), CT i :=
      Finset.single_le_sum (fun i _ => hCT0 i) (Finset.mem_range.mpr (by omega))
    calc |normalH E ^ 2 / g ^ 2| * ‖cnD i j (centerLead g E R)‖ ≤ (g ^ 2)⁻¹ * CT i :=
          mul_le_mul hx hD (norm_nonneg _) (by positivity)
      _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hle (by positivity)

/-! ### The terms of order `g⁻⁴` and higher -/

private lemma cn_monomial_split (d : ObsVar →₀ ℕ) (u u' : ObsVar → ℂ) (hu' : u' .γ = 1)
    (h : ∀ a ∈ d.support, a ≠ .γ → u' a = u a) :
    aeval u (monomial d (1 : ℂ)) = u .γ ^ d .γ * aeval u' (monomial d (1 : ℂ)) := by
  rw [aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod, map_one, one_mul, one_mul]
  by_cases hγ : ObsVar.γ ∈ d.support
  · rw [← Finset.mul_prod_erase _ _ hγ, ← Finset.mul_prod_erase _ _ hγ, hu', one_pow, one_mul]
    congr 1
    exact Finset.prod_congr rfl fun a ha => by
      rw [h a (Finset.mem_of_mem_erase ha) (Finset.ne_of_mem_erase ha)]
  · rw [Finsupp.notMem_support_iff.mp hγ, pow_zero, one_mul]
    exact Finset.prod_congr rfl fun a ha => by rw [h a ha (fun e => hγ (e ▸ ha))]

private lemma cn_high_eq (p : ObsPoly) {S : Finset (ObsVar →₀ ℕ)} (hp : p.support ⊆ S) :
    p - truncG 1 p = ∑ d ∈ S, (if 1 < d .γ then p.coeff d else 0) • monomial d (1 : ℂ) := by
  ext d
  rw [coeff_sub, cn_coeff_truncG, coeff_sum]
  simp only [coeff_smul, coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  by_cases hd : d ∈ S
  · simp only [hd, ↓reduceIte]
    split_ifs <;> first | (exfalso; omega) | ring
  · have : p.coeff d = 0 := by
      by_contra h; exact hd (hp (mem_support_iff.mpr h))
    simp [hd, this]

/-- The part of order `≥ g⁻⁴` of a polynomial with support in `S` and coefficients `≤ K` is
`O(t²)` and `O(t²)`-Lipschitz at evaluations with `γ ↦ t` and bounded variables. -/
private lemma cn_high (S : Finset (ObsVar →₀ ℕ)) {K B : ℝ} (hK : 0 ≤ K) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ObsPoly, p.support ⊆ S → (∀ d, ‖p.coeff d‖ ≤ K) →
      ∀ u v : ObsVar → ℂ, ∀ t ε : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ ε → u .γ = (t : ℂ) → v .γ = (t : ℂ) →
      (∀ d ∈ S, ∀ a ∈ d.support, a ≠ .γ → ‖u a‖ ≤ B ∧ ‖v a‖ ≤ B ∧ ‖u a - v a‖ ≤ ε) →
      ‖aeval u (p - truncG 1 p)‖ ≤ C * t ^ 2 ∧
        ‖aeval u (p - truncG 1 p) - aeval v (p - truncG 1 p)‖ ≤ C * t ^ 2 * ε := by
  choose C0 hC0 hC0' using fun d : ObsVar →₀ ℕ =>
    cn_eval_bound B (by linarith) (monomial d (1 : ℂ))
  choose C1 hC1 hC1' using fun d : ObsVar →₀ ℕ => cn_eval_lip B (by linarith) (monomial d (1 : ℂ))
  have hS0 : 0 ≤ ∑ d ∈ S, C0 d := Finset.sum_nonneg fun d _ => hC0 d
  have hS1 : 0 ≤ ∑ d ∈ S, C1 d := Finset.sum_nonneg fun d _ => hC1 d
  refine ⟨K * ∑ d ∈ S, C0 d + K * ∑ d ∈ S, C1 d, by positivity,
    fun p hp hpK u v t ε ht0 ht1 hε hut hvt huv => ?_⟩
  set VS := S.biUnion fun d => d.support
  set r : (ObsVar → ℂ) → ObsVar → ℂ := fun w a => if a = .γ then 1 else if a ∈ VS then w a else 0
  have hr : ∀ w : ObsVar → ℂ, w .γ = (t : ℂ) → ∀ d ∈ S, aeval w (monomial d (1 : ℂ)) =
      (t : ℂ) ^ d .γ * aeval (r w) (monomial d (1 : ℂ)) := by
    intro w hw d hd
    rw [← hw]
    refine cn_monomial_split d w (r w) (by simp [r]) fun a ha hγ => ?_
    have hmem : a ∈ VS := Finset.mem_biUnion.mpr ⟨d, hd, ha⟩
    simp only [r, hγ, hmem, ↓reduceIte]
  have hrb : ∀ w : ObsVar → ℂ, (∀ d ∈ S, ∀ a ∈ d.support, a ≠ .γ → ‖w a‖ ≤ B) →
      ∀ a, ‖r w a‖ ≤ B := by
    intro w hw a
    simp only [r]
    split_ifs with h1 h2
    · simpa using hB
    · obtain ⟨d, hd, ha⟩ := Finset.mem_biUnion.mp h2
      exact hw d hd a ha h1
    · simp; linarith
  have hru := hrb u fun d hd a ha hγ => (huv d hd a ha hγ).1
  have hrv := hrb v fun d hd a ha hγ => (huv d hd a ha hγ).2.1
  have hruv : ∀ a, ‖r u a - r v a‖ ≤ ε := by
    intro a
    simp only [r]
    split_ifs with h1 h2
    · simpa using hε
    · obtain ⟨d, hd, ha⟩ := Finset.mem_biUnion.mp h2
      exact (huv d hd a ha h1).2.2
    · simpa using hε
  have ht2 : ∀ d : ObsVar →₀ ℕ, 1 < d .γ → ‖(t : ℂ) ^ d .γ‖ ≤ t ^ 2 := by
    intro d hd
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg ht0]
    exact pow_le_pow_of_le_one ht0 ht1 hd
  have hc : ∀ d : ObsVar →₀ ℕ, ‖(if 1 < d .γ then p.coeff d else 0)‖ ≤ K := by
    intro d; split_ifs
    · exact hpK d
    · simpa using hK
  rw [cn_high_eq p hp]
  simp only [map_sum, map_smul, smul_eq_mul]
  have hK0 : 0 ≤ K * ∑ d ∈ S, C0 d := by positivity
  have hK1 : 0 ≤ K * ∑ d ∈ S, C1 d := by positivity
  constructor
  · calc _ ≤ ∑ d ∈ S, ‖(if 1 < d .γ then p.coeff d else 0) * aeval u (monomial d (1 : ℂ))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ d ∈ S, K * C0 d * t ^ 2 := Finset.sum_le_sum fun d hd => by
          rw [norm_mul, hr u hut d hd, norm_mul]
          by_cases h1 : 1 < d .γ
          · have := mul_le_mul (ht2 d h1) (hC0' d _ hru) (norm_nonneg _) (by positivity)
            calc _ ≤ K * (t ^ 2 * C0 d) := mul_le_mul (hc d) this (by positivity) hK
              _ = _ := by ring
          · simp only [h1, ↓reduceIte, norm_zero, zero_mul]
            have := hC0 d
            positivity
      _ = K * (∑ d ∈ S, C0 d) * t ^ 2 := by rw [Finset.mul_sum, Finset.sum_mul]
      _ ≤ _ := by nlinarith [sq_nonneg t]
  · rw [← Finset.sum_sub_distrib]
    calc _ ≤ ∑ d ∈ S, ‖(if 1 < d .γ then p.coeff d else 0) * aeval u (monomial d (1 : ℂ)) -
            (if 1 < d .γ then p.coeff d else 0) * aeval v (monomial d (1 : ℂ))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ d ∈ S, K * C1 d * t ^ 2 * ε := Finset.sum_le_sum fun d hd => by
          rw [← mul_sub, norm_mul, hr u hut d hd, hr v hvt d hd, ← mul_sub, norm_mul]
          by_cases h1 : 1 < d .γ
          · have := mul_le_mul (ht2 d h1) (hC1' d _ _ hru hrv ε hruv) (norm_nonneg _)
              (by positivity)
            calc _ ≤ K * (t ^ 2 * (C1 d * ε)) := mul_le_mul (hc d) this (by positivity) hK
              _ = _ := by ring
          · simp only [h1, ↓reduceIte, norm_zero, zero_mul]
            have := hC1 d
            positivity
      _ = K * (∑ d ∈ S, C1 d) * t ^ 2 * ε := by
          rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      _ ≤ _ := by
          have := mul_nonneg (mul_nonneg hK0 (sq_nonneg t)) hε
          nlinarith

/-- The evaluation `centerEval g (centerVec y)` as a map on the variables. -/
private def cnVal (g : ℝ) (y : ℕ → ℂ) : ObsVar → ℂ
  | .m k => centerVec y k.1
  | .f _ => 0
  | .w => 0
  | .γ => (((g ^ 2)⁻¹ : ℝ) : ℂ)

private lemma cn_centerEval_val (g : ℝ) (y : ℕ → ℂ) (p : ObsPoly) :
    centerEval g (centerVec y) p = aeval (cnVal g y) p := by
  rfl

private lemma cn_vec_bounds {M : ℕ} {y y' : ℕ → ℂ} {B ε : ℝ} (hB : 1 ≤ B) (hε : 0 ≤ ε)
    (hy : ∀ j ≤ M, ‖y j‖ ≤ B ∧ ‖y' j‖ ≤ B ∧ ‖y j - y' j‖ ≤ ε) {k : ℤ} (hk : k.natAbs ≤ M) :
    ‖centerVec y k‖ ≤ B ∧ ‖centerVec y' k‖ ≤ B ∧ ‖centerVec y k - centerVec y' k‖ ≤ ε := by
  unfold centerVec
  split_ifs with h0 h1 h2
  · simp [hB, hε]
  · simp [hε]; linarith
  · exact hy _ (by omega)
  · rw [norm_star, norm_star, ← star_sub, norm_star]
    exact hy _ (by omega)

private lemma cn_val_ok {S : Finset (ObsVar →₀ ℕ)} {M : ℕ}
    (hM : ∀ d ∈ S, ∀ a ∈ d.support, a.idx.natAbs ≤ M) (g : ℝ) {y y' : ℕ → ℂ} {B ε : ℝ}
    (hB : 1 ≤ B) (hε : 0 ≤ ε) (hy : ∀ j ≤ M, ‖y j‖ ≤ B ∧ ‖y' j‖ ≤ B ∧ ‖y j - y' j‖ ≤ ε) :
    ∀ d ∈ S, ∀ a ∈ d.support, a ≠ .γ →
      ‖cnVal g y a‖ ≤ B ∧ ‖cnVal g y' a‖ ≤ B ∧ ‖cnVal g y a - cnVal g y' a‖ ≤ ε := by
  intro d hd a ha hγ
  cases a with
  | m k => exact cn_vec_bounds hB hε hy (hM d hd _ ha)
  | f k => simp [cnVal, hε]; linarith
  | w => simp [cnVal, hε]; linarith
  | γ => exact absurd rfl hγ

private lemma cn_idx_bound (S : Finset (ObsVar →₀ ℕ)) :
    ∃ M : ℕ, ∀ d ∈ S, ∀ a ∈ d.support, a.idx.natAbs ≤ M :=
  ⟨S.sup fun d => d.support.sup fun a => a.idx.natAbs, fun _ hd _ ha =>
    (Finset.le_sup (f := fun a : ObsVar => a.idx.natAbs) ha).trans
      (Finset.le_sup (f := fun d : ObsVar →₀ ℕ => d.support.sup fun a => a.idx.natAbs) hd)⟩

private lemma cn_split (g E : ℝ) (R : ℕ) (k : NzInt) (y : ℕ → ℂ) :
    centerEval g (centerVec y) (centerInc E R k) =
      centerEval g (centerVec y) (truncG 1 (centerInc E R k)) +
        aeval (cnVal g y) (corrUpd E R (.m k) - truncG 1 (corrUpd E R (.m k))) := by
  rw [← cn_centerEval_val, ← map_add]
  congr 1
  unfold centerInc
  rw [map_sub (truncG 1), cn_truncG_X]
  ring

/-! ### The corrections -/

private lemma cn_x_le {E g : ℝ} (hE : |E| ≤ 1) :
    ‖((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ)‖ ≤ (g ^ 2)⁻¹ := by
  obtain ⟨-, -, h2⟩ := cn_normalH hE
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_eq_mul_inv]
  have : 0 ≤ (g ^ 2)⁻¹ := by positivity
  nlinarith

/-- The Newton step of (11.54) [lg:eq:center-recursion]: the leading part of `𝓔_k` at
`a^{(s+1)} = a^{(s)} − δ` with `𝖩δ = 𝓔(a^{(s)})` is `λ_k h_θ² g⁻²` times the second-order Taylor
remainder of `𝓛 m_k`. -/
private lemma cn_step_lead {g E : ℝ} {R i : ℕ} (hw : ∀ i' ≤ i,
    truncG 1 (centerInc E R (evenIdx i')) = C ((-normalPhase E) ^ (evenIdx i').1) *
      (X (.m (evenIdx i')) + C (((normalH E ^ 2 : ℝ) : ℂ)) * X .γ * centerTrace (2 * i' + 2)) -
        X (.m (evenIdx i'))) (y δ : ℕ → ℂ) :
    cnL g E i (fun j => y j - δ j) - cnL g E i y +
        ∑ j ∈ Finset.range (i + 1), centerJac g E R i j * δ j =
      (-normalPhase E) ^ (evenIdx i).1 * ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) *
        (cnT i (fun j => y j - δ j) - cnT i y - ∑ j ∈ Finset.range (i + 1),
          cnD i j (centerLead g E R) * ((y j - δ j) - y j)) := by
  have hs : ∑ j ∈ Finset.range (i + 1), centerJac g E R i j * δ j =
      ((-normalPhase E) ^ (evenIdx i).1 - 1) * δ i + (-normalPhase E) ^ (evenIdx i).1 *
        ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) *
          ∑ j ∈ Finset.range (i + 1), cnD i j (centerLead g E R) * δ j := by
    have h1 : ∀ j, centerJac g E R i j * δ j = ((-normalPhase E) ^ (evenIdx i).1 - 1) *
        (if i = j then δ j else 0) + (-normalPhase E) ^ (evenIdx i).1 *
          ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ) * (cnD i j (centerLead g E R) * δ j) := by
      intro j
      rw [cn_jac_eval (hw i le_rfl)]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, Finset.sum_ite_eq]
    simp
  rw [hs]
  have hd : ∑ j ∈ Finset.range (i + 1), cnD i j (centerLead g E R) * ((y j - δ j) - y j) =
      -∑ j ∈ Finset.range (i + 1), cnD i j (centerLead g E R) * δ j := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hd]
  unfold cnL
  ring

/-- The induction over the Newton steps of (11.54) [lg:eq:center-recursion]:
`a^{(s)} − a^{(0)} = O(g⁻²)` and `𝓔(a^{(s)}) = O(g^{−2s−4})` on rows `≤ n`. -/
private lemma cn_newton (R s : ℕ) : ∀ n : ℕ, ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ C g₀ : ℝ, 0 ≤ C ∧ 1 ≤ g₀ ∧
    ∀ g : ℝ, g₀ ≤ g → ∀ E : ℝ, |E| ≤ E₁ → ∀ i ≤ n,
      ‖centerNewton g E R s i - centerLead g E R i‖ ≤ C * (g ^ 2)⁻¹ ∧
      ‖centerEval g (centerVec (centerNewton g E R s)) (centerInc E R (evenIdx i))‖ ≤
        C * ((g ^ 2)⁻¹) ^ (s + 2) := by
  induction s with
  | zero =>
    intro n
    obtain ⟨Ea, hEa, S, K, hK, hS⟩ := corrCoeff_bounded R ((Finset.range (n + 1)).image evenIdx)
    obtain ⟨M, hM⟩ := cn_idx_bound S
    obtain ⟨Ec, hEc, CA, gc, hCA, hgc, hL⟩ := cn_lead R (max n M)
    obtain ⟨Ew, hEw, hw⟩ := cn_window R n
    obtain ⟨CH, hCH0, hCH⟩ := cn_high S hK.le (B := CA + 1) (by linarith)
    refine ⟨min Ea (min Ec Ew), lt_min hEa (lt_min hEc hEw), CH, gc, hCH0, hgc,
      fun g hg E hE i hi => ⟨?_, ?_⟩⟩
    · change ‖centerLead g E R i - centerLead g E R i‖ ≤ _
      rw [sub_self, norm_zero]; positivity
    obtain ⟨-, hb, heq⟩ := hL g hg E (hE.trans ((min_le_right _ _).trans (min_le_left _ _)))
    obtain ⟨-, hw⟩ := hw E (hE.trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hmem : evenIdx i ∈ (Finset.range (n + 1)).image evenIdx :=
      Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
    obtain ⟨-, -, hsupp, hcoef⟩ := hS E (hE.trans (min_le_left _ _)) (evenIdx i) hmem
      (.m (evenIdx i)) (by simp)
    have hg1 : 1 ≤ g := hgc.trans hg
    have ht1 : (g ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
    change ‖centerEval g (centerVec (centerLead g E R)) (centerInc E R (evenIdx i))‖ ≤ _
    rw [cn_split, cn_lead_eval (hw i hi), heq i (by omega), zero_add, zero_add]
    exact (hCH _ hsupp (fun d => (hcoef d).2.2) (cnVal g _) (cnVal g _) _ 0 (by positivity) ht1
      le_rfl rfl rfl (cn_val_ok hM g (by linarith) le_rfl fun j hj =>
        ⟨(hb j (by omega)).trans (by linarith), (hb j (by omega)).trans (by linarith),
          by simp⟩)).1
  | succ s ih =>
    intro n
    obtain ⟨Ea, hEa, S, K, hK, hS⟩ := corrCoeff_bounded R ((Finset.range (n + 1)).image evenIdx)
    obtain ⟨M, hM⟩ := cn_idx_bound S
    obtain ⟨Eb, hEb, Cs, gb, hCs, hgb, hN⟩ := ih (max n M)
    obtain ⟨Ec, hEc, CA, gc, hCA, hgc, hL⟩ := cn_lead R (max n M)
    obtain ⟨Ed, hEd, CJ, gd, hCJ, hgd, hJ⟩ := cn_jac R (max n M)
    obtain ⟨Ew, hEw, hw⟩ := cn_window R (max n M)
    set D := (1 + CJ) ^ (max n M) * Cs with hD
    have hD0 : 0 ≤ D := by positivity
    set B := CA + Cs + D + 1 with hB
    choose CT hCT0 hCT using fun i : ℕ => cn_T_taylor i (B := B) (by positivity)
    have hCTs : 0 ≤ ∑ i ∈ Finset.range (n + 1), CT i := Finset.sum_nonneg fun i _ => hCT0 i
    obtain ⟨CH, hCH0, hCH⟩ := cn_high S hK.le (B := B) (by linarith)
    refine ⟨min (min Ea Eb) (min Ec (min Ed Ew)),
      lt_min (lt_min hEa hEb) (lt_min hEc (lt_min hEd hEw)),
      Cs + D + (∑ i ∈ Finset.range (n + 1), CT i) * D * (D + Cs) + CH * D, max (max gb gc) gd,
      by positivity, le_max_of_le_left (le_max_of_le_left hgb), fun g hg E hE i hi => ?_⟩
    have hgb' : gb ≤ g := (le_max_left _ _).trans ((le_max_left _ _).trans hg)
    have hgc' : gc ≤ g := (le_max_right _ _).trans ((le_max_left _ _).trans hg)
    have hgd' : gd ≤ g := (le_max_right _ _).trans hg
    have hEa' : |E| ≤ Ea := hE.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hEb' : |E| ≤ Eb := hE.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hEc' : |E| ≤ Ec := hE.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hEd' : |E| ≤ Ed :=
      hE.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hEw' : |E| ≤ Ew :=
      hE.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    obtain ⟨-, hb0, -⟩ := hL g hgc' E hEc'
    obtain ⟨hJd, hJo⟩ := hJ g hgd' E hEd'
    obtain ⟨hE1, hw⟩ := hw E hEw'
    have hg1 : 1 ≤ g := hgb.trans hgb'
    set t : ℝ := (g ^ 2)⁻¹ with ht
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
    set y := centerNewton g E R s with hy
    set b : ℕ → ℂ := fun j => centerEval g (centerVec y) (centerInc E R (evenIdx j)) with hb
    set δ := triSolve (centerJac g E R) b with hδ
    have hnew : centerNewton g E R (s + 1) = fun j => y j - δ j := rfl
    have hδb : ∀ j ≤ max n M, ‖δ j‖ ≤ D * t ^ (s + 1) := by
      intro j hj
      have h := cn_triSolve_le (centerJac g E R) b (max n M) (c := t) (D := CJ)
        (β := Cs * t ^ (s + 2)) ht0 hCJ (by positivity) hJd hJo
        (fun i hi => (hN g hgb' E hEb' i hi).2) j hj
      refine h.trans ?_
      rw [div_le_iff₀ ht0, hD, pow_succ t (s + 1)]
      have hp : (1 + CJ) ^ j ≤ (1 + CJ) ^ (max n M) := pow_le_pow_right₀ (by linarith) hj
      have : 0 ≤ Cs * t ^ (s + 1) * t := by positivity
      nlinarith
    have he : t ^ (s + 1) ≤ t := by
      calc t ^ (s + 1) ≤ t ^ 1 := pow_le_pow_of_le_one ht0.le ht1 (by omega)
        _ = t := pow_one t
    have he1 : t ^ (s + 1) ≤ 1 := he.trans ht1
    have hyb : ∀ j ≤ max n M, ‖y j‖ ≤ CA + Cs := by
      intro j hj
      have h1 := (hN g hgb' E hEb' j hj).1
      have h2 := hb0 j hj
      calc ‖y j‖ = ‖(y j - centerLead g E R j) + centerLead g E R j‖ := by ring_nf
        _ ≤ Cs * t + CA := (norm_add_le _ _).trans (add_le_add h1 h2)
        _ ≤ CA + Cs := by nlinarith
    have hynb : ∀ j ≤ max n M, ‖y j - δ j‖ ≤ B := by
      intro j hj
      have := hδb j hj
      calc ‖y j - δ j‖ ≤ ‖y j‖ + ‖δ j‖ := norm_sub_le _ _
        _ ≤ CA + Cs + D * 1 := add_le_add (hyb j hj)
            (this.trans (mul_le_mul_of_nonneg_left he1 hD0))
        _ ≤ B := by linarith
    refine ⟨?_, ?_⟩
    · rw [hnew]
      calc ‖y i - δ i - centerLead g E R i‖ = ‖(y i - centerLead g E R i) - δ i‖ := by ring_nf
        _ ≤ Cs * t + D * t ^ (s + 1) :=
            (norm_sub_le _ _).trans (add_le_add (hN g hgb' E hEb' i (by omega)).1
              (hδb i (by omega)))
        _ ≤ Cs * t + D * t := by nlinarith
        _ ≤ _ := by
            have : 0 ≤ ((∑ i ∈ Finset.range (n + 1), CT i) * D * (D + Cs) + CH * D) * t := by
              positivity
            nlinarith
    · have hmem : evenIdx i ∈ (Finset.range (n + 1)).image evenIdx :=
        Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
      obtain ⟨-, -, hsupp, hcoef⟩ := hS E hEa' (evenIdx i) hmem (.m (evenIdx i)) (by simp)
      have hJii : centerJac g E R i i ≠ 0 := by
        intro h0; have := hJd i (by omega); rw [h0, norm_zero] at this; linarith
      have hbi := cn_triSolve_eq (centerJac g E R) b (i := i) hJii
      have hwi : ∀ i' ≤ i, _ := fun i' hi' => hw i' (by omega)
      have hA := cn_step_lead (g := g) (R := R) hwi y δ
      set H : ObsPoly := corrUpd E R (.m (evenIdx i)) - truncG 1 (corrUpd E R (.m (evenIdx i)))
      have hsplit_new := cn_split g E R (evenIdx i) (fun j => y j - δ j)
      have hsplit_old := cn_split g E R (evenIdx i) y
      rw [cn_lead_eval (hw i (by omega))] at hsplit_new hsplit_old
      have hkey : centerEval g (centerVec (centerNewton g E R (s + 1)))
          (centerInc E R (evenIdx i)) =
          (cnL g E i (fun j => y j - δ j) - cnL g E i y +
            ∑ j ∈ Finset.range (i + 1), centerJac g E R i j * δ j) +
          (aeval (cnVal g fun j => y j - δ j) H - aeval (cnVal g y) H) := by
        have hbi' : b i = cnL g E i y + aeval (cnVal g y) H := hsplit_old
        rw [hnew, hsplit_new, hbi, hbi']
        ring
      rw [hkey, hA]
      set ε := D * t ^ (s + 1) with hε
      have hε0 : 0 ≤ ε := by positivity
      have hT := hCT i y (fun j => y j - δ j) (centerLead g E R)
        (fun j hj => ⟨(hyb j (by omega)).trans (by linarith), hynb j (by omega),
          (hb0 j (by omega)).trans (by linarith)⟩) ε (Cs * t) hε0 (by positivity)
        (fun j hj => by
          simp only [sub_sub_cancel_left, norm_neg]; exact hδb j (by omega))
        (fun j hj => (hN g hgb' E hEb' j (by omega)).1)
      have hHi := (hCH _ hsupp (fun d => (hcoef d).2.2) (cnVal g fun j => y j - δ j) (cnVal g y)
        t ε ht0.le ht1 hε0 rfl rfl (cn_val_ok hM g (by linarith) hε0 fun j hj =>
          ⟨hynb j (by omega), (hyb j (by omega)).trans (by linarith), by
            simp only [sub_sub_cancel_left, norm_neg]; exact hδb j (by omega)⟩)).2
      have hCTi : CT i ≤ ∑ i ∈ Finset.range (n + 1), CT i :=
        Finset.single_le_sum (fun i _ => hCT0 i) (Finset.mem_range.mpr (by omega))
      have hlx : ‖(-normalPhase E) ^ (evenIdx i).1 * ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ)‖ ≤ t := by
        rw [norm_mul, cn_norm_phase, one_mul]; exact cn_x_le hE1
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      have h1 : ‖(-normalPhase E) ^ (evenIdx i).1 * ((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ)‖ *
          ‖cnT i (fun j => y j - δ j) - cnT i y - ∑ j ∈ Finset.range (i + 1),
            cnD i j (centerLead g E R) * ((y j - δ j) - y j)‖ ≤
          t * ((∑ i ∈ Finset.range (n + 1), CT i) * (ε * (ε + Cs * t))) :=
        mul_le_mul hlx (hT.trans (mul_le_mul_of_nonneg_right hCTi (by positivity)))
          (norm_nonneg _) ht0.le
      have hεt : ε ≤ D * t := mul_le_mul_of_nonneg_left he hD0
      have h2 : ε * (ε + Cs * t) ≤ ε * ((D + Cs) * t) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hε0
      have hpow : t ^ (s + 1 + 2) = t ^ (s + 1) * t * t := by ring
      rw [hpow]
      have h3 : t * ((∑ i ∈ Finset.range (n + 1), CT i) * (ε * (ε + Cs * t))) ≤
          (∑ i ∈ Finset.range (n + 1), CT i) * D * (D + Cs) * (t ^ (s + 1) * t * t) := by
        have := mul_le_mul_of_nonneg_left h2 (mul_nonneg ht0.le hCTs)
        calc _ = t * (∑ i ∈ Finset.range (n + 1), CT i) * (ε * (ε + Cs * t)) := by ring
          _ ≤ t * (∑ i ∈ Finset.range (n + 1), CT i) * (ε * ((D + Cs) * t)) := this
          _ = _ := by rw [hε]; ring
      have h4 : CH * t ^ 2 * ε = CH * D * (t ^ (s + 1) * t * t) := by rw [hε]; ring
      have h5 : 0 ≤ (Cs + D) * (t ^ (s + 1) * t * t) := by positivity
      linarith

/-! ### Conjugation and parity -/

private lemma cn_neg_neg (v : ObsVar) : v.neg.neg = v := by
  cases v with
  | m k => exact congrArg ObsVar.m (Subtype.ext (neg_neg k.1))
  | f k => exact congrArg ObsVar.f (Subtype.ext (neg_neg k.1))
  | w => rfl
  | γ => rfl

private lemma cn_neg_injective : Function.Injective ObsVar.neg :=
  Function.LeftInverse.injective cn_neg_neg

private lemma cn_conj_X (v : ObsVar) : conjPoly (X v) = X v.neg := by simp [conjPoly]

private lemma cn_conj_C (a : ℂ) : conjPoly (C a) = C (starRingEnd ℂ a) := by simp [conjPoly]

private lemma cn_coeff_conj (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (conjPoly p).coeff d = starRingEnd ℂ (p.coeff (d.mapDomain ObsVar.neg)) := by
  have he : conjPoly p = MvPolynomial.map (starRingEnd ℂ) (rename ObsVar.neg p) := by
    refine hom_eq_hom conjPoly ((MvPolynomial.map (starRingEnd ℂ)).comp
      (rename ObsVar.neg : ObsPoly →ₐ[ℂ] ObsPoly).toRingHom) ?_ ?_ p
    · ext r; simp [cn_conj_C]
    · intro v; simp [cn_conj_X]
  rw [he, MvPolynomial.coeff_map]
  congr 1
  have h2 : (d.mapDomain ObsVar.neg).mapDomain ObsVar.neg = d := by
    rw [← Finsupp.mapDomain_comp]
    have : (ObsVar.neg ∘ ObsVar.neg : ObsVar → ObsVar) = id := funext cn_neg_neg
    rw [this, Finsupp.mapDomain_id]
  have := coeff_rename_mapDomain ObsVar.neg cn_neg_injective p (d.mapDomain ObsVar.neg)
  rwa [h2] at this

private lemma cn_conj_bind₁ {τ : ObsVar → ObsPoly} (hτ : ∀ v, conjPoly (τ v) = τ v.neg)
    (p : ObsPoly) : conjPoly (bind₁ τ p) = bind₁ τ (conjPoly p) := by
  refine hom_eq_hom (conjPoly.comp (bind₁ τ : ObsPoly →ₐ[ℂ] ObsPoly).toRingHom)
    ((bind₁ τ : ObsPoly →ₐ[ℂ] ObsPoly).toRingHom.comp conjPoly) ?_ ?_ p
  · ext r; simp [cn_conj_C]
  · intro v; simp [hτ, cn_conj_X]

private lemma cn_conj_truncG (N : ℕ) (p : ObsPoly) :
    conjPoly (truncG N p) = truncG N (conjPoly p) := by
  ext d
  have hγ : (d.mapDomain ObsVar.neg) .γ = d .γ :=
    Finsupp.mapDomain_apply_of_injective cn_neg_injective d ObsVar.γ
  rw [cn_coeff_conj, cn_coeff_truncG, cn_coeff_truncG, cn_coeff_conj, hγ]
  split_ifs <;> simp

private lemma cn_conj_updPoly (E : ℝ) (N : ℕ) (p : ObsPoly) :
    conjPoly (updPoly E N p) = updPoly E N (conjPoly p) := by
  have hrot : ∀ q, conjPoly (rotPoly E q) = rotPoly E (conjPoly q) := by
    intro q
    refine hom_eq_hom (conjPoly.comp (rotPoly E : ObsPoly →ₐ[ℂ] ObsPoly).toRingHom)
      ((rotPoly E : ObsPoly →ₐ[ℂ] ObsPoly).toRingHom.comp conjPoly) ?_ ?_ q
    · ext r; simp [cn_conj_C, rotPoly]
    · intro v
      have hz : ∀ k : ℤ, starRingEnd ℂ ((-normalPhase E) ^ k) = (-normalPhase E) ^ (-k) := by
        intro k
        have h : starRingEnd ℂ (-normalPhase E) = (-normalPhase E)⁻¹ := by
          unfold normalPhase
          rw [neg_neg, ← Complex.exp_conj, ← Complex.exp_neg]
          congr 1
          simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
          ring
        rw [map_zpow₀, h, inv_zpow, zpow_neg]
      have hi : v.neg.idx = -v.idx := by cases v <;> simp [ObsVar.neg, ObsVar.idx]
      change conjPoly (rotPoly E (X v)) = rotPoly E (conjPoly (X v))
      simp only [rotPoly, aeval_X, cn_conj_X, map_mul, cn_conj_C, hz, hi]
  have hzw : ∀ q, conjPoly (zeroW q) = zeroW (conjPoly q) := by
    intro q
    refine hom_eq_hom (conjPoly.comp (zeroW : ObsPoly →ₐ[ℂ] ObsPoly).toRingHom)
      ((zeroW : ObsPoly →ₐ[ℂ] ObsPoly).toRingHom.comp conjPoly) ?_ ?_ q
    · ext r; simp [cn_conj_C, zeroW]
    · intro v; cases v <;> simp [zeroW, cn_conj_X, ObsVar.neg]
  unfold updPoly
  rw [cn_conj_truncG, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_mul, map_mul, map_pow, cn_conj_C, Complex.conj_ofReal, cn_conj_X, hzw,
    ← wickMap_conjPoly, hrot]
  rfl

private lemma cn_corrCoord_sym (E : ℝ) (R : ℕ) (v : ObsVar) :
    conjPoly (corrCoord E R v) = corrCoord E R v.neg := by
  cases v with
  | m k => exact (conjPoly_corrObs E R k).1
  | f k => exact (conjPoly_corrObs E R k).2
  | w =>
    change conjPoly (corrStep E (R + 2) (R + 2) (corrCoordAux E (R + 2) (R + 1)) .w) =
      corrStep E (R + 2) (R + 2) (corrCoordAux E (R + 2) (R + 1)) .w
    rw [corrStep, cn_conj_X]; rfl
  | γ =>
    change conjPoly (corrStep E (R + 2) (R + 2) (corrCoordAux E (R + 2) (R + 1)) .γ) =
      corrStep E (R + 2) (R + 2) (corrCoordAux E (R + 2) (R + 1)) .γ
    rw [corrStep, cn_conj_X]; rfl

private lemma cn_invCoord_sym (E : ℝ) (R : ℕ) :
    ∀ r v, conjPoly (revCoord (R + 2) (corrCoord E R) r v) =
      revCoord (R + 2) (corrCoord E R) r v.neg
  | 0, v => cn_conj_X v
  | r + 1, v => by
    simp only [revCoord]
    rw [cn_conj_truncG, map_sub conjPoly, cn_conj_X, cn_conj_bind₁ (cn_invCoord_sym E R r),
      map_sub conjPoly, cn_corrCoord_sym, cn_conj_X]

/-- `[P_g M_{−k}]_{≤R+2,0} = \overline{[P_g M_k]_{≤R+2,0}}` in the corrected coordinates. -/
private lemma cn_conj_centerInc (E : ℝ) (R : ℕ) (k : NzInt) :
    conjPoly (centerInc E R k) = centerInc E R ⟨-k.1, neg_ne_zero.mpr k.2⟩ := by
  unfold centerInc corrUpd invCoord
  rw [map_sub, cn_conj_truncG, cn_conj_bind₁ (cn_invCoord_sym E R _), cn_conj_updPoly,
    cn_corrCoord_sym, cn_conj_X]
  rfl

private lemma cn_centerEval_conj (g E : ℝ) (R : ℕ) (p : ObsPoly) :
    centerEval g (center g E R) (conjPoly p) = star (centerEval g (center g E R) p) := by
  refine hom_eq_hom ((centerEval g (center g E R)).toRingHom.comp conjPoly)
    ((starRingEnd ℂ).comp (centerEval g (center g E R)).toRingHom) ?_ ?_ p
  · ext r; simp [cn_conj_C, centerEval]
  · intro v
    cases v with
    | m k => simp [cn_conj_X, ObsVar.neg, centerEval, (center_zero_odd_neg g E R k.1).2.2]
    | f k => simp [cn_conj_X, ObsVar.neg, centerEval]
    | w => simp [cn_conj_X, ObsVar.neg, centerEval]
    | γ => simp [cn_conj_X, ObsVar.neg, centerEval]

/-- At centers with vanishing odd coordinates, a polynomial whose monomials all have odd degree
evaluates to `0`. -/
private lemma cn_odd_eval {k : ℤ} (hk : Odd k) {p : ObsPoly} (hp : parityPart k p = p) (g : ℝ)
    (y : ℕ → ℂ) : centerEval g (centerVec y) p = 0 := by
  rw [← hp, parityPart, map_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  split_ifs with h
  · rw [cn_centerEval_val, aeval_monomial, Finsupp.prod]
    obtain ⟨a, ha, h0⟩ : ∃ a ∈ d.support, cnVal g y a = 0 := by
      by_contra hne
      have hev : ∀ a ∈ d.support, Even a.idx := by
        intro a ha
        cases a with
        | m j =>
          by_contra ho
          exact hne ⟨_, ha, by simp [cnVal, centerVec, j.2, ObsVar.idx] at ho ⊢; simp [ho]⟩
        | f j => exact absurd ⟨_, ha, by simp [cnVal]⟩ hne
        | w => exact absurd ⟨_, ha, by simp [cnVal]⟩ hne
        | γ => exact ⟨0, rfl⟩
      have : Even (obsDeg d) := by
        unfold obsDeg
        rw [Finsupp.weight_apply, Finsupp.sum]
        exact Finset.sum_induction _ Even (fun _ _ => Even.add) ⟨0, rfl⟩
          fun a ha => by rw [nsmul_eq_mul]; exact (hev a ha).mul_left _
      rw [Int.even_sub] at h
      exact (Int.not_even_iff_odd.mpr hk) (h.mp this)
    rw [Finset.prod_eq_zero ha (by rw [h0, zero_pow (Finsupp.mem_support_iff.mp ha)]), mul_zero]
  · exact map_zero _

private lemma cn_centerVec_neg (x : ℕ → ℂ) {k : ℤ} (hk : k < 0) :
    centerVec x k = star (centerVec x (-k)) := by
  have h1 : k ≠ 0 := by omega
  have h2 : ¬ 0 < k := by omega
  by_cases ho : Odd k
  · simp [centerVec, h1, ho, ho.neg]
  · have ho' : ¬ Odd (-k) := fun h => ho (by simpa using h.neg)
    simp [centerVec, h1, ho, ho', h2, hk]

/-- (11.55) [lg:eq:center-denominators] and (11.56) [lg:eq:centers]: on a window fixed after `R`
and the index set, for large `g`: the even diagonals
`d_k = (−e^{−2iθ})^k[1 − h_θ² g⁻² k(3 + a_2)] − 1` have `|d_k| ≥ c g⁻²`;
`a = a^{(0)} + O(g⁻²)`, `𝓔(a) = O(g^{−2R−2})`, `|a_k| ≤ K`, `|a_2| < 1/4 + K g⁻²`. -/
theorem center_bounds (R : ℕ) (Ks : Finset NzInt) :
    ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ c K g₀ : ℝ, 0 < c ∧ 0 < K ∧ 1 ≤ g₀ ∧ ∀ g : ℝ, g₀ ≤ g →
      ∀ E : ℝ, |E| ≤ E₁ →
        ‖center g E R 2‖ < 1 / 4 + K / g ^ 2 ∧ ∀ k ∈ Ks,
          ‖center g E R k.1 - centerVec (centerLead g E R) k.1‖ ≤ K / g ^ 2 ∧
          ‖center g E R k.1‖ ≤ K ∧
          ‖centerEval g (center g E R) (centerInc E R k)‖ ≤ K / g ^ (2 * R + 2) ∧
          (Even k.1 → 0 < k.1 → c / g ^ 2 ≤ ‖(-normalPhase E) ^ k.1 *
            (1 - (((normalH E ^ 2 / g ^ 2 * k.1 : ℝ) : ℂ)) * (3 + center g E R 2)) - 1‖) := by
  set n := Ks.sup fun k => k.1.natAbs with hn
  obtain ⟨EN, hEN, CN, gN, hCN, hgN, hN⟩ := cn_newton R R n
  obtain ⟨EL, hEL, CA, gL, hCA, hgL, hL⟩ := cn_lead R n
  obtain ⟨EP, hEP, hP⟩ := parityPart_corrUpd R Ks
  refine ⟨min (min EN EL) (min EP 1), lt_min (lt_min hEN hEL) (lt_min hEP one_pos), 1,
    CN + CA + 1, max (max gN gL) (max (3 * ((n : ℝ) + 1)) (4 * CN + 1)), one_pos, by positivity,
    le_max_of_le_left (le_max_of_le_left hgN), fun g hg E hE => ?_⟩
  have hgN' : gN ≤ g := (le_max_left _ _).trans ((le_max_left _ _).trans hg)
  have hgL' : gL ≤ g := (le_max_right _ _).trans ((le_max_left _ _).trans hg)
  have hg3 : 3 * ((n : ℝ) + 1) ≤ g := (le_max_left _ _).trans ((le_max_right _ _).trans hg)
  have hg4 : 4 * CN + 1 ≤ g := (le_max_right _ _).trans ((le_max_right _ _).trans hg)
  have hEN' : |E| ≤ EN := hE.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hEL' : |E| ≤ EL := hE.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hEP' : |E| ≤ EP := hE.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hE1 : |E| ≤ 1 := hE.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hg1 : 1 ≤ g := hgN.trans hgN'
  obtain ⟨hl0, hlb, -⟩ := hL g hgL' E hEL'
  have hN' := hN g hgN' E hEN'
  set t : ℝ := (g ^ 2)⁻¹ with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  have hKt : ∀ K : ℝ, K / g ^ 2 = K * t := fun K => div_eq_mul_inv _ _
  set y := centerNewton g E R R with hy
  have hc : center g E R = centerVec y := rfl
  have hc2 : center g E R 2 = y 0 := by rw [hc]; exact cn_centerVec_even y 0
  have hCNt : CN * t ≤ 1 / 4 := by
    rw [ht, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    nlinarith
  have ha2 : ‖center g E R 2‖ < 1 / 4 + CN * t := by
    rw [hc2]
    calc ‖y 0‖ = ‖(y 0 - centerLead g E R 0) + centerLead g E R 0‖ := by ring_nf
      _ ≤ ‖y 0 - centerLead g E R 0‖ + ‖centerLead g E R 0‖ := norm_add_le _ _
      _ < CN * t + 1 / 4 := add_lt_add_of_le_of_lt (hN' 0 (Nat.zero_le _)).1 hl0
      _ = _ := by ring
  have hpos : ∀ j ≤ n,
      ‖center g E R (evenIdx j).1 - centerVec (centerLead g E R) (evenIdx j).1‖ ≤
        (CN + CA + 1) / g ^ 2 ∧ ‖center g E R (evenIdx j).1‖ ≤ CN + CA + 1 ∧
      ‖centerEval g (center g E R) (centerInc E R (evenIdx j))‖ ≤
        (CN + CA + 1) / g ^ (2 * R + 2) ∧
      1 / g ^ 2 ≤ ‖(-normalPhase E) ^ (evenIdx j).1 * (1 - (((normalH E ^ 2 / g ^ 2 *
        (evenIdx j).1 : ℝ) : ℂ)) * (3 + center g E R 2)) - 1‖ := by
    intro j hj
    have hv : ∀ x : ℕ → ℂ, centerVec x (evenIdx j).1 = x j := fun x => cn_centerVec_even x j
    obtain ⟨h1, h2⟩ := hN' j hj
    rw [hc, hv, hv]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hKt]; nlinarith
    · calc ‖y j‖ = ‖(y j - centerLead g E R j) + centerLead g E R j‖ := by ring_nf
        _ ≤ CN * t + CA := (norm_add_le _ _).trans (add_le_add h1 (hlb j hj))
        _ ≤ _ := by nlinarith
    · rw [div_eq_mul_inv, show 2 * R + 2 = 2 * (R + 1) by ring, pow_mul, ← inv_pow, ← ht]
      calc _ ≤ CN * t ^ (R + 2) := h2
        _ ≤ (CN + CA + 1) * t ^ (R + 1) := by
          have : t ^ (R + 2) ≤ t ^ (R + 1) := pow_le_pow_of_le_one ht0.le ht1 (by omega)
          have : 0 ≤ t ^ (R + 1) := by positivity
          nlinarith
    · have hjn : (j : ℝ) ≤ n := by exact_mod_cast hj
      obtain ⟨hk0, hk1, hk2⟩ := cn_t_small (g := g) (i := j) hE1 (by linarith)
      rw [← hc, one_div]
      exact hk2.trans (cn_diag_core _ _ _ (cn_norm_phase E _) (by linarith) hk0.le hk1)
  refine ⟨by rw [hKt]; nlinarith, fun k hk => ?_⟩
  have hkn : k.1.natAbs ≤ n := Finset.le_sup (f := fun k : NzInt => k.1.natAbs) hk
  by_cases ho : Odd k.1
  · have hz : ∀ x : ℕ → ℂ, centerVec x k.1 = 0 := fun x => by simp [centerVec, k.2, ho]
    have hK0 : 0 ≤ CN + CA + 1 := by positivity
    refine ⟨by rw [hc, hz, hz, sub_zero, norm_zero]; positivity,
      by rw [hc, hz, norm_zero]; exact hK0, ?_, fun he => absurd he (Int.not_even_iff_odd.mpr ho)⟩
    unfold centerInc
    have hX : centerEval g (centerVec y) (X (.m k)) = centerVec y k.1 := by simp [centerEval]
    rw [map_sub, hc, cn_odd_eval ho (hP E hEP' k hk).1, hX, hz, sub_zero, norm_zero]
    positivity
  rcases lt_or_gt_of_ne k.2 with hneg | hpos'
  · set k' : NzInt := ⟨-k.1, neg_ne_zero.mpr k.2⟩ with hk'
    have hj : k' = evenIdx ((-k.1) / 2 - 1).toNat := by
      apply Subtype.ext
      rw [Int.not_odd_iff_even, Int.even_iff] at ho
      simp only [evenIdx, hk']
      omega
    obtain ⟨p1, p2, p3, -⟩ := hpos ((-k.1) / 2 - 1).toNat (by omega)
    rw [← hj] at p1 p2 p3
    have hneg' : ∀ x : ℕ → ℂ, centerVec x k.1 = star (centerVec x k'.1) :=
      fun x => cn_centerVec_neg x hneg
    have hkk : centerInc E R k = conjPoly (centerInc E R k') := by
      rw [cn_conj_centerInc]
      congr 1
      exact Subtype.ext (neg_neg k.1).symm
    refine ⟨?_, ?_, ?_, fun _ h => absurd h (by omega)⟩
    · rw [hc, hneg', hneg', ← star_sub, norm_star, ← hc]; exact p1
    · rw [hc, hneg', norm_star, ← hc]; exact p2
    · rw [hkk, cn_centerEval_conj, norm_star]; exact p3
  · obtain ⟨p1, p2, p3, p4⟩ := hpos (k.1 / 2 - 1).toNat (by omega)
    have hj : k = evenIdx (k.1 / 2 - 1).toNat := by
      apply Subtype.ext
      rw [Int.not_odd_iff_even, Int.even_iff] at ho
      simp only [evenIdx]
      omega
    rw [← hj] at p1 p2 p3 p4
    exact ⟨p1, p2, p3, fun _ _ => by rw [one_div] at p4; rwa [div_eq_mul_inv, one_mul]⟩

end LSBA
