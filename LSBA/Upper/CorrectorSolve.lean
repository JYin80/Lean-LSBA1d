import LSBA.Upper.CorrectorLinear

/-!
# Solving the coefficient equation

Step (2) of the proof of Lemma 11.9 [lg:lem:centerQ] in Section 11.3.4 [lg:sec:cocycle-correction]:
the finite Neumann polynomial (11.67) [lg:eq:Q-recursion], (11.68) [lg:eq:Q-definition] gives a
coefficient vector `q` on a finite index set, depending on `g` and the energy, with the bounds
(11.69) [lg:eq:raw-Q-coefficient-bounds]: `Σ |q_k| ≤ K g⁻²` and `‖A q − b‖_1 ≤ K g^{−2R−6}`, the
residual `b − A q` vanishing outside the index set.
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Boxes of indices and triangular solves -/

/-- The box `{k : 0 < |k| ≤ N}` of nonzero indices. -/
private def csBox (N : ℕ) : Finset NzInt := (Finset.Icc (-(N : ℤ)) N).subtype fun k => k ≠ 0

private lemma mem_csBox {N : ℕ} {k : NzInt} : k ∈ csBox N ↔ |k.1| ≤ N := by
  rw [csBox, Finset.mem_subtype, Finset.mem_Icc, abs_le]

private lemma csBox_mono {N N' : ℕ} (h : N ≤ N') : csBox N ⊆ csBox N' := fun k hk => by
  rw [mem_csBox] at hk ⊢
  exact hk.trans (by exact_mod_cast h)

/-- An index of modulus larger than every modulus in `S` is not in `S`. -/
private lemma cs_not_mem {S : Finset NzInt} {N : ℕ} (hN : S.sup (fun k => k.1.natAbs) ≤ N)
    {k : NzInt} (hk : (N : ℤ) < |k.1|) : k ∉ S := fun h => by
  have h1 := Finset.le_sup (f := fun k : NzInt => k.1.natAbs) h
  have h2 : ((k.1.natAbs : ℕ) : ℤ) = |k.1| := Int.natCast_natAbs _
  have h3 : ((S.sup fun k : NzInt => k.1.natAbs : ℕ) : ℤ) ≤ N := by exact_mod_cast hN
  have h4 : ((k.1.natAbs : ℕ) : ℤ) ≤ ((S.sup fun k : NzInt => k.1.natAbs : ℕ) : ℤ) := by
    exact_mod_cast h1
  omega

/-- `Σ_r A_r v_r = Σ_r A'_r v_r + Σ_r (A_r − A'_r) v_r`. -/
private lemma cs_split (A A' v : NzInt → ℂ) (s : Finset NzInt) :
    ∑ r ∈ s, A r * v r = ∑ r ∈ s, A' r * v r + ∑ r ∈ s, (A r - A' r) * v r := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun r _ => by ring

/-- Back substitution on the box `0 < |k| ≤ N` for a matrix that vanishes in the rows of the
opposite sign and of larger `|k|`, with diagonal at least `δ` and off-diagonal entries at most
`ρ δ`: the solution is bounded by `(1 + 2ρ)^N Y / δ` when the right side is bounded by `Y`. -/
private lemma cs_solve (T : NzInt → NzInt → ℂ) {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 ≤ ρ) (N : ℕ)
    (hz : ∀ k r : NzInt, |r.1| ≤ N → k.1 * r.1 < 0 ∨ |r.1| < |k.1| → T k r = 0)
    (hd : ∀ r : NzInt, |r.1| ≤ N → δ ≤ ‖T r r‖)
    (ho : ∀ k r : NzInt, |r.1| ≤ N → k ≠ r → ‖T k r‖ ≤ ρ * δ)
    (y : NzInt → ℂ) {Y : ℝ} (hY : 0 ≤ Y) (hy : ∀ k : NzInt, |k.1| ≤ N → ‖y k‖ ≤ Y) :
    ∃ x : NzInt → ℂ, (∀ k : NzInt, (N : ℤ) < |k.1| → x k = 0) ∧
      (∀ k : NzInt, |k.1| ≤ N → ∑ r ∈ csBox N, T k r * x r = y k) ∧
      ∀ k : NzInt, ‖x k‖ ≤ (1 + 2 * ρ) ^ N * Y / δ := by
  induction N generalizing y Y with
  | zero =>
    refine ⟨0, fun _ _ => rfl, fun k hk => ?_, fun k => ?_⟩
    · have := abs_pos.mpr k.2
      push_cast at hk
      omega
    · simp only [Pi.zero_apply, norm_zero, pow_zero, one_mul]
      positivity
  | succ N ih =>
    have hN : ((N + 1 : ℕ) : ℤ) = (N : ℤ) + 1 := by push_cast; ring
    rw [hN] at hz hd ho hy
    set p : NzInt := ⟨(N : ℤ) + 1, by omega⟩ with hp
    set m : NzInt := ⟨-((N : ℤ) + 1), by omega⟩ with hm
    have hpm : p ≠ m := fun h => by
      have := congrArg Subtype.val h
      simp only [hp, hm] at this
      omega
    have hpa : |p.1| = (N : ℤ) + 1 := abs_of_pos (by simp only [hp]; omega)
    have hma : |m.1| = (N : ℤ) + 1 := by
      rw [show m.1 = -((N : ℤ) + 1) from rfl, abs_neg]
      exact abs_of_pos (by omega)
    have hlev : ∀ r : NzInt, |r.1| = (N : ℤ) + 1 → r = p ∨ r = m := by
      intro r hr
      rcases (abs_eq (by omega)).1 hr with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    set xt : NzInt → ℂ := fun k => if |k.1| = (N : ℤ) + 1 then y k / T k k else 0 with hxt
    have hsum : ∀ k, ∑ r ∈ csBox (N + 1), T k r * xt r = T k p * xt p + T k m * xt m := by
      intro k
      rw [← Finset.sum_pair (f := fun r => T k r * xt r) hpm]
      symm
      refine Finset.sum_subset ?_ ?_
      · intro r hr
        rw [Finset.mem_insert, Finset.mem_singleton] at hr
        rw [mem_csBox, hN]
        rcases hr with rfl | rfl
        · exact hpa.le
        · exact hma.le
      · intro r _ hr
        have hne : |r.1| ≠ (N : ℤ) + 1 := fun h => hr (by
          rcases hlev r h with rfl | rfl <;> simp)
        simp [xt, hne]
    have hxtb : ∀ k, ‖xt k‖ ≤ Y / δ := by
      intro k
      simp only [xt]
      split_ifs with h
      · rw [norm_div]
        exact div_le_div₀ hY (hy k h.le) hδ (hd k h.le)
      · rw [norm_zero]
        positivity
    set y' : NzInt → ℂ := fun k => y k - (T k p * xt p + T k m * xt m) with hy'
    have hy'b : ∀ k : NzInt, |k.1| ≤ N → ‖y' k‖ ≤ (1 + 2 * ρ) * Y := by
      intro k hk
      have hkp : k ≠ p := fun h => by rw [h, hpa] at hk; omega
      have hkm : k ≠ m := fun h => by rw [h, hma] at hk; omega
      have h1 : ‖T k p * xt p‖ ≤ ρ * δ * (Y / δ) := by
        rw [norm_mul]
        exact mul_le_mul (ho k p hpa.le hkp) (hxtb p) (norm_nonneg _) (by positivity)
      have h2 : ‖T k m * xt m‖ ≤ ρ * δ * (Y / δ) := by
        rw [norm_mul]
        exact mul_le_mul (ho k m hma.le hkm) (hxtb m) (norm_nonneg _) (by positivity)
      have h3 : ρ * δ * (Y / δ) = ρ * Y := by field_simp
      calc ‖y' k‖ ≤ ‖y k‖ + (‖T k p * xt p‖ + ‖T k m * xt m‖) :=
            (norm_sub_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
        _ ≤ Y + (ρ * Y + ρ * Y) := by
            rw [← h3]
            exact add_le_add (hy k (by omega)) (add_le_add h1 h2)
        _ = (1 + 2 * ρ) * Y := by ring
    obtain ⟨x', hx'0, hx'eq, hx'b⟩ := ih (fun k r hr => hz k r (by omega))
      (fun r hr => hd r (by omega)) (fun k r hr => ho k r (by omega)) y' (by positivity) hy'b
    refine ⟨fun k => x' k + xt k, fun k hk => ?_, fun k hk => ?_, fun k => ?_⟩
    · have hne : |k.1| ≠ (N : ℤ) + 1 := by rw [hN] at hk; omega
      simp only [xt, hne, ite_false, hx'0 k (by rw [hN] at hk; omega), add_zero]
    · rw [hN] at hk
      have e : ∑ r ∈ csBox (N + 1), T k r * (x' r + xt r) =
          ∑ r ∈ csBox N, T k r * x' r + (T k p * xt p + T k m * xt m) := by
        simp only [mul_add, Finset.sum_add_distrib, hsum]
        congr 1
        symm
        refine Finset.sum_subset (csBox_mono (Nat.le_succ N)) fun r hr hr' => ?_
        rw [mem_csBox] at hr hr'
        rw [hx'0 r (by omega), mul_zero]
      rw [e]
      rcases lt_or_eq_of_le hk with hk | hk
      · rw [hx'eq k (by omega)]
        simp only [hy']
        ring
      · have h0 : ∑ r ∈ csBox N, T k r * x' r = 0 := Finset.sum_eq_zero fun r hr => by
          rw [mem_csBox] at hr
          rw [hz k r (by omega) (Or.inr (by omega)), zero_mul]
        rw [h0, zero_add]
        have hTk : T k k ≠ 0 := fun h => by
          have := hd k hk.le
          rw [h, norm_zero] at this
          linarith
        rcases hlev k hk with rfl | rfl
        · rw [hz p m hma.le (Or.inl (by simp only [hp, hm]; nlinarith)), zero_mul, add_zero]
          simp only [xt, hpa, ite_true]
          exact mul_div_cancel₀ _ hTk
        · rw [hz m p hpa.le (Or.inl (by simp only [hp, hm]; nlinarith)), zero_mul, zero_add]
          simp only [xt, hma, ite_true]
          exact mul_div_cancel₀ _ hTk
    · have h1 : 1 ≤ (1 + 2 * ρ) ^ (N + 1) := one_le_pow₀ (by linarith)
      by_cases hk : |k.1| ≤ N
      · have hne : |k.1| ≠ (N : ℤ) + 1 := by omega
        simp only [xt, hne, ite_false, add_zero]
        refine (hx'b k).trans (le_of_eq ?_)
        rw [pow_succ]
        ring
      · change ‖x' k + xt k‖ ≤ _
        rw [hx'0 k (by omega), zero_add]
        refine (hxtb k).trans ?_
        rw [mul_div_assoc]
        exact le_mul_of_one_le_left (by positivity) h1

/-! ### The matrix `A_0` on a box -/

/-- `h_θ² ≤ 1` on `|E| ≤ 1`. -/
private lemma cs_normalH_sq {E : ℝ} (hE : |E| ≤ 1) : normalH E ^ 2 ≤ 1 := by
  unfold normalH freeAngle
  rw [Real.sin_arccos]
  have h1 : (E / 2) ^ 2 ≤ 3 / 4 := by
    have := sq_abs E
    nlinarith [abs_nonneg E]
  have h2 : (1 / 2 : ℝ) ≤ √(1 - (E / 2) ^ 2) := by
    rw [show (1 / 2 : ℝ) = √((1 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h3 : 0 ≤ (2 * √(1 - (E / 2) ^ 2))⁻¹ := by positivity
  have h4 : (2 * √(1 - (E / 2) ^ 2))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  nlinarith

/-- `|e^{−2iθ}| = 1`. -/
private lemma cs_norm_phase (E : ℝ) : ‖-normalPhase E‖ = 1 := by
  unfold normalPhase
  rw [neg_neg, show 2 * ((freeAngle E : ℂ) * Complex.I) =
    ((2 * freeAngle E : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `e^{−2iθ} = 1` at `E = 0`. -/
private lemma cs_phase_zero : normalPhase 0 = 1 := by
  unfold normalPhase freeAngle
  rw [zero_div, Real.arccos_zero, show 2 * (((π / 2 : ℝ) : ℂ) * Complex.I) =
    (π : ℂ) * Complex.I by push_cast; ring, Complex.exp_pi_mul_I, neg_neg]

private lemma cs_continuous_phase : Continuous fun E : ℝ => -normalPhase E := by
  unfold normalPhase freeAngle
  fun_prop

/-- For `|E|` small, `(−e^{−2iθ})^r` is within `1/2` of `(−1)^r` for all `|r| ≤ N`. -/
private lemma cs_window (N : ℕ) : ∃ E₁ : ℝ, 0 < E₁ ∧ ∀ E : ℝ, |E| ≤ E₁ → ∀ r : NzInt,
    |r.1| ≤ N → ‖(-normalPhase E) ^ r.1 - (-1) ^ r.1‖ < 1 / 2 := by
  have hev : ∀ᶠ E in nhds (0 : ℝ), ∀ r ∈ csBox N,
      dist ((-normalPhase E) ^ r.1) ((-normalPhase 0) ^ r.1) < 1 / 2 := by
    rw [Filter.eventually_all_finset]
    intro r _
    have hc : ContinuousAt (fun E => (-normalPhase E) ^ r.1) 0 :=
      cs_continuous_phase.continuousAt.zpow₀ r.1 (Or.inl (by rw [cs_phase_zero]; norm_num))
    exact (Metric.tendsto_nhds.1 hc) (1 / 2) (by norm_num)
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε / 2, by positivity, fun E hE r hr => ?_⟩
  have := h (show dist E 0 < ε by rw [Real.dist_eq, sub_zero]; linarith) r (mem_csBox.2 hr)
  rwa [dist_eq_norm, cs_phase_zero] at this

/-- `A_0` on the box `0 < |r| ≤ N` (Section 11.3.4 [lg:sec:cocycle-correction]): it vanishes in the
rows of the opposite sign and of larger `|k|`, its odd diagonal entries are at least `1/2`, all
diagonal entries are at least `c g⁻²` and the off-diagonal entries are at most `ρ c g⁻²`. -/
private lemma cs_tri (R N : ℕ) :
    ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ c ρ g₀ : ℝ, 0 < c ∧ 0 ≤ ρ ∧ 1 ≤ g₀ ∧
      ∀ g : ℝ, g₀ ≤ g → ∀ E : ℝ, |E| ≤ E₁ →
        (∀ k r : NzInt, |r.1| ≤ N → k.1 * r.1 < 0 ∨ |r.1| < |k.1| → corrMat0 g E R k r = 0) ∧
        (∀ r : NzInt, |r.1| ≤ N → ¬ Even r.1 → 1 / 2 ≤ ‖corrMat0 g E R r r‖) ∧
        (∀ r : NzInt, |r.1| ≤ N → c / g ^ 2 ≤ ‖corrMat0 g E R r r‖) ∧
        (∀ k r : NzInt, |r.1| ≤ N → k ≠ r → ‖corrMat0 g E R k r‖ ≤ ρ * (c / g ^ 2)) := by
  obtain ⟨E₂, hE₂, K₂, g₂, hK₂, hg₂, h₂⟩ := corrMat0_tri R (csBox N)
  obtain ⟨E₃, hE₃, c₃, K₃, g₃, hc₃, hK₃, hg₃, h₃⟩ := center_bounds R (csBox N)
  obtain ⟨E₄, hE₄, h₄⟩ := cs_window N
  have hc : 0 < min c₃ (1 / 2) := lt_min hc₃ (by norm_num)
  refine ⟨min (min E₂ E₃) (min E₄ 1), lt_min (lt_min hE₂ hE₃) (lt_min hE₄ one_pos),
    min c₃ (1 / 2), K₂ / min c₃ (1 / 2), max (max g₂ g₃) (N * (4 + K₃) + 1), hc,
    by positivity, le_max_of_le_left (le_max_of_le_left hg₂), fun g hg E hE => ?_⟩
  have hE2 : |E| ≤ E₂ := hE.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hE3 : |E| ≤ E₃ := hE.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hE4 : |E| ≤ E₄ := hE.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hE1 : |E| ≤ 1 := hE.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hg2 : g₂ ≤ g := (le_max_left _ _).trans ((le_max_left _ _).trans hg)
  have hg3 : g₃ ≤ g := (le_max_right _ _).trans ((le_max_left _ _).trans hg)
  have hgN : N * (4 + K₃) + 1 ≤ g := (le_max_right _ _).trans hg
  have hg1 : 1 ≤ g := hg₂.trans hg2
  have hg0 : 0 < g := by linarith
  have hgg : g ≤ g ^ 2 := by nlinarith
  have hh := cs_normalH_sq hE1
  have hh0 : 0 ≤ normalH E ^ 2 := sq_nonneg _
  have hb3 := h₃ g hg3 E hE3
  have ha2 : ‖center g E R 2‖ ≤ 1 + K₃ := by
    have : K₃ / g ^ 2 ≤ K₃ := div_le_self hK₃.le (one_le_pow₀ hg1)
    linarith [hb3.1]
  have hz : ∀ k r : NzInt, |r.1| ≤ N → k.1 * r.1 < 0 ∨ |r.1| < |k.1| →
      corrMat0 g E R k r = 0 := fun k r hr hkr =>
    (h₂ g hg2 E hE2 r (mem_csBox.2 hr) k).2.2 (hkr.elim Or.inl (fun h => Or.inr (Or.inl h)))
  have hodd : ∀ r : NzInt, |r.1| ≤ N → ¬ Even r.1 → 1 / 2 ≤ ‖corrMat0 g E R r r‖ := by
    intro r hr hre
    rw [(h₂ g hg2 E hE2 r (mem_csBox.2 hr) r).1]
    set u := (-normalPhase E) ^ r.1 with hu
    set X : ℂ := ((normalH E ^ 2 / g ^ 2 * ((|r.1| : ℤ) : ℝ) : ℝ) : ℂ) with hX
    set a := center g E R (2 * r.1.sign) with ha
    have hu1 : ‖u + 1‖ < 1 / 2 := by
      have := h₄ E hE4 r hr
      rwa [(Int.not_even_iff_odd.1 hre).neg_one_zpow, sub_neg_eq_add] at this
    have hun : ‖u‖ = 1 := by rw [hu, norm_zpow, cs_norm_phase, one_zpow]
    have ha' : ‖a‖ ≤ 1 + K₃ := by
      rcases lt_or_gt_of_ne r.2 with hneg | hpos
      · rw [ha, Int.sign_eq_neg_one_of_neg hneg, show (2 : ℤ) * -1 = -2 by rfl,
          (center_zero_odd_neg g E R 2).2.2, norm_star]
        exact ha2
      · rw [ha, Int.sign_eq_one_of_pos hpos, mul_one]
        exact ha2
    have hXn : ‖X‖ ≤ N / g ^ 2 := by
      rw [hX, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hrN : (((|r.1| : ℤ) : ℝ)) ≤ N := by exact_mod_cast hr
      calc normalH E ^ 2 / g ^ 2 * ((|r.1| : ℤ) : ℝ) ≤ 1 / g ^ 2 * N :=
            mul_le_mul (div_le_div_of_nonneg_right hh (by positivity)) hrN (by positivity)
              (by positivity)
        _ = N / g ^ 2 := by ring
    have hXa : ‖u * (X * (3 + a))‖ ≤ 1 := by
      rw [norm_mul, hun, one_mul, norm_mul]
      have h3a : ‖(3 : ℂ) + a‖ ≤ 4 + K₃ := (norm_add_le _ _).trans (by
        rw [show ‖(3 : ℂ)‖ = 3 by norm_num]; linarith)
      calc ‖X‖ * ‖(3 : ℂ) + a‖ ≤ N / g ^ 2 * (4 + K₃) :=
            mul_le_mul hXn h3a (norm_nonneg _) (by positivity)
        _ = N * (4 + K₃) / g ^ 2 := by ring
        _ ≤ 1 := by
            rw [div_le_one (by positivity)]
            linarith
    have e : u * (1 - X * (3 + a)) - 1 = -2 + (u + 1) - u * (X * (3 + a)) := by ring
    have h2 : (2 : ℝ) ≤ ‖u * (1 - X * (3 + a)) - 1‖ + ‖u + 1‖ + ‖u * (X * (3 + a))‖ := by
      have e2 : (-2 : ℂ) = (u * (1 - X * (3 + a)) - 1) - (u + 1) + u * (X * (3 + a)) := by
        rw [e]; ring
      calc (2 : ℝ) = ‖(-2 : ℂ)‖ := by norm_num
        _ ≤ _ := by
            rw [e2]
            exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    linarith
  have hdiag : ∀ r : NzInt, |r.1| ≤ N → min c₃ (1 / 2) / g ^ 2 ≤ ‖corrMat0 g E R r r‖ := by
    intro r hr
    by_cases hre : Even r.1
    · have hc₃ : min c₃ (1 / 2) / g ^ 2 ≤ c₃ / g ^ 2 :=
        div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
      refine hc₃.trans ?_
      rw [(h₂ g hg2 E hE2 r (mem_csBox.2 hr) r).1]
      rcases lt_or_gt_of_ne r.2 with hneg | hpos
      · set r' : NzInt := ⟨-r.1, neg_ne_zero.mpr r.2⟩ with hr'
        have hr'm : r' ∈ csBox N := mem_csBox.2 (by simp only [hr', abs_neg]; exact hr)
        have key := (hb3.2 r' hr'm).2.2.2 (by simp only [hr']; exact hre.neg)
          (by simp only [hr']; omega)
        have hzp : star ((-normalPhase E) ^ r'.1) = (-normalPhase E) ^ r.1 := by
          have h1 : ‖(-normalPhase E) ^ r'.1‖ = 1 := by
            rw [norm_zpow, cs_norm_phase, one_zpow]
          have h2 : star ((-normalPhase E) ^ r'.1) = ((-normalPhase E) ^ r'.1)⁻¹ :=
            (Complex.inv_eq_conj h1).symm
          rw [h2, ← zpow_neg]
          simp [hr']
        have hab : ((|r.1| : ℤ) : ℝ) = ((r'.1 : ℤ) : ℝ) := by
          simp only [hr', abs_of_neg hneg]
        rw [Int.sign_eq_neg_one_of_neg hneg, show (2 : ℤ) * -1 = -2 by rfl,
          (center_zero_odd_neg g E R 2).2.2, hab, ← hzp]
        convert key using 1
        rw [← norm_star]
        congr 1
        simp only [star_sub, star_mul', star_add, star_one, Complex.star_def, Complex.conj_conj,
          Complex.conj_ofReal, map_ofNat]
      · rw [abs_of_pos hpos, Int.sign_eq_one_of_pos hpos, mul_one]
        exact (hb3.2 r (mem_csBox.2 hr)).2.2.2 hre hpos
    · refine le_trans ?_ (hodd r hr hre)
      calc min c₃ (1 / 2) / g ^ 2 ≤ min c₃ (1 / 2) := div_le_self hc.le (one_le_pow₀ hg1)
        _ ≤ 1 / 2 := min_le_right _ _
  refine ⟨hz, hodd, hdiag, fun k r hr hkr => ?_⟩
  refine ((h₂ g hg2 E hE2 r (mem_csBox.2 hr) k).2.1 hkr).trans (le_of_eq ?_)
  field_simp

/-- Solving `A_0 x = y` on the box `0 < |k| ≤ N` (Section 11.3.4 [lg:sec:cocycle-correction]): for
`y` vanishing outside the box and bounded by `Y`, there is `x` supported in the box with
`A_0 x = y` and `|x_k| ≤ C_T g² Y`. -/
private lemma cs_solve0 (R N : ℕ) :
    ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ CT g₀ : ℝ, 0 ≤ CT ∧ 1 ≤ g₀ ∧ ∀ g : ℝ, g₀ ≤ g → ∀ E : ℝ, |E| ≤ E₁ →
      (∀ k r : NzInt, |r.1| ≤ N → k.1 * r.1 < 0 ∨ |r.1| < |k.1| → corrMat0 g E R k r = 0) ∧
      (∀ r : NzInt, |r.1| ≤ N → ¬ Even r.1 → 1 / 2 ≤ ‖corrMat0 g E R r r‖) ∧
      ∀ (y : NzInt → ℂ) (Y : ℝ), 0 ≤ Y → (∀ k : NzInt, |k.1| ≤ N → ‖y k‖ ≤ Y) →
        (∀ k : NzInt, (N : ℤ) < |k.1| → y k = 0) →
        ∃ x : NzInt → ℂ, (∀ k : NzInt, (N : ℤ) < |k.1| → x k = 0) ∧
          (∀ k : NzInt, ∑ r ∈ csBox N, corrMat0 g E R k r * x r = y k) ∧
          ∀ k : NzInt, ‖x k‖ ≤ CT * g ^ 2 * Y := by
  obtain ⟨E₁, hE₁, c, ρ, g₀, hc, hρ, hg₀, h⟩ := cs_tri R N
  refine ⟨E₁, hE₁, (1 + 2 * ρ) ^ N / c, g₀, by positivity, hg₀, fun g hg E hE => ?_⟩
  obtain ⟨hz, hodd, hd, ho⟩ := h g hg E hE
  have hg0 : 0 < g := by linarith
  refine ⟨hz, hodd, fun y Y hY hy hy0 => ?_⟩
  obtain ⟨x, hx0, hxeq, hxb⟩ := cs_solve (corrMat0 g E R) (by positivity : 0 < c / g ^ 2) hρ N
    hz hd ho y hY hy
  refine ⟨x, hx0, fun k => ?_, fun k => (hxb k).trans (le_of_eq ?_)⟩
  · by_cases hk : |k.1| ≤ N
    · exact hxeq k hk
    · rw [hy0 k (by omega)]
      refine Finset.sum_eq_zero fun r hr => ?_
      rw [mem_csBox] at hr
      rw [hz k r hr (Or.inr (by omega)), zero_mul]
  · field_simp

/-- A column `r = ±1` meets a row `k ≠ r` only in the zero pattern of `A_0`. -/
private lemma cs_unit_col {k r : NzInt} (hr : |r.1| = 1) (hkr : k ≠ r) :
    k.1 * r.1 < 0 ∨ |r.1| < |k.1| := by
  have hk := k.2
  have hne : k.1 ≠ r.1 := fun h => hkr (Subtype.ext h)
  rcases (abs_eq zero_le_one).1 hr with h | h <;> rw [h] at hne ⊢ <;>
    rcases lt_or_gt_of_ne hk with h0 | h0
  · left; linarith
  · right; rw [abs_of_pos h0]; norm_num; omega
  · right; rw [abs_of_neg h0]; norm_num; omega
  · left; linarith

/-- The Neumann recursion (11.67) [lg:eq:Q-recursion] after `s + 1` steps: on a box `0 < |k| ≤ N`,
the partial sum `Q = Σ_{j ≤ s} q^{(j)}` and the last term `q^{(s)}` satisfy `|Q_k| ≤ C g⁻²`,
`|q^{(s)}_k| ≤ C g^{−2s−2}` and `b − A Q = −(A − A_0) q^{(s)}`. -/
private lemma cs_iter (R : ℕ) (s : ℕ) :
    ∃ N : ℕ, ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ C g₀ : ℝ, 0 ≤ C ∧ 1 ≤ g₀ ∧
      ∀ g : ℝ, g₀ ≤ g → ∀ E : ℝ, |E| ≤ E₁ →
        ∃ Q qs : NzInt → ℂ, (∀ k : NzInt, (N : ℤ) < |k.1| → Q k = 0 ∧ qs k = 0) ∧
          (∀ k : NzInt, ‖Q k‖ ≤ C / g ^ 2) ∧ (∀ k : NzInt, ‖qs k‖ ≤ C / g ^ (2 * s + 2)) ∧
          ∀ k : NzInt, driftCoeff g E R k - ∑ r ∈ csBox N, corrMat g E R k r * Q r =
            -∑ r ∈ csBox N, (corrMat g E R k r - corrMat0 g E R k r) * qs r := by
  induction s with
  | zero =>
    obtain ⟨S, -, Es, hEs, hS⟩ := corrCoeff_support R ∅
    set N := max 1 (S.sup fun k => k.1.natAbs) with hN
    have hN1 : (1 : ℤ) ≤ N := by exact_mod_cast le_max_left 1 _
    obtain ⟨Ea, hEa, CT, ga, hCT, hga, hA⟩ := cs_solve0 R N
    obtain ⟨Eb, hEb, Kb, gb, hKb, hgb, hb⟩ := driftCoeff_sub_le R
    refine ⟨N, min (min Es Ea) (min Eb 1), lt_min (lt_min hEs hEa) (lt_min hEb one_pos),
      1 + CT * Kb, max ga gb, by positivity, le_max_of_le_left hga, fun g hg E hE => ?_⟩
    have hEs' : |E| ≤ Es := hE.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hEa' : |E| ≤ Ea := hE.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hEb' : |E| ≤ Eb := hE.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hE1 : |E| ≤ 1 := hE.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hga' : ga ≤ g := (le_max_left _ _).trans hg
    have hgb' : gb ≤ g := (le_max_right _ _).trans hg
    have hg1 : 1 ≤ g := hga.trans hga'
    have hg0 : 0 < g := by linarith
    have hh := cs_normalH_sq hE1
    obtain ⟨hz, hodd, hsol⟩ := hA g hga' E hEa'
    set ℓ : NzInt → ℂ := fun k =>
      if |k.1| = 1 then ((normalH E ^ 2 / (2 * g ^ 2) : ℝ) : ℂ) else 0 with hℓ
    set xl : NzInt → ℂ := fun k => ℓ k / corrMat0 g E R k k with hxl
    have hbz : ∀ k : NzInt, (N : ℤ) < |k.1| → driftCoeff g E R k = 0 := fun k hk =>
      (hS g E hEs' k (cs_not_mem (le_max_right _ _) hk)).1
    have hℓz : ∀ k : NzInt, (N : ℤ) < |k.1| → ℓ k = 0 := fun k hk => by
      have : |k.1| ≠ 1 := by omega
      simp [ℓ, this]
    have hxlz : ∀ k : NzInt, (N : ℤ) < |k.1| → xl k = 0 := fun k hk => by
      simp only [xl, hℓz k hk, zero_div]
    have hne : ∀ k : NzInt, |k.1| = 1 → corrMat0 g E R k k ≠ 0 := fun k hk1 h => by
      have hodd' : ¬ Even k.1 := by
        rcases (abs_eq zero_le_one).1 hk1 with h | h <;> rw [h] <;> decide
      have := hodd k (by omega) hodd'
      rw [h, norm_zero] at this
      norm_num at this
    have hAxl : ∀ k : NzInt, ∑ r ∈ csBox N, corrMat0 g E R k r * xl r = ℓ k := by
      intro k
      rw [Finset.sum_eq_single k]
      · by_cases hk1 : |k.1| = 1
        · simp only [xl]
          exact mul_div_cancel₀ _ (hne k hk1)
        · simp [xl, ℓ, hk1]
      · intro r hr hrk
        by_cases hr1 : |r.1| = 1
        · rw [hz k r (mem_csBox.1 hr) (cs_unit_col hr1 hrk.symm), zero_mul]
        · simp [xl, ℓ, hr1]
      · intro hk
        rw [mem_csBox] at hk
        rw [hxlz k (by omega), mul_zero]
    have hxlb : ∀ k : NzInt, ‖xl k‖ ≤ 1 / g ^ 2 := by
      intro k
      simp only [xl, ℓ]
      split_ifs with hk1
      · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have h2 := hodd k (by omega) (by
          rcases (abs_eq zero_le_one).1 hk1 with h | h <;> rw [h] <;> decide)
        calc normalH E ^ 2 / (2 * g ^ 2) / ‖corrMat0 g E R k k‖
            ≤ normalH E ^ 2 / (2 * g ^ 2) / (1 / 2) :=
              div_le_div_of_nonneg_left (by positivity) (by norm_num) h2
          _ = normalH E ^ 2 / g ^ 2 := by field_simp
          _ ≤ 1 / g ^ 2 := div_le_div_of_nonneg_right hh (by positivity)
      · rw [zero_div, norm_zero]
        positivity
    obtain ⟨x', hx'0, hx'eq, hx'b⟩ := hsol (fun k => driftCoeff g E R k - ℓ k) (Kb / g ^ 4)
      (by positivity) (fun k _ => hb g hgb' E hEb' k)
      (fun k hk => by rw [hbz k hk, hℓz k hk, sub_zero])
    have hQb : ∀ k : NzInt, ‖xl k + x' k‖ ≤ (1 + CT * Kb) / g ^ 2 := by
      intro k
      have h2 : CT * g ^ 2 * (Kb / g ^ 4) = CT * Kb / g ^ 2 := by field_simp
      calc ‖xl k + x' k‖ ≤ 1 / g ^ 2 + CT * Kb / g ^ 2 :=
            (norm_add_le _ _).trans (add_le_add (hxlb k) ((hx'b k).trans h2.le))
        _ = (1 + CT * Kb) / g ^ 2 := by ring
    refine ⟨fun k => xl k + x' k, fun k => xl k + x' k, fun k hk => ?_, hQb, fun k => ?_,
      fun k => ?_⟩
    · simp only [hxlz k hk, hx'0 k hk, add_zero, and_self]
    · simpa using hQb k
    · have h1 : ∑ r ∈ csBox N, corrMat0 g E R k r * (xl r + x' r) = driftCoeff g E R k := by
        simp only [mul_add, Finset.sum_add_distrib, hAxl, hx'eq]
        ring
      rw [cs_split (corrMat g E R k) (corrMat0 g E R k), h1]
      ring
  | succ s ih =>
    obtain ⟨N, E₁, hE₁, C, g₀, hC, hg₀, h⟩ := ih
    obtain ⟨S, -, Es, hEs, hS⟩ := corrCoeff_support R (csBox N)
    set N' := max N (S.sup fun k => k.1.natAbs) with hN'
    have hNN : (N : ℤ) ≤ N' := by exact_mod_cast le_max_left _ _
    obtain ⟨Ea, hEa, CT, ga, hCT, hga, hA⟩ := cs_solve0 R N'
    obtain ⟨Ed, hEd, Kd, gd, hKd, hgd, hd⟩ := corrMat_sub_corrMat0_le R (csBox N)
    set n : ℝ := ((csBox N).card : ℝ) with hn
    have hn0 : 0 ≤ n := Nat.cast_nonneg _
    refine ⟨N', min (min E₁ Es) (min Ea Ed), lt_min (lt_min hE₁ hEs) (lt_min hEa hEd),
      C + CT * n * Kd * C, max (max g₀ ga) gd, by positivity,
      le_max_of_le_left (le_max_of_le_left hg₀), fun g hg E hE => ?_⟩
    have hE1 : |E| ≤ E₁ := hE.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hEs' : |E| ≤ Es := hE.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hEa' : |E| ≤ Ea := hE.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hEd' : |E| ≤ Ed := hE.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hg0' : g₀ ≤ g := (le_max_left _ _).trans ((le_max_left _ _).trans hg)
    have hga' : ga ≤ g := (le_max_right _ _).trans ((le_max_left _ _).trans hg)
    have hgd' : gd ≤ g := (le_max_right _ _).trans hg
    have hg1 : 1 ≤ g := hg₀.trans hg0'
    have hg0 : 0 < g := by linarith
    obtain ⟨Q, qs, hQ0, hQb, hqsb, hres⟩ := h g hg0' E hE1
    obtain ⟨-, -, hsol⟩ := hA g hga' E hEa'
    set y : NzInt → ℂ :=
      fun k => -∑ r ∈ csBox N, (corrMat g E R k r - corrMat0 g E R k r) * qs r with hy
    have hyb : ∀ k : NzInt, ‖y k‖ ≤ n * (Kd / g ^ 4 * (C / g ^ (2 * s + 2))) := by
      intro k
      simp only [hy, norm_neg]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ _ fun r hr => ?_).trans (by rw [nsmul_eq_mul])
      rw [norm_mul]
      exact mul_le_mul (hd g hgd' E hEd' r hr k) (hqsb r) (norm_nonneg _) (by positivity)
    have hy0 : ∀ k : NzInt, (N' : ℤ) < |k.1| → y k = 0 := by
      intro k hk
      obtain ⟨-, h2⟩ := hS g E hEs' k (cs_not_mem (le_max_right _ _) hk)
      simp only [hy, neg_eq_zero]
      refine Finset.sum_eq_zero fun r hr => ?_
      rw [(h2 r hr).1, (h2 r hr).2, sub_zero, zero_mul]
    obtain ⟨x, hx0, hxeq, hxb⟩ := hsol y _ (by positivity) (fun k _ => hyb k) hy0
    have hxb' : ∀ k : NzInt, ‖x k‖ ≤ CT * n * Kd * C / g ^ (2 * (s + 1) + 2) := by
      intro k
      refine (hxb k).trans (le_of_eq ?_)
      rw [show 2 * (s + 1) + 2 = (2 * s + 2) + 2 by ring]
      field_simp
      ring
    refine ⟨fun k => Q k + x k, x, fun k hk => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
    · exact ⟨show Q k + x k = 0 by rw [(hQ0 k (by omega)).1, hx0 k hk, add_zero], hx0 k hk⟩
    · have hp : g ^ 2 ≤ g ^ (2 * (s + 1) + 2) := pow_le_pow_right₀ hg1 (by omega)
      calc ‖Q k + x k‖ ≤ C / g ^ 2 + CT * n * Kd * C / g ^ 2 :=
            (norm_add_le _ _).trans (add_le_add (hQb k) ((hxb' k).trans
              (div_le_div_of_nonneg_left (by positivity) (by positivity) hp)))
        _ = (C + CT * n * Kd * C) / g ^ 2 := by ring
    · exact (hxb' k).trans (div_le_div_of_nonneg_right (by linarith) (by positivity))
    · have hsub : csBox N ⊆ csBox N' := csBox_mono (le_max_left _ _)
      have e1 : ∑ r ∈ csBox N', corrMat g E R k r * Q r =
          ∑ r ∈ csBox N, corrMat g E R k r * Q r :=
        (Finset.sum_subset hsub fun r _ hr => by
          rw [mem_csBox] at hr
          rw [(hQ0 r (by omega)).1, mul_zero]).symm
      have e2 : ∑ r ∈ csBox N', corrMat g E R k r * (Q r + x r) =
          ∑ r ∈ csBox N', corrMat g E R k r * Q r +
            (∑ r ∈ csBox N', corrMat0 g E R k r * x r +
              ∑ r ∈ csBox N', (corrMat g E R k r - corrMat0 g E R k r) * x r) := by
        rw [← cs_split (corrMat g E R k) (corrMat0 g E R k), ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun r _ => by ring
      rw [e2, e1, hxeq k]
      have := hres k
      simp only [hy] at this ⊢
      linear_combination this

/-- (11.67) [lg:eq:Q-recursion]–(11.69) [lg:eq:raw-Q-coefficient-bounds]: for each `R` there
are a finite index set, a window, `K`, `g₀` and coefficients `q(g, E)` supported in the index set
with `Σ |q_k| ≤ K g⁻²`, `(b − A q)_k = 0` outside the index set and
`Σ_k |b_k − (A q)_k| ≤ K g^{−2R−6}`, for `g ≥ g₀` and `|E|` in the window. -/
theorem corrCoeff_solve (R : ℕ) :
    ∃ Ks : Finset NzInt, ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ K g₀ : ℝ, 0 < K ∧ 1 ≤ g₀ ∧
      ∃ q : ℝ → ℝ → NzInt → ℂ, ∀ g : ℝ, g₀ ≤ g → ∀ E : ℝ, |E| ≤ E₁ →
        (∀ k ∉ Ks, q g E k = 0) ∧ ∑ k ∈ Ks, ‖q g E k‖ ≤ K / g ^ 2 ∧
          (∀ k ∉ Ks, driftCoeff g E R k = ∑ r ∈ Ks, corrMat g E R k r * q g E r) ∧
          ∑ k ∈ Ks, ‖driftCoeff g E R k - ∑ r ∈ Ks, corrMat g E R k r * q g E r‖ ≤
            K / g ^ (2 * R + 6) := by
  obtain ⟨N, E₁, hE₁, C, g₀, hC, hg₀, h⟩ := cs_iter R R
  obtain ⟨S, -, Es, hEs, hS⟩ := corrCoeff_support R (csBox N)
  set N' := max N (S.sup fun k => k.1.natAbs) with hN'
  have hNN : (N : ℤ) ≤ N' := by exact_mod_cast le_max_left _ _
  obtain ⟨Ed, hEd, Kd, gd, hKd, hgd, hd⟩ := corrMat_sub_corrMat0_le R (csBox N)
  set n : ℝ := ((csBox N).card : ℝ) with hn
  set n' : ℝ := ((csBox N').card : ℝ) with hn'
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hn0' : 0 ≤ n' := Nat.cast_nonneg _
  set K := n' * C + n' * (n * (Kd * C)) + 1 with hK
  set E₀ := min (min E₁ Es) Ed with hE₀
  set G := max g₀ gd with hG
  have hq : ∀ g E : ℝ, ∃ v : NzInt → ℂ, G ≤ g → |E| ≤ E₀ →
      (∀ k ∉ csBox N', v k = 0) ∧ ∑ k ∈ csBox N', ‖v k‖ ≤ K / g ^ 2 ∧
        (∀ k ∉ csBox N', driftCoeff g E R k = ∑ r ∈ csBox N', corrMat g E R k r * v r) ∧
        ∑ k ∈ csBox N', ‖driftCoeff g E R k - ∑ r ∈ csBox N', corrMat g E R k r * v r‖ ≤
          K / g ^ (2 * R + 6) := by
    intro g E
    by_cases hgE : G ≤ g ∧ |E| ≤ E₀
    · obtain ⟨hg, hE⟩ := hgE
      have hE1 : |E| ≤ E₁ := hE.trans ((min_le_left _ _).trans (min_le_left _ _))
      have hEs' : |E| ≤ Es := hE.trans ((min_le_left _ _).trans (min_le_right _ _))
      have hEd' : |E| ≤ Ed := hE.trans (min_le_right _ _)
      have hg0' : g₀ ≤ g := (le_max_left _ _).trans hg
      have hgd' : gd ≤ g := (le_max_right _ _).trans hg
      have hg1 : 1 ≤ g := hg₀.trans hg0'
      have hg0 : 0 < g := by linarith
      obtain ⟨Q, qs, hQ0, hQb, hqsb, hres⟩ := h g hg0' E hE1
      have hout : ∀ k ∉ csBox N', (N : ℤ) < |k.1| := fun k hk => by
        rw [mem_csBox] at hk
        omega
      have hsub : csBox N ⊆ csBox N' := csBox_mono (le_max_left _ _)
      have e1 : ∀ k, ∑ r ∈ csBox N', corrMat g E R k r * Q r =
          ∑ r ∈ csBox N, corrMat g E R k r * Q r := fun k =>
        (Finset.sum_subset hsub fun r _ hr => by
          rw [mem_csBox] at hr
          rw [(hQ0 r (by omega)).1, mul_zero]).symm
      have hrb : ∀ k, ‖driftCoeff g E R k - ∑ r ∈ csBox N', corrMat g E R k r * Q r‖ ≤
          n * (Kd / g ^ 4 * (C / g ^ (2 * R + 2))) := by
        intro k
        rw [e1, hres, norm_neg]
        refine (norm_sum_le _ _).trans ?_
        refine (Finset.sum_le_card_nsmul _ _ _ fun r hr => ?_).trans (by rw [nsmul_eq_mul])
        rw [norm_mul]
        exact mul_le_mul (hd g hgd' E hEd' r hr k) (hqsb r) (norm_nonneg _) (by positivity)
      refine ⟨Q, fun _ _ => ⟨fun k hk => (hQ0 k (hout k hk)).1, ?_, fun k hk => ?_, ?_⟩⟩
      · refine (Finset.sum_le_card_nsmul _ _ _ fun k _ => hQb k).trans ?_
        rw [nsmul_eq_mul, ← hn', mul_div_assoc']
        have : 0 ≤ n' * (n * (Kd * C)) := by positivity
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
      · rw [e1, ← sub_eq_zero, hres, neg_eq_zero]
        obtain ⟨-, h2⟩ := hS g E hEs' k (cs_not_mem (N := N') (le_max_right _ _) (by
          rw [mem_csBox] at hk
          omega))
        refine Finset.sum_eq_zero fun r hr => ?_
        rw [(h2 r hr).1, (h2 r hr).2, sub_zero, zero_mul]
      · refine (Finset.sum_le_card_nsmul _ _ _ fun k _ => hrb k).trans ?_
        rw [nsmul_eq_mul, ← hn']
        have e : n' * (n * (Kd / g ^ 4 * (C / g ^ (2 * R + 2)))) =
            n' * (n * (Kd * C)) / g ^ (2 * R + 6) := by
          rw [show 2 * R + 6 = 4 + (2 * R + 2) by ring]
          field_simp
          ring
        rw [e]
        have : 0 ≤ n' * C := by positivity
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hgE⟩
  choose q hq using hq
  exact ⟨csBox N', E₀, lt_min (lt_min hE₁ hEs) hEd, K, G, by positivity,
    le_max_of_le_left hg₀, q, fun g hg E hE => hq g E hg hE⟩

end LSBA
