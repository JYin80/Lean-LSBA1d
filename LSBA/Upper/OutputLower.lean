import LSBA.Upper.Buffer
import LSBA.Upper.ChainBridge
import LSBA.Upper.PrepGood
import LSBA.Upper.CutLevels

/-!
# The lower bound for the transported normal

Section 9.4.2 [su:sec:discarded-output]: `‖v_{q-1}‖ ≥ 2 v_min` outside an event whose
intersection with the regular chain has arbitrarily small polynomial probability, at fixed
prepared data. Regime (i): the generic-scale iteration at `η = g²` (so `F^{(η)} = F` and
`W^{-1+δ} ≤ g²` with `δ = 1 - 2β`) on the active window is the lower half of (9.68)
[us:eq:profile] at `j = q - 1`; with `b_4 ≥ (1 + W^{ε/400})⁻¹ ‖P v_4‖²` it gives
`‖v_{q-1}‖² ≥ 2 g^{-2(q-5)} W^{-3ε/400} ‖P v_4‖²`, the square of `2 v_min`, up to the margin of
the output cut. Regime (ii): Lemma G.3 [nc:lem:buffer] on the active window gives
`‖v_{q-1}‖² ≥ 2 υ^{-(q-5)} W^{-8θ} ‖v_4‖²`. Both use the forward bridge of the chart to the
Riccati chain.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `Re x*w = Re w*x`. -/
private lemma outputLower_re_swap {W : ℕ} (x w : Fin W → ℂ) :
    (star x ⬝ᵥ w).re = (star w ⬝ᵥ x).re := by
  have : star w ⬝ᵥ x = star (star x ⬝ᵥ w) := by
    simp [dotProduct, mul_comm]
  rw [this, Complex.star_def, Complex.conj_re]

open scoped MatrixOrder ComplexOrder in
/-- For a strictly positive `N` and every vector `a`, `Re v*N⁻¹v ≥ 2 Re a*v - Re a*Na`. -/
private lemma outputLower_dual {W : ℕ} {N : Matrix (Fin W) (Fin W) ℂ} (hN : IsStrictlyPositive N)
    (a v : Fin W → ℂ) :
    2 * (star a ⬝ᵥ v).re - (star a ⬝ᵥ (N *ᵥ a)).re ≤ (star v ⬝ᵥ (N⁻¹ *ᵥ v)).re := by
  have hP : N.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hN.nonneg
  have hH : Nᴴ = N := hP.isHermitian
  have hU : IsUnit N.det := (Matrix.isUnit_iff_isUnit_det N).mp hN.isUnit
  set y : Fin W → ℂ := N⁻¹ *ᵥ v with hy
  have hNy : N *ᵥ y = v := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv N hU, Matrix.one_mulVec]
  have h0 := (Complex.nonneg_iff.mp (hP.dotProduct_mulVec_nonneg (a - y))).1
  have hyN : ∀ z : Fin W → ℂ, star y ⬝ᵥ (N *ᵥ z) = star v ⬝ᵥ z := by
    intro z
    have h := Matrix.star_mulVec N y
    rw [hNy, hH] at h
    rw [Matrix.dotProduct_mulVec, ← h]
  rw [Matrix.mulVec_sub, star_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, hNy,
    hyN] at h0
  simp only [Complex.sub_re] at h0
  have e1 := outputLower_re_swap v a
  have e2 : (star y ⬝ᵥ v).re = (star v ⬝ᵥ (N⁻¹ *ᵥ v)).re := by
    rw [outputLower_re_swap]
  rw [e2] at h0
  linarith

/-- `Re u*u = ∑ ‖u_i‖²`. -/
private lemma outputLower_re_self {W : ℕ} (u : Fin W → ℂ) :
    (star u ⬝ᵥ u).re = ∑ i, ‖u i‖ ^ 2 := by
  simp only [dotProduct, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

open scoped MatrixOrder ComplexOrder in
/-- For Hermitian `R` and an orthogonal projection `P` with `‖(η R) P‖ ≤ X`,
`Re v*(1 + η² R²)⁻¹v ≥ (1 + X²)⁻¹ ‖P v‖²`. With `P = 1_{[-X, X]}(η R)` of (9.4)
[su:eq:source-projection], `η = g²` and `X² = W^{ε/400}`, this is the bound
`b_4 ≥ (1 + W^{ε/400})⁻¹ ‖P v_4‖²` of Section 9.4.2 [su:sec:discarded-output]. -/
private lemma outputLower_b_lower {W : ℕ} {R P : Matrix (Fin W) (Fin W) ℂ} (hR : R.IsHermitian)
    (η : ℝ) (hP : Pᴴ = P) (hPP : P * P = P) {X : ℝ}
    (hAP : ‖((η : ℂ) • R) * P‖ ≤ X) (v : Fin W → ℂ) :
    (1 + X ^ 2)⁻¹ * ∑ i, ‖(P *ᵥ v) i‖ ^ 2 ≤
      (star v ⬝ᵥ ((1 + ((η : ℂ) ^ 2) • (R * R))⁻¹ *ᵥ v)).re := by
  set N : Matrix (Fin W) (Fin W) ℂ := 1 + ((η : ℂ) ^ 2) • (R * R) with hN
  set A : Matrix (Fin W) (Fin W) ℂ := (η : ℂ) • R with hA
  have hAH : Aᴴ = A := by
    rw [hA, Matrix.conjTranspose_smul, hR.eq]
    simp
  have hNA : N = 1 + A * A := by
    rw [hN, hA, Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]
  have hSP : IsStrictlyPositive N := by
    have h1 : (η : ℂ) ^ 2 = ((η ^ 2 : ℝ) : ℂ) := by push_cast; ring
    have h2 : (0 : Matrix (Fin W) (Fin W) ℂ) ≤ star R * R := star_mul_self_nonneg R
    have h3 : (0 : Matrix (Fin W) (Fin W) ℂ) ≤ (η : ℂ) ^ 2 • (R * R) := by
      rw [h1]
      have : star R = R := hR.eq
      rw [this] at h2
      exact smul_nonneg (Complex.zero_le_real.mpr (sq_nonneg η)) h2
    exact IsStrictlyPositive.add_nonneg isStrictlyPositive_one h3
  obtain ⟨u, hu⟩ : ∃ u : Fin W → ℂ, u = P *ᵥ v := ⟨_, rfl⟩
  rw [← hu]
  set lam : ℝ := (1 + X ^ 2)⁻¹ with hlam
  have hlam0 : 0 < lam := by positivity
  have hPu : P *ᵥ u = u := by rw [hu, Matrix.mulVec_mulVec, hPP]
  have hsu : star u = star v ᵥ* P := by rw [hu, Matrix.star_mulVec, hP]
  have huv : (star u ⬝ᵥ v).re = ∑ i, ‖u i‖ ^ 2 := by
    rw [← outputLower_re_self]
    have h1 : star u ⬝ᵥ v = star v ⬝ᵥ u := by rw [hsu, ← Matrix.dotProduct_mulVec, hu]
    have h2 : star u ⬝ᵥ u = star v ⬝ᵥ u := by rw [hsu, ← Matrix.dotProduct_mulVec, hPu]
    rw [h1, h2]
  have hAu : l2Norm (A *ᵥ u) ≤ X * l2Norm u := by
    have h1 : A *ᵥ u = (A * P) *ᵥ u := by rw [← Matrix.mulVec_mulVec, hPu]
    rw [h1]
    exact (l2Norm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right hAP (Real.sqrt_nonneg _))
  have hNu : (star u ⬝ᵥ (N *ᵥ u)).re ≤ (1 + X ^ 2) * ∑ i, ‖u i‖ ^ 2 := by
    have h1 : star u ⬝ᵥ (N *ᵥ u) = star u ⬝ᵥ u + star (A *ᵥ u) ⬝ᵥ (A *ᵥ u) := by
      have hsA : star (A *ᵥ u) = star u ᵥ* A := by rw [Matrix.star_mulVec, hAH]
      rw [hNA, Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec, hsA,
        Matrix.dotProduct_mulVec]
    rw [h1, Complex.add_re, outputLower_re_self, outputLower_re_self]
    have h2 : ∑ i, ‖(A *ᵥ u) i‖ ^ 2 = l2Norm (A *ᵥ u) ^ 2 := by
      rw [l2Norm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    have h3 : ∑ i, ‖u i‖ ^ 2 = l2Norm u ^ 2 := by
      rw [l2Norm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    rw [h2, h3]
    have h4 : l2Norm (A *ᵥ u) ^ 2 ≤ (X * l2Norm u) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hAu 2
    nlinarith
  have key := outputLower_dual hSP ((lam : ℂ) • u) v
  have ha : star ((lam : ℂ) • u) = (lam : ℂ) • star u := by
    rw [star_smul]; simp
  have e1 : (star ((lam : ℂ) • u) ⬝ᵥ v).re = lam * (star u ⬝ᵥ v).re := by
    rw [ha, smul_dotProduct, smul_eq_mul, Complex.re_ofReal_mul]
  have e2 : (star ((lam : ℂ) • u) ⬝ᵥ (N *ᵥ ((lam : ℂ) • u))).re =
      lam * lam * (star u ⬝ᵥ (N *ᵥ u)).re := by
    rw [ha, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
    simp only [smul_eq_mul]
    rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  rw [e1, e2, huv] at key
  have hl : lam * (1 + X ^ 2) = 1 := by rw [hlam]; field_simp
  have h5 : lam * lam * (star u ⬝ᵥ (N *ᵥ u)).re ≤ lam * ∑ i, ‖u i‖ ^ 2 := by
    calc lam * lam * (star u ⬝ᵥ (N *ᵥ u)).re ≤ lam * lam * ((1 + X ^ 2) * ∑ i, ‖u i‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hNu (by positivity)
      _ = lam * ∑ i, ‖u i‖ ^ 2 := by
          calc lam * lam * ((1 + X ^ 2) * ∑ i, ‖u i‖ ^ 2)
              = lam * (lam * (1 + X ^ 2)) * ∑ i, ‖u i‖ ^ 2 := by ring
            _ = lam * ∑ i, ‖u i‖ ^ 2 := by rw [hl]; ring
  linarith

/-- The active window is injective. -/
private lemma outputLower_actWin_inj (q : ℕ) : Function.Injective (actWin q) := by
  intro a b h
  exact Fin.ext (by simpa [actWin] using congrArg Fin.val h)

/-- An event of `q` blocks contained in the preimage of an event of the active window has at most
the probability of that event (the window sample is measure preserving). -/
private lemma outputLower_measure {W q : ℕ} (S : Set (Ω W (q - 5))) (T : Set (Ω W q))
    (hT : T ⊆ windowSample (actWin q) ⁻¹' S) : μ W q T ≤ μ W (q - 5) S := by
  have hmp := measurePreserving_windowSample W q (q - 5) (outputLower_actWin_inj q)
  calc μ W q T ≤ μ W q (windowSample (actWin q) ⁻¹' S) := measure_mono hT
    _ ≤ (Measure.map (windowSample (actWin q)) (μ W q)) S :=
        Measure.le_map_apply hmp.aemeasurable S
    _ = μ W (q - 5) S := by rw [hmp.map_eq]

/-- Regularity (9.3) [us:eq:regular] of `R_5, …, R_{q-2}` and of `R_4 = R` is regularity of the
states `0, …, q - 6` of the Riccati chain on the active window. -/
private lemma outputLower_regular {W q : ℕ} (hq : 5 ≤ q) (g E : ℝ)
    (R : Matrix (Fin W) (Fin W) ℂ) (hR : IsRegularState W g R) (ω : Ω W q)
    (hreg : ∀ j, 5 ≤ j → j ≤ q - 2 → IsRegularState W g (chartR W g E q R ω j)) :
    ∀ j, j < q - 5 →
      IsRegularState W g (ricChain W g E (q - 5) R (windowSample (actWin q) ω) j) := by
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simpa [ricChain] using hR
  · have h := (chartR_eq_ricChain hq g E R ω (m := j) (by omega)).1
    rw [← h]
    exact hreg (j + 4) (by omega) (by omega)

/-- `R_{[q-1,5]}` is the product of length `q - 5` of the Riccati chain on the active window. -/
private lemma outputLower_prod {W q : ℕ} (hq : 5 ≤ q) (g E : ℝ)
    (R : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) :
    chartProd W g E q R ω (q - 1) =
      ricProd W g E (q - 5) R (windowSample (actWin q) ω) (q - 5) := by
  have h := (chartR_eq_ricChain hq g E R ω (m := q - 5) le_rfl).2
  rw [show q - 5 + 4 = q - 1 by omega] at h
  exact h

/-- `‖u‖₂² = ∑ ‖u_i‖²`. -/
private lemma outputLower_l2_sq {W : ℕ} (u : Fin W → ℂ) :
    l2Norm u ^ 2 = ∑ i, ‖u i‖ ^ 2 := by
  rw [l2Norm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]

/-- The exponents of regime (i): `2 κ² p ≤ c η^{-h} b` when `κ² = η^{-h} y²`, `y X³ = 1`,
`X⁴ ≥ 4 / c` and `b ≥ (1 + X²)⁻¹ p`, with `X = W^{ε/800}` and `y = W^{-3ε/800}`. -/
private lemma outputLower_weak_slack {c X y G p b : ℝ} (hc : 0 < c) (hX : 1 ≤ X)
    (hy : y * X ^ 3 = 1) (h4 : 4 ≤ c * X ^ 4) (hG : 0 ≤ G) (hp : 0 ≤ p)
    (hb : (1 + X ^ 2)⁻¹ * p ≤ b) :
    2 * (G * y ^ 2) * p ≤ c * G * b := by
  have hX2 : 1 ≤ X ^ 2 := by nlinarith
  have hz : y ^ 2 * X ^ 6 = 1 := by
    calc y ^ 2 * X ^ 6 = (y * X ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hy]; norm_num
  have h1 : 2 * y ^ 2 * (1 + X ^ 2) ≤ c := by
    have h2 := mul_le_mul_of_nonneg_right h4 (by positivity : 0 ≤ y ^ 2 * X ^ 2)
    have h3 : c * X ^ 4 * (y ^ 2 * X ^ 2) = c := by
      calc c * X ^ 4 * (y ^ 2 * X ^ 2) = c * (y ^ 2 * X ^ 6) := by ring
        _ = c := by rw [hz]; ring
    have h5 : y ^ 2 ≤ y ^ 2 * X ^ 2 := by nlinarith [sq_nonneg y]
    nlinarith
  have hpos : 0 < 1 + X ^ 2 := by positivity
  have h6 : 2 * y ^ 2 ≤ c * (1 + X ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    exact h1
  calc 2 * (G * y ^ 2) * p = G * (2 * y ^ 2) * p := by ring
    _ ≤ G * (c * (1 + X ^ 2)⁻¹) * p := by gcongr
    _ = c * G * ((1 + X ^ 2)⁻¹ * p) := by ring
    _ ≤ c * G * b := by gcongr

/-- The exponents of regime (ii): `2 (U y)² ‖v‖² ≤ (c U ‖v‖ (y t))²` when `c² t² ≥ 2`, with
`U = υ^{-(q-5)/2}`, `y = W^{-4θ}` and `t = W^θ`. -/
private lemma outputLower_crit_slack {c U y t l : ℝ} (h2 : 2 ≤ c ^ 2 * t ^ 2) :
    2 * (U * y) ^ 2 * l ^ 2 ≤ (c * U * l * (y * t)) ^ 2 := by
  have h0 : 0 ≤ U ^ 2 * l ^ 2 * y ^ 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left h2 h0
  calc 2 * (U * y) ^ 2 * l ^ 2 = (U ^ 2 * l ^ 2 * y ^ 2) * 2 := by ring
    _ ≤ (U ^ 2 * l ^ 2 * y ^ 2) * (c ^ 2 * t ^ 2) := h1
    _ = (c * U * l * (y * t)) ^ 2 := by ring

/-- Regime (i), (9.68) [us:eq:profile] at `j = q - 1` with (9.67) [su:eq:output-cutoff-scale]:
for prepared data in `PrepGoodWeak`, the event that `R_5, …, R_{q-2}` are regular and
`‖v_{q-1}‖² < 2 κ² ‖P v_4‖²` has probability at most `W^{-D}`. -/
theorem output_lower_weak (κ₀ α β ε Cp : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hα : 0 < α)
    (hαβ : α < β) (hβ : β < 1 / 2) (hε : 0 < ε) (hε1 : ε ≤ 1) (hCp : 0 < Cp) (D : ℝ)
    (hD : 0 < D) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ a ∈ Set.Icc α β, ∀ E : ℝ, |E| ≤ 2 - κ₀ →
      ∀ (R : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ),
        (R, v) ∈ PrepGoodWeak W ((W : ℝ) ^ (-a)) ε Cp →
        μ W (qWeak β ε) {ω | (∀ j, 5 ≤ j → j ≤ qWeak β ε - 2 →
            IsRegularState W ((W : ℝ) ^ (-a)) (chartR W ((W : ℝ) ^ (-a)) E (qWeak β ε) R ω j)) ∧
          ∑ i, ‖(chartProd W ((W : ℝ) ^ (-a)) E (qWeak β ε) R ω (qWeak β ε - 1) *ᵥ v) i‖ ^ 2 <
            2 * (levelsWeak W ((W : ℝ) ^ (-a)) α β ε 0).kOut ^ 2 *
              ∑ i, ‖(specProj ((((W : ℝ) ^ (-a)) ^ 2 : ℝ) • R)
                (Set.Icc (-(W : ℝ) ^ (ε / 800)) ((W : ℝ) ^ (ε / 800))) *ᵥ v) i‖ ^ 2} ≤
          ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  have hβ0 : 0 < β := by linarith
  have hq5 : 5 ≤ qWeak β ε := by unfold qWeak; omega
  have hh : 1 ≤ qWeak β ε - 5 := by
    have : qWeak β ε - 5 = ⌈25600 / ε * (40 + β)⌉₊ := by unfold qWeak; omega
    rw [this]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
  obtain ⟨g₀, hg₀, H1⟩ := buffer_lower_eta κ₀ 1 hκ₀ hκ₀' one_pos (qWeak β ε - 5) hh
  obtain ⟨c, hc, H2⟩ := H1 (1 - 2 * β) (by linarith)
  obtain ⟨W₁, hW₁⟩ := H2 D hD
  have ev1 : ∀ᶠ W : ℕ in Filter.atTop, (W : ℝ) ^ (-α) < g₀ :=
    ((tendsto_rpow_neg_atTop hα).comp tendsto_natCast_atTop_atTop).eventually
      (gt_mem_nhds hg₀)
  have ev2 : ∀ᶠ W : ℕ in Filter.atTop, 4 / c ≤ (W : ℝ) ^ (ε / 200) :=
    ((tendsto_rpow_atTop (by positivity : 0 < ε / 200)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  obtain ⟨W₂, hW₂⟩ := Filter.eventually_atTop.mp ev1
  obtain ⟨W₃, hW₃⟩ := Filter.eventually_atTop.mp ev2
  refine ⟨max W₁ (max W₂ (max W₃ 1)), ?_⟩
  intro W hW a ha E hE R v hRv
  have hW1' : W₁ ≤ W := (le_max_left _ _).trans hW
  have hW2' : W₂ ≤ W := ((le_max_left _ _).trans (le_max_right _ _)).trans hW
  have hW3' : W₃ ≤ W :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hW
  have hW1 : 1 ≤ W :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hW
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < W := by linarith
  obtain ⟨hαa, haβ⟩ := ha
  set g : ℝ := (W : ℝ) ^ (-a) with hg
  have hg0 : 0 < g := Real.rpow_pos_of_pos hWpos _
  have hgg₀ : g ≤ g₀ :=
    (Real.rpow_le_rpow_of_exponent_le hWr (by linarith)).trans (hW₂ W hW2').le
  have hg1 : g ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hWr (by linarith)
  have hg2 : g ^ 2 = (W : ℝ) ^ (-2 * a) := by
    rw [hg, ← Real.rpow_natCast, ← Real.rpow_mul hWpos.le]
    congr 1
    push_cast
    ring
  have hηlow : (W : ℝ) ^ (-1 + (1 - 2 * β)) ≤ g ^ 2 := by
    rw [hg2]
    exact Real.rpow_le_rpow_of_exponent_le hWr (by linarith)
  have hη1 : g ^ 2 ≤ 1 := by nlinarith
  by_cases hv : v = 0
  · subst hv
    refine le_trans (le_of_eq ?_) zero_le
    refine measure_mono_null ?_ (measure_empty (μ := μ W (qWeak β ε)))
    intro ω hω
    exfalso
    have := hω.2
    simp at this
  have hreg0 : IsRegularState W g R := hRv.1
  refine le_trans (outputLower_measure (W := W) (q := qWeak β ε) _ _ ?_)
    (hW₁ W hW1' g (g ^ 2) E R v hg0 hgg₀ le_rfl hηlow hη1 hE hreg0 hv)
  rintro ω ⟨hreg, hlt⟩
  refine ⟨outputLower_regular hq5 g E R hreg0 ω hreg, ?_⟩
  rw [outputLower_prod hq5 g E R ω] at hlt
  rw [outputLower_l2_sq]
  refine hlt.trans_le ?_
  set X : ℝ := (W : ℝ) ^ (ε / 800) with hX
  have hX1 : 1 ≤ X := Real.one_le_rpow hWr (by positivity)
  have hy : (W : ℝ) ^ (-(3 * ε / 800)) * X ^ 3 = 1 := by
    rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul hWpos.le, ← Real.rpow_add hWpos]
    have : -(3 * ε / 800) + ε / 800 * ((3 : ℕ) : ℝ) = 0 := by push_cast; ring
    rw [this, Real.rpow_zero]
  have h4 : 4 ≤ c * X ^ 4 := by
    have h := hW₃ W hW3'
    have e : X ^ 4 = (W : ℝ) ^ (ε / 200) := by
      rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul hWpos.le]
      congr 1
      push_cast
      ring
    rw [e]
    rwa [div_le_iff₀ hc, mul_comm] at h
  have hAH : (((g ^ 2 : ℝ) : ℂ) • R).IsHermitian := by
    have hk : IsSelfAdjoint ((g ^ 2 : ℝ) : ℂ) := by rw [isSelfAdjoint_iff]; simp
    exact hreg0.1.smul hk
  have hsm : ((g ^ 2 : ℝ) • R) = (((g ^ 2 : ℝ) : ℂ) • R) :=
    RCLike.real_smul_eq_coe_smul (K := ℂ) _ _
  rw [hsm]
  obtain ⟨hPH, hPP, -, -⟩ := specProj_spec hAH (Set.Icc (-X) X)
  have hAP := (norm_mul_specProj_le hAH (by linarith : 0 ≤ X) (subset_refl _) 0 le_rfl).1
  have hb := outputLower_b_lower hreg0.1 (g ^ 2) hPH.eq hPP hAP v
  have hk : (levelsWeak W g α β ε 0).kOut =
      ((g ^ (qWeak β ε - 5))⁻¹) * (W : ℝ) ^ (-(3 * ε / 800)) := rfl
  have hGη : ((g ^ (qWeak β ε - 5))⁻¹) ^ 2 = (g ^ 2) ^ (-((qWeak β ε - 5 : ℕ) : ℝ)) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, inv_pow, ← pow_mul, ← pow_mul,
      mul_comm]
  rw [hk, mul_pow, hGη]
  exact outputLower_weak_slack hc hX1 hy h4 (by positivity)
    (Finset.sum_nonneg fun i _ => sq_nonneg _) hb

/-- Regime (ii), Lemma G.3 [nc:lem:buffer] with (9.67) [su:eq:output-cutoff-scale]: for
prepared data in `PrepGoodCrit`, the event that `R_5, …, R_{q-2}` are regular and
`‖v_{q-1}‖² < 2 κ² ‖v_4‖²` has probability at most `W^{-D}`. -/
theorem output_lower_crit (κ₀ θ : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hθ : 0 < θ)
    (hθ' : θ ≤ 1 / 100) (D : ℝ) (hD : 0 < D) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, 0 < g → g ≤ (W : ℝ) ^ (-(1 / 2 : ℝ) + θ / 2) →
      ∀ E : ℝ, |E| ≤ 2 - κ₀ → ∀ (R : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ),
        (R, v) ∈ PrepGoodCrit W g θ →
        μ W (qCrit θ) {ω | (∀ j, 5 ≤ j → j ≤ qCrit θ - 2 →
            IsRegularState W g (chartR W g E (qCrit θ) R ω j)) ∧
          ∑ i, ‖(chartProd W g E (qCrit θ) R ω (qCrit θ - 1) *ᵥ v) i‖ ^ 2 <
            2 * (levelsCrit W θ 0).kOut ^ 2 * ∑ i, ‖v i‖ ^ 2} ≤
          ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  have hq5 : 5 ≤ qCrit θ := by unfold qCrit; omega
  have hh : 1 ≤ qCrit θ - 5 := by
    have : qCrit θ - 5 = ⌈10 / θ⌉₊ := by unfold qCrit; omega
    rw [this]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
  obtain ⟨c, hc, H⟩ := buffer_lower κ₀ θ hκ₀ hκ₀' hθ hθ' (qCrit θ - 5) hh
  obtain ⟨W₁, hW₁⟩ := H D hD
  have ev : ∀ᶠ W : ℕ in Filter.atTop, 2 / c ^ 2 ≤ (W : ℝ) ^ (2 * θ) :=
    ((tendsto_rpow_atTop (by positivity : 0 < 2 * θ)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  obtain ⟨W₂, hW₂⟩ := Filter.eventually_atTop.mp ev
  refine ⟨max W₁ (max W₂ 1), ?_⟩
  intro W hW g hg hgW E hE R v hRv
  have hW1' : W₁ ≤ W := (le_max_left _ _).trans hW
  have hW2' : W₂ ≤ W := ((le_max_left _ _).trans (le_max_right _ _)).trans hW
  have hW1 : 1 ≤ W := ((le_max_right _ _).trans (le_max_right _ _)).trans hW
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < W := by linarith
  by_cases hv : v = 0
  · subst hv
    refine le_trans (le_of_eq ?_) zero_le
    refine measure_mono_null ?_ (measure_empty (μ := μ W (qCrit θ)))
    intro ω hω
    exfalso
    have := hω.2
    simp at this
  have hgW' : g ≤ (W : ℝ) ^ (-1 / 2 + θ / 2) := by
    have e : (-1 / 2 + θ / 2 : ℝ) = -(1 / 2 : ℝ) + θ / 2 := by ring
    rw [e]
    exact hgW
  refine le_trans (outputLower_measure (W := W) (q := qCrit θ) _ _ ?_)
    (hW₁ W hW1' g E R v hg hgW' hE hRv.1 hRv.2.1 hv)
  rintro ω ⟨hreg, hlt⟩
  refine ⟨outputLower_regular hq5 g E R hRv.1 ω hreg, ?_⟩
  have hlt' : l2Norm (ricProd W g E (qCrit θ - 5) R (windowSample (actWin (qCrit θ)) ω)
      (qCrit θ - 5) *ᵥ v) ^ 2 < 2 * (levelsCrit W θ 0).kOut ^ 2 * l2Norm v ^ 2 := by
    rw [outputLower_l2_sq, outputLower_l2_sq, ← outputLower_prod hq5 g E R ω]
    exact hlt
  have hcast : (qCrit θ : ℝ) - 5 = ((qCrit θ - 5 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hq5]
    norm_num
  have hk : (levelsCrit W θ 0).kOut =
      (W : ℝ) ^ ((1 - 2 * θ) * ((qCrit θ - 5 : ℕ) : ℝ) / 2) * (W : ℝ) ^ (-(4 * θ)) := by
    change ((W : ℝ) ^ (-1 + 2 * θ)) ^ (-((qCrit θ : ℝ) - 5) / 2) * (W : ℝ) ^ (-(4 * θ)) = _
    rw [← Real.rpow_mul hWpos.le, hcast]
    congr 2
    ring
  have hy : (W : ℝ) ^ (-3 * θ) = (W : ℝ) ^ (-(4 * θ)) * (W : ℝ) ^ θ := by
    rw [← Real.rpow_add hWpos]
    congr 1
    ring
  have ht : (W : ℝ) ^ (2 * θ) = ((W : ℝ) ^ θ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hWpos.le]
    congr 1
    push_cast
    ring
  have h2 : 2 ≤ c ^ 2 * ((W : ℝ) ^ θ) ^ 2 := by
    have h := hW₂ W hW2'
    rw [div_le_iff₀ (by positivity), ht] at h
    linarith
  have hl : 0 ≤ l2Norm v := Real.sqrt_nonneg _
  refine lt_of_pow_lt_pow_left₀ 2 (by positivity) (hlt'.trans_le ?_)
  rw [hk, hy]
  exact outputLower_crit_slack h2

end LSBA
