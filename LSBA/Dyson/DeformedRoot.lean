import LSBA.Dyson.DeformedMap

/-!
# The Herglotz solution `m_B`

Existence and uniqueness of the Herglotz solution `m_B(z)` of `m = ⟨(−B − z − m)⁻¹⟩` for every
Hermitian `B` and `Im z > 0`, with `M_B = M_{m_B}`, and its continuity in `η` (Lemma A.21
[da:lem:deformed]).
-/

open scoped Matrix

noncomputable section
open scoped Classical

namespace LSBA

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Herglotz solution `m_B(z)` of Lemma A.21 [da:lem:deformed] (`0` if there is none). -/
def mB (B : Matrix ι ι ℂ) (z : ℂ) : ℂ :=
  if h : ∃ m, IsDeformedRoot B z m then h.choose else 0

/-- The deformed profile `M_B(z) = (-B - z - m_B(z))⁻¹` of Lemma A.21 [da:lem:deformed]. -/
def MB (B : Matrix ι ι ℂ) (z : ℂ) : Matrix ι ι ℂ := deformedMat B z (mB B z)

/-- The scalar Dyson function `w ↦ n⁻¹ ∑_k (c_k - w)⁻¹` for real numbers `c_k`. -/
private def deformedRoot_S (c : ι → ℝ) (w : ℂ) : ℂ :=
  (Fintype.card ι : ℂ)⁻¹ * ∑ k, ((c k : ℂ) - w)⁻¹

/-- The average `n⁻¹ ∑_k (c_k - w)⁻¹ (c_k - w')⁻¹`. -/
private def deformedRoot_P (c : ι → ℝ) (w w' : ℂ) : ℂ :=
  (Fintype.card ι : ℂ)⁻¹ * ∑ k, ((c k : ℂ) - w)⁻¹ * ((c k : ℂ) - w')⁻¹

/-- The average `n⁻¹ ∑_k |c_k - w|⁻²`. -/
private def deformedRoot_A (c : ι → ℝ) (w : ℂ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ k, ‖((c k : ℂ) - w)⁻¹‖ ^ 2

omit [Fintype ι] [DecidableEq ι] in
private lemma deformedRoot_ne (c : ι → ℝ) {w : ℂ} (hw : 0 < w.im) (k : ι) :
    (c k : ℂ) - w ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

omit [Fintype ι] [DecidableEq ι] in
private lemma deformedRoot_norm_inv_le (c : ι → ℝ) {w : ℂ} {t : ℝ} (ht : 0 < t) (hw : t ≤ w.im)
    (k : ι) : ‖((c k : ℂ) - w)⁻¹‖ ≤ t⁻¹ := by
  rw [norm_inv]
  apply inv_anti₀ ht
  have h := Complex.abs_im_le_norm ((c k : ℂ) - w)
  have h2 : ((c k : ℂ) - w).im = -w.im := by simp
  rw [h2, abs_neg, abs_of_pos (lt_of_lt_of_le ht hw)] at h
  linarith

omit [DecidableEq ι] in
private lemma deformedRoot_norm_avg_le [Nonempty ι] (f : ι → ℂ) {b : ℝ} (hb : ∀ k, ‖f k‖ ≤ b) :
    ‖(Fintype.card ι : ℂ)⁻¹ * ∑ k, f k‖ ≤ b := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (Fintype.card ι : ℝ)⁻¹ * ‖∑ k, f k‖ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ k, ‖f k‖ := by
        gcongr; exact norm_sum_le _ _
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ((Fintype.card ι : ℝ) * b) := by
        gcongr
        calc ∑ k, ‖f k‖ ≤ ∑ _k : ι, b := Finset.sum_le_sum fun k _ => hb k
          _ = (Fintype.card ι : ℝ) * b := by simp
    _ = b := by field_simp

omit [DecidableEq ι] in
/-- Resolvent identity `S(w) - S(w') = (w - w') ⟨(c - w)⁻¹ (c - w')⁻¹⟩` for `Im w, Im w' > 0`. -/
private lemma deformedRoot_S_sub (c : ι → ℝ) {w w' : ℂ} (hw : 0 < w.im) (hw' : 0 < w'.im) :
    deformedRoot_S c w - deformedRoot_S c w' = (w - w') * deformedRoot_P c w w' := by
  unfold deformedRoot_S deformedRoot_P
  have key : ∑ k, (((c k : ℂ) - w)⁻¹ - ((c k : ℂ) - w')⁻¹) =
      (w - w') * ∑ k, ((c k : ℂ) - w)⁻¹ * ((c k : ℂ) - w')⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 := deformedRoot_ne c hw k
    have h2 := deformedRoot_ne c hw' k
    rw [inv_sub_inv' h1 h2]
    ring
  rw [← mul_sub, ← Finset.sum_sub_distrib, key]
  ring

omit [DecidableEq ι] in
/-- Ward-type identity `Im S(w) = Im w · ⟨|c - w|⁻²⟩`. -/
private lemma deformedRoot_im_S (c : ι → ℝ) (w : ℂ) :
    (deformedRoot_S c w).im = w.im * deformedRoot_A c w := by
  unfold deformedRoot_S deformedRoot_A
  have hn : ((Fintype.card ι : ℂ)⁻¹) = (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) := by simp
  rw [hn, Complex.im_ofReal_mul, Complex.im_sum]
  have : ∀ k, (((c k : ℂ) - w)⁻¹).im = w.im * ‖((c k : ℂ) - w)⁻¹‖ ^ 2 := by
    intro k
    rw [Complex.inv_im, norm_inv, inv_pow, Complex.sq_norm]
    have h2 : ((c k : ℂ) - w).im = -w.im := by simp
    rw [h2]
    ring
  simp only [this, ← Finset.mul_sum]
  ring

omit [DecidableEq ι] in
private lemma deformedRoot_A_nonneg (c : ι → ℝ) (w : ℂ) : 0 ≤ deformedRoot_A c w := by
  unfold deformedRoot_A
  positivity

omit [DecidableEq ι] in
private lemma deformedRoot_A_pos [Nonempty ι] (c : ι → ℝ) {w : ℂ} (hw : 0 < w.im) :
    0 < deformedRoot_A c w := by
  unfold deformedRoot_A
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  refine mul_pos (inv_pos.mpr hn) (Finset.sum_pos (fun k _ => ?_) Finset.univ_nonempty)
  exact pow_pos (norm_pos_iff.mpr (inv_ne_zero (deformedRoot_ne c hw k))) 2

omit [DecidableEq ι] in
/-- Cauchy–Schwarz: `|⟨(c - w)⁻¹ (c - w')⁻¹⟩|² ≤ ⟨|c - w|⁻²⟩ ⟨|c - w'|⁻²⟩`. -/
private lemma deformedRoot_norm_P_sq_le (c : ι → ℝ) (w w' : ℂ) :
    ‖deformedRoot_P c w w'‖ ^ 2 ≤ deformedRoot_A c w * deformedRoot_A c w' := by
  unfold deformedRoot_P deformedRoot_A
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have h1 : ‖∑ k, ((c k : ℂ) - w)⁻¹ * ((c k : ℂ) - w')⁻¹‖ ≤
      ∑ k, ‖((c k : ℂ) - w)⁻¹‖ * ‖((c k : ℂ) - w')⁻¹‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => norm_mul _ _))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖((c k : ℂ) - w)⁻¹‖)
    (fun k => ‖((c k : ℂ) - w')⁻¹‖)
  have hn : (0 : ℝ) ≤ (Fintype.card ι : ℝ)⁻¹ := by positivity
  calc ((Fintype.card ι : ℝ)⁻¹ * ‖∑ k, ((c k : ℂ) - w)⁻¹ * ((c k : ℂ) - w')⁻¹‖) ^ 2
      = ((Fintype.card ι : ℝ)⁻¹) ^ 2 * ‖∑ k, ((c k : ℂ) - w)⁻¹ * ((c k : ℂ) - w')⁻¹‖ ^ 2 := by
        ring
    _ ≤ ((Fintype.card ι : ℝ)⁻¹) ^ 2 *
        (∑ k, ‖((c k : ℂ) - w)⁻¹‖ * ‖((c k : ℂ) - w')⁻¹‖) ^ 2 := by
        gcongr
    _ ≤ ((Fintype.card ι : ℝ)⁻¹) ^ 2 *
        ((∑ k, ‖((c k : ℂ) - w)⁻¹‖ ^ 2) * ∑ k, ‖((c k : ℂ) - w')⁻¹‖ ^ 2) := by
        gcongr
    _ = _ := by ring

omit [DecidableEq ι] in
/-- For a Herglotz root `m` with `Im m < 1`: `⟨|c - (z + m)|⁻²⟩ < (1 + Im z)⁻¹`. -/
private lemma deformedRoot_A_lt (c : ι → ℝ) {z m : ℂ} (hz : 0 < z.im) (hm : 0 < m.im)
    (hm1 : m.im < 1) (hfix : m = deformedRoot_S c (z + m)) :
    deformedRoot_A c (z + m) < (1 + z.im)⁻¹ := by
  have hw : 0 < (z + m).im := by rw [Complex.add_im]; linarith
  have h := deformedRoot_im_S c (z + m)
  rw [← hfix, Complex.add_im] at h
  rw [Complex.add_im] at hw
  have hA : deformedRoot_A c (z + m) = m.im / (z.im + m.im) := by
    rw [eq_div_iff hw.ne']; linarith
  rw [hA, div_lt_iff₀ hw, ← div_eq_inv_mul, lt_div_iff₀ (by linarith)]
  nlinarith

omit [DecidableEq ι] in
private lemma deformedRoot_norm_P_sub_le [Nonempty ι] (c : ι → ℝ) {w w' r : ℂ} {τ ε : ℝ}
    (hτ : 0 < τ) (hw : τ / 2 ≤ w.im) (hw' : τ / 2 ≤ w'.im) (hr : τ ≤ r.im)
    (hwr : ‖w - r‖ ≤ ε) (hw'r : ‖w' - r‖ ≤ ε) :
    ‖deformedRoot_P c w w' - deformedRoot_P c r r‖ ≤ 6 * ε / τ ^ 3 := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hwr
  have hτ2 : 0 < τ / 2 := by positivity
  have hrp : 0 < r.im := by linarith
  have hwp : 0 < w.im := by linarith
  have hw'p : 0 < w'.im := by linarith
  unfold deformedRoot_P
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  refine deformedRoot_norm_avg_le _ fun k => ?_
  set x := ((c k : ℂ) - w)⁻¹ with hx
  set x' := ((c k : ℂ) - w')⁻¹ with hx'
  set y := ((c k : ℂ) - r)⁻¹ with hy
  have hxn : ‖x‖ ≤ 2 / τ := by
    have := deformedRoot_norm_inv_le c hτ2 hw k
    rw [← hx] at this
    calc ‖x‖ ≤ (τ / 2)⁻¹ := this
      _ = 2 / τ := by field_simp
  have hx'n : ‖x'‖ ≤ 2 / τ := by
    have := deformedRoot_norm_inv_le c hτ2 hw' k
    rw [← hx'] at this
    calc ‖x'‖ ≤ (τ / 2)⁻¹ := this
      _ = 2 / τ := by field_simp
  have hyn : ‖y‖ ≤ 1 / τ := by
    have := deformedRoot_norm_inv_le c hτ hr k
    rw [← hy] at this
    calc ‖y‖ ≤ τ⁻¹ := this
      _ = 1 / τ := by rw [one_div]
  have hxy : x - y = (w - r) * (x * y) := by
    rw [hx, hy, inv_sub_inv' (deformedRoot_ne c hwp k) (deformedRoot_ne c hrp k)]
    ring
  have hx'y : x' - y = (w' - r) * (x' * y) := by
    rw [hx', hy, inv_sub_inv' (deformedRoot_ne c hw'p k) (deformedRoot_ne c hrp k)]
    ring
  have h1 : ‖x - y‖ ≤ ε * (2 / τ * (1 / τ)) := by
    rw [hxy, norm_mul, norm_mul]
    gcongr
  have h2 : ‖x' - y‖ ≤ ε * (2 / τ * (1 / τ)) := by
    rw [hx'y, norm_mul, norm_mul]
    gcongr
  have e : x * x' - y * y = (x - y) * x' + y * (x' - y) := by ring
  rw [e]
  calc ‖(x - y) * x' + y * (x' - y)‖ ≤ ‖x - y‖ * ‖x'‖ + ‖y‖ * ‖x' - y‖ :=
        (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
    _ ≤ ε * (2 / τ * (1 / τ)) * (2 / τ) + 1 / τ * (ε * (2 / τ * (1 / τ))) := by gcongr
    _ = 6 * ε / τ ^ 3 := by field_simp; ring

/-- Banach fixed-point theorem on a closed ball of `ℂ`. -/
private lemma deformedRoot_exists_fixedPoint_ball {f : ℂ → ℂ} {m₀ : ℂ} {ρ K : ℝ} (hρ : 0 ≤ ρ)
    (hK0 : 0 ≤ K) (hK : K < 1) (hmaps : ∀ q, ‖q - m₀‖ ≤ ρ → ‖f q - m₀‖ ≤ ρ)
    (hlip : ∀ q q', ‖q - m₀‖ ≤ ρ → ‖q' - m₀‖ ≤ ρ → ‖f q - f q'‖ ≤ K * ‖q - q'‖) :
    ∃ q, ‖q - m₀‖ ≤ ρ ∧ f q = q := by
  lift K to NNReal using hK0
  have hsf : Set.MapsTo f (Metric.closedBall m₀ ρ) (Metric.closedBall m₀ ρ) := by
    intro q hq
    rw [Metric.mem_closedBall, dist_eq_norm] at hq ⊢
    exact hmaps q hq
  have hc : ContractingWith K (hsf.restrict f (Metric.closedBall m₀ ρ)
      (Metric.closedBall m₀ ρ)) := by
    refine ⟨by rw [← NNReal.coe_lt_coe]; exact hK, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [Set.MapsTo.val_restrict_apply, Subtype.dist_eq, dist_eq_norm]
    have hx := x.2
    have hy := y.2
    rw [Metric.mem_closedBall, dist_eq_norm] at hx hy
    exact hlip x y hx hy
  obtain ⟨y, hy, hfy, -⟩ := hc.exists_fixedPoint' Metric.isClosed_closedBall.isComplete hsf
    (x := m₀) (Metric.mem_closedBall_self hρ) (edist_ne_top _ _)
  exact ⟨y, by simpa [dist_eq_norm] using hy, hfy⟩

omit [DecidableEq ι] in
private lemma deformedRoot_norm_S_le [Nonempty ι] (c : ι → ℝ) {w : ℂ} {t : ℝ} (ht : 0 < t)
    (hw : t ≤ w.im) : ‖deformedRoot_S c w‖ ≤ t⁻¹ :=
  deformedRoot_norm_avg_le _ fun k => deformedRoot_norm_inv_le c ht hw k

omit [DecidableEq ι] in
private lemma deformedRoot_norm_P_le [Nonempty ι] (c : ι → ℝ) {w w' : ℂ} {t t' : ℝ} (ht : 0 < t)
    (ht' : 0 < t') (hw : t ≤ w.im) (hw' : t' ≤ w'.im) :
    ‖deformedRoot_P c w w'‖ ≤ (t * t')⁻¹ := by
  refine deformedRoot_norm_avg_le _ fun k => ?_
  rw [norm_mul, mul_inv]
  exact mul_le_mul (deformedRoot_norm_inv_le c ht hw k) (deformedRoot_norm_inv_le c ht' hw' k)
    (norm_nonneg _) (by positivity)

omit [DecidableEq ι] in
/-- Existence of a Herglotz root of `m = S(z + m)` for `Im z ≥ 3`, by contraction on the unit
ball. -/
private lemma deformedRoot_exists_large [Nonempty ι] (c : ι → ℝ) {z : ℂ} (hz : 3 ≤ z.im) :
    ∃ m, 0 < m.im ∧ m = deformedRoot_S c (z + m) := by
  have hball : ∀ q : ℂ, ‖q - 0‖ ≤ 1 → 2 ≤ (z + q).im := by
    intro q hq
    have h1 := (abs_le.mp ((Complex.abs_im_le_norm q).trans (by simpa using hq))).1
    rw [Complex.add_im]
    linarith
  obtain ⟨q, hq, hfq⟩ := deformedRoot_exists_fixedPoint_ball
    (f := fun q => deformedRoot_S c (z + q)) (m₀ := 0) (ρ := 1) (K := 1 / 4) zero_le_one
    (by norm_num) (by norm_num)
    (fun q hq => by
      have := deformedRoot_norm_S_le c (t := 2) (by norm_num) (hball q hq)
      simp only [sub_zero]
      linarith [this])
    (fun q q' hq hq' => by
      have h := deformedRoot_S_sub c (w := z + q) (w' := z + q') (by linarith [hball q hq])
        (by linarith [hball q' hq'])
      have hP := deformedRoot_norm_P_le c (w := z + q) (w' := z + q') (t := 2) (t' := 2)
        (by norm_num) (by norm_num) (hball q hq) (hball q' hq')
      simp only [add_sub_add_left_eq_sub] at h
      rw [h, norm_mul, mul_comm]
      gcongr
      norm_num at hP ⊢
      linarith)
  refine ⟨q, ?_, hfq.symm⟩
  have h2 := hball q hq
  have h := deformedRoot_im_S c (z + q)
  have hfq' : deformedRoot_S c (z + q) = q := hfq
  rw [hfq'] at h
  rw [h]
  exact mul_pos (by linarith) (deformedRoot_A_pos c (by linarith))

omit [DecidableEq ι] in
/-- A Herglotz root at height `Im z₁` persists to heights `Im z₁ - δ`, `0 ≤ δ ≤ τ⁷/5832`, for
`τ ≤ min (Im z₁) 3`: contraction of the Newton-type map `q ↦ q - a (q - S(z + q))`,
`a = (1 - ⟨M²⟩)⁻¹`, on a ball around the root. -/
private lemma deformedRoot_cont [Nonempty ι] (c : ι → ℝ) {τ δ : ℝ} {z z₁ m₁ : ℂ}
    (hτ : 0 < τ) (hτ3 : τ ≤ 3) (hτz : τ ≤ z₁.im) (hδ0 : 0 ≤ δ) (hδ : δ ≤ τ ^ 7 / 5832)
    (hz : z = z₁ - (δ : ℂ) * Complex.I) (hm₁ : 0 < m₁.im) (hm₁1 : m₁.im < 1)
    (hfix : m₁ = deformedRoot_S c (z₁ + m₁)) :
    ∃ m, 0 < m.im ∧ m = deformedRoot_S c (z + m) := by
  have hτ3' : τ ^ 3 ≤ 27 := by
    calc τ ^ 3 ≤ 3 ^ 3 := pow_le_pow_left₀ hτ.le hτ3 3
      _ = 27 := by norm_num
  have hτ4 : 0 < τ ^ 4 := by positivity
  have hτ7 : τ ^ 7 = τ ^ 4 * τ ^ 3 := by ring
  -- radius `ρ` and step `s`
  set ρ : ℝ := τ ^ 4 / 216 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hsρ : τ ^ 7 / 5832 ≤ ρ := by
    rw [hρ, hτ7]; nlinarith
  have hsum : τ ^ 7 / 5832 + ρ ≤ τ / 2 := by
    have : τ ^ 4 ≤ 27 * τ := by nlinarith [mul_pos hτ hτ]
    nlinarith
  have hδρ : δ ≤ ρ := hδ.trans hsρ
  have hδτ : δ + ρ ≤ τ / 2 := by linarith
  have hz1 : 0 < z₁.im := lt_of_lt_of_le hτ hτz
  have hzim : z.im = z₁.im - δ := by rw [hz]; simp
  have hzz1 : ‖z - z₁‖ = δ := by
    rw [hz, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_real, Complex.norm_I,
      mul_one, Real.norm_of_nonneg hδ0]
  -- the linearization `a = (1 - ⟨M²⟩)⁻¹` at the root `m₁`
  set r : ℂ := z₁ + m₁ with hr
  have hrim : τ ≤ r.im := by rw [hr, Complex.add_im]; linarith
  set P₁ : ℂ := deformedRoot_P c r r with hP₁
  have hA : deformedRoot_A c r < (1 + z₁.im)⁻¹ := deformedRoot_A_lt c hz1 hm₁ hm₁1 hfix
  have hP₁A : ‖P₁‖ ≤ deformedRoot_A c r := by
    have h := deformedRoot_norm_P_sq_le c r r
    rw [← sq] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (deformedRoot_A_nonneg c r) two_ne_zero).mp h
  have hinv : (1 + z₁.im)⁻¹ = 1 - z₁.im / (1 + z₁.im) := by field_simp; ring
  have hτ4' : τ / 4 ≤ z₁.im / (1 + z₁.im) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  have h1P : τ / 4 ≤ ‖1 - P₁‖ := by
    have := norm_sub_norm_le (1 : ℂ) P₁
    rw [norm_one] at this
    linarith
  have h1P0 : (1 : ℂ) - P₁ ≠ 0 := by
    intro h
    rw [h, norm_zero] at h1P
    linarith
  set a : ℂ := (1 - P₁)⁻¹ with ha
  have ha1 : a * (1 - P₁) = 1 := inv_mul_cancel₀ h1P0
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_mul] at ha1
    exact zero_ne_one ha1
  have hanorm : ‖a‖ ≤ 4 / τ := by
    rw [ha, norm_inv, inv_le_comm₀ (lt_of_lt_of_le (by positivity) h1P) (by positivity)]
    calc (4 / τ)⁻¹ = τ / 4 := by field_simp
      _ ≤ ‖1 - P₁‖ := h1P
  -- geometry of the ball `‖q - m₁‖ ≤ ρ`
  have hball : ∀ q : ℂ, ‖q - m₁‖ ≤ ρ → τ / 2 ≤ (z + q).im ∧ ‖(z + q) - r‖ ≤ δ + ρ := by
    intro q hq
    refine ⟨?_, ?_⟩
    · have h1 := (abs_le.mp ((Complex.abs_im_le_norm (q - m₁)).trans hq)).1
      rw [Complex.sub_im] at h1
      rw [Complex.add_im, hzim]
      linarith
    · have e : (z + q) - r = (z - z₁) + (q - m₁) := by rw [hr]; ring
      rw [e]
      calc ‖(z - z₁) + (q - m₁)‖ ≤ ‖z - z₁‖ + ‖q - m₁‖ := norm_add_le _ _
        _ ≤ δ + ρ := by rw [hzz1]; linarith
  set T : ℂ → ℂ := fun q => q - a * (q - deformedRoot_S c (z + q)) with hT
  have hlip : ∀ q q', ‖q - m₁‖ ≤ ρ → ‖q' - m₁‖ ≤ ρ → ‖T q - T q'‖ ≤ (1 / 2) * ‖q - q'‖ := by
    intro q q' hq hq'
    obtain ⟨hw, hwr⟩ := hball q hq
    obtain ⟨hw', hw'r⟩ := hball q' hq'
    have hS := deformedRoot_S_sub c (w := z + q) (w' := z + q') (by linarith) (by linarith)
    simp only [add_sub_add_left_eq_sub] at hS
    have hdiff : T q - T q' = a * (q - q') * (deformedRoot_P c (z + q) (z + q') - P₁) := by
      simp only [hT]
      linear_combination (-(q - q')) * ha1 + a * hS
    have hPb := deformedRoot_norm_P_sub_le c (w := z + q) (w' := z + q') (r := r) (τ := τ)
      (ε := δ + ρ) hτ hw hw' hrim hwr hw'r
    rw [← hP₁] at hPb
    rw [hdiff, norm_mul, norm_mul]
    have hεb : 6 * (δ + ρ) / τ ^ 3 * (4 / τ) ≤ 1 / 2 := by
      rw [div_mul_div_comm, div_le_iff₀ (by positivity)]
      nlinarith
    calc ‖a‖ * ‖q - q'‖ * ‖deformedRoot_P c (z + q) (z + q') - P₁‖
        ≤ (4 / τ) * ‖q - q'‖ * (6 * (δ + ρ) / τ ^ 3) := by gcongr
      _ = (6 * (δ + ρ) / τ ^ 3 * (4 / τ)) * ‖q - q'‖ := by ring
      _ ≤ (1 / 2) * ‖q - q'‖ := by gcongr
  have hself : ‖T m₁ - m₁‖ ≤ ρ / 2 := by
    obtain ⟨hw, -⟩ := hball m₁ (by simp [hρ0.le])
    have hS := deformedRoot_S_sub c (w := z + m₁) (w' := r) (by linarith) (by linarith)
    have e : (z + m₁) - r = z - z₁ := by rw [hr]; ring
    rw [e] at hS
    have hPb := deformedRoot_norm_P_le c (w := z + m₁) (w' := r) (t := τ / 2) (t' := τ)
      (by positivity) hτ hw hrim
    have hTm : T m₁ - m₁ = a * (deformedRoot_S c (z + m₁) - deformedRoot_S c r) := by
      simp only [hT]
      rw [← hfix]
      ring
    rw [hTm, norm_mul, hS, norm_mul, hzz1]
    have hb : ‖a‖ * (δ * (τ / 2 * τ)⁻¹) ≤ ρ / 2 := by
      calc ‖a‖ * (δ * (τ / 2 * τ)⁻¹) ≤ (4 / τ) * (δ * (τ / 2 * τ)⁻¹) := by gcongr
        _ = 8 * δ / τ ^ 3 := by field_simp; ring
        _ ≤ ρ / 2 := by
          rw [div_le_iff₀ (by positivity), hρ]
          have h8 : 8 * δ ≤ 8 * (τ ^ 4 * τ ^ 3 / 5832) := by rw [← hτ7]; linarith
          nlinarith [mul_pos hτ4 (pow_pos hτ 3)]
    calc ‖a‖ * (δ * ‖deformedRoot_P c (z + m₁) r‖) ≤ ‖a‖ * (δ * (τ / 2 * τ)⁻¹) := by gcongr
      _ ≤ ρ / 2 := hb
  obtain ⟨q, hq, hfq⟩ := deformedRoot_exists_fixedPoint_ball (f := T) (m₀ := m₁) (ρ := ρ)
    (K := 1 / 2) hρ0.le (by norm_num) (by norm_num)
    (fun q hq => by
      have h1 := hlip q m₁ hq (by simp [hρ0.le])
      calc ‖T q - m₁‖ ≤ ‖T q - T m₁‖ + ‖T m₁ - m₁‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ρ := by linarith)
    hlip
  obtain ⟨hw, -⟩ := hball q hq
  have hfq' : q = deformedRoot_S c (z + q) := by
    have h : a * (q - deformedRoot_S c (z + q)) = 0 := by
      have : T q = q := hfq
      simp only [hT] at this
      linear_combination -this
    have := (mul_eq_zero.mp h).resolve_left ha0
    exact sub_eq_zero.mp this
  refine ⟨q, ?_, hfq'⟩
  have h := deformedRoot_im_S c (z + q)
  rw [← hfq'] at h
  rw [h]
  exact mul_pos (by linarith) (deformedRoot_A_pos c (by linarith))

/-- The normalized trace of the resolvent is `n⁻¹ ∑_k (λ_k - w)⁻¹`. -/
private lemma deformedRoot_ntr_resolventMat {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {w : ℂ}
    (hw : w.im ≠ 0) :
    ntr (resolventMat A w) = deformedRoot_S (fun k => hA.eigenvalues k) w := by
  have hnorm : ∀ k, ∑ x, hA.eigenvectorBasis k x * star (hA.eigenvectorBasis k x) = 1 := by
    intro k
    have h1 := (hA.eigenvectorBasis).norm_eq_one k
    have h2 := EuclideanSpace.norm_sq_eq (hA.eigenvectorBasis k)
    rw [h1, one_pow] at h2
    have h3 : ∀ x, hA.eigenvectorBasis k x * star (hA.eigenvectorBasis k x) =
        ((‖hA.eigenvectorBasis k x‖ ^ 2 : ℝ) : ℂ) := fun x => by
      rw [mul_comm, Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
    simp only [h3]
    rw [← Complex.ofReal_sum]
    exact_mod_cast h2.symm
  have htr : (resolventMat A w).trace = ∑ k, (((hA.eigenvalues k : ℝ) : ℂ) - w)⁻¹ := by
    simp only [Matrix.trace, Matrix.diag, resolventMat_apply hA hw]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, hnorm k, one_mul]
  unfold ntr deformedRoot_S
  rw [htr]

/-- `IsDeformedRoot` in terms of the eigenvalues of `-B`. -/
private lemma deformedRoot_iff {B : Matrix ι ι ℂ} (hB : B.IsHermitian) {z m : ℂ}
    (hz : 0 < z.im) :
    IsDeformedRoot B z m ↔
      0 < m.im ∧ m = deformedRoot_S (fun k => hB.neg.eigenvalues k) (z + m) := by
  unfold IsDeformedRoot
  refine and_congr_right fun hm => ?_
  have hw : (z + m).im ≠ 0 := by rw [Complex.add_im]; linarith
  have : deformedMap B z m = deformedRoot_S (fun k => hB.neg.eigenvalues k) (z + m) :=
    deformedRoot_ntr_resolventMat hB.neg hw
  rw [this]

/-- Roots exist at every height `η₀ ≤ η ≤ 3`, by induction on the number of steps of size
`η₀⁷/5832` down from `3`. -/
private lemma deformedRoot_exists_aux [Nonempty ι] {B : Matrix ι ι ℂ} (hB : B.IsHermitian) (E : ℝ)
    {η₀ : ℝ} (hη₀ : 0 < η₀) (hη₀3 : η₀ ≤ 3) :
    ∀ k : ℕ, ∀ η : ℝ, η₀ ≤ η → η ≤ 3 → 3 - η ≤ k * (η₀ ^ 7 / 5832) →
      ∃ m, IsDeformedRoot B (E + η * Complex.I) m := by
  have hσ : 0 < η₀ ^ 7 / 5832 := by positivity
  intro k
  induction k with
  | zero =>
    intro η h1 h2 h3
    have hη : η = 3 := by simp at h3; linarith
    subst hη
    have hz : 0 < ((E : ℂ) + (3 : ℝ) * Complex.I).im := by simp
    obtain ⟨m, hm⟩ := deformedRoot_exists_large (fun k => hB.neg.eigenvalues k)
      (z := (E : ℂ) + (3 : ℝ) * Complex.I) (by simp)
    exact ⟨m, (deformedRoot_iff hB hz).mpr hm⟩
  | succ k ih =>
    intro η h1 h2 h3
    set σ : ℝ := η₀ ^ 7 / 5832 with hσdef
    set η₁ : ℝ := min 3 (η + σ) with hη₁
    have hη₁a : η ≤ η₁ := le_min h2 (by linarith)
    have hη₁b : η₁ ≤ η + σ := min_le_right _ _
    have hη₁c : η₁ ≤ 3 := min_le_left _ _
    have hη₁d : 3 - η₁ ≤ k * σ := by
      rcases le_total 3 (η + σ) with h | h
      · rw [hη₁, min_eq_left h]; have : 0 ≤ (k : ℝ) * σ := by positivity
        linarith
      · rw [hη₁, min_eq_right h]; push_cast at h3; linarith
    obtain ⟨m₁, hm₁⟩ := ih η₁ (h1.trans hη₁a) hη₁c hη₁d
    have hz₁ : 0 < ((E : ℂ) + η₁ * Complex.I).im := by simp; linarith
    have hnorm := IsDeformedRoot.norm_lt_one hB hz₁ hm₁
    have him1 : m₁.im < 1 := lt_of_le_of_lt (abs_le.mp ((Complex.abs_im_le_norm m₁).trans le_rfl)).2
      hnorm
    obtain ⟨hm₁im, hm₁fix⟩ := (deformedRoot_iff hB hz₁).mp hm₁
    have hz : 0 < ((E : ℂ) + η * Complex.I).im := by simp; linarith
    obtain ⟨m, hm⟩ := deformedRoot_cont (fun k => hB.neg.eigenvalues k) (τ := η₀)
      (δ := η₁ - η) (z := (E : ℂ) + η * Complex.I) (z₁ := (E : ℂ) + η₁ * Complex.I)
      (m₁ := m₁) hη₀ hη₀3 (by simpa using h1.trans hη₁a) (by linarith) (by linarith)
      (by push_cast; ring) hm₁im him1 hm₁fix
    exact ⟨m, (deformedRoot_iff hB hz).mpr hm⟩

/-- Existence of the Herglotz solution of Lemma A.21 [da:lem:deformed]. -/
private lemma deformedRoot_exists [Nonempty ι] {B : Matrix ι ι ℂ} (hB : B.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) : ∃ m, IsDeformedRoot B z m := by
  have hz' : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := (Complex.re_add_im z).symm
  rw [hz']
  rcases le_or_gt 3 z.im with h3 | h3
  · have hz2 : 0 < (((z.re : ℂ) + (z.im : ℂ) * Complex.I)).im := by simpa using hz
    obtain ⟨m, hm⟩ := deformedRoot_exists_large (fun k => hB.neg.eigenvalues k)
      (z := (z.re : ℂ) + (z.im : ℂ) * Complex.I) (by simpa using h3)
    exact ⟨m, (deformedRoot_iff hB hz2).mpr hm⟩
  · obtain ⟨k, hk⟩ := exists_nat_ge (3 / (z.im ^ 7 / 5832))
    have hσ : 0 < z.im ^ 7 / 5832 := by positivity
    refine deformedRoot_exists_aux hB z.re hz h3.le k z.im le_rfl h3.le ?_
    rw [div_le_iff₀ hσ] at hk
    linarith

/-- Existence and uniqueness of the Herglotz solution of Lemma A.21 [da:lem:deformed], for every
Hermitian `B` and every `Im z > 0`. -/
theorem existsUnique_isDeformedRoot [Nonempty ι] {B : Matrix ι ι ℂ} (hB : B.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) : ∃! m, IsDeformedRoot B z m := by
  obtain ⟨m, hm⟩ := deformedRoot_exists hB hz
  exact ⟨m, hm, fun m' hm' => IsDeformedRoot.unique hB hz hm' hm⟩

/-- `m_B(z)` is the Herglotz solution of Lemma A.21 [da:lem:deformed]. -/
theorem isDeformedRoot_mB [Nonempty ι] {B : Matrix ι ι ℂ} (hB : B.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) : IsDeformedRoot B z (mB B z) := by
  have h : ∃ m, IsDeformedRoot B z m := (existsUnique_isDeformedRoot hB hz).exists
  unfold mB
  simp only [h, ↓reduceDIte]
  exact h.choose_spec

/-- Lipschitz continuity of `η ↦ m_B(E + iη)`, used in the continuity argument of the proof of
Lemma A.22 [da:lem:deformed-stability]. -/
theorem norm_mB_sub_mB_le [Nonempty ι] {B : Matrix ι ι ℂ} (hB : B.IsHermitian) (E : ℝ)
    {η η' : ℝ} (hη : 0 < η) (hη' : 0 < η') :
    ‖mB B (E + η * Complex.I) - mB B (E + η' * Complex.I)‖ ≤ |η - η'| / min η η' := by
  set z : ℂ := E + η * Complex.I with hzdef
  set z' : ℂ := E + η' * Complex.I with hz'def
  have hzim : z.im = η := by simp [hzdef]
  have hz'im : z'.im = η' := by simp [hz'def]
  have hz : 0 < z.im := by rw [hzim]; exact hη
  have hz' : 0 < z'.im := by rw [hz'im]; exact hη'
  have hm := isDeformedRoot_mB hB hz
  have hm' := isDeformedRoot_mB hB hz'
  set m := mB B z with hmdef
  set m' := mB B z' with hm'def
  have him1 : m.im < 1 :=
    lt_of_le_of_lt (abs_le.mp (Complex.abs_im_le_norm m)).2 (IsDeformedRoot.norm_lt_one hB hz hm)
  have him1' : m'.im < 1 :=
    lt_of_le_of_lt (abs_le.mp (Complex.abs_im_le_norm m')).2 (IsDeformedRoot.norm_lt_one hB hz' hm')
  obtain ⟨hmim, hmfix⟩ := (deformedRoot_iff hB hz).mp hm
  obtain ⟨hmim', hmfix'⟩ := (deformedRoot_iff hB hz').mp hm'
  set c : ι → ℝ := fun k => hB.neg.eigenvalues k with hc
  have hwim : 0 < (z + m).im := by rw [Complex.add_im]; linarith
  have hwim' : 0 < (z' + m').im := by rw [Complex.add_im]; linarith
  have hS := deformedRoot_S_sub c hwim hwim'
  rw [← hmfix, ← hmfix'] at hS
  set P := deformedRoot_P c (z + m) (z' + m') with hP
  have hzz' : z - z' = ((η - η' : ℝ) : ℂ) * Complex.I := by
    simp only [hzdef, hz'def]; push_cast; ring
  have key : (m - m') * (1 - P) = ((η - η' : ℝ) : ℂ) * Complex.I * P := by
    have e : (z + m) - (z' + m') = ((η - η' : ℝ) : ℂ) * Complex.I + (m - m') := by
      rw [← hzz']; ring
    rw [e] at hS
    linear_combination hS
  set μ : ℝ := min η η' with hμdef
  have hμ : 0 < μ := lt_min hη hη'
  have hA := deformedRoot_A_lt c hz hmim him1 hmfix
  have hA' := deformedRoot_A_lt c hz' hmim' him1' hmfix'
  have hA1 : deformedRoot_A c (z + m) ≤ (1 + μ)⁻¹ := by
    refine hA.le.trans ?_
    rw [hzim]
    exact inv_anti₀ (by linarith) (by linarith [min_le_left η η'])
  have hA1' : deformedRoot_A c (z' + m') ≤ (1 + μ)⁻¹ := by
    refine hA'.le.trans ?_
    rw [hz'im]
    exact inv_anti₀ (by linarith) (by linarith [min_le_right η η'])
  have hPb : ‖P‖ ≤ (1 + μ)⁻¹ := by
    have h := deformedRoot_norm_P_sq_le c (z + m) (z' + m')
    have h2 : deformedRoot_A c (z + m) * deformedRoot_A c (z' + m') ≤ ((1 + μ)⁻¹) ^ 2 := by
      rw [sq]
      exact mul_le_mul hA1 hA1' (deformedRoot_A_nonneg c _) (by positivity)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp (h.trans h2)
  have h1P : μ / (1 + μ) ≤ ‖1 - P‖ := by
    have h := norm_sub_norm_le (1 : ℂ) P
    rw [norm_one] at h
    have e : 1 - (1 + μ)⁻¹ = μ / (1 + μ) := by field_simp; ring
    linarith
  have hn : ‖m - m'‖ * ‖1 - P‖ = |η - η'| * ‖P‖ := by
    rw [← norm_mul, key, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
  have h2 : ‖m - m'‖ * (μ / (1 + μ)) ≤ |η - η'| * (1 + μ)⁻¹ := by
    calc ‖m - m'‖ * (μ / (1 + μ)) ≤ ‖m - m'‖ * ‖1 - P‖ := by gcongr
      _ = |η - η'| * ‖P‖ := hn
      _ ≤ |η - η'| * (1 + μ)⁻¹ := by gcongr
  have h1μ : 0 < 1 + μ := by linarith
  have e1 : (1 + μ) * (‖m - m'‖ * (μ / (1 + μ))) = ‖m - m'‖ * μ := by field_simp
  have e2 : (1 + μ) * (|η - η'| * (1 + μ)⁻¹) = |η - η'| := by field_simp
  have h3 := mul_le_mul_of_nonneg_left h2 h1μ.le
  rw [e1, e2] at h3
  exact (le_div_iff₀ hμ).mpr h3

end LSBA
