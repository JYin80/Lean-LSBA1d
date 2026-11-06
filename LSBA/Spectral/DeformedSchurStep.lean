import LSBA.Spectral.SchurBounds
import LSBA.Dyson.DeformedStability
import LSBA.Spectral.SchurEvents

/-!
# The single-height step

A deterministic step of the proof of Lemma G.1 [us:lem:local-law]: on the good events, `|⟨G⟩ −
m_B| ≤ Ct/√(nη)` and `|G_ii − M_ii| ≤ Ct/√(nη)|M_ii|²` (Appendix G.1
[app:relative-local-law-proof]).
-/

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section
open scoped Classical

namespace LSBA

/-- Perturbation of an inverse: `‖(a + δ)⁻¹ - a⁻¹‖ ≤ 2 ‖δ‖ ‖a⁻¹‖²` when `‖δ‖ ≤ ‖a‖ / 2`. -/
private lemma deformedSchurStep_inv_sub {a δ : ℂ} (ha : a ≠ 0) (hδ : ‖δ‖ ≤ ‖a‖ / 2) :
    a + δ ≠ 0 ∧ ‖(a + δ)⁻¹ - a⁻¹‖ ≤ 2 * ‖δ‖ * ‖a⁻¹‖ ^ 2 := by
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have h1 : ‖a‖ / 2 ≤ ‖a + δ‖ := by
    have := norm_sub_norm_le a (-δ)
    rw [sub_neg_eq_add, norm_neg] at this
    linarith
  have hne : a + δ ≠ 0 := norm_pos_iff.mp (by linarith)
  refine ⟨hne, ?_⟩
  have hid : (a + δ)⁻¹ - a⁻¹ = -(δ * ((a + δ)⁻¹ * a⁻¹)) := by
    field_simp
    ring
  rw [hid, norm_neg, norm_mul, norm_mul, norm_inv, norm_inv]
  have h2 : ‖a + δ‖⁻¹ ≤ 2 / ‖a‖ := by
    rw [inv_eq_one_div]
    rw [div_le_div_iff₀ (by linarith) hna]
    linarith
  have h3 : ‖δ‖ * (‖a + δ‖⁻¹ * ‖a‖⁻¹) ≤ ‖δ‖ * (2 / ‖a‖ * ‖a‖⁻¹) := by
    gcongr
  calc ‖δ‖ * (‖a + δ‖⁻¹ * ‖a‖⁻¹) ≤ ‖δ‖ * (2 / ‖a‖ * ‖a‖⁻¹) := h3
    _ = 2 * ‖δ‖ * ‖a‖⁻¹ ^ 2 := by field_simp

/-- `a⁻¹ - b⁻¹ = (b - a) a⁻¹ b⁻¹`, so `‖a⁻¹ - b⁻¹‖ ≤ ‖b - a‖ ‖a⁻¹‖ ‖b⁻¹‖`, and `‖a⁻¹‖ ≤ 2 ‖b⁻¹‖`
when `‖b - a‖ ‖a⁻¹‖ ≤ 1`. -/
private lemma deformedSchurStep_ratio {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ‖b - a‖ * ‖a⁻¹‖ ≤ 1) :
    ‖a⁻¹ - b⁻¹‖ ≤ ‖b - a‖ * ‖a⁻¹‖ * ‖b⁻¹‖ ∧ ‖a⁻¹‖ ≤ 2 * ‖b⁻¹‖ := by
  have hid : a⁻¹ - b⁻¹ = (b - a) * (a⁻¹ * b⁻¹) := by
    field_simp
  have h1 : ‖a⁻¹ - b⁻¹‖ = ‖b - a‖ * ‖a⁻¹‖ * ‖b⁻¹‖ := by
    rw [hid, norm_mul, norm_mul]; ring
  refine ⟨h1.le, ?_⟩
  have h2 : ‖a⁻¹‖ ≤ ‖b⁻¹‖ + ‖a⁻¹ - b⁻¹‖ := by
    calc ‖a⁻¹‖ = ‖b⁻¹ + (a⁻¹ - b⁻¹)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  have h3 : ‖a⁻¹ - b⁻¹‖ ≤ ‖b⁻¹‖ := by
    rw [h1]
    calc ‖b - a‖ * ‖a⁻¹‖ * ‖b⁻¹‖ ≤ 1 * ‖b⁻¹‖ := by gcongr
      _ = ‖b⁻¹‖ := one_mul _
  linarith


/-- For diagonal Hermitian `B` and `Im (z + q) > 0`, the trial profile has diagonal entries
`(-B_ii - z - q)⁻¹`. -/
private lemma deformedSchurStep_deformedMat_diag {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ}
    (hB : B.IsDiag) (hBh : B.IsHermitian) {z q : ℂ} (hw : 0 < (z + q).im) (i : Fin n) :
    deformedMat B z q i i = (-B i i - (z + q))⁻¹ := by
  unfold deformedMat resolventMat
  have h : -B - (z + q) • (1 : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.diagonal (fun k => -B k k - (z + q)) := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp
    · simp [Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab, hB hab]
  have hne : ∀ k, -B k k - (z + q) ≠ 0 := by
    intro k hk
    have := congrArg Complex.im hk
    have h0 : (B k k).im = 0 := by
      have h1 := hBh.apply k k
      rw [Complex.star_def] at h1
      exact Complex.conj_eq_iff_im.mp h1
    simp [h0] at this
    rw [Complex.add_im] at hw
    linarith
  rw [h, Matrix.inv_eq_right_inv (B := Matrix.diagonal (fun k => (-B k k - (z + q))⁻¹))]
  · simp
  · rw [Matrix.diagonal_mul_diagonal]
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hne a]
    · simp [Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab]

/-- The diagonal entries of a Hermitian matrix are real. -/
private lemma deformedSchurStep_im_diag {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ}
    (hB : B.IsHermitian) (i : Fin n) : (B i i).im = 0 := by
  have := hB.apply i i
  rw [Complex.star_def] at this
  exact Complex.conj_eq_iff_im.mp this

/-- `‖a⁻¹‖ ≤ ρ⁻¹` when `Im a ≤ -ρ < 0`. -/
private lemma deformedSchurStep_norm_inv_le {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (h : ρ ≤ -a.im) :
    ‖a⁻¹‖ ≤ ρ⁻¹ := by
  rw [norm_inv]
  apply inv_anti₀ hρ
  have h1 := Complex.abs_im_le_norm a
  rw [abs_of_nonpos (by linarith)] at h1
  linarith

/-- `Im ⟨X⟩ = n⁻¹ Im Tr X`. -/
private lemma deformedSchurStep_im_ntr {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    (ntr X).im = (n : ℝ)⁻¹ * X.trace.im := by
  have : ntr X = (((n : ℝ)⁻¹ : ℝ) : ℂ) * X.trace := by simp [ntr]
  rw [this, Complex.im_ofReal_mul]

/-- A uniform bound on the diagonal entries bounds the normalized trace. -/
private lemma deformedSchurStep_norm_ntr_le {n : ℕ} (hn : 0 < n) {X : Matrix (Fin n) (Fin n) ℂ}
    {b : ℝ} (h : ∀ i, ‖X i i‖ ≤ b) : ‖ntr X‖ ≤ b := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnn : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold ntr
  rw [norm_mul, norm_inv, Fintype.card_fin, Complex.norm_natCast]
  have h1 : ‖X.trace‖ ≤ n * b := by
    calc ‖X.trace‖ ≤ ∑ i, ‖X i i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin n, b := Finset.sum_le_sum fun i _ => h i
      _ = n * b := by simp
  calc (n : ℝ)⁻¹ * ‖X.trace‖ ≤ (n : ℝ)⁻¹ * (n * b) := by gcongr
    _ = b := by field_simp

/-- Ward's identity summed: the Hilbert–Schmidt norm of a resolvent is `Im Tr G / η`. -/
private lemma deformedSchurStep_hs {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (E : ℝ) {η : ℝ} (hη : 0 < η) :
    ∑ k, ∑ l, ‖resolventMat A (E + η * Complex.I) k l‖ ^ 2 =
      (resolventMat A (E + η * Complex.I)).trace.im / η := by
  simp only [ward hA E hη.ne', Matrix.trace, Matrix.diag_apply, Complex.im_sum, Finset.sum_div]

/-- `Im Tr G ≥ 0`. -/
private lemma deformedSchurStep_im_trace_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (E : ℝ) {η : ℝ} (hη : 0 < η) :
    0 ≤ (resolventMat A (E + η * Complex.I)).trace.im := by
  have h := deformedSchurStep_hs hA E hη
  have h0 : 0 ≤ ∑ k, ∑ l, ‖resolventMat A (E + η * Complex.I) k l‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [h] at h0
  exact (div_nonneg_iff.mp h0).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hη))

/-- Schur's formula in the form `G_ii = (-b_i - z - ⟨G⟩ + δ_i)⁻¹`, with the bound on `δ_i`. -/
private lemma deformedSchurStep_schur {n : ℕ} {V B : Matrix (Fin n) (Fin n) ℂ}
    (hV : V.IsHermitian) (hB : B.IsHermitian) {z : ℂ} (hz : 0 < z.im) (i : Fin n) :
    ∃ δ : ℂ, resolventMat (V - B) z i i =
        (-B i i - (z + ntr (resolventMat (V - B) z)) + δ)⁻¹ ∧
      ‖δ‖ ≤ ‖V i i‖ + ‖schurQuadDev (V - B) z i‖ + (n : ℝ)⁻¹ * z.im⁻¹ := by
  have hH : (V - B).IsHermitian := hV.sub hB
  refine ⟨V i i - schurQuadDev (V - B) z i + (n : ℂ)⁻¹ *
    ((resolventMat (V - B) z).trace - (resolventMat (minorMat (V - B) i) z).trace), ?_, ?_⟩
  · rw [resolventMat_diag_schur hH hz i]
    congr 1
    simp only [schurQuadDev, ntr, Fintype.card_fin, Matrix.sub_apply]
    ring
  · have h1 := norm_trace_resolventMat_sub_minor_le hH hz i
    have h2 : ‖(n : ℂ)⁻¹ * ((resolventMat (V - B) z).trace -
        (resolventMat (minorMat (V - B) i) z).trace)‖ ≤ (n : ℝ)⁻¹ * z.im⁻¹ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      gcongr
    calc _ ≤ ‖V i i - schurQuadDev (V - B) z i‖ + ‖(n : ℂ)⁻¹ *
          ((resolventMat (V - B) z).trace - (resolventMat (minorMat (V - B) i) z).trace)‖ :=
          norm_add_le _ _
      _ ≤ ‖V i i‖ + ‖schurQuadDev (V - B) z i‖ + (n : ℝ)⁻¹ * z.im⁻¹ := by
          have := norm_sub_le (V i i) (schurQuadDev (V - B) z i)
          linarith


/-- `(t/n) √H ≤ √(Y+1) · t/√(nη)` when `H ≤ (nY + η⁻¹)/η` and `nη ≥ 1`. -/
private lemma deformedSchurStep_real {n t η Y H : ℝ} (hn : 0 < n) (hη : 0 < η)
    (hnη : 1 ≤ n * η) (ht : 0 ≤ t) (hY : 0 ≤ Y) (hH : H ≤ (n * Y + η⁻¹) / η) :
    t / n * Real.sqrt H ≤ Real.sqrt (Y + 1) * (t / Real.sqrt (n * η)) := by
  have hnη0 : 0 < n * η := mul_pos hn hη
  calc t / n * Real.sqrt H ≤ t / n * Real.sqrt ((n * Y + η⁻¹) / η) := by
        gcongr
    _ = Real.sqrt ((t / n) ^ 2 * ((n * Y + η⁻¹) / η)) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    _ ≤ Real.sqrt ((Y + 1) * (t / Real.sqrt (n * η)) ^ 2) := by
        apply Real.sqrt_le_sqrt
        have e2 : (t / Real.sqrt (n * η)) ^ 2 = t ^ 2 / (n * η) := by
          rw [div_pow, Real.sq_sqrt hnη0.le]
        rw [e2]
        have e : (t / n) ^ 2 * ((n * Y + η⁻¹) / η) = t ^ 2 / (n * η) * (Y + 1 / (n * η)) := by
          field_simp
        rw [e]
        have h1 : 1 / (n * η) ≤ 1 := by rw [div_le_one hnη0]; exact hnη
        have h2 : 0 ≤ t ^ 2 / (n * η) := by positivity
        calc t ^ 2 / (n * η) * (Y + 1 / (n * η)) ≤ t ^ 2 / (n * η) * (Y + 1) := by gcongr
          _ = (Y + 1) * (t ^ 2 / (n * η)) := by ring
    _ = Real.sqrt (Y + 1) * (t / Real.sqrt (n * η)) := by
        rw [Real.sqrt_mul (by linarith), Real.sqrt_sq (by positivity)]

/-- The three terms of `δ_i` are at most `(√(C*+3) + √(Y+1) + 1) t/√(nη)`. -/
private lemma deformedSchurStep_delta_le {n : ℕ} (hn : 0 < n) {V B : Matrix (Fin n) (Fin n) ℂ}
    (hV : V.IsHermitian) (hB : B.IsHermitian) {Cstar Y E η t : ℝ} (hη : 0 < η)
    (hηC : η ≤ Cstar + 3) (hnη : 1 ≤ (n : ℝ) * η) (ht : 1 ≤ t)
    (hVd : ∀ i, ‖V i i‖ ≤ t / Real.sqrt n)
    (hQ : ∀ i, ‖schurQuadDev (V - B) (E + η * Complex.I) i‖ ≤
      t / n * Real.sqrt (∑ k, ∑ l,
        ‖resolventMat (minorMat (V - B) i) (E + η * Complex.I) k l‖ ^ 2))
    (hY : (ntr (resolventMat (V - B) (E + η * Complex.I))).im ≤ Y) (i : Fin n) :
    ‖V i i‖ + ‖schurQuadDev (V - B) (E + η * Complex.I) i‖ +
        (n : ℝ)⁻¹ * (E + η * Complex.I).im⁻¹ ≤
      (Real.sqrt (Cstar + 3) + Real.sqrt (Y + 1) + 1) * (t / Real.sqrt (n * η)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hH : (V - B).IsHermitian := hV.sub hB
  have hzim : (E + η * Complex.I).im = η := by simp
  have hz : 0 < (E + η * Complex.I).im := by rw [hzim]; exact hη
  have hnη0 : 0 < (n : ℝ) * η := mul_pos hn' hη
  set s : ℝ := t / Real.sqrt (n * η) with hs
  have hs0 : 0 ≤ s := by positivity
  -- the diagonal entry
  have h1 : ‖V i i‖ ≤ Real.sqrt (Cstar + 3) * s := by
    refine (hVd i).trans ?_
    have e : t / Real.sqrt n = Real.sqrt η * s := by
      rw [hs, Real.sqrt_mul hn'.le η]
      have : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn').ne'
      have : Real.sqrt η ≠ 0 := (Real.sqrt_pos.mpr hη).ne'
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hηC) hs0
  -- the quadratic form
  have hY0 : 0 ≤ Y := le_trans (by
    rw [deformedSchurStep_im_ntr]
    have := deformedSchurStep_im_trace_nonneg hH E hη
    positivity) hY
  have h2 : ‖schurQuadDev (V - B) (E + η * Complex.I) i‖ ≤ Real.sqrt (Y + 1) * s := by
    refine (hQ i).trans ?_
    have hM : (minorMat (V - B) i).IsHermitian := hH.submatrix _
    have hhs := deformedSchurStep_hs hM E hη
    have htr := norm_trace_resolventMat_sub_minor_le hH hz i
    rw [hzim] at htr
    have him : (resolventMat (minorMat (V - B) i) (E + η * Complex.I)).trace.im -
        (resolventMat (V - B) (E + η * Complex.I)).trace.im ≤ η⁻¹ := by
      have h := Complex.abs_im_le_norm ((resolventMat (V - B) (E + η * Complex.I)).trace -
        (resolventMat (minorMat (V - B) i) (E + η * Complex.I)).trace)
      rw [Complex.sub_im] at h
      have h' := neg_le_abs ((resolventMat (V - B) (E + η * Complex.I)).trace.im -
        (resolventMat (minorMat (V - B) i) (E + η * Complex.I)).trace.im)
      rw [neg_sub] at h'
      exact h'.trans (h.trans htr)
    have hq : (resolventMat (V - B) (E + η * Complex.I)).trace.im ≤ n * Y := by
      have h := hY
      rw [deformedSchurStep_im_ntr] at h
      have := mul_le_mul_of_nonneg_left h hn'.le
      rwa [← mul_assoc, mul_inv_cancel₀ hn'.ne', one_mul] at this
    refine deformedSchurStep_real hn' hη hnη (by linarith) hY0 ?_
    rw [hhs]
    apply div_le_div_of_nonneg_right _ hη.le
    linarith
  -- the trace comparison
  have h3 : (n : ℝ)⁻¹ * (E + η * Complex.I).im⁻¹ ≤ s := by
    rw [hzim, ← mul_inv]
    set x : ℝ := n * η with hx
    have hx1 : 1 ≤ x := hnη
    have hsx : Real.sqrt x ≤ x := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
    have hsx0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
    calc x⁻¹ ≤ (Real.sqrt x)⁻¹ := inv_anti₀ hsx0 hsx
      _ ≤ t * (Real.sqrt x)⁻¹ := le_mul_of_one_le_left (inv_nonneg.mpr hsx0.le) ht
      _ = s := by rw [hs, div_eq_mul_inv]
  linarith


/-- `⟨X - Y⟩ = ⟨X⟩ - ⟨Y⟩`. -/
private lemma deformedSchurStep_ntr_sub {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ntr (X - Y) = ntr X - ntr Y := by
  simp only [ntr, Matrix.trace_sub, mul_sub]

/-- Schur complement formula of Appendix G.1 [app:relative-local-law-proof] at one height: the
entries `G_ii` are within `2 C₁ s ‖M̃_i‖²` of the trial profile `M̃_i = (-b_i - z - ⟨G⟩)⁻¹`, whose
entries have norm at most `ρ⁻¹`, so that `⟨G⟩` solves the scalar Dyson equation of Lemma A.21
[da:lem:deformed] with residual at most `2 C₁ s ρ⁻²`; here `s = t/√(nη)`. -/
private lemma deformedSchurStep_core {n : ℕ} (hn : 0 < n) {V B : Matrix (Fin n) (Fin n) ℂ}
    (hV : V.IsHermitian) (hB : B.IsHermitian) (hBd : B.IsDiag) {Cstar Y ρ E η t : ℝ}
    (hη : 0 < η) (hηC : η ≤ Cstar + 3) (hnη : 1 ≤ (n : ℝ) * η) (ht : 1 ≤ t)
    (hVd : ∀ i, ‖V i i‖ ≤ t / Real.sqrt n)
    (hQ : ∀ i, ‖schurQuadDev (V - B) (E + η * Complex.I) i‖ ≤
      t / n * Real.sqrt (∑ k, ∑ l,
        ‖resolventMat (minorMat (V - B) i) (E + η * Complex.I) k l‖ ^ 2))
    (hY : (ntr (resolventMat (V - B) (E + η * Complex.I))).im ≤ Y) (hρ : 0 < ρ)
    (hρw : ρ ≤ η + (ntr (resolventMat (V - B) (E + η * Complex.I))).im)
    (hinv : (Real.sqrt (Cstar + 3) + Real.sqrt (Y + 1) + 1) * (t / Real.sqrt (n * η)) ≤ ρ / 2) :
    (∀ i, ‖resolventMat (V - B) (E + η * Complex.I) i i -
        deformedMat B (E + η * Complex.I) (ntr (resolventMat (V - B) (E + η * Complex.I))) i i‖ ≤
      2 * ((Real.sqrt (Cstar + 3) + Real.sqrt (Y + 1) + 1) * (t / Real.sqrt (n * η))) *
        ‖deformedMat B (E + η * Complex.I)
          (ntr (resolventMat (V - B) (E + η * Complex.I))) i i‖ ^ 2) ∧
    (∀ i, ‖deformedMat B (E + η * Complex.I)
        (ntr (resolventMat (V - B) (E + η * Complex.I))) i i‖ ≤ ρ⁻¹) ∧
    ‖ntr (resolventMat (V - B) (E + η * Complex.I)) -
      deformedMap B (E + η * Complex.I) (ntr (resolventMat (V - B) (E + η * Complex.I)))‖ ≤
        2 * ((Real.sqrt (Cstar + 3) + Real.sqrt (Y + 1) + 1) * (t / Real.sqrt (n * η))) *
          ρ⁻¹ ^ 2 := by
  have hzim : (E + η * Complex.I).im = η := by simp
  have hz : 0 < (E + η * Complex.I).im := by rw [hzim]; exact hη
  set z : ℂ := E + η * Complex.I with hzdef
  set q : ℂ := ntr (resolventMat (V - B) z) with hq
  set C₁ : ℝ := Real.sqrt (Cstar + 3) + Real.sqrt (Y + 1) + 1 with hC₁
  set s : ℝ := t / Real.sqrt (n * η) with hs
  have hw : 0 < (z + q).im := by rw [Complex.add_im]; linarith
  have hentry : ∀ i, ‖resolventMat (V - B) z i i - deformedMat B z q i i‖ ≤
      2 * (C₁ * s) * ‖deformedMat B z q i i‖ ^ 2 ∧ ‖deformedMat B z q i i‖ ≤ ρ⁻¹ := by
    intro i
    obtain ⟨δ, hGi, hδ⟩ := deformedSchurStep_schur hV hB hz i
    have hδ' : ‖δ‖ ≤ C₁ * s :=
      hδ.trans (deformedSchurStep_delta_le hn hV hB hη hηC hnη ht hVd hQ hY i)
    have hM : deformedMat B z q i i = (-B i i - (z + q))⁻¹ :=
      deformedSchurStep_deformedMat_diag hBd hB hw i
    have haim : (-B i i - (z + q)).im = -(η + q.im) := by
      simp [deformedSchurStep_im_diag hB i, hzim]
    have hρa : ρ ≤ -(-B i i - (z + q)).im := by rw [haim]; linarith
    have hna : ρ ≤ ‖-B i i - (z + q)‖ := by
      have h := Complex.abs_im_le_norm (-B i i - (z + q))
      rw [abs_of_nonpos (by linarith)] at h
      linarith
    have hne : -B i i - (z + q) ≠ 0 := norm_pos_iff.mp (by linarith)
    refine ⟨?_, by rw [hM]; exact deformedSchurStep_norm_inv_le hρ hρa⟩
    obtain ⟨-, hlt⟩ := deformedSchurStep_inv_sub hne (by linarith : ‖δ‖ ≤ ‖-B i i - (z + q)‖ / 2)
    rw [hGi, hM]
    calc _ ≤ 2 * ‖δ‖ * ‖(-B i i - (z + q))⁻¹‖ ^ 2 := hlt
      _ ≤ 2 * (C₁ * s) * ‖(-B i i - (z + q))⁻¹‖ ^ 2 := by gcongr
  refine ⟨fun i => (hentry i).1, fun i => (hentry i).2, ?_⟩
  have e : ntr (resolventMat (V - B) z - deformedMat B z q) = q - deformedMap B z q :=
    deformedSchurStep_ntr_sub _ _
  rw [← e]
  refine deformedSchurStep_norm_ntr_le hn fun i => ?_
  rw [Matrix.sub_apply]
  refine (hentry i).1.trans ?_
  have h1 := (hentry i).2
  have h0 : 0 ≤ C₁ * s := by positivity
  calc 2 * (C₁ * s) * ‖deformedMat B z q i i‖ ^ 2 ≤ 2 * (C₁ * s) * ρ⁻¹ ^ 2 := by gcongr


/-- `-B_ii - w ≠ 0` for Hermitian `B` and `Im w > 0`. -/
private lemma deformedSchurStep_entry_ne {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ}
    (hB : B.IsHermitian) {w : ℂ} (hw : 0 < w.im) (i : Fin n) : -B i i - w ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp [deformedSchurStep_im_diag hB i] at this
  linarith

/-- The entry law (G.3) [us:eq:weighted-entry-law]: if `G_ii` is within `2 C₁ s ‖M̃_i‖²` of
`M̃_i = (-b_i - z - q)⁻¹`, `|q - m| ≤ C₂ s` and `|q - m| ‖M̃_i‖ ≤ 1`, then `G_ii` is within
`(8 C₁ + 2 C₂) s ‖M_ii‖²` of `M_ii = (-b_i - z - m)⁻¹`. -/
private lemma deformedSchurStep_entry {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ}
    (hB : B.IsHermitian) (hBd : B.IsDiag) {z q m g : ℂ} {C₁ C₂ s : ℝ}
    (hwq : 0 < (z + q).im) (hwm : 0 < (z + m).im) (hC₁ : 0 ≤ C₁) (hs : 0 ≤ s)
    (hdiff : ‖q - m‖ ≤ C₂ * s) (i : Fin n)
    (hqm : ‖q - m‖ * ‖deformedMat B z q i i‖ ≤ 1)
    (hg : ‖g - deformedMat B z q i i‖ ≤ 2 * (C₁ * s) * ‖deformedMat B z q i i‖ ^ 2) :
    ‖g - deformedMat B z m i i‖ ≤ (8 * C₁ + 2 * C₂) * s * ‖deformedMat B z m i i‖ ^ 2 := by
  rw [deformedSchurStep_deformedMat_diag hBd hB hwm] 
  rw [deformedSchurStep_deformedMat_diag hBd hB hwq] at hqm hg
  have hna := deformedSchurStep_entry_ne hB hwq i
  have hnb := deformedSchurStep_entry_ne hB hwm i
  have hba : -B i i - (z + m) - (-B i i - (z + q)) = q - m := by ring
  have hqm' : ‖-B i i - (z + m) - (-B i i - (z + q))‖ * ‖(-B i i - (z + q))⁻¹‖ ≤ 1 := by
    rw [hba]; exact hqm
  obtain ⟨h1, h2⟩ := deformedSchurStep_ratio hna hnb hqm'
  rw [hba] at h1
  set a : ℂ := (-B i i - (z + q))⁻¹ with ha
  set b : ℂ := (-B i i - (z + m))⁻¹ with hb
  have hb0 : 0 ≤ ‖b‖ := norm_nonneg _
  have hC₂ : 0 ≤ C₂ * s := le_trans (norm_nonneg _) hdiff
  calc ‖g - b‖ ≤ ‖g - a‖ + ‖a - b‖ := norm_sub_le_norm_sub_add_norm_sub g a b
    _ ≤ 2 * (C₁ * s) * ‖a‖ ^ 2 + ‖q - m‖ * ‖a‖ * ‖b‖ := add_le_add hg h1
    _ ≤ 2 * (C₁ * s) * (2 * ‖b‖) ^ 2 + (C₂ * s) * (2 * ‖b‖) * ‖b‖ := by
        have hC1s : 0 ≤ C₁ * s := mul_nonneg hC₁ hs
        gcongr
    _ = (8 * C₁ + 2 * C₂) * s * ‖b‖ ^ 2 := by ring


/-- Single-height step of the proof of Lemma G.1 [us:lem:local-law] (Appendix G.1
[app:relative-local-law-proof]) for diagonal `B`: if every `|V_ii| ≤ t n^{-1/2}`, every centred
quadratic form is at most `t n⁻¹ ‖G^{(i)}‖_HS`, and either `η ≥ 2` or `⟨G⟩` is already within
`c₀` of `m_B`, then `|⟨G⟩ - m_B| ≤ C t (nη)^{-1/2}` and
`|G_ii - (M_B)_ii| ≤ C t (nη)^{-1/2} |(M_B)_ii|²`, as in (G.3) [us:eq:weighted-entry-law]. -/
theorem deformed_schur_step (κ₀ Cstar : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hC : 0 < Cstar) :
    ∃ ε₀ c₀ C : ℝ, 0 < ε₀ ∧ 0 < c₀ ∧ 0 < C ∧
      ∀ (n : ℕ) (V B : Matrix (Fin n) (Fin n) ℂ) (ε E η t : ℝ), 0 < n → V.IsHermitian →
        B.IsDiag → 0 ≤ ε → ε ≤ ε₀ → DeformClass ε B → |E| ≤ 2 - κ₀ → 0 < η →
        η ≤ Cstar + 3 → 1 ≤ (n : ℝ) * η → 1 ≤ t → t / Real.sqrt (n * η) ≤ c₀ →
        (∀ i, ‖V i i‖ ≤ t / Real.sqrt n) →
        (∀ i, ‖schurQuadDev (V - B) (E + η * Complex.I) i‖ ≤
          t / n * Real.sqrt (∑ k, ∑ l,
            ‖resolventMat (minorMat (V - B) i) (E + η * Complex.I) k l‖ ^ 2)) →
        (2 ≤ η ∨ ‖ntr (resolventMat (V - B) (E + η * Complex.I)) -
          mB B (E + η * Complex.I)‖ ≤ c₀) →
        ‖ntr (resolventMat (V - B) (E + η * Complex.I)) - mB B (E + η * Complex.I)‖ ≤
            C * (t / Real.sqrt (n * η)) ∧
          ∀ i, ‖resolventMat (V - B) (E + η * Complex.I) i i - MB B (E + η * Complex.I) i i‖ ≤
            C * (t / Real.sqrt (n * η)) * ‖MB B (E + η * Complex.I) i i‖ ^ 2 := by
  have hH2 : 0 < max Cstar 2 := lt_max_of_lt_right two_pos
  obtain ⟨ε₁, Cp, hε₁, hCp, hprof⟩ := deformed_profile κ₀ (max Cstar 2) hκ₀ hκ₀' hH2
  obtain ⟨ε₂, r₀, CA, hε₂, hr₀, hCA, hres⟩ :=
    deformed_residual_stability κ₀ (max Cstar 2) hκ₀ hκ₀' hH2
  have hCp0 : 0 < Cp := by linarith
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (2 * Cp)⁻¹ := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  have hρinv : ρ⁻¹ = 2 * Cp := by rw [hρ, inv_inv]
  have hρCp : Cp⁻¹ = 2 * ρ := by rw [hρ]; field_simp
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = Real.sqrt (Cstar + 3) + Real.sqrt (Cp + 1 + 1) + 1 :=
    ⟨_, rfl⟩
  have hC₁0 : 0 < C₁ := by rw [hC₁]; positivity
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 2 * C₁ * (2 * Cp) ^ 2 := ⟨_, rfl⟩
  have hR0 : 0 < R := by rw [hR]; positivity
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, C₂ = max (4 / 3) CA * R := ⟨_, rfl⟩
  have hC₂0 : 0 < C₂ := by rw [hC₂]; positivity
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ,
      c₀ = min (min (min ρ r₀) 1) (min (ρ / (2 * C₁)) (ρ / C₂)) := ⟨_, rfl⟩
  have hc₀0 : 0 < c₀ := by
    rw [hc₀]
    refine lt_min (lt_min (lt_min hρ0 hr₀) one_pos) (lt_min ?_ ?_) <;> positivity
  have hc₀ρ : c₀ ≤ ρ := by
    rw [hc₀]; exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hc₀r : c₀ ≤ r₀ := by
    rw [hc₀]; exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hc₀1 : c₀ ≤ 1 := by
    rw [hc₀]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hc₀C₁ : c₀ ≤ ρ / (2 * C₁) := by
    rw [hc₀]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hc₀C₂ : c₀ ≤ ρ / C₂ := by
    rw [hc₀]; exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨min ε₁ ε₂, c₀, 8 * C₁ + 2 * C₂, lt_min hε₁ hε₂, hc₀0, by positivity, ?_⟩
  intro n V B ε E η t hn hV hBd hε hεε₀ hBc hE hη hηC hnη ht hs hVd hQ hdisj
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hB : B.IsHermitian := hBc.1
  have hH : (V - B).IsHermitian := hV.sub hB
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hzim : (E + η * Complex.I).im = η := by simp
  have hz : 0 < (E + η * Complex.I).im := by rw [hzim]; exact hη
  have hεε₁ : ε ≤ ε₁ := hεε₀.trans (min_le_left _ _)
  have hεε₂ : ε ≤ ε₂ := hεε₀.trans (min_le_right _ _)
  set z : ℂ := E + η * Complex.I with hzdef
  set q : ℂ := ntr (resolventMat (V - B) z) with hq
  set m : ℂ := mB B z with hm
  set s : ℝ := t / Real.sqrt (n * η) with hsdef
  have hs0 : 0 ≤ s := by positivity
  have hmroot : IsDeformedRoot B z m := isDeformedRoot_mB hB hz
  -- facts on `Im q`
  have hq0 : 0 ≤ q.im := by
    rw [hq, deformedSchurStep_im_ntr]
    have := deformedSchurStep_im_trace_nonneg hH E hη
    positivity
  have hdiag : ∀ i, ‖resolventMat (V - B) z i i‖ ≤ η⁻¹ := by
    intro i
    obtain ⟨hQ0, hd⟩ := norm_resolventMat_diag_le_schur hH hz i
    refine hd.trans ?_
    rw [hzim]
    exact inv_anti₀ hη (by linarith)
  -- a priori facts on `⟨G⟩`, from either branch of the dichotomy
  have hapriori : q.im ≤ Cp + 1 ∧ ρ ≤ η + q.im := by
    by_cases h2 : 2 ≤ η
    · have h1 : ‖q‖ ≤ η⁻¹ := deformedSchurStep_norm_ntr_le hn hdiag
      have h3 : q.im ≤ ‖q‖ := (le_abs_self _).trans (Complex.abs_im_le_norm q)
      have h4 : η⁻¹ ≤ 2⁻¹ := inv_anti₀ two_pos h2
      refine ⟨by linarith, ?_⟩
      have h5 : ρ ≤ 2⁻¹ := by
        rw [hρ]
        exact inv_anti₀ two_pos (by linarith)
      linarith
    · have hηH : η ≤ max Cstar 2 := (le_of_lt (not_le.mp h2)).trans (le_max_right _ _)
      have hc : ‖q - m‖ ≤ c₀ := hdisj.resolve_left h2
      obtain ⟨hlo, hhi, -⟩ := hprof (Fin n) B ε E η hε hεε₁ hBc hE hη hηH
      have h6 : |(q - m).im| ≤ ‖q - m‖ := Complex.abs_im_le_norm _
      rw [Complex.sub_im] at h6
      have h7 := abs_le.mp (h6.trans hc)
      constructor
      · linarith
      · linarith
  -- stability of the scalar Dyson equation
  have hstab : ‖q - m‖ ≤ max (4 / 3) CA * ‖q - deformedMap B z q‖ := by
    by_cases h2 : 2 ≤ η
    · have h := deformed_stability_high hB E h2 hq0
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    · have hηH : η ≤ max Cstar 2 := (le_of_lt (not_le.mp h2)).trans (le_max_right _ _)
      have hc : ‖q - m‖ ≤ c₀ := hdisj.resolve_left h2
      have h := hres (Fin n) B ε E η hε hεε₂ hBc hE hη hηH q (hc.trans hc₀r)
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  have hinv : C₁ * s ≤ ρ / 2 := by
    have h1 : s ≤ ρ / (2 * C₁) := hs.trans hc₀C₁
    calc C₁ * s ≤ C₁ * (ρ / (2 * C₁)) := by gcongr
      _ = ρ / 2 := by field_simp
  obtain ⟨hentry, hMt, hresid⟩ := deformedSchurStep_core hn hV hB hBd hη hηC hnη ht hVd hQ
    (Y := Cp + 1) hapriori.1 hρ0 hapriori.2 (by rw [← hC₁]; exact hinv)
  rw [← hC₁] at hentry hresid
  have hdiffC : ‖q - m‖ ≤ C₂ * s := by
    calc ‖q - m‖ ≤ max (4 / 3) CA * ‖q - deformedMap B z q‖ := hstab
      _ ≤ max (4 / 3) CA * (2 * (C₁ * s) * ρ⁻¹ ^ 2) := by gcongr
      _ = C₂ * s := by rw [hρinv, hC₂, hR]; ring
  have hqmρ : ‖q - m‖ ≤ ρ := by
    calc ‖q - m‖ ≤ C₂ * s := hdiffC
      _ ≤ C₂ * (ρ / C₂) := by gcongr; exact hs.trans hc₀C₂
      _ = ρ := by field_simp
  have hwq : 0 < (z + q).im := by rw [Complex.add_im]; linarith [hapriori.2]
  have hwm : 0 < (z + m).im := by rw [Complex.add_im, hzim]; linarith [hmroot.1]
  refine ⟨?_, fun i => ?_⟩
  · calc ‖q - m‖ ≤ C₂ * s := hdiffC
      _ ≤ (8 * C₁ + 2 * C₂) * s := mul_le_mul_of_nonneg_right (by linarith) hs0
  · have hqm : ‖q - m‖ * ‖deformedMat B z q i i‖ ≤ 1 := by
      calc ‖q - m‖ * ‖deformedMat B z q i i‖ ≤ ρ * ρ⁻¹ :=
            mul_le_mul hqmρ (hMt i) (norm_nonneg _) hρ0.le
        _ = 1 := mul_inv_cancel₀ hρ0.ne'
    exact deformedSchurStep_entry hB hBd hwq hwm hC₁0.le hs0 hdiffC i hqm (hentry i)

end LSBA
