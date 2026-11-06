import LSBA.Dyson.Semicircle
import LSBA.Dyson.DeformClass

/-!
# Small-norm and small-rank deformations

Lemma A.21 [da:lem:deformed]: for `B ∈ 𝓑(ε)` with ε small, `Im m_B ≍ 1` and `Im M_B ≍ (I + B²)⁻¹` as
forms, (A.81) [us:eq:deformed-profile]; and (A.82) [da:eq:deformed-scalar-stability].
-/

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section
open scoped Classical

namespace LSBA

section Helpers

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The function `f` of a Hermitian matrix in terms of its eigenvector unitary `U`:
`U diag(f) U^*`. -/
private def deformed_spec (U : Matrix ι ι ℂ) (f : ι → ℂ) : Matrix ι ι ℂ :=
  U * Matrix.diagonal f * star U

private lemma deformed_spec_mul {U : Matrix ι ι ℂ} (hU : star U * U = 1) (f g : ι → ℂ) :
    deformed_spec U f * deformed_spec U g = deformed_spec U (f * g) := by
  unfold deformed_spec
  have : U * Matrix.diagonal f * star U * (U * Matrix.diagonal g * star U) =
      U * Matrix.diagonal f * (star U * U) * Matrix.diagonal g * star U := by
    simp only [Matrix.mul_assoc]
  rw [this, hU, Matrix.mul_one, Matrix.mul_assoc U, Matrix.diagonal_mul_diagonal]
  rfl

private lemma deformed_spec_add (U : Matrix ι ι ℂ) (f g : ι → ℂ) :
    deformed_spec U f + deformed_spec U g = deformed_spec U (f + g) := by
  unfold deformed_spec
  rw [← Matrix.add_mul, ← Matrix.mul_add, Matrix.diagonal_add]
  rfl

private lemma deformed_spec_const {U : Matrix ι ι ℂ} (hU : U * star U = 1) (a : ℂ) :
    deformed_spec U (fun _ => a) = a • (1 : Matrix ι ι ℂ) := by
  unfold deformed_spec
  rw [← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU]

private lemma deformed_spec_sub {U : Matrix ι ι ℂ} (f g : ι → ℂ) :
    deformed_spec U f - deformed_spec U g = deformed_spec U (f - g) := by
  unfold deformed_spec
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
  rfl

private lemma deformed_ntr_spec {U : Matrix ι ι ℂ} (hU : star U * U = 1) (f : ι → ℂ) :
    ntr (deformed_spec U f) = (Fintype.card ι : ℂ)⁻¹ * ∑ k, f k := by
  unfold ntr deformed_spec
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul,
    Matrix.trace_diagonal]


private lemma deformed_unitary_left (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    star (hA.eigenvectorUnitary : Matrix ι ι ℂ) * (hA.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
  Unitary.coe_star_mul_self _

private lemma deformed_unitary_right (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix ι ι ℂ) * star (hA.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
  Unitary.coe_mul_star_self _

/-- Spectral theorem in the form `A = U diag(λ) U^*`. -/
private lemma deformed_eq_spec {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    A = deformed_spec (hA.eigenvectorUnitary : Matrix ι ι ℂ)
      (fun k => ((hA.eigenvalues k : ℝ) : ℂ)) := by
  have h := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  exact h

/-- The resolvent in the eigenbasis of `A`. -/
private lemma deformed_resolventMat_eq_spec {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {w : ℂ}
    (hw : w.im ≠ 0) :
    resolventMat A w = deformed_spec (hA.eigenvectorUnitary : Matrix ι ι ℂ)
      (fun k => (((hA.eigenvalues k : ℝ) : ℂ) - w)⁻¹) := by
  set U : Matrix ι ι ℂ := (hA.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hne : ∀ k, ((hA.eigenvalues k : ℝ) : ℂ) - w ≠ 0 := by
    intro k h
    apply hw
    have := congrArg Complex.im h
    simpa using this.symm
  have h1 : A - w • (1 : Matrix ι ι ℂ) =
      deformed_spec U (fun k => ((hA.eigenvalues k : ℝ) : ℂ) - w) := by
    have e : (fun k => ((hA.eigenvalues k : ℝ) : ℂ) - w) =
        (fun k => ((hA.eigenvalues k : ℝ) : ℂ)) - (fun _ => w) := rfl
    rw [e, ← deformed_spec_sub, deformed_spec_const (deformed_unitary_right A hA) w,
      ← deformed_eq_spec hA]
  unfold resolventMat
  refine Matrix.inv_eq_right_inv ?_
  rw [h1, deformed_spec_mul (deformed_unitary_left A hA)]
  have h2 : (fun k => ((hA.eigenvalues k : ℝ) : ℂ) - w) *
      (fun k => (((hA.eigenvalues k : ℝ) : ℂ) - w)⁻¹) = fun _ => (1 : ℂ) := by
    funext k
    exact mul_inv_cancel₀ (hne k)
  rw [h2, deformed_spec_const (deformed_unitary_right A hA), one_smul]

/-- A quadratic form of `U diag(f) U^*` is the `|u_k|²`-weighted sum of `f`, `u = U^* v`. -/
private lemma deformed_form_spec {U : Matrix ι ι ℂ} (f : ι → ℂ) (v : ι → ℂ) :
    star v ⬝ᵥ (deformed_spec U f *ᵥ v) =
      ∑ k, f k * (((‖(star U *ᵥ v) k‖ ^ 2 : ℝ)) : ℂ) := by
  unfold deformed_spec
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have h : star v ᵥ* U = star (star U *ᵥ v) := by
    rw [Matrix.star_mulVec]
    simp [Matrix.star_eq_conjTranspose]
  rw [h]
  simp only [dotProduct, Pi.star_apply, Matrix.mulVec_diagonal]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.ofReal_pow, ← Complex.conj_mul']
  simp
  ring


/-- `(1 + A²)⁻¹` in the eigenbasis of a Hermitian `A`. -/
private lemma deformed_inv_one_add_mul_self {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (1 + A * A)⁻¹ = deformed_spec (hA.eigenvectorUnitary : Matrix ι ι ℂ)
      (fun k => (((1 + hA.eigenvalues k ^ 2)⁻¹ : ℝ) : ℂ)) := by
  set U : Matrix ι ι ℂ := (hA.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hUl := deformed_unitary_left A hA
  have hUr := deformed_unitary_right A hA
  have h1 : (1 : Matrix ι ι ℂ) + A * A =
      deformed_spec U
        (fun k => 1 + ((hA.eigenvalues k : ℝ) : ℂ) * ((hA.eigenvalues k : ℝ) : ℂ)) := by
    have e1 : A * A = deformed_spec U (fun k => ((hA.eigenvalues k : ℝ) : ℂ)) *
        deformed_spec U (fun k => ((hA.eigenvalues k : ℝ) : ℂ)) := by
      rw [← deformed_eq_spec hA]
    have e2 : (1 : Matrix ι ι ℂ) = deformed_spec U (fun _ => 1) := by
      rw [deformed_spec_const hUr, one_smul]
    rw [e1, deformed_spec_mul hUl]
    conv_lhs => rw [e2]
    rw [deformed_spec_add]
    rfl
  refine Matrix.inv_eq_right_inv ?_
  rw [h1, deformed_spec_mul hUl]
  have h2 : (fun k => 1 + ((hA.eigenvalues k : ℝ) : ℂ) * ((hA.eigenvalues k : ℝ) : ℂ)) *
      (fun k => (((1 + hA.eigenvalues k ^ 2)⁻¹ : ℝ) : ℂ)) = fun _ => (1 : ℂ) := by
    funext k
    have hpos : (0 : ℝ) < 1 + hA.eigenvalues k ^ 2 := by positivity
    have : (1 + ((hA.eigenvalues k : ℝ) : ℂ) * ((hA.eigenvalues k : ℝ) : ℂ)) =
        (((1 + hA.eigenvalues k ^ 2 : ℝ)) : ℂ) := by push_cast; ring
    simp only [Pi.mul_apply]
    rw [this, ← Complex.ofReal_mul, mul_inv_cancel₀ hpos.ne', Complex.ofReal_one]
  rw [h2, deformed_spec_const hUr, one_smul]

/-- `(1 + B²)⁻¹` in the eigenbasis of `-B`. -/
private lemma deformed_inv_one_add_sq {B : Matrix ι ι ℂ} (hB : B.IsHermitian) :
    (1 + B * B)⁻¹ = deformed_spec (hB.neg.eigenvectorUnitary : Matrix ι ι ℂ)
      (fun k => (((1 + hB.neg.eigenvalues k ^ 2)⁻¹ : ℝ) : ℂ)) := by
  rw [← neg_mul_neg B B]
  exact deformed_inv_one_add_mul_self hB.neg

omit [DecidableEq ι] in
/-- The scalar Dyson function `w ↦ n⁻¹ ∑_k (c_k - w)⁻¹` for real numbers `c_k`. -/
private def deformed_S (c : ι → ℝ) (w : ℂ) : ℂ :=
  (Fintype.card ι : ℂ)⁻¹ * ∑ k, ((c k : ℂ) - w)⁻¹

omit [DecidableEq ι] in
/-- The average `n⁻¹ ∑_k (c_k - w)⁻¹ (c_k - w')⁻¹`. -/
private def deformed_P (c : ι → ℝ) (w w' : ℂ) : ℂ :=
  (Fintype.card ι : ℂ)⁻¹ * ∑ k, ((c k : ℂ) - w)⁻¹ * ((c k : ℂ) - w')⁻¹

/-- The trial profile in the eigenbasis of `-B`. -/
private lemma deformed_mat_eq_spec {B : Matrix ι ι ℂ} (hB : B.IsHermitian) {w : ℂ}
    (hw : w.im ≠ 0) (z q : ℂ) (hzq : z + q = w) :
    deformedMat B z q = deformed_spec (hB.neg.eigenvectorUnitary : Matrix ι ι ℂ)
      (fun k => (((hB.neg.eigenvalues k : ℝ) : ℂ) - w)⁻¹) := by
  unfold deformedMat
  rw [hzq]
  exact deformed_resolventMat_eq_spec hB.neg hw

/-- The scalar Dyson map in the eigenvalues of `-B`. -/
private lemma deformed_deformedMap_eq {B : Matrix ι ι ℂ} (hB : B.IsHermitian) {z q : ℂ}
    (hw : (z + q).im ≠ 0) :
    deformedMap B z q = deformed_S (fun k => hB.neg.eigenvalues k) (z + q) := by
  unfold deformedMap
  rw [deformed_mat_eq_spec hB hw z q rfl, deformed_ntr_spec (deformed_unitary_left _ hB.neg)]
  rfl

/-- `⟨M_q M_q⟩` in the eigenvalues of `-B`. -/
private lemma deformed_ntr_deformedMat_mul_self {B : Matrix ι ι ℂ} (hB : B.IsHermitian) {z q : ℂ}
    (hw : (z + q).im ≠ 0) :
    ntr (deformedMat B z q * deformedMat B z q) =
      deformed_P (fun k => hB.neg.eigenvalues k) (z + q) (z + q) := by
  rw [deformed_mat_eq_spec hB hw z q rfl, deformed_spec_mul (deformed_unitary_left _ hB.neg),
    deformed_ntr_spec (deformed_unitary_left _ hB.neg)]
  unfold deformed_P
  simp only [Pi.mul_apply]


omit [DecidableEq ι] in
private lemma deformed_ne (c' : ℝ) {w : ℂ} (hw : 0 < w.im) : (c' : ℂ) - w ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

private lemma deformed_neg_ne {w : ℂ} (hw : 0 < w.im) : -w ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

private lemma deformed_norm_inv_le (c' : ℝ) {τ : ℝ} {w : ℂ} (hτ : 0 < τ) (hw : τ ≤ w.im) :
    ‖((c' : ℂ) - w)⁻¹‖ ≤ 1 / τ := by
  rw [norm_inv, one_div]
  apply inv_anti₀ hτ
  have h := Complex.abs_im_le_norm ((c' : ℂ) - w)
  have h2 : ((c' : ℂ) - w).im = -w.im := by simp
  rw [h2, abs_neg, abs_of_pos (lt_of_lt_of_le hτ hw)] at h
  linarith

private lemma deformed_norm_neg_inv_le {τ : ℝ} {w : ℂ} (hτ : 0 < τ) (hw : τ ≤ w.im) :
    ‖(-w)⁻¹‖ ≤ 1 / τ := by
  have := deformed_norm_inv_le 0 hτ hw
  simpa using this

omit [DecidableEq ι] in
/-- Averaging a bound that is `β₁` for the `|c_k| ≤ ε` and `β₂` for the at most `ε n` others. -/
private lemma deformed_avg_le [Nonempty ι] (c : ι → ℝ) {ε β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    (hcount : ((Finset.univ.filter fun k => ε < |c k|).card : ℝ) ≤ ε * Fintype.card ι)
    (g : ι → ℂ) (hsmall : ∀ k, |c k| ≤ ε → ‖g k‖ ≤ β₁) (hall : ∀ k, ‖g k‖ ≤ β₂) :
    ‖(Fintype.card ι : ℂ)⁻¹ * ∑ k, g k‖ ≤ β₁ + ε * β₂ := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have h1 : ∑ k, ‖g k‖ ≤ Fintype.card ι * β₁ +
      (Finset.univ.filter fun k => ε < |c k|).card * β₂ := by
    calc ∑ k, ‖g k‖ ≤ ∑ k, (β₁ + if ε < |c k| then β₂ else 0) := by
          refine Finset.sum_le_sum fun k _ => ?_
          by_cases h : ε < |c k|
          · simp only [h, ite_true]
            linarith [hall k]
          · simp only [h, ite_false, add_zero]
            exact hsmall k (not_lt.mp h)
      _ = Fintype.card ι * β₁ + (Finset.univ.filter fun k => ε < |c k|).card * β₂ := by
          rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const, Finset.sum_const]
          simp
  have h2 : ‖∑ k, g k‖ ≤ Fintype.card ι * β₁ + ε * Fintype.card ι * β₂ :=
    (norm_sum_le _ _).trans (h1.trans (by nlinarith))
  calc (Fintype.card ι : ℝ)⁻¹ * ‖∑ k, g k‖
      ≤ (Fintype.card ι : ℝ)⁻¹ * (Fintype.card ι * β₁ + ε * Fintype.card ι * β₂) := by gcongr
    _ = β₁ + ε * β₂ := by field_simp

/-- For `|c'| ≤ ε` and `Im w ≥ τ`: `|(c' - w)⁻¹ - (-w)⁻¹| ≤ ε / τ²`. -/
private lemma deformed_inv_sub_le (c' : ℝ) {ε τ : ℝ} {w : ℂ} (hτ : 0 < τ) (hw : τ ≤ w.im)
    (hc : |c'| ≤ ε) : ‖((c' : ℂ) - w)⁻¹ - (-w)⁻¹‖ ≤ ε / τ ^ 2 := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans hc
  have hwp : 0 < w.im := lt_of_lt_of_le hτ hw
  have e : ((c' : ℂ) - w)⁻¹ - (-w)⁻¹ = ((c' : ℂ) - w)⁻¹ * (-(c' : ℂ)) * (-w)⁻¹ := by
    rw [inv_sub_inv' (deformed_ne c' hwp) (deformed_neg_ne hwp)]
    congr 2
    ring
  rw [e, norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have h1 := deformed_norm_inv_le c' hτ hw
  have h2 := deformed_norm_neg_inv_le hτ hw
  calc ‖((c' : ℂ) - w)⁻¹‖ * |c'| * ‖(-w)⁻¹‖ ≤ 1 / τ * ε * (1 / τ) := by gcongr
    _ = ε / τ ^ 2 := by field_simp

omit [DecidableEq ι] in
/-- `⟨(c - w)⁻¹⟩` is within `ε/τ² + 2ε/τ` of the model value `(-w)⁻¹`. -/
private lemma deformed_S_close [Nonempty ι] (c : ι → ℝ) {ε τ : ℝ} {w : ℂ} (hε : 0 ≤ ε)
    (hτ : 0 < τ) (hw : τ ≤ w.im)
    (hcount : ((Finset.univ.filter fun k => ε < |c k|).card : ℝ) ≤ ε * Fintype.card ι) :
    ‖deformed_S c w - (-w)⁻¹‖ ≤ ε / τ ^ 2 + ε * (2 / τ) := by
  have hn : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have e : deformed_S c w - (-w)⁻¹ =
      (Fintype.card ι : ℂ)⁻¹ * ∑ k, (((c k : ℂ) - w)⁻¹ - (-w)⁻¹) := by
    unfold deformed_S
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  rw [e]
  have h2 := deformed_norm_neg_inv_le hτ hw
  refine deformed_avg_le c (by positivity) (by positivity) hcount _
    (fun k hk => deformed_inv_sub_le (c k) hτ hw hk) (fun k => ?_)
  calc ‖((c k : ℂ) - w)⁻¹ - (-w)⁻¹‖ ≤ ‖((c k : ℂ) - w)⁻¹‖ + ‖(-w)⁻¹‖ := norm_sub_le _ _
    _ ≤ 1 / τ + 1 / τ := add_le_add (deformed_norm_inv_le (c k) hτ hw) h2
    _ = 2 / τ := by ring

omit [DecidableEq ι] in
/-- `⟨(c - w)⁻¹ (c - w')⁻¹⟩` is within `2ε/τ³ + 2ε/τ²` of the model value `(-w)⁻¹ (-w')⁻¹`. -/
private lemma deformed_P_close [Nonempty ι] (c : ι → ℝ) {ε τ : ℝ} {w w' : ℂ} (hε : 0 ≤ ε)
    (hτ : 0 < τ) (hw : τ ≤ w.im) (hw' : τ ≤ w'.im)
    (hcount : ((Finset.univ.filter fun k => ε < |c k|).card : ℝ) ≤ ε * Fintype.card ι) :
    ‖deformed_P c w w' - (-w)⁻¹ * (-w')⁻¹‖ ≤ 2 * ε / τ ^ 3 + ε * (2 / τ ^ 2) := by
  have hn : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have e : deformed_P c w w' - (-w)⁻¹ * (-w')⁻¹ =
      (Fintype.card ι : ℂ)⁻¹ * ∑ k, (((c k : ℂ) - w)⁻¹ * ((c k : ℂ) - w')⁻¹ -
        (-w)⁻¹ * (-w')⁻¹) := by
    unfold deformed_P
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  rw [e]
  have h2 := deformed_norm_neg_inv_le hτ hw
  have h2' := deformed_norm_neg_inv_le hτ hw'
  have hid : ∀ k, ((c k : ℂ) - w)⁻¹ * ((c k : ℂ) - w')⁻¹ - (-w)⁻¹ * (-w')⁻¹ =
      (((c k : ℂ) - w)⁻¹ - (-w)⁻¹) * ((c k : ℂ) - w')⁻¹ +
        (-w)⁻¹ * (((c k : ℂ) - w')⁻¹ - (-w')⁻¹) := fun k => by ring
  refine deformed_avg_le c (by positivity) (by positivity) hcount _ (fun k hk => ?_) (fun k => ?_)
  · rw [hid k]
    calc ‖(((c k : ℂ) - w)⁻¹ - (-w)⁻¹) * ((c k : ℂ) - w')⁻¹ +
          (-w)⁻¹ * (((c k : ℂ) - w')⁻¹ - (-w')⁻¹)‖
        ≤ ‖((c k : ℂ) - w)⁻¹ - (-w)⁻¹‖ * ‖((c k : ℂ) - w')⁻¹‖ +
          ‖(-w)⁻¹‖ * ‖((c k : ℂ) - w')⁻¹ - (-w')⁻¹‖ :=
          (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
      _ ≤ ε / τ ^ 2 * (1 / τ) + 1 / τ * (ε / τ ^ 2) := by
          gcongr
          · exact deformed_inv_sub_le (c k) hτ hw hk
          · exact deformed_norm_inv_le (c k) hτ hw'
          · exact deformed_inv_sub_le (c k) hτ hw' hk
      _ = 2 * ε / τ ^ 3 := by field_simp; ring
  · calc ‖((c k : ℂ) - w)⁻¹ * ((c k : ℂ) - w')⁻¹ - (-w)⁻¹ * (-w')⁻¹‖
        ≤ ‖((c k : ℂ) - w)⁻¹ * ((c k : ℂ) - w')⁻¹‖ + ‖(-w)⁻¹ * (-w')⁻¹‖ := norm_sub_le _ _
      _ ≤ 1 / τ * (1 / τ) + 1 / τ * (1 / τ) := by
          rw [norm_mul, norm_mul]
          gcongr
          · exact deformed_norm_inv_le (c k) hτ hw
          · exact deformed_norm_inv_le (c k) hτ hw'
      _ = 2 / τ ^ 2 := by field_simp; ring

private lemma deformed_neg_inv_sub_le {τ : ℝ} {w w₀ : ℂ} (hτ : 0 < τ) (hw : τ ≤ w.im)
    (hw₀ : τ ≤ w₀.im) : ‖(-w)⁻¹ - (-w₀)⁻¹‖ ≤ ‖w - w₀‖ / τ ^ 2 := by
  have e : (-w)⁻¹ - (-w₀)⁻¹ = (-w)⁻¹ * (w - w₀) * (-w₀)⁻¹ := by
    rw [inv_sub_inv' (deformed_neg_ne (lt_of_lt_of_le hτ hw))
      (deformed_neg_ne (lt_of_lt_of_le hτ hw₀))]
    congr 2
    ring
  rw [e, norm_mul, norm_mul]
  have h1 := deformed_norm_neg_inv_le hτ hw
  have h2 := deformed_norm_neg_inv_le hτ hw₀
  calc ‖(-w)⁻¹‖ * ‖w - w₀‖ * ‖(-w₀)⁻¹‖ ≤ 1 / τ * ‖w - w₀‖ * (1 / τ) := by gcongr
    _ = ‖w - w₀‖ / τ ^ 2 := by field_simp

omit [DecidableEq ι] in
/-- Distance of `⟨(c - (z+q))⁻¹ (c - (z+q'))⁻¹⟩` from `m₀²` for `q, q'` within `r` of the
model root `m₀ = (-(z + m₀))⁻¹`. -/
private lemma deformed_P_sub_sq [Nonempty ι] (c : ι → ℝ) {ε τ r : ℝ} {z m₀ q q' : ℂ}
    (hε : 0 ≤ ε) (hτ : 0 < τ) (hm₀ : m₀ = (-(z + m₀))⁻¹) (hw₀ : τ ≤ (z + m₀).im)
    (hw : τ ≤ (z + q).im) (hw' : τ ≤ (z + q').im) (hq : ‖q - m₀‖ ≤ r) (hq' : ‖q' - m₀‖ ≤ r)
    (hcount : ((Finset.univ.filter fun k => ε < |c k|).card : ℝ) ≤ ε * Fintype.card ι) :
    ‖deformed_P c (z + q) (z + q') - m₀ ^ 2‖ ≤
      2 * ε / τ ^ 3 + ε * (2 / τ ^ 2) + 2 * r / τ ^ 3 := by
  have h1 := deformed_P_close c hε hτ hw hw' hcount
  have h2 := deformed_neg_inv_sub_le hτ hw hw₀
  have h2' := deformed_neg_inv_sub_le hτ hw' hw₀
  have e1 : (z + q) - (z + m₀) = q - m₀ := by ring
  have e2 : (z + q') - (z + m₀) = q' - m₀ := by ring
  rw [e1] at h2
  rw [e2] at h2'
  have hy := deformed_norm_neg_inv_le hτ hw
  have hy' := deformed_norm_neg_inv_le hτ hw'
  have hy₀ := deformed_norm_neg_inv_le hτ hw₀
  have hτr : 0 ≤ r := (norm_nonneg _).trans hq
  have h3 : ‖(-(z + q))⁻¹ * (-(z + q'))⁻¹ - m₀ ^ 2‖ ≤ 2 * r / τ ^ 3 := by
    have e : (-(z + q))⁻¹ * (-(z + q'))⁻¹ - m₀ ^ 2 =
        ((-(z + q))⁻¹ - (-(z + m₀))⁻¹) * (-(z + q'))⁻¹ +
          (-(z + m₀))⁻¹ * ((-(z + q'))⁻¹ - (-(z + m₀))⁻¹) := by
      rw [← hm₀]; ring
    rw [e]
    calc ‖((-(z + q))⁻¹ - (-(z + m₀))⁻¹) * (-(z + q'))⁻¹ +
          (-(z + m₀))⁻¹ * ((-(z + q'))⁻¹ - (-(z + m₀))⁻¹)‖
        ≤ ‖(-(z + q))⁻¹ - (-(z + m₀))⁻¹‖ * ‖(-(z + q'))⁻¹‖ +
          ‖(-(z + m₀))⁻¹‖ * ‖(-(z + q'))⁻¹ - (-(z + m₀))⁻¹‖ :=
          (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
      _ ≤ r / τ ^ 2 * (1 / τ) + 1 / τ * (r / τ ^ 2) := by
          gcongr
          · exact h2.trans (by gcongr)
          · exact h2'.trans (by gcongr)
      _ = 2 * r / τ ^ 3 := by field_simp; ring
  calc ‖deformed_P c (z + q) (z + q') - m₀ ^ 2‖
      = ‖(deformed_P c (z + q) (z + q') - (-(z + q))⁻¹ * (-(z + q'))⁻¹) +
          ((-(z + q))⁻¹ * (-(z + q'))⁻¹ - m₀ ^ 2)‖ := by congr 1; ring
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add h1 h3) |>.trans_eq (by ring)


omit [DecidableEq ι] in
/-- Resolvent identity `S(w) - S(w') = (w - w') ⟨(c - w)⁻¹ (c - w')⁻¹⟩` for `Im w, Im w' > 0`. -/
private lemma deformed_S_sub (c : ι → ℝ) {w w' : ℂ} (hw : 0 < w.im) (hw' : 0 < w'.im) :
    deformed_S c w - deformed_S c w' = (w - w') * deformed_P c w w' := by
  unfold deformed_S deformed_P
  have key : ∑ k, (((c k : ℂ) - w)⁻¹ - ((c k : ℂ) - w')⁻¹) =
      (w - w') * ∑ k, ((c k : ℂ) - w)⁻¹ * ((c k : ℂ) - w')⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 := deformed_ne (c k) hw
    have h2 := deformed_ne (c k) hw'
    rw [inv_sub_inv' h1 h2]
    ring
  rw [← mul_sub, ← Finset.sum_sub_distrib, key]
  ring

/-- Banach fixed-point theorem on a closed ball of `ℂ`. -/
private lemma deformed_exists_fixedPoint_ball {f : ℂ → ℂ} {m₀ : ℂ} {ρ K : ℝ} (hρ : 0 ≤ ρ)
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
/-- Contraction for the Newton-type map `q ↦ q - a (q - S(z + q))`, `a = (1 - m₀²)⁻¹`, on a ball
around the model root `m₀ = (-(z + m₀))⁻¹`: a root of `q = S(z + q)` within `ρ` of `m₀`
(Appendix A.16 [app:deformed-dyson], proof of Lemma A.21 [da:lem:deformed]). -/
private lemma deformed_exists_root [Nonempty ι] (c : ι → ℝ) {ε τ ρ γ : ℝ} {z m₀ : ℂ}
    (hε : 0 ≤ ε) (hτ : 0 < τ) (hρ : 0 ≤ ρ) (hρτ : ρ ≤ τ) (hz : 0 < z.im)
    (hm₀ : m₀ = (-(z + m₀))⁻¹) (hm₀im : 2 * τ ≤ m₀.im) (hγ : 0 < γ) (hgap : γ ≤ ‖1 - m₀ ^ 2‖)
    (hcount : ((Finset.univ.filter fun k => ε < |c k|).card : ℝ) ≤ ε * Fintype.card ι)
    (hL : γ⁻¹ * (2 * ε / τ ^ 3 + ε * (2 / τ ^ 2) + 2 * ρ / τ ^ 3) ≤ 1 / 2)
    (hM : γ⁻¹ * (ε / τ ^ 2 + ε * (2 / τ)) ≤ ρ / 2) :
    ∃ q, ‖q - m₀‖ ≤ ρ ∧ q = deformed_S c (z + q) := by
  have h1g : (1 : ℂ) - m₀ ^ 2 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hgap
    linarith
  set a : ℂ := (1 - m₀ ^ 2)⁻¹ with ha
  have ha1 : a * (1 - m₀ ^ 2) = 1 := inv_mul_cancel₀ h1g
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_mul] at ha1
    exact zero_ne_one ha1
  have hanorm : ‖a‖ ≤ γ⁻¹ := by
    rw [ha, norm_inv]
    exact inv_anti₀ hγ hgap
  have hball : ∀ q : ℂ, ‖q - m₀‖ ≤ ρ → τ ≤ (z + q).im := by
    intro q hq
    have h1 := (abs_le.mp ((Complex.abs_im_le_norm (q - m₀)).trans hq)).1
    rw [Complex.sub_im] at h1
    rw [Complex.add_im]
    linarith
  have hw₀ : τ ≤ (z + m₀).im := by
    rw [Complex.add_im]; linarith
  set T : ℂ → ℂ := fun q => q - a * (q - deformed_S c (z + q)) with hT
  have hlip : ∀ q q', ‖q - m₀‖ ≤ ρ → ‖q' - m₀‖ ≤ ρ → ‖T q - T q'‖ ≤ (1 / 2) * ‖q - q'‖ := by
    intro q q' hq hq'
    have hwq := hball q hq
    have hwq' := hball q' hq'
    have hS := deformed_S_sub c (w := z + q) (w' := z + q') (by linarith) (by linarith)
    simp only [add_sub_add_left_eq_sub] at hS
    have hdiff : T q - T q' = (q - q') * a * (deformed_P c (z + q) (z + q') - m₀ ^ 2) := by
      simp only [hT]
      linear_combination (-(q - q')) * ha1 + a * hS
    have hPb := deformed_P_sub_sq c hε hτ hm₀ hw₀ hwq hwq' hq hq' hcount
    rw [hdiff, norm_mul, norm_mul]
    calc ‖q - q'‖ * ‖a‖ * ‖deformed_P c (z + q) (z + q') - m₀ ^ 2‖
        ≤ ‖q - q'‖ * γ⁻¹ * (2 * ε / τ ^ 3 + ε * (2 / τ ^ 2) + 2 * ρ / τ ^ 3) := by gcongr
      _ = (γ⁻¹ * (2 * ε / τ ^ 3 + ε * (2 / τ ^ 2) + 2 * ρ / τ ^ 3)) * ‖q - q'‖ := by ring
      _ ≤ (1 / 2) * ‖q - q'‖ := by gcongr
  have hself : ‖T m₀ - m₀‖ ≤ ρ / 2 := by
    have hTm : T m₀ - m₀ = a * (deformed_S c (z + m₀) - (-(z + m₀))⁻¹) := by
      simp only [hT]
      rw [← hm₀]
      ring
    rw [hTm, norm_mul]
    have hSc := deformed_S_close c hε hτ hw₀ hcount
    calc ‖a‖ * ‖deformed_S c (z + m₀) - (-(z + m₀))⁻¹‖
        ≤ γ⁻¹ * (ε / τ ^ 2 + ε * (2 / τ)) := by gcongr
      _ ≤ ρ / 2 := hM
  obtain ⟨q, hq, hfq⟩ := deformed_exists_fixedPoint_ball (f := T) (m₀ := m₀) (ρ := ρ)
    (K := 1 / 2) hρ (by norm_num) (by norm_num)
    (fun q hq => by
      have h1 := hlip q m₀ hq (by simp [hρ])
      calc ‖T q - m₀‖ ≤ ‖T q - T m₀‖ + ‖T m₀ - m₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ρ := by
          have : ‖q - m₀‖ ≤ ρ := hq
          nlinarith [norm_nonneg (q - m₀)])
    hlip
  refine ⟨q, hq, ?_⟩
  have h : a * (q - deformed_S c (z + q)) = 0 := by
    have : T q = q := hfq
    simp only [hT] at this
    linear_combination -this
  have := (mul_eq_zero.mp h).resolve_left ha0
  exact sub_eq_zero.mp this


/-- The semicircle root `m_sc = m_B(0)` on one coordinate solves `m = -(z + m)⁻¹`. -/
private lemma deformed_msc_eq {z : ℂ} (hz : 0 < z.im) : msc z = (-(z + msc z))⁻¹ := by
  have hB : (0 : Matrix (Fin 1) (Fin 1) ℂ).IsHermitian := Matrix.isHermitian_zero
  have hm := isDeformedRoot_mB hB hz
  have hw : (z + mB (0 : Matrix (Fin 1) (Fin 1) ℂ) z).im ≠ 0 := by
    have := hm.1
    rw [Complex.add_im]
    linarith
  have h := hm.2
  rw [deformed_deformedMap_eq hB hw] at h
  have hlam : ∀ k : Fin 1, hB.neg.eigenvalues k = 0 := by
    intro k
    have h1 := hB.neg.trace_eq_sum_eigenvalues
    rw [Fin.sum_univ_one] at h1
    have h0 : (-(0 : Matrix (Fin 1) (Fin 1) ℂ)).trace = 0 := by simp
    rw [h0] at h1
    have h3 : ((hB.neg.eigenvalues 0 : ℝ) : ℂ) = 0 := by simpa using h1.symm
    rw [Subsingleton.elim k 0]
    exact Complex.ofReal_eq_zero.mp h3
  have h2 : deformed_S (fun k => hB.neg.eigenvalues k) (z + mB (0 : Matrix (Fin 1) (Fin 1) ℂ) z) =
      (-(z + mB (0 : Matrix (Fin 1) (Fin 1) ℂ) z))⁻¹ := by
    unfold deformed_S
    simp only [Fin.sum_univ_one, hlam]
    simp
  exact h.trans h2

/-- The count of eigenvalues of `-B` outside `[-ε, ε]` is at most `ε n` on the class. -/
private lemma deformed_count {B : Matrix ι ι ℂ} {ε : ℝ} (hB : B.IsHermitian)
    (h : DeformClass ε B) :
    ((Finset.univ.filter fun k => ε < |hB.neg.eigenvalues k|).card : ℝ) ≤
      ε * Fintype.card ι := by
  obtain ⟨-, Bs, Bb, hsum, hs, hr⟩ := h
  have h1 := countIn_abs_gt_le_rank hB.neg (Bs := -Bs) (Bb := -Bb) (ε := ε)
    (by rw [hsum]; abel) (by rwa [norm_neg])
  have h2 : (-Bb).rank ≤ Bb.rank := by
    have : -Bb = (-1 : Matrix ι ι ℂ) * Bb := by simp
    rw [this]
    exact Matrix.rank_mul_le_right _ _
  have hc : countIn (-B) {x | ε < |x|} =
      (Finset.univ.filter fun k => ε < |hB.neg.eigenvalues k|).card := by
    simp [countIn, hB.neg]
  rw [hc] at h1
  calc ((Finset.univ.filter fun k => ε < |hB.neg.eigenvalues k|).card : ℝ)
      ≤ (Bb.rank : ℝ) := by exact_mod_cast h1.trans h2
    _ ≤ ε * Fintype.card ι := hr

/-- The constants of the contraction argument close for `ε ≤ c⁷/2048`. -/
private lemma deformed_arith {c ε : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hε : 0 ≤ ε)
    (hε₀ : ε ≤ c ^ 7 / 2048) :
    c⁻¹ * (2 * ε / (c / 2) ^ 3 + ε * (2 / (c / 2) ^ 2) + 2 * (c ^ 4 / 64) / (c / 2) ^ 3) ≤ 1 / 3 ∧
    c⁻¹ * (ε / (c / 2) ^ 2 + ε * (2 / (c / 2))) ≤ (c ^ 4 / 64) / 2 := by
  obtain ⟨t, ht0, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ t ≤ 1 / 2048 ∧ ε = c ^ 7 * t :=
    ⟨ε / c ^ 7, by positivity, by rw [div_le_iff₀ (by positivity)]; linarith, by field_simp⟩
  have c3 : c ^ 3 ≤ 1 := pow_le_one₀ hc.le hc1
  have c4 : c ^ 4 ≤ 1 := pow_le_one₀ hc.le hc1
  have c4' : 0 ≤ c ^ 4 := by positivity
  have c5 : c ^ 5 ≤ c ^ 4 := by
    have : c ^ 5 = c ^ 4 * c := by ring
    rw [this]; nlinarith
  constructor
  · have e : c⁻¹ * (2 * (c ^ 7 * t) / (c / 2) ^ 3 + c ^ 7 * t * (2 / (c / 2) ^ 2) +
        2 * (c ^ 4 / 64) / (c / 2) ^ 3) = 16 * c ^ 3 * t + 8 * c ^ 4 * t + 1 / 4 := by
      field_simp
      ring
    rw [e]
    nlinarith [mul_nonneg (pow_nonneg hc.le 3) ht0, mul_nonneg c4' ht0]
  · have e : c⁻¹ * (c ^ 7 * t / (c / 2) ^ 2 + c ^ 7 * t * (2 / (c / 2))) =
        4 * c ^ 4 * t + 4 * c ^ 5 * t := by
      field_simp
      ring
    rw [e]
    nlinarith [mul_nonneg c4' ht0, mul_nonneg (pow_nonneg hc.le 5) ht0]

/-- The perturbative bulk estimate of Lemma A.21 [da:lem:deformed]: for `ε ≤ ε₀` the root `m_B`
lies within `c⁴/64` of `m_sc`, which gives `Im m_B ≥ c/2`, `|m_B| < 1` and
`|1 - ⟨M_B²⟩| ≥ c/2`, as in (A.82) [da:eq:deformed-scalar-stability]. -/
private lemma deformed_key (κ₀ Cstar : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hC : 0 < Cstar) :
    ∃ ε₀ c : ℝ, 0 < ε₀ ∧ 0 < c ∧ c ≤ 1 ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (B : Matrix ι ι ℂ) (ε E η : ℝ),
        0 ≤ ε → ε ≤ ε₀ → DeformClass ε B → |E| ≤ 2 - κ₀ → 0 < η → η ≤ Cstar →
        c / 2 ≤ (mB B (E + η * Complex.I)).im ∧ ‖mB B (E + η * Complex.I)‖ < 1 ∧
          c / 2 ≤ ‖1 - ntr (MB B (E + η * Complex.I) * MB B (E + η * Complex.I))‖ := by
  obtain ⟨c₁, hc₁, hsc⟩ := semicircle_bounds κ₀ Cstar hκ₀ hκ₀' hC
  set c : ℝ := min c₁ 1 with hc
  have hc0 : 0 < c := lt_min hc₁ one_pos
  have hc1 : c ≤ 1 := min_le_right _ _
  have hcc₁ : c ≤ c₁ := min_le_left _ _
  refine ⟨c ^ 7 / 2048, c, by positivity, hc0, hc1, ?_⟩
  intro ι _ _ _ B ε E η hε hεε₀ hBc hE hη hηC
  have hherm : B.IsHermitian := hBc.1
  set z : ℂ := E + η * Complex.I with hzdef
  have hz : 0 < z.im := by simpa [hzdef] using hη
  obtain ⟨hm0im, hm0gap, -⟩ := hsc E η hE hη hηC
  set m₀ : ℂ := msc z with hm₀def
  have hm₀im : c ≤ m₀.im := hcc₁.trans hm0im
  have hm₀gap : c ≤ ‖1 - m₀ ^ 2‖ := hcc₁.trans hm0gap
  have hm₀ : m₀ = (-(z + m₀))⁻¹ := deformed_msc_eq hz
  have hcount := deformed_count hherm hBc
  obtain ⟨hA1, hA2⟩ := deformed_arith hc0 hc1 hε hεε₀
  have hρ0 : 0 ≤ c ^ 4 / 64 := by positivity
  have hc4 : c ^ 4 ≤ c := by
    have : c ^ 4 = c * c ^ 3 := by ring
    have h3 : c ^ 3 ≤ 1 := pow_le_one₀ hc0.le hc1
    rw [this]; nlinarith
  have hρτ : c ^ 4 / 64 ≤ c / 2 := by linarith
  obtain ⟨q, hq, hqfix⟩ := deformed_exists_root (fun k => hherm.neg.eigenvalues k) (ε := ε)
    (τ := c / 2) (ρ := c ^ 4 / 64) (γ := c) (z := z) (m₀ := m₀) hε (by positivity) hρ0 hρτ hz hm₀
    (by linarith) hc0 hm₀gap hcount (by linarith) hA2
  have hqim : c / 2 ≤ q.im := by
    have h1 := (abs_le.mp ((Complex.abs_im_le_norm (q - m₀)).trans hq)).1
    rw [Complex.sub_im] at h1
    linarith
  have hw : (z + q).im ≠ 0 := by
    rw [Complex.add_im]; linarith
  have hqroot : IsDeformedRoot B z q := by
    refine ⟨by linarith, ?_⟩
    rw [deformed_deformedMap_eq hherm hw]
    exact hqfix
  have hmeq : q = mB B z :=
    IsDeformedRoot.unique hherm hz hqroot (isDeformedRoot_mB hherm hz)
  rw [← hmeq]
  refine ⟨hqim, ?_, ?_⟩
  · exact IsDeformedRoot.norm_lt_one hherm hz hqroot
  · have hMB : MB B z = deformedMat B z q := by rw [hmeq]; rfl
    rw [hMB, deformed_ntr_deformedMat_mul_self hherm hw]
    have hw₀ : c / 2 ≤ (z + m₀).im := by
      rw [Complex.add_im]; linarith
    have hqw : c / 2 ≤ (z + q).im := by
      rw [Complex.add_im]; linarith
    have hP := deformed_P_sub_sq (fun k => hherm.neg.eigenvalues k) hε (by positivity : 0 < c / 2)
      hm₀ hw₀ hqw hqw hq hq hcount
    have hQ : 2 * ε / (c / 2) ^ 3 + ε * (2 / (c / 2) ^ 2) + 2 * (c ^ 4 / 64) / (c / 2) ^ 3 ≤
        c / 3 := by
      have := mul_le_mul_of_nonneg_left hA1 hc0.le
      rw [← mul_assoc, mul_inv_cancel₀ hc0.ne', one_mul] at this
      linarith
    have h1 := norm_sub_le_norm_sub_add_norm_sub (1 : ℂ)
      (deformed_P (fun k => hherm.neg.eigenvalues k) (z + q) (z + q)) (m₀ ^ 2)
    have h2 : ‖(1 : ℂ) - m₀ ^ 2‖ ≤
        ‖(1 : ℂ) - deformed_P (fun k => hherm.neg.eigenvalues k) (z + q) (z + q)‖ + c / 3 := by
      refine h1.trans ?_
      gcongr
      exact hP.trans hQ
    linarith


/-- The imaginary part of `(c - w)⁻¹` for real `c`. -/
private lemma deformed_inv_im (c' : ℝ) (w : ℂ) :
    (((c' : ℂ) - w)⁻¹).im = w.im / ((c' - w.re) ^ 2 + w.im ^ 2) := by
  rw [Complex.inv_im, Complex.normSq_apply]
  simp
  ring

/-- Two-sided comparison of `Im (x - w)⁻¹` with `(1 + x²)⁻¹`, for `|Re w| ≤ 3`,
`c/2 ≤ Im w ≤ Cs + 1`. -/
private lemma deformed_term {x a b c Cs C : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (ha : |a| ≤ 3)
    (hb : c / 2 ≤ b) (hb' : b ≤ Cs + 1) (hCs : 0 < Cs)
    (hC1 : 2 * (18 + (Cs + 1) ^ 2) / c ≤ C) (hC2 : 148 * (Cs + 1) / c ^ 2 ≤ C) :
    C⁻¹ * (1 + x ^ 2)⁻¹ ≤ b / ((x - a) ^ 2 + b ^ 2) ∧
      b / ((x - a) ^ 2 + b ^ 2) ≤ C * (1 + x ^ 2)⁻¹ := by
  have ha' := abs_le.mp ha
  have hb0 : 0 < b := by linarith
  have hx : 0 < 1 + x ^ 2 := by positivity
  have hD0 : 0 < (x - a) ^ 2 + b ^ 2 := by positivity
  have hK : 0 < 18 + (Cs + 1) ^ 2 := by positivity
  have hC0 : 0 < C := lt_of_lt_of_le (by positivity) hC1
  set D := (x - a) ^ 2 + b ^ 2 with hD
  have hDup : D ≤ (18 + (Cs + 1) ^ 2) * (1 + x ^ 2) := by
    have h1 : (x - a) ^ 2 ≤ 2 * x ^ 2 + 18 := by nlinarith [sq_nonneg (x + a)]
    have h2 : b ^ 2 ≤ (Cs + 1) ^ 2 := by nlinarith
    nlinarith [sq_nonneg x]
  have hDlo : c ^ 2 * (1 + x ^ 2) / 148 ≤ D := by
    have hb2 : c ^ 2 / 4 ≤ b ^ 2 := by nlinarith
    have hc2 : c ^ 2 ≤ 1 := by nlinarith
    rcases le_or_gt (|x|) 6 with hx6 | hx6
    · have : x ^ 2 ≤ 36 := by nlinarith [abs_nonneg x, sq_abs x]
      have : c ^ 2 * (1 + x ^ 2) / 148 ≤ c ^ 2 / 4 := by
        rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
        nlinarith [sq_nonneg c]
      nlinarith [sq_nonneg (x - a)]
    · have hxa : |x| / 2 ≤ |x - a| := by
        have := abs_sub_abs_le_abs_sub x a
        linarith
      have h4 : x ^ 2 / 4 ≤ (x - a) ^ 2 := by
        have : (|x| / 2) ^ 2 ≤ |x - a| ^ 2 := by gcongr
        rw [sq_abs] at this
        nlinarith [sq_abs x]
      have hx2 : 36 ≤ x ^ 2 := by nlinarith [sq_abs x]
      have : c ^ 2 * (1 + x ^ 2) / 148 ≤ x ^ 2 / 4 := by
        rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
        nlinarith [sq_nonneg c]
      nlinarith [sq_nonneg b]
  constructor
  · rw [← one_div, ← one_div, one_div_mul_one_div, div_le_div_iff₀ (by positivity) hD0]
    have h1 : 18 + (Cs + 1) ^ 2 ≤ C * b := by
      have : 2 * (18 + (Cs + 1) ^ 2) ≤ C * c := by
        rwa [div_le_iff₀ hc] at hC1
      nlinarith
    nlinarith
  · rw [← div_eq_mul_inv, div_le_div_iff₀ hD0 hx]
    have h1 : 148 * (Cs + 1) ≤ C * c ^ 2 := by
      rwa [div_le_iff₀ (by positivity)] at hC2
    nlinarith

/-- The form comparison of (A.81) [us:eq:deformed-profile] for a root `m` with `c/2 ≤ Im m` and
`|m| < 1`: in the eigenbasis of `-B`, `Im M_m` and `(1 + B²)⁻¹` are comparable term by term, hence
as quadratic forms. -/
private lemma deformed_forms {B : Matrix ι ι ℂ} (hB : B.IsHermitian) {z m : ℂ} {E η c Cs C : ℝ}
    (hz : z = E + η * Complex.I) (hE : |E| ≤ 2) (hη : 0 < η) (hηC : η ≤ Cs) (hCs : 0 < Cs)
    (hc : 0 < c) (hc1 : c ≤ 1) (hmim : c / 2 ≤ m.im) (hm1 : ‖m‖ < 1)
    (hC1 : 2 * (18 + (Cs + 1) ^ 2) / c ≤ C) (hC2 : 148 * (Cs + 1) / c ^ 2 ≤ C) (v : ι → ℂ) :
    C⁻¹ * (star v ⬝ᵥ ((1 + B * B)⁻¹ *ᵥ v)).re ≤ (star v ⬝ᵥ (deformedMat B z m *ᵥ v)).im ∧
      (star v ⬝ᵥ (deformedMat B z m *ᵥ v)).im ≤ C * (star v ⬝ᵥ ((1 + B * B)⁻¹ *ᵥ v)).re := by
  set w : ℂ := z + m with hw
  have hwre : w.re = E + m.re := by simp [hw, hz]
  have hwim : w.im = η + m.im := by simp [hw, hz]
  have hmre : |m.re| ≤ 1 := (Complex.abs_re_le_norm m).trans hm1.le
  have hmim1 : m.im ≤ 1 := (le_abs_self _).trans ((Complex.abs_im_le_norm m).trans hm1.le)
  have hare : |w.re| ≤ 3 := by
    rw [hwre]
    calc |E + m.re| ≤ |E| + |m.re| := abs_add_le _ _
      _ ≤ 3 := by linarith
  have hbl : c / 2 ≤ w.im := by rw [hwim]; linarith
  have hbu : w.im ≤ Cs + 1 := by rw [hwim]; linarith
  have hwne : w.im ≠ 0 := by linarith
  set U : Matrix ι ι ℂ := (hB.neg.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hMB := deformed_mat_eq_spec hB hwne z m hw.symm
  have hinv := deformed_inv_one_add_sq hB
  rw [hMB, hinv, deformed_form_spec, deformed_form_spec, Complex.im_sum, Complex.re_sum]
  simp only [Complex.re_ofReal_mul, Complex.ofReal_re, Complex.im_mul_ofReal, deformed_inv_im]
  have hn : ∀ k, 0 ≤ ‖(star U *ᵥ v) k‖ ^ 2 := fun k => by positivity
  have hT := fun k : ι => deformed_term (x := hB.neg.eigenvalues k) (a := w.re) (b := w.im)
    hc hc1 hare hbl hbu hCs hC1 hC2
  constructor
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    calc C⁻¹ * ((1 + hB.neg.eigenvalues k ^ 2)⁻¹ * ‖(star U *ᵥ v) k‖ ^ 2)
        = (C⁻¹ * (1 + hB.neg.eigenvalues k ^ 2)⁻¹) * ‖(star U *ᵥ v) k‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hT k).1 (hn k)
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    calc _ ≤ (C * (1 + hB.neg.eigenvalues k ^ 2)⁻¹) * ‖(star U *ᵥ v) k‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hT k).2 (hn k)
      _ = _ := by ring


end Helpers

/-- Lemma A.21 [da:lem:deformed], (A.81) [us:eq:deformed-profile]: for the class with small
`ε`, `Im m_B(E + iη) ≍ 1` and `Im M_B(E + iη) ≍ (I + B²)⁻¹` as quadratic forms, for
`|E| ≤ 2 - κ₀`, `0 < η ≤ Cstar`, with constants depending only on `κ₀, Cstar`. -/
theorem deformed_profile (κ₀ Cstar : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hC : 0 < Cstar) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 1 ≤ C ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (B : Matrix ι ι ℂ) (ε E η : ℝ),
        0 ≤ ε → ε ≤ ε₀ → DeformClass ε B → |E| ≤ 2 - κ₀ → 0 < η → η ≤ Cstar →
        C⁻¹ ≤ (mB B (E + η * Complex.I)).im ∧ (mB B (E + η * Complex.I)).im ≤ C ∧
        ∀ v : ι → ℂ,
          C⁻¹ * (star v ⬝ᵥ ((1 + B * B)⁻¹ *ᵥ v)).re ≤
              (star v ⬝ᵥ (MB B (E + η * Complex.I) *ᵥ v)).im ∧
            (star v ⬝ᵥ (MB B (E + η * Complex.I) *ᵥ v)).im ≤
              C * (star v ⬝ᵥ ((1 + B * B)⁻¹ *ᵥ v)).re := by
  obtain ⟨ε₀, c, hε₀, hc, hc1, h⟩ := deformed_key κ₀ Cstar hκ₀ hκ₀' hC
  have hpos : 0 ≤ 2 * (18 + (Cstar + 1) ^ 2) / c + 148 * (Cstar + 1) / c ^ 2 := by positivity
  refine ⟨ε₀, 2 * (18 + (Cstar + 1) ^ 2) / c + 148 * (Cstar + 1) / c ^ 2 + 1, hε₀,
    by linarith, ?_⟩
  intro ι _ _ _ B ε E η hε hεε₀ hBc hE hη hηC
  obtain ⟨hmim, hm1, -⟩ := h ι B ε E η hε hεε₀ hBc hE hη hηC
  set C : ℝ := 2 * (18 + (Cstar + 1) ^ 2) / c + 148 * (Cstar + 1) / c ^ 2 + 1 with hCdef
  have hC1 : 2 * (18 + (Cstar + 1) ^ 2) / c ≤ C := by
    have : 0 ≤ 148 * (Cstar + 1) / c ^ 2 := by positivity
    linarith
  have hC2 : 148 * (Cstar + 1) / c ^ 2 ≤ C := by
    have : 0 ≤ 2 * (18 + (Cstar + 1) ^ 2) / c := by positivity
    linarith
  have hC0 : 0 < C := by linarith
  have hE2 : |E| ≤ 2 := by linarith
  have hmim1 : (mB B (E + η * Complex.I)).im ≤ 1 :=
    (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans hm1.le)
  refine ⟨?_, ?_, fun v => ?_⟩
  · have h2 : (c / 2)⁻¹ ≤ C := by
      have : (c / 2)⁻¹ = 2 / c := by field_simp
      rw [this]
      have h3 : 2 / c ≤ 2 * (18 + (Cstar + 1) ^ 2) / c := by
        rw [div_le_div_iff_of_pos_right hc]
        nlinarith [sq_nonneg (Cstar + 1)]
      linarith
    exact (inv_le_comm₀ hC0 (by positivity)).mpr h2 |>.trans hmim
  · have : (1 : ℝ) ≤ C := by linarith
    linarith
  · exact deformed_forms (hBc.1) rfl hE2 hη hηC hC hc hc1 hmim hm1 hC1 hC2 v

/-- (A.82) [da:eq:deformed-scalar-stability]: `|m_B| ≤ 1` and the stability gap
`|1 - ⟨M_B²⟩| ≥ c` under the hypotheses of Lemma A.21 [da:lem:deformed]. -/
theorem deformed_scalar_stability (κ₀ Cstar : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hC : 0 < Cstar) :
    ∃ ε₀ c : ℝ, 0 < ε₀ ∧ 0 < c ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (B : Matrix ι ι ℂ) (ε E η : ℝ),
        0 ≤ ε → ε ≤ ε₀ → DeformClass ε B → |E| ≤ 2 - κ₀ → 0 < η → η ≤ Cstar →
        ‖mB B (E + η * Complex.I)‖ ≤ 1 ∧
          c ≤ ‖1 - ntr (MB B (E + η * Complex.I) * MB B (E + η * Complex.I))‖ := by
  obtain ⟨ε₀, c, hε₀, hc, hc1, h⟩ := deformed_key κ₀ Cstar hκ₀ hκ₀' hC
  refine ⟨ε₀, c / 2, hε₀, by positivity, ?_⟩
  intro ι _ _ _ B ε E η hε hεε₀ hBc hE hη hηC
  obtain ⟨-, hm1, hgap⟩ := h ι B ε E η hε hεε₀ hBc hE hη hηC
  exact ⟨hm1.le, hgap⟩


end LSBA
