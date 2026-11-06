import LSBA.Upper.RegularState
import LSBA.Spectral.DeformedRelLaw

/-!
# Expected spectral projections of a fresh deformed GUE matrix

(G.7) [us:eq:projexp] in Appendix G.3 [app:product-moment-proof]: for the fresh matrix
`Γ = V_a - E - g² R` with a regular state `R` (9.3) [us:eq:regular] fixed before block `a`,
`𝔼[1_{|Γ| ≤ t} | past] ≤ C W^{2δ} t` for `W^{-1-δ} ≤ t ≤ 1`. It is stated for a vector `u` and a
set `S` of pasts, both fixed before block `a`:
`𝔼[‖1_{|Γ| ≤ t} u‖² ; S] ≤ C W^{2δ} t 𝔼[‖u‖² ; S]`. For `t ≥ W^{-1+δ}` it follows from
`1_{|x| ≤ t} ≤ 2t Im (x - it)⁻¹` and the upper bound of the relative local law (G.2)
[us:eq:relative-local-law] for `B = g² R`; below that scale from monotonicity in `t`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `U diag(d) U*`. -/
private def projExp_conj {W : ℕ} (U : Matrix (Fin W) (Fin W) ℂ) (d : Fin W → ℂ) :
    Matrix (Fin W) (Fin W) ℂ :=
  U * Matrix.diagonal d * Uᴴ

/-- `U diag(d) U* · U diag(e) U* = U diag(d e) U*` for `U*U = 1`. -/
private lemma projExp_conj_mul {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ} (hU : Uᴴ * U = 1)
    (d e : Fin W → ℂ) :
    projExp_conj U d * projExp_conj U e = projExp_conj U (fun k => d k * e k) := by
  unfold projExp_conj
  calc U * Matrix.diagonal d * Uᴴ * (U * Matrix.diagonal e * Uᴴ)
      = U * Matrix.diagonal d * (Uᴴ * U) * Matrix.diagonal e * Uᴴ := by
        simp only [Matrix.mul_assoc]
    _ = U * Matrix.diagonal (fun k => d k * e k) * Uᴴ := by
        rw [hU, Matrix.mul_one, Matrix.mul_assoc U, Matrix.diagonal_mul_diagonal]

/-- `U diag(1) U* = 1` for `U U* = 1`. -/
private lemma projExp_conj_one {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ} (hU : U * Uᴴ = 1) :
    projExp_conj U (fun _ => 1) = 1 := by
  unfold projExp_conj
  have h : (Matrix.diagonal fun _ : Fin W => (1 : ℂ)) = 1 := Matrix.diagonal_one
  rw [h, Matrix.mul_one, hU]

/-- `U diag(c, …, c) U* = c · 1` for `U U* = 1`. -/
private lemma projExp_conj_const {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ} (hU : U * Uᴴ = 1)
    (c : ℂ) : projExp_conj U (fun _ => c) = c • (1 : Matrix (Fin W) (Fin W) ℂ) := by
  unfold projExp_conj
  rw [show (Matrix.diagonal fun _ : Fin W => c) = c • (1 : Matrix (Fin W) (Fin W) ℂ) by
    rw [← Matrix.diagonal_one, Matrix.smul_eq_diagonal_mul]
    simp]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU]

/-- `U diag(d) U* - U diag(e) U* = U diag(d - e) U*`. -/
private lemma projExp_conj_sub {W : ℕ} (U : Matrix (Fin W) (Fin W) ℂ) (d e : Fin W → ℂ) :
    projExp_conj U d - projExp_conj U e = projExp_conj U (fun k => d k - e k) := by
  unfold projExp_conj
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]

/-- `U diag(d) U* + U diag(e) U* = U diag(d + e) U*`. -/
private lemma projExp_conj_add {W : ℕ} (U : Matrix (Fin W) (Fin W) ℂ) (d e : Fin W → ℂ) :
    projExp_conj U d + projExp_conj U e = projExp_conj U (fun k => d k + e k) := by
  unfold projExp_conj
  rw [← Matrix.add_mul, ← Matrix.mul_add, Matrix.diagonal_add]

/-- `(U diag(d) U*)⁻¹ = U diag(d⁻¹) U*` for unitary `U` and nonzero `d`. -/
private lemma projExp_conj_inv {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ} (hU1 : Uᴴ * U = 1)
    (hU2 : U * Uᴴ = 1) {d : Fin W → ℂ} (hd : ∀ k, d k ≠ 0) :
    (projExp_conj U d)⁻¹ = projExp_conj U (fun k => (d k)⁻¹) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [projExp_conj_mul hU1]
  simp only [mul_inv_cancel₀ (hd _)]
  exact projExp_conj_one hU2

/-- `U diag(d) U* (U b) = U (d b)` for `U*U = 1`. -/
private lemma projExp_conj_mulVec {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ} (hU : Uᴴ * U = 1)
    (d b : Fin W → ℂ) :
    projExp_conj U d *ᵥ (U *ᵥ b) = U *ᵥ (fun k => d k * b k) := by
  unfold projExp_conj
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hU, Matrix.mul_one, ← Matrix.mulVec_mulVec]
  congr 1
  funext k
  exact Matrix.mulVec_diagonal d b k

/-- `(U a)* (U b) = a* b` for `U*U = 1`. -/
private lemma projExp_dot {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ} (hU : Uᴴ * U = 1)
    (a b : Fin W → ℂ) : star (U *ᵥ a) ⬝ᵥ (U *ᵥ b) = ∑ k, star (a k) * b k := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hU,
    Matrix.one_mulVec]
  rfl

/-- `‖U a‖² = Σ |a_k|²` for `U*U = 1`. -/
private lemma projExp_l2Norm_sq {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ} (hU : Uᴴ * U = 1)
    (a : Fin W → ℂ) : l2Norm (U *ᵥ a) ^ 2 = ∑ k, ‖a k‖ ^ 2 := by
  have h1 : l2Norm (U *ᵥ a) ^ 2 = ∑ i, ‖(U *ᵥ a) i‖ ^ 2 := by
    unfold l2Norm
    exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)
  have h2 : ∀ v : Fin W → ℂ, ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) = ∑ i, star (v i) * v i := fun v => by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  rw [h1]
  have h3 := projExp_dot hU a a
  have h4 : star (U *ᵥ a) ⬝ᵥ (U *ᵥ a) = ∑ i, star ((U *ᵥ a) i) * (U *ᵥ a) i := rfl
  rw [h4, ← h2, ← h2] at h3
  exact_mod_cast h3

/-- The spectral projection of a Hermitian matrix in its eigenvector basis. -/
private lemma projExp_specProj_eq {W : ℕ} {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian)
    (S : Set ℝ) :
    specProj A S = projExp_conj (hA.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)
      (fun k => if hA.eigenvalues k ∈ S then (1 : ℂ) else 0) := by
  unfold projExp_conj
  simp only [specProj, hA, ↓reduceDIte]
  ext i j
  rw [Finset.sum_filter, Matrix.sum_apply]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h : hA.eigenvalues c ∈ S <;> simp [h, Matrix.vecMulVec_apply, mul_comm]

/-- A Hermitian matrix in its eigenvector basis. -/
private lemma projExp_spectral {W : ℕ} {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian) :
    A = projExp_conj (hA.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)
      (fun k => (hA.eigenvalues k : ℂ)) := by
  have h := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  exact h

/-- Every vector is `U w` for unitary `U`. -/
private lemma projExp_coords {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ} (hU : U * Uᴴ = 1)
    (v : Fin W → ℂ) : ∃ w : Fin W → ℂ, v = U *ᵥ w :=
  ⟨Uᴴ *ᵥ v, by rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]⟩

/-- `z̄ (d z) = d |z|²`. -/
private lemma projExp_star_mul (d z : ℂ) :
    star z * (d * z) = d * ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  calc star z * (d * z) = d * (star z * z) := by ring
    _ = d * ((‖z‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.star_def, Complex.conj_mul']
        push_cast
        rfl

/-- The quadratic form of `U diag(d) U*` at `U w` is `Σ d_k |w_k|²`. -/
private lemma projExp_quad {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ} (hU : Uᴴ * U = 1)
    (d w : Fin W → ℂ) :
    star (U *ᵥ w) ⬝ᵥ (projExp_conj U d *ᵥ (U *ᵥ w)) = ∑ k, d k * ((‖w k‖ ^ 2 : ℝ) : ℂ) := by
  rw [projExp_conj_mulVec hU, projExp_dot hU]
  exact Finset.sum_congr rfl fun k _ => projExp_star_mul (d k) (w k)

/-- `Im (μ - i η)⁻¹ |z|² = |z|² η / (μ² + η²)` for real `μ`, `η`. -/
private lemma projExp_im_term (μ η : ℝ) (z : ℂ) :
    ((((μ : ℂ) - (η : ℂ) * Complex.I)⁻¹) * ((‖z‖ ^ 2 : ℝ) : ℂ)).im =
      ‖z‖ ^ 2 * (η / (μ ^ 2 + η ^ 2)) := by
  rw [Complex.im_mul_ofReal, Complex.inv_im, Complex.normSq_apply]
  simp
  ring

/-- For Hermitian `Γ`, `u` and `0 < η`, `t ≤ η`:
`‖1_{[-t,t]}(Γ) u‖² ≤ ‖u‖²` and `‖1_{[-t,t]}(Γ) u‖² ≤ 2 η Im u* (Γ - i η)⁻¹ u`. -/
private lemma projExp_form {W : ℕ} {Γ : Matrix (Fin W) (Fin W) ℂ} (hΓ : Γ.IsHermitian)
    (u : Fin W → ℂ) {η t : ℝ} (hη : 0 < η) (ht : t ≤ η) :
    l2Norm (specProj Γ (Set.Icc (-t) t) *ᵥ u) ^ 2 ≤ l2Norm u ^ 2 ∧
      l2Norm (specProj Γ (Set.Icc (-t) t) *ᵥ u) ^ 2 ≤ 2 * η *
        (star u ⬝ᵥ ((Γ - ((η : ℂ) * Complex.I) • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹ *ᵥ u)).im := by
  obtain ⟨U, hUdef⟩ : ∃ U : Matrix (Fin W) (Fin W) ℂ,
      U = (hΓ.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ) := ⟨_, rfl⟩
  have hU1 : Uᴴ * U = 1 := by
    rw [hUdef]; exact Matrix.mem_unitaryGroup_iff'.mp hΓ.eigenvectorUnitary.2
  have hU2 : U * Uᴴ = 1 := by
    rw [hUdef]; exact Matrix.mem_unitaryGroup_iff.mp hΓ.eigenvectorUnitary.2
  obtain ⟨w, rfl⟩ := projExp_coords hU2 u
  set μ : Fin W → ℝ := hΓ.eigenvalues with hμ
  have hres : (Γ - ((η : ℂ) * Complex.I) • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹ =
      projExp_conj U (fun k => ((μ k : ℂ) - (η : ℂ) * Complex.I)⁻¹) := by
    have hsub : Γ - ((η : ℂ) * Complex.I) • (1 : Matrix (Fin W) (Fin W) ℂ) =
        projExp_conj U (fun k => (μ k : ℂ) - (η : ℂ) * Complex.I) := by
      rw [← projExp_conj_sub, ← projExp_conj_const hU2, hUdef, ← projExp_spectral hΓ]
    rw [hsub]
    refine projExp_conj_inv hU1 hU2 fun k => ?_
    intro h0
    exact hη.ne' (by simpa using congrArg Complex.im h0)
  have hP : specProj Γ (Set.Icc (-t) t) *ᵥ (U *ᵥ w) =
      U *ᵥ (fun k => (if μ k ∈ Set.Icc (-t) t then (1 : ℂ) else 0) * w k) := by
    rw [projExp_specProj_eq hΓ, ← hUdef, projExp_conj_mulVec hU1]
    congr 1
    funext k
    by_cases h : hΓ.eigenvalues k ∈ Set.Icc (-t) t <;> simp [h, hμ]
  have hPn : l2Norm (specProj Γ (Set.Icc (-t) t) *ᵥ (U *ᵥ w)) ^ 2 =
      ∑ k, if μ k ∈ Set.Icc (-t) t then ‖w k‖ ^ 2 else 0 := by
    rw [hP, projExp_l2Norm_sq hU1]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : μ k ∈ Set.Icc (-t) t <;> simp [h]
  have hun : l2Norm (U *ᵥ w) ^ 2 = ∑ k, ‖w k‖ ^ 2 := projExp_l2Norm_sq hU1 w
  have hIm : (star (U *ᵥ w) ⬝ᵥ
      ((Γ - ((η : ℂ) * Complex.I) • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹ *ᵥ (U *ᵥ w))).im =
      ∑ k, ‖w k‖ ^ 2 * (η / (μ k ^ 2 + η ^ 2)) := by
    rw [hres, projExp_quad hU1, Complex.im_sum]
    exact Finset.sum_congr rfl fun k _ => projExp_im_term (μ k) η (w k)
  rw [hPn, hun, hIm, Finset.mul_sum]
  refine ⟨Finset.sum_le_sum fun k _ => ?_, Finset.sum_le_sum fun k _ => ?_⟩
  · split_ifs <;> first | exact le_rfl | positivity
  · by_cases h : μ k ∈ Set.Icc (-t) t
    · simp only [h, ↓reduceIte]
      have h1 : μ k ^ 2 ≤ η ^ 2 := by
        have hm1 : μ k ≤ η := h.2.trans ht
        have hm2 : -η ≤ μ k := by linarith [h.1]
        nlinarith
      have h2 : 0 < μ k ^ 2 + η ^ 2 := by positivity
      have h3 : 1 ≤ 2 * η * (η / (μ k ^ 2 + η ^ 2)) := by
        rw [← mul_div_assoc, le_div_iff₀ h2]
        nlinarith
      calc ‖w k‖ ^ 2 = ‖w k‖ ^ 2 * 1 := (mul_one _).symm
        _ ≤ ‖w k‖ ^ 2 * (2 * η * (η / (μ k ^ 2 + η ^ 2))) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = 2 * η * (‖w k‖ ^ 2 * (η / (μ k ^ 2 + η ^ 2))) := by ring
    · simp only [h, ↓reduceIte]
      positivity

/-- `Re v* (1 + B²)⁻¹ v ≤ ‖v‖²` for Hermitian `B`. -/
private lemma projExp_inv_le {W : ℕ} {B : Matrix (Fin W) (Fin W) ℂ} (hB : B.IsHermitian)
    (v : Fin W → ℂ) : (star v ⬝ᵥ ((1 + B * B)⁻¹ *ᵥ v)).re ≤ l2Norm v ^ 2 := by
  obtain ⟨U, hUdef⟩ : ∃ U : Matrix (Fin W) (Fin W) ℂ,
      U = (hB.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ) := ⟨_, rfl⟩
  have hU1 : Uᴴ * U = 1 := by
    rw [hUdef]; exact Matrix.mem_unitaryGroup_iff'.mp hB.eigenvectorUnitary.2
  have hU2 : U * Uᴴ = 1 := by
    rw [hUdef]; exact Matrix.mem_unitaryGroup_iff.mp hB.eigenvectorUnitary.2
  obtain ⟨w, rfl⟩ := projExp_coords hU2 v
  have hBs : B = projExp_conj U (fun k => (hB.eigenvalues k : ℂ)) := by
    rw [hUdef]; exact projExp_spectral hB
  have hnz : ∀ k, 1 + (hB.eigenvalues k : ℂ) * (hB.eigenvalues k : ℂ) ≠ 0 := fun k => by
    have : 1 + (hB.eigenvalues k : ℂ) * (hB.eigenvalues k : ℂ) =
        ((1 + hB.eigenvalues k ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hinv : (1 + B * B)⁻¹ = projExp_conj U
      (fun k => (1 + (hB.eigenvalues k : ℂ) * (hB.eigenvalues k : ℂ))⁻¹) := by
    have h1 : 1 + B * B = projExp_conj U
        (fun k => 1 + (hB.eigenvalues k : ℂ) * (hB.eigenvalues k : ℂ)) := by
      rw [← projExp_conj_add, ← projExp_conj_mul hU1, ← hBs, projExp_conj_one hU2]
    rw [h1]
    exact projExp_conj_inv hU1 hU2 hnz
  rw [hinv, projExp_quad hU1, Complex.re_sum, projExp_l2Norm_sq hU1]
  refine Finset.sum_le_sum fun k _ => ?_
  have e : (1 + (hB.eigenvalues k : ℂ) * (hB.eigenvalues k : ℂ))⁻¹ * ((‖w k‖ ^ 2 : ℝ) : ℂ) =
      (((1 + hB.eigenvalues k ^ 2)⁻¹ * ‖w k‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring_nf
  rw [e, Complex.ofReal_re]
  have h1 : (1 + hB.eigenvalues k ^ 2)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (hB.eigenvalues k)])
  exact mul_le_of_le_one_left (by positivity) h1

/-- The deformation class of Lemma G.1 [us:lem:local-law] is increasing in `ε`. -/
private lemma projExp_deformClass_mono {W : ℕ} {ε ε' : ℝ} {B : Matrix (Fin W) (Fin W) ℂ}
    (h : DeformClass ε B) (hε : ε ≤ ε') : DeformClass ε' B := by
  obtain ⟨hH, Bs, Bb, hsum, hs, hb⟩ := h
  exact ⟨hH, Bs, Bb, hsum, hs.trans hε,
    hb.trans (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _))⟩

/-- `v ↦ ‖v‖₂` is continuous. -/
private lemma projExp_continuous_l2Norm {ι : Type*} [Fintype ι] :
    Continuous fun v : ι → ℂ => l2Norm v := by
  unfold l2Norm
  fun_prop

/-- `p ↦ M p *ᵥ w p` is measurable for measurable `M` and `w`. -/
private lemma projExp_measurable_mulVec {W : ℕ} {α : Type*} [MeasurableSpace α]
    {M : α → Matrix (Fin W) (Fin W) ℂ} {w : α → Fin W → ℂ} (hM : Measurable M)
    (hw : Measurable w) : Measurable fun p => M p *ᵥ w p := by
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.measurable_sum _ fun j _ =>
    (measurable_pi_iff.mp (measurable_pi_iff.mp hM i) j).mul (measurable_pi_iff.mp hw j)

/-- The sample that is `ρ` on the blocks other than `a` and `0` on block `a`. -/
private def projExp_ext (W L : ℕ) (a : Fin L)
    (ρ : {x : Fin L × Fin W × Fin W // x.1 ≠ a} → ℝ) : Ω W L :=
  fun x => if h : x.1 ≠ a then ρ ⟨x, h⟩ else 0

private lemma projExp_measurable_ext (W L : ℕ) (a : Fin L) :
    Measurable (projExp_ext W L a) := by
  refine measurable_pi_iff.mpr fun x => ?_
  unfold projExp_ext
  by_cases h : x.1 = a
  · simp only [ne_eq, h, not_true_eq_false, ↓reduceDIte]
    exact measurable_const
  · simp only [ne_eq, h, not_false_eq_true, ↓reduceDIte]
    exact measurable_pi_apply _

private lemma projExp_ext_split (W L : ℕ) (a : Fin L) (ω : Ω W L) (x : Fin L × Fin W × Fin W)
    (hx : x.1 ≠ a) : projExp_ext W L a (blockSplit W L a ω).2 x = ω x := by
  simp [projExp_ext, blockSplit, hx]

/-- Fibre bound for the `W × W` GUE matrix `V` at a fixed Hermitian `R` and vector `v`: if the
upper bound `Im v* G v ≤ C_L Re v* (1 + B²)⁻¹ v` of the relative local law (G.2)
[us:eq:relative-local-law] for `B = g² R` at spectral parameter `E + iη` fails with probability
at most `p`, then for `t ≤ η`
`𝔼‖1_{[-t,t]}(V - E - g² R) v‖² ≤ (2 C_L η + p) ‖v‖²`. -/
private lemma projExp_fibre {W : ℕ} {CL g E t η p : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    {v : Fin W → ℂ} (hCL : 0 ≤ CL) (hη : 0 < η) (htη : t ≤ η) (hp : 0 ≤ p)
    (hR : R.IsHermitian)
    (hlaw : μ W 1 {ω | ¬ (star v ⬝ᵥ (resolventMat (gueMat W ω - ((g : ℂ) ^ 2) • R)
        ((E : ℂ) + (η : ℂ) * Complex.I) *ᵥ v)).im ≤
          CL * (star v ⬝ᵥ ((1 + (((g : ℂ) ^ 2) • R) * (((g : ℂ) ^ 2) • R))⁻¹ *ᵥ v)).re} ≤
        ENNReal.ofReal p) :
    ∫⁻ ω, ENNReal.ofReal (l2Norm (specProj (gueMat W ω - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R)
        (Set.Icc (-t) t) *ᵥ v) ^ 2) ∂(μ W 1) ≤
      ENNReal.ofReal ((2 * CL * η + p) * l2Norm v ^ 2) := by
  have hk : IsSelfAdjoint ((g : ℂ) ^ 2) := by rw [isSelfAdjoint_iff]; simp
  have hBH : (((g : ℂ) ^ 2) • R).IsHermitian := hR.smul hk
  set Bad : Set (Ω W 1) := {ω | ¬ (star v ⬝ᵥ (resolventMat (gueMat W ω - ((g : ℂ) ^ 2) • R)
        ((E : ℂ) + (η : ℂ) * Complex.I) *ᵥ v)).im ≤
          CL * (star v ⬝ᵥ ((1 + (((g : ℂ) ^ 2) • R) * (((g : ℂ) ^ 2) • R))⁻¹ *ᵥ v)).re}
    with hBad
  have hpt : ∀ ω : Ω W 1, ENNReal.ofReal (l2Norm (specProj (gueMat W ω - (E : ℂ) • 1 -
        ((g : ℂ) ^ 2) • R) (Set.Icc (-t) t) *ᵥ v) ^ 2) ≤
      ENNReal.ofReal (2 * CL * η * l2Norm v ^ 2) +
        Bad.indicator (fun _ => ENNReal.ofReal (l2Norm v ^ 2)) ω := by
    intro ω
    by_cases hΓ : (gueMat W ω - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R).IsHermitian
    · obtain ⟨h1, h2⟩ := projExp_form hΓ v hη htη
      by_cases hω : ω ∈ Bad
      · rw [Set.indicator_of_mem hω]
        exact (ENNReal.ofReal_le_ofReal h1).trans le_add_self
      · rw [Set.indicator_of_notMem hω, add_zero]
        refine ENNReal.ofReal_le_ofReal (h2.trans ?_)
        have hres : (gueMat W ω - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R -
            ((η : ℂ) * Complex.I) • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹ =
            resolventMat (gueMat W ω - ((g : ℂ) ^ 2) • R) ((E : ℂ) + (η : ℂ) * Complex.I) := by
          unfold resolventMat
          congr 1
          rw [add_smul]
          abel
        rw [hres]
        have hle : (star v ⬝ᵥ (resolventMat (gueMat W ω - ((g : ℂ) ^ 2) • R)
            ((E : ℂ) + (η : ℂ) * Complex.I) *ᵥ v)).im ≤
            CL * (star v ⬝ᵥ ((1 + (((g : ℂ) ^ 2) • R) * (((g : ℂ) ^ 2) • R))⁻¹ *ᵥ v)).re :=
          not_not.mp hω
        calc 2 * η * _ ≤ 2 * η * (CL * l2Norm v ^ 2) := by
              gcongr
              exact hle.trans (mul_le_mul_of_nonneg_left (projExp_inv_le hBH v) hCL)
          _ = 2 * CL * η * l2Norm v ^ 2 := by ring
    · have h0 : specProj (gueMat W ω - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R) (Set.Icc (-t) t) = 0 := by
        simp only [specProj, hΓ, ↓reduceDIte]
      rw [h0, Matrix.zero_mulVec]
      have : l2Norm (0 : Fin W → ℂ) = 0 := by simp [l2Norm]
      rw [this]
      simp
  calc ∫⁻ ω, ENNReal.ofReal (l2Norm (specProj (gueMat W ω - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R)
          (Set.Icc (-t) t) *ᵥ v) ^ 2) ∂(μ W 1)
      ≤ ∫⁻ ω, (ENNReal.ofReal (2 * CL * η * l2Norm v ^ 2) +
          Bad.indicator (fun _ => ENNReal.ofReal (l2Norm v ^ 2)) ω) ∂(μ W 1) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (2 * CL * η * l2Norm v ^ 2) +
          ∫⁻ ω, Bad.indicator (fun _ => ENNReal.ofReal (l2Norm v ^ 2)) ω ∂(μ W 1) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (2 * CL * η * l2Norm v ^ 2) +
          ENNReal.ofReal (l2Norm v ^ 2) * ENNReal.ofReal p :=
        add_le_add le_rfl ((lintegral_indicator_const_le Bad _).trans
          (mul_le_mul' le_rfl hlaw))
    _ = ENNReal.ofReal ((2 * CL * η + p) * l2Norm v ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add
          (by have := sq_nonneg (l2Norm v); positivity) (by positivity)]
        congr 1
        ring

/-- (G.7) [us:eq:projexp], vector form at a fresh block: for `0 < g ≤ g₀`, `|E| ≤ 2 - κ₀`,
`W^{-1-δ} ≤ t ≤ 1`, a state `R` regular on `S` and a vector `u`, both fixed before block `a`,
`𝔼[‖1_{[-t,t]}(V_a - E - g² R) u‖² ; S] ≤ C W^{2δ} t 𝔼[‖u‖² ; S]`. -/
theorem projexp_fresh (κ₀ : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) :
    ∃ g₀ C : ℝ, 0 < g₀ ∧ 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ W₀ : ℕ,
      ∀ (W L : ℕ) (a : Fin L), W₀ ≤ W → ∀ g E t : ℝ, 0 < g → g ≤ g₀ → |E| ≤ 2 - κ₀ →
      (W : ℝ) ^ (-1 - δ) ≤ t → t ≤ 1 →
      ∀ (Rp : Ω W L → Matrix (Fin W) (Fin W) ℂ) (u : Ω W L → Fin W → ℂ) (S : Set (Ω W L)),
        Measurable Rp → OffBlock W L a Rp → Measurable u → OffBlock W L a u →
        MeasurableSet S → OffBlock W L a (· ∈ S) → (∀ ω ∈ S, IsRegularState W g (Rp ω)) →
        ∫⁻ ω in S, ENNReal.ofReal (l2Norm (specProj (gueBlock W L ω a - (E : ℂ) • 1 -
            ((g : ℂ) ^ 2) • Rp ω) (Set.Icc (-t) t) *ᵥ u ω) ^ 2) ∂(μ W L) ≤
          ENNReal.ofReal (C * (W : ℝ) ^ (2 * δ) * t) *
            ∫⁻ ω in S, ENNReal.ofReal (l2Norm (u ω) ^ 2) ∂(μ W L) := by
  obtain ⟨ε₀, CL, hε₀, hCL, hlaw⟩ := localLaw_rel κ₀ 1 hκ₀ hκ₀' one_pos
  have hCL0 : 0 ≤ CL := by linarith
  refine ⟨min 1 (ε₀ ^ 2), 2 * CL + 1, lt_min one_pos (by positivity), by linarith, ?_⟩
  intro δ hδ hδ1
  obtain ⟨n₀, hn₀⟩ := hlaw ε₀ δ 1 1 hε₀ le_rfl hδ one_pos one_pos
  refine ⟨max n₀ 1, ?_⟩
  intro W L a hW g E t hg hgg₀ hE hlow ht1 Rp u S hRp hRpa hu hua hS hSa hreg
  have hWn : n₀ ≤ W := (le_max_left _ _).trans hW
  have hW1 : 1 ≤ W := (le_max_right _ _).trans hW
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < W := by linarith
  have hg1 : g ≤ 1 := hgg₀.trans (min_le_left _ _)
  have hgε : Real.sqrt g ≤ ε₀ :=
    Real.sqrt_le_iff.mpr ⟨hε₀.le, hgg₀.trans (min_le_right _ _)⟩
  have ht0 : 0 ≤ t := (Real.rpow_pos_of_pos hWpos _).le.trans hlow
  -- the spectral scale `η = max {t, W^{-1+δ}}` and the closing of the powers of `W`
  set η : ℝ := max t ((W : ℝ) ^ (-1 + δ)) with hη
  have hη0 : 0 < η :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) (le_max_right _ _)
  have htη : t ≤ η := le_max_left _ _
  have hηlow : (W : ℝ) ^ (-1 + δ) ≤ η := le_max_right _ _
  have hη1 : η ≤ 1 :=
    max_le ht1 (Real.rpow_le_one_of_one_le_of_nonpos hWr (by linarith))
  have hM1 : t ≤ (W : ℝ) ^ (2 * δ) * t :=
    le_mul_of_one_le_left ht0 (Real.one_le_rpow hWr (by linarith))
  have hM2 : (W : ℝ) ^ (-1 + δ) ≤ (W : ℝ) ^ (2 * δ) * t := by
    calc (W : ℝ) ^ (-1 + δ) = (W : ℝ) ^ (2 * δ) * (W : ℝ) ^ (-1 - δ) := by
          rw [← Real.rpow_add hWpos]
          congr 1
          ring
      _ ≤ (W : ℝ) ^ (2 * δ) * t := mul_le_mul_of_nonneg_left hlow (by positivity)
  have hp1 : (W : ℝ) ^ (-(1 : ℝ)) ≤ (W : ℝ) ^ (-1 + δ) :=
    Real.rpow_le_rpow_of_exponent_le hWr (by linarith)
  have hp0 : 0 ≤ (W : ℝ) ^ (-(1 : ℝ)) := (Real.rpow_pos_of_pos hWpos _).le
  have hnum : 2 * CL * η + (W : ℝ) ^ (-(1 : ℝ)) ≤ (2 * CL + 1) * (W : ℝ) ^ (2 * δ) * t := by
    have h1 : η ≤ (W : ℝ) ^ (2 * δ) * t := max_le hM1 hM2
    have h2 : (W : ℝ) ^ (-(1 : ℝ)) ≤ (W : ℝ) ^ (2 * δ) * t := hp1.trans hM2
    nlinarith
  -- the fibre bound at a regular state `R` and a vector `v`
  have hfib : ∀ (R : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ), IsRegularState W g R →
      ∫⁻ ω, ENNReal.ofReal (l2Norm (specProj (gueMat W ω - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R)
          (Set.Icc (-t) t) *ᵥ v) ^ 2) ∂(μ W 1) ≤
        ENNReal.ofReal ((2 * CL + 1) * (W : ℝ) ^ (2 * δ) * t) *
          ENNReal.ofReal (l2Norm v ^ 2) := by
    intro R v hR
    by_cases hv : v = 0
    · subst hv
      simp [l2Norm]
    · have hdc : DeformClass ε₀ (((g : ℂ) ^ 2) • R) :=
        projExp_deformClass_mono (hR.deformClass hg hg1) hgε
      have key := hn₀ W hWn (((g : ℂ) ^ 2) • R) E η hdc hE hηlow hη1 v hv
      have hlaw' : μ W 1 {ω | ¬ (star v ⬝ᵥ (resolventMat (gueMat W ω - ((g : ℂ) ^ 2) • R)
          ((E : ℂ) + (η : ℂ) * Complex.I) *ᵥ v)).im ≤
            CL * (star v ⬝ᵥ ((1 + (((g : ℂ) ^ 2) • R) * (((g : ℂ) ^ 2) • R))⁻¹ *ᵥ v)).re} ≤
          ENNReal.ofReal ((W : ℝ) ^ (-(1 : ℝ))) :=
        by
        refine le_trans (measure_mono ?_) key
        intro ω hω hall
        exact hω hall.2.2
      refine (projExp_fibre hCL0 hη0 htη hp0 hR.1 hlaw').trans ?_
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := sq_nonneg (l2Norm v)
      nlinarith
  -- the fresh block: the data are the values at the extension of the other blocks
  have hext := projExp_measurable_ext W L a
  have hag : ∀ ω : Ω W L, ∀ x, x.1 ≠ a →
      projExp_ext W L a (blockSplit W L a ω).2 x = ω x :=
    fun ω x hx => projExp_ext_split W L a ω x hx
  have hRe : ∀ ω : Ω W L, Rp (projExp_ext W L a (blockSplit W L a ω).2) = Rp ω :=
    fun ω => hRpa _ _ (hag ω)
  have hue : ∀ ω : Ω W L, u (projExp_ext W L a (blockSplit W L a ω).2) = u ω :=
    fun ω => hua _ _ (hag ω)
  have hSe : ∀ ω : Ω W L, projExp_ext W L a (blockSplit W L a ω).2 ∈ S ↔ ω ∈ S :=
    fun ω => Eq.to_iff (hSa _ _ (hag ω))
  let F : Matrix (Fin W) (Fin W) ℂ → ({x : Fin L × Fin W × Fin W // x.1 ≠ a} → ℝ) → ℝ≥0∞ :=
    fun V ρ => if projExp_ext W L a ρ ∈ S then
      ENNReal.ofReal (l2Norm (specProj (V - (E : ℂ) • 1 -
        ((g : ℂ) ^ 2) • Rp (projExp_ext W L a ρ)) (Set.Icc (-t) t) *ᵥ
          u (projExp_ext W L a ρ)) ^ 2) else 0
  let Bf : ({x : Fin L × Fin W × Fin W // x.1 ≠ a} → ℝ) → ℝ≥0∞ :=
    fun ρ => if projExp_ext W L a ρ ∈ S then
      ENNReal.ofReal ((2 * CL + 1) * (W : ℝ) ^ (2 * δ) * t) *
        ENNReal.ofReal (l2Norm (u (projExp_ext W L a ρ)) ^ 2) else 0
  have hF : Measurable (Function.uncurry F) := by
    have hshift : Measurable fun p : Matrix (Fin W) (Fin W) ℂ ×
        ({x : Fin L × Fin W × Fin W // x.1 ≠ a} → ℝ) =>
        p.1 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • Rp (projExp_ext W L a p.2) := by
      have hc : Continuous fun q : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ =>
          q.1 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • q.2 := by fun_prop
      exact hc.measurable.comp (measurable_fst.prodMk (hRp.comp (hext.comp measurable_snd)))
    have hm : Measurable fun p : Matrix (Fin W) (Fin W) ℂ ×
        ({x : Fin L × Fin W × Fin W // x.1 ≠ a} → ℝ) =>
        ENNReal.ofReal (l2Norm (specProj (p.1 - (E : ℂ) • 1 -
          ((g : ℂ) ^ 2) • Rp (projExp_ext W L a p.2)) (Set.Icc (-t) t) *ᵥ
            u (projExp_ext W L a p.2)) ^ 2) :=
      ENNReal.measurable_ofReal.comp
        ((projExp_continuous_l2Norm.measurable.comp (projExp_measurable_mulVec
          ((measurable_specProj isClosed_Icc).comp hshift)
          (hu.comp (hext.comp measurable_snd)))).pow_const 2)
    exact Measurable.ite (hS.preimage (hext.comp measurable_snd)) hm measurable_const
  have hB : ∀ ρ, ∫⁻ ω', F (gueMat W ω') ρ ∂(μ W 1) ≤ Bf ρ := by
    intro ρ
    by_cases hρ : projExp_ext W L a ρ ∈ S
    · simp only [F, Bf, hρ, ↓reduceIte]
      exact hfib _ _ (hreg _ hρ)
    · simp only [F, Bf, hρ, ↓reduceIte, lintegral_zero]
      exact le_rfl
  have key := lintegral_gueBlock_fresh_le W L a hF hB
  have hL : ∫⁻ ω, F (gueBlock W L ω a) (blockSplit W L a ω).2 ∂(μ W L) =
      ∫⁻ ω in S, ENNReal.ofReal (l2Norm (specProj (gueBlock W L ω a - (E : ℂ) • 1 -
        ((g : ℂ) ^ 2) • Rp ω) (Set.Icc (-t) t) *ᵥ u ω) ^ 2) ∂(μ W L) := by
    rw [← lintegral_indicator hS]
    refine lintegral_congr fun ω => ?_
    by_cases hω : ω ∈ S
    · simp [F, hω, hSe ω, hRe, hue]
    · simp [F, hω, hSe ω]
  have hR : ∫⁻ ω, Bf (blockSplit W L a ω).2 ∂(μ W L) =
      ENNReal.ofReal ((2 * CL + 1) * (W : ℝ) ^ (2 * δ) * t) *
        ∫⁻ ω in S, ENNReal.ofReal (l2Norm (u ω) ^ 2) ∂(μ W L) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator hS]
    refine lintegral_congr fun ω => ?_
    by_cases hω : ω ∈ S
    · simp [Bf, hω, hSe ω, hue]
    · simp [Bf, hω, hSe ω]
  rw [← hL, ← hR]
  exact key

end LSBA
