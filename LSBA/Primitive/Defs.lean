import LSBA.Kernel.Root
import LSBA.Loop.Basic
import LSBA.Loop.Cuts

/-!
# Primitive loops: definitions

Noncrossing dissections of the `k`-gon, the face corners and edge labels, the one-label inverses
and pair kernels of Appendix B.2 [sec:bl-primitives], the dressed dissection values of (B.1)
[ba:eq:dissection], the normalized primitive loops `F_k` and `𝒦_k = W^{1-k} F_k` of (5.10)
[fo:eq:primitive] at an anchor `m`, the root data, the pair formula (5.13) [fo:eq:pairs], the
two-loop swap and the initial values `𝒦_k(0) = Tr(M_B^{σ_1} E_{a_1} ⋯)`.
-/

open MeasureTheory Real Filter Topology Complex Finset
open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- `(i, j)` with `i < j` is a diagonal of the polygon on the vertices `0, …, k-1`: the
vertices are not neighbours modulo `k`. These are the nonadjacent cut pairs of (5.14)
[fo:eq:generator]. -/
def IsPolyDiag (k : ℕ) (d : Fin k × Fin k) : Prop :=
  d.1.val + 2 ≤ d.2.val ∧ ¬(d.1.val = 0 ∧ d.2.val + 1 = k)

instance (k : ℕ) (d : Fin k × Fin k) : Decidable (IsPolyDiag k d) := by
  unfold IsPolyDiag; exact instDecidableAnd

/-- The diagonals of the `k`-gon. -/
def polyDiags (k : ℕ) : Finset (Fin k × Fin k) :=
  @Finset.filter _ (IsPolyDiag k) (fun _ => inferInstance) Finset.univ

/-- Two diagonals cross. -/
def DiagCross {k : ℕ} (d e : Fin k × Fin k) : Prop :=
  (d.1 < e.1 ∧ e.1 < d.2 ∧ d.2 < e.2) ∨ (e.1 < d.1 ∧ d.1 < e.2 ∧ e.2 < d.2)

instance {k : ℕ} (d e : Fin k × Fin k) : Decidable (DiagCross d e) := by
  unfold DiagCross; exact instDecidableOr

/-- The noncrossing dissections of the `k`-gon (sets of pairwise noncrossing diagonals), the
index set of (B.1) [ba:eq:dissection]. -/
def dissections (k : ℕ) : Finset (Finset (Fin k × Fin k)) :=
  @Finset.filter _ (fun F => ∀ d ∈ F, ∀ e ∈ F, ¬DiagCross d e) (fun _ => inferInstance)
    (polyDiags k).powerset

/-- Cyclic offset `(w - v) mod k` of the vertex `w` seen from the vertex `v`. -/
def polyOff {k : ℕ} (v w : Fin k) : ℕ := (w.val + k - v.val) % k

/-- `w ≠ v` is joined to `v` by a side of the polygon or by a diagonal of `F`. -/
def PolyNbr {k : ℕ} (F : Finset (Fin k × Fin k)) (v w : Fin k) : Prop :=
  w ≠ v ∧ (polyOff v w = 1 ∨ polyOff v w + 1 = k ∨ (min v w, max v w) ∈ F)

instance {k : ℕ} (F : Finset (Fin k × Fin k)) (v w : Fin k) : Decidable (PolyNbr F v w) := by
  unfold PolyNbr; exact instDecidableAnd

/-- The corners at the vertex `v` of the faces of the dissection `F`: pairs `(w, w')` of
neighbours of `v`, consecutive in the cyclic order seen from `v`. -/
def polyCorners {k : ℕ} (F : Finset (Fin k × Fin k)) (v : Fin k) : Finset (Fin k × Fin k) :=
  @Finset.filter _ (fun p => PolyNbr F v p.1 ∧ PolyNbr F v p.2 ∧ polyOff v p.1 < polyOff v p.2 ∧
      ∀ u, PolyNbr F v u → ¬(polyOff v p.1 < polyOff v u ∧ polyOff v u < polyOff v p.2))
    (fun _ => inferInstance) Finset.univ

/-- The label carried by the edge `vw` in the face on one of its sides: the external
pre-label `y` for a side of the polygon; for a diagonal, its inner copy `cIn` (the
Cut_R side) or its outer copy `cOut` (the Cut_L side). `small = true` selects the face
on the side of the smaller offsets seen from `v`. -/
def edgeLab {L k : ℕ} (F : Finset (Fin k × Fin k)) (y : Fin k → Fin L) (cIn cOut : ↥F → Fin L)
    (v w : Fin k) (small : Bool) : Fin L :=
  if h : (min v w, max v w) ∈ F then
    (if decide (v < w) = small then cIn ⟨_, h⟩ else cOut ⟨_, h⟩)
  else if polyOff v w = 1 then y v else y w

/-- The one-label inverses `V_t^{σσ'}` of Appendix B.2 [sec:bl-primitives] in physical
space: `(I - tP)⁻¹` for opposite signs, `(I - tQ)⁻¹` for `++`, its conjugate for `--`. -/
def pairV {L : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) (σ σ' : Bool) :
    Matrix (Fin L) (Fin L) ℂ :=
  if σ = σ' then
    (if σ then (1 - (t : ℂ) • pairQ β M)⁻¹ else ((1 - (t : ℂ) • pairQ β M)⁻¹).map star)
  else ((1 - t • pairP β M)⁻¹).map ((↑) : ℝ → ℂ)

/-- The pair kernels of (5.13) [fo:eq:pairs]: `P(I - tP)⁻¹` for opposite signs,
`Q(I - tQ)⁻¹` for `++`, its conjugate for `--`. -/
def pairK {L : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) (σ σ' : Bool) :
    Matrix (Fin L) (Fin L) ℂ :=
  if σ = σ' then
    (if σ then pairQ β M * (1 - (t : ℂ) • pairQ β M)⁻¹
      else (pairQ β M * (1 - (t : ℂ) • pairQ β M)⁻¹).map star)
  else (mixedKer (pairP β M) t).map ((↑) : ℝ → ℂ)

/-- The one-label propagators `U_{s,t}^{σσ'}` of (5.15) [fo:eq:propagators]. -/
def pairU {L : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (s t : ℝ) (σ σ' : Bool) :
    Matrix (Fin L) (Fin L) ℂ :=
  if σ = σ' then
    (if σ then propPP (pairQ β M) s t else (propPP (pairQ β M) s t).map star)
  else (propPM (pairP β M) s t).map ((↑) : ℝ → ℂ)

/-- The core of the dissection `F` at the external pre-labels `y`: one factor `M^{σ_v}` per
face corner at the vertex `v`, and one link `β t V_t^{σ_iσ_j}` per diagonal `(i, j)`, summed
over the two copies of every diagonal label (the physical form of (B.1)
[ba:eq:dissection], external inverses removed). -/
def dissCore {L k : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) (σ : Fin k → Bool)
    (F : Finset (Fin k × Fin k)) (y : Fin k → Fin L) : ℂ :=
  ∑ cIn : ↥F → Fin L, ∑ cOut : ↥F → Fin L,
    (∏ d : ↥F, ((β * t : ℝ) : ℂ) * pairV β M t (σ d.1.1) (σ d.1.2) (cOut d) (cIn d)) *
      ∏ v : Fin k, ∏ p ∈ polyCorners F v,
        sgnMat M (σ v) (edgeLab F y cIn cOut v p.2 true) (edgeLab F y cIn cOut v p.1 false)

/-- The dressed value of the dissection `F`: the label `a_i`, between the signs `σ_i` and
`σ_{i+1}`, carries `V_t^{σ_iσ_{i+1}}`. -/
def dissVal {L k : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) (σ : Fin k → Bool)
    (F : Finset (Fin k × Fin k)) (a : Fin k → Fin L) : ℂ :=
  ∑ y : Fin k → Fin L,
    (∏ i, pairV β M t (σ i) (σ (finRotate k i)) (a i) (y i)) * dissCore β M t σ F y

/-- The normalized primitive loop `F_k = W^{k-1}𝒦_k` for the data `(β, M, m)` (it does not
depend on `W`): `m^σ` at length one, the pair formula (5.13) [fo:eq:pairs] at length two,
and the dissection sum (B.1) [ba:eq:dissection] at length `k ≥ 3`; the value `L` at length
zero makes `W F_0` the trace of the identity. -/
def primF {L : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (t : ℝ) {k : ℕ}
    (a : Fin k → Fin L) (σ : Fin k → Bool) : ℂ :=
  match k, a, σ with
  | 0, _, _ => (L : ℂ)
  | 1, _, σ => if σ 0 then m else star m
  | 2, a, σ => (β : ℂ)⁻¹ * pairK β M t (σ 0) (σ 1) (a 0) (a 1)
  | k + 3, a, σ => ∑ F ∈ dissections (k + 3), dissVal β M t σ F a

/-- `𝒦_k = W^{1-k} F_k`. -/
def primK {L : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (W : ℕ) (t : ℝ) {k : ℕ}
    (a : Fin k → Fin L) (σ : Fin k → Bool) : ℂ :=
  (W : ℂ) ^ (1 - (k : ℤ)) * primF β M m t a σ

/-- The primitive loop `𝒦_k(t; g, E; a, σ)` of (5.10) [fo:eq:primitive] at the anchor `m`,
with `M = M_B(g, E)` of (5.3) [fo:eq:characteristic]. -/
def primLoop (g : ℝ) (W L : ℕ) (E : ℝ) (m : ℂ) (t : ℝ) {k : ℕ} (a : Fin k → Fin L)
    (σ : Fin k → Bool) : ℂ :=
  primK (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) m W t a σ

/-- `F_k = W^{k-1}𝒦_k` of the model, Appendix B.5 [app:uniform-profile]. -/
def primLoopF (g : ℝ) (L : ℕ) (E : ℝ) (m : ℂ) (t : ℝ) {k : ℕ} (a : Fin k → Fin L)
    (σ : Fin k → Bool) : ℂ :=
  primF (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) m t a σ

/-- The periodic diameter of a label word: the largest cyclic distance of two labels. -/
def wordDiam {L k : ℕ} (a : Fin k → Fin L) : ℕ :=
  Finset.univ.sup fun p : Fin k × Fin k => cycDist (a p.1) (a p.2)

/-- The stable molecule `S_t^{[k]}` defined after (B.1) [ba:eq:dissection]: the core summed
over the dissections whose diagonals all join equal signs. -/
def stableMol {L k : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ) (σ : Fin k → Bool)
    (y : Fin k → Fin L) : ℂ :=
  ∑ F ∈ (dissections k).filter (fun F => ∀ d ∈ F, σ d.1 = σ d.2), dissCore β M t σ F y

/-- Normalized Fourier transform of a tensor on `ℤ_L^k` at the grid momenta `2πn_j/L`; for a
translation-invariant tensor and `Σ_j n_j ≡ 0` it is the anchored transform of Appendix B.2
[sec:bl-primitives]. -/
def tensorFourier {L k : ℕ} (S : (Fin k → Fin L) → ℂ) (n : Fin k → Fin L) : ℂ :=
  (L : ℂ)⁻¹ * ∑ x, S x * Complex.exp (-(2 * π * I * ∑ j, ((n j : ℕ) : ℂ) * ((x j : ℕ) : ℂ) / L))

/-- The algebraic data of the primitive loops: `β > 0`, `M` symmetric with diagonal `m`,
`Im m > 0`, and the characteristic identity `M - M* = 2iβ Im m · M M*` (Appendix B.1
[sec:gc-objects]). -/
structure PrimData {L : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) : Prop where
  pos : 0 < β
  symm : Mᵀ = M
  im_pos : 0 < m.im
  diag : ∀ a, M a a = m
  ward : M - Mᴴ = ((2 * β * m.im : ℝ) * I : ℂ) • (M * Mᴴ)

/-- The cycle adjacency matrix is symmetric. -/
private lemma primDefs_cycleAdj_transpose (L : ℕ) : (cycleAdj L)ᵀ = cycleAdj L := by
  ext a b
  simp only [Matrix.transpose_apply, cycleAdj, Matrix.of_apply]
  exact add_comm _ _

/-- `M_B = (bA_L - z - βm)⁻¹` is symmetric for every `m` (Lean inverse). -/
private lemma primDefs_dysonMat_transpose (b β : ℝ) (L : ℕ) (z m : ℂ) :
    (dysonMat b β L z m)ᵀ = dysonMat b β L z m := by
  rw [dysonMat, Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_smul, primDefs_cycleAdj_transpose, Matrix.transpose_one]

/-- `P` is symmetric when `M` is. -/
private lemma primDefs_pairP_transpose {L : ℕ} (β : ℝ) {M : Matrix (Fin L) (Fin L) ℂ}
    (hM : Mᵀ = M) : (pairP β M)ᵀ = pairP β M := by
  ext a b
  have h := congrFun (congrFun hM a) b
  simp only [Matrix.transpose_apply] at h
  simp only [Matrix.transpose_apply, pairP, Matrix.of_apply, h]

/-- `Q` is symmetric when `M` is. -/
private lemma primDefs_pairQ_transpose {L : ℕ} (β : ℝ) {M : Matrix (Fin L) (Fin L) ℂ}
    (hM : Mᵀ = M) : (pairQ β M)ᵀ = pairQ β M := by
  ext a b
  have h := congrFun (congrFun hM a) b
  simp only [Matrix.transpose_apply] at h
  simp only [Matrix.transpose_apply, pairQ, Matrix.of_apply, h]

/-- `X(1 - cX)⁻¹` is symmetric when `X` is, for every `c` (Lean inverse). -/
private lemma primDefs_ker_transpose {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (X : Matrix n n R) (hX : Xᵀ = X) (c : R) :
    (X * (1 - c • X)⁻¹)ᵀ = X * (1 - c • X)⁻¹ := by
  have hA : (1 - c • X)ᵀ = 1 - c • X := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hX]
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hA, hX]
  by_cases h : IsUnit (1 - c • X).det
  · have hc : (1 - c • X) * X = X * (1 - c • X) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
        Matrix.mul_smul]
    calc (1 - c • X)⁻¹ * X = (1 - c • X)⁻¹ * X * ((1 - c • X) * (1 - c • X)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ h, Matrix.mul_one]
      _ = (1 - c • X)⁻¹ * ((1 - c • X) * X) * (1 - c • X)⁻¹ := by
          rw [hc]; simp only [Matrix.mul_assoc]
      _ = X * (1 - c • X)⁻¹ := by
          rw [← Matrix.mul_assoc (1 - c • X)⁻¹, Matrix.nonsing_inv_mul _ h, Matrix.one_mul]
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.mul_zero, Matrix.zero_mul]

/-- The transpose of the pair kernel swaps the two signs. -/
private lemma primDefs_pairK_transpose {L : ℕ} (β : ℝ) {M : Matrix (Fin L) (Fin L) ℂ}
    (hM : Mᵀ = M) (t : ℝ) (s s' : Bool) : (pairK β M t s s')ᵀ = pairK β M t s' s := by
  have hQ := primDefs_ker_transpose (pairQ β M) (primDefs_pairQ_transpose β hM) (t : ℂ)
  have hP := primDefs_ker_transpose (pairP β M) (primDefs_pairP_transpose β hM) t
  cases s <;> cases s' <;>
    simp only [pairK, mixedKer, ite_true, ite_false, Bool.false_eq_true, Bool.true_eq_false,
      ← Matrix.transpose_map, hQ, hP]

/-- A real-energy root of (5.2) [fo:eq:dyson-family] gives the primitive data
`(γ_g, M_B(g, E), m)`. -/
theorem primData_of_root (g : ℝ) (L : ℕ) (hL : 3 ≤ L) (E : ℝ) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) :
    PrimData (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) m := by
  have hL1 : 1 ≤ L := by omega
  have hβ : 0 < gammaG g := by
    have : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
    unfold gammaG; positivity
  have hw : 0 < ((E : ℂ) + (gammaG g : ℂ) * m).im := by
    simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im, Complex.ofReal_re,
      zero_mul, add_zero]
    exact mul_pos hβ hm.1
  set M := dysonMat (hopB g) (gammaG g) L E m with hMdef
  have hdiag : ∀ a, M a a = m := fun a => (dysonMat_diag _ _ L hL1 E m hw a).trans hm.2.symm
  set w : ℂ := (E : ℂ) + (gammaG g : ℂ) * m with hwdef
  set B : Matrix (Fin L) (Fin L) ℂ := ((hopB g : ℝ) : ℂ) • cycleAdj L - w • 1 with hB
  have hMB : M = B⁻¹ := rfl
  have hsym : Mᵀ = M := primDefs_dysonMat_transpose _ _ _ _ _
  clear_value M B
  have hunit : IsUnit B.det := by
    by_contra h
    have h0 : M = 0 := by rw [hMB]; exact Matrix.nonsing_inv_apply_not_isUnit _ h
    have h1 := hdiag ⟨0, by omega⟩
    rw [h0] at h1
    have h2 := hm.1
    rw [← h1] at h2
    simp at h2
  have hNB : M * B = 1 := by rw [hMB]; exact Matrix.nonsing_inv_mul _ hunit
  have hBHN : Bᴴ * Mᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hNB, Matrix.conjTranspose_one]
  have hBH : Bᴴ - B = (w - starRingEnd ℂ w) • (1 : Matrix (Fin L) (Fin L) ℂ) := by
    rw [hB, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
      (cycleAdj_isHermitian L).eq, Matrix.conjTranspose_one, sub_smul]
    simp only [Complex.star_def, Complex.conj_ofReal]
    abel
  have key : M - Mᴴ = (w - starRingEnd ℂ w) • (M * Mᴴ) := by
    calc M - Mᴴ = M * (Bᴴ * Mᴴ) - (M * B) * Mᴴ := by
          rw [hBHN, hNB, Matrix.mul_one, Matrix.one_mul]
      _ = M * (Bᴴ - B) * Mᴴ := by
          rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = (w - starRingEnd ℂ w) • (M * Mᴴ) := by
          rw [hBH, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have hc : w - starRingEnd ℂ w = ((2 * gammaG g * m.im : ℝ) * I : ℂ) := by
    apply Complex.ext
    · simp [hwdef]
    · simp [hwdef]
      ring
  refine ⟨hβ, hsym, hm.1, hdiag, ?_⟩
  rw [key, hc]

/-- The rows of `P = β|M|²` sum to one under the primitive data, after (5.13) [fo:eq:pairs]. -/
theorem PrimData.row_sum {L : ℕ} {β : ℝ} {M : Matrix (Fin L) (Fin L) ℂ} {m : ℂ}
    (hD : PrimData β M m) (a : Fin L) : ∑ b, pairP β M a b = 1 := by
  have he := congrFun (congrFun hD.ward a) a
  simp only [Matrix.sub_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.mul_apply,
    smul_eq_mul, hD.diag] at he
  have hs : ∑ c, M a c * star (M a c) = ((∑ c, ‖M a c‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Complex.star_def, Complex.mul_conj']
  rw [hs] at he
  have him := congrArg Complex.im he
  simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.mul_im,
    Complex.ofReal_im, Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    add_zero, zero_add] at him
  simp only [pairP, Matrix.of_apply]
  rw [← Finset.mul_sum]
  have hpos : 0 < m.im := hD.im_pos
  have h2 : m.im * (β * ∑ c, ‖M a c‖ ^ 2) = m.im * 1 := by linarith
  exact mul_left_cancel₀ hpos.ne' h2

/-- `F_2` is the pair kernel divided by `β`. -/
private lemma primDefs_primF_two {L : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ) (t : ℝ)
    (a : Fin 2 → Fin L) (σ : Fin 2 → Bool) :
    primF β M m t a σ = (β : ℂ)⁻¹ * pairK β M t (σ 0) (σ 1) (a 0) (a 1) := rfl

/-- `𝒦_k = W^{1-k} F_k` of the model. -/
private lemma primDefs_primLoop_eq (g : ℝ) (W L : ℕ) (E : ℝ) (m : ℂ) (t : ℝ) {k : ℕ}
    (a : Fin k → Fin L) (σ : Fin k → Bool) :
    primLoop g W L E m t a σ = (W : ℂ) ^ (1 - (k : ℤ)) * primLoopF g L E m t a σ := rfl

/-- (5.13) [fo:eq:pairs], mixed signs. -/
theorem primLoop_two_pm (g : ℝ) (W L : ℕ) (E : ℝ) (m : ℂ) (t : ℝ) (a b : Fin L) :
    primLoop g W L E m t ![a, b] ![true, false] =
      ((gammaG g * W : ℝ) : ℂ)⁻¹ *
        (mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) t a b : ℂ) := by
  rw [primDefs_primLoop_eq, primLoopF, primDefs_primF_two]
  have hK : pairK (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t true false =
      (mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) t).map
        ((↑) : ℝ → ℂ) := by simp [pairK]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hK, Matrix.map_apply]
  push_cast
  rw [zpow_neg_one, mul_inv]
  ring

/-- (5.13) [fo:eq:pairs], equal signs. -/
theorem primLoop_two_pp (g : ℝ) (W L : ℕ) (E : ℝ) (m : ℂ) (t : ℝ) (a b : Fin L) :
    primLoop g W L E m t ![a, b] ![true, true] =
      ((gammaG g * W : ℝ) : ℂ)⁻¹ *
        (pairQ (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) *
          (1 - (t : ℂ) • pairQ (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))⁻¹) a b := by
  rw [primDefs_primLoop_eq, primLoopF, primDefs_primF_two]
  have hK : pairK (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t true true =
      pairQ (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) *
        (1 - (t : ℂ) • pairQ (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))⁻¹ := by
    simp [pairK]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hK]
  push_cast
  rw [zpow_neg_one, mul_inv]
  ring

/-- The two-loops of (5.13) [fo:eq:pairs] are symmetric under the swap of the two positions, for
every `t` and every `m` (`M_B` is symmetric). -/
theorem primLoop_two_swap (g : ℝ) (W L : ℕ) (E : ℝ) (m : ℂ) (t : ℝ) (x y : Fin L)
    (s s' : Bool) :
    primLoop g W L E m t ![x, y] ![s, s'] = primLoop g W L E m t ![y, x] ![s', s] := by
  have h := congrFun (congrFun (primDefs_pairK_transpose (gammaG g)
    (primDefs_dysonMat_transpose (hopB g) (gammaG g) L E m) t s' s) x) y
  simp only [Matrix.transpose_apply] at h
  rw [primDefs_primLoop_eq, primDefs_primLoop_eq, primLoopF, primLoopF, primDefs_primF_two,
    primDefs_primF_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, h]

/-- The cyclic offset without `mod`. -/
private lemma primDefs_polyOff_eq {k : ℕ} (v w : Fin k) :
    polyOff v w = if v.val ≤ w.val then w.val - v.val else w.val + k - v.val := by
  have := v.isLt
  have := w.isLt
  unfold polyOff
  split_ifs with h
  · rw [show w.val + k - v.val = (w.val - v.val) + k by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

/-- The offset seen from `v` determines the vertex. -/
private lemma primDefs_polyOff_inj {k : ℕ} {v w w' : Fin k} (h : polyOff v w = polyOff v w') :
    w = w' := by
  rw [primDefs_polyOff_eq, primDefs_polyOff_eq] at h
  have := v.isLt
  have := w.isLt
  have := w'.isLt
  apply Fin.ext
  split_ifs at h <;> omega

/-- The next vertex has offset `1`. -/
private lemma primDefs_polyOff_rot {n : ℕ} (v : Fin (n + 3)) :
    polyOff v (finRotate (n + 3) v) = 1 := by
  rw [primDefs_polyOff_eq, coe_finRotate]
  have := v.isLt
  by_cases hv : v = Fin.last (n + 2)
  · subst hv
    simp
  · have hv' : v.val ≠ n + 2 := fun h => hv (Fin.ext h)
    simp only [hv, ite_false]
    split_ifs <;> omega

/-- The previous vertex has offset `k - 1`. -/
private lemma primDefs_polyOff_rot_symm {n : ℕ} (v : Fin (n + 3)) :
    polyOff v ((finRotate (n + 3)).symm v) + 1 = n + 3 := by
  obtain ⟨u, rfl⟩ := (finRotate (n + 3)).surjective v
  rw [Equiv.symm_apply_apply, primDefs_polyOff_eq, coe_finRotate]
  have := u.isLt
  by_cases hu : u = Fin.last (n + 2)
  · subst hu
    simp
  · have hu' : u.val ≠ n + 2 := fun h => hu (Fin.ext h)
    simp only [hu, ite_false]
    split_ifs <;> omega

/-- Without diagonals, the neighbours of `v` are the vertices at offsets `1` and `k - 1`. -/
private lemma primDefs_polyNbr_empty {k : ℕ} (hk : 3 ≤ k) (v w : Fin k) :
    PolyNbr (∅ : Finset (Fin k × Fin k)) v w ↔ (polyOff v w = 1 ∨ polyOff v w + 1 = k) := by
  unfold PolyNbr
  simp only [Finset.notMem_empty, or_false]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rintro rfl
  rw [primDefs_polyOff_eq] at h
  simp at h
  omega

/-- Without diagonals, each vertex `v` has the single corner (next vertex, previous vertex). -/
private lemma primDefs_polyCorners_empty {n : ℕ} (v : Fin (n + 3)) :
    polyCorners (∅ : Finset (Fin (n + 3) × Fin (n + 3))) v =
      {(finRotate (n + 3) v, (finRotate (n + 3)).symm v)} := by
  have h1 := primDefs_polyOff_rot v
  have h2 := primDefs_polyOff_rot_symm v
  ext ⟨w₁, w₂⟩
  simp only [polyCorners, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    Prod.mk.injEq, primDefs_polyNbr_empty (by omega : 3 ≤ n + 3)]
  constructor
  · rintro ⟨hw₁, hw₂, hlt, -⟩
    have e1 : polyOff v w₁ = 1 := by omega
    have e2 : polyOff v w₂ = polyOff v ((finRotate (n + 3)).symm v) := by omega
    exact ⟨primDefs_polyOff_inj (e1.trans h1.symm), primDefs_polyOff_inj e2⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨Or.inl h1, Or.inr h2, by omega, ?_⟩
    intro u hu
    omega

/-- Without diagonals, an edge carries the external pre-label. -/
private lemma primDefs_edgeLab_empty {L k : ℕ} (y : Fin k → Fin L)
    (cIn cOut : ↥(∅ : Finset (Fin k × Fin k)) → Fin L) (v w : Fin k) (small : Bool) :
    edgeLab ∅ y cIn cOut v w small = if polyOff v w = 1 then y v else y w := by
  simp [edgeLab]

/-- The one-label inverses at `t = 0` are the identity. -/
private lemma primDefs_pairV_zero {L : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (s s' : Bool) :
    pairV β M 0 s s' = 1 := by
  unfold pairV
  split_ifs <;> simp

/-- The empty dissection is a dissection. -/
private lemma primDefs_empty_mem_dissections (k : ℕ) : ∅ ∈ dissections k := by
  simp [dissections]

/-- At `t = 0` a dissection with a diagonal has value `0` (its link carries `βt = 0`). -/
private lemma primDefs_dissVal_zero {L k : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ)
    (σ : Fin k → Bool) (F : Finset (Fin k × Fin k)) (hF : F ≠ ∅) (a : Fin k → Fin L) :
    dissVal β M 0 σ F a = 0 := by
  obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.mpr hF
  unfold dissVal dissCore
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [mul_eq_zero]
  right
  refine Finset.sum_eq_zero fun cIn _ => Finset.sum_eq_zero fun cOut _ => ?_
  rw [Finset.prod_eq_zero (Finset.mem_univ ⟨d, hd⟩) (by simp), zero_mul]

/-- At `t = 0` the empty dissection of the `k`-gon, `k ≥ 3`, has value
`Π_v (M^{σ_v})_{a_{v-1} a_v}`. -/
private lemma primDefs_dissVal_empty {L n : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ)
    (σ : Fin (n + 3) → Bool) (a : Fin (n + 3) → Fin L) :
    dissVal β M 0 σ ∅ a =
      ∏ j, sgnMat M (σ j) (a ((finRotate (n + 3)).symm j)) (a j) := by
  unfold dissVal
  simp only [primDefs_pairV_zero, Matrix.one_apply]
  rw [Finset.sum_eq_single a]
  · simp only [ite_true, Finset.prod_const_one, one_mul]
    unfold dissCore
    have hc : ∀ (cIn cOut : ↥(∅ : Finset (Fin (n + 3) × Fin (n + 3))) → Fin L),
        (∏ d : ↥(∅ : Finset (Fin (n + 3) × Fin (n + 3))),
            ((β * 0 : ℝ) : ℂ) * pairV β M 0 (σ d.1.1) (σ d.1.2) (cOut d) (cIn d)) *
          ∏ v : Fin (n + 3), ∏ p ∈ polyCorners ∅ v,
            sgnMat M (σ v) (edgeLab ∅ a cIn cOut v p.2 true)
              (edgeLab ∅ a cIn cOut v p.1 false) =
        ∏ j, sgnMat M (σ j) (a ((finRotate (n + 3)).symm j)) (a j) := by
      intro cIn cOut
      rw [Finset.prod_eq_one (fun d _ => absurd d.2 (Finset.notMem_empty _)), one_mul]
      refine Finset.prod_congr rfl fun v _ => ?_
      have h2 := primDefs_polyOff_rot_symm v
      have h3 : polyOff v ((finRotate (n + 3)).symm v) ≠ 1 := by omega
      rw [primDefs_polyCorners_empty, Finset.prod_singleton, primDefs_edgeLab_empty,
        primDefs_edgeLab_empty, primDefs_polyOff_rot]
      simp only [h3, ite_false, ite_true]
    simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_pi, Finset.prod_const,
      Fintype.card_fin]
    simp
  · intro y _ hy
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Ne.symm hi]), zero_mul]
  · simp

/-- The initial value in (5.10) [fo:eq:primitive]: `F_k(0) = Π_j (M^{σ_j})_{a_{j-1} a_j}`. -/
theorem primLoopF_init (g : ℝ) (L : ℕ) (hL : 3 ≤ L) (E : ℝ) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (k : ℕ) (hk : 1 ≤ k) (a : Fin k → Fin L)
    (σ : Fin k → Bool) :
    primLoopF g L E m 0 a σ =
      ∏ j, sgnMat (dysonMat (hopB g) (gammaG g) L E m) (σ j) (a ((finRotate k).symm j)) (a j) := by
  have hD := primData_of_root g L hL E m hm
  set M := dysonMat (hopB g) (gammaG g) L E m with hMdef
  have hβ : (gammaG g : ℂ) ≠ 0 := by exact_mod_cast hD.pos.ne'
  have hsym : ∀ x y, M y x = M x y := fun x y => congrFun (congrFun hD.symm x) y
  rcases k with _ | _ | _ | n
  · omega
  · have h0 : (finRotate 1).symm 0 = 0 := Subsingleton.elim _ _
    change (if σ 0 then m else star m) = _
    rw [Fin.prod_univ_one, h0]
    cases σ 0 <;> simp [sgnMat, hD.diag]
  · have h0 : (finRotate 2).symm 0 = 1 := by decide
    have h1 : (finRotate 2).symm 1 = 0 := by decide
    rw [primLoopF, primDefs_primF_two, Fin.prod_univ_two, h0, h1]
    cases σ 0 <;> cases σ 1 <;>
      simp [pairK, mixedKer, pairP, pairQ, sgnMat, Matrix.conjTranspose_apply, hsym (a 0) (a 1),
        ← hMdef, hβ, Complex.mul_conj', Complex.conj_mul', sq]
  · change ∑ F ∈ dissections (n + 3), dissVal _ _ 0 σ F a = _
    rw [Finset.sum_eq_single ∅ (fun F _ hF => primDefs_dissVal_zero _ _ σ F hF a)
      (fun h => absurd (primDefs_empty_mem_dissections _) h), primDefs_dissVal_empty]

/-- Entries of a product of factors `S_i D_{a_i}`, with `D_a` the diagonal matrix with entry `c`
at `a` and `0` elsewhere. -/
private lemma primDefs_prod_diag_apply {L : ℕ} (c : ℂ) :
    ∀ (n : ℕ) (S : Fin (n + 1) → Matrix (Fin L) (Fin L) ℂ) (a : Fin (n + 1) → Fin L) (x y : Fin L),
      (List.ofFn fun i => S i * Matrix.diagonal (fun b => if b = a i then c else 0)).prod x y =
        c ^ (n + 1) * S 0 x (a 0) * (∏ i : Fin n, S i.succ (a i.castSucc) (a i.succ)) *
          (if y = a (Fin.last n) then 1 else 0)
  | 0, S, a, x, y => by
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, Matrix.mul_one,
      Matrix.mul_diagonal]
    by_cases h : y = a 0
    · subst h
      simp [mul_comm]
    · simp [h]
  | n + 1, S, a, x, y => by
    rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
    rw [Finset.sum_eq_single (a 0)]
    · rw [primDefs_prod_diag_apply c n (fun i => S i.succ) (fun i => a i.succ) (a 0) y,
        Fin.prod_univ_succ]
      simp only [ite_true, Fin.succ_last, Fin.castSucc_zero, Fin.succ_castSucc]
      ring
    · intro b _ hb
      simp [hb]
    · simp

/-- Trace of a product of factors `S_i D_{a_i}`. -/
private lemma primDefs_trace_prod_diag {L n : ℕ} (c : ℂ)
    (S : Fin (n + 1) → Matrix (Fin L) (Fin L) ℂ)
    (a : Fin (n + 1) → Fin L) :
    (List.ofFn fun i => S i * Matrix.diagonal (fun b => if b = a i then c else 0)).prod.trace =
      c ^ (n + 1) * ∏ j, S j (a ((finRotate (n + 1)).symm j)) (a j) := by
  have h0 : (finRotate (n + 1)).symm 0 = Fin.last n := by
    rw [Equiv.symm_apply_eq, finRotate_last]
  have hs : ∀ i : Fin n, (finRotate (n + 1)).symm i.succ = i.castSucc := by
    intro i
    rw [Equiv.symm_apply_eq, finRotate_apply, Fin.coeSucc_eq_succ]
  simp only [Matrix.trace, Matrix.diag, primDefs_prod_diag_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Fin.prod_univ_succ, h0]
  simp only [hs]
  ring

/-- A product of Kronecker factors `X_i ⊗ 1`. -/
private lemma primDefs_list_prod_kron {L W : ℕ} :
    ∀ l : List (Matrix (Fin L) (Fin L) ℂ),
      (l.map fun X => X ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)).prod =
        l.prod ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)
  | [] => by simp
  | X :: l => by
    rw [List.map_cons, List.prod_cons, primDefs_list_prod_kron l, List.prod_cons,
      ← Matrix.mul_kronecker_mul, Matrix.mul_one]

/-- The loop of `X ⊗ I_W` reduces to a trace on the blocks. -/
private lemma primDefs_loopTr_kron {W L k : ℕ} (X : Matrix (Fin L) (Fin L) ℂ) (a : Fin k → Fin L)
    (σ : Fin k → Bool) :
    loopTr (X ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) a σ =
      (W : ℂ) * (List.ofFn fun i => sgnMat X (σ i) *
        Matrix.diagonal (fun b => if b = a i then (W : ℂ)⁻¹ else 0)).prod.trace := by
  have hS : ∀ s : Bool, sgnMat (X ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) s =
      sgnMat X s ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) := by
    intro s
    cases s <;> simp [sgnMat, Matrix.conjTranspose_kronecker]
  have hE : ∀ b : Fin L, blockE W L b =
      Matrix.diagonal (fun x => if x = b then (W : ℂ)⁻¹ else 0) ⊗ₖ
        (1 : Matrix (Fin W) (Fin W) ℂ) := by
    intro b
    ext ⟨x, α⟩ ⟨y, β⟩
    simp only [blockE, Matrix.kroneckerMap_apply, Matrix.diagonal_apply, Matrix.one_apply,
      Prod.mk.injEq]
    by_cases hxy : x = y <;> by_cases hαβ : α = β <;> by_cases hx : x = b <;> simp [hxy, hαβ, hx]
  unfold loopTr
  simp only [hS, hE, ← Matrix.mul_kronecker_mul, Matrix.mul_one]
  rw [show (List.ofFn fun i => (sgnMat X (σ i) *
        Matrix.diagonal fun x => if x = a i then (W : ℂ)⁻¹ else 0) ⊗ₖ
          (1 : Matrix (Fin W) (Fin W) ℂ)) =
      (List.ofFn fun i => sgnMat X (σ i) *
        Matrix.diagonal fun x => if x = a i then (W : ℂ)⁻¹ else 0).map
          (fun Y => Y ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) by rw [List.map_ofFn]; rfl,
    primDefs_list_prod_kron, Matrix.trace_kronecker, Matrix.trace_one, Fintype.card_fin,
    mul_comm]

/-- The initial value in (5.10) [fo:eq:primitive] is the `M`-loop
`Tr Π_j (M^{σ_j} E_{a_j})` with `M = M_B ⊗ I_W`, in the loop vocabulary of (5.5)
[fo:eq:loops]. -/
theorem primLoop_init (g : ℝ) (W L : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ L) (E : ℝ) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {k : ℕ} (a : Fin k → Fin L)
    (σ : Fin k → Bool) :
    primLoop g W L E m 0 a σ =
      loopTr (dysonMat (hopB g) (gammaG g) L E m ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) a σ := by
  rw [primDefs_primLoop_eq, primDefs_loopTr_kron]
  rcases k with _ | n
  · simp [primLoopF, primF]
  · have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast (by omega : W ≠ 0)
    rw [primLoopF_init g L hL E m hm (n + 1) (by omega) a σ, primDefs_trace_prod_diag]
    rw [zpow_sub₀ hW', zpow_one, zpow_natCast, div_eq_mul_inv, ← inv_pow]
    ring

end LSBA
