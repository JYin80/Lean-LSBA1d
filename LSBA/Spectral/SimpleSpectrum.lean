import LSBA.Model.Basic
import LSBA.Spectral.PolyNull

/-!
# Almost surely simple spectrum

The spectrum of the model (1.3) [eq:model] is almost surely simple (stated after (1.5)
[eq:eigenvectors]), through the Hankel discriminant of the eigenvalues.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Hankel discriminant `det [Tr A^{i+j}]_{0 ≤ i,j < N}`. -/
def hankelDisc (A : Matrix n n ℂ) : ℂ :=
  (Matrix.of fun i j : Fin (Fintype.card n) => (A ^ (i.val + j.val)).trace).det

/-- The Hankel determinant `det [Tr A^{i+j}]_{0 ≤ i,j < N}` over a commutative ring. -/
private def simpleSpectrum_hankelR {R : Type*} [CommRing R] (A : Matrix n n R) : R :=
  (Matrix.of fun i j : Fin (Fintype.card n) => (A ^ (i.val + j.val)).trace).det

/-- The Hankel determinant commutes with ring homomorphisms applied entrywise. -/
private lemma simpleSpectrum_map_hankelR {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A : Matrix n n R) : f (simpleSpectrum_hankelR A) = simpleSpectrum_hankelR (A.map f) := by
  unfold simpleSpectrum_hankelR
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, ← Matrix.map_pow]
  exact AddMonoidHom.map_trace f.toAddMonoidHom _

/-- Power traces of a Hermitian matrix are power sums of its eigenvalues. -/
private lemma simpleSpectrum_trace_pow {A : Matrix n n ℂ} (hA : A.IsHermitian) (s : ℕ) :
    (A ^ s).trace = ∑ m, ((hA.eigenvalues m : ℝ) : ℂ) ^ s := by
  conv_lhs => rw [hA.spectral_theorem, ← map_pow]
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul,
    Matrix.diagonal_pow, Matrix.trace_diagonal]
  simp

/-- If the power traces of `A` are the power sums of `v`, the Hankel discriminant of `A` is the
squared Vandermonde determinant of `v`. -/
private lemma simpleSpectrum_hankel_eq {A : Matrix n n ℂ} (v : n → ℂ)
    (hv : ∀ s : ℕ, (A ^ s).trace = ∑ m, v m ^ s) :
    hankelDisc A = (Matrix.vandermonde (v ∘ (Fintype.equivFin n).symm)).det ^ 2 := by
  have h : (Matrix.of fun i j : Fin (Fintype.card n) => (A ^ (i.val + j.val)).trace) =
      (Matrix.vandermonde (v ∘ (Fintype.equivFin n).symm))ᵀ *
        Matrix.vandermonde (v ∘ (Fintype.equivFin n).symm) := by
    ext i j
    rw [Matrix.vandermonde_transpose_mul_vandermonde, Matrix.of_apply, hv]
    exact (Equiv.sum_comp (Fintype.equivFin n).symm (fun m => v m ^ (i.val + j.val))).symm
  rw [hankelDisc, h, Matrix.det_mul, Matrix.det_transpose, sq]

/-- If the power traces of `A` are the power sums of `v`, the Hankel discriminant of `A` is
nonzero exactly when `v` is injective. -/
private lemma simpleSpectrum_hankel_ne_zero_iff {A : Matrix n n ℂ} (v : n → ℂ)
    (hv : ∀ s : ℕ, (A ^ s).trace = ∑ m, v m ^ s) :
    hankelDisc A ≠ 0 ↔ Function.Injective v := by
  rw [simpleSpectrum_hankel_eq v hv, pow_ne_zero_iff two_ne_zero,
    Matrix.det_vandermonde_ne_zero_iff]
  exact Equiv.injective_comp _ _

/-- For a Hermitian matrix, the Hankel discriminant is nonzero exactly when the eigenvalues are
pairwise distinct. -/
theorem hankelDisc_ne_zero_iff {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    hankelDisc A ≠ 0 ↔ Function.Injective hA.eigenvalues := by
  rw [simpleSpectrum_hankel_ne_zero_iff _ (simpleSpectrum_trace_pow hA)]
  exact Complex.ofReal_injective.of_comp_iff _

/-- Scaling a matrix by `c ≠ 0` does not change whether its Hankel discriminant vanishes. -/
private lemma simpleSpectrum_hankel_smul_ne_zero {c : ℂ} (hc : c ≠ 0) (A : Matrix n n ℂ) :
    hankelDisc (c • A) ≠ 0 ↔ hankelDisc A ≠ 0 := by
  set H : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ :=
    Matrix.of fun i j => (A ^ (i.val + j.val)).trace with hH
  have h : (Matrix.of fun i j : Fin (Fintype.card n) => ((c • A) ^ (i.val + j.val)).trace) =
      Matrix.of fun i j => c ^ i.val * (Matrix.of fun i j => c ^ j.val * H i j) i j := by
    ext i j
    rw [Matrix.of_apply, Matrix.of_apply, Matrix.of_apply, hH, Matrix.of_apply, smul_pow,
      Matrix.trace_smul, smul_eq_mul, pow_add]
    ring
  have hc' : ∀ i : Fin (Fintype.card n), c ^ i.val ≠ 0 := fun i => pow_ne_zero _ hc
  have hp : ∏ i : Fin (Fintype.card n), c ^ i.val ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => hc' i
  rw [hankelDisc, h, Matrix.det_mul_column, Matrix.det_mul_row, hankelDisc, ← hH]
  constructor
  · intro h0 h1
    exact h0 (by rw [h1, mul_zero, mul_zero])
  · intro h1
    exact mul_ne_zero hp (mul_ne_zero hp h1)

/-- The GUE block of (1.2) [eq:covariance] with polynomial entries in the coordinates. -/
private def simpleSpectrum_gueBlockPoly (W L : ℕ) (a : Fin L) :
    Matrix (Fin W) (Fin W) (MvPolynomial (Fin L × Fin W × Fin W) ℂ) :=
  Matrix.of fun α β =>
    if α = β then MvPolynomial.X (a, α, α) * MvPolynomial.C ((Real.sqrt W : ℂ))⁻¹
    else if α < β then
      (MvPolynomial.X (a, α, β) + MvPolynomial.C Complex.I * MvPolynomial.X (a, β, α)) *
        MvPolynomial.C ((Real.sqrt (2 * W) : ℂ))⁻¹
    else
      (MvPolynomial.X (a, β, α) - MvPolynomial.C Complex.I * MvPolynomial.X (a, α, β)) *
        MvPolynomial.C ((Real.sqrt (2 * W) : ℂ))⁻¹

/-- The model (1.3) [eq:model] with polynomial entries in the coordinates. -/
private def simpleSpectrum_HmatPoly (g : ℝ) (W L : ℕ) :
    Matrix (Fin L × Fin W) (Fin L × Fin W) (MvPolynomial (Fin L × Fin W × Fin W) ℂ) :=
  Matrix.of fun p q => MvPolynomial.C (((max 1 g : ℝ)⁻¹ : ℝ) : ℂ) *
    (MvPolynomial.C ((g : ℂ) * (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) p q) +
      if p.1 = q.1 then simpleSpectrum_gueBlockPoly W L p.1 p.2 q.2 else 0)

/-- Evaluating the polynomial model at a sample gives the model (1.3) [eq:model]. -/
private lemma simpleSpectrum_map_HmatPoly (g : ℝ) (W L : ℕ) (ω : Ω W L) :
    (simpleSpectrum_HmatPoly g W L).map (MvPolynomial.eval fun i => (ω i : ℂ)) =
      Hmat g W L ω := by
  ext p q
  simp only [Matrix.map_apply, simpleSpectrum_HmatPoly, simpleSpectrum_gueBlockPoly,
    Matrix.of_apply, Hmat, Hdet, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, blockDiagOp,
    gueBlock]
  split_ifs <;> simp [div_eq_mul_inv]

/-- The Hankel discriminant of the model (1.3) [eq:model] is the real evaluation of one complex
polynomial in the coordinates of the sample. -/
theorem exists_mvPolynomial_hankelDisc (g : ℝ) (W L : ℕ) :
    ∃ P : MvPolynomial (Fin L × Fin W × Fin W) ℂ,
      ∀ ω : Ω W L, hankelDisc (Hmat g W L ω) = MvPolynomial.eval (fun i => (ω i : ℂ)) P := by
  refine ⟨simpleSpectrum_hankelR (simpleSpectrum_HmatPoly g W L), fun ω => ?_⟩
  rw [simpleSpectrum_map_hankelR, simpleSpectrum_map_HmatPoly]
  rfl

/-- For every `g`, `W`, `L` some sample of the model (1.3) [eq:model] has simple spectrum. -/
theorem exists_injective_eigenvalues (g : ℝ) (W L : ℕ) :
    ∃ ω : Ω W L, Function.Injective (Hmat_isHermitian g W L ω).eigenvalues := by
  set K : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
    cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) with hK
  set d : Fin L × Fin W → ℝ := fun p => ((finProdFinEquiv p : ℕ) : ℝ) with hd
  have hdinj : Function.Injective fun p => (d p : ℂ) :=
    Complex.ofReal_injective.comp
      (Nat.cast_injective.comp (Fin.val_injective.comp finProdFinEquiv.injective))
  set D : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ := Matrix.diagonal fun p => (d p : ℂ)
    with hD
  have hD0 : hankelDisc D ≠ 0 := by
    refine (simpleSpectrum_hankel_ne_zero_iff _ fun s => ?_).mpr hdinj
    rw [hD, Matrix.diagonal_pow, Matrix.trace_diagonal]
    rfl
  obtain ⟨R, hR⟩ : ∃ R : Polynomial ℂ, ∀ u : ℂ, R.eval u = hankelDisc (u • K + D) := by
    refine ⟨simpleSpectrum_hankelR ((Polynomial.X : Polynomial ℂ) •
      K.map (Polynomial.C : ℂ →+* Polynomial ℂ) + D.map Polynomial.C),
      fun u => ?_⟩
    rw [← Polynomial.coe_evalRingHom, simpleSpectrum_map_hankelR]
    exact congrArg simpleSpectrum_hankelR (by ext p q; simp; ring)
  have hR0 : R.eval 0 ≠ 0 := by
    rw [hR, zero_smul, zero_add]
    exact hD0
  obtain ⟨u, s, hs, hgsu, hRu⟩ : ∃ u s : ℝ, s ≠ 0 ∧ g = s * u ∧ R.eval (u : ℂ) ≠ 0 := by
    by_cases hg : g = 0
    · exact ⟨0, 1, one_ne_zero, by simp [hg], by simpa using hR0⟩
    · have hRne : R ≠ 0 := fun h => hR0 (by rw [h, Polynomial.eval_zero])
      obtain ⟨u, hu⟩ := (((Polynomial.finite_setOfPred_isRoot hRne).preimage
        Complex.ofReal_injective.injOn).union (Set.finite_singleton (0 : ℝ))).exists_notMem
      simp only [Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff,
        not_or, Polynomial.IsRoot.def] at hu
      exact ⟨u, g / u, div_ne_zero hg hu.2, by field_simp [hu.2], hu.1⟩
  set ω : Ω W L := fun x => if x.2.1 = x.2.2 then Real.sqrt W * s * d (x.1, x.2.1) else 0
    with hω
  refine ⟨ω, (hankelDisc_ne_zero_iff _).mp ?_⟩
  have hblock : blockDiagOp (gueBlock W L ω) = (s : ℂ) • D := by
    ext ⟨a, α⟩ ⟨b, β⟩
    have hW : ((Real.sqrt W : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr α.pos)).ne'
    simp only [blockDiagOp, gueBlock, hω, hD, Matrix.of_apply, Matrix.smul_apply,
      Matrix.diagonal_apply, Prod.mk.injEq, smul_eq_mul]
    by_cases hab : a = b
    · subst hab
      by_cases hαβ : α = β
      · subst hαβ
        simp only [ite_true, and_self, Complex.ofReal_mul]
        field_simp
      · rcases lt_or_gt_of_ne hαβ with h | h <;> simp [hαβ, Ne.symm hαβ, h, not_lt_of_gt h]
    · simp [hab]
  have hm : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hH : Hmat g W L ω = (((max 1 g : ℝ)⁻¹ : ℂ) * s) • ((u : ℂ) • K + D) := by
    rw [Hmat, Hdet, hblock, hgsu]
    ext p q
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Complex.ofReal_mul]
    ring
  have hc : (((max 1 g : ℝ)⁻¹ : ℂ) * s) ≠ 0 :=
    mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr hm.ne')) (Complex.ofReal_ne_zero.mpr hs)
  rw [hH, simpleSpectrum_hankel_smul_ne_zero hc, ← hR]
  exact hRu

/-- The spectrum of the model (1.3) [eq:model] is almost surely simple, as stated after (1.5)
[eq:eigenvectors]. -/
theorem ae_injective_eigenvalues (g : ℝ) (W L : ℕ) :
    ∀ᵐ ω ∂(μ W L), Function.Injective (Hmat_isHermitian g W L ω).eigenvalues := by
  obtain ⟨P, hP⟩ := exists_mvPolynomial_hankelDisc g W L
  obtain ⟨ω₀, h₀⟩ := exists_injective_eigenvalues g W L
  have h₀' : MvPolynomial.eval (fun i => (ω₀ i : ℂ)) P ≠ 0 := by
    rw [← hP]
    exact (hankelDisc_ne_zero_iff _).mpr h₀
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have hnull :=
    measure_zero_mvPolynomial (fun _ : Fin L × Fin W × Fin W => gaussianReal 0 1) P ω₀ h₀'
  rw [ae_iff, μ]
  refine measure_mono_null (fun ω hω => ?_) hnull
  rw [Set.mem_ofPred_eq] at hω ⊢
  rw [← hP]
  by_contra h
  exact hω ((hankelDisc_ne_zero_iff _).mp h)

end LSBA
