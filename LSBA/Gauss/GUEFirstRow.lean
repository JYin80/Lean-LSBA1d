import LSBA.Gauss.GUEMat
import LSBA.Gauss.CGauss
import LSBA.Spectral.PolyNull

/-!
# The first row of a GUE matrix

For the `(m+1) × (m+1)` GUE matrix `V` of (1.2) [eq:covariance], the rescaled corner
`√(m+1) V₀₀`, the rescaled first column `√(m+1) (V_{k+1,0})_k` and the lower block are
independent: a standard real Gaussian, a standard complex Gaussian vector, and `√(m/(m+1))` times
an `m × m` GUE matrix. Hence `√(m+1)(A + V)` is a bordered matrix with these entries
([APSSS, (2.8)]). Also: `A + c V` is almost surely invertible for Hermitian `A` and `c ≠ 0`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The coordinates of an `(m+1) × (m+1)` GUE sample split into the corner `√(m+1) V₀₀`, the
column `(√(m+1) V_{k+1,0})_k` and the sample of the lower `m × m` block. -/
def firstRowSplit (m : ℕ) (ω : Ω (m + 1) 1) : ℝ × (Fin m → ℂ) × Ω m 1 :=
  (ω (0, 0, 0),
    fun k => ((Real.sqrt 2)⁻¹ : ℂ) * ⟨ω (0, 0, k.succ), -ω (0, k.succ, 0)⟩,
    fun x => ω (0, x.2.1.succ, x.2.2.succ))

/-- Index map from the four groups of coordinates (corner, row and column, lower block) to the
coordinates of an `(m+1) × (m+1)` sample. -/
private def firstRow_idx (m : ℕ) :
    Unit ⊕ ((Fin m × Fin 2) ⊕ (Fin 1 × Fin m × Fin m)) → Fin 1 × Fin (m + 1) × Fin (m + 1)
  | .inl _ => (0, 0, 0)
  | .inr (.inl p) => if p.2 = 0 then (0, 0, p.1.succ) else (0, p.1.succ, 0)
  | .inr (.inr x) => (0, x.2.1.succ, x.2.2.succ)

private lemma firstRow_zero_ne_succ {m : ℕ} (k : Fin m) : (0 : Fin (m + 1)) ≠ k.succ :=
  (Fin.succ_ne_zero k).symm

private lemma firstRow_idx_bijective (m : ℕ) : Function.Bijective (firstRow_idx m) := by
  constructor
  · rintro (a | ⟨k, i⟩ | ⟨z, k, l⟩) (a' | ⟨k', i'⟩ | ⟨z', k', l'⟩) h <;>
      (try fin_cases i) <;> (try fin_cases i') <;>
      simp [firstRow_idx, Prod.ext_iff, firstRow_zero_ne_succ, Fin.succ_ne_zero] at h ⊢ <;>
      first | exact h | exact ⟨Subsingleton.elim _ _, h⟩
  · rintro ⟨a, b, c⟩
    obtain rfl : a = 0 := Subsingleton.elim _ _
    refine Fin.cases ?_ (fun i => ?_) b <;> refine Fin.cases ?_ (fun j => ?_) c
    · exact ⟨.inl (), rfl⟩
    · exact ⟨.inr (.inl (j, 0)), by simp [firstRow_idx]⟩
    · exact ⟨.inr (.inl (i, 1)), by simp [firstRow_idx]⟩
    · exact ⟨.inr (.inr (0, i, j)), rfl⟩

/-- The coordinates of an `(m+1) × (m+1)` sample regrouped as corner, row and column, lower block
(independent standard Gaussians). -/
private lemma firstRow_regroup (m : ℕ) :
    MeasurePreserving
      (fun ω : Ω (m + 1) 1 => (ω (0, 0, 0),
        (fun p : Fin m × Fin 2 => ω (firstRow_idx m (.inr (.inl p))),
          fun x : Fin 1 × Fin m × Fin m => ω (0, x.2.1.succ, x.2.2.succ))))
      (μ (m + 1) 1) ((gaussianReal 0 1).prod
        ((stdGauss (Fin m × Fin 2)).prod (μ m 1))) := by
  set σ := Equiv.ofBijective (firstRow_idx m) (firstRow_idx_bijective m) with hσ
  have h1 := (measurePreserving_piCongrLeft
    (fun _ : Fin 1 × Fin (m + 1) × Fin (m + 1) => gaussianReal (0 : ℝ) 1) σ).symm
    (MeasurableEquiv.piCongrLeft (fun _ => ℝ) σ)
  have h2 := measurePreserving_sumPiEquivProdPi
    (X := fun _ : Unit ⊕ ((Fin m × Fin 2) ⊕ (Fin 1 × Fin m × Fin m)) => ℝ)
    (fun _ => gaussianReal (0 : ℝ) 1)
  have h3 := measurePreserving_sumPiEquivProdPi
    (X := fun _ : (Fin m × Fin 2) ⊕ (Fin 1 × Fin m × Fin m) => ℝ)
    (fun _ => gaussianReal (0 : ℝ) 1)
  have h4 := measurePreserving_piUnique (X := fun _ : Unit => ℝ)
    (fun _ => gaussianReal (0 : ℝ) 1)
  have h5 := (h4.prod h3).comp (h2.comp h1)
  have heq : (fun ω : Ω (m + 1) 1 => (ω (0, 0, 0),
        (fun p : Fin m × Fin 2 => ω (firstRow_idx m (.inr (.inl p))),
          fun x : Fin 1 × Fin m × Fin m => ω (0, x.2.1.succ, x.2.2.succ)))) =
      Prod.map ⇑(MeasurableEquiv.piUnique fun _ : Unit => ℝ)
          ⇑(MeasurableEquiv.sumPiEquivProdPi
            fun _ : (Fin m × Fin 2) ⊕ (Fin 1 × Fin m × Fin m) => ℝ) ∘
        ⇑(MeasurableEquiv.sumPiEquivProdPi fun _ : Unit ⊕ ((Fin m × Fin 2) ⊕
          (Fin 1 × Fin m × Fin m)) => ℝ) ∘ ⇑(MeasurableEquiv.piCongrLeft (fun _ => ℝ) σ).symm := by
    funext ω
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · rfl
    · rfl
    · rfl
  rw [heq]
  exact h5

/-- Sign flip of the second real coordinate of each pair. -/
private def firstRow_neg (m : ℕ) (y : Fin m × Fin 2 → ℝ) : Fin m × Fin 2 → ℝ :=
  fun p => if p.2 = 0 then y p else -y p

private lemma firstRow_neg_mp (m : ℕ) :
    MeasurePreserving (firstRow_neg m) (stdGauss (Fin m × Fin 2)) (stdGauss (Fin m × Fin 2)) := by
  have h : ∀ p : Fin m × Fin 2, MeasurePreserving (fun x : ℝ => if p.2 = 0 then x else -x)
      (gaussianReal (0 : ℝ) 1) (gaussianReal (0 : ℝ) 1) := by
    intro p
    by_cases hp : p.2 = 0
    · simp only [hp, ite_true]
      exact MeasurePreserving.id _
    · simp only [hp, ite_false]
      refine ⟨measurable_neg, ?_⟩
      rw [gaussianReal_map_neg, neg_zero]
  exact measurePreserving_pi (fun _ : Fin m × Fin 2 => gaussianReal (0 : ℝ) 1)
    (fun _ : Fin m × Fin 2 => gaussianReal (0 : ℝ) 1) h

/-- The coordinate map `y ↦ ((√2)⁻¹ (y_{i,0} + i y_{i,1}))ᵢ` is measurable. -/
private lemma firstRow_phi_measurable (m : ℕ) :
    Measurable fun (y : Fin m × Fin 2 → ℝ) (i : Fin m) =>
      ((Real.sqrt 2)⁻¹ : ℂ) * (⟨y (i, 0), y (i, 1)⟩ : ℂ) := by
  refine measurable_pi_iff.mpr fun i => ?_
  have : (fun y : Fin m × Fin 2 → ℝ => ((Real.sqrt 2)⁻¹ : ℂ) * (⟨y (i, 0), y (i, 1)⟩ : ℂ)) =
      fun y => ((Real.sqrt 2)⁻¹ : ℂ) * ((y (i, 0) : ℂ) + (y (i, 1) : ℂ) * Complex.I) := by
    funext y
    rw [Complex.mk_eq_add_mul_I]
  rw [this]
  fun_prop

/-- The corner, the first column and the lower block of the GUE matrix of (1.2)
[eq:covariance] are independent, with laws `N(0, 1)`, `stdCGauss (Fin m)` and `μ m 1`. -/
theorem measurePreserving_firstRowSplit (m : ℕ) :
    MeasurePreserving (firstRowSplit m) (μ (m + 1) 1)
      ((gaussianReal 0 1).prod ((stdCGauss (Fin m)).prod (μ m 1))) := by
  have hΦ : MeasurePreserving (fun (y : Fin m × Fin 2 → ℝ) (i : Fin m) =>
      ((Real.sqrt 2)⁻¹ : ℂ) * (⟨y (i, 0), y (i, 1)⟩ : ℂ)) (stdGauss (Fin m × Fin 2))
      (stdCGauss (Fin m)) :=
    ⟨firstRow_phi_measurable m, (stdCGauss_eq_map (Fin m)).symm⟩
  have h2 := (MeasurePreserving.id (gaussianReal (0 : ℝ) 1)).prod
    ((hΦ.comp (firstRow_neg_mp m)).prod (MeasurePreserving.id (μ m 1)))
  have h3 := h2.comp (firstRow_regroup m)
  have heq : firstRowSplit m = Prod.map id (Prod.map ((fun (y : Fin m × Fin 2 → ℝ) (i : Fin m) =>
      ((Real.sqrt 2)⁻¹ : ℂ) * (⟨y (i, 0), y (i, 1)⟩ : ℂ)) ∘ firstRow_neg m) id) ∘
      (fun ω : Ω (m + 1) 1 => (ω (0, 0, 0),
        (fun p : Fin m × Fin 2 => ω (firstRow_idx m (.inr (.inl p))),
          fun x : Fin 1 × Fin m × Fin m => ω (0, x.2.1.succ, x.2.2.succ)))) := by
    funext ω
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    funext k
    simp [firstRowSplit, firstRow_neg, firstRow_idx]
  rw [heq]
  exact h3

/-- For Hermitian `A`, `√(m+1) (A + V) = [[g + √(m+1) A₀₀, x*], [x, √m V' + √(m+1) D]]` with
`(g, γ, ω') = firstRowSplit m ω`, `x = γ + √(m+1) (A_{k+1,0})_k`, `V'` the `m × m` GUE matrix
of `ω'` and `D` the lower block of `A` ([APSSS, (2.8)]). -/
theorem smul_add_gueMat_eq_borderMat (m : ℕ) {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ}
    (hA : A.IsHermitian) (ω : Ω (m + 1) 1) :
    ((Real.sqrt ((m : ℝ) + 1) : ℝ) : ℂ) • (A + gueMat (m + 1) ω) =
      borderMat m (((firstRowSplit m ω).1 : ℂ) + ((Real.sqrt ((m : ℝ) + 1) : ℝ) : ℂ) * A 0 0)
        ((firstRowSplit m ω).2.1 + ((Real.sqrt ((m : ℝ) + 1) : ℝ) : ℂ) • fun k => A k.succ 0)
        (((Real.sqrt (m : ℝ) : ℝ) : ℂ) • gueMat m (firstRowSplit m ω).2.2 +
          ((Real.sqrt ((m : ℝ) + 1) : ℝ) : ℂ) • A.submatrix Fin.succ Fin.succ) := by
  have hs1 : ((Real.sqrt ((m : ℝ) + 1) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 two_pos).ne'
  have h2m : Real.sqrt (2 * ((m : ℝ) + 1)) = Real.sqrt 2 * Real.sqrt ((m : ℝ) + 1) :=
    Real.sqrt_mul (by norm_num) _
  have hherm : ∀ i j, star (A j i) = A i j := fun i j =>
    congrFun (congrFun hA i) j
  ext i j
  refine Fin.cases ?_ (fun k => ?_) i <;> refine Fin.cases ?_ (fun l => ?_) j
  · simp [borderMat, gueMat, gueBlock, firstRowSplit]
    field_simp
    ring
  · have hl : (0 : Fin (m + 1)) ≠ l.succ := (Fin.succ_ne_zero l).symm
    have hc : (starRingEnd ℂ) (A l.succ 0) = A 0 l.succ := hherm 0 l.succ
    simp [borderMat, gueMat, gueBlock, firstRowSplit, hl, h2m, hc, Complex.mk_eq_add_mul_I]
    field_simp
    ring
  · have hl : k.succ ≠ (0 : Fin (m + 1)) := Fin.succ_ne_zero k
    simp [borderMat, gueMat, gueBlock, firstRowSplit, hl, h2m, Complex.mk_eq_add_mul_I]
    field_simp
    ring
  · have hm : (0 : ℝ) < m := by
      have : 0 < m := Fin.pos k
      exact_mod_cast this
    have hsm : ((Real.sqrt (m : ℝ) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 hm).ne'
    have h2m' : Real.sqrt (2 * (m : ℝ)) = Real.sqrt 2 * Real.sqrt (m : ℝ) :=
      Real.sqrt_mul (by norm_num) _
    simp only [borderMat, gueMat, gueBlock, firstRowSplit, Matrix.of_apply, Matrix.cons_val_succ,
      Matrix.add_apply, Matrix.smul_apply, Matrix.submatrix_apply, smul_eq_mul, Nat.cast_add,
      Nat.cast_one, h2m, h2m', Fin.succ_inj, Fin.succ_lt_succ_iff, Complex.ofReal_mul]
    split_ifs <;> field_simp <;> ring

/-- The entries of `A + c V` as polynomials in the Gaussian coordinates. -/
private def gueFirstRow_entry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c : ℝ)
    (α β : Fin n) : MvPolynomial (Fin 1 × Fin n × Fin n) ℂ :=
  MvPolynomial.C (A α β) + MvPolynomial.C (c : ℂ) *
    (if α = β then MvPolynomial.X (0, α, α) * MvPolynomial.C (((Real.sqrt n : ℝ) : ℂ)⁻¹)
    else if α < β then
      (MvPolynomial.X (0, α, β) + MvPolynomial.C Complex.I * MvPolynomial.X (0, β, α)) *
        MvPolynomial.C (((Real.sqrt (2 * n) : ℝ) : ℂ)⁻¹)
    else
      (MvPolynomial.X (0, β, α) - MvPolynomial.C Complex.I * MvPolynomial.X (0, α, β)) *
        MvPolynomial.C (((Real.sqrt (2 * n) : ℝ) : ℂ)⁻¹))

private theorem gueFirstRow_eval_entry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c : ℝ)
    (ω : Ω n 1) (α β : Fin n) :
    MvPolynomial.eval (fun i => (ω i : ℂ)) (gueFirstRow_entry A c α β) =
      (A + (c : ℂ) • gueMat n ω) α β := by
  simp only [gueFirstRow_entry, gueMat, gueBlock, Matrix.add_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul, map_add, map_mul, MvPolynomial.eval_C]
  congr 2
  split_ifs <;> simp [div_eq_mul_inv, mul_comm]

/-- For Hermitian `A` and `c ≠ 0`, `A + c V` is almost surely invertible, `V` the GUE matrix of
(1.2) [eq:covariance]. -/
theorem ae_det_ne_zero_gueMat (n : ℕ) {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    {c : ℝ} (hc : c ≠ 0) : ∀ᵐ ω ∂(μ n 1), (A + (c : ℂ) • gueMat n ω).det ≠ 0 := by
  set P : MvPolynomial (Fin 1 × Fin n × Fin n) ℂ :=
    (Matrix.of fun α β => gueFirstRow_entry A c α β).det with hP
  have hev : ∀ ω : Ω n 1, MvPolynomial.eval (fun i => (ω i : ℂ)) P =
      (A + (c : ℂ) • gueMat n ω).det := by
    intro ω
    rw [hP, RingHom.map_det]
    congr 1
    ext α β
    exact gueFirstRow_eval_entry A c ω α β
  set B : Matrix (Fin n) (Fin n) ℂ := ((c⁻¹ : ℝ) : ℂ) • (1 - A) with hB
  have hBh : B.IsHermitian :=
    (Matrix.isHermitian_one.sub hA).smul (by simp [IsSelfAdjoint, Complex.conj_ofReal])
  set ω₀ : Ω n 1 := gueCoord n 1 (fun _ => B) with hω₀
  have hω₀B : gueMat n ω₀ = B := by
    have := gueBlock_gueCoord n 1 (fun _ => B) (fun _ => hBh)
    exact congrFun this 0
  have hdet : (A + (c : ℂ) • gueMat n ω₀).det = 1 := by
    rw [hω₀B, hB, smul_smul]
    have : (c : ℂ) * ((c⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ hc]; simp
    rw [this, one_smul]
    simp
  have : NullSingletonClass (gaussianReal (0 : ℝ) 1) :=
    nullSingletonClass_gaussianReal one_ne_zero
  have hnull := measure_zero_mvPolynomial (fun _ : Fin 1 × Fin n × Fin n => gaussianReal 0 1) P
    (fun i => ω₀ i) (by rw [hev, hdet]; exact one_ne_zero)
  rw [ae_iff]
  have h2 : {ω : Ω n 1 | ¬(A + (c : ℂ) • gueMat n ω).det ≠ 0} =
      {x | MvPolynomial.eval (fun i => (x i : ℂ)) P = 0} := by
    ext ω
    simp [hev]
  rw [h2]
  exact hnull

end LSBA
