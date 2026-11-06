import LSBA.Spectral.Length

/-!
# Spectral counts

Multiplicities, diagonals of spectral projections, and the counts of eigenvalues used in (1.15)
[eq:rough-counting], (1.17) [eq:main], (1.18) [eq:simultaneous] and (2.12)
[uv:eq:lower-regions-output]; the counts do not depend on a choice of eigenbasis.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Multiplicity of the eigenvalue `ev k`. -/
def mult (ev : n → ℝ) (k : n) : ℕ := #(univ.filter fun j => ev j = ev k)

/-- Diagonal of the spectral projection onto the eigenspace of `ev k`. -/
def projDiag (ev : n → ℝ) (v : n → n → ℂ) (k : n) (i : n) : ℝ :=
  ∑ j ∈ univ.filter (fun j => ev j = ev k), ‖v j i‖ ^ 2

/-- Number of eigenvalues (with multiplicity) in `J`. -/
def countIn (A : Matrix n n ℂ) (J : Set ℝ) : ℕ :=
  if hA : A.IsHermitian then #(univ.filter fun k => hA.eigenvalues k ∈ J) else 0

/-- Bad count: eigenvalues in `J` that are multiple, or simple with `ℓ < r`. -/
def badCount (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (J : Set ℝ) (r : ℝ) : ℕ :=
  if hA : A.IsHermitian then
    #(univ.filter fun k => hA.eigenvalues k ∈ J ∧
      (2 ≤ mult hA.eigenvalues k ∨
        ((ellProf W L (projDiag hA.eigenvalues (fun j => ⇑(hA.eigenvectorBasis j)) k) : ℕ)
          : ℝ) < r))
  else 0

/-- Good count (lower half): simple eigenvalues in `J` with `r ≤ ℓ`. -/
def goodCount (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (J : Set ℝ) (r : ℝ) :
    ℕ :=
  if hA : A.IsHermitian then
    #(univ.filter fun k => hA.eigenvalues k ∈ J ∧ mult hA.eigenvalues k = 1 ∧
      r ≤ ((ellProf W L (projDiag hA.eigenvalues (fun j => ⇑(hA.eigenvectorBasis j)) k) : ℕ)
        : ℝ))
  else 0

/-- Empirical distribution function `N^{-1} #{k : λ_k ≤ x}`. -/
def empCDF (A : Matrix n n ℂ) (x : ℝ) : ℝ :=
  (countIn A (Set.Iic x) : ℝ) / (Fintype.card n : ℝ)

/-- Empirical spectral measure `N^{-1} Σ_k δ_{λ_k}`. -/
def empMeasure (A : Matrix n n ℂ) : Measure ℝ :=
  if hA : A.IsHermitian then (Fintype.card n : ℝ≥0∞)⁻¹ • ∑ k, Measure.dirac (hA.eigenvalues k)
  else 0

theorem countIn_eq_card_roots {A : Matrix n n ℂ} (hA : A.IsHermitian) (J : Set ℝ) :
    countIn A J = (A.charpoly.roots.filter fun z : ℂ => z.re ∈ J).card := by
  simp only [countIn, hA, ↓reduceDIte]
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.filter_map]
  simp [Finset.card_def, Finset.filter_val]

theorem projDiag_of_mult_eq_one (ev : n → ℝ) (v : n → n → ℂ) {k : n} (h : mult ev k = 1)
    (i : n) : projDiag ev v k i = ‖v k i‖ ^ 2 := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  have hk : k ∈ univ.filter (fun j => ev j = ev k) := by simp
  rw [ha, Finset.mem_singleton] at hk
  subst hk
  unfold projDiag
  rw [ha, Finset.sum_singleton]

theorem goodCount_add_badCount (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (J : Set ℝ) (r : ℝ) : goodCount W L A J r + badCount W L A J r = countIn A J := by
  by_cases hA : A.IsHermitian
  · simp only [goodCount, badCount, countIn, hA, ↓reduceDIte]
    set s : Finset (Fin L × Fin W) := univ.filter fun k => hA.eigenvalues k ∈ J with hs
    set ℓ : Fin L × Fin W → ℝ := fun k =>
      ((ellProf W L (projDiag hA.eigenvalues (fun j => ⇑(hA.eigenvectorBasis j)) k) : ℕ) : ℝ)
      with hℓ
    have h1 : (univ.filter fun k => hA.eigenvalues k ∈ J ∧ mult hA.eigenvalues k = 1 ∧
        r ≤ ℓ k) = s.filter fun k => mult hA.eigenvalues k = 1 ∧ r ≤ ℓ k := by
      rw [hs, Finset.filter_filter]
    have h2 : (univ.filter fun k => hA.eigenvalues k ∈ J ∧
        (2 ≤ mult hA.eigenvalues k ∨ ℓ k < r)) =
        s.filter fun k => ¬(mult hA.eigenvalues k = 1 ∧ r ≤ ℓ k) := by
      rw [hs, Finset.filter_filter]
      refine Finset.filter_congr fun k _ => ?_
      have hm : 1 ≤ mult hA.eigenvalues k :=
        Finset.card_pos.mpr ⟨k, by simp⟩
      refine and_congr_right fun _ => ?_
      constructor
      · rintro (h | h) ⟨h3, h4⟩
        · omega
        · exact absurd h4 (not_le.mpr h)
      · intro h
        by_cases h3 : mult hA.eigenvalues k = 1
        · exact Or.inr (not_le.mp fun h4 => h ⟨h3, h4⟩)
        · exact Or.inl (by omega)
    rw [h1, h2]
    exact Finset.card_filter_add_card_filter_not _
  · simp [goodCount, badCount, countIn, hA]

/-- On simple spectrum a unit eigenvector for `λ_k` is a unit-modulus multiple of the `k`-th vector
of the eigenbasis. -/
private lemma exists_unit_smul_eigenvectorBasis {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (hinj : Function.Injective hA.eigenvalues)
    (k : m) (φ : m → ℂ) (hφ : A *ᵥ φ = (hA.eigenvalues k : ℂ) • φ)
    (hn : ∑ x, ‖φ x‖ ^ 2 = 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ φ = c • ⇑(hA.eigenvectorBasis k) := by
  set b := hA.eigenvectorBasis with hb
  set y : EuclideanSpace ℂ m := WithLp.toLp 2 φ with hy
  have hip : ∀ j, inner ℂ (b j) y = φ ⬝ᵥ star (⇑(b j)) := fun j => by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
  have hzero : ∀ j, j ≠ k → inner ℂ (b j) y = 0 := by
    intro j hjk
    have h1 : (A *ᵥ φ) ⬝ᵥ star (⇑(b j)) = (hA.eigenvalues k : ℂ) * (φ ⬝ᵥ star (⇑(b j))) := by
      rw [hφ, smul_dotProduct, smul_eq_mul]
    have h2 : (A *ᵥ φ) ⬝ᵥ star (⇑(b j)) = (hA.eigenvalues j : ℂ) * (φ ⬝ᵥ star (⇑(b j))) := by
      rw [dotProduct_comm, Matrix.dotProduct_mulVec]
      have : star (⇑(b j)) ᵥ* A = (hA.eigenvalues j : ℂ) • star (⇑(b j)) := by
        have h3 := congrArg star (hA.mulVec_eigenvectorBasis j)
        rw [Matrix.star_mulVec, hA.eq] at h3
        rw [h3]
        simp
        rfl
      rw [this, smul_dotProduct, smul_eq_mul, dotProduct_comm]
    have h4 : ((hA.eigenvalues j : ℂ) - (hA.eigenvalues k : ℂ)) * (φ ⬝ᵥ star (⇑(b j))) = 0 := by
      rw [sub_mul, ← h1, ← h2, sub_self]
    have h5 : ((hA.eigenvalues j : ℂ) - (hA.eigenvalues k : ℂ)) ≠ 0 := by
      rw [sub_ne_zero]
      exact fun h => hjk (hinj (by exact_mod_cast h))
    rw [hip]
    exact (mul_eq_zero.mp h4).resolve_left h5
  refine ⟨inner ℂ (b k) y, ?_, ?_⟩
  · have h := b.sum_sq_norm_inner_right y
    rw [Finset.sum_eq_single k (fun j _ hjk => by rw [hzero j hjk]; simp) (by simp)] at h
    have h' : ‖y‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      simpa [hy] using hn
    rw [h'] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h
  · have h := b.sum_repr' y
    rw [Finset.sum_eq_single k (fun j _ hjk => by rw [hzero j hjk]; simp) (by simp)] at h
    funext x
    have := congrArg (fun z : EuclideanSpace ℂ m => z x) h
    exact this.symm

private lemma mult_eq_one_of_injective {m : Type*} [Fintype m] {ev : m → ℝ}
    (hinj : Function.Injective ev) (k : m) : mult ev k = 1 := by
  unfold mult
  rw [Finset.card_eq_one]
  refine ⟨k, ?_⟩
  ext j
  simp [hinj.eq_iff]

private lemma ell_eq_ellProf_projDiag {W L : ℕ} {A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hA : A.IsHermitian) (hinj : Function.Injective hA.eigenvalues)
    (ψ : Fin L × Fin W → Fin L × Fin W → ℂ)
    (hψ : ∀ k, A *ᵥ ψ k = (hA.eigenvalues k : ℂ) • ψ k) (hn : ∀ k, ∑ x, ‖ψ k x‖ ^ 2 = 1)
    (k : Fin L × Fin W) :
    ell W L (ψ k) =
      ellProf W L (projDiag hA.eigenvalues (fun j => ⇑(hA.eigenvectorBasis j)) k) := by
  obtain ⟨c, hc, hck⟩ := exists_unit_smul_eigenvectorBasis hA hinj k (ψ k) (hψ k) (hn k)
  have hp : projDiag hA.eigenvalues (fun j => ⇑(hA.eigenvectorBasis j)) k =
      fun i => ‖(hA.eigenvectorBasis k) i‖ ^ 2 :=
    funext fun i => projDiag_of_mult_eq_one _ _ (mult_eq_one_of_injective hinj k) i
  rw [hp, hck, ell_smul_of_norm_eq_one _ hc]
  rfl

theorem badCount_eq_of_injective {W L : ℕ} {A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hA : A.IsHermitian) (hinj : Function.Injective hA.eigenvalues)
    (ψ : Fin L × Fin W → Fin L × Fin W → ℂ)
    (hψ : ∀ k, A *ᵥ ψ k = (hA.eigenvalues k : ℂ) • ψ k) (hn : ∀ k, ∑ x, ‖ψ k x‖ ^ 2 = 1)
    (J : Set ℝ) (r : ℝ) :
    badCount W L A J r = #(univ.filter fun k => hA.eigenvalues k ∈ J ∧ (ell W L (ψ k) : ℝ) < r) := by
  simp only [badCount, hA, ↓reduceDIte]
  congr 1
  refine Finset.filter_congr fun k _ => ?_
  rw [ell_eq_ellProf_projDiag hA hinj ψ hψ hn k]
  have : ¬ 2 ≤ mult hA.eigenvalues k := by
    rw [mult_eq_one_of_injective hinj k]
    omega
  simp [this]

theorem empMeasure_Iic {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : ℝ) :
    (empMeasure A (Set.Iic x)).toReal = empCDF A x := by
  have hsum : (∑ k, Measure.dirac (hA.eigenvalues k)) (Set.Iic x) =
      (#(univ.filter fun k => hA.eigenvalues k ∈ Set.Iic x) : ℝ≥0∞) := by
    rw [Measure.finsetSum_apply]
    simp [Measure.dirac_apply' _ measurableSet_Iic, Set.indicator_apply, Finset.sum_boole]
  have hcount : countIn A (Set.Iic x) = #(univ.filter fun k => hA.eigenvalues k ∈ Set.Iic x) := by
    simp only [countIn, hA, ↓reduceDIte]
    rfl
  simp only [empMeasure, hA, ↓reduceDIte, Measure.smul_apply, hsum, smul_eq_mul, empCDF, hcount]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    div_eq_inv_mul]

end LSBA
