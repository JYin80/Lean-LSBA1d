import Mathlib

/-!
# The block Anderson model

The sample space and the GUE blocks of (1.2) [eq:covariance], the cycle adjacency matrix and the
model `H_{g,W,L}` of (1.3) [eq:model] and (1.4) [eq:blockaction], and its normalized form with
`A_g` and `γ_g` of (5.1) [fo:eq:flow].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- Sample space of the `L` independent GUE blocks of size `W`, in real coordinates,
(1.2) [eq:covariance]. -/
abbrev Ω (W L : ℕ) : Type := Fin L × Fin W × Fin W → ℝ

/-- Product of standard real Gaussians on `Ω W L`. -/
def μ (W L : ℕ) : Measure (Ω W L) := Measure.pi fun _ => gaussianReal 0 1

instance (W L : ℕ) : IsProbabilityMeasure (μ W L) := by unfold μ; infer_instance

/-- Block `a` of the GUE matrix, (1.2) [eq:covariance]: diagonal `N(0,1/W)`, real and
imaginary parts of upper entries independent `N(0,1/(2W))`. -/
def gueBlock (W L : ℕ) (ω : Ω W L) (a : Fin L) : Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun α β =>
    if α = β then (ω (a, α, α) : ℂ) / Real.sqrt W
    else if α < β then ((ω (a, α, β) : ℂ) + Complex.I * ω (a, β, α)) / Real.sqrt (2 * W)
    else ((ω (a, β, α) : ℂ) - Complex.I * ω (a, α, β)) / Real.sqrt (2 * W)

/-- `A_L = S + S⁻¹` with `S` the cyclic shift of `ℤ_L`: `(A_L f)(a) = f(a+1) + f(a-1)`,
(1.3) [eq:model], for every `L`. -/
def cycleAdj (L : ℕ) : Matrix (Fin L) (Fin L) ℂ :=
  Matrix.of fun a b =>
    (if b.val = (a.val + 1) % L then 1 else 0) + (if a.val = (b.val + 1) % L then 1 else 0)

/-- Block-diagonal operator `diag(V_a : a ∈ ℤ_L)` on `ℂ^L ⊗ ℂ^W`. -/
def blockDiagOp {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then V p.1 p.2 q.2 else 0

/-- Deterministic block operator `(g A_L ⊗ I_W + diag V) / max{1,g}`, (1.3) [eq:model] and
(1.4) [eq:blockaction]. -/
def Hdet (g : ℝ) {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  ((max 1 g : ℝ)⁻¹ : ℂ) • ((g : ℂ) • (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) +
    blockDiagOp V)

/-- The random model `H_{g,W,L}` of (1.3) [eq:model]. -/
def Hmat (g : ℝ) (W L : ℕ) (ω : Ω W L) : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  Hdet g (gueBlock W L ω)

/-- `A_g = g A_L / max{1,g}`, the hopping part of (5.1) [fo:eq:flow]. -/
def Ag (g : ℝ) (L : ℕ) : Matrix (Fin L) (Fin L) ℂ := ((g / max 1 g : ℝ) : ℂ) • cycleAdj L

/-- `γ_g = max{1,g}^{-2}`, the variance rate in (5.1) [fo:eq:flow]. -/
def gammaG (g : ℝ) : ℝ := ((max 1 g) ^ 2)⁻¹

theorem gueBlock_isHermitian (W L : ℕ) (ω : Ω W L) (a : Fin L) :
    (gueBlock W L ω a).IsHermitian := by
  ext α β
  simp only [Matrix.conjTranspose_apply, gueBlock, Matrix.of_apply]
  rcases lt_trichotomy α β with h | rfl | h
  · simp [h.ne, h.ne', h, not_lt_of_gt h, Complex.conj_ofReal]
  · simp [Complex.conj_ofReal]
  · simp [h.ne, h.ne', h, not_lt_of_gt h, Complex.conj_ofReal, sub_eq_add_neg]

theorem cycleAdj_isHermitian (L : ℕ) : (cycleAdj L).IsHermitian := by
  ext a b
  simp only [Matrix.conjTranspose_apply, cycleAdj, Matrix.of_apply]
  split_ifs <;> simp

theorem blockDiagOp_isHermitian {W L : ℕ} {V : Fin L → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ a, (V a).IsHermitian) : (blockDiagOp V).IsHermitian := by
  ext ⟨a, α⟩ ⟨b, β⟩
  simp only [Matrix.conjTranspose_apply, blockDiagOp, Matrix.of_apply]
  by_cases h : a = b
  · subst h
    have := congrFun (congrFun (hV a) α) β
    simp only [Matrix.conjTranspose_apply] at this
    simp [this]
  · simp [h, Ne.symm h]

theorem Hdet_isHermitian (g : ℝ) {W L : ℕ} {V : Fin L → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ a, (V a).IsHermitian) : (Hdet g V).IsHermitian := by
  have hK : (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, (cycleAdj_isHermitian L).eq,
      Matrix.conjTranspose_one]
  ext p q
  have h1 := congrFun (congrFun hK p) q
  have h2 := congrFun (congrFun (blockDiagOp_isHermitian hV) p) q
  simp only [Matrix.conjTranspose_apply] at h1 h2
  simp only [Matrix.conjTranspose_apply, Hdet, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
    star_mul', star_add, h1, h2, star_inv₀, Complex.star_def, Complex.conj_ofReal]

theorem Hmat_isHermitian (g : ℝ) (W L : ℕ) (ω : Ω W L) : (Hmat g W L ω).IsHermitian :=
  Hdet_isHermitian g (gueBlock_isHermitian W L ω)

/-- Normalized form `H = A_g ⊗ I_W + √γ_g V` of (1.3) [eq:model], as used in (5.1) [fo:eq:flow]. -/
theorem Hdet_eq_normalized (g : ℝ) {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ) :
    Hdet g V = Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) +
      ((Real.sqrt (gammaG g) : ℝ) : ℂ) • blockDiagOp V := by
  have hm : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hs : Real.sqrt (gammaG g) = (max 1 g)⁻¹ := by
    rw [gammaG, Real.sqrt_inv, Real.sqrt_sq hm.le]
  ext p q
  simp only [Hdet, Ag, hs, Matrix.smul_apply, Matrix.add_apply, Matrix.kroneckerMap_apply,
    smul_eq_mul, Complex.ofReal_inv, Complex.ofReal_div]
  ring

end LSBA
