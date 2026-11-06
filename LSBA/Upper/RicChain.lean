import LSBA.Gauss.GUELaw

/-!
# Riccati chains on a batch of GUE blocks

The recursion `R_j = (V_j - E - g² R_{j-1})⁻¹` of (9.2) [su:eq:transported-normal] on the blocks
`V_1, …, V_h` of `Ω W h`, started at a deterministic state `R_0 = R`, and the products
`R_j ⋯ R_1`. With `R = R_4` and the blocks `V_5, …, V_{h+4}` this is the chain of Lemma G.2
[us:lem:product] and Lemma G.3 [nc:lem:buffer]; with `R = 0` and the blocks in reverse order it
is the right-cavity chain of Section 9.2 [su:sec:explicit-generator]. Lean's inverse is total; the
chain is Hermitian for Hermitian `R`, and conjugating `R` and every block by a unitary `U`
conjugates every state and product by `U`, so events defined by spectral data of the chain are
invariant under simultaneous conjugation.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The Riccati chain of (9.2) [su:eq:transported-normal] on the blocks of `Ω W h`, started at
`R`: `ricChain … 0 = R` and `ricChain … (j + 1) = (V_j - E - g² ricChain … j)⁻¹`, where `V_j` is
block `j` (and `0` from `j = h` on). -/
def ricChain (W : ℕ) (g E : ℝ) (h : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W h) :
    ℕ → Matrix (Fin W) (Fin W) ℂ
  | 0 => R
  | j + 1 => ((if hj : j < h then gueBlock W h ω ⟨j, hj⟩ else 0) - (E : ℂ) • 1 -
      ((g : ℂ) ^ 2) • ricChain W g E h R ω j)⁻¹

/-- The product `ricChain … j ⋯ ricChain … 1` (`1` for `j = 0`). -/
def ricProd (W : ℕ) (g E : ℝ) (h : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W h) :
    ℕ → Matrix (Fin W) (Fin W) ℂ
  | 0 => 1
  | j + 1 => ricChain W g E h R ω (j + 1) * ricProd W g E h R ω j

/-- For Hermitian `R`, every state of the chain is Hermitian. -/
theorem ricChain_isHermitian {W h : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    (hR : R.IsHermitian) (ω : Ω W h) (j : ℕ) : (ricChain W g E h R ω j).IsHermitian := by
  induction j with
  | zero => exact hR
  | succ j ih =>
    rw [ricChain]
    refine Matrix.IsHermitian.inv ?_
    have hV : (if hj : j < h then gueBlock W h ω ⟨j, hj⟩ else 0 :
        Matrix (Fin W) (Fin W) ℂ).IsHermitian := by
      split_ifs with hj
      · exact gueBlock_isHermitian W h ω _
      · exact Matrix.isHermitian_zero
    have hE : ((E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)).IsHermitian := by
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def,
        Complex.conj_ofReal]
    have hg : (((g : ℂ) ^ 2) • ricChain W g E h R ω j).IsHermitian := by
      unfold Matrix.IsHermitian at ih ⊢
      rw [Matrix.conjTranspose_smul, ih, Complex.star_def, map_pow, Complex.conj_ofReal]
    exact (hV.sub hE).sub hg

/-- Unitary equivariance: conjugating `R` and every block by `U` conjugates every state and every
product of the chain by `U`. -/
theorem ricChain_conj (W : ℕ) (g E : ℝ) (h : ℕ) (R : Matrix (Fin W) (Fin W) ℂ)
    (U : Matrix.unitaryGroup (Fin W) ℂ) (ω : Ω W h) (j : ℕ) :
    ricChain W g E h ((U : Matrix (Fin W) (Fin W) ℂ) * R * star (U : Matrix (Fin W) (Fin W) ℂ))
        (conjMap W h U ω) j =
      (U : Matrix (Fin W) (Fin W) ℂ) * ricChain W g E h R ω j *
        star (U : Matrix (Fin W) (Fin W) ℂ) ∧
    ricProd W g E h ((U : Matrix (Fin W) (Fin W) ℂ) * R * star (U : Matrix (Fin W) (Fin W) ℂ))
        (conjMap W h U ω) j =
      (U : Matrix (Fin W) (Fin W) ℂ) * ricProd W g E h R ω j *
        star (U : Matrix (Fin W) (Fin W) ℂ) := by
  have hUU : (U : Matrix (Fin W) (Fin W) ℂ) * star (U : Matrix (Fin W) (Fin W) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.2
  have hUU' : star (U : Matrix (Fin W) (Fin W) ℂ) * (U : Matrix (Fin W) (Fin W) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.2
  have hinv : ∀ A : Matrix (Fin W) (Fin W) ℂ,
      ((U : Matrix (Fin W) (Fin W) ℂ) * A * star (U : Matrix (Fin W) (Fin W) ℂ))⁻¹ =
        (U : Matrix (Fin W) (Fin W) ℂ) * A⁻¹ * star (U : Matrix (Fin W) (Fin W) ℂ) := by
    intro A
    have h1 : ((U : Matrix (Fin W) (Fin W) ℂ))⁻¹ = star (U : Matrix (Fin W) (Fin W) ℂ) :=
      Matrix.inv_eq_right_inv hUU
    have h2 : (star (U : Matrix (Fin W) (Fin W) ℂ))⁻¹ = (U : Matrix (Fin W) (Fin W) ℂ) :=
      Matrix.inv_eq_right_inv hUU'
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, h1, h2, Matrix.mul_assoc]
  induction j with
  | zero => exact ⟨by simp [ricChain], by simp [ricProd, hUU]⟩
  | succ j ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hs : ricChain W g E h
        ((U : Matrix (Fin W) (Fin W) ℂ) * R * star (U : Matrix (Fin W) (Fin W) ℂ))
        (conjMap W h U ω) (j + 1) =
        (U : Matrix (Fin W) (Fin W) ℂ) * ricChain W g E h R ω (j + 1) *
          star (U : Matrix (Fin W) (Fin W) ℂ) := by
      rw [ricChain, ricChain, ih1, ← hinv]
      congr 1
      have hV : (if hj : j < h then gueBlock W h (conjMap W h U ω) ⟨j, hj⟩ else 0 :
          Matrix (Fin W) (Fin W) ℂ) =
          (U : Matrix (Fin W) (Fin W) ℂ) *
            (if hj : j < h then gueBlock W h ω ⟨j, hj⟩ else 0) *
            star (U : Matrix (Fin W) (Fin W) ℂ) := by
        split_ifs with hj
        · exact gueBlock_conjMap W h U ω _
        · simp
      rw [hV]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, hUU]
    refine ⟨hs, ?_⟩
    rw [ricProd, ricProd, hs, ih2]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star (U : Matrix (Fin W) (Fin W) ℂ)), hUU', Matrix.one_mul]

end LSBA
