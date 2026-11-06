import LSBA.Prop.Ward
import LSBA.Primitive.Ward
import LSBA.Loop.Projection
import LSBA.Loop.Generator
import LSBA.Prop.Objects

/-!
# The signed Ward row of a loop error

The row (C.34) [gc:eq:row] of the loop error of an alternating word, from the Ward identity
(5.11) [gc:eq:ward], and the loop error of length one.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- Splitting off the last label of a word turns the row sum into a sum over the shorter words
with the first label equal to `c₀`. -/
private theorem wardRow_rowSum_snoc {L k : ℕ} (hk : 1 ≤ k) (F : (Fin (k + 1) → Fin L) → ℂ)
    (c₀ : Fin L) :
    rowSum F c₀ =
      ∑ a : Fin k → Fin L, if a ⟨0, hk⟩ = c₀ then ∑ c : Fin L, F (Fin.snoc a c) else 0 := by
  unfold rowSum
  rw [← (Fin.snocEquiv (fun _ : Fin (k + 1) => Fin L)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h0 : ∀ c : Fin L, (Fin.snoc a c : Fin (k + 1) → Fin L) 0 = a ⟨0, hk⟩ := by
    intro c
    have : (0 : Fin (k + 1)) = Fin.castSucc ⟨0, hk⟩ := rfl
    rw [this, Fin.snoc_castSucc]
  simp only [Fin.snocEquiv_apply, h0]
  split_ifs <;> simp

/-- The signed Ward row above (C.34) [gc:eq:row] of a loop error: for a word of length `k + 1`
whose last sign is opposite to its first, the sum of `D_{k+1}` over all labels but the first is
`(2iWη_u)⁻¹ Σ [D_k(σ⁺) - D_k(σ⁻)]`, summed over all labels of length `k` but the first, by the
Ward identity (5.11) [gc:eq:ward] for the loops and for the primitive loops. -/
theorem loopErr_rowSum_ward (g E : ℝ) (m : ℂ) {W L : ℕ} (hW : 1 ≤ W) (hL : 3 ≤ L)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hM : M.IsHermitian) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (k : ℕ) (hk : 1 ≤ k)
    (τ : Fin k → Bool) (s : Bool) (c₀ : Fin L) :
    rowSum (n := k) (fun b => resLoop g E m b (Fin.snoc (Function.update τ ⟨0, hk⟩ s) (!s)) u M -
        primLoop g W L E m u b (Fin.snoc (Function.update τ ⟨0, hk⟩ s) (!s))) c₀ =
      ((2 * Complex.I * (W : ℂ) * (etaChar g m u : ℂ)))⁻¹ *
        ∑ b : Fin k → Fin L, if b ⟨0, hk⟩ = c₀ then
          (resLoop g E m b (Function.update τ ⟨0, hk⟩ true) u M -
              primLoop g W L E m u b (Function.update τ ⟨0, hk⟩ true)) -
            (resLoop g E m b (Function.update τ ⟨0, hk⟩ false) u M -
              primLoop g W L E m u b (Function.update τ ⟨0, hk⟩ false))
        else 0 := by
  have hγ : 0 < gammaG g := by
    unfold gammaG
    have : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
    positivity
  have hzim : (zChar g E m u).im = etaChar g m u := by
    simp [zChar, etaChar]
  have hz : 0 < (zChar g E m u).im := by
    rw [hzim]
    unfold etaChar
    have : 0 < 1 - u := by linarith
    have := hm.1
    positivity
  rw [wardRow_rowSum_snoc hk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rw [Finset.sum_sub_distrib]
    have h1 := loopTr_ward hW M hM (zChar g E m u) hz k hk a τ s
    have h2 := primLoop_ward g W L hW hL E m hm u hu0 hu1 k hk a τ s
    simp only [resLoop]
    rw [h1, h2, hzim]
    ring
  · simp

/-- The loop error of length one at a root of (5.2) [fo:eq:dyson-family]:
`D_1(a, +) = ⟨G_u - M⟩_{aa}` and `D_1(a, -)` is its conjugate, since `𝒦_1 = m^σ` and
`(M_B)_{aa} = m` (the averaged component of (5.22) [gc:eq:one-step-input]). -/
theorem flowErr_one (W : ℕ) (hW : 1 ≤ W) (p : FlowPt) (hL : 3 ≤ p.L)
    (hm : IsDysonRootV (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E)) (a : Fin p.L)
    (s : Bool) (ω : Ω W p.L) :
    flowErr W p ![a] ![s] ω =
      if s then blockTr (flowG W p ω - flowM W p) a a
      else star (blockTr (flowG W p ω - flowM W p) a a) := by
  have hMt : blockTr (flowM W p) a a = mRoot p.g p.L p.E := by
    have h := loopTr_one_dysonMat p.g p.E W p.L hW (by omega) _ hm a true
    have h1 := loopTr_one (flowM W p) a
    simp only [flowM] at h1 ⊢
    simp only [ite_true] at h
    exact h1.symm.trans h
  have hprim : primLoop p.g W p.L p.E (mRoot p.g p.L p.E) p.u ![a] ![s] =
      if s then mRoot p.g p.L p.E else star (mRoot p.g p.L p.E) := by
    simp [primLoop, primK, primF]
  have hBstar : ∀ X : Matrix (Fin p.L × Fin W) (Fin p.L × Fin W) ℂ,
      loopTr X ![a] ![false] = star (blockTr X a a) := by
    intro X
    have h : loopTr X ![a] ![false] = loopTr Xᴴ ![a] ![true] := by simp [loopTr, sgnMat]
    rw [h, loopTr_one]
    simp [blockTr, Matrix.conjTranspose_apply, star_sum, star_mul']
  have hsub : blockTr (flowG W p ω - flowM W p) a a =
      blockTr (flowG W p ω) a a - mRoot p.g p.L p.E := by
    rw [← hMt]
    simp [blockTr, Matrix.sub_apply, Finset.sum_sub_distrib, mul_sub]
  unfold flowErr
  rw [hprim, hsub]
  cases s
  · rw [hBstar]
    simp
  · rw [loopTr_one]
    simp [blockTr]

end LSBA
