import LSBA.Upper.SmallGenerator
import LSBA.Upper.ChosenGenerator
import LSBA.Upper.RicChain
import LSBA.Gauss.BlockWindow

/-!
# The forward and right-cavity chains as Riccati chains

Section 9.1 [su:sec:construction] and Section 9.2 [su:sec:explicit-generator]. The active window
of `Ω W q` is the blocks `4, …, q - 2` (the inputs `V_5, …, V_{q-1}`); on it the graph coordinates
`R_j = (V_j - E - g² R_{j-1})⁻¹` started at `R_4` are the Riccati chain, with `R_{m+4}` its state
`m` and `R_{[m+4,5]}` its product of length `m`. The right-cavity window is the blocks
`q - 2, q - 3, …, 5` (the inputs `V_{q-1}, …, V_6`); on it `R←_{q-1-m}` is the state `m + 1` of
the Riccati chain started at `0`, and the right product `A = R←_{q-1} ⋯ R←_6` is the adjoint of
its product of length `q - 6`, as used for Lemma G.2 [us:lem:product] in (9.53)
[su:eq:retained-rank-moment]. Under the change (9.24) [su:eq:cut-generator-equivariance] by a
unitary `U`, every active state and product, the right-cavity inverses and products, `R̃` of
(3.4) [us:eq:cavity] and the retained projection of (9.15) [su:eq:retained-projection] are
conjugated by `U`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The active window: block `k` of the window is block `k + 4` of `Ω W q`, the input
`V_{k+5}`. -/
def actWin (q : ℕ) : Fin (q - 5) → Fin q := fun k => ⟨(k : ℕ) + 4, by omega⟩

/-- The right-cavity window: block `k` of the window is block `q - 2 - k` of `Ω W q`, the input
`V_{q-1-k}`. -/
def cavWin (q : ℕ) : Fin (q - 6) → Fin q := fun k => ⟨q - 2 - (k : ℕ), by omega⟩

private lemma ChainBridge_chartR_succ {W q : ℕ} (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ)
    (ω : Ω W q) {j : ℕ} (hj : 4 ≤ j) :
    chartR W g E q R ω (j + 1) =
      (blockSeq W q ω j - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • chartR W g E q R ω j)⁻¹ := by
  simp [chartR, not_lt.mpr hj]

private lemma ChainBridge_chartProd_succ {W q : ℕ} (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ)
    (ω : Ω W q) {j : ℕ} (hj : 4 ≤ j) :
    chartProd W g E q R ω (j + 1) = chartR W g E q R ω (j + 1) * chartProd W g E q R ω j := by
  simp [chartProd, not_lt.mpr hj]

/-- The forward bridge: for `m ≤ q - 5`, `R_{m+4}` and `R_{[m+4,5]}` are the state and the product
of length `m` of the Riccati chain on the active window, started at `R_4 = R`. -/
theorem chartR_eq_ricChain {W q : ℕ} (hq : 5 ≤ q) (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ)
    (ω : Ω W q) {m : ℕ} (hm : m ≤ q - 5) :
    chartR W g E q R ω (m + 4) = ricChain W g E (q - 5) R (windowSample (actWin q) ω) m ∧
      chartProd W g E q R ω (m + 4) = ricProd W g E (q - 5) R (windowSample (actWin q) ω) m := by
  induction m with
  | zero => exact ⟨by simp [chartR, ricChain], by simp [chartProd, ricProd]⟩
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hmq : m < q - 5 := by omega
    have hb : blockSeq W q ω (m + 4) =
        (if hj : m < q - 5 then gueBlock W (q - 5) (windowSample (actWin q) ω) ⟨m, hj⟩
          else 0) := by
      have h4 : m + 4 < q := by omega
      simp only [blockSeq, h4, hmq, ↓reduceDIte, gueBlock_windowSample]
      rfl
    have hs : chartR W g E q R ω (m + 1 + 4) =
        ricChain W g E (q - 5) R (windowSample (actWin q) ω) (m + 1) := by
      rw [show m + 1 + 4 = (m + 4) + 1 by omega, ChainBridge_chartR_succ g E R ω (by omega),
        ricChain, ih1, hb]
    refine ⟨hs, ?_⟩
    rw [show m + 1 + 4 = (m + 4) + 1 by omega, ChainBridge_chartProd_succ g E R ω (by omega),
      ricProd, ih2, show m + 4 + 1 = m + 1 + 4 by omega, hs]

/-- The right-cavity bridge: for `m ≤ q - 7`, `R←_{q-1-m}` is the state `m + 1` of the Riccati
chain on the right-cavity window started at `0`. -/
theorem cavR_eq_ricChain {W q : ℕ} (hq : 7 ≤ q) (g E : ℝ) (ω : Ω W q) {m : ℕ} (hm : m ≤ q - 7) :
    cavR W g E q ω m = ricChain W g E (q - 6) 0 (windowSample (cavWin q) ω) (m + 1) := by
  induction m with
  | zero =>
    have h0 : blockSeq W q ω (q - 2) =
        (if hj : 0 < q - 6 then gueBlock W (q - 6) (windowSample (cavWin q) ω) ⟨0, hj⟩
          else 0) := by
      have hq2 : q - 2 < q := by omega
      have hq6 : 0 < q - 6 := by omega
      simp only [blockSeq, hq2, hq6, ↓reduceDIte, gueBlock_windowSample]
      exact congrArg (gueBlock W q ω) (Fin.ext (show q - 2 = q - 2 - 0 by omega))
    simp [cavR, ricChain, h0]
  | succ m ih =>
    have hmq : m + 1 < q - 6 := by omega
    have hb : blockSeq W q ω (q - 3 - m) =
        (if hj : m + 1 < q - 6 then gueBlock W (q - 6) (windowSample (cavWin q) ω) ⟨m + 1, hj⟩
          else 0) := by
      have hq3 : q - 3 - m < q := by omega
      simp only [blockSeq, hq3, hmq, ↓reduceDIte, gueBlock_windowSample]
      exact congrArg (gueBlock W q ω) (Fin.ext (show q - 3 - m = q - 2 - (m + 1) by omega))
    rw [cavR, ricChain, ih (by omega), hb]

/-- The right product `A = R←_{q-1} ⋯ R←_6` is the adjoint of the product of length `q - 6` of
the Riccati chain on the right-cavity window started at `0`. -/
theorem cavProd_eq_ricProd {W q : ℕ} (hq : 7 ≤ q) (g E : ℝ) (ω : Ω W q) :
    (cavProd W g E q ω (q - 6))ᴴ =
      ricProd W g E (q - 6) 0 (windowSample (cavWin q) ω) (q - 6) := by
  have key : ∀ m, m ≤ q - 6 →
      (cavProd W g E q ω m)ᴴ = ricProd W g E (q - 6) 0 (windowSample (cavWin q) ω) m := by
    intro m
    induction m with
    | zero => intro _; simp [cavProd, ricProd]
    | succ m ih =>
      intro hm
      have hc : cavR W g E q ω m = ricChain W g E (q - 6) 0 (windowSample (cavWin q) ω) (m + 1) :=
        cavR_eq_ricChain hq g E ω (by omega)
      have hH : (cavR W g E q ω m)ᴴ = cavR W g E q ω m := by
        rw [hc]
        exact (ricChain_isHermitian (Matrix.isHermitian_zero) _ (m + 1)).eq
      rw [cavProd, Matrix.conjTranspose_mul, hH, ih (by omega), hc, ricProd]
  exact key (q - 6) le_rfl

section ChainBridgeConj

variable {W q : ℕ} {g E : ℝ} {R U : Matrix (Fin W) (Fin W) ℂ}

private lemma ChainBridge_conj_mul (hU : Uᴴ * U = 1) (M N : Matrix (Fin W) (Fin W) ℂ) :
    U * (M * N) * Uᴴ = U * M * Uᴴ * (U * N * Uᴴ) := by
  calc U * (M * N) * Uᴴ = U * M * (Uᴴ * U) * N * Uᴴ := by
        rw [hU, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = U * M * Uᴴ * (U * N * Uᴴ) := by simp only [Matrix.mul_assoc]

private lemma ChainBridge_conj_add (M N : Matrix (Fin W) (Fin W) ℂ) :
    U * (M + N) * Uᴴ = U * M * Uᴴ + U * N * Uᴴ := by
  rw [Matrix.mul_add, Matrix.add_mul]

private lemma ChainBridge_conj_sub (M N : Matrix (Fin W) (Fin W) ℂ) :
    U * (M - N) * Uᴴ = U * M * Uᴴ - U * N * Uᴴ := by
  rw [Matrix.mul_sub, Matrix.sub_mul]

private lemma ChainBridge_conj_one (hU' : U * Uᴴ = 1) :
    U * (1 : Matrix (Fin W) (Fin W) ℂ) * Uᴴ = 1 := by
  rw [Matrix.mul_one, hU']

private lemma ChainBridge_conj_inv (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (M : Matrix (Fin W) (Fin W) ℂ) : (U * M * Uᴴ)⁻¹ = U * M⁻¹ * Uᴴ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv hU,
    Matrix.inv_eq_left_inv hU', Matrix.mul_assoc]

private lemma ChainBridge_conj_conjTranspose (M : Matrix (Fin W) (Fin W) ℂ) :
    (U * M * Uᴴ)ᴴ = U * Mᴴ * Uᴴ := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

private lemma ChainBridge_conj_herm {M : Matrix (Fin W) (Fin W) ℂ} (hM : M.IsHermitian) :
    (U * M * Uᴴ).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [ChainBridge_conj_conjTranspose, hM.eq]

private lemma ChainBridge_conj_affine (hU' : U * Uᴴ = 1) (B X : Matrix (Fin W) (Fin W) ℂ)
    (c d : ℂ) : U * B * Uᴴ - c • 1 - d • (U * X * Uᴴ) = U * (B - c • 1 - d • X) * Uᴴ := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    hU']

private lemma ChainBridge_flagProj_conj (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (T S : Matrix (Fin W) (Fin W) ℂ) :
    flagProj (U * T * Uᴴ) (U * S * Uᴴ) = U * flagProj T S * Uᴴ := by
  unfold flagProj
  simp only [ChainBridge_conj_mul hU, ChainBridge_conj_add, ChainBridge_conj_sub,
    ChainBridge_conj_one hU', ← ChainBridge_conj_inv hU hU', ← ChainBridge_conj_conjTranspose]

private lemma ChainBridge_gsq_smul_herm (g : ℝ) {M : Matrix (Fin W) (Fin W) ℂ}
    (hM : M.IsHermitian) : (((g : ℂ) ^ 2) • M).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hM.eq]
  simp

private lemma ChainBridge_gueBlock_srcAct (hRh : R.IsHermitian) (ω : Ω W q) :
    gueBlock W q (srcAct W q g R U ω) = fun i : Fin q =>
      if (i : ℕ) = 4 then U * (gueBlock W q ω i - ((g : ℂ) ^ 2) • R) * Uᴴ + ((g : ℂ) ^ 2) • R
      else if 5 ≤ (i : ℕ) ∧ (i : ℕ) + 2 ≤ q then U * gueBlock W q ω i * Uᴴ
      else gueBlock W q ω i := by
  unfold srcAct
  refine gueBlock_gueCoord W q _ fun i => ?_
  split_ifs
  · exact (ChainBridge_conj_herm
      ((gueBlock_isHermitian W q ω i).sub (ChainBridge_gsq_smul_herm g hRh))).add
      (ChainBridge_gsq_smul_herm g hRh)
  · exact ChainBridge_conj_herm (gueBlock_isHermitian W q ω i)
  · exact gueBlock_isHermitian W q ω i

private lemma ChainBridge_blockSeq_srcAct_four (hRh : R.IsHermitian) (ω : Ω W q) (hq : 4 < q) :
    blockSeq W q (srcAct W q g R U ω) 4 =
      U * (blockSeq W q ω 4 - ((g : ℂ) ^ 2) • R) * Uᴴ + ((g : ℂ) ^ 2) • R := by
  simp only [blockSeq, hq, ↓reduceDIte, ChainBridge_gueBlock_srcAct hRh]
  simp

private lemma ChainBridge_blockSeq_srcAct_mid (hRh : R.IsHermitian) (ω : Ω W q) {k : ℕ}
    (h5 : 5 ≤ k) (hk : k + 2 ≤ q) :
    blockSeq W q (srcAct W q g R U ω) k = U * blockSeq W q ω k * Uᴴ := by
  have hkq : k < q := by omega
  have h4 : k ≠ 4 := by omega
  simp only [blockSeq, hkq, ↓reduceDIte, ChainBridge_gueBlock_srcAct hRh]
  simp [h4, h5, hk]

private lemma ChainBridge_chartR_four (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) :
    chartR W g E q R ω 4 = R := by
  simp [chartR]

private lemma ChainBridge_chartR_srcAct (hRh : R.IsHermitian) (hU : Uᴴ * U = 1)
    (hU' : U * Uᴴ = 1) (ω : Ω W q) : ∀ i, 5 + i ≤ q - 1 →
      chartR W g E q R (srcAct W q g R U ω) (5 + i) = U * chartR W g E q R ω (5 + i) * Uᴴ := by
  intro i
  induction i with
  | zero =>
    intro hi
    rw [show 5 + 0 = 4 + 1 from rfl, ChainBridge_chartR_succ g E R _ le_rfl,
      ChainBridge_chartR_succ g E R _ le_rfl, ChainBridge_chartR_four, ChainBridge_chartR_four,
      ChainBridge_blockSeq_srcAct_four hRh ω (by omega), ← ChainBridge_conj_inv hU hU']
    congr 1
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      hU']
    abel
  | succ i ih =>
    intro hi
    rw [show 5 + (i + 1) = (5 + i) + 1 by omega, ChainBridge_chartR_succ g E R _ (by omega),
      ChainBridge_chartR_succ g E R _ (by omega),
      ChainBridge_blockSeq_srcAct_mid hRh ω (by omega) (by omega), ih (by omega),
      ChainBridge_conj_affine hU', ChainBridge_conj_inv hU hU']

private lemma ChainBridge_chartProd_srcAct (hRh : R.IsHermitian) (hU : Uᴴ * U = 1)
    (hU' : U * Uᴴ = 1) (ω : Ω W q) : ∀ j, j ≤ q - 1 →
      chartProd W g E q R (srcAct W q g R U ω) j = U * chartProd W g E q R ω j * Uᴴ := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [chartProd]
    exact (ChainBridge_conj_one hU').symm
  | succ j ih =>
    intro hj
    by_cases hj4 : j < 4
    · simp only [chartProd, hj4, ↓reduceIte]
      exact (ChainBridge_conj_one hU').symm
    · simp only [chartProd, hj4, ↓reduceIte]
      have h5 := ChainBridge_chartR_srcAct (g := g) (E := E) hRh hU hU' ω (j + 1 - 5) (by omega)
      rw [show 5 + (j + 1 - 5) = j + 1 by omega] at h5
      rw [h5, ih (by omega), ← ChainBridge_conj_mul hU]

private lemma ChainBridge_cavR_srcAct (hq : 7 ≤ q) (hRh : R.IsHermitian) (hU : Uᴴ * U = 1)
    (hU' : U * Uᴴ = 1) (ω : Ω W q) : ∀ m, m ≤ q - 7 →
      cavR W g E q (srcAct W q g R U ω) m = U * cavR W g E q ω m * Uᴴ := by
  intro m
  induction m with
  | zero =>
    intro _
    simp only [cavR]
    rw [ChainBridge_blockSeq_srcAct_mid hRh ω (by omega) (by omega),
      ← ChainBridge_conj_inv hU hU']
    congr 1
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      hU']
  | succ m ih =>
    intro hm
    simp only [cavR]
    rw [ChainBridge_blockSeq_srcAct_mid hRh ω (by omega) (by omega), ih (by omega),
      ChainBridge_conj_affine hU', ChainBridge_conj_inv hU hU']

private lemma ChainBridge_cavProd_srcAct (hq : 7 ≤ q) (hRh : R.IsHermitian) (hU : Uᴴ * U = 1)
    (hU' : U * Uᴴ = 1) (ω : Ω W q) : ∀ m, m ≤ q - 6 →
      cavProd W g E q (srcAct W q g R U ω) m = U * cavProd W g E q ω m * Uᴴ := by
  intro m
  induction m with
  | zero =>
    intro _
    simp only [cavProd]
    exact (ChainBridge_conj_one hU').symm
  | succ m ih =>
    intro hm
    simp only [cavProd]
    rw [ih (by omega), ChainBridge_cavR_srcAct hq hRh hU hU' ω m (by omega),
      ← ChainBridge_conj_mul hU]

private lemma ChainBridge_cavRes_srcAct (hq : 7 ≤ q) (hRh : R.IsHermitian) (hU : Uᴴ * U = 1)
    (hU' : U * Uᴴ = 1) (ω : Ω W q) :
    cavRes W g E q R (srcAct W q g R U ω) = U * cavRes W g E q R ω * Uᴴ := by
  unfold cavRes
  rw [ChainBridge_blockSeq_srcAct_four hRh ω (by omega),
    ChainBridge_cavR_srcAct hq hRh hU hU' ω (q - 7) le_rfl, ← ChainBridge_conj_inv hU hU']
  congr 1
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    hU']
  abel

end ChainBridgeConj

/-- Under the change (9.24) [su:eq:cut-generator-equivariance] by a unitary `U` at a Hermitian
`R_4 = R`: `R_j`, `R_{[j,5]}` (`5 ≤ j ≤ q - 1`), `R←_{q-1-m}` (`m ≤ q - 7`), `A`, `R̃`,
`1_{(t², ∞)}(A* A)` and the retained projection `Q` are conjugated by `U`. -/
theorem srcAct_conj {W q : ℕ} (hq : 7 ≤ q) {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    (hR : R.IsHermitian) {U : Matrix (Fin W) (Fin W) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin W) ℂ)
    (ω : Ω W q) (t : ℝ) :
    (∀ j, 5 ≤ j → j ≤ q - 1 →
      chartR W g E q R (srcAct W q g R U ω) j = U * chartR W g E q R ω j * Uᴴ ∧
        chartProd W g E q R (srcAct W q g R U ω) j = U * chartProd W g E q R ω j * Uᴴ) ∧
    (∀ m, m ≤ q - 7 → cavR W g E q (srcAct W q g R U ω) m = U * cavR W g E q ω m * Uᴴ) ∧
    cavProd W g E q (srcAct W q g R U ω) (q - 6) = U * cavProd W g E q ω (q - 6) * Uᴴ ∧
    cavRes W g E q R (srcAct W q g R U ω) = U * cavRes W g E q R ω * Uᴴ ∧
    retSpec W g E q t (srcAct W q g R U ω) = U * retSpec W g E q t ω * Uᴴ ∧
    retProj W g E q R t (srcAct W q g R U ω) = U * retProj W g E q R t ω * Uᴴ := by
  have hU1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hU2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hS : retSpec W g E q t (srcAct W q g R U ω) = U * retSpec W g E q t ω * Uᴴ := by
    unfold retSpec
    rw [ChainBridge_cavProd_srcAct hq hR hU1 hU2 ω (q - 6) le_rfl,
      ChainBridge_conj_conjTranspose, ← ChainBridge_conj_mul hU1,
      specProj_conj (Matrix.isHermitian_conjTranspose_mul_self _) hU]
  refine ⟨fun j hj5 hjq => ⟨?_, ?_⟩, fun m hm => ?_, ?_, ?_, hS, ?_⟩
  · have h5 := ChainBridge_chartR_srcAct (g := g) (E := E) hR hU1 hU2 ω (j - 5) (by omega)
    rwa [show 5 + (j - 5) = j by omega] at h5
  · exact ChainBridge_chartProd_srcAct hR hU1 hU2 ω j hjq
  · exact ChainBridge_cavR_srcAct hq hR hU1 hU2 ω m hm
  · exact ChainBridge_cavProd_srcAct hq hR hU1 hU2 ω (q - 6) le_rfl
  · exact ChainBridge_cavRes_srcAct hq hR hU1 hU2 ω
  · unfold retProj
    rw [ChainBridge_cavRes_srcAct hq hR hU1 hU2 ω, hS, ChainBridge_flagProj_conj hU1 hU2]

end LSBA
