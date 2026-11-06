import LSBA.Averaging.LoopRows
import LSBA.Averaging.LoopField
import LSBA.Flow.MomentIter
import LSBA.Averaging.Branch
import LSBA.Sampling.Lemma48

/-!
# One step of the loop-error induction of Lemma 5.6 [fo:prop:inputs]

The deterministic rates of the loop-error hierarchy (5.17) [fo:eq:error-hierarchy] on a good set,
the
induction step in the loop length for the loop-error component of (5.22) [gc:eq:one-step-input] at
fixed time on the large-coupling family of Lemma 5.6 [fo:prop:inputs], and the length-one case.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Common facts -/

/-- `γ_g > 0`. -/
private theorem loopsStep_gammaG_pos (g : ℝ) : 0 < gammaG g := by
  unfold gammaG
  have : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  positivity

/-- `γ_g = g⁻²` for `g ≥ 1`. -/
private theorem loopsStep_gammaG_eq {g : ℝ} (hg : 1 ≤ g) : gammaG g = (g ^ 2)⁻¹ := by
  unfold gammaG; rw [max_eq_right hg]

/-! ### Deterministic rates of the loop-error hierarchy -/

section GenRates

/-- The primitive loops satisfy (5.10) [fo:eq:primitive] at every `u ∈ (-1, 1)`, all lengths. -/
private theorem loopsStep_primDeriv (g : ℝ) (W L : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ L) (E : ℝ) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (u : ℝ) (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    IsPrimDeriv (gammaG g) W L (fun r n b τ => primLoop g W L E m r (k := n) b τ) u := by
  intro n a σ
  rcases n with _ | _ | n
  · have h0 : cutSumFam (fun n b τ => primLoop g W L E m u (k := n) b τ) a σ = 0 := by
      simp [cutSumFam]
    rw [h0, mul_zero]
    exact hasDerivAt_const u (primLoop g W L E m 0 a σ)
  · have h1 : cutSumFam (fun n b τ => primLoop g W L E m u (k := n) b τ) a σ = 0 := by
      simp [cutSumFam]
    rw [h1, mul_zero]
    exact hasDerivAt_const u (primLoop g W L E m 0 a σ)
  · exact primLoop_hasDerivAt g W L hW hL E m hm u hu (by omega) a σ

/-- The free label of Cut_L is at position `i`. -/
private theorem loopsStep_cutLLab_update {L k : ℕ} (a : Fin k → Fin L) (i j : Fin k)
    (c' c : Fin L) :
    Function.update (cutLLab a i j c') ⟨i.val, by have := j.2; omega⟩ c = cutLLab a i j c := by
  funext p
  by_cases h : p = ⟨i.val, by have := j.2; omega⟩
  · subst h; simp [cutLLab]
  · rw [Function.update_of_ne h]
    have hp : p.val ≠ i.val := fun h' => h (Fin.ext h')
    simp [cutLLab, hp]

/-- The free label of Cut_R is at the last position `j - i`. -/
private theorem loopsStep_cutRLab_update {L k : ℕ} (a : Fin k → Fin L) (i j : Fin k)
    (c' c : Fin L) :
    Function.update (cutRLab a i j c') ⟨j.val - i.val, by omega⟩ c = cutRLab a i j c := by
  funext p
  by_cases h : p = ⟨j.val - i.val, by omega⟩
  · subst h; simp [cutRLab]
  · rw [Function.update_of_ne h]
    have hp : p.val ≠ j.val - i.val := fun h' => h (Fin.ext h')
    have hp' : p.val < j.val - i.val := by have := p.2; omega
    simp [cutRLab, hp']

/-- Updating the second label of a pair. -/
private theorem loopsStep_update_pair {L : ℕ} (x y c : Fin L) :
    Function.update (![x, y] : Fin 2 → Fin L) 1 c = ![x, c] := by
  funext p
  fin_cases p <;> rfl

/-- `γW |Σ_c f_c h_c| ≤ A B` from `γW Σ_c |f_c| ≤ A` and `|h_c| ≤ B`. -/
private theorem loopsStep_sum_mul_le {L : ℕ} {γW A B : ℝ} (hγW : 0 ≤ γW) (f h : Fin L → ℂ)
    (hf : γW * ∑ c, ‖f c‖ ≤ A) (hB : ∀ c, ‖h c‖ ≤ B) (hB0 : 0 ≤ B) :
    γW * ‖∑ c, f c * h c‖ ≤ A * B := by
  have h1 : ‖∑ c, f c * h c‖ ≤ (∑ c, ‖f c‖) * B := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun c _ => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB c) (norm_nonneg _)
  calc γW * ‖∑ c, f c * h c‖ ≤ γW * ((∑ c, ‖f c‖) * B) := mul_le_mul_of_nonneg_left h1 hγW
    _ = (γW * ∑ c, ‖f c‖) * B := by ring
    _ ≤ A * B := mul_le_mul_of_nonneg_right hf hB0

/-- The same with the factors in the other order. -/
private theorem loopsStep_sum_mul_le' {L : ℕ} {γW A B : ℝ} (hγW : 0 ≤ γW) (f h : Fin L → ℂ)
    (hf : γW * ∑ c, ‖f c‖ ≤ A) (hB : ∀ c, ‖h c‖ ≤ B) (hB0 : 0 ≤ B) :
    γW * ‖∑ c, h c * f c‖ ≤ A * B := by
  simp only [mul_comm (h _)]
  exact loopsStep_sum_mul_le hγW f h hf hB hB0

/-- The number of pairs `i < j` in `Fin k` is at most `k²/2`. -/
private theorem loopsStep_pairs_le (k : ℕ) :
    2 * ∑ i : Fin k, ∑ j : Fin k, (if i < j then (1 : ℝ) else 0) ≤ (k : ℝ) ^ 2 := by
  have h1 : ∑ i : Fin k, ∑ j : Fin k, (if i < j then (1 : ℝ) else 0) =
      ∑ i : Fin k, ∑ j : Fin k, (if j < i then (1 : ℝ) else 0) := Finset.sum_comm
  have h2 : ∀ i j : Fin k, (if i < j then (1 : ℝ) else 0) + (if j < i then (1 : ℝ) else 0) ≤ 1 := by
    intro i j
    split_ifs with h h' <;> first | (exact absurd (h.trans h') (lt_irrefl _)) | norm_num
  calc 2 * ∑ i : Fin k, ∑ j : Fin k, (if i < j then (1 : ℝ) else 0) =
      ∑ i : Fin k, ∑ j : Fin k,
        ((if i < j then (1 : ℝ) else 0) + (if j < i then (1 : ℝ) else 0)) := by
        rw [two_mul]
        nth_rewrite 2 [h1]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => (Finset.sum_add_distrib).symm
    _ ≤ ∑ _i : Fin k, ∑ _j : Fin k, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h2 i j
    _ = (k : ℝ) ^ 2 := by simp [sq]

variable (g E : ℝ) (m : ℂ) {W L k : ℕ} (u : ℝ) (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)

/-- Row of a loop error of length `n ≤ k` with one free label:
`γW Σ_c |D_n| ≤ (R + 2^k γ X^k/η_u) Z^{n-2}`. -/
private theorem loopsStep_rowD (hW : 1 ≤ W) (hM : M.IsHermitian) (hη : 0 < etaChar g m u)
    {X Z R : ℝ} (hX1 : 1 ≤ X) (hZ : 1 ≤ 2 * W * Z)
    (hX : ∀ c d, ‖blockOf (resolventMat M (zChar g E m u)) c d‖ ≤ X)
    (hK : ∀ n : ℕ, 2 ≤ n → n ≤ k → ∀ (b : Fin n → Fin L) (s : Fin n → Bool) (i : Fin n),
      gammaG g * W * ∑ c : Fin L, ‖primLoop g W L E m u (Function.update b i c) s‖ ≤
        R * Z ^ (n - 2))
    (n : ℕ) (hn2 : 2 ≤ n) (hnk : n ≤ k) (b : Fin n → Fin L) (s : Fin n → Bool) (i : Fin n) :
    gammaG g * W * ∑ c : Fin L, ‖resLoop g E m (Function.update b i c) s u M -
        primLoop g W L E m u (Function.update b i c) s‖ ≤
      (R + 2 ^ k * gammaG g * X ^ k / etaChar g m u) * Z ^ (n - 2) := by
  have hγ := loopsStep_gammaG_pos g
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hZ0 : 0 < Z := by
    by_contra h
    have h : Z ≤ 0 := not_lt.mp h
    have : 2 * (W : ℝ) * Z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    linarith
  have hz : 0 < (zChar g E m u).im := by rw [im_zChar]; exact hη
  have hrow := loopRows_row_ward hn2 M hM (zChar g E m u) hz X hX b s i
  rw [im_zChar] at hrow
  have hsplit : ∑ c : Fin L, ‖resLoop g E m (Function.update b i c) s u M -
        primLoop g W L E m u (Function.update b i c) s‖ ≤
      ∑ c : Fin L, ‖loopTr (resolventMat M (zChar g E m u)) (Function.update b i c) s‖ +
        ∑ c : Fin L, ‖primLoop g W L E m u (Function.update b i c) s‖ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun c _ => norm_sub_le _ _
  have hK' := hK n hn2 hnk b s i
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  have e1 : n' + 2 - 1 = n' + 1 := by omega
  have e2 : n' + 2 - 2 = n' := by omega
  rw [e1] at hrow
  rw [e2] at hK' ⊢
  -- the resolvent row
  have hWinv : (W : ℝ)⁻¹ ≤ 2 * Z := by
    rw [inv_le_iff_one_le_mul₀ hWpos]; linarith
  have hL : gammaG g * W * (X ^ (n' + 1) / ((W : ℝ) ^ (n' + 1) * etaChar g m u)) ≤
      2 ^ k * gammaG g * X ^ k / etaChar g m u * Z ^ n' := by
    have e : gammaG g * W * (X ^ (n' + 1) / ((W : ℝ) ^ (n' + 1) * etaChar g m u)) =
        gammaG g / etaChar g m u * X ^ (n' + 1) * ((W : ℝ)⁻¹) ^ n' := by
      rw [inv_pow]
      field_simp
      ring
    rw [e]
    have hXk : X ^ (n' + 1) ≤ X ^ k := pow_le_pow_right₀ hX1 (by omega)
    have hWk : ((W : ℝ)⁻¹) ^ n' ≤ 2 ^ k * Z ^ n' := by
      calc ((W : ℝ)⁻¹) ^ n' ≤ (2 * Z) ^ n' := pow_le_pow_left₀ (by positivity) hWinv n'
        _ = 2 ^ n' * Z ^ n' := mul_pow _ _ _
        _ ≤ 2 ^ k * Z ^ n' := by
            gcongr
            · norm_num
            · omega
    have hϑ : 0 ≤ gammaG g / etaChar g m u := by positivity
    calc gammaG g / etaChar g m u * X ^ (n' + 1) * ((W : ℝ)⁻¹) ^ n' ≤
        gammaG g / etaChar g m u * X ^ k * (2 ^ k * Z ^ n') := by gcongr
      _ = 2 ^ k * gammaG g * X ^ k / etaChar g m u * Z ^ n' := by ring
  calc gammaG g * W * ∑ c : Fin L, ‖resLoop g E m (Function.update b i c) s u M -
        primLoop g W L E m u (Function.update b i c) s‖ ≤
      gammaG g * W * (∑ c : Fin L, ‖loopTr (resolventMat M (zChar g E m u))
          (Function.update b i c) s‖ +
        ∑ c : Fin L, ‖primLoop g W L E m u (Function.update b i c) s‖) :=
        mul_le_mul_of_nonneg_left hsplit (by positivity)
    _ = gammaG g * W * ∑ c : Fin L, ‖loopTr (resolventMat M (zChar g E m u))
          (Function.update b i c) s‖ +
        gammaG g * W * ∑ c : Fin L, ‖primLoop g W L E m u (Function.update b i c) s‖ := by ring
    _ ≤ gammaG g * W * (X ^ (n' + 1) / ((W : ℝ) ^ (n' + 1) * etaChar g m u)) + R * Z ^ n' := by
        gcongr
    _ ≤ 2 ^ k * gammaG g * X ^ k / etaChar g m u * Z ^ n' + R * Z ^ n' := by gcongr
    _ = (R + 2 ^ k * gammaG g * X ^ k / etaChar g m u) * Z ^ n' := by ring

/-- One pair `i < j` of the cut sources of (5.17) [fo:eq:error-hierarchy] for `k ≥ 3`: the linear
and the quadratic cut terms are at most `Λ_l Z^k (3R + T)`, from the rows of `𝒦` and `D` and the
bounds of the shorter errors. -/
private theorem loopsStep_pair_le {L k : ℕ} (hk3 : 3 ≤ k) (Kf Df : LoopFam L) {γW R T Λl Z : ℝ}
    (hγW : 0 ≤ γW) (hR : 0 ≤ R) (hΛl : 0 ≤ Λl) (hZ0 : 0 ≤ Z)
    (hrowK : ∀ n : ℕ, 2 ≤ n → n ≤ k → ∀ (b : Fin n → Fin L) (s : Fin n → Bool) (i : Fin n),
      γW * ∑ c : Fin L, ‖Kf n (Function.update b i c) s‖ ≤ R * Z ^ (n - 2))
    (hrowD : ∀ n : ℕ, 2 ≤ n → n ≤ k → ∀ (b : Fin n → Fin L) (s : Fin n → Bool) (i : Fin n),
      γW * ∑ c : Fin L, ‖Df n (Function.update b i c) s‖ ≤ (R + T) * Z ^ (n - 2))
    (hsmall : ∀ n : ℕ, 2 ≤ n → n < k → ∀ (b : Fin n → Fin L) (s : Fin n → Bool),
      ‖Df n b s‖ ≤ Λl * Z ^ n)
    (a : Fin k → Fin L) (σ : Fin k → Bool) (i j : Fin k) (hij : i < j) :
    γW * ‖∑ c : Fin L,
        (if j.val = i.val + 1 then
            Kf _ (cutLLab a i j c) (cutLSgn σ i j) * Df _ (cutRLab a i j c) (cutRSgn σ i j)
          else if i.val = 0 ∧ j.val = k - 1 then
            Df _ (cutLLab a i j c) (cutLSgn σ i j) * Kf _ (cutRLab a i j c) (cutRSgn σ i j)
          else
            Kf _ (cutLLab a i j c) (cutLSgn σ i j) * Df _ (cutRLab a i j c) (cutRSgn σ i j) +
              Df _ (cutLLab a i j c) (cutLSgn σ i j) * Kf _ (cutRLab a i j c) (cutRSgn σ i j))‖ +
      γW * ‖∑ c : Fin L,
        Df _ (cutLLab a i j c) (cutLSgn σ i j) * Df _ (cutRLab a i j c) (cutRSgn σ i j)‖ ≤
      Λl * Z ^ k * (3 * R + T) := by
  have hij' : i.val < j.val := hij
  have hjk := j.2
  set nL : ℕ := k + i.val - j.val + 1 with hnL
  set nR : ℕ := j.val - i.val + 1 with hnR
  have hnL2 : 2 ≤ nL := by omega
  have hnLk : nL ≤ k := by omega
  have hnR2 : 2 ≤ nR := by omega
  have hnRk : nR ≤ k := by omega
  have hZL : Z ^ (nL - 2) * Z ^ nR = Z ^ k := by rw [← pow_add]; congr 1; omega
  have hZR : Z ^ (nR - 2) * Z ^ nL = Z ^ k := by rw [← pow_add]; congr 1; omega
  set c₀ : Fin L := a i with hc₀
  have bKL : γW * ∑ c : Fin L, ‖Kf nL (cutLLab a i j c) (cutLSgn σ i j)‖ ≤ R * Z ^ (nL - 2) := by
    have h := hrowK nL hnL2 hnLk (cutLLab a i j c₀) (cutLSgn σ i j)
      ⟨i.val, by have := j.2; omega⟩
    simp only [loopsStep_cutLLab_update] at h
    exact h
  have bKR : γW * ∑ c : Fin L, ‖Kf nR (cutRLab a i j c) (cutRSgn σ i j)‖ ≤ R * Z ^ (nR - 2) := by
    have h := hrowK nR hnR2 hnRk (cutRLab a i j c₀) (cutRSgn σ i j) ⟨j.val - i.val, by omega⟩
    simp only [loopsStep_cutRLab_update] at h
    exact h
  have bDL : γW * ∑ c : Fin L, ‖Df nL (cutLLab a i j c) (cutLSgn σ i j)‖ ≤
      (R + T) * Z ^ (nL - 2) := by
    have h := hrowD nL hnL2 hnLk (cutLLab a i j c₀) (cutLSgn σ i j)
      ⟨i.val, by have := j.2; omega⟩
    simp only [loopsStep_cutLLab_update] at h
    exact h
  have bDR : γW * ∑ c : Fin L, ‖Df nR (cutRLab a i j c) (cutRSgn σ i j)‖ ≤
      (R + T) * Z ^ (nR - 2) := by
    have h := hrowD nR hnR2 hnRk (cutRLab a i j c₀) (cutRSgn σ i j) ⟨j.val - i.val, by omega⟩
    simp only [loopsStep_cutRLab_update] at h
    exact h
  have hP0 : 0 ≤ Λl * Z ^ k := by positivity
  have hB0 : ∀ n, 0 ≤ Λl * Z ^ n := fun n => by positivity
  by_cases hadj : j.val = i.val + 1
  · have hnR' : nR < k := by omega
    have sDR : ∀ c, ‖Df nR (cutRLab a i j c) (cutRSgn σ i j)‖ ≤ Λl * Z ^ nR := fun c =>
      hsmall nR hnR2 hnR' _ _
    simp only [hadj, ↓reduceIte]
    have h1 := loopsStep_sum_mul_le hγW (fun c => Kf nL (cutLLab a i j c) (cutLSgn σ i j))
      (fun c => Df nR (cutRLab a i j c) (cutRSgn σ i j)) bKL sDR (hB0 nR)
    have h2 := loopsStep_sum_mul_le hγW (fun c => Df nL (cutLLab a i j c) (cutLSgn σ i j))
      (fun c => Df nR (cutRLab a i j c) (cutRSgn σ i j)) bDL sDR (hB0 nR)
    calc _ ≤ R * Z ^ (nL - 2) * (Λl * Z ^ nR) + (R + T) * Z ^ (nL - 2) * (Λl * Z ^ nR) :=
          add_le_add h1 h2
      _ = Λl * (Z ^ (nL - 2) * Z ^ nR) * (2 * R + T) := by ring
      _ = Λl * Z ^ k * (2 * R + T) := by rw [hZL]
      _ ≤ Λl * Z ^ k * (3 * R + T) := by gcongr; linarith
  · by_cases hcyc : i.val = 0 ∧ j.val = k - 1
    · have hnL' : nL < k := by omega
      have sDL : ∀ c, ‖Df nL (cutLLab a i j c) (cutLSgn σ i j)‖ ≤ Λl * Z ^ nL := fun c =>
        hsmall nL hnL2 hnL' _ _
      simp only [hadj, ↓reduceIte]
      simp only [hcyc, and_self, ↓reduceIte]
      have h1 := loopsStep_sum_mul_le' hγW (fun c => Kf nR (cutRLab a i j c) (cutRSgn σ i j))
        (fun c => Df nL (cutLLab a i j c) (cutLSgn σ i j)) bKR sDL (hB0 nL)
      have h2 := loopsStep_sum_mul_le' hγW (fun c => Df nR (cutRLab a i j c) (cutRSgn σ i j))
        (fun c => Df nL (cutLLab a i j c) (cutLSgn σ i j)) bDR sDL (hB0 nL)
      calc _ ≤ R * Z ^ (nR - 2) * (Λl * Z ^ nL) + (R + T) * Z ^ (nR - 2) * (Λl * Z ^ nL) :=
            add_le_add h1 h2
        _ = Λl * (Z ^ (nR - 2) * Z ^ nL) * (2 * R + T) := by ring
        _ = Λl * Z ^ k * (2 * R + T) := by rw [hZR]
        _ ≤ Λl * Z ^ k * (3 * R + T) := by gcongr; linarith
    · have hnL' : nL < k := by omega
      have hnR' : nR < k := by
        by_contra h
        apply hcyc
        omega
      have sDL : ∀ c, ‖Df nL (cutLLab a i j c) (cutLSgn σ i j)‖ ≤ Λl * Z ^ nL := fun c =>
        hsmall nL hnL2 hnL' _ _
      have sDR : ∀ c, ‖Df nR (cutRLab a i j c) (cutRSgn σ i j)‖ ≤ Λl * Z ^ nR := fun c =>
        hsmall nR hnR2 hnR' _ _
      simp only [hadj, hcyc, ↓reduceIte]
      rw [Finset.sum_add_distrib]
      have h1 := loopsStep_sum_mul_le hγW (fun c => Kf nL (cutLLab a i j c) (cutLSgn σ i j))
        (fun c => Df nR (cutRLab a i j c) (cutRSgn σ i j)) bKL sDR (hB0 nR)
      have h1' := loopsStep_sum_mul_le' hγW (fun c => Kf nR (cutRLab a i j c) (cutRSgn σ i j))
        (fun c => Df nL (cutLLab a i j c) (cutLSgn σ i j)) bKR sDL (hB0 nL)
      have h2 := loopsStep_sum_mul_le hγW (fun c => Df nL (cutLLab a i j c) (cutLSgn σ i j))
        (fun c => Df nR (cutRLab a i j c) (cutRSgn σ i j)) bDL sDR (hB0 nR)
      have htri := norm_add_le (∑ c : Fin L, Kf nL (cutLLab a i j c) (cutLSgn σ i j) *
          Df nR (cutRLab a i j c) (cutRSgn σ i j))
        (∑ c : Fin L, Df nL (cutLLab a i j c) (cutLSgn σ i j) *
          Kf nR (cutRLab a i j c) (cutRSgn σ i j))
      have htri' := mul_le_mul_of_nonneg_left htri hγW
      calc _ ≤ γW * (‖∑ c : Fin L, Kf nL (cutLLab a i j c) (cutLSgn σ i j) *
            Df nR (cutRLab a i j c) (cutRSgn σ i j)‖ +
            ‖∑ c : Fin L, Df nL (cutLLab a i j c) (cutLSgn σ i j) *
              Kf nR (cutRLab a i j c) (cutRSgn σ i j)‖) +
          γW * ‖∑ c : Fin L, Df nL (cutLLab a i j c) (cutLSgn σ i j) *
            Df nR (cutRLab a i j c) (cutRSgn σ i j)‖ := by gcongr
        _ ≤ R * Z ^ (nL - 2) * (Λl * Z ^ nR) + R * Z ^ (nR - 2) * (Λl * Z ^ nL) +
            (R + T) * Z ^ (nL - 2) * (Λl * Z ^ nR) := by
            rw [mul_add]; linarith
        _ = Λl * (Z ^ (nL - 2) * Z ^ nR) * (2 * R + T) +
            Λl * (Z ^ (nR - 2) * Z ^ nL) * R := by ring
        _ = Λl * Z ^ k * (3 * R + T) := by rw [hZL, hZR]; ring

/-- Sum over the pairs `i < j`: if each term is at most `P` after the factor `γW`, the sum is at
most `P` times the number of pairs. -/
private theorem loopsStep_pairs_sum {k : ℕ} {γW P : ℝ} (hγW : 0 ≤ γW) (f : Fin k → Fin k → ℂ)
    (hf : ∀ i j, i < j → γW * ‖f i j‖ ≤ P) :
    γW * ‖∑ i : Fin k, ∑ j : Fin k, (if i < j then f i j else 0)‖ ≤
      P * ∑ i : Fin k, ∑ j : Fin k, (if i < j then (1 : ℝ) else 0) := by
  have h1 : ‖∑ i : Fin k, ∑ j : Fin k, (if i < j then f i j else 0)‖ ≤
      ∑ i : Fin k, ∑ j : Fin k, ‖if i < j then f i j else 0‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
  calc γW * ‖∑ i : Fin k, ∑ j : Fin k, (if i < j then f i j else 0)‖ ≤
      γW * ∑ i : Fin k, ∑ j : Fin k, ‖if i < j then f i j else 0‖ :=
        mul_le_mul_of_nonneg_left h1 hγW
    _ = ∑ i : Fin k, ∑ j : Fin k, γW * ‖if i < j then f i j else 0‖ := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
    _ ≤ ∑ i : Fin k, ∑ j : Fin k, (if i < j then P else 0) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        split_ifs with h
        · exact hf i j h
        · simp
    _ = P * ∑ i : Fin k, ∑ j : Fin k, (if i < j then (1 : ℝ) else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> simp

/-- The cut sources of (5.17) [fo:eq:error-hierarchy] for `k ≥ 3`:
`γW |cutSrcLin + cutSrcQuad| ≤ k² Λ_l Z^k (2R + T)`. -/
private theorem loopsStep_cuts_le {L k : ℕ} (hk3 : 3 ≤ k) (Kf Df : LoopFam L) {γW R T Λl Z : ℝ}
    (hγW : 0 ≤ γW) (hR : 0 ≤ R) (hT : 0 ≤ T) (hΛl : 0 ≤ Λl) (hZ0 : 0 ≤ Z)
    (hrowK : ∀ n : ℕ, 2 ≤ n → n ≤ k → ∀ (b : Fin n → Fin L) (s : Fin n → Bool) (i : Fin n),
      γW * ∑ c : Fin L, ‖Kf n (Function.update b i c) s‖ ≤ R * Z ^ (n - 2))
    (hrowD : ∀ n : ℕ, 2 ≤ n → n ≤ k → ∀ (b : Fin n → Fin L) (s : Fin n → Bool) (i : Fin n),
      γW * ∑ c : Fin L, ‖Df n (Function.update b i c) s‖ ≤ (R + T) * Z ^ (n - 2))
    (hsmall : ∀ n : ℕ, 2 ≤ n → n < k → ∀ (b : Fin n → Fin L) (s : Fin n → Bool),
      ‖Df n b s‖ ≤ Λl * Z ^ n)
    (a : Fin k → Fin L) (σ : Fin k → Bool) :
    γW * ‖cutSrcLin Kf Df a σ + cutSrcQuad Df a σ‖ ≤ (k : ℝ) ^ 2 * Λl * Z ^ k * (2 * R + T) := by
  have hsum : cutSrcLin Kf Df a σ + cutSrcQuad Df a σ = ∑ i : Fin k, ∑ j : Fin k,
      (if i < j then
        (∑ c : Fin L,
          (if j.val = i.val + 1 then
              Kf _ (cutLLab a i j c) (cutLSgn σ i j) * Df _ (cutRLab a i j c) (cutRSgn σ i j)
            else if i.val = 0 ∧ j.val = k - 1 then
              Df _ (cutLLab a i j c) (cutLSgn σ i j) * Kf _ (cutRLab a i j c) (cutRSgn σ i j)
            else
              Kf _ (cutLLab a i j c) (cutLSgn σ i j) * Df _ (cutRLab a i j c) (cutRSgn σ i j) +
                Df _ (cutLLab a i j c) (cutLSgn σ i j) *
                  Kf _ (cutRLab a i j c) (cutRSgn σ i j))) +
        ∑ c : Fin L,
          Df _ (cutLLab a i j c) (cutLSgn σ i j) * Df _ (cutRLab a i j c) (cutRSgn σ i j)
      else 0) := by
    have hk2 : ¬ k ≤ 2 := by omega
    unfold cutSrcLin cutSrcQuad cutSumFam
    rw [ite_eq_right hk2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [hsum]
  have hP := loopsStep_pairs_sum (P := Λl * Z ^ k * (3 * R + T)) hγW _ fun i j hij =>
    (mul_le_mul_of_nonneg_left (norm_add_le _ _) hγW).trans
      ((le_of_eq (mul_add _ _ _)).trans
        (loopsStep_pair_le hk3 Kf Df hγW hR hΛl hZ0 hrowK hrowD hsmall a σ i j hij))
  have hcount := loopsStep_pairs_le k
  have hN0 : 0 ≤ ∑ i : Fin k, ∑ j : Fin k, (if i < j then (1 : ℝ) else 0) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num
  have hA : 0 ≤ Λl * Z ^ k := by positivity
  refine hP.trans ?_
  have e : (k : ℝ) ^ 2 * Λl * Z ^ k * (2 * R + T) = Λl * Z ^ k * ((k : ℝ) ^ 2 * (2 * R + T)) := by
    ring
  rw [e, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hA
  nlinarith

/-- The quadratic cut source of (5.17) [fo:eq:error-hierarchy] at `k = 2`:
`γW |Σ_c D(c, a₁) D(a₀, c)| ≤ A Λ` from the row `A` of `D_2` and `|D_2| ≤ Λ`. -/
private theorem loopsStep_quad_two {L : ℕ} (Df : LoopFam L) {γW A Λ : ℝ} (hγW : 0 ≤ γW)
    (hΛ : 0 ≤ Λ)
    (hrow : ∀ n : ℕ, n = 2 → ∀ (b : Fin n → Fin L) (s : Fin n → Bool) (i : Fin n),
      γW * ∑ c : Fin L, ‖Df n (Function.update b i c) s‖ ≤ A)
    (htop : ∀ n : ℕ, n = 2 → ∀ (b : Fin n → Fin L) (s : Fin n → Bool), ‖Df n b s‖ ≤ Λ)
    (a : Fin 2 → Fin L) (σ : Fin 2 → Bool) :
    γW * ‖cutSrcQuad Df a σ‖ ≤ A * Λ := by
  unfold cutSrcQuad cutSumFam
  have hP := loopsStep_pairs_sum (P := A * Λ) hγW (fun i j => ∑ c : Fin L,
      Df _ (cutLLab a i j c) (cutLSgn σ i j) * Df _ (cutRLab a i j c) (cutRSgn σ i j))
      fun (i j : Fin 2) hij => by
    have hij' : i.val < j.val := hij
    have hj := j.2
    have bDL := hrow (2 + i.val - j.val + 1) (by omega) (cutLLab a i j (a i)) (cutLSgn σ i j)
      ⟨i.val, by omega⟩
    simp only [loopsStep_cutLLab_update] at bDL
    exact loopsStep_sum_mul_le hγW _ (fun c => Df _ (cutRLab a i j c) (cutRSgn σ i j)) bDL
      (fun c => htop _ (by omega) _ _) hΛ
  refine hP.trans (le_of_eq ?_)
  have h1 : ∑ i : Fin 2, ∑ j : Fin 2, (if i < j then (1 : ℝ) else 0) = 1 := by
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    have h01 : (0 : Fin 2) < 1 := by decide
    have h10 : ¬ (1 : Fin 2) < 0 := by decide
    simp [h01, h10]
  rw [h1, mul_one]

/-- The operator `Θ` of (5.14) [fo:eq:generator] on `D_k`: `|Θ D_k| ≤ k R Λ` from the row `R` of
`𝒦_2` and `|D_k| ≤ Λ`. -/
private theorem loopsStep_theta_le {L k : ℕ} (Kf Df : LoopFam L) {γ : ℝ} {W : ℕ} {R Λ : ℝ}
    (hγW : 0 ≤ γ * W) (hΛ : 0 ≤ Λ)
    (hrow2 : ∀ (x : Fin L) (s t : Bool), γ * W * ∑ c : Fin L, ‖Kf 2 ![x, c] ![s, t]‖ ≤ R)
    (htop : ∀ (b : Fin k → Fin L) (s : Fin k → Bool), ‖Df k b s‖ ≤ Λ)
    (a : Fin k → Fin L) (σ : Fin k → Bool) :
    ‖thetaOp γ W Kf Df a σ‖ ≤ k * R * Λ := by
  unfold thetaOp
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hγW]
  have h1 : ∀ j : Fin k, γ * W * ‖∑ c : Fin L, Kf 2 ![a j, c] ![σ j, σ (finRotate k j)] *
      Df k (Function.update a j c) σ‖ ≤ R * Λ := fun j =>
    loopsStep_sum_mul_le hγW _ (fun c => Df k (Function.update a j c) σ) (hrow2 _ _ _)
      (fun c => htop _ _) hΛ
  calc γ * W * ‖∑ j : Fin k, ∑ c : Fin L, Kf 2 ![a j, c] ![σ j, σ (finRotate k j)] *
        Df k (Function.update a j c) σ‖ ≤
      γ * W * ∑ j : Fin k, ‖∑ c : Fin L, Kf 2 ![a j, c] ![σ j, σ (finRotate k j)] *
        Df k (Function.update a j c) σ‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hγW
    _ = ∑ j : Fin k, γ * W * ‖∑ c : Fin L, Kf 2 ![a j, c] ![σ j, σ (finRotate k j)] *
        Df k (Function.update a j c) σ‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ _j : Fin k, R * Λ := Finset.sum_le_sum fun j _ => h1 j
    _ = k * R * Λ := by simp; ring

end GenRates

/-- Deterministic rates of the loop-error hierarchy (5.17) [fo:eq:error-hierarchy] at a Hermitian
matrix `M` and time `u`, for `k ≥ 2`: with `‖G_{cd}‖ ≤ X` (`X ≥ 1`), `|⟨G⟩_{cc} - m| ≤ τ`, rows
`γW Σ_c |𝒦_n(…, c, …)| ≤ R Z^{n-2}` of the primitive loops for `2 ≤ n ≤ k`, shorter errors
`|D_n| ≤ Λ_l Z^n` for `2 ≤ n < k` (`2WZ ≥ 1`) and `|D_k| ≤ Λ` for every word, the generator of
`D_k` is linear in `Λ` with coefficient `kR`, plus `γ(Im m + τ)/η_u + R` when `k = 2` (the pair
row with the fixed constant), and the light insertion (5.7) [fo:eq:light] and the remaining cuts
are sources. -/
theorem loopsStep_gen_le (g E : ℝ) (m : ℂ) {W L k : ℕ} (hW : 1 ≤ W) (hL : 3 ≤ L) (hk : 2 ≤ k)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {u : ℝ} (hu : u ∈ Set.Ioo (-1 : ℝ) 1)
    {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian) {X τ Z R Λl Λ : ℝ}
    (hX1 : 1 ≤ X) (hZ : 1 ≤ 2 * W * Z) (hΛl : 0 ≤ Λl)
    (hX : ∀ c d, ‖blockOf (resolventMat M (zChar g E m u)) c d‖ ≤ X)
    (hτ : ∀ c, ‖blockTr (resolventMat M (zChar g E m u)) c c - m‖ ≤ τ)
    (hK : ∀ n : ℕ, 2 ≤ n → n ≤ k → ∀ (b : Fin n → Fin L) (s : Fin n → Bool) (i : Fin n),
      gammaG g * W * ∑ c : Fin L, ‖primLoop g W L E m u (Function.update b i c) s‖ ≤
        R * Z ^ (n - 2))
    (hlow : ∀ n : ℕ, 2 ≤ n → n < k → ∀ (b : Fin n → Fin L) (s : Fin n → Bool),
      ‖resLoop g E m b s u M - primLoop g W L E m u b s‖ ≤ Λl * Z ^ n)
    (htop : ∀ (b : Fin k → Fin L) (s : Fin k → Bool),
      ‖resLoop g E m b s u M - primLoop g W L E m u b s‖ ≤ Λ)
    (a : Fin k → Fin L) (σ : Fin k → Bool) :
    ‖blockGen W L (gammaG g)
        (fun r N => resLoop g E m a σ r N - primLoop g W L E m r a σ) u M‖ ≤
      (k * R + if k = 2 then gammaG g * (m.im + τ) / etaChar g m u + R else 0) * Λ +
        gammaG g * W * k * τ * X ^ k / ((W : ℝ) ^ k * etaChar g m u) +
        (k : ℝ) ^ 2 * Λl * Z ^ k * (2 * R + 2 ^ k * gammaG g * X ^ k / etaChar g m u) := by
  have hγ := loopsStep_gammaG_pos g
  have hm0 : 0 < m.im := hm.1
  have hu1 : u < 1 := hu.2
  have hη : 0 < etaChar g m u := etaChar_pos g m hm0 hu1
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hγW : 0 ≤ gammaG g * W := by positivity
  have hZ0 : 0 < Z := by
    by_contra h
    have h : Z ≤ 0 := not_lt.mp h
    have : 2 * (W : ℝ) * Z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    linarith
  have a0 : Fin L := ⟨0, by omega⟩
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans (htop a σ)
  have hR : 0 ≤ R := by
    have h := hK 2 le_rfl hk ![a0, a0] ![true, true] 1
    have h0 : 0 ≤ gammaG g * W * ∑ c : Fin L,
        ‖primLoop g W L E m u (Function.update ![a0, a0] 1 c) ![true, true]‖ := by positivity
    have := h0.trans h
    simpa using this
  have hτ0 : 0 ≤ τ := (norm_nonneg _).trans (hτ a0)
  set Kt : ℝ → LoopFam L := fun r n b τ => primLoop g W L E m r (k := n) b τ with hKt
  set Df : LoopFam L := errFam g E m (Kt u) u M with hDf
  have hgen := blockGen_errorLoop g E m hm0 hu1 hM Kt
    (loopsStep_primDeriv g W L hW hL E m hm u hu) a σ
  have hsplit := cutErr_split (gammaG g) W hk (Kt u) Df
    (fun x y s t => primLoop_two_swap g W L E m u x y s t) a σ
  have hlight := lightW_norm_le g E m hm0 hu1 hM X τ hX hτ a σ
  have hrow2 : ∀ (x : Fin L) (s t : Bool),
      gammaG g * W * ∑ c : Fin L, ‖Kt u 2 ![x, c] ![s, t]‖ ≤ R := by
    intro x s t
    have h := hK 2 le_rfl hk ![x, x] ![s, t] 1
    simp only [loopsStep_update_pair, Nat.sub_self, pow_zero, mul_one] at h
    exact h
  have htheta := loopsStep_theta_le (Kt u) Df hγW hΛ hrow2 htop a σ
  have e : blockGen W L (gammaG g)
      (fun r N => resLoop g E m a σ r N - primLoop g W L E m r a σ) u M =
      lightW g E m a σ u M + (thetaOp (gammaG g) W (Kt u) Df a σ +
        ((gammaG g * W : ℝ) : ℂ) * (cutSrcLin (Kt u) Df a σ + cutSrcQuad Df a σ)) := by
    rw [← hsplit]; exact hgen
  rw [e]
  set T : ℝ := 2 ^ k * gammaG g * X ^ k / etaChar g m u with hTdef
  have hT : 0 ≤ T := by positivity
  have hcut : gammaG g * W * ‖cutSrcLin (Kt u) Df a σ + cutSrcQuad Df a σ‖ ≤
      (if k = 2 then gammaG g * (m.im + τ) / etaChar g m u + R else 0) * Λ +
        (k : ℝ) ^ 2 * Λl * Z ^ k * (2 * R + T) := by
    by_cases hk2 : k = 2
    · subst hk2
      have hlin : cutSrcLin (Kt u) Df a σ = 0 := by simp [cutSrcLin]
      rw [hlin, zero_add, ite_eq_left rfl]
      have hrowD2 : ∀ n : ℕ, n = 2 → ∀ (b : Fin n → Fin L) (s : Fin n → Bool) (i : Fin n),
          gammaG g * W * ∑ c : Fin L, ‖Df n (Function.update b i c) s‖ ≤
            gammaG g * (m.im + τ) / etaChar g m u + R := by
        rintro n rfl b s i
        have hz : 0 < (zChar g E m u).im := by rw [im_zChar]; exact hη
        have hw := loopTr_two_row_ward hW M hM (zChar g E m u) hz b s i
        rw [im_zChar] at hw
        have him : (blockTr (resolventMat M (zChar g E m u)) (b (i + 1)) (b (i + 1))).im ≤
            m.im + τ := by
          have h1 := hτ (b (i + 1))
          have h2 := Complex.im_le_norm
            (blockTr (resolventMat M (zChar g E m u)) (b (i + 1)) (b (i + 1)) - m)
          rw [Complex.sub_im] at h2
          linarith
        have hKr := hK 2 le_rfl le_rfl b s i
        simp only [Nat.sub_self, pow_zero, mul_one] at hKr
        have hsplit2 : ∑ c : Fin L, ‖Df 2 (Function.update b i c) s‖ ≤
            ∑ c : Fin L, ‖loopTr (resolventMat M (zChar g E m u)) (Function.update b i c) s‖ +
              ∑ c : Fin L, ‖primLoop g W L E m u (Function.update b i c) s‖ := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_le_sum fun c _ => norm_sub_le _ _
        have hL2 : gammaG g * W * ∑ c : Fin L,
            ‖loopTr (resolventMat M (zChar g E m u)) (Function.update b i c) s‖ ≤
            gammaG g * (m.im + τ) / etaChar g m u := by
          calc gammaG g * W * ∑ c : Fin L,
              ‖loopTr (resolventMat M (zChar g E m u)) (Function.update b i c) s‖ ≤
              gammaG g * W * ((blockTr (resolventMat M (zChar g E m u)) (b (i + 1))
                (b (i + 1))).im / ((W : ℝ) * etaChar g m u)) :=
                mul_le_mul_of_nonneg_left hw hγW
            _ = gammaG g * (blockTr (resolventMat M (zChar g E m u)) (b (i + 1))
                (b (i + 1))).im / etaChar g m u := by field_simp
            _ ≤ gammaG g * (m.im + τ) / etaChar g m u := by gcongr
        calc gammaG g * W * ∑ c : Fin L, ‖Df 2 (Function.update b i c) s‖ ≤
            gammaG g * W * (∑ c : Fin L,
              ‖loopTr (resolventMat M (zChar g E m u)) (Function.update b i c) s‖ +
              ∑ c : Fin L, ‖primLoop g W L E m u (Function.update b i c) s‖) :=
              mul_le_mul_of_nonneg_left hsplit2 hγW
          _ = gammaG g * W * ∑ c : Fin L,
              ‖loopTr (resolventMat M (zChar g E m u)) (Function.update b i c) s‖ +
              gammaG g * W * ∑ c : Fin L, ‖primLoop g W L E m u (Function.update b i c) s‖ := by
              ring
          _ ≤ gammaG g * (m.im + τ) / etaChar g m u + R := add_le_add hL2 hKr
      have htop2 : ∀ n : ℕ, n = 2 → ∀ (b : Fin n → Fin L) (s : Fin n → Bool),
          ‖Df n b s‖ ≤ Λ := by
        rintro n rfl b s
        exact htop b s
      have hq := loopsStep_quad_two Df hγW hΛ hrowD2 htop2 a σ
      have h0 : 0 ≤ ((2 : ℕ) : ℝ) ^ 2 * Λl * Z ^ 2 * (2 * R + T) := by positivity
      exact le_add_of_le_of_nonneg hq h0
    · have hk3 : 3 ≤ k := by omega
      rw [ite_eq_right hk2, zero_mul, zero_add]
      refine loopsStep_cuts_le hk3 (Kt u) Df hγW hR hT hΛl hZ0.le hK ?_ hlow a σ
      intro n hn2 hnk b s i
      exact loopsStep_rowD g E m u M hW hM hη hX1 hZ hX hK n hn2 hnk b s i
  have hnorm : ‖((gammaG g * W : ℝ) : ℂ) * (cutSrcLin (Kt u) Df a σ + cutSrcQuad Df a σ)‖ =
      gammaG g * W * ‖cutSrcLin (Kt u) Df a σ + cutSrcQuad Df a σ‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hγW]
  calc ‖lightW g E m a σ u M + (thetaOp (gammaG g) W (Kt u) Df a σ +
        ((gammaG g * W : ℝ) : ℂ) * (cutSrcLin (Kt u) Df a σ + cutSrcQuad Df a σ))‖ ≤
      ‖lightW g E m a σ u M‖ + (‖thetaOp (gammaG g) W (Kt u) Df a σ‖ +
        ‖((gammaG g * W : ℝ) : ℂ) * (cutSrcLin (Kt u) Df a σ + cutSrcQuad Df a σ)‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ gammaG g * W * k * τ * X ^ k / ((W : ℝ) ^ k * etaChar g m u) + (k * R * Λ +
        ((if k = 2 then gammaG g * (m.im + τ) / etaChar g m u + R else 0) * Λ +
          (k : ℝ) ^ 2 * Λl * Z ^ k * (2 * R + T))) := by
        rw [hnorm]
        gcongr
    _ = _ := by ring

/-! ### The range of Lemma 5.6 [fo:prop:inputs] -/

section Range

/-- On the range of Lemma 5.6 [fo:prop:inputs], for `W` large: `g ≥ 1`, `L ≥ T g²` for a given
`T`, `L ≥ 3`, the anchor `m = m_{g,L}(E)` is a root with `|m| ≤ C` and `Im m ≥ C⁻¹`, where `C`
depends on `κ` only. -/
private theorem loopsStep_root (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ₀ C : ℝ, 1 ≤ Cκ₀ ∧ 1 ≤ C ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ,
      Tendsto ρ atTop atTop → ∀ T : ℝ, ∀ᶠ W : ℕ in atTop, ∀ CV : ℝ,
        ∀ p ∈ initLarge κ Cκ CV ρ W, 1 ≤ p.g ∧ T * p.g ^ 2 ≤ p.L ∧ 3 ≤ p.L ∧
          IsDysonRootV (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E) ∧
          ‖mRoot p.g p.L p.E‖ ≤ C ∧ C⁻¹ ≤ (mRoot p.g p.L p.E).im := by
  obtain ⟨Cκl, Rl, cl, Cl, hCκl, hRl, hcl, hCl, Hl⟩ := large_periodic_comparison κ hκ hκ2
  refine ⟨Cκl, max 1 Cl, hCκl, le_max_left _ _, fun Cκ hCκ ρ hρ T => ?_⟩
  set Rst : ℝ := max (max Rl 4) T with hRst
  filter_upwards [hρ.eventually_ge_atTop Rst,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
    with W hρW hlog CV p hp
  obtain ⟨hgC, hE, hLlog, -, -, -⟩ := hp
  have hgl : Cκl ≤ p.g := hCκ.trans hgC
  have hg1 : 1 ≤ p.g := hCκl.trans hgl
  have hg0 : 0 < p.g := by linarith
  have hgg : 0 < p.g ^ 2 := by positivity
  have hRst4 : 4 ≤ Rst := le_trans (le_max_right _ _) (le_max_left _ _)
  have hρ0 : 0 ≤ ρ W := by linarith
  have hlog' : (1 : ℝ) ≤ Real.log W := hlog
  have hLR : Rst * p.g ^ 2 ≤ p.L := by
    have h1 : 0 ≤ ρ W * p.g ^ 2 := mul_nonneg hρ0 hgg.le
    calc Rst * p.g ^ 2 ≤ ρ W * p.g ^ 2 := mul_le_mul_of_nonneg_right hρW hgg.le
      _ ≤ ρ W * p.g ^ 2 * Real.log W := le_mul_of_one_le_right h1 hlog'
      _ ≤ _ := hLlog
  have hRL : ∀ R' : ℝ, R' ≤ Rst → R' * p.g ^ 2 ≤ p.L := fun R' h =>
    le_trans (mul_le_mul_of_nonneg_right h hgg.le) hLR
  have hRlL := hRL Rl (le_trans (le_max_left _ _) (le_max_left _ _))
  have hL3 : 3 ≤ p.L := by
    have h1 : (1 : ℝ) ≤ p.g ^ 2 := one_le_pow₀ hg1
    have := hRL 4 hRst4
    have : (3 : ℝ) ≤ p.L := by linarith
    exact_mod_cast this
  obtain ⟨m, -, hroot, -, hmim, hmC, -⟩ := Hl p.g hgl p.L hRlL p.E hE
  have hb0 : 0 ≤ hopB p.g := by
    unfold hopB; rw [max_eq_right hg1, div_self hg0.ne']; norm_num
  have hmR : mRoot p.g p.L p.E = m :=
    (mRootV_spec (hopB p.g) (gammaG p.g) hb0 (loopsStep_gammaG_pos _) p.L hL3
      (p.E : ℂ) (by simp)).2 m hroot
  refine ⟨hg1, hRL T (le_max_right _ _), hL3, by rw [hmR]; exact hroot, ?_, ?_⟩
  · rw [hmR]; exact hmC.trans (le_max_right _ _)
  · rw [hmR]; exact le_trans (inv_anti₀ hCl (le_max_right _ _)) hmim

end Range

/-! ### Scales and rows on the range -/

section Scales

/-- `(2W)⁻¹ ≤ ζ_u ≤ 2/W` for `g ≥ 1`, `L ≥ g²` and `u ∈ [0, 1/2]` ((5.18) [fo:eq:scale]). -/
private theorem loopsStep_zeta_bounds {g : ℝ} (hg : 1 ≤ g) {W L : ℕ} (hW : 1 ≤ W)
    (hL : g ^ 2 ≤ L) {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    1 ≤ 2 * W * zetaProp g W L u ∧ W * zetaProp g W L u ≤ 2 := by
  have hγ := loopsStep_gammaG_eq hg
  have hg0 : 0 < g := by linarith
  have hgg : 0 < g ^ 2 := by positivity
  have h1u : 0 < 1 - u := by linarith
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  set s := Real.sqrt (gammaG g * (1 - u)) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.2 (by rw [hγ]; positivity)
  have hss : s ^ 2 = gammaG g * (1 - u) := Real.sq_sqrt (by rw [hγ]; positivity)
  have hs : s ≤ g⁻¹ := by
    rw [hsdef, show g⁻¹ = Real.sqrt ((g ^ 2)⁻¹) by rw [Real.sqrt_inv, Real.sqrt_sq hg0.le]]
    apply Real.sqrt_le_sqrt
    rw [hγ]
    have : 0 < (g ^ 2)⁻¹ := by positivity
    nlinarith
  have hℓlo : g ^ 2 ≤ ellProp g L u := by
    unfold ellProp
    refine le_min hL ?_
    have : g ^ 2 ≤ g / s := by
      rw [le_div_iff₀ hs0]
      calc g ^ 2 * s ≤ g ^ 2 * g⁻¹ := mul_le_mul_of_nonneg_left hs (by positivity)
        _ = g := by field_simp
    linarith
  have hℓhi : ellProp g L u ≤ 1 + g / s := min_le_right _ _
  have hℓ0 : 0 < ellProp g L u := lt_of_lt_of_le hgg hℓlo
  set Q := (W : ℝ) * ellProp g L u * (1 - u) * gammaG g with hQ
  have hQpos : 0 < Q := by rw [hQ]; have := loopsStep_gammaG_pos g; positivity
  have hz : zetaProp g W L u = Q⁻¹ := rfl
  have hQlo : (W : ℝ) / 2 ≤ Q := by
    rw [hQ, hγ]
    have h1 : (W : ℝ) * g ^ 2 * (1 - u) * (g ^ 2)⁻¹ ≤
        (W : ℝ) * ellProp g L u * (1 - u) * (g ^ 2)⁻¹ := by
      gcongr
    have h2 : (W : ℝ) * g ^ 2 * (1 - u) * (g ^ 2)⁻¹ = W * (1 - u) := by field_simp
    nlinarith
  have hQhi : Q ≤ 2 * W := by
    have hgs : g * s ≤ 1 := by
      calc g * s ≤ g * g⁻¹ := mul_le_mul_of_nonneg_left hs hg0.le
        _ = 1 := by field_simp
    have hγ1 : (1 - u) * gammaG g ≤ 1 := by
      rw [hγ]
      have : (g ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hg)
      nlinarith
    have e : (1 + g / s) * ((1 - u) * gammaG g) = (1 - u) * gammaG g + g * s := by
      field_simp
      nlinarith [hss]
    calc Q = (W : ℝ) * (ellProp g L u * ((1 - u) * gammaG g)) := by rw [hQ]; ring
      _ ≤ (W : ℝ) * ((1 + g / s) * ((1 - u) * gammaG g)) := by
          gcongr
          have := loopsStep_gammaG_pos g
          positivity
      _ = (W : ℝ) * ((1 - u) * gammaG g + g * s) := by rw [e]
      _ ≤ (W : ℝ) * (1 + 1) := by gcongr
      _ = 2 * W := by ring
  rw [hz]
  constructor
  · rw [← div_eq_mul_inv, le_div_iff₀ hQpos]; linarith
  · rw [← div_eq_mul_inv, div_le_iff₀ hQpos]; linarith

/-- The rows of the primitive loops of lengths `2, …, k`, uniformly (Lemma 5.2
[fo:lem:deterministic], free-label rows of `F_n = W^{n-1}𝒦_n`), with the coupling threshold
depending on `κ` only. -/
private theorem loopsStep_rows (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ : ℝ, 1 ≤ Cκ ∧ ∀ k : ℕ, ∃ Cs C' : ℝ, 0 < Cs ∧ 0 < C' ∧
      ∀ g : ℝ, Cκ ≤ g → ∀ L : ℕ, 3 ≤ L → Cs * g ^ 2 ≤ L → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ m : ℂ,
      IsDysonRootV (hopB g) (gammaG g) L E m → ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 →
      ∀ n : ℕ, 2 ≤ n → n ≤ k → ∀ (i : Fin n) (a : Fin n → Fin L) (σ : Fin n → Bool),
        ∑ b : Fin L, ‖primLoopF g L E m t (Function.update a i b) σ‖ ≤ C' * g ^ 2 := by
  obtain ⟨Cκ, hCκ, H⟩ := primLoopF_freeLabel' κ hκ hκ2
  refine ⟨Cκ, hCκ, fun k => ?_⟩
  induction k with
  | zero =>
    exact ⟨1, 1, one_pos, one_pos, fun g _ L _ _ E _ m _ t _ _ n hn2 hn0 => by omega⟩
  | succ k ih =>
    obtain ⟨Cs, C', hCs, hC', Hk⟩ := ih
    by_cases hk : 2 ≤ k + 1
    · obtain ⟨Cs1, C1, hCs1, hC1, H1⟩ := H (k + 1) hk
      refine ⟨max Cs Cs1, max C' C1, lt_max_of_lt_left hCs, lt_max_of_lt_left hC', ?_⟩
      intro g hg L hL hCsL E hE m hm t ht0 ht n hn2 hnk i a σ
      have hg2 : 0 ≤ g ^ 2 := sq_nonneg g
      have hCsL' : ∀ c, c ≤ max Cs Cs1 → c * g ^ 2 ≤ L := fun c hc =>
        le_trans (mul_le_mul_of_nonneg_right hc hg2) hCsL
      rcases (show n ≤ k ∨ n = k + 1 by omega) with h | rfl
      · exact (Hk g hg L hL (hCsL' Cs (le_max_left _ _)) E hE m hm t ht0 ht n hn2 h i a σ).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hg2)
      · exact (H1 g hg L hL (hCsL' Cs1 (le_max_right _ _)) E hE m hm t ht0 ht i a σ).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hg2)
    · exact ⟨Cs, C', hCs, hC', fun g hg L hL hCsL E hE m hm t ht0 ht n hn2 hnk =>
        Hk g hg L hL hCsL E hE m hm t ht0 ht n hn2 (by omega)⟩

/-- From the row of `F_n` to the row of `𝒦_n = W^{1-n} F_n` on the scale `Z` with `2WZ ≥ 1`:
`γW Σ_c |𝒦_n| ≤ C' 2^k Z^{n-2}` for `2 ≤ n ≤ k`. -/
private theorem loopsStep_row_scale {g : ℝ} (hg : 1 ≤ g) {W L n k : ℕ} (hW : 1 ≤ W) (E : ℝ)
    (m : ℂ) (t : ℝ) (b : Fin n → Fin L) (s : Fin n → Bool) (i : Fin n) (hn : 2 ≤ n)
    (hnk : n ≤ k) {C' Z : ℝ} (hC' : 0 ≤ C') (hZ : 1 ≤ 2 * W * Z)
    (h : ∑ c : Fin L, ‖primLoopF g L E m t (Function.update b i c) s‖ ≤ C' * g ^ 2) :
    gammaG g * W * ∑ c : Fin L, ‖primLoop g W L E m t (Function.update b i c) s‖ ≤
      C' * 2 ^ k * Z ^ (n - 2) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hZ0 : 0 < Z := by
    by_contra hz
    have hz : Z ≤ 0 := not_lt.mp hz
    have : 2 * (W : ℝ) * Z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hz
    linarith
  have hγ := loopsStep_gammaG_eq hg
  have hg2 : 0 < g ^ 2 := by positivity
  have he : ∀ c, ‖primLoop g W L E m t (Function.update b i c) s‖ =
      ((W : ℝ) ^ (n' + 1))⁻¹ * ‖primLoopF g L E m t (Function.update b i c) s‖ := by
    intro c
    have e1 : primLoop g W L E m t (Function.update b i c) s =
        (W : ℂ) ^ (1 - ((n' + 2 : ℕ) : ℤ)) * primLoopF g L E m t (Function.update b i c) s := rfl
    rw [e1, norm_mul, norm_zpow, Complex.norm_natCast]
    rw [show (1 : ℤ) - ((n' + 2 : ℕ) : ℤ) = -((n' + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
      zpow_natCast]
  simp only [he, ← Finset.mul_sum]
  have hWinv : (W : ℝ)⁻¹ ≤ 2 * Z := by
    rw [inv_le_iff_one_le_mul₀ hWpos]; linarith
  have e2 : gammaG g * W * (((W : ℝ) ^ (n' + 1))⁻¹ * (C' * g ^ 2)) = C' * ((W : ℝ)⁻¹) ^ n' := by
    rw [hγ, inv_pow]
    field_simp
    ring
  calc gammaG g * W * (((W : ℝ) ^ (n' + 1))⁻¹ *
        ∑ c : Fin L, ‖primLoopF g L E m t (Function.update b i c) s‖) ≤
      gammaG g * W * (((W : ℝ) ^ (n' + 1))⁻¹ * (C' * g ^ 2)) := by
        have := loopsStep_gammaG_pos g
        gcongr
    _ = C' * ((W : ℝ)⁻¹) ^ n' := e2
    _ ≤ C' * (2 * Z) ^ n' := by gcongr
    _ = C' * 2 ^ n' * Z ^ n' := by rw [mul_pow]; ring
    _ ≤ C' * 2 ^ k * Z ^ (n' + 2 - 2) := by
        rw [show n' + 2 - 2 = n' by omega]
        gcongr
        · norm_num
        · omega

end Scales

/-! ### Rates at a good matrix -/

section GoodRates

/-- `γ/η_u ≤ C/(1-u)` when `Im m ≥ C⁻¹`. -/
private theorem loopsStep_theta_bound (g : ℝ) (m : ℂ) {u C₀ : ℝ} (hu : u < 1) (hC₀ : 0 < C₀)
    (hmim : C₀⁻¹ ≤ m.im) : gammaG g / etaChar g m u ≤ C₀ / (1 - u) := by
  have hγ := loopsStep_gammaG_pos g
  have hm0 : 0 < m.im := lt_of_lt_of_le (inv_pos.2 hC₀) hmim
  have h1u : 0 < 1 - u := by linarith
  have e : gammaG g / etaChar g m u = 1 / ((1 - u) * m.im) := by
    unfold etaChar; field_simp
  rw [e, div_le_div_iff₀ (by positivity) h1u]
  have : 1 ≤ C₀ * m.im := by
    have := mul_le_mul_of_nonneg_left hmim hC₀.le
    rwa [mul_inv_cancel₀ hC₀.ne'] at this
  nlinarith

/-- The rate of one loop error at a good matrix, relative to `env = (2W)^{-k}`:
`|𝒢D_k|/env ≤ κ_l X/(1-u)` with `κ_l = ((k+1)R + 2)(C_S + 1) + 2`, from the deterministic rates
of (5.17) [fo:eq:error-hierarchy] with `X = ω`, `τ = ωζ_u`, `Z = ζ_u`, `Λ_l = ω` and
`|D_k| ≤ (C_S + 1) env X` for every word. -/
private theorem loopsStep_good_gen (g E : ℝ) (m : ℂ) {W L k : ℕ} (hW : 1 ≤ W) (hL : 3 ≤ L)
    (hk : 2 ≤ k) (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {u : ℝ} (hu0 : 0 ≤ u)
    (hu : u ≤ 1 / 2) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    {ω ζ R C₀ CS Xs : ℝ} (hω : 1 ≤ ω) (hζ1 : 1 ≤ 2 * W * ζ) (hζ2 : W * ζ ≤ 2) (hR : 0 ≤ R)
    (hCS : 0 ≤ CS) (hC₀ : 0 < C₀) (hmim : C₀⁻¹ ≤ m.im) (hωζ : ω * ζ ≤ m.im)
    (hωl : 2 ^ (k + 1) * k * C₀ ≤ ω) (hωc : (k : ℝ) ^ 2 * 4 ^ k * (2 * R + 2 ^ k * C₀) ≤ ω)
    (hXs : ω ^ (k + 2) ≤ Xs)
    (hX : ∀ c d, ‖blockOf (resolventMat M (zChar g E m u)) c d‖ ≤ ω)
    (hτ : ∀ c, ‖blockTr (resolventMat M (zChar g E m u)) c c - m‖ ≤ ω * ζ)
    (hK : ∀ n : ℕ, 2 ≤ n → n ≤ k → ∀ (b : Fin n → Fin L) (s : Fin n → Bool) (i : Fin n),
      gammaG g * W * ∑ c : Fin L, ‖primLoop g W L E m u (Function.update b i c) s‖ ≤
        R * ζ ^ (n - 2))
    (hlow : ∀ n : ℕ, 2 ≤ n → n < k → ∀ (b : Fin n → Fin L) (s : Fin n → Bool),
      ‖resLoop g E m b s u M - primLoop g W L E m u b s‖ ≤ ω * ζ ^ n)
    (hall : ∀ (b : Fin k → Fin L) (s : Fin k → Bool),
      ‖resLoop g E m b s u M - primLoop g W L E m u b s‖ ≤
        (CS + 1) * ((2 * W : ℝ) ^ k)⁻¹ * Xs)
    (a : Fin k → Fin L) (σ : Fin k → Bool) :
    ‖blockGen W L (gammaG g)
        (fun r N => resLoop g E m a σ r N - primLoop g W L E m r a σ) u M‖ /
        ((2 * W : ℝ) ^ k)⁻¹ ≤
      (((k + 1) * R + 2) * (CS + 1) + 2) * Xs / (1 - u) := by
  have hγ := loopsStep_gammaG_pos g
  have hm0 : 0 < m.im := hm.1
  have hu1 : u < 1 := by linarith
  have h1u : 0 < 1 - u := by linarith
  have hη : 0 < etaChar g m u := etaChar_pos g m hm0 hu1
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hζ0 : 0 < ζ := by
    by_contra h
    have h : ζ ≤ 0 := not_lt.mp h
    have : 2 * (W : ℝ) * ζ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    linarith
  have hω0 : 0 < ω := by linarith
  have hXs0 : 0 < Xs := lt_of_lt_of_le (by positivity) hXs
  have hϑ := loopsStep_theta_bound g m hu1 hC₀ hmim
  set Λ := (CS + 1) * ((2 * W : ℝ) ^ k)⁻¹ * Xs with hΛ
  have hgen := loopsStep_gen_le g E m hW hL hk hm (u := u) ⟨by linarith, hu1⟩ hM
    (X := ω) (τ := ω * ζ) (Z := ζ) (R := R) (Λl := ω) (Λ := Λ) hω hζ1 hω0.le hX hτ hK hlow
    hall a σ
  set E2 : ℝ := (2 * W : ℝ) ^ k with hE2
  have hE2pos : 0 < E2 := by positivity
  rw [div_eq_mul_inv, inv_inv]
  have hA : 1 ≤ 1 / (1 - u) := by rw [le_div_iff₀ h1u]; linarith
  set A := 1 / (1 - u) with hAdef
  have hdivA : ∀ x : ℝ, x / (1 - u) = x * A := fun x => by rw [hAdef]; ring
  rw [hdivA]
  set ϑ := gammaG g / etaChar g m u with hϑdef
  have hϑ0 : 0 ≤ ϑ := by positivity
  have hϑA : ϑ ≤ C₀ * A := by rw [hdivA] at hϑ; exact hϑ
  -- the linear coefficient
  have hcoef : (k * R + if k = 2 then gammaG g * (m.im + ω * ζ) / etaChar g m u + R else 0) ≤
      ((k + 1) * R + 2) * A := by
    have h2 : gammaG g * (m.im + ω * ζ) / etaChar g m u ≤ 2 * A := by
      have e : gammaG g * (m.im + ω * ζ) / etaChar g m u = (m.im + ω * ζ) * (1 / m.im) * A := by
        rw [hAdef]; unfold etaChar; field_simp
      rw [e]
      have : (m.im + ω * ζ) * (1 / m.im) ≤ 2 := by
        rw [mul_one_div, div_le_iff₀ hm0]; linarith
      have hA0 : 0 ≤ A := by linarith
      nlinarith
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h3 : ((k : ℝ) + 1) * R ≤ ((k : ℝ) + 1) * R * A :=
      le_mul_of_one_le_right (by positivity) hA
    split_ifs
    · linarith
    · linarith
  have hΛE : Λ * E2 = (CS + 1) * Xs := by
    rw [hΛ]; field_simp
  have t1 : (k * R + if k = 2 then gammaG g * (m.im + ω * ζ) / etaChar g m u + R else 0) * Λ *
      E2 ≤ ((k + 1) * R + 2) * (CS + 1) * Xs * A := by
    rw [mul_assoc, hΛE]
    have : 0 ≤ (CS + 1) * Xs := by positivity
    calc _ ≤ ((k + 1) * R + 2) * A * ((CS + 1) * Xs) := mul_le_mul_of_nonneg_right hcoef this
      _ = _ := by ring
  -- the light term
  have t2 : gammaG g * W * k * (ω * ζ) * ω ^ k / ((W : ℝ) ^ k * etaChar g m u) * E2 ≤
      Xs * A := by
    have e : gammaG g * W * k * (ω * ζ) * ω ^ k / ((W : ℝ) ^ k * etaChar g m u) * E2 =
        ϑ * k * ω ^ (k + 1) * (W * ζ) * 2 ^ k := by
      rw [hϑdef, hE2, mul_pow]
      field_simp
      ring
    rw [e]
    have hA0 : 0 ≤ A := by linarith
    have hC0A : 0 ≤ C₀ * A := by positivity
    calc ϑ * k * ω ^ (k + 1) * (W * ζ) * 2 ^ k =
        ϑ * (((k : ℝ) * ω ^ (k + 1)) * (W * ζ) * 2 ^ k) := by ring
      _ ≤ (C₀ * A) * (((k : ℝ) * ω ^ (k + 1)) * 2 * 2 ^ k) :=
          mul_le_mul hϑA (by gcongr) (by positivity) hC0A
      _ = (2 ^ (k + 1) * k * C₀) * ω ^ (k + 1) * A := by ring
      _ ≤ ω * ω ^ (k + 1) * A := by gcongr
      _ = ω ^ (k + 2) * A := by ring
      _ ≤ Xs * A := by gcongr
  -- the cut term
  have t3 : (k : ℝ) ^ 2 * ω * ζ ^ k * (2 * R + 2 ^ k * gammaG g * ω ^ k / etaChar g m u) * E2 ≤
      Xs * A := by
    have e : (k : ℝ) ^ 2 * ω * ζ ^ k * (2 * R + 2 ^ k * gammaG g * ω ^ k / etaChar g m u) * E2 =
        (k : ℝ) ^ 2 * ω * (2 * W * ζ) ^ k * (2 * R + 2 ^ k * ϑ * ω ^ k) := by
      rw [hϑdef, hE2, mul_pow, mul_pow, mul_pow]; ring
    rw [e]
    have hWζ : 2 * W * ζ ≤ 4 := by linarith
    have hωk : 1 ≤ ω ^ k := one_le_pow₀ hω
    have hA0 : 0 ≤ A := by linarith
    have hin : 2 * R + 2 ^ k * ϑ * ω ^ k ≤ (2 * R + 2 ^ k * C₀) * ω ^ k * A := by
      have h1 : 2 * R ≤ 2 * R * (ω ^ k * A) :=
        le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le hωk hA)
      have h2 : (2 ^ k * ω ^ k) * ϑ ≤ (2 ^ k * ω ^ k) * (C₀ * A) :=
        mul_le_mul_of_nonneg_left hϑA (by positivity)
      calc 2 * R + 2 ^ k * ϑ * ω ^ k = 2 * R + (2 ^ k * ω ^ k) * ϑ := by ring
        _ ≤ 2 * R * (ω ^ k * A) + (2 ^ k * ω ^ k) * (C₀ * A) := add_le_add h1 h2
        _ = (2 * R + 2 ^ k * C₀) * ω ^ k * A := by ring
    calc (k : ℝ) ^ 2 * ω * (2 * W * ζ) ^ k * (2 * R + 2 ^ k * ϑ * ω ^ k) ≤
        (k : ℝ) ^ 2 * ω * 4 ^ k * ((2 * R + 2 ^ k * C₀) * ω ^ k * A) := by
          have : 0 ≤ 2 * W * ζ := by positivity
          gcongr
      _ = ((k : ℝ) ^ 2 * 4 ^ k * (2 * R + 2 ^ k * C₀)) * ω ^ (k + 1) * A := by ring
      _ ≤ ω * ω ^ (k + 1) * A := by gcongr
      _ = ω ^ (k + 2) * A := by ring
      _ ≤ Xs * A := by gcongr
  calc ‖blockGen W L (gammaG g)
        (fun r N => resLoop g E m a σ r N - primLoop g W L E m r a σ) u M‖ * E2 ≤
      ((k * R + if k = 2 then gammaG g * (m.im + ω * ζ) / etaChar g m u + R else 0) * Λ +
        gammaG g * W * k * (ω * ζ) * ω ^ k / ((W : ℝ) ^ k * etaChar g m u) +
        (k : ℝ) ^ 2 * ω * ζ ^ k * (2 * R + 2 ^ k * gammaG g * ω ^ k / etaChar g m u)) * E2 :=
        mul_le_mul_of_nonneg_right hgen hE2pos.le
    _ = (k * R + if k = 2 then gammaG g * (m.im + ω * ζ) / etaChar g m u + R else 0) * Λ * E2 +
        gammaG g * W * k * (ω * ζ) * ω ^ k / ((W : ℝ) ^ k * etaChar g m u) * E2 +
        (k : ℝ) ^ 2 * ω * ζ ^ k * (2 * R + 2 ^ k * gammaG g * ω ^ k / etaChar g m u) * E2 := by
        ring
    _ ≤ ((k + 1) * R + 2) * (CS + 1) * Xs * A + Xs * A + Xs * A := by gcongr
    _ = (((k + 1) * R + 2) * (CS + 1) + 2) * Xs * A := by ring

/-- The bracket of one loop error at a good matrix, relative to `env² = (2W)^{-2k}`:
`Re Γ(D_k)/env² ≤ (k² 4^k C/ω³) X²/(1-u)`. -/
private theorem loopsStep_good_gamma (g E : ℝ) (m : ℂ) {W L k : ℕ} (hW : 1 ≤ W) (hk : 1 ≤ k)
    {u : ℝ} (hu1 : u < 1) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    {ω C₀ Xs : ℝ} (hω : 1 ≤ ω) (hC₀ : 0 < C₀) (hmim : C₀⁻¹ ≤ m.im) (hXs : ω ^ (k + 2) ≤ Xs)
    (hX : ∀ c d, ‖blockOf (resolventMat M (zChar g E m u)) c d‖ ≤ ω)
    (a : Fin k → Fin L) (σ : Fin k → Bool) :
    (blockGamma W L (gammaG g) (resLoop g E m a σ u) (resLoop g E m a σ u) M).re /
        (((2 * W : ℝ) ^ k)⁻¹) ^ 2 ≤
      (k : ℝ) ^ 2 * 4 ^ k * C₀ / ω ^ 3 * Xs ^ 2 / (1 - u) := by
  have hm0 : 0 < m.im := lt_of_lt_of_le (inv_pos.2 hC₀) hmim
  have h1u : 0 < 1 - u := by linarith
  have hη : 0 < etaChar g m u := etaChar_pos g m hm0 hu1
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hω0 : 0 < ω := by linarith
  have hϑ := loopsStep_theta_bound g m hu1 hC₀ hmim
  have h := blockGamma_loopTr_le g E m hm0 hW hk hu1 hM ω hX a σ
  have e1 : (k : ℝ) ^ 2 * gammaG g * ω ^ (2 * k + 1) / ((W : ℝ) ^ (2 * k) * etaChar g m u) /
      (((2 * W : ℝ) ^ k)⁻¹) ^ 2 =
      (k : ℝ) ^ 2 * 4 ^ k * (gammaG g / etaChar g m u) * ω ^ (2 * k + 1) := by
    rw [inv_pow, ← pow_mul, mul_pow, show (4 : ℝ) ^ k = 2 ^ (k * 2) by
      rw [pow_mul']; norm_num, mul_comm k 2]
    field_simp
  have hXs2 : ω ^ (2 * k + 4) ≤ Xs ^ 2 := by
    rw [show 2 * k + 4 = (k + 2) * 2 by ring, pow_mul]
    exact pow_le_pow_left₀ (by positivity) hXs 2
  calc (blockGamma W L (gammaG g) (resLoop g E m a σ u) (resLoop g E m a σ u) M).re /
        (((2 * W : ℝ) ^ k)⁻¹) ^ 2 ≤
      (k : ℝ) ^ 2 * gammaG g * ω ^ (2 * k + 1) / ((W : ℝ) ^ (2 * k) * etaChar g m u) /
        (((2 * W : ℝ) ^ k)⁻¹) ^ 2 := by gcongr
    _ = (k : ℝ) ^ 2 * 4 ^ k * (gammaG g / etaChar g m u) * ω ^ (2 * k + 1) := e1
    _ ≤ (k : ℝ) ^ 2 * 4 ^ k * (C₀ / (1 - u)) * ω ^ (2 * k + 1) := by gcongr
    _ = (k : ℝ) ^ 2 * 4 ^ k * C₀ / ω ^ 3 * ω ^ (2 * k + 4) / (1 - u) := by
        rw [show 2 * k + 4 = (2 * k + 1) + 3 by ring, pow_add]
        field_simp
        ring
    _ ≤ (k : ℝ) ^ 2 * 4 ^ k * C₀ / ω ^ 3 * Xs ^ 2 / (1 - u) := by gcongr

end GoodRates

/-! ### The surrogate: rates, crude moments and Markov -/

section Surr

/-- A field in the class is `C²` in space and differentiable in time at a time of the window. -/
private theorem loopsStep_heat_slice {ι : Type*} [Fintype ι] {F : ℝ → (ι → ℝ) → ℂ} {a b : ℝ}
    (hF : HeatClass F a b) {u : ℝ} (hu : u ∈ Set.Ioo a b) :
    Continuous (F u) ∧ ContDiff ℝ 2 (F u) ∧ ∀ y, DifferentiableAt ℝ (fun r => F r y) u := by
  obtain ⟨hc, -, ⟨Fu, hFu, -, -⟩, ⟨DF, D2F, hD, hD2, -, hcD2, -⟩⟩ := hF
  have hc2 : Continuous (D2F u) :=
    hcD2.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hu, trivial⟩
  have h1 : ContDiff ℝ 1 (DF u) := contDiff_one_iff_hasFDerivAt.2 ⟨D2F u, hc2, hD2 u hu⟩
  have h2 : ContDiff ℝ (1 + 1) (F u) :=
    contDiff_succ_iff_hasFDerivAt (n := 1).2 ⟨DF u, h1, hD u hu⟩
  have h3 : ContDiff ℝ 2 (F u) := by rw [← one_add_one_eq_two]; exact h2
  exact ⟨h3.continuous, h3, fun y => (hFu u hu y).differentiableAt⟩

/-- The carré du champ `Γ(F, F)` is real and nonnegative: its real part is its norm. -/
private theorem loopsStep_gamma_re_eq_norm {ι : Type*} [Fintype ι] {σ2 : ℝ} (hσ2 : 0 ≤ σ2)
    (F : (ι → ℝ) → ℂ) (y : ι → ℝ) :
    (coordGamma σ2 F F y).re = ‖coordGamma σ2 F F y‖ := by
  have e : coordGamma σ2 F F y =
      ((σ2 * ∑ i, ‖deriv (fun e : ℝ => F (y + e • Pi.single i 1)) 0‖ ^ 2 : ℝ) : ℂ) := by
    simp only [coordGamma, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  rw [e, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact mul_nonneg hσ2 (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- A constant shift does not change the carré du champ. -/
private theorem loopsStep_coordGamma_sub_const {ι : Type*} [Fintype ι] (σ2 : ℝ)
    (f : (ι → ℝ) → ℂ) (c : ℂ) (y : ι → ℝ) :
    coordGamma σ2 (fun z => f z - c) (fun z => f z - c) y = coordGamma σ2 f f y := by
  simp only [coordGamma, deriv_sub_const]

/-- The surrogate is at least `δ`. -/
private theorem loopsStep_lqSurr_ge {S : Type*} [Fintype S] [Nonempty S] {q : ℕ} (hq : 1 ≤ q)
    {env : S → ℝ} (henv : ∀ s, 0 < env s) {δ : ℝ} (hδ : 0 < δ) (y : S → ℂ) :
    δ ≤ lqSurr q env δ y := by
  obtain ⟨s₀⟩ := ‹Nonempty S›
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1 : (δ ^ 2) ^ q ≤ ∑ s, (‖y s‖ ^ 2 / env s ^ 2 + δ ^ 2) ^ q := by
    calc (δ ^ 2) ^ q ≤ (‖y s₀‖ ^ 2 / env s₀ ^ 2 + δ ^ 2) ^ q := by
          exact pow_le_pow_left₀ (sq_nonneg δ)
            (le_add_of_nonneg_left (by have := henv s₀; positivity)) q
      _ ≤ _ := Finset.single_le_sum (f := fun s => (‖y s‖ ^ 2 / env s ^ 2 + δ ^ 2) ^ q)
          (fun s _ => by have := henv s; positivity) (Finset.mem_univ s₀)
  have e : ((δ ^ 2) ^ q) ^ ((1 : ℝ) / (2 * q)) = δ := by
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    have : ((2 * q : ℕ) : ℝ) * (1 / (2 * q)) = 1 := by push_cast; field_simp
    rw [this, Real.rpow_one]
  calc δ = ((δ ^ 2) ^ q) ^ ((1 : ℝ) / (2 * q)) := e.symm
    _ ≤ lqSurr q env δ y := by
        unfold lqSurr
        exact Real.rpow_le_rpow (by positivity) h1 (by positivity)

/-- The surrogate is nonnegative. -/
private theorem loopsStep_lqSurr_nonneg {S : Type*} [Fintype S] (q : ℕ) (env : S → ℝ) (δ : ℝ)
    (y : S → ℂ) : 0 ≤ lqSurr q env δ y := by
  unfold lqSurr
  positivity

/-- `|S|^{1/q} ≤ 1.003` from `|S|^{1/(2q)} ≤ 1.001`. -/
private theorem loopsStep_card_q {S : Type*} [Fintype S] {q : ℕ} (hq : 1 ≤ q)
    (hS : (Fintype.card S : ℝ) ^ ((1 : ℝ) / (2 * q)) ≤ 1.001) :
    (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) ≤ 1.003 := by
  have e : (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) =
      ((Fintype.card S : ℝ) ^ ((1 : ℝ) / (2 * q))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    have : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
    norm_num
  rw [e]
  have h0 : 0 ≤ (Fintype.card S : ℝ) ^ ((1 : ℝ) / (2 * q)) := by positivity
  calc ((Fintype.card S : ℝ) ^ ((1 : ℝ) / (2 * q))) ^ 2 ≤ 1.001 ^ 2 := by gcongr
    _ ≤ 1.003 := by norm_num

/-- The coordinate generator of the surrogate of a family of fields in the class is real. -/
private theorem loopsStep_norm_coordGen_surr {ι S : Type*} [Fintype ι] [Fintype S] (σ2 : ℝ)
    {q : ℕ} (hq : 1 ≤ q) {env : S → ℝ} (henv : ∀ s, 0 < env s) {δ : ℝ} (hδ : 0 < δ)
    (Y : S → ℝ → (ι → ℝ) → ℂ) {a b u : ℝ} (hY : ∀ s, HeatClass (Y s) a b)
    (hu : u ∈ Set.Ioo a b) (y : ι → ℝ) :
    ‖coordGen σ2 (fun r z => ((lqSurr q env δ (fun s => Y s r z) : ℝ) : ℂ)) u y‖ =
      |(coordGen σ2 (fun r z => ((lqSurr q env δ (fun s => Y s r z) : ℝ) : ℂ)) u y).re| := by
  have hsl := fun s => loopsStep_heat_slice (hY s) hu
  rw [coordGen_comp_vec σ2 (lqSurr q env δ) (lqSurr_contDiff hq henv hδ) Y u y
    (fun s => (hsl s).2.2 y) (fun s => (hsl s).2.1), Complex.norm_real, Complex.ofReal_re,
    Real.norm_eq_abs]

/-- Rates of the surrogate from the normalized rates of its components:
`|𝒢X| ≤ κ X/(1-u)` and `Γ(X) ≤ b X²/(1-u)` when `|S|^{1/(2q)} ≤ 1.001`,
`|𝒢Y_s|/env ≤ κ_l X/(1-u)`, `Re Γ(Y_s)/env² ≤ b_h X²/(1-u)`,
`1.001 κ_l + 1.003 q b_h ≤ κ` and `1.003 b_h ≤ b`. -/
private theorem loopsStep_surr_rates {ι S : Type*} [Fintype ι] [Fintype S] (σ2 : ℝ)
    (hσ2 : 0 ≤ σ2) {q : ℕ} (hq : 1 ≤ q) {env : S → ℝ} (henv : ∀ s, 0 < env s) {δ : ℝ}
    (hδ : 0 < δ) (Y : S → ℝ → (ι → ℝ) → ℂ) {a b u : ℝ} (hY : ∀ s, HeatClass (Y s) a b)
    (hu : u ∈ Set.Ioo a b) (hu1 : u < 1) (y : ι → ℝ)
    (hS : (Fintype.card S : ℝ) ^ ((1 : ℝ) / (2 * q)) ≤ 1.001) {κl bh κ bΓ : ℝ}
    (hκl : 0 ≤ κl) (hbh : 0 ≤ bh)
    (hgen : ∀ s, ‖coordGen σ2 (Y s) u y‖ / env s ≤
      κl * lqSurr q env δ (fun s => Y s u y) / (1 - u))
    (hgam : ∀ s, (coordGamma σ2 (Y s u) (Y s u) y).re / env s ^ 2 ≤
      bh * lqSurr q env δ (fun s => Y s u y) ^ 2 / (1 - u))
    (hκ : 1.001 * κl + 1.003 * q * bh ≤ κ) (hb : 1.003 * bh ≤ bΓ) :
    ‖coordGen σ2 (fun r z => ((lqSurr q env δ (fun s => Y s r z) : ℝ) : ℂ)) u y‖ ≤
        κ * lqSurr q env δ (fun s => Y s u y) / (1 - u) ∧
      ‖coordGamma σ2 (fun z => ((lqSurr q env δ (fun s => Y s u z) : ℝ) : ℂ))
          (fun z => ((lqSurr q env δ (fun s => Y s u z) : ℝ) : ℂ)) y‖ ≤
        bΓ * lqSurr q env δ (fun s => Y s u y) ^ 2 / (1 - u) := by
  set X := lqSurr q env δ (fun s => Y s u y) with hXdef
  have heu : 0 < 1 - u := by linarith
  have hX0 : 0 ≤ X := loopsStep_lqSurr_nonneg q env δ _
  have hsl := fun s => loopsStep_heat_slice (hY s) hu
  obtain ⟨h1, h2⟩ := coordGen_lqSurr_le σ2 hσ2 hq henv hδ Y u y (fun s => (hsl s).2.2 y)
    (fun s => (hsl s).2.1) hgen hgam
  rw [← hXdef] at h1
  have hS2 := loopsStep_card_q hq hS
  have hc1 : 0 ≤ (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) := by positivity
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  rw [loopsStep_norm_coordGen_surr σ2 hq henv hδ Y hY hu y,
    ← loopsStep_gamma_re_eq_norm hσ2]
  refine ⟨?_, ?_⟩
  · refine h1.trans ?_
    rcases eq_or_lt_of_le hX0 with hX | hX
    · rw [← hX]; simp
    · have e1 : (Fintype.card S : ℝ) ^ ((1 : ℝ) / (2 * q)) * (κl * X / (1 - u)) +
          q * (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) * (bh * X ^ 2 / (1 - u)) / X =
          ((Fintype.card S : ℝ) ^ ((1 : ℝ) / (2 * q)) * κl +
            q * (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) * bh) * X / (1 - u) := by
        field_simp
      rw [e1]
      have hcoef : (Fintype.card S : ℝ) ^ ((1 : ℝ) / (2 * q)) * κl +
          q * (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) * bh ≤ κ := by
        have a1 : (Fintype.card S : ℝ) ^ ((1 : ℝ) / (2 * q)) * κl ≤ 1.001 * κl :=
          mul_le_mul_of_nonneg_right hS hκl
        have a2 : q * (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) * bh ≤ 1.003 * q * bh := by
          have := mul_le_mul_of_nonneg_left hS2 hq0
          have := mul_le_mul_of_nonneg_right this hbh
          linarith
        linarith
      gcongr
  · refine h2.trans ?_
    calc (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) * (bh * X ^ 2 / (1 - u)) ≤
        1.003 * (bh * X ^ 2 / (1 - u)) := by gcongr
      _ ≤ bΓ * X ^ 2 / (1 - u) := by
        rw [← mul_div_assoc, ← mul_assoc]
        gcongr

/-- The crude pointwise bounds of the surrogate: with `c ≥ 1.001/env` and `c ≥ 1.003 q/env²`,
`|𝒢X| ≤ c Σ_s (|𝒢Y_s| + |Γ(Y_s)|)` and `Γ(X) ≤ c Σ_s |Γ(Y_s)|`, for `X ≥ 1`. -/
private theorem loopsStep_surr_crude {ι S : Type*} [Fintype ι] [Fintype S] (σ2 : ℝ)
    (hσ2 : 0 ≤ σ2) {q : ℕ} (hq : 1 ≤ q) {env : ℝ} (henv : 0 < env) {δ : ℝ} (hδ : 1 ≤ δ)
    [Nonempty S] (Y : S → ℝ → (ι → ℝ) → ℂ) {a b u : ℝ} (hY : ∀ s, HeatClass (Y s) a b)
    (hu : u ∈ Set.Ioo a b) (y : ι → ℝ)
    (hS : (Fintype.card S : ℝ) ^ ((1 : ℝ) / (2 * q)) ≤ 1.001) {c : ℝ}
    (hc1 : 1.001 / env ≤ c) (hc2 : 1.003 * q / env ^ 2 ≤ c) :
    ‖coordGen σ2 (fun r z => ((lqSurr q (fun _ => env) δ (fun s => Y s r z) : ℝ) : ℂ)) u y‖ ≤
        c * ∑ s, (‖coordGen σ2 (Y s) u y‖ + ‖coordGamma σ2 (Y s u) (Y s u) y‖) ∧
      ‖coordGamma σ2 (fun z => ((lqSurr q (fun _ => env) δ (fun s => Y s u z) : ℝ) : ℂ))
          (fun z => ((lqSurr q (fun _ => env) δ (fun s => Y s u z) : ℝ) : ℂ)) y‖ ≤
        c * ∑ s, ‖coordGamma σ2 (Y s u) (Y s u) y‖ := by
  set X := lqSurr q (fun _ => env) δ (fun s => Y s u y) with hXdef
  have hX1 : 1 ≤ X := le_trans hδ (loopsStep_lqSurr_ge hq (fun _ => henv) (by linarith) _)
  have hsl := fun s => loopsStep_heat_slice (hY s) hu
  set G := ∑ s, ‖coordGen σ2 (Y s) u y‖ with hG
  set H := ∑ s, ‖coordGamma σ2 (Y s u) (Y s u) y‖ with hH
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun s _ => norm_nonneg _
  have hH0 : 0 ≤ H := Finset.sum_nonneg fun s _ => norm_nonneg _
  have hgen : ∀ s, ‖coordGen σ2 (Y s) u y‖ / env ≤ G / env := fun s =>
    div_le_div_of_nonneg_right (Finset.single_le_sum (f := fun s => ‖coordGen σ2 (Y s) u y‖)
      (fun s _ => norm_nonneg _) (Finset.mem_univ s)) henv.le
  have hgam : ∀ s, (coordGamma σ2 (Y s u) (Y s u) y).re / env ^ 2 ≤ H / env ^ 2 := fun s =>
    div_le_div_of_nonneg_right ((Complex.re_le_norm _).trans
      (Finset.single_le_sum (f := fun s => ‖coordGamma σ2 (Y s u) (Y s u) y‖)
      (fun s _ => norm_nonneg _) (Finset.mem_univ s))) (by positivity)
  obtain ⟨h1, h2⟩ := coordGen_lqSurr_le σ2 hσ2 hq (fun _ => henv) (show (0 : ℝ) < δ by linarith)
    Y u y
    (fun s => (hsl s).2.2 y) (fun s => (hsl s).2.1) hgen hgam
  rw [← hXdef] at h1
  have hS2 := loopsStep_card_q hq hS
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hc0 : 0 ≤ c := le_trans (by positivity) hc1
  rw [loopsStep_norm_coordGen_surr σ2 hq (fun _ => henv) (by linarith) Y hY hu y,
    ← loopsStep_gamma_re_eq_norm hσ2]
  refine ⟨h1.trans ?_, h2.trans ?_⟩
  · have a1 : (Fintype.card S : ℝ) ^ ((1 : ℝ) / (2 * q)) * (G / env) ≤ c * G := by
      calc (Fintype.card S : ℝ) ^ ((1 : ℝ) / (2 * q)) * (G / env) ≤ 1.001 * (G / env) := by
            gcongr
        _ = 1.001 / env * G := by ring
        _ ≤ c * G := by gcongr
    have a2 : q * (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) * (H / env ^ 2) / X ≤ c * H := by
      have hXpos : 0 < X := by linarith
      rw [div_le_iff₀ hXpos]
      calc q * (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) * (H / env ^ 2) ≤
          q * 1.003 * (H / env ^ 2) := by gcongr
        _ = 1.003 * q / env ^ 2 * H := by ring
        _ ≤ c * H := by gcongr
        _ ≤ c * H * X := le_mul_of_one_le_right (by positivity) hX1
    calc _ ≤ c * G + c * H := add_le_add a1 a2
      _ = c * ∑ s, (‖coordGen σ2 (Y s) u y‖ + ‖coordGamma σ2 (Y s u) (Y s u) y‖) := by
          rw [Finset.sum_add_distrib]; ring
  · calc (Fintype.card S : ℝ) ^ ((1 : ℝ) / q) * (H / env ^ 2) ≤ 1.003 * (H / env ^ 2) := by
          gcongr
      _ ≤ 1.003 * q / env ^ 2 * H := by
          have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
          have e1 : 1.003 * (H / env ^ 2) = 1.003 / env ^ 2 * H := by ring
          rw [e1]
          gcongr
          linarith
      _ ≤ c * H := by gcongr

/-- A moment bound for a function dominated by `c` times a finite sum of functions with bounded
moments: `∫ F^n ≤ c^n |T|^n B`. -/
private theorem loopsStep_sum_moment {α : Type*} [MeasurableSpace α] (P : Measure α) {T : Type*}
    [Fintype T] (F : α → ℝ) (f : T → α → ℝ) (hf0 : ∀ t x, 0 ≤ f t x) {c : ℝ} (hc : 0 ≤ c)
    (hF : ∀ x, 0 ≤ F x) (hFle : ∀ x, F x ≤ c * ∑ t, f t x) {n : ℕ} (hn : 1 ≤ n) {B : ℝ}
    (hi : ∀ t, Integrable (fun x => f t x ^ n) P ∧ ∫ x, f t x ^ n ∂P ≤ B) :
    ∫ x, F x ^ n ∂P ≤ c ^ n * (Fintype.card T : ℝ) ^ n * B := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hpt : ∀ x, F x ^ (n' + 1) ≤
      c ^ (n' + 1) * ((Fintype.card T : ℝ) ^ n' * ∑ t, f t x ^ (n' + 1)) := by
    intro x
    have hs0 : 0 ≤ ∑ t, f t x := Finset.sum_nonneg fun t _ => hf0 t x
    have h1 : F x ^ (n' + 1) ≤ (c * ∑ t, f t x) ^ (n' + 1) :=
      pow_le_pow_left₀ (hF x) (hFle x) _
    have h2 := pow_sum_le_card_mul_sum_pow (s := Finset.univ) (f := fun t => f t x)
      (fun t _ => hf0 t x) n'
    rw [Finset.card_univ] at h2
    rw [mul_pow] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have hRi : Integrable (fun x => c ^ (n' + 1) *
      ((Fintype.card T : ℝ) ^ n' * ∑ t, f t x ^ (n' + 1))) P :=
    ((integrable_finsetSum Finset.univ fun t _ => (hi t).1).const_mul _).const_mul _
  calc ∫ x, F x ^ (n' + 1) ∂P ≤ ∫ x, c ^ (n' + 1) *
        ((Fintype.card T : ℝ) ^ n' * ∑ t, f t x ^ (n' + 1)) ∂P :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => pow_nonneg (hF x) _) hRi
          (Eventually.of_forall hpt)
    _ = c ^ (n' + 1) * ((Fintype.card T : ℝ) ^ n' * ∑ t, ∫ x, f t x ^ (n' + 1) ∂P) := by
        rw [integral_const_mul, integral_const_mul,
          integral_finsetSum Finset.univ fun t _ => (hi t).1]
    _ ≤ c ^ (n' + 1) * ((Fintype.card T : ℝ) ^ n' * ∑ _t : T, B) := by
        gcongr with t
        exact (hi t).2
    _ = c ^ (n' + 1) * (Fintype.card T : ℝ) ^ (n' + 1) * B := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- Markov's inequality: `P{f ≥ J} ≤ B/J` when `∫ f ≤ B`. -/
private theorem loopsStep_markov {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsProbabilityMeasure P] (f : α → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f P) {J B : ℝ}
    (hJ : 0 < J) (hB : ∫ x, f x ∂P ≤ B) : P {x | J ≤ f x} ≤ ENNReal.ofReal (B / J) := by
  have h := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hf0) hfi J
  have h1 : P.real {x | J ≤ f x} ≤ B / J := by
    rw [le_div_iff₀ hJ]; linarith
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
  exact ENNReal.ofReal_le_ofReal h1

end Surr

/-! ### One step at a fixed `W` -/

section AtW

/-- The sampling property (5.26) [fo:eq:spatial-sampling] of the loop errors at `(u, y)` with
constant `C_S`, sample set `S` and floor `W^{-fl}`. -/
private def loopsStepSamp (g E : ℝ) (W L k : ℕ) (S : Finset (Fin k → Fin L)) (CS fl u : ℝ)
    (y : Ω W L) : Prop :=
  ∀ (σ : Fin k → Bool) (l : Fin k → Fin L),
    ‖loopErrField g E (mRoot g L E) W L l σ u y‖ ≤
      CS * (⨆ s : S, ‖loopErrField g E (mRoot g L E) W L (s : Fin k → Fin L) σ u y‖) +
        (W : ℝ) ^ (-fl)

/-- The good set at time `u`: the block bound `ω`, the averaged bound `ω ζ_u`, the shorter loop
errors `ω ζ_u^n` and the sampling property, at the slice `A_g ⊗ I + Σ y_{c,k} T_{c,k}`. -/
private def loopsStepGood (g E : ℝ) (W L k : ℕ) (S : Finset (Fin k → Fin L)) (ω CS fl u : ℝ)
    (y : Ω W L) : Prop :=
  (∀ c d, ‖blockOf (resolventMat (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y)
      (zChar g E (mRoot g L E) u)) c d‖ ≤ ω) ∧
  (∀ c, ‖blockTr (resolventMat (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y)
      (zChar g E (mRoot g L E) u)) c c - mRoot g L E‖ ≤ ω * zetaProp g W L u) ∧
  (∀ n : ℕ, 2 ≤ n → n < k → ∀ (b : Fin n → Fin L) (s : Fin n → Bool),
      ‖loopErrField g E (mRoot g L E) W L b s u y‖ ≤ ω * zetaProp g W L u ^ n) ∧
  loopsStepSamp g E W L k S CS fl u y

/-- `A_g ⊗ I + Σ y_{c,k} T_{c,k}` is Hermitian. -/
private theorem loopsStep_slice_herm (g : ℝ) {W L : ℕ} (hW : 1 ≤ W) (y : Ω W L) :
    (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y).IsHermitian := by
  have hA : (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)).IsHermitian := by
    have h := flowH_isHermitian g W L 0 0
    simpa [flowH, blockFlow] using h
  have e := blockFlow_eq_blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
    (s := W) (Nat.cast_nonneg W) y
  have hW0 : (W : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [div_self hW0, Real.sqrt_one, one_smul] at e
  rw [← e]
  exact blockFlow_isHermitian W L hA _ y

/-- The loop errors vanish at time `0` at the origin of the slice. -/
private theorem loopsStep_field_zero (g E : ℝ) {W L : ℕ} (hW : 1 ≤ W) (hL : 3 ≤ L)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E (mRoot g L E)) {k : ℕ} (a : Fin k → Fin L)
    (σ : Fin k → Bool) : loopErrField g E (mRoot g L E) W L a σ 0 0 = 0 := by
  unfold loopErrField
  have h0 : blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) 0 =
      flowH g W L 0 0 := by
    have hγ : 0 ≤ gammaG g := (loopsStep_gammaG_pos g).le
    unfold flowH
    rw [blockFlow_eq_blockSlice _ _ _ (by simp), smul_zero]
  rw [h0, resolvent_flow_zero, primLoop_init g W L hW hL E _ hm, sub_self]

set_option maxHeartbeats 1000000 in
-- The proof is long: the generator and bracket bounds, the crude moments and Markov's bound.
/-- One step of the induction at a fixed `W` and a point `(g, E, L, v)`: from the measure of the
bad sets at the times `u ∈ (0, v)`, the sampling at `v`, the crude moments and the parameter
inequalities, the moment comparison (Appendix C.3 [sec:gc-one-step]) iterated on the `ℓ^{2q}`
surrogate of the sampled loop errors and Markov's inequality give
`ℙ(max_{a,σ} |D_k(v)| > W^ε ζ_v^k) ≤ W^{-D}`. -/
private theorem loopsStep_atW (g E : ℝ) {W L k : ℕ} (hW : 2 ≤ W) (hL : 3 ≤ L) (hk : 2 ≤ k)
    (hg : 1 ≤ g) (hgL : g ^ 2 ≤ L)
    (hroot : IsDysonRootV (hopB g) (gammaG g) L E (mRoot g L E))
    {C₀ : ℝ} (hC₀ : 0 < C₀) (hmim : C₀⁻¹ ≤ (mRoot g L E).im)
    {v : ℝ} (hv0 : 0 < v) (hv : v ≤ 1 / 2)
    (S : Finset (Fin k → Fin L)) (hS : S.Nonempty) {q p : ℕ} (hq : 1 ≤ q) (hp : 1 ≤ p)
    {ω R CS fl δb δv K M₄ M₂ J ε D : ℝ}
    (hω : 1 ≤ ω) (hR : 0 ≤ R) (hCS : 0 ≤ CS) (hδb : 0 ≤ δb) (hδv : 0 ≤ δv) (hK0 : 0 ≤ K)
    (hJ : 0 < J)
    (hωζ : 2 * ω ≤ W * C₀⁻¹)
    (hωl : 2 ^ (k + 1) * k * C₀ ≤ ω) (hωc : (k : ℝ) ^ 2 * 4 ^ k * (2 * R + 2 ^ k * C₀) ≤ ω)
    (hbh : 1.003 * q * ((k : ℝ) ^ 2 * 4 ^ k * C₀ / ω ^ 3) ≤ 1)
    (hbΓκ : 1.003 * ((k : ℝ) ^ 2 * 4 ^ k * C₀ / ω ^ 3) * (4 * (2 * p - 1)) ≤ 1)
    (hfl : (W : ℝ) ^ (-fl) ≤ ((2 * W : ℝ) ^ k)⁻¹)
    (hSq : (Fintype.card (S × (Fin k → Bool)) : ℝ) ^ ((1 : ℝ) / (2 * q)) ≤ 1.001)
    (hK4 : (1.003 * q * (2 * W : ℝ) ^ (2 * k)) ^ (4 * p) *
      (2 * Fintype.card (S × (Fin k → Bool)) : ℝ) ^ (4 * p) * M₄ ≤ K ^ (4 * p))
    (hK2 : (1.003 * q * (2 * W : ℝ) ^ (2 * k)) ^ (2 * p) *
      (Fintype.card (S × (Fin k → Bool)) : ℝ) ^ (2 * p) * M₂ ≤ K ^ (2 * p))
    (hKδ : (2 * p + K) * δb ^ (1 / (4 * (p : ℝ))) ≤ 1)
    (hMk : ((2 : ℝ) ^ (⌈4 * (1.001 * ((((k : ℝ) + 1) * R + 2) * (CS + 1) + 2) + 1)⌉₊ + 3) *
      ω ^ (k + 2)) ^ (2 * p) / J ^ (2 * p) ≤ (W : ℝ) ^ (-(D + 1)))
    (hfin : CS * J + 1 ≤ (W : ℝ) ^ ε)
    (hfail : (W : ℝ) ^ (-(D + 1)) + δv ≤ (W : ℝ) ^ (-D))
    (hK : ∀ u ∈ Set.Ioo 0 v, ∀ n : ℕ, 2 ≤ n → n ≤ k → ∀ (b : Fin n → Fin L)
      (s : Fin n → Bool) (i : Fin n),
      gammaG g * W * ∑ c : Fin L, ‖primLoop g W L E (mRoot g L E) u (Function.update b i c) s‖ ≤
        R * zetaProp g W L u ^ (n - 2))
    (hbad : ∀ u ∈ Set.Ioo 0 v, stdGauss (Fin L × Fin W × Fin W)
      {x | ¬ loopsStepGood g E W L k S ω CS fl u (Real.sqrt (u * (gammaG g / W)) • x)} ≤
        ENNReal.ofReal δb)
    (hsv : stdGauss (Fin L × Fin W × Fin W)
      {x | ¬ loopsStepSamp g E W L k S CS fl v (Real.sqrt (v * (gammaG g / W)) • x)} ≤
        ENNReal.ofReal δv)
    (hcr : ∀ u ∈ Set.Ioo 0 v, ∀ (a : Fin k → Fin L) (σ : Fin k → Bool),
      (Integrable (fun x => ‖coordGen (gammaG g / W)
          (fun r y => loopErrField g E (mRoot g L E) W L a σ r y) u
          (Real.sqrt (u * (gammaG g / W)) • x)‖ ^ (4 * p)) (stdGauss (Fin L × Fin W × Fin W)) ∧
        ∫ x, ‖coordGen (gammaG g / W)
          (fun r y => loopErrField g E (mRoot g L E) W L a σ r y) u
          (Real.sqrt (u * (gammaG g / W)) • x)‖ ^ (4 * p) ∂(stdGauss (Fin L × Fin W × Fin W)) ≤
          M₄) ∧
      (Integrable (fun x => ‖coordGamma (gammaG g / W)
          (fun y => loopErrField g E (mRoot g L E) W L a σ u y)
          (fun y => loopErrField g E (mRoot g L E) W L a σ u y)
          (Real.sqrt (u * (gammaG g / W)) • x)‖ ^ (4 * p)) (stdGauss (Fin L × Fin W × Fin W)) ∧
        ∫ x, ‖coordGamma (gammaG g / W)
          (fun y => loopErrField g E (mRoot g L E) W L a σ u y)
          (fun y => loopErrField g E (mRoot g L E) W L a σ u y)
          (Real.sqrt (u * (gammaG g / W)) • x)‖ ^ (4 * p) ∂(stdGauss (Fin L × Fin W × Fin W)) ≤
          M₄) ∧
      (Integrable (fun x => ‖coordGamma (gammaG g / W)
          (fun y => loopErrField g E (mRoot g L E) W L a σ u y)
          (fun y => loopErrField g E (mRoot g L E) W L a σ u y)
          (Real.sqrt (u * (gammaG g / W)) • x)‖ ^ (2 * p)) (stdGauss (Fin L × Fin W × Fin W)) ∧
        ∫ x, ‖coordGamma (gammaG g / W)
          (fun y => loopErrField g E (mRoot g L E) W L a σ u y)
          (fun y => loopErrField g E (mRoot g L E) W L a σ u y)
          (Real.sqrt (u * (gammaG g / W)) • x)‖ ^ (2 * p) ∂(stdGauss (Fin L × Fin W × Fin W)) ≤
          M₂)) :
    stdGauss (Fin L × Fin W × Fin W)
      {x | ∃ w : Word k L, (W : ℝ) ^ ε * zetaProp g W L v ^ k <
        ‖loopErrField g E (mRoot g L E) W L w.1 w.2 v (Real.sqrt (v * (gammaG g / W)) • x)‖} ≤
      ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  set m := mRoot g L E with hmdef
  set σ2 : ℝ := gammaG g / W with hσ2def
  have hW1 : 1 ≤ W := by omega
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hγ := loopsStep_gammaG_pos g
  have hσ2 : 0 ≤ σ2 := by positivity
  set env : ℝ := ((2 * W : ℝ) ^ k)⁻¹ with henvdef
  have henv : 0 < env := by positivity
  have hW2r : (2 : ℝ) ≤ W := by exact_mod_cast hW
  have henv1 : env ≤ 1 := by
    rw [henvdef]
    apply inv_le_one_of_one_le₀
    exact one_le_pow₀ (by linarith)
  have hω0 : 0 < ω := by linarith
  set δs : ℝ := ω ^ (k + 2) with hδsdef
  have hδs1 : 1 ≤ δs := one_le_pow₀ hω
  have hδs0 : 0 < δs := by linarith
  have : Nonempty S := hS.to_subtype
  set S' := S × (Fin k → Bool) with hS'
  set Y : S' → ℝ → Ω W L → ℂ := fun s r y => loopErrField g E m W L (s.1 : Fin k → Fin L) s.2 r y
    with hYdef
  set Xf : ℝ → Ω W L → ℝ := fun r y => lqSurr q (fun _ : S' => env) δs (fun s => Y s r y)
    with hXfdef
  have hY : ∀ s, HeatClass (Y s) (-1 / 2) (3 / 4) := fun s =>
    heatClass_loopErrField g E m W L hW1 hL hroot _ _ (by norm_num) (by norm_num)
  have hXc : HeatClass (fun r y => ((Xf r y : ℝ) : ℂ)) (-1 / 2) (3 / 4) :=
    heatClass_lqSurr hq (fun _ => henv) hδs0 Y hY
  have hX0 : ∀ r y, 0 ≤ Xf r y := fun r y => loopsStep_lqSurr_nonneg _ _ _ _
  have hXge : ∀ r y, δs ≤ Xf r y := fun r y => loopsStep_lqSurr_ge hq (fun _ => henv) hδs0 _
  have hm0 : 0 < m.im := hroot.1
  -- scale facts
  have hζ : ∀ u, 0 ≤ u → u ≤ 1 / 2 →
      1 ≤ 2 * W * zetaProp g W L u ∧ W * zetaProp g W L u ≤ 2 := fun u hu0 hu =>
    loopsStep_zeta_bounds hg hW1 hgL hu0 hu
  have hωζ' : ∀ u, 0 ≤ u → u ≤ 1 / 2 → ω * zetaProp g W L u ≤ m.im := by
    intro u hu0 hu
    obtain ⟨-, h2⟩ := hζ u hu0 hu
    have hz0 : 0 ≤ zetaProp g W L u := by
      have := (hζ u hu0 hu).1
      by_contra h
      have h : zetaProp g W L u < 0 := not_le.mp h
      nlinarith
    have : ω * (W * zetaProp g W L u) ≤ ω * 2 := mul_le_mul_of_nonneg_left h2 hω0.le
    have h3 : ω * zetaProp g W L u * W ≤ W * C₀⁻¹ := by nlinarith
    have h4 : ω * zetaProp g W L u ≤ C₀⁻¹ := by
      have := (mul_le_mul_iff_of_pos_right hWpos).1
        (by linarith : ω * zetaProp g W L u * W ≤ C₀⁻¹ * W)
      exact this
    linarith
  -- the constants of the rates
  set κl : ℝ := (((k : ℝ) + 1) * R + 2) * (CS + 1) + 2 with hκldef
  set κ : ℝ := 1.001 * κl + 1 with hκdef
  set bh : ℝ := (k : ℝ) ^ 2 * 4 ^ k * C₀ / ω ^ 3 with hbhdef
  have hκl0 : 0 ≤ κl := by positivity
  have hκ1 : 1 ≤ κ := by rw [hκdef]; linarith
  have hbh0 : 0 ≤ bh := by positivity
  have hcardS1 : (Fintype.card S' : ℝ) ^ ((1 : ℝ) / (2 * q)) ≤ 1.001 := hSq
  -- The moment comparison iterated
  have hM := lemmaM_iter σ2 hσ2 Xf (a := -1 / 2) (b := 3 / 4) (v := v) (by norm_num) hv0 hv
    (by linarith) hXc hX0 p hp (κ := κ) (bΓ := 1.003 * bh) (K := K) (δb := δb) hκ1
    (by positivity) (by linarith) hK0 hδb (fun u => {y | ¬ loopsStepGood g E W L k S ω CS fl u y})
    hbad ?_ ?_
  rotate_left
  · -- rates on the good set
    intro u hu y hy
    simp only [Set.mem_ofPred_eq, not_not] at hy
    obtain ⟨hG1, hG2, hG3, hG4⟩ := hy
    have hu0 : 0 ≤ u := hu.1.le
    have hu2 : u ≤ 1 / 2 := by linarith [hu.2]
    have huw : u ∈ Set.Ioo (-1 / 2 : ℝ) (3 / 4) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    set M := blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) y with hMdef
    have hM := loopsStep_slice_herm g hW1 y
    set Xs := Xf u y with hXsdef
    have hXs : ω ^ (k + 2) ≤ Xs := hXge u y
    have hXs1 : 1 ≤ Xs := le_trans hδs1 hXs
    have hall : ∀ (b : Fin k → Fin L) (s : Fin k → Bool),
        ‖resLoop g E m b s u M - primLoop g W L E m u b s‖ ≤
          (CS + 1) * ((2 * W : ℝ) ^ k)⁻¹ * Xs := by
      intro b s
      have h1 := hG4 s b
      have hsup : (⨆ t : S, ‖loopErrField g E m W L (t : Fin k → Fin L) s u y‖) ≤ env * Xs := by
        refine ciSup_le fun t => ?_
        have h := lqSurr_label_le hq (fun _ : S' => henv) hδs0 (fun s => Y s u y) (t, s)
        rw [div_le_iff₀ henv] at h
        calc ‖loopErrField g E m W L (t : Fin k → Fin L) s u y‖ ≤ Xs * env := h
          _ = env * Xs := by ring
      have h2 : ‖resLoop g E m b s u M - primLoop g W L E m u b s‖ ≤
          CS * (env * Xs) + env * Xs := by
        calc ‖resLoop g E m b s u M - primLoop g W L E m u b s‖ =
            ‖loopErrField g E m W L b s u y‖ := rfl
          _ ≤ CS * (⨆ t : S, ‖loopErrField g E m W L (t : Fin k → Fin L) s u y‖) +
              (W : ℝ) ^ (-fl) := h1
          _ ≤ CS * (env * Xs) + env * Xs := by
              gcongr
              exact hfl.trans (le_mul_of_one_le_right henv.le hXs1)
      calc _ ≤ CS * (env * Xs) + env * Xs := h2
        _ = (CS + 1) * ((2 * W : ℝ) ^ k)⁻¹ * Xs := by rw [henvdef]; ring
    have hgen : ∀ s : S', ‖coordGen σ2 (Y s) u y‖ / env ≤ κl * Xs / (1 - u) := by
      intro s
      have e : coordGen σ2 (Y s) u y = blockGen W L (gammaG g)
          (fun r N => resLoop g E m (s.1 : Fin k → Fin L) s.2 r N -
            primLoop g W L E m r (s.1 : Fin k → Fin L) s.2) u M := by
        rw [hMdef, blockGen_slice]
        rfl
      rw [e]
      exact loopsStep_good_gen g E m hW1 hL hk hroot hu0 hu2 hM hω (hζ u hu0 hu2).1
        (hζ u hu0 hu2).2 hR hCS hC₀ hmim (hωζ' u hu0 hu2) hωl hωc hXs hG1 hG2 (hK u hu) hG3
        hall _ _
    have hgam : ∀ s : S', (coordGamma σ2 (Y s u) (Y s u) y).re / env ^ 2 ≤
        bh * Xs ^ 2 / (1 - u) := by
      intro s
      have e : coordGamma σ2 (Y s u) (Y s u) y = blockGamma W L (gammaG g)
          (resLoop g E m (s.1 : Fin k → Fin L) s.2 u) (resLoop g E m (s.1 : Fin k → Fin L) s.2 u)
          M := by
        rw [hMdef, blockGamma_slice]
        exact loopsStep_coordGamma_sub_const σ2 _ _ y
      rw [e]
      exact loopsStep_good_gamma g E m hW1 (by omega) (by linarith) hM hω hC₀ hmim hXs hG1 _ _
    have hr := loopsStep_surr_rates σ2 hσ2 hq (fun _ : S' => henv) hδs0 Y hY huw (by linarith) y
      hcardS1 hκl0 hbh0 hgen hgam (κ := κ) (bΓ := 1.003 * bh) (by rw [hκdef]; linarith) le_rfl
    exact hr
  · -- crude moments
    intro u hu
    have huw : u ∈ Set.Ioo (-1 / 2 : ℝ) (3 / 4) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    set c : ℝ := 1.003 * q * (2 * W : ℝ) ^ (2 * k) with hcdef
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hP : (1 : ℝ) ≤ (2 * W : ℝ) ^ k := one_le_pow₀ (by linarith)
    have hPP : (2 * W : ℝ) ^ (2 * k) = ((2 * W : ℝ) ^ k) ^ 2 := by
      rw [← pow_mul, mul_comm k 2]
    have hc1 : 1.001 / env ≤ c := by
      rw [henvdef, div_inv_eq_mul, hcdef, hPP]
      have h1 : (1.001 : ℝ) ≤ 1.003 * q := by linarith
      have h2 : (2 * W : ℝ) ^ k ≤ ((2 * W : ℝ) ^ k) ^ 2 := by nlinarith
      calc (1.001 : ℝ) * (2 * W : ℝ) ^ k ≤ 1.003 * q * (2 * W : ℝ) ^ k := by gcongr
        _ ≤ 1.003 * q * ((2 * W : ℝ) ^ k) ^ 2 := by gcongr
    have hc2 : 1.003 * q / env ^ 2 ≤ c := by
      have e : env ^ 2 = ((2 * W : ℝ) ^ (2 * k))⁻¹ := by rw [henvdef, inv_pow, hPP]
      rw [e, div_inv_eq_mul, hcdef]
    have hc0 : 0 ≤ c := by positivity
    have hpt := fun x => loopsStep_surr_crude σ2 hσ2 hq henv hδs1 Y hY huw
      (Real.sqrt (u * σ2) • x) hcardS1 hc1 hc2
    have hcru := hcr u hu
    refine ⟨?_, ?_⟩
    · have h := loopsStep_sum_moment (stdGauss (Fin L × Fin W × Fin W))
        (fun x => ‖coordGen σ2 (fun r z => ((Xf r z : ℝ) : ℂ)) u (Real.sqrt (u * σ2) • x)‖)
        (fun (t : S' ⊕ S') x => Sum.elim
          (fun s => ‖coordGen σ2 (Y s) u (Real.sqrt (u * σ2) • x)‖)
          (fun s => ‖coordGamma σ2 (Y s u) (Y s u) (Real.sqrt (u * σ2) • x)‖) t)
        (fun t x => by cases t <;> exact norm_nonneg _) hc0 (fun x => norm_nonneg _)
        (fun x => by
          refine (hpt x).1.trans (le_of_eq ?_)
          congr 1
          rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
          rfl)
        (n := 4 * p) (by omega) (B := M₄)
        (fun t => by
          rcases t with s | s
          · exact (hcru (s.1 : Fin k → Fin L) s.2).1
          · exact (hcru (s.1 : Fin k → Fin L) s.2).2.1)
      refine h.trans (le_of_eq_of_le ?_ hK4)
      rw [Fintype.card_sum]
      push_cast
      ring
    · have h := loopsStep_sum_moment (stdGauss (Fin L × Fin W × Fin W))
        (fun x => ‖coordGamma σ2 (fun z => ((Xf u z : ℝ) : ℂ)) (fun z => ((Xf u z : ℝ) : ℂ))
          (Real.sqrt (u * σ2) • x)‖)
        (fun (s : S') x => ‖coordGamma σ2 (Y s u) (Y s u) (Real.sqrt (u * σ2) • x)‖)
        (fun t x => norm_nonneg _) hc0 (fun x => norm_nonneg _) (fun x => (hpt x).2)
        (n := 2 * p) (by omega) (B := M₂)
        (fun s => (hcru (s.1 : Fin k → Fin L) s.2).2.2)
      exact h.trans hK2
  -- the initial value
  have hX00 : Xf 0 0 ≤ 1.001 * δs := by
    have h := lqSurr_le hq (fun _ : S' => henv) hδs0 (fun s => Y s 0 0)
    have hz : ∀ s : S', Y s 0 0 = 0 := fun s => loopsStep_field_zero g E hW1 hL hroot _ _
    simp only [hz, norm_zero, zero_div, ciSup_const, zero_add] at h
    have e : Xf 0 0 = lqSurr q (fun _ : S' => env) δs (fun _ => 0) := by
      simp only [hXfdef]
      congr 1
      funext s
      exact hz s
    rw [e]
    calc lqSurr q (fun _ : S' => env) δs (fun _ => 0) ≤
        (Fintype.card S' : ℝ) ^ ((1 : ℝ) / (2 * q)) * δs := h
      _ ≤ 1.001 * δs := by gcongr
  set n : ℕ := ⌈4 * κ⌉₊ with hndef
  set f : (Fin L × Fin W × Fin W → ℝ) → ℝ := fun x => Xf v (Real.sqrt (v * σ2) • x) ^ (2 * p)
    with hfdef
  have hf0 : ∀ x, 0 ≤ f x := fun x => pow_nonneg (hX0 _ _) _
  have hint0 : 0 ≤ ∫ x, f x ∂(stdGauss (Fin L × Fin W × Fin W)) :=
    integral_nonneg fun x => hf0 x
  have hδb' : 0 ≤ δb ^ (1 / (4 * (p : ℝ))) := Real.rpow_nonneg hδb _
  have hN : (∫ x, f x ∂(stdGauss (Fin L × Fin W × Fin W))) ^ (1 / (2 * (p : ℝ))) ≤
      2 ^ (n + 3) * δs := by
    refine hM.trans ?_
    calc (2 : ℝ) ^ (n + 1) * (Xf 0 0 + (2 * p + K) * δb ^ (1 / (4 * (p : ℝ)))) ≤
        2 ^ (n + 1) * (1.001 * δs + 1) :=
          mul_le_mul_of_nonneg_left (add_le_add hX00 hKδ) (by positivity)
      _ ≤ 2 ^ (n + 1) * (4 * δs) := by gcongr; linarith
      _ = 2 ^ (n + 3) * δs := by ring
  have hp0 : (0 : ℝ) < 2 * p := by positivity
  have hint : ∫ x, f x ∂(stdGauss (Fin L × Fin W × Fin W)) ≤ (2 ^ (n + 3) * δs) ^ (2 * p) := by
    have e : ∫ x, f x ∂(stdGauss (Fin L × Fin W × Fin W)) =
        ((∫ x, f x ∂(stdGauss (Fin L × Fin W × Fin W))) ^ (1 / (2 * (p : ℝ)))) ^ (2 * p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hint0]
      have : 1 / (2 * (p : ℝ)) * ((2 * p : ℕ) : ℝ) = 1 := by push_cast; field_simp
      rw [this, Real.rpow_one]
    rw [e]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hint0 _) hN _
  -- integrability of the terminal surrogate
  have hvw : v ∈ Set.Ioo (-1 / 2 : ℝ) (3 / 4) := ⟨by linarith, by linarith⟩
  have hcont : Continuous (Xf v) := by
    have h := (loopsStep_heat_slice hXc hvw).1
    have := Complex.continuous_re.comp h
    simpa [Function.comp_def] using this
  obtain ⟨CX, hCX⟩ := hXc.bdd
  have hfint : Integrable f (stdGauss (Fin L × Fin W × Fin W)) := by
    refine Integrable.of_bound ?_ (CX ^ (2 * p)) (Eventually.of_forall fun x => ?_)
    · exact ((hcont.comp (continuous_const_smul _)).pow _).aestronglyMeasurable
    · have h1 := hCX v hvw (Real.sqrt (v * σ2) • x)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hX0 _ _)] at h1
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
      exact pow_le_pow_left₀ (hX0 _ _) h1 _
  have hJp : 0 < J ^ (2 * p) := by positivity
  have hmk := loopsStep_markov (stdGauss (Fin L × Fin W × Fin W)) f hf0 hfint hJp hint
  -- the final event
  have hsub : {x : Fin L × Fin W × Fin W → ℝ | ∃ w : Word k L, (W : ℝ) ^ ε *
      zetaProp g W L v ^ k < ‖loopErrField g E m W L w.1 w.2 v (Real.sqrt (v * σ2) • x)‖} ⊆
      {x | J ^ (2 * p) ≤ f x} ∪
        {x | ¬ loopsStepSamp g E W L k S CS fl v (Real.sqrt (v * σ2) • x)} := by
    rintro x ⟨w, hw⟩
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, not_le] at hcon
    obtain ⟨hlt, hsamp⟩ := hcon
    set yv := Real.sqrt (v * σ2) • x with hyv
    have hXJ : Xf v yv < J := lt_of_pow_lt_pow_left₀ (2 * p) hJ.le hlt
    have hsup : (⨆ t : S, ‖loopErrField g E m W L (t : Fin k → Fin L) w.2 v yv‖) ≤
        env * Xf v yv := by
      refine ciSup_le fun t => ?_
      have h := lqSurr_label_le hq (fun _ : S' => henv) hδs0 (fun s => Y s v yv) (t, w.2)
      rw [div_le_iff₀ henv] at h
      calc ‖loopErrField g E m W L (t : Fin k → Fin L) w.2 v yv‖ ≤ Xf v yv * env := h
        _ = env * Xf v yv := by ring
    have hζv := (hζ v hv0.le hv).1
    have henvζ : env ≤ zetaProp g W L v ^ k := by
      rw [henvdef, ← inv_pow]
      apply pow_le_pow_left₀ (by positivity)
      rw [inv_le_iff_one_le_mul₀ (by positivity)]
      linarith
    have hWε : 0 ≤ (W : ℝ) ^ ε := by positivity
    have h1 := hsamp w.2 w.1
    have : ‖loopErrField g E m W L w.1 w.2 v yv‖ ≤ (W : ℝ) ^ ε * zetaProp g W L v ^ k := by
      calc ‖loopErrField g E m W L w.1 w.2 v yv‖ ≤
          CS * (⨆ t : S, ‖loopErrField g E m W L (t : Fin k → Fin L) w.2 v yv‖) +
            (W : ℝ) ^ (-fl) := h1
        _ ≤ CS * (env * J) + env := by
            gcongr
            exact hsup.trans (mul_le_mul_of_nonneg_left hXJ.le henv.le)
        _ = env * (CS * J + 1) := by ring
        _ ≤ env * (W : ℝ) ^ ε := by gcongr
        _ ≤ zetaProp g W L v ^ k * (W : ℝ) ^ ε := by gcongr
        _ = (W : ℝ) ^ ε * zetaProp g W L v ^ k := by ring
    linarith
  calc stdGauss (Fin L × Fin W × Fin W) {x | ∃ w : Word k L, (W : ℝ) ^ ε *
        zetaProp g W L v ^ k < ‖loopErrField g E m W L w.1 w.2 v (Real.sqrt (v * σ2) • x)‖} ≤
      stdGauss (Fin L × Fin W × Fin W) {x | J ^ (2 * p) ≤ f x} +
        stdGauss (Fin L × Fin W × Fin W)
          {x | ¬ loopsStepSamp g E W L k S CS fl v (Real.sqrt (v * σ2) • x)} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal ((2 ^ (n + 3) * δs) ^ (2 * p) / J ^ (2 * p)) + ENNReal.ofReal δv :=
        add_le_add hmk hsv
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 1))) + ENNReal.ofReal δv := by
        gcongr
    _ = ENNReal.ofReal ((W : ℝ) ^ (-(D + 1)) + δv) := by
        rw [ENNReal.ofReal_add (by positivity) hδv]
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal hfail

end AtW

/-! ### From the inputs at each time to the bad sets -/

section Events

/-- `H_u = A_g ⊗ I + √(uγ_g) V` is the slice at the scaled Gaussian coordinates. -/
private theorem loopsStep_flowH_eq (g : ℝ) (W L : ℕ) {u : ℝ} (hu : 0 ≤ u) (ω : Ω W L) :
    flowH g W L u ω = blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
      (Real.sqrt (u * (gammaG g / W)) • ω) := by
  have hγ : 0 ≤ gammaG g := (loopsStep_gammaG_pos g).le
  unfold flowH
  rw [blockFlow_eq_blockSlice _ _ _ (mul_nonneg hu hγ), mul_div_assoc]

/-- The centered averaged block trace `⟨G - M⟩_{cc} = ⟨G⟩_{cc} - m` at a root. -/
private theorem loopsStep_blockTr_sub (g E : ℝ) {W L : ℕ} (hW : 1 ≤ W) (hL : 1 ≤ L) (u : ℝ)
    (hroot : IsDysonRootV (hopB g) (gammaG g) L E (mRoot g L E))
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (c : Fin L) :
    blockTr (G - flowM W ⟨g, E, L, u⟩) c c = blockTr G c c - mRoot g L E := by
  have hM := loopTr_one_dysonMat g E W L hW hL _ hroot c true
  simp only [ite_true] at hM
  have hbt : ∀ X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ,
      blockTr X c c = loopTr X ![c] ![true] := by
    intro X; rw [loopTr_one]; rfl
  have e : blockTr (G - flowM W ⟨g, E, L, u⟩) c c =
      blockTr G c c - blockTr (flowM W ⟨g, E, L, u⟩) c c := by
    unfold blockTr
    simp only [Matrix.sub_apply, Finset.sum_sub_distrib, mul_sub]
  rw [e, hbt (flowM W ⟨g, E, L, u⟩)]
  unfold flowM
  rw [hM]

/-- The generator of the loop-error field at the scaled Gaussian coordinates is the block
generator at `H_u`. -/
private theorem loopsStep_coordGen_eq (g E : ℝ) (m : ℂ) {W L k : ℕ} (a : Fin k → Fin L)
    (σ : Fin k → Bool) {u : ℝ} (hu : 0 ≤ u) (x : Ω W L) :
    coordGen (gammaG g / W) (fun r y => loopErrField g E m W L a σ r y) u
        (Real.sqrt (u * (gammaG g / W)) • x) =
      blockGen W L (gammaG g) (fun r N => resLoop g E m a σ r N - primLoop g W L E m r a σ) u
        (flowH g W L u x) := by
  rw [loopsStep_flowH_eq g W L hu, blockGen_slice]
  rfl

/-- The carré du champ of the loop-error field at the scaled Gaussian coordinates is the
bracket of the loop at `H_u`. -/
private theorem loopsStep_coordGamma_eq (g E : ℝ) (m : ℂ) {W L k : ℕ} (a : Fin k → Fin L)
    (σ : Fin k → Bool) {u : ℝ} (hu : 0 ≤ u) (x : Ω W L) :
    coordGamma (gammaG g / W) (fun y => loopErrField g E m W L a σ u y)
        (fun y => loopErrField g E m W L a σ u y) (Real.sqrt (u * (gammaG g / W)) • x) =
      blockGamma W L (gammaG g) (resLoop g E m a σ u) (resLoop g E m a σ u)
        (flowH g W L u x) := by
  rw [loopsStep_flowH_eq g W L hu, blockGamma_slice]
  exact loopsStep_coordGamma_sub_const _ _ _ _

/-- A supremum over a smaller finite set of labels is smaller. -/
private theorem loopsStep_iSup_mono {α : Type*} {S₀ S : Finset α} (h : S₀ ⊆ S) (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) : (⨆ s : S₀, f s) ≤ ⨆ s : S, f s := by
  rcases isEmpty_or_nonempty S₀ with h0 | h0
  · rw [Real.iSup_of_isEmpty]
    exact Real.iSup_nonneg fun s => hf s
  · refine ciSup_le fun s => ?_
    exact le_ciSup_of_le (Finite.bddAbove_range _) ⟨s, h s.2⟩ le_rfl

/-- The bad set at time `u` has measure at most the sum of the failure probabilities of the block
bound, the averaged bound, the shorter loop errors and the sampling. -/
private theorem loopsStep_bad_le (g E : ℝ) {W L k : ℕ} (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hroot : IsDysonRootV (hopB g) (gammaG g) L E (mRoot g L E)) (S : Finset (Fin k → Fin L))
    {ω CS fl u a1 a2 a3 a4 : ℝ} (hu : 0 ≤ u) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3)
    (ha4 : 0 ≤ a4)
    (h1 : μ W L {x | ∃ c d : Fin L, ω < ‖blockOf (flowG W ⟨g, E, L, u⟩ x) c d‖} ≤
      ENNReal.ofReal a1)
    (h2 : μ W L {x | ∃ c : Fin L, ω * zetaProp g W L u <
      ‖blockTr (flowG W ⟨g, E, L, u⟩ x - flowM W ⟨g, E, L, u⟩) c c‖} ≤ ENNReal.ofReal a2)
    (h3 : ∀ n : ℕ, 2 ≤ n → n < k → μ W L {x | ∃ w : Word n L, ω * zetaProp g W L u ^ n <
      ‖flowErr W ⟨g, E, L, u⟩ w.1 w.2 x‖} ≤ ENNReal.ofReal a3)
    (h4 : stdGauss (Fin L × Fin W × Fin W)
      {x | ¬ loopsStepSamp g E W L k S CS fl u (Real.sqrt (u * (gammaG g / W)) • x)} ≤
        ENNReal.ofReal a4) :
    stdGauss (Fin L × Fin W × Fin W)
      {x | ¬ loopsStepGood g E W L k S ω CS fl u (Real.sqrt (u * (gammaG g / W)) • x)} ≤
      ENNReal.ofReal (a1 + a2 + k * a3 + a4) := by
  set A1 := {x : Ω W L | ∃ c d : Fin L, ω < ‖blockOf (flowG W ⟨g, E, L, u⟩ x) c d‖}
  set A2 := {x : Ω W L | ∃ c : Fin L, ω * zetaProp g W L u <
      ‖blockTr (flowG W ⟨g, E, L, u⟩ x - flowM W ⟨g, E, L, u⟩) c c‖}
  set A3 : Fin k → Set (Ω W L) := fun n => if 2 ≤ n.val then {x | ∃ w : Word n L,
      ω * zetaProp g W L u ^ (n : ℕ) < ‖flowErr W ⟨g, E, L, u⟩ w.1 w.2 x‖} else ∅
  set A4 := {x : Ω W L |
      ¬ loopsStepSamp g E W L k S CS fl u (Real.sqrt (u * (gammaG g / W)) • x)}
  have hsub : {x : Ω W L |
      ¬ loopsStepGood g E W L k S ω CS fl u (Real.sqrt (u * (gammaG g / W)) • x)} ⊆
      A1 ∪ A2 ∪ (⋃ n, A3 n) ∪ A4 := by
    intro x hx
    simp only [Set.mem_ofPred_eq, loopsStepGood, not_and_or, not_forall, not_le] at hx
    have hG : resolventMat (blockSlice W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
        (Real.sqrt (u * (gammaG g / W)) • x)) (zChar g E (mRoot g L E) u) =
        flowG W ⟨g, E, L, u⟩ x := by
      unfold flowG
      rw [loopsStep_flowH_eq g W L hu]
    rcases hx with hx | hx | hx | hx
    · obtain ⟨c, d, h⟩ := hx
      rw [hG] at h
      exact Or.inl (Or.inl (Or.inl ⟨c, d, h⟩))
    · obtain ⟨c, h⟩ := hx
      rw [hG, ← loopsStep_blockTr_sub g E hW hL u hroot] at h
      exact Or.inl (Or.inl (Or.inr ⟨c, h⟩))
    · obtain ⟨n, hn2, hnk, b, s, h⟩ := hx
      refine Or.inl (Or.inr (Set.mem_iUnion.2 ⟨⟨n, hnk⟩, ?_⟩))
      simp only [A3, hn2, ↓reduceIte]
      refine ⟨(b, s), ?_⟩
      rw [flowErr_eq_loopErrField W ⟨g, E, L, u⟩ hu]
      exact h
    · exact Or.inr hx
  have h3' : stdGauss (Fin L × Fin W × Fin W) (⋃ n, A3 n) ≤ ENNReal.ofReal (k * a3) := by
    refine (measure_iUnion_fintype_le _ _).trans ?_
    calc ∑ n : Fin k, stdGauss (Fin L × Fin W × Fin W) (A3 n) ≤
        ∑ _n : Fin k, ENNReal.ofReal a3 := by
          refine Finset.sum_le_sum fun n _ => ?_
          simp only [A3]
          split_ifs with hn
          · exact h3 n hn n.2
          · simp
      _ = ENNReal.ofReal (k * a3) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  calc stdGauss (Fin L × Fin W × Fin W) {x : Ω W L |
        ¬ loopsStepGood g E W L k S ω CS fl u (Real.sqrt (u * (gammaG g / W)) • x)} ≤
      stdGauss (Fin L × Fin W × Fin W) (A1 ∪ A2 ∪ (⋃ n, A3 n) ∪ A4) := measure_mono hsub
    _ ≤ stdGauss (Fin L × Fin W × Fin W) A1 + stdGauss (Fin L × Fin W × Fin W) A2 +
        stdGauss (Fin L × Fin W × Fin W) (⋃ n, A3 n) + stdGauss (Fin L × Fin W × Fin W) A4 :=
        (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
          (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
    _ ≤ ENNReal.ofReal a1 + ENNReal.ofReal a2 + ENNReal.ofReal (k * a3) + ENNReal.ofReal a4 :=
        add_le_add (add_le_add (add_le_add h1 h2) h3') h4
    _ = ENNReal.ofReal (a1 + a2 + k * a3 + a4) := by
        rw [ENNReal.ofReal_add (by positivity) ha4, ENNReal.ofReal_add (by positivity)
          (by positivity), ENNReal.ofReal_add ha1 ha2]

/-- The sampling property fails with probability at most `2^k η` if every sign word satisfies
the sampling bound with a smaller sample set. -/
private theorem loopsStep_samp_le (g E : ℝ) {W L k : ℕ} (S₀ S : Finset (Fin k → Fin L))
    (hS : S₀ ⊆ S) {CS fl u η : ℝ} (hCS : 0 ≤ CS) (hu : 0 ≤ u)
    (hsb : ∀ σ : Fin k → Bool, SampleBound (μ W L) (fun a ω => flowErr W ⟨g, E, L, u⟩ a σ ω)
      (fun _ => 1) S₀ CS ((W : ℝ) ^ (-fl)) η) :
    stdGauss (Fin L × Fin W × Fin W)
      {x | ¬ loopsStepSamp g E W L k S CS fl u (Real.sqrt (u * (gammaG g / W)) • x)} ≤
      ENNReal.ofReal (2 ^ k * η) := by
  have hsub : {x : Ω W L |
      ¬ loopsStepSamp g E W L k S CS fl u (Real.sqrt (u * (gammaG g / W)) • x)} ⊆
      ⋃ σ : Fin k → Bool, {ω | ∃ l, CS * (⨆ s : S₀, ‖flowErr W ⟨g, E, L, u⟩ (s : Fin k → Fin L)
        σ ω‖ / 1) + (W : ℝ) ^ (-fl) < ‖flowErr W ⟨g, E, L, u⟩ l σ ω‖ / 1} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, loopsStepSamp, not_forall, not_le] at hx
    obtain ⟨σ, l, h⟩ := hx
    refine Set.mem_iUnion.2 ⟨σ, l, ?_⟩
    simp only [div_one]
    have e : ∀ a : Fin k → Fin L, flowErr W ⟨g, E, L, u⟩ a σ x =
        loopErrField g E (mRoot g L E) W L a σ u (Real.sqrt (u * (gammaG g / W)) • x) :=
      fun a => flowErr_eq_loopErrField W ⟨g, E, L, u⟩ hu a σ x
    simp only [e]
    refine lt_of_le_of_lt ?_ h
    gcongr
    exact loopsStep_iSup_mono hS (fun a => ‖loopErrField g E (mRoot g L E) W L a σ u
      (Real.sqrt (u * (gammaG g / W)) • x)‖) fun _ => norm_nonneg _
  calc stdGauss (Fin L × Fin W × Fin W) {x : Ω W L |
        ¬ loopsStepSamp g E W L k S CS fl u (Real.sqrt (u * (gammaG g / W)) • x)} ≤
      ∑ σ : Fin k → Bool, μ W L {ω | ∃ l, CS * (⨆ s : S₀,
        ‖flowErr W ⟨g, E, L, u⟩ (s : Fin k → Fin L) σ ω‖ / 1) + (W : ℝ) ^ (-fl) <
          ‖flowErr W ⟨g, E, L, u⟩ l σ ω‖ / 1} :=
        (measure_mono hsub).trans (measure_iUnion_fintype_le _ _)
    _ ≤ ∑ _σ : Fin k → Bool, ENNReal.ofReal η := Finset.sum_le_sum fun σ _ => hsb σ
    _ = ENNReal.ofReal (2 ^ k * η) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity)]
        norm_num

/-- With all labels as the sample set and `C_S ≥ 1`, the sampling property always holds. -/
private theorem loopsStep_samp_univ (g E : ℝ) {W L k : ℕ} {CS fl u : ℝ} (hCS : 1 ≤ CS)
    (y : Ω W L) : loopsStepSamp g E W L k Finset.univ CS fl u y := by
  intro σ l
  have h1 : ‖loopErrField g E (mRoot g L E) W L l σ u y‖ ≤
      ⨆ s : (Finset.univ : Finset (Fin k → Fin L)),
        ‖loopErrField g E (mRoot g L E) W L (s : Fin k → Fin L) σ u y‖ :=
    le_ciSup_of_le (Finite.bddAbove_range _) ⟨l, Finset.mem_univ l⟩ le_rfl
  have h0 : 0 ≤ ⨆ s : (Finset.univ : Finset (Fin k → Fin L)),
      ‖loopErrField g E (mRoot g L E) W L (s : Fin k → Fin L) σ u y‖ :=
    Real.iSup_nonneg fun _ => norm_nonneg _
  have hW : 0 ≤ (W : ℝ) ^ (-fl) := Real.rpow_nonneg (Nat.cast_nonneg W) _
  nlinarith

end Events

/-! ### The sample set and the thresholds in `W` -/

section Thresholds

/-- The sample set of the step: the cells of Lemma 5.8 [uvc:thm:ordinary-sampling] and one more
word if `g² ≥ W^B`, all words otherwise. -/
private def loopsStepSet (g E B : ℝ) (W L k : ℕ) (w₀ : Fin k → Fin L) : Finset (Fin k → Fin L) :=
  if (W : ℝ) ^ B ≤ g ^ 2 then insert w₀ (loopSampleSet (cellLen g W B) E L k) else Finset.univ

/-- The sample set is nonempty. -/
private theorem loopsStepSet_nonempty (g E B : ℝ) (W L k : ℕ) (w₀ : Fin k → Fin L) :
    (loopsStepSet g E B W L k w₀).Nonempty := by
  unfold loopsStepSet
  split_ifs
  · exact Finset.insert_nonempty _ _
  · exact ⟨w₀, Finset.mem_univ _⟩

/-- `|S| ≤ (6(2C_V + 1))^k (W^{B+2})^k + 1` for `L ≤ C_V g² W²`. -/
private theorem loopsStepSet_card {g CV B E : ℝ} {W L k : ℕ} (hW : 1 ≤ W) (hB : 0 < B)
    (hCV : 0 < CV) (hLV : (L : ℝ) ≤ CV * g ^ 2 * (W : ℝ) ^ 2) (w₀ : Fin k → Fin L) :
    ((loopsStepSet g E B W L k w₀).card : ℝ) ≤
      (6 * (2 * CV + 1)) ^ k * ((W : ℝ) ^ (B + 2)) ^ k + 1 := by
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hWB : (W : ℝ) ^ (B + 2) = (W : ℝ) ^ B * (W : ℝ) ^ 2 := by
    rw [Real.rpow_add hWpos, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hWB1 : 1 ≤ (W : ℝ) ^ (B + 2) := Real.one_le_rpow hW1 (by linarith)
  have hWBpos : 0 < (W : ℝ) ^ B := Real.rpow_pos_of_pos hWpos _
  unfold loopsStepSet
  split_ifs with h
  · obtain ⟨hn1, -⟩ := cellLen_bounds g B W hW h
    have hn0 : 1 ≤ cellLen g W B := by unfold cellLen; exact le_max_left _ _
    have hcard := card_loopSampleSet_le (cellLen g W B) hn0 E L k
    have hg2 : 0 < g ^ 2 := lt_of_lt_of_le hWBpos h
    have hx : 0 < g ^ 2 * (W : ℝ) ^ (-B) := by positivity
    have hLn : (L : ℝ) / cellLen g W B ≤ 2 * CV * (W : ℝ) ^ (B + 2) := by
      have hnpos : (0 : ℝ) < cellLen g W B := by exact_mod_cast hn0
      rw [div_le_iff₀ hnpos]
      have e : g ^ 2 * (W : ℝ) ^ (-B) * (W : ℝ) ^ B = g ^ 2 := by
        rw [mul_assoc, ← Real.rpow_add hWpos, neg_add_cancel, Real.rpow_zero, mul_one]
      calc (L : ℝ) ≤ CV * g ^ 2 * (W : ℝ) ^ 2 := hLV
        _ = 2 * CV * (W : ℝ) ^ (B + 2) * (g ^ 2 * (W : ℝ) ^ (-B) / 2) := by
            rw [hWB]
            have : g ^ 2 = g ^ 2 * (W : ℝ) ^ (-B) * (W : ℝ) ^ B := e.symm
            nth_rewrite 1 [this]
            ring
        _ ≤ 2 * CV * (W : ℝ) ^ (B + 2) * cellLen g W B := by gcongr
    have h1 : (L : ℝ) / cellLen g W B + 1 ≤ (2 * CV + 1) * (W : ℝ) ^ (B + 2) := by nlinarith
    have hL0 : (0 : ℝ) ≤ (L : ℝ) / cellLen g W B + 1 := by positivity
    calc ((insert w₀ (loopSampleSet (cellLen g W B) E L k)).card : ℝ) ≤
        (loopSampleSet (cellLen g W B) E L k).card + 1 := by
          exact_mod_cast Finset.card_insert_le _ _
      _ ≤ 6 ^ k * ((L : ℝ) / cellLen g W B + 1) ^ k + 1 := by gcongr
      _ ≤ 6 ^ k * ((2 * CV + 1) * (W : ℝ) ^ (B + 2)) ^ k + 1 := by gcongr
      _ = (6 * (2 * CV + 1)) ^ k * ((W : ℝ) ^ (B + 2)) ^ k + 1 := by
          rw [mul_pow, mul_pow]; ring
  · have h' : g ^ 2 < (W : ℝ) ^ B := not_le.mp h
    have hL : (L : ℝ) ≤ 6 * (2 * CV + 1) * (W : ℝ) ^ (B + 2) := by
      calc (L : ℝ) ≤ CV * g ^ 2 * (W : ℝ) ^ 2 := hLV
        _ ≤ CV * (W : ℝ) ^ B * (W : ℝ) ^ 2 := by gcongr
        _ = CV * (W : ℝ) ^ (B + 2) := by rw [hWB]; ring
        _ ≤ 6 * (2 * CV + 1) * (W : ℝ) ^ (B + 2) := by
            have : 0 ≤ (W : ℝ) ^ (B + 2) := by positivity
            nlinarith
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    calc (L : ℝ) ^ k ≤ (6 * (2 * CV + 1) * (W : ℝ) ^ (B + 2)) ^ k := by gcongr
      _ = (6 * (2 * CV + 1)) ^ k * ((W : ℝ) ^ (B + 2)) ^ k := by rw [mul_pow]
      _ ≤ _ := by linarith

/-- The sampling property for the sample set of the step fails with probability at most `2^k η`,
given the sampling of Lemma 5.8 [uvc:thm:ordinary-sampling] for `g² ≥ W^B`. -/
private theorem loopsStepSet_samp (g E B : ℝ) {W L k : ℕ} {CS fl η u : ℝ} (hCS : 1 ≤ CS)
    (w₀ : Fin k → Fin L) (hu : 0 ≤ u)
    (hsb : (W : ℝ) ^ B ≤ g ^ 2 → ∀ σ : Fin k → Bool, SampleBound (μ W L)
      (fun a ω => flowErr W ⟨g, E, L, u⟩ a σ ω) (fun _ => 1)
      (loopSampleSet (cellLen g W B) E L k) CS ((W : ℝ) ^ (-fl)) η) :
    stdGauss (Fin L × Fin W × Fin W) {x | ¬ loopsStepSamp g E W L k
      (loopsStepSet g E B W L k w₀) CS fl u (Real.sqrt (u * (gammaG g / W)) • x)} ≤
      ENNReal.ofReal (2 ^ k * η) := by
  by_cases h : (W : ℝ) ^ B ≤ g ^ 2
  · have e : loopsStepSet g E B W L k w₀ = insert w₀ (loopSampleSet (cellLen g W B) E L k) := by
      unfold loopsStepSet; rw [ite_eq_left h]
    rw [e]
    exact loopsStep_samp_le g E _ _ (Finset.subset_insert _ _) (by linarith) hu (hsb h)
  · have e : loopsStepSet g E B W L k w₀ = Finset.univ := by
      unfold loopsStepSet; rw [ite_eq_right h]
    rw [e]
    have : {x : Ω W L | ¬ loopsStepSamp g E W L k Finset.univ CS fl u
        (Real.sqrt (u * (gammaG g / W)) • x)} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact loopsStep_samp_univ g E hCS _
    rw [this, measure_empty]
    exact bot_le

/-- `c log W + d ≤ W^a` for all large `W`. -/
private theorem loopsStep_ev_log (c d : ℝ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ W : ℕ in atTop, c * Real.log W + d ≤ (W : ℝ) ^ a := by
  filter_upwards [((tendsto_rpow_atTop (half_pos ha)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (max 1 (max (4 * |c| / a) (2 * |d|))), eventually_ge_atTop 1] with W hT hW1
  simp only [Function.comp] at hT
  set T := (W : ℝ) ^ (a / 2) with hTdef
  have hT1 : 1 ≤ T := le_trans (le_max_left _ _) hT
  have hTc : 4 * |c| / a ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hTd : 2 * |d| ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hlog0 : 0 ≤ Real.log W := Real.log_nonneg (by exact_mod_cast hW1)
  have h1 : Real.log W ≤ T / (a / 2) := Real.log_le_rpow_div hW0.le (half_pos ha)
  have hTT : (W : ℝ) ^ a = T * T := by
    rw [hTdef, ← Real.rpow_add hW0]; ring_nf
  have hc : c * Real.log W ≤ T * T / 2 := by
    calc c * Real.log W ≤ |c| * Real.log W := mul_le_mul_of_nonneg_right (le_abs_self c) hlog0
      _ ≤ |c| * (T / (a / 2)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
      _ = (4 * |c| / a) * T / 2 := by field_simp; ring
      _ ≤ T * T / 2 := by gcongr
  have hd : d ≤ T * T / 2 := by
    have : d ≤ |d| := le_abs_self d
    nlinarith
  rw [hTT]; linarith

/-- `ζ_u ≥ 0` for `g ≥ 0` and `u ≤ 1`. -/
private theorem loopsStep_zeta_nonneg {g : ℝ} (hg : 0 ≤ g) (W L : ℕ) {u : ℝ} (hu : u ≤ 1) :
    0 ≤ zetaProp g W L u := by
  unfold zetaProp ellProp
  have h1 : 0 ≤ min (L : ℝ) (1 + g / Real.sqrt (gammaG g * (1 - u))) :=
    le_min (Nat.cast_nonneg L) (by positivity)
  have hγ := loopsStep_gammaG_pos g
  have : 0 ≤ 1 - u := by linarith
  positivity

end Thresholds

/-! ### Parameter inequalities -/

section Numerics

/-- `(2p + K) δ_b^{1/(4p)} ≤ 1` for `K ≤ c_K W^{e_K}`, `δ_b = c_δ W^{-D_b}`,
`D_b = 4p e_K + D + 2` and `c_δ (2p + c_K)^{4p} ≤ W`. -/
private theorem loopsStep_num_Kδ {W : ℝ} (hW : 1 ≤ W) {p : ℕ} (hp : 1 ≤ p)
    {K cK eK cδ D Db : ℝ} (hK : 0 ≤ K) (heK : 0 ≤ eK) (hcδ : 0 ≤ cδ)
    (hD : 0 < D) (hDb : Db = 4 * p * eK + D + 2) (hKle : K ≤ cK * W ^ eK)
    (hWK : cδ * (2 * p + cK) ^ (4 * p) ≤ W) :
    (2 * p + K) * (cδ * W ^ (-Db)) ^ (1 / (4 * (p : ℝ))) ≤ 1 := by
  have hWpos : 0 < W := by linarith
  set T := 2 * (p : ℝ) + K with hTdef
  have hT0 : 0 < T := by positivity
  have hWeK1 : 1 ≤ W ^ eK := Real.one_le_rpow hW heK
  have hTle : T ≤ (2 * p + cK) * W ^ eK := by
    have : 2 * (p : ℝ) ≤ 2 * p * W ^ eK := le_mul_of_one_le_right (by positivity) hWeK1
    rw [hTdef]; nlinarith
  have hδb : 0 ≤ cδ * W ^ (-Db) := by positivity
  have hδT : cδ * W ^ (-Db) * T ^ (4 * p) ≤ 1 := by
    have e2 : (W ^ eK) ^ (4 * p) = W ^ (4 * p * eK) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hWpos.le]; push_cast; ring_nf
    have e3 : W ^ (-Db) * W ^ (4 * p * eK) = W ^ (-(D + 2)) := by
      rw [← Real.rpow_add hWpos, hDb]; ring_nf
    have hD2 : W ^ (-(D + 2)) * W ≤ 1 := by
      rw [← Real.rpow_add_one hWpos.ne']
      exact Real.rpow_le_one_of_one_le_of_nonpos hW (by linarith)
    calc cδ * W ^ (-Db) * T ^ (4 * p) ≤ cδ * W ^ (-Db) * ((2 * p + cK) * W ^ eK) ^ (4 * p) := by
          gcongr
      _ = (cδ * (2 * p + cK) ^ (4 * p)) * (W ^ (-Db) * W ^ (4 * p * eK)) := by
          rw [mul_pow, e2]; ring
      _ ≤ W * W ^ (-(D + 2)) := by
          rw [e3]; exact mul_le_mul_of_nonneg_right hWK (by positivity)
      _ ≤ 1 := by linarith
  have hδle : cδ * W ^ (-Db) ≤ (T⁻¹) ^ (4 * p) := by
    have hT4 : 0 < T ^ (4 * p) := by positivity
    rw [inv_pow]
    calc cδ * W ^ (-Db) = cδ * W ^ (-Db) * T ^ (4 * p) / T ^ (4 * p) := by field_simp
      _ ≤ 1 / T ^ (4 * p) := by gcongr
      _ = (T ^ (4 * p))⁻¹ := one_div _
  have hroot4 : (cδ * W ^ (-Db)) ^ (1 / (4 * (p : ℝ))) ≤ T⁻¹ := by
    calc (cδ * W ^ (-Db)) ^ (1 / (4 * (p : ℝ))) ≤ ((T⁻¹) ^ (4 * p)) ^ (1 / (4 * (p : ℝ))) :=
          Real.rpow_le_rpow hδb hδle (by positivity)
      _ = T⁻¹ := by
          rw [show (1 / (4 * (p : ℝ))) = (((4 * p : ℕ) : ℝ))⁻¹ by push_cast; ring]
          exact Real.pow_rpow_inv_natCast (by positivity) (by omega)
  calc T * (cδ * W ^ (-Db)) ^ (1 / (4 * (p : ℝ))) ≤ T * T⁻¹ :=
        mul_le_mul_of_nonneg_left hroot4 hT0.le
    _ = 1 := mul_inv_cancel₀ hT0.ne'

/-- The crude constant: `c (2|S'|) M_x ≤ c_K W^{e_K}` for `c = 1.003 q (2W)^{2k}`, `q ≤ W`,
`|S'| ≤ W^{C_S'}` and `M_x ≤ C_m W^{4p|C_1|}`. -/
private theorem loopsStep_num_K {W : ℝ} (hW : 1 ≤ W) {k p : ℕ} {q cardS Mx Cm CSp C₁ : ℝ}
    (hq : 0 ≤ q) (hqW : q ≤ W) (hcard0 : 0 ≤ cardS) (hcard : cardS ≤ W ^ CSp) (hMx0 : 0 ≤ Mx)
    (hMx : Mx ≤ Cm * W ^ (4 * p * |C₁|)) :
    1.003 * q * (2 * W) ^ (2 * k) * (2 * cardS) * Mx ≤
      2.006 * 4 ^ k * Cm * W ^ (1 + 2 * k + CSp + 4 * p * |C₁|) := by
  have hWpos : 0 < W := by linarith
  have hcc : 1.003 * q * (2 * W) ^ (2 * k) ≤ 1.003 * W * 4 ^ k * W ^ (2 * k) := by
    rw [mul_pow, show (2 : ℝ) ^ (2 * k) = 4 ^ k by rw [pow_mul]; norm_num]
    have : 0 ≤ (4 : ℝ) ^ k * W ^ (2 * k) := by positivity
    nlinarith
  have he : W ^ (1 + 2 * k + CSp + 4 * p * |C₁|) = W * W ^ (2 * k) * W ^ CSp *
      W ^ (4 * p * |C₁|) := by
    rw [Real.rpow_add hWpos, Real.rpow_add hWpos, Real.rpow_add hWpos, Real.rpow_one,
      show (2 * (k : ℝ)) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [he]
  have h1 : 0 ≤ 1.003 * q * (2 * W) ^ (2 * k) := by positivity
  calc 1.003 * q * (2 * W) ^ (2 * k) * (2 * cardS) * Mx ≤ (1.003 * W * 4 ^ k * W ^ (2 * k)) *
      (2 * W ^ CSp) * (Cm * W ^ (4 * p * |C₁|)) := by gcongr
    _ = 2.006 * 4 ^ k * Cm * (W * W ^ (2 * k) * W ^ CSp * W ^ (4 * p * |C₁|)) := by ring

/-- `M_x = max(1, C_4 W^{4pC_1}, C_2 W^{2pC_1}) ≤ C_m W^{4p|C_1|}` with `C_m = max(1, C_4, C_2)`. -/
private theorem loopsStep_num_Mx {W : ℝ} (hW : 1 ≤ W) (p : ℕ) (C₁ Cp4 Cp2 : ℝ) :
    max 1 (max (Cp4 * W ^ (C₁ * ((4 * p : ℕ) : ℝ))) (Cp2 * W ^ (C₁ * ((2 * p : ℕ) : ℝ)))) ≤
      max 1 (max Cp4 Cp2) * W ^ (4 * p * |C₁|) := by
  set Cm := max 1 (max Cp4 Cp2) with hCm
  have hCm1 : 1 ≤ Cm := le_max_left _ _
  have hb1 : 1 ≤ W ^ (4 * p * |C₁|) := Real.one_le_rpow hW (by positivity)
  have hle : ∀ (Cp a : ℝ), Cp ≤ Cm → a ≤ 4 * p * |C₁| → Cp * W ^ a ≤ Cm * W ^ (4 * p * |C₁|) := by
    intro Cp a hCp ha
    have hWa : 0 < W ^ a := Real.rpow_pos_of_pos (by linarith) a
    calc Cp * W ^ a ≤ Cm * W ^ a := mul_le_mul_of_nonneg_right hCp hWa.le
      _ ≤ Cm * W ^ (4 * p * |C₁|) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hW ha) (by linarith)
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hC : C₁ ≤ |C₁| := le_abs_self C₁
  have ha : 0 ≤ |C₁| := abs_nonneg C₁
  refine max_le (by nlinarith) (max_le ?_ ?_)
  · refine hle Cp4 _ ((le_max_left _ _).trans (le_max_right _ _)) ?_
    push_cast
    nlinarith
  · refine hle Cp2 _ ((le_max_right _ _).trans (le_max_right _ _)) ?_
    push_cast
    nlinarith

/-- Markov's bound at the final time: `(2^{n+3} ω^{k+2})^{2p}/J^{2p} ≤ W^{-(D+1)}` for
`ω = W^{ε/(4(k+2))}`, `J = W^{ε/2}`, `2^{n+3} ≤ W^{ε/8}` and `p ≥ 4(D+1)/ε`. -/
private theorem loopsStep_num_Mk {W : ℝ} (hW : 1 ≤ W) {k n p : ℕ} {ε D : ℝ} (hε : 0 < ε)
    (hp : 4 * (D + 1) / ε ≤ p) (hn : (2 : ℝ) ^ (n + 3) ≤ W ^ (ε / 8)) :
    ((2 : ℝ) ^ (n + 3) * (W ^ (ε / (4 * (k + 2)))) ^ (k + 2)) ^ (2 * p) / (W ^ (ε / 2)) ^ (2 * p) ≤
      W ^ (-(D + 1)) := by
  have hWpos : 0 < W := by linarith
  have hω : (W ^ (ε / (4 * (k + 2)))) ^ (k + 2) = W ^ (ε / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hWpos.le]
    congr 1
    push_cast
    field_simp
  rw [hω, ← div_pow]
  have h1 : (2 : ℝ) ^ (n + 3) * W ^ (ε / 4) / W ^ (ε / 2) ≤ W ^ (-(ε / 8)) := by
    rw [div_le_iff₀ (by positivity)]
    calc (2 : ℝ) ^ (n + 3) * W ^ (ε / 4) ≤ W ^ (ε / 8) * W ^ (ε / 4) := by gcongr
      _ = W ^ (-(ε / 8)) * W ^ (ε / 2) := by
          rw [← Real.rpow_add hWpos, ← Real.rpow_add hWpos]; ring_nf
  have h0 : 0 ≤ (2 : ℝ) ^ (n + 3) * W ^ (ε / 4) / W ^ (ε / 2) := by positivity
  calc ((2 : ℝ) ^ (n + 3) * W ^ (ε / 4) / W ^ (ε / 2)) ^ (2 * p) ≤ (W ^ (-(ε / 8))) ^ (2 * p) :=
        pow_le_pow_left₀ h0 h1 _
    _ = W ^ (-(ε / 8) * (2 * p)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hWpos.le]; push_cast; ring_nf
    _ ≤ W ^ (-(D + 1)) := by
        apply Real.rpow_le_rpow_of_exponent_le hW
        have : 4 * (D + 1) ≤ p * ε := by rwa [div_le_iff₀ hε] at hp
        nlinarith

/-- `C_S J + 1 ≤ W^ε` for `J = W^{ε/2} ≥ C_S + 1`. -/
private theorem loopsStep_num_fin {W : ℝ} (hW : 1 ≤ W) {CS ε : ℝ} (hCS : 0 ≤ CS)
    (h : CS + 1 ≤ W ^ (ε / 2)) : CS * W ^ (ε / 2) + 1 ≤ W ^ ε := by
  have hWpos : 0 < W := by linarith
  have e : W ^ ε = W ^ (ε / 2) * W ^ (ε / 2) := by rw [← Real.rpow_add hWpos]; ring_nf
  rw [e]
  have hJ1 : 1 ≤ W ^ (ε / 2) := by linarith
  nlinarith

/-- `W^{-(D+1)} + 2^k W^{-D_b} ≤ W^{-D}` for `W ≥ 2`, `W ≥ 2^k` and `D_b ≥ D + 2`. -/
private theorem loopsStep_num_fail {W : ℝ} (hW : 2 ≤ W) {k : ℕ} {D Db : ℝ} (hk : (2 : ℝ) ^ k ≤ W)
    (hDb : D + 2 ≤ Db) : W ^ (-(D + 1)) + 2 ^ k * W ^ (-Db) ≤ W ^ (-D) := by
  have hWpos : 0 < W := by linarith
  have h1 : 2 ^ k * W ^ (-Db) ≤ W ^ (-(D + 1)) := by
    calc (2 : ℝ) ^ k * W ^ (-Db) ≤ W * W ^ (-Db) := by gcongr
      _ = W ^ (1 - Db) := by
          rw [show (1 : ℝ) - Db = 1 + (-Db) by ring, Real.rpow_add hWpos, Real.rpow_one]
      _ ≤ W ^ (-(D + 1)) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : 2 * W ^ (-(D + 1)) ≤ W ^ (-D) := by
    have e : W ^ (-D) = W * W ^ (-(D + 1)) := by
      rw [show -D = 1 + (-(D + 1)) by ring, Real.rpow_add hWpos, Real.rpow_one]
    rw [e]
    exact mul_le_mul_of_nonneg_right hW (by positivity)
  linarith

end Numerics

/-! ### One step at a point of the range -/

section Point

set_option maxHeartbeats 1000000 in
-- The proof is long: the parameter inequalities and the inputs at every time.
/-- One step of the induction at a point `(g, E, L, v)` of the range with `v > 0`, for `W` beyond
the thresholds: the inputs at the times `u ∈ (0, v]` (block bound, averaged bound, shorter loop
errors, sampling, crude moments, rows) give `ℙ(max_{a,σ} |D_k(v)| > W^ε ζ_v^k) ≤ W^{-D}`. -/
private theorem loopsStep_point (κ Cκ CV : ℝ) (ρ : ℕ → ℝ) {k W : ℕ} (hk : 2 ≤ k)
    (hCV : 0 < CV) {g E : ℝ} {L : ℕ} {v : ℝ}
    (hpt : (⟨g, E, L, v⟩ : FlowPt) ∈ initLarge κ Cκ CV ρ W) (hvpos : 0 < v)
    {C₀ C' B C₁ Cp4 Cp2 ε D ν R CS CSp eK cK Db cb cq : ℝ} {p n : ℕ}
    (hC₀ : 0 < C₀) (hC' : 0 < C') (hB : 2 < B) (hε : 0 < ε) (hD : 0 < D) (hν : 0 < ν)
    (hνdef : ν = ε / (4 * (k + 2))) (hp1 : 1 ≤ p) (hpD : 4 * (D + 1) / ε ≤ p)
    (hRdef : R = C' * 2 ^ k) (hCSdef : CS = 2 * 6 ^ k)
    (hndef : n = ⌈4 * (1.001 * ((((k : ℝ) + 1) * R + 2) * (CS + 1) + 2) + 1)⌉₊)
    (hCSpdef : CSp = k * (B + 2) + 1) (heKdef : eK = 1 + 2 * k + CSp + 4 * p * |C₁|)
    (hcKdef : cK = 2.006 * 4 ^ k * max 1 (max Cp4 Cp2)) (hDbdef : Db = 4 * p * eK + D + 2)
    (hcbdef : cb = 1.003 * (k : ℝ) ^ 2 * 4 ^ k * C₀) (hcqdef : cq = CSp / (2 * Real.log 1.001))
    (hg1 : 1 ≤ g) (hgL : g ^ 2 ≤ L) (hL3 : 3 ≤ L)
    (hroot : IsDysonRootV (hopB g) (gammaG g) L E (mRoot g L E))
    (hmim : C₀⁻¹ ≤ (mRoot g L E).im)
    (hrows : ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 → ∀ n' : ℕ, 2 ≤ n' → n' ≤ k → ∀ (i : Fin n')
      (a : Fin n' → Fin L) (σ : Fin n' → Bool),
      ∑ b : Fin L, ‖primLoopF g L E (mRoot g L E) t (Function.update a i b) σ‖ ≤ C' * g ^ 2)
    (h1 : ∀ u ∈ Set.Ioo 0 v, μ W L {x | ∃ c d : Fin L,
      (W : ℝ) ^ ν < ‖blockOf (flowG W ⟨g, E, L, u⟩ x) c d‖} ≤ ENNReal.ofReal ((W : ℝ) ^ (-Db)))
    (h2 : ∀ u ∈ Set.Ioo 0 v, μ W L {x | ∃ c : Fin L, (W : ℝ) ^ ν * zetaProp g W L u <
      ‖blockTr (flowG W ⟨g, E, L, u⟩ x - flowM W ⟨g, E, L, u⟩) c c‖} ≤
        ENNReal.ofReal ((W : ℝ) ^ (-Db)))
    (h3 : ∀ u ∈ Set.Ioo 0 v, ∀ n' : ℕ, 2 ≤ n' → n' < k → μ W L {x | ∃ w : Word n' L,
      (W : ℝ) ^ ν * zetaProp g W L u ^ n' < ‖flowErr W ⟨g, E, L, u⟩ w.1 w.2 x‖} ≤
        ENNReal.ofReal ((W : ℝ) ^ (-Db)))
    (hsb : (W : ℝ) ^ B ≤ g ^ 2 → ∀ (σ : Fin k → Bool) (u : ℝ), 0 ≤ u → u ≤ 1 / 2 →
      SampleBound (μ W L) (fun a ω => flowErr W ⟨g, E, L, u⟩ a σ ω) (fun _ => 1)
        (loopSampleSet (cellLen g W B) E L k) CS ((W : ℝ) ^ (-((k : ℝ) + 1)))
        ((W : ℝ) ^ (-Db)))
    (hcr4 : ∀ u ∈ Set.Ioo 0 v, ∀ (a : Fin k → Fin L) (σ : Fin k → Bool),
      (Integrable (fun ω => ‖blockGen W L (gammaG g)
          (fun r N => resLoop g E (mRoot g L E) a σ r N - primLoop g W L E (mRoot g L E) r a σ) u
          (flowH g W L u ω)‖ ^ (4 * p)) (μ W L) ∧
        ∫ ω, ‖blockGen W L (gammaG g)
          (fun r N => resLoop g E (mRoot g L E) a σ r N - primLoop g W L E (mRoot g L E) r a σ) u
          (flowH g W L u ω)‖ ^ (4 * p) ∂(μ W L) ≤ Cp4 * (W : ℝ) ^ (C₁ * ((4 * p : ℕ) : ℝ))) ∧
      (Integrable (fun ω => ‖blockGamma W L (gammaG g) (resLoop g E (mRoot g L E) a σ u)
          (resLoop g E (mRoot g L E) a σ u) (flowH g W L u ω)‖ ^ (4 * p)) (μ W L) ∧
        ∫ ω, ‖blockGamma W L (gammaG g) (resLoop g E (mRoot g L E) a σ u)
          (resLoop g E (mRoot g L E) a σ u) (flowH g W L u ω)‖ ^ (4 * p) ∂(μ W L) ≤
          Cp4 * (W : ℝ) ^ (C₁ * ((4 * p : ℕ) : ℝ))))
    (hcr2 : ∀ u ∈ Set.Ioo 0 v, ∀ (a : Fin k → Fin L) (σ : Fin k → Bool),
      Integrable (fun ω => ‖blockGamma W L (gammaG g) (resLoop g E (mRoot g L E) a σ u)
          (resLoop g E (mRoot g L E) a σ u) (flowH g W L u ω)‖ ^ (2 * p)) (μ W L) ∧
        ∫ ω, ‖blockGamma W L (gammaG g) (resLoop g E (mRoot g L E) a σ u)
          (resLoop g E (mRoot g L E) a σ u) (flowH g W L u ω)‖ ^ (2 * p) ∂(μ W L) ≤
          Cp2 * (W : ℝ) ^ (C₁ * ((2 * p : ℕ) : ℝ)))
    (hW2 : 2 ≤ W) (hWP : 2 ^ k * ((6 * (2 * CV + 1)) ^ k + 1) ≤ (W : ℝ))
    (hWK : ((k : ℝ) + 2 + 2 ^ k) * (2 * p + cK) ^ (4 * p) ≤ (W : ℝ)) (hW2k : (2 : ℝ) ^ k ≤ W)
    (hωc : max (2 ^ (k + 1) * k * C₀) ((k : ℝ) ^ 2 * 4 ^ k * (2 * R + 2 ^ k * C₀)) ≤
      (W : ℝ) ^ ν)
    (hων : 2 * C₀ ≤ (W : ℝ) ^ (1 - ν))
    (hWq : cb * cq * Real.log W + cb * 2 ≤ (W : ℝ) ^ (3 * ν))
    (hWqW : cq * Real.log W + 2 ≤ (W : ℝ) ^ (1 : ℝ))
    (hWΓ : cb * (4 * (2 * p - 1)) ≤ (W : ℝ) ^ (3 * ν))
    (hWM : (2 : ℝ) ^ (n + 3) ≤ (W : ℝ) ^ (ε / 8)) (hWfin : CS + 1 ≤ (W : ℝ) ^ (ε / 2)) :
    μ W L {ω | ∃ l : Word k L, (W : ℝ) ^ ε * flowZeta W ⟨g, E, L, v⟩ ^ k <
      ‖flowErr W ⟨g, E, L, v⟩ l.1 l.2 ω‖} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  obtain ⟨hgC, hE, hLlog, hLV, hv0, hv12⟩ := hpt
  simp only at hgC hE hLlog hLV hv0 hv12
  have hW1 : 1 ≤ W := by omega
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW2r : (2 : ℝ) ≤ W := by exact_mod_cast hW2
  have hg0 : 0 < g := by linarith
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog1 : 0 < Real.log 1.001 := Real.log_pos (by norm_num)
  have hCSp0 : 0 < CSp := by rw [hCSpdef]; positivity
  have hcq : 0 < cq := by rw [hcqdef]; positivity
  have heK0 : 0 ≤ eK := by rw [heKdef]; positivity
  have hR : 0 ≤ R := by rw [hRdef]; positivity
  have hCS1 : 1 ≤ CS := by
    rw [hCSdef]; have : (1 : ℝ) ≤ 6 ^ k := one_le_pow₀ (by norm_num); linarith
  have hCS : 0 ≤ CS := by linarith
  obtain ⟨ω, hωdef⟩ : ∃ ω : ℝ, ω = (W : ℝ) ^ ν := ⟨_, rfl⟩
  have hω1 : 1 ≤ ω := by rw [hωdef]; exact Real.one_le_rpow hW1r hν.le
  have hω0 : 0 < ω := by linarith
  have hω3 : ω ^ 3 = (W : ℝ) ^ (3 * ν) := by
    rw [hωdef, ← Real.rpow_natCast, ← Real.rpow_mul hWpos.le]; ring_nf
  obtain ⟨q, hqdef⟩ : ∃ q : ℕ, q = ⌈cq * Real.log W⌉₊ + 1 := ⟨_, rfl⟩
  have hq1 : 1 ≤ q := by omega
  have hlogW : 0 ≤ Real.log W := Real.log_nonneg hW1r
  have hqle : (q : ℝ) ≤ cq * Real.log W + 2 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ cq * Real.log W by positivity)
    rw [hqdef]; push_cast; linarith
  have hqge : cq * Real.log W ≤ q := by
    rw [hqdef]; push_cast; linarith [Nat.le_ceil (cq * Real.log W)]
  have hqW : (q : ℝ) ≤ W := by
    have := hWqW; rw [Real.rpow_one] at this; exact hqle.trans this
  set w₀ : Fin k → Fin L := fun _ => ⟨0, by omega⟩ with hw₀
  obtain ⟨S, hSdef⟩ : ∃ S : Finset (Fin k → Fin L), S = loopsStepSet g E B W L k w₀ := ⟨_, rfl⟩
  have hSne : S.Nonempty := by rw [hSdef]; exact loopsStepSet_nonempty g E B W L k w₀
  have : Nonempty S := hSne.to_subtype
  obtain ⟨a0, ha0def⟩ : ∃ a0 : ℝ, a0 = (W : ℝ) ^ (-Db) := ⟨_, rfl⟩
  have ha0 : 0 ≤ a0 := by rw [ha0def]; positivity
  obtain ⟨M₄, hM₄def⟩ : ∃ M₄ : ℝ, M₄ = Cp4 * (W : ℝ) ^ (C₁ * ((4 * p : ℕ) : ℝ)) := ⟨_, rfl⟩
  obtain ⟨M₂, hM₂def⟩ : ∃ M₂ : ℝ, M₂ = Cp2 * (W : ℝ) ^ (C₁ * ((2 * p : ℕ) : ℝ)) := ⟨_, rfl⟩
  obtain ⟨Mx, hMxdef⟩ : ∃ Mx : ℝ, Mx = max 1 (max M₄ M₂) := ⟨_, rfl⟩
  have hMx1 : 1 ≤ Mx := by rw [hMxdef]; exact le_max_left _ _
  obtain ⟨cardS, hcardSdef⟩ : ∃ cardS : ℝ, cardS = (Fintype.card (S × (Fin k → Bool)) : ℝ) :=
    ⟨_, rfl⟩
  have hcardpos : 1 ≤ Fintype.card (S × (Fin k → Bool)) := Fintype.card_pos
  have hcardS0 : 0 ≤ cardS := by rw [hcardSdef]; positivity
  obtain ⟨cc, hccdef⟩ : ∃ cc : ℝ, cc = 1.003 * q * (2 * W : ℝ) ^ (2 * k) := ⟨_, rfl⟩
  have hcc0 : 0 ≤ cc := by rw [hccdef]; positivity
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = cc * (2 * cardS) * Mx := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  -- the block bound against the height
  have hωζ : 2 * ω ≤ W * C₀⁻¹ := by
    have e : (W : ℝ) = ω * (W : ℝ) ^ (1 - ν) := by
      rw [hωdef, ← Real.rpow_add hWpos]; simp
    have h1' : 2 * ω * C₀ ≤ W := by
      rw [e]
      have := mul_le_mul_of_nonneg_left hων hω0.le
      linarith
    rw [le_mul_inv_iff₀ hC₀]
    exact h1'
  have hωl : 2 ^ (k + 1) * k * C₀ ≤ ω := hωdef ▸ le_trans (le_max_left _ _) hωc
  have hωc' : (k : ℝ) ^ 2 * 4 ^ k * (2 * R + 2 ^ k * C₀) ≤ ω :=
    hωdef ▸ le_trans (le_max_right _ _) hωc
  have hW3ν : 0 < (W : ℝ) ^ (3 * ν) := by positivity
  have hcb0 : 0 ≤ cb := by rw [hcbdef]; positivity
  have hbh : 1.003 * q * ((k : ℝ) ^ 2 * 4 ^ k * C₀ / ω ^ 3) ≤ 1 := by
    rw [hω3, show 1.003 * (q : ℝ) * ((k : ℝ) ^ 2 * 4 ^ k * C₀ / (W : ℝ) ^ (3 * ν)) =
      cb * q / (W : ℝ) ^ (3 * ν) by rw [hcbdef]; ring, div_le_one hW3ν]
    calc cb * q ≤ cb * (cq * Real.log W + 2) := mul_le_mul_of_nonneg_left hqle hcb0
      _ = cb * cq * Real.log W + cb * 2 := by ring
      _ ≤ (W : ℝ) ^ (3 * ν) := hWq
  have hbΓκ : 1.003 * ((k : ℝ) ^ 2 * 4 ^ k * C₀ / ω ^ 3) * (4 * (2 * p - 1)) ≤ 1 := by
    rw [hω3, show 1.003 * ((k : ℝ) ^ 2 * 4 ^ k * C₀ / (W : ℝ) ^ (3 * ν)) * (4 * (2 * p - 1)) =
      cb * (4 * (2 * p - 1)) / (W : ℝ) ^ (3 * ν) by rw [hcbdef]; ring, div_le_one hW3ν]
    exact hWΓ
  have hfl : (W : ℝ) ^ (-((k : ℝ) + 1)) ≤ ((2 * W : ℝ) ^ k)⁻¹ := by
    rw [Real.rpow_neg hWpos.le,
      show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    apply inv_anti₀ (by positivity)
    rw [mul_pow, pow_succ, mul_comm]
    exact mul_le_mul_of_nonneg_left hW2k (by positivity)
  -- the size of the sample set
  have hX1 : 1 ≤ ((W : ℝ) ^ (B + 2)) ^ k := one_le_pow₀ (Real.one_le_rpow hW1r (by linarith))
  have hWCSp : (W : ℝ) ^ CSp = W * ((W : ℝ) ^ (B + 2)) ^ k := by
    rw [hCSpdef, Real.rpow_add hWpos, Real.rpow_one, ← Real.rpow_natCast,
      ← Real.rpow_mul hWpos.le]
    ring_nf
  have hcardS : cardS ≤ (W : ℝ) ^ CSp := by
    have hc := loopsStepSet_card (g := g) (CV := CV) (B := B) (E := E) hW1 (by linarith) hCV
      hLV w₀
    rw [← hSdef] at hc
    have e : cardS = (S.card : ℝ) * 2 ^ k := by
      rw [hcardSdef, Fintype.card_prod, Fintype.card_coe, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin]
      push_cast; ring
    rw [e, hWCSp]
    have hP0 : 0 ≤ (6 * (2 * CV + 1)) ^ k := by positivity
    calc (S.card : ℝ) * 2 ^ k ≤
        ((6 * (2 * CV + 1)) ^ k * ((W : ℝ) ^ (B + 2)) ^ k + 1) * 2 ^ k := by gcongr
      _ ≤ (((6 * (2 * CV + 1)) ^ k + 1) * ((W : ℝ) ^ (B + 2)) ^ k) * 2 ^ k := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [add_mul, one_mul]
          linarith
      _ = (2 ^ k * ((6 * (2 * CV + 1)) ^ k + 1)) * ((W : ℝ) ^ (B + 2)) ^ k := by ring
      _ ≤ W * ((W : ℝ) ^ (B + 2)) ^ k := by gcongr
  have hSq : (Fintype.card (S × (Fin k → Bool)) : ℝ) ^ ((1 : ℝ) / (2 * q)) ≤ 1.001 := by
    have hlogc : Real.log cardS ≤ CSp * Real.log W := by
      rw [← Real.log_rpow hWpos]
      exact Real.log_le_log (by rw [hcardSdef]; exact_mod_cast hcardpos) hcardS
    rw [hcardSdef] at hlogc
    have h := card_rpow_le_of_q (Fintype.card (S × (Fin k → Bool))) hcardpos (δq := 0.001)
      (by norm_num) hq1 (by
        rw [show (1 : ℝ) + 0.001 = 1.001 by norm_num]
        calc Real.log (Fintype.card (S × (Fin k → Bool)) : ℝ) / (2 * Real.log 1.001) ≤
            CSp * Real.log W / (2 * Real.log 1.001) := by gcongr
          _ = cq * Real.log W := by rw [hcqdef]; ring
          _ ≤ q := hqge)
    rw [show (1 : ℝ) + 0.001 = 1.001 by norm_num] at h
    exact h
  -- the crude constant
  have hK4 : (1.003 * q * (2 * W : ℝ) ^ (2 * k)) ^ (4 * p) *
      (2 * Fintype.card (S × (Fin k → Bool)) : ℝ) ^ (4 * p) * M₄ ≤ K ^ (4 * p) := by
    rw [← hccdef, ← hcardSdef, hKdef, mul_pow (cc * (2 * cardS)) Mx, mul_pow cc (2 * cardS)]
    have : M₄ ≤ Mx ^ (4 * p) := by
      rw [hMxdef]
      exact (le_trans (le_max_left _ _) (le_max_right _ _)).trans
        (le_self_pow₀ (le_max_left _ _) (by omega))
    gcongr
  have hK2 : (1.003 * q * (2 * W : ℝ) ^ (2 * k)) ^ (2 * p) *
      (Fintype.card (S × (Fin k → Bool)) : ℝ) ^ (2 * p) * M₂ ≤ K ^ (2 * p) := by
    rw [← hccdef, ← hcardSdef, hKdef, mul_pow (cc * (2 * cardS)) Mx, mul_pow cc (2 * cardS)]
    have : M₂ ≤ Mx ^ (2 * p) := by
      rw [hMxdef]
      exact (le_trans (le_max_right _ _) (le_max_right _ _)).trans
        (le_self_pow₀ (le_max_left _ _) (by omega))
    have h2c : cardS ≤ 2 * cardS := by linarith
    calc cc ^ (2 * p) * cardS ^ (2 * p) * M₂ ≤ cc ^ (2 * p) * cardS ^ (2 * p) * Mx ^ (2 * p) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ cc ^ (2 * p) * (2 * cardS) ^ (2 * p) * Mx ^ (2 * p) := by gcongr
  have hMxle : Mx ≤ max 1 (max Cp4 Cp2) * (W : ℝ) ^ (4 * p * |C₁|) := by
    rw [hMxdef, hM₄def, hM₂def]; exact loopsStep_num_Mx hW1r p C₁ Cp4 Cp2
  have hKle : K ≤ cK * (W : ℝ) ^ eK := by
    rw [hKdef, hccdef, hcKdef, heKdef]
    exact loopsStep_num_K hW1r (by positivity) hqW hcardS0 hcardS (by linarith) hMxle
  set δb : ℝ := a0 + a0 + k * a0 + 2 ^ k * a0 with hδbdef
  have hδb : 0 ≤ δb := by positivity
  have hKδ : (2 * p + K) * δb ^ (1 / (4 * (p : ℝ))) ≤ 1 := by
    have e : δb = ((k : ℝ) + 2 + 2 ^ k) * (W : ℝ) ^ (-Db) := by rw [hδbdef, ha0def]; ring
    rw [e]
    exact loopsStep_num_Kδ hW1r hp1 hK0 heK0 (by positivity) hD
      hDbdef hKle hWK
  have hMk : ((2 : ℝ) ^ (⌈4 * (1.001 * ((((k : ℝ) + 1) * R + 2) * (CS + 1) + 2) + 1)⌉₊ + 3) *
      ω ^ (k + 2)) ^ (2 * p) / ((W : ℝ) ^ (ε / 2)) ^ (2 * p) ≤ (W : ℝ) ^ (-(D + 1)) := by
    rw [← hndef, hωdef, hνdef]
    exact loopsStep_num_Mk hW1r hε hpD hWM
  have hfin : CS * (W : ℝ) ^ (ε / 2) + 1 ≤ (W : ℝ) ^ ε := loopsStep_num_fin hW1r hCS hWfin
  have hfail : (W : ℝ) ^ (-(D + 1)) + 2 ^ k * a0 ≤ (W : ℝ) ^ (-D) := by
    rw [ha0def]
    have : 0 ≤ 4 * (p : ℝ) * eK := by positivity
    exact loopsStep_num_fail hW2r hW2k (by rw [hDbdef]; linarith)
  -- the rows at every time
  have hKrows : ∀ u ∈ Set.Ioo 0 v, ∀ n' : ℕ, 2 ≤ n' → n' ≤ k → ∀ (b : Fin n' → Fin L)
      (s : Fin n' → Bool) (i : Fin n'),
      gammaG g * W * ∑ c : Fin L,
        ‖primLoop g W L E (mRoot g L E) u (Function.update b i c) s‖ ≤
        R * zetaProp g W L u ^ (n' - 2) := by
    intro u hu n' hn2 hnk b s i
    have hu0 : 0 ≤ u := hu.1.le
    have hu12 : u ≤ 1 / 2 := by linarith [hu.2]
    rw [hRdef]
    exact loopsStep_row_scale hg1 hW1 E _ u b s i hn2 hnk hC'.le
      (loopsStep_zeta_bounds hg1 hW1 hgL hu0 hu12).1 (hrows u hu0 hu12 n' hn2 hnk i b s)
  -- the bad sets
  have hbad : ∀ u ∈ Set.Ioo 0 v, stdGauss (Fin L × Fin W × Fin W)
      {x | ¬ loopsStepGood g E W L k S ω CS ((k : ℝ) + 1) u
        (Real.sqrt (u * (gammaG g / W)) • x)} ≤ ENNReal.ofReal δb := by
    intro u hu
    have hu0 : 0 ≤ u := hu.1.le
    have hu12 : u ≤ 1 / 2 := by linarith [hu.2]
    have h4 : stdGauss (Fin L × Fin W × Fin W) {x | ¬ loopsStepSamp g E W L k S CS
        ((k : ℝ) + 1) u (Real.sqrt (u * (gammaG g / W)) • x)} ≤ ENNReal.ofReal (2 ^ k * a0) := by
      rw [hSdef, ha0def]
      exact loopsStepSet_samp g E B hCS1 w₀ hu0
        (fun h σ => hsb h σ u hu0 hu12)
    have := loopsStep_bad_le g E hW1 (by omega) hroot S (ω := ω) (CS := CS)
      (fl := (k : ℝ) + 1) hu0 ha0 ha0 ha0 (by positivity)
      (by rw [hωdef, ha0def]; exact h1 u hu) (by rw [hωdef, ha0def]; exact h2 u hu)
      (fun n' hn2 hnk => by rw [hωdef, ha0def]; exact h3 u hu n' hn2 hnk) h4
    rw [hδbdef]
    exact this
  have hsv : stdGauss (Fin L × Fin W × Fin W) {x | ¬ loopsStepSamp g E W L k S CS
      ((k : ℝ) + 1) v (Real.sqrt (v * (gammaG g / W)) • x)} ≤ ENNReal.ofReal (2 ^ k * a0) := by
    rw [hSdef, ha0def]
    exact loopsStepSet_samp g E B hCS1 w₀ hv0
      (fun h σ => hsb h σ v hv0 hv12)
  have hcr : ∀ u ∈ Set.Ioo 0 v, ∀ (a : Fin k → Fin L) (σ : Fin k → Bool),
      (Integrable (fun x => ‖coordGen (gammaG g / W)
          (fun r y => loopErrField g E (mRoot g L E) W L a σ r y) u
          (Real.sqrt (u * (gammaG g / W)) • x)‖ ^ (4 * p)) (stdGauss (Fin L × Fin W × Fin W)) ∧
        ∫ x, ‖coordGen (gammaG g / W)
          (fun r y => loopErrField g E (mRoot g L E) W L a σ r y) u
          (Real.sqrt (u * (gammaG g / W)) • x)‖ ^ (4 * p) ∂(stdGauss (Fin L × Fin W × Fin W)) ≤
          M₄) ∧
      (Integrable (fun x => ‖coordGamma (gammaG g / W)
          (fun y => loopErrField g E (mRoot g L E) W L a σ u y)
          (fun y => loopErrField g E (mRoot g L E) W L a σ u y)
          (Real.sqrt (u * (gammaG g / W)) • x)‖ ^ (4 * p)) (stdGauss (Fin L × Fin W × Fin W)) ∧
        ∫ x, ‖coordGamma (gammaG g / W)
          (fun y => loopErrField g E (mRoot g L E) W L a σ u y)
          (fun y => loopErrField g E (mRoot g L E) W L a σ u y)
          (Real.sqrt (u * (gammaG g / W)) • x)‖ ^ (4 * p) ∂(stdGauss (Fin L × Fin W × Fin W)) ≤
          M₄) ∧
      (Integrable (fun x => ‖coordGamma (gammaG g / W)
          (fun y => loopErrField g E (mRoot g L E) W L a σ u y)
          (fun y => loopErrField g E (mRoot g L E) W L a σ u y)
          (Real.sqrt (u * (gammaG g / W)) • x)‖ ^ (2 * p)) (stdGauss (Fin L × Fin W × Fin W)) ∧
        ∫ x, ‖coordGamma (gammaG g / W)
          (fun y => loopErrField g E (mRoot g L E) W L a σ u y)
          (fun y => loopErrField g E (mRoot g L E) W L a σ u y)
          (Real.sqrt (u * (gammaG g / W)) • x)‖ ^ (2 * p) ∂(stdGauss (Fin L × Fin W × Fin W)) ≤
          M₂) := by
    intro u hu a σ
    have hu0 : 0 ≤ u := hu.1.le
    simp only [loopsStep_coordGen_eq g E _ a σ hu0, loopsStep_coordGamma_eq g E _ a σ hu0]
    obtain ⟨⟨i1, b1⟩, ⟨i2, b2⟩⟩ := hcr4 u hu a σ
    obtain ⟨i3, b3⟩ := hcr2 u hu a σ
    rw [hM₄def, hM₂def]
    exact ⟨⟨i1, b1⟩, ⟨i2, b2⟩, ⟨i3, b3⟩⟩
  have hmain := loopsStep_atW g E (W := W) (L := L) (k := k) hW2 hL3 hk hg1 hgL hroot hC₀ hmim
    hvpos hv12 S hSne hq1 hp1 (ω := ω) (R := R) (CS := CS) (fl := (k : ℝ) + 1) (δb := δb)
    (δv := 2 ^ k * a0) (K := K) (M₄ := M₄) (M₂ := M₂) (J := (W : ℝ) ^ (ε / 2)) (ε := ε) (D := D)
    hω1 hR hCS hδb (by positivity) hK0 (by positivity) hωζ hωl hωc' hbh hbΓκ hfl hSq hK4 hK2 hKδ
    hMk hfin hfail hKrows hbad hsv hcr
  refine le_trans (measure_mono ?_) hmain
  rintro x ⟨l, hl⟩
  refine ⟨l, ?_⟩
  rw [flowErr_eq_loopErrField W ⟨g, E, L, v⟩ hv0] at hl
  exact hl

end Point


set_option maxHeartbeats 1000000 in
-- The proof is long: the constants and the thresholds in `W` of all inputs.
/-- The induction step of Lemma 5.6 [fo:prop:inputs] for the loop errors (the statement of
`lemma46_err_step`). -/
private theorem loopsStep_err_step_aux (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) :
    ∃ Cκ₀ : ℝ, 1 ≤ Cκ₀ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      ∀ k : ℕ, 2 ≤ k →
      (∀ k' : ℕ, 1 ≤ k' → k' < k → PrecMax (fun p : FlowPt => p.L) (initLarge κ Cκ CV ρ)
        (Λ := fun _ p => Word k' p.L) (fun W p w ω => flowErr W p w.1 w.2 ω)
        (fun W p _ => flowZeta W p ^ k')) →
      PrecMax (fun p : FlowPt => p.L) (initLarge κ Cκ CV ρ) (Λ := fun _ p => Word k p.L)
        (fun W p w ω => flowErr W p w.1 w.2 ω) (fun W p _ => flowZeta W p ^ k) := by
  obtain ⟨Cκv, hCκv, Hv⟩ := vert_max κ CV hκ hκ2 hCV
  obtain ⟨Cκa, hCκa, Ha⟩ := lemma46_avg κ CV hκ hκ2 hCV
  obtain ⟨Cκc, hCκc, Hc⟩ := loops_gen_crude κ CV hκ hκ2 hCV
  obtain ⟨Cκf, hCκf, Hf⟩ := loopsStep_rows κ hκ hκ2
  obtain ⟨Cκr, C₀, hCκr, hC₀1, Hr⟩ := loopsStep_root κ hκ hκ2
  refine ⟨max (max (max Cκv Cκa) (max Cκc Cκf)) Cκr, le_trans hCκr (le_max_right _ _),
    fun Cκ hCκ ρ hρ k hk IH => ?_⟩
  have hCv : Cκv ≤ Cκ :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hCκ
  have hCa : Cκa ≤ Cκ :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hCκ
  have hCc : Cκc ≤ Cκ :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hCκ
  have hCf : Cκf ≤ Cκ :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hCκ
  have hCr : Cκr ≤ Cκ := le_trans (le_max_right _ _) hCκ
  have hCκ1 : 1 ≤ Cκ := le_trans hCκr hCr
  have hC₀ : 0 < C₀ := by linarith
  -- it suffices to treat `ε ≤ 1`
  suffices H : ∀ ε D : ℝ, 0 < ε → ε ≤ 1 → 0 < D → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ pt ∈ initLarge κ Cκ CV ρ W, μ W pt.L {ω | ∃ l : Word k pt.L,
        (W : ℝ) ^ ε * flowZeta W pt ^ k < ‖flowErr W pt l.1 l.2 ω‖} ≤
          ENNReal.ofReal ((W : ℝ) ^ (-D)) by
    intro ε D hε hD
    obtain ⟨W₀, hW₀⟩ := H (min ε 1) D (lt_min hε one_pos) (min_le_right _ _) hD
    refine ⟨max W₀ 1, fun W hW pt hpt =>
      (measure_mono ?_).trans (hW₀ W (le_trans (le_max_left _ _) hW) pt hpt)⟩
    rintro ω ⟨l, hl⟩
    refine ⟨l, lt_of_le_of_lt ?_ hl⟩
    have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_trans (le_max_right _ _) hW
    have hg0 : 0 ≤ pt.g := le_trans (by linarith) hpt.1
    have hz := loopsStep_zeta_nonneg hg0 W pt.L (u := pt.u) (by linarith [hpt.2.2.2.2.2])
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hW1 (min_le_left _ _)) (pow_nonneg hz _)
  intro ε D hε hε1 hD
  obtain ⟨Csr, C', hCsr, hC', HR⟩ := Hf k
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = C' * 2 ^ k := ⟨_, rfl⟩
  obtain ⟨CS, hCSdef⟩ : ∃ CS : ℝ, CS = 2 * 6 ^ k := ⟨_, rfl⟩
  obtain ⟨n, hndef⟩ : ∃ n : ℕ,
      n = ⌈4 * (1.001 * ((((k : ℝ) + 1) * R + 2) * (CS + 1) + 2) + 1)⌉₊ := ⟨_, rfl⟩
  obtain ⟨ν, hνdef⟩ : ∃ ν : ℝ, ν = ε / (4 * (k + 2)) := ⟨_, rfl⟩
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hν : 0 < ν := by rw [hνdef]; positivity
  have hν1 : ν ≤ 1 / 16 := by
    rw [hνdef, div_le_iff₀ (by positivity)]; nlinarith
  obtain ⟨p, hpdef⟩ : ∃ p : ℕ, p = ⌈4 * (D + 1) / ε⌉₊ + 1 := ⟨_, rfl⟩
  have hp1 : 1 ≤ p := by omega
  have hpD : 4 * (D + 1) / ε ≤ p := by
    rw [hpdef]; push_cast; linarith [Nat.le_ceil (4 * (D + 1) / ε)]
  obtain ⟨Cs, hCsdef⟩ : ∃ Cs : ℝ, Cs = max 3 C₀ := ⟨_, rfl⟩
  have hCs1 : 1 < Cs := by rw [hCsdef]; exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  obtain ⟨B, Cκs, hB, hCκs, HS⟩ := loop_sampling' κ Cs hκ hκ2 hCs1 k (by omega) 1 (1 / 2) 1
    ((k : ℝ) + 1) one_pos (by norm_num) (by norm_num) one_pos (by positivity)
  obtain ⟨C₁, HC⟩ := Hc Cκ hCc ρ hρ k (by omega)
  obtain ⟨Cp4, W₄, HW4⟩ := HC (4 * p) (by omega)
  obtain ⟨Cp2, W₂, HW2⟩ := HC (2 * p) (by omega)
  obtain ⟨CSp, hCSpdef⟩ : ∃ CSp : ℝ, CSp = k * (B + 2) + 1 := ⟨_, rfl⟩
  obtain ⟨eK, heKdef⟩ : ∃ eK : ℝ, eK = 1 + 2 * k + CSp + 4 * p * |C₁| := ⟨_, rfl⟩
  obtain ⟨cK, hcKdef⟩ : ∃ cK : ℝ, cK = 2.006 * 4 ^ k * max 1 (max Cp4 Cp2) := ⟨_, rfl⟩
  obtain ⟨Db, hDbdef⟩ : ∃ Db : ℝ, Db = 4 * p * eK + D + 2 := ⟨_, rfl⟩
  have hDb : 0 < Db := by
    have : 0 ≤ eK := by rw [heKdef, hCSpdef]; positivity
    rw [hDbdef]; positivity
  obtain ⟨W₅, HS5⟩ := HS Db hDb
  obtain ⟨Wv, HVv⟩ := Hv Cκ hCv ρ hρ ν Db hν hDb
  obtain ⟨Wa, HAa⟩ := Ha Cκ hCa ρ hρ ν Db hν hDb
  have HIH : ∀ k' ∈ Finset.Ico 2 k, ∀ᶠ W : ℕ in atTop, ∀ pt ∈ initLarge κ Cκ CV ρ W,
      μ W pt.L {ω | ∃ l : Word k' pt.L, (W : ℝ) ^ ν * flowZeta W pt ^ k' <
        ‖flowErr W pt l.1 l.2 ω‖} ≤ ENNReal.ofReal ((W : ℝ) ^ (-Db)) := by
    intro k' hk'
    rw [Finset.mem_Ico] at hk'
    obtain ⟨W₀, h⟩ := IH k' (by omega) hk'.2 ν Db hν hDb
    exact eventually_atTop.2 ⟨W₀, h⟩
  obtain ⟨cb, hcbdef⟩ : ∃ cb : ℝ, cb = 1.003 * (k : ℝ) ^ 2 * 4 ^ k * C₀ := ⟨_, rfl⟩
  obtain ⟨cq, hcqdef⟩ : ∃ cq : ℝ, cq = CSp / (2 * Real.log 1.001) := ⟨_, rfl⟩
  have hev : ∀ᶠ W : ℕ in atTop,
      (∀ CV' : ℝ, ∀ pt ∈ initLarge κ Cκ CV' ρ W, 1 ≤ pt.g ∧ max 4 Csr * pt.g ^ 2 ≤ pt.L ∧
        3 ≤ pt.L ∧ IsDysonRootV (hopB pt.g) (gammaG pt.g) pt.L pt.E (mRoot pt.g pt.L pt.E) ∧
        ‖mRoot pt.g pt.L pt.E‖ ≤ C₀ ∧ C₀⁻¹ ≤ (mRoot pt.g pt.L pt.E).im) ∧
      (∀ k' ∈ Finset.Ico 2 k, ∀ pt ∈ initLarge κ Cκ CV ρ W,
        μ W pt.L {ω | ∃ l : Word k' pt.L, (W : ℝ) ^ ν * flowZeta W pt ^ k' <
          ‖flowErr W pt l.1 l.2 ω‖} ≤ ENNReal.ofReal ((W : ℝ) ^ (-Db))) ∧
      max (max Wv Wa) (max (max W₂ W₄) W₅) ≤ W ∧ 2 ≤ W ∧ CV ≤ (W : ℝ) ∧
      2 ^ k * ((6 * (2 * CV + 1)) ^ k + 1) ≤ (W : ℝ) ∧
      ((k : ℝ) + 2 + 2 ^ k) * (2 * p + cK) ^ (4 * p) ≤ (W : ℝ) ∧
      (2 : ℝ) ^ k ≤ W ∧
      max (2 ^ (k + 1) * k * C₀) ((k : ℝ) ^ 2 * 4 ^ k * (2 * R + 2 ^ k * C₀)) ≤ (W : ℝ) ^ ν ∧
      2 * C₀ ≤ (W : ℝ) ^ (1 - ν) ∧
      cb * cq * Real.log W + cb * 2 ≤ (W : ℝ) ^ (3 * ν) ∧
      cq * Real.log W + 2 ≤ (W : ℝ) ^ (1 : ℝ) ∧
      cb * (4 * (2 * p - 1)) ≤ (W : ℝ) ^ (3 * ν) ∧
      (2 : ℝ) ^ (n + 3) ≤ (W : ℝ) ^ (ε / 8) ∧ CS + 1 ≤ (W : ℝ) ^ (ε / 2) ∧
      C₀ ≤ (W : ℝ) ^ (1 / 2 : ℝ) ∧ Cκs ≤ (W : ℝ) ^ (B / 2) := by
    have hrp : ∀ {a : ℝ}, 0 < a → ∀ c : ℝ, ∀ᶠ W : ℕ in atTop, c ≤ (W : ℝ) ^ a :=
      fun ha c => ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop c
    have hnat : ∀ c : ℝ, ∀ᶠ W : ℕ in atTop, c ≤ (W : ℝ) :=
      fun c => tendsto_natCast_atTop_atTop.eventually_ge_atTop c
    filter_upwards [Hr Cκ hCr ρ hρ (max 4 Csr), (Filter.eventually_all_finset _).2 HIH,
      eventually_ge_atTop (max (max Wv Wa) (max (max W₂ W₄) W₅)), eventually_ge_atTop 2,
      hnat CV, hnat (2 ^ k * ((6 * (2 * CV + 1)) ^ k + 1)),
      hnat (((k : ℝ) + 2 + 2 ^ k) * (2 * p + cK) ^ (4 * p)),
      hnat (2 ^ k),
      hrp hν (max (2 ^ (k + 1) * k * C₀) ((k : ℝ) ^ 2 * 4 ^ k * (2 * R + 2 ^ k * C₀))),
      hrp (by linarith : (0 : ℝ) < 1 - ν) (2 * C₀),
      loopsStep_ev_log (cb * cq) (cb * 2) (by positivity : (0 : ℝ) < 3 * ν),
      loopsStep_ev_log cq 2 one_pos,
      hrp (by positivity : (0 : ℝ) < 3 * ν) (cb * (4 * (2 * p - 1))),
      hrp (by positivity : (0 : ℝ) < ε / 8) (2 ^ (n + 3)),
      hrp (by positivity : (0 : ℝ) < ε / 2) (CS + 1),
      hrp (by norm_num : (0 : ℝ) < 1 / 2) C₀, hrp (by linarith : (0 : ℝ) < B / 2) Cκs]
      with W h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
  obtain ⟨W₀, HW₀⟩ := eventually_atTop.1 hev
  refine ⟨W₀, fun W hW pt hpt => ?_⟩
  obtain ⟨hR1, hIH, hWs, hW2, hWCV, hWP, hWK, hW2k, hωc, hων, hWq, hWqW, hWΓ, hWM, hWfin,
    hWvert, hWs2⟩ := HW₀ W hW
  obtain ⟨hg1, hTL, hL3, hroot, hmC, hmim⟩ := hR1 CV pt hpt
  obtain ⟨g, E, L, v⟩ := pt
  have hpt' := hpt
  obtain ⟨hgC, hE, hLlog, hLV, hv0, hv12⟩ := hpt'
  simp only at hg1 hTL hL3 hroot hmC hmim hgC hE hLlog hLV hv0 hv12 ⊢
  have hW1 : 1 ≤ W := by omega
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW2r : (2 : ℝ) ≤ W := by exact_mod_cast hW2
  have hg0 : 0 < g := by linarith
  have hgg : 0 ≤ g ^ 2 := sq_nonneg g
  have hgL : g ^ 2 ≤ L := le_trans (le_mul_of_one_le_left hgg (le_trans (by norm_num)
    (le_max_left _ _))) hTL
  have h4gL : 4 * g ^ 2 ≤ L := le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hgg) hTL
  have hCsrL : Csr * g ^ 2 ≤ L :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hgg) hTL
  rcases hv0.eq_or_lt with hv | hvpos
  · -- at time `0` the loop errors vanish
    subst hv
    have hempty : {ω : Ω W L | ∃ l : Word k L, (W : ℝ) ^ ε * flowZeta W ⟨g, E, L, 0⟩ ^ k <
        ‖flowErr W ⟨g, E, L, 0⟩ l.1 l.2 ω‖} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
      intro l
      have e : flowErr W ⟨g, E, L, 0⟩ l.1 l.2 ω = 0 := by
        unfold flowErr flowG
        simp only
        rw [resolvent_flow_zero, primLoop_init g W L hW1 hL3 E _ hroot, sub_self]
      rw [e, norm_zero]
      have hz := loopsStep_zeta_nonneg hg0.le W L (u := 0) (by norm_num)
      exact mul_nonneg (by positivity) (pow_nonneg hz _)
    rw [hempty, measure_empty]
    exact bot_le
  -- the inputs at the times `u ∈ (0, v]`
  have hpu : ∀ u, 0 ≤ u → u ≤ 1 / 2 → (⟨g, E, L, u⟩ : FlowPt) ∈ initLarge κ Cκ CV ρ W :=
    fun u hu0 hu12 => ⟨hgC, hE, hLlog, hLV, hu0, hu12⟩
  have h1 : ∀ u ∈ Set.Ioo 0 v, μ W L {x | ∃ c d : Fin L,
      (W : ℝ) ^ ν < ‖blockOf (flowG W ⟨g, E, L, u⟩ x) c d‖} ≤
        ENNReal.ofReal ((W : ℝ) ^ (-Db)) := by
    intro u hu
    have hu0 : 0 ≤ u := hu.1.le
    have hu12 : u ≤ 1 / 2 := by linarith [hu.2]
    have hη : g ^ 2 * etaChar g (mRoot g L E) u ≤ (W : ℝ) ^ (1 / 2 : ℝ) := by
      have e : g ^ 2 * etaChar g (mRoot g L E) u = (1 - u) * (mRoot g L E).im := by
        unfold etaChar; rw [loopsStep_gammaG_eq hg1]; field_simp
      rw [e]
      have him : (mRoot g L E).im ≤ ‖mRoot g L E‖ := Complex.im_le_norm _
      have hm0 : 0 < (mRoot g L E).im := hroot.1
      have h1u : (1 - u) * (mRoot g L E).im ≤ (mRoot g L E).im :=
        mul_le_of_le_one_left hm0.le (by linarith)
      linarith
    have h := HVv W (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hWs)
      (⟨g, E, L, u⟩, etaChar g (mRoot g L E) u) (hpu u hu0 hu12) le_rfl hη
    refine le_trans (measure_mono ?_) h
    rintro x ⟨c, d, hcd⟩
    refine ⟨c, d, Or.inl ?_⟩
    have e : segG W ((⟨g, E, L, u⟩ : FlowPt), etaChar g (mRoot g L E) u) x =
        flowG W ⟨g, E, L, u⟩ x := by
      unfold segG flowG
      simp only
      rw [← im_zChar g E (mRoot g L E) u, Complex.re_add_im]
    rw [e]
    exact hcd
  have h2 : ∀ u ∈ Set.Ioo 0 v, μ W L {x | ∃ c : Fin L, (W : ℝ) ^ ν * zetaProp g W L u <
      ‖blockTr (flowG W ⟨g, E, L, u⟩ x - flowM W ⟨g, E, L, u⟩) c c‖} ≤
        ENNReal.ofReal ((W : ℝ) ^ (-Db)) := by
    intro u hu
    have h := HAa W (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hWs)
      ⟨g, E, L, u⟩ (hpu u hu.1.le (by linarith [hu.2]))
    refine le_trans (measure_mono ?_) h
    rintro x ⟨c, hc⟩
    exact ⟨(c, c), hc⟩
  have h3 : ∀ u ∈ Set.Ioo 0 v, ∀ n' : ℕ, 2 ≤ n' → n' < k → μ W L {x | ∃ w : Word n' L,
      (W : ℝ) ^ ν * zetaProp g W L u ^ n' < ‖flowErr W ⟨g, E, L, u⟩ w.1 w.2 x‖} ≤
        ENNReal.ofReal ((W : ℝ) ^ (-Db)) := fun u hu n' hn2 hnk =>
    hIH n' (Finset.mem_Ico.2 ⟨hn2, hnk⟩) ⟨g, E, L, u⟩ (hpu u hu.1.le (by linarith [hu.2]))
  have hsb : (W : ℝ) ^ B ≤ g ^ 2 → ∀ (σ : Fin k → Bool) (u : ℝ), 0 ≤ u → u ≤ 1 / 2 →
      SampleBound (μ W L) (fun a ω => flowErr W ⟨g, E, L, u⟩ a σ ω) (fun _ => 1)
        (loopSampleSet (cellLen g W B) E L k) CS ((W : ℝ) ^ (-((k : ℝ) + 1)))
        ((W : ℝ) ^ (-Db)) := by
    intro hBg σ u hu0 hu12
    have hgB : Cκs ≤ g := by
      refine le_trans hWs2 ?_
      have hsq : ((W : ℝ) ^ (B / 2)) ^ 2 ≤ g ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hWpos.le]
        ring_nf
        exact hBg
      exact le_of_pow_le_pow_left₀ two_ne_zero hg0.le hsq
    have hLCs : (L : ℝ) ≤ g ^ 2 * (W : ℝ) ^ Cs := by
      have h3' : (W : ℝ) ^ (3 : ℝ) ≤ (W : ℝ) ^ Cs :=
        Real.rpow_le_rpow_of_exponent_le hW1r (by rw [hCsdef]; exact le_max_left _ _)
      have e3 : (W : ℝ) ^ (3 : ℝ) = W * (W : ℝ) ^ 2 := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
      calc (L : ℝ) ≤ CV * g ^ 2 * (W : ℝ) ^ 2 := hLV
        _ ≤ W * g ^ 2 * (W : ℝ) ^ 2 := by gcongr
        _ = g ^ 2 * (W * (W : ℝ) ^ 2) := by ring
        _ ≤ g ^ 2 * (W : ℝ) ^ Cs := by rw [← e3]; gcongr
    have hmCs : ‖mRoot g L E‖ ≤ Cs := hmC.trans (by rw [hCsdef]; exact le_max_right _ _)
    have hmims : Cs⁻¹ ≤ (mRoot g L E).im :=
      le_trans (inv_anti₀ hC₀ (by rw [hCsdef]; exact le_max_right _ _)) hmim
    have hW3 : (W : ℝ) ^ (-3 : ℝ) ≤ 1 - u := by
      rw [Real.rpow_neg hWpos.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have h8 : (8 : ℝ) ≤ (W : ℝ) ^ 3 := by nlinarith
      have : ((W : ℝ) ^ 3)⁻¹ ≤ 1 / 2 := by
        rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
      linarith
    have h := (HS5 W (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hWs) g L E hgB
      hBg h4gL hLCs hE hroot hmCs hmims σ u hu0 hW3).2.1
    rw [hCSdef]
    exact h
  have hcr4 := fun u (hu : u ∈ Set.Ioo 0 v) => HW4 W
    (le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hWs)
    ⟨g, E, L, u⟩ (hpu u hu.1.le (by linarith [hu.2]))
  have hcr2 := fun u (hu : u ∈ Set.Ioo 0 v) => HW2 W
    (le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hWs)
    ⟨g, E, L, u⟩ (hpu u hu.1.le (by linarith [hu.2]))
  exact loopsStep_point κ Cκ CV ρ hk hCV hpt hvpos hC₀ hC' hB hε hD hν hνdef hp1 hpD hRdef
    hCSdef hndef hCSpdef heKdef hcKdef hDbdef hcbdef hcqdef hg1 hgL hL3 hroot hmim
    (fun t ht0 ht n' hn2 hnk i a σ =>
      HR g (le_trans hCf hgC) L hL3 hCsrL E hE _ hroot t ht0 ht n' hn2 hnk i a σ)
    h1 h2 h3 hsb (fun u hu a σ => hcr4 u hu a σ) (fun u hu a σ => (hcr2 u hu a σ).2)
    hW2 hWP hWK hW2k hωc hων hWq hWqW hWΓ hWM hWfin

/-- One step of the loop-error induction of Lemma 5.6 [fo:prop:inputs] at each fixed
`u ∈ [0, 1/2]`: if `max_{a,σ} |D_{k'}| ≺ ζ_u^{k'}` for `1 ≤ k' < k`, then
`max_{a,σ} |D_k| ≺ ζ_u^k` (the loop component of (5.22) [gc:eq:one-step-input], with Lemma 5.8
[uvc:thm:ordinary-sampling] for the maximum). -/
theorem lemma46_err_step (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) :
    ∃ Cκ₀ : ℝ, 1 ≤ Cκ₀ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      ∀ k : ℕ, 2 ≤ k →
      (∀ k' : ℕ, 1 ≤ k' → k' < k → PrecMax (fun p : FlowPt => p.L) (initLarge κ Cκ CV ρ)
        (Λ := fun _ p => Word k' p.L) (fun W p w ω => flowErr W p w.1 w.2 ω)
        (fun W p _ => flowZeta W p ^ k')) →
      PrecMax (fun p : FlowPt => p.L) (initLarge κ Cκ CV ρ) (Λ := fun _ p => Word k p.L)
        (fun W p w ω => flowErr W p w.1 w.2 ω) (fun W p _ => flowZeta W p ^ k) :=
  loopsStep_err_step_aux κ CV hκ hκ2 hCV

/-! ### Loop errors of length one -/

section One

/-- The length-one loops against `m^σ` are the centered block traces. -/
private theorem loopsStep_loop_one_sub (g E : ℝ) (W L : ℕ) (hW : 1 ≤ W) (hL : 1 ≤ L) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (c : Fin L) (s : Bool) :
    ‖loopTr G ![c] ![s] - sgnScalar m s‖ =
      ‖blockTr (G - dysonMat (hopB g) (gammaG g) L E m ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) c c‖ := by
  have hM := loopTr_one_dysonMat g E W L hW hL m hm c true
  simp only [ite_true] at hM
  have hbt : ∀ X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ,
      blockTr X c c = loopTr X ![c] ![true] := by
    intro X; rw [loopTr_one]; rfl
  have hsub : blockTr (G - dysonMat (hopB g) (gammaG g) L E m ⊗ₖ
      (1 : Matrix (Fin W) (Fin W) ℂ)) c c = loopTr G ![c] ![true] - m := by
    have e : blockTr (G - dysonMat (hopB g) (gammaG g) L E m ⊗ₖ
        (1 : Matrix (Fin W) (Fin W) ℂ)) c c = blockTr G c c -
          blockTr (dysonMat (hopB g) (gammaG g) L E m ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) c c := by
      unfold blockTr
      simp only [Matrix.sub_apply, Finset.sum_sub_distrib, mul_sub]
    rw [e, hbt G, hbt, hM]
  rw [hsub]
  cases s
  · have h1 : loopTr G ![c] ![false] = star (loopTr G ![c] ![true]) := by
      rw [loopTr_one]
      have : loopTr G ![c] ![false] = loopTr Gᴴ ![c] ![true] := by simp [loopTr, sgnMat]
      rw [this, loopTr_one]
      simp [Matrix.conjTranspose_apply, star_sum]
    rw [h1, sgnScalar]
    simp only [Bool.false_eq_true, ite_false]
    rw [← star_sub, norm_star]
  · simp [sgnScalar]

/-- The primitive loop of length one is `m^σ`. -/
private theorem loopsStep_primLoop_one (g : ℝ) (W L : ℕ) (E : ℝ) (m : ℂ) (t : ℝ) (c : Fin L)
    (s : Bool) : primLoop g W L E m t ![c] ![s] = sgnScalar m s := by
  unfold primLoop primK primF sgnScalar
  cases s <;> simp

/-- `D_1(a, σ)` has the modulus of `⟨G - M⟩_{aa}`. -/
private theorem loopsStep_flowErr_one (W : ℕ) (p : FlowPt) (hW : 1 ≤ W) (hL : 1 ≤ p.L)
    (hm : IsDysonRootV (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E))
    (a : Fin 1 → Fin p.L) (σ : Fin 1 → Bool) (ω : Ω W p.L) :
    ‖flowErr W p a σ ω‖ = ‖blockTr (flowG W p ω - flowM W p) (a 0) (a 0)‖ := by
  obtain ⟨c, rfl⟩ : ∃ c, a = ![c] := ⟨a 0, by funext i; fin_cases i; rfl⟩
  obtain ⟨s, rfl⟩ : ∃ s, σ = ![s] := ⟨σ 0, by funext i; fin_cases i; rfl⟩
  unfold flowErr
  rw [loopsStep_primLoop_one]
  exact loopsStep_loop_one_sub p.g p.E W p.L hW hL _ hm (flowG W p ω) c s

end One

/-- Lemma 5.6 [fo:prop:inputs], loop errors of length one at each fixed `u ∈ [0, 1/2]`:
`max_{a,σ} |D_1| ≺ ζ_u`, since `D_1(a, +) = ⟨G_u - M⟩_{aa}` and `D_1(a, -)` is its conjugate
(the averaged component of (5.22) [gc:eq:one-step-input]). -/
theorem lemma46_err_one (κ CV : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hCV : 0 < CV) :
    ∃ Cκ₀ : ℝ, 1 ≤ Cκ₀ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      PrecMax (fun p : FlowPt => p.L) (initLarge κ Cκ CV ρ) (Λ := fun _ p => Word 1 p.L)
        (fun W p w ω => flowErr W p w.1 w.2 ω) (fun W p _ => flowZeta W p ^ 1) := by
  obtain ⟨Cκa, hCκa, Ha⟩ := lemma46_avg κ CV hκ hκ2 hCV
  obtain ⟨Cκr, C, hCκr, hC, Hr⟩ := loopsStep_root κ hκ hκ2
  refine ⟨max Cκa Cκr, le_trans hCκa (le_max_left _ _), fun Cκ hCκ ρ hρ => ?_⟩
  intro ε D hε hD
  obtain ⟨W₁, HW₁⟩ := Ha Cκ ((le_max_left _ _).trans hCκ) ρ hρ ε D hε hD
  obtain ⟨W₂, HW₂⟩ := eventually_atTop.1
    ((Hr Cκ ((le_max_right _ _).trans hCκ) ρ hρ 0).and (eventually_ge_atTop 1))
  refine ⟨max W₁ W₂, fun W hW p hp => ?_⟩
  obtain ⟨hR, hW1⟩ := HW₂ W ((le_max_right _ _).trans hW)
  obtain ⟨-, -, hL3, hroot, -, -⟩ := hR CV p hp
  refine (measure_mono ?_).trans (HW₁ W ((le_max_left _ _).trans hW) p hp)
  rintro ω ⟨w, hw⟩
  refine ⟨(w.1 0, w.1 0), ?_⟩
  simp only [pow_one] at hw
  rw [loopsStep_flowErr_one W p hW1 (by omega) hroot w.1 w.2 ω] at hw
  exact hw

end LSBA
