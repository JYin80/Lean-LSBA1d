import LSBA.Transfer.Moments

/-!
# The transfer weight of a block sequence

`K(E) = max_{0 ≤ j ≤ n} max{1, ‖F_j(E)‖, ‖F_j(E)⁻¹‖}` for the prefix products `F_j` of the transfer
matrices of Definition 7.1 [def:transfer-matrices]; for the blocks of a cell this is the weight
`K_A` of Appendix E.1 [app:fr-concentration-proof]. Its elementary bounds, its behaviour when every
block is shifted by a multiple of the identity, and its moments from Lemma 7.2
[uvs:lem:transfer-moments] for `n ≤ 2g²`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- `K(E) = max_{0 ≤ j ≤ n} max{1, ‖F_j‖, ‖F_j⁻¹‖}` with `F_j = T(V_{j-1}) ⋯ T(V_0)` at the
transfer energy `max{1,g} E / g` (Appendix E.1 [app:fr-concentration-proof]). -/
def transferWeight (g E : ℝ) {W : ℕ} (V : ℕ → Matrix (Fin W) (Fin W) ℂ) (n : ℕ) : ℝ :=
  (⨆ j : Fin (n + 1), max 1 (max ‖transferProd g ((max 1 g * E / g : ℝ) : ℂ) V j‖
    ‖(transferProd g ((max 1 g * E / g : ℝ) : ℂ) V j)⁻¹‖))

/-- `K ≥ 1`, and `‖F_j‖, ‖F_j⁻¹‖ ≤ K` for `j ≤ n`. -/
theorem transferWeight_bounds (g E : ℝ) {W : ℕ} (V : ℕ → Matrix (Fin W) (Fin W) ℂ) (n : ℕ) :
    1 ≤ transferWeight g E V n ∧ ∀ j ≤ n,
      ‖transferProd g ((max 1 g * E / g : ℝ) : ℂ) V j‖ ≤ transferWeight g E V n ∧
        ‖(transferProd g ((max 1 g * E / g : ℝ) : ℂ) V j)⁻¹‖ ≤ transferWeight g E V n := by
  unfold transferWeight
  have hbdd := Finite.bddAbove_range (fun j : Fin (n + 1) =>
    max 1 (max ‖transferProd g ((max 1 g * E / g : ℝ) : ℂ) V j‖
      ‖(transferProd g ((max 1 g * E / g : ℝ) : ℂ) V j)⁻¹‖))
  refine ⟨le_ciSup_of_le hbdd 0 (le_max_left _ _), fun j hj => ?_⟩
  have h := le_ciSup hbdd ⟨j, Nat.lt_succ_of_le hj⟩
  exact ⟨le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h,
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h⟩

/-- Shifting every block by `s I` moves the energy to `E − s/max{1,g}`. -/
theorem transferWeight_add_smul_one {g : ℝ} (hg : 0 < g) (E s : ℝ) {W : ℕ}
    (V : ℕ → Matrix (Fin W) (Fin W) ℂ) (n : ℕ) :
    transferWeight g E (fun j => V j + (s : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)) n =
      transferWeight g (E - s / max 1 g) V n := by
  have hc : (0 : ℝ) < max 1 g := lt_max_of_lt_left one_pos
  have hg' : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  have hmat : ∀ (z : ℂ) (V : Matrix (Fin W) (Fin W) ℂ),
      transferMat g z (V + (s : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)) =
        transferMat g (z - ((s / g : ℝ) : ℂ)) V := by
    intro z V
    ext ⟨a, i⟩ ⟨b, j⟩
    fin_cases a <;> fin_cases b <;>
      simp [transferMat, transferFree, Matrix.kroneckerMap_apply, Matrix.one_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      by_cases h : i = j <;> simp [h] <;> field_simp <;> ring
  have hprod : ∀ (z : ℂ) (j : ℕ),
      transferProd g z (fun i => V i + (s : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)) j =
        transferProd g (z - ((s / g : ℝ) : ℂ)) V j := by
    intro z j
    induction j with
    | zero => simp [transferProd]
    | succ j ih => rw [transferProd, transferProd, ih, hmat]
  have hE : max 1 g * E / g - s / g = max 1 g * (E - s / max 1 g) / g := by
    field_simp
  unfold transferWeight
  congr 1
  ext j
  rw [hprod, ← Complex.ofReal_sub, hE]

/-- Lemma 7.2 [uvs:lem:transfer-moments] for the weight: `𝔼 K(E)^p ≤ C` along any injective block
sequence, for `W ≥ 2p`, `g ≥ 2/√κ`, `n ≤ 2g²` and `|E| ≤ 2 − κ`. -/
theorem transferWeight_moment {κ p : ℝ} (hκ : 0 < κ) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W L : ℕ), 2 * p ≤ W → ∀ (s : ℕ → Fin L) (n : ℕ),
      Set.InjOn s (Set.Iio n) → ∀ g : ℝ, 2 / Real.sqrt κ ≤ g → (n : ℝ) ≤ 2 * g ^ 2 →
      ∀ E : ℝ, |E| ≤ 2 - κ →
        ∫⁻ ω, ENNReal.ofReal (transferWeight g E (fun i => gueBlock W L ω (s i)) n ^ p)
          ∂(μ W L) ≤ ENNReal.ofReal C := by
  obtain ⟨C₁, hC₁, h⟩ := transfer_moments κ 2 0 p hκ (by norm_num) le_rfl hp
  refine ⟨1 + C₁, by linarith, ?_⟩
  intro W L hW s n hs g hg hn E hE
  have hpow : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (max 1 (max a b)) ^ p ≤ 1 + (a ^ p + b ^ p) := by
    intro a b ha hb
    have h1 : 0 ≤ a ^ p := Real.rpow_nonneg ha p
    have h2 : 0 ≤ b ^ p := Real.rpow_nonneg hb p
    rcases max_choice 1 (max a b) with h | h
    · rw [h, Real.one_rpow]; linarith
    · rw [h]
      rcases max_choice a b with h' | h'
      · rw [h']; linarith
      · rw [h']; linarith
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hsq : Real.sqrt κ ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hsq0 : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hg1 : 1 ≤ g := le_trans ((le_div_iff₀ hsq0).mpr (by linarith)) hg
  have hg0 : 0 < g := by linarith
  have hmax : max 1 g = g := max_eq_right hg1
  have hz : ((max 1 g * E / g : ℝ) : ℂ) = (E : ℂ) := by
    rw [hmax]; congr 1; field_simp
  obtain ⟨hint, hle⟩ := h W L hW s n hs g hg (by linarith) E 0 1 hE (by simp) (by simp) zero_le_one
    le_rfl
  simp only [Real.sqrt_one, Complex.ofReal_one, one_smul, Complex.ofReal_zero, zero_mul,
    add_zero] at hint hle
  simp only [transferWeight, hz]
  set S : Ω W L → ℝ := fun ω => ⨆ j : Fin (n + 1),
    (‖transferProd g (E : ℂ) (fun i => gueBlock W L ω (s i)) j‖ ^ p +
      ‖(transferProd g (E : ℂ) (fun i => gueBlock W L ω (s i)) j)⁻¹‖ ^ p) with hS
  have hS0 : ∀ ω, 0 ≤ S ω := fun ω => Real.iSup_nonneg fun j => by positivity
  have hpt : ∀ ω, (⨆ j : Fin (n + 1), max 1 (max
      ‖transferProd g (E : ℂ) (fun i => gueBlock W L ω (s i)) j‖
      ‖(transferProd g (E : ℂ) (fun i => gueBlock W L ω (s i)) j)⁻¹‖)) ^ p ≤ 1 + S ω := by
    intro ω
    obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun j : Fin (n + 1) => max 1 (max
      ‖transferProd g (E : ℂ) (fun i => gueBlock W L ω (s i)) j‖
      ‖(transferProd g (E : ℂ) (fun i => gueBlock W L ω (s i)) j)⁻¹‖))
    rw [← hj]
    refine le_trans (hpow _ _ (norm_nonneg _) (norm_nonneg _)) ?_
    have := le_ciSup (Finite.bddAbove_range (fun j : Fin (n + 1) =>
      ‖transferProd g (E : ℂ) (fun i => gueBlock W L ω (s i)) j‖ ^ p +
        ‖(transferProd g (E : ℂ) (fun i => gueBlock W L ω (s i)) j)⁻¹‖ ^ p)) j
    linarith
  have hI : Integrable (fun ω => 1 + S ω) (μ W L) := (integrable_const 1).add hint
  calc ∫⁻ ω, ENNReal.ofReal ((⨆ j : Fin (n + 1), max 1 (max
        ‖transferProd g (E : ℂ) (fun i => gueBlock W L ω (s i)) j‖
        ‖(transferProd g (E : ℂ) (fun i => gueBlock W L ω (s i)) j)⁻¹‖)) ^ p) ∂(μ W L)
      ≤ ∫⁻ ω, ENNReal.ofReal (1 + S ω) ∂(μ W L) :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal (∫ ω, (1 + S ω) ∂(μ W L)) :=
        (ofReal_integral_eq_lintegral_ofReal hI
          (ae_of_all _ fun ω => show 0 ≤ 1 + S ω by linarith [hS0 ω])).symm
    _ ≤ ENNReal.ofReal (1 + C₁) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_add (integrable_const 1) hint]
        simp only [integral_const, smul_eq_mul, probReal_univ, one_mul]
        linarith

end LSBA
