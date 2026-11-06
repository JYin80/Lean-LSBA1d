import LSBA.Transfer.Recurrence
import LSBA.Transfer.Moments
import LSBA.Spectral.ResolventBounds

/-!
# Coarse resolvent moments

The window length (7.4) [uvs:eq:window-length], tails and moments of the arc products, the
coarse moments (7.6) [uvs:eq:coarse-moments], and Lemma 5.5 [fo:lem:resolvent-moments], (5.25)
[fo:eq:coarse-resolvent-moments], at each fixed time `t` for the single-time matrix `blockFlow`
of (5.1) [fo:eq:flow], and for the model (1.3) [eq:model] at `t = 1`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The window length `n = min{⌊(L-1)/2⌋, ⌊g²⌋}` of (7.4) [uvs:eq:window-length]. -/
def coarseN (g : ℝ) (L : ℕ) : ℕ := min ((L - 1) / 2) ⌊g ^ 2⌋₊

/-! ### Arcs on the cycle -/

private theorem coarse_val_finRotate {L : ℕ} (x : Fin L) :
    (finRotate L x).val = (x.val + 1) % L := by
  cases L with
  | zero => exact x.elim0
  | succ n =>
    rw [coe_finRotate]
    by_cases h : x = Fin.last n
    · subst h
      simp
    · simp only [h, ↓reduceIte]
      have : x.val < n := by
        have h1 := x.isLt
        have h2 : x.val ≠ n := fun h' => h (Fin.ext (by simpa using h'))
        omega
      rw [Nat.mod_eq_of_lt (by omega)]

private theorem coarse_pow_val {L : ℕ} (a : Fin L) (j : ℕ) :
    ((finRotate L ^ j) a).val = (a.val + j) % L := by
  induction j with
  | zero => simp [Nat.mod_eq_of_lt a.isLt]
  | succ j ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, coarse_val_finRotate, ih, Nat.mod_add_mod]
    rfl

private theorem coarse_pow_ne_self {L : ℕ} (a : Fin L) {k : ℕ} (hk0 : 0 < k) (hkL : k < L) :
    (finRotate L ^ k) a ≠ a := by
  intro h
  have h1 := congrArg Fin.val h
  rw [coarse_pow_val] at h1
  have h2 := a.isLt
  by_cases h3 : a.val + k < L
  · rw [Nat.mod_eq_of_lt h3] at h1
    omega
  · rw [Nat.mod_eq_sub_mod (not_lt.mp h3), Nat.mod_eq_of_lt (by omega)] at h1
    omega

private theorem coarse_arcBlock_ne_self {L : ℕ} (a : Fin L) (d : Bool) {k : ℕ} (hk0 : 0 < k)
    (hkL : k < L) : arcBlock a d k ≠ a := by
  cases d
  · intro h
    apply coarse_pow_ne_self a hk0 hkL
    have h' : ((finRotate L)⁻¹ ^ k) a = a := h
    have h2 := congrArg (⇑(finRotate L ^ k)) h'
    rw [← Equiv.Perm.mul_apply, inv_pow, mul_inv_cancel, Equiv.Perm.one_apply] at h2
    exact h2.symm
  · exact coarse_pow_ne_self a hk0 hkL

private theorem coarse_arcBlock_add {L : ℕ} (a : Fin L) (d : Bool) (i j : ℕ) :
    arcBlock (arcBlock a d i) d j = arcBlock a d (i + j) := by
  cases d
  · change ((finRotate L)⁻¹ ^ j) (((finRotate L)⁻¹ ^ i) a) = ((finRotate L)⁻¹ ^ (i + j)) a
    rw [add_comm i j, pow_add, Equiv.Perm.mul_apply]
  · change (finRotate L ^ j) ((finRotate L ^ i) a) = (finRotate L ^ (i + j)) a
    rw [add_comm i j, pow_add, Equiv.Perm.mul_apply]

/-- The blocks `a ± 1, …, a ± n` of an arc of `n ≤ L` blocks are distinct. -/
private theorem coarse_arcBlock_injOn {L : ℕ} (a : Fin L) (d : Bool) {n : ℕ} (hn : n ≤ L) :
    Set.InjOn (fun i => arcBlock a d (i + 1)) (Set.Iio n) := by
  have key : ∀ i i' : ℕ, i < i' → i' < n → arcBlock a d (i + 1) ≠ arcBlock a d (i' + 1) := by
    intro i i' hii hi'n h
    have h1 : arcBlock (arcBlock a d (i + 1)) d (i' - i) = arcBlock a d (i + 1) := by
      rw [coarse_arcBlock_add, show i + 1 + (i' - i) = i' + 1 by omega]
      exact h.symm
    exact coarse_arcBlock_ne_self _ d (by omega) (by omega) h1
  intro i hi i' hi' h
  simp only [Set.mem_Iio] at hi hi'
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · exact absurd h (key i i' hlt hi')
  · exact heq
  · exact absurd h.symm (key i' i hgt hi)

/-! ### Continuity in the sample -/

private lemma coarse_continuous_gueBlock {W L : ℕ} (b : Fin L) :
    Continuous fun ω : Ω W L => gueBlock W L ω b := by
  refine continuous_matrix fun α β => ?_
  simp only [gueBlock, Matrix.of_apply]
  split_ifs <;> fun_prop

private lemma coarse_continuous_kronecker_left {W : ℕ} (P : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous fun V : Matrix (Fin W) (Fin W) ℂ => P ⊗ₖ V := by
  refine continuous_matrix fun i j => ?_
  simp only [Matrix.kroneckerMap_apply]
  exact continuous_const.mul (continuous_id.matrix_elem i.2 j.2)

private lemma coarse_continuous_transferInv {W : ℕ} (g : ℝ) (z : ℂ) :
    Continuous fun V : Matrix (Fin W) (Fin W) ℂ => transferInv g z V := by
  unfold transferInv
  exact continuous_const.sub ((continuous_const_smul _).comp (coarse_continuous_kronecker_left _))

private lemma coarse_continuous_transferProd_inv {W L : ℕ} (g : ℝ) (z c : ℂ) (s : ℕ → Fin L)
    (j : ℕ) : Continuous fun ω : Ω W L =>
      (transferProd g z (fun i => c • gueBlock W L ω (s i)) j)⁻¹ := by
  induction j with
  | zero => simpa [transferProd] using continuous_const
  | succ j ih =>
    have heq : ∀ ω : Ω W L, (transferProd g z (fun i => c • gueBlock W L ω (s i)) (j + 1))⁻¹ =
        (transferProd g z (fun i => c • gueBlock W L ω (s i)) j)⁻¹ *
          transferInv g z (c • gueBlock W L ω (s j)) := fun ω => by
      rw [transferProd, Matrix.mul_inv_rev, inv_transferMat]
    refine Continuous.congr ?_ fun ω => (heq ω).symm
    exact ih.mul ((coarse_continuous_transferInv g z).comp
      ((coarse_continuous_gueBlock (s j)).const_smul c))

private lemma coarse_measurable_arcK {W L : ℕ} (g : ℝ) (z c : ℂ) (a : Fin L) (d : Bool)
    (n : ℕ) : Measurable fun ω : Ω W L => arcK g z (fun b => c • gueBlock W L ω b) a d n :=
  Measurable.iSup fun j => (continuous_norm.comp
    (coarse_continuous_transferProd_inv g z c (fun i => arcBlock a d (i + 1)) j)).measurable

/-! ### Tails and moments of `K_a` -/

/-- Tail of `K_a` on an arc of `n ≤ min{L, g²}` blocks, from the inverse-product version of
(7.3) [uvs:eq:transfer-tail]. -/
theorem arcK_tail (κ C₁ : ℝ) (hκ : 0 < κ) (hC₁ : 0 ≤ C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W L : ℕ) (g : ℝ), 2 / Real.sqrt κ ≤ g → ∀ n : ℕ, n ≤ L →
      (n : ℝ) ≤ g ^ 2 → ∀ E η t : ℝ, |E| ≤ 2 - κ → |η| ≤ 1 → (n : ℝ) * |η| ≤ C₁ → 0 ≤ t →
      t ≤ 1 → ∀ (a : Fin L) (d : Bool) (u : ℝ), 0 < u →
      μ W L {ω | u < arcK g (↑E + ↑η * Complex.I)
          (fun b => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω b) a d n} ≤
        ENNReal.ofReal (min 1 ((C / u) ^ W)) := by
  obtain ⟨C, hC0, h⟩ := transfer_inv_tail κ 1 C₁ hκ zero_le_one hC₁
  refine ⟨C, hC0, ?_⟩
  intro W L g hg n hnL hng E η t hE hη hnη ht0 ht1 a d u hu
  refine le_trans (measure_mono ?_) (h W L (fun i => arcBlock a d (i + 1)) n
    (coarse_arcBlock_injOn a d hnL) g hg (by rwa [one_mul]) E η t hE hη hnη ht0 ht1 u hu)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  refine lt_of_lt_of_le hω ?_
  unfold arcK
  refine Real.iSup_le (fun j => ?_) (Real.iSup_nonneg fun _ => norm_nonneg _)
  exact le_ciSup (f := fun j : Fin (n + 1) => ‖(transferProd g (↑E + ↑η * Complex.I)
    (fun i => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω (arcBlock a d (i + 1))) j)⁻¹‖)
    (Finite.bddAbove_range _) (Fin.castSucc j)

/-- Moments of `K_a` on an arc of `n ≤ min{L, g²}` blocks, from (7.1)
[uvs:eq:transfer-moments]. -/
theorem arcK_moments (κ C₁ p : ℝ) (hκ : 0 < κ) (hC₁ : 0 ≤ C₁) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W L : ℕ), 2 * p ≤ W → ∀ g : ℝ, 2 / Real.sqrt κ ≤ g → ∀ n : ℕ, n ≤ L →
      (n : ℝ) ≤ g ^ 2 → ∀ E η t : ℝ, |E| ≤ 2 - κ → |η| ≤ 1 → (n : ℝ) * |η| ≤ C₁ → 0 ≤ t →
      t ≤ 1 → ∀ (a : Fin L) (d : Bool),
      Integrable (fun ω => arcK g (↑E + ↑η * Complex.I)
          (fun b => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω b) a d n ^ p) (μ W L) ∧
      ∫ ω, arcK g (↑E + ↑η * Complex.I)
          (fun b => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω b) a d n ^ p ∂(μ W L) ≤ C := by
  obtain ⟨C, hC0, h⟩ := transfer_moments κ 1 C₁ p hκ zero_le_one hC₁ hp
  refine ⟨C, hC0, ?_⟩
  intro W L hW g hg n hnL hng E η t hE hη hnη ht0 ht1 a d
  obtain ⟨hint, hle⟩ := h W L hW (fun i => arcBlock a d (i + 1)) n
    (coarse_arcBlock_injOn a d hnL) g hg (by rwa [one_mul]) E η t hE hη hnη ht0 ht1
  have hmeas : Measurable fun ω : Ω W L => arcK g (↑E + ↑η * Complex.I)
      (fun b => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω b) a d n ^ p :=
    (coarse_measurable_arcK g _ _ a d n).pow_const p
  have hnn : ∀ ω : Ω W L, 0 ≤ arcK g (↑E + ↑η * Complex.I)
      (fun b => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω b) a d n ^ p := fun ω =>
    Real.rpow_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _) _
  have hpt : ∀ ω : Ω W L, arcK g (↑E + ↑η * Complex.I)
      (fun b => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω b) a d n ^ p ≤
      ⨆ j : Fin (n + 1),
        (‖transferProd g (↑E + ↑η * Complex.I)
            (fun i => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω (arcBlock a d (i + 1))) j‖ ^ p +
          ‖(transferProd g (↑E + ↑η * Complex.I)
            (fun i => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω (arcBlock a d (i + 1))) j)⁻¹‖ ^
              p) := by
    intro ω
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · subst hn0
      rw [arcK, Real.iSup_of_isEmpty, Real.zero_rpow hp.ne']
      exact Real.iSup_nonneg fun _ => by positivity
    · have : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
      obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun j : Fin n =>
        ‖(transferProd g (↑E + ↑η * Complex.I)
          (fun i => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω (arcBlock a d (i + 1))) j)⁻¹‖)
      rw [arcK, ← hj]
      refine le_trans ?_ (le_ciSup (f := fun j : Fin (n + 1) =>
        (‖transferProd g (↑E + ↑η * Complex.I)
            (fun i => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω (arcBlock a d (i + 1))) j‖ ^ p +
          ‖(transferProd g (↑E + ↑η * Complex.I)
            (fun i => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω (arcBlock a d (i + 1))) j)⁻¹‖ ^
              p)) (Finite.bddAbove_range _) (Fin.castSucc j))
      simp only [Fin.val_castSucc]
      exact le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _)
  refine ⟨hint.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun ω => ?_), ?_⟩
  · rw [Real.norm_of_nonneg (hnn ω)]
    exact hpt ω
  · refine (integral_mono_of_nonneg (ae_of_all _ hnn) hint (ae_of_all _ hpt)).trans ?_
    exact hle

/-! ### The resolvent entries at a fixed time -/

/-- A block of a matrix on `ℂ^L ⊗ ℂ^W` has operator norm at most that of the matrix. -/
private lemma coarse_norm_blockOf_le {W L : ℕ}
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) :
    ‖blockOf G a b‖ ≤ ‖G‖ := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  set u : EuclideanSpace ℂ (Fin L × Fin W) :=
    WithLp.toLp 2 (fun x => if x.1 = b then v.ofLp x.2 else 0) with hu
  have h := Matrix.l2_opNorm_mulVec G u
  have hnu : ‖u‖ = ‖v‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
    · simp [hu]
    · intro c _ hc; simp [hu, hc]
    · intro h; exact absurd (Finset.mem_univ b) h
  have key : ‖(Matrix.toEuclideanLin (𝕜 := ℂ) (blockOf G a b)) v‖ ≤
      ‖(EuclideanSpace.equiv (Fin L × Fin W) ℂ).symm (G *ᵥ u)‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    have hentry : ∀ α : Fin W, (Matrix.toEuclideanLin (𝕜 := ℂ) (blockOf G a b)) v α =
        (G *ᵥ ⇑u) (a, α) := by
      intro α
      change (blockOf G a b *ᵥ v.ofLp) α = _
      simp only [Matrix.mulVec, dotProduct, blockOf, Matrix.of_apply, Fintype.sum_prod_type, hu]
      rw [Finset.sum_eq_single b]
      · simp
      · intro c _ hc; simp [hc]
      · intro h; exact absurd (Finset.mem_univ b) h
    calc _ = ∑ α : Fin W, ‖(G *ᵥ ⇑u) (a, α)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [hentry α]
      _ ≤ ∑ c : Fin L, ∑ α : Fin W, ‖(G *ᵥ ⇑u) (c, α)‖ ^ 2 :=
          Finset.single_le_sum (f := fun c : Fin L => ∑ α : Fin W, ‖(G *ᵥ ⇑u) (c, α)‖ ^ 2)
            (fun c _ => Finset.sum_nonneg fun α _ => by positivity) (Finset.mem_univ a)
      _ = _ := by rw [Fintype.sum_prod_type]; rfl
  calc _ ≤ _ := key
    _ ≤ _ := h
    _ = _ := by rw [hnu]

private lemma coarse_hermitian {W L : ℕ} (c : ℝ) (ω : Ω W L) (b : Fin L) :
    (((c : ℝ) : ℂ) • gueBlock W L ω b).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, (gueBlock_isHermitian W L ω b).eq, Complex.star_def,
    Complex.conj_ofReal]

private lemma coarse_continuous_Hdet {W L : ℕ} (g : ℝ) (c : ℂ) :
    Continuous fun ω : Ω W L => Hdet g (fun b => c • gueBlock W L ω b) := by
  have hB : Continuous fun ω : Ω W L => blockDiagOp (fun b => c • gueBlock W L ω b) := by
    refine continuous_matrix fun p q => ?_
    simp only [blockDiagOp, Matrix.of_apply]
    split_ifs
    · exact ((coarse_continuous_gueBlock p.1).const_smul c).matrix_elem p.2 q.2
    · exact continuous_const
  unfold Hdet
  exact Continuous.const_smul (M := ℂ) (continuous_const.add hB) _

/-- The resolvent of `Hdet` with GUE blocks is continuous in the sample off the real axis. -/
private lemma coarse_continuous_resolvent {W L : ℕ} (g t : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    Continuous fun ω : Ω W L =>
      resolventMat (Hdet g (fun b => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω b)) z := by
  have hc : Continuous fun ω : Ω W L =>
      Hdet g (fun b => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω b) - z • (1 : Matrix _ _ ℂ) :=
    (coarse_continuous_Hdet g _).sub continuous_const
  refine continuous_iff_continuousAt.2 fun ω => ?_
  have hu := isUnit_sub_smul_one
    (Hdet_isHermitian g fun b => coarse_hermitian (Real.sqrt t) ω b) hz
  have hdet : (Hdet g (fun b => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω b) -
      z • (1 : Matrix _ _ ℂ)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  refine (continuousAt_matrix_inv _ ?_).comp hc.continuousAt
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ hdet

/-- `‖G_{ab}(E + iη)‖ ≤ η⁻¹` for every sample. -/
private lemma coarse_norm_green_le {W L : ℕ} (g t E η : ℝ) (hη : 0 < η) (a b : Fin L)
    (ω : Ω W L) :
    ‖blockOf (resolventMat (Hdet g (fun c => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω c))
      (↑E + ↑η * Complex.I)) a b‖ ≤ η⁻¹ := by
  refine (coarse_norm_blockOf_le _ a b).trans ?_
  refine norm_resolventMat_le (Hdet_isHermitian g fun c => coarse_hermitian (Real.sqrt t) ω c)
    hη ?_
  simp [abs_of_pos hη]

/-- `ω ↦ ‖G_{ab}(E + iη)‖^p` is integrable for `η > 0`: it is continuous and bounded by
`η⁻¹ ^ p`. -/
private lemma coarse_integrable_green {W L : ℕ} (g t E η p : ℝ) (hη : 0 < η) (hp : 0 < p)
    (a b : Fin L) :
    Integrable (fun ω : Ω W L => ‖blockOf (resolventMat
      (Hdet g (fun c => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω c)) (↑E + ↑η * Complex.I)) a b‖ ^
        p) (μ W L) := by
  have hz : (↑E + ↑η * Complex.I : ℂ).im ≠ 0 := by simpa using hη.ne'
  have h := coarse_continuous_resolvent (W := W) (L := L) g t hz
  have h2 : Continuous fun ω : Ω W L => blockOf (resolventMat
      (Hdet g (fun c => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω c))
        (↑E + ↑η * Complex.I)) a b := by
    refine continuous_matrix fun α β => ?_
    exact (continuous_apply (b, β)).comp ((continuous_apply (a, α)).comp h)
  refine Integrable.of_bound
    (h2.norm.rpow_const fun _ => Or.inr hp.le).aestronglyMeasurable ((η⁻¹) ^ p)
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  exact Real.rpow_le_rpow (norm_nonneg _) (coarse_norm_green_le g t E η hη a b ω) hp.le

/-! ### Coarse moments and Lemma 5.5 [fo:lem:resolvent-moments] -/

private lemma coarse_one_le_g {κ g : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) (hg : 2 / Real.sqrt κ ≤ g) :
    1 ≤ g := by
  have h1 : Real.sqrt κ ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have h2 : 1 ≤ 2 / Real.sqrt κ := (one_le_div (Real.sqrt_pos.mpr hκ)).mpr h1
  exact h2.trans hg

/-- (7.6) [uvs:eq:coarse-moments] at each fixed time `t ∈ [0, 1]`. -/
theorem coarse_moments (κ p C₀ : ℝ) (hκ : 0 < κ) (hp : 0 < p) (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : ℕ, 4 * p ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g : ℝ, 2 / Real.sqrt κ ≤ g →
      ∀ E η t : ℝ, |E| ≤ 2 - κ → 0 < η → η ≤ 1 → (coarseN g L : ℝ) * η ≤ C₀ → 0 ≤ t →
      t ≤ 1 → ∀ a b : Fin L,
      Integrable (fun ω => ‖blockOf (resolventMat (blockFlow W L
          (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) (t * gammaG g) ω) (↑E + ↑η * Complex.I))
          a b‖ ^ p) (μ W L) ∧
      ∫ ω, ‖blockOf (resolventMat (blockFlow W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
          (t * gammaG g) ω) (↑E + ↑η * Complex.I)) a b‖ ^ p ∂(μ W L) ≤
        C * ((coarseN g L : ℝ) * η) ^ (-p) := by
  obtain ⟨CA, hCA0, hA⟩ := arcK_moments κ C₀ (2 * p) hκ hC₀.le (by positivity)
  refine ⟨2 ^ p * CA, by positivity, ?_⟩
  intro W hW L hL g hg E η t hE hη0 hη1 hnη ht0 ht1 a b
  simp only [blockFlow_Ag_eq_Hdet]
  refine ⟨coarse_integrable_green g t E η p hη0 hp a b, ?_⟩
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hg1 : 1 ≤ g := coarse_one_le_g hκ hκ2 hg
  have hg2 : (1 : ℝ) ≤ g ^ 2 := one_le_pow₀ hg1
  set n := coarseN g L with hn
  have hn1 : 1 ≤ n := le_min (by omega) (Nat.le_floor (by simpa using hg2))
  have hn2 : 2 * n + 1 ≤ L := by
    have : n ≤ (L - 1) / 2 := min_le_left _ _
    omega
  have hnL : n ≤ L := by omega
  have hng : (n : ℝ) ≤ g ^ 2 :=
    le_trans (Nat.cast_le.mpr (min_le_right _ _)) (Nat.floor_le (sq_nonneg g))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnη0 : 0 < (n : ℝ) * η := mul_pos hnR hη0
  have hηabs : |η| = η := abs_of_pos hη0
  obtain ⟨hKa, hKa'⟩ := hA W L (by linarith) g hg n hnL hng E η t hE (by rwa [hηabs])
    (by rwa [hηabs]) ht0 ht1 a (arcDir a b n)
  obtain ⟨hKb, hKb'⟩ := hA W L (by linarith) g hg n hnL hng E η t hE (by rwa [hηabs])
    (by rwa [hηabs]) ht0 ht1 b true
  set Ka : Ω W L → ℝ := fun ω => arcK g (↑E + ↑η * Complex.I)
    (fun c => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω c) a (arcDir a b n) n with hKadef
  set Kb : Ω W L → ℝ := fun ω => arcK g (↑E + ↑η * Complex.I)
    (fun c => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω c) b true n with hKbdef
  have hKa0 : ∀ ω, 0 ≤ Ka ω := fun ω => Real.iSup_nonneg fun _ => norm_nonneg _
  have hKb0 : ∀ ω, 0 ≤ Kb ω := fun ω => Real.iSup_nonneg fun _ => norm_nonneg _
  have hsq : ∀ K : ℝ, 0 ≤ K → K ^ (2 * p) = (K ^ p) ^ 2 := fun K hK => by
    rw [mul_comm, Real.rpow_mul hK, Real.rpow_two]
  set c₀ : ℝ := (2 / ((n : ℝ) * η)) ^ p with hc₀
  have hc₀0 : 0 ≤ c₀ := Real.rpow_nonneg (by positivity) _
  have hpt : ∀ ω : Ω W L, ‖blockOf (resolventMat (Hdet g
      (fun c => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω c)) (↑E + ↑η * Complex.I)) a b‖ ^ p ≤
      c₀ * ((Ka ω ^ (2 * p) + Kb ω ^ (2 * p)) / 2) := by
    intro ω
    have h1 := norm_blockOf_resolvent_le (W := W) hL hg1
      (fun c => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω c)
      (fun c => coarse_hermitian (Real.sqrt t) ω c) E hη0 hn1 hn2 a b
    have h2 : ‖blockOf (resolventMat (Hdet g
        (fun c => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω c)) (↑E + ↑η * Complex.I)) a b‖ ^ p ≤
        (2 / ((n : ℝ) * η) * (Ka ω * Kb ω)) ^ p := by
      refine Real.rpow_le_rpow (norm_nonneg _) (h1.trans (le_of_eq ?_)) hp.le
      simp only [hKadef, hKbdef]
      ring
    refine h2.trans ?_
    rw [Real.mul_rpow (by positivity) (mul_nonneg (hKa0 ω) (hKb0 ω)),
      Real.mul_rpow (hKa0 ω) (hKb0 ω), hsq _ (hKa0 ω), hsq _ (hKb0 ω)]
    refine mul_le_mul_of_nonneg_left ?_ hc₀0
    nlinarith [sq_nonneg (Ka ω ^ p - Kb ω ^ p)]
  have hint : Integrable (fun ω : Ω W L => c₀ * ((Ka ω ^ (2 * p) + Kb ω ^ (2 * p)) / 2))
      (μ W L) := (((hKa.add hKb).div_const 2).const_mul c₀)
  have hlow := coarse_integrable_green (W := W) (L := L) g t E η p hη0 hp a b
  have hmain : ∫ ω, ‖blockOf (resolventMat (Hdet g
      (fun c => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω c)) (↑E + ↑η * Complex.I)) a b‖ ^ p
        ∂(μ W L) ≤ c₀ * CA := by
    refine (integral_mono hlow hint hpt).trans ?_
    rw [integral_const_mul, integral_div, integral_add hKa hKb]
    nlinarith [hKa', hKb', hc₀0]
  refine hmain.trans (le_of_eq ?_)
  rw [hc₀, Real.div_rpow (by norm_num) hnη0.le, Real.rpow_neg hnη0.le]
  ring

/-- Lemma 5.5 [fo:lem:resolvent-moments], (5.25) [fo:eq:coarse-resolvent-moments], at each
fixed time `t ∈ [0, 1]`; the thresholds are `W ≥ 4p` and `g ≥ 2 κ^{-1/2}`. -/
theorem resolvent_moments (κ p C₀ : ℝ) (hκ : 0 < κ) (hp : 0 < p) (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : ℕ, 4 * p ≤ W → ∀ L : ℕ, ∀ g : ℝ, 2 / Real.sqrt κ ≤ g →
      4 * g ^ 2 ≤ L → ∀ E η t : ℝ, |E| ≤ 2 - κ → 0 < η → η ≤ C₀ / g ^ 2 → 0 ≤ t → t ≤ 1 →
      ∀ a b : Fin L,
      Integrable (fun ω => ‖blockOf (resolventMat (blockFlow W L
          (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) (t * gammaG g) ω) (↑E + ↑η * Complex.I))
          a b‖ ^ p) (μ W L) ∧
      ∫ ω, ‖blockOf (resolventMat (blockFlow W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
          (t * gammaG g) ω) (↑E + ↑η * Complex.I)) a b‖ ^ p ∂(μ W L) ≤
        C * (g ^ 2 * η) ^ (-p) := by
  obtain ⟨Cc, hCc0, hc⟩ := coarse_moments κ p C₀ hκ hp hC₀
  refine ⟨max (2 ^ p * Cc) (C₀ ^ p), lt_max_of_lt_left (by positivity), ?_⟩
  intro W hW L g hg h4 E η t hE hη0 hηC ht0 ht1 a b
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hg1 : 1 ≤ g := coarse_one_le_g hκ hκ2 hg
  have hg2 : (1 : ℝ) ≤ g ^ 2 := one_le_pow₀ hg1
  have hg0 : (0 : ℝ) < g ^ 2 := lt_of_lt_of_le one_pos hg2
  have hgη : 0 < g ^ 2 * η := mul_pos hg0 hη0
  have hgηC : g ^ 2 * η ≤ C₀ := by
    have := mul_le_mul_of_nonneg_left hηC hg0.le
    rwa [mul_div_cancel₀ _ hg0.ne'] at this
  have hpos : 0 < (g ^ 2 * η) ^ (-p) := Real.rpow_pos_of_pos hgη _
  by_cases hη1 : η ≤ 1
  · -- the window is `n = ⌊g²⌋`
    have hL4 : (4 : ℝ) ≤ L := by linarith
    have hL3 : 3 ≤ L := by
      have : 4 ≤ L := by exact_mod_cast hL4
      omega
    have hm1 : 1 ≤ ⌊g ^ 2⌋₊ := Nat.le_floor (by simpa using hg2)
    have hmg : (⌊g ^ 2⌋₊ : ℝ) ≤ g ^ 2 := Nat.floor_le hg0.le
    have hn : coarseN g L = ⌊g ^ 2⌋₊ := by
      have h4m : 4 * ⌊g ^ 2⌋₊ ≤ L := by
        have : ((4 * ⌊g ^ 2⌋₊ : ℕ) : ℝ) ≤ L := by push_cast; linarith
        exact_mod_cast this
      exact min_eq_right (by omega)
    have hnη : (coarseN g L : ℝ) * η ≤ C₀ := by
      rw [hn]
      exact (mul_le_mul_of_nonneg_right hmg hη0.le).trans hgηC
    obtain ⟨hi, hle⟩ := hc W hW L hL3 g hg E η t hE hη0 hη1 hnη ht0 ht1 a b
    refine ⟨hi, hle.trans ?_⟩
    -- `n ≥ g² / 2`, so `(n η)^{-p} ≤ 2^p (g² η)^{-p}`
    have hhalf : g ^ 2 / 2 ≤ (⌊g ^ 2⌋₊ : ℝ) := by
      have h1 := Nat.lt_floor_add_one (g ^ 2)
      have h2 : (1 : ℝ) ≤ ⌊g ^ 2⌋₊ := by exact_mod_cast hm1
      linarith
    have hnη' : g ^ 2 * η / 2 ≤ (coarseN g L : ℝ) * η := by
      rw [hn]
      calc g ^ 2 * η / 2 = g ^ 2 / 2 * η := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hhalf hη0.le
    have hrp : ((coarseN g L : ℝ) * η) ^ (-p) ≤ (g ^ 2 * η / 2) ^ (-p) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hnη' (by linarith)
    have hrp2 : (g ^ 2 * η / 2) ^ (-p) = 2 ^ p * (g ^ 2 * η) ^ (-p) := by
      rw [Real.div_rpow hgη.le (by norm_num), Real.rpow_neg hgη.le, Real.rpow_neg (by norm_num),
        div_inv_eq_mul, mul_comm, inv_eq_one_div, div_eq_mul_inv]
    calc Cc * ((coarseN g L : ℝ) * η) ^ (-p) ≤ Cc * (2 ^ p * (g ^ 2 * η) ^ (-p)) :=
          mul_le_mul_of_nonneg_left (hrp.trans hrp2.le) hCc0.le
      _ = (2 ^ p * Cc) * (g ^ 2 * η) ^ (-p) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hpos.le
  · -- `1 < η`: the deterministic bound `‖G‖ ≤ η⁻¹`
    have hη1' : 1 < η := not_le.mp hη1
    simp only [blockFlow_Ag_eq_Hdet]
    have hint := coarse_integrable_green (W := W) (L := L) g t E η p hη0 hp a b
    refine ⟨hint, ?_⟩
    have hle : ∀ ω : Ω W L, ‖blockOf (resolventMat (Hdet g
        (fun c => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω c)) (↑E + ↑η * Complex.I)) a b‖ ^ p ≤
        (η⁻¹) ^ p := fun ω =>
      Real.rpow_le_rpow (norm_nonneg _) (coarse_norm_green_le g t E η hη0 a b ω) hp.le
    have hg2C : g ^ 2 ≤ C₀ := by nlinarith
    have hinv : η⁻¹ ≤ C₀ * (g ^ 2 * η)⁻¹ := by
      have : η⁻¹ = g ^ 2 * (g ^ 2 * η)⁻¹ := by field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_right hg2C (inv_nonneg.mpr hgη.le)
    calc ∫ ω, ‖blockOf (resolventMat (Hdet g
          (fun c => ((Real.sqrt t : ℝ) : ℂ) • gueBlock W L ω c)) (↑E + ↑η * Complex.I)) a b‖ ^ p
            ∂(μ W L) ≤ ∫ _ω, (η⁻¹) ^ p ∂(μ W L) := integral_mono hint (integrable_const _) hle
      _ = (η⁻¹) ^ p := by simp
      _ ≤ (C₀ * (g ^ 2 * η)⁻¹) ^ p := Real.rpow_le_rpow (inv_nonneg.mpr hη0.le) hinv hp.le
      _ = C₀ ^ p * (g ^ 2 * η) ^ (-p) := by
          rw [Real.mul_rpow hC₀.le (inv_nonneg.mpr hgη.le), Real.inv_rpow hgη.le,
            Real.rpow_neg hgη.le]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hpos.le

/-- Lemma 5.5 [fo:lem:resolvent-moments] at `t = 1`, for the model (1.3) [eq:model]. -/
theorem resolvent_moments_Hmat (κ p C₀ : ℝ) (hκ : 0 < κ) (hp : 0 < p) (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : ℕ, 4 * p ≤ W → ∀ L : ℕ, ∀ g : ℝ, 2 / Real.sqrt κ ≤ g →
      4 * g ^ 2 ≤ L → ∀ E η : ℝ, |E| ≤ 2 - κ → 0 < η → η ≤ C₀ / g ^ 2 → ∀ a b : Fin L,
      Integrable (fun ω => ‖blockOf (resolventMat (Hmat g W L ω) (↑E + ↑η * Complex.I)) a b‖ ^ p)
        (μ W L) ∧
      ∫ ω, ‖blockOf (resolventMat (Hmat g W L ω) (↑E + ↑η * Complex.I)) a b‖ ^ p ∂(μ W L) ≤
        C * (g ^ 2 * η) ^ (-p) := by
  obtain ⟨C, hC0, h⟩ := resolvent_moments κ p C₀ hκ hp hC₀
  refine ⟨C, hC0, ?_⟩
  intro W hW L g hg h4 E η hE hη hηC a b
  have key := h W hW L g hg h4 E η 1 hE hη hηC zero_le_one le_rfl a b
  simp only [one_mul, ← Hmat_eq_blockFlow] at key
  exact key

end LSBA
