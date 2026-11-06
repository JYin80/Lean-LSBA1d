import LSBA.Volume.Poisson
import LSBA.Volume.LocalComparison
import LSBA.Model.Scales
import LSBA.Spectral.SimpleSpectrum
import LSBA.Spectral.Measurability

/-!
# Resolvent moments imply spreading, with volume extension

Theorem 2.2 [uv:lem:lower-volume]: bounded moments of `Im G_xx` on the cycle of
`L_c = min{L, 2R + 1}` blocks at height `η_c` give the bound (2.7) [uv:eq:lower-volume-output]
on the expected number of eigenvectors with short localization length on the cycle of `L`
blocks. The law of the window blocks and Theorem 4.1 [uv:thm:smooth-cutoff] transfer the
moments from `L_c` to `L`; Lemma 4.2 [uv:lem:poisson] turns them into the count.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- Coordinates of the window blocks `[a - R, a + R]`. -/
def windowCoord {W L : ℕ} (a : Fin L) (R : ℕ) (ω : Ω W L) : Ω W (2 * R + 1) :=
  fun x => ω (windowBlock a R x.1, x.2)

theorem gueBlock_windowCoord {W L : ℕ} (a : Fin L) (R : ℕ) (ω : Ω W L) :
    gueBlock W (2 * R + 1) (windowCoord a R ω) = windowBlocks (gueBlock W L ω) a R := by
  funext j
  rfl

/-- The window blocks have the law of the GUE blocks on the cycle of `2R + 1` blocks. -/
theorem measurePreserving_windowCoord {W L : ℕ} (a : Fin L) (R : ℕ) (hRL : 2 * R + 1 ≤ L) :
    MeasurePreserving (windowCoord (W := W) a R) (μ W L) (μ W (2 * R + 1)) := by
  set e : Fin (2 * R + 1) × Fin W × Fin W → Fin L × Fin W × Fin W :=
    fun x => (windowBlock a R x.1, x.2) with he
  have hinj : Function.Injective e := by
    intro x y hxy
    simp only [he, Prod.mk.injEq] at hxy
    exact Prod.ext (windowBlock_injective a R hRL hxy.1) hxy.2
  have hmeas : Measurable (windowCoord (W := W) a R : Ω W L → Ω W (2 * R + 1)) :=
    measurable_pi_iff.mpr fun x => measurable_pi_apply _
  refine ⟨hmeas, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  let t : Fin L × Fin W × Fin W → Set ℝ := fun y => {u | ∀ x, e x = y → u ∈ s x}
  have ht : ∀ x, t (e x) = s x := by
    intro x
    ext u
    exact ⟨fun h => h x rfl, fun h x' hx' => hinj hx' ▸ h⟩
  have hpre : windowCoord a R ⁻¹' Set.univ.pi s = Set.univ.pi t := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h y x hx
      rw [← hx]
      exact h x
    · intro h x
      exact h (e x) x rfl
  rw [hpre, μ, Measure.pi_pi]
  symm
  refine Fintype.prod_of_injective e hinj _ _ (fun y hy => ?_) (fun x => by rw [ht])
  have hty : t y = Set.univ :=
    Set.eq_univ_of_forall fun u x hx => absurd ⟨x, hx⟩ hy
  rw [hty, measure_univ]

/-- `R = ⌈2/η⌉` with `η = W^ν / ℓ_{W,g}`, (2.5) [uv:eq:lower-volume-scales]. -/
def volR (W : ℕ) (g ν : ℝ) : ℕ := ⌈2 / ((W : ℝ) ^ ν / ellScale W g)⌉₊

/-- The cycle length `L_c = min{L, 2R + 1}` of Theorem 2.2 [uv:lem:lower-volume]. -/
def volLc (W L : ℕ) (g ν : ℝ) : ℕ := min L (2 * volR W g ν + 1)

/-- The moment height `η_c = W^ν / ℓ_{W,g,L_c}` of Theorem 2.2 [uv:lem:lower-volume]. -/
def volEta (W L : ℕ) (g ν : ℝ) : ℝ := (W : ℝ) ^ ν / ellStar W (volLc W L g ν) g

/-- The model (1.3) [eq:model] depends continuously on the sample. -/
private lemma lowerVolume_continuous_Hmat (g : ℝ) (W L : ℕ) : Continuous (Hmat g W L) := by
  refine continuous_matrix fun p q => ?_
  simp only [Hmat, Hdet, gueBlock, blockDiagOp, Matrix.smul_apply, Matrix.add_apply,
    Matrix.of_apply, smul_eq_mul]
  split_ifs <;> fun_prop

/-- `(ω, E) ↦ Im G_xx(E + iη)` is continuous for `η ≠ 0`. -/
private lemma lowerVolume_continuous_im (g : ℝ) (W L : ℕ) {η : ℝ} (hη : η ≠ 0)
    (x : Fin L × Fin W) :
    Continuous fun q : Ω W L × ℝ =>
      (resolventMat (Hmat g W L q.1) (q.2 + η * Complex.I) x x).im := by
  have hdet : ∀ q : Ω W L × ℝ, (Hmat g W L q.1 - ((q.2 : ℂ) + η * Complex.I) •
      (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)).det ≠ 0 :=
    fun q => Matrix.det_ne_zero_of_right_inverse
      (sub_smul_mul_resolventMat (Hmat_isHermitian g W L q.1) (by simpa using hη))
  have hM : Continuous fun q : Ω W L × ℝ => Hmat g W L q.1 - ((q.2 : ℂ) + η * Complex.I) •
      (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :=
    ((lowerVolume_continuous_Hmat g W L).comp continuous_fst).sub
      (((Complex.continuous_ofReal.comp continuous_snd).add continuous_const).smul
        continuous_const)
  simp only [resolventMat, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact Complex.continuous_im.comp
    ((hM.matrix_det.inv₀ hdet).mul (hM.matrix_adjugate.matrix_elem x x))

/-- `0 ≤ Im G_xx(E + iη) ≤ 1/η` for a Hermitian matrix and `η > 0`. -/
private lemma lowerVolume_im_bounds {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (E : ℝ) {η : ℝ} (hη : 0 < η) (x : n) :
    0 ≤ (resolventMat A (E + η * Complex.I) x x).im ∧
      (resolventMat A (E + η * Complex.I) x x).im ≤ 1 / η := by
  have h0 : 0 ≤ (resolventMat A (E + η * Complex.I) x x).im := by
    rw [im_resolventMat_diag hA E hη.ne' x]
    exact Finset.sum_nonneg fun k _ => by positivity
  refine ⟨h0, ?_⟩
  set y := (resolventMat A (E + η * Complex.I) x x).im with hy
  have hw := ward hA E hη.ne' x
  have h1 : y ^ 2 ≤ ‖resolventMat A (E + η * Complex.I) x x‖ ^ 2 :=
    pow_le_pow_left₀ h0 (Complex.abs_im_le_norm _ |>.trans' (le_abs_self _)) 2
  have h2 : ‖resolventMat A (E + η * Complex.I) x x‖ ^ 2 ≤
      ∑ y', ‖resolventMat A (E + η * Complex.I) x y'‖ ^ 2 :=
    Finset.single_le_sum (f := fun y' => ‖resolventMat A (E + η * Complex.I) x y'‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ x)
  rw [hw, ← hy] at h2
  have h3 : η * y ^ 2 ≤ y := by
    have := mul_le_mul_of_nonneg_left (h1.trans h2) hη.le
    rwa [mul_div_cancel₀ _ hη.ne'] at this
  rw [le_div_iff₀ hη]
  nlinarith

/-- Boundedness and continuity make `Y^p` integrable, with `Y = Im G_xx(E + iη)` read along a
continuous map into `Ω W L × ℝ`. -/
private lemma lowerVolume_integrable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] {m : Measure X} [IsFiniteMeasure m] (g : ℝ) (W L : ℕ) {η : ℝ}
    (hη : 0 < η) (x : Fin L × Fin W) {p : ℝ} (hp : 0 ≤ p) {φ : X → Ω W L × ℝ}
    (hφ : Continuous φ) :
    Integrable (fun y => ((resolventMat (Hmat g W L (φ y).1) ((φ y).2 + η * Complex.I) x x).im)
      ^ p) m := by
  have hc : Continuous fun y => ((resolventMat (Hmat g W L (φ y).1)
      ((φ y).2 + η * Complex.I) x x).im) ^ p :=
    ((lowerVolume_continuous_im g W L hη.ne' x).comp hφ).rpow_const fun _ => Or.inr hp
  refine Integrable.of_bound hc.aestronglyMeasurable ((1 / η) ^ p) (ae_of_all _ fun y => ?_)
  obtain ⟨h0, h1⟩ := lowerVolume_im_bounds (Hmat_isHermitian g W L (φ y).1) (φ y).2 hη x
  rw [Real.norm_of_nonneg (Real.rpow_nonneg h0 _)]
  exact Real.rpow_le_rpow h0 h1 hp

/-- Markov's step: `y 1{y > t} ≤ t^{1-p} y^p` for `y ≥ 0`, `t > 0`, `p ≥ 1`. -/
private lemma lowerVolume_markov {t y p : ℝ} (ht : 0 < t) (hy : 0 ≤ y) (hp : 1 ≤ p) :
    (if t < y then y else 0) ≤ t ^ (1 - p) * y ^ p := by
  split_ifs with h
  · have hy0 : 0 < y := ht.trans h
    calc y = y ^ p * y ^ (1 - p) := by
          rw [← Real.rpow_add hy0, add_sub_cancel, Real.rpow_one]
      _ ≤ y ^ p * t ^ (1 - p) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ht h.le (by linarith))
            (Real.rpow_nonneg hy _)
      _ = t ^ (1 - p) * y ^ p := mul_comm _ _
  · exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg hy _)

/-- Theorem 2.2 [uv:lem:lower-volume]: the moment bound (2.6) [uv:eq:lower-volume-moment] on
the cycle of `L_c` blocks implies (2.7) [uv:eq:lower-volume-output] on the cycle of `L`
blocks, with a threshold depending only on `E₀, D, τ, ν, p, C_p`. -/
theorem lower_volume (E₀ D τ ν p Cp : ℝ) (hE₀ : 0 < E₀) (hD : 0 < D) (hτ : 0 < τ ∧ τ < 1)
    (hν : 0 < ν ∧ ν < τ / 2) (hp : 1 + (D + 1) / (τ - ν) < p) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g : ℝ, 0 ≤ g → ∀ c d : ℝ, -E₀ ≤ c →
      d ≤ E₀ →
      (∀ E ∈ Set.Icc (c - volEta W L g ν) (d + volEta W L g ν),
        ∀ x : Fin (volLc W L g ν) × Fin W,
          ∫ ω, ((resolventMat (Hmat g W (volLc W L g ν) ω)
              (E + volEta W L g ν * Complex.I) x x).im) ^ p ∂(μ W (volLc W L g ν)) ≤ Cp) →
      ((W : ℝ) * L)⁻¹ * ∫ ω, (badCount W L (Hmat g W L ω) (Set.Icc c d)
          ((W : ℝ) ^ (-τ) * ellStar W L g) : ℝ) ∂(μ W L) ≤ (W : ℝ) ^ (-D) := by
  obtain ⟨hτ0, hτ1⟩ := hτ
  obtain ⟨hν0, hντ⟩ := hν
  have hτν : 0 < τ - ν := by linarith
  have hp1 : 1 < p := by
    have : 0 < (D + 1) / (τ - ν) := div_pos (by linarith) hτν
    linarith
  have hexp : D + 1 < (p - 1) * (τ - ν) := by
    have : (D + 1) / (τ - ν) < p - 1 := by linarith
    rwa [div_lt_iff₀ hτν] at this
  set Cp' := max Cp 0 with hCp'
  have hCp'0 : 0 ≤ Cp' := le_max_right _ _
  set K : ℝ := 8 / π * (2 * E₀ + 2) * 3 ^ p * Cp' * 8 ^ (p - 1) with hK
  refine ⟨max 2 ⌈K⌉₊, fun W hW L hL g hg c d hc hd hmom => ?_⟩
  have hW2 : (2 : ℝ) ≤ W := by exact_mod_cast le_trans (le_max_left _ _) hW
  have hWK : K ≤ W := le_trans (Nat.le_ceil K) (by exact_mod_cast le_trans (le_max_right _ _) hW)
  have hW0 : (0 : ℝ) < W := by linarith
  have hW1 : (1 : ℝ) ≤ W := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hWν : (W : ℝ) ^ ν ≤ W := by
    calc (W : ℝ) ^ ν ≤ (W : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
      _ = W := Real.rpow_one _
  have hWν0 : 0 < (W : ℝ) ^ ν := Real.rpow_pos_of_pos hW0 _
  -- the scales on the cycle of `L` blocks
  set ℓ := ellStar W L g with hℓ
  have hℓW : (W : ℝ) ≤ ℓ :=
    le_min (le_mul_of_one_le_right hW0.le hL1) (le_max_left _ _)
  have hℓ0 : 0 < ℓ := hW0.trans_le hℓW
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = (W : ℝ) ^ ν / ℓ := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  have hη1 : η ≤ 1 := by
    rw [hη, div_le_one hℓ0]
    exact hWν.trans hℓW
  have h3p : 1 ≤ (3 : ℝ) ^ p := Real.one_le_rpow (by norm_num) (by linarith)
  -- the moment bound on the cycle of `L` blocks
  have hmomL : ∀ E ∈ Set.Icc (c - η) (d + η), ∀ x : Fin L × Fin W,
      ∫ ω, ((resolventMat (Hmat g W L ω) (E + η * Complex.I) x x).im) ^ p ∂(μ W L) ≤
        3 ^ p * Cp' := by
    have hEta : volEta W L g ν = (W : ℝ) ^ ν / ellStar W (volLc W L g ν) g := rfl
    rw [hEta] at hmom
    generalize hLc : volLc W L g ν = Lc at hmom
    have hLc' : min L (2 * volR W g ν + 1) = Lc := hLc
    have hC : Cp ≤ 3 ^ p * Cp' :=
      (le_max_left _ _).trans (le_mul_of_one_le_left hCp'0 h3p)
    by_cases hLR : L ≤ 2 * volR W g ν + 1
    · rw [min_eq_left hLR] at hLc'
      subst hLc'
      intro E hE x
      rw [hη] at hE ⊢
      exact (hmom E hE x).trans hC
    · replace hLR := not_le.mp hLR
      rw [min_eq_right hLR.le] at hLc'
      subst hLc'
      set R := volR W g ν with hRdef
      have hℓ₀W : (W : ℝ) ≤ ellScale W g := le_max_left _ _
      have hℓ₀ : 0 < ellScale W g := hW0.trans_le hℓ₀W
      have hη₀ : 0 < (W : ℝ) ^ ν / ellScale W g := by positivity
      have hR2 : 2 / ((W : ℝ) ^ ν / ellScale W g) ≤ R := Nat.le_ceil _
      have hR1 : 1 ≤ R := Nat.one_le_iff_ne_zero.mpr fun h => by
        rw [h, Nat.cast_zero] at hR2
        have : 0 < 2 / ((W : ℝ) ^ ν / ellScale W g) := by positivity
        linarith
      have hηR : 2 ≤ (W : ℝ) ^ ν / ellScale W g * R := by
        rw [div_le_iff₀ hη₀] at hR2
        linarith
      have hRW : 2 * ellScale W g ≤ R * (W : ℝ) ^ ν := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hℓ₀] at hηR
        linarith
      have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
      have hWc : ellScale W g ≤ (W : ℝ) * ((2 * R + 1 : ℕ) : ℝ) := by
        push_cast
        nlinarith [mul_le_mul_of_nonneg_left hWν hR0]
      have hWL : (W : ℝ) * ((2 * R + 1 : ℕ) : ℝ) ≤ (W : ℝ) * L :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hLR.le) hW0.le
      have hsc : ellStar W (2 * R + 1) g = ellScale W g := min_eq_right hWc
      have hsL : ℓ = ellScale W g := min_eq_right (hWc.trans hWL)
      rw [hsc] at hmom
      have hηe : η = (W : ℝ) ^ ν / ellScale W g := by rw [hη, hsL]
      rw [← hηe] at hmom hηR
      intro E hE x
      obtain ⟨a, α⟩ := x
      have hmp := measurePreserving_windowCoord (W := W) a R hLR.le
      have hz : 0 < ((E : ℂ) + η * Complex.I).im := by simpa using hη0
      have hzR : 2 ≤ ((E : ℂ) + η * Complex.I).im * R := by simpa using hηR
      have key : ∀ ω : Ω W L,
          (resolventMat (Hmat g W L ω) (E + η * Complex.I) (a, α) (a, α)).im ≤
            3 * (resolventMat (Hmat g W (2 * R + 1) (windowCoord a R ω)) (E + η * Complex.I)
              (windowCenter R, α) (windowCenter R, α)).im := by
        intro ω
        have := im_resolvent_diag_le_window g hg (gueBlock W L ω) (gueBlock_isHermitian W L ω)
          a R hR1 hLR (E + η * Complex.I) hz hzR α
        rw [Hmat, Hmat, gueBlock_windowCoord]
        exact this
      have hcw : Continuous (windowCoord (W := W) a R : Ω W L → Ω W (2 * R + 1)) :=
        continuous_pi fun _ => continuous_apply _
      have hint := (lowerVolume_integrable (m := μ W L) g W (2 * R + 1) hη0 (windowCenter R, α)
        (by linarith : (0 : ℝ) ≤ p) (φ := fun ω => (windowCoord a R ω, E))
        (hcw.prodMk continuous_const)).const_mul ((3 : ℝ) ^ p)
      have hmap := integral_map (μ := μ W L) hmp.measurable.aemeasurable
        (f := fun ω' : Ω W (2 * R + 1) => ((resolventMat (Hmat g W (2 * R + 1) ω')
          (E + η * Complex.I) (windowCenter R, α) (windowCenter R, α)).im) ^ p)
        (by
          rw [hmp.map_eq]
          exact (lowerVolume_integrable (m := μ W (2 * R + 1)) g W (2 * R + 1) hη0
            (windowCenter R, α) (by linarith : (0 : ℝ) ≤ p) (φ := fun ω' => (ω', E))
            (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
      rw [hmp.map_eq] at hmap
      calc ∫ ω, ((resolventMat (Hmat g W L ω) (E + η * Complex.I) (a, α) (a, α)).im) ^ p
            ∂(μ W L)
          ≤ ∫ ω, (3 : ℝ) ^ p * ((resolventMat (Hmat g W (2 * R + 1) (windowCoord a R ω))
              (E + η * Complex.I) (windowCenter R, α) (windowCenter R, α)).im) ^ p
            ∂(μ W L) := by
            refine integral_mono_of_nonneg (ae_of_all _ fun ω => Real.rpow_nonneg
              (lowerVolume_im_bounds (Hmat_isHermitian g W L ω) E hη0 _).1 _) hint
              (ae_of_all _ fun ω => ?_)
            have h0 := (lowerVolume_im_bounds (Hmat_isHermitian g W L ω) E hη0 (a, α)).1
            have h0' := (lowerVolume_im_bounds (Hmat_isHermitian g W (2 * R + 1)
              (windowCoord a R ω)) E hη0 (windowCenter R, α)).1
            dsimp only
            rw [← Real.mul_rpow (by norm_num) h0']
            exact Real.rpow_le_rpow h0 (key ω) (by linarith)
        _ = (3 : ℝ) ^ p * ∫ ω', ((resolventMat (Hmat g W (2 * R + 1) ω')
              (E + η * Complex.I) (windowCenter R, α) (windowCenter R, α)).im) ^ p
            ∂(μ W (2 * R + 1)) := by
            rw [integral_const_mul, hmap]
        _ ≤ 3 ^ p * Cp' := by
            refine mul_le_mul_of_nonneg_left ((hmom E ?_ (windowCenter R, α)).trans
              (le_max_left _ _)) (by positivity)
            exact hE
  -- the count on the cycle of `L` blocks
  set r : ℝ := (W : ℝ) ^ (-τ) * ℓ with hr
  have hr0 : 0 < r := mul_pos (Real.rpow_pos_of_pos hW0 _) hℓ0
  set h : ℝ := 1 / (4 * r) with hh
  have hh0 : 0 < h := by positivity
  set t : ℝ := h / (2 * η) with htdef
  have ht0 : 0 < t := by positivity
  set I := Set.Icc (c - η) (d + η) with hI
  have hcount : ∀ᵐ ω ∂(μ W L), (badCount W L (Hmat g W L ω) (Set.Icc c d) r : ℝ) ≤
      (8 / π * t ^ (1 - p)) * ∑ x : Fin L × Fin W, ∫ E in I,
        ((resolventMat (Hmat g W L ω) (E + η * Complex.I) x x).im) ^ p := by
    filter_upwards [ae_injective_eigenvalues g W L] with ω hω
    have hA := Hmat_isHermitian g W L ω
    refine (badCount_le_four_mul_heavy hA hω (Set.Icc c d) hr0).trans ?_
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    refine le_trans (le_of_eq ?_) ((mul_le_mul_of_nonneg_left
      (sum_heavy_le_integral_im_resolventMat hA x hη0 hh0 c d) (by norm_num : (0 : ℝ) ≤ 4)).trans
        ?_)
    · congr 1
      rw [Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases h1 : hA.eigenvalues k ∈ Set.Icc c d <;>
        by_cases h2 : h < ‖hA.eigenvectorBasis k x‖ ^ 2 <;>
        simp only [Set.indicator_apply, Set.mem_ofPred_eq, ← hh, h1, h2, and_self, and_true,
          and_false, ↓reduceIte]
    have hgi := (lowerVolume_integrable (m := volume.restrict I) g W L hη0 x
      (by linarith : (0 : ℝ) ≤ p) (φ := fun E => (ω, E))
      (continuous_const.prodMk continuous_id)).const_mul (t ^ (1 - p))
    calc 4 * (2 / π * ∫ E in I, Set.indicator
            {E : ℝ | t < (resolventMat (Hmat g W L ω) (E + η * Complex.I) x x).im}
            (fun E : ℝ => (resolventMat (Hmat g W L ω) (E + η * Complex.I) x x).im) E)
        = 8 / π * ∫ E in I, Set.indicator
            {E : ℝ | t < (resolventMat (Hmat g W L ω) (E + η * Complex.I) x x).im}
            (fun E : ℝ => (resolventMat (Hmat g W L ω) (E + η * Complex.I) x x).im) E := by ring
      _ ≤ 8 / π * ∫ E in I, t ^ (1 - p) *
            ((resolventMat (Hmat g W L ω) (E + η * Complex.I) x x).im) ^ p := by
          refine mul_le_mul_of_nonneg_left (integral_mono_of_nonneg (ae_of_all _ fun E =>
            Set.indicator_nonneg (fun E _ => (lowerVolume_im_bounds hA E hη0 x).1) _) hgi
            (ae_of_all _ fun E => ?_)) (by positivity)
          simp only [Set.indicator_apply, Set.mem_ofPred_eq]
          exact lowerVolume_markov ht0 (lowerVolume_im_bounds hA E hη0 x).1 hp1.le
      _ = 8 / π * t ^ (1 - p) * ∫ E in I,
            ((resolventMat (Hmat g W L ω) (E + η * Complex.I) x x).im) ^ p := by
          rw [integral_const_mul]
          ring
  have hint : ∀ x : Fin L × Fin W, Integrable (fun q : Ω W L × ℝ =>
      ((resolventMat (Hmat g W L q.1) (q.2 + η * Complex.I) x x).im) ^ p)
      ((μ W L).prod (volume.restrict I)) := fun x =>
    lowerVolume_integrable g W L hη0 x (by linarith) continuous_id
  have hmomI : ∀ x : Fin L × Fin W, ∫ E in I, ∫ ω,
      ((resolventMat (Hmat g W L ω) (E + η * Complex.I) x x).im) ^ p ∂(μ W L) ≤
        ∫ E in I, (3 : ℝ) ^ p * Cp' := fun x =>
    setIntegral_mono_on (hint x).integral_prod_right (integrable_const _) measurableSet_Icc
      fun E hE => hmomL E hE x
  have hbad : Integrable (fun ω => (8 / π * t ^ (1 - p)) * ∑ x : Fin L × Fin W, ∫ E in I,
      ((resolventMat (Hmat g W L ω) (E + η * Complex.I) x x).im) ^ p) (μ W L) :=
    (integrable_finsetSum _ fun x _ => (hint x).integral_prod_left).const_mul _
  have hswap : ∀ x : Fin L × Fin W, ∫ ω, (∫ E in I,
      ((resolventMat (Hmat g W L ω) (E + η * Complex.I) x x).im) ^ p) ∂(μ W L) =
      ∫ E in I, ∫ ω, ((resolventMat (Hmat g W L ω) (E + η * Complex.I) x x).im) ^ p
        ∂(μ W L) := fun x => integral_integral_swap (hint x)
  -- the exponents
  have hrη : r * η = (W : ℝ) ^ (ν - τ) := by
    rw [hr, hη, show ν - τ = -τ + ν by ring, Real.rpow_add hW0]
    field_simp
  have ht : t = (8 * (W : ℝ) ^ (ν - τ))⁻¹ := by
    rw [htdef, hh, ← hrη]
    field_simp
    ring
  have htp : t ^ (1 - p) = 8 ^ (p - 1) * (W : ℝ) ^ ((ν - τ) * (p - 1)) := by
    rw [ht, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), neg_sub,
      Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hW0.le]
  have hvol : volume.real I ≤ 2 * E₀ + 2 := by
    rw [hI, Real.volume_real_Icc]
    exact max_le (by linarith) (by linarith)
  have hX : (W : ℝ) ^ ((ν - τ) * (p - 1)) ≤ (W : ℝ) ^ (-D) * (W : ℝ)⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hW0]
    exact Real.rpow_le_rpow_of_exponent_le hW1 (by nlinarith)
  have hKW : K * (W : ℝ)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hW0]
    exact hWK
  have hA0 : 0 ≤ 8 / π * 8 ^ (p - 1) * 3 ^ p * Cp' := by positivity
  have hK0 : 0 ≤ K := by
    rw [hK]
    have : 0 ≤ 2 * E₀ + 2 := by linarith
    positivity
  have htp0 : 0 ≤ 8 / π * t ^ (1 - p) := mul_nonneg (by positivity) (Real.rpow_nonneg ht0.le _)
  calc ((W : ℝ) * L)⁻¹ * ∫ ω, (badCount W L (Hmat g W L ω) (Set.Icc c d) r : ℝ) ∂(μ W L)
      ≤ ((W : ℝ) * L)⁻¹ * ∫ ω, (8 / π * t ^ (1 - p)) * (∑ x : Fin L × Fin W, ∫ E in I,
          ((resolventMat (Hmat g W L ω) (E + η * Complex.I) x x).im) ^ p) ∂(μ W L) :=
        mul_le_mul_of_nonneg_left (integral_mono_of_nonneg
          (ae_of_all _ fun _ => Nat.cast_nonneg _) hbad hcount) (by positivity)
    _ = ((W : ℝ) * L)⁻¹ * ((8 / π * t ^ (1 - p)) * ∑ x : Fin L × Fin W, ∫ E in I, ∫ ω,
          ((resolventMat (Hmat g W L ω) (E + η * Complex.I) x x).im) ^ p ∂(μ W L)) := by
        rw [integral_const_mul, integral_finsetSum _ fun x _ => (hint x).integral_prod_left]
        simp_rw [hswap]
    _ ≤ ((W : ℝ) * L)⁻¹ * ((8 / π * t ^ (1 - p)) * ∑ x : Fin L × Fin W,
          ∫ E in I, (3 : ℝ) ^ p * Cp') :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun x _ => hmomI x) htp0) (by positivity)
    _ = (8 / π * 8 ^ (p - 1) * 3 ^ p * Cp') * (W : ℝ) ^ ((ν - τ) * (p - 1)) *
          volume.real I := by
        rw [setIntegral_const, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul, htp]
        push_cast
        field_simp
    _ ≤ (8 / π * 8 ^ (p - 1) * 3 ^ p * Cp') * (W : ℝ) ^ ((ν - τ) * (p - 1)) *
          (2 * E₀ + 2) :=
        mul_le_mul_of_nonneg_left hvol (mul_nonneg hA0 (Real.rpow_nonneg hW0.le _))
    _ = K * (W : ℝ) ^ ((ν - τ) * (p - 1)) := by
        rw [hK]
        ring
    _ ≤ K * ((W : ℝ) ^ (-D) * (W : ℝ)⁻¹) := mul_le_mul_of_nonneg_left hX hK0
    _ = (K * (W : ℝ)⁻¹) * (W : ℝ) ^ (-D) := by ring
    _ ≤ 1 * (W : ℝ) ^ (-D) := mul_le_mul_of_nonneg_right hKW (Real.rpow_nonneg hW0.le _)
    _ = (W : ℝ) ^ (-D) := one_mul _

end LSBA
