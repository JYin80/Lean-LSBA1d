import LSBA.Main.StieltjesCDF
import LSBA.Main.RoughMean
import LSBA.Spectral.EmpStieltjes
import LSBA.Gauss.StdGauss

/-!
# The rough density law (Lemma 1.3 [lem:rough-density])

The tail `P(N⁻¹ Tr H² > 4) ≤ e^{-LW²/8}`, the concentration of `N⁻¹ Tr G(z)` around `m_g(z)` at one
energy ((D.6) [eq:rough-density] with the bias (D.5) [rd:eq:bias]), and Lemma 1.3
[lem:rough-density], (1.15) [eq:rough-counting], uniformly in `g ≥ 0`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- On `{N⁻¹ Tr H² > 4}` the sum of the squared Gaussian entries exceeds `2LW²`, for `g ≥ 0`. -/
private lemma roughDensity_trace_sq_subset (g : ℝ) (hg : 0 ≤ g) (W L : ℕ) (hL : 3 ≤ L) :
    {ω : Ω W L | 4 < ((W * L : ℕ) : ℝ)⁻¹ * (Hmat g W L ω * Hmat g W L ω).trace.re} ⊆
      {x | 2 * (Fintype.card (Fin L × Fin W × Fin W) : ℝ) < ∑ i, x i ^ 2} := by
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [trace_Hmat_mul_self g W L hL ω, Complex.ofReal_re] at hω
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW
    simp at hω
    linarith
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hL' : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hcard : (Fintype.card (Fin L × Fin W × Fin W) : ℝ) = L * W * W := by
    simp [Fintype.card_prod, mul_assoc]
  rw [hcard]
  set S := ∑ k, ω k ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => sq_nonneg _
  set m := max 1 g with hm
  have hm1 : 1 ≤ m := le_max_left _ _
  have hgm : g ≤ m := le_max_right _ _
  set q := m⁻¹ ^ 2 with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := pow_le_one₀ (inv_nonneg.mpr (by linarith)) (inv_le_one_of_one_le₀ hm1)
  have hqg : q * g ^ 2 ≤ 1 := by
    rw [hq, ← mul_pow]
    apply pow_le_one₀ (by positivity)
    rw [inv_mul_le_iff₀ (by linarith)]
    linarith
  have hN : ((W * L : ℕ) : ℝ) = W * L := by push_cast; ring
  rw [hN] at hω
  have hWL : (0 : ℝ) < W * L := by positivity
  have h1 : 4 * (W * L) < q * (2 * g ^ 2 * W * L + (W : ℝ)⁻¹ * S) := by
    rw [inv_mul_eq_div, lt_div_iff₀ hWL] at hω
    linarith
  have h2 : q * (2 * g ^ 2 * W * L) ≤ 2 * (W * L) := by
    have : q * (2 * g ^ 2 * W * L) = 2 * (q * g ^ 2) * (W * L) := by ring
    rw [this]
    nlinarith
  have h3 : q * ((W : ℝ)⁻¹ * S) ≤ (W : ℝ)⁻¹ * S :=
    mul_le_of_le_one_left (by positivity) hq1
  have h4 : 2 * (W * L) < (W : ℝ)⁻¹ * S := by nlinarith
  rw [inv_mul_eq_div, lt_div_iff₀ hW'] at h4
  nlinarith

/-- `P(N⁻¹ Tr H² > 4) ≤ e^{-LW²/8}` (Appendix D.2 [sec:rough-density-proof]). -/
theorem Hmat_trace_sq_tail (g : ℝ) (hg : 0 ≤ g) (W L : ℕ) (hL : 3 ≤ L) :
    μ W L {ω | 4 < ((W * L : ℕ) : ℝ)⁻¹ * (Hmat g W L ω * Hmat g W L ω).trace.re} ≤
      ENNReal.ofReal (Real.exp (-((L : ℝ) * W ^ 2) / 8)) := by
  refine (measure_mono (roughDensity_trace_sq_subset g hg W L hL)).trans ?_
  rw [μ_eq_stdGauss]
  refine (chiSq_tail (Fin L × Fin W × Fin W)).trans (le_of_eq ?_)
  congr 3
  push_cast [Fintype.card_prod, Fintype.card_fin]
  ring

/-- `0 < γ_g`. -/
private lemma roughDensity_gammaG_pos (g : ℝ) : 0 < gammaG g := by
  have : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  unfold gammaG
  positivity

/-- `γ_g ≤ 1`. -/
private lemma roughDensity_gammaG_le_one (g : ℝ) : gammaG g ≤ 1 :=
  inv_le_one_of_one_le₀ (one_le_pow₀ (le_max_left _ _))

/-- `A_g ⊗ I_W` is Hermitian. -/
private lemma roughDensity_kron_isHermitian (g : ℝ) (W L : ℕ) :
    (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, Ag, Matrix.conjTranspose_smul,
    (cycleAdj_isHermitian L).eq, Complex.star_def, Complex.conj_ofReal]

/-- One energy: (D.6) [eq:rough-density] around `m_g(z)`, with the bias (D.5) [rd:eq:bias]. -/
theorem trN_resolvent_Hmat_dev (g : ℝ) (hg : 0 ≤ g) (W L : ℕ) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (E η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hρ : roughErr W L η ≤ η / 2) (u : ℝ) (hu : 0 ≤ u) :
    μ W L {ω | u + 8 * (η⁻¹) ^ 2 * roughErr W L η <
        ‖trN (resolventMat (Hmat g W L ω) (E + η * Complex.I)) - mDyson g (E + η * Complex.I)‖} ≤
      ENNReal.ofReal (4 * Real.exp (-((W : ℝ) ^ 2 * L * η ^ 4 * u ^ 2) / π ^ 2)) := by
  set z : ℂ := E + η * Complex.I with hzdef
  have hzim : z.im = η := by simp [hzdef]
  have hz : 0 < z.im := hzim ▸ hη
  have hbias := norm_mBar_sub_mDyson_le g hg W L hW hL E η hη hη1 hρ
  have hHm : ∀ ω, Hmat g W L ω =
      blockFlow W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) (gammaG g) ω :=
    Hmat_eq_blockFlow g W L
  have hmean : ∫ ω', trN (resolventMat (blockFlow W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
      (gammaG g) ω') z) ∂(μ W L) = mBar g W L z := by
    simp only [mBar, hHm]
  have hγ0 := roughDensity_gammaG_pos g
  have hγ1 := roughDensity_gammaG_le_one g
  have hconc := trN_resolvent_concentration W L _ (roughDensity_kron_isHermitian g W L) hγ0.le hz
    u hu
  rw [hmean, hzim] at hconc
  have hsub : {ω | u + 8 * (η⁻¹) ^ 2 * roughErr W L η <
      ‖trN (resolventMat (Hmat g W L ω) z) - mDyson g z‖} ⊆
      {ω | u < ‖trN (resolventMat (blockFlow W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
        (gammaG g) ω) z) - mBar g W L z‖} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, ← hHm] at hω ⊢
    have htri : ‖trN (resolventMat (Hmat g W L ω) z) - mDyson g z‖ ≤
        ‖trN (resolventMat (Hmat g W L ω) z) - mBar g W L z‖ + ‖mBar g W L z - mDyson g z‖ := by
      have := norm_add_le (trN (resolventMat (Hmat g W L ω) z) - mBar g W L z)
        (mBar g W L z - mDyson g z)
      simpa using this
    linarith
  refine (measure_mono hsub).trans (hconc.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num))))
  have hX : 0 ≤ (W : ℝ) ^ 2 * L * η ^ 4 * u ^ 2 := by positivity
  have hπ : 0 < π ^ 2 := by positivity
  rw [neg_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_left hX (by positivity) (mul_le_of_le_one_right hπ.le hγ1)

/-- The five terms of the Stieltjes-to-CDF bound at the choices `R = 40/d`, `h = d²/200`,
`η = d³/2000`, `ε = d²/300`, `τ = 4/R²`, `a = d/10` add up to less than `d`, for `0 < d ≤ 1`. -/
private lemma roughDensity_cdf_bound_lt (d : ℝ) (hd : 0 < d) (hd1 : d ≤ 1) :
    2 * (4 / (40 / d) ^ 2) + 2 * (d ^ 3 / 2000) / π + (2 * (40 / d) + 2) * (d ^ 2 / 300) / π +
      2 * (d ^ 3 / 2000) / (π * (d ^ 2 / 200)) + d / 10 < d := by
  have hπ := Real.pi_gt_three
  have hπ0 := Real.pi_pos
  have hd2 : d ^ 2 ≤ d := by nlinarith
  have hd3 : d ^ 3 ≤ d := by nlinarith
  have t1 : 2 * (4 / (40 / d) ^ 2) ≤ d / 200 := by
    have : 2 * (4 / (40 / d) ^ 2) = d ^ 2 / 200 := by field_simp; ring
    rw [this]; linarith
  have t2 : 2 * (d ^ 3 / 2000) / π ≤ d / 1000 := by
    rw [div_le_iff₀ hπ0]; nlinarith
  have t3 : (2 * (40 / d) + 2) * (d ^ 2 / 300) / π ≤ 82 * d / 900 := by
    have : (2 * (40 / d) + 2) * (d ^ 2 / 300) = (80 * d + 2 * d ^ 2) / 300 := by
      field_simp; ring
    rw [this, div_le_iff₀ hπ0]; nlinarith
  have t4 : 2 * (d ^ 3 / 2000) / (π * (d ^ 2 / 200)) ≤ d / 15 := by
    rw [div_le_iff₀ (by positivity)]
    have : d / 15 * (π * (d ^ 2 / 200)) = π * d ^ 3 / 3000 := by ring
    rw [this]; nlinarith [pow_pos hd 3]
  linarith

/-- `roughErr W L η ≤ ρ₀` once `W ≥ 4/(η⁴ρ₀)` and `L ≥ 16/(η²ρ₀)`. -/
private lemma roughDensity_roughErr_le {η ρ₀ : ℝ} (hη : 0 < η) (hρ₀ : 0 < ρ₀) {W L : ℕ}
    (hW : 4 / (η ^ 4 * ρ₀) ≤ W) (hL : 16 / (η ^ 2 * ρ₀) ≤ L) : roughErr W L η ≤ ρ₀ := by
  have hπ4 := Real.pi_le_four
  have hW0 : (0 : ℝ) < W := lt_of_lt_of_le (by positivity) hW
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le (by positivity) hL
  have hW' : 4 ≤ W * (η ^ 4 * ρ₀) := (div_le_iff₀ (by positivity)).mp hW
  have hL' : 16 ≤ L * (η ^ 2 * ρ₀) := (div_le_iff₀ (by positivity)).mp hL
  have hs2 : π / (2 * Real.sqrt 2) ≤ 2 := by
    have : (1 : ℝ) ≤ Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have e1 : π / (2 * Real.sqrt 2) / (W * η ^ 4) ≤ ρ₀ / 2 := by
    refine (div_le_div_of_nonneg_right hs2 (by positivity)).trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : ρ₀ * (W * η ^ 4) = W * (η ^ 4 * ρ₀) := by ring
    linarith
  have e2 : 2 * π / (L * η ^ 2) ≤ ρ₀ / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : ρ₀ * (L * η ^ 2) = L * (η ^ 2 * ρ₀) := by ring
    linarith
  unfold roughErr
  linarith

/-- The deterministic step of Appendix D.2 [sec:rough-density-proof]: off the `χ²` event and off
the deviation events at the grid points `-R - 1 + jσ`, `j < K`, the empirical distribution
function is within `δ` of `F_g` everywhere. -/
private lemma roughDensity_event_subset (g : ℝ) (hg : 0 ≤ g) (W L : ℕ) (hW : 1 ≤ W) (hL : 1 ≤ L)
    {δ R h η ε σ u : ℝ} (K : ℕ) (hR0 : 0 < R) (hR4 : 4 ≤ R) (hη0 : 0 < η) (hh0 : 0 < h)
    (hh2 : h ≤ 1 / 2) (hσ0 : 0 < σ) (hcover : R + 1 ≤ -R - 1 + ((K : ℝ) - 1) * σ)
    (hclose : u + 8 * (η⁻¹) ^ 2 * roughErr W L η + 2 * σ / η ^ 2 ≤ ε)
    (hB : 2 * (4 / R ^ 2) + 2 * η / π + (2 * R + 2) * ε / π + 2 * η / (π * h) +
      Real.sqrt (2 * h) < δ) :
    {ω | ∃ x : ℝ, δ < |empCDF (Hmat g W L ω) x - Fdist g x|} ⊆
      {ω | 4 < ((W * L : ℕ) : ℝ)⁻¹ * (Hmat g W L ω * Hmat g W L ω).trace.re} ∪
        ⋃ j ∈ Finset.range K, {ω | u + 8 * (η⁻¹) ^ 2 * roughErr W L η <
          ‖trN (resolventMat (Hmat g W L ω) ((-R - 1 + j * σ : ℝ) + η * Complex.I)) -
            mDyson g ((-R - 1 + j * σ : ℝ) + η * Complex.I)‖} := by
  rintro ω ⟨x, hx⟩
  by_contra hnot
  rw [Set.mem_union, not_or] at hnot
  obtain ⟨hT, hU⟩ := hnot
  have hT' : ((W * L : ℕ) : ℝ)⁻¹ * (Hmat g W L ω * Hmat g W L ω).trace.re ≤ 4 := not_lt.mp hT
  set A := Hmat g W L ω with hAdef
  have hA : A.IsHermitian := Hmat_isHermitian g W L ω
  have : Nonempty (Fin L × Fin W) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have := isProbabilityMeasure_empMeasure hA
  have := (nuDyson_spec g hg).1
  have hcard : Fintype.card (Fin L × Fin W) = W * L := by
    simp [Fintype.card_prod, Nat.mul_comm]
  have hstμ : ∀ z : ℂ, 0 < z.im → trN (resolventMat A z) = stieltjes (empMeasure A) z := by
    intro z hz
    rw [trN, ← hcard]
    exact trace_resolventMat_eq_stieltjes hA hz.ne'
  have hgrid : ∀ j : ℕ, j < K →
      ‖stieltjes (empMeasure A) ((-R - 1 + j * σ : ℝ) + η * Complex.I) -
        stieltjes (nuDyson g) ((-R - 1 + j * σ : ℝ) + η * Complex.I)‖ ≤
          u + 8 * (η⁻¹) ^ 2 * roughErr W L η := by
    intro j hj
    have hzim : 0 < (((-R - 1 + j * σ : ℝ) : ℂ) + η * Complex.I).im := by simpa using hη0
    rw [← hstμ _ hzim, (nuDyson_spec g hg).2 _ hzim]
    refine not_lt.mp fun hlt => hU ?_
    exact Set.mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hj, hlt⟩
  have hs : ∀ E ∈ Set.Icc (-R - 1) (R + 1),
      ‖stieltjes (empMeasure A) (E + η * Complex.I) -
        stieltjes (nuDyson g) (E + η * Complex.I)‖ ≤ ε := fun E hE =>
    (norm_stieltjes_sub_le_of_grid _ _ hη0 hσ0 (-R - 1) K hgrid E
      ⟨hE.1, hE.2.trans hcover⟩).trans hclose
  have hτ0 : (0 : ℝ) ≤ 4 / R ^ 2 := by positivity
  have htail : (empMeasure A {t | R < |t|}).toReal ≤ 4 / R ^ 2 := by
    refine (empMeasure_abs_gt_le hA hR0).trans ?_
    rw [hcard]
    exact div_le_div_of_nonneg_right hT' (by positivity)
  have s1 : Set.Iio (-R) ⊆ {t : ℝ | R < |t|} := fun t (ht : t < -R) =>
    show R < |t| from lt_abs.mpr (Or.inr (by linarith))
  have s2 : Set.Ioi R ⊆ {t : ℝ | R < |t|} := fun t (ht : R < t) =>
    show R < |t| from lt_abs.mpr (Or.inl ht)
  have hμl : (empMeasure A (Set.Iio (-R))).toReal ≤ 4 / R ^ 2 :=
    (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono s1)).trans htail
  have hμr : (empMeasure A (Set.Ioi R)).toReal ≤ 4 / R ^ 2 :=
    (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono s2)).trans htail
  have hE₀ := support_bound_le_four g hg
  have s3 : Set.Iio (-R) ⊆ (Set.Icc (-((2 * g + 2) / max 1 g)) ((2 * g + 2) / max 1 g))ᶜ :=
    fun t ht hmem => by
      have : t < -R := ht
      have := (Set.mem_Icc.mp hmem).1
      linarith
  have s4 : Set.Ioi R ⊆ (Set.Icc (-((2 * g + 2) / max 1 g)) ((2 * g + 2) / max 1 g))ᶜ :=
    fun t ht hmem => by
      have : R < t := ht
      have := (Set.mem_Icc.mp hmem).2
      linarith
  have hνl : (nuDyson g (Set.Iio (-R))).toReal ≤ 4 / R ^ 2 := by
    rw [measure_mono_null s3 (nuDyson_compl_support g hg)]
    simpa using hτ0
  have hνr : (nuDyson g (Set.Ioi R)).toReal ≤ 4 / R ^ 2 := by
    rw [measure_mono_null s4 (nuDyson_compl_support g hg)]
    simpa using hτ0
  have hatom : ∀ y : ℝ, (nuDyson g (Set.Icc (y - h) (y + h))).toReal ≤ Real.sqrt (2 * h) :=
    fun y => nuDyson_Icc_le g hg y h hh0 hh2
  have hcdf := cdf_sub_le_of_stieltjes (empMeasure A) (nuDyson g) hR0 hη0 hh0 (by linarith)
    hμl hμr hνl hνr hatom hs x
  rw [empMeasure_Iic hA x] at hcdf
  have hx' : δ < |empCDF A x - (nuDyson g (Set.Iic x)).toReal| := hx
  linarith

/-- Lemma 1.3 [lem:rough-density], (1.15) [eq:rough-counting]. -/
theorem rough_density_law (δ : ℝ) (hδ : 0 < δ) :
    ∃ Wδ Lδ : ℕ, ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ W : ℕ, Wδ ≤ W → ∀ L : ℕ, max Lδ 3 ≤ L → ∀ g : ℝ, 0 ≤ g →
        μ W L {ω | ∃ x : ℝ, δ < |empCDF (Hmat g W L ω) x - Fdist g x|} ≤
          ENNReal.ofReal (C * Real.exp (-c * (W : ℝ) ^ 2 * L)) := by
  have hπ0 := Real.pi_pos
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = min δ 1 := ⟨_, rfl⟩
  have hd0 : 0 < d := hd ▸ lt_min hδ one_pos
  have hd1 : d ≤ 1 := hd ▸ min_le_right _ _
  have hdδ : d ≤ δ := hd ▸ min_le_left _ _
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 40 / d := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = d ^ 2 / 200 := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = d ^ 3 / 2000 := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = d ^ 2 / 300 := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = ε * η ^ 2 / 4 := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = ε / 8 := ⟨_, rfl⟩
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀ : ℝ, ρ₀ = ε * η ^ 2 / 32 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈(2 * R + 2) / σ⌉₊ + 1 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = η ^ 4 * u ^ 2 / π ^ 2 := ⟨_, rfl⟩
  have hR0 : 0 < R := hR ▸ by positivity
  have hR4 : 4 ≤ R := by rw [hR, le_div_iff₀ hd0]; linarith
  have hh0 : 0 < h := hh ▸ by positivity
  have hh2 : h ≤ 1 / 2 := by rw [hh]; nlinarith
  have hη0 : 0 < η := hη ▸ by positivity
  have hd3 : d ^ 3 ≤ 1 := pow_le_one₀ hd0.le hd1
  have hη1 : η ≤ 1 := by rw [hη]; linarith
  have hε0 : 0 < ε := hε ▸ by positivity
  have hε1 : ε ≤ 1 := by rw [hε]; nlinarith
  have hσ0 : 0 < σ := hσ ▸ by positivity
  have hu0 : 0 < u := hu ▸ by positivity
  have hu1 : u ≤ 1 := by rw [hu]; linarith
  have hρ₀0 : 0 < ρ₀ := hρ₀ ▸ by positivity
  have hρ₀η : ρ₀ ≤ η / 2 := by
    have h1 : η ^ 2 ≤ η := by nlinarith
    have h2 : ε * η ^ 2 ≤ η := by nlinarith
    rw [hρ₀]; linarith
  have hc0 : 0 < c := hc ▸ by positivity
  have hc8 : c ≤ 1 / 8 := by
    have h1 : η ^ 4 ≤ 1 := pow_le_one₀ hη0.le hη1
    have h2 : u ^ 2 ≤ 1 := pow_le_one₀ hu0.le hu1
    have h3 : η ^ 4 * u ^ 2 ≤ 1 := by nlinarith [pow_nonneg hη0.le 4]
    have h4 : (1 : ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
    rw [hc, div_le_iff₀ (by positivity)]
    nlinarith
  have hsqrt : Real.sqrt (2 * h) = d / 10 := by
    rw [hh, show 2 * (d ^ 2 / 200) = (d / 10) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hB : 2 * (4 / R ^ 2) + 2 * η / π + (2 * R + 2) * ε / π + 2 * η / (π * h) +
      Real.sqrt (2 * h) < δ := by
    have := roughDensity_cdf_bound_lt d hd0 hd1
    rw [hsqrt, hR, hη, hε, hh]
    linarith
  have hcover : R + 1 ≤ -R - 1 + ((K : ℝ) - 1) * σ := by
    have hK' : (K : ℝ) - 1 = ⌈(2 * R + 2) / σ⌉₊ := by rw [hK]; push_cast; ring
    rw [hK']
    have := (div_le_iff₀ hσ0).mp (Nat.le_ceil ((2 * R + 2) / σ))
    linarith
  refine ⟨⌈4 / (η ^ 4 * ρ₀)⌉₊, ⌈16 / (η ^ 2 * ρ₀)⌉₊, 1 + 4 * K, c, by positivity, hc0, ?_⟩
  intro W hW L hL g hg
  have hL3 : 3 ≤ L := le_of_max_le_right hL
  have hW1 : 1 ≤ W := le_trans (Nat.ceil_pos.mpr (by positivity)) hW
  have hρ : roughErr W L η ≤ ρ₀ := roughDensity_roughErr_le hη0 hρ₀0
    ((Nat.le_ceil _).trans (by exact_mod_cast hW))
    ((Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_left hL))
  have hρη : roughErr W L η ≤ η / 2 := hρ.trans hρ₀η
  have hclose : u + 8 * (η⁻¹) ^ 2 * roughErr W L η + 2 * σ / η ^ 2 ≤ ε := by
    have h1 : 8 * (η⁻¹) ^ 2 * roughErr W L η ≤ 8 * (η⁻¹) ^ 2 * ρ₀ :=
      mul_le_mul_of_nonneg_left hρ (by positivity)
    have h2 : 8 * (η⁻¹) ^ 2 * ρ₀ = ε / 4 := by rw [hρ₀]; field_simp; ring
    have h3 : 2 * σ / η ^ 2 = ε / 2 := by rw [hσ]; field_simp; ring
    rw [h3, hu]; linarith
  have hsub := roughDensity_event_subset g hg W L hW1 (by omega) K hR0 hR4 hη0 hh0 hh2 hσ0
    hcover hclose hB
  set e := Real.exp (-c * (W : ℝ) ^ 2 * L) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hχ : Real.exp (-((L : ℝ) * W ^ 2) / 8) ≤ e := by
    refine Real.exp_le_exp.mpr ?_
    have h0 : 0 ≤ (W : ℝ) ^ 2 * L := by positivity
    have h1 : c * ((W : ℝ) ^ 2 * L) ≤ 1 / 8 * ((W : ℝ) ^ 2 * L) :=
      mul_le_mul_of_nonneg_right hc8 h0
    calc -((L : ℝ) * W ^ 2) / 8 = -(1 / 8 * ((W : ℝ) ^ 2 * L)) := by ring
      _ ≤ -(c * ((W : ℝ) ^ 2 * L)) := neg_le_neg h1
      _ = -c * (W : ℝ) ^ 2 * L := by ring
  have hexp : -((W : ℝ) ^ 2 * L * η ^ 4 * u ^ 2) / π ^ 2 = -c * (W : ℝ) ^ 2 * L := by
    rw [hc]; ring
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add le_rfl (measure_biUnion_finset_le _ _)).trans ?_
  calc _ ≤ ENNReal.ofReal e + ∑ _j ∈ Finset.range K, ENNReal.ofReal (4 * e) := by
        refine add_le_add ((Hmat_trace_sq_tail g hg W L hL3).trans
          (ENNReal.ofReal_le_ofReal hχ)) (Finset.sum_le_sum fun j _ => ?_)
        refine (trN_resolvent_Hmat_dev g hg W L hW1 (by omega) _ η hη0 hη1 hρη u hu0.le).trans ?_
        rw [hexp]
    _ = ENNReal.ofReal (e + K * (4 * e)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_add he0 (by positivity)]
    _ = ENNReal.ofReal ((1 + 4 * K) * e) := by ring_nf

end LSBA
