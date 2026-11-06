import LSBA.Dyson.FiniteCycle
import LSBA.Dyson.Distribution

/-!
# Boundary values of the Dyson solutions

The boundary value `m_g(E + i0)` of (1.10) [eq:distribution] and the finite-cycle boundary value
`m_{g,L}(E)` of (5.2) [fo:eq:dyson-family] exist at every real energy: the values along
`E + iη` are bounded roots of polynomials whose coefficients converge, so their cluster set at
`η = 0⁺` is a connected subset of a finite root set. The bounds `|m| ≤ max{1,g}` of (A.6)
[da:eq:ward] pass to the limit.
-/

open MeasureTheory Real Filter Topology Complex
open scoped ENNReal

noncomputable section

open scoped Classical

namespace LSBA

/-- A bounded continuous function on `(0, ε)` whose values are roots of polynomials whose
coefficients converge, with nonzero limiting leading coefficient, converges at `0⁺` to a root of
the limiting polynomial. -/
theorem boundary_tendsto_of_poly (n : ℕ) (F : ℝ → ℂ) (c : ℝ → Fin (n + 1) → ℂ)
    (c₀ : Fin (n + 1) → ℂ) (ε K : ℝ) (hε : 0 < ε) (hF : ContinuousOn F (Set.Ioo 0 ε))
    (hK : ∀ η ∈ Set.Ioo 0 ε, ‖F η‖ ≤ K)
    (hc : ∀ i, Tendsto (fun η => c η i) (𝓝[>] 0) (𝓝 (c₀ i))) (hc₀ : c₀ (Fin.last n) ≠ 0)
    (hroot : ∀ η ∈ Set.Ioo 0 ε, ∑ i, c η i * F η ^ (i : ℕ) = 0) :
    ∃ u : ℂ, Tendsto F (𝓝[>] 0) (𝓝 u) ∧ ∑ i, c₀ i * u ^ (i : ℕ) = 0 := by
  set l : Filter ℝ := 𝓝[>] 0 with hl
  have hev : ∀ᶠ η in l, η ∈ Set.Ioo (0 : ℝ) ε := Ioo_mem_nhdsGT hε
  -- the root set of the limiting polynomial is finite
  have hRfin : {x : ℂ | ∑ i, c₀ i * x ^ (i : ℕ) = 0}.Finite := by
    set p : Polynomial ℂ := ∑ i : Fin (n + 1), Polynomial.C (c₀ i) * Polynomial.X ^ (i : ℕ)
      with hp
    have hpn : p.coeff n = c₀ (Fin.last n) := by
      rw [hp, Polynomial.finsetSum_coeff, Fin.sum_univ_castSucc,
        Finset.sum_eq_zero (fun i _ => ?_), zero_add, Polynomial.coeff_C_mul_X_pow]
      · simp
      rw [Polynomial.coeff_C_mul_X_pow, ite_eq_right_iff]
      intro h
      have := i.isLt
      simp only [Fin.val_castSucc] at h
      omega
    have hp0 : p ≠ 0 := fun h => hc₀ (by rw [← hpn, h]; simp)
    refine (Polynomial.finite_setOfPred_isRoot hp0).subset fun x hx => ?_
    simpa [Polynomial.IsRoot, hp, Polynomial.eval_finsetSum] using hx
  -- every cluster point of `F` at `0⁺` is a root of the limiting polynomial
  have hcl : ∀ x, MapClusterPt x l F → ∑ i, c₀ i * x ^ (i : ℕ) = 0 := by
    intro x hx
    by_contra hne
    set Φ : (Fin (n + 1) → ℂ) × ℂ → ℂ := fun p => ∑ i, p.1 i * p.2 ^ (i : ℕ) with hΦ
    have hΦc : Continuous Φ := by
      refine continuous_finsetSum _ fun i _ => ?_
      exact ((continuous_apply i).comp continuous_fst).mul (continuous_snd.pow _)
    have hopen : {y : ℂ | y ≠ 0} ∈ 𝓝 (Φ (c₀, x)) := isOpen_ne.mem_nhds hne
    have hW : Φ ⁻¹' {y : ℂ | y ≠ 0} ∈ 𝓝 (c₀, x) := hΦc.continuousAt hopen
    obtain ⟨N1, hN1, N2, hN2, hsub⟩ := mem_nhds_prod_iff.1 hW
    have h1 : ∀ᶠ η in l, c η ∈ N1 := (tendsto_pi_nhds.2 hc) hN1
    have h2 : ∃ᶠ η in l, F η ∈ N2 := mapClusterPt_iff_frequently.1 hx N2 hN2
    obtain ⟨η, ⟨hη1, hη2⟩, hη3⟩ := ((h1.and_frequently h2).and_eventually hev).exists
    exact hsub (Set.mk_mem_prod hη1 hη2) (hroot η hη3)
  -- bounded values, so a cluster point exists
  have hbd : ∀ᶠ η in l, F η ∈ Metric.closedBall (0 : ℂ) K :=
    hev.mono fun η hη => by simpa using hK η hη
  obtain ⟨u, -, hu⟩ :=
    (isCompact_closedBall (0 : ℂ) K).exists_mapClusterPt_of_frequently hbd.frequently
  -- a second cluster point would force `F` across a small sphere around the first, which
  -- carries no root
  have huniq : ∀ x', MapClusterPt x' l F → x' = u := by
    intro x' hx'
    by_contra hne
    obtain ⟨r0, hr0, hball⟩ := Metric.isOpen_iff.1 (hRfin.sdiff (t := {u})).isClosed.isOpen_compl u
      (by simp)
    set r : ℝ := r0 / 2 with hr
    have hr' : 0 < r := by positivity
    have hi : ∀ x : ℂ, ∑ i, c₀ i * x ^ (i : ℕ) = 0 → dist x u ≤ r → x = u := by
      intro x hx hxr
      by_contra hxu
      have : x ∈ Metric.ball u r0 := by
        rw [Metric.mem_ball]
        linarith [hxr]
      exact hball this ⟨hx, hxu⟩
    have hx'r : r < dist x' u := by
      by_contra h
      exact hne (hi x' (hcl x' hx') (not_lt.1 h))
    have hsph : ∀ᶠ η in l, F η ∉ Metric.sphere u r := by
      by_contra h
      obtain ⟨x, hxs, hx⟩ := (isCompact_sphere u r).exists_mapClusterPt_of_frequently h
      have hxu := hi x (hcl x hx) (le_of_eq (Metric.mem_sphere.1 hxs))
      rw [hxu, Metric.mem_sphere, dist_self] at hxs
      linarith
    obtain ⟨δ, hδ, hδsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hev.and hsph)
    have hδ' : (0 : ℝ) < δ := hδ
    have hIoo : Set.Ioo (0 : ℝ) δ ∈ l := Ioo_mem_nhdsGT hδ'
    obtain ⟨η₁, hF₁, hη₁⟩ := ((mapClusterPt_iff_frequently.1 hu (Metric.ball u r)
      (Metric.ball_mem_nhds u hr')).and_eventually hIoo).exists
    obtain ⟨η₂, hF₂, hη₂⟩ := ((mapClusterPt_iff_frequently.1 hx' (Metric.ball x' (dist x' u - r))
      (Metric.ball_mem_nhds x' (by linarith))).and_eventually hIoo).exists
    have hf₁ : ‖F η₁ - u‖ < r := by
      rw [← dist_eq_norm]; exact Metric.mem_ball.1 hF₁
    have hf₂ : r < ‖F η₂ - u‖ := by
      rw [← dist_eq_norm]
      have h1 := Metric.mem_ball.1 hF₂
      have h2 := dist_triangle x' (F η₂) u
      rw [dist_comm] at h1
      linarith
    have hsubε : Set.Ioo (0 : ℝ) δ ⊆ Set.Ioo 0 ε := fun η hη => (hδsub hη).1
    have hcont : ContinuousOn (fun η => ‖F η - u‖) (Set.Ioo 0 δ) :=
      ((hF.mono hsubε).sub continuousOn_const).norm
    obtain ⟨η, hη, hηr⟩ := isPreconnected_Ioo.intermediate_value hη₁ hη₂ hcont
      ⟨hf₁.le, hf₂.le⟩
    exact (hδsub hη).2 (by rw [Metric.mem_sphere, dist_eq_norm]; exact hηr)
  exact ⟨u, (isCompact_closedBall (0 : ℂ) K).tendsto_nhds_of_unique_mapClusterPt hbd
    (fun x _ hx => huniq x hx), hcl u hu⟩

/-- A continuous family of coefficient vectors converges coordinatewise along `0⁺`. -/
private lemma tendsto_coord_zero {n : ℕ} {c : ℝ → Fin (n + 1) → ℂ} (hc : Continuous c)
    (i : Fin (n + 1)) : Tendsto (fun η => c η i) (𝓝[>] 0) (𝓝 (c 0 i)) :=
  (((continuous_apply i).comp hc).tendsto 0).mono_left nhdsWithin_le_nhds

/-- The line `E + iη` as a continuous map into `ℂ`. -/
private lemma continuous_shift (E : ℝ) : Continuous fun η : ℝ => (E : ℂ) + η * I := by
  fun_prop

private lemma shift_im_pos (E : ℝ) {η : ℝ} (hη : 0 < η) : 0 < ((E : ℂ) + η * I).im := by
  simpa using hη

private lemma gammaG_pos_aux (g : ℝ) : 0 < gammaG g := by
  unfold gammaG
  have : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  positivity

private lemma gammaG_mul_sq_aux (g : ℝ) : gammaG g * (max 1 g) ^ 2 = 1 := by
  have : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  unfold gammaG
  field_simp

/-- Coefficients of the quartic form of (1.9) [eq:dyson] at `z = E + iη`:
`γ² u⁴ + 2γ z u³ + (z² - 4b²) u² - 1`. -/
private def linePoly (g E : ℝ) (η : ℝ) : Fin 5 → ℂ :=
  ![-1, 0, ((E : ℂ) + η * I) ^ 2 - 4 * (hopB g : ℂ) ^ 2,
    2 * (gammaG g : ℂ) * ((E : ℂ) + η * I), (gammaG g : ℂ) ^ 2]

private lemma continuous_linePoly (g E : ℝ) : Continuous (linePoly g E) := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp only [linePoly] <;> fun_prop

private lemma linePoly_last (g E : ℝ) (η : ℝ) : linePoly g E η (Fin.last 4) = (gammaG g : ℂ) ^ 2 :=
  rfl

private lemma linePoly_root (g : ℝ) (hg : 0 ≤ g) (E : ℝ) {η : ℝ} (hη : 0 < η) :
    ∑ i, linePoly g E η i * mDyson g (E + η * I) ^ (i : ℕ) = 0 := by
  have hz := shift_im_pos E hη
  obtain ⟨hm, hfix⟩ := mDyson_spec g hg _ hz
  have hq := (dyson_iff_quartic g hg _ hz _ hm).1 hfix
  simp only [linePoly, Fin.sum_univ_five]
  simp
  linear_combination hq

private lemma line_continuousOn (g : ℝ) (hg : 0 ≤ g) (E : ℝ) :
    ContinuousOn (fun η : ℝ => mDyson g (E + η * I)) (Set.Ioo 0 1) :=
  ((mDyson_differentiableOn g hg).continuousOn).comp (continuous_shift E).continuousOn
    fun _ hη => shift_im_pos E hη.1

private lemma line_norm_le (g : ℝ) (hg : 0 ≤ g) (E : ℝ) :
    ∀ η ∈ Set.Ioo (0 : ℝ) 1, ‖mDyson g (E + η * I)‖ ≤ max 1 g := fun _ hη =>
  mDyson_norm_le_max g hg _ (shift_im_pos E hη.1)

private lemma line_poly_limit (g : ℝ) (hg : 0 ≤ g) (E : ℝ) :
    ∃ u : ℂ, Tendsto (fun η : ℝ => mDyson g (E + η * I)) (𝓝[>] 0) (𝓝 u) ∧
      ∑ i, linePoly g E 0 i * u ^ (i : ℕ) = 0 :=
  boundary_tendsto_of_poly 4 (fun η : ℝ => mDyson g (E + η * I)) (linePoly g E) (linePoly g E 0)
    1 (max 1 g) one_pos (line_continuousOn g hg E) (line_norm_le g hg E)
    (tendsto_coord_zero (continuous_linePoly g E))
    (by rw [linePoly_last]; exact pow_ne_zero 2 (by exact_mod_cast (gammaG_pos_aux g).ne'))
    (fun _ hη => linePoly_root g hg E hη.1)

/-- Boundary value `m_g(E + i0) = lim_{η↓0} m_g(E + iη)` of (1.10) [eq:distribution]. -/
def mDysonBdry (g E : ℝ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun η : ℝ => mDyson g (E + η * I)

/-- The boundary value of (1.10) [eq:distribution] exists at every real energy. -/
theorem mDysonBdry_tendsto (g : ℝ) (hg : 0 ≤ g) (E : ℝ) :
    Tendsto (fun η : ℝ => mDyson g (E + η * I)) (𝓝[>] 0) (𝓝 (mDysonBdry g E)) := by
  obtain ⟨u, hu, -⟩ := line_poly_limit g hg E
  have : mDysonBdry g E = u := hu.limUnder_eq
  rw [this]
  exact hu

/-- (A.6) [da:eq:ward] at real energies: `|m_g(E + i0)| ≤ γ_g^{-1/2}`, `Im m_g(E + i0) ≥ 0`. -/
theorem mDysonBdry_norm_le (g : ℝ) (hg : 0 ≤ g) (E : ℝ) :
    ‖mDysonBdry g E‖ ≤ max 1 g ∧ 0 ≤ (mDysonBdry g E).im := by
  have hT := mDysonBdry_tendsto g hg E
  have hev : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η := self_mem_nhdsWithin
  refine ⟨le_of_tendsto hT.norm (hev.mono fun η hη => ?_),
    ge_of_tendsto ((Complex.continuous_im.tendsto _).comp hT) (hev.mono fun η hη => ?_)⟩
  · exact mDyson_norm_le_max g hg _ (shift_im_pos E hη)
  · exact (mDyson_spec g hg _ (shift_im_pos E hη)).1.le

/-- The boundary value is a root of the quartic form of (1.9) [eq:dyson] at `z = E`. -/
theorem mDysonBdry_quartic (g : ℝ) (hg : 0 ≤ g) (E : ℝ) :
    mDysonBdry g E ^ 2 * (((E : ℂ) + gammaG g * mDysonBdry g E) ^ 2 - 4 * (hopB g : ℂ) ^ 2) =
      1 := by
  obtain ⟨u, hu, hroot⟩ := line_poly_limit g hg E
  have : mDysonBdry g E = u := hu.limUnder_eq
  rw [this]
  simp only [linePoly, Fin.sum_univ_five] at hroot
  simp at hroot
  linear_combination hroot

/-! ### The finite cycle -/

/-- Ward identity for a resolvent entry with real diagonal: `Im (a - w)⁻¹ = Im w · |(a - w)⁻¹|²`. -/
private lemma im_inv_real_sub (a : ℝ) (w : ℂ) :
    (((a : ℂ) - w)⁻¹).im = w.im * ‖((a : ℂ) - w)⁻¹‖ ^ 2 := by
  rw [Complex.inv_im, Complex.sq_norm, map_inv₀, Complex.sub_im, Complex.ofReal_im]
  ring

/-- (A.6) [da:eq:ward] for (5.2) [fo:eq:dyson-family]: `|m_{g,L}(z)| ≤ γ_g^{-1/2}`. -/
theorem mDysonL_norm_le_max (g : ℝ) (hg : 0 ≤ g) (L : ℕ) (hL : 1 ≤ L) (z : ℂ) (hz : 0 < z.im) :
    ‖mDysonL g L z‖ ≤ max 1 g := by
  obtain ⟨hm, hfix⟩ := mDysonL_spec g hg L hL z hz
  set m := mDysonL g L z with hmdef
  have hγ := gammaG_pos_aux g
  have hwim : 0 < (z + (gammaG g : ℂ) * m).im := by
    rw [Complex.add_im, Complex.im_ofReal_mul]
    positivity
  set w := z + (gammaG g : ℂ) * m with hw
  set r : Fin L → ℂ := fun k => (((2 * hopB g * Real.cos (2 * π * k / L) : ℝ) : ℂ) - w)⁻¹
    with hr
  have hmr : m = (L : ℂ)⁻¹ * ∑ k, r k := hfix
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  set A : ℝ := (L : ℝ)⁻¹ * ∑ k, ‖r k‖ ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  have hLc : (L : ℂ)⁻¹ = (((L : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  have him : m.im = w.im * A := by
    have h1 : m.im = (L : ℝ)⁻¹ * ∑ k, (r k).im := by
      conv_lhs => rw [hmr, hLc, Complex.im_ofReal_mul, Complex.im_sum]
    have h2 : ∑ k, (r k).im = w.im * ∑ k, ‖r k‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => im_inv_real_sub _ _
    rw [h1, hA, h2]
    ring
  have hnorm : ‖m‖ ≤ (L : ℝ)⁻¹ * ∑ k, ‖r k‖ := by
    calc ‖m‖ = ‖(L : ℂ)⁻¹‖ * ‖∑ k, r k‖ := by rw [hmr, norm_mul]
      _ ≤ (L : ℝ)⁻¹ * ∑ k, ‖r k‖ := by
        rw [norm_inv, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
  have hcs : ‖m‖ ^ 2 ≤ A := by
    have h1 : ((L : ℝ)⁻¹ * ∑ k, ‖r k‖) ^ 2 ≤ A := by
      have hcs' : (∑ k, ‖r k‖) ^ 2 ≤ L * ∑ k, ‖r k‖ ^ 2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin L)))
          (f := fun k => ‖r k‖)
      rw [hA, mul_pow]
      calc (L : ℝ)⁻¹ ^ 2 * (∑ k, ‖r k‖) ^ 2 ≤ (L : ℝ)⁻¹ ^ 2 * (L * ∑ k, ‖r k‖ ^ 2) := by gcongr
        _ = (L : ℝ)⁻¹ * ∑ k, ‖r k‖ ^ 2 := by field_simp
    exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans h1
  have hγA : gammaG g * A ≤ 1 := by
    by_contra hcon
    have hcon' : 1 < gammaG g * A := not_le.1 hcon
    have hwim' : w.im = z.im + gammaG g * m.im := by
      rw [hw, Complex.add_im, Complex.im_ofReal_mul]
    have : m.im = (z.im + gammaG g * m.im) * A := by rw [← hwim', him]
    nlinarith [mul_nonneg hz.le hA0]
  have hM : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  have h3 : ‖m‖ ^ 2 ≤ (max 1 g) ^ 2 := by
    have e := gammaG_mul_sq_aux g
    calc ‖m‖ ^ 2 = ‖m‖ ^ 2 * (gammaG g * (max 1 g) ^ 2) := by rw [e, mul_one]
      _ = (gammaG g * ‖m‖ ^ 2) * (max 1 g) ^ 2 := by ring
      _ ≤ (gammaG g * A) * (max 1 g) ^ 2 := by gcongr
      _ ≤ 1 * (max 1 g) ^ 2 := by gcongr
      _ = (max 1 g) ^ 2 := one_mul _
  exact (sq_le_sq₀ (norm_nonneg _) hM.le).mp h3

/-- `X`-coefficients that depend continuously on a complex parameter. -/
private def CoeffCont (f : ℂ → Polynomial ℂ) : Prop :=
  ∀ i : ℕ, Continuous fun z => (f z).coeff i

private lemma CoeffCont.const (p : Polynomial ℂ) : CoeffCont fun _ => p :=
  fun _ => continuous_const

private lemma CoeffCont.C_id : CoeffCont fun z => Polynomial.C z := by
  intro i
  simp only [Polynomial.coeff_C]
  split_ifs
  · exact continuous_id
  · exact continuous_const

private lemma CoeffCont.sub {f h : ℂ → Polynomial ℂ} (hf : CoeffCont f) (hh : CoeffCont h) :
    CoeffCont fun z => f z - h z := fun i => by
  simp only [Polynomial.coeff_sub]
  exact (hf i).sub (hh i)

private lemma CoeffCont.mul {f h : ℂ → Polynomial ℂ} (hf : CoeffCont f) (hh : CoeffCont h) :
    CoeffCont fun z => f z * h z := fun i => by
  simp only [Polynomial.coeff_mul]
  exact continuous_finsetSum _ fun x _ => (hf x.1).mul (hh x.2)

private lemma CoeffCont.prod {ι : Type*} (s : Finset ι) {f : ι → ℂ → Polynomial ℂ}
    (hf : ∀ k ∈ s, CoeffCont (f k)) : CoeffCont fun z => ∏ k ∈ s, f k z := by
  induction s using Finset.induction_on with
  | empty => simpa using CoeffCont.const 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

private lemma CoeffCont.sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → Polynomial ℂ}
    (hf : ∀ k ∈ s, CoeffCont (f k)) : CoeffCont fun z => ∑ k ∈ s, f k z := fun i => by
  simp only [Polynomial.finsetSum_coeff]
  exact continuous_finsetSum _ fun k hk => hf k hk i

/-- The factor `a_k - z - γ_g X` of the cleared form of (5.2) [fo:eq:dyson-family], with
`a_k = 2b cos(2πk/L)`. -/
private def cycFac (g : ℝ) (L : ℕ) (z : ℂ) (k : Fin L) : Polynomial ℂ :=
  Polynomial.C (((2 * hopB g * Real.cos (2 * π * k / L) : ℝ) : ℂ)) - Polynomial.C z -
    Polynomial.C (gammaG g : ℂ) * Polynomial.X

/-- The cleared form of (5.2) [fo:eq:dyson-family]:
`X ∏_k (a_k - z - γ_g X) - L⁻¹ ∑_k ∏_{j ≠ k} (a_j - z - γ_g X)`. -/
private def cycPoly (g : ℝ) (L : ℕ) (z : ℂ) : Polynomial ℂ :=
  Polynomial.X * ∏ k, cycFac g L z k -
    Polynomial.C ((L : ℂ)⁻¹) * ∑ k, ∏ j ∈ Finset.univ.erase k, cycFac g L z j

private lemma coeffCont_cycFac (g : ℝ) (L : ℕ) (k : Fin L) : CoeffCont fun z => cycFac g L z k :=
  ((CoeffCont.const _).sub CoeffCont.C_id).sub (CoeffCont.const _)

private lemma coeffCont_cycPoly (g : ℝ) (L : ℕ) : CoeffCont (cycPoly g L) :=
  ((CoeffCont.const _).mul (CoeffCont.prod _ fun k _ => coeffCont_cycFac g L k)).sub
    ((CoeffCont.const _).mul (CoeffCont.sum _ fun _ _ =>
      CoeffCont.prod _ fun j _ => coeffCont_cycFac g L j))

private lemma eval_cycFac (g : ℝ) (L : ℕ) (z u : ℂ) (k : Fin L) :
    (cycFac g L z k).eval u =
      ((2 * hopB g * Real.cos (2 * π * k / L) : ℝ) : ℂ) - (z + gammaG g * u) := by
  simp only [cycFac, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X]
  ring

/-- A solution of (5.2) [fo:eq:dyson-family] in `ℂ_+` at a point with `Im (z + γ_g u) > 0` is a root
of the cleared
polynomial. -/
private lemma cycPoly_root (g : ℝ) (L : ℕ) {z u : ℂ} (hw : 0 < (z + (gammaG g : ℂ) * u).im)
    (h : u = dysonRHSL g L z u) : (cycPoly g L z).eval u = 0 := by
  set d : Fin L → ℂ := fun k =>
    ((2 * hopB g * Real.cos (2 * π * k / L) : ℝ) : ℂ) - (z + gammaG g * u) with hd
  have hd0 : ∀ k, d k ≠ 0 := fun k h0 => by
    have := congrArg Complex.im h0
    simp only [hd, Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at this
    linarith
  have hS : ∑ k, ∏ j ∈ Finset.univ.erase k, d j = (∏ k, d k) * ∑ k, (d k)⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ k)]
    field_simp [hd0 k]
  have hu : u = (L : ℂ)⁻¹ * ∑ k, (d k)⁻¹ := h
  simp only [cycPoly, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_finsetSum, eval_cycFac]
  change u * ∏ k, d k - (L : ℂ)⁻¹ * ∑ k, ∏ j ∈ Finset.univ.erase k, d j = 0
  rw [hS]
  linear_combination (∏ k, d k) * hu

private lemma natDegree_cycFac_le (g : ℝ) (L : ℕ) (z : ℂ) (k : Fin L) :
    (cycFac g L z k).natDegree ≤ 1 := by
  unfold cycFac
  compute_degree

private lemma natDegree_prod_cycFac_le (g : ℝ) (L : ℕ) (z : ℂ) (s : Finset (Fin L)) :
    (∏ k ∈ s, cycFac g L z k).natDegree ≤ L := by
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc ∑ k ∈ s, (cycFac g L z k).natDegree ≤ ∑ _k ∈ s, 1 :=
        Finset.sum_le_sum fun k _ => natDegree_cycFac_le g L z k
    _ = s.card := by simp
    _ ≤ L := by simpa using Finset.card_le_univ s

private lemma natDegree_sum_cycFac_le (g : ℝ) (L : ℕ) (z : ℂ) :
    (∑ k, ∏ j ∈ Finset.univ.erase k, cycFac g L z j).natDegree ≤ L :=
  Polynomial.natDegree_sum_le_of_forall_le _ _ fun _ _ => natDegree_prod_cycFac_le g L z _

private lemma natDegree_cycPoly_le (g : ℝ) (L : ℕ) (z : ℂ) : (cycPoly g L z).natDegree ≤ L + 1 := by
  unfold cycPoly
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine Polynomial.natDegree_mul_le.trans ?_
    have := natDegree_prod_cycFac_le g L z Finset.univ
    have h1 : (Polynomial.X : Polynomial ℂ).natDegree ≤ 1 := Polynomial.natDegree_X_le
    omega
  · exact (Polynomial.natDegree_C_mul_le _ _).trans ((natDegree_sum_cycFac_le g L z).trans
      (Nat.le_succ L))

/-- The coefficient of `X^{L+1}` is `(-γ_g)^L`. -/
private lemma coeff_cycPoly_top (g : ℝ) (L : ℕ) (z : ℂ) :
    (cycPoly g L z).coeff (L + 1) = (-(gammaG g : ℂ)) ^ L := by
  unfold cycPoly
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul,
    Polynomial.coeff_eq_zero_of_natDegree_lt (p := ∑ k, ∏ j ∈ Finset.univ.erase k, cycFac g L z j)
      (Nat.lt_succ_of_le (natDegree_sum_cycFac_le g L z)), mul_zero, sub_zero]
  have h := Polynomial.coeff_prod_of_natDegree_le Finset.univ (fun k => cycFac g L z k) 1
    (fun k _ => natDegree_cycFac_le g L z k)
  rw [Finset.card_univ, Fintype.card_fin, mul_one] at h
  rw [h]
  have hk : ∀ k : Fin L, (cycFac g L z k).coeff 1 = -(gammaG g : ℂ) := fun k => by
    simp [cycFac, Polynomial.coeff_C]
  simp [hk]

private lemma cycle_continuousOn (g : ℝ) (hg : 0 ≤ g) (L : ℕ) (hL : 1 ≤ L) (E : ℝ) :
    ContinuousOn (fun η : ℝ => mDysonL g L (E + η * I)) (Set.Ioo 0 1) :=
  ((mDysonL_differentiableOn g hg L hL).continuousOn).comp (continuous_shift E).continuousOn
    fun _ hη => shift_im_pos E hη.1

/-- The coefficient family of the cleared form of (5.2) [fo:eq:dyson-family] along `E + iη`. -/
private def cycCoeff (g : ℝ) (L : ℕ) (E : ℝ) (η : ℝ) : Fin (L + 1 + 1) → ℂ :=
  fun i => (cycPoly g L ((E : ℂ) + η * I)).coeff i

private lemma continuous_cycCoeff (g : ℝ) (L : ℕ) (E : ℝ) : Continuous (cycCoeff g L E) :=
  continuous_pi fun i => (coeffCont_cycPoly g L i).comp (continuous_shift E)

private lemma cycCoeff_last (g : ℝ) (L : ℕ) (E : ℝ) :
    cycCoeff g L E 0 (Fin.last (L + 1)) = (-(gammaG g : ℂ)) ^ L := by
  simp only [cycCoeff, Fin.val_last]
  exact coeff_cycPoly_top g L _

private lemma cycCoeff_root (g : ℝ) (hg : 0 ≤ g) (L : ℕ) (hL : 1 ≤ L) (E : ℝ) {η : ℝ}
    (hη : 0 < η) :
    ∑ i, cycCoeff g L E η i * mDysonL g L (E + η * I) ^ (i : ℕ) = 0 := by
  have hz := shift_im_pos E hη
  obtain ⟨hm, hfix⟩ := mDysonL_spec g hg L hL _ hz
  have hw : 0 < (((E : ℂ) + η * I) + (gammaG g : ℂ) * mDysonL g L (E + η * I)).im := by
    rw [Complex.add_im, Complex.im_ofReal_mul]
    have := gammaG_pos_aux g
    positivity
  have hr := cycPoly_root g L hw hfix
  rw [Polynomial.eval_eq_sum_range' (n := L + 1 + 1)
    (Nat.lt_succ_of_le (natDegree_cycPoly_le g L _))] at hr
  rw [← hr, ← Fin.sum_univ_eq_sum_range (fun i => (cycPoly g L ((E : ℂ) + η * I)).coeff i *
    mDysonL g L (E + η * I) ^ i) (L + 1 + 1)]
  rfl

/-- The boundary value of (5.2) [fo:eq:dyson-family] exists at every real energy. -/
theorem mDysonLBdry_tendsto (g : ℝ) (hg : 0 ≤ g) (L : ℕ) (hL : 1 ≤ L) (E : ℝ) :
    Tendsto (fun η : ℝ => mDysonL g L (E + η * I)) (𝓝[>] 0) (𝓝 (mDysonLBdry g L E)) := by
  have hγ := gammaG_pos_aux g
  obtain ⟨u, hu, -⟩ := boundary_tendsto_of_poly (L + 1) (fun η : ℝ => mDysonL g L (E + η * I))
    (cycCoeff g L E) (cycCoeff g L E 0) 1 (max 1 g) one_pos (cycle_continuousOn g hg L hL E)
    (fun η hη => mDysonL_norm_le_max g hg L hL _ (shift_im_pos E hη.1))
    (tendsto_coord_zero (continuous_cycCoeff g L E))
    (by
      rw [cycCoeff_last]
      exact pow_ne_zero L (neg_ne_zero.2 (by exact_mod_cast hγ.ne')))
    (fun _ hη => cycCoeff_root g hg L hL E hη.1)
  have : mDysonLBdry g L E = u := hu.limUnder_eq
  rw [this]
  exact hu

/-- `|m_{g,L}(E)| ≤ max{1,g}` and `Im m_{g,L}(E) ≥ 0` at every real energy (proof of
Lemma 5.13(a) [fo:lem:terminal-deterministic]). -/
theorem mDysonLBdry_norm_le (g : ℝ) (hg : 0 ≤ g) (L : ℕ) (hL : 1 ≤ L) (E : ℝ) :
    ‖mDysonLBdry g L E‖ ≤ max 1 g ∧ 0 ≤ (mDysonLBdry g L E).im := by
  have hT := mDysonLBdry_tendsto g hg L hL E
  have hev : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η := self_mem_nhdsWithin
  refine ⟨le_of_tendsto hT.norm (hev.mono fun η hη => ?_),
    ge_of_tendsto ((Complex.continuous_im.tendsto _).comp hT) (hev.mono fun η hη => ?_)⟩
  · exact mDysonL_norm_le_max g hg L hL _ (shift_im_pos E hη)
  · exact (mDysonL_spec g hg L hL _ (shift_im_pos E hη)).1.le

end LSBA
