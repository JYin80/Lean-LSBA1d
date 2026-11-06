import LSBA.Upper.SmallScoreSmooth

/-!
# Polynomial growth of the cut field at a fixed preparation

At a fixed preparation `(R_4, v_4)`, under the family clauses of Lemma 9.3
[su:lem:chosen-generator], the cut field of Lemma 9.4 [us:lem:score] and its derivative grow at
most linearly. The cutoff and the generator depend only on the active inputs
`V_5, …, V_{q-1}`, which are bounded on the support of the cutoff; there the generator, the
graph coordinates and the correction (9.9) [us:eq:L] are continuous on a compact set; and the
last component of (9.10) [us:eq:physical] is affine in `V_q`. This is the polynomial growth that
Gaussian integration by parts after conditioning on the preparation blocks requires
(Lemma 8.11 [up:lem:angular]; proof of Lemma 8.12 [up:lem:small-contraction]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Auxiliary lemmas -/

/-- `V_i(y + r u) = V_i(y) + r V_i(u)` for real `r`. -/
private lemma SmallScoreGrowth_gueBlock_add_smul (W q : ℕ) (y u : Ω W q) (r : ℝ) (i : Fin q) :
    gueBlock W q (y + r • u) i = gueBlock W q y i + (r : ℂ) • gueBlock W q u i := by
  ext α β
  simp only [gueBlock, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

/-- If `u` vanishes on the active blocks `4, …, q - 2` (the inputs `V_5, …, V_{q-1}`), then these
blocks of `y + r u` are those of `y`. -/
private lemma SmallScoreGrowth_gueBlock_active {W q : ℕ} {u : Ω W q}
    (hu : ∀ p : Fin q × Fin W × Fin W, 4 ≤ (p.1 : ℕ) → (p.1 : ℕ) + 2 ≤ q → u p = 0)
    (y : Ω W q) (r : ℝ) (i : Fin q) (h4 : 4 ≤ (i : ℕ)) (h2 : (i : ℕ) + 2 ≤ q) :
    gueBlock W q (y + r • u) i = gueBlock W q y i := by
  rw [SmallScoreGrowth_gueBlock_add_smul]
  have h0 : gueBlock W q u i = 0 := by
    ext α β
    simp [gueBlock, hu (i, _, _) h4 h2]
  rw [h0, smul_zero, add_zero]

/-- The graph coordinates `R_j`, `j ≤ q - 1`, of (9.2) [su:eq:transported-normal] depend only on
the active blocks. -/
private lemma SmallScoreGrowth_chartR_eq {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    {y y' : Ω W q}
    (h : ∀ i : Fin q, 4 ≤ (i : ℕ) → (i : ℕ) + 2 ≤ q → gueBlock W q y' i = gueBlock W q y i) :
    ∀ j, j ≤ q - 1 → chartR W g E q R y' j = chartR W g E q R y j
  | 0, _ => rfl
  | j + 1, hj => by
    simp only [chartR]
    split_ifs with h4
    · rfl
    · have hjq : j < q := by omega
      have hb : blockSeq W q y' j = blockSeq W q y j := by
        simp only [blockSeq, hjq, ↓reduceDIte]
        exact h ⟨j, hjq⟩ (by simp only; omega) (by simp only; omega)
      rw [hb, SmallScoreGrowth_chartR_eq h j (by omega)]

/-- The products `R_{[j,5]}`, `j ≤ q - 1`, depend only on the active blocks. -/
private lemma SmallScoreGrowth_chartProd_eq {W q : ℕ} {g E : ℝ} {R : Matrix (Fin W) (Fin W) ℂ}
    {y y' : Ω W q}
    (h : ∀ i : Fin q, 4 ≤ (i : ℕ) → (i : ℕ) + 2 ≤ q → gueBlock W q y' i = gueBlock W q y i) :
    ∀ j, j ≤ q - 1 → chartProd W g E q R y' j = chartProd W g E q R y j
  | 0, _ => rfl
  | j + 1, hj => by
    simp only [chartProd]
    split_ifs with h4
    · rfl
    · rw [SmallScoreGrowth_chartR_eq h (j + 1) hj, SmallScoreGrowth_chartProd_eq h j (by omega)]

/-- Under the first family clause of Lemma 9.3 [su:lem:chosen-generator] and `6 ≤ q`, the cut
field is affine along every `u` vanishing on the active blocks:
`F(y + r u) = F(y) + r (F(y + u) - F(y))`. -/
private lemma SmallScoreGrowth_affine {W q : ℕ} {g E : ℝ} (hq : 6 ≤ q)
    {R : Matrix (Fin W) (Fin W) ℂ} {v : Fin W → ℂ}
    {Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ} {χh : Ω W q → (Fin W → ℂ) → ℝ}
    (hF1 : ∀ ω ω' : Ω W q, (∀ i : Fin q, 4 ≤ (i : ℕ) → (i : ℕ) + 2 ≤ q →
      gueBlock W q ω i = gueBlock W q ω' i) → ∀ w, Kh ω w = Kh ω' w ∧ χh ω w = χh ω' w)
    {u : Ω W q}
    (hu : ∀ p : Fin q × Fin W × Fin W, 4 ≤ (p.1 : ℕ) → (p.1 : ℕ) + 2 ≤ q → u p = 0)
    (y : Ω W q) (r : ℝ) :
    smallScoreField W g E q R v Kh χh (y + r • u) =
      smallScoreField W g E q R v Kh χh y +
        r • (smallScoreField W g E q R v Kh χh (y + u) - smallScoreField W g E q R v Kh χh y) := by
  have hblk : ∀ s : ℝ, ∀ i : Fin q, 4 ≤ (i : ℕ) → (i : ℕ) + 2 ≤ q →
      gueBlock W q (y + s • u) i = gueBlock W q y i :=
    fun s i h4 h2 => SmallScoreGrowth_gueBlock_active hu y s i h4 h2
  have hK : ∀ s : ℝ, Kh (y + s • u) v = Kh y v ∧ χh (y + s • u) v = χh y v :=
    fun s => hF1 _ _ (hblk s) v
  have hone : y + u = y + (1 : ℝ) • u := by rw [one_smul]
  have hX : ∀ s : ℝ, smallField W g E q R v (Kh y v) (y + s • u) =
      smallField W g E q R v (Kh y v) y +
        s • (smallField W g E q R v (Kh y v) (y + (1 : ℝ) • u) -
          smallField W g E q R v (Kh y v) y) := by
    intro s
    funext i
    have hRs := SmallScoreGrowth_chartR_eq (g := g) (E := E) (R := R) (hblk s) (q - 1) le_rfl
    have hR1 := SmallScoreGrowth_chartR_eq (g := g) (E := E) (R := R) (hblk 1) (q - 1) le_rfl
    have hPs := SmallScoreGrowth_chartProd_eq (g := g) (E := E) (R := R) (hblk s) (q - 1) le_rfl
    have hP1 := SmallScoreGrowth_chartProd_eq (g := g) (E := E) (R := R) (hblk 1) (q - 1) le_rfl
    simp only [smallField, smallCorr, hRs, hR1, hPs, hP1, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply]
    split_ifs with h1 h2 h3
    · simp
    · rw [hblk s i (by omega) (by omega), hblk 1 i (by omega) (by omega)]
      simp
    · rw [hblk s i (by omega) (by omega), hblk 1 i (by omega) (by omega)]
      simp
    · rw [SmallScoreGrowth_gueBlock_add_smul W q y u s i,
        SmallScoreGrowth_gueBlock_add_smul W q y u 1 i,
        ← Complex.coe_smul]
      simp only [Complex.ofReal_one, one_smul, mul_add, add_mul, mul_sub, sub_mul,
        mul_smul_comm, smul_mul_assoc, smul_sub, smul_add]
      abel
  let ℓ := (hermCoord_isLinearMap W q).mk'
  have hℓ : ∀ X, hermCoord W q X = ℓ X := fun X => rfl
  simp only [smallScoreField]
  rw [hone, (hK r).1, (hK r).2, (hK 1).1, (hK 1).2, hX r, hℓ, hℓ, hℓ, map_add, map_smul,
    map_sub]
  module

/-- `|η_{(i,α,β)}| ≤ √(2W) ‖V_i(η)‖`: the standard coordinates of a block are bounded by its
operator norm. -/
private lemma SmallScoreGrowth_abs_coord_le {W q : ℕ} (η : Ω W q) (i : Fin q) (α β : Fin W) :
    |η (i, α, β)| ≤ Real.sqrt (2 * W) * ‖gueBlock W q η i‖ := by
  have hW : (0 : ℝ) < W := Nat.cast_pos.2 (Fin.pos α)
  have hs1 : 0 < Real.sqrt W := Real.sqrt_pos.2 hW
  have hs2 : 0 < Real.sqrt (2 * W) := Real.sqrt_pos.2 (by positivity)
  have hle : Real.sqrt W ≤ Real.sqrt (2 * W) := Real.sqrt_le_sqrt (by linarith)
  have hV : 0 ≤ ‖gueBlock W q η i‖ := norm_nonneg _
  have hent : ∀ a b : Fin W, ‖gueBlock W q η i a b‖ ≤ ‖gueBlock W q η i‖ := by
    intro a b
    have h := Matrix.l2_opNorm_mulVec (gueBlock W q η i) (WithLp.toLp 2 (Pi.single b (1 : ℂ)))
    have h1 : ‖(WithLp.toLp 2 (Pi.single b (1 : ℂ)) : EuclideanSpace ℂ (Fin W))‖ = 1 := by
      simp
    rw [h1, mul_one] at h
    refine le_trans ?_ h
    have := PiLp.norm_apply_le
      ((EuclideanSpace.equiv (Fin W) ℂ).symm (gueBlock W q η i *ᵥ Pi.single b (1 : ℂ))) a
    simpa [Matrix.mulVec_single_one] using this
  rcases lt_trichotomy α β with h | rfl | h
  · have hre : (gueBlock W q η i α β).re = η (i, α, β) / Real.sqrt (2 * W) := by
      simp only [gueBlock, Matrix.of_apply, h.ne, h, ↓reduceIte, Complex.div_ofReal_re,
        Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im]
      ring
    have h3 := Complex.abs_re_le_norm (gueBlock W q η i α β)
    rw [hre, abs_div, abs_of_pos hs2, div_le_iff₀ hs2] at h3
    nlinarith [hent α β]
  · have hre : (gueBlock W q η i α α).re = η (i, α, α) / Real.sqrt W := by
      simp [gueBlock]
    have h3 := Complex.abs_re_le_norm (gueBlock W q η i α α)
    rw [hre, abs_div, abs_of_pos hs1, div_le_iff₀ hs1] at h3
    nlinarith [hent α α]
  · have him : (gueBlock W q η i β α).im = η (i, α, β) / Real.sqrt (2 * W) := by
      simp only [gueBlock, Matrix.of_apply, h.ne, h, ↓reduceIte, Complex.div_ofReal_im,
        Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re]
      ring
    have h3 := Complex.abs_im_le_norm (gueBlock W q η i β α)
    rw [him, abs_div, abs_of_pos hs2, div_le_iff₀ hs2] at h3
    nlinarith [hent β α]

/-- Linear growth of a map `G` on `Ω W q` that is affine along every direction vanishing on the
active blocks, bounded by `M` on the ball of radius `D₀ + 1`, and zero wherever an active
coordinate exceeds `D₀`. -/
private lemma SmallScoreGrowth_bound {W q : ℕ} {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] {G : Ω W q → Y} {M D₀ : ℝ} (hM0 : 0 ≤ M) (hD₀ : 0 ≤ D₀)
    (haff : ∀ u : Ω W q,
      (∀ p : Fin q × Fin W × Fin W, 4 ≤ (p.1 : ℕ) → (p.1 : ℕ) + 2 ≤ q → u p = 0) →
      ∀ (y : Ω W q) (r : ℝ), G (y + r • u) = G y + r • (G (y + u) - G y))
    (hM : ∀ z : Ω W q, ‖z‖ ≤ D₀ + 1 → ‖G z‖ ≤ M)
    (hzero : ∀ η : Ω W q, ∀ p : Fin q × Fin W × Fin W, 4 ≤ (p.1 : ℕ) → (p.1 : ℕ) + 2 ≤ q →
      D₀ < |η p| → G η = 0)
    (η : Ω W q) : ‖G η‖ ≤ 3 * M * (1 + ‖η‖) := by
  have hη0 : 0 ≤ ‖η‖ := norm_nonneg _
  by_cases hA : ∀ p : Fin q × Fin W × Fin W, 4 ≤ (p.1 : ℕ) → (p.1 : ℕ) + 2 ≤ q → |η p| ≤ D₀
  swap
  · push Not at hA
    obtain ⟨p, h4, h2, hp⟩ := hA
    rw [hzero η p h4 h2 hp, norm_zero]
    positivity
  set x : Ω W q := fun p => if 4 ≤ (p.1 : ℕ) ∧ (p.1 : ℕ) + 2 ≤ q then η p else 0 with hxdef
  set u : Ω W q := fun p => if 4 ≤ (p.1 : ℕ) ∧ (p.1 : ℕ) + 2 ≤ q then 0 else η p with hudef
  have hxu : η = x + u := by
    funext p
    simp only [hxdef, hudef, Pi.add_apply]
    split_ifs <;> simp
  have hu : ∀ p : Fin q × Fin W × Fin W, 4 ≤ (p.1 : ℕ) → (p.1 : ℕ) + 2 ≤ q → u p = 0 := by
    intro p h4 h2
    simp [hudef, h4, h2]
  have hx : ‖x‖ ≤ D₀ := by
    refine (pi_norm_le_iff_of_nonneg hD₀).2 fun p => ?_
    simp only [hxdef, Real.norm_eq_abs]
    split_ifs with hp
    · exact hA p hp.1 hp.2
    · simp [hD₀]
  have hun : ‖u‖ ≤ ‖η‖ := by
    refine (pi_norm_le_iff_of_nonneg hη0).2 fun p => ?_
    simp only [hudef]
    split_ifs
    · simp [hη0]
    · exact norm_le_pi_norm η p
  by_cases hu1 : ‖u‖ ≤ 1
  · have hb : ‖η‖ ≤ D₀ + 1 := by
      rw [hxu]
      exact (norm_add_le x u).trans (add_le_add hx hu1)
    have := hM η hb
    nlinarith
  · push Not at hu1
    set r := ‖u‖ with hrdef
    have hr0 : r ≠ 0 := by positivity
    set u₁ : Ω W q := r⁻¹ • u with hu₁def
    have hu₁ : ∀ p : Fin q × Fin W × Fin W, 4 ≤ (p.1 : ℕ) → (p.1 : ℕ) + 2 ≤ q → u₁ p = 0 := by
      intro p h4 h2
      simp [hu₁def, hu p h4 h2]
    have hu₁n : ‖u₁‖ = 1 := by
      rw [hu₁def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (by linarith), ← hrdef,
        inv_mul_cancel₀ hr0]
    have hru : r • u₁ = u := by rw [hu₁def, smul_inv_smul₀ hr0]
    have key := haff u₁ hu₁ x r
    rw [hru, ← hxu] at key
    have hGx := hM x (by linarith)
    have hGx1 := hM (x + u₁) ((norm_add_le x u₁).trans (by rw [hu₁n]; linarith))
    have hdiff : ‖G (x + u₁) - G x‖ ≤ 2 * M :=
      (norm_sub_le _ _).trans (by linarith)
    rw [key]
    calc ‖G x + r • (G (x + u₁) - G x)‖
        ≤ ‖G x‖ + r * ‖G (x + u₁) - G x‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
      _ ≤ M + r * (2 * M) := by gcongr
      _ ≤ 3 * M * (1 + ‖η‖) := by nlinarith

/-- Under the family clauses of Lemma 9.3 [su:lem:chosen-generator] and `v_4 = v ≠ 0`, the cut
field of Lemma 9.4 [us:lem:score] and its derivative have polynomial growth. -/
theorem polyGrowth_smallScoreField {W q : ℕ} {g E : ℝ} (hq : 7 ≤ q)
    {P R : Matrix (Fin W) (Fin W) ℂ} {v : Fin W → ℂ}
    {Kh : Ω W q → (Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ} {χh : Ω W q → (Fin W → ℂ) → ℝ}
    (hF : GenFamily W q g E P R Kh χh) (hv : v ≠ 0) :
    PolyGrowth (smallScoreField W g E q R v Kh χh) ∧
      PolyGrowth (fderiv ℝ (smallScoreField W g E q R v Kh χh)) := by
  have hC : ContDiff ℝ 1 (smallScoreField W g E q R v Kh χh) := contDiff_smallScoreField hF hv
  obtain ⟨hF1, -, -, -, -, -, B, hB⟩ := hF
  set F := smallScoreField W g E q R v Kh χh with hFdef
  have hd : Differentiable ℝ F := hC.differentiable one_ne_zero
  have hFc : Continuous F := hC.continuous
  have hDc : Continuous (fderiv ℝ F) := hC.continuous_fderiv one_ne_zero
  set D₀ : ℝ := max (Real.sqrt (2 * W) * B) 0 with hD₀def
  have hD₀ : 0 ≤ D₀ := le_max_right _ _
  -- the cut field vanishes where an active coordinate exceeds `D₀`
  have hz : ∀ η : Ω W q, ∀ p : Fin q × Fin W × Fin W, 4 ≤ (p.1 : ℕ) → (p.1 : ℕ) + 2 ≤ q →
      D₀ < |η p| → F η = 0 := by
    intro η p h4 h2 hp
    have hχ : χh η v = 0 := by
      by_contra hχ
      have hb := hB η v hχ p.1 h4 h2
      have hc := SmallScoreGrowth_abs_coord_le η p.1 p.2.1 p.2.2
      have hs : 0 ≤ Real.sqrt (2 * W) := Real.sqrt_nonneg _
      have : Real.sqrt (2 * W) * ‖gueBlock W q η p.1‖ ≤ D₀ :=
        (mul_le_mul_of_nonneg_left hb hs).trans (le_max_left _ _)
      linarith
    simp [hFdef, smallScoreField, hχ]
  have hzD : ∀ η : Ω W q, ∀ p : Fin q × Fin W × Fin W, 4 ≤ (p.1 : ℕ) → (p.1 : ℕ) + 2 ≤ q →
      D₀ < |η p| → fderiv ℝ F η = 0 := by
    intro η p h4 h2 hp
    have hopen : IsOpen {y : Ω W q | D₀ < |y p|} :=
      isOpen_lt continuous_const (continuous_abs.comp (continuous_apply p))
    have hev : F =ᶠ[nhds η] fun _ => 0 := by
      filter_upwards [hopen.mem_nhds hp] with y hy
      exact hz y p h4 h2 hy
    rw [hev.fderiv_eq, fderiv_const_apply]
  have haffF : ∀ u : Ω W q,
      (∀ p : Fin q × Fin W × Fin W, 4 ≤ (p.1 : ℕ) → (p.1 : ℕ) + 2 ≤ q → u p = 0) →
      ∀ (y : Ω W q) (r : ℝ), F (y + r • u) = F y + r • (F (y + u) - F y) :=
    fun u hu y r => SmallScoreGrowth_affine (by omega) hF1 hu y r
  have haffD : ∀ u : Ω W q,
      (∀ p : Fin q × Fin W × Fin W, 4 ≤ (p.1 : ℕ) → (p.1 : ℕ) + 2 ≤ q → u p = 0) →
      ∀ (y : Ω W q) (r : ℝ), fderiv ℝ F (y + r • u) =
        fderiv ℝ F y + r • (fderiv ℝ F (y + u) - fderiv ℝ F y) := by
    intro u hu y r
    have hfun : (fun z => F (z + r • u)) = fun z => F z + r • (F (z + u) - F z) :=
      funext fun z => haffF u hu z r
    have hdu : DifferentiableAt ℝ (fun z => F (z + u)) y :=
      (hd (y + u)).comp y (differentiableAt_id.add_const u)
    have hsub : DifferentiableAt ℝ (fun z => F (z + u) - F z) y := hdu.sub (hd y)
    have hsm : DifferentiableAt ℝ (fun z => r • (F (z + u) - F z)) y := hsub.const_smul r
    rw [← fderiv_comp_add_right (f := F) (x := y) (r • u), hfun, fderiv_fun_add (hd y) hsm,
      fderiv_fun_const_smul hsub, fderiv_fun_sub hdu (hd y), fderiv_comp_add_right]
  have hK : IsCompact (Metric.closedBall (0 : Ω W q) (D₀ + 1)) := isCompact_closedBall _ _
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hFc.continuousOn
  obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn hDc.continuousOn
  refine ⟨⟨3 * max C₀ 0, 1, fun η => ?_⟩, ⟨3 * max C₁ 0, 1, fun η => ?_⟩⟩
  · rw [pow_one]
    refine SmallScoreGrowth_bound (le_max_right _ _) hD₀ haffF (fun z hz' => ?_) hz η
    exact (hC₀ z (mem_closedBall_zero_iff.2 hz')).trans (le_max_left _ _)
  · rw [pow_one]
    refine SmallScoreGrowth_bound (le_max_right _ _) hD₀ haffD (fun z hz' => ?_) hzD η
    exact (hC₁ z (mem_closedBall_zero_iff.2 hz')).trans (le_max_left _ _)

end LSBA
