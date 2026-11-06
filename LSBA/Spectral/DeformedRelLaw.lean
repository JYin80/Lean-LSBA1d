import LSBA.Spectral.DeformedIsoLaw

/-!
# The relative local law

(G.2) [us:eq:relative-local-law]: `Im v*Gv / Im v*M_Bv = 1 + O(n^ξ(nη)^{−1/2})` and
`Im v*Gv ≍ v*(I + B²)⁻¹v` with high probability.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal Matrix.Norms.L2Operator

noncomputable section
open scoped Classical

namespace LSBA

/-! ### Auxiliary facts -/

/-- `M_B(z) w ≠ 0` for `w ≠ 0` and `Im z > 0`: the profile is an inverse matrix. -/
private lemma relLaw_MB_mulVec_pos {n : ℕ} [Nonempty (Fin n)] {B : Matrix (Fin n) (Fin n) ℂ}
    (hB : B.IsHermitian) {z : ℂ} (hz : 0 < z.im) {w : Fin n → ℂ} (hw : w ≠ 0) :
    0 < ∑ k, ‖(MB B z *ᵥ w) k‖ ^ 2 := by
  have hm : 0 < (mB B z).im := (isDeformedRoot_mB hB hz).1
  have hq : (z + mB B z).im ≠ 0 := by rw [Complex.add_im]; linarith
  have hX : (-B - (z + mB B z) • (1 : Matrix (Fin n) (Fin n) ℂ)) * MB B z = 1 :=
    sub_smul_mul_resolventMat hB.neg hq
  by_contra hle
  rw [not_lt] at hle
  have h0 : MB B z *ᵥ w = 0 := by
    funext k
    have h1 : ‖(MB B z *ᵥ w) k‖ ^ 2 ≤ 0 :=
      (Finset.single_le_sum (fun k _ => sq_nonneg ‖(MB B z *ᵥ w) k‖) (Finset.mem_univ k)).trans hle
    have h2 : ‖(MB B z *ᵥ w) k‖ ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
    exact norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h2)
  apply hw
  calc w = ((-B - (z + mB B z) • (1 : Matrix (Fin n) (Fin n) ℂ)) * MB B z) *ᵥ w := by
        rw [hX, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]

/-- The real step of the relative law: if `|g - T| ≤ e S`, `S ≤ Cw T`, `T > 0`, `e ≥ 0`,
`Cw e ≤ A` and `Cw e ≤ 1/2`, then `|g / T - 1| ≤ A` and `T / 2 ≤ g ≤ 3 T / 2`. -/
private lemma relLaw_real {g T S e Cw A : ℝ} (hT : 0 < T) (he : 0 ≤ e) (hS : S ≤ Cw * T)
    (hg : |g - T| ≤ e * S) (hA : Cw * e ≤ A) (hh : Cw * e ≤ 1 / 2) :
    |g / T - 1| ≤ A ∧ T / 2 ≤ g ∧ g ≤ 3 / 2 * T := by
  have hb : |g - T| ≤ Cw * e * T := by
    calc |g - T| ≤ e * S := hg
      _ ≤ e * (Cw * T) := mul_le_mul_of_nonneg_left hS he
      _ = Cw * e * T := by ring
  have hr : |g / T - 1| ≤ Cw * e := by
    have : g / T - 1 = (g - T) / T := by field_simp
    rw [this, abs_div, abs_of_pos hT, div_le_iff₀ hT]
    exact hb
  have h2 := (abs_le.mp (hb.trans (mul_le_mul_of_nonneg_right hh hT.le)))
  refine ⟨hr.trans hA, ?_, ?_⟩ <;> nlinarith [h2.1, h2.2]

/-- `n^{δ/2} ≤ √(nη)` when `n^{-1+δ} ≤ η` and `n ≥ 1`. -/
private lemma relLaw_sqrt_ge {n : ℕ} (hn : 1 ≤ n) {δ η : ℝ} (hη : (n : ℝ) ^ (-1 + δ) ≤ η) :
    (n : ℝ) ^ (δ / 2) ≤ Real.sqrt (n * η) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  apply Real.le_sqrt_of_sq_le
  calc ((n : ℝ) ^ (δ / 2)) ^ 2 = (n : ℝ) ^ δ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]; norm_num
    _ = n * (n : ℝ) ^ (-1 + δ) := by
        conv_lhs => rw [show δ = 1 + (-1 + δ) by ring]
        rw [Real.rpow_add hN, Real.rpow_one]
    _ ≤ n * η := mul_le_mul_of_nonneg_left hη hN.le

/-- Relative law (G.2) [us:eq:relative-local-law] of Lemma G.1 [us:lem:local-law]: for
deterministic `v ≠ 0`, `|Im(v^* G v) / v^* Im M_B v - 1| ≤ n^ξ (nη)^{-1/2}` and
`Im(v^* G v) ≍ v^*(I + B²)⁻¹ v`, with probability `≥ 1 - n^{-D}`. -/
theorem localLaw_rel (κ₀ Cstar : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hC : 0 < Cstar) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 1 ≤ C ∧ ∀ ε δ ξ D : ℝ, 0 < ε → ε ≤ ε₀ → 0 < δ → 0 < ξ → 0 < D →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (B : Matrix (Fin n) (Fin n) ℂ) (E η : ℝ),
        DeformClass ε B → |E| ≤ 2 - κ₀ → (n : ℝ) ^ (-1 + δ) ≤ η → η ≤ Cstar →
        ∀ v : Fin n → ℂ, v ≠ 0 →
        μ n 1 {ω | ¬ (|(star v ⬝ᵥ (resolventMat (gueMat n ω - B) (E + η * Complex.I) *ᵥ v)).im /
                (star v ⬝ᵥ (MB B (E + η * Complex.I) *ᵥ v)).im - 1| ≤
              (n : ℝ) ^ ξ / Real.sqrt (n * η) ∧
            C⁻¹ * (star v ⬝ᵥ ((1 + B * B)⁻¹ *ᵥ v)).re ≤
              (star v ⬝ᵥ (resolventMat (gueMat n ω - B) (E + η * Complex.I) *ᵥ v)).im ∧
            (star v ⬝ᵥ (resolventMat (gueMat n ω - B) (E + η * Complex.I) *ᵥ v)).im ≤
              C * (star v ⬝ᵥ ((1 + B * B)⁻¹ *ᵥ v)).re)} ≤
          ENNReal.ofReal ((n : ℝ) ^ (-D)) := by
  obtain ⟨εp, Cp, hεp, hCp, hprof⟩ := deformed_profile κ₀ Cstar hκ₀ hκ₀' hC
  obtain ⟨εw, Cw, hεw, hCw, hvw⟩ := deformed_vector_weight κ₀ Cstar hκ₀ hκ₀' hC
  obtain ⟨εi, hεi, hiso⟩ := localLaw_iso κ₀ Cstar hκ₀ hκ₀' hC
  have hCp0 : 0 < Cp := by linarith
  have hCw0 : 0 < Cw := by linarith
  set K : ℝ := max Cp Cw with hK
  have hKp : Cp ≤ K := le_max_left _ _
  have hKw : Cw ≤ K := le_max_right _ _
  have hK1 : 1 ≤ K := hCp.trans hKp
  refine ⟨min εp (min εw εi), 2 * K, lt_min hεp (lt_min hεw hεi), by linarith, ?_⟩
  intro ε δ ξ D hε hεε₀ hδ hξ hD
  have hεp' : ε ≤ εp := hεε₀.trans (min_le_left _ _)
  have hεw' : ε ≤ εw := hεε₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεi' : ε ≤ εi := hεε₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  set ξ' : ℝ := min ξ (δ / 2) / 2 with hξ'
  have hξ'0 : 0 < ξ' := by rw [hξ']; have := lt_min hξ (by linarith : 0 < δ / 2); linarith
  have hξ'1 : ξ' ≤ ξ / 2 := by
    rw [hξ']; have := min_le_left ξ (δ / 2); linarith
  have hξ'2 : ξ' ≤ δ / 4 := by
    rw [hξ']; have := min_le_right ξ (δ / 2); linarith
  obtain ⟨n₁, hn₁⟩ := hiso ε δ ξ' D hε hεi' hδ hξ'0 hD
  have hev1 : ∀ᶠ n : ℕ in Filter.atTop, K ≤ (n : ℝ) ^ (ξ / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < ξ / 2)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop K
  have hev2 : ∀ᶠ n : ℕ in Filter.atTop, 2 * K ≤ (n : ℝ) ^ (δ / 4) :=
    ((tendsto_rpow_atTop (by positivity : 0 < δ / 4)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop (2 * K)
  obtain ⟨n₂, hn₂⟩ := Filter.eventually_atTop.mp (hev1.and hev2)
  refine ⟨max (max n₁ n₂) 1, ?_⟩
  intro n hn B E η hcl hE hηlow hηC v hv
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hn₁n : n₁ ≤ n := le_trans ((le_max_left _ _).trans (le_max_left _ _)) hn
  have hn₂n : n₂ ≤ n := le_trans ((le_max_right _ _).trans (le_max_left _ _)) hn
  have : Nonempty (Fin n) := ⟨⟨0, hn1⟩⟩
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hN0 : (0 : ℝ) < n := by linarith
  have hη0 : 0 < η := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hηlow
  have hz : 0 < (E + η * Complex.I).im := by simpa using hη0
  obtain ⟨hmlo, -, hform⟩ := hprof (Fin n) B ε E η hε.le hεp' hcl hE hη0 hηC
  obtain ⟨-, -, hwt⟩ := hvw (Fin n) B ε E η hε.le hεw' hcl hE hη0 hηC
  obtain ⟨hid, hlo', -⟩ := hwt v
  obtain ⟨hTlo, hTw⟩ := hform v
  set z : ℂ := E + η * Complex.I with hzdef
  set S : ℝ := ∑ k, ‖(MB B z *ᵥ v) k‖ ^ 2 with hSdef
  set T : ℝ := (star v ⬝ᵥ (MB B z *ᵥ v)).im with hTdef
  set w : ℝ := (star v ⬝ᵥ ((1 + B * B)⁻¹ *ᵥ v)).re with hwdef
  have hS0 : 0 < S := relLaw_MB_mulVec_pos hcl.1 hz hv
  have hm0 : 0 < (mB B z).im := lt_of_lt_of_le (inv_pos.mpr hCp0) hmlo
  have hT0 : 0 < T := by rw [hid]; positivity
  have hw0 : 0 < w := by
    by_contra hle
    rw [not_lt] at hle
    nlinarith
  have hSle : S ≤ Cw * T := (inv_mul_le_iff₀ hCw0).mp hlo'
  -- exponent bounds
  obtain ⟨hA1, hA2⟩ := hn₂ n hn₂n
  have hs : (n : ℝ) ^ (δ / 2) ≤ Real.sqrt (n * η) := relLaw_sqrt_ge hn1 hηlow
  have hs0 : 0 < Real.sqrt (n * η) :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hs
  have hKξ : K * (n : ℝ) ^ ξ' ≤ (n : ℝ) ^ ξ := by
    calc K * (n : ℝ) ^ ξ' ≤ (n : ℝ) ^ (ξ / 2) * (n : ℝ) ^ ξ' :=
          mul_le_mul_of_nonneg_right hA1 (Real.rpow_nonneg hN0.le _)
      _ = (n : ℝ) ^ (ξ / 2 + ξ') := (Real.rpow_add hN0 _ _).symm
      _ ≤ (n : ℝ) ^ ξ := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hKδ : 2 * K * (n : ℝ) ^ ξ' ≤ (n : ℝ) ^ (δ / 2) := by
    calc 2 * K * (n : ℝ) ^ ξ' ≤ (n : ℝ) ^ (δ / 4) * (n : ℝ) ^ (δ / 4) :=
          mul_le_mul hA2 (Real.rpow_le_rpow_of_exponent_le hN1 hξ'2)
            (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hN0.le _)
      _ = (n : ℝ) ^ (δ / 4 + δ / 4) := (Real.rpow_add hN0 _ _).symm
      _ = (n : ℝ) ^ (δ / 2) := by congr 1; ring
  set e : ℝ := (n : ℝ) ^ ξ' / Real.sqrt (n * η) with he
  have he0 : 0 ≤ e := by positivity
  have hKe1 : K * e ≤ (n : ℝ) ^ ξ / Real.sqrt (n * η) := by
    rw [he, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hKξ hs0.le
  have hKe2 : K * e ≤ 1 / 2 := by
    rw [he, ← mul_div_assoc, div_le_iff₀ hs0]
    nlinarith
  refine le_trans (measure_mono ?_) (hn₁ n hn₁n B E η hcl hE hηlow hηC v v)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  by_contra hgood
  rw [not_lt] at hgood
  apply hω
  set g : ℂ := star v ⬝ᵥ (resolventMat (gueMat n ω - B) z *ᵥ v) with hg
  have hdiff : star v ⬝ᵥ ((resolventMat (gueMat n ω - B) z - MB B z) *ᵥ v) =
      g - star v ⬝ᵥ (MB B z *ᵥ v) := by
    rw [Matrix.sub_mulVec, dotProduct_sub]
  rw [hdiff] at hgood
  have hSS : Real.sqrt S * Real.sqrt S = S := Real.mul_self_sqrt hS0.le
  have hgood' : |g.im - T| ≤ e * S := by
    calc |g.im - T| = |(g - star v ⬝ᵥ (MB B z *ᵥ v)).im| := by rw [Complex.sub_im]
      _ ≤ ‖g - star v ⬝ᵥ (MB B z *ᵥ v)‖ := Complex.abs_im_le_norm _
      _ ≤ e * Real.sqrt S * Real.sqrt S := hgood
      _ = e * S := by rw [mul_assoc, hSS]
  have hSle' : S ≤ K * T := hSle.trans (mul_le_mul_of_nonneg_right hKw hT0.le)
  obtain ⟨hr, hlo, hhi⟩ := relLaw_real hT0 he0 hSle' hgood' hKe1 hKe2
  refine ⟨hr, ?_, ?_⟩
  · have hKT : K⁻¹ * w ≤ T :=
      le_trans (mul_le_mul_of_nonneg_right (inv_anti₀ hCp0 hKp) hw0.le) hTlo
    have h2 : (2 * K)⁻¹ * w = (K⁻¹ * w) / 2 := by field_simp
    rw [h2]
    linarith
  · have hTK : T ≤ K * w := hTw.trans (mul_le_mul_of_nonneg_right hKp hw0.le)
    have : 0 ≤ K * w := by positivity
    linarith


end LSBA
