import LSBA.Upper.CorrectorCoeff
import LSBA.Upper.CorrectorAlg
import LSBA.Upper.CenterIncOne
import LSBA.Upper.CenterNewton

/-!
# The linear coefficients of the corrector equation

Bounds for the coefficients of (11.63) [lg:eq:Q-coefficients] (Section 11.3.4
[lg:sec:cocycle-correction], step (2)): the matrix `A_0` of the orders `1` and `g⁻²` is triangular
in `|k|` within each sign and preserves the parity of the index, with diagonal
`(−e^{−2iθ})^k [1 − |k| h_θ² g⁻² (3 + a_{±2})] − 1` and off-diagonal entries `O(g⁻²)`;
`A − A_0 = O(g⁻⁴)`; and `b_k = ½ h_θ² g⁻² [|k| = 1] + O(g⁻⁴)` (from (11.12) [lg:eq:c2] and
`a_{±1} = 0`).
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

private lemma cl_sub_C (g : ℝ) (a : ℤ → ℂ) (c : ℂ) : centerSub g a (C c) = C c := by
  simp [centerSub]

private lemma cl_sub_mVar {g : ℝ} {a : ℤ → ℂ} (ha : a 0 = 1) (j : ℤ) :
    centerSub g a (mVar j) = C (a j) := by
  unfold mVar
  split_ifs with h
  · subst h; simp [ha]
  · simp [centerSub]

private lemma cl_sub_fVar (g : ℝ) (a : ℤ → ℂ) (j : ℤ) : centerSub g a (fVar j) = fVar j := by
  unfold fVar
  split_ifs <;> simp [centerSub]

private lemma cl_sub_γ (g : ℝ) (a : ℤ → ℂ) :
    centerSub g a (X .γ) = C (((g ^ 2)⁻¹ : ℝ) : ℂ) := by
  simp [centerSub]

private lemma cl_coeff_fVar (k : NzInt) (n : ℤ) :
    (fVar n).coeff (Finsupp.single (.f k) 1) = if k.1 = n then 1 else 0 := by
  unfold fVar
  split_ifs with h1 h2 h2
  · exact absurd (h2.trans h1) k.2
  · rw [coeff_one]
    refine ite_eq_right_iff.mpr fun h => ?_
    have := congrArg (fun d : ObsVar →₀ ℕ => d (.f k)) h
    simp at this
  · rw [coeff_X]
    refine ite_eq_left_iff.mpr fun h => absurd ?_ h
    congr 2
    exact Subtype.ext h2.symm
  · rw [coeff_X]
    refine ite_eq_right_iff.mpr fun h => ?_
    have := congrArg (fun d : ObsVar →₀ ℕ => d (.f k)) h
    have hk : (⟨n, h1⟩ : NzInt) ≠ k := fun h' => h2 (by rw [← h'])
    simp [hk] at this

private lemma cl_coeff_C_fVar_C (k : NzInt) (c d : ℂ) (n : ℤ) :
    (C c * fVar n * C d).coeff (Finsupp.single (.f k) 1) = if k.1 = n then c * d else 0 := by
  rw [mul_comm, ← mul_assoc, ← C_mul, coeff_C_mul, cl_coeff_fVar]
  split_ifs <;> simp [mul_comm]

/-- The coefficient of `f_k` in `𝓛 f_r` of (11.51) [lg:eq:center-corner] at `m = a`. -/
private def clCorner (a : ℤ → ℂ) (r : ℕ) (k : ℤ) : ℂ :=
  -(if k = r then 3 * (r : ℂ) else 0) -
    (if 3 ≤ r then (if k = (r : ℤ) - 2 then (r : ℂ) - 2 else 0) else 0) -
    ∑ n ∈ Finset.Icc 1 (r + 1), (if k = n then (n : ℂ) * a ((r : ℤ) + 2 - n) else 0) -
    6 * ∑ n ∈ Finset.Icc 1 (r - 1), (if k = n then (n : ℂ) * a ((r : ℤ) - n) else 0) -
    ∑ n ∈ Finset.Icc 1 (r - 3), (if k = n then (n : ℂ) * a ((r : ℤ) - 2 - n) else 0)

private lemma cl_coeff_C_fVar (k : NzInt) (c : ℂ) (n : ℤ) :
    (C c * fVar n).coeff (Finsupp.single (.f k) 1) = if k.1 = n then c else 0 := by
  rw [coeff_C_mul, cl_coeff_fVar]
  split_ifs <;> simp

private lemma cl_coeff_corner {g : ℝ} {a : ℤ → ℂ} (ha0 : a 0 = 1) (ha1 : a 1 = 0)
    (ham1 : a (-1) = 0) (r : ℕ) (k : NzInt) :
    (centerSub g a (centerCorner r)).coeff (Finsupp.single (.f k) 1) = clCorner a r k.1 := by
  have hite : centerSub g a (if 3 ≤ r then C ((r : ℂ) - 2) * fVar ((r : ℤ) - 2) else 0) =
      if 3 ≤ r then C ((r : ℂ) - 2) * fVar ((r : ℤ) - 2) else 0 := by
    split_ifs
    · rw [map_mul, cl_sub_C, cl_sub_fVar]
    · exact map_zero _
  have h1 : centerSub g a (-C (3 * (r : ℂ)) * fVar r) = -C (3 * (r : ℂ)) * fVar r := by
    rw [map_mul, map_neg, cl_sub_C, cl_sub_fVar]
  have hite' : (if 3 ≤ r then C ((r : ℂ) - 2) * fVar ((r : ℤ) - 2) else 0).coeff
      (Finsupp.single (.f k) 1) = if 3 ≤ r then (if k.1 = (r : ℤ) - 2 then (r : ℂ) - 2 else 0)
      else 0 := by
    by_cases h3 : 3 ≤ r
    · simp only [h3, ↓reduceIte]
      exact cl_coeff_C_fVar k _ _
    · simp [h3]
  unfold centerCorner clCorner
  rw [map_add, map_sub, map_sub, map_sub, map_sub, h1, hite]
  simp only [map_mul, map_add, map_sum, cl_sub_C, cl_sub_fVar, cl_sub_mVar ha0, ha1, ham1, C_0,
    zero_mul, add_zero, mul_zero]
  simp only [coeff_sub, neg_mul, coeff_neg, coeff_sum, coeff_C_mul, ← C_mul,
    cl_coeff_C_fVar_C, hite', cl_coeff_fVar]
  split_ifs <;> simp

private lemma cl_center (g E : ℝ) (R : ℕ) :
    center g E R 0 = 1 ∧ center g E R 1 = 0 ∧ center g E R (-1) = 0 ∧
      ∀ j : ℤ, Odd j → center g E R j = 0 := by
  refine ⟨(center_zero_odd_neg g E R 0).1, (center_zero_odd_neg g E R 0).2.1,
    by simpa using (center_zero_odd_neg g E R (-1)).2.1, fun j hj => ?_⟩
  obtain ⟨i, rfl⟩ := hj
  exact (center_zero_odd_neg g E R i).2.1

private lemma cl_coeff_Xf (k r : NzInt) :
    (X (.f r) : ObsPoly).coeff (Finsupp.single (.f k) 1) = if k = r then 1 else 0 := by
  have h := cl_coeff_fVar k r.1
  simp only [fVar, r.2, ↓reduceDIte] at h
  rw [h]
  simp [Subtype.ext_iff]

/-- `(A_0)_{kr}` for `r > 0` from the leading retained map (Section 11.3.3
[lg:sec:general-state]). -/
private lemma cl_corrMat0_pos {g E : ℝ} {R : ℕ} {r : NzInt}
    (hT : truncG 1 (corrUpd E R (.f r)) = C ((-normalPhase E) ^ r.1) *
      (X (.f r) + C (((normalH E ^ 2 : ℝ) : ℂ)) * X .γ * centerCorner r.1.toNat)) (k : NzInt) :
    corrMat0 g E R k r = (if k = r then (-normalPhase E) ^ r.1 - 1 else 0) +
      (-normalPhase E) ^ r.1 * (((normalH E ^ 2 / g ^ 2 : ℝ) : ℂ)) *
        clCorner (center g E R) r.1.toNat k.1 := by
  obtain ⟨h0, h1, hm1, -⟩ := cl_center g E R
  have hXf : centerSub g (center g E R) (X (.f r)) = X (.f r) := by simp [centerSub]
  unfold corrMat0 linCoeff
  rw [hT, map_sub, map_mul, map_add, map_mul, map_mul, cl_sub_C, cl_sub_C, cl_sub_γ, hXf,
    coeff_sub, coeff_C_mul, ← C_mul]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.coe_add, Pi.add_apply, coeff_C_mul,
    cl_coeff_corner h0 h1 hm1,
    cl_coeff_Xf]
  split_ifs <;> push_cast <;> ring

/-! ### Conjugation -/

private lemma cl_neg_neg (v : ObsVar) : v.neg.neg = v := by
  cases v <;> simp [ObsVar.neg]

private lemma cl_neg_inj : Function.Injective ObsVar.neg :=
  fun u v h => by rw [← cl_neg_neg u, h, cl_neg_neg]

private lemma cl_conjPoly_eq (p : ObsPoly) :
    conjPoly p = rename ObsVar.neg (map (starRingEnd ℂ) p) := by
  have h : conjPoly = (rename ObsVar.neg : ObsPoly →ₐ[ℂ] ObsPoly).toRingHom.comp
      (map (starRingEnd ℂ)) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) fun v => ?_
    · simp [conjPoly]
    · simp [conjPoly]
  rw [h]
  rfl

private lemma cl_coeff_conj (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (conjPoly p).coeff d = star (p.coeff (d.mapDomain ObsVar.neg)) := by
  have hd : d = (d.mapDomain ObsVar.neg).mapDomain ObsVar.neg := by
    rw [← Finsupp.mapDomain_comp]
    have : ObsVar.neg ∘ ObsVar.neg = id := funext cl_neg_neg
    rw [this, Finsupp.mapDomain_id]
  conv_lhs => rw [hd]
  rw [cl_conjPoly_eq, coeff_rename_mapDomain _ cl_neg_inj, coeff_map]
  rfl

private lemma cl_coeff_truncG (N : ℕ) (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (truncG N p).coeff d = if d .γ ≤ N then p.coeff d else 0 := by
  have hw : Finsupp.weight ObsVar.gamWt d = d .γ := by
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_single ObsVar.γ]
    · simp [ObsVar.gamWt]
    · intro b _ hb
      cases b <;> simp_all [ObsVar.gamWt]
    · intro h
      simp [Finsupp.notMem_support_iff.mp h]
  unfold truncG
  rw [LinearMap.sum_apply, MvPolynomial.coeff_sum]
  simp only [coeff_weightedHomogeneousComponent, hw]
  rw [Finset.sum_ite_eq]
  simp

private lemma cl_truncG_conj (N : ℕ) (p : ObsPoly) :
    truncG N (conjPoly p) = conjPoly (truncG N p) := by
  ext d
  have h : d.mapDomain ObsVar.neg ObsVar.γ = d ObsVar.γ :=
    Finsupp.mapDomain_apply_of_injective cl_neg_inj d ObsVar.γ
  rw [cl_coeff_truncG, cl_coeff_conj, cl_coeff_conj, cl_coeff_truncG, h]
  split_ifs <;> simp

private lemma cl_sub_conj {g : ℝ} {a : ℤ → ℂ} (ha : ∀ j, a (-j) = star (a j)) (p : ObsPoly) :
    centerSub g a (conjPoly p) = conjPoly (centerSub g a p) := by
  have h : (centerSub g a : ObsPoly →ₐ[ℂ] ObsPoly).toRingHom.comp conjPoly =
      conjPoly.comp (centerSub g a : ObsPoly →ₐ[ℂ] ObsPoly).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) fun v => ?_
    · simp [conjPoly, centerSub]
    · cases v with
      | m j => simp [conjPoly, centerSub, ObsVar.neg, ha]
      | f j => simp [conjPoly, centerSub, ObsVar.neg]
      | w => simp [conjPoly, centerSub, ObsVar.neg]
      | γ => simp [conjPoly, centerSub, ObsVar.neg]
  exact congrArg (fun φ : ObsPoly →+* ObsPoly => φ p) h

private lemma cl_linCoeff_conj {g : ℝ} {a : ℤ → ℂ} (ha : ∀ j, a (-j) = star (a j)) (k : NzInt)
    (p : ObsPoly) :
    linCoeff g a ⟨-k.1, neg_ne_zero.mpr k.2⟩ (conjPoly p) = star (linCoeff g a k p) := by
  unfold linCoeff
  rw [cl_sub_conj ha, cl_coeff_conj, Finsupp.mapDomain_single]
  congr 3
  simp [ObsVar.neg]

/-- `(A_0)_{−k,−r} = \overline{(A_0)_{kr}}`. -/
private lemma cl_corrMat0_neg (g E : ℝ) (R : ℕ) (k r : NzInt) :
    corrMat0 g E R ⟨-k.1, neg_ne_zero.mpr k.2⟩ ⟨-r.1, neg_ne_zero.mpr r.2⟩ =
      star (corrMat0 g E R k r) := by
  have ha : ∀ j, center g E R (-j) = star (center g E R j) :=
    fun j => (center_zero_odd_neg g E R j).2.2
  unfold corrMat0
  have h1 : corrUpd E R (.f ⟨-r.1, neg_ne_zero.mpr r.2⟩) = conjPoly (corrUpd E R (.f r)) :=
    (conjPoly_corrUpd E R (.f r)).symm
  have h2 : (X (.f ⟨-r.1, neg_ne_zero.mpr r.2⟩) : ObsPoly) = conjPoly (X (.f r)) := by
    simp [conjPoly, ObsVar.neg]
  rw [h1, h2, cl_truncG_conj, ← map_sub, cl_linCoeff_conj ha]

/-! ### The coefficients of `𝓛 f_r` at `m = a` -/

private lemma cl_corner_diag (a : ℤ → ℂ) {r : ℕ} (hr : 1 ≤ r) :
    clCorner a r r = -(3 * (r : ℂ)) - r * a 2 := by
  unfold clCorner
  have h1 : ¬(r : ℤ) = (r : ℤ) - 2 := by omega
  have h2 : ¬r ≤ r - 1 := by omega
  have h3 : ¬r ≤ r - 3 := by omega
  have h4 : r ≤ r + 1 := by omega
  simp only [Nat.cast_inj, Finset.sum_ite_eq, Finset.mem_Icc, h1, h2, h3, h4, hr, and_true,
    and_false, ↓reduceIte, ite_self, add_sub_cancel_left]
  ring

private lemma cl_corner_zero {a : ℤ → ℂ} (hodd : ∀ j : ℤ, Odd j → a j = 0) {r : ℕ} (hr : 1 ≤ r)
    {k : ℤ} (hk : k < 0 ∨ (r : ℤ) < k ∨ ¬Even (k - r)) : clCorner a r k = 0 := by
  have hk' : k < 0 ∨ (r : ℤ) < k ∨ (k - r) % 2 = 1 := by
    rcases hk with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Int.not_even_iff.mp h))
  have ha : ∀ j : ℤ, (j = 1 ∨ j % 2 = 1) → a j = 0 := fun j hj =>
    hodd j (Int.odd_iff.mpr (by omega))
  unfold clCorner
  have e1 : (if k = r then 3 * (r : ℂ) else 0) = 0 :=
    ite_eq_right_iff.mpr fun h => absurd h (by omega)
  have e2 : (if 3 ≤ r then (if k = (r : ℤ) - 2 then (r : ℂ) - 2 else 0) else 0) = 0 := by
    split_ifs with h3 h4
    · omega
    · rfl
    · rfl
  have e3 : ∑ n ∈ Finset.Icc 1 (r + 1), (if k = n then (n : ℂ) * a ((r : ℤ) + 2 - n) else 0) =
      0 := Finset.sum_eq_zero fun n hn => by
    rw [Finset.mem_Icc] at hn
    split_ifs with h
    · rw [ha _ (by omega), mul_zero]
    · rfl
  have e4 : ∑ n ∈ Finset.Icc 1 (r - 1), (if k = n then (n : ℂ) * a ((r : ℤ) - n) else 0) =
      0 := Finset.sum_eq_zero fun n hn => by
    rw [Finset.mem_Icc] at hn
    split_ifs with h
    · rw [ha _ (by omega), mul_zero]
    · rfl
  have e5 : ∑ n ∈ Finset.Icc 1 (r - 3), (if k = n then (n : ℂ) * a ((r : ℤ) - 2 - n) else 0) =
      0 := Finset.sum_eq_zero fun n hn => by
    rw [Finset.mem_Icc] at hn
    split_ifs with h
    · rw [ha _ (by omega), mul_zero]
    · rfl
  rw [e1, e2, e3, e4, e5]
  ring

private lemma cl_sum_le {a : ℤ → ℂ} {B : ℝ} (hB : 0 ≤ B) {k : ℤ} {m M : ℕ} (hm : m ≤ M + 1)
    (f : ℕ → ℤ) (hf : ∀ n ∈ Finset.Icc 1 m, ‖a (f n)‖ ≤ B) :
    ‖∑ n ∈ Finset.Icc 1 m, (if k = n then (n : ℂ) * a (f n) else 0)‖ ≤ ((M : ℝ) + 1) ^ 2 * B := by
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ n ∈ Finset.Icc 1 m,
      ‖(if k = n then (n : ℂ) * a (f n) else 0)‖ ≤ ((M : ℝ) + 1) * B := by
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    split_ifs
    · rw [norm_mul, Complex.norm_natCast]
      have : (n : ℝ) ≤ M + 1 := by exact_mod_cast hn'.2.trans hm
      exact mul_le_mul this (hf n hn) (norm_nonneg _) (by positivity)
    · rw [norm_zero]; positivity
  refine (Finset.sum_le_sum h).trans ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have : ((m + 1 - 1 : ℕ) : ℝ) ≤ M + 1 := by
    rw [Nat.add_sub_cancel]; exact_mod_cast hm
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ M + 1) hB]

private lemma cl_corner_le {a : ℤ → ℂ} {B : ℝ} (hB : 0 ≤ B) {r M : ℕ} (hrM : r ≤ M)
    (ha : ∀ j : ℤ, 1 ≤ j → j ≤ M + 1 → ‖a j‖ ≤ B) (k : ℤ) :
    ‖clCorner a r k‖ ≤ 4 * M + 8 * ((M : ℝ) + 1) ^ 2 * B := by
  unfold clCorner
  have e1 : ‖(if k = r then 3 * (r : ℂ) else 0)‖ ≤ 3 * M := by
    split_ifs
    · rw [norm_mul, Complex.norm_natCast]
      have : (r : ℝ) ≤ M := by exact_mod_cast hrM
      norm_num; linarith
    · simp
  have e2 : ‖(if 3 ≤ r then (if k = (r : ℤ) - 2 then (r : ℂ) - 2 else 0) else 0)‖ ≤ M := by
    split_ifs with h3
    · have : ((r : ℂ) - 2) = ((r - 2 : ℕ) : ℂ) := by
        push_cast [Nat.cast_sub (by omega : 2 ≤ r)]; ring
      rw [this, Complex.norm_natCast]
      exact_mod_cast (Nat.sub_le r 2).trans hrM
    all_goals simp
  have e3 := cl_sum_le hB (k := k) (m := r + 1) (M := M) (a := a) (by omega)
    (fun n => (r : ℤ) + 2 - n) fun n hn => by
      rw [Finset.mem_Icc] at hn; exact ha _ (by omega) (by omega)
  have e4 := cl_sum_le hB (k := k) (m := r - 1) (M := M) (a := a) (by omega)
    (fun n => (r : ℤ) - n) fun n hn => by
      rw [Finset.mem_Icc] at hn; exact ha _ (by omega) (by omega)
  have e5 := cl_sum_le hB (k := k) (m := r - 3) (M := M) (a := a) (by omega)
    (fun n => (r : ℤ) - 2 - n) fun n hn => by
      rw [Finset.mem_Icc] at hn; exact ha _ (by omega) (by omega)
  generalize (if k = r then 3 * (r : ℂ) else 0) = x at e1 ⊢
  generalize (if 3 ≤ r then (if k = (r : ℤ) - 2 then (r : ℂ) - 2 else 0) else 0) = y at e2 ⊢
  generalize ∑ n ∈ Finset.Icc 1 (r + 1), (if k = n then (n : ℂ) * a ((r : ℤ) + 2 - n) else 0) =
    z at e3 ⊢
  generalize ∑ n ∈ Finset.Icc 1 (r - 1), (if k = n then (n : ℂ) * a ((r : ℤ) - n) else 0) =
    u at e4 ⊢
  generalize ∑ n ∈ Finset.Icc 1 (r - 3), (if k = n then (n : ℂ) * a ((r : ℤ) - 2 - n) else 0) =
    v at e5 ⊢
  rw [show -x - y - z - 6 * u - v = -(x + y + z + 6 * u + v) by ring, norm_neg]
  have t1 := norm_add_le (x + y + z + 6 * u) v
  have t2 := norm_add_le (x + y + z) (6 * u)
  have t3 := norm_add_le (x + y) z
  have t4 := norm_add_le x y
  rw [norm_mul, show ‖(6 : ℂ)‖ = 6 by norm_num] at t2
  linarith

/-! ### The structure of `A_0` -/

private lemma cl_norm_phase (E : ℝ) : ‖-normalPhase E‖ = 1 := by
  unfold normalPhase
  rw [neg_neg, show (2 : ℂ) * ((freeAngle E : ℂ) * Complex.I) =
    ((2 * freeAngle E : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `h_θ ≤ 1` on `|E| ≤ 1`. -/
private lemma cl_normalH {E : ℝ} (hE : |E| ≤ 1) : 0 ≤ normalH E ∧ normalH E ≤ 1 := by
  unfold normalH freeAngle
  rw [Real.sin_arccos]
  have h1 : (E / 2) ^ 2 ≤ 3 / 4 := by
    have := sq_abs E
    nlinarith [abs_nonneg E]
  have h2 : (1 / 2 : ℝ) ≤ √(1 - (E / 2) ^ 2) := by
    rw [show (1 / 2 : ℝ) = √((1 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  refine ⟨by positivity, inv_le_one_of_one_le₀ (by linarith)⟩

/-- The diagonal entry, the off-diagonal bound and the zero pattern of `A_0` in a column
`r > 0`. -/
private lemma cl_tri_pos {g E : ℝ} {R n M : ℕ} {B : ℝ} (hg : 0 < g) (hh : normalH E ^ 2 ≤ 1)
    (hB : 0 ≤ B) (hn : 1 ≤ n) (hnM : n ≤ M)
    (ha : ∀ j : ℤ, 1 ≤ j → j ≤ M + 1 → ‖center g E R j‖ ≤ B) {r : NzInt} (hr : r.1 = n)
    (hT : truncG 1 (corrUpd E R (.f r)) = C ((-normalPhase E) ^ r.1) *
      (X (.f r) + C (((normalH E ^ 2 : ℝ) : ℂ)) * X .γ * centerCorner r.1.toNat)) (k : NzInt) :
    corrMat0 g E R r r = (-normalPhase E) ^ r.1 *
        (1 - (((normalH E ^ 2 / g ^ 2 * |r.1| : ℝ) : ℂ)) * (3 + center g E R 2)) - 1 ∧
      (k ≠ r → ‖corrMat0 g E R k r‖ ≤ (4 * M + 8 * ((M : ℝ) + 1) ^ 2 * B) / g ^ 2) ∧
      (k.1 < 0 ∨ r.1 < k.1 ∨ ¬Even (k.1 - r.1) → corrMat0 g E R k r = 0) := by
  have htn : r.1.toNat = n := by simp [hr]
  have hF := cl_corrMat0_pos (g := g) hT
  rw [htn] at hF
  refine ⟨?_, fun hk => ?_, fun hk => ?_⟩
  · simp only [hF r, ↓reduceIte]
    rw [hr, cl_corner_diag _ hn, abs_of_nonneg (by positivity : (0 : ℤ) ≤ n)]
    push_cast
    ring
  · simp only [hF k, hk, ↓reduceIte]
    rw [zero_add, norm_mul, norm_mul, norm_zpow, cl_norm_phase, one_zpow,
      one_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have h1 := cl_corner_le hB hnM ha k.1
    have h2 : normalH E ^ 2 / g ^ 2 ≤ 1 / g ^ 2 := div_le_div_of_nonneg_right hh (by positivity)
    calc normalH E ^ 2 / g ^ 2 * ‖clCorner (center g E R) n k.1‖
        ≤ 1 / g ^ 2 * (4 * M + 8 * ((M : ℝ) + 1) ^ 2 * B) :=
          mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · have hne : k ≠ r := fun h => by
      subst h
      rcases hk with h | h | h
      · omega
      · omega
      · exact h (by simp)
    simp only [hF k, hne, ↓reduceIte]
    rw [cl_corner_zero (cl_center g E R).2.2.2 hn (by rwa [← hr]), mul_zero,
      zero_add]

/-- The bound `|a_j| ≤ K` for `1 ≤ j ≤ M + 1` from `center_bounds`. -/
private lemma cl_center_le (R M : ℕ) :
    ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ K g₀ : ℝ, 0 < K ∧ 1 ≤ g₀ ∧ ∀ g : ℝ, g₀ ≤ g → ∀ E : ℝ, |E| ≤ E₁ →
      ∀ j : ℤ, 1 ≤ j → j ≤ M + 1 → ‖center g E R j‖ ≤ K := by
  obtain ⟨E₁, hE₁, c, K, g₀, hc, hK, hg₀, h⟩ := center_bounds R
    ((Finset.range (M + 1)).image fun j : ℕ => (⟨(j : ℤ) + 1, by omega⟩ : NzInt))
  refine ⟨E₁, hE₁, K, g₀, hK, hg₀, fun g hg E hE j hj1 hj2 => ?_⟩
  have hmem : (⟨((j - 1).toNat : ℤ) + 1, by omega⟩ : NzInt) ∈
      (Finset.range (M + 1)).image fun j : ℕ => (⟨(j : ℤ) + 1, by omega⟩ : NzInt) :=
    Finset.mem_image.mpr ⟨(j - 1).toNat, Finset.mem_range.mpr (by omega), rfl⟩
  have := ((h g hg E hE).2 _ hmem).2.1
  have hj : ((j - 1).toNat : ℤ) + 1 = j := by omega
  simpa only [hj] using this

/-- The structure of `A_0` (Section 11.3.4 [lg:sec:cocycle-correction], from (11.51)
[lg:eq:center-corner] at `m = a`, `f = F`): on a window fixed after `R` and the index set, for
large `g`, each column `r` has the diagonal entry
`(−e^{−2iθ})^r [1 − |r| h_θ² g⁻² (3 + a_{2 sign r})] − 1`, off-diagonal entries at most `K g⁻²`,
and vanishes in the rows of the opposite sign, of larger `|k|`, or of the other parity. -/
theorem corrMat0_tri (R : ℕ) (Ks : Finset NzInt) :
    ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ K g₀ : ℝ, 0 < K ∧ 1 ≤ g₀ ∧ ∀ g : ℝ, g₀ ≤ g → ∀ E : ℝ, |E| ≤ E₁ →
      ∀ r ∈ Ks, ∀ k : NzInt,
        corrMat0 g E R r r = (-normalPhase E) ^ r.1 *
            (1 - (((normalH E ^ 2 / g ^ 2 * |r.1| : ℝ) : ℂ)) *
              (3 + center g E R (2 * Int.sign r.1))) - 1 ∧
          (k ≠ r → ‖corrMat0 g E R k r‖ ≤ K / g ^ 2) ∧
          (k.1 * r.1 < 0 ∨ |r.1| < |k.1| ∨ ¬ Even (k.1 - r.1) → corrMat0 g E R k r = 0) := by
  set M := Ks.sup fun r => r.1.natAbs with hM
  obtain ⟨E₁, hE₁, hT⟩ := truncG_one_corrUpd R
    (Ks ∪ Ks.image fun r : NzInt => (⟨-r.1, neg_ne_zero.mpr r.2⟩ : NzInt))
  obtain ⟨E₂, hE₂, B, g₀, hB, hg₀, ha⟩ := cl_center_le R M
  refine ⟨min (min E₁ E₂) 1, lt_min (lt_min hE₁ hE₂) one_pos,
    (4 * M + 8 * ((M : ℝ) + 1) ^ 2 * B) + 1, g₀, by positivity, hg₀,
    fun g hg E hE r hr k => ?_⟩
  have hE1 : |E| ≤ E₁ := hE.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hE2 : |E| ≤ E₂ := hE.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hE3 : |E| ≤ 1 := hE.trans (min_le_right _ _)
  have hg0 : 0 < g := by linarith
  have hh : normalH E ^ 2 ≤ 1 := by
    obtain ⟨h0, h1⟩ := cl_normalH hE3
    nlinarith
  have ha' := ha g hg E hE2
  have hrM : r.1.natAbs ≤ M := Finset.le_sup (f := fun r : NzInt => r.1.natAbs) hr
  have hKle : (4 * M + 8 * ((M : ℝ) + 1) ^ 2 * B) / g ^ 2 ≤
      (4 * M + 8 * ((M : ℝ) + 1) ^ 2 * B + 1) / g ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  rcases lt_or_gt_of_ne r.2 with hneg | hpos
  · -- a column `r < 0`, by conjugation
    set r' : NzInt := ⟨-r.1, neg_ne_zero.mpr r.2⟩ with hr'
    have hr'mem : r' ∈ Ks ∪ Ks.image fun r : NzInt => (⟨-r.1, neg_ne_zero.mpr r.2⟩ : NzInt) :=
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, hr, rfl⟩)
    have hr'n : r'.1 = (r'.1.toNat : ℤ) := by simp only [hr']; omega
    obtain ⟨-, hTr⟩ := hT E hE1 r' hr'mem (by simp only [hr']; omega)
    have hconj : ∀ k : NzInt, corrMat0 g E R k r =
        star (corrMat0 g E R ⟨-k.1, neg_ne_zero.mpr k.2⟩ r') := fun k => by
      rw [← cl_corrMat0_neg]
      congr 1 <;> exact Subtype.ext (by simp [hr'])
    obtain ⟨hd, ho, hz⟩ := cl_tri_pos hg0 hh hB.le (n := r'.1.toNat) (M := M)
      (by simp only [hr']; omega) (by simp only [hr']; omega) ha' hr'n hTr
      ⟨-k.1, neg_ne_zero.mpr k.2⟩
    refine ⟨?_, fun hk => ?_, fun hk => ?_⟩
    · have hrr : (⟨-r.1, neg_ne_zero.mpr r.2⟩ : NzInt) = r' := rfl
      rw [hconj, hrr, hd]
      have hsg : 2 * Int.sign r.1 = -2 := by rw [Int.sign_eq_neg_one_of_neg hneg]; rfl
      have hab : |r'.1| = |r.1| := by simp only [hr', abs_neg]
      have hzp : star ((-normalPhase E) ^ r'.1) = (-normalPhase E) ^ r.1 := by
        have h1 : ‖(-normalPhase E) ^ r'.1‖ = 1 := by rw [norm_zpow, cl_norm_phase, one_zpow]
        have h2 : star ((-normalPhase E) ^ r'.1) = ((-normalPhase E) ^ r'.1)⁻¹ :=
          (Complex.inv_eq_conj h1).symm
        rw [h2, ← zpow_neg]
        congr 1
        simp [hr']
      rw [hsg, (center_zero_odd_neg g E R 2).2.2, hab, star_sub, star_mul', hzp, star_sub,
        star_mul', star_add, star_one, Complex.star_def, Complex.conj_ofReal, map_ofNat]
    · rw [hconj, norm_star]
      exact (ho fun h => hk (Subtype.ext (by simpa [hr'] using congrArg Subtype.val h))).trans hKle
    · rw [hconj, hz, star_zero]
      have hkr : k.1 * r.1 < 0 ∨ |r.1| < |k.1| ∨ ¬Even (k.1 - r.1) := hk
      simp only [hr']
      rcases hkr with h | h | h
      · left
        nlinarith
      · rcases le_or_gt 0 k.1 with h0 | h0
        · left
          rw [abs_of_neg hneg, abs_of_nonneg h0] at h
          omega
        · right; left
          rw [abs_of_neg hneg, abs_of_neg h0] at h
          omega
      · right; right
        rwa [show -k.1 - -r.1 = -(k.1 - r.1) by ring, even_neg]
  · -- a column `r > 0`
    have hrn : r.1 = (r.1.toNat : ℤ) := by omega
    obtain ⟨-, hTr⟩ := hT E hE1 r (Finset.mem_union_left _ hr) hpos
    obtain ⟨hd, ho, hz⟩ := cl_tri_pos hg0 hh hB.le (n := r.1.toNat) (M := M) (by omega)
      (by omega) ha' hrn hTr k
    refine ⟨?_, fun hk => (ho hk).trans hKle, fun hk => hz ?_⟩
    · rw [hd, Int.sign_eq_one_of_pos hpos]
      rfl
    · rcases hk with h | h | h
      · left
        nlinarith
      · rcases le_or_gt 0 k.1 with h0 | h0
        · right; left
          rw [abs_of_pos hpos, abs_of_nonneg h0] at h
          exact h
        · left; exact h0
      · right; right; exact h

/-! ### A weighted `ℓ¹` norm of polynomials -/

/-- The weight `∏_v ρ_v^{d_v}` of a monomial `d`. -/
private def clWt (ρ : ObsVar → ℝ) (d : ObsVar →₀ ℕ) : ℝ := d.prod fun v n => ρ v ^ n

/-- The weighted `ℓ¹` norm `Σ_d |p_d| ρ^d` of a polynomial. -/
private def clNorm (ρ : ObsVar → ℝ) (p : ObsPoly) : ℝ :=
  ∑ d ∈ p.support, ‖p.coeff d‖ * clWt ρ d

private lemma clWt_nonneg {ρ : ObsVar → ℝ} (hρ : ∀ v, 0 ≤ ρ v) (d : ObsVar →₀ ℕ) :
    0 ≤ clWt ρ d :=
  Finset.prod_nonneg fun v _ => pow_nonneg (hρ v) _

private lemma clWt_add (ρ : ObsVar → ℝ) (a b : ObsVar →₀ ℕ) :
    clWt ρ (a + b) = clWt ρ a * clWt ρ b :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) fun _ _ _ => pow_add _ _ _

private lemma clWt_single (ρ : ObsVar → ℝ) (v : ObsVar) :
    clWt ρ (Finsupp.single v 1) = ρ v := by
  unfold clWt
  rw [Finsupp.prod_single_index (by rw [pow_zero]), pow_one]

private lemma clNorm_eq (ρ : ObsVar → ℝ) {p : ObsPoly} {T : Finset (ObsVar →₀ ℕ)}
    (hT : p.support ⊆ T) : clNorm ρ p = ∑ d ∈ T, ‖p.coeff d‖ * clWt ρ d := by
  unfold clNorm
  refine Finset.sum_subset hT fun d _ hd => ?_
  rw [notMem_support_iff.mp hd, norm_zero, zero_mul]

private lemma clNorm_nonneg {ρ : ObsVar → ℝ} (hρ : ∀ v, 0 ≤ ρ v) (p : ObsPoly) :
    0 ≤ clNorm ρ p :=
  Finset.sum_nonneg fun d _ => mul_nonneg (norm_nonneg _) (clWt_nonneg hρ d)

private lemma clNorm_add_le {ρ : ObsVar → ℝ} (hρ : ∀ v, 0 ≤ ρ v) (p q : ObsPoly) :
    clNorm ρ (p + q) ≤ clNorm ρ p + clNorm ρ q := by
  rw [clNorm_eq ρ (support_add (p := p) (q := q)),
    clNorm_eq ρ (Finset.subset_union_left (s₁ := p.support) (s₂ := q.support)),
    clNorm_eq ρ (Finset.subset_union_right (s₁ := p.support) (s₂ := q.support)),
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun d _ => ?_
  rw [show (p + q).coeff d = p.coeff d + q.coeff d by simp, ← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (clWt_nonneg hρ d)

private lemma clNorm_neg (ρ : ObsVar → ℝ) (p : ObsPoly) : clNorm ρ (-p) = clNorm ρ p := by
  unfold clNorm
  rw [support_neg]
  simp only [coeff_neg, norm_neg]

private lemma clNorm_sub_le {ρ : ObsVar → ℝ} (hρ : ∀ v, 0 ≤ ρ v) (p q : ObsPoly) :
    clNorm ρ (p - q) ≤ clNorm ρ p + clNorm ρ q := by
  rw [sub_eq_add_neg, ← clNorm_neg ρ q]
  exact clNorm_add_le hρ _ _

private lemma clNorm_sum_le {ι : Type*} {ρ : ObsVar → ℝ} (hρ : ∀ v, 0 ≤ ρ v) (s : Finset ι)
    (f : ι → ObsPoly) : clNorm ρ (∑ i ∈ s, f i) ≤ ∑ i ∈ s, clNorm ρ (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [clNorm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (clNorm_add_le hρ _ _).trans (add_le_add le_rfl ih)

private lemma clNorm_monomial (ρ : ObsVar → ℝ) (e : ObsVar →₀ ℕ) (c : ℂ) :
    clNorm ρ (monomial e c) = ‖c‖ * clWt ρ e := by
  rw [clNorm_eq ρ support_monomial_subset, Finset.sum_singleton]
  simp [coeff_monomial]

private lemma clNorm_C (ρ : ObsVar → ℝ) (c : ℂ) : clNorm ρ (C c) = ‖c‖ := by
  rw [C_apply, clNorm_monomial]
  simp [clWt]

private lemma clNorm_X (ρ : ObsVar → ℝ) (v : ObsVar) : clNorm ρ (X v) = ρ v := by
  rw [X, clNorm_monomial, clWt_single, norm_one, one_mul]

private lemma clNorm_mul_le {ρ : ObsVar → ℝ} (hρ : ∀ v, 0 ≤ ρ v) (p q : ObsPoly) :
    clNorm ρ (p * q) ≤ clNorm ρ p * clNorm ρ q := by
  have h : p * q = ∑ a ∈ p.support, ∑ b ∈ q.support,
      monomial (a + b) (p.coeff a * q.coeff b) := by
    conv_lhs => rw [p.as_sum, q.as_sum]
    rw [Finset.sum_mul_sum]
    simp only [monomial_mul_monomial]
  rw [h]
  refine (clNorm_sum_le hρ _ _).trans ?_
  unfold clNorm
  rw [Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun a _ => (clNorm_sum_le hρ _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [clNorm_monomial, norm_mul, clWt_add]
  ring

private lemma clNorm_one (ρ : ObsVar → ℝ) : clNorm ρ 1 = 1 := by
  rw [← C_1, clNorm_C, norm_one]

private lemma clNorm_pow_le {ρ : ObsVar → ℝ} (hρ : ∀ v, 0 ≤ ρ v) (p : ObsPoly) (n : ℕ) :
    clNorm ρ (p ^ n) ≤ clNorm ρ p ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, clNorm_one]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (clNorm_mul_le hρ _ _).trans (mul_le_mul_of_nonneg_right ih (clNorm_nonneg hρ p))

private lemma clNorm_prod_le {ι : Type*} {ρ : ObsVar → ℝ} (hρ : ∀ v, 0 ≤ ρ v) (s : Finset ι)
    (f : ι → ObsPoly) : clNorm ρ (∏ i ∈ s, f i) ≤ ∏ i ∈ s, clNorm ρ (f i) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, clNorm_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (clNorm_mul_le hρ _ _).trans (mul_le_mul_of_nonneg_left ih (clNorm_nonneg hρ _))

/-- Composition: `‖p(ψ)‖_ρ ≤ ‖p‖_{ρ'}` when `‖ψ_v‖_ρ ≤ ρ'_v` on the variables of `p`. -/
private lemma clNorm_bind₁_le {ρ ρ' : ObsVar → ℝ} (hρ : ∀ v, 0 ≤ ρ v)
    (ψ : ObsVar → ObsPoly) (p : ObsPoly) (h : ∀ v ∈ p.vars, clNorm ρ (ψ v) ≤ ρ' v) :
    clNorm ρ (bind₁ ψ p) ≤ clNorm ρ' p := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine (clNorm_sum_le hρ _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  rw [bind₁_monomial]
  refine (clNorm_mul_le hρ _ _).trans ?_
  rw [clNorm_C]
  refine mul_le_mul_of_nonneg_left ((clNorm_prod_le hρ _ _).trans ?_) (norm_nonneg _)
  refine Finset.prod_le_prod₀ (fun v _ => clNorm_nonneg hρ _) fun v hv => ?_
  have hvar : v ∈ p.vars := (mem_vars_iff_mem_support v).2 ⟨d, hd, hv⟩
  exact (clNorm_pow_le hρ _ _).trans (pow_le_pow_left₀ (clNorm_nonneg hρ _) (h v hvar) _)

/-- Coefficientwise domination. -/
private lemma clNorm_mono {ρ : ObsVar → ℝ} (hρ : ∀ v, 0 ≤ ρ v) {p q : ObsPoly}
    (h : ∀ d, ‖q.coeff d‖ ≤ ‖p.coeff d‖) : clNorm ρ q ≤ clNorm ρ p := by
  have hs : q.support ⊆ p.support := fun d hd => by
    rw [mem_support_iff] at hd ⊢
    intro h0
    have := h d
    rw [h0, norm_zero] at this
    exact hd (norm_le_zero_iff.mp this)
  rw [clNorm_eq ρ hs]
  exact Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_right (h d) (clWt_nonneg hρ d)

/-- A bound from a support and a coefficient bound. -/
private lemma clNorm_le_of_support {ρ : ObsVar → ℝ} (hρ : ∀ v, 0 ≤ ρ v) {p : ObsPoly}
    {S : Finset (ObsVar →₀ ℕ)} {K : ℝ} (hS : p.support ⊆ S) (hK : ∀ d, ‖p.coeff d‖ ≤ K) :
    clNorm ρ p ≤ ∑ d ∈ S, K * clWt ρ d := by
  rw [clNorm_eq ρ hS]
  exact Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_right (hK d) (clWt_nonneg hρ d)

/-- A single coefficient. -/
private lemma cl_coeff_le_clNorm {ρ : ObsVar → ℝ} (hρ : ∀ v, 0 ≤ ρ v) (p : ObsPoly)
    (e : ObsVar →₀ ℕ) : ‖p.coeff e‖ * clWt ρ e ≤ clNorm ρ p := by
  by_cases he : e ∈ p.support
  · exact Finset.single_le_sum (f := fun d => ‖p.coeff d‖ * clWt ρ d)
      (fun d _ => mul_nonneg (norm_nonneg _) (clWt_nonneg hρ d)) he
  · rw [notMem_support_iff.mp he, norm_zero, zero_mul]
    exact clNorm_nonneg hρ p

/-- The weight `ρ_γ = t`, `ρ_v = B` otherwise. -/
private def clRho (t B : ℝ) (v : ObsVar) : ℝ := if v = .γ then t else B

private lemma clRho_nonneg {t B : ℝ} (ht : 0 ≤ t) (hB : 0 ≤ B) (v : ObsVar) : 0 ≤ clRho t B v := by
  unfold clRho
  split_ifs <;> assumption

private lemma clWt_split (t B : ℝ) (d : ObsVar →₀ ℕ) :
    clWt (clRho t B) d = t ^ (d .γ) * clWt (clRho 1 B) d := by
  unfold clWt clRho
  rw [Finsupp.prod, Finsupp.prod]
  have h : ∀ v, (if v = ObsVar.γ then t else B) ^ (d v) =
      t ^ (if v = ObsVar.γ then d v else 0) * (if v = ObsVar.γ then 1 else B) ^ (d v) := by
    intro v
    split_ifs <;> simp
  rw [Finset.prod_congr rfl fun v _ => h v, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.sum_ite_eq']
  split_ifs with hγ
  · rfl
  · rw [Finsupp.notMem_support_iff.mp hγ]

/-- Monomials of order at least `γ²` gain the factor `t²`. -/
private lemma clNorm_gam2 {t B : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hB : 0 ≤ B) {p : ObsPoly}
    (hp : ∀ d ∈ p.support, 2 ≤ d .γ) : clNorm (clRho t B) p ≤ t ^ 2 * clNorm (clRho 1 B) p := by
  unfold clNorm
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun d hd => ?_
  rw [clWt_split, mul_left_comm]
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (norm_nonneg _)
    (clWt_nonneg (clRho_nonneg zero_le_one hB) d))
  exact pow_le_pow_of_le_one ht ht1 (hp d hd)

/-- The basic estimate: for `p` of order at least `γ²`, `|[F_k] p|_{M=a}| ≤ g⁻⁴ ‖p‖_{1, B}`
when `|a_j| ≤ B` on the variables `m_j` of `p`. -/
private lemma cl_linCoeff_le {g B : ℝ} (hg : 1 ≤ g) (hB : 1 ≤ B) {a : ℤ → ℂ} {p : ObsPoly}
    (ha : ∀ j : NzInt, ObsVar.m j ∈ p.vars → ‖a j.1‖ ≤ B) (hp : ∀ d ∈ p.support, 2 ≤ d .γ)
    (k : NzInt) : ‖linCoeff g a k p‖ ≤ clNorm (clRho 1 B) p / g ^ 4 := by
  set t : ℝ := (g ^ 2)⁻¹ with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  have hρ := clRho_nonneg ht0 (by linarith : (0 : ℝ) ≤ B)
  have h1 : ‖linCoeff g a k p‖ ≤ clNorm (clRho t B) (centerSub g a p) := by
    refine le_trans ?_ (cl_coeff_le_clNorm hρ _ (Finsupp.single (.f k) 1))
    rw [clWt_single]
    unfold clRho
    simp only [reduceCtorEq, ↓reduceIte]
    exact le_mul_of_one_le_right (norm_nonneg _) hB
  have h2 : clNorm (clRho t B) (centerSub g a p) ≤ clNorm (clRho t B) p := by
    unfold centerSub
    rw [aeval_eq_bind₁]
    refine clNorm_bind₁_le hρ _ p fun v hv => ?_
    cases v with
    | m j =>
      simp only
      rw [clNorm_C]
      simpa [clRho] using ha j hv
    | f j =>
      simp only
      rw [clNorm_X]
    | w =>
      simp only
      rw [show (0 : ObsPoly) = C 0 from C_0.symm, clNorm_C, norm_zero]
      exact hρ _
    | γ =>
      simp only
      rw [clNorm_C, Complex.norm_real, Real.norm_of_nonneg ht0]
      simp [clRho, ht]
  have h3 := clNorm_gam2 ht0 ht1 (by linarith : (0 : ℝ) ≤ B) hp
  calc ‖linCoeff g a k p‖ ≤ t ^ 2 * clNorm (clRho 1 B) p := h1.trans (h2.trans h3)
    _ = clNorm (clRho 1 B) p / g ^ 4 := by rw [ht]; field_simp

private lemma cl_linCoeff_sub (g : ℝ) (a : ℤ → ℂ) (k : NzInt) (p q : ObsPoly) :
    linCoeff g a k (p - q) = linCoeff g a k p - linCoeff g a k q := by
  unfold linCoeff
  rw [map_sub, coeff_sub]

/-- The indices of `m_k`, `f_k`. -/
private def clIdx : ObsVar → Finset NzInt
  | .m k => {k}
  | .f k => {k}
  | .w => ∅
  | .γ => ∅

/-- The indices of the variables of the monomials in `S`. -/
private def clIdxS (S : Finset (ObsVar →₀ ℕ)) : Finset NzInt :=
  S.biUnion fun d => d.support.biUnion clIdx

private lemma cl_mem_idxS {p : ObsPoly} {S : Finset (ObsVar →₀ ℕ)} (hS : p.support ⊆ S)
    {v : ObsVar} (hv : v ∈ p.vars) {j : NzInt} (hj : j ∈ clIdx v) : j ∈ clIdxS S := by
  obtain ⟨d, hd, hvd⟩ := (mem_vars_iff_mem_support v).1 hv
  exact Finset.mem_biUnion.mpr ⟨d, hS hd, Finset.mem_biUnion.mpr ⟨v, hvd, hj⟩⟩

private lemma cl_coeff_sub_truncG (N : ℕ) (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (p - truncG N p).coeff d = if d .γ ≤ N then 0 else p.coeff d := by
  rw [coeff_sub, cl_coeff_truncG]
  split_ifs <;> simp

private lemma cl_support_sub_truncG (N : ℕ) (p : ObsPoly) :
    (p - truncG N p).support ⊆ p.support ∧ ∀ d ∈ (p - truncG N p).support, N + 1 ≤ d .γ := by
  refine ⟨fun d hd => ?_, fun d hd => ?_⟩ <;>
  · rw [mem_support_iff, cl_coeff_sub_truncG] at hd
    split_ifs at hd with h
    · exact absurd rfl hd
    · first
        | exact mem_support_iff.mpr hd
        | omega

/-- `‖A − A_0‖ = O(g⁻⁴)` entrywise (Section 11.3.4 [lg:sec:cocycle-correction]). -/
theorem corrMat_sub_corrMat0_le (R : ℕ) (Ks : Finset NzInt) :
    ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ K g₀ : ℝ, 0 < K ∧ 1 ≤ g₀ ∧ ∀ g : ℝ, g₀ ≤ g → ∀ E : ℝ, |E| ≤ E₁ →
      ∀ r ∈ Ks, ∀ k : NzInt, ‖corrMat g E R k r - corrMat0 g E R k r‖ ≤ K / g ^ 4 := by
  obtain ⟨E₁, hE₁, S, Kc, hKc, hS⟩ := corrCoeff_bounded R Ks
  obtain ⟨E₂, hE₂, c, Kb, g₀, hc, hKb, hg₀, hb⟩ := center_bounds R (clIdxS S)
  set B := max Kb 1 with hB
  have hB1 : 1 ≤ B := le_max_right _ _
  have hρ := clRho_nonneg zero_le_one (by linarith : (0 : ℝ) ≤ B)
  set K₀ := ∑ d ∈ S, Kc * clWt (clRho 1 B) d with hK₀
  have hK₀0 : 0 ≤ K₀ := Finset.sum_nonneg fun d _ => mul_nonneg hKc.le (clWt_nonneg hρ d)
  refine ⟨min E₁ E₂, lt_min hE₁ hE₂, K₀ + 1, g₀, by linarith, hg₀,
    fun g hg E hE r hr k => ?_⟩
  have hE1 : |E| ≤ E₁ := hE.trans (min_le_left _ _)
  have hE2 : |E| ≤ E₂ := hE.trans (min_le_right _ _)
  have hg1 : 1 ≤ g := hg₀.trans hg
  obtain ⟨-, -, hPS, hPK⟩ := hS E hE1 r hr (.f r) (by simp)
  set P := corrUpd E R (.f r) with hP
  have hdiff : corrMat g E R k r - corrMat0 g E R k r =
      linCoeff g (center g E R) k (P - truncG 1 P) := by
    unfold corrMat corrMat0
    rw [← cl_linCoeff_sub]
    congr 1
    ring
  obtain ⟨hsup, hγ⟩ := cl_support_sub_truncG 1 P
  have ha : ∀ j : NzInt, ObsVar.m j ∈ (P - truncG 1 P).vars → ‖center g E R j.1‖ ≤ B :=
    fun j hj => ((((hb g hg E hE2).2 j
      (cl_mem_idxS (hsup.trans hPS) hj (by simp [clIdx]))).2.1).trans (le_max_left _ _))
  have hnorm : clNorm (clRho 1 B) (P - truncG 1 P) ≤ K₀ := by
    refine clNorm_le_of_support hρ (hsup.trans hPS) fun d => ?_
    rw [cl_coeff_sub_truncG]
    split_ifs
    · rw [norm_zero]; exact hKc.le
    · exact (hPK d).2.2
  rw [hdiff]
  refine (cl_linCoeff_le hg1 hB1 ha hγ k).trans ?_
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-! ### The order in `γ` of the expansion in the corrected coordinates -/

private lemma cl_dvd_iff (n : ℕ) (p : ObsPoly) :
    X .γ ^ n ∣ p ↔ ∀ d ∈ p.support, n ≤ d .γ := by
  have h : ({X .γ ^ n} : Set ObsPoly) =
      (fun s => monomial s (1 : ℂ)) '' {Finsupp.single ObsVar.γ n} := by
    rw [Set.image_singleton, X_pow_eq_monomial]
  rw [← Ideal.mem_span_singleton, h, mem_ideal_span_monomial_image]
  simp [Finsupp.single_le_iff]

private lemma cl_support_truncG (N : ℕ) (p : ObsPoly) : (truncG N p).support ⊆ p.support := by
  intro d hd
  rw [mem_support_iff, cl_coeff_truncG] at hd
  rw [mem_support_iff]
  split_ifs at hd
  · exact hd
  · exact absurd rfl hd

private lemma cl_dvd_truncG {n N : ℕ} {p : ObsPoly} (h : X .γ ^ n ∣ p) :
    X .γ ^ n ∣ truncG N p := by
  rw [cl_dvd_iff] at h ⊢
  exact fun d hd => h d (cl_support_truncG N p hd)

private lemma cl_dvd_sub_truncG (N : ℕ) (p : ObsPoly) : X .γ ^ (N + 1) ∣ p - truncG N p :=
  (cl_dvd_iff _ _).2 (cl_support_sub_truncG N p).2

private lemma cl_truncG_X {N : ℕ} (hN : 1 ≤ N) (v : ObsVar) : truncG N (X v) = X v := by
  ext d
  rw [cl_coeff_truncG]
  split_ifs with hd
  · rfl
  · rw [coeff_X]
    split_ifs with h2
    · exfalso
      subst h2
      cases v <;> simp_all
    · rfl

/-- `ψ ≡ X` modulo `γ` on every variable gives `p(ψ) ≡ p` modulo `γ`. -/
private lemma cl_bind₁_sub {ψ : ObsVar → ObsPoly} (hψ : ∀ v, X .γ ∣ ψ v - X v) (p : ObsPoly) :
    X .γ ∣ bind₁ ψ p - p := by
  set I : Ideal ObsPoly := Ideal.span {X .γ}
  have h : (Ideal.Quotient.mkₐ ℂ I).comp (bind₁ ψ) = Ideal.Quotient.mkₐ ℂ I := by
    refine MvPolynomial.algHom_ext fun v => ?_
    rw [AlgHom.comp_apply, bind₁_X_right, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact Ideal.mem_span_singleton.mpr (hψ v)
  have h' := DFunLike.congr_fun h p
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at h'
  exact Ideal.mem_span_singleton.mp h'

private lemma cl_revCoord_sub {N : ℕ} (hN : 1 ≤ N) {σ : ObsVar → ObsPoly}
    (hσ : ∀ v, X ObsVar.γ ∣ σ v - X v) (r : ℕ) :
    ∀ v, X ObsVar.γ ∣ revCoord N σ r v - X v := by
  induction r with
  | zero =>
    intro v
    rw [show revCoord N σ 0 v = X v from rfl, sub_self]
    exact dvd_zero _
  | succ r ih =>
    intro v
    have hγ : X ObsVar.γ ∣ revCoord N σ r ObsVar.γ := by
      have e : revCoord N σ r ObsVar.γ =
          (revCoord N σ r ObsVar.γ - X ObsVar.γ) + X ObsVar.γ := by ring
      rw [e]
      exact dvd_add (ih ObsVar.γ) dvd_rfl
    have hb : X ObsVar.γ ∣ bind₁ (revCoord N σ r) (σ v - X v) := by
      obtain ⟨q, hq⟩ := hσ v
      rw [hq, map_mul, bind₁_X_right]
      exact dvd_mul_of_dvd_left hγ _
    have e : revCoord N σ (r + 1) v = truncG N (X v - bind₁ (revCoord N σ r) (σ v - X v)) := rfl
    rw [e, map_sub, cl_truncG_X hN, sub_sub_cancel_left]
    have h := cl_dvd_truncG (n := 1) (N := N) (p := bind₁ (revCoord N σ r) (σ v - X v))
      (by rw [pow_one]; exact hb)
    rw [pow_one] at h
    exact dvd_neg.mpr h

private lemma cl_corrCoord_sub (E : ℝ) (R : ℕ) (v : ObsVar) : X .γ ∣ corrCoord E R v - X v := by
  cases v with
  | m k =>
    have h := cl_dvd_sub_truncG 0 (corrObsM E R k)
    rw [(corrObs_form E R k).1, zero_add, pow_one] at h
    exact h
  | f k =>
    have h := cl_dvd_sub_truncG 0 (corrObsF E R k)
    rw [(corrObs_form E R k).2.2.2.1, zero_add, pow_one] at h
    exact h
  | w => exact ⟨0, by rw [mul_zero]; exact sub_eq_zero.mpr rfl⟩
  | γ => exact ⟨0, by rw [mul_zero]; exact sub_eq_zero.mpr rfl⟩

private lemma cl_invCoord_sub (E : ℝ) (R : ℕ) (v : ObsVar) : X .γ ∣ invCoord E R v - X v :=
  cl_revCoord_sub (by omega) (cl_corrCoord_sub E R) (R + 2) v

private lemma cl_invCoord_γ (E : ℝ) (R : ℕ) : invCoord E R .γ = X .γ := by
  rw [invCoord, revCoord]
  beta_reduce
  rw [show corrCoord E R .γ = X .γ from rfl, sub_self, map_zero, sub_zero]
  exact cl_truncG_X (by omega) _

private lemma cl_invCoord_w (E : ℝ) (R : ℕ) : invCoord E R .w = X .w := by
  rw [invCoord, revCoord]
  beta_reduce
  rw [show corrCoord E R .w = X .w from rfl, sub_self, map_zero, sub_zero]
  exact cl_truncG_X (by omega) _

/-- The term `h_θ² γ c_1` of the expansion. -/
private def clZ (E : ℝ) : ObsPoly := C (((normalH E ^ (2 * 1) : ℝ) : ℂ)) * X .γ ^ 1 * incWick 1

private lemma cl_bind_incPoly_sub (E : ℝ) (R : ℕ) :
    X .γ ^ 2 ∣ bind₁ (invCoord E R) (incPoly E R) - clZ E := by
  have hterm : ∀ (c : ℂ) (r : ℕ), bind₁ (invCoord E R) (C c * X .γ ^ r * incWick r) =
      C c * X .γ ^ r * bind₁ (invCoord E R) (incWick r) := by
    intro c r
    rw [map_mul, map_mul, map_pow, bind₁_C_right, bind₁_X_right, cl_invCoord_γ]
  unfold incPoly
  rw [map_sum, show R + 3 = R + 1 + 1 + 1 from rfl, Finset.sum_range_succ',
    Finset.sum_range_succ']
  simp only [hterm, (wickMap_zero_incWick_zero 0).2, map_zero, mul_zero, add_zero, zero_add]
  have e : ∑ i ∈ Finset.range (R + 1), C (((normalH E ^ (2 * (i + 1 + 1)) : ℝ) : ℂ)) *
        X .γ ^ (i + 1 + 1) * bind₁ (invCoord E R) (incWick (i + 1 + 1)) +
      C (((normalH E ^ (2 * 1) : ℝ) : ℂ)) * X .γ ^ 1 * bind₁ (invCoord E R) (incWick 1) -
      clZ E = ∑ i ∈ Finset.range (R + 1), C (((normalH E ^ (2 * (i + 1 + 1)) : ℝ) : ℂ)) *
        X .γ ^ (i + 1 + 1) * bind₁ (invCoord E R) (incWick (i + 1 + 1)) +
      C (((normalH E ^ (2 * 1) : ℝ) : ℂ)) * X .γ ^ 1 *
        (bind₁ (invCoord E R) (incWick 1) - incWick 1) := by
    unfold clZ
    ring
  rw [e]
  refine dvd_add (Finset.dvd_sum fun i _ => ?_) ?_
  · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow _ (by omega)) _) _
  · obtain ⟨q, hq⟩ := cl_bind₁_sub (cl_invCoord_sub E R) (incWick 1)
    rw [hq]
    exact ⟨C (((normalH E ^ (2 * 1) : ℝ) : ℂ)) * q, by ring⟩

private lemma cl_incCorr_sub (E : ℝ) (R : ℕ) :
    ∀ d ∈ (incCorr E R - clZ E).support, 2 ≤ d .γ := by
  rw [← cl_dvd_iff]
  have e : incCorr E R - clZ E = truncG (R + 2) (bind₁ (invCoord E R) (incPoly E R) - clZ E) -
      (clZ E - truncG (R + 2) (clZ E)) := by
    unfold incCorr
    rw [map_sub]
    ring
  rw [e]
  exact dvd_sub (cl_dvd_truncG (cl_bind_incPoly_sub E R))
    ((pow_dvd_pow _ (by omega)).trans (cl_dvd_sub_truncG (R + 2) (clZ E)))

private lemma cl_linCoeff_Z (g E : ℝ) (R : ℕ) (k : NzInt) :
    linCoeff g (center g E R) k (clZ E) =
      if |k.1| = 1 then ((normalH E ^ 2 / (2 * g ^ 2) : ℝ) : ℂ) else 0 := by
  obtain ⟨h0, h1, hm1, -⟩ := cl_center g E R
  have hw : centerSub g (center g E R) (X .w) = 0 := by simp [centerSub]
  have hc1 : centerSub g (center g E R) (incWick 1) = C (1 / 2) * (fVar 1 + fVar (-1)) := by
    rw [incWick_one]
    simp only [map_add, map_sub, map_mul, map_pow, cl_sub_C, cl_sub_fVar, cl_sub_mVar h0, h1,
      hm1, hw, C_0]
    ring
  unfold linCoeff clZ
  rw [map_mul, map_mul, cl_sub_C, map_pow, cl_sub_γ, hc1, ← C_pow, ← C_mul, ← mul_assoc, ← C_mul,
    coeff_C_mul]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.coe_add, Pi.add_apply, cl_coeff_fVar]
  by_cases hk : |k.1| = 1
  · simp only [hk, ↓reduceIte]
    rcases (abs_eq zero_le_one).mp hk with h | h
    all_goals
      simp only [h]
      norm_num
      ring
  · have h1 : k.1 ≠ 1 := fun h => hk (by rw [h]; rfl)
    have h2 : k.1 ≠ -1 := fun h => hk (by rw [h]; rfl)
    simp [hk, h1, h2]

/-- The variables of `c_r`, `r ≤ R + 2`. -/
private def clV₀ (R : ℕ) : Finset ObsVar :=
  (Finset.range (R + 3)).biUnion fun r => (incWick r).vars

private lemma cl_vars_incPoly (E : ℝ) (R : ℕ) : (incPoly E R).vars ⊆ insert .γ (clV₀ R) := by
  intro v hv
  have h := vars_sum_subset _ _ hv
  simp only [Finset.mem_biUnion] at h
  obtain ⟨r, hr, hv⟩ := h
  have h1 := vars_mul _ _ hv
  rw [Finset.mem_union] at h1
  rcases h1 with h1 | h1
  · have h2 := vars_mul _ _ h1
    rw [Finset.mem_union, vars_C] at h2
    rcases h2 with h2 | h2
    · simp at h2
    · have h3 := vars_pow _ _ h2
      rw [vars_X, Finset.mem_singleton] at h3
      rw [h3]
      exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨r, hr, h1⟩)

/-- `‖Σ_r h^{2r} γ^r c_r‖ ≤ Σ_r c^r ‖c_r‖` for the constant weight `c` on `|E| ≤ 1`. -/
private lemma cl_norm_incPoly_le {E : ℝ} (hE : |E| ≤ 1) (R : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    clNorm (fun _ => c) (incPoly E R) ≤
      ∑ r ∈ Finset.range (R + 3), c ^ r * clNorm (fun _ => c) (incWick r) := by
  have hρ : ∀ _ : ObsVar, 0 ≤ c := fun _ => hc
  obtain ⟨hh0, hh1⟩ := cl_normalH hE
  unfold incPoly
  refine (clNorm_sum_le hρ _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  refine (clNorm_mul_le hρ _ _).trans (mul_le_mul_of_nonneg_right ?_ (clNorm_nonneg hρ _))
  refine (clNorm_mul_le hρ _ _).trans ?_
  rw [clNorm_C]
  have h1 : ‖(((normalH E ^ (2 * r) : ℝ)) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hh0 _)]
    exact pow_le_one₀ hh0 hh1
  have h2 : clNorm (fun _ => c) (X ObsVar.γ ^ r : ObsPoly) ≤ c ^ r :=
    (clNorm_pow_le hρ _ _).trans (by rw [clNorm_X])
  calc ‖(((normalH E ^ (2 * r) : ℝ)) : ℂ)‖ * clNorm (fun _ => c) (X ObsVar.γ ^ r : ObsPoly)
      ≤ 1 * c ^ r := mul_le_mul h1 h2 (clNorm_nonneg hρ _) zero_le_one
    _ = c ^ r := one_mul _

/-- `b_k = ½ h_θ² g⁻² [|k| = 1] + O(g⁻⁴)` (Section 11.3.4 [lg:sec:cocycle-correction], from (11.12)
[lg:eq:c2] and `a_{±1} = 0`). -/
theorem driftCoeff_sub_le (R : ℕ) :
    ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ K g₀ : ℝ, 0 < K ∧ 1 ≤ g₀ ∧ ∀ g : ℝ, g₀ ≤ g → ∀ E : ℝ, |E| ≤ E₁ →
      ∀ k : NzInt,
        ‖driftCoeff g E R k -
            (if |k.1| = 1 then ((normalH E ^ 2 / (2 * g ^ 2) : ℝ) : ℂ) else 0)‖ ≤ K / g ^ 4 := by
  obtain ⟨E₃, hE₃, S₀, K₀, hK₀, h₀⟩ := corrCoeff_bounded R ((clV₀ R).biUnion clIdx)
  set VV : Finset ObsVar := insert .γ (insert .w (clV₀ R)) ∪ S₀.biUnion fun d => d.support
    with hVV
  obtain ⟨E₂, hE₂, c, Kb, g₀, hc, hKb, hg₀, hb⟩ := center_bounds R (VV.biUnion clIdx)
  set B := max Kb 1 with hB
  have hB1 : 1 ≤ B := le_max_right _ _
  have hρ := clRho_nonneg zero_le_one (by linarith : (0 : ℝ) ≤ B)
  set cc := max B (∑ d ∈ S₀, K₀ * clWt (clRho 1 B) d) with hcc
  have hcc0 : 0 ≤ cc := le_trans (by linarith) (le_max_left _ _)
  have hρc : ∀ _ : ObsVar, 0 ≤ cc := fun _ => hcc0
  set K₁ := ∑ r ∈ Finset.range (R + 3), cc ^ r * clNorm (fun _ => cc) (incWick r) +
    clNorm (clRho 1 B) (incWick 1) with hK₁
  have hK₁0 : 0 ≤ K₁ := add_nonneg (Finset.sum_nonneg fun r _ =>
    mul_nonneg (pow_nonneg hcc0 _) (clNorm_nonneg hρc _)) (clNorm_nonneg hρ _)
  refine ⟨min (min E₃ E₂) 1, lt_min (lt_min hE₃ hE₂) one_pos, K₁ + 1, g₀, by linarith, hg₀,
    fun g hg E hE k => ?_⟩
  have hE3 : |E| ≤ E₃ := hE.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hE2 : |E| ≤ E₂ := hE.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hE1 : |E| ≤ 1 := hE.trans (min_le_right _ _)
  have hg1 : 1 ≤ g := hg₀.trans hg
  have hinv : ∀ u ∈ (incPoly E R).vars,
      (invCoord E R u).vars ⊆ VV ∧ clNorm (clRho 1 B) (invCoord E R u) ≤ cc := by
    intro u hu
    have hu' := cl_vars_incPoly E R hu
    have hS : ∀ i : NzInt, ∀ v ∈ [ObsVar.m i, ObsVar.f i], v = u → u ∈ clV₀ R →
        (invCoord E R u).vars ⊆ VV ∧ clNorm (clRho 1 B) (invCoord E R u) ≤ cc := by
      intro i v hv hvu hu0
      have hi : i ∈ (clV₀ R).biUnion clIdx := by
        refine Finset.mem_biUnion.mpr ⟨u, hu0, ?_⟩
        rw [← hvu]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl <;> simp [clIdx]
      obtain ⟨-, hsupp, -, hcoef⟩ := h₀ E hE3 i hi v hv
      rw [hvu] at hsupp hcoef
      refine ⟨fun x hx => ?_, ?_⟩
      · obtain ⟨d, hd, hxd⟩ := (mem_vars_iff_mem_support x).1 hx
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨d, hsupp hd, hxd⟩)
      · exact (clNorm_le_of_support hρ hsupp fun d => (hcoef d).2.1).trans (le_max_right _ _)
    cases u with
    | m i => exact hS i _ (by simp) rfl (by simpa using hu')
    | f i => exact hS i _ (by simp) rfl (by simpa using hu')
    | w =>
      rw [cl_invCoord_w, vars_X, clNorm_X]
      refine ⟨by simp [hVV], ?_⟩
      unfold clRho
      simp only [reduceCtorEq, ↓reduceIte]
      exact le_max_left _ _
    | γ =>
      rw [cl_invCoord_γ, vars_X, clNorm_X]
      refine ⟨by simp [hVV], ?_⟩
      unfold clRho
      simp only [↓reduceIte]
      exact hB1.trans (le_max_left _ _)
  have hvars : (incCorr E R - clZ E).vars ⊆ VV := by
    intro v hv
    rcases Finset.mem_union.mp (vars_sub_subset _ hv) with h | h
    · obtain ⟨d, hd, hvd⟩ := (mem_vars_iff_mem_support v).1 h
      have h' : v ∈ (bind₁ (invCoord E R) (incPoly E R)).vars :=
        (mem_vars_iff_mem_support v).2 ⟨d, cl_support_truncG _ _ hd, hvd⟩
      obtain ⟨u, hu, hvu⟩ := Finset.mem_biUnion.mp (vars_bind₁ _ _ h')
      exact (hinv u hu).1 hvu
    · unfold clZ at h
      rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h
      · rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h
        · rw [vars_C] at h
          exact absurd h (Finset.notMem_empty _)
        · have := vars_pow _ _ h
          rw [vars_X, Finset.mem_singleton] at this
          rw [this]
          simp [hVV]
      · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_biUnion.mpr ⟨1, by simp, h⟩)))
  have ha : ∀ j : NzInt, ObsVar.m j ∈ (incCorr E R - clZ E).vars → ‖center g E R j.1‖ ≤ B :=
    fun j hj => (((hb g hg E hE2).2 j
      (Finset.mem_biUnion.mpr ⟨_, hvars hj, by simp [clIdx]⟩)).2.1).trans (le_max_left _ _)
  have hnorm : clNorm (clRho 1 B) (incCorr E R - clZ E) ≤ K₁ := by
    refine (clNorm_sub_le hρ _ _).trans (add_le_add ?_ ?_)
    · have h1 : clNorm (clRho 1 B) (incCorr E R) ≤
          clNorm (clRho 1 B) (bind₁ (invCoord E R) (incPoly E R)) :=
        clNorm_mono hρ fun d => by
          unfold incCorr
          rw [cl_coeff_truncG]
          split_ifs
          · exact le_rfl
          · rw [norm_zero]; exact norm_nonneg _
      exact h1.trans ((clNorm_bind₁_le hρ _ _ fun u hu => (hinv u hu).2).trans
        (cl_norm_incPoly_le hE1 R hcc0))
    · unfold clZ
      refine (clNorm_mul_le hρ _ _).trans ?_
      have h1 : clNorm (clRho 1 B) (C (((normalH E ^ (2 * 1) : ℝ) : ℂ)) * X .γ ^ 1) ≤ 1 := by
        refine (clNorm_mul_le hρ _ _).trans ?_
        rw [clNorm_C, pow_one, clNorm_X, Complex.norm_real, Real.norm_eq_abs]
        obtain ⟨hh0, hh1⟩ := cl_normalH hE1
        rw [abs_of_nonneg (by positivity)]
        simp only [clRho, ↓reduceIte, mul_one]
        exact pow_le_one₀ hh0 hh1
      exact (mul_le_mul_of_nonneg_right h1 (clNorm_nonneg hρ _)).trans (le_of_eq (one_mul _))
  have hdiff : driftCoeff g E R k -
      (if |k.1| = 1 then ((normalH E ^ 2 / (2 * g ^ 2) : ℝ) : ℂ) else 0) =
      linCoeff g (center g E R) k (incCorr E R - clZ E) := by
    rw [cl_linCoeff_sub, cl_linCoeff_Z]
    rfl
  rw [hdiff]
  refine (cl_linCoeff_le hg1 hB1 ha (cl_incCorr_sub E R) k).trans ?_
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

end LSBA
