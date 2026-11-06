import LSBA.Kernel.Bounded

/-!
# Small-coupling rows of the bounded-coupling kernels

On `0 ≤ g ≤ C` the off-diagonal parts of the exponentially weighted rows (A.24)
[ba:eq:weighted-rows] of the Dyson matrix `M_B(g, E)` are `O(g)`, and those of the stable
inverse `(I - tQ)⁻¹` are `O(g²)`, uniformly in `0 ≤ t < 1`: Lemma A.5 [ba:lem:kernels] with
the dependence on the coupling made explicit.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- Weighted rows are submultiplicative: if every weighted row of `Z` is at most `S`, then the
weighted row of `Y Z` at `a` is at most the weighted row of `Y` at `a` times `S`. -/
private lemma smr_wmul {L : ℕ} [NeZero L] (c : ℝ) (hc : 0 ≤ c)
    (Y Z : Matrix (Fin L) (Fin L) ℂ) (S : ℝ)
    (hZ : ∀ x, ∑ b, Real.exp (c * cycDist x b) * ‖Z x b‖ ≤ S) (a : Fin L) :
    ∑ b, Real.exp (c * cycDist a b) * ‖(Y * Z) a b‖ ≤
      (∑ x, Real.exp (c * cycDist a x) * ‖Y a x‖) * S := by
  calc ∑ b, Real.exp (c * cycDist a b) * ‖(Y * Z) a b‖
      ≤ ∑ b, ∑ x, Real.exp (c * cycDist a x) * ‖Y a x‖ *
          (Real.exp (c * cycDist x b) * ‖Z x b‖) := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [Matrix.mul_apply]
        calc Real.exp (c * cycDist a b) * ‖∑ x, Y a x * Z x b‖
            ≤ Real.exp (c * cycDist a b) * ∑ x, ‖Y a x‖ * ‖Z x b‖ := by
              gcongr
              refine (norm_sum_le _ _).trans ?_
              exact Finset.sum_le_sum fun x _ => (norm_mul _ _).le
          _ = ∑ x, Real.exp (c * cycDist a b) * (‖Y a x‖ * ‖Z x b‖) := by
              rw [Finset.mul_sum]
          _ ≤ _ := Finset.sum_le_sum fun x _ => by
              have h1 : Real.exp (c * cycDist a b) ≤
                  Real.exp (c * cycDist a x) * Real.exp (c * cycDist x b) := by
                rw [← Real.exp_add, Real.exp_le_exp, ← mul_add]
                gcongr
                exact_mod_cast bd_cycDist_tri a x b
              calc Real.exp (c * cycDist a b) * (‖Y a x‖ * ‖Z x b‖)
                  ≤ (Real.exp (c * cycDist a x) * Real.exp (c * cycDist x b)) *
                      (‖Y a x‖ * ‖Z x b‖) := by gcongr
                _ = _ := by ring
    _ = ∑ x, Real.exp (c * cycDist a x) * ‖Y a x‖ *
          ∑ b, (Real.exp (c * cycDist x b) * ‖Z x b‖) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun x _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ x, Real.exp (c * cycDist a x) * ‖Y a x‖ * S :=
        Finset.sum_le_sum fun x _ => by gcongr; exact hZ x
    _ = _ := by rw [Finset.sum_mul]

/-- Off-diagonal weighted row of `Y = α I + κ U V`: it is `‖κ‖` times the weighted rows of `U`
and `V`. -/
private lemma smr_offdiag {L : ℕ} [NeZero L] (c : ℝ) (hc : 0 ≤ c)
    (Y U V : Matrix (Fin L) (Fin L) ℂ) (α κ : ℂ)
    (hY : Y = α • (1 : Matrix (Fin L) (Fin L) ℂ) + κ • (U * V)) (SU SV : ℝ)
    (hU : ∀ x, ∑ b, Real.exp (c * cycDist x b) * ‖U x b‖ ≤ SU)
    (hV : ∀ x, ∑ b, Real.exp (c * cycDist x b) * ‖V x b‖ ≤ SV) (a : Fin L) :
    ∑ b ∈ Finset.univ.erase a, Real.exp (c * cycDist a b) * ‖Y a b‖ ≤ ‖κ‖ * (SU * SV) := by
  have hSV : 0 ≤ SV := le_trans (Finset.sum_nonneg fun b _ => by positivity) (hV a)
  calc ∑ b ∈ Finset.univ.erase a, Real.exp (c * cycDist a b) * ‖Y a b‖
      = ∑ b ∈ Finset.univ.erase a, Real.exp (c * cycDist a b) * (‖κ‖ * ‖(U * V) a b‖) := by
        refine Finset.sum_congr rfl fun b hb => ?_
        have hba : a ≠ b := (Finset.ne_of_mem_erase hb).symm
        rw [hY]
        simp [hba]
    _ ≤ ∑ b, Real.exp (c * cycDist a b) * (‖κ‖ * ‖(U * V) a b‖) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          fun b _ _ => by positivity
    _ = ‖κ‖ * ∑ b, Real.exp (c * cycDist a b) * ‖(U * V) a b‖ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
    _ ≤ ‖κ‖ * ((∑ x, Real.exp (c * cycDist a x) * ‖U a x‖) * SV) := by
        gcongr
        exact smr_wmul c hc U V SV hV a
    _ ≤ ‖κ‖ * (SU * SV) := by
        gcongr
        exact hU a

/-- The weighted row of the cycle adjacency matrix is at most `2 e^c`. -/
private lemma smr_adj_row {L : ℕ} (hL : 2 ≤ L) (c : ℝ) (hc : 0 ≤ c) (a : Fin L) :
    ∑ x, Real.exp (c * cycDist a x) * ‖cycleAdj L a x‖ ≤ 2 * Real.exp c := by
  have hd : ∀ x : Fin L, (x.val = (a.val + 1) % L ∨ a.val = (x.val + 1) % L) →
      cycDist a x ≤ 1 := by
    intro x hx
    have ha := a.isLt
    have hx' := x.isLt
    unfold cycDist
    rcases hx with h | h
    · by_cases h1 : a.val + 1 < L
      · rw [Nat.mod_eq_of_lt h1] at h
        refine min_le_of_right_le ?_
        have : x.val + L - a.val = 1 + L := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      · have h2 : a.val + 1 = L := by omega
        rw [h2, Nat.mod_self] at h
        refine min_le_of_right_le ?_
        have : x.val + L - a.val = 1 := by omega
        rw [this, Nat.mod_eq_of_lt (by omega)]
    · by_cases h1 : x.val + 1 < L
      · rw [Nat.mod_eq_of_lt h1] at h
        refine min_le_of_left_le ?_
        have : a.val + L - x.val = 1 + L := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      · have h2 : x.val + 1 = L := by omega
        rw [h2, Nat.mod_self] at h
        refine min_le_of_left_le ?_
        have : a.val + L - x.val = 1 := by omega
        rw [this, Nat.mod_eq_of_lt (by omega)]
  calc ∑ x, Real.exp (c * cycDist a x) * ‖cycleAdj L a x‖
      ≤ ∑ x : Fin L, Real.exp c * ((if x.val = (a.val + 1) % L then (1 : ℝ) else 0) +
          (if a.val = (x.val + 1) % L then (1 : ℝ) else 0)) := by
        refine Finset.sum_le_sum fun x _ => ?_
        have hA : cycleAdj L a x = (if x.val = (a.val + 1) % L then (1 : ℂ) else 0) +
            (if a.val = (x.val + 1) % L then (1 : ℂ) else 0) := rfl
        have hexp : (cycDist a x ≤ 1) → Real.exp (c * cycDist a x) ≤ Real.exp c := fun hdx =>
          Real.exp_le_exp.mpr (by
            have : (cycDist a x : ℝ) ≤ 1 := by exact_mod_cast hdx
            nlinarith)
        rw [hA]
        by_cases h1 : x.val = (a.val + 1) % L <;> by_cases h2 : a.val = (x.val + 1) % L
        · have he := hexp (hd x (Or.inl h1))
          simp only [eq_true h1, eq_true h2, ite_true]
          have : ‖(1 : ℂ) + 1‖ = 2 := by norm_num
          rw [this]
          linarith
        · have he := hexp (hd x (Or.inl h1))
          simp only [eq_true h1, eq_false h2, ite_true, ite_false, add_zero, norm_one]
          linarith
        · have he := hexp (hd x (Or.inr h2))
          simp only [eq_false h1, eq_true h2, ite_true, ite_false, zero_add, norm_one]
          linarith
        · simp only [eq_false h1, eq_false h2, ite_false]
          simp
    _ = Real.exp c * ((∑ x : Fin L, if x.val = (a.val + 1) % L then (1 : ℝ) else 0) +
          ∑ x : Fin L, if a.val = (x.val + 1) % L then (1 : ℝ) else 0) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ Real.exp c * (1 + 1) := by
        gcongr
        · rw [Finset.sum_boole]
          have : (Finset.univ.filter fun x : Fin L => x.val = (a.val + 1) % L).card ≤ 1 :=
            Finset.card_le_one.mpr fun x hx y hy => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
              exact Fin.ext (hx.trans hy.symm)
          exact_mod_cast this
        · rw [Finset.sum_boole]
          have : (Finset.univ.filter fun x : Fin L => a.val = (x.val + 1) % L).card ≤ 1 :=
            Finset.card_le_one.mpr fun x hx y hy => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
              have h : (x.val + 1) % L = (y.val + 1) % L := hx.symm.trans hy
              have h' : x.val % L = y.val % L := Nat.ModEq.add_right_cancel' 1 h
              rw [Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] at h'
              exact Fin.ext h'
          exact_mod_cast this
    _ = 2 * Real.exp c := by ring

/-- First resolvent identity: `(gA - w) M = 1` gives `M = -w⁻¹ I + (g/w) A M`. -/
private lemma smr_res1 {n : Type*} [Fintype n] [DecidableEq n] (A M : Matrix n n ℂ) (g w : ℂ)
    (hw : w ≠ 0) (h : (g • A - w • (1 : Matrix n n ℂ)) * M = 1) :
    M = (-w⁻¹) • (1 : Matrix n n ℂ) + (g / w) • (A * M) := by
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul] at h
  have h' : w • M = g • (A * M) - 1 := by rw [← h]; abel
  calc M = w⁻¹ • (w • M) := by rw [smul_smul, inv_mul_cancel₀ hw, one_smul]
    _ = w⁻¹ • (g • (A * M) - 1) := by rw [h']
    _ = _ := by module

/-- Second resolvent identity: `X (δ I - κ R) = 1` gives `X = δ⁻¹ I + (κ/δ) X R`. -/
private lemma smr_res2 {n : Type*} [Fintype n] [DecidableEq n] (R X : Matrix n n ℂ) (δ κ : ℂ)
    (hδ : δ ≠ 0) (h : X * (δ • (1 : Matrix n n ℂ) - κ • R) = 1) :
    X = δ⁻¹ • (1 : Matrix n n ℂ) + (κ / δ) • (X * R) := by
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one] at h
  have h' : δ • X = 1 + κ • (X * R) := by rw [← h]; abel
  calc X = δ⁻¹ • (δ • X) := by rw [smul_smul, inv_mul_cancel₀ hδ, one_smul]
    _ = δ⁻¹ • (1 + κ • (X * R)) := by rw [h']
    _ = _ := by module

/-- The off-diagonal weighted rows of the Dyson matrix at coupling `g ≤ 1` are `O(g)`. -/
private lemma smr_small_M {L : ℕ} (hL : 3 ≤ L) (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (E : ℝ)
    (m : ℂ) (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (c' : ℝ) (hc' : 0 < c')
    (hcm : c' ≤ m.im) (c C₁ : ℝ) (hc : 0 ≤ c) (hclog : c ≤ Real.log 2)
    (hM : ∀ a, ∑ b, Real.exp (c * cycDist a b) *
      ‖dysonMat (hopB g) (gammaG g) L E m a b‖ ≤ C₁) (a : Fin L) :
    ∑ b ∈ Finset.univ.erase a, Real.exp (c * cycDist a b) *
      ‖dysonMat (hopB g) (gammaG g) L E m a b‖ ≤ 4 * C₁ / c' * g := by
  have : NeZero L := ⟨by omega⟩
  have hγ : gammaG g = 1 := by simp [gammaG, max_eq_left hg1]
  have hb : hopB g = g := by simp [hopB, max_eq_left hg1]
  have hmim : 0 < m.im := hm.1
  have hw : 0 < ((E : ℂ) + ((gammaG g : ℝ) : ℂ) * m).im := by
    simpa [hγ] using hmim
  have hC₁ : 0 ≤ C₁ := le_trans (Finset.sum_nonneg fun b _ => by positivity) (hM a)
  set M := dysonMat (hopB g) (gammaG g) L E m with hMdef
  have hdiag : ∀ x, M x x = m := fun x =>
    (dysonMat_diag (hopB g) (gammaG g) L (by omega) E m hw x).trans hm.2.symm
  set w : ℂ := (E : ℂ) + ((gammaG g : ℝ) : ℂ) * m with hwdef
  set T : Matrix (Fin L) (Fin L) ℂ :=
    ((hopB g : ℝ) : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ) with hT
  have hMT : M = T⁻¹ := rfl
  have hTu : IsUnit T.det := by
    by_contra hnu
    have h0 : M = 0 := by rw [hMT]; exact Matrix.nonsing_inv_apply_not_isUnit _ hnu
    have h := hdiag ⟨0, by omega⟩
    rw [h0] at h
    have : m.im = 0 := by rw [← h]; simp
    linarith
  have hTM : T * M = 1 := by rw [hMT]; exact Matrix.mul_nonsing_inv T hTu
  have hwim : w.im = m.im := by simp [hwdef, hγ]
  have hwn : c' ≤ ‖w‖ := by
    refine le_trans ?_ (Complex.abs_im_le_norm w)
    rw [hwim, abs_of_pos hmim]; exact hcm
  have hw0 : w ≠ 0 := fun h => by rw [h, norm_zero] at hwn; linarith
  have hres := smr_res1 (cycleAdj L) M ((hopB g : ℝ) : ℂ) w hw0 hTM
  have h2 : Real.exp c ≤ 2 := by
    have := Real.exp_le_exp.mpr hclog
    rwa [Real.exp_log (by norm_num)] at this
  have hU : ∀ x, ∑ b, Real.exp (c * cycDist x b) * ‖cycleAdj L x b‖ ≤ 4 := fun x =>
    (smr_adj_row (by omega) c hc x).trans (by linarith)
  have hoff := smr_offdiag c hc M (cycleAdj L) M (-w⁻¹) (((hopB g : ℝ) : ℂ) / w) hres 4 C₁ hU
    hM a
  refine hoff.trans ?_
  have hκ : ‖((hopB g : ℝ) : ℂ) / w‖ ≤ g / c' := by
    rw [norm_div, Complex.norm_real, hb, Real.norm_eq_abs, abs_of_nonneg hg0]
    exact div_le_div_of_nonneg_left hg0 hc' hwn
  calc ‖((hopB g : ℝ) : ℂ) / w‖ * (4 * C₁) ≤ g / c' * (4 * C₁) := by gcongr
    _ = _ := by ring

/-- The off-diagonal weighted rows of the stable inverse at coupling `g ≤ 1` are `O(g²)`. -/
private lemma smr_small_X {L : ℕ} (hL : 3 ≤ L) (g : ℝ) (hg1 : g ≤ 1) (E : ℝ)
    (m : ℂ) (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (c' : ℝ) (hc' : 0 < c')
    (hcm : c' ≤ m.im) (c C₁ K : ℝ) (hc : 0 ≤ c) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (h1 : ∀ x, ∑ b ∈ Finset.univ.erase x, Real.exp (c * cycDist x b) *
      ‖dysonMat (hopB g) (gammaG g) L E m x b‖ ≤ K * g)
    (hX : ∀ a, ∑ b, Real.exp (c * cycDist a b) *
      ‖(1 - (t : ℂ) • pairQ (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))⁻¹ a b‖ ≤ C₁)
    (a : Fin L) :
    ∑ b ∈ Finset.univ.erase a, Real.exp (c * cycDist a b) *
      ‖(1 - (t : ℂ) • pairQ (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))⁻¹ a b‖ ≤
        C₁ * K ^ 2 / c' ^ 2 * g ^ 2 := by
  have : NeZero L := ⟨by omega⟩
  have hγ : gammaG g = 1 := by simp [gammaG, max_eq_left hg1]
  have hmim : 0 < m.im := hm.1
  have hw : 0 < ((E : ℂ) + ((gammaG g : ℝ) : ℂ) * m).im := by
    simpa [hγ] using hmim
  have hC₁ : 0 ≤ C₁ := le_trans (Finset.sum_nonneg fun b _ => by positivity) (hX a)
  have hrow := pairP_row_sum (hopB g) (gammaG g) (by rw [hγ]; norm_num) L (by omega) E m hm
  set M := dysonMat (hopB g) (gammaG g) L E m with hMdef
  have hdiag : ∀ x, M x x = m := fun x =>
    (dysonMat_diag (hopB g) (gammaG g) L (by omega) E m hw x).trans hm.2.symm
  have hward : ∀ x, ∑ b, ‖M x b‖ ^ 2 = 1 := fun x => by
    simpa [pairP, hγ] using hrow x
  have hK : 0 ≤ K * g := le_trans (Finset.sum_nonneg fun b _ => by positivity) (h1 a)
  -- the diagonal and the off-diagonal part of `Q`
  set Q := pairQ (gammaG g) M with hQdef
  have hQ : ∀ x y, Q x y = M x y ^ 2 := fun x y => by simp [hQdef, pairQ, hγ]
  set R : Matrix (Fin L) (Fin L) ℂ := Q - (m ^ 2) • (1 : Matrix (Fin L) (Fin L) ℂ) with hRdef
  have hRdiag : ∀ x, R x x = 0 := fun x => by simp [hRdef, hQ, hdiag]
  have hRoff : ∀ x y, x ≠ y → ‖R x y‖ = ‖M x y‖ ^ 2 := fun x y hxy => by
    simp [hRdef, hQ, hxy, norm_pow]
  -- the lower bound on `1 - t m²`
  have hm2 : m.re ^ 2 + m.im ^ 2 ≤ 1 := by
    have h := Finset.single_le_sum (f := fun b => ‖M ⟨0, by omega⟩ b‖ ^ 2)
      (fun b _ => sq_nonneg _) (Finset.mem_univ (⟨0, by omega⟩ : Fin L))
    rw [hward] at h
    simp only [hdiag] at h
    have := Complex.sq_norm_sub_sq_re m
    linarith
  set δ : ℂ := 1 - (t : ℂ) * m ^ 2 with hδ
  have hδre : δ.re = 1 - t * (m.re ^ 2 - m.im ^ 2) := by
    simp [hδ, pow_two, Complex.mul_re]
  have hy2 : c' ^ 2 ≤ m.im ^ 2 := pow_le_pow_left₀ hc'.le hcm 2
  have hδc : c' ^ 2 ≤ ‖δ‖ := by
    refine le_trans ?_ (Complex.re_le_norm δ)
    rw [hδre]
    by_cases hxy : m.re ^ 2 ≤ m.im ^ 2
    · nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hxy), sq_nonneg m.re]
    · have hxy' := (not_le.mp hxy).le
      nlinarith [mul_nonneg (sub_nonneg.mpr ht1.le) (sub_nonneg.mpr hxy'), sq_nonneg m.re]
  have hδt : 1 - t * ‖m‖ ^ 2 ≤ ‖δ‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((t : ℂ) * m ^ 2)
    rw [norm_one, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht0] at this
    exact this
  have hδ0 : δ ≠ 0 := fun h => by rw [h, norm_zero] at hδc; nlinarith
  -- invertibility of `1 - tQ`
  set B : Matrix (Fin L) (Fin L) ℂ := 1 - (t : ℂ) • Q with hB
  have hBdet : B.det ≠ 0 := by
    refine det_ne_zero_of_sum_row_lt_diag fun k => ?_
    have hdk : ‖B k k‖ = ‖δ‖ := by simp [hB, hQ, hdiag, hδ]
    have hoff : ∀ j ∈ Finset.univ.erase k, ‖B k j‖ = t * ‖M k j‖ ^ 2 := fun j hj => by
      have hkj : k ≠ j := (Finset.ne_of_mem_erase hj).symm
      simp [hB, hQ, hkj, norm_pow, abs_of_nonneg ht0]
    rw [hdk, Finset.sum_congr rfl hoff, ← Finset.mul_sum]
    have hs := Finset.add_sum_erase Finset.univ (fun j => ‖M k j‖ ^ 2) (Finset.mem_univ k)
    rw [hward, hdiag] at hs
    have hnm : ‖m‖ ^ 2 ≤ 1 := by
      have := Complex.sq_norm_sub_sq_re m
      linarith
    nlinarith
  have hBX : (B⁻¹) * B = 1 := Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hBdet)
  have hBR : B = δ • (1 : Matrix (Fin L) (Fin L) ℂ) - (t : ℂ) • R := by
    simp only [hB, hRdef, hδ]; module
  have hres := smr_res2 R (B⁻¹) δ (t : ℂ) hδ0 (by rw [← hBR]; exact hBX)
  -- the weighted rows of `R`
  have hV : ∀ x, ∑ b, Real.exp (c * cycDist x b) * ‖R x b‖ ≤ (K * g) ^ 2 := by
    intro x
    set Tx := ∑ b ∈ Finset.univ.erase x, Real.exp (c * cycDist x b) * ‖M x b‖ with hTx
    calc ∑ b, Real.exp (c * cycDist x b) * ‖R x b‖
        = ∑ b ∈ Finset.univ.erase x, Real.exp (c * cycDist x b) * ‖R x b‖ :=
          (Finset.sum_erase _ (by simp [hRdiag])).symm
      _ ≤ ∑ b ∈ Finset.univ.erase x, (Real.exp (c * cycDist x b) * ‖M x b‖) * Tx := by
          refine Finset.sum_le_sum fun b hb => ?_
          have hbx : x ≠ b := (Finset.ne_of_mem_erase hb).symm
          rw [hRoff x b hbx]
          have h1b : ‖M x b‖ ≤ Tx := by
            refine le_trans ?_ (Finset.single_le_sum
              (f := fun b => Real.exp (c * cycDist x b) * ‖M x b‖)
              (fun _ _ => by positivity) hb)
            exact le_mul_of_one_le_left (norm_nonneg _)
              (Real.one_le_exp (mul_nonneg hc (Nat.cast_nonneg _)))
          calc Real.exp (c * cycDist x b) * ‖M x b‖ ^ 2
              = (Real.exp (c * cycDist x b) * ‖M x b‖) * ‖M x b‖ := by ring
            _ ≤ _ := by gcongr
      _ = Tx * Tx := by rw [← Finset.sum_mul]
      _ ≤ (K * g) * (K * g) := by
          have hTx0 : 0 ≤ Tx := Finset.sum_nonneg fun _ _ => by positivity
          exact mul_self_le_mul_self hTx0 (h1 x)
      _ = _ := by ring
  have hoff := smr_offdiag c hc (B⁻¹) (B⁻¹) R (δ⁻¹) ((t : ℂ) / δ) hres C₁ ((K * g) ^ 2) hX hV a
  refine hoff.trans ?_
  have hκ : ‖(t : ℂ) / δ‖ ≤ 1 / c' ^ 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
    nlinarith
  calc ‖(t : ℂ) / δ‖ * (C₁ * (K * g) ^ 2) ≤ 1 / c' ^ 2 * (C₁ * (K * g) ^ 2) := by gcongr
    _ = _ := by ring

/-- Small-coupling rows of the kernels of Lemma A.5 [ba:lem:kernels]: on `0 ≤ g ≤ C`, the
off-diagonal parts of the weighted rows (A.24) [ba:eq:weighted-rows] of `M = M_B(g, E)` are
`O(g)`, and those of the stable inverse `(I - tQ)⁻¹` are `O(g²)`, for `0 ≤ t < 1`. -/
theorem kernel_small_rows (C B₀ c' : ℝ) (hC : 0 < C) (hB₀ : 0 < B₀) (hc' : 0 < c') :
    ∃ c C' : ℝ, ∃ L₀ : ℕ, 0 < c ∧ 0 < C' ∧ ∀ g : ℝ, 0 ≤ g → g ≤ C → ∀ L : ℕ, 3 ≤ L → L₀ ≤ L →
      ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m → c' ≤ m.im →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a : Fin L,
        (∑ b ∈ Finset.univ.erase a, Real.exp (c * cycDist a b) *
          ‖dysonMat (hopB g) (gammaG g) L E m a b‖ ≤ C' * g) ∧
        ∑ b ∈ Finset.univ.erase a, Real.exp (c * cycDist a b) *
          ‖(1 - (t : ℂ) • pairQ (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))⁻¹ a b‖ ≤
            C' * g ^ 2 := by
  obtain ⟨c₀, C₁, L₀, hc₀, hC₁, H⟩ := bdd_kernels C B₀ c' hC hB₀ hc'
  have hc : 0 < min c₀ (Real.log 2) := lt_min hc₀ (Real.log_pos (by norm_num))
  have hcc₀ : min c₀ (Real.log 2) ≤ c₀ := min_le_left _ _
  have hclog : min c₀ (Real.log 2) ≤ Real.log 2 := min_le_right _ _
  set c := min c₀ (Real.log 2) with hcdef
  set K := 4 * C₁ / c' with hKdef
  have hK : 0 ≤ K := by positivity
  set C' := max (max C₁ K) (C₁ * K ^ 2 / c' ^ 2) with hC'def
  have hC1 : C₁ ≤ C' := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC2 : K ≤ C' := le_trans (le_max_right _ _) (le_max_left _ _)
  have hC3 : C₁ * K ^ 2 / c' ^ 2 ≤ C' := le_max_right _ _
  refine ⟨c, C', L₀, hc, lt_of_lt_of_le hC₁ hC1, ?_⟩
  intro g hg hgC L hL hL₀ E hE m hm hcm t ht0 ht1 a
  obtain ⟨-, -, h3, -, h5⟩ := H g hg hgC L hL hL₀ E hE m hm hcm t ht0 ht1
  have hw : ∀ (Y : Matrix (Fin L) (Fin L) ℂ) (x : Fin L),
      ∑ b, Real.exp (c * cycDist x b) * ‖Y x b‖ ≤ ∑ b, Real.exp (c₀ * cycDist x b) * ‖Y x b‖ :=
    fun Y x => Finset.sum_le_sum fun b _ => by
      gcongr
  have hM : ∀ x, ∑ b, Real.exp (c * cycDist x b) *
      ‖dysonMat (hopB g) (gammaG g) L E m x b‖ ≤ C₁ := fun x => (hw _ x).trans (h3 x)
  have hX : ∀ x, ∑ b, Real.exp (c * cycDist x b) *
      ‖(1 - (t : ℂ) • pairQ (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))⁻¹ x b‖ ≤ C₁ :=
    fun x => (hw _ x).trans (h5 x)
  by_cases hg1 : g ≤ 1
  · have h1 := fun x => smr_small_M hL g hg hg1 E m hm c' hc' hcm c C₁ hc.le hclog hM x
    have h2 := smr_small_X hL g hg1 E m hm c' hc' hcm c C₁ K hc.le t ht0 ht1 h1 hX a
    refine ⟨(h1 a).trans ?_, h2.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right hC2 hg
    · exact mul_le_mul_of_nonneg_right hC3 (sq_nonneg g)
  · have hg1' : 1 < g := not_le.mp hg1
    refine ⟨?_, ?_⟩
    · calc _ ≤ ∑ b, Real.exp (c * cycDist a b) *
            ‖dysonMat (hopB g) (gammaG g) L E m a b‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun b _ _ => by positivity
        _ ≤ C₁ := hM a
        _ ≤ C₁ * g := le_mul_of_one_le_right hC₁.le hg1'.le
        _ ≤ C' * g := mul_le_mul_of_nonneg_right hC1 hg
    · calc _ ≤ ∑ b, Real.exp (c * cycDist a b) *
            ‖(1 - (t : ℂ) • pairQ (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))⁻¹ a b‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun b _ _ => by positivity
        _ ≤ C₁ := hX a
        _ ≤ C₁ * g ^ 2 := le_mul_of_one_le_right hC₁.le (by nlinarith)
        _ ≤ C' * g ^ 2 := mul_le_mul_of_nonneg_right hC1 (sq_nonneg g)

end LSBA
