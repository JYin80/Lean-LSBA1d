import LSBA.Kernel.Root
import LSBA.Kernel.Algebra
import LSBA.Kernel.LineKernel

/-!
# Large coupling

The uniform finite-cycle comparison of Lemma A.4 [uvp:prop:finite], the anchor derivative
[fo:eq:terminal-anchor-derivative], the actual kernels of Lemma A.10 [uvp:lem:actual-kernels] with
the
local convolution bound (A.45) [uvp:eq:localconv], the kernel accuracy (A.44)
[da:eq:kernel-accuracy] and Lemma 6.1 [da:lem:scales-propagators] at large coupling.
-/

open MeasureTheory Real Filter Topology Complex
open scoped ENNReal

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Circulant geometric kernels on `ℤ_L` -/

/-- `c - a` on `ℤ_L` as a natural number below `L`. -/
private def lgD (L : ℕ) (a c : Fin L) : ℕ :=
  if a.val ≤ c.val then c.val - a.val else c.val + L - a.val

private lemma lgD_lt {L : ℕ} (a c : Fin L) : lgD L a c < L := by
  have := a.isLt; have := c.isLt
  unfold lgD; split_ifs <;> omega

private lemma lgD_swap {L : ℕ} (a c : Fin L) :
    lgD L c a = if lgD L a c = 0 then 0 else L - lgD L a c := by
  have := a.isLt; have := c.isLt
  unfold lgD; split_ifs <;> omega

private lemma lg_mod_eq (u v L : ℕ) (hu : u < L) (hv : v < L) :
    (u + L - v) % L = if v ≤ u then u - v else u + L - v := by
  split_ifs with h
  · have : u + L - v = (u - v) + L := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

private lemma lgD_eq_sub_val {L : ℕ} [NeZero L] (a c : Fin L) : lgD L a c = (c - a).val := by
  have ha := a.isLt; have hc := c.isLt
  rw [Fin.sub_def]
  simp only
  rw [show L - a.val + c.val = c.val + L - a.val by omega, lg_mod_eq _ _ _ hc ha]
  rfl

private lemma cycDist_eq_min {L : ℕ} (a c : Fin L) : cycDist a c = min (lgD L a c) (lgD L c a) := by
  have ha := a.isLt; have hc := c.isLt
  unfold cycDist
  rw [lg_mod_eq _ _ _ ha hc, lg_mod_eq _ _ _ hc ha, min_comm]
  rfl

private lemma cycDist_le_lgD {L : ℕ} (a c : Fin L) : cycDist a c ≤ lgD L a c := by
  rw [cycDist_eq_min]; exact min_le_left _ _

private lemma cycDist_le_sub_lgD {L : ℕ} (a c : Fin L) : cycDist a c ≤ L - lgD L a c := by
  have ha := a.isLt; have hc := c.isLt
  simp only [cycDist_eq_min, lgD]
  split_ifs <;> omega

private lemma cycDist_le_half {L : ℕ} (a c : Fin L) : 2 * cycDist a c ≤ L := by
  have h1 := cycDist_le_lgD a c
  have h2 := cycDist_le_sub_lgD a c
  have := lgD_lt a c
  omega

/-- Triangle inequality for the cyclic distance. -/
private lemma cycDist_triangle {L : ℕ} (a b c : Fin L) : cycDist a c ≤ cycDist a b + cycDist b c :=
    by
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt
  simp only [cycDist_eq_min, lgD]
  split_ifs <;> omega

/-- Sums over `c` of a function of `c - a` are sums over `0, …, L - 1`. -/
private lemma sum_lgD_row {L : ℕ} {M : Type*} [AddCommMonoid M] (a : Fin L) (φ : ℕ → M) :
    ∑ c : Fin L, φ (lgD L a c) = ∑ k ∈ Finset.range L, φ k := by
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL; simp
  have : NeZero L := ⟨by omega⟩
  simp_rw [lgD_eq_sub_val]
  rw [Fintype.sum_equiv (Equiv.subRight a) (fun c => φ (c - a).val) (fun c => φ c.val)
    (fun c => rfl)]
  exact Fin.sum_univ_eq_sum_range (fun k => φ k) L

/-- Sums over `a` of a function of `c - a` are sums over `0, …, L - 1`. -/
private lemma sum_lgD_col {L : ℕ} {M : Type*} [AddCommMonoid M] (c : Fin L) (φ : ℕ → M) :
    ∑ a : Fin L, φ (lgD L a c) = ∑ k ∈ Finset.range L, φ k := by
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL; simp
  have : NeZero L := ⟨by omega⟩
  simp_rw [lgD_eq_sub_val]
  rw [Fintype.sum_equiv (Equiv.subLeft c) (fun a => φ (c - a).val) (fun c => φ c.val)
    (fun a => rfl)]
  exact Fin.sum_univ_eq_sum_range (fun k => φ k) L

/-- The successor on `ℤ_L`. -/
private def lgSucc {L : ℕ} (a : Fin L) : Fin L :=
  ⟨if a.val + 1 < L then a.val + 1 else 0, by have := a.isLt; split_ifs <;> omega⟩

/-- The predecessor on `ℤ_L`. -/
private def lgPred {L : ℕ} (a : Fin L) : Fin L :=
  ⟨if 0 < a.val then a.val - 1 else L - 1, by have := a.isLt; split_ifs <;> omega⟩

private lemma lg_succ_mod_eq (L x : ℕ) (hx : x < L) :
    (x + 1) % L = if x + 1 < L then x + 1 else 0 := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have : x + 1 = L := by omega
    rw [this, Nat.mod_self]

/-- The adjacency matrix of `ℤ_L` over a field. -/
private def adjK (𝕜 : Type*) [Field 𝕜] (L : ℕ) : Matrix (Fin L) (Fin L) 𝕜 :=
  Matrix.of fun a b =>
    (if b.val = (a.val + 1) % L then 1 else 0) + (if a.val = (b.val + 1) % L then 1 else 0)

private lemma cycleAdj_eq_adjK (L : ℕ) : cycleAdj L = adjK ℂ L := rfl

private lemma adjK_apply {𝕜 : Type*} [Field 𝕜] {L : ℕ} (a k : Fin L) :
    adjK 𝕜 L a k = (if k = lgSucc a then 1 else 0) + (if k = lgPred a then 1 else 0) := by
  simp only [adjK, Matrix.of_apply]
  have hk := k.isLt
  have ha := a.isLt
  have h1 : (k.val = (a.val + 1) % L) ↔ k = lgSucc a := by
    rw [lg_succ_mod_eq L a.val ha, Fin.ext_iff]
    simp only [lgSucc]
  have h2 : (a.val = (k.val + 1) % L) ↔ k = lgPred a := by
    rw [lg_succ_mod_eq L k.val hk, Fin.ext_iff]
    simp only [lgPred]
    split_ifs <;> omega
  rw [if_congr h1 rfl rfl, if_congr h2 rfl rfl]

section Geom

variable {𝕜 : Type*} [Field 𝕜]

/-- The periodized two-sided geometric profile `k ↦ (τ^k + τ^{L-k})/(1 - τ^L)`. -/
private def geomV (τ : 𝕜) (L k : ℕ) : 𝕜 := (τ ^ k + τ ^ (L - k)) / (1 - τ ^ L)

/-- The circulant matrix with profile `geomV τ L`. -/
private def geomC (τ : 𝕜) (L : ℕ) : Matrix (Fin L) (Fin L) 𝕜 :=
  Matrix.of fun a c => geomV τ L (lgD L a c)

private lemma geomV_L (τ : 𝕜) (L : ℕ) : geomV τ L L = geomV τ L 0 := by
  unfold geomV
  simp only [Nat.sub_self, Nat.sub_zero, pow_zero]
  rw [add_comm]

private lemma geomV_rec_int {τ : 𝕜} (hτ : τ ≠ 0) (L d : ℕ) (hd : 1 ≤ d) (hd' : d + 1 ≤ L) :
    geomV τ L (d - 1) + geomV τ L (d + 1) = (τ + τ⁻¹) * geomV τ L d := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, L = e + n + 2 := ⟨L - e - 2, by omega⟩
  unfold geomV
  have e1 : e + n + 2 - (e + 1 - 1) = n + 2 := by omega
  have e2 : e + n + 2 - (e + 1 + 1) = n := by omega
  have e3 : e + n + 2 - (e + 1) = n + 1 := by omega
  rw [e1, e2, e3, Nat.add_sub_cancel]
  rw [← add_div, mul_div_assoc']
  congr 1
  field_simp
  ring

private lemma geomV_rec_zero {τ : 𝕜} (hτ : τ ≠ 0) {L : ℕ} (hD : 1 - τ ^ L ≠ 0) (hL : 2 ≤ L) :
    geomV τ L (L - 1) + geomV τ L 1 = (τ + τ⁻¹) * geomV τ L 0 - (τ⁻¹ - τ) := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 2 := ⟨L - 2, by omega⟩
  unfold geomV
  have e2 : n + 2 - 1 = n + 1 := by omega
  have e3 : n + 2 - (n + 1) = 1 := by omega
  rw [e2, e3, Nat.sub_zero]
  field_simp
  ring

/-- The circulant identity `((τ + τ⁻¹) I - A_L) G_τ = (τ⁻¹ - τ) I`: the periodized geometric
kernel is a multiple of the free resolvent at the energy `τ + τ⁻¹`. -/
private theorem geomC_mul {τ : 𝕜} (hτ : τ ≠ 0) {L : ℕ} (hD : 1 - τ ^ L ≠ 0) (hL : 3 ≤ L) :
    ((τ + τ⁻¹) • (1 : Matrix (Fin L) (Fin L) 𝕜) - adjK 𝕜 L) * geomC τ L =
      (τ⁻¹ - τ) • (1 : Matrix (Fin L) (Fin L) 𝕜) := by
  ext a c
  rw [Matrix.mul_apply]
  have key : ∀ k : Fin L,
      ((τ + τ⁻¹) • (1 : Matrix (Fin L) (Fin L) 𝕜) - adjK 𝕜 L) a k * geomC τ L k c =
        (if k = a then (τ + τ⁻¹) * geomC τ L k c else 0) -
        ((if k = lgSucc a then geomC τ L k c else 0) +
        (if k = lgPred a then geomC τ L k c else 0)) := by
    intro k
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      adjK_apply, eq_comm (a := a) (b := k)]
    split_ifs <;> ring
  simp_rw [key]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [geomC, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have hA := a.isLt
  have hC := c.isLt
  have hs : (lgSucc a).val = if a.val + 1 < L then a.val + 1 else 0 := rfl
  have hp : (lgPred a).val = if 0 < a.val then a.val - 1 else L - 1 := rfl
  by_cases hac : a = c
  · subst hac
    have e0 : lgD L a a = 0 := by simp [lgD]
    have e1 : lgD L (lgSucc a) a = L - 1 := by
      unfold lgD; rw [hs]; split_ifs <;> omega
    have e2 : lgD L (lgPred a) a = 1 := by
      unfold lgD; rw [hp]; split_ifs <;> omega
    rw [e0, e1, e2]
    simp only [↓reduceIte, mul_one]
    linear_combination (-1 : 𝕜) * geomV_rec_zero hτ hD (by omega : 2 ≤ L)
  · have hne : a.val ≠ c.val := fun h => hac (Fin.ext h)
    have hd1 : 1 ≤ lgD L a c := by unfold lgD; split_ifs <;> omega
    have hd2 : lgD L a c < L := lgD_lt a c
    have e1 : lgD L (lgSucc a) c = lgD L a c - 1 := by
      unfold lgD; rw [hs]; split_ifs <;> omega
    rw [e1]
    simp only [hac, ↓reduceIte, mul_zero]
    by_cases hlt : lgD L a c + 1 < L
    · have e2 : lgD L (lgPred a) c = lgD L a c + 1 := by
        unfold lgD at hlt ⊢; rw [hp]; split_ifs at hlt ⊢ <;> omega
      rw [e2]
      linear_combination (-1 : 𝕜) * geomV_rec_int hτ L _ hd1 hlt.le
    · have e2 : lgD L (lgPred a) c = 0 := by
        unfold lgD at hlt ⊢; rw [hp]; split_ifs at hlt ⊢ <;> omega
      rw [e2, ← geomV_L τ L]
      have : lgD L a c + 1 = L := by omega
      have h := geomV_rec_int hτ L _ hd1 this.le
      rw [this] at h
      linear_combination (-1 : 𝕜) * h

/-- The row sum of the periodized geometric profile, `(1 + τ)/(1 - τ)`. -/
private lemma sum_geomV {τ : 𝕜} (h1 : τ ≠ 1) {L : ℕ} (hD : 1 - τ ^ L ≠ 0) :
    ∑ k ∈ Finset.range L, geomV τ L k = (1 + τ) / (1 - τ) := by
  have h1' : 1 - τ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  unfold geomV
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  have hA : ∑ k ∈ Finset.range L, τ ^ k = (1 - τ ^ L) / (1 - τ) := by
    rw [geom_sum_eq h1]; field_simp; ring
  have hB : ∑ k ∈ Finset.range L, τ ^ (L - k) = τ * ((1 - τ ^ L) / (1 - τ)) := by
    rw [← hA, Finset.mul_sum]
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [← pow_succ']
    congr 1
    omega
  rw [hA, hB]
  field_simp

private lemma geomC_row_sum {τ : 𝕜} (h1 : τ ≠ 1) {L : ℕ} (hD : 1 - τ ^ L ≠ 0) (a : Fin L) :
    ∑ c, geomC τ L a c = (1 + τ) / (1 - τ) := by
  simp only [geomC, Matrix.of_apply]
  rw [sum_lgD_row a (fun k => geomV τ L k), sum_geomV h1 hD]

private lemma geomC_col_sum {τ : 𝕜} (h1 : τ ≠ 1) {L : ℕ} (hD : 1 - τ ^ L ≠ 0) (c : Fin L) :
    ∑ a, geomC τ L a c = (1 + τ) / (1 - τ) := by
  simp only [geomC, Matrix.of_apply]
  rw [sum_lgD_col c (fun k => geomV τ L k), sum_geomV h1 hD]

end Geom

/-! ### The free transforms at hopping `1` near the bulk -/

section Scalar

variable {w : ℂ}

private lemma lg_s_sq (w : ℂ) : freeS 1 w ^ 2 = w ^ 2 - 4 := by
  have := freeS_sq 1 w; simpa using this

private lemma lg_s_ne (hw : 0 < w.im) : freeS 1 w ≠ 0 := by
  intro h; have := freeS_im_pos 1 w hw; rw [h] at this; simp at this

private lemma lg_ws_ne (hw : 0 < w.im) : w + freeS 1 w ≠ 0 := by
  intro h
  have h2 := congrArg Complex.im h
  simp only [Complex.add_im, Complex.zero_im] at h2
  linarith [freeS_im_pos 1 w hw]

private lemma lg_rho_eq (hw : 0 < w.im) : freeRho 1 w = (w - freeS 1 w) / 2 := by
  unfold freeRho
  rw [div_eq_div_iff (lg_ws_ne hw) two_ne_zero]
  push_cast
  linear_combination lg_s_sq w

private lemma lg_rho_ne (hw : 0 < w.im) : freeRho 1 w ≠ 0 := by
  unfold freeRho; exact div_ne_zero (by norm_num) (lg_ws_ne hw)

private lemma lg_rho_inv (_hw : 0 < w.im) : (freeRho 1 w)⁻¹ = (w + freeS 1 w) / 2 := by
  unfold freeRho; rw [inv_div]; push_cast; ring

private lemma lg_rho_add_inv (hw : 0 < w.im) : freeRho 1 w + (freeRho 1 w)⁻¹ = w := by
  rw [lg_rho_inv hw, lg_rho_eq hw]; ring

private lemma lg_rho_inv_sub (hw : 0 < w.im) : (freeRho 1 w)⁻¹ - freeRho 1 w = freeS 1 w := by
  rw [lg_rho_inv hw, lg_rho_eq hw]; ring

private lemma lg_rho_lt (hw : 0 < w.im) : ‖freeRho 1 w‖ < 1 := norm_freeRho_lt_one 1 w hw

private lemma lg_f_mul_s (hw : 0 < w.im) : freeT 1 w * freeS 1 w = -1 := by
  rw [freeT_eq 1 w hw]; field_simp [lg_s_ne hw]

private lemma lg_norm_f (hw : 0 < w.im) : ‖freeT 1 w‖ = ‖freeS 1 w‖⁻¹ := by
  rw [freeT_eq 1 w hw, norm_neg, norm_inv]

/-- `Im w ‖ρ‖² = -Im ρ (1 - ‖ρ‖²)`. -/
private lemma lg_im_w (hw : 0 < w.im) :
    w.im * ‖freeRho 1 w‖ ^ 2 = -(freeRho 1 w).im * (1 - ‖freeRho 1 w‖ ^ 2) := by
  have h := congrArg Complex.im (lg_rho_add_inv hw)
  rw [Complex.add_im, Complex.inv_im] at h
  have hn : Complex.normSq (freeRho 1 w) ≠ 0 := by
    rw [Ne, Complex.normSq_eq_zero]; exact lg_rho_ne hw
  rw [Complex.sq_norm, ← h]
  field_simp
  ring

/-- `Im s ‖ρ‖² = -Im ρ (1 + ‖ρ‖²)`. -/
private lemma lg_im_s (hw : 0 < w.im) :
    (freeS 1 w).im * ‖freeRho 1 w‖ ^ 2 = -(freeRho 1 w).im * (1 + ‖freeRho 1 w‖ ^ 2) := by
  have h := congrArg Complex.im (lg_rho_inv_sub hw)
  rw [Complex.sub_im, Complex.inv_im] at h
  have hn : Complex.normSq (freeRho 1 w) ≠ 0 := by
    rw [Ne, Complex.normSq_eq_zero]; exact lg_rho_ne hw
  rw [Complex.sq_norm, ← h]
  field_simp
  ring

private lemma lg_neg_im_rho_pos (hw : 0 < w.im) : 0 < -(freeRho 1 w).im := by
  have h := lg_im_w hw
  have h1 : 0 < 1 - ‖freeRho 1 w‖ ^ 2 := by
    have := lg_rho_lt hw
    have := norm_nonneg (freeRho 1 w)
    nlinarith
  have h2 : 0 < ‖freeRho 1 w‖ := norm_pos_iff.mpr (lg_rho_ne hw)
  have h3 : 0 < w.im * ‖freeRho 1 w‖ ^ 2 := by positivity
  rw [h] at h3
  exact pos_of_mul_pos_left h3 h1.le

/-- The line Ward identity in closed form: `Im f (1 - ‖ρ‖²) = ‖f‖² Im w (1 + ‖ρ‖²)`. -/
private lemma lg_ward (hw : 0 < w.im) :
    (freeT 1 w).im * (1 - ‖freeRho 1 w‖ ^ 2) =
      ‖freeT 1 w‖ ^ 2 * w.im * (1 + ‖freeRho 1 w‖ ^ 2) := by
  have hs := lg_s_ne hw
  have hn : 0 < ‖freeRho 1 w‖ := norm_pos_iff.mpr (lg_rho_ne hw)
  have h1 := lg_im_w hw
  have h2 := lg_im_s hw
  have key : (freeS 1 w).im * (1 - ‖freeRho 1 w‖ ^ 2) = w.im * (1 + ‖freeRho 1 w‖ ^ 2) := by
    have hn2 : ‖freeRho 1 w‖ ^ 2 ≠ 0 := by positivity
    apply mul_right_cancel₀ hn2
    linear_combination (1 - ‖freeRho 1 w‖ ^ 2) * h2 - (1 + ‖freeRho 1 w‖ ^ 2) * h1
  have hf : (freeT 1 w).im = ‖freeT 1 w‖ ^ 2 * (freeS 1 w).im := by
    rw [freeT_eq 1 w hw, Complex.neg_im, Complex.inv_im, norm_neg, norm_inv, inv_pow,
      Complex.sq_norm]
    ring
  rw [hf, mul_assoc, key]
  ring

/-! #### Bounds for `‖w‖ ≤ 3` -/

private lemma lg_norm_s_le (hw3 : ‖w‖ ≤ 3) : ‖freeS 1 w‖ ≤ 4 := by
  have h : ‖freeS 1 w‖ ^ 2 ≤ 16 := by
    rw [← norm_pow, lg_s_sq]
    calc ‖w ^ 2 - 4‖ ≤ ‖w ^ 2‖ + ‖(4 : ℂ)‖ := norm_sub_le _ _
      _ = ‖w‖ ^ 2 + 4 := by rw [norm_pow]; norm_num
      _ ≤ 16 := by nlinarith [norm_nonneg w]
  nlinarith [norm_nonneg (freeS 1 w)]

private lemma lg_norm_rho_ge (hw : 0 < w.im) (hw3 : ‖w‖ ≤ 3) : 1 / 4 ≤ ‖freeRho 1 w‖ := by
  have hinv : ‖(freeRho 1 w)⁻¹‖ ≤ 4 := by
    rw [lg_rho_inv hw, norm_div]
    have := norm_add_le w (freeS 1 w)
    have := lg_norm_s_le hw3
    simp only [Complex.norm_ofNat]
    linarith
  have hn : 0 < ‖freeRho 1 w‖ := norm_pos_iff.mpr (lg_rho_ne hw)
  rw [norm_inv] at hinv
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
  have := (inv_le_iff_one_le_mul₀' hn).mp hinv
  linarith

/-- `1 - ‖ρ‖² ≥ Im w / 16` for `‖w‖ ≤ 3`. -/
private lemma lg_gap_ge (hw : 0 < w.im) (hw3 : ‖w‖ ≤ 3) :
    w.im / 16 ≤ 1 - ‖freeRho 1 w‖ ^ 2 := by
  have h := lg_im_w hw
  have hρ := lg_neg_im_rho_pos hw
  have hr := lg_norm_rho_ge hw hw3
  have hlt := lg_rho_lt hw
  have him : -(freeRho 1 w).im ≤ 1 := by
    have := Complex.abs_im_le_norm (freeRho 1 w)
    have := neg_abs_le (freeRho 1 w).im
    linarith
  have h1 : 0 ≤ 1 - ‖freeRho 1 w‖ ^ 2 := by nlinarith [norm_nonneg (freeRho 1 w)]
  have hr2 : 1 / 16 ≤ ‖freeRho 1 w‖ ^ 2 := by nlinarith
  have h2 : w.im / 16 ≤ w.im * ‖freeRho 1 w‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hr2 hw.le]
  nlinarith

/-! #### Bounds in the bulk `|Re w| ≤ 2 - k` -/

/-- `Im s ≥ k` for `|Re w| ≤ 2 - k`, `0 < k ≤ 1`. -/
private lemma lg_im_s_ge_k {k : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) (hw : 0 < w.im) (hre : |w.re| ≤ 2 -
    k) :
    k ≤ (freeS 1 w).im := by
  have h := congrArg Complex.re (lg_s_sq w)
  simp only [sq, Complex.mul_re, Complex.sub_re] at h
  norm_num at h
  have hb := freeS_im_pos 1 w hw
  have hx : w.re ^ 2 ≤ (2 - k) ^ 2 := by
    have := abs_nonneg w.re
    nlinarith [sq_abs w.re]
  have : k ^ 2 ≤ (freeS 1 w).im ^ 2 := by
    nlinarith [sq_nonneg (freeS 1 w).re, sq_nonneg w.im]
  nlinarith

private lemma lg_norm_s_ge_k {k : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) (hw : 0 < w.im) (hre : |w.re| ≤ 2 -
    k) :
    k ≤ ‖freeS 1 w‖ :=
  (lg_im_s_ge_k hk hk1 hw hre).trans (Complex.im_le_norm _)

private lemma lg_norm_f_le {k : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) (hw : 0 < w.im) (hre : |w.re| ≤ 2 -
    k) :
    ‖freeT 1 w‖ ≤ 1 / k := by
  rw [lg_norm_f hw, one_div]
  exact inv_anti₀ hk (lg_norm_s_ge_k hk hk1 hw hre)

private lemma lg_im_f_ge {k : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) (hw : 0 < w.im) (hre : |w.re| ≤ 2 - k)
    (hw3 : ‖w‖ ≤ 3) : k / 16 ≤ (freeT 1 w).im := by
  have hs := lg_s_ne hw
  have hf : (freeT 1 w).im = (freeS 1 w).im / ‖freeS 1 w‖ ^ 2 := by
    rw [freeT_eq 1 w hw, Complex.neg_im, Complex.inv_im, Complex.sq_norm]; ring
  rw [hf]
  have h1 := lg_im_s_ge_k hk hk1 hw hre
  have h2 := lg_norm_s_le hw3
  have h3 : 0 < ‖freeS 1 w‖ := norm_pos_iff.mpr hs
  have h4 : ‖freeS 1 w‖ ^ 2 ≤ 16 := by nlinarith
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- `-Im ρ ≥ k/4` for `Im w ≤ k/2`. -/
private lemma lg_neg_im_rho_ge {k : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) (hw : 0 < w.im)
    (hre : |w.re| ≤ 2 - k) (hwk : w.im ≤ k / 2) : k / 4 ≤ -(freeRho 1 w).im := by
  rw [lg_rho_eq hw]
  have := lg_im_s_ge_k hk hk1 hw hre
  simp only [Complex.div_ofNat_im, Complex.sub_im]
  linarith

/-- `1 - ‖ρ‖² ≤ 4 Im w / k` in the bulk at small height. -/
private lemma lg_gap_le {k : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) (hw : 0 < w.im)
    (hre : |w.re| ≤ 2 - k) (hwk : w.im ≤ k / 2) :
    1 - ‖freeRho 1 w‖ ^ 2 ≤ 4 * w.im / k := by
  have h := lg_im_w hw
  have hρ := lg_neg_im_rho_ge hk hk1 hw hre hwk
  have hlt := lg_rho_lt hw
  have h1 : 0 ≤ 1 - ‖freeRho 1 w‖ ^ 2 := by nlinarith [norm_nonneg (freeRho 1 w)]
  have h2 : w.im * ‖freeRho 1 w‖ ^ 2 ≤ w.im := by
    have : ‖freeRho 1 w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (freeRho 1 w)]
    nlinarith
  rw [le_div_iff₀ hk]
  nlinarith

/-! #### Lipschitz bounds in the bulk -/

section Lip

variable {w₁ w₂ : ℂ} {k : ℝ}

private lemma lg_s_lip (hk : 0 < k) (hk1 : k ≤ 1) (h1 : 0 < w₁.im) (h2 : 0 < w₂.im)
    (hr1 : |w₁.re| ≤ 2 - k) (hr2 : |w₂.re| ≤ 2 - k) (n1 : ‖w₁‖ ≤ 3) (n2 : ‖w₂‖ ≤ 3) :
    ‖freeS 1 w₁ - freeS 1 w₂‖ ≤ 3 / k * ‖w₁ - w₂‖ := by
  have e : (freeS 1 w₁ - freeS 1 w₂) * (freeS 1 w₁ + freeS 1 w₂) = (w₁ - w₂) * (w₁ + w₂) := by
    linear_combination lg_s_sq w₁ - lg_s_sq w₂
  have hsum : 2 * k ≤ ‖freeS 1 w₁ + freeS 1 w₂‖ := by
    have := Complex.im_le_norm (freeS 1 w₁ + freeS 1 w₂)
    rw [Complex.add_im] at this
    linarith [lg_im_s_ge_k hk hk1 h1 hr1, lg_im_s_ge_k hk hk1 h2 hr2]
  have hw : ‖w₁ + w₂‖ ≤ 6 := (norm_add_le _ _).trans (by linarith)
  have hn := congrArg norm e
  rw [norm_mul, norm_mul] at hn
  have hpos : 0 < ‖freeS 1 w₁ + freeS 1 w₂‖ := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hk]
  have : ‖freeS 1 w₁ - freeS 1 w₂‖ * (2 * k) ≤ ‖w₁ - w₂‖ * 6 := by
    calc ‖freeS 1 w₁ - freeS 1 w₂‖ * (2 * k)
        ≤ ‖freeS 1 w₁ - freeS 1 w₂‖ * ‖freeS 1 w₁ + freeS 1 w₂‖ :=
          mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
      _ = ‖w₁ - w₂‖ * ‖w₁ + w₂‖ := hn
      _ ≤ ‖w₁ - w₂‖ * 6 := mul_le_mul_of_nonneg_left hw (norm_nonneg _)
  nlinarith

private lemma lg_f_lip (hk : 0 < k) (hk1 : k ≤ 1) (h1 : 0 < w₁.im) (h2 : 0 < w₂.im)
    (hr1 : |w₁.re| ≤ 2 - k) (hr2 : |w₂.re| ≤ 2 - k) (n1 : ‖w₁‖ ≤ 3) (n2 : ‖w₂‖ ≤ 3) :
    ‖freeT 1 w₁ - freeT 1 w₂‖ ≤ 3 / k ^ 3 * ‖w₁ - w₂‖ := by
  have hs1 := lg_s_ne h1
  have hs2 := lg_s_ne h2
  have e : freeT 1 w₁ - freeT 1 w₂ =
      (freeS 1 w₁ - freeS 1 w₂) * (freeS 1 w₁)⁻¹ * (freeS 1 w₂)⁻¹ := by
    rw [freeT_eq 1 w₁ h1, freeT_eq 1 w₂ h2]; field_simp; ring
  rw [e, norm_mul, norm_mul, norm_inv, norm_inv]
  have a1 := lg_norm_s_ge_k hk hk1 h1 hr1
  have a2 := lg_norm_s_ge_k hk hk1 h2 hr2
  have hl := lg_s_lip hk hk1 h1 h2 hr1 hr2 n1 n2
  have i1 : ‖freeS 1 w₁‖⁻¹ ≤ k⁻¹ := inv_anti₀ hk a1
  have i2 : ‖freeS 1 w₂‖⁻¹ ≤ k⁻¹ := inv_anti₀ hk a2
  calc ‖freeS 1 w₁ - freeS 1 w₂‖ * ‖freeS 1 w₁‖⁻¹ * ‖freeS 1 w₂‖⁻¹
      ≤ (3 / k * ‖w₁ - w₂‖) * k⁻¹ * k⁻¹ := by gcongr
    _ = 3 / k ^ 3 * ‖w₁ - w₂‖ := by field_simp

private lemma lg_rho_lip (hk : 0 < k) (hk1 : k ≤ 1) (h1 : 0 < w₁.im) (h2 : 0 < w₂.im)
    (hr1 : |w₁.re| ≤ 2 - k) (hr2 : |w₂.re| ≤ 2 - k) (n1 : ‖w₁‖ ≤ 3) (n2 : ‖w₂‖ ≤ 3) :
    ‖freeRho 1 w₁ - freeRho 1 w₂‖ ≤ 2 / k * ‖w₁ - w₂‖ := by
  rw [lg_rho_eq h1, lg_rho_eq h2]
  have e : (w₁ - freeS 1 w₁) / 2 - (w₂ - freeS 1 w₂) / 2 =
      ((w₁ - w₂) - (freeS 1 w₁ - freeS 1 w₂)) / 2 := by ring
  rw [e, norm_div, Complex.norm_ofNat]
  have hl := lg_s_lip hk hk1 h1 h2 hr1 hr2 n1 n2
  have := norm_sub_le (w₁ - w₂) (freeS 1 w₁ - freeS 1 w₂)
  have h3 : 1 ≤ 1 / k := by rw [le_div_iff₀ hk]; linarith
  have : ‖w₁ - w₂‖ ≤ 1 / k * ‖w₁ - w₂‖ := by
    nlinarith [norm_nonneg (w₁ - w₂)]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have e2 : 2 / k * ‖w₁ - w₂‖ * 2 = 4 * (1 / k * ‖w₁ - w₂‖) := by ring
  rw [e2]
  have e3 : 3 / k * ‖w₁ - w₂‖ = 3 * (1 / k * ‖w₁ - w₂‖) := by ring
  linarith

end Lip

end Scalar

/-! ### The free resolvent on the cycle -/

/-- The free resolvent of `A_L` at `w ∈ ℂ_+` is `f(w)` times the periodized geometric kernel with
ratio `ρ(w)`. -/
private lemma lg_resolvent_eq {w : ℂ} (hw : 0 < w.im) {L : ℕ} (hL : 3 ≤ L) :
    ((1 : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹ =
      freeT 1 w • geomC (freeRho 1 w) L := by
  have hρ0 := lg_rho_ne hw
  have hD : 1 - freeRho 1 w ^ L ≠ 0 := by
    intro h
    have h1 : freeRho 1 w ^ L = 1 := by linear_combination -h
    have h2 : ‖freeRho 1 w‖ ^ L < 1 := pow_lt_one₀ (norm_nonneg _) (lg_rho_lt hw) (by omega)
    rw [← norm_pow, h1, norm_one] at h2
    exact lt_irrefl _ h2
  have hG := geomC_mul hρ0 hD hL
  rw [lg_rho_add_inv hw, lg_rho_inv_sub hw, ← cycleAdj_eq_adjK] at hG
  apply Matrix.inv_eq_right_inv
  have e : ((1 : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ)) =
      -(w • (1 : Matrix (Fin L) (Fin L) ℂ) - cycleAdj L) := by
    rw [one_smul]; abel
  rw [e, Matrix.neg_mul, Matrix.mul_smul, hG, smul_smul]
  rw [lg_f_mul_s hw]
  simp

private lemma lg_dysonMat_eq (γ : ℝ) {L : ℕ} (hL : 3 ≤ L) (E : ℝ) (m : ℂ)
    (hw : 0 < ((E : ℂ) + γ * m).im) :
    dysonMat 1 γ L E m = freeT 1 ((E : ℂ) + γ * m) • geomC (freeRho 1 ((E : ℂ) + γ * m)) L := by
  rw [← lg_resolvent_eq hw hL]
  unfold dysonMat
  simp

/-- Closed form of the finite Fourier average: `f_L = f (1 + ρ^L)/(1 - ρ^L)`. -/
private lemma lg_freeTL_eq {w : ℂ} (hw : 0 < w.im) {L : ℕ} (hL : 3 ≤ L) :
    freeTL 1 L w = freeT 1 w * ((1 + freeRho 1 w ^ L) / (1 - freeRho 1 w ^ L)) := by
  have hw' : 0 < (w + ((0 : ℝ) : ℂ) * 0).im := by simpa using hw
  have h := dysonMat_diag 1 0 L (by omega) w 0 hw' ⟨0, by omega⟩
  unfold dysonRHSV at h
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
  rw [← h]
  have e : dysonMat 1 0 L w 0 = ((1 : ℂ) • cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹ := by
    unfold dysonMat; simp
  rw [e, lg_resolvent_eq hw hL]
  simp [geomC, geomV, lgD]

/-! ### Fixed points of the Dyson maps at large coupling -/

/-- Banach's fixed point theorem on a closed disk, with contraction factor `1/2`. -/
private lemma lg_fixed (Φ : ℂ → ℂ) (c₀ : ℂ) (r : ℝ)
    (hmap : ∀ μ ∈ Metric.closedBall c₀ r, Φ μ ∈ Metric.closedBall c₀ r)
    (hlip : ∀ μ₁ ∈ Metric.closedBall c₀ r, ∀ μ₂ ∈ Metric.closedBall c₀ r,
      ‖Φ μ₁ - Φ μ₂‖ ≤ 1 / 2 * ‖μ₁ - μ₂‖) (hr : 0 ≤ r) :
    ∃ μ ∈ Metric.closedBall c₀ r, Φ μ = μ := by
  have hsf : Set.MapsTo Φ (Metric.closedBall c₀ r) (Metric.closedBall c₀ r) := hmap
  have hK : ((1 / 2 : NNReal) : ℝ) = 1 / 2 := by simp
  have hf : ContractingWith (1 / 2 : NNReal) (hsf.restrict Φ _ _) := by
    refine ⟨by rw [← NNReal.coe_lt_coe]; norm_num, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Subtype.dist_eq, Subtype.dist_eq, hK]
    simp only [Set.MapsTo.val_restrict_apply, dist_eq_norm]
    exact hlip x x.2 y y.2
  obtain ⟨y, hy, hfix, -⟩ := hf.exists_fixedPoint' Metric.isClosed_closedBall.isComplete hsf
    (Metric.mem_closedBall_self hr) (edist_ne_top _ _)
  exact ⟨y, hy, hfix⟩

/-- The center `f(E + iγ)` of the disk carrying the roots. -/
private def lgC0 (γ E : ℝ) : ℂ := freeT 1 ((E : ℂ) + (γ : ℂ) * I)

section Core

variable {k γ E : ℝ}

private lemma lg_c0_facts (hk : 0 < k) (hk1 : k ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hE : |E| ≤ 2 - 2 * k) : k / 16 ≤ (lgC0 γ E).im ∧ ‖lgC0 γ E‖ ≤ 1 / k := by
  have him : 0 < ((E : ℂ) + (γ : ℂ) * I).im := by simpa using hγ
  have hre : |((E : ℂ) + (γ : ℂ) * I).re| ≤ 2 - k := by simp; linarith
  have hn : ‖(E : ℂ) + (γ : ℂ) * I‖ ≤ 3 := by
    calc ‖(E : ℂ) + (γ : ℂ) * I‖ ≤ ‖(E : ℂ)‖ + ‖(γ : ℂ) * I‖ := norm_add_le _ _
      _ = |E| + γ := by simp [abs_of_pos hγ]
      _ ≤ 3 := by linarith
  exact ⟨lg_im_f_ge hk hk1 him hre hn, lg_norm_f_le hk hk1 him hre⟩

/-- Facts about points of the disk `closedBall (lgC0 γ E) (k/32)` and `w = E + γμ`. -/
private lemma lg_ball_facts (hk : 0 < k) (hk1 : k ≤ 1) (hγ : 0 < γ) (hγ0 : γ ≤ k ^ 5 / 1000)
    (hE : |E| ≤ 2 - 2 * k) {μ : ℂ} (hμ : μ ∈ Metric.closedBall (lgC0 γ E) (k / 32)) :
    k / 32 ≤ μ.im ∧ ‖μ‖ ≤ 2 / k ∧ 0 < ((E : ℂ) + γ * μ).im ∧
      γ * (k / 32) ≤ ((E : ℂ) + γ * μ).im ∧ ((E : ℂ) + γ * μ).im ≤ 2 * γ / k ∧
      ((E : ℂ) + γ * μ).im ≤ k / 2 ∧ |((E : ℂ) + γ * μ).re| ≤ 2 - k ∧
      ‖(E : ℂ) + γ * μ‖ ≤ 3 := by
  have hk5 : k ^ 5 ≤ k ^ 2 := pow_le_pow_of_le_one hk.le hk1 (by norm_num)
  have hk2 : k ^ 2 ≤ k := by nlinarith
  have hγ1 : γ ≤ 1 := by nlinarith
  have hγk : γ ≤ k ^ 2 / 1000 := by linarith
  obtain ⟨hc1, hc2⟩ := lg_c0_facts hk hk1 hγ hγ1 hE
  rw [Metric.mem_closedBall, dist_eq_norm] at hμ
  have h1 : k / 32 ≤ μ.im := by
    have := Complex.abs_im_le_norm (μ - lgC0 γ E)
    rw [Complex.sub_im] at this
    have := neg_abs_le (μ.im - (lgC0 γ E).im)
    linarith
  have h2 : ‖μ‖ ≤ 2 / k := by
    have := norm_le_norm_add_norm_sub' μ (lgC0 γ E)
    have h3 : k / 32 ≤ 1 / k := by
      rw [div_le_div_iff₀ (by norm_num) hk]; nlinarith
    have : 1 / k + 1 / k = 2 / k := by ring
    linarith
  have hwim : ((E : ℂ) + γ * μ).im = γ * μ.im := by simp
  have hwre : ((E : ℂ) + γ * μ).re = E + γ * μ.re := by simp
  have hγμ : γ * ‖μ‖ ≤ 2 * γ / k := by
    have := mul_le_mul_of_nonneg_left h2 hγ.le
    linarith [show γ * (2 / k) = 2 * γ / k by ring]
  have h2γ : 2 * γ / k ≤ k / 2 := by
    rw [div_le_div_iff₀ hk (by norm_num)]; nlinarith
  have himle : μ.im ≤ ‖μ‖ := Complex.im_le_norm μ
  refine ⟨h1, h2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hwim]; have : 0 < μ.im := by linarith
    positivity
  · rw [hwim]; exact mul_le_mul_of_nonneg_left h1 hγ.le
  · rw [hwim]; nlinarith
  · rw [hwim]; nlinarith
  · rw [hwre]
    have := Complex.abs_re_le_norm μ
    have : |γ * μ.re| ≤ γ * ‖μ‖ := by
      rw [abs_mul, abs_of_pos hγ]; exact mul_le_mul_of_nonneg_left this hγ.le
    have := abs_add_le E (γ * μ.re)
    linarith
  · calc ‖(E : ℂ) + γ * μ‖ ≤ ‖(E : ℂ)‖ + ‖(γ : ℂ) * μ‖ := norm_add_le _ _
      _ = |E| + γ * ‖μ‖ := by simp [abs_of_pos hγ]
      _ ≤ 3 := by linarith

/-- The line Dyson map contracts the disk. -/
private lemma lg_line_map (hk : 0 < k) (hk1 : k ≤ 1) (hγ : 0 < γ) (hγ0 : γ ≤ k ^ 5 / 1000)
    (hE : |E| ≤ 2 - 2 * k) :
    (∀ μ ∈ Metric.closedBall (lgC0 γ E) (k / 32),
      dist (freeT 1 ((E : ℂ) + γ * μ)) (lgC0 γ E) ≤ k / 64) ∧
    ∀ μ₁ ∈ Metric.closedBall (lgC0 γ E) (k / 32), ∀ μ₂ ∈ Metric.closedBall (lgC0 γ E) (k / 32),
      ‖freeT 1 ((E : ℂ) + γ * μ₁) - freeT 1 ((E : ℂ) + γ * μ₂)‖ ≤ 3 * γ / k ^ 3 * ‖μ₁ - μ₂‖ := by
  have hk5 : k ^ 5 ≤ k ^ 2 := pow_le_pow_of_le_one hk.le hk1 (by norm_num)
  have hγ1 : γ ≤ 1 := by nlinarith
  have h0im : 0 < ((E : ℂ) + (γ : ℂ) * I).im := by simpa using hγ
  have h0re : |((E : ℂ) + (γ : ℂ) * I).re| ≤ 2 - k := by simp; linarith
  have h0n : ‖(E : ℂ) + (γ : ℂ) * I‖ ≤ 3 := by
    calc ‖(E : ℂ) + (γ : ℂ) * I‖ ≤ ‖(E : ℂ)‖ + ‖(γ : ℂ) * I‖ := norm_add_le _ _
      _ = |E| + γ := by simp [abs_of_pos hγ]
      _ ≤ 3 := by linarith
  refine ⟨fun μ hμ => ?_, fun μ₁ h1 μ₂ h2 => ?_⟩
  · obtain ⟨-, hn, hp, -, -, -, hr, hw3⟩ := lg_ball_facts hk hk1 hγ hγ0 hE hμ
    rw [dist_eq_norm, lgC0]
    refine (lg_f_lip hk hk1 hp h0im hr h0re hw3 h0n).trans ?_
    have e : (E : ℂ) + γ * μ - ((E : ℂ) + γ * I) = γ * (μ - I) := by ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hγ.le]
    have h3k : 2 / k + 1 ≤ 3 / k := by
      rw [div_add_one hk.ne', div_le_div_iff_of_pos_right hk]; linarith
    have hμI : ‖μ - I‖ ≤ 3 / k := (norm_sub_le _ _).trans (by simp; linarith)
    calc 3 / k ^ 3 * (γ * ‖μ - I‖) ≤ 3 / k ^ 3 * (γ * (3 / k)) := by gcongr
      _ = 9 * γ / k ^ 4 := by field_simp; ring
      _ ≤ k / 64 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [pow_pos hk 5]
  · obtain ⟨-, -, hp1, -, -, -, hr1, n1⟩ := lg_ball_facts hk hk1 hγ hγ0 hE h1
    obtain ⟨-, -, hp2, -, -, -, hr2, n2⟩ := lg_ball_facts hk hk1 hγ hγ0 hE h2
    refine (lg_f_lip hk hk1 hp1 hp2 hr1 hr2 n1 n2).trans (le_of_eq ?_)
    have e : (E : ℂ) + γ * μ₁ - ((E : ℂ) + γ * μ₂) = γ * (μ₁ - μ₂) := by ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hγ.le]
    ring

end Core

/-! ### Tails and powers -/

private lemma lg_tail_le (a H : ℝ) (ha : 0 < a) (hH : 0 ≤ H) :
    (1 + H) * Real.exp (-(a * H)) ≤ (1 + 2 / a) * Real.exp (-(a * H / 2)) := by
  have h1 : 1 + a * H / 2 ≤ Real.exp (a * H / 2) := by
    have := Real.add_one_le_exp (a * H / 2); linarith
  have h2 : Real.exp (-(a * H)) = Real.exp (-(a * H / 2)) * Real.exp (-(a * H / 2)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp (a * H / 2) * Real.exp (-(a * H / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hp : 0 < Real.exp (-(a * H / 2)) := Real.exp_pos _
  have hHle : H ≤ 2 / a * Real.exp (a * H / 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ ha]; nlinarith
  have hE1 : 1 ≤ Real.exp (a * H / 2) := Real.one_le_exp (by positivity)
  rw [h2]
  have : (1 + H) * Real.exp (-(a * H / 2)) ≤ 1 + 2 / a := by
    calc (1 + H) * Real.exp (-(a * H / 2))
        ≤ (Real.exp (a * H / 2) + 2 / a * Real.exp (a * H / 2)) * Real.exp (-(a * H / 2)) := by
          gcongr
      _ = (1 + 2 / a) * (Real.exp (a * H / 2) * Real.exp (-(a * H / 2))) := by ring
      _ = 1 + 2 / a := by rw [h3, mul_one]
  nlinarith

private lemma lg_tail (a ε R₀ : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ R : ℝ, R₀ ≤ R ∧ 0 ≤ R ∧ ∀ H : ℝ, R ≤ H → (1 + H) * Real.exp (-(a * H)) ≤ ε := by
  set K : ℝ := 1 + 2 / a with hK
  have hKp : 0 < K := by positivity
  refine ⟨max (max R₀ 0) (2 / a * Real.log (K / ε)), le_max_of_le_left (le_max_left _ _),
    le_max_of_le_left (le_max_right _ _), fun H hH => ?_⟩
  have hH0 : 0 ≤ H := le_trans (le_max_of_le_left (le_max_right _ _)) hH
  have hH1 : 2 / a * Real.log (K / ε) ≤ H := le_trans (le_max_right _ _) hH
  refine (lg_tail_le a H ha hH0).trans ?_
  have : Real.exp (-(a * H / 2)) ≤ ε / K := by
    have hl : Real.log (K / ε) ≤ a * H / 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ ha] at hH1; linarith
    calc Real.exp (-(a * H / 2)) ≤ Real.exp (-Real.log (K / ε)) := Real.exp_le_exp.mpr (by linarith)
      _ = ε / K := by rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  calc K * Real.exp (-(a * H / 2)) ≤ K * (ε / K) := by gcongr
    _ = ε := by field_simp

private lemma lg_norm_pow_sub_le (a b : ℂ) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ n * max ‖a‖ ‖b‖ ^ (n - 1) * ‖a - b‖ := by
  rw [← geom_sum₂_mul, norm_mul]
  gcongr
  refine (norm_sum_le _ _).trans ?_
  have : ∀ i ∈ Finset.range n, ‖a ^ i * b ^ (n - 1 - i)‖ ≤ max ‖a‖ ‖b‖ ^ (n - 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow, norm_pow]
    calc ‖a‖ ^ i * ‖b‖ ^ (n - 1 - i) ≤ max ‖a‖ ‖b‖ ^ i * max ‖a‖ ‖b‖ ^ (n - 1 - i) := by
          gcongr
          · exact le_max_left _ _
          · exact le_max_right _ _
      _ = max ‖a‖ ‖b‖ ^ (n - 1) := by rw [← pow_add]; congr 1; omega
  refine (Finset.sum_le_sum this).trans ?_
  simp

/-- `‖ρ(w)‖ ≤ e^{-Im w/32}` for `‖w‖ ≤ 3`. -/
private lemma lg_norm_rho_le_exp {w : ℂ} (hw : 0 < w.im) (hw3 : ‖w‖ ≤ 3) :
    ‖freeRho 1 w‖ ≤ Real.exp (-(w.im / 32)) := by
  have h := lg_gap_ge hw hw3
  have h1 : ‖freeRho 1 w‖ ^ 2 ≤ Real.exp (-(w.im / 32)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    have := Real.add_one_le_exp (-(w.im / 16))
    have e : ((2 : ℕ) : ℝ) * -(w.im / 32) = -(w.im / 16) := by push_cast; ring
    rw [e]; linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.exp_pos _).le (by norm_num)).mp h1

/-- The finite Fourier average near `f`: `f(1+z)/(1-z) = f + 2fz/(1-z)`. -/
private lemma lg_ratio_sub (f z : ℂ) (hz : ‖z‖ ≤ 1 / 2) :
    ‖f * ((1 + z) / (1 - z)) - f‖ ≤ 4 * ‖f‖ * ‖z‖ := by
  have h1 : 1 / 2 ≤ ‖1 - z‖ := by
    have := norm_sub_norm_le (1 : ℂ) z; simp at this; linarith
  have hne : 1 - z ≠ 0 := by intro h; rw [h, norm_zero] at h1; norm_num at h1
  have e : f * ((1 + z) / (1 - z)) - f = 2 * f * z / (1 - z) := by field_simp; ring
  rw [e, norm_div, norm_mul, norm_mul, div_le_iff₀ (by linarith)]
  simp only [Complex.norm_ofNat]
  nlinarith [norm_nonneg f, norm_nonneg z, mul_nonneg (norm_nonneg f) (norm_nonneg z)]

private lemma lg_ratio_lip (f₁ f₂ z₁ z₂ : ℂ) (h1 : ‖z₁‖ ≤ 1 / 2) (h2 : ‖z₂‖ ≤ 1 / 2) :
    ‖f₁ * ((1 + z₁) / (1 - z₁)) - f₂ * ((1 + z₂) / (1 - z₂))‖ ≤
      3 * ‖f₁ - f₂‖ + 8 * ‖f₂‖ * ‖z₁ - z₂‖ := by
  have n1 : 1 / 2 ≤ ‖1 - z₁‖ := by
    have := norm_sub_norm_le (1 : ℂ) z₁; simp at this; linarith
  have n2 : 1 / 2 ≤ ‖1 - z₂‖ := by
    have := norm_sub_norm_le (1 : ℂ) z₂; simp at this; linarith
  have ne1 : 1 - z₁ ≠ 0 := by intro h; rw [h, norm_zero] at n1; norm_num at n1
  have ne2 : 1 - z₂ ≠ 0 := by intro h; rw [h, norm_zero] at n2; norm_num at n2
  have e : f₁ * ((1 + z₁) / (1 - z₁)) - f₂ * ((1 + z₂) / (1 - z₂)) =
      (f₁ - f₂) * ((1 + z₁) / (1 - z₁)) + 2 * f₂ * ((z₁ - z₂) / ((1 - z₁) * (1 - z₂))) := by
    field_simp; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have b1 : ‖(1 + z₁) / (1 - z₁)‖ ≤ 3 := by
    rw [norm_div, div_le_iff₀ (by linarith)]
    have := norm_add_le (1 : ℂ) z₁; simp at this; linarith
  have b2 : ‖(z₁ - z₂) / ((1 - z₁) * (1 - z₂))‖ ≤ 4 * ‖z₁ - z₂‖ := by
    rw [norm_div, norm_mul, div_le_iff₀ (by positivity)]
    have : 1 / 4 ≤ ‖1 - z₁‖ * ‖1 - z₂‖ := by nlinarith
    nlinarith [norm_nonneg (z₁ - z₂)]
  rw [norm_mul, norm_mul, norm_mul]
  simp only [Complex.norm_ofNat]
  have := mul_le_mul_of_nonneg_left b1 (norm_nonneg (f₁ - f₂))
  have := mul_le_mul_of_nonneg_left b2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg f₂))
  nlinarith

section Core2

variable {k γ E : ℝ}

/-- The finite Dyson map: closeness to the line map, and contraction, on the disk. -/
private lemma lg_finite_map (hk : 0 < k) (hk1 : k ≤ 1) (hγ : 0 < γ) (hγ0 : γ ≤ k ^ 5 / 1000)
    (hE : |E| ≤ 2 - 2 * k) {L : ℕ} (hL : 3 ≤ L)
    (htail : (1 + γ * L) * Real.exp (-(k / 1024 * (γ * L))) ≤ k ^ 2 / 256) :
    (∀ μ ∈ Metric.closedBall (lgC0 γ E) (k / 32),
      ‖freeRho 1 ((E : ℂ) + γ * μ)‖ ^ L ≤ Real.exp (-(k / 1024 * (γ * L))) ∧
      ‖freeTL 1 L ((E : ℂ) + γ * μ) - freeT 1 ((E : ℂ) + γ * μ)‖ ≤
        4 / k * Real.exp (-(k / 1024 * (γ * L)))) ∧
    ∀ μ₁ ∈ Metric.closedBall (lgC0 γ E) (k / 32), ∀ μ₂ ∈ Metric.closedBall (lgC0 γ E) (k / 32),
      ‖freeTL 1 L ((E : ℂ) + γ * μ₁) - freeTL 1 L ((E : ℂ) + γ * μ₂)‖ ≤ 1 / 2 * ‖μ₁ - μ₂‖ := by
  set a : ℝ := k / 1024 with ha
  set H : ℝ := γ * L with hH
  have hH0 : 0 ≤ H := by positivity
  have hexp1 : Real.exp (-(a * H)) ≤ k ^ 2 / 256 := by
    have := Real.exp_pos (-(a * H)); nlinarith
  have hk2 : k ^ 2 / 256 ≤ 1 / 2 := by nlinarith
  have hrho : ∀ μ ∈ Metric.closedBall (lgC0 γ E) (k / 32),
      ‖freeRho 1 ((E : ℂ) + γ * μ)‖ ≤ Real.exp (-(γ * k / 1024)) := by
    intro μ hμ
    obtain ⟨-, -, hp, hlo, -, -, -, hw3⟩ := lg_ball_facts hk hk1 hγ hγ0 hE hμ
    refine (lg_norm_rho_le_exp hp hw3).trans (Real.exp_le_exp.mpr ?_)
    linarith
  have hpow : ∀ μ ∈ Metric.closedBall (lgC0 γ E) (k / 32),
      ‖freeRho 1 ((E : ℂ) + γ * μ)‖ ^ L ≤ Real.exp (-(a * H)) := by
    intro μ hμ
    calc ‖freeRho 1 ((E : ℂ) + γ * μ)‖ ^ L ≤ Real.exp (-(γ * k / 1024)) ^ L := by
          gcongr; exact hrho μ hμ
      _ = Real.exp (-(a * H)) := by rw [← Real.exp_nat_mul]; congr 1; rw [ha, hH]; ring
  refine ⟨fun μ hμ => ⟨hpow μ hμ, ?_⟩, fun μ₁ h1 μ₂ h2 => ?_⟩
  · obtain ⟨-, -, hp, -, -, -, hr, hw3⟩ := lg_ball_facts hk hk1 hγ hγ0 hE hμ
    rw [lg_freeTL_eq hp hL]
    have hz : ‖freeRho 1 ((E : ℂ) + γ * μ) ^ L‖ ≤ 1 / 2 := by
      rw [norm_pow]; linarith [hpow μ hμ]
    refine (lg_ratio_sub _ _ hz).trans ?_
    have hf := lg_norm_f_le hk hk1 hp hr
    rw [norm_pow]
    calc 4 * ‖freeT 1 ((E : ℂ) + γ * μ)‖ * ‖freeRho 1 ((E : ℂ) + γ * μ)‖ ^ L
        ≤ 4 * (1 / k) * Real.exp (-(a * H)) := by
          gcongr; exact hpow μ hμ
      _ = 4 / k * Real.exp (-(a * H)) := by ring
  · obtain ⟨-, -, hp1, -, -, -, hr1, n1⟩ := lg_ball_facts hk hk1 hγ hγ0 hE h1
    obtain ⟨-, -, hp2, -, -, -, hr2, n2⟩ := lg_ball_facts hk hk1 hγ hγ0 hE h2
    rw [lg_freeTL_eq hp1 hL, lg_freeTL_eq hp2 hL]
    have hz1 : ‖freeRho 1 ((E : ℂ) + γ * μ₁) ^ L‖ ≤ 1 / 2 := by
      rw [norm_pow]; linarith [hpow μ₁ h1]
    have hz2 : ‖freeRho 1 ((E : ℂ) + γ * μ₂) ^ L‖ ≤ 1 / 2 := by
      rw [norm_pow]; linarith [hpow μ₂ h2]
    refine (lg_ratio_lip _ _ _ _ hz1 hz2).trans ?_
    have hf := lg_f_lip hk hk1 hp1 hp2 hr1 hr2 n1 n2
    have hρ := lg_rho_lip hk hk1 hp1 hp2 hr1 hr2 n1 n2
    have hf2 := lg_norm_f_le hk hk1 hp2 hr2
    have hw : (E : ℂ) + γ * μ₁ - ((E : ℂ) + γ * μ₂) = γ * (μ₁ - μ₂) := by ring
    rw [hw, norm_mul, Complex.norm_real, Real.norm_of_nonneg hγ.le] at hf hρ
    -- the power difference
    set ρ₁ := freeRho 1 ((E : ℂ) + γ * μ₁)
    set ρ₂ := freeRho 1 ((E : ℂ) + γ * μ₂)
    have hM : max ‖ρ₁‖ ‖ρ₂‖ ^ (L - 1) ≤ 4 * Real.exp (-(a * H)) := by
      have hM1 : 1 / 4 ≤ max ‖ρ₁‖ ‖ρ₂‖ := le_max_of_le_left (lg_norm_rho_ge hp1 n1)
      have hML : max ‖ρ₁‖ ‖ρ₂‖ ^ L ≤ Real.exp (-(a * H)) := by
        rcases le_total ‖ρ₁‖ ‖ρ₂‖ with h | h
        · rw [max_eq_right h]; exact hpow μ₂ h2
        · rw [max_eq_left h]; exact hpow μ₁ h1
      have e : max ‖ρ₁‖ ‖ρ₂‖ ^ L = max ‖ρ₁‖ ‖ρ₂‖ * max ‖ρ₁‖ ‖ρ₂‖ ^ (L - 1) := by
        rw [← pow_succ']; congr 1; omega
      have : 0 ≤ max ‖ρ₁‖ ‖ρ₂‖ ^ (L - 1) := by positivity
      nlinarith
    have hz : ‖ρ₁ ^ L - ρ₂ ^ L‖ ≤ 8 / k * H * Real.exp (-(a * H)) * ‖μ₁ - μ₂‖ := by
      refine (lg_norm_pow_sub_le _ _ _).trans ?_
      calc (L : ℝ) * max ‖ρ₁‖ ‖ρ₂‖ ^ (L - 1) * ‖ρ₁ - ρ₂‖
          ≤ L * (4 * Real.exp (-(a * H))) * (2 / k * (γ * ‖μ₁ - μ₂‖)) := by gcongr
        _ = 8 / k * H * Real.exp (-(a * H)) * ‖μ₁ - μ₂‖ := by rw [hH]; ring
    have hHe : H * Real.exp (-(a * H)) ≤ k ^ 2 / 256 := by
      have := Real.exp_pos (-(a * H)); nlinarith
    have hγk : 9 * γ / k ^ 3 ≤ 1 / 100 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [pow_pos hk 5, pow_le_pow_of_le_one hk.le hk1 (show 3 ≤ 5 by norm_num)]
    calc 3 * ‖freeT 1 ((E : ℂ) + γ * μ₁) - freeT 1 ((E : ℂ) + γ * μ₂)‖ +
          8 * ‖freeT 1 ((E : ℂ) + γ * μ₂)‖ * ‖ρ₁ ^ L - ρ₂ ^ L‖
        ≤ 3 * (3 / k ^ 3 * (γ * ‖μ₁ - μ₂‖)) +
          8 * (1 / k) * (8 / k * H * Real.exp (-(a * H)) * ‖μ₁ - μ₂‖) := by gcongr
      _ = (9 * γ / k ^ 3 + 64 / k ^ 2 * (H * Real.exp (-(a * H)))) * ‖μ₁ - μ₂‖ := by
          field_simp; ring
      _ ≤ (1 / 100 + 64 / k ^ 2 * (k ^ 2 / 256)) * ‖μ₁ - μ₂‖ := by gcongr
      _ ≤ 1 / 2 * ‖μ₁ - μ₂‖ := by
          have : 64 / k ^ 2 * (k ^ 2 / 256) = 1 / 4 := by field_simp; norm_num
          rw [this]; gcongr; norm_num

end Core2

section Core3

variable {k γ E : ℝ}

/-- A line solution lies in the disk. -/
private lemma lg_line_in_ball (hk : 0 < k) (hk1 : k ≤ 1) (hγ : 0 < γ) (hγ0 : γ ≤ k ^ 5 / 1000)
    (hE : |E| ≤ 2 - 2 * k) (mInf : ℂ) (hpos : 0 < mInf.im)
    (heq : mInf = freeT 1 ((E : ℂ) + γ * mInf)) :
    mInf ∈ Metric.closedBall (lgC0 γ E) (k / 32) := by
  have hk5 : k ^ 5 ≤ k ^ 2 := pow_le_pow_of_le_one hk.le hk1 (by norm_num)
  have hk2 : k ^ 2 ≤ k := by nlinarith
  have hγ1 : γ ≤ 1 := by nlinarith
  set w : ℂ := (E : ℂ) + γ * mInf with hw
  have hwim : w.im = γ * mInf.im := by simp [hw]
  have hwp : 0 < w.im := by rw [hwim]; positivity
  -- Ward: `γ ‖mInf‖² ≤ 1`
  have hward := lg_ward hwp
  rw [← heq, hwim] at hward
  have hn := lg_rho_lt hwp
  have hn0 := norm_nonneg (freeRho 1 w)
  have hg1 : γ * ‖mInf‖ ^ 2 ≤ 1 := by
    have e : mInf.im * (1 - ‖freeRho 1 w‖ ^ 2) =
        mInf.im * (γ * ‖mInf‖ ^ 2 * (1 + ‖freeRho 1 w‖ ^ 2)) := by rw [hward]; ring
    have e2 := mul_left_cancel₀ hpos.ne' e
    nlinarith [sq_nonneg ‖freeRho 1 w‖, mul_nonneg hγ.le (sq_nonneg ‖mInf‖)]
  have hsmall : γ * ‖mInf‖ ≤ k / 30 := by
    have h1 : (γ * ‖mInf‖) ^ 2 ≤ (k / 30) ^ 2 := by
      have : (γ * ‖mInf‖) ^ 2 = γ * (γ * ‖mInf‖ ^ 2) := by ring
      rw [this]
      have : γ * (γ * ‖mInf‖ ^ 2) ≤ γ := by nlinarith
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp h1
  have hre : |w.re| ≤ 2 - k := by
    have e : w.re = E + γ * mInf.re := by simp [hw]
    rw [e]
    have := Complex.abs_re_le_norm mInf
    have : |γ * mInf.re| ≤ γ * ‖mInf‖ := by
      rw [abs_mul, abs_of_pos hγ]; exact mul_le_mul_of_nonneg_left this hγ.le
    have := abs_add_le E (γ * mInf.re)
    linarith
  have hw3 : ‖w‖ ≤ 3 := by
    calc ‖w‖ ≤ ‖(E : ℂ)‖ + ‖(γ : ℂ) * mInf‖ := norm_add_le _ _
      _ = |E| + γ * ‖mInf‖ := by simp [abs_of_pos hγ]
      _ ≤ 3 := by linarith
  have hm : ‖mInf‖ ≤ 1 / k := by rw [heq]; exact lg_norm_f_le hk hk1 hwp hre
  -- distance to the center
  have h0im : 0 < ((E : ℂ) + (γ : ℂ) * I).im := by simpa using hγ
  have h0re : |((E : ℂ) + (γ : ℂ) * I).re| ≤ 2 - k := by simp; linarith
  have h0n : ‖(E : ℂ) + (γ : ℂ) * I‖ ≤ 3 := by
    calc ‖(E : ℂ) + (γ : ℂ) * I‖ ≤ ‖(E : ℂ)‖ + ‖(γ : ℂ) * I‖ := norm_add_le _ _
      _ = |E| + γ := by simp [abs_of_pos hγ]
      _ ≤ 3 := by linarith
  rw [Metric.mem_closedBall, dist_eq_norm, lgC0]
  have hl := lg_f_lip hk hk1 hwp h0im hre h0re hw3 h0n
  rw [← heq] at hl
  refine hl.trans ?_
  have e : w - ((E : ℂ) + γ * I) = γ * (mInf - I) := by rw [hw]; ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hγ.le]
  have h1k : 1 ≤ 1 / k := by rw [le_div_iff₀ hk]; linarith
  have hmI : ‖mInf - I‖ ≤ 2 / k := by
    refine (norm_sub_le _ _).trans ?_
    simp only [Complex.norm_I]
    linarith [show 2 / k = 1 / k + 1 / k by ring]
  calc 3 / k ^ 3 * (γ * ‖mInf - I‖) ≤ 3 / k ^ 3 * (γ * (2 / k)) := by gcongr
    _ = 6 * γ / k ^ 4 := by field_simp; ring
    _ ≤ k / 32 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [pow_pos hk 5]

end Core3

/-- The large-coupling Dyson solutions at hopping `1` and variance `γ`: existence of the line
and finite solutions, both in the disk around `f(E + iγ)`, uniqueness, and their exponential
closeness (Lemma A.4 [uvp:prop:finite], first display). -/
private lemma lg_core {k : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) :
    ∃ R : ℝ, 3 ≤ R ∧ ∀ γ : ℝ, 0 < γ → γ ≤ k ^ 5 / 1000 → ∀ E : ℝ, |E| ≤ 2 - 2 * k →
      (∃ mInf : ℂ, 0 < mInf.im ∧ mInf = freeT 1 ((E : ℂ) + γ * mInf)) ∧
      (∀ mInf : ℂ, 0 < mInf.im → mInf = freeT 1 ((E : ℂ) + γ * mInf) →
        mInf ∈ Metric.closedBall (lgC0 γ E) (k / 32)) ∧
      (∀ m₁ m₂ : ℂ, 0 < m₁.im → m₁ = freeT 1 ((E : ℂ) + γ * m₁) →
        0 < m₂.im → m₂ = freeT 1 ((E : ℂ) + γ * m₂) → m₁ = m₂) ∧
      ∀ L : ℕ, R ≤ γ * L →
        (1 + γ * L) * Real.exp (-(k / 1024 * (γ * L))) ≤ k ^ 2 / 256 ∧
        (∃ m : ℂ, IsDysonRootV 1 γ L E m) ∧
        ∀ m : ℂ, IsDysonRootV 1 γ L E m →
          m ∈ Metric.closedBall (lgC0 γ E) (k / 32) ∧
          ∀ mInf : ℂ, 0 < mInf.im → mInf = freeT 1 ((E : ℂ) + γ * mInf) →
            ‖m - mInf‖ ≤ 8 / k * Real.exp (-(k / 1024 * (γ * L))) := by
  obtain ⟨R, hR3, -, hR⟩ := lg_tail (k / 1024) (k ^ 2 / 256) 3 (by positivity) (by positivity)
  refine ⟨R, hR3, fun γ hγ hγ0 E hE => ?_⟩
  have hk5 : k ^ 5 ≤ k ^ 2 := pow_le_pow_of_le_one hk.le hk1 (by norm_num)
  have hγ1 : γ ≤ 1 := by nlinarith
  have hkpos : 0 ≤ k / 32 := by positivity
  obtain ⟨hmap, hlip⟩ := lg_line_map hk hk1 hγ hγ0 hE
  -- the line solution
  have hline : ∃ μ ∈ Metric.closedBall (lgC0 γ E) (k / 32), freeT 1 ((E : ℂ) + γ * μ) = μ := by
    refine lg_fixed (fun μ => freeT 1 ((E : ℂ) + γ * μ)) _ _ (fun μ hμ => ?_) (fun μ₁ h1 μ₂ h2 =>
      (hlip μ₁ h1 μ₂ h2).trans ?_) hkpos
    · rw [Metric.mem_closedBall]; exact (hmap μ hμ).trans (by linarith)
    · have hc : 3 * γ / k ^ 3 ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [pow_pos hk 5, pow_le_pow_of_le_one hk.le hk1 (show 3 ≤ 5 by norm_num)]
      exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)
  obtain ⟨mI, hmI, hmIeq⟩ := hline
  have hmIpos : 0 < mI.im := by
    have := (lg_ball_facts hk hk1 hγ hγ0 hE hmI).1; linarith
  have hin := lg_line_in_ball hk hk1 hγ hγ0 hE
  have huniq : ∀ m₁ m₂ : ℂ, 0 < m₁.im → m₁ = freeT 1 ((E : ℂ) + γ * m₁) →
      0 < m₂.im → m₂ = freeT 1 ((E : ℂ) + γ * m₂) → m₁ = m₂ := by
    intro m₁ m₂ p1 e1 p2 e2
    have b1 := hin m₁ p1 e1
    have b2 := hin m₂ p2 e2
    have h := hlip m₁ b1 m₂ b2
    rw [← e1, ← e2] at h
    have hc : 3 * γ / k ^ 3 ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [pow_pos hk 5, pow_le_pow_of_le_one hk.le hk1 (show 3 ≤ 5 by norm_num)]
    have : ‖m₁ - m₂‖ ≤ 1 / 2 * ‖m₁ - m₂‖ :=
      h.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
    have : ‖m₁ - m₂‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (m₁ - m₂)]) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  refine ⟨⟨mI, hmIpos, hmIeq.symm⟩, hin, huniq, fun L hL => ?_⟩
  have hL3 : 3 ≤ L := by
    have : (3 : ℝ) ≤ L := by
      have : γ * L ≤ L := by
        have : (0 : ℝ) ≤ L := by positivity
        nlinarith
      linarith
    exact_mod_cast this
  have htail := hR (γ * L) hL
  obtain ⟨hclose, hflip⟩ := lg_finite_map hk hk1 hγ hγ0 hE hL3 htail
  have hexp : Real.exp (-(k / 1024 * (γ * L))) ≤ k ^ 2 / 256 := by
    have := Real.exp_pos (-(k / 1024 * (γ * L)))
    have : 0 ≤ γ * L := by positivity
    nlinarith
  -- the finite solution
  have hfin : ∃ μ ∈ Metric.closedBall (lgC0 γ E) (k / 32),
      freeTL 1 L ((E : ℂ) + γ * μ) = μ := by
    refine lg_fixed (fun μ => freeTL 1 L ((E : ℂ) + γ * μ)) _ _ (fun μ hμ => ?_) hflip hkpos
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h1 := (hclose μ hμ).2
    have h2 := hmap μ hμ
    rw [dist_eq_norm] at h2
    have := norm_sub_le_norm_sub_add_norm_sub (freeTL 1 L ((E : ℂ) + γ * μ)) (freeT 1 ((E : ℂ) + γ
        * μ))
      (lgC0 γ E)
    have h3 : 4 / k * Real.exp (-(k / 1024 * (γ * L))) ≤ k / 64 := by
      calc 4 / k * Real.exp (-(k / 1024 * (γ * L))) ≤ 4 / k * (k ^ 2 / 256) := by gcongr
        _ = k / 64 := by field_simp; ring
    linarith
  obtain ⟨m₀, hm₀, hm₀eq⟩ := hfin
  have hm₀pos : 0 < m₀.im := by
    have := (lg_ball_facts hk hk1 hγ hγ0 hE hm₀).1; linarith
  have hroot : IsDysonRootV 1 γ L E m₀ := ⟨hm₀pos, by unfold dysonRHSV; exact hm₀eq.symm⟩
  refine ⟨htail, ⟨m₀, hroot⟩, fun m hm => ?_⟩
  have hmm : m = m₀ := isDysonRootV_unique 1 γ (by norm_num) hγ L hL3 E (by simp) m m₀ hm hroot
  subst hmm
  refine ⟨hm₀, fun mInf hpos heq => ?_⟩
  have hb := hin mInf hpos heq
  have e : m - mInf = (freeTL 1 L ((E : ℂ) + γ * m) - freeT 1 ((E : ℂ) + γ * m)) +
      (freeT 1 ((E : ℂ) + γ * m) - freeT 1 ((E : ℂ) + γ * mInf)) := by
    rw [hm₀eq, ← heq]; ring
  have h1 := (hclose m hm₀).2
  have h2 := hlip m hm₀ mInf hb
  have hc : 3 * γ / k ^ 3 ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [pow_pos hk 5, pow_le_pow_of_le_one hk.le hk1 (show 3 ≤ 5 by norm_num)]
  have h3 : ‖m - mInf‖ ≤ 4 / k * Real.exp (-(k / 1024 * (γ * L))) + 1 / 2 * ‖m - mInf‖ := by
    conv_lhs => rw [e]
    refine (norm_add_le _ _).trans ?_
    gcongr
    exact h2.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
  have : 8 / k * Real.exp (-(k / 1024 * (γ * L))) =
      2 * (4 / k * Real.exp (-(k / 1024 * (γ * L)))) := by ring
  rw [this]
  linarith

/-! ### Geometric sums over the cycle -/

private lemma lg_sum_geom_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (L : ℕ) :
    ∑ k ∈ Finset.range L, q ^ k ≤ 1 / (1 - q) := by
  have h1 : (1 : ℝ) - q ≠ 0 := by linarith
  have h2 : q - 1 ≠ 0 := by linarith
  rw [geom_sum_eq hq1.ne]
  rw [show (q ^ L - 1) / (q - 1) = (1 - q ^ L) / (1 - q) by field_simp; ring]
  apply div_le_div_of_nonneg_right _ (by linarith)
  have := pow_nonneg hq0 L
  linarith

private lemma lg_sum_geom_rev_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (L : ℕ) :
    ∑ k ∈ Finset.range L, q ^ (L - k) ≤ 1 / (1 - q) := by
  have e : ∑ k ∈ Finset.range L, q ^ (L - k) = q * ∑ k ∈ Finset.range L, q ^ k := by
    rw [Finset.mul_sum, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [← pow_succ']; congr 1; omega
  rw [e]
  have := lg_sum_geom_le hq0 hq1 L
  have h0 : 0 ≤ ∑ k ∈ Finset.range L, q ^ k := Finset.sum_nonneg fun k _ => pow_nonneg hq0 k
  have : q * ∑ k ∈ Finset.range L, q ^ k ≤ ∑ k ∈ Finset.range L, q ^ k := by nlinarith
  linarith

private lemma lg_sum_ngeom_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) (L : ℕ) :
    ∑ k ∈ Finset.range L, (k : ℝ) * p ^ k ≤ 1 / (1 - p) ^ 2 := by
  have hp : ‖p‖ < 1 := by rw [Real.norm_of_nonneg hp0]; exact hp1
  have hs := hasSum_coe_mul_geometric_of_norm_lt_one hp
  have hle : ∑ k ∈ Finset.range L, (k : ℝ) * p ^ k ≤ p / (1 - p) ^ 2 :=
    sum_le_hasSum (Finset.range L) (fun i _ => by positivity) hs
  refine hle.trans ?_
  apply div_le_div_of_nonneg_right (by linarith) (by positivity)

private lemma lg_sum_ngeom_rev_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) (L : ℕ) :
    ∑ k ∈ Finset.range L, ((L - k : ℕ) : ℝ) * p ^ (L - k) ≤ 1 / (1 - p) ^ 2 := by
  have hp : ‖p‖ < 1 := by rw [Real.norm_of_nonneg hp0]; exact hp1
  have hs := hasSum_coe_mul_geometric_of_norm_lt_one hp
  have e : ∑ k ∈ Finset.range L, ((L - k : ℕ) : ℝ) * p ^ (L - k) =
      ∑ k ∈ Finset.range L, ((k + 1 : ℕ) : ℝ) * p ^ (k + 1) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    have : L - (L - 1 - k) = k + 1 := by omega
    rw [this]
  rw [e]
  have h2 : ∑ k ∈ Finset.range L, ((k + 1 : ℕ) : ℝ) * p ^ (k + 1) ≤
      ∑ k ∈ Finset.range (L + 1), (k : ℝ) * p ^ k := by
    rw [Finset.sum_range_succ']
    simp
  refine h2.trans ((sum_le_hasSum (Finset.range (L + 1)) (fun i _ => by positivity) hs).trans ?_)
  apply div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- `1 - e^{-b} ≥ b/2` for `0 ≤ b ≤ 1`. -/
private lemma lg_one_sub_exp_neg (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : b / 2 ≤ 1 - Real.exp (-b) :=
    by
  have h1 := Real.add_one_le_exp b
  have h2 : Real.exp (-b) * Real.exp b = 1 := by rw [← Real.exp_add]; simp
  have h3 := Real.exp_pos (-b)
  nlinarith

/-- Weighted row sums over `Fin L` of profiles in `c - a` and `a - c`. -/
private lemma lg_row_weight_le {L : ℕ} (a : Fin L) (μ : ℝ) (hμ : 0 ≤ μ) (φ ψ : ℕ → ℝ)
    (hφ : ∀ k, 0 ≤ φ k) (hψ : ∀ k, 0 ≤ ψ k) :
    ∑ c, Real.exp (μ * cycDist a c) * (φ (lgD L a c) + ψ (L - lgD L a c)) ≤
      ∑ k ∈ Finset.range L, Real.exp (μ * k) * φ k +
        ∑ k ∈ Finset.range L, Real.exp (μ * (L - k : ℕ)) * ψ (L - k) := by
  have h : ∀ c, Real.exp (μ * cycDist a c) * (φ (lgD L a c) + ψ (L - lgD L a c)) ≤
      Real.exp (μ * lgD L a c) * φ (lgD L a c) +
        Real.exp (μ * (L - lgD L a c : ℕ)) * ψ (L - lgD L a c) := by
    intro c
    rw [mul_add]
    gcongr
    · exact hφ _
    · exact_mod_cast cycDist_le_lgD a c
    · exact hψ _
    · exact_mod_cast cycDist_le_sub_lgD a c
  refine (Finset.sum_le_sum fun c _ => h c).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib]
  rw [sum_lgD_row a (fun k => Real.exp (μ * k) * φ k),
    sum_lgD_row a (fun k => Real.exp (μ * (L - k : ℕ)) * ψ (L - k))]

private lemma lg_exp_mul_pow (μ q : ℝ) (n : ℕ) : Real.exp (μ * n) * q ^ n = (Real.exp μ * q) ^ n :=
    by
  rw [mul_pow, ← Real.exp_nat_mul, mul_comm (n : ℝ) μ]

/-- `Σ_c e^{μ d(a,c)} (q^{c-a} + q^{a-c}) ≤ 2/(1 - e^μ q)`. -/
private lemma lg_row_geom {L : ℕ} (a : Fin L) (μ q : ℝ) (hμ : 0 ≤ μ) (hq : 0 ≤ q)
    (hq1 : Real.exp μ * q < 1) :
    ∑ c, Real.exp (μ * cycDist a c) * (q ^ lgD L a c + q ^ (L - lgD L a c)) ≤
      2 / (1 - Real.exp μ * q) := by
  refine (lg_row_weight_le a μ hμ (fun k => q ^ k) (fun k => q ^ k) (fun k => pow_nonneg hq k)
    (fun k => pow_nonneg hq k)).trans ?_
  simp_rw [lg_exp_mul_pow]
  have h0 : 0 ≤ Real.exp μ * q := by positivity
  have := lg_sum_geom_le h0 hq1 L
  have := lg_sum_geom_rev_le h0 hq1 L
  have e : 2 / (1 - Real.exp μ * q) = 1 / (1 - Real.exp μ * q) + 1 / (1 - Real.exp μ * q) := by
    ring
  linarith

/-- `Σ_c e^{μ d(a,c)} ((c-a) q^{c-a} + (a-c) q^{a-c}) ≤ 2/(1 - e^μ q)²`. -/
private lemma lg_row_ngeom {L : ℕ} (a : Fin L) (μ q : ℝ) (hμ : 0 ≤ μ) (hq : 0 ≤ q)
    (hq1 : Real.exp μ * q < 1) :
    ∑ c, Real.exp (μ * cycDist a c) * ((lgD L a c : ℝ) * q ^ lgD L a c +
      ((L - lgD L a c : ℕ) : ℝ) * q ^ (L - lgD L a c)) ≤ 2 / (1 - Real.exp μ * q) ^ 2 := by
  refine (lg_row_weight_le a μ hμ (fun k => (k : ℝ) * q ^ k) (fun k => (k : ℝ) * q ^ k)
    (fun k => by positivity) (fun k => by positivity)).trans ?_
  have e1 : ∀ k : ℕ, Real.exp (μ * k) * ((k : ℝ) * q ^ k) = (k : ℝ) * (Real.exp μ * q) ^ k := by
    intro k; rw [← lg_exp_mul_pow]; ring
  simp only [e1]
  have h0 : 0 ≤ Real.exp μ * q := by positivity
  have := lg_sum_ngeom_le h0 hq1 L
  have := lg_sum_ngeom_rev_le h0 hq1 L
  have e : 2 / (1 - Real.exp μ * q) ^ 2 =
      1 / (1 - Real.exp μ * q) ^ 2 + 1 / (1 - Real.exp μ * q) ^ 2 := by ring
  linarith

private lemma lg_cycDist_cases {L : ℕ} (a c : Fin L) :
    cycDist a c = lgD L a c ∨ cycDist a c = L - lgD L a c := by
  rw [cycDist_eq_min, lgD_swap a c]
  split_ifs with h
  · left; rw [h]; simp
  · rcases le_total (lgD L a c) (L - lgD L a c) with h1 | h1
    · left; exact min_eq_left h1
    · right; exact min_eq_right h1

/-- `Σ_c e^{-ν d(a,c)} ≤ 2/(1 - e^{-ν})`. -/
private lemma lg_row_exp_neg {L : ℕ} (a : Fin L) (ν : ℝ) (hν : 0 < ν) :
    ∑ c, Real.exp (-(ν * cycDist a c)) ≤ 2 / (1 - Real.exp (-ν)) := by
  have hq : Real.exp (-ν) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have h : ∀ c, Real.exp (-(ν * cycDist a c)) ≤
      Real.exp (0 * cycDist a c) * (Real.exp (-ν) ^ lgD L a c + Real.exp (-ν) ^ (L - lgD L a c)) :=
          by
    intro c
    rw [zero_mul, Real.exp_zero, one_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    have h1 := Real.exp_pos ((lgD L a c : ℕ) * -ν)
    have h2 := Real.exp_pos (((L - lgD L a c : ℕ) : ℕ) * -ν)
    rcases lg_cycDist_cases a c with e | e
    · rw [e]; have : -(ν * (lgD L a c : ℕ)) = (lgD L a c : ℕ) * -ν := by ring
      rw [this]; linarith
    · rw [e]; have : -(ν * ((L - lgD L a c : ℕ) : ℝ)) = ((L - lgD L a c : ℕ) : ℝ) * -ν := by ring
      rw [this]; linarith
  refine (Finset.sum_le_sum fun c _ => h c).trans ?_
  have := lg_row_geom a 0 (Real.exp (-ν)) le_rfl (Real.exp_pos _).le (by simpa using hq)
  simpa using this

/-- `1 + 2/ν` bounds the row of `e^{-ν d}` for `0 < ν ≤ 1`. -/
private lemma lg_row_exp_neg' {L : ℕ} (a : Fin L) (ν : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1) :
    ∑ c, Real.exp (-(ν * cycDist a c)) ≤ 4 / ν := by
  refine (lg_row_exp_neg a ν hν).trans ?_
  have := lg_one_sub_exp_neg ν hν.le hν1
  rw [div_le_div_iff₀ (by linarith) hν]
  nlinarith

/-- `e^{c d(a,c)/a}` weights are submultiplicative along the cycle. -/
private lemma lg_exp_dist_le {L : ℕ} (μ : ℝ) (hμ : 0 ≤ μ) (a b c : Fin L) :
    Real.exp (μ * cycDist a c) ≤ Real.exp (μ * cycDist a b) * Real.exp (μ * cycDist b c) := by
  rw [← Real.exp_add, Real.exp_le_exp, ← mul_add]
  gcongr
  exact_mod_cast cycDist_triangle a b c

/-! ### Periodization of geometric profiles -/

private lemma lg_perLine_geom (σ c : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) {L : ℕ} (x : Fin L) :
    perLine (fun n : ℤ => c * σ ^ n.natAbs) L x = c * geomV σ L x.val := by
  unfold perLine geomV
  have hx := x.isLt
  have hσL0 : 0 ≤ σ ^ L := pow_nonneg hσ0 L
  have hσL1 : σ ^ L < 1 := pow_lt_one₀ hσ0 hσ1 (by omega)
  have h1 : HasSum (fun n : ℕ => c * σ ^ (((x.val : ℤ) + (n : ℤ) * L).natAbs))
      (c * σ ^ x.val * (1 - σ ^ L)⁻¹) := by
    have hg := (hasSum_geometric_of_lt_one hσL0 hσL1).mul_left (c * σ ^ x.val)
    refine hg.congr_fun fun n => ?_
    have : (((x.val : ℤ) + (n : ℤ) * L).natAbs) = x.val + L * n := by
      have : ((x.val : ℤ) + (n : ℤ) * L) = ((x.val + L * n : ℕ) : ℤ) := by push_cast; ring
      rw [this, Int.natAbs_natCast]
    rw [this, pow_add, pow_mul]; ring
  have h2 : HasSum (fun n : ℕ => c * σ ^ (((x.val : ℤ) + (-((n : ℤ) + 1)) * L).natAbs))
      (c * σ ^ (L - x.val) * (1 - σ ^ L)⁻¹) := by
    have hg := (hasSum_geometric_of_lt_one hσL0 hσL1).mul_left (c * σ ^ (L - x.val))
    refine hg.congr_fun fun n => ?_
    have : (((x.val : ℤ) + (-((n : ℤ) + 1)) * L).natAbs) = (L - x.val) + L * n := by
      have : ((x.val : ℤ) + (-((n : ℤ) + 1)) * L) = -(((L - x.val) + L * n : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub hx.le]; ring
      rw [this, Int.natAbs_neg, Int.natAbs_natCast]
    rw [this, pow_add, pow_mul]; ring
  have h := HasSum.of_nat_of_neg_add_one (f := fun n : ℤ => c * σ ^ (((x.val : ℤ) + n * L).natAbs))
    h1 h2
  rw [h.tsum_eq]
  have : (1 : ℝ) - σ ^ L ≠ 0 := by linarith
  field_simp

/-! ### The large-coupling setting -/

/-- The data of the large-coupling comparison: parameters, the finite solution `m`, the line
solution `mInf`, both in the disk around `f(E + iγ)`, and their exponential closeness. -/
private structure LgGood (k γ E : ℝ) (L : ℕ) (m mInf : ℂ) : Prop where
  hk : 0 < k
  hk1 : k ≤ 1
  hγ : 0 < γ
  hγ0 : γ ≤ k ^ 5 / 1000
  hE : |E| ≤ 2 - 2 * k
  hL : 3 ≤ L
  htail : (1 + γ * L) * Real.exp (-(k / 1024 * (γ * L))) ≤ k ^ 2 / 256
  hm : m ∈ Metric.closedBall (lgC0 γ E) (k / 32)
  hmI : mInf ∈ Metric.closedBall (lgC0 γ E) (k / 32)
  hroot : IsDysonRootV 1 γ L E m
  hpos : 0 < mInf.im
  heq : mInf = freeT 1 ((E : ℂ) + γ * mInf)
  hclose : ‖m - mInf‖ ≤ 8 / k * Real.exp (-(k / 1024 * (γ * L)))

namespace LgGood

variable {k γ E : ℝ} {L : ℕ} {m mInf : ℂ} (h : LgGood k γ E L m mInf)
include h

private lemma γ1 : γ ≤ 1 := by
  have := h.hk; have := h.hk1; have := h.hγ0
  have : k ^ 5 ≤ 1 := pow_le_one₀ h.hk.le h.hk1
  linarith

private lemma b_le : γ * k / 1024 ≤ 1 := by
  have := h.γ1; have := h.hk1; have := h.hγ; have := h.hk
  have : γ * k ≤ 1 := by nlinarith
  linarith

private lemma b_pos : 0 < γ * k / 1024 := by have := h.hγ; have := h.hk; positivity

private lemma exp_aH : Real.exp (-(k / 1024 * (γ * L))) ≤ k ^ 2 / 256 := by
  have := h.htail
  have := Real.exp_pos (-(k / 1024 * (γ * L)))
  have : 0 ≤ γ * L := by have := h.hγ; positivity
  nlinarith

private lemma exp_aH_half : Real.exp (-(k / 1024 * (γ * L))) ≤ 1 / 4 := by
  have := h.exp_aH; have := h.hk1; have := h.hk
  have : k ^ 2 ≤ 1 := by nlinarith
  linarith

/-- Facts about `w = E + γμ` for `μ` in the disk. -/
private lemma wf {μ : ℂ} (hμ : μ ∈ Metric.closedBall (lgC0 γ E) (k / 32)) :
    k / 32 ≤ μ.im ∧ ‖μ‖ ≤ 2 / k ∧ 0 < ((E : ℂ) + γ * μ).im ∧
      γ * (k / 32) ≤ ((E : ℂ) + γ * μ).im ∧ ((E : ℂ) + γ * μ).im ≤ 2 * γ / k ∧
      ((E : ℂ) + γ * μ).im ≤ k / 2 ∧ |((E : ℂ) + γ * μ).re| ≤ 2 - k ∧
      ‖(E : ℂ) + γ * μ‖ ≤ 3 :=
  lg_ball_facts h.hk h.hk1 h.hγ h.hγ0 h.hE hμ

private lemma rho_le {μ : ℂ} (hμ : μ ∈ Metric.closedBall (lgC0 γ E) (k / 32)) :
    ‖freeRho 1 ((E : ℂ) + γ * μ)‖ ≤ Real.exp (-(γ * k / 1024)) := by
  obtain ⟨-, -, hp, hlo, -, -, -, hw3⟩ := h.wf hμ
  refine (lg_norm_rho_le_exp hp hw3).trans (Real.exp_le_exp.mpr ?_)
  linarith

private lemma rho_ge {μ : ℂ} (hμ : μ ∈ Metric.closedBall (lgC0 γ E) (k / 32)) :
    1 / 4 ≤ ‖freeRho 1 ((E : ℂ) + γ * μ)‖ := by
  obtain ⟨-, -, hp, -, -, -, -, hw3⟩ := h.wf hμ
  exact lg_norm_rho_ge hp hw3

private lemma rho_pow_le {μ : ℂ} (hμ : μ ∈ Metric.closedBall (lgC0 γ E) (k / 32)) :
    ‖freeRho 1 ((E : ℂ) + γ * μ)‖ ^ L ≤ Real.exp (-(k / 1024 * (γ * L))) := by
  calc ‖freeRho 1 ((E : ℂ) + γ * μ)‖ ^ L ≤ Real.exp (-(γ * k / 1024)) ^ L := by
        gcongr; exact h.rho_le hμ
    _ = Real.exp (-(k / 1024 * (γ * L))) := by rw [← Real.exp_nat_mul]; congr 1; ring

private lemma rho_lt {μ : ℂ} (hμ : μ ∈ Metric.closedBall (lgC0 γ E) (k / 32)) :
    ‖freeRho 1 ((E : ℂ) + γ * μ)‖ < 1 := lg_rho_lt (h.wf hμ).2.2.1

private lemma f_le {μ : ℂ} (hμ : μ ∈ Metric.closedBall (lgC0 γ E) (k / 32)) :
    ‖freeT 1 ((E : ℂ) + γ * μ)‖ ≤ 1 / k := by
  obtain ⟨-, -, hp, -, -, -, hr, -⟩ := h.wf hμ
  exact lg_norm_f_le h.hk h.hk1 hp hr

private lemma gap_ge {μ : ℂ} (hμ : μ ∈ Metric.closedBall (lgC0 γ E) (k / 32)) :
    γ * k / 512 ≤ 1 - ‖freeRho 1 ((E : ℂ) + γ * μ)‖ ^ 2 := by
  obtain ⟨-, -, hp, hlo, -, -, -, hw3⟩ := h.wf hμ
  have := lg_gap_ge hp hw3
  linarith

private lemma gap_le {μ : ℂ} (hμ : μ ∈ Metric.closedBall (lgC0 γ E) (k / 32)) :
    1 - ‖freeRho 1 ((E : ℂ) + γ * μ)‖ ^ 2 ≤ 8 * γ / k ^ 2 := by
  obtain ⟨-, -, hp, -, hhi, hk2, hr, -⟩ := h.wf hμ
  refine (lg_gap_le h.hk h.hk1 hp hr hk2).trans ?_
  rw [div_le_div_iff₀ h.hk (by have := h.hk; positivity)]
  have := h.hk
  have : 4 * ((E : ℂ) + γ * μ).im * k ≤ 4 * (2 * γ / k) * k := by gcongr
  have e : 4 * (2 * γ / k) * k = 8 * γ := by field_simp; ring
  nlinarith

/-- The finite solution equals the closed form `f (1 + ρ^L)/(1 - ρ^L)`. -/
private lemma m_eq : m = freeT 1 ((E : ℂ) + γ * m) *
    ((1 + freeRho 1 ((E : ℂ) + γ * m) ^ L) / (1 - freeRho 1 ((E : ℂ) + γ * m) ^ L)) := by
  have := h.hroot.2
  unfold dysonRHSV at this
  rw [← lg_freeTL_eq (h.wf h.hm).2.2.1 h.hL]
  exact this

private lemma dysonMat_eq : dysonMat 1 γ L E m =
    freeT 1 ((E : ℂ) + γ * m) • geomC (freeRho 1 ((E : ℂ) + γ * m)) L :=
  lg_dysonMat_eq γ h.hL E m (h.wf h.hm).2.2.1

private lemma f_sub : ‖freeT 1 ((E : ℂ) + γ * m) - freeT 1 ((E : ℂ) + γ * mInf)‖ ≤
    24 / k ^ 4 * γ * Real.exp (-(k / 1024 * (γ * L))) := by
  obtain ⟨-, -, hp1, -, -, -, hr1, n1⟩ := h.wf h.hm
  obtain ⟨-, -, hp2, -, -, -, hr2, n2⟩ := h.wf h.hmI
  refine (lg_f_lip h.hk h.hk1 hp1 hp2 hr1 hr2 n1 n2).trans ?_
  have e : (E : ℂ) + γ * m - ((E : ℂ) + γ * mInf) = γ * (m - mInf) := by ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg h.hγ.le]
  have := h.hclose
  have hk := h.hk
  have hγ := h.hγ
  calc 3 / k ^ 3 * (γ * ‖m - mInf‖) ≤ 3 / k ^ 3 * (γ * (8 / k * Real.exp (-(k / 1024 * (γ * L)))))
      := by
        gcongr
    _ = 24 / k ^ 4 * γ * Real.exp (-(k / 1024 * (γ * L))) := by field_simp; ring

private lemma rho_sub : ‖freeRho 1 ((E : ℂ) + γ * m) - freeRho 1 ((E : ℂ) + γ * mInf)‖ ≤
    16 / k ^ 2 * γ * Real.exp (-(k / 1024 * (γ * L))) := by
  obtain ⟨-, -, hp1, -, -, -, hr1, n1⟩ := h.wf h.hm
  obtain ⟨-, -, hp2, -, -, -, hr2, n2⟩ := h.wf h.hmI
  refine (lg_rho_lip h.hk h.hk1 hp1 hp2 hr1 hr2 n1 n2).trans ?_
  have e : (E : ℂ) + γ * m - ((E : ℂ) + γ * mInf) = γ * (m - mInf) := by ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg h.hγ.le]
  have := h.hclose
  have hk := h.hk
  have hγ := h.hγ
  calc 2 / k * (γ * ‖m - mInf‖) ≤ 2 / k * (γ * (8 / k * Real.exp (-(k / 1024 * (γ * L))))) := by
        gcongr
    _ = 16 / k ^ 2 * γ * Real.exp (-(k / 1024 * (γ * L))) := by field_simp; ring

end LgGood

/-! ### The free row at large coupling: (A.15) [da:eq:uniform-free-row] -/

private lemma lg_geomV_norm_le (ρ : ℂ) {L : ℕ} (hL : ‖ρ‖ ^ L ≤ 1 / 2) (x : ℕ) : ‖geomV ρ L x‖ ≤ 2 *
    (‖ρ‖ ^ x + ‖ρ‖ ^ (L - x)) := by
  unfold geomV
  have h1 : 1 / 2 ≤ ‖1 - ρ ^ L‖ := by
    have := norm_sub_norm_le (1 : ℂ) (ρ ^ L); rw [norm_pow] at this; simp at this; linarith
  rw [norm_div, div_le_iff₀ (by linarith)]
  have := norm_add_le (ρ ^ x) (ρ ^ (L - x))
  rw [norm_pow, norm_pow] at this
  have h0 : 0 ≤ ‖ρ‖ ^ x + ‖ρ‖ ^ (L - x) := by positivity
  nlinarith

namespace LgGood

variable {k γ E : ℝ} {L : ℕ} {m mInf : ℂ} (h : LgGood k γ E L m mInf)
include h

/-- Pointwise profile of the free row: `|M_ac| ≤ (2/k)(q^{c-a} + q^{a-c})`, `q = e^{-γk/1024}`. -/
private lemma M_le (a c : Fin L) :
    ‖dysonMat 1 γ L E m a c‖ ≤ 2 / k * (Real.exp (-(γ * k / 1024)) ^ lgD L a c +
      Real.exp (-(γ * k / 1024)) ^ (L - lgD L a c)) := by
  rw [h.dysonMat_eq]
  simp only [Matrix.smul_apply, geomC, Matrix.of_apply, smul_eq_mul, norm_mul]
  have hf := h.f_le h.hm
  have hρ := h.rho_le h.hm
  have hL := h.rho_pow_le h.hm
  have hg := lg_geomV_norm_le _ (hL.trans h.exp_aH_half |>.trans (by norm_num)) (lgD L a c)
  have hk := h.hk
  calc ‖freeT 1 ((E : ℂ) + γ * m)‖ * ‖geomV (freeRho 1 ((E : ℂ) + γ * m)) L (lgD L a c)‖
      ≤ 1 / k * (2 * (‖freeRho 1 ((E : ℂ) + γ * m)‖ ^ lgD L a c +
          ‖freeRho 1 ((E : ℂ) + γ * m)‖ ^ (L - lgD L a c))) := by gcongr
    _ ≤ 1 / k * (2 * (Real.exp (-(γ * k / 1024)) ^ lgD L a c +
          Real.exp (-(γ * k / 1024)) ^ (L - lgD L a c))) := by gcongr
    _ = _ := by ring

/-- (A.15) [da:eq:uniform-free-row], pointwise: `|M_ac| ≤ (4/k) e^{-(k/1024) γ d(a,c)}`. -/
private lemma M_le_exp (a c : Fin L) :
    ‖dysonMat 1 γ L E m a c‖ ≤ 4 / k * Real.exp (-(k / 1024 * γ * cycDist a c)) := by
  refine (h.M_le a c).trans ?_
  have hq0 : 0 ≤ Real.exp (-(γ * k / 1024)) := (Real.exp_pos _).le
  have hq1 : Real.exp (-(γ * k / 1024)) ≤ 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by have := h.b_pos; linarith)
  have e : Real.exp (-(k / 1024 * γ * cycDist a c)) = Real.exp (-(γ * k / 1024)) ^ cycDist a c := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [e]
  have h1 : Real.exp (-(γ * k / 1024)) ^ lgD L a c ≤ Real.exp (-(γ * k / 1024)) ^ cycDist a c :=
    pow_le_pow_of_le_one hq0 hq1 (cycDist_le_lgD a c)
  have h2 : Real.exp (-(γ * k / 1024)) ^ (L - lgD L a c) ≤
      Real.exp (-(γ * k / 1024)) ^ cycDist a c :=
    pow_le_pow_of_le_one hq0 hq1 (cycDist_le_sub_lgD a c)
  have hk := h.hk
  calc 2 / k * (Real.exp (-(γ * k / 1024)) ^ lgD L a c + Real.exp (-(γ * k / 1024)) ^ (L - lgD L a
      c))
      ≤ 2 / k * (Real.exp (-(γ * k / 1024)) ^ cycDist a c +
          Real.exp (-(γ * k / 1024)) ^ cycDist a c) := by gcongr
    _ = _ := by ring

/-- (A.15) [da:eq:uniform-free-row], weighted row: `Σ_c e^{μ d} |M_ac| ≤ 16384/(k² γ)` for
`μ ≤ γk/2048`. -/
private lemma M_row (a : Fin L) (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ : μ ≤ γ * k / 2048) :
    ∑ c, Real.exp (μ * cycDist a c) * ‖dysonMat 1 γ L E m a c‖ ≤ 16384 / (k ^ 2 * γ) := by
  have hb := h.b_pos
  have hb1 := h.b_le
  set q := Real.exp (-(γ * k / 1024)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hμq : Real.exp μ * q ≤ Real.exp (-(γ * k / 2048)) := by
    rw [hq, ← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have hlt : Real.exp (-(γ * k / 2048)) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hk := h.hk
  have hγ := h.hγ
  have hgap : γ * k / 4096 ≤ 1 - Real.exp (-(γ * k / 2048)) := by
    have := lg_one_sub_exp_neg (γ * k / 2048) (by positivity) (by linarith)
    linarith
  have hrow := lg_row_geom a μ q hμ0 hq0 (hμq.trans_lt hlt)
  calc ∑ c, Real.exp (μ * cycDist a c) * ‖dysonMat 1 γ L E m a c‖
      ≤ ∑ c, Real.exp (μ * cycDist a c) * (2 / k * (q ^ lgD L a c + q ^ (L - lgD L a c))) := by
        gcongr with c; exact h.M_le a c
    _ = 2 / k * ∑ c, Real.exp (μ * cycDist a c) * (q ^ lgD L a c + q ^ (L - lgD L a c)) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun c _ => by ring
    _ ≤ 2 / k * (2 / (1 - Real.exp μ * q)) := by gcongr
    _ ≤ 2 / k * (2 / (γ * k / 4096)) := by
        gcongr
        linarith
    _ = 16384 / (k ^ 2 * γ) := by field_simp; ring

end LgGood

/-! ### The periodized line kernel `P₀` -/

private lemma lg_perP0_eq {g γ E : ℝ} (hb : hopB g = 1) (hγg : gammaG g = γ) {L : ℕ} (mInf : ℂ)
    (x : Fin L) (hσ : ‖freeRho 1 ((E : ℂ) + γ * mInf)‖ < 1) :
    perP0 g L E mInf x = γ * ‖freeT 1 ((E : ℂ) + γ * mInf)‖ ^ 2 *
      geomV (‖freeRho 1 ((E : ℂ) + γ * mInf)‖ ^ 2) L x.val := by
  unfold perP0
  rw [hb, hγg]
  have e : (fun n : ℤ => γ * ‖freeT ((1 : ℝ)) ((E : ℂ) + (γ : ℂ) * mInf) *
      freeRho 1 ((E : ℂ) + (γ : ℂ) * mInf) ^ n.natAbs‖ ^ 2) =
      fun n : ℤ => (γ * ‖freeT 1 ((E : ℂ) + γ * mInf)‖ ^ 2) *
        (‖freeRho 1 ((E : ℂ) + γ * mInf)‖ ^ 2) ^ n.natAbs := by
    funext n; rw [norm_mul, norm_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 n.natAbs]; ring
  rw [e, lg_perLine_geom _ _ (by positivity) (by nlinarith [norm_nonneg (freeRho 1 ((E : ℂ) + γ *
      mInf))])]

namespace LgGood

variable {k γ E : ℝ} {L : ℕ} {m mInf : ℂ} (h : LgGood k γ E L m mInf)
include h

/-- The line Ward identity `γ |f_∞|² (1 + |ρ_∞|²) = 1 - |ρ_∞|²`. -/
private lemma ward_inf : γ * ‖freeT 1 ((E : ℂ) + γ * mInf)‖ ^ 2 *
    (1 + ‖freeRho 1 ((E : ℂ) + γ * mInf)‖ ^ 2) = 1 - ‖freeRho 1 ((E : ℂ) + γ * mInf)‖ ^ 2 := by
  have hp := (h.wf h.hmI).2.2.1
  have hw := lg_ward hp
  rw [← h.heq] at hw
  have him : ((E : ℂ) + γ * mInf).im = γ * mInf.im := by simp
  rw [him] at hw
  have hpos := h.hpos
  have e : mInf.im * (1 - ‖freeRho 1 ((E : ℂ) + γ * mInf)‖ ^ 2) =
      mInf.im * (γ * ‖mInf‖ ^ 2 * (1 + ‖freeRho 1 ((E : ℂ) + γ * mInf)‖ ^ 2)) := by
    rw [hw]; ring
  have e2 := (mul_left_cancel₀ hpos.ne' e).symm
  rw [← h.heq]
  exact e2

private lemma perP0_nonneg {g : ℝ} (hb : hopB g = 1) (hγg : gammaG g = γ) (x : Fin L) :
    0 ≤ perP0 g L E mInf x := by
  rw [lg_perP0_eq hb hγg mInf x (h.rho_lt h.hmI)]
  have := h.hγ
  have hs : ‖freeRho 1 ((E : ℂ) + γ * mInf)‖ ^ 2 < 1 := by
    have := h.rho_lt h.hmI; nlinarith [norm_nonneg (freeRho 1 ((E : ℂ) + γ * mInf))]
  unfold geomV
  have : 0 < 1 - (‖freeRho 1 ((E : ℂ) + γ * mInf)‖ ^ 2) ^ L := by
    have := pow_lt_one₀ (by positivity) hs (show L ≠ 0 by have := h.hL; omega); linarith
  positivity

private lemma perP0_sum {g : ℝ} (hb : hopB g = 1) (hγg : gammaG g = γ) :
    ∑ x, perP0 g L E mInf x = 1 := by
  simp_rw [lg_perP0_eq hb hγg mInf _ (h.rho_lt h.hmI)]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun x => geomV _ L x) L]
  have hs : ‖freeRho 1 ((E : ℂ) + γ * mInf)‖ ^ 2 < 1 := by
    have := h.rho_lt h.hmI; nlinarith [norm_nonneg (freeRho 1 ((E : ℂ) + γ * mInf))]
  have hD : 1 - (‖freeRho 1 ((E : ℂ) + γ * mInf)‖ ^ 2) ^ L ≠ 0 := by
    have := pow_lt_one₀ (by positivity) hs (show L ≠ 0 by have := h.hL; omega); linarith
  rw [sum_geomV hs.ne hD]
  have hw := h.ward_inf
  have : 1 - ‖freeRho 1 ((E : ℂ) + γ * mInf)‖ ^ 2 ≠ 0 := by linarith
  field_simp
  linarith

private lemma perP0_even {g : ℝ} (hb : hopB g = 1) (hγg : gammaG g = γ) [NeZero L] (x : Fin L) :
    perP0 g L E mInf (-x) = perP0 g L E mInf x := by
  rw [lg_perP0_eq hb hγg mInf _ (h.rho_lt h.hmI), lg_perP0_eq hb hγg mInf _ (h.rho_lt h.hmI)]
  congr 1
  have hx := x.isLt
  rw [Fin.neg_def]
  simp only
  by_cases h0 : x.val = 0
  · rw [h0]; simp
  · rw [Nat.mod_eq_of_lt (by omega)]
    unfold geomV
    rw [add_comm, Nat.sub_sub_self hx.le]

end LgGood

/-! ### Comparison of `P` with `P₀`: (A.14) [uvp:eq:finiteerror] -/

private lemma lg_norm_pow_sub_le_real (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    |a ^ n - b ^ n| ≤ n * max a b ^ (n - 1) * |a - b| := by
  have h := lg_norm_pow_sub_le (a : ℂ) (b : ℂ) n
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ha, abs_of_nonneg hb] at h
  exact h

private lemma lg_n_pow_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (n : ℕ) : (n : ℝ) * p ^ n ≤ 1 / (1 -
    p) := by
  refine le_trans ?_ (lg_sum_geom_le hp0 hp1 n)
  have : (n : ℝ) * p ^ n = ∑ k ∈ Finset.range n, p ^ n := by simp
  rw [this]
  exact Finset.sum_le_sum fun k hk => pow_le_pow_of_le_one hp0 hp1.le (Finset.mem_range.mp hk).le

private lemma lg_pow_pred_le (s : ℝ) (hs : 1 / 16 ≤ s) (n : ℕ) : (n : ℝ) * s ^ (n - 1) ≤ 16 * (n *
    s ^ n) := by
  rcases n with _ | n
  · simp
  · simp only [Nat.add_sub_cancel, pow_succ]
    have h1 : 0 ≤ s ^ n := pow_nonneg (by linarith) n
    have h2 : (0 : ℝ) ≤ (n + 1 : ℕ) := by positivity
    have h3 : (1 : ℝ) ≤ 16 * s := by linarith
    have := mul_le_mul_of_nonneg_left h3 (mul_nonneg h2 h1)
    nlinarith

/-- `|‖G_ρ(x)‖² - G_{|ρ|²}(x)| ≤ |ρ|^L (16 (|ρ|^{2x} + |ρ|^{2(L-x)}) + 8)`. -/
private lemma lg_AB (ρ : ℂ) {L x : ℕ} (hx : x ≤ L) (hz : ‖ρ‖ ^ L ≤ 1 / 2) :
    |‖geomV ρ L x‖ ^ 2 - geomV (‖ρ‖ ^ 2) L x| ≤
      ‖ρ‖ ^ L * (16 * ((‖ρ‖ ^ 2) ^ x + (‖ρ‖ ^ 2) ^ (L - x)) + 8) := by
  set u := ρ ^ x
  set v := ρ ^ (L - x)
  set z := ρ ^ L with hzdef
  have huv : u * v = z := by rw [← pow_add]; congr 1; omega
  have hnz : ‖z‖ = ‖ρ‖ ^ L := norm_pow _ _
  have hnu : (‖ρ‖ ^ 2) ^ x = ‖u‖ ^ 2 := by rw [norm_pow, ← pow_mul, ← pow_mul, mul_comm]
  have hnv : (‖ρ‖ ^ 2) ^ (L - x) = ‖v‖ ^ 2 := by rw [norm_pow, ← pow_mul, ← pow_mul, mul_comm]
  have hnzz : (‖ρ‖ ^ 2) ^ L = ‖z‖ ^ 2 := by rw [hnz, ← pow_mul, ← pow_mul, mul_comm]
  rw [← hnz] at hz ⊢
  rw [hnu, hnv]
  unfold geomV
  rw [hnu, hnv, hnzz]
  -- real quantities
  have hz0 := norm_nonneg z
  set S := ‖u‖ ^ 2 + ‖v‖ ^ 2 with hS
  have hS0 : 0 ≤ S := by positivity
  have hsum : ‖u + v‖ ^ 2 = S + 2 * (u * (starRingEnd ℂ) v).re := by
    simp only [hS, Complex.sq_norm, Complex.normSq_add]
  have hre : |(u * (starRingEnd ℂ) v).re| ≤ ‖z‖ := by
    refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
    rw [norm_mul, Complex.norm_conj, ← norm_mul, huv]
  have hD1 : ‖1 - z‖ ^ 2 = 1 - 2 * z.re + ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub]; simp; ring
  have hrez : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hD1lo : 1 / 4 ≤ ‖1 - z‖ ^ 2 := by
    rw [hD1]; have := neg_abs_le z.re; nlinarith [abs_le.mp hrez]
  have hD2lo : 3 / 4 ≤ 1 - ‖z‖ ^ 2 := by nlinarith
  rw [norm_div, div_pow, hsum]
  rw [div_sub_div _ _ (by linarith) (by linarith), abs_div,
    abs_of_pos (by positivity : 0 < ‖1 - z‖ ^ 2 * (1 - ‖z‖ ^ 2)), div_le_iff₀ (by positivity)]
  set R := (u * (starRingEnd ℂ) v).re with hR
  set D2 := 1 - ‖z‖ ^ 2 with hD2
  have e : (S + 2 * R) * D2 - S * ‖1 - z‖ ^ 2 = S * (2 * z.re - 2 * ‖z‖ ^ 2) + 2 * R * D2 := by
    rw [hD1, hD2]; ring
  rw [← hzdef, mul_comm (‖1 - z‖ ^ 2) S, e]
  have h1 : |S * (2 * z.re - 2 * ‖z‖ ^ 2)| ≤ S * (3 * ‖z‖) := by
    rw [abs_mul, abs_of_nonneg hS0]
    gcongr
    have := abs_le.mp hrez
    rw [abs_le]; constructor <;> nlinarith
  have h2 : |2 * R * D2| ≤ 2 * ‖z‖ * D2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ D2)]
    simp only [abs_two]
    gcongr
  have h3 : 3 * S * ‖z‖ + 2 * ‖z‖ * D2 ≤ ‖z‖ * (16 * S + 8) * (‖1 - z‖ ^ 2 * D2) := by
    have hD2le : D2 ≤ 1 := by rw [hD2]; nlinarith
    have hA : 3 / 16 ≤ ‖1 - z‖ ^ 2 * D2 := by nlinarith
    have hB : D2 / 4 ≤ ‖1 - z‖ ^ 2 * D2 := by nlinarith
    nlinarith [mul_nonneg hz0 hS0]
  calc |S * (2 * z.re - 2 * ‖z‖ ^ 2) + 2 * R * D2|
      ≤ |S * (2 * z.re - 2 * ‖z‖ ^ 2)| + |2 * R * D2| := abs_add_le _ _
    _ ≤ S * (3 * ‖z‖) + 2 * ‖z‖ * D2 := add_le_add h1 h2
    _ ≤ _ := by linarith

private lemma lg_pow_sub_le_s (σ σ' s : ℝ) (h0 : 0 ≤ σ) (h0' : 0 ≤ σ') (hs : σ ≤ s) (hs' : σ' ≤ s)
    (hs16 : 1 / 16 ≤ s) (n : ℕ) : |σ ^ n - σ' ^ n| ≤ 16 * ((n : ℝ) * s ^ n) * |σ - σ'| := by
  refine (lg_norm_pow_sub_le_real σ σ' h0 h0' n).trans
    (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
  calc (n : ℝ) * max σ σ' ^ (n - 1) ≤ n * s ^ (n - 1) := by
        gcongr
        exact max_le hs hs'
    _ ≤ 16 * (n * s ^ n) := lg_pow_pred_le s hs16 n

/-- Lipschitz bound of the periodized geometric profile in its ratio. -/
private lemma lg_BB (σ σ' s : ℝ) {L x : ℕ} (h0 : 0 ≤ σ) (h0' : 0 ≤ σ') (hs : σ ≤ s)
    (hs' : σ' ≤ s) (hs16 : 1 / 16 ≤ s) (hsL : s ^ L ≤ 1 / 4) :
    |geomV σ L x - geomV σ' L x| ≤
      (22 * ((x : ℝ) * s ^ x + ((L - x : ℕ) : ℝ) * s ^ (L - x)) +
        29 * (s ^ x + s ^ (L - x)) * ((L : ℝ) * s ^ L)) * |σ - σ'| := by
  have hD : 3 / 4 ≤ 1 - σ ^ L := by
    have : σ ^ L ≤ s ^ L := pow_le_pow_left₀ h0 hs L
    linarith
  have hD' : 3 / 4 ≤ 1 - σ' ^ L := by
    have : σ' ^ L ≤ s ^ L := pow_le_pow_left₀ h0' hs' L
    linarith
  unfold geomV
  have e : (σ ^ x + σ ^ (L - x)) / (1 - σ ^ L) - (σ' ^ x + σ' ^ (L - x)) / (1 - σ' ^ L) =
      ((σ ^ x - σ' ^ x) + (σ ^ (L - x) - σ' ^ (L - x))) / (1 - σ ^ L) +
        (σ' ^ x + σ' ^ (L - x)) * ((σ ^ L - σ' ^ L) / ((1 - σ ^ L) * (1 - σ' ^ L))) := by
    field_simp; ring
  rw [e]
  have p1 := lg_pow_sub_le_s σ σ' s h0 h0' hs hs' hs16 x
  have p2 := lg_pow_sub_le_s σ σ' s h0 h0' hs hs' hs16 (L - x)
  have p3 := lg_pow_sub_le_s σ σ' s h0 h0' hs hs' hs16 L
  have hsx : σ' ^ x ≤ s ^ x := pow_le_pow_left₀ h0' hs' x
  have hsy : σ' ^ (L - x) ≤ s ^ (L - x) := pow_le_pow_left₀ h0' hs' (L - x)
  have hs0 : 0 ≤ s := le_trans h0 hs
  have hΔ := abs_nonneg (σ - σ')
  have t1 : |((σ ^ x - σ' ^ x) + (σ ^ (L - x) - σ' ^ (L - x))) / (1 - σ ^ L)| ≤
      22 * ((x : ℝ) * s ^ x + ((L - x : ℕ) : ℝ) * s ^ (L - x)) * |σ - σ'| := by
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 - σ ^ L), div_le_iff₀ (by linarith)]
    have := abs_add_le (σ ^ x - σ' ^ x) (σ ^ (L - x) - σ' ^ (L - x))
    have hn : 0 ≤ ((x : ℝ) * s ^ x + ((L - x : ℕ) : ℝ) * s ^ (L - x)) * |σ - σ'| := by positivity
    nlinarith
  have t2 : |(σ' ^ x + σ' ^ (L - x)) * ((σ ^ L - σ' ^ L) / ((1 - σ ^ L) * (1 - σ' ^ L)))| ≤
      29 * (s ^ x + s ^ (L - x)) * ((L : ℝ) * s ^ L) * |σ - σ'| := by
    rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (1 - σ ^ L) * (1 - σ' ^ L)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ σ' ^ x + σ' ^ (L - x))]
    have hDD : 9 / 16 ≤ (1 - σ ^ L) * (1 - σ' ^ L) := by nlinarith
    have hq : |σ ^ L - σ' ^ L| / ((1 - σ ^ L) * (1 - σ' ^ L)) ≤
        29 * ((L : ℝ) * s ^ L) * |σ - σ'| := by
      rw [div_le_iff₀ (by linarith)]
      have hn : 0 ≤ (L : ℝ) * s ^ L * |σ - σ'| := by positivity
      nlinarith
    calc (σ' ^ x + σ' ^ (L - x)) * (|σ ^ L - σ' ^ L| / ((1 - σ ^ L) * (1 - σ' ^ L)))
        ≤ (s ^ x + s ^ (L - x)) * (29 * ((L : ℝ) * s ^ L) * |σ - σ'|) := by
          gcongr
      _ = _ := by ring
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add t1 t2
    _ = _ := by ring

namespace LgGood

variable {k γ E : ℝ} {L : ℕ} {m mInf : ℂ} (h : LgGood k γ E L m mInf)
include h

private lemma s_facts : 1 / 16 ≤ Real.exp (-(γ * k / 512)) ∧
    γ * k / 1024 ≤ 1 - Real.exp (-(γ * k / 512)) ∧
    Real.exp (-(γ * k / 512)) ^ L ≤ 1 / 4 ∧
    ‖freeRho 1 ((E : ℂ) + γ * m)‖ ^ 2 ≤ Real.exp (-(γ * k / 512)) ∧
    ‖freeRho 1 ((E : ℂ) + γ * mInf)‖ ^ 2 ≤ Real.exp (-(γ * k / 512)) := by
  have hb := h.b_pos
  have hb1 := h.b_le
  have hγ := h.γ1
  have hk := h.hk1
  have hb2 : γ * k / 512 ≤ 1 / 512 := by
    have : γ * k ≤ 1 := by nlinarith [h.hγ, h.hk]
    linarith
  have e2 : Real.exp (-(γ * k / 512)) = Real.exp (-(γ * k / 1024)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := Real.add_one_le_exp (-(γ * k / 512)); linarith
  · have := lg_one_sub_exp_neg (γ * k / 512) (by have := h.hγ; have := h.hk; positivity)
      (by linarith)
    linarith
  · have e3 : Real.exp (-(γ * k / 512)) ^ L = Real.exp (-(k / 1024 * (γ * L))) ^ 2 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [e3]
    have := h.exp_aH_half
    have := Real.exp_pos (-(k / 1024 * (γ * L)))
    nlinarith
  · rw [e2]; gcongr; exact h.rho_le h.hm
  · rw [e2]; gcongr; exact h.rho_le h.hmI

/-- Pointwise decomposition of `P - P₀` into three explicit error profiles. -/
private lemma P_sub_le {g : ℝ} (hb : hopB g = 1) (hγg : gammaG g = γ) [NeZero L] (a c : Fin L) :
    |pairP γ (dysonMat 1 γ L E m) a c - perP0 g L E mInf (c - a)| ≤
      γ / k ^ 2 * Real.exp (-(k / 1024 * (γ * L))) *
          (16 * (Real.exp (-(γ * k / 512)) ^ lgD L a c +
            Real.exp (-(γ * k / 512)) ^ (L - lgD L a c)) + 8) +
        64 / k ^ 5 * γ ^ 2 * Real.exp (-(k / 1024 * (γ * L))) *
          (Real.exp (-(γ * k / 512)) ^ lgD L a c + Real.exp (-(γ * k / 512)) ^ (L - lgD L a c)) +
        32 / k ^ 4 * γ ^ 2 * Real.exp (-(k / 1024 * (γ * L))) *
          (22 * ((lgD L a c : ℝ) * Real.exp (-(γ * k / 512)) ^ lgD L a c +
              ((L - lgD L a c : ℕ) : ℝ) * Real.exp (-(γ * k / 512)) ^ (L - lgD L a c)) +
            29 * (Real.exp (-(γ * k / 512)) ^ lgD L a c +
              Real.exp (-(γ * k / 512)) ^ (L - lgD L a c)) *
              ((L : ℝ) * Real.exp (-(γ * k / 512)) ^ L)) := by
  obtain ⟨hs16, hs1, hsL, hr, hrI⟩ := h.s_facts
  set s := Real.exp (-(γ * k / 512)) with hsdef
  set Z := Real.exp (-(k / 1024 * (γ * L))) with hZ
  set x := lgD L a c with hxdef
  set ρ := freeRho 1 ((E : ℂ) + γ * m) with hρ
  set ρI := freeRho 1 ((E : ℂ) + γ * mInf) with hρI
  set f := freeT 1 ((E : ℂ) + γ * m) with hf
  set fI := freeT 1 ((E : ℂ) + γ * mInf) with hfI
  have hk := h.hk
  have hγ := h.hγ
  have hs0 : 0 ≤ s := (Real.exp_pos _).le
  have hZ0 : 0 ≤ Z := (Real.exp_pos _).le
  -- the two sides
  have hP : pairP γ (dysonMat 1 γ L E m) a c = γ * ‖f‖ ^ 2 * ‖geomV ρ L x‖ ^ 2 := by
    simp only [pairP, Matrix.of_apply, h.dysonMat_eq, Matrix.smul_apply, geomC, smul_eq_mul,
      norm_mul]
    rw [hxdef]; ring
  have hP0 : perP0 g L E mInf (c - a) = γ * ‖fI‖ ^ 2 * geomV (‖ρI‖ ^ 2) L x := by
    rw [lg_perP0_eq hb hγg mInf _ (h.rho_lt h.hmI), ← lgD_eq_sub_val]
  rw [hP, hP0]
  have hx : x ≤ L := (lgD_lt a c).le
  -- term 1
  have hzL : ‖ρ‖ ^ L ≤ Z := h.rho_pow_le h.hm
  have hz2 : ‖ρ‖ ^ L ≤ 1 / 2 := hzL.trans (h.exp_aH_half.trans (by norm_num))
  have t1 := lg_AB ρ hx hz2
  have hrx : (‖ρ‖ ^ 2) ^ x ≤ s ^ x := pow_le_pow_left₀ (by positivity) hr x
  have hry : (‖ρ‖ ^ 2) ^ (L - x) ≤ s ^ (L - x) := pow_le_pow_left₀ (by positivity) hr (L - x)
  have hfle : ‖f‖ ≤ 1 / k := h.f_le h.hm
  have hfIle : ‖fI‖ ≤ 1 / k := h.f_le h.hmI
  have hf2 : ‖f‖ ^ 2 ≤ 1 / k ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg f) hfle 2; rw [div_pow, one_pow] at this; exact this
  have hfI2 : ‖fI‖ ^ 2 ≤ 1 / k ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg fI) hfIle 2; rw [div_pow, one_pow] at this; exact this
  -- term 2
  have hB : geomV (‖ρ‖ ^ 2) L x ≤ 4 / 3 * (s ^ x + s ^ (L - x)) := by
    unfold geomV
    have hσL : (‖ρ‖ ^ 2) ^ L ≤ 1 / 4 := (pow_le_pow_left₀ (by positivity) hr L).trans hsL
    rw [div_le_iff₀ (by linarith)]
    nlinarith [pow_nonneg (sq_nonneg ‖ρ‖) x, pow_nonneg (sq_nonneg ‖ρ‖) (L - x),
      pow_nonneg (sq_nonneg ‖ρ‖) L]
  have hB0 : 0 ≤ geomV (‖ρ‖ ^ 2) L x := by
    unfold geomV
    have hσL : (‖ρ‖ ^ 2) ^ L ≤ 1 / 4 := (pow_le_pow_left₀ (by positivity) hr L).trans hsL
    have : 0 < 1 - (‖ρ‖ ^ 2) ^ L := by linarith
    positivity
  have hdf : |‖f‖ ^ 2 - ‖fI‖ ^ 2| ≤ 48 / k ^ 5 * γ * Z := by
    have e : ‖f‖ ^ 2 - ‖fI‖ ^ 2 = (‖f‖ + ‖fI‖) * (‖f‖ - ‖fI‖) := by ring
    rw [e, abs_mul, abs_of_nonneg (by positivity)]
    have h1 : |‖f‖ - ‖fI‖| ≤ 24 / k ^ 4 * γ * Z := (abs_norm_sub_norm_le f fI).trans h.f_sub
    calc (‖f‖ + ‖fI‖) * |‖f‖ - ‖fI‖| ≤ (2 / k) * (24 / k ^ 4 * γ * Z) := by
          gcongr
          linarith [show 2 / k = 1 / k + 1 / k by ring]
      _ = 48 / k ^ 5 * γ * Z := by field_simp; ring
  -- term 3
  have hrr : |‖ρ‖ ^ 2 - ‖ρI‖ ^ 2| ≤ 32 / k ^ 2 * γ * Z := by
    have e : ‖ρ‖ ^ 2 - ‖ρI‖ ^ 2 = (‖ρ‖ + ‖ρI‖) * (‖ρ‖ - ‖ρI‖) := by ring
    rw [e, abs_mul, abs_of_nonneg (by positivity)]
    have h1 : |‖ρ‖ - ‖ρI‖| ≤ 16 / k ^ 2 * γ * Z := (abs_norm_sub_norm_le ρ ρI).trans h.rho_sub
    have h2 : ‖ρ‖ + ‖ρI‖ ≤ 2 := by linarith [h.rho_lt h.hm, h.rho_lt h.hmI]
    calc (‖ρ‖ + ‖ρI‖) * |‖ρ‖ - ‖ρI‖| ≤ 2 * (16 / k ^ 2 * γ * Z) := by gcongr
      _ = 32 / k ^ 2 * γ * Z := by ring
  have t3 := lg_BB (‖ρ‖ ^ 2) (‖ρI‖ ^ 2) s (L := L) (x := x) (by positivity) (by positivity) hr hrI
    hs16 hsL
  -- assemble
  have e : γ * ‖f‖ ^ 2 * ‖geomV ρ L x‖ ^ 2 - γ * ‖fI‖ ^ 2 * geomV (‖ρI‖ ^ 2) L x =
      γ * ‖f‖ ^ 2 * (‖geomV ρ L x‖ ^ 2 - geomV (‖ρ‖ ^ 2) L x) +
        γ * (‖f‖ ^ 2 - ‖fI‖ ^ 2) * geomV (‖ρ‖ ^ 2) L x +
        γ * ‖fI‖ ^ 2 * (geomV (‖ρ‖ ^ 2) L x - geomV (‖ρI‖ ^ 2) L x) := by ring
  rw [e]
  have b1 : |γ * ‖f‖ ^ 2 * (‖geomV ρ L x‖ ^ 2 - geomV (‖ρ‖ ^ 2) L x)| ≤
      γ / k ^ 2 * Z * (16 * (s ^ x + s ^ (L - x)) + 8) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc γ * ‖f‖ ^ 2 * |‖geomV ρ L x‖ ^ 2 - geomV (‖ρ‖ ^ 2) L x|
        ≤ γ * (1 / k ^ 2) * (‖ρ‖ ^ L * (16 * ((‖ρ‖ ^ 2) ^ x + (‖ρ‖ ^ 2) ^ (L - x)) + 8)) := by
          gcongr
      _ ≤ γ * (1 / k ^ 2) * (Z * (16 * (s ^ x + s ^ (L - x)) + 8)) := by gcongr
      _ = _ := by ring
  have b2 : |γ * (‖f‖ ^ 2 - ‖fI‖ ^ 2) * geomV (‖ρ‖ ^ 2) L x| ≤
      64 / k ^ 5 * γ ^ 2 * Z * (s ^ x + s ^ (L - x)) := by
    rw [abs_mul, abs_mul, abs_of_pos hγ, abs_of_nonneg hB0]
    calc γ * |‖f‖ ^ 2 - ‖fI‖ ^ 2| * geomV (‖ρ‖ ^ 2) L x
        ≤ γ * (48 / k ^ 5 * γ * Z) * (4 / 3 * (s ^ x + s ^ (L - x))) := by gcongr
      _ = _ := by ring
  have b3 : |γ * ‖fI‖ ^ 2 * (geomV (‖ρ‖ ^ 2) L x - geomV (‖ρI‖ ^ 2) L x)| ≤
      32 / k ^ 4 * γ ^ 2 * Z * (22 * ((x : ℝ) * s ^ x + ((L - x : ℕ) : ℝ) * s ^ (L - x)) +
        29 * (s ^ x + s ^ (L - x)) * ((L : ℝ) * s ^ L)) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc γ * ‖fI‖ ^ 2 * |geomV (‖ρ‖ ^ 2) L x - geomV (‖ρI‖ ^ 2) L x|
        ≤ γ * (1 / k ^ 2) * ((22 * ((x : ℝ) * s ^ x + ((L - x : ℕ) : ℝ) * s ^ (L - x)) +
          29 * (s ^ x + s ^ (L - x)) * ((L : ℝ) * s ^ L)) * (32 / k ^ 2 * γ * Z)) := by
          gcongr
          exact t3.trans (mul_le_mul_of_nonneg_left hrr (by positivity))
      _ = _ := by field_simp
  calc _ ≤ _ := abs_add_three _ _ _
    _ ≤ _ := add_le_add_three b1 b2 b3

end LgGood

private lemma lg_sum_le_three {ι : Type*} [Fintype ι] (w f A B C : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hf : ∀ i, f i ≤ A i + B i + C i) :
    ∑ i, w i * f i ≤ ∑ i, w i * A i + ∑ i, w i * B i + ∑ i, w i * C i := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have := mul_le_mul_of_nonneg_left (hf i) (hw i)
  linarith

namespace LgGood

variable {k γ E : ℝ} {L : ℕ} {m mInf : ℂ} (h : LgGood k γ E L m mInf)
include h

/-- (A.14) [uvp:eq:finiteerror], pointwise: `|P_ac - P₀(c - a)| ≤ (3.4·10⁶/k⁵) γ e^{-(k/1024)γL}`.
-/
private lemma P_sub_pt {g : ℝ} (hb : hopB g = 1) (hγg : gammaG g = γ) [NeZero L] (a c : Fin L) :
    |pairP γ (dysonMat 1 γ L E m) a c - perP0 g L E mInf (c - a)| ≤
      3400000 / k ^ 5 * γ * Real.exp (-(k / 1024 * (γ * L))) := by
  refine (h.P_sub_le hb hγg a c).trans ?_
  obtain ⟨hs16, hs1, hsL, -, -⟩ := h.s_facts
  set s := Real.exp (-(γ * k / 512)) with hsdef
  set Z := Real.exp (-(k / 1024 * (γ * L))) with hZ
  set x := lgD L a c
  have hk := h.hk
  have hk1 := h.hk1
  have hγ := h.hγ
  have hγ1 := h.γ1
  have hs0 : 0 ≤ s := (Real.exp_pos _).le
  have hslt : s < 1 := by linarith [h.b_pos]
  have hZ0 : 0 ≤ Z := (Real.exp_pos _).le
  have hinv : 1 / (1 - s) ≤ 1024 / (γ * k) := by
    rw [div_le_div_iff₀ (by linarith) (by positivity)]; linarith
  have hsx : s ^ x + s ^ (L - x) ≤ 2 := by
    have := pow_le_one₀ hs0 hslt.le (n := x)
    have := pow_le_one₀ hs0 hslt.le (n := L - x)
    linarith
  have n1 : (x : ℝ) * s ^ x ≤ 1024 / (γ * k) := (lg_n_pow_le s hs0 hslt x).trans hinv
  have n2 : ((L - x : ℕ) : ℝ) * s ^ (L - x) ≤ 1024 / (γ * k) :=
    (lg_n_pow_le s hs0 hslt (L - x)).trans hinv
  have n3 : (L : ℝ) * s ^ L ≤ 1024 / (γ * k) := (lg_n_pow_le s hs0 hslt L).trans hinv
  have hk5 : k ^ 5 ≤ k ^ 2 := pow_le_pow_of_le_one hk.le hk1 (by norm_num)
  have i1 : γ / k ^ 2 * Z * (16 * (s ^ x + s ^ (L - x)) + 8) ≤ 40 / k ^ 5 * γ * Z := by
    have : γ / k ^ 2 ≤ γ / k ^ 5 := div_le_div_of_nonneg_left hγ.le (by positivity) hk5
    calc γ / k ^ 2 * Z * (16 * (s ^ x + s ^ (L - x)) + 8) ≤ γ / k ^ 5 * Z * (16 * 2 + 8) := by
          gcongr
      _ = 40 / k ^ 5 * γ * Z := by ring
  have i2 : 64 / k ^ 5 * γ ^ 2 * Z * (s ^ x + s ^ (L - x)) ≤ 128 / k ^ 5 * γ * Z := by
    calc 64 / k ^ 5 * γ ^ 2 * Z * (s ^ x + s ^ (L - x)) ≤ 64 / k ^ 5 * (γ * 1) * Z * 2 := by
          rw [sq]; gcongr
      _ = 128 / k ^ 5 * γ * Z := by ring
  have i3 : 32 / k ^ 4 * γ ^ 2 * Z * (22 * ((x : ℝ) * s ^ x + ((L - x : ℕ) : ℝ) * s ^ (L - x)) +
      29 * (s ^ x + s ^ (L - x)) * ((L : ℝ) * s ^ L)) ≤ 3342336 / k ^ 5 * γ * Z := by
    calc 32 / k ^ 4 * γ ^ 2 * Z * (22 * ((x : ℝ) * s ^ x + ((L - x : ℕ) : ℝ) * s ^ (L - x)) +
          29 * (s ^ x + s ^ (L - x)) * ((L : ℝ) * s ^ L))
        ≤ 32 / k ^ 4 * γ ^ 2 * Z * (22 * (1024 / (γ * k) + 1024 / (γ * k)) +
          29 * 2 * (1024 / (γ * k))) := by gcongr
      _ = 3342336 / k ^ 5 * γ * Z := by field_simp; ring
  have e1 : 40 / k ^ 5 * γ * Z = 40 * (γ * Z / k ^ 5) := by ring
  have e2 : 128 / k ^ 5 * γ * Z = 128 * (γ * Z / k ^ 5) := by ring
  have e3 : 3342336 / k ^ 5 * γ * Z = 3342336 * (γ * Z / k ^ 5) := by ring
  have e4 : 3400000 / k ^ 5 * γ * Z = 3400000 * (γ * Z / k ^ 5) := by ring
  have hp : 0 ≤ γ * Z / k ^ 5 := by positivity
  linarith

/-- (A.14) [uvp:eq:finiteerror], weighted:
`Σ_c e^{μ d} |P_ac - P₀(c - a)| ≤ (10^10/k⁶)(1 + γL) e^{-(3k/4096)γL}` for
`μ ≤ γk/2048`. -/
private lemma P_sub_row {g : ℝ} (hb : hopB g = 1) (hγg : gammaG g = γ) [NeZero L] (a : Fin L) (μ :
    ℝ)
    (hμ0 : 0 ≤ μ) (hμ : μ ≤ γ * k / 2048) :
    ∑ c, Real.exp (μ * cycDist a c) *
        |pairP γ (dysonMat 1 γ L E m) a c - perP0 g L E mInf (c - a)| ≤
      10000000000 / k ^ 6 * (1 + γ * L) * Real.exp (-(3 * k / 4096 * (γ * L))) := by
  obtain ⟨hs16, hs1, hsL, -, -⟩ := h.s_facts
  set s := Real.exp (-(γ * k / 512)) with hsdef
  set Z := Real.exp (-(k / 1024 * (γ * L))) with hZ
  have hk := h.hk
  have hk1 := h.hk1
  have hγ := h.hγ
  have hγ1 := h.γ1
  have hb0 := h.b_pos
  have hs0 : 0 ≤ s := (Real.exp_pos _).le
  have hslt : s < 1 := by linarith
  have hZ0 : 0 ≤ Z := (Real.exp_pos _).le
  have hinv : 1 / (1 - s) ≤ 1024 / (γ * k) := by
    rw [div_le_div_iff₀ (by linarith) (by positivity)]; linarith
  have n3 : (L : ℝ) * s ^ L ≤ 1024 / (γ * k) := (lg_n_pow_le s hs0 hslt L).trans hinv
  -- the weight against `s`
  have hμs : Real.exp μ * s ≤ Real.exp (-(3 * γ * k / 2048)) := by
    rw [hsdef, ← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have hgap : γ * k / 2048 ≤ 1 - Real.exp μ * s := by
    have h1 := lg_one_sub_exp_neg (3 * γ * k / 2048) (by positivity)
      (by have : γ * k ≤ 1 := by nlinarith
          linarith)
    linarith
  have hμs1 : Real.exp μ * s < 1 := by linarith
  have rg := fun a : Fin L => lg_row_geom a μ s hμ0 hs0 hμs1
  have rn := fun a : Fin L => lg_row_ngeom a μ s hμ0 hs0 hμs1
  have hg1 : 2 / (1 - Real.exp μ * s) ≤ 4096 / (γ * k) := by
    rw [div_le_div_iff₀ (by linarith) (by positivity)]; nlinarith
  have hg2 : 2 / (1 - Real.exp μ * s) ^ 2 ≤ 2 * (2048 / (γ * k)) ^ 2 := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    have : (γ * k) ^ 2 ≤ 2048 ^ 2 * (1 - Real.exp μ * s) ^ 2 := by
      have : γ * k ≤ 2048 * (1 - Real.exp μ * s) := by linarith
      nlinarith [mul_pos hγ hk]
    rw [mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  -- constant part of the row
  have hconst : ∑ c : Fin L, Real.exp (μ * cycDist a c) * 8 ≤ 8 * L * Real.exp (μ * L / 2) := by
    have : ∀ c : Fin L, Real.exp (μ * cycDist a c) * 8 ≤ Real.exp (μ * L / 2) * 8 := by
      intro c
      gcongr
      have := cycDist_le_half a c
      have : (2 * cycDist a c : ℕ) ≤ (L : ℝ) := by exact_mod_cast this
      push_cast at this
      nlinarith
    refine (Finset.sum_le_sum fun c _ => this c).trans (le_of_eq ?_)
    simp; ring
  have hZμ : Z * Real.exp (μ * L / 2) ≤ Real.exp (-(3 * k / 4096 * (γ * L))) := by
    rw [hZ, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : μ * L ≤ γ * k / 2048 * L := by gcongr
    nlinarith
  have hZ3 : Z ≤ Real.exp (-(3 * k / 4096 * (γ * L))) := by
    rw [hZ]; apply Real.exp_le_exp.mpr
    have : 0 ≤ γ * L := by positivity
    nlinarith
  -- sum of the pointwise decomposition
  refine (lg_sum_le_three _ _ _ _ _ (fun c => (Real.exp_pos (μ * cycDist a c)).le)
    (h.P_sub_le hb hγg a)).trans ?_
  -- three pieces
  have p1 : ∑ c, Real.exp (μ * cycDist a c) * (γ / k ^ 2 * Z *
      (16 * (s ^ lgD L a c + s ^ (L - lgD L a c)) + 8)) ≤
      γ / k ^ 2 * Z * (16 * (4096 / (γ * k)) + 8 * L * Real.exp (μ * L / 2)) := by
    have e : ∀ c : Fin L, Real.exp (μ * cycDist a c) * (γ / k ^ 2 * Z *
        (16 * (s ^ lgD L a c + s ^ (L - lgD L a c)) + 8)) =
        γ / k ^ 2 * Z * (16 * (Real.exp (μ * cycDist a c) * (s ^ lgD L a c + s ^ (L - lgD L a c))) +
          Real.exp (μ * cycDist a c) * 8) := fun c => by ring
    simp only [e]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
    gcongr
    exact (rg a).trans hg1
  have p2 : ∑ c, Real.exp (μ * cycDist a c) * (64 / k ^ 5 * γ ^ 2 * Z *
      (s ^ lgD L a c + s ^ (L - lgD L a c))) ≤ 64 / k ^ 5 * γ ^ 2 * Z * (4096 / (γ * k)) := by
    have e : ∀ c : Fin L, Real.exp (μ * cycDist a c) * (64 / k ^ 5 * γ ^ 2 * Z *
        (s ^ lgD L a c + s ^ (L - lgD L a c))) = 64 / k ^ 5 * γ ^ 2 * Z *
        (Real.exp (μ * cycDist a c) * (s ^ lgD L a c + s ^ (L - lgD L a c))) := fun c => by ring
    simp only [e]
    rw [← Finset.mul_sum]
    gcongr
    exact (rg a).trans hg1
  have p3 : ∑ c, Real.exp (μ * cycDist a c) * (32 / k ^ 4 * γ ^ 2 * Z *
      (22 * ((lgD L a c : ℝ) * s ^ lgD L a c + ((L - lgD L a c : ℕ) : ℝ) * s ^ (L - lgD L a c)) +
        29 * (s ^ lgD L a c + s ^ (L - lgD L a c)) * ((L : ℝ) * s ^ L))) ≤
      32 / k ^ 4 * γ ^ 2 * Z * (22 * (2 * (2048 / (γ * k)) ^ 2) +
        29 * (1024 / (γ * k)) * (4096 / (γ * k))) := by
    have e : ∀ c : Fin L, Real.exp (μ * cycDist a c) * (32 / k ^ 4 * γ ^ 2 * Z *
        (22 * ((lgD L a c : ℝ) * s ^ lgD L a c + ((L - lgD L a c : ℕ) : ℝ) * s ^ (L - lgD L a c)) +
          29 * (s ^ lgD L a c + s ^ (L - lgD L a c)) * ((L : ℝ) * s ^ L))) =
        32 / k ^ 4 * γ ^ 2 * Z * (22 * (Real.exp (μ * cycDist a c) *
          ((lgD L a c : ℝ) * s ^ lgD L a c + ((L - lgD L a c : ℕ) : ℝ) * s ^ (L - lgD L a c))) +
          29 * ((L : ℝ) * s ^ L) *
            (Real.exp (μ * cycDist a c) * (s ^ lgD L a c + s ^ (L - lgD L a c)))) := fun c => by
      ring
    simp only [e]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    gcongr
    · exact (rn a).trans hg2
    · exact (rg a).trans hg1
  have e1 : γ / k ^ 2 * Z * (16 * (4096 / (γ * k)) + 8 * L * Real.exp (μ * L / 2)) =
      65536 / k ^ 3 * Z + 8 / k ^ 2 * (γ * L) * (Z * Real.exp (μ * L / 2)) := by
    field_simp; ring
  have e2 : 64 / k ^ 5 * γ ^ 2 * Z * (4096 / (γ * k)) = 262144 / k ^ 6 * γ * Z := by
    field_simp; ring
  have e3 : 32 / k ^ 4 * γ ^ 2 * Z * (22 * (2 * (2048 / (γ * k)) ^ 2) +
      29 * (1024 / (γ * k)) * (4096 / (γ * k))) = 9797894144 / k ^ 6 * Z := by
    field_simp; ring
  rw [e1] at p1; rw [e2] at p2; rw [e3] at p3
  set X := Real.exp (-(3 * k / 4096 * (γ * L)))
  have hX0 : 0 ≤ X := (Real.exp_pos _).le
  have hH0 : 0 ≤ γ * L := by positivity
  have hk6 : k ^ 6 ≤ k ^ 3 := pow_le_pow_of_le_one hk.le hk1 (by norm_num)
  have hk6' : k ^ 6 ≤ k ^ 2 := pow_le_pow_of_le_one hk.le hk1 (by norm_num)
  have q1 : 65536 / k ^ 3 * Z ≤ 65536 / k ^ 6 * X := by
    gcongr
  have q2 : 8 / k ^ 2 * (γ * L) * (Z * Real.exp (μ * L / 2)) ≤ 8 / k ^ 6 * (γ * L) * X := by
    gcongr
  have q3 : 262144 / k ^ 6 * γ * Z ≤ 262144 / k ^ 6 * X := by
    calc 262144 / k ^ 6 * γ * Z ≤ 262144 / k ^ 6 * 1 * X := by gcongr
      _ = _ := by ring
  have q4 : 9797894144 / k ^ 6 * Z ≤ 9797894144 / k ^ 6 * X := by gcongr
  have fin : 65536 / k ^ 6 * X + 8 / k ^ 6 * (γ * L) * X + 262144 / k ^ 6 * X +
      9797894144 / k ^ 6 * X ≤ 10000000000 / k ^ 6 * (1 + γ * L) * X := by
    have hk6p : 0 < k ^ 6 := by positivity
    rw [show 65536 / k ^ 6 * X + 8 / k ^ 6 * (γ * L) * X + 262144 / k ^ 6 * X +
      9797894144 / k ^ 6 * X = (9798221824 + 8 * (γ * L)) * X / k ^ 6 by field_simp; ring,
      show 10000000000 / k ^ 6 * (1 + γ * L) * X = (10000000000 * (1 + γ * L)) * X / k ^ 6 by
        field_simp]
    gcongr
    linarith
  calc _ ≤ 65536 / k ^ 3 * Z + 8 / k ^ 2 * (γ * L) * (Z * Real.exp (μ * L / 2)) +
        262144 / k ^ 6 * γ * Z + 9797894144 / k ^ 6 * Z := by
        have := add_le_add (add_le_add p1 p2) p3
        linarith
    _ ≤ 65536 / k ^ 6 * X + 8 / k ^ 6 * (γ * L) * X + 262144 / k ^ 6 * X +
        9797894144 / k ^ 6 * X := by linarith
    _ ≤ _ := fin

end LgGood

/-! ### Same-sign stability at large coupling: (A.16) [uvp:eq:stable] -/

/-- A square root in the closed upper half-plane. -/
private lemma lg_exists_sqrt_upper (p : ℂ) : ∃ v : ℂ, v ^ 2 = p ∧ 0 ≤ v.im := by
  have h := Complex.cpow_ofNat_inv_pow p 2
  by_cases hv : 0 ≤ (p ^ (2⁻¹ : ℂ)).im
  · exact ⟨p ^ (2⁻¹ : ℂ), h, hv⟩
  · refine ⟨-(p ^ (2⁻¹ : ℂ)), by rw [neg_sq]; exact h, ?_⟩
    rw [Complex.neg_im]; linarith

/-- For `v² = w w'` with `w, w' ∈ ℂ_+` and `Im v ≥ 0`: `(Im v)² ≥ Im w Im w'`. -/
private lemma lg_sqrt_im_sq (w w' v : ℂ) (hv : v ^ 2 = w * w') :
    w.im * w'.im ≤ v.im ^ 2 := by
  have hre := congrArg Complex.re hv
  have hnorm : ‖v‖ ^ 2 = ‖w‖ * ‖w'‖ := by rw [← norm_pow, hv, norm_mul]
  rw [Complex.sq_norm, Complex.normSq_apply] at hnorm
  simp only [sq, Complex.mul_re] at hre
  have hcs : w.re * w'.re + w.im * w'.im ≤ ‖w‖ * ‖w'‖ := by
    have h1 : (w.re * w'.re + w.im * w'.im) ^ 2 ≤ (‖w‖ * ‖w'‖) ^ 2 := by
      rw [mul_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      nlinarith [sq_nonneg (w.re * w'.im - w.im * w'.re)]
    nlinarith [norm_nonneg w, norm_nonneg w', mul_nonneg (norm_nonneg w) (norm_nonneg w')]
  nlinarith

/-- The all-ones matrix. -/
private def lgJ (L : ℕ) : Matrix (Fin L) (Fin L) ℂ := Matrix.of fun _ _ => 1

private lemma lg_geomC_mul_J {τ : ℂ} (h1 : τ ≠ 1) {L : ℕ} (hD : 1 - τ ^ L ≠ 0) :
    geomC τ L * lgJ L = ((1 + τ) / (1 - τ)) • lgJ L := by
  ext a c
  simp only [Matrix.mul_apply, lgJ, Matrix.of_apply, mul_one, Matrix.smul_apply, smul_eq_mul]
  exact geomC_row_sum h1 hD a

private lemma lg_J_mul_geomC {τ : ℂ} (h1 : τ ≠ 1) {L : ℕ} (hD : 1 - τ ^ L ≠ 0) :
    lgJ L * geomC τ L = ((1 + τ) / (1 - τ)) • lgJ L := by
  ext a c
  simp only [Matrix.mul_apply, lgJ, Matrix.of_apply, one_mul, Matrix.smul_apply, smul_eq_mul,
    mul_one]
  exact geomC_col_sum h1 hD c

private lemma lg_J_mul_J (L : ℕ) : lgJ L * lgJ L = (L : ℂ) • lgJ L := by
  ext a c
  simp [Matrix.mul_apply, lgJ]

/-- Explicit inverse of `I - t(αG_σ + βJ)`. -/
private lemma lg_stable_inv {L : ℕ} (hL : 3 ≤ L) (σ τ α β B t : ℂ) (hσ0 : σ ≠ 0) (hσL : 1 - σ ^ L ≠
    0)
    (hσ1 : σ ≠ 1) (hτ0 : τ ≠ 0) (hτL : 1 - τ ^ L ≠ 0) (hτ1 : τ ≠ 1) (hστ : σ⁻¹ - σ ≠ 0)
    (hM3 : σ + σ⁻¹ - t * α * (σ⁻¹ - σ) = τ + τ⁻¹) (hB : B * (τ⁻¹ - τ) = t * α * (σ⁻¹ - σ))
    (hden : 1 - t * α * ((1 + σ) / (1 - σ)) - t * β * L ≠ 0) :
    (1 - t • (α • geomC σ L + β • lgJ L))⁻¹ =
      1 + B • geomC τ L + (t * β * (1 + B * ((1 + τ) / (1 - τ))) /
        (1 - t * α * ((1 + σ) / (1 - σ)) - t * β * L)) • lgJ L := by
  have hGJ := lg_geomC_mul_J hσ1 hσL
  have hJG := lg_J_mul_geomC hτ1 hτL
  have hJJ := lg_J_mul_J L
  set Gσ := geomC σ L
  set Gτ := geomC τ L
  set J := lgJ L
  set A := adjK ℂ L
  have hTσ := geomC_mul hσ0 hσL hL
  have hTτ := geomC_mul hτ0 hτL hL
  set Tσ := (σ + σ⁻¹) • (1 : Matrix (Fin L) (Fin L) ℂ) - A
  set Tτ := (τ + τ⁻¹) • (1 : Matrix (Fin L) (Fin L) ℂ) - A
  -- `X₀ = I + B G_τ` inverts `I - tα G_σ`
  have h1 : Tσ * (1 - (t * α) • Gσ) = Tτ := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, hTσ, smul_smul]
    simp only [Tσ, Tτ, ← hM3]
    module
  have h2 : Tτ * (1 + B • Gτ) = Tσ := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, hTτ, smul_smul, hB]
    simp only [Tσ, Tτ, ← hM3]
    module
  have hYT : ((σ⁻¹ - σ)⁻¹ • Gσ) * Tσ = 1 := by
    rw [mul_eq_one_comm, Matrix.mul_smul, hTσ, smul_smul, inv_mul_cancel₀ hστ, one_smul]
  have hX0 : (1 - (t * α) • Gσ) * (1 + B • Gτ) = 1 := by
    have : Tσ * ((1 - (t * α) • Gσ) * (1 + B • Gτ)) = Tσ := by rw [← Matrix.mul_assoc, h1, h2]
    have := congrArg (fun X => ((σ⁻¹ - σ)⁻¹ • Gσ) * X) this
    simp only [← Matrix.mul_assoc, hYT, Matrix.one_mul] at this
    exact this
  -- the rank-one part
  apply Matrix.inv_eq_right_inv
  set gσ := (1 + σ) / (1 - σ)
  set gτ := (1 + τ) / (1 - τ)
  set κ := t * β * (1 + B * gτ) / (1 - t * α * gσ - t * β * L) with hκ
  have hκe : κ * (1 - t * α * gσ - t * β * L) = t * β * (1 + B * gτ) := by
    rw [hκ]; field_simp
  clear_value κ gσ gτ
  have e1 : (1 - t • (α • Gσ + β • J)) = (1 - (t * α) • Gσ) - (t * β) • J := by
    rw [smul_add, smul_smul, smul_smul]; abel
  rw [e1]
  have e2 : ((1 - (t * α) • Gσ) - (t * β) • J) * (1 + B • Gτ + κ • J) =
      (1 - (t * α) • Gσ) * (1 + B • Gτ) +
        (κ - κ * (t * α * gσ) - t * β - t * β * (B * gτ) - t * β * κ * L) • J := by
    simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hGJ, hJG, hJJ, smul_smul, sub_smul]
    module
  rw [e2, hX0]
  have e3 : κ - κ * (t * α * gσ) - t * β - t * β * (B * gτ) - t * β * κ * L = 0 := by
    linear_combination hκe
  rw [e3, zero_smul, add_zero]

private lemma lg_tail_bound (a H : ℝ) (ha : 0 < a) (hH : 0 ≤ H) :
    H * Real.exp (-(a * H)) ≤ 1 + 2 / a := by
  have h := lg_tail_le a H ha hH
  have h1 : Real.exp (-(a * H / 2)) ≤ 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith)
  have h2 : H * Real.exp (-(a * H)) ≤ (1 + H) * Real.exp (-(a * H)) := by
    have := Real.exp_pos (-(a * H)); nlinarith
  have h3 : 0 < 1 + 2 / a := by positivity
  nlinarith

namespace LgGood

variable {k γ E : ℝ} {L : ℕ} {m mInf : ℂ} (h : LgGood k γ E L m mInf)
include h

/-- `Q = α G_{ρ²} + β J` with `α = γ f m`, `β = 2γ f² ρ^L/(1 - ρ^L)²`. -/
private lemma pairQ_eq [NeZero L] :
    pairQ γ (dysonMat 1 γ L E m) =
      (γ * freeT 1 ((E : ℂ) + γ * m) * m) • geomC (freeRho 1 ((E : ℂ) + γ * m) ^ 2) L +
        (2 * γ * freeT 1 ((E : ℂ) + γ * m) ^ 2 * freeRho 1 ((E : ℂ) + γ * m) ^ L /
          (1 - freeRho 1 ((E : ℂ) + γ * m) ^ L) ^ 2) • lgJ L := by
  have hlt : ‖freeRho 1 ((E : ℂ) + γ * m)‖ ^ L < 1 :=
    pow_lt_one₀ (norm_nonneg _) (h.rho_lt h.hm) (by have := h.hL; omega)
  have hm := h.m_eq
  rw [h.dysonMat_eq]
  generalize freeRho 1 ((E : ℂ) + γ * m) = ρ at hlt hm ⊢
  generalize freeT 1 ((E : ℂ) + γ * m) = f at hm ⊢
  have hD : 1 - ρ ^ L ≠ 0 := by
    intro h0
    have : ρ ^ L = 1 := by linear_combination -h0
    rw [← norm_pow, this, norm_one] at hlt; exact lt_irrefl _ hlt
  have hD' : 1 + ρ ^ L ≠ 0 := by
    intro h0
    have : ρ ^ L = -1 := by linear_combination h0
    rw [← norm_pow, this, norm_neg, norm_one] at hlt; exact lt_irrefl _ hlt
  ext a c
  simp only [pairQ, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, geomC,
    Matrix.add_apply, lgJ, mul_one]
  have hx : lgD L a c ≤ L := (lgD_lt a c).le
  generalize lgD L a c = x at hx ⊢
  unfold geomV
  have e1 : ρ ^ x * ρ ^ (L - x) = ρ ^ L := by rw [← pow_add]; congr 1; omega
  have e2 : (ρ ^ 2) ^ x = ρ ^ x * ρ ^ x := by rw [← pow_mul, ← pow_add]; congr 1; ring
  have e3 : (ρ ^ 2) ^ (L - x) = ρ ^ (L - x) * ρ ^ (L - x) := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  have e4 : (ρ ^ 2) ^ L = ρ ^ L * ρ ^ L := by rw [← pow_mul, ← pow_add]; congr 1; ring
  rw [e2, e3, e4]
  have hD2 : 1 - ρ ^ L * ρ ^ L ≠ 0 := by
    have : 1 - ρ ^ L * ρ ^ L = (1 - ρ ^ L) * (1 + ρ ^ L) := by ring
    rw [this]; exact mul_ne_zero hD hD'
  rw [hm]
  rw [← e1] at hD hD2 ⊢
  generalize ρ ^ x = u at hD hD2 ⊢
  generalize ρ ^ (L - x) = v at hD hD2 ⊢
  have hD3 : 1 - u ^ 2 * v ^ 2 ≠ 0 := by
    intro h0; apply hD2; linear_combination h0
  field_simp
  ring

end LgGood

private lemma lg_sq_facts {w : ℂ} (hw : 0 < w.im) :
    freeRho 1 w ^ 2 + (freeRho 1 w ^ 2)⁻¹ = w ^ 2 - 2 ∧
      (freeRho 1 w ^ 2)⁻¹ - freeRho 1 w ^ 2 = freeS 1 w * w ∧
      1 + freeRho 1 w ^ 2 = freeRho 1 w * w ∧ 1 - freeRho 1 w ^ 2 = freeRho 1 w * freeS 1 w := by
  have h0 := lg_rho_ne hw
  have h1 := lg_rho_add_inv hw
  have h2 := lg_rho_inv_sub hw
  set ρ := freeRho 1 w
  have hi : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ h0
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← inv_pow, ← h1]; linear_combination (-2 : ℂ) * hi
  · rw [← inv_pow]
    have e : ρ⁻¹ ^ 2 - ρ ^ 2 = (ρ⁻¹ - ρ) * (ρ + ρ⁻¹) := by ring
    rw [e, h2, h1]
  · rw [← h1]; linear_combination (-1 : ℂ) * hi
  · rw [← h2]; linear_combination (-1 : ℂ) * hi

/-- The auxiliary energy `v` with `v² = w w'`. -/
private lemma lg_aux_v {k : ℝ} (w w' : ℂ) (hw : 0 < w.im) (hww : w.im ≤ w'.im)
    (hwn : ‖w‖ ≤ 2 - k) (hw'n : ‖w'‖ ≤ 2 - k) :
    ∃ v : ℂ, v ^ 2 = w * w' ∧ w.im ≤ v.im ∧ ‖v‖ ≤ 2 - k ∧ ‖v‖ ^ 2 = ‖w‖ * ‖w'‖ := by
  obtain ⟨v, hv2, hv0⟩ := lg_exists_sqrt_upper (w * w')
  have hvim2 := lg_sqrt_im_sq w w' v hv2
  have hvn2 : ‖v‖ ^ 2 = ‖w‖ * ‖w'‖ := by rw [← norm_pow, hv2, norm_mul]
  refine ⟨v, hv2, ?_, ?_, hvn2⟩
  · have h1 : w.im * w.im ≤ w.im * w'.im := mul_le_mul_of_nonneg_left hww hw.le
    have : w.im ^ 2 ≤ v.im ^ 2 := by rw [sq]; linarith
    exact (pow_le_pow_iff_left₀ hw.le hv0 (by norm_num)).mp this
  · have h2k : 0 ≤ 2 - k := le_trans (norm_nonneg _) hwn
    have : ‖v‖ ^ 2 ≤ (2 - k) ^ 2 := by
      rw [hvn2, sq]
      exact mul_le_mul hwn hw'n (norm_nonneg _) h2k
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) h2k (by norm_num)).mp this

/-- `‖w‖ ≤ (128/k²)‖w + tγm‖`. -/
private lemma lg_w_le_w' {k γ t : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) (hγ : 0 < γ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (w m : ℂ) (hmn : ‖m‖ ≤ 2 / k) (hwlo : γ * (k / 32) ≤ w.im)
    (hm0 : 0 ≤ m.im) :
    ‖w‖ ≤ 128 / k ^ 2 * ‖w + ((t * γ : ℝ) : ℂ) * m‖ := by
  set w' := w + ((t * γ : ℝ) : ℂ) * m with hw'
  have hw'im : w.im ≤ w'.im := by
    have : w'.im = w.im + t * γ * m.im := by simp [hw']
    rw [this]; have : 0 ≤ t * γ * m.im := by positivity
    linarith
  have hw'lo : γ * (k / 32) ≤ ‖w'‖ := le_trans (le_trans hwlo hw'im) (Complex.im_le_norm _)
  have hγm : t * γ * ‖m‖ ≤ γ * ‖m‖ := by
    have := mul_le_mul_of_nonneg_right ht1 (mul_nonneg hγ.le (norm_nonneg m)); linarith
  by_cases hc : 2 * γ * ‖m‖ ≤ ‖w‖
  · have h1 : ‖w‖ - γ * ‖m‖ ≤ ‖w'‖ := by
      have := norm_sub_le w' (((t * γ : ℝ) : ℂ) * m)
      have e2 : w' - ((t * γ : ℝ) : ℂ) * m = w := by rw [hw']; ring
      rw [e2, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at this
      linarith
    have h128 : 2 ≤ 128 / k ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have : k ^ 2 ≤ 1 := by nlinarith
      linarith
    have h2 : ‖w‖ ≤ 2 * ‖w'‖ := by linarith
    calc ‖w‖ ≤ 2 * ‖w'‖ := h2
      _ ≤ 128 / k ^ 2 * ‖w'‖ := mul_le_mul_of_nonneg_right h128 (norm_nonneg _)
  · rw [not_le] at hc
    have hm2 : γ * ‖m‖ ≤ γ * (2 / k) := mul_le_mul_of_nonneg_left hmn hγ.le
    have h1 : ‖w‖ ≤ 4 * γ / k := by
      have : 2 * γ * ‖m‖ ≤ 4 * γ / k := by
        have e : 4 * γ / k = 2 * (γ * (2 / k)) := by ring
        rw [e]; linarith
      linarith
    calc ‖w‖ ≤ 4 * γ / k := h1
      _ = 128 / k ^ 2 * (γ * (k / 32)) := by field_simp; ring
      _ ≤ 128 / k ^ 2 * ‖w'‖ := mul_le_mul_of_nonneg_left hw'lo (by positivity)

/-- `‖tγmw/(s v)‖ ≤ 23γ/k³` when `‖v‖² = ‖w‖ ‖w'‖`, `‖w‖ ≤ (128/k²)‖w'‖`. -/
private lemma lg_B_le {k γ t : ℝ} (hk : 0 < k) (hγ : 0 < γ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (m w w' v sv : ℂ) (hmn : ‖m‖ ≤ 2 / k) (hsv : k ≤ ‖sv‖) (hv0 : v ≠ 0)
    (hvn2 : ‖v‖ ^ 2 = ‖w‖ * ‖w'‖) (hwK : ‖w‖ ≤ 128 / k ^ 2 * ‖w'‖) :
    ‖(t : ℂ) * γ * m * w / (sv * v)‖ ≤ 23 * γ / k ^ 3 := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hsq : ‖w‖ ^ 2 ≤ 128 / k ^ 2 * ‖v‖ ^ 2 := by
    rw [hvn2, sq]
    calc ‖w‖ * ‖w‖ ≤ ‖w‖ * (128 / k ^ 2 * ‖w'‖) := mul_le_mul_of_nonneg_left hwK (norm_nonneg _)
      _ = 128 / k ^ 2 * (‖w‖ * ‖w'‖) := by ring
  rw [norm_div, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real,
    Complex.norm_real, Real.norm_of_nonneg ht0, Real.norm_of_nonneg hγ.le,
    div_le_iff₀ (mul_pos (lt_of_lt_of_le hk hsv) hvpos)]
  have hB2 : (t * γ * ‖m‖ * ‖w‖) ^ 2 ≤ (23 * γ / k ^ 3 * (‖sv‖ * ‖v‖)) ^ 2 := by
    have ht2 : t ^ 2 ≤ 1 := by nlinarith
    have hm2 : ‖m‖ ^ 2 ≤ (2 / k) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hmn 2
    have h1 : (t * γ * ‖m‖ * ‖w‖) ^ 2 ≤ 1 * γ ^ 2 * (2 / k) ^ 2 * (128 / k ^ 2 * ‖v‖ ^ 2) := by
      rw [mul_pow, mul_pow, mul_pow]
      gcongr
    have h2 : 1 * γ ^ 2 * (2 / k) ^ 2 * (128 / k ^ 2 * ‖v‖ ^ 2) ≤
        (23 * γ / k ^ 3 * (k * ‖v‖)) ^ 2 := by
      rw [show 1 * γ ^ 2 * (2 / k) ^ 2 * (128 / k ^ 2 * ‖v‖ ^ 2) = 512 * (γ ^ 2 * ‖v‖ ^ 2 / k ^ 4)
          by
        field_simp; ring, show (23 * γ / k ^ 3 * (k * ‖v‖)) ^ 2 = 529 * (γ ^ 2 * ‖v‖ ^ 2 / k ^ 4) by
        field_simp; ring]
      have : 0 ≤ γ ^ 2 * ‖v‖ ^ 2 / k ^ 4 := by positivity
      linarith
    have h3 : (23 * γ / k ^ 3 * (k * ‖v‖)) ^ 2 ≤ (23 * γ / k ^ 3 * (‖sv‖ * ‖v‖)) ^ 2 := by
      gcongr
    linarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp hB2

private lemma lg_one_sub_pow_ne {τ : ℂ} (h : ‖τ‖ < 1) {L : ℕ} (hL : L ≠ 0) : 1 - τ ^ L ≠ 0 := by
  intro h0
  have h2 : ‖τ‖ ^ L < 1 := pow_lt_one₀ (norm_nonneg _) h hL
  have : τ ^ L = 1 := by linear_combination -h0
  rw [← norm_pow, this, norm_one] at h2; exact lt_irrefl _ h2

namespace LgGood

variable {k γ E : ℝ} {L : ℕ} {m mInf : ℂ} (h : LgGood k γ E L m mInf)
include h

set_option maxHeartbeats 1000000 in
-- the many explicit estimates of this proof exceed the default heartbeat limit
/-- The explicit form of `(I - tQ)⁻¹` with bounds on its three coefficients. -/
private lemma stable_formula [NeZero L] (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ τ B κ : ℂ, (1 - (t : ℂ) • pairQ γ (dysonMat 1 γ L E m))⁻¹ =
        1 + B • geomC τ L + κ • lgJ L ∧ ‖τ‖ ≤ Real.exp (-(γ * k / 512)) ∧
      ‖B‖ ≤ 23 * γ / k ^ 3 ∧ ‖κ‖ ≤ 753680 * γ * Real.exp (-(k / 1024 * (γ * L))) / k ^ 6 := by
  have hk := h.hk
  have hk1 := h.hk1
  have hγ := h.hγ
  have hL := h.hL
  obtain ⟨hmI, hmn, hwp, hwlo, -, -, hwre, hw3⟩ := h.wf h.hm
  obtain ⟨hσsum, hσdiff, hσp, hσm⟩ := lg_sq_facts hwp
  have hρlt := h.rho_lt h.hm
  have hρL := h.rho_pow_le h.hm
  have hfle := h.f_le h.hm
  have hfs := lg_f_mul_s hwp
  have hρ0 := lg_rho_ne hwp
  have hswk := lg_norm_s_ge_k hk hk1 hwp hwre
  have hsw0 := lg_s_ne hwp
  have hZq := h.exp_aH_half
  have htail := h.htail
  have hQ := h.pairQ_eq
  set w : ℂ := (E : ℂ) + γ * m with hwdef
  set ρ := freeRho 1 w
  set f := freeT 1 w
  set sw := freeS 1 w
  set Z := Real.exp (-(k / 1024 * (γ * L))) with hZ
  have hZ0 : 0 ≤ Z := (Real.exp_pos _).le
  -- `σ = ρ²`
  have hσn : ‖ρ ^ 2‖ < 1 := by
    rw [norm_pow]; have := norm_nonneg ρ; nlinarith
  have hσ0 : ρ ^ 2 ≠ 0 := pow_ne_zero 2 hρ0
  have hσ1 : ρ ^ 2 ≠ 1 := by intro h1; rw [h1, norm_one] at hσn; exact lt_irrefl _ hσn
  have hσL : 1 - (ρ ^ 2) ^ L ≠ 0 := lg_one_sub_pow_ne hσn (by omega)
  have hw0 : w ≠ 0 := by intro h0; rw [h0] at hwp; simp at hwp
  have hστ : (ρ ^ 2)⁻¹ - ρ ^ 2 ≠ 0 := by rw [hσdiff]; exact mul_ne_zero hsw0 hw0
  -- the auxiliary energy
  set w' : ℂ := w + ((t * γ : ℝ) : ℂ) * m with hw'def
  have hm0 : 0 ≤ m.im := by linarith
  have hww : w.im ≤ w'.im := by
    have : w'.im = w.im + t * γ * m.im := by simp [hw'def]
    rw [this]; have : 0 ≤ t * γ * m.im := by positivity
    linarith
  have hγm : γ * ‖m‖ ≤ 2 * γ / k := by
    have := mul_le_mul_of_nonneg_left hmn hγ.le; linarith [show γ * (2 / k) = 2 * γ / k by ring]
  have h4γ : 4 * γ / k ≤ k := by
    rw [div_le_iff₀ hk]
    have : k ^ 5 ≤ k ^ 2 := pow_le_pow_of_le_one hk.le hk1 (by norm_num)
    have := h.hγ0
    nlinarith
  have hwn : ‖w‖ ≤ 2 - 2 * k + 2 * γ / k := by
    calc ‖w‖ ≤ ‖(E : ℂ)‖ + ‖(γ : ℂ) * m‖ := norm_add_le _ _
      _ = |E| + γ * ‖m‖ := by simp [abs_of_pos hγ]
      _ ≤ _ := by linarith [h.hE]
  have htγm : t * γ * ‖m‖ ≤ γ * ‖m‖ := by
    have := mul_le_mul_of_nonneg_right ht1 (mul_nonneg hγ.le (norm_nonneg m)); linarith
  have hw'n : ‖w'‖ ≤ 2 - 2 * k + 4 * γ / k := by
    calc ‖w'‖ ≤ ‖w‖ + ‖((t * γ : ℝ) : ℂ) * m‖ := norm_add_le _ _
      _ = ‖w‖ + t * γ * ‖m‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      _ ≤ _ := by linarith [show (4 : ℝ) * γ / k = 2 * γ / k + 2 * γ / k by ring]
  have hwn' : ‖w‖ ≤ 2 - k := by linarith [show (4 : ℝ) * γ / k = 2 * γ / k + 2 * γ / k by ring]
  have hw'n' : ‖w'‖ ≤ 2 - k := by linarith
  obtain ⟨v, hv2, hvim, hvn, hvn2⟩ := lg_aux_v w w' hwp hww hwn' hw'n'
  have hvp : 0 < v.im := lt_of_lt_of_le hwp hvim
  have hvre : |v.re| ≤ 2 - k := (Complex.abs_re_le_norm v).trans hvn
  have hv3 : ‖v‖ ≤ 3 := by linarith
  obtain ⟨hτsum, hτdiff, -, -⟩ := lg_sq_facts hvp
  have hζ0 := lg_rho_ne hvp
  have hgapv := lg_gap_ge hvp hv3
  have hsvk := lg_norm_s_ge_k hk hk1 hvp hvre
  have hsv0 := lg_s_ne hvp
  have hv0 : v ≠ 0 := by intro h0; rw [h0] at hvp; simp at hvp
  set ζ := freeRho 1 v
  set sv := freeS 1 v
  have hτn : ‖ζ ^ 2‖ ≤ Real.exp (-(γ * k / 512)) := by
    rw [norm_pow]
    have h1 : ‖ζ‖ ^ 2 ≤ 1 - γ * k / 512 := by
      have : γ * (k / 32) / 16 ≤ v.im / 16 := by linarith
      linarith
    have := Real.add_one_le_exp (-(γ * k / 512))
    linarith
  have hτlt : ‖ζ ^ 2‖ < 1 := by
    refine lt_of_le_of_lt hτn ?_
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by have := h.b_pos; linarith)
  have hτ0 : ζ ^ 2 ≠ 0 := pow_ne_zero 2 hζ0
  have hτ1 : ζ ^ 2 ≠ 1 := by intro h1; rw [h1, norm_one] at hτlt; exact lt_irrefl _ hτlt
  have hτL : 1 - (ζ ^ 2) ^ L ≠ 0 := lg_one_sub_pow_ne hτlt (by omega)
  have hτd0 : (ζ ^ 2)⁻¹ - ζ ^ 2 ≠ 0 := by rw [hτdiff]; exact mul_ne_zero hsv0 hv0
  -- coefficients
  set α : ℂ := γ * f * m with hα
  set β : ℂ := 2 * γ * f ^ 2 * ρ ^ L / (1 - ρ ^ L) ^ 2 with hβ
  set B : ℂ := (t : ℂ) * α * ((ρ ^ 2)⁻¹ - ρ ^ 2) / ((ζ ^ 2)⁻¹ - ζ ^ 2) with hBdef
  have hM3 : ρ ^ 2 + (ρ ^ 2)⁻¹ - (t : ℂ) * α * ((ρ ^ 2)⁻¹ - ρ ^ 2) = ζ ^ 2 + (ζ ^ 2)⁻¹ := by
    rw [hσsum, hσdiff, hτsum, hv2, hα, hw'def]
    push_cast
    linear_combination (-(t : ℂ) * γ * m * w) * hfs
  have hB : B * ((ζ ^ 2)⁻¹ - ζ ^ 2) = (t : ℂ) * α * ((ρ ^ 2)⁻¹ - ρ ^ 2) := by
    rw [hBdef, div_mul_cancel₀ _ hτd0]
  have hαgσ : ‖(t : ℂ) * α * ((1 + ρ ^ 2) / (1 - ρ ^ 2))‖ ≤ 1 / 4 := by
    rw [hσp, hσm]
    have e : (t : ℂ) * α * (ρ * w / (ρ * sw)) = (t : ℂ) * γ * f * m * w / sw := by
      rw [hα]; field_simp
    rw [e, norm_div, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg ht0, Real.norm_of_nonneg hγ.le, div_le_iff₀ (by linarith)]
    have h1 : t * γ * ‖f‖ * ‖m‖ * ‖w‖ ≤ 1 * γ * (1 / k) * (2 / k) * 3 := by gcongr
    have h6 : 1 * γ * (1 / k) * (2 / k) * 3 ≤ 1 / 4 * k := by
      rw [show 1 * γ * (1 / k) * (2 / k) * 3 = 6 * γ / k ^ 2 by field_simp; ring,
        div_le_iff₀ (by positivity)]
      have : k ^ 5 ≤ k ^ 3 := pow_le_pow_of_le_one hk.le hk1 (by norm_num)
      have := h.hγ0
      nlinarith
    have h7 : 1 / 4 * k ≤ 1 / 4 * ‖sw‖ := by linarith
    linarith
  have hβn : ‖β‖ ≤ 8 * γ * Z / k ^ 2 := by
    rw [hβ]
    have h1 : 1 / 2 ≤ ‖1 - ρ ^ L‖ := by
      have := norm_sub_norm_le (1 : ℂ) (ρ ^ L); rw [norm_pow] at this; simp at this; linarith
    have h14 : 1 / 4 ≤ ‖1 - ρ ^ L‖ ^ 2 := by
      have := mul_le_mul h1 h1 (by norm_num) (norm_nonneg _); rw [sq]; linarith
    simp only [norm_div, norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg hγ.le,
      Complex.norm_ofNat]
    rw [div_le_iff₀ (by positivity)]
    have hf2 : ‖f‖ ^ 2 ≤ 1 / k ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg f) hfle 2; rwa [div_pow, one_pow] at this
    calc 2 * γ * ‖f‖ ^ 2 * ‖ρ‖ ^ L ≤ 2 * γ * (1 / k ^ 2) * Z := by gcongr
      _ = 8 * γ * Z / k ^ 2 * (1 / 4) := by field_simp; ring
      _ ≤ 8 * γ * Z / k ^ 2 * ‖1 - ρ ^ L‖ ^ 2 := by gcongr
  have hβL : ‖(t : ℂ) * β * L‖ ≤ 1 / 32 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0, Complex.norm_natCast]
    have h1 : t * ‖β‖ * L ≤ 1 * (8 * γ * Z / k ^ 2) * L := by gcongr
    have h2 : (8 * γ * Z / k ^ 2) * L ≤ 8 / k ^ 2 * ((1 + γ * L) * Z) := by
      rw [show (8 * γ * Z / k ^ 2) * L = 8 / k ^ 2 * (γ * L * Z) by ring]
      gcongr; linarith
    have h3 : 8 / k ^ 2 * ((1 + γ * L) * Z) ≤ 8 / k ^ 2 * (k ^ 2 / 256) := by gcongr
    have h4 : 8 / k ^ 2 * (k ^ 2 / 256) = 1 / 32 := by field_simp; norm_num
    linarith
  have hden : 1 / 2 ≤ ‖1 - (t : ℂ) * α * ((1 + ρ ^ 2) / (1 - ρ ^ 2)) - (t : ℂ) * β * L‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) ((t : ℂ) * α * ((1 + ρ ^ 2) / (1 - ρ ^ 2)))
    have h2 := norm_sub_norm_le (1 - (t : ℂ) * α * ((1 + ρ ^ 2) / (1 - ρ ^ 2))) ((t : ℂ) * β * L)
    rw [norm_one] at h1
    linarith
  have hden0 : 1 - (t : ℂ) * α * ((1 + ρ ^ 2) / (1 - ρ ^ 2)) - (t : ℂ) * β * L ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hden; norm_num at hden
  -- `B`
  have hBn : ‖B‖ ≤ 23 * γ / k ^ 3 := by
    have e : B = -((t : ℂ) * γ * m * w / (sv * v)) := by
      rw [hBdef, hσdiff, hτdiff, hα, ← neg_div]
      congr 1
      linear_combination ((t : ℂ) * γ * m * w) * hfs
    rw [e, norm_neg]
    exact lg_B_le hk hγ ht0 ht1 m w w' v sv hmn hsvk hv0 hvn2
      (lg_w_le_w' hk hk1 hγ ht0 ht1 w m hmn hwlo hm0)
  -- `κ`
  have hgτ : ‖(1 + ζ ^ 2) / (1 - ζ ^ 2)‖ ≤ 2048 / (γ * k) := by
    have hb := h.b_pos
    have hgk : γ * k ≤ 1 := by
      have := mul_le_mul h.γ1 hk1 hk.le zero_le_one; linarith
    have h1 : γ * k / 1024 ≤ 1 - ‖ζ ^ 2‖ := by
      have := lg_one_sub_exp_neg (γ * k / 512) (by positivity) (by linarith)
      linarith
    have h2 : 1 - ‖ζ ^ 2‖ ≤ ‖1 - ζ ^ 2‖ := by
      have := norm_sub_norm_le (1 : ℂ) (ζ ^ 2); rw [norm_one] at this; exact this
    have h3 : ‖1 + ζ ^ 2‖ ≤ 2 := by
      have := norm_add_le (1 : ℂ) (ζ ^ 2); rw [norm_one] at this; linarith
    rw [norm_div, div_le_div_iff₀ (by linarith) (by positivity)]
    have h4 : 2 * (γ * k) ≤ 2048 * ‖1 - ζ ^ 2‖ := by linarith
    have h5 : ‖1 + ζ ^ 2‖ * (γ * k) ≤ 2 * (γ * k) :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    linarith
  have h1B : ‖1 + B * ((1 + ζ ^ 2) / (1 - ζ ^ 2))‖ ≤ 47105 / k ^ 4 := by
    have h1 := norm_add_le (1 : ℂ) (B * ((1 + ζ ^ 2) / (1 - ζ ^ 2)))
    rw [norm_one, norm_mul] at h1
    have h2 : ‖B‖ * ‖(1 + ζ ^ 2) / (1 - ζ ^ 2)‖ ≤ 23 * γ / k ^ 3 * (2048 / (γ * k)) :=
      mul_le_mul hBn hgτ (norm_nonneg _) (by positivity)
    have h3 : 23 * γ / k ^ 3 * (2048 / (γ * k)) = 47104 / k ^ 4 := by field_simp; ring
    have h4 : 1 ≤ 1 / k ^ 4 := by
      rw [le_div_iff₀ (by positivity)]
      have : k ^ 4 ≤ 1 := pow_le_one₀ hk.le hk1
      linarith
    have e : 47105 / k ^ 4 = 47104 / k ^ 4 + 1 / k ^ 4 := by ring
    linarith
  set κ : ℂ := (t : ℂ) * β * (1 + B * ((1 + ζ ^ 2) / (1 - ζ ^ 2))) /
    (1 - (t : ℂ) * α * ((1 + ρ ^ 2) / (1 - ρ ^ 2)) - (t : ℂ) * β * L) with hκ
  have hκn : ‖κ‖ ≤ 753680 * γ * Z / k ^ 6 := by
    rw [hκ, norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0,
      div_le_iff₀ (by linarith)]
    have h1 : t * ‖β‖ * ‖1 + B * ((1 + ζ ^ 2) / (1 - ζ ^ 2))‖ ≤
        1 * (8 * γ * Z / k ^ 2) * (47105 / k ^ 4) := by gcongr
    have h2 : 1 * (8 * γ * Z / k ^ 2) * (47105 / k ^ 4) = 753680 * γ * Z / k ^ 6 * (1 / 2) := by
      field_simp; ring
    have h3 : 753680 * γ * Z / k ^ 6 * (1 / 2) ≤ 753680 * γ * Z / k ^ 6 *
        ‖1 - (t : ℂ) * α * ((1 + ρ ^ 2) / (1 - ρ ^ 2)) - (t : ℂ) * β * L‖ :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    linarith
  refine ⟨ζ ^ 2, B, κ, ?_, hτn, hBn, hκn⟩
  rw [hQ]
  exact lg_stable_inv hL (ρ ^ 2) (ζ ^ 2) α β B t hσ0 hσL hσ1 hτ0 hτL hτ1 hστ hM3 hB hden0

end LgGood

private lemma lg_geomV_le_q (τ : ℂ) (q : ℝ) (hq0 : 0 ≤ q) (hτ : ‖τ‖ ≤ q) {L : ℕ} (hqL : q ^ L ≤ 1 /
    4)
    (x : ℕ) : ‖geomV τ L x‖ ≤ 4 / 3 * (q ^ x + q ^ (L - x)) := by
  unfold geomV
  have h1 : 3 / 4 ≤ ‖1 - τ ^ L‖ := by
    have := norm_sub_norm_le (1 : ℂ) (τ ^ L)
    rw [norm_one, norm_pow] at this
    have : ‖τ‖ ^ L ≤ q ^ L := pow_le_pow_left₀ (norm_nonneg _) hτ L
    linarith
  rw [norm_div, div_le_iff₀ (by linarith)]
  have h2 : ‖τ ^ x + τ ^ (L - x)‖ ≤ q ^ x + q ^ (L - x) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_pow, norm_pow]
    gcongr
  have h3 : 0 ≤ q ^ x + q ^ (L - x) := by positivity
  have h4 : 4 / 3 * (q ^ x + q ^ (L - x)) * (3 / 4) ≤ 4 / 3 * (q ^ x + q ^ (L - x)) * ‖1 - τ ^ L‖ :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  linarith

private lemma lg_row_const {L : ℕ} (a : Fin L) (μ : ℝ) (hμ0 : 0 ≤ μ) :
    ∑ c : Fin L, Real.exp (μ * cycDist a c) ≤ L * Real.exp (μ * L / 2) := by
  have : ∀ c : Fin L, Real.exp (μ * cycDist a c) ≤ Real.exp (μ * L / 2) := by
    intro c
    apply Real.exp_le_exp.mpr
    have := cycDist_le_half a c
    have : (2 * cycDist a c : ℕ) ≤ (L : ℝ) := by exact_mod_cast this
    push_cast at this
    nlinarith
  refine (Finset.sum_le_sum fun c _ => this c).trans (le_of_eq ?_)
  simp

namespace LgGood

variable {k γ E : ℝ} {L : ℕ} {m mInf : ℂ} (h : LgGood k γ E L m mInf)
include h

/-- Weighted geometric rows at the rate `γk/512`, for weights `μ ≤ γk/2048`. -/
private lemma row_q (a : Fin L) (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ : μ ≤ γ * k / 2048) :
    ∑ c, Real.exp (μ * cycDist a c) *
        (Real.exp (-(γ * k / 512)) ^ lgD L a c + Real.exp (-(γ * k / 512)) ^ (L - lgD L a c)) ≤
      4096 / (γ * k) := by
  have hk := h.hk
  have hγ := h.hγ
  have hb0 := h.b_pos
  have hgk : γ * k ≤ 1 := by have := mul_le_mul h.γ1 h.hk1 hk.le zero_le_one; linarith
  set s := Real.exp (-(γ * k / 512)) with hsdef
  have hs0 : 0 ≤ s := (Real.exp_pos _).le
  have hμs : Real.exp μ * s ≤ Real.exp (-(3 * γ * k / 2048)) := by
    rw [hsdef, ← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have hgap : γ * k / 2048 ≤ 1 - Real.exp μ * s := by
    have h1 := lg_one_sub_exp_neg (3 * γ * k / 2048) (by positivity) (by linarith)
    linarith
  have hμs1 : Real.exp μ * s < 1 := by linarith
  refine (lg_row_geom a μ s hμ0 hs0 hμs1).trans ?_
  rw [div_le_div_iff₀ (by linarith) (by positivity)]
  linarith

/-- (A.16) [uvp:eq:stable]: weighted rows of the same-sign inverse `(I - tQ)⁻¹`. -/
private lemma stable_row [NeZero L] (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (a : Fin L) (μ : ℝ)
    (hμ0 : 0 ≤ μ) (hμ : μ ≤ γ * k / 2048) :
    ∑ c, Real.exp (μ * cycDist a c) * ‖(1 - (t : ℂ) • pairQ γ (dysonMat 1 γ L E m))⁻¹ a c‖ ≤
      3000000000 / k ^ 7 := by
  obtain ⟨τ, B, κ, hV, hτ, hB, hκ⟩ := h.stable_formula t ht0 ht1
  rw [hV]
  have hk := h.hk
  have hk1 := h.hk1
  have hγ := h.hγ
  obtain ⟨-, -, hsL, -, -⟩ := h.s_facts
  set s := Real.exp (-(γ * k / 512)) with hsdef
  set Z := Real.exp (-(k / 1024 * (γ * L))) with hZ
  have hs0 : 0 ≤ s := (Real.exp_pos _).le
  have hpt : ∀ c, Real.exp (μ * cycDist a c) * ‖(1 + B • geomC τ L + κ • lgJ L) a c‖ ≤
      Real.exp (μ * cycDist a c) * ‖(1 : Matrix (Fin L) (Fin L) ℂ) a c‖ +
        ‖B‖ * (4 / 3) * (Real.exp (μ * cycDist a c) * (s ^ lgD L a c + s ^ (L - lgD L a c))) +
        ‖κ‖ * Real.exp (μ * cycDist a c) := by
    intro c
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, geomC, lgJ, Matrix.of_apply,
      mul_one]
    have h1 := norm_add₃_le (a := (1 : Matrix (Fin L) (Fin L) ℂ) a c)
      (b := B * geomV τ L (lgD L a c)) (c := κ)
    rw [norm_mul] at h1
    have h2 := lg_geomV_le_q τ s hs0 hτ hsL (lgD L a c)
    have he := (Real.exp_pos (μ * cycDist a c)).le
    calc Real.exp (μ * cycDist a c) * ‖(1 : Matrix (Fin L) (Fin L) ℂ) a c +
          B * geomV τ L (lgD L a c) + κ‖
        ≤ Real.exp (μ * cycDist a c) * (‖(1 : Matrix (Fin L) (Fin L) ℂ) a c‖ +
          ‖B‖ * (4 / 3 * (s ^ lgD L a c + s ^ (L - lgD L a c))) + ‖κ‖) := by
          gcongr
          exact h1.trans (by gcongr)
      _ = _ := by ring
  refine (Finset.sum_le_sum fun c _ => hpt c).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hid : ∑ c, Real.exp (μ * cycDist a c) * ‖(1 : Matrix (Fin L) (Fin L) ℂ) a c‖ = 1 := by
    rw [Finset.sum_eq_single a]
    · simp [cycDist]
    · intro c _ hc; simp [Matrix.one_apply_ne' hc]
    · simp
  rw [hid]
  have hrq := h.row_q a μ hμ0 hμ
  have hrc := lg_row_const a μ hμ0
  have hb1 : ‖B‖ * (4 / 3) * ∑ c, Real.exp (μ * cycDist a c) *
      (s ^ lgD L a c + s ^ (L - lgD L a c)) ≤ 125611 / k ^ 4 := by
    calc ‖B‖ * (4 / 3) * ∑ c, Real.exp (μ * cycDist a c) * (s ^ lgD L a c + s ^ (L - lgD L a c))
        ≤ 23 * γ / k ^ 3 * (4 / 3) * (4096 / (γ * k)) := by gcongr
      _ = 376832 / 3 / k ^ 4 := by field_simp; ring
      _ ≤ 125611 / k ^ 4 := by gcongr; norm_num
  have hZμ : Z * Real.exp (μ * L / 2) ≤ Real.exp (-(3 * k / 4096 * (γ * L))) := by
    rw [hZ, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : μ * L ≤ γ * k / 2048 * L := by gcongr
    nlinarith
  have hH0 : 0 ≤ γ * L := by positivity
  have htb := lg_tail_bound (3 * k / 4096) (γ * L) (by positivity) hH0
  have hb2 : ‖κ‖ * ∑ c : Fin L, Real.exp (μ * cycDist a c) ≤
      753680 / k ^ 6 * (1 + 2 / (3 * k / 4096)) := by
    calc ‖κ‖ * ∑ c : Fin L, Real.exp (μ * cycDist a c)
        ≤ 753680 * γ * Z / k ^ 6 * (L * Real.exp (μ * L / 2)) := by gcongr
      _ = 753680 / k ^ 6 * ((γ * L) * (Z * Real.exp (μ * L / 2))) := by ring
      _ ≤ 753680 / k ^ 6 * ((γ * L) * Real.exp (-(3 * k / 4096 * (γ * L)))) := by gcongr
      _ ≤ 753680 / k ^ 6 * (1 + 2 / (3 * k / 4096)) := by gcongr
  have hfin : 1 + 125611 / k ^ 4 + 753680 / k ^ 6 * (1 + 2 / (3 * k / 4096)) ≤
      3000000000 / k ^ 7 := by
    have hk7 : 0 < k ^ 7 := by positivity
    have e : 1 + 125611 / k ^ 4 + 753680 / k ^ 6 * (1 + 2 / (3 * k / 4096)) =
        (k ^ 7 + 125611 * k ^ 3 + 753680 * k + 753680 * 8192 / 3) / k ^ 7 := by
      field_simp; ring
    rw [e]
    gcongr
    have : k ^ 7 ≤ 1 := pow_le_one₀ hk.le hk1
    have : k ^ 3 ≤ 1 := pow_le_one₀ hk.le hk1
    nlinarith
  linarith

end LgGood

private lemma lg_hopB_eq {g : ℝ} (hg : 1 ≤ g) : hopB g = 1 := by
  unfold hopB; rw [max_eq_right hg, div_self (by linarith)]

private lemma lg_gammaG_eq {g : ℝ} (hg : 1 ≤ g) : gammaG g = (g ^ 2)⁻¹ := by
  unfold gammaG; rw [max_eq_right hg]

/-- Uniform large-coupling setting: for `g ≥ 1000/(κ/2)⁵` and `L ≥ R g²`, the solutions exist and
every pair of solutions satisfies `LgGood`. -/
private lemma lg_setup {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ R : ℝ, 3 ≤ R ∧ ∀ g : ℝ, 1000 / (κ / 2) ^ 5 ≤ g → ∀ L : ℕ, R * g ^ 2 ≤ L →
      ∀ E : ℝ, |E| ≤ 2 - κ →
      1 ≤ g ∧ hopB g = 1 ∧ gammaG g = (g ^ 2)⁻¹ ∧
      (∃ m : ℂ, IsDysonRootV 1 (g ^ 2)⁻¹ L E m) ∧
      (∃ mInf : ℂ, 0 < mInf.im ∧ mInf = freeT 1 ((E : ℂ) + ((g ^ 2)⁻¹ : ℝ) * mInf)) ∧
      ∀ m mInf : ℂ, IsDysonRootV 1 (g ^ 2)⁻¹ L E m → 0 < mInf.im →
        mInf = freeT 1 ((E : ℂ) + ((g ^ 2)⁻¹ : ℝ) * mInf) → LgGood (κ / 2) (g ^ 2)⁻¹ E L m mInf :=
            by
  have hk : 0 < κ / 2 := by linarith
  have hk1 : κ / 2 ≤ 1 := by linarith
  obtain ⟨R, hR3, hR⟩ := lg_core hk hk1
  refine ⟨R, hR3, fun g hg L hL E hE => ?_⟩
  have hk5 : (κ / 2) ^ 5 ≤ 1 := pow_le_one₀ hk.le hk1
  have hg1 : 1 ≤ g := by
    have : 1 ≤ 1000 / (κ / 2) ^ 5 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  have hg0 : 0 < g := by linarith
  set γ : ℝ := (g ^ 2)⁻¹ with hγdef
  have hγ : 0 < γ := by positivity
  have hγ0 : γ ≤ (κ / 2) ^ 5 / 1000 := by
    rw [hγdef]
    have hg2 : g ≤ g ^ 2 := by nlinarith
    have : 1000 / (κ / 2) ^ 5 ≤ g ^ 2 := le_trans hg hg2
    rw [inv_le_comm₀ (by positivity) (by positivity), inv_div]
    exact this
  have hE' : |E| ≤ 2 - 2 * (κ / 2) := by linarith
  have hγL : R ≤ γ * L := by
    rw [hγdef, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]; exact hL
  obtain ⟨hlineEx, hlineBall, -, hfin⟩ := hR γ hγ hγ0 E hE'
  obtain ⟨htail, hfinEx, hfinProp⟩ := hfin L hγL
  have hL3 : 3 ≤ L := by
    have : (3 : ℝ) ≤ L := by
      have : R * 1 ≤ R * g ^ 2 := by gcongr; nlinarith
      linarith
    exact_mod_cast this
  refine ⟨hg1, lg_hopB_eq hg1, lg_gammaG_eq hg1, hfinEx, hlineEx, fun m mInf hm hpos heq => ?_⟩
  obtain ⟨hmb, hcl⟩ := hfinProp m hm
  exact ⟨hk, hk1, hγ, hγ0, hE', hL3, htail, hmb, hlineBall mInf hpos heq, hm, hpos, heq,
    hcl mInf hpos heq⟩

/-- Lemma A.4 [uvp:prop:finite], with constants uniform in `|E| ≤ 2 - κ`: the finite and line
solutions, (A.14) [uvp:eq:finiteerror] with its weighted form, (A.15) [da:eq:uniform-free-row]
and (A.16) [uvp:eq:stable]. -/
theorem large_periodic_comparison (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ R c C : ℝ, 1 ≤ Cκ ∧ 0 < R ∧ 0 < c ∧ 0 < C ∧
      ∀ g : ℝ, Cκ ≤ g → ∀ L : ℕ, R * g ^ 2 ≤ L → ∀ E : ℝ, |E| ≤ 2 - κ →
      ∃ m mInf : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m ∧
        (0 < mInf.im ∧ mInf = dysonRHS g E mInf) ∧
        C⁻¹ ≤ m.im ∧ ‖m‖ ≤ C ∧ C⁻¹ ≤ mInf.im ∧ ‖mInf‖ ≤ C ∧
        ‖m - mInf‖ ≤ C * Real.exp (-(c * L / g ^ 2)) ∧
        let M := dysonMat (hopB g) (gammaG g) L E m
        let P := pairP (gammaG g) M
        let P₀ := perP0 g L E mInf
        (∀ x, 0 ≤ P₀ x) ∧ ∑ x, P₀ x = 1 ∧
        (∀ a b, |P a b - P₀ (b - a)| ≤ (g ^ 2)⁻¹ * epsL C c g L) ∧
        (∀ a, ∑ b, Real.exp (c * cycDist a b / g ^ 2) * |P a b - P₀ (b - a)| ≤
          epsL C c g L) ∧
        (∀ a b, ‖M a b‖ ≤ C * Real.exp (-(c * cycDist a b / g ^ 2))) ∧
        (∀ a, ∑ b, Real.exp (c / 2 * cycDist a b / g ^ 2) * ‖M a b‖ ≤ C * g ^ 2) ∧
        ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ a, ∑ b, Real.exp (c * cycDist a b / g ^ 2) *
          ‖(1 - (t : ℂ) • pairQ (gammaG g) M)⁻¹ a b‖ ≤ C := by 
  have hk : 0 < κ / 2 := by linarith
  have hk1 : κ / 2 ≤ 1 := by linarith
  obtain ⟨R, hR3, hR⟩ := lg_setup hκ hκ2
  set k := κ / 2 with hkdef
  have hk7 : 0 < k ^ 7 := by positivity
  refine ⟨1000 / k ^ 5, R, k / 2048, 10000000000 / k ^ 7, ?_, by linarith, by positivity,
    by positivity, ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    have : k ^ 5 ≤ 1 := pow_le_one₀ hk.le hk1
    linarith
  intro g hg L hL E hE
  obtain ⟨hg1, hb, hγg, ⟨m, hm⟩, ⟨mInf, hpos, heq⟩, hgood⟩ := hR g hg L hL E hE
  have h := hgood m mInf hm hpos heq
  set γ : ℝ := (g ^ 2)⁻¹ with hγdef
  have hγ := h.hγ
  have hL3 := h.hL
  have : NeZero L := ⟨by omega⟩
  set C : ℝ := 10000000000 / k ^ 7 with hC
  have hC1 : 1 ≤ C := by
    rw [hC, le_div_iff₀ hk7]; have : k ^ 7 ≤ 1 := pow_le_one₀ hk.le hk1
    linarith
  have hk7le : ∀ n : ℕ, n ≤ 7 → k ^ 7 ≤ k ^ n := fun n hn => pow_le_pow_of_le_one hk.le hk1 hn
  have hCge : ∀ (a : ℝ) (n : ℕ), 0 ≤ a → a ≤ 10000000000 → n ≤ 7 → a / k ^ n ≤ C := by
    intro a n ha ha' hn
    rw [hC]
    calc a / k ^ n ≤ 10000000000 / k ^ n := by gcongr
      _ ≤ 10000000000 / k ^ 7 := div_le_div_of_nonneg_left (by norm_num) hk7 (hk7le n hn)
  have hdiv : ∀ x : ℝ, x / g ^ 2 = γ * x := fun x => by rw [hγdef]; ring
  have hH0 : 0 ≤ γ * L := by positivity
  have hpowC : 1 + (L : ℝ) / g ^ 2 ≤ (1 + (L : ℝ) / g ^ 2) ^ C := by
    have h0 : 0 ≤ (L : ℝ) / g ^ 2 := by positivity
    have h1 : 1 ≤ 1 + (L : ℝ) / g ^ 2 := by linarith
    simpa using Real.rpow_le_rpow_of_exponent_le h1 hC1
  have hpow1 : 1 ≤ (1 + (L : ℝ) / g ^ 2) ^ C := le_trans (by
    have : 0 ≤ (L : ℝ) / g ^ 2 := by positivity
    linarith) hpowC
  have hexpc : Real.exp (-(k / 1024 * (γ * L))) ≤ Real.exp (-(k / 2048 * L / g ^ 2)) := by
    apply Real.exp_le_exp.mpr; rw [show k / 2048 * L / g ^ 2 = k / 2048 * (γ * L) by
      rw [hγdef]; ring]
    nlinarith
  have hexpc3 : Real.exp (-(3 * k / 4096 * (γ * L))) ≤ Real.exp (-(k / 2048 * L / g ^ 2)) := by
    apply Real.exp_le_exp.mpr; rw [show k / 2048 * L / g ^ 2 = k / 2048 * (γ * L) by
      rw [hγdef]; ring]
    nlinarith
  refine ⟨m, mInf, ?_, ⟨hpos, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hb, hγg]; exact hm
  · rw [dysonRHS_eq_freeT, hb, hγg]; exact heq
  · obtain ⟨him, -⟩ := h.wf h.hm
    have h32 : 32 / k ≤ C := by simpa using hCge 32 1 (by norm_num) (by norm_num) (by norm_num)
    have : (32 / k)⁻¹ ≤ m.im := by rw [inv_div]; linarith
    exact le_trans (inv_anti₀ (by positivity) h32) this
  · exact (h.wf h.hm).2.1.trans (hCge 2 1 (by norm_num) (by norm_num) (by norm_num) |>.trans' (by
      rw [pow_one]))
  · obtain ⟨him, -⟩ := h.wf h.hmI
    have h32 : 32 / k ≤ C := by simpa using hCge 32 1 (by norm_num) (by norm_num) (by norm_num)
    have : (32 / k)⁻¹ ≤ mInf.im := by rw [inv_div]; linarith
    exact le_trans (inv_anti₀ (by positivity) h32) this
  · exact (h.wf h.hmI).2.1.trans (hCge 2 1 (by norm_num) (by norm_num) (by norm_num) |>.trans' (by
      rw [pow_one]))
  · refine h.hclose.trans ?_
    have h8 : 8 / k ≤ C := by simpa using hCge 8 1 (by norm_num) (by norm_num) (by norm_num)
    exact mul_le_mul h8 hexpc (Real.exp_pos _).le (by positivity)
  · simp only [hb, hγg]
    have hLg : (L : ℝ) / g ^ 2 = γ * L := hdiv L
    have hw : ∀ (c : ℝ) (d : ℕ), c * (d : ℝ) / g ^ 2 = (c * γ) * d := fun c d => by
      rw [hγdef]; ring
    refine ⟨h.perP0_nonneg hb hγg, h.perP0_sum hb hγg, fun a b => ?_, fun a => ?_, fun a b => ?_,
      fun a => ?_, fun t ht0 ht1 a => ?_⟩
    · refine (h.P_sub_pt hb hγg a b).trans ?_
      unfold epsL
      have h1 : 3400000 / k ^ 5 ≤ C := hCge 3400000 5 (by norm_num) (by norm_num) (by norm_num)
      have e : 3400000 / k ^ 5 * γ * Real.exp (-(k / 1024 * (γ * L))) =
          γ * (3400000 / k ^ 5 * Real.exp (-(k / 1024 * (γ * L)))) := by ring
      rw [e]
      gcongr γ * ?_
      rw [mul_assoc]
      exact mul_le_mul h1 (le_trans (le_of_eq (one_mul _).symm)
        (mul_le_mul hpow1 hexpc (Real.exp_pos _).le (by positivity))) (by positivity)
        (by positivity)
    · simp_rw [hw]
      refine (h.P_sub_row hb hγg a (k / 2048 * γ) (by positivity) (by nlinarith)).trans ?_
      unfold epsL
      have h1 : 10000000000 / k ^ 6 ≤ C := hCge 10000000000 6 (by norm_num) (by norm_num)
        (by norm_num)
      rw [hLg] at hpowC ⊢
      gcongr
    · refine (h.M_le_exp a b).trans ?_
      have h1 : 4 / k ≤ C := by simpa using hCge 4 1 (by norm_num) (by norm_num) (by norm_num)
      rw [hw]
      refine mul_le_mul h1 (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (by positivity)
      have : 0 ≤ γ * (cycDist a b : ℝ) := by positivity
      have e1 : k / 1024 * γ * (cycDist a b : ℝ) = k / 1024 * (γ * cycDist a b) := by ring
      have e2 : k / 2048 * γ * (cycDist a b : ℝ) = k / 2048 * (γ * cycDist a b) := by ring
      rw [e1, e2]; nlinarith
    · simp_rw [hw]
      refine (h.M_row a (k / 2048 / 2 * γ) (by positivity) (by nlinarith)).trans ?_
      have h1 : 16384 / k ^ 2 ≤ C := hCge 16384 2 (by norm_num) (by norm_num) (by norm_num)
      rw [show 16384 / (k ^ 2 * γ) = 16384 / k ^ 2 * g ^ 2 by rw [hγdef]; field_simp]
      gcongr
    · simp_rw [hw]
      refine (h.stable_row t ht0 ht1 a (k / 2048 * γ) (by positivity) (by nlinarith)).trans ?_
      exact hCge 3000000000 7 (by norm_num) (by norm_num) (by norm_num)

/-- Lipschitz bound for the finite Fourier average `f_L = f(1+ρ^L)/(1-ρ^L)` on the bulk region at
height `≥ y₀`. -/
private lemma lg_F_lip {k y₀ : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) (hy₀ : 0 < y₀) {L : ℕ} (hL : 3 ≤ L)
    (hZ : Real.exp (-(y₀ / 32 * L)) ≤ 1 / 4) {w₁ w₂ : ℂ} (h1 : y₀ ≤ w₁.im) (h2 : y₀ ≤ w₂.im)
    (hr1 : |w₁.re| ≤ 2 - k) (hr2 : |w₂.re| ≤ 2 - k) (n1 : ‖w₁‖ ≤ 3) (n2 : ‖w₂‖ ≤ 3) :
    ‖freeTL 1 L w₁ - freeTL 1 L w₂‖ ≤
      (9 / k ^ 3 + 256 / k ^ 2 * L * Real.exp (-(y₀ / 32 * L))) * ‖w₁ - w₂‖ := by
  have hp1 : 0 < w₁.im := lt_of_lt_of_le hy₀ h1
  have hp2 : 0 < w₂.im := lt_of_lt_of_le hy₀ h2
  set Z := Real.exp (-(y₀ / 32 * L)) with hZdef
  have hρ : ∀ w : ℂ, 0 < w.im → y₀ ≤ w.im → ‖w‖ ≤ 3 → ‖freeRho 1 w‖ ^ L ≤ Z := by
    intro w hp hy hn
    calc ‖freeRho 1 w‖ ^ L ≤ Real.exp (-(w.im / 32)) ^ L := by
          gcongr; exact lg_norm_rho_le_exp hp hn
      _ ≤ Real.exp (-(y₀ / 32)) ^ L := by gcongr
      _ = Z := by rw [← Real.exp_nat_mul, hZdef]; congr 1; ring
  have hz1 := hρ w₁ hp1 h1 n1
  have hz2 := hρ w₂ hp2 h2 n2
  rw [lg_freeTL_eq hp1 hL, lg_freeTL_eq hp2 hL]
  have hz1' : ‖freeRho 1 w₁ ^ L‖ ≤ 1 / 2 := by rw [norm_pow]; linarith
  have hz2' : ‖freeRho 1 w₂ ^ L‖ ≤ 1 / 2 := by rw [norm_pow]; linarith
  refine (lg_ratio_lip _ _ _ _ hz1' hz2').trans ?_
  have hf := lg_f_lip hk hk1 hp1 hp2 hr1 hr2 n1 n2
  have hrl := lg_rho_lip hk hk1 hp1 hp2 hr1 hr2 n1 n2
  have hf2 := lg_norm_f_le hk hk1 hp2 hr2
  set ρ₁ := freeRho 1 w₁
  set ρ₂ := freeRho 1 w₂
  have hM : max ‖ρ₁‖ ‖ρ₂‖ ^ (L - 1) ≤ 4 * Z := by
    have hM1 : 1 / 4 ≤ max ‖ρ₁‖ ‖ρ₂‖ := le_max_of_le_left (lg_norm_rho_ge hp1 n1)
    have hML : max ‖ρ₁‖ ‖ρ₂‖ ^ L ≤ Z := by
      rcases le_total ‖ρ₁‖ ‖ρ₂‖ with h | h
      · rw [max_eq_right h]; exact hz2
      · rw [max_eq_left h]; exact hz1
    have e : max ‖ρ₁‖ ‖ρ₂‖ ^ L = max ‖ρ₁‖ ‖ρ₂‖ * max ‖ρ₁‖ ‖ρ₂‖ ^ (L - 1) := by
      rw [← pow_succ']; congr 1; omega
    have : 0 ≤ max ‖ρ₁‖ ‖ρ₂‖ ^ (L - 1) := by positivity
    nlinarith
  have hz : ‖ρ₁ ^ L - ρ₂ ^ L‖ ≤ L * (4 * Z) * (2 / k * ‖w₁ - w₂‖) := by
    refine (lg_norm_pow_sub_le _ _ _).trans ?_
    gcongr
  calc 3 * ‖freeT 1 w₁ - freeT 1 w₂‖ + 8 * ‖freeT 1 w₂‖ * ‖ρ₁ ^ L - ρ₂ ^ L‖
      ≤ 3 * (3 / k ^ 3 * ‖w₁ - w₂‖) + 8 * (1 / k) * (L * (4 * Z) * (2 / k * ‖w₁ - w₂‖)) := by
        gcongr
    _ = (9 / k ^ 3 + 64 / k ^ 2 * L * Z) * ‖w₁ - w₂‖ := by field_simp; ring
    _ ≤ (9 / k ^ 3 + 256 / k ^ 2 * L * Z) * ‖w₁ - w₂‖ := by
        gcongr; norm_num

private lemma lg_freeTL_differentiableAt {L : ℕ} {w : ℂ} (hw : 0 < w.im) :
    DifferentiableAt ℂ (freeTL 1 L) w := by
  unfold freeTL
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.fun_sum
  intro j _
  apply DifferentiableAt.inv (differentiableAt_const _ |>.sub differentiableAt_id)
  apply sub_ne_zero.mpr
  intro h0
  rw [← h0, Complex.ofReal_im] at hw
  exact lt_irrefl 0 hw

set_option maxHeartbeats 4000000 in
-- the many explicit estimates of this proof exceed the default heartbeat limit
/-- The statement of (A.21) [fo:eq:terminal-anchor-derivative]. -/
private theorem lg_anchor_aux (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ R : ℝ, 1 ≤ Cκ ∧ 0 < R ∧ ∀ β : ℝ, 0 < β → Cκ ≤ β ^ (-(1 : ℝ) / 2) →
      ∀ L : ℕ, R / β ≤ L → ∀ e : ℝ, |e| ≤ 2 - κ →
        IsDysonRootV 1 β L e (mRootV 1 β L e) ∧
        HasDerivAt (fun e' : ℝ => mRootV 1 β L e') (deriv (fun e' : ℝ => mRootV 1 β L e') e) e ∧
        β * ‖deriv (fun e' : ℝ => mRootV 1 β L e') e‖ ≤ 1 / 2 := by 
  have hk : 0 < κ / 4 := by linarith
  have hk1 : κ / 4 ≤ 1 := by linarith
  obtain ⟨R₀, hR₀3, hcore⟩ := lg_core hk hk1
  set k := κ / 4 with hkdef
  obtain ⟨R, hRR₀, hR0, hRt⟩ := lg_tail (k / 2048) (k ^ 2 / 2048) R₀ (by positivity) (by positivity)
  refine ⟨1000 / k ^ 5, R, ?_, by linarith, fun β hβ hCβ L hL e he => ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    have : k ^ 5 ≤ 1 := pow_le_one₀ hk.le hk1
    linarith
  -- `β ≤ k⁵/1000`
  have hC1 : 1 ≤ 1000 / k ^ 5 := by
    rw [le_div_iff₀ (by positivity)]; have : k ^ 5 ≤ 1 := pow_le_one₀ hk.le hk1
    linarith
  have hβ0 : β ≤ k ^ 5 / 1000 := by
    have h1 : (β ^ (-(1 : ℝ) / 2)) ^ 2 = β⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hβ.le]; norm_num; exact Real.rpow_neg_one β
    have h2 : (1000 / k ^ 5) ^ 2 ≤ (β ^ (-(1 : ℝ) / 2)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hCβ 2
    rw [h1] at h2
    have h3 : 1000 / k ^ 5 ≤ β⁻¹ := by nlinarith
    rw [le_inv_comm₀ (by positivity) hβ, inv_div] at h3
    exact h3
  have hk5 : k ^ 5 ≤ 1 := pow_le_one₀ hk.le hk1
  have hβ1 : β ≤ 1 := by linarith
  have hH : R ≤ β * L := by rw [div_le_iff₀ hβ] at hL; linarith
  have hH0 : 0 ≤ β * L := by positivity
  -- the solutions near `e`
  have hnear : ∀ e' : ℝ, |e' - e| < 2 * k → |e'| ≤ 2 - 2 * k := by
    intro e' h'
    have := abs_sub_abs_le_abs_sub e' e
    have : |e| ≤ 2 - 4 * k := by rw [hkdef]; linarith
    linarith
  have hL3 : 3 ≤ L := by
    have : (3 : ℝ) ≤ L := by
      have : β * L ≤ L := by nlinarith
      linarith
    exact_mod_cast this
  have hroot : ∀ e' : ℝ, |e'| ≤ 2 - 2 * k →
      IsDysonRootV 1 β L e' (mRootV 1 β L e') ∧
        mRootV 1 β L e' ∈ Metric.closedBall (lgC0 β e') (k / 32) := by
    intro e' he'
    obtain ⟨-, -, -, hfin⟩ := hcore β hβ hβ0 e' he'
    obtain ⟨-, ⟨m₀, hm₀⟩, hprop⟩ := hfin L (le_trans hRR₀ hH)
    have hsel := (mRootV_spec 1 β (by norm_num) hβ L hL3 e' (by simp)).2 m₀ hm₀
    rw [hsel]
    exact ⟨hm₀, (hprop m₀ hm₀).1⟩
  set m : ℝ → ℂ := fun e' => mRootV 1 β L e' with hmdef
  set φ : ℝ → ℂ := fun e' => (e' : ℂ) + (β : ℂ) * m e' with hφdef
  have hfix : ∀ e' : ℝ, |e'| ≤ 2 - 2 * k → m e' = freeTL 1 L (φ e') := by
    intro e' he'
    have := (hroot e' he').1.2
    unfold dysonRHSV at this
    exact this
  -- region facts
  have hreg : ∀ e' : ℝ, |e'| ≤ 2 - 2 * k →
      β * (k / 32) ≤ (φ e').im ∧ |(φ e').re| ≤ 2 - k ∧ ‖φ e'‖ ≤ 3 ∧ ‖m e'‖ ≤ 2 / k := by
    intro e' he'
    obtain ⟨-, hmn, -, hlo, -, -, hre, hn⟩ := lg_ball_facts hk hk1 hβ hβ0 he' (hroot e' he').2
    exact ⟨hlo, hre, hn, hmn⟩
  -- Lipschitz constant of `f_L`
  set y₀ : ℝ := β * k / 64 with hy₀
  have hy₀0 : 0 < y₀ := by positivity
  set K : ℝ := 9 / k ^ 3 + 256 / k ^ 2 * L * Real.exp (-(y₀ / 32 * L)) with hK
  have hexpe : Real.exp (-(y₀ / 32 * L)) = Real.exp (-(k / 2048 * (β * L))) := by
    rw [hy₀]; ring_nf
  have htail := hRt (β * L) hH
  have hZ : Real.exp (-(y₀ / 32 * L)) ≤ 1 / 4 := by
    rw [hexpe]
    have := Real.exp_pos (-(k / 2048 * (β * L)))
    have : k ^ 2 / 2048 ≤ 1 / 4 := by nlinarith
    nlinarith
  have hK0 : 0 ≤ K := by positivity
  have hβK : β * K ≤ 1 / 4 := by
    have h1 : β * (9 / k ^ 3) ≤ 1 / 8 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      have : k ^ 5 ≤ k ^ 3 := pow_le_pow_of_le_one hk.le hk1 (by norm_num)
      nlinarith
    have h2 : β * (256 / k ^ 2 * L * Real.exp (-(y₀ / 32 * L))) ≤ 1 / 8 := by
      rw [hexpe]
      have e1 : β * (256 / k ^ 2 * L * Real.exp (-(k / 2048 * (β * L)))) =
          256 / k ^ 2 * ((β * L) * Real.exp (-(k / 2048 * (β * L)))) := by ring
      rw [e1]
      have h3 : (β * L) * Real.exp (-(k / 2048 * (β * L))) ≤ k ^ 2 / 2048 := by
        have := Real.exp_pos (-(k / 2048 * (β * L))); nlinarith
      calc 256 / k ^ 2 * ((β * L) * Real.exp (-(k / 2048 * (β * L)))) ≤
          256 / k ^ 2 * (k ^ 2 / 2048) := by gcongr
        _ = 1 / 8 := by field_simp; norm_num
    rw [hK, mul_add]; linarith
  have hFlip : ∀ w₁ w₂ : ℂ, y₀ ≤ w₁.im → y₀ ≤ w₂.im → |w₁.re| ≤ 2 - k → |w₂.re| ≤ 2 - k →
      ‖w₁‖ ≤ 3 → ‖w₂‖ ≤ 3 → ‖freeTL 1 L w₁ - freeTL 1 L w₂‖ ≤ K * ‖w₁ - w₂‖ :=
    fun w₁ w₂ h1 h2 r1 r2 n1 n2 => lg_F_lip hk hk1 hy₀0 hL3 hZ h1 h2 r1 r2 n1 n2
  have hy₀le : ∀ e' : ℝ, |e'| ≤ 2 - 2 * k → y₀ ≤ (φ e').im := by
    intro e' he'; have := (hreg e' he').1
    have : y₀ ≤ β * (k / 32) := by rw [hy₀]; nlinarith
    linarith
  -- Lipschitz bound for `m` near `e`
  have hmlip : ∀ e₁ e₂ : ℝ, |e₁| ≤ 2 - 2 * k → |e₂| ≤ 2 - 2 * k →
      ‖m e₁ - m e₂‖ ≤ 2 * K * |e₁ - e₂| := by
    intro e₁ e₂ h1 h2
    have hl := hFlip (φ e₁) (φ e₂) (hy₀le e₁ h1) (hy₀le e₂ h2) (hreg e₁ h1).2.1 (hreg e₂ h2).2.1
      (hreg e₁ h1).2.2.1 (hreg e₂ h2).2.2.1
    rw [← hfix e₁ h1, ← hfix e₂ h2] at hl
    have hφ : φ e₁ - φ e₂ = ((e₁ - e₂ : ℝ) : ℂ) + (β : ℂ) * (m e₁ - m e₂) := by
      simp only [hφdef]; push_cast; ring
    have hφn : ‖φ e₁ - φ e₂‖ ≤ |e₁ - e₂| + β * ‖m e₁ - m e₂‖ := by
      rw [hφ]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_of_nonneg hβ.le]
    have h3 : ‖m e₁ - m e₂‖ ≤ K * (|e₁ - e₂| + β * ‖m e₁ - m e₂‖) :=
      hl.trans (mul_le_mul_of_nonneg_left hφn hK0)
    have h4 : (1 - β * K) * ‖m e₁ - m e₂‖ ≤ K * |e₁ - e₂| := by nlinarith
    have h5 : 3 / 4 * ‖m e₁ - m e₂‖ ≤ (1 - β * K) * ‖m e₁ - m e₂‖ := by
      gcongr; linarith
    have h6 : 0 ≤ K * |e₁ - e₂| := by positivity
    nlinarith [norm_nonneg (m e₁ - m e₂)]
  have he' : |e| ≤ 2 - 2 * k := hnear e (by rw [sub_self, abs_zero]; positivity)
  obtain ⟨hreg₀im, hreg₀re, hreg₀n, hm₀n⟩ := hreg e he'
  set w₀ := φ e with hw₀def
  have hw₀ : 0 < w₀.im := lt_of_lt_of_le hy₀0 (hy₀le e he')
  have hFd : HasDerivAt (freeTL 1 L) (deriv (freeTL 1 L) w₀) w₀ :=
    (lg_freeTL_differentiableAt (L := L) hw₀).hasDerivAt
  set F' := deriv (freeTL 1 L) w₀ with hF'def
  -- `‖F'‖ ≤ K`
  set G : Set ℂ := {w | y₀ < w.im} ∩ {w | |w.re| < 2 - k} ∩ {w | ‖w‖ < 3} with hG
  have hGopen : IsOpen G := by
    refine ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const)).inter
      (isOpen_lt continuous_norm continuous_const)
  have hβm : β * ‖m e‖ ≤ 2 * β / k := by
    have := mul_le_mul_of_nonneg_left hm₀n hβ.le; linarith [show β * (2 / k) = 2 * β / k by ring]
  have h2βk : 2 * β / k < k := by
    rw [div_lt_iff₀ hk]
    have : k ^ 5 ≤ k ^ 2 := pow_le_pow_of_le_one hk.le hk1 (by norm_num)
    have : 0 < k ^ 2 := by positivity
    nlinarith
  have hw₀G : w₀ ∈ G := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change y₀ < w₀.im
      have : y₀ < β * (k / 32) := by rw [hy₀]; nlinarith
      linarith
    · change |w₀.re| < 2 - k
      have e1 : w₀.re = e + β * (m e).re := by simp [hw₀def, hφdef]
      rw [e1]
      have h1 : |β * (m e).re| ≤ β * ‖m e‖ := by
        rw [abs_mul, abs_of_pos hβ]
        exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hβ.le
      have h2 := abs_add_le e (β * (m e).re)
      have : |e| ≤ 2 - 4 * k := by rw [hkdef]; linarith
      linarith
    · change ‖w₀‖ < 3
      have h1 : ‖w₀‖ ≤ |e| + β * ‖m e‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_of_nonneg hβ.le]
      have : |e| ≤ 2 - 4 * k := by rw [hkdef]; linarith
      linarith
  have hlipG : LipschitzOnWith (Real.toNNReal K) (freeTL 1 L) G := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hK0]
    exact hFlip x y hx.1.1.le hy.1.1.le hx.1.2.le hy.1.2.le hx.2.le hy.2.le
  have hF'K : ‖F'‖ ≤ K := by
    have := hFd.le_of_lipschitzOn (hGopen.mem_nhds hw₀G) hlipG
    rwa [Real.coe_toNNReal _ hK0] at this
  have hβF : ‖(β : ℂ) * F'‖ ≤ 1 / 4 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ.le]
    exact le_trans (mul_le_mul_of_nonneg_left hF'K hβ.le) hβK
  have hden : 3 / 4 ≤ ‖1 - (β : ℂ) * F'‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((β : ℂ) * F')
    rw [norm_one] at this; linarith
  have hden0 : 1 - (β : ℂ) * F' ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hden; norm_num at hden
  set D := F' / (1 - (β : ℂ) * F') with hDdef
  -- `m` has derivative `D`
  have hball : ∀ᶠ e' in 𝓝 e, |e' - e| < 2 * k := by
    have := Metric.ball_mem_nhds e (show 0 < 2 * k by positivity)
    filter_upwards [this] with e' he'
    rwa [Metric.mem_ball, Real.dist_eq] at he'
  have hφbd : ∀ e' : ℝ, |e' - e| < 2 * k → ‖φ e' - w₀‖ ≤ (1 + 2 * β * K) * |e' - e| := by
    intro e' h'
    have h1 := hmlip e' e (hnear e' h') he'
    have hφ : φ e' - w₀ = ((e' - e : ℝ) : ℂ) + (β : ℂ) * (m e' - m e) := by
      simp only [hw₀def, hφdef]; push_cast; ring
    rw [hφ]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_of_nonneg hβ.le]
    have := mul_le_mul_of_nonneg_left h1 hβ.le
    nlinarith [abs_nonneg (e' - e)]
  have hφc : Tendsto φ (𝓝 e) (𝓝 w₀) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun e' : ℝ => (1 + 2 * β * K) * |e' - e|) (𝓝 e) (𝓝 0) := by
      have : Tendsto (fun e' : ℝ => |e' - e|) (𝓝 e) (𝓝 0) := by
        have h0 : Tendsto (fun e' : ℝ => e' - e) (𝓝 e) (𝓝 (e - e)) :=
          tendsto_id.sub tendsto_const_nhds
        rw [sub_self] at h0
        simpa using h0.abs
      simpa using this.const_mul (1 + 2 * β * K)
    refine squeeze_zero' (Eventually.of_forall fun e' => norm_nonneg _) ?_ hlim
    filter_upwards [hball] with e' he'
    exact hφbd e' he'
  have hr := hFd.isLittleO.comp_tendsto hφc
  have hO : Asymptotics.IsBigO (𝓝 e) (fun e' : ℝ => φ e' - w₀) (fun e' : ℝ => e' - e) := by
    refine Asymptotics.IsBigO.of_bound (1 + 2 * β * K) ?_
    filter_upwards [hball] with e' he'
    rw [Real.norm_eq_abs]
    exact hφbd e' he'
  have hr2 := (hr.trans_isBigO hO).const_mul_left (1 - (β : ℂ) * F')⁻¹
  have hmD : HasDerivAt m D e := by
    rw [hasDerivAt_iff_isLittleO]
    refine hr2.congr' ?_ EventuallyEq.rfl
    filter_upwards [hball] with e' hb'
    simp only [Function.comp]
    rw [← hfix e' (hnear e' hb'), ← hfix e he', hDdef, Complex.real_smul, smul_eq_mul]
    have hφ : φ e' - w₀ = ((e' - e : ℝ) : ℂ) + (β : ℂ) * (m e' - m e) := by
      simp only [hw₀def, hφdef]; push_cast; ring
    rw [hφ]
    field_simp
    ring
  have hderiv : deriv m e = D := hmD.deriv
  refine ⟨(hroot e he').1, ?_, ?_⟩
  · rw [hderiv]; exact hmD
  · rw [hderiv, hDdef, norm_div]
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    have h1 : β * ‖F'‖ ≤ 1 / 4 := le_trans (mul_le_mul_of_nonneg_left hF'K hβ.le) hβK
    linarith

/-- (A.21) [fo:eq:terminal-anchor-derivative]: at hopping `1` and variance `β`, the real-energy
solution is differentiable in the energy with `β|∂_e m| ≤ 1/2`. -/
theorem anchor_derivative (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ R : ℝ, 1 ≤ Cκ ∧ 0 < R ∧ ∀ β : ℝ, 0 < β → Cκ ≤ β ^ (-(1 : ℝ) / 2) →
      ∀ L : ℕ, R / β ≤ L → ∀ e : ℝ, |e| ≤ 2 - κ →
        IsDysonRootV 1 β L e (mRootV 1 β L e) ∧
        HasDerivAt (fun e' : ℝ => mRootV 1 β L e') (deriv (fun e' : ℝ => mRootV 1 β L e') e) e ∧
        β * ‖deriv (fun e' : ℝ => mRootV 1 β L e') e‖ ≤ 1 / 2 := by
  exact lg_anchor_aux κ hκ hκ2

/-- `C log y ≤ (c/2) y + C (log (2C/c) - 1)` for `y > 0`. -/
private lemma lg_log_le (C c y : ℝ) (hC : 0 < C) (hc : 0 < c) (hy : 0 < y) :
    C * Real.log y ≤ c / 2 * y + C * (Real.log (2 * C / c) - 1) := by
  have h := Real.log_le_sub_one_of_pos (show 0 < c / (2 * C) * y by positivity)
  rw [Real.log_mul (by positivity) hy.ne'] at h
  have e : Real.log (c / (2 * C)) = -Real.log (2 * C / c) := by
    rw [← Real.log_inv, inv_div]
  rw [e] at h
  have : C * (c / (2 * C) * y) = c / 2 * y := by field_simp
  nlinarith

private lemma lg_exp_sub_one_le (x : ℝ) (_hx : 0 ≤ x) : Real.exp x - 1 ≤ x * Real.exp x := by
  have h := Real.add_one_le_exp (-x)
  have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos x]

namespace LgGood

variable {k γ E : ℝ} {L : ℕ} {m mInf : ℂ} (h : LgGood k γ E L m mInf)
include h

private lemma P_nonneg (a c : Fin L) : 0 ≤ pairP γ (dysonMat 1 γ L E m) a c := by
  simp only [pairP, Matrix.of_apply]; have := h.hγ; positivity

private lemma P_le (a c : Fin L) : pairP γ (dysonMat 1 γ L E m) a c ≤
    8 * γ / k ^ 2 * (Real.exp (-(γ * k / 512)) ^ lgD L a c +
      Real.exp (-(γ * k / 512)) ^ (L - lgD L a c)) := by
  simp only [pairP, Matrix.of_apply]
  have h1 := h.M_le a c
  have hk := h.hk
  have hγ := h.hγ
  set q := Real.exp (-(γ * k / 1024))
  have e : Real.exp (-(γ * k / 512)) = q ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [e, ← pow_mul, ← pow_mul]
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have h2 : ‖dysonMat 1 γ L E m a c‖ ^ 2 ≤ (2 / k * (q ^ lgD L a c + q ^ (L - lgD L a c))) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : (2 / k * (q ^ lgD L a c + q ^ (L - lgD L a c))) ^ 2 ≤
      8 / k ^ 2 * (q ^ (2 * lgD L a c) + q ^ (2 * (L - lgD L a c))) := by
    rw [pow_mul, pow_mul, mul_pow, div_pow]
    have : (q ^ lgD L a c + q ^ (L - lgD L a c)) ^ 2 ≤
        2 * ((q ^ 2) ^ lgD L a c + (q ^ 2) ^ (L - lgD L a c)) := by
      rw [← pow_mul, ← pow_mul, mul_comm 2 (lgD L a c), mul_comm 2 (L - lgD L a c), pow_mul,
        pow_mul]
      nlinarith [sq_nonneg (q ^ lgD L a c - q ^ (L - lgD L a c))]
    calc 2 ^ 2 / k ^ 2 * (q ^ lgD L a c + q ^ (L - lgD L a c)) ^ 2
        ≤ 2 ^ 2 / k ^ 2 * (2 * ((q ^ 2) ^ lgD L a c + (q ^ 2) ^ (L - lgD L a c))) := by gcongr
      _ = _ := by ring
  calc γ * ‖dysonMat 1 γ L E m a c‖ ^ 2
      ≤ γ * (8 / k ^ 2 * (q ^ (2 * lgD L a c) + q ^ (2 * (L - lgD L a c)))) := by
        gcongr; exact h2.trans h3
    _ = _ := by ring

/-- Weighted row of `P` at small rate: `Σ_c e^{μ d} P_ac ≤ 3/2` for `μ ≤ k⁴γ/536870912`. -/
private lemma P_row_weighted (a : Fin L) (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ : μ ≤ k ^ 4 * γ / 536870912) :
    ∑ c, Real.exp (μ * cycDist a c) * pairP γ (dysonMat 1 γ L E m) a c ≤ 3 / 2 := by
  have hk := h.hk
  have hk1 := h.hk1
  have hγ := h.hγ
  have hrow := pairP_row_sum 1 γ hγ L (by have := h.hL; omega) E m h.hroot a
  have hb0 := h.b_pos
  have hgk : γ * k ≤ 1 := by have := mul_le_mul h.γ1 hk1 hk.le zero_le_one; linarith
  have hk4 : k ^ 4 ≤ k := by
    calc k ^ 4 ≤ k ^ 1 := pow_le_pow_of_le_one hk.le hk1 (by norm_num)
      _ = k := pow_one k
  have hμ' : μ ≤ γ * k / 2048 := by
    have : k ^ 4 * γ / 536870912 ≤ γ * k / 2048 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
    linarith
  set s := Real.exp (-(γ * k / 512)) with hsdef
  have hs0 : 0 ≤ s := (Real.exp_pos _).le
  have hμs : Real.exp μ * s ≤ Real.exp (-(3 * γ * k / 2048)) := by
    rw [hsdef, ← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have hgap : γ * k / 2048 ≤ 1 - Real.exp μ * s := by
    have h1 := lg_one_sub_exp_neg (3 * γ * k / 2048) (by positivity) (by linarith)
    linarith
  have hμs1 : Real.exp μ * s < 1 := by linarith
  have hrn := lg_row_ngeom a μ s hμ0 hs0 hμs1
  have hg2 : 2 / (1 - Real.exp μ * s) ^ 2 ≤ 2 * (2048 / (γ * k)) ^ 2 := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    have h1 : γ * k ≤ 2048 * (1 - Real.exp μ * s) := by linarith
    have h2 : (γ * k) ^ 2 ≤ (2048 * (1 - Real.exp μ * s)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    rw [mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  -- `(e^{μd} - 1) P ≤ μ e^{μ d} (8γ/k²)(x s^x + (L-x) s^{L-x})`
  have hpt : ∀ c, (Real.exp (μ * cycDist a c) - 1) * pairP γ (dysonMat 1 γ L E m) a c ≤
      μ * (8 * γ / k ^ 2) * (Real.exp (μ * cycDist a c) * ((lgD L a c : ℝ) * s ^ lgD L a c +
        ((L - lgD L a c : ℕ) : ℝ) * s ^ (L - lgD L a c))) := by
    intro c
    have hd0 : (0 : ℝ) ≤ cycDist a c := by positivity
    have he1 := lg_exp_sub_one_le (μ * cycDist a c) (by positivity)
    have hP := h.P_le a c
    have hPn := h.P_nonneg a c
    have hd1 : (cycDist a c : ℝ) ≤ lgD L a c := by exact_mod_cast cycDist_le_lgD a c
    have hd2 : (cycDist a c : ℝ) ≤ ((L - lgD L a c : ℕ) : ℝ) := by
      exact_mod_cast cycDist_le_sub_lgD a c
    have hE0 : 0 ≤ Real.exp (μ * cycDist a c) - 1 := by
      have := Real.one_le_exp (show 0 ≤ μ * cycDist a c by positivity); linarith
    have hsx := pow_nonneg hs0 (lgD L a c)
    have hsy := pow_nonneg hs0 (L - lgD L a c)
    calc (Real.exp (μ * cycDist a c) - 1) * pairP γ (dysonMat 1 γ L E m) a c
        ≤ (μ * cycDist a c * Real.exp (μ * cycDist a c)) *
          (8 * γ / k ^ 2 * (s ^ lgD L a c + s ^ (L - lgD L a c))) :=
          mul_le_mul he1 hP hPn (by positivity)
      _ = μ * (8 * γ / k ^ 2) * (Real.exp (μ * cycDist a c) *
          ((cycDist a c : ℝ) * s ^ lgD L a c + (cycDist a c : ℝ) * s ^ (L - lgD L a c))) := by
          ring
      _ ≤ _ := by gcongr
  have hsplit : ∑ c, Real.exp (μ * cycDist a c) * pairP γ (dysonMat 1 γ L E m) a c =
      ∑ c, (Real.exp (μ * cycDist a c) - 1) * pairP γ (dysonMat 1 γ L E m) a c +
        ∑ c, pairP γ (dysonMat 1 γ L E m) a c := by
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun c _ => by ring
  rw [hsplit, hrow]
  have hsum := Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => hpt c
  rw [← Finset.mul_sum] at hsum
  have hbd : μ * (8 * γ / k ^ 2) * (2 * (2048 / (γ * k)) ^ 2) ≤ 1 / 2 := by
    have e : μ * (8 * γ / k ^ 2) * (2 * (2048 / (γ * k)) ^ 2) = μ * (67108864 / (k ^ 4 * γ)) := by
      field_simp; ring
    rw [e]
    calc μ * (67108864 / (k ^ 4 * γ)) ≤ k ^ 4 * γ / 536870912 * (67108864 / (k ^ 4 * γ)) := by
          gcongr
      _ = 1 / 8 := by field_simp; norm_num
      _ ≤ 1 / 2 := by norm_num
  have h3 : μ * (8 * γ / k ^ 2) * ∑ c, Real.exp (μ * cycDist a c) *
      ((lgD L a c : ℝ) * s ^ lgD L a c + ((L - lgD L a c : ℕ) : ℝ) * s ^ (L - lgD L a c)) ≤
      μ * (8 * γ / k ^ 2) * (2 * (2048 / (γ * k)) ^ 2) := by
    gcongr; exact hrn.trans hg2
  linarith

end LgGood

/-! ### The comparison mixed kernel `Ξ` of Lemma A.10 [uvp:lem:actual-kernels] -/

/-- Over any field: `I + B G_τ` inverts `I - (tα) G_σ` under the energy relation. -/
private lemma lg_geom_inv {𝕜 : Type*} [Field 𝕜] {L : ℕ} (hL : 3 ≤ L) (σ τ α B t : 𝕜) (hσ0 : σ ≠ 0)
    (hσL : 1 - σ ^ L ≠ 0) (hτ0 : τ ≠ 0) (hτL : 1 - τ ^ L ≠ 0) (hστ : σ⁻¹ - σ ≠ 0)
    (hM3 : σ + σ⁻¹ - t * α * (σ⁻¹ - σ) = τ + τ⁻¹) (hB : B * (τ⁻¹ - τ) = t * α * (σ⁻¹ - σ)) :
    (1 - (t * α) • geomC σ L) * (1 + B • geomC τ L) = 1 := by
  set Gσ := geomC σ L
  set Gτ := geomC τ L
  set A := adjK 𝕜 L
  have hTσ := geomC_mul hσ0 hσL hL
  have hTτ := geomC_mul hτ0 hτL hL
  set Tσ := (σ + σ⁻¹) • (1 : Matrix (Fin L) (Fin L) 𝕜) - A
  set Tτ := (τ + τ⁻¹) • (1 : Matrix (Fin L) (Fin L) 𝕜) - A
  have h1 : Tσ * (1 - (t * α) • Gσ) = Tτ := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, hTσ, smul_smul]
    simp only [Tσ, Tτ, ← hM3]
    module
  have h2 : Tτ * (1 + B • Gτ) = Tσ := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, hTτ, smul_smul, hB]
    simp only [Tσ, Tτ, ← hM3]
    module
  have hYT : ((σ⁻¹ - σ)⁻¹ • Gσ) * Tσ = 1 := by
    rw [mul_eq_one_comm, Matrix.mul_smul, hTσ, smul_smul, inv_mul_cancel₀ hστ, one_smul]
  have : Tσ * ((1 - (t * α) • Gσ) * (1 + B • Gτ)) = Tσ := by rw [← Matrix.mul_assoc, h1, h2]
  have := congrArg (fun X => ((σ⁻¹ - σ)⁻¹ • Gσ) * X) this
  simp only [← Matrix.mul_assoc, hYT, Matrix.one_mul] at this
  exact this

private lemma lg_cosh_lamGeo {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) :
    Real.cosh (lamGeo D δ) = 1 + δ / (2 * D) :=
  Real.cosh_arcosh (by have : 0 < δ / (2 * D) := by positivity
                       linarith)

private lemma lg_lamGeo_pos {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) : 0 < lamGeo D δ :=
  Real.arcosh_pos (by have : 0 < δ / (2 * D) := by positivity
                      linarith)

private lemma lg_sqrt_eq_sinh {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) :
    Real.sqrt (δ * (δ + 4 * D)) = 2 * D * Real.sinh (lamGeo D δ) := by
  have hx1 : 1 ≤ 1 + δ / (2 * D) := by
    have : 0 < δ / (2 * D) := by positivity
    linarith
  unfold lamGeo
  rw [Real.sinh_arcosh hx1]
  have h2D : 0 ≤ 2 * D := by positivity
  rw [show 2 * D * Real.sqrt ((1 + δ / (2 * D)) ^ 2 - 1) =
      Real.sqrt ((2 * D) ^ 2 * ((1 + δ / (2 * D)) ^ 2 - 1)) by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h2D]]
  congr 1
  field_simp
  ring

/-- `Σ_c e^{μ d(a,c)} G_τ(c - a) ≤ (1 + e^μ τ)/(1 - e^μ τ)` (no loss from periodization). -/
private lemma lg_row_geomV {L : ℕ} (a : Fin L) (μ τ : ℝ) (hμ : 0 ≤ μ) (hτ : 0 ≤ τ)
    (hp : Real.exp μ * τ < 1) :
    ∑ c, Real.exp (μ * cycDist a c) * geomV τ L (lgD L a c) ≤
      (1 + Real.exp μ * τ) / (1 - Real.exp μ * τ) := by
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    have : 0 ≤ Real.exp μ * τ := by positivity
    exact div_nonneg (by linarith) (by linarith)
  set p := Real.exp μ * τ with hpdef
  have hp0 : 0 ≤ p := by positivity
  have hτp : τ ≤ p := by
    have := Real.one_le_exp hμ; nlinarith
  have hτL : τ ^ L ≤ p ^ L := pow_le_pow_left₀ hτ hτp L
  have hpL : p ^ L < 1 := pow_lt_one₀ hp0 hp (by omega)
  have h1 : ∀ c, Real.exp (μ * cycDist a c) * geomV τ L (lgD L a c) ≤
      (p ^ lgD L a c + p ^ (L - lgD L a c)) / (1 - p ^ L) := by
    intro c
    unfold geomV
    have hx : Real.exp (μ * cycDist a c) * τ ^ lgD L a c ≤ p ^ lgD L a c := by
      rw [hpdef, ← lg_exp_mul_pow]
      gcongr
      exact_mod_cast cycDist_le_lgD a c
    have hy : Real.exp (μ * cycDist a c) * τ ^ (L - lgD L a c) ≤ p ^ (L - lgD L a c) := by
      rw [hpdef, ← lg_exp_mul_pow]
      gcongr
      exact_mod_cast cycDist_le_sub_lgD a c
    rw [mul_div_assoc', mul_add]
    calc (Real.exp (μ * cycDist a c) * τ ^ lgD L a c +
          Real.exp (μ * cycDist a c) * τ ^ (L - lgD L a c)) / (1 - τ ^ L)
        ≤ (p ^ lgD L a c + p ^ (L - lgD L a c)) / (1 - τ ^ L) := by
          gcongr; linarith [pow_le_one₀ hτ (le_trans hτp hp.le) (n := L)]
      _ ≤ (p ^ lgD L a c + p ^ (L - lgD L a c)) / (1 - p ^ L) := by
          apply div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  refine (Finset.sum_le_sum fun c _ => h1 c).trans (le_of_eq ?_)
  rw [sum_lgD_row a (fun k => (p ^ k + p ^ (L - k)) / (1 - p ^ L)), ← Finset.sum_div,
    Finset.sum_add_distrib]
  have hA : ∑ k ∈ Finset.range L, p ^ k = (1 - p ^ L) / (1 - p) := by
    rw [geom_sum_eq hp.ne, div_eq_div_iff (sub_ne_zero.mpr hp.ne) (sub_ne_zero.mpr hp.ne')]
    ring
  have hB : ∑ k ∈ Finset.range L, p ^ (L - k) = p * ((1 - p ^ L) / (1 - p)) := by
    rw [← hA, Finset.mul_sum, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [← pow_succ']; congr 1; omega
  rw [hA, hB]
  have : 1 - p ^ L ≠ 0 := by linarith
  have : 1 - p ≠ 0 := by linarith
  field_simp

private lemma lg_geomV_symm {𝕜 : Type*} [Field 𝕜] (τ : 𝕜) {L : ℕ} (a c : Fin L) :
    geomV τ L (lgD L c a) = geomV τ L (lgD L a c) := by
  rw [lgD_swap a c]
  split_ifs with h
  · rw [h]
  · unfold geomV
    have := lgD_lt a c
    rw [Nat.sub_sub_self this.le, add_comm]

/-- `(1+p)/(1-p) ≤ 2(1+τ)/(1-τ)` for `p² ≤ τ < 1`. -/
private lemma lg_ratio_le (p τ : ℝ) (hp0 : 0 ≤ p) (hpτ : p ^ 2 ≤ τ) (hτ1 : τ < 1) :
    (1 + p) / (1 - p) ≤ 2 * ((1 + τ) / (1 - τ)) := by
  have hp1 : p < 1 := by nlinarith
  rw [mul_div_assoc', div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hpτ) (show (0 : ℝ) ≤ 3 - p by linarith),
    pow_nonneg (show (0 : ℝ) ≤ 1 - p by linarith) 3]

namespace LgGood

variable {k γ E : ℝ} {L : ℕ} {m mInf : ℂ} (h : LgGood k γ E L m mInf)
include h

/-- The real data of the comparison kernel: `σ = |ρ_∞|²`, `φ = γ|f_∞|²`, `D = σ/(1-σ)²`. -/
private lemma sigma_facts :
    0 < ‖freeRho 1 ((E : ℂ) + γ * mInf)‖ ^ 2 ∧ ‖freeRho 1 ((E : ℂ) + γ * mInf)‖ ^ 2 < 1 ∧
      γ * ‖freeT 1 ((E : ℂ) + γ * mInf)‖ ^ 2 =
        (1 - ‖freeRho 1 ((E : ℂ) + γ * mInf)‖ ^ 2) / (1 + ‖freeRho 1 ((E : ℂ) + γ * mInf)‖ ^ 2) :=
            by
  have hr0 : 0 < ‖freeRho 1 ((E : ℂ) + γ * mInf)‖ := lt_of_lt_of_le (by norm_num) (h.rho_ge h.hmI)
  have hr1 := h.rho_lt h.hmI
  refine ⟨by positivity, by nlinarith, ?_⟩
  have hw := h.ward_inf
  rw [eq_div_iff (by positivity)]
  exact hw

private lemma circulant_perP0 {g : ℝ} (hb : hopB g = 1) (hγg : gammaG g = γ) [NeZero L] :
    Matrix.circulant (perP0 g L E mInf) =
      (γ * ‖freeT 1 ((E : ℂ) + γ * mInf)‖ ^ 2) • geomC (‖freeRho 1 ((E : ℂ) + γ * mInf)‖ ^ 2) L :=
          by
  ext i j
  rw [Matrix.circulant_apply, lg_perP0_eq hb hγg mInf _ (h.rho_lt h.hmI)]
  simp only [Matrix.smul_apply, geomC, Matrix.of_apply, smul_eq_mul]
  congr 1
  rw [← lgD_eq_sub_val, lg_geomV_symm]

end LgGood

/-- The line ratio `τ = e^{-λ}` of the comparison mixed kernel. -/
private def lgTau (D δ : ℝ) : ℝ := Real.exp (-lamGeo D δ)

private lemma lg_tau_facts {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) :
    0 < lgTau D δ ∧ lgTau D δ < 1 ∧ lgTau D δ + (lgTau D δ)⁻¹ = 2 + δ / D ∧
      (lgTau D δ)⁻¹ - lgTau D δ = Real.sqrt (δ * (δ + 4 * D)) / D := by
  have hlam := lg_lamGeo_pos hD hδ
  have hc := lg_cosh_lamGeo hD hδ
  have hs := lg_sqrt_eq_sinh hD hδ
  unfold lgTau
  refine ⟨Real.exp_pos _, by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith), ?_, ?_⟩
  · rw [← Real.exp_neg, neg_neg]
    have : Real.exp (-lamGeo D δ) + Real.exp (lamGeo D δ) = 2 * Real.cosh (lamGeo D δ) := by
      rw [Real.cosh_eq]; ring
    rw [this, hc]; field_simp
  · rw [← Real.exp_neg, neg_neg, hs]
    have : Real.exp (lamGeo D δ) - Real.exp (-lamGeo D δ) = 2 * Real.sinh (lamGeo D δ) := by
      rw [Real.sinh_eq]; ring
    rw [this]; field_simp

private lemma lg_lineKer_eq (D δ : ℝ) (x : ℤ) :
    lineKer D δ x = (Real.sqrt (δ * (δ + 4 * D)))⁻¹ * lgTau D δ ^ x.natAbs := by
  unfold lineKer lgTau
  rw [← Real.exp_nat_mul, div_eq_inv_mul]
  congr 2
  have : ((x.natAbs : ℕ) : ℝ) = |(x : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [this]; ring

private lemma lg_row_mul {𝕜 : Type*} [Field 𝕜] {L : ℕ} (X Y : Matrix (Fin L) (Fin L) 𝕜) (a : Fin L)
    :
    ∑ b, (X * Y) a b = ∑ c, X a c * ∑ b, Y c b := by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

namespace LgGood

variable {k γ E : ℝ} {L : ℕ} {m mInf : ℂ} (h : LgGood k γ E L m mInf)
include h

/-- The comparison mixed kernel `Ξ = tP₀(I - tP₀)⁻¹` of (A.36) [da:eq:actual-kernel-decomposition]
is the periodized line kernel
`(1-δ) e^{-λ|x|}/√(δ(δ+4D))`, and `(I - tP₀)⁻¹ = I + Ξ`. -/
private lemma xi_eq {g : ℝ} (hb : hopB g = 1) (hγg : gammaG g = γ) [NeZero L] (δ : ℝ) (hδ : 0 < δ)
    (_hδ1 : δ ≤ 1) :
    let σ := ‖freeRho 1 ((E : ℂ) + γ * mInf)‖ ^ 2
    let D := σ / (1 - σ) ^ 2
    (1 - (1 - δ) • Matrix.circulant (perP0 g L E mInf))⁻¹ =
        1 + ((1 - δ) / Real.sqrt (δ * (δ + 4 * D))) • geomC (lgTau D δ) L ∧
      (1 - (1 - δ) • Matrix.circulant (perP0 g L E mInf)) *
        (1 + ((1 - δ) / Real.sqrt (δ * (δ + 4 * D))) • geomC (lgTau D δ) L) = 1 ∧
      (1 - δ) • mixedKer (Matrix.circulant (perP0 g L E mInf)) (1 - δ) =
        ((1 - δ) / Real.sqrt (δ * (δ + 4 * D))) • geomC (lgTau D δ) L ∧
      (1 - δ) / Real.sqrt (δ * (δ + 4 * D)) * ((1 + lgTau D δ) / (1 - lgTau D δ)) =
        (1 - δ) / δ := by
  intro σ D
  obtain ⟨hσ0, hσ1, hφ⟩ := h.sigma_facts
  have hD : 0 < D := by have : 0 < 1 - σ := by linarith
                        positivity
  obtain ⟨hτ0, hτ1, hτsum, hτdiff⟩ := lg_tau_facts hD hδ
  set τ := lgTau D δ
  set S := Real.sqrt (δ * (δ + 4 * D)) with hS
  have hSpos : 0 < S := Real.sqrt_pos.mpr (by positivity)
  set φ := γ * ‖freeT 1 ((E : ℂ) + γ * mInf)‖ ^ 2 with hφdef
  have hL := h.hL
  have hσL : 1 - σ ^ L ≠ 0 := by
    have := pow_lt_one₀ hσ0.le hσ1 (show L ≠ 0 by omega); linarith
  have hτL : 1 - τ ^ L ≠ 0 := by
    have := pow_lt_one₀ hτ0.le hτ1 (show L ≠ 0 by omega); linarith
  have hστ : σ⁻¹ - σ ≠ 0 := by
    have : σ < σ⁻¹ := by
      calc σ < 1 := hσ1
        _ < σ⁻¹ := (one_lt_inv₀ hσ0).mpr hσ1
    linarith
  have hσne : σ ≠ 0 := ne_of_gt hσ0
  have h1σ : 1 - σ ≠ 0 := by linarith
  have h1σ' : 1 + σ ≠ 0 := by linarith
  have hφσ : φ * (σ⁻¹ - σ) = 1 / D := by
    rw [hφ]; simp only [D]; field_simp; ring
  have hM3 : σ + σ⁻¹ - (1 - δ) * φ * (σ⁻¹ - σ) = τ + τ⁻¹ := by
    rw [hτsum, mul_assoc, hφσ]
    simp only [D]; field_simp; ring
  have hB : (1 - δ) / S * (τ⁻¹ - τ) = (1 - δ) * φ * (σ⁻¹ - σ) := by
    rw [hτdiff, mul_assoc, hφσ]; field_simp
  have hinv := lg_geom_inv hL σ τ φ ((1 - δ) / S) (1 - δ) hσ0.ne' hσL hτ0.ne' hτL hστ hM3 hB
  have hP0 := h.circulant_perP0 hb hγg
  rw [← hφdef] at hP0
  have hsm : (1 - δ) • Matrix.circulant (perP0 g L E mInf) = ((1 - δ) * φ) • geomC σ L := by
    rw [hP0, smul_smul]
  have hinv' : (1 - (1 - δ) • Matrix.circulant (perP0 g L E mInf)) *
      (1 + ((1 - δ) / S) • geomC τ L) = 1 := by rw [hsm]; exact hinv
  have hI : (1 - (1 - δ) • Matrix.circulant (perP0 g L E mInf))⁻¹ =
      1 + ((1 - δ) / S) • geomC τ L := Matrix.inv_eq_right_inv hinv'
  refine ⟨hI, hinv', ?_, ?_⟩
  · unfold mixedKer
    rw [hI, ← Matrix.smul_mul]
    have e := hinv'
    rw [Matrix.sub_mul, Matrix.one_mul] at e
    set X := 1 + ((1 - δ) / S) • geomC τ L with hX
    set Y := (1 - δ) • Matrix.circulant (perP0 g L E mInf) * X with hY
    calc Y = X - (X - Y) := by abel
      _ = X - 1 := by rw [e]
      _ = ((1 - δ) / S) • geomC τ L := by rw [hX]; abel
  · -- row sums
    have hrow := congrArg (fun X : Matrix (Fin L) (Fin L) ℝ => ∑ b, X (0 : Fin L) b) hinv'
    rw [lg_row_mul] at hrow
    have hr1 : ∀ c : Fin L, ∑ b, (1 + ((1 - δ) / S) • geomC τ L) c b =
        1 + (1 - δ) / S * ((1 + τ) / (1 - τ)) := by
      intro c
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      rw [geomC_row_sum (by linarith : τ ≠ 1) hτL c]
      simp [Matrix.one_apply]
    simp only [hr1, ← Finset.sum_mul] at hrow
    have hs : ∑ c, (1 - (1 - δ) • Matrix.circulant (perP0 g L E mInf)) (0 : Fin L) c = δ := by
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
      have : ∑ c : Fin L, Matrix.circulant (perP0 g L E mInf) (0 : Fin L) c = 1 := by
        simp only [Matrix.circulant_apply]
        rw [← h.perP0_sum hb hγg]
        exact Fintype.sum_equiv (Equiv.subLeft (0 : Fin L))
          (fun c => perP0 g L E mInf (0 - c)) (fun x => perP0 g L E mInf x) (fun c => rfl)
      rw [this]; simp [Matrix.one_apply]
    rw [hs] at hrow
    simp only [Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at hrow
    field_simp at hrow ⊢
    linarith

end LgGood

/-! ### Weighted row norms on `ℤ_L` -/

/-- All weighted absolute rows `Σ_b e^{μ d(a,b)} |X_ab|` are at most `A`. -/
private def lgRow {L : ℕ} (μ : ℝ) (X : Matrix (Fin L) (Fin L) ℝ) (A : ℝ) : Prop :=
  ∀ a, ∑ b, Real.exp (μ * cycDist a b) * |X a b| ≤ A

section RowNorm

variable {L : ℕ} {μ : ℝ}

private lemma lgRow_one (_hμ : 0 ≤ μ) : lgRow μ (1 : Matrix (Fin L) (Fin L) ℝ) 1 := by
  intro a
  rw [Finset.sum_eq_single a]
  · simp [cycDist]
  · intro b _ hb; simp [Matrix.one_apply_ne' hb]
  · simp

private lemma lgRow_add {X Y : Matrix (Fin L) (Fin L) ℝ} {A B : ℝ} (hX : lgRow μ X A) (hY : lgRow μ
    Y B) :
    lgRow μ (X + Y) (A + B) := by
  intro a
  have h : ∀ b, Real.exp (μ * cycDist a b) * |(X + Y) a b| ≤
      Real.exp (μ * cycDist a b) * |X a b| + Real.exp (μ * cycDist a b) * |Y a b| := by
    intro b; rw [Matrix.add_apply, ← mul_add]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (Real.exp_pos _).le
  refine (Finset.sum_le_sum fun b _ => h b).trans ?_
  rw [Finset.sum_add_distrib]
  exact add_le_add (hX a) (hY a)

private lemma lgRow_smul {X : Matrix (Fin L) (Fin L) ℝ} {A : ℝ} (hX : lgRow μ X A) (c : ℝ) :
    lgRow μ (c • X) (|c| * A) := by
  intro a
  simp only [Matrix.smul_apply, smul_eq_mul, abs_mul]
  have : ∑ b, Real.exp (μ * cycDist a b) * (|c| * |X a b|) =
      |c| * ∑ b, Real.exp (μ * cycDist a b) * |X a b| := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => by ring
  rw [this]
  exact mul_le_mul_of_nonneg_left (hX a) (abs_nonneg c)

private lemma lgRow_mul (hμ : 0 ≤ μ) {X Y : Matrix (Fin L) (Fin L) ℝ} {A B : ℝ} (hX : lgRow μ X A)
    (hY : lgRow μ Y B) (hB : 0 ≤ B) : lgRow μ (X * Y) (A * B) := by
  intro a
  have h1 : ∀ c, Real.exp (μ * cycDist a c) * |(X * Y) a c| ≤
      ∑ b, (Real.exp (μ * cycDist a b) * |X a b|) * (Real.exp (μ * cycDist b c) * |Y b c|) := by
    intro c
    rw [Matrix.mul_apply]
    calc Real.exp (μ * cycDist a c) * |∑ b, X a b * Y b c|
        ≤ Real.exp (μ * cycDist a c) * ∑ b, |X a b * Y b c| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (Real.exp_pos _).le
      _ = ∑ b, Real.exp (μ * cycDist a c) * (|X a b| * |Y b c|) := by
          rw [Finset.mul_sum]; simp [abs_mul]
      _ ≤ ∑ b, (Real.exp (μ * cycDist a b) * |X a b|) * (Real.exp (μ * cycDist b c) * |Y b c|) := by
          refine Finset.sum_le_sum fun b _ => ?_
          have := lg_exp_dist_le μ hμ a b c
          calc Real.exp (μ * cycDist a c) * (|X a b| * |Y b c|)
              ≤ (Real.exp (μ * cycDist a b) * Real.exp (μ * cycDist b c)) * (|X a b| * |Y b c|) :=
                mul_le_mul_of_nonneg_right this (by positivity)
            _ = _ := by ring
  refine (Finset.sum_le_sum fun c _ => h1 c).trans ?_
  rw [Finset.sum_comm]
  have h2 : ∀ b, ∑ c, (Real.exp (μ * cycDist a b) * |X a b|) *
      (Real.exp (μ * cycDist b c) * |Y b c|) ≤ (Real.exp (μ * cycDist a b) * |X a b|) * B := by
    intro b; rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hY b) (by positivity)
  refine (Finset.sum_le_sum fun b _ => h2 b).trans ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (hX a) hB

private lemma lgRow_unweighted (hμ : 0 ≤ μ) {X : Matrix (Fin L) (Fin L) ℝ} {A : ℝ} (hX : lgRow μ X
    A)
    (a : Fin L) : ∑ b, |X a b| ≤ A := by
  refine le_trans (Finset.sum_le_sum fun b _ => ?_) (hX a)
  have : 1 ≤ Real.exp (μ * cycDist a b) := Real.one_le_exp (by positivity)
  nlinarith [abs_nonneg (X a b)]

/-- Neumann series in the weighted row norm. -/
private lemma lgRow_inv (hμ : 0 ≤ μ) {X : Matrix (Fin L) (Fin L) ℝ} (hX : lgRow μ X (1 / 2)) :
    (1 - X) * (1 - X)⁻¹ = 1 ∧ (1 - X)⁻¹ * (1 - X) = 1 ∧ lgRow μ (1 - X)⁻¹ 2 := by
  have hdet : (1 - X).det ≠ 0 := by
    apply det_ne_zero_of_sum_row_lt_diag
    intro k
    have hrow := lgRow_unweighted hμ hX k
    have hsplit := Finset.add_sum_erase Finset.univ (fun b => |X k b|) (Finset.mem_univ k)
    have hoff : ∑ j ∈ Finset.univ.erase k, ‖(1 - X) k j‖ = ∑ j ∈ Finset.univ.erase k, |X k j| := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Matrix.sub_apply, Matrix.one_apply_ne' (Finset.ne_of_mem_erase hj), zero_sub,
        Real.norm_eq_abs, abs_neg]
    rw [hoff]
    have hdiag : 1 - |X k k| ≤ ‖(1 - X) k k‖ := by
      rw [Matrix.sub_apply, Matrix.one_apply_eq, Real.norm_eq_abs]
      have := abs_sub_abs_le_abs_sub 1 (X k k); rw [abs_one] at this; linarith
    linarith
  have hU : IsUnit (1 - X).det := isUnit_iff_ne_zero.mpr hdet
  have h1 : (1 - X) * (1 - X)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hU
  have h2 : (1 - X)⁻¹ * (1 - X) = 1 := Matrix.nonsing_inv_mul _ hU
  refine ⟨h1, h2, ?_⟩
  set Y := (1 - X)⁻¹
  have hYe : Y = 1 + X * Y := by
    have : (1 - X) * Y = 1 := h1
    rw [Matrix.sub_mul, Matrix.one_mul] at this
    calc Y = (Y - X * Y) + X * Y := by abel
      _ = 1 + X * Y := by rw [this]
  rcases isEmpty_or_nonempty (Fin L) with hE | hN
  · intro a; exact (IsEmpty.false a).elim
  obtain ⟨a₀, -, ha₀⟩ := Finset.exists_max_image Finset.univ
    (fun a => ∑ b, Real.exp (μ * cycDist a b) * |Y a b|) Finset.univ_nonempty
  set A₀ := ∑ b, Real.exp (μ * cycDist a₀ b) * |Y a₀ b|
  have hYrow : lgRow μ Y A₀ := fun a => ha₀ a (Finset.mem_univ a)
  have hA0 : 0 ≤ A₀ := Finset.sum_nonneg fun b _ => by positivity
  have hXY := lgRow_mul hμ hX hYrow hA0
  have hsum := lgRow_add (lgRow_one (L := L) hμ) hXY
  rw [← hYe] at hsum
  have := hsum a₀
  have hA : A₀ ≤ 2 := by linarith
  exact fun a => (hYrow a).trans hA

private lemma lgRow_mono {X : Matrix (Fin L) (Fin L) ℝ} {A A' : ℝ} (hX : lgRow μ X A) (h : A ≤ A') :
    lgRow μ X A' := fun a => (hX a).trans h

end RowNorm

/-- Perturbation of an inverse `(I - tP₀)⁻¹ = R₀` in the weighted row norm (Neumann series). -/
private lemma lg_neumann_pert {L : ℕ} {μ t A e : ℝ} (hμ : 0 ≤ μ) (ht : 0 ≤ t) (hA : 0 ≤ A) (he0 : 0
    ≤ e)
    (P P₀ R₀ : Matrix (Fin L) (Fin L) ℝ) (hR₁ : (1 - t • P₀) * R₀ = 1)
    (hRow : lgRow μ R₀ A) (hPP : lgRow μ (P - P₀) e) (he : t * A * e ≤ 1 / 2) :
    (1 - t • P) * (1 - t • P)⁻¹ = 1 ∧ (1 - t • P)⁻¹ * (1 - t • P) = 1 ∧
      lgRow μ (1 - t • P)⁻¹ (2 * A) ∧ lgRow μ ((1 - t • P)⁻¹ - R₀) (2 * A * (t * e) * A) := by
  set X := t • (R₀ * (P - P₀)) with hXdef
  have hX : lgRow μ X (1 / 2) := by
    have h1 := lgRow_mul hμ hRow hPP he0
    have h2 := lgRow_smul h1 t
    rw [abs_of_nonneg ht] at h2
    have e1 : |t| * (A * e) = t * A * e := by rw [abs_of_nonneg ht]; ring
    exact lgRow_mono h2 (by linarith [e1])
  obtain ⟨hi1, hi2, hiRow⟩ := lgRow_inv hμ hX
  set Y := (1 - X)⁻¹ * R₀ with hYdef
  have hfac : 1 - t • P = (1 - t • P₀) * (1 - X) := by
    rw [hXdef, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, hR₁,
      Matrix.one_mul]
    rw [smul_sub]; abel
  have hY1 : (1 - t • P) * Y = 1 := by
    rw [hfac, hYdef, Matrix.mul_assoc, ← Matrix.mul_assoc (1 - X), hi1, Matrix.one_mul, hR₁]
  have hY2 : Y * (1 - t • P) = 1 := mul_eq_one_comm.mp hY1
  have hinv : (1 - t • P)⁻¹ = Y := Matrix.inv_eq_right_inv hY1
  rw [hinv]
  refine ⟨hY1, hY2, ?_, ?_⟩
  · have := lgRow_mul hμ hiRow hRow hA
    exact this
  · have hR₂ : R₀ * (1 - t • P₀) = 1 := mul_eq_one_comm.mp hR₁
    have e1 : Y - R₀ = Y * (t • (P - P₀)) * R₀ := by
      have : t • (P - P₀) = (1 - t • P₀) - (1 - t • P) := by rw [smul_sub]; abel
      rw [this, Matrix.mul_sub, Matrix.sub_mul, hY2, Matrix.one_mul, Matrix.mul_assoc, hR₁,
        Matrix.mul_one]
    rw [e1]
    have hY := lgRow_mul hμ hiRow hRow hA
    have hPt := lgRow_smul hPP t
    rw [abs_of_nonneg ht] at hPt
    have h1 := lgRow_mul hμ hY hPt (by positivity)
    exact lgRow_mul hμ h1 hRow hA

private lemma lg_geomV_nonneg (τ : ℝ) (h0 : 0 ≤ τ) (h1 : τ < 1) (L k : ℕ) (hL : L ≠ 0) :
    0 ≤ geomV τ L k := by
  unfold geomV
  have : 0 < 1 - τ ^ L := by have := pow_lt_one₀ h0 h1 hL; linarith
  positivity

/-- Weighted rows of a periodized geometric kernel `B G_τ` with row `ρ_Ξ`. -/
private lemma lg_row_xi {L : ℕ} (hL : L ≠ 0) (B τ μ : ℝ) (hB : 0 ≤ B) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hμ : 0 ≤ μ) (hcase : Real.exp μ ^ 2 * τ ≤ 1 ∨ μ * L ≤ 1) :
    lgRow μ (B • geomC τ L) (2 * (B * ((1 + τ) / (1 - τ)))) := by
  intro a
  have hnn : ∀ c, |(B • geomC τ L) a c| = B * geomV τ L (lgD L a c) := by
    intro c
    simp only [Matrix.smul_apply, geomC, Matrix.of_apply, smul_eq_mul]
    exact abs_of_nonneg (mul_nonneg hB (lg_geomV_nonneg τ hτ0.le hτ1 L _ hL))
  simp only [hnn]
  have e : ∀ c, Real.exp (μ * cycDist a c) * (B * geomV τ L (lgD L a c)) =
      B * (Real.exp (μ * cycDist a c) * geomV τ L (lgD L a c)) := fun c => by ring
  simp only [e]
  rw [← Finset.mul_sum, mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ hB
  rcases hcase with hc | hc
  · have hp : Real.exp μ * τ < 1 := by
      have h0 : 0 ≤ Real.exp μ * τ := by positivity
      have h2 : (Real.exp μ * τ) ^ 2 < 1 := by
        have : (Real.exp μ * τ) ^ 2 = (Real.exp μ ^ 2 * τ) * τ := by ring
        rw [this]; nlinarith
      nlinarith
    refine (lg_row_geomV a μ τ hμ hτ0.le hp).trans ?_
    exact lg_ratio_le _ _ (by positivity) (by nlinarith) hτ1
  · have hw : ∀ c, Real.exp (μ * cycDist a c) ≤ 2 := by
      intro c
      have h1 : μ * cycDist a c ≤ 1 / 2 := by
        have := cycDist_le_half a c
        have h2 : (2 * cycDist a c : ℕ) ≤ (L : ℝ) := by exact_mod_cast this
        push_cast at h2
        nlinarith
      calc Real.exp (μ * cycDist a c) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr h1
        _ ≤ 2 := by
          have := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 2) (by norm_num) (by norm_num)
          linarith
    have hsum : ∑ c, geomV τ L (lgD L a c) = (1 + τ) / (1 - τ) := by
      rw [sum_lgD_row a (fun k => geomV τ L k), sum_geomV (ne_of_lt hτ1)
        (by have := pow_lt_one₀ hτ0.le hτ1 hL; linarith)]
    calc ∑ c, Real.exp (μ * cycDist a c) * geomV τ L (lgD L a c)
        ≤ ∑ c, 2 * geomV τ L (lgD L a c) := Finset.sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_right (hw c) (lg_geomV_nonneg τ hτ0.le hτ1 L _ hL)
      _ = 2 * ((1 + τ) / (1 - τ)) := by rw [← Finset.mul_sum, hsum]

namespace LgGood

variable {k γ E : ℝ} {L : ℕ} {m mInf : ℂ} (h : LgGood k γ E L m mInf)
include h

private lemma D_bounds :
    k ^ 4 / 1024 * (γ⁻¹) ^ 2 ≤ ‖freeRho 1 ((E : ℂ) + γ * mInf)‖ ^ 2 /
      (1 - ‖freeRho 1 ((E : ℂ) + γ * mInf)‖ ^ 2) ^ 2 ∧
    ‖freeRho 1 ((E : ℂ) + γ * mInf)‖ ^ 2 / (1 - ‖freeRho 1 ((E : ℂ) + γ * mInf)‖ ^ 2) ^ 2 ≤
      262144 / k ^ 2 * (γ⁻¹) ^ 2 := by
  have hk := h.hk
  have hγ := h.hγ
  have hlo := h.gap_ge h.hmI
  have hhi := h.gap_le h.hmI
  have hr := h.rho_ge h.hmI
  have hr1 := h.rho_lt h.hmI
  set σ := ‖freeRho 1 ((E : ℂ) + γ * mInf)‖ ^ 2
  have hσ16 : 1 / 16 ≤ σ := by nlinarith
  have hσ1 : σ ≤ 1 := by nlinarith [norm_nonneg (freeRho 1 ((E : ℂ) + γ * mInf))]
  have hd0 : 0 < 1 - σ := lt_of_lt_of_le (by positivity) hlo
  constructor
  · rw [le_div_iff₀ (by positivity)]
    have h1 : (1 - σ) ^ 2 ≤ (8 * γ / k ^ 2) ^ 2 := pow_le_pow_left₀ hd0.le hhi 2
    calc k ^ 4 / 1024 * γ⁻¹ ^ 2 * (1 - σ) ^ 2 ≤ k ^ 4 / 1024 * γ⁻¹ ^ 2 * (8 * γ / k ^ 2) ^ 2 := by
          gcongr
      _ = 1 / 16 := by field_simp; norm_num
      _ ≤ σ := hσ16
  · rw [div_le_iff₀ (by positivity)]
    have h1 : (γ * k / 512) ^ 2 ≤ (1 - σ) ^ 2 := pow_le_pow_left₀ (by positivity) hlo 2
    calc σ ≤ 1 := hσ1
      _ = 262144 / k ^ 2 * γ⁻¹ ^ 2 * (γ * k / 512) ^ 2 := by field_simp; norm_num
      _ ≤ 262144 / k ^ 2 * γ⁻¹ ^ 2 * (1 - σ) ^ 2 := by gcongr

omit h in
private lemma xi_entry [NeZero L] (δ D : ℝ) (hD : 0 < D) (hδ : 0 < δ) (a b : Fin L) :
    (1 - δ) / Real.sqrt (δ * (δ + 4 * D)) * geomV (lgTau D δ) L (lgD L a b) =
      perLine (fun x => (1 - δ) * lineKer D δ x) L (b - a) := by
  have e : (fun x : ℤ => (1 - δ) * lineKer D δ x) =
      fun x : ℤ => ((1 - δ) / Real.sqrt (δ * (δ + 4 * D))) * lgTau D δ ^ x.natAbs := by
    funext x; rw [lg_lineKer_eq]; ring
  obtain ⟨hτ0, hτ1, -, -⟩ := lg_tau_facts hD hδ
  rw [e, lg_perLine_geom _ _ hτ0.le hτ1, lgD_eq_sub_val]

end LgGood

private lemma lg_finRotate_sub {L : ℕ} [NeZero L] (a b : Fin L) :
    finRotate L b - a = finRotate L (b - a) := by
  rw [finRotate_apply, finRotate_apply]; abel

/-- Reindexing rows of circulant profiles: `Σ_b F(b - a) = Σ_y F(y)`. -/
private lemma lg_sum_sub {L : ℕ} [NeZero L] (a : Fin L) (F : Fin L → ℝ) : ∑ b, F (b - a) = ∑ y, F y
    :=
  Fintype.sum_equiv (Equiv.subRight a) _ _ (fun _ => rfl)

namespace LgGood

variable {k γ E : ℝ} {L : ℕ} {m mInf : ℂ} (h : LgGood k γ E L m mInf)
include h

/-- The mixed comparison kernel `Ξ` of (A.36) [da:eq:actual-kernel-decomposition]: (A.38)
[uvp:eq:xi]–(A.40)
[uvp:eq:xi2] and the weighted row of `I + Ξ` in (A.43)
[da:eq:weighted-actual-kernels]. -/
private lemma xi_pack {g : ℝ} (hb : hopB g = 1) (hγg : gammaG g = γ) [NeZero L] (hg1 : 1 ≤ g)
    (hγdef : γ = (g ^ 2)⁻¹) (hLg : g ^ 2 ≤ L) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (CG : ℝ)
    (hCG : 0 < CG)
    (HG : ∀ (a D δ : ℝ) (L : ℕ), 1 ≤ a → k ^ 4 / 1024 * a ^ 2 ≤ D → D ≤ 262144 / k ^ 2 * a ^ 2 →
      a ≤ L → 0 < δ → δ ≤ 1 →
      let Ξ := perLine (fun x => (1 - δ) * lineKer D δ x) L
      let lam := lamGeo D δ
      let ℓ := min (L : ℝ) (a / Real.sqrt δ)
      (lam ≤ CG * Real.sqrt δ / a ∧ Real.sqrt δ / a ≤ CG * lam) ∧
      ∑ x, Ξ x ≤ CG / δ ∧ (∀ x, Ξ x ≤ CG / (δ * ℓ)) ∧
      ∑ x, |Ξ (finRotate L x) - Ξ x| ≤ CG * lam / δ ∧
      (∀ x, |Ξ (finRotate L x) - Ξ x| ≤ CG * lam / (δ * ℓ)) ∧
      ∑ x, |Ξ (finRotate L (finRotate L x)) - 2 * Ξ (finRotate L x) + Ξ x| ≤
        CG * lam ^ 2 / δ) :
    let Ξ := (1 - δ) • mixedKer (Matrix.circulant (perP0 g L E mInf)) (1 - δ)
    let ℓ := min (L : ℝ) (g ^ 2 / Real.sqrt δ)
    let lam := Real.sqrt δ / g ^ 2
    (∀ a b, 0 ≤ Ξ a b) ∧ (∀ a, ∑ b, Ξ a b = (1 - δ) / δ) ∧
    (∀ a, ∑ b, Ξ a b ≤ CG / δ) ∧ (∀ a b, Ξ a b ≤ CG / (δ * ℓ)) ∧
    (∀ a, ∑ b, |Ξ a (finRotate L b) - Ξ a b| ≤ CG ^ 2 * lam / δ) ∧
    (∀ a b, |Ξ a (finRotate L b) - Ξ a b| ≤ CG ^ 2 * lam / (δ * ℓ)) ∧
    (∀ a, ∑ b, |Ξ a (finRotate L (finRotate L b)) - 2 * Ξ a (finRotate L b) + Ξ a b| ≤
      CG ^ 3 * lam ^ 2 / δ) ∧
    (1 - (1 - δ) • Matrix.circulant (perP0 g L E mInf))⁻¹ = 1 + Ξ ∧
    (1 - (1 - δ) • Matrix.circulant (perP0 g L E mInf)) * (1 + Ξ) = 1 ∧
    ∀ c : ℝ, 0 < c → c ≤ 1 → c ≤ 1 / (4 * CG) → lgRow (c / ℓ) (1 + Ξ) (1 + 2 * ((1 - δ) / δ)) := by
  intro Ξ ℓ lam
  obtain ⟨hI, hprod, hXi, hrowΞ⟩ := h.xi_eq hb hγg δ hδ hδ1
  obtain ⟨hσ0, hσ1, -⟩ := h.sigma_facts
  set σ := ‖freeRho 1 ((E : ℂ) + γ * mInf)‖ ^ 2 with hσdef
  set D := σ / (1 - σ) ^ 2 with hDdef
  have hD : 0 < D := by have : 0 < 1 - σ := by linarith
                        positivity
  obtain ⟨hτ0, hτ1, -, -⟩ := lg_tau_facts hD hδ
  set τ := lgTau D δ with hτdef
  set S := Real.sqrt (δ * (δ + 4 * D)) with hSdef
  have hSpos : 0 < S := Real.sqrt_pos.mpr (by positivity)
  have hB0 : 0 ≤ (1 - δ) / S := div_nonneg (by linarith) hSpos.le
  have hXieq : Ξ = ((1 - δ) / S) • geomC τ L := hXi
  have hL0 : L ≠ 0 := NeZero.ne L
  -- entries of `Ξ`
  have hent : ∀ a b, Ξ a b = perLine (fun x => (1 - δ) * lineKer D δ x) L (b - a) := by
    intro a b
    rw [hXieq]
    simp only [Matrix.smul_apply, geomC, Matrix.of_apply, smul_eq_mul]
    exact LgGood.xi_entry δ D hD hδ a b
  -- geometric bounds
  obtain ⟨hDlo, hDhi⟩ := h.D_bounds
  have hγinv : γ⁻¹ = g ^ 2 := by rw [hγdef, inv_inv]
  rw [hγinv] at hDlo hDhi
  have hg2 : 1 ≤ g ^ 2 := by nlinarith
  obtain ⟨⟨hlam1, hlam2⟩, hG1, hG2, hG3, hG4, hG5⟩ := HG (g ^ 2) D δ L hg2 hDlo hDhi hLg hδ hδ1
  set Ξf := perLine (fun x => (1 - δ) * lineKer D δ x) L with hΞf
  have hlamG : lamGeo D δ ≤ CG * lam := by
    simp only [lam]; rw [← mul_div_assoc]; exact hlam1
  have hlam0 : 0 ≤ lam := by positivity
  have hδℓ : 0 < δ * ℓ := by
    have : 0 < ℓ := lt_min (by have := Nat.pos_of_ne_zero hL0; exact_mod_cast this)
      (by positivity)
    positivity
  have hΞnn : ∀ a b, 0 ≤ Ξ a b := by
    intro a b; rw [hXieq]
    simp only [Matrix.smul_apply, geomC, Matrix.of_apply, smul_eq_mul]
    exact mul_nonneg hB0 (lg_geomV_nonneg τ hτ0.le hτ1 L _ hL0)
  have hΞrow : ∀ a, ∑ b, Ξ a b = (1 - δ) / δ := by
    intro a; rw [hXieq]
    simp only [Matrix.smul_apply, geomC, Matrix.of_apply, smul_eq_mul]
    rw [← Finset.mul_sum, sum_lgD_row a (fun k => geomV τ L k), sum_geomV (ne_of_lt hτ1)
      (by have := pow_lt_one₀ hτ0.le hτ1 hL0; linarith)]
    exact hrowΞ
  refine ⟨hΞnn, hΞrow, fun a => ?_, fun a b => ?_, fun a => ?_, fun a b => ?_, fun a => ?_, ?_, ?_,
    fun c hc hc1 hcG => ?_⟩
  · simp only [hent]; rw [lg_sum_sub a (fun y => Ξf y)]; exact hG1
  · rw [hent]; exact hG2 _
  · simp only [hent, lg_finRotate_sub]
    rw [lg_sum_sub a (fun y => |Ξf (finRotate L y) - Ξf y|)]
    refine hG3.trans ?_
    calc CG * lamGeo D δ / δ ≤ CG * (CG * lam) / δ := by gcongr
      _ = CG ^ 2 * lam / δ := by ring
  · rw [hent, hent, lg_finRotate_sub]
    refine (hG4 _).trans ?_
    calc CG * lamGeo D δ / (δ * ℓ) ≤ CG * (CG * lam) / (δ * ℓ) := by gcongr
      _ = CG ^ 2 * lam / (δ * ℓ) := by ring
  · simp only [hent, lg_finRotate_sub]
    rw [lg_sum_sub a (fun y => |Ξf (finRotate L (finRotate L y)) - 2 * Ξf (finRotate L y) + Ξf y|)]
    refine hG5.trans ?_
    have hl0 : 0 ≤ lamGeo D δ := (lg_lamGeo_pos hD hδ).le
    calc CG * lamGeo D δ ^ 2 / δ ≤ CG * (CG * lam) ^ 2 / δ := by gcongr
      _ = CG ^ 3 * lam ^ 2 / δ := by ring
  · rw [hI, hXieq]
  · rw [hXieq]; exact hprod
  · have hℓ0 : 0 < ℓ := by
      have : 0 < δ * ℓ := hδℓ
      exact pos_of_mul_pos_right this hδ.le
    have hμ : 0 ≤ c / ℓ := by positivity
    have hcase : Real.exp (c / ℓ) ^ 2 * τ ≤ 1 ∨ c / ℓ * L ≤ 1 := by
      rcases le_total (L : ℝ) (g ^ 2 / Real.sqrt δ) with hcap | hcap
      · right
        have : ℓ = L := min_eq_left hcap
        rw [this, div_mul_cancel₀ _ (by simpa [this] using hℓ0.ne')]
        exact hc1
      · left
        have hℓe : ℓ = g ^ 2 / Real.sqrt δ := min_eq_right hcap
        have hsδ : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
        have hlampos : 0 < lamGeo D δ := lg_lamGeo_pos hD hδ
        have h2μ : 2 * (c / ℓ) ≤ lamGeo D δ := by
          rw [hℓe, div_div_eq_mul_div]
          have h1 : Real.sqrt δ / g ^ 2 ≤ CG * lamGeo D δ := hlam2
          have h2 : 2 * (c * Real.sqrt δ / g ^ 2) ≤ 2 * (1 / (4 * CG)) * (Real.sqrt δ / g ^ 2) := by
            rw [show 2 * (c * Real.sqrt δ / g ^ 2) = 2 * c * (Real.sqrt δ / g ^ 2) by ring]
            gcongr
          have h3 : 2 * (1 / (4 * CG)) * (Real.sqrt δ / g ^ 2) ≤
              2 * (1 / (4 * CG)) * (CG * lamGeo D δ) := by gcongr
          have h4 : 2 * (1 / (4 * CG)) * (CG * lamGeo D δ) = lamGeo D δ / 2 := by
            field_simp; ring
          linarith
        rw [hτdef, lgTau, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        push_cast
        linarith
    have hx := lg_row_xi hL0 ((1 - δ) / S) τ (c / ℓ) hB0 hτ0 hτ1 hμ hcase
    rw [hrowΞ, ← hXieq] at hx
    exact lgRow_add (lgRow_one hμ) hx

end LgGood

namespace LgGood

variable {k γ E : ℝ} {L : ℕ} {m mInf : ℂ} (h : LgGood k γ E L m mInf)
include h

/-- The comparison kernel `P₀` against the actual `P`: (A.14) [uvp:eq:finiteerror] in the norms of
Lemma A.9 [uvp:lem:perturb], and the resulting bound (A.41) [uvp:eq:error] on
`t(P(I-tP)⁻¹ - P₀(I-tP₀)⁻¹)`. -/
private lemma err_pack {g : ℝ} (hb : hopB g = 1) (hγg : gammaG g = γ) [NeZero L]
    (hγdef : γ = (g ^ 2)⁻¹) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    let P := pairP γ (dysonMat 1 γ L E m)
    let P₀ := Matrix.circulant (perP0 g L E mInf)
    let εt := 10000000000 / k ^ 6 * (1 + γ * L) * Real.exp (-(3 * k / 4096 * (γ * L)))
    (∀ a b, 0 ≤ P₀ a b) ∧ (∀ a, ∑ b, P₀ a b = 1) ∧ P₀.transpose = P₀ ∧
    (∀ μ : ℝ, 0 ≤ μ → μ ≤ γ * k / 2048 → lgRow μ (P - P₀) εt) ∧
    (∀ a, ∑ b, |P a b - P₀ a b| ≤ εt) ∧ (∀ a b, |P a b - P₀ a b| ≤ εt / g ^ 2) ∧
    (∀ x, ∑ y, |(1 - δ) * (mixedKer P (1 - δ) x y - mixedKer P₀ (1 - δ) x y)| ≤ εt / δ ^ 2) ∧
    (∀ x y, |(1 - δ) * (mixedKer P (1 - δ) x y - mixedKer P₀ (1 - δ) x y)| ≤
      εt / (g ^ 2 * δ ^ 2)) := by
  intro P P₀ εt
  have hk := h.hk
  have hk1 := h.hk1
  have hγ := h.hγ
  have hP0ab : ∀ a b, P₀ a b = perP0 g L E mInf (b - a) := by
    intro a b
    simp only [P₀, Matrix.circulant_apply]
    rw [← neg_sub, h.perP0_even hb hγg]
  have hnn : ∀ a b, 0 ≤ P₀ a b := fun a b => by rw [hP0ab]; exact h.perP0_nonneg hb hγg _
  have hrow : ∀ a, ∑ b, P₀ a b = 1 := by
    intro a; simp only [hP0ab]
    rw [lg_sum_sub a (fun y => perP0 g L E mInf y)]; exact h.perP0_sum hb hγg
  have hsym : P₀.transpose = P₀ := by
    ext a b; rw [Matrix.transpose_apply, hP0ab, hP0ab, ← neg_sub, h.perP0_even hb hγg]
  have hwr : ∀ μ : ℝ, 0 ≤ μ → μ ≤ γ * k / 2048 → lgRow μ (P - P₀) εt := by
    intro μ hμ0 hμ a
    have := h.P_sub_row hb hγg a μ hμ0 hμ
    simp only [Matrix.sub_apply, hP0ab]
    exact this
  have hunw : ∀ a, ∑ b, |P a b - P₀ a b| ≤ εt := by
    intro a
    have := lgRow_unweighted le_rfl (hwr 0 le_rfl (by positivity)) a
    simpa using this
  have hεtZ : 3400000 / k ^ 5 * Real.exp (-(k / 1024 * (γ * L))) ≤ εt := by
    have hH : 0 ≤ γ * L := by positivity
    have h1 : Real.exp (-(k / 1024 * (γ * L))) ≤ Real.exp (-(3 * k / 4096 * (γ * L))) := by
      apply Real.exp_le_exp.mpr; nlinarith
    have h2 : 3400000 / k ^ 5 ≤ 10000000000 / k ^ 6 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : k ^ 6 ≤ k ^ 5 := pow_le_pow_of_le_one hk.le hk1 (by norm_num)
      nlinarith [pow_pos hk 5]
    calc 3400000 / k ^ 5 * Real.exp (-(k / 1024 * (γ * L)))
        ≤ 10000000000 / k ^ 6 * 1 * Real.exp (-(3 * k / 4096 * (γ * L))) := by
          rw [mul_one]; gcongr
      _ ≤ εt := by
          change _ ≤ 10000000000 / k ^ 6 * (1 + γ * L) * Real.exp (-(3 * k / 4096 * (γ * L)))
          gcongr
          linarith
  have hpt : ∀ a b, |P a b - P₀ a b| ≤ εt / g ^ 2 := by
    intro a b
    rw [hP0ab]
    refine (h.P_sub_pt hb hγg a b).trans ?_
    have e : εt / g ^ 2 = εt * γ := by rw [hγdef, div_eq_mul_inv]
    rw [e]
    calc 3400000 / k ^ 5 * γ * Real.exp (-(k / 1024 * (γ * L)))
        = γ * (3400000 / k ^ 5 * Real.exp (-(k / 1024 * (γ * L)))) := by ring
      _ ≤ γ * εt := by gcongr
      _ = εt * γ := by ring
  have hPnn : ∀ a b, 0 ≤ P a b := fun a b => h.P_nonneg a b
  have hProw : ∀ a, ∑ b, P a b = 1 :=
    fun a => pairP_row_sum 1 γ hγ L (by have := h.hL; omega) E m h.hroot a
  have hg2 : 0 < g ^ 2 := by
    have : 0 < (g ^ 2)⁻¹ := hγdef ▸ hγ
    exact inv_pos.mp this
  obtain ⟨k1, k2⟩ := kernel_perturb P₀ P hnn hPnn hrow hProw hsym εt (g ^ 2) δ hg2 hδ hδ1 hunw hpt
  exact ⟨hnn, hrow, hsym, hwr, hunw, hpt, k1, k2⟩

end LgGood

/-- For `C ≥ 1`, `c > 0` there is `R₂` with `C (1 + H)^C e^{-cH/2} ≤ c` for `H ≥ R₂`. -/
private lemma lg_tail_rpow (C c : ℝ) (hC : 1 ≤ C) (hc : 0 < c) :
    ∃ R₂ : ℝ, 0 ≤ R₂ ∧ ∀ H : ℝ, R₂ ≤ H →
      C * (1 + H) ^ C * Real.exp (-(c / 2 * H)) ≤ c := by
  set K : ℝ := C * (Real.log (2 * C / (c / 2)) - 1) with hK
  set M : ℝ := C * Real.exp (c / 4 + K) with hM
  have hMp : 0 < M := by positivity
  refine ⟨max 0 (4 / c * Real.log (M / c)), le_max_left _ _, fun H hH => ?_⟩
  have hH0 : 0 ≤ H := le_trans (le_max_left _ _) hH
  have hH1 : 4 / c * Real.log (M / c) ≤ H := le_trans (le_max_right _ _) hH
  have hlog := lg_log_le C (c / 2) (1 + H) (by linarith) (by positivity) (by linarith)
  have hpow : (1 + H) ^ C ≤ Real.exp (c / 4 * (1 + H) + K) := by
    rw [Real.rpow_def_of_pos (by linarith), Real.exp_le_exp, mul_comm]
    have e : c / 2 / 2 * (1 + H) = c / 4 * (1 + H) := by ring
    rw [hK]; linarith
  have hlogle : Real.log (M / c) ≤ c / 4 * H := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hc] at hH1; linarith
  calc C * (1 + H) ^ C * Real.exp (-(c / 2 * H))
      ≤ C * Real.exp (c / 4 * (1 + H) + K) * Real.exp (-(c / 2 * H)) := by gcongr
    _ = M * Real.exp (-(c / 4 * H)) := by
        rw [hM, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ M * Real.exp (-Real.log (M / c)) := by gcongr
    _ = c := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp

set_option maxHeartbeats 4000000 in
-- the many explicit estimates of this proof exceed the default heartbeat limit
/-- The statement of Lemma A.10 [uvp:lem:actual-kernels] at large coupling. -/
private theorem lg_actual_kernels_aux (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ R c C : ℝ, 1 ≤ Cκ ∧ 0 < R ∧ 0 < c ∧ 0 < C ∧
      ∀ g : ℝ, Cκ ≤ g → ∀ L : ℕ, ∀ E : ℝ, |E| ≤ 2 - κ →
      ∀ m mInf : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m →
      (0 < mInf.im ∧ mInf = dysonRHS g E mInf) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → R * (1 + |Real.log δ|) ≤ L / g ^ 2 →
      let P := pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)
      let Ξ := (1 - δ) • mixedKer (Matrix.circulant (perP0 g L E mInf)) (1 - δ)
      let 𝓔 := (1 - (1 - δ) • P)⁻¹ - 1 - Ξ
      let ℓ := min (L : ℝ) (g ^ 2 / Real.sqrt δ)
      let lam := Real.sqrt δ / g ^ 2
      let ε := epsL C c g L
      ε ≤ c * δ ^ 2 ∧
      (∀ a b, 0 ≤ mixedKer P (1 - δ) a b ∧ mixedKer P (1 - δ) a b ≤ C / (δ * ℓ)) ∧
      (∀ a, ∑ b, Ξ a b ≤ C / δ) ∧ (∀ a b, Ξ a b ≤ C / (δ * ℓ)) ∧
      (∀ a, ∑ b, |Ξ a (finRotate L b) - Ξ a b| ≤ C * lam / δ) ∧
      (∀ a b, |Ξ a (finRotate L b) - Ξ a b| ≤ C * lam / (δ * ℓ)) ∧
      (∀ a, ∑ b, |Ξ a (finRotate L (finRotate L b)) - 2 * Ξ a (finRotate L b) + Ξ a b| ≤
        C * lam ^ 2 / δ) ∧
      (∀ a, ∑ b, |𝓔 a b| ≤ C * ε / δ ^ 2) ∧ (∀ a b, |𝓔 a b| ≤ C * ε / (g ^ 2 * δ ^ 2)) ∧
      (ℓ ≤ ellProp g L (1 - δ) ∧ ellProp g L (1 - δ) ≤ 2 * ℓ) ∧
      (∀ a, ∑ b, Real.exp (c * cycDist a b / ℓ) * (|(1 + Ξ) a b| + |(1 - (1 - δ) • P)⁻¹ a b|) ≤
        C / δ) ∧
      (∀ a, ∑ b, Real.exp (c * cycDist a b / ℓ) * |𝓔 a b| ≤ C * ε / δ ^ 2) ∧
      1 ≤ g ^ 2 / (δ * ℓ) ∧ (∀ a, ∑ b, |𝓔 a b| ≤ C) ∧
      (∀ a x, ∑ b, Real.exp (-(c * cycDist x b / g ^ 2)) *
        |(1 : Matrix (Fin L) (Fin L) ℝ) a b| ≤ C * (g ^ 2 / (δ * ℓ))) ∧
      (∀ a x, ∑ b, Real.exp (-(c * cycDist x b / g ^ 2)) * |Ξ a b| ≤ C * (g ^ 2 / (δ * ℓ))) ∧
      (∀ a x, ∑ b, Real.exp (-(c * cycDist x b / g ^ 2)) * |𝓔 a b| ≤ C * (g ^ 2 / (δ * ℓ))) ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ a x, ∑ b, Real.exp (-(c * cycDist x b / g ^ 2)) *
        ‖(1 - (t : ℂ) • pairQ (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))⁻¹ a b‖ ≤
          C * (g ^ 2 / (δ * ℓ)) := by 
  have hk : 0 < κ / 2 := by linarith
  have hk1 : κ / 2 ≤ 1 := by linarith
  obtain ⟨Rs, hRs3, hRs⟩ := lg_setup hκ hκ2
  set k := κ / 2 with hkdef
  have hκ12 : k ^ 4 / 1024 ≤ 262144 / k ^ 2 := by
    have : k ^ 4 ≤ 1 := pow_le_one₀ hk.le hk1
    have : k ^ 2 ≤ 1 := pow_le_one₀ hk.le hk1
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  obtain ⟨CG, hCG, HG⟩ := geom_bounds (k ^ 4 / 1024) (262144 / k ^ 2) (by positivity) hκ12
  set c : ℝ := min (k / 2048) (1 / (4 * CG)) with hcdef
  have hc0 : 0 < c := lt_min (by positivity) (by positivity)
  have hck : c ≤ k / 2048 := min_le_left _ _
  have hcG : c ≤ 1 / (4 * CG) := min_le_right _ _
  have hc1 : c ≤ 1 := by linarith
  set C : ℝ := 10000000000 / k ^ 7 + CG ^ 3 + CG ^ 2 + 4 * CG / c + 2 * CG + 64 / k ^ 2 + 100
    with hCdef
  have hk7 : 0 < k ^ 7 := by positivity
  have hCpos : ∀ x : ℝ, x ∈ ({10000000000 / k ^ 7, CG ^ 3, CG ^ 2, 4 * CG / c, 2 * CG, 64 / k ^ 2,
      100} : Set ℝ) → x ≤ C := by
    have h1 : 0 ≤ 10000000000 / k ^ 7 := by positivity
    have h2 : 0 ≤ CG ^ 3 := by positivity
    have h3 : 0 ≤ CG ^ 2 := by positivity
    have h4 : 0 ≤ 4 * CG / c := by positivity
    have h5 : 0 ≤ 2 * CG := by positivity
    have h6 : 0 ≤ 64 / k ^ 2 := by positivity
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [hCdef] <;> linarith
  have hC100 : 100 ≤ C := hCpos 100 (by simp)
  have hC2 : 2 * CG + 100 ≤ C := by
    have h1 : 0 ≤ 10000000000 / k ^ 7 := by positivity
    have h2 : 0 ≤ CG ^ 3 := by positivity
    have h3 : 0 ≤ CG ^ 2 := by positivity
    have h4 : 0 ≤ 4 * CG / c := by positivity
    have h6 : 0 ≤ 64 / k ^ 2 := by positivity
    simp only [hCdef]; linarith
  have hC1 : 1 ≤ C := by linarith
  obtain ⟨R₂, hR₂0, hR₂⟩ := lg_tail_rpow C c hC1 hc0
  set R : ℝ := max Rs (max (4 / c) R₂) with hRdef
  have hRsR : Rs ≤ R := le_max_left _ _
  have hR4 : 4 / c ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
  have hR2 : R₂ ≤ R := le_trans (le_max_right _ _) (le_max_right _ _)
  have hR0 : 0 < R := by linarith
  refine ⟨1000 / k ^ 5, R, c, C, ?_, hR0, hc0, by linarith, ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    have : k ^ 5 ≤ 1 := pow_le_one₀ hk.le hk1
    linarith
  intro g hg L E hE m mInf hm hmI δ hδ hδ1 hRδ
  have habs : 1 ≤ 1 + |Real.log δ| := by have := abs_nonneg (Real.log δ); linarith
  have hRL : R ≤ (L : ℝ) / g ^ 2 := le_trans (le_mul_of_one_le_right hR0.le habs) hRδ
  have hg0 : 0 < g := by
    have : 1 ≤ 1000 / k ^ 5 := by
      rw [le_div_iff₀ (by positivity)]; have : k ^ 5 ≤ 1 := pow_le_one₀ hk.le hk1
      linarith
    linarith
  have hg2 : 0 < g ^ 2 := by positivity
  have hLg : Rs * g ^ 2 ≤ L := by
    have := le_trans hRsR hRL; rwa [le_div_iff₀ hg2] at this
  obtain ⟨hg1, hb, hγg, -, -, hgood⟩ := hRs g hg L hLg E hE
  rw [hb, hγg] at hm
  obtain ⟨hmIpos, hmIeq⟩ := hmI
  rw [dysonRHS_eq_freeT, hb, hγg] at hmIeq
  have h := hgood m mInf hm hmIpos hmIeq
  set γ : ℝ := (g ^ 2)⁻¹ with hγdef
  have hγ := h.hγ
  have hL3 := h.hL
  have : NeZero L := ⟨by omega⟩
  intro P Ξ 𝓔 ℓ lam ε
  have hP : P = pairP γ (dysonMat 1 γ L E m) := by simp only [P, hb, hγg]
  -- scale facts
  have hsδ : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hsδ1 : Real.sqrt δ ≤ 1 := Real.sqrt_le_one.mpr hδ1
  have hg2L : g ^ 2 ≤ L := by
    have : Rs * g ^ 2 ≥ 1 * g ^ 2 := by gcongr; linarith
    linarith
  have hℓg : g ^ 2 ≤ ℓ := by
    apply le_min hg2L
    rw [le_div_iff₀ hsδ]; nlinarith
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le hg2 hℓg
  have hδℓ0 : 0 < δ * ℓ := by positivity
  have hδℓ : δ * ℓ ≤ g ^ 2 := by
    have h1 : ℓ ≤ g ^ 2 / Real.sqrt δ := min_le_right _ _
    have h2 : δ * ℓ ≤ δ * (g ^ 2 / Real.sqrt δ) := by gcongr
    have h3 : δ * (g ^ 2 / Real.sqrt δ) = Real.sqrt δ * g ^ 2 := by
      field_simp; rw [Real.sq_sqrt hδ.le]
    nlinarith
  have hA1 : 1 ≤ g ^ 2 / (δ * ℓ) := by rw [le_div_iff₀ hδℓ0]; linarith
  -- comparison kernel and error
  obtain ⟨hΞnn, hΞrow, hK3, hK4, hK5, hK6, hK7, hI0, hprod0, hΞw⟩ :=
    h.xi_pack hb hγg hg1 hγdef hg2L δ hδ hδ1 CG hCG HG
  clear HG hRs hgood
  obtain ⟨hP0nn, hP0row, hP0sym, hPw, hPunw, hPpt, hE1, hE2⟩ := h.err_pack hb hγg hγdef δ hδ hδ1
  set εt : ℝ := 10000000000 / k ^ 6 * (1 + γ * L) * Real.exp (-(3 * k / 4096 * (γ * L)))
    with hεt
  have hH : (L : ℝ) / g ^ 2 = γ * L := by rw [hγdef]; ring
  have hH0 : 0 ≤ γ * L := by positivity
  -- `εt ≤ ε ≤ c δ²`
  have hεt0 : 0 ≤ εt := by positivity
  have hεtε : εt ≤ ε := by
    simp only [ε, epsL, hH]
    have h1 : 10000000000 / k ^ 6 ≤ C := by
      refine le_trans ?_ (hCpos (10000000000 / k ^ 7) (by simp))
      exact div_le_div_of_nonneg_left (by norm_num) hk7 (pow_le_pow_of_le_one hk.le hk1 (by
          norm_num))
    have h2 : 1 + γ * L ≤ (1 + γ * L) ^ C := by
      simpa using Real.rpow_le_rpow_of_exponent_le (show 1 ≤ 1 + γ * L by linarith) hC1
    have h3 : Real.exp (-(3 * k / 4096 * (γ * L))) ≤ Real.exp (-(c * L / g ^ 2)) := by
      apply Real.exp_le_exp.mpr
      rw [show c * L / g ^ 2 = c * (γ * L) by rw [hγdef]; ring]
      have h4 : c ≤ 3 * k / 4096 := by linarith
      have h5 := mul_le_mul_of_nonneg_right h4 hH0
      linarith
    simp only [hεt]
    exact mul_le_mul (mul_le_mul h1 h2 (by linarith) (by linarith)) h3 (Real.exp_pos _).le
      (by positivity)
  have hK1 : ε ≤ c * δ ^ 2 := by
    simp only [ε, epsL, hH]
    have hHR : R ≤ γ * L := hH ▸ hRL
    have h1 := hR₂ (γ * L) (le_trans hR2 hHR)
    have hlogδ : -(γ * L) / R ≤ Real.log δ := by
      have h2 : R * |Real.log δ| ≤ γ * L := by
        have := hRδ; rw [hH] at this; nlinarith [abs_nonneg (Real.log δ)]
      have h3 : |Real.log δ| ≤ γ * L / R := by rw [le_div_iff₀ hR0]; linarith
      have h4 := neg_abs_le (Real.log δ)
      have : -(γ * L / R) ≤ Real.log δ := by linarith
      rwa [neg_div]
    have hδexp : Real.exp (-(γ * L) / R) ≤ δ := by
      calc Real.exp (-(γ * L) / R) ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr hlogδ
        _ = δ := Real.exp_log hδ
    have hδ2 : Real.exp (-(c / 2 * (γ * L))) ≤ δ ^ 2 := by
      have h5 : Real.exp (-(c / 2 * (γ * L))) ≤ Real.exp (-(γ * L) / R) ^ 2 := by
        rw [← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have : 2 / R ≤ c / 2 := by
          rw [div_le_iff₀ hR0]; rw [div_le_iff₀ hc0] at hR4; nlinarith
        push_cast
        rw [show (2 : ℝ) * (-(γ * L) / R) = -(2 / R * (γ * L)) by ring]
        nlinarith
      exact h5.trans (pow_le_pow_left₀ (Real.exp_pos _).le hδexp 2)
    have e : C * (1 + γ * L) ^ C * Real.exp (-(c * L / g ^ 2)) =
        (C * (1 + γ * L) ^ C * Real.exp (-(c / 2 * (γ * L)))) * Real.exp (-(c / 2 * (γ * L))) := by
      have hx : Real.exp (-(c * (γ * L))) =
          Real.exp (-(c / 2 * (γ * L))) * Real.exp (-(c / 2 * (γ * L))) := by
        rw [← Real.exp_add]; ring_nf
      rw [show c * L / g ^ 2 = c * (γ * L) by rw [hγdef]; ring, hx]
      ring
    rw [e]
    exact mul_le_mul h1 hδ2 (Real.exp_pos _).le hc0.le
  -- the Neumann series for the actual inverse
  set Pγ := pairP γ (dysonMat 1 γ L E m) with hPγ
  set P₀ := Matrix.circulant (perP0 g L E mInf) with hP₀
  set t : ℝ := 1 - δ with ht
  have ht0 : 0 ≤ t := by linarith
  have ht1 : t < 1 := by linarith
  set μ : ℝ := c / ℓ with hμdef
  have hμ0 : 0 ≤ μ := by positivity
  have hμk : μ ≤ γ * k / 2048 := by
    have h1 : c / ℓ ≤ c / g ^ 2 := div_le_div_of_nonneg_left hc0.le hg2 hℓg
    have h2 : c / g ^ 2 = c * γ := by rw [hγdef]; ring
    have h3 : c * γ ≤ k / 2048 * γ := mul_le_mul_of_nonneg_right hck hγ.le
    linarith
  set A : ℝ := 1 + 2 * ((1 - δ) / δ) with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hA3 : A ≤ 3 / δ := by
    rw [hAdef, le_div_iff₀ hδ]; field_simp; nlinarith
  have hR0row := hΞw c hc0 hc1 hcG
  have hPPw := hPw μ hμ0 hμk
  have hεtc : εt ≤ c * δ ^ 2 := hεtε.trans hK1
  have he : t * A * εt ≤ 1 / 2 := by
    have h1 : t * A * εt ≤ 1 * (3 / δ) * (c * δ ^ 2) := by
      apply mul_le_mul (mul_le_mul (by linarith) hA3 hA0 (by norm_num)) hεtc hεt0 (by positivity)
    have h2 : 1 * (3 / δ) * (c * δ ^ 2) = 3 * c * δ := by field_simp
    have h3 : 3 * c * δ ≤ 3 * c := by nlinarith
    have h4 : 3 * c ≤ 1 / 2 := by
      have : k / 2048 ≤ 1 / 2048 := by linarith
      linarith
    linarith
  obtain ⟨hY1, hY2, hYrow, hdiffrow⟩ :=
    lg_neumann_pert hμ0 ht0 hA0 hεt0 Pγ P₀ (1 + Ξ) hprod0 hR0row hPPw he
  set Y := (1 - t • Pγ)⁻¹ with hYdef
  have h𝓔 : 𝓔 = Y - (1 + Ξ) := by simp only [𝓔, hP, Y, t]; abel
  have hYm : Y - 1 = t • mixedKer Pγ t := by
    have e := hY1
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul] at e
    unfold mixedKer
    rw [← hYdef]
    calc Y - 1 = Y - (Y - t • (Pγ * Y)) := by rw [e]
      _ = t • (Pγ * Y) := by abel
  have h𝓔e : ∀ a b, 𝓔 a b = (1 - δ) * (mixedKer Pγ (1 - δ) a b - mixedKer P₀ (1 - δ) a b) := by
    intro a b
    have h1 : 𝓔 = t • mixedKer Pγ t - Ξ := by rw [h𝓔, ← hYm]; abel
    rw [h1]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Ξ, t]
    ring
  have h𝓔pt : ∀ a b, |𝓔 a b| ≤ εt / (g ^ 2 * δ ^ 2) := fun a b => by rw [h𝓔e]; exact hE2 a b
  have h𝓔row : ∀ a, ∑ b, |𝓔 a b| ≤ εt / δ ^ 2 := fun a => by simp only [h𝓔e]; exact hE1 a
  have h𝓔c : ∀ a b, |𝓔 a b| ≤ c / g ^ 2 := by
    intro a b
    refine (h𝓔pt a b).trans ?_
    rw [div_le_div_iff₀ (by positivity) hg2]
    have := mul_le_mul_of_nonneg_left hεtc hg2.le
    nlinarith
  have hCε : ∀ x : ℝ, 0 ≤ x → x ≤ C * x := fun x hx => le_mul_of_one_le_left hx hC1
  have hε0 : 0 ≤ ε := hεt0.trans hεtε
  refine ⟨hK1, fun a b => ?_, fun a => (hK3 a).trans ?_, fun a b => (hK4 a b).trans ?_,
    fun a => (hK5 a).trans ?_, fun a b => (hK6 a b).trans ?_, fun a => (hK7 a).trans ?_,
    fun a => ?_, fun a b => ?_, ?_, fun a => ?_, fun a => ?_, hA1, fun a => ?_, fun a x => ?_,
    fun a x => ?_, fun a x => ?_, fun t' ht'0 ht'1 a x => ?_⟩
  · -- (A.37) [da:eq:uniform-mixed-row]: the actual mixed kernel
    have hProw : ∀ a, ∑ b, Pγ a b = 1 :=
      fun a => pairP_row_sum 1 γ hγ L (by omega) E m h.hroot a
    have hnn := mixedKer_nonneg_row Pγ (fun a b => h.P_nonneg a b) hProw t ht0 ht1
    rw [hP]
    refine ⟨hnn.1 a b, ?_⟩
    have hcδℓ : c / g ^ 2 ≤ c / (δ * ℓ) := div_le_div_of_nonneg_left hc0.le hδℓ0 hδℓ
    by_cases hδ2 : δ ≤ 1 / 2
    · have ht2 : 1 / 2 ≤ t := by linarith
      have h1 : t * mixedKer Pγ t a b = Ξ a b + 𝓔 a b := by
        have e1 : (Y - 1) a b = Ξ a b + 𝓔 a b := by
          rw [h𝓔]; simp only [Matrix.sub_apply, Matrix.add_apply]; ring
        rw [hYm] at e1
        simpa using e1
      have h2 : Ξ a b + 𝓔 a b ≤ CG / (δ * ℓ) + c / (δ * ℓ) :=
        add_le_add (hK4 a b) ((le_abs_self _).trans ((h𝓔c a b).trans hcδℓ))
      have h3 : mixedKer Pγ t a b ≤ 2 * (CG / (δ * ℓ) + c / (δ * ℓ)) := by
        have hm0 := hnn.1 a b
        nlinarith
      refine h3.trans ?_
      rw [show 2 * (CG / (δ * ℓ) + c / (δ * ℓ)) = (2 * CG + 2 * c) / (δ * ℓ) by ring]
      apply div_le_div_of_nonneg_right _ hδℓ0.le
      linarith
    · have ht2 : t < 1 / 2 := by linarith
      -- `Y = I + t K` is nonnegative with rows `1/(1-t)`
      have hYe : ∀ a c, Y a c = (1 : Matrix (Fin L) (Fin L) ℝ) a c + t * mixedKer Pγ t a c := by
        intro a c
        have := congrArg (fun X : Matrix (Fin L) (Fin L) ℝ => X a c) hYm
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this
        linarith
      have hY0 : ∀ a c, 0 ≤ Y a c := by
        intro a c; rw [hYe]
        have : 0 ≤ (1 : Matrix (Fin L) (Fin L) ℝ) a c := by
          rw [Matrix.one_apply]; split_ifs <;> norm_num
        exact add_nonneg this (mul_nonneg ht0 (hnn.1 a c))
      have hYr : ∑ c, Y a c ≤ 2 := by
        simp only [hYe, Finset.sum_add_distrib, ← Finset.mul_sum, hnn.2 a]
        simp only [Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        have h1t : (1 : ℝ) - t ≠ 0 := by linarith
        have e : 1 + t * (1 - t)⁻¹ = (1 - t)⁻¹ := by field_simp; ring
        rw [e, inv_le_comm₀ (by linarith) (by norm_num)]; linarith
      -- commutation `P Y = Y P`
      have hcomm : Pγ * Y = Y * Pγ := by
        have hc1 : (1 - t • Pγ) * Pγ = Pγ * (1 - t • Pγ) := by
          rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
            Matrix.mul_smul]
        calc Pγ * Y = Y * (1 - t • Pγ) * Pγ * Y := by rw [hY2, Matrix.one_mul]
          _ = Y * ((1 - t • Pγ) * Pγ) * Y := by simp only [Matrix.mul_assoc]
          _ = Y * (Pγ * (1 - t • Pγ)) * Y := by rw [hc1]
          _ = Y * Pγ * ((1 - t • Pγ) * Y) := by simp only [Matrix.mul_assoc]
          _ = Y * Pγ := by rw [hY1, Matrix.mul_one]
      have hPsup : ∀ c b, Pγ c b ≤ 16 * γ / k ^ 2 := by
        intro c b
        refine (h.P_le c b).trans ?_
        have hs1 : Real.exp (-(γ * k / 512)) ≤ 1 := by
          rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by have := h.b_pos; linarith)
        have hs0 : 0 ≤ Real.exp (-(γ * k / 512)) := (Real.exp_pos _).le
        have h1 := pow_le_one₀ hs0 hs1 (n := lgD L c b)
        have h2 := pow_le_one₀ hs0 hs1 (n := L - lgD L c b)
        have h3 : 0 ≤ 8 * γ / k ^ 2 := by positivity
        calc 8 * γ / k ^ 2 * (Real.exp (-(γ * k / 512)) ^ lgD L c b +
              Real.exp (-(γ * k / 512)) ^ (L - lgD L c b)) ≤ 8 * γ / k ^ 2 * (1 + 1) := by gcongr
          _ = 16 * γ / k ^ 2 := by ring
      have hK : mixedKer Pγ t a b ≤ 32 * γ / k ^ 2 := by
        unfold mixedKer
        rw [← hYdef, hcomm, Matrix.mul_apply]
        calc ∑ c, Y a c * Pγ c b ≤ ∑ c, Y a c * (16 * γ / k ^ 2) :=
              Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hPsup c b) (hY0 a c)
          _ = (∑ c, Y a c) * (16 * γ / k ^ 2) := by rw [Finset.sum_mul]
          _ ≤ 2 * (16 * γ / k ^ 2) := by gcongr
          _ = 32 * γ / k ^ 2 := by ring
      refine hK.trans ?_
      have hγδℓ : γ ≤ 1 / (δ * ℓ) := by
        rw [hγdef, ← one_div]; exact div_le_div_of_nonneg_left zero_le_one hδℓ0 hδℓ
      calc 32 * γ / k ^ 2 = 32 / k ^ 2 * γ := by ring
        _ ≤ C * (1 / (δ * ℓ)) := by
            apply mul_le_mul _ hγδℓ hγ.le (by linarith)
            have h1 := hCpos (64 / k ^ 2) (by simp)
            have h2 : 32 / k ^ 2 ≤ 64 / k ^ 2 := by gcongr; norm_num
            linarith
        _ = C / (δ * ℓ) := by ring
  · exact div_le_div_of_nonneg_right (by have := hCpos (2 * CG) (by simp); linarith) hδ.le
  · exact div_le_div_of_nonneg_right (by have := hCpos (2 * CG) (by simp); linarith) hδℓ0.le
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hCpos (CG ^ 2) (by simp))
      (by positivity)) hδ.le
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hCpos (CG ^ 2) (by simp))
      (by positivity)) hδℓ0.le
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hCpos (CG ^ 3) (by simp))
      (by positivity)) hδ.le
  · refine (h𝓔row a).trans ?_
    calc εt / δ ^ 2 ≤ ε / δ ^ 2 := div_le_div_of_nonneg_right hεtε (by positivity)
      _ ≤ C * ε / δ ^ 2 := div_le_div_of_nonneg_right (hCε ε hε0) (by positivity)
  · refine (h𝓔pt a b).trans ?_
    calc εt / (g ^ 2 * δ ^ 2) ≤ ε / (g ^ 2 * δ ^ 2) := div_le_div_of_nonneg_right hεtε (by
        positivity)
      _ ≤ C * ε / (g ^ 2 * δ ^ 2) := div_le_div_of_nonneg_right (hCε ε hε0) (by positivity)
  · -- (A.42) [da:eq:primitive-scale-conversion]
    have hX1 : 1 ≤ g ^ 2 / Real.sqrt δ := by rw [le_div_iff₀ hsδ]; nlinarith
    have hell : ellProp g L (1 - δ) = min (L : ℝ) (1 + g ^ 2 / Real.sqrt δ) := by
      unfold ellProp
      congr 2
      rw [hγg, show 1 - (1 - δ) = δ by ring, Real.sqrt_mul (by positivity), Real.sqrt_inv,
        Real.sqrt_sq hg0.le]
      field_simp
    rw [hell]
    constructor
    · exact min_le_min le_rfl (by linarith)
    · rcases le_total (L : ℝ) (g ^ 2 / Real.sqrt δ) with hc | hc
      · have : ℓ = L := min_eq_left hc
        rw [this]
        have := min_le_left (L : ℝ) (1 + g ^ 2 / Real.sqrt δ)
        have : (0 : ℝ) ≤ L := by positivity
        linarith
      · have : ℓ = g ^ 2 / Real.sqrt δ := min_eq_right hc
        rw [this]
        have := min_le_right (L : ℝ) (1 + g ^ 2 / Real.sqrt δ)
        linarith
  · -- (A.43) [da:eq:weighted-actual-kernels]: weighted rows of `I + Ξ` and of the actual inverse
    have hw : ∀ b, Real.exp (c * cycDist a b / ℓ) = Real.exp (μ * cycDist a b) := fun b => by
      rw [hμdef]; ring_nf
    simp only [hw, mul_add, Finset.sum_add_distrib]
    rw [hP]
    have h1 := hR0row a
    have h2 := hYrow a
    calc ∑ b, Real.exp (μ * cycDist a b) * |(1 + Ξ) a b| +
          ∑ b, Real.exp (μ * cycDist a b) * |(1 - (1 - δ) • Pγ)⁻¹ a b|
        ≤ A + 2 * A := add_le_add h1 h2
      _ ≤ 3 * (3 / δ) := by linarith
      _ ≤ C / δ := by
          rw [show 3 * (3 / δ) = 9 / δ by ring]
          exact div_le_div_of_nonneg_right (by linarith) hδ.le
  · -- (A.43) [da:eq:weighted-actual-kernels]: weighted row of `𝓔`
    have hw : ∀ b, Real.exp (c * cycDist a b / ℓ) = Real.exp (μ * cycDist a b) := fun b => by
      rw [hμdef]; ring_nf
    simp only [hw]
    rw [h𝓔]
    refine (hdiffrow a).trans ?_
    have h1 : 2 * A * (t * εt) * A ≤ 2 * (3 / δ) * (1 * εt) * (3 / δ) := by
      apply mul_le_mul (mul_le_mul (mul_le_mul le_rfl hA3 hA0 (by norm_num))
        (mul_le_mul_of_nonneg_right (by linarith) hεt0) (by positivity) (by positivity)) hA3 hA0
        (by positivity)
    have h2 : 2 * (3 / δ) * (1 * εt) * (3 / δ) = 18 * εt / δ ^ 2 := by field_simp; ring
    have h3 : 18 * εt / δ ^ 2 ≤ C * ε / δ ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : 18 * εt ≤ 18 * ε := by linarith
      have : 18 * ε ≤ C * ε := mul_le_mul_of_nonneg_right (by linarith) hε0
      linarith
    linarith
  · refine (h𝓔row a).trans ?_
    have : εt / δ ^ 2 ≤ c := by rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  · -- (A.45) [uvp:eq:localconv] for `I`
    rw [Finset.sum_eq_single a]
    · rw [Matrix.one_apply_eq, abs_one, mul_one]
      have h1 : Real.exp (-(c * cycDist x a / g ^ 2)) ≤ 1 := by
        rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by
          have : 0 ≤ c * cycDist x a / g ^ 2 := by positivity
          linarith)
      have h2 : 1 ≤ C * (g ^ 2 / (δ * ℓ)) := by nlinarith
      linarith
    · intro b _ hb; rw [Matrix.one_apply_ne' hb]; simp
    · simp
  · -- (A.45) [uvp:eq:localconv] for `Ξ`
    have hν : 0 < c / g ^ 2 := by positivity
    have hν1 : c / g ^ 2 ≤ 1 := by
      rw [div_le_one hg2]; nlinarith
    have hrow := lg_row_exp_neg' x (c / g ^ 2) hν hν1
    have hw : ∀ b, Real.exp (-(c * cycDist x b / g ^ 2)) = Real.exp (-(c / g ^ 2 * cycDist x b)) :=
      fun b => by ring_nf
    simp only [hw]
    calc ∑ b, Real.exp (-(c / g ^ 2 * cycDist x b)) * |Ξ a b|
        ≤ ∑ b, Real.exp (-(c / g ^ 2 * cycDist x b)) * (CG / (δ * ℓ)) := by
          gcongr with b
          rw [abs_of_nonneg (hΞnn a b)]; exact hK4 a b
      _ = (∑ b, Real.exp (-(c / g ^ 2 * cycDist x b))) * (CG / (δ * ℓ)) := by rw [Finset.sum_mul]
      _ ≤ 4 / (c / g ^ 2) * (CG / (δ * ℓ)) := by gcongr
      _ = 4 * CG / c * (g ^ 2 / (δ * ℓ)) := by field_simp
      _ ≤ C * (g ^ 2 / (δ * ℓ)) := by gcongr; exact hCpos _ (by simp)
  · -- (A.45) [uvp:eq:localconv] for `𝓔`
    have hν : 0 < c / g ^ 2 := by positivity
    have hν1 : c / g ^ 2 ≤ 1 := by
      rw [div_le_one hg2]; nlinarith
    have hrow := lg_row_exp_neg' x (c / g ^ 2) hν hν1
    have hw : ∀ b, Real.exp (-(c * cycDist x b / g ^ 2)) = Real.exp (-(c / g ^ 2 * cycDist x b)) :=
      fun b => by ring_nf
    simp only [hw]
    calc ∑ b, Real.exp (-(c / g ^ 2 * cycDist x b)) * |𝓔 a b|
        ≤ ∑ b, Real.exp (-(c / g ^ 2 * cycDist x b)) * (c / g ^ 2) := by
          gcongr with b; exact h𝓔c a b
      _ = (∑ b, Real.exp (-(c / g ^ 2 * cycDist x b))) * (c / g ^ 2) := by rw [Finset.sum_mul]
      _ ≤ 4 / (c / g ^ 2) * (c / g ^ 2) := by gcongr
      _ = 4 := by field_simp
      _ ≤ 4 * (g ^ 2 / (δ * ℓ)) := by nlinarith
      _ ≤ C * (g ^ 2 / (δ * ℓ)) := by gcongr; linarith
  · -- (A.45) [uvp:eq:localconv] for the stable inverses
    rw [hb, hγg]
    have hst := h.stable_row t' ht'0 ht'1 a (γ * k / 2048) (by positivity) le_rfl
    have hle : ∀ b, Real.exp (-(c * cycDist x b / g ^ 2)) ≤ Real.exp (γ * k / 2048 * cycDist a b)
        := by
      intro b
      apply Real.exp_le_exp.mpr
      have : 0 ≤ c * cycDist x b / g ^ 2 := by positivity
      have : 0 ≤ γ * k / 2048 * cycDist a b := by positivity
      linarith
    calc ∑ b, Real.exp (-(c * cycDist x b / g ^ 2)) *
          ‖(1 - (t' : ℂ) • pairQ γ (dysonMat 1 γ L E m))⁻¹ a b‖
        ≤ ∑ b, Real.exp (γ * k / 2048 * cycDist a b) *
          ‖(1 - (t' : ℂ) • pairQ γ (dysonMat 1 γ L E m))⁻¹ a b‖ := by
          gcongr with b; exact Real.exp_le_exp.mp (hle b)
      _ ≤ 3000000000 / k ^ 7 := hst
      _ ≤ C := le_trans (div_le_div_of_nonneg_right (by norm_num) hk7.le)
          (hCpos (10000000000 / k ^ 7) (by simp))
      _ ≤ C * (g ^ 2 / (δ * ℓ)) := by nlinarith

/-- Lemma A.10 [uvp:lem:actual-kernels]: the decomposition (A.36)
[da:eq:actual-kernel-decomposition] with (A.37) [da:eq:uniform-mixed-row]–(A.43)
[da:eq:weighted-actual-kernels] and the local convolution bound (A.45) [uvp:eq:localconv] for
`K ∈ {I, Ξ, 𝓔, (I - tQ)⁻¹}`, uniform in the output coordinate `x`. -/
theorem large_actual_kernels (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ R c C : ℝ, 1 ≤ Cκ ∧ 0 < R ∧ 0 < c ∧ 0 < C ∧
      ∀ g : ℝ, Cκ ≤ g → ∀ L : ℕ, ∀ E : ℝ, |E| ≤ 2 - κ →
      ∀ m mInf : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m →
      (0 < mInf.im ∧ mInf = dysonRHS g E mInf) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → R * (1 + |Real.log δ|) ≤ L / g ^ 2 →
      let P := pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)
      let Ξ := (1 - δ) • mixedKer (Matrix.circulant (perP0 g L E mInf)) (1 - δ)
      let 𝓔 := (1 - (1 - δ) • P)⁻¹ - 1 - Ξ
      let ℓ := min (L : ℝ) (g ^ 2 / Real.sqrt δ)
      let lam := Real.sqrt δ / g ^ 2
      let ε := epsL C c g L
      ε ≤ c * δ ^ 2 ∧
      (∀ a b, 0 ≤ mixedKer P (1 - δ) a b ∧ mixedKer P (1 - δ) a b ≤ C / (δ * ℓ)) ∧
      (∀ a, ∑ b, Ξ a b ≤ C / δ) ∧ (∀ a b, Ξ a b ≤ C / (δ * ℓ)) ∧
      (∀ a, ∑ b, |Ξ a (finRotate L b) - Ξ a b| ≤ C * lam / δ) ∧
      (∀ a b, |Ξ a (finRotate L b) - Ξ a b| ≤ C * lam / (δ * ℓ)) ∧
      (∀ a, ∑ b, |Ξ a (finRotate L (finRotate L b)) - 2 * Ξ a (finRotate L b) + Ξ a b| ≤
        C * lam ^ 2 / δ) ∧
      (∀ a, ∑ b, |𝓔 a b| ≤ C * ε / δ ^ 2) ∧ (∀ a b, |𝓔 a b| ≤ C * ε / (g ^ 2 * δ ^ 2)) ∧
      (ℓ ≤ ellProp g L (1 - δ) ∧ ellProp g L (1 - δ) ≤ 2 * ℓ) ∧
      (∀ a, ∑ b, Real.exp (c * cycDist a b / ℓ) * (|(1 + Ξ) a b| + |(1 - (1 - δ) • P)⁻¹ a b|) ≤
        C / δ) ∧
      (∀ a, ∑ b, Real.exp (c * cycDist a b / ℓ) * |𝓔 a b| ≤ C * ε / δ ^ 2) ∧
      1 ≤ g ^ 2 / (δ * ℓ) ∧ (∀ a, ∑ b, |𝓔 a b| ≤ C) ∧
      (∀ a x, ∑ b, Real.exp (-(c * cycDist x b / g ^ 2)) *
        |(1 : Matrix (Fin L) (Fin L) ℝ) a b| ≤ C * (g ^ 2 / (δ * ℓ))) ∧
      (∀ a x, ∑ b, Real.exp (-(c * cycDist x b / g ^ 2)) * |Ξ a b| ≤ C * (g ^ 2 / (δ * ℓ))) ∧
      (∀ a x, ∑ b, Real.exp (-(c * cycDist x b / g ^ 2)) * |𝓔 a b| ≤ C * (g ^ 2 / (δ * ℓ))) ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ a x, ∑ b, Real.exp (-(c * cycDist x b / g ^ 2)) *
        ‖(1 - (t : ℂ) • pairQ (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))⁻¹ a b‖ ≤
          C * (g ^ 2 / (δ * ℓ)) := by
  exact lg_actual_kernels_aux κ hκ hκ2

/-- (A.44) [da:eq:kernel-accuracy]. -/
theorem kernel_accuracy (C c r Q : ℝ) (hC : 0 < C) (hc : 0 < c) (hr : 0 ≤ r) (hQ : 0 < Q) :
    ∃ CrQ : ℝ, ∃ W₀ : ℕ, 0 < CrQ ∧ ∀ W : ℕ, W₀ ≤ W → ∀ δ g : ℝ, (W : ℝ) ^ (-3 : ℝ) ≤ δ →
      0 < g → ∀ L : ℕ, CrQ * g ^ 2 * Real.log W ≤ L →
      δ ^ (-r) * epsL C c g L ≤ (W : ℝ) ^ (-Q) := by 
  set K₁ : ℝ := c / 2 + C * (Real.log (2 * C / c) - 1) with hK₁
  set CrQ : ℝ := 2 * (3 * r + Q + 1) / c with hCrQ
  refine ⟨CrQ, max 3 ⌈C * Real.exp K₁⌉₊, by positivity, fun W hW δ g hδ hg L hL => ?_⟩
  have hW3 : (3 : ℝ) ≤ W := by
    have : (3 : ℕ) ≤ W := le_trans (le_max_left _ _) hW
    exact_mod_cast this
  have hWC : C * Real.exp K₁ ≤ W := by
    have h1 : ⌈C * Real.exp K₁⌉₊ ≤ W := le_trans (le_max_right _ _) hW
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast h1)
  have hW0 : (0 : ℝ) < W := by linarith
  have hlogW : 0 < Real.log W := Real.log_pos (by linarith)
  have hδ0 : 0 < δ := lt_of_lt_of_le (by positivity) hδ
  set H : ℝ := (L : ℝ) / g ^ 2 with hHdef
  have hH : CrQ * Real.log W ≤ H := by
    rw [hHdef, le_div_iff₀ (by positivity)]; linarith
  have hH0 : 0 ≤ H := le_trans (by positivity) hH
  -- `δ^{-r} ≤ W^{3r}`
  have hδr : δ ^ (-r) ≤ (W : ℝ) ^ (3 * r) := by
    calc δ ^ (-r) ≤ ((W : ℝ) ^ (-3 : ℝ)) ^ (-r) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hδ (by linarith)
      _ = (W : ℝ) ^ (3 * r) := by rw [← Real.rpow_mul hW0.le]; ring_nf
  -- `(1 + H)^C ≤ e^{cH/2 + K₁}`
  have hpow : (1 + H) ^ C ≤ Real.exp (c / 2 * H + K₁) := by
    rw [Real.rpow_def_of_pos (by linarith), Real.exp_le_exp, mul_comm]
    have := lg_log_le C c (1 + H) hC hc (by linarith)
    rw [hK₁]; linarith
  -- `e^{-cH/2} ≤ W^{-(3r + Q + 1)}`
  have hexp : Real.exp (-(c / 2 * H)) ≤ (W : ℝ) ^ (-(3 * r + Q + 1)) := by
    rw [Real.rpow_def_of_pos hW0, Real.exp_le_exp]
    have : c / 2 * (CrQ * Real.log W) ≤ c / 2 * H := by gcongr
    have e : c / 2 * (CrQ * Real.log W) = (3 * r + Q + 1) * Real.log W := by
      rw [hCrQ]; field_simp
    nlinarith
  unfold epsL
  rw [← hHdef]
  have e1 : Real.exp (-(c * L / g ^ 2)) = Real.exp (-(c * H)) := by rw [hHdef]; ring_nf
  rw [e1]
  have e2 : Real.exp (c / 2 * H + K₁) * Real.exp (-(c * H)) =
      Real.exp K₁ * Real.exp (-(c / 2 * H)) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  calc δ ^ (-r) * (C * (1 + H) ^ C * Real.exp (-(c * H)))
      ≤ (W : ℝ) ^ (3 * r) * (C * Real.exp (c / 2 * H + K₁) * Real.exp (-(c * H))) := by
        gcongr
    _ = C * Real.exp K₁ * ((W : ℝ) ^ (3 * r) * Real.exp (-(c / 2 * H))) := by
        rw [mul_assoc C, e2]; ring
    _ ≤ W * ((W : ℝ) ^ (3 * r) * (W : ℝ) ^ (-(3 * r + Q + 1))) := by gcongr
    _ = (W : ℝ) ^ (-Q) := by
        rw [← Real.rpow_add hW0]
        conv_lhs => arg 1; rw [← Real.rpow_one (W : ℝ)]
        rw [← Real.rpow_add hW0]; ring_nf

/-- Pointwise exponential profile of a periodized geometric kernel with row `t/δ`:
`B G_τ(x) ≤ (8C/(δℓ)) e^{-d/(Cℓ)}`, where `τ = e^{-λ}`, `√δ/a ≤ Cλ`, `λ ≤ C√δ/a`, `ℓ = min(L,
    a/√δ)`. -/
private lemma lg_xi_profile {L : ℕ} (hL : L ≠ 0) (B lam δ a t CG : ℝ) (_hB : 0 ≤ B) (hlam : 0 < lam)
    (hδ : 0 < δ) (_hδ1 : δ ≤ 1) (ha : 0 < a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hCG : 1 ≤ CG)
    (hrow : B * ((1 + Real.exp (-lam)) / (1 - Real.exp (-lam))) = t / δ)
    (hl1 : lam ≤ CG * Real.sqrt δ / a) (hl2 : Real.sqrt δ / a ≤ CG * lam) (x : Fin L) (y : Fin L) :
    B * geomV (Real.exp (-lam)) L (lgD L x y) ≤
      8 * CG / (δ * min (L : ℝ) (a / Real.sqrt δ)) *
        Real.exp (-(cycDist x y / (CG * min (L : ℝ) (a / Real.sqrt δ)))) := by
  set τ := Real.exp (-lam) with hτ
  set ℓ := min (L : ℝ) (a / Real.sqrt δ) with hℓ
  have hsδ : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL
  have hℓ0 : 0 < ℓ := lt_min hL0 (by positivity)
  have hτ0 : 0 < τ := Real.exp_pos _
  have hτ1 : τ < 1 := by rw [hτ, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  -- `B ≤ (t/δ) λ`
  have hBle : B ≤ t / δ * lam := by
    have h1 : B = t / δ * ((1 - τ) / (1 + τ)) := by
      rw [← hrow]; field_simp [show 1 - τ ≠ 0 by linarith]
    rw [h1]
    have h2 : (1 - τ) / (1 + τ) ≤ lam := by
      rw [div_le_iff₀ (by linarith)]
      have := Real.add_one_le_exp (-lam)
      nlinarith
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  -- `G_τ(x) ≤ 2 τ^d/(1 - τ^L)`
  have hd1 := cycDist_le_lgD x y
  have hd2 := cycDist_le_sub_lgD x y
  have hτd1 : τ ^ lgD L x y ≤ τ ^ cycDist x y := pow_le_pow_of_le_one hτ0.le hτ1.le hd1
  have hτd2 : τ ^ (L - lgD L x y) ≤ τ ^ cycDist x y := pow_le_pow_of_le_one hτ0.le hτ1.le hd2
  have hτL : 0 < 1 - τ ^ L := by have := pow_lt_one₀ hτ0.le hτ1 hL; linarith
  have hG : geomV τ L (lgD L x y) ≤ 2 * τ ^ cycDist x y / (1 - τ ^ L) := by
    unfold geomV
    apply div_le_div_of_nonneg_right _ hτL.le
    linarith
  have hlamℓ : lam ≤ CG / ℓ := by
    have : Real.sqrt δ / a ≤ 1 / ℓ := by
      rw [div_le_div_iff₀ ha hℓ0, one_mul]
      have := min_le_right (L : ℝ) (a / Real.sqrt δ)
      rw [le_div_iff₀ hsδ] at this; linarith
    calc lam ≤ CG * Real.sqrt δ / a := hl1
      _ = CG * (Real.sqrt δ / a) := by ring
      _ ≤ CG * (1 / ℓ) := by gcongr
      _ = CG / ℓ := by ring
  have hdL : (cycDist x y : ℝ) ≤ L / 2 := by
    have := cycDist_le_half x y
    have h2 : ((2 * cycDist x y : ℕ) : ℝ) ≤ L := by exact_mod_cast this
    push_cast at h2; linarith
  by_cases hlamL : 1 ≤ lam * L
  · -- long cycle: `1 - τ^L ≥ 1/2`
    have hτL2 : 1 / 2 ≤ 1 - τ ^ L := by
      have : τ ^ L = Real.exp (-(lam * L)) := by rw [hτ, ← Real.exp_nat_mul]; ring_nf
      rw [this]
      have : Real.exp (-(lam * L)) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      have : Real.exp (-1) ≤ 1 / 2 := by
        have := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 2) (by norm_num) (by norm_num)
        have h3 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
        have h4 : 2 ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
        nlinarith [Real.exp_pos (-1)]
      linarith
    have hτd : τ ^ cycDist x y ≤ Real.exp (-(cycDist x y / (CG * ℓ))) := by
      rw [hτ, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hl3 : 1 / (CG * ℓ) ≤ lam := by
        rcases le_total (L : ℝ) (a / Real.sqrt δ) with hc | hc
        · have : ℓ = L := min_eq_left hc
          rw [this, div_le_iff₀ (by positivity)]; nlinarith
        · have : ℓ = a / Real.sqrt δ := min_eq_right hc
          rw [this]
          have : 1 / (CG * (a / Real.sqrt δ)) = Real.sqrt δ / a / CG := by field_simp
          rw [this, div_le_iff₀ (by linarith)]; linarith
      have : (cycDist x y : ℝ) / (CG * ℓ) ≤ cycDist x y * lam := by
        rw [div_eq_mul_one_div]; gcongr
      linarith
    calc B * geomV τ L (lgD L x y) ≤ (t / δ * lam) * (2 * τ ^ cycDist x y / (1 - τ ^ L)) := by
          gcongr
          exact lg_geomV_nonneg τ hτ0.le hτ1 L _ hL
      _ ≤ (1 / δ * (CG / ℓ)) * (2 * τ ^ cycDist x y / (1 / 2)) := by
          gcongr
      _ = 4 * CG / (δ * ℓ) * τ ^ cycDist x y := by field_simp; ring
      _ ≤ 8 * CG / (δ * ℓ) * Real.exp (-(cycDist x y / (CG * ℓ))) := by
          have : 4 * CG / (δ * ℓ) ≤ 8 * CG / (δ * ℓ) := by gcongr; norm_num
          exact mul_le_mul this hτd (by positivity) (by positivity)
  · -- short cycle
    push Not at hlamL
    have hτL2 : lam * L / 2 ≤ 1 - τ ^ L := by
      have : τ ^ L = Real.exp (-(lam * L)) := by rw [hτ, ← Real.exp_nat_mul]; ring_nf
      rw [this]
      exact lg_one_sub_exp_neg (lam * L) (by positivity) hlamL.le
    have hLℓ : (L : ℝ) / CG ≤ ℓ := by
      apply le_min
      · rw [div_le_iff₀ (by linarith)]; nlinarith
      · rw [div_le_div_iff₀ (by linarith) hsδ]
        have : L * Real.sqrt δ ≤ a * CG := by
          have h1 : lam * L < 1 := hlamL
          have h2 : Real.sqrt δ / a * L ≤ CG * lam * L := by gcongr
          have h3 : Real.sqrt δ / a * L ≤ CG := by nlinarith
          rw [div_mul_eq_mul_div, div_le_iff₀ ha] at h3; linarith
        linarith
    have hexp : 1 / 2 ≤ Real.exp (-(cycDist x y / (CG * ℓ))) := by
      have h1 : (cycDist x y : ℝ) / (CG * ℓ) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]
        have : (L : ℝ) ≤ CG * ℓ := by rw [div_le_iff₀ (by linarith)] at hLℓ; linarith
        linarith
      have := Real.add_one_le_exp (-(cycDist x y / (CG * ℓ)))
      linarith
    have hGs : geomV τ L (lgD L x y) ≤ 4 / (lam * L) := by
      refine hG.trans ?_
      have h1 : τ ^ cycDist x y ≤ 1 := pow_le_one₀ hτ0.le hτ1.le
      rw [div_le_div_iff₀ hτL (by positivity)]
      have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ lam * L)
      linarith
    calc B * geomV τ L (lgD L x y) ≤ (t / δ * lam) * (4 / (lam * L)) := by
          gcongr
          exact lg_geomV_nonneg τ hτ0.le hτ1 L _ hL
      _ = 4 * t / (δ * L) := by field_simp
      _ ≤ 4 * CG / (δ * ℓ) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hℓL : ℓ ≤ L := min_le_left _ _
          have h4 : t * ℓ ≤ CG * L := by
            have := mul_le_mul ht1 hℓL hℓ0.le zero_le_one
            nlinarith
          nlinarith
      _ = 8 * CG / (δ * ℓ) * (1 / 2) := by ring
      _ ≤ 8 * CG / (δ * ℓ) * Real.exp (-(cycDist x y / (CG * ℓ))) := by gcongr

/-- `I - uP` is invertible for a probability kernel `P` and `0 ≤ u < 1`. -/
private lemma lg_inv_stoch {L : ℕ} (P : Matrix (Fin L) (Fin L) ℝ) (hP : ∀ a b, 0 ≤ P a b)
    (hrow : ∀ a, ∑ b, P a b = 1) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (1 - u • P) * (1 - u • P)⁻¹ = 1 ∧ (1 - u • P)⁻¹ * (1 - u • P) = 1 := by
  have hdet : (1 - u • P).det ≠ 0 := by
    apply det_ne_zero_of_sum_row_lt_diag
    intro k
    have hoff : ∑ j ∈ Finset.univ.erase k, ‖(1 - u • P) k j‖ = u * (1 - P k k) := by
      rw [← hrow k, ← Finset.add_sum_erase Finset.univ (fun j => P k j) (Finset.mem_univ k)]
      simp only [add_sub_cancel_left, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Matrix.sub_apply, Matrix.one_apply_ne' (Finset.ne_of_mem_erase hj), zero_sub,
        Real.norm_eq_abs, abs_neg, Matrix.smul_apply, smul_eq_mul, abs_of_nonneg
        (mul_nonneg hu0 (hP k j))]
    rw [hoff, Matrix.sub_apply, Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul,
      Real.norm_eq_abs]
    have hPk : P k k ≤ 1 := by
      rw [← hrow k]
      exact Finset.single_le_sum (fun j _ => hP k j) (Finset.mem_univ k)
    have : 0 ≤ 1 - u * P k k := by nlinarith [hP k k]
    rw [abs_of_nonneg this]
    nlinarith [hP k k]
  have hU : IsUnit (1 - u • P).det := isUnit_iff_ne_zero.mpr hdet
  exact ⟨Matrix.mul_nonsing_inv _ hU, Matrix.nonsing_inv_mul _ hU⟩

namespace LgGood

variable {k γ E : ℝ} {L : ℕ} {m mInf : ℂ} (h : LgGood k γ E L m mInf)
include h

/-- Lemma 6.1 [da:lem:scales-propagators] at early times `u ≤ 1/2`:
`P(I - uP)⁻¹ ≤ (128γ/k²) e^{-c₀γ d}`. -/
private lemma kernel_early (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) (a b : Fin L) :
    mixedKer (pairP γ (dysonMat 1 γ L E m)) u a b ≤
      128 * γ / k ^ 2 * Real.exp (-(k ^ 4 * γ / 536870912 * cycDist a b)) := by
  have hk := h.hk
  have hk1 := h.hk1
  have hγ := h.hγ
  set P := pairP γ (dysonMat 1 γ L E m) with hPdef
  set μ : ℝ := k ^ 4 * γ / 536870912 with hμ
  have hμ0 : 0 ≤ μ := by positivity
  have hPnn : ∀ a b, 0 ≤ P a b := fun a b => h.P_nonneg a b
  have hProw : ∀ a, ∑ b, P a b = 1 :=
    fun a => pairP_row_sum 1 γ hγ L (by have := h.hL; omega) E m h.hroot a
  obtain ⟨hY1, hY2⟩ := lg_inv_stoch P hPnn hProw u hu0 (by linarith)
  set Y := (1 - u • P)⁻¹ with hYdef
  have hcomm : P * Y = Y * P := by
    have hc1 : (1 - u • P) * P = P * (1 - u • P) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
        Matrix.mul_smul]
    calc P * Y = Y * (1 - u • P) * P * Y := by rw [hY2, Matrix.one_mul]
      _ = Y * ((1 - u • P) * P) * Y := by simp only [Matrix.mul_assoc]
      _ = Y * (P * (1 - u • P)) * Y := by rw [hc1]
      _ = Y * P * ((1 - u • P) * Y) := by simp only [Matrix.mul_assoc]
      _ = Y * P := by rw [hY1, Matrix.mul_one]
  -- weighted row of `Y`
  have hwrow := h.P_row_weighted a μ hμ0 le_rfl
  have hearly := early_inverse_abstract P (pairQ γ (dysonMat 1 γ L E m)) μ hμ0 hPnn
    (fun a b => by simp [P, pairP, pairQ, norm_pow, Complex.norm_real, abs_of_pos hγ])
    (fun a => h.P_row_weighted a μ hμ0 le_rfl) u hu0 hu a
  have hYw : ∑ c, Real.exp (μ * cycDist a c) * |Y a c| ≤ 8 := by
    refine le_trans (Finset.sum_le_sum fun c _ => ?_) hearly
    have := norm_nonneg ((1 - (u : ℂ) • pairQ γ (dysonMat 1 γ L E m))⁻¹ a c)
    have he := (Real.exp_pos (μ * cycDist a c)).le
    nlinarith
  -- weighted sup of `P`
  have hPw : ∀ c, Real.exp (μ * cycDist c b) * P c b ≤ 16 * γ / k ^ 2 := by
    intro c
    have hP := h.P_le c b
    set s := Real.exp (-(γ * k / 512)) with hs
    have hs0 : 0 ≤ s := (Real.exp_pos _).le
    have hμs : Real.exp μ * s ≤ 1 := by
      rw [hs, ← Real.exp_add, ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have : k ^ 4 ≤ k := by
        calc k ^ 4 ≤ k ^ 1 := pow_le_pow_of_le_one hk.le hk1 (by norm_num)
          _ = k := pow_one k
      have : k ^ 4 * γ / 536870912 ≤ γ * k / 512 := by
        rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
      linarith
    have h1 : Real.exp (μ * cycDist c b) * s ^ lgD L c b ≤ 1 := by
      calc Real.exp (μ * cycDist c b) * s ^ lgD L c b
          ≤ Real.exp (μ * lgD L c b) * s ^ lgD L c b := by
            gcongr; exact_mod_cast cycDist_le_lgD c b
        _ = (Real.exp μ * s) ^ lgD L c b := lg_exp_mul_pow μ s _
        _ ≤ 1 := pow_le_one₀ (by positivity) hμs
    have h2 : Real.exp (μ * cycDist c b) * s ^ (L - lgD L c b) ≤ 1 := by
      calc Real.exp (μ * cycDist c b) * s ^ (L - lgD L c b)
          ≤ Real.exp (μ * (L - lgD L c b : ℕ)) * s ^ (L - lgD L c b) := by
            gcongr; exact_mod_cast cycDist_le_sub_lgD c b
        _ = (Real.exp μ * s) ^ (L - lgD L c b) := lg_exp_mul_pow μ s _
        _ ≤ 1 := pow_le_one₀ (by positivity) hμs
    calc Real.exp (μ * cycDist c b) * P c b
        ≤ Real.exp (μ * cycDist c b) * (8 * γ / k ^ 2 * (s ^ lgD L c b + s ^ (L - lgD L c b))) :=
          mul_le_mul_of_nonneg_left hP (Real.exp_pos _).le
      _ = 8 * γ / k ^ 2 * (Real.exp (μ * cycDist c b) * s ^ lgD L c b +
          Real.exp (μ * cycDist c b) * s ^ (L - lgD L c b)) := by ring
      _ ≤ 8 * γ / k ^ 2 * (1 + 1) := by gcongr
      _ = 16 * γ / k ^ 2 := by ring
  -- combine
  have hK : Real.exp (μ * cycDist a b) * mixedKer P u a b ≤ 8 * (16 * γ / k ^ 2) := by
    unfold mixedKer
    rw [← hYdef, hcomm, Matrix.mul_apply, Finset.mul_sum]
    calc ∑ c, Real.exp (μ * cycDist a b) * (Y a c * P c b)
        ≤ ∑ c, (Real.exp (μ * cycDist a c) * |Y a c|) * (Real.exp (μ * cycDist c b) * P c b) := by
          refine Finset.sum_le_sum fun c _ => ?_
          have h1 := lg_exp_dist_le μ hμ0 a c b
          have h2 : Y a c * P c b ≤ |Y a c| * P c b :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (hPnn c b)
          calc Real.exp (μ * cycDist a b) * (Y a c * P c b)
              ≤ Real.exp (μ * cycDist a b) * (|Y a c| * P c b) :=
                mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
            _ ≤ (Real.exp (μ * cycDist a c) * Real.exp (μ * cycDist c b)) * (|Y a c| * P c b) :=
                mul_le_mul_of_nonneg_right h1 (mul_nonneg (abs_nonneg _) (hPnn c b))
            _ = _ := by ring
      _ ≤ ∑ c, (Real.exp (μ * cycDist a c) * |Y a c|) * (16 * γ / k ^ 2) :=
          Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hPw c)
            (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))
      _ = (∑ c, Real.exp (μ * cycDist a c) * |Y a c|) * (16 * γ / k ^ 2) := by rw [Finset.sum_mul]
      _ ≤ 8 * (16 * γ / k ^ 2) := by gcongr
  have hpos := Real.exp_pos (μ * cycDist a b)
  have e : Real.exp (-(μ * cycDist a b)) * Real.exp (μ * cycDist a b) = 1 := by
    rw [← Real.exp_add]; simp
  calc mixedKer P u a b = Real.exp (-(μ * cycDist a b)) *
        (Real.exp (μ * cycDist a b) * mixedKer P u a b) := by rw [← mul_assoc, e, one_mul]
    _ ≤ Real.exp (-(μ * cycDist a b)) * (8 * (16 * γ / k ^ 2)) := by gcongr
    _ = 128 * γ / k ^ 2 * Real.exp (-(μ * cycDist a b)) := by ring

end LgGood

/-- `ℓ ≤ ℓ_{1-δ} ≤ 2ℓ` for `ℓ = min(L, g²/√δ)`, (A.42) [da:eq:primitive-scale-conversion]. -/
private lemma lg_ellProp_cmp {g : ℝ} (hg : 1 ≤ g) {L : ℕ} (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    min (L : ℝ) (g ^ 2 / Real.sqrt δ) ≤ ellProp g L (1 - δ) ∧
      ellProp g L (1 - δ) ≤ 2 * min (L : ℝ) (g ^ 2 / Real.sqrt δ) := by
  have hg0 : 0 < g := by linarith
  have hsδ : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hsδ1 : Real.sqrt δ ≤ 1 := Real.sqrt_le_one.mpr hδ1
  have hX1 : 1 ≤ g ^ 2 / Real.sqrt δ := by rw [le_div_iff₀ hsδ]; nlinarith
  have hell : ellProp g L (1 - δ) = min (L : ℝ) (1 + g ^ 2 / Real.sqrt δ) := by
    unfold ellProp
    congr 2
    rw [lg_gammaG_eq hg, show 1 - (1 - δ) = δ by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_inv, Real.sqrt_sq (by positivity)]
    field_simp
  rw [hell]
  constructor
  · exact min_le_min le_rfl (by linarith)
  · rcases le_total (L : ℝ) (g ^ 2 / Real.sqrt δ) with hc | hc
    · rw [min_eq_left hc]
      have := min_le_left (L : ℝ) (1 + g ^ 2 / Real.sqrt δ)
      have : (0 : ℝ) ≤ L := by positivity
      linarith
    · rw [min_eq_right hc]
      have := min_le_right (L : ℝ) (1 + g ^ 2 / Real.sqrt δ)
      linarith

namespace LgGood

variable {k γ E : ℝ} {L : ℕ} {m mInf : ℂ} (h : LgGood k γ E L m mInf)
include h

/-- Lemma 6.1 [da:lem:scales-propagators] at late times `u = 1 - δ ≥ 1/2`: exponential profile plus
the error `𝓔` of (A.36) [da:eq:actual-kernel-decomposition]. -/
private lemma kernel_late {g : ℝ} (hb : hopB g = 1) (hγg : gammaG g = γ) [NeZero L] (hg1 : 1 ≤ g)
    (hγdef : γ = (g ^ 2)⁻¹) (hLg : g ^ 2 ≤ L) (δ : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (CG : ℝ)
    (HG : ∀ (a D δ : ℝ) (L : ℕ), 1 ≤ a → k ^ 4 / 1024 * a ^ 2 ≤ D → D ≤ 262144 / k ^ 2 * a ^ 2 →
      a ≤ L → 0 < δ → δ ≤ 1 →
      let Ξ := perLine (fun x => (1 - δ) * lineKer D δ x) L
      let lam := lamGeo D δ
      let ℓ := min (L : ℝ) (a / Real.sqrt δ)
      (lam ≤ CG * Real.sqrt δ / a ∧ Real.sqrt δ / a ≤ CG * lam) ∧
      ∑ x, Ξ x ≤ CG / δ ∧ (∀ x, Ξ x ≤ CG / (δ * ℓ)) ∧
      ∑ x, |Ξ (finRotate L x) - Ξ x| ≤ CG * lam / δ ∧
      (∀ x, |Ξ (finRotate L x) - Ξ x| ≤ CG * lam / (δ * ℓ)) ∧
      ∑ x, |Ξ (finRotate L (finRotate L x)) - 2 * Ξ (finRotate L x) + Ξ x| ≤
        CG * lam ^ 2 / δ) (a b : Fin L) :
    mixedKer (pairP γ (dysonMat 1 γ L E m)) (1 - δ) a b ≤
      32 * max CG 1 / (δ * ellProp g L (1 - δ)) *
          Real.exp (-(cycDist a b / (max CG 1 * ellProp g L (1 - δ)))) +
        2 * (10000000000 / k ^ 6 * (1 + γ * L) * Real.exp (-(3 * k / 4096 * (γ * L)))) /
          (g ^ 2 * δ ^ 2) := by
  have hδ1 : δ ≤ 1 := by linarith
  have hk := h.hk
  have hγ := h.hγ
  obtain ⟨hI, hprod, hXi, hrowΞ⟩ := h.xi_eq hb hγg δ hδ hδ1
  obtain ⟨hσ0, hσ1, -⟩ := h.sigma_facts
  set σ := ‖freeRho 1 ((E : ℂ) + γ * mInf)‖ ^ 2 with hσdef
  set D := σ / (1 - σ) ^ 2 with hDdef
  have hD : 0 < D := by have : 0 < 1 - σ := by linarith
                        positivity
  set S := Real.sqrt (δ * (δ + 4 * D)) with hSdef
  have hSpos : 0 < S := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨hDlo, hDhi⟩ := h.D_bounds
  have hγinv : γ⁻¹ = g ^ 2 := by rw [hγdef, inv_inv]
  rw [hγinv] at hDlo hDhi
  have hg2 : 1 ≤ g ^ 2 := by nlinarith
  obtain ⟨⟨hlam1, hlam2⟩, -⟩ := HG (g ^ 2) D δ L hg2 hDlo hDhi hLg hδ hδ1
  set CG' := max CG 1 with hCG'
  have hCG1 : 1 ≤ CG' := le_max_right _ _
  have hlamp := lg_lamGeo_pos hD hδ
  have hl1 : lamGeo D δ ≤ CG' * Real.sqrt δ / g ^ 2 := by
    refine hlam1.trans ?_
    have : 0 ≤ Real.sqrt δ / g ^ 2 := by positivity
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) this
  have hl2 : Real.sqrt δ / g ^ 2 ≤ CG' * lamGeo D δ :=
    hlam2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hlamp.le)
  -- the profile of `Ξ`
  have hΞab : ((1 - δ) • mixedKer (Matrix.circulant (perP0 g L E mInf)) (1 - δ)) a b =
      (1 - δ) / S * geomV (Real.exp (-lamGeo D δ)) L (lgD L a b) := by
    rw [hXi]; simp [geomC, lgTau]
  have hprof := lg_xi_profile (NeZero.ne L) ((1 - δ) / S) (lamGeo D δ) δ (g ^ 2) (1 - δ) CG'
    (div_nonneg (by linarith) hSpos.le) hlamp hδ hδ1 (by positivity) (by linarith) (by linarith)
    hCG1 hrowΞ hl1 hl2 a b
  rw [← hΞab] at hprof
  -- the error term
  obtain ⟨-, -, -, -, -, -, -, hE2⟩ := h.err_pack hb hγg hγdef δ hδ hδ1
  set εt := 10000000000 / k ^ 6 * (1 + γ * L) * Real.exp (-(3 * k / 4096 * (γ * L)))
  have hEab := hE2 a b
  set ℓ := min (L : ℝ) (g ^ 2 / Real.sqrt δ) with hℓ
  obtain ⟨hℓu1, hℓu2⟩ := lg_ellProp_cmp hg1 (L := L) δ hδ hδ1
  rw [← hℓ] at hℓu1 hℓu2
  have hℓ0 : 0 < ℓ := lt_min (by have := Nat.pos_of_ne_zero (NeZero.ne L); exact_mod_cast this)
    (by have := Real.sqrt_pos.mpr hδ; positivity)
  set ℓu := ellProp g L (1 - δ)
  have hℓu0 : 0 < ℓu := lt_of_lt_of_le hℓ0 hℓu1
  -- combine
  set K := mixedKer (pairP γ (dysonMat 1 γ L E m)) (1 - δ) a b
  set Ξab := ((1 - δ) • mixedKer (Matrix.circulant (perP0 g L E mInf)) (1 - δ)) a b
  have hsplit : (1 - δ) * K = Ξab +
      (1 - δ) * (K - mixedKer (Matrix.circulant (perP0 g L E mInf)) (1 - δ) a b) := by
    simp only [Ξab, Matrix.smul_apply, smul_eq_mul]; ring
  have hKle : K ≤ 2 * Ξab + 2 * (εt / (g ^ 2 * δ ^ 2)) := by
    have h1 : (1 - δ) * K ≤ Ξab + εt / (g ^ 2 * δ ^ 2) := by
      rw [hsplit]; exact add_le_add le_rfl ((le_abs_self _).trans hEab)
    have hK0 : 0 ≤ K := by
      have := (mixedKer_nonneg_row (pairP γ (dysonMat 1 γ L E m)) (fun a b => h.P_nonneg a b)
        (fun a => pairP_row_sum 1 γ hγ L (by have := h.hL; omega) E m h.hroot a) (1 - δ)
        (by linarith) (by linarith)).1 a b
      exact this
    have hΞ0 : 0 ≤ Ξab := by
      simp only [Ξab, hΞab]
      have hτ1 : Real.exp (-lamGeo D δ) < 1 := by
        rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
      exact mul_nonneg (div_nonneg (by linarith) hSpos.le)
        (lg_geomV_nonneg _ (Real.exp_pos _).le hτ1 L _ (NeZero.ne L))
    have hε0 : 0 ≤ εt / (g ^ 2 * δ ^ 2) := by positivity
    nlinarith
  refine hKle.trans ?_
  have hΞle : 2 * Ξab ≤ 32 * CG' / (δ * ℓu) * Real.exp (-(cycDist a b / (CG' * ℓu))) := by
    have h1 : 8 * CG' / (δ * ℓ) ≤ 16 * CG' / (δ * ℓu) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left hℓu2 (show 0 ≤ 8 * CG' * δ by positivity)
      linarith
    have h2 : Real.exp (-(cycDist a b / (CG' * ℓ))) ≤ Real.exp (-(cycDist a b / (CG' * ℓu))) := by
      apply Real.exp_le_exp.mpr
      have : (cycDist a b : ℝ) / (CG' * ℓu) ≤ cycDist a b / (CG' * ℓ) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
      linarith
    calc 2 * Ξab ≤ 2 * (8 * CG' / (δ * ℓ) * Real.exp (-(cycDist a b / (CG' * ℓ)))) := by
          gcongr
      _ ≤ 2 * (16 * CG' / (δ * ℓu) * Real.exp (-(cycDist a b / (CG' * ℓu)))) := by
          gcongr
      _ = 32 * CG' / (δ * ℓu) * Real.exp (-(cycDist a b / (CG' * ℓu))) := by ring
  rw [show 2 * εt / (g ^ 2 * δ ^ 2) = 2 * (εt / (g ^ 2 * δ ^ 2)) by ring]
  linarith

end LgGood

private lemma lg_log_ge_one {W : ℕ} (hW : 3 ≤ W) : 1 ≤ Real.log W := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : (3 : ℝ) ≤ W := by exact_mod_cast hW
  linarith

set_option maxHeartbeats 4000000 in
-- the many explicit estimates of this proof exceed the default heartbeat limit
/-- The statement of Lemma 6.1 [da:lem:scales-propagators] at large coupling. -/
private theorem lg_scalesProp_aux (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ c C' : ℝ, 1 ≤ Cκ ∧ 0 < c ∧ 0 < C' ∧ ∀ A : ℝ, 0 < A → ∃ CA : ℝ, ∃ W₀ : ℕ, 0 < CA ∧
      ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, Cκ ≤ g → ∀ L : ℕ, CA * g ^ 2 * Real.log W ≤ L →
      ∀ E : ℝ, |E| ≤ 2 - κ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m →
      let M := dysonMat (hopB g) (gammaG g) L E m
      (C'⁻¹ ≤ m.im ∧ m.im ≤ C') ∧ (∀ a b, ‖M a b‖ ≤ C') ∧
      (∀ a, gammaG g * ∑ b, (‖M a b‖ + ‖M a b‖ ^ 2) ≤ C') ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ a, ∑ b, ‖(1 - (u : ℂ) • pairQ (gammaG g) M)⁻¹ a b‖ ≤ C') ∧
      ∀ u : ℝ, 0 ≤ u → (W : ℝ) ^ (-3 : ℝ) ≤ 1 - u → ∀ a b,
        0 ≤ mixedKer (pairP (gammaG g) M) u a b ∧
        mixedKer (pairP (gammaG g) M) u a b ≤
          C' / ((1 - u) * ellProp g L u) * Real.exp (-(c * cycDist a b / ellProp g L u)) +
            (ellProp g L u)⁻¹ * (W : ℝ) ^ (-A) := by 
  have hk : 0 < κ / 2 := by linarith
  have hk1 : κ / 2 ≤ 1 := by linarith
  obtain ⟨Rs, hRs3, hRs⟩ := lg_setup hκ hκ2
  set k := κ / 2 with hkdef
  have hκ12 : k ^ 4 / 1024 ≤ 262144 / k ^ 2 := by
    have : k ^ 4 ≤ 1 := pow_le_one₀ hk.le hk1
    have : k ^ 2 ≤ 1 := pow_le_one₀ hk.le hk1
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  obtain ⟨CG, hCG, HG⟩ := geom_bounds (k ^ 4 / 1024) (262144 / k ^ 2) (by positivity) hκ12
  set CG' := max CG 1 with hCG'
  have hCG1 : 1 ≤ CG' := le_max_right _ _
  set c : ℝ := min (k ^ 4 / 536870912) (1 / CG') with hcdef
  have hc0 : 0 < c := lt_min (by positivity) (by positivity)
  have hc₀ : c ≤ k ^ 4 / 536870912 := min_le_left _ _
  have hcG : c ≤ 1 / CG' := min_le_right _ _
  set C' : ℝ := 32 / k + 4 / k + 16384 / k ^ 2 + 1 + 3000000000 / k ^ 7 + 512 / k ^ 2 + 32 * CG'
    with hC'def
  have hk2p : 0 < k ^ 2 := by positivity
  have hk7p : 0 < k ^ 7 := by positivity
  have t1 : 0 ≤ 32 / k := by positivity
  have t2 : 0 ≤ 4 / k := by positivity
  have t3 : 0 ≤ 16384 / k ^ 2 := by positivity
  have t4 : 0 ≤ 3000000000 / k ^ 7 := by positivity
  have t5 : 0 ≤ 512 / k ^ 2 := by positivity
  have t6 : 0 ≤ 32 * CG' := by positivity
  have hC'0 : 0 < C' := by simp only [hC'def]; linarith
  refine ⟨1000 / k ^ 5, c, C', ?_, hc0, hC'0, fun A hA => ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    have : k ^ 5 ≤ 1 := pow_le_one₀ hk.le hk1
    linarith
  obtain ⟨CrQ, W₁, hCrQ, hka⟩ := kernel_accuracy (10000000000 / k ^ 6) (3 * k / 4096) 3 (A + 1)
    (by positivity) (by positivity) (by norm_num) (by linarith)
  refine ⟨max CrQ (max Rs 1), max W₁ 4, lt_of_lt_of_le hCrQ (le_max_left _ _),
    fun W hW g hg L hL E hE m hm => ?_⟩
  have hW4 : 4 ≤ W := le_trans (le_max_right _ _) hW
  have hWW₁ : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hlogW : 1 ≤ Real.log W := lg_log_ge_one (by omega)
  have hW0 : (0 : ℝ) < W := by have : (4 : ℝ) ≤ W := by exact_mod_cast hW4
                               linarith
  have hg1' : 1 ≤ g := by
    have : 1 ≤ 1000 / k ^ 5 := by
      rw [le_div_iff₀ (by positivity)]; have : k ^ 5 ≤ 1 := pow_le_one₀ hk.le hk1
      linarith
    linarith
  have hg2 : 0 < g ^ 2 := by positivity
  have hCAlog : max CrQ (max Rs 1) * g ^ 2 ≤ L := by
    have h1 : max CrQ (max Rs 1) * g ^ 2 * 1 ≤ max CrQ (max Rs 1) * g ^ 2 * Real.log W := by
      gcongr
    linarith
  have hLg : Rs * g ^ 2 ≤ L := by
    have : Rs ≤ max CrQ (max Rs 1) := le_trans (le_max_left _ _) (le_max_right _ _)
    have h2 : Rs * g ^ 2 ≤ max CrQ (max Rs 1) * g ^ 2 := by gcongr
    linarith
  obtain ⟨hg1, hb, hγg, -, ⟨mInf, hpos, heq⟩, hgood⟩ := hRs g hg L hLg E hE
  rw [hb, hγg] at hm
  have h := hgood m mInf hm hpos heq
  set γ : ℝ := (g ^ 2)⁻¹ with hγdef
  have hγ := h.hγ
  have hL3 := h.hL
  have : NeZero L := ⟨by omega⟩
  intro M
  have hM : M = dysonMat 1 γ L E m := by simp only [M, hb, hγg]
  rw [hγg, hM]
  have hg2L : g ^ 2 ≤ L := by
    have : (1 : ℝ) * g ^ 2 ≤ Rs * g ^ 2 := by gcongr; linarith
    linarith
  refine ⟨⟨?_, ?_⟩, fun a b => ?_, fun a => ?_, fun u hu0 hu1 a => ?_, fun u hu0 hu a b => ?_⟩
  · obtain ⟨him, -⟩ := h.wf h.hm
    have h32 : 32 / k ≤ C' := by simp only [hC'def]; linarith
    have : (32 / k)⁻¹ ≤ m.im := by rw [inv_div]; linarith
    exact le_trans (inv_anti₀ (by positivity) h32) this
  · obtain ⟨-, hmn, -⟩ := h.wf h.hm
    have : 2 / k ≤ 4 / k := by gcongr; norm_num
    have h4 : 4 / k ≤ C' := by simp only [hC'def]; linarith
    linarith [Complex.im_le_norm m]
  · refine (h.M_le_exp a b).trans ?_
    have h1 : Real.exp (-(k / 1024 * γ * cycDist a b)) ≤ 1 := by
      rw [← Real.exp_zero]; apply Real.exp_le_exp.mpr
      have : 0 ≤ k / 1024 * γ * cycDist a b := by positivity
      linarith
    have h4 : 4 / k ≤ C' := by simp only [hC'def]; linarith
    calc 4 / k * Real.exp (-(k / 1024 * γ * cycDist a b)) ≤ 4 / k * 1 := by gcongr
      _ ≤ C' := by linarith
  · have hrow := pairP_row_sum 1 γ hγ L (by omega) E m h.hroot a
    have hMr := h.M_row a 0 le_rfl (by positivity)
    simp only [zero_mul, Real.exp_zero, one_mul] at hMr
    simp only [pairP, Matrix.of_apply] at hrow
    rw [Finset.sum_add_distrib, mul_add, Finset.mul_sum (s := Finset.univ)
      (f := fun b => ‖dysonMat 1 γ L (↑E) m a b‖ ^ 2), hrow]
    have h1 : γ * ∑ b, ‖dysonMat 1 γ L (↑E) m a b‖ ≤ 16384 / k ^ 2 := by
      calc γ * ∑ b, ‖dysonMat 1 γ L (↑E) m a b‖ ≤ γ * (16384 / (k ^ 2 * γ)) := by gcongr
        _ = 16384 / k ^ 2 := by field_simp
    simp only [hC'def]; linarith
  · have hst := h.stable_row u hu0 hu1 a 0 le_rfl (by positivity)
    simp only [zero_mul, Real.exp_zero, one_mul] at hst
    refine hst.trans ?_
    simp only [hC'def]; linarith
  · -- the kernel bounds (6.3) [fo:eq:kernel-bounds]
    have hW3 : (0 : ℝ) < (W : ℝ) ^ (-3 : ℝ) := Real.rpow_pos_of_pos hW0 _
    set δ := 1 - u with hδdef
    have hδ0 : 0 < δ := lt_of_lt_of_le hW3 hu
    have hδ1 : δ ≤ 1 := by linarith
    have hu1 : u < 1 := by linarith
    have hProw : ∀ a, ∑ b, pairP γ (dysonMat 1 γ L E m) a b = 1 :=
      fun a => pairP_row_sum 1 γ hγ L (by omega) E m h.hroot a
    have hnn := mixedKer_nonneg_row (pairP γ (dysonMat 1 γ L E m)) (fun a b => h.P_nonneg a b)
      hProw u hu0 hu1
    refine ⟨hnn.1 a b, ?_⟩
    obtain ⟨hℓu1, hℓu2⟩ := lg_ellProp_cmp hg1 (L := L) δ hδ0 hδ1
    rw [show 1 - δ = u by rw [hδdef]; ring] at hℓu1 hℓu2
    set ℓ := min (L : ℝ) (g ^ 2 / Real.sqrt δ) with hℓ
    set ℓu := ellProp g L u with hℓu
    have hsδ : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ0
    have hsδ1 : Real.sqrt δ ≤ 1 := Real.sqrt_le_one.mpr hδ1
    have hℓg : g ^ 2 ≤ ℓ := by
      apply le_min hg2L
      rw [le_div_iff₀ hsδ]; nlinarith
    have hℓu0 : 0 < ℓu := lt_of_lt_of_le (lt_of_lt_of_le hg2 hℓg) hℓu1
    have hrem0 : 0 ≤ ℓu⁻¹ * (W : ℝ) ^ (-A) := by positivity
    by_cases hu2 : u ≤ 1 / 2
    · -- early times
      have hK := h.kernel_early u hu0 hu2 a b
      have hδ2 : 1 / 2 ≤ δ := by linarith
      have hℓu4 : ℓu ≤ 4 * g ^ 2 := by
        have h1 : ℓ ≤ g ^ 2 / Real.sqrt δ := min_le_right _ _
        have h2 : g ^ 2 / Real.sqrt δ ≤ 2 * g ^ 2 := by
          rw [div_le_iff₀ hsδ]
          have : 1 / 2 ≤ Real.sqrt δ := by
            rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
              rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
            exact Real.sqrt_le_sqrt (by linarith)
          nlinarith
        linarith
      have hγℓ : 1 / ℓu ≤ γ := by
        rw [hγdef, ← one_div]
        exact div_le_div_of_nonneg_left zero_le_one hg2 (le_trans hℓg hℓu1)
      have hexp : Real.exp (-(k ^ 4 * γ / 536870912 * cycDist a b)) ≤
          Real.exp (-(c * cycDist a b / ℓu)) := by
        apply Real.exp_le_exp.mpr
        have h1 : c * cycDist a b / ℓu ≤ k ^ 4 / 536870912 * γ * cycDist a b := by
          rw [show c * cycDist a b / ℓu = c * (1 / ℓu) * cycDist a b by ring]
          gcongr
        have : k ^ 4 * γ / 536870912 * cycDist a b = k ^ 4 / 536870912 * γ * cycDist a b := by ring
        linarith
      have hpre : 128 * γ / k ^ 2 ≤ C' / ((1 - u) * ℓu) := by
        rw [div_le_div_iff₀ hk2p (by positivity)]
        have h1 : (1 - u) * ℓu ≤ 4 * g ^ 2 := by nlinarith
        have h2 : 128 * γ * ((1 - u) * ℓu) ≤ 128 * γ * (4 * g ^ 2) := by gcongr
        have h3 : 128 * γ * (4 * g ^ 2) = 512 := by rw [hγdef]; field_simp; norm_num
        have h4 : 512 ≤ C' * k ^ 2 := by
          have : 512 / k ^ 2 ≤ C' := by simp only [hC'def]; linarith
          rwa [div_le_iff₀ hk2p] at this
        linarith
      calc mixedKer (pairP γ (dysonMat 1 γ L E m)) u a b
          ≤ 128 * γ / k ^ 2 * Real.exp (-(k ^ 4 * γ / 536870912 * cycDist a b)) := hK
        _ ≤ C' / ((1 - u) * ℓu) * Real.exp (-(c * cycDist a b / ℓu)) := by gcongr
        _ ≤ _ := le_add_of_nonneg_right hrem0
    · -- late times
      push Not at hu2
      have hδ2 : δ ≤ 1 / 2 := by linarith
      have hK := h.kernel_late hb hγg hg1 hγdef hg2L δ hδ0 hδ2 CG HG a b
      rw [show 1 - δ = u by rw [hδdef]; ring] at hK
      refine hK.trans (add_le_add ?_ ?_)
      · have h1 : 32 * CG' ≤ C' := by simp only [hC'def]; linarith
        have h2 : Real.exp (-(cycDist a b / (CG' * ℓu))) ≤ Real.exp (-(c * cycDist a b / ℓu)) := by
          apply Real.exp_le_exp.mpr
          have : c * cycDist a b / ℓu ≤ cycDist a b / (CG' * ℓu) := by
            rw [show c * cycDist a b / ℓu = c * (cycDist a b / ℓu) by ring,
              show (cycDist a b : ℝ) / (CG' * ℓu) = 1 / CG' * (cycDist a b / ℓu) by
                field_simp]
            gcongr
          linarith
        exact mul_le_mul (div_le_div_of_nonneg_right h1 (by positivity)) h2 (Real.exp_pos _).le
          (by positivity)
      · -- the remainder
        set εt := 10000000000 / k ^ 6 * (1 + γ * L) * Real.exp (-(3 * k / 4096 * (γ * L)))
        have hεt : εt ≤ epsL (10000000000 / k ^ 6) (3 * k / 4096) g L := by
          unfold epsL
          have hH : (L : ℝ) / g ^ 2 = γ * L := by rw [hγdef]; ring
          rw [hH]
          have hC₀ : (1 : ℝ) ≤ 10000000000 / k ^ 6 := by
            rw [le_div_iff₀ (by positivity)]; have : k ^ 6 ≤ 1 := pow_le_one₀ hk.le hk1
            linarith
          have hH0 : 0 ≤ γ * L := by positivity
          have h1 : 1 ≤ 1 + γ * L := by linarith
          have h2 : 1 + γ * L ≤ (1 + γ * L) ^ (10000000000 / k ^ 6) := by
            simpa using Real.rpow_le_rpow_of_exponent_le h1 hC₀
          have e : Real.exp (-(3 * k / 4096 * L / g ^ 2)) = Real.exp (-(3 * k / 4096 * (γ * L))) :=
              by
            rw [hγdef]; ring_nf
          rw [e]
          simp only [εt]; gcongr
        have hg0 : 0 < g := by linarith
        have hCrQL : CrQ * g ^ 2 * Real.log W ≤ L := by
          refine le_trans ?_ hL
          have : 0 ≤ g ^ 2 * Real.log W := by positivity
          have h1 : CrQ ≤ max CrQ (max Rs 1) := le_max_left _ _
          nlinarith
        have hka' := hka W hWW₁ δ g hu hg0 L hCrQL
        have hδ3 : δ ^ (-(3 : ℝ)) = (δ ^ 3)⁻¹ := by
          rw [Real.rpow_neg hδ0.le]; norm_num
        rw [hδ3] at hka'
        have hε3 : εt ≤ δ ^ 3 * (W : ℝ) ^ (-(A + 1)) := by
          have h1 : epsL (10000000000 / k ^ 6) (3 * k / 4096) g L ≤ δ ^ 3 * (W : ℝ) ^ (-(A + 1)) :=
              by
            have hd3 : 0 < δ ^ 3 := by positivity
            rw [inv_mul_le_iff₀ hd3] at hka'
            exact hka'
          linarith
        have hWA : (W : ℝ) ^ (-(A + 1)) = (W : ℝ) ^ (-A) * (W : ℝ)⁻¹ := by
          rw [show -(A + 1) = -A + (-1) by ring, Real.rpow_add hW0, Real.rpow_neg_one]
        have hW14 : (W : ℝ)⁻¹ ≤ 1 / 4 := by
          rw [inv_le_comm₀ hW0 (by norm_num)]
          have : (4 : ℝ) ≤ W := by exact_mod_cast hW4
          linarith
        have hWApos : 0 < (W : ℝ) ^ (-A) := Real.rpow_pos_of_pos hW0 _
        have hsδδ : δ ≤ Real.sqrt δ := by
          rw [Real.le_sqrt hδ0.le hδ0.le]; nlinarith
        have hℓu2' : ℓu ≤ 2 * g ^ 2 / δ := by
          have h1 : ℓ ≤ g ^ 2 / Real.sqrt δ := min_le_right _ _
          have h2 : g ^ 2 / Real.sqrt δ ≤ g ^ 2 / δ := div_le_div_of_nonneg_left hg2.le hδ0 hsδδ
          rw [mul_div_assoc]; linarith
        have hinvℓ : δ / (2 * g ^ 2) ≤ ℓu⁻¹ := by
          rw [← one_div, div_le_div_iff₀ (by positivity) hℓu0]
          rw [le_div_iff₀ hδ0] at hℓu2'
          linarith
        calc 2 * εt / (g ^ 2 * δ ^ 2) ≤ 2 * (δ ^ 3 * ((W : ℝ) ^ (-A) * (W : ℝ)⁻¹)) /
              (g ^ 2 * δ ^ 2) := by rw [← hWA]; gcongr
          _ = 2 * δ * (W : ℝ)⁻¹ / g ^ 2 * (W : ℝ) ^ (-A) := by field_simp
          _ ≤ 2 * δ * (1 / 4) / g ^ 2 * (W : ℝ) ^ (-A) := by gcongr
          _ = δ / (2 * g ^ 2) * (W : ℝ) ^ (-A) := by field_simp; ring
          _ ≤ ℓu⁻¹ * (W : ℝ) ^ (-A) := by gcongr

/-- Lemma 6.1 [da:lem:scales-propagators], large coupling: (6.2) [fo:eq:propagation-dyson] and
(6.3) [fo:eq:kernel-bounds] with remainder `ℓ_u⁻¹W^{-A}`; `c, C'` do not depend on `A`. -/
theorem scalesProp_large (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ c C' : ℝ, 1 ≤ Cκ ∧ 0 < c ∧ 0 < C' ∧ ∀ A : ℝ, 0 < A → ∃ CA : ℝ, ∃ W₀ : ℕ, 0 < CA ∧
      ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, Cκ ≤ g → ∀ L : ℕ, CA * g ^ 2 * Real.log W ≤ L →
      ∀ E : ℝ, |E| ≤ 2 - κ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m →
      let M := dysonMat (hopB g) (gammaG g) L E m
      (C'⁻¹ ≤ m.im ∧ m.im ≤ C') ∧ (∀ a b, ‖M a b‖ ≤ C') ∧
      (∀ a, gammaG g * ∑ b, (‖M a b‖ + ‖M a b‖ ^ 2) ≤ C') ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ a, ∑ b, ‖(1 - (u : ℂ) • pairQ (gammaG g) M)⁻¹ a b‖ ≤ C') ∧
      ∀ u : ℝ, 0 ≤ u → (W : ℝ) ^ (-3 : ℝ) ≤ 1 - u → ∀ a b,
        0 ≤ mixedKer (pairP (gammaG g) M) u a b ∧
        mixedKer (pairP (gammaG g) M) u a b ≤
          C' / ((1 - u) * ellProp g L u) * Real.exp (-(c * cycDist a b / ellProp g L u)) +
            (ellProp g L u)⁻¹ * (W : ℝ) ^ (-A) := by
  exact lg_scalesProp_aux κ hκ hκ2

end LSBA
