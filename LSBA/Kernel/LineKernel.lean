import LSBA.Kernel.Defs

/-!
# Line kernels and free interpolation

The periodized geometric kernel of Lemma A.8 [uvp:lem:geom] ((A.34)
[da:eq:geometric-kernel-bounds]), powers of the free transfer matrix, and Lemma 6.5
[da:lem:free-interpolation].
-/

open MeasureTheory Real Filter Topology Complex
open scoped ENNReal

noncomputable section

open scoped Classical

namespace LSBA

/-- The decay factor is nonzero and `w = b (ρ + ρ⁻¹)`, (A.4) [da:eq:free-decay-factor]. -/
private lemma freeRho_aux (b : ℝ) (hb : 0 < b) (w : ℂ) (hw : 0 < w.im) :
    freeRho b w ≠ 0 ∧ w = b * (freeRho b w + (freeRho b w)⁻¹) := by
  have hs2 := freeS_sq b w
  have him : 0 < (w + freeS b w).im := by
    rw [Complex.add_im]; linarith [freeS_im_pos b w hw]
  have hne : w + freeS b w ≠ 0 := by
    intro h; rw [h] at him; simp at him
  have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have h2b : (2 * (b : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hb'
  refine ⟨?_, ?_⟩
  · unfold freeRho
    exact div_ne_zero h2b hne
  · unfold freeRho
    rw [inv_div]
    field_simp
    linear_combination (-1 : ℂ) * hs2

/-- `cosh λ = 1 + δ/(2D)`, the defining relation of the decay rate, (A.28) [ba:eq:linekernel]. -/
private lemma cosh_lamGeo {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) :
    Real.cosh (lamGeo D δ) = 1 + δ / (2 * D) :=
  Real.cosh_arcosh (by have : 0 < δ / (2 * D) := by positivity
                       linarith)

/-- The decay rate is positive. -/
private lemma lamGeo_pos {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) : 0 < lamGeo D δ :=
  Real.arcosh_pos (by have : 0 < δ / (2 * D) := by positivity
                      linarith)

/-- `√(δ(δ + 4D)) = 2D sinh λ`. -/
private lemma sqrt_eq_two_mul_sinh {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) :
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

/-- Periodization at an integer point: `n ↦ Σ_j p(n + jL)`. -/
private def perZ (p : ℤ → ℝ) (L : ℕ) (n : ℤ) : ℝ := ∑' j : ℤ, p (n + j * L)

private lemma perZ_summable {p : ℤ → ℝ} (hp : Summable p) {L : ℕ} (hL : 1 ≤ L) (n : ℤ) :
    Summable fun j : ℤ => p (n + j * L) := by
  have hinj : Function.Injective fun j : ℤ => n + j * (L : ℤ) := by
    intro j k h
    have hL' : (L : ℤ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
    have : j * (L : ℤ) = k * L := by simpa using h
    exact mul_right_cancel₀ hL' this
  exact hp.comp_injective hinj

private lemma perZ_add_mul (p : ℤ → ℝ) (L : ℕ) (n k : ℤ) :
    perZ p L (n + k * L) = perZ p L n := by
  unfold perZ
  rw [← (Equiv.addRight k).tsum_eq (fun j : ℤ => p (n + j * L))]
  congr 1
  ext j
  simp only [Equiv.coe_addRight]
  congr 1
  ring

private lemma perZ_sub (p q : ℤ → ℝ) {L : ℕ} (hp : Summable p) (hq : Summable q) (hL : 1 ≤ L)
    (n : ℤ) : perZ p L n - perZ q L n = perZ (fun m => p m - q m) L n := by
  unfold perZ
  rw [← Summable.tsum_sub (perZ_summable hp hL n) (perZ_summable hq hL n)]

/-- The sum over the residues of the periodization is the sum over `ℤ`. -/
private lemma sum_perZ {p : ℤ → ℝ} (hp : Summable p) {L : ℕ} (hL : 1 ≤ L) :
    ∑ x : Fin L, perZ p L x = ∑' n, p n := by
  have : NeZero L := ⟨by omega⟩
  let e : Fin L × ℤ ≃ ℤ := (Equiv.prodComm (Fin L) ℤ).trans (Int.divModEquiv L).symm
  have he : ∀ y : Fin L × ℤ, e y = y.2 * L + (y.1 : ℤ) := by
    intro y; simp [e]
  have h1 : HasSum (fun y : Fin L × ℤ => p (e y)) (∑' n, p n) :=
    (e.hasSum_iff).mpr hp.hasSum
  have h2 : HasSum (fun x : Fin L => perZ p L x) (∑' n, p n) := by
    refine h1.prod_fiberwise (fun x => ?_)
    have := (perZ_summable hp hL (x : ℤ)).hasSum
    simp only [he]
    have h3 : (fun c : ℤ => p (c * L + (x : ℤ))) = fun j => p ((x : ℤ) + j * L) := by
      ext j; ring_nf
    rw [h3]
    exact this
  exact (hasSum_fintype _).unique h2

/-- `Σ_{n ∈ ℤ} c^{|n|}` converges for `0 ≤ c < 1`. -/
private lemma summable_geomAbs {c : ℝ} (h0 : 0 ≤ c) (h1 : c < 1) :
    Summable fun n : ℤ => c ^ n.natAbs := by
  have hg : Summable fun n : ℕ => c ^ n := summable_geometric_of_lt_one h0 h1
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using hg
  · simpa using hg

private lemma tsum_geomAbs {c : ℝ} (h0 : 0 ≤ c) (h1 : c < 1) :
    ∑' n : ℤ, c ^ n.natAbs = (1 + c) / (1 - c) := by
  have hg : Summable fun n : ℕ => c ^ n := summable_geometric_of_lt_one h0 h1
  have hc : (1 - c) ≠ 0 := by linarith
  have e : ∀ n : ℕ, c ^ ((-((n : ℤ) + 1)).natAbs) = c * c ^ n := by
    intro n
    rw [Int.natAbs_neg, show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring,
      Int.natAbs_natCast, pow_succ]
    ring
  rw [tsum_of_nat_of_neg_add_one (f := fun n : ℤ => c ^ n.natAbs)
    (by simpa using hg) ((hg.mul_left c).congr (fun n => (e n).symm))]
  simp only [Int.natAbs_natCast, e]
  rw [tsum_mul_left, tsum_geometric_of_lt_one h0 h1]
  field_simp

private lemma geomAbs_diff {c : ℝ} (h0 : 0 < c) (h1 : c < 1) {A : ℝ} (hA : 0 ≤ A) (n : ℤ) :
    |A * c ^ (n + 1).natAbs - A * c ^ n.natAbs| ≤
      (1 - c) * (A * c ^ n.natAbs + A * c ^ (n + 1).natAbs) := by
  rcases le_or_gt 0 n with hn | hn
  · have e : (n + 1).natAbs = n.natAbs + 1 := by omega
    rw [e, pow_succ]
    have h2 : 0 ≤ A * c ^ n.natAbs := by positivity
    rw [abs_of_nonpos (by nlinarith)]
    nlinarith [mul_nonneg h2 h0.le]
  · have e : n.natAbs = (n + 1).natAbs + 1 := by omega
    rw [e, pow_succ]
    have h2 : 0 ≤ A * c ^ (n + 1).natAbs := by positivity
    rw [abs_of_nonneg (by nlinarith)]
    nlinarith [mul_nonneg h2 h0.le]

private lemma geomAbs_diff2 {c : ℝ} (h0 : 0 < c) (h1 : c < 1) {A : ℝ} (hA : 0 ≤ A) (n : ℤ) :
    |A * c ^ (n + 2).natAbs - 2 * (A * c ^ (n + 1).natAbs) + A * c ^ n.natAbs| ≤
      A * c⁻¹ * (1 - c) ^ 2 * c ^ (n + 1).natAbs + (if n = -1 then 2 * A * (1 - c) else 0) := by
  have hcne : c ≠ 0 := h0.ne'
  rcases lt_trichotomy n (-1) with hn | hn | hn
  · -- `n ≤ -2`
    have e1 : (n + 1).natAbs = (n + 2).natAbs + 1 := by omega
    have e2 : n.natAbs = (n + 2).natAbs + 2 := by omega
    rw [e1, e2, ite_eq_right hn.ne]
    have key : A * c ^ (n + 2).natAbs - 2 * (A * c ^ ((n + 2).natAbs + 1)) +
        A * c ^ ((n + 2).natAbs + 2) = A * c ^ (n + 2).natAbs * (1 - c) ^ 2 := by ring
    have key2 : A * c⁻¹ * (1 - c) ^ 2 * c ^ ((n + 2).natAbs + 1) =
        A * c ^ (n + 2).natAbs * (1 - c) ^ 2 := by
      field_simp; ring
    rw [key, key2, add_zero]
    exact (abs_of_nonneg (by positivity)).le
  · subst hn
    simp only [↓reduceIte]
    have e : ((-1 : ℤ) + 2).natAbs = 1 := by norm_num
    have e' : ((-1 : ℤ) + 1).natAbs = 0 := by norm_num
    have e'' : ((-1 : ℤ)).natAbs = 1 := by norm_num
    rw [e, e', e'']
    have : |A * c ^ 1 - 2 * (A * c ^ 0) + A * c ^ 1| = 2 * A * (1 - c) := by
      rw [show A * c ^ 1 - 2 * (A * c ^ 0) + A * c ^ 1 = -(2 * A * (1 - c)) by ring, abs_neg,
        abs_of_nonneg (by nlinarith)]
    rw [this]
    have : 0 ≤ A * c⁻¹ * (1 - c) ^ 2 * c ^ 0 := by positivity
    linarith
  · have hn0 : 0 ≤ n := by omega
    have e1 : (n + 1).natAbs = n.natAbs + 1 := by omega
    have e2 : (n + 2).natAbs = n.natAbs + 2 := by omega
    rw [e1, e2, ite_eq_right hn.ne']
    have key : A * c ^ (n.natAbs + 2) - 2 * (A * c ^ (n.natAbs + 1)) + A * c ^ n.natAbs =
        A * c ^ n.natAbs * (1 - c) ^ 2 := by ring
    have key2 : A * c⁻¹ * (1 - c) ^ 2 * c ^ (n.natAbs + 1) =
        A * c ^ n.natAbs * (1 - c) ^ 2 := by
      field_simp; ring
    rw [key, key2, add_zero]
    exact (abs_of_nonneg (by positivity)).le

private lemma abs_perZ_le {g B : ℤ → ℝ} (hB : Summable B) (hgB : ∀ n, |g n| ≤ B n) {L : ℕ}
    (hL : 1 ≤ L) (n : ℤ) : |perZ g L n| ≤ perZ B L n := by
  unfold perZ
  have hBs := perZ_summable hB hL n
  have hgs : Summable fun j : ℤ => g (n + j * L) :=
    Summable.of_norm_bounded hBs (fun j => by simpa using hgB _)
  calc |∑' j : ℤ, g (n + j * L)| ≤ ∑' j : ℤ, |g (n + j * L)| := by
        simpa using norm_tsum_le_tsum_norm hgs.norm
    _ ≤ ∑' j : ℤ, B (n + j * L) := Summable.tsum_le_tsum (fun j => hgB _) hgs.abs hBs

/-- The periodization of `A c^{|n|}` at a residue `x < L` is at most `2A/(1 - c^L)`. -/
private lemma perZ_geomAbs_le {c : ℝ} (h0 : 0 < c) (h1 : c < 1) {A : ℝ} (hA : 0 ≤ A) {L : ℕ}
    (hL : 1 ≤ L) (x : ℕ) (hx : x < L) :
    perZ (fun n : ℤ => A * c ^ n.natAbs) L x ≤ 2 * A / (1 - c ^ L) := by
  have hcL0 : 0 ≤ c ^ L := by positivity
  have hcL1 : c ^ L < 1 := pow_lt_one₀ h0.le h1 (by omega)
  have hp : Summable fun n : ℤ => A * c ^ n.natAbs := (summable_geomAbs h0.le h1).mul_left A
  have hg : Summable fun n : ℕ => A * (c ^ L) ^ n :=
    (summable_geometric_of_lt_one hcL0 hcL1).mul_left A
  have hs := perZ_summable hp hL (x : ℤ)
  have hs1 : Summable fun n : ℕ => A * c ^ ((x : ℤ) + (n : ℤ) * L).natAbs := by
    exact hs.comp_injective (i := fun n : ℕ => (n : ℤ)) Nat.cast_injective
  have hinj2 : Function.Injective fun n : ℕ => -((n : ℤ) + 1) := by
    intro a b h; simpa using h
  have hs2 : Summable fun n : ℕ => A * c ^ ((x : ℤ) + (-((n : ℤ) + 1)) * L).natAbs := by
    exact hs.comp_injective hinj2
  have b1 : ∀ n : ℕ, A * c ^ ((x : ℤ) + (n : ℤ) * L).natAbs ≤ A * (c ^ L) ^ n := by
    intro n
    have e : (x : ℤ) + (n : ℤ) * L = ((x + n * L : ℕ) : ℤ) := by push_cast; ring
    rw [e, Int.natAbs_natCast, ← pow_mul']
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one h0.le h1.le (by omega)) hA
  have b2 : ∀ n : ℕ, A * c ^ ((x : ℤ) + (-((n : ℤ) + 1)) * L).natAbs ≤ A * (c ^ L) ^ n := by
    intro n
    have e : (x : ℤ) + (-((n : ℤ) + 1)) * L = (x : ℤ) - ((n * L : ℕ) + (L : ℤ)) := by
      push_cast; ring
    have e2 : ((x : ℤ) - (((n * L : ℕ) : ℤ) + (L : ℤ))).natAbs = n * L + L - x := by omega
    rw [e, e2, ← pow_mul']
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one h0.le h1.le (by omega)) hA
  unfold perZ
  rw [tsum_of_nat_of_neg_add_one (f := fun j : ℤ => A * c ^ ((x : ℤ) + j * L).natAbs)
    hs1 hs2]
  have t1 := Summable.tsum_le_tsum b1 hs1 hg
  have t2 := Summable.tsum_le_tsum b2 hs2 hg
  have hgt : ∑' n : ℕ, A * (c ^ L) ^ n = A * (1 - c ^ L)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hcL0 hcL1]
  rw [hgt] at t1 t2
  have : 2 * A / (1 - c ^ L) = A * (1 - c ^ L)⁻¹ + A * (1 - c ^ L)⁻¹ := by
    field_simp
    ring
  rw [this]
  exact add_le_add t1 t2

/-- Rotation by one step on the residues shifts the argument of the periodization. -/
private lemma perZ_finRotate (p : ℤ → ℝ) {L : ℕ} (hL : 1 ≤ L) (x : Fin L) (k : ℤ) :
    perZ p L ((((finRotate L x : Fin L) : ℕ) : ℤ) + k) = perZ p L (((x : ℕ) : ℤ) + 1 + k) := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  rw [finRotate_apply, Fin.val_add_one x]
  split_ifs with h
  · have hx : ((x : ℕ) : ℤ) = n := by rw [h]; simp
    rw [hx]
    have := perZ_add_mul p (n + 1) k 1
    rw [show ((0 : ℕ) : ℤ) + k = k by simp,
      show (n : ℤ) + 1 + k = k + 1 * ((n + 1 : ℕ) : ℤ) by push_cast; ring, this]
  · congr 1

private lemma perLine_eq (p : ℤ → ℝ) (L : ℕ) (x : Fin L) :
    perLine p L x = perZ p L ((x : ℕ) : ℤ) := rfl

private lemma perZ_comp_add (p : ℤ → ℝ) (L : ℕ) (n k : ℤ) :
    perZ (fun m => p (m + k)) L n = perZ p L (n + k) := by
  unfold perZ
  congr 1
  ext j
  ring_nf

private lemma perZ_add {p q : ℤ → ℝ} (hp : Summable p) (hq : Summable q) {L : ℕ} (hL : 1 ≤ L)
    (n : ℤ) : perZ (fun m => p m + q m) L n = perZ p L n + perZ q L n := by
  unfold perZ
  exact Summable.tsum_add (perZ_summable hp hL n) (perZ_summable hq hL n)

private lemma perZ_const_mul (a : ℝ) (p : ℤ → ℝ) (L : ℕ) (n : ℤ) :
    perZ (fun m => a * p m) L n = a * perZ p L n := by
  unfold perZ
  exact tsum_mul_left

private lemma perZ_second {p : ℤ → ℝ} (hp : Summable p) {L : ℕ} (hL : 1 ≤ L) (n : ℤ) :
    perZ (fun m => p (m + 2) - 2 * p (m + 1) + p m) L n =
      perZ p L (n + 2) - 2 * perZ p L (n + 1) + perZ p L n := by
  have hp1 : Summable fun m => p (m + 1) := (Equiv.addRight (1 : ℤ)).summable_iff.mpr hp
  have hp2 : Summable fun m => p (m + 2) := (Equiv.addRight (2 : ℤ)).summable_iff.mpr hp
  rw [perZ_add (hp2.sub (hp1.mul_left 2)) hp hL,
    show (fun m => p (m + 2) - 2 * p (m + 1)) = fun m => p (m + 2) - (fun m => 2 * p (m + 1)) m
      from rfl,
    ← perZ_sub (fun m => p (m + 2)) (fun m => 2 * p (m + 1)) hp2 (hp1.mul_left 2) hL n,
    perZ_const_mul, perZ_comp_add, perZ_comp_add]

/-- The periodization bounds for the kernel `A c^{|n|}`. -/
private lemma geomAbs_per {c : ℝ} (h0 : 0 < c) (h1 : c < 1) {A : ℝ} (hA : 0 ≤ A) {L : ℕ}
    (hL : 1 ≤ L) :
    ∑ x : Fin L, perLine (fun n : ℤ => A * c ^ n.natAbs) L x = A * ((1 + c) / (1 - c)) ∧
    (∀ x : Fin L, perLine (fun n : ℤ => A * c ^ n.natAbs) L x ≤ 2 * A / (1 - c ^ L)) ∧
    (∀ x : Fin L, |perLine (fun n : ℤ => A * c ^ n.natAbs) L (finRotate L x) -
        perLine (fun n : ℤ => A * c ^ n.natAbs) L x| ≤
      (1 - c) * (perLine (fun n : ℤ => A * c ^ n.natAbs) L x +
        perLine (fun n : ℤ => A * c ^ n.natAbs) L (finRotate L x))) ∧
    ∑ x : Fin L, |perLine (fun n : ℤ => A * c ^ n.natAbs) L (finRotate L (finRotate L x)) -
        2 * perLine (fun n : ℤ => A * c ^ n.natAbs) L (finRotate L x) +
        perLine (fun n : ℤ => A * c ^ n.natAbs) L x| ≤
      A * (1 - c) * (c⁻¹ * (1 + c) + 2) := by
  set p : ℤ → ℝ := fun n => A * c ^ n.natAbs with hpdef
  have hs0 := summable_geomAbs h0.le h1
  have hp : Summable p := hs0.mul_left A
  have hp1 : Summable fun m => p (m + 1) := (Equiv.addRight (1 : ℤ)).summable_iff.mpr hp
  have hc1 : (1 - c) ≠ 0 := by linarith
  have hrot : ∀ x : Fin L, perLine p L (finRotate L x) = perZ p L (((x : ℕ) : ℤ) + 1) := by
    intro x
    have := perZ_finRotate p hL x 0
    rw [add_zero] at this
    rw [perLine_eq]
    exact this
  have hrot2 : ∀ x : Fin L, perLine p L (finRotate L (finRotate L x)) =
      perZ p L (((x : ℕ) : ℤ) + 2) := by
    intro x
    have h1' := perZ_finRotate p hL (finRotate L x) 0
    have h2' := perZ_finRotate p hL x 1
    simp only [add_zero] at h1'
    have := h1'.trans h2'
    rw [show ((x : ℕ) : ℤ) + 1 + 1 = ((x : ℕ) : ℤ) + 2 by ring] at this
    rw [perLine_eq]
    exact this
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [perLine_eq]
    rw [sum_perZ hp hL]
    simp only [hpdef]
    rw [tsum_mul_left, tsum_geomAbs h0.le h1]
  · intro x
    rw [perLine_eq]
    exact perZ_geomAbs_le h0 h1 hA hL x x.isLt
  · intro x
    set Bg : ℤ → ℝ := fun m => (1 - c) * (p m + p (m + 1)) with hBg
    have hBgs : Summable Bg := (hp.add hp1).mul_left _
    have hdiff : perLine p L (finRotate L x) - perLine p L x =
        perZ (fun m => p (m + 1) - p m) L (x : ℕ) := by
      rw [hrot, perLine_eq, ← perZ_comp_add p L, perZ_sub (fun m => p (m + 1)) p hp1 hp hL]
    have hB : perZ Bg L (x : ℕ) = (1 - c) * (perLine p L x + perLine p L (finRotate L x)) := by
      rw [hBg, perZ_const_mul, perZ_add hp hp1 hL, perZ_comp_add, hrot, perLine_eq]
    rw [hdiff, ← hB]
    exact abs_perZ_le hBgs (fun m => geomAbs_diff h0 h1 hA m) hL _
  · set Bh : ℤ → ℝ := fun m => A * c⁻¹ * (1 - c) ^ 2 * c ^ (m + 1).natAbs +
      (if m = -1 then 2 * A * (1 - c) else 0) with hBh
    have hsh : Summable fun m : ℤ => c ^ (m + 1).natAbs :=
      (Equiv.addRight (1 : ℤ)).summable_iff.mpr hs0
    have hBhs1 : Summable fun m : ℤ => A * c⁻¹ * (1 - c) ^ 2 * c ^ (m + 1).natAbs :=
      hsh.mul_left _
    have hBhs2 : Summable fun m : ℤ => (if m = -1 then 2 * A * (1 - c) else 0) :=
      (hasSum_ite_eq (-1 : ℤ) (2 * A * (1 - c))).summable
    have hBhs : Summable Bh := hBhs1.add hBhs2
    have hle : ∀ x : Fin L, |perLine p L (finRotate L (finRotate L x)) -
        2 * perLine p L (finRotate L x) + perLine p L x| ≤ perZ Bh L (x : ℕ) := by
      intro x
      have e : perLine p L (finRotate L (finRotate L x)) -
          2 * perLine p L (finRotate L x) + perLine p L x =
          perZ (fun m => p (m + 2) - 2 * p (m + 1) + p m) L (x : ℕ) := by
        rw [perZ_second hp hL, hrot2, hrot, perLine_eq]
      rw [e]
      exact abs_perZ_le hBhs (fun m => geomAbs_diff2 h0 h1 hA m) hL _
    calc ∑ x : Fin L, |perLine p L (finRotate L (finRotate L x)) -
          2 * perLine p L (finRotate L x) + perLine p L x|
        ≤ ∑ x : Fin L, perZ Bh L (x : ℕ) := Finset.sum_le_sum fun x _ => hle x
      _ = ∑' m, Bh m := sum_perZ hBhs hL
      _ = A * (1 - c) * (c⁻¹ * (1 + c) + 2) := by
        rw [hBh, Summable.tsum_add hBhs1 hBhs2, tsum_mul_left, tsum_ite_eq]
        have hshift : ∑' m : ℤ, c ^ (m + 1).natAbs = (1 + c) / (1 - c) := by
          have := (Equiv.addRight (1 : ℤ)).tsum_eq (fun m : ℤ => c ^ m.natAbs)
          simp only [Equiv.coe_addRight] at this
          rw [this, tsum_geomAbs h0.le h1]
        rw [hshift]
        field_simp

private lemma exp_add_exp_neg_lamGeo {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) :
    Real.exp (lamGeo D δ) + Real.exp (-lamGeo D δ) = 2 + δ / D := by
  have h := cosh_lamGeo hD hδ
  rw [Real.cosh_eq] at h
  have hD0 : D ≠ 0 := hD.ne'
  field_simp at h ⊢
  linarith

/-- `λ² ≤ δ/D`. -/
private lemma sq_lamGeo_le {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) : lamGeo D δ ^ 2 ≤ δ / D := by
  have hlam := lamGeo_pos hD hδ
  have h := exp_add_exp_neg_lamGeo hD hδ
  set lam := lamGeo D δ
  have hcosh : Real.cosh lam = 2 * Real.sinh (lam / 2) ^ 2 + 1 := by
    have := Real.cosh_two_mul (lam / 2)
    rw [show 2 * (lam / 2) = lam by ring, Real.cosh_sq] at this
    linarith
  have hsinh : lam / 2 ≤ Real.sinh (lam / 2) := Real.self_le_sinh_iff.mpr (by positivity)
  have hc : Real.exp lam + Real.exp (-lam) = 2 * Real.cosh lam := by
    rw [Real.cosh_eq]; ring
  have h2 : (lam / 2) ^ 2 ≤ Real.sinh (lam / 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsinh 2
  nlinarith

/-- `δ/D ≤ λ² e^λ`. -/
private lemma div_le_sq_lamGeo {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) :
    δ / D ≤ lamGeo D δ ^ 2 * Real.exp (lamGeo D δ) := by
  have hlam := lamGeo_pos hD hδ
  have h := exp_add_exp_neg_lamGeo hD hδ
  set lam := lamGeo D δ
  have he : Real.exp (-lam) = (Real.exp lam)⁻¹ := Real.exp_neg lam
  have hpos : 0 < Real.exp lam := Real.exp_pos lam
  have h1 : 1 - Real.exp (-lam) ≤ lam := by linarith [Real.add_one_le_exp (-lam)]
  have h2 : 0 ≤ 1 - Real.exp (-lam) := by
    have : Real.exp (-lam) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    linarith
  have h3 : (1 - Real.exp (-lam)) ^ 2 ≤ lam ^ 2 := pow_le_pow_left₀ h2 h1 2
  have h4 : δ / D = (1 - Real.exp (-lam)) ^ 2 * Real.exp lam := by
    rw [he] at h ⊢
    have : δ / D = Real.exp lam + (Real.exp lam)⁻¹ - 2 := by linarith
    rw [this]
    field_simp
    ring
  rw [h4]
  exact mul_le_mul_of_nonneg_right h3 hpos.le

/-- `√(δ(δ+4D)) (1 - e^{-λ}) = δ (1 + e^{-λ})`. -/
private lemma sd_mul_one_sub {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) :
    Real.sqrt (δ * (δ + 4 * D)) * (1 - Real.exp (-lamGeo D δ)) =
      δ * (1 + Real.exp (-lamGeo D δ)) := by
  rw [sqrt_eq_two_mul_sinh hD hδ, Real.sinh_eq]
  have h := exp_add_exp_neg_lamGeo hD hδ
  set lam := lamGeo D δ
  have he : Real.exp (-lam) = (Real.exp lam)⁻¹ := Real.exp_neg lam
  have hpos := Real.exp_pos lam
  have hD0 : D ≠ 0 := hD.ne'
  have hδ' : δ = D * (Real.exp lam + (Real.exp lam)⁻¹ - 2) := by
    rw [he] at h
    field_simp
    field_simp at h
    linarith
  rw [he]
  rw [hδ']
  field_simp
  ring

/-- `2Dλ ≤ √(δ(δ+4D))`. -/
private lemma two_mul_le_sd {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) :
    2 * D * lamGeo D δ ≤ Real.sqrt (δ * (δ + 4 * D)) := by
  rw [sqrt_eq_two_mul_sinh hD hδ]
  exact mul_le_mul_of_nonneg_left (Real.self_le_sinh_iff.mpr (lamGeo_pos hD hδ).le) (by positivity)

private lemma lineKer_eq (D δ : ℝ) (x : ℤ) :
    lineKer D δ x = (Real.sqrt (δ * (δ + 4 * D)))⁻¹ * Real.exp (-lamGeo D δ) ^ x.natAbs := by
  unfold lineKer
  rw [← Real.exp_nat_mul, div_eq_inv_mul]
  have : ((x.natAbs : ℕ) : ℝ) = |(x : ℝ)| := by simp
  rw [this]
  congr 2
  ring

/-- Lemma A.8 [uvp:lem:geom]: (A.34) [da:eq:geometric-kernel-bounds] for the periodized kernel
`Ξ = tP(I-tP)⁻¹`, `t = 1 - δ`, with `D ≍ a²` and `λ ≍ √δ/a`. -/
theorem geom_bounds (κ₁ κ₂ : ℝ) (hκ₁ : 0 < κ₁) (hκ₂ : κ₁ ≤ κ₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a D δ : ℝ) (L : ℕ), 1 ≤ a → κ₁ * a ^ 2 ≤ D → D ≤ κ₂ * a ^ 2 →
      a ≤ L → 0 < δ → δ ≤ 1 →
      let Ξ := perLine (fun x => (1 - δ) * lineKer D δ x) L
      let lam := lamGeo D δ
      let ℓ := min (L : ℝ) (a / Real.sqrt δ)
      (lam ≤ C * Real.sqrt δ / a ∧ Real.sqrt δ / a ≤ C * lam) ∧
      ∑ x, Ξ x ≤ C / δ ∧ (∀ x, Ξ x ≤ C / (δ * ℓ)) ∧
      ∑ x, |Ξ (finRotate L x) - Ξ x| ≤ C * lam / δ ∧
      (∀ x, |Ξ (finRotate L x) - Ξ x| ≤ C * lam / (δ * ℓ)) ∧
      ∑ x, |Ξ (finRotate L (finRotate L x)) - 2 * Ξ (finRotate L x) + Ξ x| ≤
        C * lam ^ 2 / δ := by
  have hκ₂p : 0 < κ₂ := lt_of_lt_of_le hκ₁ hκ₂
  set m : ℝ := 1 + 1 / κ₁ with hm
  have hm1 : 1 ≤ m := by have : 0 < 1 / κ₁ := by positivity
                         linarith
  have hexpm : 1 ≤ Real.exp m := Real.one_le_exp (by linarith)
  set C₀ : ℝ := 1 + 1 / κ₁ + κ₂ * Real.exp m with hC₀
  have hC₀1 : 1 ≤ C₀ := by have : 0 < 1 / κ₁ := by positivity
                           have : 0 < κ₂ * Real.exp m := by positivity
                           linarith
  have hC₀a : 1 / κ₁ ≤ C₀ := by have : 0 < κ₂ * Real.exp m := by positivity
                                linarith
  have hC₀b : κ₂ * Real.exp m ≤ C₀ := by have : 0 < 1 / κ₁ := by positivity
                                         linarith
  set C₂ : ℝ := (C₀ + C₀ ^ 2) / κ₁ with hC₂
  set C₃ : ℝ := 2 * C₀ ^ 2 / κ₁ with hC₃
  set C₅ : ℝ := Real.exp m * C₃ with hC₅
  have hC₂p : 0 < C₂ := by positivity
  have hC₃p : 0 < C₃ := by positivity
  have hC₅p : 0 < C₅ := by positivity
  set C : ℝ := 1 + C₀ + C₂ + C₃ + 2 * C₂ + C₅ with hC
  have hCp : 0 < C := by positivity
  have hC1 : 1 ≤ C := by linarith
  have hC0 : C₀ ≤ C := by linarith
  have hCC₂ : 2 * C₂ ≤ C := by linarith
  have hCC₂' : C₂ ≤ C := by linarith
  have hCC₃ : C₃ ≤ C := by linarith
  have hCC₅ : C₅ ≤ C := by linarith
  refine ⟨C, hCp, ?_⟩
  intro a D δ L ha hD1 hD2 haL hδ hδ1
  dsimp only
  have ha0 : 0 < a := by linarith
  have hD : 0 < D := by nlinarith [mul_pos hκ₁ (mul_pos ha0 ha0)]
  have hL1 : (1 : ℝ) ≤ L := le_trans ha haL
  have hL : 1 ≤ L := by exact_mod_cast hL1
  have hL0 : (0 : ℝ) < L := by linarith
  -- the square root of `δ`
  set s : ℝ := Real.sqrt δ with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hδ
  have hs2 : s ^ 2 = δ := Real.sq_sqrt hδ.le
  have hs1 : s ≤ 1 := by nlinarith
  -- the line-kernel parameters
  have hlam0 : 0 < lamGeo D δ := lamGeo_pos hD hδ
  have hlam_sq : lamGeo D δ ^ 2 ≤ δ / D := sq_lamGeo_le hD hδ
  have hlam_sq' : δ / D ≤ lamGeo D δ ^ 2 * Real.exp (lamGeo D δ) := div_le_sq_lamGeo hD hδ
  have hSd2 : 2 * D * lamGeo D δ ≤ Real.sqrt (δ * (δ + 4 * D)) := two_mul_le_sd hD hδ
  have hSdc : Real.sqrt (δ * (δ + 4 * D)) * (1 - Real.exp (-lamGeo D δ)) =
      δ * (1 + Real.exp (-lamGeo D δ)) := sd_mul_one_sub hD hδ
  have hker := lineKer_eq D δ
  set lam := lamGeo D δ with hlam
  set c := Real.exp (-lam) with hc
  set Sd := Real.sqrt (δ * (δ + 4 * D)) with hSd
  have hc0 : 0 < c := Real.exp_pos _
  have hc1 : c < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hSdpos : 0 < Sd := Real.sqrt_pos.mpr (by positivity)
  have hcexp : Real.exp lam = c⁻¹ := by rw [hc, Real.exp_neg, inv_inv]
  have h1c : 1 - c ≤ lam := by linarith [Real.add_one_le_exp (-lam)]
  have h1c0 : 0 ≤ 1 - c := by linarith
  -- comparison of `λ` with `√δ / a`
  have ha2 : 1 ≤ a ^ 2 := one_le_pow₀ ha
  have hu : δ / D ≤ 1 / κ₁ := by
    rw [div_le_div_iff₀ hD hκ₁]
    have h1 : κ₁ ≤ κ₁ * a ^ 2 := le_mul_of_one_le_right hκ₁.le ha2
    have h2 : δ * κ₁ ≤ κ₁ := mul_le_of_le_one_left hκ₁.le hδ1
    linarith
  have hlam_m : lam ≤ m := by
    by_contra h
    rw [not_le] at h
    have h1 : m ^ 2 < lam ^ 2 := pow_lt_pow_left₀ h (by linarith) two_ne_zero
    have h2 : m ≤ m ^ 2 := by nlinarith only [hm1]
    have h3 : 0 < 1 / κ₁ := by positivity
    linarith
  have hK1 : lam * a ≤ C₀ * s := by
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp ?_
    have h1 : (lam * a) ^ 2 ≤ δ / κ₁ := by
      have h2 : lam ^ 2 * a ^ 2 ≤ (δ / D) * a ^ 2 :=
        mul_le_mul_of_nonneg_right hlam_sq (sq_nonneg a)
      have h3 : (δ / D) * a ^ 2 ≤ δ / κ₁ := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hD hκ₁]
        have := mul_le_mul_of_nonneg_left hD1 hδ.le
        linarith
      rw [mul_pow]
      exact h2.trans h3
    have h4 : δ / κ₁ ≤ (C₀ * s) ^ 2 := by
      rw [mul_pow, hs2]
      have e : δ / κ₁ = δ * (1 / κ₁) := by ring
      rw [e]
      have : C₀ ≤ C₀ ^ 2 := by nlinarith only [hC₀1]
      calc δ * (1 / κ₁) ≤ δ * C₀ := mul_le_mul_of_nonneg_left hC₀a hδ.le
        _ ≤ δ * C₀ ^ 2 := mul_le_mul_of_nonneg_left this hδ.le
        _ = C₀ ^ 2 * δ := by ring
    exact h1.trans h4
  have hK2 : s ≤ C₀ * lam * a := by
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp ?_
    rw [hs2]
    have h1 : δ = (δ / D) * D := by field_simp
    have h2 : Real.exp lam ≤ Real.exp m := Real.exp_le_exp.mpr hlam_m
    have h5 : C₀ ≤ C₀ ^ 2 := by nlinarith only [hC₀1]
    calc δ = (δ / D) * D := h1
      _ ≤ (lam ^ 2 * Real.exp lam) * D := mul_le_mul_of_nonneg_right hlam_sq' hD.le
      _ ≤ (lam ^ 2 * Real.exp m) * (κ₂ * a ^ 2) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h2 (sq_nonneg _)) hD2 hD.le (by positivity)
      _ = (κ₂ * Real.exp m) * (lam * a) ^ 2 := by ring
      _ ≤ C₀ * (lam * a) ^ 2 := mul_le_mul_of_nonneg_right hC₀b (sq_nonneg _)
      _ ≤ C₀ ^ 2 * (lam * a) ^ 2 := mul_le_mul_of_nonneg_right h5 (sq_nonneg _)
      _ = (C₀ * lam * a) ^ 2 := by ring
  -- the amplitude `A` and its size
  set A : ℝ := (1 - δ) / Sd with hA
  have hA0 : 0 ≤ A := div_nonneg (by linarith) hSdpos.le
  have hfun : (fun x : ℤ => (1 - δ) * lineKer D δ x) = fun n : ℤ => A * c ^ n.natAbs := by
    funext n
    rw [hker n, hA]
    ring
  rw [hfun]
  obtain ⟨hper1, hper2, hper3, hper4⟩ := geomAbs_per hc0 hc1 hA0 hL
  have e1 : 2 * κ₁ * (a * s) ≤ C₀ * Sd := by
    calc 2 * κ₁ * (a * s) = 2 * κ₁ * a * s := by ring
      _ ≤ 2 * κ₁ * a * (C₀ * lam * a) :=
          mul_le_mul_of_nonneg_left hK2 (by positivity)
      _ = C₀ * (2 * (κ₁ * a ^ 2) * lam) := by ring
      _ ≤ C₀ * (2 * D * lam) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right (by linarith) hlam0.le
      _ ≤ C₀ * Sd := mul_le_mul_of_nonneg_left hSd2 (by positivity)
  have e2 : A * Sd = 1 - δ := by rw [hA]; field_simp
  have hAX : 2 * κ₁ * (a * s) * A ≤ C₀ := by
    have e3 : (2 * κ₁ * (a * s) * A) * Sd ≤ C₀ * Sd := by
      calc (2 * κ₁ * (a * s) * A) * Sd = 2 * κ₁ * (a * s) * (A * Sd) := by ring
        _ = 2 * κ₁ * (a * s) * (1 - δ) := by rw [e2]
        _ ≤ 2 * κ₁ * (a * s) * 1 :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ ≤ C₀ * Sd := by linarith
    exact le_of_mul_le_mul_right e3 hSdpos
  have hδle : δ ≤ C₀ * lam * a * s := by
    calc δ = s * s := by rw [← hs2]; ring
      _ ≤ (C₀ * lam * a) * s := mul_le_mul_of_nonneg_right hK2 hs0.le
  have hA4 : 4 * A * δ ≤ C₃ * lam := by
    refine le_of_mul_le_mul_left ?_ hκ₁
    have hk : κ₁ * (C₃ * lam) = 2 * C₀ ^ 2 * lam := by rw [hC₃]; field_simp
    rw [hk]
    calc κ₁ * (4 * A * δ) ≤ κ₁ * (4 * A * (C₀ * lam * a * s)) := by
          apply mul_le_mul_of_nonneg_left _ hκ₁.le
          exact mul_le_mul_of_nonneg_left hδle (by positivity)
      _ = (2 * C₀ * lam) * (2 * κ₁ * (a * s) * A) := by ring
      _ ≤ (2 * C₀ * lam) * C₀ := mul_le_mul_of_nonneg_left hAX (by positivity)
      _ = 2 * C₀ ^ 2 * lam := by ring
  -- the scale `ℓ`
  have hℓ0 : 0 < min (L : ℝ) (a / s) := lt_min hL0 (div_pos ha0 hs0)
  have hℓL : min (L : ℝ) (a / s) ≤ L := min_le_left _ _
  have hℓa : min (L : ℝ) (a / s) * s ≤ a :=
    (le_div_iff₀ hs0).mp (min_le_right _ _)
  set ℓ := min (L : ℝ) (a / s) with hℓ
  have hq0 : 0 < δ * ℓ := mul_pos hδ hℓ0
  have hqa : δ * ℓ ≤ a * s := by
    calc δ * ℓ = s * (ℓ * s) := by rw [← hs2]; ring
      _ ≤ s * a := mul_le_mul_of_nonneg_left hℓa hs0.le
      _ = a * s := by ring
  have hqL : δ * ℓ ≤ s ^ 2 * L := by
    rw [hs2]; exact mul_le_mul_of_nonneg_left hℓL hδ.le
  -- the sup bound
  have hE : 2 * A / (1 - c ^ L) ≤ C₂ / (δ * ℓ) := by
    set t : ℝ := lam * L with ht
    have ht0 : 0 < t := mul_pos hlam0 hL0
    have hcL : c ^ L = Real.exp (-t) := by
      rw [hc, ← Real.exp_nat_mul, ht]; congr 1; ring
    have hexp : Real.exp (-t) ≤ (1 + t)⁻¹ := by
      rw [Real.exp_neg]
      exact inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp t])
    have hden : t / (1 + t) ≤ 1 - c ^ L := by
      rw [hcL]
      have : t / (1 + t) = 1 - (1 + t)⁻¹ := by field_simp; ring
      rw [this]; linarith
    have hden0 : 0 < t / (1 + t) := by positivity
    have step1 : 2 * A / (1 - c ^ L) ≤ 2 * A + 2 * A / t := by
      calc 2 * A / (1 - c ^ L) ≤ 2 * A / (t / (1 + t)) :=
            div_le_div_of_nonneg_left (by positivity) hden0 hden
        _ = 2 * A + 2 * A / t := by field_simp; ring
    have hB2a : 2 * A ≤ (C₀ / κ₁) / (δ * ℓ) := by
      rw [div_div, le_div_iff₀ (mul_pos hκ₁ hq0)]
      calc 2 * A * (κ₁ * (δ * ℓ)) ≤ 2 * A * (κ₁ * (a * s)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hqa hκ₁.le) (by positivity)
        _ = 2 * κ₁ * (a * s) * A := by ring
        _ ≤ C₀ := hAX
    have hB2b : 2 * A / t ≤ (C₀ ^ 2 / κ₁) / (δ * ℓ) := by
      rw [div_div, div_le_div_iff₀ ht0 (mul_pos hκ₁ hq0)]
      refine le_of_mul_le_mul_left ?_ ha0
      calc a * (2 * A * (κ₁ * (δ * ℓ))) ≤ a * (2 * A * (κ₁ * (s ^ 2 * L))) := by
            apply mul_le_mul_of_nonneg_left _ ha0.le
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hqL hκ₁.le)
              (by positivity)
        _ = (2 * κ₁ * (a * s) * A) * (s * L) := by ring
        _ ≤ C₀ * (s * L) := mul_le_mul_of_nonneg_right hAX (by positivity)
        _ ≤ C₀ * ((C₀ * lam * a) * L) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK2 hL0.le) (by linarith)
        _ = a * (C₀ ^ 2 * t) := by rw [ht]; ring
    calc 2 * A / (1 - c ^ L) ≤ 2 * A + 2 * A / t := step1
      _ ≤ (C₀ / κ₁) / (δ * ℓ) + (C₀ ^ 2 / κ₁) / (δ * ℓ) := add_le_add hB2a hB2b
      _ = C₂ / (δ * ℓ) := by rw [hC₂]; ring
  have hΞle : ∀ x : Fin L, perLine (fun n : ℤ => A * c ^ n.natAbs) L x ≤ C₂ / (δ * ℓ) :=
    fun x => (hper2 x).trans hE
  have hC₂ℓ : C₂ / (δ * ℓ) ≤ C / (δ * ℓ) := div_le_div_of_nonneg_right hCC₂' hq0.le
  have hsumΞ : ∑ x : Fin L, perLine (fun n : ℤ => A * c ^ n.natAbs) L x = (1 - δ) / δ := by
    rw [hper1]
    have h1c' : (1 - c) ≠ 0 := by linarith
    have : (1 + c) / (1 - c) = Sd / δ := by
      rw [div_eq_div_iff h1c' hδ.ne']
      linarith [hSdc]
    rw [this, hA]
    field_simp
  set Ξ := perLine (fun n : ℤ => A * c ^ n.natAbs) L with hΞ
  have h4A : 4 * A ≤ C₃ * lam / δ := (le_div_iff₀ hδ).mpr (by linarith)
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ ha0]
    exact hK1.trans (mul_le_mul_of_nonneg_right hC0 hs0.le)
  · rw [div_le_iff₀ ha0]
    calc s ≤ C₀ * lam * a := hK2
      _ ≤ C * lam * a := by
          apply mul_le_mul_of_nonneg_right _ ha0.le
          exact mul_le_mul_of_nonneg_right hC0 hlam0.le
      _ = C * lam * a := rfl
  · rw [hsumΞ]
    exact div_le_div_of_nonneg_right (by linarith) hδ.le
  · exact fun x => (hΞle x).trans hC₂ℓ
  · have h1c' : (1 - c) ≠ 0 := by linarith
    calc ∑ x : Fin L, |Ξ (finRotate L x) - Ξ x|
        ≤ ∑ x : Fin L, (1 - c) * (Ξ x + Ξ (finRotate L x)) :=
          Finset.sum_le_sum fun x _ => hper3 x
      _ = 2 * (1 - c) * ∑ x : Fin L, Ξ x := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib,
            Equiv.sum_comp (finRotate L) (fun x => Ξ x)]
          ring
      _ = 2 * A * (1 + c) := by
          rw [hper1]; field_simp
      _ ≤ 4 * A := by nlinarith only [hA0, hc1]
      _ ≤ C₃ * lam / δ := h4A
      _ ≤ C * lam / δ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCC₃ hlam0.le) hδ.le
  · intro x
    have hS : Ξ x + Ξ (finRotate L x) ≤ C₂ / (δ * ℓ) + C₂ / (δ * ℓ) :=
      add_le_add (hΞle x) (hΞle _)
    have hS0 : 0 ≤ C₂ / (δ * ℓ) + C₂ / (δ * ℓ) := by positivity
    calc |Ξ (finRotate L x) - Ξ x| ≤ (1 - c) * (Ξ x + Ξ (finRotate L x)) := hper3 x
      _ ≤ (1 - c) * (C₂ / (δ * ℓ) + C₂ / (δ * ℓ)) := mul_le_mul_of_nonneg_left hS h1c0
      _ ≤ lam * (C₂ / (δ * ℓ) + C₂ / (δ * ℓ)) := mul_le_mul_of_nonneg_right h1c hS0
      _ = (2 * C₂) * lam / (δ * ℓ) := by ring
      _ ≤ C * lam / (δ * ℓ) := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCC₂ hlam0.le) hq0.le
  · have hce : c⁻¹ ≤ Real.exp m := by
      rw [← hcexp]; exact Real.exp_le_exp.mpr hlam_m
    have hcinv : 0 ≤ c⁻¹ := inv_nonneg.mpr hc0.le
    have hb : c⁻¹ * (1 + c) + 2 ≤ 4 * Real.exp m := by
      have : c⁻¹ * (1 + c) ≤ c⁻¹ * 2 := mul_le_mul_of_nonneg_left (by linarith) hcinv
      nlinarith only [this, hce, hexpm]
    have hb0 : 0 ≤ c⁻¹ * (1 + c) + 2 := by positivity
    calc ∑ x : Fin L, |Ξ (finRotate L (finRotate L x)) - 2 * Ξ (finRotate L x) + Ξ x|
        ≤ A * (1 - c) * (c⁻¹ * (1 + c) + 2) := hper4
      _ ≤ A * lam * (4 * Real.exp m) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1c hA0) hb hb0 (by positivity)
      _ = (4 * A) * (Real.exp m * lam) := by ring
      _ ≤ (C₃ * lam / δ) * (Real.exp m * lam) :=
          mul_le_mul_of_nonneg_right h4A (by positivity)
      _ = C₅ * lam ^ 2 / δ := by rw [hC₅]; ring
      _ ≤ C * lam ^ 2 / δ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCC₅ (sq_nonneg _)) hδ.le

/-- Three-term recurrence of the sine. -/
private lemma sin_step (x ϑ : ℝ) :
    Real.sin (x + ϑ) = 2 * Real.cos ϑ * Real.sin x - Real.sin (x - ϑ) := by
  rw [Real.sin_add, Real.sin_sub]
  ring

set_option linter.flexible false in
/-- Chebyshev form of the powers of `T(2cos ϑ)`, scaled by `sin ϑ`. -/
private lemma transferT_pow_smul (ϑ : ℝ) (j : ℕ) :
    Real.sin ϑ • transferT (2 * Real.cos ϑ) ^ j =
      !![Real.sin ((j + 1) * ϑ), -Real.sin (j * ϑ);
        Real.sin (j * ϑ), -Real.sin ((j - 1) * ϑ)] := by
  induction j with
  | zero =>
    ext i k
    fin_cases i <;> fin_cases k <;> simp [Real.sin_neg]
  | succ j ih =>
    rw [pow_succ, ← smul_mul_assoc, ih]
    ext i k
    fin_cases i <;> fin_cases k <;> simp [transferT, Matrix.mul_apply, Fin.sum_univ_two]
    · have h := sin_step (((j : ℝ) + 1) * ϑ) ϑ
      rw [show ((j : ℝ) + 1 + 1) * ϑ = ((j : ℝ) + 1) * ϑ + ϑ by ring, h,
        show ((j : ℝ) + 1) * ϑ - ϑ = j * ϑ by ring]
      ring
    · have h := sin_step ((j : ℝ) * ϑ) ϑ
      rw [show ((j : ℝ) + 1) * ϑ = (j : ℝ) * ϑ + ϑ by ring, h,
        show (j : ℝ) * ϑ - ϑ = ((j : ℝ) - 1) * ϑ by ring]
      ring

/-- The powers of `T(2cos ϑ)` have entries at most `1/sin ϑ` (Chebyshev form), as used in the proof
of Lemma 6.5 [da:lem:free-interpolation]. -/
theorem transferT_pow_le (ϑ : ℝ) (h0 : 0 < ϑ) (hπ : ϑ < π) (j : ℕ) (i k : Fin 2) :
    |(transferT (2 * Real.cos ϑ) ^ j) i k| ≤ (Real.sin ϑ)⁻¹ := by
  have hs : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have h := congrFun (congrFun (transferT_pow_smul ϑ j) i) k
  simp only [Matrix.smul_apply, smul_eq_mul] at h
  have h1 : |Real.sin ϑ * (transferT (2 * Real.cos ϑ) ^ j) i k| ≤ 1 := by
    rw [h]
    fin_cases i <;> fin_cases k <;> simp [abs_sin_le_one]
  rw [abs_mul, abs_of_pos hs] at h1
  rw [← one_div, le_div_iff₀ hs]
  linarith

private lemma fin_val_add_one {n : ℕ} (a : Fin (n + 1)) :
    ((a + 1 : Fin (n + 1)) : ℕ) = (a.val + 1) % (n + 1) := by
  rw [Fin.val_add]; simp [Nat.add_mod]

/-- The cycle adjacency matrix in terms of the group structure of `Fin (n + 1)`. -/
private lemma cycleAdj_fin {n : ℕ} (a b : Fin (n + 1)) :
    cycleAdj (n + 1) a b = (if b = a + 1 then 1 else 0) + (if a = b + 1 then 1 else 0) := by
  unfold cycleAdj
  simp only [Matrix.of_apply]
  have h1 : (b.val = (a.val + 1) % (n + 1)) ↔ b = a + 1 := by
    rw [Fin.ext_iff, fin_val_add_one]
  have h2 : (a.val = (b.val + 1) % (n + 1)) ↔ a = b + 1 := by
    rw [Fin.ext_iff, fin_val_add_one]
  rw [if_congr h1 rfl rfl, if_congr h2 rfl rfl]

private lemma cycleAdj_add {n : ℕ} (τ a b : Fin (n + 1)) :
    cycleAdj (n + 1) (a + τ) (b + τ) = cycleAdj (n + 1) a b := by
  rw [cycleAdj_fin, cycleAdj_fin]
  have e1 : (b + τ = a + τ + 1) ↔ b = a + 1 := by
    rw [add_right_comm a τ 1]; exact add_left_inj τ
  have e2 : (a + τ = b + τ + 1) ↔ a = b + 1 := by
    rw [add_right_comm b τ 1]; exact add_left_inj τ
  simp only [e1, e2]

/-- The inverse of a circulant is translation invariant. -/
private lemma inv_add_invariant {n : ℕ} (w : ℂ) (τ a b : Fin (n + 1)) :
    ((cycleAdj (n + 1) - w • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹) (a + τ) (b + τ) =
    ((cycleAdj (n + 1) - w • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹) a b := by
  set A' := cycleAdj (n + 1) - w • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) with hA'
  have h : A'.submatrix (Equiv.addRight τ) (Equiv.addRight τ) = A' := by
    ext x y
    simp [hA', Matrix.one_apply, cycleAdj_add]
  have := Matrix.inv_submatrix_equiv A' (Equiv.addRight τ) (Equiv.addRight τ)
  rw [h] at this
  exact (congrFun (congrFun this a) b).symm

/-- Row relation of a right inverse of `A_L - w`: `M(a+1, b) + M(a-1, b) - w M(a, b) = δ_{ab}`. -/
private lemma matrix_rec {n : ℕ} (w : ℂ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hM : (cycleAdj (n + 1) - w • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) * M = 1)
    (a b : Fin (n + 1)) :
    M (a + 1) b + M (a - 1) b - w * M a b = if a = b then 1 else 0 := by
  have h := congrFun (congrFun hM a) b
  simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, cycleAdj_fin] at h
  have s1 : ∑ k, (if k = a + 1 then (1 : ℂ) else 0) * M k b = M (a + 1) b := by simp
  have s2 : ∑ k, (if a = k + 1 then (1 : ℂ) else 0) * M k b = M (a - 1) b := by
    rw [Finset.sum_eq_single (a - 1)]
    · simp
    · intro k _ hk
      have : a ≠ k + 1 := by
        intro h'; apply hk; rw [h']; simp
      simp [this]
    · simp
  have s3 : ∑ k, w * (if a = k then (1 : ℂ) else 0) * M k b = w * M a b := by simp
  simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib] at h
  rw [s1, s2, s3] at h
  exact h

/-- Variation of constants for the three-term recurrence `X(i+2) = E X(i+1) - X(i) + f(i)`, with the
fundamental solution `V` (`V 0 = 0`, `V 1 = 1`, `V (t+1) = E V t - V (t-1)`). -/
private lemma duhamel_formula (V : ℝ → ℝ) (E : ℝ) (hV0 : V 0 = 0) (hV1 : V 1 = 1)
    (hV : ∀ t, V (t + 1) = E * V t - V (t - 1)) (X f : ℕ → ℂ)
    (hX : ∀ i, X (i + 2) = (E : ℂ) * X (i + 1) - X i + f i) (j : ℕ) :
    X (j + 1) = (V ((j : ℝ) + 1) : ℂ) * X 1 - (V (j : ℝ) : ℂ) * X 0 +
      ∑ i ∈ Finset.range j, (V ((j : ℝ) - i) : ℂ) * f i := by
  set S : ℕ → ℂ := fun j => ∑ i ∈ Finset.range j, (V ((j : ℝ) - i) : ℂ) * f i with hSdef
  have hVn : ∀ m : ℕ, V ((m : ℝ) + 2) = E * V ((m : ℝ) + 1) - V (m : ℝ) := by
    intro m
    have := hV ((m : ℝ) + 1)
    rw [show (m : ℝ) + 1 + 1 = (m : ℝ) + 2 by ring,
      show (m : ℝ) + 1 - 1 = (m : ℝ) by ring] at this
    exact this
  have hS : ∀ j : ℕ, S (j + 2) = (E : ℂ) * S (j + 1) - S j + f (j + 1) := by
    intro j
    have h1 : S (j + 2) = ∑ i ∈ Finset.range (j + 1), (V (((j + 2 : ℕ) : ℝ) - i) : ℂ) * f i +
        f (j + 1) := by
      simp only [hSdef]
      rw [Finset.sum_range_succ]
      have : V (((j + 2 : ℕ) : ℝ) - ((j + 1 : ℕ) : ℝ)) = 1 := by
        rw [← hV1]; congr 1; push_cast; ring
      rw [this]; simp
    have h2 : ∑ i ∈ Finset.range (j + 1), (V (((j + 2 : ℕ) : ℝ) - i) : ℂ) * f i =
        (E : ℂ) * S (j + 1) - ∑ i ∈ Finset.range (j + 1), (V ((j : ℝ) - i) : ℂ) * f i := by
      simp only [hSdef]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := hV (((j + 1 : ℕ) : ℝ) - i)
      rw [show ((j + 1 : ℕ) : ℝ) - i + 1 = ((j + 2 : ℕ) : ℝ) - i by push_cast; ring,
        show ((j + 1 : ℕ) : ℝ) - i - 1 = (j : ℝ) - i by push_cast; ring] at this
      rw [this]
      push_cast
      ring
    have h3 : ∑ i ∈ Finset.range (j + 1), (V ((j : ℝ) - i) : ℂ) * f i = S j := by
      simp only [hSdef]
      rw [Finset.sum_range_succ]
      simp [hV0]
    rw [h1, h2, h3]
  set U : ℕ → ℂ := fun j => (V ((j : ℝ) + 1) : ℂ) * X 1 - (V (j : ℝ) : ℂ) * X 0 + S j with hU
  have hUrec : ∀ j : ℕ, U (j + 2) = (E : ℂ) * U (j + 1) - U j + f (j + 1) := by
    intro j
    simp only [hU]
    rw [hS j]
    have h1 : V (((j + 2 : ℕ) : ℝ) + 1) = E * V (((j + 1 : ℕ) : ℝ) + 1) - V ((j : ℝ) + 1) := by
      have := hVn (j + 1)
      push_cast at this ⊢
      rw [show (j : ℝ) + 2 + 1 = (j : ℝ) + 1 + 2 by ring] at *
      linarith
    have h2 : V (((j + 2 : ℕ) : ℝ)) = E * V (((j + 1 : ℕ) : ℝ)) - V ((j : ℝ)) := by
      have := hVn j
      push_cast at this ⊢
      exact this
    have h1c : (V (((j + 2 : ℕ) : ℝ) + 1) : ℂ) =
        (E : ℂ) * (V (((j + 1 : ℕ) : ℝ) + 1) : ℂ) - (V ((j : ℝ) + 1) : ℂ) := by
      exact_mod_cast h1
    have h2c : (V (((j + 2 : ℕ) : ℝ)) : ℂ) =
        (E : ℂ) * (V (((j + 1 : ℕ) : ℝ)) : ℂ) - (V ((j : ℝ)) : ℂ) := by
      exact_mod_cast h2
    rw [h1c, h2c]
    ring
  have key : ∀ j : ℕ, X (j + 1) = U j ∧ X (j + 2) = U (j + 1) := by
    intro j
    induction j with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp [hU, hSdef, hV0, hV1]
      · have hV2 : V 2 = E := by
          have := hVn 0
          simp only [Nat.cast_zero, zero_add] at this
          rw [hV0, hV1] at this
          linarith
        have h0 := hX 0
        simp only [hU, hSdef, Nat.cast_zero, Nat.cast_one, zero_add, Finset.sum_range_one,
          sub_zero, hV1]
        rw [show (1 : ℝ) + 1 = 2 by norm_num, hV2]
        simp only [zero_add] at h0
        rw [h0]
        push_cast
        ring
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      have h3 := hX (j + 1)
      rw [show j + 1 + 2 = j + 3 by ring, show j + 1 + 1 = j + 2 by ring] at h3
      change X (j + 3) = U (j + 2)
      rw [h3, ih.2, ih.1, hUrec j]
  exact (key j).1

private lemma finRotate_pow_val {n : ℕ} (b₀ : Fin (n + 1)) (j : ℕ) :
    ((((finRotate (n + 1)) ^ j) b₀ : Fin (n + 1)) : ℕ) = (b₀.val + j) % (n + 1) := by
  induction j with
  | zero => simp [Nat.mod_eq_of_lt b₀.isLt]
  | succ j ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, finRotate_apply, fin_val_add_one, ih,
      Nat.mod_add_mod, ← add_assoc]

private lemma mod_cases (L x : ℕ) (hx : x < 2 * L) :
    x % L = if x < L then x else x - L := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (not_lt.mp h), Nat.mod_eq_of_lt (by omega)]

/-- Within one lap, the rotation `finRotate^i b₀` hits `b` exactly for `i` equal to the offset. -/
private lemma pow_eq_iff {n : ℕ} (b₀ b : Fin (n + 1)) (i : ℕ) (hi : i < n + 1) :
    ((finRotate (n + 1)) ^ i) b₀ = b ↔ i = (b.val + (n + 1) - b₀.val) % (n + 1) := by
  rw [Fin.ext_iff, finRotate_pow_val]
  have hb0 := b₀.isLt
  have hb := b.isLt
  have e1 := mod_cases (n + 1) (b₀.val + i) (by omega)
  have e2 := mod_cases (n + 1) (b.val + (n + 1) - b₀.val) (by omega)
  rw [e1, e2]
  split_ifs <;> omega

private lemma source_sum {n : ℕ} (V : ℝ → ℝ) (b₀ b : Fin (n + 1)) (j : ℕ) (hj : j < n + 1) :
    ∑ i ∈ Finset.range j, (V ((j : ℝ) - i) : ℂ) *
        (if ((finRotate (n + 1)) ^ i) b₀ = b then (1 : ℂ) else 0) =
      if (b.val + (n + 1) - b₀.val) % (n + 1) < j then
        (V ((j : ℝ) - ((b.val + (n + 1) - b₀.val) % (n + 1) : ℕ)) : ℂ) else 0 := by
  set k := (b.val + (n + 1) - b₀.val) % (n + 1) with hk
  have : ∀ i ∈ Finset.range j, (V ((j : ℝ) - i) : ℂ) *
      (if ((finRotate (n + 1)) ^ i) b₀ = b then (1 : ℂ) else 0) =
      if i = k then (V ((j : ℝ) - i) : ℂ) else 0 := by
    intro i hi
    have hi' : i < n + 1 := lt_of_lt_of_le (Finset.mem_range.mp hi) hj.le
    rw [if_congr (pow_eq_iff b₀ b i hi') rfl rfl]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' (Finset.range j) k]
  simp only [Finset.mem_range]

/-- The interpolation identity of Lemma 6.5 [da:lem:free-interpolation] as an exact equation
for a right inverse `M` of `A_L - w`: the remainder is `(w - 2cos ϑ)` times a convolution. -/
private lemma fi_cell {n : ℕ} (w : ℂ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hM : (cycleAdj (n + 1) - w • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) * M = 1)
    (ϑ : ℝ) (hs : Real.sin ϑ ≠ 0) (b₀ b : Fin (n + 1)) (j : ℕ) (hj : j < n + 1) :
    M ((finRotate (n + 1) ^ j) b₀) b =
      ((Real.sin (((j : ℝ) + 1) * ϑ) / Real.sin ϑ : ℝ) : ℂ) * M b₀ b -
      ((Real.sin ((j : ℝ) * ϑ) / Real.sin ϑ : ℝ) : ℂ) * M ((finRotate (n + 1)).symm b₀) b +
      ((if (b.val + (n + 1) - b₀.val) % (n + 1) < j then
        Real.sin (((j : ℝ) - (((b.val + (n + 1) - b₀.val) % (n + 1) : ℕ) : ℝ)) * ϑ) /
          Real.sin ϑ else 0 : ℝ) : ℂ) +
      (w - ((2 * Real.cos ϑ : ℝ) : ℂ)) *
        ∑ i ∈ Finset.range j, ((Real.sin (((j : ℝ) - i) * ϑ) / Real.sin ϑ : ℝ) : ℂ) *
          M ((finRotate (n + 1) ^ i) b₀) b := by
  set σ := finRotate (n + 1) with hσ
  set V : ℝ → ℝ := fun t => Real.sin (t * ϑ) / Real.sin ϑ with hV
  set E : ℝ := 2 * Real.cos ϑ with hE
  set X : ℕ → ℂ := fun m => M (σ.symm ((σ ^ m) b₀)) b with hXdef
  set δ : ℕ → ℂ := fun i => if (σ ^ i) b₀ = b then 1 else 0 with hδ
  set f : ℕ → ℂ := fun i => δ i + (w - (E : ℂ)) * X (i + 1) with hf
  have hX1 : ∀ m, X (m + 1) = M ((σ ^ m) b₀) b := by
    intro m
    simp only [hXdef]
    rw [pow_succ', Equiv.Perm.mul_apply, Equiv.symm_apply_apply]
  have hrec : ∀ i, X (i + 2) = (E : ℂ) * X (i + 1) - X i + f i := by
    intro i
    have hr := matrix_rec w M hM ((σ ^ i) b₀) b
    have e1 : (σ ^ i) b₀ + 1 = (σ ^ (i + 1)) b₀ := by
      rw [pow_succ', Equiv.Perm.mul_apply, hσ, finRotate_apply]
    have e2 : (σ ^ i) b₀ - 1 = σ.symm ((σ ^ i) b₀) := by
      rw [hσ, finRotate_symm_apply]
    rw [e1, e2] at hr
    have h2 : X (i + 2) = M ((σ ^ (i + 1)) b₀) b := hX1 (i + 1)
    have h1 : X (i + 1) = M ((σ ^ i) b₀) b := hX1 i
    have h0 : X i = M (σ.symm ((σ ^ i) b₀)) b := rfl
    simp only [hf, hδ]
    rw [h2, h1, h0]
    linear_combination hr
  have hV0 : V 0 = 0 := by simp [hV]
  have hV1 : V 1 = 1 := by simp [hV, div_self hs]
  have hVrec : ∀ t, V (t + 1) = E * V t - V (t - 1) := by
    intro t
    simp only [hV, hE]
    rw [show (t + 1) * ϑ = t * ϑ + ϑ by ring, show (t - 1) * ϑ = t * ϑ - ϑ by ring, sin_step]
    ring
  have hD := duhamel_formula V E hV0 hV1 hVrec X f hrec j
  have hXj : X (j + 1) = M ((σ ^ j) b₀) b := hX1 j
  have hX1' : X 1 = M b₀ b := by rw [hX1 0]; simp
  have hX0 : X 0 = M (σ.symm b₀) b := by simp [hXdef]
  have hsum : ∑ i ∈ Finset.range j, (V ((j : ℝ) - i) : ℂ) * f i =
      ∑ i ∈ Finset.range j, (V ((j : ℝ) - i) : ℂ) * δ i +
        (w - (E : ℂ)) * ∑ i ∈ Finset.range j, (V ((j : ℝ) - i) : ℂ) * M ((σ ^ i) b₀) b := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hf]
    rw [hX1 i]
    ring
  have hsrc := source_sum V b₀ b j hj
  rw [hXj, hX1', hX0, hsum] at hD
  rw [hD]
  simp only [hδ] at *
  rw [hsrc]
  have hite : (if (b.val + (n + 1) - b₀.val) % (n + 1) < j then
        (V ((j : ℝ) - (((b.val + (n + 1) - b₀.val) % (n + 1) : ℕ) : ℝ)) : ℂ) else 0) =
      ((if (b.val + (n + 1) - b₀.val) % (n + 1) < j then
        V ((j : ℝ) - (((b.val + (n + 1) - b₀.val) % (n + 1) : ℕ) : ℝ)) else 0 : ℝ) : ℂ) := by
    split_ifs <;> simp
  rw [hite]
  simp only [hV]
  ring

/-- Away from the band edges, `|s(w)| ≥ κ/2`. -/
private lemma fi_s_lower {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) {w : ℂ}
    (hw : ‖w - E‖ ≤ κ / 2) : κ / 2 ≤ ‖freeS 1 w‖ := by
  have hre : |w.re - E| ≤ κ / 2 := by
    have := Complex.abs_re_le_norm (w - (E : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    exact this.trans hw
  have hE' := abs_le.mp hE
  have hre' := abs_le.mp hre
  have h1 : κ / 2 ≤ ‖w - 2‖ := by
    have h3 : (w - 2).re = w.re - 2 := by simp
    have h4 := Complex.abs_re_le_norm (w - 2)
    have h5 := neg_abs_le (w - 2).re
    rw [h3] at h4 h5
    linarith
  have h2 : κ / 2 ≤ ‖w + 2‖ := by
    have h3 : (w + 2).re = w.re + 2 := by simp
    have h4 := Complex.re_le_norm (w + 2)
    rw [h3] at h4
    linarith
  have hsq : freeS 1 w ^ 2 = (w - 2) * (w + 2) := by
    rw [freeS_sq]; push_cast; ring
  have hn : ‖freeS 1 w‖ ^ 2 = ‖w - 2‖ * ‖w + 2‖ := by
    rw [← norm_pow, hsq, norm_mul]
  have : (κ / 2) ^ 2 ≤ ‖freeS 1 w‖ ^ 2 := by
    rw [hn, sq]
    exact mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp this

/-- `1 - |ρ(w)| ≥ min{c,1}/(4g²)` when `Im w ≥ c/g²`, `g ≥ 1`. -/
private lemma fi_one_sub_r {c g : ℝ} (hc : 0 < c) (hg : 1 ≤ g) {w : ℂ} (hw : c / g ^ 2 ≤ w.im) :
    min c 1 / (4 * g ^ 2) ≤ 1 - ‖freeRho 1 w‖ := by
  have hg2 : 1 ≤ g ^ 2 := one_le_pow₀ hg
  have hgp : 0 < g ^ 2 := by linarith
  have hw0 : 0 < w.im := lt_of_lt_of_le (by positivity) hw
  obtain ⟨hρ0, hw_eq⟩ := freeRho_aux 1 one_pos w hw0
  have hr1 : ‖freeRho 1 w‖ < 1 := norm_freeRho_lt_one 1 w hw0
  set ρ := freeRho 1 w with hρ
  have hr0 : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ0
  set r := ‖ρ‖ with hr
  set N := r ^ 2 with hN
  have hNpos : 0 < N := by positivity
  have hnormSq : Complex.normSq ρ = N := by rw [hN, hr, Complex.sq_norm]
  have him : w.im = ρ.im - ρ.im / N := by
    rw [hw_eq, Complex.ofReal_one, one_mul, Complex.add_im, Complex.inv_im, hnormSq]; ring
  have hNxy : N = ρ.re ^ 2 + ρ.im ^ 2 := by
    rw [hN, hr, Complex.sq_norm, Complex.normSq_apply]; ring
  have hy : |ρ.im| ≤ r := by
    rw [hr]; exact Complex.abs_im_le_norm ρ
  have hN1 : N < 1 := by nlinarith
  -- `N · Im w = ρ.im (N - 1) ≤ r (1 - N)`
  have h1 : N * w.im = ρ.im * (N - 1) := by rw [him]; field_simp
  have h2 : N * w.im ≤ r * (1 - N) := by
    rw [h1]
    have : ρ.im * (N - 1) ≤ |ρ.im| * (1 - N) := by
      rw [show ρ.im * (N - 1) = -ρ.im * (1 - N) by ring]
      exact mul_le_mul_of_nonneg_right (neg_le_abs _) (by linarith)
    exact this.trans (mul_le_mul_of_nonneg_right hy (by linarith))
  have h3 : r * w.im ≤ 1 - N := by
    have : r * (r * w.im) ≤ r * (1 - N) := by rw [hN] at h2; nlinarith
    exact le_of_mul_le_mul_left this hr0
  have hcw : c / g ^ 2 ≤ w.im := hw
  have hc' : min c 1 / g ^ 2 ≤ w.im :=
    le_trans (div_le_div_of_nonneg_right (min_le_left _ _) hgp.le) hcw
  have hmin1 : min c 1 ≤ 1 := min_le_right _ _
  have hmin0 : 0 < min c 1 := lt_min hc one_pos
  by_cases hrh : 1 / 2 ≤ r
  · have h4 : r * (min c 1 / g ^ 2) ≤ 1 - N := le_trans (mul_le_mul_of_nonneg_left hc' hr0.le) h3
    have h5 : 1 - N ≤ 2 * (1 - r) := by rw [hN]; nlinarith
    have h6 : (1 / 2) * (min c 1 / g ^ 2) ≤ r * (min c 1 / g ^ 2) :=
      mul_le_mul_of_nonneg_right hrh (by positivity)
    have : min c 1 / (4 * g ^ 2) = (1 / 4) * (min c 1 / g ^ 2) := by field_simp
    rw [this]
    nlinarith
  · rw [not_le] at hrh
    have : min c 1 / (4 * g ^ 2) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith

/-- `r^L ≤ e^{-c'}` when `1 - r ≥ c'/(4g²)` and `L ≥ 4g²`. -/
private lemma fi_pow_le {r c' g : ℝ} {L : ℕ} (hr0 : 0 < r) (hr1 : r < 1) (hg : 1 ≤ g)
    (hL : 4 * g ^ 2 ≤ L) (h : c' / (4 * g ^ 2) ≤ 1 - r) :
    r ^ L ≤ Real.exp (-c') := by
  have hg2 : 1 ≤ g ^ 2 := one_le_pow₀ hg
  have hr : r ≤ Real.exp (-(1 - r)) := by linarith [Real.add_one_le_exp (-(1 - r))]
  have h1 : r ^ L ≤ Real.exp (-(1 - r)) ^ L := pow_le_pow_left₀ hr0.le hr L
  rw [← Real.exp_nat_mul] at h1
  refine h1.trans (Real.exp_le_exp.mpr ?_)
  have h2 : c' ≤ (4 * g ^ 2) * (1 - r) := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * g ^ 2)).mp h
    linarith
  have h3 : (4 * g ^ 2) * (1 - r) ≤ L * (1 - r) :=
    mul_le_mul_of_nonneg_right hL (by linarith)
  nlinarith

/-- Entry bound for row `0` of `(A_L - w)⁻¹`. -/
private lemma fi_row0_norm {n : ℕ} (hn : 2 ≤ n) {w : ℂ} (hw : 0 < w.im) (x : Fin (n + 1))
    {κ σ₁ : ℝ} (hκ : 0 < κ) (hs : κ / 2 ≤ ‖freeS 1 w‖) (hσ : 0 < σ₁)
    (hσ' : σ₁ ≤ 1 - ‖freeRho 1 w‖ ^ (n + 1)) :
    ‖((cycleAdj (n + 1) - w • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹) 0 x‖ ≤
      (2 / κ) * (‖freeRho 1 w‖ ^ (x : ℕ) + ‖freeRho 1 w‖ ^ (n + 1 - (x : ℕ))) / σ₁ := by
  have h := freeRowCycle_eq 1 w hw (n + 1) (by omega) x
  simp only [Complex.ofReal_one, one_smul] at h
  have h0 : ((cycleAdj (n + 1) - w • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹) 0 x =
      freeT 1 w * (freeRho 1 w ^ (x : ℕ) + freeRho 1 w ^ (n + 1 - (x : ℕ))) /
        (1 - freeRho 1 w ^ (n + 1)) := h
  rw [h0, norm_div, norm_mul]
  have hfT : ‖freeT 1 w‖ ≤ 2 / κ := by
    rw [freeT_eq 1 w hw, norm_neg, norm_inv]
    rw [show 2 / κ = (κ / 2)⁻¹ by field_simp]
    exact inv_anti₀ (by positivity) hs
  have hnum : ‖freeRho 1 w ^ (x : ℕ) + freeRho 1 w ^ (n + 1 - (x : ℕ))‖ ≤
      ‖freeRho 1 w‖ ^ (x : ℕ) + ‖freeRho 1 w‖ ^ (n + 1 - (x : ℕ)) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_pow, norm_pow]
  have hden : σ₁ ≤ ‖1 - freeRho 1 w ^ (n + 1)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (freeRho 1 w ^ (n + 1))
    rw [norm_one, norm_pow] at this
    linarith
  have hnn : 0 ≤ (2 / κ) * (‖freeRho 1 w‖ ^ (x : ℕ) + ‖freeRho 1 w‖ ^ (n + 1 - (x : ℕ))) := by
    positivity
  refine div_le_div₀ hnn ?_ hσ hden
  exact mul_le_mul hfT hnum (norm_nonneg _) (by positivity)

private lemma fi_sum_geom {r : ℝ} (h0 : 0 < r) (h1 : r < 1) (L : ℕ) :
    ∑ x : Fin L, (r ^ (x : ℕ) + r ^ (L - (x : ℕ))) ≤ 2 / (1 - r) := by
  rw [Finset.sum_add_distrib, Fin.sum_univ_eq_sum_range (fun i => r ^ i) L,
    Fin.sum_univ_eq_sum_range (fun i => r ^ (L - i)) L]
  have e : ∑ i ∈ Finset.range L, r ^ (L - i) = ∑ i ∈ Finset.range L, r ^ (i + 1) := by
    rw [← Finset.sum_range_reflect (fun j => r ^ (j + 1)) L]
    refine Finset.sum_congr rfl fun i hi => ?_
    have := Finset.mem_range.mp hi
    congr 1; omega
  rw [e]
  have g1 : ∑ i ∈ Finset.range L, r ^ i ≤ (1 - r)⁻¹ := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := L) h0.le h1
    rw [← Finset.range_eq_Ico] at this
    simpa [div_eq_mul_inv] using this
  have e2 : ∑ i ∈ Finset.range L, r ^ (i + 1) = r * ∑ i ∈ Finset.range L, r ^ i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e2]
  have h3 : r * ∑ i ∈ Finset.range L, r ^ i ≤ (1 - r)⁻¹ := by
    calc r * ∑ i ∈ Finset.range L, r ^ i ≤ 1 * (1 - r)⁻¹ :=
          mul_le_mul h1.le g1 (Finset.sum_nonneg fun i _ => by positivity) zero_le_one
      _ = (1 - r)⁻¹ := one_mul _
  rw [div_eq_mul_inv, two_mul]
  linarith

/-- `A_L - w` is invertible for `Im w > 0`. -/
private lemma fi_mul_inv {n : ℕ} (hn : 2 ≤ n) {w : ℂ} (hw : 0 < w.im) :
    (cycleAdj (n + 1) - w • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) *
      (cycleAdj (n + 1) - w • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ = 1 := by
  set A' := cycleAdj (n + 1) - w • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) with hA'
  refine Matrix.mul_nonsing_inv A' ?_
  by_contra hnu
  have h0 := Matrix.nonsing_inv_apply_not_isUnit A' hnu
  have h := freeRowCycle_eq 1 w hw (n + 1) (by omega) 0
  simp only [Complex.ofReal_one, one_smul] at h
  have h' : (A'⁻¹) 0 0 = freeT 1 w * (freeRho 1 w ^ ((0 : Fin (n + 1)) : ℕ) +
      freeRho 1 w ^ (n + 1 - ((0 : Fin (n + 1)) : ℕ))) / (1 - freeRho 1 w ^ (n + 1)) := h
  rw [h0] at h'
  have hr1 : ‖freeRho 1 w‖ < 1 := norm_freeRho_lt_one 1 w hw
  have hz : ‖freeRho 1 w ^ (n + 1)‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hr1 (by omega)
  have hne1 : 1 - freeRho 1 w ^ (n + 1) ≠ 0 := by
    intro h2
    have : freeRho 1 w ^ (n + 1) = 1 := by linear_combination -h2
    rw [this, norm_one] at hz
    exact lt_irrefl _ hz
  have hne2 : 1 + freeRho 1 w ^ (n + 1) ≠ 0 := by
    intro h2
    have : freeRho 1 w ^ (n + 1) = -1 := by linear_combination h2
    rw [this, norm_neg, norm_one] at hz
    exact lt_irrefl _ hz
  have hs0 : freeS 1 w ≠ 0 := by
    intro h2
    have := freeS_im_pos 1 w hw
    rw [h2] at this
    simp at this
  have hf : freeT 1 w ≠ 0 := by
    rw [freeT_eq 1 w hw]; exact neg_ne_zero.mpr (inv_ne_zero hs0)
  simp only [Fin.val_zero, pow_zero, Nat.sub_zero] at h'
  rw [Matrix.zero_apply] at h'
  have := div_eq_zero_iff.mp h'.symm
  rcases this with h3 | h3
  · rcases mul_eq_zero.mp h3 with h4 | h4
    · exact hf h4
    · exact hne2 h4
  · exact hne1 h3

/-- Entry and row-sum bounds (6.15) [uvc:eq:free-row-bounds] for `(A_L - w)⁻¹`. -/
private lemma fi_entries {κ c g E : ℝ} (hκ : 0 < κ) (hc : 0 < c) (hg1 : 1 ≤ g) {n : ℕ}
    (hn : 2 ≤ n) (hL : 4 * g ^ 2 ≤ ((n + 1 : ℕ) : ℝ)) (hE : |E| ≤ 2 - κ) {w : ℂ}
    (hw : c / g ^ 2 ≤ w.im) (hwκ : ‖w - E‖ ≤ κ / 2) :
    (∀ a b : Fin (n + 1),
      ‖((cycleAdj (n + 1) - w • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹) a b‖ ≤
        4 / (κ * (1 - Real.exp (-min c 1)))) ∧
    (∀ a : Fin (n + 1), (g ^ 2)⁻¹ * ∑ b : Fin (n + 1),
      ‖((cycleAdj (n + 1) - w • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹) a b‖ ≤
        16 / (κ * (1 - Real.exp (-min c 1)) * min c 1)) := by
  set c' : ℝ := min c 1 with hc'
  have hc'0 : 0 < c' := lt_min hc one_pos
  set σ₁ : ℝ := 1 - Real.exp (-c') with hσ₁
  have hσ₁0 : 0 < σ₁ := by
    have := Real.exp_lt_one_iff.mpr (by linarith : -c' < 0)
    linarith
  have hgsq : 1 ≤ g ^ 2 := one_le_pow₀ hg1
  have hgp : 0 < g ^ 2 := by linarith
  have hw0 : 0 < w.im := lt_of_lt_of_le (by positivity) hw
  have hs : κ / 2 ≤ ‖freeS 1 w‖ := fi_s_lower hκ hE hwκ
  have hr : c' / (4 * g ^ 2) ≤ 1 - ‖freeRho 1 w‖ := fi_one_sub_r hc hg1 hw
  have hρ1 : ‖freeRho 1 w‖ < 1 := norm_freeRho_lt_one 1 w hw0
  have hρ0 : 0 < ‖freeRho 1 w‖ := norm_pos_iff.mpr (freeRho_aux 1 one_pos w hw0).1
  have hpow : ‖freeRho 1 w‖ ^ (n + 1) ≤ Real.exp (-c') := fi_pow_le hρ0 hρ1 hg1 hL hr
  have hσ' : σ₁ ≤ 1 - ‖freeRho 1 w‖ ^ (n + 1) := by rw [hσ₁]; linarith
  set M := (cycleAdj (n + 1) - w • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ with hM
  have htr : ∀ a b : Fin (n + 1), M a b = M 0 (b - a) := by
    intro a b
    have := inv_add_invariant w (-a) a b
    rw [add_neg_cancel, ← sub_eq_add_neg] at this
    exact this.symm
  have hrow0 : ∀ x : Fin (n + 1), ‖M 0 x‖ ≤
      (2 / κ) * (‖freeRho 1 w‖ ^ (x : ℕ) + ‖freeRho 1 w‖ ^ (n + 1 - (x : ℕ))) / σ₁ :=
    fun x => fi_row0_norm hn hw0 x hκ hs hσ₁0 hσ'
  have hr1 : ∀ m : ℕ, ‖freeRho 1 w‖ ^ m ≤ 1 := fun m => pow_le_one₀ hρ0.le hρ1.le
  refine ⟨?_, ?_⟩
  · intro a b
    rw [htr a b]
    refine (hrow0 (b - a)).trans ?_
    have h1 := hr1 (b - a : Fin (n + 1)).val
    have h2 := hr1 (n + 1 - (b - a : Fin (n + 1)).val)
    have : (2 / κ) * (‖freeRho 1 w‖ ^ (b - a : Fin (n + 1)).val +
        ‖freeRho 1 w‖ ^ (n + 1 - (b - a : Fin (n + 1)).val)) / σ₁ ≤ (2 / κ) * (1 + 1) / σ₁ :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity))
        hσ₁0.le
    refine this.trans (le_of_eq ?_)
    field_simp
    ring
  · intro a
    have hsum : ∑ b, ‖M a b‖ = ∑ x, ‖M 0 x‖ := by
      simp_rw [htr a]
      exact Equiv.sum_comp (Equiv.subRight a) (fun x => ‖M 0 x‖)
    have h1 : ∑ x : Fin (n + 1), ‖M 0 x‖ ≤ (2 / (κ * σ₁)) * (2 / (1 - ‖freeRho 1 w‖)) := by
      calc ∑ x : Fin (n + 1), ‖M 0 x‖
          ≤ ∑ x : Fin (n + 1), (2 / κ) *
              (‖freeRho 1 w‖ ^ (x : ℕ) + ‖freeRho 1 w‖ ^ (n + 1 - (x : ℕ))) / σ₁ :=
            Finset.sum_le_sum fun x _ => hrow0 x
        _ = (2 / (κ * σ₁)) * ∑ x : Fin (n + 1),
              (‖freeRho 1 w‖ ^ (x : ℕ) + ‖freeRho 1 w‖ ^ (n + 1 - (x : ℕ))) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => ?_
            field_simp
        _ ≤ (2 / (κ * σ₁)) * (2 / (1 - ‖freeRho 1 w‖)) :=
            mul_le_mul_of_nonneg_left (fi_sum_geom hρ0 hρ1 (n + 1)) (by positivity)
    have h2 : 2 / (1 - ‖freeRho 1 w‖) ≤ 8 * g ^ 2 / c' := by
      rw [div_le_div_iff₀ (by linarith) hc'0]
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * g ^ 2)).mp hr
      nlinarith
    have h3 : ∑ b, ‖M a b‖ ≤ (16 / (κ * σ₁ * c')) * g ^ 2 := by
      rw [hsum]
      refine h1.trans ?_
      calc (2 / (κ * σ₁)) * (2 / (1 - ‖freeRho 1 w‖)) ≤ (2 / (κ * σ₁)) * (8 * g ^ 2 / c') :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (16 / (κ * σ₁ * c')) * g ^ 2 := by field_simp; ring
    calc (g ^ 2)⁻¹ * ∑ b, ‖M a b‖ ≤ (g ^ 2)⁻¹ * ((16 / (κ * σ₁ * c')) * g ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 16 / (κ * σ₁ * c') := by field_simp

/-- The interpolation identity (6.17) [da:eq:dyson-interpolation] with the error bound, for a
right inverse `M` of `A_L - w` with bounded entries. -/
private lemma fi_interp {κ C g E : ℝ} {n : ℕ} {w : ℂ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hκ : 0 < κ) (hκ2 : κ < 2) (hC : 0 < C) (hgp : 0 < g ^ 2) (hE : |E| ≤ 2 - κ)
    (hwE : ‖w - E‖ ≤ C / g ^ 2) (hL : 4 * g ^ 2 ≤ ((n + 1 : ℕ) : ℝ))
    (hmul : (cycleAdj (n + 1) - w • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) * M = 1)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (hent : ∀ a b, ‖M a b‖ ≤ C₀) :
    ∀ (b₀ : Fin (n + 1)) (n' : ℕ), (n' : ℝ) ≤ 1 * g ^ 2 → ∀ j : ℕ, j < n' → ∀ b : Fin (n + 1),
      ‖M ((finRotate (n + 1) ^ j) b₀) b -
        (((Real.sin (((j : ℝ) + 1) * Real.arccos (E / 2)) /
            Real.sin (Real.arccos (E / 2)) : ℝ) : ℂ) * M b₀ b -
          ((Real.sin ((j : ℝ) * Real.arccos (E / 2)) /
            Real.sin (Real.arccos (E / 2)) : ℝ) : ℂ) * M ((finRotate (n + 1)).symm b₀) b +
          ((if (b.val + (n + 1) - b₀.val) % (n + 1) < j then
            Real.sin (((j : ℝ) - (((b.val + (n + 1) - b₀.val) % (n + 1) : ℕ) : ℝ)) *
              Real.arccos (E / 2)) / Real.sin (Real.arccos (E / 2)) else 0 : ℝ) : ℂ))‖ ≤
        (2 * C * C₀ / κ) * n' / g ^ 2 := by
  intro b₀ n' hn' j hj b
  have hjn : (j : ℝ) < n' := by exact_mod_cast hj
  have hn'g : (n' : ℝ) ≤ g ^ 2 := by simpa using hn'
  have hjL : j < n + 1 := by
    have h1 : (j : ℝ) < n + 1 := by
      have : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [this] at hL
      nlinarith
    exact_mod_cast h1
  have hE' := abs_le.mp hE
  have hcos : Real.cos (Real.arccos (E / 2)) = E / 2 :=
    Real.cos_arccos (by linarith) (by linarith)
  have hsin : κ / 2 ≤ Real.sin (Real.arccos (E / 2)) := by
    rw [Real.sin_arccos]
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hs0 : Real.sin (Real.arccos (E / 2)) ≠ 0 := (lt_of_lt_of_le (by positivity) hsin).ne'
  have key := fi_cell w M hmul (Real.arccos (E / 2)) hs0 b₀ b j hjL
  set ϑ := Real.arccos (E / 2) with hϑ
  have hε : ‖w - ((2 * Real.cos ϑ : ℝ) : ℂ)‖ ≤ C / g ^ 2 := by
    rw [hcos, show 2 * (E / 2) = E by ring]
    exact hwE
  have hV : ∀ t : ℝ, ‖((Real.sin (t * ϑ) / Real.sin ϑ : ℝ) : ℂ)‖ ≤ 2 / κ := by
    intro t
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos (lt_of_lt_of_le (by positivity) hsin)]
    rw [div_le_div_iff₀ (lt_of_lt_of_le (by positivity) hsin) hκ]
    have := Real.abs_sin_le_one (t * ϑ)
    nlinarith
  have hsum : ‖∑ i ∈ Finset.range j, ((Real.sin (((j : ℝ) - i) * ϑ) / Real.sin ϑ : ℝ) : ℂ) *
      M ((finRotate (n + 1) ^ i) b₀) b‖ ≤ j * (2 / κ * C₀) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ Finset.range j, ‖((Real.sin (((j : ℝ) - i) * ϑ) / Real.sin ϑ : ℝ) : ℂ) *
          M ((finRotate (n + 1) ^ i) b₀) b‖
        ≤ ∑ i ∈ Finset.range j, (2 / κ * C₀) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul]
          exact mul_le_mul (hV _) (hent _ _) (norm_nonneg _) (by positivity)
      _ = j * (2 / κ * C₀) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have heq : M ((finRotate (n + 1) ^ j) b₀) b -
      (((Real.sin (((j : ℝ) + 1) * ϑ) / Real.sin ϑ : ℝ) : ℂ) * M b₀ b -
        ((Real.sin ((j : ℝ) * ϑ) / Real.sin ϑ : ℝ) : ℂ) * M ((finRotate (n + 1)).symm b₀) b +
        ((if (b.val + (n + 1) - b₀.val) % (n + 1) < j then
          Real.sin (((j : ℝ) - (((b.val + (n + 1) - b₀.val) % (n + 1) : ℕ) : ℝ)) * ϑ) /
            Real.sin ϑ else 0 : ℝ) : ℂ)) =
      (w - ((2 * Real.cos ϑ : ℝ) : ℂ)) *
        ∑ i ∈ Finset.range j, ((Real.sin (((j : ℝ) - i) * ϑ) / Real.sin ϑ : ℝ) : ℂ) *
          M ((finRotate (n + 1) ^ i) b₀) b := by
    rw [key]; ring
  rw [heq, norm_mul]
  calc ‖w - ((2 * Real.cos ϑ : ℝ) : ℂ)‖ *
        ‖∑ i ∈ Finset.range j, ((Real.sin (((j : ℝ) - i) * ϑ) / Real.sin ϑ : ℝ) : ℂ) *
          M ((finRotate (n + 1) ^ i) b₀) b‖
      ≤ (C / g ^ 2) * (n' * (2 / κ * C₀)) := by
        apply mul_le_mul hε _ (norm_nonneg _) (by positivity)
        exact hsum.trans (mul_le_mul_of_nonneg_right hjn.le (by positivity))
    _ = (2 * C * C₀ / κ) * n' / g ^ 2 := by field_simp

/-- Lemma 6.5 [da:lem:free-interpolation]: (6.15) [uvc:eq:free-row-bounds] and (6.17)
[da:eq:dyson-interpolation] with the coefficients (6.16)
[da:eq:cell-interpolation-coefficients], for every `w` with `Im w ≥ c/g²` and `|w - E| ≤ C/g²`.
The interval starts at `b₀`; `a = b₀ + j`, and `k` is the offset of `b` in `[b₀, b₀ + L)`. -/
theorem free_interpolation (κ C c : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hC : 0 < C) (hc : 0 < c) :
    ∃ Cκ C' c₀ : ℝ, 1 ≤ Cκ ∧ 0 < C' ∧ 0 < c₀ ∧ ∀ g : ℝ, Cκ ≤ g → ∀ L : ℕ, 4 * g ^ 2 ≤ L →
      ∀ E : ℝ, |E| ≤ 2 - κ → ∀ w : ℂ, c / g ^ 2 ≤ w.im → ‖w - E‖ ≤ C / g ^ 2 →
      let M := (cycleAdj L - w • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹
      let ϑ := Real.arccos (E / 2)
      (∀ a b, ‖M a b‖ ≤ C') ∧ (∀ a, (g ^ 2)⁻¹ * ∑ b, ‖M a b‖ ≤ C') ∧
      ∀ (b₀ : Fin L) (n : ℕ), (n : ℝ) ≤ c₀ * g ^ 2 → ∀ j : ℕ, j < n → ∀ b : Fin L,
        let a := (finRotate L ^ j) b₀
        let k := (b.val + L - b₀.val) % L
        ‖M a b - ((Real.sin ((j + 1) * ϑ) / Real.sin ϑ : ℝ) * M b₀ b -
            (Real.sin (j * ϑ) / Real.sin ϑ : ℝ) * M ((finRotate L).symm b₀) b +
            (if k < j then (Real.sin (((j : ℝ) - k) * ϑ) / Real.sin ϑ : ℝ) else 0))‖ ≤
          C' * n / g ^ 2 := by
  set c' : ℝ := min c 1 with hc'
  have hc'0 : 0 < c' := lt_min hc one_pos
  set σ₁ : ℝ := 1 - Real.exp (-c') with hσ₁
  have hσ₁0 : 0 < σ₁ := by
    have := Real.exp_lt_one_iff.mpr (by linarith : -c' < 0)
    linarith
  set C₀ : ℝ := 4 / (κ * σ₁) with hC₀
  set R₁ : ℝ := 16 / (κ * σ₁ * c') with hR₁
  set C₂ : ℝ := 2 * C * C₀ / κ with hC₂
  have hC₀p : 0 < C₀ := by positivity
  have hR₁p : 0 < R₁ := by positivity
  have hC₂p : 0 < C₂ := by positivity
  refine ⟨max 1 (2 * C / κ), max C₀ (max R₁ C₂), 1, le_max_left _ _,
    lt_max_of_lt_left hC₀p, one_pos, ?_⟩
  intro g hg L hL E hE w hw hwE
  have hg1 : 1 ≤ g := le_trans (le_max_left _ _) hg
  have hg2 : 2 * C / κ ≤ g := le_trans (le_max_right _ _) hg
  have hgsq : 1 ≤ g ^ 2 := one_le_pow₀ hg1
  have hgp : 0 < g ^ 2 := by linarith
  have hCg : C / g ^ 2 ≤ κ / 2 := by
    rw [div_le_iff₀ hgp]
    have h1 : C ≤ κ / 2 * g := by
      have := (div_le_iff₀ hκ).mp hg2
      linarith
    nlinarith
  have hL4 : (4 : ℝ) ≤ L := le_trans (by nlinarith) hL
  have hL4' : 4 ≤ L := by exact_mod_cast hL4
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  have hn : 2 ≤ n := by omega
  have hw0 : 0 < w.im := lt_of_lt_of_le (by positivity) hw
  have hmul := fi_mul_inv hn hw0
  obtain ⟨he1, he2⟩ := fi_entries hκ hc hg1 hn hL hE hw (hwE.trans hCg)
  have hint := fi_interp _ hκ hκ2 hC hgp hE hwE hL hmul hC₀p.le he1
  intro M ϑ
  refine ⟨fun a b => (he1 a b).trans (le_max_left _ _),
    fun a => (he2 a).trans ((le_max_left _ _).trans (le_max_right _ _)), ?_⟩
  intro b₀ n' hn' j hj b
  refine (hint b₀ n' hn' j hj b).trans ?_
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) (Nat.cast_nonneg _))
    hgp.le

end LSBA
