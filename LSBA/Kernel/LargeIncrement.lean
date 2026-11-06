import LSBA.Kernel.Large

/-!
# The increment bound of the mixed kernel at large coupling

(A.49) [da:eq:mixed-profile-increment] on the large-coupling range, from Lemma A.10
[uvp:lem:actual-kernels] and (A.44) [da:eq:kernel-accuracy].
-/

open MeasureTheory Real Filter Topology Complex
open scoped ENNReal

noncomputable section

open scoped Classical

namespace LSBA

private lemma li_val_finRotate {L : ℕ} (x : Fin L) :
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

/-- The `j`-th power of the cyclic shift moves the index by `j` modulo `L`. -/
private lemma li_pow_val {L : ℕ} (x : Fin L) (j : ℕ) :
    ((finRotate L ^ j) x).val = (x.val + j) % L := by
  induction j with
  | zero => simp [Nat.mod_eq_of_lt x.isLt]
  | succ j ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, li_val_finRotate, ih, Nat.mod_add_mod]
    rfl

/-- Moving from `x` to `y` takes `(y - x) mod L` steps of the cyclic shift. -/
private lemma li_pow_eq {L : ℕ} (x y : Fin L) :
    (finRotate L ^ ((y.val + L - x.val) % L)) x = y := by
  apply Fin.ext
  rw [li_pow_val, Nat.add_mod_mod]
  have hx := x.isLt
  have hy := y.isLt
  have : x.val + (y.val + L - x.val) = y.val + L := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hy]

/-- A function with increments at most `B` along the cyclic shift changes by at most `k * B` over
`k` steps. -/
private lemma li_telescope_pow {L : ℕ} (f : Fin L → ℝ) (B : ℝ)
    (hB : ∀ x, |f (finRotate L x) - f x| ≤ B) (x : Fin L) (k : ℕ) :
    |f ((finRotate L ^ k) x) - f x| ≤ k * B := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := hB ((finRotate L ^ k) x)
    have e : (finRotate L ^ (k + 1)) x = finRotate L ((finRotate L ^ k) x) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    rw [e]
    calc |f (finRotate L ((finRotate L ^ k) x)) - f x|
        = |(f (finRotate L ((finRotate L ^ k) x)) - f ((finRotate L ^ k) x)) +
            (f ((finRotate L ^ k) x) - f x)| := by ring_nf
      _ ≤ |f (finRotate L ((finRotate L ^ k) x)) - f ((finRotate L ^ k) x)| +
            |f ((finRotate L ^ k) x) - f x| := abs_add_le _ _
      _ ≤ B + k * B := add_le_add h1 ih
      _ = ((k + 1 : ℕ) : ℝ) * B := by push_cast; ring

/-- Telescoping along the shorter arc: `cycDist b b'` unit increments. -/
private lemma li_telescope {L : ℕ} (f : Fin L → ℝ) (B : ℝ)
    (hB : ∀ x, |f (finRotate L x) - f x| ≤ B) (b b' : Fin L) :
    |f b - f b'| ≤ (cycDist b b' : ℝ) * B := by
  unfold cycDist
  rcases le_total ((b.val + L - b'.val) % L) ((b'.val + L - b.val) % L) with h | h
  · rw [min_eq_left h]
    have := li_telescope_pow f B hB b' ((b.val + L - b'.val) % L)
    rw [li_pow_eq b' b] at this
    exact this
  · rw [min_eq_right h, abs_sub_comm]
    have := li_telescope_pow f B hB b ((b'.val + L - b.val) % L)
    rw [li_pow_eq b b'] at this
    exact this

private lemma li_log_ge_one {W : ℕ} (hW : 3 ≤ W) : 1 ≤ Real.log W := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : (3 : ℝ) ≤ W := by exact_mod_cast hW
  linarith

private lemma li_hopB_nonneg {g : ℝ} (hg : 0 ≤ g) : 0 ≤ hopB g :=
  div_nonneg hg (le_trans zero_le_one (le_max_left _ _))

private lemma li_gammaG_pos (g : ℝ) : 0 < gammaG g := by
  have : 0 < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  unfold gammaG
  positivity

set_option maxHeartbeats 1000000 in
-- the many explicit estimates of this proof exceed the default heartbeat limit
/-- (A.49) [da:eq:mixed-profile-increment] at large coupling, for `u ≥ 1/2`, `1 - u ≥ W^{-3}` and
`L ≥ C_A g² log W`, from Lemma A.10 [uvp:lem:actual-kernels] and (A.44) [da:eq:kernel-accuracy];
`C'` does not depend on `A`. -/
theorem increment_large (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ Cκ C' : ℝ, 1 ≤ Cκ ∧ 0 < C' ∧ ∀ A : ℝ, 0 < A → ∃ CA : ℝ, ∃ W₀ : ℕ, 0 < CA ∧
      ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, Cκ ≤ g → ∀ L : ℕ, CA * g ^ 2 * Real.log W ≤ L →
      ∀ E : ℝ, |E| ≤ 2 - κ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m →
      ∀ u : ℝ, 1 / 2 ≤ u → (W : ℝ) ^ (-3 : ℝ) ≤ 1 - u → ∀ a b b' : Fin L,
        |mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) u a b -
            mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) u a b'| ≤
          C' / ((1 - u) * ellProp g L u) * ((cycDist b b' : ℝ) / ellProp g L u) +
            (ellProp g L u)⁻¹ * (W : ℝ) ^ (-A) := by
  obtain ⟨Cκp, Rp, cp, Cp, hCκp, hRp, hcp, hCp, hp⟩ := large_periodic_comparison κ hκ hκ2
  obtain ⟨Cκa, Ra, c, C, hCκa, hRa, hc, hC, ha⟩ := large_actual_kernels κ hκ hκ2
  refine ⟨max Cκp Cκa, 8 * C, le_trans hCκp (le_max_left _ _), by positivity, fun A hA => ?_⟩
  obtain ⟨CrQ, W₁, hCrQ, hka⟩ := kernel_accuracy C c 3 (A + 1) hC hc (by norm_num) (by linarith)
  refine ⟨max (4 * Ra) (max Rp (max CrQ 3)), max W₁ (max 3 ⌈16 * C⌉₊),
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 4 * Ra) (le_max_left _ _),
    fun W hW g hg L hL E hE m hm u hu hWu a b b' => ?_⟩
  set CA : ℝ := max (4 * Ra) (max Rp (max CrQ 3)) with hCA
  have hCA1 : 4 * Ra ≤ CA := le_max_left _ _
  have hCA2 : Rp ≤ CA := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCA3 : CrQ ≤ CA :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hCA4 : (3 : ℝ) ≤ CA :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hWW₁ : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hW3 : 3 ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hWC : ⌈16 * C⌉₊ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  have hW16 : 16 * C ≤ W := le_trans (Nat.le_ceil _) (by exact_mod_cast hWC)
  have hW3r : (3 : ℝ) ≤ W := by exact_mod_cast hW3
  have hW0 : (0 : ℝ) < W := by linarith
  have hlogW : 1 ≤ Real.log W := li_log_ge_one hW3
  have hgp : Cκp ≤ g := le_trans (le_max_left _ _) hg
  have hga : Cκa ≤ g := le_trans (le_max_right _ _) hg
  have hg1 : 1 ≤ g := le_trans hCκp hgp
  have hg0 : 0 < g := by linarith
  have hg2 : 0 < g ^ 2 := by positivity
  have hγ : 0 < gammaG g := li_gammaG_pos g
  -- the range of `L`
  have hLg : CA * g ^ 2 ≤ L := by
    have h1 : CA * g ^ 2 * 1 ≤ CA * g ^ 2 * Real.log W := by
      have : 0 ≤ CA * g ^ 2 := by positivity
      gcongr
    linarith
  have hL3 : 3 ≤ L := by
    have h1 : (3 : ℝ) ≤ CA * g ^ 2 := by nlinarith
    have : (3 : ℝ) ≤ L := by linarith
    exact_mod_cast this
  have hLp : Rp * g ^ 2 ≤ L := by
    have : Rp * g ^ 2 ≤ CA * g ^ 2 := by gcongr
    linarith
  have : NeZero L := ⟨by omega⟩
  -- `δ = 1 - u`
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 1 - u := ⟨_, rfl⟩
  have hu_eq : 1 - δ = u := by linarith
  have hδW : (W : ℝ) ^ (-3 : ℝ) ≤ δ := by rw [hδdef]; exact hWu
  have hδ0 : 0 < δ := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) hδW
  have hδ1 : δ ≤ 1 := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hu1 : u < 1 := by linarith
  have hlogδ : |Real.log δ| ≤ 3 * Real.log W := by
    rw [abs_of_nonpos (Real.log_nonpos hδ0.le hδ1)]
    have h1 : Real.log ((W : ℝ) ^ (-3 : ℝ)) ≤ Real.log δ :=
      Real.log_le_log (Real.rpow_pos_of_pos hW0 _) hδW
    rw [Real.log_rpow hW0] at h1
    linarith
  have hRlog : Ra * (1 + |Real.log δ|) ≤ L / g ^ 2 := by
    rw [le_div_iff₀ hg2]
    have hlogW0 : 0 ≤ Real.log W := by linarith
    calc Ra * (1 + |Real.log δ|) * g ^ 2 ≤ Ra * (1 + 3 * Real.log W) * g ^ 2 := by gcongr
      _ ≤ 4 * Ra * Real.log W * g ^ 2 := by
          have : Ra * (1 + 3 * Real.log W) ≤ 4 * Ra * Real.log W := by nlinarith
          gcongr
      _ ≤ CA * Real.log W * g ^ 2 := by gcongr
      _ = CA * g ^ 2 * Real.log W := by ring
      _ ≤ L := hL
  -- the solution is the one of Lemma A.4 [uvp:prop:finite]
  obtain ⟨m', mInf, hm', hmI, -⟩ := hp g hgp L hLp E hE
  obtain rfl : m = m' := isDysonRootV_unique (hopB g) (gammaG g) (li_hopB_nonneg hg0.le) hγ L hL3
    (E : ℂ) (by simp) m m' hm hm'
  obtain ⟨-, -, -, -, -, h6, -, -, h9, h10, -⟩ :=
    ha g hga L E hE m mInf hm hmI δ hδ0 hδ1 hRlog
  set P := pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) with hPdef
  set Ξ : Matrix (Fin L) (Fin L) ℝ :=
    (1 - δ) • mixedKer (Matrix.circulant (perP0 g L E mInf)) (1 - δ) with hΞ
  set Ee : Matrix (Fin L) (Fin L) ℝ := (1 - (1 - δ) • P)⁻¹ - 1 - Ξ with hEe
  set ℓ : ℝ := min (L : ℝ) (g ^ 2 / Real.sqrt δ) with hℓ
  set lam : ℝ := Real.sqrt δ / g ^ 2 with hlam
  set ε : ℝ := epsL C c g L with hε
  have h6' : ∀ a b, |Ξ a (finRotate L b) - Ξ a b| ≤ C * lam / (δ * ℓ) := h6
  have h9' : ∀ a b, |Ee a b| ≤ C * ε / (g ^ 2 * δ ^ 2) := h9
  obtain ⟨hℓu1, hℓu2⟩ := h10
  rw [hu_eq] at hℓu1 hℓu2
  set ℓu : ℝ := ellProp g L u with hℓu
  -- the scales
  have hsδ : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ0
  have hsδ1 : Real.sqrt δ ≤ 1 := Real.sqrt_le_one.mpr hδ1
  have hℓ0 : 0 < ℓ := lt_min (by have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
                                 exact this) (by positivity)
  have hℓu0 : 0 < ℓu := lt_of_lt_of_le hℓ0 hℓu1
  have hlamℓ : lam * ℓ ≤ 1 := by
    have h1 : ℓ ≤ g ^ 2 / Real.sqrt δ := min_le_right _ _
    calc lam * ℓ ≤ lam * (g ^ 2 / Real.sqrt δ) := by
          have : 0 ≤ lam := by positivity
          gcongr
      _ = 1 := by rw [hlam]; field_simp
  -- the identity `u * K = Ξ + 𝓔`
  have hPnn : ∀ a b, 0 ≤ P a b := fun a b => by
    simp only [hPdef, pairP, Matrix.of_apply]
    exact mul_nonneg hγ.le (sq_nonneg _)
  have hProw : ∀ a, ∑ b, P a b = 1 := fun a =>
    pairP_row_sum (hopB g) (gammaG g) hγ L (by omega) E m hm a
  have hinv : (1 - u • P)⁻¹ = 1 + u • mixedKer P u := by
    have h := (propPM_identities P hPnn hProw 0 u u le_rfl hu0 le_rfl hu1).1
    simpa [propPM] using h
  have hid : ∀ x, u * mixedKer P u a x = Ξ a x + Ee a x := by
    intro x
    have h1 := congrFun (congrFun hinv a) x
    simp only [hEe, hu_eq, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul] at h1 ⊢
    linarith
  have hu2 : u⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hu_inv : 0 < u⁻¹ := inv_pos.mpr (by linarith)
  have hK : mixedKer P u a b - mixedKer P u a b' =
      u⁻¹ * ((Ξ a b - Ξ a b') + (Ee a b - Ee a b')) := by
    have h1 := hid b
    have h2 := hid b'
    have hu0' : u ≠ 0 := by linarith
    field_simp
    linarith
  -- the main term
  have hmain : 2 * ((cycDist b b' : ℝ) * (C * lam / (δ * ℓ))) ≤
      8 * C / ((1 - u) * ℓu) * ((cycDist b b' : ℝ) / ℓu) := by
    have hd : (0 : ℝ) ≤ cycDist b b' := Nat.cast_nonneg _
    have h1 : C * lam / (δ * ℓ) ≤ 4 * C / (δ * ℓu ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h2 : ℓu ^ 2 ≤ 4 * ℓ ^ 2 := by
        have := pow_le_pow_left₀ hℓu0.le hℓu2 2
        linarith only [this]
      have h3 : C * lam * (δ * ℓu ^ 2) ≤ C * lam * (δ * (4 * ℓ ^ 2)) := by
        have : 0 ≤ C * lam := by positivity
        gcongr
      have h4 : C * lam * (δ * (4 * ℓ ^ 2)) = 4 * C * δ * ℓ * (lam * ℓ) := by ring
      have h5 : 4 * C * δ * ℓ * (lam * ℓ) ≤ 4 * C * δ * ℓ * 1 := by
        have : 0 ≤ 4 * C * δ * ℓ := by positivity
        gcongr
      linarith
    have h7 : 8 * C / ((1 - u) * ℓu) * ((cycDist b b' : ℝ) / ℓu) =
        2 * ((cycDist b b' : ℝ) * (4 * C / (δ * ℓu ^ 2))) := by
      rw [← hδdef]; field_simp; ring
    rw [h7]
    gcongr
  -- the remainder
  have hrem : 4 * (C * ε / (g ^ 2 * δ ^ 2)) ≤ ℓu⁻¹ * (W : ℝ) ^ (-A) := by
    have hCrQL : CrQ * g ^ 2 * Real.log W ≤ L := by
      refine le_trans ?_ hL
      have : 0 ≤ g ^ 2 * Real.log W := by positivity
      nlinarith
    have hka' := hka W hWW₁ δ g hδW hg0 L hCrQL
    have hδ3 : δ ^ (-(3 : ℝ)) = (δ ^ 3)⁻¹ := by
      rw [Real.rpow_neg hδ0.le]; norm_num
    rw [hδ3] at hka'
    have hε3 : ε ≤ δ ^ 3 * (W : ℝ) ^ (-(A + 1)) := by
      have hd3 : 0 < δ ^ 3 := by positivity
      rw [inv_mul_le_iff₀ hd3] at hka'
      exact hka'
    have hWA : (W : ℝ) ^ (-(A + 1)) = (W : ℝ) ^ (-A) * (W : ℝ)⁻¹ := by
      rw [show -(A + 1) = -A + (-1) by ring, Real.rpow_add hW0, Real.rpow_neg_one]
    have hWApos : 0 < (W : ℝ) ^ (-A) := Real.rpow_pos_of_pos hW0 _
    have hCW : C * (W : ℝ)⁻¹ ≤ 1 / 16 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hW0]; linarith
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
    have hCε : C * ε ≤ C * (δ ^ 3 * ((W : ℝ) ^ (-A) * (W : ℝ)⁻¹)) := by
      rw [← hWA]; gcongr
    calc 4 * (C * ε / (g ^ 2 * δ ^ 2))
        ≤ 4 * (C * (δ ^ 3 * ((W : ℝ) ^ (-A) * (W : ℝ)⁻¹)) / (g ^ 2 * δ ^ 2)) := by gcongr
      _ = 4 * δ * (C * (W : ℝ)⁻¹) / g ^ 2 * (W : ℝ) ^ (-A) := by field_simp
      _ ≤ 4 * δ * (1 / 16) / g ^ 2 * (W : ℝ) ^ (-A) := by gcongr
      _ = δ / (4 * g ^ 2) * (W : ℝ) ^ (-A) := by field_simp; ring
      _ ≤ δ / (2 * g ^ 2) * (W : ℝ) ^ (-A) := by
          gcongr; norm_num
      _ ≤ ℓu⁻¹ * (W : ℝ) ^ (-A) := by gcongr
  -- assembly
  have hΞd : |Ξ a b - Ξ a b'| ≤ (cycDist b b' : ℝ) * (C * lam / (δ * ℓ)) :=
    li_telescope (fun x => Ξ a x) (C * lam / (δ * ℓ)) (fun x => h6' a x) b b'
  have hE1 : |Ee a b - Ee a b'| ≤ 2 * (C * ε / (g ^ 2 * δ ^ 2)) := by
    calc |Ee a b - Ee a b'| ≤ |Ee a b| + |Ee a b'| := abs_sub _ _
      _ ≤ C * ε / (g ^ 2 * δ ^ 2) + C * ε / (g ^ 2 * δ ^ 2) := add_le_add (h9' a b) (h9' a b')
      _ = 2 * (C * ε / (g ^ 2 * δ ^ 2)) := by ring
  rw [hK, abs_mul, abs_of_pos hu_inv]
  calc u⁻¹ * |(Ξ a b - Ξ a b') + (Ee a b - Ee a b')|
      ≤ 2 * (|Ξ a b - Ξ a b'| + |Ee a b - Ee a b'|) := by
        refine le_trans (mul_le_mul_of_nonneg_left (abs_add_le _ _) hu_inv.le) ?_
        gcongr
    _ ≤ 2 * ((cycDist b b' : ℝ) * (C * lam / (δ * ℓ)) + 2 * (C * ε / (g ^ 2 * δ ^ 2))) := by
        gcongr
    _ = 2 * ((cycDist b b' : ℝ) * (C * lam / (δ * ℓ))) + 4 * (C * ε / (g ^ 2 * δ ^ 2)) := by ring
    _ ≤ _ := add_le_add hmain hrem

end LSBA
