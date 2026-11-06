import LSBA.Upper.LargeCorrelator
import LSBA.Upper.Interface
import LSBA.Spectral.SimpleSpectrum

/-!
# Concentration from interval averaging

The deterministic steps of Appendix E.1 [app:fr-concentration-proof] after (E.3)
[uva:eq:cell-correlator] in the proof of Lemma 8.1 [uva:thm:upper-audit]: the cell-correlator bound
on `J = [−E₀, E₀]` gives (3.6) [eq:averaged-tail] on `J` at the block radius `R = K W g² log W`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Cyclic distance on `ℤ_L` -/

/-- `(x + K − y) mod K` for `x, y < K`. -/
private lemma largeAverageUpper_mod {K x y : ℕ} (hx : x < K) (hy : y < K) :
    (x + K - y) % K = if y ≤ x then x - y else x + K - y := by
  split_ifs with h
  · have : x + K - y = (x - y) + K := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

private lemma largeAverageUpper_cycDist_comm {L : ℕ} (a b : Fin L) :
    cycDist a b = cycDist b a := by
  unfold cycDist
  exact min_comm _ _

private lemma largeAverageUpper_cycDist_tri {L : ℕ} (a b c : Fin L) :
    cycDist a c ≤ cycDist a b + cycDist b c := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  simp only [cycDist, largeAverageUpper_mod ha hb, largeAverageUpper_mod hb ha,
    largeAverageUpper_mod ha hc, largeAverageUpper_mod hc ha, largeAverageUpper_mod hb hc,
    largeAverageUpper_mod hc hb]
  split_ifs <;> omega

private lemma largeAverageUpper_cycDist_lt {L : ℕ} (a b : Fin L) : cycDist a b < L :=
  (min_le_left _ _).trans_lt (Nat.mod_lt _ a.pos)

/-- The block `a + u` is at cyclic distance at most `u` from `a`. -/
private lemma largeAverageUpper_cycDist_cellBlock {L : ℕ} (a : Fin L) (u : ℕ) :
    cycDist a (cellBlock a u) ≤ u := by
  have hx : (cellBlock a u).val < L := (cellBlock a u).isLt
  have h1 : ((cellBlock a u).val + L - a.val + a.val) % L = (u + a.val) % L := by
    rw [Nat.sub_add_cancel (by omega), Nat.add_mod_right]
    simp only [cellBlock]
    rw [Nat.mod_mod, Nat.add_comm]
  have h2 : (cellBlock a u).val + L - a.val ≡ u [MOD L] := Nat.ModEq.add_right_cancel' _ h1
  calc cycDist a (cellBlock a u) ≤ ((cellBlock a u).val + L - a.val) % L := min_le_right _ _
    _ = u % L := h2
    _ ≤ u := Nat.mod_le _ _

/-- For `M n ≤ L` and `i, j < M`: `n ((i − j) mod M) ≤ (i n − j n) mod L`. -/
private lemma largeAverageUpper_mul_mod {L M n i j : ℕ} (hi : i < M) (hj : j < M)
    (hMn : M * n ≤ L) (hi' : i * n < L) (hj' : j * n < L) :
    n * ((i + M - j) % M) ≤ (i * n + L - j * n) % L := by
  rw [largeAverageUpper_mod hi hj, largeAverageUpper_mod hi' hj']
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hmono : j ≤ i ↔ j * n ≤ i * n :=
    ⟨fun h => Nat.mul_le_mul_right n h, fun h => Nat.le_of_mul_le_mul_right h hn⟩
  split_ifs with h1 h2 h2
  · rw [Nat.mul_sub, Nat.mul_comm n i, Nat.mul_comm n j]
  · exact absurd (hmono.mp h1) h2
  · exact absurd (hmono.mpr h2) h1
  · have e : n * (i + M - j) + n * j = n * i + n * M := by
      rw [← Nat.mul_add, ← Nat.mul_add, Nat.sub_add_cancel (by omega)]
    rw [Nat.mul_comm n j, Nat.mul_comm n i, Nat.mul_comm n M] at e
    omega

/-- The blocks `i n` and `j n` of `ℤ_L`, `i, j < M`, `M n ≤ L`, are at cyclic distance at least
`n ‖i − j‖_M`. -/
private lemma largeAverageUpper_cycDist_scale {L M n : ℕ} (hMn : M * n ≤ L) (i j : Fin M)
    (hi : i.val * n < L) (hj : j.val * n < L) :
    n * cycDist i j ≤ cycDist (⟨i.val * n, hi⟩ : Fin L) ⟨j.val * n, hj⟩ := by
  unfold cycDist
  exact le_min ((Nat.mul_le_mul_left n (min_le_left _ _)).trans
      (largeAverageUpper_mul_mod i.isLt j.isLt hMn hi hj))
    ((Nat.mul_le_mul_left n (min_le_right _ _)).trans
      (largeAverageUpper_mul_mod j.isLt i.isLt hMn hj hi))

/-! ### Geometric sums -/

/-- `Σ_y e^{−μ σ(y)} ≤ (1 − e^{−μ})⁻¹` for an injective `σ : Fin K → {0, …, K − 1}`. -/
private lemma largeAverageUpper_sum_inj {K : ℕ} (σ : Fin K → ℕ) (hσ : Function.Injective σ)
    (hσK : ∀ y, σ y < K) {μ : ℝ} (hμ : 0 < μ) :
    ∑ y, Real.exp (-μ * σ y) ≤ 1 / (1 - Real.exp (-μ)) := by
  have hr0 : 0 ≤ Real.exp (-μ) := (Real.exp_pos _).le
  have hr1 : Real.exp (-μ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  calc ∑ y, Real.exp (-μ * σ y) = ∑ t ∈ univ.image σ, Real.exp (-μ * t) :=
        (Finset.sum_image (f := fun t : ℕ => Real.exp (-μ * t)) fun x _ y _ h => hσ h).symm
    _ ≤ ∑ t ∈ Finset.range K, Real.exp (-μ * t) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => (Real.exp_pos _).le
        intro t ht
        obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp ht
        exact Finset.mem_range.mpr (hσK y)
    _ = ∑ t ∈ Finset.Ico 0 K, Real.exp (-μ) ^ t := by
        rw [Finset.range_eq_Ico]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← Real.exp_nat_mul, mul_comm]
    _ ≤ Real.exp (-μ) ^ 0 / (1 - Real.exp (-μ)) := geom_sum_Ico_le_of_lt_one hr0 hr1
    _ = 1 / (1 - Real.exp (-μ)) := by rw [pow_zero]

/-- `Σ_{y ∈ ℤ_K} e^{−μ ‖a − y‖_K} ≤ 2 (1 − e^{−μ})⁻¹`. -/
private lemma largeAverageUpper_sum_exp_cycDist {K : ℕ} (a : Fin K) {μ : ℝ} (hμ : 0 < μ) :
    ∑ y : Fin K, Real.exp (-μ * cycDist a y) ≤ 2 / (1 - Real.exp (-μ)) := by
  have hb : ∀ y : Fin K, Real.exp (-μ * cycDist a y) ≤
      Real.exp (-μ * ((a.val + K - y.val) % K : ℕ)) +
        Real.exp (-μ * ((y.val + K - a.val) % K : ℕ)) := by
    intro y
    unfold cycDist
    rcases min_choice ((a.val + K - y.val) % K) ((y.val + K - a.val) % K) with h | h <;> rw [h]
    · linarith [Real.exp_pos (-μ * ((y.val + K - a.val) % K : ℕ))]
    · linarith [Real.exp_pos (-μ * ((a.val + K - y.val) % K : ℕ))]
  have hi1 : Function.Injective fun y : Fin K => (a.val + K - y.val) % K := by
    intro y y' h
    simp only at h
    rw [largeAverageUpper_mod a.isLt y.isLt, largeAverageUpper_mod a.isLt y'.isLt] at h
    apply Fin.ext
    have := y.isLt
    have := y'.isLt
    split_ifs at h <;> omega
  have hi2 : Function.Injective fun y : Fin K => (y.val + K - a.val) % K := by
    intro y y' h
    simp only at h
    rw [largeAverageUpper_mod y.isLt a.isLt, largeAverageUpper_mod y'.isLt a.isLt] at h
    apply Fin.ext
    have := y.isLt
    have := y'.isLt
    split_ifs at h <;> omega
  have h1 := largeAverageUpper_sum_inj _ hi1 (fun y => Nat.mod_lt _ y.pos) hμ
  have h2 := largeAverageUpper_sum_inj _ hi2 (fun y => Nat.mod_lt _ y.pos) hμ
  calc ∑ y : Fin K, Real.exp (-μ * cycDist a y)
      ≤ ∑ y : Fin K, (Real.exp (-μ * ((a.val + K - y.val) % K : ℕ)) +
          Real.exp (-μ * ((y.val + K - a.val) % K : ℕ))) := Finset.sum_le_sum fun y _ => hb y
    _ = ∑ y : Fin K, Real.exp (-μ * ((a.val + K - y.val) % K : ℕ)) +
          ∑ y : Fin K, Real.exp (-μ * ((y.val + K - a.val) % K : ℕ)) := Finset.sum_add_distrib
    _ ≤ 1 / (1 - Real.exp (-μ)) + 1 / (1 - Real.exp (-μ)) := add_le_add h1 h2
    _ = 2 / (1 - Real.exp (-μ)) := by ring

/-- For the cells starting at the blocks `i n`, `i < M`, `M n ≤ L`:
`Σ_j e^{−μ ‖s_i − s_j‖_L} ≤ 2 (1 − e^{−μ n})⁻¹`. -/
private lemma largeAverageUpper_sum_cells {L M n : ℕ} (hMn : M * n ≤ L) (s : Fin M → Fin L)
    (hs : ∀ i, (s i).val = i.val * n) (i : Fin M) {μ : ℝ} (hμ : 0 < μ) (hn : 0 < n) :
    ∑ j, Real.exp (-μ * cycDist (s i) (s j)) ≤ 2 / (1 - Real.exp (-(μ * n))) := by
  calc ∑ j, Real.exp (-μ * cycDist (s i) (s j))
      ≤ ∑ j, Real.exp (-(μ * n) * cycDist i j) := by
        refine Finset.sum_le_sum fun j _ => Real.exp_le_exp.mpr ?_
        have hi : i.val * n < L := by rw [← hs i]; exact (s i).isLt
        have hj : j.val * n < L := by rw [← hs j]; exact (s j).isLt
        have hsi : s i = ⟨i.val * n, hi⟩ := Fin.ext (hs i)
        have hsj : s j = ⟨j.val * n, hj⟩ := Fin.ext (hs j)
        have h : ((n * cycDist i j : ℕ) : ℝ) ≤
            (cycDist (⟨i.val * n, hi⟩ : Fin L) ⟨j.val * n, hj⟩ : ℝ) := by
          exact_mod_cast largeAverageUpper_cycDist_scale hMn i j hi hj
        push_cast at h
        rw [hsi, hsj]
        nlinarith
    _ ≤ _ := largeAverageUpper_sum_exp_cycDist i (by positivity)

/-- `(1 − e^{−x})⁻¹ ≤ 1 + x⁻¹` for `x > 0`. -/
private lemma largeAverageUpper_inv_one_sub_exp {x : ℝ} (hx : 0 < x) :
    1 / (1 - Real.exp (-x)) ≤ 1 + 1 / x := by
  have ht0 : 0 < Real.exp (-x) := Real.exp_pos _
  have ht1 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hte : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have hex := Real.add_one_le_exp x
  have hxt : (x + 1) * Real.exp (-x) ≤ 1 := by nlinarith
  rw [div_le_iff₀ (by linarith)]
  have e : (1 + 1 / x) * (1 - Real.exp (-x)) = ((x + 1) * (1 - Real.exp (-x))) / x := by
    field_simp
  rw [e, le_div_iff₀ hx]
  nlinarith

/-! ### Block tails and cell masses -/

private lemma largeAverageUpper_corr_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (T₁ T₂ : Finset ι) (J : Set ℝ) : 0 ≤ eigMassCorr A T₁ T₂ J := by
  unfold eigMassCorr
  split_ifs
  · exact Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  · exact le_rfl

/-- If every cyclic block distance is at most `R`, the block tail beyond `R` is at most `0`. -/
private lemma largeAverageUpper_blockTail_nonpos {W L : ℕ} {R : ℝ}
    (hR : ∀ a b : Fin L, (cycDist a b : ℝ) ≤ R) (p : Fin L × Fin W → ℝ) :
    blockTail W L R p ≤ 0 := by
  unfold blockTail
  split_ifs with h
  · refine (Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ ⟨0, h⟩))).trans
      (le_of_eq ?_)
    refine Finset.sum_eq_zero fun b hb => ?_
    exact absurd (Finset.mem_filter.mp hb).2 (not_lt.mpr (hR _ _))
  · exact le_rfl

/-- The block tail is at most the mass outside the ball of radius `R` around any block `a`. -/
private lemma largeAverageUpper_blockTail_le {W L : ℕ} (R : ℝ) (p : Fin L × Fin W → ℝ)
    (a : Fin L) :
    blockTail W L R p ≤
      ∑ b ∈ univ.filter (fun b : Fin L => R < (cycDist a b : ℝ)), ∑ α, p (b, α) := by
  unfold blockTail
  rw [dite_eq_left_of_eq_true (eq_true a.pos)]
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ a))

/-- A sum over the coordinates of the cell `a, …, a+ℓ−1`, grouped by blocks. -/
private lemma largeAverageUpper_sum_cellCoords {W L : ℕ} (a : Fin L) (ℓ : ℕ)
    (f : Fin L × Fin W → ℝ) :
    ∑ x ∈ cellCoords a ℓ, f x = ∑ b : Fin L, if b ∈ cellSet a ℓ then ∑ α, f (b, α) else 0 := by
  rw [cellCoords, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp

/-- The deterministic step of the proof of Lemma 8.1 [uva:thm:upper-audit] on simple
spectrum: for cells `A_i = s_i, …, s_i+ℓ−1` covering `ℤ_L`, the count of (3.6)
[eq:averaged-tail] is at most `W^a Σ_i Σ_{‖s_i − s_j‖_L > R − ℓ} Q(A_i, A_j)`. -/
private lemma largeAverageUpper_det {W L : ℕ} (hW : 0 < W) {ι : Type*} [Fintype ι] [Nonempty ι]
    (s : ι → Fin L) (ℓ : ℕ) (hcov : ∀ b : Fin L, ∃ i, ∃ u < ℓ, cellBlock (s i) u = b)
    {H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hH : H.IsHermitian)
    (hinj : Function.Injective hH.eigenvalues) (J : Set ℝ) (R a : ℝ) :
    (tailCount W L H J R a : ℝ) ≤ (W : ℝ) ^ a * ∑ i, ∑ j ∈ univ.filter
      (fun j => R - (ℓ : ℝ) < (cycDist (s i) (s j) : ℝ)),
        eigMassCorr H (cellCoords (s i) ℓ) (cellCoords (s j) ℓ) J := by
  obtain ⟨m, hm⟩ : ∃ m : ι → Fin L × Fin W → ℝ, m = fun i k =>
      ∑ x ∈ cellCoords (s i) ℓ, ‖hH.eigenvectorBasis k x‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ι → Finset ι, F = fun i =>
      univ.filter (fun j => R - (ℓ : ℝ) < (cycDist (s i) (s j) : ℝ)) := ⟨_, rfl⟩
  have hm0 : ∀ i k, 0 ≤ m i k := fun i k => by
    rw [hm]
    exact Finset.sum_nonneg fun _ _ => by positivity
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hWa : (0 : ℝ) ≤ (W : ℝ) ^ a := (Real.rpow_pos_of_pos hW0 _).le
  have hX0 : ∀ k, 0 ≤ (W : ℝ) ^ a * ∑ i, ∑ j ∈ F i, Real.sqrt (m i k * m j k) := fun k =>
    mul_nonneg hWa (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _)
  have hRHS : (W : ℝ) ^ a * ∑ i, ∑ j ∈ univ.filter
      (fun j => R - (ℓ : ℝ) < (cycDist (s i) (s j) : ℝ)),
        eigMassCorr H (cellCoords (s i) ℓ) (cellCoords (s j) ℓ) J =
      ∑ k ∈ univ.filter (fun k => hH.eigenvalues k ∈ J),
        (W : ℝ) ^ a * ∑ i, ∑ j ∈ F i, Real.sqrt (m i k * m j k) := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm, hF]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [eigMassCorr, hH, ↓reduceDIte, hm]
  have hmult : ∀ k, mult hH.eigenvalues k = 1 := by
    intro k
    unfold mult
    rw [Finset.card_eq_one]
    exact ⟨k, by ext j; simp [hinj.eq_iff]⟩
  have key : ∀ k, (W : ℝ) ^ (-a) < blockTail W L R
      (projDiag hH.eigenvalues (fun j => ⇑(hH.eigenvectorBasis j)) k) →
      1 ≤ (W : ℝ) ^ a * ∑ i, ∑ j ∈ F i, Real.sqrt (m i k * m j k) := by
    intro k hQ
    have hp : projDiag hH.eigenvalues (fun j => ⇑(hH.eigenvectorBasis j)) k =
        fun x => ‖hH.eigenvectorBasis k x‖ ^ 2 :=
      funext fun x => projDiag_of_mult_eq_one _ _ (hmult k) x
    rw [hp] at hQ
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image univ (fun i => m i k) univ_nonempty
    set f : Fin L → ℝ := fun b => ∑ α, ‖hH.eigenvectorBasis k (b, α)‖ ^ 2 with hfdef
    have hf0 : ∀ b, 0 ≤ f b := fun b => Finset.sum_nonneg fun _ _ => by positivity
    have hcover : ∑ b ∈ univ.filter (fun b : Fin L => R < (cycDist (s i₀) b : ℝ)), f b ≤
        ∑ j ∈ F i₀, m j k := by
      calc ∑ b ∈ univ.filter (fun b : Fin L => R < (cycDist (s i₀) b : ℝ)), f b
          ≤ ∑ b ∈ univ.filter (fun b : Fin L => R < (cycDist (s i₀) b : ℝ)),
              ∑ j ∈ F i₀, (if b ∈ cellSet (s j) ℓ then f b else 0) := by
            refine Finset.sum_le_sum fun b hb => ?_
            obtain ⟨j, u, hu, hjb⟩ := hcov b
            have hjF : j ∈ F i₀ := by
              rw [hF, Finset.mem_filter]
              refine ⟨Finset.mem_univ _, ?_⟩
              have hRb : R < (cycDist (s i₀) b : ℝ) := (Finset.mem_filter.mp hb).2
              have htri := largeAverageUpper_cycDist_tri (s i₀) (s j) b
              have hcb := largeAverageUpper_cycDist_cellBlock (s j) u
              rw [hjb] at hcb
              have h1 : (cycDist (s i₀) b : ℝ) ≤ (cycDist (s i₀) (s j) : ℝ) + u := by
                exact_mod_cast htri.trans (by omega)
              have hu' : (u : ℝ) < ℓ := by exact_mod_cast hu
              linarith
            have hmem : b ∈ cellSet (s j) ℓ :=
              Finset.mem_image.mpr ⟨u, Finset.mem_range.mpr hu, hjb⟩
            calc f b = (if b ∈ cellSet (s j) ℓ then f b else 0) :=
                (ite_eq_left_of_eq_true _ _ (eq_true hmem)).symm
              _ ≤ ∑ j' ∈ F i₀, (if b ∈ cellSet (s j') ℓ then f b else 0) :=
                Finset.single_le_sum (f := fun j' => if b ∈ cellSet (s j') ℓ then f b else 0)
                  (fun j' _ => by split_ifs; exacts [hf0 b, le_rfl]) hjF
        _ = ∑ j ∈ F i₀, ∑ b ∈ univ.filter (fun b : Fin L => R < (cycDist (s i₀) b : ℝ)),
              (if b ∈ cellSet (s j) ℓ then f b else 0) := Finset.sum_comm
        _ ≤ ∑ j ∈ F i₀, ∑ b : Fin L, (if b ∈ cellSet (s j) ℓ then f b else 0) := by
            refine Finset.sum_le_sum fun j _ => ?_
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              fun b _ _ => by split_ifs; exacts [hf0 b, le_rfl]
        _ = ∑ j ∈ F i₀, m j k := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hm]
            exact (largeAverageUpper_sum_cellCoords (s j) ℓ
              (fun x => ‖hH.eigenvectorBasis k x‖ ^ 2)).symm
    have hsq : ∑ j ∈ F i₀, m j k ≤ ∑ j ∈ F i₀, Real.sqrt (m i₀ k * m j k) := by
      refine Finset.sum_le_sum fun j _ => ?_
      calc m j k = Real.sqrt (m j k * m j k) := (Real.sqrt_mul_self (hm0 j k)).symm
        _ ≤ Real.sqrt (m i₀ k * m j k) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (hi₀ j (Finset.mem_univ _)) (hm0 j k))
    have hsum : ∑ j ∈ F i₀, Real.sqrt (m i₀ k * m j k) ≤
        ∑ i, ∑ j ∈ F i, Real.sqrt (m i k * m j k) :=
      Finset.single_le_sum (f := fun i => ∑ j ∈ F i, Real.sqrt (m i k * m j k))
        (fun i _ => Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _) (Finset.mem_univ i₀)
    have hbt := largeAverageUpper_blockTail_le (W := W) R
      (fun x => ‖hH.eigenvectorBasis k x‖ ^ 2) (s i₀)
    have hWa1 : (W : ℝ) ^ a * (W : ℝ) ^ (-a) = 1 := by
      rw [← Real.rpow_add hW0]
      simp
    calc (1 : ℝ) = (W : ℝ) ^ a * (W : ℝ) ^ (-a) := hWa1.symm
      _ ≤ (W : ℝ) ^ a * blockTail W L R (fun x => ‖hH.eigenvectorBasis k x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hQ.le hWa
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbt.trans (hcover.trans (hsq.trans hsum))) hWa
  rw [hRHS]
  unfold tailCount profCount
  rw [dite_eq_left_of_eq_true (eq_true hH)]
  calc ((univ.filter fun k => hH.eigenvalues k ∈ J ∧
        projDiag hH.eigenvalues (fun j => ⇑(hH.eigenvectorBasis j)) k ∈
          {p | (W : ℝ) ^ (-a) < blockTail W L R p}).card : ℝ)
      = ∑ k ∈ univ.filter (fun k => hH.eigenvalues k ∈ J ∧
          projDiag hH.eigenvalues (fun j => ⇑(hH.eigenvectorBasis j)) k ∈
            {p | (W : ℝ) ^ (-a) < blockTail W L R p}), (1 : ℝ) := by simp
    _ ≤ ∑ k ∈ univ.filter (fun k => hH.eigenvalues k ∈ J ∧
          projDiag hH.eigenvalues (fun j => ⇑(hH.eigenvectorBasis j)) k ∈
            {p | (W : ℝ) ^ (-a) < blockTail W L R p}),
          (W : ℝ) ^ a * ∑ i, ∑ j ∈ F i, Real.sqrt (m i k * m j k) :=
        Finset.sum_le_sum fun k hk => key k (Finset.mem_filter.mp hk).2.2
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => hX0 k
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        exact hk.1

/-- The cell correlator `Q(A, B)` of the model (1.3) [eq:model] is a.e.-measurable for
measurable `J`. -/
private lemma largeAverageUpper_aemeasurable_corr (g : ℝ) (W L : ℕ) {J : Set ℝ}
    (hJ : MeasurableSet J) (T₁ T₂ : Finset (Fin L × Fin W)) :
    AEMeasurable (fun ω => ENNReal.ofReal (eigMassCorr (Hmat g W L ω) T₁ T₂ J)) (μ W L) := by
  have hF : Measurable fun ω : Ω W L => ∑ k, if eigAt (Hmat g W L ω) k ∈ J then
      Real.sqrt ((∑ i ∈ T₁, eigProfile (Hmat g W L ω) k i) *
        ∑ i ∈ T₂, eigProfile (Hmat g W L ω) k i) else 0 := by
    refine Finset.measurable_sum _ fun k _ => Measurable.ite ?_ ?_ measurable_const
    · exact hJ.preimage (continuous_sortedEig_Hmat g W L _).measurable
    · exact Real.continuous_sqrt.measurable.comp
        ((Finset.measurable_sum _ fun i _ =>
          (measurable_pi_apply i).comp (measurable_eigProfile_Hmat g W L k)).mul
        (Finset.measurable_sum _ fun i _ =>
          (measurable_pi_apply i).comp (measurable_eigProfile_Hmat g W L k)))
  refine ENNReal.measurable_ofReal.comp_aemeasurable (hF.aemeasurable.congr ?_)
  filter_upwards [ae_injective_eigenvalues g W L] with ω hω
  have hA := Hmat_isHermitian g W L ω
  have hev : ∀ k, hA.eigenvalues k = eigAt (Hmat g W L ω) k := fun k =>
    eigenvalues_eq_sortedEig hA k
  have hp : ∀ k i, eigProfile (Hmat g W L ω) k i = ‖hA.eigenvectorBasis k i‖ ^ 2 := by
    intro k i
    rw [norm_sq_eigenvectorBasis_eq_adjugate hA hω]
    simp only [eigProfile, hev]
  unfold eigMassCorr
  simp only [hA, ↓reduceDIte, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hev, hp]

/-- The final estimate of the proof of Lemma 8.1 [uva:thm:upper-audit]: with `b = W g²`,
`R = K b log W`, `c K / 2 = A + P + D + 1 + c / 2` and the cells starting at the blocks `i n`,
`W^A Σ_i Σ_{‖s_i − s_j‖_L > R − 2n} C n W^P e^{−c (‖s_i − s_j‖_L − 4n)/b} ≤ W L W^{−D}`. -/
private lemma largeAverageUpper_bound {W L M n : ℕ} {A D C c P K g R : ℝ} (s : Fin M → Fin L)
    (hs : ∀ i, (s i).val = i.val * n) (hMn : M * n ≤ L) (hn0 : 0 < n) (hC : 0 < C)
    (hc : 0 < c) (hKc : c * K / 2 = A + P + D + 1 + c / 2) (hW1 : (1 : ℝ) ≤ W)
    (hWC₁ : 2 * C * Real.exp (5 * c) * (1 + 4 / c) ≤ W) (hng : (n : ℝ) ≤ g ^ 2)
    (hgn : g ^ 2 ≤ 2 * n) (hRdef : R = K * W * g ^ 2 * Real.log W) :
    (W : ℝ) ^ A * ∑ i, ∑ j ∈ univ.filter
      (fun j => R - ((2 * n : ℕ) : ℝ) < (cycDist (s i) (s j) : ℝ)),
        C * n * (W : ℝ) ^ P *
          Real.exp (-c * ((cycDist (s i) (s j) - 4 * n : ℕ) : ℝ) / (W * g ^ 2)) ≤
      (W : ℝ) * L * (W : ℝ) ^ (-D) := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hg2 : 1 ≤ g ^ 2 := by linarith
  have hgne : g ≠ 0 := by
    rintro rfl
    norm_num at hg2
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = W * g ^ 2 := ⟨_, rfl⟩
  have hb0 : 0 < b := by rw [hbdef]; positivity
  have hnb : (n : ℝ) ≤ b := by rw [hbdef]; nlinarith
  have hWA : (0 : ℝ) ≤ (W : ℝ) ^ A := (Real.rpow_pos_of_pos hW0 _).le
  obtain ⟨μ', hμ'def⟩ : ∃ μ' : ℝ, μ' = c / (2 * b) := ⟨_, rfl⟩
  have hμ' : 0 < μ' := by rw [hμ'def]; positivity
  have hterm : ∀ i, ∀ j ∈ univ.filter
      (fun j => R - ((2 * n : ℕ) : ℝ) < (cycDist (s i) (s j) : ℝ)),
      Real.exp (-c * ((cycDist (s i) (s j) - 4 * n : ℕ) : ℝ) / (W * g ^ 2)) ≤
        Real.exp (5 * c) * (W : ℝ) ^ (-(c * K / 2)) *
          Real.exp (-μ' * cycDist (s i) (s j)) := by
    intro i j hj
    have hF' : R - ((2 * n : ℕ) : ℝ) < (cycDist (s i) (s j) : ℝ) := (Finset.mem_filter.mp hj).2
    push_cast at hF'
    have hd : (cycDist (s i) (s j) : ℝ) ≤ ((cycDist (s i) (s j) - 4 * n : ℕ) : ℝ) + 4 * n := by
      exact_mod_cast (by omega : cycDist (s i) (s j) ≤ (cycDist (s i) (s j) - 4 * n) + 4 * n)
    obtain ⟨d, hddef⟩ : ∃ d : ℝ, d = ((cycDist (s i) (s j) - 4 * n : ℕ) : ℝ) := ⟨_, rfl⟩
    obtain ⟨Dij, hDdef⟩ : ∃ Dij : ℝ, Dij = (cycDist (s i) (s j) : ℝ) := ⟨_, rfl⟩
    rw [← hddef, ← hDdef] at hd ⊢
    rw [← hDdef] at hF'
    rw [Real.rpow_def_of_pos hW0, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    have e1 : -c * d / (W * g ^ 2) = -c * d / b := by rw [hbdef]
    have e2 : (5 * c + Real.log W * (-(c * K / 2)) + -μ' * Dij) * b =
        5 * c * b - c * R / 2 - c * Dij / 2 := by
      rw [hRdef, hμ'def, hbdef]
      field_simp
      ring
    rw [e1, div_le_iff₀ hb0, e2]
    nlinarith [mul_le_mul_of_nonneg_left hd hc.le, mul_le_mul_of_nonneg_left hnb hc.le,
      mul_lt_mul_of_pos_left hF' hc]
  have hgeo : ∀ i, ∑ j, Real.exp (-μ' * cycDist (s i) (s j)) ≤ 2 * (1 + 4 / c) * W := by
    intro i
    have h1 := largeAverageUpper_sum_cells hMn s hs i hμ' hn0
    have hx : 0 < μ' * n := by positivity
    have h2 := largeAverageUpper_inv_one_sub_exp hx
    have h3 : 1 / (μ' * n) ≤ 4 * W / c := by
      rw [div_le_div_iff₀ hx hc, one_mul, hμ'def,
        show 4 * (W : ℝ) * (c / (2 * b) * n) = 2 * W * c * n / b by field_simp; ring,
        le_div_iff₀ hb0, hbdef]
      nlinarith [mul_le_mul_of_nonneg_left hgn (by positivity : (0 : ℝ) ≤ c * W)]
    have h4 : 2 * (1 + 4 / c) * (W : ℝ) = 2 * W + 2 * (4 * W / c) := by ring
    calc ∑ j, Real.exp (-μ' * cycDist (s i) (s j))
        ≤ 2 / (1 - Real.exp (-(μ' * n))) := h1
      _ = 2 * (1 / (1 - Real.exp (-(μ' * n)))) := by ring
      _ ≤ 2 * (1 + 1 / (μ' * n)) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ 2 * (1 + 4 * W / c) := mul_le_mul_of_nonneg_left (add_le_add le_rfl h3) (by norm_num)
      _ ≤ 2 * (1 + 4 / c) * W := by rw [h4]; linarith
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = C * n * (W : ℝ) ^ P *
      (Real.exp (5 * c) * (W : ℝ) ^ (-(c * K / 2)) * (2 * (1 + 4 / c) * W)) := ⟨_, rfl⟩
  have hrow : ∀ i, ∑ j ∈ univ.filter
      (fun j => R - ((2 * n : ℕ) : ℝ) < (cycDist (s i) (s j) : ℝ)),
      C * n * (W : ℝ) ^ P *
        Real.exp (-c * ((cycDist (s i) (s j) - 4 * n : ℕ) : ℝ) / (W * g ^ 2)) ≤ B := by
    intro i
    have hCn : 0 ≤ C * n * (W : ℝ) ^ P := by positivity
    have hE : 0 ≤ Real.exp (5 * c) * (W : ℝ) ^ (-(c * K / 2)) := by positivity
    rw [hBdef, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hCn
    calc ∑ j ∈ univ.filter (fun j => R - ((2 * n : ℕ) : ℝ) < (cycDist (s i) (s j) : ℝ)),
          Real.exp (-c * ((cycDist (s i) (s j) - 4 * n : ℕ) : ℝ) / (W * g ^ 2))
        ≤ ∑ j ∈ univ.filter (fun j => R - ((2 * n : ℕ) : ℝ) < (cycDist (s i) (s j) : ℝ)),
          Real.exp (5 * c) * (W : ℝ) ^ (-(c * K / 2)) *
            Real.exp (-μ' * cycDist (s i) (s j)) := Finset.sum_le_sum fun j hj => hterm i j hj
      _ = Real.exp (5 * c) * (W : ℝ) ^ (-(c * K / 2)) *
          ∑ j ∈ univ.filter (fun j => R - ((2 * n : ℕ) : ℝ) < (cycDist (s i) (s j) : ℝ)),
            Real.exp (-μ' * cycDist (s i) (s j)) := by rw [Finset.mul_sum]
      _ ≤ Real.exp (5 * c) * (W : ℝ) ^ (-(c * K / 2)) *
          ∑ j, Real.exp (-μ' * cycDist (s i) (s j)) := by
          refine mul_le_mul_of_nonneg_left ?_ hE
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun _ _ _ => (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left (hgeo i) hE
  have hexp : (W : ℝ) ^ A * (W : ℝ) ^ P * (W : ℝ) ^ (-(c * K / 2)) * W ≤ (W : ℝ) ^ (-D) := by
    calc (W : ℝ) ^ A * (W : ℝ) ^ P * (W : ℝ) ^ (-(c * K / 2)) * W
        = (W : ℝ) ^ (A + P + -(c * K / 2) + 1) := by
          rw [Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_one]
      _ ≤ (W : ℝ) ^ (-D) := Real.rpow_le_rpow_of_exponent_le hW1 (by rw [hKc]; linarith)
  have hMnR : (M : ℝ) * n ≤ L := by exact_mod_cast hMn
  have hC₁0 : 0 ≤ 2 * C * Real.exp (5 * c) * (1 + 4 / c) := by positivity
  calc (W : ℝ) ^ A * ∑ i, ∑ j ∈ univ.filter
        (fun j => R - ((2 * n : ℕ) : ℝ) < (cycDist (s i) (s j) : ℝ)),
        C * n * (W : ℝ) ^ P *
          Real.exp (-c * ((cycDist (s i) (s j) - 4 * n : ℕ) : ℝ) / (W * g ^ 2))
      ≤ (W : ℝ) ^ A * ∑ _i : Fin M, B :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hrow i) hWA
    _ = (W : ℝ) ^ A * (M * B) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = 2 * C * Real.exp (5 * c) * (1 + 4 / c) * ((M : ℝ) * n) *
          ((W : ℝ) ^ A * (W : ℝ) ^ P * (W : ℝ) ^ (-(c * K / 2)) * W) := by
        rw [hBdef]
        ring
    _ ≤ W * L * (W : ℝ) ^ (-D) :=
        mul_le_mul (mul_le_mul hWC₁ hMnR (by positivity) hW0.le) hexp (by positivity)
          (by positivity)

/-- The deterministic steps of Appendix E.1 [app:fr-concentration-proof] after (E.3)
[uva:eq:cell-correlator]: for fixed `C, c, P, A, D > 0` there are `K` and a width threshold,
independent of `L, g`, such that the cell-correlator bound
`𝔼 Q(A, B) ≤ C n W^P exp(−c d/(W g²))` on `J = [-E₀, E₀]` for `n = ⌊g²⌋ ≥ 1` and all cells of
length in `[n, 2n]` gives (3.6) [eq:averaged-tail] on `J` with `R = K W g² log W`. -/
theorem averaged_tail_of_correlator {E₀ C c P : ℝ} (hC : 0 < C) (hc : 0 < c) (hP : 0 < P)
    (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ K : ℝ, 0 < K ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, ∀ g : ℝ, 0 ≤ g → 1 ≤ g ^ 2 →
      (∀ a b : Fin L, ∀ nA nB d : ℕ,
        ⌊g ^ 2⌋₊ ≤ nA → nA ≤ 2 * ⌊g ^ 2⌋₊ → ⌊g ^ 2⌋₊ ≤ nB → nB ≤ 2 * ⌊g ^ 2⌋₊ →
        (∀ i < nA, ∀ j < nB, d ≤ cycDist (cellBlock a i) (cellBlock b j)) →
          ∫⁻ ω, ENNReal.ofReal (eigMassCorr (Hmat g W L ω) (cellCoords a nA) (cellCoords b nB)
              (Set.Icc (-E₀) E₀)) ∂(μ W L) ≤
            ENNReal.ofReal (C * ⌊g ^ 2⌋₊ * (W : ℝ) ^ P * Real.exp (-c * d / (W * g ^ 2)))) →
        AveragedTailBound W L g (Set.Icc (-E₀) E₀) (K * W * g ^ 2 * Real.log W) A D := by
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 2 * (A + P + D + 1) / c + 1 := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by
    have : 0 ≤ 2 * (A + P + D + 1) / c := by positivity
    linarith
  have hKc : c * K / 2 = A + P + D + 1 + c / 2 := by
    rw [hKdef]
    field_simp
  obtain ⟨C₁, hC₁def⟩ : ∃ C₁ : ℝ, C₁ = 2 * C * Real.exp (5 * c) * (1 + 4 / c) := ⟨_, rfl⟩
  refine ⟨K, by linarith, max 3 ⌈C₁⌉₊, ?_⟩
  intro W hW L g hg0 hg2 hcor
  have hW3 : (3 : ℝ) ≤ W := by exact_mod_cast le_trans (le_max_left _ _) hW
  have hWC₁ : C₁ ≤ (W : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hW)
  have hW0 : (0 : ℝ) < W := by linarith
  have hW1 : (1 : ℝ) ≤ W := by linarith
  have hWpos : 0 < W := by exact_mod_cast hW0
  have hlog : 1 ≤ Real.log W := by
    rw [Real.le_log_iff_exp_le hW0]
    have := Real.exp_one_lt_d9
    norm_num at this
    linarith
  obtain ⟨n, hndef⟩ : ∃ n : ℕ, n = ⌊g ^ 2⌋₊ := ⟨_, rfl⟩
  have hn1 : 1 ≤ n := by
    rw [hndef]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hg2).ne'
  have hn0 : 0 < n := hn1
  have hng : (n : ℝ) ≤ g ^ 2 := by
    rw [hndef]
    exact Nat.floor_le (by positivity)
  have hgn : g ^ 2 ≤ 2 * n := by
    have h := Nat.lt_floor_add_one (g ^ 2)
    rw [← hndef] at h
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    linarith
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = W * g ^ 2 := ⟨_, rfl⟩
  have hb0 : 0 < b := by rw [hbdef]; positivity
  have hnb : (n : ℝ) ≤ b := by rw [hbdef]; nlinarith
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = K * W * g ^ 2 * Real.log W := ⟨_, rfl⟩
  have hRg : g ^ 2 ≤ R := by
    have h1 : 1 ≤ K * W * Real.log W :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK1 hW1) hlog
    rw [hRdef]
    nlinarith
  obtain ⟨J, hJdef⟩ : ∃ J : Set ℝ, J = Set.Icc (-E₀) E₀ := ⟨_, rfl⟩
  have hJ : MeasurableSet J := by rw [hJdef]; exact measurableSet_Icc
  unfold AveragedTailBound
  rw [← hRdef, ← hJdef]
  have hRHS0 : 0 ≤ (W : ℝ) * L * (W : ℝ) ^ (-D) := by positivity
  suffices hI : ∫ ω, (tailCount W L (Hmat g W L ω) J R A : ℝ) ∂(μ W L) ≤
      (W : ℝ) * L * (W : ℝ) ^ (-D) by
    rcases Nat.eq_zero_or_pos L with hL | hL
    · simp only [hL, Nat.cast_zero, mul_zero, inv_zero, zero_mul]
      positivity
    · have hWL : (0 : ℝ) < W * L := by positivity
      calc ((W : ℝ) * L)⁻¹ * ∫ ω, (tailCount W L (Hmat g W L ω) J R A : ℝ) ∂(μ W L)
          ≤ ((W : ℝ) * L)⁻¹ * ((W : ℝ) * L * (W : ℝ) ^ (-D)) :=
            mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr hWL.le)
        _ = (W : ℝ) ^ (-D) := by field_simp
  by_cases hnL : n ≤ L
  swap
  · -- `L < n ≤ R`: every block distance is at most `R` and the count vanishes
    have hRall : ∀ a b' : Fin L, (cycDist a b' : ℝ) ≤ R := fun a b' => by
      have h1 := largeAverageUpper_cycDist_lt a b'
      have h2 : (cycDist a b' : ℝ) ≤ n := by exact_mod_cast (by omega : cycDist a b' ≤ n)
      linarith
    have h0 : ∀ ω, tailCount W L (Hmat g W L ω) J R A = 0 := by
      intro ω
      unfold tailCount profCount
      rw [dite_eq_left_of_eq_true (eq_true (Hmat_isHermitian g W L ω))]
      refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun k _ hk => ?_)
      have hbt := largeAverageUpper_blockTail_nonpos (W := W) hRall
        (projDiag (Hmat_isHermitian g W L ω).eigenvalues
          (fun j => ⇑((Hmat_isHermitian g W L ω).eigenvectorBasis j)) k)
      have h2 := hk.2
      simp only [Set.mem_ofPred_eq] at h2
      have hpos : 0 < (W : ℝ) ^ (-A) := Real.rpow_pos_of_pos hW0 _
      linarith
    simp only [h0, Nat.cast_zero, integral_zero]
    exact hRHS0
  -- `n ≤ L`: the cells `A_i = i n, …, i n + 2n − 1`, `i < M = ⌊L/n⌋`, cover `ℤ_L`
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = L / n := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by rw [hMdef]; exact Nat.div_pos hnL hn0
  have hMn : M * n ≤ L := by rw [hMdef]; exact Nat.div_mul_le_self L n
  have hLM : L < M * n + n := by rw [hMdef]; exact Nat.lt_div_mul_add hn0
  have hsL : ∀ i : Fin M, i.val * n < L := fun i => by
    have h := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at h
    omega
  obtain ⟨s, hsdef⟩ : ∃ s : Fin M → Fin L, s = fun i => ⟨i.val * n, hsL i⟩ := ⟨_, rfl⟩
  have hs : ∀ i, (s i).val = i.val * n := fun i => by rw [hsdef]
  have : Nonempty (Fin M) := ⟨⟨0, hM1⟩⟩
  have hcov : ∀ b' : Fin L, ∃ i : Fin M, ∃ u < 2 * n, cellBlock (s i) u = b' := by
    intro b'
    have hb := b'.isLt
    have h1 := Nat.div_mul_le_self b'.val n
    have h2 := Nat.lt_div_mul_add (a := b'.val) hn0
    by_cases hq : b'.val / n < M
    · refine ⟨⟨b'.val / n, hq⟩, b'.val - b'.val / n * n, by omega, Fin.ext ?_⟩
      change ((s ⟨b'.val / n, hq⟩).val + (b'.val - b'.val / n * n)) % L = b'.val
      rw [hs, Nat.add_sub_cancel' h1, Nat.mod_eq_of_lt hb]
    · have h3 : M * n ≤ b'.val / n * n := Nat.mul_le_mul_right n (by omega)
      have h4 : (M - 1) * n + n = M * n := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hM1]
      have h5 : b'.val - (M - 1) * n < 2 * n := by omega
      refine ⟨⟨M - 1, by omega⟩, b'.val - (M - 1) * n, h5, Fin.ext ?_⟩
      change ((s ⟨M - 1, by omega⟩).val + (b'.val - (M - 1) * n)) % L = b'.val
      rw [hs]
      change ((M - 1) * n + (b'.val - (M - 1) * n)) % L = b'.val
      rw [Nat.add_sub_cancel' (by omega), Nat.mod_eq_of_lt hb]
  obtain ⟨F, hFdef⟩ : ∃ F : Fin M → Finset (Fin M), F = fun i =>
      univ.filter (fun j => R - ((2 * n : ℕ) : ℝ) < (cycDist (s i) (s j) : ℝ)) := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : Fin M → Fin M → Ω W L → ℝ, Q = fun i j ω =>
      eigMassCorr (Hmat g W L ω) (cellCoords (s i) (2 * n)) (cellCoords (s j) (2 * n)) J :=
    ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : Fin M → Fin M → ℝ, T = fun i j => C * n * (W : ℝ) ^ P *
      Real.exp (-c * ((cycDist (s i) (s j) - 4 * n : ℕ) : ℝ) / (W * g ^ 2)) := ⟨_, rfl⟩
  have hQ0 : ∀ i j ω, 0 ≤ Q i j ω := fun i j ω => by
    rw [hQdef]
    exact largeAverageUpper_corr_nonneg _ _ _ _
  have hT0 : ∀ i j, 0 ≤ T i j := fun i j => by
    rw [hTdef]
    positivity
  -- the deterministic step on simple spectrum
  have hdet : ∀ᵐ ω ∂(μ W L), (tailCount W L (Hmat g W L ω) J R A : ℝ) ≤
      (W : ℝ) ^ A * ∑ i, ∑ j ∈ F i, Q i j ω := by
    filter_upwards [ae_injective_eigenvalues g W L] with ω hω
    rw [hFdef, hQdef]
    exact largeAverageUpper_det hWpos s (2 * n) hcov (Hmat_isHermitian g W L ω) hω J R A
  -- (E.3) [uva:eq:cell-correlator] for each pair of cells
  have hpair : ∀ i, ∀ j ∈ F i,
      ∫⁻ ω, ENNReal.ofReal (Q i j ω) ∂(μ W L) ≤ ENNReal.ofReal (T i j) := by
    intro i j _
    rw [hQdef, hTdef]
    have h := hcor (s i) (s j) (2 * n) (2 * n) (cycDist (s i) (s j) - 4 * n)
      (by rw [← hndef]; omega) (by rw [← hndef]) (by rw [← hndef]; omega) (by rw [← hndef]) ?_
    · rw [← hndef, ← hJdef] at h
      exact h
    intro u hu v hv
    have t1 := largeAverageUpper_cycDist_tri (s i) (cellBlock (s i) u) (s j)
    have t2 := largeAverageUpper_cycDist_tri (cellBlock (s i) u) (cellBlock (s j) v) (s j)
    have t3 := largeAverageUpper_cycDist_cellBlock (s i) u
    have t4 := largeAverageUpper_cycDist_cellBlock (s j) v
    rw [largeAverageUpper_cycDist_comm (cellBlock (s j) v) (s j)] at t2
    omega
  -- taking expectations
  have hint := integrable_tailCount_Hmat g W L hJ R A
  have hnn : 0 ≤ᵐ[μ W L] fun ω => (tailCount W L (Hmat g W L ω) J R A : ℝ) :=
    Filter.Eventually.of_forall fun ω => Nat.cast_nonneg _
  have hWA : (0 : ℝ) ≤ (W : ℝ) ^ A := (Real.rpow_pos_of_pos hW0 _).le
  have hlin : ENNReal.ofReal (∫ ω, (tailCount W L (Hmat g W L ω) J R A : ℝ) ∂(μ W L)) ≤
      ENNReal.ofReal ((W : ℝ) ^ A * ∑ i, ∑ j ∈ F i, T i j) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint hnn]
    calc ∫⁻ ω, ENNReal.ofReal (tailCount W L (Hmat g W L ω) J R A : ℝ) ∂(μ W L)
        ≤ ∫⁻ ω, ENNReal.ofReal ((W : ℝ) ^ A * ∑ i, ∑ j ∈ F i, Q i j ω) ∂(μ W L) :=
          lintegral_mono_ae (hdet.mono fun ω h => ENNReal.ofReal_le_ofReal h)
      _ = ∫⁻ ω, ENNReal.ofReal ((W : ℝ) ^ A) *
            ∑ i, ∑ j ∈ F i, ENNReal.ofReal (Q i j ω) ∂(μ W L) := by
          refine lintegral_congr fun ω => ?_
          rw [ENNReal.ofReal_mul hWA,
            ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => hQ0 i j ω]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          exact ENNReal.ofReal_sum_of_nonneg fun j _ => hQ0 i j ω
      _ = ENNReal.ofReal ((W : ℝ) ^ A) *
            ∑ i, ∑ j ∈ F i, ∫⁻ ω, ENNReal.ofReal (Q i j ω) ∂(μ W L) := by
          have hmeas : ∀ i j, AEMeasurable (fun ω => ENNReal.ofReal (Q i j ω)) (μ W L) :=
            fun i j => by
              rw [hQdef]
              exact largeAverageUpper_aemeasurable_corr g W L hJ _ _
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_finsetSum' _ fun i _ => Finset.aemeasurable_fun_sum _ fun j _ => hmeas i j]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          exact lintegral_finsetSum' _ fun j _ => hmeas i j
      _ ≤ ENNReal.ofReal ((W : ℝ) ^ A) * ∑ i, ∑ j ∈ F i, ENNReal.ofReal (T i j) := by
          gcongr with i _ j hj
          exact hpair i j hj
      _ = ENNReal.ofReal ((W : ℝ) ^ A * ∑ i, ∑ j ∈ F i, T i j) := by
          rw [ENNReal.ofReal_mul hWA,
            ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => hT0 i j]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          exact (ENNReal.ofReal_sum_of_nonneg fun j _ => hT0 i j).symm
  -- the geometric sum over the cells and the choice of `K`
  have hreal : (W : ℝ) ^ A * ∑ i, ∑ j ∈ F i, T i j ≤ (W : ℝ) * L * (W : ℝ) ^ (-D) := by
    rw [hFdef, hTdef]
    exact largeAverageUpper_bound s hs hMn hn0 hC hc hKc hW1 (hC₁def ▸ hWC₁) hng hgn hRdef
  exact (ENNReal.ofReal_le_ofReal_iff hRHS0).mp (hlin.trans (ENNReal.ofReal_le_ofReal hreal))

end LSBA
