import LSBA.Upper.Correlator
import LSBA.Spectral.BlockTail

/-!
# From block correlators to the count of (3.6) [eq:averaged-tail]

The proof of Lemma 8.1(i) [uva:thm:upper-audit]: on simple spectrum, the count
`B_A(R)` of (3.6) [eq:averaged-tail] is at most `W^A Σ_a Σ_{‖b-a‖_L > R} 𝒬_{ab}(J)`, and a block
correlator decay gives (E.2) [uv:eq:ordinary-count].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- A profile `p` with block masses `Σ_α p(b, α) = s_b²` and block tail above `c` has
`c < Σ_a Σ_{‖b-a‖_L > R} s_a s_b`: the block `a₀` of maximal `s` gives
`Σ_{‖b-a₀‖_L > R} s_b² ≤ Σ_{‖b-a₀‖_L > R} s_{a₀} s_b`. -/
private lemma correlatorCount_lt_sum {W L : ℕ} (R c : ℝ) (p : Fin L × Fin W → ℝ)
    (s : Fin L → ℝ) (hs : ∀ b, 0 ≤ s b) (hp : ∀ b, ∑ α, p (b, α) = s b * s b)
    (h : c < blockTail W L R p) :
    c < ∑ a : Fin L, ∑ b ∈ univ.filter (fun b : Fin L => R < (cycDist a b : ℝ)), s a * s b := by
  by_cases hL : 0 < L
  · obtain ⟨a₀, -, ha₀⟩ := Finset.exists_max_image (univ : Finset (Fin L)) s
      ⟨⟨0, hL⟩, mem_univ _⟩
    have hle : blockTail W L R p ≤
        ∑ b ∈ univ.filter (fun b : Fin L => R < (cycDist a₀ b : ℝ)), ∑ α, p (b, α) := by
      simp only [blockTail, hL, ↓reduceDIte]
      exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ (mem_univ a₀))
    refine lt_of_lt_of_le h (hle.trans ?_)
    calc _ = ∑ b ∈ univ.filter (fun b : Fin L => R < (cycDist a₀ b : ℝ)), s b * s b :=
          Finset.sum_congr rfl fun b _ => hp b
      _ ≤ ∑ b ∈ univ.filter (fun b : Fin L => R < (cycDist a₀ b : ℝ)), s a₀ * s b :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (ha₀ b (mem_univ _)) (hs b)
      _ ≤ _ := Finset.single_le_sum
          (f := fun a => ∑ b ∈ univ.filter (fun b : Fin L => R < (cycDist a b : ℝ)), s a * s b)
          (fun a _ => Finset.sum_nonneg fun b _ => mul_nonneg (hs a) (hs b)) (mem_univ a₀)
  · obtain rfl : L = 0 := by omega
    simpa [blockTail] using h

/-- Residue of `x - y` modulo `L` for `x, y < L`, as a case split. -/
private lemma correlatorCount_mod (x y L : ℕ) (hx : x < L) (hy : y < L) :
    (x + L - y) % L = if y ≤ x then x - y else x + L - y := by
  split_ifs with h
  · have h1 : x + L - y = (x - y) + L := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

/-- The pair (cyclic distance, side) determines the block `b` at cyclic distance from `a`. -/
private lemma correlatorCount_cycDist_inj {L : ℕ} (a b b' : Fin L)
    (h1 : cycDist a b = cycDist a b')
    (h2 : decide ((b.val + L - a.val) % L ≤ (a.val + L - b.val) % L) =
      decide ((b'.val + L - a.val) % L ≤ (a.val + L - b'.val) % L)) : b = b' := by
  unfold cycDist at h1
  simp only [decide_eq_decide] at h2
  rw [correlatorCount_mod _ _ L b.2 a.2, correlatorCount_mod _ _ L a.2 b.2,
    correlatorCount_mod _ _ L b'.2 a.2, correlatorCount_mod _ _ L a.2 b'.2] at h1 h2
  have := a.2; have := b.2; have := b'.2
  refine Fin.ext ?_
  split_ifs at h1 h2 <;> omega

/-- The cyclic distance on `Fin L` is less than `L`. -/
private lemma correlatorCount_cycDist_lt {L : ℕ} (a b : Fin L) : cycDist a b < L :=
  lt_of_le_of_lt (min_le_left _ _) (Nat.mod_lt _ a.pos)

/-- The geometric tail `Σ_{d > R} e^{-κ d} ≤ (1 + 1/κ) e^{-κ R}`, from `e^κ ≥ 1 + κ`. -/
private lemma correlatorCount_geom {κ : ℝ} (hκ : 0 < κ) (R : ℝ) (L : ℕ) :
    ∑ d ∈ Finset.Ico (⌊R⌋₊ + 1) L, Real.exp (-κ * d) ≤ (1 + 1 / κ) * Real.exp (-κ * R) := by
  set q := Real.exp (-κ) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hpow : ∀ d : ℕ, Real.exp (-κ * d) = q ^ d := fun d => by
    rw [hq, ← Real.exp_nat_mul, mul_comm]
  simp only [hpow]
  refine (geom_sum_Ico_le_of_lt_one hq0.le hq1).trans ?_
  have h1 : (1 + κ) * q ≤ 1 := by
    have := Real.add_one_le_exp κ
    have h2 : q * Real.exp κ = 1 := by rw [hq, ← Real.exp_add]; simp
    nlinarith
  have h3 : q ^ (⌊R⌋₊ + 1) ≤ Real.exp (-κ * R) := by
    rw [← hpow]
    push_cast
    exact Real.exp_le_exp.mpr (by nlinarith [Nat.lt_floor_add_one R])
  have h4 : 1 / (1 - q) ≤ 1 + 1 / κ := by
    rw [div_le_iff₀ (by linarith)]
    have : (1 + 1 / κ) * (1 - q) = 1 + (1 - (1 + κ) * q) / κ := by field_simp; ring
    rw [this]
    have : 0 ≤ (1 - (1 + κ) * q) / κ := div_nonneg (by linarith) hκ.le
    linarith
  calc q ^ (⌊R⌋₊ + 1) / (1 - q) = q ^ (⌊R⌋₊ + 1) * (1 / (1 - q)) := by rw [mul_one_div]
    _ ≤ Real.exp (-κ * R) * (1 + 1 / κ) :=
      mul_le_mul h3 h4 (by have : 0 < 1 - q := by linarith
                           positivity) (Real.exp_pos _).le
    _ = _ := mul_comm _ _

/-- At most two blocks lie at each cyclic distance from `a`, so
`Σ_{‖b-a‖_L > R} e^{-κ‖b-a‖_L} ≤ 2 (1 + 1/κ) e^{-κ R}` for `R ≥ 0`. -/
private lemma correlatorCount_sum_far {L : ℕ} (a : Fin L) {κ R : ℝ} (hκ : 0 < κ) (hR : 0 ≤ R) :
    ∑ b ∈ univ.filter (fun b : Fin L => R < (cycDist a b : ℝ)), Real.exp (-κ * cycDist a b) ≤
      2 * ((1 + 1 / κ) * Real.exp (-κ * R)) := by
  set far := univ.filter (fun b : Fin L => R < (cycDist a b : ℝ)) with hfar
  set φ : Fin L → ℕ × Bool := fun b => (cycDist a b,
    decide ((b.val + L - a.val) % L ≤ (a.val + L - b.val) % L)) with hφ
  have hinj : Set.InjOn φ far := fun b _ b' _ h =>
    correlatorCount_cycDist_inj a b b' (congrArg Prod.fst h) (congrArg Prod.snd h)
  have h1 : ∑ b ∈ far, Real.exp (-κ * cycDist a b) = ∑ x ∈ far.image φ, Real.exp (-κ * x.1) := by
    rw [Finset.sum_image hinj]
  have hsub : far.image φ ⊆ (Finset.Ico (⌊R⌋₊ + 1) L) ×ˢ (univ : Finset Bool) := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    simp only [hfar, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    simp only [Finset.mem_product, Finset.mem_Ico, Finset.mem_univ, and_true, hφ]
    refine ⟨?_, correlatorCount_cycDist_lt a b⟩
    exact Nat.succ_le_of_lt ((Nat.floor_lt hR).mpr hb)
  calc ∑ b ∈ far, Real.exp (-κ * cycDist a b) = ∑ x ∈ far.image φ, Real.exp (-κ * x.1) := h1
    _ ≤ ∑ x ∈ (Finset.Ico (⌊R⌋₊ + 1) L) ×ˢ (univ : Finset Bool), Real.exp (-κ * x.1) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => (Real.exp_pos _).le
    _ = 2 * ∑ d ∈ Finset.Ico (⌊R⌋₊ + 1) L, Real.exp (-κ * d) := by
        rw [Finset.sum_product]
        simp [Finset.mul_sum, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (correlatorCount_geom hκ R L) (by norm_num)

/-- The proof of Lemma 8.1(i) [uva:thm:upper-audit]: on simple spectrum, the count of
(3.6) [eq:averaged-tail] is at most `W^A Σ_a Σ_{‖b-a‖_L > R} 𝒬_{ab}(J)`. -/
theorem tailCount_le_blockCorr {W L : ℕ} {H : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hH : H.IsHermitian) (hinj : Function.Injective hH.eigenvalues) (J : Set ℝ) (R A : ℝ) :
    (tailCount W L H J R A : ℝ) ≤
      (W : ℝ) ^ A * ∑ a : Fin L, ∑ b ∈ univ.filter (fun b : Fin L => R < (cycDist a b : ℝ)),
        blockCorr H J a b := by
  set far : Fin L → Finset (Fin L) := fun a =>
    univ.filter (fun b : Fin L => R < (cycDist a b : ℝ)) with hfar
  set s : Fin (L) × Fin W → Fin L → ℝ := fun k b =>
    Real.sqrt (∑ α, ‖hH.eigenvectorBasis k (b, α)‖ ^ 2) with hs
  have hcomm : ∑ a : Fin L, ∑ b ∈ far a, blockCorr H J a b =
      ∑ k, ∑ a : Fin L, ∑ b ∈ far a, if hH.eigenvalues k ∈ J then s k a * s k b else 0 := by
    simp only [blockCorr, hH, ↓reduceDIte, hs]
    exact (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans Finset.sum_comm
  rw [hcomm, Finset.mul_sum]
  unfold tailCount profCount
  simp only [hH, ↓reduceDIte]
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : hH.eigenvalues k ∈ J
  · simp only [hk, ite_true, true_and]
    by_cases hc : projDiag hH.eigenvalues (fun j => ⇑(hH.eigenvectorBasis j)) k ∈
        {p : Fin L × Fin W → ℝ | (W : ℝ) ^ (-A) < blockTail W L R p}
    · simp only [hc, ite_true, Nat.cast_one]
      have hWpos : 0 < (W : ℝ) := by exact_mod_cast k.2.pos
      have hmult : mult hH.eigenvalues k = 1 := by
        unfold mult
        rw [Finset.card_eq_one]
        exact ⟨k, by ext j; simp [hinj.eq_iff]⟩
      have := correlatorCount_lt_sum (W := W) R ((W : ℝ) ^ (-A))
        (projDiag hH.eigenvalues (fun j => ⇑(hH.eigenvectorBasis j)) k) (s k)
        (fun b => Real.sqrt_nonneg _)
        (fun b => by
          simp only [projDiag_of_mult_eq_one _ _ hmult, hs]
          rw [Real.mul_self_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]) hc
      have hpos : 0 < (W : ℝ) ^ A := Real.rpow_pos_of_pos hWpos A
      have h2 := mul_lt_mul_of_pos_left this hpos
      rw [Real.rpow_neg hWpos.le, mul_inv_cancel₀ hpos.ne'] at h2
      exact h2.le
    · simp only [hc, ite_false, Nat.cast_zero]
      exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Finset.sum_nonneg fun a _ =>
        Finset.sum_nonneg fun b _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  · simp only [hk, false_and, ite_false, Finset.sum_const_zero, mul_zero, Nat.cast_zero]
    exact le_rfl

/-- (E.2) [uv:eq:ordinary-count] from a block correlator decay (proof of
Lemma 8.1(i) [uva:thm:upper-audit]). -/
theorem averagedTail_le_of_blockCorr {Cq Pq cq b : ℝ} (hCq : 0 ≤ Cq) (hcq : 0 < cq) (hb : 0 < b)
    {W L : ℕ} (hW : 1 ≤ W) (hL : 3 ≤ L) {g : ℝ} {J : Set ℝ} (hJ : MeasurableSet J)
    (hQ : ∀ a c : Fin L, a ≠ c →
      ∫ ω, blockCorr (Hmat g W L ω) J a c ∂(μ W L) ≤
        Cq * (W : ℝ) ^ Pq * Real.exp (-cq * cycDist a c / b))
    {R A : ℝ} (hR : 0 ≤ R) :
    ((W : ℝ) * L)⁻¹ * ∫ ω, (tailCount W L (Hmat g W L ω) J R A : ℝ) ∂(μ W L) ≤
      2 * Cq * (1 + b / cq) * (W : ℝ) ^ (A + Pq - 1) * Real.exp (-cq * R / b) := by
  have hWpos : (0 : ℝ) < W := Nat.cast_pos.mpr hW
  have hLpos : (0 : ℝ) < L := Nat.cast_pos.mpr (by omega)
  set κ := cq / b with hκ_def
  have hκ : 0 < κ := div_pos hcq hb
  set far : Fin L → Finset (Fin L) := fun a =>
    univ.filter (fun b : Fin L => R < (cycDist a b : ℝ)) with hfar
  have hint : ∀ a c : Fin L, Integrable (fun ω => blockCorr (Hmat g W L ω) J a c) (μ W L) :=
    integrable_blockCorr_Hmat g W L hJ
  have hsumint : Integrable (fun ω => (W : ℝ) ^ A *
      ∑ a : Fin L, ∑ b ∈ far a, blockCorr (Hmat g W L ω) J a b) (μ W L) :=
    (integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hint a b).const_mul _
  have h1 : ∫ ω, (tailCount W L (Hmat g W L ω) J R A : ℝ) ∂(μ W L) ≤
      ∫ ω, (W : ℝ) ^ A * ∑ a : Fin L, ∑ b ∈ far a, blockCorr (Hmat g W L ω) J a b ∂(μ W L) := by
    refine integral_mono_ae (integrable_tailCount_Hmat g W L hJ R A) hsumint ?_
    filter_upwards [ae_injective_eigenvalues g W L] with ω hω
    exact tailCount_le_blockCorr (Hmat_isHermitian g W L ω) hω J R A
  have h2 : ∫ ω, (W : ℝ) ^ A * ∑ a : Fin L, ∑ b ∈ far a, blockCorr (Hmat g W L ω) J a b
      ∂(μ W L) =
      (W : ℝ) ^ A * ∑ a : Fin L, ∑ b ∈ far a, ∫ ω, blockCorr (Hmat g W L ω) J a b ∂(μ W L) := by
    rw [integral_const_mul, integral_finsetSum _ fun a _ =>
      integrable_finsetSum _ fun b _ => hint a b]
    congr 1
    exact Finset.sum_congr rfl fun a _ => integral_finsetSum _ fun b _ => hint a b
  have hC : 0 ≤ Cq * (W : ℝ) ^ Pq := mul_nonneg hCq (Real.rpow_nonneg hWpos.le _)
  have h3 : ∀ a : Fin L, ∑ b ∈ far a, ∫ ω, blockCorr (Hmat g W L ω) J a b ∂(μ W L) ≤
      Cq * (W : ℝ) ^ Pq * (2 * ((1 + 1 / κ) * Real.exp (-κ * R))) := by
    intro a
    calc _ ≤ ∑ b ∈ far a, Cq * (W : ℝ) ^ Pq * Real.exp (-κ * cycDist a b) := by
          refine Finset.sum_le_sum fun b hb => ?_
          have hb' : R < (cycDist a b : ℝ) := by simpa [hfar] using hb
          have hne : a ≠ b := by
            rintro rfl
            simp only [cycDist, Nat.add_sub_cancel_left, Nat.mod_self, min_self,
              Nat.cast_zero] at hb'
            linarith
          refine (hQ a b hne).trans (le_of_eq ?_)
          congr 2
          rw [hκ_def]
          ring
      _ = Cq * (W : ℝ) ^ Pq * ∑ b ∈ far a, Real.exp (-κ * cycDist a b) := by
          rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (correlatorCount_sum_far a hκ hR) hC
  have h4 : ∫ ω, (tailCount W L (Hmat g W L ω) J R A : ℝ) ∂(μ W L) ≤
      (W : ℝ) ^ A * (L * (Cq * (W : ℝ) ^ Pq * (2 * ((1 + 1 / κ) * Real.exp (-κ * R))))) := by
    refine h1.trans (h2.le.trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hWpos.le _)))
    refine (Finset.sum_le_sum fun a _ => h3 a).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hexp : Real.exp (-κ * R) = Real.exp (-cq * R / b) := by
    congr 1
    rw [hκ_def]
    ring
  have hk1 : 1 / κ = b / cq := by rw [hκ_def, one_div_div]
  rw [hexp, hk1] at h4
  calc _ ≤ ((W : ℝ) * L)⁻¹ * ((W : ℝ) ^ A * (L * (Cq * (W : ℝ) ^ Pq *
          (2 * ((1 + b / cq) * Real.exp (-cq * R / b)))))) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by
        rw [Real.rpow_sub_one hWpos.ne', Real.rpow_add hWpos]
        field_simp

end LSBA
