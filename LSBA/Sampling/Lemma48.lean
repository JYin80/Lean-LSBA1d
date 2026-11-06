import LSBA.Sampling.Fekete
import LSBA.Sampling.Primitive
import LSBA.Sampling.Bounded
import LSBA.Kernel.Weights

/-!
# Loop sampling at large coupling

Lemma 5.8 [uvc:thm:ordinary-sampling] and Corollary 7.8 [uvc:cor:weighted-sampling], (7.23)
[uvc:eq:weighted-pair-sampling], at
a fixed time: the sample set of loop words built from Fekete points on cell products, its size,
the sampling bounds for loops and loop errors with and without the weight, and the weighted
sampling input (5.34) [fo:eq:weighted-sampling-input] with the absolute constant `C_w = 2·6²`.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The sample set `𝒮_k` of Lemma 5.8 [uvc:thm:ordinary-sampling]: the union over all products
of cells of the points of Lemma 7.6 [uvc:lem:fekete] for the space of Lemma 7.5 [uvc:lem:space]. -/
def loopSampleSet (n : ℕ) (E : ℝ) (L k : ℕ) : Finset (Fin k → Fin L) :=
  (univ.filter fun a : Fin k → Fin L => ∀ j, (a j).val % n = 0).biUnion fun a =>
    (feketeSet (loopSpace n E a)).image Subtype.val

/-! ## Cells and sample points -/

/-- The first block of a cell is a multiple of `n`. -/
private lemma lemma48_cellStart_mod (n : ℕ) {L : ℕ} (x : Fin L) : (cellStart n x).val % n = 0 := by
  simp [cellStart]

/-- The first block of a cell is its own first block. -/
private lemma lemma48_cellStart_idem (n : ℕ) (hn : 1 ≤ n) {L : ℕ} (x : Fin L) :
    cellStart n (cellStart n x) = cellStart n x := by
  ext
  simp [cellStart, Nat.mul_div_cancel _ (by omega : 0 < n)]

/-- First blocks of cells and their predecessors are anchors. -/
private lemma lemma48_anchor (n : ℕ) {L : ℕ} (a : Fin L) :
    IsAnchor n (cellStart n a) ∧ IsAnchor n (cellPrev n a) := by
  refine ⟨Or.inl (lemma48_cellStart_mod n a), Or.inr ?_⟩
  unfold cellPrev
  rw [Equiv.apply_symm_apply]
  exact lemma48_cellStart_mod n a

/-- The Fekete points of the cell product of a word of first blocks lie in `𝒮_k`. -/
private lemma lemma48_mem (n : ℕ) (E : ℝ) {L k : ℕ} (a : Fin k → Fin L)
    (ha : ∀ j, (a j).val % n = 0) (s : feketeSet (loopSpace n E a)) :
    (s : CellProd n a).1 ∈ loopSampleSet n E L k := by
  unfold loopSampleSet
  rw [Finset.mem_biUnion]
  exact ⟨a, by simp [ha], Finset.mem_image_of_mem _ s.2⟩

/-- `(x + L - y) mod L` for `x, y < L`. -/
private lemma lemma48_mod {L x y : ℕ} (hx : x < L) (hy : y < L) :
    (x + L - y) % L = if y ≤ x then x - y else x + L - y := by
  split_ifs with h
  · have : x + L - y = (x - y) + L := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

/-- The triangle inequality for the cyclic distance. -/
private lemma lemma48_cycDist_tri {L : ℕ} (a b c : Fin L) :
    cycDist a c ≤ cycDist a b + cycDist b c := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  unfold cycDist
  rw [lemma48_mod ha hc, lemma48_mod hc ha, lemma48_mod ha hb, lemma48_mod hb ha,
    lemma48_mod hb hc, lemma48_mod hc hb]
  split_ifs <;> omega

/-- Two blocks of the same cell are at cyclic distance at most `n`. -/
private lemma lemma48_cycDist_cell (n : ℕ) (hn : 1 ≤ n) {L : ℕ} (x s : Fin L)
    (h : cellStart n x = cellStart n s) : cycDist x s ≤ n := by
  have hxL := x.isLt
  have hsL := s.isLt
  have h1 := Nat.div_add_mod' x.val n
  have h2 := Nat.div_add_mod' s.val n
  have h3 : x.val / n * n = s.val / n * n := congrArg Fin.val h
  have h4 : x.val % n < n := Nat.mod_lt _ (by omega)
  have h5 : s.val % n < n := Nat.mod_lt _ (by omega)
  unfold cycDist
  rw [lemma48_mod hxL hsL, lemma48_mod hsL hxL]
  split_ifs <;> omega

/-- Words in the same cell product have diameters within `2n`. -/
private lemma lemma48_wordDiam_le (n : ℕ) (hn : 1 ≤ n) {L k : ℕ} (x s : Fin k → Fin L)
    (h : ∀ j, cellStart n (s j) = cellStart n (x j)) : wordDiam x ≤ wordDiam s + 2 * n := by
  unfold wordDiam
  apply Finset.sup_le
  intro p _
  have t1 := lemma48_cycDist_tri (x p.1) (s p.1) (x p.2)
  have t2 := lemma48_cycDist_tri (s p.1) (s p.2) (x p.2)
  have c1 := lemma48_cycDist_cell n hn (x p.1) (s p.1) (h p.1).symm
  have c2 := lemma48_cycDist_cell n hn (s p.2) (x p.2) (h p.2)
  have hle : cycDist (s p.1) (s p.2) ≤
      univ.sup fun q : Fin k × Fin k => cycDist (s q.1) (s q.2) :=
    Finset.le_sup (f := fun q : Fin k × Fin k => cycDist (s q.1) (s q.2)) (Finset.mem_univ p)
  omega

/-- `|diam x - diam s| ≤ 2n` for words in the same cell product. -/
private lemma lemma48_wordDiam_abs (n : ℕ) (hn : 1 ≤ n) {L k : ℕ} (x s : Fin k → Fin L)
    (h : ∀ j, cellStart n (s j) = cellStart n (x j)) :
    |(wordDiam x : ℝ) - wordDiam s| ≤ 2 * n := by
  have h1 := lemma48_wordDiam_le n hn x s h
  have h2 := lemma48_wordDiam_le n hn s x fun j => (h j).symm
  rw [abs_sub_le_iff]
  constructor
  · have : (wordDiam x : ℝ) ≤ wordDiam s + 2 * n := by exact_mod_cast h1
    linarith
  · have : (wordDiam s : ℝ) ≤ wordDiam x + 2 * n := by exact_mod_cast h2
    linarith

/-- The diameter of a word of length two is the cyclic distance of its labels. -/
private lemma lemma48_wordDiam_pair {L : ℕ} (a b : Fin L) : wordDiam ![a, b] = cycDist a b := by
  have hself : ∀ c : Fin L, cycDist c c = 0 := fun c => by simp [cycDist]
  have hcomm : cycDist b a = cycDist a b := by unfold cycDist; exact min_comm _ _
  apply le_antisymm
  · unfold wordDiam
    apply Finset.sup_le
    rintro ⟨i, j⟩ -
    fin_cases i <;> fin_cases j <;> simp [hself, hcomm]
  · unfold wordDiam
    exact Finset.le_sup (f := fun p : Fin 2 × Fin 2 => cycDist (![a, b] p.1) (![a, b] p.2))
      (Finset.mem_univ ((0 : Fin 2), (1 : Fin 2)))

/-! ## The norming step on cell products -/

/-- Lemma 7.6 [uvc:lem:fekete] on every cell product, with weights: if on the cell product of
every word of first blocks `X = Z - F` with `Z, F` within `e` (in total) of the space of Lemma 7.5
[uvc:lem:space], the weight is at least `c > 0` and varies by a factor at most `2` inside a cell
product, then `|X|/w ≤ 2·6^k max_{𝒮_k} |X|/w + (6^k + 1) e / c`. -/
private theorem lemma48_norming (n : ℕ) (hn : 1 ≤ n) (E : ℝ) {L k : ℕ}
    (X : (Fin k → Fin L) → ℂ) (w : (Fin k → Fin L) → ℝ) (c e : ℝ) (hc : 0 < c)
    (hw : ∀ x, c ≤ w x)
    (hratio : ∀ x s : Fin k → Fin L, (∀ j, cellStart n (s j) = cellStart n (x j)) →
      w s / w x ≤ 2)
    (happ : ∀ a : Fin k → Fin L, (∀ j, (a j).val % n = 0) →
      ∃ Z Fn v v' : CellProd n a → ℂ, v ∈ loopSpace n E a ∧ v' ∈ loopSpace n E a ∧
        (∀ x, X x.1 = Z x - Fn x) ∧ ‖Z - v‖ + ‖Fn - v'‖ ≤ e) :
    ∀ x, ‖X x‖ / w x ≤
      2 * 6 ^ k * (⨆ s : loopSampleSet n E L k, ‖X s‖ / w s) + (6 ^ k + 1) * e / c := by
  intro x
  set a : Fin k → Fin L := fun j => cellStart n (x j) with ha_def
  have ha : ∀ j, (a j).val % n = 0 := fun j => lemma48_cellStart_mod n (x j)
  obtain ⟨Z, Fn, v, v', hv, hv', hX, he⟩ := happ a ha
  let x' : CellProd n a := ⟨x, fun j => (lemma48_cellStart_idem n hn (x j)).symm⟩
  obtain ⟨-, hspec⟩ := feketeSet_spec (loopSpace n E a)
  have h1 := hspec Z Fn v v' hv hv' x'
  have hw0 : ∀ y, 0 < w y := fun y => hc.trans_le (hw y)
  set Ms : ℝ := ⨆ s : loopSampleSet n E L k, ‖X s‖ / w s with hMs_def
  have hMs0 : 0 ≤ Ms := Real.iSup_nonneg fun s => div_nonneg (norm_nonneg _) (hw0 _).le
  have hMs : ∀ y (hy : y ∈ loopSampleSet n E L k), ‖X y‖ / w y ≤ Ms := fun y hy =>
    le_ciSup (f := fun s : loopSampleSet n E L k => ‖X s‖ / w s) (Set.finite_range _).bddAbove
      ⟨y, hy⟩
  have hM : (⨆ s : feketeSet (loopSpace n E a), ‖Z s - Fn s‖) ≤ 2 * Ms * w x := by
    refine Real.iSup_le (fun s => ?_) (by have := hw0 x; positivity)
    rw [← hX s.1]
    have h2 := hMs _ (lemma48_mem n E a ha s)
    have h3 := hratio x s.1.1 fun j => (s.1.2 j).trans (lemma48_cellStart_idem n hn (x j))
    have hws := hw0 s.1.1
    have hwx := hw0 x
    rw [div_le_iff₀ hws] at h2
    rw [div_le_iff₀ hwx] at h3
    nlinarith
  have hd : (Module.finrank ℂ (loopSpace n E a) : ℝ) ≤ 6 ^ k := by
    exact_mod_cast finrank_loopSpace_le n E a
  have he0 : 0 ≤ e := le_trans (by positivity) he
  have hXx : ‖X x‖ = ‖Z x' - Fn x'‖ := by rw [hX x']
  have hmain : ‖X x‖ ≤ 6 ^ k * (2 * Ms * w x) + (6 ^ k + 1) * e := by
    rw [hXx]
    refine h1.trans ?_
    have hsup0 : 0 ≤ ⨆ s : feketeSet (loopSpace n E a), ‖Z s - Fn s‖ :=
      Real.iSup_nonneg fun _ => norm_nonneg _
    have hd0 : (0 : ℝ) ≤ Module.finrank ℂ (loopSpace n E a) := Nat.cast_nonneg _
    have hwx := hw0 x
    gcongr
  have hwx : 0 < w x := hw0 x
  have hec : (6 ^ k + 1) * e ≤ (6 ^ k + 1) * e / c * w x := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    exact mul_le_mul_of_nonneg_left (hw x) (by positivity)
  rw [div_le_iff₀ hwx]
  nlinarith

/-! ## Arithmetic of the exponents -/

/-- The bound `C W^{-a} ≤ c` holds for all large `W`. -/
private lemma lemma48_ev (K a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ W : ℕ in atTop, K * (W : ℝ) ^ (-a) ≤ c := by
  have h : Tendsto (fun W : ℕ => K * (W : ℝ) ^ (-a)) atTop (𝓝 (K * 0)) :=
    ((tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop).const_mul K
  rw [mul_zero] at h
  exact h.eventually (eventually_le_nhds hc)

/-- The loop-distance bound: with `B/4 ≥ 4k + F + D + 1`, `B/2 ≥ 3C' + F + D + 1` and
`(6^k + 1)(2^{k+1} C + C') W^{-1} ≤ 1`, the error `(6^k + 1)(e_ℒ + e_𝒦) W^F` is at most `W^{-D}`. -/
private lemma lemma48_err_arith (x F D B CL CP : ℝ) (k : ℕ) (hx : 1 ≤ x) (hCL : 0 < CL)
    (hCP : 0 < CP) (hB4 : 4 * (k : ℝ) + F + D + 1 ≤ B / 4) (hB2 : 3 * CP + F + D + 1 ≤ B / 2)
    (hev : (6 ^ k + 1) * (2 ^ (k + 1) * CL + CP) * x ^ (-1 : ℝ) ≤ 1) :
    (6 ^ k + 1) * (CL * (2 * x ^ (-(B / 4))) * (1 + x ^ (4 : ℝ)) ^ k +
      CP * x ^ (-(B / 2)) * x ^ (3 * CP)) / x ^ (-F) ≤ x ^ (-D) := by
  have hx0 : 0 < x := by linarith
  have h4 : 1 ≤ x ^ (4 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hpow : (1 + x ^ (4 : ℝ)) ^ k ≤ 2 ^ k * x ^ (4 * (k : ℝ)) := by
    calc (1 + x ^ (4 : ℝ)) ^ k ≤ (2 * x ^ (4 : ℝ)) ^ k :=
          pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = 2 ^ k * x ^ (4 * (k : ℝ)) := by
          rw [mul_pow, ← Real.rpow_natCast (x ^ (4 : ℝ)), ← Real.rpow_mul hx0.le]
  have hxF : 0 < x ^ (-F) := Real.rpow_pos_of_pos hx0 _
  have e1 : x ^ (-(B / 4)) * x ^ (4 * (k : ℝ)) / x ^ (-F) ≤ x ^ (-D) * x ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_sub hx0, ← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have e2 : x ^ (-(B / 2)) * x ^ (3 * CP) / x ^ (-F) ≤ x ^ (-D) * x ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_sub hx0, ← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hB0 : 0 ≤ x ^ (-(B / 4)) := (Real.rpow_pos_of_pos hx0 _).le
  have t1 : CL * (2 * x ^ (-(B / 4))) * (1 + x ^ (4 : ℝ)) ^ k / x ^ (-F) ≤
      2 ^ (k + 1) * CL * (x ^ (-D) * x ^ (-1 : ℝ)) := by
    calc CL * (2 * x ^ (-(B / 4))) * (1 + x ^ (4 : ℝ)) ^ k / x ^ (-F)
        ≤ CL * (2 * x ^ (-(B / 4))) * (2 ^ k * x ^ (4 * (k : ℝ))) / x ^ (-F) := by
          gcongr
      _ = 2 ^ (k + 1) * CL * (x ^ (-(B / 4)) * x ^ (4 * (k : ℝ)) / x ^ (-F)) := by ring
      _ ≤ 2 ^ (k + 1) * CL * (x ^ (-D) * x ^ (-1 : ℝ)) := by gcongr
  have t2 : CP * x ^ (-(B / 2)) * x ^ (3 * CP) / x ^ (-F) ≤ CP * (x ^ (-D) * x ^ (-1 : ℝ)) := by
    calc CP * x ^ (-(B / 2)) * x ^ (3 * CP) / x ^ (-F)
        = CP * (x ^ (-(B / 2)) * x ^ (3 * CP) / x ^ (-F)) := by ring
      _ ≤ CP * (x ^ (-D) * x ^ (-1 : ℝ)) := by gcongr
  have hD0 : 0 ≤ x ^ (-D) := (Real.rpow_pos_of_pos hx0 _).le
  calc (6 ^ k + 1) * (CL * (2 * x ^ (-(B / 4))) * (1 + x ^ (4 : ℝ)) ^ k +
        CP * x ^ (-(B / 2)) * x ^ (3 * CP)) / x ^ (-F)
      = (6 ^ k + 1) * (CL * (2 * x ^ (-(B / 4))) * (1 + x ^ (4 : ℝ)) ^ k / x ^ (-F) +
          CP * x ^ (-(B / 2)) * x ^ (3 * CP) / x ^ (-F)) := by ring
    _ ≤ (6 ^ k + 1) * (2 ^ (k + 1) * CL * (x ^ (-D) * x ^ (-1 : ℝ)) +
          CP * (x ^ (-D) * x ^ (-1 : ℝ))) := by gcongr
    _ = ((6 ^ k + 1) * (2 ^ (k + 1) * CL + CP) * x ^ (-1 : ℝ)) * x ^ (-D) := by ring
    _ ≤ 1 * x ^ (-D) := by gcongr
    _ = x ^ (-D) := one_mul _

/-- The anchor-envelope bound: with `p = 2(B + C) + D' + 1`, at most `36 W^{2(B+C)}` anchor pairs,
`g²η ≥ (C_χ W³)^{-1}` and `72 C_m C_χ^p W^{-1} ≤ 1`, the union of the Markov bounds
`C_m (g²η)^{-p} W^{-4p}` is at most `W^{-D'}/2`. -/
private lemma lemma48_env_arith (x B C D' Cm Cχ p N y : ℝ) (hx : 1 ≤ x)
    (hp : p = 2 * (B + C) + D' + 1) (hp0 : 0 < p) (hCm : 0 < Cm) (hCχ : 0 < Cχ)
    (hN : N ≤ 36 * x ^ (2 * (B + C))) (hy : 0 < y)
    (hy' : (Cχ * x ^ (3 : ℝ))⁻¹ ≤ y) (hev : 72 * Cm * Cχ ^ p * x ^ (-1 : ℝ) ≤ 1) :
    N * (Cm * y ^ (-p) / (x ^ (4 : ℝ)) ^ p) ≤ x ^ (-D') / 2 := by
  have hx0 : 0 < x := by linarith
  have ha : 0 < Cχ * x ^ (3 : ℝ) := by positivity
  have hyp : y ^ (-p) ≤ Cχ ^ p * x ^ (3 * p) := by
    calc y ^ (-p) ≤ ((Cχ * x ^ (3 : ℝ))⁻¹) ^ (-p) :=
          Real.rpow_le_rpow_of_nonpos (inv_pos.mpr ha) hy' (by linarith)
      _ = (Cχ * x ^ (3 : ℝ)) ^ p := by
          rw [Real.inv_rpow ha.le, Real.rpow_neg ha.le, inv_inv]
      _ = Cχ ^ p * x ^ (3 * p) := by
          rw [Real.mul_rpow hCχ.le (by positivity), ← Real.rpow_mul hx0.le]
  have h4 : (x ^ (4 : ℝ)) ^ p = x ^ (4 * p) := by rw [← Real.rpow_mul hx0.le]
  have hexp : x ^ (2 * (B + C)) * x ^ (3 * p) / x ^ (4 * p) = x ^ (-D') * x ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_sub hx0, ← Real.rpow_add hx0]
    congr 1
    rw [hp]
    ring
  have h4p : 0 < x ^ (4 * p) := Real.rpow_pos_of_pos hx0 _
  have hD : 0 ≤ x ^ (-D') := (Real.rpow_pos_of_pos hx0 _).le
  rw [h4]
  calc N * (Cm * y ^ (-p) / x ^ (4 * p))
      ≤ (36 * x ^ (2 * (B + C))) * (Cm * (Cχ ^ p * x ^ (3 * p)) / x ^ (4 * p)) := by
        gcongr
    _ = (36 * Cm * Cχ ^ p) * (x ^ (2 * (B + C)) * x ^ (3 * p) / x ^ (4 * p)) := by ring
    _ = (72 * Cm * Cχ ^ p * x ^ (-1 : ℝ)) * (x ^ (-D') / 2) := by rw [hexp]; ring
    _ ≤ 1 * (x ^ (-D') / 2) := by gcongr
    _ = x ^ (-D') / 2 := one_mul _

/-- Markov's inequality for the `p`-th moment: `P(t ≤ f) ≤ K t^{-p}` when `E f^p ≤ K`. -/
private lemma lemma48_markov {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsFiniteMeasure P] (f : Ω' → ℝ) (p t K : ℝ) (hp : 0 < p) (ht : 0 < t)
    (hf : Integrable (fun ω => f ω ^ p) P) (hf0 : ∀ ω, 0 ≤ f ω) (hK : ∫ ω, f ω ^ p ∂P ≤ K) :
    P {ω | t ≤ f ω} ≤ ENNReal.ofReal (K / t ^ p) := by
  have htp : 0 < t ^ p := Real.rpow_pos_of_pos ht p
  have hsub : {ω | t ≤ f ω} ⊆ {ω | t ^ p ≤ f ω ^ p} := fun ω hω =>
    Real.rpow_le_rpow ht.le hω hp.le
  have hM := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hf0 ω) p) hf (t ^ p)
  refine (measure_mono hsub).trans ?_
  have hK0 : 0 ≤ K := (integral_nonneg fun ω => Real.rpow_nonneg (hf0 ω) p).trans hK
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity), le_div_iff₀ htp]
  rw [measureReal_def] at hM
  nlinarith

/-- Hermitian GUE blocks stay Hermitian under real scaling. -/
private lemma lemma48_herm (W L : ℕ) (ω : Ω W L) (b : ℝ) (r : Fin L) :
    (((b : ℝ) : ℂ) • gueBlock W L ω r).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, (gueBlock_isHermitian W L ω r).eq, Complex.star_def,
    Complex.conj_ofReal]

/-- `W^{1-k} W^{k-1} = 1` and `|W^{1-k}| ≤ 1` for `W, k ≥ 1`. -/
private lemma lemma48_zpow (W : ℕ) (hW : 1 ≤ W) (k : ℕ) (hk : 1 ≤ k) :
    (W : ℂ) ^ (1 - (k : ℤ)) * (W : ℂ) ^ (k - 1) = 1 ∧ ‖(W : ℂ) ^ (1 - (k : ℤ))‖ ≤ 1 := by
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast (by omega : W ≠ 0)
  constructor
  · rw [← zpow_natCast, ← zpow_add₀ hW0]
    have : (1 - (k : ℤ)) + ((k - 1 : ℕ) : ℤ) = 0 := by omega
    rw [this, zpow_zero]
  · rw [norm_zpow, Complex.norm_natCast]
    exact zpow_le_one_of_nonpos₀ (by exact_mod_cast hW) (by omega)

/-- `ℓ_v(g) ≥ g²` for `g ≥ 1`, `L ≥ g²` and `0 ≤ v < 1`, (5.18) [fo:eq:scale]. -/
private lemma lemma48_ellProp (g : ℝ) (hg : 1 ≤ g) (L : ℕ) (hL : g ^ 2 ≤ L) (v : ℝ) (hv0 : 0 ≤ v)
    (hv : v < 1) : g ^ 2 ≤ ellProp g L v := by
  unfold ellProp
  have hγ : gammaG g = (g ^ 2)⁻¹ := by unfold gammaG; rw [max_eq_right hg]
  rw [hγ]
  refine le_min hL ?_
  have hg0 : 0 < g := by linarith
  have h1v : 0 < 1 - v := by linarith
  have hs0 : 0 < Real.sqrt ((g ^ 2)⁻¹ * (1 - v)) := Real.sqrt_pos.mpr (by positivity)
  have hs : Real.sqrt ((g ^ 2)⁻¹ * (1 - v)) ≤ g⁻¹ := by
    rw [show g⁻¹ = Real.sqrt ((g ^ 2)⁻¹) by rw [Real.sqrt_inv, Real.sqrt_sq hg0.le]]
    exact Real.sqrt_le_sqrt (mul_le_of_le_one_right (by positivity) (by linarith))
  have h1 : g / g⁻¹ ≤ g / Real.sqrt ((g ^ 2)⁻¹ * (1 - v)) :=
    div_le_div_of_nonneg_left hg0.le hs0 hs
  have h2 : g / g⁻¹ = g ^ 2 := by field_simp
  linarith

/-- The weight of Lemma 6.2 [da:lem:scale-budgets] is at least `W^{-F}`. -/
private lemma lemma48_weight_ge (cw θ F : ℝ) (W : ℕ) (ℓ r : ℝ) :
    (W : ℝ) ^ (-F) ≤ weightFn cw θ F W ℓ r := by
  unfold weightFn
  linarith [Real.exp_pos (-(cw * (r / ℓ) ^ θ))]

/-- A sampling bound on words of length two gives the same bound on pairs, with the sample set
of the pairs `(s₀, s₁)`. -/
private lemma lemma48_pair {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') {L : ℕ}
    (X : (Fin 2 → Fin L) → Ω' → ℂ) (w : (Fin 2 → Fin L) → ℝ) (hw : ∀ a, 0 < w a)
    (X₂ : Fin L × Fin L → Ω' → ℂ) (w₂ : Fin L × Fin L → ℝ)
    (hX : ∀ ab ω, X₂ ab ω = X ![ab.1, ab.2] ω) (hw₂ : ∀ ab, w₂ ab = w ![ab.1, ab.2])
    (S : Finset (Fin 2 → Fin L)) (Cs δ η : ℝ) (hCs : 0 ≤ Cs) (h : SampleBound P X w S Cs δ η) :
    SampleBound P X₂ w₂ (S.image fun s => (s 0, s 1)) Cs δ η := by
  unfold SampleBound at *
  refine (measure_mono ?_).trans h
  rintro ω ⟨ab, hab⟩
  refine ⟨![ab.1, ab.2], ?_⟩
  have hfin : ∀ s : Fin 2 → Fin L, ![s 0, s 1] = s := fun s => by
    ext i; fin_cases i <;> rfl
  have hsup : (⨆ s : S, ‖X s ω‖ / w s) ≤
      ⨆ t : (S.image fun s => (s 0, s 1)), ‖X₂ t ω‖ / w₂ t := by
    refine Real.iSup_le (fun s => ?_) (Real.iSup_nonneg fun t => by
      rw [hw₂]; exact div_nonneg (norm_nonneg _) (hw _).le)
    have hmem : ((s : Fin 2 → Fin L) 0, (s : Fin 2 → Fin L) 1) ∈ S.image fun s => (s 0, s 1) :=
      Finset.mem_image_of_mem _ s.2
    calc ‖X s ω‖ / w s = ‖X₂ ((s : Fin 2 → Fin L) 0, (s : Fin 2 → Fin L) 1) ω‖ /
          w₂ ((s : Fin 2 → Fin L) 0, (s : Fin 2 → Fin L) 1) := by
          simp only [hX, hw₂, hfin]
      _ ≤ _ := le_ciSup (f := fun t : (S.image fun s => (s 0, s 1)) => ‖X₂ t ω‖ / w₂ t)
          (Set.finite_range _).bddAbove ⟨_, hmem⟩
  have e1 := hX ab ω
  have e2 := hw₂ ab
  rw [e1, e2] at hab
  have := mul_le_mul_of_nonneg_left hsup hCs
  linarith

/-- With `g² ≥ W^B` and `L ≤ g² W^C`, `L/n + 1 ≤ 3 W^{B+C}`. -/
private lemma lemma48_cells (g B C : ℝ) (W L : ℕ) (hW : 1 ≤ W) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hg : (W : ℝ) ^ B ≤ g ^ 2) (hL : (L : ℝ) ≤ g ^ 2 * (W : ℝ) ^ C) :
    (L : ℝ) / cellLen g W B + 1 ≤ 3 * (W : ℝ) ^ (B + C) := by
  have hx0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  obtain ⟨hlo, -⟩ := cellLen_bounds g B W hW hg
  have hWB : 0 < (W : ℝ) ^ B := Real.rpow_pos_of_pos hx0 B
  have hg2 : 0 < g ^ 2 := lt_of_lt_of_le hWB hg
  have hy : 0 < g ^ 2 * (W : ℝ) ^ (-B) / 2 := by
    have := Real.rpow_pos_of_pos hx0 (-B); positivity
  have hn : (0 : ℝ) < cellLen g W B := lt_of_lt_of_le hy hlo
  have h1 : (L : ℝ) / cellLen g W B ≤ 2 * (W : ℝ) ^ (B + C) := by
    rw [div_le_iff₀ hn]
    have e : (W : ℝ) ^ (B + C) * (W : ℝ) ^ (-B) = (W : ℝ) ^ C := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    have hWBC : 0 ≤ (W : ℝ) ^ (B + C) := (Real.rpow_pos_of_pos hx0 _).le
    calc (L : ℝ) ≤ g ^ 2 * (W : ℝ) ^ C := hL
      _ = 2 * (W : ℝ) ^ (B + C) * (g ^ 2 * (W : ℝ) ^ (-B) / 2) := by rw [← e]; ring
      _ ≤ 2 * (W : ℝ) ^ (B + C) * cellLen g W B := by gcongr
  have h2 : (1 : ℝ) ≤ (W : ℝ) ^ (B + C) := Real.one_le_rpow (by exact_mod_cast hW) (by linarith)
  linarith

/-- `|𝒮_k| ≤ 6^k (L/n + 1)^k`. -/
theorem card_loopSampleSet_le (n : ℕ) (hn : 1 ≤ n) (E : ℝ) (L k : ℕ) :
    ((loopSampleSet n E L k).card : ℝ) ≤ 6 ^ k * ((L : ℝ) / n + 1) ^ k := by
  set starts := univ.filter fun b : Fin L => b.val % n = 0 with hstarts
  have hfilt : (univ.filter fun a : Fin k → Fin L => ∀ j, (a j).val % n = 0) =
      Fintype.piFinset fun _ => starts := by
    ext a
    simp [Fintype.mem_piFinset, starts]
  have h2 : ∀ a : Fin k → Fin L,
      ((feketeSet (loopSpace n E a)).image Subtype.val).card ≤ 6 ^ k := fun a =>
    Finset.card_image_le.trans ((feketeSet_spec _).1.trans (finrank_loopSpace_le n E a))
  have h3 : (loopSampleSet n E L k).card ≤ starts.card ^ k * 6 ^ k := by
    unfold loopSampleSet
    refine Finset.card_biUnion_le.trans ((Finset.sum_le_sum fun a _ => h2 a).trans ?_)
    rw [Finset.sum_const, smul_eq_mul, hfilt, Fintype.card_piFinset, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have h4 := card_cellStarts_le n L hn
  calc ((loopSampleSet n E L k).card : ℝ) ≤ ((starts.card ^ k * 6 ^ k : ℕ) : ℝ) := by
        exact_mod_cast h3
    _ = 6 ^ k * (starts.card : ℝ) ^ k := by push_cast; ring
    _ ≤ 6 ^ k * ((L : ℝ) / n + 1) ^ k := by gcongr

/-- Lemma 5.8 [uvc:thm:ordinary-sampling] and Corollary 7.8 [uvc:cor:weighted-sampling] at a fixed
time `u ≤ 1 - W^{-3}`, for `g² ≥ W^B`: the loops and the loop errors satisfy (5.26)
[fo:eq:spatial-sampling] and its weighted form (7.23) [uvc:eq:weighted-pair-sampling] (weights
`e^{-c(diam/ℓ)^θ} + W^{-F}` with any `ℓ ≥ g²`), with the time- and sign-independent sample set
`𝒮_k` and the constant `2 d_k`, `d_k = 6^k`. -/
theorem loop_sampling (κ C : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hC : 1 < C) (k : ℕ) (hk : 1 ≤ k)
    (cw θ F D D' : ℝ) (hcw : 0 < cw) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2) (hF : 0 < F) (hD : 0 < D)
    (hD' : 0 < D') :
    ∃ B Cκ : ℝ, 2 < B ∧ 1 ≤ Cκ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ (g : ℝ) (L : ℕ) (E : ℝ),
      Cκ ≤ g → (W : ℝ) ^ B ≤ g ^ 2 → 4 * g ^ 2 ≤ L → (L : ℝ) ≤ g ^ 2 * (W : ℝ) ^ C →
      |E| ≤ 2 - κ → IsDysonRootV (hopB g) (gammaG g) L E (mRoot g L E) →
      ‖mRoot g L E‖ ≤ C → C⁻¹ ≤ (mRoot g L E).im →
      ∀ (σ : Fin k → Bool) (u : ℝ), 0 ≤ u → (W : ℝ) ^ (-3 : ℝ) ≤ 1 - u →
        SampleBound (μ W L) (fun a ω => loopTr (flowG W ⟨g, E, L, u⟩ ω) a σ) (fun _ => 1)
          (loopSampleSet (cellLen g W B) E L k) (2 * 6 ^ k) ((W : ℝ) ^ (-D))
          ((W : ℝ) ^ (-D')) ∧
        SampleBound (μ W L) (fun a ω => flowErr W ⟨g, E, L, u⟩ a σ ω) (fun _ => 1)
          (loopSampleSet (cellLen g W B) E L k) (2 * 6 ^ k) ((W : ℝ) ^ (-D))
          ((W : ℝ) ^ (-D')) ∧
        ∀ ℓ : ℝ, g ^ 2 ≤ ℓ →
          SampleBound (μ W L) (fun a ω => loopTr (flowG W ⟨g, E, L, u⟩ ω) a σ)
            (fun a => weightFn cw θ F W ℓ (wordDiam a)) (loopSampleSet (cellLen g W B) E L k)
            (2 * 6 ^ k) ((W : ℝ) ^ (-D)) ((W : ℝ) ^ (-D')) ∧
          SampleBound (μ W L) (fun a ω => flowErr W ⟨g, E, L, u⟩ a σ ω)
            (fun a => weightFn cw θ F W ℓ (wordDiam a)) (loopSampleSet (cellLen g W B) E L k)
            (2 * 6 ^ k) ((W : ℝ) ^ (-D)) ((W : ℝ) ^ (-D')) := by
  obtain ⟨Cκχ, Cχ, hCκχ, hCχ, Hχ⟩ := char_large κ C hκ hκ2 hC.le
  obtain ⟨Cδ, hCδ, Hδ⟩ := cellClose_perturb κ hκ hκ2
  obtain ⟨CL, hCL, HL⟩ := loopTr_dist_space κ hκ hκ2 k hk
  obtain ⟨CκP, c₀, CP, hCκP, hc₀, hCP, HP⟩ := primLoopF_dist_space κ C hκ hκ2 hC.le k hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set B : ℝ := 4 * (4 * (k : ℝ) + F + D + 1) + 2 * (3 * CP + F + D + 1) with hBdef
  have hB2 : 2 < B := by rw [hBdef]; nlinarith
  have hB0 : 0 ≤ B := by linarith
  have hB4 : 4 * (k : ℝ) + F + D + 1 ≤ B / 4 := by rw [hBdef]; nlinarith
  have hB2' : 3 * CP + F + D + 1 ≤ B / 2 := by rw [hBdef]; nlinarith
  set Cκ : ℝ := max (max Cκχ CκP) (2 / Real.sqrt (κ / 2)) with hCκdef
  have hCκχ' : Cκχ ≤ Cκ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCκP' : CκP ≤ Cκ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCκr : 2 / Real.sqrt (κ / 2) ≤ Cκ := le_max_right _ _
  have hCκ1 : 1 ≤ Cκ := hCκχ.trans hCκχ'
  refine ⟨B, Cκ, hB2, hCκ1, ?_⟩
  set p : ℝ := 2 * (B + C) + D' + 1 with hpdef
  have hp : 0 < p := by rw [hpdef]; linarith
  obtain ⟨Cm, hCm, Hm⟩ := resolvent_moments (κ / 2) p Cχ (by linarith) hp (by linarith)
  obtain ⟨W₁, H₁⟩ := cells_prefix κ B C (D' + 1) hκ hκ2 hB2 (by linarith) (by linarith)
  have hev : ∀ᶠ W : ℕ in atTop, ((2 ≤ W ∧ W₁ ≤ W) ∧ 4 * p ≤ (W : ℝ)) ∧
      (Cχ * (W : ℝ) ^ (-B) ≤ 1 ∧ Cδ * Cχ * (W : ℝ) ^ (-(3 * B / 4)) ≤ 1 ∧
        2 * (W : ℝ) ^ (-(B / 4)) ≤ 1 ∧ 1 * (W : ℝ) ^ (-B) ≤ c₀) ∧
      (72 * Cm * Cχ ^ p * (W : ℝ) ^ (-1 : ℝ) ≤ 1 ∧
        (6 ^ k + 1) * (2 ^ (k + 1) * CL + CP) * (W : ℝ) ^ (-1 : ℝ) ≤ 1 ∧
        2 * cw * (W : ℝ) ^ (-(B * θ)) ≤ Real.log 2) :=
    (((eventually_ge_atTop 2).and (eventually_ge_atTop W₁)).and
      (tendsto_natCast_atTop_atTop.eventually_ge_atTop (4 * p))).and
    (((lemma48_ev Cχ B 1 (by linarith) one_pos).and
      ((lemma48_ev (Cδ * Cχ) (3 * B / 4) 1 (by linarith) one_pos).and
      ((lemma48_ev 2 (B / 4) 1 (by linarith) one_pos).and
      (lemma48_ev 1 B c₀ (by linarith) hc₀)))).and
    ((lemma48_ev (72 * Cm * Cχ ^ p) 1 1 one_pos one_pos).and
      ((lemma48_ev ((6 ^ k + 1) * (2 ^ (k + 1) * CL + CP)) 1 1 one_pos one_pos).and
      (lemma48_ev (2 * cw) (B * θ) (Real.log 2) (by positivity)
        (Real.log_pos (by norm_num))))))
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp hev
  refine ⟨W₀, fun W hW g L E hgC hWB h4L hLC hE hroot hmC hmim σ u hu0 hu1 => ?_⟩
  obtain ⟨⟨⟨hW2, hW₁⟩, hW4p⟩, ⟨hE4, hE5, hE6, hE7⟩, ⟨hE8, hE9, hE10⟩⟩ := hW₀ W hW
  have hW1 : 1 ≤ W := by omega
  have hx0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hx1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hx2 : (2 : ℝ) ≤ W := by exact_mod_cast hW2
  have hg1 : 1 ≤ g := hCκ1.trans hgC
  have hg0 : 0 < g := by linarith
  have hgg : 0 < g ^ 2 := by positivity
  have hγ : gammaG g = (g ^ 2)⁻¹ := by unfold gammaG; rw [max_eq_right hg1]
  have hW3 : 0 < (W : ℝ) ^ (-3 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hu1' : u < 1 := by linarith
  have hWB0 : 0 < (W : ℝ) ^ (-B) := Real.rpow_pos_of_pos hx0 _
  have hWB4 : 0 < (W : ℝ) ^ (-(B / 4)) := Real.rpow_pos_of_pos hx0 _
  set m : ℂ := mRoot g L E with hmdef
  obtain ⟨hre, hzE, hη0, hηC, hgη⟩ := Hχ g (hCκχ'.trans hgC) E m hE hmC hmim u hu0 hu1'
  set z : ℂ := zChar g E m u with hzdef
  set η : ℝ := etaChar g m u with hηdef
  have hzim : z.im = η := by simp [hzdef, hηdef, zChar, etaChar]
  set n : ℕ := cellLen g W B with hndef
  obtain ⟨-, hnhi⟩ := cellLen_bounds g B W hW1 hWB
  have hn1 : 1 ≤ n := le_max_left _ _
  have hL3 : 3 ≤ L := by
    have h1 : (1 : ℝ) ≤ g ^ 2 := one_le_pow₀ hg1
    have : (3 : ℝ) ≤ L := by linarith
    exact_mod_cast this
  -- the random potential and the Green function
  set s : ℝ := u * gammaG g with hsdef
  let V : Ω W L → Fin L → Matrix (Fin W) (Fin W) ℂ := fun ω r =>
    ((Real.sqrt s : ℝ) : ℂ) • gueBlock W L ω r
  have hV : ∀ ω r, (V ω r).IsHermitian := fun ω r => lemma48_herm W L ω _ r
  have hG : ∀ ω, flowG W ⟨g, E, L, u⟩ ω =
      resolventMat (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp (V ω)) z := by
    intro ω
    change resolventMat (flowH g W L u ω) z = _
    rw [flowH_cycle g hg1]
  -- the bad events
  set A₁ : Set (Ω W L) :=
    {ω | ¬ CellClose n E (E : ℂ) (V ω) ((W : ℝ) ^ (-(B / 4)))} with hA₁
  have hμA₁ : μ W L A₁ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D' + 1))) :=
    H₁ W hW₁ g L E s hWB hLC hE (mul_nonneg hu0 (by rw [hγ]; positivity))
      (by rw [hsdef, hγ, mul_assoc, inv_mul_cancel₀ hgg.ne', mul_one]; exact hu1'.le)
  set anc : Finset (Fin L) := univ.filter fun α : Fin L => IsAnchor n α with hanc
  set T : ℝ := (W : ℝ) ^ (4 : ℝ) with hT
  have hT0 : 0 < T := Real.rpow_pos_of_pos hx0 _
  open scoped Matrix.Norms.L2Operator in
  set A₂ : Set (Ω W L) := ⋃ ab ∈ anc ×ˢ anc,
    {ω | T ≤ ‖blockOf (flowG W ⟨g, E, L, u⟩ ω) ab.1 ab.2‖} with hA₂
  have hzri : ((z.re : ℝ) : ℂ) + ((η : ℝ) : ℂ) * Complex.I = z := by
    apply Complex.ext <;> simp [hzim]
  open scoped Matrix.Norms.L2Operator in
  have hμA₂ : μ W L A₂ ≤ ENNReal.ofReal ((W : ℝ) ^ (-D') / 2) := by
    have hone : ∀ ab : Fin L × Fin L,
        μ W L {ω | T ≤ ‖blockOf (flowG W ⟨g, E, L, u⟩ ω) ab.1 ab.2‖} ≤
          ENNReal.ofReal (Cm * (g ^ 2 * η) ^ (-p) / T ^ p) := by
      intro ab
      obtain ⟨hint, hbd⟩ := Hm W hW4p L g (hCκr.trans hgC) h4L z.re η u hre hη0 hηC hu0
        hu1'.le ab.1 ab.2
      have hfun : (fun ω => ‖blockOf (resolventMat (blockFlow W L
          (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) (u * gammaG g) ω)
          (((z.re : ℝ) : ℂ) + ((η : ℝ) : ℂ) * Complex.I)) ab.1 ab.2‖ ^ p) =
          fun ω => ‖blockOf (flowG W ⟨g, E, L, u⟩ ω) ab.1 ab.2‖ ^ p := by
        funext ω
        rw [hzri]
        rfl
      rw [hfun] at hint hbd
      exact lemma48_markov _ _ p T _ hp hT0 hint (fun _ => norm_nonneg _) hbd
    have hcard : (((anc ×ˢ anc).card : ℕ) : ℝ) ≤ 36 * (W : ℝ) ^ (2 * (B + C)) := by
      have h6 := (card_cells_le_pow g B C W L hW1 hB0 (by linarith) hWB hLC).2
      rw [Finset.card_product, Nat.cast_mul]
      have hpow : ((W : ℝ) ^ (B + C)) ^ 2 = (W : ℝ) ^ (2 * (B + C)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; ring_nf
      have hc0 : (0 : ℝ) ≤ anc.card := Nat.cast_nonneg _
      calc (anc.card : ℝ) * anc.card ≤ (6 * (W : ℝ) ^ (B + C)) * (6 * (W : ℝ) ^ (B + C)) :=
            mul_le_mul h6 h6 hc0 (hc0.trans h6)
        _ = 36 * ((W : ℝ) ^ (B + C)) ^ 2 := by ring
        _ = 36 * (W : ℝ) ^ (2 * (B + C)) := by rw [hpow]
    have hy' : (Cχ * (W : ℝ) ^ (3 : ℝ))⁻¹ ≤ g ^ 2 * η := by
      rw [mul_inv, ← Real.rpow_neg hx0.le]
      calc Cχ⁻¹ * (W : ℝ) ^ (-3 : ℝ) ≤ Cχ⁻¹ * (1 - u) :=
            mul_le_mul_of_nonneg_left hu1 (by positivity)
        _ = (1 - u) / Cχ := by ring
        _ ≤ g ^ 2 * η := hgη
    have harith := lemma48_env_arith W B C D' Cm Cχ p (((anc ×ˢ anc).card : ℕ) : ℝ) (g ^ 2 * η)
      hx1 hpdef hp hCm (by linarith) hcard (mul_pos hgg hη0) hy' hE8
    calc μ W L A₂ ≤ ∑ ab ∈ anc ×ˢ anc,
          μ W L {ω | T ≤ ‖blockOf (flowG W ⟨g, E, L, u⟩ ω) ab.1 ab.2‖} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ ab ∈ anc ×ˢ anc, ENNReal.ofReal (Cm * (g ^ 2 * η) ^ (-p) / T ^ p) :=
          Finset.sum_le_sum fun ab _ => hone ab
      _ = ENNReal.ofReal ((((anc ×ˢ anc).card : ℕ) : ℝ) * (Cm * (g ^ 2 * η) ^ (-p) / T ^ p)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-D') / 2) := ENNReal.ofReal_le_ofReal harith
  have hμ : μ W L (A₁ ∪ A₂) ≤ ENNReal.ofReal ((W : ℝ) ^ (-D')) := by
    have h1 : (W : ℝ) ^ (-(D' + 1)) ≤ (W : ℝ) ^ (-D') / 2 := by
      rw [show -(D' + 1) = -D' + (-1) by ring, Real.rpow_add hx0, Real.rpow_neg_one]
      have : (W : ℝ)⁻¹ ≤ 1 / 2 := by
        rw [inv_eq_one_div]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx2
      have hD0 : 0 ≤ (W : ℝ) ^ (-D') := (Real.rpow_pos_of_pos hx0 _).le
      calc (W : ℝ) ^ (-D') * (W : ℝ)⁻¹ ≤ (W : ℝ) ^ (-D') * (1 / 2) :=
            mul_le_mul_of_nonneg_left this hD0
        _ = (W : ℝ) ^ (-D') / 2 := by ring
    calc μ W L (A₁ ∪ A₂) ≤ μ W L A₁ + μ W L A₂ := measure_union_le _ _
      _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D' + 1))) + ENNReal.ofReal ((W : ℝ) ^ (-D') / 2) :=
          add_le_add hμA₁ hμA₂
      _ = ENNReal.ofReal ((W : ℝ) ^ (-(D' + 1)) + (W : ℝ) ^ (-D') / 2) :=
          (ENNReal.ofReal_add (Real.rpow_pos_of_pos hx0 _).le
            (by have := Real.rpow_pos_of_pos hx0 (-D'); positivity)).symm
      _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-D')) := ENNReal.ofReal_le_ofReal (by linarith)
  -- the deterministic errors
  set eL : ℝ := CL * (2 * (W : ℝ) ^ (-(B / 4))) * (1 + T) ^ k with heL
  set eP : ℝ := CP * (W : ℝ) ^ (-(B / 2)) * (W : ℝ) ^ (3 * CP) with heP
  have heL0 : 0 ≤ eL := by rw [heL]; positivity
  have heP0 : 0 ≤ eP := by
    rw [heP]
    have := Real.rpow_pos_of_pos hx0 (-(B / 2))
    have := Real.rpow_pos_of_pos hx0 (3 * CP)
    positivity
  have herr : (6 ^ k + 1) * (eL + eP) / (W : ℝ) ^ (-F) ≤ (W : ℝ) ^ (-D) :=
    lemma48_err_arith W F D B CL CP k hx1 hCL hCP hB4 hB2' hE9
  have hWF : 0 < (W : ℝ) ^ (-F) := Real.rpow_pos_of_pos hx0 _
  have herrL : (6 ^ k + 1) * eL / (W : ℝ) ^ (-F) ≤ (W : ℝ) ^ (-D) := by
    refine le_trans ?_ herr
    gcongr
    linarith
  obtain ⟨hc1, hcle⟩ := lemma48_zpow W hW1 k hk
  have hconj : ‖starRingEnd ℂ z - (E : ℂ)‖ = ‖z - (E : ℂ)‖ := by
    have : starRingEnd ℂ z - (E : ℂ) = starRingEnd ℂ (z - (E : ℂ)) := by
      rw [map_sub, Complex.conj_ofReal]
    rw [this, Complex.norm_conj]
  have hnz : (n : ℝ) * ‖z - (E : ℂ)‖ ≤ Cχ * (W : ℝ) ^ (-B) := by
    calc (n : ℝ) * ‖z - (E : ℂ)‖ ≤ (g ^ 2 * (W : ℝ) ^ (-B)) * (Cχ / g ^ 2) :=
          mul_le_mul hnhi hzE (norm_nonneg _) (by positivity)
      _ = Cχ * (W : ℝ) ^ (-B) := by field_simp
  have hδB : Cδ * n * ‖z - (E : ℂ)‖ ≤ (W : ℝ) ^ (-(B / 4)) := by
    have hsplit : (W : ℝ) ^ (-B) = (W : ℝ) ^ (-(3 * B / 4)) * (W : ℝ) ^ (-(B / 4)) := by
      rw [← Real.rpow_add hx0]; ring_nf
    calc Cδ * n * ‖z - (E : ℂ)‖ = Cδ * ((n : ℝ) * ‖z - (E : ℂ)‖) := by ring
      _ ≤ Cδ * (Cχ * (W : ℝ) ^ (-B)) := mul_le_mul_of_nonneg_left hnz hCδ.le
      _ = (Cδ * Cχ * (W : ℝ) ^ (-(3 * B / 4))) * (W : ℝ) ^ (-(B / 4)) := by rw [hsplit]; ring
      _ ≤ 1 * (W : ℝ) ^ (-(B / 4)) := by gcongr
      _ = (W : ℝ) ^ (-(B / 4)) := one_mul _
  have hnc₀ : (n : ℝ) ≤ c₀ * g ^ 2 := by
    calc (n : ℝ) ≤ g ^ 2 * (W : ℝ) ^ (-B) := hnhi
      _ ≤ g ^ 2 * c₀ := by gcongr; linarith
      _ = c₀ * g ^ 2 := by ring
  have hsq : Real.sqrt ((n : ℝ) / g ^ 2) ≤ (W : ℝ) ^ (-(B / 2)) := by
    have h1 : (n : ℝ) / g ^ 2 ≤ (W : ℝ) ^ (-B) := by
      rw [div_le_iff₀ hgg]; linarith
    calc Real.sqrt ((n : ℝ) / g ^ 2) ≤ Real.sqrt ((W : ℝ) ^ (-B)) := Real.sqrt_le_sqrt h1
      _ = (W : ℝ) ^ (-(B / 2)) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]; ring_nf
  have hut : (1 - u) ^ (-CP) ≤ (W : ℝ) ^ (3 * CP) := by
    calc (1 - u) ^ (-CP) ≤ ((W : ℝ) ^ (-3 : ℝ)) ^ (-CP) :=
          Real.rpow_le_rpow_of_nonpos hW3 hu1 (by linarith)
      _ = (W : ℝ) ^ (3 * CP) := by rw [← Real.rpow_mul hx0.le]; ring_nf
  have hgood : ∀ ω, ω ∉ A₁ ∪ A₂ → ∀ a : Fin k → Fin L, (∀ j, (a j).val % n = 0) →
      ∃ vL vP : CellProd n a → ℂ, vL ∈ loopSpace n E a ∧ vP ∈ loopSpace n E a ∧
        ‖(fun x : CellProd n a => loopTr (flowG W ⟨g, E, L, u⟩ ω) x.1 σ) - vL‖ ≤ eL ∧
        ‖(fun x : CellProd n a => primLoop g W L E m u x.1 σ) - vP‖ ≤ eP := by
    intro ω hω a _
    have hω1 : ω ∉ A₁ := fun h => hω (Or.inl h)
    have hω2 : ω ∉ A₂ := fun h => hω (Or.inr h)
    have hcl0 : CellClose n E (E : ℂ) (V ω) ((W : ℝ) ^ (-(B / 4))) := not_not.mp hω1
    have hε1 : (W : ℝ) ^ (-(B / 4)) ≤ 1 := by linarith
    have hnz1 : (n : ℝ) * ‖z - (E : ℂ)‖ ≤ 1 := hnz.trans hE4
    have hcl := Hδ W L n E _ z (V ω) hE hWB4.le hε1 hnz1 hcl0
    have hcl' := Hδ W L n E _ (starRingEnd ℂ z) (V ω) hE hWB4.le hε1 (by rwa [hconj]) hcl0
    rw [hconj] at hcl'
    have hε₁ : (W : ℝ) ^ (-(B / 4)) + Cδ * n * ‖z - (E : ℂ)‖ ≤ 2 * (W : ℝ) ^ (-(B / 4)) := by
      linarith
    have hε₁0 : 0 ≤ (W : ℝ) ^ (-(B / 4)) + Cδ * n * ‖z - (E : ℂ)‖ := by positivity
    have hε₁1 : (W : ℝ) ^ (-(B / 4)) + Cδ * n * ‖z - (E : ℂ)‖ ≤ 1 := by linarith
    have hzim0 : z.im ≠ 0 := by rw [hzim]; exact hη0.ne'
    open scoped Matrix.Norms.L2Operator in
    have hlt : ∀ α β : Fin L, IsAnchor n α → IsAnchor n β →
        ‖blockOf (flowG W ⟨g, E, L, u⟩ ω) α β‖ ≤ T := by
      intro α β hα hβ
      by_contra hcon
      exact hω2 (Set.mem_iUnion₂.mpr ⟨(α, β), Finset.mem_product.mpr
        ⟨by simp [hanc, hα], by simp [hanc, hβ]⟩, (not_le.mp hcon).le⟩)
    have henv : anchorEnv n (flowG W ⟨g, E, L, u⟩ ω) ≤ T := by
      refine Real.iSup_le (fun ab => ?_) hT0.le
      obtain ⟨h1a, h2a⟩ := lemma48_anchor n ab.1
      obtain ⟨h1b, h2b⟩ := lemma48_anchor n ab.2
      unfold anchorNorm
      exact max_le (max_le (hlt _ _ h1a h1b) (hlt _ _ h1a h2b))
        (max_le (hlt _ _ h2a h1b) (hlt _ _ h2a h2b))
    have henv0 : 0 ≤ anchorEnv n (flowG W ⟨g, E, L, u⟩ ω) :=
      Real.iSup_nonneg fun ab => le_max_of_le_left (le_max_of_le_left (norm_nonneg _))
    obtain ⟨v, hv, hvb⟩ := HL W L n E _ z (V ω) hW1 hL3 hn1 hE (hV ω) hzim0 hε₁0 hε₁1 hcl hcl' a σ
    obtain ⟨v', hv', hv'b⟩ := HP g (hCκP'.trans hgC) L h4L E hE m hroot hmC hmim n hn1 hnc₀ u hu0
      hu1' a σ
    set c : ℂ := (W : ℂ) ^ (1 - (k : ℤ)) with hcdef
    refine ⟨c • v, c • v', (loopSpace n E a).smul_mem c hv, (loopSpace n E a).smul_mem c hv',
      ?_, ?_⟩
    · rw [pi_norm_le_iff_of_nonneg heL0]
      intro x
      have hb := hvb x
      rw [← hG ω] at hb
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have e1 : loopTr (flowG W ⟨g, E, L, u⟩ ω) x.1 σ - c * v x =
          c * ((W : ℂ) ^ (k - 1) * loopTr (flowG W ⟨g, E, L, u⟩ ω) x.1 σ - v x) := by
        rw [mul_sub, ← mul_assoc, hc1, one_mul]
      rw [e1, norm_mul]
      calc ‖c‖ * ‖(W : ℂ) ^ (k - 1) * loopTr (flowG W ⟨g, E, L, u⟩ ω) x.1 σ - v x‖
          ≤ 1 * (CL * ((W : ℝ) ^ (-(B / 4)) + Cδ * n * ‖z - (E : ℂ)‖) *
            (1 + anchorEnv n (flowG W ⟨g, E, L, u⟩ ω)) ^ k) :=
            mul_le_mul hcle hb (norm_nonneg _) zero_le_one
        _ ≤ eL := by
            rw [one_mul, heL]
            gcongr
    · rw [pi_norm_le_iff_of_nonneg heP0]
      intro x
      have hb := hv'b x
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have e1 : primLoop g W L E m u x.1 σ - c * v' x =
          c * (primLoopF g L E m u x.1 σ - v' x) := by
        rw [mul_sub]; rfl
      rw [e1, norm_mul]
      calc ‖c‖ * ‖primLoopF g L E m u x.1 σ - v' x‖
          ≤ 1 * (CP * Real.sqrt ((n : ℝ) / g ^ 2) * (1 - u) ^ (-CP)) :=
            mul_le_mul hcle hb (norm_nonneg _) zero_le_one
        _ ≤ eP := by
            rw [one_mul, heP]
            have := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < 1 - u) (-CP)
            gcongr
  -- the weights
  have hw1F : (W : ℝ) ^ (-F) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
  have hratio1 : ∀ x s : Fin k → Fin L, (∀ j, cellStart n (s j) = cellStart n (x j)) →
      (fun _ => (1 : ℝ)) s / (fun _ => (1 : ℝ)) x ≤ 2 := fun _ _ _ => by norm_num
  have hratio : ∀ ℓ : ℝ, g ^ 2 ≤ ℓ → ∀ x s : Fin k → Fin L,
      (∀ j, cellStart n (s j) = cellStart n (x j)) →
      weightFn cw θ F W ℓ (wordDiam s) / weightFn cw θ F W ℓ (wordDiam x) ≤ 2 := by
    intro ℓ hℓ x s hxs
    have hℓ0 : 0 < ℓ := hgg.trans_le hℓ
    obtain ⟨-, h2⟩ := weight_comparison cw θ F hcw hθ (by linarith) W hW1 ℓ hℓ0 (wordDiam x)
      (wordDiam s) n (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (lemma48_wordDiam_abs n hn1 x s hxs)
    refine h2.trans ?_
    have hnl : (n : ℝ) / ℓ ≤ (W : ℝ) ^ (-B) := by
      rw [div_le_iff₀ hℓ0]
      calc (n : ℝ) ≤ g ^ 2 * (W : ℝ) ^ (-B) := hnhi
        _ ≤ ℓ * (W : ℝ) ^ (-B) := by gcongr
        _ = (W : ℝ) ^ (-B) * ℓ := by ring
    have hθ' : ((n : ℝ) / ℓ) ^ θ ≤ (W : ℝ) ^ (-(B * θ)) := by
      calc ((n : ℝ) / ℓ) ^ θ ≤ ((W : ℝ) ^ (-B)) ^ θ :=
            Real.rpow_le_rpow (by positivity) hnl hθ.le
        _ = (W : ℝ) ^ (-(B * θ)) := by rw [← Real.rpow_mul hx0.le]; ring_nf
    calc Real.exp (2 * cw * ((n : ℝ) / ℓ) ^ θ) ≤ Real.exp (Real.log 2) := by
          apply Real.exp_le_exp.mpr
          calc 2 * cw * ((n : ℝ) / ℓ) ^ θ ≤ 2 * cw * (W : ℝ) ^ (-(B * θ)) := by gcongr
            _ ≤ Real.log 2 := hE10
      _ = 2 := Real.exp_log (by norm_num)
  have happL : ∀ ω, ω ∉ A₁ ∪ A₂ → ∀ a : Fin k → Fin L, (∀ j, (a j).val % n = 0) →
      ∃ Z Fn v v' : CellProd n a → ℂ, v ∈ loopSpace n E a ∧ v' ∈ loopSpace n E a ∧
        (∀ x, (fun a => loopTr (flowG W ⟨g, E, L, u⟩ ω) a σ) x.1 = Z x - Fn x) ∧
        ‖Z - v‖ + ‖Fn - v'‖ ≤ eL := by
    intro ω hω a ha
    obtain ⟨vL, -, hvL, -, hbL, -⟩ := hgood ω hω a ha
    exact ⟨fun x => loopTr (flowG W ⟨g, E, L, u⟩ ω) x.1 σ, 0, vL, 0, hvL,
      (loopSpace n E a).zero_mem, fun x => by simp, by simpa using hbL⟩
  have happE : ∀ ω, ω ∉ A₁ ∪ A₂ → ∀ a : Fin k → Fin L, (∀ j, (a j).val % n = 0) →
      ∃ Z Fn v v' : CellProd n a → ℂ, v ∈ loopSpace n E a ∧ v' ∈ loopSpace n E a ∧
        (∀ x, (fun a => flowErr W ⟨g, E, L, u⟩ a σ ω) x.1 = Z x - Fn x) ∧
        ‖Z - v‖ + ‖Fn - v'‖ ≤ eL + eP := by
    intro ω hω a ha
    obtain ⟨vL, vP, hvL, hvP, hbL, hbP⟩ := hgood ω hω a ha
    exact ⟨fun x => loopTr (flowG W ⟨g, E, L, u⟩ ω) x.1 σ,
      fun x => primLoop g W L E m u x.1 σ, vL, vP, hvL, hvP, fun x => rfl, add_le_add hbL hbP⟩
  refine ⟨?_, ?_, fun ℓ hℓ => ⟨?_, ?_⟩⟩
  · refine sampleBound_of_norming _ _ _ _ _ _ _ _ hμ fun ω hω l => ?_
    refine (lemma48_norming n hn1 E (fun a => loopTr (flowG W ⟨g, E, L, u⟩ ω) a σ)
      (fun _ => (1 : ℝ)) _ eL hWF (fun _ => hw1F) hratio1
      (happL ω hω) l).trans ?_
    linarith
  · refine sampleBound_of_norming _ _ _ _ _ _ _ _ hμ fun ω hω l => ?_
    refine (lemma48_norming n hn1 E (fun a => flowErr W ⟨g, E, L, u⟩ a σ ω)
      (fun _ => (1 : ℝ)) _ (eL + eP) hWF (fun _ => hw1F)
      hratio1 (happE ω hω) l).trans ?_
    linarith
  · refine sampleBound_of_norming _ _ _ _ _ _ _ _ hμ fun ω hω l => ?_
    refine (lemma48_norming n hn1 E (fun a => loopTr (flowG W ⟨g, E, L, u⟩ ω) a σ)
      (fun a => weightFn cw θ F W ℓ (wordDiam a)) _ eL hWF
      (fun _ => lemma48_weight_ge _ _ _ _ _ _) (hratio ℓ hℓ) (happL ω hω) l).trans ?_
    linarith
  · refine sampleBound_of_norming _ _ _ _ _ _ _ _ hμ fun ω hω l => ?_
    refine (lemma48_norming n hn1 E (fun a => flowErr W ⟨g, E, L, u⟩ a σ ω)
      (fun a => weightFn cw θ F W ℓ (wordDiam a)) _ (eL + eP)
      hWF (fun _ => lemma48_weight_ge _ _ _ _ _ _) (hratio ℓ hℓ) (happE ω hω) l).trans ?_
    linarith

/-- The weighted sampling (5.34) [fo:eq:weighted-sampling-input] at large coupling with
`C_w = 2 d_2 = 72`, fixed before `C_V` and the chain depth, for every base family inside the
large-coupling range (Corollary 7.8 [uvc:cor:weighted-sampling]). -/
theorem swInput_of_large (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (CV : ℝ) (hCV : 0 < CV) (J : ℕ) :
    ∃ Cκ₀ : ℝ, 1 ≤ Cκ₀ ∧ ∀ Cκ : ℝ, Cκ₀ ≤ Cκ → ∀ ρ : ℕ → ℝ, Tendsto ρ atTop atTop →
      ∀ base : ℕ → Set FlowPt,
        (∀ W p, p ∈ base W → Cκ ≤ p.g ∧ |p.E| ≤ 2 - 3 * κ / 4 ∧
          ρ W * p.g ^ 2 * Real.log W ≤ p.L ∧ (p.L : ℝ) ≤ CV * p.g ^ 2 * (W : ℝ) ^ 2 ∧
          1 / 2 ≤ p.u ∧ (W : ℝ) ^ (-3 : ℝ) ≤ 1 - p.u) →
        SwInput base J 72 := by
  obtain ⟨Cκ₀, C'', hCκ₀, hC'', HR⟩ := cmpReach_large κ CV hκ hκ2 hCV J
  refine ⟨Cκ₀, hCκ₀, fun Cκ hCκ ρ hρ base hbase => ?_⟩
  obtain ⟨W₂, HR'⟩ := HR Cκ hCκ ρ hρ
  intro cp θ F D D' hcp _ hθ hθ2 hF hD hD'
  set C' : ℝ := max 3 (C'' + 1) with hC'def
  have hC'3 : 3 ≤ C' := le_max_left _ _
  have hC''C' : C'' ≤ C' := by have := le_max_right 3 (C'' + 1); linarith
  obtain ⟨B, Cκl, hB, -, W₀l, HL⟩ := loop_sampling (κ / 2) C' (by linarith) (by linarith)
    (by linarith) 2 (by norm_num) cp θ F D D' hcp hθ hθ2 hF hD hD'
  refine ⟨2 * B + 2 * C' + 6, ?_⟩
  have hev : ∀ᶠ W : ℕ in atTop, ((W₂ ≤ W ∧ W₀l ≤ W) ∧ 3 ≤ W) ∧
      (Cκl ≤ (W : ℝ) ∧ 2 * CV ≤ (W : ℝ) ∧ 4 * CV ^ 2 ≤ (W : ℝ)) ∧ 4 ≤ ρ W :=
    (((eventually_ge_atTop W₂).and (eventually_ge_atTop W₀l)).and (eventually_ge_atTop 3)).and
      (((tendsto_natCast_atTop_atTop.eventually_ge_atTop Cκl).and
        ((tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 * CV)).and
          (tendsto_natCast_atTop_atTop.eventually_ge_atTop (4 * CV ^ 2)))).and
        (hρ.eventually_ge_atTop 4))
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp hev
  refine ⟨W₀, fun W hW d p hd hreach => ?_⟩
  obtain ⟨⟨⟨hW₂, hW₀l⟩, hW3⟩, ⟨hWκ, hWCV, hWCV2⟩, hρ4⟩ := hW₀ W hW
  obtain ⟨hgp, hEp, hroot, hmim, hmC, hLlog, hLV, hu12, hut⟩ := HR' base hbase W hW₂ d p hd hreach
  have hx0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hx1 : (1 : ℝ) ≤ W := by exact_mod_cast (by omega : 1 ≤ W)
  have hx3 : (3 : ℝ) ≤ W := by exact_mod_cast hW3
  have hg0 : 0 < p.g :=
    lt_of_lt_of_le (div_pos (by linarith) (Real.sqrt_pos.mpr two_pos)) hgp
  have hpu : p.u < 1 := by have := Real.rpow_pos_of_pos hx0 (-3 : ℝ); linarith
  have hwpos : ∀ (ℓ : ℝ) (r : ℝ), 0 < weightFn cp θ F W ℓ r := fun ℓ r =>
    (Real.rpow_pos_of_pos hx0 _).trans_le (lemma48_weight_ge _ _ _ _ _ _)
  have hLV' : (p.L : ℝ) ≤ p.g ^ 2 * (W : ℝ) ^ C' := by
    have h3 : (W : ℝ) ^ (3 : ℝ) ≤ (W : ℝ) ^ C' := Real.rpow_le_rpow_of_exponent_le hx1 hC'3
    have h3' : (W : ℝ) ^ (3 : ℝ) = (W : ℝ) ^ 2 * W := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    have hg2 : 0 ≤ p.g ^ 2 := sq_nonneg _
    calc (p.L : ℝ) ≤ 2 * CV * p.g ^ 2 * (W : ℝ) ^ 2 := hLV
      _ ≤ W * p.g ^ 2 * (W : ℝ) ^ 2 := by gcongr
      _ = p.g ^ 2 * (W : ℝ) ^ (3 : ℝ) := by rw [h3']; ring
      _ ≤ p.g ^ 2 * (W : ℝ) ^ C' := by gcongr
  by_cases hbr : (W : ℝ) ^ B ≤ p.g ^ 2
  · have hWg : (W : ℝ) ≤ p.g := by
      have h2 : (W : ℝ) ^ (2 : ℝ) ≤ (W : ℝ) ^ B := Real.rpow_le_rpow_of_exponent_le hx1 hB.le
      rw [Real.rpow_two] at h2
      nlinarith
    have hg1 : 1 ≤ p.g := hx1.trans hWg
    have hlog : 1 ≤ Real.log W := by
      rw [Real.le_log_iff_exp_le hx0]
      have := Real.exp_one_lt_d9
      norm_num at this
      linarith
    have h4L : 4 * p.g ^ 2 ≤ p.L := by
      have hg2 : 0 ≤ p.g ^ 2 := sq_nonneg _
      have h1 : 4 ≤ ρ W * Real.log W := by nlinarith
      calc 4 * p.g ^ 2 ≤ (ρ W * Real.log W) * p.g ^ 2 := by gcongr
        _ = ρ W * p.g ^ 2 * Real.log W := by ring
        _ ≤ p.L := hLlog
    refine ⟨(loopSampleSet (cellLen p.g W B) p.E p.L 2).image fun s => (s 0, s 1), ?_, ?_⟩
    · have hc := card_loopSampleSet_le (cellLen p.g W B) (le_max_left _ _) p.E p.L 2
      have hcells := lemma48_cells p.g B C' W p.L (by omega) (by linarith) (by linarith) hbr hLV'
      have hn0 : 0 ≤ (p.L : ℝ) / cellLen p.g W B + 1 := by positivity
      have hpow : ((W : ℝ) ^ (B + C')) ^ 2 = (W : ℝ) ^ (2 * B + 2 * C') := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
      have h6 : (324 : ℝ) ≤ (W : ℝ) ^ (6 : ℝ) := by
        rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        have : (3 : ℝ) ^ 6 ≤ (W : ℝ) ^ 6 := pow_le_pow_left₀ (by norm_num) hx3 6
        norm_num at this
        linarith
      have hsplit : (W : ℝ) ^ (2 * B + 2 * C' + 6) =
          (W : ℝ) ^ (2 * B + 2 * C') * (W : ℝ) ^ (6 : ℝ) :=
        Real.rpow_add hx0 _ _
      have hW0 : 0 ≤ (W : ℝ) ^ (2 * B + 2 * C') := (Real.rpow_pos_of_pos hx0 _).le
      calc ((((loopSampleSet (cellLen p.g W B) p.E p.L 2).image fun s => (s 0, s 1)).card : ℕ) : ℝ)
          ≤ ((loopSampleSet (cellLen p.g W B) p.E p.L 2).card : ℝ) := by
            exact_mod_cast Finset.card_image_le
        _ ≤ 6 ^ 2 * ((p.L : ℝ) / cellLen p.g W B + 1) ^ 2 := hc
        _ ≤ 6 ^ 2 * (3 * (W : ℝ) ^ (B + C')) ^ 2 := by gcongr
        _ = 324 * (W : ℝ) ^ (2 * B + 2 * C') := by rw [mul_pow, hpow]; ring
        _ ≤ (W : ℝ) ^ (6 : ℝ) * (W : ℝ) ^ (2 * B + 2 * C') := by gcongr
        _ = (W : ℝ) ^ (2 * B + 2 * C' + 6) := by rw [hsplit]; ring
    · intro u v hu hv hvp
      have hu0 : 0 ≤ u := by linarith
      have hu3 : (W : ℝ) ^ (-3 : ℝ) ≤ 1 - u := by linarith
      have hℓ := lemma48_ellProp p.g hg1 p.L (by linarith) v (by linarith) (by linarith)
      have h4 := ((HL W hW₀l p.g p.L p.E (hWκ.trans hWg) hbr h4L hLV' hEp hroot
        (hmC.trans hC''C') ((inv_anti₀ (by linarith) hC''C').trans hmim) ![true, false] u hu0
        hu3).2.2 _ hℓ).2
      rw [show (2 : ℝ) * 6 ^ 2 = 72 by norm_num] at h4
      exact lemma48_pair (μ W p.L) (fun a ω => flowErr W ⟨p.g, p.E, p.L, u⟩ a ![true, false] ω)
        (fun a => weightFn cp θ F W (ellProp p.g p.L v) (wordDiam a)) (fun a => hwpos _ _)
        (fun ab ω => flowErr W ⟨p.g, p.E, p.L, u⟩ ![ab.1, ab.2] ![true, false] ω)
        (fun ab => weightFn cp θ F W (ellProp p.g p.L v) (cycDist ab.1 ab.2)) (fun ab ω => rfl)
        (fun ab => by simp only [lemma48_wordDiam_pair])
        (loopSampleSet (cellLen p.g W B) p.E p.L 2) 72 ((W : ℝ) ^ (-D)) ((W : ℝ) ^ (-D'))
        (by norm_num) h4
  · refine ⟨Finset.univ, ?_, fun u v _ _ _ => sampleBound_univ _ _ _ (fun _ => (hwpos _ _).le)
      (by norm_num) (Real.rpow_pos_of_pos hx0 _).le _⟩
    have hbr' : p.g ^ 2 < (W : ℝ) ^ B := not_le.mp hbr
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    have hL0 : 0 ≤ (p.L : ℝ) := Nat.cast_nonneg _
    have hWB0 : 0 ≤ (W : ℝ) ^ B := (Real.rpow_pos_of_pos hx0 _).le
    have hLb : (p.L : ℝ) ≤ 2 * CV * (W : ℝ) ^ B * (W : ℝ) ^ 2 := by
      calc (p.L : ℝ) ≤ 2 * CV * p.g ^ 2 * (W : ℝ) ^ 2 := hLV
        _ ≤ 2 * CV * (W : ℝ) ^ B * (W : ℝ) ^ 2 := by gcongr
    have h5 : (W : ℝ) ^ (5 : ℝ) ≤ (W : ℝ) ^ (2 * C' + 6) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have h5' : (W : ℝ) ^ (5 : ℝ) = W * (W : ℝ) ^ 4 := by
      rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    have hpow : ((W : ℝ) ^ B) ^ 2 = (W : ℝ) ^ (2 * B) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
    have hW2B : 0 ≤ (W : ℝ) ^ (2 * B) := (Real.rpow_pos_of_pos hx0 _).le
    calc (p.L : ℝ) * p.L ≤ (2 * CV * (W : ℝ) ^ B * (W : ℝ) ^ 2) *
          (2 * CV * (W : ℝ) ^ B * (W : ℝ) ^ 2) := mul_le_mul hLb hLb hL0 (hL0.trans hLb)
      _ = (4 * CV ^ 2) * (W : ℝ) ^ 4 * ((W : ℝ) ^ B) ^ 2 := by ring
      _ ≤ W * (W : ℝ) ^ 4 * ((W : ℝ) ^ B) ^ 2 := by gcongr
      _ = (W : ℝ) ^ (5 : ℝ) * (W : ℝ) ^ (2 * B) := by rw [h5', hpow]
      _ ≤ (W : ℝ) ^ (2 * C' + 6) * (W : ℝ) ^ (2 * B) := by gcongr
      _ = (W : ℝ) ^ (2 * B + 2 * C' + 6) := by
          rw [← Real.rpow_add hx0]; congr 1; ring

/-- Lemma 5.8 [uvc:thm:ordinary-sampling] for loops and loop errors at each fixed time, with the
cell exponent `B` and the coupling threshold chosen before the failure exponent `D'`. -/
theorem loop_sampling' (κ C : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hC : 1 < C) (k : ℕ) (hk : 1 ≤ k)
    (cw θ F D : ℝ) (hcw : 0 < cw) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2) (hF : 0 < F) (hD : 0 < D) :
    ∃ B Cκ : ℝ, 2 < B ∧ 1 ≤ Cκ ∧ ∀ D' : ℝ, 0 < D' →
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ (g : ℝ) (L : ℕ) (E : ℝ),
      Cκ ≤ g → (W : ℝ) ^ B ≤ g ^ 2 → 4 * g ^ 2 ≤ L → (L : ℝ) ≤ g ^ 2 * (W : ℝ) ^ C →
      |E| ≤ 2 - κ → IsDysonRootV (hopB g) (gammaG g) L E (mRoot g L E) →
      ‖mRoot g L E‖ ≤ C → C⁻¹ ≤ (mRoot g L E).im →
      ∀ (σ : Fin k → Bool) (u : ℝ), 0 ≤ u → (W : ℝ) ^ (-3 : ℝ) ≤ 1 - u →
        SampleBound (μ W L) (fun a ω => loopTr (flowG W ⟨g, E, L, u⟩ ω) a σ) (fun _ => 1)
          (loopSampleSet (cellLen g W B) E L k) (2 * 6 ^ k) ((W : ℝ) ^ (-D))
          ((W : ℝ) ^ (-D')) ∧
        SampleBound (μ W L) (fun a ω => flowErr W ⟨g, E, L, u⟩ a σ ω) (fun _ => 1)
          (loopSampleSet (cellLen g W B) E L k) (2 * 6 ^ k) ((W : ℝ) ^ (-D))
          ((W : ℝ) ^ (-D')) ∧
        ∀ ℓ : ℝ, g ^ 2 ≤ ℓ →
          SampleBound (μ W L) (fun a ω => loopTr (flowG W ⟨g, E, L, u⟩ ω) a σ)
            (fun a => weightFn cw θ F W ℓ (wordDiam a)) (loopSampleSet (cellLen g W B) E L k)
            (2 * 6 ^ k) ((W : ℝ) ^ (-D)) ((W : ℝ) ^ (-D')) ∧
          SampleBound (μ W L) (fun a ω => flowErr W ⟨g, E, L, u⟩ a σ ω)
            (fun a => weightFn cw θ F W ℓ (wordDiam a)) (loopSampleSet (cellLen g W B) E L k)
            (2 * 6 ^ k) ((W : ℝ) ^ (-D)) ((W : ℝ) ^ (-D')) := by
  obtain ⟨Cκχ, Cχ, hCκχ, hCχ, Hχ⟩ := char_large κ C hκ hκ2 hC.le
  obtain ⟨Cδ, hCδ, Hδ⟩ := cellClose_perturb κ hκ hκ2
  obtain ⟨CL, hCL, HL⟩ := loopTr_dist_space κ hκ hκ2 k hk
  obtain ⟨CκP, c₀, CP, hCκP, hc₀, hCP, HP⟩ := primLoopF_dist_space κ C hκ hκ2 hC.le k hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set B : ℝ := 4 * (4 * (k : ℝ) + F + D + 1) + 2 * (3 * CP + F + D + 1) with hBdef
  have hB2 : 2 < B := by rw [hBdef]; nlinarith
  have hB0 : 0 ≤ B := by linarith
  have hB4 : 4 * (k : ℝ) + F + D + 1 ≤ B / 4 := by rw [hBdef]; nlinarith
  have hB2' : 3 * CP + F + D + 1 ≤ B / 2 := by rw [hBdef]; nlinarith
  set Cκ : ℝ := max (max Cκχ CκP) (2 / Real.sqrt (κ / 2)) with hCκdef
  have hCκχ' : Cκχ ≤ Cκ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCκP' : CκP ≤ Cκ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCκr : 2 / Real.sqrt (κ / 2) ≤ Cκ := le_max_right _ _
  have hCκ1 : 1 ≤ Cκ := hCκχ.trans hCκχ'
  refine ⟨B, Cκ, hB2, hCκ1, fun D' hD' => ?_⟩
  set p : ℝ := 2 * (B + C) + D' + 1 with hpdef
  have hp : 0 < p := by rw [hpdef]; linarith
  obtain ⟨Cm, hCm, Hm⟩ := resolvent_moments (κ / 2) p Cχ (by linarith) hp (by linarith)
  obtain ⟨W₁, H₁⟩ := cells_prefix κ B C (D' + 1) hκ hκ2 hB2 (by linarith) (by linarith)
  have hev : ∀ᶠ W : ℕ in atTop, ((2 ≤ W ∧ W₁ ≤ W) ∧ 4 * p ≤ (W : ℝ)) ∧
      (Cχ * (W : ℝ) ^ (-B) ≤ 1 ∧ Cδ * Cχ * (W : ℝ) ^ (-(3 * B / 4)) ≤ 1 ∧
        2 * (W : ℝ) ^ (-(B / 4)) ≤ 1 ∧ 1 * (W : ℝ) ^ (-B) ≤ c₀) ∧
      (72 * Cm * Cχ ^ p * (W : ℝ) ^ (-1 : ℝ) ≤ 1 ∧
        (6 ^ k + 1) * (2 ^ (k + 1) * CL + CP) * (W : ℝ) ^ (-1 : ℝ) ≤ 1 ∧
        2 * cw * (W : ℝ) ^ (-(B * θ)) ≤ Real.log 2) :=
    (((eventually_ge_atTop 2).and (eventually_ge_atTop W₁)).and
      (tendsto_natCast_atTop_atTop.eventually_ge_atTop (4 * p))).and
    (((lemma48_ev Cχ B 1 (by linarith) one_pos).and
      ((lemma48_ev (Cδ * Cχ) (3 * B / 4) 1 (by linarith) one_pos).and
      ((lemma48_ev 2 (B / 4) 1 (by linarith) one_pos).and
      (lemma48_ev 1 B c₀ (by linarith) hc₀)))).and
    ((lemma48_ev (72 * Cm * Cχ ^ p) 1 1 one_pos one_pos).and
      ((lemma48_ev ((6 ^ k + 1) * (2 ^ (k + 1) * CL + CP)) 1 1 one_pos one_pos).and
      (lemma48_ev (2 * cw) (B * θ) (Real.log 2) (by positivity)
        (Real.log_pos (by norm_num))))))
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp hev
  refine ⟨W₀, fun W hW g L E hgC hWB h4L hLC hE hroot hmC hmim σ u hu0 hu1 => ?_⟩
  obtain ⟨⟨⟨hW2, hW₁⟩, hW4p⟩, ⟨hE4, hE5, hE6, hE7⟩, ⟨hE8, hE9, hE10⟩⟩ := hW₀ W hW
  have hW1 : 1 ≤ W := by omega
  have hx0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hx1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hx2 : (2 : ℝ) ≤ W := by exact_mod_cast hW2
  have hg1 : 1 ≤ g := hCκ1.trans hgC
  have hg0 : 0 < g := by linarith
  have hgg : 0 < g ^ 2 := by positivity
  have hγ : gammaG g = (g ^ 2)⁻¹ := by unfold gammaG; rw [max_eq_right hg1]
  have hW3 : 0 < (W : ℝ) ^ (-3 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hu1' : u < 1 := by linarith
  have hWB0 : 0 < (W : ℝ) ^ (-B) := Real.rpow_pos_of_pos hx0 _
  have hWB4 : 0 < (W : ℝ) ^ (-(B / 4)) := Real.rpow_pos_of_pos hx0 _
  set m : ℂ := mRoot g L E with hmdef
  obtain ⟨hre, hzE, hη0, hηC, hgη⟩ := Hχ g (hCκχ'.trans hgC) E m hE hmC hmim u hu0 hu1'
  set z : ℂ := zChar g E m u with hzdef
  set η : ℝ := etaChar g m u with hηdef
  have hzim : z.im = η := by simp [hzdef, hηdef, zChar, etaChar]
  set n : ℕ := cellLen g W B with hndef
  obtain ⟨-, hnhi⟩ := cellLen_bounds g B W hW1 hWB
  have hn1 : 1 ≤ n := le_max_left _ _
  have hL3 : 3 ≤ L := by
    have h1 : (1 : ℝ) ≤ g ^ 2 := one_le_pow₀ hg1
    have : (3 : ℝ) ≤ L := by linarith
    exact_mod_cast this
  -- the random potential and the Green function
  set s : ℝ := u * gammaG g with hsdef
  let V : Ω W L → Fin L → Matrix (Fin W) (Fin W) ℂ := fun ω r =>
    ((Real.sqrt s : ℝ) : ℂ) • gueBlock W L ω r
  have hV : ∀ ω r, (V ω r).IsHermitian := fun ω r => lemma48_herm W L ω _ r
  have hG : ∀ ω, flowG W ⟨g, E, L, u⟩ ω =
      resolventMat (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp (V ω)) z := by
    intro ω
    change resolventMat (flowH g W L u ω) z = _
    rw [flowH_cycle g hg1]
  -- the bad events
  set A₁ : Set (Ω W L) :=
    {ω | ¬ CellClose n E (E : ℂ) (V ω) ((W : ℝ) ^ (-(B / 4)))} with hA₁
  have hμA₁ : μ W L A₁ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D' + 1))) :=
    H₁ W hW₁ g L E s hWB hLC hE (mul_nonneg hu0 (by rw [hγ]; positivity))
      (by rw [hsdef, hγ, mul_assoc, inv_mul_cancel₀ hgg.ne', mul_one]; exact hu1'.le)
  set anc : Finset (Fin L) := univ.filter fun α : Fin L => IsAnchor n α with hanc
  set T : ℝ := (W : ℝ) ^ (4 : ℝ) with hT
  have hT0 : 0 < T := Real.rpow_pos_of_pos hx0 _
  open scoped Matrix.Norms.L2Operator in
  set A₂ : Set (Ω W L) := ⋃ ab ∈ anc ×ˢ anc,
    {ω | T ≤ ‖blockOf (flowG W ⟨g, E, L, u⟩ ω) ab.1 ab.2‖} with hA₂
  have hzri : ((z.re : ℝ) : ℂ) + ((η : ℝ) : ℂ) * Complex.I = z := by
    apply Complex.ext <;> simp [hzim]
  open scoped Matrix.Norms.L2Operator in
  have hμA₂ : μ W L A₂ ≤ ENNReal.ofReal ((W : ℝ) ^ (-D') / 2) := by
    have hone : ∀ ab : Fin L × Fin L,
        μ W L {ω | T ≤ ‖blockOf (flowG W ⟨g, E, L, u⟩ ω) ab.1 ab.2‖} ≤
          ENNReal.ofReal (Cm * (g ^ 2 * η) ^ (-p) / T ^ p) := by
      intro ab
      obtain ⟨hint, hbd⟩ := Hm W hW4p L g (hCκr.trans hgC) h4L z.re η u hre hη0 hηC hu0
        hu1'.le ab.1 ab.2
      have hfun : (fun ω => ‖blockOf (resolventMat (blockFlow W L
          (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) (u * gammaG g) ω)
          (((z.re : ℝ) : ℂ) + ((η : ℝ) : ℂ) * Complex.I)) ab.1 ab.2‖ ^ p) =
          fun ω => ‖blockOf (flowG W ⟨g, E, L, u⟩ ω) ab.1 ab.2‖ ^ p := by
        funext ω
        rw [hzri]
        rfl
      rw [hfun] at hint hbd
      exact lemma48_markov _ _ p T _ hp hT0 hint (fun _ => norm_nonneg _) hbd
    have hcard : (((anc ×ˢ anc).card : ℕ) : ℝ) ≤ 36 * (W : ℝ) ^ (2 * (B + C)) := by
      have h6 := (card_cells_le_pow g B C W L hW1 hB0 (by linarith) hWB hLC).2
      rw [Finset.card_product, Nat.cast_mul]
      have hpow : ((W : ℝ) ^ (B + C)) ^ 2 = (W : ℝ) ^ (2 * (B + C)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; ring_nf
      have hc0 : (0 : ℝ) ≤ anc.card := Nat.cast_nonneg _
      calc (anc.card : ℝ) * anc.card ≤ (6 * (W : ℝ) ^ (B + C)) * (6 * (W : ℝ) ^ (B + C)) :=
            mul_le_mul h6 h6 hc0 (hc0.trans h6)
        _ = 36 * ((W : ℝ) ^ (B + C)) ^ 2 := by ring
        _ = 36 * (W : ℝ) ^ (2 * (B + C)) := by rw [hpow]
    have hy' : (Cχ * (W : ℝ) ^ (3 : ℝ))⁻¹ ≤ g ^ 2 * η := by
      rw [mul_inv, ← Real.rpow_neg hx0.le]
      calc Cχ⁻¹ * (W : ℝ) ^ (-3 : ℝ) ≤ Cχ⁻¹ * (1 - u) :=
            mul_le_mul_of_nonneg_left hu1 (by positivity)
        _ = (1 - u) / Cχ := by ring
        _ ≤ g ^ 2 * η := hgη
    have harith := lemma48_env_arith W B C D' Cm Cχ p (((anc ×ˢ anc).card : ℕ) : ℝ) (g ^ 2 * η)
      hx1 hpdef hp hCm (by linarith) hcard (mul_pos hgg hη0) hy' hE8
    calc μ W L A₂ ≤ ∑ ab ∈ anc ×ˢ anc,
          μ W L {ω | T ≤ ‖blockOf (flowG W ⟨g, E, L, u⟩ ω) ab.1 ab.2‖} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ ab ∈ anc ×ˢ anc, ENNReal.ofReal (Cm * (g ^ 2 * η) ^ (-p) / T ^ p) :=
          Finset.sum_le_sum fun ab _ => hone ab
      _ = ENNReal.ofReal ((((anc ×ˢ anc).card : ℕ) : ℝ) * (Cm * (g ^ 2 * η) ^ (-p) / T ^ p)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-D') / 2) := ENNReal.ofReal_le_ofReal harith
  have hμ : μ W L (A₁ ∪ A₂) ≤ ENNReal.ofReal ((W : ℝ) ^ (-D')) := by
    have h1 : (W : ℝ) ^ (-(D' + 1)) ≤ (W : ℝ) ^ (-D') / 2 := by
      rw [show -(D' + 1) = -D' + (-1) by ring, Real.rpow_add hx0, Real.rpow_neg_one]
      have : (W : ℝ)⁻¹ ≤ 1 / 2 := by
        rw [inv_eq_one_div]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx2
      have hD0 : 0 ≤ (W : ℝ) ^ (-D') := (Real.rpow_pos_of_pos hx0 _).le
      calc (W : ℝ) ^ (-D') * (W : ℝ)⁻¹ ≤ (W : ℝ) ^ (-D') * (1 / 2) :=
            mul_le_mul_of_nonneg_left this hD0
        _ = (W : ℝ) ^ (-D') / 2 := by ring
    calc μ W L (A₁ ∪ A₂) ≤ μ W L A₁ + μ W L A₂ := measure_union_le _ _
      _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D' + 1))) + ENNReal.ofReal ((W : ℝ) ^ (-D') / 2) :=
          add_le_add hμA₁ hμA₂
      _ = ENNReal.ofReal ((W : ℝ) ^ (-(D' + 1)) + (W : ℝ) ^ (-D') / 2) :=
          (ENNReal.ofReal_add (Real.rpow_pos_of_pos hx0 _).le
            (by have := Real.rpow_pos_of_pos hx0 (-D'); positivity)).symm
      _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-D')) := ENNReal.ofReal_le_ofReal (by linarith)
  -- the deterministic errors
  set eL : ℝ := CL * (2 * (W : ℝ) ^ (-(B / 4))) * (1 + T) ^ k with heL
  set eP : ℝ := CP * (W : ℝ) ^ (-(B / 2)) * (W : ℝ) ^ (3 * CP) with heP
  have heL0 : 0 ≤ eL := by rw [heL]; positivity
  have heP0 : 0 ≤ eP := by
    rw [heP]
    have := Real.rpow_pos_of_pos hx0 (-(B / 2))
    have := Real.rpow_pos_of_pos hx0 (3 * CP)
    positivity
  have herr : (6 ^ k + 1) * (eL + eP) / (W : ℝ) ^ (-F) ≤ (W : ℝ) ^ (-D) :=
    lemma48_err_arith W F D B CL CP k hx1 hCL hCP hB4 hB2' hE9
  have hWF : 0 < (W : ℝ) ^ (-F) := Real.rpow_pos_of_pos hx0 _
  have herrL : (6 ^ k + 1) * eL / (W : ℝ) ^ (-F) ≤ (W : ℝ) ^ (-D) := by
    refine le_trans ?_ herr
    gcongr
    linarith
  obtain ⟨hc1, hcle⟩ := lemma48_zpow W hW1 k hk
  have hconj : ‖starRingEnd ℂ z - (E : ℂ)‖ = ‖z - (E : ℂ)‖ := by
    have : starRingEnd ℂ z - (E : ℂ) = starRingEnd ℂ (z - (E : ℂ)) := by
      rw [map_sub, Complex.conj_ofReal]
    rw [this, Complex.norm_conj]
  have hnz : (n : ℝ) * ‖z - (E : ℂ)‖ ≤ Cχ * (W : ℝ) ^ (-B) := by
    calc (n : ℝ) * ‖z - (E : ℂ)‖ ≤ (g ^ 2 * (W : ℝ) ^ (-B)) * (Cχ / g ^ 2) :=
          mul_le_mul hnhi hzE (norm_nonneg _) (by positivity)
      _ = Cχ * (W : ℝ) ^ (-B) := by field_simp
  have hδB : Cδ * n * ‖z - (E : ℂ)‖ ≤ (W : ℝ) ^ (-(B / 4)) := by
    have hsplit : (W : ℝ) ^ (-B) = (W : ℝ) ^ (-(3 * B / 4)) * (W : ℝ) ^ (-(B / 4)) := by
      rw [← Real.rpow_add hx0]; ring_nf
    calc Cδ * n * ‖z - (E : ℂ)‖ = Cδ * ((n : ℝ) * ‖z - (E : ℂ)‖) := by ring
      _ ≤ Cδ * (Cχ * (W : ℝ) ^ (-B)) := mul_le_mul_of_nonneg_left hnz hCδ.le
      _ = (Cδ * Cχ * (W : ℝ) ^ (-(3 * B / 4))) * (W : ℝ) ^ (-(B / 4)) := by rw [hsplit]; ring
      _ ≤ 1 * (W : ℝ) ^ (-(B / 4)) := by gcongr
      _ = (W : ℝ) ^ (-(B / 4)) := one_mul _
  have hnc₀ : (n : ℝ) ≤ c₀ * g ^ 2 := by
    calc (n : ℝ) ≤ g ^ 2 * (W : ℝ) ^ (-B) := hnhi
      _ ≤ g ^ 2 * c₀ := by gcongr; linarith
      _ = c₀ * g ^ 2 := by ring
  have hsq : Real.sqrt ((n : ℝ) / g ^ 2) ≤ (W : ℝ) ^ (-(B / 2)) := by
    have h1 : (n : ℝ) / g ^ 2 ≤ (W : ℝ) ^ (-B) := by
      rw [div_le_iff₀ hgg]; linarith
    calc Real.sqrt ((n : ℝ) / g ^ 2) ≤ Real.sqrt ((W : ℝ) ^ (-B)) := Real.sqrt_le_sqrt h1
      _ = (W : ℝ) ^ (-(B / 2)) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]; ring_nf
  have hut : (1 - u) ^ (-CP) ≤ (W : ℝ) ^ (3 * CP) := by
    calc (1 - u) ^ (-CP) ≤ ((W : ℝ) ^ (-3 : ℝ)) ^ (-CP) :=
          Real.rpow_le_rpow_of_nonpos hW3 hu1 (by linarith)
      _ = (W : ℝ) ^ (3 * CP) := by rw [← Real.rpow_mul hx0.le]; ring_nf
  have hgood : ∀ ω, ω ∉ A₁ ∪ A₂ → ∀ a : Fin k → Fin L, (∀ j, (a j).val % n = 0) →
      ∃ vL vP : CellProd n a → ℂ, vL ∈ loopSpace n E a ∧ vP ∈ loopSpace n E a ∧
        ‖(fun x : CellProd n a => loopTr (flowG W ⟨g, E, L, u⟩ ω) x.1 σ) - vL‖ ≤ eL ∧
        ‖(fun x : CellProd n a => primLoop g W L E m u x.1 σ) - vP‖ ≤ eP := by
    intro ω hω a _
    have hω1 : ω ∉ A₁ := fun h => hω (Or.inl h)
    have hω2 : ω ∉ A₂ := fun h => hω (Or.inr h)
    have hcl0 : CellClose n E (E : ℂ) (V ω) ((W : ℝ) ^ (-(B / 4))) := not_not.mp hω1
    have hε1 : (W : ℝ) ^ (-(B / 4)) ≤ 1 := by linarith
    have hnz1 : (n : ℝ) * ‖z - (E : ℂ)‖ ≤ 1 := hnz.trans hE4
    have hcl := Hδ W L n E _ z (V ω) hE hWB4.le hε1 hnz1 hcl0
    have hcl' := Hδ W L n E _ (starRingEnd ℂ z) (V ω) hE hWB4.le hε1 (by rwa [hconj]) hcl0
    rw [hconj] at hcl'
    have hε₁ : (W : ℝ) ^ (-(B / 4)) + Cδ * n * ‖z - (E : ℂ)‖ ≤ 2 * (W : ℝ) ^ (-(B / 4)) := by
      linarith
    have hε₁0 : 0 ≤ (W : ℝ) ^ (-(B / 4)) + Cδ * n * ‖z - (E : ℂ)‖ := by positivity
    have hε₁1 : (W : ℝ) ^ (-(B / 4)) + Cδ * n * ‖z - (E : ℂ)‖ ≤ 1 := by linarith
    have hzim0 : z.im ≠ 0 := by rw [hzim]; exact hη0.ne'
    open scoped Matrix.Norms.L2Operator in
    have hlt : ∀ α β : Fin L, IsAnchor n α → IsAnchor n β →
        ‖blockOf (flowG W ⟨g, E, L, u⟩ ω) α β‖ ≤ T := by
      intro α β hα hβ
      by_contra hcon
      exact hω2 (Set.mem_iUnion₂.mpr ⟨(α, β), Finset.mem_product.mpr
        ⟨by simp [hanc, hα], by simp [hanc, hβ]⟩, (not_le.mp hcon).le⟩)
    have henv : anchorEnv n (flowG W ⟨g, E, L, u⟩ ω) ≤ T := by
      refine Real.iSup_le (fun ab => ?_) hT0.le
      obtain ⟨h1a, h2a⟩ := lemma48_anchor n ab.1
      obtain ⟨h1b, h2b⟩ := lemma48_anchor n ab.2
      unfold anchorNorm
      exact max_le (max_le (hlt _ _ h1a h1b) (hlt _ _ h1a h2b))
        (max_le (hlt _ _ h2a h1b) (hlt _ _ h2a h2b))
    have henv0 : 0 ≤ anchorEnv n (flowG W ⟨g, E, L, u⟩ ω) :=
      Real.iSup_nonneg fun ab => le_max_of_le_left (le_max_of_le_left (norm_nonneg _))
    obtain ⟨v, hv, hvb⟩ := HL W L n E _ z (V ω) hW1 hL3 hn1 hE (hV ω) hzim0 hε₁0 hε₁1 hcl hcl' a σ
    obtain ⟨v', hv', hv'b⟩ := HP g (hCκP'.trans hgC) L h4L E hE m hroot hmC hmim n hn1 hnc₀ u hu0
      hu1' a σ
    set c : ℂ := (W : ℂ) ^ (1 - (k : ℤ)) with hcdef
    refine ⟨c • v, c • v', (loopSpace n E a).smul_mem c hv, (loopSpace n E a).smul_mem c hv',
      ?_, ?_⟩
    · rw [pi_norm_le_iff_of_nonneg heL0]
      intro x
      have hb := hvb x
      rw [← hG ω] at hb
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have e1 : loopTr (flowG W ⟨g, E, L, u⟩ ω) x.1 σ - c * v x =
          c * ((W : ℂ) ^ (k - 1) * loopTr (flowG W ⟨g, E, L, u⟩ ω) x.1 σ - v x) := by
        rw [mul_sub, ← mul_assoc, hc1, one_mul]
      rw [e1, norm_mul]
      calc ‖c‖ * ‖(W : ℂ) ^ (k - 1) * loopTr (flowG W ⟨g, E, L, u⟩ ω) x.1 σ - v x‖
          ≤ 1 * (CL * ((W : ℝ) ^ (-(B / 4)) + Cδ * n * ‖z - (E : ℂ)‖) *
            (1 + anchorEnv n (flowG W ⟨g, E, L, u⟩ ω)) ^ k) :=
            mul_le_mul hcle hb (norm_nonneg _) zero_le_one
        _ ≤ eL := by
            rw [one_mul, heL]
            gcongr
    · rw [pi_norm_le_iff_of_nonneg heP0]
      intro x
      have hb := hv'b x
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have e1 : primLoop g W L E m u x.1 σ - c * v' x =
          c * (primLoopF g L E m u x.1 σ - v' x) := by
        rw [mul_sub]; rfl
      rw [e1, norm_mul]
      calc ‖c‖ * ‖primLoopF g L E m u x.1 σ - v' x‖
          ≤ 1 * (CP * Real.sqrt ((n : ℝ) / g ^ 2) * (1 - u) ^ (-CP)) :=
            mul_le_mul hcle hb (norm_nonneg _) zero_le_one
        _ ≤ eP := by
            rw [one_mul, heP]
            have := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < 1 - u) (-CP)
            gcongr
  -- the weights
  have hw1F : (W : ℝ) ^ (-F) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
  have hratio1 : ∀ x s : Fin k → Fin L, (∀ j, cellStart n (s j) = cellStart n (x j)) →
      (fun _ => (1 : ℝ)) s / (fun _ => (1 : ℝ)) x ≤ 2 := fun _ _ _ => by norm_num
  have hratio : ∀ ℓ : ℝ, g ^ 2 ≤ ℓ → ∀ x s : Fin k → Fin L,
      (∀ j, cellStart n (s j) = cellStart n (x j)) →
      weightFn cw θ F W ℓ (wordDiam s) / weightFn cw θ F W ℓ (wordDiam x) ≤ 2 := by
    intro ℓ hℓ x s hxs
    have hℓ0 : 0 < ℓ := hgg.trans_le hℓ
    obtain ⟨-, h2⟩ := weight_comparison cw θ F hcw hθ (by linarith) W hW1 ℓ hℓ0 (wordDiam x)
      (wordDiam s) n (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (lemma48_wordDiam_abs n hn1 x s hxs)
    refine h2.trans ?_
    have hnl : (n : ℝ) / ℓ ≤ (W : ℝ) ^ (-B) := by
      rw [div_le_iff₀ hℓ0]
      calc (n : ℝ) ≤ g ^ 2 * (W : ℝ) ^ (-B) := hnhi
        _ ≤ ℓ * (W : ℝ) ^ (-B) := by gcongr
        _ = (W : ℝ) ^ (-B) * ℓ := by ring
    have hθ' : ((n : ℝ) / ℓ) ^ θ ≤ (W : ℝ) ^ (-(B * θ)) := by
      calc ((n : ℝ) / ℓ) ^ θ ≤ ((W : ℝ) ^ (-B)) ^ θ :=
            Real.rpow_le_rpow (by positivity) hnl hθ.le
        _ = (W : ℝ) ^ (-(B * θ)) := by rw [← Real.rpow_mul hx0.le]; ring_nf
    calc Real.exp (2 * cw * ((n : ℝ) / ℓ) ^ θ) ≤ Real.exp (Real.log 2) := by
          apply Real.exp_le_exp.mpr
          calc 2 * cw * ((n : ℝ) / ℓ) ^ θ ≤ 2 * cw * (W : ℝ) ^ (-(B * θ)) := by gcongr
            _ ≤ Real.log 2 := hE10
      _ = 2 := Real.exp_log (by norm_num)
  have happL : ∀ ω, ω ∉ A₁ ∪ A₂ → ∀ a : Fin k → Fin L, (∀ j, (a j).val % n = 0) →
      ∃ Z Fn v v' : CellProd n a → ℂ, v ∈ loopSpace n E a ∧ v' ∈ loopSpace n E a ∧
        (∀ x, (fun a => loopTr (flowG W ⟨g, E, L, u⟩ ω) a σ) x.1 = Z x - Fn x) ∧
        ‖Z - v‖ + ‖Fn - v'‖ ≤ eL := by
    intro ω hω a ha
    obtain ⟨vL, -, hvL, -, hbL, -⟩ := hgood ω hω a ha
    exact ⟨fun x => loopTr (flowG W ⟨g, E, L, u⟩ ω) x.1 σ, 0, vL, 0, hvL,
      (loopSpace n E a).zero_mem, fun x => by simp, by simpa using hbL⟩
  have happE : ∀ ω, ω ∉ A₁ ∪ A₂ → ∀ a : Fin k → Fin L, (∀ j, (a j).val % n = 0) →
      ∃ Z Fn v v' : CellProd n a → ℂ, v ∈ loopSpace n E a ∧ v' ∈ loopSpace n E a ∧
        (∀ x, (fun a => flowErr W ⟨g, E, L, u⟩ a σ ω) x.1 = Z x - Fn x) ∧
        ‖Z - v‖ + ‖Fn - v'‖ ≤ eL + eP := by
    intro ω hω a ha
    obtain ⟨vL, vP, hvL, hvP, hbL, hbP⟩ := hgood ω hω a ha
    exact ⟨fun x => loopTr (flowG W ⟨g, E, L, u⟩ ω) x.1 σ,
      fun x => primLoop g W L E m u x.1 σ, vL, vP, hvL, hvP, fun x => rfl, add_le_add hbL hbP⟩
  refine ⟨?_, ?_, fun ℓ hℓ => ⟨?_, ?_⟩⟩
  · refine sampleBound_of_norming _ _ _ _ _ _ _ _ hμ fun ω hω l => ?_
    refine (lemma48_norming n hn1 E (fun a => loopTr (flowG W ⟨g, E, L, u⟩ ω) a σ)
      (fun _ => (1 : ℝ)) _ eL hWF (fun _ => hw1F) hratio1
      (happL ω hω) l).trans ?_
    linarith
  · refine sampleBound_of_norming _ _ _ _ _ _ _ _ hμ fun ω hω l => ?_
    refine (lemma48_norming n hn1 E (fun a => flowErr W ⟨g, E, L, u⟩ a σ ω)
      (fun _ => (1 : ℝ)) _ (eL + eP) hWF (fun _ => hw1F)
      hratio1 (happE ω hω) l).trans ?_
    linarith
  · refine sampleBound_of_norming _ _ _ _ _ _ _ _ hμ fun ω hω l => ?_
    refine (lemma48_norming n hn1 E (fun a => loopTr (flowG W ⟨g, E, L, u⟩ ω) a σ)
      (fun a => weightFn cw θ F W ℓ (wordDiam a)) _ eL hWF
      (fun _ => lemma48_weight_ge _ _ _ _ _ _) (hratio ℓ hℓ) (happL ω hω) l).trans ?_
    linarith
  · refine sampleBound_of_norming _ _ _ _ _ _ _ _ hμ fun ω hω l => ?_
    refine (lemma48_norming n hn1 E (fun a => flowErr W ⟨g, E, L, u⟩ a σ ω)
      (fun a => weightFn cw θ F W ℓ (wordDiam a)) _ (eL + eP)
      hWF (fun _ => lemma48_weight_ge _ _ _ _ _ _) (hratio ℓ hℓ) (happE ω hω) l).trans ?_
    linarith

end LSBA
