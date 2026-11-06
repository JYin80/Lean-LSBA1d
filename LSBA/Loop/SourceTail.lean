import LSBA.Loop.Cuts
import LSBA.Loop.Generator
import LSBA.Primitive.Defs
import LSBA.Loop.ErrorHierarchy
import LSBA.Loop.Projection
import LSBA.Kernel.Tensor

/-!
# Tail bounds of the sources of the projected loop-error equation

Bounds of the light term, the linear and quadratic cut sources and the bracket of (C.32)
[gc:eq:sourcetable] by the maximum of the shorter loop errors plus their tail beyond a given
diameter, the commutator bound for complex tensors, and the chain bound (C.40) [gc:eq:chain].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Near and far labels -/

private lemma sourceTail_mod {L x y : ℕ} (hx : x < L) (hy : y < L) :
    (x + L - y) % L = if y ≤ x then x - y else x + L - y := by
  split_ifs with h
  · have : x + L - y = (x - y) + L := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

/-- A cyclic ball of radius `r` has at most `2r + 1` points. -/
private lemma sourceTail_ball_card {L : ℕ} (β : Fin L) (r : ℕ) :
    (Finset.univ.filter fun x : Fin L => cycDist x β ≤ r).card ≤ 2 * r + 1 := by
  have hβ := β.isLt
  have h1 : (Finset.univ.filter fun x : Fin L => cycDist x β ≤ r).card ≤
      (Finset.range (r + 1) ∪ Finset.Ico (L - r) L).card := by
    refine Finset.card_le_card_of_injOn (fun x : Fin L => (x.val + L - β.val) % L) ?_ ?_
    · intro x hx
      have hx' : cycDist x β ≤ r := by simpa using hx
      have hxl := x.isLt
      simp only [cycDist, sourceTail_mod hxl hβ, sourceTail_mod hβ hxl] at hx'
      simp only [Finset.coe_union, Finset.coe_range, Finset.coe_Ico, Set.mem_union,
        Set.mem_Iio, Set.mem_Ico, sourceTail_mod hxl hβ]
      split_ifs at hx' ⊢ <;> omega
    · intro x _ x' _ hxx
      have hxl := x.isLt
      have hxl' := x'.isLt
      simp only [sourceTail_mod hxl hβ, sourceTail_mod hxl' hβ] at hxx
      apply Fin.ext
      split_ifs at hxx <;> omega
  refine h1.trans ?_
  calc (Finset.range (r + 1) ∪ Finset.Ico (L - r) L).card
      ≤ (Finset.range (r + 1)).card + (Finset.Ico (L - r) L).card := Finset.card_union_le _ _
    _ ≤ (r + 1) + r := by
        rw [Finset.card_range, Nat.card_Ico]
        omega
    _ = 2 * r + 1 := by ring

/-- The labels within real distance `d ≥ 0` of `β` number at most `2d + 1`. -/
private lemma sourceTail_near_card {L : ℕ} (β : Fin L) (d : ℝ) (hd : 0 ≤ d) :
    ((Finset.univ.filter fun x : Fin L => (cycDist x β : ℝ) ≤ d).card : ℝ) ≤ 2 * d + 1 := by
  have h : (Finset.univ.filter fun x : Fin L => (cycDist x β : ℝ) ≤ d) =
      Finset.univ.filter fun x : Fin L => cycDist x β ≤ ⌊d⌋₊ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Nat.le_floor_iff hd).symm
  rw [h]
  have h1 := sourceTail_ball_card β ⌊d⌋₊
  have h2 : ((Finset.univ.filter fun x : Fin L => cycDist x β ≤ ⌊d⌋₊).card : ℝ) ≤
      ((2 * ⌊d⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
  have h3 := Nat.floor_le hd
  push_cast at h2
  linarith

/-- Row bound: a function bounded by `X` everywhere and by `τ` at labels farther than `d` from `β`
has `ℓ¹` norm at most `(2d + 1) X + L τ`. -/
private lemma sourceTail_row {L : ℕ} (T : Fin L → ℂ) (β : Fin L) (X d τ : ℝ) (hd : 0 ≤ d)
    (hτ0 : 0 ≤ τ) (hX : ∀ c, ‖T c‖ ≤ X) (hτ : ∀ c, d < (cycDist c β : ℝ) → ‖T c‖ ≤ τ) :
    ∑ c, ‖T c‖ ≤ (2 * d + 1) * X + L * τ := by
  have hX0 : 0 ≤ X := (norm_nonneg _).trans (hX β)
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x : Fin L => (cycDist x β : ℝ) ≤ d)]
  have hn := sourceTail_near_card β d hd
  have h1 : ∑ c ∈ Finset.univ.filter (fun x : Fin L => (cycDist x β : ℝ) ≤ d), ‖T c‖ ≤
      (Finset.univ.filter fun x : Fin L => (cycDist x β : ℝ) ≤ d).card * X := by
    rw [← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ fun c _ => hX c
  have h2 : ∑ c ∈ Finset.univ.filter (fun x : Fin L => ¬ (cycDist x β : ℝ) ≤ d), ‖T c‖ ≤
      (Finset.univ.filter fun x : Fin L => ¬ (cycDist x β : ℝ) ≤ d).card * τ := by
    rw [← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ fun c hc => hτ c (by
      simpa using hc)
  have h3 : ((Finset.univ.filter fun x : Fin L => ¬ (cycDist x β : ℝ) ≤ d).card : ℝ) ≤ L := by
    have := Finset.card_filter_le (Finset.univ : Finset (Fin L))
      (fun x : Fin L => ¬ (cycDist x β : ℝ) ≤ d)
    simpa using this
  have h4 : ((Finset.univ.filter fun x : Fin L => (cycDist x β : ℝ) ≤ d).card : ℝ) * X ≤
      (2 * d + 1) * X := mul_le_mul_of_nonneg_right hn hX0
  have h5 : ((Finset.univ.filter fun x : Fin L => ¬ (cycDist x β : ℝ) ≤ d).card : ℝ) * τ ≤
      L * τ := mul_le_mul_of_nonneg_right h3 hτ0
  linarith

/-- A product of a nonnegatively bounded factor and a factor of bounded `ℓ¹` norm. -/
private lemma sourceTail_prod {L : ℕ} (F G : Fin L → ℂ) (XF S : ℝ) (hXF : 0 ≤ XF)
    (hF : ∀ c, ‖F c‖ ≤ XF) (hG : ∑ c, ‖G c‖ ≤ S) : ‖∑ c, F c * G c‖ ≤ XF * S := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ c, ‖F c * G c‖ ≤ ∑ c, XF * ‖G c‖ := by
        refine Finset.sum_le_sum fun c _ => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hF c) (norm_nonneg _)
    _ = XF * ∑ c, ‖G c‖ := by rw [Finset.mul_sum]
    _ ≤ XF * S := mul_le_mul_of_nonneg_left hG hXF

private lemma sourceTail_cyc_le {L n : ℕ} (w : Fin n → Fin L) (p q : Fin n) :
    cycDist (w p) (w q) ≤ wordDiam w :=
  Finset.le_sup (f := fun p : Fin n × Fin n => cycDist (w p.1) (w p.2)) (Finset.mem_univ (p, q))

private lemma sourceTail_far {L n : ℕ} (w : Fin n → Fin L) (p q : Fin n) (d : ℝ)
    (h : d < (cycDist (w p) (w q) : ℝ)) : d < (wordDiam w : ℝ) :=
  lt_of_lt_of_le h (by exact_mod_cast sourceTail_cyc_le w p q)

private lemma sourceTail_pairs (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ∑ i : Fin k, ∑ j : Fin k, (if i < j then t else 0) ≤ (k : ℝ) ^ 2 / 2 * t := by
  have h1 : ∑ i : Fin k, ∑ j : Fin k, (if i < j then t else 0) =
      ∑ i : Fin k, ∑ j : Fin k, (if j < i then t else 0) := Finset.sum_comm
  have h2 : ∑ i : Fin k, ∑ j : Fin k, ((if i < j then t else 0) + (if j < i then t else 0)) ≤
      ∑ i : Fin k, ∑ j : Fin k, t := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    by_cases h : i < j
    · simp [h, not_lt.mpr h.le]
    · by_cases h' : j < i <;> simp [h, h', ht]
  simp only [Finset.sum_add_distrib] at h2
  rw [← h1] at h2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
  have : ((k : ℝ) * ((k : ℝ) * t)) = (k : ℝ) ^ 2 * t := by ring
  nlinarith

private lemma sourceTail_pairsum {k : ℕ} (T : Fin k → Fin k → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hT : ∀ i j, i < j → ‖T i j‖ ≤ B) :
    ‖∑ i, ∑ j, (if i < j then T i j else 0)‖ ≤ (k : ℝ) ^ 2 / 2 * B := by
  refine le_trans ?_ (sourceTail_pairs k B hB)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  by_cases h : i < j
  · simpa [h] using hT i j h
  · simp [h]

/-! ### Localized rows of the cut words -/

private lemma sourceTail_rowR {L k : ℕ} (D : LoopFam L) (a : Fin k → Fin L) (σ : Fin k → Bool)
    (i j : Fin k) (hij : i < j) (X d τ : ℝ) (hd : 0 ≤ d) (hτ0 : 0 ≤ τ)
    (hX : ∀ (b : Fin (j.val - i.val + 1) → Fin L) (s : Fin (j.val - i.val + 1) → Bool),
      ‖D (j.val - i.val + 1) b s‖ ≤ X)
    (hτ : ∀ (b : Fin (j.val - i.val + 1) → Fin L) (s : Fin (j.val - i.val + 1) → Bool),
      d < wordDiam b → ‖D (j.val - i.val + 1) b s‖ ≤ τ) :
    ∑ c, ‖D _ (cutRLab a i j c) (cutRSgn σ i j)‖ ≤ (2 * d + 1) * X + L * τ := by
  have hij' : i.val < j.val := hij
  refine sourceTail_row (fun c => D _ (cutRLab a i j c) (cutRSgn σ i j)) (a i) X d τ hd hτ0
    (fun c => hX _ _) fun c hc => hτ _ _ ?_
  refine sourceTail_far (cutRLab a i j c) (Fin.last _) ⟨0, by omega⟩ d ?_
  have e1 : cutRLab a i j c (Fin.last _) = c := by simp [cutRLab]
  have e2 : cutRLab a i j c ⟨0, by omega⟩ = a i := by
    have h0 : 0 < j.val - i.val := by omega
    simp [cutRLab, h0]
  rwa [e1, e2]

private lemma sourceTail_rowL {L k : ℕ} (D : LoopFam L) (a : Fin k → Fin L) (σ : Fin k → Bool)
    (i j : Fin k) (hij : i < j) (X d τ : ℝ) (hd : 0 ≤ d) (hτ0 : 0 ≤ τ)
    (hX : ∀ (b : Fin (k + i.val - j.val + 1) → Fin L) (s : Fin (k + i.val - j.val + 1) → Bool),
      ‖D (k + i.val - j.val + 1) b s‖ ≤ X)
    (hτ : ∀ (b : Fin (k + i.val - j.val + 1) → Fin L) (s : Fin (k + i.val - j.val + 1) → Bool),
      d < wordDiam b → ‖D (k + i.val - j.val + 1) b s‖ ≤ τ) :
    ∑ c, ‖D _ (cutLLab a i j c) (cutLSgn σ i j)‖ ≤ (2 * d + 1) * X + L * τ := by
  have hij' : i.val < j.val := hij
  have hjk := j.2
  refine sourceTail_row (fun c => D _ (cutLLab a i j c) (cutLSgn σ i j)) (a j) X d τ hd hτ0
    (fun c => hX _ _) fun c hc => hτ _ _ ?_
  refine sourceTail_far (cutLLab a i j c) ⟨i.val, by omega⟩ ⟨i.val + 1, by omega⟩ d ?_
  have e1 : cutLLab a i j c ⟨i.val, by omega⟩ = c := by simp [cutLLab]
  have e2 : cutLLab a i j c ⟨i.val + 1, by omega⟩ = a j := by
    simp only [cutLLab, Nat.not_lt.mpr (Nat.le_succ i.val), Nat.succ_ne_self, dite_false,
      ite_false]
    congr 1
    apply Fin.ext
    simp only
    omega
  rwa [e1, e2]

private lemma sourceTail_KD {L k : ℕ} (K D : LoopFam L) (a : Fin k → Fin L) (σ : Fin k → Bool)
    (i j : Fin k) (hij : i < j) (XK X d τ : ℝ) (hd : 0 ≤ d) (hτ0 : 0 ≤ τ) (hXK : 0 ≤ XK)
    (hK : ∀ (b : Fin (k + i.val - j.val + 1) → Fin L) (s : Fin (k + i.val - j.val + 1) → Bool),
      ‖K (k + i.val - j.val + 1) b s‖ ≤ XK)
    (hD : ∀ (b : Fin (j.val - i.val + 1) → Fin L) (s : Fin (j.val - i.val + 1) → Bool),
      ‖D (j.val - i.val + 1) b s‖ ≤ X)
    (hDτ : ∀ (b : Fin (j.val - i.val + 1) → Fin L) (s : Fin (j.val - i.val + 1) → Bool),
      d < wordDiam b → ‖D (j.val - i.val + 1) b s‖ ≤ τ) :
    ‖∑ c, K _ (cutLLab a i j c) (cutLSgn σ i j) * D _ (cutRLab a i j c) (cutRSgn σ i j)‖ ≤
      XK * ((2 * d + 1) * X + L * τ) :=
  sourceTail_prod _ _ _ _ hXK (fun _ => hK _ _) (sourceTail_rowR D a σ i j hij X d τ hd hτ0 hD hDτ)

private lemma sourceTail_DK {L k : ℕ} (K D : LoopFam L) (a : Fin k → Fin L) (σ : Fin k → Bool)
    (i j : Fin k) (hij : i < j) (XK X d τ : ℝ) (hd : 0 ≤ d) (hτ0 : 0 ≤ τ) (hXK : 0 ≤ XK)
    (hK : ∀ (b : Fin (j.val - i.val + 1) → Fin L) (s : Fin (j.val - i.val + 1) → Bool),
      ‖K (j.val - i.val + 1) b s‖ ≤ XK)
    (hD : ∀ (b : Fin (k + i.val - j.val + 1) → Fin L) (s : Fin (k + i.val - j.val + 1) → Bool),
      ‖D (k + i.val - j.val + 1) b s‖ ≤ X)
    (hDτ : ∀ (b : Fin (k + i.val - j.val + 1) → Fin L) (s : Fin (k + i.val - j.val + 1) → Bool),
      d < wordDiam b → ‖D (k + i.val - j.val + 1) b s‖ ≤ τ) :
    ‖∑ c, D _ (cutLLab a i j c) (cutLSgn σ i j) * K _ (cutRLab a i j c) (cutRSgn σ i j)‖ ≤
      XK * ((2 * d + 1) * X + L * τ) := by
  simp only [mul_comm (D _ (cutLLab a i j _) (cutLSgn σ i j))]
  exact sourceTail_prod _ _ _ _ hXK (fun _ => hK _ _)
    (sourceTail_rowL D a σ i j hij X d τ hd hτ0 hD hDτ)

/-! ### The light term -/

/-- The light insertion `𝒲_k` of (5.7) [fo:eq:light] with its free label localized: if
`|D_1| ≤ X₁` at every label and sign, and every loop of length `k + 1` is at most `X`, and at
most `τ` above diameter `d`, then `‖𝒲_k‖ ≤ γ W k X₁ ((2d + 1) X + L τ)` (the light row of (C.32)
[gc:eq:sourcetable]). -/
theorem lightW_tail_le (g E : ℝ) (m : ℂ) {W L k : ℕ} (u : ℝ)
    (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (X₁ X d τ : ℝ) (hd : 0 ≤ d) (hX₁ : 0 ≤ X₁)
    (hτ0 : 0 ≤ τ)
    (h1 : ∀ (c : Fin L) (s : Bool),
      ‖loopTr (resolventMat M (zChar g E m u)) ![c] ![s] - sgnScalar m s‖ ≤ X₁)
    (hX : ∀ (b : Fin (k + 1) → Fin L) (s : Fin (k + 1) → Bool),
      ‖loopTr (resolventMat M (zChar g E m u)) b s‖ ≤ X)
    (hτ : ∀ (b : Fin (k + 1) → Fin L) (s : Fin (k + 1) → Bool), d < wordDiam b →
      ‖loopTr (resolventMat M (zChar g E m u)) b s‖ ≤ τ)
    (a : Fin k → Fin L) (σ : Fin k → Bool) :
    ‖lightW g E m a σ u M‖ ≤ gammaG g * W * k * X₁ * ((2 * d + 1) * X + L * τ) := by
  have hγ : 0 ≤ gammaG g := by unfold gammaG; positivity
  unfold lightW
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hi : ∀ i : Fin k, ‖∑ c : Fin L,
      (loopTr (resolventMat M (zChar g E m u)) ![c] ![σ i] - sgnScalar m (σ i)) *
        loopTr (resolventMat M (zChar g E m u)) (insLab a i c) (insSgn σ i)‖ ≤
      X₁ * ((2 * d + 1) * X + L * τ) := by
    intro i
    refine sourceTail_prod _ _ _ _ hX₁ (fun c => h1 c (σ i)) ?_
    refine sourceTail_row (fun c => loopTr (resolventMat M (zChar g E m u)) (insLab a i c)
      (insSgn σ i)) (a i) X d τ hd hτ0 (fun c => hX _ _) fun c hc => hτ _ _ ?_
    refine sourceTail_far (insLab a i c) i.castSucc i.succ d ?_
    have e1 : insLab a i c i.castSucc = c := by simp [insLab]
    have e2 : insLab a i c i.succ = a i := by
      unfold insLab
      rw [← Fin.succAbove_castSucc_self i, Fin.insertNth_apply_succAbove]
    rwa [e1, e2]
  calc gammaG g * W * ‖∑ i : Fin k, ∑ c : Fin L,
        (loopTr (resolventMat M (zChar g E m u)) ![c] ![σ i] - sgnScalar m (σ i)) *
          loopTr (resolventMat M (zChar g E m u)) (insLab a i c) (insSgn σ i)‖
      ≤ gammaG g * W * ∑ _i : Fin k, (X₁ * ((2 * d + 1) * X + L * τ)) := by
        refine mul_le_mul_of_nonneg_left
          ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hi i)) (by positivity)
    _ = gammaG g * W * k * X₁ * ((2 * d + 1) * X + L * τ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ### The cut sources -/

/-- The linear cut source of (5.17) [fo:eq:error-hierarchy] after `Θ` is removed, with the free
label localized by the error factor: if `|𝒦_j| ≤ X^𝒦_j` for `3 ≤ j ≤ k`, and `|D_j| ≤ X_j`, at
most `τ` above diameter `d`, for `2 ≤ j < k`, then
`|cutSrcLin| ≤ k² Σ_{3 ≤ p ≤ k} X^𝒦_p ((2d + 1) X_{k+2-p} + L τ)` (the shorter linear cuts of
(C.32) [gc:eq:sourcetable]). -/
theorem cutSrcLin_tail_le {L k : ℕ} (K D : LoopFam L) (Xk X : ℕ → ℝ) (d τ : ℝ) (hd : 0 ≤ d)
    (hτ0 : 0 ≤ τ)
    (hK : ∀ j, 3 ≤ j → j ≤ k → ∀ (b : Fin j → Fin L) (s : Fin j → Bool), ‖K j b s‖ ≤ Xk j)
    (hD : ∀ j, 2 ≤ j → j < k → ∀ (b : Fin j → Fin L) (s : Fin j → Bool), ‖D j b s‖ ≤ X j)
    (hDτ : ∀ j, 2 ≤ j → j < k → ∀ (b : Fin j → Fin L) (s : Fin j → Bool), d < wordDiam b →
      ‖D j b s‖ ≤ τ)
    (a : Fin k → Fin L) (σ : Fin k → Bool) :
    ‖cutSrcLin K D a σ‖ ≤
      (k : ℝ) ^ 2 * ∑ p ∈ Finset.Icc 3 k, Xk p * ((2 * d + 1) * X (k + 2 - p) + L * τ) := by
  by_cases hk : k ≤ 2
  · have : Finset.Icc 3 k = ∅ := Finset.Icc_eq_empty (by omega)
    simp [cutSrcLin, hk, this]
  push Not at hk
  have hk0 : 0 < k := by omega
  set a0 : Fin L := a ⟨0, hk0⟩
  set F : ℕ → ℝ := fun p => Xk p * ((2 * d + 1) * X (k + 2 - p) + L * τ) with hF
  have hF0 : ∀ p ∈ Finset.Icc 3 k, 0 ≤ F p := by
    intro p hp
    rw [Finset.mem_Icc] at hp
    have h1 : 0 ≤ Xk p := (norm_nonneg _).trans (hK p hp.1 hp.2 (fun _ => a0) (fun _ => true))
    have h2 : 0 ≤ X (k + 2 - p) :=
      (norm_nonneg _).trans (hD (k + 2 - p) (by omega) (by omega) (fun _ => a0) (fun _ => true))
    exact mul_nonneg h1 (add_nonneg (mul_nonneg (by linarith) h2)
      (mul_nonneg (Nat.cast_nonneg _) hτ0))
  set Ftot := ∑ p ∈ Finset.Icc 3 k, F p with hFtot
  have hFtot0 : 0 ≤ Ftot := Finset.sum_nonneg hF0
  have hle : ∀ p, 3 ≤ p → p ≤ k → F p ≤ Ftot := fun p h3 h4 =>
    Finset.single_le_sum hF0 (Finset.mem_Icc.mpr ⟨h3, h4⟩)
  have hXK0 : ∀ p, 3 ≤ p → p ≤ k → 0 ≤ Xk p := fun p h3 h4 =>
    (norm_nonneg _).trans (hK p h3 h4 (fun _ => a0) (fun _ => true))
  have hKD : ∀ i j : Fin k, i < j → 3 ≤ k + i.val - j.val + 1 → k + i.val - j.val + 1 ≤ k →
      2 ≤ j.val - i.val + 1 → j.val - i.val + 1 < k →
      ‖∑ c, K _ (cutLLab a i j c) (cutLSgn σ i j) * D _ (cutRLab a i j c) (cutRSgn σ i j)‖ ≤
        Ftot := by
    intro i j hij h1 h2 h3 h4
    have hij' : i.val < j.val := hij
    have hjk := j.2
    refine (sourceTail_KD K D a σ i j hij (Xk (k + i.val - j.val + 1)) (X (j.val - i.val + 1)) d τ
      hd hτ0 (hXK0 _ h1 h2) (fun b s => hK _ h1 h2 b s) (fun b s => hD _ h3 h4 b s)
      (fun b s hb => hDτ _ h3 h4 b s hb)).trans ?_
    have e : k + 2 - (k + i.val - j.val + 1) = j.val - i.val + 1 := by omega
    have := hle _ h1 h2
    simp only [hF, e] at this
    exact this
  have hDK : ∀ i j : Fin k, i < j → 3 ≤ j.val - i.val + 1 → j.val - i.val + 1 ≤ k →
      2 ≤ k + i.val - j.val + 1 → k + i.val - j.val + 1 < k →
      ‖∑ c, D _ (cutLLab a i j c) (cutLSgn σ i j) * K _ (cutRLab a i j c) (cutRSgn σ i j)‖ ≤
        Ftot := by
    intro i j hij h1 h2 h3 h4
    have hij' : i.val < j.val := hij
    have hjk := j.2
    refine (sourceTail_DK K D a σ i j hij (Xk (j.val - i.val + 1)) (X (k + i.val - j.val + 1)) d τ
      hd hτ0 (hXK0 _ h1 h2) (fun b s => hK _ h1 h2 b s) (fun b s => hD _ h3 h4 b s)
      (fun b s hb => hDτ _ h3 h4 b s hb)).trans ?_
    have e : k + 2 - (j.val - i.val + 1) = k + i.val - j.val + 1 := by omega
    have := hle _ h1 h2
    simp only [hF, e] at this
    exact this
  have hpair : ∀ i j : Fin k, i < j →
      ‖∑ c : Fin L, (if j.val = i.val + 1 then
        K _ (cutLLab a i j c) (cutLSgn σ i j) * D _ (cutRLab a i j c) (cutRSgn σ i j)
      else if i.val = 0 ∧ j.val = k - 1 then
        D _ (cutLLab a i j c) (cutLSgn σ i j) * K _ (cutRLab a i j c) (cutRSgn σ i j)
      else
        K _ (cutLLab a i j c) (cutLSgn σ i j) * D _ (cutRLab a i j c) (cutRSgn σ i j) +
          D _ (cutLLab a i j c) (cutLSgn σ i j) * K _ (cutRLab a i j c) (cutRSgn σ i j))‖ ≤
        2 * Ftot := by
    intro i j hij
    have hij' : i.val < j.val := hij
    have hjk := j.2
    by_cases h1 : j.val = i.val + 1
    · simp only [h1, ite_true]
      have := hKD i j hij (by omega) (by omega) (by omega) (by omega)
      linarith
    · by_cases h2 : i.val = 0 ∧ j.val = k - 1
      · simp only [h1, ite_false]
        simp only [eq_true h2, ite_true]
        have := hDK i j hij (by omega) (by omega) (by omega) (by omega)
        linarith
      · simp only [h1, ite_false, eq_false h2]
        rw [Finset.sum_add_distrib]
        refine (norm_add_le _ _).trans ?_
        have e1 := hKD i j hij (by omega) (by omega) (by omega) (by omega)
        have e2 := hDK i j hij (by omega) (by omega) (by omega) (by omega)
        linarith
  unfold cutSrcLin
  simp only [eq_false (by omega : ¬ k ≤ 2), ite_false]
  refine (sourceTail_pairsum _ (2 * Ftot) (by linarith) hpair).trans (le_of_eq ?_)
  ring

/-- The quadratic cut source of (5.17) [fo:eq:error-hierarchy] with the free label localized: if
`|D_j| ≤ X_j`, and at most `τ` above diameter `d`, for `2 ≤ j ≤ k`, then
`|cutSrcQuad| ≤ k² Σ_{2 ≤ p ≤ k} X_p ((2d + 1) X_{k+2-p} + L τ)` (the quadratic row of (C.32)
[gc:eq:sourcetable]). -/
theorem cutSrcQuad_tail_le {L k : ℕ} (D : LoopFam L) (X : ℕ → ℝ) (d τ : ℝ) (hd : 0 ≤ d)
    (hτ0 : 0 ≤ τ)
    (hD : ∀ j, 2 ≤ j → j ≤ k → ∀ (b : Fin j → Fin L) (s : Fin j → Bool), ‖D j b s‖ ≤ X j)
    (hDτ : ∀ j, 2 ≤ j → j ≤ k → ∀ (b : Fin j → Fin L) (s : Fin j → Bool), d < wordDiam b →
      ‖D j b s‖ ≤ τ)
    (a : Fin k → Fin L) (σ : Fin k → Bool) :
    ‖cutSrcQuad D a σ‖ ≤
      (k : ℝ) ^ 2 * ∑ p ∈ Finset.Icc 2 k, X p * ((2 * d + 1) * X (k + 2 - p) + L * τ) := by
  by_cases hk : k < 2
  · have : Finset.Icc 2 k = ∅ := Finset.Icc_eq_empty (by omega)
    have h0 : ∀ i j : Fin k, ¬ i < j := fun i j => by
      have := i.2; have := j.2; intro h; have : i.val < j.val := h; omega
    simp [cutSrcQuad, cutSumFam, h0, this]
  push Not at hk
  have hk0 : 0 < k := by omega
  set a0 : Fin L := a ⟨0, hk0⟩
  set F : ℕ → ℝ := fun p => X p * ((2 * d + 1) * X (k + 2 - p) + L * τ) with hF
  have hX0 : ∀ p, 2 ≤ p → p ≤ k → 0 ≤ X p := fun p h3 h4 =>
    (norm_nonneg _).trans (hD p h3 h4 (fun _ => a0) (fun _ => true))
  have hF0 : ∀ p ∈ Finset.Icc 2 k, 0 ≤ F p := by
    intro p hp
    rw [Finset.mem_Icc] at hp
    exact mul_nonneg (hX0 p hp.1 hp.2) (add_nonneg (mul_nonneg (by linarith)
      (hX0 _ (by omega) (by omega))) (mul_nonneg (Nat.cast_nonneg _) hτ0))
  set Ftot := ∑ p ∈ Finset.Icc 2 k, F p with hFtot
  have hFtot0 : 0 ≤ Ftot := Finset.sum_nonneg hF0
  have hle : ∀ p, 2 ≤ p → p ≤ k → F p ≤ Ftot := fun p h3 h4 =>
    Finset.single_le_sum hF0 (Finset.mem_Icc.mpr ⟨h3, h4⟩)
  have hpair : ∀ i j : Fin k, i < j →
      ‖∑ c : Fin L, D _ (cutLLab a i j c) (cutLSgn σ i j) *
        D _ (cutRLab a i j c) (cutRSgn σ i j)‖ ≤ Ftot := by
    intro i j hij
    have hij' : i.val < j.val := hij
    have hjk := j.2
    have h1 : 2 ≤ k + i.val - j.val + 1 := by omega
    have h2 : k + i.val - j.val + 1 ≤ k := by omega
    have h3 : 2 ≤ j.val - i.val + 1 := by omega
    have h4 : j.val - i.val + 1 ≤ k := by omega
    refine (sourceTail_KD D D a σ i j hij (X (k + i.val - j.val + 1)) (X (j.val - i.val + 1)) d τ
      hd hτ0 (hX0 _ h1 h2) (fun b s => hD _ h1 h2 b s) (fun b s => hD _ h3 h4 b s)
      (fun b s hb => hDτ _ h3 h4 b s hb)).trans ?_
    have e : k + 2 - (k + i.val - j.val + 1) = j.val - i.val + 1 := by omega
    have := hle _ h1 h2
    simp only [hF, e] at this
    exact this
  unfold cutSrcQuad cutSumFam
  refine (sourceTail_pairsum _ Ftot hFtot0 hpair).trans ?_
  have : (0 : ℝ) ≤ (k : ℝ) ^ 2 := by positivity
  nlinarith

/-! ### Words as lists of signed labels -/

/-- The factor `X^{s} E_x` of a loop for a signed label. -/
private def stF {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (p : Bool × Fin L) :
    Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  sgnMat G p.1 * blockE W L p.2

/-- The ordered product of the factors of a list of signed labels. -/
private def stProd {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (l : List (Bool × Fin L)) : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  (l.map (stF G)).prod

private lemma stProd_append {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (l l' : List (Bool × Fin L)) : stProd G (l ++ l') = stProd G l * stProd G l' := by
  simp [stProd]

private lemma stProd_cons {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (p : Bool × Fin L) (l : List (Bool × Fin L)) : stProd G (p :: l) = stF G p * stProd G l := by
  simp [stProd]

/-- A list of signed labels of length `n` is a loop word of length `n` with the same trace. -/
private lemma sourceTail_ofList {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (P : List (Bool × Fin L)) (n : ℕ) (hn : P.length = n) :
    ∃ (w : Fin n → Fin L) (s : Fin n → Bool), loopTr G w s = (stProd G P).trace ∧
      ∀ x ∈ P, ∃ p, w p = x.2 := by
  subst hn
  refine ⟨fun p => (P.get p).2, fun p => (P.get p).1, ?_, ?_⟩
  · unfold loopTr stProd
    congr 2
    apply List.ext_getElem <;> simp [stF]
  · intro x hx
    obtain ⟨p, hp⟩ := List.mem_iff_get.mp hx
    exact ⟨p, by simp only [← hp]⟩

private lemma sourceTail_blockE_conj {W L : ℕ} (c : Fin L) : (blockE W L c)ᴴ = blockE W L c := by
  rw [blockE, Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  by_cases h : p.1 = c <;> simp [h]

private lemma sourceTail_sgn_conj {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (s : Bool) : (sgnMat G s)ᴴ = sgnMat G (!s) := by
  cases s <;> simp [sgnMat]

/-- The conjugate transpose of a list product is the product over the reversed list of the
conjugate factors. -/
private lemma stProd_conj {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (l : List (Bool × Fin L)) :
    (stProd G l)ᴴ = (l.reverse.map fun p => blockE W L p.2 * sgnMat G (!p.1)).prod := by
  induction l with
  | nil => simp [stProd]
  | cons p l ih =>
    rw [stProd_cons, Matrix.conjTranspose_mul, ih, List.reverse_cons, List.map_append,
      List.prod_append]
    simp [stF, sourceTail_blockE_conj, sourceTail_sgn_conj]

/-- Signs shifted by one position along a list. -/
private def stSh {L : ℕ} : Bool → List (Bool × Fin L) → List (Bool × Fin L)
  | _, [] => []
  | t, p :: r => (t, p.2) :: stSh (!p.1) r

/-- The last shifted sign. -/
private def stLst {L : ℕ} : Bool → List (Bool × Fin L) → Bool
  | t, [] => t
  | _, p :: r => stLst (!p.1) r

private lemma stSh_length {L : ℕ} (t : Bool) (r : List (Bool × Fin L)) :
    (stSh t r).length = r.length := by
  induction r generalizing t with
  | nil => rfl
  | cons p r ih => simp [stSh, ih]

private lemma stRegroup {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (r : List (Bool × Fin L)) : ∀ t : Bool,
    sgnMat G t * (r.map fun p => blockE W L p.2 * sgnMat G (!p.1)).prod =
      stProd G (stSh t r) * sgnMat G (stLst t r) := by
  induction r with
  | nil => intro t; simp [stSh, stLst, stProd]
  | cons p r ih =>
    intro t
    have h := ih (!p.1)
    simp only [stSh, stLst, stProd_cons, List.map_cons, List.prod_cons, stF]
    simp only [stProd] at h
    calc sgnMat G t * (blockE W L p.2 * sgnMat G (!p.1) *
          (r.map fun p => blockE W L p.2 * sgnMat G (!p.1)).prod)
        = sgnMat G t * blockE W L p.2 * (sgnMat G (!p.1) *
          (r.map fun p => blockE W L p.2 * sgnMat G (!p.1)).prod) := by simp only [mul_assoc]
      _ = _ := by rw [h]; simp only [mul_assoc, stProd]

/-- The signed labels of the word `a`, `σ` read cyclically from position `i`. -/
private def stRead {L k : ℕ} (a : Fin k → Fin L) (σ : Fin k → Bool) (i : Fin k) :
    List (Bool × Fin L) :=
  List.ofFn fun p : Fin k => (σ (i + p), a (i + p))

private lemma stRead_length {L k : ℕ} (a : Fin k → Fin L) (σ : Fin k → Bool) (i : Fin k) :
    (stRead a σ i).length = k := by simp [stRead]

private lemma loopB_eq_stProd {W L k : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a : Fin k → Fin L) (σ : Fin k → Bool) (i : Fin k) :
    loopB G a σ i = stProd G (stRead a σ i) * sgnMat G (σ i) := by
  unfold loopB stProd stRead
  rw [List.map_ofFn]
  rfl

/-- One term of the bracket sum as a loop of length `k + k' + 2` containing the summed label and a
label of the first word. -/
private lemma sourceTail_bracket_term {W L k k' : ℕ}
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a : Fin k → Fin L) (σ : Fin k → Bool)
    (a' : Fin k' → Fin L) (σ' : Fin k' → Bool) (i : Fin k) (j : Fin k') (c : Fin L) :
    ∃ (w : Fin (k + k' + 2) → Fin L) (s : Fin (k + k' + 2) → Bool),
      (((W : ℂ) • blockE W L c) * loopB G a σ i * ((W : ℂ) • blockE W L c) *
        (loopB G a' σ' j)ᴴ).trace = (W : ℂ) ^ 2 * loopTr G w s ∧
      (∃ p, w p = c) ∧ ∃ q, w q = a (i + ⟨0, Fin.pos i⟩) := by
  set A := stRead a σ i with hA
  set A' := stRead a' σ' j with hA'
  set t0 : Bool := !σ' j
  set ℓ := stLst t0 A'.reverse
  set P : List (Bool × Fin L) := (ℓ, c) :: (A ++ ((σ i, c) :: stSh t0 A'.reverse)) with hP
  have hlen : P.length = k + k' + 2 := by
    simp [hP, hA, stRead_length, stSh_length, hA', stRead_length]
    ring
  obtain ⟨w, s, hw, hmem⟩ := sourceTail_ofList G P _ hlen
  refine ⟨w, s, ?_, ?_, ?_⟩
  · rw [hw]
    have hB : (loopB G a' σ' j)ᴴ =
        sgnMat G t0 * (A'.reverse.map fun p => blockE W L p.2 * sgnMat G (!p.1)).prod := by
      rw [loopB_eq_stProd, Matrix.conjTranspose_mul, ← hA', stProd_conj, sourceTail_sgn_conj]
    rw [hB, stRegroup, loopB_eq_stProd, ← hA]
    set Ec := blockE W L c
    set Sl := sgnMat G ℓ
    have e1 : (((W : ℂ) • Ec) * (stProd G A * sgnMat G (σ i)) * ((W : ℂ) • Ec) *
        (stProd G (stSh t0 A'.reverse) * Sl)) =
        (W : ℂ) ^ 2 •
          (Ec * (stProd G A * sgnMat G (σ i) * Ec * stProd G (stSh t0 A'.reverse)) * Sl) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      congr 1
      ring
    rw [e1, Matrix.trace_smul, Matrix.trace_mul_comm]
    simp only [hP, stProd_cons, stProd_append, stF, smul_eq_mul, Matrix.mul_assoc]
    rfl
  · exact hmem (ℓ, c) (by simp [hP])
  · refine hmem (σ (i + ⟨0, Fin.pos i⟩), a (i + ⟨0, Fin.pos i⟩)) ?_
    simp only [hP, List.mem_cons, List.mem_append]
    right; left
    simp only [hA, stRead, List.mem_ofFn]
    exact ⟨⟨0, Fin.pos i⟩, rfl⟩

/-! ### The bracket -/

/-- The bracket (5.9) [gc:eq:bracket] of two loops with the joined label localized: if every loop
of length `k + k' + 2` is at most `X`, and at most `τ` above diameter `d`, then
`|Γ(ℒ_k, ℒ_{k'})| ≤ γ W k k' ((2d + 1) X + L τ)` (the cross bracket of (C.32)
[gc:eq:sourcetable]). -/
theorem blockGamma_loopTr_tail_le (g E : ℝ) (m : ℂ) (hm : 0 < m.im) {W L k k' : ℕ} {u : ℝ}
    (hu : u < 1) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    (X d τ : ℝ) (hd : 0 ≤ d) (hτ0 : 0 ≤ τ)
    (hX : ∀ (b : Fin (k + k' + 2) → Fin L) (s : Fin (k + k' + 2) → Bool),
      ‖loopTr (resolventMat M (zChar g E m u)) b s‖ ≤ X)
    (hτ : ∀ (b : Fin (k + k' + 2) → Fin L) (s : Fin (k + k' + 2) → Bool), d < wordDiam b →
      ‖loopTr (resolventMat M (zChar g E m u)) b s‖ ≤ τ)
    (a : Fin k → Fin L) (σ : Fin k → Bool) (a' : Fin k' → Fin L) (σ' : Fin k' → Bool) :
    ‖blockGamma W L (gammaG g) (resLoop g E m a σ u) (resLoop g E m a' σ' u) M‖ ≤
      gammaG g * W * k * k' * ((2 * d + 1) * X + L * τ) := by
  rw [blockGamma_loopTr g E m hm hu hM a σ a' σ']
  set G := resolventMat M (zChar g E m u) with hG
  have hγ : 0 ≤ gammaG g := by unfold gammaG; positivity
  have hrow : ∀ (i : Fin k) (j : Fin k'), ∑ c : Fin L, ‖(((W : ℂ) • blockE W L c) *
      loopB G a σ i * ((W : ℂ) • blockE W L c) * (loopB G a' σ' j)ᴴ).trace‖ ≤
        (W : ℝ) ^ 2 * ((2 * d + 1) * X + L * τ) := by
    intro i j
    have hW2 : (0 : ℝ) ≤ (W : ℝ) ^ 2 := by positivity
    have h := sourceTail_row (fun c : Fin L => (((W : ℂ) • blockE W L c) *
      loopB G a σ i * ((W : ℂ) • blockE W L c) * (loopB G a' σ' j)ᴴ).trace)
      (a (i + ⟨0, Fin.pos i⟩)) ((W : ℝ) ^ 2 * X) d ((W : ℝ) ^ 2 * τ) hd (mul_nonneg hW2 hτ0)
      (fun c => by
        obtain ⟨w, s, hw, -⟩ := sourceTail_bracket_term G a σ a' σ' i j c
        simp only [hw, norm_mul, norm_pow, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left (hX w s) hW2)
      (fun c hc => by
        obtain ⟨w, s, hw, ⟨p, hp⟩, ⟨q, hq⟩⟩ := sourceTail_bracket_term G a σ a' σ' i j c
        simp only [hw, norm_mul, norm_pow, Complex.norm_natCast]
        refine mul_le_mul_of_nonneg_left (hτ w s (sourceTail_far w p q d ?_)) hW2
        rwa [hp, hq])
    refine h.trans (le_of_eq ?_)
    ring
  have hsum : ‖∑ c : Fin L, ∑ i : Fin k, ∑ j : Fin k', (((W : ℂ) • blockE W L c) *
      loopB G a σ i * ((W : ℂ) • blockE W L c) * (loopB G a' σ' j)ᴴ).trace‖ ≤
      k * k' * ((W : ℝ) ^ 2 * ((2 * d + 1) * X + L * τ)) := by
    calc _ ≤ ∑ c : Fin L, ∑ i : Fin k, ∑ j : Fin k', ‖(((W : ℂ) • blockE W L c) *
          loopB G a σ i * ((W : ℂ) • blockE W L c) * (loopB G a' σ' j)ᴴ).trace‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ =>
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _))
      _ = ∑ i : Fin k, ∑ j : Fin k', ∑ c : Fin L, ‖(((W : ℂ) • blockE W L c) *
          loopB G a σ i * ((W : ℂ) • blockE W L c) * (loopB G a' σ' j)ᴴ).trace‖ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
      _ ≤ ∑ _i : Fin k, ∑ _j : Fin k', (W : ℝ) ^ 2 * ((2 * d + 1) * X + L * τ) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hrow i j
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine (mul_le_mul_of_nonneg_left hsum (by positivity)).trans (le_of_eq ?_)
  by_cases hW : (W : ℝ) = 0
  · simp [hW]
  · field_simp

/-! ### The commutator bound for complex rows -/

private lemma sourceTail_prod_sum {L k : ℕ} (θ : Fin L → ℝ) (hθ1 : ∑ x, θ x = 1) (c : Fin L) :
    ∑ as : Fin k → Fin L, ∏ j, θ (c - as j) = 1 := by
  have : NeZero L := ⟨by rintro rfl; exact c.elim0⟩
  have h1 : ∑ x, θ (c - x) = 1 := by
    rw [← hθ1]
    exact Fintype.sum_equiv (Equiv.subLeft c) _ _ (fun x => rfl)
  rw [← Fintype.sum_pow (fun x => θ (c - x)) k, h1, one_pow]

/-- (6.5) [da:eq:commutator-bound] for a complex row `h`: with `K ≥ 0` of row `(1 - v)⁻¹`, a
probability profile `θ ≤ C_θ/ℓ` and `|h| ≤ H`, the commutator (6.4) [gc:eq:commutator] has zero
row and is at most `2C_θ^k H/((1 - v)ℓ^k)`. -/
theorem commutator_bound_cplx {L k : ℕ} (K : Matrix (Fin L) (Fin L) ℝ) (θ : Fin L → ℝ)
    (h : Fin L → ℂ) (v Cθ ℓ H : ℝ) (hK : ∀ a b, 0 ≤ K a b) (hrow : ∀ a, ∑ b, K a b = (1 - v)⁻¹)
    (hv : v < 1) (hθ0 : ∀ x, 0 ≤ θ x) (hθ1 : ∑ x, θ x = 1) (hθC : ∀ x, θ x ≤ Cθ / ℓ)
    (hℓ : 0 < ℓ) (hh : ∀ c, ‖h c‖ ≤ H) :
    (∀ a₁, ∑ as : Fin k → Fin L, ∑ c, ((K a₁ c : ℝ) : ℂ) * h c *
        (∏ j, ((θ (c - as j) : ℝ) : ℂ) - ∏ j, ((θ (a₁ - as j) : ℝ) : ℂ)) = 0) ∧
      ∀ a₁ (as : Fin k → Fin L), ‖∑ c, ((K a₁ c : ℝ) : ℂ) * h c *
        (∏ j, ((θ (c - as j) : ℝ) : ℂ) - ∏ j, ((θ (a₁ - as j) : ℝ) : ℂ))‖ ≤
          2 * Cθ ^ k * H / ((1 - v) * ℓ ^ k) := by
  have hc : ∀ c : Fin L, ∑ as : Fin k → Fin L, ∏ j, ((θ (c - as j) : ℝ) : ℂ) = 1 := by
    intro c
    have h2 := sourceTail_prod_sum (k := k) θ hθ1 c
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h2
  refine ⟨fun a₁ => ?_, fun a₁ as => ?_⟩
  · rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun c _ => ?_
    simp_rw [← Finset.mul_sum, Finset.sum_sub_distrib, hc c, hc a₁, sub_self, mul_zero]
  · have hCℓ : 0 ≤ Cθ / ℓ := le_trans (hθ0 a₁) (hθC a₁)
    have hH : 0 ≤ H := le_trans (norm_nonneg _) (hh a₁)
    have hv1 : 0 < 1 - v := by linarith
    have hprod : ∀ c : Fin L, 0 ≤ ∏ j : Fin k, θ (c - as j) ∧
        ∏ j : Fin k, θ (c - as j) ≤ (Cθ / ℓ) ^ k := by
      intro c
      refine ⟨Finset.prod_nonneg fun j _ => hθ0 _, ?_⟩
      calc ∏ j : Fin k, θ (c - as j) ≤ ∏ _j : Fin k, (Cθ / ℓ) :=
            Finset.prod_le_prod₀ (fun j _ => hθ0 _) (fun j _ => hθC _)
        _ = (Cθ / ℓ) ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hterm : ∀ c, ‖((K a₁ c : ℝ) : ℂ) * h c *
        (∏ j, ((θ (c - as j) : ℝ) : ℂ) - ∏ j, ((θ (a₁ - as j) : ℝ) : ℂ))‖ ≤
        K a₁ c * (H * (Cθ / ℓ) ^ k) := by
      intro c
      obtain ⟨h1, h2⟩ := hprod c
      obtain ⟨h3, h4⟩ := hprod a₁
      have hd : ‖(∏ j, ((θ (c - as j) : ℝ) : ℂ) - ∏ j, ((θ (a₁ - as j) : ℝ) : ℂ))‖ ≤
          (Cθ / ℓ) ^ k := by
        rw [← Complex.ofReal_prod, ← Complex.ofReal_prod, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs, abs_le]
        constructor <;> linarith
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hK a₁ c), mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (hK a₁ c)
      exact mul_le_mul (hh c) hd (norm_nonneg _) hH
    calc _ ≤ ∑ c, K a₁ c * (H * (Cθ / ℓ) ^ k) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => hterm c)
      _ = (1 - v)⁻¹ * (H * (Cθ / ℓ) ^ k) := by rw [← Finset.sum_mul, hrow]
      _ ≤ 2 * Cθ ^ k * H / ((1 - v) * ℓ ^ k) := by
          have e : 2 * Cθ ^ k * H / ((1 - v) * ℓ ^ k) = 2 * ((1 - v)⁻¹ * (H * (Cθ / ℓ) ^ k)) := by
            rw [div_pow]
            field_simp
          rw [e]
          have : 0 ≤ (1 - v)⁻¹ * (H * (Cθ / ℓ) ^ k) := by positivity
          linarith

/-! ### The chain bound -/

/-- The unnormalized projection onto block `x`. -/
private def stP (W L : ℕ) (x : Fin L) : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  Matrix.diagonal fun p => if p.1 = x then 1 else 0

private lemma stP_mul_self {W L : ℕ} (x : Fin L) : stP W L x * stP W L x = stP W L x := by
  unfold stP
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  by_cases h : p.1 = x <;> simp [h]

private lemma stP_conj {W L : ℕ} (x : Fin L) : (stP W L x)ᴴ = stP W L x := by
  rw [stP, Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  by_cases h : p.1 = x <;> simp [h]

private lemma blockE_eq_stP {W L : ℕ} (x : Fin L) :
    blockE W L x = ((W : ℂ)⁻¹) • stP W L x := by
  ext p q
  by_cases h : p = q
  · subst h
    by_cases h1 : p.1 = x <;> simp [blockE, stP, h1]
  · simp [blockE, stP, h]

/-- The product of the unnormalized factors `X^{s} P_x` of a list of signed labels. -/
private def stQ {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (l : List (Bool × Fin L)) : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  (l.map fun p => sgnMat G p.1 * stP W L p.2).prod

private lemma stQ_append {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (l l' : List (Bool × Fin L)) : stQ G (l ++ l') = stQ G l * stQ G l' := by
  simp [stQ]

private lemma stQ_cons {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (p : Bool × Fin L) (l : List (Bool × Fin L)) :
    stQ G (p :: l) = (sgnMat G p.1 * stP W L p.2) * stQ G l := by
  simp [stQ]

private lemma stProd_eq_stQ {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (l : List (Bool × Fin L)) :
    stProd G l = ((W : ℂ)⁻¹) ^ l.length • stQ G l := by
  induction l with
  | nil => simp [stProd, stQ]
  | cons p l ih =>
    rw [stProd_cons, stQ_cons, ih, stF, blockE_eq_stP, List.length_cons, pow_succ]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]

private lemma stQ_absorb {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (l : List (Bool × Fin L)) (p : Bool × Fin L) :
    stQ G (l ++ [p]) * stP W L p.2 = stQ G (l ++ [p]) := by
  rw [stQ_append]
  simp only [stQ, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Matrix.mul_assoc, stP_mul_self]

private lemma stQ_conj {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (l : List (Bool × Fin L)) :
    (stQ G l)ᴴ = (l.reverse.map fun p => stP W L p.2 * sgnMat G (!p.1)).prod := by
  induction l with
  | nil => simp [stQ]
  | cons p l ih =>
    rw [stQ_cons, Matrix.conjTranspose_mul, ih, List.reverse_cons, List.map_append,
      List.prod_append]
    simp [stP_conj, sourceTail_sgn_conj]

/-- Shifted signs followed by a final label. -/
private def stTl {L : ℕ} : Bool → List (Bool × Fin L) → Fin L → List (Bool × Fin L)
  | t, [], e => [(t, e)]
  | t, p :: r, e => (t, p.2) :: stTl (!p.1) r e

private lemma stTl_length {L : ℕ} (r : List (Bool × Fin L)) (e : Fin L) :
    ∀ t, (stTl t r e).length = r.length + 1 := by
  induction r with
  | nil => intro t; rfl
  | cons p r ih => intro t; simp [stTl, ih]

private lemma stTl_regroup {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (e : Fin L)
    (r : List (Bool × Fin L)) : ∀ t : Bool,
    sgnMat G t * (r.map fun p => stP W L p.2 * sgnMat G (!p.1)).prod * stP W L e =
      stQ G (stTl t r e) := by
  induction r with
  | nil => intro t; simp [stTl, stQ]
  | cons p r ih =>
    intro t
    have h := ih (!p.1)
    simp only [stTl, stQ_cons, List.map_cons, List.prod_cons]
    rw [← h]
    simp only [Matrix.mul_assoc]

/-- Hilbert–Schmidt square: the sum of the squared moduli of the entries. -/
private def stHsq {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

private lemma stHsq_nonneg {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) : 0 ≤ stHsq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma stHsq_trace {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    (A * Aᴴ).trace = ((stHsq A : ℝ) : ℂ) := by
  simp only [stHsq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def, Complex.mul_conj', Complex.ofReal_sum, Complex.ofReal_pow]

private lemma stHsq_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) :
    stHsq (A * B) ≤ stHsq A * stHsq B := by
  have hB : stHsq B = ∑ j, ∑ l, ‖B l j‖ ^ 2 := Finset.sum_comm
  have h : stHsq A * stHsq B = ∑ i, ∑ j, (∑ l, ‖A i l‖ ^ 2) * ∑ l, ‖B l j‖ ^ 2 := by
    rw [hB, stHsq, Finset.sum_mul_sum]
  rw [h]
  unfold stHsq
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  rw [Matrix.mul_apply]
  calc ‖∑ l, A i l * B l j‖ ^ 2 ≤ (∑ l, ‖A i l‖ * ‖B l j‖) ^ 2 := by
        gcongr
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp only [norm_mul]
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

private lemma stHsq_trace_le {ι : Type*} [Fintype ι] (C C' : Matrix ι ι ℂ) :
    ‖(C * C').trace‖ ^ 2 ≤ stHsq C * stHsq C' := by
  have h1 : ‖(C * C').trace‖ ≤ ∑ x : ι × ι, ‖C x.1 x.2‖ * ‖C' x.2 x.1‖ := by
    rw [Fintype.sum_prod_type]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp only [norm_mul]
  have h2 : stHsq C' = ∑ x : ι × ι, ‖C' x.2 x.1‖ ^ 2 := by
    rw [Fintype.sum_prod_type, stHsq, Finset.sum_comm]
  have h3 : stHsq C = ∑ x : ι × ι, ‖C x.1 x.2‖ ^ 2 := by
    rw [Fintype.sum_prod_type, stHsq]
  rw [h2, h3]
  calc ‖(C * C').trace‖ ^ 2 ≤ (∑ x : ι × ι, ‖C x.1 x.2‖ * ‖C' x.2 x.1‖) ^ 2 := by gcongr
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

private lemma stQ_eq_stProd {W L : ℕ} (hW : W ≠ 0)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (l : List (Bool × Fin L)) :
    stQ G l = (W : ℂ) ^ l.length • stProd G l := by
  rw [stProd_eq_stQ, smul_smul, ← mul_pow, mul_inv_cancel₀ (by exact_mod_cast hW), one_pow,
    one_smul]

/-- The squared Hilbert–Schmidt norm of a chain `P_e X^{s_1}P_{x_1} ⋯ X^{s_l}P_{x_l}` is `W^{2l}`
times a loop of length `2l`. -/
private lemma stHS {W L : ℕ} (hW : W ≠ 0) (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (e : Fin L) (l' : List (Bool × Fin L)) (p : Bool × Fin L) (n : ℕ) (hn : l'.length + 1 = n) :
    ∃ (w : Fin (2 * n) → Fin L) (s : Fin (2 * n) → Bool),
      ((stP W L e * stQ G (l' ++ [p])) * (stP W L e * stQ G (l' ++ [p]))ᴴ).trace =
        (W : ℂ) ^ (2 * n) * loopTr G w s := by
  set l := l' ++ [p] with hl
  set P := l ++ stTl (!p.1) l'.reverse e with hP
  have hlen : P.length = 2 * n := by
    simp [hP, hl, stTl_length]
    omega
  obtain ⟨w, s, hw, -⟩ := sourceTail_ofList G P _ hlen
  refine ⟨w, s, ?_⟩
  rw [hw]
  have hrev : l.reverse = p :: l'.reverse := by simp [hl]
  have hconj : (stQ G l)ᴴ = (stP W L p.2 * sgnMat G (!p.1)) *
      (l'.reverse.map fun p => stP W L p.2 * sgnMat G (!p.1)).prod := by
    rw [stQ_conj, hrev]
    simp
  have key : stQ G l * ((stQ G l)ᴴ * stP W L e) = stQ G P := by
    rw [hconj, hP, stQ_append G l, ← stTl_regroup G e l'.reverse (!p.1)]
    calc stQ G l * (stP W L p.2 * sgnMat G (!p.1) *
          (l'.reverse.map fun p => stP W L p.2 * sgnMat G (!p.1)).prod * stP W L e)
        = (stQ G l * stP W L p.2) * (sgnMat G (!p.1) *
          (l'.reverse.map fun p => stP W L p.2 * sgnMat G (!p.1)).prod * stP W L e) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hl, stQ_absorb]
  have e1 : ((stP W L e * stQ G l) * (stP W L e * stQ G l)ᴴ).trace = (stQ G P).trace := by
    rw [Matrix.conjTranspose_mul, stP_conj, ← key]
    calc _ = (stP W L e * (stQ G l * ((stQ G l)ᴴ * stP W L e))).trace := by
          simp only [Matrix.mul_assoc]
      _ = ((stQ G l * ((stQ G l)ᴴ * stP W L e)) * stP W L e).trace := Matrix.trace_mul_comm _ _
      _ = (stQ G l * ((stQ G l)ᴴ * stP W L e)).trace := by
          congr 1
          simp only [Matrix.mul_assoc, stP_mul_self]
  rw [e1, stQ_eq_stProd hW, Matrix.trace_smul, hlen, smul_eq_mul]

private lemma stHS_bound {W L : ℕ} (hW : W ≠ 0) (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (e : Fin L) (l' : List (Bool × Fin L)) (p : Bool × Fin L) (n : ℕ) (hn : l'.length + 1 = n)
    (X : ℝ) (hX : ∀ (w : Fin (2 * n) → Fin L) (s : Fin (2 * n) → Bool), ‖loopTr G w s‖ ≤ X) :
    stHsq (stP W L e * stQ G (l' ++ [p])) ≤ (W : ℝ) ^ (2 * n) * X := by
  obtain ⟨w, s, h⟩ := stHS hW G e l' p n hn
  rw [stHsq_trace] at h
  have h1 : stHsq (stP W L e * stQ G (l' ++ [p])) =
      ‖(W : ℂ) ^ (2 * n) * loopTr G w s‖ := by
    rw [← h, Complex.norm_real, Real.norm_of_nonneg (stHsq_nonneg _)]
  rw [h1, norm_mul, norm_pow, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (hX w s) (by positivity)

private lemma stSplit4 {α : Type*} (pl : List α) (l₁ l₂ : ℕ)
    (h : pl.length = l₁ + l₂ + (l₁ + l₂)) :
    ∃ u₁ u₂ v₁ v₂ : List α, pl = u₁ ++ u₂ ++ v₁ ++ v₂ ∧ u₁.length = l₁ ∧ u₂.length = l₂ ∧
      v₁.length = l₁ ∧ v₂.length = l₂ := by
  refine ⟨pl.take l₁, (pl.drop l₁).take l₂, ((pl.drop l₁).drop l₂).take l₁,
    ((pl.drop l₁).drop l₂).drop l₁, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.append_assoc, List.take_append_drop]
  · simp; omega
  · simp; omega
  · simp; omega
  · simp; omega

private lemma stLastSplit {α : Type*} (l : List α) (h : 1 ≤ l.length) :
    ∃ (l' : List α) (p : α), l = l' ++ [p] ∧ l'.length + 1 = l.length := by
  have hne : l ≠ [] := by rintro rfl; simp at h
  refine ⟨l.dropLast, l.getLast hne, (List.dropLast_append_getLast hne).symm, ?_⟩
  simp
  omega

/-- The chain bound (C.40) [gc:eq:chain] by trace Cauchy–Schwarz: if every loop of length `2l₁`
is at most `X₁` and every loop of length `2l₂` at most `X₂`, then every loop of length
`2(l₁ + l₂)` is at most `X₁ X₂`. -/
theorem loopTr_chain {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (l₁ l₂ : ℕ)
    (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂) (X₁ X₂ : ℝ)
    (h₁ : ∀ (b : Fin (2 * l₁) → Fin L) (s : Fin (2 * l₁) → Bool), ‖loopTr G b s‖ ≤ X₁)
    (h₂ : ∀ (b : Fin (2 * l₂) → Fin L) (s : Fin (2 * l₂) → Bool), ‖loopTr G b s‖ ≤ X₂)
    (b : Fin (2 * (l₁ + l₂)) → Fin L) (s : Fin (2 * (l₁ + l₂)) → Bool) :
    ‖loopTr G b s‖ ≤ X₁ * X₂ := by
  by_cases hW : W = 0
  · subst hW
    have h0 : loopTr G b s = 0 := by simp [loopTr, Matrix.trace]
    rw [h0, norm_zero]
    have hi : 0 < 2 * (l₁ + l₂) := by omega
    have hi1 : 0 < 2 * l₁ := by omega
    have hi2 : 0 < 2 * l₂ := by omega
    have hL : Fin L := b ⟨0, hi⟩
    exact mul_nonneg ((norm_nonneg _).trans (h₁ (fun _ => hL) (fun _ => true)))
      ((norm_nonneg _).trans (h₂ (fun _ => hL) (fun _ => true)))
  have hWpos : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero hW
  set pl : List (Bool × Fin L) := List.ofFn fun p => (s p, b p) with hpl
  have hloop : loopTr G b s = (stProd G pl).trace := by
    unfold loopTr stProd
    rw [hpl, List.map_ofFn]
    rfl
  have hplen : pl.length = l₁ + l₂ + (l₁ + l₂) := by
    simp [hpl]
    omega
  obtain ⟨u₁, u₂, v₁, v₂, hsplit, h1, h2, h3, h4⟩ := stSplit4 pl l₁ l₂ hplen
  obtain ⟨u₁', p₁, hu₁e, hu₁⟩ := stLastSplit u₁ (by omega)
  obtain ⟨u₂', p₂, hu₂e, hu₂⟩ := stLastSplit u₂ (by omega)
  obtain ⟨v₁', q₁, hv₁e, hv₁⟩ := stLastSplit v₁ (by omega)
  obtain ⟨v₂', q₂, hv₂e, hv₂⟩ := stLastSplit v₂ (by omega)
  subst hu₁e hu₂e hv₁e hv₂e
  set a := stQ G (u₁' ++ [p₁]) with ha
  set a₂ := stQ G (u₂' ++ [p₂]) with ha₂
  set b₁ := stQ G (v₁' ++ [q₁]) with hb₁
  set b₂ := stQ G (v₂' ++ [q₂]) with hb₂
  have hQ : stQ G pl = a * a₂ * b₁ * b₂ := by
    rw [hsplit, stQ_append, stQ_append, stQ_append]
  have habs₁ : a * stP W L p₁.2 = a := stQ_absorb G u₁' p₁
  have habs₂ : a₂ * stP W L p₂.2 = a₂ := stQ_absorb G u₂' p₂
  have habs₃ : b₁ * stP W L q₁.2 = b₁ := stQ_absorb G v₁' q₁
  have habs₄ : b₂ * stP W L q₂.2 = b₂ := stQ_absorb G v₂' q₂
  set A := stP W L q₂.2 * a with hA
  set B := stP W L p₁.2 * a₂ with hB
  set A' := stP W L p₂.2 * b₁ with hA'
  set B' := stP W L q₁.2 * b₂ with hB'
  have hC : A * B = stP W L q₂.2 * (a * a₂) := by
    calc A * B = stP W L q₂.2 * ((a * stP W L p₁.2) * a₂) := by simp only [hA, hB, Matrix.mul_assoc]
      _ = _ := by rw [habs₁]
  have hC' : A' * B' = stP W L p₂.2 * (b₁ * b₂) := by
    calc A' * B' = stP W L p₂.2 * ((b₁ * stP W L q₁.2) * b₂) := by
          simp only [hA', hB', Matrix.mul_assoc]
      _ = _ := by rw [habs₃]
  have hCC : ((A * B) * (A' * B')).trace = (stQ G pl).trace := by
    rw [hC, hC', hQ]
    calc (stP W L q₂.2 * (a * a₂) * (stP W L p₂.2 * (b₁ * b₂))).trace
        = (stP W L q₂.2 * (a * a₂ * (b₁ * b₂))).trace := by
          congr 1
          calc stP W L q₂.2 * (a * a₂) * (stP W L p₂.2 * (b₁ * b₂))
              = stP W L q₂.2 * (a * (a₂ * stP W L p₂.2) * (b₁ * b₂)) := by
                simp only [Matrix.mul_assoc]
            _ = _ := by rw [habs₂]
      _ = ((a * a₂ * (b₁ * b₂)) * stP W L q₂.2).trace := Matrix.trace_mul_comm _ _
      _ = (a * a₂ * b₁ * b₂).trace := by
          congr 1
          calc (a * a₂ * (b₁ * b₂)) * stP W L q₂.2
              = a * a₂ * b₁ * (b₂ * stP W L q₂.2) := by simp only [Matrix.mul_assoc]
            _ = _ := by rw [habs₄]
  have hsA := stHS_bound hW G q₂.2 u₁' p₁ l₁ (by omega) X₁ h₁
  have hsB := stHS_bound hW G p₁.2 u₂' p₂ l₂ (by omega) X₂ h₂
  have hsA' := stHS_bound hW G p₂.2 v₁' q₁ l₁ (by omega) X₁ h₁
  have hsB' := stHS_bound hW G q₁.2 v₂' q₂ l₂ (by omega) X₂ h₂
  have hα₁ : 0 ≤ (W : ℝ) ^ (2 * l₁) * X₁ := (stHsq_nonneg _).trans hsA
  have hα₂ : 0 ≤ (W : ℝ) ^ (2 * l₂) * X₂ := (stHsq_nonneg _).trans hsB
  have hsq : ‖(stQ G pl).trace‖ ^ 2 ≤
      (((W : ℝ) ^ (2 * l₁) * X₁) * ((W : ℝ) ^ (2 * l₂) * X₂)) ^ 2 := by
    rw [← hCC]
    calc ‖((A * B) * (A' * B')).trace‖ ^ 2 ≤ stHsq (A * B) * stHsq (A' * B') :=
          stHsq_trace_le _ _
      _ ≤ (stHsq A * stHsq B) * (stHsq A' * stHsq B') :=
          mul_le_mul (stHsq_mul _ _) (stHsq_mul _ _) (stHsq_nonneg _)
            (mul_nonneg (stHsq_nonneg _) (stHsq_nonneg _))
      _ ≤ (((W : ℝ) ^ (2 * l₁) * X₁) * ((W : ℝ) ^ (2 * l₂) * X₂)) *
          (((W : ℝ) ^ (2 * l₁) * X₁) * ((W : ℝ) ^ (2 * l₂) * X₂)) :=
          mul_le_mul (mul_le_mul hsA hsB (stHsq_nonneg _) hα₁)
            (mul_le_mul hsA' hsB' (stHsq_nonneg _) hα₁)
            (mul_nonneg (stHsq_nonneg _) (stHsq_nonneg _)) (mul_nonneg hα₁ hα₂)
      _ = _ := by ring
  have hle : ‖(stQ G pl).trace‖ ≤ ((W : ℝ) ^ (2 * l₁) * X₁) * ((W : ℝ) ^ (2 * l₂) * X₂) := by
    by_contra hlt
    push Not at hlt
    nlinarith [mul_nonneg hα₁ hα₂, norm_nonneg ((stQ G pl).trace)]
  rw [hloop, stProd_eq_stQ, Matrix.trace_smul, norm_smul, hplen]
  have hN : ((W : ℝ) ^ (2 * l₁) * X₁) * ((W : ℝ) ^ (2 * l₂) * X₂) =
      (W : ℝ) ^ (l₁ + l₂ + (l₁ + l₂)) * (X₁ * X₂) := by
    rw [show l₁ + l₂ + (l₁ + l₂) = 2 * l₁ + 2 * l₂ by ring, pow_add]
    ring
  rw [hN] at hle
  calc ‖((W : ℂ)⁻¹) ^ (l₁ + l₂ + (l₁ + l₂))‖ * ‖(stQ G pl).trace‖
      ≤ ‖((W : ℂ)⁻¹) ^ (l₁ + l₂ + (l₁ + l₂))‖ * ((W : ℝ) ^ (l₁ + l₂ + (l₁ + l₂)) * (X₁ * X₂)) :=
        mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    _ = X₁ * X₂ := by
        rw [norm_pow, norm_inv, Complex.norm_natCast, ← mul_assoc, ← mul_pow,
          inv_mul_cancel₀ hWpos.ne', one_pow, one_mul]

end LSBA
