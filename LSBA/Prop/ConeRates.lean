import LSBA.Loop.ProjField
import LSBA.Loop.WardRow
import LSBA.Kernel.Restore
import LSBA.Loop.SourceTail

/-!
# Deterministic rates of the propagated loop-error fields of Step 3

The deterministic part of Step 3 of Appendix C.3 [sec:gc-one-step] at one Hermitian matrix and one
time `r ≤ v`: the sources of (C.32) [gc:eq:sourcetable] with their tails, the Ward row (C.34)
[gc:eq:row], and the generator of the propagated projected field (C.35)
[fo:eq:projected-error-equation] (cyclically alternating words) and of the propagated field
(other words), bounded by the loop errors, the loops and the primitive loops at time `r` and the
kernel at times `r` and `v`.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Cyclic distances and diameters of words -/

private lemma coneRates_mod {L x y : ℕ} (hx : x < L) (hy : y < L) :
    (x + L - y) % L = if y ≤ x then x - y else x + L - y := by
  split_ifs with h
  · have : x + L - y = (x - y) + L := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

private lemma coneRates_cycDist_comm {L : ℕ} (a b : Fin L) : cycDist a b = cycDist b a := by
  unfold cycDist; exact min_comm _ _

private lemma coneRates_cycDist_tri {L : ℕ} (a b c : Fin L) :
    cycDist a c ≤ cycDist a b + cycDist b c := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  simp only [cycDist, coneRates_mod ha hb, coneRates_mod hb ha, coneRates_mod ha hc,
    coneRates_mod hc ha, coneRates_mod hb hc, coneRates_mod hc hb]
  split_ifs <;> omega

private lemma coneRates_cycDist_self {L : ℕ} (a : Fin L) : cycDist a a = 0 := by
  have ha := a.isLt
  simp only [cycDist, coneRates_mod ha ha]
  simp

private lemma coneRates_le_wordDiam {L k : ℕ} (y : Fin k → Fin L) (i j : Fin k) :
    cycDist (y i) (y j) ≤ wordDiam y :=
  Finset.le_sup (f := fun p : Fin k × Fin k => cycDist (y p.1) (y p.2)) (Finset.mem_univ (i, j))

/-- The diameter of a word is attained by a pair of its labels. -/
private lemma coneRates_wordDiam_eq {L k : ℕ} (y : Fin k → Fin L) (hk : 0 < k) :
    ∃ i j : Fin k, wordDiam y = cycDist (y i) (y j) := by
  have : (Finset.univ : Finset (Fin k × Fin k)).Nonempty := ⟨(⟨0, hk⟩, ⟨0, hk⟩), by simp⟩
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup Finset.univ this
    (fun p : Fin k × Fin k => cycDist (y p.1) (y p.2))
  exact ⟨p.1, p.2, hp⟩

/-- A word whose labels are among the labels of another word has at most its diameter. -/
private lemma coneRates_wordDiam_comp {L k k' : ℕ} (y : Fin k → Fin L) (f : Fin k' → Fin k) :
    wordDiam (y ∘ f) ≤ wordDiam y :=
  Finset.sup_le fun p _ => coneRates_le_wordDiam y (f p.1) (f p.2)

/-- A word of length one has diameter `0`. -/
private lemma coneRates_wordDiam_one {L : ℕ} (y : Fin 1 → Fin L) : wordDiam y = 0 := by
  refine Nat.eq_zero_of_le_zero (Finset.sup_le fun p _ => ?_)
  rw [Subsingleton.elim p.1 p.2, coneRates_cycDist_self]

/-- If a word has diameter above `R`, some label is farther than `R/2` from its first label. -/
private lemma coneRates_far_first {L n : ℕ} (b : Fin (n + 1) → Fin L) (R : ℝ) (hR : 0 ≤ R)
    (h : R < wordDiam b) : ∃ j : Fin n, R / 2 < cycDist (b 0) (b j.succ) := by
  obtain ⟨p, q, hpq⟩ := coneRates_wordDiam_eq b (Nat.succ_pos n)
  have htri := coneRates_cycDist_tri (b p) (b 0) (b q)
  rw [coneRates_cycDist_comm (b p) (b 0)] at htri
  have h1 : R < (cycDist (b 0) (b p) : ℝ) + cycDist (b 0) (b q) := by
    rw [hpq] at h
    exact lt_of_lt_of_le h (by exact_mod_cast htri)
  have key : ∀ x : Fin (n + 1), R / 2 < cycDist (b 0) (b x) → ∃ j : Fin n,
      R / 2 < cycDist (b 0) (b j.succ) := by
    intro x hx
    refine Fin.cases (fun h0 => ?_) (fun j hj => ⟨j, hj⟩) x hx
    exfalso
    rw [coneRates_cycDist_self] at h0
    simp at h0
    linarith
  by_cases hp : R / 2 < cycDist (b 0) (b p)
  · exact key p hp
  · refine key q ?_
    push Not at hp
    linarith

/-! ### Two cut pieces of a long word -/

/-- The two cut pieces of (5.6) [fo:eq:cuts] share the cut label and together carry every label
of the word; so if the word has diameter above `2d`, one of the pieces has diameter above `d`. -/
private lemma coneRates_cut_far {L k : ℕ} (a : Fin k → Fin L) (i j : Fin k) (hij : i < j)
    (c : Fin L) (d : ℝ) (ha : 2 * d < wordDiam a) :
    d < wordDiam (cutLLab a i j c) ∨ d < wordDiam (cutRLab a i j c) := by
  have hij' : i.val < j.val := hij
  have hjk := j.2
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have hcL : cutLLab a i j c ⟨i.val, by omega⟩ = c := by simp [cutLLab]
  have hcR : cutRLab a i j c ⟨j.val - i.val, by omega⟩ = c := by simp [cutRLab]
  have hc : ∀ p : Fin k, (cycDist (a p) c : ℝ) ≤ d := by
    intro p
    by_cases hp1 : p.val < i.val
    · have e : cutLLab a i j c ⟨p.val, by omega⟩ = a p := by simp [cutLLab, hp1]
      have := coneRates_le_wordDiam (cutLLab a i j c) ⟨p.val, by omega⟩ ⟨i.val, by omega⟩
      rw [e, hcL] at this
      exact le_trans (by exact_mod_cast this) h1
    by_cases hp2 : j.val ≤ p.val
    · have e : cutLLab a i j c ⟨p.val - j.val + i.val + 1, by omega⟩ = a p := by
        have n1 : ¬ (p.val - j.val + i.val + 1 < i.val) := by omega
        have n2 : ¬ (p.val - j.val + i.val + 1 = i.val) := by omega
        simp only [cutLLab, n1, n2, dite_false, ite_false]
        congr 1
        ext
        simp only
        omega
      have := coneRates_le_wordDiam (cutLLab a i j c) ⟨p.val - j.val + i.val + 1, by omega⟩
        ⟨i.val, by omega⟩
      rw [e, hcL] at this
      exact le_trans (by exact_mod_cast this) h1
    · have e : cutRLab a i j c ⟨p.val - i.val, by omega⟩ = a p := by
        have n1 : p.val - i.val < j.val - i.val := by omega
        simp only [cutRLab, n1, dite_true]
        congr 1
        ext
        simp only
        omega
      have := coneRates_le_wordDiam (cutRLab a i j c) ⟨p.val - i.val, by omega⟩
        ⟨j.val - i.val, by omega⟩
      rw [e, hcR] at this
      exact le_trans (by exact_mod_cast this) h2
  obtain ⟨p, q, hpq⟩ := coneRates_wordDiam_eq a (by omega)
  have htri := coneRates_cycDist_tri (a p) c (a q)
  rw [coneRates_cycDist_comm c (a q)] at htri
  have : (wordDiam a : ℝ) ≤ 2 * d := by
    rw [hpq]
    have h3 : (cycDist (a p) (a q) : ℝ) ≤ cycDist (a p) c + cycDist (a q) c := by
      exact_mod_cast htri
    linarith [hc p, hc q]
  linarith

/-- A cut product whose two factor families are at most `S`, and at most `τ` on words of diameter
`> d`, summed over the cut label, on a word of diameter `> 2d`. -/
private lemma coneRates_cut_prod {L k : ℕ} (F G : LoopFam L) (a : Fin k → Fin L)
    (σ : Fin k → Bool) (i j : Fin k) (hij : i < j) (d τ S : ℝ) (hτ0 : 0 ≤ τ) (hS0 : 0 ≤ S)
    (ha : 2 * d < wordDiam a)
    (hF : ∀ (b : Fin (k + i.val - j.val + 1) → Fin L) (s : Fin (k + i.val - j.val + 1) → Bool),
      ‖F (k + i.val - j.val + 1) b s‖ ≤ S)
    (hFτ : ∀ (b : Fin (k + i.val - j.val + 1) → Fin L) (s : Fin (k + i.val - j.val + 1) → Bool),
      d < wordDiam b → ‖F (k + i.val - j.val + 1) b s‖ ≤ τ)
    (hG : ∀ (b : Fin (j.val - i.val + 1) → Fin L) (s : Fin (j.val - i.val + 1) → Bool),
      ‖G (j.val - i.val + 1) b s‖ ≤ S)
    (hGτ : ∀ (b : Fin (j.val - i.val + 1) → Fin L) (s : Fin (j.val - i.val + 1) → Bool),
      d < wordDiam b → ‖G (j.val - i.val + 1) b s‖ ≤ τ) :
    ‖∑ c : Fin L, F _ (cutLLab a i j c) (cutLSgn σ i j) * G _ (cutRLab a i j c) (cutRSgn σ i j)‖ ≤
      L * (τ * S) := by
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ c : Fin L, ‖F _ (cutLLab a i j c) (cutLSgn σ i j) *
      G _ (cutRLab a i j c) (cutRSgn σ i j)‖ ≤ τ * S := by
    intro c
    rw [norm_mul]
    rcases coneRates_cut_far a i j hij c d ha with hL | hR
    · exact mul_le_mul (hFτ _ _ hL) (hG _ _) (norm_nonneg _) hτ0
    · rw [mul_comm τ S]
      exact mul_le_mul (hF _ _) (hGτ _ _ hR) (norm_nonneg _) hS0
  calc ∑ c : Fin L, ‖F _ (cutLLab a i j c) (cutLSgn σ i j) *
        G _ (cutRLab a i j c) (cutRSgn σ i j)‖ ≤ ∑ _c : Fin L, τ * S :=
        Finset.sum_le_sum fun c _ => hterm c
    _ = L * (τ * S) := by simp

private lemma coneRates_pairs (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
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

private lemma coneRates_pairsum {k : ℕ} (T : Fin k → Fin k → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hT : ∀ i j, i < j → ‖T i j‖ ≤ B) :
    ‖∑ i, ∑ j, (if i < j then T i j else 0)‖ ≤ (k : ℝ) ^ 2 / 2 * B := by
  refine le_trans ?_ (coneRates_pairs k B hB)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  by_cases h : i < j
  · simpa [h] using hT i j h
  · simp [h]

/-- The primitive loop of length one is `m^σ`. -/
private lemma coneRates_primLoop_one (g : ℝ) (W L : ℕ) (E : ℝ) (m : ℂ) (u : ℝ) (c : Fin L)
    (s : Bool) : primLoop g W L E m u ![c] ![s] = sgnScalar m s := by
  cases s <;> simp [primLoop, primK, primF, sgnScalar]

/-! ### The kernels at a root -/

private lemma coneRates_gamma_pos (g : ℝ) : 0 < gammaG g := by
  unfold gammaG
  have : (0 : ℝ) < max 1 g := lt_of_lt_of_le one_pos (le_max_left _ _)
  positivity

/-- At a root, `P = γ_g|M_B|²` is nonnegative with rows summing to one. -/
private lemma coneRates_P_facts (g : ℝ) (L : ℕ) (hL : 3 ≤ L) (E : ℝ) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) :
    (∀ a b, 0 ≤ pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) a b) ∧
    (∀ a, ∑ b, pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) a b = 1) := by
  refine ⟨fun a b => ?_, fun a => pairP_row_sum _ _ (coneRates_gamma_pos g) L (by omega) E m hm a⟩
  simp only [pairP, Matrix.of_apply]
  exact mul_nonneg (coneRates_gamma_pos g).le (sq_nonneg _)

/-- Strict diagonal dominance: `1 - tX` is invertible when every absolute row of `X` is at most
`1` and `‖t‖ < 1`. -/
private lemma coneRates_det_ne {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n 𝕜) (hX : ∀ a, ∑ b, ‖X a b‖ ≤ 1) (t : 𝕜) (ht : ‖t‖ < 1) :
    (1 - t • X).det ≠ 0 := by
  apply det_ne_zero_of_sum_row_lt_diag
  intro k
  have hoff : ∀ j ∈ Finset.univ.erase k, ‖(1 - t • X) k j‖ = ‖t‖ * ‖X k j‖ := by
    intro j hj
    rw [Matrix.sub_apply, Matrix.one_apply_ne (Finset.ne_of_mem_erase hj).symm, zero_sub,
      norm_neg, Matrix.smul_apply, smul_eq_mul, norm_mul]
  rw [Finset.sum_congr rfl hoff, ← Finset.mul_sum]
  have hs : ∑ j ∈ Finset.univ.erase k, ‖X k j‖ = ∑ j, ‖X k j‖ - ‖X k k‖ := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]; ring
  have hdiag : 1 - ‖t‖ * ‖X k k‖ ≤ ‖(1 - t • X) k k‖ := by
    rw [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul]
    calc 1 - ‖t‖ * ‖X k k‖ = ‖(1 : 𝕜)‖ - ‖t * X k k‖ := by rw [norm_one, norm_mul]
      _ ≤ ‖1 - t * X k k‖ := norm_sub_norm_le _ _
  have h2 : ‖t‖ * ∑ j, ‖X k j‖ ≤ ‖t‖ * 1 := mul_le_mul_of_nonneg_left (hX k) (norm_nonneg t)
  rw [hs]
  nlinarith [norm_nonneg t, norm_nonneg (X k k)]

/-- The propagators of (5.15) [fo:eq:propagators] from a time to itself are the identity. -/
private lemma coneRates_pairU_self (g : ℝ) (L : ℕ) (hL : 3 ≤ L) (E : ℝ) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1)
    (s s' : Bool) : pairU (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) v v s s' = 1 := by
  obtain ⟨hP, hrow⟩ := coneRates_P_facts g L hL E m hm
  set Mb := dysonMat (hopB g) (gammaG g) L E m
  have hPM : propPM (pairP (gammaG g) Mb) v v = 1 := by
    rw [(propPM_identities _ hP hrow v v v hv0 le_rfl le_rfl hv1).1, sub_self, zero_smul,
      add_zero]
  have hQrow : ∀ a, ∑ b, ‖pairQ (gammaG g) Mb a b‖ ≤ 1 := by
    intro a
    rw [← hrow a]
    refine le_of_eq (Finset.sum_congr rfl fun b _ => ?_)
    simp only [pairQ, pairP, Matrix.of_apply, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (coneRates_gamma_pos g)]
  have hPP : propPP (pairQ (gammaG g) Mb) v v = 1 := by
    unfold propPP
    refine Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr
      (coneRates_det_ne _ hQrow (v : ℂ) ?_))
    rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  unfold pairU
  split_ifs
  · exact hPP
  · rw [hPP]; exact Matrix.map_one _ (star_zero _) (star_one _)
  · rw [hPM]; exact Matrix.map_one _ (by simp) (by simp)

/-- A product of entries of the identity matrix along two words is the indicator of their
equality. -/
private lemma coneRates_prod_one {R : Type*} [CommRing R] {L k : ℕ} (a b : Fin k → Fin L) :
    ∏ j, (1 : Matrix (Fin L) (Fin L) R) (a j) (b j) = if a = b then 1 else 0 := by
  by_cases h : a = b
  · subst h; simp
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    simp only [h, ↓reduceIte]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

/-- `Σ_b coef_{v,r}(a, b) G(b) = Σ_{b'} Π_j U_{a_j b'_j} (𝒬_r G)(b')` with `U = I + (v - r)K_v`,
for the coefficients before (C.35) [fo:eq:projected-error-equation]. -/
private lemma coneRates_coef_sum {L n : ℕ} (P : Matrix (Fin L) (Fin L) ℝ) (v r : ℝ)
    (a : Fin (n + 1) → Fin L) (G : (Fin (n + 1) → Fin L) → ℂ) :
    ∑ b, projCoef P v r a b * G b =
      ∑ b', (∏ j, (((1 + (v - r) • mixedKer P v) (a j) (b' j) : ℝ) : ℂ)) *
        projQ (wardProfile P r) G b' := by
  unfold projCoef
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  simp_rw [mul_assoc, ← Finset.mul_sum]
  congr 1
  unfold projQ rowSum
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  congr 1
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : b' 0 = b 0
  · simp [h, mul_comm]
  · simp [h, Ne.symm h]

/-! ### Words with a fixed first label -/

private lemma coneRates_sum_cons {L k : ℕ} {M : Type*} [AddCommMonoid M]
    (f : (Fin (k + 1) → Fin L) → M) :
    ∑ b, f b = ∑ x : Fin L, ∑ c : Fin k → Fin L, f (Fin.cons x c) := by
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin L)).sum_comp, Fintype.sum_prod_type]
  rfl

/-- A signed row is a sum over the remaining labels. -/
private lemma coneRates_row_cons {L k : ℕ} {M : Type*} [AddCommMonoid M]
    (f : (Fin (k + 1) → Fin L) → M) (x : Fin L) :
    ∑ b, (if b 0 = x then f b else 0) = ∑ c : Fin k → Fin L, f (Fin.cons x c) := by
  rw [coneRates_sum_cons, Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [hy]
  · simp

/-- A product of a probability profile over the remaining labels sums to one. -/
private lemma coneRates_prod_sum {L k : ℕ} (θ : Fin L → ℝ) (hθ1 : ∑ x, θ x = 1) (c : Fin L) :
    ∑ as : Fin k → Fin L, ∏ j, θ (c - as j) = 1 := by
  have : NeZero L := ⟨by rintro rfl; exact c.elim0⟩
  have h1 : ∑ x, θ (c - x) = 1 := by
    rw [← hθ1]
    exact Fintype.sum_equiv (Equiv.subLeft c) _ _ (fun x => rfl)
  rw [← Fintype.sum_pow (fun x => θ (c - x)) k, h1, one_pow]

/-- The projection `𝒬` before (C.33) [fo:eq:ward-projection] for a probability profile has zero
signed rows. -/
private lemma coneRates_projQ_row {L n : ℕ} (θ : Fin L → ℝ) (hθ1 : ∑ x, θ x = 1)
    (F : (Fin (n + 1) → Fin L) → ℂ) (x : Fin L) :
    ∑ b : Fin (n + 1) → Fin L, (if b 0 = x then projQ θ F b else 0) = 0 := by
  rw [coneRates_row_cons]
  unfold projQ
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h1 : ∑ c : Fin n → Fin L, ∏ j, ((θ (x - c j) : ℝ) : ℂ) = 1 := by
    have := coneRates_prod_sum (k := n) θ hθ1 x
    exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) this
  have h2 : ∑ c : Fin n → Fin L, F (Fin.cons x c) = rowSum F x := by
    unfold rowSum
    rw [coneRates_row_cons]
  rw [h1, h2, mul_one, sub_self]

/-- A product of `n` factors in `[0, B]`, one of which is at most `t`. -/
private lemma coneRates_prod_le_one {n : ℕ} (f : Fin (n + 1) → ℝ) (B t : ℝ)
    (h0 : ∀ j, 0 ≤ f j) (hB : ∀ j, f j ≤ B) (j₀ : Fin (n + 1)) (ht : f j₀ ≤ t) :
    ∏ j, f j ≤ t * B ^ n := by
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ j₀)]
  have hB0 : 0 ≤ B := (h0 j₀).trans (hB j₀)
  have h1 : ∏ j ∈ Finset.univ.erase j₀, f j ≤ B ^ n := by
    calc ∏ j ∈ Finset.univ.erase j₀, f j ≤ ∏ _j ∈ Finset.univ.erase j₀, B :=
          Finset.prod_le_prod₀ (fun j _ => h0 j) (fun j _ => hB j)
      _ = B ^ n := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _)]
          simp
  exact mul_le_mul ht h1 (Finset.prod_nonneg fun j _ => h0 j) ((h0 j₀).trans ht)

private lemma coneRates_prod_le {n : ℕ} (f : Fin n → ℝ) (B : ℝ) (h0 : ∀ j, 0 ≤ f j)
    (hB : ∀ j, f j ≤ B) : ∏ j, f j ≤ B ^ n := by
  calc ∏ j, f j ≤ ∏ _j : Fin n, B := Finset.prod_le_prod₀ (fun j _ => h0 j) (fun j _ => hB j)
    _ = B ^ n := by simp

/-- The projection `𝒬_θ F` of a tensor with entries at most `S`, and at most `T` above relative
diameter `R`, for a nonnegative profile `θ`. -/
private lemma coneRates_projQ_le {L n : ℕ} (θ : Fin L → ℝ) (F : (Fin (n + 1) → Fin L) → ℂ)
    (R S T : ℝ) (hR : 0 ≤ R) (hT : 0 ≤ T) (hF : ∀ b, ‖F b‖ ≤ S)
    (hFτ : ∀ b : Fin (n + 1) → Fin L, R < wordDiam b → ‖F b‖ ≤ T) (hθ0 : ∀ x, 0 ≤ θ x)
    (b : Fin (n + 1) → Fin L) :
    ‖projQ θ F b‖ ≤ ‖F b‖ + ((2 * R + 1) ^ n * S + (L : ℝ) ^ n * T) *
      ∏ j : Fin n, θ (b 0 - b j.succ) := by
  unfold projQ
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, ← Complex.ofReal_prod, Complex.norm_real,
    Real.norm_of_nonneg (Finset.prod_nonneg fun j _ => hθ0 _)]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (rowSum_le_of_tail F R S T hR hT hF hFτ (b 0))
    (Finset.prod_nonneg fun j _ => hθ0 _))

/-- The row of a product of matrices. -/
private lemma coneRates_row_mul {L : ℕ} (A B : Matrix (Fin L) (Fin L) ℂ) (α β : ℝ)
    (hβ : 0 ≤ β) (hB : ∀ c, ∑ b, ‖B c b‖ ≤ β) (a : Fin L) (hA : ∑ c, ‖A a c‖ ≤ α) :
    ∑ b, ‖(A * B) a b‖ ≤ α * β := by
  calc ∑ b, ‖(A * B) a b‖ ≤ ∑ b, ∑ c, ‖A a c‖ * ‖B c b‖ := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [Matrix.mul_apply]
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp
    _ = ∑ c, ‖A a c‖ * ∑ b, ‖B c b‖ := by
        rw [Finset.sum_comm]
        simp [Finset.mul_sum]
    _ ≤ ∑ c, ‖A a c‖ * β := Finset.sum_le_sum fun c _ =>
        mul_le_mul_of_nonneg_left (hB c) (norm_nonneg _)
    _ = (∑ c, ‖A a c‖) * β := by rw [Finset.sum_mul]
    _ ≤ α * β := mul_le_mul_of_nonneg_right hA hβ

/-! ### Restoration of the propagated fields -/

/-- (A.74) [fo:eq:projected-propagation], zero-row case, for the propagator
`I + (v - r)P(I - vP)⁻¹` of the kernel `P` at a root, from the kernel bounds at `v`. -/
private lemma coneRates_restoreProj (n : ℕ) (hn : 2 ≤ n) (C₁ : ℝ) (hC₁ : 0 < C₁) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (g E : ℝ) (m : ℂ) (L : ℕ), 3 ≤ L →
      IsDysonRootV (hopB g) (gammaG g) L E m →
      ∀ (r v ρ ℓu ℓv H S τA : ℝ) (A : (Fin n → Fin L) → ℂ) (a : Fin n → Fin L),
      0 ≤ r → r ≤ v → v < 1 → (1 - r) / (1 - v) ≤ ρ →
      1 ≤ ℓu → ℓu ≤ ℓv → ℓu ≤ L → 1 ≤ H → 1 ≤ ρ * ℓu / ℓv → 0 ≤ τA →
      (∀ x y, (v - r) * mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v x y ≤
        C₁ * ρ / ℓv) →
      (∀ x y y', |(v - r) * mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v x y -
          (v - r) * mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v x y'| ≤
        C₁ * ρ / ℓv * (((cycDist y y' : ℝ) + ℓu) / ℓv)) →
      (∀ b, ‖A b‖ ≤ S) → (∀ b, H * ℓu < wordDiam b → ‖A b‖ ≤ τA) →
      (∀ b₁ : Fin L, ∑ b : Fin n → Fin L, (if b ⟨0, by omega⟩ = b₁ then A b else 0) = 0) →
      ‖∑ b : Fin n → Fin L, (∏ j, (((1 + (v - r) •
          mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v) (a j) (b j) : ℝ) :
            ℂ)) * A b‖ ≤
        Cn * H ^ n * (ρ * ℓu / ℓv) ^ n * S + Cn * (H * (1 + ρ) * (L / ℓu)) ^ (2 * n) * τA := by
  obtain ⟨Cn, hCn, hres⟩ := restore_zeroRow n hn C₁ hC₁
  refine ⟨Cn, hCn, ?_⟩
  intro g E m L hL hm r v ρ ℓu ℓv H S τA A a hr0 hrv hv1 hρ h1u huv huL hH hX hτA hΞ hinc hA
    hAτ hzero
  obtain ⟨hP, hrow⟩ := coneRates_P_facts g L hL E m hm
  set P := pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) with hPdef
  obtain ⟨hK0, hKrow⟩ := mixedKer_nonneg_row P hP hrow v (hr0.trans hrv) hv1
  have hv1' : 0 < 1 - v := by linarith
  have hΞrow : ∀ x, ∑ y, ((v - r) • mixedKer P v) x y ≤ ρ := by
    intro x
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, hKrow x]
    have e : (v - r) * (1 - v)⁻¹ = (1 - r) / (1 - v) - 1 := by field_simp; ring
    rw [e]
    linarith
  have hb := hres L ((v - r) • mixedKer P v) A ρ ℓu ℓv H τA
    (fun x y => by
      simp only [Matrix.smul_apply, smul_eq_mul]
      exact mul_nonneg (by linarith) (hK0 x y))
    hΞrow (fun x y => by simpa only [Matrix.smul_apply, smul_eq_mul] using hΞ x y)
    (fun x y y' => by simpa only [Matrix.smul_apply, smul_eq_mul] using hinc x y y')
    h1u huv huL hH hX hτA hAτ hzero a
  have : Nonempty (Fin n → Fin L) := ⟨a⟩
  have hsup : (⨆ b, ‖A b‖) ≤ S := ciSup_le hA
  have hρ0 : 0 ≤ ρ * ℓu / ℓv := by linarith
  refine hb.trans ?_
  gcongr

/-- (A.74) [fo:eq:projected-propagation], case of a stable leg, for the propagators (5.15)
[fo:eq:propagators] at a root, from the kernel bound at `v` and the Dyson bounds. -/
private lemma coneRates_restoreStable (k : ℕ) (hk : 2 ≤ k) (C₁ : ℝ) (hC₁ : 0 < C₁) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (g E : ℝ) (m : ℂ) (L : ℕ), 3 ≤ L →
      IsDysonRootV (hopB g) (gammaG g) L E m →
      ∀ (r v ρ ℓu ℓv H S τA : ℝ) (σ : Fin k → Bool) (A : (Fin k → Fin L) → ℂ)
        (a : Fin k → Fin L),
      (∃ j, σ (finRotate k j) = σ j) →
      0 ≤ r → r ≤ v → v < 1 →
      1 ≤ ℓu → ℓu ≤ ℓv → ℓu ≤ L → 1 ≤ H → 1 ≤ ρ * ℓu / ℓv → 0 ≤ τA →
      (∀ x y, (v - r) * mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v x y ≤
        C₁ * ρ / ℓv) →
      (∀ x, gammaG g * ∑ y, ‖dysonMat (hopB g) (gammaG g) L E m x y‖ ^ 2 ≤ C₁) →
      (∀ x, ∑ y, ‖(1 - (v : ℂ) • pairQ (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))⁻¹ x y‖ ≤
        C₁) →
      (∀ b, ‖A b‖ ≤ S) → (∀ b, H * ℓu < wordDiam b → ‖A b‖ ≤ τA) →
      ‖∑ b : Fin k → Fin L, (∏ j, pairU (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) r v (σ j)
          (σ (finRotate k j)) (a j) (b j)) * A b‖ ≤
        Cn * H ^ (k - 1) * (ρ * ℓu / ℓv) ^ (k - 1) * S + Cn * ((1 + ρ) * (L / ℓu)) ^ k * τA := by
  obtain ⟨Cn, hCn, hres⟩ := restore_stableLeg k hk ((1 + C₁) * C₁) (by positivity)
  refine ⟨Cn, hCn, ?_⟩
  intro g E m L hL hm r v ρ ℓu ℓv H S τA σ A a hst hr0 hrv hv1 h1u huv huL hH hX hτA hΞ hM hR
    hA hAτ
  obtain ⟨hP, hrow⟩ := coneRates_P_facts g L hL E m hm
  set Mb := dysonMat (hopB g) (gammaG g) L E m with hMb
  set P := pairP (gammaG g) Mb with hPdef
  set Q := pairQ (gammaG g) Mb with hQdef
  have hℓv : 0 < ℓv := by linarith
  have hρ : 0 ≤ ρ := by
    by_contra hρ
    push Not at hρ
    have : ρ * ℓu / ℓv < 0 := div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hρ (by linarith)) hℓv
    linarith
  have hC1' : C₁ ≤ (1 + C₁) * C₁ := by nlinarith
  -- the same-sign rows
  have hQrow : ∀ x, ∑ y, ‖(1 - (r : ℂ) • Q) x y‖ ≤ 1 + C₁ := by
    intro x
    calc ∑ y, ‖(1 - (r : ℂ) • Q) x y‖ ≤ ∑ y, (‖(1 : Matrix (Fin L) (Fin L) ℂ) x y‖ +
          r * (gammaG g * ‖Mb x y‖ ^ 2)) := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [Matrix.sub_apply]
          refine (norm_sub_le _ _).trans (le_of_eq ?_)
          simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg hr0, hQdef, pairQ, Matrix.of_apply, norm_pow,
            Real.norm_of_nonneg (coneRates_gamma_pos g).le]
      _ = 1 + r * (gammaG g * ∑ y, ‖Mb x y‖ ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          congr 1
          simp only [Matrix.one_apply]
          rw [Finset.sum_eq_single x (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
          simp
      _ ≤ 1 + C₁ := by
          have := hM x
          have h0 : 0 ≤ gammaG g * ∑ y, ‖Mb x y‖ ^ 2 :=
            mul_nonneg (coneRates_gamma_pos g).le (Finset.sum_nonneg fun y _ => by positivity)
          nlinarith
  have hPProw : ∀ x, ∑ y, ‖propPP Q r v x y‖ ≤ (1 + C₁) * C₁ := fun x =>
    coneRates_row_mul _ _ _ _ hC₁.le hR x (hQrow x)
  have hleg : ∀ i : Fin k, σ i = σ (finRotate k i) →
      ∀ x, ∑ y, ‖pairU (gammaG g) Mb r v (σ i) (σ (finRotate k i)) x y‖ ≤ (1 + C₁) * C₁ := by
    intro i hi x
    unfold pairU
    split_ifs
    · exact hPProw x
    · simpa [Matrix.map_apply, norm_star] using hPProw x
  have hPM : propPM P r v = 1 + (v - r) • mixedKer P v :=
    (propPM_identities P hP hrow r r v hr0 le_rfl hrv hv1).1
  obtain ⟨hK0, -⟩ := mixedKer_nonneg_row P hP hrow v (hr0.trans hrv) hv1
  have hmix : ∀ i : Fin k, σ i ≠ σ (finRotate k i) → ∀ x y,
      ‖pairU (gammaG g) Mb r v (σ i) (σ (finRotate k i)) x y -
        (1 : Matrix (Fin L) (Fin L) ℂ) x y‖ ≤ (1 + C₁) * C₁ * ρ / ℓv := by
    intro i hi x y
    have e : pairU (gammaG g) Mb r v (σ i) (σ (finRotate k i)) x y -
        (1 : Matrix (Fin L) (Fin L) ℂ) x y = (((v - r) * mixedKer P v x y : ℝ) : ℂ) := by
      unfold pairU
      split_ifs with h1
      · exact absurd h1 hi
      · exact absurd h1 hi
      rw [show propPM (pairP (gammaG g) Mb) r v = _ from hPM]
      by_cases hxy : x = y
      · subst hxy; simp
      · simp [hxy]
    rw [e, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (by linarith) (hK0 x y))]
    refine (hΞ x y).trans ?_
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hC1' (div_nonneg hρ hℓv.le)
  obtain ⟨i₀, hi₀⟩ := hst
  have hb := hres L (fun i => pairU (gammaG g) Mb r v (σ i) (σ (finRotate k i))) A ρ ℓu ℓv H τA i₀
    (fun i => by
      by_cases hi : σ i = σ (finRotate k i)
      · exact Or.inl (hleg i hi)
      · exact Or.inr (hmix i hi))
    (hleg i₀ hi₀.symm) h1u huv huL hH hX hτA hAτ a
  have : Nonempty (Fin k → Fin L) := ⟨a⟩
  have hsup : (⨆ b, ‖A b‖) ≤ S := ciSup_le hA
  have hρ0 : 0 ≤ ρ * ℓu / ℓv := by linarith
  refine hb.trans ?_
  gcongr

/-- The primitive loops satisfy (5.10) [fo:eq:primitive] at every `u ∈ (-1, 1)`, all lengths. -/
private theorem coneRates_primDeriv (g : ℝ) (W L : ℕ) (hW : 1 ≤ W) (hL : 3 ≤ L) (E : ℝ) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (u : ℝ) (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    IsPrimDeriv (gammaG g) W L (fun r n b τ => primLoop g W L E m r (k := n) b τ) u := by
  intro n a σ
  rcases n with _ | _ | n
  · have h0 : cutSumFam (fun n b τ => primLoop g W L E m u (k := n) b τ) a σ = 0 := by
      simp [cutSumFam]
    rw [h0, mul_zero]
    exact hasDerivAt_const u (primLoop g W L E m 0 a σ)
  · have h1 : cutSumFam (fun n b τ => primLoop g W L E m u (k := n) b τ) a σ = 0 := by
      simp [cutSumFam]
    rw [h1, mul_zero]
    exact hasDerivAt_const u (primLoop g W L E m 0 a σ)
  · exact primLoop_hasDerivAt g W L hW hL E m hm u hu (by omega) a σ

/-- The source sizes of `coneRates_src` are nonnegative. -/
private lemma coneRates_sizes_nonneg {L k : ℕ} (hk : 2 ≤ k) (X κ : ℕ → ℝ) (Y : ℝ)
    (hX0 : ∀ j, 1 ≤ j → j ≤ k → 0 ≤ X j) (hκ0 : ∀ j, 3 ≤ j → j ≤ k → 0 ≤ κ j) (hY0 : 0 ≤ Y) :
    0 ≤ X 1 * Y + ∑ p ∈ Finset.Icc 3 k, κ p * X (k + 2 - p) +
        ∑ p ∈ Finset.Icc 2 k, X p * X (k + 2 - p) ∧
      0 ≤ ∑ j ∈ Finset.Icc 1 k, X j + ∑ j ∈ Finset.Icc 3 k, κ j := by
  have _ : L = L := rfl
  refine ⟨add_nonneg (add_nonneg (mul_nonneg (hX0 1 le_rfl (by omega)) hY0)
    (Finset.sum_nonneg fun p hp => ?_)) (Finset.sum_nonneg fun p hp => ?_),
    add_nonneg (Finset.sum_nonneg fun p hp => ?_) (Finset.sum_nonneg fun p hp => ?_)⟩ <;>
    rw [Finset.mem_Icc] at hp
  · exact mul_nonneg (hκ0 p hp.1 hp.2) (hX0 _ (by omega) (by omega))
  · exact mul_nonneg (hX0 p (by omega) hp.2) (hX0 _ (by omega) (by omega))
  · exact hX0 p hp.1 hp.2
  · exact hκ0 p hp.1 hp.2

/-- Two numbers in `[0, M]` differ by at most `M`. -/
private lemma coneRates_abs_sub_le {x y M : ℝ} (hx0 : 0 ≤ x) (hxM : x ≤ M) (hy0 : 0 ≤ y)
    (hyM : y ≤ M) : |x - y| ≤ M := by
  rw [abs_le]; constructor <;> linarith

/-- The commutator (6.4) [gc:eq:commutator] on a word of diameter above `Hℓ`: every summand has
either the kernel `K(b₀, c)` beyond `Hℓ/4` or both profile products with a factor beyond `Hℓ/4`. -/
private lemma coneRates_comm_tail {L n : ℕ} (K : Matrix (Fin L) (Fin L) ℝ) (θ : Fin L → ℝ)
    (h : Fin L → ℂ) (r Cθ ℓu H τθ Hh : ℝ) (hK : ∀ a b, 0 ≤ K a b)
    (hrow : ∀ a, ∑ b, K a b = (1 - r)⁻¹) (hr : r < 1) (hℓu : 0 < ℓu) (hH : 0 ≤ H)
    (hτθ0 : 0 ≤ τθ) (hθ0 : ∀ x, 0 ≤ θ x) (hθC : ∀ x, θ x ≤ Cθ / ℓu)
    (hθτ : ∀ x y, H * ℓu / 4 < cycDist y x → θ (x - y) ≤ τθ / ℓu)
    (hKτ : ∀ x y, H * ℓu / 4 < cycDist x y → K x y ≤ τθ / ((1 - r) * ℓu))
    (hh : ∀ c, ‖h c‖ ≤ Hh) (b : Fin (n + 1 + 1) → Fin L) (hb : H * ℓu < wordDiam b) :
    ‖∑ c, ((K (b 0) c : ℝ) : ℂ) * h c *
        (∏ j : Fin (n + 1), ((θ (c - b j.succ) : ℝ) : ℂ) -
          ∏ j : Fin (n + 1), ((θ (b 0 - b j.succ) : ℝ) : ℂ))‖ ≤
      Hh * ((1 - r)⁻¹ * (τθ / ℓu * (Cθ / ℓu) ^ n) +
        L * (τθ / ((1 - r) * ℓu) * (Cθ / ℓu) ^ (n + 1))) := by
  have hHh : 0 ≤ Hh := (norm_nonneg _).trans (hh (b 0))
  have hr1 : 0 < 1 - r := by linarith
  have hHl : 0 ≤ H * ℓu := by positivity
  obtain ⟨j₀, hj₀⟩ := coneRates_far_first b (H * ℓu) hHl hb
  have hB : 0 ≤ Cθ / ℓu := (hθ0 (b 0)).trans (hθC _)
  set M1 : ℝ := τθ / ℓu * (Cθ / ℓu) ^ n with hM1
  set M2 : ℝ := τθ / ((1 - r) * ℓu) * (Cθ / ℓu) ^ (n + 1) with hM2
  have hM2nn : 0 ≤ M2 := by positivity
  have hterm : ∀ c, ‖((K (b 0) c : ℝ) : ℂ) * h c *
      (∏ j : Fin (n + 1), ((θ (c - b j.succ) : ℝ) : ℂ) -
        ∏ j : Fin (n + 1), ((θ (b 0 - b j.succ) : ℝ) : ℂ))‖ ≤ (K (b 0) c * M1 + M2) * Hh := by
    intro c
    rw [← Complex.ofReal_prod, ← Complex.ofReal_prod, ← Complex.ofReal_sub, norm_mul, norm_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (hK _ _), Real.norm_eq_abs]
    have hp0 : ∀ x : Fin L, 0 ≤ ∏ j : Fin (n + 1), θ (x - b j.succ) :=
      fun x => Finset.prod_nonneg fun j _ => hθ0 _
    have hpC : ∀ x : Fin L, ∏ j : Fin (n + 1), θ (x - b j.succ) ≤ (Cθ / ℓu) ^ (n + 1) :=
      fun x => coneRates_prod_le _ _ (fun j => hθ0 _) (fun j => hθC _)
    by_cases hc : (cycDist (b 0) c : ℝ) ≤ H * ℓu / 4
    · -- both profile products carry a far factor
      have h0 : θ (b 0 - b j₀.succ) ≤ τθ / ℓu := hθτ _ _ (by
        rw [coneRates_cycDist_comm]
        have : H * ℓu / 4 ≤ H * ℓu / 2 := by linarith
        linarith)
      have h1 : θ (c - b j₀.succ) ≤ τθ / ℓu := by
        refine hθτ _ _ ?_
        have htri := coneRates_cycDist_tri (b 0) c (b j₀.succ)
        have htri' : (cycDist (b 0) (b j₀.succ) : ℝ) ≤ cycDist (b 0) c + cycDist c (b j₀.succ) := by
          exact_mod_cast htri
        rw [coneRates_cycDist_comm]
        linarith
      have q0 := coneRates_prod_le_one (fun j : Fin (n + 1) => θ (b 0 - b j.succ)) (Cθ / ℓu)
        (τθ / ℓu) (fun j => hθ0 _) (fun j => hθC _) j₀ h0
      have q1 := coneRates_prod_le_one (fun j : Fin (n + 1) => θ (c - b j.succ)) (Cθ / ℓu)
        (τθ / ℓu) (fun j => hθ0 _) (fun j => hθC _) j₀ h1
      have hd := coneRates_abs_sub_le (hp0 c) q1 (hp0 (b 0)) q0
      calc K (b 0) c * ‖h c‖ * |∏ j : Fin (n + 1), θ (c - b j.succ) -
            ∏ j : Fin (n + 1), θ (b 0 - b j.succ)|
          ≤ K (b 0) c * Hh * M1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hh c) (hK _ _)) hd (abs_nonneg _)
              (mul_nonneg (hK _ _) hHh)
        _ ≤ (K (b 0) c * M1 + M2) * Hh := by nlinarith [hK (b 0) c]
    · -- the kernel is far
      push Not at hc
      have hKc := hKτ _ _ hc
      have hd := coneRates_abs_sub_le (hp0 c) (hpC c) (hp0 (b 0)) (hpC (b 0))
      calc K (b 0) c * ‖h c‖ * |∏ j : Fin (n + 1), θ (c - b j.succ) -
            ∏ j : Fin (n + 1), θ (b 0 - b j.succ)|
          ≤ τθ / ((1 - r) * ℓu) * Hh * (Cθ / ℓu) ^ (n + 1) :=
            mul_le_mul (mul_le_mul hKc (hh c) (norm_nonneg _) (by positivity)) hd (abs_nonneg _)
              (by positivity)
        _ = M2 * Hh := by rw [hM2]; ring
        _ ≤ (K (b 0) c * M1 + M2) * Hh := by
            have : 0 ≤ K (b 0) c * M1 := mul_nonneg (hK _ _) (by positivity)
            nlinarith
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun c _ => hterm c).trans (le_of_eq ?_))
  rw [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.sum_mul, hrow]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The exponent bookkeeping of the generator of the propagated projected field: the restored
sources and commutator, with `𝔓 = H(1 + ρ)L/ℓ_u` written `Pp`, against the rates of
`coneRates_genProj`. -/
private lemma coneRates_genProj_arith (n : ℕ) (Cn₀ Cθ H Xs Pp Q α β τθ S1 Sc T1 Tc Ssrc Tsrc
    Nsq : ℝ) (hCn₀ : 0 ≤ Cn₀) (hCθ : 1 ≤ Cθ) (hH : 1 ≤ H) (hXs0 : 0 ≤ Xs) (hHP : H ≤ Pp)
    (hXP : Xs ≤ Pp) (hQP : Q ≤ Pp) (hQ1 : 1 ≤ Q) (hα0 : 0 ≤ α) (hαH : α ≤ H) (hβ0 : 0 ≤ β)
    (hβH : β ≤ H) (hτθ0 : 0 ≤ τθ) (hτθ1 : τθ ≤ 1) (hS1 : 0 ≤ S1) (hSc : 0 ≤ Sc) (hT1 : 0 ≤ T1)
    (hTc : 0 ≤ Tc) (hNsq : 1 ≤ Nsq) (hSsrc : Ssrc ≤ Nsq * (H * S1 + T1))
    (hTsrc : Tsrc = 3 * Nsq * T1) :
    Cn₀ * H ^ (n + 1 + 1) * Xs ^ (n + 1 + 1) * (Ssrc + Cθ ^ (n + 1) *
        (α ^ (n + 1) * Ssrc + Q ^ (n + 1) * Tsrc) + 2 * Cθ ^ (n + 1) * (β ^ n * Sc + Q ^ n * Tc)) +
      Cn₀ * Pp ^ (2 * (n + 1 + 1)) * (Tsrc + τθ * Cθ ^ n *
        (α ^ (n + 1) * Ssrc + Q ^ (n + 1) * Tsrc) +
        τθ * Cθ ^ n * (1 + Cθ * Q) * (β ^ n * Sc + Q ^ n * Tc)) ≤
    12 * (Cn₀ * Nsq * Cθ ^ (n + 1 + 1)) *
        (H ^ (2 * (n + 1 + 1)) * Xs ^ (n + 1 + 1) + Pp ^ (4 * (n + 1 + 1)) * τθ) * (S1 + Sc) +
      12 * (Cn₀ * Nsq * Cθ ^ (n + 1 + 1)) * Pp ^ (4 * (n + 1 + 1)) * (T1 + Tc) := by
  set N := n + 1 + 1 with hN
  have hP1 : 1 ≤ Pp := hH.trans hHP
  have hP0 : 0 ≤ Pp := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have pw : ∀ a b : ℕ, a ≤ b → Pp ^ a ≤ Pp ^ b := fun a b h => pow_le_pow_right₀ hP1 h
  have hw : ∀ a b : ℕ, a ≤ b → H ^ a ≤ H ^ b := fun a b h => pow_le_pow_right₀ hH h
  set c := Cθ ^ (n + 1) with hc
  set c' := Cθ ^ n with hc'
  set D := Cθ ^ (n + 1 + 1) with hD
  have hc'1 : 1 ≤ c' := one_le_pow₀ hCθ
  have hc'c : c' ≤ c := pow_le_pow_right₀ hCθ (by omega)
  have hcD : c ≤ D := pow_le_pow_right₀ hCθ (by omega)
  have hCc : Cθ * c' = c := by rw [hc, hc', pow_succ]; ring
  have hc0 : 0 ≤ c := by linarith
  have hD0 : 0 ≤ D := by linarith
  set BH := H ^ (2 * N) * Xs ^ N with hBH
  set PP := Pp ^ (2 * N) with hPP
  set B4 := Pp ^ (4 * N) with hB4
  have hG0 : 0 ≤ H ^ N * Xs ^ N := by positivity
  have hBH0 : 0 ≤ BH := by positivity
  have hPP0 : 0 ≤ PP := by positivity
  have hB40 : 0 ≤ B4 := by positivity
  have hGP : H ^ N * Xs ^ N ≤ PP := by
    calc H ^ N * Xs ^ N ≤ Pp ^ N * Pp ^ N := by gcongr
      _ = PP := by rw [hPP, ← pow_add]; ring_nf
  -- monomials
  have m1 : H ^ N * Xs ^ N * H ≤ BH := by
    calc H ^ N * Xs ^ N * H = H ^ (N + 1) * Xs ^ N := by rw [pow_succ]; ring
      _ ≤ BH := mul_le_mul_of_nonneg_right (hw _ _ (by omega)) (by positivity)
  have m2 : H ^ N * Xs ^ N * α ^ (n + 1) * H ≤ BH := by
    calc H ^ N * Xs ^ N * α ^ (n + 1) * H ≤ H ^ N * Xs ^ N * H ^ (n + 1) * H := by gcongr
      _ = H ^ (2 * N) * Xs ^ N := by
          have : 2 * N = N + (n + 1) + 1 := by omega
          rw [this, pow_succ, pow_add]
          ring
  have m3 : H ^ N * Xs ^ N * β ^ n ≤ BH := by
    calc H ^ N * Xs ^ N * β ^ n ≤ H ^ N * Xs ^ N * H ^ n := by gcongr
      _ = H ^ (N + n) * Xs ^ N := by rw [pow_add]; ring
      _ ≤ BH := mul_le_mul_of_nonneg_right (hw _ _ (by omega)) (by positivity)
  have m4 : H ^ N * Xs ^ N ≤ B4 := hGP.trans (pw _ _ (by omega))
  have m5 : H ^ N * Xs ^ N * α ^ (n + 1) ≤ B4 := by
    calc H ^ N * Xs ^ N * α ^ (n + 1) ≤ PP * Pp ^ (n + 1) := by
          gcongr
          exact hαH.trans hHP
      _ = Pp ^ (2 * N + (n + 1)) := by rw [hPP, ← pow_add]
      _ ≤ B4 := pw _ _ (by omega)
  have m6 : H ^ N * Xs ^ N * Q ^ (n + 1) ≤ B4 := by
    calc H ^ N * Xs ^ N * Q ^ (n + 1) ≤ PP * Pp ^ (n + 1) := by gcongr
      _ = Pp ^ (2 * N + (n + 1)) := by rw [hPP, ← pow_add]
      _ ≤ B4 := pw _ _ (by omega)
  have m7 : H ^ N * Xs ^ N * Q ^ n ≤ B4 := by
    calc H ^ N * Xs ^ N * Q ^ n ≤ PP * Pp ^ n := by gcongr
      _ = Pp ^ (2 * N + n) := by rw [hPP, ← pow_add]
      _ ≤ B4 := pw _ _ (by omega)
  have m8 : PP ≤ B4 := pw _ _ (by omega)
  have m9 : PP * α ^ (n + 1) * H ≤ B4 := by
    calc PP * α ^ (n + 1) * H ≤ PP * Pp ^ (n + 1) * Pp := by
          gcongr
          exact hαH.trans hHP
      _ = Pp ^ (2 * N + (n + 1) + 1) := by rw [hPP, ← pow_add, pow_succ]
      _ ≤ B4 := pw _ _ (by omega)
  have m10 : PP * α ^ (n + 1) ≤ B4 := by
    calc PP * α ^ (n + 1) ≤ PP * Pp ^ (n + 1) := by
          gcongr
          exact hαH.trans hHP
      _ = Pp ^ (2 * N + (n + 1)) := by rw [hPP, ← pow_add]
      _ ≤ B4 := pw _ _ (by omega)
  have m11 : PP * Q ^ (n + 1) ≤ B4 := by
    calc PP * Q ^ (n + 1) ≤ PP * Pp ^ (n + 1) := by gcongr
      _ = Pp ^ (2 * N + (n + 1)) := by rw [hPP, ← pow_add]
      _ ≤ B4 := pw _ _ (by omega)
  have hone : c' * (1 + Cθ * Q) ≤ 2 * D * Q := by
    have h1 : c' * (1 + Cθ * Q) = c' + c * Q := by rw [← hCc]; ring
    have h2 : c' ≤ c * Q := hc'c.trans (le_mul_of_one_le_right hc0 hQ1)
    have h3 : c * Q ≤ D * Q := mul_le_mul_of_nonneg_right hcD hQ0
    linarith
  have m12 : c' * (1 + Cθ * Q) * (PP * β ^ n) ≤ 2 * D * B4 := by
    have hq : Q * (PP * β ^ n) ≤ B4 := by
      calc Q * (PP * β ^ n) ≤ Pp * (PP * Pp ^ n) := by
            gcongr
            exact hβH.trans hHP
        _ = Pp ^ (2 * N + n + 1) := by rw [hPP, ← pow_add, pow_succ]; ring
        _ ≤ B4 := pw _ _ (by omega)
    calc c' * (1 + Cθ * Q) * (PP * β ^ n) ≤ 2 * D * Q * (PP * β ^ n) := by gcongr
      _ = 2 * D * (Q * (PP * β ^ n)) := by ring
      _ ≤ 2 * D * B4 := by gcongr
  have m13 : c' * (1 + Cθ * Q) * (PP * Q ^ n) ≤ 2 * D * B4 := by
    have hq : Q * (PP * Q ^ n) ≤ B4 := by
      calc Q * (PP * Q ^ n) ≤ Pp * (PP * Pp ^ n) := by gcongr
        _ = Pp ^ (2 * N + n + 1) := by rw [hPP, ← pow_add, pow_succ]; ring
        _ ≤ B4 := pw _ _ (by omega)
    calc c' * (1 + Cθ * Q) * (PP * Q ^ n) ≤ 2 * D * Q * (PP * Q ^ n) := by gcongr
      _ = 2 * D * (Q * (PP * Q ^ n)) := by ring
      _ ≤ 2 * D * B4 := by gcongr
  -- the coefficients
  set U := Cn₀ * Nsq * D with hU
  have hU0 : 0 ≤ U := by positivity
  have k1 : Cn₀ * Nsq ≤ U := by
    rw [hU]; exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hCθ)
  have k2 : Cn₀ * Nsq * c ≤ U := by rw [hU]; gcongr
  have k3 : Cn₀ * c ≤ U := by
    rw [hU]
    calc Cn₀ * c ≤ Cn₀ * D := by gcongr
      _ ≤ Cn₀ * Nsq * D := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hD0 hNsq) hCn₀
  have k4 : Cn₀ * Nsq * c' ≤ U := by rw [hU]; gcongr; exact hc'c.trans hcD
  have k5 : Cn₀ * D ≤ U := by
    rw [hU, mul_assoc]
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hD0 hNsq) hCn₀
  -- substitute the source sizes
  have hstep : Cn₀ * H ^ N * Xs ^ N * (Ssrc + c * (α ^ (n + 1) * Ssrc + Q ^ (n + 1) * Tsrc) +
        2 * c * (β ^ n * Sc + Q ^ n * Tc)) +
      Cn₀ * PP * (Tsrc + τθ * c' * (α ^ (n + 1) * Ssrc + Q ^ (n + 1) * Tsrc) +
        τθ * c' * (1 + Cθ * Q) * (β ^ n * Sc + Q ^ n * Tc)) ≤
      Cn₀ * H ^ N * Xs ^ N * (Nsq * (H * S1 + T1) + c * (α ^ (n + 1) * (Nsq * (H * S1 + T1)) +
          Q ^ (n + 1) * (3 * Nsq * T1)) + 2 * c * (β ^ n * Sc + Q ^ n * Tc)) +
      Cn₀ * PP * (3 * Nsq * T1 + τθ * c' * (α ^ (n + 1) * (Nsq * (H * S1 + T1)) +
          Q ^ (n + 1) * (3 * Nsq * T1)) +
        τθ * c' * (1 + Cθ * Q) * (β ^ n * Sc + Q ^ n * Tc)) := by
    rw [hTsrc]
    gcongr
  refine hstep.trans ?_
  -- the products
  have p1 := mul_le_mul m1 k1 (by positivity) hBH0
  have p2 := mul_le_mul m4 k1 (by positivity) hB40
  have p3 := mul_le_mul m2 k2 (by positivity) hBH0
  have p4 := mul_le_mul m5 k2 (by positivity) hB40
  have p5 := mul_le_mul m6 k2 (by positivity) hB40
  have p6 := mul_le_mul m3 k3 (by positivity) hBH0
  have p7 := mul_le_mul m7 k3 (by positivity) hB40
  have p8 := mul_le_mul m8 k1 (by positivity) hB40
  have p9 := mul_le_mul m9 k4 (by positivity) hB40
  have p10 := mul_le_mul m10 k4 (by positivity) hB40
  have p11 := mul_le_mul m11 k4 (by positivity) hB40
  have p12 := mul_le_mul m12 (le_refl Cn₀) hCn₀ (by positivity)
  have p13 := mul_le_mul m13 (le_refl Cn₀) hCn₀ (by positivity)
  have q1 := mul_le_mul_of_nonneg_right p1 hS1
  have q2 := mul_le_mul_of_nonneg_right p2 hT1
  have q3 := mul_le_mul_of_nonneg_right p3 hS1
  have q4 := mul_le_mul_of_nonneg_right p4 hT1
  have q5 := mul_le_mul_of_nonneg_right p5 hT1
  have q6 := mul_le_mul_of_nonneg_right p6 hSc
  have q7 := mul_le_mul_of_nonneg_right p7 hTc
  have q8 := mul_le_mul_of_nonneg_right p8 hT1
  have q9 := mul_le_mul_of_nonneg_right p9 (mul_nonneg hτθ0 hS1)
  have q10 := mul_le_mul_of_nonneg_right p10 (mul_nonneg hτθ0 hT1)
  have q11 := mul_le_mul_of_nonneg_right p11 (mul_nonneg hτθ0 hT1)
  have q12 := mul_le_mul_of_nonneg_right p12 (mul_nonneg hτθ0 hSc)
  have q13 := mul_le_mul_of_nonneg_right p13 (mul_nonneg hτθ0 hTc)
  have r10 : U * B4 * (τθ * T1) ≤ U * B4 * T1 := by
    have := mul_le_mul_of_nonneg_left hτθ1 (mul_nonneg (mul_nonneg hU0 hB40) hT1)
    linarith
  have r11 : 2 * D * B4 * Cn₀ * (τθ * Sc) ≤ 2 * U * B4 * (τθ * Sc) := by
    have := mul_le_mul_of_nonneg_right k5 (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hB40)
      (mul_nonneg hτθ0 hSc))
    linarith
  have r12 : 2 * D * B4 * Cn₀ * (τθ * Tc) ≤ 2 * U * B4 * Tc := by
    have h1 := mul_le_mul_of_nonneg_right k5 (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hB40)
      (mul_nonneg hτθ0 hTc))
    have h2 := mul_le_mul_of_nonneg_left hτθ1 (mul_nonneg (mul_nonneg hU0 hB40) hTc)
    linarith
  have s1 : 0 ≤ U * BH * S1 := by positivity
  have s2 : 0 ≤ U * BH * Sc := by positivity
  have s3 : 0 ≤ U * B4 * τθ * S1 := by positivity
  have s4 : 0 ≤ U * B4 * τθ * Sc := by positivity
  have s5 : 0 ≤ U * B4 * T1 := by positivity
  have s6 : 0 ≤ U * B4 * Tc := by positivity
  linarith [q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, r10, r11, r12, s1, s2, s3, s4,
    s5, s6]

/-! ### The rates -/

/-- The sources of (C.32) [gc:eq:sourcetable] at one matrix `M`: the light term `𝒲_k` of (5.7)
[fo:eq:light] plus `γ_g W` times the cut terms of (5.17) [fo:eq:error-hierarchy] with `Θ` removed.
If the loop errors `D_j` (`1 ≤ j ≤ k`), the primitive loops `𝒦_j` (`3 ≤ j ≤ k`) and the loops of
length `k + 1` are bounded by `X j`, `κ j` and `Y`, and the loop errors of lengths `2 ≤ j ≤ k`,
these primitive loops and these loops are bounded by `τ` on words of diameter `> d`, then the source
is at most `k²γ_g W((2d + 1)(X₁Y + Σ_p κ_p X_{k+2-p} + Σ_p X_p X_{k+2-p}) + Lτ Σ)`, and at most
`3k²γ_g W Lτ Σ` on words of diameter `> 2d`, with `Σ = Σ_{1 ≤ j ≤ k} X_j + Σ_{3 ≤ j ≤ k} κ_j`. -/
theorem coneRates_src (g E : ℝ) (m : ℂ) {W L k : ℕ} (hk : 2 ≤ k) (u : ℝ)
    (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (X κ : ℕ → ℝ) (Y d τ : ℝ) (hd : 0 ≤ d)
    (hτ : 0 ≤ τ)
    (hX : ∀ j, 1 ≤ j → j ≤ k → ∀ (b : Fin j → Fin L) (s : Fin j → Bool),
      ‖loopTr (resolventMat M (zChar g E m u)) b s - primLoop g W L E m u b s‖ ≤ X j)
    (hXτ : ∀ j, 2 ≤ j → j ≤ k → ∀ (b : Fin j → Fin L) (s : Fin j → Bool), d < wordDiam b →
      ‖loopTr (resolventMat M (zChar g E m u)) b s - primLoop g W L E m u b s‖ ≤ τ)
    (hκ : ∀ j, 3 ≤ j → j ≤ k → ∀ (b : Fin j → Fin L) (s : Fin j → Bool),
      ‖primLoop g W L E m u b s‖ ≤ κ j)
    (hκτ : ∀ j, 3 ≤ j → j ≤ k → ∀ (b : Fin j → Fin L) (s : Fin j → Bool), d < wordDiam b →
      ‖primLoop g W L E m u b s‖ ≤ τ)
    (hY : ∀ (b : Fin (k + 1) → Fin L) (s : Fin (k + 1) → Bool),
      ‖loopTr (resolventMat M (zChar g E m u)) b s‖ ≤ Y)
    (hYτ : ∀ (b : Fin (k + 1) → Fin L) (s : Fin (k + 1) → Bool), d < wordDiam b →
      ‖loopTr (resolventMat M (zChar g E m u)) b s‖ ≤ τ)
    (a : Fin k → Fin L) (σ : Fin k → Bool) :
    ‖lightW g E m a σ u M + ((gammaG g * W : ℝ) : ℂ) *
        (cutSrcLin (fun _ c τ' => primLoop g W L E m u c τ')
            (errFam g E m (fun _ c τ' => primLoop g W L E m u c τ') u M) a σ +
          cutSrcQuad (errFam g E m (fun _ c τ' => primLoop g W L E m u c τ') u M) a σ)‖ ≤
      (k : ℝ) ^ 2 * (gammaG g * W) * ((2 * d + 1) * (X 1 * Y +
          ∑ p ∈ Finset.Icc 3 k, κ p * X (k + 2 - p) + ∑ p ∈ Finset.Icc 2 k, X p * X (k + 2 - p)) +
        L * τ * (∑ j ∈ Finset.Icc 1 k, X j + ∑ j ∈ Finset.Icc 3 k, κ j)) ∧
    (2 * d < wordDiam a →
      ‖lightW g E m a σ u M + ((gammaG g * W : ℝ) : ℂ) *
        (cutSrcLin (fun _ c τ' => primLoop g W L E m u c τ')
            (errFam g E m (fun _ c τ' => primLoop g W L E m u c τ') u M) a σ +
          cutSrcQuad (errFam g E m (fun _ c τ' => primLoop g W L E m u c τ') u M) a σ)‖ ≤
        3 * (k : ℝ) ^ 2 * (gammaG g * W) * L * τ *
          (∑ j ∈ Finset.Icc 1 k, X j + ∑ j ∈ Finset.Icc 3 k, κ j)) := by
  have hk0 : 0 < k := by omega
  set a0 : Fin L := a ⟨0, hk0⟩
  have hX0 : ∀ j, 1 ≤ j → j ≤ k → 0 ≤ X j := fun j h1 h2 =>
    (norm_nonneg _).trans (hX j h1 h2 (fun _ => a0) (fun _ => true))
  have hκ0 : ∀ j, 3 ≤ j → j ≤ k → 0 ≤ κ j := fun j h1 h2 =>
    (norm_nonneg _).trans (hκ j h1 h2 (fun _ => a0) (fun _ => true))
  have hY0 : 0 ≤ Y := (norm_nonneg _).trans (hY (fun _ => a0) (fun _ => true))
  have hγ : 0 ≤ gammaG g := by unfold gammaG; positivity
  have hγW : 0 ≤ gammaG g * W := by positivity
  have hX1 : 0 ≤ X 1 := hX0 1 le_rfl (by omega)
  have h1 : ∀ (c : Fin L) (s : Bool),
      ‖loopTr (resolventMat M (zChar g E m u)) ![c] ![s] - sgnScalar m s‖ ≤ X 1 := by
    intro c s
    have := hX 1 le_rfl (by omega) ![c] ![s]
    rwa [coneRates_primLoop_one] at this
  have hnγ : ‖((gammaG g * W : ℝ) : ℂ)‖ = gammaG g * W := by
    rw [Complex.norm_real, Real.norm_of_nonneg hγW]
  have hSκ0 : 0 ≤ ∑ j ∈ Finset.Icc 3 k, κ j := Finset.sum_nonneg fun j hj => by
    rw [Finset.mem_Icc] at hj; exact hκ0 j hj.1 hj.2
  have hSX0 : 0 ≤ ∑ j ∈ Finset.Icc 2 k, X j := Finset.sum_nonneg fun j hj => by
    rw [Finset.mem_Icc] at hj; exact hX0 j (by omega) hj.2
  have e3 : ∑ j ∈ Finset.Icc 1 k, X j = X 1 + ∑ j ∈ Finset.Icc 2 k, X j := by
    rw [← Finset.add_sum_Ioc_eq_sum_Icc (by omega : 1 ≤ k), ← Finset.Icc_add_one_left_eq_Ioc]
    rfl
  refine ⟨?_, fun ha => ?_⟩
  · have hl := lightW_tail_le g E m u M (X 1) Y d τ hd hX1 hτ h1 hY hYτ a σ
    have hlin := cutSrcLin_tail_le (fun _ c τ' => primLoop g W L E m u c τ')
      (errFam g E m (fun _ c τ' => primLoop g W L E m u c τ') u M) κ X d τ hd hτ
      (fun j h3 h4 b s => hκ j h3 h4 b s)
      (fun j h2 h3 b s => hX j (by omega) h3.le b s)
      (fun j h2 h3 b s hb => hXτ j h2 h3.le b s hb) a σ
    have hquad := cutSrcQuad_tail_le
      (errFam g E m (fun _ c τ' => primLoop g W L E m u c τ') u M) X d τ hd hτ
      (fun j h2 h3 b s => hX j (by omega) h3 b s)
      (fun j h2 h3 b s hb => hXτ j h2 h3 b s hb) a σ
    have e1 : ∑ p ∈ Finset.Icc 3 k, κ p * ((2 * d + 1) * X (k + 2 - p) + L * τ) =
        (2 * d + 1) * ∑ p ∈ Finset.Icc 3 k, κ p * X (k + 2 - p) +
          L * τ * ∑ j ∈ Finset.Icc 3 k, κ j := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by ring
    have e2 : ∑ p ∈ Finset.Icc 2 k, X p * ((2 * d + 1) * X (k + 2 - p) + L * τ) =
        (2 * d + 1) * ∑ p ∈ Finset.Icc 2 k, X p * X (k + 2 - p) +
          L * τ * ∑ j ∈ Finset.Icc 2 k, X j := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by ring
    rw [e1] at hlin
    rw [e2] at hquad
    rw [e3]
    have hk1 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      nlinarith
    have hrest : 0 ≤ (2 * d + 1) * Y + L * τ := by positivity
    have hslack := mul_nonneg (mul_nonneg hγW (sub_nonneg.mpr hk1)) (mul_nonneg hX1 hrest)
    calc _ ≤ ‖lightW g E m a σ u M‖ + gammaG g * W *
          (‖cutSrcLin (fun _ c τ' => primLoop g W L E m u c τ')
              (errFam g E m (fun _ c τ' => primLoop g W L E m u c τ') u M) a σ‖ +
            ‖cutSrcQuad (errFam g E m (fun _ c τ' => primLoop g W L E m u c τ') u M) a σ‖) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, hnγ]
          gcongr
          exact norm_add_le _ _
      _ ≤ gammaG g * W * k * X 1 * ((2 * d + 1) * Y + L * τ) + gammaG g * W *
          ((k : ℝ) ^ 2 * ((2 * d + 1) * ∑ p ∈ Finset.Icc 3 k, κ p * X (k + 2 - p) +
              L * τ * ∑ j ∈ Finset.Icc 3 k, κ j) +
            (k : ℝ) ^ 2 * ((2 * d + 1) * ∑ p ∈ Finset.Icc 2 k, X p * X (k + 2 - p) +
              L * τ * ∑ j ∈ Finset.Icc 2 k, X j)) := by gcongr
      _ ≤ _ := by linarith
  · set St := ∑ j ∈ Finset.Icc 1 k, X j + ∑ j ∈ Finset.Icc 3 k, κ j with hSt
    have hSX : ∀ j, 1 ≤ j → j ≤ k → X j ≤ St := by
      intro j h1 h2
      have : X j ≤ ∑ j ∈ Finset.Icc 1 k, X j := Finset.single_le_sum
        (fun i hi => by rw [Finset.mem_Icc] at hi; exact hX0 i hi.1 hi.2)
        (Finset.mem_Icc.mpr ⟨h1, h2⟩)
      linarith
    have hSK : ∀ j, 3 ≤ j → j ≤ k → κ j ≤ St := by
      intro j h1 h2
      have : κ j ≤ ∑ j ∈ Finset.Icc 3 k, κ j := Finset.single_le_sum
        (fun i hi => by rw [Finset.mem_Icc] at hi; exact hκ0 i hi.1 hi.2)
        (Finset.mem_Icc.mpr ⟨h1, h2⟩)
      have : 0 ≤ ∑ j ∈ Finset.Icc 1 k, X j := by rw [e3]; linarith
      linarith
    have hSt0 : 0 ≤ St := le_trans hX1 (hSX 1 le_rfl (by omega))
    have hda : d < (wordDiam a : ℝ) := by linarith
    -- the light term
    have hlight : ‖lightW g E m a σ u M‖ ≤ gammaG g * W * (k * (L * (τ * St))) := by
      unfold lightW
      rw [norm_mul, hnγ]
      refine mul_le_mul_of_nonneg_left ?_ hγW
      refine (norm_sum_le _ _).trans ?_
      calc ∑ i : Fin k, ‖∑ c : Fin L,
            (loopTr (resolventMat M (zChar g E m u)) ![c] ![σ i] - sgnScalar m (σ i)) *
              loopTr (resolventMat M (zChar g E m u)) (insLab a i c) (insSgn σ i)‖
          ≤ ∑ _i : Fin k, ∑ _c : Fin L, τ * St := by
            refine Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
              (Finset.sum_le_sum fun c _ => ?_)
            rw [norm_mul, mul_comm τ St]
            have hfar : d < (wordDiam (insLab a i c) : ℝ) := by
              have e : insLab a i c ∘ (Fin.succAbove i.castSucc) = a := by
                funext p
                simp [insLab, Fin.insertNth_apply_succAbove]
              have := coneRates_wordDiam_comp (insLab a i c) (Fin.succAbove i.castSucc)
              rw [e] at this
              exact lt_of_lt_of_le hda (by exact_mod_cast this)
            exact mul_le_mul ((h1 c (σ i)).trans (hSX 1 le_rfl (by omega)))
              (hYτ _ _ hfar) (norm_nonneg _) hSt0
        _ = k * (L * (τ * St)) := by simp
    -- the linear cut source
    have hlin : ‖cutSrcLin (fun _ c τ' => primLoop g W L E m u c τ')
        (errFam g E m (fun _ c τ' => primLoop g W L E m u c τ') u M) a σ‖ ≤
        (k : ℝ) ^ 2 / 2 * (2 * (L * (τ * St))) := by
      by_cases hk2 : k ≤ 2
      · simp only [cutSrcLin, hk2, ite_true, norm_zero]
        positivity
      unfold cutSrcLin
      simp only [hk2, ite_false]
      refine coneRates_pairsum _ _ (by positivity) fun i j hij => ?_
      have hij' : i.val < j.val := hij
      have hjk := j.2
      have hKD : 3 ≤ k + i.val - j.val + 1 → k + i.val - j.val + 1 ≤ k →
          2 ≤ j.val - i.val + 1 → j.val - i.val + 1 ≤ k →
          ‖∑ c, primLoop g W L E m u (cutLLab a i j c) (cutLSgn σ i j) *
            errFam g E m (fun _ c τ' => primLoop g W L E m u c τ') u M _ (cutRLab a i j c)
              (cutRSgn σ i j)‖ ≤ L * (τ * St) := fun h3 h4 h5 h6 =>
        coneRates_cut_prod (fun _ c τ' => primLoop g W L E m u c τ')
          (errFam g E m (fun _ c τ' => primLoop g W L E m u c τ') u M) a σ i j hij d τ St hτ hSt0
          ha (fun b s => (hκ _ h3 h4 b s).trans (hSK _ h3 h4)) (fun b s hb => hκτ _ h3 h4 b s hb)
          (fun b s => (hX _ (by omega) h6 b s).trans (hSX _ (by omega) h6))
          (fun b s hb => hXτ _ h5 h6 b s hb)
      have hDK : 2 ≤ k + i.val - j.val + 1 → k + i.val - j.val + 1 ≤ k →
          3 ≤ j.val - i.val + 1 → j.val - i.val + 1 ≤ k →
          ‖∑ c, errFam g E m (fun _ c τ' => primLoop g W L E m u c τ') u M _ (cutLLab a i j c)
              (cutLSgn σ i j) *
            primLoop g W L E m u (cutRLab a i j c) (cutRSgn σ i j)‖ ≤ L * (τ * St) :=
        fun h3 h4 h5 h6 =>
        coneRates_cut_prod (errFam g E m (fun _ c τ' => primLoop g W L E m u c τ') u M)
          (fun _ c τ' => primLoop g W L E m u c τ') a σ i j hij d τ St hτ hSt0 ha
          (fun b s => (hX _ (by omega) h4 b s).trans (hSX _ (by omega) h4))
          (fun b s hb => hXτ _ h3 h4 b s hb)
          (fun b s => (hκ _ h5 h6 b s).trans (hSK _ h5 h6)) (fun b s hb => hκτ _ h5 h6 b s hb)
      have hLτ : 0 ≤ (L : ℝ) * (τ * St) := by positivity
      by_cases c1 : j.val = i.val + 1
      · simp only [c1, ite_true]
        have := hKD (by omega) (by omega) (by omega) (by omega)
        linarith
      · by_cases c2 : i.val = 0 ∧ j.val = k - 1
        · simp only [c1, ite_false]
          simp only [eq_true c2, ite_true]
          have := hDK (by omega) (by omega) (by omega) (by omega)
          linarith
        · simp only [c1, ite_false, eq_false c2]
          rw [Finset.sum_add_distrib]
          refine (norm_add_le _ _).trans ?_
          have e1 := hKD (by omega) (by omega) (by omega) (by omega)
          have e2 := hDK (by omega) (by omega) (by omega) (by omega)
          linarith
    -- the quadratic cut source
    have hquad : ‖cutSrcQuad (errFam g E m (fun _ c τ' => primLoop g W L E m u c τ') u M) a σ‖ ≤
        (k : ℝ) ^ 2 / 2 * (L * (τ * St)) := by
      unfold cutSrcQuad cutSumFam
      refine coneRates_pairsum _ _ (by positivity) fun i j hij => ?_
      have hij' : i.val < j.val := hij
      have hjk := j.2
      exact coneRates_cut_prod (errFam g E m (fun _ c τ' => primLoop g W L E m u c τ') u M)
        (errFam g E m (fun _ c τ' => primLoop g W L E m u c τ') u M) a σ i j hij d τ St hτ hSt0 ha
        (fun b s => (hX _ (by omega) (by omega) b s).trans (hSX _ (by omega) (by omega)))
        (fun b s hb => hXτ _ (by omega) (by omega) b s hb)
        (fun b s => (hX _ (by omega) (by omega) b s).trans (hSX _ (by omega) (by omega)))
        (fun b s hb => hXτ _ (by omega) (by omega) b s hb)
    have hk1 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      nlinarith
    have hLτS : 0 ≤ (L : ℝ) * (τ * St) := by positivity
    have hslack := mul_nonneg hγW (mul_nonneg (sub_nonneg.mpr hk1) hLτS)
    have hk20 : 0 ≤ (k : ℝ) ^ 2 := by positivity
    have hslack2 := mul_nonneg hγW (mul_nonneg hk20 hLτS)
    calc _ ≤ ‖lightW g E m a σ u M‖ + gammaG g * W *
          (‖cutSrcLin (fun _ c τ' => primLoop g W L E m u c τ')
              (errFam g E m (fun _ c τ' => primLoop g W L E m u c τ') u M) a σ‖ +
            ‖cutSrcQuad (errFam g E m (fun _ c τ' => primLoop g W L E m u c τ') u M) a σ‖) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, hnγ]
          gcongr
          exact norm_add_le _ _
      _ ≤ gammaG g * W * (k * (L * (τ * St))) + gammaG g * W *
          ((k : ℝ) ^ 2 / 2 * (2 * (L * (τ * St))) + (k : ℝ) ^ 2 / 2 * (L * (τ * St))) := by
          gcongr
      _ ≤ _ := by linarith

/-- The Ward row (C.34) [gc:eq:row] at one matrix: for a word of length `n + 1` whose last sign is
opposite to its first, `|Σ_{b₀ = c} D_{n+1}(b)| ≤ (Wη_u)⁻¹((2d + 1)^{n-1}X + L^{n-1}τ)` if the
loop errors of length `n` are bounded by `X`, and by `τ` on words of diameter `> d`. -/
theorem coneRates_rowWard (g E : ℝ) (m : ℂ) {W L n : ℕ} (hW : 1 ≤ W) (hL : 3 ≤ L) (hn : 1 ≤ n)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hM : M.IsHermitian) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (X d τ : ℝ) (hd : 0 ≤ d)
    (hτ : 0 ≤ τ)
    (hX : ∀ (b : Fin n → Fin L) (s : Fin n → Bool),
      ‖loopTr (resolventMat M (zChar g E m u)) b s - primLoop g W L E m u b s‖ ≤ X)
    (hXτ : ∀ (b : Fin n → Fin L) (s : Fin n → Bool), d < wordDiam b →
      ‖loopTr (resolventMat M (zChar g E m u)) b s - primLoop g W L E m u b s‖ ≤ τ)
    (σ : Fin (n + 1) → Bool) (hσ : σ (Fin.last n) = !σ 0) (c : Fin L) :
    ‖rowSum (fun b => resLoop g E m b σ u M - primLoop g W L E m u b σ) c‖ ≤
      (W * etaChar g m u)⁻¹ * ((2 * d + 1) ^ (n - 1) * X + (L : ℝ) ^ (n - 1) * τ) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hγ := coneRates_gamma_pos g
  have hη : 0 < etaChar g m u := by
    unfold etaChar
    have := hm.1
    have : 0 < 1 - u := by linarith
    positivity
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  set τ' : Fin (n' + 1) → Bool := Fin.init σ with hτ'
  have hσe : Fin.snoc (Function.update τ' ⟨0, by omega⟩ (σ 0)) (!σ 0) = σ := by
    have hu : Function.update τ' ⟨0, by omega⟩ (σ 0) = τ' := by
      refine Function.update_eq_self_iff.mpr ?_
      simp only [hτ', Fin.init]
      rfl
    rw [hu, ← hσ]
    exact Fin.snoc_init_self σ
  have key := loopErr_rowSum_ward g E m hW hL hm hM hu0 hu1 (n' + 1) (by omega) τ' (σ 0) c
  rw [hσe] at key
  rw [key]
  set Fp : (Fin (n' + 1) → Fin L) → ℂ := fun b =>
    resLoop g E m b (Function.update τ' ⟨0, by omega⟩ true) u M -
      primLoop g W L E m u b (Function.update τ' ⟨0, by omega⟩ true) with hFp
  set Fm : (Fin (n' + 1) → Fin L) → ℂ := fun b =>
    resLoop g E m b (Function.update τ' ⟨0, by omega⟩ false) u M -
      primLoop g W L E m u b (Function.update τ' ⟨0, by omega⟩ false) with hFm
  have hsum : ∑ b : Fin (n' + 1) → Fin L,
      (if b ⟨0, by omega⟩ = c then Fp b - Fm b else 0) = rowSum Fp c - rowSum Fm c := by
    unfold rowSum
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    have : (⟨0, by omega⟩ : Fin (n' + 1)) = 0 := rfl
    rw [this]
    split_ifs <;> simp
  rw [hsum]
  have hp := rowSum_le_of_tail Fp d X τ hd hτ (fun b => hX b _) (fun b hb => hXτ b _ hb) c
  have hm' := rowSum_le_of_tail Fm d X τ hd hτ (fun b => hX b _) (fun b hb => hXτ b _ hb) c
  have hn : ‖(2 * Complex.I * (W : ℂ) * (etaChar g m u : ℂ))‖ = 2 * (W * etaChar g m u) := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_natCast, Complex.norm_real,
      Real.norm_of_nonneg hη.le]
    norm_num
    ring
  rw [norm_mul, norm_inv, hn, Nat.add_sub_cancel]
  have hWη : 0 < W * etaChar g m u := by positivity
  calc (2 * (W * etaChar g m u))⁻¹ * ‖rowSum Fp c - rowSum Fm c‖
      ≤ (2 * (W * etaChar g m u))⁻¹ * (‖rowSum Fp c‖ + ‖rowSum Fm c‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
    _ ≤ (2 * (W * etaChar g m u))⁻¹ *
          (2 * ((2 * d + 1) ^ n' * X + (L : ℝ) ^ n' * τ)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (W * etaChar g m u)⁻¹ * ((2 * d + 1) ^ n' * X + (L : ℝ) ^ n' * τ) := by
        field_simp

/-- At `r = v` both propagators are the identity: `Σ_b coef_{v,v}(a, b)F(b) = 𝒬_v F(a)` for the
coefficients of (C.35) [fo:eq:projected-error-equation], and `Σ_b Π_j U_{v,v}(a_j, b_j)F(b) = F(a)`
for the one-label propagators of (5.15) [fo:eq:propagators]. -/
theorem coneRates_fieldSelf (g E : ℝ) (m : ℂ) {L : ℕ} (hL : 3 ≤ L)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) :
    (∀ (n : ℕ) (F : (Fin (n + 1) → Fin L) → ℂ) (a : Fin (n + 1) → Fin L),
      ∑ b, projCoef (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v v a b * F b =
        projQ (wardProfile (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v) F a) ∧
    ∀ (k : ℕ) (σ : Fin k → Bool) (F : (Fin k → Fin L) → ℂ) (a : Fin k → Fin L),
      ∑ b : Fin k → Fin L, (∏ j, pairU (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) v v (σ j)
          (σ (finRotate k j)) (a j) (b j)) * F b = F a := by
  obtain ⟨hP, hrow⟩ := coneRates_P_facts g L hL E m hm
  refine ⟨fun n F a => ?_, fun k σ F a => ?_⟩
  · rw [coneRates_coef_sum, sub_self, zero_smul, add_zero]
    have e : ∀ b' : Fin (n + 1) → Fin L,
        (∏ j, (((1 : Matrix (Fin L) (Fin L) ℝ) (a j) (b' j) : ℝ) : ℂ)) =
          if a = b' then 1 else 0 := by
      intro b'
      rw [← Complex.ofReal_prod, coneRates_prod_one]
      split_ifs <;> simp
    simp only [e, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  · simp only [coneRates_pairU_self g L hL E m hm hv0 hv1, coneRates_prod_one, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The propagated projected field of (C.35) [fo:eq:projected-error-equation] at one sample, for a
general tensor `F` of length `n + 1`: `|Σ_b coef_{r,v}(a, b)F(b)|`, with `𝒬_r` built from the
profile `θ_r` and the propagator `I + (v - r)P(I - vP)⁻¹`, is at most
`C_n(H^{2(n+1)}(ρℓ_u/ℓ_v)^{n+1} + 𝔓^{4(n+1)}τ_θ)X_F + C_n 𝔓^{4(n+1)}τ`, `𝔓 = H(1 + ρ)L/ℓ_u`, if
`|F| ≤ X_F`, `|F| ≤ τ` on words of diameter `> d`, the kernel at `r` is at most
`C_θ/((1 - r)ℓ_u)` and at most `τ_θ/((1 - r)ℓ_u)` at distance `> Hℓ_u/4`, and
`Ξ = (v - r)P(I - vP)⁻¹` has the profile bounds of the restoration with scales `ℓ_u ≤ ℓ_v`. -/
theorem coneRates_fieldProj (n : ℕ) (hn : 1 ≤ n) (C₁ Cθ : ℝ) (hC₁ : 0 < C₁) (hCθ : 1 ≤ Cθ) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (g E : ℝ) (m : ℂ) (L : ℕ), 3 ≤ L →
      IsDysonRootV (hopB g) (gammaG g) L E m →
      ∀ (r v ρ ℓu ℓv H d τ τθ XF : ℝ) (F : (Fin (n + 1) → Fin L) → ℂ) (a : Fin (n + 1) → Fin L),
      0 ≤ r → r ≤ v → v < 1 → (1 - r) / (1 - v) ≤ ρ →
      1 ≤ ℓu → ℓu ≤ ℓv → ℓu ≤ L → 1 ≤ H → 1 ≤ ρ * ℓu / ℓv → 0 ≤ d → 4 * d + 2 ≤ H * ℓu →
      0 ≤ τ → 0 ≤ τθ → τθ ≤ 1 →
      (∀ x y, mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) r x y ≤
        Cθ / ((1 - r) * ℓu)) →
      (∀ x y, H * ℓu / 4 < cycDist x y →
        mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) r x y ≤
          τθ / ((1 - r) * ℓu)) →
      (∀ x y, (v - r) * mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v x y ≤
        C₁ * ρ / ℓv) →
      (∀ x y y', |(v - r) * mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v x y -
          (v - r) * mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v x y'| ≤
        C₁ * ρ / ℓv * (((cycDist y y' : ℝ) + ℓu) / ℓv)) →
      (∀ b, ‖F b‖ ≤ XF) → (∀ b, d < wordDiam b → ‖F b‖ ≤ τ) →
      ‖∑ b, projCoef (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v r a b * F b‖ ≤
        Cn * (H ^ (2 * (n + 1)) * (ρ * ℓu / ℓv) ^ (n + 1) +
            (H * (1 + ρ) * (L / ℓu)) ^ (4 * (n + 1)) * τθ) * XF +
          Cn * (H * (1 + ρ) * (L / ℓu)) ^ (4 * (n + 1)) * τ := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨Cn₀, hCn₀, hres⟩ := coneRates_restoreProj (n + 1 + 1) (by omega) C₁ hC₁
  refine ⟨Cn₀ * (1 + 2 * Cθ ^ (n + 1)), by positivity, ?_⟩
  intro g E m L hL hm r v ρ ℓu ℓv H d τ τθ XF F a hr0 hrv hv1 hρ h1u huv huL hH hX hd hdH hτ hτθ0
    hτθ1 hbulk hfar hΞ hinc hF hFτ
  obtain ⟨hP, hrow⟩ := coneRates_P_facts g L hL E m hm
  have : NeZero L := ⟨by omega⟩
  set P := pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) with hPdef
  have hr1 : r < 1 := lt_of_le_of_lt hrv hv1
  have hℓu : 0 < ℓu := by linarith
  have hr1' : 0 < 1 - r := by linarith
  obtain ⟨hθ0, hθ1⟩ := (wardProfile_facts g L hL E m hm).2 r hr0 hr1
  have hθeq : ∀ x y, wardProfile P r (x - y) = (1 - r) * mixedKer P r y x := fun x y =>
    ((wardProfile_facts g L hL E m hm).1 r ⟨by linarith, hr1⟩ x y).2.1
  have hθC : ∀ x y, wardProfile P r (x - y) ≤ Cθ / ℓu := by
    intro x y
    rw [hθeq]
    calc (1 - r) * mixedKer P r y x ≤ (1 - r) * (Cθ / ((1 - r) * ℓu)) :=
          mul_le_mul_of_nonneg_left (hbulk y x) hr1'.le
      _ = Cθ / ℓu := by field_simp
  have hθτ : ∀ x y, H * ℓu / 4 < cycDist y x → wardProfile P r (x - y) ≤ τθ / ℓu := by
    intro x y hxy
    rw [hθeq]
    calc (1 - r) * mixedKer P r y x ≤ (1 - r) * (τθ / ((1 - r) * ℓu)) :=
          mul_le_mul_of_nonneg_left (hfar y x hxy) hr1'.le
      _ = τθ / ℓu := by field_simp
  have hdH' : d < H * ℓu := by linarith
  have hXF0 : 0 ≤ XF := (norm_nonneg _).trans (hF a)
  have hCθ0 : 0 ≤ Cθ := by linarith
  set α : ℝ := (2 * d + 1) / ℓu with hα
  set Q : ℝ := (L : ℝ) / ℓu with hQ
  have hα0 : 0 ≤ α := by positivity
  have hαH : α ≤ H := by rw [hα, div_le_iff₀ hℓu]; linarith
  have hQ1 : 1 ≤ Q := by rw [hQ, le_div_iff₀ hℓu]; linarith
  set SA : ℝ := XF + (α ^ (n + 1) * Cθ ^ (n + 1) * XF + Q ^ (n + 1) * Cθ ^ (n + 1) * τ) with hSA
  set τA : ℝ := τ + τθ * Cθ ^ n * (α ^ (n + 1) * XF + Q ^ (n + 1) * τ) with hτA
  have hτA0 : 0 ≤ τA := by positivity
  have hsup : ∀ b, ‖projQ (wardProfile P r) F b‖ ≤ SA := by
    intro b
    refine (coneRates_projQ_le _ F d XF τ hd hτ hF hFτ hθ0 b).trans ?_
    have hprod := coneRates_prod_le (fun j : Fin (n + 1) => wardProfile P r (b 0 - b j.succ))
      (Cθ / ℓu) (fun j => hθ0 _) (fun j => hθC _ _)
    have e : ((2 * d + 1) ^ (n + 1) * XF + (L : ℝ) ^ (n + 1) * τ) * (Cθ / ℓu) ^ (n + 1) =
        α ^ (n + 1) * Cθ ^ (n + 1) * XF + Q ^ (n + 1) * Cθ ^ (n + 1) * τ := by
      rw [hα, hQ, div_pow, div_pow, div_pow]
      field_simp
    calc _ ≤ XF + ((2 * d + 1) ^ (n + 1) * XF + (L : ℝ) ^ (n + 1) * τ) * (Cθ / ℓu) ^ (n + 1) :=
          add_le_add (hF b) (mul_le_mul_of_nonneg_left hprod (by positivity))
      _ = SA := by rw [e]
  have htail : ∀ b, H * ℓu < wordDiam b → ‖projQ (wardProfile P r) F b‖ ≤ τA := by
    intro b hb
    obtain ⟨j₀, hj₀⟩ := coneRates_far_first b (H * ℓu) (by positivity) hb
    refine (coneRates_projQ_le _ F d XF τ hd hτ hF hFτ hθ0 b).trans ?_
    have hprod := coneRates_prod_le_one (fun j : Fin (n + 1) => wardProfile P r (b 0 - b j.succ))
      (Cθ / ℓu) (τθ / ℓu) (fun j => hθ0 _) (fun j => hθC _ _) j₀ (hθτ _ _ (by
        rw [coneRates_cycDist_comm]
        have : H * ℓu / 4 < H * ℓu / 2 := by
          have : 0 < H * ℓu := by positivity
          linarith
        linarith))
    have e : ((2 * d + 1) ^ (n + 1) * XF + (L : ℝ) ^ (n + 1) * τ) *
        (τθ / ℓu * (Cθ / ℓu) ^ n) = τθ * Cθ ^ n * (α ^ (n + 1) * XF + Q ^ (n + 1) * τ) := by
      rw [hα, hQ, div_pow, div_pow, div_pow]
      field_simp
      ring
    calc _ ≤ τ + ((2 * d + 1) ^ (n + 1) * XF + (L : ℝ) ^ (n + 1) * τ) *
          (τθ / ℓu * (Cθ / ℓu) ^ n) :=
          add_le_add (hFτ b (by linarith)) (mul_le_mul_of_nonneg_left hprod (by positivity))
      _ = τA := by rw [e]
  have hb := hres g E m L hL hm r v ρ ℓu ℓv H SA τA (projQ (wardProfile P r) F) a hr0 hrv hv1 hρ
    h1u huv huL hH hX hτA0 hΞ hinc hsup htail (fun b₁ => coneRates_projQ_row _ hθ1 F b₁)
  rw [coneRates_coef_sum]
  refine hb.trans ?_
  -- the exponents
  have hℓv : 0 < ℓv := by linarith
  have hρ0 : 0 ≤ ρ := by
    by_contra hρ'
    push Not at hρ'
    have : ρ * ℓu / ℓv < 0 := div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hρ' hℓu) hℓv
    linarith
  set Xs : ℝ := ρ * ℓu / ℓv with hXs
  set Pp : ℝ := H * (1 + ρ) * Q with hPp
  have hXsρ : Xs ≤ 1 + ρ := by
    rw [hXs, div_le_iff₀ hℓv]
    nlinarith
  have hρ1 : 1 ≤ 1 + ρ := by linarith
  have hHρ : 1 ≤ H * (1 + ρ) := one_le_mul_of_one_le_of_one_le hH hρ1
  have hHP : H ≤ Pp := by
    rw [hPp, mul_assoc]
    exact le_mul_of_one_le_right (by linarith) (one_le_mul_of_one_le_of_one_le hρ1 hQ1)
  have hQP : Q ≤ Pp := le_mul_of_one_le_left (by linarith) hHρ
  have hXP : Xs ≤ Pp := by
    refine hXsρ.trans ?_
    calc 1 + ρ ≤ H * (1 + ρ) := le_mul_of_one_le_left (by linarith) hH
      _ ≤ Pp := le_mul_of_one_le_right (by linarith) hQ1
  have hP1 : 1 ≤ Pp := le_trans hH hHP
  have hXs0 : 0 ≤ Xs := by linarith
  set N := n + 1 + 1 with hN
  have pw : ∀ a b : ℕ, a ≤ b → Pp ^ a ≤ Pp ^ b := fun a b h => pow_le_pow_right₀ hP1 h
  have i1 : H ^ N * Xs ^ N ≤ H ^ (2 * N) * Xs ^ N :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hH (by omega)) (by positivity)
  have i2 : H ^ N * Xs ^ N * α ^ (n + 1) ≤ H ^ (2 * N) * Xs ^ N := by
    calc H ^ N * Xs ^ N * α ^ (n + 1) ≤ H ^ N * Xs ^ N * H ^ (n + 1) := by gcongr
      _ = H ^ (N + (n + 1)) * Xs ^ N := by rw [pow_add]; ring
      _ ≤ H ^ (2 * N) * Xs ^ N :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hH (by omega)) (by positivity)
  have i3 : H ^ N * Xs ^ N * Q ^ (n + 1) ≤ Pp ^ (4 * N) := by
    calc H ^ N * Xs ^ N * Q ^ (n + 1) ≤ Pp ^ N * Pp ^ N * Pp ^ (n + 1) := by gcongr
      _ = Pp ^ (N + N + (n + 1)) := by rw [← pow_add, ← pow_add]
      _ ≤ Pp ^ (4 * N) := pw _ _ (by omega)
  have i4 : Pp ^ (2 * N) ≤ Pp ^ (4 * N) := pw _ _ (by omega)
  have i5 : Pp ^ (2 * N) * α ^ (n + 1) ≤ Pp ^ (4 * N) := by
    calc Pp ^ (2 * N) * α ^ (n + 1) ≤ Pp ^ (2 * N) * Pp ^ (n + 1) := by
          gcongr
          exact hαH.trans hHP
      _ = Pp ^ (2 * N + (n + 1)) := (pow_add _ _ _).symm
      _ ≤ Pp ^ (4 * N) := pw _ _ (by omega)
  have i6 : Pp ^ (2 * N) * Q ^ (n + 1) ≤ Pp ^ (4 * N) := by
    calc Pp ^ (2 * N) * Q ^ (n + 1) ≤ Pp ^ (2 * N) * Pp ^ (n + 1) := by gcongr
      _ = Pp ^ (2 * N + (n + 1)) := (pow_add _ _ _).symm
      _ ≤ Pp ^ (4 * N) := pw _ _ (by omega)
  have hCθn : Cθ ^ n ≤ Cθ ^ (n + 1) := pow_le_pow_right₀ hCθ (by omega)
  have hCm0 : 0 ≤ Cθ ^ (n + 1) := by positivity
  have hCn0 : 0 ≤ Cθ ^ n := by positivity
  have hPP0 : 0 ≤ Pp ^ (4 * N) := by positivity
  have hHX0 : 0 ≤ H ^ (2 * N) * Xs ^ N := by positivity
  have j1 := mul_le_mul_of_nonneg_right i1 (mul_nonneg hCn₀.le hXF0)
  have j2 := mul_le_mul_of_nonneg_right i2 (mul_nonneg (mul_nonneg hCn₀.le hCm0) hXF0)
  have j3 := mul_le_mul_of_nonneg_right i3 (mul_nonneg (mul_nonneg hCn₀.le hCm0) hτ)
  have j4 := mul_le_mul_of_nonneg_right i4 (mul_nonneg hCn₀.le hτ)
  have j5 : Pp ^ (2 * N) * α ^ (n + 1) * (Cn₀ * (τθ * Cθ ^ n * XF)) ≤
      Pp ^ (4 * N) * (Cn₀ * (τθ * Cθ ^ (n + 1) * XF)) := by
    refine mul_le_mul i5 ?_ (by positivity) hPP0
    gcongr
  have j6 : Pp ^ (2 * N) * Q ^ (n + 1) * (Cn₀ * (τθ * Cθ ^ n * τ)) ≤
      Pp ^ (4 * N) * (Cn₀ * (1 * Cθ ^ (n + 1) * τ)) := by
    refine mul_le_mul i6 ?_ (by positivity) hPP0
    gcongr
  have s1 : 0 ≤ Cn₀ * Cθ ^ (n + 1) * (H ^ (2 * N) * Xs ^ N) * XF := by positivity
  have s2 : 0 ≤ Cn₀ * (1 + Cθ ^ (n + 1)) * (Pp ^ (4 * N) * τθ) * XF := by positivity
  rw [hSA, hτA]
  linarith [j1, j2, j3, j4, j5, j6, s1, s2]

/-- The propagated field of a word with a stable leg at one sample, for a general tensor `F` of
length `k`: `|Σ_b Π_j U_{r,v}^{σ_jσ_{j+1}}(a_j, b_j)F(b)| ≤
C_k H^{k-1}(ρℓ_u/ℓ_v)^{k-1}X_F + C_k((1 + ρ)L/ℓ_u)^kτ` for the propagators of (5.15)
[fo:eq:propagators], if `|F| ≤ X_F`, `|F| ≤ τ` on words of diameter `> d`,
`(v - r)P(I - vP)⁻¹ ≤ C₁ρ/ℓ_v`, and `γ_g Σ_b |M_{ab}|² ≤ C₁` and the rows of `(I - vQ)⁻¹` are at
most `C₁` (the Dyson bounds (6.2) [fo:eq:propagation-dyson]). -/
theorem coneRates_fieldStable (k : ℕ) (hk : 2 ≤ k) (C₁ : ℝ) (hC₁ : 0 < C₁) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (g E : ℝ) (m : ℂ) (L : ℕ), 3 ≤ L →
      IsDysonRootV (hopB g) (gammaG g) L E m →
      ∀ (r v ρ ℓu ℓv H d τ XF : ℝ) (σ : Fin k → Bool) (F : (Fin k → Fin L) → ℂ)
        (a : Fin k → Fin L),
      (∃ j, σ (finRotate k j) = σ j) →
      0 ≤ r → r ≤ v → v < 1 → (1 - r) / (1 - v) ≤ ρ →
      1 ≤ ℓu → ℓu ≤ ℓv → ℓu ≤ L → 1 ≤ H → 1 ≤ ρ * ℓu / ℓv → 0 ≤ d → 4 * d + 2 ≤ H * ℓu →
      0 ≤ τ →
      (∀ x y, (v - r) * mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v x y ≤
        C₁ * ρ / ℓv) →
      (∀ x, gammaG g * ∑ y, ‖dysonMat (hopB g) (gammaG g) L E m x y‖ ^ 2 ≤ C₁) →
      (∀ x, ∑ y, ‖(1 - (v : ℂ) • pairQ (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))⁻¹ x y‖ ≤
        C₁) →
      (∀ b, ‖F b‖ ≤ XF) → (∀ b, d < wordDiam b → ‖F b‖ ≤ τ) →
      ‖∑ b : Fin k → Fin L, (∏ j, pairU (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) r v (σ j)
          (σ (finRotate k j)) (a j) (b j)) * F b‖ ≤
        Cn * H ^ (k - 1) * (ρ * ℓu / ℓv) ^ (k - 1) * XF + Cn * ((1 + ρ) * (L / ℓu)) ^ k * τ := by
  obtain ⟨Cn, hCn, hst⟩ := coneRates_restoreStable k hk C₁ hC₁
  refine ⟨Cn, hCn, ?_⟩
  intro g E m L hL hm r v ρ ℓu ℓv H d τ XF σ F a hσ hr0 hrv hv1 _ h1u huv huL hH hX hd hdH hτ hΞ
    hM hR hF hFτ
  exact hst g E m L hL hm r v ρ ℓu ℓv H XF τ σ F a hσ hr0 hrv hv1 h1u huv huL hH hX hτ hΞ hM hR hF
    fun b hb => hFτ b (by linarith)

/-- The generator of the propagated projected field (C.35) [fo:eq:projected-error-equation] of a
cyclically alternating word of length `n + 1` at time `r` and one Hermitian matrix `M`: with
`𝔓 = H(1 + ρ)L/ℓ_u`, `|𝒢| ≤ C_n(H^{2(n+1)}(ρℓ_u/ℓ_v)^{n+1} + 𝔓^{4(n+1)}τ_θ)S + C_n𝔓^{4(n+1)}T`,
where `S = γ_g Wℓ_u(X₁Y + Σ_p κ_p X_{n+3-p} + Σ_p X_p X_{n+3-p}) + X_n/((1 - r)Wη_rℓ_u)` collects
the source terms of (C.32) [gc:eq:sourcetable] and the commutator with the Ward row (C.34)
[gc:eq:row], and `T = γ_g W Lτ(Σ_j X_j + Σ_j κ_j) + τ/((1 - r)Wη_rℓ_u)` the tails; the bounds on
the loop errors, loops and primitive loops at `M` are those of `coneRates_src`, and the kernel
bounds those of `coneRates_fieldProj`. -/
theorem coneRates_genProj (n : ℕ) (hn : 1 ≤ n) (C₁ Cθ : ℝ) (hC₁ : 0 < C₁) (hCθ : 1 ≤ Cθ) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (g E : ℝ) (m : ℂ) (W L : ℕ), 1 ≤ W → 3 ≤ L →
      IsDysonRootV (hopB g) (gammaG g) L E m →
      ∀ (r v : ℝ) (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ), M.IsHermitian →
      ∀ (σ : Fin (n + 1) → Bool), (∀ j, σ (finRotate (n + 1) j) = !σ j) →
      ∀ (a : Fin (n + 1) → Fin L) (X κ : ℕ → ℝ) (Y ρ ℓu ℓv H d τ τθ : ℝ),
      0 ≤ r → r ≤ v → v < 1 → (1 - r) / (1 - v) ≤ ρ →
      1 ≤ ℓu → ℓu ≤ ℓv → ℓu ≤ L → 1 ≤ H → 1 ≤ ρ * ℓu / ℓv → 0 ≤ d → 4 * d + 2 ≤ H * ℓu →
      0 ≤ τ → 0 ≤ τθ → τθ ≤ 1 →
      (∀ x y, mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) r x y ≤
        Cθ / ((1 - r) * ℓu)) →
      (∀ x y, H * ℓu / 4 < cycDist x y →
        mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) r x y ≤
          τθ / ((1 - r) * ℓu)) →
      (∀ x y, (v - r) * mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v x y ≤
        C₁ * ρ / ℓv) →
      (∀ x y y', |(v - r) * mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v x y -
          (v - r) * mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v x y'| ≤
        C₁ * ρ / ℓv * (((cycDist y y' : ℝ) + ℓu) / ℓv)) →
      (∀ j, 1 ≤ j → j ≤ n + 1 → ∀ (b : Fin j → Fin L) (s : Fin j → Bool),
        ‖loopTr (resolventMat M (zChar g E m r)) b s - primLoop g W L E m r b s‖ ≤ X j) →
      (∀ j, 2 ≤ j → j ≤ n + 1 → ∀ (b : Fin j → Fin L) (s : Fin j → Bool), d < wordDiam b →
        ‖loopTr (resolventMat M (zChar g E m r)) b s - primLoop g W L E m r b s‖ ≤ τ) →
      (∀ j, 3 ≤ j → j ≤ n + 1 → ∀ (b : Fin j → Fin L) (s : Fin j → Bool),
        ‖primLoop g W L E m r b s‖ ≤ κ j) →
      (∀ j, 3 ≤ j → j ≤ n + 1 → ∀ (b : Fin j → Fin L) (s : Fin j → Bool), d < wordDiam b →
        ‖primLoop g W L E m r b s‖ ≤ τ) →
      (∀ (b : Fin (n + 1 + 1) → Fin L) (s : Fin (n + 1 + 1) → Bool),
        ‖loopTr (resolventMat M (zChar g E m r)) b s‖ ≤ Y) →
      (∀ (b : Fin (n + 1 + 1) → Fin L) (s : Fin (n + 1 + 1) → Bool), d < wordDiam b →
        ‖loopTr (resolventMat M (zChar g E m r)) b s‖ ≤ τ) →
      ‖blockGen W L (gammaG g) (fun r' N => ∑ b,
          projCoef (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v r' a b *
            (resLoop g E m b σ r' N - primLoop g W L E m r' b σ)) r M‖ ≤
        Cn * (H ^ (2 * (n + 1)) * (ρ * ℓu / ℓv) ^ (n + 1) +
            (H * (1 + ρ) * (L / ℓu)) ^ (4 * (n + 1)) * τθ) *
          (gammaG g * W * ℓu * (X 1 * Y + ∑ p ∈ Finset.Icc 3 (n + 1), κ p * X (n + 3 - p) +
              ∑ p ∈ Finset.Icc 2 (n + 1), X p * X (n + 3 - p)) +
            X n / ((1 - r) * (W * etaChar g m r) * ℓu)) +
        Cn * (H * (1 + ρ) * (L / ℓu)) ^ (4 * (n + 1)) *
          (gammaG g * W * L * τ *
              (∑ j ∈ Finset.Icc 1 (n + 1), X j + ∑ j ∈ Finset.Icc 3 (n + 1), κ j) +
            τ / ((1 - r) * (W * etaChar g m r) * ℓu)) := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨Cn₀, hCn₀, hres⟩ := coneRates_restoreProj (n + 1 + 1) (by omega) C₁ hC₁
  refine ⟨12 * (Cn₀ * ((n + 1 + 1 : ℕ) : ℝ) ^ 2 * Cθ ^ (n + 1 + 1)), by positivity, ?_⟩
  intro g E m W L hW hL hm r v M hM σ hσ a X κ Y ρ ℓu ℓv H d τ τθ hr0 hrv hv1 hρ h1u huv huL hH
    hXs hd hdH hτ hτθ0 hτθ1 hbulk hfar hΞ hinc hX hXτ hκ hκτ hY hYτ
  obtain ⟨hP, hrow⟩ := coneRates_P_facts g L hL E m hm
  have : NeZero L := ⟨by omega⟩
  set P := pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) with hPdef
  have hr1 : r < 1 := lt_of_le_of_lt hrv hv1
  have hrI : r ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hr1⟩
  have hvI : v ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hv1⟩
  have hℓu : 0 < ℓu := by linarith
  have hr1' : 0 < 1 - r := by linarith
  obtain ⟨hθ0, hθ1⟩ := (wardProfile_facts g L hL E m hm).2 r hr0 hr1
  have hθeq : ∀ x y, wardProfile P r (x - y) = (1 - r) * mixedKer P r y x := fun x y =>
    ((wardProfile_facts g L hL E m hm).1 r hrI x y).2.1
  have hθC : ∀ x y, wardProfile P r (x - y) ≤ Cθ / ℓu := by
    intro x y
    rw [hθeq]
    calc (1 - r) * mixedKer P r y x ≤ (1 - r) * (Cθ / ((1 - r) * ℓu)) :=
          mul_le_mul_of_nonneg_left (hbulk y x) hr1'.le
      _ = Cθ / ℓu := by field_simp
  have hθC' : ∀ x, wardProfile P r x ≤ Cθ / ℓu := fun x => by simpa using hθC x 0
  have hθτ : ∀ x y, H * ℓu / 4 < cycDist y x → wardProfile P r (x - y) ≤ τθ / ℓu := by
    intro x y hxy
    rw [hθeq]
    calc (1 - r) * mixedKer P r y x ≤ (1 - r) * (τθ / ((1 - r) * ℓu)) :=
          mul_le_mul_of_nonneg_left (hfar y x hxy) hr1'.le
      _ = τθ / ℓu := by field_simp
  obtain ⟨hK0, hKrow⟩ := mixedKer_nonneg_row P hP hrow r hr0 hr1
  have hγ := coneRates_gamma_pos g
  have hγW : 0 ≤ gammaG g * W := by positivity
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  have hη : 0 < etaChar g m r := by
    unfold etaChar
    have := hm.1
    positivity
  have hCθ0 : 0 ≤ Cθ := by linarith
  have hH0 : 0 ≤ H := by linarith
  -- the sizes
  set a0 : Fin L := ⟨0, by omega⟩
  have hX0 : ∀ j, 1 ≤ j → j ≤ n + 1 + 1 → 0 ≤ X j := fun j h1 h2 =>
    (norm_nonneg _).trans (hX j h1 h2 (fun _ => a0) (fun _ => true))
  have hκ0 : ∀ j, 3 ≤ j → j ≤ n + 1 + 1 → 0 ≤ κ j := fun j h1 h2 =>
    (norm_nonneg _).trans (hκ j h1 h2 (fun _ => a0) (fun _ => true))
  have hY0 : 0 ≤ Y := (norm_nonneg _).trans (hY (fun _ => a0) (fun _ => true))
  obtain ⟨hSm0, hSt0⟩ := coneRates_sizes_nonneg (L := L) (k := n + 1 + 1) (by omega) X κ Y hX0 hκ0
    hY0
  have hsrc := fun b => coneRates_src g E m (k := n + 1 + 1) (by omega) r M X κ Y d τ hd hτ hX
    hXτ hκ hκτ hY hYτ b σ
  set Sm := X 1 * Y + ∑ p ∈ Finset.Icc 3 (n + 1 + 1), κ p * X (n + 1 + 3 - p) +
    ∑ p ∈ Finset.Icc 2 (n + 1 + 1), X p * X (n + 1 + 3 - p) with hSmdef
  set St := ∑ j ∈ Finset.Icc 1 (n + 1 + 1), X j + ∑ j ∈ Finset.Icc 3 (n + 1 + 1), κ j with hStdef
  set Nsq : ℝ := ((n + 1 + 1 : ℕ) : ℝ) ^ 2 with hNsq
  set Ssrc : ℝ := Nsq * (gammaG g * W) * ((2 * d + 1) * Sm + L * τ * St) with hSsrc
  set Tsrc : ℝ := 3 * Nsq * (gammaG g * W) * L * τ * St with hTsrc
  have hTsrc0 : 0 ≤ Tsrc := by positivity
  -- the Ward row
  have hσ' : σ (Fin.last (n + 1)) = !σ 0 := by
    have h := hσ (Fin.last (n + 1))
    rw [finRotate_last] at h
    rw [h, Bool.not_not]
  set Hh : ℝ := (W * etaChar g m r)⁻¹ * ((2 * d + 1) ^ n * X (n + 1) + (L : ℝ) ^ n * τ) with hHh
  have hh : ∀ c, ‖rowSum (fun b' => resLoop g E m b' σ r M - primLoop g W L E m r b' σ) c‖ ≤
      Hh := by
    intro c
    have := coneRates_rowWard g E m hW hL (by omega : 1 ≤ n + 1) hm hM hr0 hr1 (X (n + 1)) d τ hd
      hτ (hX (n + 1) (by omega) (by omega))
      (fun b s hb => by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · subst h0
          rw [coneRates_wordDiam_one] at hb
          simp at hb
          linarith
        · exact hXτ (n + 1) (by omega) (by omega) b s hb) σ hσ' c
    simpa only [Nat.add_sub_cancel] using this
  rw [blockGen_projField g E m hW hL (by omega) hm hrI hvI hM σ hσ a]
  -- the restored tensor
  set α : ℝ := (4 * d + 1) / ℓu with hα
  set β : ℝ := (2 * d + 1) / ℓu with hβ
  set Q : ℝ := (L : ℝ) / ℓu with hQ
  set Dn : ℝ := (1 - r) * (W * etaChar g m r) * ℓu with hDn
  have hDn0 : 0 < Dn := by positivity
  set Sc : ℝ := X (n + 1) / Dn with hSc
  set Tc : ℝ := τ / Dn with hTc
  have hα0 : 0 ≤ α := by positivity
  have hβ0 : 0 ≤ β := by positivity
  have hαH : α ≤ H := by rw [hα, div_le_iff₀ hℓu]; linarith
  have hβH : β ≤ H := by rw [hβ, div_le_iff₀ hℓu]; linarith
  have hQ1 : 1 ≤ Q := by rw [hQ, le_div_iff₀ hℓu]; linarith
  have hHhid : Hh / ((1 - r) * ℓu ^ (n + 1)) = β ^ n * Sc + Q ^ n * Tc := by
    rw [hHh, hβ, hQ, hSc, hTc, hDn, div_pow, div_pow]
    field_simp
    ring
  set SA : ℝ := Ssrc + Cθ ^ (n + 1) * (α ^ (n + 1) * Ssrc + Q ^ (n + 1) * Tsrc) +
    2 * Cθ ^ (n + 1) * (β ^ n * Sc + Q ^ n * Tc) with hSA
  set τA : ℝ := Tsrc + τθ * Cθ ^ n * (α ^ (n + 1) * Ssrc + Q ^ (n + 1) * Tsrc) +
    τθ * Cθ ^ n * (1 + Cθ * Q) * (β ^ n * Sc + Q ^ n * Tc) with hτA
  have hSc0 : 0 ≤ Sc := div_nonneg (hX0 _ (by omega) (by omega)) hDn0.le
  have hTc0 : 0 ≤ Tc := div_nonneg hτ hDn0.le
  have hτA0 : 0 ≤ τA := by positivity
  have hcomm := commutator_bound_cplx (k := n + 1) (mixedKer P r) (wardProfile P r)
    (fun c => rowSum (fun b' => resLoop g E m b' σ r M - primLoop g W L E m r b' σ) c) r Cθ ℓu Hh
    hK0 hKrow hr1 hθ0 hθ1 hθC' hℓu hh
  have hsrcR : ∀ b : Fin (n + 1 + 1) → Fin L, 2 * d < wordDiam b →
      ‖lightW g E m b σ r M + ((gammaG g * W : ℝ) : ℂ) *
        (cutSrcLin (fun _ c τ' => primLoop g W L E m r c τ')
            (errFam g E m (fun _ c τ' => primLoop g W L E m r c τ') r M) b σ +
          cutSrcQuad (errFam g E m (fun _ c τ' => primLoop g W L E m r c τ') r M) b σ)‖ ≤
        Tsrc := fun b hb => (hsrc b).2 hb
  have hsrcS : ∀ b : Fin (n + 1 + 1) → Fin L,
      ‖lightW g E m b σ r M + ((gammaG g * W : ℝ) : ℂ) *
        (cutSrcLin (fun _ c τ' => primLoop g W L E m r c τ')
            (errFam g E m (fun _ c τ' => primLoop g W L E m r c τ') r M) b σ +
          cutSrcQuad (errFam g E m (fun _ c τ' => primLoop g W L E m r c τ') r M) b σ)‖ ≤
        Ssrc := fun b => (hsrc b).1
  have hpq : ∀ b : Fin (n + 1 + 1) → Fin L,
      ((2 * (2 * d) + 1) ^ (n + 1) * Ssrc + (L : ℝ) ^ (n + 1) * Tsrc) =
        ℓu ^ (n + 1) * (α ^ (n + 1) * Ssrc + Q ^ (n + 1) * Tsrc) := fun b => by
    rw [hα, hQ, div_pow, div_pow]
    field_simp
    ring
  have hsupA : ∀ b : Fin (n + 1 + 1) → Fin L, ‖projQ (wardProfile P r)
      (fun b' => lightW g E m b' σ r M + ((gammaG g * W : ℝ) : ℂ) *
        (cutSrcLin (fun _ c τ' => primLoop g W L E m r c τ')
            (errFam g E m (fun _ c τ' => primLoop g W L E m r c τ') r M) b' σ +
          cutSrcQuad (errFam g E m (fun _ c τ' => primLoop g W L E m r c τ') r M) b' σ)) b +
      ∑ c, ((mixedKer P r (b 0) c : ℝ) : ℂ) *
        rowSum (fun b' => resLoop g E m b' σ r M - primLoop g W L E m r b' σ) c *
        (∏ j : Fin (n + 1), ((wardProfile P r (c - b j.succ) : ℝ) : ℂ) -
          ∏ j : Fin (n + 1), ((wardProfile P r (b 0 - b j.succ) : ℝ) : ℂ))‖ ≤ SA := by
    intro b
    refine (norm_add_le _ _).trans ?_
    have h1 := coneRates_projQ_le (wardProfile P r) _ (2 * d) Ssrc Tsrc (by linarith) hTsrc0 hsrcS
      hsrcR hθ0 b
    have hprod := coneRates_prod_le (fun j : Fin (n + 1) => wardProfile P r (b 0 - b j.succ))
      (Cθ / ℓu) (fun j => hθ0 _) (fun j => hθC _ _)
    have h2 := hcomm.2 (b 0) (fun j => b j.succ)
    have e2 : 2 * Cθ ^ (n + 1) * Hh / ((1 - r) * ℓu ^ (n + 1)) =
        2 * Cθ ^ (n + 1) * (β ^ n * Sc + Q ^ n * Tc) := by
      rw [← hHhid]; ring
    rw [e2] at h2
    have e1 : ((2 * (2 * d) + 1) ^ (n + 1) * Ssrc + (L : ℝ) ^ (n + 1) * Tsrc) *
        (Cθ / ℓu) ^ (n + 1) = Cθ ^ (n + 1) * (α ^ (n + 1) * Ssrc + Q ^ (n + 1) * Tsrc) := by
      rw [hpq b, div_pow Cθ ℓu]
      generalize α ^ (n + 1) * Ssrc + Q ^ (n + 1) * Tsrc = Z
      field_simp
    have h3 := h1.trans (le_of_le_of_eq (add_le_add (hsrcS b)
      (mul_le_mul_of_nonneg_left hprod (by positivity))) (by rw [e1]))
    rw [hSA]
    linarith
  have htailA : ∀ b : Fin (n + 1 + 1) → Fin L, H * ℓu < wordDiam b → ‖projQ (wardProfile P r)
      (fun b' => lightW g E m b' σ r M + ((gammaG g * W : ℝ) : ℂ) *
        (cutSrcLin (fun _ c τ' => primLoop g W L E m r c τ')
            (errFam g E m (fun _ c τ' => primLoop g W L E m r c τ') r M) b' σ +
          cutSrcQuad (errFam g E m (fun _ c τ' => primLoop g W L E m r c τ') r M) b' σ)) b +
      ∑ c, ((mixedKer P r (b 0) c : ℝ) : ℂ) *
        rowSum (fun b' => resLoop g E m b' σ r M - primLoop g W L E m r b' σ) c *
        (∏ j : Fin (n + 1), ((wardProfile P r (c - b j.succ) : ℝ) : ℂ) -
          ∏ j : Fin (n + 1), ((wardProfile P r (b 0 - b j.succ) : ℝ) : ℂ))‖ ≤ τA := by
    intro b hb
    refine (norm_add_le _ _).trans ?_
    obtain ⟨j₀, hj₀⟩ := coneRates_far_first b (H * ℓu) (by positivity) hb
    have h1 := coneRates_projQ_le (wardProfile P r) _ (2 * d) Ssrc Tsrc (by linarith) hTsrc0 hsrcS
      hsrcR hθ0 b
    have hprod := coneRates_prod_le_one (fun j : Fin (n + 1) => wardProfile P r (b 0 - b j.succ))
      (Cθ / ℓu) (τθ / ℓu) (fun j => hθ0 _) (fun j => hθC _ _) j₀ (hθτ _ _ (by
        rw [coneRates_cycDist_comm]
        have : H * ℓu / 4 < H * ℓu / 2 := by
          have : 0 < H * ℓu := mul_pos (by linarith) hℓu
          linarith
        linarith))
    have e1 : ((2 * (2 * d) + 1) ^ (n + 1) * Ssrc + (L : ℝ) ^ (n + 1) * Tsrc) *
        (τθ / ℓu * (Cθ / ℓu) ^ n) = τθ * Cθ ^ n * (α ^ (n + 1) * Ssrc + Q ^ (n + 1) * Tsrc) := by
      rw [hpq b, div_pow Cθ ℓu]
      generalize α ^ (n + 1) * Ssrc + Q ^ (n + 1) * Tsrc = Z
      field_simp
      ring
    have h3 := h1.trans (le_of_le_of_eq (add_le_add (hsrcR b (by linarith))
      (mul_le_mul_of_nonneg_left hprod (by positivity))) (by rw [e1]))
    have h2 := coneRates_comm_tail (mixedKer P r) (wardProfile P r)
      (fun c => rowSum (fun b' => resLoop g E m b' σ r M - primLoop g W L E m r b' σ) c) r Cθ ℓu H
      τθ Hh hK0 hKrow hr1 hℓu hH0 hτθ0 hθ0 hθC' hθτ (fun x y hxy => hfar x y hxy) hh b hb
    have e2 : Hh * ((1 - r)⁻¹ * (τθ / ℓu * (Cθ / ℓu) ^ n) +
        L * (τθ / ((1 - r) * ℓu) * (Cθ / ℓu) ^ (n + 1))) =
        τθ * Cθ ^ n * (1 + Cθ * Q) * (Hh / ((1 - r) * ℓu ^ (n + 1))) := by
      rw [div_pow Cθ ℓu, div_pow Cθ ℓu, hQ]
      field_simp
      ring
    rw [e2, hHhid] at h2
    rw [hτA]
    linarith
  have hzero : ∀ b₁ : Fin L, ∑ b : Fin (n + 1 + 1) → Fin L, (if b ⟨0, by omega⟩ = b₁ then
      projQ (wardProfile P r)
        (fun b' => lightW g E m b' σ r M + ((gammaG g * W : ℝ) : ℂ) *
          (cutSrcLin (fun _ c τ' => primLoop g W L E m r c τ')
              (errFam g E m (fun _ c τ' => primLoop g W L E m r c τ') r M) b' σ +
            cutSrcQuad (errFam g E m (fun _ c τ' => primLoop g W L E m r c τ') r M) b' σ)) b +
        ∑ c, ((mixedKer P r (b 0) c : ℝ) : ℂ) *
          rowSum (fun b' => resLoop g E m b' σ r M - primLoop g W L E m r b' σ) c *
          (∏ j : Fin (n + 1), ((wardProfile P r (c - b j.succ) : ℝ) : ℂ) -
            ∏ j : Fin (n + 1), ((wardProfile P r (b 0 - b j.succ) : ℝ) : ℂ)) else 0) = 0 := by
    intro b₁
    have e : ∀ (x y : ℂ) (b : Fin (n + 1 + 1) → Fin L),
        (if b ⟨0, by omega⟩ = b₁ then x + y else 0) =
          (if b 0 = b₁ then x else 0) + (if b 0 = b₁ then y else 0) := fun x y b => by
      have : (⟨0, by omega⟩ : Fin (n + 1 + 1)) = 0 := rfl
      rw [this]
      split_ifs <;> simp
    simp only [e, Finset.sum_add_distrib]
    rw [coneRates_projQ_row _ hθ1, zero_add, coneRates_row_cons]
    simp only [Fin.cons_zero, Fin.cons_succ]
    exact hcomm.1 b₁
  refine (hres g E m L hL hm r v ρ ℓu ℓv H SA τA _ a hr0 hrv hv1 hρ h1u huv huL hH hXs hτA0 hΞ
    hinc hsupA htailA hzero).trans ?_
  -- the exponents
  have hℓv : 0 < ℓv := by linarith
  have hρ0 : 0 ≤ ρ := by
    by_contra hρ'
    push Not at hρ'
    have : ρ * ℓu / ℓv < 0 := div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hρ' hℓu) hℓv
    linarith
  have hρ1 : 1 ≤ 1 + ρ := by linarith
  have hXsρ : ρ * ℓu / ℓv ≤ 1 + ρ := by
    rw [div_le_iff₀ hℓv]
    calc ρ * ℓu ≤ ρ * ℓv := mul_le_mul_of_nonneg_left huv hρ0
      _ ≤ (1 + ρ) * ℓv := by linarith
  have hHρ : 1 ≤ H * (1 + ρ) := one_le_mul_of_one_le_of_one_le hH hρ1
  have hHP : H ≤ H * (1 + ρ) * Q := by
    rw [mul_assoc]
    exact le_mul_of_one_le_right hH0 (one_le_mul_of_one_le_of_one_le hρ1 hQ1)
  have hQP : Q ≤ H * (1 + ρ) * Q := le_mul_of_one_le_left (by linarith) hHρ
  have hXP : ρ * ℓu / ℓv ≤ H * (1 + ρ) * Q := by
    refine hXsρ.trans ?_
    calc 1 + ρ ≤ H * (1 + ρ) := le_mul_of_one_le_left (by linarith) hH
      _ ≤ H * (1 + ρ) * Q := le_mul_of_one_le_right (by linarith) hQ1
  have hNsq : 1 ≤ Nsq := by
    rw [hNsq]
    have : (1 : ℝ) ≤ ((n + 1 + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 1 + 1)
    exact one_le_pow₀ this
  have hS1 : 0 ≤ gammaG g * W * ℓu * Sm := by positivity
  have hT1 : 0 ≤ gammaG g * W * L * τ * St := by positivity
  have hSsrcB : Ssrc ≤ Nsq * (H * (gammaG g * W * ℓu * Sm) + gammaG g * W * L * τ * St) := by
    rw [hSsrc]
    have h2 : (2 * d + 1) * Sm ≤ H * ℓu * Sm := mul_le_mul_of_nonneg_right (by linarith) hSm0
    have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg (by linarith : (0 : ℝ) ≤ Nsq) hγW)
    linarith
  have hTsrcB : Tsrc = 3 * Nsq * (gammaG g * W * L * τ * St) := by rw [hTsrc]; ring
  have key := coneRates_genProj_arith n Cn₀ Cθ H (ρ * ℓu / ℓv) (H * (1 + ρ) * Q) Q α β τθ
    (gammaG g * W * ℓu * Sm) Sc (gammaG g * W * L * τ * St) Tc Ssrc Tsrc Nsq hCn₀.le hCθ hH
    (by positivity) hHP hXP hQP hQ1 hα0 hαH hβ0 hβH hτθ0 hτθ1 hS1 hSc0 hT1 hTc0 hNsq hSsrcB
    hTsrcB
  rw [hSA, hτA]
  refine key.trans (le_of_eq ?_)
  rw [hSc, hTc, hDn, hQ]

/-- The generator of the propagated field of a word of length `k` with a stable leg (a pair of
equal neighbouring signs) at time `r` and one Hermitian matrix `M`: with the one-label
propagators of (5.15) [fo:eq:propagators], `|𝒢| ≤ C_k H^k(ρℓ_u/ℓ_v)^{k-1}S +
C_k(H(1 + ρ)L/ℓ_u)^{2k}T`, where `S = γ_g Wℓ_u(X₁Y + Σ_p κ_p X_{k+2-p} + Σ_p X_p X_{k+2-p})` and
`T = γ_g W Lτ(Σ_j X_j + Σ_j κ_j)`, under the bounds of `coneRates_src` at `M` and of
`coneRates_fieldStable`. -/
theorem coneRates_genStable (k : ℕ) (hk : 2 ≤ k) (C₁ : ℝ) (hC₁ : 0 < C₁) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (g E : ℝ) (m : ℂ) (W L : ℕ), 1 ≤ W → 3 ≤ L →
      IsDysonRootV (hopB g) (gammaG g) L E m →
      ∀ (r v : ℝ) (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ), M.IsHermitian →
      ∀ (σ : Fin k → Bool), (∃ j, σ (finRotate k j) = σ j) →
      ∀ (a : Fin k → Fin L) (X κ : ℕ → ℝ) (Y ρ ℓu ℓv H d τ : ℝ),
      0 ≤ r → r ≤ v → v < 1 → (1 - r) / (1 - v) ≤ ρ →
      1 ≤ ℓu → ℓu ≤ ℓv → ℓu ≤ L → 1 ≤ H → 1 ≤ ρ * ℓu / ℓv → 0 ≤ d → 4 * d + 2 ≤ H * ℓu →
      0 ≤ τ →
      (∀ x y, (v - r) * mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v x y ≤
        C₁ * ρ / ℓv) →
      (∀ x, gammaG g * ∑ y, ‖dysonMat (hopB g) (gammaG g) L E m x y‖ ^ 2 ≤ C₁) →
      (∀ x, ∑ y, ‖(1 - (v : ℂ) • pairQ (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))⁻¹ x y‖ ≤
        C₁) →
      (∀ j, 1 ≤ j → j ≤ k → ∀ (b : Fin j → Fin L) (s : Fin j → Bool),
        ‖loopTr (resolventMat M (zChar g E m r)) b s - primLoop g W L E m r b s‖ ≤ X j) →
      (∀ j, 2 ≤ j → j ≤ k → ∀ (b : Fin j → Fin L) (s : Fin j → Bool), d < wordDiam b →
        ‖loopTr (resolventMat M (zChar g E m r)) b s - primLoop g W L E m r b s‖ ≤ τ) →
      (∀ j, 3 ≤ j → j ≤ k → ∀ (b : Fin j → Fin L) (s : Fin j → Bool),
        ‖primLoop g W L E m r b s‖ ≤ κ j) →
      (∀ j, 3 ≤ j → j ≤ k → ∀ (b : Fin j → Fin L) (s : Fin j → Bool), d < wordDiam b →
        ‖primLoop g W L E m r b s‖ ≤ τ) →
      (∀ (b : Fin (k + 1) → Fin L) (s : Fin (k + 1) → Bool),
        ‖loopTr (resolventMat M (zChar g E m r)) b s‖ ≤ Y) →
      (∀ (b : Fin (k + 1) → Fin L) (s : Fin (k + 1) → Bool), d < wordDiam b →
        ‖loopTr (resolventMat M (zChar g E m r)) b s‖ ≤ τ) →
      ‖blockGen W L (gammaG g) (fun r' N => ∑ b : Fin k → Fin L,
          (∏ j, pairU (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) r' v (σ j)
            (σ (finRotate k j)) (a j) (b j)) *
            (resLoop g E m b σ r' N - primLoop g W L E m r' b σ)) r M‖ ≤
        Cn * H ^ k * (ρ * ℓu / ℓv) ^ (k - 1) *
            (gammaG g * W * ℓu * (X 1 * Y + ∑ p ∈ Finset.Icc 3 k, κ p * X (k + 2 - p) +
              ∑ p ∈ Finset.Icc 2 k, X p * X (k + 2 - p))) +
          Cn * (H * (1 + ρ) * (L / ℓu)) ^ (2 * k) *
            (gammaG g * W * L * τ * (∑ j ∈ Finset.Icc 1 k, X j + ∑ j ∈ Finset.Icc 3 k, κ j)) := by
  obtain ⟨Cn₀, hCn₀, hst⟩ := coneRates_restoreStable k hk C₁ hC₁
  refine ⟨4 * (k : ℝ) ^ 2 * Cn₀, by positivity, ?_⟩
  intro g E m W L hW hL hm r v M hM σ hσ a X κ Y ρ ℓu ℓv H d τ hr0 hrv hv1 _ h1u huv huL hH hXs hd
    hdH hτ hΞ hMb hR hX hXτ hκ hκτ hY hYτ
  have hr1 : r < 1 := lt_of_le_of_lt hrv hv1
  have hrI : r ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hr1⟩
  have hvI : v ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hv1⟩
  rw [blockGen_propagated g E m hm.1 hk hr1 hM
    (fun r' n c τ' => primLoop g W L E m r' (k := n) c τ')
    (coneRates_primDeriv g W L hW hL E m hm r hrI)
    (fun x y s t => primLoop_two_swap g W L E m r x y s t) σ
    (fun j r' => pairU (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) r' v (σ j)
      (σ (finRotate k j)))
    (fun j x y => pairU_hasDerivAt g W L hW hL E m hm (σ j) (σ (finRotate k j)) hrI hvI x y) a]
  have hk0 : 0 < k := by omega
  have hL0 : 0 < L := by omega
  set a0 : Fin L := ⟨0, hL0⟩
  have hX0 : ∀ j, 1 ≤ j → j ≤ k → 0 ≤ X j := fun j h1 h2 =>
    (norm_nonneg _).trans (hX j h1 h2 (fun _ => a0) (fun _ => true))
  have hκ0 : ∀ j, 3 ≤ j → j ≤ k → 0 ≤ κ j := fun j h1 h2 =>
    (norm_nonneg _).trans (hκ j h1 h2 (fun _ => a0) (fun _ => true))
  have hY0 : 0 ≤ Y := (norm_nonneg _).trans (hY (fun _ => a0) (fun _ => true))
  obtain ⟨hSm, hSτ⟩ := coneRates_sizes_nonneg (L := L) hk X κ Y hX0 hκ0 hY0
  set Sm := X 1 * Y + ∑ p ∈ Finset.Icc 3 k, κ p * X (k + 2 - p) +
    ∑ p ∈ Finset.Icc 2 k, X p * X (k + 2 - p) with hSmdef
  set Sτ := ∑ j ∈ Finset.Icc 1 k, X j + ∑ j ∈ Finset.Icc 3 k, κ j with hSτdef
  have hγW : 0 ≤ gammaG g * W := by have := coneRates_gamma_pos g; positivity
  have hsrc := fun b => coneRates_src g E m hk r M X κ Y d τ hd hτ hX hXτ hκ hκτ hY hYτ b σ
  have hT0 : 0 ≤ 3 * (k : ℝ) ^ 2 * (gammaG g * W) * L * τ * Sτ := by positivity
  have hb := hst g E m L hL hm r v ρ ℓu ℓv H
    ((k : ℝ) ^ 2 * (gammaG g * W) * ((2 * d + 1) * Sm + L * τ * Sτ))
    (3 * (k : ℝ) ^ 2 * (gammaG g * W) * L * τ * Sτ) σ _ a hσ hr0 hrv hv1 h1u huv huL hH hXs hT0
    hΞ hMb hR (fun b => (hsrc b).1) (fun b hb => (hsrc b).2 (by linarith))
  refine hb.trans ?_
  -- the exponents
  have hℓu : 0 < ℓu := by linarith
  have hℓv : 0 < ℓv := by linarith
  have hρ0 : 0 ≤ ρ := by
    by_contra hρ'
    push Not at hρ'
    have : ρ * ℓu / ℓv < 0 := div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hρ' hℓu) hℓv
    linarith
  set Xs : ℝ := ρ * ℓu / ℓv with hXsdef
  set Q : ℝ := (L : ℝ) / ℓu with hQ
  have hQ1 : 1 ≤ Q := by rw [hQ, le_div_iff₀ hℓu]; linarith
  set Pp : ℝ := H * (1 + ρ) * Q with hPp
  have hρ1 : 1 ≤ 1 + ρ := by linarith
  have hHρ : 1 ≤ H * (1 + ρ) := one_le_mul_of_one_le_of_one_le hH hρ1
  have hXsρ : Xs ≤ 1 + ρ := by
    rw [hXsdef, div_le_iff₀ hℓv]
    nlinarith
  have hHP : H ≤ Pp := by
    rw [hPp, mul_assoc]
    exact le_mul_of_one_le_right (by linarith) (one_le_mul_of_one_le_of_one_le hρ1 hQ1)
  have hXP : Xs ≤ Pp := by
    refine hXsρ.trans ?_
    calc 1 + ρ ≤ H * (1 + ρ) := le_mul_of_one_le_left (by linarith) hH
      _ ≤ Pp := le_mul_of_one_le_right (by linarith) hQ1
  have hρQP : (1 + ρ) * Q ≤ Pp := by
    rw [hPp, mul_assoc]
    exact le_mul_of_one_le_left (by positivity) hH
  have hP1 : 1 ≤ Pp := le_trans hH hHP
  have hXs0 : 0 ≤ Xs := by linarith
  have hHk : H ^ k = H ^ (k - 1) * H := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have i1 : H ^ (k - 1) * Xs ^ (k - 1) ≤ Pp ^ (2 * k) := by
    calc H ^ (k - 1) * Xs ^ (k - 1) ≤ Pp ^ (k - 1) * Pp ^ (k - 1) := by gcongr
      _ = Pp ^ (k - 1 + (k - 1)) := (pow_add _ _ _).symm
      _ ≤ Pp ^ (2 * k) := pow_le_pow_right₀ hP1 (by omega)
  have i2 : ((1 + ρ) * Q) ^ k ≤ Pp ^ (2 * k) := by
    calc ((1 + ρ) * Q) ^ k ≤ Pp ^ k := by gcongr
      _ ≤ Pp ^ (2 * k) := pow_le_pow_right₀ hP1 (by omega)
  have hdl : 2 * d + 1 ≤ H * ℓu := by linarith
  have hk2 : 0 ≤ (k : ℝ) ^ 2 := by positivity
  have hHX : 0 ≤ H ^ (k - 1) * Xs ^ (k - 1) := by positivity
  have j1 : Cn₀ * H ^ (k - 1) * Xs ^ (k - 1) * ((k : ℝ) ^ 2 * (gammaG g * W) * ((2 * d + 1) * Sm))
      ≤ Cn₀ * (k : ℝ) ^ 2 * (H ^ k * Xs ^ (k - 1) * (gammaG g * W * ℓu * Sm)) := by
    rw [hHk]
    have : (2 * d + 1) * Sm ≤ H * ℓu * Sm := mul_le_mul_of_nonneg_right hdl hSm
    have h' := mul_le_mul_of_nonneg_left this
      (mul_nonneg (mul_nonneg (mul_nonneg hCn₀.le hHX) hk2) hγW)
    linarith [h']
  have j2 : Cn₀ * H ^ (k - 1) * Xs ^ (k - 1) * ((k : ℝ) ^ 2 * (gammaG g * W) * (L * τ * Sτ)) ≤
      Cn₀ * (k : ℝ) ^ 2 * (Pp ^ (2 * k) * (gammaG g * W * L * τ * Sτ)) := by
    have h0 : 0 ≤ gammaG g * W * L * τ * Sτ := by positivity
    have h' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right i1 h0)
      (mul_nonneg hCn₀.le hk2)
    linarith [h']
  have j3 : Cn₀ * ((1 + ρ) * Q) ^ k * (3 * (k : ℝ) ^ 2 * (gammaG g * W) * L * τ * Sτ) ≤
      3 * Cn₀ * (k : ℝ) ^ 2 * (Pp ^ (2 * k) * (gammaG g * W * L * τ * Sτ)) := by
    have h0 : 0 ≤ gammaG g * W * L * τ * Sτ := by positivity
    have h' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right i2 h0)
      (mul_nonneg hCn₀.le hk2)
    linarith [h']
  have s1 : 0 ≤ Cn₀ * (k : ℝ) ^ 2 * (H ^ k * Xs ^ (k - 1) * (gammaG g * W * ℓu * Sm)) := by
    positivity
  have e : Cn₀ * H ^ (k - 1) * Xs ^ (k - 1) *
      ((k : ℝ) ^ 2 * (gammaG g * W) * ((2 * d + 1) * Sm + L * τ * Sτ)) =
      Cn₀ * H ^ (k - 1) * Xs ^ (k - 1) * ((k : ℝ) ^ 2 * (gammaG g * W) * ((2 * d + 1) * Sm)) +
      Cn₀ * H ^ (k - 1) * Xs ^ (k - 1) * ((k : ℝ) ^ 2 * (gammaG g * W) * (L * τ * Sτ)) := by ring
  rw [e]
  have s2 : 0 ≤ Cn₀ * (k : ℝ) ^ 2 * (Pp ^ (2 * k) * (gammaG g * W * L * τ * Sτ)) := by positivity
  linarith [j1, j2, j3, s1, s2]

end LSBA
