import LSBA.Loop.ProjField
import LSBA.Kernel.Restore
import LSBA.Loop.SourceTail

/-!
# Deterministic brackets of the propagated loop-error fields of Step 3

The bracket (5.9) [gc:eq:bracket] of the propagated projected field (C.35)
[fo:eq:projected-error-equation] (cyclically alternating words) and of the propagated field
(other words) at one Hermitian matrix and one time `r ≤ v` of Step 3 of Appendix C.3
[sec:gc-one-step], bounded by the loops of length `2k + 2` and their tails, the input of the
`√B_{2n+2}` term of (C.36) [gc:eq:recurrence].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Joined loops of the bracket -/

/-- The factor `X^{s} E_x` of a loop for a signed label. -/
private def cbF {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (p : Bool × Fin L) :
    Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  sgnMat G p.1 * blockE W L p.2

/-- The ordered product of the factors of a list of signed labels. -/
private def cbProd {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (l : List (Bool × Fin L)) : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  (l.map (cbF G)).prod

private lemma cbProd_append {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (l l' : List (Bool × Fin L)) : cbProd G (l ++ l') = cbProd G l * cbProd G l' := by
  simp [cbProd]

private lemma cbProd_cons {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (p : Bool × Fin L) (l : List (Bool × Fin L)) : cbProd G (p :: l) = cbF G p * cbProd G l := by
  simp [cbProd]

/-- A list of signed labels of length `n` is a loop word of length `n` with the same trace. -/
private lemma cb_ofList {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (P : List (Bool × Fin L)) (n : ℕ) (hn : P.length = n) :
    ∃ (w : Fin n → Fin L) (s : Fin n → Bool), loopTr G w s = (cbProd G P).trace ∧
      ∀ x ∈ P, ∃ p, w p = x.2 := by
  subst hn
  refine ⟨fun p => (P.get p).2, fun p => (P.get p).1, ?_, ?_⟩
  · unfold loopTr cbProd
    congr 2
    apply List.ext_getElem <;> simp [cbF]
  · intro x hx
    obtain ⟨p, hp⟩ := List.mem_iff_get.mp hx
    exact ⟨p, by simp only [← hp]⟩

private lemma cb_blockE_conj {W L : ℕ} (c : Fin L) : (blockE W L c)ᴴ = blockE W L c := by
  rw [blockE, Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  by_cases h : p.1 = c <;> simp [h]

private lemma cb_sgn_conj {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (s : Bool) : (sgnMat G s)ᴴ = sgnMat G (!s) := by
  cases s <;> simp [sgnMat]

/-- The conjugate transpose of a list product is the product over the reversed list of the
conjugate factors. -/
private lemma cbProd_conj {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (l : List (Bool × Fin L)) :
    (cbProd G l)ᴴ = (l.reverse.map fun p => blockE W L p.2 * sgnMat G (!p.1)).prod := by
  induction l with
  | nil => simp [cbProd]
  | cons p l ih =>
    rw [cbProd_cons, Matrix.conjTranspose_mul, ih, List.reverse_cons, List.map_append,
      List.prod_append]
    simp [cbF, cb_blockE_conj, cb_sgn_conj]

/-- Signs shifted by one position along a list. -/
private def cbSh {L : ℕ} : Bool → List (Bool × Fin L) → List (Bool × Fin L)
  | _, [] => []
  | t, p :: r => (t, p.2) :: cbSh (!p.1) r

/-- The last shifted sign. -/
private def cbLst {L : ℕ} : Bool → List (Bool × Fin L) → Bool
  | t, [] => t
  | _, p :: r => cbLst (!p.1) r

private lemma cbSh_length {L : ℕ} (t : Bool) (r : List (Bool × Fin L)) :
    (cbSh t r).length = r.length := by
  induction r generalizing t with
  | nil => rfl
  | cons p r ih => simp [cbSh, ih]

/-- Shifting the signs keeps every label. -/
private lemma cbSh_mem {L : ℕ} (r : List (Bool × Fin L)) :
    ∀ (t : Bool) (x : Bool × Fin L), x ∈ r → ∃ s, (s, x.2) ∈ cbSh t r := by
  induction r with
  | nil => intro t x hx; simp at hx
  | cons p r ih =>
    intro t x hx
    rcases List.mem_cons.mp hx with h | h
    · exact ⟨t, by simp [cbSh, h]⟩
    · obtain ⟨s, hs⟩ := ih (!p.1) x h
      exact ⟨s, by simp only [cbSh, List.mem_cons]; exact Or.inr hs⟩

private lemma cb_regroup {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (r : List (Bool × Fin L)) : ∀ t : Bool,
    sgnMat G t * (r.map fun p => blockE W L p.2 * sgnMat G (!p.1)).prod =
      cbProd G (cbSh t r) * sgnMat G (cbLst t r) := by
  induction r with
  | nil => intro t; simp [cbSh, cbLst, cbProd]
  | cons p r ih =>
    intro t
    have h := ih (!p.1)
    simp only [cbSh, cbLst, cbProd_cons, List.map_cons, List.prod_cons, cbF]
    simp only [cbProd] at h
    calc sgnMat G t * (blockE W L p.2 * sgnMat G (!p.1) *
          (r.map fun p => blockE W L p.2 * sgnMat G (!p.1)).prod)
        = sgnMat G t * blockE W L p.2 * (sgnMat G (!p.1) *
          (r.map fun p => blockE W L p.2 * sgnMat G (!p.1)).prod) := by simp only [mul_assoc]
      _ = _ := by rw [h]; simp only [mul_assoc, cbProd]

/-- The signed labels of the word `a`, `σ` read cyclically from position `i`. -/
private def cbRead {L k : ℕ} (a : Fin k → Fin L) (σ : Fin k → Bool) (i : Fin k) :
    List (Bool × Fin L) :=
  List.ofFn fun p : Fin k => (σ (i + p), a (i + p))

private lemma cbRead_length {L k : ℕ} (a : Fin k → Fin L) (σ : Fin k → Bool) (i : Fin k) :
    (cbRead a σ i).length = k := by simp [cbRead]

/-- The cyclic reading from `i` contains every signed label of the word. -/
private lemma cbRead_mem {L k : ℕ} (a : Fin k → Fin L) (σ : Fin k → Bool) (i i₀ : Fin k) :
    (σ i₀, a i₀) ∈ cbRead a σ i := by
  have : NeZero k := ⟨by rintro rfl; exact i.elim0⟩
  simp only [cbRead, List.mem_ofFn]
  exact ⟨i₀ - i, by simp⟩

private lemma loopB_eq_cbProd {W L k : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a : Fin k → Fin L) (σ : Fin k → Bool) (i : Fin k) :
    loopB G a σ i = cbProd G (cbRead a σ i) * sgnMat G (σ i) := by
  unfold loopB cbProd cbRead
  rw [List.map_ofFn]
  rfl

/-- One term of the bracket sum (5.9) [gc:eq:bracket] as `W²` times a loop of length
`k + k' + 2` whose labels contain all labels of both words. -/
private lemma cb_bracket_term {W L k k' : ℕ}
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a : Fin k → Fin L) (σ : Fin k → Bool)
    (a' : Fin k' → Fin L) (σ' : Fin k' → Bool) (i : Fin k) (j : Fin k') (c : Fin L) :
    ∃ (w : Fin (k + k' + 2) → Fin L) (s : Fin (k + k' + 2) → Bool),
      (((W : ℂ) • blockE W L c) * loopB G a σ i * ((W : ℂ) • blockE W L c) *
        (loopB G a' σ' j)ᴴ).trace = (W : ℂ) ^ 2 * loopTr G w s ∧
      ∀ q, ∃ p, w p = Fin.append a a' q := by
  set A := cbRead a σ i with hA
  set A' := cbRead a' σ' j with hA'
  set t0 : Bool := !σ' j
  set ℓ := cbLst t0 A'.reverse
  set P : List (Bool × Fin L) := (ℓ, c) :: (A ++ ((σ i, c) :: cbSh t0 A'.reverse)) with hP
  have hlen : P.length = k + k' + 2 := by
    simp [hP, hA, cbRead_length, cbSh_length, hA', cbRead_length]
    ring
  obtain ⟨w, s, hw, hmem⟩ := cb_ofList G P _ hlen
  refine ⟨w, s, ?_, ?_⟩
  · rw [hw]
    have hB : (loopB G a' σ' j)ᴴ =
        sgnMat G t0 * (A'.reverse.map fun p => blockE W L p.2 * sgnMat G (!p.1)).prod := by
      rw [loopB_eq_cbProd, Matrix.conjTranspose_mul, ← hA', cbProd_conj, cb_sgn_conj]
    rw [hB, cb_regroup, loopB_eq_cbProd, ← hA]
    set Ec := blockE W L c
    set Sl := sgnMat G ℓ
    have e1 : (((W : ℂ) • Ec) * (cbProd G A * sgnMat G (σ i)) * ((W : ℂ) • Ec) *
        (cbProd G (cbSh t0 A'.reverse) * Sl)) =
        (W : ℂ) ^ 2 •
          (Ec * (cbProd G A * sgnMat G (σ i) * Ec * cbProd G (cbSh t0 A'.reverse)) * Sl) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      congr 1
      ring
    rw [e1, Matrix.trace_smul, Matrix.trace_mul_comm]
    simp only [hP, cbProd_cons, cbProd_append, cbF, smul_eq_mul, Matrix.mul_assoc]
    rfl
  · intro q
    refine Fin.addCases (fun i₀ => ?_) (fun j₀ => ?_) q
    · rw [Fin.append_left]
      obtain ⟨p, hp⟩ := hmem (σ i₀, a i₀) (by
        simp only [hP, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl (cbRead_mem a σ i i₀)))
      exact ⟨p, hp⟩
    · rw [Fin.append_right]
      obtain ⟨s', hs'⟩ := cbSh_mem A'.reverse t0 (σ' j₀, a' j₀)
        (List.mem_reverse.mpr (cbRead_mem a' σ' j j₀))
      obtain ⟨p, hp⟩ := hmem (s', a' j₀) (by
        simp only [hP, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr (Or.inr hs')))
      exact ⟨p, hp⟩

/-- The diameter grows when every label of a word occurs in a longer word. -/
private lemma cb_wordDiam_le {L n N : ℕ} (y : Fin n → Fin L) (w : Fin N → Fin L)
    (h : ∀ q, ∃ p, w p = y q) : wordDiam y ≤ wordDiam w := by
  unfold wordDiam
  refine Finset.sup_le fun q _ => ?_
  obtain ⟨p₁, h₁⟩ := h q.1
  obtain ⟨p₂, h₂⟩ := h q.2
  rw [← h₁, ← h₂]
  exact Finset.le_sup (f := fun p : Fin N × Fin N => cycDist (w p.1) (w p.2))
    (Finset.mem_univ (p₁, p₂))

/-- The bracket (5.9) [gc:eq:bracket] of two loops at one Hermitian matrix is a sum over one block
label `c` and `k k'` cut positions of loops of length `k + k' + 2` whose labels contain both
words; so `|Γ(ℒ_k(a), ℒ_{k'}(a'))| ≤ γ_g W k k' Lτ` when the two words together have diameter
`> d` and these loops are bounded by `τ` on words of diameter `> d`. -/
theorem coneBracket_far (g E : ℝ) (m : ℂ) (hm : 0 < m.im) {W L k k' : ℕ} {u : ℝ} (hu : u < 1)
    {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian) (d τ : ℝ) (hd : 0 ≤ d)
    (hτ0 : 0 ≤ τ)
    (hτ : ∀ (b : Fin (k + k' + 2) → Fin L) (s : Fin (k + k' + 2) → Bool), d < wordDiam b →
      ‖loopTr (resolventMat M (zChar g E m u)) b s‖ ≤ τ)
    (a : Fin k → Fin L) (σ : Fin k → Bool) (a' : Fin k' → Fin L) (σ' : Fin k' → Bool)
    (had : d < wordDiam (Fin.append a a')) :
    ‖blockGamma W L (gammaG g) (resLoop g E m a σ u) (resLoop g E m a' σ' u) M‖ ≤
      gammaG g * W * k * k' * L * τ := by
  have _ := hd
  have _ := hτ0
  rw [blockGamma_loopTr g E m hm hu hM a σ a' σ']
  set G := resolventMat M (zChar g E m u) with hG
  have hγ : 0 ≤ gammaG g := by unfold gammaG; positivity
  have hterm : ∀ (c : Fin L) (i : Fin k) (j : Fin k'), ‖(((W : ℂ) • blockE W L c) *
      loopB G a σ i * ((W : ℂ) • blockE W L c) * (loopB G a' σ' j)ᴴ).trace‖ ≤
        (W : ℝ) ^ 2 * τ := by
    intro c i j
    obtain ⟨w, s, hw, hmem⟩ := cb_bracket_term G a σ a' σ' i j c
    rw [hw, norm_mul, norm_pow, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left (hτ w s ?_) (by positivity)
    exact lt_of_lt_of_le had (by exact_mod_cast cb_wordDiam_le _ w hmem)
  have hsum : ‖∑ c : Fin L, ∑ i : Fin k, ∑ j : Fin k', (((W : ℂ) • blockE W L c) *
      loopB G a σ i * ((W : ℂ) • blockE W L c) * (loopB G a' σ' j)ᴴ).trace‖ ≤
      L * k * k' * ((W : ℝ) ^ 2 * τ) := by
    calc _ ≤ ∑ c : Fin L, ∑ i : Fin k, ∑ j : Fin k', ‖(((W : ℂ) • blockE W L c) *
          loopB G a σ i * ((W : ℂ) • blockE W L c) * (loopB G a' σ' j)ᴴ).trace‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ =>
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _))
      _ ≤ ∑ _c : Fin L, ∑ _i : Fin k, ∑ _j : Fin k', (W : ℝ) ^ 2 * τ :=
          Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun i _ =>
            Finset.sum_le_sum fun j _ => hterm c i j
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine (mul_le_mul_of_nonneg_left hsum (by positivity)).trans (le_of_eq ?_)
  by_cases hW : (W : ℝ) = 0
  · simp [hW]
  · field_simp

/-! ### The bracket tensor -/

/-- The two bounds of `𝒱(c, c') = Γ(ℒ(c), ℒ(c'))` from the loops of length `N = k + k' + 2`. -/
private lemma cb_V {g E : ℝ} {m : ℂ} (hm : 0 < m.im) {W L k k' N : ℕ} (hN : k + k' + 2 = N)
    {u : ℝ} (hu : u < 1) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    {Y d τ : ℝ} (hd : 0 ≤ d) (hτ0 : 0 ≤ τ)
    (hY : ∀ (b : Fin N → Fin L) (s : Fin N → Bool),
      ‖loopTr (resolventMat M (zChar g E m u)) b s‖ ≤ Y)
    (hτ : ∀ (b : Fin N → Fin L) (s : Fin N → Bool), d < wordDiam b →
      ‖loopTr (resolventMat M (zChar g E m u)) b s‖ ≤ τ)
    (a : Fin k → Fin L) (σ : Fin k → Bool) (a' : Fin k' → Fin L) (σ' : Fin k' → Bool) :
    ‖blockGamma W L (gammaG g) (resLoop g E m a σ u) (resLoop g E m a' σ' u) M‖ ≤
        gammaG g * W * k * k' * ((2 * d + 1) * Y + L * τ) ∧
      (d < wordDiam (Fin.append a a') →
        ‖blockGamma W L (gammaG g) (resLoop g E m a σ u) (resLoop g E m a' σ' u) M‖ ≤
          gammaG g * W * k * k' * L * τ) := by
  subst hN
  exact ⟨blockGamma_loopTr_tail_le g E m hm hu hM Y d τ hd hτ0 hY hτ a σ a' σ',
    fun h => coneBracket_far g E m hm hu hM d τ hd hτ0 hτ a σ a' σ' h⟩

/-- The scale facts shared by both brackets: `ρ > 0`, `ρℓ_u/ℓ_v ≤ 1 + ρ`, and
`H, (1 + ρ)L/ℓ_u, ρℓ_u/ℓ_v ≤ 𝔓 = H(1 + ρ)L/ℓ_u`. -/
private lemma cb_scales {ρ ℓu ℓv H : ℝ} {L : ℕ} (h1u : 1 ≤ ℓu) (huv : ℓu ≤ ℓv) (huL : ℓu ≤ L)
    (hH : 1 ≤ H) (hX : 1 ≤ ρ * ℓu / ℓv) :
    0 < ρ ∧ 1 ≤ (L : ℝ) / ℓu ∧ 0 ≤ ρ * ℓu / ℓv ∧
      ρ * ℓu / ℓv ≤ H * (1 + ρ) * (L / ℓu) ∧ H ≤ H * (1 + ρ) * (L / ℓu) ∧
      1 ≤ (1 + ρ) * (L / ℓu) ∧ (1 + ρ) * (L / ℓu) ≤ H * (1 + ρ) * (L / ℓu) ∧
      (L : ℝ) / ℓu ≤ H * (1 + ρ) * (L / ℓu) ∧ H * (L / ℓu) ≤ H * (1 + ρ) * (L / ℓu) := by
  have hℓu : 0 < ℓu := by linarith
  have hℓv : 0 < ℓv := by linarith
  have hρ : 0 < ρ := by
    by_contra h
    push Not at h
    have : ρ * ℓu / ℓv ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg h hℓu.le) hℓv.le
    linarith
  have hQ : 1 ≤ (L : ℝ) / ℓu := (one_le_div hℓu).mpr huL
  have hH0 : 0 ≤ H := by linarith
  have hXρ : ρ * ℓu / ℓv ≤ ρ := by
    rw [div_le_iff₀ hℓv]
    exact mul_le_mul_of_nonneg_left huv hρ.le
  have hR1 : 1 ≤ (1 + ρ) * (L / ℓu) := by nlinarith
  have hRΛ : (1 + ρ) * (L / ℓu) ≤ H * (1 + ρ) * (L / ℓu) := by
    rw [mul_assoc]; exact le_mul_of_one_le_left (by linarith) hH
  have hHΛ : H ≤ H * (1 + ρ) * (L / ℓu) := by
    rw [mul_assoc]; exact le_mul_of_one_le_right hH0 hR1
  have hQR : (L : ℝ) / ℓu ≤ (1 + ρ) * (L / ℓu) := le_mul_of_one_le_left (by linarith) (by linarith)
  refine ⟨hρ, hQ, by positivity, ?_, hHΛ, hR1, hRΛ, hQR.trans hRΛ, ?_⟩
  · have : ρ ≤ (1 + ρ) * (L / ℓu) := by nlinarith
    linarith
  · rw [mul_assoc H]
    exact mul_le_mul_of_nonneg_left hQR hH0

/-! ### Words of length `2k` -/

/-- A sum over words of length `m + m` is a double sum over their two halves. -/
private lemma cb_sum_append {L m : ℕ} (F : (Fin (m + m) → Fin L) → ℂ) :
    ∑ w, F w = ∑ b : Fin m → Fin L, ∑ b' : Fin m → Fin L, F (Fin.append b b') := by
  rw [← (Fin.appendEquiv m m).sum_comp, Fintype.sum_prod_type]
  rfl

/-- A double sum with product weights over two words of length `m` is a sum over words of length
`m + m` with product weights. -/
private lemma cb_double_sum {L m : ℕ} (c : Fin (m + m) → Fin L → ℂ)
    (A : (Fin m → Fin L) → (Fin m → Fin L) → ℂ) :
    ∑ b : Fin m → Fin L, ∑ b' : Fin m → Fin L, (∏ j, c (Fin.castAdd m j) (b j)) *
        (∏ j, c (Fin.natAdd m j) (b' j)) * A b b' =
      ∑ w : Fin (m + m) → Fin L, (∏ i, c i (w i)) *
        A (fun i => w (Fin.castAdd m i)) (fun i => w (Fin.natAdd m i)) := by
  rw [cb_sum_append]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right]

/-! ### Rows of words -/

private lemma cb_sum_cons {L k : ℕ} {M : Type*} [AddCommMonoid M]
    (f : (Fin (k + 1) → Fin L) → M) :
    ∑ b, f b = ∑ x : Fin L, ∑ c : Fin k → Fin L, f (Fin.cons x c) := by
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin L)).sum_comp, Fintype.sum_prod_type]
  rfl

/-- A row whose entries are at most `δ` is at most `L^n δ`. -/
private lemma cb_row_le {L n : ℕ} (F : (Fin (n + 1) → Fin L) → ℂ) (c : Fin L) (δ : ℝ)
    (hF : ∀ b, b 0 = c → ‖F b‖ ≤ δ) : ‖rowSum F c‖ ≤ (L : ℝ) ^ n * δ := by
  unfold rowSum
  calc ‖∑ b : Fin (n + 1) → Fin L, if b 0 = c then F b else 0‖
      ≤ ∑ b : Fin (n + 1) → Fin L, ‖if b 0 = c then F b else 0‖ := norm_sum_le _ _
    _ ≤ ∑ b : Fin (n + 1) → Fin L, (if b 0 = c then δ else 0) := by
        refine Finset.sum_le_sum fun b _ => ?_
        split_ifs with h
        · exact hF b h
        · simp
    _ = (L : ℝ) ^ n * δ := by
        rw [cb_sum_cons]
        simp only [Fin.cons_zero]
        rw [Finset.sum_eq_single c (fun x _ hx => by simp [hx]) (by simp)]
        simp [Finset.card_univ, Fintype.card_fin]

/-! ### Cyclic distance -/

private lemma cb_mod {L x y : ℕ} (hx : x < L) (hy : y < L) :
    (x + L - y) % L = if y ≤ x then x - y else x + L - y := by
  split_ifs with h
  · have : x + L - y = (x - y) + L := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

private lemma cb_cycDist_comm {L : ℕ} (a b : Fin L) : cycDist a b = cycDist b a := by
  unfold cycDist; exact min_comm _ _

private lemma cb_cycDist_tri {L : ℕ} (a b c : Fin L) :
    cycDist a c ≤ cycDist a b + cycDist b c := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  simp only [cycDist, cb_mod ha hb, cb_mod hb ha, cb_mod ha hc, cb_mod hc ha, cb_mod hb hc,
    cb_mod hc hb]
  split_ifs <;> omega

private lemma cb_cycDist_self {L : ℕ} (a : Fin L) : cycDist a a = 0 := by
  have ha := a.isLt
  simp only [cycDist, cb_mod ha ha]
  simp

private lemma cb_le_wordDiam {L k : ℕ} (y : Fin k → Fin L) (i j : Fin k) :
    (cycDist (y i) (y j) : ℝ) ≤ wordDiam y := by
  exact_mod_cast Finset.le_sup (f := fun p : Fin k × Fin k => cycDist (y p.1) (y p.2))
    (Finset.mem_univ (i, j))

/-- A word of diameter `> R ≥ 0` has, for every anchor `α`, a label farther than `R/2` from `α`. -/
private lemma cb_anchor {L N : ℕ} (w : Fin N → Fin L) (R : ℝ) (hR : 0 ≤ R)
    (h : R < wordDiam w) (α : Fin L) : ∃ p, R / 2 < cycDist (w p) α := by
  by_contra hc
  push Not at hc
  have hpair : ∀ p q, (cycDist (w p) (w q) : ℝ) ≤ R := by
    intro p q
    have h1 := cb_cycDist_tri (w p) α (w q)
    rw [cb_cycDist_comm α] at h1
    have : (cycDist (w p) (w q) : ℝ) ≤ cycDist (w p) α + cycDist (w q) α := by exact_mod_cast h1
    linarith [hc p, hc q]
  have h1 : wordDiam w ≤ ⌊R⌋₊ := Finset.sup_le fun q _ => Nat.le_floor (hpair q.1 q.2)
  have h2 : (wordDiam w : ℝ) ≤ R := (Nat.cast_le.mpr h1).trans (Nat.floor_le hR)
  linarith

/-- The far label of `cb_anchor` lies in one of the two halves of a joined word. -/
private lemma cb_anchor2 {L m : ℕ} (b b' : Fin m → Fin L) (R : ℝ) (hR : 0 ≤ R)
    (h : R < wordDiam (Fin.append b b')) (α : Fin L) :
    (∃ i, R / 2 < cycDist (b i) α) ∨ ∃ j, R / 2 < cycDist (b' j) α := by
  obtain ⟨p, hp⟩ := cb_anchor _ R hR h α
  refine Fin.addCases (fun i hp => ?_) (fun j hp => ?_) p hp
  · rw [Fin.append_left] at hp; exact Or.inl ⟨i, hp⟩
  · rw [Fin.append_right] at hp; exact Or.inr ⟨j, hp⟩

/-- A word none of whose labels is farther than `R ≥ 0` from its first label. -/
private lemma cb_near {L n : ℕ} (y : Fin (n + 1) → Fin L) (R : ℝ) (hR : 0 ≤ R)
    (h : ¬ ∃ j : Fin n, R < cycDist (y j.succ) (y 0)) (i : Fin (n + 1)) :
    (cycDist (y i) (y 0) : ℝ) ≤ R := by
  push Not at h
  refine Fin.cases ?_ (fun j => h j) i
  rw [cb_cycDist_self]; simpa using hR

/-! ### Rows and products of the projection -/

/-- The product `Π_{j ≥ 1} θ(a₀ - a_j)` of the projection. -/
private def cbPi {L n : ℕ} (θ : Fin L → ℝ) (x : Fin (n + 1) → Fin L) : ℂ :=
  ∏ j : Fin n, ((θ (x 0 - x j.succ) : ℝ) : ℂ)

private lemma cb_rowSum_sub {L n : ℕ} (F G : (Fin (n + 1) → Fin L) → ℂ) (z : ℂ) (x : Fin L) :
    rowSum (fun c => F c - G c * z) x = rowSum F x - rowSum G x * z := by
  unfold rowSum
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> ring

/-- `(𝒬 ⊗ 𝒬)𝒱` in four terms: the tensor, its two rows times a product of profiles, and its
double row times both products. -/
private lemma cb_projQ2 {L n : ℕ} (θ : Fin L → ℝ)
    (V : (Fin (n + 1) → Fin L) → (Fin (n + 1) → Fin L) → ℂ) (b b' : Fin (n + 1) → Fin L) :
    projQ θ (fun c => projQ θ (V c) b') b =
      V b b' - rowSum (V b) (b' 0) * cbPi θ b' - rowSum (fun c => V c b') (b 0) * cbPi θ b +
        rowSum (fun c => rowSum (V c) (b' 0)) (b 0) * cbPi θ b' * cbPi θ b := by
  have h := cb_rowSum_sub (fun c => V c b') (fun c => rowSum (V c) (b' 0)) (cbPi θ b') (b 0)
  calc projQ θ (fun c => projQ θ (V c) b') b
      = (V b b' - rowSum (V b) (b' 0) * cbPi θ b') -
          rowSum (fun c => V c b' - rowSum (V c) (b' 0) * cbPi θ b') (b 0) * cbPi θ b := rfl
    _ = (V b b' - rowSum (V b) (b' 0) * cbPi θ b') -
          (rowSum (fun c => V c b') (b 0) -
            rowSum (fun c => rowSum (V c) (b' 0)) (b 0) * cbPi θ b') * cbPi θ b := by rw [h]
    _ = _ := by ring

/-- The rows of a projected tensor vanish when the profile is normalized. -/
private lemma cb_rowSum_projQ {L n : ℕ} (θ : Fin L → ℝ) (hθ : ∑ x, θ x = 1)
    (F : (Fin (n + 1) → Fin L) → ℂ) (c : Fin L) : rowSum (projQ θ F) c = 0 := by
  have : NeZero L := ⟨by rintro rfl; exact c.elim0⟩
  have h1 : ∑ x, θ (c - x) = 1 := by
    rw [← hθ]
    exact Fintype.sum_equiv (Equiv.subLeft c) _ _ (fun x => rfl)
  have h2 : ∑ t : Fin n → Fin L, ∏ j : Fin n, ((θ (c - t j) : ℝ) : ℂ) = 1 := by
    rw [← Fintype.prod_sum (fun (_ : Fin n) (x : Fin L) => ((θ (c - x) : ℝ) : ℂ))]
    simp [← Complex.ofReal_sum, h1]
  have e : ∀ b : Fin (n + 1) → Fin L, (if b 0 = c then projQ θ F b else 0) =
      (if b 0 = c then F b else 0) -
        rowSum F c * (if b 0 = c then ∏ j : Fin n, ((θ (c - b j.succ) : ℝ) : ℂ) else 0) := by
    intro b
    split_ifs with h
    · simp only [projQ, h]
    · simp
  have h3 : ∑ b : Fin (n + 1) → Fin L,
      (if b 0 = c then ∏ j : Fin n, ((θ (c - b j.succ) : ℝ) : ℂ) else 0) = 1 := by
    rw [cb_sum_cons, Finset.sum_eq_single c (fun x _ hx => by simp [hx]) (by simp)]
    simpa using h2
  change (∑ b : Fin (n + 1) → Fin L, if b 0 = c then projQ θ F b else 0) = 0
  rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_sub_distrib, ← Finset.mul_sum, h3]
  change rowSum F c - rowSum F c * 1 = 0
  ring

/-- The zero row of `(𝒬 ⊗ 𝒬)𝒱` as a tensor of order `2(n + 1)`, in the first label. -/
private lemma cb_zeroRow {L n : ℕ} (θ : Fin L → ℝ) (hθ : ∑ x, θ x = 1)
    (G : (Fin (n + 1) → Fin L) → (Fin (n + 1) → Fin L) → ℂ) (h0 : 0 < n + 1 + (n + 1))
    (b₁ : Fin L) :
    ∑ w : Fin (n + 1 + (n + 1)) → Fin L, (if w ⟨0, h0⟩ = b₁ then
      projQ θ (G (fun i => w (Fin.natAdd (n + 1) i))) (fun i => w (Fin.castAdd (n + 1) i))
        else 0) = 0 := by
  rw [cb_sum_append, Finset.sum_comm]
  refine Finset.sum_eq_zero fun b' _ => ?_
  have e : ∀ b : Fin (n + 1) → Fin L, Fin.append b b' ⟨0, h0⟩ = b 0 := by
    intro b
    have : (⟨0, h0⟩ : Fin (n + 1 + (n + 1))) = Fin.castAdd (n + 1) 0 := rfl
    rw [this, Fin.append_left]
  simp only [e, Fin.append_left, Fin.append_right]
  exact cb_rowSum_projQ θ hθ (G b') b₁

private lemma cb_prod_le {n : ℕ} (f : Fin n → ℝ) (B : ℝ) (h0 : ∀ j, 0 ≤ f j)
    (hB : ∀ j, f j ≤ B) : ‖∏ j, ((f j : ℝ) : ℂ)‖ ≤ B ^ n := by
  rw [norm_prod]
  calc ∏ j, ‖((f j : ℝ) : ℂ)‖ = ∏ j, f j :=
        Finset.prod_congr rfl fun j _ => by rw [Complex.norm_real, Real.norm_of_nonneg (h0 j)]
    _ ≤ ∏ _j : Fin n, B := Finset.prod_le_prod₀ (fun j _ => h0 j) (fun j _ => hB j)
    _ = B ^ n := by simp

private lemma cb_prod_le_far {n : ℕ} (f : Fin n → ℝ) (B t : ℝ) (h0 : ∀ j, 0 ≤ f j)
    (hB : ∀ j, f j ≤ B) (j₀ : Fin n) (ht : f j₀ ≤ B * t) :
    ‖∏ j, ((f j : ℝ) : ℂ)‖ ≤ B ^ n * t := by
  have hn : ‖∏ j, ((f j : ℝ) : ℂ)‖ = ∏ j, f j := by
    rw [norm_prod]
    exact Finset.prod_congr rfl fun j _ => by rw [Complex.norm_real, Real.norm_of_nonneg (h0 j)]
  rw [hn, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j₀)]
  have h1 : ∏ j ∈ Finset.univ.erase j₀, f j ≤ B ^ (n - 1) := by
    calc ∏ j ∈ Finset.univ.erase j₀, f j ≤ ∏ _j ∈ Finset.univ.erase j₀, B :=
          Finset.prod_le_prod₀ (fun j _ => h0 j) (fun j _ => hB j)
      _ = B ^ (n - 1) := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin]
  have hn1 : n = (n - 1) + 1 := by have := j₀.isLt; omega
  calc f j₀ * ∏ j ∈ Finset.univ.erase j₀, f j ≤ (B * t) * B ^ (n - 1) :=
        mul_le_mul ht h1 (Finset.prod_nonneg fun j _ => h0 j) ((h0 j₀).trans ht)
    _ = B ^ n * t := by conv_rhs => rw [hn1]
                        ring

/-! ### The projected bracket tensor -/

/-- The row bound `R₁ = D^n X + L^n T` of a localized tensor. -/
private def cbR1 (n : ℕ) (L D XV TV : ℝ) : ℝ := D ^ n * XV + L ^ n * TV

/-- The bound `R₂ = D^n R₁ + L^{2n} T` of a double row. -/
private def cbR2 (n : ℕ) (L D XV TV : ℝ) : ℝ := D ^ n * cbR1 n L D XV TV + L ^ n * (L ^ n * TV)

/-- The sup bound of `(𝒬 ⊗ 𝒬)𝒱`, with `p` the bound of a product of profiles. -/
private def cbSA (n : ℕ) (L D p XV TV : ℝ) : ℝ :=
  XV + cbR1 n L D XV TV * p + cbR1 n L D XV TV * p + cbR2 n L D XV TV * p * p

/-- The tail bound of `(𝒬 ⊗ 𝒬)𝒱`. -/
private def cbτA (n : ℕ) (L D p τθ XV TV : ℝ) : ℝ :=
  TV + (cbR1 n L D XV TV * (p * τθ) + L ^ n * TV * p) +
    (cbR1 n L D XV TV * (p * τθ) + L ^ n * TV * p) +
    (cbR2 n L D XV TV * (p * p * τθ) + L ^ n * (L ^ n * TV) * (p * p))

private lemma cbτA_nonneg (n : ℕ) (L D p τθ XV TV : ℝ) (hL : 0 ≤ L) (hD : 0 ≤ D) (hp : 0 ≤ p)
    (hτθ : 0 ≤ τθ) (hXV : 0 ≤ XV) (hTV : 0 ≤ TV) : 0 ≤ cbτA n L D p τθ XV TV := by
  unfold cbτA cbR2 cbR1; positivity

private lemma cb_arith_core {u w e h q l XV TV : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ e * h) (hw0 : 0 ≤ w)
    (hw : w ≤ e * q) (he : 1 ≤ e) (hh : 1 ≤ h) (hq : 1 ≤ q) (hql : q ≤ l) (hhl : h ≤ l)
    (hhq : h * q ≤ l) (hXV : 0 ≤ XV) (hTV : 0 ≤ TV) :
    (1 + u) ^ 2 * XV + (2 * w + u * w + w ^ 2) * TV ≤
        4 * e ^ 2 * h ^ 2 * XV + 4 * e ^ 2 * l ^ 2 * TV ∧
      (1 + w) ^ 2 * TV ≤ 4 * e ^ 2 * l ^ 2 * TV := by
  have hl : 1 ≤ l := hh.trans hhl
  have he0 : 0 ≤ e := by linarith
  have hh0 : 0 ≤ h := by linarith
  have hq0 : 0 ≤ q := by linarith
  have heh : 1 ≤ e * h := one_le_mul_of_one_le_of_one_le he hh
  have h1 : (1 + u) ^ 2 ≤ 4 * e ^ 2 * h ^ 2 := by
    have a : 1 + u ≤ 2 * (e * h) := by linarith
    have b : (1 + u) ^ 2 ≤ (2 * (e * h)) ^ 2 := pow_le_pow_left₀ (by linarith) a 2
    nlinarith
  have hee : e ≤ e ^ 2 := by nlinarith
  have hll : l ≤ l ^ 2 := by nlinarith
  have hel : 1 ≤ e * l := one_le_mul_of_one_le_of_one_le he hl
  have hw1 : w ≤ e ^ 2 * l ^ 2 := by
    calc w ≤ e * q := hw
      _ ≤ e ^ 2 * l ^ 2 := mul_le_mul hee (hql.trans hll) hq0 (by positivity)
  have hw2 : u * w ≤ e ^ 2 * l ^ 2 := by
    calc u * w ≤ (e * h) * (e * q) := mul_le_mul hu hw hw0 (by positivity)
      _ = e ^ 2 * (h * q) := by ring
      _ ≤ e ^ 2 * l ^ 2 := mul_le_mul_of_nonneg_left (hhq.trans hll) (by positivity)
  have hw3 : w ^ 2 ≤ e ^ 2 * l ^ 2 := by
    calc w ^ 2 ≤ (e * q) ^ 2 := pow_le_pow_left₀ hw0 hw 2
      _ = e ^ 2 * q ^ 2 := by ring
      _ ≤ e ^ 2 * l ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0 hql 2) (by positivity)
  have h2 : 2 * w + u * w + w ^ 2 ≤ 4 * e ^ 2 * l ^ 2 := by linarith
  have h3 : (1 + w) ^ 2 ≤ 4 * e ^ 2 * l ^ 2 := by
    have a : 1 + w ≤ 2 * (e * l) := by
      have : w ≤ e * l := hw.trans (mul_le_mul_of_nonneg_left hql he0)
      linarith
    have b : (1 + w) ^ 2 ≤ (2 * (e * l)) ^ 2 := pow_le_pow_left₀ (by linarith) a 2
    nlinarith
  refine ⟨?_, mul_le_mul_of_nonneg_right h3 hTV⟩
  have := mul_le_mul_of_nonneg_right h1 hXV
  have := mul_le_mul_of_nonneg_right h2 hTV
  linarith

/-- The final arithmetic of the projected bracket: the restoration at order `2(n + 1)` applied to
the sup and tail bounds of `(𝒬 ⊗ 𝒬)𝒱`. -/
private lemma cb_arith_proj (n : ℕ) (Cθ Cn₀ H X Λ ℓ d Lr τθ B₁ B₂ S τA : ℝ) (hCθ : 1 ≤ Cθ)
    (hCn₀ : 0 ≤ Cn₀) (hH : 1 ≤ H) (hX0 : 0 ≤ X) (hXΛ : X ≤ Λ) (hHΛ : H ≤ Λ)
    (hQ : 1 ≤ Lr / ℓ) (hQΛ : Lr / ℓ ≤ Λ) (hHQ : H * (Lr / ℓ) ≤ Λ) (hℓ : 1 ≤ ℓ) (hd : 0 ≤ d)
    (hD : 2 * d + 1 ≤ H * ℓ) (hτθ0 : 0 ≤ τθ) (hτθ1 : τθ ≤ 1) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hS : S ≤ cbSA n Lr (2 * d + 1) ((Cθ / ℓ) ^ n) (((n : ℝ) + 1) ^ 2 * (H * B₁ + B₂))
      (((n : ℝ) + 1) ^ 2 * B₂))
    (hτA : τA = cbτA n Lr (2 * d + 1) ((Cθ / ℓ) ^ n) τθ (((n : ℝ) + 1) ^ 2 * (H * B₁ + B₂))
      (((n : ℝ) + 1) ^ 2 * B₂)) :
    Cn₀ * H ^ (n + 1 + (n + 1)) * X ^ (n + 1 + (n + 1)) * S +
        Cn₀ * Λ ^ (2 * (n + 1 + (n + 1))) * τA ≤
      20 * (((n : ℝ) + 1) ^ 2 * (Cθ ^ n) ^ 2) * Cn₀ *
          (H ^ (4 * (n + 1)) * X ^ (2 * (n + 1)) + Λ ^ (8 * (n + 1)) * τθ) * B₁ +
        20 * (((n : ℝ) + 1) ^ 2 * (Cθ ^ n) ^ 2) * Cn₀ * Λ ^ (8 * (n + 1)) * B₂ := by
  have hℓ0 : 0 < ℓ := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hΛ1 : 1 ≤ Λ := hH.trans hHΛ
  have hΛ0 : 0 ≤ Λ := by linarith
  have hCθ0 : 0 ≤ Cθ := by linarith
  have hQ0 : 0 ≤ Lr / ℓ := by linarith
  set XV := ((n : ℝ) + 1) ^ 2 * (H * B₁ + B₂) with hXV
  set TV := ((n : ℝ) + 1) ^ 2 * B₂ with hTV
  have hXV0 : 0 ≤ XV := by positivity
  have hTV0 : 0 ≤ TV := by positivity
  set u := (Cθ / ℓ) ^ n * (2 * d + 1) ^ n with hu
  set w := (Cθ / ℓ) ^ n * Lr ^ n with hw
  have hu0 : 0 ≤ u := by positivity
  have hue : u ≤ Cθ ^ n * H ^ n := by
    rw [hu, ← mul_pow, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ n
    rw [div_mul_eq_mul_div, div_le_iff₀ hℓ0, mul_assoc]
    exact mul_le_mul_of_nonneg_left hD hCθ0
  have hwe : w = Cθ ^ n * (Lr / ℓ) ^ n := by
    rw [hw, ← mul_pow, ← mul_pow]
    congr 1
    ring
  have hw0 : 0 ≤ w := by rw [hwe]; positivity
  obtain ⟨c1, c2⟩ := cb_arith_core (u := u) (w := w) (e := Cθ ^ n) (h := H ^ n)
    (q := (Lr / ℓ) ^ n) (l := Λ ^ n) hu0 hue hw0 hwe.le (one_le_pow₀ hCθ) (one_le_pow₀ hH)
    (one_le_pow₀ hQ) (pow_le_pow_left₀ hQ0 hQΛ n) (pow_le_pow_left₀ hH0 hHΛ n)
    (by rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hHQ n) hXV0 hTV0
  have eSA : cbSA n Lr (2 * d + 1) ((Cθ / ℓ) ^ n) XV TV =
      (1 + u) ^ 2 * XV + (2 * w + u * w + w ^ 2) * TV := by
    simp only [cbSA, cbR1, cbR2, hu, hw]
    ring
  have eτA : cbτA n Lr (2 * d + 1) ((Cθ / ℓ) ^ n) τθ XV TV =
      τθ * ((2 * u + u ^ 2) * XV + (2 * w + u * w + w ^ 2) * TV) + (1 + w) ^ 2 * TV := by
    simp only [cbτA, cbR1, cbR2, hu, hw]
    ring
  set Sb := 4 * (Cθ ^ n) ^ 2 * (H ^ n) ^ 2 * XV + 4 * (Cθ ^ n) ^ 2 * (Λ ^ n) ^ 2 * TV with hSb
  have hSb0 : 0 ≤ Sb := by positivity
  have hS' : S ≤ Sb := hS.trans (eSA ▸ c1)
  have hτA' : τA ≤ τθ * Sb + 4 * (Cθ ^ n) ^ 2 * (Λ ^ n) ^ 2 * TV := by
    rw [hτA, eτA]
    have a : (2 * u + u ^ 2) * XV ≤ (1 + u) ^ 2 * XV :=
      mul_le_mul_of_nonneg_right (by have : (1 + u) ^ 2 = 2 * u + u ^ 2 + 1 := by ring
                                     linarith) hXV0
    have b : τθ * ((2 * u + u ^ 2) * XV + (2 * w + u * w + w ^ 2) * TV) ≤ τθ * Sb :=
      mul_le_mul_of_nonneg_left (by linarith) hτθ0
    linarith
  rw [show n + 1 + (n + 1) = 2 * (n + 1) by ring]
  set N := 2 * (n + 1) with hN
  set K := ((n : ℝ) + 1) ^ 2 * (Cθ ^ n) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hX2 : 0 ≤ X ^ N := by positivity
  have hHN : 0 ≤ H ^ N := by positivity
  -- the monomials
  have pw : ∀ a b : ℕ, a ≤ b → Λ ^ a ≤ Λ ^ b := fun a b h => pow_le_pow_right₀ hΛ1 h
  have hHnΛ : H ^ n ≤ Λ ^ n := pow_le_pow_left₀ hH0 hHΛ n
  have hHNΛ : H ^ N ≤ Λ ^ N := pow_le_pow_left₀ hH0 hHΛ N
  have hXNΛ : X ^ N ≤ Λ ^ N := pow_le_pow_left₀ hX0 hXΛ N
  have M1 : H ^ N * (H ^ n) ^ 2 * H ≤ H ^ (4 * (n + 1)) := by
    rw [show H ^ N * (H ^ n) ^ 2 * H = H ^ (4 * n + 3) by rw [hN]; ring]
    exact pow_le_pow_right₀ hH (by omega)
  have hHXN : H ^ N * X ^ N ≤ Λ ^ N * Λ ^ N := mul_le_mul hHNΛ hXNΛ hX2 (by positivity)
  have M2 : H ^ N * X ^ N * (H ^ n) ^ 2 ≤ Λ ^ (8 * (n + 1)) := by
    calc H ^ N * X ^ N * (H ^ n) ^ 2 ≤ Λ ^ N * Λ ^ N * (Λ ^ n) ^ 2 :=
          mul_le_mul hHXN (pow_le_pow_left₀ (by positivity) hHnΛ 2) (by positivity)
            (by positivity)
      _ = Λ ^ (6 * n + 4) := by rw [hN]; ring
      _ ≤ _ := pw _ _ (by omega)
  have M3 : H ^ N * X ^ N * (Λ ^ n) ^ 2 ≤ Λ ^ (8 * (n + 1)) := by
    calc H ^ N * X ^ N * (Λ ^ n) ^ 2 ≤ Λ ^ N * Λ ^ N * (Λ ^ n) ^ 2 :=
          mul_le_mul_of_nonneg_right hHXN (by positivity)
      _ = Λ ^ (6 * n + 4) := by rw [hN]; ring
      _ ≤ _ := pw _ _ (by omega)
  have M4 : Λ ^ (2 * N) * ((H ^ n) ^ 2 * H) ≤ Λ ^ (8 * (n + 1)) := by
    calc Λ ^ (2 * N) * ((H ^ n) ^ 2 * H) ≤ Λ ^ (2 * N) * ((Λ ^ n) ^ 2 * Λ) := by gcongr
      _ = Λ ^ (6 * n + 5) := by rw [hN]; ring
      _ ≤ _ := pw _ _ (by omega)
  have M5 : Λ ^ (2 * N) * (H ^ n) ^ 2 ≤ Λ ^ (8 * (n + 1)) := by
    calc Λ ^ (2 * N) * (H ^ n) ^ 2 ≤ Λ ^ (2 * N) * (Λ ^ n) ^ 2 := by gcongr
      _ = Λ ^ (6 * n + 4) := by rw [hN]; ring
      _ ≤ _ := pw _ _ (by omega)
  have M6 : Λ ^ (2 * N) * (Λ ^ n) ^ 2 ≤ Λ ^ (8 * (n + 1)) := by
    calc Λ ^ (2 * N) * (Λ ^ n) ^ 2 = Λ ^ (6 * n + 4) := by rw [hN]; ring
      _ ≤ _ := pw _ _ (by omega)
  set Λ8 := Λ ^ (8 * (n + 1)) with hΛ8
  set H4 := H ^ (4 * (n + 1)) with hH4
  have step1 : Cn₀ * H ^ N * X ^ N * S + Cn₀ * Λ ^ (2 * N) * τA ≤
      Cn₀ * H ^ N * X ^ N * Sb +
        Cn₀ * Λ ^ (2 * N) * (τθ * Sb + 4 * (Cθ ^ n) ^ 2 * (Λ ^ n) ^ 2 * TV) := by
    gcongr
  have e2 : Cn₀ * H ^ N * X ^ N * Sb +
      Cn₀ * Λ ^ (2 * N) * (τθ * Sb + 4 * (Cθ ^ n) ^ 2 * (Λ ^ n) ^ 2 * TV) =
      4 * K * Cn₀ * ((H ^ N * (H ^ n) ^ 2 * H) * X ^ N * B₁ +
        (H ^ N * X ^ N * (H ^ n) ^ 2) * B₂ + (H ^ N * X ^ N * (Λ ^ n) ^ 2) * B₂ +
        τθ * ((Λ ^ (2 * N) * ((H ^ n) ^ 2 * H)) * B₁) + τθ * ((Λ ^ (2 * N) * (H ^ n) ^ 2) * B₂) +
        τθ * ((Λ ^ (2 * N) * (Λ ^ n) ^ 2) * B₂) + (Λ ^ (2 * N) * (Λ ^ n) ^ 2) * B₂) := by
    rw [hSb, hXV, hTV, hK]; ring
  have t1 : (H ^ N * (H ^ n) ^ 2 * H) * X ^ N * B₁ ≤ H4 * X ^ N * B₁ := by gcongr
  have t2 : (H ^ N * X ^ N * (H ^ n) ^ 2) * B₂ ≤ Λ8 * B₂ := by gcongr
  have t3 : (H ^ N * X ^ N * (Λ ^ n) ^ 2) * B₂ ≤ Λ8 * B₂ := by gcongr
  have t4 : τθ * ((Λ ^ (2 * N) * ((H ^ n) ^ 2 * H)) * B₁) ≤ τθ * (Λ8 * B₁) := by gcongr
  have t5 : τθ * ((Λ ^ (2 * N) * (H ^ n) ^ 2) * B₂) ≤ Λ8 * B₂ := by
    calc τθ * ((Λ ^ (2 * N) * (H ^ n) ^ 2) * B₂) ≤ 1 * (Λ8 * B₂) := by gcongr
      _ = Λ8 * B₂ := one_mul _
  have t6 : τθ * ((Λ ^ (2 * N) * (Λ ^ n) ^ 2) * B₂) ≤ Λ8 * B₂ := by
    calc τθ * ((Λ ^ (2 * N) * (Λ ^ n) ^ 2) * B₂) ≤ 1 * (Λ8 * B₂) := by gcongr
      _ = Λ8 * B₂ := one_mul _
  have t7 : (Λ ^ (2 * N) * (Λ ^ n) ^ 2) * B₂ ≤ Λ8 * B₂ := by gcongr
  have hsum : (H ^ N * (H ^ n) ^ 2 * H) * X ^ N * B₁ +
        (H ^ N * X ^ N * (H ^ n) ^ 2) * B₂ + (H ^ N * X ^ N * (Λ ^ n) ^ 2) * B₂ +
        τθ * ((Λ ^ (2 * N) * ((H ^ n) ^ 2 * H)) * B₁) + τθ * ((Λ ^ (2 * N) * (H ^ n) ^ 2) * B₂) +
        τθ * ((Λ ^ (2 * N) * (Λ ^ n) ^ 2) * B₂) + (Λ ^ (2 * N) * (Λ ^ n) ^ 2) * B₂ ≤
      H4 * X ^ N * B₁ + τθ * (Λ8 * B₁) + 5 * (Λ8 * B₂) := by linarith
  have hfin : 4 * K * Cn₀ * (H4 * X ^ N * B₁ + τθ * (Λ8 * B₁) + 5 * (Λ8 * B₂)) ≤
      20 * K * Cn₀ * (H4 * X ^ N + Λ8 * τθ) * B₁ + 20 * K * Cn₀ * Λ8 * B₂ := by
    have e3 : 20 * K * Cn₀ * (H4 * X ^ N + Λ8 * τθ) * B₁ + 20 * K * Cn₀ * Λ8 * B₂ -
        4 * K * Cn₀ * (H4 * X ^ N * B₁ + τθ * (Λ8 * B₁) + 5 * (Λ8 * B₂)) =
        16 * K * Cn₀ * (H4 * X ^ N * B₁ + τθ * (Λ8 * B₁)) := by ring
    have : 0 ≤ 16 * K * Cn₀ * (H4 * X ^ N * B₁ + τθ * (Λ8 * B₁)) := by positivity
    linarith
  calc Cn₀ * H ^ N * X ^ N * S + Cn₀ * Λ ^ (2 * N) * τA ≤ _ := step1
    _ = _ := e2
    _ ≤ 4 * K * Cn₀ * (H4 * X ^ N * B₁ + τθ * (Λ8 * B₁) + 5 * (Λ8 * B₂)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ _ := hfin

/-- Sup and tail bounds of `(𝒬 ⊗ 𝒬)𝒱` for a tensor `𝒱` at most `X_V`, and at most `T_V` on joined
words of diameter `> d`, and a profile at most `C_θ/ℓ`, and at most `C_θτ_θ/ℓ` at distance
`> Hℓ/4`: if the joined word has diameter `> Hℓ ≥ 4d + 2`, either a profile factor is far, or
the rows have an anchor at distance `> d` from a label of the other word. -/
private lemma cb_projTensor {L n : ℕ} (θ : Fin L → ℝ)
    (V : (Fin (n + 1) → Fin L) → (Fin (n + 1) → Fin L) → ℂ) (Cθ ℓ H d τθ XV TV : ℝ)
    (hd : 0 ≤ d) (hHd : 4 * d + 2 ≤ H * ℓ) (hτθ0 : 0 ≤ τθ) (hTV : 0 ≤ TV)
    (hθ0 : ∀ x y, 0 ≤ θ (x - y)) (hθB : ∀ x y, θ (x - y) ≤ Cθ / ℓ)
    (hθF : ∀ x y, H * ℓ / 4 < cycDist y x → θ (x - y) ≤ Cθ / ℓ * τθ)
    (hV : ∀ b b', ‖V b b'‖ ≤ XV)
    (hVτ : ∀ b b', d < wordDiam (Fin.append b b') → ‖V b b'‖ ≤ TV)
    (b b' : Fin (n + 1) → Fin L) :
    ‖projQ θ (fun c => projQ θ (V c) b') b‖ ≤ cbSA n L (2 * d + 1) ((Cθ / ℓ) ^ n) XV TV ∧
      (H * ℓ < wordDiam (Fin.append b b') →
        ‖projQ θ (fun c => projQ θ (V c) b') b‖ ≤
          cbτA n L (2 * d + 1) ((Cθ / ℓ) ^ n) τθ XV TV) := by
  set p := (Cθ / ℓ) ^ n with hp
  have hXV : 0 ≤ XV := (norm_nonneg _).trans (hV b b')
  have hHℓ : 0 < H * ℓ := by linarith
  have hPi : ∀ x : Fin (n + 1) → Fin L, ‖cbPi θ x‖ ≤ p := fun x =>
    cb_prod_le (fun j => θ (x 0 - x j.succ)) (Cθ / ℓ) (fun j => hθ0 _ _) (fun j => hθB _ _)
  have hPiF : ∀ x : Fin (n + 1) → Fin L, (∃ j : Fin n, H * ℓ / 4 < cycDist (x j.succ) (x 0)) →
      ‖cbPi θ x‖ ≤ p * τθ := fun x ⟨j, hj⟩ =>
    cb_prod_le_far (fun j => θ (x 0 - x j.succ)) (Cθ / ℓ) τθ (fun j => hθ0 _ _)
      (fun j => hθB _ _) j (hθF _ _ hj)
  have hp0 : 0 ≤ p := (norm_nonneg _).trans (hPi b)
  have hdl : ∀ c c' : Fin (n + 1) → Fin L, (wordDiam c : ℝ) ≤ wordDiam (Fin.append c c') :=
    fun c c' => by
      exact_mod_cast cb_wordDiam_le c (Fin.append c c')
        (fun q => ⟨Fin.castAdd _ q, Fin.append_left _ _ _⟩)
  have hdr : ∀ c c' : Fin (n + 1) → Fin L, (wordDiam c' : ℝ) ≤ wordDiam (Fin.append c c') :=
    fun c c' => by
      exact_mod_cast cb_wordDiam_le c' (Fin.append c c')
        (fun q => ⟨Fin.natAdd _ q, Fin.append_right _ _ _⟩)
  have hpair : ∀ (c c' : Fin (n + 1) → Fin L) (i j : Fin (n + 1)),
      (cycDist (c i) (c' j) : ℝ) ≤ wordDiam (Fin.append c c') := fun c c' i j => by
    have := cb_le_wordDiam (Fin.append c c') (Fin.castAdd _ i) (Fin.natAdd _ j)
    simpa only [Fin.append_left, Fin.append_right] using this
  have hpair' : ∀ (c c' : Fin (n + 1) → Fin L) (i j : Fin (n + 1)),
      (cycDist (c' j) (c i) : ℝ) ≤ wordDiam (Fin.append c c') := fun c c' i j => by
    rw [cb_cycDist_comm]; exact hpair c c' i j
  have hR1a : ∀ c c0', ‖rowSum (V c) c0'‖ ≤ cbR1 n L (2 * d + 1) XV TV := fun c c0' =>
    rowSum_le_of_tail (V c) d XV TV hd hTV (hV c)
      (fun c' hc' => hVτ c c' (lt_of_lt_of_le hc' (hdr c c'))) c0'
  have hR1b : ∀ c' c0, ‖rowSum (fun c => V c c') c0‖ ≤ cbR1 n L (2 * d + 1) XV TV :=
    fun c' c0 => rowSum_le_of_tail (fun c => V c c') d XV TV hd hTV (fun c => hV c c')
      (fun c hc => hVτ c c' (lt_of_lt_of_le hc (hdl c c'))) c0
  have hR2 : ∀ c0 c0', ‖rowSum (fun c => rowSum (V c) c0') c0‖ ≤ cbR2 n L (2 * d + 1) XV TV :=
    fun c0 c0' => rowSum_le_of_tail (fun c => rowSum (V c) c0') d _ ((L : ℝ) ^ n * TV) hd
      (by positivity) (fun c => hR1a c c0')
      (fun c hc => cb_row_le (V c) c0' TV
        (fun c' _ => hVτ c c' (lt_of_lt_of_le hc (hdl c c')))) c0
  have hF2 : ∀ c c0', (∃ i, d < cycDist (c i) c0') →
      ‖rowSum (V c) c0'‖ ≤ (L : ℝ) ^ n * TV := fun c c0' ⟨i, hi⟩ =>
    cb_row_le (V c) c0' TV fun c' hc' =>
      hVτ c c' (lt_of_lt_of_le (by rw [hc']; exact hi) (hpair c c' i 0))
  have hF1 : ∀ c' c0, (∃ j, d < cycDist (c' j) c0) →
      ‖rowSum (fun c => V c c') c0‖ ≤ (L : ℝ) ^ n * TV := fun c' c0 ⟨j, hj⟩ =>
    cb_row_le (fun c => V c c') c0 TV fun c hc =>
      hVτ c c' (lt_of_lt_of_le (by rw [hc]; exact hj) (hpair' c c' 0 j))
  have hF12 : ∀ c0 c0', d < cycDist c0 c0' →
      ‖rowSum (fun c => rowSum (V c) c0') c0‖ ≤ (L : ℝ) ^ n * ((L : ℝ) ^ n * TV) :=
    fun c0 c0' h => cb_row_le _ c0 _ fun c hc => cb_row_le (V c) c0' TV fun c' hc' =>
      hVτ c c' (lt_of_lt_of_le (by rw [hc, hc']; exact h) (hpair c c' 0 0))
  have hR1n : 0 ≤ cbR1 n L (2 * d + 1) XV TV := by unfold cbR1; positivity
  have hR2n : 0 ≤ cbR2 n L (2 * d + 1) XV TV := by unfold cbR2; positivity
  rw [cb_projQ2]
  set h₂ := rowSum (V b) (b' 0) with hh₂
  set h₁ := rowSum (fun c => V c b') (b 0) with hh₁
  set h₁₂ := rowSum (fun c => rowSum (V c) (b' 0)) (b 0) with hh₁₂
  set Pb := cbPi θ b with hPb
  set Pb' := cbPi θ b' with hPb'
  have hnorm : ‖V b b' - h₂ * Pb' - h₁ * Pb + h₁₂ * Pb' * Pb‖ ≤
      ‖V b b'‖ + ‖h₂‖ * ‖Pb'‖ + ‖h₁‖ * ‖Pb‖ + ‖h₁₂‖ * ‖Pb'‖ * ‖Pb‖ := by
    calc _ ≤ ‖V b b' - h₂ * Pb' - h₁ * Pb‖ + ‖h₁₂ * Pb' * Pb‖ := norm_add_le _ _
      _ ≤ ‖V b b' - h₂ * Pb'‖ + ‖h₁ * Pb‖ + ‖h₁₂ * Pb' * Pb‖ := by
          gcongr; exact norm_sub_le _ _
      _ ≤ ‖V b b'‖ + ‖h₂ * Pb'‖ + ‖h₁ * Pb‖ + ‖h₁₂ * Pb' * Pb‖ := by
          gcongr; exact norm_sub_le _ _
      _ = _ := by simp only [norm_mul]
  have hPbn := hPi b
  have hPbn' := hPi b'
  refine ⟨hnorm.trans ?_, fun hw => hnorm.trans ?_⟩
  · unfold cbSA
    have a1 := hV b b'
    have a2 : ‖h₂‖ * ‖Pb'‖ ≤ cbR1 n L (2 * d + 1) XV TV * p :=
      mul_le_mul (hR1a b (b' 0)) hPbn' (norm_nonneg _) hR1n
    have a3 : ‖h₁‖ * ‖Pb‖ ≤ cbR1 n L (2 * d + 1) XV TV * p :=
      mul_le_mul (hR1b b' (b 0)) hPbn (norm_nonneg _) hR1n
    have a4 : ‖h₁₂‖ * ‖Pb'‖ * ‖Pb‖ ≤ cbR2 n L (2 * d + 1) XV TV * p * p :=
      mul_le_mul (mul_le_mul (hR2 _ _) hPbn' (norm_nonneg _) hR2n) hPbn (norm_nonneg _)
        (by positivity)
    linarith
  · unfold cbτA
    have hdH : d < H * ℓ := by linarith
    have hd4 : d < H * ℓ / 4 := by linarith
    have a1 : ‖V b b'‖ ≤ TV := hVτ b b' (lt_trans hdH hw)
    have hT1 : 0 ≤ (L : ℝ) ^ n * TV * p := by positivity
    have hT1' : 0 ≤ cbR1 n L (2 * d + 1) XV TV * (p * τθ) := by positivity
    have a2 : ‖h₂‖ * ‖Pb'‖ ≤
        cbR1 n L (2 * d + 1) XV TV * (p * τθ) + (L : ℝ) ^ n * TV * p := by
      by_cases hfar : ∃ j : Fin n, H * ℓ / 4 < cycDist (b' j.succ) (b' 0)
      · have := mul_le_mul (hR1a b (b' 0)) (hPiF b' hfar) (norm_nonneg _) hR1n
        linarith
      · have hnear := cb_near b' (H * ℓ / 4) (by linarith) hfar
        rcases cb_anchor2 b b' (H * ℓ) hHℓ.le hw (b' 0) with ⟨i, hi⟩ | ⟨j, hj⟩
        · have := mul_le_mul (hF2 b (b' 0) ⟨i, by linarith⟩) hPbn' (norm_nonneg _)
            (by positivity)
          linarith
        · have := hnear j; linarith
    have a3 : ‖h₁‖ * ‖Pb‖ ≤
        cbR1 n L (2 * d + 1) XV TV * (p * τθ) + (L : ℝ) ^ n * TV * p := by
      by_cases hfar : ∃ j : Fin n, H * ℓ / 4 < cycDist (b j.succ) (b 0)
      · have := mul_le_mul (hR1b b' (b 0)) (hPiF b hfar) (norm_nonneg _) hR1n
        linarith
      · have hnear := cb_near b (H * ℓ / 4) (by linarith) hfar
        rcases cb_anchor2 b b' (H * ℓ) hHℓ.le hw (b 0) with ⟨i, hi⟩ | ⟨j, hj⟩
        · have := hnear i; linarith
        · have := mul_le_mul (hF1 b' (b 0) ⟨j, by linarith⟩) hPbn (norm_nonneg _)
            (by positivity)
          linarith
    have hT2 : 0 ≤ (L : ℝ) ^ n * ((L : ℝ) ^ n * TV) * (p * p) := by positivity
    have hT2' : 0 ≤ cbR2 n L (2 * d + 1) XV TV * (p * p * τθ) := by positivity
    have a4 : ‖h₁₂‖ * ‖Pb'‖ * ‖Pb‖ ≤ cbR2 n L (2 * d + 1) XV TV * (p * p * τθ) +
        (L : ℝ) ^ n * ((L : ℝ) ^ n * TV) * (p * p) := by
      by_cases hfar : ∃ j : Fin n, H * ℓ / 4 < cycDist (b j.succ) (b 0)
      · have := mul_le_mul (mul_le_mul (hR2 (b 0) (b' 0)) hPbn' (norm_nonneg _) hR2n)
          (hPiF b hfar) (norm_nonneg _) (by positivity)
        have e : cbR2 n L (2 * d + 1) XV TV * p * (p * τθ) =
            cbR2 n L (2 * d + 1) XV TV * (p * p * τθ) := by ring
        linarith
      · by_cases hfar' : ∃ j : Fin n, H * ℓ / 4 < cycDist (b' j.succ) (b' 0)
        · have := mul_le_mul (mul_le_mul (hR2 (b 0) (b' 0)) (hPiF b' hfar') (norm_nonneg _) hR2n)
            hPbn (norm_nonneg _) (by positivity)
          have e : cbR2 n L (2 * d + 1) XV TV * (p * τθ) * p =
              cbR2 n L (2 * d + 1) XV TV * (p * p * τθ) := by ring
          linarith
        · have hnear := cb_near b (H * ℓ / 4) (by linarith) hfar
          have hnear' := cb_near b' (H * ℓ / 4) (by linarith) hfar'
          rcases cb_anchor2 b b' (H * ℓ) hHℓ.le hw (b 0) with ⟨i, hi⟩ | ⟨j, hj⟩
          · have := hnear i; linarith
          · have htri := cb_cycDist_tri (b' j) (b' 0) (b 0)
            have htri' : (cycDist (b' j) (b 0) : ℝ) ≤
                cycDist (b' j) (b' 0) + cycDist (b' 0) (b 0) := by
              exact_mod_cast htri
            have hfar0 : d < (cycDist (b 0) (b' 0) : ℝ) := by
              rw [cb_cycDist_comm]; linarith [hnear' j]
            have := mul_le_mul (mul_le_mul (hF12 (b 0) (b' 0) hfar0) hPbn' (norm_nonneg _)
              (by positivity)) hPbn (norm_nonneg _) (by positivity)
            have e : (L : ℝ) ^ n * ((L : ℝ) ^ n * TV) * p * p =
                (L : ℝ) ^ n * ((L : ℝ) ^ n * TV) * (p * p) := by ring
            linarith
    linarith

/-- The bracket of the propagated projected field (C.35) [fo:eq:projected-error-equation] of a
word of length `n + 1` at time `r` and one Hermitian matrix: with `𝔓 = H(1 + ρ)L/ℓ_u`,
`|Γ| ≤ C_n(H^{4(n+1)}(ρℓ_u/ℓ_v)^{2(n+1)} + 𝔓^{8(n+1)}τ_θ)γ_g Wℓ_u Y₂ + C_n𝔓^{8(n+1)}γ_g W Lτ`
if the loops of length `2(n + 1) + 2` are bounded by `Y₂`, and by `τ` on words of diameter `> d`,
the kernel at `r` is at most `C_θ/((1 - r)ℓ_u)` and at most `τ_θ/((1 - r)ℓ_u)` at distance
`> Hℓ_u/4`, and `Ξ = (v - r)P(I - vP)⁻¹` has the profile bounds of the restoration with scales
`ℓ_u ≤ ℓ_v`. -/
theorem coneBracket_proj (n : ℕ) (hn : 1 ≤ n) (C₁ Cθ : ℝ) (hC₁ : 0 < C₁) (hCθ : 1 ≤ Cθ) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (g E : ℝ) (m : ℂ) (W L : ℕ), 1 ≤ W → 3 ≤ L →
      IsDysonRootV (hopB g) (gammaG g) L E m →
      ∀ (r v : ℝ) (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ), M.IsHermitian →
      ∀ (σ : Fin (n + 1) → Bool) (a : Fin (n + 1) → Fin L) (Y₂ ρ ℓu ℓv H d τ τθ : ℝ),
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
      (∀ (b : Fin (2 * (n + 1) + 2) → Fin L) (s : Fin (2 * (n + 1) + 2) → Bool),
        ‖loopTr (resolventMat M (zChar g E m r)) b s‖ ≤ Y₂) →
      (∀ (b : Fin (2 * (n + 1) + 2) → Fin L) (s : Fin (2 * (n + 1) + 2) → Bool), d < wordDiam b →
        ‖loopTr (resolventMat M (zChar g E m r)) b s‖ ≤ τ) →
      ‖blockGamma W L (gammaG g)
          (fun N => ∑ b, projCoef (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v r a b *
            (resLoop g E m b σ r N - primLoop g W L E m r b σ))
          (fun N => ∑ b, projCoef (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v r a b *
            (resLoop g E m b σ r N - primLoop g W L E m r b σ)) M‖ ≤
        Cn * (H ^ (4 * (n + 1)) * (ρ * ℓu / ℓv) ^ (2 * (n + 1)) +
            (H * (1 + ρ) * (L / ℓu)) ^ (8 * (n + 1)) * τθ) * (gammaG g * W * ℓu * Y₂) +
          Cn * (H * (1 + ρ) * (L / ℓu)) ^ (8 * (n + 1)) * (gammaG g * W * L * τ) := by
  have _ := hn
  obtain ⟨Cn₀, hCn₀, hR⟩ := restore_zeroRow (n + 1 + (n + 1)) (by omega) C₁ hC₁
  refine ⟨20 * (((n : ℝ) + 1) ^ 2 * (Cθ ^ n) ^ 2) * Cn₀, by positivity, ?_⟩
  intro g E m W L hW hL hroot r v M hM σ a Y₂ ρ ℓu ℓv H d τ τθ hr0 hrv hv1 hρ h1u huv huL hH hX
    hd hHd hτ0 hτθ0 hτθ1 hKr hKfar hΞent hΞinc hY hτ
  obtain ⟨hρ0, hQ1, hX0, hXΛ, hHΛ, -, -, hQΛ, hHQΛ⟩ := cb_scales (L := L) h1u huv huL hH hX
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  have hr1 : r < 1 := by linarith
  have hv0 : 0 ≤ v := hr0.trans hrv
  have hℓu : 0 < ℓu := by linarith
  have h1r : 0 < 1 - r := by linarith
  have h1v : 0 < 1 - v := by linarith
  have hCθ0 : 0 ≤ Cθ := by linarith
  have : Nonempty (Fin L) := ⟨⟨0, by omega⟩⟩
  set P := pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) with hPdef
  have hP0 : ∀ x y, 0 ≤ P x y := fun x y => by
    simp only [hPdef, pairP, Matrix.of_apply]; positivity
  have hProw : ∀ x, ∑ y, P x y = 1 := pairP_row_sum (hopB g) (gammaG g) hγ L (by omega) E m hroot
  obtain ⟨hKv0, hKvrow⟩ := mixedKer_nonneg_row P hP0 hProw v hv0 hv1
  have hWF := wardProfile_facts g L hL E m hroot
  have hθsum : ∑ x, wardProfile P r x = 1 := (hWF.2 r hr0 hr1).2
  have hθ0 : ∀ x, 0 ≤ wardProfile P r x := (hWF.2 r hr0 hr1).1
  have hθeq : ∀ x y, wardProfile P r (x - y) = (1 - r) * mixedKer P r y x :=
    fun x y => (hWF.1 r ⟨by linarith, hr1⟩ x y).2.1
  have hθB : ∀ x y, wardProfile P r (x - y) ≤ Cθ / ℓu := by
    intro x y
    rw [hθeq]
    calc (1 - r) * mixedKer P r y x ≤ (1 - r) * (Cθ / ((1 - r) * ℓu)) :=
          mul_le_mul_of_nonneg_left (hKr y x) h1r.le
      _ = Cθ / ℓu := by field_simp
  have hθF : ∀ x y, H * ℓu / 4 < cycDist y x → wardProfile P r (x - y) ≤ Cθ / ℓu * τθ := by
    intro x y hxy
    rw [hθeq]
    have h1 : τθ ≤ Cθ * τθ := le_mul_of_one_le_left hτθ0 hCθ
    calc (1 - r) * mixedKer P r y x ≤ (1 - r) * (τθ / ((1 - r) * ℓu)) :=
          mul_le_mul_of_nonneg_left (hKfar y x hxy) h1r.le
      _ = τθ / ℓu := by field_simp
      _ ≤ Cθ * τθ / ℓu := div_le_div_of_nonneg_right h1 hℓu.le
      _ = Cθ / ℓu * τθ := by ring
  have hY0 : 0 ≤ Y₂ := (norm_nonneg _).trans (hY (fun _ => ⟨0, by omega⟩) (fun _ => true))
  have hk2 : n + 1 + (n + 1) + 2 = 2 * (n + 1) + 2 := by ring
  set B₁ := gammaG g * W * ℓu * Y₂ with hB₁
  set B₂ := gammaG g * W * L * τ with hB₂
  have hB₁0 : 0 ≤ B₁ := by positivity
  have hB₂0 : 0 ≤ B₂ := by positivity
  have hV : ∀ b b' : Fin (n + 1) → Fin L, ‖blockGamma W L (gammaG g) (resLoop g E m b σ r)
      (resLoop g E m b' σ r) M‖ ≤ ((n : ℝ) + 1) ^ 2 * (H * B₁ + B₂) := by
    intro b b'
    refine ((cb_V hroot.1 hk2 hr1 hM hd hτ0 hY hτ b σ b' σ).1).trans ?_
    have h2d : 2 * d + 1 ≤ H * ℓu := by linarith
    push_cast
    calc gammaG g * W * (n + 1) * (n + 1) * ((2 * d + 1) * Y₂ + L * τ) =
          ((n : ℝ) + 1) ^ 2 * (gammaG g * W * ((2 * d + 1) * Y₂) + gammaG g * W * L * τ) := by
          ring
      _ ≤ ((n : ℝ) + 1) ^ 2 * (gammaG g * W * ((H * ℓu) * Y₂) + gammaG g * W * L * τ) := by
          gcongr
      _ = _ := by rw [hB₁, hB₂]; ring
  have hVτ : ∀ b b' : Fin (n + 1) → Fin L, d < wordDiam (Fin.append b b') →
      ‖blockGamma W L (gammaG g) (resLoop g E m b σ r) (resLoop g E m b' σ r) M‖ ≤
        ((n : ℝ) + 1) ^ 2 * B₂ := by
    intro b b' h
    refine ((cb_V hroot.1 hk2 hr1 hM hd hτ0 hY hτ b σ b' σ).2 h).trans (le_of_eq ?_)
    push_cast
    rw [hB₂]
    ring
  have hPT := fun b b' => cb_projTensor (wardProfile P r)
    (fun c c' => blockGamma W L (gammaG g) (resLoop g E m c σ r) (resLoop g E m c' σ r) M)
    Cθ ℓu H d τθ (((n : ℝ) + 1) ^ 2 * (H * B₁ + B₂)) (((n : ℝ) + 1) ^ 2 * B₂) hd hHd hτθ0
    (by positivity) (fun x y => hθ0 _) hθB hθF hV hVτ b b'
  rw [blockGamma_projField g E m hroot.1 P hr1 hM σ a]
  have hsum := cb_double_sum
    (fun i x => ((((1 + (v - r) • mixedKer P v) (Fin.append a a i) x : ℝ) : ℂ)))
    (fun b b' => projQ (wardProfile P r) (fun c => projQ (wardProfile P r) (fun c' =>
      blockGamma W L (gammaG g) (resLoop g E m c σ r) (resLoop g E m c' σ r) M) b') b)
  simp only [Fin.append_left, Fin.append_right] at hsum
  rw [hsum]
  have hΞ0 : ∀ x y, 0 ≤ ((v - r) • mixedKer P v) x y := fun x y => by
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact mul_nonneg (by linarith) (hKv0 x y)
  have hΞrow : ∀ x, ∑ y, ((v - r) • mixedKer P v) x y ≤ ρ := fun x => by
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, hKvrow x]
    have e : (v - r) * (1 - v)⁻¹ = (1 - r) / (1 - v) - 1 := by field_simp; ring
    rw [e]
    linarith
  have hΞent' : ∀ x y, ((v - r) • mixedKer P v) x y ≤ C₁ * ρ / ℓv := fun x y => by
    simpa only [Matrix.smul_apply, smul_eq_mul] using hΞent x y
  have hΞinc' : ∀ x y y', |((v - r) • mixedKer P v) x y - ((v - r) • mixedKer P v) x y'| ≤
      C₁ * ρ / ℓv * (((cycDist y y' : ℝ) + ℓu) / ℓv) := fun x y y' => by
    simpa only [Matrix.smul_apply, smul_eq_mul] using hΞinc x y y'
  have hτA0 : 0 ≤ cbτA n L (2 * d + 1) ((Cθ / ℓu) ^ n) τθ (((n : ℝ) + 1) ^ 2 * (H * B₁ + B₂))
      (((n : ℝ) + 1) ^ 2 * B₂) := by
    have hH0 : 0 ≤ H := by linarith
    have hXV0 : 0 ≤ ((n : ℝ) + 1) ^ 2 * (H * B₁ + B₂) := by positivity
    have hTV0 : 0 ≤ ((n : ℝ) + 1) ^ 2 * B₂ := by positivity
    have hp0 : 0 ≤ (Cθ / ℓu) ^ n := by positivity
    have hD0 : 0 ≤ 2 * d + 1 := by linarith
    exact cbτA_nonneg n _ _ _ _ _ _ (Nat.cast_nonneg L) hD0 hp0 hτθ0 hXV0 hTV0
  refine (hR L ((v - r) • mixedKer P v)
    (fun w => projQ (wardProfile P r) (fun c => projQ (wardProfile P r) (fun c' =>
      blockGamma W L (gammaG g) (resLoop g E m c σ r) (resLoop g E m c' σ r) M)
        (fun i => w (Fin.natAdd (n + 1) i))) (fun i => w (Fin.castAdd (n + 1) i)))
    ρ ℓu ℓv H _ hΞ0 hΞrow hΞent' hΞinc' h1u huv huL hH hX hτA0
    (fun w hw => (hPT _ _).2 (by rw [Fin.append_castAdd_natAdd]; exact hw))
    (fun b₁ => cb_zeroRow (wardProfile P r) hθsum
      (fun b' c => projQ (wardProfile P r) (fun c' =>
        blockGamma W L (gammaG g) (resLoop g E m c σ r) (resLoop g E m c' σ r) M) b')
      (by omega) b₁) (Fin.append a a)).trans ?_
  exact cb_arith_proj n Cθ Cn₀ H (ρ * ℓu / ℓv) (H * (1 + ρ) * (L / ℓu)) ℓu d L τθ B₁ B₂ _ _
    hCθ hCn₀.le hH hX0 hXΛ hHΛ hQ1 hQΛ hHQΛ h1u hd (by linarith) hτθ0 hτθ1 hB₁0 hB₂0
    (ciSup_le fun w => (hPT _ _).1) rfl

/-! ### Stable legs -/

/-- Moving along a block direction from `M`: the slice at `e • δ_{(c,κ)}` is `M + e T_{c,κ}`. -/
private theorem cb_slice_line {W L : ℕ}
    (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (c : Fin L) (κ : Fin W × Fin W) (e : ℝ) :
    blockSlice W L M (e • Pi.single (c, κ.1, κ.2) 1) = M + (e : ℂ) • blockBasis W L c κ := by
  unfold blockSlice
  congr 1
  rw [Finset.sum_eq_single c, Finset.sum_eq_single κ]
  · simp
  · intro κ' _ hκ'
    have : (c, κ'.1, κ'.2) ≠ (c, κ.1, κ.2) := by
      intro h; apply hκ'; simp only [Prod.mk.injEq, true_and] at h; exact Prod.ext h.1 h.2
    simp [this]
  · simp
  · intro c' _ hc'
    refine Finset.sum_eq_zero fun κ' _ => ?_
    have : (c', κ'.1, κ'.2) ≠ (c, κ.1, κ.2) := by
      intro h; apply hc'; simp only [Prod.mk.injEq] at h; exact h.1
    simp [this]
  · simp

/-- A resolvent loop at the characteristic is differentiable along every block direction. -/
private theorem cb_diff (g E : ℝ) (m : ℂ) (hm : 0 < m.im) {W L k : ℕ} {u : ℝ}
    (hu : u < 1) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    (a : Fin k → Fin L) (σ : Fin k → Bool) (c : Fin L) (κ : Fin W × Fin W) :
    DifferentiableAt ℝ
      (fun e : ℝ => resLoop g E m a σ u (M + (e : ℂ) • blockBasis W L c κ)) 0 := by
  have hC := heatClass_loopTr W L k M hM g E m hm a σ (a' := u - 1) (b' := (u + 1) / 2)
    (by linarith)
  have hu' : u ∈ Set.Ioo (u - 1) ((u + 1) / 2) := ⟨by linarith, by linarith⟩
  obtain ⟨DF, D2F, hD, -⟩ := hC.dx
  set w : Ω W L := Pi.single (c, κ.1, κ.2) 1 with hw
  have hφ : HasDerivAt (fun e : ℝ => e • w) w 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
  have hf : (fun e : ℝ => resLoop g E m a σ u (M + (e : ℂ) • blockBasis W L c κ)) =
      (fun x => loopTr (resolventMat (blockSlice W L M x) (zChar g E m u)) a σ) ∘
        (fun e : ℝ => e • w) := by
    funext e
    simp only [Function.comp, hw, cb_slice_line, resLoop]
  rw [hf]
  exact (hD u hu' ((0 : ℝ) • w)).differentiableAt.comp (0 : ℝ) hφ.differentiableAt

/-- Absolute rows of a product. -/
private lemma cb_row_mul {L : ℕ} (A B : Matrix (Fin L) (Fin L) ℂ) (x : Fin L) (CB : ℝ)
    (hB : ∀ z, ∑ y, ‖B z y‖ ≤ CB) : ∑ y, ‖(A * B) x y‖ ≤ (∑ z, ‖A x z‖) * CB := by
  calc ∑ y, ‖(A * B) x y‖ ≤ ∑ y, ∑ z, ‖A x z‖ * ‖B z y‖ := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [Matrix.mul_apply]
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp only [norm_mul]
    _ = ∑ z, ‖A x z‖ * ∑ y, ‖B z y‖ := by
        rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ ≤ ∑ z, ‖A x z‖ * CB :=
        Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hB z) (norm_nonneg _)
    _ = (∑ z, ‖A x z‖) * CB := by rw [Finset.sum_mul]

/-- The same-sign propagators `U^{σσ}_{r,v}` of (5.15) [fo:eq:propagators] have absolute rows at
most `(1 + C₁)C₁` when `γ Σ_b |M_{ab}|² ≤ C₁` and the rows of `(I - vQ)⁻¹` are at most `C₁`. -/
private lemma cb_row_same {L : ℕ} (β : ℝ) (hβ : 0 < β) (D : Matrix (Fin L) (Fin L) ℂ)
    (r v C₁ : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (hC₁ : 0 < C₁)
    (hD : ∀ x, β * ∑ y, ‖D x y‖ ^ 2 ≤ C₁)
    (hQ : ∀ x, ∑ y, ‖(1 - (v : ℂ) • pairQ β D)⁻¹ x y‖ ≤ C₁) (s : Bool) (x : Fin L) :
    ∑ y, ‖pairU β D r v s s x y‖ ≤ (1 + C₁) * C₁ := by
  have hA : ∑ z, ‖(1 - (r : ℂ) • pairQ β D) x z‖ ≤ 1 + C₁ := by
    calc ∑ z, ‖(1 - (r : ℂ) • pairQ β D) x z‖
        ≤ ∑ z, (‖(1 : Matrix (Fin L) (Fin L) ℂ) x z‖ + r * (β * ‖D x z‖ ^ 2)) := by
          refine Finset.sum_le_sum fun z _ => ?_
          rw [Matrix.sub_apply]
          refine (norm_sub_le _ _).trans (le_of_eq ?_)
          simp only [Matrix.smul_apply, pairQ, Matrix.of_apply, smul_eq_mul, norm_mul,
            Complex.norm_real, Real.norm_of_nonneg hr0, Real.norm_of_nonneg hβ.le, norm_pow]
      _ = 1 + r * (β * ∑ z, ‖D x z‖ ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          congr 1
          rw [Finset.sum_eq_single x (fun z _ hz => by simp [Matrix.one_apply_ne' hz])
            (by simp)]
          simp
      _ ≤ 1 + C₁ := by nlinarith [hD x]
  have hP : ∑ y, ‖propPP (pairQ β D) r v x y‖ ≤ (1 + C₁) * C₁ :=
    (cb_row_mul _ _ x C₁ hQ).trans (mul_le_mul_of_nonneg_right hA hC₁.le)
  unfold pairU
  cases s
  · simpa [Matrix.map_apply, norm_star] using hP
  · simpa using hP

/-- The mixed-sign propagators `U^{σσ'}_{r,v} = I + (v - r)P(I - vP)⁻¹`, `σ ≠ σ'`, of (5.15)
[fo:eq:propagators] differ from the identity by `(v - r)P(I - vP)⁻¹`. -/
private lemma cb_mixed {L : ℕ} (β : ℝ) (D : Matrix (Fin L) (Fin L) ℂ)
    (hP : ∀ a b, 0 ≤ pairP β D a b) (hrow : ∀ a, ∑ b, pairP β D a b = 1)
    (r v B : ℝ) (hr0 : 0 ≤ r) (hrv : r ≤ v) (hv1 : v < 1)
    (hB : ∀ x y, (v - r) * mixedKer (pairP β D) v x y ≤ B) (s s' : Bool) (hs : s ≠ s')
    (x y : Fin L) :
    ‖pairU β D r v s s' x y - (1 : Matrix (Fin L) (Fin L) ℂ) x y‖ ≤ B ∧
      ‖star (pairU β D r v s s' x y) - (1 : Matrix (Fin L) (Fin L) ℂ) x y‖ ≤ B := by
  have hv0 : 0 ≤ v := hr0.trans hrv
  have hK := (mixedKer_nonneg_row (pairP β D) hP hrow v hv0 hv1).1 x y
  have hU : pairU β D r v s s' x y = (((1 : Matrix (Fin L) (Fin L) ℝ) x y +
      (v - r) * mixedKer (pairP β D) v x y : ℝ) : ℂ) := by
    unfold pairU
    simp only [hs, ↓reduceIte]
    rw [(propPM_identities (pairP β D) hP hrow r r v hr0 le_rfl hrv hv1).1]
    simp [Matrix.map_apply]
  have h1 : (1 : Matrix (Fin L) (Fin L) ℂ) x y =
      (((1 : Matrix (Fin L) (Fin L) ℝ) x y : ℝ) : ℂ) := by
    by_cases h : x = y <;> simp [Matrix.one_apply, h]
  have hnn : 0 ≤ (v - r) * mixedKer (pairP β D) v x y := mul_nonneg (by linarith) hK
  have e : ‖pairU β D r v s s' x y - (1 : Matrix (Fin L) (Fin L) ℂ) x y‖ =
      (v - r) * mixedKer (pairP β D) v x y := by
    rw [hU, h1, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    ring
  refine ⟨by rw [e]; exact hB x y, ?_⟩
  have e2 : star (pairU β D r v s s' x y) = pairU β D r v s s' x y := by
    rw [hU, Complex.star_def, Complex.conj_ofReal]
  rw [e2, e]
  exact hB x y

/-- The final arithmetic of the bracket with a stable leg. -/
private lemma cb_arith_stable (k : ℕ) (hk : 1 ≤ k) (Cn₀ H X Λ R B₁ B₂ S : ℝ) (hCn₀ : 0 ≤ Cn₀)
    (hH : 1 ≤ H) (hX : 0 ≤ X) (hHΛ : H ≤ Λ) (hXΛ : X ≤ Λ) (hR0 : 0 ≤ R) (hRΛ : R ≤ Λ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hS : S ≤ (k : ℝ) ^ 2 * (H * B₁ + B₂)) :
    Cn₀ * H ^ (k + k - 1) * X ^ (k + k - 1) * S + Cn₀ * R ^ (k + k) * ((k : ℝ) ^ 2 * B₂) ≤
      2 * Cn₀ * (k : ℝ) ^ 2 * H ^ (2 * k) * X ^ (2 * k - 1) * B₁ +
        2 * Cn₀ * (k : ℝ) ^ 2 * Λ ^ (4 * k) * B₂ := by
  have hΛ1 : 1 ≤ Λ := hH.trans hHΛ
  have hH0 : 0 ≤ H := by linarith
  have ek : k + k - 1 = 2 * k - 1 := by omega
  have ek' : k + k = 2 * k := by omega
  rw [ek, ek']
  have e1 : H ^ (2 * k) = H ^ (2 * k - 1) * H := by
    rw [← pow_succ]; congr 1; omega
  have hHX : H ^ (2 * k - 1) * X ^ (2 * k - 1) ≤ Λ ^ (4 * k) := by
    calc H ^ (2 * k - 1) * X ^ (2 * k - 1) ≤ Λ ^ (2 * k - 1) * Λ ^ (2 * k - 1) :=
          mul_le_mul (pow_le_pow_left₀ hH0 hHΛ _) (pow_le_pow_left₀ hX hXΛ _) (by positivity)
            (by positivity)
      _ = Λ ^ (2 * k - 1 + (2 * k - 1)) := (pow_add _ _ _).symm
      _ ≤ Λ ^ (4 * k) := pow_le_pow_right₀ hΛ1 (by omega)
  have hRp : R ^ (2 * k) ≤ Λ ^ (4 * k) :=
    (pow_le_pow_left₀ hR0 hRΛ _).trans (pow_le_pow_right₀ hΛ1 (by omega))
  have hk2 : 0 ≤ (k : ℝ) ^ 2 := by positivity
  have hP : 0 ≤ Cn₀ * H ^ (2 * k - 1) * X ^ (2 * k - 1) := by positivity
  calc Cn₀ * H ^ (2 * k - 1) * X ^ (2 * k - 1) * S + Cn₀ * R ^ (2 * k) * ((k : ℝ) ^ 2 * B₂)
      ≤ Cn₀ * H ^ (2 * k - 1) * X ^ (2 * k - 1) * ((k : ℝ) ^ 2 * (H * B₁ + B₂)) +
          Cn₀ * R ^ (2 * k) * ((k : ℝ) ^ 2 * B₂) := by gcongr
    _ = Cn₀ * (k : ℝ) ^ 2 * (H ^ (2 * k - 1) * H) * X ^ (2 * k - 1) * B₁ +
          Cn₀ * (k : ℝ) ^ 2 * B₂ * (H ^ (2 * k - 1) * X ^ (2 * k - 1)) +
          Cn₀ * (k : ℝ) ^ 2 * B₂ * R ^ (2 * k) := by ring
    _ ≤ Cn₀ * (k : ℝ) ^ 2 * H ^ (2 * k) * X ^ (2 * k - 1) * B₁ +
          Cn₀ * (k : ℝ) ^ 2 * B₂ * Λ ^ (4 * k) + Cn₀ * (k : ℝ) ^ 2 * B₂ * Λ ^ (4 * k) := by
        rw [← e1]; gcongr
    _ ≤ _ := by
        have h0 : 0 ≤ Cn₀ * (k : ℝ) ^ 2 * H ^ (2 * k) * X ^ (2 * k - 1) * B₁ := by positivity
        have e2 : 2 * Cn₀ * (k : ℝ) ^ 2 * H ^ (2 * k) * X ^ (2 * k - 1) * B₁ +
            2 * Cn₀ * (k : ℝ) ^ 2 * Λ ^ (4 * k) * B₂ - (Cn₀ * (k : ℝ) ^ 2 * H ^ (2 * k) *
              X ^ (2 * k - 1) * B₁ + Cn₀ * (k : ℝ) ^ 2 * B₂ * Λ ^ (4 * k) +
              Cn₀ * (k : ℝ) ^ 2 * B₂ * Λ ^ (4 * k)) =
            Cn₀ * (k : ℝ) ^ 2 * H ^ (2 * k) * X ^ (2 * k - 1) * B₁ := by ring
        linarith

/-- The bracket of the propagated field of a word of length `k` with a stable leg at time `r` and
one Hermitian matrix: `|Γ| ≤ C_k H^{2k}(ρℓ_u/ℓ_v)^{2k-1}γ_g Wℓ_u Y₂ +
C_k(H(1 + ρ)L/ℓ_u)^{4k}γ_g W Lτ` if the loops of length `2k + 2` are bounded by `Y₂`, and by `τ`
on words of diameter `> d`, `(v - r)P(I - vP)⁻¹ ≤ C₁ρ/ℓ_v`, and `γ_g Σ_b |M_{ab}|² ≤ C₁` and the
rows of `(I - vQ)⁻¹` are at most `C₁` (the Dyson bounds (6.2) [fo:eq:propagation-dyson]). -/
theorem coneBracket_stable (k : ℕ) (hk : 2 ≤ k) (C₁ : ℝ) (hC₁ : 0 < C₁) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (g E : ℝ) (m : ℂ) (W L : ℕ), 1 ≤ W → 3 ≤ L →
      IsDysonRootV (hopB g) (gammaG g) L E m →
      ∀ (r v : ℝ) (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ), M.IsHermitian →
      ∀ (σ : Fin k → Bool), (∃ j, σ (finRotate k j) = σ j) →
      ∀ (a : Fin k → Fin L) (Y₂ ρ ℓu ℓv H d τ : ℝ),
      0 ≤ r → r ≤ v → v < 1 → (1 - r) / (1 - v) ≤ ρ →
      1 ≤ ℓu → ℓu ≤ ℓv → ℓu ≤ L → 1 ≤ H → 1 ≤ ρ * ℓu / ℓv → 0 ≤ d → 4 * d + 2 ≤ H * ℓu →
      0 ≤ τ →
      (∀ x y, (v - r) * mixedKer (pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)) v x y ≤
        C₁ * ρ / ℓv) →
      (∀ x, gammaG g * ∑ y, ‖dysonMat (hopB g) (gammaG g) L E m x y‖ ^ 2 ≤ C₁) →
      (∀ x, ∑ y, ‖(1 - (v : ℂ) • pairQ (gammaG g) (dysonMat (hopB g) (gammaG g) L E m))⁻¹ x y‖ ≤
        C₁) →
      (∀ (b : Fin (2 * k + 2) → Fin L) (s : Fin (2 * k + 2) → Bool),
        ‖loopTr (resolventMat M (zChar g E m r)) b s‖ ≤ Y₂) →
      (∀ (b : Fin (2 * k + 2) → Fin L) (s : Fin (2 * k + 2) → Bool), d < wordDiam b →
        ‖loopTr (resolventMat M (zChar g E m r)) b s‖ ≤ τ) →
      ‖blockGamma W L (gammaG g)
          (fun N => ∑ b : Fin k → Fin L, (∏ j, pairU (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)
            r v (σ j) (σ (finRotate k j)) (a j) (b j)) *
            (resLoop g E m b σ r N - primLoop g W L E m r b σ))
          (fun N => ∑ b : Fin k → Fin L, (∏ j, pairU (gammaG g) (dysonMat (hopB g) (gammaG g) L E m)
            r v (σ j) (σ (finRotate k j)) (a j) (b j)) *
            (resLoop g E m b σ r N - primLoop g W L E m r b σ)) M‖ ≤
        Cn * H ^ (2 * k) * (ρ * ℓu / ℓv) ^ (2 * k - 1) * (gammaG g * W * ℓu * Y₂) +
          Cn * (H * (1 + ρ) * (L / ℓu)) ^ (4 * k) * (gammaG g * W * L * τ) := by
  obtain ⟨Cn₀, hCn₀, hS⟩ := restore_stableLeg (k + k) (by omega) (C₁ + (1 + C₁) * C₁)
    (by positivity)
  refine ⟨2 * Cn₀ * (k : ℝ) ^ 2, by positivity, ?_⟩
  intro g E m W L hW hL hroot r v M hM σ hσ a Y₂ ρ ℓu ℓv H d τ hr0 hrv hv1 hρ h1u huv huL hH hX
    hd hHd hτ0 hΞ hMrow hQinv hY hτ
  obtain ⟨j₀, hj₀⟩ := hσ
  obtain ⟨hρ0, -, hX0, hXΛ, hHΛ, hR1, hRΛ, -, -⟩ := cb_scales (L := L) h1u huv huL hH hX
  have hγ : 0 < gammaG g := by unfold gammaG; positivity
  have hr1 : r < 1 := by linarith
  have hℓv : 0 < ℓv := by linarith
  have hP0 : ∀ x y, 0 ≤ pairP (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) x y := fun x y => by
    simp only [pairP, Matrix.of_apply]; positivity
  have hProw := pairP_row_sum (hopB g) (gammaG g) hγ L (by omega) E m hroot
  have hY0 : 0 ≤ Y₂ := (norm_nonneg _).trans (hY (fun _ => ⟨0, by omega⟩) (fun _ => true))
  have : Nonempty (Fin L) := ⟨⟨0, by omega⟩⟩
  set C₂ : ℝ := C₁ + (1 + C₁) * C₁ with hC₂
  have hC₁₂ : C₁ * ρ / ℓv ≤ C₂ * ρ / ℓv := by
    gcongr
    nlinarith
  set U₀ : Fin k → Matrix (Fin L) (Fin L) ℂ := fun j =>
    pairU (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) r v (σ j) (σ (finRotate k j)) with hU₀
  set V : (Fin k → Fin L) → (Fin k → Fin L) → ℂ := fun b b' =>
    blockGamma W L (gammaG g) (resLoop g E m b σ r) (resLoop g E m b' σ r) M with hV
  have hdiff : ∀ (b : Fin k → Fin L) (c : Fin L) (κ : Fin W × Fin W), DifferentiableAt ℝ
      (fun e : ℝ => (fun N => resLoop g E m b σ r N - primLoop g W L E m r b σ)
        (M + (e : ℂ) • blockBasis W L c κ)) 0 :=
    fun b c κ => (cb_diff g E m hroot.1 hr1 hM b σ c κ).sub_const _
  rw [blockGamma_tensor (gammaG g) _ _ _ _ M hdiff hdiff]
  have hG : ∀ b b', blockGamma W L (gammaG g)
      (fun N => resLoop g E m b σ r N - primLoop g W L E m r b σ)
      (fun N => resLoop g E m b' σ r N - primLoop g W L E m r b' σ) M = V b b' := by
    intro b b'
    simp only [hV, blockGamma, deriv_sub_const]
  simp only [hG, star_prod]
  have hsum := cb_double_sum
    (fun i x => Fin.append U₀ (fun j => (U₀ j).map star) i (Fin.append a a i) x) V
  simp only [Fin.append_left, Fin.append_right, Matrix.map_apply, hU₀] at hsum
  rw [hsum]
  have hleg : ∀ i, (∀ x, ∑ y, ‖Fin.append U₀ (fun j => (U₀ j).map star) i x y‖ ≤ C₂) ∨
      ∀ x y, ‖Fin.append U₀ (fun j => (U₀ j).map star) i x y -
        (1 : Matrix (Fin L) (Fin L) ℂ) x y‖ ≤ C₂ * ρ / ℓv := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left, hU₀]
      by_cases hs : σ j = σ (finRotate k j)
      · left
        intro x
        rw [← hs]
        refine (cb_row_same (gammaG g) hγ _ r v C₁ hr0 hr1 hC₁ hMrow hQinv (σ j) x).trans ?_
        linarith
      · right
        intro x y
        exact (cb_mixed (gammaG g) _ hP0 hProw r v _ hr0 hrv hv1 hΞ _ _ hs x y).1.trans hC₁₂
    · simp only [Fin.append_right, hU₀, Matrix.map_apply]
      by_cases hs : σ j = σ (finRotate k j)
      · left
        intro x
        rw [← hs]
        simp only [norm_star]
        refine (cb_row_same (gammaG g) hγ _ r v C₁ hr0 hr1 hC₁ hMrow hQinv (σ j) x).trans ?_
        linarith
      · right
        intro x y
        exact (cb_mixed (gammaG g) _ hP0 hProw r v _ hr0 hrv hv1 hΞ _ _ hs x y).2.trans hC₁₂
  have hi₀ : ∀ x, ∑ y, ‖Fin.append U₀ (fun j => (U₀ j).map star) (Fin.castAdd k j₀) x y‖ ≤ C₂ := by
    intro x
    simp only [Fin.append_left, hU₀]
    rw [hj₀]
    refine (cb_row_same (gammaG g) hγ _ r v C₁ hr0 hr1 hC₁ hMrow hQinv (σ j₀) x).trans ?_
    linarith
  have hk2 : k + k + 2 = 2 * k + 2 := by ring
  have htail : ∀ w : Fin (k + k) → Fin L, H * ℓu < wordDiam w →
      ‖V (fun i => w (Fin.castAdd k i)) (fun i => w (Fin.natAdd k i))‖ ≤
        (k : ℝ) ^ 2 * (gammaG g * W * L * τ) := by
    intro w hw
    have hdw : d < (wordDiam (Fin.append (fun i => w (Fin.castAdd k i))
        (fun i => w (Fin.natAdd k i))) : ℝ) := by
      rw [Fin.append_castAdd_natAdd]; linarith
    refine ((cb_V hroot.1 hk2 hr1 hM hd hτ0 hY hτ _ σ _ σ).2 hdw).trans (le_of_eq ?_)
    ring
  have hsup : (⨆ w : Fin (k + k) → Fin L,
      ‖V (fun i => w (Fin.castAdd k i)) (fun i => w (Fin.natAdd k i))‖) ≤
        (k : ℝ) ^ 2 * (H * (gammaG g * W * ℓu * Y₂) + gammaG g * W * L * τ) := by
    refine ciSup_le fun w => ((cb_V hroot.1 hk2 hr1 hM hd hτ0 hY hτ _ σ _ σ).1).trans ?_
    have h2d : 2 * d + 1 ≤ H * ℓu := by linarith
    calc gammaG g * W * k * k * ((2 * d + 1) * Y₂ + L * τ) =
          (k : ℝ) ^ 2 * (gammaG g * W * ((2 * d + 1) * Y₂) + gammaG g * W * L * τ) := by ring
      _ ≤ (k : ℝ) ^ 2 * (gammaG g * W * ((H * ℓu) * Y₂) + gammaG g * W * L * τ) := by gcongr
      _ = _ := by ring
  refine (hS L (Fin.append U₀ (fun j => (U₀ j).map star))
    (fun w => V (fun i => w (Fin.castAdd k i)) (fun i => w (Fin.natAdd k i)))
    ρ ℓu ℓv H ((k : ℝ) ^ 2 * (gammaG g * W * L * τ)) (Fin.castAdd k j₀) hleg hi₀ h1u huv huL hH
    hX (by positivity) htail (Fin.append a a)).trans ?_
  exact cb_arith_stable k (by omega) Cn₀ H _ _ _ _ _ _ hCn₀.le hH hX0 hHΛ hXΛ (by linarith) hRΛ
    (by positivity) (by positivity) hsup

end LSBA
