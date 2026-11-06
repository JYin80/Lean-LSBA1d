import LSBA.Gauss.HeatBlock
import LSBA.Flow.Realization
import LSBA.Loop.Cuts

/-!
# The loop hierarchy in generator form

The resolvent loops `ℒ_k(u)` of (5.5) [fo:eq:loops] at the characteristic `z_u`, the centered
insertion term `𝒲_k` of (5.7) [fo:eq:light], and the generator forms of (5.4) [fo:eq:ito], (5.8)
[fo:eq:hierarchy] and (5.9) [gc:eq:bracket], pointwise for every Hermitian matrix; the bound
`|ℒ_2(a,c;+,+)| ≤ (ℒ_2(a,c;+,−) ℒ_2(c,a;+,−))^{1/2}`.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- `m^+ = m`, `m^- = m̄`. -/
def sgnScalar (m : ℂ) (s : Bool) : ℂ := if s then m else star m

/-- The loop `ℒ_k(u; a, σ)` of (5.5) [fo:eq:loops] at the matrix `M`. -/
def resLoop (g E : ℝ) (m : ℂ) {W L k : ℕ} (a : Fin k → Fin L) (σ : Fin k → Bool) (u : ℝ)
    (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) : ℂ :=
  loopTr (resolventMat M (zChar g E m u)) a σ

/-- The centered insertion term `𝒲_k` of (5.7) [fo:eq:light]. -/
def lightW (g E : ℝ) (m : ℂ) {W L k : ℕ} (a : Fin k → Fin L) (σ : Fin k → Bool) (u : ℝ)
    (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) : ℂ :=
  ((gammaG g * W : ℝ) : ℂ) * ∑ i : Fin k, ∑ c : Fin L,
    (loopTr (resolventMat M (zChar g E m u)) ![c] ![σ i] - sgnScalar m (σ i)) *
      loopTr (resolventMat M (zChar g E m u)) (insLab a i c) (insSgn σ i)

/-! ### Products of words -/

section GeneratorWords

variable {A : Type*} [Monoid A]

/-- The ordered product `Y s · Y (s+1) ⋯ Y (s+l-1)`. -/
private def generatorRp (Y : ℕ → A) (s l : ℕ) : A := ((List.range' s l).map Y).prod

private theorem generatorRp_zero (Y : ℕ → A) (s : ℕ) : generatorRp Y s 0 = 1 := by
  simp [generatorRp]

private theorem generatorRp_succ (Y : ℕ → A) (s l : ℕ) :
    generatorRp Y s (l + 1) = Y s * generatorRp Y (s + 1) l := by
  simp [generatorRp, List.range'_succ]

private theorem generatorRp_add (Y : ℕ → A) (s a b : ℕ) :
    generatorRp Y s (a + b) = generatorRp Y s a * generatorRp Y (s + a) b := by
  induction a generalizing s with
  | zero => simp [generatorRp_zero]
  | succ a ih =>
    rw [Nat.add_right_comm a 1 b, generatorRp_succ, ih (s + 1), generatorRp_succ, mul_assoc,
      show s + 1 + a = s + (a + 1) by omega]

private theorem generatorRp_congr (Y Y' : ℕ → A) (s s' l : ℕ)
    (h : ∀ x < l, Y (s + x) = Y' (s' + x)) : generatorRp Y s l = generatorRp Y' s' l := by
  induction l generalizing s s' with
  | zero => simp [generatorRp_zero]
  | succ l ih =>
    rw [generatorRp_succ, generatorRp_succ, ih (s + 1) (s' + 1)]
    · congr 1
      simpa using h 0 (by omega)
    · intro x hx
      have := h (x + 1) (by omega)
      rwa [show s + (x + 1) = s + 1 + x by omega, show s' + (x + 1) = s' + 1 + x by omega]
        at this

private theorem generatorRp_split (Y : ℕ → A) (s l i : ℕ) (h1 : s ≤ i) (h2 : i < s + l) :
    generatorRp Y s l =
      generatorRp Y s (i - s) * Y i * generatorRp Y (i + 1) (s + l - i - 1) := by
  have hl : l = (i - s) + ((s + l - i - 1) + 1) := by omega
  conv_lhs => rw [hl]
  rw [generatorRp_add, generatorRp_succ, show s + (i - s) = i by omega, mul_assoc]

private theorem generatorRp_ofFn : ∀ {k : ℕ} (g : Fin k → A) (Y : ℕ → A) (s : ℕ),
    (∀ p : Fin k, g p = Y (s + p)) → (List.ofFn g).prod = generatorRp Y s k
  | 0, g, Y, s, _ => by simp [generatorRp_zero]
  | k + 1, g, Y, s, h => by
    rw [List.ofFn_succ, List.prod_cons, generatorRp_succ,
      generatorRp_ofFn (fun p : Fin k => g p.succ) Y (s + 1) (fun p => by
        rw [h p.succ, Fin.val_succ, Nat.add_right_comm, Nat.add_assoc])]
    simpa using congrArg (· * generatorRp Y (s + 1) k) (h 0)

/-- Extension of a word `Fin k → A` to `ℕ`, by `1` beyond the end. -/
private def generatorExt {k : ℕ} (F : Fin k → A) (x : ℕ) : A :=
  if h : x < k then F ⟨x, h⟩ else 1

private theorem generatorExt_fin {k : ℕ} (F : Fin k → A) (p : Fin k) :
    generatorExt F p = F p := by
  simp [generatorExt, p.2]

private theorem generator_prod_update {k : ℕ} (F : Fin k → A) (i : Fin k) (Z : A) :
    (List.ofFn (Function.update F i Z)).prod =
      generatorRp (generatorExt F) 0 i * Z * generatorRp (generatorExt F) (i + 1) (k - i - 1) := by
  rw [generatorRp_ofFn _ (generatorExt (Function.update F i Z)) 0
      (fun p => by rw [zero_add, generatorExt_fin]),
    generatorRp_split (generatorExt (Function.update F i Z)) 0 k i (Nat.zero_le _)
      (by have := i.2; omega)]
  have hi : generatorExt (Function.update F i Z) i = Z := by
    rw [generatorExt_fin, Function.update_self]
  rw [hi, Nat.sub_zero, zero_add]
  have hoff : ∀ x, x ≠ (i : ℕ) →
      generatorExt (Function.update F i Z) x = generatorExt F x := by
    intro x hxi
    by_cases hxk : x < k
    · simp only [generatorExt, hxk, dite_true]
      rw [Function.update_of_ne]
      intro hc; rw [Fin.ext_iff] at hc; exact hxi hc
    · simp [generatorExt, hxk]
  rw [generatorRp_congr (generatorExt (Function.update F i Z)) (generatorExt F) 0 0 i
      (fun x hx => hoff _ (by omega)),
    generatorRp_congr (generatorExt (Function.update F i Z)) (generatorExt F) (i + 1) (i + 1)
      (k - i - 1) (fun x hx => hoff _ (by omega))]

private theorem generator_prod_update₂ {k : ℕ} (F : Fin k → A) (i j : Fin k) (hij : i < j)
    (Zi Zj : A) :
    (List.ofFn (Function.update (Function.update F i Zi) j Zj)).prod =
      generatorRp (generatorExt F) 0 i * Zi * generatorRp (generatorExt F) (i + 1) (j - i - 1) *
        Zj * generatorRp (generatorExt F) (j + 1) (k - j - 1) := by
  have hij' : (i : ℕ) < j := hij
  have hjk := j.2
  set F' := Function.update (Function.update F i Zi) j Zj with hF'
  rw [generatorRp_ofFn _ (generatorExt F') 0 (fun p => by rw [zero_add, generatorExt_fin]),
    generatorRp_split (generatorExt F') 0 k i (Nat.zero_le _) (by omega),
    generatorRp_split (generatorExt F') (i + 1) (0 + k - i - 1) j (by omega) (by omega)]
  have hne : j ≠ i := ne_of_gt hij
  have h1 : generatorExt F' i = Zi := by
    rw [generatorExt_fin, hF', Function.update_of_ne (Ne.symm hne), Function.update_self]
  have h2 : generatorExt F' j = Zj := by
    rw [generatorExt_fin, hF', Function.update_self]
  rw [h1, h2, Nat.sub_zero, zero_add, show i + 1 + (k - i - 1) - j - 1 = k - j - 1 by omega,
    show (j : ℕ) - (i + 1) = j - i - 1 by omega]
  have hoff : ∀ x, x ≠ (i : ℕ) → x ≠ (j : ℕ) → generatorExt F' x = generatorExt F x := by
    intro x hxi hxj
    by_cases hxk : x < k
    · simp only [generatorExt, hxk, dite_true, hF']
      rw [Function.update_of_ne, Function.update_of_ne]
      · intro hc; rw [Fin.ext_iff] at hc; exact hxi hc
      · intro hc; rw [Fin.ext_iff] at hc; exact hxj hc
    · simp [generatorExt, hxk]
  have c1 := generatorRp_congr (generatorExt F') (generatorExt F) 0 0 i
    (fun x hx => hoff _ (by omega) (by omega))
  have c2 := generatorRp_congr (generatorExt F') (generatorExt F) (i + 1) (i + 1) (j - i - 1)
    (fun x hx => hoff _ (by omega) (by omega))
  have c3 := generatorRp_congr (generatorExt F') (generatorExt F) (j + 1) (j + 1) (k - j - 1)
    (fun x hx => hoff _ (by omega) (by omega))
  rw [c1, c2, c3]
  simp only [mul_assoc]

private theorem generatorRp_tail {k : ℕ} (F : Fin k → A) (i : Fin k) :
    generatorRp (generatorExt F) i (k - i) =
      F i * generatorRp (generatorExt F) (i + 1) (k - i - 1) := by
  rw [show k - (i : ℕ) = (k - i - 1) + 1 by have := i.2; omega, generatorRp_succ,
    generatorExt_fin, Nat.add_sub_cancel]

end GeneratorWords

section GeneratorLoopWords

variable {W L : ℕ}

/-- The factors `X^{σ_p} E_{a_p}` of a loop word. -/
private def generatorWord {k : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a : Fin k → Fin L) (σ : Fin k → Bool) (p : Fin k) :
    Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  sgnMat X (σ p) * blockE W L (a p)

private theorem generator_insertNth {α : Type*} {k : ℕ} (i : Fin k) (x : α) (f : Fin k → α)
    (p : Fin (k + 1)) :
    Fin.insertNth (α := fun _ => α) i.castSucc x f p =
      if h : (p : ℕ) < i then f ⟨p, by have := i.2; omega⟩
      else if (p : ℕ) = i then x else f ⟨p - 1, by have := p.2; omega⟩ := by
  rcases lt_trichotomy p i.castSucc with h | h | h
  · have h' : (p : ℕ) < i := h
    rw [Fin.insertNth_apply_below h]
    simp only [eq_rec_constant, h', ↓reduceDIte]
    rfl
  · subst h
    simp
  · have h' : (i : ℕ) < p := h
    rw [Fin.insertNth_apply_above h]
    simp only [eq_rec_constant, show ¬ ((p : ℕ) < i) by omega, show (p : ℕ) ≠ i by omega,
      ↓reduceDIte, ↓reduceIte]
    congr 1

private theorem generator_loopTr_ins {k : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a : Fin k → Fin L) (σ : Fin k → Bool) (i : Fin k) (c : Fin L) :
    loopTr X (insLab a i c) (insSgn σ i) =
      (generatorRp (generatorExt (generatorWord X a σ)) 0 i * (sgnMat X (σ i) * blockE W L c) *
        generatorRp (generatorExt (generatorWord X a σ)) i (k - i)).trace := by
  set Y := generatorExt (generatorWord X a σ) with hY
  set Z := sgnMat X (σ i) * blockE W L c with hZ
  let Y' : ℕ → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ := fun x =>
    if x < i then Y x else if x = i then Z else Y (x - 1)
  have hi := i.2
  unfold loopTr
  rw [generatorRp_ofFn _ Y' 0 (fun p => by
      have hp := p.2
      simp only [insLab, insSgn, generator_insertNth, zero_add, Y']
      by_cases h1 : (p : ℕ) < i
      · simp only [h1, ↓reduceDIte, ↓reduceIte, hY, generatorExt, show (p : ℕ) < k by omega]
        rfl
      · by_cases h2 : (p : ℕ) = i
        · simp only [h2, lt_self_iff_false, ↓reduceDIte, ↓reduceIte, hZ]
        · simp only [h1, h2, ↓reduceDIte, ↓reduceIte, hY, generatorExt,
            show (p : ℕ) - 1 < k by omega]
          rfl),
    generatorRp_split Y' 0 (k + 1) i (Nat.zero_le _) (by omega),
    Nat.sub_zero, show 0 + (k + 1) - i - 1 = k - i by omega,
    generatorRp_congr Y' Y 0 0 i (fun x hx => by simp [Y', show x < (i : ℕ) by omega]),
    generatorRp_congr Y' Y (i + 1) i (k - i) (fun x hx => by
      simp only [Y', show ¬ (i + 1 + x < (i : ℕ)) by omega, show i + 1 + x ≠ (i : ℕ) by omega,
        ↓reduceIte]
      congr 1; omega)]
  simp [Y']

private theorem generator_loopTr_cutR {k : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a : Fin k → Fin L) (σ : Fin k → Bool) (i j : Fin k) (hij : i < j) (c : Fin L) :
    loopTr X (cutRLab a i j c) (cutRSgn σ i j) =
      (generatorRp (generatorExt (generatorWord X a σ)) i (j - i) *
        (sgnMat X (σ j) * blockE W L c)).trace := by
  set Y := generatorExt (generatorWord X a σ) with hY
  set Z := sgnMat X (σ j) * blockE W L c with hZ
  let Y' : ℕ → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ := fun x =>
    if x < j - i then Y (i + x) else Z
  have hij' : (i : ℕ) < j := hij
  have hj := j.2
  unfold loopTr
  rw [generatorRp_ofFn _ Y' 0 (fun p => by
      have hp := p.2
      simp only [cutRLab, cutRSgn, zero_add, Y']
      by_cases h1 : (p : ℕ) < j - i
      · simp only [h1, ↓reduceDIte, ↓reduceIte, hY, generatorExt,
          show (i : ℕ) + p < k by omega]
        rfl
      · simp only [h1, ↓reduceDIte, ↓reduceIte, hZ]
        congr 3
        exact Fin.ext (by simp; omega)),
    generatorRp_add, generatorRp_succ, generatorRp_zero, mul_one,
    generatorRp_congr Y' Y 0 i (j - i) (fun x hx => by simp [Y', show x < (j : ℕ) - i by omega])]
  simp [Y']

private theorem generator_loopTr_cutL {k : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a : Fin k → Fin L) (σ : Fin k → Bool) (i j : Fin k) (hij : i < j) (c : Fin L) :
    loopTr X (cutLLab a i j c) (cutLSgn σ i j) =
      (generatorRp (generatorExt (generatorWord X a σ)) 0 i * (sgnMat X (σ i) * blockE W L c) *
        generatorRp (generatorExt (generatorWord X a σ)) j (k - j)).trace := by
  set Y := generatorExt (generatorWord X a σ) with hY
  set Z := sgnMat X (σ i) * blockE W L c with hZ
  let Y' : ℕ → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ := fun x =>
    if x < i then Y x else if x = i then Z else Y (x + j - i - 1)
  have hij' : (i : ℕ) < j := hij
  have hj := j.2
  unfold loopTr
  rw [generatorRp_ofFn _ Y' 0 (fun p => by
      have hp := p.2
      simp only [cutLLab, cutLSgn, zero_add, Y']
      by_cases h1 : (p : ℕ) < i
      · simp only [h1, ↓reduceDIte, ↓reduceIte, hY, generatorExt, show (p : ℕ) < k by omega,
          show (p : ℕ) ≤ i by omega]
        rfl
      · by_cases h2 : (p : ℕ) = i
        · simp only [h2, lt_self_iff_false, le_refl, ↓reduceDIte, ↓reduceIte, hZ, Fin.eta]
        · simp only [h1, h2, ↓reduceDIte, ↓reduceIte, hY, generatorExt,
            show ¬ ((p : ℕ) ≤ i) by omega, show (p : ℕ) + j - i - 1 < k by omega]
          rfl),
    generatorRp_split Y' 0 (k + i - j + 1) i (Nat.zero_le _) (by omega),
    Nat.sub_zero, show 0 + (k + i - j + 1) - i - 1 = k - j by omega,
    generatorRp_congr Y' Y 0 0 i (fun x hx => by simp [Y', show x < (i : ℕ) by omega]),
    generatorRp_congr Y' Y (i + 1) j (k - j) (fun x hx => by
      simp only [Y', show ¬ (i + 1 + x < (i : ℕ)) by omega, show i + 1 + x ≠ (i : ℕ) by omega,
        ↓reduceIte]
      congr 1; omega)]
  simp [Y']

end GeneratorLoopWords

/-! ### Calculus along lines and in time -/

section GeneratorCalculus

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Product rule for an ordered product of `k` matrix-valued functions. -/
private theorem generator_hasDerivAt_prod : ∀ {k : ℕ} (f f' : Fin k → ℝ → Matrix n n ℂ) (t : ℝ),
    (∀ p, HasDerivAt (f p) (f' p t) t) →
    HasDerivAt (fun s => (List.ofFn fun p => f p s).prod)
      (∑ i, (List.ofFn (Function.update (fun p => f p t) i (f' i t))).prod) t
  | 0, f, f', t, _ => by
    simpa using hasDerivAt_const t (1 : Matrix n n ℂ)
  | k + 1, f, f', t, hf => by
    have ih := generator_hasDerivAt_prod (fun p : Fin k => f p.succ) (fun p => f' p.succ) t
      (fun p => hf p.succ)
    have h := (hf 0).mul ih
    simp only [List.ofFn_succ, List.prod_cons]
    refine h.congr_deriv ?_
    rw [Fin.sum_univ_succ, Finset.mul_sum]
    refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun i _ => ?_)
    · simp
    · have hi : (0 : Fin (k + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
      simp only [Function.update_apply, hi, ↓reduceIte, Fin.succ_inj]
      congr 2
      exact congrArg List.ofFn (funext fun j => Function.update_apply _ _ _ _)

/-- The trace as a continuous real-linear functional. -/
private def generatorTrace (n : Type*) [Fintype n] [DecidableEq n] : Matrix n n ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap ((Matrix.traceLinearMap n ℂ ℂ).restrictScalars ℝ)

/-- The entry `(p, q)` as a continuous real-linear functional. -/
private def generatorEntry (p q : n) : Matrix n n ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M p q
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

private theorem generator_hasDerivAt_trace {P : ℝ → Matrix n n ℂ} {P' : Matrix n n ℂ} {t : ℝ}
    (h : HasDerivAt P P' t) : HasDerivAt (fun s => (P s).trace) P'.trace t :=
  (generatorTrace n).hasFDerivAt.comp_hasDerivAt t h

private theorem generator_hasDerivAt_entry {P : ℝ → Matrix n n ℂ} {P' : Matrix n n ℂ} {t : ℝ}
    (h : HasDerivAt P P' t) (p q : n) : HasDerivAt (fun s => P s p q) (P' p q) t :=
  (generatorEntry p q).hasFDerivAt.comp_hasDerivAt t h

/-- Second derivative of the trace of an ordered product: the terms with one factor
differentiated twice and the terms with two distinct factors differentiated once. -/
private theorem generator_iteratedDeriv_trace_prod {k : ℕ} (f f' f'' : Fin k → ℝ → Matrix n n ℂ)
    (t₀ : ℝ) (hf : ∀ p s, HasDerivAt (f p) (f' p s) s)
    (hf' : ∀ p, HasDerivAt (f' p) (f'' p t₀) t₀) :
    iteratedDeriv 2 (fun s => (List.ofFn fun p => f p s).prod.trace) t₀ =
      ∑ i, (List.ofFn (Function.update (fun p => f p t₀) i (f'' i t₀))).prod.trace +
        ∑ i, ∑ j, if j = i then 0 else
          (List.ofFn (Function.update (Function.update (fun p => f p t₀) i (f' i t₀)) j
            (f' j t₀))).prod.trace := by
  have h1 : deriv (fun s => (List.ofFn fun p => f p s).prod.trace) = fun s =>
      (∑ i, (List.ofFn fun p => Function.update f i (f' i) p s).prod).trace := by
    funext s
    refine (generator_hasDerivAt_trace
      (generator_hasDerivAt_prod f f' s fun p => hf p s)).deriv.trans ?_
    congr 2
    funext i
    congr 2
    funext p
    by_cases hp : p = i
    · subst hp; simp
    · simp [hp]
  have hg : ∀ i p, HasDerivAt (Function.update f i (f' i) p)
      (Function.update f' i (f'' i) p t₀) t₀ := by
    intro i p
    by_cases hp : p = i
    · subst hp; simpa using hf' p
    · simpa [hp] using hf p t₀
  have h2 := generator_hasDerivAt_trace (HasDerivAt.sum (u := Finset.univ) fun i _ =>
    generator_hasDerivAt_prod (Function.update f i (f' i)) (Function.update f' i (f'' i)) t₀
      (hg i))
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1]
  refine (h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)).deriv.trans ?_
  · simp
  · rw [Matrix.trace_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.trace_sum]
    have hsplit : ∀ j : Fin k,
        (List.ofFn (Function.update (fun p => Function.update f i (f' i) p t₀) j
          (Function.update f' i (f'' i) j t₀))).prod.trace =
        (if j = i then (List.ofFn (Function.update (fun p => f p t₀) i (f'' i t₀))).prod.trace
          else 0) +
        (if j = i then 0 else
          (List.ofFn (Function.update (Function.update (fun p => f p t₀) i (f' i t₀)) j
            (f' j t₀))).prod.trace) := by
      intro j
      by_cases hj : j = i
      · subst hj
        simp only [↓reduceIte, add_zero]
        congr 3
        funext p
        by_cases hp : p = j
        · subst hp; simp
        · simp [hp]
      · simp only [hj, ↓reduceIte, zero_add]
        congr 3
        funext p
        by_cases hp : p = j
        · subst hp; simp [hj]
        · by_cases hpi : p = i
          · subst hpi; simp [hp]
          · simp [hp, hpi]
    simp only [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- `d/dr (M - w(r))⁻¹ = w'(r) (M - w(r))⁻²` for Hermitian `M` and `Im w(r) ≠ 0`. -/
private theorem generator_hasDerivAt_resolvent_time {M : Matrix n n ℂ} (hM : M.IsHermitian)
    {w : ℝ → ℂ} {w' : ℂ} {u : ℝ} (hw : HasDerivAt w w' u) (hwu : (w u).im ≠ 0) :
    HasDerivAt (fun r => resolventMat M (w r))
      (w' • (resolventMat M (w u) * resolventMat M (w u))) u := by
  set U := (isUnit_sub_smul_one hM hwu).unit
  have hus : (U : Matrix n n ℂ) = M - w u • (1 : Matrix n n ℂ) := IsUnit.unit_spec _
  have hinv : ((U⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ) = resolventMat M (w u) := by
    rw [resolventMat, Matrix.nonsing_inv_eq_ringInverse, ← hus, Ring.inverse_unit]
  have hF : HasFDerivAt (Ring.inverse (M₀ := Matrix n n ℂ))
      (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) ↑U⁻¹) ↑U⁻¹)
      (M - w u • (1 : Matrix n n ℂ)) := by
    rw [← hus]; exact hasFDerivAt_ringInverse U
  have hP : HasDerivAt (fun r => M - w r • (1 : Matrix n n ℂ)) (-(w' • (1 : Matrix n n ℂ))) u :=
    ((hasDerivAt_const u M).sub (hw.smul_const (1 : Matrix n n ℂ))).congr_deriv (by simp)
  have hcomp := hF.comp_hasDerivAt u hP
  have e : (fun r => resolventMat M (w r)) =
      Ring.inverse ∘ (fun r => M - w r • (1 : Matrix n n ℂ)) := by
    funext r
    simp [resolventMat, Matrix.nonsing_inv_eq_ringInverse]
  rw [e]
  refine hcomp.congr_deriv ?_
  simp [ContinuousLinearMap.mulLeftRight_apply, hinv]

/-- Along `s ↦ M + sT`, `d/ds (-(G T G) B) = (G T G T G + G T G T G) B`. -/
private theorem generator_hasDerivAt_line₂ {M T : Matrix n n ℂ} (hM : M.IsHermitian)
    (hT : T.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (B : Matrix n n ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
        -(resolventMat (M + (s : ℂ) • T) z * T * resolventMat (M + (s : ℂ) • T) z) * B)
      ((resolventMat (M + (t : ℂ) • T) z * T * resolventMat (M + (t : ℂ) • T) z * T *
          resolventMat (M + (t : ℂ) • T) z +
        resolventMat (M + (t : ℂ) • T) z * T * resolventMat (M + (t : ℂ) • T) z * T *
          resolventMat (M + (t : ℂ) • T) z) * B) t := by
  have h := hasDerivAt_resolventMat_line hM hT hz t
  have h2 := ((h.mul_const T).mul h).neg.mul_const B
  refine h2.congr_deriv ?_
  noncomm_ring

end GeneratorCalculus

/-! ### Signs, the characteristic, and the block basis -/

section GeneratorBasis

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem generator_sgnMat_resolvent {M : Matrix n n ℂ} (hM : M.IsHermitian) (z : ℂ)
    (s : Bool) : sgnMat (resolventMat M z) s = resolventMat M (sgnScalar z s) := by
  cases s
  · simp only [sgnMat, sgnScalar, Bool.false_eq_true, ↓reduceIte, resolventMat]
    rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hM.eq]
  · simp [sgnMat, sgnScalar]

omit [Fintype n] [DecidableEq n] in
private theorem generator_isHermitian_line {M T : Matrix n n ℂ} (hM : M.IsHermitian)
    (hT : T.IsHermitian) (e : ℝ) : (M + (e : ℂ) • T).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hM.eq, hT.eq, Complex.star_def,
    Complex.conj_ofReal]

private theorem generator_sgnScalar_zChar (g E : ℝ) (m : ℂ) (r : ℝ) (s : Bool) :
    sgnScalar (zChar g E m r) s = zChar g E (sgnScalar m s) r := by
  cases s
  · simp [sgnScalar, zChar, Complex.conj_ofReal]
  · simp [sgnScalar]

private theorem generator_im_zChar_ne (g E : ℝ) (m : ℂ) (hm : 0 < m.im) {u : ℝ} (hu : u < 1)
    (s : Bool) : (zChar g E (sgnScalar m s) u).im ≠ 0 := by
  have h := etaChar_pos g m hm hu
  rw [im_zChar]
  cases s
  · have e : etaChar g (sgnScalar m false) u = -etaChar g m u := by
      simp [etaChar, sgnScalar]
    rw [e]
    exact neg_ne_zero.mpr h.ne'
  · simpa [sgnScalar] using h.ne'

private theorem generator_hasDerivAt_zChar (g E : ℝ) (m : ℂ) (r : ℝ) :
    HasDerivAt (zChar g E m) (-((gammaG g : ℝ) : ℂ) * m) r := by
  have h1 : HasDerivAt (fun t : ℝ => (1 - t) * gammaG g) (-gammaG g) r := by
    simpa using ((hasDerivAt_id r).const_sub 1).mul_const (gammaG g)
  have h2 := ((h1.ofReal_comp).mul_const m).const_add (E : ℂ)
  refine h2.congr_deriv ?_
  push_cast
  ring

variable {W L : ℕ}

private theorem generator_sum_blockBasis_mul (c : Fin L) (p q r s : Fin L × Fin W) :
    ∑ κ : Fin W × Fin W, blockBasis W L c κ p q * blockBasis W L c κ r s =
      if p = s ∧ q = r ∧ p.1 = c ∧ q.1 = c then 1 else 0 := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  obtain ⟨r1, r2⟩ := r
  obtain ⟨s1, s2⟩ := s
  simp only [blockBasis, Matrix.of_apply]
  by_cases hA : p1 = c ∧ q1 = c
  · by_cases hB : r1 = c ∧ s1 = c
    · obtain ⟨rfl, rfl⟩ := hA
      obtain ⟨rfl, rfl⟩ := hB
      simp [sum_hermBasis_apply_mul_apply, Prod.ext_iff]
    · simp only [hB, ↓reduceIte, mul_zero, Finset.sum_const_zero]
      refine (ite_eq_right_iff.mpr fun h => absurd ?_ hB).symm
      obtain ⟨h1, h2, -, -⟩ := h
      exact ⟨(congrArg Prod.fst h2).symm.trans hA.2, (congrArg Prod.fst h1).symm.trans hA.1⟩
  · simp only [hA, ↓reduceIte, zero_mul, Finset.sum_const_zero]
    simp

private theorem generator_P_apply (c : Fin L) (p q : Fin L × Fin W) :
    ((W : ℂ) • blockE W L c) p q = if p = q ∧ p.1 = c then 1 else 0 := by
  have hW : (W : ℂ) ≠ 0 := by exact_mod_cast (Fin.pos p.2).ne'
  simp only [Matrix.smul_apply, blockE, Matrix.diagonal_apply, smul_eq_mul]
  by_cases h : p = q <;> by_cases h' : p.1 = c <;> simp [h, h', hW]

private theorem generator_trace_mul_P (c : Fin L) (Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    (Y * ((W : ℂ) • blockE W L c)).trace = ∑ r, if r.1 = c then Y r r else 0 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, generator_P_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h : r.1 = c <;> simp [h, mul_ite, ite_and]

/-- `Σ_k T_{c,k} Y T_{c,k} = Tr(Y P_c) P_c` with `P_c = W E_c`. -/
private theorem generator_sum_basis_mul_mul (c : Fin L)
    (Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    ∑ κ, blockBasis W L c κ * Y * blockBasis W L c κ =
      (Y * ((W : ℂ) • blockE W L c)).trace • ((W : ℂ) • blockE W L c) := by
  ext p q
  have e : ∀ κ, (blockBasis W L c κ * Y * blockBasis W L c κ) p q =
      ∑ r, ∑ s, Y r s * (blockBasis W L c κ p r * blockBasis W L c κ s q) := by
    intro κ
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by ring
  rw [Matrix.sum_apply]
  simp only [e]
  rw [Finset.sum_comm]
  simp only [fun r => Finset.sum_comm (γ := Fin W × Fin W) (s := Finset.univ) (t := Finset.univ)
    (f := fun κ s => Y r s * (blockBasis W L c κ p r * blockBasis W L c κ s q)),
    ← Finset.mul_sum, generator_sum_blockBasis_mul]
  rw [Matrix.smul_apply, generator_P_apply, generator_trace_mul_P, smul_eq_mul]
  by_cases h : p = q ∧ p.1 = c
  · obtain ⟨rfl, hc⟩ := h
    simp [hc, ite_and, mul_ite]
  · rcases not_and_or.mp h with h | h <;> simp [h]

/-- `Σ_k Tr(T_{c,k} X) Tr(Y T_{c,k}) = Tr(P_c X P_c Y)` with `P_c = W E_c`. -/
private theorem generator_sum_trace_mul_trace (c : Fin L)
    (X Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    ∑ κ, (blockBasis W L c κ * X).trace * (Y * blockBasis W L c κ).trace =
      (((W : ℂ) • blockE W L c) * X * ((W : ℂ) • blockE W L c) * Y).trace := by
  have e : ∀ κ, (blockBasis W L c κ * X).trace * (Y * blockBasis W L c κ).trace =
      ∑ r, ∑ s, ∑ t, ∑ v, (blockBasis W L c κ t v * blockBasis W L c κ s r) *
        (X v t * Y r s) := by
    intro κ
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ =>
      Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun v _ => by ring
  simp only [e]
  have hswap : ∀ F : (Fin W × Fin W) → (Fin L × Fin W) → (Fin L × Fin W) → (Fin L × Fin W) →
      (Fin L × Fin W) → ℂ, ∑ κ, ∑ r, ∑ s, ∑ t, ∑ v, F κ r s t v =
        ∑ r, ∑ s, ∑ t, ∑ v, ∑ κ, F κ r s t v := by
    intro F
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_comm]
  rw [hswap]
  simp only [← Finset.sum_mul, generator_sum_blockBasis_mul]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, generator_P_apply]
  simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, Finset.sum_ite_irrel, Finset.sum_const_zero, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x.1 = c
  · simp only [hx, ↓reduceIte]
  · simp [hx]

private theorem generator_sum_P :
    ∑ c : Fin L, (W : ℂ) • blockE W L c = (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) := by
  ext p q
  rw [Matrix.sum_apply]
  simp only [generator_P_apply, Matrix.one_apply]
  by_cases h : p = q <;> simp [h]

private theorem generator_loopTr_one (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (c : Fin L)
    (s : Bool) : loopTr X ![c] ![s] = (sgnMat X s * blockE W L c).trace := by
  simp [loopTr]

/-- The coefficient identity `(γ/(2W)) · 2W² = γW`. -/
private theorem generator_coef (γ : ℝ) :
    ((γ / (2 * W) : ℝ) : ℂ) * (2 * ((W : ℂ) * (W : ℂ))) = ((γ * W : ℝ) : ℂ) := by
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW; simp
  · have : (W : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
    push_cast
    field_simp

end GeneratorBasis

/-- `ℒ_2(a, c; s, t) = Σ_{p,q} X^s_{pq} X^t_{qp} e_a(q) e_c(p)` with `e_a(q) = W⁻¹ 1(q ∈ a)`. -/
private theorem generator_loopTr_two_apply {W L : ℕ}
    (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a c : Fin L) (s t : Bool) :
    loopTr X ![a, c] ![s, t] = ∑ p, ∑ q, sgnMat X s p q * sgnMat X t q p *
      ((((if q.1 = a then (W : ℝ)⁻¹ else 0) * (if p.1 = c then (W : ℝ)⁻¹ else 0) : ℝ)) : ℂ) := by
  simp only [loopTr, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    blockE]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  by_cases ha : q.1 = a <;> by_cases hc : p.1 = c
  · simp [ha, hc, Matrix.diagonal_apply]
    ring
  all_goals simp [ha, hc, Matrix.diagonal_apply]

/-- (5.4) [fo:eq:ito] in generator form: `𝒢_u G = γ G diag(⟨G̃⟩_{cc}) G`, entrywise. -/
theorem blockGen_resolvent (g E : ℝ) (m : ℂ) (hm : 0 < m.im) {W L : ℕ} {u : ℝ} (hu : u < 1)
    {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian) (p q : Fin L × Fin W) :
    blockGen W L (gammaG g) (fun r N => resolventMat N (zChar g E m r) p q) u M =
      ((gammaG g * W : ℝ) : ℂ) * ∑ c : Fin L,
        (loopTr (resolventMat M (zChar g E m u)) ![c] ![true] - m) *
          (resolventMat M (zChar g E m u) * blockE W L c * resolventMat M (zChar g E m u)) p q := by
  unfold blockGen
  beta_reduce
  have hz : (zChar g E m u).im ≠ 0 := by
    simpa [sgnScalar] using generator_im_zChar_ne g E m hm hu true
  set z := zChar g E m u with hzdef
  set G := resolventMat M z with hG
  have htime : deriv (fun r => resolventMat M (zChar g E m r) p q) u =
      ((-((gammaG g : ℝ) : ℂ) * m) • (G * G)) p q :=
    (generator_hasDerivAt_entry (generator_hasDerivAt_resolvent_time hM
      (generator_hasDerivAt_zChar g E m u) hz) p q).deriv
  have hspace : ∀ c κ, iteratedDeriv 2 (fun e : ℝ =>
      resolventMat (M + (e : ℂ) • blockBasis W L c κ) z p q) 0 =
      (G * (blockBasis W L c κ * G * blockBasis W L c κ) * G +
        G * (blockBasis W L c κ * G * blockBasis W L c κ) * G) p q := by
    intro c κ
    have hT := blockBasis_isHermitian W L c κ
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have h1 : deriv (fun e : ℝ => resolventMat (M + (e : ℂ) • blockBasis W L c κ) z p q) =
        fun e : ℝ => (-(resolventMat (M + (e : ℂ) • blockBasis W L c κ) z * blockBasis W L c κ *
          resolventMat (M + (e : ℂ) • blockBasis W L c κ) z) * 1 :
            Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) p q := by
      funext e
      rw [mul_one]
      exact (generator_hasDerivAt_entry (hasDerivAt_resolventMat_line hM hT hz e) p q).deriv
    rw [h1, (generator_hasDerivAt_entry (generator_hasDerivAt_line₂ hM hT hz 1 0) p q).deriv]
    simp [hG, mul_assoc]
  have hsum : ∀ c, ∑ κ, (G * (blockBasis W L c κ * G * blockBasis W L c κ) * G +
      G * (blockBasis W L c κ * G * blockBasis W L c κ) * G) p q =
      2 * (((W : ℂ) * loopTr G ![c] ![true]) * ((W : ℂ) * (G * blockE W L c * G) p q)) := by
    intro c
    rw [← Matrix.sum_apply, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      generator_sum_basis_mul_mul, generator_loopTr_one]
    simp only [sgnMat, ↓reduceIte, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hGG : (G * G) p q = ∑ c : Fin L, (W : ℂ) * (G * blockE W L c * G) p q := by
    have e : G * G = G * (∑ c : Fin L, (W : ℂ) • blockE W L c) * G := by
      rw [generator_sum_P, mul_one]
    rw [e, Finset.mul_sum, Finset.sum_mul, Matrix.sum_apply]
    simp
  simp only [htime, hspace, hsum, Matrix.smul_apply, smul_eq_mul, hGG]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hc := generator_coef (W := W) (gammaG g)
  rw [generator_loopTr_one] at *
  simp only [sgnMat, ↓reduceIte]
  push_cast at hc ⊢
  linear_combination ((G * blockE W L c).trace * (G * blockE W L c * G) p q) * hc

section GeneratorHierarchy

open scoped Matrix.Norms.L2Operator

variable {W L : ℕ}

/-- `X X = Σ_c W X E_c X`. -/
private theorem generator_mul_self_eq (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    X * X = ∑ c : Fin L, (W : ℂ) • (X * blockE W L c * X) := by
  have e : X * X = X * (∑ c : Fin L, (W : ℂ) • blockE W L c) * X := by
    rw [generator_sum_P, mul_one]
  rw [e, Finset.mul_sum, Finset.sum_mul]
  simp

/-- The time derivative of a resolvent loop at the characteristic:
`∂_u ℒ_k = -γ W Σ_i m^{σ_i} Σ_c Cut_i^c`. -/
private theorem generator_deriv_loop_time (g E : ℝ) (m : ℂ) (hm : 0 < m.im) {k : ℕ} {u : ℝ}
    (hu : u < 1) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    (a : Fin k → Fin L) (σ : Fin k → Bool) :
    deriv (fun r => resLoop g E m a σ r M) u =
      ∑ i, ∑ c, (-((gammaG g : ℝ) : ℂ) * sgnScalar m (σ i) * (W : ℂ)) *
        loopTr (resolventMat M (zChar g E m u)) (insLab a i c) (insSgn σ i) := by
  set G := resolventMat M (zChar g E m u) with hG
  have hz := generator_im_zChar_ne g E m hm hu
  have hfun : (fun r => resLoop g E m a σ r M) = fun r : ℝ =>
      (List.ofFn fun p => resolventMat M (zChar g E (sgnScalar m (σ p)) r) *
        blockE W L (a p)).prod.trace := by
    funext r
    unfold resLoop loopTr
    congr 3
    funext p
    rw [generator_sgnMat_resolvent hM, generator_sgnScalar_zChar]
  rw [hfun]
  have hd := generator_hasDerivAt_trace (generator_hasDerivAt_prod
    (fun p r => resolventMat M (zChar g E (sgnScalar m (σ p)) r) * blockE W L (a p))
    (fun p r => ((-((gammaG g : ℝ) : ℂ) * sgnScalar m (σ p)) •
      (resolventMat M (zChar g E (sgnScalar m (σ p)) r) *
        resolventMat M (zChar g E (sgnScalar m (σ p)) r))) * blockE W L (a p)) u
    (fun p => by
      have h := (generator_hasDerivAt_resolvent_time hM
        (generator_hasDerivAt_zChar g E (sgnScalar m (σ p)) u) (hz (σ p))).mul_const
          (blockE W L (a p))
      exact h))
  rw [hd.deriv]
  have h0 : ∀ s : Bool, resolventMat M (zChar g E (sgnScalar m s) u) = sgnMat G s := by
    intro s
    rw [← generator_sgnScalar_zChar, ← generator_sgnMat_resolvent hM]
  simp only [h0]
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (fun p => sgnMat G (σ p) * blockE W L (a p)) = generatorWord G a σ from rfl,
    generator_prod_update, generator_mul_self_eq]
  simp only [generator_loopTr_ins, generatorRp_tail, generatorWord, Finset.smul_sum,
    Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, smul_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [mul_assoc]

/-- The second derivative of a resolvent loop along a Hermitian direction `T` at `0`. -/
private theorem generator_iteratedDeriv_loop_line (g E : ℝ) (m : ℂ) (hm : 0 < m.im) {k : ℕ}
    {u : ℝ} (hu : u < 1) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    (a : Fin k → Fin L) (σ : Fin k → Bool) {T : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hT : T.IsHermitian) (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hG : resolventMat M (zChar g E m u) = G) :
    iteratedDeriv 2 (fun e : ℝ => resLoop g E m a σ u (M + (e : ℂ) • T)) 0 =
      ∑ i, (List.ofFn (Function.update (generatorWord G a σ) i
        ((sgnMat G (σ i) * T * sgnMat G (σ i) * T * sgnMat G (σ i) +
          sgnMat G (σ i) * T * sgnMat G (σ i) * T * sgnMat G (σ i)) *
            blockE W L (a i)))).prod.trace +
      ∑ i, ∑ j, if j = i then 0 else
        (List.ofFn (Function.update (Function.update (generatorWord G a σ) i
          (-(sgnMat G (σ i) * T * sgnMat G (σ i)) * blockE W L (a i))) j
          (-(sgnMat G (σ j) * T * sgnMat G (σ j)) * blockE W L (a j)))).prod.trace := by
  have hz := generator_im_zChar_ne g E m hm hu
  have hfun : (fun e : ℝ => resLoop g E m a σ u (M + (e : ℂ) • T)) = fun e : ℝ =>
      (List.ofFn fun p => resolventMat (M + (e : ℂ) • T) (zChar g E (sgnScalar m (σ p)) u) *
        blockE W L (a p)).prod.trace := by
    funext e
    unfold resLoop loopTr
    congr 3
    funext p
    rw [generator_sgnMat_resolvent (generator_isHermitian_line hM hT e),
      generator_sgnScalar_zChar]
  rw [hfun]
  have h := generator_iteratedDeriv_trace_prod
    (fun p e => resolventMat (M + (e : ℂ) • T) (zChar g E (sgnScalar m (σ p)) u) *
      blockE W L (a p))
    (fun p e => -(resolventMat (M + (e : ℂ) • T) (zChar g E (sgnScalar m (σ p)) u) * T *
      resolventMat (M + (e : ℂ) • T) (zChar g E (sgnScalar m (σ p)) u)) * blockE W L (a p))
    (fun p e => (resolventMat (M + (e : ℂ) • T) (zChar g E (sgnScalar m (σ p)) u) * T *
      resolventMat (M + (e : ℂ) • T) (zChar g E (sgnScalar m (σ p)) u) * T *
      resolventMat (M + (e : ℂ) • T) (zChar g E (sgnScalar m (σ p)) u) +
      resolventMat (M + (e : ℂ) • T) (zChar g E (sgnScalar m (σ p)) u) * T *
      resolventMat (M + (e : ℂ) • T) (zChar g E (sgnScalar m (σ p)) u) * T *
      resolventMat (M + (e : ℂ) • T) (zChar g E (sgnScalar m (σ p)) u)) * blockE W L (a p)) 0
    (fun p e => by
      have h := (hasDerivAt_resolventMat_line hM hT (hz (σ p)) e).mul_const (blockE W L (a p))
      exact h)
    (fun p => generator_hasDerivAt_line₂ hM hT (hz (σ p)) _ 0)
  beta_reduce at h
  rw [h]
  have h0 : ∀ s : Bool, resolventMat (M + ((0 : ℝ) : ℂ) • T) (zChar g E (sgnScalar m s) u) =
      sgnMat G s := by
    intro s
    rw [Complex.ofReal_zero, zero_smul, add_zero, ← generator_sgnScalar_zChar,
      ← generator_sgnMat_resolvent hM, hG]
  simp only [h0]
  rfl

private theorem generatorRp_head {A : Type*} [Monoid A] {k : ℕ} (F : Fin k → A) (i j : Fin k)
    (hij : i < j) :
    generatorRp (generatorExt F) i (j - i) =
      F i * generatorRp (generatorExt F) (i + 1) (j - i - 1) := by
  have hij' : (i : ℕ) < j := hij
  rw [show (j : ℕ) - i = (j - i - 1) + 1 by omega, generatorRp_succ, generatorExt_fin,
    Nat.add_sub_cancel]

/-- The terms with one factor differentiated twice, summed over the block basis of block `c`. -/
private theorem generator_sum_self (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) {k : ℕ}
    (a : Fin k → Fin L) (σ : Fin k → Bool) (i : Fin k) (c : Fin L) :
    ∑ κ, (List.ofFn (Function.update (generatorWord G a σ) i
        ((sgnMat G (σ i) * blockBasis W L c κ * sgnMat G (σ i) * blockBasis W L c κ *
            sgnMat G (σ i) +
          sgnMat G (σ i) * blockBasis W L c κ * sgnMat G (σ i) * blockBasis W L c κ *
            sgnMat G (σ i)) * blockE W L (a i)))).prod.trace =
      2 * ((W : ℂ) * loopTr G ![c] ![σ i]) * ((W : ℂ) * loopTr G (insLab a i c) (insSgn σ i)) := by
  simp only [generator_prod_update]
  set Pre := generatorRp (generatorExt (generatorWord G a σ)) 0 i
  set Suf := generatorRp (generatorExt (generatorWord G a σ)) (i + 1) (k - i - 1)
  set X := sgnMat G (σ i) with hX
  set Ei := blockE W L (a i)
  have e : ∀ κ, (Pre * ((X * blockBasis W L c κ * X * blockBasis W L c κ * X +
      X * blockBasis W L c κ * X * blockBasis W L c κ * X) * Ei) * Suf).trace =
      2 * (Pre * (X * (blockBasis W L c κ * X * blockBasis W L c κ) * X * Ei) * Suf).trace := by
    intro κ
    rw [two_mul, ← Matrix.trace_add]
    congr 1
    noncomm_ring
  simp only [e, ← Finset.mul_sum, ← Matrix.trace_sum]
  have e2 : ∑ κ, Pre * (X * (blockBasis W L c κ * X * blockBasis W L c κ) * X * Ei) * Suf =
      Pre * (X * (∑ κ, blockBasis W L c κ * X * blockBasis W L c κ) * X * Ei) * Suf := by
    simp only [Finset.mul_sum, Finset.sum_mul]
  rw [e2, generator_sum_basis_mul_mul, generator_loopTr_one, generator_loopTr_ins,
    generatorRp_tail]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, generatorWord,
    mul_assoc]
  ring

/-- The terms with two distinct factors differentiated once, summed over the block basis of
block `c`: `W² Cut_L Cut_R`. -/
private theorem generator_sum_cross (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) {k : ℕ}
    (a : Fin k → Fin L) (σ : Fin k → Bool) (i j : Fin k) (hij : i < j) (c : Fin L) :
    ∑ κ, (List.ofFn (Function.update (Function.update (generatorWord G a σ) i
        (-(sgnMat G (σ i) * blockBasis W L c κ * sgnMat G (σ i)) * blockE W L (a i))) j
        (-(sgnMat G (σ j) * blockBasis W L c κ * sgnMat G (σ j)) * blockE W L (a j)))).prod.trace =
      ((W : ℂ) * loopTr G (cutLLab a i j c) (cutLSgn σ i j)) *
        ((W : ℂ) * loopTr G (cutRLab a i j c) (cutRSgn σ i j)) := by
  simp only [generator_prod_update₂ _ _ _ hij]
  rw [generator_loopTr_cutL G a σ i j hij c, generator_loopTr_cutR G a σ i j hij c,
    generatorRp_tail, generatorRp_head _ i j hij]
  set Pre := generatorRp (generatorExt (generatorWord G a σ)) 0 i
  set Mid := generatorRp (generatorExt (generatorWord G a σ)) (i + 1) (j - i - 1)
  set Suf := generatorRp (generatorExt (generatorWord G a σ)) (j + 1) (k - j - 1)
  set Xi := sgnMat G (σ i)
  set Xj := sgnMat G (σ j)
  set Ei := blockE W L (a i)
  set Ej := blockE W L (a j)
  set Ec := blockE W L c
  have e : ∀ κ, (Pre * (-(Xi * blockBasis W L c κ * Xi) * Ei) * Mid *
      (-(Xj * blockBasis W L c κ * Xj) * Ej) * Suf).trace =
      (blockBasis W L c κ * (Xi * Ei * Mid * Xj) * blockBasis W L c κ *
        (Xj * Ej * Suf * Pre * Xi)).trace := by
    intro κ
    rw [show Pre * (-(Xi * blockBasis W L c κ * Xi) * Ei) * Mid *
        (-(Xj * blockBasis W L c κ * Xj) * Ej) * Suf =
        (Pre * Xi) * (blockBasis W L c κ * (Xi * Ei * Mid * Xj) * blockBasis W L c κ *
          (Xj * Ej * Suf)) by noncomm_ring, Matrix.trace_mul_comm]
    simp only [mul_assoc]
  simp only [e]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, generator_sum_basis_mul_mul]
  have hL : (Pre * (Xi * Ec) * (generatorWord G a σ j * Suf)).trace =
      (Ec * (Xj * Ej * Suf * Pre * Xi)).trace := by
    rw [show Pre * (Xi * Ec) * (generatorWord G a σ j * Suf) =
        (Pre * Xi) * (Ec * (Xj * Ej * Suf)) by simp only [generatorWord, mul_assoc]; rfl,
      Matrix.trace_mul_comm]
    simp only [mul_assoc]
  rw [hL]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, generatorWord,
    mul_assoc]
  ring

/-- Summing over ordered pairs of distinct positions. -/
private theorem generator_sum_ne {k : ℕ} (H : Fin k → Fin k → ℂ) :
    ∑ i, ∑ j, (if j = i then 0 else H i j) =
      ∑ i, ∑ j, (if i < j then H i j + H j i else 0) := by
  have e : ∀ i j, (if j = i then 0 else H i j) =
      (if i < j then H i j else 0) + (if j < i then H i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_gt h, not_lt_of_gt h]
    · subst h; simp
    · simp [h, ne_of_lt h, not_lt_of_gt h]
  have e' : ∀ i j, (if i < j then H i j + H j i else 0) =
      (if i < j then H i j else 0) + (if i < j then H j i else 0) := by
    intro i j
    split_ifs <;> simp
  simp only [e, e', Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]

/-- The second-order part of the generator on a loop, summed over the block basis of block `c`. -/
private theorem generator_sum_iteratedDeriv (g E : ℝ) (m : ℂ) (hm : 0 < m.im) {k : ℕ} {u : ℝ}
    (hu : u < 1) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    (a : Fin k → Fin L) (σ : Fin k → Bool) (c : Fin L) :
    ∑ κ, iteratedDeriv 2 (fun e : ℝ => resLoop g E m a σ u (M + (e : ℂ) • blockBasis W L c κ)) 0 =
      2 * ((W : ℂ) * (W : ℂ)) *
        (∑ i, loopTr (resolventMat M (zChar g E m u)) ![c] ![σ i] *
            loopTr (resolventMat M (zChar g E m u)) (insLab a i c) (insSgn σ i) +
          ∑ i, ∑ j, if i < j then
            loopTr (resolventMat M (zChar g E m u)) (cutLLab a i j c) (cutLSgn σ i j) *
              loopTr (resolventMat M (zChar g E m u)) (cutRLab a i j c) (cutRSgn σ i j)
            else 0) := by
  set G := resolventMat M (zChar g E m u) with hG
  rw [Finset.sum_congr rfl fun κ _ => generator_iteratedDeriv_loop_line g E m hm hu hM a σ
    (blockBasis_isHermitian W L c κ) G hG.symm, Finset.sum_add_distrib, Finset.sum_comm]
  simp only [generator_sum_self, generator_sum_ne]
  have hswap : ∀ F : (Fin W × Fin W) → Fin k → Fin k → ℂ,
      ∑ κ, ∑ i, ∑ j, F κ i j = ∑ i, ∑ j, ∑ κ, F κ i j := by
    intro F
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [hswap]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i < j
    · simp only [hij, ↓reduceIte]
      rw [Finset.sum_add_distrib, generator_sum_cross G a σ i j hij c]
      have hcomm : ∀ κ, Function.update (Function.update (generatorWord G a σ) j
          (-(sgnMat G (σ j) * blockBasis W L c κ * sgnMat G (σ j)) * blockE W L (a j))) i
          (-(sgnMat G (σ i) * blockBasis W L c κ * sgnMat G (σ i)) * blockE W L (a i)) =
          Function.update (Function.update (generatorWord G a σ) i
          (-(sgnMat G (σ i) * blockBasis W L c κ * sgnMat G (σ i)) * blockE W L (a i))) j
          (-(sgnMat G (σ j) * blockBasis W L c κ * sgnMat G (σ j)) * blockE W L (a j)) :=
        fun κ => Function.update_comm (ne_of_gt hij) _ _ _
      simp only [hcomm, generator_sum_cross G a σ i j hij c]
      ring
    · simp [hij]


/-- Bookkeeping of the time part, the self terms and the cross terms of (5.8) [fo:eq:hierarchy]. -/
private theorem generator_assemble {k L : ℕ} (coef γW γ w : ℂ) (hc : coef * (2 * (w * w)) = γW)
    (hγ : γ * w = γW) (I L1 : Fin k → Fin L → ℂ) (S : Fin k → ℂ) (C : Fin L → Fin k → Fin k → ℂ) :
    (∑ i, ∑ c, (-γ * S i * w) * I i c) +
        coef * ∑ c, 2 * (w * w) *
          (∑ i, L1 i c * I i c + ∑ i, ∑ j, if i < j then C c i j else 0) =
      γW * ∑ i, ∑ c, (L1 i c - S i) * I i c +
        γW * ∑ i, ∑ j, if i < j then ∑ c, C c i j else 0 := by
  have h1 : coef * ∑ c, 2 * (w * w) *
      (∑ i, L1 i c * I i c + ∑ i, ∑ j, if i < j then C c i j else 0) =
      γW * (∑ i, ∑ c, L1 i c * I i c) + γW * ∑ i, ∑ j, if i < j then ∑ c, C c i j else 0 := by
    have hB : (∑ c, ∑ i, ∑ j, if i < j then C c i j else 0) =
        ∑ i, ∑ j, if i < j then ∑ c, C c i j else 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    have e : ∀ c, coef * (2 * (w * w) *
        (∑ i, L1 i c * I i c + ∑ i, ∑ j, if i < j then C c i j else 0)) =
        γW * (∑ i, L1 i c * I i c) + γW * ∑ i, ∑ j, if i < j then C c i j else 0 := by
      intro c
      rw [← mul_assoc, hc, mul_add]
    rw [Finset.mul_sum]
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, hB]
    rw [Finset.sum_comm]
  have h2 : (∑ i, ∑ c, (-γ * S i * w) * I i c) = -(γW * ∑ i, ∑ c, S i * I i c) := by
    rw [← hγ, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [h1, h2]
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

end GeneratorHierarchy

/-- (5.8) [fo:eq:hierarchy] in generator form: `𝒢_u ℒ_k = 𝒲_k + γW Σ_{i<j} Σ_c Cut_L Cut_R`. -/
theorem blockGen_loopTr (g E : ℝ) (m : ℂ) (hm : 0 < m.im) {W L k : ℕ} {u : ℝ} (hu : u < 1)
    {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian) (a : Fin k → Fin L)
    (σ : Fin k → Bool) :
    blockGen W L (gammaG g) (resLoop g E m a σ) u M =
      lightW g E m a σ u M + ((gammaG g * W : ℝ) : ℂ) *
        cutSumFam (fun n b τ => loopTr (resolventMat M (zChar g E m u)) b τ) a σ := by
  unfold blockGen lightW cutSumFam
  rw [generator_deriv_loop_time g E m hm hu hM a σ]
  simp only [generator_sum_iteratedDeriv g E m hm hu hM a σ]
  have hc := generator_coef (W := W) (gammaG g)
  have hγ : ((gammaG g : ℝ) : ℂ) * (W : ℂ) = ((gammaG g * W : ℝ) : ℂ) := by push_cast; ring
  exact generator_assemble _ _ _ _ hc hγ
    (fun i c => loopTr (resolventMat M (zChar g E m u)) (insLab a i c) (insSgn σ i))
    (fun i c => loopTr (resolventMat M (zChar g E m u)) ![c] ![σ i])
    (fun i => sgnScalar m (σ i))
    (fun c i j => loopTr (resolventMat M (zChar g E m u)) (cutLLab a i j c) (cutLSgn σ i j) *
      loopTr (resolventMat M (zChar g E m u)) (cutRLab a i j c) (cutRSgn σ i j))

/-- `B_i = X^{σ_i} E_{a_i} ⋯ X^{σ_{i+k-1}} E_{a_{i+k-1}} X^{σ_i}` (indices mod `k`), before (5.9)
[gc:eq:bracket]. -/
def loopB {W L k : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a : Fin k → Fin L)
    (σ : Fin k → Bool) (i : Fin k) : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  (List.ofFn fun p : Fin k => sgnMat X (σ (i + p)) * blockE W L (a (i + p))).prod * sgnMat X (σ i)

section GeneratorBracket

open scoped Matrix.Norms.L2Operator

variable {W L : ℕ}

private theorem generator_loopB {k : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a : Fin k → Fin L) (σ : Fin k → Bool) (i : Fin k) :
    loopB X a σ i =
      generatorRp (generatorExt (generatorWord X a σ)) i (k - i) *
        generatorRp (generatorExt (generatorWord X a σ)) 0 i * sgnMat X (σ i) := by
  set Y := generatorExt (generatorWord X a σ) with hY
  have hi := i.2
  unfold loopB
  rw [generatorRp_ofFn _ (fun x => Y ((i + x) % k)) 0 (fun p => by
      simp only [hY, zero_add, generatorExt, Nat.mod_lt _ (by omega : 0 < k), dite_true]
      simp only [generatorWord]
      congr)]
  have hk : k = (k - i) + i := by omega
  rw [congrArg (generatorRp (fun x => Y ((i + x) % k)) 0) hk, generatorRp_add,
    generatorRp_congr _ Y 0 i (k - i) (fun x hx => by
      simp only [zero_add]; rw [Nat.mod_eq_of_lt (by omega)]),
    generatorRp_congr _ Y (0 + (k - i)) 0 i (fun x hx => by
      simp only [zero_add]
      rw [show (i : ℕ) + (k - i + x) = x + k by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)])]

/-- The first derivative of a resolvent loop along a block basis direction at `0`:
`∂_T ℒ_k = -Σ_i Tr(T B_i)`. -/
private theorem generator_deriv_loop_basis (g E : ℝ) (m : ℂ) (hm : 0 < m.im) {k : ℕ} {u : ℝ}
    (hu : u < 1) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    (a : Fin k → Fin L) (σ : Fin k → Bool) (c : Fin L) (κ : Fin W × Fin W) :
    deriv (fun e : ℝ => resLoop g E m a σ u (M + (e : ℂ) • blockBasis W L c κ)) 0 =
      -∑ i, (blockBasis W L c κ * loopB (resolventMat M (zChar g E m u)) a σ i).trace := by
  set T := blockBasis W L c κ with hTdef
  have hT : T.IsHermitian := blockBasis_isHermitian W L c κ
  set G := resolventMat M (zChar g E m u) with hG
  have hz := generator_im_zChar_ne g E m hm hu
  have hfun : (fun e : ℝ => resLoop g E m a σ u (M + (e : ℂ) • T)) = fun e : ℝ =>
      (List.ofFn fun p => resolventMat (M + (e : ℂ) • T) (zChar g E (sgnScalar m (σ p)) u) *
        blockE W L (a p)).prod.trace := by
    funext e
    unfold resLoop loopTr
    congr 3
    funext p
    rw [generator_sgnMat_resolvent (generator_isHermitian_line hM hT e),
      generator_sgnScalar_zChar]
  rw [hfun]
  have hd := generator_hasDerivAt_trace (generator_hasDerivAt_prod
    (fun p e => resolventMat (M + (e : ℂ) • T) (zChar g E (sgnScalar m (σ p)) u) * blockE W L (a p))
    (fun p e => -(resolventMat (M + (e : ℂ) • T) (zChar g E (sgnScalar m (σ p)) u) * T *
      resolventMat (M + (e : ℂ) • T) (zChar g E (sgnScalar m (σ p)) u)) * blockE W L (a p)) 0
    (fun p => by
      have h := (hasDerivAt_resolventMat_line hM hT (hz (σ p)) 0).mul_const (blockE W L (a p))
      exact h))
  rw [hd.deriv]
  have h0 : ∀ s : Bool, resolventMat (M + ((0 : ℝ) : ℂ) • T) (zChar g E (sgnScalar m s) u) =
      sgnMat G s := by
    intro s
    rw [Complex.ofReal_zero, zero_smul, add_zero, ← generator_sgnScalar_zChar,
      ← generator_sgnMat_resolvent hM]
  simp only [h0]
  rw [Matrix.trace_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (fun p => sgnMat G (σ p) * blockE W L (a p)) = generatorWord G a σ from rfl,
    generator_prod_update, generator_loopB, generatorRp_tail]
  set Pre := generatorRp (generatorExt (generatorWord G a σ)) 0 i
  set Suf := generatorRp (generatorExt (generatorWord G a σ)) (i + 1) (k - i - 1)
  set X := sgnMat G (σ i)
  have e1 : Pre * (-(X * T * X) * blockE W L (a i)) * Suf =
      -((Pre * X) * (T * (X * blockE W L (a i) * Suf))) := by noncomm_ring
  rw [e1, Matrix.trace_neg, Matrix.trace_mul_comm]
  simp only [generatorWord, mul_assoc]
  rfl

end GeneratorBracket

/-- (5.9) [gc:eq:bracket] in generator form. -/
theorem blockGamma_loopTr (g E : ℝ) (m : ℂ) (hm : 0 < m.im) {W L k k' : ℕ} {u : ℝ} (hu : u < 1)
    {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian) (a : Fin k → Fin L)
    (σ : Fin k → Bool) (a' : Fin k' → Fin L) (σ' : Fin k' → Bool) :
    blockGamma W L (gammaG g) (resLoop g E m a σ u) (resLoop g E m a' σ' u) M =
      ((gammaG g / W : ℝ) : ℂ) * ∑ c : Fin L, ∑ i : Fin k, ∑ j : Fin k',
        (((W : ℂ) • blockE W L c) * loopB (resolventMat M (zChar g E m u)) a σ i *
          ((W : ℂ) • blockE W L c) * (loopB (resolventMat M (zChar g E m u)) a' σ' j)ᴴ).trace := by
  unfold blockGamma
  simp only [generator_deriv_loop_basis g E m hm hu hM]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  set G := resolventMat M (zChar g E m u)
  have hstar : ∀ κ j, star (blockBasis W L c κ * loopB G a' σ' j).trace =
      ((loopB G a' σ' j)ᴴ * blockBasis W L c κ).trace := by
    intro κ j
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      (blockBasis_isHermitian W L c κ).eq]
  simp only [neg_mul_neg, star_neg, star_sum, hstar, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact generator_sum_trace_mul_trace c _ _

/-- `|ℒ_2(a,c;+,+)| ≤ (ℒ_2(a,c;+,-) ℒ_2(c,a;+,-))^{1/2}` for every matrix. -/
theorem norm_loopTr_pp_le {W L : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a c : Fin L) :
    ‖loopTr X ![a, c] ![true, true]‖ ≤
      Real.sqrt ((loopTr X ![a, c] ![true, false]).re * (loopTr X ![c, a] ![true, false]).re) := by
  set w : Fin L × Fin W → Fin L × Fin W → ℝ := fun p q =>
    (if q.1 = a then (W : ℝ)⁻¹ else 0) * (if p.1 = c then (W : ℝ)⁻¹ else 0) with hw
  have hw0 : ∀ p q, 0 ≤ w p q := by
    intro p q
    simp only [hw]
    apply mul_nonneg <;> split_ifs <;> positivity
  have h1 : loopTr X ![a, c] ![true, true] = ∑ p, ∑ q, X p q * X q p * (w p q : ℂ) := by
    rw [generator_loopTr_two_apply]; simp [sgnMat, hw]
  have h2 : (loopTr X ![a, c] ![true, false]).re = ∑ p, ∑ q, (‖X p q‖ * Real.sqrt (w p q)) ^ 2 := by
    rw [generator_loopTr_two_apply]
    simp only [sgnMat, ↓reduceIte, Bool.false_eq_true, Matrix.conjTranspose_apply,
      Complex.star_def, Complex.mul_conj', Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [mul_pow, Real.sq_sqrt (hw0 p q), hw]
    norm_cast
  have h3 : (loopTr X ![c, a] ![true, false]).re = ∑ p, ∑ q, (‖X q p‖ * Real.sqrt (w p q)) ^ 2 := by
    rw [generator_loopTr_two_apply, Finset.sum_comm]
    simp only [sgnMat, ↓reduceIte, Bool.false_eq_true, Matrix.conjTranspose_apply,
      Complex.star_def, Complex.mul_conj', Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [mul_pow, Real.sq_sqrt (hw0 p q), hw]
    norm_cast
    ring
  rw [h1, h2, h3]
  calc ‖∑ p, ∑ q, X p q * X q p * (w p q : ℂ)‖
      ≤ ∑ p, ∑ q, (‖X p q‖ * Real.sqrt (w p q)) * (‖X q p‖ * Real.sqrt (w p q)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw0 p q)]
        refine le_of_eq ?_
        rw [show ‖X p q‖ * √(w p q) * (‖X q p‖ * √(w p q)) =
          ‖X p q‖ * ‖X q p‖ * (√(w p q) * √(w p q)) by ring, Real.mul_self_sqrt (hw0 p q)]
    _ = ∑ x : (Fin L × Fin W) × (Fin L × Fin W),
          (‖X x.1 x.2‖ * Real.sqrt (w x.1 x.2)) * (‖X x.2 x.1‖ * Real.sqrt (w x.1 x.2)) :=
        (Fintype.sum_prod_type' _).symm
    _ ≤ Real.sqrt (∑ x : (Fin L × Fin W) × (Fin L × Fin W),
          (‖X x.1 x.2‖ * Real.sqrt (w x.1 x.2)) ^ 2) *
        Real.sqrt (∑ x : (Fin L × Fin W) × (Fin L × Fin W),
          (‖X x.2 x.1‖ * Real.sqrt (w x.1 x.2)) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = Real.sqrt ((∑ p, ∑ q, (‖X p q‖ * Real.sqrt (w p q)) ^ 2) *
          ∑ p, ∑ q, (‖X q p‖ * Real.sqrt (w p q)) ^ 2) := by
        have e1 : ∑ x : (Fin L × Fin W) × (Fin L × Fin W),
            (‖X x.1 x.2‖ * Real.sqrt (w x.1 x.2)) ^ 2 =
            ∑ p, ∑ q, (‖X p q‖ * Real.sqrt (w p q)) ^ 2 := Fintype.sum_prod_type _
        have e2 : ∑ x : (Fin L × Fin W) × (Fin L × Fin W),
            (‖X x.2 x.1‖ * Real.sqrt (w x.1 x.2)) ^ 2 =
            ∑ p, ∑ q, (‖X q p‖ * Real.sqrt (w p q)) ^ 2 := Fintype.sum_prod_type _
        rw [e1, e2, ← Real.sqrt_mul]
        exact Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => sq_nonneg _


end LSBA
