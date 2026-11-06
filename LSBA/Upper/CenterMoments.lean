import LSBA.Upper.CenterNewton
import LSBA.Upper.CenterInnovation
import LSBA.Analysis.MomentTools

/-!
# The one-step moment recursion

The one-step moment recursion (11.59) [lg:eq:momentrec] for weighted sums of `|M_k − a_k|^{2p}`
and `|F_k|^{2p}` over a finite index set `J` that contains, with each `k`, every `j ≠ 0` with
`|j| ≤ |k|`, coupled to a larger fixed set `J′` (proof of Lemma 11.8 [lg:lem:dynamic]).
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA
/-! ### Real inequalities -/

/-- Convex splitting: `((1 − t/8) a + t b)^n ≤ (1 − t/16) a^n + 16^{n−1} t b^n`. -/
private lemma cm_split {n : ℕ} (hn : 1 ≤ n) {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    ((1 - t / 8) * a + t * b) ^ n ≤ (1 - t / 16) * a ^ n + 16 ^ (n - 1) * t * b ^ n := by
  have hl : 0 < 1 - t / 16 := by linarith
  set r := (1 - t / 8) / (1 - t / 16) with hr
  have hr0 : 0 ≤ r := div_nonneg (by linarith) hl.le
  have hr1 : r ≤ 1 := (div_le_one hl).mpr (by linarith)
  have hconv := (convexOn_pow n).2 (Set.mem_Ici.mpr (mul_nonneg hr0 ha))
    (Set.mem_Ici.mpr (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hb)) hl.le
    (by linarith : (0 : ℝ) ≤ t / 16) (by ring : (1 - t / 16) + t / 16 = 1)
  simp only [smul_eq_mul] at hconv
  have he : (1 - t / 16) * (r * a) + t / 16 * (16 * b) = (1 - t / 8) * a + t * b := by
    rw [← mul_assoc, hr, mul_div_cancel₀ _ hl.ne']; ring
  rw [he] at hconv
  refine hconv.trans (add_le_add ?_ (le_of_eq ?_))
  · rw [mul_pow]
    have : r ^ n ≤ 1 := pow_le_one₀ hr0 hr1
    have h2 : 0 ≤ a ^ n := pow_nonneg ha n
    exact mul_le_mul_of_nonneg_left (by nlinarith) hl.le
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [mul_pow, pow_succ]
    simp only [Nat.add_sub_cancel]
    ring

/-- `x^{p−1} y ≤ ε x^p + y^p / ε^{p−1}`. -/
private lemma cm_young {p : ℕ} (hp : 1 ≤ p) {x y ε : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hε : 0 < ε) :
    x ^ (p - 1) * y ≤ ε * x ^ p + y ^ p / ε ^ (p - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h1 : 0 ≤ y ^ (m + 1) / ε ^ m := by positivity
  have h2 : 0 ≤ ε * x ^ (m + 1) := by positivity
  rcases le_total y (ε * x) with h | h
  · have : x ^ m * y ≤ x ^ m * (ε * x) := mul_le_mul_of_nonneg_left h (pow_nonneg hx m)
    rw [pow_succ]; nlinarith
  · have hxy : x ≤ y / ε := by rw [le_div_iff₀ hε]; linarith
    have : x ^ m ≤ (y / ε) ^ m := pow_le_pow_left₀ hx hxy m
    calc x ^ m * y ≤ (y / ε) ^ m * y := mul_le_mul_of_nonneg_right this hy
      _ = y ^ (m + 1) / ε ^ m := by rw [div_pow, pow_succ]; ring
      _ ≤ _ := by linarith

/-- `a^{n−j} b^j ≤ a^{n−2} b² + b^n` for `2 ≤ j ≤ n`. -/
private lemma cm_mix {n j : ℕ} (hj : 2 ≤ j) (hjn : j ≤ n) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ (n - j) * b ^ j ≤ a ^ (n - 2) * b ^ 2 + b ^ n := by
  have h1 : 0 ≤ a ^ (n - 2) * b ^ 2 := by positivity
  have h2 : 0 ≤ b ^ n := by positivity
  rcases le_total b a with h | h
  · have e1 : a ^ (n - 2) = a ^ (n - j) * a ^ (j - 2) := by rw [← pow_add]; congr 1; omega
    have e2 : b ^ j = b ^ (j - 2) * b ^ 2 := by rw [← pow_add]; congr 1; omega
    rw [e1, e2]
    have : b ^ (j - 2) ≤ a ^ (j - 2) := pow_le_pow_left₀ hb h _
    have h3 : 0 ≤ a ^ (n - j) * b ^ 2 := by positivity
    nlinarith
  · have : a ^ (n - j) ≤ b ^ (n - j) := pow_le_pow_left₀ ha h _
    have e : b ^ n = b ^ (n - j) * b ^ j := by rw [← pow_add]; congr 1; omega
    have h3 : 0 ≤ b ^ j := by positivity
    nlinarith

/-- `(Σ_s f)^n ≤ #s^{n−1} Σ_s f^n`. -/
private lemma cm_pow_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) {n : ℕ}
    (hn : 1 ≤ n) : (∑ i ∈ s, f i) ^ n ≤ (s.card : ℝ) ^ (n - 1) * ∑ i ∈ s, f i ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simpa using pow_sum_le_card_mul_sum_pow hf m

/-! ### Supports and ideals of the corrected updates -/

private lemma cm_weight_gamWt (d : ObsVar →₀ ℕ) : Finsupp.weight ObsVar.gamWt d = d .γ := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_single ObsVar.γ]
  · simp [ObsVar.gamWt]
  · intro b _ hb
    cases b <;> simp_all [ObsVar.gamWt]
  · intro h
    simp [Finsupp.notMem_support_iff.mp h]

private lemma cm_coeff_truncG (N : ℕ) (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (truncG N p).coeff d = if d .γ ≤ N then p.coeff d else 0 := by
  unfold truncG
  rw [LinearMap.sum_apply, MvPolynomial.coeff_sum]
  simp only [coeff_weightedHomogeneousComponent, cm_weight_gamWt]
  rw [Finset.sum_ite_eq]
  simp

private lemma cm_support_truncG (N : ℕ) (p : ObsPoly) : (truncG N p).support ⊆ p.support :=
  fun d hd => by
    rw [mem_support_iff, cm_coeff_truncG] at hd; rw [mem_support_iff]; split_ifs at hd <;> simp_all

private lemma cm_supported_of_support {s : Set ObsVar} {p q : ObsPoly} (h : p.support ⊆ q.support)
    (hq : q ∈ supported ℂ s) : p ∈ supported ℂ s := by
  rw [mem_supported] at hq ⊢
  intro i hi
  obtain ⟨d, hd, hid⟩ := (mem_vars_iff_mem_support _).mp hi
  exact hq ((mem_vars_iff_mem_support _).mpr ⟨d, h hd, hid⟩)

private lemma cm_bind₁_mem {s t : Set ObsVar} {f : ObsVar → ObsPoly}
    (hf : ∀ v ∈ s, f v ∈ supported ℂ t) {p : ObsPoly} (hp : p ∈ supported ℂ s) :
    bind₁ f p ∈ supported ℂ t := by
  rw [mem_supported] at hp ⊢
  intro j hj
  obtain ⟨i, hi, hj'⟩ := mem_vars_bind₁ f p hj
  exact mem_supported.mp (hf i (hp hi)) hj'

private lemma cm_γ_mem : ObsVar.γ ∈ traceVars := Or.inl ⟨rfl, fun h => ObsVar.noConfusion h⟩

private lemma cm_corrCoord_γ (E : ℝ) (R : ℕ) : corrCoord E R .γ = X .γ := rfl

private lemma cm_trace_corrCoord (E : ℝ) (R : ℕ) {v : ObsVar} (hv : v ∈ traceVars) :
    corrCoord E R v ∈ supported ℂ traceVars := by
  rcases hv with ⟨h0, hw⟩ | ⟨k, rfl⟩
  · cases v with
    | m j => exact (corrObs_form E R j).2.2.1
    | f j => exact absurd h0 j.2
    | w => exact absurd rfl hw
    | γ => rw [cm_corrCoord_γ]; exact X_mem_supported.mpr cm_γ_mem
  · exact (corrObs_form E R k).2.2.1

private lemma cm_trace_revCoord (E : ℝ) (R N : ℕ) (r : ℕ) :
    ∀ v ∈ traceVars, revCoord N (corrCoord E R) r v ∈ supported ℂ traceVars := by
  induction r with
  | zero => exact fun v hv => X_mem_supported.mpr hv
  | succ r ih =>
    intro v hv
    have h : (X v - bind₁ (revCoord N (corrCoord E R) r) (corrCoord E R v - X v) : ObsPoly) ∈
        supported ℂ traceVars :=
      Subalgebra.sub_mem _ (X_mem_supported.mpr hv) (cm_bind₁_mem ih
        (Subalgebra.sub_mem _ (cm_trace_corrCoord E R hv) (X_mem_supported.mpr hv)))
    exact cm_supported_of_support (cm_support_truncG _ _) h

private lemma cm_zeroW_mem {p : ObsPoly} (hp : p ∈ supported ℂ (traceVars ∪ {.w})) :
    zeroW p ∈ supported ℂ traceVars := by
  unfold zeroW
  rw [aeval_eq_bind₁]
  refine cm_bind₁_mem (fun v hv => ?_) hp
  split_ifs with h
  · exact Subalgebra.zero_mem _
  · rcases hv with hv | hv
    · exact X_mem_supported.mpr hv
    · exact absurd hv h

private lemma cm_rot_mem (E : ℝ) {p : ObsPoly} (hp : p ∈ supported ℂ traceVars) :
    rotPoly E p ∈ supported ℂ traceVars := by
  unfold rotPoly
  rw [aeval_eq_bind₁]
  exact cm_bind₁_mem (fun v hv => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (X_mem_supported.mpr hv)) hp

private lemma cm_trace_updPoly (E : ℝ) (N : ℕ) {p : ObsPoly} (hp : p ∈ supported ℂ traceVars) :
    updPoly E N p ∈ supported ℂ traceVars := by
  have hz : ∀ r, zeroW (wickMap r (rotPoly E p)) ∈ supported ℂ traceVars := fun r =>
    cm_zeroW_mem (wickMap_traceVars r (rotPoly E p) (cm_rot_mem E hp)).1
  have hs : (∑ r ∈ Finset.range (N + 1),
      C (((normalH E ^ (2 * r) : ℝ) : ℂ)) * X .γ ^ r * zeroW (wickMap r (rotPoly E p))) ∈
      supported ℂ traceVars :=
    Subalgebra.sum_mem _ fun r _ => Subalgebra.mul_mem _ (Subalgebra.mul_mem _
      (Subalgebra.algebraMap_mem _ _) (Subalgebra.pow_mem _ (X_mem_supported.mpr cm_γ_mem) _))
      (hz r)
  unfold updPoly
  exact cm_supported_of_support (cm_support_truncG _ _) hs

/-- The corrected update of `M_k` is a polynomial in the `m_j` and `γ` (Lemma 11.7 (iii)
[lg:lem:ideal]). -/
private lemma cm_trace_corrUpd (E : ℝ) (R : ℕ) (k : NzInt) :
    corrUpd E R (.m k) ∈ supported ℂ traceVars :=
  cm_supported_of_support (cm_support_truncG _ _) (cm_bind₁_mem
    (fun v hv => cm_trace_revCoord E R (R + 2) (R + 2) v hv)
    (cm_trace_updPoly E (R + 2) (corrObs_form E R k).2.2.1))

private lemma cm_fIdeal_of_support {p q : ObsPoly} (h : p.support ⊆ q.support) (hq : q ∈ fIdeal) :
    p ∈ fIdeal := by
  rw [fIdeal, show Set.range (fun k : NzInt => (X (.f k) : ObsPoly)) = X '' Set.range ObsVar.f
    by rw [← Set.range_comp]; rfl, mem_ideal_span_X_image] at hq ⊢
  exact fun d hd => hq d (h hd)

private lemma cm_fIdeal_map {φ : ObsPoly →ₐ[ℂ] ObsPoly} (hφ : ∀ k, φ (X (.f k)) ∈ fIdeal)
    {p : ObsPoly} (hp : p ∈ fIdeal) : φ p ∈ fIdeal := by
  have h : Ideal.map φ fIdeal ≤ fIdeal := by
    rw [fIdeal, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    exact hφ k
  exact h (Ideal.mem_map_of_mem φ hp)

/-- The corrected update of `F_k` lies in the ideal `(f_j)` (Lemma 11.7 (i) [lg:lem:ideal]). -/
private lemma cm_f_corrUpd (E : ℝ) (R : ℕ) (k : NzInt) : corrUpd E R (.f k) ∈ fIdeal := by
  have hX : ∀ j : NzInt, (X (.f j) : ObsPoly) ∈ fIdeal := fun j => Ideal.subset_span ⟨j, rfl⟩
  have hsub : fIdeal ≤ obsIdeal := Ideal.span_mono (Set.subset_union_right)
  have hupd : updPoly E (R + 2) (corrObsF E R k) ∈ fIdeal := by
    refine cm_fIdeal_of_support (cm_support_truncG _ _) (Ideal.sum_mem _ fun r _ => ?_)
    refine Ideal.mul_mem_left _ _ ?_
    have hrot : rotPoly E (corrObsF E R k) ∈ fIdeal := cm_fIdeal_map (fun j => by
      rw [rotPoly, aeval_X]; exact Ideal.mul_mem_left _ _ (hX j))
      (corrObs_form E R k).2.2.2.2.2.2.1
    have hw := wickMap_mem_obsIdeal r (hsub hrot)
    have hz : Ideal.map zeroW obsIdeal ≤ fIdeal := by
      rw [obsIdeal, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, hx, rfl⟩
      rcases hx with hx | ⟨j, rfl⟩
      · rw [Set.mem_singleton_iff.mp hx, zeroW, aeval_X]; simp
      · rw [zeroW, aeval_X]
        simp only [reduceCtorEq, ite_false]
        exact hX j
    exact hz (Ideal.mem_map_of_mem zeroW hw)
  exact cm_fIdeal_of_support (cm_support_truncG _ _)
    (cm_fIdeal_map (φ := bind₁ (invCoord E R)) (fun j => by
      rw [bind₁_X_right]; exact (corrObs_form E R j).2.2.2.2.2.2.2) hupd)

/-! ### Differences of monomials -/

private lemma cm_pow_sub {a b : ℂ} {B : ℝ} (hB : 1 ≤ B) (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (e : ℕ) :
    ‖a ^ e - b ^ e‖ ≤ e * B ^ e * ‖a - b‖ := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hae : ‖a ^ e‖ ≤ B ^ e := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) ha e
    have h1 : 0 ≤ B ^ e * ‖a - b‖ := by positivity
    rw [show a ^ (e + 1) - b ^ (e + 1) = a ^ e * (a - b) + (a ^ e - b ^ e) * b by ring, pow_succ]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]; push_cast
    nlinarith [mul_le_mul_of_nonneg_right hae (norm_nonneg (a - b)),
      mul_le_mul_of_nonneg_left hB h1, mul_le_mul ih hb (norm_nonneg _) (by positivity),
      mul_nonneg (Nat.cast_nonneg (α := ℝ) e) h1]

private lemma cm_norm_prod_le {ι : Type*} (s : Finset ι) (e : ι → ℕ) (b : ι → ℂ) {B : ℝ}
    (hb : ∀ i ∈ s, ‖b i‖ ≤ B) : ‖∏ i ∈ s, b i ^ e i‖ ≤ B ^ (∑ i ∈ s, e i) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  refine (Finset.norm_prod_le _ _).trans (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    fun i hi => ?_)
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hb i hi) _

private lemma cm_prod_sub {ι : Type*} (s : Finset ι) (e : ι → ℕ) (a b : ι → ℂ)
    {B : ℝ} (hB : 1 ≤ B) (ha : ∀ i ∈ s, ‖a i‖ ≤ B) (hb : ∀ i ∈ s, ‖b i‖ ≤ B) :
    ‖∏ i ∈ s, a i ^ e i - ∏ i ∈ s, b i ^ e i‖ ≤
      (∑ i ∈ s, e i : ℕ) * B ^ (∑ i ∈ s, e i) * ∑ i ∈ s, ‖a i - b i‖ := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hai := ha i (Finset.mem_insert_self i s)
    have ih' := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      (fun j hj => hb j (Finset.mem_insert_of_mem hj))
    have hP := cm_norm_prod_le s e b (fun j hj => hb j (Finset.mem_insert_of_mem hj))
    have hai' : ‖a i ^ e i‖ ≤ B ^ e i := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hai _
    have hdi := cm_pow_sub hB hai (hb i (Finset.mem_insert_self i s)) (e i)
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi, Finset.sum_insert hi,
      show ∀ x y z w : ℂ, x * y - z * w = x * (y - w) + (x - z) * w from fun _ _ _ _ => by ring]
    set Es := ∑ j ∈ s, e j
    set Ss := ∑ j ∈ s, ‖a j - b j‖
    have hSs : 0 ≤ Ss := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have h3 : 0 ≤ B ^ e i * B ^ Es := by positivity
    have h0 : 0 ≤ ‖a i - b i‖ := norm_nonneg _
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, pow_add]; push_cast
    nlinarith [mul_le_mul hai' ih' (norm_nonneg _) (by positivity),
      mul_le_mul hdi hP (norm_nonneg _) (by positivity),
      mul_nonneg h3 (mul_nonneg (Nat.cast_nonneg (α := ℝ) Es) h0),
      mul_nonneg h3 (mul_nonneg (Nat.cast_nonneg (α := ℝ) (e i)) hSs)]

/-- Lipschitz bound for a polynomial all of whose monomials contain `γ²`, between two valuations
that agree at `γ`. -/
private lemma cm_lip (q : ObsPoly) {S : Finset (ObsVar →₀ ℕ)} (hS : q.support ⊆ S) {K : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ d, ‖q.coeff d‖ ≤ K) (h2 : ∀ d ∈ q.support, 2 ≤ d .γ)
    {x y : ObsVar → ℂ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hx : x .γ = t) (hy : y .γ = t)
    {B Δ : ℝ} (hB : 1 ≤ B) (hΔ : 0 ≤ Δ)
    (hxy : ∀ d ∈ q.support, ∀ v ∈ d.support, ‖x v‖ ≤ B ∧ ‖y v‖ ≤ B ∧ ‖x v - y v‖ ≤ Δ) :
    ‖aeval x q - aeval y q‖ ≤
      t ^ 2 * (K * ∑ d ∈ S, ((∑ v ∈ d.support, d v : ℕ) : ℝ) * B ^ (∑ v ∈ d.support, d v) *
        d.support.card) * Δ := by
  rw [show aeval x q = eval x q from rfl, show aeval y q = eval y q from rfl, eval_eq, eval_eq,
    ← Finset.sum_sub_distrib]
  set T : (ObsVar →₀ ℕ) → ℝ := fun d =>
    ((∑ v ∈ d.support, d v : ℕ) : ℝ) * B ^ (∑ v ∈ d.support, d v) * d.support.card with hT
  have hT0 : ∀ d, 0 ≤ T d := fun d => by positivity
  have hd : ∀ d ∈ q.support, ‖q.coeff d * ∏ i ∈ d.support, x i ^ d i -
      q.coeff d * ∏ i ∈ d.support, y i ^ d i‖ ≤ t ^ 2 * K * T d * Δ := by
    intro d hdq
    have hγ : ObsVar.γ ∈ d.support := Finsupp.mem_support_iff.mpr (by have := h2 d hdq; omega)
    rw [← mul_sub, norm_mul, ← Finset.mul_prod_erase _ _ hγ, ← Finset.mul_prod_erase _ _ hγ,
      hx, hy, ← mul_sub, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht0]
    have htp : t ^ d .γ ≤ t ^ 2 := pow_le_pow_of_le_one ht0 ht1 (h2 d hdq)
    have hsub := cm_prod_sub (d.support.erase .γ) (fun i => d i) x y hB
      (fun i hi => (hxy d hdq i (Finset.mem_of_mem_erase hi)).1)
      (fun i hi => (hxy d hdq i (Finset.mem_of_mem_erase hi)).2.1)
    have hE : (∑ i ∈ d.support.erase .γ, d i) ≤ ∑ v ∈ d.support, d v :=
      Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
    have hS1 : ∑ i ∈ d.support.erase .γ, ‖x i - y i‖ ≤ d.support.card * Δ := by
      refine (Finset.sum_le_card_nsmul _ _ Δ fun i hi =>
        (hxy d hdq i (Finset.mem_of_mem_erase hi)).2.2).trans ?_
      rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_erase_le) hΔ
    have hprod : ‖∏ i ∈ d.support.erase .γ, x i ^ d i - ∏ i ∈ d.support.erase .γ, y i ^ d i‖ ≤
        T d * Δ := by
      refine hsub.trans (le_of_le_of_eq (b := ((∑ v ∈ d.support, d v : ℕ) : ℝ) *
        B ^ (∑ v ∈ d.support, d v) * (d.support.card * Δ)) ?_ (by rw [hT]; ring))
      gcongr
    calc ‖q.coeff d‖ * (t ^ d .γ * ‖∏ i ∈ d.support.erase .γ, x i ^ d i -
          ∏ i ∈ d.support.erase .γ, y i ^ d i‖)
        ≤ K * (t ^ 2 * (T d * Δ)) := by gcongr; exact hK d
      _ = t ^ 2 * K * T d * Δ := by ring
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hd).trans ?_)
  have : ∑ d ∈ q.support, t ^ 2 * K * T d * Δ ≤ ∑ d ∈ S, t ^ 2 * K * T d * Δ :=
    Finset.sum_le_sum_of_subset_of_nonneg hS fun d _ _ => by
      have := hT0 d; positivity
  refine this.trans (le_of_eq ?_)
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-! ### The leading coefficients at a valuation

(11.51) [lg:eq:center-corner] and (11.52) [lg:eq:center-trace]. -/

/-- (11.52) [lg:eq:center-trace] as a function of the values `M_j` (`M_0 = 1`). -/
private def cmTau (k : ℕ) (M : ℤ → ℂ) : ℂ :=
  -(3 * (k : ℂ)) * M k - 3 * (k : ℂ) * ∑ a ∈ Finset.Icc 1 (k - 1), M a * M ((k : ℤ) - a) -
    (k : ℂ) / 2 * ∑ a ∈ Finset.range (k - 1), M a * M ((k : ℤ) - 2 - a) -
    (k : ℂ) / 2 * ∑ a ∈ Finset.Icc 1 (k + 1), M a * M ((k : ℤ) + 2 - a)

/-- (11.51) [lg:eq:center-corner] as a function of the values `M_j`, `F_j`. -/
private def cmCorner (k : ℕ) (M F : ℤ → ℂ) : ℂ :=
  -(3 * (k : ℂ)) * F k - (if 3 ≤ k then ((k : ℂ) - 2) * F ((k : ℤ) - 2) else 0) -
    ∑ n ∈ Finset.Icc 1 (k + 1), (n : ℂ) * F n * M ((k : ℤ) + 2 - n) -
    6 * ∑ n ∈ Finset.Icc 1 (k - 1), (n : ℂ) * F n * M ((k : ℤ) - n) -
    ∑ n ∈ Finset.Icc 1 (k - 3), (n : ℂ) * F n * M ((k : ℤ) - 2 - n) +
    F k * (M 1 * F 1 + M (-1) * F (-1))

private lemma cm_eval_trace (z : ObsVar → ℂ) (k : ℕ) :
    aeval z (centerTrace k) = cmTau k (fun j => aeval z (mVar j)) := by
  simp [centerTrace, cmTau, map_sum]

private lemma cm_eval_corner (z : ObsVar → ℂ) (k : ℕ) :
    aeval z (centerCorner k) =
      cmCorner k (fun j => aeval z (mVar j)) (fun j => aeval z (fVar j)) := by
  simp only [centerCorner, cmCorner, map_sub, map_add, map_mul, map_sum, map_neg, aeval_C,
    Algebra.algebraMap_self, RingHom.id_apply]
  split_ifs <;> simp

private lemma cm_norm_sum_le {s : Finset ℕ} {f : ℕ → ℂ} {c : ℝ} {N : ℕ} (hc : 0 ≤ c)
    (hN : s.card ≤ N) (h : ∀ a ∈ s, ‖f a‖ ≤ c) : ‖∑ a ∈ s, f a‖ ≤ N * c := by
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ c h).trans ?_)
  rw [nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hN) hc

private lemma cm_prod_diff {a b c d : ℂ} {B S : ℝ} (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ B)
    (h1 : ‖a - c‖ ≤ S) (h2 : ‖b - d‖ ≤ S) (hB : 0 ≤ B) : ‖a * b - c * d‖ ≤ 2 * B * S := by
  have e : a * b - c * d = (a - c) * b + c * (b - d) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have hS : 0 ≤ S := (norm_nonneg _).trans h1
  nlinarith [mul_le_mul h1 hb (norm_nonneg _) hS, mul_le_mul hc h2 (norm_nonneg _) hB]

/-- The trace row at `k = 1`: `𝓛m_1(M) − 𝓛m_1(A) = −(3 + M_2)(M_1 − A_1)` when `A_1 = 0`. -/
private lemma cm_tau_one (M A : ℤ → ℂ) (hA1 : A 1 = 0) :
    cmTau 1 M - cmTau 1 A = -(3 + M 2) * (M 1 - A 1) := by
  simp only [cmTau, Nat.sub_self, Finset.range_zero, Finset.sum_empty]
  rw [show Finset.Icc 1 (1 + 1) = {1, 2} by decide, Finset.sum_pair (by norm_num)]
  norm_num
  rw [hA1]
  ring

/-- The trace row for `k ≥ 2`: the diagonal coefficient is `3k + (k/2)(M_2 + A_2)`, and the rest
is bounded by the lower deviations. -/
private lemma cm_tau_diff {k : ℕ} (hk : 2 ≤ k) (M A : ℤ → ℂ) {B S : ℝ} (hB : 0 ≤ B)
    (hM : ∀ j : ℤ, 0 ≤ j → j ≤ k + 1 → ‖M j‖ ≤ B) (hA : ∀ j : ℤ, 0 ≤ j → j ≤ k + 1 → ‖A j‖ ≤ B)
    (hA1 : A 1 = 0) (hY : ∀ j : ℤ, 0 ≤ j → j < k → ‖M j - A j‖ ≤ S) :
    ‖cmTau k M - cmTau k A +
        (3 * (k : ℂ) + (k : ℂ) / 2 * (M 2 + A 2)) * (M k - A k)‖ ≤ 10 * k ^ 2 * B * S := by
  have hS : 0 ≤ S := (norm_nonneg _).trans (hY 0 le_rfl (by omega))
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  -- the products `M_a M_b − A_a A_b` with `0 ≤ a, b < k`
  have hpr : ∀ (s : Finset ℕ) (e : ℕ → ℤ), s.card ≤ k → (∀ a ∈ s, a < k ∧ 0 ≤ e a ∧ e a < k) →
      ‖∑ a ∈ s, (M a * M (e a) - A a * A (e a))‖ ≤ k * (2 * B * S) := fun s e hs he =>
    cm_norm_sum_le (by positivity) hs fun a ha => by
      obtain ⟨h1, h2, h3⟩ := he a ha
      exact cm_prod_diff (hM _ h2 (by omega)) (hA _ (by omega) (by omega))
        (hY _ (by omega) (by omega)) (hY _ h2 h3) hB
  have h1 := hpr (Finset.Icc 1 (k - 1)) (fun a => (k : ℤ) - a) (by simp) fun a ha => by
    simp only [Finset.mem_Icc] at ha; omega
  have h2 := hpr (Finset.range (k - 1)) (fun a => (k : ℤ) - 2 - a) (by simp) fun a ha => by
    simp only [Finset.mem_range] at ha; omega
  -- the third sum, split into `Y_a M_{k+2−a}` and `A_a Y_{k+2−a}`
  set s := Finset.Icc 1 (k + 1) with hs
  set f : ℕ → ℂ := fun a => (M a - A a) * M ((k : ℤ) + 2 - a) with hf
  set g : ℕ → ℂ := fun a => A a * (M ((k : ℤ) + 2 - a) - A ((k : ℤ) + 2 - a)) with hg
  have hsplit : ∑ a ∈ s, M a * M ((k : ℤ) + 2 - a) - ∑ a ∈ s, A a * A ((k : ℤ) + 2 - a) =
      ∑ a ∈ s, f a + ∑ a ∈ s, g a := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by simp only [hf, hg]; ring
  rw [← Finset.add_sum_erase _ f (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩ : k + 1 ∈ s),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr
      ⟨by omega, by omega⟩⟩ : k ∈ s.erase (k + 1)),
    ← Finset.add_sum_erase _ g (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩ : 1 ∈ s),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr
      ⟨by omega, by omega⟩⟩ : 2 ∈ s.erase 1)] at hsplit
  have hfk : f k = (M k - A k) * M 2 := by simp only [hf]; congr 2; ring
  have hg1 : g 1 = 0 := by simp [hg, hA1]
  have hg2 : g 2 = A 2 * (M k - A k) := by simp only [hg]; congr 3 <;> push_cast <;> ring
  rw [hfk, hg1, hg2] at hsplit
  have hmain : cmTau k M - cmTau k A + (3 * (k : ℂ) + (k : ℂ) / 2 * (M 2 + A 2)) * (M k - A k) =
      -(3 * (k : ℂ)) * ∑ a ∈ Finset.Icc 1 (k - 1), (M a * M ((k : ℤ) - a) - A a * A ((k : ℤ) - a)) -
        (k : ℂ) / 2 * ∑ a ∈ Finset.range (k - 1),
          (M a * M ((k : ℤ) - 2 - a) - A a * A ((k : ℤ) - 2 - a)) -
        (k : ℂ) / 2 * (f (k + 1) + ∑ a ∈ (s.erase (k + 1)).erase k, f a +
          ∑ a ∈ (s.erase 1).erase 2, g a) := by
    simp only [cmTau, Finset.sum_sub_distrib]
    rw [← hs]
    linear_combination (-(k : ℂ) / 2) * hsplit
  rw [hmain]
  -- the bounds
  have hcard : ∀ a b : ℕ, ((s.erase a).erase b).card ≤ k + 1 := fun a b =>
    Finset.card_erase_le.trans (Finset.card_erase_le.trans (by simp [hs]))
  have hfr : ‖∑ a ∈ (s.erase (k + 1)).erase k, f a‖ ≤ (k + 1 : ℕ) * (B * S) :=
    cm_norm_sum_le (by positivity) (hcard _ _) fun a ha => by
      simp only [hs, Finset.mem_erase, Finset.mem_Icc] at ha
      rw [hf, norm_mul, mul_comm B S]
      exact mul_le_mul (hY _ (by omega) (by omega)) (hM _ (by omega) (by omega)) (norm_nonneg _) hS
  have hgr : ‖∑ a ∈ (s.erase 1).erase 2, g a‖ ≤ (k + 1 : ℕ) * (B * S) :=
    cm_norm_sum_le (by positivity) (hcard _ _) fun a ha => by
      simp only [hs, Finset.mem_erase, Finset.mem_Icc] at ha
      rw [hg, norm_mul]
      exact mul_le_mul (hA _ (by omega) (by omega)) (hY _ (by omega) (by omega)) (norm_nonneg _) hB
  have hfk1 : ‖f (k + 1)‖ ≤ 2 * B * S := by
    simp only [hf, norm_mul, show ((k : ℤ) + 2 - ((k + 1 : ℕ) : ℤ)) = 1 by push_cast; ring]
    have h3 := hM ((k + 1 : ℕ) : ℤ) (by omega) (by push_cast; omega)
    have h4 := hA ((k + 1 : ℕ) : ℤ) (by omega) (by push_cast; omega)
    exact mul_le_mul ((norm_sub_le _ _).trans (by linarith))
      (by simpa [hA1] using hY 1 (by omega) (by omega)) (norm_nonneg _) (by positivity)
  have h3 := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add hfk1 hfr)) hgr)
  refine (norm_sub_le _ _).trans ((add_le_add (norm_sub_le _ _) le_rfl).trans ?_)
  rw [norm_mul, norm_mul, norm_mul, show ‖(k : ℂ) / 2‖ = k / 2 by simp,
    show ‖-(3 * (k : ℂ))‖ = 3 * k by simp]
  have hBS : 0 ≤ B * S := mul_nonneg hB hS
  push_cast at h3 ⊢
  have hk' : (0 : ℝ) ≤ k := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 3 * k),
    mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ k / 2),
    mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ k / 2), mul_nonneg hk' hBS,
    mul_nonneg (mul_nonneg hk' hk') hBS]

/-- The corner row: the diagonal coefficient is `3k + k M_2`; the rest is bounded by the lower
`|F_j|` and by `|M_{±1}|`. -/
private lemma cm_corner_diff {k : ℕ} (hk : 1 ≤ k) (M F : ℤ → ℂ) {B SF : ℝ} (hB : 1 ≤ B)
    (hSF : 0 ≤ SF) (hM : ∀ j : ℤ, -1 ≤ j → j ≤ k + 1 → ‖M j‖ ≤ B)
    (hF : ∀ j : ℤ, -1 ≤ j → j ≤ k + 1 → ‖F j‖ ≤ B) (hY : ∀ j : ℤ, 1 ≤ j → j < k → ‖F j‖ ≤ SF) :
    ‖cmCorner k M F + (3 * (k : ℂ) + (k : ℂ) * M 2) * F k‖ ≤
      11 * ((k + 1) ^ 2 * B ^ 2) * (SF + ‖M 1‖ + ‖M (-1)‖) := by
  set P : ℝ := (k + 1) ^ 2 * B ^ 2 with hP
  set Xs : ℝ := SF + ‖M 1‖ + ‖M (-1)‖ with hXs
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hB0 : 0 ≤ B := by linarith
  have hPk : (k + 1 : ℝ) * k * B ≤ P := by
    rw [hP]; nlinarith [mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ (k + 1) * k * B)]
  have hPB : B ^ 2 ≤ P := by
    rw [hP]; nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ k * (k + 2)) (sq_nonneg B)]
  have hX0 : SF ≤ Xs := by rw [hXs]; linarith [norm_nonneg (M 1), norm_nonneg (M (-1))]
  have hX1 : ‖M 1‖ + ‖M (-1)‖ ≤ Xs := by rw [hXs]; linarith
  have hkk : (k : ℝ) * B ≤ (k + 1) * k * B := by
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ k) hB0]
  -- the lower terms `n F_n M_j`, `1 ≤ n < k`, and their sums
  have hsum : ∀ (s : Finset ℕ) (e : ℕ → ℤ), s.card ≤ k + 1 →
      (∀ n ∈ s, 1 ≤ n ∧ n < k ∧ -1 ≤ e n ∧ e n ≤ k + 1) →
      ‖∑ n ∈ s, (n : ℂ) * F n * M (e n)‖ ≤ P * Xs := by
    intro s e hs he
    refine (cm_norm_sum_le (c := k * B * SF) (by positivity) hs fun n hn => ?_).trans ?_
    · obtain ⟨h1, h2, h3, h4⟩ := he n hn
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      have hnR : (n : ℝ) ≤ k := by exact_mod_cast h2.le
      calc (n : ℝ) * ‖F n‖ * ‖M (e n)‖ ≤ k * SF * B := by
            gcongr; exacts [hY n (by omega) (by omega), hM _ h3 h4]
        _ = k * B * SF := by ring
    · push_cast
      calc ((k : ℝ) + 1) * (k * B * SF) = (k + 1) * k * B * SF := by ring
        _ ≤ P * Xs := mul_le_mul hPk hX0 hSF (by positivity)
  set s := Finset.Icc 1 (k + 1) with hs
  set h : ℕ → ℂ := fun n => (n : ℂ) * F n * M ((k : ℤ) + 2 - n) with hh
  have hk1 : k + 1 ∈ s := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  have hkk' : k ∈ s.erase (k + 1) :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  have hhk : h k = (k : ℂ) * F k * M 2 := by simp only [hh]; congr 2; ring
  have hmain : cmCorner k M F + (3 * (k : ℂ) + (k : ℂ) * M 2) * F k =
      -(if 3 ≤ k then ((k : ℂ) - 2) * F ((k : ℤ) - 2) else 0) - h (k + 1) -
        ∑ n ∈ (s.erase (k + 1)).erase k, h n -
        6 * ∑ n ∈ Finset.Icc 1 (k - 1), (n : ℂ) * F n * M ((k : ℤ) - n) -
        ∑ n ∈ Finset.Icc 1 (k - 3), (n : ℂ) * F n * M ((k : ℤ) - 2 - n) +
        F k * (M 1 * F 1 + M (-1) * F (-1)) := by
    have e : ∑ n ∈ Finset.Icc 1 (k + 1), (n : ℂ) * F n * M ((k : ℤ) + 2 - n) =
        h (k + 1) + h k + ∑ n ∈ (s.erase (k + 1)).erase k, h n := by
      rw [← Finset.add_sum_erase _ _ hk1, ← Finset.add_sum_erase _ _ hkk']; ring
    simp only [cmCorner]
    rw [e, hhk]
    ring
  rw [hmain]
  -- the remaining pieces
  have b1 : ‖(if 3 ≤ k then ((k : ℂ) - 2) * F ((k : ℤ) - 2) else 0)‖ ≤ P * Xs := by
    split_ifs with h3
    · have h3R : (3 : ℝ) ≤ k := by exact_mod_cast h3
      rw [norm_mul, show (k : ℂ) - 2 = ((k - 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
      have hF2 := hY ((k : ℤ) - 2) (by omega) (by omega)
      have : (k : ℝ) ≤ P := by nlinarith
      nlinarith [mul_le_mul (by linarith : (k : ℝ) - 2 ≤ k) hF2 (norm_nonneg _) (by positivity),
        mul_le_mul this hX0 hSF (by positivity)]
    · simp; positivity
  have b2 : ‖h (k + 1)‖ ≤ P * Xs := by
    simp only [hh, norm_mul, show ((k : ℤ) + 2 - ((k + 1 : ℕ) : ℤ)) = 1 by push_cast; ring,
      Complex.norm_natCast]
    have := hF ((k : ℤ) + 1) (by omega) le_rfl
    have hk1B : (k + 1 : ℝ) * B ≤ (k + 1) * k * B := by
      nlinarith [mul_le_mul_of_nonneg_left hkR (by positivity : (0 : ℝ) ≤ (k + 1) * B)]
    calc ((k + 1 : ℕ) : ℝ) * ‖F ((k + 1 : ℕ) : ℤ)‖ * ‖M 1‖ ≤ (k + 1 : ℝ) * B * Xs := by
          push_cast; gcongr; linarith [norm_nonneg (M (-1))]
      _ ≤ P * Xs := mul_le_mul_of_nonneg_right (hPk.trans' hk1B) (hSF.trans hX0)
  have b6 : ‖F k * (M 1 * F 1 + M (-1) * F (-1))‖ ≤ P * Xs := by
    rw [norm_mul]
    have e2 : ‖M 1 * F 1 + M (-1) * F (-1)‖ ≤ B * (‖M 1‖ + ‖M (-1)‖) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      nlinarith [mul_le_mul_of_nonneg_left (hF 1 (by omega) (by omega)) (norm_nonneg (M 1)),
        mul_le_mul_of_nonneg_left (hF (-1) le_rfl (by omega)) (norm_nonneg (M (-1)))]
    calc ‖F k‖ * ‖M 1 * F 1 + M (-1) * F (-1)‖ ≤ B * (B * (‖M 1‖ + ‖M (-1)‖)) := by
          gcongr; exact hF k (by omega) (by omega)
      _ = B ^ 2 * (‖M 1‖ + ‖M (-1)‖) := by ring
      _ ≤ P * Xs := mul_le_mul hPB hX1 (by positivity) (by positivity)
  have b3 : ‖∑ n ∈ (s.erase (k + 1)).erase k, h n‖ ≤ P * Xs := hsum _ (fun n => (k : ℤ) + 2 - n)
    ((Finset.card_erase_le).trans (Finset.card_erase_le.trans (by simp [hs]))) fun n hn => by
      simp only [hs, Finset.mem_erase, Finset.mem_Icc] at hn; omega
  have b4 := hsum (Finset.Icc 1 (k - 1)) (fun n => (k : ℤ) - n) (by simp; omega) fun n hn => by
    simp only [Finset.mem_Icc] at hn; omega
  have b5 := hsum (Finset.Icc 1 (k - 3)) (fun n => (k : ℤ) - 2 - n) (by simp; omega)
    fun n hn => by simp only [Finset.mem_Icc] at hn; omega
  calc _ ≤ ‖(if 3 ≤ k then ((k : ℂ) - 2) * F ((k : ℤ) - 2) else 0)‖ + ‖h (k + 1)‖ +
        ‖∑ n ∈ (s.erase (k + 1)).erase k, h n‖ +
        6 * ‖∑ n ∈ Finset.Icc 1 (k - 1), (n : ℂ) * F n * M ((k : ℤ) - n)‖ +
        ‖∑ n ∈ Finset.Icc 1 (k - 3), (n : ℂ) * F n * M ((k : ℤ) - 2 - n)‖ +
        ‖F k * (M 1 * F 1 + M (-1) * F (-1))‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_sub_le _ _).trans (add_le_add ?_ (by rw [norm_mul]; norm_num))
        refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
        exact (norm_sub_le _ _).trans (add_le_add (by rw [norm_neg]) le_rfl)
    _ ≤ P * Xs + P * Xs + P * Xs + 6 * (P * Xs) + P * Xs + P * Xs := by gcongr
    _ = 11 * P * Xs := by ring

/-! ### The contraction factor and the parameters `h_θ`, `λ_k` -/

/-- `|1 − s t d| ≤ 1 − t/8` for `Re d ≥ 1`, `|d| ≤ D`, `1/4 ≤ s ≤ 1`, `t D² ≤ 1`. -/
private lemma cm_contract {d : ℂ} {D s t : ℝ} (hRe : 1 ≤ d.re) (hD : ‖d‖ ≤ D) (hs1 : 1 / 4 ≤ s)
    (hs2 : s ≤ 1) (ht0 : 0 ≤ t) (htD : t * D ^ 2 ≤ 1) :
    ‖1 - ((s * t : ℝ) : ℂ) * d‖ ≤ 1 - t / 8 := by
  set x := s * t with hx
  have hd1 : 1 ≤ ‖d‖ := hRe.trans (Complex.re_le_norm d)
  have hD1 : 1 ≤ D := hd1.trans hD
  have hD2 : 1 ≤ D ^ 2 := one_le_pow₀ hD1
  have ht1 : t ≤ 1 := by nlinarith
  have hx0 : 0 ≤ x := by positivity
  have hxt : x ≤ t := by nlinarith
  have hxt' : t / 4 ≤ x := by nlinarith
  have hxD : x * ‖d‖ ^ 2 ≤ 1 := by
    have : ‖d‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hD 2
    nlinarith [mul_le_mul hxt this (sq_nonneg _) ht0]
  have hsq : ‖1 - (x : ℂ) * d‖ ^ 2 ≤ (1 - x / 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hn : ‖d‖ ^ 2 = d.re * d.re + d.im * d.im := by
      rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_im, Complex.one_im, Complex.mul_im, zero_mul, sub_zero,
      zero_sub]
    nlinarith [mul_le_mul_of_nonneg_left hxD hx0, mul_le_mul_of_nonneg_left hRe hx0]
  have h1 : 0 ≤ 1 - x / 2 := by linarith
  have := (pow_le_pow_iff_left₀ (norm_nonneg _) h1 two_ne_zero).mp hsq
  linarith

private lemma cm_normalH_bounds {E : ℝ} (hE : |E| ≤ 1) :
    1 / 4 ≤ normalH E ^ 2 ∧ normalH E ^ 2 ≤ 1 := by
  unfold normalH
  rw [freeAngle, Real.sin_arccos]
  have h1 : (E / 2) ^ 2 ≤ 1 / 4 := by
    rw [div_pow]
    nlinarith [sq_abs E, abs_nonneg E]
  have h2 : 1 / 2 ≤ √(1 - (E / 2) ^ 2) := by
    rw [show (1 : ℝ) / 2 = √((1 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have h3 : √(1 - (E / 2) ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg (E / 2)])
  have hpos : 0 < 2 * √(1 - (E / 2) ^ 2) := by linarith
  rw [inv_pow]
  constructor
  · rw [le_inv_comm₀ (by norm_num) (by positivity)]
    nlinarith
  · rw [inv_le_one₀ (by positivity)]
    nlinarith

private lemma cm_norm_lam (E : ℝ) (k : ℤ) : ‖(-normalPhase E) ^ k‖ = 1 := by
  rw [norm_zpow, norm_neg, normalPhase, norm_neg,
    show (2 : ℂ) * (freeAngle E * Complex.I) = ((2 * freeAngle E : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_zpow]

/-! ### One step of the conditional moments -/

private lemma cm_continuous {W : ℕ} (g E : ℝ) {X : State W} (hX : IsState X) (q : ObsPoly) :
    Continuous fun ω : Ω W 1 => obsEval g (stepState g E X (gueBlock W 1 ω 0)) q := by
  rw [show (fun ω : Ω W 1 => obsEval g (stepState g E X (gueBlock W 1 ω 0)) q) = fun ω =>
      eval (fun v => obsEval g (stepState g E X (gueBlock W 1 ω 0)) (MvPolynomial.X v)) q from
    funext fun ω => by
      conv_lhs => rw [MvPolynomial.aeval_unique (obsEval g _)]
      rfl]
  refine (MvPolynomial.continuous_eval q).comp (continuous_pi fun v => ?_)
  cases v with
  | m k => simpa [obsEval] using (contDiff_obsM_stepState g E hX k.1).continuous
  | f k => simpa [obsEval] using (contDiff_obsF_stepState g E hX k.1).continuous
  | w => simpa [obsEval] using continuous_const
  | γ => simpa [obsEval] using continuous_const

/-- The conditional moment of order `2p` of a polynomial observable, expanded around its
conditional mean (proof of (11.59) [lg:eq:momentrec]). -/
private lemma cm_moment (p : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {W : ℕ}, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, ∀ X : State W, IsState X →
      ∀ (q : ObsPoly) (a : ℂ),
        transOp g E (fun Y => ‖obsEval g Y q - a‖ ^ (2 * p)) X ≤
          ‖transOp g E (fun Y => obsEval g Y q) X - a‖ ^ (2 * p) +
            K * (‖transOp g E (fun Y => obsEval g Y q) X - a‖ ^ (2 * p - 2) *
              ∫ ω, ‖obsEval g (stepState g E X (gueBlock W 1 ω 0)) q -
                transOp g E (fun Y => obsEval g Y q) X‖ ^ (2 * 1) ∂(μ W 1) +
              ∫ ω, ‖obsEval g (stepState g E X (gueBlock W 1 ω 0)) q -
                transOp g E (fun Y => obsEval g Y q) X‖ ^ (2 * p) ∂(μ W 1)) := by
  obtain ⟨Kp, hKp, hmom⟩ := integral_norm_add_pow_le p
  refine ⟨Kp * (2 * p + 1), by positivity, fun {W} hW g hg E X hX q a => ?_⟩
  set F : Ω W 1 → ℂ := fun ω => obsEval g (stepState g E X (gueBlock W 1 ω 0)) q with hF
  set m : ℂ := transOp g E (fun Y => obsEval g Y q) X with hm
  have hFc : Continuous F := cm_continuous g E hX q
  have hFb : ∀ ω, ‖F ω‖ ≤ ∑ d ∈ q.support, ‖q.coeff d‖ := fun ω =>
    norm_obsEval_le hW hg (isState_stepState g E hX (gueBlock_isHermitian W 1 ω 0)) q
  set Bq := ∑ d ∈ q.support, ‖q.coeff d‖
  have hm' : m = ∫ ω, F ω ∂(μ W 1) := rfl
  set ξ : Ω W 1 → ℂ := fun ω => F ω - m with hξ
  have hξc : Continuous ξ := hFc.sub continuous_const
  have hξb : ∀ ω, ‖ξ ω‖ ≤ Bq + ‖m‖ := fun ω => (norm_sub_le _ _).trans (add_le_add (hFb ω) le_rfl)
  have hFi : Integrable F (μ W 1) :=
    Integrable.of_bound hFc.aestronglyMeasurable Bq (Filter.Eventually.of_forall hFb)
  have hξi : Integrable ξ (μ W 1) := hFi.sub (integrable_const m)
  have hξpow : ∀ j : ℕ, Integrable (fun ω => ‖ξ ω‖ ^ j) (μ W 1) := fun j =>
    Integrable.of_bound ((continuous_norm.comp hξc).pow j).aestronglyMeasurable
      ((Bq + ‖m‖) ^ j) (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hξb ω) j)
  have hξ0 : ∫ ω, ξ ω ∂(μ W 1) = 0 := by
    rw [integral_sub hFi (integrable_const m), integral_const, ← hm']; simp
  have h1 := hmom (μ W 1) (m - a) ξ hξi hξ0 (fun j _ => hξpow j)
  have hL : transOp g E (fun Y => ‖obsEval g Y q - a‖ ^ (2 * p)) X =
      ∫ ω, ‖(m - a) + ξ ω‖ ^ (2 * p) ∂(μ W 1) := by
    unfold transOp
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      simp only [hξ, hF]; congr 2; ring)
  rw [hL]
  refine h1.trans (add_le_add le_rfl ?_)
  set A := ‖m - a‖
  set I2 := ∫ ω, ‖ξ ω‖ ^ (2 * 1) ∂(μ W 1)
  set In := ∫ ω, ‖ξ ω‖ ^ (2 * p) ∂(μ W 1)
  have hI2 : 0 ≤ I2 := integral_nonneg fun _ => by positivity
  have hIn : 0 ≤ In := integral_nonneg fun _ => by positivity
  have hterm : ∀ j ∈ Finset.Icc 2 (2 * p), A ^ (2 * p - j) * ∫ ω, ‖ξ ω‖ ^ j ∂(μ W 1) ≤
      A ^ (2 * p - 2) * I2 + In := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    rw [← integral_const_mul, show A ^ (2 * p - 2) * I2 =
      ∫ ω, A ^ (2 * p - 2) * ‖ξ ω‖ ^ (2 * 1) ∂(μ W 1) from (integral_const_mul _ _).symm,
      ← integral_add ((hξpow _).const_mul _) (hξpow _)]
    refine integral_mono ((hξpow _).const_mul _) (((hξpow _).const_mul _).add (hξpow _))
      fun ω => ?_
    simpa using cm_mix (n := 2 * p) hj1 hj2 (norm_nonneg (m - a)) (norm_nonneg (ξ ω))
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at hsum
  have hc : ((2 * p + 1 - 2 : ℕ) : ℝ) ≤ 2 * p + 1 := by exact_mod_cast Nat.sub_le (2 * p + 1) 2
  have := mul_le_mul_of_nonneg_left (hsum.trans (mul_le_mul_of_nonneg_right hc
    (by positivity : 0 ≤ A ^ (2 * p - 2) * I2 + In))) hKp.le
  linarith

/-! ### Closing one row -/

/-- `(a + b + c + d + e)^n ≤ 5^{n−1}(a^n + b^n + c^n + d^n + e^n)`. -/
private lemma cm_pow5 {n : ℕ} (hn : 1 ≤ n) {a b c d e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) :
    (a + b + c + d + e) ^ n ≤ 5 ^ (n - 1) * (a ^ n + b ^ n + c ^ n + d ^ n + e ^ n) := by
  have h := cm_pow_sum (Finset.univ : Finset (Fin 5)) (f := ![a, b, c, d, e])
    (fun i _ => by fin_cases i <;> simp [ha, hb, hc, hd, he]) hn
  simp [Fin.sum_univ_five] at h
  simpa [add_assoc] using h

/-- One row of (11.59) [lg:eq:momentrec]: the conditional moment bound, the innovation bounds and
the contraction of the conditional mean give the recursion for `|Y|^{2p}`. -/
private lemma cm_row {p : ℕ} (hp : 1 ≤ p) {t ω P μ Y Km K1 K2 I2 In b₁ b₂ b₃ b₄ b₅ : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) (hω : 0 ≤ ω) (hμ0 : 0 ≤ μ) (hY : 0 ≤ Y) (hKm : 0 ≤ Km)
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃) (hb₄ : 0 ≤ b₄)
    (hb₅ : 0 ≤ b₅)
    (hP : P ≤ μ ^ (2 * p) + Km * (μ ^ (2 * p - 2) * I2 + In)) (hI2 : I2 ≤ K1 * (t * ω))
    (hIn : In ≤ K2 * (t * ω) ^ p) (hμ : μ ≤ (1 - t / 8) * Y + t * (b₁ + b₂ + b₃ + b₄ + b₅)) :
    P ≤ (1 - t / 32) * Y ^ (2 * p) +
      t * (2 * 16 ^ (2 * p - 1) * 5 ^ (2 * p - 1) *
          (b₁ ^ (2 * p) + b₂ ^ (2 * p) + b₃ ^ (2 * p) + b₄ ^ (2 * p) + b₅ ^ (2 * p)) +
        (32 ^ (p - 1) * (Km * K1) ^ p + Km * K2) * ω ^ p) := by
  have hn : 1 ≤ 2 * p := by omega
  set β := b₁ + b₂ + b₃ + b₄ + b₅ with hβ
  have hβ0 : 0 ≤ β := by positivity
  -- the innovation terms
  have hμ2 : μ ^ (2 * p - 2) = (μ ^ 2) ^ (p - 1) := by
    rw [← pow_mul]; congr 1; omega
  have hμ2' : μ ^ (2 * p) = (μ ^ 2) ^ p := by rw [← pow_mul]
  have hI2' : 0 ≤ μ ^ (2 * p - 2) := by positivity
  have hyoung := cm_young hp (sq_nonneg μ) (by positivity : 0 ≤ Km * K1 * ω)
    (by norm_num : (0 : ℝ) < 1 / 32)
  have htp : t ^ p ≤ t := by
    calc t ^ p ≤ t ^ 1 := pow_le_pow_of_le_one ht0.le ht1 hp
      _ = t := pow_one t
  have hωp : 0 ≤ ω ^ p := by positivity
  have hInn : Km * In ≤ Km * K2 * t * ω ^ p := by
    have : In ≤ K2 * t * ω ^ p := by
      rw [mul_pow] at hIn
      calc In ≤ K2 * (t ^ p * ω ^ p) := hIn
        _ ≤ K2 * (t * ω ^ p) := by gcongr
        _ = K2 * t * ω ^ p := by ring
    calc Km * In ≤ Km * (K2 * t * ω ^ p) := mul_le_mul_of_nonneg_left this hKm
      _ = Km * K2 * t * ω ^ p := by ring
  have hI2n : Km * (μ ^ (2 * p - 2) * I2) ≤
      t * (1 / 32 * μ ^ (2 * p) + 32 ^ (p - 1) * (Km * K1) ^ p * ω ^ p) := by
    have h1 : Km * (μ ^ (2 * p - 2) * I2) ≤ t * ((μ ^ 2) ^ (p - 1) * (Km * K1 * ω)) := by
      rw [hμ2] at hI2' ⊢
      calc Km * ((μ ^ 2) ^ (p - 1) * I2) ≤ Km * ((μ ^ 2) ^ (p - 1) * (K1 * (t * ω))) := by
            gcongr
        _ = t * ((μ ^ 2) ^ (p - 1) * (Km * K1 * ω)) := by ring
    refine h1.trans (mul_le_mul_of_nonneg_left (hyoung.trans (le_of_eq ?_)) ht0.le)
    rw [hμ2', one_div, inv_pow, div_inv_eq_mul, mul_pow, mul_pow]
    ring
  have hP' : P ≤ (1 + t / 32) * μ ^ (2 * p) + t * ((32 ^ (p - 1) * (Km * K1) ^ p + Km * K2) *
      ω ^ p) := by
    have := hP.trans (add_le_add le_rfl ((mul_add Km _ _).le.trans (add_le_add hI2n hInn)))
    linarith
  -- the contraction
  have hsplit := cm_split hn hY hβ0 ht0.le ht1
  have hμp : μ ^ (2 * p) ≤ ((1 - t / 8) * Y + t * β) ^ (2 * p) := pow_le_pow_left₀ hμ0 hμ _
  have hβp := cm_pow5 hn hb₁ hb₂ hb₃ hb₄ hb₅
  have h16 : (0 : ℝ) ≤ 16 ^ (2 * p - 1) := by positivity
  have hY2 : 0 ≤ Y ^ (2 * p) := by positivity
  have hm : μ ^ (2 * p) ≤ (1 - t / 16) * Y ^ (2 * p) +
      t * (16 ^ (2 * p - 1) * 5 ^ (2 * p - 1) *
        (b₁ ^ (2 * p) + b₂ ^ (2 * p) + b₃ ^ (2 * p) + b₄ ^ (2 * p) + b₅ ^ (2 * p))) := by
    refine hμp.trans (hsplit.trans (add_le_add le_rfl ?_))
    have := mul_le_mul_of_nonneg_left hβp (mul_nonneg h16 ht0.le)
    calc 16 ^ (2 * p - 1) * t * β ^ (2 * p) =
          16 ^ (2 * p - 1) * t * (b₁ + b₂ + b₃ + b₄ + b₅) ^ (2 * p) := by rw [hβ]
      _ ≤ 16 ^ (2 * p - 1) * t * (5 ^ (2 * p - 1) *
          (b₁ ^ (2 * p) + b₂ ^ (2 * p) + b₃ ^ (2 * p) + b₄ ^ (2 * p) + b₅ ^ (2 * p))) := this
      _ = _ := by ring
  set Bs := 16 ^ (2 * p - 1) * 5 ^ (2 * p - 1) *
    (b₁ ^ (2 * p) + b₂ ^ (2 * p) + b₃ ^ (2 * p) + b₄ ^ (2 * p) + b₅ ^ (2 * p)) with hBs
  have hBs0 : 0 ≤ Bs := by positivity
  have h1 : (1 + t / 32) * μ ^ (2 * p) ≤ (1 - t / 32) * Y ^ (2 * p) + t * (2 * Bs) := by
    have e2 : (1 + t / 32) * (1 - t / 16) ≤ 1 - t / 32 := by nlinarith
    have e3 : 1 + t / 32 ≤ 2 := by linarith
    have htB : 0 ≤ t * Bs := mul_nonneg ht0.le hBs0
    calc (1 + t / 32) * μ ^ (2 * p) ≤ (1 + t / 32) * ((1 - t / 16) * Y ^ (2 * p) + t * Bs) :=
          mul_le_mul_of_nonneg_left hm (by positivity)
      _ = (1 + t / 32) * (1 - t / 16) * Y ^ (2 * p) + (1 + t / 32) * (t * Bs) := by ring
      _ ≤ (1 - t / 32) * Y ^ (2 * p) + 2 * (t * Bs) :=
          add_le_add (mul_le_mul_of_nonneg_right e2 hY2) (mul_le_mul_of_nonneg_right e3 htB)
      _ = (1 - t / 32) * Y ^ (2 * p) + t * (2 * Bs) := by ring
  have e4 : 2 * 16 ^ (2 * p - 1) * 5 ^ (2 * p - 1) *
      (b₁ ^ (2 * p) + b₂ ^ (2 * p) + b₃ ^ (2 * p) + b₄ ^ (2 * p) + b₅ ^ (2 * p)) = 2 * Bs := by
    rw [hBs]; ring
  rw [e4]
  linarith

/-! ### Weights -/

/-- Weights decreasing in `|k|` absorb the couplings to lower indices. -/
private lemma cm_weights (J : Finset NzInt) {f P : NzInt → ℝ} (hf : ∀ k, 0 ≤ f k)
    {c₀ C t Sl : ℝ} (hc₀ : 0 < c₀) (hC : 0 ≤ C) (ht : 0 ≤ t) (hSl : 0 ≤ Sl)
    (hrow : ∀ k ∈ J, P k ≤ (1 - c₀ * t) * f k +
      t * (C * ∑ j ∈ J.filter (fun j => j.1.natAbs < k.1.natAbs), f j + Sl)) :
    ∑ k ∈ J, ((1 + 2 * C * J.card / c₀)⁻¹) ^ k.1.natAbs * P k ≤
      (1 - c₀ / 2 * t) * ∑ k ∈ J, ((1 + 2 * C * J.card / c₀)⁻¹) ^ k.1.natAbs * f k +
        t * (J.card * Sl) := by
  set β := 1 + 2 * C * J.card / c₀ with hβ
  have hβ1 : 1 ≤ β := le_add_of_nonneg_right (by positivity)
  have hb1 : β⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hβ1
  set u : NzInt → ℝ := fun k => (β⁻¹) ^ k.1.natAbs with hu
  have hu0 : ∀ k, 0 ≤ u k := fun k => by positivity
  -- the couplings to lower indices
  have hsw : C * ∑ k ∈ J, u k * ∑ j ∈ J.filter (fun j => j.1.natAbs < k.1.natAbs), f j ≤
      c₀ / 2 * ∑ k ∈ J, u k * f k := by
    have e : ∑ k ∈ J, u k * ∑ j ∈ J.filter (fun j => j.1.natAbs < k.1.natAbs), f j =
        ∑ j ∈ J, f j * ∑ k ∈ J.filter (fun k => j.1.natAbs < k.1.natAbs), u k := by
      simp only [Finset.sum_filter, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by split_ifs <;> ring
    have hc : C * (J.card * β⁻¹) ≤ c₀ / 2 := by
      rw [← div_eq_mul_inv, mul_div_assoc', div_le_iff₀ (by positivity)]
      have : c₀ / 2 * β = c₀ / 2 + C * J.card := by rw [hβ]; field_simp
      rw [this]; linarith
    rw [e, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have huj := hu0 j
    have hs : ∑ k ∈ J.filter (fun k => j.1.natAbs < k.1.natAbs), u k ≤ J.card * (u j * β⁻¹) := by
      refine (Finset.sum_le_card_nsmul _ _ (u j * β⁻¹) fun k hk => ?_).trans ?_
      · rw [← pow_succ]
        exact pow_le_pow_of_le_one (by positivity) hb1 (Finset.mem_filter.mp hk).2
      · rw [nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_filter_le _ _)
          (by positivity)
    calc C * (f j * ∑ k ∈ J.filter (fun k => j.1.natAbs < k.1.natAbs), u k)
        ≤ C * (f j * (J.card * (u j * β⁻¹))) := by gcongr; exact hf j
      _ = C * (J.card * β⁻¹) * (u j * f j) := by ring
      _ ≤ c₀ / 2 * (u j * f j) := mul_le_mul_of_nonneg_right hc (mul_nonneg (hu0 j) (hf j))
  have h1 : ∑ k ∈ J, u k * P k ≤ ∑ k ∈ J, ((1 - c₀ * t) * (u k * f k) +
      t * (C * (u k * ∑ j ∈ J.filter (fun j => j.1.natAbs < k.1.natAbs), f j)) + t * (u k * Sl)) :=
    Finset.sum_le_sum fun k hk => by nlinarith [mul_le_mul_of_nonneg_left (hrow k hk) (hu0 k)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul] at h1
  have h2 : ∑ k ∈ J, u k ≤ J.card :=
    (Finset.sum_le_card_nsmul _ _ 1 fun k _ => pow_le_one₀ (by positivity) hb1).trans (by simp)
  nlinarith [mul_le_mul_of_nonneg_left hsw ht, mul_le_mul_of_nonneg_left h2 (mul_nonneg ht hSl)]

/-! ### Valuations -/

private lemma cm_aeval_mVar (z : ObsVar → ℂ) (j : ℤ) :
    aeval z (mVar j) = if h : j = 0 then 1 else z (.m ⟨j, h⟩) := by
  unfold mVar; split_ifs <;> simp

private lemma cm_centerEval_eq (g : ℝ) (a : ℤ → ℂ) (q : ObsPoly) :
    centerEval g a q = aeval (fun v => centerEval g a (X v)) q := by
  conv_lhs => rw [MvPolynomial.aeval_unique (centerEval g a)]
  rfl

private lemma cm_aeval_fIdeal {z : ObsVar → ℂ} (hz : ∀ j, z (.f j) = 0) {q : ObsPoly}
    (hq : q ∈ fIdeal) : aeval z q = 0 := by
  refine (show fIdeal ≤ RingHom.ker (aeval z : ObsPoly →ₐ[ℂ] ℂ) from ?_) hq
  rw [fIdeal, Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  simp [hz j]

/-- Rows `−k` and `k` have equal moduli on states. -/
private lemma cm_conj {W : ℕ} (hW : 1 ≤ W) (g E : ℝ) (R : ℕ) {Y : State W} (hY : IsState Y)
    (k : NzInt) :
    ‖obsEval g Y (corrObsM E R ⟨-k.1, neg_ne_zero.mpr k.2⟩) - center g E R (-k.1)‖ =
        ‖obsEval g Y (corrObsM E R k) - center g E R k.1‖ ∧
      ‖obsEval g Y (corrObsF E R ⟨-k.1, neg_ne_zero.mpr k.2⟩)‖ =
        ‖obsEval g Y (corrObsF E R k)‖ := by
  obtain ⟨hM, hF⟩ := conjPoly_corrObs E R k
  rw [← hM, ← hF, obsEval_conjPoly hW g hY, obsEval_conjPoly hW g hY,
    (center_zero_odd_neg g E R k.1).2.2, ← star_sub, norm_star, norm_star]
  exact ⟨rfl, rfl⟩

/-- `λ(Y + h² t τ)` contracts when `τ = −dY + L` with `Re d ≥ 1`. -/
private lemma cm_lead {lam Yk τ d : ℂ} {s t D ℓ : ℝ} (hlam : ‖lam‖ = 1) (hRe : 1 ≤ d.re)
    (hD : ‖d‖ ≤ D) (hs1 : 1 / 4 ≤ s) (hs2 : s ≤ 1) (ht0 : 0 ≤ t) (htD : t * D ^ 2 ≤ 1)
    (hL : ‖τ + d * Yk‖ ≤ ℓ) :
    ‖lam * (Yk + (s : ℂ) * (t : ℂ) * τ)‖ ≤ (1 - t / 8) * ‖Yk‖ + t * ℓ := by
  have e : lam * (Yk + (s : ℂ) * (t : ℂ) * τ) =
      lam * ((1 - ((s * t : ℝ) : ℂ) * d) * Yk + ((s * t : ℝ) : ℂ) * (τ + d * Yk)) := by
    push_cast; ring
  rw [e, norm_mul, hlam, one_mul]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h1 := cm_contract hRe hD hs1 hs2 ht0 htD
  have hst : s * t ≤ t := by nlinarith
  have hℓ : 0 ≤ ℓ := (norm_nonneg _).trans hL
  gcongr

private lemma cm_d_trace {k : ℕ} (hk : 1 ≤ k) {z w : ℂ} (hz : ‖z‖ ≤ 2) (hw : ‖w‖ ≤ 2) :
    1 ≤ (3 * (k : ℂ) + (k : ℂ) / 2 * (z + w)).re ∧
      ‖3 * (k : ℂ) + (k : ℂ) / 2 * (z + w)‖ ≤ 5 * k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hzw : ‖z + w‖ ≤ 4 := (norm_add_le _ _).trans (by linarith)
  have hre : -4 ≤ (z + w).re := by
    have := Complex.abs_re_le_norm (z + w); rw [abs_le] at this; linarith
  constructor
  · simp only [Complex.add_re, Complex.mul_re, Complex.div_re, Complex.natCast_re,
      Complex.natCast_im, Complex.re_ofNat, Complex.im_ofNat]
    norm_num
    have : (k : ℝ) / 2 * (z + w).re ≥ -(2 * k) := by nlinarith
    simp only [Complex.add_re] at this
    nlinarith
  · refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_div]
    simp only [Complex.norm_natCast, Complex.norm_ofNat]
    nlinarith

private lemma cm_d_corner {k : ℕ} (hk : 1 ≤ k) {z : ℂ} (hz : ‖z‖ ≤ 2) :
    1 ≤ (3 * (k : ℂ) + (k : ℂ) * z).re ∧ ‖3 * (k : ℂ) + (k : ℂ) * z‖ ≤ 5 * k := by
  rw [show (k : ℂ) * z = (k : ℂ) / 2 * (z + z) by ring]; exact cm_d_trace hk hz hz

/-- The values `M_j`, `F_j`, `W⁻¹`, `g⁻²` of the corrected coordinates at a state. -/
private def cmX (g E : ℝ) (R : ℕ) {W : ℕ} (X : State W) : ObsVar → ℂ :=
  fun v => obsEval g X (corrCoord E R v)

/-- The values `a_j`, `0`, `0`, `g⁻²` at the centers. -/
private def cmY (g E : ℝ) (R : ℕ) : ObsVar → ℂ := fun v => centerEval g (center g E R) (X v)

private lemma cmX_γ (g E : ℝ) (R : ℕ) {W : ℕ} (X : State W) :
    cmX g E R X .γ = (((g ^ 2)⁻¹ : ℝ) : ℂ) := by
  simp [cmX, cm_corrCoord_γ, obsEval]

private lemma cmX_w (g E : ℝ) (R : ℕ) {W : ℕ} (X : State W) : cmX g E R X .w = (W : ℂ)⁻¹ := by
  simp [cmX, corrCoord, corrCoordAux, corrStep, obsEval]

private lemma cmY_m (g E : ℝ) (R : ℕ) (j : NzInt) : cmY g E R (.m j) = center g E R j.1 := by
  simp [cmY, centerEval]

private lemma cmY_f (g E : ℝ) (R : ℕ) (j : NzInt) : cmY g E R (.f j) = 0 := by
  simp [cmY, centerEval]

private lemma cmY_w (g E : ℝ) (R : ℕ) : cmY g E R .w = 0 := by simp [cmY, centerEval]

private lemma cmY_γ (g E : ℝ) (R : ℕ) : cmY g E R .γ = (((g ^ 2)⁻¹ : ℝ) : ℂ) := by
  simp [cmY, centerEval]

private lemma cm_mVar_Y (g E : ℝ) (R : ℕ) (j : ℤ) :
    aeval (cmY g E R) (mVar j) = center g E R j := by
  rw [cm_aeval_mVar]
  split_ifs with h
  · rw [h, (center_zero_odd_neg g E R 0).1]
  · rw [cmY_m]

private lemma cm_mVar_X (g E : ℝ) (R : ℕ) {W : ℕ} (X : State W) {j : ℤ} (h : j ≠ 0) :
    aeval (cmX g E R X) (mVar j) = obsEval g X (corrObsM E R ⟨j, h⟩) := by
  simp only [cm_aeval_mVar, h, ↓reduceDIte]; rfl

private lemma cm_fVar_X (g E : ℝ) (R : ℕ) {W : ℕ} (X : State W) {j : ℤ} (h : j ≠ 0) :
    aeval (cmX g E R X) (fVar j) = obsEval g X (corrObsF E R ⟨j, h⟩) := by
  simp only [fVar, h, ↓reduceDIte, aeval_X]; rfl

/-- The variables of a finite set of monomials, by index. -/
private def cmIdx : ObsVar → Finset NzInt
  | .m j => {j}
  | .f j => {j}
  | _ => ∅

private lemma cm_center_one (g E : ℝ) (R : ℕ) : center g E R 1 = 0 := by
  simpa using (center_zero_odd_neg g E R 0).2.1

private lemma cm_eval_cmX {W : ℕ} (g E : ℝ) (R : ℕ) (X : State W) (q : ObsPoly) :
    obsEval g X (bind₁ (corrCoord E R) q) = aeval (cmX g E R X) q := by
  unfold obsEval; rw [aeval_bind₁]; rfl

private lemma cm_norm4 (a b c d : ℂ) : ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ :=
  (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)

private lemma cm_H_coeff (U : ObsPoly) (d : ObsVar →₀ ℕ) :
    (U - truncG 1 U).coeff d = if d .γ ≤ 1 then 0 else U.coeff d := by
  rw [coeff_sub, cm_coeff_truncG]; split_ifs <;> simp

private lemma cm_H_support (U : ObsPoly) : (U - truncG 1 U).support ⊆ U.support := fun d hd => by
  rw [mem_support_iff, cm_H_coeff] at hd; rw [mem_support_iff]; split_ifs at hd <;> simp_all

private lemma cm_H_two (U : ObsPoly) : ∀ d ∈ (U - truncG 1 U).support, 2 ≤ d .γ := fun d hd => by
  rw [mem_support_iff, cm_H_coeff] at hd; split_ifs at hd with h <;> simp_all; omega

private lemma cm_slots3 {x₁ x₂ x₃ y₁ y₂ y₃ s₁ s₂ s₃ : ℝ} (h₁ : x₁ ≤ y₁ * s₁) (h₂ : x₂ ≤ y₂ * s₂)
    (h₃ : x₃ ≤ y₃ * s₃) (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) (hy₃ : 0 ≤ y₃) (hs₁ : 0 ≤ s₁)
    (hs₂ : 0 ≤ s₂) (hs₃ : 0 ≤ s₃) : x₁ + x₂ + x₃ ≤ (y₁ + y₂ + y₃) * (s₁ + s₂ + s₃) := by
  nlinarith [mul_nonneg hy₁ hs₂, mul_nonneg hy₁ hs₃, mul_nonneg hy₂ hs₁, mul_nonneg hy₂ hs₃,
    mul_nonneg hy₃ hs₁, mul_nonneg hy₃ hs₂]

private lemma cm_slots4 {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ s₁ s₂ s₃ s₄ : ℝ} (h₁ : x₁ ≤ y₁ * s₁)
    (h₂ : x₂ ≤ y₂ * s₂) (h₃ : x₃ ≤ y₃ * s₃) (h₄ : x₄ ≤ y₄ * s₄) (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂)
    (hy₃ : 0 ≤ y₃) (hy₄ : 0 ≤ y₄) (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂) (hs₃ : 0 ≤ s₃) (hs₄ : 0 ≤ s₄) :
    x₁ + x₂ + x₃ + x₄ ≤ (y₁ + y₂ + y₃ + y₄) * (s₁ + s₂ + s₃ + s₄) := by
  nlinarith [mul_nonneg hy₁ hs₂, mul_nonneg hy₁ hs₃, mul_nonneg hy₁ hs₄, mul_nonneg hy₂ hs₁,
    mul_nonneg hy₂ hs₃, mul_nonneg hy₂ hs₄, mul_nonneg hy₃ hs₁, mul_nonneg hy₃ hs₂,
    mul_nonneg hy₃ hs₄, mul_nonneg hy₄ hs₁, mul_nonneg hy₄ hs₂, mul_nonneg hy₄ hs₃]

private lemma cm_pow_g (g : ℝ) (p : ℕ) : ((g ^ 2)⁻¹) ^ (2 * p) = 1 / g ^ (4 * p) := by
  rw [inv_pow, ← pow_mul, one_div]; congr 2; ring

private lemma cm_pow_gR (g : ℝ) (p R : ℕ) : ((g ^ (2 * R))⁻¹) ^ (2 * p) = 1 / g ^ (4 * p * R) := by
  rw [inv_pow, ← pow_mul, one_div]; congr 2; ring

private lemma cm_pow_W {W : ℝ} (hW : 1 ≤ W) (p a : ℕ) :
    ((W ^ a)⁻¹) ^ (2 * p) ≤ 1 / W ^ (a * p) ∧ ((W ^ a)⁻¹) ^ p = 1 / W ^ (a * p) := by
  have e : ((W ^ a)⁻¹) ^ p = 1 / W ^ (a * p) := by rw [inv_pow, ← pow_mul, one_div]
  refine ⟨?_, e⟩
  rw [inv_pow, ← pow_mul, one_div]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hW (by nlinarith))

private lemma cm_H_coeff_le {U : ObsPoly} {K : ℝ} (hK : 0 ≤ K) (hU : ∀ d, ‖U.coeff d‖ ≤ K) (d) :
    ‖(U - truncG 1 U).coeff d‖ ≤ K := by
  rw [cm_H_coeff]; split_ifs
  · simpa using hK
  · exact hU d

private lemma cm_aeval_lead (z : ObsVar → ℂ) (a b : ℂ) (v : ObsVar) (P : ObsPoly) :
    aeval z (C a * (X v + C b * X .γ * P)) = a * (z v + b * z .γ * aeval z P) := by
  simp

/-- `|M_j − a_j|` at a state. -/
private def cmYv (g E : ℝ) (R : ℕ) {W : ℕ} (X : State W) (j : NzInt) : ℝ :=
  ‖obsEval g X (corrObsM E R j) - center g E R j.1‖

/-- `|F_j|` at a state. -/
private def cmZv (g E : ℝ) (R : ℕ) {W : ℕ} (X : State W) (j : NzInt) : ℝ :=
  ‖obsEval g X (corrObsF E R j)‖

/-- Rows `k` and `|k|` have equal moduli on states. -/
private lemma cm_sym {W : ℕ} (hW : 1 ≤ W) (g E : ℝ) (R : ℕ) {Y : State W} (hY : IsState Y)
    (k : NzInt) : cmYv g E R Y k = cmYv g E R Y ⟨k.1.natAbs, by simpa using k.2⟩ ∧
      cmZv g E R Y k = cmZv g E R Y ⟨k.1.natAbs, by simpa using k.2⟩ := by
  rcases Int.natAbs_eq k.1 with h | h
  · have hk : k = ⟨k.1.natAbs, by simpa using k.2⟩ := Subtype.ext h
    rw [← hk]; exact ⟨rfl, rfl⟩
  · have hk : k = ⟨-((⟨k.1.natAbs, by simpa using k.2⟩ : NzInt).1), neg_ne_zero.mpr
        (⟨k.1.natAbs, by simpa using k.2⟩ : NzInt).2⟩ := Subtype.ext h
    obtain ⟨h1, h2⟩ := cm_conj hW g E R hY ⟨k.1.natAbs, by simpa using k.2⟩
    rw [← hk] at h1 h2
    refine ⟨?_, h2⟩
    unfold cmYv; rw [← h1]; congr 3

/-- `(c Σ_s f)^n ≤ c^n #t^{n−1} Σ_s f^n` for `s ⊆ t`. -/
private lemma cm_bsum {ι : Type*} {s t : Finset ι} (hst : s ⊆ t) {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i)
    {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 1 ≤ n) :
    (c * ∑ i ∈ s, f i) ^ n ≤ c ^ n * (t.card : ℝ) ^ (n - 1) * ∑ i ∈ s, f i ^ n := by
  rw [mul_pow, mul_assoc]
  refine mul_le_mul_of_nonneg_left ((cm_pow_sum s (fun i _ => hf i) hn).trans
    (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun i _ => pow_nonneg (hf i) n)))
    (by positivity)
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Finset.card_le_card hst) _

private lemma cm_final {g A n S K sl : ℝ} (hsl : 0 ≤ sl) (hK : n * S ≤ K) :
    (1 - 1 / 32 / 2 * (g ^ 2)⁻¹) * A + (g ^ 2)⁻¹ * (n * (S * sl)) ≤
      (1 - 1 / 32 / 2 / g ^ 2) * A + K / g ^ 2 * sl := by
  rw [div_eq_mul_inv (1 / 32 / 2), div_eq_mul_inv K]
  nlinarith [mul_le_mul_of_nonneg_right hK (mul_nonneg (inv_nonneg.mpr (sq_nonneg g)) hsl)]

set_option maxHeartbeats 4000000 in -- both rows are assembled in one context
/-- The rows of (11.59) [lg:eq:momentrec] before the weights: each row contracts up to its
couplings to lower rows and the error terms of (11.59) [lg:eq:momentrec]. -/
private lemma cm_rows (R : ℕ) (J : Finset NzInt)
    (hJ : ∀ k ∈ J, ∀ j : NzInt, |j.1| ≤ |k.1| → j ∈ J) {p : ℕ} (hp : 1 ≤ p) :
    ∃ J' : Finset NzInt, J ⊆ J' ∧ ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ CM CF SM SF g₀ : ℝ, 0 ≤ CM ∧ 0 ≤ CF ∧
      0 ≤ SM ∧ 0 ≤ SF ∧ 1 ≤ g₀ ∧ ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, g₀ ≤ g → ∀ E : ℝ, |E| ≤ E₁ →
      ∀ X : State W, IsState X → ∀ k ∈ J,
        transOp g E (fun Y => cmYv g E R Y k ^ (2 * p)) X ≤
          (1 - 1 / 32 * (g ^ 2)⁻¹) * cmYv g E R X k ^ (2 * p) + (g ^ 2)⁻¹ *
            (CM * ∑ j ∈ J.filter (fun j => j.1.natAbs < k.1.natAbs), cmYv g E R X j ^ (2 * p) +
              SM * (1 / (W : ℝ) ^ (2 * p) + 1 / g ^ (4 * p) * ∑ j ∈ J', cmYv g E R X j ^ (2 * p) +
                1 / g ^ (4 * p * R))) ∧
        transOp g E (fun Y => cmZv g E R Y k ^ (2 * p)) X ≤
          (1 - 1 / 32 * (g ^ 2)⁻¹) * cmZv g E R X k ^ (2 * p) + (g ^ 2)⁻¹ *
            (CF * ∑ j ∈ J.filter (fun j => j.1.natAbs < k.1.natAbs), cmZv g E R X j ^ (2 * p) +
              SF * (1 / (W : ℝ) ^ p + ∑ j ∈ J', cmYv g E R X j ^ (2 * p) +
                1 / g ^ (4 * p) * ∑ j ∈ J', cmZv g E R X j ^ (2 * p) + 1 / g ^ (4 * p * R))) := by
  -- the index sets: `J₀ = {0 < |j| ≤ N}` and the indices of the variables of the updates
  obtain ⟨n0, hn0⟩ : ∃ n0, n0 = J.sup (fun k : NzInt => k.1.natAbs) := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = n0 + 2 := ⟨_, rfl⟩
  have hkN : ∀ k ∈ J, k.1.natAbs ≤ n0 := fun k hk => by
    rw [hn0]; exact Finset.le_sup (f := fun k : NzInt => k.1.natAbs) hk
  obtain ⟨E₀, hE₀, S, K₀, hK₀, hS⟩ := corrCoeff_bounded R J
  obtain ⟨J', hJ'⟩ : ∃ J' : Finset NzInt, J' = (Finset.Icc (-(N : ℤ)) N).subtype (fun j => j ≠ 0) ∪
      S.biUnion (fun d => d.support.biUnion cmIdx) := ⟨_, rfl⟩
  have hSJ' : ∀ d ∈ S, ∀ v ∈ d.support, ∀ j ∈ cmIdx v, j ∈ J' := fun d hd v hv j hj => by
    rw [hJ']
    exact Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_biUnion.mpr ⟨v, hv, hj⟩⟩)
  have hsmall : ∀ j : NzInt, j.1.natAbs ≤ N → j ∈ J' := fun j hj => by
    rw [hJ', Finset.mem_union, Finset.mem_subtype, Finset.mem_Icc]; omega
  have hJJ' : J ⊆ J' := fun k hk => hsmall k (by have := hkN k hk; omega)
  obtain ⟨E₁, hE₁, K₁, hK₁, hN1⟩ := norm_obsEval_corrObs_sub_le R J'
  obtain ⟨E₂, hE₂, c₂, K₂, g₂, hc₂, hK₂, hg₂, hC2⟩ := center_bounds R J'
  obtain ⟨E₃, hE₃, K₃, hK₃, hT3⟩ := transOp_corrObs_sub_le R J
  obtain ⟨E₄, hE₄, K₄, hK₄, hI4⟩ := innovation_moment_corrObs R J p
  obtain ⟨E₅, hE₅, K₅, hK₅, hI5⟩ := innovation_moment_corrObs R J 1
  obtain ⟨E₆, hE₆, hL6⟩ := truncG_one_corrUpd R J
  obtain ⟨Km, hKm, hmom⟩ := cm_moment p
  -- the constants
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 2 + K₁ + K₂ := ⟨_, rfl⟩
  have hB1 : 1 ≤ B := by rw [hB]; linarith
  have hB0 : 0 ≤ B := by linarith
  obtain ⟨LH, hLH⟩ : ∃ LH : ℝ, LH = K₀ * ∑ d ∈ S, ((∑ v ∈ d.support, d v : ℕ) : ℝ) *
      B ^ (∑ v ∈ d.support, d v) * d.support.card := ⟨_, rfl⟩
  have hLH0 : 0 ≤ LH := by rw [hLH]; positivity
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = 2 * 16 ^ (2 * p - 1) * 5 ^ (2 * p - 1) := ⟨_, rfl⟩
  obtain ⟨Cξ, hCξ⟩ : ∃ Cξ : ℝ, Cξ = 32 ^ (p - 1) * (Km * K₅) ^ p + Km * K₄ := ⟨_, rfl⟩
  obtain ⟨CT, hCT⟩ : ∃ CT : ℝ, CT = 10 * (N : ℝ) ^ 2 * B := ⟨_, rfl⟩
  obtain ⟨CC, hCC⟩ : ∃ CC : ℝ, CC = 11 * (((N : ℝ) + 1) ^ 2 * B ^ 2) := ⟨_, rfl⟩
  obtain ⟨nJ, hnJ⟩ : ∃ nJ : ℝ, nJ = (J.card : ℝ) ^ (2 * p - 1) := ⟨_, rfl⟩
  obtain ⟨nJ', hnJ'⟩ : ∃ nJ' : ℝ, nJ' = (J'.card : ℝ) ^ (2 * p - 1) := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have hCξ0 : 0 ≤ Cξ := by rw [hCξ]; positivity
  have hCT0 : 0 ≤ CT := by rw [hCT]; positivity
  have hCC0 : 0 ≤ CC := by rw [hCC]; positivity
  have hnJ0 : 0 ≤ nJ := by rw [hnJ]; positivity
  have hnJ'0 : 0 ≤ nJ' := by rw [hnJ']; positivity
  refine ⟨J', hJJ', min (min (min E₀ E₁) (min E₂ E₃)) (min (min E₄ E₅) (min E₆ 1)),
    lt_min (lt_min (lt_min hE₀ hE₁) (lt_min hE₂ hE₃))
      (lt_min (lt_min hE₄ hE₅) (lt_min hE₆ one_pos)),
    Q * CT ^ (2 * p) * nJ, Q * CC ^ (2 * p) * nJ,
    (Q * K₃ ^ (2 * p) + Cξ) + Q * (LH ^ (2 * p) * nJ') + Q * (K₃ + K₂) ^ (2 * p),
    (Q * (LH + K₃) ^ (2 * p) + Cξ) + Q * ((CC + LH) ^ (2 * p) * nJ') + Q * (LH ^ (2 * p) * nJ') +
      Q * K₃ ^ (2 * p), max g₂ (5 * N + K₁ + 2 * K₂ + 1), by positivity, by positivity,
    by positivity, by positivity, le_max_of_le_left hg₂, ?_⟩
  intro W hW g hg E hE X hX k hk'
  -- reduction to `k > 0`
  obtain ⟨kn, hkn⟩ : ∃ kn, kn = k.1.natAbs := ⟨_, rfl⟩
  have hk0 : (kn : ℤ) ≠ 0 := by rw [hkn]; simpa using k.2
  have hk : (⟨kn, hk0⟩ : NzInt) ∈ J := hJ k hk' _ (by simp [hkn])
  have hPe : ∀ f₁ f₂ : State W → ℝ, (∀ Y : State W, IsState Y → f₁ Y = f₂ Y) →
      transOp g E f₁ X = transOp g E f₂ X := fun f₁ f₂ hf =>
    integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      hf _ (isState_stepState g E hX (gueBlock_isHermitian W 1 ω 0)))
  have hsk : ∀ Y : State W, IsState Y → cmYv g E R Y k = cmYv g E R Y ⟨kn, hk0⟩ ∧
      cmZv g E R Y k = cmZv g E R Y ⟨kn, hk0⟩ := fun Y hY => by
    subst hkn; exact cm_sym hW g E R hY k
  rw [hPe (fun Y => cmYv g E R Y k ^ (2 * p)) (fun Y => cmYv g E R Y ⟨kn, hk0⟩ ^ (2 * p))
      fun Y hY => by rw [(hsk Y hY).1],
    hPe (fun Y => cmZv g E R Y k ^ (2 * p)) (fun Y => cmZv g E R Y ⟨kn, hk0⟩ ^ (2 * p))
      fun Y hY => by rw [(hsk Y hY).2],
    (hsk X hX).1, (hsk X hX).2, ← hkn]
  -- the parameters
  have hg₂' : g₂ ≤ g := (le_max_left _ _).trans hg
  have hgB : 5 * (N : ℝ) + K₁ + 2 * K₂ + 1 ≤ g := (le_max_right _ _).trans hg
  have hN0 : (0 : ℝ) ≤ 5 * N := by positivity
  have hg1 : 1 ≤ g := hg₂.trans hg₂'
  have hg2 : 1 ≤ g ^ 2 := one_le_pow₀ hg1
  have hgg : g ≤ g ^ 2 := by nlinarith
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (g ^ 2)⁻¹ := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t ≤ 1 := by rw [ht]; exact inv_le_one_of_one_le₀ hg2
  have hWR : (1 : ℝ) ≤ W := by exact_mod_cast hW
  obtain ⟨⟨⟨hE₀', hE₁'⟩, ⟨hE₂', hE₃'⟩⟩, ⟨⟨hE₄', hE₅'⟩, ⟨hE₆', hE1⟩⟩⟩ :=
    (le_min_iff.mp hE).imp (fun h => (le_min_iff.mp h).imp (fun h => le_min_iff.mp h)
      (fun h => le_min_iff.mp h)) (fun h => (le_min_iff.mp h).imp (fun h => le_min_iff.mp h)
      (fun h => le_min_iff.mp h))
  have hh := cm_normalH_bounds hE1
  -- bounds at the state and the centers
  have hbd : ∀ j ∈ J', ‖obsEval g X (corrObsM E R j)‖ ≤ B ∧ ‖obsEval g X (corrObsF E R j)‖ ≤ B ∧
      ‖center g E R j.1‖ ≤ B := by
    intro j hj
    obtain ⟨hm, hf, -, -⟩ := hN1 W hW g hg1 E hE₁' X hX j hj
    obtain ⟨-, ha, -, -⟩ := (hC2 g hg₂' E hE₂').2 j hj
    have h1 : K₁ / g ^ 2 ≤ K₁ := div_le_self hK₁.le hg2
    have := (norm_sub_norm_le _ _).trans (hm.trans h1)
    have := (norm_sub_norm_le _ _).trans (hf.trans h1)
    have := norm_obsM_le_one j.1 hX
    have := norm_obsF_le_one j.1 hX
    exact ⟨by rw [hB]; linarith, by rw [hB]; linarith, by rw [hB]; linarith⟩
  have hM2 : ‖obsEval g X (corrObsM E R ⟨2, by norm_num⟩)‖ ≤ 2 := by
    obtain ⟨hm, -, -, -⟩ := hN1 W hW g hg1 E hE₁' X hX ⟨2, by norm_num⟩ (hsmall _ (by simp; omega))
    have h1 : K₁ / g ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    have := norm_obsM_le_one 2 hX
    have := (norm_sub_norm_le _ _).trans (hm.trans h1)
    linarith
  have ha2 : ‖center g E R 2‖ ≤ 1 := by
    have h := (hC2 g hg₂' E hE₂').1
    have : K₂ / g ^ 2 ≤ 1 / 2 := by rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  -- the deviations
  obtain ⟨ΔM, hΔM⟩ : ∃ ΔM : ℝ, ΔM = ∑ j ∈ J', cmYv g E R X j := ⟨_, rfl⟩
  obtain ⟨ΔZ, hΔZ⟩ : ∃ ΔZ : ℝ, ΔZ = ∑ j ∈ J', cmZv g E R X j := ⟨_, rfl⟩
  have hΔM0 : 0 ≤ ΔM := by rw [hΔM]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hΔZ0 : 0 ≤ ΔZ := by rw [hΔZ]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hWi : ‖((W : ℂ))⁻¹‖ = (W : ℝ)⁻¹ := by simp
  have hWi1 : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hWR
  have hWi0 : 0 ≤ (W : ℝ)⁻¹ := by positivity
  have hxγ : cmX g E R X .γ = (t : ℂ) := by rw [cmX_γ, ht]
  have hyγ : cmY g E R .γ = (t : ℂ) := by rw [cmY_γ, ht]
  have hvb : ∀ d ∈ S, ∀ v ∈ d.support, ‖cmX g E R X v‖ ≤ B ∧ ‖cmY g E R v‖ ≤ B ∧
      ‖cmX g E R X v - cmY g E R v‖ ≤ ΔM + ΔZ + (W : ℝ)⁻¹ ∧
      (v ∈ traceVars → ‖cmX g E R X v - cmY g E R v‖ ≤ ΔM) := by
    intro d hd v hv
    cases v with
    | m j =>
      have hj : j ∈ J' := hSJ' d hd _ hv j (by simp [cmIdx])
      have hY : ‖cmX g E R X (.m j) - cmY g E R (.m j)‖ ≤ ΔM := by
        rw [cmY_m, hΔM]
        exact Finset.single_le_sum (f := cmYv g E R X) (fun _ _ => norm_nonneg _) hj
      exact ⟨(hbd j hj).1, by rw [cmY_m]; exact (hbd j hj).2.2, by linarith, fun _ => hY⟩
    | f j =>
      have hj : j ∈ J' := hSJ' d hd _ hv j (by simp [cmIdx])
      have hY : ‖cmX g E R X (.f j) - cmY g E R (.f j)‖ ≤ ΔZ := by
        rw [cmY_f, sub_zero, hΔZ]
        exact Finset.single_le_sum (f := cmZv g E R X) (fun _ _ => norm_nonneg _) hj
      refine ⟨(hbd j hj).2.1, by rw [cmY_f, norm_zero]; linarith, by linarith, fun h => ?_⟩
      rcases h with ⟨h0, -⟩ | ⟨j', hj'⟩
      · exact absurd h0 j.2
      · exact absurd hj' (fun h => ObsVar.noConfusion h)
    | w =>
      refine ⟨by rw [cmX_w, hWi]; linarith, by rw [cmY_w, norm_zero]; linarith,
        by rw [cmX_w, cmY_w, sub_zero, hWi]; linarith, fun h => ?_⟩
      rcases h with ⟨-, h⟩ | ⟨j', hj'⟩
      · exact absurd rfl h
      · exact absurd hj' (fun h => ObsVar.noConfusion h)
    | γ =>
      have ht' : ‖(t : ℂ)‖ ≤ B := by rw [Complex.norm_real, Real.norm_of_nonneg ht0.le]; linarith
      refine ⟨by rw [hxγ]; exact ht', by rw [hyγ]; exact ht', ?_, fun _ => ?_⟩ <;>
        rw [hxγ, hyγ, sub_self, norm_zero] <;> positivity
  -- the row index
  have hkn1 : 1 ≤ kn := by omega
  have hknN : kn ≤ n0 := by simpa using hkN _ hk
  obtain ⟨hLm, hLf⟩ := hL6 E hE₆' _ hk (by simp; omega)
  rw [show (⟨(kn : ℤ), hk0⟩ : NzInt).1.toNat = kn by simp] at hLm hLf
  have hlam : ‖(-normalPhase E) ^ (⟨(kn : ℤ), hk0⟩ : NzInt).1‖ = 1 := cm_norm_lam E _
  have htD : t * (5 * (N : ℝ)) ^ 2 ≤ 1 := by
    rw [ht, inv_mul_le_iff₀ (by positivity), mul_one]
    exact pow_le_pow_left₀ hN0 (by linarith) 2
  have hlow : ∀ j : ℤ, ∀ h : j ≠ 0, 0 < j → j < kn →
      (⟨j, h⟩ : NzInt) ∈ J.filter (fun j => j.1.natAbs < kn) := by
    intro j h hj0 hjk
    refine Finset.mem_filter.mpr ⟨hJ _ hk _ ?_, by simp; omega⟩
    rw [abs_of_pos hj0, abs_of_pos (by simp; omega)]; simp; omega
  have hsmall' : ∀ j : ℤ, ∀ h : j ≠ 0, j.natAbs ≤ kn + 1 → (⟨j, h⟩ : NzInt) ∈ J' :=
    fun j h hj => hsmall _ (by simp; omega)
  have hMX : ∀ j : ℤ, j.natAbs ≤ kn + 1 → ‖aeval (cmX g E R X) (mVar j)‖ ≤ B := by
    intro j hj
    by_cases h : j = 0
    · simp [h, mVar]; linarith
    · rw [cm_mVar_X g E R X h]; exact (hbd _ (hsmall' j h hj)).1
  have hMX2 : ‖aeval (cmX g E R X) (mVar 2)‖ ≤ 2 := by
    rw [cm_mVar_X g E R X (by norm_num : (2 : ℤ) ≠ 0)]; exact hM2
  have hpow : ∀ (a : ℝ), (1 / (g * a)) ^ 2 = t * (a ^ 2)⁻¹ := fun a => by rw [ht]; field_simp
  have hg2R : g ^ (2 * R + 2) = g ^ (2 * R) * g ^ 2 := by rw [pow_add]
  have hknR : (kn : ℝ) ≤ N := by rw [hN]; push_cast; exact_mod_cast (by omega : kn ≤ n0 + 2)
  have hn : 1 ≤ 2 * p := by omega
  have hN2 : (2 : ℝ) ≤ N := by rw [hN]; push_cast; linarith [(Nat.cast_nonneg n0 : (0 : ℝ) ≤ n0)]
  rw [← ht]
  refine ⟨?_, ?_⟩
  · -- the row of `M_k`
    obtain ⟨Sk, hSk⟩ : ∃ Sk : ℝ, Sk = ∑ j ∈ J.filter (fun j => j.1.natAbs < kn),
        cmYv g E R X j := ⟨_, rfl⟩
    have hSk0 : 0 ≤ Sk := by rw [hSk]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    obtain ⟨-, -, hUS, hUc⟩ := hS E hE₀' _ hk (.m ⟨kn, hk0⟩) (by simp)
    obtain ⟨-, -, hinc, -⟩ := (hC2 g hg₂' E hE₂').2 _ (hJJ' hk)
    have hTm := (hT3 W hW g hg1 E hE₃' X hX _ hk).1
    have hUtr := cm_trace_corrUpd E R ⟨kn, hk0⟩
    obtain ⟨U, hU⟩ : ∃ U, U = corrUpd E R (.m ⟨kn, hk0⟩) := ⟨_, rfl⟩
    rw [← hU] at hUS hLm hUtr
    rw [cm_eval_cmX, ← hU] at hTm
    have hcinc : centerEval g (center g E R) (centerInc E R ⟨kn, hk0⟩) =
        aeval (cmY g E R) U - center g E R kn := by
      rw [centerInc, ← hU, map_sub, cm_centerEval_eq g _ U]
      exact congrArg₂ _ rfl (cmY_m g E R ⟨kn, hk0⟩)
    rw [hcinc] at hinc
    have hT1x : aeval (cmX g E R X) (truncG 1 U) = (-normalPhase E) ^ (kn : ℤ) *
        (obsEval g X (corrObsM E R ⟨kn, hk0⟩) + ((normalH E ^ 2 : ℝ) : ℂ) * (t : ℂ) *
          aeval (cmX g E R X) (centerTrace kn)) := by
      rw [hLm, cm_aeval_lead, hxγ]; rfl
    have hT1y : aeval (cmY g E R) (truncG 1 U) = (-normalPhase E) ^ (kn : ℤ) *
        (center g E R kn + ((normalH E ^ 2 : ℝ) : ℂ) * (t : ℂ) *
          aeval (cmY g E R) (centerTrace kn)) := by
      rw [hLm, cm_aeval_lead, hyγ, cmY_m]
    -- the trace row
    have hYj : ∀ j : ℤ, 0 ≤ j → j < kn →
        ‖aeval (cmX g E R X) (mVar j) - center g E R j‖ ≤ Sk := by
      intro j hj0 hjk
      by_cases h : j = 0
      · subst h; simp [mVar, (center_zero_odd_neg g E R 0).1]; exact hSk0
      · rw [cm_mVar_X g E R X h, hSk]
        exact Finset.single_le_sum (f := cmYv g E R X) (fun _ _ => norm_nonneg _)
          (hlow j h (by omega) hjk)
    have hτ : ∃ d : ℂ, 1 ≤ d.re ∧ ‖d‖ ≤ 5 * N ∧
        ‖(aeval (cmX g E R X) (centerTrace kn) - aeval (cmY g E R) (centerTrace kn)) +
          d * (obsEval g X (corrObsM E R ⟨kn, hk0⟩) - center g E R kn)‖ ≤ CT * Sk := by
      rw [cm_eval_trace, cm_eval_trace, funext (cm_mVar_Y g E R),
        ← cm_mVar_X g E R X hk0]
      rcases Nat.lt_or_ge kn 2 with h1 | h2
      · obtain rfl : kn = 1 := by omega
        refine ⟨3 + aeval (cmX g E R X) (mVar 2), ?_, (norm_add_le _ _).trans ?_, ?_⟩
        · have := (abs_le.mp (Complex.abs_re_le_norm (aeval (cmX g E R X) (mVar 2)))).1
          simp only [Complex.add_re, Complex.re_ofNat]; linarith
        · simp only [Complex.norm_ofNat]; linarith
        · rw [show ((1 : ℕ) : ℤ) = 1 by norm_num, cm_tau_one _ _ (cm_center_one g E R)]
          simp only [neg_mul, neg_add_cancel, norm_zero]
          exact mul_nonneg hCT0 hSk0
      · refine ⟨3 * (kn : ℂ) + (kn : ℂ) / 2 * (aeval (cmX g E R X) (mVar 2) + center g E R 2),
          (cm_d_trace hkn1 hMX2 (by linarith)).1,
          (cm_d_trace hkn1 hMX2 (by linarith)).2.trans (by linarith), ?_⟩
        refine (le_of_eq_of_le (by ring_nf) (cm_tau_diff h2 _ _ hB0 (fun j _ _ => hMX j
          (by omega)) (fun j _ _ => ?_) (cm_center_one g E R) hYj)).trans ?_
        · by_cases h : j = 0
          · simp [h, (center_zero_odd_neg g E R 0).1]; linarith
          · exact (hbd _ (hsmall' j h (by omega))).2.2
        rw [hCT]
        have := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hknR 2)
          (mul_nonneg hB0 hSk0)
        nlinarith
    obtain ⟨d, hdre, hdn, hdL⟩ := hτ
    -- the orders `≥ g⁻⁴` and the conditional mean
    have hHx := cm_lip (U - truncG 1 U) ((cm_H_support U).trans hUS) hK₀.le
      (cm_H_coeff_le hK₀.le fun d => by rw [hU]; exact (hUc d).2.2)
      (cm_H_two U) ht0.le ht1 hxγ hyγ hB1 hΔM0 (fun d hd v hv => by
        obtain ⟨b1, b2, -, b4⟩ := hvb d (hUS (cm_H_support U hd)) v hv
        refine ⟨b1, b2, b4 ?_⟩
        rw [mem_supported] at hUtr
        exact hUtr ((mem_vars_iff_mem_support _).mpr ⟨d, cm_H_support U hd, hv⟩))
    rw [← hLH] at hHx
    have hμ : ‖transOp g E (fun Y => obsEval g Y (corrObsM E R ⟨kn, hk0⟩)) X - center g E R kn‖ ≤
        (1 - t / 8) * ‖obsEval g X (corrObsM E R ⟨kn, hk0⟩) - center g E R kn‖ + t * (CT * Sk +
          t * LH * ΔM +
          K₃ * ((W : ℝ) ^ 2)⁻¹ + (K₃ + K₂) * (g ^ (2 * R))⁻¹ + 0) := by
      set PM := transOp g E (fun Y => obsEval g Y (corrObsM E R ⟨kn, hk0⟩)) X
      have e : PM - center g E R kn = (PM - aeval (cmX g E R X) U) +
          (aeval (cmX g E R X) (truncG 1 U) - aeval (cmY g E R) (truncG 1 U)) +
          (aeval (cmX g E R X) (U - truncG 1 U) - aeval (cmY g E R) (U - truncG 1 U)) +
          (aeval (cmY g E R) U - center g E R kn) := by rw [map_sub, map_sub]; ring
      have hlead := cm_lead hlam hdre hdn hh.1 hh.2 ht0.le htD hdL
      rw [hT1x, hT1y, ← mul_sub, show ∀ a b c d d' e : ℂ, a + b * c * d - (e + b * c * d') =
        (a - e) + b * c * (d - d') from fun a b c d d' e => by ring] at e
      rw [e]
      refine (cm_norm4 _ _ _ _).trans ?_
      have e1 : K₃ * (1 / (g ^ 2 * (W : ℝ) ^ 2) + 1 / g ^ (2 * R + 2)) =
          t * (K₃ * ((W : ℝ) ^ 2)⁻¹ + K₃ * (g ^ (2 * R))⁻¹) := by rw [ht, hg2R]; field_simp
      have e2 : K₂ / g ^ (2 * R + 2) = t * (K₂ * (g ^ (2 * R))⁻¹) := by
        rw [ht, hg2R]; field_simp
      rw [e1] at hTm
      rw [e2] at hinc
      have : t * (CT * Sk + t * LH * ΔM + K₃ * ((W : ℝ) ^ 2)⁻¹ + (K₃ + K₂) * (g ^ (2 * R))⁻¹ + 0) =
          t * (K₃ * ((W : ℝ) ^ 2)⁻¹ + K₃ * (g ^ (2 * R))⁻¹) + t * (CT * Sk) +
            t ^ 2 * LH * ΔM + t * (K₂ * (g ^ (2 * R))⁻¹) := by ring
      rw [this]
      linarith
    -- the moment step
    have hrow := cm_row (ω := ((W : ℝ) ^ 2)⁻¹) hp ht0 ht1 (by positivity) (norm_nonneg _)
      (norm_nonneg _) hKm.le hK₅.le hK₄.le (mul_nonneg hCT0 hSk0) (by positivity) (by positivity)
      (by positivity) le_rfl (hmom hW g hg1 E X hX (corrObsM E R ⟨kn, hk0⟩) (center g E R kn))
      (by rw [mul_one, ← hpow]; simpa using (hI5 W hW g hg1 E hE₅' X hX _ hk).1)
      (by rw [← hpow, ← pow_mul]; exact (hI4 W hW g hg1 E hE₄' X hX _ hk).1) hμ
    rw [← hQ, ← hCξ, show (1 : ℝ) - t / 32 = 1 - 1 / 32 * t by ring] at hrow
    refine hrow.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ ht0.le))
    -- the slots
    have hW2 := cm_pow_W hWR p 2
    have hb1 : (CT * Sk) ^ (2 * p) ≤ CT ^ (2 * p) * nJ *
        ∑ j ∈ J.filter (fun j => j.1.natAbs < kn), cmYv g E R X j ^ (2 * p) := by
      rw [hSk, hnJ]; exact cm_bsum (Finset.filter_subset _ J) (fun j => norm_nonneg _) hCT0 hn
    have hb2 : ((g ^ 2)⁻¹ * LH * ΔM) ^ (2 * p) ≤ LH ^ (2 * p) * nJ' *
        (1 / g ^ (4 * p) * ∑ j ∈ J', cmYv g E R X j ^ (2 * p)) := by
      rw [hΔM, hnJ']
      refine (cm_bsum (subset_refl J') (f := cmYv g E R X) (fun j => norm_nonneg _)
        (by positivity) hn).trans (le_of_eq ?_)
      rw [mul_pow, cm_pow_g]; ring
    have hs := cm_slots3 (x₁ := Q * (K₃ * ((W : ℝ) ^ 2)⁻¹) ^ (2 * p) + Cξ * (((W : ℝ) ^ 2)⁻¹) ^ p)
      (y₁ := Q * K₃ ^ (2 * p) + Cξ) (s₁ := 1 / (W : ℝ) ^ (2 * p))
      (x₂ := Q * ((g ^ 2)⁻¹ * LH * ΔM) ^ (2 * p)) (y₂ := Q * (LH ^ (2 * p) * nJ'))
      (s₂ := 1 / g ^ (4 * p) * ∑ j ∈ J', cmYv g E R X j ^ (2 * p))
      (x₃ := Q * ((K₃ + K₂) * (g ^ (2 * R))⁻¹) ^ (2 * p)) (y₃ := Q * (K₃ + K₂) ^ (2 * p))
      (s₃ := 1 / g ^ (4 * p * R))
      ((add_le_add (mul_le_mul_of_nonneg_left ((mul_pow _ _ _).le.trans
        (mul_le_mul_of_nonneg_left hW2.1 (by positivity))) hQ0) (le_of_eq (by rw [hW2.2]))).trans
        (le_of_eq (by ring)))
      ((mul_le_mul_of_nonneg_left hb2 hQ0).trans (le_of_eq (by ring)))
      (le_of_eq (by rw [mul_pow, cm_pow_gR]; ring))
      (by positivity) (by positivity) (by positivity) (by positivity)
      (mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => pow_nonneg (norm_nonneg _) _))
      (by positivity)
    have h1 := mul_le_mul_of_nonneg_left hb1 hQ0
    rw [zero_pow (by omega : 2 * p ≠ 0), add_zero, ht]
    linarith
  · -- the row of `F_k`
    obtain ⟨-, -, hUS, hUc⟩ := hS E hE₀' _ hk (.f ⟨kn, hk0⟩) (by simp)
    have hTf := (hT3 W hW g hg1 E hE₃' X hX _ hk).2
    have hP := hmom hW g hg1 E X hX (corrObsF E R ⟨kn, hk0⟩) 0
    simp only [sub_zero] at hP
    have hUf := cm_f_corrUpd E R ⟨kn, hk0⟩
    obtain ⟨U, hU⟩ : ∃ U, U = corrUpd E R (.f ⟨kn, hk0⟩) := ⟨_, rfl⟩
    rw [← hU] at hUS hLf hUf
    rw [cm_eval_cmX, ← hU] at hTf
    have hT1x : aeval (cmX g E R X) (truncG 1 U) = (-normalPhase E) ^ (kn : ℤ) *
        (obsEval g X (corrObsF E R ⟨kn, hk0⟩) + ((normalH E ^ 2 : ℝ) : ℂ) * (t : ℂ) *
          aeval (cmX g E R X) (centerCorner kn)) := by
      rw [hLf, cm_aeval_lead, hxγ]; rfl
    -- the corner row
    obtain ⟨SFk, hSFk⟩ : ∃ SFk : ℝ, SFk = ∑ j ∈ J.filter (fun j => j.1.natAbs < kn),
        cmZv g E R X j := ⟨_, rfl⟩
    have hSFk0 : 0 ≤ SFk := by rw [hSFk]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hM1 : ‖aeval (cmX g E R X) (mVar 1)‖ + ‖aeval (cmX g E R X) (mVar (-1))‖ ≤ ΔM := by
      have hne : (⟨1, by norm_num⟩ : NzInt) ≠ ⟨-1, by norm_num⟩ := by
        intro h; have := congrArg Subtype.val h; norm_num at this
      have := Finset.sum_le_sum_of_subset_of_nonneg (f := cmYv g E R X)
        (s := {⟨1, by norm_num⟩, ⟨-1, by norm_num⟩}) (t := J') (by
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact hsmall' 1 _ (by simp)
          · rw [Finset.mem_singleton.mp hj]; exact hsmall' (-1) _ (by simp))
        (fun _ _ _ => norm_nonneg _)
      rw [Finset.sum_pair hne] at this
      rw [cm_mVar_X g E R X (by norm_num : (1 : ℤ) ≠ 0),
        cm_mVar_X g E R X (by norm_num : (-1 : ℤ) ≠ 0), hΔM]
      simpa [cmYv, cm_center_one, show center g E R (-1) = 0 by
        simpa using (center_zero_odd_neg g E R (-1)).2.1] using this
    have hτ : ∃ d : ℂ, 1 ≤ d.re ∧ ‖d‖ ≤ 5 * N ∧
        ‖aeval (cmX g E R X) (centerCorner kn) + d * obsEval g X (corrObsF E R ⟨kn, hk0⟩)‖ ≤
          CC * (SFk + ΔM) := by
      rw [cm_eval_corner, ← cm_fVar_X g E R X hk0]
      refine ⟨3 * (kn : ℂ) + (kn : ℂ) * aeval (cmX g E R X) (mVar 2),
        (cm_d_corner hkn1 hMX2).1, (cm_d_corner hkn1 hMX2).2.trans (by linarith), ?_⟩
      refine (cm_corner_diff hkn1 _ _ hB1 hSFk0 (fun j _ _ => hMX j (by omega))
        (fun j _ _ => ?_) fun j hj1 hjk => ?_).trans ?_
      · by_cases h : j = 0
        · simp [h, fVar]; linarith
        · rw [cm_fVar_X g E R X h]; exact (hbd _ (hsmall' j h (by omega))).2.1
      · rw [cm_fVar_X g E R X (by omega : j ≠ 0), hSFk]
        exact Finset.single_le_sum (f := cmZv g E R X) (fun _ _ => norm_nonneg _)
          (hlow j _ (by omega) hjk)
      · rw [hCC]
        have hX : SFk + ‖aeval (cmX g E R X) (mVar 1)‖ + ‖aeval (cmX g E R X) (mVar (-1))‖ ≤
            SFk + ΔM := by linarith
        have hk1 : ((kn : ℝ) + 1) ^ 2 * B ^ 2 ≤ ((N : ℝ) + 1) ^ 2 * B ^ 2 := by
          gcongr
        exact mul_le_mul (mul_le_mul_of_nonneg_left hk1 (by norm_num)) hX (by positivity)
          (by positivity)
    obtain ⟨d, hdre, hdn, hdL⟩ := hτ
    -- the orders `≥ g⁻⁴` and the conditional mean
    have hHx := cm_lip (U - truncG 1 U) ((cm_H_support U).trans hUS) hK₀.le
      (cm_H_coeff_le hK₀.le fun d => by rw [hU]; exact (hUc d).2.2)
      (cm_H_two U) ht0.le ht1 hxγ hyγ hB1 (Δ := ΔM + ΔZ + (W : ℝ)⁻¹) (by positivity)
      (fun d hd v hv => (hvb d (hUS (cm_H_support U hd)) v hv).imp_right fun h => h.imp_right
        fun h => h.1)
    rw [← hLH] at hHx
    have hμ : ‖transOp g E (fun Y => obsEval g Y (corrObsF E R ⟨kn, hk0⟩)) X‖ ≤
        (1 - t / 8) * ‖obsEval g X (corrObsF E R ⟨kn, hk0⟩)‖ + t * (CC * SFk + (CC + LH) * ΔM +
          t * LH * ΔZ +
          (LH + K₃) * (W : ℝ)⁻¹ + K₃ * (g ^ (2 * R))⁻¹) := by
      set PF := transOp g E (fun Y => obsEval g Y (corrObsF E R ⟨kn, hk0⟩)) X
      have e : PF = (PF - aeval (cmX g E R X) U) +
          (aeval (cmX g E R X) (truncG 1 U) - aeval (cmY g E R) (truncG 1 U)) +
          (aeval (cmX g E R X) (U - truncG 1 U) - aeval (cmY g E R) (U - truncG 1 U)) +
          aeval (cmY g E R) U := by rw [map_sub, map_sub]; ring
      have hlead := cm_lead hlam hdre hdn hh.1 hh.2 ht0.le htD hdL
      rw [hT1x, cm_aeval_fIdeal (cmY_f g E R) (cm_fIdeal_of_support (cm_support_truncG _ _) hUf),
        sub_zero] at e
      rw [e, cm_aeval_fIdeal (cmY_f g E R) hUf, add_zero]
      refine (norm_add₃_le).trans ?_
      have e1 : K₃ * (1 / (g ^ 2 * (W : ℝ)) + 1 / g ^ (2 * R + 2)) =
          t * (K₃ * (W : ℝ)⁻¹ + K₃ * (g ^ (2 * R))⁻¹) := by rw [ht, hg2R]; field_simp
      rw [e1] at hTf
      have hl1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left hLH0 ht1) hΔM0) ht0.le
      have hl2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left hLH0 ht1) hWi0) ht0.le
      have e4 : t * (CC * SFk + (CC + LH) * ΔM + t * LH * ΔZ + (LH + K₃) * (W : ℝ)⁻¹ +
          K₃ * (g ^ (2 * R))⁻¹) = t * (CC * (SFk + ΔM)) + t * (LH * ΔM) + t * (t * LH * ΔZ) +
          t * (LH * (W : ℝ)⁻¹) + t * (K₃ * (W : ℝ)⁻¹ + K₃ * (g ^ (2 * R))⁻¹) := by ring
      have e3 : t ^ 2 * LH * (ΔM + ΔZ + (W : ℝ)⁻¹) =
          t * (t * LH * ΔM) + t * (t * LH * ΔZ) + t * (t * LH * (W : ℝ)⁻¹) := by ring
      rw [e4]
      rw [e3] at hHx
      linarith
    -- the moment step
    have hsW : (Real.sqrt W) ^ 2 = W := Real.sq_sqrt (by positivity)
    have hrow := cm_row (ω := (W : ℝ)⁻¹) hp ht0 ht1 (by positivity) (norm_nonneg _)
      (norm_nonneg _) hKm.le hK₅.le hK₄.le (mul_nonneg hCC0 hSFk0) (by positivity) (by positivity)
      (by positivity) (by positivity) hP
      (by rw [← hsW, mul_one, ← hpow]; simpa using (hI5 W hW g hg1 E hE₅' X hX _ hk).2)
      (by rw [← hsW, ← hpow, ← pow_mul]; exact (hI4 W hW g hg1 E hE₄' X hX _ hk).2) hμ
    rw [← hQ, ← hCξ, show (1 : ℝ) - t / 32 = 1 - 1 / 32 * t by ring] at hrow
    refine hrow.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ ht0.le))
    -- the slots
    have hW1 := cm_pow_W hWR p 1
    simp only [pow_one, one_mul] at hW1
    have hb1 : (CC * SFk) ^ (2 * p) ≤ CC ^ (2 * p) * nJ *
        ∑ j ∈ J.filter (fun j => j.1.natAbs < kn), cmZv g E R X j ^ (2 * p) := by
      rw [hSFk, hnJ]; exact cm_bsum (Finset.filter_subset _ J) (fun j => norm_nonneg _) hCC0 hn
    have hb2 : ((CC + LH) * ΔM) ^ (2 * p) ≤ (CC + LH) ^ (2 * p) * nJ' *
        ∑ j ∈ J', cmYv g E R X j ^ (2 * p) := by
      rw [hΔM, hnJ']; exact cm_bsum (subset_refl J') (fun j => norm_nonneg _) (by positivity) hn
    have hb3 : ((g ^ 2)⁻¹ * LH * ΔZ) ^ (2 * p) ≤ LH ^ (2 * p) * nJ' *
        (1 / g ^ (4 * p) * ∑ j ∈ J', cmZv g E R X j ^ (2 * p)) := by
      rw [hΔZ, hnJ']
      refine (cm_bsum (subset_refl J') (f := cmZv g E R X) (fun j => norm_nonneg _)
        (by positivity) hn).trans (le_of_eq ?_)
      rw [mul_pow, cm_pow_g]; ring
    have hs := cm_slots4 (x₁ := Q * ((LH + K₃) * (W : ℝ)⁻¹) ^ (2 * p) + Cξ * ((W : ℝ)⁻¹) ^ p)
      (y₁ := Q * (LH + K₃) ^ (2 * p) + Cξ) (s₁ := 1 / (W : ℝ) ^ p)
      (x₂ := Q * ((CC + LH) * ΔM) ^ (2 * p)) (y₂ := Q * ((CC + LH) ^ (2 * p) * nJ'))
      (s₂ := ∑ j ∈ J', cmYv g E R X j ^ (2 * p))
      (x₃ := Q * ((g ^ 2)⁻¹ * LH * ΔZ) ^ (2 * p)) (y₃ := Q * (LH ^ (2 * p) * nJ'))
      (s₃ := 1 / g ^ (4 * p) * ∑ j ∈ J', cmZv g E R X j ^ (2 * p))
      (x₄ := Q * (K₃ * (g ^ (2 * R))⁻¹) ^ (2 * p)) (y₄ := Q * K₃ ^ (2 * p))
      (s₄ := 1 / g ^ (4 * p * R))
      ((add_le_add (mul_le_mul_of_nonneg_left ((mul_pow _ _ _).le.trans
        (mul_le_mul_of_nonneg_left hW1.1 (by positivity))) hQ0) (le_of_eq (by rw [hW1.2]))).trans
        (le_of_eq (by ring)))
      ((mul_le_mul_of_nonneg_left hb2 hQ0).trans (le_of_eq (by ring)))
      ((mul_le_mul_of_nonneg_left hb3 hQ0).trans (le_of_eq (by ring)))
      (le_of_eq (by rw [mul_pow, cm_pow_gR]; ring))
      (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
      (Finset.sum_nonneg fun j _ => pow_nonneg (norm_nonneg _) _)
      (mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => pow_nonneg (norm_nonneg _) _))
      (by positivity)
    have h1 := mul_le_mul_of_nonneg_left hb1 hQ0
    rw [ht]
    linarith


/-- (11.59) [lg:eq:momentrec] in conditional form: for a finite index set `J` that contains, with
each `k`, every nonzero `j` with `|j| ≤ |k|` (so that every order-`g⁻²` coupling of the rows of `J`
stays in `J`), there are a larger fixed set `J′`, positive weights `u`, `v` and constants such
that, at every state, with
`Y_k = M_k − a_k` and `Z_k = F_k`,
`Σ_J u_k P_g|Y_k|^{2p} ≤ (1 − c g⁻²) Σ_J u_k |Y_k|^{2p} + K g⁻²[W^{−2p} + g^{−4p} Σ_{J′}|Y_k|^{2p}
+ g^{−4pR}]` and
`Σ_J v_k P_g|Z_k|^{2p} ≤ (1 − c g⁻²) Σ_J v_k |Z_k|^{2p} + K g⁻²[W^{−p} + Σ_{J′}|Y_k|^{2p}
+ g^{−4p} Σ_{J′}|Z_k|^{2p} + g^{−4pR}]`. -/
theorem moment_contraction_corrObs (R : ℕ) (hR : 2 ≤ R) (J : Finset NzInt)
    (hJ : ∀ k ∈ J, ∀ j : NzInt, |j.1| ≤ |k.1| → j ∈ J) {p : ℕ} (hp : 1 ≤ p) :
    ∃ J' : Finset NzInt, J ⊆ J' ∧ ∃ u v : NzInt → ℝ, (∀ k, 0 < u k ∧ 0 < v k) ∧
      ∃ E₁ : ℝ, 0 < E₁ ∧ ∃ c K g₀ : ℝ, 0 < c ∧ 0 < K ∧ 1 ≤ g₀ ∧
        ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, g₀ ≤ g → ∀ E : ℝ, |E| ≤ E₁ → ∀ X : State W, IsState X →
          ∑ k ∈ J, u k * transOp g E
              (fun Y => ‖obsEval g Y (corrObsM E R k) - center g E R k.1‖ ^ (2 * p)) X ≤
            (1 - c / g ^ 2) *
                ∑ k ∈ J, u k * ‖obsEval g X (corrObsM E R k) - center g E R k.1‖ ^ (2 * p) +
              K / g ^ 2 * (1 / (W : ℝ) ^ (2 * p) + 1 / g ^ (4 * p) *
                ∑ k ∈ J', ‖obsEval g X (corrObsM E R k) - center g E R k.1‖ ^ (2 * p) +
                1 / g ^ (4 * p * R)) ∧
          ∑ k ∈ J, v k * transOp g E (fun Y => ‖obsEval g Y (corrObsF E R k)‖ ^ (2 * p)) X ≤
            (1 - c / g ^ 2) * ∑ k ∈ J, v k * ‖obsEval g X (corrObsF E R k)‖ ^ (2 * p) +
              K / g ^ 2 * (1 / (W : ℝ) ^ p +
                ∑ k ∈ J', ‖obsEval g X (corrObsM E R k) - center g E R k.1‖ ^ (2 * p) +
                1 / g ^ (4 * p) * ∑ k ∈ J', ‖obsEval g X (corrObsF E R k)‖ ^ (2 * p) +
                1 / g ^ (4 * p * R)) := by
  obtain ⟨J', hJJ', E₁, hE₁, CM, CF, SM, SF, g₀, hCM, hCF, hSM, hSF, hg₀, hrow⟩ :=
    cm_rows R J hJ hp
  simp only [cmYv, cmZv] at hrow
  refine ⟨J', hJJ', fun k => ((1 + 2 * CM * J.card / (1 / 32))⁻¹) ^ k.1.natAbs,
    fun k => ((1 + 2 * CF * J.card / (1 / 32))⁻¹) ^ k.1.natAbs,
    fun k => ⟨by positivity, by positivity⟩, E₁, hE₁, 1 / 32 / 2, J.card * (SM + SF) + 1, g₀,
    by norm_num, by positivity, hg₀, fun W hW g hg E hE X hX => ?_⟩
  have hg0 : 0 < g := by linarith [hg₀.trans hg]
  refine ⟨(cm_weights J (f := fun k => ‖obsEval g X (corrObsM E R k) - center g E R k.1‖ ^
      (2 * p)) (fun k => by positivity) (c₀ := 1 / 32) (by norm_num) hCM (by positivity)
      (by positivity) fun k hk => (hrow W hW g hg E hE X hX k hk).1).trans
      (cm_final (by positivity) (by nlinarith [(Nat.cast_nonneg J.card : (0 : ℝ) ≤ J.card)])),
    (cm_weights J (f := fun k => ‖obsEval g X (corrObsF E R k)‖ ^ (2 * p))
      (fun k => by positivity) (c₀ := 1 / 32) (by norm_num) hCF (by positivity)
      (by positivity) fun k hk => (hrow W hW g hg E hE X hX k hk).2).trans
      (cm_final (by positivity) (by nlinarith [(Nat.cast_nonneg J.card : (0 : ℝ) ≤ J.card)]))⟩

end LSBA
