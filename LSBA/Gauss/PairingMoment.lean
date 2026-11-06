import LSBA.Gauss.WickFamily
import LSBA.Analysis.PairingNorm

/-!
# Trace moments of GUE words as sums over pairings

For independent GUE blocks with the covariance (1.2) [eq:covariance],
`𝔼 Tr(G_{j_0} ⋯ G_{j_{n-1}}) = Σ_{σ pairing, j∘σ = j} w_W(σ)`, where the weight
`w_W(σ) = 𝔼 Tr(G_{c_0} ⋯ G_{c_{n-1}})` with one independent block per pair of `σ` does not depend
on the labels `j`, and is real and nonnegative. This is the Gaussian half of the tensor bound in
Appendix G.4 [app:compact-gaussian].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Isserlis expansion of a labelled word -/

/-- The involutions of `Fin n` without fixed points on `s`, equal to the identity off `s`, that
pair only equal labels `j`. -/
private def PairingMoment_pp {n m : ℕ} (j : Fin n → Fin m) (s : Finset (Fin n)) :
    Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun σ => ∀ i, (i ∈ s → σ i ∈ s ∧ σ i ≠ i ∧ σ (σ i) = i ∧ j (σ i) = j i) ∧
    (i ∉ s → σ i = i)

private lemma PairingMoment_mem_pp {n m : ℕ} {j : Fin n → Fin m} {s : Finset (Fin n)}
    {σ : Equiv.Perm (Fin n)} : σ ∈ PairingMoment_pp j s ↔
      ∀ i, (i ∈ s → σ i ∈ s ∧ σ i ≠ i ∧ σ (σ i) = i ∧ j (σ i) = j i) ∧ (i ∉ s → σ i = i) := by
  simp [PairingMoment_pp]

private lemma PairingMoment_pp_empty {n m : ℕ} (j : Fin n → Fin m) :
    PairingMoment_pp j ∅ = {1} := by
  ext σ
  rw [PairingMoment_mem_pp, Finset.mem_singleton]
  constructor
  · intro h
    exact Equiv.ext fun i => (h i).2 (Finset.notMem_empty i)
  · rintro rfl i
    exact ⟨fun h => absurd h (Finset.notMem_empty i), fun _ => rfl⟩

/-- Removing the pair `{i₀, σ i₀}` of `σ` leaves `σ` unchanged on the other points of `s`. -/
private lemma PairingMoment_swap_apply {n m : ℕ} {j : Fin n → Fin m} {s : Finset (Fin n)}
    {σ : Equiv.Perm (Fin n)} {i₀ k : Fin n} (hσ : σ ∈ PairingMoment_pp j s) (hi₀ : i₀ ∈ s)
    (hk : σ i₀ = k) {i : Fin n} (hi : i ∈ (s.erase i₀).erase k) :
    (Equiv.swap i₀ k * σ) i = σ i ∧ σ i ∈ (s.erase i₀).erase k := by
  rw [PairingMoment_mem_pp] at hσ
  obtain ⟨-, -, hσk, -⟩ := (hσ i₀).1 hi₀
  rw [hk] at hσk
  obtain ⟨hik, hi0, his⟩ : i ≠ k ∧ i ≠ i₀ ∧ i ∈ s := by simpa using hi
  obtain ⟨hsi, -, hii, -⟩ := (hσ i).1 his
  have h1 : σ i ≠ i₀ := fun h => hik (hii.symm.trans (by rw [h, hk]))
  have h2 : σ i ≠ k := fun h => hi0 (hii.symm.trans (by rw [h, hσk]))
  refine ⟨?_, by simp [h1, h2, hsi]⟩
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]

private lemma PairingMoment_swap_mem_erase {n m : ℕ} {j : Fin n → Fin m} {s : Finset (Fin n)}
    {σ : Equiv.Perm (Fin n)} {i₀ k : Fin n} (hσ : σ ∈ PairingMoment_pp j s) (hi₀ : i₀ ∈ s)
    (hk : σ i₀ = k) :
    Equiv.swap i₀ k * σ ∈ PairingMoment_pp j ((s.erase i₀).erase k) := by
  have happ := fun {i} (hi : i ∈ (s.erase i₀).erase k) => PairingMoment_swap_apply hσ hi₀ hk hi
  rw [PairingMoment_mem_pp] at hσ ⊢
  obtain ⟨hks, -, hσk, -⟩ := (hσ i₀).1 hi₀
  rw [hk] at hks hσk
  intro i
  constructor
  · intro hi
    obtain ⟨-, -, his⟩ : i ≠ k ∧ i ≠ i₀ ∧ i ∈ s := by simpa using hi
    obtain ⟨-, hne, hii, hj⟩ := (hσ i).1 his
    obtain ⟨ha, hb⟩ := happ hi
    rw [ha, (happ hb).1, hii]
    exact ⟨hb, hne, rfl, hj⟩
  · intro hi
    by_cases h0 : i = i₀
    · rw [h0, Equiv.Perm.mul_apply, hk, Equiv.swap_apply_right]
    by_cases h1 : i = k
    · rw [h1, Equiv.Perm.mul_apply, hσk, Equiv.swap_apply_left]
    have his : i ∉ s := fun h => hi (by simp [h, h0, h1])
    rw [Equiv.Perm.mul_apply, (hσ i).2 his, Equiv.swap_apply_of_ne_of_ne h0 h1]

private lemma PairingMoment_swap_mem {n m : ℕ} {j : Fin n → Fin m} {s : Finset (Fin n)}
    {τ : Equiv.Perm (Fin n)} {i₀ k : Fin n} (hτ : τ ∈ PairingMoment_pp j ((s.erase i₀).erase k))
    (hi₀ : i₀ ∈ s) (hk : k ∈ s) (hki : k ≠ i₀) (hj : j k = j i₀) :
    Equiv.swap i₀ k * τ ∈ PairingMoment_pp j s ∧ (Equiv.swap i₀ k * τ) i₀ = k := by
  rw [PairingMoment_mem_pp] at hτ ⊢
  have hmem : ∀ i, i ∈ (s.erase i₀).erase k ↔ i ≠ k ∧ i ≠ i₀ ∧ i ∈ s := fun i => by simp
  have hτ0 : τ i₀ = i₀ := (hτ i₀).2 (by simp [hmem])
  have hτk : τ k = k := (hτ k).2 (by simp [hmem])
  have hin : ∀ i, i ∈ (s.erase i₀).erase k →
      (Equiv.swap i₀ k * τ) i = τ i ∧ τ i ∈ (s.erase i₀).erase k := by
    intro i hi
    have h := ((hτ i).1 hi).1
    have h' := (hmem _).1 h
    exact ⟨Equiv.swap_apply_of_ne_of_ne h'.2.1 h'.1, h⟩
  have h0 : (Equiv.swap i₀ k * τ) i₀ = k := by
    rw [Equiv.Perm.mul_apply, hτ0, Equiv.swap_apply_left]
  have h1 : (Equiv.swap i₀ k * τ) k = i₀ := by
    rw [Equiv.Perm.mul_apply, hτk, Equiv.swap_apply_right]
  refine ⟨fun i => ⟨fun hi => ?_, fun hi => ?_⟩, h0⟩
  · by_cases e0 : i = i₀
    · rw [e0, h0, h1]
      exact ⟨hk, hki, rfl, hj⟩
    by_cases e1 : i = k
    · rw [e1, h1, h0]
      exact ⟨hi₀, Ne.symm hki, rfl, hj.symm⟩
    have hi' : i ∈ (s.erase i₀).erase k := (hmem i).2 ⟨e1, e0, hi⟩
    obtain ⟨ha, hb⟩ := hin i hi'
    obtain ⟨-, hd, he, hf⟩ := (hτ i).1 hi'
    rw [ha, (hin _ hb).1]
    exact ⟨((hmem _).1 hb).2.2, hd, he, hf⟩
  · have e0 : i ≠ i₀ := fun h => hi (h ▸ hi₀)
    have e1 : i ≠ k := fun h => hi (h ▸ hk)
    have hτi : τ i = i := (hτ i).2 (fun h => hi ((hmem i).1 h).2.2)
    rw [Equiv.Perm.mul_apply, hτi, Equiv.swap_apply_of_ne_of_ne e0 e1]

/-- A product over `s` along `σ` splits off the factors of the pair `{i₀, σ i₀}`. -/
private lemma PairingMoment_prod_split {n m : ℕ} {j : Fin n → Fin m} {s : Finset (Fin n)}
    {σ : Equiv.Perm (Fin n)} {i₀ k : Fin n} (hσ : σ ∈ PairingMoment_pp j s) (hi₀ : i₀ ∈ s)
    (hk : σ i₀ = k) (D : Fin n → Fin n → ℂ) :
    ∏ i ∈ s, D i (σ i) = D i₀ k * D k i₀ *
      ∏ i ∈ (s.erase i₀).erase k, D i ((Equiv.swap i₀ k * σ) i) := by
  have happ := fun {i} (hi : i ∈ (s.erase i₀).erase k) => PairingMoment_swap_apply hσ hi₀ hk hi
  rw [PairingMoment_mem_pp] at hσ
  obtain ⟨hks, hki, hσk, -⟩ := (hσ i₀).1 hi₀
  rw [hk] at hks hki hσk
  rw [← Finset.mul_prod_erase s (fun i => D i (σ i)) hi₀,
    ← Finset.mul_prod_erase (s.erase i₀) (fun i => D i (σ i)) (Finset.mem_erase.2 ⟨hki, hks⟩)]
  simp only [hk, hσk, mul_assoc]
  congr 2
  exact Finset.prod_congr rfl fun i hi => by rw [(happ hi).1]

/-- Isserlis expansion of a word in independent GUE blocks of (1.2) [eq:covariance]:
`𝔼 ∏_{i∈s} x_i* G_{j_i} w_i` is the sum over the label-respecting pairings `σ` of `s` of
`∏_{i∈s} c(i, σ i) (x_i* w_{σ i})`, with `c(i, k) = W⁻¹` for `i < k` and `1` otherwise. -/
private lemma PairingMoment_isserlis (W m n : ℕ) (j : Fin n → Fin m) (x w : Fin n → Fin W → ℂ)
    (s : Finset (Fin n)) :
    ∫ ω, ∏ i ∈ s, (star (x i) ⬝ᵥ (gueBlock W m ω (j i) *ᵥ w i)) ∂(μ W m) =
      ∑ σ ∈ PairingMoment_pp j s,
        ∏ i ∈ s, (if i < σ i then (W : ℂ)⁻¹ else 1) * (star (x i) ⬝ᵥ w (σ i)) := by
  induction s using Finset.strongInduction with
  | H s ih =>
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [PairingMoment_pp_empty]
  have hi₀ : s.min' hs ∈ s := s.min'_mem hs
  set i₀ := s.min' hs with hi₀def
  have hfun : (fun ω => ∏ i ∈ s, (star (x i) ⬝ᵥ (gueBlock W m ω (j i) *ᵥ w i))) = fun ω =>
      (star (x i₀) ⬝ᵥ (gueBlock W m ω (j i₀) *ᵥ w i₀)) *
        ∏ i ∈ s.erase i₀, (star (x i) ⬝ᵥ (gueBlock W m ω (j i) *ᵥ w i)) :=
    funext fun ω => (Finset.mul_prod_erase s _ hi₀).symm
  rw [hfun, integral_gueLin_mul_prod_family]
  have hmaps : ∀ σ ∈ PairingMoment_pp j s,
      σ i₀ ∈ (s.erase i₀).filter (fun k => j k = j i₀) := by
    intro σ hσ
    obtain ⟨h1, h2, -, h4⟩ := ((PairingMoment_mem_pp.1 hσ) i₀).1 hi₀
    exact Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨h2, h1⟩, h4⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk1, hkj⟩ := Finset.mem_filter.1 hk
  obtain ⟨hki, hks⟩ := Finset.mem_erase.1 hk1
  have hlt : i₀ < k := lt_of_le_of_ne (s.min'_le k hks) (Ne.symm hki)
  rw [ih _ ((Finset.erase_subset k _).trans_ssubset (Finset.erase_ssubset hi₀)), Finset.mul_sum]
  symm
  refine Finset.sum_nbij' (fun σ => Equiv.swap i₀ k * σ) (fun τ => Equiv.swap i₀ k * τ)
    ?_ ?_ ?_ ?_ ?_
  · intro σ hσ
    obtain ⟨hσ, hσk⟩ := Finset.mem_filter.1 hσ
    exact PairingMoment_swap_mem_erase hσ hi₀ hσk
  · intro τ hτ
    obtain ⟨h1, h2⟩ := PairingMoment_swap_mem hτ hi₀ hks hki hkj
    exact Finset.mem_filter.2 ⟨h1, h2⟩
  · intro σ _
    exact Equiv.swap_mul_self_mul _ _ _
  · intro τ _
    exact Equiv.swap_mul_self_mul _ _ _
  · intro σ hσ
    obtain ⟨hσ, hσk⟩ := Finset.mem_filter.1 hσ
    have h := PairingMoment_prod_split hσ hi₀ hσk
      (fun i k => (if i < k then (W : ℂ)⁻¹ else 1) * (star (x i) ⬝ᵥ w k))
    rw [h, ite_eq_left hlt, ite_eq_right (not_lt.2 hlt.le)]
    ring

/-! ### Entries and traces -/

private lemma PairingMoment_entry (W : ℕ) (A : Matrix (Fin W) (Fin W) ℂ) (p q : Fin W) :
    A p q = star (Pi.single p (1 : ℂ) : Fin W → ℂ) ⬝ᵥ (A *ᵥ Pi.single q 1) := by
  simp

private lemma PairingMoment_single_dot (W : ℕ) (p q : Fin W) :
    star (Pi.single p (1 : ℂ) : Fin W → ℂ) ⬝ᵥ Pi.single q 1 = if p = q then 1 else 0 := by
  simp [Pi.single_apply, eq_comm]

/-- The real weight `∏_i c(i, σ i) [p_i = q_{σ i}]` of a pairing `σ` for the index maps `p, q`. -/
private def PairingMoment_wt (W : ℕ) {n : ℕ} (p q : Fin n → Fin W) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∏ i, (if i < σ i then (W : ℝ)⁻¹ else 1) * (if p i = q (σ i) then 1 else 0)

/-- Isserlis expansion of a product of entries of GUE blocks. -/
private lemma PairingMoment_isserlis_entry (W m n : ℕ) (j : Fin n → Fin m) (p q : Fin n → Fin W) :
    ∫ ω, ∏ i, gueBlock W m ω (j i) (p i) (q i) ∂(μ W m) =
      ∑ σ ∈ PairingMoment_pp j Finset.univ, (PairingMoment_wt W p q σ : ℂ) := by
  have h := PairingMoment_isserlis W m n j (fun i => Pi.single (p i) 1)
    (fun i => Pi.single (q i) 1) Finset.univ
  have he : (fun ω => ∏ i, gueBlock W m ω (j i) (p i) (q i)) = fun ω =>
      ∏ i, (star (Pi.single (p i) (1 : ℂ) : Fin W → ℂ) ⬝ᵥ
        (gueBlock W m ω (j i) *ᵥ Pi.single (q i) 1)) :=
    funext fun ω => Finset.prod_congr rfl fun i _ => PairingMoment_entry W _ _ _
  rw [he, h]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [PairingMoment_wt, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [PairingMoment_single_dot]
  split_ifs <;> simp

/-- Entries of a product of `k + 1` matrices as a sum over the `k` intermediate indices. -/
private lemma PairingMoment_prod_apply (W k : ℕ) (M : Fin (k + 1) → Matrix (Fin W) (Fin W) ℂ)
    (α β : Fin W) :
    (List.ofFn M).prod α β = ∑ b : Fin k → Fin W,
      ∏ i, M i ((Fin.cons α b : Fin (k + 1) → Fin W) i)
        ((Fin.snoc b β : Fin (k + 1) → Fin W) i) := by
  induction k generalizing α with
  | zero => simp [List.ofFn_succ, Fin.snoc]
  | succ k ih =>
    rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
    simp_rw [ih (fun i => M i.succ)]
    rw [← (Fin.consEquiv fun _ => Fin W).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Fin.prod_univ_succ (n := k + 1)]
    simp only [Fin.consEquiv_apply, ← Fin.cons_snoc_eq_snoc_cons, Fin.cons_zero, Fin.cons_succ]

/-- The trace of a product of `k + 1` matrices as a sum over closed index paths. -/
private lemma PairingMoment_trace (W k : ℕ) (M : Fin (k + 1) → Matrix (Fin W) (Fin W) ℂ) :
    ((List.ofFn M).prod).trace = ∑ a : Fin W × (Fin k → Fin W),
      ∏ i, M i ((Fin.cons a.1 a.2 : Fin (k + 1) → Fin W) i)
        ((Fin.snoc a.2 a.1 : Fin (k + 1) → Fin W) i) := by
  rw [Matrix.trace, Fintype.sum_prod_type]
  simp only [Matrix.diag, PairingMoment_prod_apply]

/-! ### Integrability -/

private lemma PairingMoment_integrable_poly (ι : Type*) [Fintype ι] (m : ℕ) :
    Integrable (fun x : ι → ℝ => (1 + ‖x‖) ^ m) (stdGauss ι) := by
  have hpow1 : Integrable (fun x : ℝ => (1 + |x|) ^ m) (gaussianReal 0 1) := by
    have hm : MemLp id (m : ENNReal) (gaussianReal (0 : ℝ) 1) :=
      memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := 1) m (ENNReal.natCast_ne_top m)
    have hm' : MemLp id (m : ℕ) (gaussianReal (0 : ℝ) 1) := by simpa using hm
    have h1 : Integrable (fun x : ℝ => ‖id x‖ ^ m) (gaussianReal 0 1) :=
      hm'.integrable_norm_pow'
    have h2 : Integrable (fun x : ℝ => (2 : ℝ) ^ m * (1 + |x| ^ m)) (gaussianReal 0 1) :=
      ((integrable_const (1 : ℝ)).add (by simpa using h1)).const_mul _
    refine h2.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (by fun_prop : Continuous fun x : ℝ => (1 + |x|) ^ m).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity)]
      have h2m : (0 : ℝ) ≤ 2 ^ m := by positivity
      have hx : (0 : ℝ) ≤ |x| ^ m := by positivity
      rcases le_total |x| 1 with h | h
      · calc (1 + |x|) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
          _ ≤ 2 ^ m * (1 + |x| ^ m) := by nlinarith
      · calc (1 + |x|) ^ m ≤ (2 * |x|) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
          _ = 2 ^ m * |x| ^ m := by rw [mul_pow]
          _ ≤ 2 ^ m * (1 + |x| ^ m) := by nlinarith
  have hprod : Integrable (fun x : ι → ℝ => ∏ j, (1 + |x j|) ^ m) (stdGauss ι) :=
    Integrable.fintype_prod (f := fun _ (t : ℝ) => (1 + |t|) ^ m) (fun _ => hpow1)
  refine hprod.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (by fun_prop : Continuous fun x : ι → ℝ => (1 + ‖x‖) ^ m).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity), Finset.prod_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ m
    have hone : ∀ s : Finset ι, (1 : ℝ) ≤ ∏ l ∈ s, (1 + |x l|) := fun s =>
      Finset.one_le_prod₀ fun l _ => by linarith [abs_nonneg (x l)]
    have : ‖x‖ ≤ (∏ j, (1 + |x j|)) - 1 := by
      refine (pi_norm_le_iff_of_nonneg (by linarith [hone Finset.univ])).mpr fun j => ?_
      have hj : 1 + |x j| ≤ ∏ l, (1 + |x l|) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
        exact le_mul_of_one_le_right (by positivity) (hone _)
      rw [Real.norm_eq_abs]
      linarith
    linarith

private lemma PairingMoment_norm_entry_le (W m : ℕ) (ω : Ω W m) (a : Fin m) (α β : Fin W) :
    ‖gueBlock W m ω a α β‖ ≤ 2 * (1 + ‖ω‖) := by
  have hW : (1 : ℝ) ≤ W := by exact_mod_cast Fin.pos α
  have h1 : 1 ≤ Real.sqrt W := Real.one_le_sqrt.2 hW
  have h2 : 1 ≤ Real.sqrt (2 * W) := Real.one_le_sqrt.2 (by linarith)
  have hc : ∀ c, |ω c| ≤ ‖ω‖ := fun c => by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm ω c
  have hdiv : ∀ (z : ℂ) (r : ℝ), 1 ≤ r → ‖z / (r : ℂ)‖ ≤ ‖z‖ := fun z r hr => by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    exact div_le_self (norm_nonneg _) hr
  have hn : 0 ≤ ‖ω‖ := norm_nonneg ω
  simp only [gueBlock, Matrix.of_apply]
  split_ifs
  · refine (hdiv _ _ h1).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith [hc (a, α, α)]
  · refine (hdiv _ _ h2).trans ?_
    calc ‖(ω (a, α, β) : ℂ) + Complex.I * ω (a, β, α)‖
        ≤ ‖(ω (a, α, β) : ℂ)‖ + ‖Complex.I * ω (a, β, α)‖ := norm_add_le _ _
      _ = |ω (a, α, β)| + |ω (a, β, α)| := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 2 * (1 + ‖ω‖) := by linarith [hc (a, α, β), hc (a, β, α)]
  · refine (hdiv _ _ h2).trans ?_
    calc ‖(ω (a, β, α) : ℂ) - Complex.I * ω (a, α, β)‖
        ≤ ‖(ω (a, β, α) : ℂ)‖ + ‖Complex.I * ω (a, α, β)‖ := norm_sub_le _ _
      _ = |ω (a, β, α)| + |ω (a, α, β)| := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 2 * (1 + ‖ω‖) := by linarith [hc (a, α, β), hc (a, β, α)]

private lemma PairingMoment_integrable_prod (W m n : ℕ) (j : Fin n → Fin m)
    (p q : Fin n → Fin W) :
    Integrable (fun ω => ∏ i, gueBlock W m ω (j i) (p i) (q i)) (μ W m) := by
  have hcont : Continuous fun ω : Ω W m => ∏ i, gueBlock W m ω (j i) (p i) (q i) := by
    refine continuous_finsetProd _ fun i _ => ?_
    simp only [gueBlock, Matrix.of_apply]
    split_ifs <;> fun_prop
  rw [μ_eq_stdGauss]
  refine ((PairingMoment_integrable_poly _ n).const_mul (2 ^ n)).mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [norm_prod]
  calc ∏ i, ‖gueBlock W m ω (j i) (p i) (q i)‖ ≤ ∏ _i : Fin n, 2 * (1 + ‖ω‖) :=
        Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
          (fun i _ => PairingMoment_norm_entry_le W m ω _ _ _)
    _ = 2 ^ n * (1 + ‖ω‖) ^ n := by simp [Finset.prod_const, mul_pow]

/-! ### Regrouping by pairings -/

/-- The weight of a pairing `σ` of `Fin (k + 1)` summed over closed index paths. -/
private def PairingMoment_F (W k : ℕ) (σ : Equiv.Perm (Fin (k + 1))) : ℝ :=
  ∑ a : Fin W × (Fin k → Fin W), PairingMoment_wt W (Fin.cons a.1 a.2 : Fin (k + 1) → Fin W)
    (Fin.snoc a.2 a.1 : Fin (k + 1) → Fin W) σ

private lemma PairingMoment_expand (W m k : ℕ) (j : Fin (k + 1) → Fin m) :
    ∫ ω, ((List.ofFn fun i => gueBlock W m ω (j i)).prod).trace ∂(μ W m) =
      ∑ σ ∈ PairingMoment_pp j Finset.univ, (PairingMoment_F W k σ : ℂ) := by
  simp_rw [PairingMoment_trace]
  rw [integral_finsetSum _ fun a _ => PairingMoment_integrable_prod W m (k + 1) j _ _]
  simp_rw [PairingMoment_isserlis_entry]
  rw [Finset.sum_comm]
  simp [PairingMoment_F, Complex.ofReal_sum]

private lemma PairingMoment_pp_min {n : ℕ} {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ pairings n) :
    PairingMoment_pp (fun i => min i (σ i)) Finset.univ = {σ} := by
  simp only [pairings, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
  ext τ
  simp only [PairingMoment_mem_pp, Finset.mem_univ, Finset.mem_singleton, true_implies,
    not_true_eq_false, false_implies, and_true, true_and]
  constructor
  · intro h
    ext i
    obtain ⟨hne, -, hj⟩ := h i
    rcases min_choice (τ i) (σ (τ i)) with h1 | h1 <;>
      rcases min_choice i (σ i) with h2 | h2 <;> rw [h1, h2] at hj
    · exact absurd hj hne
    · exact congrArg Fin.val hj
    · exact congrArg Fin.val (((hσ _).1).symm.trans (by rw [hj]))
    · exact absurd (σ.injective hj) hne
  · rintro rfl i
    exact ⟨(hσ i).2, (hσ i).1, by rw [(hσ i).1, min_comm]⟩

private lemma PairingMoment_pp_univ {n m : ℕ} (j : Fin n → Fin m) :
    PairingMoment_pp j Finset.univ = (pairings n).filter (fun σ => ∀ i, j (σ i) = j i) := by
  ext σ
  simp only [PairingMoment_mem_pp, pairings, Finset.mem_filter, Finset.mem_univ, true_and,
    true_implies, not_true_eq_false, false_implies, and_true]
  constructor
  · intro h
    exact ⟨fun i => ⟨(h i).2.1, (h i).1⟩, fun i => (h i).2.2⟩
  · rintro ⟨h1, h2⟩ i
    exact ⟨(h1 i).2, (h1 i).1, h2 i⟩

/-- The weight of a pairing `σ` of `Fin n`: `𝔼 Tr(G_{c_0} ⋯ G_{c_{n-1}})` with `c_i = min(i, σ i)`,
one independent GUE block of (1.2) [eq:covariance] per pair. -/
def pairWeight (W : ℕ) {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℂ :=
  ∫ ω, ((List.ofFn fun i => gueBlock W n ω (min i (σ i))).prod).trace ∂(μ W n)

/-- The weight of a pairing of `Fin (k + 1)` is the real path sum `PairingMoment_F`. -/
private lemma PairingMoment_pairWeight_eq (W k : ℕ) {σ : Equiv.Perm (Fin (k + 1))}
    (hσ : σ ∈ pairings (k + 1)) : pairWeight W σ = (PairingMoment_F W k σ : ℂ) := by
  rw [pairWeight, PairingMoment_expand W (k + 1) k (fun i => min i (σ i)),
    PairingMoment_pp_min hσ, Finset.sum_singleton]

/-- Pairing expansion of a GUE word, (1.2) [eq:covariance]:
`𝔼 Tr(G_{j_0} ⋯ G_{j_{n-1}}) = Σ_{σ ∈ pairings n, j∘σ = j} w_W(σ)`. -/
theorem integral_trace_prod_gueBlock (W m n : ℕ) (j : Fin n → Fin m) :
    ∫ ω, ((List.ofFn fun i => gueBlock W m ω (j i)).prod).trace ∂(μ W m) =
      ∑ σ ∈ (pairings n).filter (fun σ => ∀ i, j (σ i) = j i), pairWeight W σ := by
  cases n with
  | zero =>
    have h1 : (pairings 0).filter (fun σ => ∀ i, j (σ i) = j i) = {1} := by
      ext σ
      simp [pairings, Subsingleton.elim σ 1]
    rw [h1, Finset.sum_singleton]
    simp [pairWeight]
  | succ k =>
    rw [PairingMoment_expand, PairingMoment_pp_univ]
    exact Finset.sum_congr rfl fun σ hσ =>
      (PairingMoment_pairWeight_eq W k (Finset.mem_filter.1 hσ).1).symm

/-- The weight of a pairing is real and nonnegative. -/
theorem pairWeight_nonneg (W : ℕ) {n : ℕ} {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ pairings n) :
    0 ≤ (pairWeight W σ).re ∧ (pairWeight W σ).im = 0 := by
  cases n with
  | zero => simp [pairWeight]
  | succ k =>
    rw [PairingMoment_pairWeight_eq W k hσ, Complex.ofReal_re, Complex.ofReal_im]
    refine ⟨Finset.sum_nonneg fun a _ => Finset.prod_nonneg fun i _ => mul_nonneg ?_ ?_, rfl⟩
    · split_ifs <;> positivity
    · split_ifs <;> norm_num

end LSBA
