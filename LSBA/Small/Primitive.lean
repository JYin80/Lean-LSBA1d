import LSBA.Small.Molecule
import LSBA.Primitive.Bounded

/-!
# Sharp primitive loop bounds

Proposition B.2 [ba:prop:primitive] and the bound (5.20) [fo:eq:primitivebound] of Lemma 5.2
[fo:lem:deterministic](a) without the factor `(1 + g^{-2})^{k-2}`: `|𝒦_k(t)| ≤ C' ζ_t^{k-1}` on
`0 < g ≤ C`, and the primitive slot `|𝒦_k| ≤ W^δ ζ_t^{k-1}` of the general Theorem 5.12
[gc:thm:common] for `2 ≤ k ≤ k_max`.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ## The single-molecule step with the cancellation `(1 - t) + g² Σ_j |n_j|²`

With (B.3) [ba:eq:cancel] in the form `|Ŝ_t(n)| ≤ C'((1 - t) + g² Σ_j |n_j|²_𝕋)` and the
coercivity (A.25) [ba:eq:coercivity], an alternating molecule cancels one mixed leg at the cost
`k`, with no factor `1 + g⁻²`. -/

section Base

variable {L : ℕ}

/-- The coercivity step: `δ + g² Σ_j τ_j² ≤ k Σ_{j ≠ v} (δ + g²τ_j²)` when
`τ_v ≤ Σ_{j ≠ v} τ_j`. -/
private lemma sharp_coer {k : ℕ} (hk : 2 ≤ k) {g δ : ℝ} (hδ : 0 ≤ δ) (τ : Fin k → ℝ)
    (hτ : ∀ j, 0 ≤ τ j) (v : Fin k) (htri : τ v ≤ ∑ j ∈ Finset.univ.erase v, τ j) :
    δ + g ^ 2 * ∑ j, τ j ^ 2 ≤ k * ∑ j ∈ Finset.univ.erase v, (δ + g ^ 2 * τ j ^ 2) := by
  have hcard : ((Finset.univ.erase v).card : ℝ) = k - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
    have : 1 ≤ k := by omega
    push_cast [this]
    ring
  set T := ∑ j ∈ Finset.univ.erase v, τ j ^ 2 with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hsq : τ v ^ 2 ≤ (k - 1) * T := by
    have h0 : 0 ≤ τ v := hτ v
    calc τ v ^ 2 ≤ (∑ j ∈ Finset.univ.erase v, τ j) ^ 2 := pow_le_pow_left₀ h0 htri 2
      _ ≤ ((Finset.univ.erase v).card : ℝ) * T := sq_sum_le_card_mul_sum_sq
      _ = (k - 1) * T := by rw [hcard]
  have hsum : ∑ j, τ j ^ 2 = τ v ^ 2 + T :=
    (Finset.add_sum_erase _ (fun j => τ j ^ 2) (Finset.mem_univ v)).symm
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hR : ∑ j ∈ Finset.univ.erase v, (δ + g ^ 2 * τ j ^ 2) = (k - 1) * δ + g ^ 2 * T := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard, ← Finset.mul_sum]
  rw [hsum, hR]
  have hg2 : 0 ≤ g ^ 2 := sq_nonneg g
  have h1 : δ ≤ k * (k - 1) * δ := by
    have : (1 : ℝ) ≤ k * (k - 1) := by nlinarith
    nlinarith
  have h2 : g ^ 2 * (τ v ^ 2 + T) ≤ k * (g ^ 2 * T) := by
    have : τ v ^ 2 + T ≤ k * T := by nlinarith
    nlinarith
  nlinarith

/-- The marginal of an alternating molecule with the cancellation `δ + g² Σ_j τ_j²`. -/
private lemma sharp_alt_marg [NeZero L] {k : ℕ} (hk : 3 ≤ k) (S : (Fin k → Fin L) → ℂ)
    (hsupp : ∀ n, ∑ j, n j ≠ 0 → tensorFourier S n = 0) {U : Fin L → ℝ} {CU Kb g δ : ℝ}
    (hU : ∀ q, 0 ≤ U q) (hKb : 0 ≤ Kb) (hδ : 0 ≤ δ)
    (hcoer : ∀ q, U q * (δ + g ^ 2 * torusAbs L q ^ 2) ≤ CU)
    (hS2 : ∀ n, ∑ j, n j = 0 →
      ‖tensorFourier S n‖ ≤ Kb * (δ + g ^ 2 * ∑ j, torusAbs L (n j) ^ 2))
    (v : Fin k) (q : Fin L) :
    bnd_N (Function.update (fun _ => U) v (bnd_del q)) S ≤
      Kb * k * CU * ((k - 1) * (∑ x, U x) ^ (k - 2)) := by
  set wv : Fin k → Fin L → ℝ := Function.update (fun _ => U) v (bnd_del q) with hwv
  have hwv_ne : ∀ j, j ≠ v → wv j = U := fun j hj => by rw [hwv, Function.update_of_ne hj]
  have hwv_v : wv v = bnd_del q := by rw [hwv, Function.update_self]
  -- the pointwise estimate on `Σ_j n_j = 0`
  have hpt : ∀ n : Fin k → Fin L, ∑ j, n j = 0 →
      (∏ j, wv j (n j)) * ‖tensorFourier S n‖ ≤ Kb * k * CU *
        ∑ i ∈ Finset.univ.erase v, ∏ j, (if j = i then 1 else wv j (n j)) := by
    intro n hn
    have hterm : ∀ i ∈ Finset.univ.erase v, ∏ j, (if j = i then 1 else wv j (n j)) =
        bnd_del q (n v) * ∏ j ∈ (Finset.univ.erase v).erase i, U (n j) := by
      intro i hi
      have hiv := Finset.ne_of_mem_erase hi
      rw [bnd_prod_ite_one, ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hiv,
        Finset.mem_univ v⟩), hwv_v, Finset.erase_right_comm]
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [hwv_ne j (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj))]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hlhs : ∏ j, wv j (n j) = bnd_del q (n v) * ∏ j ∈ Finset.univ.erase v, U (n j) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v), hwv_v]
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [hwv_ne j (Finset.ne_of_mem_erase hj)]
    rw [hlhs]
    have hd0 := bnd_del_nonneg q (n v)
    have hP0 : 0 ≤ ∏ j ∈ Finset.univ.erase v, U (n j) := Finset.prod_nonneg fun j _ => hU _
    have hτ0 : ∀ j, 0 ≤ torusAbs L (n j) := fun j => by unfold torusAbs; positivity
    have hco := sharp_coer (g := g) (by omega) hδ (fun j => torusAbs L (n j)) hτ0 v
      (bnd_torus_tri n hn v)
    have hkey : (∏ j ∈ Finset.univ.erase v, U (n j)) * ‖tensorFourier S n‖ ≤
        Kb * k * CU *
          ∑ i ∈ Finset.univ.erase v, ∏ j ∈ (Finset.univ.erase v).erase i, U (n j) := by
      calc (∏ j ∈ Finset.univ.erase v, U (n j)) * ‖tensorFourier S n‖
          ≤ (∏ j ∈ Finset.univ.erase v, U (n j)) *
              (Kb * (δ + g ^ 2 * ∑ j, torusAbs L (n j) ^ 2)) :=
            mul_le_mul_of_nonneg_left (hS2 n hn) hP0
        _ ≤ (∏ j ∈ Finset.univ.erase v, U (n j)) * (Kb * (k *
              ∑ i ∈ Finset.univ.erase v, (δ + g ^ 2 * torusAbs L (n i) ^ 2))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hco hKb) hP0
        _ = Kb * k * ∑ i ∈ Finset.univ.erase v, (∏ j ∈ Finset.univ.erase v, U (n j)) *
              (δ + g ^ 2 * torusAbs L (n i) ^ 2) := by
            rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
        _ ≤ Kb * k * ∑ i ∈ Finset.univ.erase v, CU *
              ∏ j ∈ (Finset.univ.erase v).erase i, U (n j) := by
            have hk0 : (0 : ℝ) ≤ Kb * k := by positivity
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) hk0
            rw [← Finset.mul_prod_erase _ _ hi]
            have hQ : 0 ≤ ∏ j ∈ (Finset.univ.erase v).erase i, U (n j) :=
              Finset.prod_nonneg fun j _ => hU _
            calc U (n i) * (∏ j ∈ (Finset.univ.erase v).erase i, U (n j)) *
                  (δ + g ^ 2 * torusAbs L (n i) ^ 2)
                = (U (n i) * (δ + g ^ 2 * torusAbs L (n i) ^ 2)) *
                    ∏ j ∈ (Finset.univ.erase v).erase i, U (n j) := by ring
              _ ≤ CU * ∏ j ∈ (Finset.univ.erase v).erase i, U (n j) :=
                  mul_le_mul_of_nonneg_right (hcoer _) hQ
        _ = Kb * k * CU * ∑ i ∈ Finset.univ.erase v,
              ∏ j ∈ (Finset.univ.erase v).erase i, U (n j) := by
            rw [← Finset.mul_sum]; ring
    calc bnd_del q (n v) * (∏ j ∈ Finset.univ.erase v, U (n j)) * ‖tensorFourier S n‖
        = bnd_del q (n v) * ((∏ j ∈ Finset.univ.erase v, U (n j)) * ‖tensorFourier S n‖) := by
          ring
      _ ≤ bnd_del q (n v) * (Kb * k * CU *
            ∑ i ∈ Finset.univ.erase v, ∏ j ∈ (Finset.univ.erase v).erase i, U (n j)) :=
          mul_le_mul_of_nonneg_left hkey hd0
      _ = _ := by ring
  -- summing over the momenta
  have hsum : bnd_N wv S ≤ Kb * k * CU * ∑ i ∈ Finset.univ.erase v,
      ∑ n : Fin k → Fin L,
        (if ∑ j, n j = 0 then ∏ j, (if j = i then 1 else wv j (n j)) else 0) := by
    unfold bnd_N
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    by_cases hn : ∑ j, n j = 0
    · simp only [ite_eq_left hn]
      exact hpt n hn
    · simp only [ite_eq_right hn, Finset.sum_const_zero, mul_zero]
      rw [hsupp n hn, norm_zero, mul_zero]
  refine hsum.trans (le_of_eq ?_)
  have hval : ∀ i ∈ Finset.univ.erase v,
      ∑ n : Fin k → Fin L, (if ∑ j, n j = 0 then ∏ j, (if j = i then 1 else wv j (n j)) else 0) =
        (∑ x, U x) ^ (k - 2) := by
    intro i hi
    have hiv := Finset.ne_of_mem_erase hi
    rw [bnd_sum_constraint_prod i wv]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hiv, Finset.mem_univ v⟩),
      hwv_v]
    have h1 : ∑ x, bnd_del q x = 1 := by
      have := bnd_sum_del q (fun _ => 1); simpa using this
    rw [h1, one_mul]
    rw [Finset.prod_congr rfl fun j hj => by
      rw [hwv_ne j (Finset.ne_of_mem_erase hj)]]
    rw [Finset.prod_const]
    congr 1
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hiv, Finset.mem_univ v⟩),
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
  push_cast [show 1 ≤ k by omega]
  ring

/-- The norm and the mixed-leg marginals of a stable molecule with the cancellation
`δ + g² Σ_j τ_j²` (single-molecule step of Proposition B.2 [ba:prop:primitive]). -/
private lemma sharp_base [NeZero L] {k : ℕ} (hk : 3 ≤ k) (S : (Fin k → Fin L) → ℂ)
    (hS : ∀ (y : Fin k → Fin L) (c : Fin L), S (fun i => y i + c) = S y) (σ : Fin k → Bool)
    {U : Fin L → ℝ} {Cs CU Kb g δ : ℝ} (hU : ∀ q, 1 / 2 ≤ U q) (hCs : 1 ≤ Cs) (hKb : 0 ≤ Kb)
    (hδ : 0 ≤ δ) (hcoer : ∀ q, U q * (δ + g ^ 2 * torusAbs L q ^ 2) ≤ CU)
    (hS1 : ∀ n, ‖tensorFourier S n‖ ≤ Kb)
    (hS2 : (∀ i, σ (finRotate k i) = !σ i) → ∀ n, ∑ j, n j = 0 →
      ‖tensorFourier S n‖ ≤ Kb * (δ + g ^ 2 * ∑ j, torusAbs L (n j) ^ 2)) :
    bnd_N (bnd_w U Cs σ) S ≤ bnd_KB k Cs CU Kb * (∑ q, U q) ^ (k - 1) ∧
      ∀ v, σ v ≠ σ (finRotate k v) → ∀ q,
        bnd_N (Function.update (bnd_w U Cs σ) v (bnd_del q)) S ≤
          bnd_KB k Cs CU Kb * (∑ q, U q) ^ (k - 2) := by
  have hU0 : ∀ q, 0 ≤ U q := fun q => le_trans (by norm_num) (hU q)
  have hCU : 0 ≤ CU := le_trans (mul_nonneg (hU0 0) (by unfold torusAbs; positivity)) (hcoer 0)
  set H := ∑ q, U q with hH
  have hHL : (L : ℝ) / 2 ≤ H := by
    have : ∑ q : Fin L, (1 / 2 : ℝ) ≤ H := Finset.sum_le_sum fun q _ => hU q
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    linarith
  have hH0 : 0 ≤ H := le_trans (by positivity) hHL
  have hsupp : ∀ n, ∑ j, n j ≠ 0 → tensorFourier S n = 0 := bnd_tf_support S hS
  have hw0 : ∀ j x, 0 ≤ bnd_w U Cs σ j x := bnd_w_nonneg hU0 (by linarith) σ
  have hKB0 : 0 ≤ Kb * ((k : ℝ) ^ 2 * CU) := by positivity
  have hKB1 : 0 ≤ Kb * (Cs * (2 * Cs) ^ k) := by
    have : 0 ≤ Cs := by linarith
    positivity
  have hKB : bnd_KB k Cs CU Kb = Kb * ((k : ℝ) ^ 2 * CU) + Kb * (Cs * (2 * Cs) ^ k) := by
    unfold bnd_KB; ring
  by_cases halt : ∀ i, σ (finRotate k i) = !σ i
  · -- alternating: every leg is mixed
    have hwU : bnd_w U Cs σ = fun _ => U := by
      funext j x
      unfold bnd_w
      rw [halt j]
      cases σ j <;> simp
    have hS2' := hS2 halt
    have hmarg : ∀ v q, bnd_N (Function.update (bnd_w U Cs σ) v (bnd_del q)) S ≤
        Kb * k * CU * ((k - 1) * H ^ (k - 2)) := by
      intro v q
      rw [hwU]
      exact sharp_alt_marg hk S hsupp hU0 hKb hδ hcoer hS2' v q
    have hM0 : Kb * k * CU * ((k - 1) * H ^ (k - 2)) ≤ bnd_KB k Cs CU Kb * H ^ (k - 2) := by
      rw [hKB]
      have hk1 : (k : ℝ) * (k - 1) ≤ (k : ℝ) ^ 2 := by nlinarith
      have hHk : 0 ≤ H ^ (k - 2) := pow_nonneg hH0 _
      have h1 : Kb * k * CU * ((k - 1) * H ^ (k - 2)) =
          (Kb * (k * (k - 1)) * CU) * H ^ (k - 2) := by ring
      rw [h1]
      have h3 : Kb * (k * (k - 1)) * CU ≤ Kb * ((k : ℝ) ^ 2 * CU) := by
        have := mul_le_mul_of_nonneg_right hk1 hCU
        nlinarith
      exact mul_le_mul_of_nonneg_right (by linarith) hHk
    refine ⟨?_, fun v _ q => (hmarg v q).trans hM0⟩
    have hv0 : 0 < k := by omega
    have hN : bnd_N (bnd_w U Cs σ) S = ∑ x, U x *
        bnd_N (Function.update (bnd_w U Cs σ) ⟨0, hv0⟩ (bnd_del x)) S := by
      rw [bnd_N_update_sum]
      congr 1
      rw [hwU]
      exact (Function.update_eq_self _ _).symm
    rw [hN]
    calc ∑ x, U x * bnd_N (Function.update (bnd_w U Cs σ) ⟨0, hv0⟩ (bnd_del x)) S
        ≤ ∑ x, U x * (bnd_KB k Cs CU Kb * H ^ (k - 2)) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
            ((hmarg _ x).trans hM0) (hU0 x)
      _ = bnd_KB k Cs CU Kb * H ^ (k - 1) := by
          rw [← Finset.sum_mul, ← hH]
          have : H ^ (k - 1) = H * H ^ (k - 2) := by
            rw [← pow_succ']; congr 1; omega
          rw [this]; ring
  · -- a stable leg `s`
    push Not at halt
    obtain ⟨s, hs⟩ := halt
    have hss : σ s = σ (finRotate k s) := by
      cases h1 : σ s <;> cases h2 : σ (finRotate k s) <;> simp_all
    have hws : ∀ x, bnd_w U Cs σ s x = Cs := fun x => by unfold bnd_w; rw [ite_eq_left hss]
    have hrow : ∀ j, ∑ x, bnd_w U Cs σ j x ≤ 2 * Cs * H := by
      intro j
      unfold bnd_w
      split_ifs
      · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        nlinarith
      · nlinarith
    have hrow0 : ∀ j, 0 ≤ ∑ x, bnd_w U Cs σ j x := fun j => Finset.sum_nonneg fun x _ => hw0 j x
    have hCs0 : 0 ≤ Cs := by linarith
    have hfin : ∀ m : ℕ, m ≤ k → Cs * Kb * (2 * Cs * H) ^ m ≤ bnd_KB k Cs CU Kb * H ^ m := by
      intro m hm
      rw [hKB, mul_pow]
      have h1 : (2 * Cs) ^ m ≤ (2 * Cs) ^ k := pow_le_pow_right₀ (by linarith) hm
      have hHm : 0 ≤ H ^ m := pow_nonneg hH0 m
      have h2 : Cs * Kb * ((2 * Cs) ^ m * H ^ m) ≤ Kb * (Cs * (2 * Cs) ^ k) * H ^ m := by
        have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hCs0 hKb)
        nlinarith
      refine h2.trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith) hHm
    refine ⟨?_, fun v hv q => ?_⟩
    · refine (bnd_N_stableLeg S hsupp hS1 _ hw0 s hws).trans ?_
      refine le_trans ?_ (hfin (k - 1) (by omega))
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCs0 hKb)
      have := bnd_prod_le_pow (Finset.univ.erase s) (fun j => ∑ x, bnd_w U Cs σ j x) (2 * Cs * H)
        (fun j _ => hrow0 j) (fun j _ => hrow j)
      rwa [Finset.card_erase_of_mem (Finset.mem_univ s), Finset.card_univ,
        Fintype.card_fin] at this
    · have hvs : v ≠ s := fun h => hv (h ▸ hss)
      have hw0' := bnd_update_nonneg hw0 (bnd_del_nonneg q) (v := v)
      have hws' : ∀ x, Function.update (bnd_w U Cs σ) v (bnd_del q) s x = Cs := fun x => by
        rw [Function.update_of_ne hvs.symm, hws]
      refine (bnd_N_stableLeg S hsupp hS1 _ hw0' s hws').trans ?_
      refine le_trans ?_ (hfin (k - 2) (by omega))
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCs0 hKb)
      have hvmem : v ∈ Finset.univ.erase s := Finset.mem_erase.mpr ⟨hvs, Finset.mem_univ v⟩
      rw [← Finset.mul_prod_erase _ _ hvmem, Function.update_self]
      have h1 : ∑ x, bnd_del q x = 1 := by
        have := bnd_sum_del q (fun _ => 1); simpa using this
      rw [h1, one_mul]
      have := bnd_prod_le_pow ((Finset.univ.erase s).erase v)
        (fun j => ∑ x, Function.update (bnd_w U Cs σ) v (bnd_del q) j x) (2 * Cs * H)
        (fun j _ => Finset.sum_nonneg fun x _ => hw0' j x)
        (fun j hj => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
          exact hrow j)
      rwa [Finset.card_erase_of_mem hvmem, Finset.card_erase_of_mem (Finset.mem_univ s),
        Finset.card_univ, Fintype.card_fin, show k - 1 - 1 = k - 2 by omega] at this

end Base

/-! ## Induction along the molecule tree

The norms (B.4) [ba:eq:norms] of the graded cores by induction on the length, with the
single-molecule step above as base; a mixed diagonal glues two shorter graded cores with the
link `β t V_t`. -/

section Induct

variable {L : ℕ}

/-- The norms of the graded cores, by induction on the length (Proposition B.2
[ba:prop:primitive], norms (B.4) [ba:eq:norms]), with the cancellation `δ + g² Σ_j τ_j²`. -/
private lemma sharp_induct [NeZero L] (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (t : ℝ)
    {U : Fin L → ℝ} {Cs CU Kb g δ : ℝ} (hU : ∀ q, 1 / 2 ≤ U q) (hCs : 1 ≤ Cs) (hKb : 0 ≤ Kb)
    (hδ : 0 ≤ δ) (hcoer : ∀ q, U q * (δ + g ^ 2 * torusAbs L q ^ 2) ≤ CU)
    (hβt0 : 0 ≤ β * t) (hβt1 : β * t ≤ 1)
    (hVc : ∀ a a' c : Fin L, (1 - t • pairP β M)⁻¹ (a + c) (a' + c) = (1 - t • pairP β M)⁻¹ a a')
    (hVhat : ∀ q, ‖∑ u, (((1 - t • pairP β M)⁻¹ 0 u : ℝ) : ℂ) * bnd_chi L q u‖ ≤ U q)
    (kmax : ℕ)
    (hST : ∀ (k : ℕ) (σ : Fin k → Bool) (y : Fin k → Fin L) (c : Fin L),
      stableMol β M t σ (fun i => y i + c) = stableMol β M t σ y)
    (hS1 : ∀ k, 3 ≤ k → k ≤ kmax → ∀ (σ : Fin k → Bool) n,
      ‖tensorFourier (stableMol β M t σ) n‖ ≤ Kb)
    (hS2 : ∀ k, 3 ≤ k → k ≤ kmax → ∀ σ : Fin k → Bool, (∀ i, σ (finRotate k i) = !σ i) →
      ∀ n, ∑ j, n j = 0 →
        ‖tensorFourier (stableMol β M t σ) n‖ ≤
          Kb * (δ + g ^ 2 * ∑ j, torusAbs L (n j) ^ 2)) :
    ∀ k, 3 ≤ k → k ≤ kmax → ∀ (σ : Fin k → Bool) (r : ℕ),
      bnd_N (bnd_w U Cs σ) (bnd_Cr β M t σ r) ≤ bnd_Kseq (fun n => bnd_KB n Cs CU Kb) k *
          (∑ q, U q) ^ (k - 1) ∧
        ∀ v, σ v ≠ σ (finRotate k v) → ∀ q,
          bnd_N (Function.update (bnd_w U Cs σ) v (bnd_del q)) (bnd_Cr β M t σ r) ≤
            bnd_Kseq (fun n => bnd_KB n Cs CU Kb) k * (∑ q, U q) ^ (k - 2) := by
  set A : ℕ → ℝ := fun n => bnd_KB n Cs CU Kb with hA
  have hU0 : ∀ q, 0 ≤ U q := fun q => le_trans (by norm_num) (hU q)
  have hCU : 0 ≤ CU := le_trans (mul_nonneg (hU0 0) (by unfold torusAbs; positivity)) (hcoer 0)
  have hA0 : ∀ n, 0 ≤ A n := fun n => by
    simp only [hA, bnd_KB]
    have : 0 ≤ Cs := by linarith
    positivity
  set H := ∑ q, U q with hH
  have hH0 : 0 ≤ H := Finset.sum_nonneg fun q _ => hU0 q
  have hCs0 : 0 ≤ Cs := by linarith
  have hw0 : ∀ {k : ℕ} (σ : Fin k → Bool) s x, 0 ≤ bnd_w U Cs σ s x :=
    fun σ => bnd_w_nonneg hU0 hCs0 σ
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  intro hk hkmax σ r
  have hK0 := bnd_Kseq_nonneg A hA0
  have hbound0 : ∀ m, 0 ≤ bnd_Kseq A k * H ^ m := fun m => by
    have := hK0 k; positivity
  -- grade zero: the stable molecule
  rcases Nat.eq_zero_or_pos r with hr0 | hr1
  · subst hr0
    rw [bnd_Cr_zero]
    obtain ⟨h1, h2⟩ := sharp_base hk (stableMol β M t σ) (hST k σ) σ hU hCs hKb hδ hcoer
      (hS1 k hk hkmax σ) (hS2 k hk hkmax σ)
    have hle : ∀ m, bnd_KB k Cs CU Kb * H ^ m ≤ bnd_Kseq A k * H ^ m := fun m =>
      mul_le_mul_of_nonneg_right (bnd_Kseq_base A k) (pow_nonneg hH0 _)
    exact ⟨h1.trans (hle _), fun v hv q => (h2 v hv q).trans (hle _)⟩
  -- grades beyond `k²` vanish
  rcases Nat.lt_or_ge (k * k) r with hbig | hsmall
  · rw [bnd_Cr_big β M t σ hbig]
    exact ⟨by rw [bnd_N_zero]; exact hbound0 _, fun _ _ _ => by rw [bnd_N_zero]; exact hbound0 _⟩
  -- the gluing step
  set K' := bnd_Kseq A (k - 1) with hK'
  have hK'0 : 0 ≤ K' := hK0 _
  set D := (polyDiags k).filter (fun d => σ d.1 ≠ σ d.2) with hD
  set T : (Fin k × Fin k) × ℕ → (Fin k → Fin L) → ℂ := fun x =>
    bnd_glueT x.1.1 x.1.2 (((β * t : ℝ) : ℂ) • pairV β M t (σ x.1.1) (σ x.1.2))
      (bnd_Cr β M t (cutLSgn σ x.1.1 x.1.2) x.2)
      (bnd_Cr β M t (cutRSgn σ x.1.1 x.1.2) (r - 1 - x.2)) with hT
  have hdom : ∀ n, ‖tensorFourier (bnd_Cr β M t σ r) n‖ ≤
      ∑ x ∈ D ×ˢ Finset.range r, ‖tensorFourier (T x) n‖ := by
    intro n
    have hrec := bnd_Cr_rec β M t σ r
    have h1 : (r : ℂ) * tensorFourier (bnd_Cr β M t σ r) n =
        ∑ d ∈ D, ∑ rL ∈ Finset.range r, tensorFourier (T (d, rL)) n := by
      rw [← bnd_tf_smul, funext hrec, bnd_tf_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [bnd_tf_sum]
    have h2 : ‖tensorFourier (bnd_Cr β M t σ r) n‖ ≤
        ‖(r : ℂ) * tensorFourier (bnd_Cr β M t σ r) n‖ := by
      rw [norm_mul, Complex.norm_natCast]
      have : (1 : ℝ) ≤ r := by exact_mod_cast hr1
      nlinarith [norm_nonneg (tensorFourier (bnd_Cr β M t σ r) n)]
    refine h2.trans ?_
    rw [h1, Finset.sum_product]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => norm_sum_le _ _)
  have hcard : ((D ×ˢ Finset.range r).card : ℝ) ≤ (k : ℝ) ^ 4 := by
    rw [Finset.card_product, Finset.card_range]
    have h1 : D.card ≤ k * k := by
      refine (Finset.card_filter_le _ _).trans ?_
      have := Finset.card_le_univ (polyDiags k)
      simpa [Fintype.card_prod, Fintype.card_fin] using this
    have h2 : D.card * r ≤ k ^ 4 := by
      calc D.card * r ≤ (k * k) * (k * k) := Nat.mul_le_mul h1 hsmall
        _ = k ^ 4 := by ring
    exact_mod_cast h2
  -- each glued term
  have hterm : ∀ x ∈ D ×ˢ Finset.range r,
      bnd_N (bnd_w U Cs σ) (T x) ≤ K' ^ 2 * H ^ (k - 1) ∧
        ∀ v, σ v ≠ σ (finRotate k v) → ∀ q,
          bnd_N (Function.update (bnd_w U Cs σ) v (bnd_del q)) (T x) ≤ K' ^ 2 * H ^ (k - 2) := by
    rintro ⟨⟨i, j⟩, rL⟩ hx
    rw [Finset.mem_product, hD, Finset.mem_filter] at hx
    obtain ⟨⟨hd, hmix⟩, -⟩ := hx
    have hdv := (bnd_mem_polyDiags _).mp hd
    simp only at hdv hmix
    have hj := j.isLt
    have hkL3 : 3 ≤ k + (i : ℕ) - (j : ℕ) + 1 := by omega
    have hkLk : k + (i : ℕ) - (j : ℕ) + 1 < k := by omega
    have hkR3 : 3 ≤ (j : ℕ) - (i : ℕ) + 1 := by omega
    have hkRk : (j : ℕ) - (i : ℕ) + 1 < k := by omega
    obtain ⟨hLN, hLm⟩ := IH _ hkLk hkL3 (by omega) (cutLSgn σ i j) rL
    obtain ⟨hRN, hRm⟩ := IH _ hkRk hkR3 (by omega) (cutRSgn σ i j) (r - 1 - rL)
    have hKL : bnd_Kseq A (k + (i : ℕ) - (j : ℕ) + 1) ≤ K' := bnd_Kseq_mono A (by omega)
    have hKR : bnd_Kseq A ((j : ℕ) - (i : ℕ) + 1) ≤ K' := bnd_Kseq_mono A (by omega)
    have hmono : ∀ m e', bnd_Kseq A m ≤ K' → bnd_Kseq A m * H ^ e' ≤ K' * H ^ e' :=
      fun m e' h => mul_le_mul_of_nonneg_right h (pow_nonneg hH0 _)
    obtain ⟨g1, g2⟩ := bnd_glue_one hd hmix β M t hU0 hCs0 hβt0 hβt1 hVc hVhat
      (bnd_Cr β M t (cutLSgn σ i j) rL) (bnd_Cr β M t (cutRSgn σ i j) (r - 1 - rL))
      (aM := K' * H ^ (k + (i : ℕ) - (j : ℕ) + 1 - 2))
      (bN := K' * H ^ ((j : ℕ) - (i : ℕ) + 1 - 1))
      (bM := K' * H ^ ((j : ℕ) - (i : ℕ) + 1 - 2))
      (fun p hp q => (hLm p hp q).trans (hmono _ _ hKL)) (hRN.trans (hmono _ _ hKR))
      (fun p hp q => (hRm p hp q).trans (hmono _ _ hKR))
    have e1 : K' * H ^ (k + (i : ℕ) - (j : ℕ) + 1 - 2) * (K' * H ^ ((j : ℕ) - (i : ℕ) + 1 - 1)) =
        K' ^ 2 * H ^ (k - 1) := by
      rw [show k - 1 = (k + (i : ℕ) - (j : ℕ) + 1 - 2) + ((j : ℕ) - (i : ℕ) + 1 - 1) by omega,
        pow_add]
      ring
    have e2 : K' * H ^ (k + (i : ℕ) - (j : ℕ) + 1 - 2) * (K' * H ^ ((j : ℕ) - (i : ℕ) + 1 - 2)) =
        K' ^ 2 * H ^ (k - 2) := by
      rw [show k - 2 = (k + (i : ℕ) - (j : ℕ) + 1 - 2) + ((j : ℕ) - (i : ℕ) + 1 - 2) by omega,
        pow_add]
      ring
    exact ⟨g1.trans e1.le, fun v hv q => (g2 v hv q).trans e2.le⟩
  have hfin : ∀ m, (k : ℝ) ^ 4 * (K' ^ 2 * H ^ m) ≤ bnd_Kseq A k * H ^ m := by
    intro m
    have hstep := bnd_Kseq_step A hA0 (k - 1)
    rw [show k - 1 + 1 = k by omega] at hstep
    have : ((k : ℝ)) ^ 4 * K' ^ 2 ≤ bnd_Kseq A k := hstep
    have hp : 0 ≤ H ^ m := by positivity
    calc (k : ℝ) ^ 4 * (K' ^ 2 * H ^ m) = ((k : ℝ) ^ 4 * K' ^ 2) * H ^ m := by ring
      _ ≤ bnd_Kseq A k * H ^ m := mul_le_mul_of_nonneg_right this hp
  have hsum : ∀ (w : Fin k → Fin L → ℝ), (∀ s x, 0 ≤ w s x) → ∀ m,
      (∀ x ∈ D ×ˢ Finset.range r, bnd_N w (T x) ≤ K' ^ 2 * H ^ m) →
      bnd_N w (bnd_Cr β M t σ r) ≤ bnd_Kseq A k * H ^ m := by
    intro w hw m hb
    refine (bnd_N_le_sum _ hw _ T hdom).trans ?_
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hb0 : 0 ≤ K' ^ 2 * H ^ m := by positivity
    exact (mul_le_mul_of_nonneg_right hcard hb0).trans (hfin m)
  exact ⟨hsum _ (hw0 σ) _ fun x hx => (hterm x hx).1,
    fun v hv q => hsum _ (bnd_update_nonneg (hw0 σ) (bnd_del_nonneg q)) _
      fun x hx => (hterm x hx).2 v hv q⟩

/-- Proposition B.2 [ba:prop:primitive] for fixed data with the cancellation
`δ + g² Σ_j τ_j²`: `L^{k-1} |F_k| ≤ (k²+1) K_k (Σ_q U(q))^{k-1}` for `3 ≤ k ≤ k_max`. -/
private lemma sharp_primF_bound [NeZero L] (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) (m : ℂ)
    (t : ℝ) {U : Fin L → ℝ} {Cs CU Kb g δ : ℝ} (hU : ∀ q, 1 / 2 ≤ U q) (hCs : 1 ≤ Cs)
    (hKb : 0 ≤ Kb) (hδ : 0 ≤ δ) (hcoer : ∀ q, U q * (δ + g ^ 2 * torusAbs L q ^ 2) ≤ CU)
    (hβt0 : 0 ≤ β * t) (hβt1 : β * t ≤ 1)
    (hVc : ∀ a a' c : Fin L, (1 - t • pairP β M)⁻¹ (a + c) (a' + c) = (1 - t • pairP β M)⁻¹ a a')
    (hVhat : ∀ q, ‖∑ u, (((1 - t • pairP β M)⁻¹ 0 u : ℝ) : ℂ) * bnd_chi L q u‖ ≤ U q)
    (hrowS : ∀ (s : Bool) (a : Fin L), ∑ x, ‖pairV β M t s s a x‖ ≤ Cs)
    (kmax : ℕ)
    (hST : ∀ (k : ℕ) (σ : Fin k → Bool) (y : Fin k → Fin L) (c : Fin L),
      stableMol β M t σ (fun i => y i + c) = stableMol β M t σ y)
    (hS1 : ∀ k, 3 ≤ k → k ≤ kmax → ∀ (σ : Fin k → Bool) n,
      ‖tensorFourier (stableMol β M t σ) n‖ ≤ Kb)
    (hS2 : ∀ k, 3 ≤ k → k ≤ kmax → ∀ σ : Fin k → Bool, (∀ i, σ (finRotate k i) = !σ i) →
      ∀ n, ∑ j, n j = 0 →
        ‖tensorFourier (stableMol β M t σ) n‖ ≤
          Kb * (δ + g ^ 2 * ∑ j, torusAbs L (n j) ^ 2))
    (k : ℕ) (hk : 3 ≤ k) (hkmax : k ≤ kmax) (σ : Fin k → Bool) (a : Fin k → Fin L) :
    (L : ℝ) ^ (k - 1) * ‖primF β M m t a σ‖ ≤ ((k * k + 1 : ℕ) : ℝ) *
      bnd_Kseq (fun n => bnd_KB n Cs CU Kb) k * (∑ q, U q) ^ (k - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
  have hU0 : ∀ q, 0 ≤ U q := fun q => le_trans (by norm_num) (hU q)
  have hw0 := bnd_w_nonneg hU0 (by linarith : (0 : ℝ) ≤ Cs) σ
  rw [bnd_primF_eq]
  refine (bnd_dress (by omega) _ _ (bnd_w U Cs σ) (fun j a' q => bnd_dress_w β M t hVc hVhat
    hrowS σ j a' q) a).trans ?_
  have hind := sharp_induct β M t hU hCs hKb hδ hcoer hβt0 hβt1 hVc hVhat kmax hST hS1 hS2
    (n + 3) hk hkmax σ
  refine (bnd_N_le_sum (Finset.range ((n + 3) * (n + 3) + 1)) hw0 _ (fun r => bnd_Cr β M t σ r)
    (fun x => by
      rw [bnd_tf_sum]
      exact norm_sum_le _ _)).trans ?_
  refine (Finset.sum_le_sum fun r _ => (hind r).1).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring_nf
  exact le_rfl

end Induct

/-! ## The model on `0 < g ≤ C`

The data `(γ_g, M_B(g, E), m)` of a root of (5.2) [fo:eq:dyson-family] with the constants of
Lemma A.5 [ba:lem:kernels], Lemma 6.1 [da:lem:scales-propagators], Lemma B.1 [ba:lem:moment],
and (B.3) [ba:eq:cancel] with the factor `g²`. -/

section Model

/-- Proposition B.2 [ba:prop:primitive] for `F_k = W^{k-1} 𝒦_k`, `3 ≤ k ≤ k_max`, without the
factor `(1 + g^{-2})^{k-2}`: `|F_k| ≤ K ((1-t)ℓ_t)^{-(k-1)}` on `0 < g ≤ C`. -/
private lemma sharp_propB2 (C B₀ c' : ℝ) (hC : 0 < C) (hB₀ : 0 < B₀) (hc' : 0 < c')
    (kmax : ℕ) :
    ∃ K : ℝ, ∃ L₀ : ℕ, 0 < K ∧ ∀ g : ℝ, 0 < g → g ≤ C → ∀ L : ℕ, 3 ≤ L → L₀ ≤ L →
      ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m → c' ≤ m.im →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ k : ℕ, 3 ≤ k → k ≤ kmax →
      ∀ (a : Fin k → Fin L) (σ : Fin k → Bool),
        ‖primLoopF g L E m t a σ‖ ≤ K * ((1 - t) * ellProp g L t)⁻¹ ^ (k - 1) := by
  obtain ⟨cs, Csym, Ls, hcs, hCsym, Hs⟩ := bdd_symbol C B₀ c' hC hB₀ hc'
  obtain ⟨cp, Cp, Lp, hcp, hCp, Hp⟩ := scalesProp_bdd C B₀ c' hC hB₀ hc'
  have h1 : ∀ k : ℕ, ∃ C1 : ℝ, ∃ L1 : ℕ, 0 ≤ C1 ∧ (3 ≤ k → ∀ g : ℝ, 0 ≤ g → g ≤ C →
      ∀ L : ℕ, 3 ≤ L → L1 ≤ L → ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ,
      IsDysonRootV (hopB g) (gammaG g) L E m → c' ≤ m.im → ∀ t : ℝ, 0 ≤ t → t < 1 →
      ∀ (σ : Fin k → Bool) (n : Fin k → Fin L),
        ‖tensorFourier (stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ) n‖ ≤
          C1) := by
    intro k
    by_cases hk : 3 ≤ k
    · obtain ⟨c, C', L₀, hc, hC', H⟩ := stableMol_bdd C B₀ c' hC hB₀ hc' k 0 hk
      refine ⟨C', L₀, hC'.le, fun _ g hg hgC L hL hL₀ E hE m hm hcm t ht0 ht1 σ n => ?_⟩
      have : NeZero L := ⟨by omega⟩
      refine bnd_tf_le_rows (by omega) _ (fun b => ?_) n
      refine le_trans (Finset.sum_le_sum fun y _ => ?_)
        (H g hg hgC L hL hL₀ E hE m hm hcm t ht0 ht1.le σ ⟨0, by omega⟩ b).1
      have : 1 ≤ Real.exp (c * wordDiam y) := Real.one_le_exp (by positivity)
      nlinarith [norm_nonneg (stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ y)]
    · exact ⟨0, 0, le_rfl, fun h => absurd h hk⟩
  have h2 : ∀ k : ℕ, ∃ C2 : ℝ, ∃ L2 : ℕ, 0 ≤ C2 ∧ (4 ≤ k → ∀ g : ℝ, 0 ≤ g → g ≤ C →
      ∀ L : ℕ, 3 ≤ L → L2 ≤ L → ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ,
      IsDysonRootV (hopB g) (gammaG g) L E m → c' ≤ m.im → ∀ t : ℝ, 0 ≤ t → t < 1 →
      ∀ σ : Fin k → Bool, (∀ i, σ (finRotate k i) = !σ i) →
      ∀ n : Fin k → Fin L, (∑ j, (n j : ℕ)) % L = 0 →
        ‖tensorFourier (stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ) n‖ ≤
          C2 * ((1 - t) + g ^ 2 * ∑ j, torusAbs L (n j) ^ 2)) := by
    intro k
    by_cases hk : 4 ≤ k
    · obtain ⟨C', L₀, hC', H⟩ := stableMol_small_cancel C B₀ c' hC hB₀ hc' k hk
      exact ⟨C', L₀, hC'.le, fun _ => H⟩
    · exact ⟨0, 0, le_rfl, fun h => absurd h hk⟩
  choose C1 L1 hC1 H1 using h1
  choose C2 L2 hC2 H2 using h2
  set Kb : ℝ := ∑ k ∈ Finset.range (kmax + 1), (C1 k + C2 k) with hKb
  have hKb0 : 0 ≤ Kb := Finset.sum_nonneg fun k _ => add_nonneg (hC1 k) (hC2 k)
  have hC1K : ∀ k, k ≤ kmax → C1 k ≤ Kb := fun k hk => by
    have := Finset.single_le_sum (f := fun k => C1 k + C2 k)
      (fun k _ => add_nonneg (hC1 k) (hC2 k)) (Finset.mem_range.mpr (by omega : k < kmax + 1))
    linarith [hC2 k]
  have hC2K : ∀ k, k ≤ kmax → C2 k ≤ Kb := fun k hk => by
    have := Finset.single_le_sum (f := fun k => C1 k + C2 k)
      (fun k _ => add_nonneg (hC1 k) (hC2 k)) (Finset.mem_range.mpr (by omega : k < kmax + 1))
    linarith [hC1 k]
  set L₀ : ℕ := Ls + Lp + ∑ k ∈ Finset.range (kmax + 1), (L1 k + L2 k) with hL₀
  have hL1K : ∀ k, k ≤ kmax → L1 k ≤ L₀ := fun k hk => by
    have := Finset.single_le_sum (f := fun k => L1 k + L2 k) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega : k < kmax + 1))
    omega
  have hL2K : ∀ k, k ≤ kmax → L2 k ≤ L₀ := fun k hk => by
    have := Finset.single_le_sum (f := fun k => L1 k + L2 k) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega : k < kmax + 1))
    omega
  set Cs : ℝ := max Cp 1 with hCs
  set Kq : ℝ := bnd_Kseq (fun n => bnd_KB n Cs Csym Kb) kmax with hKq
  set K : ℝ := ((kmax * kmax + 1 : ℕ) : ℝ) * Kq * (max Csym 1) ^ kmax + 1 with hK
  have hA0 : ∀ n, 0 ≤ bnd_KB n Cs Csym Kb := fun n => by
    unfold bnd_KB
    have : 0 ≤ Cs := le_trans zero_le_one (le_max_right _ _)
    positivity
  have hKq0 : 0 ≤ Kq := bnd_Kseq_nonneg _ hA0 kmax
  refine ⟨K, L₀, by positivity, ?_⟩
  intro g hg hgC L hL hLL₀ E hE m hm hcm t ht0 ht1 k hk hkmax a σ
  have : NeZero L := ⟨by omega⟩
  have hLs : Ls ≤ L := by omega
  have hLp : Lp ≤ L := by omega
  obtain ⟨hU, ⟨hβt0, hβt1⟩, hVc, hVhat, hST⟩ := bnd_model g hL E m hm ht0 ht1
  obtain ⟨-, Hs2⟩ := Hs g hg.le hgC L hL hLs E hE m hm hcm
  obtain ⟨Hcoer, Havg⟩ := Hs2 t ht0 ht1
  obtain ⟨-, -, -, Hrow, -⟩ := Hp g hg.le hgC L hL hLp E hE m hm hcm
  have hδ : 0 < 1 - t := by linarith
  have hcoer : ∀ q, bnd_U g L E m t q * ((1 - t) + g ^ 2 * torusAbs L q ^ 2) ≤ Csym := by
    intro q
    have h := (Hcoer q).2
    have hpos : 0 < (1 - t) + g ^ 2 * torusAbs L q ^ 2 := by positivity
    unfold bnd_U
    rwa [le_div_iff₀ hpos] at h
  have hrowS : ∀ (s : Bool) (a : Fin L),
      ∑ x, ‖pairV (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t s s a x‖ ≤ Cs := by
    intro s a
    have h := Hrow t ht0 ht1.le a
    refine le_trans ?_ (h.trans (le_max_left _ _))
    cases s <;> simp [pairV, Matrix.map_apply]
  have hS1 : ∀ k, 3 ≤ k → k ≤ kmax → ∀ (σ : Fin k → Bool) n,
      ‖tensorFourier (stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ) n‖ ≤ Kb :=
    fun k hk hkm σ n => (H1 k hk g hg.le hgC L hL (by linarith [hL1K k hkm]) E hE m hm hcm t
      ht0 ht1 σ n).trans (hC1K k hkm)
  have hS2 : ∀ k, 3 ≤ k → k ≤ kmax → ∀ σ : Fin k → Bool, (∀ i, σ (finRotate k i) = !σ i) →
      ∀ n, ∑ j, n j = 0 →
        ‖tensorFourier (stableMol (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) t σ) n‖ ≤
          Kb * ((1 - t) + g ^ 2 * ∑ j, torusAbs L (n j) ^ 2) := by
    intro k hk hkm σ halt n hn
    rcases Nat.lt_or_ge k 4 with h3 | h4
    · exfalso
      have hk3 : k = 3 := by omega
      subst hk3
      have e0 := halt 0
      have e1 := halt 1
      have e2 := halt 2
      have r0 : finRotate 3 0 = 1 := by decide
      have r1 : finRotate 3 1 = 2 := by decide
      have r2 : finRotate 3 2 = 0 := by decide
      rw [r0] at e0; rw [r1] at e1; rw [r2] at e2
      cases h : σ 0 <;> simp_all
    · have hn' : (∑ j, (n j : ℕ)) % L = 0 := by
        rw [← bnd_val_sum, hn, Fin.val_zero]
      have hX : 0 ≤ (1 - t) + g ^ 2 * ∑ j, torusAbs L (n j) ^ 2 :=
        add_nonneg hδ.le (mul_nonneg (sq_nonneg g) (Finset.sum_nonneg fun j _ => sq_nonneg _))
      exact (H2 k h4 g hg.le hgC L hL (by linarith [hL2K k hkm]) E hE m hm hcm t ht0 ht1 σ halt
        n hn').trans (mul_le_mul_of_nonneg_right (hC2K k hkm) hX)
  have hmain := sharp_primF_bound (gammaG g) (dysonMat (hopB g) (gammaG g) L E m) m t hU
    (le_max_right Cp 1) hKb0 hδ.le hcoer hβt0 hβt1 hVc hVhat hrowS kmax hST hS1 hS2 k hk hkmax
    σ a
  -- the average of `U`
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have havg : ∑ q, bnd_U g L E m t q ≤ L * (Csym * ((1 - t) * ellProp g L t)⁻¹) := by
    obtain ⟨he, -, hle⟩ := Havg ⟨0, by omega⟩
    have : (L : ℝ)⁻¹ * ∑ q, bnd_U g L E m t q ≤ Csym / ((1 - t) * ellProp g L t) := by
      unfold bnd_U; rw [he]; exact hle
    rw [inv_mul_le_iff₀ hLpos] at this
    rwa [div_eq_mul_inv] at this
  have hell : 0 < ellProp g L t := by
    have := (scale_facts g hg.le 1 L le_rfl (by omega) t t ht0 le_rfl ht1).1
    linarith
  set R := ((1 - t) * ellProp g L t)⁻¹ with hR
  have hR0 : 0 ≤ R := by positivity
  have hU0 : 0 ≤ ∑ q, bnd_U g L E m t q :=
    Finset.sum_nonneg fun q _ => le_trans (by norm_num) (hU q)
  have hKk : bnd_Kseq (fun n => bnd_KB n Cs Csym Kb) k ≤ Kq := bnd_Kseq_mono _ hkmax
  have hKk0 : 0 ≤ bnd_Kseq (fun n => bnd_KB n Cs Csym Kb) k := bnd_Kseq_nonneg _ hA0 k
  have hkk : ((k * k + 1 : ℕ) : ℝ) ≤ ((kmax * kmax + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul hkmax hkmax) 1
  have hCpow : Csym ^ (k - 1) ≤ (max Csym 1) ^ kmax := by
    calc Csym ^ (k - 1) ≤ (max Csym 1) ^ (k - 1) :=
          pow_le_pow_left₀ hCsym.le (le_max_left _ _) _
      _ ≤ (max Csym 1) ^ kmax := pow_le_pow_right₀ (le_max_right _ _) (by omega)
  have hLk : (0 : ℝ) < (L : ℝ) ^ (k - 1) := by positivity
  have hstep : (L : ℝ) ^ (k - 1) * ‖primLoopF g L E m t a σ‖ ≤
      (L : ℝ) ^ (k - 1) * (((kmax * kmax + 1 : ℕ) : ℝ) * Kq * (max Csym 1) ^ kmax *
        R ^ (k - 1)) := by
    refine hmain.trans ?_
    have hpow : (∑ q, bnd_U g L E m t q) ^ (k - 1) ≤ (L : ℝ) ^ (k - 1) * (Csym ^ (k - 1) *
        R ^ (k - 1)) := by
      rw [← mul_pow, ← mul_pow]
      exact pow_le_pow_left₀ hU0 havg _
    calc ((k * k + 1 : ℕ) : ℝ) * bnd_Kseq (fun n => bnd_KB n Cs Csym Kb) k *
          (∑ q, bnd_U g L E m t q) ^ (k - 1)
        ≤ ((k * k + 1 : ℕ) : ℝ) * bnd_Kseq (fun n => bnd_KB n Cs Csym Kb) k *
          ((L : ℝ) ^ (k - 1) * (Csym ^ (k - 1) * R ^ (k - 1))) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ ((kmax * kmax + 1 : ℕ) : ℝ) * Kq *
          ((L : ℝ) ^ (k - 1) * ((max Csym 1) ^ kmax * R ^ (k - 1))) := by
          gcongr
      _ = _ := by ring
  have hfin := le_of_mul_le_mul_left hstep hLk
  refine hfin.trans ?_
  gcongr
  linarith

end Model

/-- Proposition B.2 [ba:prop:primitive] and the bound (5.20) [fo:eq:primitivebound] of Lemma 5.2
[fo:lem:deterministic](a) without the factor `(1 + g^{-2})^{k-2}`: `|𝒦_k(t)| ≤ C' ζ_t^{k-1}` for
every `0 < g ≤ C`, `L ≥ L₀`, `W ≥ 1`, `0 ≤ t < 1` (the bound of [TYY, Lemma 3.15] at fixed
`k`). -/
theorem primLoop_sharp (C B₀ c' : ℝ) (hC : 0 < C) (hB₀ : 0 < B₀) (hc' : 0 < c') (k : ℕ)
    (hk : 2 ≤ k) :
    ∃ C' : ℝ, ∃ L₀ : ℕ, 0 < C' ∧ ∀ g : ℝ, 0 < g → g ≤ C → ∀ L : ℕ, 3 ≤ L → L₀ ≤ L →
      ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m → c' ≤ m.im →
      ∀ W : ℕ, 1 ≤ W → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (a : Fin k → Fin L) (σ : Fin k → Bool),
        ‖primLoop g W L E m t a σ‖ ≤ C' * zetaProp g W L t ^ (k - 1) := by
  rcases Nat.lt_or_ge k 3 with hk2 | hk3
  · -- `k = 2`: the factor is `(1 + g^{-2})^0 = 1`
    obtain rfl : k = 2 := by omega
    obtain ⟨C₂, L₀, hC₂, H⟩ := primLoop_bdd C B₀ c' hC hB₀ hc' 2 le_rfl
    refine ⟨C₂, L₀, hC₂, ?_⟩
    intro g hg hgC L hL hL₀ E hE m hm hcm W hW t ht0 ht1 a σ
    have h := H g hg hgC L hL hL₀ E hE m hm hcm W hW t ht0 ht1 a σ
    simpa using h
  · -- `k ≥ 3`
    obtain ⟨K, L₀, hK, H⟩ := sharp_propB2 C B₀ c' hC hB₀ hc' k
    refine ⟨K, L₀, hK, ?_⟩
    intro g hg hgC L hL hL₀ E hE m hm hcm W hW t ht0 ht1 a σ
    rw [bnd_norm_primLoop g W L E m t (by omega), bnd_zeta_eq]
    have h := H g hg hgC L hL hL₀ E hE m hm hcm t ht0 ht1 k hk3 le_rfl a σ
    have hγ1 : 1 ≤ (gammaG g)⁻¹ := one_le_inv₀ (bnd_gamma_pos g) |>.mpr (bnd_gamma_le_one g)
    have hδ : 0 < 1 - t := by linarith
    have hell0 : 0 < ellProp g L t := by
      have := (scale_facts g hg.le 1 L le_rfl (by omega) t t ht0 le_rfl ht1).1
      linarith
    set R := ((1 - t) * ellProp g L t)⁻¹ with hR
    have hR0 : 0 ≤ R := by positivity
    have hW0 : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
    calc ((W : ℝ)⁻¹) ^ (k - 1) * ‖primLoopF g L E m t a σ‖
        ≤ ((W : ℝ)⁻¹) ^ (k - 1) * (K * R ^ (k - 1)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = K * ((W : ℝ)⁻¹ * 1 * R) ^ (k - 1) := by
          rw [mul_one, mul_pow]; ring
      _ ≤ K * ((W : ℝ)⁻¹ * (gammaG g)⁻¹ * R) ^ (k - 1) := by
          gcongr

/-- The primitive slot of the general Theorem 5.12 [gc:thm:common] with no lower bound on the
coupling: `|𝒦_k| ≤ W^δ ζ_t^{k-1}` for `2 ≤ k ≤ k_max` and `0 < g ≤ C`. -/
theorem primLoop_sharp_slot (C B₀ c' δ : ℝ) (hC : 0 < C) (hB₀ : 0 < B₀) (hc' : 0 < c')
    (hδ : 0 < δ) (kmax : ℕ) :
    ∃ W₀ L₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ g : ℝ, 0 < g → g ≤ C →
      ∀ L : ℕ, 3 ≤ L → L₀ ≤ L → ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ,
      IsDysonRootV (hopB g) (gammaG g) L E m → c' ≤ m.im → ∀ t : ℝ, 0 ≤ t → t < 1 →
      ∀ k : ℕ, 2 ≤ k → k ≤ kmax → ∀ (a : Fin k → Fin L) (σ : Fin k → Bool),
        ‖primLoop g W L E m t a σ‖ ≤ (W : ℝ) ^ δ * zetaProp g W L t ^ (k - 1) := by
  have h : ∀ k : ℕ, ∃ C' : ℝ, ∃ L₀ : ℕ, 0 < C' ∧ (2 ≤ k → ∀ g : ℝ, 0 < g → g ≤ C →
      ∀ L : ℕ, 3 ≤ L → L₀ ≤ L → ∀ E : ℝ, |E| ≤ B₀ → ∀ m : ℂ,
      IsDysonRootV (hopB g) (gammaG g) L E m → c' ≤ m.im → ∀ W : ℕ, 1 ≤ W → ∀ t : ℝ, 0 ≤ t →
      t < 1 → ∀ (a : Fin k → Fin L) (σ : Fin k → Bool),
        ‖primLoop g W L E m t a σ‖ ≤ C' * zetaProp g W L t ^ (k - 1)) := by
    intro k
    by_cases hk : 2 ≤ k
    · obtain ⟨C', L₀, hC', H⟩ := primLoop_sharp C B₀ c' hC hB₀ hc' k hk
      exact ⟨C', L₀, hC', fun _ => H⟩
    · exact ⟨1, 0, one_pos, fun h => absurd h hk⟩
  choose Ck Lk hCk Hk using h
  set Cmax : ℝ := ∑ k ∈ Finset.range (kmax + 1), Ck k with hCmax
  have hCmax : ∀ k, k ≤ kmax → Ck k ≤ Cmax := fun k hk =>
    Finset.single_le_sum (f := Ck) (fun k _ => (hCk k).le)
      (Finset.mem_range.mpr (by omega : k < kmax + 1))
  have hCmax0 : 0 ≤ Cmax := Finset.sum_nonneg fun k _ => (hCk k).le
  set L₀ : ℕ := ∑ k ∈ Finset.range (kmax + 1), Lk k with hL₀
  have hL₀ : ∀ k, k ≤ kmax → Lk k ≤ L₀ := fun k hk =>
    Finset.single_le_sum (f := Lk) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega : k < kmax + 1))
  refine ⟨⌈Cmax ^ (1 / δ)⌉₊ + 1, L₀, ?_⟩
  intro W hW g hg hgC L hL hLL₀ E hE m hm hcm t ht0 ht1 k hk2 hkmax a σ
  have hW1 : 1 ≤ W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hb := Hk k hk2 g hg hgC L hL (le_trans (hL₀ k hkmax) hLL₀) E hE m hm hcm W hW1 t ht0 ht1
    a σ
  have hζ0 : 0 ≤ zetaProp g W L t ^ (k - 1) := by
    have := (scale_facts g hg.le W L hW1 (by omega) t t ht0 le_rfl ht1).2.2.2.1
    exact pow_nonneg (le_trans (by positivity) this) _
  -- `C_max ≤ W^δ`
  have hCW : Cmax ≤ (W : ℝ) ^ δ := by
    have h1 : Cmax ^ (1 / δ) ≤ (W : ℝ) := by
      have := Nat.le_ceil (Cmax ^ (1 / δ))
      have h' : ((⌈Cmax ^ (1 / δ)⌉₊ : ℕ) : ℝ) ≤ W := by
        exact_mod_cast (by omega : ⌈Cmax ^ (1 / δ)⌉₊ ≤ W)
      linarith
    have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hCmax0 _) h1 hδ.le
    rwa [← Real.rpow_mul hCmax0, show 1 / δ * δ = 1 by field_simp, Real.rpow_one] at h2
  calc ‖primLoop g W L E m t a σ‖ ≤ Ck k * zetaProp g W L t ^ (k - 1) := hb
    _ ≤ Cmax * zetaProp g W L t ^ (k - 1) :=
        mul_le_mul_of_nonneg_right (hCmax k hkmax) hζ0
    _ ≤ (W : ℝ) ^ δ * zetaProp g W L t ^ (k - 1) := mul_le_mul_of_nonneg_right hCW hζ0


end LSBA
