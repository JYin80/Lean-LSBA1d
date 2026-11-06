import LSBA.Sampling.AuxHierarchy
import LSBA.Primitive.Tree

/-!
# The orbital limit

Lemma 5.4 [uvc:lem:orbital-limit], (5.24) [uvc:eq:orbital-limit]: at fixed `g, L, E, T`, the
normalized expected loops of the width-`W̃` model converge to the primitive loops `F_k`,
uniformly on `[0, T]`.
-/

open MeasureTheory Real Filter Topology Complex Finset
open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The cut sums of two loop families differ by at most `2n²L B D` when, at every length
`2 ≤ p ≤ n`, both are bounded by `B` and they differ by at most `D`. -/
private lemma orbital_cutSum_sub_le {L n : ℕ} (A F : LoopFam L) (a : Fin n → Fin L)
    (σ : Fin n → Bool) {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hA : ∀ p (b : Fin p → Fin L) (τ : Fin p → Bool), 2 ≤ p → p ≤ n → ‖A p b τ‖ ≤ B)
    (hF : ∀ p (b : Fin p → Fin L) (τ : Fin p → Bool), 2 ≤ p → p ≤ n → ‖F p b τ‖ ≤ B)
    (hAF : ∀ p (b : Fin p → Fin L) (τ : Fin p → Bool), 2 ≤ p → p ≤ n →
      ‖A p b τ - F p b τ‖ ≤ D) :
    ‖cutSumFam A a σ - cutSumFam F a σ‖ ≤ n * n * L * (2 * B * D) := by
  unfold cutSumFam
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ i : Fin n, ‖(∑ j : Fin n, if i < j then ∑ c : Fin L,
      A _ (cutLLab a i j c) (cutLSgn σ i j) * A _ (cutRLab a i j c) (cutRSgn σ i j) else 0) -
      ∑ j : Fin n, if i < j then ∑ c : Fin L,
      F _ (cutLLab a i j c) (cutLSgn σ i j) * F _ (cutRLab a i j c) (cutRSgn σ i j) else 0‖ ≤
      n * (L * (2 * B * D)) := by
    intro i
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    have h2 : ∀ j : Fin n, ‖(if i < j then ∑ c : Fin L,
        A _ (cutLLab a i j c) (cutLSgn σ i j) * A _ (cutRLab a i j c) (cutRSgn σ i j) else 0) -
        (if i < j then ∑ c : Fin L,
        F _ (cutLLab a i j c) (cutLSgn σ i j) * F _ (cutRLab a i j c) (cutRSgn σ i j) else 0)‖ ≤
        L * (2 * B * D) := by
      intro j
      split_ifs with hij
      · rw [← Finset.sum_sub_distrib]
        refine (norm_sum_le _ _).trans ?_
        have hij' : i.val < j.val := hij
        have hj := j.isLt
        have h3 : ∀ c : Fin L, ‖A _ (cutLLab a i j c) (cutLSgn σ i j) *
            A _ (cutRLab a i j c) (cutRSgn σ i j) - F _ (cutLLab a i j c) (cutLSgn σ i j) *
            F _ (cutRLab a i j c) (cutRSgn σ i j)‖ ≤ 2 * B * D := by
          intro c
          have e : A _ (cutLLab a i j c) (cutLSgn σ i j) * A _ (cutRLab a i j c) (cutRSgn σ i j) -
              F _ (cutLLab a i j c) (cutLSgn σ i j) * F _ (cutRLab a i j c) (cutRSgn σ i j) =
              (A _ (cutLLab a i j c) (cutLSgn σ i j) - F _ (cutLLab a i j c) (cutLSgn σ i j)) *
                A _ (cutRLab a i j c) (cutRSgn σ i j) + F _ (cutLLab a i j c) (cutLSgn σ i j) *
                (A _ (cutRLab a i j c) (cutRSgn σ i j) -
                  F _ (cutRLab a i j c) (cutRSgn σ i j)) := by
            ring
          rw [e]
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
          have a1 := hAF _ (cutLLab a i j c) (cutLSgn σ i j) (by omega) (by omega)
          have a2 := hA _ (cutRLab a i j c) (cutRSgn σ i j) (by omega) (by omega)
          have a3 := hF _ (cutLLab a i j c) (cutLSgn σ i j) (by omega) (by omega)
          have a4 := hAF _ (cutRLab a i j c) (cutRSgn σ i j) (by omega) (by omega)
          calc _ ≤ D * B + B * D := add_le_add (mul_le_mul a1 a2 (norm_nonneg _) hD)
                (mul_le_mul a3 a4 (norm_nonneg _) hB)
            _ = 2 * B * D := by ring
        refine (Finset.sum_le_sum fun c _ => h3 c).trans (le_of_eq ?_)
        simp
      · simp only [sub_self, norm_zero]; positivity
    refine (Finset.sum_le_sum fun j _ => h2 j).trans (le_of_eq ?_)
    simp
  refine (Finset.sum_le_sum fun i _ => h1 i).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Index set of the loop tensors of lengths at most `k`. -/
private abbrev orbital_Idx (k L : ℕ) : Type :=
  Σ n : Fin (k + 1), (Fin n → Fin L) × (Fin n → Bool)

/-- Lemma 5.4 [uvc:lem:orbital-limit], (5.24) [uvc:eq:orbital-limit] in the form `F_k = W^{k-1}𝒦_k`:
at fixed `g, L, E, T`, the normalized expected loops of the width-`W̃` model at time `t` (block
noise of variance `tγ_g/W̃`) converge to `F_k`, uniformly on `[0, T]`. -/
theorem orbital_limit (g : ℝ) (hg : 0 < g) (L : ℕ) (hL : 3 ≤ L) (E : ℝ) (m : ℂ)
    (hm : IsDysonRootV (hopB g) (gammaG g) L E m) (T : ℝ) (hT0 : 0 ≤ T) (hT : T < 1) (k : ℕ)
    (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ Wt : ℕ, N ≤ Wt → ∀ t : ℝ, 0 ≤ t → t ≤ T →
      ∀ (a : Fin k → Fin L) (σ : Fin k → Bool),
        ‖(Wt : ℂ) ^ (k - 1) * ∫ ω, loopTr (W := Wt)
            ((Hdet g (fun b => ((Real.sqrt t : ℝ) : ℂ) • gueBlock Wt L ω b) -
              zChar g E m t • (1 : Matrix (Fin L × Fin Wt) (Fin L × Fin Wt) ℂ))⁻¹) a σ
            ∂(μ Wt L) - primLoopF g L E m t a σ‖ ≤ ε := by
  have hm0 : 0 < m.im := hm.1
  have hD := primData_of_root g L hL E m hm
  rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk2
  · -- length one: the one-loop mean field
    obtain ⟨C1, hC1, hone⟩ := auxLoop_one g hg L hL E m hm T hT0 hT
    refine ⟨⌈C1 / ε⌉₊ + 1, fun Wt hWt t ht0 htT a σ => ?_⟩
    have hW1 : 1 ≤ Wt := le_trans (by omega) hWt
    have hW' : (0 : ℝ) < Wt := by exact_mod_cast hW1
    change ‖auxLoop g Wt L E m t 1 a σ - primLoopF g L E m t a σ‖ ≤ ε
    have ha : a = ![a 0] := by
      funext i; rw [Fin.fin_one_eq_zero i]; rfl
    have hσ : σ = ![σ 0] := by
      funext i; rw [Fin.fin_one_eq_zero i]; rfl
    have hF1 : primLoopF g L E m t ![a 0] ![σ 0] = if σ 0 then m else star m := rfl
    rw [ha, hσ, hF1]
    refine (hone Wt hW1 t ht0 htT (a 0) (σ 0)).trans ?_
    rw [div_le_iff₀ hW']
    have h1 : C1 / ε ≤ Wt := by
      have := Nat.le_ceil (C1 / ε)
      have h2 : ((⌈C1 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ Wt := by exact_mod_cast hWt
      push_cast at h2
      linarith
    rw [div_le_iff₀ hε] at h1
    linarith
  -- lengths `2 ≤ n ≤ k`: Grönwall for the vector of differences
  set γ := gammaG g with hγdef
  have hγ : 0 < γ := hD.pos
  set η := etaChar g m T with hηdef
  have hη : 0 < η := etaChar_pos g m hm0 hT
  have hh : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ (2 ≤ n → ∀ Wt : ℕ, 1 ≤ Wt →
      ∀ (a : Fin n → Fin L) (σ : Fin n → Bool),
        ContinuousOn (fun t => auxLoop g Wt L E m t n a σ) (Set.Icc 0 T) ∧
        ∀ t ∈ Set.Ioo 0 T, ∃ d : ℂ, HasDerivAt (fun s => auxLoop g Wt L E m s n a σ) d t ∧
          ‖d - (γ : ℂ) * cutSumFam (auxLoop g Wt L E m t) a σ‖ ≤ C / Wt) := by
    intro n
    by_cases hn : 2 ≤ n
    · obtain ⟨C, hC, h⟩ := auxLoop_hierarchy g hg L hL E m hm T hT0 hT n hn
      exact ⟨C, hC, fun _ => h⟩
    · exact ⟨1, one_pos, fun h => absurd h hn⟩
  choose Ch hCh0 hCh using hh
  set Cs := ∑ n ∈ Finset.range (k + 1), Ch n with hCs
  have hCs_le : ∀ n, n ≤ k → Ch n ≤ Cs := fun n hn =>
    Finset.single_le_sum (f := Ch) (fun i _ => (hCh0 i).le) (Finset.mem_range.2 (by omega))
  have hCs0 : 0 < Cs := (hCh0 0).trans_le (hCs_le 0 (by omega))
  -- the primitive loops: derivative and a bound on `[0, T]`
  have hFd : ∀ n (b : Fin n → Fin L) (τ : Fin n → Bool), 2 ≤ n → ∀ t : ℝ, 0 ≤ t → t ≤ T →
      HasDerivAt (fun s => primLoopF g L E m s b τ)
        ((γ : ℂ) * cutSumFam (fun n b τ => primLoopF g L E m t (k := n) b τ) b τ) t :=
    fun n b τ hn t ht0 htT => primF_hasDerivAt hD t ⟨by linarith, by linarith⟩ hn b τ
  set VF : ℝ → orbital_Idx k L → ℂ := fun t i =>
    if 2 ≤ (i.1 : ℕ) then primLoopF g L E m t i.2.1 i.2.2 else 0 with hVF
  have hVFc : ContinuousOn VF (Set.Icc 0 T) := by
    refine continuousOn_pi.2 fun i => ?_
    by_cases hi : 2 ≤ (i.1 : ℕ)
    · simp only [hVF, hi, ite_true]
      exact fun t ht => (hFd _ _ _ hi t ht.1 ht.2).continuousAt.continuousWithinAt
    · simp only [hVF, hi, ite_false]
      exact continuousOn_const
  obtain ⟨BF, hBF⟩ := isCompact_Icc.exists_bound_of_continuousOn hVFc
  have hFb : ∀ t ∈ Set.Icc 0 T, ∀ p (b : Fin p → Fin L) (τ : Fin p → Bool), 2 ≤ p → p ≤ k →
      ‖primLoopF g L E m t b τ‖ ≤ max BF 0 := by
    intro t ht p b τ hp hpk
    have h := norm_le_pi_norm (VF t) (⟨⟨p, by omega⟩, (b, τ)⟩ : orbital_Idx k L)
    simp only [hVF, hp, ite_true] at h
    exact h.trans ((hBF t ht).trans (le_max_left _ _))
  set BA := (L : ℝ) * (max 1 η⁻¹) ^ k with hBA
  have hAb : ∀ Wt : ℕ, 1 ≤ Wt → ∀ t ∈ Set.Icc 0 T, ∀ p (b : Fin p → Fin L) (τ : Fin p → Bool),
      2 ≤ p → p ≤ k → ‖auxLoop g Wt L E m t p b τ‖ ≤ BA := by
    intro Wt hW t ht p b τ hp hpk
    have ht1 : t < 1 := by linarith [ht.2]
    refine (auxHierarchy_norm_auxLoop_le g L E m hm0 Wt hW t ht1 p (by omega) b τ).trans ?_
    rw [hBA]
    gcongr
    have hηt : (etaChar g m t)⁻¹ ≤ η⁻¹ := by
      refine inv_anti₀ hη ?_
      simp only [hηdef, etaChar]
      have := ht.2
      gcongr
    calc (etaChar g m t)⁻¹ ^ p ≤ η⁻¹ ^ p :=
          pow_le_pow_left₀ (inv_nonneg.2 (etaChar_pos g m hm0 ht1).le) hηt p
      _ ≤ (max 1 η⁻¹) ^ p := pow_le_pow_left₀ (inv_nonneg.2 hη.le) (le_max_right _ _) p
      _ ≤ (max 1 η⁻¹) ^ k := pow_le_pow_right₀ (le_max_left _ _) hpk
  set Bt := BA + max BF 0 with hBt
  have hBt0 : 0 ≤ Bt := by positivity
  set K := γ * (k * k * L * (2 * Bt)) + 1 with hK
  have hK0 : 0 < K := by positivity
  have hexp1 : 1 ≤ Real.exp (K * T) := Real.one_le_exp (by positivity)
  refine ⟨⌈Cs * Real.exp (K * T) / (K * ε)⌉₊ + 1, fun Wt hWt t ht0 htT a σ => ?_⟩
  have hW1 : 1 ≤ Wt := le_trans (by omega) hWt
  have hW' : (0 : ℝ) < Wt := by exact_mod_cast hW1
  change ‖auxLoop g Wt L E m t k a σ - primLoopF g L E m t a σ‖ ≤ ε
  -- the vector of differences
  set V : ℝ → orbital_Idx k L → ℂ := fun s i => if 2 ≤ (i.1 : ℕ) then
    auxLoop g Wt L E m s i.1 i.2.1 i.2.2 - primLoopF g L E m s i.2.1 i.2.2 else 0 with hV
  have hVi : ∀ s p (b : Fin p → Fin L) (τ : Fin p → Bool) (hp : 2 ≤ p) (hpk : p ≤ k),
      V s ⟨⟨p, by omega⟩, (b, τ)⟩ = auxLoop g Wt L E m s p b τ - primLoopF g L E m s b τ := by
    intro s p b τ hp hpk
    simp only [hV, hp, ite_true]
  have hVc : ContinuousOn V (Set.Icc 0 T) := by
    refine continuousOn_pi.2 fun i => ?_
    by_cases hi : 2 ≤ (i.1 : ℕ)
    · simp only [hV, hi, ite_true]
      exact (hCh _ hi Wt hW1 i.2.1 i.2.2).1.sub
        (fun t ht => (hFd _ _ _ hi t ht.1 ht.2).continuousAt.continuousWithinAt)
    · simp only [hV, hi, ite_false]
      exact continuousOn_const
  have hV0 : V 0 = 0 := by
    funext i
    by_cases hi : 2 ≤ (i.1 : ℕ)
    · simp only [hV, hi, ite_true, Pi.zero_apply]
      rw [auxLoop_init g L hL E m hm Wt hW1 _ (by omega) i.2.1 i.2.2, sub_self]
    · simp only [hV, hi, ite_false, Pi.zero_apply]
  have hVd : ∀ x ∈ Set.Ioo 0 T, ∃ V' : orbital_Idx k L → ℂ,
      HasDerivAt V V' x ∧ ‖V'‖ ≤ K * ‖V x‖ + Cs / Wt := by
    intro x hx
    have hxI : x ∈ Set.Icc 0 T := ⟨hx.1.le, hx.2.le⟩
    have hcomp : ∀ i : orbital_Idx k L, ∃ d : ℂ, HasDerivAt (fun s => V s i) d x ∧
        ‖d‖ ≤ K * ‖V x‖ + Cs / Wt := by
      intro i
      by_cases hi : 2 ≤ (i.1 : ℕ)
      · obtain ⟨d, hd, hdb⟩ := (hCh _ hi Wt hW1 i.2.1 i.2.2).2 x hx
        refine ⟨d - (γ : ℂ) * cutSumFam (fun n b τ => primLoopF g L E m x (k := n) b τ)
          i.2.1 i.2.2, ?_, ?_⟩
        · have e : (fun s => V s i) = fun s =>
              auxLoop g Wt L E m s i.1 i.2.1 i.2.2 - primLoopF g L E m s i.2.1 i.2.2 := by
            funext s; simp only [hV, hi, ite_true]
          rw [e]
          exact hd.sub (hFd _ _ _ hi x hx.1.le hx.2.le)
        · have hnk : (i.1 : ℕ) ≤ k := Nat.lt_succ_iff.mp i.1.isLt
          have hcut := orbital_cutSum_sub_le (auxLoop g Wt L E m x)
            (fun n b τ => primLoopF g L E m x (k := n) b τ) i.2.1 i.2.2 hBt0 (norm_nonneg (V x))
            (fun p b τ hp hpn => (hAb Wt hW1 x hxI p b τ hp (hpn.trans hnk)).trans
              (le_add_of_nonneg_right (le_max_right _ _)))
            (fun p b τ hp hpn => (hFb x hxI p b τ hp (hpn.trans hnk)).trans
              (le_add_of_nonneg_left (by positivity)))
            (fun p b τ hp hpn => by
              rw [← hVi x p b τ hp (hpn.trans hnk)]
              exact norm_le_pi_norm (V x) _)
          have e : d - (γ : ℂ) * cutSumFam (fun n b τ => primLoopF g L E m x (k := n) b τ)
              i.2.1 i.2.2 = (d - (γ : ℂ) * cutSumFam (auxLoop g Wt L E m x) i.2.1 i.2.2) +
              (γ : ℂ) * (cutSumFam (auxLoop g Wt L E m x) i.2.1 i.2.2 -
                cutSumFam (fun n b τ => primLoopF g L E m x (k := n) b τ) i.2.1 i.2.2) := by
            ring
          rw [e]
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hγ]
          have hn' : ((i.1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hnk
          have h1 : Ch i.1 / Wt ≤ Cs / Wt := by gcongr; exact hCs_le _ hnk
          have h2 : γ * (((i.1 : ℕ) : ℝ) * ((i.1 : ℕ) : ℝ) * L * (2 * Bt * ‖V x‖)) ≤
              (K - 1) * ‖V x‖ := by
            rw [hK, add_sub_cancel_right]
            have : ((i.1 : ℕ) : ℝ) * ((i.1 : ℕ) : ℝ) ≤ (k : ℝ) * k :=
              mul_le_mul hn' hn' (by positivity) (by positivity)
            have hVn := norm_nonneg (V x)
            calc γ * (((i.1 : ℕ) : ℝ) * ((i.1 : ℕ) : ℝ) * L * (2 * Bt * ‖V x‖))
                ≤ γ * ((k : ℝ) * k * L * (2 * Bt * ‖V x‖)) := by gcongr
              _ = γ * ((k : ℝ) * k * L * (2 * Bt)) * ‖V x‖ := by ring
          have h3 := mul_le_mul_of_nonneg_left hcut hγ.le
          nlinarith [norm_nonneg (V x)]
      · refine ⟨0, ?_, ?_⟩
        · have e : (fun s => V s i) = fun _ => 0 := by
            funext s; simp only [hV, hi, ite_false]
          rw [e]
          exact hasDerivAt_const x 0
        · rw [norm_zero]; positivity
    choose d hd using hcomp
    exact ⟨d, hasDerivAt_pi.2 fun i => (hd i).1,
      (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (hd i).2⟩
  choose! V' hV' using hVd
  -- Grönwall on `[δ, s]` and `δ → 0`
  set c := Cs / Wt / K * (Real.exp (K * T) - 1) with hc
  have hc0 : 0 ≤ c := by
    have : 0 ≤ Real.exp (K * T) - 1 := by linarith
    positivity
  have hmain : ∀ s ∈ Set.Icc 0 T, ‖V s‖ ≤ c := by
    intro s hs
    rcases hs.1.eq_or_lt with h0 | hpos
    · rw [← h0, hV0, norm_zero]; exact hc0
    have key : ∀ δ ∈ Set.Ioo 0 s, ‖V s‖ ≤ ‖V δ‖ * Real.exp (K * T) + c := by
      intro δ hδ
      have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (f := V) (f' := V')
        (δ := ‖V δ‖) (K := K) (ε := Cs / Wt) (a := δ) (b := s)
        (hVc.mono (Set.Icc_subset_Icc hδ.1.le hs.2))
        (fun x hx =>
          (hV' x ⟨by linarith [hδ.1, hx.1], by linarith [hx.2, hs.2]⟩).1.hasDerivWithinAt)
        le_rfl (fun x hx => (hV' x ⟨by linarith [hδ.1, hx.1], by linarith [hx.2, hs.2]⟩).2)
        s ⟨hδ.2.le, le_rfl⟩
      rw [gronwallBound_of_K_ne_0 hK0.ne'] at hgr
      beta_reduce at hgr
      have he : Real.exp (K * (s - δ)) ≤ Real.exp (K * T) := by
        refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hK0.le)
        linarith [hδ.1, hs.2]
      refine hgr.trans ?_
      rw [hc]
      have hq : 0 ≤ Cs / Wt / K := by positivity
      gcongr
    have hlim : Tendsto (fun δ => ‖V δ‖ * Real.exp (K * T) + c) (𝓝[Set.Ioo 0 s] 0)
        (𝓝 (‖(0 : orbital_Idx k L → ℂ)‖ * Real.exp (K * T) + c)) := by
      have hcw : ContinuousWithinAt V (Set.Ioo 0 s) 0 :=
        (hVc 0 ⟨le_rfl, hT0⟩).mono fun y hy => ⟨hy.1.le, hy.2.le.trans hs.2⟩
      have ht := hcw.tendsto
      rw [hV0] at ht
      exact (ht.norm.mul_const _).add_const _
    have : (𝓝[Set.Ioo 0 s] (0 : ℝ)).NeBot := left_nhdsWithin_Ioo_neBot hpos
    have h := ge_of_tendsto hlim (eventually_nhdsWithin_of_forall key)
    simpa using h
  -- conclusion
  have hcomp := hVi t k a σ hk2 le_rfl
  rw [← hcomp]
  refine (norm_le_pi_norm (V t) _).trans ((hmain t ⟨ht0, htT⟩).trans ?_)
  rw [hc]
  have hN : Cs * Real.exp (K * T) / (K * ε) < Wt := by
    have := Nat.le_ceil (Cs * Real.exp (K * T) / (K * ε))
    have h2 : ((⌈Cs * Real.exp (K * T) / (K * ε)⌉₊ + 1 : ℕ) : ℝ) ≤ Wt := by exact_mod_cast hWt
    push_cast at h2
    linarith
  rw [div_lt_iff₀ (by positivity)] at hN
  calc Cs / Wt / K * (Real.exp (K * T) - 1) ≤ Cs / Wt / K * Real.exp (K * T) := by
        gcongr; linarith
    _ = Cs * Real.exp (K * T) / (K * Wt) := by field_simp
    _ ≤ ε := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith

end LSBA
