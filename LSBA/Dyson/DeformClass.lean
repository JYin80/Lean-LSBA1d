import LSBA.Spectral.Counts

/-!
# The deformation class

The class `𝓑(ε)` of Hermitian `B = Bs + Bb` with `‖Bs‖ ≤ ε`, `rank Bb ≤ ε#ι` (Lemma A.21
[da:lem:deformed], Lemma G.1 [us:lem:local-law]), the count of eigenvalues above `ε` by the rank,
and the converse criterion used for the regular inverses of (9.3) [us:eq:regular].
-/

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section
open scoped Classical

namespace LSBA

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The class of Lemma A.21 [da:lem:deformed]: Hermitian `B = B_small + B_bad` with
`‖B_small‖ ≤ ε` (operator norm) and `rank B_bad ≤ ε n`, `n = #ι`. -/
def DeformClass (ε : ℝ) (B : Matrix ι ι ℂ) : Prop :=
  B.IsHermitian ∧ ∃ Bs Bb : Matrix ι ι ℂ, B = Bs + Bb ∧ ‖Bs‖ ≤ ε ∧
    (Bb.rank : ℝ) ≤ ε * Fintype.card ι

omit [DecidableEq ι] in
/-- Squared norm of a linear combination of an orthonormal family. -/
private lemma deformClass_norm_sq_sum {κ : Type*} [Fintype κ]
    {v : κ → EuclideanSpace ℂ ι} (hv : Orthonormal ℂ v) (c : κ → ℂ) :
    ‖∑ k, c k • v k‖ ^ 2 = ∑ k, ‖c k‖ ^ 2 := by
  have h := hv.inner_sum c c Finset.univ
  have h2 : ((‖∑ k, c k • v k‖ : ℝ) : ℂ) ^ 2 = ∑ k, ((‖c k‖ : ℝ) : ℂ) ^ 2 := by
    have e := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (∑ k, c k • v k)
    rw [h] at e
    refine Eq.trans e.symm ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.conj_mul']
  exact_mod_cast h2

/-- The count in the proof of Lemma A.21 [da:lem:deformed]:
`#{λ(B) ∉ [-ε, ε]} ≤ rank B_bad`. -/
theorem countIn_abs_gt_le_rank {B Bs Bb : Matrix ι ι ℂ} (hB : B.IsHermitian) {ε : ℝ}
    (hsum : B = Bs + Bb) (hs : ‖Bs‖ ≤ ε) :
    countIn B {x | ε < |x|} ≤ Bb.rank := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hs
  set U := hB.eigenvectorBasis with hU
  set S : Finset ι := Finset.univ.filter fun k => ε < |hB.eigenvalues k| with hS
  have hcount : countIn B {x | ε < |x|} = Fintype.card S := by
    simp [countIn, hB, ← hS]
  rw [hcount]
  have hortho : Orthonormal ℂ (fun k : S => (U k)) :=
    U.orthonormal.comp _ Subtype.val_injective
  let M : (S → ℂ) →ₗ[ℂ] (ι → ℂ) := Fintype.linearCombination ℂ (fun k : S => (U k).ofLp)
  have hinj : Function.Injective (Bb.mulVecLin ∘ₗ M) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hc' : Bb *ᵥ (M c) = 0 := hc
    have hMc : M c = ∑ k : S, c k • (U k).ofLp := Fintype.linearCombination_apply _ _ _
    have hBw : B *ᵥ (M c) = ∑ k : S, (c k * (hB.eigenvalues k : ℂ)) • (U k).ofLp := by
      rw [hMc, Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.mulVec_smul, hB.mulVec_eigenvectorBasis]
      ext i
      simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul, hU]
      ring
    have hBs : Bs *ᵥ (M c) = B *ᵥ (M c) := by
      rw [hsum, Matrix.add_mulVec, hc', add_zero]
    set x : EuclideanSpace ℂ ι := WithLp.toLp 2 (M c) with hx
    have hxsum : x = ∑ k : S, c k • U k := by
      rw [hx, hMc]; ext i; simp
    have hBxsum : WithLp.toLp 2 (Bs *ᵥ (M c)) =
        ∑ k : S, (c k * (hB.eigenvalues k : ℂ)) • U k := by
      rw [hBs, hBw]; ext i; simp
    have hbound := Matrix.l2_opNorm_mulVec Bs x
    have hb2 : ‖WithLp.toLp 2 (Bs *ᵥ (M c))‖ ≤ ε * ‖x‖ :=
      hbound.trans (mul_le_mul_of_nonneg_right hs (norm_nonneg _))
    have hsq : ‖WithLp.toLp 2 (Bs *ᵥ (M c))‖ ^ 2 ≤ ε ^ 2 * ‖x‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hb2 2
    rw [hBxsum, deformClass_norm_sq_sum hortho, hxsum, deformClass_norm_sq_sum hortho] at hsq
    have hterm : ∀ k : S, 0 ≤ (hB.eigenvalues k ^ 2 - ε ^ 2) * ‖c k‖ ^ 2 := by
      intro k
      have hk : ε < |hB.eigenvalues k| := (Finset.mem_filter.mp k.2).2
      have : ε ^ 2 < hB.eigenvalues k ^ 2 := by
        rw [← sq_abs (hB.eigenvalues k)]
        exact pow_lt_pow_left₀ hk hε two_ne_zero
      exact mul_nonneg (by linarith) (sq_nonneg _)
    have hsum0 : ∑ k : S, (hB.eigenvalues k ^ 2 - ε ^ 2) * ‖c k‖ ^ 2 ≤ 0 := by
      have : ∑ k : S, (hB.eigenvalues k ^ 2 - ε ^ 2) * ‖c k‖ ^ 2 =
          ∑ k : S, ‖c k * (hB.eigenvalues k : ℂ)‖ ^ 2 - ε ^ 2 * ∑ k : S, ‖c k‖ ^ 2 := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [norm_mul, mul_pow]
        simp [Complex.norm_real, sq_abs]
        ring
      rw [this]; linarith
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hterm k).mp
      (le_antisymm hsum0 (Finset.sum_nonneg fun k _ => hterm k))
    funext k
    have hk : ε < |hB.eigenvalues k| := (Finset.mem_filter.mp k.2).2
    have hpos : 0 < hB.eigenvalues k ^ 2 - ε ^ 2 := by
      rw [sub_pos, ← sq_abs (hB.eigenvalues k)]
      exact pow_lt_pow_left₀ hk hε two_ne_zero
    have h0 := hall k (Finset.mem_univ k)
    have : ‖c k‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hpos.ne'
      · exact h
    simpa using this
  have h1 := (LinearEquiv.ofInjective _ hinj).finrank_eq
  have h2 : Module.finrank ℂ (LinearMap.range (Bb.mulVecLin ∘ₗ M)) ≤ Bb.rank := by
    unfold Matrix.rank
    exact Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
  rw [Module.finrank_fintype_fun_eq_card] at h1
  exact h1.le.trans h2

/-- Spectral membership criterion for the class of Lemma A.21 [da:lem:deformed]: at most `ε n`
eigenvalues outside `[-s, s]` with `0 ≤ s ≤ ε`. -/
theorem deformClass_of_countIn_le {B : Matrix ι ι ℂ} (hB : B.IsHermitian) {s ε : ℝ}
    (hs : 0 ≤ s) (hsε : s ≤ ε)
    (hcount : (countIn B {x | s < |x|} : ℝ) ≤ ε * Fintype.card ι) : DeformClass ε B := by
  set U : Matrix ι ι ℂ := (hB.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hUu : U ∈ unitary (Matrix ι ι ℂ) := hB.eigenvectorUnitary.2
  let ds : ι → ℂ := fun k => if |hB.eigenvalues k| ≤ s then (hB.eigenvalues k : ℂ) else 0
  let db : ι → ℂ := fun k => if |hB.eigenvalues k| ≤ s then 0 else (hB.eigenvalues k : ℂ)
  have hspec : B = U * Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues) * star U := by
    have := hB.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hdd : (RCLike.ofReal ∘ hB.eigenvalues : ι → ℂ) = ds + db := by
    funext k
    simp only [Function.comp_apply, Pi.add_apply, ds, db]
    split_ifs <;> simp
  refine ⟨hB, U * Matrix.diagonal ds * star U, U * Matrix.diagonal db * star U, ?_, ?_, ?_⟩
  · have hD : Matrix.diagonal (ds + db) = Matrix.diagonal ds + Matrix.diagonal db :=
      (Matrix.diagonal_add ds db).symm
    conv_lhs => rw [hspec, hdd, hD]
    rw [Matrix.mul_add, Matrix.add_mul]
  · by_cases hne : Nonempty ι
    · have hn : ‖U‖ = 1 := CStarRing.norm_of_mem_unitary hUu
      have hn' : ‖star U‖ = 1 := CStarRing.norm_of_mem_unitary (Unitary.star_mem hUu)
      have hd : ‖Matrix.diagonal ds‖ ≤ s := by
        rw [Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg hs]
        intro k
        simp only [ds]
        split_ifs with h
        · simpa [Complex.norm_real] using h
        · simpa using hs
      calc ‖U * Matrix.diagonal ds * star U‖
          ≤ ‖U * Matrix.diagonal ds‖ * ‖star U‖ := norm_mul_le _ _
        _ ≤ ‖U‖ * ‖Matrix.diagonal ds‖ * ‖star U‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ s := by rw [hn, hn', one_mul, mul_one]; exact hd
        _ ≤ ε := hsε
    · have : IsEmpty ι := not_nonempty_iff.mp hne
      rw [Subsingleton.elim (U * Matrix.diagonal ds * star U) 0, norm_zero]
      exact hs.trans hsε
  · have h1 : (U * Matrix.diagonal db * star U).rank ≤ (Matrix.diagonal db).rank :=
      (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    rw [Matrix.rank_diagonal] at h1
    have h2 : Fintype.card {i // db i ≠ 0} ≤ countIn B {x | s < |x|} := by
      rw [Fintype.card_subtype]
      simp only [countIn, hB, ↓reduceDIte]
      refine Finset.card_le_card fun k hk => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      by_contra hcon
      apply hk
      have hle : |hB.eigenvalues k| ≤ s := not_lt.mp hcon
      simp [db, hle]
    calc ((U * Matrix.diagonal db * star U).rank : ℝ) ≤ (countIn B {x | s < |x|} : ℝ) := by
          exact_mod_cast h1.trans h2
      _ ≤ ε * Fintype.card ι := hcount

end LSBA
