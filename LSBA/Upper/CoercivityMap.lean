import Mathlib

/-!
# The structured map `𝓛_G` and its smallest singular value

The map `𝓛_G P = (G_j P + P* G_j)_j` of (G.10) [cg:eq:LG], its smallest singular value on
`𝒬_W = {P : Im Tr P = 0}` as the infimum `S_W(G)` of `‖𝓛_G P‖` over unit `P ∈ 𝒬_W`, the bounds
`S_W(G) ≤ 2 (Σ_j ‖G_j‖²)^{1/2}` and `|S_W(G) - S_W(G')| ≤ 2 ‖G - G'‖`, the smallest eigenvalue
`inf_{‖y‖=1} Σ_j ‖G_j y‖²` of `Σ_j G_j²` for Hermitian `G_j` (Lemma G.4 [lem:c-gaussian],
Appendix G.4 [app:compact-gaussian]). Hilbert–Schmidt norms for `P` and for arrays; operator
norms for single matrices.
-/

open Real Finset
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The squared Hilbert–Schmidt norm `Σ_{a,b} |A_{ab}|²`. -/
def hsSq {k l : Type*} [Fintype k] [Fintype l] (A : Matrix k l ℂ) : ℝ :=
  ∑ a, ∑ b, ‖A a b‖ ^ 2

/-- The structured map `𝓛_G P = (G_j P + P* G_j)_j` of (G.10) [cg:eq:LG]. -/
def cohMap {m W : ℕ} (G : Fin m → Matrix (Fin W) (Fin W) ℂ) (P : Matrix (Fin W) (Fin W) ℂ) :
    Fin m → Matrix (Fin W) (Fin W) ℂ :=
  fun j => G j * P + Pᴴ * G j

/-- `S_W(G)`: the smallest singular value of `𝓛_G` on `𝒬_W = {P : Im Tr P = 0}` (Lemma G.4
[lem:c-gaussian]), as the infimum of `‖𝓛_G P‖` over `P ∈ 𝒬_W` with `‖P‖ = 1`. -/
def coerMin {m W : ℕ} (G : Fin m → Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  ⨅ P : {P : Matrix (Fin W) (Fin W) ℂ // P.trace.im = 0 ∧ hsSq P = 1},
    Real.sqrt (∑ j, hsSq (cohMap G P.1 j))

/-- `λ_min(Σ_j G_j*G_j) = inf_{‖y‖=1} Σ_j ‖G_j y‖²` (the smallest eigenvalue of
`S = Σ_j G_j²` in the proof of Lemma G.4 [lem:c-gaussian] for Hermitian `G_j`). -/
def quadMin {m W : ℕ} (G : Fin m → Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  ⨅ y : {y : Fin W → ℂ // ∑ a, ‖y a‖ ^ 2 = 1}, ∑ j, ∑ a, ‖(G j *ᵥ y.1) a‖ ^ 2

section CoercivityMapAux

private lemma CoercivityMap_hsSq_nonneg {k l : Type*} [Fintype k] [Fintype l] (A : Matrix k l ℂ) :
    0 ≤ hsSq A := by
  unfold hsSq; positivity

private lemma CoercivityMap_hsSq_smul {k l : Type*} [Fintype k] [Fintype l] (r : ℝ)
    (A : Matrix k l ℂ) : hsSq (r • A) = r ^ 2 * hsSq A := by
  unfold hsSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [mul_pow, sq_abs]

private lemma CoercivityMap_hsSq_neg {k l : Type*} [Fintype k] [Fintype l] (A : Matrix k l ℂ) :
    hsSq (-A) = hsSq A := by
  unfold hsSq; simp

private lemma CoercivityMap_hsSq_conjTranspose {k l : Type*} [Fintype k] [Fintype l]
    (A : Matrix k l ℂ) : hsSq Aᴴ = hsSq A := by
  unfold hsSq
  rw [Finset.sum_comm]
  simp [Matrix.conjTranspose_apply]

private lemma CoercivityMap_sum_sq_mulVec_le {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ)
    (x : Fin W → ℂ) : ∑ a, ‖(A *ᵥ x) a‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ c, ‖x c‖ ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec A ((EuclideanSpace.equiv (Fin W) ℂ).symm x)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)] at h2
  simpa using h2

private lemma CoercivityMap_hsSq_mul_opNorm_le {W : ℕ} (A B : Matrix (Fin W) (Fin W) ℂ) :
    hsSq (A * B) ≤ ‖A‖ ^ 2 * hsSq B := by
  have hB : ‖A‖ ^ 2 * hsSq B = ∑ b, ‖A‖ ^ 2 * ∑ c, ‖B c b‖ ^ 2 := by
    unfold hsSq; rw [Finset.sum_comm, Finset.mul_sum]
  rw [hB]
  unfold hsSq
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun b _ => ?_
  have := CoercivityMap_sum_sq_mulVec_le A (fun c => B c b)
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

private lemma CoercivityMap_hsSq_mul_le {k l n : Type*} [Fintype k] [Fintype l] [Fintype n]
    (A : Matrix k l ℂ) (B : Matrix l n ℂ) : hsSq (A * B) ≤ hsSq A * hsSq B := by
  unfold hsSq
  calc ∑ a, ∑ b, ‖(A * B) a b‖ ^ 2
      ≤ ∑ a, ∑ b, ((∑ c, ‖A a c‖ ^ 2) * ∑ c, ‖B c b‖ ^ 2) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        calc ‖(A * B) a b‖ ^ 2 ≤ (∑ c, ‖A a c‖ * ‖B c b‖) ^ 2 := by
              rw [Matrix.mul_apply]
              refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
              refine (norm_sum_le _ _).trans ?_
              simp
          _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ a, ∑ c, ‖A a c‖ ^ 2) * ∑ b, ∑ c, ‖B c b‖ ^ 2 := by
        rw [← Finset.sum_mul_sum]
    _ = _ := by rw [Finset.sum_comm (f := fun b c => ‖B c b‖ ^ 2)]

private lemma CoercivityMap_sqrt_sum_hsSq_add_le {m W : ℕ}
    (A B : Fin m → Matrix (Fin W) (Fin W) ℂ) :
    Real.sqrt (∑ j, hsSq (A j + B j)) ≤
      Real.sqrt (∑ j, hsSq (A j)) + Real.sqrt (∑ j, hsSq (B j)) := by
  let e : (Fin m → Matrix (Fin W) (Fin W) ℂ) → EuclideanSpace ℂ (Fin m × Fin W × Fin W) :=
    fun A => WithLp.toLp 2 (fun x => A x.1 x.2.1 x.2.2)
  have hnorm : ∀ A : Fin m → Matrix (Fin W) (Fin W) ℂ,
      Real.sqrt (∑ j, hsSq (A j)) = ‖e A‖ := by
    intro A
    rw [EuclideanSpace.norm_eq]
    congr 1
    simp [e, hsSq, Fintype.sum_prod_type]
  have hadd : e (A + B) = e A + e B := by
    ext x; simp [e]
  have h : Real.sqrt (∑ j, hsSq (A j + B j)) = ‖e A + e B‖ := by
    rw [← hadd]; exact hnorm (A + B)
  rw [h, hnorm A, hnorm B]
  exact norm_add_le _ _

private lemma CoercivityMap_sqrt_cohMap_le {m W : ℕ} (H : Fin m → Matrix (Fin W) (Fin W) ℂ)
    {P : Matrix (Fin W) (Fin W) ℂ} (c : Fin m → ℝ)
    (h1 : ∀ j, hsSq (H j * P) ≤ c j) (h2 : ∀ j, hsSq (Pᴴ * H j) ≤ c j) :
    Real.sqrt (∑ j, hsSq (cohMap H P j)) ≤ 2 * Real.sqrt (∑ j, c j) := by
  have := CoercivityMap_sqrt_sum_hsSq_add_le (fun j => H j * P) (fun j => Pᴴ * H j)
  have a1 : Real.sqrt (∑ j, hsSq (H j * P)) ≤ Real.sqrt (∑ j, c j) :=
    Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => h1 j)
  have a2 : Real.sqrt (∑ j, hsSq (Pᴴ * H j)) ≤ Real.sqrt (∑ j, c j) :=
    Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => h2 j)
  unfold cohMap
  linarith

end CoercivityMapAux

/-- The singular-value bound at every `P ∈ 𝒬_W`: `S_W(G) ‖P‖ ≤ ‖𝓛_G P‖` (Lemma G.4
[lem:c-gaussian], as used for (10.14) [eq:c-main-coercivity]). -/
theorem coerMin_mul_le {m W : ℕ} (G : Fin m → Matrix (Fin W) (Fin W) ℂ)
    {P : Matrix (Fin W) (Fin W) ℂ} (hP : P.trace.im = 0) :
    coerMin G * Real.sqrt (hsSq P) ≤ Real.sqrt (∑ j, hsSq (cohMap G P j)) := by
  have hbdd : BddBelow (Set.range fun Q : {Q : Matrix (Fin W) (Fin W) ℂ //
      Q.trace.im = 0 ∧ hsSq Q = 1} => Real.sqrt (∑ j, hsSq (cohMap G Q.1 j))) :=
    ⟨0, by rintro _ ⟨Q, rfl⟩; exact Real.sqrt_nonneg _⟩
  rcases (CoercivityMap_hsSq_nonneg P).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · have hspos : 0 < Real.sqrt (hsSq P) := Real.sqrt_pos.2 hpos
    have hs2 : Real.sqrt (hsSq P) ^ 2 = hsSq P := Real.sq_sqrt hpos.le
    set s := Real.sqrt (hsSq P) with hs
    have hr : s⁻¹ * s = 1 := inv_mul_cancel₀ hspos.ne'
    have hmem : (s⁻¹ • P).trace.im = 0 ∧ hsSq (s⁻¹ • P) = 1 := by
      refine ⟨?_, ?_⟩
      · rw [Matrix.trace_smul, Complex.smul_im, hP]; simp
      · rw [CoercivityMap_hsSq_smul, ← hs2]
        field_simp
    have hc : ∀ j, cohMap G (s⁻¹ • P) j = s⁻¹ • cohMap G P j := by
      intro j
      simp [cohMap, Matrix.conjTranspose_smul, smul_add]
    have h := ciInf_le hbdd (⟨s⁻¹ • P, hmem⟩ : {Q : Matrix (Fin W) (Fin W) ℂ //
      Q.trace.im = 0 ∧ hsSq Q = 1})
    have hco : coerMin G ≤ s⁻¹ * Real.sqrt (∑ j, hsSq (cohMap G P j)) := by
      refine h.trans (le_of_eq ?_)
      simp only [hc, CoercivityMap_hsSq_smul]
      rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.2 hspos.le)]
    calc coerMin G * s ≤ s⁻¹ * Real.sqrt (∑ j, hsSq (cohMap G P j)) * s :=
          mul_le_mul_of_nonneg_right hco hspos.le
      _ = Real.sqrt (∑ j, hsSq (cohMap G P j)) := by
          rw [mul_comm, ← mul_assoc, mul_comm s, hr, one_mul]

/-- `0 ≤ S_W(G) ≤ 2 (Σ_j ‖G_j‖²)^{1/2}` (proof of Lemma G.4 [lem:c-gaussian]). -/
theorem coerMin_le {m W : ℕ} (G : Fin m → Matrix (Fin W) (Fin W) ℂ) :
    0 ≤ coerMin G ∧ coerMin G ≤ 2 * Real.sqrt (∑ j, ‖G j‖ ^ 2) := by
  have hnn : 0 ≤ coerMin G := Real.iInf_nonneg fun _ => Real.sqrt_nonneg _
  refine ⟨hnn, ?_⟩
  rcases isEmpty_or_nonempty {P : Matrix (Fin W) (Fin W) ℂ // P.trace.im = 0 ∧ hsSq P = 1} with
    hE | ⟨⟨P, hPim, hP1⟩⟩
  · have : coerMin G = 0 := Real.iInf_of_isEmpty _
    rw [this]; positivity
  · have hbdd : BddBelow (Set.range fun Q : {Q : Matrix (Fin W) (Fin W) ℂ //
        Q.trace.im = 0 ∧ hsSq Q = 1} => Real.sqrt (∑ j, hsSq (cohMap G Q.1 j))) :=
      ⟨0, by rintro _ ⟨Q, rfl⟩; exact Real.sqrt_nonneg _⟩
    refine (ciInf_le hbdd (⟨P, hPim, hP1⟩ : {Q : Matrix (Fin W) (Fin W) ℂ //
      Q.trace.im = 0 ∧ hsSq Q = 1})).trans ?_
    refine CoercivityMap_sqrt_cohMap_le G (fun j => ‖G j‖ ^ 2) ?_ ?_
    · intro j
      simpa [hP1] using CoercivityMap_hsSq_mul_opNorm_le (G j) P
    · intro j
      rw [← CoercivityMap_hsSq_conjTranspose, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
      have := CoercivityMap_hsSq_mul_opNorm_le (G j)ᴴ P
      rw [Matrix.l2_opNorm_conjTranspose] at this
      simpa [hP1] using this

/-- `G ↦ S_W(G)` is `2`-Lipschitz in the Hilbert–Schmidt product norm (proof of Lemma G.4
[lem:c-gaussian]). -/
theorem abs_coerMin_sub_le {m W : ℕ} (G G' : Fin m → Matrix (Fin W) (Fin W) ℂ) :
    |coerMin G - coerMin G'| ≤ 2 * Real.sqrt (∑ j, hsSq (G j - G' j)) := by
  have key : ∀ G G' : Fin m → Matrix (Fin W) (Fin W) ℂ,
      coerMin G ≤ coerMin G' + 2 * Real.sqrt (∑ j, hsSq (G j - G' j)) := by
    intro G G'
    have hD : 0 ≤ 2 * Real.sqrt (∑ j, hsSq (G j - G' j)) := by positivity
    rcases isEmpty_or_nonempty {P : Matrix (Fin W) (Fin W) ℂ // P.trace.im = 0 ∧ hsSq P = 1}
      with hE | hN
    · have h1 : coerMin G = 0 := Real.iInf_of_isEmpty _
      have h2 : coerMin G' = 0 := Real.iInf_of_isEmpty _
      rw [h1, h2]; linarith
    · have hbdd : ∀ G : Fin m → Matrix (Fin W) (Fin W) ℂ, BddBelow (Set.range
          fun Q : {Q : Matrix (Fin W) (Fin W) ℂ // Q.trace.im = 0 ∧ hsSq Q = 1} =>
            Real.sqrt (∑ j, hsSq (cohMap G Q.1 j))) :=
        fun G => ⟨0, by rintro _ ⟨Q, rfl⟩; exact Real.sqrt_nonneg _⟩
      have : coerMin G - 2 * Real.sqrt (∑ j, hsSq (G j - G' j)) ≤ coerMin G' := by
        refine le_ciInf fun ⟨P, hPim, hP1⟩ => ?_
        have h1 := ciInf_le (hbdd G) (⟨P, hPim, hP1⟩ : {Q : Matrix (Fin W) (Fin W) ℂ //
          Q.trace.im = 0 ∧ hsSq Q = 1})
        have hsplit : cohMap G P = fun j => cohMap G' P j + cohMap (G - G') P j := by
          funext j
          simp [cohMap, sub_mul, mul_sub]
          abel
        have h2 := CoercivityMap_sqrt_sum_hsSq_add_le (cohMap G' P) (cohMap (G - G') P)
        have h3 := CoercivityMap_sqrt_cohMap_le (G - G') (P := P)
          (fun j => hsSq (G j - G' j)) ?_ ?_
        · have h1' : coerMin G ≤ Real.sqrt (∑ j, hsSq (cohMap G P j)) := h1
          rw [hsplit] at h1'
          change coerMin G - 2 * Real.sqrt (∑ j, hsSq (G j - G' j)) ≤
            Real.sqrt (∑ j, hsSq (cohMap G' P j))
          linarith
        · intro j
          simpa [hP1] using CoercivityMap_hsSq_mul_le ((G - G') j) P
        · intro j
          simpa [hP1, CoercivityMap_hsSq_conjTranspose] using
            CoercivityMap_hsSq_mul_le Pᴴ ((G - G') j)
      linarith
  have swap : ∀ G G' : Fin m → Matrix (Fin W) (Fin W) ℂ, ∑ j, hsSq (G' j - G j) =
      ∑ j, hsSq (G j - G' j) := by
    intro G G'
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← neg_sub, CoercivityMap_hsSq_neg]
  rw [abs_le]
  have a := key G G'
  have b := key G' G
  rw [swap] at b
  constructor <;> linarith

end LSBA
