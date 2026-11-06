import LSBA.Prop.StepDefs

/-!
# Input statements of the general Theorem 5.12 [gc:thm:common]

The segment heights and objects of Lemma 5.9 [gc:lem:residual], the residual (5.27)
[gc:eq:positive-dyson]–(5.28) [gc:eq:residual-input], the
scalar identity, the input statements of Lemma 5.10 [fo:lem:sampling-continuity] (a) (crude
moments), Lemma 5.9 [gc:lem:residual] (averaging), Lemmas 5.8 [uvc:thm:ordinary-sampling] and
5.10(b) [fo:lem:sampling-continuity] (sampling)
and the weighted sampling (5.34) [fo:eq:weighted-sampling-input] with constant `C_w`, their bundle,
and the explicit constants `c_*`, `M`, `N₀` of the mixed-pair bound.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The spectral heights at `p` used by Lemmas 5.9 [gc:lem:residual] and 5.10
[fo:lem:sampling-continuity]: the characteristic height `η_u`, and, when `d < J`, every height of
a comparison segment `[η_u, Im w]` of Lemma 6.4 [da:lem:positive-height] for an earlier time
`s ∈ [1/2, u]`. -/
def SegHeight (J d : ℕ) (p : FlowPt) (y : ℝ) : Prop :=
  y = etaChar p.g (mRoot p.g p.L p.E) p.u ∨
    (d < J ∧ ∃ s : ℝ, 1 / 2 ≤ s ∧ s ≤ p.u ∧ etaChar p.g (mRoot p.g p.L p.E) p.u ≤ y ∧
      y ≤ (wCmp p.g p.L p.E (mRoot p.g p.L p.E) s p.u).im)

/-- Admissible pairs `(p, y)`: `p` reached with depth `d ≤ J` and `y` one of its heights. -/
def SegAdm (base : ℕ → Set FlowPt) (J W : ℕ) (x : FlowPt × ℝ) : Prop :=
  ∃ d : ℕ, d ≤ J ∧ CmpReach base W d x.1 ∧ SegHeight J d x.1 x.2

/-- `G = (H_u(g) - z)⁻¹` at `z = Re z_u + iy`. -/
def segG (W : ℕ) (x : FlowPt × ℝ) (ω : Ω W x.1.L) :
    Matrix (Fin x.1.L × Fin W) (Fin x.1.L × Fin W) ℂ :=
  resolventMat (flowH x.1.g W x.1.L x.1.u ω)
    (((zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re : ℂ) + (x.2 : ℂ) * Complex.I)

/-- `M_u(z) = M_{B,u}(z) ⊗ I_W` of (5.27) [gc:eq:positive-dyson] at `z = Re z_u + iy`. -/
def segM (W : ℕ) (x : FlowPt × ℝ) : Matrix (Fin x.1.L × Fin W) (Fin x.1.L × Fin W) ℂ :=
  segMat x.1.g x.1.L (zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re x.1.u
    (x.2 / gammaG x.1.g) ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)

/-- `Π(G) = I + (z - A_g ⊗ I)G + uγ_g diag(⟨G⟩_{aa} I_W) G` of (5.28) [gc:eq:residual-input]. -/
def resPi {W L : ℕ} (g u : ℝ) (z : ℂ) (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  1 + (z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) -
      Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) * G +
    ((u * gammaG g : ℝ) : ℂ) • (Matrix.diagonal (fun x : Fin L × Fin W => blockTr G x.1 x.1) * G)

/-- The residual `R_{ab} = ⟨M_u(z) Π(G)⟩_{ab}` of (5.28) [gc:eq:residual-input]. -/
def segRes (W : ℕ) (x : FlowPt × ℝ) (ω : Ω W x.1.L) (a b : Fin x.1.L) : ℂ :=
  blockTr (segM W x * resPi x.1.g x.1.u
    (((zChar x.1.g x.1.E (mRoot x.1.g x.1.L x.1.E) x.1.u).re : ℂ) + (x.2 : ℂ) * Complex.I)
    (segG W x ω)) a b

/-- The residual `R_{ab}` of (5.28) [gc:eq:residual-input] on the characteristic `z = z_u`, with
`M_u(z_u) = M_B ⊗ I`. -/
def flowRes (W : ℕ) (p : FlowPt) (ω : Ω W p.L) (a b : Fin p.L) : ℂ :=
  blockTr (flowM W p * resPi p.g p.u (zChar p.g p.E (mRoot p.g p.L p.E) p.u) (flowG W p ω)) a b

/-- `b A_L` is Hermitian for real `b`. -/
private lemma inputs_smul_cycleAdj_isHermitian (b : ℝ) (L : ℕ) :
    (((b : ℝ) : ℂ) • cycleAdj L).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, (cycleAdj_isHermitian L).eq, Complex.star_def, Complex.conj_ofReal]

/-- `(bA_L - w)` and the Dyson matrix `(bA_L - w)⁻¹` are mutually inverse when `Im w > 0`,
`w = z + βm`. -/
private lemma inputs_dysonMat_mul (b β : ℝ) (L : ℕ) (z m : ℂ) (hw : 0 < (z + β * m).im) :
    (((b : ℝ) : ℂ) • cycleAdj L - (z + β * m) • (1 : Matrix (Fin L) (Fin L) ℂ)) *
        dysonMat b β L z m = 1 ∧
      dysonMat b β L z m *
        (((b : ℝ) : ℂ) • cycleAdj L - (z + β * m) • (1 : Matrix (Fin L) (Fin L) ℂ)) = 1 := by
  have h := sub_smul_mul_resolventMat (inputs_smul_cycleAdj_isHermitian b L) hw.ne'
  exact ⟨h, mul_eq_one_comm.mp h⟩

/-- Rows of `(M ⊗ I_W) X`: `((M ⊗ I) X)_{(a,α),y} = Σ_c M_{ac} X_{(c,α),y}`. -/
private lemma inputs_kron_mul_apply (W L : ℕ) (M : Matrix (Fin L) (Fin L) ℂ)
    (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a : Fin L) (α : Fin W) (y : Fin L × Fin W) :
    ((M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) * X) (a, α) y = ∑ c : Fin L, M a c * X (c, α) y := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero]
  simp

/-- `⟨(M ⊗ I) diag(d_c I_W) G⟩_{ab} = Σ_c M_{ac} d_c ⟨G⟩_{cb}`. -/
private lemma inputs_blockTr_mul_diag (W L : ℕ) (M : Matrix (Fin L) (Fin L) ℂ) (d : Fin L → ℂ)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) :
    blockTr ((M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) *
        (Matrix.diagonal (fun x : Fin L × Fin W => d x.1) * G)) a b =
      ∑ c : Fin L, M a c * d c * blockTr G c b := by
  unfold blockTr
  simp only [inputs_kron_mul_apply, Matrix.diagonal_mul]
  rw [Finset.mul_sum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

/-- `⟨M ⊗ I_W⟩_{ab} = M_{ab}` for `W ≥ 1`. -/
private lemma inputs_blockTr_kron (W L : ℕ) (hW : 1 ≤ W) (M : Matrix (Fin L) (Fin L) ℂ)
    (a b : Fin L) : blockTr (M ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) a b = M a b := by
  have hW0 : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold blockTr
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- If `M (A - w) = 1` then `(M ⊗ I)(A ⊗ I - w) = 1`. -/
private lemma inputs_kron_inv (W L : ℕ) (Mb A : Matrix (Fin L) (Fin L) ℂ) (w : ℂ)
    (h : Mb * (A - w • (1 : Matrix (Fin L) (Fin L) ℂ)) = 1) :
    (Mb ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) *
      (A ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) -
        w • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) = 1 := by
  have e : A ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) -
      w • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) =
      (A - w • (1 : Matrix (Fin L) (Fin L) ℂ)) ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) := by
    ext ⟨a, α⟩ ⟨b, β⟩
    simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.one_apply,
      Prod.mk.injEq, smul_eq_mul]
    by_cases hab : a = b <;> by_cases hαβ : α = β <;> simp [hab, hαβ]
  rw [e, ← Matrix.mul_kronecker_mul, h, Matrix.mul_one, Matrix.one_kronecker_one]

/-- The matrix form of the first identity of (5.32) [gc:eq:scalar], for every `G`: if
`M (A - w) = 1` and `z = w - β'm` then
`G - M⊗I = -(M⊗I) Π(G) + β' (M⊗I) diag(⟨G⟩_{cc} - m) G`. -/
private lemma inputs_identity (W L : ℕ) (Mb A : Matrix (Fin L) (Fin L) ℂ) (w z m β' : ℂ)
    (h : Mb * (A - w • (1 : Matrix (Fin L) (Fin L) ℂ)) = 1) (hz : z = w - β' * m)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :
    G - Mb ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) =
      -((Mb ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) *
        (1 + (z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) -
            A ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) * G +
          β' • (Matrix.diagonal (fun x : Fin L × Fin W => blockTr G x.1 x.1) * G))) +
      β' • ((Mb ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) *
        (Matrix.diagonal (fun x : Fin L × Fin W => blockTr G x.1 x.1 - m) * G)) := by
  set K := Mb ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) with hKdef
  have hK := inputs_kron_inv W L Mb A w h
  rw [← hKdef] at hK
  have hKz : K * (z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) -
      A ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) = -1 - (β' * m) • K := by
    have e : z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) -
        A ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) =
        -(A ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) -
          w • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)) -
          (β' * m) • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) := by
      rw [hz, sub_smul]; abel
    rw [e, Matrix.mul_sub, Matrix.mul_neg, hK, Matrix.mul_smul, Matrix.mul_one]
  have hD : Matrix.diagonal (fun x : Fin L × Fin W => blockTr G x.1 x.1 - m) =
      Matrix.diagonal (fun x : Fin L × Fin W => blockTr G x.1 x.1) -
        m • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) := by
    ext x y
    by_cases hxy : x = y
    · subst hxy; simp
    · simp [Matrix.diagonal_apply_ne _ hxy, Matrix.one_apply_ne hxy]
  have e1 : K * ((1 + (z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) -
        A ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) * G +
          β' • (Matrix.diagonal (fun x : Fin L × Fin W => blockTr G x.1 x.1) * G))) =
      K + (-G - (β' * m) • (K * G)) +
        β' • (K * (Matrix.diagonal (fun x : Fin L × Fin W => blockTr G x.1 x.1) * G)) := by
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hKz, Matrix.mul_smul]
    rw [sub_mul, Matrix.smul_mul, neg_mul, Matrix.one_mul]
  rw [e1, hD, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_smul]
  module

/-- `⟨·⟩_{ab}` is additive and homogeneous. -/
private lemma inputs_blockTr_sub {W L : ℕ} (X Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : blockTr (X - Y) a b = blockTr X a b - blockTr Y a b := by
  unfold blockTr
  simp only [Matrix.sub_apply, Finset.sum_sub_distrib, mul_sub]

private lemma inputs_blockTr_neg {W L : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : blockTr (-X) a b = -blockTr X a b := by
  unfold blockTr
  simp only [Matrix.neg_apply, Finset.sum_neg_distrib, mul_neg]

private lemma inputs_blockTr_add {W L : ℕ} (X Y : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : blockTr (X + Y) a b = blockTr X a b + blockTr Y a b := by
  unfold blockTr
  simp only [Matrix.add_apply, Finset.sum_add_distrib, mul_add]

private lemma inputs_blockTr_smul {W L : ℕ} (c : ℂ) (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : blockTr (c • X) a b = c * blockTr X a b := by
  unfold blockTr
  simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

/-- (5.32) [gc:eq:scalar], first identity, for every Hermitian matrix in place of `H_u(g)`:
`⟨G̃⟩_{ab} = -R_{ab} + uγ_g Σ_c (M_B)_{ac} ⟨G̃⟩_{cc} ⟨G⟩_{cb}` on the characteristic. -/
theorem scalar_identity (W : ℕ) (hW : 1 ≤ W) (p : FlowPt) (hm : 0 < (mRoot p.g p.L p.E).im)
    (hu : p.u < 1) (ω : Ω W p.L) (a b : Fin p.L) :
    blockTr (flowG W p ω - flowM W p) a b = -flowRes W p ω a b +
      ((p.u * gammaG p.g : ℝ) : ℂ) * ∑ c : Fin p.L,
        dysonMat (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E) a c *
          blockTr (flowG W p ω - flowM W p) c c * blockTr (flowG W p ω) c b := by
  unfold flowRes resPi flowM
  have hγ : 0 < gammaG p.g := by
    unfold gammaG
    have : (1 : ℝ) ≤ max 1 p.g := le_max_left _ _
    positivity
  have hex : ∃ m : ℂ, IsDysonRootV (hopB p.g) (gammaG p.g) p.L (p.E : ℂ) m := by
    by_contra h
    have h0 : mRoot p.g p.L p.E = 0 := by
      simp [mRoot, mRootV, h]
    rw [h0] at hm
    simp at hm
  have hroot : IsDysonRootV (hopB p.g) (gammaG p.g) p.L (p.E : ℂ) (mRoot p.g p.L p.E) := by
    simp only [mRoot, mRootV, hex, ↓reduceDIte]
    exact hex.choose_spec
  set m := mRoot p.g p.L p.E with hmdef
  have hw : 0 < ((p.E : ℂ) + (gammaG p.g : ℂ) * m).im := by
    simpa using mul_pos hγ hm
  have hL : 1 ≤ p.L := Fin.pos a
  have hdiag : ∀ c : Fin p.L, dysonMat (hopB p.g) (gammaG p.g) p.L p.E m c c = m := fun c => by
    rw [dysonMat_diag _ _ _ hL _ _ hw c]
    exact hroot.2.symm
  obtain ⟨-, hMA⟩ := inputs_dysonMat_mul (hopB p.g) (gammaG p.g) p.L (p.E : ℂ) m hw
  have key := inputs_identity W p.L (dysonMat (hopB p.g) (gammaG p.g) p.L p.E m) (Ag p.g p.L)
    ((p.E : ℂ) + (gammaG p.g : ℂ) * m) (zChar p.g p.E m p.u) m ((p.u * gammaG p.g : ℝ) : ℂ)
    hMA (by unfold zChar; push_cast; ring) (flowG W p ω)
  have hdg := inputs_blockTr_mul_diag W p.L (dysonMat (hopB p.g) (gammaG p.g) p.L p.E m)
    (fun c => blockTr (flowG W p ω) c c - m) (flowG W p ω) a b
  have key2 := congrArg (fun X => blockTr X a b) key
  simp only [inputs_blockTr_sub, inputs_blockTr_neg, inputs_blockTr_add,
    inputs_blockTr_smul] at key2
  rw [hdg] at key2
  simp only [inputs_blockTr_sub, inputs_blockTr_kron W p.L hW, hdiag]
  rw [inputs_blockTr_kron W p.L hW] at key2
  exact key2

open scoped Matrix.Norms.L2Operator in
/-- The first bound of (5.33) [fo:eq:coarse-time-input] at each fixed time, on the characteristic
and at the comparison-segment heights (Lemma 5.10 [fo:lem:sampling-continuity], last
paragraph): a fixed exponent `C₀` with `E‖G_{ab}‖^p ≤ C_p W^{C₀ p}` for every order `p`. -/
def CrudeInput (base : ℕ → Set FlowPt) (J : ℕ) : Prop :=
  ∃ C₀ : ℝ, ∀ p : ℕ, 1 ≤ p → ∃ Cp : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ x, SegAdm base J W x →
    ∀ a b : Fin x.1.L, Integrable (fun ω => ‖blockOf (segG W x ω) a b‖ ^ p) (μ W x.1.L) ∧
      ∫ ω, ‖blockOf (segG W x ω) a b‖ ^ p ∂(μ W x.1.L) ≤ Cp * (W : ℝ) ^ (C₀ * p)

/-- Lemma 5.9 [gc:lem:residual] at the admissible pairs, under the original Gaussian law:
(i) the averaged-residual implication (5.29) [gc:eq:averaging-input], (ii) the entrywise
implication (5.30) [gc:eq:haar] for each pair of blocks, for a deterministic `Ψ > 0`, (iii) the
residual moments (5.31) [fo:eq:residual-moments]; uniform over families of admissible pairs. -/
def AveragingInput (base : ℕ → Set FlowPt) (J : ℕ) : Prop :=
  (∀ Dom : ℕ → Set (FlowPt × ℝ), (∀ W x, x ∈ Dom W → SegAdm base J W x) →
    ∀ (K χ : ℕ → FlowPt × ℝ → ℝ) (CK : ℝ), (∀ W x, x ∈ Dom W →
      1 ≤ K W x ∧ K W x ≤ (W : ℝ) ^ CK ∧ (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ χ W x) →
    PrecMax (fun x : FlowPt × ℝ => x.1.L) Dom (Λ := fun _ x => Fin x.1.L × Fin x.1.L)
      (fun W x ab ω => blockTr (segG W x ω) ab.1 ab.2) (fun W x _ => K W x) →
    PrecMax (fun x : FlowPt × ℝ => x.1.L) Dom
      (Λ := fun W x => (Fin x.1.L × Fin W) × (Fin x.1.L × Fin W))
      (fun W x e ω => segG W x ω e.1 e.2 -
        if e.1.2 = e.2.2 then blockTr (segG W x ω) e.1.1 e.2.1 else 0)
      (fun W x _ => K W x * χ W x) →
    PrecMax (fun x : FlowPt × ℝ => x.1.L) Dom (Λ := fun _ x => Fin x.1.L × Fin x.1.L)
      (fun W x ab ω => segRes W x ω ab.1 ab.2) (fun W x _ => (K W x * χ W x) ^ 2)) ∧
  (∀ Dom : ℕ → Set (FlowPt × ℝ), (∀ W x, x ∈ Dom W → SegAdm base J W x) →
    ∀ Ψ : ℕ → FlowPt × ℝ → ℝ, (∀ W x, x ∈ Dom W → 0 < Ψ W x) →
    (∀ ε D : ℝ, 0 < ε → 0 < D → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ x ∈ Dom W, ∀ a b : Fin x.1.L,
      μ W x.1.L {ω | (W : ℝ) ^ ε * Ψ W x ^ 2 < ((W : ℝ) ^ 2)⁻¹ * blockHS2 (segG W x ω) a b} ≤
        ENNReal.ofReal ((W : ℝ) ^ (-D))) →
    ∀ ε D : ℝ, 0 < ε → 0 < D → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ x ∈ Dom W, ∀ a b : Fin x.1.L,
      μ W x.1.L {ω | ∃ i j : Fin W, (W : ℝ) ^ ε * Ψ W x <
        ‖segG W x ω (a, i) (b, j) - if i = j then blockTr (segG W x ω) a b else 0‖} ≤
        ENNReal.ofReal ((W : ℝ) ^ (-D))) ∧
  (∀ p : ℕ, 2 ≤ p → Even p → ∀ C : ℝ, 0 < C → ∃ Cp : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
    ∀ x, SegAdm base J W x → ∀ χ : ℝ, (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ χ →
    (∀ e₁ e₂ : Fin x.1.L × Fin W,
      Integrable (fun ω => ‖(segG W x ω - segM W x) e₁ e₂‖ ^ (2 * p)) (μ W x.1.L) ∧
      (∫ ω, ‖(segG W x ω - segM W x) e₁ e₂‖ ^ (2 * p) ∂(μ W x.1.L)) ^ (1 / (2 * (p : ℝ))) ≤
        C * χ) →
    ∀ a b : Fin x.1.L, Integrable (fun ω => ‖segRes W x ω a b‖ ^ p) (μ W x.1.L) ∧
      ∫ ω, ‖segRes W x ω a b‖ ^ p ∂(μ W x.1.L) ≤ Cp * χ ^ (2 * p))

/-- The sampling inequality (5.34) [fo:eq:weighted-sampling-input] at one time: with probability
at least `1 - η`, `max_λ ‖X_λ‖/w_λ ≤ C max_{λ ∈ S} ‖X_λ‖/w_λ + δ`. -/
def SampleBound {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') {Λ : Type*}
    (X : Λ → Ω' → ℂ) (w : Λ → ℝ) (S : Finset Λ) (C δ η : ℝ) : Prop :=
  P {ω | ∃ l, C * (⨆ s : S, ‖X s ω‖ / w s) + δ < ‖X l ω‖ / w l} ≤ ENNReal.ofReal η

/-- Lemma 5.10(b) [fo:lem:sampling-continuity] with Lemma 5.8 [uvc:thm:ordinary-sampling] at each
fixed time: (1) loops and loop errors at every time `u ≤ t` of a reached point, unweighted and with
the weight `e^{-c(diam/ℓ_u)^θ} + W^{-F}`, with one sample set of at most `W^{C_S}` label words for
all times and signs; (2) centered block traces `⟨G - M_u(z)⟩_{ab}`, traceless entries and residuals
at each admissible pair, with `w = 1` (the sample sets may depend on the pair). -/
def SamplingInput (base : ℕ → Set FlowPt) (J : ℕ) : Prop :=
  (∀ k : ℕ, 1 ≤ k → ∀ cw θ F : ℝ, 0 < cw → 0 < θ → θ ≤ 1 / 2 → 0 < F → ∀ D D' : ℝ, 0 < D →
    0 < D' → ∃ CS Cs : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ d p, d ≤ J → CmpReach base W d p →
      ∃ S : Finset (Fin k → Fin p.L), (S.card : ℝ) ≤ (W : ℝ) ^ CS ∧
        ∀ (σ : Fin k → Bool) (u : ℝ), 0 ≤ u → u ≤ p.u →
          SampleBound (μ W p.L) (fun a ω => loopTr (flowG W ⟨p.g, p.E, p.L, u⟩ ω) a σ)
            (fun _ => 1) S Cs ((W : ℝ) ^ (-D)) ((W : ℝ) ^ (-D')) ∧
          SampleBound (μ W p.L) (fun a ω => flowErr W ⟨p.g, p.E, p.L, u⟩ a σ ω)
            (fun _ => 1) S Cs ((W : ℝ) ^ (-D)) ((W : ℝ) ^ (-D')) ∧
          SampleBound (μ W p.L) (fun a ω => loopTr (flowG W ⟨p.g, p.E, p.L, u⟩ ω) a σ)
            (fun a => weightFn cw θ F W (ellProp p.g p.L u) (wordDiam a)) S Cs
            ((W : ℝ) ^ (-D)) ((W : ℝ) ^ (-D')) ∧
          SampleBound (μ W p.L) (fun a ω => flowErr W ⟨p.g, p.E, p.L, u⟩ a σ ω)
            (fun a => weightFn cw θ F W (ellProp p.g p.L u) (wordDiam a)) S Cs
            ((W : ℝ) ^ (-D)) ((W : ℝ) ^ (-D'))) ∧
  (∀ D D' : ℝ, 0 < D → 0 < D' → ∃ CS Cs : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ x,
    SegAdm base J W x → ∃ (S₁ : Finset (Fin x.1.L × Fin x.1.L))
      (S₂ : Finset ((Fin x.1.L × Fin W) × (Fin x.1.L × Fin W))),
      (S₁.card : ℝ) ≤ (W : ℝ) ^ CS ∧ (S₂.card : ℝ) ≤ (W : ℝ) ^ CS ∧
      SampleBound (μ W x.1.L) (fun ab ω => blockTr (segG W x ω - segM W x) ab.1 ab.2)
        (fun _ => 1) S₁ Cs ((W : ℝ) ^ (-D)) ((W : ℝ) ^ (-D')) ∧
      SampleBound (μ W x.1.L) (fun e ω => segG W x ω e.1 e.2 -
          if e.1.2 = e.2.2 then blockTr (segG W x ω) e.1.1 e.2.1 else 0)
        (fun _ => 1) S₂ Cs ((W : ℝ) ^ (-D)) ((W : ℝ) ^ (-D')) ∧
      SampleBound (μ W x.1.L) (fun ab ω => segRes W x ω ab.1 ab.2)
        (fun _ => 1) S₁ Cs ((W : ℝ) ^ (-D)) ((W : ℝ) ^ (-D')))

/-- The weighted sampling (5.34) [fo:eq:weighted-sampling-input] of the mixed two-loop error at time
`u` with the terminal weight `w_v`, `1/2 ≤ u ≤ v ≤ t`, the constant `C_w` fixed before `c_p, θ, F`,
and one sample set of at most `W^{C_S}` pairs for all `u, v`. -/
def SwInput (base : ℕ → Set FlowPt) (J : ℕ) (Cw : ℝ) : Prop :=
  ∀ cp θ F D D' : ℝ, 0 < cp → cp ≤ 1 → 0 < θ → θ ≤ 1 / 2 → 0 < F → 0 < D → 0 < D' →
    ∃ CS : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ d p, d ≤ J → CmpReach base W d p →
      ∃ S : Finset (Fin p.L × Fin p.L), (S.card : ℝ) ≤ (W : ℝ) ^ CS ∧
        ∀ u v : ℝ, 1 / 2 ≤ u → u ≤ v → v ≤ p.u →
          SampleBound (μ W p.L)
            (fun ab ω => flowErr W ⟨p.g, p.E, p.L, u⟩ ![ab.1, ab.2] ![true, false] ω)
            (fun ab => weightFn cp θ F W (ellProp p.g p.L v) (cycDist ab.1 ab.2)) S Cw
            ((W : ℝ) ^ (-D)) ((W : ℝ) ^ (-D'))

/-- The analytic inputs of the general Theorem 5.12 [gc:thm:common] on the
points reached from `base` with depth at most `J`: the explicit constant of the weighted sampling,
the crude moments, Lemma 5.9 [gc:lem:residual], Lemma 5.10(b) [fo:lem:sampling-continuity] with
Lemma 5.8 [uvc:thm:ordinary-sampling], and the weighted sampling (5.34)
[fo:eq:weighted-sampling-input]. -/
structure PropInputs (base : ℕ → Set FlowPt) (J : ℕ) where
  Cw : ℝ
  one_le_Cw : 1 ≤ Cw
  crude : CrudeInput base J
  averaging : AveragingInput base J
  sampling : SamplingInput base J
  sw : SwInput base J Cw

/-- `c_* = (1 + √(1 + 4e²/(1 - ε_c)²)) · 2(1 + δ) C_w` at `ε_c = δ = 1/100`. -/
def cstarN (Cw : ℝ) : ℝ :=
  (1 + Real.sqrt (1 + 4 * Real.exp 2 / (1 - 1 / 100) ^ 2)) * (2 * (1 + 1 / 100) * Cw)

/-- The barrier exponent `M = c_*/2 + 4` of the barrier `J₀ = W^ε R^M`. -/
def lemmaNM (Cw : ℝ) : ℝ := cstarN Cw / 2 + 4

/-- `N₀(C_w) = max{20, 3c_*/2 + 7}` in the strengthened form `R^N ζ_t ≤ W^{-c}` of (5.38)
[gc:eq:one-step]. -/
def lemmaNN0 (Cw : ℝ) : ℝ := max 20 (3 * cstarN Cw / 2 + 7)

end LSBA
