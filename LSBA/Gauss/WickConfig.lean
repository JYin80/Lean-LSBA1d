import LSBA.Transfer.ObsPoly
import LSBA.Gauss.Wick
import LSBA.Gauss.GUENormMoment

/-!
# Wick contraction of trace and marked-form configurations

Words in `C`, `C⁻¹` and one GUE block `V`; configurations, i.e. polynomials in normalized traces
`W⁻¹ Tr(word)` and marked forms `v* word v`; and their formal Gaussian expectation `cfgWick` with
values in polynomials in `m_k`, `f_k`, `W⁻¹`, `g⁻²`, computed by pairing the first `V` of a
configuration with every other `V` (rule `𝔼 V_ab V_cd = W⁻¹ δ_ad δ_bc` of (1.2) [eq:covariance]):
inside one trace or form the pair splits off `W⁻¹ Tr` of the enclosed word; across two factors it
joins them with a factor `W⁻²` (a trace involved) or `W⁻¹` (two marked forms). This is the
contraction calculus of the proof of Lemma 11.7 [lg:lem:ideal].
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- Letters of matrix words: `C`, `C⁻¹`, `V`. -/
inductive WLetter
  | c
  | cInv
  | v
  deriving DecidableEq

/-- Noncommutative polynomials in `C`, `C⁻¹`, `V`. -/
abbrev WordAlg : Type := FreeAlgebra ℂ WLetter

/-- The matrix value of a word at `(C, V)`. -/
def wordMat {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) : WordAlg →ₐ[ℂ] Matrix (Fin W) (Fin W) ℂ :=
  FreeAlgebra.lift ℂ fun l => match l with
    | .c => C
    | .cInv => C⁻¹
    | .v => V

/-- The word with the given letters. -/
def wordOf (u : List WLetter) : WordAlg := (u.map (FreeAlgebra.ι ℂ)).prod

/-- Factors of a configuration: a normalized trace `W⁻¹ Tr(u)`, a marked form `v* u v`, `W⁻¹`,
`g⁻²`. -/
inductive CfgVar
  | trc (u : List WLetter)
  | mrk (u : List WLetter)
  | w
  | γ
  deriving DecidableEq

/-- Configurations: polynomials in traces and marked forms of words. -/
abbrev CfgPoly : Type := MvPolynomial CfgVar ℂ

/-- The value of a configuration at a state `(C, v)` and a block `V`. -/
def cfgEval (g : ℝ) {W : ℕ} (X : State W) (V : Matrix (Fin W) (Fin W) ℂ) : CfgPoly →ₐ[ℂ] ℂ :=
  aeval fun x => match x with
    | .trc u => (W : ℂ)⁻¹ * (wordMat X.1 V (wordOf u)).trace
    | .mrk u => vecForm (wordMat X.1 V (wordOf u)) X.2
    | .w => (W : ℂ)⁻¹
    | .γ => (((g ^ 2)⁻¹ : ℝ) : ℂ)

/-- The word of a trace or marked factor. -/
def CfgVar.word : CfgVar → List WLetter
  | .trc u => u
  | .mrk u => u
  | _ => []

/-- Whether a factor is a marked form. -/
def CfgVar.isMrk : CfgVar → Bool
  | .mrk _ => true
  | _ => false

/-- The number of `V` letters in a factor. -/
def CfgVar.vc (x : CfgVar) : ℕ := x.word.count .v

/-- The exponent `#C − #C⁻¹` of a word. -/
def wordExp (u : List WLetter) : ℤ := (u.count .c : ℤ) - u.count .cInv

/-- A factor without `V` as a polynomial in the observables: `m_{exp}`, `f_{exp}`, `w`, `γ`. -/
def CfgVar.base : CfgVar → ObsPoly
  | .trc u => mVar (wordExp u)
  | .mrk u => fVar (wordExp u)
  | .w => X .w
  | .γ => X .γ

/-- A code of a letter. -/
def WLetter.code : WLetter → ℕ
  | .c => 0
  | .cInv => 1
  | .v => 2

/-- An injective key of a factor, which chooses the pivot factor. -/
def CfgVar.key : CfgVar → List ℕ
  | .trc u => 0 :: u.map WLetter.code
  | .mrk u => 1 :: u.map WLetter.code
  | .w => [2]
  | .γ => [3]

/-- The pivot of a monomial: the factor containing `V` with the least key. -/
def cfgPick (d : CfgVar →₀ ℕ) : CfgVar :=
  if h : (d.support.filter fun x => 0 < x.vc).Nonempty then
    Classical.choose ((d.support.filter fun x => 0 < x.vc).exists_min_image CfgVar.key h)
  else .w

/-- The positions of the letters `V` in a word. -/
def vPos (u : List WLetter) : List ℕ :=
  (List.range u.length).filter fun j => u[j]? = some .v

/-- Pairing the first `V` of `φ = A V B` with the `V` at position `j` of `B = B₁ V B₂`:
`W⁻¹ Tr(B₁)` times the factor of `A B₂` of the same kind. -/
def selfPair (φ : CfgVar) (j : ℕ) : CfgVar →₀ ℕ :=
  Finsupp.single (.trc ((φ.word.drop (φ.word.idxOf .v + 1)).take j)) 1 +
    Finsupp.single (if φ.isMrk then
        .mrk (φ.word.take (φ.word.idxOf .v) ++ (φ.word.drop (φ.word.idxOf .v + 1)).drop (j + 1))
      else
        .trc (φ.word.take (φ.word.idxOf .v) ++ (φ.word.drop (φ.word.idxOf .v + 1)).drop (j + 1)))
      1

/-- Pairing the first `V` of `φ = A V B` with the `V` at position `j` of another factor
`ψ = C V D`: the power of `W⁻¹` and the joined factors (`Tr(BADC)`, `v*ADCBv`, `v*CBADv`, or
`(v*ADv)(v*CBv)`). -/
def crossPair (φ ψ : CfgVar) (j : ℕ) : ℕ × (CfgVar →₀ ℕ) :=
  let A := φ.word.take (φ.word.idxOf .v)
  let B := φ.word.drop (φ.word.idxOf .v + 1)
  let C' := ψ.word.take j
  let D := ψ.word.drop (j + 1)
  match φ.isMrk, ψ.isMrk with
  | false, false => (2, Finsupp.single (.trc (B ++ A ++ D ++ C')) 1)
  | true, false => (2, Finsupp.single (.mrk (A ++ D ++ C' ++ B)) 1)
  | false, true => (2, Finsupp.single (.mrk (C' ++ B ++ A ++ D)) 1)
  | true, true => (1, Finsupp.single (.mrk (A ++ D)) 1 + Finsupp.single (.mrk (C' ++ B)) 1)

/-- The Wick expansion of a monomial, with fuel `n` (one pair per step). -/
def cfgWickAux : ℕ → (CfgVar →₀ ℕ) → ObsPoly
  | 0, d => d.prod fun x k => x.base ^ k
  | n + 1, d =>
    if (d.support.filter fun x => 0 < x.vc).Nonempty then
      ((vPos ((cfgPick d).word.drop ((cfgPick d).word.idxOf .v + 1))).map fun j =>
          cfgWickAux n (d - Finsupp.single (cfgPick d) 1 + selfPair (cfgPick d) j)).sum +
        ∑ ψ ∈ (d - Finsupp.single (cfgPick d) 1).support,
          ((vPos ψ.word).map fun j =>
            (((d - Finsupp.single (cfgPick d) 1 : CfgVar →₀ ℕ) ψ : ℕ) : ℂ) •
              (X ObsVar.w ^ (crossPair (cfgPick d) ψ j).1 *
                cfgWickAux n (d - Finsupp.single (cfgPick d) 1 - Finsupp.single ψ 1 +
                  (crossPair (cfgPick d) ψ j).2))).sum
    else d.prod fun x k => x.base ^ k

/-- The formal Gaussian expectation of a configuration (fuel = number of `V` letters). -/
def cfgWick (c : CfgPoly) : ObsPoly :=
  ∑ d ∈ c.support, c.coeff d • cfgWickAux (Finsupp.weight CfgVar.vc d) d

/-! ### Polynomials in the entries of one block -/

/-- Polynomials in the entries `V_ab` of a `W × W` matrix. -/
private abbrev EntPoly (W : ℕ) : Type := MvPolynomial (Fin W × Fin W) ℂ

/-- The matrix of entry variables. -/
private def entMat (W : ℕ) : Matrix (Fin W) (Fin W) (EntPoly W) :=
  Matrix.of fun a b => X (a, b)

/-- A constant matrix. -/
private def cstMat {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin W) (Fin W) (EntPoly W) :=
  A.map (algebraMap ℂ (EntPoly W))

/-- Words as matrices of entry polynomials. -/
private def wordP {W : ℕ} (C : Matrix (Fin W) (Fin W) ℂ) :
    WordAlg →ₐ[ℂ] Matrix (Fin W) (Fin W) (EntPoly W) :=
  FreeAlgebra.lift ℂ fun l => match l with
    | .c => cstMat C
    | .cInv => cstMat C⁻¹
    | .v => entMat W

/-- Evaluation of entry polynomials at a matrix. -/
private def entEval {W : ℕ} (V : Matrix (Fin W) (Fin W) ℂ) : EntPoly W →ₐ[ℂ] ℂ :=
  aeval fun ab => V ab.1 ab.2

private theorem mapMatrix_entEval_wordP {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) (x : WordAlg) :
    (wordP C x).map (entEval V) = wordMat C V x := by
  have h : (entEval V).mapMatrix.comp (wordP C) = wordMat C V := by
    apply FreeAlgebra.hom_ext
    funext l
    cases l <;> ext i j <;> simp [wordP, wordMat, cstMat, entMat, entEval]
  exact AlgHom.congr_fun h x

private theorem entEval_trace {W : ℕ} (V : Matrix (Fin W) (Fin W) ℂ)
    (M : Matrix (Fin W) (Fin W) (EntPoly W)) :
    entEval V M.trace = (M.map (entEval V)).trace := by
  simp [Matrix.trace, map_sum]

/-- The rank-one matrix `v v*`. -/
private def prj {W : ℕ} (v : EuclideanSpace ℂ (Fin W)) : Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun i j => v i * star (v j)

private theorem vecForm_eq_trace {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W)) : vecForm A v = (A * prj v).trace := by
  simp only [vecForm, Matrix.trace, Matrix.mul_apply, prj, Matrix.of_apply, Matrix.diag_apply]
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, RCLike.inner_apply,
    WithLp.ofLp_toLp, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.star_def]
  ring

/-- The polynomial in the entries of the value of a configuration. -/
private def cfgP (g : ℝ) {W : ℕ} (Z : State W) : CfgPoly →ₐ[ℂ] EntPoly W :=
  aeval fun x => match x with
    | .trc u => (W : ℂ)⁻¹ • (wordP Z.1 (wordOf u)).trace
    | .mrk u => (wordP Z.1 (wordOf u) * cstMat (prj Z.2)).trace
    | .w => algebraMap ℂ _ (W : ℂ)⁻¹
    | .γ => algebraMap ℂ _ (((g ^ 2)⁻¹ : ℝ) : ℂ)

private theorem entEval_cfgP (g : ℝ) {W : ℕ} (Z : State W) (V : Matrix (Fin W) (Fin W) ℂ)
    (c : CfgPoly) : entEval V (cfgP g Z c) = cfgEval g Z V c := by
  have h : (entEval V).comp (cfgP g Z) = cfgEval g Z V := by
    apply MvPolynomial.algHom_ext
    intro x
    cases x with
    | trc u => simp [cfgP, cfgEval, entEval_trace, mapMatrix_entEval_wordP]
    | mrk u =>
      simp only [AlgHom.comp_apply, cfgP, cfgEval, aeval_X, entEval_trace, vecForm_eq_trace]
      rw [← AlgHom.mapMatrix_apply, map_mul, AlgHom.mapMatrix_apply, AlgHom.mapMatrix_apply,
        mapMatrix_entEval_wordP]
      congr 2
      ext i j
      simp [cstMat, entEval]
    | w => simp [cfgP, cfgEval]
    | γ => simp [cfgP, cfgEval]
  exact AlgHom.congr_fun h c

/-! ### Gaussian expectation of entry polynomials -/

private theorem measurable_gueBlock_zero (W : ℕ) :
    Measurable fun ω : Ω W 1 => gueBlock W 1 ω 0 := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

private theorem norm_entry_le_l2 {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) (a b : Fin W) :
    ‖A a b‖ ≤ ‖A‖ := by
  have h := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single b 1)
  rw [PiLp.norm_single, norm_one, mul_one] at h
  refine le_trans (le_of_eq ?_) ((PiLp.norm_apply_le _ a).trans h)
  simp

private theorem integrable_entEval (W : ℕ) (p : EntPoly W) :
    Integrable (fun ω => entEval (gueBlock W 1 ω 0) p) (μ W 1) := by
  induction p using MvPolynomial.induction_on' with
  | monomial m a =>
    have hform : ∀ V : Matrix (Fin W) (Fin W) ℂ, entEval V (monomial m a) =
        a * ∏ ab ∈ m.support, V ab.1 ab.2 ^ m ab := by
      intro V
      simp [entEval, aeval_monomial, Finsupp.prod]
    simp only [hform]
    refine Integrable.mono' ((integrable_norm_gueBlock_pow W (∑ ab ∈ m.support, m ab)).const_mul
      ‖a‖) ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · refine Measurable.aestronglyMeasurable (Measurable.const_mul ?_ a)
      refine Finset.measurable_prod _ fun ab _ => Measurable.pow_const ?_ _
      exact (measurable_pi_iff.mp (measurable_pi_iff.mp (measurable_gueBlock_zero W) ab.1)) ab.2
    · rw [norm_mul, ← Finset.prod_pow_eq_pow_sum]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg a)
      refine (Finset.norm_prod_le _ _).trans (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        fun ab _ => ?_)
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_entry_le_l2 _ _ _) _
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq

/-- The Gaussian expectation of an entry polynomial at one GUE block. -/
private def gexp (W : ℕ) : EntPoly W →ₗ[ℂ] ℂ where
  toFun p := ∫ ω, entEval (gueBlock W 1 ω 0) p ∂(μ W 1)
  map_add' p q := by
    simp only [map_add]
    exact integral_add (integrable_entEval W p) (integrable_entEval W q)
  map_smul' a p := by
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    exact integral_const_mul a _

private theorem gexp_apply (W : ℕ) (p : EntPoly W) :
    gexp W p = ∫ ω, entEval (gueBlock W 1 ω 0) p ∂(μ W 1) := rfl

/-- The Leibniz rule over a finite product. -/
private theorem derivation_prod {W : ℕ} (D : Derivation ℂ (EntPoly W) (EntPoly W)) {ι : Type*}
    (s : Finset ι) (f : ι → EntPoly W) :
    D (∏ i ∈ s, f i) = ∑ j ∈ s, (∏ i ∈ s.erase j, f i) * D (f j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha,
      Finset.erase_insert ha]
    simp only [smul_eq_mul, Finset.mul_sum]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hja : a ≠ j := fun h => ha (h ▸ hj)
    rw [Finset.erase_insert_of_ne hja,
      Finset.prod_insert fun h => ha (Finset.mem_of_mem_erase h)]
    ring

/-- Gaussian integration by parts for a product of entries: `𝔼[V_bc p] = W⁻¹ 𝔼[∂p/∂V_cb]`. -/
private theorem gexp_X_mul_prod (W : ℕ) {ι : Type*} (s : Finset ι) (ab : ι → Fin W × Fin W)
    (b c : Fin W) :
    gexp W (X (b, c) * ∏ i ∈ s, X (ab i)) =
      (W : ℂ)⁻¹ * gexp W (pderiv (c, b) (∏ i ∈ s, X (ab i))) := by
  have hl : ∀ (V : Matrix (Fin W) (Fin W) ℂ) (a a' : Fin W),
      star (Pi.single a (1 : ℂ) : Fin W → ℂ) ⬝ᵥ (V *ᵥ Pi.single a' 1) = V a a' := by
    intro V a a'
    simp [Matrix.mulVec_single]
  have key := integral_gueLin_mul_prod W s (fun i => Pi.single (ab i).1 (1 : ℂ))
    (fun i => Pi.single (ab i).2 (1 : ℂ)) (Pi.single b 1) (Pi.single c 1)
  simp only [hl] at key
  rw [derivation_prod, map_sum, Finset.mul_sum]
  simp only [gexp_apply, map_mul, map_prod, entEval, aeval_X]
  rw [key]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pderiv_X]
  by_cases h : ab j = (c, b)
  · simp [h]
  · have h' : ¬ (b = (ab j).2 ∧ (ab j).1 = c) := fun h' => h (Prod.ext h'.2 h'.1.symm)
    rw [Pi.single_eq_of_ne h]
    simp only [map_zero, mul_zero, integral_zero]
    by_cases hb : b = (ab j).2
    · have hc : (ab j).1 ≠ c := fun hc => h' ⟨hb, hc⟩
      simp [Pi.single_apply, hc]
    · simp [Pi.single_apply, hb]

/-- Gaussian integration by parts for entry polynomials: `𝔼[V_bc p] = W⁻¹ 𝔼[∂p/∂V_cb]`
((1.2) [eq:covariance]). -/
private theorem gexp_X_mul (W : ℕ) (b c : Fin W) (p : EntPoly W) :
    gexp W (X (b, c) * p) = (W : ℂ)⁻¹ * gexp W (pderiv (c, b) p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial m a =>
    have hm : (monomial m a : EntPoly W) =
        a • ∏ i ∈ m.support.sigma (fun ab => Finset.range (m ab)), X i.1 := by
      rw [monomial_eq, Finset.prod_sigma, ← C_mul']
      simp [Finsupp.prod]
    rw [hm, mul_smul_comm, map_smul, Derivation.map_smul, map_smul, gexp_X_mul_prod,
      smul_eq_mul, smul_eq_mul]
    ring
  | add p q hp hq =>
    rw [mul_add, map_add, hp, hq, map_add, map_add]
    ring

/-! ### Derivatives of words -/

private theorem map_derivation_mul {W : ℕ} (D : Derivation ℂ (EntPoly W) (EntPoly W))
    (M N : Matrix (Fin W) (Fin W) (EntPoly W)) :
    (M * N).map D = M.map D * N + M * N.map D := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum, Derivation.leibniz,
    smul_eq_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

private theorem map_derivation_cstMat {W : ℕ} (D : Derivation ℂ (EntPoly W) (EntPoly W))
    (A : Matrix (Fin W) (Fin W) ℂ) : (cstMat A).map D = 0 := by
  ext i j
  simp [cstMat]

private theorem map_derivation_one {W : ℕ} (D : Derivation ℂ (EntPoly W) (EntPoly W)) :
    (1 : Matrix (Fin W) (Fin W) (EntPoly W)).map D = 0 := by
  ext i j
  by_cases h : i = j <;> simp [h, Derivation.map_one_eq_zero]

private theorem vPos_nil : vPos [] = [] := rfl

private theorem vPos_cons (l : WLetter) (u : List WLetter) :
    vPos (l :: u) = (if l = .v then [0] else []) ++ (vPos u).map (· + 1) := by
  simp only [vPos, List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map]
  by_cases h : l = .v <;> simp [h, Function.comp_def]

private theorem wordOf_cons (l : WLetter) (u : List WLetter) :
    wordOf (l :: u) = FreeAlgebra.ι ℂ l * wordOf u := by
  simp [wordOf]

private theorem wordOf_append (u u' : List WLetter) : wordOf (u ++ u') = wordOf u * wordOf u' := by
  simp [wordOf]

/-- Derivative of a word: the sum over its letters `V` of the word with that `V` replaced. -/
private theorem map_derivation_wordP {W : ℕ} (C : Matrix (Fin W) (Fin W) ℂ)
    (D : Derivation ℂ (EntPoly W) (EntPoly W)) (u : List WLetter) :
    (wordP C (wordOf u)).map D = ((vPos u).map fun j =>
      wordP C (wordOf (u.take j)) * (entMat W).map D * wordP C (wordOf (u.drop (j + 1)))).sum := by
  induction u with
  | nil => simp [wordOf, vPos_nil, map_derivation_one]
  | cons l u ih =>
    rw [wordOf_cons, map_mul, map_derivation_mul, ih, vPos_cons, List.map_append,
      List.sum_append, List.map_map]
    have hr : ((vPos u).map ((fun j => wordP C (wordOf ((l :: u).take j)) * (entMat W).map D *
        wordP C (wordOf ((l :: u).drop (j + 1)))) ∘ (· + 1))).sum =
        wordP C (FreeAlgebra.ι ℂ l) * ((vPos u).map fun j => wordP C (wordOf (u.take j)) *
          (entMat W).map D * wordP C (wordOf (u.drop (j + 1)))).sum := by
      rw [← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun j _ => ?_
      simp only [Function.comp_apply, List.take_succ_cons, List.drop_succ_cons, wordOf_cons,
        map_mul, Matrix.mul_assoc]
    rw [hr]
    cases l with
    | c => simp [wordP, map_derivation_cstMat]
    | cInv => simp [wordP, map_derivation_cstMat]
    | v => simp [wordP, wordOf]

/-- A word without `V` has derivative `0`. -/
private theorem vPos_eq_nil {u : List WLetter} (h : WLetter.v ∉ u) : vPos u = [] := by
  simp only [vPos, List.filter_eq_nil_iff, List.mem_range, decide_eq_true_eq]
  intro j hj hv
  exact h (List.mem_of_getElem? hv)

private theorem mem_vPos {u : List WLetter} {j : ℕ} (hj : j ∈ vPos u) : u[j]? = some .v := by
  simpa [vPos] using (List.mem_filter.mp hj).2

/-- The derivation `Σ_ab Y_ab ∂/∂V_ab` in the direction of a matrix `Y`. -/
private def dirD {W : ℕ} (Y : Matrix (Fin W) (Fin W) (EntPoly W)) :
    Derivation ℂ (EntPoly W) (EntPoly W) :=
  ∑ ab : Fin W × Fin W, Y ab.1 ab.2 • pderiv ab

private theorem dirD_apply {W : ℕ} (Y : Matrix (Fin W) (Fin W) (EntPoly W)) (p : EntPoly W) :
    dirD Y p = ∑ ab : Fin W × Fin W, Y ab.1 ab.2 * pderiv ab p := by
  rw [dirD, ← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  simp [Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply]

private theorem entMat_map_dirD {W : ℕ} (Y : Matrix (Fin W) (Fin W) (EntPoly W)) :
    (entMat W).map (dirD Y) = Y := by
  ext i j
  simp [dirD_apply, entMat, pderiv_X, Pi.single_apply]

private theorem mul_entMat_pderiv_mul_apply {W : ℕ} (M N : Matrix (Fin W) (Fin W) (EntPoly W))
    (b c i j : Fin W) :
    (M * (entMat W).map (pderiv (c, b)) * N) i j = M i c * N b j := by
  simp [Matrix.mul_apply, entMat, pderiv_X, Pi.single_apply, ite_and]

/-- `Π M Π = Tr(MΠ) Π` for the rank-one `Π = v v*`. -/
private theorem prj_mul_prj {W : ℕ} (v : EuclideanSpace ℂ (Fin W))
    (M : Matrix (Fin W) (Fin W) (EntPoly W)) :
    cstMat (prj v) * M * cstMat (prj v) = (M * cstMat (prj v)).trace • cstMat (prj v) := by
  refine Matrix.ext fun i l => ?_
  simp only [Matrix.mul_apply, cstMat, prj, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
    Matrix.trace, Matrix.diag_apply, smul_eq_mul, Finset.sum_mul, map_mul]
  exact Finset.sum_comm.trans
    (Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring)

/-! ### Factors as traces -/

/-- The scalar of a factor: `1` for a marked form, `W⁻¹` otherwise. -/
private def cfgKap (W : ℕ) (x : CfgVar) : ℂ := if x.isMrk then 1 else (W : ℂ)⁻¹

/-- The matrix closing a factor: `v v*` for a marked form, `1` otherwise. -/
private def cfgPrj {W : ℕ} (Z : State W) (x : CfgVar) : Matrix (Fin W) (Fin W) (EntPoly W) :=
  if x.isMrk then cstMat (prj Z.2) else 1

private theorem map_derivation_cfgPrj {W : ℕ} (D : Derivation ℂ (EntPoly W) (EntPoly W))
    (Z : State W) (x : CfgVar) : (cfgPrj Z x).map D = 0 := by
  unfold cfgPrj
  split_ifs
  exacts [map_derivation_cstMat D _, map_derivation_one D]

private theorem cfgP_X_of_vc (g : ℝ) {W : ℕ} (Z : State W) {x : CfgVar} (hx : 0 < x.vc) :
    cfgP g Z (X x) = cfgKap W x • (wordP Z.1 (wordOf x.word) * cfgPrj Z x).trace := by
  cases x with
  | trc u => simp [cfgP, cfgKap, cfgPrj, CfgVar.isMrk, CfgVar.word]
  | mrk u => simp [cfgP, cfgKap, cfgPrj, CfgVar.isMrk, CfgVar.word]
  | w => simp [CfgVar.vc, CfgVar.word] at hx
  | γ => simp [CfgVar.vc, CfgVar.word] at hx

private theorem cfgP_X_ite (g : ℝ) {W : ℕ} (Z : State W) (φ : CfgVar) (u : List WLetter) :
    cfgP g Z (X (if φ.isMrk then .mrk u else .trc u)) =
      cfgKap W φ • (wordP Z.1 (wordOf u) * cfgPrj Z φ).trace := by
  unfold cfgKap cfgPrj
  split_ifs <;> simp [cfgP]

private theorem derivation_trace {W : ℕ} (D : Derivation ℂ (EntPoly W) (EntPoly W))
    (M : Matrix (Fin W) (Fin W) (EntPoly W)) : D M.trace = (M.map D).trace := by
  simp [Matrix.trace, map_sum]

/-- The derivative of a factor in the direction `Y`. -/
private theorem dirD_cfgP_X (g : ℝ) {W : ℕ} (Z : State W)
    (Y : Matrix (Fin W) (Fin W) (EntPoly W)) (ψ : CfgVar) :
    dirD Y (cfgP g Z (X ψ)) = cfgKap W ψ • (((vPos ψ.word).map fun j =>
      wordP Z.1 (wordOf (ψ.word.take j)) * Y * wordP Z.1 (wordOf (ψ.word.drop (j + 1)))).sum *
        cfgPrj Z ψ).trace := by
  cases ψ with
  | trc u =>
    simp only [cfgP, aeval_X, Derivation.map_smul, derivation_trace, map_derivation_wordP,
      entMat_map_dirD, cfgKap, cfgPrj, CfgVar.isMrk, CfgVar.word]
    simp
  | mrk u =>
    simp only [cfgP, aeval_X, derivation_trace, map_derivation_mul, map_derivation_wordP,
      entMat_map_dirD, map_derivation_cstMat, cfgKap, cfgPrj, CfgVar.isMrk, CfgVar.word,
      Matrix.mul_zero, add_zero]
    simp
  | w => simp [cfgP, CfgVar.word, vPos_nil]
  | γ => simp [cfgP, CfgVar.word, vPos_nil]

/-! ### Letters `V` in words -/

private theorem count_split {u : List WLetter} {j : ℕ} (h : u[j]? = some .v) :
    u.count .v = (u.take j).count .v + 1 + (u.drop (j + 1)).count .v := by
  obtain ⟨hj, hu⟩ := List.getElem?_eq_some_iff.mp h
  conv_lhs => rw [← List.take_append_drop j u, List.drop_eq_getElem_cons hj, hu]
  simp [List.count_append]
  omega

private theorem idxOf_v {u : List WLetter} (h : WLetter.v ∈ u) :
    u[u.idxOf .v]? = some .v := by
  have hl := List.idxOf_lt_length_iff.mpr h
  rw [List.getElem?_eq_getElem hl, List.getElem_idxOf hl]

private theorem word_split {u : List WLetter} (h : WLetter.v ∈ u) :
    u = u.take (u.idxOf .v) ++ .v :: u.drop (u.idxOf .v + 1) := by
  have hl := List.idxOf_lt_length_iff.mpr h
  conv_lhs => rw [← List.take_append_drop (u.idxOf .v) u, List.drop_eq_getElem_cons hl,
    List.getElem_idxOf hl]

private theorem not_mem_take_idxOf (u : List WLetter) : WLetter.v ∉ u.take (u.idxOf .v) := by
  induction u with
  | nil => simp
  | cons a u ih =>
    by_cases h : a = .v
    · simp [h]
    · rw [List.idxOf_cons]
      have : (a == WLetter.v) = false := by simpa using h
      simp [this, ih, Ne.symm h]

/-- The Leibniz rule for a monomial composed with an algebra map. -/
private theorem derivation_monomial {W : ℕ} (D : Derivation ℂ (EntPoly W) (EntPoly W))
    (f : CfgPoly →ₐ[ℂ] EntPoly W) (e : CfgVar →₀ ℕ) :
    D (f (monomial e 1)) = ∑ ψ ∈ e.support,
      (e ψ : ℂ) • (f (monomial (e - Finsupp.single ψ 1) 1) * D (f (X ψ))) := by
  induction e using Finsupp.induction with
  | zero => simp [Derivation.map_one_eq_zero]
  | single_add a b g ha hb ih =>
    have hga : g a = 0 := Finsupp.notMem_support_iff.mp ha
    have e1 : Finsupp.single a b + g - Finsupp.single a 1 = Finsupp.single a (b - 1) + g := by
      ext x
      by_cases hx : x = a
      · subst hx; simp [hga]
      · simp [Ne.symm hx]
    have e2 : ∀ ψ ∈ g.support, Finsupp.single a b + g - Finsupp.single ψ 1 =
        Finsupp.single a b + (g - Finsupp.single ψ 1) := by
      intro ψ hψ
      have hψa : ψ ≠ a := fun h => ha (h ▸ hψ)
      ext x
      by_cases hx : x = ψ
      · subst hx; simp [Ne.symm hψa]
      · simp [Finsupp.single_apply, Ne.symm hx]
    rw [monomial_single_add, map_mul, map_pow, Derivation.leibniz, Derivation.leibniz_pow, ih,
      Finsupp.support_single_add ha hb, Finset.sum_cons, e1, monomial_single_add]
    have e3 : ∀ ψ ∈ g.support, ((Finsupp.single a b + g) ψ : ℂ) •
        (f (monomial (Finsupp.single a b + g - Finsupp.single ψ 1) 1) * D (f (X ψ))) =
        f (X a) ^ b * ((g ψ : ℂ) • (f (monomial (g - Finsupp.single ψ 1) 1) * D (f (X ψ)))) := by
      intro ψ hψ
      have hψa : ψ ≠ a := fun h => ha (h ▸ hψ)
      rw [e2 ψ hψ, monomial_single_add, map_mul, map_pow]
      simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hψa, zero_add,
        Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
      ring
    rw [Finset.sum_congr rfl e3, ← Finset.mul_sum]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, hga, add_zero, smul_eq_mul, map_mul,
      map_pow, nsmul_eq_mul, Nat.cast_smul_eq_nsmul]
    ring

/-! ### One contraction -/

private theorem trace_entMat_mul {W : ℕ} (M : Matrix (Fin W) (Fin W) (EntPoly W)) :
    (entMat W * M).trace = ∑ bc : Fin W × Fin W, X bc * M bc.2 bc.1 := by
  simp [Matrix.trace, Matrix.mul_apply, entMat, Fintype.sum_prod_type]

private theorem list_sum_matrix_apply {W : ℕ} (L : List ℕ)
    (F : ℕ → Matrix (Fin W) (Fin W) (EntPoly W)) (i j : Fin W) :
    (L.map F).sum i j = (L.map fun x => F x i j).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

private theorem finset_sum_list_sum {M : Type*} [AddCommMonoid M] {ι : Type*} (s : Finset ι)
    (L : List ℕ) (F : ι → ℕ → M) :
    ∑ x ∈ s, (L.map (F x)).sum = (L.map fun j => ∑ x ∈ s, F x j).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [Finset.sum_add_distrib, ih]

/-- Integration by parts against the first `V` of a factor `φ = A V B`: the self-contractions
with the `V`s of `B` and the derivative of the rest in the direction `B Π A`. -/
private theorem gexp_cfgP_X_mul (g : ℝ) {W : ℕ} (Z : State W) {φ : CfgVar} (hφ : 0 < φ.vc)
    (Q : EntPoly W) :
    gexp W (cfgP g Z (X φ) * Q) = (W : ℂ)⁻¹ * cfgKap W φ *
      (((vPos (φ.word.drop (φ.word.idxOf .v + 1))).map fun j =>
        gexp W ((wordP Z.1 (wordOf ((φ.word.drop (φ.word.idxOf .v + 1)).take j))).trace *
          (wordP Z.1 (wordOf ((φ.word.drop (φ.word.idxOf .v + 1)).drop (j + 1))) * cfgPrj Z φ *
            wordP Z.1 (wordOf (φ.word.take (φ.word.idxOf .v)))).trace * Q)).sum +
        gexp W (dirD (wordP Z.1 (wordOf (φ.word.drop (φ.word.idxOf .v + 1))) * cfgPrj Z φ *
          wordP Z.1 (wordOf (φ.word.take (φ.word.idxOf .v)))) Q)) := by
  have hv : WLetter.v ∈ φ.word := List.count_pos_iff.mp hφ
  have hsplit := word_split hv
  set A := φ.word.take (φ.word.idxOf .v) with hAdef
  set B := φ.word.drop (φ.word.idxOf .v + 1) with hBdef
  set Y := wordP Z.1 (wordOf B) * cfgPrj Z φ * wordP Z.1 (wordOf A) with hY
  have hA : ∀ D : Derivation ℂ (EntPoly W) (EntPoly W), (wordP Z.1 (wordOf A)).map D = 0 := by
    intro D
    rw [map_derivation_wordP, vPos_eq_nil (not_mem_take_idxOf _)]
    rfl
  have h1 : cfgP g Z (X φ) = cfgKap W φ • ∑ bc : Fin W × Fin W, X bc * Y bc.2 bc.1 := by
    rw [cfgP_X_of_vc g Z hφ, hsplit, wordOf_append, wordOf_cons, map_mul, map_mul,
      ← trace_entMat_mul]
    have hvv : wordP Z.1 (FreeAlgebra.ι ℂ WLetter.v) = entMat W := by simp [wordP]
    rw [hvv, hY]
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hYd : ∀ bc : Fin W × Fin W, pderiv (bc.2, bc.1) (Y bc.2 bc.1) =
      ((vPos B).map fun j => (wordP Z.1 (wordOf (B.take j))) bc.2 bc.2 *
        (wordP Z.1 (wordOf (B.drop (j + 1))) * cfgPrj Z φ * wordP Z.1 (wordOf A)) bc.1
          bc.1).sum := by
    intro bc
    rw [← Matrix.map_apply (f := pderiv (bc.2, bc.1)), hY, map_derivation_mul, map_derivation_mul,
      hA, map_derivation_cfgPrj, map_derivation_wordP]
    simp only [Matrix.mul_zero, add_zero, ← List.sum_map_mul_right, list_sum_matrix_apply]
    refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc, mul_entMat_pderiv_mul_apply]
  have hself : ∑ bc : Fin W × Fin W, pderiv (bc.2, bc.1) (Y bc.2 bc.1) =
      ((vPos B).map fun j => (wordP Z.1 (wordOf (B.take j))).trace *
        (wordP Z.1 (wordOf (B.drop (j + 1))) * cfgPrj Z φ * wordP Z.1 (wordOf A)).trace).sum := by
    simp only [hYd]
    rw [finset_sum_list_sum]
    refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
    rw [Fintype.sum_prod_type, Matrix.trace, Matrix.trace, Finset.sum_mul_sum, Finset.sum_comm]
    simp only [Matrix.diag_apply]
  have hcross : ∑ bc : Fin W × Fin W, Y bc.2 bc.1 * pderiv (bc.2, bc.1) Q = dirD Y Q := by
    rw [dirD_apply]
    exact Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun bc => rfl
  have h2 : ∀ bc : Fin W × Fin W, pderiv (bc.2, bc.1) (Y bc.2 bc.1 * Q) =
      Y bc.2 bc.1 * pderiv (bc.2, bc.1) Q + Q * pderiv (bc.2, bc.1) (Y bc.2 bc.1) := by
    intro bc
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have hX : ∀ (bc : Fin W × Fin W) (p : EntPoly W),
      gexp W (X bc * p) = (W : ℂ)⁻¹ * gexp W (pderiv (bc.2, bc.1) p) :=
    fun bc p => gexp_X_mul W bc.1 bc.2 p
  have hsum : ∀ bc : Fin W × Fin W, gexp W (X bc * Y bc.2 bc.1 * Q) =
      (W : ℂ)⁻¹ * (gexp W (Y bc.2 bc.1 * pderiv (bc.2, bc.1) Q) +
        gexp W (Q * pderiv (bc.2, bc.1) (Y bc.2 bc.1))) := fun bc => by
    rw [mul_assoc, hX, h2, map_add]
  rw [h1, smul_mul_assoc, map_smul, Finset.sum_mul, map_sum,
    Finset.sum_congr rfl fun bc _ => hsum bc, ← Finset.mul_sum, Finset.sum_add_distrib,
    ← map_sum, ← map_sum, hcross, ← Finset.mul_sum, hself, smul_eq_mul,
    ← List.sum_map_mul_left, map_list_sum, List.map_map]
  have h3 : (vPos B).map (gexp W ∘ fun j => Q * ((wordP Z.1 (wordOf (B.take j))).trace *
      (wordP Z.1 (wordOf (B.drop (j + 1))) * cfgPrj Z φ * wordP Z.1 (wordOf A)).trace)) =
      (vPos B).map fun j => gexp W ((wordP Z.1 (wordOf (B.take j))).trace *
        (wordP Z.1 (wordOf (B.drop (j + 1))) * cfgPrj Z φ * wordP Z.1 (wordOf A)).trace * Q) :=
    List.map_congr_left fun j _ => by rw [Function.comp_apply, mul_comm Q]
  rw [h3]
  ring

private theorem monomial_add_single (e : CfgVar →₀ ℕ) (x : CfgVar) :
    (monomial (e + Finsupp.single x 1) 1 : CfgPoly) = monomial e 1 * X x := by
  rw [add_comm, monomial_single_add, pow_one, mul_comm]

private theorem monomial_single_one (x : CfgVar) :
    (monomial (Finsupp.single x 1) 1 : CfgPoly) = X x := rfl

/-- The joined factor of `crossPair`: contracting the first `V` of `φ = A V B` with the `V` of
`ψ = C V D` at position `j`. -/
private theorem cross_identity (g : ℝ) {W : ℕ} (Z : State W) (φ ψ : CfgVar) (j : ℕ) :
    (cfgKap W φ * ((W : ℂ)⁻¹ * cfgKap W ψ)) •
      (wordP Z.1 (wordOf (ψ.word.take j)) *
        (wordP Z.1 (wordOf (φ.word.drop (φ.word.idxOf .v + 1))) * cfgPrj Z φ *
          wordP Z.1 (wordOf (φ.word.take (φ.word.idxOf .v)))) *
        wordP Z.1 (wordOf (ψ.word.drop (j + 1))) * cfgPrj Z ψ).trace =
    ((W : ℂ)⁻¹ ^ (crossPair φ ψ j).1) • cfgP g Z (monomial (crossPair φ ψ j).2 1) := by
  unfold crossPair cfgKap cfgPrj
  generalize φ.word.take (φ.word.idxOf .v) = A
  generalize φ.word.drop (φ.word.idxOf .v + 1) = B
  generalize ψ.word.take j = C'
  generalize ψ.word.drop (j + 1) = D
  cases φ.isMrk <;> cases ψ.isMrk <;>
    simp only [Bool.false_eq_true, ite_true, ite_false, monomial_single_one, cfgP, aeval_X,
      wordOf_append, map_mul, smul_smul, mul_one, one_mul, monomial_single_add,
      pow_one]
  all_goals
    generalize wordP Z.1 (wordOf A) = MA
    generalize wordP Z.1 (wordOf B) = MB
    generalize wordP Z.1 (wordOf C') = MC
    generalize wordP Z.1 (wordOf D) = MD
  · have ht : (MC * (MB * MA) * MD).trace = (MB * MA * MD * MC).trace := by
      simp only [Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm MC]
      simp only [Matrix.mul_assoc]
    rw [ht, show ((W : ℂ)⁻¹ * ((W : ℂ)⁻¹ * (W : ℂ)⁻¹)) = (W : ℂ)⁻¹ ^ 2 * (W : ℂ)⁻¹ by ring]
  · have ht : (MC * (MB * MA) * MD * cstMat (prj Z.2)).trace =
        (MC * MB * MA * MD * cstMat (prj Z.2)).trace := by
      simp only [Matrix.mul_assoc]
    rw [ht, ← pow_two]
  · have ht : (MC * (MB * cstMat (prj Z.2) * MA) * MD).trace =
        (MA * MD * MC * MB * cstMat (prj Z.2)).trace := by
      rw [show MC * (MB * cstMat (prj Z.2) * MA) * MD = (MC * MB * cstMat (prj Z.2)) * (MA * MD)
        by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [ht, ← pow_two]
  · have ht : (MC * (MB * cstMat (prj Z.2) * MA) * MD * cstMat (prj Z.2)).trace =
        (MA * MD * cstMat (prj Z.2)).trace * (MC * MB * cstMat (prj Z.2)).trace := by
      rw [show MC * (MB * cstMat (prj Z.2) * MA) * MD * cstMat (prj Z.2) =
          MC * MB * (cstMat (prj Z.2) * (MA * MD) * cstMat (prj Z.2)) by
            simp only [Matrix.mul_assoc], prj_mul_prj, Matrix.mul_smul, Matrix.trace_smul,
        smul_eq_mul]
    rw [ht]

private theorem trace_list_sum_mul {W : ℕ} (L : List ℕ)
    (F : ℕ → Matrix (Fin W) (Fin W) (EntPoly W)) (P : Matrix (Fin W) (Fin W) (EntPoly W)) :
    ((L.map F).sum * P).trace = (L.map fun j => (F j * P).trace).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [Matrix.add_mul, Matrix.trace_add, ih]

private theorem cfgP_X_trc (g : ℝ) {W : ℕ} (Z : State W) (u : List WLetter) :
    cfgP g Z (X (.trc u)) = (W : ℂ)⁻¹ • (wordP Z.1 (wordOf u)).trace := by
  simp [cfgP]

private theorem gexp_smul_aux (W : ℕ) (Q t₁ t₂ : EntPoly W) (a b : ℂ) :
    a * b * gexp W (t₁ * t₂ * Q) = gexp W (Q * (a • t₁) * (b • t₂)) := by
  have h : Q * (a • t₁) * (b • t₂) = (a * b) • (t₁ * t₂ * Q) := by
    simp only [Algebra.smul_def, map_mul]
    ring
  rw [h, map_smul, smul_eq_mul]

/-- One step of the Wick expansion of a monomial at a factor `φ` containing `V`. -/
private theorem gexp_cfgP_monomial (g : ℝ) {W : ℕ} (Z : State W) {d : CfgVar →₀ ℕ}
    {φ : CfgVar} (hφd : φ ∈ d.support) (hφ : 0 < φ.vc) :
    gexp W (cfgP g Z (monomial d 1)) =
      ((vPos (φ.word.drop (φ.word.idxOf .v + 1))).map fun j =>
          gexp W (cfgP g Z (monomial (d - Finsupp.single φ 1 + selfPair φ j) 1))).sum +
        ∑ ψ ∈ (d - Finsupp.single φ 1).support,
          ((vPos ψ.word).map fun j =>
            (((d - Finsupp.single φ 1 : CfgVar →₀ ℕ) ψ : ℕ) : ℂ) •
              ((W : ℂ)⁻¹ ^ (crossPair φ ψ j).1 *
                gexp W (cfgP g Z (monomial (d - Finsupp.single φ 1 - Finsupp.single ψ 1 +
                  (crossPair φ ψ j).2) 1)))).sum := by
  set e := d - Finsupp.single φ 1 with he
  have hd : d = e + Finsupp.single φ 1 := by
    rw [he, tsub_add_cancel_of_le]
    exact Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hφd))
  conv_lhs => rw [hd, monomial_add_single, map_mul, mul_comm, gexp_cfgP_X_mul g Z hφ]
  rw [mul_add, derivation_monomial, map_sum, Finset.mul_sum]
  congr 1
  · rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
    rw [selfPair, ← add_assoc, monomial_add_single, monomial_add_single, map_mul (cfgP g Z),
      map_mul (cfgP g Z), cfgP_X_ite, wordOf_append, map_mul (wordP Z.1)]
    have ht : (wordP Z.1 (wordOf (φ.word.take (φ.word.idxOf .v))) *
        wordP Z.1 (wordOf ((φ.word.drop (φ.word.idxOf .v + 1)).drop (j + 1))) *
          cfgPrj Z φ).trace =
        (wordP Z.1 (wordOf ((φ.word.drop (φ.word.idxOf .v + 1)).drop (j + 1))) * cfgPrj Z φ *
          wordP Z.1 (wordOf (φ.word.take (φ.word.idxOf .v)))).trace := by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
    rw [ht, cfgP_X_trc, gexp_smul_aux]
  · refine Finset.sum_congr rfl fun ψ _ => ?_
    have hj : ∀ j, (W : ℂ)⁻¹ ^ (crossPair φ ψ j).1 *
        gexp W (cfgP g Z (monomial (e - Finsupp.single ψ 1 + (crossPair φ ψ j).2) 1)) =
        cfgKap W φ * ((W : ℂ)⁻¹ * cfgKap W ψ) *
          gexp W (cfgP g Z (monomial (e - Finsupp.single ψ 1) 1) *
            (wordP Z.1 (wordOf (ψ.word.take j)) *
              (wordP Z.1 (wordOf (φ.word.drop (φ.word.idxOf .v + 1))) * cfgPrj Z φ *
                wordP Z.1 (wordOf (φ.word.take (φ.word.idxOf .v)))) *
              wordP Z.1 (wordOf (ψ.word.drop (j + 1))) * cfgPrj Z ψ).trace) := by
      intro j
      rw [show (monomial (e - Finsupp.single ψ 1 + (crossPair φ ψ j).2) 1 : CfgPoly) =
          monomial (e - Finsupp.single ψ 1) 1 * monomial (crossPair φ ψ j).2 1 by
        rw [monomial_mul_monomial, one_mul], map_mul (cfgP g Z), ← smul_eq_mul, ← map_smul,
        ← mul_smul_comm, ← cross_identity g Z φ ψ j, mul_smul_comm, map_smul, smul_eq_mul]
    rw [dirD_cfgP_X, trace_list_sum_mul, mul_smul_comm, ← List.sum_map_mul_left, map_smul,
      map_smul, map_list_sum, List.map_map, smul_eq_mul, smul_eq_mul, ← List.sum_map_mul_left,
      ← List.sum_map_mul_left, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
    rw [Function.comp_apply, hj, smul_eq_mul]
    ring

/-! ### Factors without `V` -/

private theorem wordMat_of_count {W : ℕ} {C : Matrix (Fin W) (Fin W) ℂ} (hC : IsUnit C.det)
    (V : Matrix (Fin W) (Fin W) ℂ) (u : List WLetter) (hu : u.count .v = 0) :
    wordMat C V (wordOf u) = C ^ wordExp u := by
  induction u with
  | nil => simp [wordOf, wordExp]
  | cons l u ih =>
    cases l with
    | c =>
      have hu' : u.count .v = 0 := by simpa [List.count_cons] using hu
      rw [wordOf_cons, map_mul, ih hu',
        show wordExp (.c :: u) = 1 + wordExp u by simp [wordExp]; ring,
        Matrix.zpow_add hC, zpow_one]
      simp [wordMat]
    | cInv =>
      have hu' : u.count .v = 0 := by simpa [List.count_cons] using hu
      rw [wordOf_cons, map_mul, ih hu',
        show wordExp (.cInv :: u) = -1 + wordExp u by simp [wordExp]; ring,
        Matrix.zpow_add hC, Matrix.zpow_neg_one]
      simp [wordMat]
    | v => simp at hu

private theorem obsEval_mVar {W : ℕ} (hW : 1 ≤ W) (g : ℝ) {Z : State W} (hZ : IsState Z)
    (k : ℤ) : obsEval g Z (mVar k) = obsM k Z := by
  by_cases hk : k = 0
  · subst hk
    simp [mVar, (obsM_zero_neg hW hZ 0).1]
  · simp [mVar, hk, obsEval]

private theorem obsEval_fVar {W : ℕ} (g : ℝ) {Z : State W} (hZ : IsState Z) (k : ℤ) :
    obsEval g Z (fVar k) = obsF k Z := by
  by_cases hk : k = 0
  · subst hk
    simp [fVar, (obsF_zero_neg hZ 0).1]
  · simp [fVar, hk, obsEval]

/-- A factor without `V` evaluates to its observable. -/
private theorem cfgEval_X_of_vc {W : ℕ} (hW : 1 ≤ W) (g : ℝ) {Z : State W} (hZ : IsState Z)
    (V : Matrix (Fin W) (Fin W) ℂ) {x : CfgVar} (hx : x.vc = 0) :
    cfgEval g Z V (X x) = obsEval g Z x.base := by
  have hC : IsUnit Z.1.det :=
    Matrix.isUnit_det_of_right_inverse (Matrix.mem_unitaryGroup_iff.mp hZ.1)
  cases x with
  | trc u =>
    simp only [cfgEval, aeval_X, CfgVar.base, obsEval_mVar hW g hZ]
    rw [wordMat_of_count hC V u hx]
    rfl
  | mrk u =>
    simp only [cfgEval, aeval_X, CfgVar.base, obsEval_fVar g hZ]
    rw [wordMat_of_count hC V u hx]
    rfl
  | w => simp [cfgEval, CfgVar.base, obsEval]
  | γ => simp [cfgEval, CfgVar.base, obsEval]

/-- The expectation of a monomial without `V`. -/
private theorem gexp_cfgP_base {W : ℕ} (hW : 1 ≤ W) (g : ℝ) {Z : State W} (hZ : IsState Z)
    {d : CfgVar →₀ ℕ} (hd : ∀ x ∈ d.support, x.vc = 0) :
    gexp W (cfgP g Z (monomial d 1)) = obsEval g Z (d.prod fun x k => x.base ^ k) := by
  have h : ∀ V : Matrix (Fin W) (Fin W) ℂ, entEval V (cfgP g Z (monomial d 1)) =
      obsEval g Z (d.prod fun x k => x.base ^ k) := by
    intro V
    rw [entEval_cfgP, monomial_eq, C_1, one_mul, map_finsuppProd, map_finsuppProd]
    refine Finset.prod_congr rfl fun x hx => ?_
    dsimp only
    rw [map_pow, map_pow, cfgEval_X_of_vc hW g hZ V (hd x hx)]
  rw [gexp_apply]
  simp only [h]
  rw [μ_eq_stdGauss, integral_const, probReal_univ, one_smul]

/-! ### Weights -/

private theorem weight_single_one (x : CfgVar) :
    Finsupp.weight CfgVar.vc (Finsupp.single x 1) = x.vc := by
  simp [Finsupp.weight_single]

private theorem vc_ite (φ : CfgVar) (u : List WLetter) :
    (if φ.isMrk then CfgVar.mrk u else CfgVar.trc u).vc = u.count .v := by
  split_ifs <;> rfl

private theorem vc_eq_zero_of_weight {d : CfgVar →₀ ℕ} (hd : Finsupp.weight CfgVar.vc d = 0)
    {x : CfgVar} (hx : x ∈ d.support) : x.vc = 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_zero_iff] at hd
  have := hd x hx
  simp only [smul_eq_mul, mul_eq_zero] at this
  exact this.resolve_left (Finsupp.mem_support_iff.mp hx)

private theorem weight_eq_zero_of_vc {d : CfgVar →₀ ℕ} (hd : ∀ x ∈ d.support, x.vc = 0) :
    Finsupp.weight CfgVar.vc d = 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_eq_zero fun x hx => by simp [hd x hx]

private theorem weight_sub_single {d : CfgVar →₀ ℕ} {x : CfgVar} (hx : x ∈ d.support) :
    Finsupp.weight CfgVar.vc d =
      Finsupp.weight CfgVar.vc (d - Finsupp.single x 1) + x.vc := by
  conv_lhs => rw [← tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr
    (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hx)))]
  rw [map_add, weight_single_one]

private theorem vc_trc (u : List WLetter) : (CfgVar.trc u).vc = u.count .v := rfl

private theorem vc_mrk (u : List WLetter) : (CfgVar.mrk u).vc = u.count .v := rfl

private theorem weight_selfPair {φ : CfgVar} (hφ : 0 < φ.vc) {j : ℕ}
    (hj : j ∈ vPos (φ.word.drop (φ.word.idxOf .v + 1))) :
    Finsupp.weight CfgVar.vc (selfPair φ j) + 2 = φ.vc := by
  have hv : WLetter.v ∈ φ.word := List.count_pos_iff.mp hφ
  have h1 := count_split (idxOf_v hv)
  have h2 := count_split (mem_vPos hj)
  rw [selfPair, map_add, weight_single_one, weight_single_one, vc_ite, vc_trc,
    show φ.vc = φ.word.count .v from rfl, h1, h2, List.count_append]
  omega

private theorem weight_crossPair {φ ψ : CfgVar} (hφ : 0 < φ.vc) {j : ℕ}
    (hj : j ∈ vPos ψ.word) :
    Finsupp.weight CfgVar.vc (crossPair φ ψ j).2 + 2 = φ.vc + ψ.vc := by
  have hv : WLetter.v ∈ φ.word := List.count_pos_iff.mp hφ
  have h1 := count_split (idxOf_v hv)
  have h2 := count_split (mem_vPos hj)
  unfold crossPair
  rw [show φ.vc = φ.word.count .v from rfl, show ψ.vc = ψ.word.count .v from rfl, h1, h2]
  generalize φ.word.take (φ.word.idxOf .v) = A
  generalize φ.word.drop (φ.word.idxOf .v + 1) = B
  generalize ψ.word.take j = C'
  generalize ψ.word.drop (j + 1) = D
  cases φ.isMrk <;> cases ψ.isMrk <;>
    simp only [map_add, weight_single_one, vc_trc, vc_mrk, List.count_append] <;> omega

/-- The pivot is a factor of the monomial containing `V`. -/
private theorem cfgPick_mem {d : CfgVar →₀ ℕ}
    (h : (d.support.filter fun x => 0 < x.vc).Nonempty) :
    cfgPick d ∈ d.support ∧ 0 < (cfgPick d).vc := by
  have := (Classical.choose_spec
    ((d.support.filter fun x => 0 < x.vc).exists_min_image CfgVar.key h)).1
  simp only [cfgPick, h, ↓reduceDIte]
  exact Finset.mem_filter.mp this

private theorem vc_of_not_nonempty {d : CfgVar →₀ ℕ}
    (h : ¬ (d.support.filter fun x => 0 < x.vc).Nonempty) : ∀ x ∈ d.support, x.vc = 0 := by
  intro x hx
  by_contra hne
  exact h ⟨x, Finset.mem_filter.mpr ⟨hx, Nat.pos_of_ne_zero hne⟩⟩

/-! ### The Wick expansion of a monomial -/

private theorem gexp_cfgP_eq_cfgWickAux {W : ℕ} (hW : 1 ≤ W) (g : ℝ) {Z : State W}
    (hZ : IsState Z) : ∀ (n : ℕ) (d : CfgVar →₀ ℕ), Finsupp.weight CfgVar.vc d ≤ n →
      gexp W (cfgP g Z (monomial d 1)) = obsEval g Z (cfgWickAux n d)
  | 0, d, hd => by
    rw [cfgWickAux]
    exact gexp_cfgP_base hW g hZ fun x hx => vc_eq_zero_of_weight (Nat.le_zero.mp hd) hx
  | n + 1, d, hd => by
    rw [cfgWickAux]
    split_ifs with hne
    · obtain ⟨hφd, hφ⟩ := cfgPick_mem hne
      have hwd := weight_sub_single hφd
      rw [gexp_cfgP_monomial g Z hφd hφ, map_add, map_list_sum, List.map_map, map_sum]
      congr 1
      · refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
        rw [Function.comp_apply, ← gexp_cfgP_eq_cfgWickAux hW g hZ n]
        have := weight_selfPair hφ hj
        rw [map_add]
        omega
      · refine Finset.sum_congr rfl fun ψ hψ => ?_
        rw [map_list_sum, List.map_map]
        refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
        rw [Function.comp_apply, map_smul, map_mul, map_pow,
          ← gexp_cfgP_eq_cfgWickAux hW g hZ n]
        · simp [obsEval]
        · have h1 := weight_crossPair hφ hj
          have h2 := weight_sub_single hψ
          rw [map_add]
          omega
    · exact gexp_cfgP_base hW g hZ (vc_of_not_nonempty hne)

private theorem cfgWickAux_eq_zero_of_odd : ∀ (n : ℕ) (d : CfgVar →₀ ℕ),
    Finsupp.weight CfgVar.vc d ≤ n → Odd (Finsupp.weight CfgVar.vc d) → cfgWickAux n d = 0
  | 0, d, hd, ho => by
    rw [Nat.le_zero.mp hd] at ho
    exact absurd ho (by decide)
  | n + 1, d, hd, ho => by
    rw [cfgWickAux]
    split_ifs with hne
    · obtain ⟨hφd, hφ⟩ := cfgPick_mem hne
      have hwd := weight_sub_single hφd
      have hself : ∀ j ∈ vPos ((cfgPick d).word.drop ((cfgPick d).word.idxOf .v + 1)),
          cfgWickAux n (d - Finsupp.single (cfgPick d) 1 + selfPair (cfgPick d) j) = 0 := by
        intro j hj
        have := weight_selfPair hφ hj
        refine cfgWickAux_eq_zero_of_odd n _ ?_ ?_ <;> rw [map_add]
        · omega
        · rcases ho with ⟨m, hm⟩
          exact ⟨m - 1, by omega⟩
      rw [List.map_congr_left hself, Finset.sum_eq_zero]
      · simp
      · intro ψ hψ
        have hcross : ∀ j ∈ vPos ψ.word,
            (((d - Finsupp.single (cfgPick d) 1 : CfgVar →₀ ℕ) ψ : ℕ) : ℂ) •
              (X ObsVar.w ^ (crossPair (cfgPick d) ψ j).1 *
                cfgWickAux n (d - Finsupp.single (cfgPick d) 1 - Finsupp.single ψ 1 +
                  (crossPair (cfgPick d) ψ j).2)) = 0 := by
          intro j hj
          have h1 := weight_crossPair hφ hj
          have h2 := weight_sub_single hψ
          rw [cfgWickAux_eq_zero_of_odd n _ ?_ ?_, mul_zero, smul_zero] <;> rw [map_add]
          · omega
          · rcases ho with ⟨m, hm⟩
            exact ⟨m - 1, by omega⟩
        rw [List.map_congr_left hcross]
        simp
    · exact absurd ho (by rw [weight_eq_zero_of_vc (vc_of_not_nonempty hne)]; decide)

/-- The Wick expansion computes the GUE expectation of a configuration (1.2) [eq:covariance]. -/
theorem integral_cfgEval {W : ℕ} (hW : 1 ≤ W) (g : ℝ) {X : State W} (hX : IsState X)
    (c : CfgPoly) :
    ∫ ω, cfgEval g X (gueBlock W 1 ω 0) c ∂(μ W 1) = obsEval g X (cfgWick c) := by
  simp_rw [← entEval_cfgP]
  rw [← gexp_apply, cfgWick, map_sum]
  conv_lhs => rw [c.as_sum]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [show (monomial d (c.coeff d) : CfgPoly) = c.coeff d • monomial d 1 by
      rw [smul_monomial, smul_eq_mul, mul_one], map_smul, map_smul, map_smul,
    gexp_cfgP_eq_cfgWickAux hW g hX _ d le_rfl]

/-- A configuration all of whose monomials have an odd number of `V` letters has expectation
`0`. -/
theorem cfgWick_eq_zero_of_odd (c : CfgPoly)
    (hc : ∀ d ∈ c.support, Odd (Finsupp.weight CfgVar.vc d)) : cfgWick c = 0 := by
  exact Finset.sum_eq_zero fun d hd => by
    rw [cfgWickAux_eq_zero_of_odd _ d le_rfl (hc d hd), smul_zero]

end LSBA
