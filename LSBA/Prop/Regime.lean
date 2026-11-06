import LSBA.Prop.Objects
import LSBA.Kernel.Comparison

/-!
# The comparison reach and the regime

The comparison point of Lemma 6.3 [da:lem:comparison-parameters], the reach of a base family under
nested comparison chains of length at most `J`, and the deterministic regime of the general
Theorem 5.12 [gc:thm:common] in general form: propagators, kernels, budgets, comparison
parameters, heights and the primitive slot on the reach.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- One comparison of Lemma 6.3 [da:lem:comparison-parameters]: from `(g, E, L, u)` and an earlier
time `s`, the point `(g', E', L, s)` with `g' = g√(s/u)` and the energy `E'` of (A.58)
[bl:eq:exactlaw]. -/
def cmpPt (p : FlowPt) (s : ℝ) : FlowPt :=
  ⟨gCmp p.g s p.u, ECmp p.g p.L p.E (mRoot p.g p.L p.E) s p.u, p.L, s⟩

/-- Points reached from a base family by nested chains of comparisons (Lemma 6.3(b)
[da:lem:comparison-parameters]), with the number `d` of comparisons used: earlier times
`v ≥ 1/2` at the same `(g, E, L)`, one comparison `p ↦ cmpPt p s` with `1/2 ≤ s ≤ u` per unit of
depth, and depth lifting. -/
inductive CmpReach (base : ℕ → Set FlowPt) (W : ℕ) : ℕ → FlowPt → Prop
  | base {p : FlowPt} : p ∈ base W → CmpReach base W 0 p
  | earlier {d : ℕ} {p : FlowPt} (v : ℝ) : CmpReach base W d p → 1 / 2 ≤ v → v ≤ p.u →
      CmpReach base W d ⟨p.g, p.E, p.L, v⟩
  | cmp {d : ℕ} {p : FlowPt} (s : ℝ) : CmpReach base W d p → 1 / 2 ≤ s → s ≤ p.u →
      CmpReach base W (d + 1) (cmpPt p s)
  | lift {d : ℕ} {p : FlowPt} : CmpReach base W d p → CmpReach base W (d + 1) p

/-- The deterministic data of a propagation regime, the parameter domain of the general form
of Theorem 5.12 [gc:thm:common]: a base family of points, a chain depth `J`,
and, for `W ≥ W₀`, at every point reached by at most `J` comparisons: the Dyson bounds (6.2)
[fo:eq:propagation-dyson], the kernel profile (6.3) [fo:eq:kernel-bounds] with remainder
`ℓ_u⁻¹W^{-A}`, the polynomial budget (6.6) [fo:eq:spatial-sum-budget], the comparison points of
(6.9) [da:eq:comparison-parameters] with the endpoint identity, the positive-height bounds
(6.12) [gc:eq:positive-stability]–(6.14) [da:eq:height-derivative] on the comparison segments, and
the primitive-loop
slot, tails (5.21) [fo:eq:primitive-tail] and long pairs (B.16) [b:eq:primitive-long-pair]. -/
structure PropRegime where
  base : ℕ → Set FlowPt
  J : ℕ
  C : ℝ
  c : ℝ
  one_le_C : 1 ≤ C
  c_pos : 0 < c
  time : ∀ W p, p ∈ base W → 1 / 2 ≤ p.u ∧ (W : ℝ) ^ (-3 : ℝ) ≤ 1 - p.u
  dyson : ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ d p, d ≤ J → CmpReach base W d p →
    3 ≤ p.L ∧ 0 ≤ p.g ∧ IsDysonRootV (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E) ∧
    C⁻¹ ≤ (mRoot p.g p.L p.E).im ∧ (mRoot p.g p.L p.E).im ≤ C ∧
    (∀ a b, ‖dysonMat (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E) a b‖ ≤ C) ∧
    (∀ a, gammaG p.g * ∑ b, (‖dysonMat (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E) a b‖ +
      ‖dysonMat (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E) a b‖ ^ 2) ≤ C) ∧
    ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ a, ∑ b, ‖(1 - (u : ℂ) • pairQ (gammaG p.g)
      (dysonMat (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E)))⁻¹ a b‖ ≤ C
  kernel : ∀ A : ℝ, 0 < A → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ d p, d ≤ J → CmpReach base W d p →
    ∀ a b, 0 ≤ mixedKer (pairP (gammaG p.g)
        (dysonMat (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E))) p.u a b ∧
      mixedKer (pairP (gammaG p.g)
        (dysonMat (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E))) p.u a b ≤
      C / ((1 - p.u) * ellProp p.g p.L p.u) * Real.exp (-(c * cycDist a b / ellProp p.g p.L p.u)) +
        (ellProp p.g p.L p.u)⁻¹ * (W : ℝ) ^ (-A)
  budget : ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ d p, d ≤ J → CmpReach base W d p →
    gammaG p.g * p.L + p.L / ellProp p.g p.L p.u ≤ (W : ℝ) ^ C
  cmp : ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ d p (s : ℝ), d < J → CmpReach base W d p → 1 / 2 ≤ s →
    s ≤ p.u →
    (wCmp p.g p.L p.E (mRoot p.g p.L p.E) s p.u).re = (zChar p.g p.E (mRoot p.g p.L p.E) p.u).re ∧
    etaChar p.g (mRoot p.g p.L p.E) p.u ≤ (wCmp p.g p.L p.E (mRoot p.g p.L p.E) s p.u).im ∧
    (wCmp p.g p.L p.E (mRoot p.g p.L p.E) s p.u).im ≤
      C * ((1 - s) / (1 - p.u)) * etaChar p.g (mRoot p.g p.L p.E) p.u ∧
    wCmp p.g p.L p.E (mRoot p.g p.L p.E) s p.u = ((xiCmp p.g s p.u : ℝ) : ℂ)⁻¹ *
      zChar (cmpPt p s).g (cmpPt p s).E (mRoot (cmpPt p s).g p.L (cmpPt p s).E) s
  height : ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ d p (s y : ℝ), d < J → CmpReach base W d p →
    1 / 2 ≤ s → s ≤ p.u → etaChar p.g (mRoot p.g p.L p.E) p.u ≤ y →
    y ≤ (wCmp p.g p.L p.E (mRoot p.g p.L p.E) s p.u).im →
    IsDysonRootV (hopB p.g) (p.u * gammaG p.g) p.L
        (((zChar p.g p.E (mRoot p.g p.L p.E) p.u).re : ℂ) + (y : ℂ) * Complex.I)
        (mRootV (hopB p.g) (p.u * gammaG p.g) p.L
          (((zChar p.g p.E (mRoot p.g p.L p.E) p.u).re : ℂ) + (y : ℂ) * Complex.I)) ∧
      c ≤ (mRootV (hopB p.g) (p.u * gammaG p.g) p.L
          (((zChar p.g p.E (mRoot p.g p.L p.E) p.u).re : ℂ) + (y : ℂ) * Complex.I)).im ∧
      (∀ a b, ‖segMat p.g p.L (zChar p.g p.E (mRoot p.g p.L p.E) p.u).re p.u (y / gammaG p.g) a b‖
        ≤ C) ∧
      (∀ a, gammaG p.g * ∑ b,
        (‖segMat p.g p.L (zChar p.g p.E (mRoot p.g p.L p.E) p.u).re p.u (y / gammaG p.g) a b‖ +
         ‖segMat p.g p.L (zChar p.g p.E (mRoot p.g p.L p.E) p.u).re p.u (y / gammaG p.g) a b‖ ^ 2)
          ≤ C) ∧
      (∀ a, ∑ b, ‖(1 - pairQ (p.u * gammaG p.g)
        (segMat p.g p.L (zChar p.g p.E (mRoot p.g p.L p.E) p.u).re p.u (y / gammaG p.g)))⁻¹ a b‖
          ≤ C) ∧
      (∀ a b, DifferentiableAt ℝ (fun r : ℝ =>
        segMat p.g p.L (zChar p.g p.E (mRoot p.g p.L p.E) p.u).re p.u r a b) (y / gammaG p.g)) ∧
      ∀ a b, ‖deriv (fun r : ℝ =>
        segMat p.g p.L (zChar p.g p.E (mRoot p.g p.L p.E) p.u).re p.u r a b) (y / gammaG p.g)‖ ≤ C
  prim : ∀ kmax : ℕ, ∀ δ : ℝ, 0 < δ → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ d p, d ≤ J →
    CmpReach base W d p → ∀ k : ℕ, 2 ≤ k → k ≤ kmax → ∀ (a : Fin k → Fin p.L) (σ : Fin k → Bool),
      ‖primLoop p.g W p.L p.E (mRoot p.g p.L p.E) p.u a σ‖ ≤
        (W : ℝ) ^ δ * zetaProp p.g W p.L p.u ^ (k - 1)
  primTail : ∀ k : ℕ, 2 ≤ k → ∀ ε Q : ℝ, 0 < ε → 0 < Q → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
    ∀ d p, d ≤ J → CmpReach base W d p → ∀ (a : Fin k → Fin p.L) (σ : Fin k → Bool),
      (W : ℝ) ^ ε * ellProp p.g p.L p.u < wordDiam a →
        ‖primLoop p.g W p.L p.E (mRoot p.g p.L p.E) p.u a σ‖ ≤ (W : ℝ) ^ (-Q)
  longPair : ∀ θ cp F : ℝ, 0 < θ → θ ≤ 1 / 2 → 0 < cp → 0 < F → ∃ C' : ℝ, ∃ W₀ : ℕ,
    ∀ W : ℕ, W₀ ≤ W → ∀ d p, d ≤ J → CmpReach base W d p → ∀ (a b : Fin p.L) (σ₁ σ₂ : Bool),
      ellProp p.g p.L p.u * Real.log W ^ ((3 : ℝ) / 2) ≤ cycDist a b →
        ‖primLoop p.g W p.L p.E (mRoot p.g p.L p.E) p.u ![a, b] ![σ₁, σ₂]‖ ≤
          C' * zetaProp p.g W p.L p.u ^ 2 * weightFn cp θ F W (ellProp p.g p.L p.u) (cycDist a b)

end LSBA
