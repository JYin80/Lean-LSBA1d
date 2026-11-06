import LSBA.Flow.Realization
import LSBA.Gauss.RoughDensity
import LSBA.Primitive.Defs
import LSBA.Prop.Domination

/-!
# Flow points and the one-step input

Parameter points `(g, W, L, E, t)` of the flow, the resolvent, Dyson matrix, loop errors and scales
at a point, and the one-step input (5.22) [gc:eq:one-step-input] in fixed-time form.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- A deterministic point `(g, E, L, u)`: coupling, anchor energy, number of blocks, time. -/
structure FlowPt where
  g : ℝ
  E : ℝ
  L : ℕ
  u : ℝ

/-- `G_u(g, E) = (H_u(g) - z_u(g, E))⁻¹` at the anchor `m = m_{g,L}(E)`, (5.3)
[fo:eq:characteristic], for the single-time realization of (5.1) [fo:eq:flow]. -/
def flowG (W : ℕ) (p : FlowPt) (ω : Ω W p.L) : Matrix (Fin p.L × Fin W) (Fin p.L × Fin W) ℂ :=
  resolventMat (flowH p.g W p.L p.u ω) (zChar p.g p.E (mRoot p.g p.L p.E) p.u)

/-- `M = M_B(g, E) ⊗ I_W`, (5.3) [fo:eq:characteristic]; `G̃_u = G_u - M`. -/
def flowM (W : ℕ) (p : FlowPt) : Matrix (Fin p.L × Fin W) (Fin p.L × Fin W) ℂ :=
  dysonMat (hopB p.g) (gammaG p.g) p.L p.E (mRoot p.g p.L p.E) ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)

/-- Squared Hilbert–Schmidt norm `‖X_{ab}‖²_HS` of a block. -/
def blockHS2 {W L : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) : ℝ :=
  ∑ α : Fin W, ∑ β : Fin W, ‖X (a, α) (b, β)‖ ^ 2

/-- The loop error `D_k = ℒ_k - 𝒦_k` of (5.17) [fo:eq:error-hierarchy] at the point `p`. -/
def flowErr (W : ℕ) (p : FlowPt) {k : ℕ} (a : Fin k → Fin p.L) (σ : Fin k → Bool)
    (ω : Ω W p.L) : ℂ :=
  loopTr (flowG W p ω) a σ - primLoop p.g W p.L p.E (mRoot p.g p.L p.E) p.u a σ

/-- `ζ_u(g)` of (5.18) [fo:eq:scale] at the point. -/
def flowZeta (W : ℕ) (p : FlowPt) : ℝ := zetaProp p.g W p.L p.u

/-- `ℓ_u(g)` of (5.18) [fo:eq:scale] at the point. -/
def flowEll (p : FlowPt) : ℝ := ellProp p.g p.L p.u

/-- Label words with signs of length `k` on `ℤ_L`. -/
abbrev Word (k L : ℕ) : Type := (Fin k → Fin L) × (Fin k → Bool)

/-- The estimates (5.22) [gc:eq:one-step-input] at the points `pt i`, `i ∈ Dom W`, with the
maxima over labels and signs inside the probability, for every loop length `k ≥ 1` and every
`ε, A, F > 0`, profile constants `c_p, θ`. -/
structure OneStepInput (cp θ : ℝ) {ι : Type*} (pt : ι → FlowPt) (Dom : ℕ → Set ι) : Prop where
  loop : ∀ k : ℕ, 1 ≤ k → PrecMax (fun i => (pt i).L) Dom (Λ := fun _ i => Word k (pt i).L)
    (fun W i w ω => loopTr (flowG W (pt i) ω) w.1 w.2) (fun W i _ => flowZeta W (pt i) ^ (k - 1))
  err : ∀ k : ℕ, 1 ≤ k → PrecMax (fun i => (pt i).L) Dom (Λ := fun _ i => Word k (pt i).L)
    (fun W i w ω => flowErr W (pt i) w.1 w.2 ω) (fun W i _ => flowZeta W (pt i) ^ k)
  avg : PrecMax (fun i => (pt i).L) Dom (Λ := fun _ i => Fin (pt i).L × Fin (pt i).L)
    (fun W i ab ω => blockTr (flowG W (pt i) ω - flowM W (pt i)) ab.1 ab.2)
    (fun W i _ => flowZeta W (pt i))
  entry : PrecMax (fun i => (pt i).L) Dom
    (Λ := fun W i => (Fin (pt i).L × Fin W) × (Fin (pt i).L × Fin W))
    (fun W i e ω => (flowG W (pt i) ω - flowM W (pt i)) e.1 e.2)
    (fun W i _ => Real.sqrt (flowZeta W (pt i)))
  pair : ∀ F : ℝ, 0 < F → PrecMax (fun i => (pt i).L) Dom
    (Λ := fun _ i => Fin (pt i).L × Fin (pt i).L)
    (fun W i ab ω => flowErr W (pt i) ![ab.1, ab.2] ![true, false] ω)
    (fun W i ab => flowZeta W (pt i) ^ 2 * weightFn cp θ F W (flowEll (pt i)) (cycDist ab.1 ab.2))
  tail : ∀ k : ℕ, 2 ≤ k → ∀ ε A : ℝ, 0 < ε → 0 < A → PrecMax (fun i => (pt i).L) Dom
    (Λ := fun W i => {w : Word k (pt i).L // (W : ℝ) ^ ε * flowEll (pt i) < wordDiam w.1})
    (fun W i w ω => ((‖loopTr (flowG W (pt i) ω) w.1.1 w.1.2‖ + ‖flowErr W (pt i) w.1.1 w.1.2 ω‖ :
      ℝ) : ℂ))
    (fun W _ _ => (W : ℝ) ^ (-A))

end LSBA
