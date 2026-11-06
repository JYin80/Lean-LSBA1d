import LSBA.Dyson.FiniteCycle
import LSBA.Dyson.FreeGreen
import LSBA.Model.Cycle

/-!
# Deterministic kernels: definitions

The finite-cycle Dyson equation with independent hopping and variance (A.2)
[da:eq:dyson] and its root selection, the matrix `M_B`, the pair kernels `P` and `Q` of (5.13)
[fo:eq:pairs], the mixed kernel and the propagators of (5.15) [fo:eq:propagators], the scales `ℓ_t`,
`ζ_t`, the
characteristic `z_t`, `η_t` of (5.3) [fo:eq:characteristic], weights, line kernels, the regularity
domain at bounded coupling, and the free transfer matrix.
-/

open MeasureTheory Real Filter Topology Complex
open scoped ENNReal

noncomputable section

open scoped Classical

namespace LSBA

/-- Right side of the finite-cycle Dyson equation with hopping `b` and variance `β`, (A.2)
[da:eq:dyson]: `b = √γ_g g`, `β = γ_g` gives (5.2) [fo:eq:dyson-family]; `β = uγ_g` gives (5.27)
[gc:eq:positive-dyson]. -/
def dysonRHSV (b β : ℝ) (L : ℕ) (z u : ℂ) : ℂ := freeTL b L (z + β * u)

/-- `m` lies in `ℂ_+` and solves the finite-cycle Dyson equation at `z`. -/
def IsDysonRootV (b β : ℝ) (L : ℕ) (z m : ℂ) : Prop := 0 < m.im ∧ m = dysonRHSV b β L z m

/-- A solution in `ℂ_+` at `z` (junk value `0` if there is none). -/
def mRootV (b β : ℝ) (L : ℕ) (z : ℂ) : ℂ :=
  if h : ∃ m : ℂ, IsDysonRootV b β L z m then h.choose else 0

/-- `m(g,E) = m_{g,L}(E)` of (5.3) [fo:eq:characteristic] as the real-energy solution. -/
def mRoot (g : ℝ) (L : ℕ) (E : ℝ) : ℂ := mRootV (hopB g) (gammaG g) L E

/-- Dyson matrix `(bA_L - z - βm)⁻¹`: `M_B(g,E)` of (5.3) [fo:eq:characteristic] and
`M_{B,u}(z;g)` of (5.27) [gc:eq:positive-dyson]. -/
def dysonMat (b β : ℝ) (L : ℕ) (z m : ℂ) : Matrix (Fin L) (Fin L) ℂ :=
  ((b : ℂ) • cycleAdj L - (z + β * m) • (1 : Matrix (Fin L) (Fin L) ℂ))⁻¹

/-- Mixed-sign pair matrix `P_ab = β|M_ab|²`, (5.12) [fo:eq:PQ]. -/
def pairP {L : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) : Matrix (Fin L) (Fin L) ℝ :=
  Matrix.of fun a b => β * ‖M a b‖ ^ 2

/-- Same-sign pair matrix `Q_ab = βM_ab²`, (5.12) [fo:eq:PQ]. -/
def pairQ {L : ℕ} (β : ℝ) (M : Matrix (Fin L) (Fin L) ℂ) : Matrix (Fin L) (Fin L) ℂ :=
  Matrix.of fun a b => (β : ℂ) * M a b ^ 2

/-- Mixed kernel `P(I - uP)⁻¹`, (5.13) [fo:eq:pairs]. -/
def mixedKer {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ) (u : ℝ) : Matrix n n ℝ :=
  P * (1 - u • P)⁻¹

/-- `U^{+-}_{s,t} = (I - sP)(I - tP)⁻¹`, (5.15) [fo:eq:propagators]. -/
def propPM {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ) (s t : ℝ) : Matrix n n ℝ :=
  (1 - s • P) * (1 - t • P)⁻¹

/-- `U^{++}_{s,t} = (I - sQ)(I - tQ)⁻¹`, (5.15) [fo:eq:propagators]. -/
def propPP {n : Type*} [Fintype n] [DecidableEq n] (Q : Matrix n n ℂ) (s t : ℝ) : Matrix n n ℂ :=
  (1 - (s : ℂ) • Q) * (1 - (t : ℂ) • Q)⁻¹

/-- `ℓ_t(g) = min{L, 1 + g/√(γ_g(1-t))}`, (5.18) [fo:eq:scale] (value `1` at `t = 1`). -/
def ellProp (g : ℝ) (L : ℕ) (t : ℝ) : ℝ :=
  min (L : ℝ) (1 + g / Real.sqrt (gammaG g * (1 - t)))

/-- `ζ_t(g) = (Wℓ_t(g)(1-t)γ_g)⁻¹`, (5.18) [fo:eq:scale] (value `0` at `t = 1`). -/
def zetaProp (g : ℝ) (W L : ℕ) (t : ℝ) : ℝ :=
  ((W : ℝ) * ellProp g L t * (1 - t) * gammaG g)⁻¹

/-- `z_t = E + (1-t)γ_g m`, (5.3) [fo:eq:characteristic]. -/
def zChar (g E : ℝ) (m : ℂ) (t : ℝ) : ℂ := (E : ℂ) + (((1 - t) * gammaG g : ℝ) : ℂ) * m

/-- `η_t = (1-t)γ_g Im m`, (5.3) [fo:eq:characteristic]. -/
def etaChar (g : ℝ) (m : ℂ) (t : ℝ) : ℝ := (1 - t) * gammaG g * m.im

/-- Symbol `P̂(k)` on the Fourier grid `2πk/L`, averaged over rows. -/
def kerSymbol {L : ℕ} (P : Matrix (Fin L) (Fin L) ℝ) (k : Fin L) : ℝ :=
  (L : ℝ)⁻¹ * ∑ a : Fin L, ∑ x : Fin L,
    P a x * Real.cos (2 * π * (k : ℝ) * ((x : ℝ) - (a : ℝ)) / L)

/-- Torus distance `|2πk/L|_𝕋` of a grid frequency to `0`. -/
def torusAbs (L : ℕ) (k : Fin L) : ℝ := 2 * π * (min k.val (L - k.val) : ℕ) / L

/-- The weight `w(r) = exp(-c₁(r/ℓ)^θ) + W^{-F}` of Lemma 6.2 [da:lem:scale-budgets]. -/
def weightFn (c₁ θ F : ℝ) (W : ℕ) (ℓ r : ℝ) : ℝ :=
  Real.exp (-(c₁ * (r / ℓ) ^ θ)) + (W : ℝ) ^ (-F)

/-- Periodization `x ↦ Σ_j p(x + jL)` of a kernel on `ℤ`. -/
def perLine (p : ℤ → ℝ) (L : ℕ) (x : Fin L) : ℝ := ∑' j : ℤ, p ((x.val : ℤ) + j * L)

/-- `ε_L = C(1 + L/g²)^C e^{-cL/g²}`, (A.14) [uvp:eq:finiteerror]. -/
def epsL (C c g : ℝ) (L : ℕ) : ℝ :=
  C * (1 + (L : ℝ) / g ^ 2) ^ C * Real.exp (-(c * L / g ^ 2))

/-- Decay rate `λ` with `cosh λ = 1 + δ/(2D)`, (A.28) [ba:eq:linekernel]. -/
def lamGeo (D δ : ℝ) : ℝ := Real.arcosh (1 + δ / (2 * D))

/-- Line mixed kernel `e^{-λ|x|}/√(δ(δ+4D))`, (A.28) [ba:eq:linekernel]. -/
def lineKer (D δ : ℝ) (x : ℤ) : ℝ :=
  Real.exp (-(lamGeo D δ * |(x : ℝ)|)) / Real.sqrt (δ * (δ + 4 * D))

/-- Periodized line kernel `P₀` of Lemma A.4 [uvp:prop:finite] from a line solution `mInf`. -/
def perP0 (g : ℝ) (L : ℕ) (E : ℝ) (mInf : ℂ) : Fin L → ℝ :=
  perLine (fun x : ℤ => gammaG g *
    ‖freeT (hopB g) ((E : ℂ) + gammaG g * mInf) *
      freeRho (hopB g) ((E : ℂ) + gammaG g * mInf) ^ x.natAbs‖ ^ 2) L

/-- Bounded-coupling regular domain: `g ∈ [0,C]`, `|E| ≤ B`, the anchor solves (5.2)
[fo:eq:dyson-family] with
`Im m ≥ c'`. -/
def RegBdd (C B c' : ℝ) (L : ℕ) (g E : ℝ) : Prop :=
  0 ≤ g ∧ g ≤ C ∧ |E| ≤ B ∧ IsDysonRootV (hopB g) (gammaG g) L E (mRoot g L E) ∧
    c' ≤ (mRoot g L E).im

/-- The free transfer matrix `T(E) = [[E, -1], [1, 0]]` (Definition 7.1 [def:transfer-matrices]
at `W = 1`). -/
def transferT (E : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![E, -1; 1, 0]

end LSBA
