import LSBA.Upper.ConversionEndpoint
import LSBA.Upper.LargeTransfer
import LSBA.Model.Cycle

/-!
# Fractional-moment predicates

The hypotheses and conclusions shared by Section 8.1 [sec:fr-concentration] and Section 8.2
[sec:upper-conversion], at fixed parameters: the fixed-energy bound (8.2) [up:eq:fmr-pointwise]
on a cycle and on a Dirichlet path, the energy-averaged bound (8.3) [uva:eq:conversion-input] on
a Dirichlet path, and the negative-moment bound (8.12) [up:eq:negative-transfer-input] over the
boundary frames of Definition 8.3 [def:boundary-frames]. Constants are arguments; the uniformity
of the paper is carried by the theorems that use these predicates.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- (8.2) [up:eq:fmr-pointwise] on the cycle of `L` blocks, at fixed `W, L, g`, energy set `J`,
exponent `q` and constants `C, c, 𝔟`: for all `E ∈ J` and all blocks `x, y`, diagonal included,
`𝔼‖G(x, y; E)‖^q ≤ W^C exp(-c ‖x - y‖_L / 𝔟)`. -/
def FracCycle (W L : ℕ) (g : ℝ) (J : Set ℝ) (q C c b : ℝ) : Prop :=
  ∀ E ∈ J, ∀ x y : Fin L,
    ∫⁻ ω, ‖blockOf (resolventMat (Hmat g W L ω) E) x y‖ₑ ^ q ∂(μ W L) ≤
      ENNReal.ofReal ((W : ℝ) ^ C * Real.exp (-c * cycDist x y / b))

/-- (8.2) [up:eq:fmr-pointwise] on the Dirichlet path of `m` blocks (the operator (8.5)
[up:eq:shifted-resolvent] with zero endpoint shifts), at fixed `W, m, g`, energy set `J`, exponent
`q` and constants `C, c, 𝔟`: for all `E ∈ J` and all blocks `x, y`, diagonal included,
`𝔼‖G(x, y; E)‖^q ≤ W^C exp(-c |x - y| / 𝔟)`. -/
def FracPath (W m : ℕ) (g : ℝ) (J : Set ℝ) (q C c b : ℝ) : Prop :=
  ∀ E ∈ J, ∀ x y : Fin m,
    ∫⁻ ω, ‖blockOf (resolventMat (pathOp g (gueBlock W m ω) 0 0) E) x y‖ₑ ^ q ∂(μ W m) ≤
      ENNReal.ofReal ((W : ℝ) ^ C * Real.exp (-c * |((x : ℕ) : ℝ) - (y : ℕ)| / b))

/-- (8.3) [uva:eq:conversion-input] on the Dirichlet path of `m` blocks, at fixed `W, m, g`,
energy set `J`, exponent `q` and constants `C, c, 𝔟`: for all blocks `x, y`, diagonal included,
`∫_J 𝔼‖G(x, y; E)‖^q dE ≤ W^C exp(-c |x - y| / 𝔟)`. -/
def AvgFracPath (W m : ℕ) (g : ℝ) (J : Set ℝ) (q C c b : ℝ) : Prop :=
  ∀ x y : Fin m,
    ∫⁻ E in J, ∫⁻ ω, ‖blockOf (resolventMat (pathOp g (gueBlock W m ω) 0 0) E) x y‖ₑ ^ q
        ∂(μ W m) ≤
      ENNReal.ofReal ((W : ℝ) ^ C * Real.exp (-c * |((x : ℕ) : ℝ) - (y : ℕ)| / b))

/-- (8.12) [up:eq:negative-transfer-input] at fixed `W, g`, energy set `J`, exponent `s` and
constants `C, c`: for all `n ≥ 1`, `E ∈ J` and boundary frames `Φ` of Definition 8.3
[def:boundary-frames], `𝔼‖D_n(Φ; E)⁻¹‖^s ≤ C W exp(-c n / (W g²))`, over `n` fresh GUE blocks and
at the energy (8.9) [eq:c-transfer]. -/
def NegTransfer (W : ℕ) (g : ℝ) (J : Set ℝ) (s C c : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ E ∈ J, ∀ Φ : Matrix (Fin 2 × Fin W) (Fin W) ℂ, IsBoundaryFrame Φ →
    ∫⁻ ω, ‖(frameD (transferProd g ((max 1 g * E / g : ℝ) : ℂ) (seqBlocks (gueBlock W n ω)) n)
        Φ)⁻¹‖ₑ ^ s ∂(μ W n) ≤
      ENNReal.ofReal (C * W * Real.exp (-c * n / (W * g ^ 2)))

/-- (8.2) [up:eq:fmr-pointwise] on the cycle passes to a smaller energy set, a larger power of
`W`, a smaller rate `c' ≥ 0` and a larger scale. -/
theorem FracCycle.mono {W L : ℕ} {g : ℝ} {J J' : Set ℝ} {q C C' c c' b b' : ℝ} (hW : 1 ≤ W)
    (hJ : J' ⊆ J) (hC : C ≤ C') (hc0 : 0 ≤ c') (hc : c' ≤ c) (hb0 : 0 < b) (hb : b ≤ b')
    (h : FracCycle W L g J q C c b) : FracCycle W L g J' q C' c' b' := by
  intro E hE x y
  refine (h E (hJ hE) x y).trans (ENNReal.ofReal_le_ofReal ?_)
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hd : (0 : ℝ) ≤ (cycDist x y : ℝ) := Nat.cast_nonneg _
  have hb0' : 0 < b' := lt_of_lt_of_le hb0 hb
  have hrate : c' / b' ≤ c / b :=
    div_le_div₀ (hc0.trans hc) hc hb0 hb
  have hexp : Real.exp (-c * cycDist x y / b) ≤ Real.exp (-c' * cycDist x y / b') := by
    apply Real.exp_le_exp.mpr
    have e1 : -c * (cycDist x y : ℝ) / b = -(c / b) * cycDist x y := by ring
    have e2 : -c' * (cycDist x y : ℝ) / b' = -(c' / b') * cycDist x y := by ring
    rw [e1, e2]
    nlinarith
  exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hW1 hC) hexp (Real.exp_pos _).le
    (by positivity)

/-- (8.2) [up:eq:fmr-pointwise] on the cycle passes to the union of two energy sets at equal
constants. -/
theorem FracCycle.union {W L : ℕ} {g : ℝ} {J₁ J₂ : Set ℝ} {q C c b : ℝ}
    (h₁ : FracCycle W L g J₁ q C c b) (h₂ : FracCycle W L g J₂ q C c b) :
    FracCycle W L g (J₁ ∪ J₂) q C c b := by
  rintro E (hE | hE) x y
  · exact h₁ E hE x y
  · exact h₂ E hE x y

end LSBA
