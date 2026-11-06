# Lean formalization of Jun Yin, "The Localization Scale of the Block Anderson Model in One Dimension at Arbitrary Coupling and Volume"

This repository contains a Lean 4 / Mathlib proof of the main results of

> Jun Yin, *The Localization Scale of the Block Anderson Model in One Dimension at Arbitrary Coupling and Volume*.

The version of the paper that the Lean code follows is
[`paper/localization-scale-1d-block-anderson.pdf`](paper/localization-scale-1d-block-anderson.pdf) (LaTeX source in
`paper/tex/`). Equation and theorem numbers in `docs/PAPER-VS-LEAN.md` and in the comments of the code refer
to this PDF.

## Main results

| paper | Lean | file |
|---|---|---|
| Theorem 1.4, (1.17): lower half | `LSBA.lower_ratio_endpoint` | `LSBA/Main/Endpoints.lean` |
| Theorem 1.4, (1.17): both halves | `LSBA.main_ratio_endpoint` | `LSBA/Main/UpperEndpoints.lean` |
| Corollary 1.5, (1.18): lower half | `LSBA.lower_simultaneous_endpoint` | `LSBA/Main/Endpoints.lean` |
| Corollary 1.5, (1.18): both halves | `LSBA.simultaneous_endpoint` | `LSBA/Main/UpperEndpoints.lean` |
| Lemma 1.3, (1.15) | `LSBA.rough_density_endpoint` | `LSBA/Main/Endpoints.lean` |
| Lemma 1.2 | `LSBA.distribution_lemma` | `LSBA/Dyson/DistributionLemma.lean` |
| the count forms (2.12) and (3.11) | `LSBA.lower_count_endpoint`, `LSBA.upper_count_endpoint` | `LSBA/Main/Endpoints.lean`, `LSBA/Main/UpperEndpoints.lean` |
| Theorems 3.1–3.4 | `LSBA.strong_upper`, `LSBA.sharp_small_upper`, `LSBA.compact_upper`, `LSBA.large_upper` | `LSBA/Upper/StrongUpper.lean`, `LSBA/Upper/SharpSmall.lean`, `LSBA/Upper/CompactUpper.lean`, `LSBA/Upper/LargeUpper.lean` |

Theorem 1.4 in Lean (`x / 0 = 0` is real division):

```lean
theorem main_ratio_endpoint (κ : ℝ) (hκ : 0 < κ ∧ κ < 1 / 2) :
    ∃ L₀ : ℕ, ∀ L₁ : ℕ, L₀ ≤ L₁ → ∀ D τ : ℝ, 0 < D → 0 < τ →
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g : ℝ, 0 ≤ g →
        1 - (W : ℝ) ^ (-D) ≤
          ∫ ω, (goodCountTwoSided W L (Hmat g W L ω) (bulkSet g κ L₁ L)
                  ((W : ℝ) ^ (-τ) * ellStar W L g) ((W : ℝ) ^ τ * ellStar W L g) : ℝ) /
                (countIn (Hmat g W L ω) (bulkSet g κ L₁ L) : ℝ) ∂(μ W L)
```

Here `Hmat g W L ω` is the block Anderson model H_{g,W,L} of (1.3), with `L` blocks of size `W` and coupling `g`, and
`μ W L` is the probability measure on the Gaussian coordinates `ω` of the blocks (a product of standard real
Gaussians). `ellStar W L g` is the localization scale ℓ_{W,g,L} = min{WL, max{W, W²g²}} of (1.7). `bulkSet g κ L₁ L`
is the energy set J_{g,κ,L} of (1.16), with the threshold L_{κ/2} replaced by `L₁`. `countIn A J` is the number of
eigenvalues of `A` in `J`, with multiplicity. `goodCountTwoSided … a b` counts the simple eigenvalues in that set whose
eigenvector has localization length ℓ between `a` and `b`. `docs/PAPER-VS-LEAN.md` gives every definition and its
relation to the paper.

## External inputs

None. Every result of another paper that the Lean proof uses is proved in this repository from Mathlib.

## Axioms

Every declaration of the library depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. There is
no `sorry` and no declared `axiom`. To check, for example: `#print axioms LSBA.main_ratio_endpoint`.

## Build

The toolchain is `leanprover/lean4:v4.36.0-rc1` (file `lean-toolchain`) with Mathlib `v4.36.0-rc1`.

```
lake exe cache get
lake build
```

The hypotheses of the theorems can be satisfied: `LSBA/Main/Endpoints.lean` and `LSBA/Main/UpperEndpoints.lean` end
with compiled non-degenerate examples of `lower_count_endpoint`, `lower_ratio_endpoint`, `lower_simultaneous_endpoint`,
`rough_density_endpoint` and `upper_count_endpoint`, at fixed parameters, with `W` above the threshold of the theorem.

## `docs/PAPER-VS-LEAN.md`

[`docs/PAPER-VS-LEAN.md`](docs/PAPER-VS-LEAN.md) compares the paper and the Lean proof in detail: what is proved,
every difference between the Lean statements and the printed ones, and where the Lean proof takes a different route
from the paper.

## License and authors

The code is released under the Apache License 2.0; see [`LICENSE`](LICENSE).

Paper: Jun Yin. Lean formalization: Jun Yin, with Claude Opus 5.5 and Claude Sonnet 5.5 (Anthropic).
