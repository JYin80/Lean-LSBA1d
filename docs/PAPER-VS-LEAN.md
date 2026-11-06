# The paper and the Lean library

This document compares

> Jun Yin, *The Localization Scale of the Block Anderson Model in One Dimension at Arbitrary Coupling and Volume*

with its Lean 4 / Mathlib formalization in this repository. The paper is `paper/localization-scale-1d-block-anderson.pdf`, with source `paper/tex/localization-scale-1d-block-anderson.tex`. Theorem and equation numbers are those of this PDF; each result is cited by its number and its TeX label, for example Theorem 1.4 [thm:main]. Lean declarations live in the namespace `LSBA` and are cited by name and file. Part 5 below is a table from paper results to Lean names.

Notation. In Lean statements, `Fin L` indexes the blocks, `Fin W` the orbitals, and `Fin L × Fin W` the sites, block first. Real powers W^{-τ} are written with `Real.rpow`. All constants are existential and come after the fixed parameters, as in the paper.

## 1. What is proved

### 1.1 Main statements

| paper | Lean | file | how the Lean statement corresponds |
|---|---|---|---|
| Theorem 1.4 [thm:main], (1.17) [eq:main], both halves | `main_ratio_endpoint` | `LSBA/Main/UpperEndpoints.lean` | the expected ratio with both bounds on ℓ(ψ_k) |
| Theorem 1.4 [thm:main], (1.17) [eq:main], lower half | `lower_ratio_endpoint` | `LSBA/Main/Endpoints.lean` | the same ratio with `goodCount` (lower bound on ℓ only) |
| Corollary 1.5 [cor:simultaneous], (1.18) [eq:simultaneous], both halves | `simultaneous_endpoint` | `LSBA/Main/UpperEndpoints.lean` | the measure of the bad event is at most W^{-D} |
| Corollary 1.5 [cor:simultaneous], (1.18) [eq:simultaneous], lower half | `lower_simultaneous_endpoint` | `LSBA/Main/Endpoints.lean` | the same, for eigenvectors below W^{-τ}ℓ_{W,g,L} |
| (2.12) [uv:eq:lower-regions-output] | `lower_count_endpoint` | `LSBA/Main/Endpoints.lean` | the count B₋, with its a.e. measurability |
| (3.11) [uv:eq:upper-count] | `upper_count_endpoint` | `LSBA/Main/UpperEndpoints.lean` | the count B₊, with its a.e. measurability |
| Lemma 1.3 [lem:rough-density], (1.15) [eq:rough-counting] | `rough_density_endpoint` | `LSBA/Main/Endpoints.lean` | the bad event: some x has deviation above δ |
| Lemma 1.2 [da:lem:distribution] | `distribution_lemma` | `LSBA/Dyson/DistributionLemma.lean` | the three items, as a conjunction |
| Theorem 3.1 [thm:strong-upper] | `StrongUpper`, proved by `strong_upper` | `LSBA/Upper/Interface.lean`, `LSBA/Upper/StrongUpper.lean` | (3.6) [eq:averaged-tail] with (3.7) [eq:strong-radius] |
| Theorem 3.2 [thm:sharp-small-upper] | `SharpSmallUpper`, proved by `sharp_small_upper` | `LSBA/Upper/Interface.lean`, `LSBA/Upper/SharpSmall.lean` | (3.6) [eq:averaged-tail] with (3.8) [eq:sharp-small-radius] |
| Theorem 3.3 [thm:compact-upper] | `CompactUpper`, proved by `compact_upper` | `LSBA/Upper/Interface.lean`, `LSBA/Upper/CompactUpper.lean` | (3.6) [eq:averaged-tail] with (3.9) [eq:coarse-radius] |
| Theorem 3.4 [thm:large-upper] | `LargeUpper`, proved by `large_upper` | `LSBA/Upper/Interface.lean`, `LSBA/Upper/LargeUpper.lean` | (3.6) [eq:averaged-tail] with (3.10) [eq:large-radius] |

The seven endpoints are also called E1–E4 (`lower_count_endpoint`, `lower_ratio_endpoint`, `lower_simultaneous_endpoint`, `rough_density_endpoint`) and U1–U3 (`upper_count_endpoint`, `main_ratio_endpoint`, `simultaneous_endpoint`).

The step from the four theorems to (3.11) [uv:eq:upper-count] is `upperCount_of_averagedTail` (`LSBA/Upper/Assembly.lean`), which takes `StrongUpper`, `SharpSmallUpper`, `CompactUpper`, `LargeUpper` as its four arguments.

Theorem 1.4 [thm:main] in Lean:

```lean
theorem main_ratio_endpoint (κ : ℝ) (hκ : 0 < κ ∧ κ < 1 / 2) :
    ∃ L₀ : ℕ, ∀ L₁ : ℕ, L₀ ≤ L₁ → ∀ D τ : ℝ, 0 < D → 0 < τ →
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g : ℝ, 0 ≤ g →
        1 - (W : ℝ) ^ (-D) ≤
          ∫ ω, (goodCountTwoSided W L (Hmat g W L ω) (bulkSet g κ L₁ L)
                  ((W : ℝ) ^ (-τ) * ellStar W L g) ((W : ℝ) ^ τ * ellStar W L g) : ℝ) /
                (countIn (Hmat g W L ω) (bulkSet g κ L₁ L) : ℝ) ∂(μ W L)
```

The division is real division, so 0/0 = 0 as in the paper. The fixed parameters κ, D, τ precede the width threshold W₀, and W₀ is uniform in L ≥ 3 and g ≥ 0. Here L₁ stands for the threshold L_{κ/2} of (1.16) [eq:bulk-sampling]: Lemma 1.3 [lem:rough-density] only asserts that a threshold exists and any larger one is also valid, so one takes L_{κ/2} ≥ L₀.

### 1.2 Definitions in the statements

| paper | Lean | file | relation |
|---|---|---|---|
| index set (1.1) [eq:blocks] | `Fin L × Fin W`, coordinates through `finProdFinEquiv` | `LSBA/Spectral/Length.lean` | (a, α) ↦ α + W·a, counted from 0 |
| GUE blocks (1.2) [eq:covariance] | `Ω`, `μ`, `gueBlock` | `LSBA/Model/Basic.lean` | product of standard real Gaussians; V_a is an explicit function of ω, and (1.2) [eq:covariance] is the theorem `gueBlock_covariance` (`LSBA/Gauss/GUELaw.lean`) |
| the matrix A_L, (1.3) [eq:model] | `cycleAdj` | `LSBA/Model/Basic.lean` | defined for every L; equal to the adjacency matrix for L ≥ 3 |
| the model (1.3) [eq:model] | `Hdet`, `Hmat` | `LSBA/Model/Basic.lean` | same formula, for every real g and every L |
| eigenvalues and eigenvectors (1.5) [eq:eigenvectors] | Mathlib's `Matrix.IsHermitian.eigenvalues`, `Matrix.IsHermitian.eigenvectorBasis` | Mathlib | ordering not used; the spectrum is a.s. simple by `ae_injective_eigenvalues` (`LSBA/Spectral/SimpleSpectrum.lean`) |
| ℓ(ψ), Definition 1.1 [def:length], (1.6) [eq:length] | `ell`, `ellProf`, `ellMass` | `LSBA/Spectral/Length.lean` | `ellMass` is defined for every real profile, with the extra clause r = N; on profiles of total mass ≥ 1/2 it is the paper's ℓ |
| ℓ_{W,g}, ℓ_{W,g,L} of (1.7) [eq:scales] | `ellScale`, `ellStar` | `LSBA/Model/Scales.lean` | same |
| m_g, (1.9) [eq:dyson] | `mDyson`, characterized by `mDyson_spec`, `mDyson_unique`, `mDyson_asymp` | `LSBA/Dyson/Scalar.lean` | the unique solution in ℂ₊; the value 0 if there were none; for g ≥ 0 the three theorems exclude that value. `mDyson_asymp` is the explicit form ‖z m_g(z) + 1‖ ≤ 3/(‖z‖ − 3) of m_g ∼ −1/z |
| ν_g | `nuDyson`, characterized by `nuDyson_spec` | `LSBA/Dyson/Stieltjes.lean` | a probability measure with Stieltjes transform m_g, chosen by the axiom of choice (`Measure.dirac` at 0 if there were none; `nuDyson_spec` excludes it for g ≥ 0) |
| F_g, (1.10) [eq:distribution] | `Fdist`; `Fdist_eq_integral_bdry` | `LSBA/Dyson/Stieltjes.lean`, `LSBA/Dyson/Density.lean` | F_g(x) = ν_g((−∞, x]); the second equality of (1.10) [eq:distribution] is the theorem, with E + i0 given by `mDysonBdry` (`LSBA/Dyson/Boundary.lean`) |
| J_{g,κ,L}, (1.16) [eq:bulk-sampling] | `bulkSet` | `LSBA/Model/Bulk.lean` | `bulkSet g κ L₀ L` is the paper's set with L_{κ/2} replaced by L₀, defined for all real g, κ |
| #{k : λ_k ∈ J} | `countIn` | `LSBA/Spectral/Counts.lean` | with multiplicity; 0 on non-Hermitian matrices |
| B₋ of (2.12) [uv:eq:lower-regions-output] | `badCount` | `LSBA/Spectral/Counts.lean` | k with λ_k ∈ J that are multiple, or simple with ℓ < r |
| B₊ of the proof of Theorem 1.4 [thm:main] | `badCountUp` | `LSBA/Spectral/TwoSidedCounts.lean` | k with λ_k ∈ J that are multiple, or simple with ℓ > r |
| numerator of (1.17) [eq:main] | `goodCountTwoSided`, `goodCount` | `LSBA/Spectral/TwoSidedCounts.lean`, `LSBA/Spectral/Counts.lean` | k with λ_k ∈ J simple and r ≤ ℓ ≤ R (resp. r ≤ ℓ) |
| N⁻¹#{k : λ_k ≤ x} | `empCDF` | `LSBA/Spectral/Counts.lean` | division by the cardinality of the index set, which is L·W |
| the count of (3.6) [eq:averaged-tail] | `AveragedTailBound`, `tailCount`, `blockTail` | `LSBA/Upper/Interface.lean`, `LSBA/Spectral/BlockTail.lean` | see part 2.2 |

The counts do not depend on a choice of eigenbasis. They use the diagonal of the spectral projection, `projDiag` (`LSBA/Spectral/Counts.lean`), which equals |ψ_k|² at a simple eigenvalue, and they count a multiple eigenvalue as bad. By `ae_injective_eigenvalues` the Lean counts equal the paper's almost surely.

### 1.3 Axioms

`#print axioms` of `main_ratio_endpoint`, of the other six endpoints above, of `distribution_lemma` and of the four theorems lists exactly `propext`, `Classical.choice`, `Quot.sound`. The library has no `sorry` and no declared `axiom`. The files `LSBA/Main/Endpoints.lean` and `LSBA/Main/UpperEndpoints.lean` end with compiled `example`s that instantiate E1–E4 and U1 at fixed parameters, with W above the threshold of the theorem.

## 2. Statement differences

Each entry below states how the Lean statement differs from the paper's, and most differences are of form. Where the Lean statement does not give the paper's as printed, the entry says so: with "weaker" (a bound, a constant or a uniformity), "stronger hypothesis", "fixed time" (no supremum over time, part 4.1), "not formalized" or "only" (a clause or a case is not stated), or by naming the difference directly, for example "≤", not the identity, in (E.7). Each such form suffices for every later use in the library, and no statement of part 1 is affected.

### 2.1 Conventions used throughout

- **Uniform form instead of sequences.** The paper writes parameter families g = g(W), L = L(W) and "for sufficiently large W". Lean fixes the parameters, then gives ∃ W₀ with the conclusion for all W ≥ W₀, uniformly on the stated range. Conditions such as log W ≪ L are written ρ(W) log W ≤ L for a function ρ → ∞ chosen before W₀ (`small_lower_fdist`, `large_lower`, `theorem412_large`); the moment constant is chosen before ρ, as the paper's last sentences in Theorem 2.3 [thm:bounded-lower] and Theorem 2.5 [uvu:thm:terminal] say.
- **Standing hypotheses.** L ≥ 3 and g ≥ 0 are the paper's standing conditions (the paragraph after (1.5) [eq:eigenvectors]). "Every L" reads L ≥ 3. They appear as hypotheses only where the proofs use them, so many statements hold for all L or all real g.
- **Total functions.** Matrix inverses are Mathlib's `Matrix.inv` (0 on a singular matrix), so a singular resolvent is 0; g⁻¹ is 0 at g = 0. Where a statement needs invertibility it carries an explicit `IsUnit` hypothesis or a proof of a.e. invertibility (`ae_det_ne_zero_gueBlock`). Data that need a Hermitian matrix are 0 off Hermitian matrices.
- **Expectations.** Upper bounds on moments are written with the lower Lebesgue integral ∫⁻ ‖X‖ₑ^p, which cannot become vacuous when X is not integrable. Some upper bounds on a Bochner integral also give integrability or measurability: `Integrable` conjuncts in `resolvent_moments`, `transfer_moments`, `small_lower_fdist`, `large_lower`; `AEMeasurable` conjuncts in `lower_count_endpoint`, `upper_count_endpoint`. The count bounds `AveragedTailBound`, `haar_count_le`, `outlier_mean_le` have no such conjunct; `aemeasurable_tailCount_Hmat`, `aemeasurable_badCount_Hmat` give the measurability of the first two counts separately.
- **Conditional expectations.** No filtrations are built. Conditioning on blocks is written as an exact Tonelli identity on the coordinates of `Ω` (`lintegral_windowJoin`, `lintegral_blockSnoc`, `lintegral_gueBlock_fresh_le`).
- **Gaussian coordinates.** Vector fields and divergences live on `Ω W q` with coordinates of variance 1, not on Herm(W)^q with variance 1/W; `hermCoord` converts between them.
- **Indices.** Blocks, sites, loop positions and input blocks are numbered from 0, so V k in the Lean transfer products is V_{k+1} of the paper. In Lean loop identities the index k of `loopTr_ward`, `primF_ward` is the paper's k − 1.
- **Stochastic domination.** X ≺ Y is written with an explicit order of quantifiers in `PrecMax`: parameter family and labels, then (ε, D), then W₀, then the point.
- **Explicit constants.** Many unnamed constants are explicit in Lean, for example c₀ = 1/8 and c = 1/25 in (2.2) [eq:haar-count], κ₀ = c = κ²/4 and C = 8/κ² in (1.14) [eq:bulk-bridge], and the Poincaré and concentration constants π²/8 and 1/π² (`poincare_grad`, `concentration_complex`).
- **Measurable sets.** Energy intervals J are usually any measurable set J ⊆ [−E₀, E₀]. By monotonicity this is equivalent to the interval form or stronger.
- **Smoothness.** Gaussian integration by parts and Poincaré inequalities carry their regularity hypotheses explicitly: C¹ with polynomially bounded gradient (`poincare_grad_poly`, `moment_poincare_grad_poly`), and the class `IBPAdmissible` for vector fields. The paper says "smooth".
- **Gaussian concentration.** `concentration_real`, `concentration_complex` are stated for C¹ Lipschitz functions and `concentration_lipschitz` for every Euclidean-Lipschitz function.
- **Names.** Module and declaration names are identifiers, not paper numbers. For example, `lemma46_fixedTime` in `LSBA/Averaging/Lemma46.lean` corresponds to Lemma 5.6 [fo:prop:inputs], `loop_sampling` in `LSBA/Sampling/Lemma48.lean` to Lemma 5.8 [uvc:thm:ordinary-sampling], and `theorem412_large` in `LSBA/Prop/Theorem412.lean` to a case of Theorem 5.12 [gc:thm:common]. The paper numbers are the ones given in this document and in the comments.

### 2.2 The main statements

**Theorem 1.4 [thm:main] (`main_ratio_endpoint`).** The threshold in J_{g,κ,L} is any L₁ ≥ L₀; the paper's choice is one case (part 1.1). All τ > 0 are allowed; the proofs work with τ ∈ (0, 1) and pass to larger τ by monotonicity of the count. The eigenvector count treats a multiple eigenvalue as not good, which changes nothing almost surely. A lower bound on a Bochner integral is not vacuous, so no measurability conjunct is needed.

**(2.12) and (3.11).** (2.12) [uv:eq:lower-regions-output] and (3.11) [uv:eq:upper-count] hold in Lean for every fixed threshold L₀ (`lower_count_endpoint`, `upper_count_endpoint`). This is stronger than the paper's threshold L_{κ/2}. They keep τ ∈ (0, 1), the range of the paper's proofs, and they add the a.e. measurability of the count, without which an upper bound on the integral would say nothing. `badCount` counts ℓ < r (not ≤) and `badCountUp` counts ℓ > r, as in the paper.

**Corollary 1.5 [cor:simultaneous] (`simultaneous_endpoint`).** For every fixed L₀ the measure of {ω : 0 < B₋ + B₊} is at most W^{-D}. Since μ(A) + μ(Aᶜ) ≥ 1, this gives P ≥ 1 − W^{-D} of (1.18) [eq:simultaneous] with no measurability input. Lean proves it from the counts (2.12) [uv:eq:lower-regions-output], (3.11) [uv:eq:upper-count] by Markov's inequality with D′ = D + B_L + 2.

**Lemma 1.3 [lem:rough-density] (`rough_density_endpoint`, a restatement of `rough_density_law`).** The condition is L ≥ max{L_δ, 3} and g ≥ 0. "sup_x > δ" is written ∃ x, δ < |…|, which is equivalent.

**Lemma 1.2 [da:lem:distribution] (`distribution_lemma`).** Item (i) is written ν_g([−4, 4]ᶜ) = 0. Item (ii) is the ε–h₀ form of the limit in (1.13) [rd:eq:noatoms]. Item (iii) is (1.14) [eq:bulk-bridge] with the constants existential. The library also has the stronger forms: `nuDyson_Icc_le` gives ν_g([x − h, x + h]) ≤ √(2h) for 0 < h ≤ 1/2 (for h > 1/2 the bound exceeds 1); `bulk_window_explicit` gives (iii) with κ₀ = c = κ²/4, C = 8/κ²; `nuDyson_compl_support` gives the support bound (2g + 2)/max{1, g}. The weak continuity of g ↦ ν_g on [0, ∞] and the limit laws of (1.11) [eq:arcsine] are not formalized; no proof in the library uses them.

**(3.6) and Theorem 3.1 [thm:strong-upper]–Theorem 3.4 [thm:large-upper].** `AveragedTailBound W L g J R A D` has two exponents: the threshold W^{-A} inside the count and the bound W^{-D} outside. (3.6) [eq:averaged-tail] is the case A = D. Conversely, the bound at max{A, D} gives the whole family, so the two forms are equivalent. The block tail is `blockTail`, with the minimum over a as a `Finset.min'`. The four predicates take R equal to the paper's bound, which is an admissible choice under "R ≤", and larger R follow by `averagedTailBound_mono`. In Theorem 3.1 [thm:strong-upper], `StrongUpper` has c_* before A and D as in the paper, J = `Set.univ`, R = ⌈(log W)²⌉₊, and the added hypothesis g ≥ 0. log is `Real.log`. The expectation is a Bochner integral with no measurability conjunct; measurability of the count is the separate lemma `aemeasurable_tailCount_Hmat`.

**(3.12) [uv:eq:sampling].** The ratio form uses the exponent D + 1 for both counts where (3.12) [uv:eq:sampling] uses D + 2. Both close.

### 2.3 Nine statements compared in detail

**Lemma 5.2 [fo:lem:deterministic].** Lean statements: `primLoop_sharp`, `primLoop_bdd`, `primLoop_bdd_tail` (case (a)); `primLoop_large'`, `primLoop_large_tail'` (case (b)). Lean is at least as strong. In case (a), `primLoop_sharp` gives ‖𝒦_k‖ ≤ C′ζ_t^{k−1} for 0 < g ≤ C, L ≥ L₀, W ≥ 1, all 0 ≤ t < 1, with no condition log W ≪ L ≤ W² and no condition 1 − t ≥ W⁻³; `primLoop_bdd` is the same with the extra factor (1 + g⁻²)^{k−2}. In case (b), `primLoop_large'` has one C_κ ≥ 1 before k, as the paper says, and C_* = C_\*(κ, k), with no upper bound on g or L. The tails (5.21) [fo:eq:primitive-tail] are `primLoop_bdd_tail` (0 ≤ g ≤ C, L ≥ L₀) and `primLoop_large_tail'`, the latter under L ≥ C_* g² log W with C_* depending on ε, Q, k, which is stronger than the rate form L ≫ g² log W.

**Proposition 8.2 [up:prop:fr-concentration].** Lean statement: `frac_criterion`. It uses one constant C₀ for the polynomial range g ≤ W^{C₀} and for the length n ≤ C₀𝔟 log W. It gives the paper's statement with C₀ := max{C₀, C₁}, and the output constants depend on that maximum and s, which the paper allows. Lean is stronger otherwise: J is any set, there is no E₀, no upper bound on 𝔟, and C, c, W₀ do not depend on n. The hypothesis `EndpointMomentAt` is (8.6) [uv:eq:upper-volume-input], with Hermitian shifts L₀, R₀ and no norm restriction; the output is `FracPath` on every path and `FracCycle` on every cycle with L ≥ 3, at q = s/2. The composition with Lemma 8.1(i) in the last sentence of the proposition is the separate theorem `frac_tail_of_transfer`.

**Proposition 8.4 [up:prop:conversion].** Lean statements: `frac_local_of_growth` for (i), `frac_avg_of_negative_moment` for (ii); the core is `endpointMoment_of_transferInput`. For (i): J is any set, 𝔟 and E₀ do not occur, the length condition is only 1 ≤ n (the paper's 2 log W ≤ n₀ is not needed), and the implication holds at each single point (W, g, J, n), with W₀ depending only on (C₀, t). The exponent is existential, with witness `endpointExponent`; since the input (8.11) [up:eq:input] at a larger exponent implies it at a smaller one, this covers "a sufficiently large fixed D′". `TransferInputAt` is (8.11) [up:eq:input] with both suprema outside the probability. For (ii): the implication holds at fixed (W, g), E₀ > 0 is dropped, q = s/4 and C′ = 2, c′ = c/4; `NegTransfer` is (8.12) [up:eq:negative-transfer-input]. A form with q = s/2 and a general measurable J₀ is `green_path_of_transfer`.

**Lemma 9.3 [su:lem:chosen-generator].** Lean statements: `chosen_generator_weak`, `chosen_generator_crit`, through the predicates `ChosenGenerator`, `GenPoint`, `GenFamily`. **One bound is weaker,** so the Lean statement does not imply the final one: the bound ‖K‖²_HS ≤ 32 of (9.25) [su:eq:pair-generator-size] is ‖K‖²_HS ≤ C with C existential, and every use in the library needs only a constant. The family K̂ and the cutoff χ̂ are existential functions of (R₄, ω, v̂), with the properties of the lemma as clauses; the K of the construction and its source-coordinate formula are not exported. Two more clauses differ from the printed text. "Smooth near the support of χ̂" is C² on an open set containing `tsupport`. The regularity needed for integration by parts is written out (joint measurability, bounded active support, invertibility of the chain on the support). In regime (i) the conclusion is stated for ε ≤ ε₀; `AngularFieldAt` is monotone in C𝔟 (`angularFieldAt_mono`), and the proof of Lemma 8.12 [up:lem:small-contraction] (i) uses this for ε > ε₀. The source cutoff contains the factor in W²⁰‖Pv̂‖²/‖v̂‖² of the paper, with constants 2W²⁰ on the support and W²⁰ on the plateau (`srcCut`, `srcCutV`, `srcCut_tsupport`, `srcCut_eq_one`). The regime (ii) rows of `levels_crit` carry that factor, so the intermediate bounds there are weaker by a power of W than the regime (ii) lines of (9.70) [su:eq:error] and (9.77) [su:eq:normalization-derivative-bound]; they still give the boundedness that the proof uses.

**Lemma 11.5 [up:lem:center-transfer].** Lean statement: `center_transfer`. It has a general exponent B_g in W^ε ≤ g < W^{B_g}; the paper is B_g = 1 with ε < 1. The order of constants is ∃ κ₁, ∃ C₁⁰, ∀ C₁ ≥ C₁⁰, ∃ W₀, which is the paper's "any sufficiently large fixed C₁". Lean is stronger.

**Lemma 11.6 [lg:lem:fluctuations].** No Lean statement; see part 4.5. `scalar_growth` proves Lemma 11.10 [lg:lem:scalar-growth] without it.

**Lemma 11.8 [lg:lem:dynamic].** The label is cited in several files as parts of a proof; the lemma is split. Lean statements: `corrObs_form` (form of the polynomial corrections), `corrCoeff_bounded` (finitely many monomials, bounded coefficients), `corrObs_stability` (the event (11.44) [lg:eq:burnevent]), `center_zero_odd_neg` (a_{2j+1} = 0 and a_{−k} = conj a_k), `center_bounds` (`LSBA/Upper/CenterNewton.lean`; for the centers a_k = `center` on a finite index set, ‖a_k‖ ≤ K and |a₂| < 1/4 + K/g², for g ≥ g₀ and |E| ≤ E₁). The integer R is a parameter fixed before the indices, as in the paper. The polynomials are defined objects independent of η, D, B₁; the energy window |E| ≤ E₁ replaces |θ| ≤ δ and comes after (D, η, B₁), as in the paper. `corrObs_stability` has 0 < ε, B₁ > 0 and no upper bound g < W, and holds on `μ W N` for every N ≤ W^{B₁}.

**Lemma B.10 [b:lem:early-primitive].** Lean statements: `primLoop_early` for (a), `primLoopF_freeLabel'` for (b). Lean is stronger: (a) holds for 0 ≤ g ≤ C, L ≥ L₀, W ≥ 1, without the volume condition; (b) is stated for the W-free function 𝔉_k with 𝒦_k = W^{1−k}𝔉_k, under g ≥ C_κ, L ≥ C_* g² only, with no upper bound on g or L and no threshold in W.

**Lemma G.1 [us:lem:local-law].** Lean statements: `localLaw_avg`, `localLaw_iso`, `localLaw_entry`, `localLaw_rel`, `localLaw_avg_asymp`. They are in dimension n with entry variance 1/n, and the energy is placed in the spectral parameter: G = (V − B − z)⁻¹ with z = E + iη, and M = `MB` at z. ≺ is written at each deterministic (B, E, η, u, v) as a bound n^{-D} on the bad event, with exponents ξ, D. The class is `DeformClass`, with B Hermitian and no norm bound: ‖B‖ ≤ W^K is not needed. **One bound is weaker:** the averaged law `localLaw_avg` has rate (Wη)^{-1/2}, not (Wη)^{-1}. Every use in the proof needs only ≍ or the rate (Wη)^{-1/2}. `localLaw_rel` puts the ratio bound and the two-sided comparison of (G.2) [us:eq:relative-local-law] into one event. As in the paper, the event depends on the vector.

### 2.4 Results of Section 2 and Section 4

- Lemma 2.1 [thm:orbital]: `haar_count_le` gives (2.2) [eq:haar-count] in the basis-free form, with c₀ = 1/8, c = 1/25, every W, L, real g, measurable J and threshold r ≤ W/8. (2.3) [eq:orbital-length] has no Lean statement (part 4.5). `haar_region_count`, `haar_short_cycle_count` give (2.12) [uv:eq:lower-regions-output] on the region (2.4) [uv:eq:haar-lower-region] and for L < L₀, for every measurable J, every real g, every τ > 0.
- Theorem 2.2 [uv:lem:lower-volume]: `lower_volume` takes a closed interval [c, d], possibly empty, and W₀ comes after E₀, D, τ, ν, p, C_p and before W, L, g, c, d. The moment hypothesis is stated for the given instance, so no threshold in it appears. The case J = ℝ of (2.12) [uv:eq:lower-regions-output] is not part of it.
- Theorem 2.3 [thm:bounded-lower]: `small_lower_fdist`, in the uniform form the paper states, with an `Integrable` conjunct.
- Lemma 2.4 [uv:lem:short-spreading]: `short_spreading` has C_κ before ∀ L₀ and the other constants after it (J depends on L₀), with separate constants C, c.
- Theorem 2.5 [uvu:thm:terminal]: `large_lower`, in the uniform form, with an `Integrable` conjunct.
- Theorem 4.1 [uv:thm:smooth-cutoff]: `im_resolvent_window_comparison`. The Loewner order is written as a quadratic form for each u; the window is renumbered `Fin (2R+1)` with center `windowCenter`; C = 3; η > 0 and R ≥ 1 are explicit.
- Lemma 4.2 [uv:lem:poisson]: `poisson_smoothing`, `poisson_smoothing_matrix`. J = [c, d] is closed and the measure has finitely many atoms. Both uses of the paper are of this form.

### 2.5 Section 5: loops and propagation

All statements of Sections 5 and 7 that have a supremum over time inside the probability are fixed-time statements in Lean; see part 4.1.

- Lemma 5.1 [fo:lem:mixed-ward]: `loopTr_ward` for every Hermitian H and Im z > 0, `primF_ward`, `primLoop_ward`. Only the first and last positions are stated; any vertex follows by rotation (`primLoop_rotate`).
- Lemma 5.2 [fo:lem:deterministic]: part 2.3.
- Lemma 5.3 [fo:lem:bounded-initial]: `initBdd`, `boundedInitial_packet`, `boundedInitial_avg`, `boundedInitial_entry`, `boundedInitial_loop`, `boundedInitial_loopError`, `boundedInitial_pair`, `boundedInitial_tail`, componentwise at each u ∈ [0, 1/2], for 0 < g ≤ C, 3 ≤ L ≤ W².
- Lemma 5.4 [uvc:lem:orbital-limit]: `orbital_limit` is stated for 𝔉_k at fixed time with noise √t·GUE, uniformly on [0, T] in an ε–N form, for each fixed (g, L, E, T).
- Lemma 5.5 [fo:lem:resolvent-moments]: `resolvent_moments`, `resolvent_moments_Hmat`, `resolvent_moments_vert`. It is for each fixed t, with W ≥ 4p, g ≥ 2/√κ explicit and any 0 < κ.
- Lemma 5.6 [fo:prop:inputs]: `lemma46_fixedTime`, `lemma46_avg`, `lemma46_entry`, `lemma46_loop`, `lemma46_err`, `lemma46_pair`, `lemma46_tail`, `initLarge`, each at fixed time, and with any volume constant C_V > 0.
- Definition 5.7 [def:cells-anchors]: `cellStart`, `cellLen`, `cellLen_bounds`. Cells are [jn, (j+1)n) ∩ [0, L); only the last can be shorter. The proofs use adjacency, length ≤ n and the count.
- Lemma 5.8 [uvc:thm:ordinary-sampling]: `loop_sampling`, `loop_sampling'`, at fixed time, with sample sets independent of time. `loop_sampling` has the extra hypothesis C_κ ≤ g. In `loop_sampling'` the exponent B depends only on the lower bound exponent, and the failure exponent is chosen after B, which is stronger.
- Lemma 5.9 [gc:lem:residual]: `AveragingInput` at admissible pairs, all with u ≥ 1/2, through `averagingInput_bdd`, `averagingInput_large`, `averagingInput_of_rows`. Early times enter through Lemma 5.3 [fo:lem:bounded-initial] and Lemma 5.6 [fo:prop:inputs] (`boundedInitial_packet`, `vert_moments`).
- Lemma 5.10 [fo:lem:sampling-continuity]: `CrudeInput`, `SamplingInput`, `pair_sampling`, `precMax_of_sampleMoment`. Moments are for every p ≥ 1. One sample set serves all signs and all fields. The time increments of the paper are replaced by moment recursions (part 4.1).
- Lemma 5.11 [fo:lem:families]: `lemma411`, `flow_cmp_samplewise`. The comparison holds sample by sample, H_s(g′) = ξH_u(g), with no coupling of laws, for nested chains (`cmpChain`). Lean is stronger.
- Theorem 5.12 [gc:thm:common]: `theorem412_one`, `theorem412_iter`, `theorem412_small`, `theorem412_large`. It is proved for a general regime (`PropRegime`) with inputs (`PropInputs`), and the two named cases are instances. It is a fixed-time statement. Case (a) holds for any positive lower rate g ≥ g_min(W), with no g ≥ W^{−o(1)}. **Weaker uniformity:** θ_* and c_p* come after the regime parameters, while the paper has θ_* = θ_\*(c₀); the proof gives θ_* = 2^{−J−1}, and every use applies it as stated.
- Lemma 5.13 [fo:lem:terminal-deterministic]: `terminal_bdd_regular`, `terminal_large_anchor`, `mDysonLBdry_norm_le`.
- Lemma 5.14 [fo:lem:bounded-terminal-matching]: `terminal_match_bdd`. The matching is an identity for each sample, with explicit bounds. Lean is stronger.

### 2.6 Section 6: deterministic parameters

- Lemma 6.1 [da:lem:scales-propagators]: `scalesProp_bdd` for all 0 ≤ u < 1 with no remainder, `scalesProp_large` for all 1 − u ≥ W⁻³. The paper has 1/2 ≤ s ≤ u ≤ t. "c ≤ Im m" in the bounded case is a hypothesis.
- Lemma 6.2 [da:lem:scale-budgets]: `weight_comparison`, `weight_convolution`, `weightFn`, `scale_facts`. Stated for an abstract scale ℓ, and for 0 < θ ≤ 1.
- Lemma 6.3 [da:lem:comparison-parameters]: `cmpParams_bdd`, `cmpParams_large`, `cmpChain_bdd`, `cmpChain_large`, `cmpReach_bdd`, `cmpReach_large`, `cmpReach_chain`. The clauses are stated separately. "Interspersed with movement to earlier times" is a nesting condition on the chain.
- Lemma 6.4 [da:lem:positive-height]: `positiveHeight_bdd`, `positiveHeight_large`, `segRows_bdd`, `segRows_large`. The large-coupling form is on the direct region, which contains the comparison segments.
- Lemma 6.5 [da:lem:free-interpolation]: `free_interpolation`, `rowInterp_dyson`, `transferT_pow_le`, for general w with |w − E| ≤ C/g² and general m. "Norm bounded uniformly" is the explicit bound 1/sin ϑ. The second-coordinate interpolation follows from Mᵀ = M.
- Lemma 6.6 [da:lem:regular-dyson-profile]: no Lean statement (part 4.5).

### 2.7 Section 7: transfer matrices and sampling

- Definition 7.1 [def:transfer-matrices]: `transferMat`, `transferProd`, `freeConj`, `freeRot`, `freeShear`, `freeAngle`. The matrix inverses are Lean's. The algebraic identities (`transferMat_mul_transferInv`, `inv_transferMat`) hold for all real g, complex V, real η. Lean keeps 2 cos ϑ = E where the paper has E = 2 sin θ, ϑ = π/2 − θ; the coefficients agree. B_E and X_j, which the paper only asserts to exist, are explicit.
- Lemma 7.2 [uvs:lem:transfer-moments]: `transfer_moments`, `one_step_moment_inv`. Constants are uniform after C₀, C₁; |η| ≤ 1 and n|η| ≤ C₁; the blocks are any injective sequence (`Set.InjOn`); there is an `Integrable` conjunct.
- Lemma 7.3 [uvc:lem:weighted-ward]: `weighted_ward`, `weighted_ward_identity`, for any Hermitian blocks and L ≥ 3.
- Proposition 7.4 [uvc:prop:green]: `green_interp`, `green_interp_hs`, at fixed time. The constants are explicit: 16/κ + 4, 2 + 4/κ.
- Lemma 7.5 [uvc:lem:space]: `loopSpace`, `finrank_loopSpace_le`, `loopTr_dist_space`. The space is spanned by products of six edge functions on k edges, with d_k = 6^k. Only the upper bound on the dimension is stated.
- Lemma 7.6 [uvc:lem:fekete]: `fekete_norming`. Infima over the space are replaced by bounds for every v, v′ in it, and d₀ ≥ 1 is dropped.
- Lemma 7.7 [uvc:lem:cells]: `cells_prefix`, at fixed time, with the event `CellClose` and L ≤ g²W^C explicit.
- Corollary 7.8 [uvc:cor:weighted-sampling]: `loop_sampling`, `swInput_of_large`, at fixed time, for any weight scale ℓ ≥ g².
- Remark 7.9: no statement.
- Proposition 7.10 [uvc:prop:residual-compression]: `segRes_identity`, `residual_interp`, `pair_sampling`. The compression is a deterministic statement about the combination `resComb`. `pair_sampling` assumes 4g² ≤ L ≤ g²W^C.

### 2.8 Section 8: the upper bound reduction

- Lemma 8.1(i): `frac_concentration_fixed`. The hypothesis is needed only on the one cycle at the given parameters (`FracCycle`), which is stronger than uniformity over paths and cycles. J is any measurable subset of [−E₀, E₀]. A and D are independent. The radius is the ceiling ⌈C_D 𝔟 log W⌉ of the proof, equivalent to (8.4) [uva:eq:conversion-radius] with C_D + 1. The sentence "In particular" is not stated separately.
- Lemma 8.1(ii): `frac_concentration_averaged`. It is at fixed (W, g), for every L, with E₀ > 0 dropped, A and D independent, and R without a ceiling. The sentence "In particular" is not stated separately.
- Proposition 8.2 [up:prop:fr-concentration], Proposition 8.4 [up:prop:conversion]: part 2.3.
- (8.7) [eq:c-apriori]: `resolvent_block_moment_le`, for any deterministic Hermitian K₀ and scale c > 0, with C_p explicit; `pathOp_moment_le`, `Hmat_moment_le` are the path and cycle cases. The display is the same.
- Definition 8.3 [def:boundary-frames]: `IsBoundaryFrame`, `frameD`. `frameD` is defined for every matrix and every frame, and `frameD_spec` holds for every J_ph-isometry.
- Definition 8.5 [up:def:transfer-operator]: `batchMat`, `halfOp`, `volCocycle`, `IsoFlag`. The operator P_{1/2} is an expectation over q input blocks, for all real g, E and all q ≥ 0. Flags are encoded by the pair of orthogonal projections (P_U, P_Y) with their Borel σ-algebra. The action and the cocycle are defined for every J-unitary T.
- Lemma 8.6 [up:lem:operator-reduction]: `frameD_moment_le` for **all** n, `transferInputAt_of_powerDecay` with n₀ = ⌈C𝔟 log W⌉, which need not be a multiple of q, and with 2 log W ≤ n₀ as a conclusion. `transferLength_of_contraction` only gives some 1 ≤ n ≤ C𝔟 log W, which is the form the chain uses; it is weaker than (8.22) [up:eq:transfer-length] in that it does not name n₀. Neither 𝔟 ≤ W^{B_b} nor measurability of J is assumed. The constants are explicit.
- Definition 8.7 [up:def:isotropic-group]: `isoGroup`, with `mem_lieOmega_iff` for the algebra.
- Definition 8.8 [up:def:angular-norm]: `AngL4Le`, `AngContractionAt`, predicates with the supremum over all circles.
- Lemma 8.9 [up:lem:good-bad]: `GoodBadSplitAt`, `GoodBadSplit`, `good_bad_split`, `goodBadSplitAt_of_cutoff`. This is an operator form. There is no Haar density f, no decomposition of dT, and the pushforward sentence is absent. The decomposition is a cutoff of the GUE inputs, and (8.27) [up:eq:coarse-density] becomes a bound on the support. Every use reads only the operator bounds.
- Lemma 8.10 [up:lem:operator-iteration]: `iterate_halfOp_one_le`, `powerDecay_of_contraction`. (8.32) [cc:eq:pointwise] is ‖P^k 1‖ ≤ (1 + 4K)ρ^k. At ρ = 3/4 this is the paper's bound; for other ρ it is weaker and still gives (8.21) [up:eq:power-input]. The same c as in (8.30) [up:eq:P-contraction] is kept.
- Lemma 8.11 [up:lem:angular]: `angContractionAt_of_field`, `angContractionAllAt_of_field_zero`, through `AngularFieldAt`, `AngularFieldZeroAt`, `IBPAdmissible`. The conditions on the field are line derivatives in projection coordinates, required only where χ ≠ 0. The case K_out = 0 has its own predicates.
- Lemma 8.12 [up:lem:small-contraction]: `small_contraction_weak`, `small_contraction_crit`. The conclusion is `AngularFieldAt`, with q ≥ 7 written out. Regime (ii) does not need the lower bound c_*W^{−1/2} ≤ g in the geometric part (`overlap_crit`, `cutPlat_crit`). `weak_length_of_contraction` writes the step from g = W^{−a} to the whole range W^{−β} ≤ g ≤ W^{−α}.
- Lemma 8.13 [up:lem:density-contraction]: `density_contraction`. The items (i), (ii) form one theorem with one constant and one cutoff for each W. Item (ii) holds for every E ≠ 0 with constant C(1 + |E|⁻¹)², and the window form follows. Lean is stronger.

### 2.9 Sections 9 and 10: vector fields

- Lemma 9.1 [su:lem:preparation]: `preparation_weak`, `preparation_crit`, `ae_prepOK`, `isPrepChart_of_prepOK`, `prepInd_spec`. Regime (i) holds for all ε > 0, with C, W₀ independent of q ≥ 4. The coordinates enter by explicit extraction. `[NeZero W]` is explicit.
- Lemma 9.2 [su:lem:field-geometry]: `field_geometry`, `smallField_motion`, `smallField_isHermitian`. No condition on V_q is needed: the last line of (9.13) [us:eq:orbit] is stated for M_q = V_q − E − g²R_{q−1}, as in the paper. `smallField_isHermitian` holds for all Hermitian R, all real g, E, all q.
- Lemma 9.3 [su:lem:chosen-generator]: part 2.3.
- Lemma 9.4 [us:lem:score]: `score_bound`, `lintegral_gaussDiv_smallScore_le`, `active_gaussDiv_eq`, `rotFrame_chain`. It is at a fixed preparation on `μ W q`, with terms as lower integrals. The divergence is expanded in a tight frame, not an orthonormal basis.
- Lemma 9.5 [us:lem:range]: `invImage_relative_le`. Q₀ is any orthogonal projection commuting with B₀; the failure probability is W^{-D} + Ce^{−cd}.
- Lemma 9.6 [us:lem:self]: `gaussProj_overlap_le`, with the spectral input as the hypothesis `InvSpecInput`, for every A > 0; n ≤ W is any size. The output is a vector bound.
- Corollary 9.7 [nc:lem:compression]: `invImage_overlap_le`, for any vector v; the small part of B need not be Hermitian.
- Lemma 10.1 [lem:c-gaussian-lift]: `gaussian_lift_general`, `gaussian_lift_away`, `gaussian_lift_general_batch`, `IsCutLift`. It is stated for a given cutoff satisfying the coercivity conditions, for each g > 0. For 0 < |E| ≤ E₀ the constant is explicit in |E|. Lean's M₀ is constructed (`flagDir`), not chosen. Indices are shifted: input k of `Fin q` is the paper's k + 1.
- Displays of Section 10 are stated in squared Frobenius form, or in standard coordinates, for every M; the constants are explicit (`cutField_divergence_le`, `hermBasis_completeness`).

### 2.10 Section 11: large coupling

- Theorem 11.1 [uvg:thm:transfer]: `negative_transfer_moment`, for a deterministic frame Φ; a random frame is handled by the user through Fubini. Its proof uses `norm_inv_rpow_le_sum`.
- Lemma 11.2 [uvg:lem:drifts]: `large_drifts`, `innovation_var`, for every g ≥ 1 and W ≥ 1, with variance bounds in unit-variance coordinates.
- Lemma 11.3 [uvg:lem:positive]: `large_positive`, in two parts: the bound on 𝒬 and (11.23) [uvg:eq:positive]. The statement asserts the existence of K, for all g ≥ 1 (the proof gives K explicitly in A, B, E₀), and its conclusion includes `1 ≤ Cs`, so C_* ≥ 1 is part of what is proved, not an extra hypothesis. **Not formalized:** the last sentence of the lemma, that on {‖V‖ ≤ c₀g} the derivative in V of c − 𝒬(C′, v′) is at most C/g in Hilbert–Schmidt norm. The Lean proof of Lemma 11.4 does not use it (part 4.7).
- Lemma 11.4 [uvg:lem:mgf]: `large_mgf`, which also asserts s < 1; `large_scalar_fraction` for (11.24) [uvg:eq:scalarfraction]. The proof takes a different route (part 4.7).
- Lemma 11.5 [up:lem:center-transfer]: part 2.3.
- Lemma 11.7 [lg:lem:ideal]: `wickMap`, `obsIdeal`, `wickMap_mem_obsIdeal`, `wickMap_traceVars`, `transOp_obsEval_sub_le`. The coefficients are a defined map on polynomials, independent of θ, g, W, E₀, and the statement holds for every g ≥ 1, W ≥ 1, |E| ≤ E₀ < 2.
- Lemma 11.8 [lg:lem:dynamic]: part 2.3. The moment recursion (11.59) [lg:eq:momentrec] is `moment_contraction_corrObs`, with J closed under lower indices as in the paper, in a conditional form at each state; (11.60) [lg:eq:momentout] is `moment_bound_corrObs`, for every k ∈ J, every W ≥ 1, g ≥ g₀. `parityPart_corrUpd` omits the sentence that p(M) contains only M_j factors; it is not used.
- Lemma 11.9 [lg:lem:centerQ]: `center_corrector`, with general B_g, B₁ > 1 + 2B_g; `corrQ_bounds` for the bounds (11.28) [lg:eq:Q-regularity], written as a Lipschitz bound on states. Part (ii) is split into a deterministic drift bound on a good set `corrGood` and the event bound. `corrector_drift` is (11.70) [lg:eq:smalldefect] for all g ≥ W^ε, with no upper bound on g.
- Lemma 11.10 [lg:lem:scalar-growth]: `scalar_growth`, with general B_g; the length is an argument n with n = ⌈C₁Wg² log W⌉₊. Lean is stronger.

### 2.11 Appendix A

- Lemma A.1 [da:lem:free-green]: `freeS_sq`, `freeT_eq`, `norm_freeRho_lt_one`, `freeRowCycle_eq`, for every real b. The ℤ row is a recurrence.
- Lemma A.2 [bl:lem:regular]: `regular_quantile`, `mDyson_deriv_le`, `bandEdge`. The quantile form is at γ = γ_g, with one more conjunct |x| + b ≤ e_g. Only the first z-derivative is stated; the g-derivative and mixed derivatives are not formalized.
- Lemma A.3 [bl:lem:finite]: `finite_regular_point`, `finite_regular_quantile`, `finiteRoot_of_lineRoot`. The case j = r = 0 at γ = γ_g, and the local form in a family (b, β). Derivative bounds of m_{g,L} − m_g are not formalized.
- Lemma A.4 [uvp:prop:finite]: `large_periodic_comparison`, `perP0`, with constants uniform in |E| ≤ 2 − κ. Lemma A.4 [uvp:prop:finite] is stated at c′ = c/2 in its row bound; other c′ < c follow by summation.
- Lemma A.5 [ba:lem:kernels]: `bdd_kernels`, `bdd_symbol`, `kernel_small_rows`. Row identities come from `pairP_row_sum`, `mixedKer_nonneg_row`.
- Lemma A.6 [da:lem:line-kernel]: `geom_bounds`, `lamGeo`, `lineKer`. Only the periodized bounds the proofs use are stated; the Fourier identities, the case g = 0 and the size of D_g are not formalized.
- Lemma A.7 [da:lem:transport-refinements]: `bdd_gradient`. **Weaker uniformity:** the rate c and C′ come after B_L and j, while the paper's c is that of Lemma A.5 [ba:lem:kernels]. The uses are at fixed j, B_L. The display (A.30) [da:eq:stable-spatial-moments] is given in a stronger form by `kernel_small_rows` (Lemma A.5): the exponentially weighted off-diagonal row sum is at most C′g².
- Lemma A.8 [uvp:lem:geom]: `geom_bounds`, periodized, for a ≤ L.
- Lemma A.9 [uvp:lem:perturb]: `kernel_perturb`, for any symmetric stochastic P₀ and stochastic P₁.
- Lemma A.10 [uvp:lem:actual-kernels]: `large_actual_kernels`, `increment_large`, `kernel_accuracy`. Row identities are not repeated; only forward differences are stated.
- Lemma A.11 [da:lem:stopped-pair-weights]: no single declaration. (A.52) [da:eq:short-weight] and the propagation are covered by `weightFn`, `weight_comparison`, `weight_convolution`, with an abstract scale, used inside the propagation proofs.
- Lemma A.12 [da:lem:profile-improvement]: `profile_minimum`, with the condition W ≥ 3 written out. The improvement step is `step5`. The first display, (A.55) [gc:eq:ratios], has no separate public statement.
- Lemma A.15 [da:lem:early-pair-inverses]: `early_inverse_abstract`, an abstract Neumann statement with constant 8.
- Lemma A.17 [da:lem:rough-stability]: `rough_stability`, `freeTL_sub_freeT`, with `freeTL_sub_freeT` for every L ≥ 1.
- Lemma A.18 [fo:lem:matching]: `terminal_match_large`, packaged with the root, Im m and norm clauses of Lemma 5.13 [fo:lem:terminal-deterministic]; the matching holds for each sample.
- Lemma A.21 [da:lem:deformed], Lemma A.22 [da:lem:deformed-stability]: `deformed_profile`, `deformed_residual_stability`, `deformed_vector_weight`, `deformed_scalar_stability`, `norm_mB_sub_mB_le`. They hold for all finite index types, with constants independent of the dimension. The energy is in the spectral parameter. The class `DeformClass` allows non-Hermitian parts B_s, B_b of a Hermitian B.
- Lemma A.13 [ll:lem:deterministic], Lemma A.14 [da:lem:polynomial-derivatives], Corollary A.16 [da:cor:remainder-derivatives], Lemma A.19 [da:lem:polynomial-terminal], Lemma A.20 [da:lem:polynomial-parameters]: no Lean statement (part 4.5).

### 2.12 Appendix B

- Lemma B.1 [ba:lem:moment]: `stableMol_bdd` for 0 ≤ t ≤ 1, `stableMol_bdd_cancel`, `stableMol_small_cancel` for 0 ≤ t < 1. The moments are for integer r only, which is equivalent.
- Proposition B.2 [ba:prop:primitive]: `primLoop_sharp`, `primLoopF_bdd_weighted`. The bound is sharp and uniform on 0 < g ≤ C.
- Proposition B.3 [ll:prop:primitive]: no Lean statement (part 4.5).
- Lemma B.4 [uvp:lem:anchor]: `uvp_anchor`. **Stronger hypothesis:** the convolution hypothesis has weight c/(k−1), where the paper derives this from c by annuli. All callers supply it.
- Lemma B.5 [uvp:lem:taylor]: no public statement. The bound is an internal step of `LSBA/Primitive/Uniform.lean`.
- Theorem B.6 [uvp:thm:molecule]: `uvp_molecule`, for every k ≥ 3, for any molecule and each mixed leg.
- Theorem B.7 [uvp:thm:tree]: no public statement. The induction on the length is an internal step of `LSBA/Primitive/Large.lean`.
- Proposition B.8 [uvp:prop:cores]: `stableMol_large'`. The core hypotheses are proved directly at a = g² for g ≥ C_κ, L ≥ Rg², with no condition in W.
- Corollary B.9 [uvp:cor:joint-tail]: `primLoopF_large_weighted`, `primLoop_large_tail'`.
- Lemma B.10 [b:lem:early-primitive]: part 2.3.
- Lemma B.11 [b:lem:primitive-pair]: `primLoop_longPair`, `primLoop_longPair_large'`.

### 2.13 Appendices C, D, E

- The displays of Appendix C are proved at fixed time; see part 4.1. Those identities that are pointwise are stated for each Hermitian matrix: `blockGen_loopTr`, `blockGen_propagated`, `blockGen_projField`.
- Appendix D: the mean and the bias are bounded with explicit constants (`trN_resolvent_Hmat_dev`, `Hmat_trace_sq_tail`). The common unitary conjugation of Appendix D.1 [subsec:pf_thm31] is the two statements `gueBlock_conjMap`, `measurePreserving_conjMap`, stronger than equality of laws. Uniform vectors on the sphere are the law of a normalized Gaussian (`map_haarU_mulVec`).
- Appendix E: (E.6) [uva:eq:average] holds for every r ≥ 0 in `cell_average`, and the input (E.14) [eq:c-interval] is any measurable J ⊆ [−E₀, E₀]. The bounds (E.12), (E.13) hold for all r, h (`transferWeight_sup_le`, `transferWeight_moment`). The correlator bounds are `blockCorr_decay`, `averagedTail_le_of_blockCorr`, `cell_correlator_of_path`, `averaged_tail_of_correlator`. The spectral-averaging display (E.7) is an inequality: `lintegral_eigMassSum_rankOnePert_le` gives "≤", not the identity, which is all the proof uses. (E.15) [eq:c-cycle-Schur] and (E.16) [eq:c-cycle] are `cycle_schur'`, `cycle_moment_of_path`, `frac_cycle_of_path`, for every path exponent p ∈ (0, 1) and all g ≥ 0.

### 2.14 Appendices F and G

- Lemma F.1 [cc:lem:quotient]: `quotProj_spec`, `exists_isCircleBasis`, `exp_two_mul_volCocycle_circlePair`, `volCocycle_mul`, for all J-unitary T, with 1 ≤ W explicit. `logVol` is defined on all matrices.
- Lemma F.2 [cc:lem:cofactor]: `exp_neg_volCocycle_omitPair`, `norm_frameD_inv_rpow_le`. (F.4) [cc:eq:inverse] holds for 0 < s ≤ 2.
- Lemma F.3 [lem:c-operators]: `abs_integral_goodPart_le`, `abs_integral_circleDeriv_le`. This is the lifted form: the hypothesis on ‖X_M f‖₁ becomes a bound on the divergence of the lifted field; the bound is linear in A₀.
- Lemma G.1 [us:lem:local-law]: part 2.3.
- Lemma G.2 [us:lem:product]: `product_moment`, from a fixed regular R on `Ω W h`, with failure C(W^{−δ₀} + g^{1/2}) and no lower bound on g.
- Lemma G.3 [nc:lem:buffer]: `buffer_lower`, `buffer_lower_eta` (any η with g² ≤ η), `output_lower_weak`, `output_lower_crit`. The display (9.68) [us:eq:profile] is stated only at j = q − 1 and only for the lower half, at fixed preparation data, which is the part used.
- Lemma G.4 [lem:c-gaussian]: `coercivity_cutoff`, `coerMin_lt_prob_le`, `coerMin_le`, with quantification over the input tuples through an orthogonal layout (`layoutBlocks`). The margins are absolute constants, and c, C, W₀ are uniform over the layouts of a given length.

### 2.15 Displays and auxiliary statements

Dyson equations and characteristics:

- (5.2) [fo:eq:dyson-family]: `mDysonL` is the unique solution in ℂ₊. The boundary value `mDysonLBdry` exists for every real E and every L ≥ 1 (`mDysonLBdry_tendsto`). `IsDysonRootV` and `mRootV` cover every hopping and variance, with uniqueness `isDysonRootV_unique` also on the real axis. `primData_of_root` packs the characteristic data into `PrimData`.
- (5.1) [fo:eq:flow], (5.3) [fo:eq:characteristic]: `flowH_isHermitian`, `etaChar_pos`, `norm_resolvent_zChar_le`, for every u < 1 and every Hermitian matrix.

Loops and primitive loops:

- Notation of Section 5.2 [sec:fo-loops]: `loopTr` with positions `Fin k`, signs `Bool`, and the trace identities `loopTr_rotate`, `star_loopTr`.
- (5.17) [fo:eq:error-hierarchy]: `cutSrcLin` is defined for each k and is 0 for k ≤ 2; `cutErr_split` includes k = 2. (5.9) [gc:eq:bracket]: `blockGamma_loopTr` allows two loops of different lengths.
- (B.1) [ba:eq:dissection]: `dissCore`, `dissVal` are in physical space; the paper uses Fourier multipliers. The two agree by the cyclic symmetry of M_B.
- (5.10) [fo:eq:primitive]: `primF`, with uniqueness requiring continuity on [0, T), since the Lean clause is a one-sided derivative. (5.14) [fo:eq:generator], (5.16) [fo:eq:duhamel]: `primF_generator`, `primF_duhamel`, for k ≥ 3.
- (B.9) [uvp:eq:mass]: `UvpCore` has the mass bound at each anchor; this is equivalent under translation invariance.
- (C.34) [gc:eq:row]: `loopErr_rowSum_ward`, for any Hermitian M and non-alternating middle signs.
- (A.74) [fo:eq:projected-propagation]: the zero-row tensors are restored by a uniform profile on the scale ℓ_u (`restore_zeroRow`, `restore_stableLeg`).

Sections 7 and 8:

- (7.5) [uvs:eq:pathwise-green-block]: `norm_blockOf_resolvent_le`, for every real E; `blockFlow_Ag_eq_Hdet`, for every real t.
- (7.26) [gc:eq:residual-fixed-moment]: `residual_moment`, `residual_moment_entries`, with any K ≥ 1 and an `Integrable` conjunct; `vert_moments` for every integer p ≥ 1.
- (7.7) [uv:eq:seed-exponential-tail]: `badCount_le_heavy_integral` assumes simple spectrum, which holds almost surely.
- (3.6) [eq:averaged-tail] to ℓ: `badCountUp_le_tailCount` has the explicit conditions W^{−a} ≤ 1/2, R ≥ 0, in place of "for large W", and assumes simple spectrum.
- `blockCorr`, `eigMassSum` are defined through the eigenbasis and agree with the paper's quantities on simple spectrum. `eigMassCorr_le_sqrt_card` holds for any coordinate sets.
- (8.18) [up:eq:transfer-batches]: the batches are not a sequence; independence enters through `measurePreserving_blockAppend` and `batchMat_add`.
- (8.36) [cc:eq:jac]: the change of variables `lintegral_circleMeasure_flagAct`, not a density ratio. The circle measure is the image of the parameter under a rotation in closed form (`circleRot`, `circleMeasure_eq_map`, `circleMeasure_eq_map_circleRot`), with no measurable choice of frames.
- (8.25) [up:eq:invariant-function]: `halfOp_isSimulInvariant`, and the semigroup law `halfOp_mul_eq_iterate`, which the paper uses without listing them.

Section 9:

- Section 9.1 [su:sec:construction]: the chart is `IsPrepChart`, with `IsUnit` hypotheses wherever an inverse is used. `smallField` is (9.10) [us:eq:physical] without the cutoff, which is applied later.
- (9.29) [su:eq:pair-source-derivative-sum]: `srcEnergy`, `tangGradSq`, `tangProj`, in a basis-free form with squared norms.
- (9.20) [us:eq:sourceenergy]: `smallGen_bounds`, `srcVec_sq_le`, in squared form, with general b > 0. `smallGen_spec` needs only P* = P, P² = P, Pv ≠ 0.
- `smallGen_srcDeriv` assumes B_Q ≥ 3/4 on ran Q (the paper has 1/2) and 4‖Qv₄‖² ≤ ‖Pv₄‖². Both hold on the support of the cutoff (`CutSupp`), and the constant is absolute.
- (9.66) [su:eq:active-chain-inverse]: `activeMat_inv_tail` has a stronger bound and a larger failure probability, of order (q − 5)²W^{−1/2}. (9.53) [su:eq:retained-rank-moment]: `trace_retProj`, `countIn_le_rankSurr`, as two statements. (9.50) [us:eq:absolute]: `invImage_compress_sub_le`.
- (9.24) [su:eq:cut-generator-equivariance]: `srcAct_conj` writes the conjugation of every intermediate object. (9.15) [su:eq:retained-projection]: `retProj`, the projection `flagProj` onto a range.
- The cutoff levels are explicit (`normCut`, `rankSurr`, `chainPlat_tail`). The score bound is one formula for both regimes (`smallDivBound`, `smallDivBound_weak_le`, `smallDivBound_crit_le`), and the average over the preparation is the identity `lintegral_prefix_diag`.

Section 10:

- (10.12) [eq:c-data-map]: `liftSeq`, `liftE`, `liftF` are total, with zero outside `Fin q`; `liftF_eq` holds for each even q.
- (10.25) [eq:c-K0-adjoint]: `liftK0_spec`, a pairing identity, with `liftField` the Riesz representative. `cohLeftInv` is a least-squares left inverse on all of M_W(ℂ), equal to the paper's on its domain. (10.30) [lg:eq:minimal-lift]: `hermLiftMat`, `lsqInv`.
- (10.8) [eq:c-product-map], (G.18) [eq:c-observe]: `prodDiff_mem_lieOmega`, `hsInner_prodDiff`, `conj_mem_lieOmega`.
- Appendix G.5 [sec:c-component-proof]: the cutoff of Lemma G.4 [lem:c-gaussian] acts only on the first 1000 inputs; every other input has a Hilbert–Schmidt cutoff with ‖V_i‖ ≤ √(3W) (`blockCut`, `batchCut`). `lintegral_norm_batchMat_le` holds for all n, W, E and g > 0. `isCutLift_rev`, `isCoercivityCutoff_rev` reverse the input order.
- `flagDir_spec` also gives two further identities for M₀.

Section 11:

- (11.3) [lg:eq:matrix-update], (11.5) [lg:eq:matrix-product]: `normalD`, `ellN`, with `isUnit_stepF`, `isUnit_normalD`, for all real g, |E| < 2. `exists_normalFrame`, `norm_inv_frameD_le` give the invertibility of the normal frame.
- (11.21) [uvg:eq:fmean]: the Taylor coefficients are the explicit matrices `dirY1`, `dirY2`, `dirN1`, `dirN2`. `inv_stepF_eq_sum_add` is the finite Neumann identity behind the expansion.
- (11.63) [lg:eq:Q-coefficients]: `linCoeff`, with finite support `corrCoeff_support`; `corrCoeff_solve` is existential in the index set and in q. (11.62) [lg:eq:corrector-linear-expansions]: `incMean_corr_sub_le`, for all R ∈ ℕ. `incWick_one`, `zeroW_wickMap_one_mVar` are formal coefficient identities, and `traceVars` allows g⁻² in the polynomials of Lemma 11.7 [lg:lem:ideal].

Appendices:

- The restricted resolvent in the path bound: `maskRes` is defined on all of `Fin L × Fin W`, as (1_Λ(H − E)1_Λ + 1_{Λᶜ})⁻¹. The walks use `blockOf_maskRes_eq_zero_of_separated`, so dead-end walks do not occur.
- Appendix D.2 [sec:rough-density-proof]: the block translations are stated for every permutation of the blocks (`measurePreserving_shiftMap`, `gueBlock_shiftMap`). The tail and the Stieltjes steps are stated for a general Hermitian matrix or a single transform (`empMeasure_abs_gt_le`, `norm_stieltjes_sub_le`, `cdf_sub_le_of_stieltjes`).
- Appendix G.1 [app:relative-local-law-proof]: the conditional Gaussian estimates are the Tonelli identity `lintegral_col_offRow`, for `OffRow` functions, with explicit tails; the linear tail is 4e^{−t²/2}.
- (A.84) [da:eq:deformed-vector-weight]: `im_dotProduct_deformedMat`, for any trial value. `deformed_stability_high` is a global form for η ≥ 2. `countIn_abs_gt_le_rank`, `deformClass_of_countIn_le` relate `DeformClass` to the spectral definition.

## 3. External inputs

There are none. No result of another paper is assumed; every statement in part 1 depends only on Mathlib and the three standard axioms. The works below are cited in the paper. They fall in two groups.

**Conclusions proved in the library.**

| work | what the paper uses | Lean |
|---|---|---|
| [YY] H.-T. Yau, J. Yin, arXiv:2501.01718v4 | loop hierarchy, primitive loops, one-step propagation (Sections 5, C) | `LSBA/Loop`, `LSBA/Primitive`, `LSBA/Flow`, `LSBA/Prop` |
| [TYY] S. K. Truong, F. Yang, J. Yin, arXiv:2503.11382v2 | the same objects at the block Anderson level, including its Lemma 3.3, Lemma 4.16, Corollary 4.21, Corollary 4.28, Lemma 4.29, Lemma 7.7, Lemma 7.18 | `LSBA/Loop`, `LSBA/Primitive`, `LSBA/Kernel`, `LSBA/Prop`, `LSBA/Dyson` |
| [DYYY] S. Dubova, F. Yang, H.-T. Yau, J. Yin, arXiv:2507.20274v3 | Section 8 and Appendix B.1, for Lemma 5.3 [fo:lem:bounded-initial] | `initBdd`, `boundedInitial_packet` |
| [PSSS] Int. Math. Res. Not. IMRN 2019 | its Theorem 1, for Theorem 3.1 [thm:strong-upper] | `path_halfMoment`, `lintegral_walkProd_add_halfMoment`, `fracPath_strong`, in the path form at d = 1, s = 1/2 with hopping gI |
| [APSSS] Comm. Contemp. Math. 19 (2017) | its Theorem 1, for (9.58) [us:eq:wegner], in the complex (GUE) form | `fresh_inv_norm_tail`, `fresh_inv_count_tail`, `stdCGauss_quadForm_ratio_le`, `cGauss_norm_ge_mul_abs_le` |
| [ASFH] Comm. Math. Phys. 224 (2001) | its Theorem A.1 and (2.23)–(2.24), for Lemma 8.1 and Proposition 8.2 [up:prop:fr-concentration] | `lintegral_eigCorr_rankOnePert_le`, `correlator_spectral_average`, `frac_criterion` |
| [Drogin] arXiv:2608.22543v1 | the operator framework of Sections 8, F, G | `halfOp`, `good_bad_split`, `powerDecay_of_contraction`, `angContractionAt_of_field` |
| [SSB], [SBanomaly] | the normal form and the expansions near zero energy | `LSBA/Transfer`, `large_drifts`, `center_corrector` |
| [GKT] Ann. Inst. Fourier 54 (2004) | the exponential-conjugation method in Lemma 7.3 [uvc:lem:weighted-ward] | `weighted_ward` |
| [MS] | the boundary comparison in Proposition 8.4 [up:prop:conversion] | `pathOp_boundary_comparison` |
| [PSZ] | Boole's identity, in Proposition 8.4 [up:prop:conversion] (ii) | `LSBA/Analysis/Boole.lean` |
| [SSB-averaging] | spectral averaging in Appendix E | `lintegral_eigMassSum_rankOnePert_le`, `cell_average` |

**Not proved: avoided by another argument.** The library does not contain the following results. It proves the paper's statements that use them by other arguments, listed in part 4.

| work or tool | where the paper uses it | part |
|---|---|---|
| [Biane], Indiana Univ. Math. J. 46 (1997) | Lemma A.2 [bl:lem:regular], Lemma 1.2 [da:lem:distribution] | 4.2, 4.3 |
| free-probability realization of ν_g | proof of Lemma 1.2 [da:lem:distribution] | 4.2 |
| [Teschl], Section 1.3, (1.121) | Lemma A.1 [da:lem:free-green] | 4.4 |
| Itô's formula, BDG inequality, stopping times | Sections 5, 7, Appendix C | 4.1 |
| [CGV], Geom. Funct. Anal. 36 (2026) | proof of Lemma G.4 [lem:c-gaussian] | 4.7 |
| [HKR], [KYiso], [KYani] | proof of Lemma G.1 [us:lem:local-law] | 4.7 |

The other entries of the bibliography are background or attribution, and no step of the Lean proof depends on them.

## 4. Where the Lean proof takes a different route

### 4.1 Section 5 and Appendix C: fixed times instead of Brownian paths

The paper runs the characteristic flow on Brownian paths, with Itô's formula (5.4) [fo:eq:ito], the BDG inequality and stopping times. The library has one Gaussian sample and a smooth time parameter: H_t = A_g ⊗ I + √t √γ V (`flowH`, `blockFlow`). There is no stochastic integral in the library.

- Itô's formula becomes the generator identity at each fixed time (`blockGen_resolvent`, `blockGen_loopTr`, `blockGen_propagated`), which holds for each Hermitian matrix.
- Stopping times and BDG become deterministic continuous induction on moment functionals, with an ODE comparison (`lemmaM_gaussian`, `momentIter_step'`, `lemmaM_iter`). The stopped bootstrap for mixed pairs is `lemmaN_mixed`, an ℓ^{2q} surrogate with q ≍ log W and explicit cutoffs. Same-sign pairs need no barrier: the bound |ℒ₂^{++}| ≤ (ℒ₂^{+−}(a,c) ℒ₂^{+−}(c,a))^{1/2} holds on the good event.
- Grids in time are not used; a deterministic Lipschitz grid is used only for the spectral parameter.

As a result the following statements are fixed-time statements, without a supremum in t inside the probability:

| paper | fixed-time Lean form |
|---|---|
| Lemma 5.3 [fo:lem:bounded-initial] | `boundedInitial_packet`, `initBdd` |
| Lemma 5.6 [fo:prop:inputs] | `lemma46_fixedTime` |
| Lemma 5.8 [uvc:thm:ordinary-sampling] | `loop_sampling'` |
| Theorem 5.12 [gc:thm:common] | `theorem412_one`, `theorem412_iter`, `theorem412_small`, `theorem412_large` |
| Proposition 7.4 [uvc:prop:green] | `green_interp`, `vert_max` |
| Lemma 7.7 [uvc:lem:cells] | `cells_prefix` |
| Corollary 7.8 [uvc:cor:weighted-sampling] | `swInput_of_large` |
| Proposition 7.10 [uvc:prop:residual-compression] | `residual_interp`, `pair_sampling` |

The endpoints are statements at one time, so these suffice. The hierarchy, the Ward identities and the kernels are the paper's. Pointwise identities, for example the propagated form in (C.21) [fo:eq:propagated-pair-bracket] and the following display, are stated without martingale terms. Constants differ inside the stopping argument; the conclusions are in the same ≺ form.

### 4.2 Lemma 1.2 [da:lem:distribution]

The paper's proof, in Appendix A.2 [app:bulk-regularity], uses the free-probability realization of ν_g, compactness in g and a spectral comparison. The library proves the statement directly from the bound on Im m and the single-band structure: `nuDyson_noatoms_uniform`, `nuDyson_Icc_le`, `bulk_window_explicit`, `nuDyson_compl_support`, `support_bound_le_four`. Item (ii) has the stronger form ν_g([x − h, x + h]) ≤ √(2h) for 0 < h ≤ 1/2 (`nuDyson_Icc_le`). As a check on the order of this bound: as g → ∞ the arcsine mass of [2 − 2h, 2] is arccos(1 − h)/π ∼ √(2h)/π.

### 4.3 Lemma A.2 [bl:lem:regular]

The paper cites [Biane]. The library analyses the fourth-degree equation for m directly: `dyson_iff_quartic'`, `mDysonBdry_quartic`, with the explicit edge `bandEdge` (`bandEdge_spec`, `bandEdge_ge_two`, `bandEdge_le`). `mDysonBdry_im_pos_iff` gives the single band. The existence of m_g comes from a contraction mapping, and ν_g from a Cauchy representation and Prokhorov's theorem. The explicit decay of the free row replaces the contour shift.

### 4.4 Lemma A.1 [da:lem:free-green]

The paper cites [Teschl, (1.121)]. The library uses the recurrence and periodization (`freeS_sq`, `freeT_eq`, `norm_freeRho_lt_one`, `freeRowCycle_eq` in `LSBA/Dyson/FreeGreen.lean`).

### 4.5 Results with no Lean statement

| paper | why the library needs no statement |
|---|---|
| (2.3) [eq:orbital-length] of Lemma 2.1 [thm:orbital] | nothing outside its own proof uses it; (2.2) [eq:haar-count] suffices |
| Lemma 6.6 [da:lem:regular-dyson-profile] | it is the case B = g²R of Lemma A.21 [da:lem:deformed]; the library uses `deformed_profile` and `localLaw_rel` directly, with `IsRegularState.deformClass` giving the class membership |
| Lemma 11.6 [lg:lem:fluctuations] | the library proves a stronger scalar growth bound directly: `scalar_growth` uses one-step exponential moments (`incStep_mgf_le`, `corrStep_mgf_le`), a product bound along the chain and Markov's inequality. It uses only a lower bound on ℓ_n and no maximal martingale inequality |
| Lemma A.13 [ll:lem:deterministic], Proposition B.3 [ll:prop:primitive] | the polynomial-volume bound with a logarithmic loss, outside the proof of Theorem 1.4 [thm:main]; `primLoop_large'` has no such loss |
| Lemma A.14 [da:lem:polynomial-derivatives], Lemma A.19 [da:lem:polynomial-terminal], Lemma A.20 [da:lem:polynomial-parameters], Corollary A.16 [da:cor:remainder-derivatives] | outside the proof of Theorem 1.4 [thm:main]; the propagation uses `scalesProp_large`, `terminal_match_large`, `kernel_accuracy` |

The definitions Definition 8.7 [up:def:isotropic-group], Definition 8.8 [up:def:angular-norm] do have Lean forms (part 2.8), and the label [uvu:fo:prop:inputs] is a second label of Lemma 5.6 [fo:prop:inputs].

### 4.6 Upper bound: choices where Lean is stronger or uses another admissible form

- Lemma 8.6 [up:lem:operator-reduction] for all n: `frameD_moment_le` holds for every n, not only multiples of q; an incomplete batch is bounded by the GUE norm moment.
- (E.6) [uva:eq:average] for all r: `cell_average`; (E.12), (E.13) for all r, h.
- General B_g in Lemma 11.5 [up:lem:center-transfer], Lemma 11.9 [lg:lem:centerQ], Lemma 11.10 [lg:lem:scalar-growth]: `center_transfer`, `center_corrector`, `scalar_growth`; the paper uses B_g = 1.
- **Theorem 3.1 [thm:strong-upper], a proof choice.** The statement is exactly (3.7) [eq:strong-radius], with J = ℝ (`Set.univ`). Inside the proof, Lean uses Lemma 8.1(i) on J₀ = [−33/2, 33/2] and counts the eigenvalues outside by `outlier_mean_le`, with the threshold W ≥ 32 and a norm and dimension count. The paper uses [−3, 3] and Weyl's inequality. This is not a statement difference.
- **Theorem 3.1 [thm:strong-upper], exponents.** The hopping g is deterministic; the path bound is at exponent 1/2 (`fracPath_strong`, with C = 9/4, c = 𝔟 = 1), and `frac_cycle_of_path` gives the cycle at q = 1/4. The path half of (8.2) [up:eq:fmr-pointwise] at q = 1/4 is not stated.
- Lemma 8.9 [up:lem:good-bad] in operator form and the existential K̂ of Lemma 9.3 [su:lem:chosen-generator]: parts 2.8, 2.3.
- Batch length in Theorem 3.2 [thm:sharp-small-upper]: `angContractionAt_mul` passes from a batch length q to q·m for any m ≥ 1, and the proof uses a multiple of 1000 q₀, where the paper uses lcm(q, 1000).
- Theorem 3.3 [thm:compact-upper]: `compactUpper_of_contraction` is the theorem as a consequence of Lemma 8.9 [up:lem:good-bad] and the contraction; `sharpSmallUpper_of_contraction` is the analogue.
- Theorem 3.4 [thm:large-upper]: the split at g = W and the union at the level of (8.2) [up:eq:fmr-pointwise] are the paper's. In `large_frac_cycle` the choices are t = 1/4, q = 1/8, the exponent D′ at C₀ = 1, then one larger constant for `frac_criterion`. `large_away_length` holds on 1 ≤ g ≤ W, wider than needed, and only gives some 1 ≤ n ≤ C W g² log W, which is what the chain reads. `large_frac_cycle` gives the cycle half of (8.2) [up:eq:fmr-pointwise] only.
- Appendix E: overlapping cells of length 2n on a lattice of mesh n, not a partition into cells of length in [n, 2n]; pairs within 4n go through a deterministic bound.
- Lemma 8.11 [up:lem:angular]: the proof uses smooth invariant approximations (`exists_invariant_contDiff_flagApprox`, `two_mul_integral_cutoff_le`), not a local flow, and a C¹ test function with φ′ ∈ [0, 1].

### 4.7 Other proofs that differ

- Lemma 5.4 [uvc:lem:orbital-limit]: a mean-field argument for the block trace with a Gronwall estimate on the expected hierarchy (`auxLoop_hierarchy`, `auxLoop_variance`), not orbital unitary invariance or compactness.
- Lemma 7.2 [uvs:lem:transfer-moments], Lemma 2.4 [uv:lem:short-spreading]: a first-passage bound in place of a supermartingale maximal inequality.
- Proof of Lemma 5.6 [fo:prop:inputs]: the branch is selected at fixed u by continuity in Im z, from a grid of heights; the loop component comes from block envelopes (`lemma46_loop`).
- Theorem 5.12 [gc:thm:common], Step 4, Step 5: one node estimate at length two, with the lower bound F′ = F + 18 (`step4`, `step5`).
- Lemma G.4 [lem:c-gaussian]: non-asymptotic forms replace strong convergence. There is no free semicircular family: the bounds are λ_min(S) ≥ 79, ‖S‖ ≤ 192 outside probability e^{−cW}, 𝔼‖Σ B_j ⊗ C_jᵗ‖ ≤ 28.5, and 𝔼 S_W² ≥ 40 for W ≥ W₀ (`coerMin_sq_mean_ge`, `integral_topRe_gueBlock_le`). Variance replaces Paley–Zygmund (`coerMin_lt_prob_le`). So [CGV] is not used.
- Lemma G.1 [us:lem:local-law]: a Schur complement and stability argument at the level the proof needs (`resolventMat_diag_schur`, `resolventMat_offdiag_schur`, `deformed_schur_step`, `deformed_grid_chain`), with fixed sign conjugation (`measurePreserving_signConj`), not independent phases. No general isotropic or anisotropic law is cited.
- (9.58) [us:eq:wegner]: from the one-block estimate in the form of [APSSS], with a new proof of the complex form (`stdCGauss_quadForm_ratio_le`), not the k-block form of [PSSS, Theorem 2].
- Lemma G.2 [us:lem:product]: bands of ratio W^ε with a union bound (`product_moment`), not dyadic bands with cancellation of counts.
- Lemma 9.3 [su:lem:chosen-generator] (ii): the cutoffs are explicit smooth factors, and the smoothness of the spectral projection comes from the inverse function theorem, not a Riesz contour integral.
- Lemma 11.8 [lg:lem:dynamic], Lemma 11.7 [lg:lem:ideal]: exact algebraic remainders with polynomial growth replace Taylor truncation and nets. The Gaussian expectations are computed by a Wick recursion on words (`integral_gueLin_mul_prod`, `wickMap`).
- Lemma F.3 [lem:c-operators]: a Dini-type regularity on the compact flag space and a layer-cake step with constant 4/3 (`measure_le_of_circleDeriv_le`), not the BV density of the paper.
- Lemma 11.4 [uvg:lem:mgf]: `large_mgf` bounds the moment generating function through the centered second moment of Y, its mean, and a polynomial tail bound from the fourth and fifth moments of the block norm (steps of the proof in `LSBA/Upper/LargeMGF.lean`). It uses no Lipschitz extension and no Gaussian concentration, so it does not need the derivative clause of Lemma 11.3 [uvg:lem:positive] (part 2.10).

### 4.8 (8.7) [eq:c-apriori]

The paper and the library use the same argument: the scalar averaging over ξ_x = W⁻¹Tr V_x ∼ N(0, W⁻²), whose scaled density is at most CW max{1, g}, a union over at most 2W eigenvalues, and integration of the tail min{1, CW² max{1, g}/h} (`resolvent_block_moment_le`). There is no difference.

## 5. Table

Relation is one of: same; Lean stronger; different form; different route; no Lean statement; no public statement (a private step of the named file). Several may apply. "Different form" includes a Lean statement that is weaker in one clause. Parts 2 and 4 give the details.

| paper | Lean | file | relation |
|---|---|---|---|
| Definition 1.1 [def:length] | `ell`, `ellMass` | `LSBA/Spectral/Length.lean` | different form |
| Lemma 1.2 [da:lem:distribution] | `distribution_lemma`, `nuDyson_Icc_le`, `bulk_window_explicit` | `LSBA/Dyson/DistributionLemma.lean`, `LSBA/Dyson/Distribution.lean` | Lean stronger; different route |
| Lemma 1.3 [lem:rough-density] | `rough_density_endpoint`, `rough_density_law` | `LSBA/Main/Endpoints.lean`, `LSBA/Main/RoughDensity.lean` | same |
| Theorem 1.4 [thm:main] | `main_ratio_endpoint`, `lower_ratio_endpoint` | `LSBA/Main/UpperEndpoints.lean`, `LSBA/Main/Endpoints.lean` | Lean stronger |
| Corollary 1.5 [cor:simultaneous] | `simultaneous_endpoint`, `lower_simultaneous_endpoint` | `LSBA/Main/UpperEndpoints.lean`, `LSBA/Main/Endpoints.lean` | Lean stronger |
| Lemma 2.1 [thm:orbital] | `haar_count_le` | `LSBA/Main/SimpleRanges.lean` | Lean stronger for (2.2); no Lean statement for (2.3) |
| Theorem 2.2 [uv:lem:lower-volume] | `lower_volume` | `LSBA/Volume/LowerVolume.lean` | different form |
| Theorem 2.3 [thm:bounded-lower] | `small_lower_fdist` | `LSBA/Small/Lower.lean` | same |
| Lemma 2.4 [uv:lem:short-spreading] | `short_spreading` | `LSBA/Transfer/ShortSpreading.lean` | different form |
| Theorem 2.5 [uvu:thm:terminal] | `large_lower` | `LSBA/Final/Large.lean` | same |
| Theorem 3.1 [thm:strong-upper] | `StrongUpper`, `strong_upper` | `LSBA/Upper/Interface.lean`, `LSBA/Upper/StrongUpper.lean` | different form |
| Theorem 3.2 [thm:sharp-small-upper] | `SharpSmallUpper`, `sharp_small_upper` | `LSBA/Upper/Interface.lean`, `LSBA/Upper/SharpSmall.lean` | different form |
| Theorem 3.3 [thm:compact-upper] | `CompactUpper`, `compact_upper` | `LSBA/Upper/Interface.lean`, `LSBA/Upper/CompactUpper.lean` | different form |
| Theorem 3.4 [thm:large-upper] | `LargeUpper`, `large_upper` | `LSBA/Upper/Interface.lean`, `LSBA/Upper/LargeUpper.lean` | different form |
| Theorem 4.1 [uv:thm:smooth-cutoff] | `im_resolvent_window_comparison` | `LSBA/Volume/LocalComparison.lean` | different form |
| Lemma 4.2 [uv:lem:poisson] | `poisson_smoothing`, `poisson_smoothing_matrix` | `LSBA/Volume/Poisson.lean` | different form |
| Lemma 5.1 [fo:lem:mixed-ward] | `loopTr_ward`, `primF_ward` | `LSBA/Prop/Ward.lean`, `LSBA/Primitive/Ward.lean` | different form |
| Lemma 5.2 [fo:lem:deterministic] | `primLoop_sharp`, `primLoop_bdd_tail`, `primLoop_large'`, `primLoop_large_tail'` | `LSBA/Small/Primitive.lean`, `LSBA/Primitive/Early.lean`, `LSBA/Primitive/Large.lean` | Lean stronger |
| Lemma 5.3 [fo:lem:bounded-initial] | `initBdd`, `boundedInitial_packet` | `LSBA/Flow/BoundedInitialPacket.lean` | different form; different route |
| Lemma 5.4 [uvc:lem:orbital-limit] | `orbital_limit` | `LSBA/Primitive/Orbital.lean` | different form; different route |
| Lemma 5.5 [fo:lem:resolvent-moments] | `resolvent_moments`, `resolvent_moments_vert` | `LSBA/Transfer/Coarse.lean`, `LSBA/Averaging/Vertical.lean` | different form |
| Lemma 5.6 [fo:prop:inputs] | `lemma46_fixedTime`, `initLarge` | `LSBA/Averaging/Lemma46.lean`, `LSBA/Averaging/Vertical.lean` | different form; different route |
| Definition 5.7 [def:cells-anchors] | `cellStart`, `cellLen` | `LSBA/Sampling/Cells.lean` | different form |
| Lemma 5.8 [uvc:thm:ordinary-sampling] | `loop_sampling`, `loop_sampling'` | `LSBA/Sampling/Lemma48.lean` | different form; different route |
| Lemma 5.9 [gc:lem:residual] | `averagingInput_bdd`, `averagingInput_large` | `LSBA/Averaging/Inputs.lean` | different form |
| Lemma 5.10 [fo:lem:sampling-continuity] | `pair_sampling`, `precMax_of_sampleMoment` | `LSBA/Sampling/Residual.lean`, `LSBA/Prop/SampleMoment.lean` | different form; different route |
| Lemma 5.11 [fo:lem:families] | `lemma411`, `flow_cmp_samplewise` | `LSBA/Prop/Comparison.lean` | Lean stronger |
| Theorem 5.12 [gc:thm:common] | `theorem412_iter`, `theorem412_small`, `theorem412_large` | `LSBA/Prop/Iteration.lean`, `LSBA/Small/Propagation.lean`, `LSBA/Prop/Theorem412.lean` | different form; different route |
| Lemma 5.13 [fo:lem:terminal-deterministic] | `terminal_bdd_regular`, `terminal_large_anchor` | `LSBA/Final/Terminal.lean` | same |
| Lemma 5.14 [fo:lem:bounded-terminal-matching] | `terminal_match_bdd` | `LSBA/Final/MatchBdd.lean` | Lean stronger |
| Lemma 6.1 [da:lem:scales-propagators] | `scalesProp_bdd`, `scalesProp_large` | `LSBA/Kernel/Bounded.lean`, `LSBA/Kernel/Large.lean` | different form |
| Lemma 6.2 [da:lem:scale-budgets] | `weight_comparison`, `weight_convolution`, `scale_facts` | `LSBA/Kernel/Weights.lean`, `LSBA/Kernel/Scales.lean` | different form |
| Lemma 6.3 [da:lem:comparison-parameters] | `cmpParams_bdd`, `cmpParams_large`, `cmpReach_chain` | `LSBA/Kernel/Comparison.lean`, `LSBA/Sampling/Reach.lean` | different form |
| Lemma 6.4 [da:lem:positive-height] | `positiveHeight_bdd`, `positiveHeight_large` | `LSBA/Kernel/Comparison.lean` | different form |
| Lemma 6.5 [da:lem:free-interpolation] | `free_interpolation`, `rowInterp_dyson` | `LSBA/Kernel/LineKernel.lean`, `LSBA/Sampling/Residual.lean` | Lean stronger |
| Lemma 6.6 [da:lem:regular-dyson-profile] | — | — | no Lean statement |
| Definition 7.1 [def:transfer-matrices] | `transferMat`, `transferProd`, `freeConj` | `LSBA/Transfer/Basic.lean` | different form |
| Lemma 7.2 [uvs:lem:transfer-moments] | `transfer_moments`, `one_step_moment_inv` | `LSBA/Transfer/Moments.lean`, `LSBA/Transfer/OneStep.lean` | Lean stronger; different route |
| Lemma 7.3 [uvc:lem:weighted-ward] | `weighted_ward`, `weighted_ward_identity` | `LSBA/Averaging/Ward.lean` | Lean stronger |
| Proposition 7.4 [uvc:prop:green] | `green_interp`, `green_interp_hs` | `LSBA/Sampling/Transfer.lean` | different form |
| Lemma 7.5 [uvc:lem:space] | `loopSpace`, `finrank_loopSpace_le`, `loopTr_dist_space` | `LSBA/Sampling/Space.lean` | different form |
| Lemma 7.6 [uvc:lem:fekete] | `fekete_norming` | `LSBA/Sampling/Fekete.lean` | different form |
| Lemma 7.7 [uvc:lem:cells] | `cells_prefix` | `LSBA/Sampling/Prefix.lean` | different form |
| Corollary 7.8 [uvc:cor:weighted-sampling] | `loop_sampling`, `swInput_of_large` | `LSBA/Sampling/Lemma48.lean` | different form |
| Remark 7.9 | — | — | no Lean statement |
| Proposition 7.10 [uvc:prop:residual-compression] | `residual_interp`, `segRes_identity`, `pair_sampling` | `LSBA/Sampling/Residual.lean` | different form |
| Lemma 8.1 | `frac_concentration_fixed`, `frac_concentration_averaged` | `LSBA/Upper/FracConcentration.lean`, `LSBA/Upper/FracAveraged.lean` | Lean stronger |
| Proposition 8.2 [up:prop:fr-concentration] | `frac_criterion` | `LSBA/Upper/FracCriterion.lean` | Lean stronger |
| Definition 8.3 [def:boundary-frames] | `IsBoundaryFrame`, `frameD`, `NegTransfer` | `LSBA/Transfer/Frames.lean`, `LSBA/Upper/FracMoment.lean` | different form |
| Proposition 8.4 [up:prop:conversion] | `frac_local_of_growth`, `frac_avg_of_negative_moment` | `LSBA/Upper/FracLocal.lean`, `LSBA/Upper/FracAvgPath.lean` | Lean stronger |
| Definition 8.5 [up:def:transfer-operator] | `batchMat`, `halfOp`, `volCocycle` | `LSBA/Upper/Operator.lean`, `LSBA/Transfer/VolCocycle.lean` | different form |
| Lemma 8.6 [up:lem:operator-reduction] | `frameD_moment_le`, `transferInputAt_of_powerDecay`, `transferLength_of_contraction` | `LSBA/Upper/OperatorReduction.lean`, `LSBA/Upper/OperatorLength.lean`, `LSBA/Upper/FracChain.lean` | Lean stronger; different form |
| Definition 8.7 [up:def:isotropic-group] | `isoGroup` | `LSBA/Transfer/IsoGroup.lean` | same |
| Definition 8.8 [up:def:angular-norm] | `AngL4Le` | `LSBA/Transfer/CircleMeasure.lean` | same |
| Lemma 8.9 [up:lem:good-bad] | `GoodBadSplit`, `good_bad_split` | `LSBA/Upper/OperatorIteration.lean`, `LSBA/Upper/GoodBad.lean` | different form |
| Lemma 8.10 [up:lem:operator-iteration] | `powerDecay_of_contraction`, `iterate_halfOp_one_le` | `LSBA/Upper/OperatorIteration.lean` | different form |
| Lemma 8.11 [up:lem:angular] | `angContractionAt_of_field`, `angContractionAllAt_of_field_zero` | `LSBA/Upper/Angular.lean` | different form; different route |
| Lemma 8.12 [up:lem:small-contraction] | `small_contraction_weak`, `small_contraction_crit` | `LSBA/Upper/SmallContraction.lean` | different form |
| Lemma 8.13 [up:lem:density-contraction] | `density_contraction` | `LSBA/Upper/DensityContraction.lean` | Lean stronger |
| Lemma 9.1 [su:lem:preparation] | `preparation_weak`, `preparation_crit` | `LSBA/Upper/Preparation.lean`, `LSBA/Upper/PrepGood.lean` | Lean stronger |
| Lemma 9.2 [su:lem:field-geometry] | `field_geometry`, `smallField_motion` | `LSBA/Upper/FieldGeometry.lean` | Lean stronger |
| Lemma 9.3 [su:lem:chosen-generator] | `chosen_generator_weak`, `chosen_generator_crit`, `ChosenGenerator` | `LSBA/Upper/ChosenGeneratorExists.lean`, `LSBA/Upper/ChosenGenerator.lean` | different form (one bound weaker) |
| Lemma 9.4 [us:lem:score] | `score_bound`, `lintegral_gaussDiv_smallScore_le` | `LSBA/Upper/Score.lean`, `LSBA/Upper/SmallScorePrefix.lean` | different form |
| Lemma 9.5 [us:lem:range] | `invImage_relative_le` | `LSBA/Spectral/InvImageRange.lean` | Lean stronger |
| Lemma 9.6 [us:lem:self] | `gaussProj_overlap_le` | `LSBA/Gauss/GaussProjection.lean` | Lean stronger |
| Corollary 9.7 [nc:lem:compression] | `invImage_overlap_le` | `LSBA/Spectral/InvImageCompress.lean` | Lean stronger |
| Lemma 10.1 [lem:c-gaussian-lift] | `gaussian_lift_general`, `gaussian_lift_away` | `LSBA/Upper/LiftGeneral.lean`, `LSBA/Upper/LiftAway.lean` | different form |
| Theorem 11.1 [uvg:thm:transfer] | `negative_transfer_moment` | `LSBA/Upper/LargeTransfer.lean` | different form (deterministic frame) |
| Lemma 11.2 [uvg:lem:drifts] | `large_drifts` | `LSBA/Upper/LargeDrift.lean` | Lean stronger |
| Lemma 11.3 [uvg:lem:positive] | `large_positive` | `LSBA/Upper/LargePositive.lean` | different form (derivative clause not formalized) |
| Lemma 11.4 [uvg:lem:mgf] | `large_mgf` | `LSBA/Upper/LargeMGF.lean` | Lean stronger; different route |
| Lemma 11.5 [up:lem:center-transfer] | `center_transfer` | `LSBA/Upper/NearZeroTransfer.lean` | Lean stronger |
| Lemma 11.6 [lg:lem:fluctuations] | — | — | no Lean statement |
| Lemma 11.7 [lg:lem:ideal] | `wickMap_mem_obsIdeal`, `transOp_obsEval_sub_le` | `LSBA/Upper/CenterIdeal.lean`, `LSBA/Upper/CenterExpansion.lean` | different form |
| Lemma 11.8 [lg:lem:dynamic] | `corrObs_form`, `corrCoeff_bounded`, `corrObs_stability`, `center_zero_odd_neg`, `center_bounds` | `LSBA/Upper/CenterCorrection.lean`, `LSBA/Upper/CenterParity.lean`, `LSBA/Upper/CenterStability.lean`, `LSBA/Upper/CenterCenters.lean`, `LSBA/Upper/CenterNewton.lean` | different form |
| Lemma 11.9 [lg:lem:centerQ] | `center_corrector` | `LSBA/Upper/CenterCorrector.lean` | Lean stronger |
| Lemma 11.10 [lg:lem:scalar-growth] | `scalar_growth` | `LSBA/Upper/NearZeroGrowth.lean` | Lean stronger; different route |
| Lemma A.1 [da:lem:free-green] | `freeT_eq`, `freeRowCycle_eq` | `LSBA/Dyson/FreeGreen.lean` | Lean stronger; different route |
| Lemma A.2 [bl:lem:regular] | `regular_quantile`, `mDyson_deriv_le` | `LSBA/Dyson/Regular.lean` | different form; different route |
| Lemma A.3 [bl:lem:finite] | `finite_regular_point`, `finite_regular_quantile` | `LSBA/Dyson/FiniteRegular.lean` | different form |
| Lemma A.4 [uvp:prop:finite] | `large_periodic_comparison` | `LSBA/Kernel/Large.lean` | different form |
| Lemma A.5 [ba:lem:kernels] | `bdd_kernels`, `bdd_symbol` | `LSBA/Kernel/Bounded.lean` | different form |
| Lemma A.6 [da:lem:line-kernel] | `geom_bounds`, `lineKer` | `LSBA/Kernel/LineKernel.lean`, `LSBA/Kernel/Defs.lean` | different form |
| Lemma A.7 [da:lem:transport-refinements] | `bdd_gradient` | `LSBA/Kernel/Bounded.lean` | different form |
| Lemma A.8 [uvp:lem:geom] | `geom_bounds` | `LSBA/Kernel/LineKernel.lean` | different form |
| Lemma A.9 [uvp:lem:perturb] | `kernel_perturb` | `LSBA/Kernel/Algebra.lean` | Lean stronger |
| Lemma A.10 [uvp:lem:actual-kernels] | `large_actual_kernels`, `increment_large` | `LSBA/Kernel/Large.lean`, `LSBA/Kernel/LargeIncrement.lean` | different form |
| Lemma A.11 [da:lem:stopped-pair-weights] | `weight_comparison`, `weight_convolution` | `LSBA/Kernel/Weights.lean` | different form |
| Lemma A.12 [da:lem:profile-improvement] | `profile_minimum`, `step5` | `LSBA/Kernel/Scales.lean`, `LSBA/Prop/Step45.lean` | different form |
| Lemma A.13 [ll:lem:deterministic] | — | — | no Lean statement |
| Lemma A.14 [da:lem:polynomial-derivatives] | — | — | no Lean statement |
| Lemma A.15 [da:lem:early-pair-inverses] | `early_inverse_abstract` | `LSBA/Kernel/Algebra.lean` | different form |
| Corollary A.16 [da:cor:remainder-derivatives] | — | — | no Lean statement |
| Lemma A.17 [da:lem:rough-stability] | `rough_stability`, `freeTL_sub_freeT` | `LSBA/Dyson/RoughStability.lean` | same |
| Lemma A.18 [fo:lem:matching] | `terminal_match_large` | `LSBA/Final/MatchLarge.lean` | Lean stronger |
| Lemma A.19 [da:lem:polynomial-terminal] | — | — | no Lean statement |
| Lemma A.20 [da:lem:polynomial-parameters] | — | — | no Lean statement |
| Lemma A.21 [da:lem:deformed] | `deformed_profile`, `deformed_scalar_stability` | `LSBA/Dyson/Deformed.lean` | Lean stronger |
| Lemma A.22 [da:lem:deformed-stability] | `deformed_residual_stability`, `deformed_vector_weight` | `LSBA/Dyson/DeformedStability.lean` | Lean stronger |
| Lemma B.1 [ba:lem:moment] | `stableMol_bdd`, `stableMol_bdd_cancel` | `LSBA/Primitive/Molecule.lean` | different form |
| Proposition B.2 [ba:prop:primitive] | `primLoop_sharp`, `primLoopF_bdd_weighted` | `LSBA/Small/Primitive.lean`, `LSBA/Primitive/Early.lean` | Lean stronger |
| Proposition B.3 [ll:prop:primitive] | — | — | no Lean statement |
| Lemma B.4 [uvp:lem:anchor] | `uvp_anchor` | `LSBA/Primitive/Uniform.lean` | different form |
| Lemma B.5 [uvp:lem:taylor] | — | `LSBA/Primitive/Uniform.lean` | no public statement; internal step of that file |
| Theorem B.6 [uvp:thm:molecule] | `uvp_molecule` | `LSBA/Primitive/Uniform.lean` | Lean stronger |
| Theorem B.7 [uvp:thm:tree] | — | `LSBA/Primitive/Large.lean` | no public statement; internal step of that file |
| Proposition B.8 [uvp:prop:cores] | `stableMol_large'` | `LSBA/Primitive/Molecule.lean` | Lean stronger |
| Corollary B.9 [uvp:cor:joint-tail] | `primLoopF_large_weighted`, `primLoop_large_tail'` | `LSBA/Primitive/Large.lean` | Lean stronger |
| Lemma B.10 [b:lem:early-primitive] | `primLoop_early`, `primLoopF_freeLabel'` | `LSBA/Primitive/Early.lean`, `LSBA/Primitive/Large.lean` | Lean stronger |
| Lemma B.11 [b:lem:primitive-pair] | `primLoop_longPair`, `primLoop_longPair_large'` | `LSBA/Primitive/Bounded.lean`, `LSBA/Primitive/Large.lean` | same |
| Lemma F.1 [cc:lem:quotient] | `quotProj_spec`, `exists_isCircleBasis`, `exp_two_mul_volCocycle_circlePair` | `LSBA/Transfer/Circle.lean`, `LSBA/Transfer/CircleJacobian.lean` | Lean stronger |
| Lemma F.2 [cc:lem:cofactor] | `exp_neg_volCocycle_omitPair`, `norm_frameD_inv_rpow_le` | `LSBA/Transfer/Cofactor.lean` | Lean stronger |
| Lemma F.3 [lem:c-operators] | `abs_integral_goodPart_le`, `abs_integral_circleDeriv_le` | `LSBA/Upper/GoodOperator.lean`, `LSBA/Upper/VerticalBound.lean` | different form; different route |
| Lemma G.1 [us:lem:local-law] | `localLaw_rel`, `localLaw_iso`, `localLaw_entry`, `localLaw_avg` | `LSBA/Spectral/DeformedRelLaw.lean`, `LSBA/Spectral/DeformedIsoLaw.lean`, `LSBA/Spectral/DeformedLocalLaw.lean` | different form; different route |
| Lemma G.2 [us:lem:product] | `product_moment` | `LSBA/Upper/ProductMoment.lean` | Lean stronger; different route |
| Lemma G.3 [nc:lem:buffer] | `buffer_lower`, `buffer_lower_eta` | `LSBA/Upper/Buffer.lean` | Lean stronger |
| Lemma G.4 [lem:c-gaussian] | `coercivity_cutoff`, `coerMin_lt_prob_le` | `LSBA/Upper/CoercivityCutoff.lean`, `LSBA/Upper/CoercivityTail.lean` | different form; different route |

Displays cited in the text:

| paper | Lean | file | relation |
|---|---|---|---|
| (2.2) [eq:haar-count] | `haar_count_le` | `LSBA/Main/SimpleRanges.lean` | Lean stronger |
| (2.3) [eq:orbital-length] | — | — | no Lean statement |
| (2.12) [uv:eq:lower-regions-output] | `lower_count_endpoint` | `LSBA/Main/Endpoints.lean` | Lean stronger |
| (3.6) [eq:averaged-tail] | `AveragedTailBound` | `LSBA/Upper/Interface.lean` | different form |
| (3.11) [uv:eq:upper-count] | `upper_count_endpoint` | `LSBA/Main/UpperEndpoints.lean` | Lean stronger |
| (8.7) [eq:c-apriori] | `resolvent_block_moment_le` | `LSBA/Upper/ConversionApriori.lean` | same |
| (8.2) [up:eq:fmr-pointwise] | `FracCycle`, `FracPath` | `LSBA/Upper/FracMoment.lean` | same |
| (8.6) [uv:eq:upper-volume-input] | `EndpointMomentAt` | `LSBA/Upper/ConversionEndpoint.lean` | same |
| (8.11) [up:eq:input] | `TransferInputAt` | `LSBA/Upper/ConversionEndpoint.lean` | same |
| (8.12) [up:eq:negative-transfer-input] | `NegTransfer` | `LSBA/Upper/FracMoment.lean` | same |
| (E.6) [uva:eq:average] | `cell_average` | `LSBA/Upper/LargeAverage.lean` | Lean stronger |
| (E.15) [eq:c-cycle-Schur] | `cycle_schur'`, `cycle_moment_of_path` | `LSBA/Transfer/PathSchur.lean`, `LSBA/Upper/ConversionCycle.lean` | Lean stronger |
