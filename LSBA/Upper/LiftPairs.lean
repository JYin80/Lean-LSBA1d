import LSBA.Upper.LiftObserve
import LSBA.Gauss.GUELayout

/-!
# The pair equations

The data map of (10.12) [eq:c-data-map]: `E_q = 0`, `E_{i-1} = -R_i C_i - E_i*` and
`F_i(R) = E_i C_i + C_i E_i* + C_i R_i C_i + R_{i+1} - R_{i-1}`; for a target `Z` of the
algebra (10.3) [eq:c-Lie] with data `R_i` and upper-left block `P`, the pair equations (10.13)
[eq:c-block-equations], (G.19) [eq:c-pair] `C_i P + P* C_i = F_i(R)` at the interior odd indices
of an even `q`; and, for `q = 1000` and the disjoint pairs `(i_j, k_j) = (4j+1, 4j-1)`,
`1 ≤ j ≤ 128`, the equation `𝓛 P = 2^{-1/2} g 𝓕 R` with `G_j = 2^{-1/2}(V_{k_j} - V_{i_j})`
(Section 10 [sec:compact-proof]). Input `k` of `Fin q` stands for the paper's index `k + 1`.
-/

open Real Finset
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- An array on `Fin q`, extended by `0` to all natural indices. -/
def liftSeq {W q : ℕ} (R : Fin q → Matrix (Fin W) (Fin W) ℂ) (k : ℕ) : Matrix (Fin W) (Fin W) ℂ :=
  if h : k < q then R ⟨k, h⟩ else 0

/-- `E` at the index `top - n`: `E_top = 0` and `E_{i-1} = -R_i C_i - E_i*` (10.12)
[eq:c-data-map]. -/
def liftEAux {W : ℕ} (C R : ℕ → Matrix (Fin W) (Fin W) ℂ) (top : ℕ) :
    ℕ → Matrix (Fin W) (Fin W) ℂ
  | 0 => 0
  | n + 1 => -(R (top - n) * C (top - n)) - (liftEAux C R top n)ᴴ

/-- `E_k` of (10.12) [eq:c-data-map] at input `k` (the paper's `E_{k+1}`), with `E = 0` at the
last input. -/
def liftE {W q : ℕ} (g z : ℝ) (V R : Fin q → Matrix (Fin W) (Fin W) ℂ) (k : ℕ) :
    Matrix (Fin W) (Fin W) ℂ :=
  liftEAux (liftSeq (liftC g z V)) (liftSeq R) (q - 1) (q - 1 - k)

/-- `F_k(R) = E_k C_k + C_k E_k* + C_k R_k C_k + R_{k+1} - R_{k-1}` of (10.12)
[eq:c-data-map] at input `k` (the paper's `F_{k+1}`). -/
def liftF {W q : ℕ} (g z : ℝ) (V R : Fin q → Matrix (Fin W) (Fin W) ℂ) (k : ℕ) :
    Matrix (Fin W) (Fin W) ℂ :=
  liftE g z V R k * liftSeq (liftC g z V) k + liftSeq (liftC g z V) k * (liftE g z V R k)ᴴ +
    liftSeq (liftC g z V) k * liftSeq R k * liftSeq (liftC g z V) k + liftSeq R (k + 1) -
    liftSeq R (k - 1)

/-- (10.13) [eq:c-block-equations], (G.19) [eq:c-pair]: for even `q`, a target `Z` of the
algebra with data `R_i` and upper-left block `P`, and an even input `k` with
`2 ≤ k ≤ q - 2` (the paper's odd `3 ≤ i ≤ q - 1`), `C_k P + P* C_k = F_k(R)`. -/
theorem liftF_eq {W q : ℕ} {g z : ℝ} {V : Fin q → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ i, (V i).IsHermitian) {Z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hZ : Z ∈ lieOmega W) (hq : Even q) {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k) (hkq : k + 2 ≤ q) :
    liftSeq (liftC g z V) k * blockPart Z 0 0 + (blockPart Z 0 0)ᴴ * liftSeq (liftC g z V) k =
      liftF g z V (fun i => blockPart (liftConj g z V Z i) 1 0) k := by
  have hs : ∀ (X : Fin q → Matrix (Fin W) (Fin W) ℂ) (n : ℕ) (h : n < q),
      liftSeq X n = X ⟨n, h⟩ := fun X n h => by simp [liftSeq, h]
  obtain ⟨htop, hrec⟩ := liftConj_recursion (g := g) (z := z) hV hZ
  have hpar : ∀ n, n < q →
      liftSeq (fun i => blockPart (liftConj g z V Z i) 0 0) (q - 1 - n) =
        (if Even n then blockPart Z 0 0 else -(blockPart Z 0 0)ᴴ) +
          liftEAux (liftSeq (liftC g z V)) (liftSeq fun i => blockPart (liftConj g z V Z i) 1 0)
            (q - 1) n := by
    intro n
    induction n with
    | zero =>
      intro h
      rw [hs _ _ (by omega), htop _ (by simp only; omega)]
      simp [liftEAux]
    | succ n ih =>
      intro h
      have e := (hrec ⟨q - 1 - n, by omega⟩ ⟨q - 1 - (n + 1), by omega⟩
        (by simp only; omega)).1
      have e1 := hs (fun i => blockPart (liftConj g z V Z i) 0 0) (q - 1 - n) (by omega)
      have e2 := hs (fun i => blockPart (liftConj g z V Z i) 1 0) (q - 1 - n) (by omega)
      have e3 := hs (liftC g z V) (q - 1 - n) (by omega)
      rw [hs _ _ (by omega), e, liftEAux, ← e1, ← e2, ← e3, ih (by omega)]
      rcases Nat.even_or_odd n with hn | hn
      · have hn' : ¬ Even (n + 1) := by rw [Nat.even_add_one]; exact not_not.mpr hn
        simp only [hn, hn', ite_true, ite_false, Matrix.conjTranspose_add]
        abel
      · have hn' : Even (n + 1) := hn.add_one
        have hn'' : ¬ Even n := Nat.not_even_iff_odd.mpr hn
        simp only [hn', hn'', ite_true, ite_false, Matrix.conjTranspose_add,
          Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose]
        abel
  have hodd : ¬ Even (q - 1 - k) := by
    obtain ⟨a, ha⟩ := hq
    obtain ⟨b, hb⟩ := hk
    rintro ⟨c, hc⟩
    omega
  have hPk := hpar (q - 1 - k) (by omega)
  rw [show q - 1 - (q - 1 - k) = k by omega, hs _ _ (by omega)] at hPk
  simp only [hodd, ite_false] at hPk
  have eU := (hrec ⟨k + 1, by omega⟩ ⟨k, by omega⟩ rfl).2.1
  have eR := (hrec ⟨k, by omega⟩ ⟨k - 1, by omega⟩ (by simp only; omega)).2.2
  unfold liftF liftE
  rw [hs _ k (by omega), hs _ k (by omega), hs _ (k + 1) (by omega), hs _ (k - 1) (by omega)]
  rw [eR, eU, hPk]
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_neg,
    Matrix.conjTranspose_conjTranspose, Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul,
    Matrix.mul_neg]
  abel

/-- The input `i_j` of the pair `j` (the paper's `4j + 1`, `1 ≤ j ≤ 128`). -/
def liftPairI : Fin 128 → Fin 1000 := fun j => ⟨4 * j + 4, by omega⟩

/-- The input `k_j` of the pair `j` (the paper's `4j - 1`, `1 ≤ j ≤ 128`). -/
def liftPairK : Fin 128 → Fin 1000 := fun j => ⟨4 * j + 2, by omega⟩

/-- The layout `G_j = 2^{-1/2} (V_{k_j} - V_{i_j})` of Section 10 [sec:compact-proof]. -/
def liftLayout : Matrix (Fin 128) (Fin 1000) ℝ := pairLayout liftPairI liftPairK

/-- The data map `𝓕 R = (F_{i_j}(R) - F_{k_j}(R))_j` of Section 10 [sec:compact-proof]. -/
def pairData {W : ℕ} (g z : ℝ) (V R : Fin 1000 → Matrix (Fin W) (Fin W) ℂ) :
    Fin 128 → Matrix (Fin W) (Fin W) ℂ :=
  fun j => liftF g z V R (liftPairI j) - liftF g z V R (liftPairK j)

/-- `𝓛 P = 2^{-1/2} g 𝓕 R` (Section 10 [sec:compact-proof], (G.19) [eq:c-pair]): for `g > 0`,
`G = liftLayout V` and a target `Z` of the algebra with data `R_i` and upper-left block `P`. -/
theorem cohMap_liftLayout {W : ℕ} {g z : ℝ} (hg : 0 < g) {V : Fin 1000 → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ i, (V i).IsHermitian) {Z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hZ : Z ∈ lieOmega W) :
    cohMap (layoutBlocks liftLayout V) (blockPart Z 0 0) =
      ((((Real.sqrt 2)⁻¹ * g : ℝ)) : ℂ) •
        pairData g z V (fun i => blockPart (liftConj g z V Z i) 1 0) := by
  have hik : ∀ a b, liftPairI a ≠ liftPairK b := fun a b h => by
    simp [liftPairI, liftPairK, Fin.ext_iff] at h; omega
  have hF : ∀ j : Fin 1000, Even j.val → 2 ≤ j.val → j.val + 2 ≤ 1000 →
      liftF g z V (fun i => blockPart (liftConj g z V Z i) 1 0) j =
        liftC g z V j * blockPart Z 0 0 + (blockPart Z 0 0)ᴴ * liftC g z V j := by
    intro j h1 h2 h3
    rw [← liftF_eq hV hZ (by decide) h1 h2 h3]
    simp [liftSeq, j.isLt]
  have hg0 : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  have hc : ((((Real.sqrt 2)⁻¹ * g : ℝ)) : ℂ) * (g : ℂ)⁻¹ = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
    push_cast
    field_simp
  funext j
  have hd : liftC g z V (liftPairI j) - liftC g z V (liftPairK j) =
      ((g : ℂ)⁻¹) • (V (liftPairK j) - V (liftPairI j)) := by
    simp only [liftC, smul_sub]
    abel
  rw [Pi.smul_apply, pairData,
    hF _ (Nat.even_iff.mpr (by simp [liftPairI]; omega)) (by simp [liftPairI])
      (by simp [liftPairI]; omega),
    hF _ (Nat.even_iff.mpr (by simp [liftPairK]; omega)) (by simp [liftPairK])
      (by simp [liftPairK]; omega)]
  have e : liftC g z V (liftPairI j) * blockPart Z 0 0 +
        (blockPart Z 0 0)ᴴ * liftC g z V (liftPairI j) -
      (liftC g z V (liftPairK j) * blockPart Z 0 0 +
        (blockPart Z 0 0)ᴴ * liftC g z V (liftPairK j)) =
      (liftC g z V (liftPairI j) - liftC g z V (liftPairK j)) * blockPart Z 0 0 +
        (blockPart Z 0 0)ᴴ * (liftC g z V (liftPairI j) - liftC g z V (liftPairK j)) := by
    rw [Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [e, hd, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, smul_smul, hc]
  change layoutBlocks liftLayout V j * blockPart Z 0 0 +
    (blockPart Z 0 0)ᴴ * layoutBlocks liftLayout V j = _
  rw [liftLayout, layoutBlocks_pairLayout hik, Matrix.smul_mul, Matrix.mul_smul]

end LSBA
