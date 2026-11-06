import LSBA.Upper.SmallChart
import LSBA.Spectral.SpecProj

/-!
# The construction of `K`

Section 9.2 [su:sec:explicit-generator], conditionally on `R_4 = R` and for a projection `P`, a
threshold `t = t_cut` and a source `v = v_4`. The right-cavity inverses
`R←_{q-1} = (V_{q-1} - E)⁻¹`, `R←_j = (V_j - E - g² R←_{j+1})⁻¹` and their product
`A = R←_{q-1} ⋯ R←_6`; `R̃ = (V_5 - E - g² R_4 - g² R←_6)⁻¹` and the cavity identity
`R_{[q-1,5]} = A R̃` (3.4) [us:eq:cavity]; the retained projection `Q` onto
`R̃ ran(A_>*)` (9.15) [su:eq:retained-projection] with `A_> = A 1_{(t², ∞)}(A* A)`; the allowed
projection `Π = P - ‖P v‖⁻² (P v)(P v)*`; the vector `y = Π Q B_Q⁻¹ Q v` and the generator `K_0`
of (9.16) [us:eq:H0], with `B_Q⁻¹` realized as `Q (Q Π Q + 1 - Q)⁻¹ Q`; the discarded error
`e_{q-1} = A_< R̃ (y - v)` of (9.17) [us:eq:error]; the scale `ξ` and `K = K_0/ξ` of (9.18)
[us:eq:normalize]. Their algebraic identities, and the elementary bounds (9.21)
[su:eq:normalized-generator-costs] under (9.19) [su:eq:generator-admissibility].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The right-cavity inverses of Section 9.2 [su:sec:explicit-generator], counted from the right:
`cavR … 0 = R←_{q-1} = (V_{q-1} - E)⁻¹` and `cavR … (m + 1) = R←_{q-2-m}
= (V_{q-2-m} - E - g² R←_{q-1-m})⁻¹`; so `R←_j = cavR … (q - 1 - j)`. -/
def cavR (W : ℕ) (g E : ℝ) (q : ℕ) (ω : Ω W q) : ℕ → Matrix (Fin W) (Fin W) ℂ
  | 0 => (blockSeq W q ω (q - 2) - (E : ℂ) • 1)⁻¹
  | m + 1 => (blockSeq W q ω (q - 3 - m) - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • cavR W g E q ω m)⁻¹

/-- `cavProd … m = R←_{q-1} ⋯ R←_{q-m}`; the product `A = R←_{q-1} ⋯ R←_6` of Section 9.2
[su:sec:explicit-generator] is `cavProd … (q - 6)`. -/
def cavProd (W : ℕ) (g E : ℝ) (q : ℕ) (ω : Ω W q) : ℕ → Matrix (Fin W) (Fin W) ℂ
  | 0 => 1
  | m + 1 => cavProd W g E q ω m * cavR W g E q ω m

/-- `R̃ = (V_5 - E - g² R_4 - g² R←_6)⁻¹` of (3.4) [us:eq:cavity]. -/
def cavRes (W : ℕ) (g E : ℝ) (q : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) :
    Matrix (Fin W) (Fin W) ℂ :=
  (blockSeq W q ω 4 - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • R -
    ((g : ℂ) ^ 2) • cavR W g E q ω (q - 7))⁻¹

/-- The retained spectral projection `1_{(t², ∞)}(A* A)`, so that `A_> = A 1_{(t², ∞)}(A* A)`
(Section 9.2 [su:sec:explicit-generator]). -/
def retSpec (W : ℕ) (g E : ℝ) (q : ℕ) (t : ℝ) (ω : Ω W q) : Matrix (Fin W) (Fin W) ℂ :=
  specProj ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)) (Set.Ioi (t ^ 2))

/-- The retained projection `Q` of (9.15) [su:eq:retained-projection], the orthogonal projection
onto `R̃ (ran 1_{(t², ∞)}(A* A)) = R̃ (ran A_>*)`. -/
def retProj (W : ℕ) (g E : ℝ) (q : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) (t : ℝ) (ω : Ω W q) :
    Matrix (Fin W) (Fin W) ℂ :=
  flagProj (cavRes W g E q R ω) (retSpec W g E q t ω)

/-- The allowed projection `Π = P - ‖P v‖⁻² (P v)(P v)*` of Section 9.2
[su:sec:explicit-generator]. -/
def allowProj {W : ℕ} (P : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  P - (star (P *ᵥ v) ⬝ᵥ (P *ᵥ v))⁻¹ • Matrix.vecMulVec (P *ᵥ v) (star (P *ᵥ v))

/-- The vector `y = Π Q B_Q⁻¹ Q v` of (9.16) [us:eq:H0], with `B_Q⁻¹ = Q (Q Π Q + 1 - Q)⁻¹ Q` on
`ran Q`. -/
def srcVec (W : ℕ) (g E : ℝ) (q : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) (t : ℝ)
    (P : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) (v : Fin W → ℂ) : Fin W → ℂ :=
  (allowProj P v * retProj W g E q R t ω *
      (retProj W g E q R t ω * allowProj P v * retProj W g E q R t ω +
        (1 - retProj W g E q R t ω))⁻¹ * retProj W g E q R t ω) *ᵥ v

/-- The generator `K_0 = ‖P v‖⁻² (y (P v)* - (P v) y*)` of (9.16) [us:eq:H0]. -/
def gen0 (W : ℕ) (g E : ℝ) (q : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) (t : ℝ)
    (P : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) (v : Fin W → ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  (star (P *ᵥ v) ⬝ᵥ (P *ᵥ v))⁻¹ •
    (Matrix.vecMulVec (srcVec W g E q R t P ω v) (star (P *ᵥ v)) -
      Matrix.vecMulVec (P *ᵥ v) (star (srcVec W g E q R t P ω v)))

/-- The scale `ξ = ‖v_{q-1}‖⁻² Re(v_{q-1}* R_{[q-1,5]} y)` of (9.18) [us:eq:normalize]. -/
def genScale (W : ℕ) (g E : ℝ) (q : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) (t : ℝ)
    (P : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) (v : Fin W → ℂ) : ℝ :=
  (star (chartProd W g E q R ω (q - 1) *ᵥ v) ⬝ᵥ
      (chartProd W g E q R ω (q - 1) *ᵥ srcVec W g E q R t P ω v)).re /
    ∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2

/-- The generator `K = K_0 / ξ` of (9.18) [us:eq:normalize]. -/
def smallGen (W : ℕ) (g E : ℝ) (q : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) (t : ℝ)
    (P : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) (v : Fin W → ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  (((genScale W g E q R t P ω v)⁻¹ : ℝ) : ℂ) • gen0 W g E q R t P ω v

/-- The discarded error `e_{q-1} = A_< R̃ (y - v)` of (9.17) [us:eq:error], with
`A_< = A 1_{(-∞, t²]}(A* A)`. -/
def discErr (W : ℕ) (g E : ℝ) (q : ℕ) (R : Matrix (Fin W) (Fin W) ℂ) (t : ℝ)
    (P : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) (v : Fin W → ℂ) : Fin W → ℂ :=
  (cavProd W g E q ω (q - 6) *
      specProj ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)) (Set.Iic (t ^ 2)) *
      cavRes W g E q R ω) *ᵥ (srcVec W g E q R t P ω v - v)

/-- The right-cavity matrix before inversion: `cavX … k = (cavR … k)⁻¹`. -/
private def SmallGenerator_cavX (W : ℕ) (g E : ℝ) (q : ℕ) (ω : Ω W q) :
    ℕ → Matrix (Fin W) (Fin W) ℂ
  | 0 => blockSeq W q ω (q - 2) - (E : ℂ) • 1
  | k + 1 => blockSeq W q ω (q - 3 - k) - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • cavR W g E q ω k

private lemma SmallGenerator_cavX_succ (W : ℕ) (g E : ℝ) (q : ℕ) (ω : Ω W q) (k : ℕ) :
    SmallGenerator_cavX W g E q ω (k + 1) =
      blockSeq W q ω (q - 3 - k) - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • cavR W g E q ω k := rfl

private lemma SmallGenerator_cavR_eq (W : ℕ) (g E : ℝ) (q : ℕ) (ω : Ω W q) (k : ℕ) :
    cavR W g E q ω k = (SmallGenerator_cavX W g E q ω k)⁻¹ := by
  cases k <;> rfl

/-- `cavN … k = V_{q-1-k} - E - g² R←_{q-k} - g² R_{q-2-k}` (`R←_q = 0`), so that
`R_{q-1} ⋯ R_{q-1-k} · cavN … k = R←_{q-1} ⋯ R←_{q-k}`. -/
private def SmallGenerator_cavN (W : ℕ) (g E : ℝ) (q : ℕ) (R : Matrix (Fin W) (Fin W) ℂ)
    (ω : Ω W q) (k : ℕ) : Matrix (Fin W) (Fin W) ℂ :=
  SmallGenerator_cavX W g E q ω k - ((g : ℂ) ^ 2) • chartR W g E q R ω (q - 2 - k)

/-- The product `R_{q-1} ⋯ R_{q-k}` of chart coordinates, growing on the right. -/
private def SmallGenerator_top (W : ℕ) (g E : ℝ) (q : ℕ) (R : Matrix (Fin W) (Fin W) ℂ)
    (ω : Ω W q) : ℕ → Matrix (Fin W) (Fin W) ℂ
  | 0 => 1
  | k + 1 => SmallGenerator_top W g E q R ω k * chartR W g E q R ω (q - 1 - k)

private lemma SmallGenerator_chartR_succ {W q : ℕ} (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ)
    (ω : Ω W q) {j : ℕ} (hj : 4 ≤ j) :
    chartR W g E q R ω (j + 1) =
      (blockSeq W q ω j - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • chartR W g E q R ω j)⁻¹ := by
  simp [chartR, not_lt.mpr hj]

private lemma SmallGenerator_chartProd_succ {W q : ℕ} (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ)
    (ω : Ω W q) {j : ℕ} (hj : 4 ≤ j) :
    chartProd W g E q R ω (j + 1) =
      chartR W g E q R ω (j + 1) * chartProd W g E q R ω j := by
  simp [chartProd, not_lt.mpr hj]

private lemma SmallGenerator_chartProd_four {W q : ℕ} (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ)
    (ω : Ω W q) : chartProd W g E q R ω 4 = 1 := by
  simp [chartProd]

private lemma SmallGenerator_chartR_four {W q : ℕ} (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ)
    (ω : Ω W q) : chartR W g E q R ω 4 = R := by
  simp [chartR]

private lemma SmallGenerator_top_eq {W q : ℕ} (g E : ℝ) (R : Matrix (Fin W) (Fin W) ℂ)
    (ω : Ω W q) : ∀ k, k + 5 ≤ q → chartProd W g E q R ω (q - 1) =
      SmallGenerator_top W g E q R ω k * chartProd W g E q R ω (q - 1 - k) := by
  intro k
  induction k with
  | zero => intro _; simp [SmallGenerator_top]
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have e1 : q - 1 - k = (q - 2 - k) + 1 := by omega
    have e2 : q - 1 - (k + 1) = q - 2 - k := by omega
    rw [h1, e1, SmallGenerator_chartProd_succ g E R ω (by omega), e2, ← Matrix.mul_assoc]
    simp only [SmallGenerator_top, e1]

private lemma SmallGenerator_cavN_mul {W q : ℕ} {g E : ℝ} (R : Matrix (Fin W) (Fin W) ℂ)
    (ω : Ω W q) {k : ℕ} (hk : IsUnit (cavR W g E q ω k)) :
    SmallGenerator_cavN W g E q R ω k * cavR W g E q ω k =
      1 - ((g : ℂ) ^ 2) • (chartR W g E q R ω (q - 2 - k) * cavR W g E q ω k) := by
  have hX : IsUnit (SmallGenerator_cavX W g E q ω k).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_nonsing_inv_iff.mp
      (by rwa [← SmallGenerator_cavR_eq]))
  unfold SmallGenerator_cavN
  rw [SmallGenerator_cavR_eq, Matrix.sub_mul, Matrix.mul_nonsing_inv _ hX, Matrix.smul_mul]

private lemma SmallGenerator_claim {W q : ℕ} {g E : ℝ} (R : Matrix (Fin W) (Fin W) ℂ)
    (ω : Ω W q)
    (hR : ∀ j, 5 ≤ j → j ≤ q - 1 → IsUnit (chartR W g E q R ω j))
    (hC : ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω m)) :
    ∀ k, k + 6 ≤ q → SmallGenerator_top W g E q R ω (k + 1) * SmallGenerator_cavN W g E q R ω k =
      cavProd W g E q ω k := by
  intro k
  induction k with
  | zero =>
    intro hk
    have e1 : q - 1 - 0 = (q - 2) + 1 := by omega
    have hu := hR (q - 1) (by omega) le_rfl
    have h0 : SmallGenerator_cavN W g E q R ω 0 =
        (blockSeq W q ω (q - 2) - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • chartR W g E q R ω (q - 2)) := by
      simp [SmallGenerator_cavN, SmallGenerator_cavX]
    have hc : chartR W g E q R ω (q - 1) =
        (SmallGenerator_cavN W g E q R ω 0)⁻¹ := by
      rw [h0, show q - 1 = (q - 2) + 1 by omega, SmallGenerator_chartR_succ g E R ω (by omega)]
    have hd : IsUnit (SmallGenerator_cavN W g E q R ω 0).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_nonsing_inv_iff.mp (hc ▸ hu))
    simp only [SmallGenerator_top, cavProd, Matrix.one_mul, Nat.sub_zero]
    rw [hc, Matrix.nonsing_inv_mul _ hd]
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    have hCk := hC k (by omega)
    have hRk := hR (q - 2 - k) (by omega) (by omega)
    have hcn := SmallGenerator_cavN_mul (g := g) (E := E) R ω hCk
    set j := q - 3 - k with hj
    have e1 : q - 2 - k = j + 1 := by omega
    have e2 : q - 1 - (k + 1) = j + 1 := by omega
    have hrj := SmallGenerator_chartR_succ g E R ω (j := j) (by omega)
    rw [e1] at hcn hRk
    set M := blockSeq W q ω j - (E : ℂ) • 1 - ((g : ℂ) ^ 2) • chartR W g E q R ω j with hM
    have hMd : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.isUnit_nonsing_inv_iff.mp (hrj ▸ hRk))
    have hN : SmallGenerator_cavN W g E q R ω (k + 1) = M - ((g : ℂ) ^ 2) • cavR W g E q ω k := by
      simp only [SmallGenerator_cavN, SmallGenerator_cavX, hM]
      rw [show q - 2 - (k + 1) = j by omega]
      abel
    have key : chartR W g E q R ω (j + 1) * SmallGenerator_cavN W g E q R ω (k + 1) =
        1 - ((g : ℂ) ^ 2) • (chartR W g E q R ω (j + 1) * cavR W g E q ω k) := by
      rw [hN, hrj, Matrix.mul_sub, Matrix.nonsing_inv_mul _ hMd, Matrix.mul_smul]
    calc SmallGenerator_top W g E q R ω (k + 1 + 1) * SmallGenerator_cavN W g E q R ω (k + 1)
        = SmallGenerator_top W g E q R ω (k + 1) *
            (chartR W g E q R ω (j + 1) * SmallGenerator_cavN W g E q R ω (k + 1)) := by
          simp only [SmallGenerator_top, e2, Matrix.mul_assoc]
      _ = SmallGenerator_top W g E q R ω (k + 1) *
            (SmallGenerator_cavN W g E q R ω k * cavR W g E q ω k) := by rw [key, hcn]
      _ = cavProd W g E q ω (k + 1) := by
          rw [← Matrix.mul_assoc, ih']; rfl

private lemma SmallGenerator_norm_sq_sum {W : ℕ} {u : Fin W → ℂ} :
    star u ⬝ᵥ u = ((∑ i, ‖u i‖ ^ 2 : ℝ) : ℂ) := by
  simp [dotProduct, Complex.conj_mul', Complex.ofReal_sum]

private lemma SmallGenerator_core {W : ℕ} {P : Matrix (Fin W) (Fin W) ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) {v : Fin W → ℂ} (hv : P *ᵥ v ≠ 0)
    (y : Fin W → ℂ) (hy : ∃ z, y = allowProj P v *ᵥ z) :
    ((star (P *ᵥ v) ⬝ᵥ (P *ᵥ v))⁻¹ •
        (Matrix.vecMulVec y (star (P *ᵥ v)) - Matrix.vecMulVec (P *ᵥ v) (star y)))ᴴ =
      -((star (P *ᵥ v) ⬝ᵥ (P *ᵥ v))⁻¹ •
        (Matrix.vecMulVec y (star (P *ᵥ v)) - Matrix.vecMulVec (P *ᵥ v) (star y))) ∧
    P * ((star (P *ᵥ v) ⬝ᵥ (P *ᵥ v))⁻¹ •
        (Matrix.vecMulVec y (star (P *ᵥ v)) - Matrix.vecMulVec (P *ᵥ v) (star y))) * P =
      (star (P *ᵥ v) ⬝ᵥ (P *ᵥ v))⁻¹ •
        (Matrix.vecMulVec y (star (P *ᵥ v)) - Matrix.vecMulVec (P *ᵥ v) (star y)) ∧
    ((star (P *ᵥ v) ⬝ᵥ (P *ᵥ v))⁻¹ •
        (Matrix.vecMulVec y (star (P *ᵥ v)) - Matrix.vecMulVec (P *ᵥ v) (star y))) *ᵥ v = y := by
  obtain ⟨z, rfl⟩ := hy
  set u := P *ᵥ v with hu
  have hPh : Pᴴ = P := hP.eq
  have hPu : P *ᵥ u = u := by rw [hu, Matrix.mulVec_mulVec, hPP]
  have hnr : star u ⬝ᵥ u = ((∑ i, ‖u i‖ ^ 2 : ℝ) : ℂ) := SmallGenerator_norm_sq_sum
  have hpos : 0 < ∑ i, ‖u i‖ ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    exact Finset.sum_pos' (fun j _ => by positivity)
      ⟨i, Finset.mem_univ _, by
        have : u i ≠ 0 := hi
        positivity⟩
  set c : ℝ := (∑ i, ‖u i‖ ^ 2)⁻¹ with hc
  have hcn : (star u ⬝ᵥ u)⁻¹ = (c : ℂ) := by rw [hnr, hc, Complex.ofReal_inv]
  have hcnn : (c : ℂ) * (star u ⬝ᵥ u) = 1 := by
    rw [← hcn]; exact inv_mul_cancel₀ (by rw [hnr]; exact_mod_cast hpos.ne')
  rw [hcn]
  have hsu : star u = star v ᵥ* P := by rw [hu, Matrix.star_mulVec, hPh]
  have hvu : star v ⬝ᵥ u = star u ⬝ᵥ u := by
    rw [hsu, ← Matrix.dotProduct_mulVec, hPu]
  have huv : star u ⬝ᵥ v = star u ⬝ᵥ u := by
    rw [hsu, ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec, hPu]
  have hsuP : star u ᵥ* P = star u := by
    rw [hsu, Matrix.vecMul_vecMul, hPP]
  have hPi_h : (allowProj P v)ᴴ = allowProj P v := by
    unfold allowProj
    rw [← hu, hcn, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_vecMulVec, star_star, hPh]
    simp
  have hPPi : P * allowProj P v = allowProj P v := by
    unfold allowProj
    rw [← hu, hcn, Matrix.mul_sub, hPP, Matrix.mul_smul, Matrix.mul_vecMulVec, hPu]
  have hPiv : allowProj P v *ᵥ v = 0 := by
    unfold allowProj
    rw [← hu, hcn, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
      op_smul_eq_smul, huv, smul_smul, hcnn, one_smul, ← hu, sub_self]
  have hy1 : P *ᵥ (allowProj P v *ᵥ z) = allowProj P v *ᵥ z := by
    rw [Matrix.mulVec_mulVec, hPPi]
  have hy2 : star (allowProj P v *ᵥ z) ⬝ᵥ v = 0 := by
    rw [Matrix.star_mulVec, hPi_h, ← Matrix.dotProduct_mulVec, hPiv, dotProduct_zero]
  set y := allowProj P v *ᵥ z with hy
  have hsy : star y ᵥ* P = star y := by
    conv_lhs => rw [← hPh]
    rw [← Matrix.star_mulVec, hy1]
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_vecMulVec,
      Matrix.conjTranspose_vecMulVec, star_star, star_star, ← smul_neg, neg_sub]
    simp
  · rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_vecMulVec,
      Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, hsuP, hsy, hPu, hy1]
  · rw [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec,
      op_smul_eq_smul, op_smul_eq_smul, huv, hy2, zero_smul, sub_zero, smul_smul, hcnn,
      one_smul]

private lemma SmallGenerator_blockSeq_herm {W q : ℕ} (ω : Ω W q) (k : ℕ) :
    (blockSeq W q ω k).IsHermitian := by
  unfold blockSeq
  split_ifs
  · exact gueBlock_isHermitian W q ω _
  · exact Matrix.isHermitian_zero

private lemma SmallGenerator_smul_herm {W : ℕ} (r : ℝ) {A : Matrix (Fin W) (Fin W) ℂ}
    (hA : A.IsHermitian) : ((r : ℂ) • A).IsHermitian := by
  unfold Matrix.IsHermitian at hA ⊢
  rw [Matrix.conjTranspose_smul, hA]
  simp

private lemma SmallGenerator_sq_smul_herm {W : ℕ} (g : ℝ) {A : Matrix (Fin W) (Fin W) ℂ}
    (hA : A.IsHermitian) : (((g : ℂ) ^ 2) • A).IsHermitian := by
  have := SmallGenerator_smul_herm (g ^ 2) hA
  simpa using this

private lemma SmallGenerator_cavR_herm {W q : ℕ} (g E : ℝ) (ω : Ω W q) (m : ℕ) :
    (cavR W g E q ω m).IsHermitian := by
  induction m with
  | zero =>
    rw [SmallGenerator_cavR_eq]
    exact ((SmallGenerator_blockSeq_herm ω _).sub
      (SmallGenerator_smul_herm E Matrix.isHermitian_one)).inv
  | succ m ih =>
    rw [SmallGenerator_cavR_eq, SmallGenerator_cavX_succ]
    exact (((SmallGenerator_blockSeq_herm ω _).sub
      (SmallGenerator_smul_herm E Matrix.isHermitian_one)).sub
      (SmallGenerator_sq_smul_herm g ih)).inv

private lemma SmallGenerator_cavRes_herm {W q : ℕ} (g E : ℝ) {R : Matrix (Fin W) (Fin W) ℂ}
    (hRh : R.IsHermitian) (ω : Ω W q) : (cavRes W g E q R ω).IsHermitian := by
  unfold cavRes
  exact ((((SmallGenerator_blockSeq_herm ω _).sub
    (SmallGenerator_smul_herm E Matrix.isHermitian_one)).sub
    (SmallGenerator_sq_smul_herm g hRh)).sub
    (SmallGenerator_sq_smul_herm g (SmallGenerator_cavR_herm g E ω _))).inv

private lemma SmallGenerator_Q_alg {W : ℕ} (Q Pi : Matrix (Fin W) (Fin W) ℂ) (hQQ : Q * Q = Q)
    (hB : IsUnit (Q * Pi * Q + (1 - Q))) :
    Q * (Pi * Q * (Q * Pi * Q + (1 - Q))⁻¹ * Q) = Q := by
  have hBd : IsUnit (Q * Pi * Q + (1 - Q)).det := (Matrix.isUnit_iff_isUnit_det _).mp hB
  have hQB : Q * (Q * Pi * Q + (1 - Q)) = Q * Pi * Q := by
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hQQ]
    abel
  calc Q * (Pi * Q * (Q * Pi * Q + (1 - Q))⁻¹ * Q)
      = (Q * Pi * Q) * (Q * Pi * Q + (1 - Q))⁻¹ * Q := by simp only [Matrix.mul_assoc]
    _ = (Q * (Q * Pi * Q + (1 - Q))) * (Q * Pi * Q + (1 - Q))⁻¹ * Q := by rw [hQB]
    _ = Q * ((Q * Pi * Q + (1 - Q)) * (Q * Pi * Q + (1 - Q))⁻¹) * Q := by
        simp only [Matrix.mul_assoc]
    _ = Q := by rw [Matrix.mul_nonsing_inv _ hBd, Matrix.mul_one, hQQ]

/-- (3.4) [us:eq:cavity]: `R_{[q-1,5]} = A R̃` where all the inverses exist. -/
theorem chartProd_eq_cavProd_mul {W q : ℕ} {g E : ℝ} (hq : 7 ≤ q)
    (R : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q)
    (hR : ∀ j, 5 ≤ j → j ≤ q - 1 → IsUnit (chartR W g E q R ω j))
    (hC : ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω m)) (hT : IsUnit (cavRes W g E q R ω)) :
    chartProd W g E q R ω (q - 1) = cavProd W g E q ω (q - 6) * cavRes W g E q R ω := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 7 := ⟨q - 7, by omega⟩
  have hcl := SmallGenerator_claim R ω hR hC (n + 1) (by omega)
  have htop := SmallGenerator_top_eq g E R ω (n + 2) (by omega)
  rw [show n + 7 - 1 - (n + 2) = 4 by omega, SmallGenerator_chartProd_four] at htop
  rw [Matrix.mul_one] at htop
  have hres : cavRes W g E (n + 7) R ω =
      (SmallGenerator_cavN W g E (n + 7) R ω (n + 1))⁻¹ := by
    unfold cavRes SmallGenerator_cavN
    rw [SmallGenerator_cavX_succ, show n + 7 - 2 - (n + 1) = 4 by omega,
      show n + 7 - 3 - n = 4 by omega, show n + 7 - 7 = n by omega, SmallGenerator_chartR_four]
    congr 1
    abel
  have hd : IsUnit (SmallGenerator_cavN W g E (n + 7) R ω (n + 1)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_nonsing_inv_iff.mp (hres ▸ hT))
  rw [htop, hres, show n + 7 - 6 = n + 1 by omega, ← hcl, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]

/-- (9.16) [us:eq:H0], (9.18) [us:eq:normalize]: for an orthogonal projection `P` with
`P v ≠ 0`, `K_0* = -K_0`, `K_0 = P K_0 P` and `K_0 v = y`; if moreover `ξ ≠ 0`, then `K* = -K`,
`K = P K P` and `K` satisfies (9.8) [su:eq:generator-normalization]. -/
theorem smallGen_spec {W q : ℕ} {g E : ℝ} (R : Matrix (Fin W) (Fin W) ℂ) (t : ℝ)
    {P : Matrix (Fin W) (Fin W) ℂ} (hP : P.IsHermitian) (hPP : P * P = P) (ω : Ω W q)
    {v : Fin W → ℂ} (hv : P *ᵥ v ≠ 0) :
    ((gen0 W g E q R t P ω v)ᴴ = -gen0 W g E q R t P ω v ∧
      P * gen0 W g E q R t P ω v * P = gen0 W g E q R t P ω v ∧
      gen0 W g E q R t P ω v *ᵥ v = srcVec W g E q R t P ω v) ∧
    (genScale W g E q R t P ω v ≠ 0 →
      (smallGen W g E q R t P ω v)ᴴ = -smallGen W g E q R t P ω v ∧
      P * smallGen W g E q R t P ω v * P = smallGen W g E q R t P ω v ∧
      IsGenNormalized W g E q R v (smallGen W g E q R t P ω v) ω) := by
  have hy : ∃ z, srcVec W g E q R t P ω v = allowProj P v *ᵥ z := by
    refine ⟨(retProj W g E q R t ω *
      (retProj W g E q R t ω * allowProj P v * retProj W g E q R t ω +
        (1 - retProj W g E q R t ω))⁻¹ * retProj W g E q R t ω) *ᵥ v, ?_⟩
    unfold srcVec
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mul_assoc]
  have h0 : ((gen0 W g E q R t P ω v)ᴴ = -gen0 W g E q R t P ω v ∧
      P * gen0 W g E q R t P ω v * P = gen0 W g E q R t P ω v ∧
      gen0 W g E q R t P ω v *ᵥ v = srcVec W g E q R t P ω v) :=
    SmallGenerator_core hP hPP hv _ hy
  refine ⟨h0, fun hξ => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h0
  have hs : smallGen W g E q R t P ω v =
      (((genScale W g E q R t P ω v)⁻¹ : ℝ) : ℂ) • gen0 W g E q R t P ω v := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hs, Matrix.conjTranspose_smul, h1]
    simp
  · rw [hs, Matrix.mul_smul, Matrix.smul_mul, h2]
  · unfold IsGenNormalized
    rw [hs, Matrix.smul_mulVec, h3, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
      Complex.re_ofReal_mul]
    have hx : genScale W g E q R t P ω v =
        (star (chartProd W g E q R ω (q - 1) *ᵥ v) ⬝ᵥ
          (chartProd W g E q R ω (q - 1) *ᵥ srcVec W g E q R t P ω v)).re /
        ∑ i, ‖(chartProd W g E q R ω (q - 1) *ᵥ v) i‖ ^ 2 := rfl
    rw [hx] at hξ ⊢
    obtain ⟨hnum, hden⟩ := div_ne_zero_iff.mp hξ
    field_simp

/-- (9.17) [us:eq:error]: `R_{[q-1,5]} (y - v) = e_{q-1}`, where the inverses of (3.4)
[us:eq:cavity] exist, `R_4` is Hermitian and `B_Q = Q Π Q|_{ran Q}` is invertible. -/
theorem discErr_eq {W q : ℕ} {g E : ℝ} (hq : 7 ≤ q) {R : Matrix (Fin W) (Fin W) ℂ}
    (hRh : R.IsHermitian) (t : ℝ) (P : Matrix (Fin W) (Fin W) ℂ) (ω : Ω W q) (v : Fin W → ℂ)
    (hR : ∀ j, 5 ≤ j → j ≤ q - 1 → IsUnit (chartR W g E q R ω j))
    (hC : ∀ m, m ≤ q - 7 → IsUnit (cavR W g E q ω m)) (hT : IsUnit (cavRes W g E q R ω))
    (hB : IsUnit (retProj W g E q R t ω * allowProj P v * retProj W g E q R t ω +
      (1 - retProj W g E q R t ω))) :
    chartProd W g E q R ω (q - 1) *ᵥ (srcVec W g E q R t P ω v - v) =
      discErr W g E q R t P ω v := by
  have hRt := SmallGenerator_cavRes_herm g E hRh ω
  have hAh : ((cavProd W g E q ω (q - 6))ᴴ * cavProd W g E q ω (q - 6)).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_self _
  obtain ⟨hSh, hSS, -, -⟩ := specProj_spec hAh (Set.Ioi (t ^ 2))
  obtain ⟨hQh, hQQ, hQR⟩ := flagProj_spec hT hSh hSS
  obtain ⟨-, -⟩ := specProj_add_compl hAh (Set.Ioi (t ^ 2))
  have hsum := (specProj_add_compl hAh (Set.Ioi (t ^ 2))).1
  rw [Set.compl_Ioi] at hsum
  set A := cavProd W g E q ω (q - 6) with hA
  set S := specProj (Aᴴ * A) (Set.Ioi (t ^ 2)) with hS
  set S' := specProj (Aᴴ * A) (Set.Iic (t ^ 2)) with hS'
  set Rt := cavRes W g E q R ω with hRtdef
  set Q := retProj W g E q R t ω with hQ
  set Pi := allowProj P v with hPi
  have hQR' : Q * (Rt * S) = Rt * S := hQR
  have hQh' : Qᴴ = Q := hQh
  have hSRQ : S * Rt * Q = S * Rt := by
    have := congrArg Matrix.conjTranspose hQR'
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSh.eq, hRt.eq, hQh'] at this
    exact this
  have hQM : Q * (Pi * Q * (Q * Pi * Q + (1 - Q))⁻¹ * Q) = Q :=
    SmallGenerator_Q_alg Q Pi hQQ hB
  have hQw : Q *ᵥ (srcVec W g E q R t P ω v - v) = 0 := by
    have hy : Q *ᵥ srcVec W g E q R t P ω v = Q *ᵥ v := by
      unfold srcVec
      rw [Matrix.mulVec_mulVec]
      exact congrArg (· *ᵥ v) hQM
    rw [Matrix.mulVec_sub, hy, sub_self]
  have hAS : A * Rt = A * S * Rt + A * S' * Rt := by
    rw [← Matrix.add_mul, ← Matrix.mul_add, hsum, Matrix.mul_one]
  have hzero : (A * S * Rt) *ᵥ (srcVec W g E q R t P ω v - v) = 0 := by
    have : A * S * Rt = A * (S * Rt * Q) := by rw [hSRQ, Matrix.mul_assoc]
    rw [this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hQw]
    simp
  rw [chartProd_eq_cavProd_mul hq R ω hR hC hT, discErr]
  rw [hAS, Matrix.add_mulVec, hzero, zero_add]

end LSBA
