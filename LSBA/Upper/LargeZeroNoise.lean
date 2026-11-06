import LSBA.Transfer.Transition
import LSBA.Gauss.GUEContract
import LSBA.Gauss.GUENormMoment

/-!
# Zero-noise limits of products of observables

For all `k, l ∈ ℤ`, the one-step mean of a product of two observables of (11.10) [lg:eq:observables]
is its zero-noise value up to `K/g²`: `‖P_g(φ_k ψ_l) − (−e^{−2iθ})^{k+l} φ_k ψ_l‖ ≤ K/g²`, for every
`g ≥ 1`, `W ≥ 1` and state, with `K` depending only on `E₀`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Expansions in the step size `t`

A function `a` of the block `V` has *zero-noise value* `a₀` with constant `K` and degree `r` when
its even part is `a₀ + O(t²)` and its odd part is `O(t)`, with remainders `K t^j (1 + ‖V‖)^r`
for Hermitian `V`. -/

/-- `a` has the zero-noise value `a₀` with constant `K` and degree `r` at step size `t`. -/
private def ZG {𝔸 : Type*} [NormedAddCommGroup 𝔸] [NormedSpace ℂ 𝔸] {W : ℕ} (t K : ℝ) (r : ℕ)
    (a : Matrix (Fin W) (Fin W) ℂ → 𝔸) (a₀ : 𝔸) : Prop :=
  ‖a₀‖ ≤ K ∧ ∀ V : Matrix (Fin W) (Fin W) ℂ, V.IsHermitian →
    ‖a V - a (-V)‖ ≤ K * t * (1 + ‖V‖) ^ r ∧
      ‖a V + a (-V) - (2 : ℂ) • a₀‖ ≤ K * t ^ 2 * (1 + ‖V‖) ^ r

private lemma zn_one_le {x : ℝ} (hx : 0 ≤ x) (r : ℕ) : 1 ≤ (1 + x) ^ r :=
  one_le_pow₀ (by linarith)

private lemma zn_norm_two_smul {𝔸 : Type*} [NormedAddCommGroup 𝔸] [NormedSpace ℂ 𝔸] (x : 𝔸) :
    ‖(2 : ℂ) • x‖ = 2 * ‖x‖ := by
  rw [norm_smul]
  norm_num

private lemma zn_K_nonneg {𝔸 : Type*} [NormedAddCommGroup 𝔸] [NormedSpace ℂ 𝔸] {W : ℕ}
    {t K : ℝ} {r : ℕ} {a : Matrix (Fin W) (Fin W) ℂ → 𝔸} {a₀ : 𝔸} (h : ZG t K r a a₀) :
    0 ≤ K :=
  (norm_nonneg _).trans h.1

private lemma zn_norm_le {𝔸 : Type*} [NormedAddCommGroup 𝔸] [NormedSpace ℂ 𝔸] {W : ℕ}
    {t K : ℝ} {r : ℕ} {a : Matrix (Fin W) (Fin W) ℂ → 𝔸} {a₀ : 𝔸} (h : ZG t K r a a₀)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) :
    ‖a V‖ ≤ 2 * K * (1 + ‖V‖) ^ r := by
  have hK := zn_K_nonneg h
  obtain ⟨h0, h⟩ := h
  obtain ⟨h1, h2⟩ := h V hV
  have hP := zn_one_le (norm_nonneg V) r
  set P := (1 + ‖V‖) ^ r with hPdef
  have e : (2 : ℂ) • a V = (a V - a (-V)) + (a V + a (-V) - (2 : ℂ) • a₀) + (2 : ℂ) • a₀ := by
    rw [two_smul, two_smul]; abel
  have hn : 2 * ‖a V‖ ≤ ‖a V - a (-V)‖ + ‖a V + a (-V) - (2 : ℂ) • a₀‖ + 2 * ‖a₀‖ := by
    rw [← zn_norm_two_smul, e]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _)) ?_
    rw [zn_norm_two_smul]
  have a1 : K * t * P ≤ K * P := by
    have : K * P * t ≤ K * P * 1 := mul_le_mul_of_nonneg_left ht1 (by positivity)
    nlinarith
  have a2 : K * t ^ 2 * P ≤ K * P := by
    have : t ^ 2 ≤ 1 := by nlinarith
    have : K * P * t ^ 2 ≤ K * P * 1 := mul_le_mul_of_nonneg_left this (by positivity)
    nlinarith
  have a3 : K ≤ K * P := by nlinarith
  nlinarith

private lemma zn_const {𝔸 : Type*} [NormedAddCommGroup 𝔸] [NormedSpace ℂ 𝔸] {W : ℕ} {t K : ℝ}
    {c : 𝔸} (hc : ‖c‖ ≤ K) (ht0 : 0 ≤ t) (r : ℕ) :
    ZG (W := W) t K r (fun _ => c) c := by
  have hK : 0 ≤ K := (norm_nonneg _).trans hc
  refine ⟨hc, fun V _ => ⟨?_, ?_⟩⟩
  · simp only [sub_self, norm_zero]
    positivity
  · rw [two_smul, sub_self, norm_zero]
    positivity

private lemma zn_congr {𝔸 : Type*} [NormedAddCommGroup 𝔸] [NormedSpace ℂ 𝔸] {W : ℕ} {t K : ℝ}
    {r : ℕ} {a b : Matrix (Fin W) (Fin W) ℂ → 𝔸} {a₀ : 𝔸}
    (hab : ∀ V : Matrix (Fin W) (Fin W) ℂ, V.IsHermitian → a V = b V) (h : ZG t K r a a₀) :
    ZG t K r b a₀ := by
  refine ⟨h.1, fun V hV => ?_⟩
  have := h.2 V hV
  rwa [hab V hV, hab (-V) hV.neg] at this

private lemma zn_mono {𝔸 : Type*} [NormedAddCommGroup 𝔸] [NormedSpace ℂ 𝔸] {W : ℕ} {t K K' : ℝ}
    {r r' : ℕ} {a : Matrix (Fin W) (Fin W) ℂ → 𝔸} {a₀ : 𝔸} (h : ZG t K r a a₀) (hK : K ≤ K')
    (hr : r ≤ r') (ht0 : 0 ≤ t) : ZG t K' r' a a₀ := by
  refine ⟨h.1.trans hK, fun V hV => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 V hV
  have hP : (1 + ‖V‖) ^ r ≤ (1 + ‖V‖) ^ r' :=
    pow_le_pow_right₀ (by linarith [norm_nonneg V]) hr
  have hK0 := zn_K_nonneg h
  have hK'0 : 0 ≤ K' := hK0.trans hK
  refine ⟨h1.trans ?_, h2.trans ?_⟩
  · gcongr
  · gcongr

private lemma zn_add {𝔸 : Type*} [NormedAddCommGroup 𝔸] [NormedSpace ℂ 𝔸] {W : ℕ} {t K K' : ℝ}
    {r : ℕ} {a b : Matrix (Fin W) (Fin W) ℂ → 𝔸} {a₀ b₀ : 𝔸} (ha : ZG t K r a a₀)
    (hb : ZG t K' r b b₀) : ZG t (K + K') r (fun V => a V + b V) (a₀ + b₀) := by
  refine ⟨(norm_add_le _ _).trans (add_le_add ha.1 hb.1), fun V hV => ?_⟩
  obtain ⟨h1, h2⟩ := ha.2 V hV
  obtain ⟨h1', h2'⟩ := hb.2 V hV
  constructor
  · have e : a V + b V - (a (-V) + b (-V)) = (a V - a (-V)) + (b V - b (-V)) := by abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    nlinarith
  · have e : a V + b V + (a (-V) + b (-V)) - (2 : ℂ) • (a₀ + b₀) =
        (a V + a (-V) - (2 : ℂ) • a₀) + (b V + b (-V) - (2 : ℂ) • b₀) := by
      rw [smul_add]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    nlinarith

private lemma zn_smul {𝔸 : Type*} [NormedAddCommGroup 𝔸] [NormedSpace ℂ 𝔸] {W : ℕ} {t K : ℝ}
    {r : ℕ} {a : Matrix (Fin W) (Fin W) ℂ → 𝔸} {a₀ : 𝔸} (h : ZG t K r a a₀) {c : ℂ}
    (hc : ‖c‖ ≤ 1) : ZG t K r (fun V => c • a V) (c • a₀) := by
  have hK := zn_K_nonneg h
  refine ⟨?_, fun V hV => ?_⟩
  · rw [norm_smul]
    calc ‖c‖ * ‖a₀‖ ≤ 1 * K := mul_le_mul hc h.1 (norm_nonneg _) zero_le_one
      _ = K := one_mul K
  obtain ⟨h1, h2⟩ := h.2 V hV
  constructor
  · rw [← smul_sub, norm_smul]
    calc ‖c‖ * ‖a V - a (-V)‖ ≤ 1 * (K * t * (1 + ‖V‖) ^ r) :=
          mul_le_mul hc h1 (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  · have e : c • a V + c • a (-V) - (2 : ℂ) • c • a₀ = c • (a V + a (-V) - (2 : ℂ) • a₀) := by
      rw [smul_sub, smul_add, smul_comm (2 : ℂ) c a₀]
    rw [e, norm_smul]
    calc ‖c‖ * ‖a V + a (-V) - (2 : ℂ) • a₀‖ ≤ 1 * (K * t ^ 2 * (1 + ‖V‖) ^ r) :=
          mul_le_mul hc h2 (norm_nonneg _) zero_le_one
      _ = _ := one_mul _

private lemma zn_nm {𝔸 : Type*} [NormedRing 𝔸] {u v : 𝔸} {α β : ℝ} (hu : ‖u‖ ≤ α)
    (hv : ‖v‖ ≤ β) (hα : 0 ≤ α) : ‖u * v‖ ≤ α * β :=
  (norm_mul_le _ _).trans (mul_le_mul hu hv (norm_nonneg _) hα)

private lemma zn_mul {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] {W : ℕ} {t K K' : ℝ}
    {r r' : ℕ} {a b : Matrix (Fin W) (Fin W) ℂ → 𝔸} {a₀ b₀ : 𝔸} (ha : ZG t K r a a₀)
    (hb : ZG t K' r' b b₀) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ZG t (4 * K * K') (r + r') (fun V => a V * b V) (a₀ * b₀) := by
  have hK := zn_K_nonneg ha
  have hK' := zn_K_nonneg hb
  refine ⟨?_, fun V hV => ?_⟩
  · calc ‖a₀ * b₀‖ ≤ K * K' := zn_nm ha.1 hb.1 hK
      _ ≤ 4 * K * K' := by nlinarith [mul_nonneg hK hK']
  have hna := zn_norm_le ha ht0 ht1 hV
  have hna' := zn_norm_le ha ht0 ht1 hV.neg
  have hnb := zn_norm_le hb ht0 ht1 hV
  have hnb' := zn_norm_le hb ht0 ht1 hV.neg
  rw [norm_neg] at hna' hnb'
  obtain ⟨ha1, ha2⟩ := ha.2 V hV
  obtain ⟨hb1, hb2⟩ := hb.2 V hV
  have hP := zn_one_le (norm_nonneg V) r
  have hQ := zn_one_le (norm_nonneg V) r'
  rw [pow_add]
  set P := (1 + ‖V‖) ^ r
  set Q := (1 + ‖V‖) ^ r'
  set x := a V
  set x' := a (-V)
  set y := b V
  set y' := b (-V)
  have hP0 : 0 ≤ P := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hKP : 0 ≤ K * P := by positivity
  have hKQ : 0 ≤ K' * Q := by positivity
  have hs : ‖y + y'‖ ≤ 4 * K' * Q := by
    calc ‖y + y'‖ ≤ ‖y‖ + ‖y'‖ := norm_add_le _ _
      _ ≤ 4 * K' * Q := by linarith
  have hs' : ‖x + x'‖ ≤ 4 * K * P := by
    calc ‖x + x'‖ ≤ ‖x‖ + ‖x'‖ := norm_add_le _ _
      _ ≤ 4 * K * P := by linarith
  have hKt : 0 ≤ K * t := by positivity
  constructor
  · have e : (2 : ℂ) • (x * y - x' * y') = (x - x') * (y + y') + (x + x') * (y - y') := by
      rw [smul_sub, two_smul, two_smul]
      noncomm_ring
    have h1 : ‖(x - x') * (y + y')‖ ≤ (K * t * P) * (4 * K' * Q) :=
      zn_nm ha1 hs (by positivity)
    have h2 : ‖(x + x') * (y - y')‖ ≤ (4 * K * P) * (K' * t * Q) :=
      zn_nm hs' hb1 (by positivity)
    have h3 : 2 * ‖x * y - x' * y'‖ ≤ 8 * K * K' * t * (P * Q) := by
      rw [← zn_norm_two_smul, e]
      refine (norm_add_le _ _).trans ?_
      nlinarith
    nlinarith [mul_nonneg (mul_nonneg hK hK') ht0, mul_nonneg hP0 hQ0]
  · have e : (2 : ℂ) • (x * y + x' * y' - (2 : ℂ) • (a₀ * b₀)) =
        (x + x' - (2 : ℂ) • a₀) * (y + y') + (2 : ℂ) • (a₀ * (y + y' - (2 : ℂ) • b₀)) +
          (x - x') * (y - y') := by
      simp only [smul_sub, two_smul, mul_add, mul_sub, add_mul, sub_mul]
      noncomm_ring
    have h1 : ‖(x + x' - (2 : ℂ) • a₀) * (y + y')‖ ≤ (K * t ^ 2 * P) * (4 * K' * Q) :=
      zn_nm ha2 hs (by positivity)
    have h2 : ‖a₀ * (y + y' - (2 : ℂ) • b₀)‖ ≤ K * (K' * t ^ 2 * Q) :=
      zn_nm ha.1 hb2 hK
    have h3 : ‖(x - x') * (y - y')‖ ≤ (K * t * P) * (K' * t * Q) :=
      zn_nm ha1 hb1 (by positivity)
    have h4 : 2 * ‖x * y + x' * y' - (2 : ℂ) • (a₀ * b₀)‖ ≤
        4 * (K * K' * t ^ 2) * (P * Q) * 2 := by
      rw [← zn_norm_two_smul, e]
      have h5 : K * (K' * t ^ 2 * Q) ≤ K * K' * t ^ 2 * (P * Q) := by
        have : 0 ≤ K * K' * t ^ 2 * Q := by positivity
        nlinarith
      have h6 := norm_add_le ((x + x' - (2 : ℂ) • a₀) * (y + y'))
        ((2 : ℂ) • (a₀ * (y + y' - (2 : ℂ) • b₀)))
      have h7 := norm_add_le ((x + x' - (2 : ℂ) • a₀) * (y + y') +
        (2 : ℂ) • (a₀ * (y + y' - (2 : ℂ) • b₀))) ((x - x') * (y - y'))
      rw [zn_norm_two_smul] at h6
      have hA : 0 ≤ K * K' * t ^ 2 * (P * Q) := by positivity
      linarith
    nlinarith [mul_nonneg (mul_nonneg hK hK') (sq_nonneg t), mul_nonneg hP0 hQ0]

private lemma zn_pow {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] {W : ℕ}
    {t K : ℝ} {r : ℕ} {a : Matrix (Fin W) (Fin W) ℂ → 𝔸} {a₀ : 𝔸} (h : ZG t K r a a₀)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) :
    ZG t (4 ^ n * K ^ n) (n * r) (fun V => a V ^ n) (a₀ ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero, zero_mul, one_mul]
    exact zn_const (by simp) ht0 0
  | succ n ih =>
    have h1 := zn_mul ih h ht0 ht1
    rw [← pow_succ] at h1
    refine zn_mono (zn_congr (fun V _ => (pow_succ _ _).symm) h1) (le_of_eq (by ring))
      (le_of_eq (by ring)) ht0

private lemma zn_star {W : ℕ} {t K : ℝ} {r : ℕ}
    {a : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ} {a₀ : Matrix (Fin W) (Fin W) ℂ}
    (h : ZG t K r a a₀) : ZG t K r (fun V => (a V)ᴴ) a₀ᴴ := by
  refine ⟨by rw [Matrix.l2_opNorm_conjTranspose]; exact h.1, fun V hV => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 V hV
  constructor
  · rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
    exact h1
  · have e : (a V)ᴴ + (a (-V))ᴴ - (2 : ℂ) • a₀ᴴ = (a V + a (-V) - (2 : ℂ) • a₀)ᴴ := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_smul]
      simp
    rw [e, Matrix.l2_opNorm_conjTranspose]
    exact h2

private lemma zn_lin {𝔸 𝔹 : Type*} [NormedAddCommGroup 𝔸] [NormedSpace ℂ 𝔸]
    [NormedAddCommGroup 𝔹] [NormedSpace ℂ 𝔹] {W : ℕ} {t K : ℝ} {r : ℕ}
    {a : Matrix (Fin W) (Fin W) ℂ → 𝔸} {a₀ : 𝔸} (Φ : 𝔸 →ₗ[ℂ] 𝔹) (hΦ : ∀ x, ‖Φ x‖ ≤ ‖x‖)
    (h : ZG t K r a a₀) : ZG t K r (fun V => Φ (a V)) (Φ a₀) := by
  refine ⟨(hΦ _).trans h.1, fun V hV => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 V hV
  constructor
  · rw [← map_sub]
    exact (hΦ _).trans h1
  · have e : Φ (a V) + Φ (a (-V)) - (2 : ℂ) • Φ a₀ = Φ (a V + a (-V) - (2 : ℂ) • a₀) := by
      rw [map_sub, map_add, map_smul]
    rw [e]
    exact (hΦ _).trans h2

private lemma zn_of_odd {𝔸 : Type*} [NormedAddCommGroup 𝔸] [NormedSpace ℂ 𝔸] {W : ℕ} {t B : ℝ}
    {r : ℕ} {a : Matrix (Fin W) (Fin W) ℂ → 𝔸} (hB : 0 ≤ B)
    (hodd : ∀ V : Matrix (Fin W) (Fin W) ℂ, V.IsHermitian → a (-V) = -a V)
    (hb : ∀ V : Matrix (Fin W) (Fin W) ℂ, V.IsHermitian → ‖a V‖ ≤ B * t * (1 + ‖V‖) ^ r) :
    ZG t (2 * B) r a 0 := by
  refine ⟨by simp; linarith, fun V hV => ⟨?_, ?_⟩⟩
  · rw [hodd V hV, sub_neg_eq_add]
    calc ‖a V + a V‖ ≤ ‖a V‖ + ‖a V‖ := norm_add_le _ _
      _ ≤ 2 * B * t * (1 + ‖V‖) ^ r := by linarith [hb V hV]
  · rw [hodd V hV, smul_zero, add_neg_cancel, sub_zero, norm_zero]
    have := zn_one_le (norm_nonneg V) r
    positivity

private lemma zn_of_small {𝔸 : Type*} [NormedAddCommGroup 𝔸] [NormedSpace ℂ 𝔸] {W : ℕ}
    {t B : ℝ} {r : ℕ} {a : Matrix (Fin W) (Fin W) ℂ → 𝔸} (hB : 0 ≤ B) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1)
    (hb : ∀ V : Matrix (Fin W) (Fin W) ℂ, V.IsHermitian →
      ‖a V‖ ≤ B * t ^ 2 * (1 + ‖V‖) ^ r) : ZG t (2 * B) r a 0 := by
  refine ⟨by simp; linarith, fun V hV => ?_⟩
  have h1 := hb V hV
  have h2 := hb (-V) hV.neg
  rw [norm_neg] at h2
  have hP := zn_one_le (norm_nonneg V) r
  have ht2 : t ^ 2 ≤ t := by nlinarith
  have hBP : 0 ≤ B * (1 + ‖V‖) ^ r := by positivity
  constructor
  · calc ‖a V - a (-V)‖ ≤ ‖a V‖ + ‖a (-V)‖ := norm_sub_le _ _
      _ ≤ 2 * B * t * (1 + ‖V‖) ^ r := by nlinarith
  · rw [smul_zero, sub_zero]
    calc ‖a V + a (-V)‖ ≤ ‖a V‖ + ‖a (-V)‖ := norm_add_le _ _
      _ ≤ 2 * B * t ^ 2 * (1 + ‖V‖) ^ r := by nlinarith

private lemma zn_inv {W : ℕ} {t K L : ℝ} {r q : ℕ} {d : Matrix (Fin W) (Fin W) ℂ → ℂ}
    (hd : ZG t K r d 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hne : ∀ V : Matrix (Fin W) (Fin W) ℂ, V.IsHermitian → d V ≠ 0)
    (hL : ∀ V : Matrix (Fin W) (Fin W) ℂ, V.IsHermitian → ‖(d V)⁻¹‖ ≤ L * (1 + ‖V‖) ^ q) :
    ZG t (1 + L ^ 2 * (K + K ^ 2)) (2 * r + 2 * q) (fun V => (d V)⁻¹) 1 := by
  have hK := zn_K_nonneg hd
  have hL0 : 0 ≤ L := by
    have h := hL 0 Matrix.isHermitian_zero
    simp only [norm_zero, add_zero, one_pow, mul_one] at h
    exact (norm_nonneg _).trans h
  have hc : 0 ≤ 1 + L ^ 2 * (K + K ^ 2) := by positivity
  refine ⟨by rw [norm_one]; nlinarith [mul_nonneg (sq_nonneg L) (add_nonneg hK (sq_nonneg K))],
    fun V hV => ?_⟩
  obtain ⟨h1, h2⟩ := hd.2 V hV
  have hx := hne V hV
  have hx' := hne (-V) hV.neg
  have hix := hL V hV
  have hix' := hL (-V) hV.neg
  rw [norm_neg] at hix'
  set S : ℝ := 1 + ‖V‖ with hS
  have hS1 : 1 ≤ S := by rw [hS]; linarith [norm_nonneg V]
  set x := d V
  set x' := d (-V)
  rw [smul_eq_mul, mul_one] at h2
  set Q : ℝ := S ^ q with hQ
  set P : ℝ := S ^ r with hP
  have hP1 : 1 ≤ P := one_le_pow₀ hS1
  have hQ1 : 1 ≤ Q := one_le_pow₀ hS1
  have hPP : P ≤ S ^ (2 * r) := pow_le_pow_right₀ hS1 (by omega)
  have hQQ : Q ^ 2 = S ^ (2 * q) := by rw [hQ, ← pow_mul, mul_comm]
  have hSS : S ^ (2 * r + 2 * q) = S ^ (2 * r) * Q ^ 2 := by rw [pow_add, hQQ]
  have hnn : ‖x⁻¹ * x'⁻¹‖ ≤ (L * Q) * (L * Q) := zn_nm hix hix' (by positivity)
  have hLQ : 0 ≤ (L * Q) * (L * Q) := by positivity
  have hP0 : 0 ≤ P := by linarith
  constructor
  · have e : x⁻¹ - x'⁻¹ = x⁻¹ * x'⁻¹ * (x' - x) := by field_simp
    rw [e, norm_mul]
    have h3 : ‖x' - x‖ ≤ K * t * P := by rw [norm_sub_rev]; exact h1
    have h4 : ‖x⁻¹ * x'⁻¹‖ * ‖x' - x‖ ≤ ((L * Q) * (L * Q)) * (K * t * P) :=
      mul_le_mul hnn h3 (norm_nonneg _) hLQ
    have h5 : ((L * Q) * (L * Q)) * (K * t * P) ≤
        (1 + L ^ 2 * (K + K ^ 2)) * t * S ^ (2 * r + 2 * q) := by
      rw [hSS]
      have h7 : P * Q ^ 2 ≤ S ^ (2 * r) * Q ^ 2 := mul_le_mul_of_nonneg_right hPP (by positivity)
      have h8 : 0 ≤ L ^ 2 * K * t := by positivity
      have h9 := mul_le_mul_of_nonneg_left h7 h8
      have h10 : 0 ≤ t * (S ^ (2 * r) * Q ^ 2) * (1 + L ^ 2 * K ^ 2) := by positivity
      have hfin : (1 + L ^ 2 * (K + K ^ 2)) * t * (S ^ (2 * r) * Q ^ 2) =
          L ^ 2 * K * t * (S ^ (2 * r) * Q ^ 2) +
            t * (S ^ (2 * r) * Q ^ 2) * (1 + L ^ 2 * K ^ 2) := by ring
      have hlhs : ((L * Q) * (L * Q)) * (K * t * P) = L ^ 2 * K * t * (P * Q ^ 2) := by ring
      rw [hlhs, hfin]
      linarith
    linarith
  · have e : x⁻¹ + x'⁻¹ - (2 : ℂ) • (1 : ℂ) = x⁻¹ * x'⁻¹ *
        (-(x + x' - 2) - ((x + x' - 2) ^ 2 - (x - x') ^ 2) / 2) := by
      rw [smul_eq_mul, mul_one]
      field_simp
      ring
    rw [e, norm_mul]
    set e₁ : ℂ := x + x' - 2 with he₁
    set o₁ : ℂ := x - x' with ho₁
    have hb : ‖-e₁ - (e₁ ^ 2 - o₁ ^ 2) / 2‖ ≤ ‖e₁‖ + (‖e₁‖ ^ 2 + ‖o₁‖ ^ 2) / 2 := by
      calc ‖-e₁ - (e₁ ^ 2 - o₁ ^ 2) / 2‖ ≤ ‖-e₁‖ + ‖(e₁ ^ 2 - o₁ ^ 2) / 2‖ := norm_sub_le _ _
        _ ≤ ‖e₁‖ + (‖e₁‖ ^ 2 + ‖o₁‖ ^ 2) / 2 := by
          rw [norm_neg, norm_div]
          have h2' : ‖(2 : ℂ)‖ = 2 := by norm_num
          rw [h2']
          have : ‖e₁ ^ 2 - o₁ ^ 2‖ ≤ ‖e₁‖ ^ 2 + ‖o₁‖ ^ 2 := by
            refine (norm_sub_le _ _).trans ?_
            rw [norm_pow, norm_pow]
          linarith
    have ha1 : ‖e₁‖ ≤ K * t ^ 2 * P := h2
    have ha2 : ‖o₁‖ ≤ K * t * P := h1
    have hn1 : 0 ≤ ‖e₁‖ := norm_nonneg _
    have hn2 : 0 ≤ ‖o₁‖ := norm_nonneg _
    have ht2 : t ^ 2 ≤ 1 := by nlinarith
    have h3 : ‖e₁‖ + (‖e₁‖ ^ 2 + ‖o₁‖ ^ 2) / 2 ≤ (K + K ^ 2) * t ^ 2 * S ^ (2 * r) := by
      have hPS : P ^ 2 ≤ S ^ (2 * r) := by rw [hP, ← pow_mul, mul_comm]
      have hPS' : P ≤ S ^ (2 * r) := hPP
      have h4 : ‖e₁‖ ^ 2 ≤ (K * t ^ 2 * P) ^ 2 := pow_le_pow_left₀ hn1 ha1 2
      have h5 : ‖o₁‖ ^ 2 ≤ (K * t * P) ^ 2 := pow_le_pow_left₀ hn2 ha2 2
      have h6 : (K * t ^ 2 * P) ^ 2 ≤ K ^ 2 * t ^ 2 * P ^ 2 := by
        have : (K * t ^ 2 * P) ^ 2 = K ^ 2 * t ^ 2 * P ^ 2 * t ^ 2 := by ring
        rw [this]
        have : 0 ≤ K ^ 2 * t ^ 2 * P ^ 2 := by positivity
        nlinarith
      have h7 : (K * t * P) ^ 2 = K ^ 2 * t ^ 2 * P ^ 2 := by ring
      have h8 : K * t ^ 2 * P ≤ K * t ^ 2 * S ^ (2 * r) := by
        have : 0 ≤ K * t ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left hPS' this
      have h9 : K ^ 2 * t ^ 2 * P ^ 2 ≤ K ^ 2 * t ^ 2 * S ^ (2 * r) := by
        have : 0 ≤ K ^ 2 * t ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left hPS this
      nlinarith
    have h4 : ‖x⁻¹ * x'⁻¹‖ * ‖-e₁ - (e₁ ^ 2 - o₁ ^ 2) / 2‖ ≤
        ((L * Q) * (L * Q)) * ((K + K ^ 2) * t ^ 2 * S ^ (2 * r)) :=
      mul_le_mul hnn (hb.trans h3) (norm_nonneg _) hLQ
    refine h4.trans ?_
    rw [hSS]
    have hfin : (1 + L ^ 2 * (K + K ^ 2)) * t ^ 2 * (S ^ (2 * r) * Q ^ 2) =
        ((L * Q) * (L * Q)) * ((K + K ^ 2) * t ^ 2 * S ^ (2 * r)) +
          t ^ 2 * (S ^ (2 * r) * Q ^ 2) := by ring
    rw [hfin]
    have h5 : 0 ≤ t ^ 2 * (S ^ (2 * r) * Q ^ 2) := by positivity
    linarith

/-! ### The one-step update as an expansion in `t = h_θ / g` -/

private lemma zn_normalH_nonneg (E : ℝ) : 0 ≤ normalH E := by
  unfold normalH freeAngle
  have h := Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg (E / 2))
    (Real.arccos_le_pi (E / 2))
  positivity

/-- `h_θ ≤ (2 √(1 − E₀²/4))⁻¹` for `|E| ≤ E₀ < 2`. -/
private lemma zn_normalH_le {E₀ E : ℝ} (hE₀ : E₀ < 2) (hE : |E| ≤ E₀) :
    normalH E ≤ (2 * √(1 - E₀ ^ 2 / 4))⁻¹ := by
  unfold normalH freeAngle
  rw [Real.sin_arccos]
  have ha := abs_nonneg E
  have h1 : E ^ 2 ≤ E₀ ^ 2 := by
    rw [← sq_abs E]
    exact pow_le_pow_left₀ ha hE 2
  have h2 : 0 < 1 - E₀ ^ 2 / 4 := by nlinarith
  have h3 : √(1 - E₀ ^ 2 / 4) ≤ √(1 - (E / 2) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  have h4 : 0 < √(1 - E₀ ^ 2 / 4) := Real.sqrt_pos.mpr h2
  exact inv_anti₀ (by positivity) (by linarith)

private lemma zn_norm_normalPhase (E : ℝ) : ‖normalPhase E‖ = 1 := by
  unfold normalPhase
  rw [norm_neg, show 2 * ((freeAngle E : ℂ) * Complex.I) =
    ((2 * freeAngle E : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma zn_star_normalPhase_mul (E : ℝ) : star (normalPhase E) * normalPhase E = 1 := by
  unfold normalPhase
  rw [star_neg, neg_mul_neg, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat,
    show (2 : ℂ) * (↑(freeAngle E) * -Complex.I) + 2 * (↑(freeAngle E) * Complex.I) = 0 by ring,
    Complex.exp_zero]

private lemma zn_isUnit_det {W : ℕ} {C : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) : IsUnit C.det :=
  Matrix.isUnit_det_of_right_inverse (Matrix.mem_unitaryGroup_iff.mp hC)

private lemma zn_inv_eq {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin W) ℂ) : U⁻¹ = Uᴴ := by
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.star_eq_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff.mp hU

private lemma zn_zpow_mem {W : ℕ} {C : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (k : ℤ) : C ^ k ∈ Matrix.unitaryGroup (Fin W) ℂ := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [zpow_natCast]
    exact pow_mem hC n
  · rw [Matrix.zpow_neg (zn_isUnit_det hC), zpow_natCast,
      zn_inv_eq (pow_mem hC n), ← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem (pow_mem hC n)

private lemma zn_zpow_neg {W : ℕ} {C : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (k : ℤ) : C ^ (-k) = (C ^ k)ᴴ := by
  rw [Matrix.zpow_neg (zn_isUnit_det hC), zn_inv_eq (zn_zpow_mem hC k)]

private lemma zn_norm_lin_le {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W)) : ‖Matrix.toEuclideanLin A v‖ ≤ ‖A‖ * ‖v‖ :=
  (Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) A).le_opNorm v

private lemma zn_norm_vecForm_le {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ)
    {v : EuclideanSpace ℂ (Fin W)} (hv : ‖v‖ = 1) : ‖vecForm A v‖ ≤ ‖A‖ := by
  unfold vecForm
  calc ‖inner ℂ v (Matrix.toEuclideanLin A v)‖ ≤ ‖v‖ * ‖Matrix.toEuclideanLin A v‖ :=
        norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖A‖ * ‖v‖) := by gcongr; exact zn_norm_lin_le A v
    _ = ‖A‖ := by rw [hv]; ring

private lemma zn_diag_eq_vecForm {W : ℕ} (U : Matrix (Fin W) (Fin W) ℂ) (i : Fin W) :
    U i i = vecForm U (EuclideanSpace.single i (1 : ℂ)) := by
  unfold vecForm
  simp [Matrix.toLpLin_apply, EuclideanSpace.inner_single_left]

/-- The normalized trace has norm at most the operator norm. -/
private lemma zn_norm_trace_le {W : ℕ} (hW : 1 ≤ W) (B : Matrix (Fin W) (Fin W) ℂ) :
    ‖(W : ℂ)⁻¹ * B.trace‖ ≤ ‖B‖ := by
  have hd : ∀ i : Fin W, ‖B i i‖ ≤ ‖B‖ := fun i => by
    rw [zn_diag_eq_vecForm B i]
    exact zn_norm_vecForm_le B (by simp)
  have htr : ‖B.trace‖ ≤ W * ‖B‖ := by
    calc ‖B.trace‖ = ‖∑ i, B i i‖ := rfl
      _ ≤ ∑ i, ‖B i i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin W, ‖B‖ := Finset.sum_le_sum fun i _ => hd i
      _ = W * ‖B‖ := by simp
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (W : ℝ)⁻¹ * ‖B.trace‖ ≤ (W : ℝ)⁻¹ * (W * ‖B‖) := by gcongr
    _ = ‖B‖ := by field_simp

/-- `B ↦ W⁻¹ Tr B` as a linear map. -/
private def znTr (W : ℕ) : Matrix (Fin W) (Fin W) ℂ →ₗ[ℂ] ℂ where
  toFun B := (W : ℂ)⁻¹ * B.trace
  map_add' A B := by rw [Matrix.trace_add]; ring
  map_smul' c A := by rw [Matrix.trace_smul]; simp only [smul_eq_mul, RingHom.id_apply]; ring

/-- `B ↦ v* B v` as a linear map. -/
private def znVec {W : ℕ} (v : EuclideanSpace ℂ (Fin W)) :
    Matrix (Fin W) (Fin W) ℂ →ₗ[ℂ] ℂ where
  toFun B := vecForm B v
  map_add' A B := by
    unfold vecForm
    rw [map_add, LinearMap.add_apply, inner_add_right]
  map_smul' c A := by
    unfold vecForm
    rw [map_smul, LinearMap.smul_apply, inner_smul_right]
    rfl

private lemma zn_mat_one_add {W : ℕ} (hW : 1 ≤ W) {C : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) :
    ‖C‖ = 1 ∧ ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ = 1 ∧ ‖1 + C‖ ≤ 2 := by
  have : Nonempty (Fin W) := ⟨⟨0, hW⟩⟩
  have hnC : ‖C‖ = 1 := CStarRing.norm_of_mem_unitary hC
  have h1 : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ = 1 := norm_one
  refine ⟨hnC, h1, ?_⟩
  calc ‖1 + C‖ ≤ ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ + ‖C‖ := norm_add_le _ _
    _ = 2 := by rw [h1, hnC]; norm_num

private lemma zn_Xn {W : ℕ} (hW : 1 ≤ W) {g E : ℝ} (hg : 0 < g)
    {C : Matrix (Fin W) (Fin W) ℂ} (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ)
    (V : Matrix (Fin W) (Fin W) ℂ) :
    ‖(Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C))‖ ≤
      2 * (normalH E / g) * (1 + ‖V‖) := by
  obtain ⟨hnC, hn1, hn2⟩ := zn_mat_one_add hW hC
  have ht0 : 0 ≤ normalH E / g := div_nonneg (zn_normalH_nonneg E) hg.le
  have hnc : ‖Complex.I * ((normalH E / g : ℝ) : ℂ)‖ = normalH E / g := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
  rw [norm_smul, hnc]
  calc normalH E / g * ‖V * (1 + C)‖ ≤ normalH E / g * (‖V‖ * 2) := by
        gcongr
        exact (norm_mul_le _ _).trans (by gcongr)
    _ ≤ 2 * (normalH E / g) * (1 + ‖V‖) := by nlinarith [norm_nonneg V]

/-- The first-order term `i t V (I + C)` of the update is odd in `V`. -/
private lemma zn_X {W : ℕ} (hW : 1 ≤ W) {g E : ℝ} (hg : 0 < g)
    {C : Matrix (Fin W) (Fin W) ℂ} (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) :
    ZG (normalH E / g) (2 * 2) 1
      (fun V => (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C))) 0 := by
  refine zn_of_odd (B := 2) (by norm_num) (fun V _ => ?_) (fun V _ => ?_)
  · simp only [neg_mul, smul_neg]
  · have := zn_Xn hW hg hC (E := E) V
    rw [pow_one]
    linarith

/-- `F(C, V)⁻¹ = I + O(t)` with the first-order term odd in `V` (the Neumann expansion of
(11.3) [lg:eq:matrix-update] to second order). -/
private lemma zn_finv {W : ℕ} (hW : 1 ≤ W) {g E : ℝ} (hg : 0 < g) (ht1 : normalH E / g ≤ 1)
    {C : Matrix (Fin W) (Fin W) ℂ} (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) :
    ZG (normalH E / g) 21 3 (fun V => (stepF g E C V)⁻¹) 1 := by
  obtain ⟨hnC, hn1, hn2⟩ := zn_mat_one_add hW hC
  have ht0 : 0 ≤ normalH E / g := div_nonneg (zn_normalH_nonneg E) hg.le
  have hX := zn_X hW hg hC (E := E)
  have hS : ZG (normalH E / g) (2 * 8) 3 (fun V =>
      ((Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C))) ^ 2 * (stepF g E C V)⁻¹) 0 := by
    refine zn_of_small (B := 8) (by norm_num) ht0 ht1 (fun V hV => ?_)
    have hF := (norm_stepF_le hg E hC hV).2
    have hF' : ‖(stepF g E C V)⁻¹‖ ≤ 2 * (1 + ‖V‖) := by
      have : 2 * normalH E * ‖V‖ / g = 2 * (normalH E / g) * ‖V‖ := by ring
      rw [this] at hF
      nlinarith [norm_nonneg V]
    have hP := zn_one_le (norm_nonneg V) 3
    have h1 : ‖((Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C))) ^ 2‖ ≤
        (2 * (normalH E / g) * (1 + ‖V‖)) ^ 2 :=
      (norm_pow_le' _ (by norm_num : 0 < 2)).trans
        (pow_le_pow_left₀ (norm_nonneg _) (zn_Xn hW hg hC V) 2)
    calc ‖((Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C))) ^ 2 * (stepF g E C V)⁻¹‖
        ≤ (2 * (normalH E / g) * (1 + ‖V‖)) ^ 2 * (2 * (1 + ‖V‖)) :=
          zn_nm h1 hF' (by positivity)
      _ = 8 * (normalH E / g) ^ 2 * (1 + ‖V‖) ^ 3 := by ring
  have h1 : ZG (W := W) (normalH E / g) 1 3 (fun _ => (1 : Matrix (Fin W) (Fin W) ℂ)) 1 :=
    zn_mono (zn_const (by rw [hn1]) ht0 0) le_rfl (by norm_num) ht0
  have hsum := zn_add h1 (zn_add (zn_mono hX le_rfl (by norm_num) ht0) hS)
  rw [add_zero, add_zero] at hsum
  refine zn_mono (zn_congr (fun V hV => ?_) hsum) (by norm_num) le_rfl ht0
  have e := inv_stepF_eq_sum_add g E hC hV 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] at e
  rw [add_assoc] at e
  exact e.symm

/-- `C' = −e^{−2iθ} C + O(t)` with the first-order term odd in `V`: the one-step update (11.3)
[lg:eq:matrix-update] of the unitary matrix. -/
private lemma zn_stepC {W : ℕ} (hW : 1 ≤ W) {g E : ℝ} (hg : 0 < g) (ht1 : normalH E / g ≤ 1)
    {C : Matrix (Fin W) (Fin W) ℂ} (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) :
    ZG (normalH E / g) 3000 4 (fun V => stepC g E C V) ((-normalPhase E) • C) := by
  obtain ⟨hnC, hn1, hn2⟩ := zn_mat_one_add hW hC
  have ht0 : 0 ≤ normalH E / g := div_nonneg (zn_normalH_nonneg E) hg.le
  have hX := zn_X hW hg hC (E := E)
  have hF := zn_finv hW hg ht1 hC
  have hq := zn_mul (zn_mul (zn_const (c := 1 + C) (K := 2) hn2 ht0 0) hX ht0 ht1) hF ht0 ht1
  have hq' := zn_smul hq (c := -normalPhase E) (by rw [norm_neg, zn_norm_normalPhase])
  have hcn : ‖(-normalPhase E) • C‖ ≤ 1 := by
    rw [norm_smul, norm_neg, zn_norm_normalPhase, hnC]; norm_num
  have hsum := zn_add (zn_mono (zn_const (c := (-normalPhase E) • C) (K := 1) hcn ht0 0) le_rfl
    (by norm_num : 0 ≤ 0 + 1 + 3) ht0) hq'
  simp only [mul_zero, zero_mul, smul_zero, add_zero] at hsum
  refine zn_mono (zn_congr (fun V hV => ?_) hsum) (by norm_num) (by norm_num) ht0
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_stepF g E hC hV)
  have hFF : stepF g E C V * (stepF g E C V)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hF1 : stepF g E C V =
      1 - (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C)) := rfl
  have key : (C + (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C))) *
      (stepF g E C V)⁻¹ = C + (1 + C) *
        ((Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C))) * (stepF g E C V)⁻¹ := by
    have h2 : (C + (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C))) *
        (stepF g E C V)⁻¹ = C * (stepF g E C V * (stepF g E C V)⁻¹) + (1 + C) *
        ((Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C))) * (stepF g E C V)⁻¹ := by
      generalize (stepF g E C V)⁻¹ = Fi
      generalize (Complex.I * ((normalH E / g : ℝ) : ℂ)) • (V * (1 + C)) = X at hF1 ⊢
      rw [hF1]
      noncomm_ring
    rw [h2, hFF, mul_one]
  unfold stepC
  rw [key, smul_add]

/-- Integer powers of the update: `C'^k = (−e^{−2iθ})^k C^k + O(t)` with an odd first-order
term. -/
private lemma zn_stepC_zpow {W : ℕ} (hW : 1 ≤ W) {g E : ℝ} (hg : 0 < g)
    (ht1 : normalH E / g ≤ 1) {C : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (k : ℤ) :
    ZG (normalH E / g) (4 ^ k.natAbs * 3000 ^ k.natAbs) (k.natAbs * 4)
      (fun V => stepC g E C V ^ k) ((-normalPhase E) ^ k • C ^ k) := by
  have : Nonempty (Fin W) := ⟨⟨0, hW⟩⟩
  have ht0 : 0 ≤ normalH E / g := div_nonneg (zn_normalH_nonneg E) hg.le
  have hB := zn_stepC hW hg ht1 hC
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · have h := zn_pow hB ht0 ht1 n
    rw [smul_pow] at h
    simpa [zpow_natCast] using h
  · have h := zn_star (zn_pow hB ht0 ht1 n)
    have hstar : star (-normalPhase E) = (-normalPhase E)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [star_neg, neg_mul_neg]
      exact zn_star_normalPhase_mul E
    have h0 : ((((-normalPhase E) • C) ^ n)ᴴ) = (-normalPhase E) ^ (-(n : ℤ)) • C ^ (-(n : ℤ)) := by
      rw [smul_pow, Matrix.conjTranspose_smul, star_pow, hstar, zn_zpow_neg hC, zpow_neg]
      simp only [zpow_natCast, inv_pow]
    rw [h0] at h
    rw [Int.natAbs_neg, Int.natAbs_natCast]
    refine zn_congr (fun V hV => ?_) h
    rw [zn_zpow_neg (stepC_mem_unitaryGroup g E hC hV), zpow_natCast]

/-- The observable `m_k` along the update: `m_k(X') = (−e^{−2iθ})^k m_k(X) + O(t)`, odd first-order
term. -/
private lemma zn_obsM {W : ℕ} (hW : 1 ≤ W) {g E : ℝ} (hg : 0 < g) (ht1 : normalH E / g ≤ 1)
    {X : State W} (hX : IsState X) (k : ℤ) :
    ZG (normalH E / g) (4 ^ k.natAbs * 3000 ^ k.natAbs) (k.natAbs * 4)
      (fun V => obsM k (stepState g E X V)) ((-normalPhase E) ^ k * obsM k X) := by
  have h := zn_lin (znTr W) (fun B => zn_norm_trace_le hW B) (zn_stepC_zpow hW hg ht1 hX.1 k)
  have e : znTr W ((-normalPhase E) ^ k • X.1 ^ k) = (-normalPhase E) ^ k * obsM k X := by
    change (W : ℂ)⁻¹ * ((-normalPhase E) ^ k • X.1 ^ k).trace = _
    rw [Matrix.trace_smul, smul_eq_mul]
    unfold obsM
    ring
  rw [e] at h
  exact h

private lemma zn_lin_mul {W : ℕ} (A B : Matrix (Fin W) (Fin W) ℂ) (v : EuclideanSpace ℂ (Fin W)) :
    Matrix.toEuclideanLin (A * B) v = Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

private lemma zn_lin_one {W : ℕ} (v : EuclideanSpace ℂ (Fin W)) :
    Matrix.toEuclideanLin (1 : Matrix (Fin W) (Fin W) ℂ) v = v := by
  simp

private lemma zn_inner_lin_conjTranspose {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ)
    (v w : EuclideanSpace ℂ (Fin W)) :
    inner ℂ v (Matrix.toEuclideanLin Aᴴ w) = inner ℂ (Matrix.toEuclideanLin A v) w := by
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]

private lemma zn_norm_stepPhase (E : ℝ) : ‖stepPhase E‖ = 1 := by
  unfold stepPhase
  rw [show -((freeAngle E : ℂ) * Complex.I) = ((-freeAngle E : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The conjugated update matrix `N_l = F⁻¹ C'^l F⁻ᴴ`, whose quadratic form at `v` is the numerator
of `f_l(X')`. -/
private def znN (g E : ℝ) {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) (l : ℤ) :
    Matrix (Fin W) (Fin W) ℂ :=
  (stepF g E C V)⁻¹ * stepC g E C V ^ l * ((stepF g E C V)⁻¹)ᴴ

private lemma zn_vecForm_N {W : ℕ} (A B : Matrix (Fin W) (Fin W) ℂ) (v : EuclideanSpace ℂ (Fin W)) :
    vecForm (A * B * Aᴴ) v = vecForm B (Matrix.toEuclideanLin Aᴴ v) := by
  unfold vecForm
  rw [zn_lin_mul, zn_lin_mul]
  have h := zn_inner_lin_conjTranspose Aᴴ v (Matrix.toEuclideanLin B (Matrix.toEuclideanLin Aᴴ v))
  rw [Matrix.conjTranspose_conjTranspose] at h
  exact h

private lemma zn_stepVec_adj (g E : ℝ) {W : ℕ} {X : State W} (hX : IsState X)
    {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) :
    Matrix.toEuclideanLin (stepF g E X.1 V)ᴴ (stepVec g E X V) = X.2 := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_stepF g E hX.1 hV)
  unfold stepVec
  rw [← zn_lin_mul, ← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hdet,
    Matrix.conjTranspose_one, zn_lin_one]

/-- `‖F⁻ᴴ v‖ ≥ (1 + 2 t ‖V‖)⁻¹` for a unit vector `v`. -/
private lemma zn_norm_stepVec_ge {g E : ℝ} (hg : 0 < g) {W : ℕ} {X : State W} (hX : IsState X)
    {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) :
    (1 + 2 * (normalH E / g) * ‖V‖)⁻¹ ≤ ‖stepVec g E X V‖ := by
  have hF := (norm_stepF_le hg E hX.1 hV).1
  have hL : 0 < 1 + 2 * (normalH E / g) * ‖V‖ := by
    have : 0 ≤ normalH E / g := div_nonneg (zn_normalH_nonneg E) hg.le
    positivity
  have e : 2 * normalH E * ‖V‖ / g = 2 * (normalH E / g) * ‖V‖ := by ring
  rw [e] at hF
  rw [inv_le_iff_one_le_mul₀ hL]
  calc (1 : ℝ) = ‖X.2‖ := hX.2.symm
    _ = ‖Matrix.toEuclideanLin (stepF g E X.1 V)ᴴ (stepVec g E X V)‖ := by
      rw [zn_stepVec_adj g E hX hV]
    _ ≤ ‖(stepF g E X.1 V)ᴴ‖ * ‖stepVec g E X V‖ := zn_norm_lin_le _ _
    _ = ‖stepF g E X.1 V‖ * ‖stepVec g E X V‖ := by rw [Matrix.l2_opNorm_conjTranspose]
    _ ≤ (1 + 2 * (normalH E / g) * ‖V‖) * ‖stepVec g E X V‖ := by gcongr
    _ = ‖stepVec g E X V‖ * (1 + 2 * (normalH E / g) * ‖V‖) := mul_comm _ _

/-- The normalized value at the updated state: `f_l(X') = (v* N_l v) / (v* N_0 v)`, where
`v* N_0 v = ‖F⁻ᴴ v‖²`. -/
private lemma zn_obsF_eq {g E : ℝ} (hg : 0 < g) {W : ℕ} {X : State W} (hX : IsState X)
    {V : Matrix (Fin W) (Fin W) ℂ} (hV : V.IsHermitian) (l : ℤ) :
    obsF l (stepState g E X V) =
      vecForm (znN g E X.1 V l) X.2 * (vecForm (znN g E X.1 V 0) X.2)⁻¹ ∧
    vecForm (znN g E X.1 V 0) X.2 = ((‖stepVec g E X V‖ ^ 2 : ℝ) : ℂ) ∧
    ‖stepVec g E X V‖ ≠ 0 := by
  have hge := zn_norm_stepVec_ge (E := E) hg hX hV
  have hL : 0 < 1 + 2 * (normalH E / g) * ‖V‖ := by
    have : 0 ≤ normalH E / g := div_nonneg (zn_normalH_nonneg E) hg.le
    positivity
  have hw : 0 < ‖stepVec g E X V‖ := lt_of_lt_of_le (inv_pos.mpr hL) hge
  set w := stepVec g E X V with hwdef
  have hwv : ∀ B : Matrix (Fin W) (Fin W) ℂ,
      vecForm ((stepF g E X.1 V)⁻¹ * B * ((stepF g E X.1 V)⁻¹)ᴴ) X.2 = vecForm B w := by
    intro B
    rw [zn_vecForm_N]
    rfl
  have hd : vecForm (znN g E X.1 V 0) X.2 = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    unfold znN
    rw [zpow_zero, hwv]
    unfold vecForm
    rw [zn_lin_one, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  refine ⟨?_, hd, hw.ne'⟩
  have hn : vecForm (znN g E X.1 V l) X.2 = vecForm (stepC g E X.1 V ^ l) w := by
    unfold znN
    exact hwv _
  rw [hn, hd]
  change vecForm (stepC g E X.1 V ^ l) ((stepPhase E * ((‖w‖⁻¹ : ℝ) : ℂ)) • w) = _
  set s : ℂ := stepPhase E * ((‖w‖⁻¹ : ℝ) : ℂ) with hs
  have hsn : ‖s‖ = ‖w‖⁻¹ := by
    rw [hs, norm_mul, zn_norm_stepPhase, Complex.norm_real, norm_inv, norm_norm, one_mul]
  have hss : (starRingEnd ℂ) s * s = (((‖w‖⁻¹) ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul', hsn]
    push_cast
    rfl
  unfold vecForm
  rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, hss]
  have hw0 : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  push_cast
  field_simp

/-- The constant of the numerator expansion of `f_l(X')`. -/
private def znKN (l : ℤ) : ℝ := 4 * (4 * 21 * (4 ^ l.natAbs * 3000 ^ l.natAbs)) * 21

/-- The degree of the numerator expansion of `f_l(X')`. -/
private def znRN (l : ℤ) : ℕ := 3 + l.natAbs * 4 + 3

/-- The numerator `v* N_l v` of `f_l(X')` has the zero-noise value `(−e^{−2iθ})^l f_l(X)`. -/
private lemma zn_numF {W : ℕ} (hW : 1 ≤ W) {g E : ℝ} (hg : 0 < g) (ht1 : normalH E / g ≤ 1)
    {X : State W} (hX : IsState X) (l : ℤ) :
    ZG (normalH E / g) (znKN l) (znRN l) (fun V => vecForm (znN g E X.1 V l) X.2)
      ((-normalPhase E) ^ l * obsF l X) := by
  have ht0 : 0 ≤ normalH E / g := div_nonneg (zn_normalH_nonneg E) hg.le
  have hF := zn_finv hW hg ht1 hX.1
  have h := zn_mul (zn_mul hF (zn_stepC_zpow hW hg ht1 hX.1 l) ht0 ht1) (zn_star hF) ht0 ht1
  rw [Matrix.conjTranspose_one, one_mul, mul_one] at h
  have h' := zn_lin (znVec X.2) (fun B => zn_norm_vecForm_le B hX.2) h
  have e : znVec X.2 ((-normalPhase E) ^ l • X.1 ^ l) = (-normalPhase E) ^ l * obsF l X := by
    change vecForm ((-normalPhase E) ^ l • X.1 ^ l) X.2 = _
    unfold vecForm obsF
    rw [map_smul, LinearMap.smul_apply, inner_smul_right]
    rfl
  rw [e] at h'
  exact zn_mono (zn_congr (fun V _ => rfl) h') (le_of_eq (by unfold znKN; ring))
    (le_of_eq (by unfold znRN; ring)) ht0

/-- The observable `f_l` along the update: `f_l(X') = (−e^{−2iθ})^l f_l(X) + O(t)`, odd
first-order term. -/
private lemma zn_obsF {W : ℕ} (hW : 1 ≤ W) {g E : ℝ} (hg : 0 < g) (ht1 : normalH E / g ≤ 1)
    {X : State W} (hX : IsState X) (l : ℤ) :
    ZG (normalH E / g) (4 * znKN l * (1 + 4 ^ 2 * (znKN 0 + znKN 0 ^ 2)))
      (znRN l + (2 * znRN 0 + 2 * 2)) (fun V => obsF l (stepState g E X V))
      ((-normalPhase E) ^ l * obsF l X) := by
  have ht0 : 0 ≤ normalH E / g := div_nonneg (zn_normalH_nonneg E) hg.le
  have hd := zn_numF hW hg ht1 hX 0
  rw [zpow_zero, (obsF_zero_neg hX 0).1, one_mul] at hd
  have hne : ∀ V : Matrix (Fin W) (Fin W) ℂ, V.IsHermitian →
      vecForm (znN g E X.1 V 0) X.2 ≠ 0 := by
    intro V hV
    obtain ⟨-, h2, h3⟩ := zn_obsF_eq hg hX hV (E := E) 0
    rw [h2]
    exact_mod_cast pow_ne_zero 2 h3
  have hL : ∀ V : Matrix (Fin W) (Fin W) ℂ, V.IsHermitian →
      ‖(vecForm (znN g E X.1 V 0) X.2)⁻¹‖ ≤ 4 * (1 + ‖V‖) ^ 2 := by
    intro V hV
    obtain ⟨-, h2, h3⟩ := zn_obsF_eq hg hX hV (E := E) 0
    have hge := zn_norm_stepVec_ge (E := E) hg hX hV
    have hL0 : 0 < 1 + 2 * (normalH E / g) * ‖V‖ := by positivity
    have hw : 0 < ‖stepVec g E X V‖ := lt_of_lt_of_le (inv_pos.mpr hL0) hge
    rw [h2, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have h4 : ‖stepVec g E X V‖⁻¹ ≤ 1 + 2 * (normalH E / g) * ‖V‖ := by
      rw [inv_le_comm₀ hw hL0]
      exact hge
    have h5 : 1 + 2 * (normalH E / g) * ‖V‖ ≤ 2 * (1 + ‖V‖) := by
      nlinarith [norm_nonneg V]
    calc (‖stepVec g E X V‖ ^ 2)⁻¹ = (‖stepVec g E X V‖⁻¹) ^ 2 := by rw [inv_pow]
      _ ≤ (2 * (1 + ‖V‖)) ^ 2 := by
        gcongr
        exact h4.trans h5
      _ = 4 * (1 + ‖V‖) ^ 2 := by ring
  have hinv := zn_inv hd ht0 ht1 hne hL
  have hprod := zn_mul (zn_numF hW hg ht1 hX l) hinv ht0 ht1
  rw [mul_one] at hprod
  exact zn_congr (fun V hV => (zn_obsF_eq hg hX hV l).1.symm) hprod

/-! ### Integration over one block -/

private lemma zn_measurable_gb (W : ℕ) : Measurable fun ω : Ω W 1 => gueBlock W 1 ω 0 := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

private lemma zn_pow_le {x : ℝ} (hx : 0 ≤ x) (r : ℕ) : (1 + x) ^ r ≤ 2 ^ r * (1 + x ^ r) := by
  have h := add_pow_le zero_le_one hx r
  rw [one_pow] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le r 1)

/-- `𝔼 (1 + ‖V‖)^r ≤ M` uniformly in `W`. -/
private lemma zn_moment (r : ℕ) : ∃ M : ℝ, 0 < M ∧ ∀ W : ℕ,
    Integrable (fun ω : Ω W 1 => (1 + ‖gueBlock W 1 ω 0‖) ^ r) (μ W 1) ∧
      ∫ ω, (1 + ‖gueBlock W 1 ω 0‖) ^ r ∂(μ W 1) ≤ M := by
  obtain ⟨C, hC, h⟩ := lintegral_norm_gueBlock_pow_le r
  refine ⟨2 ^ r * (1 + C), by positivity, fun W => ?_⟩
  have hdom : Integrable (fun ω : Ω W 1 => 2 ^ r * (1 + ‖gueBlock W 1 ω 0‖ ^ r)) (μ W 1) :=
    ((integrable_const (1 : ℝ)).add (integrable_norm_gueBlock_pow W r)).const_mul _
  have hmeas : Measurable fun ω : Ω W 1 => (1 + ‖gueBlock W 1 ω 0‖) ^ r :=
    (measurable_const.add (measurable_norm.comp (zn_measurable_gb W))).pow_const r
  have hint : Integrable (fun ω : Ω W 1 => (1 + ‖gueBlock W 1 ω 0‖) ^ r) (μ W 1) :=
    hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact zn_pow_le (norm_nonneg _) r)
  refine ⟨hint, ?_⟩
  have hn : ∫ ω, ‖gueBlock W 1 ω 0‖ ^ r ∂(μ W 1) ≤ C := by
    have h1 := ofReal_integral_eq_lintegral_ofReal (integrable_norm_gueBlock_pow W r)
      (Filter.Eventually.of_forall fun ω => by positivity)
    have h2 : ∫⁻ ω, ENNReal.ofReal (‖gueBlock W 1 ω 0‖ ^ r) ∂(μ W 1) =
        ∫⁻ ω, ‖gueBlock W 1 ω 0‖ₑ ^ r ∂(μ W 1) := by
      refine lintegral_congr fun ω => ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rw [h2] at h1
    exact (ENNReal.ofReal_le_ofReal_iff hC.le).mp (h1.trans_le (h W))
  calc ∫ ω, (1 + ‖gueBlock W 1 ω 0‖) ^ r ∂(μ W 1)
      ≤ ∫ ω, 2 ^ r * (1 + ‖gueBlock W 1 ω 0‖ ^ r) ∂(μ W 1) :=
        integral_mono hint hdom fun ω => zn_pow_le (norm_nonneg _) r
    _ = 2 ^ r * (1 + ∫ ω, ‖gueBlock W 1 ω 0‖ ^ r ∂(μ W 1)) := by
        rw [integral_const_mul, integral_add (integrable_const _)
          (integrable_norm_gueBlock_pow W r)]
        simp
    _ ≤ 2 ^ r * (1 + C) := by gcongr

/-- A measurable function bounded by `1` on Hermitian blocks, with zero-noise value `a₀`, has
one-block mean `a₀ + O(t²)`: the odd part is discarded by the symmetry `V ↦ -V` of the law, and the
even remainder is integrated against the norm moments. -/
private lemma zn_integral {W : ℕ} {t K : ℝ} {r : ℕ} {a : Matrix (Fin W) (Fin W) ℂ → ℂ} {a₀ : ℂ}
    (h : ZG t K r a a₀) (ha : Measurable a)
    (hb : ∀ V : Matrix (Fin W) (Fin W) ℂ, V.IsHermitian → ‖a V‖ ≤ 1) {M : ℝ}
    (hM : Integrable (fun ω : Ω W 1 => (1 + ‖gueBlock W 1 ω 0‖) ^ r) (μ W 1))
    (hMb : ∫ ω, (1 + ‖gueBlock W 1 ω 0‖) ^ r ∂(μ W 1) ≤ M) :
    ‖∫ ω, a (gueBlock W 1 ω 0) ∂(μ W 1) - a₀‖ ≤ K * t ^ 2 * M := by
  have hK := zn_K_nonneg h
  have hgb := zn_measurable_gb W
  have hi : Integrable (fun ω : Ω W 1 => a (gueBlock W 1 ω 0)) (μ W 1) :=
    Integrable.of_bound (ha.comp hgb).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => hb _ (gueBlock_isHermitian W 1 ω 0))
  have hj : Integrable (fun ω : Ω W 1 => a (-gueBlock W 1 ω 0)) (μ W 1) :=
    Integrable.of_bound (ha.comp hgb.neg).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => hb _ (gueBlock_isHermitian W 1 ω 0).neg)
  have hodd := integral_odd_gueBlock (G := ℂ) W (fun V => a V - a (-V))
    (fun V => by simp only [neg_neg]; abel)
  rw [integral_sub hi hj] at hodd
  have hadd : Integrable (fun ω : Ω W 1 => a (gueBlock W 1 ω 0) + a (-gueBlock W 1 ω 0))
      (μ W 1) := hi.add hj
  have e1 := integral_sub hadd (integrable_const ((2 : ℂ) • a₀)) (μ := μ W 1)
  have e2 : ∫ ω, (a (gueBlock W 1 ω 0) + a (-gueBlock W 1 ω 0)) ∂(μ W 1) =
      ∫ ω, a (gueBlock W 1 ω 0) ∂(μ W 1) + ∫ ω, a (-gueBlock W 1 ω 0) ∂(μ W 1) :=
    integral_add hi hj
  have e3 : ∫ _ : Ω W 1, (2 : ℂ) • a₀ ∂(μ W 1) = (2 : ℂ) • a₀ := by
    rw [integral_const]
    simp
  have hsum : ∫ ω, (a (gueBlock W 1 ω 0) + a (-gueBlock W 1 ω 0) - (2 : ℂ) • a₀) ∂(μ W 1) =
      (2 : ℂ) • (∫ ω, a (gueBlock W 1 ω 0) ∂(μ W 1) - a₀) := by
    rw [e1, e2, e3, sub_eq_zero.mp hodd, smul_sub, two_smul, two_smul]
  have hbd : ‖∫ ω, (a (gueBlock W 1 ω 0) + a (-gueBlock W 1 ω 0) - (2 : ℂ) • a₀) ∂(μ W 1)‖ ≤
      ∫ ω, K * t ^ 2 * (1 + ‖gueBlock W 1 ω 0‖) ^ r ∂(μ W 1) :=
    norm_integral_le_of_norm_le (hM.const_mul _) (Filter.Eventually.of_forall fun ω => by
      have := (h.2 _ (gueBlock_isHermitian W 1 ω 0)).2
      exact this)
  rw [hsum, zn_norm_two_smul, integral_const_mul] at hbd
  have h2 : K * t ^ 2 * ∫ ω, (1 + ‖gueBlock W 1 ω 0‖) ^ r ∂(μ W 1) ≤ K * t ^ 2 * M :=
    mul_le_mul_of_nonneg_left hMb (by positivity)
  have h3 := norm_nonneg (∫ ω, a (gueBlock W 1 ω 0) ∂(μ W 1) - a₀)
  linarith

private lemma zn_measurable_inv {W : ℕ} :
    Measurable fun X : Matrix (Fin W) (Fin W) ℂ => X⁻¹ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  have h : (fun X : Matrix (Fin W) (Fin W) ℂ => X⁻¹ i j) =
      fun X => (X.det)⁻¹ * X.adjugate i j := by
    funext X
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [h]
  have hd : Continuous fun X : Matrix (Fin W) (Fin W) ℂ => X.det := continuous_id.matrix_det
  have ha : Continuous fun X : Matrix (Fin W) (Fin W) ℂ => X.adjugate i j :=
    (continuous_id.matrix_adjugate).matrix_elem i j
  exact hd.measurable.inv.mul ha.measurable

private lemma zn_measurable_zpow {W : ℕ} (k : ℤ) :
    Measurable fun A : Matrix (Fin W) (Fin W) ℂ => A ^ k := by
  cases k with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact (continuous_id.pow n).measurable
  | negSucc n =>
    simp only [zpow_negSucc]
    exact zn_measurable_inv.comp (continuous_id.pow _).measurable

private lemma zn_cont_vecForm {W : ℕ} :
    Continuous fun q : Matrix (Fin W) (Fin W) ℂ × EuclideanSpace ℂ (Fin W) => vecForm q.1 q.2 := by
  have hc : Continuous (fun q : Matrix (Fin W) (Fin W) ℂ × EuclideanSpace ℂ (Fin W) =>
      Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) q.1 q.2) :=
    Matrix.continuous_uncurry_toEuclideanCLM
  exact continuous_snd.inner hc

private lemma zn_measurable_obsM (W : ℕ) (k : ℤ) : Measurable fun X : State W => obsM k X :=
  measurable_const.mul ((continuous_id.matrix_trace).measurable.comp
    ((zn_measurable_zpow k).comp measurable_fst))

private lemma zn_measurable_obsF (W : ℕ) (k : ℤ) : Measurable fun X : State W => obsF k X := by
  unfold obsF
  have h1 : Measurable fun X : State W => (X.1 ^ k, X.2) :=
    ((zn_measurable_zpow k).comp measurable_fst).prodMk measurable_snd
  have h2 := (zn_cont_vecForm (W := W)).measurable.comp h1
  exact h2

private lemma zn_measurable_step (g E : ℝ) {W : ℕ} (X : State W) :
    Measurable fun V : Matrix (Fin W) (Fin W) ℂ => stepState g E X V := by
  have hS : Measurable fun V : Matrix (Fin W) (Fin W) ℂ => (X, V) :=
    Measurable.prodMk measurable_const measurable_id
  have h := (measurable_stepState g E W).comp hS
  exact h

private lemma zn_mul_le_one {a b : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a‖ * ‖b‖ ≤ 1 :=
  (mul_le_mul ha hb (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- The zero-noise limit of `P_g(φ ψ)` for two observables with zero-noise expansions. -/
private lemma zn_final {E₀ : ℝ} (hE₀ : E₀ < 2) (φ ψ : ∀ {W : ℕ}, State W → ℂ) (k l : ℤ)
    (hφm : ∀ W : ℕ, Measurable fun X : State W => φ X)
    (hψm : ∀ W : ℕ, Measurable fun X : State W => ψ X)
    (hφb : ∀ (W : ℕ) (X : State W), IsState X → ‖φ X‖ ≤ 1)
    (hψb : ∀ (W : ℕ) (X : State W), IsState X → ‖ψ X‖ ≤ 1)
    (hφ : ∃ (K : ℝ) (r : ℕ), ∀ W : ℕ, 1 ≤ W → ∀ g E : ℝ, 0 < g → normalH E / g ≤ 1 →
      ∀ X : State W, IsState X →
        ZG (normalH E / g) K r (fun V => φ (stepState g E X V)) ((-normalPhase E) ^ k * φ X))
    (hψ : ∃ (K : ℝ) (r : ℕ), ∀ W : ℕ, 1 ≤ W → ∀ g E : ℝ, 0 < g → normalH E / g ≤ 1 →
      ∀ X : State W, IsState X →
        ZG (normalH E / g) K r (fun V => ψ (stepState g E X V)) ((-normalPhase E) ^ l * ψ X)) :
    ∃ K : ℝ, 0 < K ∧ ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ E₀ →
      ∀ X : State W, IsState X →
        ‖transOp g E (fun Y => φ Y * ψ Y) X -
            (-normalPhase E) ^ (k + l) * (φ X * ψ X)‖ ≤ K / g ^ 2 := by
  obtain ⟨K₁, r₁, h₁⟩ := hφ
  obtain ⟨K₂, r₂, h₂⟩ := hψ
  obtain ⟨M, hM0, hM⟩ := zn_moment (r₁ + r₂)
  set H : ℝ := (2 * √(1 - E₀ ^ 2 / 4))⁻¹ with hH
  have hH0 : 0 ≤ H := by positivity
  refine ⟨4 * |K₁| * |K₂| * M * H ^ 2 + 2 * H ^ 2 + 1, by positivity, ?_⟩
  intro W hW g hg E hE X hX
  have hg0 : 0 < g := by linarith
  have hg2 : 0 < g ^ 2 := by positivity
  have hh0 := zn_normalH_nonneg E
  have hhH : normalH E ≤ H := zn_normalH_le hE₀ hE
  have hlam1 : ‖-normalPhase E‖ = 1 := by rw [norm_neg, zn_norm_normalPhase]
  have hlam : (-normalPhase E) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlam1
    exact zero_ne_one hlam1
  have hstate : ∀ V : Matrix (Fin W) (Fin W) ℂ, V.IsHermitian →
      ‖φ (stepState g E X V) * ψ (stepState g E X V)‖ ≤ 1 := fun V hV => by
    have hS := isState_stepState g E hX hV
    rw [norm_mul]
    exact zn_mul_le_one (hφb W _ hS) (hψb W _ hS)
  by_cases ht1 : normalH E / g ≤ 1
  · have ht0 : 0 ≤ normalH E / g := div_nonneg hh0 hg0.le
    have hZ1 := h₁ W hW g E hg0 ht1 X hX
    have hZ2 := h₂ W hW g E hg0 ht1 X hX
    have hZ := zn_mul hZ1 hZ2 ht0 ht1
    have hv : (-normalPhase E) ^ k * φ X * ((-normalPhase E) ^ l * ψ X) =
        (-normalPhase E) ^ (k + l) * (φ X * ψ X) := by
      rw [zpow_add₀ hlam]; ring
    rw [hv] at hZ
    have hmeas : Measurable fun V : Matrix (Fin W) (Fin W) ℂ =>
        φ (stepState g E X V) * ψ (stepState g E X V) :=
      ((hφm W).comp (zn_measurable_step g E X)).mul ((hψm W).comp (zn_measurable_step g E X))
    have hint := zn_integral hZ hmeas hstate (hM W).1 (hM W).2
    have hK1 := zn_K_nonneg hZ1
    have hK2 := zn_K_nonneg hZ2
    have e : 4 * K₁ * K₂ * (normalH E / g) ^ 2 * M = 4 * K₁ * K₂ * M * normalH E ^ 2 / g ^ 2 := by
      field_simp
    have hle : 4 * K₁ * K₂ * M * normalH E ^ 2 ≤ 4 * |K₁| * |K₂| * M * H ^ 2 := by
      rw [abs_of_nonneg hK1, abs_of_nonneg hK2]
      have : normalH E ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ hh0 hhH 2
      have h4 : 0 ≤ 4 * K₁ * K₂ * M := by positivity
      exact mul_le_mul_of_nonneg_left this h4
    change ‖∫ ω, φ (stepState g E X (gueBlock W 1 ω 0)) * ψ (stepState g E X (gueBlock W 1 ω 0))
      ∂(μ W 1) - _‖ ≤ _
    refine hint.trans ?_
    rw [e]
    refine div_le_div_of_nonneg_right ?_ hg2.le
    have : 0 ≤ 2 * H ^ 2 := by positivity
    linarith
  · have hgh : g < normalH E := by
      by_contra hcon
      exact ht1 (div_le_one_of_le₀ (not_lt.mp hcon) hg0.le)
    have hgH : g ^ 2 ≤ H ^ 2 := by nlinarith
    have h1 : ‖transOp g E (fun Y => φ Y * ψ Y) X‖ ≤ 1 := by
      unfold transOp
      have := norm_integral_le_of_norm_le_const (μ := μ W 1)
        (f := fun ω => φ (stepState g E X (gueBlock W 1 ω 0)) *
          ψ (stepState g E X (gueBlock W 1 ω 0))) (C := 1)
        (Filter.Eventually.of_forall fun ω => hstate _ (gueBlock_isHermitian W 1 ω 0))
      simpa using this
    have h2 : ‖(-normalPhase E) ^ (k + l) * (φ X * ψ X)‖ ≤ 1 := by
      rw [norm_mul, norm_zpow, hlam1, one_zpow, one_mul, norm_mul]
      exact zn_mul_le_one (hφb W X hX) (hψb W X hX)
    have h3 : (2 : ℝ) ≤ 2 * H ^ 2 / g ^ 2 := by
      rw [le_div_iff₀ hg2]
      nlinarith
    calc ‖transOp g E (fun Y => φ Y * ψ Y) X - (-normalPhase E) ^ (k + l) * (φ X * ψ X)‖
        ≤ ‖transOp g E (fun Y => φ Y * ψ Y) X‖ +
            ‖(-normalPhase E) ^ (k + l) * (φ X * ψ X)‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith
      _ ≤ 2 * H ^ 2 / g ^ 2 := h3
      _ ≤ (4 * |K₁| * |K₂| * M * H ^ 2 + 2 * H ^ 2 + 1) / g ^ 2 := by
        refine div_le_div_of_nonneg_right ?_ hg2.le
        have : 0 ≤ 4 * |K₁| * |K₂| * M * H ^ 2 := by positivity
        linarith

/-- The zero-noise step multiplies `m_k`, `f_k` by `(-e^{-2iθ})^k` (Section 11.2
[sec:uniform-large-g], before (11.22) [uvg:eq:means]); for products of two observables
`P_g(m_k m_l) = (-e^{-2iθ})^{k+l} m_k m_l + O(g⁻²)`. -/
theorem transOp_obsM_mul_obsM {E₀ : ℝ} (hE₀ : E₀ < 2) (k l : ℤ) :
    ∃ K : ℝ, 0 < K ∧ ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ E₀ →
      ∀ X : State W, IsState X →
        ‖transOp g E (fun Y => obsM k Y * obsM l Y) X -
            (-normalPhase E) ^ (k + l) * (obsM k X * obsM l X)‖ ≤ K / g ^ 2 := by
  exact zn_final hE₀ (fun {W} X => obsM k X) (fun {W} X => obsM l X) k l
    (fun W => zn_measurable_obsM W k) (fun W => zn_measurable_obsM W l)
    (fun W X hX => norm_obsM_le_one k hX) (fun W X hX => norm_obsM_le_one l hX)
    ⟨_, _, fun W hW g E hg ht1 X hX => zn_obsM hW hg ht1 hX k⟩
    ⟨_, _, fun W hW g E hg ht1 X hX => zn_obsM hW hg ht1 hX l⟩

/-- `P_g(m_k f_l) = (-e^{-2iθ})^{k+l} m_k f_l + O(g⁻²)` (Section 11.2 [sec:uniform-large-g]). -/
theorem transOp_obsM_mul_obsF {E₀ : ℝ} (hE₀ : E₀ < 2) (k l : ℤ) :
    ∃ K : ℝ, 0 < K ∧ ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ E₀ →
      ∀ X : State W, IsState X →
        ‖transOp g E (fun Y => obsM k Y * obsF l Y) X -
            (-normalPhase E) ^ (k + l) * (obsM k X * obsF l X)‖ ≤ K / g ^ 2 := by
  exact zn_final hE₀ (fun {W} X => obsM k X) (fun {W} X => obsF l X) k l
    (fun W => zn_measurable_obsM W k) (fun W => zn_measurable_obsF W l)
    (fun W X hX => norm_obsM_le_one k hX) (fun W X hX => norm_obsF_le_one l hX)
    ⟨_, _, fun W hW g E hg ht1 X hX => zn_obsM hW hg ht1 hX k⟩
    ⟨_, _, fun W hW g E hg ht1 X hX => zn_obsF hW hg ht1 hX l⟩

/-- `P_g(f_k f_l) = (-e^{-2iθ})^{k+l} f_k f_l + O(g⁻²)` (Section 11.2 [sec:uniform-large-g]). -/
theorem transOp_obsF_mul_obsF {E₀ : ℝ} (hE₀ : E₀ < 2) (k l : ℤ) :
    ∃ K : ℝ, 0 < K ∧ ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ E₀ →
      ∀ X : State W, IsState X →
        ‖transOp g E (fun Y => obsF k Y * obsF l Y) X -
            (-normalPhase E) ^ (k + l) * (obsF k X * obsF l X)‖ ≤ K / g ^ 2 := by
  exact zn_final hE₀ (fun {W} X => obsF k X) (fun {W} X => obsF l X) k l
    (fun W => zn_measurable_obsF W k) (fun W => zn_measurable_obsF W l)
    (fun W X hX => norm_obsF_le_one k hX) (fun W X hX => norm_obsF_le_one l hX)
    ⟨_, _, fun W hW g E hg ht1 X hX => zn_obsF hW hg ht1 hX k⟩
    ⟨_, _, fun W hW g E hg ht1 X hX => zn_obsF hW hg ht1 hX l⟩

end LSBA
