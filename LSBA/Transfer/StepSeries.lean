import LSBA.Gauss.WickConfig

/-!
# The one-step update as a power series in `h_θ/g`

The unrotated update `K̃ = (C + itV(I + C))F⁻¹ = C + Σ_{j≥1} (it)^j U(VU)^j` (`U = I + C`,
`t = h_θ/g`) of (11.3) [lg:eq:matrix-update], its adjoint, `F⁻¹ = Σ_j (itVU)^j` and
`F^{−*} = Σ_j (−it)^j (U*V)^j` as formal power series in `t` over words; the configurations of
`m_k(K̃)`, `f_k(K̃, F^{−*}v/‖F^{−*}v‖) = v*F⁻¹K̃^kF^{−*}v / Y` with `Y = ‖F^{−*}v‖²`, and of the
increment `c = −½ log Y` of (11.7) [lg:eq:update]; and the expansion of a polynomial in the
observables after one step with an exact remainder `K t^{N+1}(1 + ‖V‖)^r` (proof of Lemma 11.7
[lg:lem:ideal]).
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The letter `C` as a word. -/
def wC : WordAlg := FreeAlgebra.ι ℂ WLetter.c

/-- The letter `C⁻¹` as a word. -/
def wCi : WordAlg := FreeAlgebra.ι ℂ WLetter.cInv

/-- The letter `V` as a word. -/
def wV : WordAlg := FreeAlgebra.ι ℂ WLetter.v

/-- `K̃ = C + Σ_{j≥1} (it)^j U(VU)^j`, the update of (11.3) [lg:eq:matrix-update] before the
rotation by `−e^{−2iθ}`, as a power series in `t`. -/
def kSeries : PowerSeries WordAlg :=
  PowerSeries.mk fun j => if j = 0 then wC else (Complex.I ^ j) • ((1 + wC) * (wV * (1 + wC)) ^ j)

/-- `K̃* = C⁻¹ + Σ_{j≥1} (−it)^j (U*V)^j U*` (`C* = C⁻¹`). -/
def kAdjSeries : PowerSeries WordAlg :=
  PowerSeries.mk fun j =>
    if j = 0 then wCi else ((-Complex.I) ^ j) • (((1 + wCi) * wV) ^ j * (1 + wCi))

/-- `F⁻¹ = Σ_j (itVU)^j`. -/
def fInvSeries : PowerSeries WordAlg :=
  PowerSeries.mk fun j => (Complex.I ^ j) • (wV * (1 + wC)) ^ j

/-- `F^{−*} = Σ_j (−it)^j (U*V)^j`. -/
def fInvAdjSeries : PowerSeries WordAlg :=
  PowerSeries.mk fun j => ((-Complex.I) ^ j) • ((1 + wCi) * wV) ^ j

/-- `K̃^k`, `k ∈ ℤ` (negative powers through `K̃* = K̃⁻¹`). -/
def kPowSeries (k : ℤ) : PowerSeries WordAlg :=
  if 0 ≤ k then kSeries ^ k.toNat else kAdjSeries ^ (-k).toNat

/-- A linear functional on words given on basis words. -/
def wordFun (φ : List WLetter → CfgPoly) : WordAlg →ₗ[ℂ] CfgPoly :=
  Finsupp.linearCombination ℂ (fun u : FreeMonoid WLetter => φ (FreeMonoid.toList u)) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap ∘ₗ
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℂ) (X := WLetter)).toLinearMap

/-- The normalized trace of a word (`1` on the empty word). -/
def trcFun : WordAlg →ₗ[ℂ] CfgPoly := wordFun fun u => if u = [] then 1 else X (.trc u)

/-- The marked form of a word (`1` on the empty word). -/
def mrkFun : WordAlg →ₗ[ℂ] CfgPoly := wordFun fun u => if u = [] then 1 else X (.mrk u)

/-- A linear map applied to each coefficient of a power series. -/
def seriesMap (L : WordAlg →ₗ[ℂ] CfgPoly) (S : PowerSeries WordAlg) : PowerSeries CfgPoly :=
  PowerSeries.mk fun n => L (PowerSeries.coeff n S)

/-- `Y = v* F⁻¹ F^{−*} v = ‖F^{−*}v‖²`. -/
def ySeries : PowerSeries CfgPoly := seriesMap mrkFun (fInvSeries * fInvAdjSeries)

/-- `1/Y` (constant coefficient `1`). -/
def yInvSeries : PowerSeries CfgPoly := PowerSeries.invOfUnit ySeries 1

/-- `log(1 + x)` for a series `x` without constant term. -/
def logSeries (x : PowerSeries CfgPoly) : PowerSeries CfgPoly :=
  PowerSeries.mk fun n => ∑ j ∈ Finset.range (n + 1),
    ((-1 : ℂ) ^ (j + 1) / j) • PowerSeries.coeff n (x ^ j)

/-- The increment `c = −½ log Y` of (11.7) [lg:eq:update] as a series in `t`. -/
def incSeries : PowerSeries CfgPoly := (-(1 / 2 : ℂ)) • logSeries (ySeries - 1)

/-- The unrotated one-step image of a polynomial in the observables: `m_k ↦ m_k(K̃)`,
`f_k ↦ v*F⁻¹K̃^kF^{−*}v / Y`, `w`, `γ` fixed. -/
def stepSeries : ObsPoly →ₐ[ℂ] PowerSeries CfgPoly :=
  aeval fun v => match v with
    | .m k => seriesMap trcFun (kPowSeries k.1)
    | .f k => seriesMap mrkFun (fInvSeries * kPowSeries k.1 * fInvAdjSeries) * yInvSeries
    | .w => PowerSeries.C (X .w)
    | .γ => PowerSeries.C (X .γ)

/-! ### Polynomial bounds, uniform over a family of points -/

/-- A family of points with a weight `t ∈ [0, H]` and a size `s ≥ 1`. -/
private structure Scl (ι : Type) where
  P : Set ι
  t : ι → ℝ
  s : ι → ℝ
  H : ℝ
  one_le_H : 1 ≤ H
  t_nonneg : ∀ c ∈ P, 0 ≤ t c
  t_le : ∀ c ∈ P, t c ≤ H
  one_le_s : ∀ c ∈ P, 1 ≤ s c

/-- `f ≤ K t^m s^r` on the family, for some `K ≥ 0` and `r`. -/
private def PBt {ι : Type} (σ : Scl ι) (m : ℕ) (f : ι → ℝ) : Prop :=
  ∃ K : ℝ, ∃ r : ℕ, 0 ≤ K ∧ ∀ c ∈ σ.P, f c ≤ K * σ.t c ^ m * σ.s c ^ r

section Bounds

variable {ι : Type} {σ : Scl ι}

private theorem Scl.s_pow_nonneg (σ : Scl ι) {c : ι} (hc : c ∈ σ.P) (r : ℕ) : 0 ≤ σ.s c ^ r :=
  pow_nonneg (le_trans zero_le_one (σ.one_le_s c hc)) r

private theorem PBt.raise {m : ℕ} {f : ι → ℝ} {K : ℝ} {r r' : ℕ} (hK : 0 ≤ K) (hr : r ≤ r')
    {c : ι} (hc : c ∈ σ.P) (h : f c ≤ K * σ.t c ^ m * σ.s c ^ r) :
    f c ≤ K * σ.t c ^ m * σ.s c ^ r' :=
  h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (σ.one_le_s c hc) hr)
    (mul_nonneg hK (pow_nonneg (σ.t_nonneg c hc) _)))

private theorem PBt.add {m : ℕ} {f g : ι → ℝ} (hf : PBt σ m f) (hg : PBt σ m g) :
    PBt σ m (fun c => f c + g c) := by
  obtain ⟨K₁, r₁, hK₁, h₁⟩ := hf
  obtain ⟨K₂, r₂, hK₂, h₂⟩ := hg
  refine ⟨K₁ + K₂, max r₁ r₂, add_nonneg hK₁ hK₂, fun c hc => ?_⟩
  calc f c + g c ≤ K₁ * σ.t c ^ m * σ.s c ^ max r₁ r₂ + K₂ * σ.t c ^ m * σ.s c ^ max r₁ r₂ :=
        add_le_add (PBt.raise hK₁ (le_max_left r₁ r₂) hc (h₁ c hc))
          (PBt.raise hK₂ (le_max_right r₁ r₂) hc (h₂ c hc))
    _ = _ := by ring

private theorem PBt.mul {m m' : ℕ} {f g : ι → ℝ} (hf : PBt σ m f) (hg : PBt σ m' g)
    (hg0 : ∀ c ∈ σ.P, 0 ≤ g c) : PBt σ (m + m') (fun c => f c * g c) := by
  obtain ⟨K₁, r₁, hK₁, h₁⟩ := hf
  obtain ⟨K₂, r₂, hK₂, h₂⟩ := hg
  refine ⟨K₁ * K₂, r₁ + r₂, mul_nonneg hK₁ hK₂, fun c hc => ?_⟩
  have ht := σ.t_nonneg c hc
  have hs : 0 ≤ σ.s c := by linarith [σ.one_le_s c hc]
  calc f c * g c ≤ (K₁ * σ.t c ^ m * σ.s c ^ r₁) * (K₂ * σ.t c ^ m' * σ.s c ^ r₂) :=
        mul_le_mul (h₁ c hc) (h₂ c hc) (hg0 c hc) (by positivity)
    _ = _ := by ring

private theorem PBt.le {m : ℕ} {f g : ι → ℝ} (hg : PBt σ m g) (h : ∀ c ∈ σ.P, f c ≤ g c) :
    PBt σ m f := by
  obtain ⟨K, r, hK, h₁⟩ := hg
  exact ⟨K, r, hK, fun c hc => (h c hc).trans (h₁ c hc)⟩

private theorem PBt.const {K : ℝ} (hK : 0 ≤ K) : PBt σ 0 (fun _ => K) :=
  ⟨K, 0, hK, fun c _ => by simp⟩

private theorem PBt.zero (m : ℕ) : PBt σ m (fun _ => 0) :=
  ⟨0, 0, le_rfl, fun c _ => by simp⟩

private theorem PBt.t_pow (m : ℕ) : PBt σ m (fun c => σ.t c ^ m) :=
  ⟨1, 0, zero_le_one, fun c _ => by simp⟩

private theorem PBt.s_pow (r : ℕ) : PBt σ 0 (fun c => σ.s c ^ r) :=
  ⟨1, r, zero_le_one, fun c _ => by simp⟩

private theorem PBt.lower {m m' : ℕ} {f : ι → ℝ} (h : m ≤ m') (hf : PBt σ m' f) :
    PBt σ m f := by
  obtain ⟨K, r, hK, h₁⟩ := hf
  have hH : 0 ≤ σ.H := le_trans zero_le_one σ.one_le_H
  refine ⟨K * σ.H ^ (m' - m), r, mul_nonneg hK (pow_nonneg hH _), fun c hc => ?_⟩
  have ht := σ.t_nonneg c hc
  have hs : 0 ≤ σ.s c ^ r := pow_nonneg (by linarith [σ.one_le_s c hc]) _
  have e : σ.t c ^ m' = σ.t c ^ (m' - m) * σ.t c ^ m := by
    rw [← pow_add, Nat.sub_add_cancel h]
  have hle : σ.t c ^ (m' - m) ≤ σ.H ^ (m' - m) := pow_le_pow_left₀ ht (σ.t_le c hc) _
  calc f c ≤ K * σ.t c ^ m' * σ.s c ^ r := h₁ c hc
    _ = K * σ.t c ^ (m' - m) * σ.t c ^ m * σ.s c ^ r := by rw [e]; ring
    _ ≤ K * σ.H ^ (m' - m) * σ.t c ^ m * σ.s c ^ r := by gcongr

private theorem PBt.sum {κ : Type} (S : Finset κ) {m : ℕ} {f : κ → ι → ℝ}
    (h : ∀ i ∈ S, PBt σ m (f i)) : PBt σ m (fun c => ∑ i ∈ S, f i c) := by
  induction S using Finset.induction_on with
  | empty => simpa using PBt.zero (σ := σ) m
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a S)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem PBt.pow {m : ℕ} {f : ι → ℝ} (hf : PBt σ m f) (h0 : ∀ c ∈ σ.P, 0 ≤ f c) :
    ∀ k : ℕ, PBt σ (m * k) (fun c => f c ^ k)
  | 0 => by simpa using PBt.const (σ := σ) zero_le_one
  | k + 1 => by
    have := (PBt.pow hf h0 k).mul hf h0
    simpa [pow_succ, Nat.mul_succ] using this

end Bounds

/-! ### Expansions with exact polynomial remainders -/

section Expansion

variable {ι : Type} {σ : Scl ι} {R : ι → Type} [∀ c, NormedRing (R c)]
  [∀ c, NormedAlgebra ℂ (R c)]

/-- `Σ_{n ≤ N} t^n α_n`. -/
private def psum (σ : Scl ι) (α : ∀ c, ℕ → R c) (N : ℕ) (c : ι) : R c :=
  ∑ n ∈ Finset.range (N + 1), ((σ.t c ^ n : ℝ) : ℂ) • α c n

/-- The coefficients `α_n` are polynomially bounded and `a − Σ_{n ≤ N} t^n α_n = O(t^{N+1})`
with polynomial constants, for every `N`. -/
private def Good (σ : Scl ι) (a : ∀ c, R c) (α : ∀ c, ℕ → R c) : Prop :=
  (∀ n, PBt σ 0 fun c => ‖α c n‖) ∧ ∀ N, PBt σ (N + 1) fun c => ‖a c - psum σ α N c‖

/-- The Cauchy product of two coefficient sequences. -/
private def cauchy (α β : ∀ c, ℕ → R c) (c : ι) (n : ℕ) : R c :=
  ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, α c x.1 * β c x.2

private theorem norm_rsmul {A : Type} [NormedRing A] [NormedAlgebra ℂ A] {x : ℝ} (hx : 0 ≤ x)
    (y : A) : ‖((x : ℝ) : ℂ) • y‖ = x * ‖y‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hx]

private theorem PBt.psumN {α : ∀ c, ℕ → R c} (h : ∀ n, PBt σ 0 fun c => ‖α c n‖) (N : ℕ) :
    PBt σ 0 fun c => ‖psum σ α N c‖ := by
  have hn : ∀ n, PBt σ 0 (fun c => σ.t c ^ n * ‖α c n‖) := fun n =>
    ((PBt.t_pow n).mul (h n) (fun _ _ => norm_nonneg _)).lower (Nat.zero_le _)
  refine (PBt.sum (Finset.range (N + 1)) fun n _ => hn n).le fun c hc => ?_
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_))
  rw [norm_rsmul (pow_nonneg (σ.t_nonneg c hc) _)]

private theorem Good.norm {a : ∀ c, R c} {α : ∀ c, ℕ → R c} (h : Good σ a α) :
    PBt σ 0 fun c => ‖a c‖ := by
  refine ((h.2 0).lower (Nat.zero_le _)).add (PBt.psumN h.1 0) |>.le fun c _ => ?_
  calc ‖a c‖ = ‖(a c - psum σ α 0 c) + psum σ α 0 c‖ := by rw [sub_add_cancel]
    _ ≤ _ := norm_add_le _ _

private theorem Good.congr {a a' : ∀ c, R c} {α α' : ∀ c, ℕ → R c} (h : Good σ a α)
    (ha : ∀ c ∈ σ.P, a c = a' c) (hα : ∀ c ∈ σ.P, ∀ n, α c n = α' c n) : Good σ a' α' := by
  refine ⟨fun n => (h.1 n).le fun c hc => by rw [hα c hc], fun N => (h.2 N).le fun c hc => ?_⟩
  have : psum σ α N c = psum σ α' N c :=
    Finset.sum_congr rfl fun n _ => by rw [hα c hc]
  rw [← ha c hc, ← this]

private theorem Good.add {a b : ∀ c, R c} {α β : ∀ c, ℕ → R c} (ha : Good σ a α)
    (hb : Good σ b β) : Good σ (fun c => a c + b c) (fun c n => α c n + β c n) := by
  refine ⟨fun n => ((ha.1 n).add (hb.1 n)).le fun c _ => norm_add_le _ _, fun N =>
    ((ha.2 N).add (hb.2 N)).le fun c _ => ?_⟩
  have : psum σ (fun c n => α c n + β c n) N c = psum σ α N c + psum σ β N c := by
    simp only [psum, smul_add, Finset.sum_add_distrib]
  rw [this, add_sub_add_comm]
  exact norm_add_le _ _

private theorem Good.smul {a : ∀ c, R c} {α : ∀ c, ℕ → R c} (ha : Good σ a α) (z : ι → ℂ)
    (hz : ∀ c ∈ σ.P, ‖z c‖ ≤ 1) : Good σ (fun c => z c • a c) (fun c n => z c • α c n) := by
  have key : ∀ c ∈ σ.P, ∀ x : R c, ‖z c • x‖ ≤ ‖x‖ := fun c hc x => by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right (hz c hc) (norm_nonneg _)).trans (by rw [one_mul])
  refine ⟨fun n => (ha.1 n).le fun c hc => key c hc _, fun N => (ha.2 N).le fun c hc => ?_⟩
  have : psum σ (fun c n => z c • α c n) N c = z c • psum σ α N c := by
    simp only [psum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun n _ => smul_comm _ _ _
  rw [this, ← smul_sub]
  exact key c hc _

private theorem Good.zero : Good σ (fun c => (0 : R c)) (fun _ _ => 0) :=
  ⟨fun _ => (PBt.zero 0).le fun _ _ => by simp,
    fun N => (PBt.zero (N + 1)).le fun _ _ => by simp [psum]⟩

private theorem Good.sum {κ : Type} (S : Finset κ) {a : κ → ∀ c, R c}
    {α : κ → ∀ c, ℕ → R c} (h : ∀ i ∈ S, Good σ (a i) (α i)) :
    Good σ (fun c => ∑ i ∈ S, a i c) (fun c n => ∑ i ∈ S, α i c n) := by
  induction S using Finset.induction_on with
  | empty => simpa using (Good.zero (σ := σ) (R := R))
  | insert j S hj ih =>
    simp only [Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self j S)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- A map that is additive, commutes with real scalars and does not increase norms. -/
private theorem Good.map {R' : ι → Type} [∀ c, NormedRing (R' c)] [∀ c, NormedAlgebra ℂ (R' c)]
    {a : ∀ c, R c} {α : ∀ c, ℕ → R c} (ha : Good σ a α) (f : ∀ c, R c →+ R' c)
    (hf : ∀ c (x : ℝ) (y : R c), f c (((x : ℝ) : ℂ) • y) = ((x : ℝ) : ℂ) • f c y)
    (hn : ∀ c ∈ σ.P, ∀ y : R c, ‖f c y‖ ≤ ‖y‖) :
    Good σ (fun c => f c (a c)) (fun c n => f c (α c n)) := by
  refine ⟨fun n => (ha.1 n).le fun c hc => hn c hc _, fun N => (ha.2 N).le fun c hc => ?_⟩
  have : psum σ (fun c n => f c (α c n)) N c = f c (psum σ α N c) := by
    simp only [psum, map_sum, hf]
  rw [this, ← map_sub]
  exact hn c hc _

/-- Finitely many coefficients: `a = Σ_{n ≤ D} t^n α_n`. -/
private theorem Good.fin {α : ∀ c, ℕ → R c} (D : ℕ) (hα : ∀ n, PBt σ 0 fun c => ‖α c n‖)
    (hz : ∀ c, ∀ n, D < n → α c n = 0) : Good σ (fun c => psum σ α D c) α := by
  refine ⟨hα, fun N => ?_⟩
  rcases le_or_gt D N with h | h
  · have e : ∀ c, psum σ α N c = psum σ α D c := by
      intro c
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [psum, show D + (k + 1) + 1 = D + k + 1 + 1 by ring, Finset.sum_range_succ, ← psum,
          ih (by omega), hz c _ (by omega), smul_zero, add_zero]
    exact (PBt.zero _).le fun c _ => by rw [e, sub_self, norm_zero]
  · have e : ∀ c, psum σ α D c - psum σ α N c =
        ∑ n ∈ Finset.Ico (N + 1) (D + 1), ((σ.t c ^ n : ℝ) : ℂ) • α c n := by
      intro c
      rw [psum, psum, ← Finset.sum_range_add_sum_Ico _ (show N + 1 ≤ D + 1 by omega),
        add_sub_cancel_left]
    refine (PBt.sum (Finset.Ico (N + 1) (D + 1)) fun n hn =>
      ((PBt.t_pow n).mul (hα n) (fun _ _ => norm_nonneg _)).lower
        (by rw [Finset.mem_Ico] at hn; omega)).le fun c hc => ?_
    rw [e]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_))
    rw [norm_rsmul (pow_nonneg (σ.t_nonneg c hc) _)]

/-- `A_N B_N − (AB)_N`: the products of orders `N+1, …, 2N`. -/
private theorem psum_mul_sub (α β : ∀ c, ℕ → R c) (N : ℕ) (c : ι) :
    psum σ α N c * psum σ β N c - psum σ (cauchy α β) N c =
      ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.Ico (N + 1 - i) (N + 1),
        ((σ.t c ^ (i + j) : ℝ) : ℂ) • (α c i * β c j) := by
  set F : ℕ → ℕ → R c := fun i j => ((σ.t c ^ (i + j) : ℝ) : ℂ) • (α c i * β c j) with hF
  have h1 : psum σ α N c * psum σ β N c =
      ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), F i j := by
    rw [psum, psum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hF, smul_mul_smul_comm]
    simp only [pow_add, Complex.ofReal_mul]
  have h2 : psum σ (cauchy α β) N c =
      ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1 - i), F i j := by
    rw [← Finset.sum_range_diag_flip]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [cauchy, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => α c i * β c j),
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [hF]
    simp only
    rw [Nat.add_sub_cancel' (by omega)]
  rw [h1, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [← Finset.sum_range_add_sum_Ico _ (show N + 1 - i ≤ N + 1 by omega), add_sub_cancel_left]

private theorem PBt.cross {α β : ∀ c, ℕ → R c} (hα : ∀ n, PBt σ 0 fun c => ‖α c n‖)
    (hβ : ∀ n, PBt σ 0 fun c => ‖β c n‖) (N : ℕ) :
    PBt σ (N + 1) fun c =>
      ‖psum σ α N c * psum σ β N c - psum σ (cauchy α β) N c‖ := by
  have hterm : ∀ i j, N + 1 ≤ i + j →
      PBt σ (N + 1) (fun c => σ.t c ^ (i + j) * (‖α c i‖ * ‖β c j‖)) := fun i j hij =>
    ((PBt.t_pow (i + j)).mul ((hα i).mul (hβ j) (fun _ _ => norm_nonneg _))
      (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))).lower (by omega)
  refine (PBt.sum (Finset.range (N + 1)) fun i hi => PBt.sum (Finset.Ico (N + 1 - i) (N + 1))
    fun j hj => hterm i j ?_).le fun c hc => ?_
  · rw [Finset.mem_Ico] at hj
    rw [Finset.mem_range] at hi
    omega
  · rw [psum_mul_sub]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun j _ => ?_))
    rw [norm_rsmul (pow_nonneg (σ.t_nonneg c hc) _)]
    exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) (pow_nonneg (σ.t_nonneg c hc) _)

omit [∀ c, NormedAlgebra ℂ (R c)] in
private theorem PBt.cauchyN {α β : ∀ c, ℕ → R c} (hα : ∀ n, PBt σ 0 fun c => ‖α c n‖)
    (hβ : ∀ n, PBt σ 0 fun c => ‖β c n‖) (n : ℕ) : PBt σ 0 fun c => ‖cauchy α β c n‖ := by
  refine (PBt.sum (Finset.HasAntidiagonal.antidiagonal n) fun x _ =>
    (hα x.1).mul (hβ x.2) (fun _ _ => norm_nonneg _)).le fun c _ => ?_
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => norm_mul_le _ _)

private theorem Good.mul {a b : ∀ c, R c} {α β : ∀ c, ℕ → R c} (ha : Good σ a α)
    (hb : Good σ b β) : Good σ (fun c => a c * b c) (cauchy α β) := by
  refine ⟨PBt.cauchyN ha.1 hb.1, fun N => ?_⟩
  have h1 := (ha.2 N).mul hb.norm (fun _ _ => norm_nonneg _)
  have h2 := (PBt.psumN ha.1 N).mul (hb.2 N) (fun _ _ => norm_nonneg _)
  rw [add_zero] at h1
  rw [zero_add] at h2
  refine ((h1.add h2).add (PBt.cross ha.1 hb.1 N)).le fun c _ => ?_
  have e : a c * b c - psum σ (cauchy α β) N c = (a c - psum σ α N c) * b c +
      psum σ α N c * (b c - psum σ β N c) +
        (psum σ α N c * psum σ β N c - psum σ (cauchy α β) N c) := by noncomm_ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))) le_rfl)

end Expansion

section Series

variable {ι : Type} {σ : Scl ι} {R : ι → Type} [∀ c, NormedRing (R c)]
  [∀ c, NormedAlgebra ℂ (R c)]

/-- `1/a` from `a` and a coefficient sequence `β` with `α ⋆ β = δ₀`. -/
private theorem Good.inv {a : ι → ℂ} {α β : ι → ℕ → ℂ}
    (ha : Good (R := fun _ => ℂ) σ a α) (hβ : ∀ n, PBt σ 0 fun c => ‖β c n‖)
    (hδ : ∀ c ∈ σ.P, ∀ n, cauchy (R := fun _ => ℂ) α β c n = if n = 0 then 1 else 0)
    (hinv : PBt σ 0 fun c => ‖(a c)⁻¹‖) (h0 : ∀ c ∈ σ.P, a c ≠ 0) :
    Good (R := fun _ => ℂ) σ (fun c => (a c)⁻¹) β := by
  refine ⟨hβ, fun N => ?_⟩
  have hone : ∀ c ∈ σ.P, psum (R := fun _ => ℂ) σ (cauchy (R := fun _ => ℂ) α β) N c = 1 := by
    intro c hc
    rw [psum, Finset.sum_congr rfl fun n _ => by rw [hδ c hc n]]
    simp
  have h1 := (ha.2 N).mul (PBt.psumN hβ N) (fun _ _ => norm_nonneg _)
  have h2 := hinv.mul (h1.add (PBt.cross (R := fun _ => ℂ) ha.1 hβ N))
    (fun _ _ => add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))
  rw [add_zero, zero_add] at h2
  refine h2.le fun c hc => ?_
  set A := psum (R := fun _ => ℂ) σ α N c
  set B := psum (R := fun _ => ℂ) σ β N c
  have e : (a c)⁻¹ - B = (a c)⁻¹ * (-(a c - A) * B -
      (A * B - psum (R := fun _ => ℂ) σ (cauchy (R := fun _ => ℂ) α β) N c)) := by
    rw [hone c hc]
    field_simp [h0 c hc]
    ring
  rw [e, norm_mul]
  refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add ?_ le_rfl))
    (norm_nonneg _)
  rw [norm_mul, norm_neg]

private theorem coeff_mul_map {A : Type} [Ring A] [Algebra ℂ A] {B : Type} [Ring B]
    [Algebra ℂ B] (φ : A →ₐ[ℂ] B) (S T : PowerSeries A) (n : ℕ) :
    φ (PowerSeries.coeff n (S * T)) = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n,
      φ (PowerSeries.coeff x.1 S) * φ (PowerSeries.coeff x.2 T) := by
  rw [PowerSeries.coeff_mul, map_sum]
  simp only [map_mul]

private theorem Good.mulS {A : Type} [Ring A] [Algebra ℂ A] (φ : ∀ c, A →ₐ[ℂ] R c)
    {a b : ∀ c, R c} {S T : ι → PowerSeries A}
    (ha : Good σ a fun c n => φ c (PowerSeries.coeff n (S c)))
    (hb : Good σ b fun c n => φ c (PowerSeries.coeff n (T c))) :
    Good σ (fun c => a c * b c) fun c n => φ c (PowerSeries.coeff n (S c * T c)) :=
  (ha.mul hb).congr (fun _ _ => rfl) fun c _ n => by rw [cauchy, coeff_mul_map]

private theorem Good.powS {A : Type} [Ring A] [Algebra ℂ A] (φ : ∀ c, A →ₐ[ℂ] R c)
    {a : ∀ c, R c} {S : ι → PowerSeries A}
    (ha : Good σ a fun c n => φ c (PowerSeries.coeff n (S c))) :
    ∀ k : ℕ, Good σ (fun c => a c ^ (k + 1)) fun c n => φ c (PowerSeries.coeff n (S c ^ (k + 1)))
  | 0 => by simpa using ha
  | k + 1 => by
    have := (Good.powS φ ha k).mulS φ ha
    simpa only [← pow_succ] using this

end Series

/-! ### The one-step quantities as expansions -/

/-- A point: a width `W`, a coupling `g`, an energy `E`, a state and a block. -/
private structure SCtx where
  W : ℕ
  g : ℝ
  E : ℝ
  X : State W
  V : Matrix (Fin W) (Fin W) ℂ

/-- The points `W ≥ 1`, `g ≥ 1`, `|E| ≤ E₀`, a state, a Hermitian block. -/
private def sAdm (E₀ : ℝ) : Set SCtx :=
  {c | 1 ≤ c.W ∧ 1 ≤ c.g ∧ |c.E| ≤ E₀ ∧ IsState c.X ∧ c.V.IsHermitian}

private theorem stepSeries_normalH_nonneg (E : ℝ) : 0 ≤ normalH E := by
  unfold normalH freeAngle
  have h := Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg (E / 2))
    (Real.arccos_le_pi (E / 2))
  positivity

/-- `h_θ ≤ (4 − E₀²)^{−1/2}` for `|E| ≤ E₀ < 2`. -/
private theorem stepSeries_normalH_le {E₀ E : ℝ} (hE₀ : E₀ < 2) (hE : |E| ≤ E₀) :
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

/-- The scale `t = h_θ/g ≤ (4 − E₀²)^{−1/2}`, `s = 1 + ‖V‖`. -/
private def sScl {E₀ : ℝ} (hE₀ : E₀ < 2) : Scl SCtx where
  P := sAdm E₀
  t c := normalH c.E / c.g
  s c := 1 + ‖c.V‖
  H := max 1 (2 * √(1 - E₀ ^ 2 / 4))⁻¹
  one_le_H := le_max_left _ _
  t_nonneg c hc := div_nonneg (stepSeries_normalH_nonneg _) (by linarith [hc.2.1])
  t_le c hc := (div_le_self (stepSeries_normalH_nonneg _) hc.2.1).trans
    ((stepSeries_normalH_le hE₀ hc.2.2.1).trans (le_max_right _ _))
  one_le_s c _ := le_add_of_nonneg_right (norm_nonneg _)

/-- The matrices at a point. -/
private abbrev MatF (c : SCtx) : Type := Matrix (Fin c.W) (Fin c.W) ℂ

private theorem stepSeries_norm_unitary {W : ℕ} (hW : 1 ≤ W) {U : Matrix (Fin W) (Fin W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin W) ℂ) : ‖U‖ = 1 := by
  have : Nonempty (Fin W) := ⟨⟨0, hW⟩⟩
  exact CStarRing.norm_of_mem_unitary hU

private theorem stepSeries_norm_pow_le {W : ℕ} (hW : 1 ≤ W) (M : Matrix (Fin W) (Fin W) ℂ)
    (n : ℕ) : ‖M ^ n‖ ≤ ‖M‖ ^ n := by
  rcases n with _ | n
  · simp [stepSeries_norm_unitary hW (one_mem _)]
  · exact norm_pow_le' M (Nat.succ_pos n)

private theorem stepSeries_inv_eq {W : ℕ} {U : Matrix (Fin W) (Fin W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin W) ℂ) : U⁻¹ = Uᴴ := by
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.star_eq_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff'.mp hU

/-- `‖V(I + C)‖ ≤ 2(1 + ‖V‖)`. -/
private theorem stepSeries_norm_Q {E₀ : ℝ} {c : SCtx} (hc : c ∈ sAdm E₀) :
    ‖c.V * (1 + c.X.1)‖ ≤ 2 * (1 + ‖c.V‖) := by
  have h1 : ‖1 + c.X.1‖ ≤ 2 := by
    calc ‖1 + c.X.1‖ ≤ ‖(1 : MatF c)‖ + ‖c.X.1‖ := norm_add_le _ _
      _ = 2 := by
        rw [stepSeries_norm_unitary hc.1 (one_mem _), stepSeries_norm_unitary hc.1 hc.2.2.2.1.1]
        norm_num
  calc ‖c.V * (1 + c.X.1)‖ ≤ ‖c.V‖ * ‖1 + c.X.1‖ := norm_mul_le _ _
    _ ≤ ‖c.V‖ * 2 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ ≤ 2 * (1 + ‖c.V‖) := by linarith [norm_nonneg c.V]

private theorem stepSeries_wordMat_fInv {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) (n : ℕ) :
    wordMat C V (PowerSeries.coeff n fInvSeries) = Complex.I ^ n • (V * (1 + C)) ^ n := by
  simp [fInvSeries, wordMat, wV, wC]

/-- `F⁻¹ = Σ_{n ≤ N} (itVU)^n + (itVU)^{N+1}F⁻¹`: the expansion `fInvSeries` of `F⁻¹`. -/
private theorem good_fInv {E₀ : ℝ} (hE₀ : E₀ < 2) :
    Good (R := MatF) (sScl hE₀) (fun c => (stepF c.g c.E c.X.1 c.V)⁻¹)
      (fun c n => wordMat c.X.1 c.V (PowerSeries.coeff n fInvSeries)) := by
  refine ⟨fun n => ?_, fun N => ?_⟩
  · refine ((PBt.const (σ := sScl hE₀) (show (0 : ℝ) ≤ 2 ^ n by positivity)).mul
      (PBt.s_pow n) (fun c hc => (sScl hE₀).s_pow_nonneg hc n)).le fun c hc => ?_
    dsimp only
    rw [stepSeries_wordMat_fInv, norm_smul, norm_pow, Complex.norm_I, one_pow, one_mul]
    refine (stepSeries_norm_pow_le hc.1 _ n).trans ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (stepSeries_norm_Q hc) n
  · have hX : PBt (sScl hE₀) 1 fun c => (sScl hE₀).t c * (2 * (sScl hE₀).s c) :=
      (PBt.t_pow 1).mul ((PBt.const (σ := sScl hE₀) zero_le_two).mul (PBt.s_pow 1)
        (fun c hc => (sScl hE₀).s_pow_nonneg hc 1)) (fun c hc => by
          have := (sScl hE₀).one_le_s c hc; positivity) |>.le fun c _ => by simp
    have hF : PBt (sScl hE₀) 0 fun c => 1 + 2 * (sScl hE₀).H * (sScl hE₀).s c :=
      (PBt.const zero_le_one).add ((PBt.const (σ := sScl hE₀)
        (show (0 : ℝ) ≤ 2 * (sScl hE₀).H by linarith [(sScl hE₀).one_le_H])).mul (PBt.s_pow 1)
        (fun c hc => by have := (sScl hE₀).one_le_s c hc; positivity) |>.le fun c _ => by simp)
    have h := (hX.pow (fun c hc => by
      have := (sScl hE₀).t_nonneg c hc; have := (sScl hE₀).one_le_s c hc; positivity) (N + 1)).mul
        hF (fun c hc => by
          have := (sScl hE₀).one_le_s c hc; have := (sScl hE₀).one_le_H; positivity)
    rw [one_mul, add_zero] at h
    refine h.le fun c hc => ?_
    have ht := (sScl hE₀).t_nonneg c hc
    set Xm := (Complex.I * ((normalH c.E / c.g : ℝ) : ℂ)) • (c.V * (1 + c.X.1)) with hXm
    have hsum : psum (sScl hE₀) (fun c n => wordMat c.X.1 c.V (PowerSeries.coeff n fInvSeries))
        N c = ∑ k ∈ Finset.range (N + 1), Xm ^ k := by
      refine Finset.sum_congr rfl fun n _ => ?_
      dsimp only
      rw [stepSeries_wordMat_fInv, hXm, smul_pow, smul_smul, mul_pow, Complex.ofReal_pow,
        mul_comm]
      rfl
    have e := inv_stepF_eq_sum_add c.g c.E hc.2.2.2.1.1 hc.2.2.2.2 (N + 1)
    dsimp only
    rw [hsum, e, ← hXm, add_sub_cancel_left]
    have hXn : ‖Xm‖ ≤ (sScl hE₀).t c * (2 * (sScl hE₀).s c) := by
      rw [hXm, norm_smul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_of_nonneg (show (0 : ℝ) ≤ normalH c.E / c.g from ht)]
      exact mul_le_mul_of_nonneg_left (stepSeries_norm_Q hc) ht
    have hFn : ‖(stepF c.g c.E c.X.1 c.V)⁻¹‖ ≤ 1 + 2 * (sScl hE₀).H * (sScl hE₀).s c := by
      refine (norm_stepF_le (by linarith [hc.2.1]) c.E hc.2.2.2.1.1 hc.2.2.2.2).2.trans ?_
      have h1 : 2 * normalH c.E * ‖c.V‖ / c.g = 2 * (sScl hE₀).t c * ‖c.V‖ := by
        simp only [sScl]; ring
      rw [h1]
      have := (sScl hE₀).t_le c hc
      have : ‖c.V‖ ≤ (sScl hE₀).s c := by simp [sScl]
      have := norm_nonneg c.V
      nlinarith
    calc ‖Xm ^ (N + 1) * (stepF c.g c.E c.X.1 c.V)⁻¹‖
        ≤ ‖Xm‖ ^ (N + 1) * ‖(stepF c.g c.E c.X.1 c.V)⁻¹‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_pow_le' _ (Nat.succ_pos N))
            (norm_nonneg _))
      _ ≤ _ := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hXn _) hFn (norm_nonneg _)
          (pow_nonneg (mul_nonneg ht (by linarith [(sScl hE₀).one_le_s c hc])) _)

/-- `C + t · iV(I + C)`, the factor `C + itV(I + C)` of (11.3) [lg:eq:matrix-update]. -/
private def linSeries : PowerSeries WordAlg :=
  PowerSeries.C wC + PowerSeries.C (Complex.I • (wV * (1 + wC))) * PowerSeries.X

private theorem stepSeries_linSeries_mul : linSeries * fInvSeries = kSeries := by
  ext n
  simp only [linSeries, add_mul, mul_assoc, map_add, PowerSeries.coeff_C_mul]
  rcases n with _ | m
  · simp [fInvSeries, kSeries]
  · rw [PowerSeries.coeff_succ_X_mul]
    simp only [fInvSeries, kSeries, PowerSeries.coeff_mk, Nat.succ_ne_zero m, ↓reduceIte]
    rw [smul_mul_smul_comm, ← pow_succ', ← pow_succ', mul_smul_comm, ← smul_add, add_mul,
      one_mul]
    congr 1
    abel

private theorem stepSeries_wordMat_lin {W : ℕ} (C V : Matrix (Fin W) (Fin W) ℂ) (n : ℕ) :
    wordMat C V (PowerSeries.coeff n linSeries) =
      if n = 0 then C else if n = 1 then Complex.I • (V * (1 + C)) else 0 := by
  rcases n with _ | _ | n <;> simp [linSeries, wordMat, wC, wV, PowerSeries.coeff_C]

/-- The unrotated update `K̃ = (C + itV(I + C))F⁻¹`. -/
private def kMat (c : SCtx) : MatF c :=
  (c.X.1 + (Complex.I * ((normalH c.E / c.g : ℝ) : ℂ)) • (c.V * (1 + c.X.1))) *
    (stepF c.g c.E c.X.1 c.V)⁻¹

/-- `wordMat` at a point. -/
private def wMat (c : SCtx) : WordAlg →ₐ[ℂ] MatF c := wordMat c.X.1 c.V

private theorem good_K {E₀ : ℝ} (hE₀ : E₀ < 2) :
    Good (R := MatF) (sScl hE₀) kMat
      (fun c n => wMat c (PowerSeries.coeff n kSeries)) := by
  have hlin : Good (R := MatF) (sScl hE₀)
      (fun c => c.X.1 + (Complex.I * ((normalH c.E / c.g : ℝ) : ℂ)) • (c.V * (1 + c.X.1)))
      (fun c n => wMat c (PowerSeries.coeff n linSeries)) := by
    refine (Good.fin 1 (fun n => ?_) (fun c n hn => ?_)).congr (fun c _ => ?_) (fun _ _ _ => rfl)
    · refine ((PBt.const (σ := sScl hE₀) zero_le_two).mul (PBt.s_pow 1)
        (fun c hc => (sScl hE₀).s_pow_nonneg hc 1)).le fun c hc => ?_
      have h2 : 2 ≤ 2 * (sScl hE₀).s c ^ 1 := by
        have := (sScl hE₀).one_le_s c hc; rw [pow_one]; linarith
      rw [wMat, stepSeries_wordMat_lin]
      split_ifs
      · rw [stepSeries_norm_unitary hc.1 hc.2.2.2.1.1]; linarith
      · rw [norm_smul, Complex.norm_I, one_mul, pow_one]; exact stepSeries_norm_Q hc
      · rw [norm_zero]; linarith
    · rw [wMat, stepSeries_wordMat_lin]
      simp only [show n ≠ 0 by omega, show n ≠ 1 by omega, ↓reduceIte]
    · simp only [psum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, wMat,
        stepSeries_wordMat_lin, pow_zero, pow_one, Complex.ofReal_one, one_smul, one_ne_zero,
        ↓reduceIte, smul_smul]
      rw [mul_comm]
      rfl
  refine (hlin.mulS (R := MatF) (S := fun _ => linSeries) (T := fun _ => fInvSeries) wMat
    (good_fInv hE₀)).congr (fun c _ => rfl) fun c _ n => ?_
  rw [stepSeries_linSeries_mul]

/-- The conjugate transpose. -/
private def ctHom (c : SCtx) : MatF c →+ MatF c :=
  (Matrix.conjTransposeAddEquiv (Fin c.W) (Fin c.W) ℂ).toAddMonoidHom

private theorem Good.ct {E₀ : ℝ} {hE₀ : E₀ < 2} {a : ∀ c, MatF c} {α : ∀ c, ℕ → MatF c}
    (h : Good (R := MatF) (sScl hE₀) a α) :
    Good (R := MatF) (sScl hE₀) (fun c => (a c)ᴴ) (fun c n => (α c n)ᴴ) :=
  h.map (R' := MatF) ctHom (fun c x y => by simp [ctHom, Matrix.conjTranspose_smul])
    (fun c _ y => by simp [ctHom, Matrix.l2_opNorm_conjTranspose])

private theorem stepSeries_wordMat_fInvAdj {W : ℕ} {C V : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (hV : V.IsHermitian) (n : ℕ) :
    wordMat C V (PowerSeries.coeff n fInvAdjSeries) =
      (wordMat C V (PowerSeries.coeff n fInvSeries))ᴴ := by
  rw [stepSeries_wordMat_fInv]
  simp [fInvAdjSeries, wordMat, wV, wCi, Matrix.conjTranspose_smul, Matrix.conjTranspose_pow,
    Matrix.conjTranspose_mul, hV.eq, stepSeries_inv_eq hC]

private theorem stepSeries_wordMat_kAdj {W : ℕ} {C V : Matrix (Fin W) (Fin W) ℂ}
    (hC : C ∈ Matrix.unitaryGroup (Fin W) ℂ) (hV : V.IsHermitian) (n : ℕ) :
    wordMat C V (PowerSeries.coeff n kAdjSeries) =
      (wordMat C V (PowerSeries.coeff n kSeries))ᴴ := by
  rcases n with _ | n
  · simp [kAdjSeries, kSeries, wordMat, wCi, wC, stepSeries_inv_eq hC]
  · simp [kAdjSeries, kSeries, wordMat, wV, wCi, wC, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_pow, Matrix.conjTranspose_mul, hV.eq, stepSeries_inv_eq hC]

private theorem good_fInvAdj {E₀ : ℝ} (hE₀ : E₀ < 2) :
    Good (R := MatF) (sScl hE₀) (fun c => ((stepF c.g c.E c.X.1 c.V)⁻¹)ᴴ)
      (fun c n => wMat c (PowerSeries.coeff n fInvAdjSeries)) :=
  (good_fInv hE₀).ct.congr (fun _ _ => rfl) fun _c hc n =>
    (stepSeries_wordMat_fInvAdj hc.2.2.2.1.1 hc.2.2.2.2 n).symm

private theorem good_KAdj {E₀ : ℝ} (hE₀ : E₀ < 2) :
    Good (R := MatF) (sScl hE₀) (fun c => (kMat c)ᴴ)
      (fun c n => wMat c (PowerSeries.coeff n kAdjSeries)) :=
  (good_K hE₀).ct.congr (fun _ _ => rfl) fun _c hc n =>
    (stepSeries_wordMat_kAdj hc.2.2.2.1.1 hc.2.2.2.2 n).symm

/-- `K̃^k`, through `K̃* = K̃⁻¹` for `k < 0`. -/
private def kPowMat (c : SCtx) (k : ℤ) : MatF c :=
  if 0 ≤ k then kMat c ^ k.toNat else (kMat c)ᴴ ^ (-k).toNat

private theorem good_kPow {E₀ : ℝ} (hE₀ : E₀ < 2) {k : ℤ} (hk : k ≠ 0) :
    Good (R := MatF) (sScl hE₀) (fun c => kPowMat c k)
      (fun c n => wMat c (PowerSeries.coeff n (kPowSeries k))) := by
  by_cases h : 0 ≤ k
  · have e : k.toNat = (k.toNat - 1) + 1 := by omega
    refine ((good_K hE₀).powS (R := MatF) (S := fun _ => kSeries) wMat (k.toNat - 1)).congr
      (fun c _ => ?_) (fun c _ n => ?_)
    · simp only [kPowMat, h, ↓reduceIte, ← e]
    · simp only [kPowSeries, h, ↓reduceIte, ← e]
  · have e : (-k).toNat = ((-k).toNat - 1) + 1 := by omega
    refine ((good_KAdj hE₀).powS (R := MatF) (S := fun _ => kAdjSeries) wMat
      ((-k).toNat - 1)).congr (fun c _ => ?_) (fun c _ n => ?_)
    · simp only [kPowMat, h, ↓reduceIte, ← e]
    · simp only [kPowSeries, h, ↓reduceIte, ← e]

/-! ### Traces and marked forms -/

private theorem stepSeries_eq_wordOf (u : List WLetter) :
    FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℂ) (X := WLetter) (wordOf u) =
      MonoidAlgebra.of ℂ (FreeMonoid WLetter) (FreeMonoid.ofList u) := by
  induction u with
  | nil => simp [wordOf]; rfl
  | cons l u ih =>
    simp only [wordOf, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]

private theorem stepSeries_wordFun_wordOf (φ : List WLetter → CfgPoly) (u : List WLetter) :
    wordFun φ (wordOf u) = φ u := by
  simp only [wordFun, LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply,
    stepSeries_eq_wordOf]
  simp [MonoidAlgebra.of_apply]

/-- Linear maps on words agree if they agree on basis words. -/
private theorem stepSeries_lin_ext {M : Type} [AddCommGroup M] [Module ℂ M]
    (L₁ L₂ : WordAlg →ₗ[ℂ] M) (h : ∀ u, L₁ (wordOf u) = L₂ (wordOf u)) : L₁ = L₂ := by
  let e : WordAlg ≃ₗ[ℂ] (FreeMonoid WLetter →₀ ℂ) :=
    FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearEquiv.trans
      (MonoidAlgebra.coeffLinearEquiv ℂ)
  have : L₁ ∘ₗ e.symm.toLinearMap = L₂ ∘ₗ e.symm.toLinearMap := by
    refine Finsupp.lhom_ext fun m b => ?_
    have he : e.symm (Finsupp.single m b) = b • wordOf (FreeMonoid.toList m) := by
      apply e.injective
      rw [e.apply_symm_apply, map_smul]
      simp [e, stepSeries_eq_wordOf, MonoidAlgebra.of_apply]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, he, map_smul, h]
  ext x
  have := congrArg (fun L => L (e x)) this
  simpa using this

private theorem stepSeries_norm_vecForm_le {W : ℕ} (M : Matrix (Fin W) (Fin W) ℂ)
    {v : EuclideanSpace ℂ (Fin W)} (hv : ‖v‖ = 1) : ‖vecForm M v‖ ≤ ‖M‖ := by
  unfold vecForm
  calc ‖inner ℂ v (Matrix.toEuclideanLin M v)‖ ≤ ‖v‖ * ‖Matrix.toEuclideanLin M v‖ :=
        norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖M‖ * ‖v‖) := mul_le_mul_of_nonneg_left
        ((Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) M).le_opNorm v) (norm_nonneg _)
    _ = ‖M‖ := by rw [hv]; ring

private theorem stepSeries_norm_trace_le {W : ℕ} (hW : 1 ≤ W) (M : Matrix (Fin W) (Fin W) ℂ) :
    ‖(W : ℂ)⁻¹ * M.trace‖ ≤ ‖M‖ := by
  have hdiag : ∀ i, ‖M i i‖ ≤ ‖M‖ := fun i => by
    have : M i i = vecForm M (EuclideanSpace.single i (1 : ℂ)) := by
      simp [vecForm, Matrix.toLpLin_apply, EuclideanSpace.inner_single_left]
    rw [this]
    exact stepSeries_norm_vecForm_le M (by simp)
  have htr : ‖M.trace‖ ≤ W * ‖M‖ := by
    calc ‖M.trace‖ = ‖∑ i, M i i‖ := rfl
      _ ≤ ∑ i, ‖M i i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin W, ‖M‖ := Finset.sum_le_sum fun i _ => hdiag i
      _ = W * ‖M‖ := by simp
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  calc (W : ℝ)⁻¹ * ‖M.trace‖ ≤ (W : ℝ)⁻¹ * (W * ‖M‖) := by gcongr
    _ = ‖M‖ := by field_simp

/-- `v* M v` as a linear map. -/
private def vfLin {W : ℕ} (v : EuclideanSpace ℂ (Fin W)) : Matrix (Fin W) (Fin W) ℂ →ₗ[ℂ] ℂ where
  toFun M := vecForm M v
  map_add' M N := by simp [vecForm, map_add]
  map_smul' a M := by simp [vecForm]

/-- `W⁻¹ Tr M` as a linear map. -/
private def trLin (W : ℕ) : Matrix (Fin W) (Fin W) ℂ →ₗ[ℂ] ℂ :=
  (W : ℂ)⁻¹ • Matrix.traceLinearMap (Fin W) ℂ ℂ

private theorem cfgEval_trcFun {W : ℕ} (hW : 1 ≤ W) (g : ℝ) (X : State W)
    (V : Matrix (Fin W) (Fin W) ℂ) (x : WordAlg) :
    cfgEval g X V (trcFun x) = (W : ℂ)⁻¹ * (wordMat X.1 V x).trace := by
  have h := stepSeries_lin_ext ((cfgEval g X V).toLinearMap ∘ₗ trcFun)
    (trLin W ∘ₗ (wordMat X.1 V).toLinearMap) fun u => by
      simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, trcFun,
        stepSeries_wordFun_wordOf, trLin, LinearMap.smul_apply, Matrix.traceLinearMap_apply,
        smul_eq_mul]
      split_ifs with hu
      · subst hu
        have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast (show W ≠ 0 by omega)
        simp [wordOf, Matrix.trace_one, hW']
      · simp [cfgEval]
  exact LinearMap.congr_fun h x

private theorem cfgEval_mrkFun {W : ℕ} (g : ℝ) {X : State W} (hX : ‖X.2‖ = 1)
    (V : Matrix (Fin W) (Fin W) ℂ) (x : WordAlg) :
    cfgEval g X V (mrkFun x) = vecForm (wordMat X.1 V x) X.2 := by
  have h := stepSeries_lin_ext ((cfgEval g X V).toLinearMap ∘ₗ mrkFun)
    (vfLin X.2 ∘ₗ (wordMat X.1 V).toLinearMap) fun u => by
      simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, mrkFun,
        stepSeries_wordFun_wordOf, vfLin]
      split_ifs with hu
      · subst hu
        simp [wordOf, vecForm, inner_self_eq_norm_sq_to_K, hX]
      · simp [cfgEval]
        rfl
  exact LinearMap.congr_fun h x

/-- The expansion of `W⁻¹ Tr K̃^k`. -/
private theorem good_trc {E₀ : ℝ} (hE₀ : E₀ < 2) {k : ℤ} (hk : k ≠ 0) :
    Good (R := fun _ => ℂ) (sScl hE₀) (fun c => (c.W : ℂ)⁻¹ * (kPowMat c k).trace)
      (fun c n => cfgEval c.g c.X c.V
        (PowerSeries.coeff n (seriesMap trcFun (kPowSeries k)))) := by
  refine ((good_kPow hE₀ hk).map (R' := fun _ => ℂ) (fun c => (trLin c.W).toAddMonoidHom)
    (fun c x y => by simp) (fun c hc y => ?_)).congr (fun c _ => ?_) (fun c hc n => ?_)
  · simpa [trLin] using stepSeries_norm_trace_le hc.1 y
  · simp [trLin]
  · simp [seriesMap, cfgEval_trcFun hc.1, trLin, wMat]

/-- The expansion of `v* M v` from an expansion of `M`. -/
private theorem good_mrk {E₀ : ℝ} (hE₀ : E₀ < 2) {a : ∀ c, MatF c} {S : PowerSeries WordAlg}
    (h : Good (R := MatF) (sScl hE₀) a (fun c n => wMat c (PowerSeries.coeff n S))) :
    Good (R := fun _ => ℂ) (sScl hE₀) (fun c => vecForm (a c) c.X.2)
      (fun c n => cfgEval c.g c.X c.V (PowerSeries.coeff n (seriesMap mrkFun S))) := by
  refine (h.map (R' := fun _ => ℂ) (fun c => (vfLin c.X.2).toAddMonoidHom)
    (fun c x y => by simp) (fun c hc y => ?_)).congr (fun c _ => ?_) (fun c hc n => ?_)
  · exact stepSeries_norm_vecForm_le y hc.2.2.2.1.2
  · rfl
  · simp only [seriesMap, PowerSeries.coeff_mk, cfgEval_mrkFun _ hc.2.2.2.1.2]
    rfl

/-! ### The normalization `Y = ‖F^{−*}v‖²` and its inverse -/

/-- `Y = v* F⁻¹ F^{−*} v`. -/
private def yVal (c : SCtx) : ℂ :=
  vecForm ((stepF c.g c.E c.X.1 c.V)⁻¹ * ((stepF c.g c.E c.X.1 c.V)⁻¹)ᴴ) c.X.2

private theorem stepSeries_vecForm_conj {W : ℕ} (A M : Matrix (Fin W) (Fin W) ℂ)
    (v : EuclideanSpace ℂ (Fin W)) :
    vecForm (A * M * Aᴴ) v = vecForm M (Matrix.toEuclideanLin Aᴴ v) := by
  unfold vecForm
  have e : Matrix.toEuclideanLin (A * M * Aᴴ) v = Matrix.toEuclideanLin A
      (Matrix.toEuclideanLin M (Matrix.toEuclideanLin Aᴴ v)) := by
    simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  rw [e, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]

private theorem stepSeries_yVal (c : SCtx) :
    yVal c = ((‖stepVec c.g c.E c.X c.V‖ ^ 2 : ℝ) : ℂ) := by
  have := stepSeries_vecForm_conj (stepF c.g c.E c.X.1 c.V)⁻¹ 1 c.X.2
  rw [Matrix.mul_one] at this
  have h1 : ∀ w : EuclideanSpace ℂ (Fin c.W), Matrix.toEuclideanLin (1 : MatF c) w = w :=
    fun w => by simp
  rw [yVal, this, vecForm, h1, inner_self_eq_norm_sq_to_K, stepVec]
  push_cast
  rfl

/-- `‖F^{−*}v‖ > 0` and `‖F^{−*}v‖⁻¹ ≤ 1 + 2H(1 + ‖V‖)`. -/
private theorem stepSeries_norm_w {E₀ : ℝ} {hE₀ : E₀ < 2} {c : SCtx} (hc : c ∈ (sScl hE₀).P) :
    0 < ‖stepVec c.g c.E c.X c.V‖ ∧
      ‖stepVec c.g c.E c.X c.V‖⁻¹ ≤ 1 + 2 * (sScl hE₀).H * (sScl hE₀).s c := by
  have hg : 0 < c.g := by linarith [hc.2.1]
  have hF := (norm_stepF_le hg c.E hc.2.2.2.1.1 hc.2.2.2.2).1
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_stepF c.g c.E hc.2.2.2.1.1 hc.2.2.2.2)
  have hadj : Matrix.toEuclideanLin (stepF c.g c.E c.X.1 c.V)ᴴ (stepVec c.g c.E c.X c.V) =
      c.X.2 := by
    have e : (stepF c.g c.E c.X.1 c.V)ᴴ * ((stepF c.g c.E c.X.1 c.V)⁻¹)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.conjTranspose_one]
    have := congrArg (fun M => Matrix.toEuclideanLin M c.X.2) e
    simpa [stepVec, Matrix.toLpLin_apply, Matrix.mulVec_mulVec] using this
  have hL : 1 ≤ (1 + 2 * normalH c.E * ‖c.V‖ / c.g) * ‖stepVec c.g c.E c.X c.V‖ := by
    calc (1 : ℝ) = ‖c.X.2‖ := hc.2.2.2.1.2.symm
      _ = ‖Matrix.toEuclideanLin (stepF c.g c.E c.X.1 c.V)ᴴ (stepVec c.g c.E c.X c.V)‖ := by
          rw [hadj]
      _ ≤ ‖(stepF c.g c.E c.X.1 c.V)ᴴ‖ * ‖stepVec c.g c.E c.X c.V‖ :=
          (Matrix.toEuclideanCLM (n := Fin c.W) (𝕜 := ℂ) _).le_opNorm _
      _ ≤ _ := by
          rw [Matrix.l2_opNorm_conjTranspose]
          exact mul_le_mul_of_nonneg_right hF (norm_nonneg _)
  have hpos : 0 < ‖stepVec c.g c.E c.X c.V‖ := by
    rcases (norm_nonneg (stepVec c.g c.E c.X c.V)).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hL; linarith
  refine ⟨hpos, ?_⟩
  have h1 : 2 * normalH c.E * ‖c.V‖ / c.g = 2 * (sScl hE₀).t c * ‖c.V‖ := by
    simp only [sScl]; ring
  have ht := (sScl hE₀).t_le c hc
  have ht0 := (sScl hE₀).t_nonneg c hc
  have hs : ‖c.V‖ ≤ (sScl hE₀).s c := by simp [sScl]
  rw [inv_le_iff_one_le_mul₀ hpos]
  refine hL.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  rw [h1]
  have := norm_nonneg c.V
  nlinarith

private theorem good_Y {E₀ : ℝ} (hE₀ : E₀ < 2) :
    Good (R := fun _ => ℂ) (sScl hE₀) yVal
      (fun c n => cfgEval c.g c.X c.V (PowerSeries.coeff n ySeries)) :=
  good_mrk hE₀ ((good_fInv hE₀).mulS (R := MatF) (S := fun _ => fInvSeries)
    (T := fun _ => fInvAdjSeries) wMat (good_fInvAdj hE₀))

private theorem stepSeries_constantCoeff_y :
    PowerSeries.constantCoeff ySeries = ((1 : CfgPolyˣ) : CfgPoly) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ySeries, seriesMap, PowerSeries.coeff_mk,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]
  have h1 : PowerSeries.constantCoeff fInvSeries = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; simp [fInvSeries]
  have h2 : PowerSeries.constantCoeff fInvAdjSeries = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; simp [fInvAdjSeries]
  rw [h1, h2, mul_one, show (1 : WordAlg) = wordOf [] by simp [wordOf], mrkFun,
    stepSeries_wordFun_wordOf]
  simp

private theorem good_yInv {E₀ : ℝ} (hE₀ : E₀ < 2) :
    Good (R := fun _ => ℂ) (sScl hE₀) (fun c => (yVal c)⁻¹)
      (fun c n => cfgEval c.g c.X c.V (PowerSeries.coeff n yInvSeries)) := by
  have hY := good_Y hE₀
  have hβ : ∀ n, PBt (sScl hE₀) 0 fun c =>
      ‖cfgEval c.g c.X c.V (PowerSeries.coeff n yInvSeries)‖ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | n
      · refine (PBt.const zero_le_one).le fun c _ => ?_
        simp [yInvSeries, PowerSeries.coeff_invOfUnit]
      · refine (PBt.sum (Finset.HasAntidiagonal.antidiagonal (n + 1))
          (f := fun x c => if x.2 < n + 1 then
            ‖cfgEval c.g c.X c.V (PowerSeries.coeff x.1 ySeries)‖ *
              ‖cfgEval c.g c.X c.V (PowerSeries.coeff x.2 yInvSeries)‖ else 0)
          fun x _ => ?_).le fun c _ => ?_
        · by_cases hx : x.2 < n + 1
          · simpa only [hx, ↓reduceIte] using (hY.1 x.1).mul (ih x.2 hx)
              (fun _ _ => norm_nonneg _)
          · simpa only [hx, ↓reduceIte] using PBt.zero (σ := sScl hE₀) 0
        · rw [yInvSeries, PowerSeries.coeff_invOfUnit, ← yInvSeries]
          simp only [Nat.succ_ne_zero, ↓reduceIte, inv_one, Units.val_one, neg_mul, one_mul,
            map_neg, map_sum, norm_neg]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
          split_ifs
          · rw [map_mul, norm_mul]
          · simp
  have hδ : ∀ c ∈ (sScl hE₀).P, ∀ n, cauchy (R := fun _ => ℂ)
      (fun c n => cfgEval c.g c.X c.V (PowerSeries.coeff n ySeries))
      (fun c n => cfgEval c.g c.X c.V (PowerSeries.coeff n yInvSeries)) c n =
        if n = 0 then 1 else 0 := by
    intro c _ n
    rw [cauchy, ← coeff_mul_map, yInvSeries,
      PowerSeries.mul_invOfUnit _ _ stepSeries_constantCoeff_y, PowerSeries.coeff_one]
    split_ifs <;> simp
  have hinv : PBt (sScl hE₀) 0 fun c => ‖(yVal c)⁻¹‖ := by
    refine ((PBt.const zero_le_one).add ((PBt.const (σ := sScl hE₀)
      (show (0 : ℝ) ≤ 2 * (sScl hE₀).H by linarith [(sScl hE₀).one_le_H])).mul (PBt.s_pow 1)
      (fun c hc => (sScl hE₀).s_pow_nonneg hc 1)) |>.pow (fun c hc => by
        have := (sScl hE₀).s_pow_nonneg hc 1; have := (sScl hE₀).one_le_H
        positivity) 2).le fun c hc => ?_
    obtain ⟨hpos, hle⟩ := stepSeries_norm_w hc
    rw [stepSeries_yVal, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      ← inv_pow, pow_one]
    exact pow_le_pow_left₀ (by positivity) hle 2
  refine Good.inv hY hβ hδ hinv fun c hc => ?_
  rw [stepSeries_yVal]
  have := (stepSeries_norm_w hc).1
  exact_mod_cast (by positivity : (0 : ℝ) < ‖stepVec c.g c.E c.X c.V‖ ^ 2).ne'

/-! ### One step of a polynomial in the observables -/

private theorem stepSeries_norm_normalPhase (E : ℝ) : ‖normalPhase E‖ = 1 := by
  unfold normalPhase
  rw [norm_neg, show (2 : ℂ) * ((freeAngle E : ℂ) * Complex.I) =
    ((2 * freeAngle E : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private theorem stepSeries_norm_stepPhase (E : ℝ) : ‖stepPhase E‖ = 1 := by
  unfold stepPhase
  rw [show -((freeAngle E : ℂ) * Complex.I) = ((-freeAngle E : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private theorem stepSeries_star_eq_inv {z : ℂ} (h : ‖z‖ = 1) : star z = z⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h]
  simp

/-- `C′^k = (−e^{−2iθ})^k K̃^k`, `k ∈ ℤ`. -/
private theorem stepSeries_stepC_zpow {E₀ : ℝ} {c : SCtx} (hc : c ∈ sAdm E₀) (k : ℤ) :
    stepC c.g c.E c.X.1 c.V ^ k = (-normalPhase c.E) ^ k • kPowMat c k := by
  have hK : stepC c.g c.E c.X.1 c.V = (-normalPhase c.E) • kMat c := rfl
  cases k with
  | ofNat n =>
    simp only [kPowMat, Int.ofNat_eq_natCast, Int.natCast_nonneg, ↓reduceIte, zpow_natCast,
      Int.toNat_natCast, hK, smul_pow]
  | negSucc m =>
    have hU := pow_mem (stepC_mem_unitaryGroup c.g c.E hc.2.2.2.1.1 hc.2.2.2.2) (m + 1)
    have h0 : ¬ (0 : ℤ) ≤ Int.negSucc m := by omega
    have h1 : (-Int.negSucc m).toNat = m + 1 := by omega
    rw [zpow_negSucc, zpow_negSucc, stepSeries_inv_eq hU, kPowMat]
    simp only [h0, ↓reduceIte, h1]
    rw [hK, smul_pow,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_pow, stepSeries_star_eq_inv (by
        rw [norm_pow, norm_neg, stepSeries_norm_normalPhase, one_pow])]

/-- The unrotated value of a variable after one step: `W⁻¹ Tr K̃^k`,
`v*F⁻¹K̃^kF^{−*}v / Y`, `W⁻¹`, `g⁻²`. -/
private def trueVal (c : SCtx) : ObsVar → ℂ
  | .m k => (c.W : ℂ)⁻¹ * (kPowMat c k.1).trace
  | .f k => vecForm ((stepF c.g c.E c.X.1 c.V)⁻¹ * kPowMat c k.1 *
      ((stepF c.g c.E c.X.1 c.V)⁻¹)ᴴ) c.X.2 * (yVal c)⁻¹
  | .w => (c.W : ℂ)⁻¹
  | .γ => (((c.g ^ 2)⁻¹ : ℝ) : ℂ)

private theorem stepSeries_vecForm_smul {W : ℕ} (z α : ℂ) (M : Matrix (Fin W) (Fin W) ℂ)
    (w : EuclideanSpace ℂ (Fin W)) :
    vecForm (z • M) (α • w) = z * (star α * α) * vecForm M w := by
  simp only [vecForm, map_smul, LinearMap.smul_apply, inner_smul_left, inner_smul_right]
  simp only [Complex.star_def]
  ring

private theorem stepSeries_obsEval_X {E₀ : ℝ} {c : SCtx} (hc : c ∈ sAdm E₀) (v : ObsVar) :
    obsEval c.g (stepState c.g c.E c.X c.V) (X v) = (-normalPhase c.E) ^ v.idx * trueVal c v := by
  cases v with
  | m k =>
    simp only [obsEval, aeval_X, obsM, stepState, stepSeries_stepC_zpow hc, Matrix.trace_smul,
      ObsVar.idx, trueVal, smul_eq_mul]
    ring
  | f k =>
    have e1 : vecForm ((stepF c.g c.E c.X.1 c.V)⁻¹ * kPowMat c k.1 *
        ((stepF c.g c.E c.X.1 c.V)⁻¹)ᴴ) c.X.2 = vecForm (kPowMat c k.1) (stepVec c.g c.E c.X c.V) :=
      stepSeries_vecForm_conj _ _ _
    have hα : star (stepPhase c.E * ((‖stepVec c.g c.E c.X c.V‖⁻¹ : ℝ) : ℂ)) *
        (stepPhase c.E * ((‖stepVec c.g c.E c.X c.V‖⁻¹ : ℝ) : ℂ)) =
          (((‖stepVec c.g c.E c.X c.V‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul', norm_mul, stepSeries_norm_stepPhase, one_mul,
        Complex.norm_real, norm_inv, norm_norm]
      push_cast
      ring
    simp only [obsEval, aeval_X, obsF, stepState, ObsVar.idx, trueVal]
    rw [stepSeries_stepC_zpow hc, stepSeries_vecForm_smul, e1, stepSeries_yVal, hα]
    push_cast
    ring
  | w => simp [obsEval, ObsVar.idx, trueVal]
  | γ => simp [obsEval, ObsVar.idx, trueVal]

/-- Products of configuration series. -/
private theorem Good.mulC {E₀ : ℝ} {hE₀ : E₀ < 2} {a b : SCtx → ℂ}
    {S T : SCtx → PowerSeries CfgPoly}
    (ha : Good (R := fun _ => ℂ) (sScl hE₀) a
      (fun c n => cfgEval c.g c.X c.V (PowerSeries.coeff n (S c))))
    (hb : Good (R := fun _ => ℂ) (sScl hE₀) b
      (fun c n => cfgEval c.g c.X c.V (PowerSeries.coeff n (T c)))) :
    Good (R := fun _ => ℂ) (sScl hE₀) (fun c => a c * b c)
      (fun c n => cfgEval c.g c.X c.V (PowerSeries.coeff n (S c * T c))) :=
  (ha.mul hb).congr (fun _ _ => rfl) fun c _ n => by rw [cauchy, coeff_mul_map]

/-- A constant coefficient series `C(x)` with `|x| ≤ 1`. -/
private theorem good_constVar {E₀ : ℝ} (hE₀ : E₀ < 2) (x : CfgVar) (b : SCtx → ℂ)
    (hb : ∀ c ∈ (sScl hE₀).P, cfgEval c.g c.X c.V (X x) = b c ∧ ‖b c‖ ≤ 1) :
    Good (R := fun _ => ℂ) (sScl hE₀) b
      (fun c n => cfgEval c.g c.X c.V (PowerSeries.coeff n (PowerSeries.C (X x)))) := by
  refine (Good.fin (R := fun _ => ℂ) (σ := sScl hE₀)
    (α := fun c n => cfgEval c.g c.X c.V (PowerSeries.coeff n (PowerSeries.C (X x)))) 0
    (fun n => (PBt.const zero_le_one).le fun c hc => ?_)
    (fun c n hn => by simp [PowerSeries.coeff_C, show n ≠ 0 by omega])).congr
    (fun c hc => ?_) (fun _ _ _ => rfl)
  · rw [PowerSeries.coeff_C]
    split_ifs
    · rw [(hb c hc).1]; exact (hb c hc).2
    · simp
  · simp [psum, PowerSeries.coeff_C, (hb c hc).1]

private theorem stepSeries_X (v : ObsVar) : stepSeries (X v) = match v with
    | .m k => seriesMap trcFun (kPowSeries k.1)
    | .f k => seriesMap mrkFun (fInvSeries * kPowSeries k.1 * fInvAdjSeries) * yInvSeries
    | .w => PowerSeries.C (X .w)
    | .γ => PowerSeries.C (X .γ) := by
  rw [stepSeries, aeval_X]

private theorem good_var {E₀ : ℝ} (hE₀ : E₀ < 2) (v : ObsVar) :
    Good (R := fun _ => ℂ) (sScl hE₀) (fun c => trueVal c v)
      (fun c n => cfgEval c.g c.X c.V (PowerSeries.coeff n (stepSeries (X v)))) := by
  cases v with
  | m k =>
    exact (good_trc hE₀ k.2).congr (fun _ _ => rfl) fun c _ n => by rw [stepSeries_X]
  | f k =>
    have h1 := good_mrk hE₀ (((good_fInv hE₀).mulS (R := MatF) (S := fun _ => fInvSeries)
      (T := fun _ => kPowSeries k.1) wMat (good_kPow hE₀ k.2)).mulS (R := MatF)
      (T := fun _ => fInvAdjSeries) wMat (good_fInvAdj hE₀))
    exact (h1.mulC (T := fun _ => yInvSeries) (good_yInv hE₀)).congr (fun _ _ => rfl)
      fun c _ n => by rw [stepSeries_X]
  | w =>
    refine (good_constVar hE₀ .w (fun c => trueVal c .w) fun c hc =>
      ⟨by simp [cfgEval, trueVal], ?_⟩).congr (fun _ _ => rfl) fun c _ n => by rw [stepSeries_X]
    rw [trueVal, norm_inv, Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hc.1)
  | γ =>
    refine (good_constVar hE₀ .γ (fun c => trueVal c .γ) fun c hc =>
      ⟨by simp [cfgEval, trueVal], ?_⟩).congr (fun _ _ => rfl) fun c _ n => by rw [stepSeries_X]
    rw [trueVal, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (by nlinarith [hc.2.1])

private theorem good_rotVar {E₀ : ℝ} (hE₀ : E₀ < 2) (v : ObsVar) :
    Good (R := fun _ => ℂ) (sScl hE₀) (fun c => obsEval c.g (stepState c.g c.E c.X c.V) (X v))
      (fun c n => cfgEval c.g c.X c.V
        (PowerSeries.coeff n (stepSeries (rotPoly c.E (X v))))) := by
  refine ((good_var hE₀ v).smul (fun c => (-normalPhase c.E) ^ v.idx) fun c _ => ?_).congr
    (fun c hc => ?_) (fun c _ n => ?_)
  · rw [norm_zpow, norm_neg, stepSeries_norm_normalPhase, one_zpow]
  · rw [stepSeries_obsEval_X hc, smul_eq_mul]
  · rw [rotPoly, aeval_X, MvPolynomial.C_mul', map_smul, PowerSeries.coeff_smul, map_smul]

/-- The expansion `stepSeries (rotPoly E p)` of `p(X′)`, for every polynomial `p`. -/
private theorem good_poly {E₀ : ℝ} (hE₀ : E₀ < 2) (p : ObsPoly) :
    Good (R := fun _ => ℂ) (sScl hE₀) (fun c => obsEval c.g (stepState c.g c.E c.X c.V) p)
      (fun c n => cfgEval c.g c.X c.V (PowerSeries.coeff n (stepSeries (rotPoly c.E p)))) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine (Good.fin (R := fun _ => ℂ) (σ := sScl hE₀) (α := fun _ n => if n = 0 then a else 0) 0
      (fun n => (PBt.const (norm_nonneg a)).le fun c _ => ?_)
      (fun c n hn => by simp [show n ≠ 0 by omega])).congr (fun c _ => ?_) (fun c _ n => ?_)
    · split_ifs <;> simp
    · simp [psum, obsEval]
    · rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes,
        Algebra.algebraMap_eq_smul_one, PowerSeries.coeff_smul, PowerSeries.coeff_one, map_smul]
      split_ifs <;> simp
  | add p q hp hq =>
    exact (hp.add hq).congr (fun c _ => (map_add _ _ _).symm)
      (fun c _ n => by rw [map_add, map_add, map_add, map_add])
  | mul_X p v hp =>
    exact (hp.mulC (S := fun c => stepSeries (rotPoly c.E p))
      (T := fun c => stepSeries (rotPoly c.E (X v))) (good_rotVar hE₀ v)).congr
      (fun c _ => (map_mul _ _ _).symm)
      (fun c _ n => by rw [map_mul (rotPoly c.E), map_mul stepSeries])

private theorem psum_complex {E₀ : ℝ} {hE₀ : E₀ < 2} (α : SCtx → ℕ → ℂ) (N : ℕ) (c : SCtx) :
    psum (R := fun _ => ℂ) (sScl hE₀) α N c =
      ∑ n ∈ Finset.range (N + 1), (((sScl hE₀).t c ^ n : ℝ) : ℂ) * α c n :=
  Finset.sum_congr rfl fun _ _ => smul_eq_mul _ _

/-! ### The increment `c = −½ log Y` -/

private theorem Good.powC {E₀ : ℝ} {hE₀ : E₀ < 2} {a : SCtx → ℂ}
    {S : SCtx → PowerSeries CfgPoly}
    (ha : Good (R := fun _ => ℂ) (sScl hE₀) a
      (fun c n => cfgEval c.g c.X c.V (PowerSeries.coeff n (S c)))) :
    ∀ k : ℕ, Good (R := fun _ => ℂ) (sScl hE₀) (fun c => a c ^ (k + 1))
      (fun c n => cfgEval c.g c.X c.V (PowerSeries.coeff n (S c ^ (k + 1))))
  | 0 => by simpa only [zero_add, pow_one] using ha
  | k + 1 => by simpa only [← pow_succ] using (Good.powC ha k).mulC ha

/-- `Z = Y − 1` with the series `ySeries − 1`. -/
private theorem good_Z {E₀ : ℝ} (hE₀ : E₀ < 2) :
    Good (R := fun _ => ℂ) (sScl hE₀) (fun c => yVal c - 1)
      (fun c n => cfgEval c.g c.X c.V (PowerSeries.coeff n (ySeries - 1))) := by
  refine ((good_Y hE₀).add (Good.fin (R := fun _ => ℂ) (σ := sScl hE₀)
    (α := fun _ n => if n = 0 then (-1 : ℂ) else 0) 0
    (fun n => (PBt.const zero_le_one).le fun c _ => ?_)
    (fun c n hn => by simp [show n ≠ 0 by omega]))).congr (fun c _ => ?_) (fun c _ n => ?_)
  · split_ifs <;> simp
  · simp [psum, sub_eq_add_neg]
  · rw [map_sub, PowerSeries.coeff_one, map_sub]
    split_ifs <;> simp [sub_eq_add_neg]

/-- The coefficient `(−1)^j/(j+1)` of `x^{j+1}` in `log(1 + x)`. -/
private def logCoeff (j : ℕ) : ℂ := (-1 : ℂ) ^ (j + 2) / ((j + 1 : ℕ) : ℂ)

private theorem stepSeries_norm_logCoeff (j : ℕ) : ‖logCoeff j‖ ≤ 1 := by
  rw [logCoeff, norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast]
  have : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos j
  exact div_le_one_of_le₀ this (by positivity)

/-- The truncation `Σ_{j<M} (−1)^{j}/(j+1) x^{j+1}` of `log(1 + x)`. -/
private def logTrunc (x : PowerSeries CfgPoly) (M : ℕ) : PowerSeries CfgPoly :=
  ∑ j ∈ Finset.range M, logCoeff j • x ^ (j + 1)

private theorem stepSeries_coeff_pow_eq_zero {x : PowerSeries CfgPoly}
    (hx : PowerSeries.constantCoeff x = 0) {n k : ℕ} (h : n < k) :
    PowerSeries.coeff n (x ^ k) = 0 := by
  obtain ⟨y, rfl⟩ := PowerSeries.X_dvd_iff.mpr hx
  rw [mul_pow, PowerSeries.coeff_X_pow_mul']
  simp only [show ¬ k ≤ n by omega, ↓reduceIte]

/-- The coefficients of `logSeries x` up to order `M` are those of the truncation. -/
private theorem stepSeries_coeff_logSeries {x : PowerSeries CfgPoly}
    (hx : PowerSeries.constantCoeff x = 0) {n M : ℕ} (h : n ≤ M) :
    PowerSeries.coeff n (logSeries x) = PowerSeries.coeff n (logTrunc x M) := by
  rw [logSeries, PowerSeries.coeff_mk, logTrunc, map_sum, Finset.sum_range_succ',
    ← Finset.sum_range_add_sum_Ico _ h]
  simp only [Nat.cast_zero, div_zero, zero_smul, add_zero, PowerSeries.coeff_smul]
  rw [Finset.sum_eq_zero (s := Finset.Ico n M) fun j hj => by
    rw [Finset.mem_Ico] at hj
    rw [stepSeries_coeff_pow_eq_zero hx (by omega), smul_zero], add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [logCoeff, Nat.cast_succ]

private theorem stepSeries_constantCoeff_x :
    PowerSeries.constantCoeff (ySeries - 1) = 0 := by
  rw [map_sub, stepSeries_constantCoeff_y, Units.val_one, map_one, sub_self]

/-- `|log(1 + z) − Σ_{j<N} (−1)^j z^{j+1}/(j+1)| ≤ 2^{N+1}|z|^{N+1}(3 + |z| + (1+z)⁻¹ +
Σ_{j<N}|z|^{j+1})` for `z > −1`. -/
private theorem stepSeries_log_rem {z : ℝ} (hz : -1 < z) (N : ℕ) :
    |Real.log (1 + z) - ∑ j ∈ Finset.range N, (-1) ^ (j + 2) / ((j : ℝ) + 1) * z ^ (j + 1)| ≤
      2 ^ (N + 1) * |z| ^ (N + 1) *
        (3 + |z| + (1 + z)⁻¹ + ∑ j ∈ Finset.range N, |z| ^ (j + 1)) := by
  have hy : 0 < 1 + z := by linarith
  have hS : 0 ≤ ∑ j ∈ Finset.range N, |z| ^ (j + 1) :=
    Finset.sum_nonneg fun j _ => by positivity
  have hyi : 0 ≤ (1 + z)⁻¹ := by positivity
  have hza := abs_nonneg z
  rcases le_or_gt |z| (1 / 2) with h | h
  · have hlt : |-z| < 1 := by rw [abs_neg]; linarith
    have key := Real.abs_log_sub_add_sum_range_le hlt N
    have e2 : ∑ i ∈ Finset.range N, (-z) ^ (i + 1) / ((i : ℝ) + 1) =
        -∑ j ∈ Finset.range N, (-1) ^ (j + 2) / ((j : ℝ) + 1) * z ^ (j + 1) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [neg_pow, pow_succ (-1 : ℝ) (i + 1)]
      ring
    rw [e2, sub_neg_eq_add, abs_neg] at key
    rw [show Real.log (1 + z) - ∑ j ∈ Finset.range N, (-1) ^ (j + 2) / ((j : ℝ) + 1) *
      z ^ (j + 1) = -∑ j ∈ Finset.range N, (-1) ^ (j + 2) / ((j : ℝ) + 1) * z ^ (j + 1) +
        Real.log (1 + z) by ring]
    refine key.trans ?_
    have hp := pow_nonneg hza (N + 1)
    have h1 : |z| ^ (N + 1) / (1 - |z|) ≤ 2 * |z| ^ (N + 1) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have h2 : (2 : ℝ) ≤ 2 ^ (N + 1) * 3 := by
      have := one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := N + 1)
      linarith
    have h3 : 3 ≤ 3 + |z| + (1 + z)⁻¹ + ∑ j ∈ Finset.range N, |z| ^ (j + 1) := by linarith
    calc |z| ^ (N + 1) / (1 - |z|) ≤ 2 * |z| ^ (N + 1) := h1
      _ ≤ 2 ^ (N + 1) * |z| ^ (N + 1) * 3 := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
  · have hlog : |Real.log (1 + z)| ≤ 1 + |z| + (1 + z)⁻¹ := by
      rw [abs_le]
      constructor
      · have := Real.log_le_sub_one_of_pos (inv_pos.mpr hy)
        rw [Real.log_inv] at this
        linarith
      · have := Real.log_le_sub_one_of_pos hy
        have := le_abs_self z
        linarith
    have hL : |∑ j ∈ Finset.range N, (-1) ^ (j + 2) / ((j : ℝ) + 1) * z ^ (j + 1)| ≤
        ∑ j ∈ Finset.range N, |z| ^ (j + 1) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_pow]
      have hj : (1 : ℝ) ≤ |(j : ℝ) + 1| := by
        rw [abs_of_pos (by positivity)]
        linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      calc 1 / |(j : ℝ) + 1| * |z| ^ (j + 1) ≤ 1 * |z| ^ (j + 1) :=
            mul_le_mul_of_nonneg_right (div_le_one_of_le₀ hj (abs_nonneg _)) (by positivity)
        _ = |z| ^ (j + 1) := one_mul _
    have hone : (1 : ℝ) ≤ 2 ^ (N + 1) * |z| ^ (N + 1) := by
      rw [← mul_pow]
      exact one_le_pow₀ (by linarith)
    calc _ ≤ |Real.log (1 + z)| + |∑ j ∈ Finset.range N, (-1) ^ (j + 2) / ((j : ℝ) + 1) *
          z ^ (j + 1)| := abs_sub _ _
      _ ≤ 3 + |z| + (1 + z)⁻¹ + ∑ j ∈ Finset.range N, |z| ^ (j + 1) := by linarith
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hone

/-- The expansion `logSeries (ySeries − 1)` of `log Y`. -/
private theorem good_log {E₀ : ℝ} (hE₀ : E₀ < 2) :
    Good (R := fun _ => ℂ) (sScl hE₀)
      (fun c => ((Real.log (1 + (‖stepVec c.g c.E c.X c.V‖ ^ 2 - 1)) : ℝ) : ℂ))
      (fun c n => cfgEval c.g c.X c.V (PowerSeries.coeff n (logSeries (ySeries - 1)))) := by
  have hx := stepSeries_constantCoeff_x
  have hZ := good_Z hE₀
  have hT : ∀ M, Good (R := fun _ => ℂ) (sScl hE₀)
      (fun c => ∑ j ∈ Finset.range M, logCoeff j • (yVal c - 1) ^ (j + 1))
      (fun c n => cfgEval c.g c.X c.V (PowerSeries.coeff n (logTrunc (ySeries - 1) M))) :=
    fun M => (Good.sum (Finset.range M) fun j _ =>
      (hZ.powC (S := fun _ => ySeries - 1) j).smul (fun _ => logCoeff j)
        fun _ _ => stepSeries_norm_logCoeff j).congr (fun _ _ => rfl) fun c _ n => by
      rw [logTrunc, map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [PowerSeries.coeff_smul, map_smul]
  have hZ1 : PBt (sScl hE₀) 1 fun c => ‖yVal c - 1‖ := (hZ.2 0).le fun c _ => by
    rw [psum, Finset.sum_range_one, PowerSeries.coeff_zero_eq_constantCoeff_apply, hx, map_zero,
      smul_zero, sub_zero]
  have hZ0 : ∀ k, PBt (sScl hE₀) 0 fun c => ‖yVal c - 1‖ ^ k := fun k => by
    simpa only [zero_mul] using (hZ1.lower (Nat.zero_le 1)).pow (fun _ _ => norm_nonneg _) k
  have hreal : ∀ c ∈ (sScl hE₀).P, yVal c - 1 =
      (((‖stepVec c.g c.E c.X c.V‖ ^ 2 - 1 : ℝ)) : ℂ) := fun c _ => by
    rw [stepSeries_yVal]; push_cast; ring
  refine ⟨fun n => ((hT n).1 n).le fun c _ => by
    dsimp only; rw [stepSeries_coeff_logSeries hx le_rfl],
    fun N => ?_⟩
  have hB : PBt (sScl hE₀) (N + 1) fun c => 2 ^ (N + 1) * ‖yVal c - 1‖ ^ (N + 1) *
      (3 + ‖yVal c - 1‖ + ‖(yVal c)⁻¹‖ + ∑ j ∈ Finset.range N, ‖yVal c - 1‖ ^ (j + 1)) := by
    have h1 := ((PBt.const (σ := sScl hE₀) (show (0 : ℝ) ≤ 2 ^ (N + 1) by positivity)).mul
      (hZ1.pow (fun _ _ => norm_nonneg _) (N + 1)) (fun _ _ => by positivity))
    have h2 := (((PBt.const (σ := sScl hE₀) (show (0 : ℝ) ≤ 3 by norm_num)).add
      (hZ0 1 |>.le fun _ _ => by rw [pow_one])).add (good_yInv hE₀).norm).add
      (PBt.sum (Finset.range N) fun j _ => hZ0 (j + 1))
    have := h1.mul h2 (fun _ _ => by positivity)
    simpa only [zero_add, one_mul, add_zero] using this
  refine ((hB.add ((hT N).2 N)).le fun c hc => ?_)
  have hpsum : psum (R := fun _ => ℂ) (sScl hE₀)
      (fun c n => cfgEval c.g c.X c.V (PowerSeries.coeff n (logSeries (ySeries - 1)))) N c =
      psum (R := fun _ => ℂ) (sScl hE₀)
        (fun c n => cfgEval c.g c.X c.V (PowerSeries.coeff n (logTrunc (ySeries - 1) N))) N c :=
    Finset.sum_congr rfl fun n hn => by
      dsimp only
      rw [stepSeries_coeff_logSeries hx (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))]
  rw [hpsum]
  refine (norm_sub_le_norm_sub_add_norm_sub _
    (∑ j ∈ Finset.range N, logCoeff j • (yVal c - 1) ^ (j + 1)) _).trans (add_le_add ?_ le_rfl)
  have hw := (stepSeries_norm_w hc).1
  set z := ‖stepVec c.g c.E c.X c.V‖ ^ 2 - 1 with hzdef
  have hz : -1 < z := by rw [hzdef]; nlinarith [pow_pos hw 2]
  have hL : ∑ j ∈ Finset.range N, logCoeff j • (yVal c - 1) ^ (j + 1) =
      ((∑ j ∈ Finset.range N, (-1) ^ (j + 2) / ((j : ℝ) + 1) * z ^ (j + 1) : ℝ) : ℂ) := by
    rw [hreal c hc, ← hzdef]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [logCoeff, smul_eq_mul]
    push_cast
    ring
  have hzn : ‖yVal c - 1‖ = |z| := by
    rw [hreal c hc, ← hzdef, Complex.norm_real, Real.norm_eq_abs]
  have hyn : ‖(yVal c)⁻¹‖ = (1 + z)⁻¹ := by
    rw [stepSeries_yVal, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity), hzdef]
    ring_nf
  rw [hL, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hzn, hyn]
  exact stepSeries_log_rem hz N

/-- The expansion `incSeries` of `c = −log ‖F^{−*}v‖` (11.7) [lg:eq:update]. -/
private theorem good_inc {E₀ : ℝ} (hE₀ : E₀ < 2) :
    Good (R := fun _ => ℂ) (sScl hE₀) (fun c => ((stepInc c.g c.E c.X c.V : ℝ) : ℂ))
      (fun c n => cfgEval c.g c.X c.V (PowerSeries.coeff n incSeries)) := by
  refine ((good_log hE₀).smul (fun _ => -(1 / 2 : ℂ)) fun _ _ => by norm_num).congr
    (fun c _ => ?_) (fun c _ n => ?_)
  · rw [smul_eq_mul, stepInc, add_sub_cancel, Real.log_pow]
    push_cast
    ring
  · rw [incSeries, PowerSeries.coeff_smul, map_smul]

/-- One step of a polynomial in the observables, expanded to order `N` in `t = h_θ/g`, with an
exact remainder valid for every Hermitian block (no cutoff): `p(X′) = Σ_{n≤N} t^n (ρ_θ p)_n(X, V) +
O(t^{N+1}(1 + ‖V‖)^r)`, uniformly in `W ≥ 1`, `g ≥ 1`, `|E| ≤ E₀` and the state. -/
theorem norm_obsEval_stepState_sub_le {E₀ : ℝ} (hE₀ : E₀ < 2) (p : ObsPoly) (N : ℕ) :
    ∃ K : ℝ, ∃ r : ℕ, 0 < K ∧ ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ E₀ →
      ∀ X : State W, IsState X → ∀ V : Matrix (Fin W) (Fin W) ℂ, V.IsHermitian →
        ‖obsEval g (stepState g E X V) p - ∑ n ∈ Finset.range (N + 1),
            (((normalH E / g) ^ n : ℝ) : ℂ) *
              cfgEval g X V (PowerSeries.coeff n (stepSeries (rotPoly E p)))‖ ≤
          K * (normalH E / g) ^ (N + 1) * (1 + ‖V‖) ^ r := by
  obtain ⟨K, r, hK, h⟩ := (good_poly hE₀ p).2 N
  refine ⟨max K 1, r, lt_of_lt_of_le one_pos (le_max_right _ _),
    fun W hW g hg E hE X hX V hV => ?_⟩
  have hc : (⟨W, g, E, X, V⟩ : SCtx) ∈ sAdm E₀ := ⟨hW, hg, hE, hX, hV⟩
  have h1 := h _ hc
  beta_reduce at h1
  rw [psum_complex] at h1
  refine h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (pow_nonneg ((sScl hE₀).t_nonneg _ hc) _)) ((sScl hE₀).s_pow_nonneg hc r))

/-- The increment `c` of (11.7) [lg:eq:update] expanded to order `N` in `t = h_θ/g`, with an
exact remainder valid for every Hermitian block. -/
theorem norm_stepInc_sub_le {E₀ : ℝ} (hE₀ : E₀ < 2) (N : ℕ) :
    ∃ K : ℝ, ∃ r : ℕ, 0 < K ∧ ∀ W : ℕ, 1 ≤ W → ∀ g : ℝ, 1 ≤ g → ∀ E : ℝ, |E| ≤ E₀ →
      ∀ X : State W, IsState X → ∀ V : Matrix (Fin W) (Fin W) ℂ, V.IsHermitian →
        ‖((stepInc g E X V : ℝ) : ℂ) - ∑ n ∈ Finset.range (N + 1),
            (((normalH E / g) ^ n : ℝ) : ℂ) * cfgEval g X V (PowerSeries.coeff n incSeries)‖ ≤
          K * (normalH E / g) ^ (N + 1) * (1 + ‖V‖) ^ r := by
  obtain ⟨K, r, hK, h⟩ := (good_inc hE₀).2 N
  refine ⟨max K 1, r, lt_of_lt_of_le one_pos (le_max_right _ _),
    fun W hW g hg E hE X hX V hV => ?_⟩
  have hc : (⟨W, g, E, X, V⟩ : SCtx) ∈ sAdm E₀ := ⟨hW, hg, hE, hX, hV⟩
  have h1 := h _ hc
  beta_reduce at h1
  rw [psum_complex] at h1
  refine h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (pow_nonneg ((sScl hE₀).t_nonneg _ hc) _)) ((sScl hE₀).s_pow_nonneg hc r))

end LSBA
