import LSBA.Transfer.Circle

/-!
# The angular measure on the circle

The normalized angular measure `dm_U = dθ/2π` on the circle 𝒞_U as a probability measure on flags,
its independence of the circle basis, and measurability of `θ ↦ Y_θ` (before (8.36) [cc:eq:jac]).
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

/-- The point `Y_θ` of the circle `𝒞_U` through the base `U` of `x`, for the fixed choice of
`(e, f)`. -/
def circleFlag {W : ℕ} (x : IsoFlag W) (θ : ℝ) : IsoFlag W :=
  if h : circlePair x.1.1 (circleBasis x.1.1).1 (circleBasis x.1.1).2 θ ∈ isoFlags W then
    ⟨_, h⟩ else x

/-- The normalized angle measure `dθ/2π` on `(0, 2π]`. -/
def angleMeas : Measure ℝ :=
  (ENNReal.ofReal (2 * π))⁻¹ • volume.restrict (Set.Ioc 0 (2 * π))

/-- The normalized angular measure `m_U` on the circle `𝒞_U` through the base of `x`
(Section 8.3 [sec:upper-inputs], (F.1) [cc:eq:circle]). -/
def circleMeasure {W : ℕ} (x : IsoFlag W) : Measure (IsoFlag W) :=
  Measure.map (circleFlag x) angleMeas

/-- `sup_U ‖h(U, ·)‖_{L⁴(𝒞_U, m_U)} ≤ M`, the angular `L⁴` norm of Section 8.3
[sec:upper-inputs]. -/
def AngL4Le {W : ℕ} (h : IsoFlag W → ℝ) (M : ℝ) : Prop :=
  ∀ x : IsoFlag W, ∫⁻ y, ‖h y‖ₑ ^ 4 ∂(circleMeasure x) ≤ ENNReal.ofReal M ^ 4

/-! ### Helpers -/

/-- `θ ↦ (P, P + v_θ v_θ*)` is continuous. -/
private theorem circleMeasure_continuous {W : ℕ} (P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (e f : Fin 2 × Fin W → ℂ) : Continuous (circlePair P e f) := by
  unfold circlePair circleVec
  refine continuous_const.prodMk (continuous_const.add ?_)
  refine Continuous.matrix_vecMulVec ?_ ?_
  · fun_prop
  · fun_prop

/-- For a circle basis `(e, f)` of the base of `x`, `θ ↦ Y_θ` is measurable. -/
private theorem circleMeasure_measurable_G {W : ℕ} (x : IsoFlag W) {e f : Fin 2 × Fin W → ℂ}
    (hef : IsCircleBasis x.1.1 e f) :
    Measurable (fun θ : ℝ =>
      (⟨circlePair x.1.1 e f θ, circlePair_mem_isoFlags x.2.1 hef θ⟩ : IsoFlag W)) :=
  Measurable.subtype_mk (circleMeasure_continuous _ e f).measurable

/-- `θ ↦ Y_θ` is `2π`-periodic. -/
private theorem circleMeasure_periodic {W : ℕ} (P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (e f : Fin 2 × Fin W → ℂ) (θ : ℝ) : circlePair P e f (θ + 2 * π) = circlePair P e f θ := by
  have h : Complex.exp (((θ + 2 * π : ℝ) : ℂ) * Complex.I) = Complex.exp ((θ : ℂ) * Complex.I) := by
    have : ((θ + 2 * π : ℝ) : ℂ) * Complex.I = (θ : ℂ) * Complex.I + 2 * π * Complex.I := by
      push_cast; ring
    rw [this]
    exact Complex.exp_periodic _
  unfold circlePair circleVec
  rw [h]

/-- The fixed choice `circleBasis` is a circle basis when one exists. -/
private theorem circleMeasure_basis_spec {W : ℕ}
    {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {e f : Fin 2 × Fin W → ℂ}
    (hef : IsCircleBasis P e f) :
    IsCircleBasis P (circleBasis P).1 (circleBasis P).2 := by
  have h : ∃ ef : (Fin 2 × Fin W → ℂ) × (Fin 2 × Fin W → ℂ), IsCircleBasis P ef.1 ef.2 :=
    ⟨(e, f), hef⟩
  unfold circleBasis
  rw [dite_eq_left h]
  exact h.choose_spec

/-- When a circle basis exists, `circleFlag x` is the map `θ ↦ Y_θ` of the fixed choice. -/
private theorem circleMeasure_circleFlag_eq {W : ℕ} (x : IsoFlag W) {e f : Fin 2 × Fin W → ℂ}
    (hef : IsCircleBasis x.1.1 e f) :
    circleFlag x = fun θ => (⟨circlePair x.1.1 (circleBasis x.1.1).1 (circleBasis x.1.1).2 θ,
      circlePair_mem_isoFlags x.2.1 (circleMeasure_basis_spec hef) θ⟩ : IsoFlag W) := by
  funext θ
  exact dite_eq_left _

/-- `θ ↦ Y_θ` is constant if there is no circle basis. -/
private theorem circleMeasure_circleFlag_const {W : ℕ} (x : IsoFlag W)
    (h : ¬ ∃ ef : (Fin 2 × Fin W → ℂ) × (Fin 2 × Fin W → ℂ), IsCircleBasis x.1.1 ef.1 ef.2) :
    ∀ θ, circleFlag x θ = circleFlag x 0 := by
  have hc : circleBasis x.1.1 = 0 := by
    unfold circleBasis
    rw [dite_eq_right h]
  have key : ∀ θ, circlePair x.1.1 (0 : Fin 2 × Fin W → ℂ) 0 θ = (x.1.1, x.1.1) := by
    intro θ
    simp [circlePair, circleVec]
  intro θ
  unfold circleFlag
  simp only [hc, Prod.fst_zero, Prod.snd_zero, key]

open scoped ComplexOrder in
/-- Two Hermitian idempotents `B`, `B'` with `B B' = B'` and equal traces coincide. -/
private theorem circleMeasure_eq_of_trace {ι : Type*} [Fintype ι] {B B' : Matrix ι ι ℂ}
    (hB : Bᴴ = B) (hBB : B * B = B) (hB' : B'ᴴ = B') (hB'B' : B' * B' = B')
    (hmul : B * B' = B') (htr : B.trace = B'.trace) : B = B' := by
  have hmul' : B' * B = B' := by
    have := congrArg Matrix.conjTranspose hmul
    rwa [Matrix.conjTranspose_mul, hB, hB'] at this
  have hD : (B - B')ᴴ = B - B' := by rw [Matrix.conjTranspose_sub, hB, hB']
  have hDD : (B - B') * (B - B') = B - B' := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, hBB, hmul, hmul', hB'B']
    abel
  have htr0 : ((B - B')ᴴ * (B - B')).trace = 0 := by
    rw [hD, hDD, Matrix.trace_sub, htr, sub_self]
  exact sub_eq_zero.mp (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htr0)

/-- `J` is Hermitian: `v* (J u) = (J v)* u`. -/
private theorem circleMeasure_star_J {W : ℕ} (v u : Fin 2 × Fin W → ℂ) :
    star v ⬝ᵥ (isoJ W *ᵥ u) = star (isoJ W *ᵥ v) ⬝ᵥ u := by
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, isoJ_conjTranspose]

/-- `f* u = 0` for a circle basis `(e, f)` and a vector `u` with `J u = u`. -/
private theorem circleMeasure_star_f {W : ℕ} {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {e f : Fin 2 × Fin W → ℂ} (hef : IsCircleBasis P e f) {u : Fin 2 × Fin W → ℂ}
    (hu : isoJ W *ᵥ u = u) : star f ⬝ᵥ u = 0 := by
  obtain ⟨-, -, -, hfJ, -, -⟩ := hef
  have h := circleMeasure_star_J f u
  rw [hu, hfJ, star_neg, neg_dotProduct] at h
  have h2 : (2 : ℂ) * (star f ⬝ᵥ u) = 0 := by linear_combination h
  simpa using h2

/-- `e* u = 0` for a circle basis `(e, f)` and a vector `u` with `J u = -u`. -/
private theorem circleMeasure_star_e {W : ℕ} {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {e f : Fin 2 × Fin W → ℂ} (hef : IsCircleBasis P e f) {u : Fin 2 × Fin W → ℂ}
    (hu : isoJ W *ᵥ u = -u) : star e ⬝ᵥ u = 0 := by
  obtain ⟨-, -, heJ, -, -, -⟩ := hef
  have h := circleMeasure_star_J e u
  rw [hu, heJ, dotProduct_neg] at h
  have h2 : (2 : ℂ) * (star e ⬝ᵥ u) = 0 := by linear_combination -h
  simpa using h2

/-- `quotProj P` fixes `u` when `P u = 0` and `P J u = 0`. -/
private theorem circleMeasure_Q_mulVec {W : ℕ}
    {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {u : Fin 2 × Fin W → ℂ}
    (h1 : P *ᵥ u = 0) (h2 : P *ᵥ (isoJ W *ᵥ u) = 0) : quotProj P *ᵥ u = u := by
  unfold quotProj
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, h2, h1]
  simp

/-- `e* f = 0` for a circle basis. -/
private theorem circleMeasure_star_dot {W : ℕ} {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {e f : Fin 2 × Fin W → ℂ} (hef : IsCircleBasis P e f) : star e ⬝ᵥ f = 0 :=
  circleMeasure_star_e hef (u := f) hef.2.2.2.1

/-- `quotProj P = e e* + f f*` for a circle basis (Lemma F.1 [cc:lem:quotient]). -/
private theorem circleMeasure_quotProj_eq {W : ℕ}
    {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hP : P ∈ isoBases W)
    {e f : Fin 2 × Fin W → ℂ} (hef : IsCircleBasis P e f) :
    quotProj P = Matrix.vecMulVec e (star e) + Matrix.vecMulVec f (star f) := by
  have hW : 1 ≤ W := by
    by_contra h
    have hW : W = 0 := by omega
    subst hW
    have := hef.1
    simp [dotProduct] at this
  obtain ⟨hQh, hQQ, -, hQtr, -⟩ := quotProj_spec hW hP
  have hef0 := hef
  obtain ⟨-, -, heJ, hfJ, heP, hfP⟩ := hef
  have hQe : quotProj P *ᵥ e = e :=
    circleMeasure_Q_mulVec heP (by rw [heJ, heP])
  have hQf : quotProj P *ᵥ f = f :=
    circleMeasure_Q_mulVec hfP (by rw [hfJ, Matrix.mulVec_neg, hfP, neg_zero])
  have h0 := circleMeasure_star_dot hef0
  have h0' : star f ⬝ᵥ e = 0 := by
    have : star f ⬝ᵥ e = star (star e ⬝ᵥ f) := by
      rw [← Matrix.star_dotProduct_star, star_star]
    rw [this, h0, star_zero]
  obtain ⟨he, hf, -⟩ := hef0
  have hEE : Matrix.vecMulVec e (star e) * Matrix.vecMulVec e (star e) =
      Matrix.vecMulVec e (star e) := by
    rw [Matrix.vecMulVec_mul_vecMulVec, he, one_smul]
  have hEF : Matrix.vecMulVec e (star e) * Matrix.vecMulVec f (star f) = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, h0, zero_smul, Matrix.vecMulVec_zero]
  have hFE : Matrix.vecMulVec f (star f) * Matrix.vecMulVec e (star e) = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, h0', zero_smul, Matrix.vecMulVec_zero]
  have hFF : Matrix.vecMulVec f (star f) * Matrix.vecMulVec f (star f) =
      Matrix.vecMulVec f (star f) := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hf, one_smul]
  refine circleMeasure_eq_of_trace hQh hQQ ?_ ?_ ?_ ?_
  · rw [Matrix.conjTranspose_add, Matrix.conjTranspose_vecMulVec, Matrix.conjTranspose_vecMulVec,
      star_star, star_star]
  · simp only [Matrix.add_mul, Matrix.mul_add, hEE, hEF, hFE, hFF, zero_add, add_zero]
  · rw [Matrix.mul_add, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, hQe, hQf]
  · rw [Matrix.trace_add, Matrix.trace_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm e,
      dotProduct_comm f, he, hf, hQtr]
    norm_num

/-- A vector `u ∈ H_U` is `(e* u) e + (f* u) f`. -/
private theorem circleMeasure_expand {W : ℕ} {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hP : P ∈ isoBases W) {e f : Fin 2 × Fin W → ℂ} (hef : IsCircleBasis P e f)
    {u : Fin 2 × Fin W → ℂ} (h1 : P *ᵥ u = 0) (h2 : P *ᵥ (isoJ W *ᵥ u) = 0) :
    u = (star e ⬝ᵥ u) • e + (star f ⬝ᵥ u) • f := by
  have h := congrArg (fun M => M *ᵥ u) (circleMeasure_quotProj_eq hP hef)
  simp only [circleMeasure_Q_mulVec h1 h2, Matrix.add_mulVec, Matrix.vecMulVec_mulVec] at h
  simpa using h

/-- Two circle bases of the same base differ by a phase: `Y_θ(e', f') = Y_{θ+c}(e, f)`. -/
private theorem circleMeasure_shift_pair {W : ℕ}
    {P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hP : P ∈ isoBases W)
    {e f e' f' : Fin 2 × Fin W → ℂ} (hef : IsCircleBasis P e f) (hef' : IsCircleBasis P e' f') :
    ∃ c : ℝ, ∀ θ, circlePair P e' f' θ = circlePair P e f (θ + c) := by
  have hee := hef.1
  have hff := hef.2.1
  obtain ⟨he', hf', he'J, hf'J, he'P, hf'P⟩ := hef'
  have hJe' : P *ᵥ (isoJ W *ᵥ e') = 0 := by rw [he'J, he'P]
  have hJf' : P *ᵥ (isoJ W *ᵥ f') = 0 := by rw [hf'J, Matrix.mulVec_neg, hf'P, neg_zero]
  have hxe := circleMeasure_expand hP hef he'P hJe'
  have hxf := circleMeasure_expand hP hef hf'P hJf'
  rw [circleMeasure_star_f hef he'J, zero_smul, add_zero] at hxe
  rw [circleMeasure_star_e hef hf'J, zero_smul, zero_add] at hxf
  obtain ⟨a, ha⟩ : ∃ a : ℂ, e' = a • e := ⟨_, hxe⟩
  obtain ⟨b, hb⟩ : ∃ b : ℂ, f' = b • f := ⟨_, hxf⟩
  subst ha hb
  have ha1 : star a * a = 1 := by
    rw [mul_comm]
    simpa [star_smul, smul_dotProduct, dotProduct_smul, hee] using he'
  have hb1 : star b * b = 1 := by
    rw [mul_comm]
    simpa [star_smul, smul_dotProduct, dotProduct_smul, hff] using hf'
  have ha0 : a ≠ 0 := fun h => by rw [h, star_zero, zero_mul] at ha1; exact zero_ne_one ha1
  have hnorm : ∀ z : ℂ, star z * z = 1 → ‖z‖ = 1 := by
    intro z hz
    rw [Complex.star_def, Complex.conj_mul'] at hz
    have h : ‖z‖ ^ 2 = 1 := by exact_mod_cast hz
    nlinarith [norm_nonneg z]
  have hu1 : ‖b / a‖ = 1 := by rw [norm_div, hnorm a ha1, hnorm b hb1, div_one]
  obtain ⟨ζ, hexp, hbζ⟩ : ∃ ζ : ℂ, Complex.exp ((Complex.arg ζ : ℂ) * Complex.I) = ζ ∧
      b = a * ζ := by
    refine ⟨b / a, ?_, by field_simp⟩
    have := Complex.norm_mul_exp_arg_mul_I (b / a)
    rwa [hu1, Complex.ofReal_one, one_mul] at this
  subst hbζ
  refine ⟨Complex.arg ζ, fun θ => ?_⟩
  have hv : circleVec (a • e) ((a * ζ) • f) θ = a • circleVec e f (θ + Complex.arg ζ) := by
    unfold circleVec
    have : Complex.exp (((θ + Complex.arg ζ : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((θ : ℂ) * Complex.I) * ζ := by
      push_cast
      rw [add_mul, Complex.exp_add, hexp]
    rw [this]
    generalize (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = c
    generalize Complex.exp ((θ : ℂ) * Complex.I) = w
    simp only [smul_add, smul_smul]
    match_scalars <;> ring
  have hk : a * star a = 1 := by rw [mul_comm]; exact ha1
  unfold circlePair
  rw [hv, star_smul, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul, hk, one_smul]

/-- Shifting the angle by `c` does not change the pushforward of `angleMeas` by a measurable
`2π`-periodic map. -/
private theorem circleMeasure_map_shift {β : Type*} [MeasurableSpace β] {g : ℝ → β}
    (hg : Measurable g) (hper : ∀ θ, g (θ + 2 * π) = g θ) (c : ℝ) :
    Measure.map (fun θ => g (θ + c)) angleMeas = Measure.map g angleMeas := by
  have hT : (0 : ℝ) < 2 * π := by positivity
  have hgc : Measurable (fun θ => g (θ + c)) := hg.comp (measurable_add_const c)
  ext A hA
  rw [Measure.map_apply hgc hA, Measure.map_apply hg hA]
  set B : Set ℝ := g ⁻¹' A with hB
  have hBm : MeasurableSet B := hg hA
  have hBc : MeasurableSet ((fun θ => θ + c) ⁻¹' B) := measurable_add_const c hBm
  have hper' : Function.Periodic g (2 * π) := hper
  have hinv : ∀ k : AddSubgroup.zmultiples (2 * π), (fun x : ℝ => k +ᵥ x) ⁻¹' B = B := by
    intro k
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp k.2
    ext x
    simp only [Set.mem_preimage, hB, AddSubgroup.vadd_def, vadd_eq_add, ← hn]
    rw [add_comm, (hper'.zsmul n) x]
  have h1 := isAddFundamentalDomain_Ioc hT 0 volume
  have h2 := isAddFundamentalDomain_Ioc hT c volume
  rw [zero_add] at h1
  have hmain : volume (B ∩ Set.Ioc c (c + 2 * π)) = volume (B ∩ Set.Ioc 0 (2 * π)) :=
    h2.measure_set_eq h1 hBm hinv
  have hpre : (fun θ : ℝ => θ + c) ⁻¹' (B ∩ Set.Ioc c (c + 2 * π)) =
      (fun θ => g (θ + c)) ⁻¹' A ∩ Set.Ioc 0 (2 * π) := by
    ext θ
    simp [hB]
  have hshift : volume ((fun θ : ℝ => g (θ + c)) ⁻¹' A ∩ Set.Ioc 0 (2 * π)) =
      volume (B ∩ Set.Ioc c (c + 2 * π)) := by
    rw [← hpre]
    exact measure_preimage_add_right _ _ _
  unfold angleMeas
  rw [Measure.smul_apply, Measure.smul_apply, Measure.restrict_apply (hgc hA),
    Measure.restrict_apply hBm, hshift, hmain]

/-- `m_U` does not depend on the choice of `(e, f)` (Section 8.3 [sec:upper-inputs]). -/
theorem circleMeasure_eq_map {W : ℕ} (x : IsoFlag W) {e f : Fin 2 × Fin W → ℂ}
    (hef : IsCircleBasis x.1.1 e f) :
    circleMeasure x = Measure.map
      (fun θ => (⟨circlePair x.1.1 e f θ, circlePair_mem_isoFlags x.2.1 hef θ⟩ : IsoFlag W))
      angleMeas := by
  have h0 := circleMeasure_basis_spec hef
  obtain ⟨c, hc⟩ := circleMeasure_shift_pair x.2.1 hef h0
  have hflag : circleFlag x = fun θ =>
      (⟨circlePair x.1.1 e f (θ + c), circlePair_mem_isoFlags x.2.1 hef _⟩ : IsoFlag W) := by
    rw [circleMeasure_circleFlag_eq x hef]
    funext θ
    exact Subtype.ext (hc θ)
  unfold circleMeasure
  rw [hflag]
  exact circleMeasure_map_shift (g := fun θ =>
      (⟨circlePair x.1.1 e f θ, circlePair_mem_isoFlags x.2.1 hef θ⟩ : IsoFlag W))
    (circleMeasure_measurable_G x hef)
    (fun θ => Subtype.ext (circleMeasure_periodic _ e f θ)) c

/-- `θ ↦ Y_θ` is measurable. -/
theorem measurable_circleFlag {W : ℕ} (x : IsoFlag W) : Measurable (circleFlag x) := by
  by_cases h : ∃ ef : (Fin 2 × Fin W → ℂ) × (Fin 2 × Fin W → ℂ),
      IsCircleBasis x.1.1 ef.1 ef.2
  · obtain ⟨⟨e, f⟩, hef⟩ := h
    rw [circleMeasure_circleFlag_eq x hef]
    exact circleMeasure_measurable_G x (circleMeasure_basis_spec hef)
  · have : circleFlag x = fun _ => circleFlag x 0 := funext (circleMeasure_circleFlag_const x h)
    rw [this]
    exact measurable_const

/-- `m_U` is a probability measure. -/
theorem isProbabilityMeasure_circleMeasure {W : ℕ} (x : IsoFlag W) :
    IsProbabilityMeasure (circleMeasure x) := by
  have hT : (0 : ℝ) < 2 * π := by positivity
  have h : IsProbabilityMeasure angleMeas := by
    refine ⟨?_⟩
    unfold angleMeas
    rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_Ioc, sub_zero, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by simpa using hT) ENNReal.ofReal_ne_top
  exact (Measure.isProbabilityMeasure_map_iff (measurable_circleFlag x).aemeasurable).mpr h

end LSBA
