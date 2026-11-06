import LSBA.Gauss.GUEMat

/-!
# Splitting a GUE matrix along a row

Functions that ignore row and column `j`, and Tonelli for the coordinates of column `j` against the
rest: the column entries are independent complex Gaussians of variance `1/n`.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

noncomputable section
open scoped Classical

namespace LSBA

/-- `A` does not depend on the coordinates of row and column `j` of the GUE matrix
(1.2) [eq:covariance]. -/
def OffRow (n : ℕ) (j : Fin n) {α : Type*} (A : Ω n 1 → α) : Prop :=
  ∀ ω ω' : Ω n 1, (∀ x : Fin 1 × Fin n × Fin n, x.2.1 ≠ j → x.2.2 ≠ j → ω x = ω' x) →
    A ω = A ω'

/-- A sign change `y ↦ ±y` leaves the standard Gaussian measure of a measurable set unchanged. -/
private theorem rowSplit_gaussian_sign (s : ℝ) (hs : s = 1 ∨ s = -1) {t : Set ℝ}
    (ht : MeasurableSet t) :
    gaussianReal 0 1 ((fun y : ℝ => s * y) ⁻¹' t) = gaussianReal 0 1 t := by
  rcases hs with rfl | rfl
  · simp
  · have h := gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1)
    have h2 : ((fun y : ℝ => (-1 : ℝ) * y) ⁻¹' t) = Neg.neg ⁻¹' t := by
      ext y; simp
    rw [h2, ← Measure.map_apply measurable_neg ht, h]
    simp

/-- Overwriting the coordinates `σ l` of a standard Gaussian vector on `ι` by the signed
coordinates `s l * x l` of an independent standard Gaussian vector on `ι'` preserves the product
measure. -/
private theorem rowSplit_map_extend {ι' ι : Type*} [Fintype ι'] [Fintype ι] (σ : ι' → ι)
    (hσ : Function.Injective σ) (s : ι' → ℝ) (hs : ∀ l, s l = 1 ∨ s l = -1) :
    MeasurePreserving
      (fun p : (ι' → ℝ) × (ι → ℝ) => Function.extend σ (fun l => s l * p.1 l) p.2)
      ((Measure.pi fun _ : ι' => gaussianReal 0 1).prod (Measure.pi fun _ : ι => gaussianReal 0 1))
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hmeas : Measurable
      (fun p : (ι' → ℝ) × (ι → ℝ) => Function.extend σ (fun l => s l * p.1 l) p.2) := by
    refine measurable_pi_iff.mpr fun i => ?_
    by_cases h : ∃ l, σ l = i
    · obtain ⟨l, rfl⟩ := h
      simp only [hσ.extend_apply]
      exact measurable_const.mul ((measurable_pi_apply l).comp measurable_fst)
    · simp only [Function.extend_apply' _ _ _ h]
      exact (measurable_pi_apply i).comp measurable_snd
  refine ⟨hmeas, ?_⟩
  symm
  refine Measure.pi_eq fun t ht => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi ht)]
  have hpre : (fun p : (ι' → ℝ) × (ι → ℝ) => Function.extend σ (fun l => s l * p.1 l) p.2) ⁻¹'
      (Set.univ.pi t) =
      (Set.univ.pi fun l => (fun y : ℝ => s l * y) ⁻¹' t (σ l)) ×ˢ
        (Set.univ.pi fun i => if i ∈ Set.range σ then Set.univ else t i) := by
    ext ⟨x, ω⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun l => ?_, fun i => ?_⟩
      · simpa [hσ.extend_apply] using h (σ l)
      · by_cases hi : i ∈ Set.range σ
        · simp [hi]
        · have hi' : ¬ ∃ l, σ l = i := hi
          simpa [hi, Function.extend_apply' _ _ _ hi'] using h i
    · rintro ⟨h1, h2⟩ i
      by_cases hi : ∃ l, σ l = i
      · obtain ⟨l, rfl⟩ := hi
        simpa [hσ.extend_apply] using h1 l
      · have hi' : i ∉ Set.range σ := hi
        simpa [hi', Function.extend_apply' _ _ _ hi] using h2 i
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi]
  have h1 : ∏ i, (gaussianReal 0 1) ((fun y => s i * y) ⁻¹' t (σ i)) =
      ∏ i ∈ Finset.univ.image σ, gaussianReal 0 1 (t i) := by
    rw [Finset.prod_image fun a _ b _ h => hσ h]
    exact Finset.prod_congr rfl fun l _ => rowSplit_gaussian_sign (s l) (hs l) (ht (σ l))
  have h2 : ∏ i, (gaussianReal 0 1) (if i ∈ Set.range σ then Set.univ else t i) =
      ∏ i ∈ (Finset.univ.image σ)ᶜ, gaussianReal 0 1 (t i) := by
    rw [← Finset.prod_mul_prod_compl (Finset.univ.image σ)]
    rw [Finset.prod_eq_one fun i hi => by
      have : i ∈ Set.range σ := by simpa using hi
      simp [this], one_mul]
    refine Finset.prod_congr rfl fun i hi => ?_
    have : i ∉ Set.range σ := by simpa using hi
    simp [this]
  rw [h1, h2, Finset.prod_mul_prod_compl]

/-- The coordinate of the sample carrying the real part (`l.2 = 0`) or, up to the sign
`rowSplit_sign`, the imaginary part (`l.2 = 1`) of `√(2n) V_{e l.1, j}`, (1.2) [eq:covariance]. -/
private def rowSplit_pos (n : ℕ) (j : Fin n) {κ : Type*} (e : κ → Fin n) (l : κ × Fin 2) :
    Fin 1 × Fin n × Fin n :=
  if (l.2 = 0 ↔ e l.1 < j) then (0, e l.1, j) else (0, j, e l.1)

/-- The sign relating the coordinate `rowSplit_pos l` to the real or imaginary part of
`√(2n) V_{e l.1, j}`: `-1` if `l.2 = 1` and `j < e l.1`, and `+1` otherwise. -/
private def rowSplit_sign (n : ℕ) (j : Fin n) {κ : Type*} (e : κ → Fin n) (l : κ × Fin 2) : ℝ :=
  if l.2 = 1 ∧ j < e l.1 then -1 else 1

/-- The coordinates `rowSplit_pos` of distinct pairs are distinct. -/
private theorem rowSplit_pos_injective (n : ℕ) (j : Fin n) {κ : Type*} (e : κ → Fin n)
    (he : Function.Injective e) (hej : ∀ k, e k ≠ j) :
    Function.Injective (rowSplit_pos n j e) := by
  rintro ⟨k, b⟩ ⟨k', b'⟩ h
  simp only [rowSplit_pos] at h
  have hb : ∀ b : Fin 2, b = 0 ∨ b = 1 := by decide
  rcases hb b with rfl | rfl <;> rcases hb b' with rfl | rfl <;>
    by_cases h1 : e k < j <;> by_cases h2 : e k' < j <;>
    simp [h1, h2, Prod.ext_iff] at h <;> simp_all [he.eq_iff]

/-- Overwriting the coordinates `rowSplit_pos` by the signed vector `x` turns the entries
`V_{e k, j}` into `(2n)^{-1/2}(x_{k0} + i x_{k1})`, (1.2) [eq:covariance]. -/
private theorem rowSplit_entry (n : ℕ) (j : Fin n) {κ : Type*} (e : κ → Fin n)
    (he : Function.Injective e) (hej : ∀ k, e k ≠ j) (x : κ × Fin 2 → ℝ) (ω : Ω n 1) (k : κ) :
    gueMat n (Function.extend (rowSplit_pos n j e)
        (fun l => rowSplit_sign n j e l * x l) ω) (e k) j =
      ((Real.sqrt (2 * n))⁻¹ : ℝ) * (⟨x (k, 0), x (k, 1)⟩ : ℂ) := by
  have hinj := rowSplit_pos_injective n j e he hej
  have hne : e k ≠ j := hej k
  simp only [gueMat, gueBlock, Matrix.of_apply, hne, ↓reduceIte]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h0 : rowSplit_pos n j e (k, 0) = (0, e k, j) := by simp [rowSplit_pos, hlt]
    have h1 : rowSplit_pos n j e (k, 1) = (0, j, e k) := by simp [rowSplit_pos, hlt]
    have hnj : ¬ j < e k := lt_asymm hlt
    simp only [hlt, ↓reduceIte]
    rw [← h0, ← h1, hinj.extend_apply, hinj.extend_apply]
    simp [rowSplit_sign, hnj, Complex.mk_eq_add_mul_I, div_eq_inv_mul, mul_comm]
  · have hlt : ¬ e k < j := not_lt.mpr hgt.le
    have h0 : rowSplit_pos n j e (k, 0) = (0, j, e k) := by simp [rowSplit_pos, hlt]
    have h1 : rowSplit_pos n j e (k, 1) = (0, e k, j) := by simp [rowSplit_pos, hlt]
    simp only [hlt, ↓reduceIte]
    rw [← h0, ← h1, hinj.extend_apply, hinj.extend_apply]
    simp [rowSplit_sign, hgt, Complex.mk_eq_add_mul_I, div_eq_inv_mul, mul_comm]

/-- The sign `rowSplit_sign` is `1` or `-1`. -/
private theorem rowSplit_sign_cases (n : ℕ) (j : Fin n) {κ : Type*} (e : κ → Fin n)
    (l : κ × Fin 2) : rowSplit_sign n j e l = 1 ∨ rowSplit_sign n j e l = -1 := by
  unfold rowSplit_sign
  split_ifs <;> simp

/-- The coordinates `rowSplit_pos` all lie in row `j` or column `j`. -/
private theorem rowSplit_pos_mem (n : ℕ) (j : Fin n) {κ : Type*} (e : κ → Fin n)
    (l : κ × Fin 2) : (rowSplit_pos n j e l).2.1 = j ∨ (rowSplit_pos n j e l).2.2 = j := by
  unfold rowSplit_pos
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The entries of the GUE matrix are measurable in the sample. -/
private theorem rowSplit_measurable_entry (n : ℕ) (a b : Fin n) :
    Measurable fun ω : Ω n 1 => gueMat n ω a b := by
  unfold gueMat gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

/-- Row split of the GUE measure, Appendix G.1 [app:relative-local-law-proof]: entries
`V_{e k, j}` of column `j` off the diagonal are independent of every function of the other
coordinates and form a complex Gaussian vector with `E|V_{e k, j}|² = 1/n`. -/
theorem lintegral_col_offRow {α : Type*} [MeasurableSpace α] (n : ℕ) (j : Fin n)
    {κ : Type*} [Fintype κ] (e : κ → Fin n) (he : Function.Injective e) (hej : ∀ k, e k ≠ j)
    {A : Ω n 1 → α} (hA : Measurable A) (hoff : OffRow n j A)
    {Φ : (κ → ℂ) × α → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ ω, Φ (fun k => gueMat n ω (e k) j, A ω) ∂(μ n 1) =
      ∫⁻ ω, ∫⁻ x, Φ (fun k => ((Real.sqrt (2 * n))⁻¹ : ℝ) * (⟨x (k, 0), x (k, 1)⟩ : ℂ), A ω)
        ∂(stdGauss (κ × Fin 2)) ∂(μ n 1) := by
  have hinj := rowSplit_pos_injective n j e he hej
  have hmp : MeasurePreserving
      (fun p : (κ × Fin 2 → ℝ) × Ω n 1 => Function.extend (rowSplit_pos n j e)
        (fun l => rowSplit_sign n j e l * p.1 l) p.2)
      ((stdGauss (κ × Fin 2)).prod (μ n 1)) (μ n 1) :=
    rowSplit_map_extend (rowSplit_pos n j e) hinj (rowSplit_sign n j e)
      (rowSplit_sign_cases n j e)
  have hcol : Measurable fun ω : Ω n 1 => (fun k => gueMat n ω (e k) j) :=
    measurable_pi_iff.mpr fun k => rowSplit_measurable_entry n (e k) j
  have hF : Measurable fun ω : Ω n 1 => Φ (fun k => gueMat n ω (e k) j, A ω) :=
    hΦ.comp (hcol.prodMk hA)
  have hFG : AEMeasurable (fun p : (κ × Fin 2 → ℝ) × Ω n 1 =>
      Φ (fun k => gueMat n (Function.extend (rowSplit_pos n j e)
        (fun l => rowSplit_sign n j e l * p.1 l) p.2) (e k) j,
        A (Function.extend (rowSplit_pos n j e) (fun l => rowSplit_sign n j e l * p.1 l) p.2)))
      ((stdGauss (κ × Fin 2)).prod (μ n 1)) :=
    (hF.comp hmp.measurable).aemeasurable
  rw [← hmp.lintegral_comp hF, lintegral_prod_symm _ hFG]
  refine lintegral_congr fun ω => lintegral_congr fun x => ?_
  have hA' : A (Function.extend (rowSplit_pos n j e)
      (fun l => rowSplit_sign n j e l * x l) ω) = A ω := by
    refine hoff _ _ fun i h1 h2 => ?_
    have hi : ¬ ∃ l, rowSplit_pos n j e l = i := by
      rintro ⟨l, rfl⟩
      rcases rowSplit_pos_mem n j e l with h | h
      · exact h1 h
      · exact h2 h
    exact Function.extend_apply' _ _ _ hi
  simp only [hA', rowSplit_entry n j e he hej x ω]

end LSBA
