import LSBA.Sampling.Space
import LSBA.Sampling.Prefix
import LSBA.Primitive.Orbital
import LSBA.Transfer.Coarse
import LSBA.Kernel.Large

/-!
# Primitive loops near the common space

The primitive part of Lemma 7.5 [uvc:lem:space]: for the auxiliary model at every large width,
and in the limit (Lemma 5.4 [uvc:lem:orbital-limit]) for the primitive loops `F_k`, the distance
to the common space on a cell product is at most `C′(n/g²)^{1/2}(1 − t)^{-C′}`.
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ## Moment bounds -/

section Moments

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- `f ≥ 0` is measurable, `f^p` is integrable and `E f^p ≤ A^p`. -/
private def PrimMom (ν : Measure X) (p : ℕ) (f : X → ℝ) (A : ℝ) : Prop :=
  AEStronglyMeasurable f ν ∧ (∀ x, 0 ≤ f x) ∧ Integrable (fun x => f x ^ p) ν ∧
    ∫ x, f x ^ p ∂ν ≤ A ^ p

private theorem primMom_const [IsProbabilityMeasure ν] {c : ℝ} (hc : 0 ≤ c) (p : ℕ) :
    PrimMom ν p (fun _ => c) c :=
  ⟨aestronglyMeasurable_const, fun _ => hc, integrable_const _, by simp⟩

private theorem primMom_mono {p : ℕ} {f : X → ℝ} {A A' : ℝ} (hA : 0 ≤ A) (hAA : A ≤ A')
    (hf : PrimMom ν p f A) : PrimMom ν p f A' :=
  ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.trans (pow_le_pow_left₀ hA hAA p)⟩

private theorem primMom_smul {p : ℕ} {f : X → ℝ} {A c : ℝ} (hc : 0 ≤ c)
    (hf : PrimMom ν p f A) : PrimMom ν p (fun x => c * f x) (c * A) := by
  have he : (fun x => (c * f x) ^ p) = fun x => c ^ p * f x ^ p := by
    funext x; rw [mul_pow]
  refine ⟨hf.1.const_mul c, fun x => mul_nonneg hc (hf.2.1 x), ?_, ?_⟩
  · rw [he]; exact hf.2.2.1.const_mul _
  · rw [he, integral_const_mul, mul_pow]
    exact mul_le_mul_of_nonneg_left hf.2.2.2 (pow_nonneg hc p)

private theorem primMom_add {p : ℕ} (hp : 1 ≤ p) {f g : X → ℝ} {A B : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hf : PrimMom ν p f A) (hg : PrimMom ν p g B) :
    PrimMom ν p (fun x => f x + g x) (2 * (A + B)) := by
  have hpt : ∀ x, (f x + g x) ^ p ≤ 2 ^ p * (f x ^ p + g x ^ p) := by
    intro x
    have hf0 := hf.2.1 x
    have hg0 := hg.2.1 x
    have h1 : f x + g x ≤ 2 * max (f x) (g x) := by
      have := le_max_left (f x) (g x); have := le_max_right (f x) (g x); linarith
    have h2 : max (f x) (g x) ^ p ≤ f x ^ p + g x ^ p := by
      rcases le_total (f x) (g x) with h | h
      · rw [max_eq_right h]; have := pow_nonneg hf0 p; linarith
      · rw [max_eq_left h]; have := pow_nonneg hg0 p; linarith
    calc (f x + g x) ^ p ≤ (2 * max (f x) (g x)) ^ p :=
          pow_le_pow_left₀ (by positivity) h1 p
      _ = 2 ^ p * max (f x) (g x) ^ p := mul_pow _ _ _
      _ ≤ _ := by gcongr
  have hsum : Integrable (fun x => 2 ^ p * (f x ^ p + g x ^ p)) ν :=
    (hf.2.2.1.add hg.2.2.1).const_mul _
  have hm : AEStronglyMeasurable (fun x => f x + g x) ν := hf.1.add hg.1
  have h0 : ∀ x, 0 ≤ f x + g x := fun x => add_nonneg (hf.2.1 x) (hg.2.1 x)
  have hint : Integrable (fun x => (f x + g x) ^ p) ν :=
    hsum.mono' (hm.pow p) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (h0 x) p)]; exact hpt x)
  refine ⟨hm, h0, hint, ?_⟩
  calc ∫ x, (f x + g x) ^ p ∂ν ≤ ∫ x, 2 ^ p * (f x ^ p + g x ^ p) ∂ν :=
        integral_mono hint hsum hpt
    _ = 2 ^ p * (∫ x, f x ^ p ∂ν + ∫ x, g x ^ p ∂ν) := by
        rw [integral_const_mul, integral_add hf.2.2.1 hg.2.2.1]
    _ ≤ 2 ^ p * (A ^ p + B ^ p) := by gcongr; exacts [hf.2.2.2, hg.2.2.2]
    _ ≤ 2 ^ p * (A + B) ^ p := by gcongr; exact pow_add_pow_le hA hB (by omega)
    _ = (2 * (A + B)) ^ p := (mul_pow _ _ _).symm

private theorem primMom_max {p : ℕ} (hp : 1 ≤ p) {f g : X → ℝ} {A B : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hf : PrimMom ν p f A) (hg : PrimMom ν p g B) :
    PrimMom ν p (fun x => max (f x) (g x)) (A + B) := by
  have hpt : ∀ x, max (f x) (g x) ^ p ≤ f x ^ p + g x ^ p := by
    intro x
    rcases le_total (f x) (g x) with h | h
    · rw [max_eq_right h]; have := pow_nonneg (hf.2.1 x) p; linarith
    · rw [max_eq_left h]; have := pow_nonneg (hg.2.1 x) p; linarith
  have hsum : Integrable (fun x => f x ^ p + g x ^ p) ν := hf.2.2.1.add hg.2.2.1
  have hm : AEStronglyMeasurable (fun x => max (f x) (g x)) ν := hf.1.sup hg.1
  have h0 : ∀ x, 0 ≤ max (f x) (g x) := fun x => le_max_of_le_left (hf.2.1 x)
  have hint : Integrable (fun x => max (f x) (g x) ^ p) ν :=
    hsum.mono' (hm.pow p) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (h0 x) p)]; exact hpt x)
  refine ⟨hm, h0, hint, ?_⟩
  calc ∫ x, max (f x) (g x) ^ p ∂ν ≤ ∫ x, f x ^ p + g x ^ p ∂ν := integral_mono hint hsum hpt
    _ = ∫ x, f x ^ p ∂ν + ∫ x, g x ^ p ∂ν := integral_add hf.2.2.1 hg.2.2.1
    _ ≤ A ^ p + B ^ p := add_le_add hf.2.2.2 hg.2.2.2
    _ ≤ (A + B) ^ p := pow_add_pow_le hA hB (by omega)

/-- `∏ u_i ≤ 1 + Σ u_i^p` for `N ≤ p` nonnegative numbers. -/
private theorem prim_prod_le_one_add {N p : ℕ} (hNp : N ≤ p) (u : Fin N → ℝ)
    (hu : ∀ i, 0 ≤ u i) : ∏ i, u i ≤ 1 + ∑ i, u i ^ p := by
  have hs : 0 ≤ ∑ i, u i ^ p := Finset.sum_nonneg fun i _ => pow_nonneg (hu i) p
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ u
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩)
  have h1 : ∏ i, u i ≤ u i₀ ^ N := by
    calc ∏ i, u i ≤ ∏ _i : Fin N, u i₀ :=
          Finset.prod_le_prod₀ (fun i _ => hu i) fun i _ => hi₀ i (Finset.mem_univ i)
      _ = u i₀ ^ N := by simp
  rcases le_total (u i₀) 1 with h | h
  · have := pow_le_one₀ (hu i₀) h (n := N); linarith
  · have h2 : u i₀ ^ N ≤ u i₀ ^ p := pow_le_pow_right₀ h hNp
    have h3 : u i₀ ^ p ≤ ∑ i, u i ^ p :=
      Finset.single_le_sum (f := fun i => u i ^ p) (fun i _ => pow_nonneg (hu i) p)
        (Finset.mem_univ i₀)
    linarith

/-- The expectation of a product of `N ≤ p` nonnegative factors with `E f_i^p ≤ A_i^p` is at
most `(N + 1) ∏ A_i`. -/
private theorem primMom_prod [IsProbabilityMeasure ν] {N p : ℕ} (hNp : N ≤ p)
    (f : Fin N → X → ℝ) (A : Fin N → ℝ) (hA : ∀ i, 0 < A i)
    (hf : ∀ i, PrimMom ν p (f i) (A i)) :
    Integrable (fun x => ∏ i, f i x) ν ∧ ∫ x, ∏ i, f i x ∂ν ≤ (N + 1) * ∏ i, A i := by
  have hPA : 0 < ∏ i, A i := Finset.prod_pos fun i _ => hA i
  set g : X → ℝ := fun x => (∏ i, A i) * (1 + ∑ i, (A i ^ p)⁻¹ * f i x ^ p) with hg
  have hpt : ∀ x, ∏ i, f i x ≤ g x := by
    intro x
    have hu := prim_prod_le_one_add hNp (fun i => f i x / A i)
      (fun i => div_nonneg ((hf i).2.1 x) (hA i).le)
    have e1 : ∏ i, f i x = (∏ i, A i) * ∏ i, (f i x / A i) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      field_simp [(hA i).ne']
    have e2 : ∀ i, (f i x / A i) ^ p = (A i ^ p)⁻¹ * f i x ^ p := by
      intro i; rw [div_pow, div_eq_inv_mul]
    simp only [e2] at hu
    rw [e1, hg]
    exact mul_le_mul_of_nonneg_left hu hPA.le
  have hgi : Integrable g ν := by
    refine (Integrable.add (integrable_const 1) ?_).const_mul _
    exact integrable_finsetSum _ fun i _ => (hf i).2.2.1.const_mul _
  have hm : AEStronglyMeasurable (fun x => ∏ i, f i x) ν :=
    Finset.aestronglyMeasurable_fun_prod _ fun i _ => (hf i).1
  have h0 : ∀ x, 0 ≤ ∏ i, f i x := fun x => Finset.prod_nonneg fun i _ => (hf i).2.1 x
  have hint : Integrable (fun x => ∏ i, f i x) ν :=
    hgi.mono' hm (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]; exact hpt x)
  refine ⟨hint, (integral_mono hint hgi hpt).trans ?_⟩
  have hI : ∫ x, g x ∂ν = (∏ i, A i) * (1 + ∑ i, (A i ^ p)⁻¹ * ∫ x, f i x ^ p ∂ν) := by
    rw [hg, integral_const_mul, integral_add (integrable_const 1)
      (integrable_finsetSum _ fun i _ => (hf i).2.2.1.const_mul _),
      integral_finsetSum _ fun i _ => (hf i).2.2.1.const_mul _]
    simp [integral_const_mul]
  rw [hI]
  have hb : ∀ i, (A i ^ p)⁻¹ * ∫ x, f i x ^ p ∂ν ≤ 1 := by
    intro i
    have hAp : 0 < A i ^ p := pow_pos (hA i) p
    rw [inv_mul_le_iff₀ hAp, mul_one]
    exact (hf i).2.2.2
  have hs : ∑ i, (A i ^ p)⁻¹ * ∫ x, f i x ^ p ∂ν ≤ N := by
    calc _ ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ => hb i
      _ = N := by simp
  nlinarith

end Moments

/-! ## Loops in block form and the interpolated blocks -/

section Blocks

open scoped Matrix.Norms.L2Operator


/-- The inclusion `ℂ^W → ℂ^L ⊗ ℂ^W` of the coordinates into block `b`. -/
private def primEmb (W L : ℕ) (b : Fin L) : Matrix (Fin L × Fin W) (Fin W) ℂ :=
  Matrix.of fun p β => if p = (b, β) then 1 else 0

/-- `E_b = W⁻¹ ι_b ι_b*`. -/
private theorem prim_emb_blockE (W L : ℕ) (b : Fin L) :
    blockE W L b = (W : ℂ)⁻¹ • (primEmb W L b * (primEmb W L b)ᴴ) := by
  ext p q
  simp only [blockE, primEmb, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.of_apply, smul_eq_mul]
  by_cases h : p = q
  · subst h
    obtain ⟨a, α⟩ := p
    by_cases hb : a = b
    · subst hb; simp
    · simp [hb]
  · simp only [h, ↓reduceIte]
    symm
    rw [mul_eq_zero]
    right
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hp : p = (b, x)
    · by_cases hq : q = (b, x)
      · exact absurd (hp.trans hq.symm) h
      · simp [hq]
    · simp [hp]

/-- `ι_a* X ι_b` is the `(a, b)` block of `X`. -/
private theorem prim_emb_block (W L : ℕ) (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : (primEmb W L a)ᴴ * X * primEmb W L b = blockOf X a b := by
  ext α β
  simp [primEmb, blockOf, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- `ι_{z_0}* X_1 E_{z_1} ⋯ X_m E_{z_m}` is `W^{-m}` times the ordered product of the blocks
`(X_i)_{z_{i-1} z_i}` and `ι_{z_m}*`. -/
private theorem prim_chain (W L : ℕ) :
    ∀ (m : ℕ) (z : Fin (m + 1) → Fin L) (X : Fin m → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ),
      (primEmb W L (z 0))ᴴ * (List.ofFn fun i : Fin m => X i * blockE W L (z i.succ)).prod =
        ((W : ℂ)⁻¹ ^ m) •
          (List.ofFn fun i : Fin m => blockOf (X i) (z i.castSucc) (z i.succ)).prod
          * (primEmb W L (z (Fin.last m)))ᴴ := by
  intro m
  induction m with
  | zero =>
    intro z X
    simp
  | succ m ih =>
    intro z X
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    have h := ih (fun i => z i.succ) (fun i => X i.succ)
    simp only [Fin.succ_castSucc, Fin.succ_last] at h
    set rest := (List.ofFn fun i : Fin m => X i.succ * blockE W L (z i.succ.succ)).prod
    have e1 : (primEmb W L (z 0))ᴴ * (X 0 * blockE W L (z (Fin.succ 0)) * rest) =
        (W : ℂ)⁻¹ • (blockOf (X 0) (z 0) (z (Fin.succ 0)) *
          ((primEmb W L (z (Fin.succ 0)))ᴴ * rest)) := by
      rw [prim_emb_blockE, ← prim_emb_block W L (X 0) (z 0) (z (Fin.succ 0))]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [e1, h, Fin.castSucc_zero]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, smul_smul, pow_succ]
    congr 1
    ring

private theorem prim_rot_symm_zero (m : ℕ) : (finRotate (m + 1)).symm 0 = Fin.last m :=
  (finRotate (m + 1)).symm_apply_eq.mpr finRotate_last'.symm

private theorem prim_rot_symm_succ (m : ℕ) (i : Fin m) :
    (finRotate (m + 1)).symm i.succ = i.castSucc :=
  (finRotate (m + 1)).symm_apply_eq.mpr (by rw [finRotate_apply, Fin.coeSucc_eq_succ])

/-- The loop trace of (5.5) [fo:eq:loops] in block form: `Tr(X_1 E_{x_1} ⋯ X_k E_{x_k})` is
`W^{-k}` times the trace of the ordered product of the blocks `(X_i)_{x_{i-1} x_i}`, with
`x_0 = x_k`. -/
private theorem prim_loop_trace (W L m : ℕ)
    (X : Fin (m + 1) → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (x : Fin (m + 1) → Fin L) :
    Matrix.trace (List.ofFn fun i : Fin (m + 1) => X i * blockE W L (x i)).prod =
      (W : ℂ)⁻¹ ^ (m + 1) * Matrix.trace (List.ofFn fun i : Fin (m + 1) =>
        blockOf (X i) (x ((finRotate (m + 1)).symm i)) (x i)).prod := by
  have h := prim_chain W L m x (fun i => X i.succ)
  rw [List.ofFn_succ, List.prod_cons]
  set rest := (List.ofFn fun i : Fin m => X i.succ * blockE W L (x i.succ)).prod
  set chain := (List.ofFn fun i : Fin m => blockOf (X i.succ) (x i.castSucc) (x i.succ)).prod
  have e1 : X 0 * blockE W L (x 0) * rest = (W : ℂ)⁻¹ • ((X 0 * primEmb W L (x 0)) *
      ((primEmb W L (x 0))ᴴ * rest)) := by
    rw [prim_emb_blockE]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  have e2 : (List.ofFn fun i : Fin (m + 1) =>
        blockOf (X i) (x ((finRotate (m + 1)).symm i)) (x i)).prod =
      blockOf (X 0) (x (Fin.last m)) (x 0) * chain := by
    rw [List.ofFn_succ, List.prod_cons, prim_rot_symm_zero]
    simp only [prim_rot_symm_succ]
    rfl
  rw [e1, h, e2, Matrix.trace_smul, smul_eq_mul]
  have e3 : (X 0 * primEmb W L (x 0)) *
      (((W : ℂ)⁻¹ ^ m) • chain * (primEmb W L (x (Fin.last m)))ᴴ) =
      ((W : ℂ)⁻¹ ^ m) •
        ((X 0 * primEmb W L (x 0) * chain) * (primEmb W L (x (Fin.last m)))ᴴ) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [e3, Matrix.trace_smul, Matrix.trace_mul_comm, smul_eq_mul]
  have e4 : (primEmb W L (x (Fin.last m)))ᴴ * (X 0 * primEmb W L (x 0) * chain) =
      blockOf (X 0) (x (Fin.last m)) (x 0) * chain := by
    rw [← prim_emb_block W L (X 0) (x (Fin.last m)) (x 0)]
    simp only [Matrix.mul_assoc]
  rw [e4]
  ring

/-! ## Anchor sums and coefficient bounds -/

/-- The first block `c` of a cell and its predecessor, indexed by `true` and `false`. -/
private def primAnch {L : ℕ} (c : Fin L) (i : Bool) : Fin L :=
  if i then c else (finRotate L).symm c

private theorem prim_anch_true {L : ℕ} (n : ℕ) (x : Fin L) :
    primAnch (cellStart n x) true = cellStart n x := rfl

private theorem prim_anch_false {L : ℕ} (n : ℕ) (x : Fin L) :
    primAnch (cellStart n x) false = cellPrev n x := rfl

private theorem prim_prev_ne {L : ℕ} (hL : 2 ≤ L) (c : Fin L) : (finRotate L).symm c ≠ c := by
  intro h
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 2 := ⟨L - 2, by omega⟩
  have h2 : c + 1 = c := by
    have := (finRotate (m + 2)).symm_apply_eq.mp h
    simpa using this.symm
  have h3 : (1 : Fin (m + 2)) = 0 := by simp at h2
  rw [Fin.one_eq_zero_iff] at h3
  omega

/-- A sum supported on the two anchors of a cell has two terms. -/
private theorem prim_sum_two {L : ℕ} (hL : 2 ≤ L) (c : Fin L) {M : Type*} [AddCommMonoid M]
    (φ : Fin L → M) (h0 : ∀ α, α ≠ c → α ≠ (finRotate L).symm c → φ α = 0) :
    ∑ α, φ α = ∑ i : Bool, φ (primAnch c i) := by
  rw [Fintype.sum_bool, Finset.sum_eq_add c ((finRotate L).symm c)
    (prim_prev_ne hL c).symm (fun α _ hα => h0 α hα.1 hα.2)
    (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h)]
  simp [primAnch]

/-- In the bulk `|E| ≤ 2 - κ`: `sin ϑ ≥ κ/2` for `ϑ = arccos (E/2)`. -/
private theorem prim_sin_ge {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ) :
    κ / 2 ≤ Real.sin (Real.arccos (E / 2)) := by
  have hS := Real.sin_arccos (E / 2)
  set S := Real.sin (Real.arccos (E / 2))
  have hE2 : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hE 2
  have hpos : 0 ≤ 1 - (E / 2) ^ 2 := by nlinarith
  have hS2 : S ^ 2 = 1 - (E / 2) ^ 2 := by rw [hS, Real.sq_sqrt hpos]
  have hS1 : S ≤ 1 := Real.sin_le_one _
  have hS0 : 0 ≤ S := by rw [hS]; exact Real.sqrt_nonneg _
  nlinarith

/-- `|sin t / sin ϑ| ≤ 2/κ` in the bulk. -/
private theorem prim_abs_div_le {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (t : ℝ) : |Real.sin t / Real.sin (Real.arccos (E / 2))| ≤ 2 / κ := by
  have hs := prim_sin_ge hκ hκ2 hE
  have hs0 : 0 < Real.sin (Real.arccos (E / 2)) := by linarith
  rw [abs_div, abs_of_pos hs0, div_le_div_iff₀ hs0 hκ]
  have := Real.abs_sin_le_one t
  nlinarith

/-- The free coefficients satisfy `|c_{aα}| ≤ 2/κ`. -/
private theorem prim_coef_abs_le {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (n : ℕ) {L : ℕ} (a α : Fin L) : |cellCoef n E a α| ≤ 2 / κ := by
  unfold cellCoef
  split_ifs
  · exact prim_abs_div_le hκ hκ2 hE _
  · rw [abs_neg]; exact prim_abs_div_le hκ hκ2 hE _
  · rw [abs_zero]; positivity

/-- The free source coefficients satisfy `|q_{ab}| ≤ 2/κ`. -/
private theorem prim_src_abs_le {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (n : ℕ) {L : ℕ} (a b : Fin L) : |cellSrc n E a b| ≤ 2 / κ := by
  unfold cellSrc
  split_ifs
  · exact prim_abs_div_le hκ hκ2 hE _
  · rw [abs_zero]; positivity

/-- `c_{aα}` vanishes off the two anchors of the cell of `a`. -/
private theorem prim_coef_other (n : ℕ) (E : ℝ) {L : ℕ} (a α : Fin L) (h1 : α ≠ cellStart n a)
    (h2 : α ≠ (finRotate L).symm (cellStart n a)) : cellCoef n E a α = 0 := by
  have h2' : α ≠ cellPrev n a := h2
  simp only [cellCoef, h1, h2', ite_false]

/-- `|d_{ab}| ≤ K + 2K²` with `K = 2/κ`. -/
private theorem prim_d_abs_le {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (n : ℕ) {L : ℕ} (hL : 2 ≤ L) (a b : Fin L) :
    |cellD n E a b| ≤ 2 / κ + 2 * (2 / κ) ^ 2 := by
  have hK : 0 ≤ 2 / κ := by positivity
  unfold cellD
  rw [prim_sum_two hL (cellStart n a) (fun α => cellCoef n E a α * cellSrc n E b α)
    (fun α h1 h2 => by
      rw [prim_coef_other n E a α h1 h2, zero_mul])]
  refine (abs_add_le _ _).trans ?_
  have h1 := prim_src_abs_le hκ hκ2 hE n a b
  have h2 : |∑ i : Bool, cellCoef n E a (primAnch (cellStart n a) i) *
      cellSrc n E b (primAnch (cellStart n a) i)| ≤ 2 * (2 / κ) ^ 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ i : Bool, |cellCoef n E a (primAnch (cellStart n a) i) *
        cellSrc n E b (primAnch (cellStart n a) i)| ≤ (2 / κ) ^ 2 := by
      intro i
      rw [abs_mul, sq]
      exact mul_le_mul (prim_coef_abs_le hκ hκ2 hE n _ _) (prim_src_abs_le hκ hκ2 hE n _ _)
        (abs_nonneg _) hK
    calc _ ≤ ∑ _i : Bool, (2 / κ) ^ 2 := Finset.sum_le_sum fun i _ => this i
      _ = 2 * (2 / κ) ^ 2 := by simp
  linarith

/-! ## Expansion of the interpolated blocks -/

/-- The double sum over blocks of `c_{pα} c_{qβ} f(α, β)` has only the four anchor terms. -/
private theorem prim_dblsum {L : ℕ} (hL : 2 ≤ L) (n : ℕ) (E : ℝ) (p q : Fin L) {M : Type*}
    [AddCommMonoid M] [Module ℂ M] (f : Fin L → Fin L → M) :
    ∑ α, ∑ β, ((cellCoef n E p α * cellCoef n E q β : ℝ) : ℂ) • f α β =
      ∑ i : Bool, ∑ j : Bool, ((cellCoef n E p (primAnch (cellStart n p) i) *
        cellCoef n E q (primAnch (cellStart n q) j) : ℝ) : ℂ) •
          f (primAnch (cellStart n p) i) (primAnch (cellStart n q) j) := by
  rw [prim_sum_two hL (cellStart n p) _ ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [prim_sum_two hL (cellStart n q) _ ?_]
    intro β h1 h2
    rw [prim_coef_other n E q β h1 h2]
    simp
  · intro α h1 h2
    refine Finset.sum_eq_zero fun β _ => ?_
    rw [prim_coef_other n E p α h1 h2]
    simp

/-- The constant matrices multiplying the six edge functions in the interpolation of the block
`(p, q)` (for the sign `σ`), where `c` and `d` are the first blocks of the cells of `p` and `q`. -/
private def primMat {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (σ : Bool)
    (c d : Fin L) : (Bool × Bool) ⊕ Bool → Matrix (Fin W) (Fin W) ℂ
  | .inl (i, j) => if σ then blockOf G (primAnch c i) (primAnch d j)
      else (blockOf G (primAnch d j) (primAnch c i))ᴴ
  | .inr false => if σ then 1 else 0
  | .inr true => if σ then 0 else 1

/-- The interpolation of `G_{pq}` as a combination of the six edge functions with constant
matrices. -/
private theorem prim_expand_true {W L : ℕ} (hL : 2 ≤ L) (n : ℕ) (E : ℝ)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (p q : Fin L) :
    interpBlock n E G p q =
      ∑ s, edgeFn n E s p q • primMat G true (cellStart n p) (cellStart n q) s := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, interpBlock,
    prim_dblsum hL n E p q (fun α β => blockOf G α β)]
  simp only [primMat, Fintype.sum_bool, edgeFn, ite_true, smul_zero, Bool.false_eq_true,
    ite_false, zero_add]
  rfl

/-- The adjoint of the interpolation of `G_{qp}` as a combination of the six edge functions of
`(p, q)` with constant matrices. -/
private theorem prim_expand_false {W L : ℕ} (hL : 2 ≤ L) (n : ℕ) (E : ℝ)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (p q : Fin L) :
    (interpBlock n E G q p)ᴴ =
      ∑ s, edgeFn n E s p q • primMat G false (cellStart n p) (cellStart n q) s := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, interpBlock,
    Matrix.conjTranspose_add, Matrix.conjTranspose_sum]
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Complex.star_def,
    Complex.conj_ofReal, Matrix.conjTranspose_one]
  rw [prim_dblsum hL n E q p (fun α β => (blockOf G α β)ᴴ)]
  simp only [primMat, Fintype.sum_bool, edgeFn, Bool.false_eq_true, ite_false, smul_zero,
    ite_true, add_zero, prim_anch_true, prim_anch_false,
    mul_comm (cellCoef n E p _) (cellCoef n E q _)]
  abel

/-! ## Norm bounds -/

/-- The identity matrix has operator norm at most `1`. -/
private theorem prim_norm_one_le (k : Type*) [Fintype k] [DecidableEq k] :
    ‖(1 : Matrix k k ℂ)‖ ≤ 1 := by
  have := Matrix.l2_opNorm_conjTranspose_mul_self (1 : Matrix k k ℂ)
  rw [Matrix.conjTranspose_one, Matrix.one_mul] at this
  nlinarith [norm_nonneg (1 : Matrix k k ℂ)]

/-- An anchor block is bounded by the anchor norm. -/
private theorem prim_anchor_le (n : ℕ) {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (p q : Fin L) (i j : Bool) :
    ‖blockOf G (primAnch (cellStart n p) i) (primAnch (cellStart n q) j)‖ ≤
      anchorNorm n G p q := by
  unfold anchorNorm
  cases i <;> cases j <;> simp [prim_anch_true, prim_anch_false]

/-- The anchor norm is nonnegative. -/
private theorem prim_anchorNorm_nonneg (n : ℕ) {W L : ℕ}
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (p q : Fin L) : 0 ≤ anchorNorm n G p q :=
  le_max_of_le_left (le_max_of_le_left (norm_nonneg _))

/-- The `(a, b)` block of an adjoint is the adjoint of the `(b, a)` block. -/
private theorem prim_blockOf_conjTranspose {W L : ℕ}
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (a b : Fin L) :
    blockOf Gᴴ a b = (blockOf G b a)ᴴ := by
  ext; simp [blockOf]

/-- An entry is bounded by the operator norm. -/
private theorem prim_norm_entry_le {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (i j : n) : ‖M i j‖ ≤ ‖M‖ := by
  have h := Matrix.l2_opNorm_mulVec M (EuclideanSpace.single j (1 : ℂ))
  have hn : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  rw [hn, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le ((EuclideanSpace.equiv n ℂ).symm
    (M.mulVec (EuclideanSpace.single j (1 : ℂ)).ofLp)) i
  convert this using 2
  simp

/-- `‖Tr D‖ ≤ W ‖D‖` for `D` on `ℂ^W`. -/
private theorem prim_norm_trace_le (W : ℕ) (D : Matrix (Fin W) (Fin W) ℂ) :
    ‖Matrix.trace D‖ ≤ W * ‖D‖ := by
  unfold Matrix.trace
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖Matrix.diag D i‖ ≤ ∑ _i : Fin W, ‖D‖ :=
        Finset.sum_le_sum fun i _ => prim_norm_entry_le D i i
    _ = W * ‖D‖ := by simp

/-- Expansion of an ordered product of sums of scalar multiples of matrices. -/
private theorem prim_prod_sum {ι : Type*} [Fintype ι] {W : ℕ} :
    ∀ (m : ℕ) (c : Fin m → ι → ℂ) (M : Fin m → ι → Matrix (Fin W) (Fin W) ℂ),
      (List.ofFn fun i => ∑ s, c i s • M i s).prod =
        ∑ t : Fin m → ι, (∏ i, c i (t i)) • (List.ofFn fun i => M i (t i)).prod := by
  intro m
  induction m with
  | zero => intro c M; simp
  | succ m ih =>
    intro c M
    rw [List.ofFn_succ, List.prod_cons, ih (fun i => c i.succ) (fun i => M i.succ),
      ← (Fin.consEquiv (fun _ : Fin (m + 1) => ι)).sum_comp, Fintype.sum_prod_type,
      Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ, Fin.prod_univ_succ,
      List.ofFn_succ, List.prod_cons, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [mul_comm]


/-- `ι_b* ι_b = 1`. -/
private theorem prim_emb_ct_mul (W L : ℕ) (b : Fin L) :
    (primEmb W L b)ᴴ * primEmb W L b = 1 := by
  ext α β
  simp only [primEmb, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.one_apply]
  rw [Finset.sum_eq_single (b, α)]
  · by_cases h : α = β
    · subst h; simp
    · simp [h]
  · intro p _ hp; simp [hp]
  · simp

/-- `‖ι_b‖ ≤ 1`. -/
private theorem prim_emb_norm_le (W L : ℕ) (b : Fin L) : ‖primEmb W L b‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (primEmb W L b)
  rw [prim_emb_ct_mul] at h
  have h1 := prim_norm_one_le (Fin W)
  nlinarith [norm_nonneg (primEmb W L b)]

/-- A block is bounded by the whole matrix: `‖X_{ab}‖ ≤ ‖X‖`. -/
private theorem prim_blockOf_norm_le {W L : ℕ} (X : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) : ‖blockOf X a b‖ ≤ ‖X‖ := by
  rw [← prim_emb_block]
  have ha := prim_emb_norm_le W L a
  have hb := prim_emb_norm_le W L b
  rw [← Matrix.l2_opNorm_conjTranspose] at ha
  calc ‖(primEmb W L a)ᴴ * X * primEmb W L b‖
      ≤ ‖(primEmb W L a)ᴴ * X‖ * ‖primEmb W L b‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖(primEmb W L a)ᴴ‖ * ‖X‖) * ‖primEmb W L b‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (1 * ‖X‖) * 1 := by gcongr
    _ = ‖X‖ := by ring

/-- `‖X^σ‖ = ‖X‖`. -/
private theorem prim_norm_sgnMat {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ)
    (σ : Bool) : ‖sgnMat X σ‖ = ‖X‖ := by
  cases σ
  · simp [sgnMat, Matrix.l2_opNorm_conjTranspose]
  · simp [sgnMat]

/-- Columnwise `Σ |(Y X)_ij|² ≤ ‖Y‖² Σ |X_ij|²`. -/
private theorem prim_sum_sq_mul_left {n : Type*} [Fintype n] [DecidableEq n]
    (Y X : Matrix n n ℂ) :
    ∑ i, ∑ j, ‖(Y * X) i j‖ ^ 2 ≤ ‖Y‖ ^ 2 * ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => ‖X i j‖ ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  set x : EuclideanSpace ℂ n := (EuclideanSpace.equiv n ℂ).symm (fun i => X i j) with hx
  have h := Matrix.l2_opNorm_mulVec Y x
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  simpa [hx, Matrix.mul_apply, Matrix.mulVec, dotProduct] using h2

private theorem prim_sum_sq_conjTranspose {n : Type*} [Fintype n] (X : Matrix n n ℂ) :
    ∑ i, ∑ j, ‖Xᴴ i j‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  rw [Finset.sum_comm]; simp [Matrix.conjTranspose_apply]

private theorem prim_nhs_nonneg (W : ℕ) {n : Type*} [Fintype n] (X : Matrix n n ℂ) :
    0 ≤ nhs W X := Real.sqrt_nonneg _

/-- `‖X^*‖_{2,W} = ‖X‖_{2,W}`. -/
private theorem prim_nhs_conjTranspose (W : ℕ) {n : Type*} [Fintype n] (X : Matrix n n ℂ) :
    nhs W Xᴴ = nhs W X := by
  unfold nhs; rw [prim_sum_sq_conjTranspose]

/-- `‖Y X‖_{2,W} ≤ ‖Y‖ ‖X‖_{2,W}`. -/
private theorem prim_nhs_mul_left (W : ℕ) {n : Type*} [Fintype n] [DecidableEq n]
    (Y X : Matrix n n ℂ) : nhs W (Y * X) ≤ ‖Y‖ * nhs W X := by
  unfold nhs
  rw [← Real.sqrt_sq (norm_nonneg Y), ← Real.sqrt_mul (sq_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  have h := prim_sum_sq_mul_left Y X
  have hW : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h hW]

/-- `‖X Y‖_{2,W} ≤ ‖X‖_{2,W} ‖Y‖`. -/
private theorem prim_nhs_mul_right (W : ℕ) {n : Type*} [Fintype n] [DecidableEq n]
    (X Y : Matrix n n ℂ) : nhs W (X * Y) ≤ nhs W X * ‖Y‖ := by
  rw [← prim_nhs_conjTranspose, Matrix.conjTranspose_mul, ← prim_nhs_conjTranspose W X,
    ← Matrix.l2_opNorm_conjTranspose Y, mul_comm]
  exact prim_nhs_mul_left W _ _

/-- `|W⁻¹ Tr X| ≤ ‖X‖_{2,W}` on `ℂ^W`. -/
private theorem prim_trace_le_nhs {W : ℕ} (hW : 1 ≤ W) (X : Matrix (Fin W) (Fin W) ℂ) :
    ‖(W : ℂ)⁻¹ * Matrix.trace X‖ ≤ nhs W X := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have h1 : ‖Matrix.trace X‖ ≤ ∑ i, ‖X i i‖ := by
    unfold Matrix.trace; exact (norm_sum_le _ _).trans (le_of_eq rfl)
  have h2 : ∑ i, ‖X i i‖ ≤ Real.sqrt W * Real.sqrt (∑ i, ∑ j, ‖X i j‖ ^ 2) := by
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : Fin W => (1 : ℝ))
      (fun i => ‖X i i‖)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at hcs
    refine hcs.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _))
    exact Finset.sum_le_sum fun i _ =>
      Finset.single_le_sum (f := fun j => ‖X i j‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ i)
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  unfold nhs
  rw [Real.sqrt_mul (by positivity), Real.sqrt_inv]
  have hsW : Real.sqrt W * Real.sqrt W = W := Real.mul_self_sqrt hW0.le
  have hs0 : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW0
  calc (W : ℝ)⁻¹ * ‖Matrix.trace X‖
      ≤ (W : ℝ)⁻¹ * (Real.sqrt W * Real.sqrt (∑ i, ∑ j, ‖X i j‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    _ = (Real.sqrt W)⁻¹ * Real.sqrt (∑ i, ∑ j, ‖X i j‖ ^ 2) := by
        have e : (W : ℝ)⁻¹ = (Real.sqrt W)⁻¹ * (Real.sqrt W)⁻¹ := by rw [← mul_inv, hsW]
        rw [e, mul_assoc, inv_mul_cancel_left₀ hs0.ne']

/-- Norm of an ordered product with factor bounds `N_i`. -/
private theorem prim_list_prod_norm_le {W : ℕ} :
    ∀ (m : ℕ) (Z : Fin m → Matrix (Fin W) (Fin W) ℂ) (N : Fin m → ℝ),
      (∀ i, 0 ≤ N i) → (∀ i, ‖Z i‖ ≤ N i) → ‖(List.ofFn Z).prod‖ ≤ ∏ i, N i := by
  intro m
  induction m with
  | zero => intro Z N _ _; simpa using prim_norm_one_le (Fin W)
  | succ m ih =>
    intro Z N h0 hZ
    rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul (hZ 0)
      (ih _ _ (fun i => h0 _) fun i => hZ _) (norm_nonneg _) (h0 0))

/-- Telescoping for the normalized trace of two ordered products:
`|W⁻¹ Tr A(∏Y − ∏Z)| ≤ ‖A‖ (Σ_i ‖Y_i − Z_i‖_{2,W}) ∏_i (1 + N_i)` when `‖Y_i‖, ‖Z_i‖ ≤ N_i`. -/
private theorem prim_tele {W : ℕ} (hW : 1 ≤ W) :
    ∀ (m : ℕ) (A : Matrix (Fin W) (Fin W) ℂ) (Y Z : Fin m → Matrix (Fin W) (Fin W) ℂ)
      (N : Fin m → ℝ), (∀ i, 0 ≤ N i) → (∀ i, ‖Y i‖ ≤ N i) → (∀ i, ‖Z i‖ ≤ N i) →
      ‖(W : ℂ)⁻¹ * Matrix.trace (A * ((List.ofFn Y).prod - (List.ofFn Z).prod))‖ ≤
        ‖A‖ * ((∑ i, nhs W (Y i - Z i)) * ∏ i, (1 + N i)) := by
  intro m
  induction m with
  | zero => intro A Y Z N _ _ _; simp
  | succ m ih =>
    intro A Y Z N h0 hY hZ
    set PY := (List.ofFn fun i : Fin m => Y i.succ).prod
    set PZ := (List.ofFn fun i : Fin m => Z i.succ).prod
    have hPZ : ‖PZ‖ ≤ ∏ i : Fin m, N i.succ :=
      prim_list_prod_norm_le m _ _ (fun i => h0 _) fun i => hZ _
    have hPN : ∏ i : Fin m, N i.succ ≤ ∏ i : Fin m, (1 + N i.succ) :=
      Finset.prod_le_prod₀ (fun i _ => h0 _) fun i _ => by linarith
    have hP1 : 1 ≤ ∏ i : Fin m, (1 + N i.succ) := by
      calc (1 : ℝ) = ∏ _i : Fin m, (1 : ℝ) := by simp
        _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun i _ => by linarith [h0 i.succ]
    have hih := ih (A * Y 0) (fun i => Y i.succ) (fun i => Z i.succ) (fun i => N i.succ)
      (fun i => h0 _) (fun i => hY _) fun i => hZ _
    have e : A * (Y 0 * PY - Z 0 * PZ) = A * (Y 0 - Z 0) * PZ + A * Y 0 * (PY - PZ) := by
      noncomm_ring
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, e, Matrix.trace_add,
      mul_add]
    refine (norm_add_le _ _).trans ?_
    have t1 : ‖(W : ℂ)⁻¹ * Matrix.trace (A * (Y 0 - Z 0) * PZ)‖ ≤
        ‖A‖ * (nhs W (Y 0 - Z 0) * ∏ i : Fin m, (1 + N i.succ)) := by
      refine (prim_trace_le_nhs hW _).trans ?_
      refine (prim_nhs_mul_right W _ _).trans ?_
      refine (mul_le_mul_of_nonneg_right (prim_nhs_mul_left W _ _) (norm_nonneg _)).trans ?_
      have := prim_nhs_nonneg W (Y 0 - Z 0)
      calc ‖A‖ * nhs W (Y 0 - Z 0) * ‖PZ‖ ≤ ‖A‖ * nhs W (Y 0 - Z 0) *
            ∏ i : Fin m, (1 + N i.succ) := by gcongr; exact hPZ.trans hPN
        _ = _ := by ring
    have t2 : ‖(W : ℂ)⁻¹ * Matrix.trace (A * Y 0 * (PY - PZ))‖ ≤
        ‖A‖ * ((1 + N 0) * ((∑ i : Fin m, nhs W (Y i.succ - Z i.succ)) *
          ∏ i : Fin m, (1 + N i.succ))) := by
      refine hih.trans ?_
      have hs : 0 ≤ (∑ i : Fin m, nhs W (Y i.succ - Z i.succ)) * ∏ i : Fin m, (1 + N i.succ) :=
        mul_nonneg (Finset.sum_nonneg fun i _ => prim_nhs_nonneg W _) (by linarith)
      calc ‖A * Y 0‖ * ((∑ i : Fin m, nhs W (Y i.succ - Z i.succ)) *
            ∏ i : Fin m, (1 + N i.succ))
          ≤ (‖A‖ * (1 + N 0)) * ((∑ i : Fin m, nhs W (Y i.succ - Z i.succ)) *
            ∏ i : Fin m, (1 + N i.succ)) := by
            gcongr
            refine (Matrix.l2_opNorm_mul _ _).trans ?_
            gcongr
            linarith [hY 0]
        _ = _ := by ring
    refine (add_le_add t1 t2).trans ?_
    rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
    have hg : 0 ≤ ‖A‖ * nhs W (Y 0 - Z 0) * (∏ i : Fin m, (1 + N i.succ)) * N 0 :=
      mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (prim_nhs_nonneg _ _)) (by linarith))
        (h0 0)
    nlinarith [hg]

/-- The interpolated block is bounded by `(6K² + K)(1 + anchorNorm)` with `K = 2/κ`. -/
private theorem prim_interp_norm_le {κ E : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hE : |E| ≤ 2 - κ)
    (n : ℕ) {W L : ℕ} (hL : 2 ≤ L) (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (a b : Fin L) :
    ‖interpBlock n E G a b‖ ≤ (6 * (2 / κ) ^ 2 + 2 / κ) * (1 + anchorNorm n G a b) := by
  have hK : 0 ≤ 2 / κ := by positivity
  have hA := prim_anchorNorm_nonneg n G a b
  rw [interpBlock, prim_dblsum hL n E a b (fun α β => blockOf G α β)]
  refine (norm_add_le _ _).trans ?_
  have hin : ∀ i j : Bool, ‖((cellCoef n E a (primAnch (cellStart n a) i) *
      cellCoef n E b (primAnch (cellStart n b) j) : ℝ) : ℂ) •
        blockOf G (primAnch (cellStart n a) i) (primAnch (cellStart n b) j)‖ ≤
          (2 / κ) ^ 2 * anchorNorm n G a b := by
    intro i j
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_mul, sq]
    exact mul_le_mul (mul_le_mul (prim_coef_abs_le hκ hκ2 hE n _ _)
      (prim_coef_abs_le hκ hκ2 hE n _ _) (abs_nonneg _) hK) (prim_anchor_le n G a b i j)
      (norm_nonneg _) (by positivity)
  have h1 : ‖∑ i : Bool, ∑ j : Bool, ((cellCoef n E a (primAnch (cellStart n a) i) *
      cellCoef n E b (primAnch (cellStart n b) j) : ℝ) : ℂ) •
        blockOf G (primAnch (cellStart n a) i) (primAnch (cellStart n b) j)‖ ≤
          4 * ((2 / κ) ^ 2 * anchorNorm n G a b) := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _i : Bool, ∑ _j : Bool, (2 / κ) ^ 2 * anchorNorm n G a b :=
          Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun j _ => hin i j)
      _ = _ := by simp; ring
  have h2 : ‖((cellD n E a b : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤
      2 / κ + 2 * (2 / κ) ^ 2 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have := prim_norm_one_le (Fin W)
    have hd := prim_d_abs_le hκ hκ2 hE n hL a b
    calc |cellD n E a b| * ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ |cellD n E a b| * 1 := by
          gcongr
      _ ≤ _ := by linarith
  nlinarith [mul_nonneg (sq_nonneg (2 / κ)) hA]

end Blocks

/-! ## The auxiliary model as a block model on the cycle -/

section Model

open scoped Matrix.Norms.L2Operator

/-- The blocks `√(tγ_g) V_r` of the auxiliary model. -/
private def primV (g : ℝ) (W L : ℕ) (t : ℝ) (ω : Ω W L) : Fin L → Matrix (Fin W) (Fin W) ℂ :=
  fun r => ((Real.sqrt (t * gammaG g) : ℝ) : ℂ) • gueBlock W L ω r

/-- `A_L ⊗ I + diag(√(tγ_g) V_r)`. -/
private def primH (g : ℝ) (W L : ℕ) (t : ℝ) (ω : Ω W L) :
    Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp (primV g W L t ω)

private theorem primV_herm (g : ℝ) (W L : ℕ) (t : ℝ) (ω : Ω W L) (r : Fin L) :
    (primV g W L t ω r).IsHermitian := by
  unfold primV Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, (gueBlock_isHermitian W L ω r).eq]
  simp [Complex.conj_ofReal]

private theorem primH_herm (g : ℝ) (W L : ℕ) (t : ℝ) (ω : Ω W L) :
    (primH g W L t ω).IsHermitian := by
  refine Matrix.IsHermitian.add ?_ (blockDiagOp_isHermitian (primV_herm g W L t ω))
  rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, (cycleAdj_isHermitian L).eq,
    Matrix.conjTranspose_one]

/-- For `g ≥ 1` the single-time matrix `A_g ⊗ I + √(tγ_g) V` is `primH`. -/
private theorem prim_flow_eq {g : ℝ} (hg : 1 ≤ g) (W L : ℕ) (t : ℝ) (ω : Ω W L) :
    blockFlow W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) (t * gammaG g) ω =
      primH g W L t ω :=
  flowH_cycle g hg W L t ω

/-- For `g ≥ 1` the resolvent of the auxiliary model is the resolvent of `primH` at `z_t`. -/
private theorem prim_auxG_eq {g : ℝ} (hg : 1 ≤ g) (W L : ℕ) (E : ℝ) (m : ℂ) (t : ℝ)
    (ω : Ω W L) : auxG g W L E m t ω = resolventMat (primH g W L t ω) (zChar g E m t) := by
  unfold auxG resolventMat
  rw [← blockFlow_Ag_eq_Hdet, prim_flow_eq hg]

private theorem prim_cont_gue (W L : ℕ) (r : Fin L) :
    Continuous fun ω : Ω W L => gueBlock W L ω r := by
  refine continuous_matrix fun α β => ?_
  simp only [gueBlock, Matrix.of_apply]
  split_ifs <;> fun_prop

private theorem prim_cont_V (g : ℝ) (W L : ℕ) (t : ℝ) (r : Fin L) :
    Continuous fun ω : Ω W L => primV g W L t ω r := by
  unfold primV
  exact (continuous_const (y := ((Real.sqrt (t * gammaG g) : ℝ) : ℂ))).smul
    (prim_cont_gue W L r)

private theorem prim_cont_H (g : ℝ) (W L : ℕ) (t : ℝ) :
    Continuous fun ω : Ω W L => primH g W L t ω := by
  refine continuous_const.add (continuous_matrix fun p q => ?_)
  simp only [blockDiagOp, Matrix.of_apply]
  split_ifs
  · exact (prim_cont_V g W L t p.1).matrix_elem p.2 q.2
  · exact continuous_const

/-- The resolvent of `primH` is continuous in the sample. -/
private theorem prim_cont_G (g : ℝ) (W L : ℕ) (t : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    Continuous fun ω : Ω W L => resolventMat (primH g W L t ω) z := by
  have hc : Continuous fun ω : Ω W L =>
      primH g W L t ω - z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) :=
    (prim_cont_H g W L t).sub continuous_const
  refine continuous_iff_continuousAt.mpr fun ω => ?_
  have hdet : (primH g W L t ω - z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)).det ≠ 0 := by
    have := isUnit_sub_smul_one (primH_herm g W L t ω) hz
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at this
    exact this
  have hinv : ContinuousAt Ring.inverse
      (primH g W L t ω - z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  exact ContinuousAt.comp (f := fun ω : Ω W L =>
    primH g W L t ω - z • (1 : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ))
    (continuousAt_matrix_inv _ hinv) hc.continuousAt

private theorem prim_cont_blockOf {Y : Type*} [TopologicalSpace Y] {W L : ℕ}
    {F : Y → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hF : Continuous F) (a b : Fin L) :
    Continuous fun y => blockOf (F y) a b :=
  continuous_matrix fun α β => hF.matrix_elem (a, α) (b, β)

private theorem prim_cont_list_prod {Y : Type*} [TopologicalSpace Y] {W : ℕ} :
    ∀ (k : ℕ) (F : Fin k → Y → Matrix (Fin W) (Fin W) ℂ), (∀ i, Continuous (F i)) →
      Continuous fun y => (List.ofFn fun i => F i y).prod := by
  intro k
  induction k with
  | zero => intro F _; simpa using continuous_const
  | succ k ih =>
    intro F hF
    simp only [List.ofFn_succ, List.prod_cons]
    exact (hF 0).matrix_mul (ih (fun i => F i.succ) fun i => hF _)

private theorem prim_cont_cellProd (g : ℝ) (W L : ℕ) (t : ℝ) (z : ℂ) (b : Fin L) :
    ∀ j : ℕ, Continuous fun ω : Ω W L => cellProd z (primV g W L t ω) b j := by
  intro j
  induction j with
  | zero => exact continuous_const
  | succ j ih =>
    simp only [cellProd]
    refine Continuous.matrix_mul ?_ ih
    unfold blockT
    exact Continuous.matrix_fromBlocks (continuous_const.sub (prim_cont_V g W L t _))
      continuous_const continuous_const continuous_const

private theorem prim_cont_nhs (W : ℕ) {n : Type*} [Fintype n] :
    Continuous fun X : Matrix n n ℂ => nhs W X := by
  unfold nhs
  refine Real.continuous_sqrt.comp (continuous_const.mul ?_)
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((continuous_apply_apply i j).norm).pow 2

/-- A conditional factor `if c then f else 0` keeps the moment bound of `f`. -/
private theorem prim_mom_ite {X : Type*} [MeasurableSpace X] {ν : Measure X}
    [IsProbabilityMeasure ν] {p : ℕ} {f : X → ℝ} {A : ℝ} (hA : 0 ≤ A) {c : Prop} [Decidable c]
    (hf : PrimMom ν p f A) : PrimMom ν p (fun x => if c then f x else 0) A := by
  by_cases h : c
  · simpa [h] using hf
  · simp only [h, ite_false]
    exact primMom_mono le_rfl hA (primMom_const le_rfl p)

/-- The anchor-pair matrices are bounded by `max 1 ‖G‖`. -/
private theorem prim_mat_norm_le {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (σ : Bool) (c d : Fin L) (s : (Bool × Bool) ⊕ Bool) : ‖primMat G σ c d s‖ ≤ max 1 ‖G‖ := by
  rcases s with ⟨i, j⟩ | b
  · cases σ
    · simp only [primMat, Bool.false_eq_true, ite_false, Matrix.l2_opNorm_conjTranspose]
      exact (prim_blockOf_norm_le G _ _).trans (le_max_right _ _)
    · simp only [primMat, ite_true]
      exact (prim_blockOf_norm_le G _ _).trans (le_max_right _ _)
  · cases σ <;> cases b <;>
      simp only [primMat, Bool.false_eq_true, ite_false, ite_true, norm_zero] <;>
      first
        | exact (prim_norm_one_le _).trans (le_max_left _ _)
        | exact le_trans zero_le_one (le_max_left _ _)

private theorem prim_cont_mat {Y : Type*} [TopologicalSpace Y] {W L : ℕ}
    {F : Y → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hF : Continuous F) (σ : Bool)
    (c d : Fin L) (s : (Bool × Bool) ⊕ Bool) : Continuous fun y => primMat (F y) σ c d s := by
  rcases s with ⟨i, j⟩ | b
  · cases σ
    · simp only [primMat, Bool.false_eq_true, ite_false]
      exact (prim_cont_blockOf hF _ _).matrix_conjTranspose
    · simp only [primMat, ite_true]
      exact prim_cont_blockOf hF _ _
  · cases σ <;> cases b <;> simp only [primMat, Bool.false_eq_true, ite_false, ite_true] <;>
      exact continuous_const

/-- A loop factor `X^σ_{pq}` is the `σ`-adjoint of the block `X_{αβ}` with `(α, β) = (p, q)` for
`σ = +` and `(q, p)` for `σ = -`. -/
private theorem prim_Y_eq {W L : ℕ} (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (σ : Bool)
    (p q : Fin L) :
    blockOf (sgnMat G σ) p q = sgnMat (blockOf G (if σ then p else q) (if σ then q else p)) σ := by
  cases σ
  · simp [sgnMat, prim_blockOf_conjTranspose]
  · simp [sgnMat]

/-- The interpolated factor in the same form. -/
private theorem prim_Z_eq {W L : ℕ} (hL : 2 ≤ L) (n : ℕ) (E : ℝ)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (σ : Bool) (p q : Fin L) :
    ∑ s, edgeFn n E s p q • primMat G σ (cellStart n p) (cellStart n q) s =
      sgnMat (interpBlock n E G (if σ then p else q) (if σ then q else p)) σ := by
  cases σ
  · rw [← prim_expand_false hL n E G p q]; simp [sgnMat]
  · rw [← prim_expand_true hL n E G p q]; simp [sgnMat]

/-- Lemma 5.5 [fo:lem:resolvent-moments] for a block of the auxiliary resolvent at `z`, in the
form of a moment bound `E‖G_{ab}‖^P ≤ (max{1, C} B⁻¹)^P` when `g² Im z ≥ B`. -/
private theorem prim_mom_block {κ C Crm : ℝ} {P : ℕ} (hP : 1 ≤ P)
    (hrm : ∀ W : ℕ, 4 * (P : ℝ) ≤ W → ∀ L : ℕ, ∀ g : ℝ, 2 / Real.sqrt (κ / 2) ≤ g →
      4 * g ^ 2 ≤ L → ∀ E η t : ℝ, |E| ≤ 2 - κ / 2 → 0 < η → η ≤ C / g ^ 2 → 0 ≤ t → t ≤ 1 →
      ∀ a b : Fin L,
      Integrable (fun ω => ‖blockOf (resolventMat (blockFlow W L
          (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) (t * gammaG g) ω) (↑E + ↑η * Complex.I))
          a b‖ ^ (P : ℝ)) (μ W L) ∧
      ∫ ω, ‖blockOf (resolventMat (blockFlow W L (Ag g L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ))
          (t * gammaG g) ω) (↑E + ↑η * Complex.I)) a b‖ ^ (P : ℝ) ∂(μ W L) ≤
        Crm * (g ^ 2 * η) ^ (-(P : ℝ)))
    {W L : ℕ} (hW : 4 * (P : ℝ) ≤ W) {g : ℝ} (hg1 : 1 ≤ g) (hg : 2 / Real.sqrt (κ / 2) ≤ g)
    (hL : 4 * g ^ 2 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {z : ℂ}
    (hzE : |z.re| ≤ 2 - κ / 2) (hη : 0 < z.im) (hηC : z.im ≤ C / g ^ 2) {B : ℝ} (hB : 0 < B)
    (hgη : B ≤ g ^ 2 * z.im) (a b : Fin L) :
    PrimMom (μ W L) P (fun ω => ‖blockOf (resolventMat (primH g W L t ω) z) a b‖)
      (max 1 Crm * B⁻¹) := by
  obtain ⟨hI, hle⟩ := hrm W hW L g hg hL z.re z.im t hzE hη hηC ht0 ht1 a b
  have hz : ((z.re : ℂ) + (z.im : ℂ) * Complex.I) = z := Complex.re_add_im z
  rw [hz] at hI hle
  simp only [prim_flow_eq hg1, Real.rpow_natCast] at hI hle
  refine ⟨((prim_cont_blockOf (prim_cont_G g W L t hη.ne') a b).norm).aestronglyMeasurable,
    fun ω => norm_nonneg _, hI, hle.trans ?_⟩
  have hgη0 : 0 < g ^ 2 * z.im := lt_of_lt_of_le hB hgη
  have h1 : (g ^ 2 * z.im) ^ (-(P : ℝ)) ≤ (B⁻¹) ^ P := by
    rw [Real.rpow_neg hgη0.le, Real.rpow_natCast, inv_pow]
    exact inv_anti₀ (pow_pos hB P) (pow_le_pow_left₀ hB.le hgη P)
  have h2 : Crm ≤ (max 1 Crm) ^ P :=
    (le_max_right 1 Crm).trans (le_self_pow₀ (le_max_left 1 Crm) (by omega))
  have h3 : 0 ≤ (g ^ 2 * z.im) ^ (-(P : ℝ)) := Real.rpow_nonneg hgη0.le _
  rw [mul_pow]
  exact mul_le_mul h2 h1 h3 (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) P)

/-- (7.14) [uvc:eq:prefix-moments] for the transfer products of the auxiliary model, in the
form of a moment bound for `‖T_{b+j-1}(z) ⋯ T_b(z) - T(E)^j‖_{2,W}`. -/
private theorem prim_mom_pref {κ Cpm cpm : ℝ} {q : ℕ}
    (hpm : ∀ (W L : ℕ) (E s : ℝ) (z : ℂ) (b : Fin L) (n j : ℕ),
      |E| ≤ 2 - κ → 0 ≤ s → n ≤ L → j ≤ n → (n : ℝ) * s ≤ cpm → (n : ℝ) * ‖z - E‖ ≤ cpm →
      Integrable (fun ω => (∑ x, ∑ y, ‖(cellProd z (fun r => ((Real.sqrt s : ℝ) : ℂ) •
          gueBlock W L ω r) b j - blockT (E : ℂ) 0 ^ j :
            Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) x y‖ ^ 2) ^ q) (μ W L) ∧
      ∫ ω, (∑ x, ∑ y, ‖(cellProd z (fun r => ((Real.sqrt s : ℝ) : ℂ) • gueBlock W L ω r) b j -
          blockT (E : ℂ) 0 ^ j : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) x y‖ ^ 2) ^ q
          ∂(μ W L) ≤
        Cpm * (W : ℝ) ^ q * (((n : ℝ) * s) ^ q + ((n : ℝ) * ‖z - E‖) ^ (2 * q)))
    {W L : ℕ} (hW : 1 ≤ W) {E g t : ℝ} (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) {z : ℂ} {n j : ℕ}
    (hnL : n ≤ L) (hjn : j ≤ n) (hns : (n : ℝ) * (t * gammaG g) ≤ cpm)
    (hnz : (n : ℝ) * ‖z - E‖ ≤ cpm) (b : Fin L) {D : ℝ}
    (hDb : Cpm * (((n : ℝ) * (t * gammaG g)) ^ q + ((n : ℝ) * ‖z - E‖) ^ (2 * q)) ≤
      D ^ (2 * q)) :
    PrimMom (μ W L) (2 * q) (fun ω => prodErr (nhs W) E z (primV g W L t ω) b j) D := by
  have hγ : 0 ≤ gammaG g := by unfold gammaG; positivity
  obtain ⟨hI, hle⟩ := hpm W L E (t * gammaG g) z b n j hE (mul_nonneg ht0 hγ) hnL hjn hns hnz
  set S : Ω W L → ℝ := fun ω => ∑ x, ∑ y, ‖(cellProd z (primV g W L t ω) b j -
      blockT (E : ℂ) 0 ^ j : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) x y‖ ^ 2 with hS
  have hS0 : ∀ ω, 0 ≤ S ω := fun ω => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hpow : ∀ ω, prodErr (nhs W) E z (primV g W L t ω) b j ^ (2 * q) =
      ((W : ℝ)⁻¹) ^ q * S ω ^ q := by
    intro ω
    have h0 : 0 ≤ (W : ℝ)⁻¹ * S ω := mul_nonneg (by positivity) (hS0 ω)
    change (Real.sqrt ((W : ℝ)⁻¹ * S ω)) ^ (2 * q) = _
    rw [pow_mul, Real.sq_sqrt h0, mul_pow]
  have hI' : Integrable (fun ω => S ω ^ q) (μ W L) := hI
  have hle' : ∫ ω, S ω ^ q ∂(μ W L) ≤ Cpm * (W : ℝ) ^ q *
      (((n : ℝ) * (t * gammaG g)) ^ q + ((n : ℝ) * ‖z - E‖) ^ (2 * q)) := hle
  refine ⟨((prim_cont_nhs W).comp ((prim_cont_cellProd g W L t z b j).sub
    continuous_const)).aestronglyMeasurable, fun ω => prim_nhs_nonneg W _, ?_, ?_⟩
  · simp only [hpow]; exact hI'.const_mul _
  · simp only [hpow]
    rw [integral_const_mul]
    calc ((W : ℝ)⁻¹) ^ q * ∫ ω, S ω ^ q ∂(μ W L)
        ≤ ((W : ℝ)⁻¹) ^ q * (Cpm * (W : ℝ) ^ q *
          (((n : ℝ) * (t * gammaG g)) ^ q + ((n : ℝ) * ‖z - E‖) ^ (2 * q))) :=
          mul_le_mul_of_nonneg_left hle' (by positivity)
      _ = Cpm * (((n : ℝ) * (t * gammaG g)) ^ q + ((n : ℝ) * ‖z - E‖) ^ (2 * q)) := by
          rw [inv_pow]; field_simp
      _ ≤ D ^ (2 * q) := hDb

/-- The first index `α_i` of the `i`-th factor of a loop word: `x_{i-1}` for `σ_i = +`, `x_i`
for `σ_i = -`. -/
private def primAl {L k : ℕ} (σ : Fin k → Bool) (x : Fin k → Fin L) (i : Fin k) : Fin L :=
  if σ i then x ((finRotate k).symm i) else x i

/-- The second index `β_i` of the `i`-th factor of a loop word. -/
private def primBe {L k : ℕ} (σ : Fin k → Bool) (x : Fin k → Fin L) (i : Fin k) : Fin L :=
  if σ i then x i else x ((finRotate k).symm i)

/-- The coefficient `W⁻¹ Tr ∏_i M_{i, w_i}` of the spanning function of the word `w`. -/
private def primCoef {W L k : ℕ} (n : ℕ) (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (σ : Fin k → Bool) (a : Fin k → Fin L) (w : Fin k → (Bool × Bool) ⊕ Bool) : ℂ :=
  (W : ℂ)⁻¹ * Matrix.trace (List.ofFn fun i => primMat G (σ i)
    (cellStart n (a ((finRotate k).symm i))) (cellStart n (a i)) (w i)).prod

/-- The spanning function `x ↦ ∏_j f_{w(j+1)}(x_j, x_{j+1})` of the word `w`. -/
private def primBas {L k : ℕ} (n : ℕ) (E : ℝ) (w : Fin k → (Bool × Bool) ⊕ Bool)
    (x : Fin k → Fin L) : ℂ :=
  ∏ j, edgeFn n E (w (finRotate k j)) (x j) (x (finRotate k j))

/-- The normalized loop `W^{k-1} ℒ_k` as `W⁻¹ Tr` of the ordered product of the factors
`(X_{α_i β_i})^{σ_i}`. -/
private theorem prim_loop_block {W L k : ℕ} (hW : 1 ≤ W) (hk : 1 ≤ k)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (x : Fin k → Fin L) (σ : Fin k → Bool) :
    (W : ℂ) ^ (k - 1) * loopTr G x σ = (W : ℂ)⁻¹ * Matrix.trace (List.ofFn fun i =>
      sgnMat (blockOf G (primAl σ x i) (primBe σ x i)) (σ i)).prod := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast (by omega : W ≠ 0)
  have h := prim_loop_trace W L m (fun i => sgnMat G (σ i)) x
  have h' : loopTr G x σ = Matrix.trace (List.ofFn fun i : Fin (m + 1) =>
      sgnMat G (σ i) * blockE W L (x i)).prod := rfl
  have hY : ∀ i, blockOf (sgnMat G (σ i)) (x ((finRotate (m + 1)).symm i)) (x i) =
      sgnMat (blockOf G (primAl σ x i) (primBe σ x i)) (σ i) := by
    intro i
    rw [prim_Y_eq]
    simp only [primAl, primBe]
  rw [h', h]
  simp only [hY]
  rw [Nat.add_sub_cancel, pow_succ, inv_pow]
  field_simp

/-- The ordered product of the interpolated factors expands in the spanning functions. -/
private theorem prim_interp_expand {W L k : ℕ} (hL : 2 ≤ L) (n : ℕ) (E : ℝ)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (σ : Fin k → Bool) (a x : Fin k → Fin L)
    (hx : ∀ j, cellStart n (x j) = cellStart n (a j)) :
    (W : ℂ)⁻¹ * Matrix.trace (List.ofFn fun i =>
      sgnMat (interpBlock n E G (primAl σ x i) (primBe σ x i)) (σ i)).prod =
        ∑ w, primCoef n G σ a w * primBas n E w x := by
  set e := finRotate k
  have hZ : ∀ i, sgnMat (interpBlock n E G (primAl σ x i) (primBe σ x i)) (σ i) =
      ∑ s, edgeFn n E s (x (e.symm i)) (x i) •
        primMat G (σ i) (cellStart n (a (e.symm i))) (cellStart n (a i)) s := by
    intro i
    rw [← hx (e.symm i), ← hx i, prim_Z_eq hL n E G (σ i) (x (e.symm i)) (x i)]
    simp only [primAl, primBe]
    cases σ i <;> rfl
  simp only [hZ]
  rw [prim_prod_sum k (fun i s => edgeFn n E s (x (e.symm i)) (x i))
    (fun i s => primMat G (σ i) (cellStart n (a (e.symm i))) (cellStart n (a i)) s),
    Matrix.trace_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Matrix.trace_smul, smul_eq_mul]
  have hp : ∏ i, edgeFn n E (w i) (x (e.symm i)) (x i) =
      ∏ j, edgeFn n E (w (e j)) (x j) (x (e j)) := by
    rw [← Equiv.prod_comp e]
    simp
  rw [hp, primCoef, primBas]
  ring

/-- A combination of the spanning functions lies in the common space. -/
private theorem prim_mem_loopSpace {L k : ℕ} (n : ℕ) (E : ℝ) (a : Fin k → Fin L)
    (d : (Fin k → (Bool × Bool) ⊕ Bool) → ℂ) :
    (fun x : CellProd n a => ∑ w, d w * primBas n E w x.1) ∈ loopSpace n E a := by
  have hv : (fun x : CellProd n a => ∑ w, d w * primBas n E w x.1) =
      ∑ w : Fin k → (Bool × Bool) ⊕ Bool, d w • (fun x : CellProd n a =>
        ∏ j, edgeFn n E (w (finRotate k j)) (x.1 j) (x.1 (finRotate k j))) := by
    funext x
    simp [primBas, Finset.sum_apply]
  rw [hv]
  exact Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨fun j => w (finRotate k j), rfl⟩)

private theorem prim_cont_sgn {Y : Type*} [TopologicalSpace Y] {n : Type*}
    {F : Y → Matrix n n ℂ} (hF : Continuous F) (σ : Bool) :
    Continuous fun y => sgnMat (F y) σ := by
  cases σ
  · simp only [sgnMat, Bool.false_eq_true, ite_false]; exact hF.matrix_conjTranspose
  · simpa [sgnMat] using hF

private theorem prim_sgn_sub {n : Type*} (X Y : Matrix n n ℂ) (σ : Bool) :
    sgnMat X σ - sgnMat Y σ = sgnMat (X - Y) σ := by
  cases σ <;> simp [sgnMat, Matrix.conjTranspose_sub]

private theorem prim_nhs_sgn (W : ℕ) {n : Type*} [Fintype n] (X : Matrix n n ℂ) (σ : Bool) :
    nhs W (sgnMat X σ) = nhs W X := by
  cases σ
  · simp only [sgnMat, Bool.false_eq_true, ite_false]; exact prim_nhs_conjTranspose W X
  · simp [sgnMat]

/-- `|W⁻¹ Tr X| ≤ ‖X‖` on `ℂ^W`. -/
private theorem prim_trace_le_norm {W : ℕ} (hW : 1 ≤ W) (X : Matrix (Fin W) (Fin W) ℂ) :
    ‖(W : ℂ)⁻¹ * Matrix.trace X‖ ≤ ‖X‖ := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have := prim_norm_trace_le W X
  calc (W : ℝ)⁻¹ * ‖Matrix.trace X‖ ≤ (W : ℝ)⁻¹ * (W * ‖X‖) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = ‖X‖ := by field_simp

end Model

/-! ## The auxiliary loops near the common space -/

section Main

open scoped Matrix.Norms.L2Operator

/-- The interpolation error factor `C (e_z(α, β) + e_{z̄}(β, α₀) + e_{z̄}(β, α₋))` of
`green_interp_hs` for the factor `(α, β)`. -/
private def primErr {W L : ℕ} (Chs : ℝ) (n : ℕ) (E : ℝ) (z : ℂ)
    (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (α β : Fin L) : ℝ :=
  Chs * (interpErr (nhs W) n E z V α β + interpErr (nhs W) n E (starRingEnd ℂ z) V β
    (cellStart n α) + interpErr (nhs W) n E (starRingEnd ℂ z) V β (cellPrev n α))

/-- The common bound `1 + ‖X_{αβ}‖ + A (1 + anchorNorm)` of the exact and interpolated
factors. -/
private def primN {W L : ℕ} (AK : ℝ) (n : ℕ) (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (α β : Fin L) : ℝ :=
  1 + (‖blockOf G α β‖ + AK * (1 + anchorNorm n G α β))

/-- Deterministic telescoping bound for one sample: the normalized loop and its interpolation
differ by at most `Σ_i e_i (1 + interpEnv_i) ∏_j N_j`. -/
private theorem prim_pointwise {κ Chs : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2)
    (hhs : ∀ (W L n : ℕ) (E : ℝ) (z : ℂ) (V : Fin L → Matrix (Fin W) (Fin W) ℂ),
      1 ≤ W → 3 ≤ L → 1 ≤ n → |E| ≤ 2 - κ → (∀ r, (V r).IsHermitian) → z.im ≠ 0 →
      let G := resolventMat (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V) z
      ∀ a b : Fin L,
        nhs W (blockOf G a b - interpBlock n E G a b) ≤
          Chs * (interpErr (nhs W) n E z V a b +
              interpErr (nhs W) n E (starRingEnd ℂ z) V b (cellStart n a) +
              interpErr (nhs W) n E (starRingEnd ℂ z) V b (cellPrev n a)) *
            (1 + interpEnv n G a b))
    {W L n k : ℕ} (hW : 1 ≤ W) (hL : 3 ≤ L) (hn : 1 ≤ n) {E : ℝ} (hE : |E| ≤ 2 - κ) {z : ℂ}
    (hz : z.im ≠ 0) (V : Fin L → Matrix (Fin W) (Fin W) ℂ) (hV : ∀ r, (V r).IsHermitian)
    (x : Fin k → Fin L) (σ : Fin k → Bool) :
    let G := resolventMat (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V) z
    ‖(W : ℂ)⁻¹ * Matrix.trace (List.ofFn fun i =>
        sgnMat (blockOf G (primAl σ x i) (primBe σ x i)) (σ i)).prod -
      (W : ℂ)⁻¹ * Matrix.trace (List.ofFn fun i =>
        sgnMat (interpBlock n E G (primAl σ x i) (primBe σ x i)) (σ i)).prod‖ ≤
      ∑ i, primErr Chs n E z V (primAl σ x i) (primBe σ x i) *
        (1 + interpEnv n G (primAl σ x i) (primBe σ x i)) *
          ∏ j, primN (6 * (2 / κ) ^ 2 + 2 / κ) n G (primAl σ x j) (primBe σ x j) := by
  intro G
  have hL2 : 2 ≤ L := by omega
  set AK : ℝ := 6 * (2 / κ) ^ 2 + 2 / κ with hAK
  have hAK0 : 0 ≤ AK := by positivity
  set Y : Fin k → Matrix (Fin W) (Fin W) ℂ := fun i =>
    sgnMat (blockOf G (primAl σ x i) (primBe σ x i)) (σ i) with hY
  set Z : Fin k → Matrix (Fin W) (Fin W) ℂ := fun i =>
    sgnMat (interpBlock n E G (primAl σ x i) (primBe σ x i)) (σ i) with hZ
  set N : Fin k → ℝ := fun j => ‖blockOf G (primAl σ x j) (primBe σ x j)‖ +
    AK * (1 + anchorNorm n G (primAl σ x j) (primBe σ x j)) with hN
  have hN0 : ∀ j, 0 ≤ N j := fun j => add_nonneg (norm_nonneg _)
    (mul_nonneg hAK0 (by linarith [prim_anchorNorm_nonneg n G (primAl σ x j) (primBe σ x j)]))
  have hYN : ∀ j, ‖Y j‖ ≤ N j := by
    intro j
    simp only [hY, hN, prim_norm_sgnMat]
    have hA := prim_anchorNorm_nonneg n G (primAl σ x j) (primBe σ x j)
    have := mul_nonneg hAK0
      (show (0 : ℝ) ≤ 1 + anchorNorm n G (primAl σ x j) (primBe σ x j) by linarith)
    linarith
  have hZN : ∀ j, ‖Z j‖ ≤ N j := by
    intro j
    simp only [hZ, hN, prim_norm_sgnMat]
    have := prim_interp_norm_le hκ hκ2 hE n hL2 G (primAl σ x j) (primBe σ x j)
    linarith [norm_nonneg (blockOf G (primAl σ x j) (primBe σ x j))]
  have ht := prim_tele hW k 1 Y Z N hN0 hYN hZN
  rw [one_mul] at ht
  have hdiff : ∀ i, nhs W (Y i - Z i) ≤ primErr Chs n E z V (primAl σ x i) (primBe σ x i) *
      (1 + interpEnv n G (primAl σ x i) (primBe σ x i)) := by
    intro i
    simp only [hY, hZ, prim_sgn_sub, prim_nhs_sgn]
    exact hhs W L n E z V hW hL hn hE hV hz (primAl σ x i) (primBe σ x i)
  have e : (W : ℂ)⁻¹ * Matrix.trace (List.ofFn Y).prod -
      (W : ℂ)⁻¹ * Matrix.trace (List.ofFn Z).prod =
      (W : ℂ)⁻¹ * Matrix.trace ((List.ofFn Y).prod - (List.ofFn Z).prod) := by
    rw [Matrix.trace_sub, mul_sub]
  change ‖(W : ℂ)⁻¹ * Matrix.trace (List.ofFn Y).prod -
      (W : ℂ)⁻¹ * Matrix.trace (List.ofFn Z).prod‖ ≤ _
  rw [e]
  refine ht.trans ?_
  have h1 := prim_norm_one_le (Fin W)
  have hP0 : 0 ≤ ∏ j, (1 + N j) := Finset.prod_nonneg fun j _ => by linarith [hN0 j]
  have hS0 : 0 ≤ ∑ i, nhs W (Y i - Z i) := Finset.sum_nonneg fun i _ => prim_nhs_nonneg W _
  calc ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ * ((∑ i, nhs W (Y i - Z i)) * ∏ j, (1 + N j))
      ≤ 1 * ((∑ i, nhs W (Y i - Z i)) * ∏ j, (1 + N j)) := by gcongr
    _ = (∑ i, nhs W (Y i - Z i)) * ∏ j, (1 + N j) := one_mul _
    _ ≤ (∑ i, primErr Chs n E z V (primAl σ x i) (primBe σ x i) *
          (1 + interpEnv n G (primAl σ x i) (primBe σ x i))) * ∏ j, (1 + N j) :=
        mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun i _ => hdiff i) hP0
    _ = _ := by rw [Finset.sum_mul]; rfl

/-- Moment bound for the interpolation error factor. -/
private theorem prim_mom_err {W L n P : ℕ} (hP : 1 ≤ P) (hn : 1 ≤ n) {g t E Chs A : ℝ}
    (hChs : 0 ≤ Chs) (hA : 0 ≤ A) {z : ℂ}
    (hPre : ∀ z' : ℂ, (z' = z ∨ z' = starRingEnd ℂ z) → ∀ (b : Fin L) (j : ℕ), j ≤ n →
      PrimMom (μ W L) P (fun ω => prodErr (nhs W) E z' (primV g W L t ω) b j) A)
    (α β : Fin L) :
    PrimMom (μ W L) P (fun ω => primErr Chs n E z (primV g W L t ω) α β) (40 * Chs * A) := by
  have hI : ∀ z' : ℂ, (z' = z ∨ z' = starRingEnd ℂ z) → ∀ a' b' : Fin L,
      PrimMom (μ W L) P (fun ω => interpErr (nhs W) n E z' (primV g W L t ω) a' b')
        (4 * A) := by
    intro z' hz' a' b'
    have hm := Nat.mod_lt a'.val (by omega : 0 < n)
    have h1 := hPre z' hz' (cellStart n a') (a'.val % n) hm.le
    simp only [interpErr]
    exact primMom_mono (by positivity) (le_of_eq (by ring : 2 * (A + A) = 4 * A))
      (primMom_add hP hA hA h1 (prim_mom_ite hA
        (hPre z' hz' (finRotate L b') (a'.val % n - b'.val % n - 1) (by omega))))
  have h := primMom_add hP (by positivity) (by positivity)
    (primMom_add hP (by positivity) (by positivity) (hI z (Or.inl rfl) α β)
      (hI _ (Or.inr rfl) β (cellStart n α))) (hI _ (Or.inr rfl) β (cellPrev n α))
  have h' := primMom_smul hChs h
  exact primMom_mono (by positivity) (le_of_eq (by ring)) h'

/-- Moment bound for the anchor norm. -/
private theorem prim_mom_anchor {W L n P : ℕ} (hP : 1 ≤ P) {A : ℝ} (hA : 0 ≤ A)
    {G : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hB : ∀ α β, PrimMom (μ W L) P (fun ω => ‖blockOf (G ω) α β‖) A) (α β : Fin L) :
    PrimMom (μ W L) P (fun ω => anchorNorm n (G ω) α β) (4 * A) := by
  have h := primMom_max hP (by positivity) (by positivity)
    (primMom_max hP hA hA (hB (cellStart n α) (cellStart n β)) (hB (cellStart n α) (cellPrev n β)))
    (primMom_max hP hA hA (hB (cellPrev n α) (cellStart n β)) (hB (cellPrev n α) (cellPrev n β)))
  exact primMom_mono (by positivity) (le_of_eq (by ring)) h

/-- Moment bound for `1 + interpEnv`. -/
private theorem prim_mom_env {W L n P : ℕ} (hP : 1 ≤ P) {A : ℝ} (hA : 0 ≤ A)
    {G : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hB : ∀ α β, PrimMom (μ W L) P (fun ω => ‖blockOf (G ω) α β‖) A) (α β : Fin L) :
    PrimMom (μ W L) P (fun ω => 1 + interpEnv n (G ω) α β) (2 * (1 + 6 * A)) := by
  have h := primMom_max hP (by positivity) (by positivity) (prim_mom_anchor (n := n) hP hA hB α β)
    (primMom_max hP hA hA (hB (cellStart n α) β) (hB (cellPrev n α) β))
  have h' := primMom_add hP zero_le_one (by positivity) (primMom_const zero_le_one P) h
  exact primMom_mono (by positivity) (le_of_eq (by ring)) h'

/-- Moment bound for the factor bound `primN`. -/
private theorem prim_mom_N {W L n P : ℕ} (hP : 1 ≤ P) {A AK : ℝ} (hA : 0 ≤ A) (hAK : 0 ≤ AK)
    {G : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hB : ∀ α β, PrimMom (μ W L) P (fun ω => ‖blockOf (G ω) α β‖) A) (α β : Fin L) :
    PrimMom (μ W L) P (fun ω => primN AK n (G ω) α β)
      (2 * ((1 + AK) + 2 * (A + AK * (4 * A)))) := by
  have h := primMom_add hP (by positivity) (by positivity)
    (primMom_const (by positivity : (0 : ℝ) ≤ 1 + AK) P)
    (primMom_add hP hA (by positivity) (hB α β)
      (primMom_smul hAK (prim_mom_anchor (n := n) hP hA hB α β)))
  have e : (fun ω => primN AK n (G ω) α β) = fun ω =>
      (1 + AK) + (‖blockOf (G ω) α β‖ + AK * anchorNorm n (G ω) α β) := by
    funext ω; simp only [primN]; ring
  rw [e]; exact h

/-- The auxiliary loops at one width: with moment bounds `A_G` for the blocks of the resolvent and
`A_P` for the transfer-product errors, the normalized expected loop is within
`k (k + 3) · 40 C A_P · Λ^{k+1}` of `𝒱`, `Λ = 2((1 + A) + 2(A_G + 4 A A_G)) + 2(1 + 6 A_G)`. -/
private theorem prim_core {κ Chs : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (hChs : 0 < Chs)
    (hhs : ∀ (W L n : ℕ) (E : ℝ) (z : ℂ) (V : Fin L → Matrix (Fin W) (Fin W) ℂ),
      1 ≤ W → 3 ≤ L → 1 ≤ n → |E| ≤ 2 - κ → (∀ r, (V r).IsHermitian) → z.im ≠ 0 →
      let G := resolventMat (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ) + blockDiagOp V) z
      ∀ a b : Fin L,
        nhs W (blockOf G a b - interpBlock n E G a b) ≤
          Chs * (interpErr (nhs W) n E z V a b +
              interpErr (nhs W) n E (starRingEnd ℂ z) V b (cellStart n a) +
              interpErr (nhs W) n E (starRingEnd ℂ z) V b (cellPrev n a)) *
            (1 + interpEnv n G a b))
    {W L n k' P : ℕ} (hW : 1 ≤ W) (hL : 3 ≤ L) (hn : 1 ≤ n) (hP : k' + 3 ≤ P) {E g t : ℝ}
    (hE : |E| ≤ 2 - κ) {z : ℂ} (hz : 0 < z.im) {AG AP : ℝ} (hAG : 0 ≤ AG) (hAP : 0 < AP)
    (hB : ∀ α β, PrimMom (μ W L) P
      (fun ω => ‖blockOf (resolventMat (primH g W L t ω) z) α β‖) AG)
    (hPre : ∀ z' : ℂ, (z' = z ∨ z' = starRingEnd ℂ z) → ∀ (b : Fin L) (j : ℕ), j ≤ n →
      PrimMom (μ W L) P (fun ω => prodErr (nhs W) E z' (primV g W L t ω) b j) AP)
    (a : Fin (k' + 1) → Fin L) (σ : Fin (k' + 1) → Bool) :
    ∃ v ∈ loopSpace n E a, ∀ x : CellProd n a,
      ‖(W : ℂ) ^ (k' + 1 - 1) * ∫ ω, loopTr (resolventMat (primH g W L t ω) z) x.1 σ ∂(μ W L) -
          v x‖ ≤
        ((k' + 1 : ℕ) : ℝ) * (((k' + 3 : ℕ) : ℝ) + 1) * (40 * Chs * AP) *
          (2 * ((1 + (6 * (2 / κ) ^ 2 + 2 / κ)) + 2 * (AG + (6 * (2 / κ) ^ 2 + 2 / κ) *
            (4 * AG))) + 2 * (1 + 6 * AG)) ^ (k' + 2) := by
  have hP1 : 1 ≤ P := by omega
  set AK : ℝ := 6 * (2 / κ) ^ 2 + 2 / κ with hAK
  have hAK0 : 0 ≤ AK := by positivity
  set Λ' : ℝ := 2 * ((1 + AK) + 2 * (AG + AK * (4 * AG))) + 2 * (1 + 6 * AG) with hΛ'
  have hΛ'0 : 0 < Λ' := by positivity
  set G : Ω W L → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ := fun ω =>
    resolventMat (primH g W L t ω) z with hGdef
  have hGc : Continuous G := prim_cont_G g W L t hz.ne'
  have hGn : ∀ ω, ‖G ω‖ ≤ (z.im)⁻¹ := fun ω =>
    norm_resolventMat_le (primH_herm g W L t ω) hz (le_abs_self _)
  have hη0 : 0 ≤ (z.im)⁻¹ := inv_nonneg.mpr hz.le
  -- the coefficients of the spanning functions are integrable
  have hc_int : ∀ w : Fin (k' + 1) → (Bool × Bool) ⊕ Bool,
      Integrable (fun ω => primCoef n (G ω) σ a w) (μ W L) := by
    intro w
    have hcont : Continuous fun ω => primCoef n (G ω) σ a w := by
      unfold primCoef
      exact continuous_const.mul ((prim_cont_list_prod _ _ fun i =>
        prim_cont_mat hGc _ _ _ _).matrix_trace)
    refine Integrable.of_bound hcont.aestronglyMeasurable ((max 1 (z.im)⁻¹) ^ (k' + 1))
      (Eventually.of_forall fun ω => ?_)
    unfold primCoef
    refine (prim_trace_le_norm hW _).trans ?_
    have h := prim_list_prod_norm_le (k' + 1) (fun i => primMat (G ω) (σ i)
      (cellStart n (a ((finRotate (k' + 1)).symm i))) (cellStart n (a i)) (w i))
      (fun _ => max 1 (z.im)⁻¹) (fun _ => le_trans zero_le_one (le_max_left _ _))
      (fun i => (prim_mat_norm_le _ _ _ _ _).trans (max_le_max le_rfl (hGn ω)))
    simpa using h
  set v : CellProd n a → ℂ := fun x =>
    ∑ w, (∫ ω, primCoef n (G ω) σ a w ∂(μ W L)) * primBas n E w x.1 with hv
  refine ⟨v, prim_mem_loopSpace n E a _, fun x => ?_⟩
  set fY : Ω W L → ℂ := fun ω => (W : ℂ)⁻¹ * Matrix.trace (List.ofFn fun i =>
    sgnMat (blockOf (G ω) (primAl σ x.1 i) (primBe σ x.1 i)) (σ i)).prod with hfY
  set fZ : Ω W L → ℂ := fun ω => (W : ℂ)⁻¹ * Matrix.trace (List.ofFn fun i =>
    sgnMat (interpBlock n E (G ω) (primAl σ x.1 i) (primBe σ x.1 i)) (σ i)).prod with hfZ
  have hexp : fZ = fun ω => ∑ w, primCoef n (G ω) σ a w * primBas n E w x.1 := by
    funext ω
    exact prim_interp_expand (by omega) n E (G ω) σ a x.1 x.2
  have hfZ_int : Integrable fZ (μ W L) := by
    rw [hexp]
    exact integrable_finsetSum _ fun w _ => (hc_int w).mul_const _
  have hfY_int : Integrable fY (μ W L) := by
    have hcont : Continuous fY :=
      continuous_const.mul ((prim_cont_list_prod _ _ fun i =>
        prim_cont_sgn (prim_cont_blockOf hGc _ _) _).matrix_trace)
    refine Integrable.of_bound hcont.aestronglyMeasurable (((z.im)⁻¹) ^ (k' + 1))
      (Eventually.of_forall fun ω => ?_)
    refine (prim_trace_le_norm hW _).trans ?_
    have h := prim_list_prod_norm_le (k' + 1) (fun i =>
      sgnMat (blockOf (G ω) (primAl σ x.1 i) (primBe σ x.1 i)) (σ i)) (fun _ => (z.im)⁻¹)
      (fun _ => hη0) (fun i => by
        rw [prim_norm_sgnMat]; exact (prim_blockOf_norm_le _ _ _).trans (hGn ω))
    simpa using h
  have hLHS : (W : ℂ) ^ (k' + 1 - 1) * ∫ ω, loopTr (G ω) x.1 σ ∂(μ W L) = ∫ ω, fY ω ∂(μ W L) := by
    rw [← integral_const_mul]
    congr 1
    funext ω
    exact prim_loop_block hW (by omega) (G ω) x.1 σ
  have hRHS : v x = ∫ ω, fZ ω ∂(μ W L) := by
    rw [hexp, integral_finsetSum _ fun w _ => (hc_int w).mul_const _]
    simp only [hv]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [integral_mul_const]
  change ‖(W : ℂ) ^ (k' + 1 - 1) * ∫ ω, loopTr (G ω) x.1 σ ∂(μ W L) - v x‖ ≤ _
  rw [hLHS, hRHS, ← integral_sub hfY_int hfZ_int]
  -- the factors
  set α : Fin (k' + 1) → Fin L := primAl σ x.1 with hα
  set β : Fin (k' + 1) → Fin L := primBe σ x.1 with hβ
  set F : Fin (k' + 1) → Fin (k' + 3) → Ω W L → ℝ := fun i =>
    Fin.cons (fun ω => primErr Chs n E z (primV g W L t ω) (α i) (β i))
      (Fin.cons (fun ω => 1 + interpEnv n (G ω) (α i) (β i))
        (fun j ω => primN AK n (G ω) (α j) (β j))) with hF
  set A : Fin (k' + 3) → ℝ := Fin.cons (40 * Chs * AP) (fun _ => Λ') with hA
  have hApos : ∀ l, 0 < A l := by
    intro l
    refine Fin.cases ?_ (fun l => ?_) l
    · simp only [hA, Fin.cons_zero]; positivity
    · simp only [hA, Fin.cons_succ]; exact hΛ'0
  have hFm : ∀ i l, PrimMom (μ W L) P (F i l) (A l) := by
    intro i l
    refine Fin.cases ?_ (fun l => ?_) l
    · simp only [hF, hA, Fin.cons_zero]
      exact prim_mom_err hP1 hn hChs.le hAP.le hPre (α i) (β i)
    · refine Fin.cases ?_ (fun j => ?_) l
      · simp only [hF, hA, Fin.cons_zero, Fin.cons_succ]
        refine primMom_mono (by positivity) ?_ (prim_mom_env hP1 hAG hB (α i) (β i))
        have : 0 ≤ 2 * ((1 + AK) + 2 * (AG + AK * (4 * AG))) := by positivity
        linarith
      · simp only [hF, hA, Fin.cons_succ]
        refine primMom_mono (by positivity) ?_ (prim_mom_N hP1 hAG hAK0 hB (α j) (β j))
        have : 0 ≤ 2 * (1 + 6 * AG) := by positivity
        linarith
  have hprod : ∀ i, Integrable (fun ω => ∏ l, F i l ω) (μ W L) ∧
      ∫ ω, ∏ l, F i l ω ∂(μ W L) ≤ (((k' + 3 : ℕ) : ℝ) + 1) * ∏ l, A l :=
    fun i => primMom_prod hP (F i) A hApos (hFm i)
  have hprodA : ∏ l, A l = 40 * Chs * AP * Λ' ^ (k' + 2) := by
    rw [Fin.prod_univ_succ]
    simp [hA]
  have hRint : Integrable (fun ω => ∑ i, ∏ l, F i l ω) (μ W L) :=
    integrable_finsetSum _ fun i _ => (hprod i).1
  have hpt : ∀ ω, ‖fY ω - fZ ω‖ ≤ ∑ i, ∏ l, F i l ω := by
    intro ω
    have h := prim_pointwise hκ hκ2 hhs hW hL hn hE hz.ne' (primV g W L t ω)
      (primV_herm g W L t ω) x.1 σ
    refine h.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hF]
    conv_rhs => rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, mul_assoc]
    rfl
  refine (norm_integral_le_of_norm_le hRint (Eventually.of_forall hpt)).trans ?_
  rw [integral_finsetSum _ fun i _ => (hprod i).1]
  calc ∑ i, ∫ ω, ∏ l, F i l ω ∂(μ W L)
      ≤ ∑ _i : Fin (k' + 1), (((k' + 3 : ℕ) : ℝ) + 1) * ∏ l, A l :=
        Finset.sum_le_sum fun i _ => (hprod i).2
    _ = _ := by
        rw [hprodA, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The window facts at the characteristic parameter `z_t` for `g ≥ C_κ`, `‖m‖ ≤ C`,
`Im m ≥ C⁻¹`: `|Re z_t| ≤ 2 - κ/2`, `0 < Im z_t ≤ C/g²`, `g² Im z_t ≥ (1 - t)/C`,
`‖z_t - E‖ ≤ C/g²`. -/
private theorem prim_window {κ C g E t : ℝ} {m : ℂ} (hκ : 0 < κ) (hC0 : 0 < C) (hg1 : 1 ≤ g)
    (hgC : 2 * C / κ ≤ g ^ 2) (hE : |E| ≤ 2 - κ) (hmC : ‖m‖ ≤ C) (hmim : C⁻¹ ≤ m.im)
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    |(zChar g E m t).re| ≤ 2 - κ / 2 ∧ 0 < (zChar g E m t).im ∧
      (zChar g E m t).im ≤ C / g ^ 2 ∧ (1 - t) / C ≤ g ^ 2 * (zChar g E m t).im ∧
      ‖zChar g E m t - E‖ ≤ C / g ^ 2 := by
  have hg2 : 0 < g ^ 2 := by positivity
  have hγ : gammaG g = (g ^ 2)⁻¹ := by unfold gammaG; rw [max_eq_right hg1]
  have hγ0 : 0 < (g ^ 2)⁻¹ := inv_pos.mpr hg2
  have h1t : 0 < 1 - t := by linarith
  have h1t1 : 1 - t ≤ 1 := by linarith
  have hmim0 : 0 < m.im := lt_of_lt_of_le (inv_pos.mpr hC0) hmim
  have hmimC : m.im ≤ C := (Complex.im_le_norm m).trans hmC
  have hzim : (zChar g E m t).im = (1 - t) * (g ^ 2)⁻¹ * m.im := by
    rw [← hγ]; simp [zChar, Complex.add_im, Complex.mul_im]
  have hzre : (zChar g E m t).re = E + (1 - t) * (g ^ 2)⁻¹ * m.re := by
    rw [← hγ]; simp [zChar, Complex.add_re, Complex.mul_re]
  have hCg : C / g ^ 2 ≤ κ / 2 := by
    rw [div_le_iff₀ hg2]
    have e : 2 * C / κ * κ = 2 * C := by field_simp
    have := mul_le_mul_of_nonneg_right hgC (le_of_lt (half_pos hκ))
    calc C = 2 * C / κ * (κ / 2) := by field_simp
      _ ≤ g ^ 2 * (κ / 2) := this
      _ = κ / 2 * g ^ 2 := mul_comm _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hzre]
    have h2 : |(1 - t) * (g ^ 2)⁻¹ * m.re| ≤ C / g ^ 2 := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg h1t.le hγ0.le)]
      have h3 := (Complex.abs_re_le_norm m).trans hmC
      calc (1 - t) * (g ^ 2)⁻¹ * |m.re| ≤ 1 * (g ^ 2)⁻¹ * C := by gcongr
        _ = C / g ^ 2 := by ring
    calc |E + (1 - t) * (g ^ 2)⁻¹ * m.re| ≤ |E| + |(1 - t) * (g ^ 2)⁻¹ * m.re| :=
          abs_add_le _ _
      _ ≤ 2 - κ / 2 := by linarith
  · rw [hzim]; positivity
  · rw [hzim]
    calc (1 - t) * (g ^ 2)⁻¹ * m.im ≤ 1 * (g ^ 2)⁻¹ * C := by gcongr
      _ = C / g ^ 2 := by ring
  · rw [hzim]
    have e : g ^ 2 * ((1 - t) * (g ^ 2)⁻¹ * m.im) = (1 - t) * m.im := by field_simp
    rw [e, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hmim h1t.le
  · have e : zChar g E m t - E = (((1 - t) * (g ^ 2)⁻¹ : ℝ) : ℂ) * m := by
      rw [← hγ]; simp [zChar]
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg h1t.le hγ0.le)]
    calc (1 - t) * (g ^ 2)⁻¹ * ‖m‖ ≤ 1 * (g ^ 2)⁻¹ * C := by gcongr
      _ = C / g ^ 2 := by ring

/-- Lemma 7.5 [uvc:lem:space], the uniform interpolation error before the limit. -/
private theorem prim_aux_main (κ C : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hC : 1 ≤ C) (k : ℕ)
    (hk : 1 ≤ k) :
    ∃ Cκ c₀ C' : ℝ, 1 ≤ Cκ ∧ 0 < c₀ ∧ 0 < C' ∧ ∀ g : ℝ, Cκ ≤ g → ∀ L : ℕ, 4 * g ^ 2 ≤ L →
      ∀ E : ℝ, |E| ≤ 2 - κ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m → ‖m‖ ≤ C →
      C⁻¹ ≤ m.im → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ c₀ * g ^ 2 → ∀ t : ℝ, 0 ≤ t → t < 1 →
      ∀ (a : Fin k → Fin L) (σ : Fin k → Bool), ∃ Wt₀ : ℕ, ∀ Wt : ℕ, Wt₀ ≤ Wt →
        ∃ v ∈ loopSpace n E a, ∀ x : CellProd n a,
          ‖auxLoop g Wt L E m t k x.1 σ - v x‖ ≤
            C' * Real.sqrt (n / g ^ 2) * (1 - t) ^ (-C') := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨Chs, hChs, hhs⟩ := green_interp_hs κ hκ hκ2
  obtain ⟨Cpm, cpm, hCpm, hcpm, hpm⟩ := prefix_moments κ (k' + 3) hκ hκ2 (by omega)
  have hC0 : 0 < C := by linarith
  obtain ⟨Crm, hCrm, hrm⟩ := resolvent_moments (κ / 2) ((2 * (k' + 3) : ℕ) : ℝ) C
    (by positivity) (by positivity) hC0
  set AK : ℝ := 6 * (2 / κ) ^ 2 + 2 / κ with hAK
  have hAK0 : 0 ≤ AK := by positivity
  set Λ₁ : ℝ := max 1 Crm * C with hΛ₁
  have hΛ₁0 : 0 < Λ₁ := mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) hC0
  set Λ₂ : ℝ := max 1 (Cpm * (1 + C ^ (2 * (k' + 3)))) with hΛ₂
  have hΛ₂1 : 1 ≤ Λ₂ := le_max_left _ _
  set Λ : ℝ := 2 * ((1 + AK) + 2 * (Λ₁ + AK * (4 * Λ₁))) + 2 * (1 + 6 * Λ₁) with hΛ
  have hΛ0 : 0 < Λ := by positivity
  set Ctot : ℝ := ((k' + 1 : ℕ) : ℝ) * (((k' + 3 : ℕ) : ℝ) + 1) * (40 * Chs * Λ₂) *
    Λ ^ (k' + 2) with hCtot
  have hCtot0 : 0 ≤ Ctot := by positivity
  set C' : ℝ := max ((k' + 2 : ℕ) : ℝ) Ctot with hC'
  have hC'0 : 0 < C' := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨max (max 1 (2 / Real.sqrt (κ / 2))) (Real.sqrt (2 * C / κ)), min (cpm / C) (1 / 4), C',
    le_trans (le_max_left _ _) (le_max_left _ _), lt_min (by positivity) (by norm_num), hC'0, ?_⟩
  intro g hg L hL E hE m hm hmC hmim n hn hnc t ht0 ht1 a σ
  refine ⟨8 * (k' + 3), fun Wt hWt => ?_⟩
  have hg1 : 1 ≤ g := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hg
  have hg0 : 0 < g := by linarith
  have hg2 : 0 < g ^ 2 := by positivity
  have hgκ : 2 / Real.sqrt (κ / 2) ≤ g :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hg
  have hgC : 2 * C / κ ≤ g ^ 2 := by
    have h1 : Real.sqrt (2 * C / κ) ≤ g := le_trans (le_max_right _ _) hg
    have h2 := Real.sq_sqrt (show 0 ≤ 2 * C / κ by positivity)
    rw [← h2]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  have hγ : gammaG g = (g ^ 2)⁻¹ := by unfold gammaG; rw [max_eq_right hg1]
  have hL4 : (4 : ℝ) ≤ L := by
    have : (1 : ℝ) ≤ g ^ 2 := one_le_pow₀ hg1
    linarith
  have hL3 : 3 ≤ L := by exact_mod_cast (show (3 : ℝ) ≤ L by linarith)
  have hW1 : 1 ≤ Wt := by omega
  have hWP : 4 * (((2 * (k' + 3) : ℕ) : ℝ)) ≤ Wt := by
    have : 4 * (2 * (k' + 3)) ≤ Wt := by omega
    exact_mod_cast this
  have h1t : 0 < 1 - t := by linarith
  have h1t1 : 1 - t ≤ 1 := by linarith
  obtain ⟨hzre, hη, hηC, hgη, hzE⟩ := prim_window hκ hC0 hg1 hgC hE hmC hmim ht0 ht1
  set z : ℂ := zChar g E m t with hz
  have hzE' : ‖starRingEnd ℂ z - E‖ ≤ C / g ^ 2 := by
    have e : starRingEnd ℂ z - E = starRingEnd ℂ (z - E) := by simp
    rw [e, Complex.norm_conj]; exact hzE
  have hnr : (n : ℝ) / g ^ 2 ≤ min (cpm / C) (1 / 4) := by rw [div_le_iff₀ hg2]; exact hnc
  have hnr1 : (n : ℝ) / g ^ 2 ≤ 1 / 4 := hnr.trans (min_le_right _ _)
  have hnr2 : (n : ℝ) / g ^ 2 ≤ cpm / C := hnr.trans (min_le_left _ _)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 ≤ (n : ℝ) / g ^ 2 := by positivity
  have hnL : n ≤ L := by
    have h1 : (n : ℝ) ≤ g ^ 2 / 4 := by
      have := (div_le_iff₀ hg2).mp hnr1; linarith
    have : (n : ℝ) ≤ L := by linarith
    exact_mod_cast this
  have hns : (n : ℝ) * (t * gammaG g) ≤ cpm := by
    rw [hγ]
    have e : (n : ℝ) * (t * (g ^ 2)⁻¹) = t * ((n : ℝ) / g ^ 2) := by field_simp
    rw [e]
    have h5 : cpm / C ≤ cpm := div_le_self hcpm.le hC
    calc t * ((n : ℝ) / g ^ 2) ≤ 1 * (cpm / C) := by gcongr
      _ ≤ cpm := by linarith
  have hnz : ∀ z' : ℂ, ‖z' - E‖ ≤ C / g ^ 2 → (n : ℝ) * ‖z' - E‖ ≤ cpm := by
    intro z' hz'
    calc (n : ℝ) * ‖z' - E‖ ≤ n * (C / g ^ 2) := mul_le_mul_of_nonneg_left hz' hn0.le
      _ = C * ((n : ℝ) / g ^ 2) := by ring
      _ ≤ C * (cpm / C) := mul_le_mul_of_nonneg_left hnr2 hC0.le
      _ = cpm := by field_simp
  set τ : ℝ := (1 - t)⁻¹ with hτ
  have hτ1 : 1 ≤ τ := one_le_inv₀ h1t |>.mpr h1t1
  set r : ℝ := Real.sqrt ((n : ℝ) / g ^ 2) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by positivity)
  -- the moment bounds
  have hB : ∀ α β, PrimMom (μ Wt L) (2 * (k' + 3))
      (fun ω => ‖blockOf (resolventMat (primH g Wt L t ω) z) α β‖) (Λ₁ * τ) := by
    intro α β
    have h := prim_mom_block (by omega) hrm hWP hg1 hgκ hL ht0 ht1.le hzre hη hηC
      (div_pos h1t hC0) hgη α β
    refine primMom_mono (by positivity) (le_of_eq ?_) h
    rw [inv_div, hΛ₁, hτ]; ring
  have hPre : ∀ z' : ℂ, (z' = z ∨ z' = starRingEnd ℂ z) → ∀ (b : Fin L) (j : ℕ), j ≤ n →
      PrimMom (μ Wt L) (2 * (k' + 3)) (fun ω => prodErr (nhs Wt) E z' (primV g Wt L t ω) b j)
        (Λ₂ * r) := by
    intro z' hz' b j hj
    have hz'E : ‖z' - E‖ ≤ C / g ^ 2 := by rcases hz' with rfl | rfl <;> assumption
    refine prim_mom_pref hpm hW1 hE ht0 hnL hj hns (hnz z' hz'E) b ?_
    set x : ℝ := (n : ℝ) / g ^ 2 with hx
    have hx1 : x ≤ 1 := by linarith
    have ha : (n : ℝ) * (t * gammaG g) ≤ x := by
      rw [hγ, hx]
      have e : (n : ℝ) * (t * (g ^ 2)⁻¹) = t * ((n : ℝ) / g ^ 2) := by field_simp
      rw [e]
      calc t * ((n : ℝ) / g ^ 2) ≤ 1 * ((n : ℝ) / g ^ 2) := by gcongr
        _ = _ := one_mul _
    have hb : (n : ℝ) * ‖z' - E‖ ≤ C * x := by
      calc (n : ℝ) * ‖z' - E‖ ≤ n * (C / g ^ 2) := mul_le_mul_of_nonneg_left hz'E hn0.le
        _ = C * x := by rw [hx]; ring
    have hsum : ((n : ℝ) * (t * gammaG g)) ^ (k' + 3) + ((n : ℝ) * ‖z' - E‖) ^ (2 * (k' + 3)) ≤
        (1 + C ^ (2 * (k' + 3))) * x ^ (k' + 3) := by
      have hγ0 : 0 ≤ gammaG g := by unfold gammaG; positivity
      have h1 : ((n : ℝ) * (t * gammaG g)) ^ (k' + 3) ≤ x ^ (k' + 3) :=
        pow_le_pow_left₀ (mul_nonneg hn0.le (mul_nonneg ht0 hγ0)) ha _
      have h2 : ((n : ℝ) * ‖z' - E‖) ^ (2 * (k' + 3)) ≤ (C * x) ^ (2 * (k' + 3)) :=
        pow_le_pow_left₀ (by positivity) hb _
      have h3 : (C * x) ^ (2 * (k' + 3)) ≤ C ^ (2 * (k' + 3)) * x ^ (k' + 3) := by
        rw [mul_pow, two_mul, pow_add x]
        have h6 : x ^ (k' + 3) ≤ 1 := pow_le_one₀ hx0 hx1
        have h4 : 0 ≤ x ^ (k' + 3) := pow_nonneg hx0 _
        have h5 : 0 ≤ C ^ (k' + 3 + (k' + 3)) := by positivity
        refine mul_le_mul_of_nonneg_left ?_ h5
        calc x ^ (k' + 3) * x ^ (k' + 3) ≤ x ^ (k' + 3) * 1 :=
              mul_le_mul_of_nonneg_left h6 h4
          _ = x ^ (k' + 3) := mul_one _
      calc ((n : ℝ) * (t * gammaG g)) ^ (k' + 3) + ((n : ℝ) * ‖z' - E‖) ^ (2 * (k' + 3))
          ≤ x ^ (k' + 3) + C ^ (2 * (k' + 3)) * x ^ (k' + 3) := add_le_add h1 (h2.trans h3)
        _ = _ := by ring
    have hr2 : r ^ (2 * (k' + 3)) = x ^ (k' + 3) := by
      rw [pow_mul, hr, Real.sq_sqrt hx0]
    calc Cpm * (((n : ℝ) * (t * gammaG g)) ^ (k' + 3) + ((n : ℝ) * ‖z' - E‖) ^ (2 * (k' + 3)))
        ≤ Cpm * ((1 + C ^ (2 * (k' + 3))) * x ^ (k' + 3)) :=
          mul_le_mul_of_nonneg_left hsum hCpm.le
      _ = (Cpm * (1 + C ^ (2 * (k' + 3)))) * x ^ (k' + 3) := by ring
      _ ≤ Λ₂ * x ^ (k' + 3) := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      _ ≤ Λ₂ ^ (2 * (k' + 3)) * x ^ (k' + 3) :=
          mul_le_mul_of_nonneg_right (le_self_pow₀ hΛ₂1 (by omega)) (by positivity)
      _ = (Λ₂ * r) ^ (2 * (k' + 3)) := by rw [mul_pow, hr2]
  obtain ⟨v, hv, hvx⟩ := prim_core hκ hκ2 hChs hhs hW1 hL3 hn (by omega : k' + 3 ≤ 2 * (k' + 3))
    hE hη (by positivity : (0 : ℝ) ≤ Λ₁ * τ) (by positivity : (0 : ℝ) < Λ₂ * r) hB hPre a σ
  refine ⟨v, hv, fun x => ?_⟩
  have hx := hvx x
  have hA : auxLoop g Wt L E m t (k' + 1) x.1 σ = (Wt : ℂ) ^ (k' + 1 - 1) *
      ∫ ω, loopTr (resolventMat (primH g Wt L t ω) z) x.1 σ ∂(μ Wt L) := by
    unfold auxLoop
    congr 2
    funext ω
    rw [prim_auxG_eq hg1]
  rw [hA]
  refine hx.trans ?_
  -- final constants
  have hΛ' : 2 * ((1 + AK) + 2 * (Λ₁ * τ + AK * (4 * (Λ₁ * τ)))) + 2 * (1 + 6 * (Λ₁ * τ)) ≤
      Λ * τ := by
    have e : Λ * τ - (2 * ((1 + AK) + 2 * (Λ₁ * τ + AK * (4 * (Λ₁ * τ)))) +
        2 * (1 + 6 * (Λ₁ * τ))) = (2 * (1 + AK) + 2) * (τ - 1) := by rw [hΛ]; ring
    have h0 : 0 ≤ (2 * (1 + AK) + 2) * (τ - 1) := mul_nonneg (by positivity) (by linarith)
    linarith
  have hpow : (2 * ((1 + AK) + 2 * (Λ₁ * τ + AK * (4 * (Λ₁ * τ)))) +
      2 * (1 + 6 * (Λ₁ * τ))) ^ (k' + 2) ≤ (Λ * τ) ^ (k' + 2) :=
    pow_le_pow_left₀ (by positivity) hΛ' _
  have hτpow : τ ^ (k' + 2) ≤ (1 - t) ^ (-C') := by
    rw [hτ, inv_pow, Real.rpow_neg h1t.le]
    refine inv_anti₀ (Real.rpow_pos_of_pos h1t _) ?_
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge h1t h1t1 (le_max_left _ _)
  calc ((k' + 1 : ℕ) : ℝ) * (((k' + 3 : ℕ) : ℝ) + 1) * (40 * Chs * (Λ₂ * r)) *
        (2 * ((1 + AK) + 2 * (Λ₁ * τ + AK * (4 * (Λ₁ * τ)))) + 2 * (1 + 6 * (Λ₁ * τ))) ^ (k' + 2)
      ≤ ((k' + 1 : ℕ) : ℝ) * (((k' + 3 : ℕ) : ℝ) + 1) * (40 * Chs * (Λ₂ * r)) *
        (Λ * τ) ^ (k' + 2) := by gcongr
    _ = Ctot * r * τ ^ (k' + 2) := by rw [hCtot, mul_pow]; ring
    _ ≤ C' * r * (1 - t) ^ (-C') := by
        gcongr
        exact le_max_right _ _

/-- The proof of `primLoopF_dist_space`: the limit `W̃ → ∞` of the prelimit bound through
Lemma 5.4 [uvc:lem:orbital-limit]; the common space is finite-dimensional, hence closed, so the
distance is attained. -/
private theorem prim_lim_main (κ C : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hC : 1 ≤ C) (k : ℕ)
    (hk : 1 ≤ k) :
    ∃ Cκ c₀ C' : ℝ, 1 ≤ Cκ ∧ 0 < c₀ ∧ 0 < C' ∧ ∀ g : ℝ, Cκ ≤ g → ∀ L : ℕ, 4 * g ^ 2 ≤ L →
      ∀ E : ℝ, |E| ≤ 2 - κ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m → ‖m‖ ≤ C →
      C⁻¹ ≤ m.im → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ c₀ * g ^ 2 → ∀ t : ℝ, 0 ≤ t → t < 1 →
      ∀ (a : Fin k → Fin L) (σ : Fin k → Bool), ∃ v ∈ loopSpace n E a, ∀ x : CellProd n a,
        ‖primLoopF g L E m t x.1 σ - v x‖ ≤ C' * Real.sqrt (n / g ^ 2) * (1 - t) ^ (-C') := by
  obtain ⟨Cκ, c₀, C', hCκ, hc₀, hC', h⟩ := prim_aux_main κ C hκ hκ2 hC k hk
  refine ⟨Cκ, c₀, C', hCκ, hc₀, hC', ?_⟩
  intro g hg L hL E hE m hm hmC hmim n hn hnc t ht0 ht1 a σ
  have hg1 : 1 ≤ g := hCκ.trans hg
  have hg0 : 0 < g := by linarith
  have hL3 : 3 ≤ L := by
    have : (1 : ℝ) ≤ g ^ 2 := one_le_pow₀ hg1
    exact_mod_cast (show (3 : ℝ) ≤ L by linarith)
  obtain ⟨Wt₀, hW⟩ := h g hg L hL E hE m hm hmC hmim n hn hnc t ht0 ht1 a σ
  set B₀ : ℝ := C' * Real.sqrt (n / g ^ 2) * (1 - t) ^ (-C') with hB₀
  have hB₀0 : 0 ≤ B₀ := by
    have : 0 < 1 - t := by linarith
    positivity
  set F : CellProd n a → ℂ := fun x => primLoopF g L E m t x.1 σ with hF
  have hclose : ∀ ε : ℝ, 0 < ε → Metric.infDist F (loopSpace n E a : Set (CellProd n a → ℂ)) ≤
      B₀ + ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := orbital_limit g hg0 L hL3 E m hm t ht0 ht1 k hk ε hε
    obtain ⟨v, hv, hvx⟩ := hW (max Wt₀ N) (le_max_left _ _)
    refine (Metric.infDist_le_dist_of_mem hv).trans ?_
    rw [dist_eq_norm]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun x => ?_
    have h1 := hvx x
    have h2 : ‖auxLoop g (max Wt₀ N) L E m t k x.1 σ - primLoopF g L E m t x.1 σ‖ ≤ ε :=
      hN (max Wt₀ N) (le_max_right _ _) t ht0 le_rfl x.1 σ
    have e : (F - v) x = (auxLoop g (max Wt₀ N) L E m t k x.1 σ - v x) -
        (auxLoop g (max Wt₀ N) L E m t k x.1 σ - primLoopF g L E m t x.1 σ) := by
      simp only [Pi.sub_apply, hF]; ring
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  have hinf : Metric.infDist F (loopSpace n E a : Set (CellProd n a → ℂ)) ≤ B₀ :=
    le_of_forall_pos_le_add fun ε hε => hclose ε hε
  obtain ⟨v, hv, hd⟩ := IsClosed.exists_infDist_eq_dist
    (Submodule.closed_of_finiteDimensional (loopSpace n E a)) ⟨0, (loopSpace n E a).zero_mem⟩ F
  refine ⟨v, hv, fun x => ?_⟩
  calc ‖primLoopF g L E m t x.1 σ - v x‖ = ‖(F - v) x‖ := rfl
    _ ≤ ‖F - v‖ := norm_le_pi_norm (F - v) x
    _ = Metric.infDist F (loopSpace n E a : Set (CellProd n a → ℂ)) := by
        rw [hd, dist_eq_norm]
    _ ≤ B₀ := hinf

end Main

/-- Lemma 7.5 [uvc:lem:space], primitive bound of (7.12) [uvc:eq:common-space-errors]:
`F_k = W^{k-1} 𝒦_k` is within `C' (n/g²)^{1/2} (1 - t)^{-C'}` of `𝒱` on every cell product. -/
theorem primLoopF_dist_space (κ C : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) (hC : 1 ≤ C) (k : ℕ)
    (hk : 1 ≤ k) :
    ∃ Cκ c₀ C' : ℝ, 1 ≤ Cκ ∧ 0 < c₀ ∧ 0 < C' ∧ ∀ g : ℝ, Cκ ≤ g → ∀ L : ℕ, 4 * g ^ 2 ≤ L →
      ∀ E : ℝ, |E| ≤ 2 - κ → ∀ m : ℂ, IsDysonRootV (hopB g) (gammaG g) L E m → ‖m‖ ≤ C →
      C⁻¹ ≤ m.im → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ c₀ * g ^ 2 → ∀ t : ℝ, 0 ≤ t → t < 1 →
      ∀ (a : Fin k → Fin L) (σ : Fin k → Bool), ∃ v ∈ loopSpace n E a, ∀ x : CellProd n a,
        ‖primLoopF g L E m t x.1 σ - v x‖ ≤ C' * Real.sqrt (n / g ^ 2) * (1 - t) ^ (-C') := by
  exact prim_lim_main κ C hκ hκ2 hC k hk

end LSBA
