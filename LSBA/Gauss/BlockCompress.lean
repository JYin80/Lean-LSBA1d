import LSBA.Gauss.GUEMat
import LSBA.Gauss.RectGauss

/-!
# The GUE in an adapted orthonormal basis

For `Φ : W × d` and `Ψ : W × m` with orthonormal columns, `Φ* Ψ = 0` and `d + m = W`, the three
blocks `Φ* V Φ`, `Ψ* V Φ`, `Ψ* V Ψ` of the `W × W` GUE matrix `V` of (1.2) [eq:covariance] are
independent: `Φ* V Φ` and `Ψ* V Ψ` are `√(d/W)` and `√(m/W)` times GUE matrices of sizes `d` and
`m`, and the cross block `Ψ* V Φ` has independent complex Gaussian entries of variance `1/W`.
This is the split of the fresh GUE block into the space `𝒬` and its complement in the proof of
Lemma 9.5 [us:lem:range], Corollary 9.7 [nc:lem:compression] and (9.50) [us:eq:absolute].
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-! ### Coordinates -/

/-- Restriction of a standard Gaussian product to the coordinates in the image of an injection is a
standard Gaussian product. -/
private lemma blockCompress_restrict {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (e : ι' → ι) (he : Function.Injective e) :
    MeasurePreserving (fun (ω : ι → ℝ) (x : ι') => ω (e x))
      (Measure.pi fun _ : ι => gaussianReal 0 1) (Measure.pi fun _ : ι' => gaussianReal 0 1) := by
  let p : ι → Prop := fun i => ∃ x, e x = i
  let f : ι' ≃ Subtype p := Equiv.ofInjective e he
  have h1 := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => gaussianReal (0 : ℝ) 1) p
  have h2 := measurePreserving_fst (μ := Measure.pi fun i : Subtype p => gaussianReal (0 : ℝ) 1)
    (ν := Measure.pi fun i : {i // ¬ p i} => gaussianReal (0 : ℝ) 1)
  have h3 := (measurePreserving_piCongrLeft (α := fun _ : Subtype p => ℝ)
    (fun _ : Subtype p => gaussianReal (0 : ℝ) 1) f).symm
  have h := h3.comp (h2.comp h1)
  convert h using 1
  funext ω x
  change ω (e x) = (Equiv.piCongrLeft (fun _ : Subtype p => ℝ) f).symm (fun x => ω ↑x) x
  rw [Equiv.piCongrLeft_symm_apply]
  rfl

/-- Functions of the coordinates `e x` and of the coordinates `e' y`, for index families with
disjoint ranges, are independent under a standard Gaussian product. -/
private lemma blockCompress_indep {ι κ κ' A B : Type*} [Fintype ι] [Finite κ] [Finite κ']
    [MeasurableSpace A] [MeasurableSpace B] (e : κ → ι) (e' : κ' → ι)
    (hdisj : ∀ x y, e x ≠ e' y) (φ : (κ → ℝ) → A) (ψ : (κ' → ℝ) → B) (hφ : Measurable φ)
    (hψ : Measurable ψ) :
    IndepFun (fun ω : ι → ℝ => φ fun x => ω (e x)) (fun ω : ι → ℝ => ψ fun y => ω (e' y))
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have := Fintype.ofFinite κ
  have := Fintype.ofFinite κ'
  have hind : iIndepFun (fun (i : ι) (ω : ι → ℝ) => ω i)
      (Measure.pi fun _ : ι => gaussianReal 0 1) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hS : Disjoint (Finset.univ.image e) (Finset.univ.image e') := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨y, -, hy⟩ := Finset.mem_image.1 hb
    exact hdisj x y hy.symm
  have hf : Measurable fun v : (Finset.univ.image e) → ℝ =>
      φ fun x => v ⟨e x, Finset.mem_image_of_mem e (Finset.mem_univ x)⟩ :=
    hφ.comp (measurable_pi_iff.2 fun x => measurable_pi_apply _)
  have hg : Measurable fun v : (Finset.univ.image e') → ℝ =>
      ψ fun y => v ⟨e' y, Finset.mem_image_of_mem e' (Finset.mem_univ y)⟩ :=
    hψ.comp (measurable_pi_iff.2 fun x => measurable_pi_apply _)
  exact (hind.indepFun_finset _ _ hS fun i => measurable_pi_apply i).comp hf hg


/-- The coordinates of the first-block entries. -/
private def blockCompress_e1 (d m : ℕ) (x : Fin 1 × Fin d × Fin d) :
    Fin 1 × Fin (d + m) × Fin (d + m) :=
  (x.1, Fin.castAdd m x.2.1, Fin.castAdd m x.2.2)

/-- The coordinates of the second-block entries. -/
private def blockCompress_e2 (d m : ℕ) (x : Fin 1 × Fin m × Fin m) :
    Fin 1 × Fin (d + m) × Fin (d + m) :=
  (x.1, Fin.natAdd d x.2.1, Fin.natAdd d x.2.2)

/-- The coordinates of the cross entries: the pair `((i, j), k)` is the real part (`k = 0`) or the
imaginary part (`k = 1`) of the entry in row `d + i`, column `j`. -/
private def blockCompress_e3 (d m : ℕ) (x : (Fin m × Fin d) × Fin 2) :
    Fin 1 × Fin (d + m) × Fin (d + m) :=
  (0, if x.2 = 0 then (Fin.castAdd m x.1.2, Fin.natAdd d x.1.1)
    else (Fin.natAdd d x.1.1, Fin.castAdd m x.1.2))

private lemma blockCompress_e1_inj (d m : ℕ) : Function.Injective (blockCompress_e1 d m) := by
  intro x y h
  simp only [blockCompress_e1, Prod.mk.injEq, Fin.castAdd_inj] at h
  exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)

private lemma blockCompress_e2_inj (d m : ℕ) : Function.Injective (blockCompress_e2 d m) := by
  intro x y h
  simp only [blockCompress_e2, Prod.mk.injEq, Fin.natAdd_inj] at h
  exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)

private lemma blockCompress_e3_inj (d m : ℕ) : Function.Injective (blockCompress_e3 d m) := by
  rintro ⟨⟨i, j⟩, k⟩ ⟨⟨i', j'⟩, k'⟩ h
  have hi := i.isLt
  have hj := j.isLt
  have hi' := i'.isLt
  have hj' := j'.isLt
  fin_cases k <;> fin_cases k' <;>
    simp [blockCompress_e3, Prod.ext_iff, Fin.ext_iff] at h ⊢ <;> omega

private lemma blockCompress_e1_ne_e2 (d m : ℕ) (x y) : blockCompress_e1 d m x ≠
    blockCompress_e2 d m y := by
  intro h
  have := x.2.1.isLt
  simp [blockCompress_e1, blockCompress_e2, Prod.ext_iff, Fin.ext_iff] at h
  omega

private lemma blockCompress_e1_ne_e3 (d m : ℕ) (x y) : blockCompress_e1 d m x ≠
    blockCompress_e3 d m y := by
  intro h
  have h1 := x.2.1.isLt
  have h2 := x.2.2.isLt
  obtain ⟨⟨i, j⟩, k⟩ := y
  fin_cases k <;> simp [blockCompress_e1, blockCompress_e3, Prod.ext_iff, Fin.ext_iff] at h <;>
    omega

private lemma blockCompress_e2_ne_e3 (d m : ℕ) (x y) : blockCompress_e2 d m x ≠
    blockCompress_e3 d m y := by
  intro h
  have h1 := x.2.1.isLt
  have h2 := x.2.2.isLt
  obtain ⟨⟨i, j⟩, k⟩ := y
  have := j.isLt
  fin_cases k <;> simp [blockCompress_e2, blockCompress_e3, Prod.ext_iff, Fin.ext_iff] at h <;>
    omega


/-- The complex vector with the real coordinates `y`: `(y_{i,0} + i y_{i,1}) / √2`. -/
private def blockCompress_cplx {ι : Type*} (y : ι × Fin 2 → ℝ) : ι → ℂ :=
  fun i => ((Real.sqrt 2)⁻¹ : ℂ) * ⟨y (i, 0), y (i, 1)⟩

private lemma blockCompress_measurable_cplx {ι : Type*} :
    Measurable (blockCompress_cplx (ι := ι)) := by
  refine measurable_pi_iff.2 fun i => ?_
  have : (fun y : ι × Fin 2 → ℝ => blockCompress_cplx y i) = fun y =>
      ((Real.sqrt 2)⁻¹ : ℂ) * ((y (i, 0) : ℂ) + (y (i, 1) : ℂ) * Complex.I) := by
    funext y
    simp only [blockCompress_cplx, Complex.mk_eq_add_mul_I]
  rw [this]
  fun_prop

/-- Reversing the sign of the second real coordinate of each pair. -/
private def blockCompress_sgn {ι : Type*} (y : ι × Fin 2 → ℝ) : ι × Fin 2 → ℝ :=
  fun x => if x.2 = 0 then y x else -y x

private lemma blockCompress_sgn_mp (ι : Type*) [Fintype ι] :
    MeasurePreserving (blockCompress_sgn (ι := ι))
      (Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 1)
      (Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 1) := by
  have h := measurePreserving_pi (fun _ : ι × Fin 2 => gaussianReal (0 : ℝ) 1)
    (fun _ : ι × Fin 2 => gaussianReal (0 : ℝ) 1)
    (f := fun (x : ι × Fin 2) (t : ℝ) => if x.2 = 0 then t else -t) (fun x => by
      by_cases hx : x.2 = 0
      · simp only [hx, ite_true]
        exact MeasurePreserving.id (gaussianReal (0 : ℝ) 1)
      · simp only [hx, ite_false]
        refine ⟨measurable_neg, ?_⟩
        simpa using gaussianReal_map_neg (μ := 0) (v := 1))
  exact h

/-- The cross block of the standard-basis blocks, as the complex Gaussian vector: the entry
`(i, j)` is `(ω_{j, d+i} - i ω_{d+i, j}) / √2`. -/
private def blockCompress_r3 (d m : ℕ) (ω : Fin 1 × Fin (d + m) × Fin (d + m) → ℝ) :
    Fin m × Fin d → ℂ :=
  blockCompress_cplx (blockCompress_sgn fun x => ω (blockCompress_e3 d m x))

private lemma blockCompress_measurable_r3 (d m : ℕ) : Measurable (blockCompress_r3 d m) :=
  blockCompress_measurable_cplx.comp
    ((blockCompress_sgn_mp (Fin m × Fin d)).measurable.comp
      (measurable_pi_iff.2 fun _ => measurable_pi_apply _))

/-- The law of the cross coordinates is `stdCGauss`. -/
private lemma blockCompress_map_r3 (d m : ℕ) :
    (μ (d + m) 1).map (blockCompress_r3 d m) = stdCGauss (Fin m × Fin d) := by
  have hres := blockCompress_restrict (blockCompress_e3 d m) (blockCompress_e3_inj d m)
  have hsgn := blockCompress_sgn_mp (Fin m × Fin d)
  have hrestr : Measurable fun (ω : Fin 1 × Fin (d + m) × Fin (d + m) → ℝ) x =>
      ω (blockCompress_e3 d m x) := hres.measurable
  have hsm : Measurable (blockCompress_sgn (ι := Fin m × Fin d)) := hsgn.measurable
  have hr3 : blockCompress_r3 d m = blockCompress_cplx ∘ (blockCompress_sgn ∘ fun
      (ω : Fin 1 × Fin (d + m) × Fin (d + m) → ℝ) x => ω (blockCompress_e3 d m x)) := rfl
  rw [hr3, ← Measure.map_map blockCompress_measurable_cplx (hsm.comp hrestr),
    ← Measure.map_map hsm hrestr]
  have h1 : (μ (d + m) 1).map (fun (ω : Fin 1 × Fin (d + m) × Fin (d + m) → ℝ) x =>
      ω (blockCompress_e3 d m x)) = stdGauss ((Fin m × Fin d) × Fin 2) := hres.map_eq
  rw [h1]
  have h2 : (stdGauss ((Fin m × Fin d) × Fin 2)).map blockCompress_sgn =
      stdGauss ((Fin m × Fin d) × Fin 2) := hsgn.map_eq
  rw [h2, stdCGauss_eq_map]
  rfl


/-- The coordinates of the first-block entries, as a one-block sample of size `d`. -/
private def blockCompress_r1 (d m : ℕ) (ω : Ω (d + m) 1) : Ω d 1 :=
  fun x => ω (blockCompress_e1 d m x)

/-- The coordinates of the second-block entries, as a one-block sample of size `m`. -/
private def blockCompress_r2 (d m : ℕ) (ω : Ω (d + m) 1) : Ω m 1 :=
  fun x => ω (blockCompress_e2 d m x)

private lemma blockCompress_mp_r1 (d m : ℕ) :
    MeasurePreserving (blockCompress_r1 d m) (μ (d + m) 1) (μ d 1) :=
  blockCompress_restrict (blockCompress_e1 d m) (blockCompress_e1_inj d m)

private lemma blockCompress_mp_r2 (d m : ℕ) :
    MeasurePreserving (blockCompress_r2 d m) (μ (d + m) 1) (μ m 1) :=
  blockCompress_restrict (blockCompress_e2 d m) (blockCompress_e2_inj d m)

/-- The three groups of coordinates are independent with laws `μ d 1`, `stdCGauss` and `μ m 1`. -/
private lemma blockCompress_joint (d m : ℕ) :
    (μ (d + m) 1).map (fun ω => (blockCompress_r1 d m ω,
        (blockCompress_r3 d m ω, blockCompress_r2 d m ω))) =
      (μ d 1).prod ((stdCGauss (Fin m × Fin d)).prod (μ m 1)) := by
  have hm1 := (blockCompress_mp_r1 d m).measurable
  have hm2 := (blockCompress_mp_r2 d m).measurable
  have hm3 := blockCompress_measurable_r3 d m
  have h23 : IndepFun (blockCompress_r3 d m) (blockCompress_r2 d m) (μ (d + m) 1) :=
    blockCompress_indep (blockCompress_e3 d m) (blockCompress_e2 d m)
      (fun x y => (blockCompress_e2_ne_e3 d m y x).symm)
      (fun v => blockCompress_cplx (blockCompress_sgn v)) (fun v => v)
      (blockCompress_measurable_cplx.comp (blockCompress_sgn_mp (Fin m × Fin d)).measurable)
      measurable_id
  have h1 : IndepFun (blockCompress_r1 d m)
      (fun ω => (blockCompress_r3 d m ω, blockCompress_r2 d m ω)) (μ (d + m) 1) :=
    blockCompress_indep (blockCompress_e1 d m)
      (Sum.elim (blockCompress_e3 d m) (blockCompress_e2 d m))
      (fun x y => by
        rcases y with y | y
        · exact blockCompress_e1_ne_e3 d m x y
        · exact blockCompress_e1_ne_e2 d m x y)
      (fun v => v)
      (fun v => (blockCompress_cplx (blockCompress_sgn fun x => v (Sum.inl x)),
        fun y => v (Sum.inr y)))
      measurable_id
      (Measurable.prodMk
        (blockCompress_measurable_cplx.comp
          ((blockCompress_sgn_mp (Fin m × Fin d)).measurable.comp
            (measurable_pi_iff.2 fun _ => measurable_pi_apply _)))
        (measurable_pi_iff.2 fun _ => measurable_pi_apply _))
  rw [(indepFun_iff_map_prod_eq_prod_map_map hm1.aemeasurable (hm3.prodMk hm2).aemeasurable).1 h1,
    (indepFun_iff_map_prod_eq_prod_map_map hm3.aemeasurable hm2.aemeasurable).1 h23]
  rw [(blockCompress_mp_r1 d m).map_eq, (blockCompress_mp_r2 d m).map_eq,
    blockCompress_map_r3]


/-! ### The standard basis -/

/-- Each entry of a GUE block is a measurable function of the sample. -/
private lemma blockCompress_measurable_gueBlock_apply (W : ℕ) (α β : Fin W) :
    Measurable fun ω : Ω W 1 => gueBlock W 1 ω 0 α β := by
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

/-- The entries of the `W × W` GUE block at the images of an order embedding `ρ : Fin n → Fin W`
are `√(n/W)` times those of the `n × n` GUE block of the sample read at the coordinates of `ρ`:
the variances of (1.2) [eq:covariance] agree. -/
private lemma blockCompress_entry {W n : ℕ} (ρ : Fin n → Fin W)
    (hinj : ∀ a b, ρ a = ρ b ↔ a = b) (hlt : ∀ a b, ρ a < ρ b ↔ a < b) (ω : Ω W 1)
    (α β : Fin n) :
    gueBlock W 1 ω 0 (ρ α) (ρ β) =
      ((Real.sqrt ((n : ℝ) / W) : ℝ) : ℂ) •
        gueBlock n 1 (fun x => ω (x.1, ρ x.2.1, ρ x.2.2)) 0 α β := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Fin.pos α
  have hW : (0 : ℝ) < W := by exact_mod_cast Fin.pos (ρ α)
  have ha : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 hn).ne'
  have hb : Real.sqrt W ≠ 0 := (Real.sqrt_pos.2 hW).ne'
  have hc : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 two_pos).ne'
  have hs : ((Real.sqrt ((n : ℝ) / W) : ℝ) : ℂ) = (Real.sqrt n : ℂ) / Real.sqrt W := by
    rw [Real.sqrt_div hn.le, Complex.ofReal_div]
  have h2n : ((Real.sqrt (2 * n) : ℝ) : ℂ) = (Real.sqrt 2 : ℂ) * Real.sqrt n := by
    rw [Real.sqrt_mul (by norm_num), Complex.ofReal_mul]
  have h2W : ((Real.sqrt (2 * W) : ℝ) : ℂ) = (Real.sqrt 2 : ℂ) * Real.sqrt W := by
    rw [Real.sqrt_mul (by norm_num), Complex.ofReal_mul]
  have ha' : (Real.sqrt n : ℂ) ≠ 0 := by exact_mod_cast ha
  have hb' : (Real.sqrt W : ℂ) ≠ 0 := by exact_mod_cast hb
  have hc' : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast hc
  simp only [gueBlock, Matrix.of_apply, smul_eq_mul, hinj, hlt, hs, h2n, h2W]
  split_ifs
  · field_simp
  · field_simp
  · field_simp

private lemma blockCompress_entry_cast (d m : ℕ) (ω : Ω (d + m) 1) (α β : Fin d) :
    gueBlock (d + m) 1 ω 0 (Fin.castAdd m α) (Fin.castAdd m β) =
      ((Real.sqrt ((d : ℝ) / ((d + m : ℕ) : ℝ)) : ℝ) : ℂ) •
        gueBlock d 1 (blockCompress_r1 d m ω) 0 α β :=
  blockCompress_entry (Fin.castAdd m) (fun _ _ => Fin.castAdd_inj)
    (fun _ _ => Iff.rfl) ω α β

private lemma blockCompress_entry_nat (d m : ℕ) (ω : Ω (d + m) 1) (α β : Fin m) :
    gueBlock (d + m) 1 ω 0 (Fin.natAdd d α) (Fin.natAdd d β) =
      ((Real.sqrt ((m : ℝ) / ((d + m : ℕ) : ℝ)) : ℝ) : ℂ) •
        gueBlock m 1 (blockCompress_r2 d m ω) 0 α β :=
  blockCompress_entry (Fin.natAdd d) (fun _ _ => Fin.natAdd_inj d)
    (fun _ _ => Fin.natAdd_lt_natAdd_iff d) ω α β

private lemma blockCompress_entry_cross (d m : ℕ) (ω : Ω (d + m) 1) (i : Fin m) (j : Fin d) :
    gueBlock (d + m) 1 ω 0 (Fin.natAdd d i) (Fin.castAdd m j) =
      (((Real.sqrt ((d + m : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) * blockCompress_r3 d m ω (i, j) := by
  have hj := j.isLt
  have hlt : Fin.castAdd m j < Fin.natAdd d i := by
    rw [Fin.lt_def]
    simp only [Fin.val_castAdd, Fin.val_natAdd]
    omega
  have hW : (0 : ℝ) < ((d + m : ℕ) : ℝ) := Nat.cast_pos.2 (by omega)
  have hb : Real.sqrt ((d + m : ℕ) : ℝ) ≠ 0 := (Real.sqrt_pos.2 hW).ne'
  have hc : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 two_pos).ne'
  have h2W : ((Real.sqrt (2 * ((d + m : ℕ) : ℝ)) : ℝ) : ℂ) =
      (Real.sqrt 2 : ℂ) * Real.sqrt ((d + m : ℕ) : ℝ) := by
    rw [Real.sqrt_mul (by norm_num), Complex.ofReal_mul]
  have hb' : (Real.sqrt ((d + m : ℕ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hb
  have hc' : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast hc
  simp only [gueBlock, Matrix.of_apply, blockCompress_r3, blockCompress_cplx, blockCompress_sgn,
    blockCompress_e3, hlt.ne', hlt.not_gt, ite_false]
  simp only [h2W, Complex.ofReal_inv]
  simp [Complex.mk_eq_add_mul_I]
  field_simp
  ring


/-- The block law in the standard basis `Fin (d + m) ≃ Fin d ⊕ Fin m`. -/
private lemma blockCompress_std (d m : ℕ) :
    (μ (d + m) 1).map (fun ω => ((gueMat (d + m) ω).submatrix (Fin.castAdd m) (Fin.castAdd m),
        (gueMat (d + m) ω).submatrix (Fin.natAdd d) (Fin.castAdd m),
        (gueMat (d + m) ω).submatrix (Fin.natAdd d) (Fin.natAdd d))) =
      ((μ d 1).map fun ω =>
          ((Real.sqrt ((d : ℝ) / ((d + m : ℕ) : ℝ)) : ℝ) : ℂ) • gueMat d ω).prod
        (((stdCGauss (Fin m × Fin d)).map fun x =>
            (((Real.sqrt ((d + m : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • cgMat x).prod
          ((μ m 1).map fun ω =>
            ((Real.sqrt ((m : ℝ) / ((d + m : ℕ) : ℝ)) : ℝ) : ℂ) • gueMat m ω)) := by
  have hf1 : Measurable fun ω : Ω d 1 =>
      ((Real.sqrt ((d : ℝ) / ((d + m : ℕ) : ℝ)) : ℝ) : ℂ) • gueMat d ω := by
    refine Matrix.measurable_iff.2 fun α β => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, gueMat]
    exact (blockCompress_measurable_gueBlock_apply d α β).const_mul _
  have hf2 : Measurable fun ω : Ω m 1 =>
      ((Real.sqrt ((m : ℝ) / ((d + m : ℕ) : ℝ)) : ℝ) : ℂ) • gueMat m ω := by
    refine Matrix.measurable_iff.2 fun α β => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, gueMat]
    exact (blockCompress_measurable_gueBlock_apply m α β).const_mul _
  have hf3 : Measurable fun x : Fin m × Fin d → ℂ =>
      (((Real.sqrt ((d + m : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • cgMat x := by
    refine Matrix.measurable_iff.2 fun α β => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, cgMat, Matrix.of_apply]
    exact (measurable_pi_apply (α, β)).const_mul _
  have hJ : Measurable fun ω => (blockCompress_r1 d m ω,
      (blockCompress_r3 d m ω, blockCompress_r2 d m ω)) :=
    (blockCompress_mp_r1 d m).measurable.prodMk
      ((blockCompress_measurable_r3 d m).prodMk (blockCompress_mp_r2 d m).measurable)
  rw [Measure.map_prod_map _ _ hf3 hf2, Measure.map_prod_map _ _ hf1 (hf3.prodMap hf2),
    ← blockCompress_joint, Measure.map_map (hf1.prodMap (hf3.prodMap hf2)) hJ]
  congr 1
  funext ω
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext α β
    simp only [Matrix.submatrix_apply, Function.comp_apply, Prod.map_fst, Matrix.smul_apply,
      gueMat]
    exact blockCompress_entry_cast d m ω α β
  · ext i j
    simp only [Matrix.submatrix_apply, Function.comp_apply, Prod.map_fst, Prod.map_snd,
      Matrix.smul_apply, gueMat, cgMat, Matrix.of_apply, smul_eq_mul]
    exact blockCompress_entry_cross d m ω i j
  · ext α β
    simp only [Matrix.submatrix_apply, Function.comp_apply, Prod.map_snd, Matrix.smul_apply,
      gueMat]
    exact blockCompress_entry_nat d m ω α β


/-! ### The adapted basis -/

/-- The orthonormal columns `Φ`, `Ψ` with `Φ* Ψ = 0` and `d + m = W` are the columns of a unitary
matrix. -/
private lemma blockCompress_unitary (d m : ℕ) (Φ : Matrix (Fin (d + m)) (Fin d) ℂ)
    (Ψ : Matrix (Fin (d + m)) (Fin m) ℂ) (hΦ : Φᴴ * Φ = 1) (hΨ : Ψᴴ * Ψ = 1)
    (hΦΨ : Φᴴ * Ψ = 0) :
    ∃ U : Matrix.unitaryGroup (Fin (d + m)) ℂ,
      (∀ (r : Fin (d + m)) (j : Fin d), (U : Matrix (Fin (d + m)) (Fin (d + m)) ℂ) r
        (Fin.castAdd m j) = Φ r j) ∧
      ∀ (r : Fin (d + m)) (j : Fin m), (U : Matrix (Fin (d + m)) (Fin (d + m)) ℂ) r
        (Fin.natAdd d j) = Ψ r j := by
  let U : Matrix (Fin (d + m)) (Fin (d + m)) ℂ :=
    Matrix.of fun r c => Fin.addCases (motive := fun _ => ℂ) (fun j => Φ r j) (fun j => Ψ r j) c
  have hΨΦ : Ψᴴ * Φ = 0 := by
    have := congrArg Matrix.conjTranspose hΦΨ
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] at this
  have hU : star U * U = 1 := by
    ext a b
    rw [Matrix.mul_apply, Matrix.one_apply]
    induction a using Fin.addCases with
    | left i =>
      induction b using Fin.addCases with
      | left j =>
        have h := congrFun (congrFun hΦ i) j
        rw [Matrix.mul_apply, Matrix.one_apply] at h
        simpa [U, Matrix.conjTranspose_apply] using h
      | right j =>
        have h := congrFun (congrFun hΦΨ i) j
        rw [Matrix.mul_apply] at h
        have hne : Fin.castAdd m i ≠ Fin.natAdd d j := fun h => by
          have := congrArg Fin.val h
          simp at this
          omega
        simpa [U, Matrix.conjTranspose_apply, hne] using h
    | right i =>
      induction b using Fin.addCases with
      | left j =>
        have h := congrFun (congrFun hΨΦ i) j
        rw [Matrix.mul_apply] at h
        have hne : Fin.natAdd d i ≠ Fin.castAdd m j := fun h => by
          have := congrArg Fin.val h
          simp at this
          omega
        simpa [U, Matrix.conjTranspose_apply, hne] using h
      | right j =>
        have h := congrFun (congrFun hΨ i) j
        rw [Matrix.mul_apply, Matrix.one_apply] at h
        simpa [U, Matrix.conjTranspose_apply] using h
  exact ⟨⟨U, Matrix.mem_unitaryGroup_iff'.2 hU⟩, fun r j => by simp [U], fun r j => by simp [U]⟩


/-- Compressing by the columns `ρ`, `σ` of a unitary `U` is the corresponding submatrix of the
conjugate `U* G U`. -/
private lemma blockCompress_conj_submatrix {N a b : ℕ} (U G : Matrix (Fin N) (Fin N) ℂ)
    (P : Matrix (Fin N) (Fin a) ℂ) (Q : Matrix (Fin N) (Fin b) ℂ) (ρ : Fin a → Fin N)
    (σ : Fin b → Fin N) (hP : ∀ r j, U r (ρ j) = P r j) (hQ : ∀ r j, U r (σ j) = Q r j) :
    Pᴴ * G * Q = (star U * G * U).submatrix ρ σ := by
  ext α β
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.star_apply,
    Matrix.submatrix_apply, hP, hQ]

/-- The block law of the GUE in an adapted orthonormal basis (proof of Lemma 9.5
[us:lem:range]): the blocks `(Φ* V Φ, Ψ* V Φ, Ψ* V Ψ)` have the product law of
`√(d/W) V_d`, `W^{-1/2} G` (`G` standard complex Gaussian, `m × d`) and `√(m/W) V_m`. -/
theorem map_blockCompress_gueMat (W d m : ℕ) (hW : d + m = W) (Φ : Matrix (Fin W) (Fin d) ℂ)
    (Ψ : Matrix (Fin W) (Fin m) ℂ) (hΦ : Φᴴ * Φ = 1) (hΨ : Ψᴴ * Ψ = 1) (hΦΨ : Φᴴ * Ψ = 0) :
    (μ W 1).map (fun ω => (Φᴴ * gueMat W ω * Φ, Ψᴴ * gueMat W ω * Φ, Ψᴴ * gueMat W ω * Ψ)) =
      ((μ d 1).map fun ω => ((Real.sqrt ((d : ℝ) / W) : ℝ) : ℂ) • gueMat d ω).prod
        (((stdCGauss (Fin m × Fin d)).map fun x => (((Real.sqrt W)⁻¹ : ℝ) : ℂ) • cgMat x).prod
          ((μ m 1).map fun ω => ((Real.sqrt ((m : ℝ) / W) : ℝ) : ℂ) • gueMat m ω)) := by
  subst hW
  obtain ⟨U, hUΦ, hUΨ⟩ := blockCompress_unitary d m Φ Ψ hΦ hΨ hΦΨ
  have hT : MeasurePreserving (conjMap (d + m) 1 (star U)) (μ (d + m) 1) (μ (d + m) 1) :=
    measurePreserving_conjMap (d + m) 1 (star U)
  have hent : ∀ (α β : Fin (d + m)), Measurable fun ω : Ω (d + m) 1 => gueMat (d + m) ω α β :=
    fun α β => blockCompress_measurable_gueBlock_apply (d + m) α β
  have hH : Measurable fun ω : Ω (d + m) 1 =>
      ((gueMat (d + m) ω).submatrix (Fin.castAdd m) (Fin.castAdd m),
        (gueMat (d + m) ω).submatrix (Fin.natAdd d) (Fin.castAdd m),
        (gueMat (d + m) ω).submatrix (Fin.natAdd d) (Fin.natAdd d)) := by
    refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_) <;>
      exact Matrix.measurable_iff.2 fun α β => hent _ _
  have hfun : (fun ω : Ω (d + m) 1 =>
      (Φᴴ * gueMat (d + m) ω * Φ, Ψᴴ * gueMat (d + m) ω * Φ, Ψᴴ * gueMat (d + m) ω * Ψ)) =
      (fun ω : Ω (d + m) 1 =>
        ((gueMat (d + m) ω).submatrix (Fin.castAdd m) (Fin.castAdd m),
          (gueMat (d + m) ω).submatrix (Fin.natAdd d) (Fin.castAdd m),
          (gueMat (d + m) ω).submatrix (Fin.natAdd d) (Fin.natAdd d))) ∘
        conjMap (d + m) 1 (star U) := by
    funext ω
    have hstar : ((star U : Matrix.unitaryGroup (Fin (d + m)) ℂ) :
        Matrix (Fin (d + m)) (Fin (d + m)) ℂ) =
        star (U : Matrix (Fin (d + m)) (Fin (d + m)) ℂ) := rfl
    have hconj : gueMat (d + m) (conjMap (d + m) 1 (star U) ω) =
        star (U : Matrix (Fin (d + m)) (Fin (d + m)) ℂ) * gueMat (d + m) ω *
          (U : Matrix (Fin (d + m)) (Fin (d + m)) ℂ) := by
      simp only [gueMat]
      rw [gueBlock_conjMap, hstar, star_star]
    simp only [Function.comp_apply, hconj]
    exact Prod.ext
      (blockCompress_conj_submatrix _ _ Φ Φ _ _ hUΦ hUΦ)
      (Prod.ext (blockCompress_conj_submatrix _ _ Ψ Φ _ _ hUΨ hUΦ)
        (blockCompress_conj_submatrix _ _ Ψ Ψ _ _ hUΨ hUΨ))
  rw [hfun, ← Measure.map_map hH hT.measurable, hT.map_eq]
  exact blockCompress_std d m

end LSBA
