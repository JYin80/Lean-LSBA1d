import LSBA.Gauss.GUEMat

/-!
# Compressions of a GUE matrix

For `Q*Q = 1` (`Q : W × n`), the law of `Q*V_WQ` is the law of `√(n/W) V_n` (the dimension adapter
of Appendix G.2 [app:inverse-image-inputs]).
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

noncomputable section
open scoped Classical

namespace LSBA

/-- Restriction of a standard Gaussian product to the coordinates in the image of an injection is a
standard Gaussian product. -/
private lemma compress_measurePreserving_restrict {ι ι' : Type*} [Fintype ι] [Fintype ι']
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

/-- The columns of an isometry `Q` are orthonormal in `ℂ^W`. -/
private lemma compress_orthonormal_cols {W n : ℕ} (Q : Matrix (Fin W) (Fin n) ℂ)
    (hQ : Qᴴ * Q = 1) :
    Orthonormal ℂ
      (fun j : Fin n => (WithLp.toLp 2 (fun r => Q r j) : EuclideanSpace ℂ (Fin W))) := by
  rw [orthonormal_iff_ite]
  intro i j
  have h := congrFun (congrFun hQ i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [Matrix.conjTranspose_apply, dotProduct] at h ⊢
  simpa [mul_comm] using h

/-- An isometry `Q : W × n` has `n ≤ W`, and its columns are the first `n` columns of a unitary. -/
private lemma compress_exists_unitary (W n : ℕ) (Q : Matrix (Fin W) (Fin n) ℂ)
    (hQ : Qᴴ * Q = 1) :
    ∃ h : n ≤ W, ∃ U : Matrix.unitaryGroup (Fin W) ℂ,
      ∀ (r : Fin W) (j : Fin n), (U : Matrix (Fin W) (Fin W) ℂ) r (Fin.castLE h j) = Q r j := by
  have hon := compress_orthonormal_cols Q hQ
  have hle : n ≤ W := by
    have := hon.linearIndependent.fintype_card_le_finrank
    simpa using this
  refine ⟨hle, ?_⟩
  let v : Fin W → EuclideanSpace ℂ (Fin W) := fun i =>
    if hi : i.val < n then WithLp.toLp 2 (fun r => Q r ⟨i.val, hi⟩) else 0
  let s : Set (Fin W) := {i | i.val < n}
  let g : s → Fin n := fun i => ⟨i.1.val, i.2⟩
  have hg : Function.Injective g := fun a b hab =>
    Subtype.ext (Fin.ext (by simpa [g] using congrArg Fin.val hab))
  have hvs : s.domRestrict v = (fun j : Fin n => (WithLp.toLp 2 (fun r => Q r j) :
      EuclideanSpace ℂ (Fin W))) ∘ g := by
    funext i
    have hi : (i : Fin W).val < n := i.2
    simp [v, g, Set.domRestrict, hi]
  have hort : Orthonormal ℂ (s.domRestrict v) := by
    rw [hvs]; exact hon.comp g hg
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin W)) (by simp) hort
  refine ⟨⟨(EuclideanSpace.basisFun (Fin W) ℂ).toBasis.toMatrix b,
    OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary _ _⟩, fun r j => ?_⟩
  have hj : Fin.castLE hle j ∈ s := by simp [s]
  have := hb _ hj
  simp only [Module.Basis.toMatrix_apply]
  simp [this, v]

/-- Each entry of a GUE block is a measurable function of the sample. -/
private lemma compress_measurable_gueBlock_apply (W : ℕ) (α β : Fin W) :
    Measurable fun ω : Ω W 1 => gueBlock W 1 ω 0 α β := by
  unfold gueBlock
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

/-- The coordinates `(0, α, β)` with `α, β < n` of a one-block sample of size `W ≥ n`, as a
one-block sample of size `n`. -/
private def compressRestrict {W n : ℕ} (h : n ≤ W) (ω : Ω W 1) : Ω n 1 :=
  fun x => ω (x.1, Fin.castLE h x.2.1, Fin.castLE h x.2.2)

/-- The entries of the `W × W` GUE block on the first `n` indices are `√(n/W)` times those of the
`n × n` GUE block of the restricted sample: the variances of (1.2) [eq:covariance] agree. -/
private lemma compressRestrict_gueBlock {W n : ℕ} (h : n ≤ W) (ω : Ω W 1) (α β : Fin n) :
    gueBlock W 1 ω 0 (Fin.castLE h α) (Fin.castLE h β) =
      ((Real.sqrt ((n : ℝ) / W) : ℝ) : ℂ) • gueBlock n 1 (compressRestrict h ω) 0 α β := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Fin.pos α
  have hW : (0 : ℝ) < W := lt_of_lt_of_le hn (by exact_mod_cast h)
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
  have hlt : ∀ a b : Fin n, Fin.castLE h a < Fin.castLE h b ↔ a < b := fun a b => Iff.rfl
  have hinj : ∀ a b : Fin n, Fin.castLE h a = Fin.castLE h b ↔ a = b := fun a b => Fin.castLE_inj
  simp only [gueBlock, Matrix.of_apply, smul_eq_mul, compressRestrict, hinj,
    hlt, hs, h2n, h2W]
  split_ifs
  · field_simp
  · field_simp
  · field_simp

/-- Compression of the GUE matrix of (1.2) [eq:covariance] to an isometry `Q`: `Q^* V Q` has the
law of `√(n/W)` times the `n × n` GUE matrix; the rescaling of Appendix G.2.2
[app:inverse-image-spectrum]. -/
theorem map_compress_gueMat (W n : ℕ) (Q : Matrix (Fin W) (Fin n) ℂ) (hQ : Qᴴ * Q = 1) :
    (μ W 1).map (fun ω => Qᴴ * gueMat W ω * Q) =
      (μ n 1).map (fun ω => ((Real.sqrt ((n : ℝ) / W) : ℝ) : ℂ) • gueMat n ω) := by
  obtain ⟨h, U, hU⟩ := compress_exists_unitary W n Q hQ
  have hT : MeasurePreserving (conjMap W 1 (star U)) (μ W 1) (μ W 1) :=
    measurePreserving_conjMap W 1 (star U)
  have hρ : MeasurePreserving (compressRestrict h) (μ W 1) (μ n 1) :=
    compress_measurePreserving_restrict (fun x : Fin 1 × Fin n × Fin n =>
      ((x.1, Fin.castLE h x.2.1, Fin.castLE h x.2.2) : Fin 1 × Fin W × Fin W))
      (fun x y hxy => by
        simp only [Prod.mk.injEq, Fin.castLE_inj] at hxy
        exact Prod.ext hxy.1 (Prod.ext hxy.2.1 hxy.2.2))
  have hF : Measurable fun ω : Ω n 1 => ((Real.sqrt ((n : ℝ) / W) : ℝ) : ℂ) • gueMat n ω := by
    refine Matrix.measurable_iff.2 fun α β => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, gueMat]
    exact (compress_measurable_gueBlock_apply n α β).const_mul _
  have hfun : (fun ω : Ω W 1 => Qᴴ * gueMat W ω * Q) =
      (fun ω : Ω n 1 => ((Real.sqrt ((n : ℝ) / W) : ℝ) : ℂ) • gueMat n ω) ∘
        (compressRestrict h ∘ conjMap W 1 (star U)) := by
    funext ω
    ext α β
    have hconj := gueBlock_conjMap W 1 (star U) ω 0
    have hstar : ((star U : Matrix.unitaryGroup (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ) =
        star (U : Matrix (Fin W) (Fin W) ℂ) := rfl
    have hentry : (Qᴴ * gueMat W ω * Q) α β =
        (star (U : Matrix (Fin W) (Fin W) ℂ) * gueBlock W 1 ω 0 *
          (U : Matrix (Fin W) (Fin W) ℂ)) (Fin.castLE h α) (Fin.castLE h β) := by
      simp only [gueMat, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.star_apply, hU]
    rw [hentry]
    have hconj' : gueBlock W 1 (conjMap W 1 (star U) ω) 0 =
        star (U : Matrix (Fin W) (Fin W) ℂ) * gueBlock W 1 ω 0 *
          (U : Matrix (Fin W) (Fin W) ℂ) := by
      rw [hconj, hstar, star_star]
    rw [← hconj', compressRestrict_gueBlock h]
    rfl
  rw [hfun, ← Measure.map_map hF (hρ.measurable.comp hT.measurable),
    ← Measure.map_map hρ.measurable hT.measurable, hT.map_eq, hρ.map_eq]


end LSBA
