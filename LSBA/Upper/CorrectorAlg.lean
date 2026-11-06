import LSBA.Upper.CenterCorrection

/-!
# Algebraic properties of the corrected updates

Two properties of the update `[P_g p]_{≤R+2,0}` of the corrected observables in the corrected
coordinates (11.47) [lg:eq:current-coordinate-updates], used in Section 11.3.4
[lg:sec:cocycle-correction]: the update of `F_k` lies in the ideal `(f_j : j ≠ 0)` (no term free
of `F`, at every order), and the updates commute with conjugation `x_k ↦ x_{−k}`.
-/

open MeasureTheory ProbabilityTheory Real Finset MvPolynomial
open scoped ENNReal NNReal Kronecker Matrix Matrix.Norms.L2Operator

noncomputable section

open scoped Classical

namespace LSBA

private lemma ca_weight_gamWt (d : ObsVar →₀ ℕ) : Finsupp.weight ObsVar.gamWt d = d .γ := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_single ObsVar.γ]
  · simp [ObsVar.gamWt]
  · intro b _ hb
    cases b <;> simp_all [ObsVar.gamWt]
  · intro h
    simp [Finsupp.notMem_support_iff.mp h]

private lemma ca_coeff_comp (s : ℕ) (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (weightedHomogeneousComponent ObsVar.gamWt s p).coeff d =
      if d .γ = s then p.coeff d else 0 := by
  rw [coeff_weightedHomogeneousComponent, ca_weight_gamWt]

private lemma ca_coeff_truncG (N : ℕ) (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (truncG N p).coeff d = if d .γ ≤ N then p.coeff d else 0 := by
  unfold truncG
  rw [LinearMap.sum_apply, MvPolynomial.coeff_sum]
  simp only [ca_coeff_comp]
  rw [Finset.sum_ite_eq]
  simp

private lemma ca_support_truncG (N : ℕ) (p : ObsPoly) : (truncG N p).support ⊆ p.support := by
  intro d hd
  rw [mem_support_iff, ca_coeff_truncG] at hd
  rw [mem_support_iff]
  intro h
  exact hd (by simp [h])

private lemma ca_fIdeal_iff (p : ObsPoly) :
    p ∈ fIdeal ↔ ∀ d ∈ p.support, ∃ k : NzInt, d (.f k) ≠ 0 := by
  have h : fIdeal = Ideal.span (MvPolynomial.X '' (Set.range ObsVar.f) : Set ObsPoly) := by
    unfold fIdeal
    congr 1
    ext x
    simp [Set.mem_image]
  rw [h, mem_ideal_span_X_image]
  constructor
  · intro H d hd
    obtain ⟨i, ⟨k, rfl⟩, hi⟩ := H d hd
    exact ⟨k, hi⟩
  · intro H d hd
    obtain ⟨k, hk⟩ := H d hd
    exact ⟨.f k, ⟨k, rfl⟩, hk⟩

private lemma ca_fIdeal_of_support_subset {p q : ObsPoly} (h : q.support ⊆ p.support)
    (hp : p ∈ fIdeal) : q ∈ fIdeal := by
  rw [ca_fIdeal_iff] at hp ⊢
  exact fun d hd => hp d (h hd)

private lemma ca_bind₁_fIdeal (τ : ObsVar → ObsPoly) (hτ : ∀ k : NzInt, τ (.f k) ∈ fIdeal)
    {p : ObsPoly} (hp : p ∈ fIdeal) : bind₁ τ p ∈ fIdeal := by
  have h : fIdeal ≤ Ideal.comap (bind₁ τ : ObsPoly →ₐ[ℂ] ObsPoly) fIdeal := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    change bind₁ τ (X (.f k)) ∈ fIdeal
    rw [bind₁_X_right]
    exact hτ k
  exact Ideal.mem_comap.mp (h hp)

private lemma ca_zeroW_X (v : ObsVar) : zeroW (X v) = if v = .w then 0 else X v := by
  simp [zeroW]


private lemma ca_fIdeal_le_obs : fIdeal ≤ obsIdeal := Ideal.span_mono Set.subset_union_right

private lemma ca_zeroW_obsIdeal {p : ObsPoly} (hp : p ∈ obsIdeal) : zeroW p ∈ fIdeal := by
  have h : obsIdeal ≤ Ideal.comap (zeroW : ObsPoly →ₐ[ℂ] ObsPoly) fIdeal := by
    refine Ideal.span_le.mpr ?_
    rintro _ (hx | ⟨k, rfl⟩)
    · rw [Set.mem_singleton_iff.mp hx]
      change zeroW (X .w) ∈ fIdeal
      rw [ca_zeroW_X]
      simp
    · change zeroW (X (.f k)) ∈ fIdeal
      rw [ca_zeroW_X]
      simp only [ite_false, reduceCtorEq]
      exact Ideal.subset_span ⟨k, rfl⟩
  exact Ideal.mem_comap.mp (h hp)

private lemma ca_rotPoly_fIdeal (E : ℝ) {p : ObsPoly} (hp : p ∈ fIdeal) :
    rotPoly E p ∈ fIdeal := by
  refine ca_bind₁_fIdeal (fun v => C ((-normalPhase E) ^ v.idx) * X v) ?_ hp
  intro k
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)

private lemma ca_updPoly_fIdeal (E : ℝ) (N : ℕ) {p : ObsPoly} (hp : p ∈ fIdeal) :
    updPoly E N p ∈ fIdeal := by
  unfold updPoly
  refine ca_fIdeal_of_support_subset (ca_support_truncG N _) ?_
  refine Ideal.sum_mem _ fun r _ => Ideal.mul_mem_left _ _ ?_
  exact ca_zeroW_obsIdeal (wickMap_mem_obsIdeal r (ca_fIdeal_le_obs (ca_rotPoly_fIdeal E hp)))

private lemma ca_revCoord_succ (N : ℕ) (σ : ObsVar → ObsPoly) (r : ℕ) (v : ObsVar) :
    revCoord N σ (r + 1) v = truncG N (X v - bind₁ (revCoord N σ r) (σ v - X v)) := by
  rw [revCoord]

private lemma ca_neg_neg (v : ObsVar) : v.neg.neg = v := by
  cases v with
  | m k => exact congrArg ObsVar.m (Subtype.ext (neg_neg k.1))
  | f k => exact congrArg ObsVar.f (Subtype.ext (neg_neg k.1))
  | w => rfl
  | γ => rfl

private lemma ca_neg_injective : Function.Injective ObsVar.neg :=
  Function.LeftInverse.injective ca_neg_neg

private lemma ca_idx_neg (v : ObsVar) : v.neg.idx = -v.idx := by
  cases v <;> simp [ObsVar.neg, ObsVar.idx]

private lemma ca_conj_X (v : ObsVar) : conjPoly (X v) = X v.neg := by
  simp [conjPoly]

private lemma ca_conj_C (a : ℂ) : conjPoly (C a) = C (starRingEnd ℂ a) := by
  simp [conjPoly]

private lemma ca_conj_eq (p : ObsPoly) :
    conjPoly p = MvPolynomial.map (starRingEnd ℂ) (rename ObsVar.neg p) := by
  refine hom_eq_hom conjPoly
    ((MvPolynomial.map (starRingEnd ℂ)).comp (rename ObsVar.neg : ObsPoly →ₐ[ℂ] ObsPoly).toRingHom)
    ?_ ?_ p
  · ext r
    simp [ca_conj_C]
  · intro v
    simp [ca_conj_X]

private lemma ca_mapDomain_neg_neg (d : ObsVar →₀ ℕ) :
    (d.mapDomain ObsVar.neg).mapDomain ObsVar.neg = d := by
  rw [← Finsupp.mapDomain_comp]
  have : (ObsVar.neg ∘ ObsVar.neg : ObsVar → ObsVar) = id := funext ca_neg_neg
  rw [this, Finsupp.mapDomain_id]

private lemma ca_coeff_conj (p : ObsPoly) (d : ObsVar →₀ ℕ) :
    (conjPoly p).coeff d = starRingEnd ℂ (p.coeff (d.mapDomain ObsVar.neg)) := by
  rw [ca_conj_eq, MvPolynomial.coeff_map]
  congr 1
  have := coeff_rename_mapDomain ObsVar.neg ca_neg_injective p (d.mapDomain ObsVar.neg)
  rwa [ca_mapDomain_neg_neg] at this

private lemma ca_mapDomain_neg_gamma (d : ObsVar →₀ ℕ) : (d.mapDomain ObsVar.neg) .γ = d .γ := by
  exact Finsupp.mapDomain_apply_of_injective ca_neg_injective d ObsVar.γ

private lemma ca_conj_bind₁ {τ : ObsVar → ObsPoly} (hτ : ∀ v, conjPoly (τ v) = τ v.neg)
    (p : ObsPoly) : conjPoly (bind₁ τ p) = bind₁ τ (conjPoly p) := by
  refine hom_eq_hom (conjPoly.comp (bind₁ τ : ObsPoly →ₐ[ℂ] ObsPoly).toRingHom)
    ((bind₁ τ : ObsPoly →ₐ[ℂ] ObsPoly).toRingHom.comp conjPoly) ?_ ?_ p
  · ext r
    simp [ca_conj_C]
  · intro v
    simp [hτ, ca_conj_X]

private lemma ca_conj_zpow (E : ℝ) (k : ℤ) :
    starRingEnd ℂ ((-normalPhase E) ^ k) = (-normalPhase E) ^ (-k) := by
  have h : starRingEnd ℂ (-normalPhase E) = (-normalPhase E)⁻¹ := by
    unfold normalPhase
    rw [neg_neg, ← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  rw [map_zpow₀, h, inv_zpow, zpow_neg]

private lemma ca_conj_rot (E : ℝ) (p : ObsPoly) :
    conjPoly (rotPoly E p) = rotPoly E (conjPoly p) := by
  refine hom_eq_hom (conjPoly.comp (rotPoly E : ObsPoly →ₐ[ℂ] ObsPoly).toRingHom)
    ((rotPoly E : ObsPoly →ₐ[ℂ] ObsPoly).toRingHom.comp conjPoly) ?_ ?_ p
  · ext r
    simp [ca_conj_C, rotPoly]
  · intro v
    have h1 : rotPoly E (X v) = C ((-normalPhase E) ^ v.idx) * X v := by simp [rotPoly]
    have h2 : rotPoly E (X v.neg) = C ((-normalPhase E) ^ v.neg.idx) * X v.neg := by
      simp [rotPoly]
    change conjPoly (rotPoly E (X v)) = rotPoly E (conjPoly (X v))
    rw [ca_conj_X, h1, h2, map_mul, ca_conj_C, ca_conj_X, ca_conj_zpow, ca_idx_neg]

private lemma ca_conj_zeroW (p : ObsPoly) : conjPoly (zeroW p) = zeroW (conjPoly p) := by
  refine hom_eq_hom (conjPoly.comp (zeroW : ObsPoly →ₐ[ℂ] ObsPoly).toRingHom)
    ((zeroW : ObsPoly →ₐ[ℂ] ObsPoly).toRingHom.comp conjPoly) ?_ ?_ p
  · ext r
    simp [ca_conj_C, zeroW]
  · intro v
    cases v <;> simp [zeroW, ca_conj_X, ObsVar.neg]

private lemma ca_conj_truncG (N : ℕ) (p : ObsPoly) :
    conjPoly (truncG N p) = truncG N (conjPoly p) := by
  ext d
  rw [ca_coeff_conj, ca_coeff_truncG, ca_coeff_truncG, ca_coeff_conj, ca_mapDomain_neg_gamma]
  split_ifs <;> simp

private lemma ca_conj_updPoly (E : ℝ) (N : ℕ) (p : ObsPoly) :
    conjPoly (updPoly E N p) = updPoly E N (conjPoly p) := by
  unfold updPoly
  rw [ca_conj_truncG, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_mul, map_mul, map_pow, ca_conj_C, Complex.conj_ofReal, ca_conj_X, ca_conj_zeroW,
    ← wickMap_conjPoly, ca_conj_rot]
  rfl

/-- Conjugation symmetry of a coordinate system: `\overline{σ(x_k)} = σ(x_{−k})`. -/
private def caSym (σ : ObsVar → ObsPoly) : Prop := ∀ v, conjPoly (σ v) = σ v.neg

private lemma ca_sym_X : caSym (X : ObsVar → ObsPoly) := fun v => ca_conj_X v

private lemma ca_revCoord_sym (N : ℕ) {σ : ObsVar → ObsPoly} (hσ : caSym σ) :
    ∀ r, caSym (revCoord N σ r)
  | 0 => ca_sym_X
  | r + 1 => by
    intro v
    have ih := ca_revCoord_sym N hσ r
    rw [ca_revCoord_succ, ca_revCoord_succ, ca_conj_truncG, map_sub conjPoly, ca_conj_X,
      ca_conj_bind₁ ih, map_sub conjPoly, hσ v, ca_conj_X]

private lemma ca_corrCoord_sym (E : ℝ) (R : ℕ) : caSym (corrCoord E R) := by
  intro v
  cases v with
  | m k => exact (conjPoly_corrObs E R k).1
  | f k => exact (conjPoly_corrObs E R k).2
  | w => exact ca_conj_X .w
  | γ => exact ca_conj_X .γ

/-- Every monomial of `[P_g F_k]_{≤R+2,0}` in the corrected coordinates contains some `F_j`
(Lemma 11.7 (i) [lg:lem:ideal] and (11.47) [lg:eq:current-coordinate-updates]), for every
energy. -/
theorem corrUpd_mem_fIdeal (E : ℝ) (R : ℕ) (k : NzInt) : corrUpd E R (.f k) ∈ fIdeal := by
  obtain ⟨-, -, -, -, -, -, hF, -⟩ := corrObs_form E R k
  exact ca_fIdeal_of_support_subset (ca_support_truncG _ _)
    (ca_bind₁_fIdeal _ (fun j => (corrObs_form E R j).2.2.2.2.2.2.2)
      (ca_updPoly_fIdeal E _ hF))

/-- Conjugation maps the corrected update of `x_k` to that of `x_{−k}` (Section 11.3.3
[lg:sec:general-state]), for every energy. -/
theorem conjPoly_corrUpd (E : ℝ) (R : ℕ) (v : ObsVar) :
    conjPoly (corrUpd E R v) = corrUpd E R v.neg := by
  unfold corrUpd
  have hinv : ∀ u, conjPoly (invCoord E R u) = invCoord E R u.neg :=
    ca_revCoord_sym _ (ca_corrCoord_sym E R) _
  rw [ca_conj_truncG, ca_conj_bind₁ hinv, ca_conj_updPoly, ca_corrCoord_sym E R v]

end LSBA
