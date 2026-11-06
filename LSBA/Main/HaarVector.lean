import LSBA.Main.CountMono
import LSBA.Gauss.Sphere

/-!
# Common unitary conjugation

Appendix D.1 [subsec:pf_thm31]: common conjugation of the blocks conjugates the model by
`I_L ⊗ U`; for a unit vector `ψ`, the probability under the Haar
measure that `(I ⊗ U)ψ` has localization length `< W/8` is exponentially small; hence the Haar
average of the bad count of a conjugated Hermitian matrix with simple spectrum is small.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- `(I_L ⊗ U)* = I_L ⊗ U*`. -/
private theorem haarVector_star_kron (W L : ℕ) (U : Matrix (Fin W) (Fin W) ℂ) :
    star ((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ U) = (1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ star U := by
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.star_eq_conjTranspose]

/-- Appendix D.1 [subsec:pf_thm31]: common conjugation of the blocks conjugates the model by
`I_L ⊗ U`. -/
theorem Hmat_conjMap (g : ℝ) (W L : ℕ) (U : Matrix.unitaryGroup (Fin W) ℂ) (ω : Ω W L) :
    Hmat g W L (conjMap W L U ω) =
      ((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ)) * Hmat g W L ω *
        star ((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ)) := by
  have hUU : (U : Matrix (Fin W) (Fin W) ℂ) * star (U : Matrix (Fin W) (Fin W) ℂ) = 1 :=
    Unitary.coe_mul_star_self U
  have hV : gueBlock W L (conjMap W L U ω) = fun a =>
      (U : Matrix (Fin W) (Fin W) ℂ) * gueBlock W L ω a * star (U : Matrix (Fin W) (Fin W) ℂ) :=
    funext (gueBlock_conjMap W L U ω)
  rw [haarVector_star_kron]
  unfold Hmat Hdet
  rw [hV, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul]
  congr 2
  · rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.mul_one,
      hUU, Matrix.one_mul]
  · ext p q
    obtain ⟨a, α⟩ := p
    obtain ⟨b, β⟩ := q
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.one_apply, blockDiagOp, Matrix.of_apply]
    by_cases hab : a = b
    · subst hab
      simp [ite_mul, Finset.sum_ite_eq']
    · simp [ite_mul, Finset.sum_ite_eq', hab]

/-- `∑ |z_i|² = z* z`. -/
private theorem haarVector_sum_sq_eq {n : Type*} [Fintype n] (z : n → ℂ) :
    ((∑ i, ‖z i‖ ^ 2 : ℝ) : ℂ) = star z ⬝ᵥ z := by
  simp [dotProduct, Complex.conj_mul']

/-- A matrix with `M* M = 1` preserves `∑ |v_i|²`. -/
private theorem haarVector_sum_norm_mulVec {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : star M * M = 1) (v : n → ℂ) :
    ∑ i, ‖(M *ᵥ v) i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  have h : star (M *ᵥ v) ⬝ᵥ (M *ᵥ v) = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      ← Matrix.star_eq_conjTranspose, hM, Matrix.vecMul_one]
  exact_mod_cast (haarVector_sum_sq_eq _).trans (h.trans (haarVector_sum_sq_eq _).symm)

/-- `((I_L ⊗ U) ψ)(a, α) = (U ψ_a)_α` with `ψ_a = ψ(a, ·)`. -/
private theorem haarVector_kron_mulVec (W L : ℕ) (U : Matrix (Fin W) (Fin W) ℂ)
    (ψ : Fin L × Fin W → ℂ) (a : Fin L) (α : Fin W) :
    (((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ U) *ᵥ ψ) (a, α) = (U *ᵥ fun β => ψ (a, β)) α := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply, ite_mul]

/-- Reduction modulo `M` of a number below `2M`. -/
private theorem haarVector_mod_two {t M : ℕ} (h : t < 2 * M) :
    (t < M ∧ t % M = t) ∨ (M ≤ t ∧ t % M = t - M) := by
  rcases lt_or_ge t M with h1 | h1
  · exact Or.inl ⟨h1, Nat.mod_eq_of_lt h1⟩
  · refine Or.inr ⟨h1, ?_⟩
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]

/-- Comparison of the multiples `W a` and `W b`. -/
private theorem haarVector_mul_cases (W a b : ℕ) :
    (a + 1 ≤ b ∧ W * a + W ≤ W * b) ∨ (a = b ∧ W * a = W * b) ∨
      (a = b + 1 ∧ W * a = W * b + W) ∨ (b + 2 ≤ a ∧ W * b + 2 * W ≤ W * a) := by
  rcases lt_trichotomy a b with h | rfl | h
  · left
    have := Nat.mul_le_mul_left W (show a + 1 ≤ b by omega)
    exact ⟨h, by linarith [Nat.mul_succ W a]⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · rcases Nat.lt_or_ge (b + 1) a with h' | h'
    · right; right; right
      have := Nat.mul_le_mul_left W (show b + 2 ≤ a by omega)
      exact ⟨h', by nlinarith⟩
    · right; right; left
      obtain rfl : a = b + 1 := by omega
      exact ⟨rfl, by ring⟩

/-- Arithmetic form of the window inclusion below. -/
private theorem haarVector_window_nat {W L a a₀ β α₀ ℓ w₀ : ℕ} (ha : a < L) (ha₀ : a₀ < L)
    (hβ : β < W) (hα : α₀ < W) (hℓ : ℓ ≤ w₀) (hw : w₀ < W)
    (hi : (β + W * a + L * W - (α₀ + W * a₀)) % (L * W) < ℓ) :
    (β + W - α₀) % W < w₀ ∧ (a = a₀ ∨ a = (a₀ + 1) % L) := by
  have hLW : L * W = W * L := Nat.mul_comm L W
  have h1 := Nat.mul_le_mul_left W (show a + 1 ≤ L by omega)
  have h2 := Nat.mul_le_mul_left W (show a₀ + 1 ≤ L by omega)
  rw [Nat.mul_succ] at h1 h2
  have hc := haarVector_mul_cases W a a₀
  have hc0 := haarVector_mul_cases W a 0
  have hcL := haarVector_mul_cases W (a₀ + 1) L
  rw [Nat.mul_succ] at hcL
  rw [Nat.mul_zero] at hc0
  have hm := haarVector_mod_two (t := β + W * a + L * W - (α₀ + W * a₀)) (M := L * W) (by omega)
  have hs := haarVector_mod_two (t := β + W - α₀) (M := W) (by omega)
  have hL : (a₀ + 1 < L ∧ (a₀ + 1) % L = a₀ + 1) ∨ (a₀ + 1 = L ∧ (a₀ + 1) % L = 0) := by
    rcases Nat.lt_or_ge (a₀ + 1) L with h | h
    · exact Or.inl ⟨h, Nat.mod_eq_of_lt h⟩
    · exact Or.inr ⟨by omega, by rw [show a₀ + 1 = L by omega, Nat.mod_self]⟩
  generalize (β + W * a + L * W - (α₀ + W * a₀)) % (L * W) = k at hi hm
  generalize (β + W - α₀) % W = k' at hs ⊢
  generalize (a₀ + 1) % L = k'' at hL ⊢
  generalize W * a = P at *
  generalize W * a₀ = P₀ at *
  generalize W * (a₀ + 1) = P₁ at *
  generalize L * W = Q at *
  generalize W * L = Q' at *
  omega

/-- A cyclic interval of `ℤ_{LW}` of length `ℓ ≤ w₀ < W`, in the coordinates (1.1) [eq:blocks],
lies in two consecutive blocks, inside one cyclic window of `w₀` orbitals. -/
private theorem haarVector_window (W L : ℕ) (a a₀ : Fin L) (β α₀ : Fin W) {ℓ w₀ : ℕ}
    (hℓ : ℓ ≤ w₀) (hw : w₀ < W)
    (hi : finProdFinEquiv (a, β) ∈ cycInterval (L * W) (finProdFinEquiv (a₀, α₀)) ℓ) :
    β ∈ cycInterval W α₀ w₀ ∧ ((a : ℕ) = a₀ ∨ (a : ℕ) = ((a₀ : ℕ) + 1) % L) := by
  simp only [cycInterval, Finset.mem_filter, Finset.mem_univ, true_and,
    finProdFinEquiv_apply_val] at hi ⊢
  exact haarVector_window_nat a.isLt a₀.isLt β.isLt α₀.isLt hℓ hw hi

/-- The mass of a cyclic interval of length `ℓ ≤ w₀ < W` is at most the sum of the masses of one
cyclic window of `w₀` orbitals in two blocks. -/
private theorem haarVector_interval_le (W L : ℕ) (φ : Fin L × Fin W → ℂ) (x : Fin (L * W))
    {ℓ w₀ : ℕ} (hℓ : ℓ ≤ w₀) (hw : w₀ < W) (hL : 0 < L) :
    ∑ i ∈ cycInterval (L * W) x ℓ, ‖φ (finProdFinEquiv.symm i)‖ ^ 2 ≤
      ∑ β ∈ cycInterval W (finProdFinEquiv.symm x).2 w₀, ‖φ ((finProdFinEquiv.symm x).1, β)‖ ^ 2 +
        ∑ β ∈ cycInterval W (finProdFinEquiv.symm x).2 w₀,
          ‖φ (⟨((finProdFinEquiv.symm x).1 + 1 : ℕ) % L, Nat.mod_lt _ hL⟩, β)‖ ^ 2 := by
  set a₀ := (finProdFinEquiv.symm x).1
  set α₀ := (finProdFinEquiv.symm x).2
  set a₁ : Fin L := ⟨((a₀ : ℕ) + 1) % L, Nat.mod_lt _ hL⟩
  set S := cycInterval W α₀ w₀
  have hx : x = finProdFinEquiv (a₀, α₀) := (Equiv.apply_symm_apply _ x).symm
  have hsub : (cycInterval (L * W) x ℓ).map finProdFinEquiv.symm.toEmbedding ⊆
      ({a₀} ×ˢ S) ∪ ({a₁} ×ˢ S) := by
    intro q hq
    rw [Finset.mem_map] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    obtain ⟨⟨a, β⟩, rfl⟩ := finProdFinEquiv.surjective i
    rw [hx] at hi
    obtain ⟨hβ, ha⟩ := haarVector_window W L a a₀ β α₀ hℓ hw hi
    simp only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply, Finset.mem_union,
      Finset.mem_product, Finset.mem_singleton]
    rcases ha with ha | ha
    · exact Or.inl ⟨Fin.ext ha, hβ⟩
    · exact Or.inr ⟨Fin.ext ha, hβ⟩
  have hnn : ∀ q : Fin L × Fin W, 0 ≤ ‖φ q‖ ^ 2 := fun q => by positivity
  calc ∑ i ∈ cycInterval (L * W) x ℓ, ‖φ (finProdFinEquiv.symm i)‖ ^ 2
      = ∑ q ∈ (cycInterval (L * W) x ℓ).map finProdFinEquiv.symm.toEmbedding, ‖φ q‖ ^ 2 := by
        rw [Finset.sum_map]
        rfl
    _ ≤ ∑ q ∈ ({a₀} ×ˢ S) ∪ ({a₁} ×ˢ S), ‖φ q‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ => hnn q
    _ ≤ ∑ q ∈ {a₀} ×ˢ S, ‖φ q‖ ^ 2 + ∑ q ∈ {a₁} ×ˢ S, ‖φ q‖ ^ 2 := by
        rw [← Finset.sum_union_inter]
        exact le_add_of_nonneg_right (Finset.sum_nonneg fun q _ => hnn q)
    _ = _ := by
        rw [Finset.sum_product, Finset.sum_product, Finset.sum_singleton, Finset.sum_singleton]

/-- Appendix D.1 [subsec:pf_thm31], fixed vector: for a unit `ψ`, the Haar probability that
`(I_L ⊗ U) ψ` has length `< W/8` is at most `4 W e^{-W/25}`. -/
theorem haarU_ell_kron_lt (W L : ℕ) (ψ : Fin L × Fin W → ℂ) (hψ : ∑ x, ‖ψ x‖ ^ 2 = 1) :
    haarU W {U | ((ell W L (((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ
        (U : Matrix (Fin W) (Fin W) ℂ)) *ᵥ ψ) : ℕ) : ℝ) < (W : ℝ) / 8} ≤
      ENNReal.ofReal (4 * W * Real.exp (-(W : ℝ) / 25)) := by
  have hLW : 0 < L * W := by
    rcases Nat.eq_zero_or_pos (L * W) with h | h
    · exfalso
      have : IsEmpty (Fin L × Fin W) := by
        rw [← Fintype.card_eq_zero_iff, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, h]
      rw [Finset.univ_eq_empty, Finset.sum_empty] at hψ
      exact zero_ne_one hψ
    · exact h
  have hL : 0 < L := Nat.pos_of_mul_pos_right hLW
  have hW : 0 < W := Nat.pos_of_mul_pos_left hLW
  set w₀ := W / 8 with hw₀def
  have hw₀ : w₀ < W := Nat.div_lt_self hW (by norm_num)
  have h8 : 8 * w₀ ≤ W := by omega
  set v : Fin L → Fin W → ℂ := fun a β => ψ (a, β) with hvdef
  have hv1 : ∑ a, ∑ β, ‖v a β‖ ^ 2 = 1 := by rw [← hψ, Fintype.sum_prod_type]
  have hva : ∀ a, ∑ β, ‖v a β‖ ^ 2 ≤ 1 := fun a => by
    rw [← hv1]
    exact Finset.single_le_sum (f := fun a => ∑ β, ‖v a β‖ ^ 2)
      (fun a _ => Finset.sum_nonneg fun β _ => by positivity) (Finset.mem_univ a)
  set Hv : Finset (Fin L) := univ.filter fun a => (1 / 4 : ℝ) ≤ ∑ β, ‖v a β‖ ^ 2 with hHv
  have hHv4 : (#Hv : ℝ) ≤ 4 := by
    have h1 : (#Hv : ℝ) * (1 / 4) ≤ ∑ a ∈ Hv, ∑ β, ‖v a β‖ ^ 2 := by
      calc (#Hv : ℝ) * (1 / 4) = ∑ a ∈ Hv, (1 / 4 : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum fun a ha => (Finset.mem_filter.mp ha).2
    have h2 : ∑ a ∈ Hv, ∑ β, ‖v a β‖ ^ 2 ≤ 1 := by
      rw [← hv1]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun a _ _ => Finset.sum_nonneg fun β _ => by positivity
    linarith
  set E : Fin L × Fin W → Set (Matrix.unitaryGroup (Fin W) ℂ) := fun p =>
    {U | (∑ i, ‖v p.1 i‖ ^ 2) / 4 ≤
      ∑ i ∈ cycInterval W p.2 w₀, ‖(U : Matrix (Fin W) (Fin W) ℂ).mulVec (v p.1) i‖ ^ 2}
    with hEdef
  have hsub : {U : Matrix.unitaryGroup (Fin W) ℂ | ((ell W L (((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ
        (U : Matrix (Fin W) (Fin W) ℂ)) *ᵥ ψ) : ℕ) : ℝ) < (W : ℝ) / 8} ⊆
      ⋃ p ∈ Hv ×ˢ (univ : Finset (Fin W)), E p := by
    intro U hU
    rw [Set.mem_ofPred_eq] at hU
    set φ := ((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ)) *ᵥ ψ with hφ
    have hφa : ∀ a β, φ (a, β) = ((U : Matrix (Fin W) (Fin W) ℂ) *ᵥ v a) β := fun a β =>
      haarVector_kron_mulVec W L _ ψ a β
    have hUU : star (U : Matrix (Fin W) (Fin W) ℂ) * U = 1 := Unitary.coe_star_mul_self U
    have hnorm : ∀ a, ∑ β, ‖((U : Matrix (Fin W) (Fin W) ℂ) *ᵥ v a) β‖ ^ 2 =
        ∑ β, ‖v a β‖ ^ 2 := fun a => haarVector_sum_norm_mulVec hUU (v a)
    set p : Fin (L * W) → ℝ := fun i => ‖φ (finProdFinEquiv.symm i)‖ ^ 2 with hp
    have hell : ell W L φ = ellMass (L * W) p := rfl
    have hℓ : ellMass (L * W) p ≤ w₀ := by
      rw [hell] at hU
      have : (8 * ellMass (L * W) p : ℝ) < W := by linarith
      have : 8 * ellMass (L * W) p < W := by exact_mod_cast this
      omega
    have htot : (1 : ℝ) / 2 ≤ ∑ i, p i := by
      have : ∑ i, p i = 1 := by
        rw [hp, ← hv1, ← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← hnorm a]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [Equiv.symm_apply_apply, hφa]
      linarith
    obtain ⟨x, hx⟩ := exists_mass_ellMass hLW p htot
    have hI := hx.trans (haarVector_interval_le W L φ x hℓ hw₀ hL)
    set a₀ := (finProdFinEquiv.symm x).1
    set α₀ := (finProdFinEquiv.symm x).2
    set a₁ : Fin L := ⟨((a₀ : ℕ) + 1) % L, Nat.mod_lt _ hL⟩
    have hexists : ∃ a, (1 / 4 : ℝ) ≤
        ∑ β ∈ cycInterval W α₀ w₀, ‖((U : Matrix (Fin W) (Fin W) ℂ) *ᵥ v a) β‖ ^ 2 := by
      simp only [hφa] at hI
      by_contra hcon
      push Not at hcon
      have := hcon a₀
      have := hcon a₁
      linarith
    obtain ⟨a, ha⟩ := hexists
    have hle : ∑ β ∈ cycInterval W α₀ w₀, ‖((U : Matrix (Fin W) (Fin W) ℂ) *ᵥ v a) β‖ ^ 2 ≤
        ∑ β, ‖v a β‖ ^ 2 := by
      rw [← hnorm a]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun β _ _ => by positivity
    have haH : a ∈ Hv := Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha.trans hle⟩
    refine Set.mem_biUnion (x := (a, α₀)) (Finset.mem_product.mpr ⟨haH, Finset.mem_univ _⟩) ?_
    change (∑ i, ‖v a i‖ ^ 2) / 4 ≤
      ∑ i ∈ cycInterval W α₀ w₀, ‖(U : Matrix (Fin W) (Fin W) ℂ).mulVec (v a) i‖ ^ 2
    have := hva a
    linarith
  have hE : ∀ p ∈ Hv ×ˢ (univ : Finset (Fin W)),
      haarU W (E p) ≤ ENNReal.ofReal (Real.exp (-(W : ℝ) / 25)) := by
    intro p hp
    have hpH := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
    have hne : v p.1 ≠ 0 := by
      intro h0
      rw [h0] at hpH
      simp at hpH
      norm_num at hpH
    refine (haarU_mass_tail W (v p.1) hne (cycInterval W p.2 w₀)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [card_cycInterval W p.2 w₀ hw₀.le]
    exact mass_tail_le_exp W w₀ h8
  calc haarU W _ ≤ haarU W (⋃ p ∈ Hv ×ˢ (univ : Finset (Fin W)), E p) := measure_mono hsub
    _ ≤ ∑ p ∈ Hv ×ˢ (univ : Finset (Fin W)), haarU W (E p) := measure_biUnion_finset_le _ _
    _ ≤ ∑ p ∈ Hv ×ˢ (univ : Finset (Fin W)), ENNReal.ofReal (Real.exp (-(W : ℝ) / 25)) :=
        Finset.sum_le_sum hE
    _ = ENNReal.ofReal (((#Hv * W : ℕ) : ℝ) * Real.exp (-(W : ℝ) / 25)) := by
        rw [Finset.sum_const, Finset.card_product, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (4 * W * Real.exp (-(W : ℝ) / 25)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        push_cast
        gcongr

/-- `Q A Q*` is Hermitian for Hermitian `A`. -/
private theorem haarVector_conj_isHermitian {n : Type*} [Fintype n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (Q : Matrix n n ℂ) : (Q * A * star Q).IsHermitian := by
  unfold Matrix.IsHermitian at hA ⊢
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hA, Matrix.mul_assoc]

/-- The eigenvalues of a unitary conjugate of a Hermitian matrix are those of the matrix. -/
private theorem haarVector_eigenvalues_conj {n : Type*} [Fintype n] [DecidableEq n]
    {A Q : Matrix n n ℂ} (hQ : star Q * Q = 1) (hA : A.IsHermitian)
    (hB : (Q * A * star Q).IsHermitian) : hB.eigenvalues = hA.eigenvalues := by
  rw [Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff, Matrix.mul_assoc,
    Matrix.charpoly_mul_comm, Matrix.mul_assoc, hQ, Matrix.mul_one]

/-- Appendix D.1 [subsec:pf_thm31], fixed matrix with simple spectrum: the Haar average of the
bad count of `(I_L ⊗ U) A (I_L ⊗ U)*` with threshold `r ≤ W/8`. -/
theorem lintegral_badCount_conj_le (W L : ℕ) {A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hA : A.IsHermitian) (hinj : Function.Injective hA.eigenvalues) (J : Set ℝ) {r : ℝ}
    (hr : r ≤ (W : ℝ) / 8) :
    ∫⁻ U, (badCount W L (((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ)) * A *
        star ((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ))) J r : ℝ≥0∞)
        ∂(haarU W) ≤
      ENNReal.ofReal ((L : ℝ) * W * (4 * W * Real.exp (-(W : ℝ) / 25))) := by
  set c : ℝ := 4 * W * Real.exp (-(W : ℝ) / 25) with hc
  set vk : Fin L × Fin W → Fin L × Fin W → ℂ := fun k => ⇑(hA.eigenvectorBasis k) with hvkdef
  have hvk : ∀ k, ∑ x, ‖vk k x‖ ^ 2 = 1 := fun k => by
    have h := (hA.eigenvectorBasis).norm_eq_one k
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
    exact h
  set Ev : Fin L × Fin W → Set (Matrix.unitaryGroup (Fin W) ℂ) := fun k =>
    {U | ((ell W L (((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ)) *ᵥ vk k) :
      ℕ) : ℝ) < (W : ℝ) / 8} with hEv
  have hpt : ∀ U : Matrix.unitaryGroup (Fin W) ℂ,
      (badCount W L (((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ)) * A *
        star ((1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ))) J r : ℝ≥0∞) ≤
      ∑ k, (toMeasurable (haarU W) (Ev k)).indicator 1 U := by
    intro U
    set Q := (1 : Matrix (Fin L) (Fin L) ℂ) ⊗ₖ (U : Matrix (Fin W) (Fin W) ℂ) with hQdef
    have hQ : star Q * Q = 1 := by
      rw [hQdef, haarVector_star_kron, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
        Unitary.coe_star_mul_self U, Matrix.one_kronecker_one]
    have hB : (Q * A * star Q).IsHermitian := haarVector_conj_isHermitian hA Q
    have hev := haarVector_eigenvalues_conj hQ hA hB
    have hinjB : Function.Injective hB.eigenvalues := hev ▸ hinj
    have hψ : ∀ k, (Q * A * star Q) *ᵥ (Q *ᵥ vk k) = (hB.eigenvalues k : ℂ) • (Q *ᵥ vk k) := by
      intro k
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (Q * A), hQ, Matrix.mul_one,
        ← Matrix.mulVec_mulVec, hvkdef, hA.mulVec_eigenvectorBasis, hev,
        ← Complex.coe_smul, Matrix.mulVec_smul]
    have hn : ∀ k, ∑ x, ‖(Q *ᵥ vk k) x‖ ^ 2 = 1 := fun k =>
      (haarVector_sum_norm_mulVec hQ _).trans (hvk k)
    rw [badCount_eq_of_injective hB hinjB (fun k => Q *ᵥ vk k) hψ hn J r,
      Finset.card_eq_sum_ones, Nat.cast_sum]
    calc ∑ k ∈ univ.filter (fun k => hB.eigenvalues k ∈ J ∧ (ell W L (Q *ᵥ vk k) : ℝ) < r),
          ((1 : ℕ) : ℝ≥0∞)
        ≤ ∑ k ∈ univ.filter (fun k => hB.eigenvalues k ∈ J ∧ (ell W L (Q *ᵥ vk k) : ℝ) < r),
          (toMeasurable (haarU W) (Ev k)).indicator 1 U := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' := (Finset.mem_filter.mp hk).2.2
          have hU : U ∈ Ev k := by
            change ((ell W L (Q *ᵥ vk k) : ℕ) : ℝ) < (W : ℝ) / 8
            exact lt_of_lt_of_le hk' hr
          rw [Set.indicator_of_mem (subset_toMeasurable _ _ hU)]
          simp
      _ ≤ ∑ k, (toMeasurable (haarU W) (Ev k)).indicator 1 U :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => zero_le
  calc _ ≤ ∫⁻ U, ∑ k, (toMeasurable (haarU W) (Ev k)).indicator 1 U ∂(haarU W) :=
        lintegral_mono hpt
    _ = ∑ k, ∫⁻ U, (toMeasurable (haarU W) (Ev k)).indicator 1 U ∂(haarU W) :=
        lintegral_finsetSum _ fun k _ =>
          measurable_one.indicator (measurableSet_toMeasurable _ _)
    _ = ∑ k, haarU W (Ev k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [lintegral_indicator_one (measurableSet_toMeasurable _ _), measure_toMeasurable]
    _ ≤ ∑ _k : Fin L × Fin W, ENNReal.ofReal c :=
        Finset.sum_le_sum fun k _ => haarU_ell_kron_lt W L (vk k) (hvk k)
    _ = ENNReal.ofReal ((L : ℝ) * W * c) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul,
          show (L : ℝ) * W * c = ((L * W : ℕ) : ℝ) * c by push_cast; ring,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

end LSBA
