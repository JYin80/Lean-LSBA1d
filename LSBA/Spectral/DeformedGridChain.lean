import LSBA.Spectral.DeformedSchurStep

/-!
# The continuity grid

The single-height conclusion propagates down the grid `η + k n^{−4}`, `k ≤ 2n⁴` (Appendix G.1
[app:relative-local-law-proof]).
-/

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section
open scoped Classical

namespace LSBA

/-- An entry is bounded by the operator norm. -/
private lemma deformedGridChain_norm_entry_le {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (i j : n) : ‖M i j‖ ≤ ‖M‖ := by
  have h := Matrix.l2_opNorm_mulVec M (EuclideanSpace.single j (1 : ℂ))
  have hn : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  rw [hn, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le ((EuclideanSpace.equiv n ℂ).symm
    (M.mulVec (EuclideanSpace.single j (1 : ℂ)).ofLp)) i
  convert this using 2
  simp

/-- The normalized trace is bounded by the operator norm. -/
private lemma deformedGridChain_norm_ntr_le {n : ℕ} (hn : 0 < n) (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖ntr X‖ ≤ ‖X‖ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold ntr
  rw [norm_mul, norm_inv, Fintype.card_fin, Complex.norm_natCast]
  have h1 : ‖X.trace‖ ≤ n * ‖X‖ := by
    calc ‖X.trace‖ ≤ ∑ i, ‖X i i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin n, ‖X‖ :=
          Finset.sum_le_sum fun i _ => deformedGridChain_norm_entry_le X i i
      _ = n * ‖X‖ := by simp
  calc (n : ℝ)⁻¹ * ‖X.trace‖ ≤ (n : ℝ)⁻¹ * (n * ‖X‖) := by gcongr
    _ = ‖X‖ := by field_simp

/-- The normalized trace is linear. -/
private lemma deformedGridChain_ntr_sub {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ntr (X - Y) = ntr X - ntr Y := by
  simp [ntr, Matrix.trace_sub, mul_sub]

/-- Resolvent identity in the spectral parameter at two heights:
`‖G(E + ia) - G(E + ib)‖ ≤ |a - b| a⁻¹ b⁻¹` for Hermitian `A`. -/
private lemma deformedGridChain_resolvent_diff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (E : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ‖resolventMat A (E + (a : ℂ) * Complex.I) - resolventMat A (E + b * Complex.I)‖ ≤
      |a - b| * a⁻¹ * b⁻¹ := by
  set za : ℂ := E + a * Complex.I with hza
  set zb : ℂ := E + b * Complex.I with hzb
  have hzaim : za.im = a := by simp [hza]
  have hzbim : zb.im = b := by simp [hzb]
  have hMa := sub_smul_mul_resolventMat hA (z := za) (by rw [hzaim]; exact ha.ne')
  have hMb := sub_smul_mul_resolventMat hA (z := zb) (by rw [hzbim]; exact hb.ne')
  have hGa := mul_eq_one_comm.mp hMa
  have hid : resolventMat A za - resolventMat A zb =
      (za - zb) • (resolventMat A za * resolventMat A zb) := by
    have h1 : resolventMat A za * (A - zb • (1 : Matrix ι ι ℂ)) * resolventMat A zb =
        resolventMat A za := by
      rw [Matrix.mul_assoc, hMb, Matrix.mul_one]
    have h2 : resolventMat A za * (A - za • (1 : Matrix ι ι ℂ)) * resolventMat A zb =
        resolventMat A zb := by
      rw [hGa, Matrix.one_mul]
    have h3 : (A - zb • (1 : Matrix ι ι ℂ)) - (A - za • (1 : Matrix ι ι ℂ)) =
        (za - zb) • (1 : Matrix ι ι ℂ) := by
      rw [sub_smul]; abel
    calc resolventMat A za - resolventMat A zb
        = resolventMat A za * (A - zb • (1 : Matrix ι ι ℂ)) * resolventMat A zb -
            resolventMat A za * (A - za • (1 : Matrix ι ι ℂ)) * resolventMat A zb := by
          rw [h1, h2]
      _ = resolventMat A za * ((A - zb • (1 : Matrix ι ι ℂ)) - (A - za • (1 : Matrix ι ι ℂ))) *
            resolventMat A zb := by
          rw [← Matrix.sub_mul, ← Matrix.mul_sub]
      _ = (za - zb) • (resolventMat A za * resolventMat A zb) := by
          rw [h3]; simp
  have hna : ‖resolventMat A za‖ ≤ a⁻¹ := norm_resolventMat_le hA ha (by rw [hzaim, abs_of_pos ha])
  have hnb : ‖resolventMat A zb‖ ≤ b⁻¹ := norm_resolventMat_le hA hb (by rw [hzbim, abs_of_pos hb])
  have hz : ‖za - zb‖ = |a - b| := by
    have : za - zb = (((a - b : ℝ)) : ℂ) * Complex.I := by simp [hza, hzb]; ring
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hid, norm_smul, hz, mul_assoc]
  calc |a - b| * ‖resolventMat A za * resolventMat A zb‖
      ≤ |a - b| * (‖resolventMat A za‖ * ‖resolventMat A zb‖) := by
        gcongr; exact norm_mul_le _ _
    _ ≤ |a - b| * (a⁻¹ * b⁻¹) := by gcongr

/-- One grid step of `⟨G⟩ - m_B` is at most `2 n^{-2}` when `n η ≥ 1` and `η ≤ a`. -/
private lemma deformedGridChain_drift {n : ℕ} (hn : 0 < n) {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (E : ℝ) {η a : ℝ} (hη : 0 < η)
    (hnη : 1 ≤ (n : ℝ) * η) (ha : η ≤ a) :
    ‖(ntr (resolventMat A (E + (a : ℂ) * Complex.I)) - mB B (E + (a : ℂ) * Complex.I)) -
      (ntr (resolventMat A (E + ((a + 1 / (n : ℝ) ^ 4 : ℝ) : ℂ) * Complex.I)) -
        mB B (E + ((a + 1 / (n : ℝ) ^ 4 : ℝ) : ℂ) * Complex.I))‖ ≤ 2 / (n : ℝ) ^ 2 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set d : ℝ := 1 / (n : ℝ) ^ 4 with hd
  have hd0 : 0 < d := by positivity
  have ha0 : 0 < a := lt_of_lt_of_le hη ha
  have hb0 : 0 < a + d := by linarith
  have hηinv : η⁻¹ ≤ n := by
    rw [inv_eq_one_div, div_le_iff₀ hη]; exact hnη
  have hainv : a⁻¹ ≤ n := (inv_anti₀ hη ha).trans hηinv
  have hbinv : (a + d)⁻¹ ≤ n := (inv_anti₀ hη (by linarith)).trans hηinv
  have habs : |a - (a + d)| = d := by
    rw [show a - (a + d) = -d by ring, abs_neg, abs_of_pos hd0]
  -- resolvent part
  have hG := deformedGridChain_resolvent_diff (hA) E ha0 hb0
  rw [habs] at hG
  have hG2 : ‖resolventMat A (E + (a : ℂ) * Complex.I) -
      resolventMat A (E + ((a + d : ℝ) : ℂ) * Complex.I)‖ ≤ 1 / (n : ℝ) ^ 2 := by
    refine hG.trans ?_
    calc d * a⁻¹ * (a + d)⁻¹ ≤ d * n * n := by gcongr
      _ = 1 / (n : ℝ) ^ 2 := by rw [hd]; field_simp
  have hT : ‖ntr (resolventMat A (E + (a : ℂ) * Complex.I)) -
      ntr (resolventMat A (E + ((a + d : ℝ) : ℂ) * Complex.I))‖ ≤ 1 / (n : ℝ) ^ 2 := by
    rw [← deformedGridChain_ntr_sub]
    exact (deformedGridChain_norm_ntr_le hn _).trans hG2
  -- profile part
  have hm := norm_mB_sub_mB_le hB E ha0 hb0
  rw [habs, min_eq_left (by linarith)] at hm
  have hm2 : ‖mB B (E + (a : ℂ) * Complex.I) -
      mB B (E + ((a + d : ℝ) : ℂ) * Complex.I)‖ ≤ 1 / (n : ℝ) ^ 2 := by
    refine hm.trans ?_
    calc d / a ≤ d / η := div_le_div_of_nonneg_left hd0.le hη ha
      _ = d * η⁻¹ := div_eq_mul_inv _ _
      _ ≤ d * n := by gcongr
      _ = 1 / (n : ℝ) ^ 3 := by rw [hd]; field_simp
      _ ≤ 1 / (n : ℝ) ^ 2 :=
          one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hn1 (by norm_num))
  have hsplit : (ntr (resolventMat A (E + (a : ℂ) * Complex.I)) -
        mB B (E + (a : ℂ) * Complex.I)) -
      (ntr (resolventMat A (E + ((a + d : ℝ) : ℂ) * Complex.I)) -
        mB B (E + ((a + d : ℝ) : ℂ) * Complex.I)) =
      (ntr (resolventMat A (E + (a : ℂ) * Complex.I)) -
        ntr (resolventMat A (E + ((a + d : ℝ) : ℂ) * Complex.I))) -
        (mB B (E + (a : ℂ) * Complex.I) - mB B (E + ((a + d : ℝ) : ℂ) * Complex.I)) := by ring
  rw [hsplit]
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ 1 / (n : ℝ) ^ 2 + 1 / (n : ℝ) ^ 2 := add_le_add hT hm2
    _ = 2 / (n : ℝ) ^ 2 := by ring

/-- Continuity step of the proof of Lemma G.1 [us:lem:local-law] for diagonal `B`: if the
diagonal and quadratic-form bounds of the single-height step hold at every height
`η_k = η + k n^{-4}`, `0 ≤ k ≤ 2 n⁴`, then the averaged and entrywise bounds hold at `η`. -/
theorem deformed_grid_chain (κ₀ Cstar : ℝ) (hκ₀ : 0 < κ₀) (hκ₀' : κ₀ < 2) (hC : 0 < Cstar) :
    ∃ ε₀ c₀ C : ℝ, 0 < ε₀ ∧ 0 < c₀ ∧ 0 < C ∧ ∃ n₁ : ℕ,
      ∀ (n : ℕ) (V B : Matrix (Fin n) (Fin n) ℂ) (ε E η t : ℝ), n₁ ≤ n → 0 < n →
        V.IsHermitian → B.IsDiag → 0 ≤ ε → ε ≤ ε₀ → DeformClass ε B → |E| ≤ 2 - κ₀ →
        0 < η → η ≤ Cstar → 1 ≤ (n : ℝ) * η → 1 ≤ t → t / Real.sqrt (n * η) ≤ c₀ →
        (∀ i, ‖V i i‖ ≤ t / Real.sqrt n) →
        (∀ k : ℕ, k ≤ 2 * n ^ 4 → ∀ i,
          ‖schurQuadDev (V - B) (E + (η + (k : ℝ) / (n : ℝ) ^ 4) * Complex.I) i‖ ≤
            t / n * Real.sqrt (∑ k', ∑ l, ‖resolventMat (minorMat (V - B) i)
              (E + (η + (k : ℝ) / (n : ℝ) ^ 4) * Complex.I) k' l‖ ^ 2)) →
        ‖ntr (resolventMat (V - B) (E + η * Complex.I)) - mB B (E + η * Complex.I)‖ ≤
            C * (t / Real.sqrt (n * η)) ∧
          ∀ i, ‖resolventMat (V - B) (E + η * Complex.I) i i - MB B (E + η * Complex.I) i i‖ ≤
            C * (t / Real.sqrt (n * η)) * ‖MB B (E + η * Complex.I) i i‖ ^ 2 := by
  obtain ⟨ε₀, c₀, C, hε₀, hc₀, hC0, hstep⟩ := deformed_schur_step κ₀ Cstar hκ₀ hκ₀' hC
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge (4 / c₀)
  refine ⟨ε₀, min c₀ (c₀ / (2 * C)), C, hε₀, lt_min hc₀ (by positivity), hC0, max n₀ 1, ?_⟩
  intro n V B ε E η t hn₁ hn hV hBd hε0 hεε hcl hE hη hηC hnη ht1 htc hVd hQ
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnn₀ : 4 / c₀ ≤ (n : ℝ) := by
    have : n₀ ≤ n := (le_max_left _ _).trans hn₁
    exact hn₀.trans (by exact_mod_cast this)
  have hBh : B.IsHermitian := hcl.1
  have hAh : (V - B).IsHermitian := hV.sub hBh
  -- the small error
  have herr : 2 / (n : ℝ) ^ 2 ≤ c₀ / 2 := by
    have h1 : 4 ≤ c₀ * n := by
      have := (div_le_iff₀ hc₀).mp hnn₀
      linarith
    have h2 : 2 / (n : ℝ) ^ 2 ≤ 2 / n :=
      div_le_div_of_nonneg_left (by norm_num) hn' (by nlinarith)
    have h3 : 2 / (n : ℝ) ≤ c₀ / 2 := by
      rw [div_le_div_iff₀ hn' (by norm_num)]; linarith
    exact h2.trans h3
  have htc' : t / Real.sqrt (n * η) ≤ c₀ / (2 * C) :=
    htc.trans (min_le_right _ _)
  have htc0 : t / Real.sqrt (n * η) ≤ c₀ := htc.trans (min_le_left _ _)
  have hCt : C * (t / Real.sqrt (n * η)) ≤ c₀ / 2 := by
    calc C * (t / Real.sqrt (n * η)) ≤ C * (c₀ / (2 * C)) := by gcongr
      _ = c₀ / 2 := by field_simp
  have hK : ∀ k : ℕ, k ≤ 2 * n ^ 4 → (k : ℝ) / (n : ℝ) ^ 4 ≤ 2 := by
    intro k hk
    rw [div_le_iff₀ (by positivity)]
    have : (k : ℝ) ≤ 2 * (n : ℝ) ^ 4 := by exact_mod_cast hk
    linarith
  have hk0 : ∀ k : ℕ, 0 ≤ (k : ℝ) / (n : ℝ) ^ 4 := fun k => by positivity
  -- the single-height step at height `k`
  have step_at : ∀ k : ℕ, k ≤ 2 * n ^ 4 →
      (2 ≤ η + (k : ℝ) / (n : ℝ) ^ 4 ∨
        ‖ntr (resolventMat (V - B) (E + ((η + (k : ℝ) / (n : ℝ) ^ 4 : ℝ) : ℂ) * Complex.I)) -
          mB B (E + ((η + (k : ℝ) / (n : ℝ) ^ 4 : ℝ) : ℂ) * Complex.I)‖ ≤ c₀) →
      ‖ntr (resolventMat (V - B) (E + ((η + (k : ℝ) / (n : ℝ) ^ 4 : ℝ) : ℂ) * Complex.I)) -
          mB B (E + ((η + (k : ℝ) / (n : ℝ) ^ 4 : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (t / Real.sqrt (n * (η + (k : ℝ) / (n : ℝ) ^ 4))) ∧
      ∀ i, ‖resolventMat (V - B) (E + ((η + (k : ℝ) / (n : ℝ) ^ 4 : ℝ) : ℂ) * Complex.I) i i -
          MB B (E + ((η + (k : ℝ) / (n : ℝ) ^ 4 : ℝ) : ℂ) * Complex.I) i i‖ ≤
        C * (t / Real.sqrt (n * (η + (k : ℝ) / (n : ℝ) ^ 4))) *
          ‖MB B (E + ((η + (k : ℝ) / (n : ℝ) ^ 4 : ℝ) : ℂ) * Complex.I) i i‖ ^ 2 := by
    intro k hk hdisj
    have hηk : η ≤ η + (k : ℝ) / (n : ℝ) ^ 4 := by linarith [hk0 k]
    have hηk0 : 0 < η + (k : ℝ) / (n : ℝ) ^ 4 := lt_of_lt_of_le hη hηk
    have hz : (E : ℂ) + (η + (k : ℝ) / (n : ℝ) ^ 4) * Complex.I =
        (E : ℂ) + ((η + (k : ℝ) / (n : ℝ) ^ 4 : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have hQk := hQ k hk
    rw [hz] at hQk
    refine hstep n V B ε E (η + (k : ℝ) / (n : ℝ) ^ 4) t hn hV hBd hε0 hεε hcl hE hηk0 ?_ ?_ ht1 ?_
      hVd hQk hdisj
    · linarith [hK k hk]
    · calc (1 : ℝ) ≤ n * η := hnη
        _ ≤ n * (η + (k : ℝ) / (n : ℝ) ^ 4) := by gcongr
    · refine le_trans ?_ htc0
      apply div_le_div_of_nonneg_left (by linarith) (by positivity)
      apply Real.sqrt_le_sqrt
      gcongr
  -- downward induction along the grid
  have key : ∀ j k : ℕ, k + j = 2 * n ^ 4 →
      (2 ≤ η + (k : ℝ) / (n : ℝ) ^ 4 ∨
        ‖ntr (resolventMat (V - B) (E + ((η + (k : ℝ) / (n : ℝ) ^ 4 : ℝ) : ℂ) * Complex.I)) -
          mB B (E + ((η + (k : ℝ) / (n : ℝ) ^ 4 : ℝ) : ℂ) * Complex.I)‖ ≤ c₀) := by
    intro j
    induction j with
    | zero =>
      intro k hk
      left
      have hk' : k = 2 * n ^ 4 := by omega
      subst hk'
      have : ((2 * n ^ 4 : ℕ) : ℝ) / (n : ℝ) ^ 4 = 2 := by
        push_cast; field_simp
      rw [this]; linarith
    | succ j ih =>
      intro k hk
      right
      have hk1 : k + 1 + j = 2 * n ^ 4 := by omega
      have hk1le : k + 1 ≤ 2 * n ^ 4 := by omega
      have hprev := (step_at (k + 1) hk1le (ih (k + 1) hk1)).1
      have hhk : η + ((k + 1 : ℕ) : ℝ) / (n : ℝ) ^ 4 =
          (η + (k : ℝ) / (n : ℝ) ^ 4) + 1 / (n : ℝ) ^ 4 := by
        push_cast; ring
      rw [hhk] at hprev
      have hdrift := deformedGridChain_drift hn hAh hBh E hη hnη
        (a := η + (k : ℝ) / (n : ℝ) ^ 4) (by linarith [hk0 k])
      have hrate : C * (t / Real.sqrt (n * ((η + (k : ℝ) / (n : ℝ) ^ 4) +
          1 / (n : ℝ) ^ 4))) ≤ c₀ / 2 := by
        refine le_trans ?_ hCt
        apply mul_le_mul_of_nonneg_left _ hC0.le
        apply div_le_div_of_nonneg_left (by linarith) (by positivity)
        apply Real.sqrt_le_sqrt
        have : 0 ≤ (k : ℝ) / (n : ℝ) ^ 4 := hk0 k
        have : 0 ≤ 1 / (n : ℝ) ^ 4 := by positivity
        have : (n : ℝ) * η ≤ n * ((η + (k : ℝ) / (n : ℝ) ^ 4) + 1 / (n : ℝ) ^ 4) := by
          gcongr
          linarith
        exact this
      set X := ntr (resolventMat (V - B) (E + ((η + (k : ℝ) / (n : ℝ) ^ 4 : ℝ) : ℂ) * Complex.I)) -
          mB B (E + ((η + (k : ℝ) / (n : ℝ) ^ 4 : ℝ) : ℂ) * Complex.I) with hX
      set Y := ntr (resolventMat (V - B)
          (E + (((η + (k : ℝ) / (n : ℝ) ^ 4) + 1 / (n : ℝ) ^ 4 : ℝ) : ℂ) * Complex.I)) -
          mB B (E + (((η + (k : ℝ) / (n : ℝ) ^ 4) + 1 / (n : ℝ) ^ 4 : ℝ) : ℂ) * Complex.I) with hY
      calc ‖X‖ = ‖Y + (X - Y)‖ := by congr 1; ring
        _ ≤ ‖Y‖ + ‖X - Y‖ := norm_add_le _ _
        _ ≤ c₀ / 2 + c₀ / 2 := add_le_add (hprev.trans hrate) (hdrift.trans herr)
        _ = c₀ := by ring
  have h0 := step_at 0 (Nat.zero_le _) (key (2 * n ^ 4) 0 (by omega))
  simpa using h0

end LSBA
