import LSBA.Loop.Generator
import LSBA.Primitive.Tree

/-!
# The error hierarchy in generator form

The primitive equation (5.10) [fo:eq:primitive] at a time `u` as a predicate on loop families,
the loop errors `D = ℒ − 𝒦`, the generator form of (5.17) [fo:eq:error-hierarchy] for any family
satisfying it, the split of the adjacent cut terms into `Θ` of (5.14) [fo:eq:generator], the
generator identity behind the stopped Duhamel expression after (C.21)
[fo:eq:propagated-pair-bracket], and the propagated bracket of (C.21)
[fo:eq:propagated-pair-bracket].
-/

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The primitive equation (5.10) [fo:eq:primitive] at time `u`, for every length. -/
def IsPrimDeriv (γ : ℝ) (W L : ℕ) (K : ℝ → LoopFam L) (u : ℝ) : Prop :=
  ∀ (n : ℕ) (a : Fin n → Fin L) (σ : Fin n → Bool),
    HasDerivAt (fun r => K r n a σ) (((γ * W : ℝ) : ℂ) * cutSumFam (K u) a σ) u

/-- The loop errors `D = ℒ - 𝒦` at `(u, M)`. -/
def errFam (g E : ℝ) (m : ℂ) {W L : ℕ} (K : LoopFam L) (u : ℝ)
    (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) : LoopFam L :=
  fun n b τ => loopTr (resolventMat M (zChar g E m u)) b τ - K n b τ

/-- Moving along a block direction from `M`: the slice at `e • δ_{(c,κ)}` is `M + e T_{c,κ}`. -/
private theorem errorHierarchy_slice_line {W L : ℕ}
    (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (c : Fin L) (κ : Fin W × Fin W) (e : ℝ) :
    blockSlice W L M (e • Pi.single (c, κ.1, κ.2) 1) = M + (e : ℂ) • blockBasis W L c κ := by
  unfold blockSlice
  congr 1
  rw [Finset.sum_eq_single c, Finset.sum_eq_single κ]
  · simp
  · intro κ' _ hκ'
    have : (c, κ'.1, κ'.2) ≠ (c, κ.1, κ.2) := by
      intro h; apply hκ'; simp only [Prod.mk.injEq, true_and] at h; exact Prod.ext h.1 h.2
    simp [this]
  · simp
  · intro c' _ hc'
    refine Finset.sum_eq_zero fun κ' _ => ?_
    have : (c', κ'.1, κ'.2) ≠ (c, κ.1, κ.2) := by
      intro h; apply hc'; simp only [Prod.mk.injEq] at h; exact h.1
    simp [this]
  · simp

/-- A resolvent loop at the characteristic is differentiable in time at `u < 1`, and twice
differentiable along every block direction. -/
private theorem errorHierarchy_smooth (g E : ℝ) (m : ℂ) (hm : 0 < m.im) {W L k : ℕ} {u : ℝ}
    (hu : u < 1) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    (a : Fin k → Fin L) (σ : Fin k → Bool) :
    DifferentiableAt ℝ (fun r => resLoop g E m a σ r M) u ∧
    ∀ (c : Fin L) (κ : Fin W × Fin W),
      (∀ e : ℝ, DifferentiableAt ℝ
        (fun e : ℝ => resLoop g E m a σ u (M + (e : ℂ) • blockBasis W L c κ)) e) ∧
      DifferentiableAt ℝ
        (deriv (fun e : ℝ => resLoop g E m a σ u (M + (e : ℂ) • blockBasis W L c κ))) 0 := by
  have hC := heatClass_loopTr W L k M hM g E m hm a σ (a' := u - 1) (b' := (u + 1) / 2)
    (by linarith)
  have hu' : u ∈ Set.Ioo (u - 1) ((u + 1) / 2) := ⟨by linarith, by linarith⟩
  have h0 : blockSlice W L M 0 = M := by simp [blockSlice]
  obtain ⟨Fu, hFu, -⟩ := hC.du
  obtain ⟨DF, D2F, hD, hD2, -⟩ := hC.dx
  refine ⟨?_, fun c κ => ?_⟩
  · have := (hFu u hu' 0).differentiableAt
    simpa [resLoop, h0] using this
  · set v : Ω W L := Pi.single (c, κ.1, κ.2) 1 with hv
    have hφ : ∀ e : ℝ, HasDerivAt (fun e : ℝ => e • v) v e := fun e => by
      simpa using (hasDerivAt_id e).smul_const v
    have hf : (fun e : ℝ => resLoop g E m a σ u (M + (e : ℂ) • blockBasis W L c κ)) =
        (fun x => loopTr (resolventMat (blockSlice W L M x) (zChar g E m u)) a σ) ∘
          (fun e : ℝ => e • v) := by
      funext e
      simp only [Function.comp, hv, errorHierarchy_slice_line, resLoop]
    have hder : ∀ e : ℝ, HasDerivAt
        (fun e : ℝ => resLoop g E m a σ u (M + (e : ℂ) • blockBasis W L c κ))
        (DF u (e • v) v) e := fun e => by
      rw [hf]; exact (hD u hu' (e • v)).comp_hasDerivAt e (hφ e)
    refine ⟨fun e => (hder e).differentiableAt, ?_⟩
    have hdf : deriv (fun e : ℝ => resLoop g E m a σ u (M + (e : ℂ) • blockBasis W L c κ)) =
        fun e => DF u (e • v) v := funext fun e => (hder e).deriv
    rw [hdf]
    have h1 : DifferentiableAt ℝ (fun e : ℝ => DF u (e • v)) 0 :=
      (hD2 u hu' ((0 : ℝ) • v)).differentiableAt.comp (0 : ℝ) (hφ 0).differentiableAt
    exact h1.clm_apply (differentiableAt_const v)

/-- With `ℒ = 𝒦 + D`, the quadratic cut sum of `ℒ` minus that of `𝒦` is the cut term of (5.17)
[fo:eq:error-hierarchy]. -/
private theorem errorHierarchy_cut_sub {L k : ℕ} (K D : LoopFam L) (a : Fin k → Fin L)
    (σ : Fin k → Bool) :
    cutSumFam (fun n b τ => K n b τ + D n b τ) a σ - cutSumFam K a σ = cutErrSum K D a σ := by
  unfold cutSumFam cutErrSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  · simp

/-- (5.17) [fo:eq:error-hierarchy] in generator form. -/
theorem blockGen_errorLoop (g E : ℝ) (m : ℂ) (hm : 0 < m.im) {W L k : ℕ} {u : ℝ} (hu : u < 1)
    {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian) (K : ℝ → LoopFam L)
    (hK : IsPrimDeriv (gammaG g) W L K u) (a : Fin k → Fin L) (σ : Fin k → Bool) :
    blockGen W L (gammaG g) (fun r N => resLoop g E m a σ r N - K r k a σ) u M =
      lightW g E m a σ u M +
        ((gammaG g * W : ℝ) : ℂ) * cutErrSum (K u) (errFam g E m (K u) u M) a σ := by
  obtain ⟨hT, -⟩ := errorHierarchy_smooth g E m hm hu hM (W := W) a σ
  have hKd := hK k a σ
  have htime : deriv (fun r => resLoop g E m a σ r M - K r k a σ) u =
      deriv (fun r => resLoop g E m a σ r M) u -
        ((gammaG g * W : ℝ) : ℂ) * cutSumFam (K u) a σ := by
    exact (hT.hasDerivAt.sub hKd).deriv
  have hline : ∀ (c : Fin L) (κ : Fin W × Fin W),
      iteratedDeriv 2 (fun e : ℝ =>
        resLoop g E m a σ u (M + (e : ℂ) • blockBasis W L c κ) - K u k a σ) 0 =
      iteratedDeriv 2 (fun e : ℝ => resLoop g E m a σ u (M + (e : ℂ) • blockBasis W L c κ)) 0 := by
    intro c κ
    rw [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_one,
      deriv_sub_const_fun]
  have hG := blockGen_loopTr g E m hm hu hM (W := W) a σ
  have hcut := errorHierarchy_cut_sub (K u) (errFam g E m (K u) u M) a σ
  have he : (fun n b τ => K u n b τ + errFam g E m (K u) u M n b τ) =
      fun n b τ => loopTr (resolventMat M (zChar g E m u)) b τ := by
    funext n b τ; simp [errFam]
  rw [he] at hcut
  unfold blockGen at hG ⊢
  simp only [hline]
  rw [htime]
  linear_combination hG + ((gammaG g * W : ℝ) : ℂ) * hcut

/-- Two values of a loop family agree when the lengths agree and the words agree position by
position. -/
private theorem errorHierarchy_fam_congr {L : ℕ} (F : LoopFam L) {n n' : ℕ} (h : n = n')
    (x : Fin n → Fin L) (y : Fin n → Bool) (x' : Fin n' → Fin L) (y' : Fin n' → Bool)
    (hx : ∀ (p : ℕ) (hp : p < n) (hp' : p < n'), x ⟨p, hp⟩ = x' ⟨p, hp'⟩)
    (hy : ∀ (p : ℕ) (hp : p < n) (hp' : p < n'), y ⟨p, hp⟩ = y' ⟨p, hp'⟩) :
    F n x y = F n' x' y' := by
  subst h
  have e1 : x = x' := funext fun p => hx p.1 p.2 p.2
  have e2 : y = y' := funext fun p => hy p.1 p.2 p.2
  rw [e1, e2]

/-- At an adjacent pair `(i, i+1)`, Cut_L is the word with `a_i` replaced by `c`. -/
private theorem errorHierarchy_adj_L {L k : ℕ} (F : LoopFam L) (a : Fin k → Fin L)
    (σ : Fin k → Bool) (i j : Fin k) (hij : j.val = i.val + 1) (c : Fin L) :
    F _ (cutLLab a i j c) (cutLSgn σ i j) = F k (Function.update a i c) σ := by
  apply errorHierarchy_fam_congr F (by omega)
  · intro p hp hp'
    simp only [cutLLab, Function.update_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega) |
      exact congrArg Fin.val (congrArg a (Fin.ext (by first | omega | (simp; omega))))
  · intro p hp hp'
    simp only [cutLSgn]
    split_ifs <;> first | rfl | exact congrArg σ (Fin.ext (by first | omega | (simp; omega)))

/-- At an adjacent pair `(i, i+1)`, Cut_R is the two-loop `(a_i, c; σ_i, σ_{i+1})`. -/
private theorem errorHierarchy_adj_R {L k : ℕ} (F : LoopFam L) (a : Fin k → Fin L)
    (σ : Fin k → Bool) (i j : Fin k) (hij : j.val = i.val + 1) (c : Fin L) :
    F _ (cutRLab a i j c) (cutRSgn σ i j) = F 2 ![a i, c] ![σ i, σ j] := by
  apply errorHierarchy_fam_congr F (by omega)
  · intro p hp hp'
    rcases p with _ | _ | p
    · simp only [cutRLab]
      rw [dite_eq_left (by omega)]
      simp
    · simp only [cutRLab]
      rw [dite_eq_right (by omega)]
      simp
    · omega
  · intro p hp hp'
    rcases p with _ | _ | p
    · simp [cutRSgn]
    · simp only [cutRSgn]
      have : (⟨1, hp'⟩ : Fin 2) = 1 := rfl
      rw [this, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact congrArg σ (Fin.ext (by first | omega | (simp; omega)))
    · omega

/-- At the cyclic pair `(0, k-1)`, Cut_L is the two-loop `(c, a_{k-1}; σ_0, σ_{k-1})`. -/
private theorem errorHierarchy_cyc_L {L k : ℕ} (F : LoopFam L) (a : Fin k → Fin L)
    (σ : Fin k → Bool) (i j : Fin k) (hi : i.val = 0) (hj : j.val = k - 1) (hk : 2 ≤ k)
    (c : Fin L) :
    F _ (cutLLab a i j c) (cutLSgn σ i j) = F 2 ![c, a j] ![σ i, σ j] := by
  apply errorHierarchy_fam_congr F (by omega)
  · intro p hp hp'
    rcases p with _ | _ | p
    · simp only [cutLLab]
      rw [dite_eq_right (by omega), ite_eq_left (by omega)]
      simp
    · simp only [cutLLab]
      rw [dite_eq_right (by omega), ite_eq_right (by omega)]
      have : (⟨1, hp'⟩ : Fin 2) = 1 := rfl
      rw [this, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact congrArg a (Fin.ext (by first | omega | (simp; omega)))
    · omega
  · intro p hp hp'
    rcases p with _ | _ | p
    · simp only [cutLSgn]
      rw [dite_eq_left (by omega)]
      simp only [Fin.zero_eta, Matrix.cons_val_zero]
      exact congrArg σ (Fin.ext (by first | omega | (simp; omega)))
    · simp only [cutLSgn]
      rw [dite_eq_right (by omega)]
      have : (⟨1, hp'⟩ : Fin 2) = 1 := rfl
      rw [this, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact congrArg σ (Fin.ext (by first | omega | (simp; omega)))
    · omega

/-- At the cyclic pair `(0, k-1)`, Cut_R is the word with `a_{k-1}` replaced by `c`. -/
private theorem errorHierarchy_cyc_R {L k : ℕ} (F : LoopFam L) (a : Fin k → Fin L)
    (σ : Fin k → Bool) (i j : Fin k) (hi : i.val = 0) (hj : j.val = k - 1) (hk : 2 ≤ k)
    (c : Fin L) :
    F _ (cutRLab a i j c) (cutRSgn σ i j) = F k (Function.update a j c) σ := by
  apply errorHierarchy_fam_congr F (by omega)
  · intro p hp hp'
    simp only [cutRLab, Function.update_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega) |
      exact congrArg Fin.val (congrArg a (Fin.ext (by first | omega | (simp; omega))))
  · intro p hp hp'
    simp only [cutRSgn]
    exact congrArg σ (Fin.ext (by first | omega | (simp; omega)))

/-- The cut terms of (5.17) [fo:eq:error-hierarchy] minus the sources: the `D_L 𝒦_R` terms at the
adjacent pairs and the `𝒦_L D_R` term at the cyclic pair. -/
private theorem errorHierarchy_cut_decomp {L k : ℕ} (hk : 2 ≤ k) (K D : LoopFam L)
    (a : Fin k → Fin L) (σ : Fin k → Bool) :
    cutErrSum K D a σ = (∑ i : Fin k, ∑ j : Fin k,
      ((if j.val = i.val + 1 then ∑ c : Fin L,
          D _ (cutLLab a i j c) (cutLSgn σ i j) * K _ (cutRLab a i j c) (cutRSgn σ i j) else 0) +
        (if i < j ∧ i.val = 0 ∧ j.val = k - 1 then ∑ c : Fin L,
          K _ (cutLLab a i j c) (cutLSgn σ i j) * D _ (cutRLab a i j c) (cutRSgn σ i j) else 0))) +
      (cutSrcLin K D a σ + cutSrcQuad D a σ) := by
  unfold cutErrSum cutSrcLin cutSrcQuad cutSumFam
  by_cases hk2 : k ≤ 2
  · rw [ite_eq_left hk2, zero_add]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hi := i.2
    have hj := j.2
    split_ifs <;> (try simp only [Fin.lt_def] at *) <;>
      first | (exfalso; omega) | ((try simp only [Finset.sum_add_distrib]); ring)
  · rw [ite_eq_right hk2]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hi := i.2
    have hj := j.2
    split_ifs <;> (try simp only [Fin.lt_def] at *) <;>
      first | (exfalso; omega) | ((try simp only [Finset.sum_add_distrib]); ring)

/-- The adjacent cut terms of (5.17) [fo:eq:error-hierarchy] are `Θ` of (5.14)
[fo:eq:generator]. -/
theorem cutErr_split (γ : ℝ) (W : ℕ) {L k : ℕ} (hk : 2 ≤ k) (K D : LoopFam L)
    (hrot : ∀ (x y : Fin L) (s t : Bool), K 2 ![x, y] ![s, t] = K 2 ![y, x] ![t, s])
    (a : Fin k → Fin L) (σ : Fin k → Bool) :
    ((γ * W : ℝ) : ℂ) * cutErrSum K D a σ =
      thetaOp γ W K D a σ + ((γ * W : ℝ) : ℂ) * (cutSrcLin K D a σ + cutSrcQuad D a σ) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hrotC : ∀ i : Fin n, finRotate (n + 1) i.castSucc = i.succ := fun i => by
    ext
    rw [coe_finRotate_of_ne_last (Fin.castSucc_lt_last i).ne]
    simp
  have hA : ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      (if j.val = i.val + 1 then ∑ c : Fin L,
        D _ (cutLLab a i j c) (cutLSgn σ i j) * K _ (cutRLab a i j c) (cutRSgn σ i j) else 0) =
      ∑ i : Fin n, ∑ c : Fin L, K 2 ![a i.castSucc, c] ![σ i.castSucc,
        σ (finRotate (n + 1) i.castSucc)] * D (n + 1) (Function.update a i.castSucc c) σ := by
    rw [Fin.sum_univ_castSucc]
    have hlast : ∑ j : Fin (n + 1), (if j.val = (Fin.last n).val + 1 then ∑ c : Fin L,
        D _ (cutLLab a (Fin.last n) j c) (cutLSgn σ (Fin.last n) j) *
          K _ (cutRLab a (Fin.last n) j c) (cutRSgn σ (Fin.last n) j) else 0) = 0 :=
      Finset.sum_eq_zero fun j _ => ite_eq_right (by have := j.2; simp; omega)
    rw [hlast, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i.succ]
    · rw [ite_eq_left (by simp)]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [errorHierarchy_adj_L D a σ _ _ (by simp) c, errorHierarchy_adj_R K a σ _ _ (by simp) c,
        hrotC, mul_comm]
    · intro j _ hj
      refine ite_eq_right fun h => absurd (Fin.ext (by simp [h])) hj
    · simp
  have hB : ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      (if i < j ∧ i.val = 0 ∧ j.val = n + 1 - 1 then ∑ c : Fin L,
        K _ (cutLLab a i j c) (cutLSgn σ i j) * D _ (cutRLab a i j c) (cutRSgn σ i j) else 0) =
      ∑ c : Fin L, K 2 ![a (Fin.last n), c] ![σ (Fin.last n), σ (finRotate (n + 1) (Fin.last n))] *
        D (n + 1) (Function.update a (Fin.last n) c) σ := by
    rw [Finset.sum_eq_single 0, Finset.sum_eq_single (Fin.last n)]
    · rw [ite_eq_left ⟨by simp [Fin.lt_def]; omega, rfl, by simp⟩]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [errorHierarchy_cyc_L K a σ 0 (Fin.last n) rfl (by simp) hk c,
        errorHierarchy_cyc_R D a σ 0 (Fin.last n) rfl (by simp) hk c, hrot, finRotate_last]
    · intro j _ hj
      refine ite_eq_right ?_
      rintro ⟨-, -, h⟩
      exact hj (Fin.ext (by simp; omega))
    · simp
    · intro i _ hi
      refine Finset.sum_eq_zero fun j _ => ite_eq_right ?_
      rintro ⟨-, h, -⟩
      exact hi (Fin.ext h)
    · simp
  have hΘ := Fin.sum_univ_castSucc (fun j : Fin (n + 1) => ∑ c : Fin L,
    K 2 ![a j, c] ![σ j, σ (finRotate (n + 1) j)] * D (n + 1) (Function.update a j c) σ)
  rw [errorHierarchy_cut_decomp hk K D a σ]
  simp only [Finset.sum_add_distrib]
  rw [hA, hB, thetaOp, hΘ]
  ring

/-- Linearity of the block generator over a finite family with time-dependent scalar coefficients
`w_b`: `𝒢(Σ_b w_b G_b) = Σ_b (∂_u w_b · G_b + w_b 𝒢 G_b)`. -/
private theorem errorHierarchy_blockGen_sum {W L : ℕ} (γ : ℝ) {ι : Type*} [Fintype ι]
    (w : ι → ℝ → ℂ) (w' : ι → ℂ)
    (G : ι → ℝ → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ → ℂ) (u : ℝ)
    (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (hw : ∀ b, HasDerivAt (w b) (w' b) u)
    (hGt : ∀ b, DifferentiableAt ℝ (fun r => G b r M) u)
    (hGl : ∀ b (c : Fin L) (κ : Fin W × Fin W),
      (∀ e : ℝ, DifferentiableAt ℝ (fun e : ℝ => G b u (M + (e : ℂ) • blockBasis W L c κ)) e) ∧
      DifferentiableAt ℝ (deriv (fun e : ℝ => G b u (M + (e : ℂ) • blockBasis W L c κ))) 0) :
    blockGen W L γ (fun r N => ∑ b, w b r * G b r N) u M =
      ∑ b, (w' b * G b u M + w b u * blockGen W L γ (G b) u M) := by
  unfold blockGen
  have ht : deriv (fun r => ∑ b, w b r * G b r M) u =
      ∑ b, (w' b * G b u M + w b u * deriv (fun r => G b r M) u) :=
    (HasDerivAt.fun_sum (u := Finset.univ)
      fun b _ => ((hw b).mul (hGt b).hasDerivAt)).deriv
  have hl : ∀ (c : Fin L) (κ : Fin W × Fin W),
      iteratedDeriv 2 (fun e : ℝ => ∑ b, w b u * G b u (M + (e : ℂ) • blockBasis W L c κ)) 0 =
      ∑ b, w b u * iteratedDeriv 2 (fun e : ℝ => G b u (M + (e : ℂ) • blockBasis W L c κ)) 0 := by
    intro c κ
    have h1 : deriv (fun e : ℝ => ∑ b, w b u * G b u (M + (e : ℂ) • blockBasis W L c κ)) =
        fun e => ∑ b, w b u * deriv (fun e : ℝ => G b u (M + (e : ℂ) • blockBasis W L c κ)) e :=
      funext fun e => (HasDerivAt.fun_sum (u := Finset.univ)
        fun b _ => (((hGl b c κ).1 e).hasDerivAt.const_mul (w b u))).deriv
    rw [iteratedDeriv_succ, iteratedDeriv_one, h1, (HasDerivAt.fun_sum (u := Finset.univ)
      fun b _ => ((hGl b c κ).2.hasDerivAt.const_mul (w b u))).deriv]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [ht]
  simp only [hl]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  have hswap : ∑ c : Fin L, ∑ κ : Fin W × Fin W, ∑ b, ((γ / (2 * W) : ℝ) : ℂ) *
      (w b u * iteratedDeriv 2 (fun e : ℝ => G b u (M + (e : ℂ) • blockBasis W L c κ)) 0) =
      ∑ b, ∑ c : Fin L, ∑ κ : Fin W × Fin W, w b u * (((γ / (2 * W) : ℝ) : ℂ) *
        iteratedDeriv 2 (fun e : ℝ => G b u (M + (e : ℂ) • blockBasis W L c κ)) 0) := by
    calc _ = ∑ c : Fin L, ∑ b, ∑ κ : Fin W × Fin W, ((γ / (2 * W) : ℝ) : ℂ) *
          (w b u * iteratedDeriv 2 (fun e : ℝ => G b u (M + (e : ℂ) • blockBasis W L c κ)) 0) :=
          Finset.sum_congr rfl fun c _ => Finset.sum_comm
      _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
            Finset.sum_congr rfl fun κ _ => ?_
          ring
  rw [hswap, ← Finset.sum_add_distrib]

/-- Exchange of the labels `b_j ↔ c` in a double sum over words `b` and labels `c`. -/
private theorem errorHierarchy_swap_sum {L k : ℕ} (j : Fin k)
    (F : (Fin k → Fin L) → Fin L → ℂ) :
    ∑ b : Fin k → Fin L, ∑ c : Fin L, F b c =
      ∑ b : Fin k → Fin L, ∑ c : Fin L, F (Function.update b j c) (b j) := by
  have hinv : Function.Involutive
      (fun p : (Fin k → Fin L) × Fin L => (Function.update p.1 j p.2, p.1 j)) := by
    intro p
    simp
  rw [← Fintype.sum_prod_type' F,
    ← Fintype.sum_prod_type' (fun b c => F (Function.update b j c) (b j))]
  exact (Equiv.sum_comp (Function.Involutive.toPerm _ hinv)
    (fun p : (Fin k → Fin L) × Fin L => F p.1 p.2)).symm

/-- The cancellation of `Θ` against the time derivative of the deterministic legs: for
`∂_u V_j = -V_j · κ K_j`, `Σ_b (∂_u Π_j V_j) D_b + Σ_b (Π_j V_j) Θ D (b) = 0`. -/
private theorem errorHierarchy_theta_cancel {L k : ℕ} (κ₀ : ℂ) (a : Fin k → Fin L)
    (V : Fin k → Fin L → Fin L → ℂ) (K2 : Fin k → Fin L → Fin L → ℂ)
    (D : (Fin k → Fin L) → ℂ) :
    ∑ b : Fin k → Fin L,
      ((∑ j, (∏ l ∈ Finset.univ.erase j, V l (a l) (b l)) •
          (-(∑ c, V j (a j) c * (κ₀ * K2 j c (b j))))) * D b +
        (∏ j, V j (a j) (b j)) * (κ₀ * ∑ j, ∑ c, K2 j (b j) c * D (Function.update b j c))) =
      0 := by
  set S : ℂ := ∑ j, ∑ b : Fin k → Fin L, ∑ c,
    (∏ l ∈ Finset.univ.erase j, V l (a l) (b l)) * V j (a j) c * K2 j c (b j) * D b with hS
  have hA : ∑ b : Fin k → Fin L, (∑ j, (∏ l ∈ Finset.univ.erase j, V l (a l) (b l)) •
      (-(∑ c, V j (a j) c * (κ₀ * K2 j c (b j))))) * D b = -κ₀ * S := by
    rw [hS, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul, ← Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have hB : ∑ b : Fin k → Fin L, (∏ j, V j (a j) (b j)) *
      (κ₀ * ∑ j, ∑ c, K2 j (b j) c * D (Function.update b j c)) = κ₀ * S := by
    have h1 : ∀ b : Fin k → Fin L, (∏ j, V j (a j) (b j)) *
        (κ₀ * ∑ j, ∑ c, K2 j (b j) c * D (Function.update b j c)) =
        κ₀ * ∑ j, ∑ c, (∏ l, V l (a l) (b l)) * K2 j (b j) c * D (Function.update b j c) := by
      intro b
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => ?_
      ring
    simp only [h1]
    rw [← Finset.mul_sum, Finset.sum_comm, hS]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [errorHierarchy_swap_sum j]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    have hp : ∏ l, V l (a l) (Function.update b j c l) =
        V j (a j) c * ∏ l ∈ Finset.univ.erase j, V l (a l) (b l) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun l hl => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
    rw [hp, Function.update_self, Function.update_idem, Function.update_eq_self]
    ring
  rw [Finset.sum_add_distrib, hA, hB]
  ring

/-- Propagated error equation: for deterministic legs with `∂_u U_j = -U_j Θ_j`,
`𝒢_u(𝒰 D_k) = 𝒰(𝒲_k + γW (linear + quadratic sources))`, the generator identity behind the
unlabelled stopped Duhamel expression after (C.21) [fo:eq:propagated-pair-bracket], here unstopped
and for every `k ≥ 2`. -/
theorem blockGen_propagated (g E : ℝ) (m : ℂ) (hm : 0 < m.im) {W L k : ℕ} (hk : 2 ≤ k) {u : ℝ}
    (hu : u < 1) {M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hM : M.IsHermitian)
    (K : ℝ → LoopFam L) (hK : IsPrimDeriv (gammaG g) W L K u)
    (hrot : ∀ (x y : Fin L) (s t : Bool), K u 2 ![x, y] ![s, t] = K u 2 ![y, x] ![t, s])
    (σ : Fin k → Bool) (U : Fin k → ℝ → Matrix (Fin L) (Fin L) ℂ)
    (hU : ∀ j x y, HasDerivAt (fun r => U j r x y)
      (-(∑ c, U j u x c * (((gammaG g * W : ℝ) : ℂ) * K u 2 ![c, y] ![σ j, σ (finRotate k j)]))) u)
    (a : Fin k → Fin L) :
    blockGen W L (gammaG g)
        (fun r N => ∑ b : Fin k → Fin L, (∏ j, U j r (a j) (b j)) * (resLoop g E m b σ r N - K r k b σ))
        u M =
      ∑ b : Fin k → Fin L, (∏ j, U j u (a j) (b j)) *
        (lightW g E m b σ u M + ((gammaG g * W : ℝ) : ℂ) *
          (cutSrcLin (K u) (errFam g E m (K u) u M) b σ +
            cutSrcQuad (errFam g E m (K u) u M) b σ)) := by
  have hsm := fun b : Fin k → Fin L => errorHierarchy_smooth g E m hm hu hM (W := W) b σ
  refine (errorHierarchy_blockGen_sum (gammaG g) (fun b r => ∏ j, U j r (a j) (b j))
    (fun b => ∑ j, (∏ l ∈ Finset.univ.erase j, U l u (a l) (b l)) •
      (-(∑ c, U j u (a j) c *
        (((gammaG g * W : ℝ) : ℂ) * K u 2 ![c, b j] ![σ j, σ (finRotate k j)]))))
    (fun b r N => resLoop g E m b σ r N - K r k b σ) u M
    (fun b => HasDerivAt.fun_finsetProd (u := Finset.univ) fun j _ => hU j (a j) (b j))
    (fun b => (hsm b).1.sub (hK k b σ).differentiableAt)
    (fun b c κ => ⟨fun e => (((hsm b).2 c κ).1 e).sub_const _, by
      rw [deriv_sub_const_fun]; exact ((hsm b).2 c κ).2⟩)).trans ?_
  have hC := errorHierarchy_theta_cancel ((gammaG g * W : ℝ) : ℂ) a (fun j => U j u)
    (fun j x y => K u 2 ![x, y] ![σ j, σ (finRotate k j)])
    (fun b => errFam g E m (K u) u M k b σ)
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← hC]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [blockGen_errorLoop g E m hm hu hM K hK b σ,
    cutErr_split (gammaG g) W hk (K u) (errFam g E m (K u) u M) hrot b σ, thetaOp]
  simp only [errFam, resLoop]
  ring

/-- Exchange of a double sum over `(c, κ)` with a double sum over `(b, b')`. -/
private theorem errorHierarchy_sum_comm4 {ι₁ ι₂ ι₃ ι₄ : Type*} [Fintype ι₁] [Fintype ι₂]
    [Fintype ι₃] [Fintype ι₄] (F : ι₁ → ι₂ → ι₃ → ι₄ → ℂ) :
    ∑ c, ∑ κ, ∑ b, ∑ b', F c κ b b' = ∑ b, ∑ b', ∑ c, ∑ κ, F c κ b b' := by
  calc ∑ c, ∑ κ, ∑ b, ∑ b', F c κ b b' = ∑ c, ∑ b, ∑ κ, ∑ b', F c κ b b' :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ b', ∑ κ, F c κ b b' :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ b', ∑ κ, F c κ b b' := Finset.sum_comm
    _ = ∑ b, ∑ b', ∑ c, ∑ κ, F c κ b b' := Finset.sum_congr rfl fun b _ => Finset.sum_comm

/-- The propagated bracket `Γ(𝒰F, 𝒰'F') = (𝒰 ⊗ conj 𝒰') Γ(F, F')`, as used in (C.21)
[fo:eq:propagated-pair-bracket]. -/
theorem blockGamma_tensor {W L : ℕ} (γ : ℝ) {β β' : Type*} [Fintype β] [Fintype β']
    (α : β → ℂ) (α' : β' → ℂ) (f : β → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ → ℂ)
    (f' : β' → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ → ℂ)
    (M : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (hf : ∀ b c k, DifferentiableAt ℝ (fun e : ℝ => f b (M + (e : ℂ) • blockBasis W L c k)) 0)
    (hf' : ∀ b c k, DifferentiableAt ℝ (fun e : ℝ => f' b (M + (e : ℂ) • blockBasis W L c k)) 0) :
    blockGamma W L γ (fun N => ∑ b, α b * f b N) (fun N => ∑ b, α' b * f' b N) M =
      ∑ b, ∑ b', α b * star (α' b') * blockGamma W L γ (f b) (f' b') M := by
  have hd : ∀ c k, deriv (fun e : ℝ => ∑ b, α b * f b (M + (e : ℂ) • blockBasis W L c k)) 0 =
      ∑ b, α b * deriv (fun e : ℝ => f b (M + (e : ℂ) • blockBasis W L c k)) 0 := by
    intro c k
    exact (HasDerivAt.fun_sum (u := Finset.univ)
      (fun b _ => ((hf b c k).hasDerivAt.const_mul (α b)))).deriv
  have hd' : ∀ c k, deriv (fun e : ℝ => ∑ b, α' b * f' b (M + (e : ℂ) • blockBasis W L c k)) 0 =
      ∑ b, α' b * deriv (fun e : ℝ => f' b (M + (e : ℂ) • blockBasis W L c k)) 0 := by
    intro c k
    exact (HasDerivAt.fun_sum (u := Finset.univ)
      (fun b _ => ((hf' b c k).hasDerivAt.const_mul (α' b)))).deriv
  unfold blockGamma
  simp only [hd, hd']
  have hin : ∀ c k, (∑ b, α b * deriv (fun e : ℝ => f b (M + (e : ℂ) • blockBasis W L c k)) 0) *
      star (∑ b', α' b' * deriv (fun e : ℝ => f' b' (M + (e : ℂ) • blockBasis W L c k)) 0) =
      ∑ b, ∑ b', α b * star (α' b') *
        (deriv (fun e : ℝ => f b (M + (e : ℂ) • blockBasis W L c k)) 0 *
          star (deriv (fun e : ℝ => f' b' (M + (e : ℂ) • blockBasis W L c k)) 0)) := by
    intro c k
    rw [star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    rw [star_mul']
    ring
  simp only [hin, Finset.mul_sum]
  refine (errorHierarchy_sum_comm4 _).trans ?_
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun k _ => ?_
  ring

end LSBA
