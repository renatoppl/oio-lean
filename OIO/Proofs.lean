import OIO.Statements

/-!
# Online Inverse Optimization — Formal Proofs (`OIO.Proofs`)

This module imports the definitions and propositional theorem statements from `OIO.Statements`
and provides complete, kernel-checked proofs of all formalized results.

## Structure
- **Section 1**: Helper definitions for `RVMSkip(α)` and shared linear-algebraic / matrix lemmas
- **Section 2**: `RVMHelpers` and `RVMProofs` (Lemmas 2.3(a,b,d) and 2.5)
- **Section 3**: `SkipHelpers` and `prop_3_3` (Proposition 3.3)
- **Section 4**: Lemmas 2.6, Theorem 2.1, Corollary 2.2, Equation (6), Lemma 2.3(c), Lemma 2.7
- **Section 5**: Causality (`thm_causality`), Remark 2.4 (`rem_cost_counts`), Remark 3.1 (`rem_stall`)
- **Section 7**: Master theorem (`oio_all_results`) and top-level wrapper theorems
-/

open scoped Matrix BigOperators

noncomputable def skipPathMetric {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) (η : ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  let st := rvmSkipState α v t
  stretchMetric (rvmSkipPathActiveSet α v t η) st.γ v

noncomputable def skipStepNorm {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) : ℝ :=
  matNorm ((skipPathMetric α v t α)⁻¹) (v t)

noncomputable def skipWeight {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) : ℝ :=
  1 / (8 * (skipStepNorm α v t) ^ 2)

def skipSlab {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) (p : Fin d → ℝ) : Prop :=
  inSlab α (rvmSkipQuery α v (t + 1)) (v t) (skipStepNorm α v t) p

noncomputable def skipRoundRevokePoint {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t i : ℕ) :
    Fin d → ℝ :=
  let st := rvmSkipState α v t
  rvmRevocationPoint α st.c v st.s st.γ (v t) (st.A.card + 1) α st.p st.A i

noncomputable def skipXi {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) : ℝ :=
  dotProduct (rvmSkipQuery α v (t + 1) - rvmSkipQuery α v t) (v t)

noncomputable def skipStretchEndPoint {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) :
    ℕ → ℕ → (Fin d → ℝ)
  | 0, _ => 0
  | r + 1, t =>
    if r ≤ t then
      rvmSkipQuery α v (r + 1)
    else if t ∈ rvmSkipRevokedInRound α v r then
      skipRoundRevokePoint α v r t
    else if t ∈ rvmSkipPathActiveSet α v r α then
      rvmSkipQuery α v (r + 1)
    else
      skipStretchEndPoint α v r t

noncomputable def skipDelta {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (T t : ℕ) : ℝ :=
  dotProduct (skipStretchEndPoint α v T t - rvmSkipQuery α v (t + 1)) (v t)

noncomputable def skipLambda {d : ℕ} (α : ℝ) (w_star : Fin d → ℝ) (v : ℕ → (Fin d → ℝ))
    (T t : ℕ) : ℝ :=
  let r_t := rvmSkipLoss α w_star v t
  let s_t := skipStepNorm α v t
  let γ_t := skipWeight α v t
  let ξ_t := skipXi α v t
  let Δ_t := skipDelta α v T t
  (-2) * α * r_t + α ^ 2 * s_t ^ 2 + γ_t * (2 * Δ_t * r_t - Δ_t * (Δ_t + 2 * ξ_t))

noncomputable def skipSurvivingMetric {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (T t : ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  stretchMetric ((rvmSkipActiveSet α v T).filter (· < t)) (skipWeight α v) v

lemma h_dot_self_nonneg : ∀ {d : ℕ} (u : Fin d → ℝ), 0 ≤ dotProduct u u := by
  intro d u
  unfold dotProduct
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (u i))

lemma h_vecMulVec_mulVec : ∀ {d : ℕ} (a b x : Fin d → ℝ),
    Matrix.vecMulVec a b *ᵥ x = (dotProduct b x) • a := by
  intro d a b x
  ext j
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => by ring)

lemma h_quad_sum : ∀ {d : ℕ} (S : Finset ℕ) (γ : ℕ → ℝ) (v : ℕ → (Fin d → ℝ)) (x : Fin d → ℝ),
    dotProduct x ((∑ i ∈ S, (γ i) • Matrix.vecMulVec (v i) (v i)) *ᵥ x) =
      ∑ i ∈ S, γ i * (dotProduct x (v i)) ^ 2 := by
  intro d S γ v x
  induction S using Finset.induction_on with
  | empty =>
    simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Matrix.add_mulVec, Matrix.smul_mulVec, h_vecMulVec_mulVec,
        dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
        ih, Finset.sum_insert ha, dotProduct_comm (v a) x]
    ring

lemma h_quad_stretch : ∀ {d : ℕ} (S : Finset ℕ) (γ : ℕ → ℝ) (v : ℕ → (Fin d → ℝ)) (x : Fin d → ℝ),
    quadForm (stretchMetric S γ v) x =
      dotProduct x x + ∑ i ∈ S, γ i * (dotProduct x (v i)) ^ 2 := by
  intro d S γ v x
  unfold quadForm stretchMetric
  rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, h_quad_sum]

lemma h_dot_pos_of_ne_zero : ∀ {d : ℕ} (x : Fin d → ℝ), x ≠ 0 → 0 < dotProduct x x := by
  intro d x hx
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
  have hj_pos : 0 < x j * x j := mul_self_pos.mpr hj
  have hj_le : x j * x j ≤ ∑ k : Fin d, x k * x k :=
    Finset.single_le_sum (fun k _ => mul_self_nonneg (x k)) (Finset.mem_univ j)
  unfold dotProduct
  linarith

lemma h_stretch_herm : ∀ {d : ℕ} (S : Finset ℕ) (γ : ℕ → ℝ) (v : ℕ → (Fin d → ℝ)),
    (stretchMetric S γ v).IsHermitian := by
  intro d S γ v
  ext j k
  simp [stretchMetric, Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, mul_comm, eq_comm]

lemma h_stretch_posDef : ∀ {d : ℕ} (S : Finset ℕ) (γ : ℕ → ℝ) (_hγ : ∀ i ∈ S, 0 ≤ γ i)
    (v : ℕ → (Fin d → ℝ)), (stretchMetric S γ v).PosDef := by
  intro d S γ hγ v
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (h_stretch_herm S γ v) ?_
  intro x hx
  rw [star_trivial]
  change 0 < quadForm (stretchMetric S γ v) x
  rw [h_quad_stretch]
  have hx_pos : 0 < dotProduct x x := h_dot_pos_of_ne_zero x hx
  have h_sum_nonneg : 0 ≤ ∑ i ∈ S, γ i * (dotProduct x (v i)) ^ 2 :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hγ i hi) (sq_nonneg _))
  linarith

lemma h_stretch_sdiff_posSemidef : ∀ {d : ℕ} (S₁ S₂ : Finset ℕ) (_h_sub : S₂ ⊆ S₁)
    (γ : ℕ → ℝ) (_hγ : ∀ i ∈ S₁, 0 ≤ γ i) (v : ℕ → (Fin d → ℝ)),
    (stretchMetric S₁ γ v - stretchMetric S₂ γ v).PosSemidef := by
  intro d S₁ S₂ h_sub γ hγ v
  have h_diff_eq : stretchMetric S₁ γ v - stretchMetric S₂ γ v =
      ∑ i ∈ S₁ \ S₂, (γ i) • Matrix.vecMulVec (v i) (v i) := by
    unfold stretchMetric
    rw [add_sub_add_left_eq_sub]
    exact sub_eq_iff_eq_add.mpr (Finset.sum_sdiff h_sub).symm
  rw [h_diff_eq]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext j k
    simp [Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, mul_comm]
  · intro x
    rw [star_trivial, h_quad_sum]
    exact Finset.sum_nonneg (fun i hi => mul_nonneg (hγ i (Finset.mem_sdiff.mp hi).1) (sq_nonneg _))

lemma h_stretch_inv_mono : ∀ {d : ℕ} (S₁ S₂ : Finset ℕ) (_h_sub : S₂ ⊆ S₁)
    (γ : ℕ → ℝ) (_hγ : ∀ i ∈ S₁, 0 ≤ γ i) (v : ℕ → (Fin d → ℝ)) (x : Fin d → ℝ),
    quadForm ((stretchMetric S₁ γ v)⁻¹) x ≤ quadForm ((stretchMetric S₂ γ v)⁻¹) x ∧
    matNorm ((stretchMetric S₁ γ v)⁻¹) x ≤ matNorm ((stretchMetric S₂ γ v)⁻¹) x := by
  intro d S₁ S₂ h_sub γ hγ v x
  set A := stretchMetric S₂ γ v
  set B := stretchMetric S₁ γ v
  have hγ₂ : ∀ i ∈ S₂, 0 ≤ γ i := fun i hi => hγ i (h_sub hi)
  have hA_pd : A.PosDef := h_stretch_posDef S₂ γ hγ₂ v
  have hB_pd : B.PosDef := h_stretch_posDef S₁ γ hγ v
  have hA_det : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA_pd.isUnit
  have hB_det : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB_pd.isUnit
  set z := A⁻¹ *ᵥ x
  set y := B⁻¹ *ᵥ x
  have hAz : A *ᵥ z = x := by
    dsimp [z]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA_det, Matrix.one_mulVec]
  have hBy : B *ᵥ y = x := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B hB_det, Matrix.one_mulVec]
  have hA_tr : A.transpose = A := h_stretch_herm S₂ γ v
  have hA_symm : dotProduct z (A *ᵥ y) = dotProduct y (A *ᵥ z) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA_tr, dotProduct_comm]
  have h_diff_eq : B - A = ∑ i ∈ S₁ \ S₂, (γ i) • Matrix.vecMulVec (v i) (v i) := by
    dsimp [A, B]
    unfold stretchMetric
    rw [add_sub_add_left_eq_sub]
    exact sub_eq_iff_eq_add.mpr (Finset.sum_sdiff h_sub).symm
  have h_id : quadForm A (y - z) + dotProduct y ((B - A) *ᵥ y) =
      quadForm (A⁻¹) x - quadForm (B⁻¹) x := by
    unfold quadForm
    change dotProduct (y - z) (A *ᵥ (y - z)) + dotProduct y ((B - A) *ᵥ y) =
      dotProduct x z - dotProduct x y
    rw [Matrix.mulVec_sub, Matrix.sub_mulVec, dotProduct_sub, sub_dotProduct,
        sub_dotProduct, dotProduct_sub, hA_symm, hAz, hBy, dotProduct_comm y x, dotProduct_comm z x]
    ring
  have h_t1 : 0 ≤ quadForm A (y - z) := by
    dsimp [A]
    rw [h_quad_stretch]
    have := h_dot_self_nonneg (y - z)
    have : 0 ≤ ∑ i ∈ S₂, γ i * (dotProduct (y - z) (v i)) ^ 2 :=
      Finset.sum_nonneg (fun i hi => mul_nonneg (hγ₂ i hi) (sq_nonneg _))
    linarith
  have h_t2 : 0 ≤ dotProduct y ((B - A) *ᵥ y) := by
    rw [h_diff_eq, h_quad_sum]
    exact Finset.sum_nonneg (fun i hi => mul_nonneg (hγ i (Finset.mem_sdiff.mp hi).1) (sq_nonneg _))
  have h_q_le : quadForm (B⁻¹) x ≤ quadForm (A⁻¹) x := by linarith
  exact ⟨h_q_le, Real.sqrt_le_sqrt h_q_le⟩

lemma h_fold_min : ∀ (A : Finset ℕ) (rem : ℝ) (f : ℕ → ℝ),
    A.fold min rem f ≤ rem ∧
    (∀ i ∈ A, A.fold min rem f ≤ f i) ∧
    (0 < rem → (∀ i ∈ A, 0 < f i) → 0 < A.fold min rem f) ∧
    (A.fold min rem f < rem → ∃ i ∈ A, A.fold min rem f = f i) := by
  intro A rem f
  induction A using Finset.induction_on with
  | empty =>
    simp
  | @insert a s ha ih =>
    rw [Finset.fold_insert ha]
    refine ⟨le_trans (min_le_right _ _) ih.1, ?_, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | h_in
      · exact min_le_left _ _
      · exact le_trans (min_le_right _ _) (ih.2.1 i h_in)
    · intro hrem hf
      exact lt_min (hf a (Finset.mem_insert_self a s))
        (ih.2.2.1 hrem (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
    · intro h_lt
      rcases min_choice (f a) (s.fold min rem f) with h_eq | h_eq
      · exact ⟨a, Finset.mem_insert_self a s, h_eq⟩
      · rw [h_eq] at h_lt
        obtain ⟨i, hi, hi_eq⟩ := ih.2.2.2 h_lt
        exact ⟨i, Finset.mem_insert_of_mem hi, h_eq.trans hi_eq⟩

lemma h_exit_pos : ∀ {d : ℕ} (α rem : ℝ) (_hrem : 0 < rem)
    (c v : ℕ → (Fin d → ℝ)) (s : ℕ → ℝ) (p u : Fin d → ℝ) (i : ℕ),
    inSlab α (c i) (v i) (s i) p →
    0 < pieceExitDelta α rem c v s p u i := by
  intro d α rem hrem c v s p u i h_in
  have h_abs : |dotProduct (p - c i) (v i)| < 4 * α * (s i) ^ 2 := h_in
  have h_lt := abs_lt.mp h_abs
  unfold pieceExitDelta
  dsimp only
  split_ifs with h1 h2
  · exact div_pos (by linarith) h1
  · exact div_pos_of_neg_of_neg (by linarith) h2
  · exact hrem

namespace RVMHelpers

lemma h_state_gamma : ∀ {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t i : ℕ),
    i < t → (rvmState α v t).γ i = rvmWeight α v i := by
  intro d α v t
  induction t with
  | zero =>
    intro i hi
    omega
  | succ t ih =>
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | h_eq
    · have hne : i ≠ t := ne_of_lt hlt
      change Function.update (rvmState α v t).γ t (rvmWeight α v t) i = rvmWeight α v i
      rw [Function.update_of_ne hne]
      exact ih i hlt
    · subst h_eq
      change Function.update (rvmState α v i).γ i (rvmWeight α v i) i = rvmWeight α v i
      exact Function.update_self i (rvmWeight α v i) (rvmState α v i).γ

lemma h_state_gamma_nonneg : ∀ {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t i : ℕ),
    0 ≤ (rvmState α v t).γ i := by
  intro d α v t
  induction t with
  | zero =>
    intro i
    exact le_refl 0
  | succ t ih =>
    intro i
    change 0 ≤ Function.update (rvmState α v t).γ t (rvmWeight α v t) i
    by_cases h : i = t
    · subst h
      rw [Function.update_self]
      unfold rvmWeight
      positivity
    · rw [Function.update_of_ne h]
      exact ih i

lemma h_state_c : ∀ {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t i : ℕ),
    i < t → (rvmState α v t).c i = rvmQuery α v (i + 1) := by
  intro d α v t
  induction t with
  | zero => intro i hi; omega
  | succ t ih =>
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | h_eq
    · have hne : i ≠ t := ne_of_lt hlt
      change Function.update (rvmState α v t).c t (rvmQuery α v (t + 1)) i = rvmQuery α v (i + 1)
      rw [Function.update_of_ne hne]
      exact ih i hlt
    · subst h_eq
      change Function.update (rvmState α v i).c i (rvmQuery α v (i + 1)) i = rvmQuery α v (i + 1)
      exact Function.update_self i (rvmQuery α v (i + 1)) (rvmState α v i).c

lemma h_state_s : ∀ {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t i : ℕ),
    i < t → (rvmState α v t).s i = rvmStepNorm α v i := by
  intro d α v t
  induction t with
  | zero => intro i hi; omega
  | succ t ih =>
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | h_eq
    · have hne : i ≠ t := ne_of_lt hlt
      change Function.update (rvmState α v t).s t (rvmStepNorm α v t) i = rvmStepNorm α v i
      rw [Function.update_of_ne hne]
      exact ih i hlt
    · subst h_eq
      change Function.update (rvmState α v i).s i (rvmStepNorm α v i) i = rvmStepNorm α v i
      exact Function.update_self i (rvmStepNorm α v i) (rvmState α v i).s

lemma h_endPoint_active : ∀ {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (r i : ℕ),
    i ∈ rvmActiveSet α v r → rvmStretchEndPoint α v r i = rvmQuery α v r := by
  intro d α v r i hi
  cases r with
  | zero =>
    simp [rvmActiveSet, rvmState] at hi
  | succ r =>
    have hi' : i = r ∨ i ∈ rvmPathActiveSet α v r α := Finset.mem_insert.mp hi
    unfold rvmStretchEndPoint
    by_cases hri : r ≤ i
    · simp [hri]
    · rcases hi' with rfl | h_path
      · exact False.elim (hri (le_refl i))
      · have h_not_rev : i ∉ rvmRevokedInRound α v r := by
          unfold rvmRevokedInRound
          intro h_rev
          exact (Finset.mem_sdiff.mp h_rev).2 h_path
        simp [hri, h_not_rev, h_path]

lemma lem_2_3a : Lemma2_3a_ActiveSlabsContainQuery := by
  intro d hd α hα v h_unit t
  have h_move_preserves : ∀ (n : ℕ) (rem : ℝ) (_hrem : 0 < rem)
      (c : ℕ → (Fin d → ℝ)) (s γ : ℕ → ℝ) (v_t : Fin d → ℝ)
      (p : Fin d → ℝ) (A : Finset ℕ),
      (∀ i ∈ A, inSlab α (c i) (v i) (s i) p) →
      let res := rvmMoveEval α c v s γ v_t n rem p A rem
      res.2 ⊆ A ∧ ∀ i ∈ res.2, inSlab α (c i) (v i) (s i) res.1 := by
    intro n
    induction n with
    | zero =>
      intro rem _ c s γ v_t p A hA
      exact ⟨Finset.Subset.refl A, hA⟩
    | succ n ih =>
      intro rem hrem c s γ v_t p A hA
      dsimp only [rvmMoveEval]
      set H := stretchMetric A γ v
      set u := H⁻¹ *ᵥ v_t
      set δ := pieceStepTime α rem c v s A p u
      set p_next := p + δ • u
      set A_next := A.filter (fun i => inSlab α (c i) (v i) (s i) p_next)
      have hδ_le : δ ≤ rem := (h_fold_min A rem (pieceExitDelta α rem c v s p u)).1
      have h_not_lt : ¬ (rem < δ) := not_lt.mpr hδ_le
      have hA_next_sub : A_next ⊆ A := Finset.filter_subset _ A
      have hA_next_in : ∀ i ∈ A_next, inSlab α (c i) (v i) (s i) p_next :=
        fun i hi => (Finset.mem_filter.mp hi).2
      rw [if_neg h_not_lt]
      split_ifs with h_lt
      · have h_rec := ih (rem - δ) (by linarith) c s γ v_t p_next A_next hA_next_in
        exact ⟨h_rec.1.trans hA_next_sub, h_rec.2⟩
      · exact ⟨hA_next_sub, hA_next_in⟩
  have h_step_norm_pos : ∀ r, 0 < rvmStepNorm α v r := by
    intro r
    set H := rvmPathMetric α v r α
    have hγ : ∀ i, 0 ≤ (rvmState α v r).γ i := h_state_gamma_nonneg α v r
    have h_pd : H.PosDef := h_stretch_posDef _ _ (fun i _ => hγ i) v
    have hH_det : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp h_pd.isUnit
    set w := H⁻¹ *ᵥ v r
    have hHw : H *ᵥ w = v r := by
      dsimp [w]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv H hH_det, Matrix.one_mulVec]
    have hw_ne : w ≠ 0 := by
      intro hw0
      have hv0 : v r = 0 := by rw [← hHw, hw0, Matrix.mulVec_zero]
      have h1 := h_unit r
      rw [hv0, dotProduct_zero] at h1
      norm_num at h1
    have h_q_eq : quadForm (H⁻¹) (v r) = quadForm H w := by
      unfold quadForm
      change dotProduct (v r) w = dotProduct w (H *ᵥ w)
      rw [← hHw, dotProduct_comm]
    have h_qw_pos : 0 < quadForm H w := by
      dsimp [H, rvmPathMetric]
      rw [h_quad_stretch]
      have := h_dot_pos_of_ne_zero w hw_ne
      have : 0 ≤ ∑ i ∈ rvmPathActiveSet α v r α, (rvmState α v r).γ i * (dotProduct w (v i)) ^ 2 :=
        Finset.sum_nonneg (fun i _ => mul_nonneg (hγ i) (sq_nonneg _))
      linarith
    unfold rvmStepNorm rvmDualLength matNorm
    exact Real.sqrt_pos.mpr (by linarith)
  have h_inv : ∀ r, ∀ i ∈ rvmActiveSet α v r, i < r ∧ rvmSlab α v i (rvmQuery α v r) := by
    intro r
    induction r with
    | zero =>
      intro i hi
      simp [rvmActiveSet, rvmState] at hi
    | succ r ih =>
      intro i hi
      set st := rvmState α v r
      have hA_in : ∀ j ∈ st.A, inSlab α (st.c j) (v j) (st.s j) st.p := by
        intro j hj
        obtain ⟨hj_lt, hj_slab⟩ := ih j hj
        unfold rvmSlab at hj_slab
        rwa [h_state_c α v r j hj_lt, h_state_s α v r j hj_lt]
      have h_pres := h_move_preserves (st.A.card + 1) α hα st.c st.s st.γ (v r) st.p st.A hA_in
      rcases Finset.mem_insert.mp hi with rfl | h_in_after
      · refine ⟨Nat.lt_succ_self i, ?_⟩
        unfold rvmSlab inSlab
        rw [sub_self, zero_dotProduct, abs_zero]
        have hs_pos := h_step_norm_pos i
        positivity
      · have hi_in_A : i ∈ st.A := h_pres.1 h_in_after
        obtain ⟨hi_lt, _⟩ := ih i hi_in_A
        have hi_in_slab : inSlab α (st.c i) (v i) (st.s i) (rvmQuery α v (r + 1)) :=
          h_pres.2 i h_in_after
        rw [h_state_c α v r i hi_lt, h_state_s α v r i hi_lt] at hi_in_slab
        exact ⟨Nat.lt_succ_of_lt hi_lt, hi_in_slab⟩
  refine ⟨h_inv t, ?_⟩
  set st := rvmState α v t
  have hA_in : ∀ i ∈ st.A, inSlab α (st.c i) (v i) (st.s i) st.p := by
    intro i hi
    obtain ⟨hi_lt, hi_slab⟩ := h_inv t i hi
    unfold rvmSlab at hi_slab
    rwa [h_state_c α v t i hi_lt, h_state_s α v t i hi_lt]
  set H := stretchMetric st.A st.γ v
  set u := H⁻¹ *ᵥ v t
  set δ := pieceStepTime α α st.c v st.s st.A st.p u
  have hδ_pos : 0 < δ :=
    (h_fold_min st.A α (pieceExitDelta α α st.c v st.s st.p u)).2.2.1 hα
      (fun i hi => h_exit_pos α α hα st.c v st.s st.p u i (hA_in i hi))
  have h_eval_0 : rvmMoveEval α st.c v st.s st.γ (v t) (st.A.card + 1) α st.p st.A 0 = (st.p, st.A) := by
    dsimp only [rvmMoveEval]
    rw [if_pos hδ_pos, zero_smul, add_zero]
  have hp0 : rvmPath α v t 0 = rvmQuery α v t := by
    unfold rvmPath rvmQuery
    dsimp only
    rw [h_eval_0]
  have hA0 : rvmPathActiveSet α v t 0 = rvmActiveSet α v t := by
    unfold rvmPathActiveSet rvmActiveSet
    dsimp only
    rw [h_eval_0]
  have hH0 : rvmPathMetric α v t 0 = rvmMetric α v t := by
    unfold rvmPathMetric rvmMetric
    dsimp only
    rw [hA0]
    rfl
  exact ⟨hp0, hA0, hH0⟩

lemma h_ray_slab : ∀ {d : ℕ} (α rem : ℝ) (_hrem : 0 < rem)
    (c v : ℕ → (Fin d → ℝ)) (s : ℕ → ℝ) (p u : Fin d → ℝ) (A : Finset ℕ)
    (_hA : ∀ i ∈ A, inSlab α (c i) (v i) (s i) p),
    let δ := pieceStepTime α rem c v s A p u
    let p_next := p + δ • u
    let A_next := A.filter (fun i => inSlab α (c i) (v i) (s i) p_next)
    0 < δ ∧ δ ≤ rem ∧
    (∀ i ∈ A, ∀ τ : ℝ, 0 ≤ τ → τ < δ → inSlab α (c i) (v i) (s i) (p + τ • u)) ∧
    (∀ i ∈ A \ A_next, |dotProduct (p_next - c i) (v i)| = 4 * α * (s i) ^ 2) ∧
    (δ < rem → 1 ≤ (A \ A_next).card ∧ A_next.card < A.card) := by
  intro d α rem hrem c v s p u A hA δ p_next A_next
  have h_fold := h_fold_min A rem (pieceExitDelta α rem c v s p u)
  have hδ_pos : 0 < δ := h_fold.2.2.1 hrem (fun i hi => h_exit_pos α rem hrem c v s p u i (hA i hi))
  have hδ_le : δ ≤ rem := h_fold.1
  have h_dot_ray : ∀ (i : ℕ) (τ : ℝ),
      dotProduct (p + τ • u - c i) (v i) =
        dotProduct (p - c i) (v i) + τ * dotProduct u (v i) := by
    intro i τ
    have h_sub : p + τ • u - c i = (p - c i) + τ • u := by abel
    rw [h_sub, add_dotProduct, smul_dotProduct, smul_eq_mul]
  have h_interior : ∀ i ∈ A, ∀ τ : ℝ, 0 ≤ τ → τ < δ → inSlab α (c i) (v i) (s i) (p + τ • u) := by
    intro i hi τ hτ0 hτδ
    unfold inSlab
    rw [h_dot_ray]
    set φ := dotProduct (p - c i) (v i)
    set β := dotProduct u (v i)
    have hφ := abs_lt.mp (hA i hi)
    have hδ_i : δ ≤ pieceExitDelta α rem c v s p u i := h_fold.2.1 i hi
    unfold pieceExitDelta at hδ_i
    dsimp only at hδ_i
    split_ifs at hδ_i with hβ_pos hβ_neg
    · have h_lt_div : τ < (4 * α * (s i) ^ 2 - φ) / β := lt_of_lt_of_le hτδ hδ_i
      have h_mul : τ * β < 4 * α * (s i) ^ 2 - φ := (lt_div_iff₀ hβ_pos).mp h_lt_div
      have h_nonneg : 0 ≤ τ * β := mul_nonneg hτ0 (le_of_lt hβ_pos)
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    · have h_lt_div : τ < (-4 * α * (s i) ^ 2 - φ) / β := lt_of_lt_of_le hτδ hδ_i
      have h_neg_pos : 0 < -β := neg_pos.mpr hβ_neg
      have h_eq_div : (-4 * α * (s i) ^ 2 - φ) / β = (4 * α * (s i) ^ 2 + φ) / (-β) := by
        rw [← neg_div_neg_eq]
        ring
      rw [h_eq_div] at h_lt_div
      have h_mul : τ * (-β) < 4 * α * (s i) ^ 2 + φ := (lt_div_iff₀ h_neg_pos).mp h_lt_div
      have h_nonpos : τ * β ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hτ0 (le_of_lt hβ_neg)
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    · have hβ0 : β = 0 := by linarith
      rw [hβ0, mul_zero, add_zero]
      exact abs_lt.mpr hφ
  have h_endpoint_le : ∀ i ∈ A, |dotProduct (p_next - c i) (v i)| ≤ 4 * α * (s i) ^ 2 := by
    intro i hi
    dsimp [p_next]
    rw [h_dot_ray]
    set φ := dotProduct (p - c i) (v i)
    set β := dotProduct u (v i)
    have hφ := abs_lt.mp (hA i hi)
    have hδ_i : δ ≤ pieceExitDelta α rem c v s p u i := h_fold.2.1 i hi
    unfold pieceExitDelta at hδ_i
    dsimp only at hδ_i
    split_ifs at hδ_i with hβ_pos hβ_neg
    · have h_mul : δ * β ≤ 4 * α * (s i) ^ 2 - φ := (le_div_iff₀ hβ_pos).mp hδ_i
      have h_nonneg : 0 ≤ δ * β := mul_nonneg (le_of_lt hδ_pos) (le_of_lt hβ_pos)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · have h_neg_pos : 0 < -β := neg_pos.mpr hβ_neg
      have h_eq_div : (-4 * α * (s i) ^ 2 - φ) / β = (4 * α * (s i) ^ 2 + φ) / (-β) := by
        rw [← neg_div_neg_eq]
        ring
      rw [h_eq_div] at hδ_i
      have h_mul : δ * (-β) ≤ 4 * α * (s i) ^ 2 + φ := (le_div_iff₀ h_neg_pos).mp hδ_i
      have h_nonpos : δ * β ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hδ_pos) (le_of_lt hβ_neg)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · have hβ0 : β = 0 := by linarith
      rw [hβ0, mul_zero, add_zero]
      exact le_of_lt (hA i hi)
  have h_boundary : ∀ i ∈ A \ A_next, |dotProduct (p_next - c i) (v i)| = 4 * α * (s i) ^ 2 := by
    intro i hi
    have hiA : i ∈ A := (Finset.mem_sdiff.mp hi).1
    have hi_not : i ∉ A_next := (Finset.mem_sdiff.mp hi).2
    have h_not_in : ¬ inSlab α (c i) (v i) (s i) p_next := by
      intro h_in
      exact hi_not (Finset.mem_filter.mpr ⟨hiA, h_in⟩)
    unfold inSlab at h_not_in
    exact le_antisymm (h_endpoint_le i hiA) (not_lt.mp h_not_in)
  have h_strict : δ < rem → 1 ≤ (A \ A_next).card ∧ A_next.card < A.card := by
    intro h_lt
    obtain ⟨i₀, hi₀A, hi₀_eq⟩ := h_fold.2.2.2 h_lt
    have hi₀_not : i₀ ∉ A_next := by
      intro h_mem
      have h_in : inSlab α (c i₀) (v i₀) (s i₀) p_next := (Finset.mem_filter.mp h_mem).2
      unfold inSlab at h_in
      dsimp [p_next] at h_in
      rw [h_dot_ray] at h_in
      set φ := dotProduct (p - c i₀) (v i₀)
      set β := dotProduct u (v i₀)
      have h_exit : δ = pieceExitDelta α rem c v s p u i₀ := hi₀_eq
      unfold pieceExitDelta at h_exit
      dsimp only at h_exit
      split_ifs at h_exit with hβ_pos hβ_neg
      · have h_mul : δ * β = 4 * α * (s i₀) ^ 2 - φ := by
          rw [h_exit]
          exact div_mul_cancel₀ _ (ne_of_gt hβ_pos)
        have h_sum : φ + δ * β = 4 * α * (s i₀) ^ 2 := by linarith
        rw [h_sum] at h_in
        have := le_abs_self (4 * α * (s i₀) ^ 2)
        linarith
      · have h_mul : δ * β = -4 * α * (s i₀) ^ 2 - φ := by
          rw [h_exit]
          exact div_mul_cancel₀ _ (ne_of_lt hβ_neg)
        have h_sum : φ + δ * β = -(4 * α * (s i₀) ^ 2) := by linarith
        rw [h_sum, abs_neg] at h_in
        have := le_abs_self (4 * α * (s i₀) ^ 2)
        linarith
      · linarith [h_exit, h_lt]
    have h_mem_sdiff : i₀ ∈ A \ A_next := Finset.mem_sdiff.mpr ⟨hi₀A, hi₀_not⟩
    have h_pos : 0 < (A \ A_next).card := Finset.card_pos.mpr ⟨i₀, h_mem_sdiff⟩
    have h_card_eq : (A \ A_next).card + A_next.card = A.card :=
      Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ A)
    have h_aux : ∀ (a b c : ℕ), 0 < a → a + b = c → 1 ≤ a ∧ b < c := by
      intro a b c h1 h2; omega
    exact h_aux _ _ _ h_pos h_card_eq
  exact ⟨hδ_pos, hδ_le, h_interior, h_boundary, h_strict⟩

lemma h_move_sub : ∀ {d : ℕ} (α : ℝ) (n : ℕ) (rem : ℝ) (_hrem : 0 < rem)
    (c v : ℕ → (Fin d → ℝ)) (s γ : ℕ → ℝ) (v_t : Fin d → ℝ)
    (p : Fin d → ℝ) (A : Finset ℕ),
    (∀ i ∈ A, inSlab α (c i) (v i) (s i) p) →
    (rvmMoveEval α c v s γ v_t n rem p A rem).2 ⊆ A := by
  intro d α n
  induction n with
  | zero => intro rem _ c v s γ v_t p A _; exact Finset.Subset.refl A
  | succ n ih =>
    intro rem hrem c v s γ v_t p A hA
    dsimp only [rvmMoveEval]
    set H := stretchMetric A γ v
    set u := H⁻¹ *ᵥ v_t
    set δ := pieceStepTime α rem c v s A p u
    set p_next := p + δ • u
    set A_next := A.filter (fun i => inSlab α (c i) (v i) (s i) p_next)
    have hδ_le : δ ≤ rem := (h_fold_min A rem (pieceExitDelta α rem c v s p u)).1
    rw [if_neg (not_lt.mpr hδ_le)]
    split_ifs with h_lt
    · exact (ih (rem - δ) (by linarith) c v s γ v_t p_next A_next
        (fun i hi => (Finset.mem_filter.mp hi).2)).trans (Finset.filter_subset _ A)
    · exact Finset.filter_subset _ A

lemma h_sdiff_card_le : ∀ (S₁ S₂ S₃ : Finset ℕ),
    S₃ ⊆ S₂ → S₂ ⊆ S₁ →
    (S₁ \ S₂).card + (S₂ \ S₃).card = (S₁ \ S₃).card ∧
    (S₁ \ S₃).card ≤ S₁.card := by
  intro S₁ S₂ S₃ h32 h21
  have hc1 := Finset.card_sdiff_add_card_eq_card h21
  have hc2 := Finset.card_sdiff_add_card_eq_card h32
  have hc3 := Finset.card_sdiff_add_card_eq_card (h32.trans h21)
  omega

lemma h_pieces_bound_aux : ∀ (p_rec d1 d2 d3 cA : ℕ),
    1 ≤ d1 → p_rec ≤ d2 + 1 → d1 + d2 = d3 → d3 ≤ cA →
    1 ≤ 1 + p_rec ∧ 1 + p_rec ≤ d3 + 1 ∧ d3 ≤ cA := by
  intro p_rec d1 d2 d3 cA h1 h2 h3 h4; omega

lemma h_eval_zero : ∀ {d : ℕ} (α : ℝ) (k : ℕ) (rem : ℝ) (_hrem : 0 < rem)
    (c v : ℕ → (Fin d → ℝ)) (s γ : ℕ → ℝ) (v_t : Fin d → ℝ)
    (p : Fin d → ℝ) (A : Finset ℕ),
    (∀ j ∈ A, inSlab α (c j) (v j) (s j) p) →
    rvmMoveEval α c v s γ v_t k rem p A 0 = (p, A) := by
  intro d α k rem hrem c v s γ v_t p A hA
  cases k with
  | zero => rfl
  | succ k' =>
    dsimp only [rvmMoveEval]
    have hδ_pos : 0 < pieceStepTime α rem c v s A p ((stretchMetric A γ v)⁻¹ *ᵥ v_t) :=
      (h_ray_slab α rem hrem c v s p ((stretchMetric A γ v)⁻¹ *ᵥ v_t) A hA).1
    rw [if_pos hδ_pos, zero_smul, add_zero]

lemma h_move_fuel_ind : ∀ {d : ℕ} (α : ℝ) (n : ℕ) (rem : ℝ) (_hrem : 0 < rem)
    (c v : ℕ → (Fin d → ℝ)) (s γ : ℕ → ℝ) (v_t : Fin d → ℝ)
    (p : Fin d → ℝ) (A : Finset ℕ),
    A.card < n →
    (∀ i ∈ A, inSlab α (c i) (v i) (s i) p) →
    let eval := rvmMoveEval α c v s γ v_t n rem p A
    let pieces := rvmMovePieces α c v s γ v_t n rem p A
    eval 0 = (p, A) ∧
    1 ≤ pieces ∧
    pieces ≤ (A \ (eval rem).2).card + 1 ∧
    (A \ (eval rem).2).card ≤ A.card ∧
    (∀ η ∈ Set.Icc 0 rem, ∀ i : ℕ,
      i ∈ (eval η).2 ↔
        (i ∈ A ∧ ∀ τ ∈ Set.Icc 0 η, inSlab α (c i) (v i) (s i) (eval τ).1)) ∧
    (∀ η ∈ Set.Ico 0 rem, ∃ δ' > 0, η + δ' ≤ rem ∧
      ∀ τ ∈ Set.Icc 0 δ',
        (eval (η + τ)).1 = (eval η).1 + τ • ((stretchMetric (eval η).2 γ v)⁻¹ *ᵥ v_t)) := by
  intro d α n
  induction n with
  | zero =>
    intro rem _ c v s γ v_t p A h_card _
    exact False.elim (Nat.not_lt_zero _ h_card)
  | succ m ih =>
    intro rem hrem c v s γ v_t p A h_card hA
    set H := stretchMetric A γ v
    set u := H⁻¹ *ᵥ v_t
    set δ := pieceStepTime α rem c v s A p u
    set p_next := p + δ • u
    set A_next := A.filter (fun i => inSlab α (c i) (v i) (s i) p_next)
    have h_rs := h_ray_slab α rem hrem c v s p u A hA
    have hδ_pos : 0 < δ := h_rs.1
    have hδ_le : δ ≤ rem := h_rs.2.1
    have h_int := h_rs.2.2.1
    have h_strict := h_rs.2.2.2.2
    have hA_next_sub : A_next ⊆ A := Finset.filter_subset _ A
    have hA_next_in : ∀ i ∈ A_next, inSlab α (c i) (v i) (s i) p_next :=
      fun i hi => (Finset.mem_filter.mp hi).2
    have h_eval_lt : ∀ τ < δ, rvmMoveEval α c v s γ v_t (m + 1) rem p A τ = (p + τ • u, A) := by
      intro τ hτ
      dsimp only [rvmMoveEval]
      rw [if_pos hτ]
    have h_eval_0 : rvmMoveEval α c v s γ v_t (m + 1) rem p A 0 = (p, A) := by
      rw [h_eval_lt 0 hδ_pos, zero_smul, add_zero]
    by_cases h_lt : δ < rem
    · have h_str := h_strict h_lt
      have h_card_next : A_next.card < m :=
        Nat.lt_of_lt_of_le h_str.2 (Nat.le_of_lt_succ h_card)
      have h_rec := ih (rem - δ) (by linarith) c v s γ v_t p_next A_next h_card_next hA_next_in
      have h_eval_ge : ∀ τ, δ ≤ τ →
          rvmMoveEval α c v s γ v_t (m + 1) rem p A τ =
            rvmMoveEval α c v s γ v_t m (rem - δ) p_next A_next (τ - δ) := by
        intro τ hτ
        dsimp only [rvmMoveEval]
        rw [if_neg (not_lt.mpr hτ), if_pos h_lt]
      have h_eval_δ : rvmMoveEval α c v s γ v_t (m + 1) rem p A δ = (p_next, A_next) := by
        rw [h_eval_ge δ (le_refl δ), sub_self, h_rec.1]
      have h_eval_rem : rvmMoveEval α c v s γ v_t (m + 1) rem p A rem =
          rvmMoveEval α c v s γ v_t m (rem - δ) p_next A_next (rem - δ) :=
        h_eval_ge rem hδ_le
      have h_pieces_eq : rvmMovePieces α c v s γ v_t (m + 1) rem p A =
          1 + rvmMovePieces α c v s γ v_t m (rem - δ) p_next A_next := by
        dsimp only [rvmMovePieces]
        rw [if_pos h_lt]
      have hA_end_sub : (rvmMoveEval α c v s γ v_t m (rem - δ) p_next A_next (rem - δ)).2 ⊆ A_next :=
        h_move_sub α m (rem - δ) (by linarith) c v s γ v_t p_next A_next hA_next_in
      have h_sc := h_sdiff_card_le A A_next
        (rvmMoveEval α c v s γ v_t m (rem - δ) p_next A_next (rem - δ)).2
        hA_end_sub hA_next_sub
      have h_pb := h_pieces_bound_aux
        (rvmMovePieces α c v s γ v_t m (rem - δ) p_next A_next)
        (A \ A_next).card
        (A_next \ (rvmMoveEval α c v s γ v_t m (rem - δ) p_next A_next (rem - δ)).2).card
        (A \ (rvmMoveEval α c v s γ v_t m (rem - δ) p_next A_next (rem - δ)).2).card
        A.card
        h_str.1 h_rec.2.2.1 h_sc.1 h_sc.2
      have h_p1 : 1 ≤ rvmMovePieces α c v s γ v_t (m + 1) rem p A := by
        rw [h_pieces_eq]; exact h_pb.1
      have h_p2 : rvmMovePieces α c v s γ v_t (m + 1) rem p A ≤
          (A \ (rvmMoveEval α c v s γ v_t (m + 1) rem p A rem).2).card + 1 := by
        rw [h_pieces_eq, h_eval_rem]; exact h_pb.2.1
      have h_p3 : (A \ (rvmMoveEval α c v s γ v_t (m + 1) rem p A rem).2).card ≤ A.card := by
        rw [h_eval_rem]; exact h_pb.2.2
      refine ⟨h_eval_0, h_p1, h_p2, h_p3, ?_, ?_⟩
      · intro η hη i
        by_cases hη_lt : η < δ
        · rw [h_eval_lt η hη_lt]
          dsimp only
          refine ⟨fun hiA => ⟨hiA, ?_⟩, fun h => h.1⟩
          intro τ hτ
          have hτ_lt : τ < δ := lt_of_le_of_lt hτ.2 hη_lt
          rw [h_eval_lt τ hτ_lt]
          exact h_int i hiA τ hτ.1 hτ_lt
        · have hδ_le_η : δ ≤ η := not_lt.mp hη_lt
          rw [h_eval_ge η hδ_le_η]
          have h_iff_rec := h_rec.2.2.2.2.1 (η - δ) ⟨by linarith [hη.1], by linarith [hη.2]⟩ i
          rw [h_iff_rec]
          constructor
          · rintro ⟨hi_next, h_all_rec⟩
            have hiA : i ∈ A := (Finset.mem_filter.mp hi_next).1
            refine ⟨hiA, ?_⟩
            intro τ hτ
            by_cases hτ_lt : τ < δ
            · rw [h_eval_lt τ hτ_lt]
              exact h_int i hiA τ hτ.1 hτ_lt
            · have hδ_le_τ : δ ≤ τ := not_lt.mp hτ_lt
              rw [h_eval_ge τ hδ_le_τ]
              exact h_all_rec (τ - δ) ⟨by linarith, by linarith [hτ.2]⟩
          · rintro ⟨hiA, h_all⟩
            have h_at_δ : inSlab α (c i) (v i) (s i) p_next := by
              have h1 := h_all δ ⟨le_of_lt hδ_pos, hδ_le_η⟩
              rwa [h_eval_δ] at h1
            refine ⟨Finset.mem_filter.mpr ⟨hiA, h_at_δ⟩, ?_⟩
            intro τ' hτ'
            have h1 := h_all (δ + τ') ⟨by linarith [hτ'.1], by linarith [hτ'.2]⟩
            rw [h_eval_ge (δ + τ') (by linarith [hτ'.1]), add_sub_cancel_left] at h1
            exact h1
      · intro η hη
        by_cases hη_lt : η < δ
        · refine ⟨δ - η, by linarith, by linarith, ?_⟩
          intro τ hτ
          rw [h_eval_lt η hη_lt]
          dsimp only
          by_cases hτ_lt : τ < δ - η
          · rw [h_eval_lt (η + τ) (by linarith)]
            dsimp only
            rw [add_smul, add_assoc]
          · have hτ_eq : τ = δ - η := le_antisymm hτ.2 (not_lt.mp hτ_lt)
            have h_sum_eq : η + τ = δ := by linarith
            rw [h_sum_eq, h_eval_δ, hτ_eq]
            change p + δ • u = p + η • u + (δ - η) • u
            rw [add_assoc, ← add_smul, add_sub_cancel]
        · have hδ_le_η : δ ≤ η := not_lt.mp hη_lt
          obtain ⟨δ', hδ'_pos, hδ'_le, hδ'_lin⟩ :=
            h_rec.2.2.2.2.2 (η - δ) ⟨by linarith, by linarith [hη.2]⟩
          refine ⟨δ', hδ'_pos, by linarith, ?_⟩
          intro τ hτ
          rw [h_eval_ge η hδ_le_η, h_eval_ge (η + τ) (by linarith [hτ.1])]
          have h_arg : η + τ - δ = η - δ + τ := by ring
          rw [h_arg]
          exact hδ'_lin τ hτ
    · have hδ_eq : δ = rem := le_antisymm hδ_le (not_lt.mp h_lt)
      have h_eval_rem : rvmMoveEval α c v s γ v_t (m + 1) rem p A rem = (p_next, A_next) := by
        dsimp only [rvmMoveEval]
        rw [if_neg (not_lt.mpr hδ_le), if_neg h_lt]
      have h_pieces_eq : rvmMovePieces α c v s γ v_t (m + 1) rem p A = 1 := by
        dsimp only [rvmMovePieces]
        rw [if_neg h_lt]
      have h_sc := h_sdiff_card_le A A_next A_next (Finset.Subset.refl _) hA_next_sub
      refine ⟨h_eval_0, by rw [h_pieces_eq], by rw [h_pieces_eq]; exact Nat.le_add_left 1 _,
        by rw [h_eval_rem]; exact h_sc.2, ?_, ?_⟩
      · intro η hη i
        by_cases hη_lt : η < δ
        · rw [h_eval_lt η hη_lt]
          dsimp only
          refine ⟨fun hiA => ⟨hiA, ?_⟩, fun h => h.1⟩
          intro τ hτ
          have hτ_lt : τ < δ := lt_of_le_of_lt hτ.2 hη_lt
          rw [h_eval_lt τ hτ_lt]
          exact h_int i hiA τ hτ.1 hτ_lt
        · have hη_eq : η = rem := le_antisymm hη.2 (by linarith [not_lt.mp hη_lt])
          rw [hη_eq, h_eval_rem]
          dsimp only
          rw [Finset.mem_filter]
          constructor
          · rintro ⟨hiA, hi_next⟩
            refine ⟨hiA, ?_⟩
            intro τ hτ
            by_cases hτ_lt : τ < δ
            · rw [h_eval_lt τ hτ_lt]
              exact h_int i hiA τ hτ.1 hτ_lt
            · have hτ_eq : τ = rem := le_antisymm hτ.2 (by linarith [not_lt.mp hτ_lt])
              rw [hτ_eq, h_eval_rem]
              exact hi_next
          · rintro ⟨hiA, h_all⟩
            refine ⟨hiA, ?_⟩
            have h1 := h_all rem ⟨le_of_lt hrem, le_refl rem⟩
            rwa [h_eval_rem] at h1
      · intro η hη
        have hη_lt : η < δ := by linarith [hη.2]
        refine ⟨δ - η, by linarith, by linarith, ?_⟩
        intro τ hτ
        rw [h_eval_lt η hη_lt]
        dsimp only
        by_cases hτ_lt : τ < δ - η
        · rw [h_eval_lt (η + τ) (by linarith)]
          dsimp only
          rw [add_smul, add_assoc]
        · have hτ_eq : τ = δ - η := le_antisymm hτ.2 (not_lt.mp hτ_lt)
          have h_sum_eq : η + τ = rem := by linarith
          rw [h_sum_eq, h_eval_rem, hτ_eq]
          change p + δ • u = p + η • u + (δ - η) • u
          rw [add_assoc, ← add_smul, add_sub_cancel]

lemma h_move_pieces_partition :
    ∀ {d : ℕ} (α : ℝ) (n : ℕ) (rem : ℝ) (_hrem : 0 < rem)
      (c v : ℕ → (Fin d → ℝ)) (s γ : ℕ → ℝ) (v_t : Fin d → ℝ)
      (p : Fin d → ℝ) (A : Finset ℕ),
      A.card < n →
      (∀ i ∈ A, inSlab α (c i) (v i) (s i) p) →
      let eval := rvmMoveEval α c v s γ v_t n rem p A
      let pieces := rvmMovePieces α c v s γ v_t n rem p A
      1 ≤ pieces ∧
      ∃ η : ℕ → ℝ, η 0 = 0 ∧ η pieces = rem ∧
        (∀ j < pieces, η j < η (j + 1)) ∧
        ∀ j < pieces, ∃ a b : Fin d → ℝ,
          ∀ τ ∈ Set.Icc (η j) (η (j + 1)), (eval τ).1 = a + τ • b := by
  intro d α n
  induction n with
  | zero =>
    intro rem _ c v s γ v_t p A h_card _
    exact False.elim (Nat.not_lt_zero _ h_card)
  | succ m ih =>
    intro rem hrem c v s γ v_t p A h_card hA
    set H := stretchMetric A γ v
    set u := H⁻¹ *ᵥ v_t
    set δ := pieceStepTime α rem c v s A p u
    set p_next := p + δ • u
    set A_next := A.filter (fun i => inSlab α (c i) (v i) (s i) p_next)
    have h_rs := h_ray_slab α rem hrem c v s p u A hA
    have hδ_pos : 0 < δ := h_rs.1
    have hδ_le : δ ≤ rem := h_rs.2.1
    have h_strict := h_rs.2.2.2.2
    have hA_next_in : ∀ i ∈ A_next, inSlab α (c i) (v i) (s i) p_next :=
      fun i hi => (Finset.mem_filter.mp hi).2
    have h_eval_lt : ∀ τ < δ, (rvmMoveEval α c v s γ v_t (m + 1) rem p A τ).1 = p + τ • u := by
      intro τ hτ
      dsimp only [rvmMoveEval]
      rw [if_pos hτ]
    by_cases h_lt : δ < rem
    · have h_card_next : A_next.card < m :=
        Nat.lt_of_lt_of_le (h_strict h_lt).2 (Nat.le_of_lt_succ h_card)
      obtain ⟨hp_rec, η_rec, hη_rec0, hη_rec_end, hη_rec_mono, hη_rec_aff⟩ :=
        ih (rem - δ) (by linarith) c v s γ v_t p_next A_next h_card_next hA_next_in
      set pieces_rec := rvmMovePieces α c v s γ v_t m (rem - δ) p_next A_next
      have h_pieces_eq : rvmMovePieces α c v s γ v_t (m + 1) rem p A = pieces_rec + 1 := by
        dsimp only [rvmMovePieces]
        rw [if_pos h_lt, Nat.add_comm]
      have h_eval_ge : ∀ τ, δ ≤ τ →
          rvmMoveEval α c v s γ v_t (m + 1) rem p A τ =
            rvmMoveEval α c v s γ v_t m (rem - δ) p_next A_next (τ - δ) := by
        intro τ hτ
        dsimp only [rvmMoveEval]
        rw [if_neg (not_lt.mpr hτ), if_pos h_lt]
      have h_eval_δ : (rvmMoveEval α c v s γ v_t (m + 1) rem p A δ).1 = p + δ • u := by
        rw [h_eval_ge δ (le_refl δ), sub_self,
            h_eval_zero α m (rem - δ) (by linarith) c v s γ v_t p_next A_next hA_next_in]
      let η : ℕ → ℝ := fun j => match j with
        | 0 => 0
        | k + 1 => δ + η_rec k
      have hη_nonneg : ∀ k ≤ pieces_rec, 0 ≤ η_rec k := by
        intro k
        induction k with
        | zero => intro _; rw [hη_rec0]
        | succ k ih_k =>
          intro hk
          have hk_lt : k < pieces_rec := hk
          have h1 := ih_k (le_of_lt hk_lt)
          have h2 := hη_rec_mono k hk_lt
          linarith
      refine ⟨by rw [h_pieces_eq]; omega, η, rfl, ?_, ?_, ?_⟩
      · rw [h_pieces_eq]
        dsimp [η]
        rw [hη_rec_end]
        ring
      · intro j hj
        rw [h_pieces_eq] at hj
        cases j with
        | zero =>
          dsimp [η]
          rw [hη_rec0]
          linarith
        | succ k =>
          dsimp [η]
          have hk_lt : k < pieces_rec := Nat.lt_of_succ_lt_succ hj
          linarith [hη_rec_mono k hk_lt]
      · intro j hj
        rw [h_pieces_eq] at hj
        cases j with
        | zero =>
          refine ⟨p, u, ?_⟩
          intro τ hτ
          dsimp [η] at hτ
          rw [hη_rec0, add_zero] at hτ
          rcases eq_or_lt_of_le hτ.2 with rfl | hτ_lt
          · exact h_eval_δ
          · exact h_eval_lt τ hτ_lt
        | succ k =>
          have hk_lt : k < pieces_rec := Nat.lt_of_succ_lt_succ hj
          obtain ⟨a', b', hab'⟩ := hη_rec_aff k hk_lt
          refine ⟨a' - δ • b', b', ?_⟩
          intro τ hτ
          dsimp [η] at hτ
          have hη_k_nonneg : 0 ≤ η_rec k := hη_nonneg k (le_of_lt hk_lt)
          have hδ_le_τ : δ ≤ τ := by linarith [hτ.1]
          rw [h_eval_ge τ hδ_le_τ]
          have hτ_sub : τ - δ ∈ Set.Icc (η_rec k) (η_rec (k + 1)) :=
            ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
          rw [hab' (τ - δ) hτ_sub, sub_smul]; abel
    · have hδ_eq : δ = rem := le_antisymm hδ_le (not_lt.mp h_lt)
      have h_pieces_eq : rvmMovePieces α c v s γ v_t (m + 1) rem p A = 1 := by
        dsimp only [rvmMovePieces]
        rw [if_neg h_lt]
      have h_eval_rem : (rvmMoveEval α c v s γ v_t (m + 1) rem p A rem).1 = p + rem • u := by
        dsimp only [rvmMoveEval]
        rw [if_neg (not_lt.mpr hδ_le), if_neg h_lt]
        change p + δ • u = p + rem • u
        rw [hδ_eq]
      let η : ℕ → ℝ := fun j => if j = 0 then 0 else rem
      refine ⟨by rw [h_pieces_eq], η, rfl, ?_, ?_, ?_⟩
      · rw [h_pieces_eq]
        dsimp [η]
      · intro j hj
        rw [h_pieces_eq] at hj
        have hj0 : j = 0 := by omega
        subst hj0
        dsimp [η]
        simpa using hrem
      · intro j hj
        rw [h_pieces_eq] at hj
        have hj0 : j = 0 := by omega
        subst hj0
        refine ⟨p, u, ?_⟩
        intro τ hτ
        dsimp [η] at hτ
        rcases eq_or_lt_of_le hτ.2 with rfl | hτ_lt
        · exact h_eval_rem
        · exact h_eval_lt τ (by linarith)

lemma isOpen_inSlab {d : ℕ} (α : ℝ) (center v_i : Fin d → ℝ) (s_i : ℝ) :
    IsOpen {p : Fin d → ℝ | inSlab α center v_i s_i p} := by
  unfold inSlab
  refine isOpen_lt ?_ continuous_const
  refine Continuous.abs ?_
  unfold dotProduct
  refine continuous_finset_sum _ (fun j _ => ?_)
  exact ((continuous_apply j).sub continuous_const).mul continuous_const

lemma continuousOn_glue_Icc {E : Type*} [TopologicalSpace E] {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) {f : ℝ → E}
    (h1 : ContinuousOn f (Set.Icc a b)) (h2 : ContinuousOn f (Set.Icc b c)) :
    ContinuousOn f (Set.Icc a c) := by
  intro x hx
  rcases lt_trichotomy x b with hlt | h_eq | hgt
  · have h_mem : Set.Iio b ∈ nhdsWithin x (Set.Icc a c) :=
      nhdsWithin_le_nhds (Iio_mem_nhds hlt)
    have h_sub : Set.Icc a c ∩ Set.Iio b ⊆ Set.Icc a b :=
      fun y hy => ⟨hy.1.1, le_of_lt hy.2⟩
    exact (h1 x ⟨hx.1, le_of_lt hlt⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Filter.inter_mem self_mem_nhdsWithin h_mem) h_sub)
  · subst h_eq
    rw [ContinuousWithinAt]
    have h_union : Set.Icc a c = Set.Icc a x ∪ Set.Icc x c := (Set.Icc_union_Icc_eq_Icc hab hbc).symm
    rw [h_union, nhdsWithin_union]
    exact Filter.Tendsto.sup (h1 x ⟨hab, le_refl x⟩) (h2 x ⟨le_refl x, hbc⟩)
  · have h_mem : Set.Ioi b ∈ nhdsWithin x (Set.Icc a c) :=
      nhdsWithin_le_nhds (Ioi_mem_nhds hgt)
    have h_sub : Set.Icc a c ∩ Set.Ioi b ⊆ Set.Icc b c :=
      fun y hy => ⟨le_of_lt hy.2, hy.1.2⟩
    exact (h2 x ⟨le_of_lt hgt, hx.2⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Filter.inter_mem self_mem_nhdsWithin h_mem) h_sub)

lemma continuousOn_of_piecewise_affine {d : ℕ} (m : ℕ) (η : ℕ → ℝ) (f : ℝ → (Fin d → ℝ))
    (h_mono : ∀ j < m, η j < η (j + 1))
    (h_aff : ∀ j < m, ∃ a b : Fin d → ℝ, ∀ τ ∈ Set.Icc (η j) (η (j + 1)), f τ = a + τ • b) :
    ContinuousOn f (Set.Icc (η 0) (η m)) := by
  have h_ind : ∀ k ≤ m, η 0 ≤ η k ∧ ContinuousOn f (Set.Icc (η 0) (η k)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨le_refl _, ?_⟩
      rw [Set.Icc_self]
      exact continuousOn_singleton f (η 0)
    | succ k ih =>
      intro hk
      have hk_lt : k < m := hk
      obtain ⟨h0k, hcont_k⟩ := ih (le_of_lt hk_lt)
      have h_step : η k < η (k + 1) := h_mono k hk_lt
      obtain ⟨a, b, hab⟩ := h_aff k hk_lt
      have h_aff_cont : ContinuousOn (fun τ : ℝ => a + τ • b) (Set.Icc (η k) (η (k + 1))) :=
        (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
      have hcont_seg : ContinuousOn f (Set.Icc (η k) (η (k + 1))) :=
        h_aff_cont.congr (fun τ hτ => hab τ hτ)
      exact ⟨le_trans h0k (le_of_lt h_step),
        continuousOn_glue_Icc h0k (le_of_lt h_step) hcont_k hcont_seg⟩
  exact (h_ind m (le_refl m)).2

lemma hasDerivWithinAt_of_local_right_affine {d : ℕ} (f : ℝ → (Fin d → ℝ)) (η δ : ℝ)
    (hδ : 0 < δ) (u : Fin d → ℝ)
    (h_aff : ∀ τ ∈ Set.Icc 0 δ, f (η + τ) = f η + τ • u) :
    HasDerivWithinAt f u (Set.Ici η) η := by
  let g : ℝ → (Fin d → ℝ) := fun x => f η + (x - η) • u
  have hg_deriv : HasDerivAt g u η := by
    have h1 : HasDerivAt (fun x : ℝ => x - η) 1 η := by
      simpa using (hasDerivAt_id η).sub_const η
    have h2 : HasDerivAt (fun x : ℝ => (x - η) • u) ((1 : ℝ) • u) η := h1.smul_const u
    rw [one_smul] at h2
    exact h2.const_add (f η)
  have hg_within : HasDerivWithinAt g u (Set.Ici η) η := hg_deriv.hasDerivWithinAt
  have h_ev : f =ᶠ[nhdsWithin η (Set.Ici η)] g := by
    have h_mem : Set.Iio (η + δ) ∈ nhdsWithin η (Set.Ici η) :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by linarith))
    refine Filter.eventuallyEq_of_mem (Filter.inter_mem self_mem_nhdsWithin h_mem) ?_
    intro x ⟨hx_ge, hx_lt⟩
    have hx_ge' : η ≤ x := hx_ge
    have hx_lt' : x < η + δ := hx_lt
    have hx_sub : x - η ∈ Set.Icc 0 δ := ⟨by linarith, by linarith⟩
    have h_eq := h_aff (x - η) hx_sub
    have h_add : η + (x - η) = x := by ring
    rw [h_add] at h_eq
    exact h_eq
  exact hg_within.congr_of_eventuallyEq h_ev (by simp [g])

lemma solvesMove_unique_aux {d : ℕ} (α : ℝ) (hα : 0 < α)
    (A₀ : Finset ℕ) (c v : ℕ → (Fin d → ℝ)) (s γ : ℕ → ℝ) (v_t p₀ : Fin d → ℝ)
    (q₁ q₂ : ℝ → (Fin d → ℝ))
    (h1_cont : ContinuousOn q₁ (Set.Icc 0 α))
    (h2_cont : ContinuousOn q₂ (Set.Icc 0 α))
    (h1_0 : q₁ 0 = p₀) (h2_0 : q₂ 0 = p₀)
    (h1_deriv : ∀ η ∈ Set.Ico 0 α, HasDerivWithinAt q₁
      ((stretchMetric (open Classical in A₀.filter (fun i => ∀ τ ∈ Set.Icc 0 η, inSlab α (c i) (v i) (s i) (q₁ τ))) γ v)⁻¹ *ᵥ v_t)
      (Set.Ici η) η)
    (h2_deriv : ∀ η ∈ Set.Ico 0 α, HasDerivWithinAt q₂
      ((stretchMetric (open Classical in A₀.filter (fun i => ∀ τ ∈ Set.Icc 0 η, inSlab α (c i) (v i) (s i) (q₂ τ))) γ v)⁻¹ *ᵥ v_t)
      (Set.Ici η) η) :
    Set.EqOn q₁ q₂ (Set.Icc 0 α) := by
  classical
  let cand (q : ℝ → (Fin d → ℝ)) (η : ℝ) : Finset ℕ :=
    A₀.filter (fun i => ∀ τ ∈ Set.Icc 0 η, inSlab α (c i) (v i) (s i) (q τ))
  let S : Set ℝ := {η ∈ Set.Icc 0 α | ∀ τ ∈ Set.Icc 0 η, q₁ τ = q₂ τ}
  have h0_mem : (0 : ℝ) ∈ S := by
    refine ⟨⟨le_refl 0, le_of_lt hα⟩, ?_⟩
    intro τ hτ
    have hτ0 : τ = 0 := le_antisymm hτ.2 hτ.1
    rw [hτ0, h1_0, h2_0]
  have hS_nonempty : S.Nonempty := ⟨0, h0_mem⟩
  have hS_bdd : BddAbove S := ⟨α, fun η hη => hη.1.2⟩
  set η_star := sSup S
  have hη_ge : 0 ≤ η_star := le_csSup hS_bdd h0_mem
  have hη_le : η_star ≤ α := csSup_le hS_nonempty (fun η hη => hη.1.2)
  have h_lt_eq : ∀ τ ∈ Set.Ico 0 η_star, q₁ τ = q₂ τ := by
    intro τ hτ
    obtain ⟨η, hηS, hτ_lt⟩ := (lt_csSup_iff hS_bdd hS_nonempty).mp hτ.2
    exact hηS.2 τ ⟨hτ.1, le_of_lt hτ_lt⟩
  have h_at_star : q₁ η_star = q₂ η_star := by
    rcases eq_or_lt_of_le hη_ge with h_eq0 | h_pos
    · rw [← h_eq0, h1_0, h2_0]
    · have h_sub : Set.Ico 0 η_star ⊆ Set.Icc 0 α :=
        fun x hx => ⟨hx.1, le_trans (le_of_lt hx.2) hη_le⟩
      have h_t1 : Filter.Tendsto q₁ (nhdsWithin η_star (Set.Ico 0 η_star)) (nhds (q₁ η_star)) :=
        (h1_cont η_star ⟨hη_ge, hη_le⟩).mono h_sub
      have h_t2 : Filter.Tendsto q₂ (nhdsWithin η_star (Set.Ico 0 η_star)) (nhds (q₂ η_star)) :=
        (h2_cont η_star ⟨hη_ge, hη_le⟩).mono h_sub
      have h_ev : q₁ =ᶠ[nhdsWithin η_star (Set.Ico 0 η_star)] q₂ :=
        Filter.eventuallyEq_of_mem self_mem_nhdsWithin h_lt_eq
      have h_t1' : Filter.Tendsto q₂ (nhdsWithin η_star (Set.Ico 0 η_star)) (nhds (q₁ η_star)) :=
        h_t1.congr' h_ev
      haveI : (nhdsWithin η_star (Set.Ico 0 η_star)).NeBot :=
        mem_closure_iff_nhdsWithin_neBot.mp (by rw [closure_Ico (ne_of_lt h_pos)]; exact ⟨hη_ge, le_refl η_star⟩)
      exact tendsto_nhds_unique h_t1' h_t2
  have h_star_mem : η_star ∈ S := by
    refine ⟨⟨hη_ge, hη_le⟩, ?_⟩
    intro τ hτ
    rcases eq_or_lt_of_le hτ.2 with rfl | hlt
    · exact h_at_star
    · exact h_lt_eq τ ⟨hτ.1, hlt⟩
  rcases eq_or_lt_of_le hη_le with h_eq_α | h_lt_α
  · rw [← h_eq_α]
    exact h_star_mem.2
  · exfalso
    set A' := cand q₁ η_star
    have h_cand_eq : cand q₂ η_star = A' := by
      ext i
      simp only [cand, A', Finset.mem_filter]
      refine ⟨fun ⟨hi, h⟩ => ⟨hi, fun τ hτ => ?_⟩, fun ⟨hi, h⟩ => ⟨hi, fun τ hτ => ?_⟩⟩
      · rw [h_star_mem.2 τ hτ]; exact h τ hτ
      · rw [← h_star_mem.2 τ hτ]; exact h τ hτ
    let U : Set (Fin d → ℝ) := ⋂ i ∈ A', {p | inSlab α (c i) (v i) (s i) p}
    have hU_open : IsOpen U := isOpen_biInter_finset (fun i _ => isOpen_inSlab α (c i) (v i) (s i))
    have hq1_in_U : q₁ η_star ∈ U := by
      simp only [U, Set.mem_iInter, Set.mem_setOf_eq]
      intro i hi
      exact (Finset.mem_filter.mp hi).2 η_star ⟨hη_ge, le_refl η_star⟩
    have hq2_in_U : q₂ η_star ∈ U := h_at_star ▸ hq1_in_U
    have h_ev1 : ∀ᶠ x in nhdsWithin η_star (Set.Icc 0 α), q₁ x ∈ U :=
      (h1_cont η_star ⟨hη_ge, hη_le⟩).eventually (hU_open.mem_nhds hq1_in_U)
    have h_ev2 : ∀ᶠ x in nhdsWithin η_star (Set.Icc 0 α), q₂ x ∈ U :=
      (h2_cont η_star ⟨hη_ge, hη_le⟩).eventually (hU_open.mem_nhds hq2_in_U)
    have h_ev_both : ∀ᶠ x in nhdsWithin η_star (Set.Icc 0 α), q₁ x ∈ U ∧ q₂ x ∈ U :=
      h_ev1.and h_ev2
    obtain ⟨ε, hε_pos, hε_sub⟩ := Metric.mem_nhdsWithin_iff.mp h_ev_both
    set δ := min (ε / 2) (α - η_star)
    have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith)
    have hδ_le_α : η_star + δ ≤ α := by
      have : δ ≤ α - η_star := min_le_right _ _
      linarith
    have h_in_U : ∀ x ∈ Set.Icc η_star (η_star + δ), q₁ x ∈ U ∧ q₂ x ∈ U := by
      intro x hx
      have hx_ball : x ∈ Metric.ball η_star ε := by
        rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith [hx.1])]
        have : δ ≤ ε / 2 := min_le_left _ _
        linarith [hx.2]
      exact hε_sub ⟨hx_ball, ⟨le_trans hη_ge hx.1, le_trans hx.2 hδ_le_α⟩⟩
    have h_cand1 : ∀ x ∈ Set.Icc η_star (η_star + δ), cand q₁ x = A' := by
      intro x hx
      ext i
      simp only [cand, A', Finset.mem_filter]
      refine ⟨fun ⟨hi, h⟩ => ⟨hi, fun τ hτ => h τ ⟨hτ.1, le_trans hτ.2 hx.1⟩⟩, ?_⟩
      rintro ⟨hi, h⟩
      refine ⟨hi, fun τ hτ => ?_⟩
      by_cases hτ_le : τ ≤ η_star
      · exact h τ ⟨hτ.1, hτ_le⟩
      · have h_mem_U := (h_in_U τ ⟨le_of_not_ge hτ_le, le_trans hτ.2 hx.2⟩).1
        simp only [U, Set.mem_iInter, Set.mem_setOf_eq] at h_mem_U
        exact h_mem_U i (Finset.mem_filter.mpr ⟨hi, h⟩)
    have h_cand2 : ∀ x ∈ Set.Icc η_star (η_star + δ), cand q₂ x = A' := by
      intro x hx
      rw [← h_cand_eq]
      ext i
      simp only [cand, Finset.mem_filter]
      refine ⟨fun ⟨hi, h⟩ => ⟨hi, fun τ hτ => h τ ⟨hτ.1, le_trans hτ.2 hx.1⟩⟩, ?_⟩
      rintro ⟨hi, h⟩
      refine ⟨hi, fun τ hτ => ?_⟩
      by_cases hτ_le : τ ≤ η_star
      · exact h τ ⟨hτ.1, hτ_le⟩
      · have h_mem_U := (h_in_U τ ⟨le_of_not_ge hτ_le, le_trans hτ.2 hx.2⟩).2
        simp only [U, Set.mem_iInter, Set.mem_setOf_eq] at h_mem_U
        have hi_A' : i ∈ A' := by
          rw [← h_cand_eq]
          exact Finset.mem_filter.mpr ⟨hi, h⟩
        exact h_mem_U i hi_A'
    set u_const := (stretchMetric A' γ v)⁻¹ *ᵥ v_t
    have hd1 : ∀ x ∈ Set.Ico η_star (η_star + δ), HasDerivWithinAt q₁ u_const (Set.Ici x) x := by
      intro x hx
      have h_d := h1_deriv x ⟨le_trans hη_ge hx.1, lt_of_lt_of_le hx.2 hδ_le_α⟩
      change HasDerivWithinAt q₁ ((stretchMetric (cand q₁ x) γ v)⁻¹ *ᵥ v_t) (Set.Ici x) x at h_d
      rwa [h_cand1 x ⟨hx.1, le_of_lt hx.2⟩] at h_d
    have hd2 : ∀ x ∈ Set.Ico η_star (η_star + δ), HasDerivWithinAt q₂ u_const (Set.Ici x) x := by
      intro x hx
      have h_d := h2_deriv x ⟨le_trans hη_ge hx.1, lt_of_lt_of_le hx.2 hδ_le_α⟩
      change HasDerivWithinAt q₂ ((stretchMetric (cand q₂ x) γ v)⁻¹ *ᵥ v_t) (Set.Ici x) x at h_d
      rwa [h_cand2 x ⟨hx.1, le_of_lt hx.2⟩] at h_d
    have h_sub_Icc : Set.Icc η_star (η_star + δ) ⊆ Set.Icc 0 α :=
      fun x hx => ⟨le_trans hη_ge hx.1, le_trans hx.2 hδ_le_α⟩
    have h_eq_ext : ∀ y ∈ Set.Icc η_star (η_star + δ), q₁ y = q₂ y :=
      eq_of_has_deriv_right_eq hd1 hd2 (h1_cont.mono h_sub_Icc) (h2_cont.mono h_sub_Icc) h_at_star
    have h_next_mem : η_star + δ ∈ S := by
      refine ⟨⟨by linarith, hδ_le_α⟩, ?_⟩
      intro τ hτ
      by_cases hτ_le : τ ≤ η_star
      · exact h_star_mem.2 τ ⟨hτ.1, hτ_le⟩
      · exact h_eq_ext τ ⟨le_of_not_ge hτ_le, hτ.2⟩
    have h_le_sup : η_star + δ ≤ η_star := le_csSup hS_bdd h_next_mem
    linarith

end RVMHelpers

section RVMProofs
open RVMHelpers

theorem lem_2_3b : Lemma2_3b_PiecewiseLinearMove :=
by
  intro d hd α hα v h_unit t
  set st := rvmState α v t
  have h_a_all := lem_2_3a hd α hα v h_unit t
  have h_a := h_a_all.1
  have hA_in : ∀ i ∈ st.A, inSlab α (st.c i) (v i) (st.s i) st.p := by
    intro i hi
    obtain ⟨hi_lt, hi_slab⟩ := h_a i hi
    unfold rvmSlab at hi_slab
    rwa [h_state_c α v t i hi_lt, h_state_s α v t i hi_lt]
  have h_res := h_move_fuel_ind α (st.A.card + 1) α hα st.c v st.s st.γ (v t) st.p st.A
    (Nat.lt_succ_self _) hA_in
  have h_part := (h_move_pieces_partition α (st.A.card + 1) α hα st.c v st.s st.γ (v t) st.p st.A
    (Nat.lt_succ_self _) hA_in).2
  have h_active_iff : ∀ η ∈ Set.Icc 0 α, ∀ i : ℕ,
      i ∈ rvmPathActiveSet α v t η ↔
        (i ∈ rvmActiveSet α v t ∧ ∀ τ ∈ Set.Icc 0 η, rvmSlab α v i (rvmPath α v t τ)) := by
    intro η hη i
    unfold rvmPathActiveSet rvmActiveSet rvmPath
    dsimp only
    rw [h_res.2.2.2.2.1 η hη i]
    constructor
    · rintro ⟨hiA, h_all⟩
      have hi_lt : i < t := (h_a i hiA).1
      refine ⟨hiA, ?_⟩
      intro τ hτ
      have h1 := h_all τ hτ
      unfold rvmSlab
      rwa [← h_state_c α v t i hi_lt, ← h_state_s α v t i hi_lt]
    · rintro ⟨hiA, h_all⟩
      have hi_lt : i < t := (h_a i hiA).1
      refine ⟨hiA, ?_⟩
      intro τ hτ
      have h1 := h_all τ hτ
      unfold rvmSlab at h1
      rwa [h_state_c α v t i hi_lt, h_state_s α v t i hi_lt]
  have h_local_aff : ∀ η ∈ Set.Ico 0 α, ∃ δ > 0, η + δ ≤ α ∧
      ∀ τ ∈ Set.Icc 0 δ,
        rvmPath α v t (η + τ) = rvmPath α v t η + τ • ((rvmPathMetric α v t η)⁻¹ *ᵥ v t) :=
    h_res.2.2.2.2.2
  have h_solves : SolvesMove α v t (rvmPath α v t) := by
    obtain ⟨η_seq, hη0, hη_end, hη_mono, hη_aff⟩ := h_part
    have h_cont : ContinuousOn (rvmPath α v t) (Set.Icc 0 α) := by
      have h_c := continuousOn_of_piecewise_affine (rvmRoundPieces α v t) η_seq (rvmPath α v t) hη_mono hη_aff
      have h_eq_Icc : Set.Icc (η_seq 0) (η_seq (rvmRoundPieces α v t)) = Set.Icc 0 α := by
        rw [hη0]
        exact congr_arg (Set.Icc 0) hη_end
      rwa [h_eq_Icc] at h_c
    refine ⟨h_cont, h_a_all.2.1, ?_⟩
    intro η hη
    obtain ⟨δ, hδ_pos, _, hδ_aff⟩ := h_local_aff η hη
    have h_cand_eq : candActiveSet α v t (rvmPath α v t) η = rvmPathActiveSet α v t η := by
      ext i
      simp only [candActiveSet, Finset.mem_filter]
      exact (h_active_iff η ⟨hη.1, le_of_lt hη.2⟩ i).symm
    have h_metric_eq : stretchMetric (candActiveSet α v t (rvmPath α v t) η) (rvmWeight α v) v =
        rvmPathMetric α v t η := by
      unfold rvmPathMetric stretchMetric
      dsimp only
      rw [h_cand_eq]
      congr 1
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hiA : i ∈ rvmActiveSet α v t := ((h_active_iff η ⟨hη.1, le_of_lt hη.2⟩ i).mp hi).1
      have hi_lt : i < t := (h_a i hiA).1
      rw [h_state_gamma α v t i hi_lt]
    rw [h_metric_eq]
    exact hasDerivWithinAt_of_local_right_affine (rvmPath α v t) η δ hδ_pos
      ((rvmPathMetric α v t η)⁻¹ *ᵥ v t) hδ_aff
  have h_unique : ∀ q, SolvesMove α v t q → Set.EqOn q (rvmPath α v t) (Set.Icc 0 α) := by
    intro q hq
    exact solvesMove_unique_aux α hα (rvmActiveSet α v t) (fun i => rvmQuery α v (i + 1)) v
      (rvmStepNorm α v) (rvmWeight α v) (v t) (rvmQuery α v t) q (rvmPath α v t)
      hq.1 h_solves.1 hq.2.1 h_solves.2.1 hq.2.2 h_solves.2.2
  exact ⟨h_res.2.1, h_res.2.2.1, h_res.2.2.2.1, h_active_iff, h_local_aff, h_solves, h_unique, h_part⟩

theorem lem_2_3d : Lemma2_3d_RevocationOnBoundary :=
by
  intro d hd α hα v h_unit
  have h_rev_ind : ∀ (n : ℕ) (rem : ℝ) (_hrem : 0 < rem)
      (c : ℕ → (Fin d → ℝ)) (s γ : ℕ → ℝ) (v_t : Fin d → ℝ)
      (p : Fin d → ℝ) (A : Finset ℕ),
      A.card < n →
      (∀ j ∈ A, inSlab α (c j) (v j) (s j) p) →
      ∀ i ∈ A \ (rvmMoveEval α c v s γ v_t n rem p A rem).2,
        let η := rvmRevocationTime α c v s γ v_t n rem p A i
        let q := rvmRevocationPoint α c v s γ v_t n rem p A i
        0 < η ∧ η ≤ rem ∧
        q = (rvmMoveEval α c v s γ v_t n rem p A η).1 ∧
        (∀ τ ∈ Set.Ico 0 η, i ∈ (rvmMoveEval α c v s γ v_t n rem p A τ).2) ∧
        i ∉ (rvmMoveEval α c v s γ v_t n rem p A η).2 ∧
        |dotProduct (q - c i) (v i)| = 4 * α * (s i) ^ 2 := by
    intro n
    induction n with
    | zero =>
      intro rem _ c s γ v_t p A h_card _
      exact False.elim (Nat.not_lt_zero _ h_card)
    | succ m ih =>
      intro rem hrem c s γ v_t p A h_card hA i hi
      set H := stretchMetric A γ v
      set u := H⁻¹ *ᵥ v_t
      set δ := pieceStepTime α rem c v s A p u
      set p_next := p + δ • u
      set A_next := A.filter (fun j => inSlab α (c j) (v j) (s j) p_next)
      have h_rs := h_ray_slab α rem hrem c v s p u A hA
      have hδ_pos : 0 < δ := h_rs.1
      have hδ_le : δ ≤ rem := h_rs.2.1
      have h_boundary := h_rs.2.2.2.1
      have h_strict := h_rs.2.2.2.2
      have hA_next_in : ∀ j ∈ A_next, inSlab α (c j) (v j) (s j) p_next :=
        fun j hj => (Finset.mem_filter.mp hj).2
      have hiA : i ∈ A := (Finset.mem_sdiff.mp hi).1
      have hi_not_end : i ∉ (rvmMoveEval α c v s γ v_t (m + 1) rem p A rem).2 :=
        (Finset.mem_sdiff.mp hi).2
      have h_eval_lt : ∀ τ < δ, rvmMoveEval α c v s γ v_t (m + 1) rem p A τ = (p + τ • u, A) := by
        intro τ hτ
        dsimp only [rvmMoveEval]
        rw [if_pos hτ]
      by_cases h_cond : i ∈ A_next ∧ δ < rem
      · have hi_next : i ∈ A_next := h_cond.1
        have h_lt : δ < rem := h_cond.2
        have h_str := h_strict h_lt
        have h_card_next : A_next.card < m :=
          Nat.lt_of_lt_of_le h_str.2 (Nat.le_of_lt_succ h_card)
        have h_eval_ge : ∀ τ, δ ≤ τ →
            rvmMoveEval α c v s γ v_t (m + 1) rem p A τ =
              rvmMoveEval α c v s γ v_t m (rem - δ) p_next A_next (τ - δ) := by
          intro τ hτ
          dsimp only [rvmMoveEval]
          rw [if_neg (not_lt.mpr hτ), if_pos h_lt]
        have h_eval_rem : rvmMoveEval α c v s γ v_t (m + 1) rem p A rem =
            rvmMoveEval α c v s γ v_t m (rem - δ) p_next A_next (rem - δ) :=
          h_eval_ge rem hδ_le
        have hi_sdiff_next : i ∈ A_next \ (rvmMoveEval α c v s γ v_t m (rem - δ) p_next A_next (rem - δ)).2 := by
          rw [← h_eval_rem]
          exact Finset.mem_sdiff.mpr ⟨hi_next, hi_not_end⟩
        have h_rec := ih (rem - δ) (by linarith) c s γ v_t p_next A_next h_card_next hA_next_in i hi_sdiff_next
        set η' := rvmRevocationTime α c v s γ v_t m (rem - δ) p_next A_next i
        set q' := rvmRevocationPoint α c v s γ v_t m (rem - δ) p_next A_next i
        have h_time_eq : rvmRevocationTime α c v s γ v_t (m + 1) rem p A i = δ + η' := by
          dsimp only [rvmRevocationTime]
          rw [if_pos h_cond]
        have h_pt_eq : rvmRevocationPoint α c v s γ v_t (m + 1) rem p A i = q' := by
          dsimp only [rvmRevocationPoint]
          rw [if_pos h_cond]
        have h_eval_η : rvmMoveEval α c v s γ v_t (m + 1) rem p A (δ + η') =
            rvmMoveEval α c v s γ v_t m (rem - δ) p_next A_next η' := by
          rw [h_eval_ge (δ + η') (by linarith [h_rec.1]), add_sub_cancel_left]
        refine ⟨by rw [h_time_eq]; linarith [h_rec.1], by rw [h_time_eq]; linarith [h_rec.2.1], ?_, ?_, ?_, ?_⟩
        · rw [h_pt_eq, h_time_eq, h_eval_η]
          exact h_rec.2.2.1
        · intro τ hτ
          rw [h_time_eq] at hτ
          by_cases hτ_lt : τ < δ
          · rw [h_eval_lt τ hτ_lt]
            exact hiA
          · have hδ_le_τ : δ ≤ τ := not_lt.mp hτ_lt
            rw [h_eval_ge τ hδ_le_τ]
            exact h_rec.2.2.2.1 (τ - δ) ⟨by linarith, by linarith [hτ.2]⟩
        · rw [h_time_eq, h_eval_η]
          exact h_rec.2.2.2.2.1
        · rw [h_pt_eq]
          exact h_rec.2.2.2.2.2
      · have h_time_eq : rvmRevocationTime α c v s γ v_t (m + 1) rem p A i = δ := by
          dsimp only [rvmRevocationTime]
          rw [if_neg h_cond]
        have h_pt_eq : rvmRevocationPoint α c v s γ v_t (m + 1) rem p A i = p_next := by
          dsimp only [rvmRevocationPoint]
          rw [if_neg h_cond]
        have hi_not_next : i ∉ A_next := by
          intro hi_next
          have h_not_lt : ¬ (δ < rem) := fun h_lt => h_cond ⟨hi_next, h_lt⟩
          have h_eval_rem : rvmMoveEval α c v s γ v_t (m + 1) rem p A rem = (p_next, A_next) := by
            dsimp only [rvmMoveEval]
            rw [if_neg (not_lt.mpr hδ_le), if_neg h_not_lt]
          rw [h_eval_rem] at hi_not_end
          exact hi_not_end hi_next
        have h_eval_δ : rvmMoveEval α c v s γ v_t (m + 1) rem p A δ = (p_next, A_next) := by
          dsimp only [rvmMoveEval]
          rw [if_neg (lt_irrefl δ)]
          split_ifs with h_lt
          · rw [sub_self, h_eval_zero α m (rem - δ) (by linarith) c v s γ v_t p_next A_next hA_next_in]
          · rfl
        refine ⟨by rw [h_time_eq]; exact hδ_pos, by rw [h_time_eq]; exact hδ_le, ?_, ?_, ?_, ?_⟩
        · rw [h_pt_eq, h_time_eq, h_eval_δ]
        · intro τ hτ
          rw [h_time_eq] at hτ
          rw [h_eval_lt τ hτ.2]
          exact hiA
        · rw [h_time_eq, h_eval_δ]
          exact hi_not_next
        · rw [h_pt_eq]
          exact h_boundary i (Finset.mem_sdiff.mpr ⟨hiA, hi_not_next⟩)
  have h_part1 : ∀ (t : ℕ), ∀ i ∈ rvmRevokedInRound α v t,
      rvmRoundRevokeTime α v t i ∈ Set.Ioc 0 α ∧
      rvmRoundRevokePoint α v t i = rvmPath α v t (rvmRoundRevokeTime α v t i) ∧
      (∀ η ∈ Set.Ico 0 (rvmRoundRevokeTime α v t i), i ∈ rvmPathActiveSet α v t η) ∧
      i ∉ rvmPathActiveSet α v t (rvmRoundRevokeTime α v t i) ∧
      (∃ η ∈ Set.Icc 0 α, rvmRoundRevokePoint α v t i = rvmPath α v t η) ∧
      |dotProduct (rvmRoundRevokePoint α v t i - rvmQuery α v (i + 1)) (v i)| =
        4 * α * (rvmStepNorm α v i) ^ 2 := by
    intro t i hi
    set st := rvmState α v t
    have h_a := (lem_2_3a hd α hα v h_unit t).1
    have hA_in : ∀ j ∈ st.A, inSlab α (st.c j) (v j) (st.s j) st.p := by
      intro j hj
      obtain ⟨hj_lt, hj_slab⟩ := h_a j hj
      unfold rvmSlab at hj_slab
      rwa [h_state_c α v t j hj_lt, h_state_s α v t j hj_lt]
    have h_rev := h_rev_ind (st.A.card + 1) α hα st.c st.s st.γ (v t) st.p st.A
      (Nat.lt_succ_self _) hA_in i hi
    have hiA : i ∈ st.A := (Finset.mem_sdiff.mp hi).1
    have hi_lt : i < t := (h_a i hiA).1
    have h_bd := h_rev.2.2.2.2.2
    rw [h_state_c α v t i hi_lt, h_state_s α v t i hi_lt] at h_bd
    refine ⟨⟨h_rev.1, h_rev.2.1⟩, h_rev.2.2.1, h_rev.2.2.2.1, h_rev.2.2.2.2.1,
      ⟨rvmRoundRevokeTime α v t i, ⟨le_of_lt h_rev.1, h_rev.2.1⟩, h_rev.2.2.1⟩, h_bd⟩
  refine ⟨h_part1, ?_⟩
  intro T
  induction T with
  | zero =>
    intro t ht
    omega
  | succ r ih =>
    intro t ht
    constructor
    · intro ht_not
      have ht_ne : t ≠ r := by
        intro h_eq
        apply ht_not
        rw [h_eq]
        unfold rvmActiveSet rvmState
        dsimp only
        exact Finset.mem_insert_self r _
      have ht_lt_r : t < r := by omega
      have ht_not_after : t ∉ rvmPathActiveSet α v r α := by
        intro h_mem
        apply ht_not
        unfold rvmActiveSet rvmState
        dsimp only
        exact Finset.mem_insert_of_mem h_mem
      unfold rvmDelta
      have h_not_le : ¬ (r ≤ t) := by omega
      by_cases ht_rev : t ∈ rvmRevokedInRound α v r
      · have h_ep : rvmStretchEndPoint α v (r + 1) t = rvmRoundRevokePoint α v r t := by
          unfold rvmStretchEndPoint
          rw [if_neg h_not_le, if_pos ht_rev]
        rw [h_ep]
        exact (h_part1 r t ht_rev).2.2.2.2.2
      · have ht_not_A_r : t ∉ rvmActiveSet α v r := by
          intro h_in_A
          exact ht_rev (Finset.mem_sdiff.mpr ⟨h_in_A, ht_not_after⟩)
        have h_ep : rvmStretchEndPoint α v (r + 1) t = rvmStretchEndPoint α v r t := by
          conv_lhs => unfold rvmStretchEndPoint
          rw [if_neg h_not_le, if_neg ht_rev, if_neg ht_not_after]
        rw [h_ep]
        exact (ih t ht_lt_r).1 ht_not_A_r
    · intro ht_in
      have h_ep := h_endPoint_active α v (r + 1) t ht_in
      have h_slab := ((lem_2_3a hd α hα v h_unit (r + 1)).1 t ht_in).2
      unfold rvmDelta
      rw [h_ep]
      exact h_slab

theorem lem_2_5 : Lemma2_5_OneMove :=
by
  intro d hd α hα w_star v h_unit t
  have h_one_move_ind : ∀ (n : ℕ) (rem : ℝ) (_hrem : 0 < rem)
      (c : ℕ → (Fin d → ℝ)) (s γ : ℕ → ℝ) (_hγ : ∀ i, 0 ≤ γ i) (v_t : Fin d → ℝ)
      (p : Fin d → ℝ) (A : Finset ℕ),
      A.card < n →
      (∀ j ∈ A, inSlab α (c j) (v j) (s j) p) →
      ∀ (p_end : Fin d → ℝ) (A_end : Finset ℕ),
      rvmMoveEval α c v s γ v_t n rem p A rem = (p_end, A_end) →
      ∀ (s_end_sq : ℝ),
      quadForm ((stretchMetric A_end γ v)⁻¹) v_t = s_end_sq →
      0 ≤ s_end_sq ∧
      0 ≤ dotProduct (p_end - p) v_t ∧
      dotProduct (p_end - p) v_t ≤ rem * s_end_sq ∧
      quadForm (stretchMetric A_end γ v) (p_end - w_star) -
          quadForm (stretchMetric A γ v) (p - w_star) ≤
        -2 * rem * dotProduct (w_star - p) v_t + rem ^ 2 * s_end_sq -
          ∑ i ∈ A \ A_end,
            γ i * (dotProduct (w_star - rvmRevocationPoint α c v s γ v_t n rem p A i) (v i)) ^ 2 := by
    intro n
    induction n with
    | zero =>
      intro rem _ c s γ _ v_t p A h_card _
      exact False.elim (Nat.not_lt_zero _ h_card)
    | succ m ih =>
      intro rem hrem c s γ hγ v_t p A h_card hA p_end A_end h_eval s_end_sq hs_end
      set H := stretchMetric A γ v
      set u := H⁻¹ *ᵥ v_t
      set δ := pieceStepTime α rem c v s A p u
      set p_next := p + δ • u
      set A_next := A.filter (fun j => inSlab α (c j) (v j) (s j) p_next)
      set σ_sq := quadForm (H⁻¹) v_t
      have h_rs := h_ray_slab α rem hrem c v s p u A hA
      have hδ_pos : 0 < δ := h_rs.1
      have hδ_le : δ ≤ rem := h_rs.2.1
      have h_strict := h_rs.2.2.2.2
      have hA_next_sub : A_next ⊆ A := Finset.filter_subset _ A
      have hA_next_in : ∀ j ∈ A_next, inSlab α (c j) (v j) (s j) p_next :=
        fun j hj => (Finset.mem_filter.mp hj).2
      have hH_pd : H.PosDef := h_stretch_posDef A γ (fun i _ => hγ i) v
      have hH_det : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH_pd.isUnit
      have hHu : H *ᵥ u = v_t := by
        dsimp [u]
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv H hH_det, Matrix.one_mulVec]
      have hσ_nonneg : 0 ≤ σ_sq := by
        have h_eq : σ_sq = quadForm H u := by
          unfold σ_sq quadForm
          change dotProduct v_t u = dotProduct u (H *ᵥ u)
          rw [hHu, dotProduct_comm]
        rw [h_eq]
        dsimp [H]
        rw [h_quad_stretch]
        have h1 := h_dot_self_nonneg u
        have h2 : 0 ≤ ∑ i ∈ A, γ i * (dotProduct u (v i)) ^ 2 :=
          Finset.sum_nonneg (fun i _ => mul_nonneg (hγ i) (sq_nonneg _))
        linarith
      have h_uv : dotProduct u v_t = σ_sq := dotProduct_comm u v_t
      have h_step_disp : dotProduct (p_next - p) v_t = δ * σ_sq := by
        have h_diff : p_next - p = δ • u := add_sub_cancel_left p (δ • u)
        rw [h_diff, smul_dotProduct, smul_eq_mul, h_uv]
      have h_quad_step : quadForm H (p_next - w_star) - quadForm H (p - w_star) =
          -2 * δ * dotProduct (w_star - p) v_t + δ ^ 2 * σ_sq := by
        unfold quadForm
        set x := p - w_star
        have h_pn : p_next - w_star = x + δ • u := by
          dsimp [p_next, x]
          exact add_sub_right_comm p (δ • u) w_star
        have h_mul : H *ᵥ (x + δ • u) = H *ᵥ x + δ • v_t := by
          rw [Matrix.mulVec_add, Matrix.mulVec_smul, hHu]
        have hH_tr : H.transpose = H := h_stretch_herm A γ v
        have h_symm : dotProduct u (H *ᵥ x) = dotProduct x v_t := by
          rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hH_tr, hHu, dotProduct_comm]
        have h_neg : dotProduct x v_t = -dotProduct (w_star - p) v_t := by
          have : x = -(w_star - p) := (neg_sub w_star p).symm
          rw [this, neg_dotProduct]
        rw [h_pn, h_mul, add_dotProduct, dotProduct_add, dotProduct_add,
          dotProduct_smul, dotProduct_smul, smul_dotProduct, smul_dotProduct,
          smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, h_symm, h_neg, h_uv]
        ring
      have h_quad_drop : quadForm (stretchMetric A_next γ v) (p_next - w_star) -
          quadForm H (p_next - w_star) =
            - ∑ i ∈ A \ A_next, γ i * (dotProduct (w_star - p_next) (v i)) ^ 2 := by
        dsimp only [H]
        rw [h_quad_stretch A_next γ v (p_next - w_star), h_quad_stretch A γ v (p_next - w_star)]
        have h_sdiff := Finset.sum_sdiff hA_next_sub
          (f := fun i => γ i * (dotProduct (p_next - w_star) (v i)) ^ 2)
        have h_sq_eq : ∀ i, (dotProduct (p_next - w_star) (v i)) ^ 2 =
            (dotProduct (w_star - p_next) (v i)) ^ 2 := by
          intro i
          have : p_next - w_star = -(w_star - p_next) := (neg_sub w_star p_next).symm
          rw [this, neg_dotProduct, neg_sq]
        simp_rw [h_sq_eq] at h_sdiff ⊢
        linarith
      have h_rev_first : ∀ i ∈ A \ A_next,
          rvmRevocationPoint α c v s γ v_t (m + 1) rem p A i = p_next := by
        intro i hi
        have hi_not : i ∉ A_next := (Finset.mem_sdiff.mp hi).2
        dsimp only [rvmRevocationPoint]
        rw [if_neg (fun h => hi_not h.1)]
      have h_sum_first : ∑ i ∈ A \ A_next,
          γ i * (dotProduct (w_star - rvmRevocationPoint α c v s γ v_t (m + 1) rem p A i) (v i)) ^ 2 =
            ∑ i ∈ A \ A_next, γ i * (dotProduct (w_star - p_next) (v i)) ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [h_rev_first i hi]
      by_cases h_lt : δ < rem
      · have h_str := h_strict h_lt
        have h_card_next : A_next.card < m :=
          Nat.lt_of_lt_of_le h_str.2 (Nat.le_of_lt_succ h_card)
        have h_eval_rem : rvmMoveEval α c v s γ v_t m (rem - δ) p_next A_next (rem - δ) =
            (p_end, A_end) := by
          rw [← h_eval]
          dsimp only [rvmMoveEval]
          rw [if_neg (not_lt.mpr hδ_le), if_pos h_lt]
        have h_rec := ih (rem - δ) (by linarith) c s γ hγ v_t p_next A_next h_card_next hA_next_in
          p_end A_end h_eval_rem s_end_sq hs_end
        have hA_end_sub_next : A_end ⊆ A_next := by
          have h_sub := h_move_sub α m (rem - δ) (by linarith) c v s γ v_t p_next A_next hA_next_in
          rwa [h_eval_rem] at h_sub
        have hA_end_sub_A : A_end ⊆ A := hA_end_sub_next.trans hA_next_sub
        have h_σ_le_end : σ_sq ≤ s_end_sq := by
          rw [← hs_end]
          exact (h_stretch_inv_mono A A_end hA_end_sub_A γ (fun i _ => hγ i) v v_t).1
        have h_disp_split : dotProduct (p_end - p) v_t =
            dotProduct (p_end - p_next) v_t + dotProduct (p_next - p) v_t := by
          rw [← add_dotProduct, sub_add_sub_cancel]
        have h_disp_nonneg : 0 ≤ dotProduct (p_end - p) v_t := by
          rw [h_disp_split, h_step_disp]
          have : 0 ≤ δ * σ_sq := mul_nonneg (le_of_lt hδ_pos) hσ_nonneg
          linarith [h_rec.2.1]
        have h_disp_upper : dotProduct (p_end - p) v_t ≤ rem * s_end_sq := by
          rw [h_disp_split, h_step_disp]
          have : δ * σ_sq ≤ δ * s_end_sq :=
            mul_le_mul_of_nonneg_left h_σ_le_end (le_of_lt hδ_pos)
          linarith [h_rec.2.2.1]
        have h_rev_second : ∀ i ∈ A_next \ A_end,
            rvmRevocationPoint α c v s γ v_t (m + 1) rem p A i =
              rvmRevocationPoint α c v s γ v_t m (rem - δ) p_next A_next i := by
          intro i hi
          have hi_next : i ∈ A_next := (Finset.mem_sdiff.mp hi).1
          dsimp only [rvmRevocationPoint]
          rw [if_pos ⟨hi_next, h_lt⟩]
        have h_sum_second : ∑ i ∈ A_next \ A_end,
            γ i * (dotProduct (w_star - rvmRevocationPoint α c v s γ v_t (m + 1) rem p A i) (v i)) ^ 2 =
              ∑ i ∈ A_next \ A_end,
                γ i * (dotProduct (w_star - rvmRevocationPoint α c v s γ v_t m (rem - δ) p_next A_next i) (v i)) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [h_rev_second i hi]
        have h_disj : Disjoint (A \ A_next) (A_next \ A_end) := by
          rw [Finset.disjoint_left]
          intro i hi1 hi2
          exact (Finset.mem_sdiff.mp hi1).2 (Finset.mem_sdiff.mp hi2).1
        have h_union : (A \ A_next) ∪ (A_next \ A_end) = A \ A_end := by
          ext i
          simp only [Finset.mem_union, Finset.mem_sdiff]
          constructor
          · rintro (⟨hiA, hi_not_next⟩ | ⟨hi_next, hi_not_end⟩)
            · exact ⟨hiA, fun hi_end => hi_not_next (hA_end_sub_next hi_end)⟩
            · exact ⟨hA_next_sub hi_next, hi_not_end⟩
          · rintro ⟨hiA, hi_not_end⟩
            by_cases hi_next : i ∈ A_next
            · exact Or.inr ⟨hi_next, hi_not_end⟩
            · exact Or.inl ⟨hiA, hi_next⟩
        have h_sum_total : ∑ i ∈ A \ A_end,
            γ i * (dotProduct (w_star - rvmRevocationPoint α c v s γ v_t (m + 1) rem p A i) (v i)) ^ 2 =
              (∑ i ∈ A \ A_next, γ i * (dotProduct (w_star - p_next) (v i)) ^ 2) +
              (∑ i ∈ A_next \ A_end,
                γ i * (dotProduct (w_star - rvmRevocationPoint α c v s γ v_t m (rem - δ) p_next A_next i) (v i)) ^ 2) := by
          rw [← h_union, Finset.sum_union h_disj, h_sum_first, h_sum_second]
        have h_wp_next : dotProduct (w_star - p_next) v_t =
            dotProduct (w_star - p) v_t - δ * σ_sq := by
          have : w_star - p_next = (w_star - p) - (p_next - p) := by abel
          rw [this, sub_dotProduct, h_step_disp]
        have h_quad_coeff : (δ ^ 2 + 2 * δ * (rem - δ)) * σ_sq + (rem - δ) ^ 2 * s_end_sq ≤
            rem ^ 2 * s_end_sq := by
          have h_pos_factor : 0 ≤ δ ^ 2 + 2 * δ * (rem - δ) := by nlinarith
          have h_le : (δ ^ 2 + 2 * δ * (rem - δ)) * σ_sq ≤ (δ ^ 2 + 2 * δ * (rem - δ)) * s_end_sq :=
            mul_le_mul_of_nonneg_left h_σ_le_end h_pos_factor
          calc
            (δ ^ 2 + 2 * δ * (rem - δ)) * σ_sq + (rem - δ) ^ 2 * s_end_sq
              ≤ (δ ^ 2 + 2 * δ * (rem - δ)) * s_end_sq + (rem - δ) ^ 2 * s_end_sq := by linarith
            _ = rem ^ 2 * s_end_sq := by ring
        have h_quad_total : quadForm (stretchMetric A_end γ v) (p_end - w_star) - quadForm H (p - w_star) ≤
            -2 * rem * dotProduct (w_star - p) v_t + rem ^ 2 * s_end_sq -
              ∑ i ∈ A \ A_end,
                γ i * (dotProduct (w_star - rvmRevocationPoint α c v s γ v_t (m + 1) rem p A i) (v i)) ^ 2 := by
          have h_rec_q := h_rec.2.2.2
          rw [h_wp_next] at h_rec_q
          linarith [h_quad_step, h_quad_drop, h_rec_q, h_sum_total, h_quad_coeff]
        exact ⟨h_rec.1, h_disp_nonneg, h_disp_upper, h_quad_total⟩
      · have hδ_eq : δ = rem := le_antisymm hδ_le (not_lt.mp h_lt)
        have h_eval_rem : (p_next, A_next) = (p_end, A_end) := by
          rw [← h_eval]
          dsimp only [rvmMoveEval]
          rw [if_neg (not_lt.mpr hδ_le), if_neg h_lt]
        have hp_end : p_end = p_next := (Prod.mk.inj h_eval_rem).1.symm
        have hA_end : A_end = A_next := (Prod.mk.inj h_eval_rem).2.symm
        have hA_end_sub_A : A_end ⊆ A := by rw [hA_end]; exact hA_next_sub
        have h_σ_le_end : σ_sq ≤ s_end_sq := by
          rw [← hs_end]
          exact (h_stretch_inv_mono A A_end hA_end_sub_A γ (fun i _ => hγ i) v v_t).1
        have hs_end_nonneg : 0 ≤ s_end_sq := le_trans hσ_nonneg h_σ_le_end
        have h_disp_nonneg : 0 ≤ dotProduct (p_end - p) v_t := by
          rw [hp_end, h_step_disp]
          exact mul_nonneg (le_of_lt hδ_pos) hσ_nonneg
        have h_disp_upper : dotProduct (p_end - p) v_t ≤ rem * s_end_sq := by
          rw [hp_end, h_step_disp, hδ_eq]
          exact mul_le_mul_of_nonneg_left h_σ_le_end (le_of_lt hrem)
        have h_quad_total : quadForm (stretchMetric A_end γ v) (p_end - w_star) - quadForm H (p - w_star) ≤
            -2 * rem * dotProduct (w_star - p) v_t + rem ^ 2 * s_end_sq -
              ∑ i ∈ A \ A_end,
                γ i * (dotProduct (w_star - rvmRevocationPoint α c v s γ v_t (m + 1) rem p A i) (v i)) ^ 2 := by
          rw [hp_end, hA_end]
          have h_sq_le : δ ^ 2 * σ_sq ≤ rem ^ 2 * s_end_sq := by
            rw [hδ_eq]
            exact mul_le_mul_of_nonneg_left h_σ_le_end (sq_nonneg rem)
          have h_qs := h_quad_step
          rw [hδ_eq] at h_qs h_sq_le
          linarith [h_qs, h_quad_drop, h_sum_first, h_sq_le]
        exact ⟨hs_end_nonneg, h_disp_nonneg, h_disp_upper, h_quad_total⟩
  set st := rvmState α v t
  have h_a := (lem_2_3a hd α hα v h_unit t).1
  have hA_in : ∀ j ∈ st.A, inSlab α (st.c j) (v j) (st.s j) st.p := by
    intro j hj
    obtain ⟨hj_lt, hj_slab⟩ := h_a j hj
    unfold rvmSlab at hj_slab
    rwa [h_state_c α v t j hj_lt, h_state_s α v t j hj_lt]
  have hγ_nonneg : ∀ i, 0 ≤ st.γ i := h_state_gamma_nonneg α v t
  have h_eval_eq : rvmMoveEval α st.c v st.s st.γ (v t) (st.A.card + 1) α st.p st.A α =
      (rvmQuery α v (t + 1), rvmPathActiveSet α v t α) := Prod.ext rfl rfl
  set s_end_sq := quadForm ((stretchMetric (rvmPathActiveSet α v t α) st.γ v)⁻¹) (v t)
  have h_ind := h_one_move_ind (st.A.card + 1) α hα st.c st.s st.γ hγ_nonneg (v t) st.p st.A
    (Nat.lt_succ_self _) hA_in (rvmQuery α v (t + 1)) (rvmPathActiveSet α v t α) h_eval_eq
    s_end_sq rfl
  have h_s_end_sq : s_end_sq = (rvmStepNorm α v t) ^ 2 := by
    unfold rvmStepNorm rvmDualLength matNorm
    exact (Real.sq_sqrt h_ind.1).symm
  have h_sum_weights : ∑ i ∈ st.A \ rvmPathActiveSet α v t α,
      st.γ i * (dotProduct (w_star - rvmRevocationPoint α st.c v st.s st.γ (v t) (st.A.card + 1) α st.p st.A i) (v i)) ^ 2 =
        ∑ i ∈ rvmRevokedInRound α v t,
          rvmWeight α v i * (dotProduct (w_star - rvmRoundRevokePoint α v t i) (v i)) ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hiA : i ∈ st.A := (Finset.mem_sdiff.mp hi).1
    have hi_lt : i < t := (h_a i hiA).1
    rw [h_state_gamma α v t i hi_lt]
    rfl
  have h_res := h_ind.2
  rw [h_s_end_sq, h_sum_weights] at h_res
  exact h_res

end RVMProofs

namespace SkipHelpers

lemma h_state_c : ∀ {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t i : ℕ),
    i < t → (rvmSkipState α v t).c i = rvmSkipQuery α v (i + 1) := by
  intro d α v t
  induction t with
  | zero => intro i hi; omega
  | succ t ih =>
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | h_eq
    · have hne : i ≠ t := ne_of_lt hlt
      change Function.update (rvmSkipState α v t).c t (rvmSkipQuery α v (t + 1)) i = rvmSkipQuery α v (i + 1)
      rw [Function.update_of_ne hne]
      exact ih i hlt
    · subst h_eq
      change Function.update (rvmSkipState α v i).c i (rvmSkipQuery α v (i + 1)) i = rvmSkipQuery α v (i + 1)
      exact Function.update_self i (rvmSkipQuery α v (i + 1)) (rvmSkipState α v i).c

lemma h_state_s : ∀ {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t i : ℕ),
    i < t → (rvmSkipState α v t).s i = skipStepNorm α v i := by
  intro d α v t
  induction t with
  | zero => intro i hi; omega
  | succ t ih =>
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | h_eq
    · have hne : i ≠ t := ne_of_lt hlt
      change Function.update (rvmSkipState α v t).s t (skipStepNorm α v t) i = skipStepNorm α v i
      rw [Function.update_of_ne hne]
      exact ih i hlt
    · subst h_eq
      change Function.update (rvmSkipState α v i).s i (skipStepNorm α v i) i = skipStepNorm α v i
      exact Function.update_self i (skipStepNorm α v i) (rvmSkipState α v i).s

lemma h_state_gamma : ∀ {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t i : ℕ),
    i < t → (rvmSkipState α v t).γ i = skipWeight α v i := by
  intro d α v t
  induction t with
  | zero => intro i hi; omega
  | succ t ih =>
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | h_eq
    · have hne : i ≠ t := ne_of_lt hlt
      change Function.update (rvmSkipState α v t).γ t (skipWeight α v t) i = skipWeight α v i
      rw [Function.update_of_ne hne]
      exact ih i hlt
    · subst h_eq
      change Function.update (rvmSkipState α v i).γ i (skipWeight α v i) i = skipWeight α v i
      exact Function.update_self i (skipWeight α v i) (rvmSkipState α v i).γ

lemma h_state_gamma_nonneg : ∀ {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t i : ℕ),
    0 ≤ (rvmSkipState α v t).γ i := by
  intro d α v t
  induction t with
  | zero => intro i; exact le_refl 0
  | succ t ih =>
    intro i
    change 0 ≤ Function.update (rvmSkipState α v t).γ t (skipWeight α v t) i
    by_cases h : i = t
    · subst h
      rw [Function.update_self]
      unfold skipWeight
      positivity
    · rw [Function.update_of_ne h]
      exact ih i

lemma h_active_succ_sub : ∀ {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (r : ℕ),
    rvmSkipActiveSet α v (r + 1) ⊆ insert r (rvmSkipPathActiveSet α v r α) := by
  intro d α v r i hi
  change i ∈ (if (skipStepNorm α v r) ^ 2 > ((r + 2 : ℝ) ^ 4)⁻¹ then
    insert r (rvmSkipPathActiveSet α v r α) else rvmSkipPathActiveSet α v r α) at hi
  split_ifs at hi with h_cond
  · exact hi
  · exact Finset.mem_insert_of_mem hi

lemma h_endPoint_active : ∀ {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (r i : ℕ),
    i ∈ rvmSkipActiveSet α v r → skipStretchEndPoint α v r i = rvmSkipQuery α v r := by
  intro d α v r i hi
  cases r with
  | zero =>
    simp [rvmSkipActiveSet, rvmSkipState] at hi
  | succ r =>
    have hi' : i = r ∨ i ∈ rvmSkipPathActiveSet α v r α :=
      Finset.mem_insert.mp (h_active_succ_sub α v r hi)
    unfold skipStretchEndPoint
    by_cases hri : r ≤ i
    · simp [hri]
    · rcases hi' with rfl | h_path
      · exact False.elim (hri (le_refl i))
      · have h_not_rev : i ∉ rvmSkipRevokedInRound α v r := by
          unfold rvmSkipRevokedInRound
          intro h_rev
          exact (Finset.mem_sdiff.mp h_rev).2 h_path
        simp [hri, h_not_rev, h_path]

lemma h_ray_slab : ∀ {d : ℕ} (α rem : ℝ) (_hrem : 0 < rem)
    (c v : ℕ → (Fin d → ℝ)) (s : ℕ → ℝ) (p u : Fin d → ℝ) (A : Finset ℕ)
    (_hA : ∀ i ∈ A, inSlab α (c i) (v i) (s i) p),
    let δ := pieceStepTime α rem c v s A p u
    let p_next := p + δ • u
    let A_next := A.filter (fun i => inSlab α (c i) (v i) (s i) p_next)
    0 < δ ∧ δ ≤ rem ∧
    (∀ i ∈ A \ A_next, |dotProduct (p_next - c i) (v i)| = 4 * α * (s i) ^ 2) ∧
    (δ < rem → A_next.card < A.card) := by
  intro d α rem hrem c v s p u A hA
  have h := RVMHelpers.h_ray_slab α rem hrem c v s p u A hA
  exact ⟨h.1, h.2.1, h.2.2.2.1, fun hlt => (h.2.2.2.2 hlt).2⟩

lemma h_move_preserves : ∀ {d : ℕ} (α : ℝ) (n : ℕ) (rem : ℝ) (_hrem : 0 < rem)
    (c v : ℕ → (Fin d → ℝ)) (s γ : ℕ → ℝ) (v_t : Fin d → ℝ)
    (p : Fin d → ℝ) (A : Finset ℕ),
    (∀ i ∈ A, inSlab α (c i) (v i) (s i) p) →
    let res := rvmMoveEval α c v s γ v_t n rem p A rem
    res.2 ⊆ A ∧ ∀ i ∈ res.2, inSlab α (c i) (v i) (s i) res.1 := by
  intro d α n
  induction n with
  | zero =>
    intro rem _ c v s γ v_t p A hA
    exact ⟨Finset.Subset.refl A, hA⟩
  | succ n ih =>
    intro rem hrem c v s γ v_t p A hA
    dsimp only [rvmMoveEval]
    set H := stretchMetric A γ v
    set u := H⁻¹ *ᵥ v_t
    set δ := pieceStepTime α rem c v s A p u
    set p_next := p + δ • u
    set A_next := A.filter (fun i => inSlab α (c i) (v i) (s i) p_next)
    have hδ_le : δ ≤ rem := (h_fold_min A rem (pieceExitDelta α rem c v s p u)).1
    have h_not_lt : ¬ (rem < δ) := not_lt.mpr hδ_le
    have hA_next_sub : A_next ⊆ A := Finset.filter_subset _ A
    have hA_next_in : ∀ i ∈ A_next, inSlab α (c i) (v i) (s i) p_next :=
      fun i hi => (Finset.mem_filter.mp hi).2
    rw [if_neg h_not_lt]
    split_ifs with h_lt
    · have h_rec := ih (rem - δ) (by linarith) c v s γ v_t p_next A_next hA_next_in
      exact ⟨h_rec.1.trans hA_next_sub, h_rec.2⟩
    · exact ⟨hA_next_sub, hA_next_in⟩

lemma h_step_norm_pos : ∀ {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ))
    (_h_unit : ∀ k, dotProduct (v k) (v k) = 1) (r : ℕ),
    0 < skipStepNorm α v r := by
  intro d α v h_unit r
  set H := skipPathMetric α v r α
  have hγ : ∀ i, 0 ≤ (rvmSkipState α v r).γ i := h_state_gamma_nonneg α v r
  have h_pd : H.PosDef := h_stretch_posDef _ _ (fun i _ => hγ i) v
  have hH_det : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp h_pd.isUnit
  set w := H⁻¹ *ᵥ v r
  have hHw : H *ᵥ w = v r := by
    dsimp [w]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv H hH_det, Matrix.one_mulVec]
  have hw_ne : w ≠ 0 := by
    intro hw0
    have hv0 : v r = 0 := by rw [← hHw, hw0, Matrix.mulVec_zero]
    have h1 := h_unit r
    rw [hv0, dotProduct_zero] at h1
    norm_num at h1
  have h_q_eq : quadForm (H⁻¹) (v r) = quadForm H w := by
    unfold quadForm
    change dotProduct (v r) w = dotProduct w (H *ᵥ w)
    rw [← hHw, dotProduct_comm]
  have h_qw_pos : 0 < quadForm H w := by
    dsimp [H, skipPathMetric]
    rw [h_quad_stretch]
    have := h_dot_pos_of_ne_zero w hw_ne
    have : 0 ≤ ∑ i ∈ rvmSkipPathActiveSet α v r α, (rvmSkipState α v r).γ i * (dotProduct w (v i)) ^ 2 :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hγ i) (sq_nonneg _))
    linarith
  unfold skipStepNorm matNorm
  exact Real.sqrt_pos.mpr (by linarith)

lemma h_skip_inv : ∀ {d : ℕ} (α : ℝ) (_hα : 0 < α) (v : ℕ → (Fin d → ℝ))
    (_h_unit : ∀ k, dotProduct (v k) (v k) = 1) (r : ℕ),
    (∀ i ∈ rvmSkipActiveSet α v r,
      i < r ∧ skipSlab α v i (rvmSkipQuery α v r) ∧ ((i + 2 : ℝ) ^ 4)⁻¹ < (skipStepNorm α v i) ^ 2) ∧
    rvmSkipPathActiveSet α v r α ⊆ rvmSkipActiveSet α v r := by
  intro d α hα v h_unit
  have h_inv : ∀ r, ∀ i ∈ rvmSkipActiveSet α v r,
      i < r ∧ skipSlab α v i (rvmSkipQuery α v r) ∧ ((i + 2 : ℝ) ^ 4)⁻¹ < (skipStepNorm α v i) ^ 2 := by
    intro r
    induction r with
    | zero =>
      intro i hi
      simp [rvmSkipActiveSet, rvmSkipState] at hi
    | succ r ih =>
      intro i hi
      set st := rvmSkipState α v r
      have hA_in : ∀ j ∈ st.A, inSlab α (st.c j) (v j) (st.s j) st.p := by
        intro j hj
        obtain ⟨hj_lt, hj_slab, _⟩ := ih j hj
        unfold skipSlab at hj_slab
        rwa [h_state_c α v r j hj_lt, h_state_s α v r j hj_lt]
      have h_pres := h_move_preserves α (st.A.card + 1) α hα st.c v st.s st.γ (v r) st.p st.A hA_in
      change i ∈ (if (skipStepNorm α v r) ^ 2 > ((r + 2 : ℝ) ^ 4)⁻¹ then
        insert r (rvmSkipPathActiveSet α v r α) else rvmSkipPathActiveSet α v r α) at hi
      split_ifs at hi with h_cond
      · rcases Finset.mem_insert.mp hi with rfl | h_in_after
        · refine ⟨Nat.lt_succ_self i, ?_, h_cond⟩
          unfold skipSlab inSlab
          rw [sub_self, zero_dotProduct, abs_zero]
          have hs_pos := h_step_norm_pos α v h_unit i
          positivity
        · have hi_in_A : i ∈ st.A := h_pres.1 h_in_after
          obtain ⟨hi_lt, _, hi_thresh⟩ := ih i hi_in_A
          have hi_in_slab : inSlab α (st.c i) (v i) (st.s i) (rvmSkipQuery α v (r + 1)) :=
            h_pres.2 i h_in_after
          rw [h_state_c α v r i hi_lt, h_state_s α v r i hi_lt] at hi_in_slab
          exact ⟨Nat.lt_succ_of_lt hi_lt, hi_in_slab, hi_thresh⟩
      · have hi_in_A : i ∈ st.A := h_pres.1 hi
        obtain ⟨hi_lt, _, hi_thresh⟩ := ih i hi_in_A
        have hi_in_slab : inSlab α (st.c i) (v i) (st.s i) (rvmSkipQuery α v (r + 1)) :=
          h_pres.2 i hi
        rw [h_state_c α v r i hi_lt, h_state_s α v r i hi_lt] at hi_in_slab
        exact ⟨Nat.lt_succ_of_lt hi_lt, hi_in_slab, hi_thresh⟩
  intro r
  refine ⟨h_inv r, ?_⟩
  set st := rvmSkipState α v r
  have hA_in : ∀ j ∈ st.A, inSlab α (st.c j) (v j) (st.s j) st.p := by
    intro j hj
    obtain ⟨hj_lt, hj_slab, _⟩ := h_inv r j hj
    unfold skipSlab at hj_slab
    rwa [h_state_c α v r j hj_lt, h_state_s α v r j hj_lt]
  exact (h_move_preserves α (st.A.card + 1) α hα st.c v st.s st.γ (v r) st.p st.A hA_in).1

lemma h_rev_ind : ∀ {d : ℕ} (α : ℝ) (n : ℕ) (rem : ℝ) (_hrem : 0 < rem)
    (c v : ℕ → (Fin d → ℝ)) (s γ : ℕ → ℝ) (v_t : Fin d → ℝ)
    (p : Fin d → ℝ) (A : Finset ℕ),
    A.card < n →
    (∀ j ∈ A, inSlab α (c j) (v j) (s j) p) →
    ∀ i ∈ A \ (rvmMoveEval α c v s γ v_t n rem p A rem).2,
      let q := rvmRevocationPoint α c v s γ v_t n rem p A i
      |dotProduct (q - c i) (v i)| = 4 * α * (s i) ^ 2 := by
  intro d α n
  induction n with
  | zero =>
    intro rem _ c v s γ v_t p A h_card _
    exact False.elim (Nat.not_lt_zero _ h_card)
  | succ m ih =>
    intro rem hrem c v s γ v_t p A h_card hA i hi
    set H := stretchMetric A γ v
    set u := H⁻¹ *ᵥ v_t
    set δ := pieceStepTime α rem c v s A p u
    set p_next := p + δ • u
    set A_next := A.filter (fun j => inSlab α (c j) (v j) (s j) p_next)
    have h_rs := h_ray_slab α rem hrem c v s p u A hA
    have hδ_le : δ ≤ rem := h_rs.2.1
    have h_boundary := h_rs.2.2.1
    have h_strict := h_rs.2.2.2
    have hA_next_in : ∀ j ∈ A_next, inSlab α (c j) (v j) (s j) p_next :=
      fun j hj => (Finset.mem_filter.mp hj).2
    have hiA : i ∈ A := (Finset.mem_sdiff.mp hi).1
    have hi_not_end : i ∉ (rvmMoveEval α c v s γ v_t (m + 1) rem p A rem).2 :=
      (Finset.mem_sdiff.mp hi).2
    by_cases h_cond : i ∈ A_next ∧ δ < rem
    · have hi_next : i ∈ A_next := h_cond.1
      have h_lt : δ < rem := h_cond.2
      have h_card_next : A_next.card < m :=
        Nat.lt_of_lt_of_le (h_strict h_lt) (Nat.le_of_lt_succ h_card)
      have h_eval_rem : rvmMoveEval α c v s γ v_t (m + 1) rem p A rem =
          rvmMoveEval α c v s γ v_t m (rem - δ) p_next A_next (rem - δ) := by
        dsimp only [rvmMoveEval]
        rw [if_neg (not_lt.mpr hδ_le), if_pos h_lt]
      have hi_sdiff_next : i ∈ A_next \ (rvmMoveEval α c v s γ v_t m (rem - δ) p_next A_next (rem - δ)).2 := by
        rw [← h_eval_rem]
        exact Finset.mem_sdiff.mpr ⟨hi_next, hi_not_end⟩
      have h_rec := ih (rem - δ) (by linarith) c v s γ v_t p_next A_next h_card_next hA_next_in i hi_sdiff_next
      have h_pt_eq : rvmRevocationPoint α c v s γ v_t (m + 1) rem p A i =
          rvmRevocationPoint α c v s γ v_t m (rem - δ) p_next A_next i := by
        dsimp only [rvmRevocationPoint]
        rw [if_pos h_cond]
      rw [h_pt_eq]
      exact h_rec
    · have h_pt_eq : rvmRevocationPoint α c v s γ v_t (m + 1) rem p A i = p_next := by
        dsimp only [rvmRevocationPoint]
        rw [if_neg h_cond]
      have hi_not_next : i ∉ A_next := by
        intro hi_next
        have h_not_lt : ¬ (δ < rem) := fun h_lt => h_cond ⟨hi_next, h_lt⟩
        have h_eval_rem : rvmMoveEval α c v s γ v_t (m + 1) rem p A rem = (p_next, A_next) := by
          dsimp only [rvmMoveEval]
          rw [if_neg (not_lt.mpr hδ_le), if_neg h_not_lt]
        rw [h_eval_rem] at hi_not_end
        exact hi_not_end hi_next
      rw [h_pt_eq]
      exact h_boundary i (Finset.mem_sdiff.mpr ⟨hiA, hi_not_next⟩)

lemma h_one_move_ind : ∀ {d : ℕ} (α : ℝ) (w_star : Fin d → ℝ) (n : ℕ) (rem : ℝ) (_hrem : 0 < rem)
    (c v : ℕ → (Fin d → ℝ)) (s γ : ℕ → ℝ) (_hγ : ∀ i, 0 ≤ γ i) (v_t : Fin d → ℝ)
    (p : Fin d → ℝ) (A : Finset ℕ),
    A.card < n →
    (∀ j ∈ A, inSlab α (c j) (v j) (s j) p) →
    ∀ (p_end : Fin d → ℝ) (A_end : Finset ℕ),
    rvmMoveEval α c v s γ v_t n rem p A rem = (p_end, A_end) →
    ∀ (s_end_sq : ℝ),
    quadForm ((stretchMetric A_end γ v)⁻¹) v_t = s_end_sq →
    0 ≤ s_end_sq ∧
    0 ≤ dotProduct (p_end - p) v_t ∧
    dotProduct (p_end - p) v_t ≤ rem * s_end_sq ∧
    quadForm (stretchMetric A_end γ v) (p_end - w_star) -
        quadForm (stretchMetric A γ v) (p - w_star) ≤
      -2 * rem * dotProduct (w_star - p) v_t + rem ^ 2 * s_end_sq -
        ∑ i ∈ A \ A_end,
          γ i * (dotProduct (w_star - rvmRevocationPoint α c v s γ v_t n rem p A i) (v i)) ^ 2 := by
  intro d α w_star n
  induction n with
  | zero =>
    intro rem _ c v s γ _ v_t p A h_card _
    exact False.elim (Nat.not_lt_zero _ h_card)
  | succ m ih =>
    intro rem hrem c v s γ hγ v_t p A h_card hA p_end A_end h_eval s_end_sq hs_end
    set H := stretchMetric A γ v
    set u := H⁻¹ *ᵥ v_t
    set δ := pieceStepTime α rem c v s A p u
    set p_next := p + δ • u
    set A_next := A.filter (fun j => inSlab α (c j) (v j) (s j) p_next)
    set σ_sq := quadForm (H⁻¹) v_t
    have h_rs := h_ray_slab α rem hrem c v s p u A hA
    have hδ_pos : 0 < δ := h_rs.1
    have hδ_le : δ ≤ rem := h_rs.2.1
    have h_strict := h_rs.2.2.2
    have hA_next_sub : A_next ⊆ A := Finset.filter_subset _ A
    have hA_next_in : ∀ j ∈ A_next, inSlab α (c j) (v j) (s j) p_next :=
      fun j hj => (Finset.mem_filter.mp hj).2
    have hH_pd : H.PosDef := h_stretch_posDef A γ (fun i _ => hγ i) v
    have hH_det : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH_pd.isUnit
    have hHu : H *ᵥ u = v_t := by
      dsimp [u]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv H hH_det, Matrix.one_mulVec]
    have hσ_nonneg : 0 ≤ σ_sq := by
      have h_eq : σ_sq = quadForm H u := by
        unfold σ_sq quadForm
        change dotProduct v_t u = dotProduct u (H *ᵥ u)
        rw [hHu, dotProduct_comm]
      rw [h_eq]
      dsimp [H]
      rw [h_quad_stretch]
      have h1 := h_dot_self_nonneg u
      have h2 : 0 ≤ ∑ i ∈ A, γ i * (dotProduct u (v i)) ^ 2 :=
        Finset.sum_nonneg (fun i _ => mul_nonneg (hγ i) (sq_nonneg _))
      linarith
    have h_uv : dotProduct u v_t = σ_sq := dotProduct_comm u v_t
    have h_step_disp : dotProduct (p_next - p) v_t = δ * σ_sq := by
      have h_diff : p_next - p = δ • u := add_sub_cancel_left p (δ • u)
      rw [h_diff, smul_dotProduct, smul_eq_mul, h_uv]
    have h_quad_step : quadForm H (p_next - w_star) - quadForm H (p - w_star) =
        -2 * δ * dotProduct (w_star - p) v_t + δ ^ 2 * σ_sq := by
      unfold quadForm
      set x := p - w_star
      have h_pn : p_next - w_star = x + δ • u := by
        dsimp [p_next, x]
        exact add_sub_right_comm p (δ • u) w_star
      have h_mul : H *ᵥ (x + δ • u) = H *ᵥ x + δ • v_t := by
        rw [Matrix.mulVec_add, Matrix.mulVec_smul, hHu]
      have hH_tr : H.transpose = H := h_stretch_herm A γ v
      have h_symm : dotProduct u (H *ᵥ x) = dotProduct x v_t := by
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hH_tr, hHu, dotProduct_comm]
      have h_neg : dotProduct x v_t = -dotProduct (w_star - p) v_t := by
        have : x = -(w_star - p) := (neg_sub w_star p).symm
        rw [this, neg_dotProduct]
      rw [h_pn, h_mul, add_dotProduct, dotProduct_add, dotProduct_add,
        dotProduct_smul, dotProduct_smul, smul_dotProduct, smul_dotProduct,
        smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, h_symm, h_neg, h_uv]
      ring
    have h_quad_drop : quadForm (stretchMetric A_next γ v) (p_next - w_star) -
        quadForm H (p_next - w_star) =
          - ∑ i ∈ A \ A_next, γ i * (dotProduct (w_star - p_next) (v i)) ^ 2 := by
      dsimp only [H]
      rw [h_quad_stretch A_next γ v (p_next - w_star), h_quad_stretch A γ v (p_next - w_star)]
      have h_sdiff := Finset.sum_sdiff hA_next_sub
        (f := fun i => γ i * (dotProduct (p_next - w_star) (v i)) ^ 2)
      have h_sq_eq : ∀ i, (dotProduct (p_next - w_star) (v i)) ^ 2 =
          (dotProduct (w_star - p_next) (v i)) ^ 2 := by
        intro i
        have : p_next - w_star = -(w_star - p_next) := (neg_sub w_star p_next).symm
        rw [this, neg_dotProduct, neg_sq]
      simp_rw [h_sq_eq] at h_sdiff ⊢
      linarith
    have h_rev_first : ∀ i ∈ A \ A_next,
        rvmRevocationPoint α c v s γ v_t (m + 1) rem p A i = p_next := by
      intro i hi
      have hi_not : i ∉ A_next := (Finset.mem_sdiff.mp hi).2
      dsimp only [rvmRevocationPoint]
      rw [if_neg (fun h => hi_not h.1)]
    have h_sum_first : ∑ i ∈ A \ A_next,
        γ i * (dotProduct (w_star - rvmRevocationPoint α c v s γ v_t (m + 1) rem p A i) (v i)) ^ 2 =
          ∑ i ∈ A \ A_next, γ i * (dotProduct (w_star - p_next) (v i)) ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [h_rev_first i hi]
    by_cases h_lt : δ < rem
    · have h_card_next : A_next.card < m :=
        Nat.lt_of_lt_of_le (h_strict h_lt) (Nat.le_of_lt_succ h_card)
      have h_eval_rem : rvmMoveEval α c v s γ v_t m (rem - δ) p_next A_next (rem - δ) =
          (p_end, A_end) := by
        rw [← h_eval]
        dsimp only [rvmMoveEval]
        rw [if_neg (not_lt.mpr hδ_le), if_pos h_lt]
      have h_rec := ih (rem - δ) (by linarith) c v s γ hγ v_t p_next A_next h_card_next hA_next_in
        p_end A_end h_eval_rem s_end_sq hs_end
      have hA_end_sub_next : A_end ⊆ A_next := by
        have h_sub := (h_move_preserves α m (rem - δ) (by linarith) c v s γ v_t p_next A_next hA_next_in).1
        rwa [h_eval_rem] at h_sub
      have hA_end_sub_A : A_end ⊆ A := hA_end_sub_next.trans hA_next_sub
      have h_σ_le_end : σ_sq ≤ s_end_sq := by
        rw [← hs_end]
        exact (h_stretch_inv_mono A A_end hA_end_sub_A γ (fun i _ => hγ i) v v_t).1
      have h_disp_split : dotProduct (p_end - p) v_t =
          dotProduct (p_end - p_next) v_t + dotProduct (p_next - p) v_t := by
        rw [← add_dotProduct, sub_add_sub_cancel]
      have h_disp_nonneg : 0 ≤ dotProduct (p_end - p) v_t := by
        rw [h_disp_split, h_step_disp]
        have : 0 ≤ δ * σ_sq := mul_nonneg (le_of_lt hδ_pos) hσ_nonneg
        linarith [h_rec.2.1]
      have h_disp_upper : dotProduct (p_end - p) v_t ≤ rem * s_end_sq := by
        rw [h_disp_split, h_step_disp]
        have : δ * σ_sq ≤ δ * s_end_sq :=
          mul_le_mul_of_nonneg_left h_σ_le_end (le_of_lt hδ_pos)
        linarith [h_rec.2.2.1]
      have h_rev_second : ∀ i ∈ A_next \ A_end,
          rvmRevocationPoint α c v s γ v_t (m + 1) rem p A i =
            rvmRevocationPoint α c v s γ v_t m (rem - δ) p_next A_next i := by
        intro i hi
        have hi_next : i ∈ A_next := (Finset.mem_sdiff.mp hi).1
        dsimp only [rvmRevocationPoint]
        rw [if_pos ⟨hi_next, h_lt⟩]
      have h_sum_second : ∑ i ∈ A_next \ A_end,
          γ i * (dotProduct (w_star - rvmRevocationPoint α c v s γ v_t (m + 1) rem p A i) (v i)) ^ 2 =
            ∑ i ∈ A_next \ A_end,
              γ i * (dotProduct (w_star - rvmRevocationPoint α c v s γ v_t m (rem - δ) p_next A_next i) (v i)) ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [h_rev_second i hi]
      have h_disj : Disjoint (A \ A_next) (A_next \ A_end) := by
        rw [Finset.disjoint_left]
        intro i hi1 hi2
        exact (Finset.mem_sdiff.mp hi1).2 (Finset.mem_sdiff.mp hi2).1
      have h_union : (A \ A_next) ∪ (A_next \ A_end) = A \ A_end := by
        ext i
        simp only [Finset.mem_union, Finset.mem_sdiff]
        constructor
        · rintro (⟨hiA, hi_not_next⟩ | ⟨hi_next, hi_not_end⟩)
          · exact ⟨hiA, fun hi_end => hi_not_next (hA_end_sub_next hi_end)⟩
          · exact ⟨hA_next_sub hi_next, hi_not_end⟩
        · rintro ⟨hiA, hi_not_end⟩
          by_cases hi_next : i ∈ A_next
          · exact Or.inr ⟨hi_next, hi_not_end⟩
          · exact Or.inl ⟨hiA, hi_next⟩
      have h_sum_total : ∑ i ∈ A \ A_end,
          γ i * (dotProduct (w_star - rvmRevocationPoint α c v s γ v_t (m + 1) rem p A i) (v i)) ^ 2 =
            (∑ i ∈ A \ A_next, γ i * (dotProduct (w_star - p_next) (v i)) ^ 2) +
            (∑ i ∈ A_next \ A_end,
              γ i * (dotProduct (w_star - rvmRevocationPoint α c v s γ v_t m (rem - δ) p_next A_next i) (v i)) ^ 2) := by
        rw [← h_union, Finset.sum_union h_disj, h_sum_first, h_sum_second]
      have h_wp_next : dotProduct (w_star - p_next) v_t =
          dotProduct (w_star - p) v_t - δ * σ_sq := by
        have : w_star - p_next = (w_star - p) - (p_next - p) := by abel
        rw [this, sub_dotProduct, h_step_disp]
      have h_quad_coeff : (δ ^ 2 + 2 * δ * (rem - δ)) * σ_sq + (rem - δ) ^ 2 * s_end_sq ≤
          rem ^ 2 * s_end_sq := by
        have h_pos_factor : 0 ≤ δ ^ 2 + 2 * δ * (rem - δ) := by nlinarith
        have h_le : (δ ^ 2 + 2 * δ * (rem - δ)) * σ_sq ≤ (δ ^ 2 + 2 * δ * (rem - δ)) * s_end_sq :=
          mul_le_mul_of_nonneg_left h_σ_le_end h_pos_factor
        calc
          (δ ^ 2 + 2 * δ * (rem - δ)) * σ_sq + (rem - δ) ^ 2 * s_end_sq
            ≤ (δ ^ 2 + 2 * δ * (rem - δ)) * s_end_sq + (rem - δ) ^ 2 * s_end_sq := by linarith
          _ = rem ^ 2 * s_end_sq := by ring
      have h_quad_total : quadForm (stretchMetric A_end γ v) (p_end - w_star) - quadForm H (p - w_star) ≤
          -2 * rem * dotProduct (w_star - p) v_t + rem ^ 2 * s_end_sq -
            ∑ i ∈ A \ A_end,
              γ i * (dotProduct (w_star - rvmRevocationPoint α c v s γ v_t (m + 1) rem p A i) (v i)) ^ 2 := by
        have h_rec_q := h_rec.2.2.2
        rw [h_wp_next] at h_rec_q
        linarith [h_quad_step, h_quad_drop, h_rec_q, h_sum_total, h_quad_coeff]
      exact ⟨h_rec.1, h_disp_nonneg, h_disp_upper, h_quad_total⟩
    · have hδ_eq : δ = rem := le_antisymm hδ_le (not_lt.mp h_lt)
      have h_eval_rem : (p_next, A_next) = (p_end, A_end) := by
        rw [← h_eval]
        dsimp only [rvmMoveEval]
        rw [if_neg (not_lt.mpr hδ_le), if_neg h_lt]
      have hp_end : p_end = p_next := (Prod.mk.inj h_eval_rem).1.symm
      have hA_end : A_end = A_next := (Prod.mk.inj h_eval_rem).2.symm
      have hA_end_sub_A : A_end ⊆ A := by rw [hA_end]; exact hA_next_sub
      have h_σ_le_end : σ_sq ≤ s_end_sq := by
        rw [← hs_end]
        exact (h_stretch_inv_mono A A_end hA_end_sub_A γ (fun i _ => hγ i) v v_t).1
      have hs_end_nonneg : 0 ≤ s_end_sq := le_trans hσ_nonneg h_σ_le_end
      have h_disp_nonneg : 0 ≤ dotProduct (p_end - p) v_t := by
        rw [hp_end, h_step_disp]
        exact mul_nonneg (le_of_lt hδ_pos) hσ_nonneg
      have h_disp_upper : dotProduct (p_end - p) v_t ≤ rem * s_end_sq := by
        rw [hp_end, h_step_disp, hδ_eq]
        exact mul_le_mul_of_nonneg_left h_σ_le_end (le_of_lt hrem)
      have h_quad_total : quadForm (stretchMetric A_end γ v) (p_end - w_star) - quadForm H (p - w_star) ≤
          -2 * rem * dotProduct (w_star - p) v_t + rem ^ 2 * s_end_sq -
            ∑ i ∈ A \ A_end,
              γ i * (dotProduct (w_star - rvmRevocationPoint α c v s γ v_t (m + 1) rem p A i) (v i)) ^ 2 := by
        rw [hp_end, hA_end]
        have h_sq_le : δ ^ 2 * σ_sq ≤ rem ^ 2 * s_end_sq := by
          rw [hδ_eq]
          exact mul_le_mul_of_nonneg_left h_σ_le_end (sq_nonneg rem)
        have h_qs := h_quad_step
        rw [hδ_eq] at h_qs h_sq_le
        linarith [h_qs, h_quad_drop, h_sum_first, h_sq_le]
      exact ⟨hs_end_nonneg, h_disp_nonneg, h_disp_upper, h_quad_total⟩

lemma h_skip_one_move : ∀ {d : ℕ} (α : ℝ) (_hα : 0 < α) (w_star : Fin d → ℝ)
    (v : ℕ → (Fin d → ℝ)) (_h_unit : ∀ k, dotProduct (v k) (v k) = 1) (t : ℕ),
    0 ≤ skipXi α v t ∧
    skipXi α v t ≤ α * (skipStepNorm α v t) ^ 2 ∧
    quadForm (skipPathMetric α v t α) (rvmSkipQuery α v (t + 1) - w_star) -
        quadForm (rvmSkipMetric α v t) (rvmSkipQuery α v t - w_star) ≤
      -2 * α * rvmSkipLoss α w_star v t + α ^ 2 * (skipStepNorm α v t) ^ 2 -
        ∑ i ∈ rvmSkipRevokedInRound α v t,
          skipWeight α v i * (dotProduct (w_star - skipRoundRevokePoint α v t i) (v i)) ^ 2 := by
  intro d α hα w_star v h_unit t
  set st := rvmSkipState α v t
  have h_a := (h_skip_inv α hα v h_unit t).1
  have hA_in : ∀ j ∈ st.A, inSlab α (st.c j) (v j) (st.s j) st.p := by
    intro j hj
    obtain ⟨hj_lt, hj_slab, _⟩ := h_a j hj
    unfold skipSlab at hj_slab
    rwa [h_state_c α v t j hj_lt, h_state_s α v t j hj_lt]
  have hγ_nonneg : ∀ i, 0 ≤ st.γ i := h_state_gamma_nonneg α v t
  have h_eval_eq : rvmMoveEval α st.c v st.s st.γ (v t) (st.A.card + 1) α st.p st.A α =
      (rvmSkipQuery α v (t + 1), rvmSkipPathActiveSet α v t α) := Prod.ext rfl rfl
  set s_end_sq := quadForm ((stretchMetric (rvmSkipPathActiveSet α v t α) st.γ v)⁻¹) (v t)
  have h_ind := h_one_move_ind α w_star (st.A.card + 1) α hα st.c v st.s st.γ hγ_nonneg (v t) st.p st.A
    (Nat.lt_succ_self _) hA_in (rvmSkipQuery α v (t + 1)) (rvmSkipPathActiveSet α v t α) h_eval_eq
    s_end_sq rfl
  have h_s_end_sq : s_end_sq = (skipStepNorm α v t) ^ 2 := by
    unfold skipStepNorm matNorm
    exact (Real.sq_sqrt h_ind.1).symm
  have h_sum_weights : ∑ i ∈ st.A \ rvmSkipPathActiveSet α v t α,
      st.γ i * (dotProduct (w_star - rvmRevocationPoint α st.c v st.s st.γ (v t) (st.A.card + 1) α st.p st.A i) (v i)) ^ 2 =
        ∑ i ∈ rvmSkipRevokedInRound α v t,
          skipWeight α v i * (dotProduct (w_star - skipRoundRevokePoint α v t i) (v i)) ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hiA : i ∈ st.A := (Finset.mem_sdiff.mp hi).1
    have hi_lt : i < t := (h_a i hiA).1
    rw [h_state_gamma α v t i hi_lt]
    rfl
  have h_res := h_ind.2
  rw [h_s_end_sq, h_sum_weights] at h_res
  exact h_res

lemma h_skip_ledger : ∀ {d : ℕ} (α : ℝ) (_hα : 0 < α) (w_star : Fin d → ℝ)
    (v : ℕ → (Fin d → ℝ)) (_h_unit : ∀ k, dotProduct (v k) (v k) = 1) (T : ℕ),
    dotProduct (rvmSkipQuery α v T - w_star) (rvmSkipQuery α v T - w_star) -
        dotProduct w_star w_star ≤
      ∑ t ∈ Finset.range T, skipLambda α w_star v T t := by
  intro d α hα w_star v h_unit T
  have h_path_sub : ∀ r, rvmSkipPathActiveSet α v r α ⊆ rvmSkipActiveSet α v r :=
    fun r => (h_skip_inv α hα v h_unit r).2
  have h_active_sub : ∀ r, rvmSkipActiveSet α v r ⊆ Finset.range r := by
    intro r i hi
    exact Finset.mem_range.mpr (((h_skip_inv α hα v h_unit r).1 i hi).1)
  have h_sum_subset_ite : ∀ (r : ℕ) (S : Finset ℕ) (f : ℕ → ℝ),
      S ⊆ Finset.range r →
      ∑ i ∈ S, f i = ∑ i ∈ Finset.range r, if i ∈ S then f i else 0 := by
    intro r S f hS
    rw [← Finset.sum_filter]
    have h_eq : (Finset.range r).filter (· ∈ S) = S := by
      ext x
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun hx => ⟨hS hx, hx⟩⟩
    rw [h_eq]
  have h_ind : ∀ r : ℕ,
      dotProduct (rvmSkipQuery α v r - w_star) (rvmSkipQuery α v r - w_star) +
        ∑ t ∈ Finset.range r,
          skipWeight α v t * (dotProduct (w_star - skipStretchEndPoint α v r t) (v t)) ^ 2 -
        dotProduct w_star w_star ≤
      ∑ t ∈ Finset.range r,
        (-2 * α * rvmSkipLoss α w_star v t + α ^ 2 * (skipStepNorm α v t) ^ 2 +
          skipWeight α v t * (dotProduct (w_star - rvmSkipQuery α v (t + 1)) (v t)) ^ 2) := by
    intro r
    induction r with
    | zero =>
      have hq0 : rvmSkipQuery α v 0 = 0 := rfl
      rw [hq0, Finset.range_zero, Finset.sum_empty, Finset.sum_empty, zero_sub,
          dotProduct_neg, neg_dotProduct, neg_neg, add_zero, sub_self]
    | succ r ih =>
      have h_move := (h_skip_one_move α hα w_star v h_unit r).2.2
      have h_quad_start : quadForm (rvmSkipMetric α v r) (rvmSkipQuery α v r - w_star) =
          dotProduct (rvmSkipQuery α v r - w_star) (rvmSkipQuery α v r - w_star) +
            ∑ i ∈ Finset.range r,
              if i ∈ rvmSkipActiveSet α v r then
                skipWeight α v i * (dotProduct (w_star - rvmSkipQuery α v r) (v i)) ^ 2
              else 0 := by
        unfold rvmSkipMetric
        rw [h_quad_stretch]
        congr 1
        rw [← h_sum_subset_ite r (rvmSkipActiveSet α v r) _ (h_active_sub r)]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi_lt : i < r := Finset.mem_range.mp (h_active_sub r hi)
        rw [h_state_gamma α v r i hi_lt]
        have h_sub_sq : (dotProduct (rvmSkipQuery α v r - w_star) (v i)) ^ 2 =
            (dotProduct (w_star - rvmSkipQuery α v r) (v i)) ^ 2 := by
          rw [sub_dotProduct, sub_dotProduct]
          ring
        rw [h_sub_sq]
      have h_quad_end : quadForm (skipPathMetric α v r α) (rvmSkipQuery α v (r + 1) - w_star) =
          dotProduct (rvmSkipQuery α v (r + 1) - w_star) (rvmSkipQuery α v (r + 1) - w_star) +
            ∑ i ∈ Finset.range r,
              if i ∈ rvmSkipPathActiveSet α v r α then
                skipWeight α v i * (dotProduct (w_star - rvmSkipQuery α v (r + 1)) (v i)) ^ 2
              else 0 := by
        unfold skipPathMetric
        rw [h_quad_stretch]
        congr 1
        have h_sub_r : rvmSkipPathActiveSet α v r α ⊆ Finset.range r :=
          (h_path_sub r).trans (h_active_sub r)
        rw [← h_sum_subset_ite r (rvmSkipPathActiveSet α v r α) _ h_sub_r]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi_lt : i < r := Finset.mem_range.mp (h_sub_r hi)
        rw [h_state_gamma α v r i hi_lt]
        have h_sub_sq : (dotProduct (rvmSkipQuery α v (r + 1) - w_star) (v i)) ^ 2 =
            (dotProduct (w_star - rvmSkipQuery α v (r + 1)) (v i)) ^ 2 := by
          rw [sub_dotProduct, sub_dotProduct]
          ring
        rw [h_sub_sq]
      have h_rev_sub : rvmSkipRevokedInRound α v r ⊆ Finset.range r := by
        intro i hi
        exact h_active_sub r (Finset.mem_sdiff.mp hi).1
      have h_rev_sum : ∑ i ∈ rvmSkipRevokedInRound α v r,
            skipWeight α v i * (dotProduct (w_star - skipRoundRevokePoint α v r i) (v i)) ^ 2 =
          ∑ i ∈ Finset.range r,
            if i ∈ rvmSkipRevokedInRound α v r then
              skipWeight α v i * (dotProduct (w_star - skipRoundRevokePoint α v r i) (v i)) ^ 2
            else 0 :=
        h_sum_subset_ite r (rvmSkipRevokedInRound α v r) _ h_rev_sub
      have h_pointwise : ∀ i ∈ Finset.range r,
          skipWeight α v i * (dotProduct (w_star - skipStretchEndPoint α v (r + 1) i) (v i)) ^ 2 -
            skipWeight α v i * (dotProduct (w_star - skipStretchEndPoint α v r i) (v i)) ^ 2 =
          (if i ∈ rvmSkipPathActiveSet α v r α then
            skipWeight α v i * (dotProduct (w_star - rvmSkipQuery α v (r + 1)) (v i)) ^ 2
          else 0) +
          (if i ∈ rvmSkipRevokedInRound α v r then
            skipWeight α v i * (dotProduct (w_star - skipRoundRevokePoint α v r i) (v i)) ^ 2
          else 0) -
          (if i ∈ rvmSkipActiveSet α v r then
            skipWeight α v i * (dotProduct (w_star - rvmSkipQuery α v r) (v i)) ^ 2
          else 0) := by
        intro i hi
        have hi_lt : i < r := Finset.mem_range.mp hi
        have h_not_le : ¬ (r ≤ i) := not_le.mpr hi_lt
        by_cases hA : i ∈ rvmSkipActiveSet α v r
        · have h_end_r : skipStretchEndPoint α v r i = rvmSkipQuery α v r := h_endPoint_active α v r i hA
          by_cases hP : i ∈ rvmSkipPathActiveSet α v r α
          · have h_not_rev : i ∉ rvmSkipRevokedInRound α v r := by
              unfold rvmSkipRevokedInRound
              intro h_rev
              exact (Finset.mem_sdiff.mp h_rev).2 hP
            have h_end_succ : skipStretchEndPoint α v (r + 1) i = rvmSkipQuery α v (r + 1) := by
              rw [skipStretchEndPoint]
              simp [h_not_le, h_not_rev, hP]
            simp [hA, hP, h_not_rev, h_end_r, h_end_succ]
          · have h_rev : i ∈ rvmSkipRevokedInRound α v r := Finset.mem_sdiff.mpr ⟨hA, hP⟩
            have h_end_succ : skipStretchEndPoint α v (r + 1) i = skipRoundRevokePoint α v r i := by
              rw [skipStretchEndPoint]
              simp [h_not_le, h_rev]
            simp [hA, hP, h_rev, h_end_r, h_end_succ]
        · have hP : i ∉ rvmSkipPathActiveSet α v r α := fun hp => hA (h_path_sub r hp)
          have h_not_rev : i ∉ rvmSkipRevokedInRound α v r := fun h_rev => hA (Finset.mem_sdiff.mp h_rev).1
          have h_end_succ : skipStretchEndPoint α v (r + 1) i = skipStretchEndPoint α v r i := by
            rw [skipStretchEndPoint]
            simp [h_not_le, h_not_rev, hP]
          simp [hA, hP, h_not_rev, h_end_succ]
      have h_sum_diff : ∑ i ∈ Finset.range r,
            skipWeight α v i * (dotProduct (w_star - skipStretchEndPoint α v (r + 1) i) (v i)) ^ 2 -
          ∑ i ∈ Finset.range r,
            skipWeight α v i * (dotProduct (w_star - skipStretchEndPoint α v r i) (v i)) ^ 2 =
        ∑ i ∈ Finset.range r,
            (if i ∈ rvmSkipPathActiveSet α v r α then
              skipWeight α v i * (dotProduct (w_star - rvmSkipQuery α v (r + 1)) (v i)) ^ 2
            else 0) +
          ∑ i ∈ Finset.range r,
            (if i ∈ rvmSkipRevokedInRound α v r then
              skipWeight α v i * (dotProduct (w_star - skipRoundRevokePoint α v r i) (v i)) ^ 2
            else 0) -
          ∑ i ∈ Finset.range r,
            (if i ∈ rvmSkipActiveSet α v r then
              skipWeight α v i * (dotProduct (w_star - rvmSkipQuery α v r) (v i)) ^ 2
            else 0) := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl h_pointwise
      have h_end_self : skipStretchEndPoint α v (r + 1) r = rvmSkipQuery α v (r + 1) := by
        rw [skipStretchEndPoint]
        simp
      rw [Finset.sum_range_succ, Finset.sum_range_succ, h_end_self]
      linarith
  have h_lambda_id : ∀ t ∈ Finset.range T,
      skipLambda α w_star v T t =
        (-2 * α * rvmSkipLoss α w_star v t + α ^ 2 * (skipStepNorm α v t) ^ 2 +
          skipWeight α v t * (dotProduct (w_star - rvmSkipQuery α v (t + 1)) (v t)) ^ 2) -
        skipWeight α v t * (dotProduct (w_star - skipStretchEndPoint α v T t) (v t)) ^ 2 := by
    intro t _
    unfold skipLambda rvmSkipLoss skipXi skipDelta
    dsimp only
    have h1 : dotProduct (w_star - rvmSkipQuery α v (t + 1)) (v t) =
        dotProduct (w_star - rvmSkipQuery α v t) (v t) -
          dotProduct (rvmSkipQuery α v (t + 1) - rvmSkipQuery α v t) (v t) := by
      rw [sub_dotProduct, sub_dotProduct, sub_dotProduct]
      ring
    have h2 : dotProduct (w_star - skipStretchEndPoint α v T t) (v t) =
        dotProduct (w_star - rvmSkipQuery α v (t + 1)) (v t) -
          dotProduct (skipStretchEndPoint α v T t - rvmSkipQuery α v (t + 1)) (v t) := by
      rw [sub_dotProduct, sub_dotProduct, sub_dotProduct]
      ring
    rw [h2, h1]
    ring
  have h_sum_lambda : ∑ t ∈ Finset.range T, skipLambda α w_star v T t =
      ∑ t ∈ Finset.range T,
        (-2 * α * rvmSkipLoss α w_star v t + α ^ 2 * (skipStepNorm α v t) ^ 2 +
          skipWeight α v t * (dotProduct (w_star - rvmSkipQuery α v (t + 1)) (v t)) ^ 2) -
      ∑ t ∈ Finset.range T,
        skipWeight α v t * (dotProduct (w_star - skipStretchEndPoint α v T t) (v t)) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl h_lambda_id
  have h_nonneg_rem : 0 ≤ ∑ t ∈ Finset.range T,
      skipWeight α v t * (dotProduct (w_star - skipStretchEndPoint α v T t) (v t)) ^ 2 := by
    refine Finset.sum_nonneg (fun t _ => ?_)
    unfold skipWeight
    positivity
  linarith [h_ind T]

lemma h_skip_lifetime : ∀ {d : ℕ} (α : ℝ) (_hα : 0 < α) (w_star : Fin d → ℝ)
    (v : ℕ → (Fin d → ℝ)) (_h_unit : ∀ k, dotProduct (v k) (v k) = 1) (T t : ℕ),
    t < T →
    0 ≤ rvmSkipLoss α w_star v t →
    skipLambda α w_star v T t ≤
      -α * rvmSkipLoss α w_star v t +
        (if t ∈ rvmSkipActiveSet α v T then (9 / 8 : ℝ) * α ^ 2 * (skipStepNorm α v t) ^ 2 else 0) +
        α ^ 2 * ((t + 2 : ℝ) ^ 4)⁻¹ := by
  intro d α hα w_star v h_unit T t htT hr_nonneg
  have h_part1 : ∀ (r : ℕ), ∀ i ∈ rvmSkipRevokedInRound α v r,
      |dotProduct (skipRoundRevokePoint α v r i - rvmSkipQuery α v (i + 1)) (v i)| =
        4 * α * (skipStepNorm α v i) ^ 2 := by
    intro r i hi
    set st := rvmSkipState α v r
    have h_a := (h_skip_inv α hα v h_unit r).1
    have hA_in : ∀ j ∈ st.A, inSlab α (st.c j) (v j) (st.s j) st.p := by
      intro j hj
      obtain ⟨hj_lt, hj_slab, _⟩ := h_a j hj
      unfold skipSlab at hj_slab
      rwa [h_state_c α v r j hj_lt, h_state_s α v r j hj_lt]
    have h_bd := h_rev_ind α (st.A.card + 1) α hα st.c v st.s st.γ (v r) st.p st.A
      (Nat.lt_succ_self _) hA_in i hi
    have hiA : i ∈ st.A := (Finset.mem_sdiff.mp hi).1
    have hi_lt : i < r := (h_a i hiA).1
    rwa [h_state_c α v r i hi_lt, h_state_s α v r i hi_lt] at h_bd
  by_cases h_made : (skipStepNorm α v t) ^ 2 > ((t + 2 : ℝ) ^ 4)⁻¹
  · have h_delta_ind : ∀ (R_hor : ℕ), t < R_hor →
        (t ∉ rvmSkipActiveSet α v R_hor → |skipDelta α v R_hor t| = 4 * α * (skipStepNorm α v t) ^ 2) ∧
        (t ∈ rvmSkipActiveSet α v R_hor → |skipDelta α v R_hor t| < 4 * α * (skipStepNorm α v t) ^ 2) := by
      intro R_hor
      induction R_hor with
      | zero => intro ht; omega
      | succ r ih =>
        intro ht
        constructor
        · intro ht_not
          have ht_ne : t ≠ r := by
            intro h_eq
            apply ht_not
            subst h_eq
            change t ∈ (if (skipStepNorm α v t) ^ 2 > ((t + 2 : ℝ) ^ 4)⁻¹ then
              insert t (rvmSkipPathActiveSet α v t α) else rvmSkipPathActiveSet α v t α)
            rw [if_pos h_made]
            exact Finset.mem_insert_self t _
          have ht_lt_r : t < r := by omega
          have ht_not_after : t ∉ rvmSkipPathActiveSet α v r α := by
            intro h_mem
            apply ht_not
            change t ∈ (if (skipStepNorm α v r) ^ 2 > ((r + 2 : ℝ) ^ 4)⁻¹ then
              insert r (rvmSkipPathActiveSet α v r α) else rvmSkipPathActiveSet α v r α)
            split_ifs
            · exact Finset.mem_insert_of_mem h_mem
            · exact h_mem
          unfold skipDelta
          have h_not_le : ¬ (r ≤ t) := by omega
          by_cases ht_rev : t ∈ rvmSkipRevokedInRound α v r
          · have h_ep : skipStretchEndPoint α v (r + 1) t = skipRoundRevokePoint α v r t := by
              unfold skipStretchEndPoint
              rw [if_neg h_not_le, if_pos ht_rev]
            rw [h_ep]
            exact h_part1 r t ht_rev
          · have ht_not_A_r : t ∉ rvmSkipActiveSet α v r := by
              intro h_in_A
              exact ht_rev (Finset.mem_sdiff.mpr ⟨h_in_A, ht_not_after⟩)
            have h_ep : skipStretchEndPoint α v (r + 1) t = skipStretchEndPoint α v r t := by
              conv_lhs => unfold skipStretchEndPoint
              rw [if_neg h_not_le, if_neg ht_rev, if_neg ht_not_after]
            rw [h_ep]
            exact (ih ht_lt_r).1 ht_not_A_r
        · intro ht_in
          have h_ep := h_endPoint_active α v (r + 1) t ht_in
          have h_slab := ((h_skip_inv α hα v h_unit (r + 1)).1 t ht_in).2.1
          unfold skipDelta
          rw [h_ep]
          exact h_slab
    have h_d := h_delta_ind T htT
    have hs_pos : 0 < skipStepNorm α v t := h_step_norm_pos α v h_unit t
    have h_m := h_skip_one_move α hα w_star v h_unit t
    have hξ_nonneg : 0 ≤ skipXi α v t := h_m.1
    have hξ_le : skipXi α v t ≤ α * (skipStepNorm α v t) ^ 2 := h_m.2.1
    have hγ_eq : skipWeight α v t * (8 * (skipStepNorm α v t) ^ 2) = 1 := by
      unfold skipWeight
      exact div_mul_cancel₀ 1 (ne_of_gt (by positivity))
    have hγ_pos : 0 < skipWeight α v t := by
      unfold skipWeight
      positivity
    have h_extra_pos : 0 ≤ α ^ 2 * ((t + 2 : ℝ) ^ 4)⁻¹ := by positivity
    by_cases h_mem : t ∈ rvmSkipActiveSet α v T
    · simp only [h_mem, ↓reduceIte]
      have hΔ_abs : |skipDelta α v T t| < 4 * α * (skipStepNorm α v t) ^ 2 := h_d.2 h_mem
      have hΔ_le : skipDelta α v T t ≤ 4 * α * (skipStepNorm α v t) ^ 2 :=
        (le_abs_self _).trans (le_of_lt hΔ_abs)
      have h_sq_nonneg : 0 ≤ (skipDelta α v T t + skipXi α v t) ^ 2 := sq_nonneg _
      have h_xi_sq : (skipXi α v t) ^ 2 ≤ α ^ 2 * (skipStepNorm α v t) ^ 4 := by nlinarith
      have h_quad : -(α ^ 2 * (skipStepNorm α v t) ^ 4) ≤
          skipDelta α v T t * (skipDelta α v T t + 2 * skipXi α v t) := by nlinarith
      have h_r_term : 2 * skipDelta α v T t * rvmSkipLoss α w_star v t ≤
          8 * α * (skipStepNorm α v t) ^ 2 * rvmSkipLoss α w_star v t := by nlinarith
      have h_comb : 2 * skipDelta α v T t * rvmSkipLoss α w_star v t -
            skipDelta α v T t * (skipDelta α v T t + 2 * skipXi α v t) ≤
          (8 * (skipStepNorm α v t) ^ 2) *
            (α * rvmSkipLoss α w_star v t + (1 / 8 : ℝ) * α ^ 2 * (skipStepNorm α v t) ^ 2) := by
        linarith
      have h_mul := mul_le_mul_of_nonneg_left h_comb (le_of_lt hγ_pos)
      have h_rhs : skipWeight α v t * ((8 * (skipStepNorm α v t) ^ 2) *
            (α * rvmSkipLoss α w_star v t + (1 / 8 : ℝ) * α ^ 2 * (skipStepNorm α v t) ^ 2)) =
          α * rvmSkipLoss α w_star v t + (1 / 8 : ℝ) * α ^ 2 * (skipStepNorm α v t) ^ 2 := by
        calc skipWeight α v t * ((8 * (skipStepNorm α v t) ^ 2) *
              (α * rvmSkipLoss α w_star v t + (1 / 8 : ℝ) * α ^ 2 * (skipStepNorm α v t) ^ 2))
          _ = (skipWeight α v t * (8 * (skipStepNorm α v t) ^ 2)) *
              (α * rvmSkipLoss α w_star v t + (1 / 8 : ℝ) * α ^ 2 * (skipStepNorm α v t) ^ 2) := by ring
          _ = 1 * (α * rvmSkipLoss α w_star v t + (1 / 8 : ℝ) * α ^ 2 * (skipStepNorm α v t) ^ 2) := by rw [hγ_eq]
          _ = α * rvmSkipLoss α w_star v t + (1 / 8 : ℝ) * α ^ 2 * (skipStepNorm α v t) ^ 2 := by ring
      unfold skipLambda
      dsimp only
      linarith
    · simp only [h_mem, ↓reduceIte, add_zero]
      have hΔ_abs : |skipDelta α v T t| = 4 * α * (skipStepNorm α v t) ^ 2 := h_d.1 h_mem
      have hΔ_sq : (skipDelta α v T t) ^ 2 = 16 * α ^ 2 * (skipStepNorm α v t) ^ 4 := by
        calc (skipDelta α v T t) ^ 2
          _ = |skipDelta α v T t| ^ 2 := (sq_abs _).symm
          _ = (4 * α * (skipStepNorm α v t) ^ 2) ^ 2 := by rw [hΔ_abs]
          _ = 16 * α ^ 2 * (skipStepNorm α v t) ^ 4 := by ring
      have hΔ_le : skipDelta α v T t ≤ 4 * α * (skipStepNorm α v t) ^ 2 :=
        (le_abs_self _).trans (le_of_eq hΔ_abs)
      have hΔ_ge : -(4 * α * (skipStepNorm α v t) ^ 2) ≤ skipDelta α v T t := by
        have := neg_abs_le (skipDelta α v T t)
        rwa [hΔ_abs] at this
      have h_quad : 8 * α ^ 2 * (skipStepNorm α v t) ^ 4 ≤
          skipDelta α v T t * (skipDelta α v T t + 2 * skipXi α v t) := by nlinarith
      have h_r_term : 2 * skipDelta α v T t * rvmSkipLoss α w_star v t ≤
          8 * α * (skipStepNorm α v t) ^ 2 * rvmSkipLoss α w_star v t := by nlinarith
      have h_comb : 2 * skipDelta α v T t * rvmSkipLoss α w_star v t -
            skipDelta α v T t * (skipDelta α v T t + 2 * skipXi α v t) ≤
          (8 * (skipStepNorm α v t) ^ 2) * (α * rvmSkipLoss α w_star v t - α ^ 2 * (skipStepNorm α v t) ^ 2) := by
        linarith
      have h_mul := mul_le_mul_of_nonneg_left h_comb (le_of_lt hγ_pos)
      have h_rhs : skipWeight α v t * ((8 * (skipStepNorm α v t) ^ 2) *
            (α * rvmSkipLoss α w_star v t - α ^ 2 * (skipStepNorm α v t) ^ 2)) =
          α * rvmSkipLoss α w_star v t - α ^ 2 * (skipStepNorm α v t) ^ 2 := by
        calc skipWeight α v t * ((8 * (skipStepNorm α v t) ^ 2) *
              (α * rvmSkipLoss α w_star v t - α ^ 2 * (skipStepNorm α v t) ^ 2))
          _ = (skipWeight α v t * (8 * (skipStepNorm α v t) ^ 2)) *
              (α * rvmSkipLoss α w_star v t - α ^ 2 * (skipStepNorm α v t) ^ 2) := by ring
          _ = 1 * (α * rvmSkipLoss α w_star v t - α ^ 2 * (skipStepNorm α v t) ^ 2) := by rw [hγ_eq]
          _ = α * rvmSkipLoss α w_star v t - α ^ 2 * (skipStepNorm α v t) ^ 2 := by ring
      unfold skipLambda
      dsimp only
      linarith
  · have hs_le : (skipStepNorm α v t) ^ 2 ≤ ((t + 2 : ℝ) ^ 4)⁻¹ := not_lt.mp h_made
    have h_skipped_ind : ∀ (R_hor : ℕ), t < R_hor →
        t ∉ rvmSkipActiveSet α v R_hor ∧ skipStretchEndPoint α v R_hor t = rvmSkipQuery α v (t + 1) := by
      intro R_hor
      induction R_hor with
      | zero => intro ht; omega
      | succ r ih =>
        intro ht
        rcases Nat.lt_succ_iff_lt_or_eq.mp ht with hlt | rfl
        · obtain ⟨ht_not_r, hep_r⟩ := ih hlt
          have h_path_sub : rvmSkipPathActiveSet α v r α ⊆ rvmSkipActiveSet α v r :=
            (h_skip_inv α hα v h_unit r).2
          have ht_not_path : t ∉ rvmSkipPathActiveSet α v r α := fun hp => ht_not_r (h_path_sub hp)
          have ht_not_rev : t ∉ rvmSkipRevokedInRound α v r :=
            fun hrev => ht_not_r (Finset.mem_sdiff.mp hrev).1
          have ht_ne : t ≠ r := ne_of_lt hlt
          have ht_not_succ : t ∉ rvmSkipActiveSet α v (r + 1) := by
            intro h_in
            rcases Finset.mem_insert.mp (h_active_succ_sub α v r h_in) with h_eq | h_p
            · exact ht_ne h_eq
            · exact ht_not_path h_p
          have h_not_le : ¬ (r ≤ t) := not_le.mpr hlt
          have hep_succ : skipStretchEndPoint α v (r + 1) t = rvmSkipQuery α v (t + 1) := by
            conv_lhs => unfold skipStretchEndPoint
            rw [if_neg h_not_le, if_neg ht_not_rev, if_neg ht_not_path, hep_r]
          exact ⟨ht_not_succ, hep_succ⟩
        · have ht_not_succ : t ∉ rvmSkipActiveSet α v (t + 1) := by
            change t ∉ (if (skipStepNorm α v t) ^ 2 > ((t + 2 : ℝ) ^ 4)⁻¹ then
              insert t (rvmSkipPathActiveSet α v t α) else rvmSkipPathActiveSet α v t α)
            rw [if_neg h_made]
            intro hp
            have ht_in_A : t ∈ rvmSkipActiveSet α v t := (h_skip_inv α hα v h_unit t).2 hp
            have ht_lt_t : t < t := ((h_skip_inv α hα v h_unit t).1 t ht_in_A).1
            omega
          have hep_succ : skipStretchEndPoint α v (t + 1) t = rvmSkipQuery α v (t + 1) := by
            unfold skipStretchEndPoint
            rw [if_pos (le_refl t)]
          exact ⟨ht_not_succ, hep_succ⟩
    obtain ⟨ht_not_T, hep_T⟩ := h_skipped_ind T htT
    have hΔ_zero : skipDelta α v T t = 0 := by
      unfold skipDelta
      rw [hep_T, sub_self, zero_dotProduct]
    simp only [ht_not_T, ↓reduceIte, add_zero]
    unfold skipLambda
    dsimp only
    rw [hΔ_zero]
    have h_sq_le : α ^ 2 * (skipStepNorm α v t) ^ 2 ≤ α ^ 2 * ((t + 2 : ℝ) ^ 4)⁻¹ :=
      mul_le_mul_of_nonneg_left hs_le (sq_nonneg α)
    have h_ar_nonneg : 0 ≤ α * rvmSkipLoss α w_star v t := mul_nonneg (le_of_lt hα) hr_nonneg
    linarith

lemma h_surv_sub_path : ∀ {d : ℕ} (α : ℝ) (_hα : 0 < α) (v : ℕ → (Fin d → ℝ))
    (_h_unit : ∀ k, dotProduct (v k) (v k) = 1) (t r : ℕ),
    t < r → (rvmSkipActiveSet α v r).filter (· < t) ⊆ rvmSkipPathActiveSet α v t α := by
  intro d α hα v h_unit t r htr
  induction r with
  | zero => omega
  | succ r ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp htr with hlt | rfl
    · intro i hi
      have hi_mem : i ∈ rvmSkipActiveSet α v (r + 1) := (Finset.mem_filter.mp hi).1
      have hi_lt_t : i < t := (Finset.mem_filter.mp hi).2
      have hi_ne_r : i ≠ r := by omega
      have hi_path_r : i ∈ rvmSkipPathActiveSet α v r α := by
        rcases Finset.mem_insert.mp (h_active_succ_sub α v r hi_mem) with rfl | h_in
        · exact False.elim (hi_ne_r rfl)
        · exact h_in
      have hi_act_r : i ∈ rvmSkipActiveSet α v r := (h_skip_inv α hα v h_unit r).2 hi_path_r
      exact ih hlt (Finset.mem_filter.mpr ⟨hi_act_r, hi_lt_t⟩)
    · intro i hi
      have hi_mem : i ∈ rvmSkipActiveSet α v (t + 1) := (Finset.mem_filter.mp hi).1
      have hi_lt_t : i < t := (Finset.mem_filter.mp hi).2
      have hi_ne_t : i ≠ t := ne_of_lt hi_lt_t
      rcases Finset.mem_insert.mp (h_active_succ_sub α v t hi_mem) with rfl | h_in
      · exact False.elim (hi_ne_t rfl)
      · exact h_in

lemma h_skip_surviving : ∀ {d : ℕ} (α : ℝ) (_hα : 0 < α) (v : ℕ → (Fin d → ℝ))
    (_h_unit : ∀ k, dotProduct (v k) (v k) = 1) (T : ℕ),
    ∑ t ∈ rvmSkipActiveSet α v T, (skipStepNorm α v t) ^ 2 ≤ 9 * (d : ℝ) := by
  intro d α hα v h_unit T
  have hγ_nonneg : ∀ i, 0 ≤ skipWeight α v i := by
    intro i
    unfold skipWeight
    positivity
  have h_path_sub : ∀ r, rvmSkipPathActiveSet α v r α ⊆ rvmSkipActiveSet α v r :=
    fun r => (h_skip_inv α hα v h_unit r).2
  have h_active_sub : ∀ r, rvmSkipActiveSet α v r ⊆ Finset.range r := by
    intro r i hi
    exact Finset.mem_range.mpr (((h_skip_inv α hα v h_unit r).1 i hi).1)
  have h_sherman_morrison : ∀ (S : Finset ℕ) (u : Fin d → ℝ) (hu : dotProduct u u = 1)
      (γ_t : ℝ) (hγ_pos : 0 < γ_t),
      let G := stretchMetric S (skipWeight α v) v
      let s_bar_sq := quadForm (G⁻¹) u
      0 ≤ s_bar_sq ∧
      ((G⁻¹).trace - ((G + γ_t • Matrix.vecMulVec u u)⁻¹).trace ≥
        s_bar_sq * (γ_t * s_bar_sq / (1 + γ_t * s_bar_sq))) := by
    intro S u hu γ_t hγ_pos G s_bar_sq
    have hG_pd : G.PosDef := h_stretch_posDef S (skipWeight α v) (fun i _ => hγ_nonneg i) v
    have hG_det : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG_pd.isUnit
    have hG_tr : G.transpose = G := h_stretch_herm S (skipWeight α v) v
    set M := G⁻¹
    have hM_tr : M.transpose = M := by
      dsimp [M]
      rw [Matrix.transpose_nonsing_inv, hG_tr]
    have hGM_vec : ∀ x : Fin d → ℝ, G *ᵥ (M *ᵥ x) = x := by
      intro x
      dsimp [M]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hG_det, Matrix.one_mulVec]
    set w := M *ᵥ u
    have hGw : G *ᵥ w = u := hGM_vec u
    have hs_bar_eq : s_bar_sq = quadForm G w := by
      dsimp [s_bar_sq]
      unfold quadForm
      change dotProduct u w = dotProduct w (G *ᵥ w)
      rw [← hGw, dotProduct_comm]
    have hs_bar_nonneg : 0 ≤ s_bar_sq := by
      rw [hs_bar_eq, h_quad_stretch]
      have := h_dot_self_nonneg w
      have : 0 ≤ ∑ i ∈ S, skipWeight α v i * (dotProduct w (v i)) ^ 2 :=
        Finset.sum_nonneg (fun i _ => mul_nonneg (hγ_nonneg i) (sq_nonneg _))
      linarith
    have h_denom_pos : 0 < 1 + γ_t * s_bar_sq := by positivity
    have h_denom_ne : 1 + γ_t * s_bar_sq ≠ 0 := ne_of_gt h_denom_pos
    set c := γ_t / (1 + γ_t * s_bar_sq)
    set N := M - c • Matrix.vecMulVec w w
    set G' := G + γ_t • Matrix.vecMulVec u u
    have hG'_pd : G'.PosDef := by
      refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
      · ext j k
        dsimp [G', G]
        simp [stretchMetric, Matrix.one_apply, Matrix.sum_apply,
          Matrix.smul_apply, Matrix.vecMulVec_apply, mul_comm, eq_comm]
      · intro x hx
        rw [star_trivial]
        dsimp [G']
        rw [Matrix.add_mulVec, Matrix.smul_mulVec, h_vecMulVec_mulVec, dotProduct_add,
            dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
        change 0 < quadForm G x + γ_t * (dotProduct u x * dotProduct x u)
        rw [h_quad_stretch, dotProduct_comm u x]
        have := h_dot_pos_of_ne_zero x hx
        have : 0 ≤ ∑ i ∈ S, skipWeight α v i * (dotProduct x (v i)) ^ 2 :=
          Finset.sum_nonneg (fun i _ => mul_nonneg (hγ_nonneg i) (sq_nonneg _))
        have : 0 ≤ γ_t * (dotProduct x u * dotProduct x u) :=
          mul_nonneg (le_of_lt hγ_pos) (mul_self_nonneg _)
        linarith
    have hG'_det : IsUnit G'.det := (Matrix.isUnit_iff_isUnit_det G').mp hG'_pd.isUnit
    have hG'N_vec : ∀ x : Fin d → ℝ, (G' * N) *ᵥ x = x := by
      intro x
      rw [← Matrix.mulVec_mulVec]
      dsimp [N]
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, h_vecMulVec_mulVec]
      dsimp [G']
      rw [Matrix.add_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
          hGM_vec x, hGw, Matrix.smul_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul,
          Matrix.mulVec_smul, h_vecMulVec_mulVec, h_vecMulVec_mulVec]
      have h_sym_ux : dotProduct u (M *ᵥ x) = dotProduct w x := by
        dsimp [w]
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM_tr]
      have h_uw : dotProduct u w = s_bar_sq := rfl
      rw [h_sym_ux, h_uw]
      ext j
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hc_id : 1 - c * s_bar_sq = 1 / (1 + γ_t * s_bar_sq) := by
        dsimp [c]
        field_simp
        ring
      have hc_cancel : -(c * dotProduct w x * u j) +
          γ_t * (dotProduct w x * u j - c * (dotProduct w x * (s_bar_sq * u j))) = 0 := by
        dsimp [c]
        field_simp
        ring
      linarith
    have hG'N_one : G' * N = 1 := by
      ext j k
      have hk := congr_fun (hG'N_vec (Pi.single k 1)) j
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using hk
    have hG'_inv : G'⁻¹ = N := by
      calc G'⁻¹
        _ = G'⁻¹ * 1 := (Matrix.mul_one G'⁻¹).symm
        _ = G'⁻¹ * (G' * N) := by rw [hG'N_one]
        _ = (G'⁻¹ * G') * N := (Matrix.mul_assoc G'⁻¹ G' N).symm
        _ = 1 * N := by rw [Matrix.nonsing_inv_mul G' hG'_det]
        _ = N := Matrix.one_mul N
    have h_tr_vec : (Matrix.vecMulVec w w).trace = dotProduct w w := rfl
    have h_tr_diff : M.trace - (G'⁻¹).trace = c * dotProduct w w := by
      rw [hG'_inv]
      dsimp [N]
      rw [Matrix.trace_sub, Matrix.trace_smul, h_tr_vec, smul_eq_mul]
      ring
    have h_cs : s_bar_sq ^ 2 ≤ dotProduct w w := by
      have h_nonneg := h_dot_self_nonneg (w - s_bar_sq • u)
      have h_exp : dotProduct (w - s_bar_sq • u) (w - s_bar_sq • u) =
          dotProduct w w - s_bar_sq ^ 2 := by
        rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, smul_dotProduct,
            dotProduct_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
            smul_eq_mul, smul_eq_mul, dotProduct_comm w u, hu]
        change dotProduct w w - s_bar_sq * s_bar_sq - (s_bar_sq * s_bar_sq - s_bar_sq * (s_bar_sq * 1)) =
          dotProduct w w - s_bar_sq ^ 2
        ring
      linarith
    have hc_nonneg : 0 ≤ c := by
      dsimp [c]
      positivity
    have h_mul := mul_le_mul_of_nonneg_left h_cs hc_nonneg
    refine ⟨hs_bar_nonneg, ?_⟩
    rw [h_tr_diff]
    calc s_bar_sq * (γ_t * s_bar_sq / (1 + γ_t * s_bar_sq))
      _ = c * s_bar_sq ^ 2 := by dsimp [c]; ring
      _ ≤ c * dotProduct w w := h_mul
  have h_ind : ∀ t ≤ T,
      ∑ i ∈ (rvmSkipActiveSet α v T).filter (· < t), (skipStepNorm α v i) ^ 2 ≤
        9 * ((d : ℝ) - ((skipSurvivingMetric α v T t)⁻¹).trace) := by
    intro t htT
    induction t with
    | zero =>
      have h_empty : (rvmSkipActiveSet α v T).filter (· < 0) = ∅ := by
        ext x
        simp
      have h_tr_one : ((skipSurvivingMetric α v T 0)⁻¹).trace = (d : ℝ) := by
        unfold skipSurvivingMetric stretchMetric
        rw [h_empty, Finset.sum_empty, add_zero, inv_one, Matrix.trace_one, Fintype.card_fin]
      rw [h_empty, Finset.sum_empty, h_tr_one, sub_self, mul_zero]
    | succ t ih =>
      have ht_lt : t < T := htT
      have h_prev := ih (le_of_lt ht_lt)
      by_cases ht_mem : t ∈ rvmSkipActiveSet α v T
      · have h_filt_eq : (rvmSkipActiveSet α v T).filter (· < t + 1) =
            insert t ((rvmSkipActiveSet α v T).filter (· < t)) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · intro ⟨hiA, hi_lt⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi_lt with hlt | h_eq
            · exact Or.inr ⟨hiA, hlt⟩
            · exact Or.inl h_eq
          · rintro (h_eq | ⟨hiA, hlt⟩)
            · subst h_eq
              exact ⟨ht_mem, Nat.lt_succ_self i⟩
            · exact ⟨hiA, Nat.lt_succ_of_lt hlt⟩
        have ht_not_mem_filt : t ∉ (rvmSkipActiveSet α v T).filter (· < t) := by simp
        have h_metric_succ : skipSurvivingMetric α v T (t + 1) =
            skipSurvivingMetric α v T t + (skipWeight α v t) • Matrix.vecMulVec (v t) (v t) := by
          unfold skipSurvivingMetric stretchMetric
          rw [h_filt_eq, Finset.sum_insert ht_not_mem_filt]
          abel
        have hs_pos : 0 < skipStepNorm α v t := h_step_norm_pos α v h_unit t
        have hγ_pos : 0 < skipWeight α v t := by
          unfold skipWeight
          positivity
        have h_sm := h_sherman_morrison ((rvmSkipActiveSet α v T).filter (· < t)) (v t) (h_unit t)
          (skipWeight α v t) hγ_pos
        set G_t := skipSurvivingMetric α v T t
        set s_bar_sq := quadForm (G_t⁻¹) (v t)
        have h_sub_path : (rvmSkipActiveSet α v T).filter (· < t) ⊆ rvmSkipPathActiveSet α v t α :=
          h_surv_sub_path α hα v h_unit t T ht_lt
        have h_path_metric_eq : skipPathMetric α v t α =
            stretchMetric (rvmSkipPathActiveSet α v t α) (skipWeight α v) v := by
          dsimp only [skipPathMetric, stretchMetric]
          congr 1
          refine Finset.sum_congr rfl (fun i hi => ?_)
          have hi_lt : i < t := Finset.mem_range.mp (h_active_sub t (h_path_sub t hi))
          rw [h_state_gamma α v t i hi_lt]
        have hs_sq_eq : (skipStepNorm α v t) ^ 2 =
            quadForm ((stretchMetric (rvmSkipPathActiveSet α v t α) (skipWeight α v) v)⁻¹) (v t) := by
          unfold skipStepNorm matNorm
          rw [h_path_metric_eq]
          have h_nonneg : 0 ≤ quadForm ((stretchMetric (rvmSkipPathActiveSet α v t α) (skipWeight α v) v)⁻¹) (v t) :=
            (h_sherman_morrison (rvmSkipPathActiveSet α v t α) (v t) (h_unit t)
              (skipWeight α v t) hγ_pos).1
          exact Real.sq_sqrt h_nonneg
        have hs_le_sbar : (skipStepNorm α v t) ^ 2 ≤ s_bar_sq := by
          rw [hs_sq_eq]
          exact (h_stretch_inv_mono (rvmSkipPathActiveSet α v t α) ((rvmSkipActiveSet α v T).filter (· < t))
            h_sub_path (skipWeight α v) (fun i _ => hγ_nonneg i) v (v t)).1
        have hγ_sbar : (1 / 8 : ℝ) ≤ skipWeight α v t * s_bar_sq := by
          have hγ_st : skipWeight α v t * (skipStepNorm α v t) ^ 2 = 1 / 8 := by
            unfold skipWeight
            have hs_ne : (skipStepNorm α v t) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hs_pos)
            field_simp
          have h_mul := mul_le_mul_of_nonneg_left hs_le_sbar (le_of_lt hγ_pos)
          linarith
        have h_frac : (1 / 9 : ℝ) ≤ skipWeight α v t * s_bar_sq / (1 + skipWeight α v t * s_bar_sq) := by
          rw [le_div_iff₀ (by linarith)]
          linarith
        have h_drop : (skipStepNorm α v t) ^ 2 / 9 ≤
            (G_t⁻¹).trace - ((skipSurvivingMetric α v T (t + 1))⁻¹).trace := by
          rw [h_metric_succ]
          have h_sm2 : s_bar_sq * (skipWeight α v t * s_bar_sq / (1 + skipWeight α v t * s_bar_sq)) ≤
              (G_t⁻¹).trace - ((G_t + (skipWeight α v t) • Matrix.vecMulVec (v t) (v t))⁻¹).trace := h_sm.2
          have h_step1 : s_bar_sq * (1 / 9 : ℝ) ≤
              s_bar_sq * (skipWeight α v t * s_bar_sq / (1 + skipWeight α v t * s_bar_sq)) :=
            mul_le_mul_of_nonneg_left h_frac h_sm.1
          linarith
        rw [h_filt_eq, Finset.sum_insert ht_not_mem_filt]
        linarith
      · have h_filt_eq : (rvmSkipActiveSet α v T).filter (· < t + 1) =
            (rvmSkipActiveSet α v T).filter (· < t) := by
          ext i
          simp only [Finset.mem_filter]
          refine ⟨fun ⟨hiA, hi_lt⟩ => ⟨hiA, ?_⟩, fun ⟨hiA, hi_lt⟩ => ⟨hiA, Nat.lt_succ_of_lt hi_lt⟩⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi_lt with hlt | rfl
          · exact hlt
          · exact False.elim (ht_mem hiA)
        have h_metric_eq : skipSurvivingMetric α v T (t + 1) = skipSurvivingMetric α v T t := by
          unfold skipSurvivingMetric
          rw [h_filt_eq]
        rw [h_filt_eq, h_metric_eq]
        exact h_prev
  have h_filt_T : (rvmSkipActiveSet α v T).filter (· < T) = rvmSkipActiveSet α v T := by
    ext i
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro hi
    exact Finset.mem_range.mp (h_active_sub T hi)
  have h_first : ∑ t ∈ rvmSkipActiveSet α v T, (skipStepNorm α v t) ^ 2 ≤
      9 * ((d : ℝ) - ((skipSurvivingMetric α v T T)⁻¹).trace) := by
    have := h_ind T (le_refl T)
    rwa [h_filt_T] at this
  have h_tr_nonneg : 0 ≤ ((skipSurvivingMetric α v T T)⁻¹).trace := by
    set G_T := skipSurvivingMetric α v T T
    have hG_pd : G_T.PosDef := h_stretch_posDef _ (skipWeight α v) (fun i _ => hγ_nonneg i) v
    have hG_det : IsUnit G_T.det := (Matrix.isUnit_iff_isUnit_det G_T).mp hG_pd.isUnit
    refine Finset.sum_nonneg (fun j _ => ?_)
    set e_j : Fin d → ℝ := Pi.single j 1
    set w_j := G_T⁻¹ *ᵥ e_j
    have hGw_j : G_T *ᵥ w_j = e_j := by
      dsimp [w_j]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G_T hG_det, Matrix.one_mulVec]
    have h_entry : (G_T⁻¹).diag j = quadForm G_T w_j := by
      have h1 : dotProduct e_j w_j = (G_T⁻¹).diag j := by
        dsimp [e_j, w_j, Matrix.diag]
        simp [dotProduct, Matrix.mulVec, Pi.single_apply]
      unfold quadForm
      rw [← h1, ← hGw_j, dotProduct_comm]
    rw [h_entry]
    dsimp [G_T, skipSurvivingMetric]
    rw [h_quad_stretch]
    have := h_dot_self_nonneg w_j
    have : 0 ≤ ∑ i ∈ (rvmSkipActiveSet α v T).filter (· < T), skipWeight α v i * (dotProduct w_j (v i)) ^ 2 :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hγ_nonneg i) (sq_nonneg _))
    linarith
  linarith

lemma h_telescoping : ∀ T : ℕ,
    ∑ t ∈ Finset.range T, ((t + 2 : ℝ) ^ 4)⁻¹ ≤
      (221 / 2592 : ℝ) - 1 / (8 * ((max T 2 + 1 : ℕ) : ℝ) * ((max T 2 + 2 : ℕ) : ℝ)) := by
  intro T
  induction T with
  | zero => norm_num
  | succ T ih =>
    rcases eq_or_ne T 0 with rfl | hT0
    · norm_num
    · rcases eq_or_ne T 1 with rfl | hT1
      · norm_num [Finset.sum_range_succ]
      · have hT2 : 2 ≤ T := by omega
        have hmax1 : max T 2 = T := max_eq_left hT2
        have hmax2 : max (T + 1) 2 = T + 1 := max_eq_left (by omega)
        rw [Finset.sum_range_succ, hmax2]
        rw [hmax1] at ih
        have hm2 : (2 : ℝ) ≤ (T : ℝ) := Nat.ofNat_le_cast.mpr hT2
        push_cast at ih ⊢
        set m : ℝ := (T : ℝ)
        have h_pos1 : 0 < m + 1 := by linarith
        have h_pos2 : 0 < m + 2 := by linarith
        have h_pos3 : 0 < m + 1 + 2 := by linarith
        have h_step : ((m + 2) ^ 4)⁻¹ ≤
            1 / (8 * (m + 1) * (m + 2)) - 1 / (8 * (m + 1 + 1) * (m + 1 + 2)) := by
          have h_diff : 1 / (8 * (m + 1) * (m + 2)) - 1 / (8 * (m + 1 + 1) * (m + 1 + 2)) - ((m + 2) ^ 4)⁻¹ =
              (2 * (m - 2) * (m + 2) ^ 2 + 8) /
                (8 * (m + 1) * (m + 1 + 2) * (m + 2) ^ 4) := by
            field_simp
            ring
          have h_nonneg : 0 ≤ (2 * (m - 2) * (m + 2) ^ 2 + 8) /
              (8 * (m + 1) * (m + 1 + 2) * (m + 2) ^ 4) := by
            refine div_nonneg ?_ (by positivity)
            have : 0 ≤ m - 2 := by linarith
            positivity
          linarith
        linarith

lemma h_sum_inv_pow4 : ∀ T : ℕ, ∑ t ∈ Finset.range T, ((t + 2 : ℝ) ^ 4)⁻¹ ≤ (9 / 100 : ℝ) := by
  intro T
  have h1 := h_telescoping T
  have h_pos : 0 ≤ 1 / (8 * ((max T 2 + 1 : ℕ) : ℝ) * ((max T 2 + 2 : ℕ) : ℝ)) := by positivity
  linarith

lemma h_det_rank_one : ∀ {d : ℕ} (G : Matrix (Fin d) (Fin d) ℝ) (_hG : IsUnit G.det)
    (u : Fin d → ℝ) (γ : ℝ),
    (G + γ • Matrix.vecMulVec u u).det = G.det * (1 + γ * quadForm (G⁻¹) u) := by
  intro d G hG u γ
  set w := G⁻¹ *ᵥ u
  have hGw : G *ᵥ w = u := by
    dsimp [w]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hG, Matrix.one_mulVec]
  let B : Matrix (Fin d) (Fin 1) ℝ := fun i _ => -γ * w i
  let C : Matrix (Fin 1) (Fin d) ℝ := fun _ j => u j
  have h_gbc : G * (B * C) = -(γ • Matrix.vecMulVec u u) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul, B, C, Fin.sum_univ_one]
    have h_gw_i : ∑ k : Fin d, G i k * w k = u i := congr_fun hGw i
    calc ∑ k : Fin d, G i k * (-γ * w k * u j)
      _ = -γ * ((∑ k : Fin d, G i k * w k) * u j) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => by ring)
      _ = -(γ * (u i * u j)) := by rw [h_gw_i]; ring
  have h_factor : G + γ • Matrix.vecMulVec u u = G * (1 - B * C) := by
    rw [Matrix.mul_sub, Matrix.mul_one, h_gbc, sub_neg_eq_add]
  have h_schur1 : (Matrix.fromBlocks (1 : Matrix (Fin d) (Fin d) ℝ) B C (1 : Matrix (Fin 1) (Fin 1) ℝ)).det =
      (1 - B * C).det := by
    simp
  have h_schur2 : (Matrix.fromBlocks (1 : Matrix (Fin d) (Fin d) ℝ) B C (1 : Matrix (Fin 1) (Fin 1) ℝ)).det =
      (1 - C * B).det := by
    have := Matrix.det_fromBlocks_one₁₁ B C (1 : Matrix (Fin 1) (Fin 1) ℝ)
    simpa using this
  have h_det_1_CB : (1 - C * B).det = 1 + γ * quadForm (G⁻¹) u := by
    rw [Matrix.det_fin_one]
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply, C, B, quadForm, dotProduct, w, ite_true]
    rw [Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => by ring)
  rw [h_factor, Matrix.det_mul, ← h_schur1, h_schur2, h_det_1_CB]

lemma h_det_le_trace_pow : ∀ {d : ℕ} (_hd : 0 < d) (H : Matrix (Fin d) (Fin d) ℝ)
    (_hH_herm : H.IsHermitian) (_hH_pd : H.PosDef),
    H.det ≤ (H.trace / (d : ℝ)) ^ d := by
  intro d hd H hH_herm hH_pd
  let eig := hH_herm.eigenvalues
  have heig_pos : ∀ j : Fin d, 0 < eig j := fun j => hH_pd.eigenvalues_pos j
  have h_det_eq : H.det = ∏ j : Fin d, eig j := by
    have h1 := hH_herm.det_eq_prod_eigenvalues
    simpa [eig] using h1
  have h_tr_eq : H.trace = ∑ j : Fin d, eig j := by
    have h1 := hH_herm.trace_eq_sum_eigenvalues
    simpa [eig] using h1
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have h_tr_pos : 0 < H.trace := by
    rw [h_tr_eq]
    refine Finset.sum_pos (fun j _ => heig_pos j) ?_
    rw [Finset.univ_nonempty_iff]
    exact ⟨⟨0, hd⟩⟩
  set μ := H.trace / (d : ℝ)
  have hμ_pos : 0 < μ := div_pos h_tr_pos hd_pos
  have h_term : ∀ j : Fin d, eig j ≤ μ * Real.exp (eig j / μ - 1) := by
    intro j
    have h_exp := Real.add_one_le_exp (eig j / μ - 1)
    have h_sub : eig j / μ - 1 + 1 = eig j / μ := sub_add_cancel _ _
    rw [h_sub] at h_exp
    have h_mul := mul_le_mul_of_nonneg_left h_exp (le_of_lt hμ_pos)
    have h_lhs : μ * (eig j / μ) = eig j := mul_div_cancel₀ (eig j) (ne_of_gt hμ_pos)
    rwa [h_lhs] at h_mul
  have h_prod : ∏ j : Fin d, eig j ≤ ∏ j : Fin d, (μ * Real.exp (eig j / μ - 1)) :=
    Finset.prod_le_prod (fun j _ => le_of_lt (heig_pos j)) (fun j _ => h_term j)
  have h_prod_rhs : (∏ j : Fin d, (μ * Real.exp (eig j / μ - 1))) = μ ^ d := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← Real.exp_sum]
    have h_sum_zero : (∑ j : Fin d, (eig j / μ - 1)) = 0 := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← h_tr_eq, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      dsimp [μ]
      have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
      have htr_ne : H.trace ≠ 0 := ne_of_gt h_tr_pos
      field_simp
      ring
    rw [h_sum_zero, Real.exp_zero, mul_one]
  rw [h_det_eq, ← h_prod_rhs]
  exact h_prod

end SkipHelpers

open SkipHelpers in
lemma prop_3_3_core :
    ∀ {d : ℕ} (_hd : 0 < d) (R : ℝ) (_hR : 0 < R)
      (w_star : Fin d → ℝ) (_hw : dotProduct w_star w_star ≤ R ^ 2)
      (v : ℕ → (Fin d → ℝ)) (_h_unit : ∀ t, dotProduct (v t) (v t) = 1)
      (α : ℝ),
      α = R / (3 * Real.sqrt (d : ℝ)) →
      (∀ T : ℕ, (∀ t < T, 0 ≤ rvmSkipLoss α w_star v t) →
        rvmSkipRegret α w_star v T ≤ ((51 / 8 : ℝ) + (0.03 : ℝ) / (d : ℝ)) * R * Real.sqrt (d : ℝ) ∧
        ((51 / 8 : ℝ) + (0.03 : ℝ) / (d : ℝ)) * R * Real.sqrt (d : ℝ) <
          (6.41 : ℝ) * R * Real.sqrt (d : ℝ)) ∧
      (∀ t : ℕ,
        (9 / 8 : ℝ) ^ (rvmSkipActiveSet α v t).card ≤ (rvmSkipMetric α v t).det ∧
        (rvmSkipMetric α v t).trace ≤ (d : ℝ) + ((t + 1 : ℝ) ^ 5) / 8 ∧
        ((rvmSkipActiveSet α v t).card : ℝ) ≤
          (d : ℝ) * Real.log (1 + ((t + 1 : ℝ) ^ 5) / (8 * (d : ℝ))) / Real.log (9 / 8 : ℝ)) :=
by
  intro d hd R hR w_star hw v h_unit α hα_eq
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hsqrt_pos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd_pos
  have hα_pos : 0 < α := by rw [hα_eq]; positivity
  have h_sq_sqrt : (Real.sqrt (d : ℝ)) ^ 2 = (d : ℝ) := Real.sq_sqrt (le_of_lt hd_pos)
  have h_d_alpha_sq : (d : ℝ) * α ^ 2 = R ^ 2 / 9 := by
    rw [hα_eq]
    have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
    calc (d : ℝ) * (R / (3 * Real.sqrt (d : ℝ))) ^ 2
      _ = (d : ℝ) * (R ^ 2 / (9 * (Real.sqrt (d : ℝ)) ^ 2)) := by ring
      _ = (d : ℝ) * (R ^ 2 / (9 * (d : ℝ))) := by rw [h_sq_sqrt]
      _ = R ^ 2 / 9 := by field_simp
  have h_alpha_mul : α * (3 * Real.sqrt (d : ℝ)) = R := by
    rw [hα_eq]
    exact div_mul_cancel₀ R (ne_of_gt (by positivity))
  have h_alpha_div_d : α * (3 * Real.sqrt (d : ℝ)) / (d : ℝ) = R / (d : ℝ) := by
    rw [h_alpha_mul]
  constructor
  · intro T hr_nonneg
    have h_ledger := h_skip_ledger α hα_pos w_star v h_unit T
    have h_surv := h_skip_surviving α hα_pos v h_unit T
    have h_term_bound : ∀ t ∈ Finset.range T,
        skipLambda α w_star v T t ≤
          (-α * rvmSkipLoss α w_star v t +
            if t ∈ rvmSkipActiveSet α v T then (9 / 8 : ℝ) * α ^ 2 * (skipStepNorm α v t) ^ 2 else 0) +
          α ^ 2 * ((t + 2 : ℝ) ^ 4)⁻¹ := by
      intro t ht
      exact h_skip_lifetime α hα_pos w_star v h_unit T t (Finset.mem_range.mp ht) (hr_nonneg t (Finset.mem_range.mp ht))
    have h_sum_lambda : ∑ t ∈ Finset.range T, skipLambda α w_star v T t ≤
        -α * rvmSkipRegret α w_star v T + (9 / 8 : ℝ) * R ^ 2 + (9 / 100 : ℝ) * α ^ 2 := by
      have h1 := Finset.sum_le_sum h_term_bound
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h1
      have h_reg_sum : ∑ t ∈ Finset.range T, (-α * rvmSkipLoss α w_star v t) = -α * rvmSkipRegret α w_star v T := by
        unfold rvmSkipRegret
        rw [← Finset.mul_sum]
      have h_ite_sum : ∑ t ∈ Finset.range T,
            (if t ∈ rvmSkipActiveSet α v T then (9 / 8 : ℝ) * α ^ 2 * (skipStepNorm α v t) ^ 2 else 0) ≤
          (9 / 8 : ℝ) * α ^ 2 * ∑ t ∈ rvmSkipActiveSet α v T, (skipStepNorm α v t) ^ 2 := by
        rw [← Finset.sum_filter, Finset.mul_sum]
        have h_sub : (Finset.range T).filter (· ∈ rvmSkipActiveSet α v T) ⊆ rvmSkipActiveSet α v T :=
          fun x hx => (Finset.mem_filter.mp hx).2
        exact Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun x _ _ => by positivity)
      have h_surv_bound : (9 / 8 : ℝ) * α ^ 2 * ∑ t ∈ rvmSkipActiveSet α v T, (skipStepNorm α v t) ^ 2 ≤
          (9 / 8 : ℝ) * R ^ 2 := by
        calc (9 / 8 : ℝ) * α ^ 2 * ∑ t ∈ rvmSkipActiveSet α v T, (skipStepNorm α v t) ^ 2
          _ ≤ (9 / 8 : ℝ) * α ^ 2 * (9 * (d : ℝ)) :=
            mul_le_mul_of_nonneg_left h_surv (by positivity)
          _ = (81 / 8 : ℝ) * ((d : ℝ) * α ^ 2) := by ring
          _ = (81 / 8 : ℝ) * (R ^ 2 / 9) := by rw [h_d_alpha_sq]
          _ = (9 / 8 : ℝ) * R ^ 2 := by ring
      have h_skip_sum : ∑ t ∈ Finset.range T, α ^ 2 * ((t + 2 : ℝ) ^ 4)⁻¹ ≤ (9 / 100 : ℝ) * α ^ 2 := by
        rw [← Finset.mul_sum]
        have := mul_le_mul_of_nonneg_left (h_sum_inv_pow4 T) (sq_nonneg α)
        linarith
      linarith
    have h_dist_nonneg : 0 ≤ dotProduct (rvmSkipQuery α v T - w_star) (rvmSkipQuery α v T - w_star) :=
      h_dot_self_nonneg _
    have h_alpha_reg : α * rvmSkipRegret α w_star v T ≤ (17 / 8 : ℝ) * R ^ 2 + (9 / 100 : ℝ) * α ^ 2 := by
      linarith
    have h_reg_bound : rvmSkipRegret α w_star v T ≤
        ((51 / 8 : ℝ) + (0.03 : ℝ) / (d : ℝ)) * R * Real.sqrt (d : ℝ) := by
      have h_mul := mul_le_mul_of_nonneg_right h_alpha_reg (by positivity : 0 ≤ 3 * Real.sqrt (d : ℝ))
      have h_lhs : α * rvmSkipRegret α w_star v T * (3 * Real.sqrt (d : ℝ)) = R * rvmSkipRegret α w_star v T := by
        calc α * rvmSkipRegret α w_star v T * (3 * Real.sqrt (d : ℝ))
          _ = (α * (3 * Real.sqrt (d : ℝ))) * rvmSkipRegret α w_star v T := by ring
          _ = R * rvmSkipRegret α w_star v T := by rw [h_alpha_mul]
      have h_rhs : ((17 / 8 : ℝ) * R ^ 2 + (9 / 100 : ℝ) * α ^ 2) * (3 * Real.sqrt (d : ℝ)) =
          R * (((51 / 8 : ℝ) + (0.03 : ℝ) / (d : ℝ)) * R * Real.sqrt (d : ℝ)) := by
        have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
        calc ((17 / 8 : ℝ) * R ^ 2 + (9 / 100 : ℝ) * α ^ 2) * (3 * Real.sqrt (d : ℝ))
          _ = (51 / 8 : ℝ) * R ^ 2 * Real.sqrt (d : ℝ) +
              (27 / 100 : ℝ) * ((d : ℝ) * α ^ 2) * Real.sqrt (d : ℝ) / (d : ℝ) := by
            field_simp
            ring
          _ = (51 / 8 : ℝ) * R ^ 2 * Real.sqrt (d : ℝ) +
              (27 / 100 : ℝ) * (R ^ 2 / 9) * Real.sqrt (d : ℝ) / (d : ℝ) := by
            rw [h_d_alpha_sq]
          _ = R * (((51 / 8 : ℝ) + (0.03 : ℝ) / (d : ℝ)) * R * Real.sqrt (d : ℝ)) := by
            field_simp
            ring
      rw [h_lhs, h_rhs] at h_mul
      exact le_of_mul_le_mul_left h_mul hR
    have hd_ge_1 : (1 : ℝ) ≤ (d : ℝ) := Nat.one_le_cast.mpr hd
    have h_div_le : (0.03 : ℝ) / (d : ℝ) ≤ 0.03 := by
      rw [div_le_iff₀ hd_pos]
      linarith
    have h_strict : ((51 / 8 : ℝ) + (0.03 : ℝ) / (d : ℝ)) * R * Real.sqrt (d : ℝ) <
        (6.41 : ℝ) * R * Real.sqrt (d : ℝ) := by
      have h_coeff : (51 / 8 : ℝ) + (0.03 : ℝ) / (d : ℝ) < 6.41 := by linarith
      have h_Rsqrt_pos : 0 < R * Real.sqrt (d : ℝ) := mul_pos hR hsqrt_pos
      calc ((51 / 8 : ℝ) + (0.03 : ℝ) / (d : ℝ)) * R * Real.sqrt (d : ℝ)
        _ = ((51 / 8 : ℝ) + (0.03 : ℝ) / (d : ℝ)) * (R * Real.sqrt (d : ℝ)) := by ring
        _ < 6.41 * (R * Real.sqrt (d : ℝ)) := mul_lt_mul_of_pos_right h_coeff h_Rsqrt_pos
        _ = 6.41 * R * Real.sqrt (d : ℝ) := by ring
    exact ⟨h_reg_bound, h_strict⟩
  · intro t
    have hγ_nonneg : ∀ i, 0 ≤ skipWeight α v i := by
      intro i
      unfold skipWeight
      positivity
    have h_path_sub : ∀ r, rvmSkipPathActiveSet α v r α ⊆ rvmSkipActiveSet α v r :=
      fun r => (h_skip_inv α hα_pos v h_unit r).2
    have h_active_sub : ∀ r, rvmSkipActiveSet α v r ⊆ Finset.range r := by
      intro r i hi
      exact Finset.mem_range.mpr (((h_skip_inv α hα_pos v h_unit r).1 i hi).1)
    have h_det_ind : ∀ r ≤ t,
        (9 / 8 : ℝ) ^ ((rvmSkipActiveSet α v t).filter (· < r)).card ≤
          (skipSurvivingMetric α v t r).det := by
      intro r hrt
      induction r with
      | zero =>
        have h_empty : (rvmSkipActiveSet α v t).filter (· < 0) = ∅ := by
          ext x
          simp
        unfold skipSurvivingMetric stretchMetric
        rw [h_empty, Finset.card_empty, pow_zero, Finset.sum_empty, add_zero, Matrix.det_one]
      | succ r ih =>
        have hr_lt : r < t := hrt
        have h_prev := ih (le_of_lt hr_lt)
        by_cases hr_mem : r ∈ rvmSkipActiveSet α v t
        · have h_filt_eq : (rvmSkipActiveSet α v t).filter (· < r + 1) =
              insert r ((rvmSkipActiveSet α v t).filter (· < r)) := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · intro ⟨hiA, hi_lt⟩
              rcases Nat.lt_succ_iff_lt_or_eq.mp hi_lt with hlt | h_eq
              · exact Or.inr ⟨hiA, hlt⟩
              · exact Or.inl h_eq
            · rintro (h_eq | ⟨hiA, hlt⟩)
              · subst h_eq
                exact ⟨hr_mem, Nat.lt_succ_self i⟩
              · exact ⟨hiA, Nat.lt_succ_of_lt hlt⟩
          have hr_not_mem_filt : r ∉ (rvmSkipActiveSet α v t).filter (· < r) := by simp
          have h_metric_succ : skipSurvivingMetric α v t (r + 1) =
              skipSurvivingMetric α v t r + (skipWeight α v r) • Matrix.vecMulVec (v r) (v r) := by
            unfold skipSurvivingMetric stretchMetric
            rw [h_filt_eq, Finset.sum_insert hr_not_mem_filt]
            abel
          set G_r := skipSurvivingMetric α v t r
          have hG_pd : G_r.PosDef :=
            h_stretch_posDef _ (skipWeight α v) (fun i _ => hγ_nonneg i) v
          have hG_det : IsUnit G_r.det := (Matrix.isUnit_iff_isUnit_det G_r).mp hG_pd.isUnit
          have h_det_step := h_det_rank_one G_r hG_det (v r) (skipWeight α v r)
          have h_sub_path : (rvmSkipActiveSet α v t).filter (· < r) ⊆ rvmSkipPathActiveSet α v r α :=
            h_surv_sub_path α hα_pos v h_unit r t hr_lt
          have h_path_metric_eq : skipPathMetric α v r α =
              stretchMetric (rvmSkipPathActiveSet α v r α) (skipWeight α v) v := by
            dsimp only [skipPathMetric, stretchMetric]
            congr 1
            refine Finset.sum_congr rfl (fun i hi => ?_)
            have hi_lt : i < r := Finset.mem_range.mp (h_active_sub r (h_path_sub r hi))
            rw [h_state_gamma α v r i hi_lt]
          have h_q_nonneg : 0 ≤ quadForm ((stretchMetric (rvmSkipPathActiveSet α v r α) (skipWeight α v) v)⁻¹) (v r) := by
            set H_p := stretchMetric (rvmSkipPathActiveSet α v r α) (skipWeight α v) v
            have hHp_pd : H_p.PosDef := h_stretch_posDef _ (skipWeight α v) (fun i _ => hγ_nonneg i) v
            have hHp_det : IsUnit H_p.det := (Matrix.isUnit_iff_isUnit_det H_p).mp hHp_pd.isUnit
            set w_p := H_p⁻¹ *ᵥ v r
            have hHp_w : H_p *ᵥ w_p = v r := by
              dsimp [w_p]
              rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv H_p hHp_det, Matrix.one_mulVec]
            have h_eq : quadForm (H_p⁻¹) (v r) = quadForm H_p w_p := by
              unfold quadForm
              change dotProduct (v r) w_p = dotProduct w_p (H_p *ᵥ w_p)
              rw [← hHp_w, dotProduct_comm]
            rw [h_eq]
            dsimp [H_p]
            rw [h_quad_stretch]
            have := h_dot_self_nonneg w_p
            have : 0 ≤ ∑ i ∈ rvmSkipPathActiveSet α v r α, skipWeight α v i * (dotProduct w_p (v i)) ^ 2 :=
              Finset.sum_nonneg (fun i _ => mul_nonneg (hγ_nonneg i) (sq_nonneg _))
            linarith
          have hs_sq_eq : (skipStepNorm α v r) ^ 2 =
              quadForm ((stretchMetric (rvmSkipPathActiveSet α v r α) (skipWeight α v) v)⁻¹) (v r) := by
            unfold skipStepNorm matNorm
            rw [h_path_metric_eq]
            exact Real.sq_sqrt h_q_nonneg
          have hs_le_q : (skipStepNorm α v r) ^ 2 ≤ quadForm (G_r⁻¹) (v r) := by
            rw [hs_sq_eq]
            exact (h_stretch_inv_mono (rvmSkipPathActiveSet α v r α) ((rvmSkipActiveSet α v t).filter (· < r))
              h_sub_path (skipWeight α v) (fun i _ => hγ_nonneg i) v (v r)).1
          have hs_pos : 0 < skipStepNorm α v r := h_step_norm_pos α v h_unit r
          have hγ_pos : 0 < skipWeight α v r := by
            unfold skipWeight
            positivity
          have h_factor_ge : (9 / 8 : ℝ) ≤ 1 + skipWeight α v r * quadForm (G_r⁻¹) (v r) := by
            have hγ_st : skipWeight α v r * (skipStepNorm α v r) ^ 2 = 1 / 8 := by
              unfold skipWeight
              have hs_ne : (skipStepNorm α v r) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hs_pos)
              field_simp
            have h_mul := mul_le_mul_of_nonneg_left hs_le_q (le_of_lt hγ_pos)
            linarith
          have h_pow_pos : 0 ≤ (9 / 8 : ℝ) ^ ((rvmSkipActiveSet α v t).filter (· < r)).card := by
            positivity
          have hG_det_nonneg : 0 ≤ G_r.det := le_trans h_pow_pos h_prev
          rw [h_filt_eq, Finset.card_insert_of_notMem hr_not_mem_filt, pow_succ,
              h_metric_succ, h_det_step]
          calc (9 / 8 : ℝ) ^ ((rvmSkipActiveSet α v t).filter (· < r)).card * (9 / 8 : ℝ)
            _ ≤ G_r.det * (9 / 8 : ℝ) := mul_le_mul_of_nonneg_right h_prev (by norm_num)
            _ ≤ G_r.det * (1 + skipWeight α v r * quadForm (G_r⁻¹) (v r)) :=
              mul_le_mul_of_nonneg_left h_factor_ge hG_det_nonneg
        · have h_filt_eq : (rvmSkipActiveSet α v t).filter (· < r + 1) =
              (rvmSkipActiveSet α v t).filter (· < r) := by
            ext i
            simp only [Finset.mem_filter]
            refine ⟨fun ⟨hiA, hi_lt⟩ => ⟨hiA, ?_⟩, fun ⟨hiA, hi_lt⟩ => ⟨hiA, Nat.lt_succ_of_lt hi_lt⟩⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi_lt with hlt | rfl
            · exact hlt
            · exact False.elim (hr_mem hiA)
          have h_metric_eq : skipSurvivingMetric α v t (r + 1) = skipSurvivingMetric α v t r := by
            unfold skipSurvivingMetric
            rw [h_filt_eq]
          rw [h_filt_eq, h_metric_eq]
          exact h_prev
    have h_filt_t : (rvmSkipActiveSet α v t).filter (· < t) = rvmSkipActiveSet α v t := by
      ext i
      simp only [Finset.mem_filter, and_iff_left_iff_imp]
      intro hi
      exact Finset.mem_range.mp (h_active_sub t hi)
    have h_metric_t : skipSurvivingMetric α v t t = rvmSkipMetric α v t := by
      unfold skipSurvivingMetric rvmSkipMetric
      rw [h_filt_t]
      dsimp only [stretchMetric]
      congr 1
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi_lt : i < t := Finset.mem_range.mp (h_active_sub t hi)
      rw [h_state_gamma α v t i hi_lt]
    have h_det_lower : (9 / 8 : ℝ) ^ (rvmSkipActiveSet α v t).card ≤ (rvmSkipMetric α v t).det := by
      have := h_det_ind t (le_refl t)
      rwa [h_filt_t, h_metric_t] at this
    have h_trace_upper : (rvmSkipMetric α v t).trace ≤ (d : ℝ) + ((t + 1 : ℝ) ^ 5) / 8 := by
      rw [← h_metric_t]
      unfold skipSurvivingMetric stretchMetric
      rw [h_filt_t, Matrix.trace_add, Matrix.trace_one, Fintype.card_fin, Matrix.trace_sum]
      have h_tr_term : ∀ i ∈ rvmSkipActiveSet α v t,
          ((skipWeight α v i) • Matrix.vecMulVec (v i) (v i)).trace ≤ ((t + 1 : ℝ) ^ 4) / 8 := by
        intro i hi
        have h_tr_v : (Matrix.vecMulVec (v i) (v i)).trace = 1 := by
          change dotProduct (v i) (v i) = 1
          exact h_unit i
        rw [Matrix.trace_smul, h_tr_v, smul_eq_mul, mul_one]
        obtain ⟨hi_lt, _, hi_thresh⟩ := (h_skip_inv α hα_pos v h_unit t).1 i hi
        have hi_le : (i + 2 : ℝ) ≤ (t + 1 : ℝ) := by
          have : i + 2 ≤ t + 1 := by omega
          exact_mod_cast this
        have h_pow_le : (i + 2 : ℝ) ^ 4 ≤ (t + 1 : ℝ) ^ 4 :=
          pow_le_pow_left₀ (by positivity) hi_le 4
        have h_inv_pos : 0 < ((i + 2 : ℝ) ^ 4)⁻¹ := by positivity
        have hs_sq_pos : 0 < (skipStepNorm α v i) ^ 2 := lt_trans h_inv_pos hi_thresh
        have h_γ_le : skipWeight α v i ≤ ((i + 2 : ℝ) ^ 4) / 8 := by
          unfold skipWeight
          rw [div_le_iff₀ (by positivity)]
          have h_mul := mul_le_mul_of_nonneg_left (le_of_lt hi_thresh) (by positivity : 0 ≤ (i + 2 : ℝ) ^ 4 * 8)
          have h_lhs : (i + 2 : ℝ) ^ 4 * 8 * ((i + 2 : ℝ) ^ 4)⁻¹ = 8 := by
            have : (i + 2 : ℝ) ^ 4 ≠ 0 := by positivity
            field_simp
          linarith
        linarith
      have h_sum_le : ∑ i ∈ rvmSkipActiveSet α v t,
            ((skipWeight α v i) • Matrix.vecMulVec (v i) (v i)).trace ≤
          ∑ _i ∈ Finset.range t, ((t + 1 : ℝ) ^ 4) / 8 := by
        calc ∑ i ∈ rvmSkipActiveSet α v t, ((skipWeight α v i) • Matrix.vecMulVec (v i) (v i)).trace
          _ ≤ ∑ _i ∈ rvmSkipActiveSet α v t, ((t + 1 : ℝ) ^ 4) / 8 :=
            Finset.sum_le_sum h_tr_term
          _ ≤ ∑ _i ∈ Finset.range t, ((t + 1 : ℝ) ^ 4) / 8 :=
            Finset.sum_le_sum_of_subset_of_nonneg (h_active_sub t) (fun _ _ _ => by positivity)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h_sum_le
      have h_t_le : (t : ℝ) * (((t + 1 : ℝ) ^ 4) / 8) ≤ ((t + 1 : ℝ) ^ 5) / 8 := by
        have : (t : ℝ) ≤ (t + 1 : ℝ) := by linarith
        have : (t : ℝ) * (t + 1 : ℝ) ^ 4 ≤ (t + 1 : ℝ) * (t + 1 : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_right this (by positivity)
        linarith
      linarith
    set H_t := rvmSkipMetric α v t
    have hH_herm : H_t.IsHermitian := h_stretch_herm _ _ v
    have hH_pd : H_t.PosDef :=
      h_stretch_posDef _ _ (fun i _ => h_state_gamma_nonneg α v t i) v
    have h_det_amgm : H_t.det ≤ (H_t.trace / (d : ℝ)) ^ d :=
      h_det_le_trace_pow hd H_t hH_herm hH_pd
    have h_tr_div_le : H_t.trace / (d : ℝ) ≤ 1 + ((t + 1 : ℝ) ^ 5) / (8 * (d : ℝ)) := by
      rw [div_le_iff₀ hd_pos]
      have h_rhs : (1 + ((t + 1 : ℝ) ^ 5) / (8 * (d : ℝ))) * (d : ℝ) =
          (d : ℝ) + ((t + 1 : ℝ) ^ 5) / 8 := by
        have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
        field_simp
      linarith
    have h_tr_nonneg : 0 ≤ H_t.trace / (d : ℝ) := by
      have h_det_pos : 0 < (9 / 8 : ℝ) ^ (rvmSkipActiveSet α v t).card := by positivity
      have heig_pos : ∀ j : Fin d, 0 < hH_herm.eigenvalues j := fun j => hH_pd.eigenvalues_pos j
      have h_tr_eq : H_t.trace = ∑ j : Fin d, hH_herm.eigenvalues j := by
        simpa using hH_herm.trace_eq_sum_eigenvalues
      have : 0 ≤ H_t.trace := by
        rw [h_tr_eq]
        exact Finset.sum_nonneg (fun j _ => le_of_lt (heig_pos j))
      exact div_nonneg this (le_of_lt hd_pos)
    have h_pow_chain : (9 / 8 : ℝ) ^ (rvmSkipActiveSet α v t).card ≤
        (1 + ((t + 1 : ℝ) ^ 5) / (8 * (d : ℝ))) ^ d := by
      calc (9 / 8 : ℝ) ^ (rvmSkipActiveSet α v t).card
        _ ≤ H_t.det := h_det_lower
        _ ≤ (H_t.trace / (d : ℝ)) ^ d := h_det_amgm
        _ ≤ (1 + ((t + 1 : ℝ) ^ 5) / (8 * (d : ℝ))) ^ d :=
          pow_le_pow_left₀ h_tr_nonneg h_tr_div_le d
    have h_lhs_pos : 0 < (9 / 8 : ℝ) ^ (rvmSkipActiveSet α v t).card := by positivity
    have h_log_le := Real.log_le_log h_lhs_pos h_pow_chain
    rw [Real.log_pow, Real.log_pow] at h_log_le
    have h_log98_pos : 0 < Real.log (9 / 8 : ℝ) := Real.log_pos (by norm_num)
    refine ⟨h_det_lower, h_trace_upper, ?_⟩
    rwa [le_div_iff₀ h_log98_pos]

open RVMHelpers

lemma lem_2_6 :
    Lemma2_3c_MetricAndDualLengthMonotone →
    Lemma2_3d_RevocationOnBoundary →
    Lemma2_5_OneMove →
    Lemma2_6_StretchLifetime := by
  intro h23c h23d h25 d hd α hα w_star v h_unit T t htT hr_nonneg
  have h_c := h23c hd α hα v h_unit t 0 α (le_refl 0) (le_of_lt hα) (le_refl α)
  have hs_pos : 0 < rvmStepNorm α v t :=
    lt_of_lt_of_le h_c.2.2.2.1 (le_trans h_c.2.2.2.2.1 h_c.2.2.2.2.2.1)
  have hs2_pos : 0 < (rvmStepNorm α v t) ^ 2 := sq_pos_of_pos hs_pos
  have h_d := (h23d hd α hα v h_unit).2 T t htT
  have h_m := h25 hd α hα w_star v h_unit t
  have hξ_nonneg : 0 ≤ rvmXi α v t := h_m.1
  have hξ_le : rvmXi α v t ≤ α * (rvmStepNorm α v t) ^ 2 := h_m.2.1
  have hγ_eq : rvmWeight α v t * (8 * (rvmStepNorm α v t) ^ 2) = 1 := by
    unfold rvmWeight
    exact div_mul_cancel₀ 1 (ne_of_gt (by positivity))
  have hγ_pos : 0 < rvmWeight α v t := by
    unfold rvmWeight
    positivity
  constructor
  · intro h_not_mem
    have hΔ_abs : |rvmDelta α v T t| = 4 * α * (rvmStepNorm α v t) ^ 2 := h_d.1 h_not_mem
    have hΔ_sq : (rvmDelta α v T t) ^ 2 = 16 * α ^ 2 * (rvmStepNorm α v t) ^ 4 := by
      calc (rvmDelta α v T t) ^ 2
        _ = |rvmDelta α v T t| ^ 2 := (sq_abs _).symm
        _ = (4 * α * (rvmStepNorm α v t) ^ 2) ^ 2 := by rw [hΔ_abs]
        _ = 16 * α ^ 2 * (rvmStepNorm α v t) ^ 4 := by ring
    have hΔ_le : rvmDelta α v T t ≤ 4 * α * (rvmStepNorm α v t) ^ 2 :=
      (le_abs_self _).trans (le_of_eq hΔ_abs)
    have hΔ_ge : -(4 * α * (rvmStepNorm α v t) ^ 2) ≤ rvmDelta α v T t := by
      have := neg_abs_le (rvmDelta α v T t)
      rwa [hΔ_abs] at this
    have h_quad : 8 * α ^ 2 * (rvmStepNorm α v t) ^ 4 ≤
        rvmDelta α v T t * (rvmDelta α v T t + 2 * rvmXi α v t) := by
      nlinarith
    have h_r_term : 2 * rvmDelta α v T t * rvmLoss α w_star v t ≤
        8 * α * (rvmStepNorm α v t) ^ 2 * rvmLoss α w_star v t := by
      nlinarith
    have h_comb : 2 * rvmDelta α v T t * rvmLoss α w_star v t -
          rvmDelta α v T t * (rvmDelta α v T t + 2 * rvmXi α v t) ≤
        (8 * (rvmStepNorm α v t) ^ 2) * (α * rvmLoss α w_star v t - α ^ 2 * (rvmStepNorm α v t) ^ 2) := by
      linarith
    have h_mul := mul_le_mul_of_nonneg_left h_comb (le_of_lt hγ_pos)
    have h_rhs : rvmWeight α v t * ((8 * (rvmStepNorm α v t) ^ 2) *
          (α * rvmLoss α w_star v t - α ^ 2 * (rvmStepNorm α v t) ^ 2)) =
        α * rvmLoss α w_star v t - α ^ 2 * (rvmStepNorm α v t) ^ 2 := by
      calc rvmWeight α v t * ((8 * (rvmStepNorm α v t) ^ 2) *
            (α * rvmLoss α w_star v t - α ^ 2 * (rvmStepNorm α v t) ^ 2))
        _ = (rvmWeight α v t * (8 * (rvmStepNorm α v t) ^ 2)) *
            (α * rvmLoss α w_star v t - α ^ 2 * (rvmStepNorm α v t) ^ 2) := by ring
        _ = 1 * (α * rvmLoss α w_star v t - α ^ 2 * (rvmStepNorm α v t) ^ 2) := by rw [hγ_eq]
        _ = α * rvmLoss α w_star v t - α ^ 2 * (rvmStepNorm α v t) ^ 2 := by ring
    unfold rvmLambda
    dsimp only
    linarith
  · intro h_mem
    have hΔ_abs : |rvmDelta α v T t| < 4 * α * (rvmStepNorm α v t) ^ 2 := h_d.2 h_mem
    have hΔ_le : rvmDelta α v T t ≤ 4 * α * (rvmStepNorm α v t) ^ 2 :=
      (le_abs_self _).trans (le_of_lt hΔ_abs)
    have h_sq_nonneg : 0 ≤ (rvmDelta α v T t + rvmXi α v t) ^ 2 := sq_nonneg _
    have h_xi_sq : (rvmXi α v t) ^ 2 ≤ α ^ 2 * (rvmStepNorm α v t) ^ 4 := by
      nlinarith
    have h_quad : -(α ^ 2 * (rvmStepNorm α v t) ^ 4) ≤
        rvmDelta α v T t * (rvmDelta α v T t + 2 * rvmXi α v t) := by
      nlinarith
    have h_r_term : 2 * rvmDelta α v T t * rvmLoss α w_star v t ≤
        8 * α * (rvmStepNorm α v t) ^ 2 * rvmLoss α w_star v t := by
      nlinarith
    have h_comb : 2 * rvmDelta α v T t * rvmLoss α w_star v t -
          rvmDelta α v T t * (rvmDelta α v T t + 2 * rvmXi α v t) ≤
        (8 * (rvmStepNorm α v t) ^ 2) *
          (α * rvmLoss α w_star v t + (1 / 8 : ℝ) * α ^ 2 * (rvmStepNorm α v t) ^ 2) := by
      linarith
    have h_mul := mul_le_mul_of_nonneg_left h_comb (le_of_lt hγ_pos)
    have h_rhs : rvmWeight α v t * ((8 * (rvmStepNorm α v t) ^ 2) *
          (α * rvmLoss α w_star v t + (1 / 8 : ℝ) * α ^ 2 * (rvmStepNorm α v t) ^ 2)) =
        α * rvmLoss α w_star v t + (1 / 8 : ℝ) * α ^ 2 * (rvmStepNorm α v t) ^ 2 := by
      calc rvmWeight α v t * ((8 * (rvmStepNorm α v t) ^ 2) *
            (α * rvmLoss α w_star v t + (1 / 8 : ℝ) * α ^ 2 * (rvmStepNorm α v t) ^ 2))
        _ = (rvmWeight α v t * (8 * (rvmStepNorm α v t) ^ 2)) *
            (α * rvmLoss α w_star v t + (1 / 8 : ℝ) * α ^ 2 * (rvmStepNorm α v t) ^ 2) := by ring
        _ = 1 * (α * rvmLoss α w_star v t + (1 / 8 : ℝ) * α ^ 2 * (rvmStepNorm α v t) ^ 2) := by rw [hγ_eq]
        _ = α * rvmLoss α w_star v t + (1 / 8 : ℝ) * α ^ 2 * (rvmStepNorm α v t) ^ 2 := by ring
    unfold rvmLambda
    dsimp only
    linarith

lemma thm_2_1_core :
    Equation6_Ledger →
    Lemma2_6_StretchLifetime →
    Lemma2_7_SurvivingStretches →
    ∀ {d : ℕ} (_hd : 0 < d) (R : ℝ) (_hR : 0 < R)
      (w_star : Fin d → ℝ) (_hw : dotProduct w_star w_star ≤ R ^ 2)
      (v : ℕ → (Fin d → ℝ)) (_h_unit : ∀ t, dotProduct (v t) (v t) = 1)
      (α : ℝ),
      α = R / (3 * Real.sqrt (d : ℝ)) →
      ∀ T : ℕ, (∀ t < T, 0 ≤ rvmLoss α w_star v t) →
        rvmRegret α w_star v T ≤ (51 / 8 : ℝ) * R * Real.sqrt (d : ℝ) ∧
        (51 / 8 : ℝ) * R * Real.sqrt (d : ℝ) < (6.4 : ℝ) * R * Real.sqrt (d : ℝ) ∧
        dotProduct (rvmQuery α v T - w_star) (rvmQuery α v T - w_star) ≤ (17 / 8 : ℝ) * R ^ 2 := by
  intro h_eq6 h26 h27 d hd R hR w_star hw v h_unit α hα_eq T hr_nonneg
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hsqrt_pos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd_pos
  have hα_pos : 0 < α := by rw [hα_eq]; positivity
  have h_sq_sqrt : (Real.sqrt (d : ℝ)) ^ 2 = (d : ℝ) := Real.sq_sqrt (le_of_lt hd_pos)
  have h_d_alpha_sq : (d : ℝ) * α ^ 2 = R ^ 2 / 9 := by
    rw [hα_eq]
    have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
    calc (d : ℝ) * (R / (3 * Real.sqrt (d : ℝ))) ^ 2
      _ = (d : ℝ) * (R ^ 2 / (9 * (Real.sqrt (d : ℝ)) ^ 2)) := by ring
      _ = (d : ℝ) * (R ^ 2 / (9 * (d : ℝ))) := by rw [h_sq_sqrt]
      _ = R ^ 2 / 9 := by field_simp
  have h_alpha_mul : α * (3 * Real.sqrt (d : ℝ)) = R := by
    rw [hα_eq]
    exact div_mul_cancel₀ R (ne_of_gt (by positivity))
  have h_ledger := h_eq6 hd α hα_pos w_star v h_unit T
  have h_surv := (h27 hd α hα_pos v h_unit T).1.trans (h27 hd α hα_pos v h_unit T).2
  have h_term_bound : ∀ t ∈ Finset.range T,
      rvmLambda α w_star v T t ≤
        -α * rvmLoss α w_star v t +
          if t ∈ rvmActiveSet α v T then (9 / 8 : ℝ) * α ^ 2 * (rvmStepNorm α v t) ^ 2 else 0 := by
    intro t ht
    have htT : t < T := Finset.mem_range.mp ht
    have h_lt := h26 hd α hα_pos w_star v h_unit T t htT (hr_nonneg t htT)
    by_cases h_mem : t ∈ rvmActiveSet α v T
    · simp only [h_mem, ↓reduceIte]
      exact h_lt.2 h_mem
    · simp only [h_mem, ↓reduceIte, add_zero]
      exact h_lt.1 h_mem
  have h_sum_lambda : ∑ t ∈ Finset.range T, rvmLambda α w_star v T t ≤
      -α * rvmRegret α w_star v T + (9 / 8 : ℝ) * R ^ 2 := by
    have h1 := Finset.sum_le_sum h_term_bound
    rw [Finset.sum_add_distrib] at h1
    have h_reg_sum : ∑ t ∈ Finset.range T, (-α * rvmLoss α w_star v t) = -α * rvmRegret α w_star v T := by
      unfold rvmRegret
      rw [← Finset.mul_sum]
    have h_ite_sum : ∑ t ∈ Finset.range T,
          (if t ∈ rvmActiveSet α v T then (9 / 8 : ℝ) * α ^ 2 * (rvmStepNorm α v t) ^ 2 else 0) ≤
        (9 / 8 : ℝ) * α ^ 2 * ∑ t ∈ rvmActiveSet α v T, (rvmStepNorm α v t) ^ 2 := by
      rw [← Finset.sum_filter, Finset.mul_sum]
      have h_sub : (Finset.range T).filter (· ∈ rvmActiveSet α v T) ⊆ rvmActiveSet α v T := by
        intro x hx
        exact (Finset.mem_filter.mp hx).2
      exact Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun x _ _ => by positivity)
    have h_surv_bound : (9 / 8 : ℝ) * α ^ 2 * ∑ t ∈ rvmActiveSet α v T, (rvmStepNorm α v t) ^ 2 ≤
        (9 / 8 : ℝ) * R ^ 2 := by
      calc (9 / 8 : ℝ) * α ^ 2 * ∑ t ∈ rvmActiveSet α v T, (rvmStepNorm α v t) ^ 2
        _ ≤ (9 / 8 : ℝ) * α ^ 2 * (9 * (d : ℝ)) := by
          exact mul_le_mul_of_nonneg_left h_surv (by positivity)
        _ = (81 / 8 : ℝ) * ((d : ℝ) * α ^ 2) := by ring
        _ = (81 / 8 : ℝ) * (R ^ 2 / 9) := by rw [h_d_alpha_sq]
        _ = (9 / 8 : ℝ) * R ^ 2 := by ring
    linarith
  have h_dist_nonneg : 0 ≤ dotProduct (rvmQuery α v T - w_star) (rvmQuery α v T - w_star) :=
    h_dot_self_nonneg _
  have h_reg_nonneg : 0 ≤ rvmRegret α w_star v T := by
    unfold rvmRegret
    exact Finset.sum_nonneg (fun t ht => hr_nonneg t (Finset.mem_range.mp ht))
  have h_alpha_reg : α * rvmRegret α w_star v T ≤ (17 / 8 : ℝ) * R ^ 2 := by
    linarith
  have h_reg_bound : rvmRegret α w_star v T ≤ (51 / 8 : ℝ) * R * Real.sqrt (d : ℝ) := by
    have h_mul := mul_le_mul_of_nonneg_right h_alpha_reg (by positivity : 0 ≤ 3 * Real.sqrt (d : ℝ))
    have h_lhs : α * rvmRegret α w_star v T * (3 * Real.sqrt (d : ℝ)) = R * rvmRegret α w_star v T := by
      calc α * rvmRegret α w_star v T * (3 * Real.sqrt (d : ℝ))
        _ = (α * (3 * Real.sqrt (d : ℝ))) * rvmRegret α w_star v T := by ring
        _ = R * rvmRegret α w_star v T := by rw [h_alpha_mul]
    rw [h_lhs] at h_mul
    nlinarith
  refine ⟨h_reg_bound, ?_, ?_⟩
  · nlinarith
  · nlinarith

lemma oiloGameIndex_zero {d : ℕ} (x x_hat : ℕ → (Fin d → ℝ)) :
    oiloGameIndex x x_hat 0 = 0 := by
  simp [oiloGameIndex]

lemma oiloGameIndex_succ_eq {d : ℕ} (x x_hat : ℕ → (Fin d → ℝ)) (t : ℕ)
    (h : x t = x_hat t) :
    oiloGameIndex x x_hat (t + 1) = oiloGameIndex x x_hat t := by
  classical
  unfold oiloGameIndex
  rw [Finset.range_add_one, Finset.filter_insert, if_neg (not_not.mpr h)]

lemma oiloGameIndex_succ_ne {d : ℕ} (x x_hat : ℕ → (Fin d → ℝ)) (t : ℕ)
    (h : x t ≠ x_hat t) :
    oiloGameIndex x x_hat (t + 1) = oiloGameIndex x x_hat t + 1 := by
  classical
  unfold oiloGameIndex
  have ht : t ∉ (Finset.range t).filter (fun s => x s ≠ x_hat s) := by simp
  rw [Finset.range_add_one, Finset.filter_insert, if_pos h, Finset.card_insert_of_notMem ht]

lemma lem_eq_6 :
    Lemma2_3a_ActiveSlabsContainQuery →
    Lemma2_3b_PiecewiseLinearMove →
    Lemma2_5_OneMove →
    Equation6_Ledger := by
  intro h23a h23b h25 d hd α hα w_star v h_unit T
  have h_path_sub : ∀ r, rvmPathActiveSet α v r α ⊆ rvmActiveSet α v r := by
    intro r i hi
    exact (((h23b hd α hα v h_unit r).2.2.2.1 α ⟨le_of_lt hα, le_refl α⟩ i).mp hi).1
  have h_active_sub : ∀ r, rvmActiveSet α v r ⊆ Finset.range r := by
    intro r i hi
    exact Finset.mem_range.mpr ((h23a hd α hα v h_unit r).1 i hi).1
  have h_sum_subset_ite : ∀ (r : ℕ) (S : Finset ℕ) (f : ℕ → ℝ),
      S ⊆ Finset.range r →
      ∑ i ∈ S, f i = ∑ i ∈ Finset.range r, if i ∈ S then f i else 0 := by
    intro r S f hS
    rw [← Finset.sum_filter]
    have h_eq : (Finset.range r).filter (· ∈ S) = S := by
      ext x
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun hx => ⟨hS hx, hx⟩⟩
    rw [h_eq]
  have h_ind : ∀ r : ℕ,
      dotProduct (rvmQuery α v r - w_star) (rvmQuery α v r - w_star) +
        ∑ t ∈ Finset.range r,
          rvmWeight α v t * (dotProduct (w_star - rvmStretchEndPoint α v r t) (v t)) ^ 2 -
        dotProduct w_star w_star ≤
      ∑ t ∈ Finset.range r,
        (-2 * α * rvmLoss α w_star v t + α ^ 2 * (rvmStepNorm α v t) ^ 2 +
          rvmWeight α v t * (dotProduct (w_star - rvmQuery α v (t + 1)) (v t)) ^ 2) := by
    intro r
    induction r with
    | zero =>
      have hq0 : rvmQuery α v 0 = 0 := rfl
      rw [hq0, Finset.range_zero, Finset.sum_empty, Finset.sum_empty, zero_sub,
          dotProduct_neg, neg_dotProduct, neg_neg, add_zero, sub_self]
    | succ r ih =>
      have h_move := (h25 hd α hα w_star v h_unit r).2.2
      have h_quad_start : quadForm (rvmMetric α v r) (rvmQuery α v r - w_star) =
          dotProduct (rvmQuery α v r - w_star) (rvmQuery α v r - w_star) +
            ∑ i ∈ Finset.range r,
              if i ∈ rvmActiveSet α v r then
                rvmWeight α v i * (dotProduct (w_star - rvmQuery α v r) (v i)) ^ 2
              else 0 := by
        unfold rvmMetric
        rw [h_quad_stretch]
        congr 1
        rw [← h_sum_subset_ite r (rvmActiveSet α v r) _ (h_active_sub r)]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi_lt : i < r := Finset.mem_range.mp (h_active_sub r hi)
        rw [h_state_gamma α v r i hi_lt]
        have h_sub_sq : (dotProduct (rvmQuery α v r - w_star) (v i)) ^ 2 =
            (dotProduct (w_star - rvmQuery α v r) (v i)) ^ 2 := by
          rw [sub_dotProduct, sub_dotProduct]
          ring
        rw [h_sub_sq]
      have h_quad_end : quadForm (rvmPathMetric α v r α) (rvmQuery α v (r + 1) - w_star) =
          dotProduct (rvmQuery α v (r + 1) - w_star) (rvmQuery α v (r + 1) - w_star) +
            ∑ i ∈ Finset.range r,
              if i ∈ rvmPathActiveSet α v r α then
                rvmWeight α v i * (dotProduct (w_star - rvmQuery α v (r + 1)) (v i)) ^ 2
              else 0 := by
        unfold rvmPathMetric
        rw [h_quad_stretch]
        congr 1
        have h_sub_r : rvmPathActiveSet α v r α ⊆ Finset.range r :=
          (h_path_sub r).trans (h_active_sub r)
        rw [← h_sum_subset_ite r (rvmPathActiveSet α v r α) _ h_sub_r]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi_lt : i < r := Finset.mem_range.mp (h_sub_r hi)
        rw [h_state_gamma α v r i hi_lt]
        have h_sub_sq : (dotProduct (rvmQuery α v (r + 1) - w_star) (v i)) ^ 2 =
            (dotProduct (w_star - rvmQuery α v (r + 1)) (v i)) ^ 2 := by
          rw [sub_dotProduct, sub_dotProduct]
          ring
        rw [h_sub_sq]
      have h_rev_sub : rvmRevokedInRound α v r ⊆ Finset.range r := by
        intro i hi
        exact h_active_sub r (Finset.mem_sdiff.mp hi).1
      have h_rev_sum : ∑ i ∈ rvmRevokedInRound α v r,
            rvmWeight α v i * (dotProduct (w_star - rvmRoundRevokePoint α v r i) (v i)) ^ 2 =
          ∑ i ∈ Finset.range r,
            if i ∈ rvmRevokedInRound α v r then
              rvmWeight α v i * (dotProduct (w_star - rvmRoundRevokePoint α v r i) (v i)) ^ 2
            else 0 :=
        h_sum_subset_ite r (rvmRevokedInRound α v r) _ h_rev_sub
      have h_pointwise : ∀ i ∈ Finset.range r,
          rvmWeight α v i * (dotProduct (w_star - rvmStretchEndPoint α v (r + 1) i) (v i)) ^ 2 -
            rvmWeight α v i * (dotProduct (w_star - rvmStretchEndPoint α v r i) (v i)) ^ 2 =
          (if i ∈ rvmPathActiveSet α v r α then
            rvmWeight α v i * (dotProduct (w_star - rvmQuery α v (r + 1)) (v i)) ^ 2
          else 0) +
          (if i ∈ rvmRevokedInRound α v r then
            rvmWeight α v i * (dotProduct (w_star - rvmRoundRevokePoint α v r i) (v i)) ^ 2
          else 0) -
          (if i ∈ rvmActiveSet α v r then
            rvmWeight α v i * (dotProduct (w_star - rvmQuery α v r) (v i)) ^ 2
          else 0) := by
        intro i hi
        have hi_lt : i < r := Finset.mem_range.mp hi
        have h_not_le : ¬ (r ≤ i) := not_le.mpr hi_lt
        by_cases hA : i ∈ rvmActiveSet α v r
        · have h_end_r : rvmStretchEndPoint α v r i = rvmQuery α v r := h_endPoint_active α v r i hA
          by_cases hP : i ∈ rvmPathActiveSet α v r α
          · have h_not_rev : i ∉ rvmRevokedInRound α v r := by
              unfold rvmRevokedInRound
              intro h_rev
              exact (Finset.mem_sdiff.mp h_rev).2 hP
            have h_end_succ : rvmStretchEndPoint α v (r + 1) i = rvmQuery α v (r + 1) := by
              rw [rvmStretchEndPoint]
              simp [h_not_le, h_not_rev, hP]
            simp [hA, hP, h_not_rev, h_end_r, h_end_succ]
          · have h_rev : i ∈ rvmRevokedInRound α v r := Finset.mem_sdiff.mpr ⟨hA, hP⟩
            have h_end_succ : rvmStretchEndPoint α v (r + 1) i = rvmRoundRevokePoint α v r i := by
              rw [rvmStretchEndPoint]
              simp [h_not_le, h_rev]
            simp [hA, hP, h_rev, h_end_r, h_end_succ]
        · have hP : i ∉ rvmPathActiveSet α v r α := fun hp => hA (h_path_sub r hp)
          have h_not_rev : i ∉ rvmRevokedInRound α v r := fun h_rev => hA (Finset.mem_sdiff.mp h_rev).1
          have h_end_succ : rvmStretchEndPoint α v (r + 1) i = rvmStretchEndPoint α v r i := by
            rw [rvmStretchEndPoint]
            simp [h_not_le, h_not_rev, hP]
          simp [hA, hP, h_not_rev, h_end_succ]
      have h_sum_diff : ∑ i ∈ Finset.range r,
            rvmWeight α v i * (dotProduct (w_star - rvmStretchEndPoint α v (r + 1) i) (v i)) ^ 2 -
          ∑ i ∈ Finset.range r,
            rvmWeight α v i * (dotProduct (w_star - rvmStretchEndPoint α v r i) (v i)) ^ 2 =
        ∑ i ∈ Finset.range r,
            (if i ∈ rvmPathActiveSet α v r α then
              rvmWeight α v i * (dotProduct (w_star - rvmQuery α v (r + 1)) (v i)) ^ 2
            else 0) +
          ∑ i ∈ Finset.range r,
            (if i ∈ rvmRevokedInRound α v r then
              rvmWeight α v i * (dotProduct (w_star - rvmRoundRevokePoint α v r i) (v i)) ^ 2
            else 0) -
          ∑ i ∈ Finset.range r,
            (if i ∈ rvmActiveSet α v r then
              rvmWeight α v i * (dotProduct (w_star - rvmQuery α v r) (v i)) ^ 2
            else 0) := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl h_pointwise
      have h_end_self : rvmStretchEndPoint α v (r + 1) r = rvmQuery α v (r + 1) := by
        rw [rvmStretchEndPoint]
        simp
      rw [Finset.sum_range_succ, Finset.sum_range_succ, h_end_self]
      linarith
  have h_lambda_id : ∀ t ∈ Finset.range T,
      rvmLambda α w_star v T t =
        (-2 * α * rvmLoss α w_star v t + α ^ 2 * (rvmStepNorm α v t) ^ 2 +
          rvmWeight α v t * (dotProduct (w_star - rvmQuery α v (t + 1)) (v t)) ^ 2) -
        rvmWeight α v t * (dotProduct (w_star - rvmStretchEndPoint α v T t) (v t)) ^ 2 := by
    intro t _
    unfold rvmLambda rvmLoss rvmXi rvmDelta
    dsimp only
    have h1 : dotProduct (w_star - rvmQuery α v (t + 1)) (v t) =
        dotProduct (w_star - rvmQuery α v t) (v t) -
          dotProduct (rvmQuery α v (t + 1) - rvmQuery α v t) (v t) := by
      rw [sub_dotProduct, sub_dotProduct, sub_dotProduct]
      ring
    have h2 : dotProduct (w_star - rvmStretchEndPoint α v T t) (v t) =
        dotProduct (w_star - rvmQuery α v (t + 1)) (v t) -
          dotProduct (rvmStretchEndPoint α v T t - rvmQuery α v (t + 1)) (v t) := by
      rw [sub_dotProduct, sub_dotProduct, sub_dotProduct]
      ring
    rw [h2, h1]
    ring
  have h_sum_lambda : ∑ t ∈ Finset.range T, rvmLambda α w_star v T t =
      ∑ t ∈ Finset.range T,
        (-2 * α * rvmLoss α w_star v t + α ^ 2 * (rvmStepNorm α v t) ^ 2 +
          rvmWeight α v t * (dotProduct (w_star - rvmQuery α v (t + 1)) (v t)) ^ 2) -
      ∑ t ∈ Finset.range T,
        rvmWeight α v t * (dotProduct (w_star - rvmStretchEndPoint α v T t) (v t)) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl h_lambda_id
  have h_nonneg_rem : 0 ≤ ∑ t ∈ Finset.range T,
      rvmWeight α v t * (dotProduct (w_star - rvmStretchEndPoint α v T t) (v t)) ^ 2 := by
    refine Finset.sum_nonneg (fun t _ => ?_)
    unfold rvmWeight
    positivity
  linarith [h_ind T]

lemma lem_2_3c :
    Lemma2_3b_PiecewiseLinearMove →
    Lemma2_3c_MetricAndDualLengthMonotone := by
  intro h23b d hd α hα v h_unit t η₁ η₂ h01 h12 h2α
  have h_b := (h23b hd α hα v h_unit t).2.2.2.1
  have h_sub12 : rvmPathActiveSet α v t η₂ ⊆ rvmPathActiveSet α v t η₁ := by
    intro i hi
    have hi2 := (h_b η₂ ⟨le_trans h01 h12, h2α⟩ i).mp hi
    refine (h_b η₁ ⟨h01, le_trans h12 h2α⟩ i).mpr ⟨hi2.1, ?_⟩
    intro τ hτ
    exact hi2.2 τ ⟨hτ.1, le_trans hτ.2 h12⟩
  have h_sub2α : rvmPathActiveSet α v t α ⊆ rvmPathActiveSet α v t η₂ := by
    intro i hi
    have hiα := (h_b α ⟨le_of_lt hα, le_refl α⟩ i).mp hi
    refine (h_b η₂ ⟨le_trans h01 h12, h2α⟩ i).mpr ⟨hiα.1, ?_⟩
    intro τ hτ
    exact hiα.2 τ ⟨hτ.1, le_trans hτ.2 h2α⟩
  have hγ : ∀ i, 0 ≤ (rvmState α v t).γ i := h_state_gamma_nonneg α v t
  have h_pd1 : (rvmPathMetric α v t η₁).PosDef :=
    h_stretch_posDef _ _ (fun i _ => hγ i) v
  have h_psd12 : (rvmPathMetric α v t η₁ - rvmPathMetric α v t η₂).PosSemidef :=
    h_stretch_sdiff_posSemidef _ _ h_sub12 _ (fun i _ => hγ i) v
  have h_dl12 : rvmDualLength α v t η₁ ≤ rvmDualLength α v t η₂ :=
    (h_stretch_inv_mono _ _ h_sub12 _ (fun i _ => hγ i) v (v t)).2
  have h_dl2α : rvmDualLength α v t η₂ ≤ rvmStepNorm α v t :=
    (h_stretch_inv_mono _ _ h_sub2α _ (fun i _ => hγ i) v (v t)).2
  have h_sn_le_1 : rvmStepNorm α v t ≤ 1 := by
    have h_le_empty := (h_stretch_inv_mono (rvmPathActiveSet α v t α) ∅ (Finset.empty_subset _)
      (rvmState α v t).γ (fun i _ => hγ i) v (v t)).2
    have h_empty_eq : matNorm ((stretchMetric ∅ (rvmState α v t).γ v)⁻¹) (v t) = 1 := by
      unfold matNorm quadForm stretchMetric
      rw [Finset.sum_empty, add_zero, inv_one, Matrix.one_mulVec, h_unit t, Real.sqrt_one]
    unfold rvmStepNorm rvmDualLength rvmPathMetric
    linarith
  have h_dl1_pos : 0 < rvmDualLength α v t η₁ := by
    set H₁ := rvmPathMetric α v t η₁
    set w := H₁⁻¹ *ᵥ v t
    have hH₁_det : IsUnit H₁.det := (Matrix.isUnit_iff_isUnit_det H₁).mp h_pd1.isUnit
    have hHw : H₁ *ᵥ w = v t := by
      dsimp [w]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv H₁ hH₁_det, Matrix.one_mulVec]
    have hw_ne : w ≠ 0 := by
      intro hw0
      have hv0 : v t = 0 := by rw [← hHw, hw0, Matrix.mulVec_zero]
      have h1 := h_unit t
      rw [hv0, dotProduct_zero] at h1
      norm_num at h1
    have hH₁_tr : H₁.transpose = H₁ := h_stretch_herm _ _ v
    have h_q_eq : quadForm (H₁⁻¹) (v t) = quadForm H₁ w := by
      unfold quadForm
      change dotProduct (v t) w = dotProduct w (H₁ *ᵥ w)
      rw [← hHw, dotProduct_comm]
    have h_qw_pos : 0 < quadForm H₁ w := by
      dsimp [H₁, rvmPathMetric]
      rw [h_quad_stretch]
      have := h_dot_pos_of_ne_zero w hw_ne
      have : 0 ≤ ∑ i ∈ rvmPathActiveSet α v t η₁, (rvmState α v t).γ i * (dotProduct w (v i)) ^ 2 :=
        Finset.sum_nonneg (fun i _ => mul_nonneg (hγ i) (sq_nonneg _))
      linarith
    unfold rvmDualLength matNorm
    exact Real.sqrt_pos.mpr (by linarith)
  exact ⟨h_sub12, h_pd1, h_psd12, h_dl1_pos, h_dl12, h_dl2α, h_sn_le_1⟩

lemma lem_2_7 :
    Lemma2_3a_ActiveSlabsContainQuery →
    Lemma2_3b_PiecewiseLinearMove →
    Lemma2_3c_MetricAndDualLengthMonotone →
    Lemma2_7_SurvivingStretches := by
  intro h23a h23b h23c d hd α hα v h_unit T
  have hγ_nonneg : ∀ i, 0 ≤ rvmWeight α v i := by
    intro i
    unfold rvmWeight
    positivity
  have h_path_sub : ∀ r, rvmPathActiveSet α v r α ⊆ rvmActiveSet α v r := by
    intro r i hi
    exact (((h23b hd α hα v h_unit r).2.2.2.1 α ⟨le_of_lt hα, le_refl α⟩ i).mp hi).1
  have h_active_sub : ∀ r, rvmActiveSet α v r ⊆ Finset.range r := by
    intro r i hi
    exact Finset.mem_range.mpr ((h23a hd α hα v h_unit r).1 i hi).1
  have h_surv_sub_path : ∀ t r, t < r →
      (rvmActiveSet α v r).filter (· < t) ⊆ rvmPathActiveSet α v t α := by
    intro t r htr
    induction r with
    | zero => omega
    | succ r ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp htr with hlt | rfl
      · intro i hi
        have hi_mem : i ∈ rvmActiveSet α v (r + 1) := (Finset.mem_filter.mp hi).1
        have hi_lt_t : i < t := (Finset.mem_filter.mp hi).2
        have hi_ne_r : i ≠ r := by omega
        have hi_path_r : i ∈ rvmPathActiveSet α v r α := by
          rcases Finset.mem_insert.mp hi_mem with rfl | h_in
          · exact False.elim (hi_ne_r rfl)
          · exact h_in
        have hi_act_r : i ∈ rvmActiveSet α v r := h_path_sub r hi_path_r
        exact ih hlt (Finset.mem_filter.mpr ⟨hi_act_r, hi_lt_t⟩)
      · intro i hi
        have hi_mem : i ∈ rvmActiveSet α v (t + 1) := (Finset.mem_filter.mp hi).1
        have hi_lt_t : i < t := (Finset.mem_filter.mp hi).2
        have hi_ne_t : i ≠ t := ne_of_lt hi_lt_t
        rcases Finset.mem_insert.mp hi_mem with rfl | h_in
        · exact False.elim (hi_ne_t rfl)
        · exact h_in
  have h_sherman_morrison : ∀ (S : Finset ℕ) (u : Fin d → ℝ) (hu : dotProduct u u = 1)
      (γ_t : ℝ) (hγ_pos : 0 < γ_t),
      let G := stretchMetric S (rvmWeight α v) v
      let s_bar_sq := quadForm (G⁻¹) u
      0 ≤ s_bar_sq ∧
      ((G⁻¹).trace - ((G + γ_t • Matrix.vecMulVec u u)⁻¹).trace ≥
        s_bar_sq * (γ_t * s_bar_sq / (1 + γ_t * s_bar_sq))) := by
    intro S u hu γ_t hγ_pos G s_bar_sq
    have hG_pd : G.PosDef := h_stretch_posDef S (rvmWeight α v) (fun i _ => hγ_nonneg i) v
    have hG_det : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG_pd.isUnit
    have hG_tr : G.transpose = G := h_stretch_herm S (rvmWeight α v) v
    set M := G⁻¹
    have hM_tr : M.transpose = M := by
      dsimp [M]
      rw [Matrix.transpose_nonsing_inv, hG_tr]
    have hGM_vec : ∀ x : Fin d → ℝ, G *ᵥ (M *ᵥ x) = x := by
      intro x
      dsimp [M]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hG_det, Matrix.one_mulVec]
    set w := M *ᵥ u
    have hGw : G *ᵥ w = u := hGM_vec u
    have hs_bar_eq : s_bar_sq = quadForm G w := by
      dsimp [s_bar_sq]
      unfold quadForm
      change dotProduct u w = dotProduct w (G *ᵥ w)
      rw [← hGw, dotProduct_comm]
    have hs_bar_nonneg : 0 ≤ s_bar_sq := by
      rw [hs_bar_eq, h_quad_stretch]
      have := h_dot_self_nonneg w
      have : 0 ≤ ∑ i ∈ S, rvmWeight α v i * (dotProduct w (v i)) ^ 2 :=
        Finset.sum_nonneg (fun i _ => mul_nonneg (hγ_nonneg i) (sq_nonneg _))
      linarith
    have h_denom_pos : 0 < 1 + γ_t * s_bar_sq := by positivity
    have h_denom_ne : 1 + γ_t * s_bar_sq ≠ 0 := ne_of_gt h_denom_pos
    set c := γ_t / (1 + γ_t * s_bar_sq)
    set N := M - c • Matrix.vecMulVec w w
    set G' := G + γ_t • Matrix.vecMulVec u u
    have hG'_pd : G'.PosDef := by
      refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
      · ext j k
        dsimp [G', G]
        simp [stretchMetric, Matrix.one_apply, Matrix.sum_apply,
          Matrix.smul_apply, Matrix.vecMulVec_apply, mul_comm, eq_comm]
      · intro x hx
        rw [star_trivial]
        dsimp [G']
        rw [Matrix.add_mulVec, Matrix.smul_mulVec, h_vecMulVec_mulVec, dotProduct_add,
            dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
        change 0 < quadForm G x + γ_t * (dotProduct u x * dotProduct x u)
        rw [h_quad_stretch, dotProduct_comm u x]
        have := h_dot_pos_of_ne_zero x hx
        have : 0 ≤ ∑ i ∈ S, rvmWeight α v i * (dotProduct x (v i)) ^ 2 :=
          Finset.sum_nonneg (fun i _ => mul_nonneg (hγ_nonneg i) (sq_nonneg _))
        have : 0 ≤ γ_t * (dotProduct x u * dotProduct x u) :=
          mul_nonneg (le_of_lt hγ_pos) (mul_self_nonneg _)
        linarith
    have hG'_det : IsUnit G'.det := (Matrix.isUnit_iff_isUnit_det G').mp hG'_pd.isUnit
    have hG'N_vec : ∀ x : Fin d → ℝ, (G' * N) *ᵥ x = x := by
      intro x
      rw [← Matrix.mulVec_mulVec]
      dsimp [N]
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, h_vecMulVec_mulVec]
      dsimp [G']
      rw [Matrix.add_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
          hGM_vec x, hGw, Matrix.smul_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul,
          Matrix.mulVec_smul, h_vecMulVec_mulVec, h_vecMulVec_mulVec]
      have h_sym_ux : dotProduct u (M *ᵥ x) = dotProduct w x := by
        dsimp [w]
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM_tr]
      have h_uw : dotProduct u w = s_bar_sq := rfl
      rw [h_sym_ux, h_uw]
      ext j
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hc_id : 1 - c * s_bar_sq = 1 / (1 + γ_t * s_bar_sq) := by
        dsimp [c]
        field_simp
        ring
      have hc_cancel : -(c * dotProduct w x * u j) +
          γ_t * (dotProduct w x * u j - c * (dotProduct w x * (s_bar_sq * u j))) = 0 := by
        dsimp [c]
        field_simp
        ring
      linarith
    have hG'N_one : G' * N = 1 := by
      ext j k
      have hk := congr_fun (hG'N_vec (Pi.single k 1)) j
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using hk
    have hG'_inv : G'⁻¹ = N := by
      calc G'⁻¹
        _ = G'⁻¹ * 1 := (Matrix.mul_one G'⁻¹).symm
        _ = G'⁻¹ * (G' * N) := by rw [hG'N_one]
        _ = (G'⁻¹ * G') * N := (Matrix.mul_assoc G'⁻¹ G' N).symm
        _ = 1 * N := by rw [Matrix.nonsing_inv_mul G' hG'_det]
        _ = N := Matrix.one_mul N
    have h_tr_vec : (Matrix.vecMulVec w w).trace = dotProduct w w := by
      rfl
    have h_tr_diff : M.trace - (G'⁻¹).trace = c * dotProduct w w := by
      rw [hG'_inv]
      dsimp [N]
      rw [Matrix.trace_sub, Matrix.trace_smul, h_tr_vec, smul_eq_mul]
      ring
    have h_cs : s_bar_sq ^ 2 ≤ dotProduct w w := by
      have h_nonneg := h_dot_self_nonneg (w - s_bar_sq • u)
      have h_exp : dotProduct (w - s_bar_sq • u) (w - s_bar_sq • u) =
          dotProduct w w - s_bar_sq ^ 2 := by
        rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, smul_dotProduct,
            dotProduct_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
            smul_eq_mul, smul_eq_mul, dotProduct_comm w u, hu]
        change dotProduct w w - s_bar_sq * s_bar_sq - (s_bar_sq * s_bar_sq - s_bar_sq * (s_bar_sq * 1)) =
          dotProduct w w - s_bar_sq ^ 2
        ring
      linarith
    have hc_nonneg : 0 ≤ c := by
      dsimp [c]
      positivity
    have h_mul := mul_le_mul_of_nonneg_left h_cs hc_nonneg
    refine ⟨hs_bar_nonneg, ?_⟩
    rw [h_tr_diff]
    calc s_bar_sq * (γ_t * s_bar_sq / (1 + γ_t * s_bar_sq))
      _ = c * s_bar_sq ^ 2 := by dsimp [c]; ring
      _ ≤ c * dotProduct w w := h_mul
  have h_ind : ∀ t ≤ T,
      ∑ i ∈ (rvmActiveSet α v T).filter (· < t), (rvmStepNorm α v i) ^ 2 ≤
        9 * ((d : ℝ) - ((rvmSurvivingMetric α v T t)⁻¹).trace) := by
    intro t htT
    induction t with
    | zero =>
      have h_empty : (rvmActiveSet α v T).filter (· < 0) = ∅ := by
        ext x
        simp
      have h_tr_one : ((rvmSurvivingMetric α v T 0)⁻¹).trace = (d : ℝ) := by
        unfold rvmSurvivingMetric stretchMetric
        rw [h_empty, Finset.sum_empty, add_zero, inv_one, Matrix.trace_one, Fintype.card_fin]
      rw [h_empty, Finset.sum_empty, h_tr_one, sub_self, mul_zero]
    | succ t ih =>
      have ht_lt : t < T := htT
      have h_prev := ih (le_of_lt ht_lt)
      by_cases ht_mem : t ∈ rvmActiveSet α v T
      · have h_filt_eq : (rvmActiveSet α v T).filter (· < t + 1) =
            insert t ((rvmActiveSet α v T).filter (· < t)) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · intro ⟨hiA, hi_lt⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi_lt with hlt | h_eq
            · exact Or.inr ⟨hiA, hlt⟩
            · exact Or.inl h_eq
          · rintro (h_eq | ⟨hiA, hlt⟩)
            · subst h_eq
              exact ⟨ht_mem, Nat.lt_succ_self i⟩
            · exact ⟨hiA, Nat.lt_succ_of_lt hlt⟩
        have ht_not_mem_filt : t ∉ (rvmActiveSet α v T).filter (· < t) := by
          simp
        have h_metric_succ : rvmSurvivingMetric α v T (t + 1) =
            rvmSurvivingMetric α v T t + (rvmWeight α v t) • Matrix.vecMulVec (v t) (v t) := by
          unfold rvmSurvivingMetric stretchMetric
          rw [h_filt_eq, Finset.sum_insert ht_not_mem_filt]
          abel
        have h_c := h23c hd α hα v h_unit t 0 α (le_refl 0) (le_of_lt hα) (le_refl α)
        have hs_pos : 0 < rvmStepNorm α v t :=
          lt_of_lt_of_le h_c.2.2.2.1 (le_trans h_c.2.2.2.2.1 h_c.2.2.2.2.2.1)
        have hγ_pos : 0 < rvmWeight α v t := by
          unfold rvmWeight
          positivity
        have h_sm := h_sherman_morrison ((rvmActiveSet α v T).filter (· < t)) (v t) (h_unit t)
          (rvmWeight α v t) hγ_pos
        set G_t := rvmSurvivingMetric α v T t
        set s_bar_sq := quadForm (G_t⁻¹) (v t)
        have h_sub_path : (rvmActiveSet α v T).filter (· < t) ⊆ rvmPathActiveSet α v t α :=
          h_surv_sub_path t T ht_lt
        have h_path_metric_eq : rvmPathMetric α v t α =
            stretchMetric (rvmPathActiveSet α v t α) (rvmWeight α v) v := by
          dsimp only [rvmPathMetric, stretchMetric]
          congr 1
          refine Finset.sum_congr rfl (fun i hi => ?_)
          have hi_lt : i < t := Finset.mem_range.mp (h_active_sub t (h_path_sub t hi))
          rw [h_state_gamma α v t i hi_lt]
        have hs_sq_eq : (rvmStepNorm α v t) ^ 2 =
            quadForm ((stretchMetric (rvmPathActiveSet α v t α) (rvmWeight α v) v)⁻¹) (v t) := by
          unfold rvmStepNorm rvmDualLength matNorm
          rw [h_path_metric_eq]
          have h_nonneg : 0 ≤ quadForm ((stretchMetric (rvmPathActiveSet α v t α) (rvmWeight α v) v)⁻¹) (v t) := by
            have h_sm_self := (h_sherman_morrison (rvmPathActiveSet α v t α) (v t) (h_unit t)
              (rvmWeight α v t) hγ_pos).1
            exact h_sm_self
          exact Real.sq_sqrt h_nonneg
        have hs_le_sbar : (rvmStepNorm α v t) ^ 2 ≤ s_bar_sq := by
          rw [hs_sq_eq]
          exact (h_stretch_inv_mono (rvmPathActiveSet α v t α) ((rvmActiveSet α v T).filter (· < t))
            h_sub_path (rvmWeight α v) (fun i _ => hγ_nonneg i) v (v t)).1
        have hγ_sbar : (1 / 8 : ℝ) ≤ rvmWeight α v t * s_bar_sq := by
          have hγ_st : rvmWeight α v t * (rvmStepNorm α v t) ^ 2 = 1 / 8 := by
            unfold rvmWeight
            have hs_ne : (rvmStepNorm α v t) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hs_pos)
            field_simp
          have h_mul := mul_le_mul_of_nonneg_left hs_le_sbar (le_of_lt hγ_pos)
          linarith
        have h_frac : (1 / 9 : ℝ) ≤ rvmWeight α v t * s_bar_sq / (1 + rvmWeight α v t * s_bar_sq) := by
          rw [le_div_iff₀ (by linarith)]
          linarith
        have h_drop : (rvmStepNorm α v t) ^ 2 / 9 ≤
            (G_t⁻¹).trace - ((rvmSurvivingMetric α v T (t + 1))⁻¹).trace := by
          rw [h_metric_succ]
          have h_sm2 : s_bar_sq * (rvmWeight α v t * s_bar_sq / (1 + rvmWeight α v t * s_bar_sq)) ≤
              (G_t⁻¹).trace - ((G_t + (rvmWeight α v t) • Matrix.vecMulVec (v t) (v t))⁻¹).trace := h_sm.2
          have h_step1 : s_bar_sq * (1 / 9 : ℝ) ≤
              s_bar_sq * (rvmWeight α v t * s_bar_sq / (1 + rvmWeight α v t * s_bar_sq)) :=
            mul_le_mul_of_nonneg_left h_frac h_sm.1
          linarith
        rw [h_filt_eq, Finset.sum_insert ht_not_mem_filt]
        linarith
      · have h_filt_eq : (rvmActiveSet α v T).filter (· < t + 1) =
            (rvmActiveSet α v T).filter (· < t) := by
          ext i
          simp only [Finset.mem_filter]
          refine ⟨fun ⟨hiA, hi_lt⟩ => ⟨hiA, ?_⟩, fun ⟨hiA, hi_lt⟩ => ⟨hiA, Nat.lt_succ_of_lt hi_lt⟩⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi_lt with hlt | rfl
          · exact hlt
          · exact False.elim (ht_mem hiA)
        have h_metric_eq : rvmSurvivingMetric α v T (t + 1) = rvmSurvivingMetric α v T t := by
          unfold rvmSurvivingMetric
          rw [h_filt_eq]
        rw [h_filt_eq, h_metric_eq]
        exact h_prev
  have h_filt_T : (rvmActiveSet α v T).filter (· < T) = rvmActiveSet α v T := by
    ext i
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro hi
    exact Finset.mem_range.mp (h_active_sub T hi)
  have h_first : ∑ t ∈ rvmActiveSet α v T, (rvmStepNorm α v t) ^ 2 ≤
      9 * ((d : ℝ) - ((rvmSurvivingMetric α v T T)⁻¹).trace) := by
    have := h_ind T (le_refl T)
    rwa [h_filt_T] at this
  have h_tr_nonneg : 0 ≤ ((rvmSurvivingMetric α v T T)⁻¹).trace := by
    set G_T := rvmSurvivingMetric α v T T
    have hG_pd : G_T.PosDef := h_stretch_posDef _ (rvmWeight α v) (fun i _ => hγ_nonneg i) v
    have hG_det : IsUnit G_T.det := (Matrix.isUnit_iff_isUnit_det G_T).mp hG_pd.isUnit
    refine Finset.sum_nonneg (fun j _ => ?_)
    set e_j : Fin d → ℝ := Pi.single j 1
    set w_j := G_T⁻¹ *ᵥ e_j
    have hGw_j : G_T *ᵥ w_j = e_j := by
      dsimp [w_j]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G_T hG_det, Matrix.one_mulVec]
    have h_entry : (G_T⁻¹).diag j = quadForm G_T w_j := by
      have h1 : dotProduct e_j w_j = (G_T⁻¹).diag j := by
        dsimp [e_j, w_j, Matrix.diag]
        simp [dotProduct, Matrix.mulVec, Pi.single_apply]
      unfold quadForm
      rw [← h1, ← hGw_j, dotProduct_comm]
    rw [h_entry]
    dsimp [G_T, rvmSurvivingMetric]
    rw [h_quad_stretch]
    have := h_dot_self_nonneg w_j
    have : 0 ≤ ∑ i ∈ (rvmActiveSet α v T).filter (· < T), rvmWeight α v i * (dotProduct w_j (v i)) ^ 2 :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hγ_nonneg i) (sq_nonneg _))
    linarith
  exact ⟨h_first, by linarith⟩

lemma moveEval_snd_sub {d : ℕ} (α : ℝ) (c v : ℕ → (Fin d → ℝ)) (s γ : ℕ → ℝ) (v_t : Fin d → ℝ)
    (n : ℕ) (rem : ℝ) (p : Fin d → ℝ) (A : Finset ℕ) (τ : ℝ) :
    (rvmMoveEval α c v s γ v_t n rem p A τ).2 ⊆ A := by
  induction n generalizing rem p A τ with
  | zero => exact Finset.Subset.refl A
  | succ n ih =>
    dsimp only [rvmMoveEval]
    split_ifs with h1 h2
    · exact Finset.Subset.refl A
    · exact (ih _ _ _ _).trans (Finset.filter_subset _ A)
    · exact Finset.filter_subset _ A

lemma rvmState_A_sub_range {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) :
    (rvmState α v t).A ⊆ Finset.range t := by
  induction t with
  | zero => simp [rvmState]
  | succ t ih =>
    intro i hi
    rw [Finset.range_add_one]
    set st := rvmState α v t
    change i ∈ insert t (rvmMoveEval α st.c v st.s st.γ (v t) (st.A.card + 1) α st.p st.A α).2 at hi
    rcases Finset.mem_insert.mp hi with h_eq | hi_after
    · subst h_eq
      exact Finset.mem_insert_self i _
    · exact Finset.mem_insert_of_mem (ih (moveEval_snd_sub _ _ _ _ _ _ _ _ _ _ _ hi_after))

lemma rvmSkipState_A_sub_range {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) :
    (rvmSkipState α v t).A ⊆ Finset.range t := by
  induction t with
  | zero => simp [rvmSkipState]
  | succ t ih =>
    intro i hi
    rw [Finset.range_add_one]
    set st := rvmSkipState α v t
    set A_after := (rvmMoveEval α st.c v st.s st.γ (v t) (st.A.card + 1) α st.p st.A α).2
    set s_t := matNorm ((stretchMetric A_after st.γ v)⁻¹) (v t)
    change i ∈ (if s_t ^ 2 > ((t + 2 : ℝ) ^ 4)⁻¹ then insert t A_after else A_after) at hi
    split_ifs at hi with h_cond
    · rcases Finset.mem_insert.mp hi with h_eq | hi_after
      · subst h_eq
        exact Finset.mem_insert_self i _
      · exact Finset.mem_insert_of_mem (ih (moveEval_snd_sub _ _ _ _ _ _ _ _ _ _ _ hi_after))
    · exact Finset.mem_insert_of_mem (ih (moveEval_snd_sub _ _ _ _ _ _ _ _ _ _ _ hi))

lemma stretchMetric_congr {d : ℕ} (A : Finset ℕ) (γ : ℕ → ℝ) (v v' : ℕ → (Fin d → ℝ))
    (hv : ∀ i ∈ A, v i = v' i) :
    stretchMetric A γ v = stretchMetric A γ v' := by
  unfold stretchMetric
  congr 1
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [hv i hi]

lemma pieceStepTime_congr {d : ℕ} (α rem : ℝ) (c v v' : ℕ → (Fin d → ℝ)) (s : ℕ → ℝ)
    (A : Finset ℕ) (p u : Fin d → ℝ) (hv : ∀ i ∈ A, v i = v' i) :
    pieceStepTime α rem c v s A p u = pieceStepTime α rem c v' s A p u := by
  unfold pieceStepTime
  refine Finset.fold_congr (fun i hi => ?_)
  unfold pieceExitDelta
  rw [hv i hi]

lemma moveEval_congr {d : ℕ} (α : ℝ) (c v v' : ℕ → (Fin d → ℝ)) (s γ : ℕ → ℝ) (v_t : Fin d → ℝ)
    (n : ℕ) (rem : ℝ) (p : Fin d → ℝ) (A : Finset ℕ) (τ : ℝ)
    (hv : ∀ i ∈ A, v i = v' i) :
    rvmMoveEval α c v s γ v_t n rem p A τ = rvmMoveEval α c v' s γ v_t n rem p A τ := by
  induction n generalizing rem p A τ with
  | zero => rfl
  | succ n ih =>
    have hH : stretchMetric A γ v = stretchMetric A γ v' := stretchMetric_congr A γ v v' hv
    set u := (stretchMetric A γ v)⁻¹ *ᵥ v_t
    have hu : (stretchMetric A γ v')⁻¹ *ᵥ v_t = u := by rw [← hH]
    have hδ : pieceStepTime α rem c v s A p u = pieceStepTime α rem c v' s A p u :=
      pieceStepTime_congr α rem c v v' s A p u hv
    set δ := pieceStepTime α rem c v s A p u
    set p_next := p + δ • u
    have hA_next : A.filter (fun i => inSlab α (c i) (v i) (s i) p_next) =
        A.filter (fun i => inSlab α (c i) (v' i) (s i) p_next) := by
      refine Finset.filter_congr (fun i hi => ?_)
      unfold inSlab
      rw [hv i hi]
    dsimp only [rvmMoveEval]
    simp only [hu, ← hδ]
    split_ifs with h1 h2
    · rfl
    · rw [← hA_next]
      exact ih _ _ _ _ (fun i hi => hv i ((Finset.mem_filter.mp hi).1))
    · change (p_next, A.filter (fun i => inSlab α (c i) (v i) (s i) p_next)) =
        (p_next, A.filter (fun i => inSlab α (c i) (v' i) (s i) p_next))
      rw [hA_next]

lemma rvmState_causal {d : ℕ} (α : ℝ) (v v' : ℕ → (Fin d → ℝ)) (t : ℕ)
    (hv : ∀ s < t, v s = v' s) :
    rvmState α v t = rvmState α v' t ∧
    rvmSkipState α v t = rvmSkipState α v' t := by
  induction t with
  | zero => exact ⟨rfl, rfl⟩
  | succ t ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun s hs => hv s (Nat.lt_succ_of_lt hs))
    have hvt : v t = v' t := hv t (Nat.lt_succ_self t)
    constructor
    · have hvA : ∀ i ∈ (rvmState α v t).A, v i = v' i :=
        fun i hi => hv i (Nat.lt_succ_of_lt (Finset.mem_range.mp (rvmState_A_sub_range α v t hi)))
      have h_ev := moveEval_congr α (rvmState α v t).c v v' (rvmState α v t).s (rvmState α v t).γ
        (v t) ((rvmState α v t).A.card + 1) α (rvmState α v t).p (rvmState α v t).A α hvA
      have hvA_after : ∀ i ∈ (rvmMoveEval α (rvmState α v t).c v' (rvmState α v t).s (rvmState α v t).γ
          (v t) ((rvmState α v t).A.card + 1) α (rvmState α v t).p (rvmState α v t).A α).2, v i = v' i :=
        fun i hi => hvA i (moveEval_snd_sub _ _ _ _ _ _ _ _ _ _ _ hi)
      have hH_after := stretchMetric_congr _ (rvmState α v t).γ v v' hvA_after
      dsimp only [rvmState]
      rw [← ih1, ← hvt, h_ev, hH_after]
    · have hvA : ∀ i ∈ (rvmSkipState α v t).A, v i = v' i :=
        fun i hi => hv i (Nat.lt_succ_of_lt (Finset.mem_range.mp (rvmSkipState_A_sub_range α v t hi)))
      have h_ev := moveEval_congr α (rvmSkipState α v t).c v v' (rvmSkipState α v t).s (rvmSkipState α v t).γ
        (v t) ((rvmSkipState α v t).A.card + 1) α (rvmSkipState α v t).p (rvmSkipState α v t).A α hvA
      have hvA_after : ∀ i ∈ (rvmMoveEval α (rvmSkipState α v t).c v' (rvmSkipState α v t).s (rvmSkipState α v t).γ
          (v t) ((rvmSkipState α v t).A.card + 1) α (rvmSkipState α v t).p (rvmSkipState α v t).A α).2, v i = v' i :=
        fun i hi => hvA i (moveEval_snd_sub _ _ _ _ _ _ _ _ _ _ _ hi)
      have hH_after := stretchMetric_congr _ (rvmSkipState α v t).γ v v' hvA_after
      dsimp only [rvmSkipState]
      rw [← ih2, ← hvt, h_ev, hH_after]

lemma card_sdiff_sum_le (A B : ℕ → Finset ℕ)
    (h0 : (A 0).card = 0)
    (h_sub : ∀ t, B t ⊆ A t)
    (h_succ : ∀ t, (A (t + 1)).card ≤ (B t).card + 1)
    (T : ℕ) :
    (A T).card + ∑ t ∈ Finset.range T, (A t \ B t).card ≤ T := by
  induction T with
  | zero => simp [h0]
  | succ T ih =>
    rw [Finset.sum_range_succ]
    have h_sdiff : (A T \ B T).card + (B T).card = (A T).card :=
      Finset.card_sdiff_add_card_eq_card (h_sub T)
    have h_next := h_succ T
    omega

lemma sherman_morrison_update_and_downdate {d : ℕ}
    (G : Matrix (Fin d) (Fin d) ℝ) (hG_tr : G.transpose = G) (hG_det : IsUnit G.det)
    (u : Fin d → ℝ) (γ_i : ℝ)
    (h_nonneg : 0 ≤ quadForm (G⁻¹) u) (hγ_nonneg : 0 ≤ γ_i)
    (hG'_det : IsUnit (G + γ_i • Matrix.vecMulVec u u).det) :
    let H := G + γ_i • Matrix.vecMulVec u u
    let M := H⁻¹
    let N_inv := G⁻¹
    (H⁻¹ = N_inv - (γ_i / (1 + γ_i * quadForm N_inv u)) • Matrix.vecMulVec (N_inv *ᵥ u) (N_inv *ᵥ u)) ∧
    (1 - γ_i * quadForm M u = 1 / (1 + γ_i * quadForm N_inv u)) ∧
    (0 < 1 - γ_i * quadForm M u) ∧
    (G⁻¹ = M + (γ_i / (1 - γ_i * quadForm M u)) • Matrix.vecMulVec (M *ᵥ u) (M *ᵥ u)) := by
  intro H M N_inv
  have hN_tr : N_inv.transpose = N_inv := by
    dsimp [N_inv]
    rw [Matrix.transpose_nonsing_inv, hG_tr]
  have hGN_vec : ∀ x : Fin d → ℝ, G *ᵥ (N_inv *ᵥ x) = x := by
    intro x
    dsimp [N_inv]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hG_det, Matrix.one_mulVec]
  set w := N_inv *ᵥ u
  have hGw : G *ᵥ w = u := hGN_vec u
  set s_sq := quadForm N_inv u
  have h_denom_pos : 0 < 1 + γ_i * s_sq := by positivity
  have h_denom_ne : 1 + γ_i * s_sq ≠ 0 := ne_of_gt h_denom_pos
  set c := γ_i / (1 + γ_i * s_sq)
  set K := N_inv - c • Matrix.vecMulVec w w
  have hHK_vec : ∀ x : Fin d → ℝ, (H * K) *ᵥ x = x := by
    intro x
    rw [← Matrix.mulVec_mulVec]
    dsimp [K, H]
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, h_vecMulVec_mulVec,
        Matrix.add_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
        hGN_vec x, hGw, Matrix.smul_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul,
        Matrix.mulVec_smul, h_vecMulVec_mulVec, h_vecMulVec_mulVec]
    have h_sym_ux : dotProduct u (N_inv *ᵥ x) = dotProduct w x := by
      dsimp [w]
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hN_tr]
    have h_uw : dotProduct u w = s_sq := rfl
    rw [h_sym_ux, h_uw]
    ext j
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hc_cancel : -(c * dotProduct w x * u j) +
        γ_i * (dotProduct w x * u j - c * (dotProduct w x * (s_sq * u j))) = 0 := by
      dsimp [c]
      field_simp
      ring
    linarith
  have hHK_one : H * K = 1 := by
    ext j k
    have hk := congr_fun (hHK_vec (Pi.single k 1)) j
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using hk
  have hM_eq_K : M = K := by
    dsimp [M]
    calc H⁻¹
      _ = H⁻¹ * 1 := (Matrix.mul_one H⁻¹).symm
      _ = H⁻¹ * (H * K) := by rw [hHK_one]
      _ = (H⁻¹ * H) * K := (Matrix.mul_assoc H⁻¹ H K).symm
      _ = 1 * K := by rw [Matrix.nonsing_inv_mul H hG'_det]
      _ = K := Matrix.one_mul K
  have hMu : M *ᵥ u = (1 / (1 + γ_i * s_sq)) • w := by
    rw [hM_eq_K]
    dsimp [K]
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, h_vecMulVec_mulVec]
    have h_wu : dotProduct w u = s_sq := by
      rw [dotProduct_comm]
      rfl
    rw [h_wu]
    ext j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    dsimp [c]
    field_simp
    ring
  have h_qM : quadForm M u = s_sq / (1 + γ_i * s_sq) := by
    unfold quadForm
    rw [hMu, dotProduct_smul, smul_eq_mul]
    have h_uw : dotProduct u w = s_sq := rfl
    rw [h_uw]
    ring
  have h_denom_id : 1 - γ_i * quadForm M u = 1 / (1 + γ_i * s_sq) := by
    rw [h_qM]
    field_simp
    ring
  have h_one_minus_pos : 0 < 1 - γ_i * quadForm M u := by
    rw [h_denom_id]
    positivity
  have h_downdate : N_inv = M + (γ_i / (1 - γ_i * quadForm M u)) • Matrix.vecMulVec (M *ᵥ u) (M *ᵥ u) := by
    rw [h_denom_id, hMu, hM_eq_K]
    dsimp [K, c]
    ext j k
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  exact ⟨hM_eq_K, h_denom_id, h_one_minus_pos, h_downdate⟩

lemma rem_cost_counts_core :
    ∀ {d : ℕ} (_hd : 0 < d) (α : ℝ) (_hα : 0 < α)
      (v : ℕ → (Fin d → ℝ)) (_h_unit : ∀ k, dotProduct (v k) (v k) = 1),
      (∀ t, (rvmActiveSet α v t).card ≤ t) ∧
      (∀ T, ∑ t ∈ Finset.range T, rvmRevokedCount α v t ≤ T) ∧
      (∀ T, ∑ t ∈ Finset.range T, rvmRoundPieces α v t ≤ 2 * T) ∧
      (∀ t, (rvmSkipActiveSet α v t).card ≤ t ∧
        1 ≤ rvmSkipRoundPieces α v t ∧
        rvmSkipRoundPieces α v t ≤ rvmSkipRevokedCount α v t + 1 ∧
        rvmSkipRevokedCount α v t ≤ (rvmSkipActiveSet α v t).card) ∧
      (∀ T, ∑ t ∈ Finset.range T, rvmSkipRevokedCount α v t ≤ T) ∧
      (∀ T, ∑ t ∈ Finset.range T, rvmSkipRoundPieces α v t ≤ 2 * T) ∧
      (∀ (S : Finset ℕ) (i : ℕ), i ∉ S →
        let γ := rvmWeight α v
        let N := stretchMetric S γ v
        let H := stretchMetric (insert i S) γ v
        let M := H⁻¹
        1 - γ i * quadForm M (v i) = 1 / (1 + γ i * quadForm (N⁻¹) (v i)) ∧
        0 < 1 - γ i * quadForm M (v i) ∧
        N⁻¹ = M + (γ i / (1 - γ i * quadForm M (v i))) • Matrix.vecMulVec (M *ᵥ v i) (M *ᵥ v i)) ∧
      (∀ t,
        let M := (rvmPathMetric α v t α)⁻¹
        let s_t := rvmStepNorm α v t
        let γ_t := rvmWeight α v t
        γ_t / (1 + γ_t * s_t ^ 2) = 1 / (9 * s_t ^ 2) ∧
        (rvmMetric α v (t + 1))⁻¹ =
          M - (1 / (9 * s_t ^ 2)) • Matrix.vecMulVec (M *ᵥ v t) (M *ᵥ v t)) := by
  intro d hd α hα v h_unit
  have h_rvm_card : ∀ t, (rvmActiveSet α v t).card ≤ t := by
    intro t
    have h_sub := rvmState_A_sub_range α v t
    have h_le := Finset.card_le_card h_sub
    simpa using h_le
  have h_rvm_rev_sum : ∀ T, ∑ t ∈ Finset.range T, rvmRevokedCount α v t ≤ T := by
    intro T
    have h_cs := card_sdiff_sum_le (rvmActiveSet α v) (fun t => rvmPathActiveSet α v t α)
      rfl
      (fun t => moveEval_snd_sub _ _ _ _ _ _ _ _ _ _ _)
      (fun t => Finset.card_insert_le t _)
      T
    unfold rvmRevokedCount rvmRevokedInRound
    omega
  have h_rvm_pieces_sum : ∀ T, ∑ t ∈ Finset.range T, rvmRoundPieces α v t ≤ 2 * T := by
    intro T
    have h_le : ∀ t ∈ Finset.range T, rvmRoundPieces α v t ≤ rvmRevokedCount α v t + 1 :=
      fun t _ => (lem_2_3b hd α hα v h_unit t).2.1
    have h_sum_le := Finset.sum_le_sum h_le
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at h_sum_le
    have h_rev := h_rvm_rev_sum T
    omega
  have h_skip_round : ∀ t, (rvmSkipActiveSet α v t).card ≤ t ∧
      1 ≤ rvmSkipRoundPieces α v t ∧
      rvmSkipRoundPieces α v t ≤ rvmSkipRevokedCount α v t + 1 ∧
      rvmSkipRevokedCount α v t ≤ (rvmSkipActiveSet α v t).card := by
    intro t
    have h_sub := rvmSkipState_A_sub_range α v t
    have h_card_le : (rvmSkipActiveSet α v t).card ≤ t := by
      have h_le := Finset.card_le_card h_sub
      simpa using h_le
    set st := rvmSkipState α v t
    have h_inv := (SkipHelpers.h_skip_inv α hα v h_unit t).1
    have hA_in : ∀ i ∈ st.A, inSlab α (st.c i) (v i) (st.s i) st.p := by
      intro i hi
      obtain ⟨hi_lt, hi_slab, _⟩ := h_inv i hi
      unfold skipSlab at hi_slab
      rwa [SkipHelpers.h_state_c α v t i hi_lt, SkipHelpers.h_state_s α v t i hi_lt]
    have h_res := h_move_fuel_ind α (st.A.card + 1) α hα st.c v st.s st.γ (v t) st.p st.A
      (Nat.lt_succ_self _) hA_in
    exact ⟨h_card_le, h_res.2.1, h_res.2.2.1, h_res.2.2.2.1⟩
  have h_skip_rev_sum : ∀ T, ∑ t ∈ Finset.range T, rvmSkipRevokedCount α v t ≤ T := by
    intro T
    have h_succ : ∀ t, (rvmSkipActiveSet α v (t + 1)).card ≤ (rvmSkipPathActiveSet α v t α).card + 1 := by
      intro t
      have h1 := Finset.card_le_card (SkipHelpers.h_active_succ_sub α v t)
      have h2 := Finset.card_insert_le t (rvmSkipPathActiveSet α v t α)
      omega
    have h_cs := card_sdiff_sum_le (rvmSkipActiveSet α v) (fun t => rvmSkipPathActiveSet α v t α)
      rfl
      (fun t => moveEval_snd_sub _ _ _ _ _ _ _ _ _ _ _)
      h_succ
      T
    unfold rvmSkipRevokedCount rvmSkipRevokedInRound
    omega
  have h_skip_pieces_sum : ∀ T, ∑ t ∈ Finset.range T, rvmSkipRoundPieces α v t ≤ 2 * T := by
    intro T
    have h_le : ∀ t ∈ Finset.range T, rvmSkipRoundPieces α v t ≤ rvmSkipRevokedCount α v t + 1 :=
      fun t _ => (h_skip_round t).2.2.1
    have h_sum_le := Finset.sum_le_sum h_le
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at h_sum_le
    have h_rev := h_skip_rev_sum T
    omega
  have hγ_nonneg : ∀ j, 0 ≤ rvmWeight α v j := by
    intro j
    unfold rvmWeight
    positivity
  have h_quad_inv_nonneg : ∀ (S : Finset ℕ) (u : Fin d → ℝ),
      0 ≤ quadForm ((stretchMetric S (rvmWeight α v) v)⁻¹) u := by
    intro S u
    set G := stretchMetric S (rvmWeight α v) v
    have hG_pd : G.PosDef := h_stretch_posDef S (rvmWeight α v) (fun j _ => hγ_nonneg j) v
    have hG_det : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG_pd.isUnit
    set w := G⁻¹ *ᵥ u
    have hGw : G *ᵥ w = u := by
      dsimp [w]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hG_det, Matrix.one_mulVec]
    have h_eq : quadForm (G⁻¹) u = quadForm G w := by
      unfold quadForm
      change dotProduct u w = dotProduct w (G *ᵥ w)
      rw [← hGw, dotProduct_comm]
    rw [h_eq]
    dsimp [G]
    rw [h_quad_stretch]
    have := h_dot_self_nonneg w
    have : 0 ≤ ∑ j ∈ S, rvmWeight α v j * (dotProduct w (v j)) ^ 2 :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (hγ_nonneg j) (sq_nonneg _))
    linarith
  have h_sm_downdate : ∀ (S : Finset ℕ) (i : ℕ), i ∉ S →
      let γ := rvmWeight α v
      let N := stretchMetric S γ v
      let H := stretchMetric (insert i S) γ v
      let M := H⁻¹
      1 - γ i * quadForm M (v i) = 1 / (1 + γ i * quadForm (N⁻¹) (v i)) ∧
      0 < 1 - γ i * quadForm M (v i) ∧
      N⁻¹ = M + (γ i / (1 - γ i * quadForm M (v i))) • Matrix.vecMulVec (M *ᵥ v i) (M *ᵥ v i) := by
    intro S i hi γ N H M
    have hH_eq : H = N + (γ i) • Matrix.vecMulVec (v i) (v i) := by
      dsimp [H, N]
      unfold stretchMetric
      rw [Finset.sum_insert hi]
      abel
    have hN_pd : N.PosDef := h_stretch_posDef S γ (fun j _ => hγ_nonneg j) v
    have hN_det : IsUnit N.det := (Matrix.isUnit_iff_isUnit_det N).mp hN_pd.isUnit
    have hN_tr : N.transpose = N := h_stretch_herm S γ v
    have hH_pd : H.PosDef := h_stretch_posDef (insert i S) γ (fun j _ => hγ_nonneg j) v
    have hH_det : IsUnit (N + (γ i) • Matrix.vecMulVec (v i) (v i)).det := by
      rw [← hH_eq]
      exact (Matrix.isUnit_iff_isUnit_det H).mp hH_pd.isUnit
    have h_sm := sherman_morrison_update_and_downdate N hN_tr hN_det (v i) (γ i)
      (h_quad_inv_nonneg S (v i)) (hγ_nonneg i) hH_det
    have hM_eq : (N + (γ i) • Matrix.vecMulVec (v i) (v i))⁻¹ = M := by
      dsimp [M]
      rw [hH_eq]
    refine ⟨?_, ?_, ?_⟩
    · have h1 := h_sm.2.1
      rwa [hM_eq] at h1
    · have h2 := h_sm.2.2.1
      rwa [hM_eq] at h2
    · have h3 := h_sm.2.2.2
      rwa [hM_eq] at h3
  have h_sm_update : ∀ t,
      let M := (rvmPathMetric α v t α)⁻¹
      let s_t := rvmStepNorm α v t
      let γ_t := rvmWeight α v t
      γ_t / (1 + γ_t * s_t ^ 2) = 1 / (9 * s_t ^ 2) ∧
      (rvmMetric α v (t + 1))⁻¹ =
        M - (1 / (9 * s_t ^ 2)) • Matrix.vecMulVec (M *ᵥ v t) (M *ᵥ v t) := by
    intro t M s_t γ_t
    have h_c := lem_2_3c lem_2_3b hd α hα v h_unit t 0 α (le_refl 0) (le_of_lt hα) (le_refl α)
    have hs_pos : 0 < s_t :=
      lt_of_lt_of_le h_c.2.2.2.1 (le_trans h_c.2.2.2.2.1 h_c.2.2.2.2.2.1)
    have hs_sq_pos : 0 < s_t ^ 2 := sq_pos_of_pos hs_pos
    have h_coeff : γ_t / (1 + γ_t * s_t ^ 2) = 1 / (9 * s_t ^ 2) := by
      dsimp [γ_t]
      unfold rvmWeight
      change (1 / (8 * s_t ^ 2)) / (1 + (1 / (8 * s_t ^ 2)) * s_t ^ 2) = 1 / (9 * s_t ^ 2)
      field_simp
      ring
    set S := rvmPathActiveSet α v t α
    have h_sub_range : S ⊆ Finset.range t :=
      (moveEval_snd_sub _ _ _ _ _ _ _ _ _ _ _).trans (rvmState_A_sub_range α v t)
    have ht_not_mem : t ∉ S := by
      intro htS
      have := Finset.mem_range.mp (h_sub_range htS)
      omega
    have h_path_metric_eq : rvmPathMetric α v t α = stretchMetric S (rvmWeight α v) v := by
      unfold rvmPathMetric stretchMetric
      dsimp only
      congr 1
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi_lt : i < t := Finset.mem_range.mp (h_sub_range hi)
      rw [h_state_gamma α v t i hi_lt]
    have h_next_metric_eq : rvmMetric α v (t + 1) =
        rvmPathMetric α v t α + γ_t • Matrix.vecMulVec (v t) (v t) := by
      have h_ins : rvmMetric α v (t + 1) = stretchMetric (insert t S) (rvmWeight α v) v := by
        unfold rvmMetric stretchMetric
        change (1 : Matrix (Fin d) (Fin d) ℝ) + ∑ i ∈ insert t S,
            ((rvmState α v (t + 1)).γ i) • Matrix.vecMulVec (v i) (v i) =
          1 + ∑ i ∈ insert t S, (rvmWeight α v i) • Matrix.vecMulVec (v i) (v i)
        congr 1
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi_lt : i < t + 1 := by
          rcases Finset.mem_insert.mp hi with h_eq | hiS
          · subst h_eq
            exact Nat.lt_succ_self i
          · exact Nat.lt_succ_of_lt (Finset.mem_range.mp (h_sub_range hiS))
        rw [h_state_gamma α v (t + 1) i hi_lt]
      rw [h_ins, h_path_metric_eq]
      unfold stretchMetric
      rw [Finset.sum_insert ht_not_mem]
      abel
    set G := rvmPathMetric α v t α
    have hG_pd : G.PosDef := by
      rw [h_path_metric_eq]
      exact h_stretch_posDef S (rvmWeight α v) (fun j _ => hγ_nonneg j) v
    have hG_det : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG_pd.isUnit
    have hG_tr : G.transpose = G := by
      rw [h_path_metric_eq]
      exact h_stretch_herm S (rvmWeight α v) v
    have h_q_nonneg : 0 ≤ quadForm M (v t) := by
      change 0 ≤ quadForm (G⁻¹) (v t)
      rw [h_path_metric_eq]
      exact h_quad_inv_nonneg S (v t)
    have hs_sq_eq : quadForm M (v t) = s_t ^ 2 := by
      dsimp [s_t, M]
      unfold rvmStepNorm rvmDualLength matNorm
      exact (Real.sq_sqrt h_q_nonneg).symm
    have hG'_pd : (G + γ_t • Matrix.vecMulVec (v t) (v t)).PosDef := by
      rw [← h_next_metric_eq]
      exact h_stretch_posDef _ _ (fun j _ => h_state_gamma_nonneg α v (t + 1) j) v
    have hG'_det : IsUnit (G + γ_t • Matrix.vecMulVec (v t) (v t)).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp hG'_pd.isUnit
    have h_sm := (sherman_morrison_update_and_downdate G hG_tr hG_det (v t) γ_t
      h_q_nonneg (hγ_nonneg t) hG'_det).1
    refine ⟨h_coeff, ?_⟩
    rw [h_next_metric_eq, h_sm]
    dsimp [M, G] at hs_sq_eq ⊢
    rw [hs_sq_eq, h_coeff]
  exact ⟨h_rvm_card, h_rvm_rev_sum, h_rvm_pieces_sum, h_skip_round,
    h_skip_rev_sum, h_skip_pieces_sum, h_sm_downdate, h_sm_update⟩

/-! ### Incremental Sherman–Morrison Equivalence & Instrumented Scalar-Operation Bounds -/

lemma CostM.foldl_val {α β : Type*} (f : α → β → CostM α) (a : α) (l : List β) :
    (CostM.foldl f a l).val = l.foldl (fun acc x => (f acc x).val) a := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih => exact ih (f a x).val

lemma CostM.foldl_ops_le {α β : Type*} (f : α → β → CostM α) (a : α) (l : List β) (c : ℕ)
    (h : ∀ acc, ∀ x ∈ l, (f acc x).ops ≤ c) :
    (CostM.foldl f a l).ops ≤ l.length * c := by
  induction l generalizing a with
  | nil => simp [CostM.foldl, CostM.pure]
  | cons x xs ih =>
    simp only [CostM.foldl, CostM.bind, List.length_cons, Nat.succ_mul]
    have hx := h a x List.mem_cons_self
    have hxs := ih (f a x).val (fun acc y hy => h acc y (List.mem_cons_of_mem _ hy))
    omega

lemma CostM.foldl_ops_eq {α β : Type*} (f : α → β → CostM α) (a : α) (l : List β) (c : ℕ)
    (h : ∀ acc, ∀ x ∈ l, (f acc x).ops = c) :
    (CostM.foldl f a l).ops = l.length * c := by
  induction l generalizing a with
  | nil => simp [CostM.foldl, CostM.pure]
  | cons x xs ih =>
    simp only [CostM.foldl, CostM.bind, List.length, Nat.succ_mul]
    have hx := h a x List.mem_cons_self
    have hxs := ih (f a x).val (fun acc y hy => h acc y (List.mem_cons_of_mem _ hy))
    omega

lemma foldl_update_of_mem {β γ : Type*} [DecidableEq β] (g : β → γ) (l : List β) (init : β → γ)
    (y : β) :
    l.foldl (fun acc x => Function.update acc x (g x)) init y =
      if y ∈ l then g y else init y := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, List.mem_cons]
    by_cases hxs : y ∈ xs
    · simp [hxs]
    · by_cases hx : y = x
      · subst hx; simp [hxs]
      · simp [hxs, hx]

lemma foldl_filter_update (p : ℕ → Bool) (g : ℕ → ℝ) (l : List ℕ)
    (S₀ : Finset ℕ) (f₀ : ℕ → ℝ) :
    let res := l.foldl (fun (acc : Finset ℕ × (ℕ → ℝ)) i =>
      if p i then (insert i acc.1, Function.update acc.2 i (g i)) else acc) (S₀, f₀)
    (∀ j, j ∈ res.1 ↔ (j ∈ l ∧ p j = true) ∨ j ∈ S₀) ∧
    (∀ j, res.2 j = if j ∈ l ∧ p j = true then g j else f₀ j) := by
  induction l generalizing S₀ f₀ with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.mem_cons]
    by_cases hpx : p x = true
    · simp only [hpx, ↓reduceIte]
      rcases ih (insert x S₀) (Function.update f₀ x (g x)) with ⟨h1, h2⟩
      refine ⟨fun j => ?_, fun j => ?_⟩
      · rw [h1 j, Finset.mem_insert]
        by_cases hjx : j = x
        · subst hjx; simp [hpx]
        · simp [hjx]
      · rw [h2 j]
        by_cases hjx : j = x
        · subst hjx; simp [hpx]
        · simp [hjx]
    · have hpx_f : p x = false := Bool.eq_false_iff.mpr hpx
      simp only [hpx_f, Bool.false_eq_true, ↓reduceIte]
      rcases ih S₀ f₀ with ⟨h1, h2⟩
      refine ⟨fun j => ?_, fun j => ?_⟩
      · rw [h1 j]
        by_cases hjx : j = x
        · subst hjx; simp [hpx]
        · simp [hjx]
      · rw [h2 j]
        by_cases hjx : j = x
        · subst hjx; simp [hpx]
        · simp [hjx]

lemma ramVecAdd_val {d : ℕ} (u w : Fin d → ℝ) : (ramVecAdd u w).val = u + w := by
  ext j
  rw [ramVecAdd, CostM.foldl_val]
  have h := foldl_update_of_mem (fun k : Fin d => u k + w k) (List.finRange d) 0 j
  simpa [CostM.bind, CostM.pure, ramAdd, List.mem_finRange] using h

lemma ramVecAdd_ops {d : ℕ} (u w : Fin d → ℝ) : (ramVecAdd u w).ops = d := by
  rw [ramVecAdd, CostM.foldl_ops_eq _ _ _ 1 (fun _ _ _ => rfl), List.length_finRange, Nat.mul_one]

lemma ramVecSub_val {d : ℕ} (u w : Fin d → ℝ) : (ramVecSub u w).val = u - w := by
  ext j
  rw [ramVecSub, CostM.foldl_val]
  have h := foldl_update_of_mem (fun k : Fin d => u k - w k) (List.finRange d) 0 j
  simpa [CostM.bind, CostM.pure, ramSub, List.mem_finRange] using h

lemma ramVecSub_ops {d : ℕ} (u w : Fin d → ℝ) : (ramVecSub u w).ops = d := by
  rw [ramVecSub, CostM.foldl_ops_eq _ _ _ 1 (fun _ _ _ => rfl), List.length_finRange, Nat.mul_one]

lemma ramVecSmul_val {d : ℕ} (c : ℝ) (u : Fin d → ℝ) : (ramVecSmul c u).val = c • u := by
  ext j
  rw [ramVecSmul, CostM.foldl_val]
  have h := foldl_update_of_mem (fun k : Fin d => c * u k) (List.finRange d) 0 j
  simpa [CostM.bind, CostM.pure, ramMul, List.mem_finRange] using h

lemma ramVecSmul_ops {d : ℕ} (c : ℝ) (u : Fin d → ℝ) : (ramVecSmul c u).ops = d := by
  rw [ramVecSmul, CostM.foldl_ops_eq _ _ _ 1 (fun _ _ _ => rfl), List.length_finRange, Nat.mul_one]

lemma foldl_and_eq_all {β : Type*} (p : β → Bool) (l : List β) (init : Bool) :
    l.foldl (fun acc x => acc && p x) init = (init && l.all p) := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.all_cons, ih, Bool.and_assoc]

lemma ramVecEq_val {d : ℕ} (u w : Fin d → ℝ) :
    (ramVecEq u w).val = true ↔ u = w := by
  rw [ramVecEq, CostM.foldl_val]
  change (List.finRange d).foldl
    (fun acc j => acc && (open Classical in decide (u j = w j))) true = true ↔ u = w
  rw [foldl_and_eq_all, Bool.true_and, List.all_eq_true]
  constructor
  · intro h
    ext j
    have hj := h j (List.mem_finRange j)
    simpa [decide_eq_true_iff] using hj
  · intro h j _
    subst h
    simp

lemma ramVecEq_ops {d : ℕ} (u w : Fin d → ℝ) : (ramVecEq u w).ops = d := by
  rw [ramVecEq, CostM.foldl_ops_eq _ _ _ 1 (fun _ _ _ => rfl), List.length_finRange, Nat.mul_one]

lemma foldl_add_eq_sum {β : Type*} (g : β → ℝ) (l : List β) (init : ℝ) :
    l.foldl (fun acc x => acc + g x) init = init + (l.map g).sum := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
    ring

lemma ramDot_val {d : ℕ} (u w : Fin d → ℝ) : (ramDot u w).val = dotProduct u w := by
  rw [ramDot, CostM.foldl_val]
  change (List.finRange d).foldl (fun acc j => acc + u j * w j) 0 = dotProduct u w
  rw [foldl_add_eq_sum, zero_add]
  simp [dotProduct, Fin.sum_univ_def]

lemma ramDot_ops {d : ℕ} (u w : Fin d → ℝ) : (ramDot u w).ops = 2 * d := by
  rw [ramDot, CostM.foldl_ops_eq _ _ _ 2 (fun _ _ _ => rfl), List.length_finRange]
  ring

lemma ramMatVec_val {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    (ramMatVec M v).val = M *ᵥ v := by
  ext i
  rw [ramMatVec, CostM.foldl_val]
  have h := foldl_update_of_mem (fun k : Fin d => (ramDot (M k) v).val) (List.finRange d) 0 i
  simp only [CostM.bind, CostM.pure] at h ⊢
  rw [h, if_pos (List.mem_finRange i), ramDot_val]
  rfl

lemma ramMatVec_ops {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    (ramMatVec M v).ops = 2 * d ^ 2 := by
  rw [ramMatVec, CostM.foldl_ops_eq _ _ _ (2 * d)]
  · rw [List.length_finRange]; ring
  · intro acc i _
    simp [CostM.bind, CostM.pure, ramDot_ops]

lemma ramRankOneAdd_val {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (w : Fin d → ℝ) :
    (ramRankOneAdd M c w).val = M + c • Matrix.vecMulVec w w := by
  ext i j
  rw [ramRankOneAdd, CostM.foldl_val]
  let rowFn : Fin d → (Fin d → ℝ) := fun r =>
    (CostM.foldl (fun accCol k =>
      CostM.bind (ramRankOneAddEntry M c w r k) (fun v_rk =>
        CostM.pure (Function.update accCol k v_rk))) 0 (List.finRange d)).val
  change (List.finRange d).foldl (fun acc x => Function.update acc x (rowFn x)) M i j =
    (M + c • Matrix.vecMulVec w w) i j
  rw [foldl_update_of_mem rowFn (List.finRange d) M i, if_pos (List.mem_finRange i)]
  dsimp [rowFn]
  rw [CostM.foldl_val]
  change (List.finRange d).foldl
    (fun accCol k => Function.update accCol k (ramRankOneAddEntry M c w i k).val) 0 j =
    (M + c • Matrix.vecMulVec w w) i j
  rw [foldl_update_of_mem (fun k : Fin d => (ramRankOneAddEntry M c w i k).val)
    (List.finRange d) 0 j, if_pos (List.mem_finRange j)]
  simp [ramRankOneAddEntry, CostM.bind, ramMul, ramAdd, Matrix.add_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]

lemma ramRankOneAdd_ops {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (w : Fin d → ℝ) :
    (ramRankOneAdd M c w).ops = 3 * d ^ 2 := by
  rw [ramRankOneAdd, CostM.foldl_ops_eq _ _ _ (3 * d)]
  · rw [List.length_finRange]; ring
  · intro accRow i _
    simp only [CostM.bind, CostM.pure, Nat.add_zero]
    rw [CostM.foldl_ops_eq _ _ _ 3 (fun _ _ _ => rfl), List.length_finRange]
    ring

lemma ramRankOneSub_val {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (w : Fin d → ℝ) :
    (ramRankOneSub M c w).val = M - c • Matrix.vecMulVec w w := by
  ext i j
  rw [ramRankOneSub, CostM.foldl_val]
  let rowFn : Fin d → (Fin d → ℝ) := fun r =>
    (CostM.foldl (fun accCol k =>
      CostM.bind (ramRankOneSubEntry M c w r k) (fun v_rk =>
        CostM.pure (Function.update accCol k v_rk))) 0 (List.finRange d)).val
  change (List.finRange d).foldl (fun acc x => Function.update acc x (rowFn x)) M i j =
    (M - c • Matrix.vecMulVec w w) i j
  rw [foldl_update_of_mem rowFn (List.finRange d) M i, if_pos (List.mem_finRange i)]
  dsimp [rowFn]
  rw [CostM.foldl_val]
  change (List.finRange d).foldl
    (fun accCol k => Function.update accCol k (ramRankOneSubEntry M c w i k).val) 0 j =
    (M - c • Matrix.vecMulVec w w) i j
  rw [foldl_update_of_mem (fun k : Fin d => (ramRankOneSubEntry M c w i k).val)
    (List.finRange d) 0 j, if_pos (List.mem_finRange j)]
  simp [ramRankOneSubEntry, CostM.bind, ramMul, ramSub, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]

lemma ramRankOneSub_ops {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (w : Fin d → ℝ) :
    (ramRankOneSub M c w).ops = 3 * d ^ 2 := by
  rw [ramRankOneSub, CostM.foldl_ops_eq _ _ _ (3 * d)]
  · rw [List.length_finRange]; ring
  · intro accRow i _
    simp only [CostM.bind, CostM.pure, Nat.add_zero]
    rw [CostM.foldl_ops_eq _ _ _ 3 (fun _ _ _ => rfl), List.length_finRange]
    ring

lemma ramFastPieceExitDelta_val (α rem : ℝ) (s_sq φ β : ℕ → ℝ) (i : ℕ) :
    (ramFastPieceExitDelta α rem s_sq φ β i).val = fastPieceExitDelta α rem s_sq φ β i := by
  unfold ramFastPieceExitDelta fastPieceExitDelta
  by_cases h1 : 0 < β i
  · have h1b : (ramLt 0 (β i)).val = true := by simp [ramLt, h1]
    simp [CostM.bind, h1, h1b, ramMul, ramSub, ramDiv]
    ring
  · have h1b : (ramLt 0 (β i)).val = false := by simp [ramLt, h1]
    by_cases h2 : β i < 0
    · have h2b : (ramLt (β i) 0).val = true := by simp [ramLt, h2]
      simp [CostM.bind, h1, h1b, h2, h2b, ramMul, ramNeg, ramSub, ramDiv]
      ring
    · have h2b : (ramLt (β i) 0).val = false := by simp [ramLt, h2]
      simp [CostM.bind, CostM.pure, h1, h1b, h2, h2b]

lemma ramFastPieceExitDelta_ops_le (α rem : ℝ) (s_sq φ β : ℕ → ℝ) (i : ℕ) :
    (ramFastPieceExitDelta α rem s_sq φ β i).ops ≤ 7 := by
  dsimp only [ramFastPieceExitDelta, CostM.bind, CostM.pure, ramLt, ramMul, ramNeg, ramSub, ramDiv]
  split_ifs <;> dsimp <;> omega

lemma ramComputeBeta_val {d : ℕ} (u : Fin d → ℝ) (v : ℕ → (Fin d → ℝ)) (A : Finset ℕ) (i : ℕ) :
    (ramComputeBeta u v A).val i = if i ∈ A then dotProduct u (v i) else 0 := by
  rw [ramComputeBeta, CostM.foldl_val]
  change (A.sort (· ≤ ·)).foldl (fun acc x => Function.update acc x (ramDot u (v x)).val)
    (fun _ => 0) i = if i ∈ A then dotProduct u (v i) else 0
  rw [foldl_update_of_mem (fun x => (ramDot u (v x)).val) (A.sort (· ≤ ·)) (fun _ => 0) i]
  simp [Finset.mem_sort, ramDot_val]

lemma ramComputeBeta_ops {d : ℕ} (u : Fin d → ℝ) (v : ℕ → (Fin d → ℝ)) (A : Finset ℕ) :
    (ramComputeBeta u v A).ops = 2 * d * A.card := by
  rw [ramComputeBeta, CostM.foldl_ops_eq _ _ _ (2 * d)]
  · rw [Finset.length_sort]; ring
  · intro acc i _
    simp [CostM.bind, CostM.pure, ramDot_ops]

lemma finset_fold_min_init {α : Type*} [LinearOrder α] (f : ℕ → α) (S : Finset ℕ) (a b : α) :
    S.fold min (min a b) f = min a (S.fold min b f) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    rw [Finset.fold_insert hx, Finset.fold_insert hx, ih]
    ac_rfl

lemma list_foldl_min_of_nodup {α : Type*} [LinearOrder α] (f : ℕ → α) (l : List ℕ)
    (hl : l.Nodup) (init : α) :
    l.foldl (fun acc i => min acc (f i)) init = l.toFinset.fold min init f := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    have hx : x ∉ xs.toFinset := by simpa using hl.1
    simp only [List.foldl_cons, List.toFinset_cons]
    rw [ih hl.2, Finset.fold_insert hx, min_comm init (f x), finset_fold_min_init]

lemma foldl_min_eq_finset_fold {α : Type*} [LinearOrder α] (f : ℕ → α) (A : Finset ℕ) (init : α) :
    (A.sort (· ≤ ·)).foldl (fun acc i => min acc (f i)) init = A.fold min init f := by
  rw [list_foldl_min_of_nodup f (A.sort (· ≤ ·)) (A.sort_nodup (· ≤ ·)) init, Finset.sort_toFinset]

lemma ramFastPieceStepTime_val (α rem : ℝ) (s_sq φ : ℕ → ℝ) (A : Finset ℕ) (β : ℕ → ℝ) :
    (ramFastPieceStepTime α rem s_sq φ A β).val = fastPieceStepTime α rem s_sq φ A β := by
  rw [ramFastPieceStepTime, CostM.foldl_val, fastPieceStepTime]
  change (A.sort (· ≤ ·)).foldl
    (fun acc i => min acc (ramFastPieceExitDelta α rem s_sq φ β i).val) rem =
    A.fold min rem (fun i => fastPieceExitDelta α rem s_sq φ β i)
  simp only [ramFastPieceExitDelta_val]
  exact foldl_min_eq_finset_fold (fun i => fastPieceExitDelta α rem s_sq φ β i) A rem

lemma ramFastPieceStepTime_ops_le (α rem : ℝ) (s_sq φ : ℕ → ℝ) (A : Finset ℕ) (β : ℕ → ℝ) :
    (ramFastPieceStepTime α rem s_sq φ A β).ops ≤ 8 * A.card := by
  have h := CostM.foldl_ops_le (fun acc i =>
    CostM.bind (ramFastPieceExitDelta α rem s_sq φ β i) (fun d_i => ramMin acc d_i))
    rem (A.sort (· ≤ ·)) 8 (by
      intro acc i _
      simp only [CostM.bind, ramMin]
      have h_le := ramFastPieceExitDelta_ops_le α rem s_sq φ β i
      omega)
  rw [Finset.length_sort] at h
  calc (ramFastPieceStepTime α rem s_sq φ A β).ops
      ≤ A.card * 8 := h
    _ = 8 * A.card := by ring

lemma ramPhiUpdate_val (φ : ℕ → ℝ) (δ : ℝ) (β : ℕ → ℝ) (i : ℕ) :
    (ramPhiUpdate φ δ β i).val = φ i + δ * β i := rfl

lemma ramPhiUpdate_ops (φ : ℕ → ℝ) (δ : ℝ) (β : ℕ → ℝ) (i : ℕ) :
    (ramPhiUpdate φ δ β i).ops = 2 := rfl

lemma ramSlabCheck_val (α : ℝ) (s_sq : ℕ → ℝ) (phi_i : ℝ) (i : ℕ) :
    ((ramSlabCheck α s_sq phi_i i).val = true) ↔ |phi_i| < 4 * α * s_sq i := by
  simp only [ramSlabCheck, CostM.bind, ramAbs, ramMul, ramLt, decide_eq_true_iff]
  ring_nf

lemma ramSlabCheck_ops (α : ℝ) (s_sq : ℕ → ℝ) (phi_i : ℝ) (i : ℕ) :
    (ramSlabCheck α s_sq phi_i i).ops = 4 := rfl

lemma ramUpdateSlabs_val (α δ : ℝ) (s_sq φ β : ℕ → ℝ) (A : Finset ℕ) :
    let res := (ramUpdateSlabs α δ s_sq φ β A).val
    res.1 = A.filter (fun i =>
      (ramSlabCheck α s_sq (φ i + δ * β i) i).val = true) ∧
    (∀ j, res.2 j = if j ∈ res.1 then φ j + δ * β j else 0) := by
  dsimp only
  rw [ramUpdateSlabs, CostM.foldl_val]
  let p : ℕ → Bool := fun i => (ramSlabCheck α s_sq (φ i + δ * β i) i).val
  let g : ℕ → ℝ := fun i => φ i + δ * β i
  change let res := (A.sort (· ≤ ·)).foldl (fun (acc : Finset ℕ × (ℕ → ℝ)) i =>
      if p i then (insert i acc.1, Function.update acc.2 i (g i)) else acc) (∅, fun _ => 0)
    res.1 = A.filter (fun i => p i = true) ∧
    (∀ j, res.2 j = if j ∈ res.1 then g j else 0)
  rcases foldl_filter_update p g (A.sort (· ≤ ·)) ∅ (fun _ => 0) with ⟨h1, h2⟩
  have h_set : ((A.sort (· ≤ ·)).foldl (fun (acc : Finset ℕ × (ℕ → ℝ)) i =>
      if p i then (insert i acc.1, Function.update acc.2 i (g i)) else acc) (∅, fun _ => 0)).1 =
      A.filter (fun i => p i = true) := by
    ext j
    rw [h1 j, Finset.mem_filter, Finset.mem_sort]
    simp
  refine ⟨h_set, fun j => ?_⟩
  rw [h2 j, h_set]
  simp [Finset.mem_filter, Finset.mem_sort]

lemma ramUpdateSlabs_ops (α δ : ℝ) (s_sq φ β : ℕ → ℝ) (A : Finset ℕ) :
    (ramUpdateSlabs α δ s_sq φ β A).ops = 6 * A.card := by
  rw [ramUpdateSlabs, CostM.foldl_ops_eq _ _ _ 6]
  · rw [Finset.length_sort]; ring
  · intro acc i _
    rfl

lemma ramDowndate_val {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (γ_i : ℝ) (v_i : Fin d → ℝ) :
    (ramDowndate M γ_i v_i).val = shermanMorrisonDowndate M γ_i v_i := by
  simp [ramDowndate, shermanMorrisonDowndate, CostM.bind, ramMatVec_val, ramDot_val,
    ramMul, ramSub, ramDiv, ramRankOneAdd_val]

lemma ramDowndate_ops {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (γ_i : ℝ) (v_i : Fin d → ℝ) :
    (ramDowndate M γ_i v_i).ops = downdateArithOps d := by
  simp only [ramDowndate, downdateArithOps, CostM.bind, ramMatVec_ops, ramDot_ops,
    ramMul, ramSub, ramDiv, ramRankOneAdd_ops]
  ring

lemma shermanMorrisonDowndateSetWithCost_val {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (γ : ℕ → ℝ) (v : ℕ → (Fin d → ℝ)) (R : Finset ℕ) :
    (shermanMorrisonDowndateSetWithCost M γ v R).val =
      shermanMorrisonDowndateSet M γ v R := by
  rw [shermanMorrisonDowndateSetWithCost, CostM.foldl_val, shermanMorrisonDowndateSet]
  simp only [ramDowndate_val]

lemma shermanMorrisonDowndateSetWithCost_ops {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (γ : ℕ → ℝ) (v : ℕ → (Fin d → ℝ)) (R : Finset ℕ) :
    (shermanMorrisonDowndateSetWithCost M γ v R).ops = R.card * downdateArithOps d := by
  rw [shermanMorrisonDowndateSetWithCost, CostM.foldl_ops_eq _ _ _ (downdateArithOps d)]
  · rw [Finset.length_sort]
  · intro acc i _
    exact ramDowndate_ops acc (γ i) (v i)

lemma ramStretchCreation_val {d : ℕ}
    (M_after : Matrix (Fin d) (Fin d) ℝ) (v_t : Fin d → ℝ) :
    (ramStretchCreation M_after v_t).val =
      let w := M_after *ᵥ v_t
      let s_sq := dotProduct v_t w
      (s_sq, 1 / (8 * s_sq), shermanMorrisonStretchUpdate M_after s_sq w) := by
  simp [ramStretchCreation, shermanMorrisonStretchUpdate, CostM.bind, CostM.pure,
    ramMatVec_val, ramDot_val, ramMul, ramDiv, ramRankOneSub_val]

lemma ramStretchCreation_ops {d : ℕ}
    (M_after : Matrix (Fin d) (Fin d) ℝ) (v_t : Fin d → ℝ) :
    (ramStretchCreation M_after v_t).ops = stretchArithOps d := by
  simp only [ramStretchCreation, stretchArithOps, CostM.bind, CostM.pure,
    ramMatVec_ops, ramDot_ops, ramMul, ramDiv, ramRankOneSub_ops]
  ring

lemma ramSkipStretchCreation_val {d : ℕ}
    (M_after : Matrix (Fin d) (Fin d) ℝ) (v_t : Fin d → ℝ) (t : ℕ) :
    (ramSkipStretchCreation M_after v_t t).val =
      let w := M_after *ᵥ v_t
      let s_sq := dotProduct v_t w
      let γ_t := 1 / (8 * s_sq)
      if ((t + 2 : ℝ) ^ 4)⁻¹ < s_sq then
        (true, s_sq, γ_t, shermanMorrisonStretchUpdate M_after s_sq w)
      else
        (false, s_sq, γ_t, M_after) := by
  dsimp only [ramSkipStretchCreation, shermanMorrisonStretchUpdate]
  simp only [CostM.bind, CostM.pure, ramMatVec_val, ramDot_val,
    ramMul, ramDiv, ramAdd, ramRankOneSub_val]
  have h_pow : ((t : ℝ) + 2) * ((t : ℝ) + 2) * (((t : ℝ) + 2) * ((t : ℝ) + 2)) =
      (t + 2 : ℝ) ^ 4 := by ring
  have h_inv : 1 / ((t + 2 : ℝ) ^ 4) = ((t + 2 : ℝ) ^ 4)⁻¹ := one_div _
  rw [h_pow, h_inv]
  by_cases h : ((t + 2 : ℝ) ^ 4)⁻¹ < dotProduct v_t (M_after *ᵥ v_t)
  · have hb : (ramLt (((t + 2 : ℝ) ^ 4)⁻¹) (dotProduct v_t (M_after *ᵥ v_t))).val = true := by
      simp [ramLt, h]
    simp [h, hb]
  · have hb : (ramLt (((t + 2 : ℝ) ^ 4)⁻¹) (dotProduct v_t (M_after *ᵥ v_t))).val = false := by
      simp [ramLt, h]
    simp [h, hb]

lemma ramSkipStretchCreation_ops_le {d : ℕ}
    (M_after : Matrix (Fin d) (Fin d) ℝ) (v_t : Fin d → ℝ) (t : ℕ) :
    (ramSkipStretchCreation M_after v_t t).ops ≤ skipStretchArithOps d := by
  dsimp only [ramSkipStretchCreation, skipStretchArithOps]
  simp only [CostM.bind, CostM.pure, ramMatVec_ops, ramDot_ops,
    ramMul, ramDiv, ramAdd, ramLt, ramRankOneSub_ops]
  split_ifs <;> dsimp <;> omega

lemma ramFastPiece_ops_le {d : ℕ} (α rem : ℝ) (v : ℕ → (Fin d → ℝ))
    (s_sq γ : ℕ → ℝ) (v_t : Fin d → ℝ) (p : Fin d → ℝ) (A : Finset ℕ)
    (M : Matrix (Fin d) (Fin d) ℝ) (φ : ℕ → ℝ) :
    let res := ramFastPiece α rem v s_sq γ v_t p A M φ
    let A_next := res.val.2.2.1
    res.ops + 2 ≤
      pieceArithOps d A.card + (A \ A_next).card * downdateArithOps d := by
  dsimp only [ramFastPiece]
  simp only [CostM.bind, CostM.pure, ramMatVec_ops, ramComputeBeta_ops,
    ramVecSmul_ops, ramVecAdd_ops, ramUpdateSlabs_ops, shermanMorrisonDowndateSetWithCost_ops,
    pieceArithOps]
  have h_step := ramFastPieceStepTime_ops_le α rem s_sq φ A
    (ramComputeBeta (ramMatVec M v_t).val v A).val
  nlinarith

lemma CostM.foldl_congr {α β : Type*} (f g : α → β → CostM α) (a : α) (l : List β)
    (h : ∀ acc, ∀ x ∈ l, f acc x = g acc x) :
    CostM.foldl f a l = CostM.foldl g a l := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [CostM.foldl]
    rw [h a x List.mem_cons_self]
    congr 1
    funext a'
    exact ih a' (fun acc y hy => h acc y (List.mem_cons_of_mem _ hy))

lemma ramComputeBeta_congr {d : ℕ} (u : Fin d → ℝ) (v v' : ℕ → (Fin d → ℝ)) (A : Finset ℕ)
    (hv : ∀ i ∈ A, v i = v' i) :
    ramComputeBeta u v A = ramComputeBeta u v' A := by
  unfold ramComputeBeta
  apply CostM.foldl_congr
  intro acc i hi
  rw [hv i ((Finset.mem_sort (· ≤ ·)).mp hi)]

lemma shermanMorrisonDowndateSetWithCost_congr {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (γ : ℕ → ℝ) (v v' : ℕ → (Fin d → ℝ)) (R : Finset ℕ)
    (hv : ∀ i ∈ R, v i = v' i) :
    shermanMorrisonDowndateSetWithCost M γ v R =
      shermanMorrisonDowndateSetWithCost M γ v' R := by
  unfold shermanMorrisonDowndateSetWithCost
  apply CostM.foldl_congr
  intro acc i hi
  rw [hv i ((Finset.mem_sort (· ≤ ·)).mp hi)]

lemma ramFastPiece_active_subset {d : ℕ} (α rem : ℝ) (v : ℕ → (Fin d → ℝ))
    (s_sq γ : ℕ → ℝ) (v_t : Fin d → ℝ) (p : Fin d → ℝ) (A : Finset ℕ)
    (M : Matrix (Fin d) (Fin d) ℝ) (φ : ℕ → ℝ) :
    (ramFastPiece α rem v s_sq γ v_t p A M φ).val.2.2.1 ⊆ A := by
  dsimp only [ramFastPiece, CostM.bind, CostM.pure]
  have h := (ramUpdateSlabs_val α
    (ramFastPieceStepTime α rem s_sq φ A (ramComputeBeta (ramMatVec M v_t).val v A).val).val
    s_sq φ (ramComputeBeta (ramMatVec M v_t).val v A).val A).1
  rw [h]
  exact Finset.filter_subset _ A

lemma CostM.bind_congr {α β : Type*} {m₁ m₂ : CostM α} {f g : α → CostM β}
    (hm : m₁ = m₂) (hf : f m₁.val = g m₂.val) :
    CostM.bind m₁ f = CostM.bind m₂ g := by
  subst hm
  simp only [CostM.bind, hf]

lemma ramFastPiece_congr {d : ℕ} (α rem : ℝ) (v v' : ℕ → (Fin d → ℝ))
    (s_sq γ : ℕ → ℝ) (v_t : Fin d → ℝ) (p : Fin d → ℝ) (A : Finset ℕ)
    (M : Matrix (Fin d) (Fin d) ℝ) (φ : ℕ → ℝ)
    (hv : ∀ i ∈ A, v i = v' i) :
    ramFastPiece α rem v s_sq γ v_t p A M φ =
      ramFastPiece α rem v' s_sq γ v_t p A M φ := by
  unfold ramFastPiece
  apply CostM.bind_congr rfl
  rw [ramComputeBeta_congr _ v v' A hv]
  apply CostM.bind_congr rfl
  apply CostM.bind_congr rfl
  apply CostM.bind_congr rfl
  apply CostM.bind_congr rfl
  apply CostM.bind_congr rfl
  rw [shermanMorrisonDowndateSetWithCost_congr M γ v v' _
    (fun i hi => hv i (Finset.sdiff_subset hi))]

lemma rvmFastMove_active_subset {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ))
    (s_sq γ : ℕ → ℝ) (v_t : Fin d → ℝ) :
    ∀ (n : ℕ) (rem : ℝ) (p : Fin d → ℝ) (A : Finset ℕ)
      (M : Matrix (Fin d) (Fin d) ℝ) (φ : ℕ → ℝ),
      (rvmFastMove α v s_sq γ v_t n rem p A M φ).val.2.1 ⊆ A := by
  intro n
  induction n with
  | zero => intro rem p A M φ; exact Finset.Subset.refl A
  | succ n ih =>
    intro rem p A M φ
    have h_sub1 := ramFastPiece_active_subset α rem v s_sq γ v_t p A M φ
    dsimp only [rvmFastMove, CostM.bind, CostM.pure]
    split_ifs with hcont
    · exact (ih _ _ _ _ _).trans h_sub1
    · exact h_sub1

lemma rvmFastMove_congr {d : ℕ} (α : ℝ) (v v' : ℕ → (Fin d → ℝ))
    (s_sq γ : ℕ → ℝ) (v_t : Fin d → ℝ) :
    ∀ (n : ℕ) (rem : ℝ) (p : Fin d → ℝ) (A : Finset ℕ)
      (M : Matrix (Fin d) (Fin d) ℝ) (φ : ℕ → ℝ),
      (∀ i ∈ A, v i = v' i) →
      rvmFastMove α v s_sq γ v_t n rem p A M φ =
        rvmFastMove α v' s_sq γ v_t n rem p A M φ := by
  intro n
  induction n with
  | zero => intro rem p A M φ _; rfl
  | succ n ih =>
    intro rem p A M φ hv
    have h_piece_eq := ramFastPiece_congr α rem v v' s_sq γ v_t p A M φ hv
    have h_sub1 := ramFastPiece_active_subset α rem v' s_sq γ v_t p A M φ
    have hv_next : ∀ i ∈ (ramFastPiece α rem v' s_sq γ v_t p A M φ).val.2.2.1, v i = v' i :=
      fun i hi => hv i (h_sub1 hi)
    dsimp only [rvmFastMove]
    rw [h_piece_eq]
    apply CostM.bind_congr rfl
    apply CostM.bind_congr rfl
    split_ifs with hcont
    · apply CostM.bind_congr rfl
      exact ih _ _ _ _ _ hv_next
    · rfl

lemma rvmFastState_A_sub_range {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) :
    (rvmFastState α v t).A ⊆ Finset.range t := by
  induction t with
  | zero => simp [rvmFastState]
  | succ t ih =>
    intro i hi
    simp only [rvmFastState, rvmFastStep, Finset.mem_insert] at hi
    rw [Finset.mem_range_succ_iff]
    rcases hi with rfl | hi_after
    · exact le_refl i
    · have h_sub := rvmFastMove_active_subset α v (rvmFastState α v t).s_sq
        (rvmFastState α v t).γ (v t) ((rvmFastState α v t).A.card + 1) α
        (rvmFastState α v t).p (rvmFastState α v t).A
        (rvmFastState α v t).M (rvmFastState α v t).φ
      exact le_of_lt (Finset.mem_range.mp (ih (h_sub hi_after)))

lemma rvmSkipFastState_A_sub_range {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) :
    (rvmSkipFastState α v t).A ⊆ Finset.range t := by
  induction t with
  | zero => simp [rvmSkipFastState]
  | succ t ih =>
    intro i hi
    dsimp only [rvmSkipFastState] at hi
    have h_sub := rvmFastMove_active_subset α v (rvmSkipFastState α v t).s_sq
      (rvmSkipFastState α v t).γ (v t) ((rvmSkipFastState α v t).A.card + 1) α
      (rvmSkipFastState α v t).p (rvmSkipFastState α v t).A
      (rvmSkipFastState α v t).M (rvmSkipFastState α v t).φ
    rw [Finset.mem_range_succ_iff]
    split_ifs at hi with hkeep
    · rcases Finset.mem_insert.mp hi with rfl | hi_after
      · exact le_refl i
      · exact le_of_lt (Finset.mem_range.mp (ih (h_sub hi_after)))
    · exact le_of_lt (Finset.mem_range.mp (ih (h_sub hi)))

lemma rvmFastStep_congr {d : ℕ} (α : ℝ) (v v' : ℕ → (Fin d → ℝ)) (t : ℕ)
    (st : RVMFastState d) (hstA : st.A ⊆ Finset.range t)
    (hv : ∀ s < t + 1, v s = v' s) :
    rvmFastStep α v t st = rvmFastStep α v' t st := by
  have hvt : v t = v' t := hv t (Nat.lt_succ_self t)
  have hvA : ∀ i ∈ st.A, v i = v' i :=
    fun i hi => hv i (Nat.lt_succ_of_lt (Finset.mem_range.mp (hstA hi)))
  have h_move := rvmFastMove_congr α v v' st.s_sq st.γ (v t)
    (st.A.card + 1) α st.p st.A st.M st.φ hvA
  unfold rvmFastStep
  rw [h_move, hvt]

lemma rvmFastState_causal {d : ℕ} (α : ℝ) (v v' : ℕ → (Fin d → ℝ)) (t : ℕ)
    (hv : ∀ s < t, v s = v' s) :
    rvmFastState α v t = rvmFastState α v' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih' := ih (fun s hs => hv s (Nat.lt_succ_of_lt hs))
    simp only [rvmFastState]
    rw [← ih']
    exact rvmFastStep_congr α v v' t (rvmFastState α v t) (rvmFastState_A_sub_range α v t) hv

lemma rvmSkipFastState_causal {d : ℕ} (α : ℝ) (v v' : ℕ → (Fin d → ℝ)) (t : ℕ)
    (hv : ∀ s < t, v s = v' s) :
    rvmSkipFastState α v t = rvmSkipFastState α v' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih' := ih (fun s hs => hv s (Nat.lt_succ_of_lt hs))
    have hvt : v t = v' t := hv t (Nat.lt_succ_self t)
    have hvA : ∀ i ∈ (rvmSkipFastState α v t).A, v i = v' i :=
      fun i hi => hv i (Nat.lt_succ_of_lt (Finset.mem_range.mp
        (rvmSkipFastState_A_sub_range α v t hi)))
    have h_move := rvmFastMove_congr α v v' (rvmSkipFastState α v t).s_sq
      (rvmSkipFastState α v t).γ (v t) ((rvmSkipFastState α v t).A.card + 1) α
      (rvmSkipFastState α v t).p (rvmSkipFastState α v t).A
      (rvmSkipFastState α v t).M (rvmSkipFastState α v t).φ hvA
    dsimp only [rvmSkipFastState]
    rw [← ih', h_move, hvt]

/-- **Causality of `RVM(α)` and `RVMSkip(α)` (mathematical and incremental states)** -/
theorem thm_causality : Causality_OraclePrefix := by
  intro d α v v' t hv
  have h_math := rvmState_causal α v v' t hv
  exact ⟨h_math.1, h_math.2, rvmFastState_causal α v v' t hv, rvmSkipFastState_causal α v v' t hv⟩

lemma ramFastPiece_val_eq {d : ℕ} (α rem : ℝ)
    (c v : ℕ → (Fin d → ℝ)) (s s_sq γ : ℕ → ℝ)
    (v_t : Fin d → ℝ) (p : Fin d → ℝ) (A : Finset ℕ)
    (M : Matrix (Fin d) (Fin d) ℝ) (φ : ℕ → ℝ)
    (hM : M = (stretchMetric A γ v)⁻¹)
    (hs_sq : ∀ i ∈ A, s_sq i = (s i) ^ 2)
    (hφ_in : ∀ i ∈ A, φ i = dotProduct (p - c i) (v i)) :
    let H := stretchMetric A γ v
    let u := H⁻¹ *ᵥ v_t
    let δ := pieceStepTime α rem c v s A p u
    let p_next := p + δ • u
    let A_next := open Classical in A.filter (fun i => inSlab α (c i) (v i) (s i) p_next)
    let step := ramFastPiece α rem v s_sq γ v_t p A M φ
    step.val.1 = δ ∧
    step.val.2.1 = p_next ∧
    step.val.2.2.1 = A_next ∧
    step.val.2.2.2.1 = shermanMorrisonDowndateSet M γ v (A \ A_next) ∧
    (∀ i ∈ A_next, step.val.2.2.2.2 i = dotProduct (p_next - c i) (v i)) ∧
    (∀ i ∉ A_next, step.val.2.2.2.2 i = 0) := by
  classical
  intro H u δ p_next A_next step
  have hu : (ramMatVec M v_t).val = u := by
    rw [ramMatVec_val, hM]
  set β := (ramComputeBeta u v A).val
  have hβ : ∀ i ∈ A, β i = dotProduct u (v i) := by
    intro i hi
    dsimp [β]
    rw [ramComputeBeta_val, if_pos hi]
  have hδ : (ramFastPieceStepTime α rem s_sq φ A β).val = δ := by
    rw [ramFastPieceStepTime_val]
    unfold δ fastPieceStepTime pieceStepTime
    apply Finset.fold_congr
    intro i hi
    unfold fastPieceExitDelta pieceExitDelta
    rw [hβ i hi, hs_sq i hi, hφ_in i hi]
  have hp_next : (ramVecAdd p (ramVecSmul δ u).val).val = p_next := by
    rw [ramVecAdd_val, ramVecSmul_val]
  have h_upd := ramUpdateSlabs_val α δ s_sq φ β A
  dsimp only at h_upd
  have hφ_step : ∀ i ∈ A, φ i + δ * β i = dotProduct (p_next - c i) (v i) := by
    intro i hi
    dsimp [p_next]
    rw [hφ_in i hi, hβ i hi, add_sub_right_comm, add_dotProduct, smul_dotProduct, smul_eq_mul]
  have hA_next : (ramUpdateSlabs α δ s_sq φ β A).val.1 = A_next := by
    rw [h_upd.1]
    apply Finset.filter_congr
    intro i hi
    rw [ramSlabCheck_val, hφ_step i hi, hs_sq i hi]
    rfl
  have h_step_val : step.val =
      (δ, p_next, A_next, shermanMorrisonDowndateSet M γ v (A \ A_next),
        (ramUpdateSlabs α δ s_sq φ β A).val.2) := by
    dsimp only [step, ramFastPiece, CostM.bind, CostM.pure]
    rw [hu, hδ, hp_next, hA_next, shermanMorrisonDowndateSetWithCost_val]
  rw [h_step_val]
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro i hi
    have hiA : i ∈ A := (Finset.mem_filter.mp hi).1
    have h2 := h_upd.2 i
    rw [hA_next] at h2
    rw [h2, if_pos hi, hφ_step i hiA]
  · intro i hi
    have h2 := h_upd.2 i
    rw [hA_next] at h2
    rw [h2, if_neg hi]

lemma rvmFastMove_succ_pos {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ))
    (s_sq γ : ℕ → ℝ) (v_t : Fin d → ℝ) (n : ℕ) (rem : ℝ) (p : Fin d → ℝ) (A : Finset ℕ)
    (M : Matrix (Fin d) (Fin d) ℝ) (φ : ℕ → ℝ)
    (h_lt : (ramFastPiece α rem v s_sq γ v_t p A M φ).val.1 < rem) :
    let step := ramFastPiece α rem v s_sq γ v_t p A M φ
    let rec_move := rvmFastMove α v s_sq γ v_t n (rem - step.val.1)
      step.val.2.1 step.val.2.2.1 step.val.2.2.2.1 step.val.2.2.2.2
    (rvmFastMove α v s_sq γ v_t (n + 1) rem p A M φ).val = rec_move.val ∧
    (rvmFastMove α v s_sq γ v_t (n + 1) rem p A M φ).ops = step.ops + 2 + rec_move.ops := by
  dsimp only [rvmFastMove, CostM.bind, CostM.pure]
  have hb : (ramLt (ramFastPiece α rem v s_sq γ v_t p A M φ).val.1 rem).val = true := by
    simp [ramLt, h_lt]
  rw [if_pos hb]
  dsimp only [CostM.bind, CostM.pure, ramLt, ramSub]
  exact ⟨rfl, by ring⟩

lemma rvmFastMove_succ_neg {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ))
    (s_sq γ : ℕ → ℝ) (v_t : Fin d → ℝ) (n : ℕ) (rem : ℝ) (p : Fin d → ℝ) (A : Finset ℕ)
    (M : Matrix (Fin d) (Fin d) ℝ) (φ : ℕ → ℝ)
    (h_nlt : ¬ ((ramFastPiece α rem v s_sq γ v_t p A M φ).val.1 < rem)) :
    let step := ramFastPiece α rem v s_sq γ v_t p A M φ
    (rvmFastMove α v s_sq γ v_t (n + 1) rem p A M φ).val =
      (step.val.2.1, step.val.2.2.1, step.val.2.2.2.1, step.val.2.2.2.2) ∧
    (rvmFastMove α v s_sq γ v_t (n + 1) rem p A M φ).ops = step.ops + 1 := by
  dsimp only [rvmFastMove, CostM.bind, CostM.pure]
  have hb : (ramLt (ramFastPiece α rem v s_sq γ v_t p A M φ).val.1 rem).val = false := by
    simp [ramLt, h_nlt]
  rw [if_neg (by simp [hb])]
  dsimp only [ramLt]
  exact ⟨rfl, by omega⟩

lemma rvmMoveEval_succ {d : ℕ} (α : ℝ)
    (c v : ℕ → (Fin d → ℝ)) (s γ : ℕ → ℝ) (v_t : Fin d → ℝ)
    (n : ℕ) (rem : ℝ) (p : Fin d → ℝ) (A : Finset ℕ) (τ : ℝ) :
    rvmMoveEval α c v s γ v_t (n + 1) rem p A τ =
      let H := stretchMetric A γ v
      let u := H⁻¹ *ᵥ v_t
      let δ := pieceStepTime α rem c v s A p u
      let p_next := p + δ • u
      let A_next := A.filter (fun i => inSlab α (c i) (v i) (s i) p_next)
      if τ < δ then
        (p + τ • u, A)
      else if δ < rem then
        rvmMoveEval α c v s γ v_t n (rem - δ) p_next A_next (τ - δ)
      else
        (p_next, A_next) := rfl

lemma rvmMoveEval_active_subset {d : ℕ} (α : ℝ)
    (c v : ℕ → (Fin d → ℝ)) (s γ : ℕ → ℝ) (v_t : Fin d → ℝ) :
    ∀ (n : ℕ) (rem : ℝ) (p : Fin d → ℝ) (A : Finset ℕ) (τ : ℝ),
      (rvmMoveEval α c v s γ v_t n rem p A τ).2 ⊆ A := by
  intro n
  induction n with
  | zero => intro rem p A τ; simp [rvmMoveEval]
  | succ n ih =>
    intro rem p A τ
    rw [rvmMoveEval_succ]
    dsimp only []
    split_ifs with h1 h2
    · exact Finset.Subset.refl A
    · exact Finset.Subset.trans (ih _ _ _ _) (Finset.filter_subset _ A)
    · exact Finset.filter_subset _ A

lemma card_sdiff_add_card_sdiff {α : Type*} [DecidableEq α] {A B C : Finset α}
    (hCB : C ⊆ B) (hBA : B ⊆ A) :
    (A \ B).card + (B \ C).card = (A \ C).card := by
  have h_disj : Disjoint (A \ B) (B \ C) := by
    rw [Finset.disjoint_left]
    intro x hxAB hxBC
    exact (Finset.mem_sdiff.mp hxAB).2 (Finset.mem_sdiff.mp hxBC).1
  rw [← Finset.card_union_of_disjoint h_disj]
  congr 1
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro (⟨hxA, hxB⟩ | ⟨hxB, hxC⟩)
    · exact ⟨hxA, fun hxC => hxB (hCB hxC)⟩
    · exact ⟨hBA hxB, hxC⟩
  · rintro ⟨hxA, hxC⟩
    by_cases hxB : x ∈ B
    · exact Or.inr ⟨hxB, hxC⟩
    · exact Or.inl ⟨hxA, hxB⟩

lemma shermanMorrisonDowndate_erase {d : ℕ}
    (v : ℕ → (Fin d → ℝ)) {γ : ℕ → ℝ} (hγ_nonneg : ∀ k, 0 ≤ γ k)
    (S : Finset ℕ) {i : ℕ} (hi : i ∈ S) :
    shermanMorrisonDowndate ((stretchMetric S γ v)⁻¹) (γ i) (v i) =
      (stretchMetric (S.erase i) γ v)⁻¹ := by
  classical
  set N := stretchMetric (S.erase i) γ v
  have h_ins : insert i (S.erase i) = S := Finset.insert_erase hi
  have hi_not : i ∉ S.erase i := Finset.notMem_erase i S
  have hH_eq : stretchMetric S γ v = N + (γ i) • Matrix.vecMulVec (v i) (v i) := by
    rw [← h_ins]
    dsimp [N]
    unfold stretchMetric
    rw [Finset.sum_insert hi_not]
    abel
  have hN_pd : N.PosDef := h_stretch_posDef (S.erase i) γ (fun j _ => hγ_nonneg j) v
  have hN_det : IsUnit N.det := (Matrix.isUnit_iff_isUnit_det N).mp hN_pd.isUnit
  have hN_tr : N.transpose = N := h_stretch_herm (S.erase i) γ v
  have hH_pd : (stretchMetric S γ v).PosDef := h_stretch_posDef S γ (fun j _ => hγ_nonneg j) v
  have hH_det : IsUnit (N + (γ i) • Matrix.vecMulVec (v i) (v i)).det := by
    rw [← hH_eq]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hH_pd.isUnit
  have h_q_nonneg : 0 ≤ quadForm (N⁻¹) (v i) := by
    set w := N⁻¹ *ᵥ v i
    have hNw : N *ᵥ w = v i := by
      dsimp [w]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv N hN_det, Matrix.one_mulVec]
    have h_eq : quadForm (N⁻¹) (v i) = quadForm N w := by
      unfold quadForm
      change dotProduct (v i) w = dotProduct w (N *ᵥ w)
      rw [← hNw, dotProduct_comm]
    rw [h_eq]
    dsimp [N]
    rw [h_quad_stretch]
    have := h_dot_self_nonneg w
    have : 0 ≤ ∑ j ∈ S.erase i, γ j * (dotProduct w (v j)) ^ 2 :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (hγ_nonneg j) (sq_nonneg _))
    linarith
  have h_sm := (sherman_morrison_update_and_downdate N hN_tr hN_det (v i) (γ i)
    h_q_nonneg (hγ_nonneg i) hH_det).2.2.2
  rw [← hH_eq] at h_sm
  exact h_sm.symm

lemma shermanMorrisonDowndate_foldl {d : ℕ}
    (v : ℕ → (Fin d → ℝ)) {γ : ℕ → ℝ} (hγ_nonneg : ∀ k, 0 ≤ γ k)
    (L : List ℕ) (h_nodup : L.Nodup) (A : Finset ℕ) (hL : ∀ i ∈ L, i ∈ A) :
    L.foldl (fun Acc i => shermanMorrisonDowndate Acc (γ i) (v i)) ((stretchMetric A γ v)⁻¹) =
      (stretchMetric (A \ L.toFinset) γ v)⁻¹ := by
  classical
  induction L generalizing A with
  | nil =>
    simp
  | cons i L ih =>
    rw [List.nodup_cons] at h_nodup
    rcases h_nodup with ⟨hi_not_L, hL_nodup⟩
    have hiA : i ∈ A := hL i List.mem_cons_self
    have hL_erase : ∀ j ∈ L, j ∈ A.erase i := by
      intro j hj
      rw [Finset.mem_erase]
      exact ⟨fun h_eq => hi_not_L (h_eq ▸ hj), hL j (List.mem_cons_of_mem i hj)⟩
    simp only [List.foldl_cons]
    rw [shermanMorrisonDowndate_erase v hγ_nonneg A hiA]
    rw [ih hL_nodup (A.erase i) hL_erase]
    congr 2
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_erase, List.toFinset_cons, Finset.mem_insert]
    tauto

lemma shermanMorrisonDowndateSet_eq {d : ℕ}
    (v : ℕ → (Fin d → ℝ)) {γ : ℕ → ℝ} (hγ_nonneg : ∀ k, 0 ≤ γ k)
    (A R : Finset ℕ) (hR : R ⊆ A) :
    shermanMorrisonDowndateSet ((stretchMetric A γ v)⁻¹) γ v R =
      (stretchMetric (A \ R) γ v)⁻¹ := by
  classical
  unfold shermanMorrisonDowndateSet
  have h_nodup : (R.sort (· ≤ ·)).Nodup := R.sort_nodup (· ≤ ·)
  have h_mem : ∀ i ∈ R.sort (· ≤ ·), i ∈ A := by
    intro i hi
    exact hR ((Finset.mem_sort (· ≤ ·)).mp hi)
  rw [shermanMorrisonDowndate_foldl v hγ_nonneg (R.sort (· ≤ ·)) h_nodup A h_mem]
  rw [Finset.sort_toFinset]

lemma rvmFastMove_equiv {d : ℕ} (α : ℝ)
    (c v : ℕ → (Fin d → ℝ))
    (s s_sq γ : ℕ → ℝ) (hγ_nonneg : ∀ i, 0 ≤ γ i)
    (v_t : Fin d → ℝ) (n : ℕ) (rem : ℝ) (p : Fin d → ℝ) (A : Finset ℕ)
    (M : Matrix (Fin d) (Fin d) ℝ) (φ : ℕ → ℝ)
    (hM : M = (stretchMetric A γ v)⁻¹)
    (hs_sq : ∀ i ∈ A, s_sq i = (s i) ^ 2)
    (hφ_on : ∀ i ∈ A, φ i = dotProduct (p - c i) (v i))
    (hφ_off : ∀ i ∉ A, φ i = 0) :
    let res_fast := rvmFastMove α v s_sq γ v_t n rem p A M φ
    let res_eval := rvmMoveEval α c v s γ v_t n rem p A rem
    let pieces := rvmMovePieces α c v s γ v_t n rem p A
    res_fast.val.1 = res_eval.1 ∧
    res_fast.val.2.1 = res_eval.2 ∧
    res_fast.val.2.2.1 = (stretchMetric res_eval.2 γ v)⁻¹ ∧
    (∀ i ∈ res_eval.2, res_fast.val.2.2.2 i = dotProduct (res_eval.1 - c i) (v i)) ∧
    (∀ i ∉ res_eval.2, res_fast.val.2.2.2 i = 0) ∧
    res_fast.ops ≤
      pieces * pieceArithOps d A.card +
      (A \ res_eval.2).card * downdateArithOps d := by
  classical
  induction n generalizing rem p A M φ with
  | zero =>
    dsimp only [rvmFastMove, CostM.pure, rvmMoveEval, rvmMovePieces]
    exact ⟨rfl, rfl, hM, hφ_on, hφ_off, by simp⟩
  | succ n ih =>
    set H := stretchMetric A γ v
    set u := H⁻¹ *ᵥ v_t
    set δ := pieceStepTime α rem c v s A p u
    set p_next := p + δ • u
    set A_next := A.filter (fun i => inSlab α (c i) (v i) (s i) p_next)
    have hδ_le : δ ≤ rem := (h_fold_min A rem (pieceExitDelta α rem c v s p u)).1
    have h_piece := ramFastPiece_val_eq α rem c v s s_sq γ v_t p A M φ hM hs_sq hφ_on
    set step := ramFastPiece α rem v s_sq γ v_t p A M φ
    have hM_next : step.val.2.2.2.1 = (stretchMetric A_next γ v)⁻¹ := by
      rw [h_piece.2.2.2.1, hM,
        shermanMorrisonDowndateSet_eq v hγ_nonneg A (A \ A_next) Finset.sdiff_subset]
      rw [Finset.sdiff_sdiff_eq_self (Finset.filter_subset _ A)]
    have hφ_next_on : ∀ i ∈ A_next, step.val.2.2.2.2 i = dotProduct (p_next - c i) (v i) :=
      h_piece.2.2.2.2.1
    have hφ_next_off : ∀ i ∉ A_next, step.val.2.2.2.2 i = 0 :=
      h_piece.2.2.2.2.2
    have hs_sq_next : ∀ i ∈ A_next, s_sq i = (s i) ^ 2 :=
      fun i hi => hs_sq i (Finset.filter_subset _ A hi)
    have h_fops : step.ops + 2 ≤ pieceArithOps d A.card + (A \ step.val.2.2.1).card * downdateArithOps d :=
      ramFastPiece_ops_le α rem v s_sq γ v_t p A M φ
    rw [h_piece.2.2.1] at h_fops
    by_cases h_lt : δ < rem
    · have h_step_lt : step.val.1 < rem := by rw [h_piece.1]; exact h_lt
      have h_move_pos := rvmFastMove_succ_pos α v s_sq γ v_t n rem p A M φ h_step_lt
      have h_eval_pos : rvmMoveEval α c v s γ v_t (n + 1) rem p A rem =
          rvmMoveEval α c v s γ v_t n (rem - δ) p_next A_next (rem - δ) := by
        rw [rvmMoveEval_succ]
        dsimp only []
        rw [if_neg (not_lt.mpr hδ_le), if_pos h_lt]
      have h_pieces_pos : rvmMovePieces α c v s γ v_t (n + 1) rem p A =
          1 + rvmMovePieces α c v s γ v_t n (rem - δ) p_next A_next := by
        dsimp only [rvmMovePieces]
        rw [if_pos h_lt]
      have h_ih := ih (rem - δ) p_next A_next
        step.val.2.2.2.1 step.val.2.2.2.2 hM_next hs_sq_next hφ_next_on hφ_next_off
      have h_rec_eq : rvmFastMove α v s_sq γ v_t n (rem - step.val.1)
          step.val.2.1 step.val.2.2.1 step.val.2.2.2.1 step.val.2.2.2.2 =
          rvmFastMove α v s_sq γ v_t n (rem - δ) p_next A_next
            step.val.2.2.2.1 step.val.2.2.2.2 := by
        rw [h_piece.1, h_piece.2.1, h_piece.2.2.1]
      dsimp only at h_move_pos
      rw [h_rec_eq] at h_move_pos
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h_move_pos.1, h_eval_pos]; exact h_ih.1
      · rw [h_move_pos.1, h_eval_pos]; exact h_ih.2.1
      · rw [h_move_pos.1, h_eval_pos]; exact h_ih.2.2.1
      · intro i hi
        rw [h_move_pos.1]
        rw [h_eval_pos] at hi ⊢
        exact h_ih.2.2.2.1 i hi
      · intro i hi
        rw [h_move_pos.1]
        rw [h_eval_pos] at hi
        exact h_ih.2.2.2.2.1 i hi
      · rw [h_move_pos.2, h_eval_pos, h_pieces_pos]
        set rem_ops := (rvmFastMove α v s_sq γ v_t n (rem - δ) p_next A_next
          step.val.2.2.2.1 step.val.2.2.2.2).ops
        set rem_pieces := rvmMovePieces α c v s γ v_t n (rem - δ) p_next A_next
        set A_final := (rvmMoveEval α c v s γ v_t n (rem - δ) p_next A_next (rem - δ)).2
        have h_ops_ih : rem_ops ≤
            rem_pieces * pieceArithOps d A_next.card +
            (A_next \ A_final).card * downdateArithOps d := h_ih.2.2.2.2.2
        have hA_sub : A_next ⊆ A := Finset.filter_subset _ A
        have hA_card : A_next.card ≤ A.card := Finset.card_le_card hA_sub
        have h_piece_mono : pieceArithOps d A_next.card ≤ pieceArithOps d A.card := by
          unfold pieceArithOps; nlinarith
        have h_mul :
            rem_pieces * pieceArithOps d A_next.card ≤
              rem_pieces * pieceArithOps d A.card :=
          Nat.mul_le_mul_left _ h_piece_mono
        have h_eval_sub : A_final ⊆ A_next :=
          rvmMoveEval_active_subset α c v s γ v_t n (rem - δ) p_next A_next (rem - δ)
        have h_sdiff : (A \ A_next).card + (A_next \ A_final).card = (A \ A_final).card :=
          card_sdiff_add_card_sdiff h_eval_sub hA_sub
        nlinarith [h_fops, h_ops_ih, h_mul, h_sdiff]
    · have h_step_nlt : ¬ (step.val.1 < rem) := by rw [h_piece.1]; exact h_lt
      have h_move_neg := rvmFastMove_succ_neg α v s_sq γ v_t n rem p A M φ h_step_nlt
      have h_eval_neg : rvmMoveEval α c v s γ v_t (n + 1) rem p A rem = (p_next, A_next) := by
        rw [rvmMoveEval_succ]
        dsimp only []
        rw [if_neg (not_lt.mpr hδ_le), if_neg h_lt]
      have h_pieces_neg : rvmMovePieces α c v s γ v_t (n + 1) rem p A = 1 := by
        unfold rvmMovePieces
        dsimp only []
        rw [if_neg h_lt]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h_move_neg.1, h_eval_neg]; exact h_piece.2.1
      · rw [h_move_neg.1, h_eval_neg]; exact h_piece.2.2.1
      · rw [h_move_neg.1, h_eval_neg]; exact hM_next
      · intro i hi
        rw [h_move_neg.1]
        rw [h_eval_neg] at hi ⊢
        exact hφ_next_on i hi
      · intro i hi
        rw [h_move_neg.1]
        rw [h_eval_neg] at hi
        exact hφ_next_off i hi
      · rw [h_move_neg.2, h_eval_neg, h_pieces_neg]
        nlinarith [h_fops]

lemma rvmFastState_equiv {d : ℕ} (hd : 0 < d) (α : ℝ) (hα : 0 < α)
    (v : ℕ → (Fin d → ℝ)) (h_unit : ∀ k, dotProduct (v k) (v k) = 1) (t : ℕ) :
    (rvmFastState α v t).p = (rvmState α v t).p ∧
    (rvmFastState α v t).A = (rvmState α v t).A ∧
    (rvmFastState α v t).c = (rvmState α v t).c ∧
    (∀ i, (rvmFastState α v t).s_sq i = ((rvmState α v t).s i) ^ 2) ∧
    (rvmFastState α v t).γ = (rvmState α v t).γ ∧
    (rvmFastState α v t).M = (rvmMetric α v t)⁻¹ ∧
    (∀ i ∈ (rvmFastState α v t).A, (rvmFastState α v t).φ i =
      dotProduct ((rvmFastState α v t).p - (rvmFastState α v t).c i) (v i)) ∧
    (∀ i ∉ (rvmFastState α v t).A, (rvmFastState α v t).φ i = 0) ∧
    rvmRoundArithOps α v t ≤
      rvmRoundPieces α v t * pieceArithOps d (rvmActiveSet α v t).card +
      rvmRevokedCount α v t * downdateArithOps d +
      stretchArithOps d := by
  classical
  have h_inv : ∀ r : ℕ,
      (rvmFastState α v r).p = (rvmState α v r).p ∧
      (rvmFastState α v r).A = (rvmState α v r).A ∧
      (rvmFastState α v r).c = (rvmState α v r).c ∧
      (∀ i, (rvmFastState α v r).s_sq i = ((rvmState α v r).s i) ^ 2) ∧
      (rvmFastState α v r).γ = (rvmState α v r).γ ∧
      (rvmFastState α v r).M = (rvmMetric α v r)⁻¹ ∧
      (∀ i ∈ (rvmFastState α v r).A, (rvmFastState α v r).φ i =
        dotProduct ((rvmFastState α v r).p - (rvmFastState α v r).c i) (v i)) ∧
      (∀ i ∉ (rvmFastState α v r).A, (rvmFastState α v r).φ i = 0) := by
    intro r
    induction r with
    | zero =>
      refine ⟨rfl, rfl, rfl, ?_, rfl, ?_, ?_, ?_⟩
      · intro i; unfold rvmFastState rvmState; simp
      · unfold rvmFastState rvmMetric rvmState stretchMetric; simp
      · intro i hi; unfold rvmFastState at hi; simp at hi
      · intro i _; rfl
    | succ r ih =>
      rcases ih with ⟨hp, hA, hc, hs_sq, hγ, hM, hφ_on, hφ_off⟩
      have hγ_nonneg : ∀ i, 0 ≤ (rvmState α v r).γ i := h_state_gamma_nonneg α v r
      have hγ_fast_nonneg : ∀ i, 0 ≤ (rvmFastState α v r).γ i := by
        intro i; rw [hγ]; exact hγ_nonneg i
      have hM_eq : (rvmFastState α v r).M =
          (stretchMetric (rvmFastState α v r).A (rvmFastState α v r).γ v)⁻¹ := by
        rw [hM, hA, hγ]; rfl
      have hs_sq_A : ∀ i ∈ (rvmFastState α v r).A,
          (rvmFastState α v r).s_sq i = ((rvmState α v r).s i) ^ 2 :=
        fun i _ => hs_sq i
      have h_move := rvmFastMove_equiv α (rvmFastState α v r).c v
        (rvmState α v r).s (rvmFastState α v r).s_sq (rvmFastState α v r).γ hγ_fast_nonneg
        (v r) ((rvmFastState α v r).A.card + 1) α
        (rvmFastState α v r).p (rvmFastState α v r).A
        (rvmFastState α v r).M (rvmFastState α v r).φ hM_eq hs_sq_A hφ_on hφ_off
      have h_eval_eq :
          rvmMoveEval α (rvmFastState α v r).c v (rvmState α v r).s (rvmFastState α v r).γ
            (v r) ((rvmFastState α v r).A.card + 1) α
            (rvmFastState α v r).p (rvmFastState α v r).A α =
          rvmMoveEval α (rvmState α v r).c v (rvmState α v r).s (rvmState α v r).γ
            (v r) ((rvmState α v r).A.card + 1) α
            (rvmState α v r).p (rvmState α v r).A α := by
        rw [hp, hA, hc, hγ]
      set move := rvmFastMove α v (rvmFastState α v r).s_sq (rvmFastState α v r).γ
        (v r) ((rvmFastState α v r).A.card + 1) α
        (rvmFastState α v r).p (rvmFastState α v r).A
        (rvmFastState α v r).M (rvmFastState α v r).φ
      set res_eval := rvmMoveEval α (rvmState α v r).c v (rvmState α v r).s (rvmState α v r).γ
        (v r) ((rvmState α v r).A.card + 1) α
        (rvmState α v r).p (rvmState α v r).A α
      have hp_next : move.val.1 = res_eval.1 := by rw [h_move.1, h_eval_eq]
      have hA_after : move.val.2.1 = res_eval.2 := by rw [h_move.2.1, h_eval_eq]
      have hM_after : move.val.2.2.1 = (rvmPathMetric α v r α)⁻¹ := by
        rw [h_move.2.2.1, h_eval_eq, hγ]; rfl
      have h_str_val := ramStretchCreation_val move.val.2.2.1 (v r)
      have h_c := lem_2_3c lem_2_3b hd α hα v h_unit r 0 α (le_refl 0) (le_of_lt hα) (le_refl α)
      have hs_pos : 0 < rvmStepNorm α v r :=
        lt_of_lt_of_le h_c.2.2.2.1 (le_trans h_c.2.2.2.2.1 h_c.2.2.2.2.2.1)
      have hs_sq_eq : dotProduct (v r) (move.val.2.2.1 *ᵥ v r) = (rvmStepNorm α v r) ^ 2 := by
        have h_sqrt_eq : Real.sqrt (dotProduct (v r) (move.val.2.2.1 *ᵥ v r)) = rvmStepNorm α v r := by
          rw [hM_after]; rfl
        have h_nn : 0 ≤ dotProduct (v r) (move.val.2.2.1 *ᵥ v r) :=
          le_of_lt (Real.sqrt_pos.mp (by linarith))
        rw [← h_sqrt_eq, Real.sq_sqrt h_nn]
      have hs_sq_t : (ramStretchCreation move.val.2.2.1 (v r)).val.1 = (rvmStepNorm α v r) ^ 2 := by
        rw [h_str_val]; exact hs_sq_eq
      have hγ_t : (ramStretchCreation move.val.2.2.1 (v r)).val.2.1 =
          1 / (8 * (rvmStepNorm α v r) ^ 2) := by
        rw [h_str_val]; dsimp only []; rw [hs_sq_eq]
      have h_sm := (rem_cost_counts_core hd α hα v h_unit).2.2.2.2.2.2.2 r
      have hM_next : (ramStretchCreation move.val.2.2.1 (v r)).val.2.2 =
          (rvmMetric α v (r + 1))⁻¹ := by
        rw [h_str_val]
        dsimp only [shermanMorrisonStretchUpdate]
        rw [hs_sq_eq, hM_after, ← h_sm.2]
      refine ⟨hp_next, ?_, ?_, ?_, ?_, hM_next, ?_, ?_⟩
      · change insert r move.val.2.1 = insert r res_eval.2
        rw [hA_after]
      · change Function.update (rvmFastState α v r).c r move.val.1 =
          Function.update (rvmState α v r).c r res_eval.1
        rw [hc, hp_next]
      · intro i
        change Function.update (rvmFastState α v r).s_sq r
          (ramStretchCreation move.val.2.2.1 (v r)).val.1 i =
          (Function.update (rvmState α v r).s r (rvmStepNorm α v r) i) ^ 2
        by_cases hir : i = r
        · subst hir
          rw [Function.update_self, Function.update_self, hs_sq_t]
        · rw [Function.update_of_ne hir, Function.update_of_ne hir]
          exact hs_sq i
      · change Function.update (rvmFastState α v r).γ r
          (ramStretchCreation move.val.2.2.1 (v r)).val.2.1 =
          Function.update (rvmState α v r).γ r (1 / (8 * (rvmStepNorm α v r) ^ 2))
        rw [hγ, hγ_t]
      · intro i hi
        change Function.update move.val.2.2.2 r 0 i =
          dotProduct (move.val.1 - Function.update (rvmFastState α v r).c r move.val.1 i) (v i)
        by_cases hir : i = r
        · subst hir
          rw [Function.update_self, Function.update_self, sub_self, zero_dotProduct]
        · rw [Function.update_of_ne hir, Function.update_of_ne hir]
          have hi_mem : i ∈ move.val.2.1 := by
            change i ∈ insert r move.val.2.1 at hi
            exact (Finset.mem_insert.mp hi).resolve_left hir
          rw [h_move.2.2.2.1 i (h_move.2.1 ▸ hi_mem), h_move.1]
      · intro i hi
        change Function.update move.val.2.2.2 r 0 i = 0
        have hi_not_ins : i ∉ insert r move.val.2.1 := hi
        have hir : i ≠ r := by rintro rfl; exact hi_not_ins (Finset.mem_insert_self i _)
        have hi_not_move : i ∉ move.val.2.1 :=
          fun hm => hi_not_ins (Finset.mem_insert_of_mem hm)
        rw [Function.update_of_ne hir]
        exact h_move.2.2.2.2.1 i (h_move.2.1 ▸ hi_not_move)
  rcases h_inv t with ⟨hp, hA, hc, hs_sq, hγ, hM, hφ_on, hφ_off⟩
  refine ⟨hp, hA, hc, hs_sq, hγ, hM, hφ_on, hφ_off, ?_⟩
  have hγ_nonneg : ∀ i, 0 ≤ (rvmState α v t).γ i := h_state_gamma_nonneg α v t
  have hγ_fast_nonneg : ∀ i, 0 ≤ (rvmFastState α v t).γ i := by
    intro i; rw [hγ]; exact hγ_nonneg i
  have hM_eq : (rvmFastState α v t).M =
      (stretchMetric (rvmFastState α v t).A (rvmFastState α v t).γ v)⁻¹ := by
    rw [hM, hA, hγ]; rfl
  have hs_sq_A : ∀ i ∈ (rvmFastState α v t).A,
      (rvmFastState α v t).s_sq i = ((rvmState α v t).s i) ^ 2 :=
    fun i _ => hs_sq i
  have h_move := rvmFastMove_equiv α (rvmFastState α v t).c v
    (rvmState α v t).s (rvmFastState α v t).s_sq (rvmFastState α v t).γ hγ_fast_nonneg
    (v t) ((rvmFastState α v t).A.card + 1) α
    (rvmFastState α v t).p (rvmFastState α v t).A
    (rvmFastState α v t).M (rvmFastState α v t).φ hM_eq hs_sq_A hφ_on hφ_off
  set move := rvmFastMove α v (rvmFastState α v t).s_sq (rvmFastState α v t).γ
    (v t) ((rvmFastState α v t).A.card + 1) α
    (rvmFastState α v t).p (rvmFastState α v t).A
    (rvmFastState α v t).M (rvmFastState α v t).φ
  have h_pieces_eq :
      rvmMovePieces α (rvmFastState α v t).c v (rvmState α v t).s (rvmFastState α v t).γ
        (v t) ((rvmFastState α v t).A.card + 1) α
        (rvmFastState α v t).p (rvmFastState α v t).A =
      rvmRoundPieces α v t := by
    unfold rvmRoundPieces
    rw [hp, hA, hc, hγ]
  have h_rev_eq :
      ((rvmFastState α v t).A \
        (rvmMoveEval α (rvmFastState α v t).c v (rvmState α v t).s (rvmFastState α v t).γ
          (v t) ((rvmFastState α v t).A.card + 1) α
          (rvmFastState α v t).p (rvmFastState α v t).A α).2).card =
      rvmRevokedCount α v t := by
    unfold rvmRevokedCount rvmRevokedInRound rvmActiveSet rvmPathActiveSet
    rw [hp, hA, hc, hγ]
  have h_card_eq : (rvmFastState α v t).A.card = (rvmActiveSet α v t).card := by
    unfold rvmActiveSet; rw [hA]
  have h_str_ops := ramStretchCreation_ops move.val.2.2.1 (v t)
  have h_mops := h_move.2.2.2.2.2
  rw [h_pieces_eq, h_rev_eq, h_card_eq] at h_mops
  change move.ops + (ramStretchCreation move.val.2.2.1 (v t)).ops ≤ _
  rw [h_str_ops]
  omega

lemma rvmSkipFastState_equiv {d : ℕ} (α : ℝ)
    (v : ℕ → (Fin d → ℝ)) (h_unit : ∀ k, dotProduct (v k) (v k) = 1) (t : ℕ) :
    (rvmSkipFastState α v t).p = (rvmSkipState α v t).p ∧
    (rvmSkipFastState α v t).A = (rvmSkipState α v t).A ∧
    (rvmSkipFastState α v t).c = (rvmSkipState α v t).c ∧
    (∀ i, (rvmSkipFastState α v t).s_sq i = ((rvmSkipState α v t).s i) ^ 2) ∧
    (rvmSkipFastState α v t).γ = (rvmSkipState α v t).γ ∧
    (rvmSkipFastState α v t).M = (rvmSkipMetric α v t)⁻¹ ∧
    (∀ i ∈ (rvmSkipFastState α v t).A, (rvmSkipFastState α v t).φ i =
      dotProduct ((rvmSkipFastState α v t).p - (rvmSkipFastState α v t).c i) (v i)) ∧
    (∀ i ∉ (rvmSkipFastState α v t).A, (rvmSkipFastState α v t).φ i = 0) ∧
    rvmSkipRoundArithOps α v t ≤
      rvmSkipRoundPieces α v t * pieceArithOps d (rvmSkipActiveSet α v t).card +
      rvmSkipRevokedCount α v t * downdateArithOps d +
      skipStretchArithOps d := by
  classical
  have h_inv : ∀ r : ℕ,
      (rvmSkipFastState α v r).p = (rvmSkipState α v r).p ∧
      (rvmSkipFastState α v r).A = (rvmSkipState α v r).A ∧
      (rvmSkipFastState α v r).c = (rvmSkipState α v r).c ∧
      (∀ i, (rvmSkipFastState α v r).s_sq i = ((rvmSkipState α v r).s i) ^ 2) ∧
      (rvmSkipFastState α v r).γ = (rvmSkipState α v r).γ ∧
      (rvmSkipFastState α v r).M = (rvmSkipMetric α v r)⁻¹ ∧
      (∀ i ∈ (rvmSkipFastState α v r).A, (rvmSkipFastState α v r).φ i =
        dotProduct ((rvmSkipFastState α v r).p - (rvmSkipFastState α v r).c i) (v i)) ∧
      (∀ i ∉ (rvmSkipFastState α v r).A, (rvmSkipFastState α v r).φ i = 0) := by
    intro r
    induction r with
    | zero =>
      refine ⟨rfl, rfl, rfl, ?_, rfl, ?_, ?_, ?_⟩
      · intro i; unfold rvmSkipFastState rvmSkipState; simp
      · unfold rvmSkipFastState rvmSkipMetric rvmSkipState stretchMetric; simp
      · intro i hi; unfold rvmSkipFastState at hi; simp at hi
      · intro i _; rfl
    | succ r ih =>
      rcases ih with ⟨hp, hA, hc, hs_sq, hγ, hM, hφ_on, hφ_off⟩
      have hγ_nonneg : ∀ i, 0 ≤ (rvmSkipState α v r).γ i := SkipHelpers.h_state_gamma_nonneg α v r
      have hγ_fast_nonneg : ∀ i, 0 ≤ (rvmSkipFastState α v r).γ i := by
        intro i; rw [hγ]; exact hγ_nonneg i
      have hM_eq : (rvmSkipFastState α v r).M =
          (stretchMetric (rvmSkipFastState α v r).A (rvmSkipFastState α v r).γ v)⁻¹ := by
        rw [hM, hA, hγ]; rfl
      have hs_sq_A : ∀ i ∈ (rvmSkipFastState α v r).A,
          (rvmSkipFastState α v r).s_sq i = ((rvmSkipState α v r).s i) ^ 2 :=
        fun i _ => hs_sq i
      have h_move := rvmFastMove_equiv α (rvmSkipFastState α v r).c v
        (rvmSkipState α v r).s (rvmSkipFastState α v r).s_sq (rvmSkipFastState α v r).γ hγ_fast_nonneg
        (v r) ((rvmSkipFastState α v r).A.card + 1) α
        (rvmSkipFastState α v r).p (rvmSkipFastState α v r).A
        (rvmSkipFastState α v r).M (rvmSkipFastState α v r).φ hM_eq hs_sq_A hφ_on hφ_off
      have h_eval_eq :
          rvmMoveEval α (rvmSkipFastState α v r).c v
            (rvmSkipState α v r).s (rvmSkipFastState α v r).γ
            (v r) ((rvmSkipFastState α v r).A.card + 1) α
            (rvmSkipFastState α v r).p (rvmSkipFastState α v r).A α =
          rvmMoveEval α (rvmSkipState α v r).c v (rvmSkipState α v r).s (rvmSkipState α v r).γ
            (v r) ((rvmSkipState α v r).A.card + 1) α
            (rvmSkipState α v r).p (rvmSkipState α v r).A α := by
        rw [hp, hA, hc, hγ]
      set move := rvmFastMove α v (rvmSkipFastState α v r).s_sq (rvmSkipFastState α v r).γ
        (v r) ((rvmSkipFastState α v r).A.card + 1) α
        (rvmSkipFastState α v r).p (rvmSkipFastState α v r).A
        (rvmSkipFastState α v r).M (rvmSkipFastState α v r).φ
      set res_eval := rvmMoveEval α (rvmSkipState α v r).c v
        (rvmSkipState α v r).s (rvmSkipState α v r).γ
        (v r) ((rvmSkipState α v r).A.card + 1) α
        (rvmSkipState α v r).p (rvmSkipState α v r).A α
      have hp_next : move.val.1 = res_eval.1 := by rw [h_move.1, h_eval_eq]
      have hA_after : move.val.2.1 = res_eval.2 := by rw [h_move.2.1, h_eval_eq]
      have hM_after : move.val.2.2.1 = (skipPathMetric α v r α)⁻¹ := by
        rw [h_move.2.2.1, h_eval_eq, hγ]; rfl
      have h_str_val := ramSkipStretchCreation_val move.val.2.2.1 (v r) r
      have hs_pos : 0 < skipStepNorm α v r := SkipHelpers.h_step_norm_pos α v h_unit r
      have hs_sq_eq : dotProduct (v r) (move.val.2.2.1 *ᵥ v r) = (skipStepNorm α v r) ^ 2 := by
        have h_sqrt_eq : Real.sqrt (dotProduct (v r) (move.val.2.2.1 *ᵥ v r)) = skipStepNorm α v r := by
          rw [hM_after]; rfl
        have h_nn : 0 ≤ dotProduct (v r) (move.val.2.2.1 *ᵥ v r) :=
          le_of_lt (Real.sqrt_pos.mp (by linarith))
        rw [← h_sqrt_eq, Real.sq_sqrt h_nn]
      have hs_sq_t : (ramSkipStretchCreation move.val.2.2.1 (v r) r).val.2.1 =
          (skipStepNorm α v r) ^ 2 := by
        rw [h_str_val]; dsimp only []; split_ifs <;> exact hs_sq_eq
      have hγ_t : (ramSkipStretchCreation move.val.2.2.1 (v r) r).val.2.2.1 =
          1 / (8 * (skipStepNorm α v r) ^ 2) := by
        rw [h_str_val]; dsimp only []; split_ifs <;> rw [hs_sq_eq]
      have h_keep_iff : (ramSkipStretchCreation move.val.2.2.1 (v r) r).val.1 = true ↔
          (skipStepNorm α v r) ^ 2 > ((r + 2 : ℝ) ^ 4)⁻¹ := by
        rw [h_str_val]; dsimp only []; rw [hs_sq_eq, gt_iff_lt]
        split_ifs with h <;> simp [h]
      set S := rvmSkipPathActiveSet α v r α
      have h_sub_range : S ⊆ Finset.range r :=
        (moveEval_snd_sub _ _ _ _ _ _ _ _ _ _ _).trans (rvmSkipState_A_sub_range α v r)
      have hr_not_mem : r ∉ S := by
        intro hrS
        have := Finset.mem_range.mp (h_sub_range hrS)
        omega
      have h_path_gamma : stretchMetric S (Function.update (rvmSkipState α v r).γ r (skipWeight α v r)) v =
          skipPathMetric α v r α := by
        unfold skipPathMetric stretchMetric
        dsimp only []
        congr 1
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi_ne : i ≠ r := fun h_eq => hr_not_mem (h_eq ▸ hi)
        rw [Function.update_of_ne hi_ne]
      have hM_next : (ramSkipStretchCreation move.val.2.2.1 (v r) r).val.2.2.2 =
          (rvmSkipMetric α v (r + 1))⁻¹ := by
        rw [h_str_val]
        dsimp only []
        rw [hs_sq_eq]
        by_cases hk : ((r + 2 : ℝ) ^ 4)⁻¹ < (skipStepNorm α v r) ^ 2
        · rw [if_pos hk]
          dsimp only []
          unfold rvmSkipMetric
          change shermanMorrisonStretchUpdate move.val.2.2.1 ((skipStepNorm α v r) ^ 2)
              (move.val.2.2.1 *ᵥ v r) =
            (stretchMetric (if (skipStepNorm α v r) ^ 2 > ((r + 2 : ℝ) ^ 4)⁻¹ then
              insert r S else S)
              (Function.update (rvmSkipState α v r).γ r (skipWeight α v r)) v)⁻¹
          rw [if_pos hk]
          have h_ins_eq : stretchMetric (insert r S)
              (Function.update (rvmSkipState α v r).γ r (skipWeight α v r)) v =
              skipPathMetric α v r α + (skipWeight α v r) • Matrix.vecMulVec (v r) (v r) := by
            rw [← h_path_gamma]
            unfold stretchMetric
            rw [Finset.sum_insert hr_not_mem, Function.update_self]
            abel
          set G := skipPathMetric α v r α
          have hG_pd : G.PosDef := h_stretch_posDef S _ (fun j _ => hγ_nonneg j) v
          have hG_det : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG_pd.isUnit
          have hG_tr : G.transpose = G := h_stretch_herm S _ v
          have h_q_nonneg : 0 ≤ quadForm (G⁻¹) (v r) := by
            rw [← hM_after]; change 0 ≤ dotProduct (v r) (move.val.2.2.1 *ᵥ v r)
            rw [hs_sq_eq]; positivity
          have hγ_r_nn : 0 ≤ skipWeight α v r := by unfold skipWeight; positivity
          have hG'_pd : (G + (skipWeight α v r) • Matrix.vecMulVec (v r) (v r)).PosDef := by
            rw [← h_ins_eq]
            exact h_stretch_posDef _ _ (fun j _ => SkipHelpers.h_state_gamma_nonneg α v (r + 1) j) v
          have hG'_det : IsUnit (G + (skipWeight α v r) • Matrix.vecMulVec (v r) (v r)).det :=
            (Matrix.isUnit_iff_isUnit_det _).mp hG'_pd.isUnit
          have h_sm := (sherman_morrison_update_and_downdate G hG_tr hG_det (v r) (skipWeight α v r)
            h_q_nonneg hγ_r_nn hG'_det).1
          have h_q_eq : quadForm (G⁻¹) (v r) = (skipStepNorm α v r) ^ 2 := by
            rw [← hM_after]; exact hs_sq_eq
          have h_coeff : skipWeight α v r / (1 + skipWeight α v r * (skipStepNorm α v r) ^ 2) =
              1 / (9 * (skipStepNorm α v r) ^ 2) := by
            unfold skipWeight
            have hs_sq_pos : 0 < (skipStepNorm α v r) ^ 2 := sq_pos_of_pos hs_pos
            field_simp
            ring
          rw [h_ins_eq, h_sm, h_q_eq, h_coeff, hM_after]
          rfl
        · rw [if_neg hk]
          dsimp only []
          unfold rvmSkipMetric
          change move.val.2.2.1 =
            (stretchMetric (if (skipStepNorm α v r) ^ 2 > ((r + 2 : ℝ) ^ 4)⁻¹ then
              insert r S else S)
              (Function.update (rvmSkipState α v r).γ r (skipWeight α v r)) v)⁻¹
          rw [if_neg hk, h_path_gamma, hM_after]
      refine ⟨hp_next, ?_, ?_, ?_, ?_, hM_next, ?_, ?_⟩
      · change (if (ramSkipStretchCreation move.val.2.2.1 (v r) r).val.1 then
            insert r move.val.2.1 else move.val.2.1) =
          (if (skipStepNorm α v r) ^ 2 > ((r + 2 : ℝ) ^ 4)⁻¹ then
            insert r res_eval.2 else res_eval.2)
        rw [hA_after]
        by_cases hk : (skipStepNorm α v r) ^ 2 > ((r + 2 : ℝ) ^ 4)⁻¹
        · rw [if_pos (h_keep_iff.mpr hk), if_pos hk]
        · have h_false : ¬ ((ramSkipStretchCreation move.val.2.2.1 (v r) r).val.1 = true) :=
            fun h => hk (h_keep_iff.mp h)
          rw [if_neg h_false, if_neg hk]
      · change Function.update (rvmSkipFastState α v r).c r move.val.1 =
          Function.update (rvmSkipState α v r).c r res_eval.1
        rw [hc, hp_next]
      · intro i
        change Function.update (rvmSkipFastState α v r).s_sq r
          (ramSkipStretchCreation move.val.2.2.1 (v r) r).val.2.1 i =
          (Function.update (rvmSkipState α v r).s r (skipStepNorm α v r) i) ^ 2
        by_cases hir : i = r
        · subst hir
          rw [Function.update_self, Function.update_self, hs_sq_t]
        · rw [Function.update_of_ne hir, Function.update_of_ne hir]
          exact hs_sq i
      · change Function.update (rvmSkipFastState α v r).γ r
          (ramSkipStretchCreation move.val.2.2.1 (v r) r).val.2.2.1 =
          Function.update (rvmSkipState α v r).γ r (1 / (8 * (skipStepNorm α v r) ^ 2))
        rw [hγ, hγ_t]
      · intro i hi
        change (if (ramSkipStretchCreation move.val.2.2.1 (v r) r).val.1 then
            Function.update move.val.2.2.2 r 0 else move.val.2.2.2) i =
          dotProduct (move.val.1 - Function.update (rvmSkipFastState α v r).c r move.val.1 i) (v i)
        change i ∈ (if (ramSkipStretchCreation move.val.2.2.1 (v r) r).val.1 then
          insert r move.val.2.1 else move.val.2.1) at hi
        by_cases h_keep : (ramSkipStretchCreation move.val.2.2.1 (v r) r).val.1 = true
        · rw [if_pos h_keep] at hi ⊢
          by_cases hir : i = r
          · subst hir
            rw [Function.update_self, Function.update_self, sub_self, zero_dotProduct]
          · rw [Function.update_of_ne hir, Function.update_of_ne hir]
            have hi_mem : i ∈ move.val.2.1 := (Finset.mem_insert.mp hi).resolve_left hir
            rw [h_move.2.2.2.1 i (h_move.2.1 ▸ hi_mem), h_move.1]
        · rw [if_neg h_keep] at hi ⊢
          have hi_eval : i ∈ res_eval.2 := by rw [← hA_after]; exact hi
          have hir : i ≠ r := fun h_eq => hr_not_mem (h_eq ▸ hi_eval)
          rw [Function.update_of_ne hir]
          rw [h_move.2.2.2.1 i (h_move.2.1 ▸ hi), h_move.1]
      · intro i hi
        change (if (ramSkipStretchCreation move.val.2.2.1 (v r) r).val.1 then
            Function.update move.val.2.2.2 r 0 else move.val.2.2.2) i = 0
        change i ∉ (if (ramSkipStretchCreation move.val.2.2.1 (v r) r).val.1 then
          insert r move.val.2.1 else move.val.2.1) at hi
        by_cases h_keep : (ramSkipStretchCreation move.val.2.2.1 (v r) r).val.1 = true
        · rw [if_pos h_keep] at hi ⊢
          have hir : i ≠ r := by rintro rfl; exact hi (Finset.mem_insert_self i _)
          have hi_not : i ∉ move.val.2.1 := fun hm => hi (Finset.mem_insert_of_mem hm)
          rw [Function.update_of_ne hir]
          exact h_move.2.2.2.2.1 i (h_move.2.1 ▸ hi_not)
        · rw [if_neg h_keep] at hi ⊢
          exact h_move.2.2.2.2.1 i (h_move.2.1 ▸ hi)
  rcases h_inv t with ⟨hp, hA, hc, hs_sq, hγ, hM, hφ_on, hφ_off⟩
  refine ⟨hp, hA, hc, hs_sq, hγ, hM, hφ_on, hφ_off, ?_⟩
  have hγ_nonneg : ∀ i, 0 ≤ (rvmSkipState α v t).γ i := SkipHelpers.h_state_gamma_nonneg α v t
  have hγ_fast_nonneg : ∀ i, 0 ≤ (rvmSkipFastState α v t).γ i := by
    intro i; rw [hγ]; exact hγ_nonneg i
  have hM_eq : (rvmSkipFastState α v t).M =
      (stretchMetric (rvmSkipFastState α v t).A (rvmSkipFastState α v t).γ v)⁻¹ := by
    rw [hM, hA, hγ]; rfl
  have hs_sq_A : ∀ i ∈ (rvmSkipFastState α v t).A,
      (rvmSkipFastState α v t).s_sq i = ((rvmSkipState α v t).s i) ^ 2 :=
    fun i _ => hs_sq i
  have h_move := rvmFastMove_equiv α (rvmSkipFastState α v t).c v
    (rvmSkipState α v t).s (rvmSkipFastState α v t).s_sq (rvmSkipFastState α v t).γ hγ_fast_nonneg
    (v t) ((rvmSkipFastState α v t).A.card + 1) α
    (rvmSkipFastState α v t).p (rvmSkipFastState α v t).A
    (rvmSkipFastState α v t).M (rvmSkipFastState α v t).φ hM_eq hs_sq_A hφ_on hφ_off
  set move := rvmFastMove α v (rvmSkipFastState α v t).s_sq (rvmSkipFastState α v t).γ
    (v t) ((rvmSkipFastState α v t).A.card + 1) α
    (rvmSkipFastState α v t).p (rvmSkipFastState α v t).A
    (rvmSkipFastState α v t).M (rvmSkipFastState α v t).φ
  have h_pieces_eq :
      rvmMovePieces α (rvmSkipFastState α v t).c v
        (rvmSkipState α v t).s (rvmSkipFastState α v t).γ
        (v t) ((rvmSkipFastState α v t).A.card + 1) α
        (rvmSkipFastState α v t).p (rvmSkipFastState α v t).A =
      rvmSkipRoundPieces α v t := by
    unfold rvmSkipRoundPieces
    rw [hp, hA, hc, hγ]
  have h_rev_eq :
      ((rvmSkipFastState α v t).A \
        (rvmMoveEval α (rvmSkipFastState α v t).c v
          (rvmSkipState α v t).s (rvmSkipFastState α v t).γ
          (v t) ((rvmSkipFastState α v t).A.card + 1) α
          (rvmSkipFastState α v t).p (rvmSkipFastState α v t).A α).2).card =
      rvmSkipRevokedCount α v t := by
    unfold rvmSkipRevokedCount rvmSkipRevokedInRound rvmSkipActiveSet rvmSkipPathActiveSet
    rw [hp, hA, hc, hγ]
  have h_card_eq : (rvmSkipFastState α v t).A.card = (rvmSkipActiveSet α v t).card := by
    unfold rvmSkipActiveSet; rw [hA]
  have h_str_ops := ramSkipStretchCreation_ops_le move.val.2.2.1 (v t) t
  have h_mops := h_move.2.2.2.2.2
  rw [h_pieces_eq, h_rev_eq, h_card_eq] at h_mops
  change move.ops + (ramSkipStretchCreation move.val.2.2.1 (v t) t).ops ≤ _
  omega

lemma rvmTotalArithOps_eq_sum {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (T : ℕ) :
    rvmTotalArithOps α v T = ∑ t ∈ Finset.range T, rvmRoundArithOps α v t := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Finset.sum_range_succ, ← ih]
    rfl

lemma rvmSkipTotalArithOps_eq_sum {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (T : ℕ) :
    rvmSkipTotalArithOps α v T = ∑ t ∈ Finset.range T, rvmSkipRoundArithOps α v t := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Finset.sum_range_succ, ← ih]
    rfl

lemma pieceArithOps_le {d : ℕ} (hd : 0 < d) (cardA : ℕ) :
    pieceArithOps d cardA ≤ 6 * d ^ 2 + 18 * cardA * d := by
  unfold pieceArithOps
  nlinarith

lemma downdateArithOps_le {d : ℕ} (hd : 0 < d) :
    downdateArithOps d ≤ 10 * d ^ 2 := by
  unfold downdateArithOps
  nlinarith

lemma stretchArithOps_le {d : ℕ} (hd : 0 < d) :
    stretchArithOps d ≤ 12 * d ^ 2 := by
  unfold stretchArithOps
  nlinarith

lemma skipStretchArithOps_le {d : ℕ} (hd : 0 < d) :
    skipStretchArithOps d ≤ 17 * d ^ 2 := by
  unfold skipStretchArithOps
  nlinarith

lemma oiloReductionArithOps_le {d : ℕ} (hd : 0 < d) :
    oiloReductionArithOps d ≤ 8 * d ^ 2 := by
  unfold oiloReductionArithOps
  nlinarith

lemma round_ops_bound_aux {d pieces k cardA : ℕ} (hd : 0 < d)
    (hp : pieces ≤ k + 1) :
    pieces * pieceArithOps d cardA + k * downdateArithOps d + stretchArithOps d ≤
      28 * (k + 1) * (d ^ 2 + cardA * d) := by
  have h1 := pieceArithOps_le hd cardA
  have h2 := downdateArithOps_le hd
  have h3 := stretchArithOps_le hd
  have h_p_mul : pieces * pieceArithOps d cardA ≤ (k + 1) * (6 * d ^ 2 + 18 * cardA * d) :=
    Nat.mul_le_mul hp h1
  have h_d_mul : k * downdateArithOps d ≤ k * (10 * d ^ 2) :=
    Nat.mul_le_mul_left k h2
  have h_alg : (k + 1) * (6 * d ^ 2 + 18 * cardA * d) + k * (10 * d ^ 2) + 12 * d ^ 2 +
      ((12 * k + 10) * d ^ 2 + 10 * (k + 1) * cardA * d) =
      28 * (k + 1) * (d ^ 2 + cardA * d) := by ring
  omega

lemma skip_round_ops_bound_aux {d pieces k cardA : ℕ} (hd : 0 < d)
    (hp : pieces ≤ k + 1) :
    pieces * pieceArithOps d cardA + k * downdateArithOps d + skipStretchArithOps d ≤
      33 * (k + 1) * (d ^ 2 + cardA * d) := by
  have h1 := pieceArithOps_le hd cardA
  have h2 := downdateArithOps_le hd
  have h3 := skipStretchArithOps_le hd
  have h_p_mul : pieces * pieceArithOps d cardA ≤ (k + 1) * (6 * d ^ 2 + 18 * cardA * d) :=
    Nat.mul_le_mul hp h1
  have h_d_mul : k * downdateArithOps d ≤ k * (10 * d ^ 2) :=
    Nat.mul_le_mul_left k h2
  have h_alg : (k + 1) * (6 * d ^ 2 + 18 * cardA * d) + k * (10 * d ^ 2) + 17 * d ^ 2 +
      ((17 * k + 10) * d ^ 2 + 15 * (k + 1) * cardA * d) =
      33 * (k + 1) * (d ^ 2 + cardA * d) := by ring
  omega

lemma rvmRoundArithOps_le {d : ℕ} (hd : 0 < d) (α : ℝ) (hα : 0 < α)
    (v : ℕ → (Fin d → ℝ)) (h_unit : ∀ k, dotProduct (v k) (v k) = 1) (t : ℕ) :
    rvmRoundArithOps α v t ≤
      28 * (rvmRevokedCount α v t + 1) * (d ^ 2 + (rvmActiveSet α v t).card * d) ∧
    rvmRoundArithOps α v t ≤ 28 * (t + 1) * d ^ 2 + 28 * (t + 1) ^ 2 * d := by
  have hb := lem_2_3b hd α hα v h_unit t
  have hc := (rem_cost_counts_core hd α hα v h_unit).1 t
  have h_raw := (rvmFastState_equiv hd α hα v h_unit t).2.2.2.2.2.2.2.2
  have h_first : rvmRoundArithOps α v t ≤
      28 * (rvmRevokedCount α v t + 1) * (d ^ 2 + (rvmActiveSet α v t).card * d) :=
    le_trans h_raw (round_ops_bound_aux hd hb.2.1)
  have hk_le : rvmRevokedCount α v t ≤ t := le_trans hb.2.2.1 hc
  refine ⟨h_first, ?_⟩
  have h_k1 : 28 * (rvmRevokedCount α v t + 1) ≤ 28 * (t + 1) := by omega
  have h_c1 : d ^ 2 + (rvmActiveSet α v t).card * d ≤ d ^ 2 + t * d := by nlinarith
  have h_mul : 28 * (rvmRevokedCount α v t + 1) * (d ^ 2 + (rvmActiveSet α v t).card * d) ≤
      28 * (t + 1) * (d ^ 2 + t * d) := Nat.mul_le_mul h_k1 h_c1
  nlinarith

lemma rvmTotalArithOps_le {d : ℕ} (hd : 0 < d) (α : ℝ) (hα : 0 < α)
    (v : ℕ → (Fin d → ℝ)) (h_unit : ∀ k, dotProduct (v k) (v k) = 1) (T : ℕ) :
    rvmTotalArithOps α v T ≤ 34 * T * d ^ 2 + 36 * T ^ 2 * d := by
  have h_rem := rem_cost_counts_core hd α hα v h_unit
  have h_card : ∀ t ∈ Finset.range T, (rvmActiveSet α v t).card ≤ T := by
    intro t ht
    exact le_trans (h_rem.1 t) (le_of_lt (Finset.mem_range.mp ht))
  have h_round : ∀ t ∈ Finset.range T,
      rvmRoundArithOps α v t ≤
        rvmRoundPieces α v t * (6 * d ^ 2 + 18 * T * d) +
        rvmRevokedCount α v t * (10 * d ^ 2) + 12 * d ^ 2 := by
    intro t ht
    have h_raw := (rvmFastState_equiv hd α hα v h_unit t).2.2.2.2.2.2.2.2
    have h1 := pieceArithOps_le hd (rvmActiveSet α v t).card
    have h1' : pieceArithOps d (rvmActiveSet α v t).card ≤ 6 * d ^ 2 + 18 * T * d := by
      have hc := h_card t ht
      nlinarith
    have h2 := downdateArithOps_le hd
    have h3 := stretchArithOps_le hd
    have hm1 := Nat.mul_le_mul_left (rvmRoundPieces α v t) h1'
    have hm2 := Nat.mul_le_mul_left (rvmRevokedCount α v t) h2
    omega
  have h_sum := Finset.sum_le_sum h_round
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    Finset.sum_const, Finset.card_range, smul_eq_mul] at h_sum
  have h_pieces := h_rem.2.2.1 T
  have h_rev := h_rem.2.1 T
  have hp_mul : (∑ x ∈ Finset.range T, rvmRoundPieces α v x) * (6 * d ^ 2 + 18 * T * d) ≤
      (2 * T) * (6 * d ^ 2 + 18 * T * d) :=
    Nat.mul_le_mul_right _ h_pieces
  have hr_mul : (∑ x ∈ Finset.range T, rvmRevokedCount α v x) * (10 * d ^ 2) ≤
      T * (10 * d ^ 2) :=
    Nat.mul_le_mul_right _ h_rev
  rw [rvmTotalArithOps_eq_sum]
  nlinarith

lemma ramNormalizeDiff_eq {d : ℕ} (x_t x_hat_t : Fin d → ℝ) :
    (ramNormalizeDiff x_t x_hat_t).val =
      (Real.sqrt (dotProduct (x_t - x_hat_t) (x_t - x_hat_t)))⁻¹ • (x_t - x_hat_t) ∧
    (ramNormalizeDiff x_t x_hat_t).ops = 4 * d + 2 := by
  unfold ramNormalizeDiff
  dsimp [CostM.bind, ramSqrt, ramDiv]
  rw [ramVecSub_val, ramVecSub_ops, ramDot_val, ramDot_ops, ramVecSmul_val, ramVecSmul_ops, one_div]
  refine ⟨rfl, by omega⟩

lemma oiloRoundArithOps_eq {d : ℕ} (α : ℝ)
    (x x_hat u : ℕ → (Fin d → ℝ)) (t : ℕ) :
    oiloRoundArithOps α x x_hat u t =
      open Classical in
      if x t = x_hat t then 2 * d
      else oiloReductionArithOps d + rvmRoundArithOps α u (oiloGameIndex x x_hat t) := by
  classical
  unfold oiloRoundArithOps oiloReductionArithOps
  dsimp only []
  have h1 : (ramVecEq (rvmFastState α u (oiloGameIndex x x_hat t)).p 0).ops = d :=
    ramVecEq_ops _ _
  have h2 : (ramVecEq (x t) (x_hat t)).ops = d :=
    ramVecEq_ops _ _
  have h3 : (ramNormalizeDiff (x t) (x_hat t)).ops = 4 * d + 2 :=
    (ramNormalizeDiff_eq (x t) (x_hat t)).2
  have h_cmp : (ramVecEq (x t) (x_hat t)).val = true ↔ x t = x_hat t := by
    rw [ramVecEq_val]
  rw [h1, h2, h3]
  by_cases h_eq : x t = x_hat t
  · rw [if_pos (h_cmp.mpr h_eq), if_pos h_eq]; ring
  · have h_f : ¬ ((ramVecEq (x t) (x_hat t)).val = true) := fun h => h_eq (h_cmp.mp h)
    rw [if_neg h_f, if_neg h_eq]
    omega

lemma oiloGameIndex_le_self {d : ℕ} (x x_hat : ℕ → (Fin d → ℝ)) (t : ℕ) :
    oiloGameIndex x x_hat t ≤ t := by
  classical
  unfold oiloGameIndex
  calc ((Finset.range t).filter (fun s => x s ≠ x_hat s)).card
    _ ≤ (Finset.range t).card := Finset.card_filter_le _ _
    _ = t := Finset.card_range t

lemma oiloOps_le {d : ℕ} (hd : 0 < d) (α : ℝ) (hα : 0 < α)
    (x x_hat u : ℕ → (Fin d → ℝ)) (h_unit : ∀ k, dotProduct (u k) (u k) = 1) :
    (∀ t : ℕ,
      oiloRoundArithOps α x x_hat u t ≤ 36 * (t + 1) * d ^ 2 + 28 * (t + 1) ^ 2 * d) ∧
    (∀ T : ℕ,
      oiloTotalArithOps α x x_hat u T ≤ 42 * T * d ^ 2 + 36 * T ^ 2 * d) := by
  classical
  have h_red := oiloReductionArithOps_le hd
  constructor
  · intro t
    rw [oiloRoundArithOps_eq]
    split_ifs with h_eq
    · nlinarith
    · have hg_le : oiloGameIndex x x_hat t ≤ t := oiloGameIndex_le_self x x_hat t
      have h_rvm := (rvmRoundArithOps_le hd α hα u h_unit (oiloGameIndex x x_hat t)).2
      have h_g1 : 28 * (oiloGameIndex x x_hat t + 1) * d ^ 2 ≤ 28 * (t + 1) * d ^ 2 := by
        nlinarith
      have h_sq : (oiloGameIndex x x_hat t + 1) ^ 2 ≤ (t + 1) ^ 2 := by nlinarith
      have h_g2 : 28 * (oiloGameIndex x x_hat t + 1) ^ 2 * d ≤ 28 * (t + 1) ^ 2 * d := by
        nlinarith
      have h_red_t : oiloReductionArithOps d ≤ 8 * (t + 1) * d ^ 2 := by nlinarith
      have h_alg : 8 * (t + 1) * d ^ 2 + 28 * (t + 1) * d ^ 2 = 36 * (t + 1) * d ^ 2 := by ring
      omega
  · intro T
    have h_ind : ∀ k : ℕ,
        oiloTotalArithOps α x x_hat u k ≤
          8 * k * d ^ 2 + rvmTotalArithOps α u (oiloGameIndex x x_hat k) := by
      intro k
      induction k with
      | zero =>
        simp [oiloTotalArithOps, rvmTotalArithOps_eq_sum, oiloGameIndex]
      | succ k ih =>
        have h_tot_succ : oiloTotalArithOps α x x_hat u (k + 1) =
            oiloTotalArithOps α x x_hat u k + oiloRoundArithOps α x x_hat u k :=
          Finset.sum_range_succ _ k
        rw [h_tot_succ, oiloRoundArithOps_eq]
        have h_alg : 8 * (k + 1) * d ^ 2 = 8 * k * d ^ 2 + 8 * d ^ 2 := by ring
        split_ifs with h_eq
        · rw [oiloGameIndex_succ_eq x x_hat k h_eq]
          have hd_le : 2 * d ≤ 8 * d ^ 2 := by nlinarith
          omega
        · rw [oiloGameIndex_succ_ne x x_hat k h_eq]
          have h_rvm_succ : rvmTotalArithOps α u (oiloGameIndex x x_hat k + 1) =
              rvmTotalArithOps α u (oiloGameIndex x x_hat k) +
                rvmRoundArithOps α u (oiloGameIndex x x_hat k) := by
            rw [rvmTotalArithOps_eq_sum, rvmTotalArithOps_eq_sum, Finset.sum_range_succ]
          rw [h_rvm_succ]
          omega
    have h1 := h_ind T
    have hg_le : oiloGameIndex x x_hat T ≤ T := oiloGameIndex_le_self x x_hat T
    have h_rvm := rvmTotalArithOps_le hd α hα u h_unit (oiloGameIndex x x_hat T)
    have h_sq : (oiloGameIndex x x_hat T) ^ 2 ≤ T ^ 2 := by nlinarith
    have h_t1 : 34 * oiloGameIndex x x_hat T * d ^ 2 ≤ 34 * T * d ^ 2 := by nlinarith
    have h_t2 : 36 * (oiloGameIndex x x_hat T) ^ 2 * d ≤ 36 * T ^ 2 * d := by nlinarith
    have : 8 * T * d ^ 2 + 34 * T * d ^ 2 = 42 * T * d ^ 2 := by ring
    omega

lemma rvmSkipOps_le {d : ℕ} (hd : 0 < d) (R : ℝ) (hR : 0 < R)
    (w_star : Fin d → ℝ) (hw : dotProduct w_star w_star ≤ R ^ 2)
    (v : ℕ → (Fin d → ℝ)) (h_unit : ∀ k, dotProduct (v k) (v k) = 1)
    (α : ℝ) (hα_eq : α = R / (3 * Real.sqrt (d : ℝ))) :
    let B : ℕ → ℝ := fun t =>
      (d : ℝ) * Real.log (1 + ((t + 1 : ℝ) ^ 5) / (8 * (d : ℝ))) / Real.log (9 / 8 : ℝ)
    (∀ t : ℕ,
      rvmSkipRoundArithOps α v t ≤
        rvmSkipRoundPieces α v t * pieceArithOps d (rvmSkipActiveSet α v t).card +
        rvmSkipRevokedCount α v t * downdateArithOps d +
        skipStretchArithOps d ∧
      rvmSkipRoundArithOps α v t ≤
        33 * ((rvmSkipActiveSet α v t).card + 1) * (d ^ 2 + (rvmSkipActiveSet α v t).card * d) ∧
      (rvmSkipRoundArithOps α v t : ℝ) ≤
        33 * (B t + 1) * ((d : ℝ) ^ 2 + B t * (d : ℝ))) ∧
    (∀ T : ℕ,
      (rvmSkipTotalArithOps α v T : ℝ) ≤
        39 * (T : ℝ) * (d : ℝ) ^ 2 + 36 * (T : ℝ) * B T * (d : ℝ)) := by
  intro B
  have hα : 0 < α := by rw [hα_eq]; positivity
  have h_rem := rem_cost_counts_core hd α hα v h_unit
  have h_prop := (prop_3_3_core hd R hR w_star hw v h_unit α hα_eq).2
  have hB_mono : ∀ {t T : ℕ}, t ≤ T → B t ≤ B T := by
    intro t T htT
    dsimp [B]
    have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
    have hlog_pos : 0 < Real.log (9 / 8 : ℝ) := Real.log_pos (by norm_num)
    apply div_le_div_of_nonneg_right _ (le_of_lt hlog_pos)
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hd_pos)
    apply Real.log_le_log (by positivity)
    have ht_le : (t + 1 : ℝ) ≤ (T + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ htT
    have h_pow : (t + 1 : ℝ) ^ 5 ≤ (T + 1 : ℝ) ^ 5 :=
      pow_le_pow_left₀ (by positivity) ht_le 5
    have : ((t + 1 : ℝ) ^ 5) / (8 * (d : ℝ)) ≤ ((T + 1 : ℝ) ^ 5) / (8 * (d : ℝ)) :=
      div_le_div_of_nonneg_right h_pow (by positivity)
    linarith
  constructor
  · intro t
    have h_sk := h_rem.2.2.2.1 t
    have h_raw := (rvmSkipFastState_equiv α v h_unit t).2.2.2.2.2.2.2.2
    have h_first : rvmSkipRoundArithOps α v t ≤
        33 * ((rvmSkipActiveSet α v t).card + 1) * (d ^ 2 + (rvmSkipActiveSet α v t).card * d) := by
      have h1 : rvmSkipRoundArithOps α v t ≤
          33 * (rvmSkipRevokedCount α v t + 1) * (d ^ 2 + (rvmSkipActiveSet α v t).card * d) :=
        le_trans h_raw (skip_round_ops_bound_aux hd h_sk.2.2.1)
      have hk : rvmSkipRevokedCount α v t ≤ (rvmSkipActiveSet α v t).card := h_sk.2.2.2
      have h_k1 : 33 * (rvmSkipRevokedCount α v t + 1) ≤ 33 * ((rvmSkipActiveSet α v t).card + 1) := by
        omega
      exact le_trans h1 (Nat.mul_le_mul_right _ h_k1)
    refine ⟨h_raw, h_first, ?_⟩
    have h_cast : (rvmSkipRoundArithOps α v t : ℝ) ≤
        33 * (((rvmSkipActiveSet α v t).card : ℝ) + 1) *
          ((d : ℝ) ^ 2 + ((rvmSkipActiveSet α v t).card : ℝ) * (d : ℝ)) := by
      exact_mod_cast h_first
    have h_card_B : ((rvmSkipActiveSet α v t).card : ℝ) ≤ B t := (h_prop t).2.2
    have h_card_nn : (0 : ℝ) ≤ ((rvmSkipActiveSet α v t).card : ℝ) := Nat.cast_nonneg _
    have hd_nn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
    have h_f1 : 33 * (((rvmSkipActiveSet α v t).card : ℝ) + 1) ≤ 33 * (B t + 1) := by linarith
    have h_f2 : (d : ℝ) ^ 2 + ((rvmSkipActiveSet α v t).card : ℝ) * (d : ℝ) ≤
        (d : ℝ) ^ 2 + B t * (d : ℝ) := by nlinarith
    exact le_trans h_cast (mul_le_mul h_f1 h_f2 (by positivity) (by linarith))
  · intro T
    have h_round : ∀ t ∈ Finset.range T,
        (rvmSkipRoundArithOps α v t : ℝ) ≤
           (rvmSkipRoundPieces α v t : ℝ) * (6 * (d : ℝ) ^ 2 + 18 * B T * (d : ℝ)) +
          (rvmSkipRevokedCount α v t : ℝ) * (10 * (d : ℝ) ^ 2) + 17 * (d : ℝ) ^ 2 := by
      intro t ht
      have h_raw : (rvmSkipRoundArithOps α v t : ℝ) ≤
          (rvmSkipRoundPieces α v t : ℝ) * (pieceArithOps d (rvmSkipActiveSet α v t).card : ℝ) +
          (rvmSkipRevokedCount α v t : ℝ) * (downdateArithOps d : ℝ) +
          (skipStretchArithOps d : ℝ) := by
        exact_mod_cast (rvmSkipFastState_equiv α v h_unit t).2.2.2.2.2.2.2.2
      have h1 : (pieceArithOps d (rvmSkipActiveSet α v t).card : ℝ) ≤
          6 * (d : ℝ) ^ 2 + 18 * ((rvmSkipActiveSet α v t).card : ℝ) * (d : ℝ) := by
        exact_mod_cast pieceArithOps_le hd (rvmSkipActiveSet α v t).card
      have h_card_BT : ((rvmSkipActiveSet α v t).card : ℝ) ≤ B T :=
        le_trans (h_prop t).2.2 (hB_mono (le_of_lt (Finset.mem_range.mp ht)))
      have hd_nn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
      have h1' : (pieceArithOps d (rvmSkipActiveSet α v t).card : ℝ) ≤
          6 * (d : ℝ) ^ 2 + 18 * B T * (d : ℝ) := by nlinarith
      have h2 : (downdateArithOps d : ℝ) ≤ 10 * (d : ℝ) ^ 2 := by
        exact_mod_cast downdateArithOps_le hd
      have h3 : (skipStretchArithOps d : ℝ) ≤ 17 * (d : ℝ) ^ 2 := by
        exact_mod_cast skipStretchArithOps_le hd
      have hp_nn : (0 : ℝ) ≤ (rvmSkipRoundPieces α v t : ℝ) := Nat.cast_nonneg _
      have hk_nn : (0 : ℝ) ≤ (rvmSkipRevokedCount α v t : ℝ) := Nat.cast_nonneg _
      nlinarith
    have h_sum := Finset.sum_le_sum h_round
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h_sum
    have h_pieces : (∑ t ∈ Finset.range T, (rvmSkipRoundPieces α v t : ℝ)) ≤ 2 * (T : ℝ) := by
      exact_mod_cast h_rem.2.2.2.2.2.1 T
    have h_rev : (∑ t ∈ Finset.range T, (rvmSkipRevokedCount α v t : ℝ)) ≤ (T : ℝ) := by
      exact_mod_cast h_rem.2.2.2.2.1 T
    have hB_nn : 0 ≤ B T :=
      le_trans (Nat.cast_nonneg _) (h_prop T).2.2
    have hd_nn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
    have hp_mul : (∑ i ∈ Finset.range T, (rvmSkipRoundPieces α v i : ℝ)) *
        (6 * (d : ℝ) ^ 2 + 18 * B T * (d : ℝ)) ≤
        (2 * (T : ℝ)) * (6 * (d : ℝ) ^ 2 + 18 * B T * (d : ℝ)) :=
      mul_le_mul_of_nonneg_right h_pieces (by positivity)
    have hr_mul : (∑ i ∈ Finset.range T, (rvmSkipRevokedCount α v i : ℝ)) * (10 * (d : ℝ) ^ 2) ≤
        (T : ℝ) * (10 * (d : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right h_rev (by positivity)
    have h_alg : (2 * (T : ℝ)) * (6 * (d : ℝ) ^ 2 + 18 * B T * (d : ℝ)) +
        (T : ℝ) * (10 * (d : ℝ) ^ 2) + (T : ℝ) * (17 * (d : ℝ) ^ 2) =
        39 * (T : ℝ) * (d : ℝ) ^ 2 + 36 * (T : ℝ) * B T * (d : ℝ) := by ring
    have hTd_nn : 0 ≤ (T : ℝ) * (d : ℝ) ^ 2 := by positivity
    have h_tot_eq : (rvmSkipTotalArithOps α v T : ℝ) =
        ∑ t ∈ Finset.range T, (rvmSkipRoundArithOps α v t : ℝ) := by
      rw [rvmSkipTotalArithOps_eq_sum]
      push_cast
      rfl
    rw [h_tot_eq]
    linarith

/-- **Remark 2.4 (Combinatorial piece/revocation counts, Sherman–Morrison implementation, and per-round cost)** -/
theorem rem_cost_counts : Remark2_4_CombinatorialCounts := by
  intro d hd α hα v h_unit
  have hc := rem_cost_counts_core hd α hα v h_unit
  refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.1,
    hc.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2, ?_⟩
  intro t
  have hf := rvmFastState_equiv hd α hα v h_unit t
  have hop := (rvmRoundArithOps_le hd α hα v h_unit t).1
  exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2.1,
    hf.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.1, rvmTotalArithOps_eq_sum α v t,
    hf.2.2.2.2.2.2.2.2, hop⟩

/-- **Proposition 3.3 (Skipping small stretches)** -/
theorem prop_3_3 : Proposition3_3_SkippingSmallStretches := by
  intro d hd R hR w_star hw v h_unit α hα_eq B
  have h_core := prop_3_3_core hd R hR w_star hw v h_unit α hα_eq
  have h_ops := rvmSkipOps_le hd R hR w_star hw v h_unit α hα_eq
  refine ⟨h_core.1, ?_, ?_⟩
  · intro t
    have hf_t := rvmSkipFastState_equiv α v h_unit t
    have hc_t := h_core.2 t
    have hop_t := h_ops.1 t
    exact ⟨hf_t.1, hf_t.2.1, hf_t.2.2.1, hf_t.2.2.2.1, hf_t.2.2.2.2.1,
      hf_t.2.2.2.2.2.1, hf_t.2.2.2.2.2.2.1, hf_t.2.2.2.2.2.2.2.1,
      hc_t.1, hc_t.2.1, hc_t.2.2, hop_t.1, hop_t.2.1, hop_t.2.2⟩
  · intro T
    exact ⟨rvmSkipTotalArithOps_eq_sum α v T, h_ops.2 T⟩

lemma thm_2_1 :
    Equation6_Ledger →
    Lemma2_6_StretchLifetime →
    Lemma2_7_SurvivingStretches →
    Theorem2_1_RVMRegretBound := by
  intro h_eq6 h26 h27 d hd R hR w_star hw v h_unit α hα_eq T hr_nonneg
  have h_core := thm_2_1_core h_eq6 h26 h27 hd R hR w_star hw v h_unit α hα_eq T hr_nonneg
  have hα_pos : 0 < α := by rw [hα_eq]; positivity
  refine ⟨h_core.1, h_core.2.1, h_core.2.2, ?_, ?_⟩
  · intro t
    exact (rvmRoundArithOps_le hd α hα_pos v h_unit t).2
  · exact rvmTotalArithOps_le hd α hα_pos v h_unit T

/-! ### Compact Nonempty Maximizers & Closed-Loop OILO Learner (Corollary 2.2) -/

lemma continuous_dotProduct_const {d : ℕ} (w : Fin d → ℝ) :
    Continuous (fun y : Fin d → ℝ => dotProduct w y) := by
  classical
  unfold dotProduct
  exact continuous_finset_sum _ (fun i _ => continuous_const.mul (continuous_apply i))

lemma linearMaximizer_spec {d : ℕ} (w : Fin d → ℝ) (S : Set (Fin d → ℝ))
    (h_compact : IsCompact S) (h_nonempty : S.Nonempty) :
    linearMaximizer w S ∈ S ∧ ∀ y ∈ S, dotProduct w y ≤ dotProduct w (linearMaximizer w S) := by
  classical
  have h_cont : ContinuousOn (fun y : Fin d → ℝ => dotProduct w y) S :=
    (continuous_dotProduct_const w).continuousOn
  obtain ⟨x, hxS, hx_max⟩ := h_compact.exists_isMaxOn h_nonempty h_cont
  have h_ex : ∃ x ∈ S, ∀ y ∈ S, dotProduct w y ≤ dotProduct w x :=
    ⟨x, hxS, fun y hy => hx_max hy⟩
  unfold linearMaximizer
  rw [dif_pos h_ex]
  exact Classical.choose_spec h_ex

lemma dotProduct_self_pos_of_ne_zero {d : ℕ} {v : Fin d → ℝ} (hv : v ≠ 0) :
    0 < dotProduct v v := by
  classical
  have h_ex : ∃ i, v i ≠ 0 := Function.ne_iff.mp hv
  rcases h_ex with ⟨i, hi⟩
  have h_nonneg : ∀ j ∈ (Finset.univ : Finset (Fin d)), 0 ≤ v j * v j :=
    fun j _ => mul_self_nonneg (v j)
  have h_pos : 0 < v i * v i := mul_self_pos.mpr hi
  exact Finset.sum_pos' h_nonneg ⟨i, Finset.mem_univ i, h_pos⟩

lemma dotProduct_normalize_self {d : ℕ} {v : Fin d → ℝ} (hv : v ≠ 0) :
    dotProduct ((Real.sqrt (dotProduct v v))⁻¹ • v) ((Real.sqrt (dotProduct v v))⁻¹ • v) = 1 := by
  have hpos : 0 < dotProduct v v := dotProduct_self_pos_of_ne_zero hv
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  calc (Real.sqrt (dotProduct v v))⁻¹ * ((Real.sqrt (dotProduct v v))⁻¹ * dotProduct v v)
    _ = ((Real.sqrt (dotProduct v v)) ^ 2)⁻¹ * dotProduct v v := by ring
    _ = (dotProduct v v)⁻¹ * dotProduct v v := by rw [Real.sq_sqrt (le_of_lt hpos)]
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)

lemma oiloLearnerState_succ_pos {d : ℕ} (α : ℝ) (e : Fin d → ℝ)
    (X : ℕ → Set (Fin d → ℝ)) (x : ℕ → (Fin d → ℝ)) (t : ℕ)
    (h_eq : x t = oiloLearnerAction α e X x t) :
    oiloLearnerState α e X x (t + 1) =
      let st := oiloLearnerState α e X x t
      let r_ops := (ramVecEq st.fast.p 0).ops + (ramVecEq (x t) (oiloLearnerAction α e X x t)).ops
      { g := st.g
        u := st.u
        fast := st.fast
        roundOps := r_ops
        totalOps := st.totalOps + r_ops } := by
  have h_cmp : (ramVecEq (x t) (oiloLearnerAction α e X x t)).val = true :=
    (ramVecEq_val _ _).mpr h_eq
  dsimp only [oiloLearnerState]
  change (if (ramVecEq (x t) (oiloLearnerAction α e X x t)).val = true then _ else _) = _
  rw [if_pos h_cmp]
  rfl

lemma oiloLearnerState_succ_neg {d : ℕ} (α : ℝ) (e : Fin d → ℝ)
    (X : ℕ → Set (Fin d → ℝ)) (x : ℕ → (Fin d → ℝ)) (t : ℕ)
    (h_ne : x t ≠ oiloLearnerAction α e X x t) :
    oiloLearnerState α e X x (t + 1) =
      let st := oiloLearnerState α e X x t
      let norm_step := ramNormalizeDiff (x t) (oiloLearnerAction α e X x t)
      let u_next := Function.update st.u st.g norm_step.val
      let fast_next := rvmFastStep α u_next st.g st.fast
      let r_ops := (ramVecEq st.fast.p 0).ops +
        (ramVecEq (x t) (oiloLearnerAction α e X x t)).ops +
        norm_step.ops + fast_next.roundOps
      { g := st.g + 1
        u := u_next
        fast := fast_next
        roundOps := r_ops
        totalOps := st.totalOps + r_ops } := by
  have h_cmp : ¬ ((ramVecEq (x t) (oiloLearnerAction α e X x t)).val = true) :=
    fun h => h_ne ((ramVecEq_val _ _).mp h)
  dsimp only [oiloLearnerState]
  change (if (ramVecEq (x t) (oiloLearnerAction α e X x t)).val = true then _ else _) = _
  rw [if_neg h_cmp]
  rfl

lemma oiloLearnerGameIndex_succ {d : ℕ} (α : ℝ) (e : Fin d → ℝ)
    (X : ℕ → Set (Fin d → ℝ)) (x : ℕ → (Fin d → ℝ)) (t : ℕ) :
    oiloLearnerGameIndex α e X x (t + 1) =
      open Classical in
      if x t = oiloLearnerAction α e X x t then
        oiloLearnerGameIndex α e X x t
      else
        oiloLearnerGameIndex α e X x t + 1 := by
  classical
  unfold oiloLearnerGameIndex
  by_cases h_eq : x t = oiloLearnerAction α e X x t
  · rw [oiloLearnerState_succ_pos α e X x t h_eq, if_pos h_eq]
  · rw [oiloLearnerState_succ_neg α e X x t h_eq, if_neg h_eq]

lemma oiloLearnerDirections_succ {d : ℕ} (α : ℝ) (e : Fin d → ℝ)
    (X : ℕ → Set (Fin d → ℝ)) (x : ℕ → (Fin d → ℝ)) (t : ℕ) :
    oiloLearnerDirections α e X x (t + 1) =
      open Classical in
      if x t = oiloLearnerAction α e X x t then
        oiloLearnerDirections α e X x t
      else
        Function.update (oiloLearnerDirections α e X x t) (oiloLearnerGameIndex α e X x t)
          ((Real.sqrt (dotProduct (x t - oiloLearnerAction α e X x t)
            (x t - oiloLearnerAction α e X x t)))⁻¹ •
              (x t - oiloLearnerAction α e X x t)) := by
  classical
  unfold oiloLearnerDirections oiloLearnerGameIndex
  by_cases h_eq : x t = oiloLearnerAction α e X x t
  · rw [oiloLearnerState_succ_pos α e X x t h_eq, if_pos h_eq]
  · rw [oiloLearnerState_succ_neg α e X x t h_eq, if_neg h_eq]
    dsimp only
    rw [(ramNormalizeDiff_eq (x t) (oiloLearnerAction α e X x t)).1]

lemma oiloLearnerFastState_succ {d : ℕ} (α : ℝ) (e : Fin d → ℝ)
    (X : ℕ → Set (Fin d → ℝ)) (x : ℕ → (Fin d → ℝ)) (t : ℕ) :
    oiloLearnerFastState α e X x (t + 1) =
      open Classical in
      if x t = oiloLearnerAction α e X x t then
        oiloLearnerFastState α e X x t
      else
        rvmFastStep α (oiloLearnerDirections α e X x (t + 1))
          (oiloLearnerGameIndex α e X x t) (oiloLearnerFastState α e X x t) := by
  classical
  by_cases h_eq : x t = oiloLearnerAction α e X x t
  · unfold oiloLearnerFastState
    rw [oiloLearnerState_succ_pos α e X x t h_eq, if_pos h_eq]
  · rw [if_neg h_eq]
    have hu_succ : oiloLearnerDirections α e X x (t + 1) =
        Function.update (oiloLearnerState α e X x t).u (oiloLearnerState α e X x t).g
          (ramNormalizeDiff (x t) (oiloLearnerAction α e X x t)).val := by
      unfold oiloLearnerDirections
      rw [oiloLearnerState_succ_neg α e X x t h_eq]
    unfold oiloLearnerFastState oiloLearnerGameIndex
    rw [oiloLearnerState_succ_neg α e X x t h_eq, hu_succ]

lemma oiloLearnerFastState_eq {d : ℕ} (α : ℝ) (e : Fin d → ℝ)
    (X : ℕ → Set (Fin d → ℝ)) (x : ℕ → (Fin d → ℝ)) (t : ℕ) :
    oiloLearnerFastState α e X x t =
      rvmFastState α (oiloLearnerDirections α e X x t) (oiloLearnerGameIndex α e X x t) := by
  classical
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [oiloLearnerFastState_succ, oiloLearnerGameIndex_succ]
    by_cases h_eq : x t = oiloLearnerAction α e X x t
    · rw [if_pos h_eq, if_pos h_eq, ih]
      have hu_eq : oiloLearnerDirections α e X x (t + 1) = oiloLearnerDirections α e X x t := by
        rw [oiloLearnerDirections_succ, if_pos h_eq]
      rw [hu_eq]
    · rw [if_neg h_eq, if_neg h_eq, ih]
      have h_pref : ∀ r < oiloLearnerGameIndex α e X x t,
          oiloLearnerDirections α e X x t r = oiloLearnerDirections α e X x (t + 1) r := by
        intro r hr
        rw [oiloLearnerDirections_succ, if_neg h_eq, Function.update_of_ne (ne_of_lt hr)]
      have h_caus := rvmFastState_causal α
        (oiloLearnerDirections α e X x t) (oiloLearnerDirections α e X x (t + 1))
        (oiloLearnerGameIndex α e X x t) h_pref
      rw [h_caus]
      rfl

lemma oiloLearnerState_causal {d : ℕ} (α : ℝ) (e : Fin d → ℝ)
    (X X' : ℕ → Set (Fin d → ℝ)) (x x' : ℕ → (Fin d → ℝ)) (t : ℕ)
    (h : ∀ s < t, X s = X' s ∧ x s = x' s) :
    oiloLearnerState α e X x t = oiloLearnerState α e X' x' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih' := ih (fun s hs => h s (Nat.lt_succ_of_lt hs))
    obtain ⟨hXt, hxt⟩ := h t (Nat.lt_succ_self t)
    dsimp only [oiloLearnerState]
    rw [ih', hXt, hxt]

lemma oiloLearnerGameIndex_eq {d : ℕ} (α : ℝ) (e : Fin d → ℝ)
    (X : ℕ → Set (Fin d → ℝ)) (x : ℕ → (Fin d → ℝ)) (t : ℕ) :
    oiloLearnerGameIndex α e X x t = oiloGameIndex x (oiloLearnerAction α e X x) t := by
  classical
  induction t with
  | zero =>
    unfold oiloLearnerGameIndex oiloLearnerState oiloGameIndex
    simp
  | succ t ih =>
    rw [oiloLearnerGameIndex_succ]
    unfold oiloGameIndex at ih ⊢
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with h_eq h_ne
    · exfalso; exact h_ne h_eq
    · exact ih
    · rw [Finset.card_insert_of_notMem (by simp), ih]

lemma oiloLearnerDirections_unit {d : ℕ} (α : ℝ) {e : Fin d → ℝ} (he : e ≠ 0)
    (X : ℕ → Set (Fin d → ℝ)) (x : ℕ → (Fin d → ℝ)) (t k : ℕ) :
    dotProduct (oiloLearnerDirections α e X x t k) (oiloLearnerDirections α e X x t k) = 1 := by
  classical
  induction t generalizing k with
  | zero =>
    unfold oiloLearnerDirections oiloLearnerState
    exact dotProduct_normalize_self he
  | succ t ih =>
    rw [oiloLearnerDirections_succ]
    split_ifs with h_eq
    · exact ih k
    · by_cases hk : k = oiloLearnerGameIndex α e X x t
      · subst hk
        rw [Function.update_self]
        exact dotProduct_normalize_self (sub_ne_zero.mpr h_eq)
      · rw [Function.update_of_ne hk]
        exact ih k

lemma oiloLearnerDirections_prefix {d : ℕ} (α : ℝ) (e : Fin d → ℝ)
    (X : ℕ → Set (Fin d → ℝ)) (x : ℕ → (Fin d → ℝ)) {t T : ℕ} (htT : t ≤ T)
    {k : ℕ} (hk : k < oiloLearnerGameIndex α e X x t) :
    oiloLearnerDirections α e X x T k = oiloLearnerDirections α e X x t k := by
  classical
  induction T with
  | zero =>
    have ht0 : t = 0 := Nat.eq_zero_of_le_zero htT
    subst ht0
    rfl
  | succ T ih =>
    rcases Nat.of_le_succ htT with h_le | rfl
    · have h_mono : oiloLearnerGameIndex α e X x t ≤ oiloLearnerGameIndex α e X x T := by
        rw [oiloLearnerGameIndex_eq, oiloLearnerGameIndex_eq]
        exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono h_le))
      have hkT : k < oiloLearnerGameIndex α e X x T := lt_of_lt_of_le hk h_mono
      have h_step : oiloLearnerDirections α e X x (T + 1) k = oiloLearnerDirections α e X x T k := by
        rw [oiloLearnerDirections_succ]
        split_ifs with h_eq
        · rfl
        · rw [Function.update_of_ne (ne_of_lt hkT)]
      rw [h_step, ih h_le]
    · rfl

lemma oiloLearnerDirections_at_non_tie {d : ℕ} (α : ℝ) (e : Fin d → ℝ)
    (X : ℕ → Set (Fin d → ℝ)) (x : ℕ → (Fin d → ℝ)) {t T : ℕ} (htT : t < T)
    (hne : x t ≠ oiloLearnerAction α e X x t) :
    oiloLearnerDirections α e X x T (oiloLearnerGameIndex α e X x t) =
      (Real.sqrt (dotProduct (x t - oiloLearnerAction α e X x t)
        (x t - oiloLearnerAction α e X x t)))⁻¹ • (x t - oiloLearnerAction α e X x t) := by
  classical
  have h_at_succ :
      oiloLearnerDirections α e X x (t + 1) (oiloLearnerGameIndex α e X x t) =
        (Real.sqrt (dotProduct (x t - oiloLearnerAction α e X x t)
           (x t - oiloLearnerAction α e X x t)))⁻¹ • (x t - oiloLearnerAction α e X x t) := by
    rw [oiloLearnerDirections_succ, if_neg hne, Function.update_self]
  have h_idx_succ :
      oiloLearnerGameIndex α e X x (t + 1) = oiloLearnerGameIndex α e X x t + 1 := by
    rw [oiloLearnerGameIndex_succ, if_neg hne]
  have hk : oiloLearnerGameIndex α e X x t < oiloLearnerGameIndex α e X x (t + 1) := by
    omega
  rw [oiloLearnerDirections_prefix α e X x htT hk, h_at_succ]

lemma oiloLearnerTotalArithOps_eq_sum {d : ℕ} (α : ℝ) (e : Fin d → ℝ)
    (X : ℕ → Set (Fin d → ℝ)) (x : ℕ → (Fin d → ℝ)) (T : ℕ) :
    oiloLearnerTotalArithOps α e X x T =
      ∑ t ∈ Finset.range T, oiloLearnerRoundArithOps α e X x t := by
  classical
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Finset.sum_range_succ, ← ih]
    unfold oiloLearnerTotalArithOps oiloLearnerRoundArithOps
    by_cases h_eq : x T = oiloLearnerAction α e X x T
    · rw [oiloLearnerState_succ_pos α e X x T h_eq]
    · rw [oiloLearnerState_succ_neg α e X x T h_eq]

lemma oiloLearnerRoundArithOps_def {d : ℕ} (α : ℝ) (e : Fin d → ℝ)
    (X : ℕ → Set (Fin d → ℝ)) (x : ℕ → (Fin d → ℝ)) (t : ℕ) :
    oiloLearnerRoundArithOps α e X x t =
      open Classical in
      if x t = oiloLearnerAction α e X x t then 2 * d
      else
        oiloReductionArithOps d +
          rvmRoundArithOps α (oiloLearnerDirections α e X x (t + 1))
            (oiloLearnerGameIndex α e X x t) := by
  classical
  have h1 : (ramVecEq (oiloLearnerState α e X x t).fast.p 0).ops = d := ramVecEq_ops _ _
  have h2 : (ramVecEq (x t) (oiloLearnerAction α e X x t)).ops = d := ramVecEq_ops _ _
  have h3 : (ramNormalizeDiff (x t) (oiloLearnerAction α e X x t)).ops = 4 * d + 2 :=
    (ramNormalizeDiff_eq _ _).2
  by_cases h_eq : x t = oiloLearnerAction α e X x t
  · unfold oiloLearnerRoundArithOps
    rw [oiloLearnerState_succ_pos α e X x t h_eq, if_pos h_eq]
    dsimp only
    rw [h1, h2]
    omega
  · rw [if_neg h_eq]
    have hu_succ : oiloLearnerDirections α e X x (t + 1) =
        Function.update (oiloLearnerState α e X x t).u (oiloLearnerState α e X x t).g
          (ramNormalizeDiff (x t) (oiloLearnerAction α e X x t)).val := by
      unfold oiloLearnerDirections
      rw [oiloLearnerState_succ_neg α e X x t h_eq]
    unfold oiloLearnerRoundArithOps oiloReductionArithOps
    rw [oiloLearnerState_succ_neg α e X x t h_eq]
    dsimp only
    rw [h1, h2, h3, ← hu_succ]
    change d + d + (4 * d + 2) +
      (rvmFastStep α (oiloLearnerDirections α e X x (t + 1))
        (oiloLearnerGameIndex α e X x t) (oiloLearnerFastState α e X x t)).roundOps = _
    rw [oiloLearnerFastState_eq]
    have h_pref : ∀ r < oiloLearnerGameIndex α e X x t,
        oiloLearnerDirections α e X x t r = oiloLearnerDirections α e X x (t + 1) r := by
      intro r hr
      rw [oiloLearnerDirections_succ, if_neg h_eq, Function.update_of_ne (ne_of_lt hr)]
    have h_caus := rvmFastState_causal α
      (oiloLearnerDirections α e X x t) (oiloLearnerDirections α e X x (t + 1))
      (oiloLearnerGameIndex α e X x t) h_pref
    rw [h_caus]
    change d + d + (4 * d + 2) + rvmRoundArithOps α (oiloLearnerDirections α e X x (t + 1))
      (oiloLearnerGameIndex α e X x t) = _
    omega

lemma oiloLearnerRoundArithOps_eq_horizon {d : ℕ} (α : ℝ) (e : Fin d → ℝ)
    (X : ℕ → Set (Fin d → ℝ)) (x : ℕ → (Fin d → ℝ)) {t T : ℕ} (htT : t < T) :
    oiloLearnerRoundArithOps α e X x t =
      oiloRoundArithOps α x (oiloLearnerAction α e X x) (oiloLearnerDirections α e X x T) t := by
  classical
  rw [oiloLearnerRoundArithOps_def, oiloRoundArithOps_eq]
  by_cases h_eq : x t = oiloLearnerAction α e X x t
  · rw [if_pos h_eq, if_pos h_eq]
  · rw [if_neg h_eq, if_neg h_eq]
    apply congrArg (oiloReductionArithOps d + ·)
    rw [← oiloLearnerGameIndex_eq]
    have h_idx_succ : oiloLearnerGameIndex α e X x (t + 1) = oiloLearnerGameIndex α e X x t + 1 := by
      rw [oiloLearnerGameIndex_succ, if_neg h_eq]
    have h_pref : ∀ r < oiloLearnerGameIndex α e X x t + 1,
        oiloLearnerDirections α e X x (t + 1) r = oiloLearnerDirections α e X x T r := by
      intro r hr
      rw [← h_idx_succ] at hr
      exact (oiloLearnerDirections_prefix α e X x htT hr).symm
    exact congrArg RVMFastState.roundOps (rvmFastState_causal α
      (oiloLearnerDirections α e X x (t + 1)) (oiloLearnerDirections α e X x T)
      (oiloLearnerGameIndex α e X x t + 1) h_pref)

lemma oiloLearnerTotalArithOps_eq_horizon {d : ℕ} (α : ℝ) (e : Fin d → ℝ)
    (X : ℕ → Set (Fin d → ℝ)) (x : ℕ → (Fin d → ℝ)) (T : ℕ) :
    oiloLearnerTotalArithOps α e X x T =
      oiloTotalArithOps α x (oiloLearnerAction α e X x) (oiloLearnerDirections α e X x T) T := by
  rw [oiloLearnerTotalArithOps_eq_sum]
  unfold oiloTotalArithOps
  refine Finset.sum_congr rfl (fun t ht => ?_)
  exact oiloLearnerRoundArithOps_eq_horizon α e X x (Finset.mem_range.mp ht)

lemma oiloLearnerFastState_eq_horizon {d : ℕ} (α : ℝ) (e : Fin d → ℝ)
    (X : ℕ → Set (Fin d → ℝ)) (x : ℕ → (Fin d → ℝ)) {t T : ℕ} (htT : t ≤ T) :
    oiloLearnerFastState α e X x t =
      rvmFastState α (oiloLearnerDirections α e X x T)
        (oiloGameIndex x (oiloLearnerAction α e X x) t) := by
  rw [oiloLearnerFastState_eq, ← oiloLearnerGameIndex_eq]
  exact rvmFastState_causal α (oiloLearnerDirections α e X x t)
    (oiloLearnerDirections α e X x T) (oiloLearnerGameIndex α e X x t)
    (fun k hk => (oiloLearnerDirections_prefix α e X x htT hk).symm)

lemma oiloLearnerQuery_eq_horizon {d : ℕ} (hd : 0 < d) (α : ℝ) (hα : 0 < α)
    {e : Fin d → ℝ} (he : e ≠ 0)
    (X : ℕ → Set (Fin d → ℝ)) (x : ℕ → (Fin d → ℝ)) {t T : ℕ} (htT : t ≤ T) :
    oiloLearnerQuery α e X x t =
      rvmQuery α (oiloLearnerDirections α e X x T) (oiloGameIndex x (oiloLearnerAction α e X x) t) := by
  unfold oiloLearnerQuery
  change (oiloLearnerFastState α e X x t).p = _
  rw [oiloLearnerFastState_eq_horizon α e X x htT, ← oiloLearnerGameIndex_eq]
  exact (rvmFastState_equiv hd α hα (oiloLearnerDirections α e X x T)
    (oiloLearnerDirections_unit α he X x T) (oiloLearnerGameIndex α e X x t)).1

lemma oiloLearnerHypothesis_eq_horizon {d : ℕ} (hd : 0 < d) (α : ℝ) (hα : 0 < α)
    {e : Fin d → ℝ} (he : e ≠ 0)
    (X : ℕ → Set (Fin d → ℝ)) (x : ℕ → (Fin d → ℝ)) {t T : ℕ} (htT : t ≤ T) :
    oiloLearnerHypothesis α e X x t =
      oiloHypothesis α e x (oiloLearnerAction α e X x) (oiloLearnerDirections α e X x T) t := by
  classical
  unfold oiloLearnerHypothesis oiloHypothesis
  dsimp only []
  have hq := oiloLearnerQuery_eq_horizon hd α hα he X x htT
  have h_iff := ramVecEq_val (oiloLearnerQuery α e X x t) 0
  by_cases hp0 : oiloLearnerQuery α e X x t = 0
  · rw [if_pos (h_iff.mpr hp0), ← hq, if_pos hp0]
  · have h_f : ¬ ((ramVecEq (oiloLearnerQuery α e X x t) 0).val = true) :=
      fun h => hp0 (h_iff.mp h)
    rw [if_neg h_f, ← hq, if_neg hp0]

lemma oilo_round_shortfall {d : ℕ}
    (w_star : Fin d → ℝ) (e : Fin d → ℝ) (he : e ≠ 0)
    (X : ℕ → Set (Fin d → ℝ)) (hX_ball : ∀ t, ∀ y ∈ X t, dotProduct y y ≤ 1)
    (x x_hat : ℕ → (Fin d → ℝ)) (hx_mem : ∀ t, x t ∈ X t) (hx_hat_mem : ∀ t, x_hat t ∈ X t)
    (u : ℕ → (Fin d → ℝ)) (h_unit : ∀ k, dotProduct (u k) (u k) = 1)
    (α : ℝ) (t : ℕ)
    (h_learner_t : ∀ y ∈ X t,
      dotProduct (oiloHypothesis α e x x_hat u t) y ≤
        dotProduct (oiloHypothesis α e x x_hat u t) (x_hat t))
    (h_expert_t : ∀ y ∈ X t, dotProduct w_star y ≤ dotProduct w_star (x t))
    (hu_t : x t ≠ x_hat t →
      u (oiloGameIndex x x_hat t) =
        (Real.sqrt (dotProduct (x t - x_hat t) (x t - x_hat t)))⁻¹ • (x t - x_hat t)) :
    oiloHypothesis α e x x_hat u t ≠ 0 ∧
    dotProduct (rvmQuery α u (oiloGameIndex x x_hat t)) (x t - x_hat t) ≤ 0 ∧
    0 ≤ dotProduct w_star (x t - x_hat t) ∧
    (x t ≠ x_hat t →
      0 ≤ rvmLoss α w_star u (oiloGameIndex x x_hat t) ∧
      dotProduct w_star (x t - x_hat t) ≤ 2 * rvmLoss α w_star u (oiloGameIndex x x_hat t)) := by
  set k := oiloGameIndex x x_hat t
  set p_k := rvmQuery α u k
  have h_hyp_ne : oiloHypothesis α e x x_hat u t ≠ 0 := by
    unfold oiloHypothesis
    dsimp only
    split_ifs with h0
    · exact he
    · exact h0
  have hp_le : dotProduct p_k (x t - x_hat t) ≤ 0 := by
    by_cases hp0 : p_k = 0
    · rw [hp0, zero_dotProduct]
    · have h_hyp : oiloHypothesis α e x x_hat u t = p_k := by
        unfold oiloHypothesis
        dsimp only
        exact if_neg hp0
      have h_opt := h_learner_t (x t) (hx_mem t)
      rw [h_hyp] at h_opt
      rw [dotProduct_sub]
      linarith
  have hw_nonneg : 0 ≤ dotProduct w_star (x t - x_hat t) := by
    have h_opt := h_expert_t (x_hat t) (hx_hat_mem t)
    rw [dotProduct_sub]
    linarith
  refine ⟨h_hyp_ne, hp_le, hw_nonneg, ?_⟩
  intro h_ne
  set δ := x t - x_hat t
  set s := Real.sqrt (dotProduct δ δ)
  have hu_k : u k = s⁻¹ • δ := hu_t h_ne
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_ne : s ≠ 0 := by
    intro hs0
    have hu0 : u k = 0 := by rw [hu_k, hs0, inv_zero, zero_smul]
    have h1 := h_unit k
    rw [hu0, dotProduct_zero] at h1
    norm_num at h1
  have hs_pos : 0 < s := lt_of_le_of_ne hs_nonneg (Ne.symm hs_ne)
  have h_loss_eq : s * rvmLoss α w_star u k = dotProduct w_star δ - dotProduct p_k δ := by
    unfold rvmLoss
    change s * dotProduct (w_star - p_k) (u k) = dotProduct w_star δ - dotProduct p_k δ
    rw [hu_k, dotProduct_smul, smul_eq_mul, sub_dotProduct, ← mul_assoc, mul_inv_cancel₀ hs_ne, one_mul]
  have h_s_loss_ge : dotProduct w_star δ ≤ s * rvmLoss α w_star u k := by linarith
  have hr_nonneg : 0 ≤ rvmLoss α w_star u k := by nlinarith
  have h_par : dotProduct δ δ + dotProduct (x t + x_hat t) (x t + x_hat t) =
      2 * dotProduct (x t) (x t) + 2 * dotProduct (x_hat t) (x_hat t) := by
    unfold δ dotProduct
    simp only [Pi.sub_apply, Pi.add_apply]
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => by ring)
  have h_sum_pos : 0 ≤ dotProduct (x t + x_hat t) (x t + x_hat t) := h_dot_self_nonneg _
  have h_δ_le_4 : dotProduct δ δ ≤ 4 := by
    have := hX_ball t (x t) (hx_mem t)
    have := hX_ball t (x_hat t) (hx_hat_mem t)
    linarith
  have hs_le_2 : s ≤ 2 := by
    calc s = Real.sqrt (dotProduct δ δ) := rfl
      _ ≤ Real.sqrt 4 := Real.sqrt_le_sqrt h_δ_le_4
      _ = 2 := by norm_num
  refine ⟨hr_nonneg, ?_⟩
  nlinarith

lemma oilo_horizon_reduction {d : ℕ} (hd : 0 < d)
    (h_thm1 : Theorem2_1_RVMRegretBound)
    (w_star : Fin d → ℝ) (hw : dotProduct w_star w_star ≤ 1)
    (e : Fin d → ℝ) (he : e ≠ 0)
    (X : ℕ → Set (Fin d → ℝ)) (hX_ball : ∀ t, ∀ y ∈ X t, dotProduct y y ≤ 1)
    (x x_hat : ℕ → (Fin d → ℝ)) (hx_mem : ∀ t, x t ∈ X t) (hx_hat_mem : ∀ t, x_hat t ∈ X t)
    (u : ℕ → (Fin d → ℝ)) (h_unit : ∀ k, dotProduct (u k) (u k) = 1)
    (α : ℝ) (hα_eq : α = 1 / (3 * Real.sqrt (d : ℝ))) (T : ℕ)
    (h_learner_opt : ∀ t < T, ∀ y ∈ X t,
      dotProduct (oiloHypothesis α e x x_hat u t) y ≤
        dotProduct (oiloHypothesis α e x x_hat u t) (x_hat t))
    (h_expert_opt : ∀ t < T, ∀ y ∈ X t, dotProduct w_star y ≤ dotProduct w_star (x t))
    (hu_eq : ∀ t < T, x t ≠ x_hat t →
      u (oiloGameIndex x x_hat t) =
        (Real.sqrt (dotProduct (x t - x_hat t) (x t - x_hat t)))⁻¹ • (x t - x_hat t)) :
    oiloGameIndex x x_hat T ≤ T ∧
    ∑ t ∈ Finset.range T, dotProduct w_star (x t - x_hat t) ≤
      2 * rvmRegret α w_star u (oiloGameIndex x x_hat T) ∧
    2 * rvmRegret α w_star u (oiloGameIndex x x_hat T) ≤
      (51 / 4 : ℝ) * Real.sqrt (d : ℝ) ∧
    ∑ t ∈ Finset.range T, dotProduct w_star (x t - x_hat t) ≤
      (51 / 4 : ℝ) * Real.sqrt (d : ℝ) ∧
    (51 / 4 : ℝ) * Real.sqrt (d : ℝ) < 13 * Real.sqrt (d : ℝ) ∧
    oiloTotalArithOps α x x_hat u T ≤ 42 * T * d ^ 2 + 36 * T ^ 2 * d := by
  have h_ind : ∀ r ≤ T,
      oiloGameIndex x x_hat r ≤ r ∧
      (∀ k < oiloGameIndex x x_hat r, 0 ≤ rvmLoss α w_star u k) ∧
      ∑ t ∈ Finset.range r, dotProduct w_star (x t - x_hat t) ≤
        2 * rvmRegret α w_star u (oiloGameIndex x x_hat r) := by
    intro r hrT
    induction r with
    | zero =>
      rw [oiloGameIndex_zero]
      refine ⟨le_refl 0, fun k hk => by omega, ?_⟩
      simp [rvmRegret]
    | succ r ih =>
      have hr_lt : r < T := hrT
      have ih' := ih (le_of_lt hr_lt)
      by_cases h_eq : x r = x_hat r
      · rw [oiloGameIndex_succ_eq x x_hat r h_eq, Finset.sum_range_succ]
        have h_zero : dotProduct w_star (x r - x_hat r) = 0 := by
          rw [sub_eq_zero.mpr h_eq, dotProduct_zero]
        refine ⟨Nat.le_succ_of_le ih'.1, ih'.2.1, ?_⟩
        linarith [ih'.2.2]
      · rw [oiloGameIndex_succ_ne x x_hat r h_eq, Finset.sum_range_succ]
        have h_r := (oilo_round_shortfall w_star e he X hX_ball x x_hat hx_mem hx_hat_mem
          u h_unit α r (h_learner_opt r hr_lt) (h_expert_opt r hr_lt) (hu_eq r hr_lt)).2.2.2 h_eq
        refine ⟨Nat.succ_le_succ ih'.1, ?_, ?_⟩
        · intro k hk
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
          · exact ih'.2.1 k hlt
          · exact h_r.1
        · unfold rvmRegret
          rw [Finset.sum_range_succ]
          change ∑ t ∈ Finset.range r, dotProduct w_star (x t - x_hat t) + dotProduct w_star (x r - x_hat r) ≤
            2 * (rvmRegret α w_star u (oiloGameIndex x x_hat r) + rvmLoss α w_star u (oiloGameIndex x x_hat r))
          linarith [ih'.2.2, h_r.2]
  obtain ⟨h_idx_le, h_loss_nonneg, h_sum_le⟩ := h_ind T (le_refl T)
  have hw1 : dotProduct w_star w_star ≤ 1 ^ 2 := by linarith
  have h_thm := h_thm1 hd 1 one_pos w_star hw1 u h_unit α hα_eq (oiloGameIndex x x_hat T) h_loss_nonneg
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hsqrt_pos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd_pos
  have hα_pos : 0 < α := by rw [hα_eq]; positivity
  refine ⟨h_idx_le, h_sum_le, ?_, ?_, ?_, (oiloOps_le hd α hα_pos x x_hat u h_unit).2 T⟩
  · linarith [h_thm.1]
  · linarith [h_thm.1]
  · linarith

lemma cor_2_2 :
    Theorem2_1_RVMRegretBound →
    Corollary2_2_OnlineInverseOptimization := by
  intro h_thm1 d hd
  refine ⟨?_, ?_, ?_⟩
  · intro w_star hw e he X hX_ball x x_hat hx_mem hx_hat_mem u h_unit α hα_eq
       h_learner_opt h_expert_opt hu_eq
    have hα_pos : 0 < α := by rw [hα_eq]; positivity
    refine ⟨?_, ?_⟩
    · intro t
      have hr := oilo_round_shortfall w_star e he X hX_ball x x_hat hx_mem hx_hat_mem
        u h_unit α t (h_learner_opt t) (h_expert_opt t) (hu_eq t)
      exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, (oiloOps_le hd α hα_pos x x_hat u h_unit).1 t⟩
    · intro T
      exact oilo_horizon_reduction hd h_thm1 w_star hw e he X hX_ball x x_hat hx_mem hx_hat_mem
        u h_unit α hα_eq T (fun t _ => h_learner_opt t) (fun t _ => h_expert_opt t)
        (fun t _ => hu_eq t)
  · intro w S h_compact h_nonempty
    exact linearMaximizer_spec w S h_compact h_nonempty
  · intro w_star hw e he X hX_compact hX_nonempty hX_ball x hx_mem h_expert_opt α hα_eq x_hat
    have hα_pos : 0 < α := by rw [hα_eq]; positivity
    have h_max : ∀ t, x_hat t ∈ X t ∧
        ∀ y ∈ X t, dotProduct (oiloLearnerHypothesis α e X x t) y ≤
          dotProduct (oiloLearnerHypothesis α e X x t) (x_hat t) :=
      fun t => linearMaximizer_spec (oiloLearnerHypothesis α e X x t) (X t)
        (hX_compact t) (hX_nonempty t)
    have hx_hat_mem : ∀ t, x_hat t ∈ X t := fun t => (h_max t).1
    have h_learner_max : ∀ t, ∀ y ∈ X t,
        dotProduct (oiloLearnerHypothesis α e X x t) y ≤
          dotProduct (oiloLearnerHypothesis α e X x t) (x_hat t) :=
      fun t => (h_max t).2
    refine ⟨?_, ?_, ?_⟩
    · intro X' x' t h_pref
      exact oiloLearnerState_causal α e X X' x x' t h_pref
    · intro t
      have h_iff := ramVecEq_val (oiloLearnerQuery α e X x t) 0
      have h_hyp_ne : oiloLearnerHypothesis α e X x t ≠ 0 := by
        unfold oiloLearnerHypothesis
        dsimp only []
        by_cases hp0 : oiloLearnerQuery α e X x t = 0
        · rw [if_pos (h_iff.mpr hp0)]; exact he
        · have h_f : ¬ ((ramVecEq (oiloLearnerQuery α e X x t) 0).val = true) :=
            fun h => hp0 (h_iff.mp h)
          rw [if_neg h_f]; exact hp0
      have hp_le : dotProduct (oiloLearnerQuery α e X x t) (x t - x_hat t) ≤ 0 := by
        by_cases hp0 : oiloLearnerQuery α e X x t = 0
        · rw [hp0, zero_dotProduct]
        · have h_f : ¬ ((ramVecEq (oiloLearnerQuery α e X x t) 0).val = true) :=
            fun h => hp0 (h_iff.mp h)
          have h_hyp : oiloLearnerHypothesis α e X x t = oiloLearnerQuery α e X x t := by
            unfold oiloLearnerHypothesis
            dsimp only []
            rw [if_neg h_f]
          have h_opt := h_learner_max t (x t) (hx_mem t)
          rw [h_hyp] at h_opt
          rw [dotProduct_sub]
          linarith
      have hw_nonneg : 0 ≤ dotProduct w_star (x t - x_hat t) := by
        have h_opt := h_expert_opt t (x_hat t) (hx_hat_mem t)
        rw [dotProduct_sub]
        linarith
      exact ⟨oiloLearnerFastState_eq α e X x t, h_hyp_ne, hx_hat_mem t,
        h_learner_max t, hp_le, hw_nonneg⟩
    · intro T u
      have h_unit : ∀ k, dotProduct (u k) (u k) = 1 :=
        oiloLearnerDirections_unit α he X x T
      have h_l_opt : ∀ t < T, ∀ y ∈ X t,
          dotProduct (oiloHypothesis α e x x_hat u t) y ≤
            dotProduct (oiloHypothesis α e x x_hat u t) (x_hat t) := by
        intro t ht y hy
        rw [← oiloLearnerHypothesis_eq_horizon hd α hα_pos he X x (le_of_lt ht)]
        exact h_learner_max t y hy
      have hu_eq : ∀ t < T, x t ≠ x_hat t →
          u (oiloGameIndex x x_hat t) =
            (Real.sqrt (dotProduct (x t - x_hat t) (x t - x_hat t)))⁻¹ • (x t - x_hat t) := by
        intro t ht hne
        dsimp [u, x_hat]
        rw [← oiloLearnerGameIndex_eq]
        exact oiloLearnerDirections_at_non_tie α e X x ht hne
      have h_red := oilo_horizon_reduction hd h_thm1 w_star hw e he X hX_ball x x_hat
        hx_mem hx_hat_mem u h_unit α hα_eq T h_l_opt (fun t _ => h_expert_opt t) hu_eq
      have h_tot_eq := oiloLearnerTotalArithOps_eq_horizon α e X x T
      refine ⟨oiloLearnerGameIndex_eq α e X x T, h_red.1, ?_, ?_, ?_,
        oiloLearnerTotalArithOps_eq_sum α e X x T, h_tot_eq,
        h_red.2.1, h_red.2.2.1, h_red.2.2.2.1, h_red.2.2.2.2.1, ?_, ?_⟩
      · intro t htT
        exact oiloLearnerFastState_eq_horizon α e X x htT
      · intro t htT
        exact oiloLearnerQuery_eq_horizon hd α hα_pos he X x htT
      · intro t htT
        exact oiloLearnerRoundArithOps_eq_horizon α e X x htT
      · intro t htT
        rw [oiloLearnerRoundArithOps_eq_horizon α e X x htT]
        exact (oiloOps_le hd α hα_pos x x_hat u h_unit).1 t
      · rw [h_tot_eq]
        exact h_red.2.2.2.2.2

/-! ### Algorithm Without Revocation (Remark 3.1) -/

lemma stretchMetric_const_single {d : ℕ} (i₀ : Fin d) (S : Finset ℕ) (γ : ℕ → ℝ) :
    stretchMetric S γ (fun _ => (Pi.single i₀ (1 : ℝ) : Fin d → ℝ)) =
      Matrix.diagonal (Function.update (fun _ : Fin d => (1 : ℝ)) i₀ (1 + ∑ k ∈ S, γ k)) := by
  classical
  let e₀ : Fin d → ℝ := Pi.single i₀ 1
  ext i j
  unfold stretchMetric
  rw [Matrix.add_apply, Matrix.one_apply, Matrix.sum_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
    by_cases hi : i = i₀
    · subst hi
      rw [Function.update_self]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [Matrix.smul_apply, Matrix.vecMulVec_apply]
      change γ k * (e₀ i * e₀ i) = γ k
      dsimp [e₀]
      rw [Pi.single_eq_same, mul_one, mul_one]
    · rw [Function.update_of_ne hi]
      have h_zero : ∑ k ∈ S, (γ k • Matrix.vecMulVec e₀ e₀) i i = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        rw [Matrix.smul_apply, Matrix.vecMulVec_apply]
        change γ k * (e₀ i * e₀ i) = 0
        dsimp [e₀]
        rw [Pi.single_eq_of_ne hi, mul_zero, mul_zero]
      rw [h_zero, add_zero]
  · simp only [hij, ↓reduceIte]
    have h_zero : ∑ k ∈ S, (γ k • Matrix.vecMulVec e₀ e₀) i j = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      rw [Matrix.smul_apply, Matrix.vecMulVec_apply]
      change γ k * (e₀ i * e₀ j) = 0
      dsimp [e₀]
      by_cases hi : i = i₀
      · subst hi
        have hj : j ≠ i := Ne.symm hij
        rw [Pi.single_eq_of_ne hj, mul_zero, mul_zero]
      · rw [Pi.single_eq_of_ne hi, zero_mul, mul_zero]
    rw [h_zero, add_zero]

lemma diagonal_update_inv {d : ℕ} (i₀ : Fin d) {μ : ℝ} (hμ : μ ≠ 0) :
    (Matrix.diagonal (Function.update (fun _ : Fin d => (1 : ℝ)) i₀ μ))⁻¹ =
      Matrix.diagonal (Function.update (fun _ : Fin d => (1 : ℝ)) i₀ (1 / μ)) := by
  classical
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one using 2
  ext i
  by_cases hi : i = i₀
  · subst hi
    rw [Function.update_self, Function.update_self, mul_one_div_cancel hμ]
  · rw [Function.update_of_ne hi, Function.update_of_ne hi, mul_one]

lemma diagonal_update_mulVec_single {d : ℕ} (i₀ : Fin d) (c : ℝ) :
    Matrix.diagonal (Function.update (fun _ : Fin d => (1 : ℝ)) i₀ c) *ᵥ
      (Pi.single i₀ (1 : ℝ) : Fin d → ℝ) =
      c • (Pi.single i₀ (1 : ℝ) : Fin d → ℝ) := by
  classical
  let e₀ : Fin d → ℝ := Pi.single i₀ 1
  ext i
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  change Function.update (fun _ : Fin d => (1 : ℝ)) i₀ c i * e₀ i = c * e₀ i
  dsimp [e₀]
  by_cases hi : i = i₀
  · subst hi
    rw [Function.update_self, Pi.single_eq_same]
  · rw [Function.update_of_ne hi, Pi.single_eq_of_ne hi, mul_zero, mul_zero]

lemma quadForm_diagonal_update_single {d : ℕ} (i₀ : Fin d) (c : ℝ) :
    quadForm (Matrix.diagonal (Function.update (fun _ : Fin d => (1 : ℝ)) i₀ c))
      (Pi.single i₀ (1 : ℝ) : Fin d → ℝ) = c := by
  classical
  unfold quadForm
  rw [diagonal_update_mulVec_single, dotProduct_smul, dotProduct_single, Pi.single_eq_same,
    mul_one, smul_eq_mul, mul_one]

lemma geom_weight_sum (t : ℕ) :
    1 + ∑ k ∈ Finset.range t, (1 / 8 : ℝ) * (9 / 8 : ℝ) ^ k = (9 / 8 : ℝ) ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih]
    ring

lemma rvmNoRevokeState_axis_aligned {d : ℕ} (i₀ : Fin d) (α : ℝ) (t : ℕ) :
    let e₀ : Fin d → ℝ := Pi.single i₀ 1
    let v : ℕ → (Fin d → ℝ) := fun _ => e₀
    (rvmNoRevokeState α v t).A = Finset.range t ∧
    (∀ k < t, (rvmNoRevokeState α v t).γ k = (1 / 8 : ℝ) * (9 / 8 : ℝ) ^ k) ∧
    (rvmNoRevokeState α v t).p = (∑ k ∈ Finset.range t, α / (9 / 8 : ℝ) ^ k) • e₀ := by
  classical
  intro e₀ v
  induction t with
  | zero =>
    simp [rvmNoRevokeState]
  | succ t ih =>
    rcases ih with ⟨hA, hγ, hp⟩
    have h_sum : 1 + ∑ k ∈ (rvmNoRevokeState α v t).A, (rvmNoRevokeState α v t).γ k =
        (9 / 8 : ℝ) ^ t := by
      rw [hA]
      have h_congr : ∑ k ∈ Finset.range t, (rvmNoRevokeState α v t).γ k =
          ∑ k ∈ Finset.range t, (1 / 8 : ℝ) * (9 / 8 : ℝ) ^ k :=
        Finset.sum_congr rfl (fun k hk => hγ k (Finset.mem_range.mp hk))
      rw [h_congr, geom_weight_sum]
    have hH : stretchMetric (rvmNoRevokeState α v t).A (rvmNoRevokeState α v t).γ v =
        Matrix.diagonal (Function.update (fun _ : Fin d => (1 : ℝ)) i₀ ((9 / 8 : ℝ) ^ t)) := by
      dsimp [v, e₀]
      rw [stretchMetric_const_single, h_sum]
    have hμ_pos : (0 : ℝ) < (9 / 8 : ℝ) ^ t := by positivity
    have hH_inv : (stretchMetric (rvmNoRevokeState α v t).A (rvmNoRevokeState α v t).γ v)⁻¹ =
        Matrix.diagonal (Function.update (fun _ : Fin d => (1 : ℝ)) i₀ (1 / (9 / 8 : ℝ) ^ t)) := by
      rw [hH, diagonal_update_inv i₀ (ne_of_gt hμ_pos)]
    have hs_sq : (matNorm (stretchMetric (rvmNoRevokeState α v t).A (rvmNoRevokeState α v t).γ v)⁻¹
        (v t)) ^ 2 = 1 / (9 / 8 : ℝ) ^ t := by
      unfold matNorm
      rw [hH_inv]
      dsimp [v, e₀]
      rw [quadForm_diagonal_update_single, Real.sq_sqrt (by positivity)]
    have hγ_t : 1 / (8 * (matNorm (stretchMetric (rvmNoRevokeState α v t).A
        (rvmNoRevokeState α v t).γ v)⁻¹ (v t)) ^ 2) = (1 / 8 : ℝ) * (9 / 8 : ℝ) ^ t := by
      rw [hs_sq]
      field_simp
    have hmvec : (stretchMetric (rvmNoRevokeState α v t).A (rvmNoRevokeState α v t).γ v)⁻¹ *ᵥ v t =
        (1 / (9 / 8 : ℝ) ^ t) • e₀ := by
      rw [hH_inv]
      dsimp [v, e₀]
      exact diagonal_update_mulVec_single i₀ (1 / (9 / 8 : ℝ) ^ t)
    refine ⟨?_, ?_, ?_⟩
    · change insert t (rvmNoRevokeState α v t).A = Finset.range (t + 1)
      rw [hA, Finset.range_add_one]
    · intro k hk
      change Function.update (rvmNoRevokeState α v t).γ t _ k = _
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h_lt | rfl
      · rw [Function.update_of_ne (ne_of_lt h_lt)]
        exact hγ k h_lt
      · rw [Function.update_self, hγ_t]
    · change (rvmNoRevokeState α v t).p +
        α • ((stretchMetric (rvmNoRevokeState α v t).A (rvmNoRevokeState α v t).γ v)⁻¹ *ᵥ v t) = _
      rw [hp, hmvec, smul_smul, Finset.sum_range_succ, add_smul]
      congr 2
      ring

/-- **Remark 3.1 (Stalling without revocation)** -/
theorem rem_stall : Remark3_1_StallingWithoutRevocation := by
  classical
  intro d hd i₀ R hR α hα_eq e₀ v w_star μ s_sq γ p t
  have hd_ge_10 : (10 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd_pos : (0 : ℝ) < (d : ℝ) := by linarith
  have hsqrt_gt_3 : (3 : ℝ) < Real.sqrt (d : ℝ) := by
    have h9 : (3 : ℝ) = Real.sqrt 9 := by norm_num
    rw [h9]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hsqrt_pos : 0 < Real.sqrt (d : ℝ) := by linarith
  have hα_pos : 0 < α := by rw [hα_eq]; positivity
  have hs_sq_eq : ∀ k : ℕ, s_sq k = (8 / 9 : ℝ) ^ k := by
    intro k
    dsimp [s_sq, μ]
    rw [one_div, ← inv_pow]
    congr 1
    norm_num
  have hμ_succ : μ (t + 1) = μ t + γ t := by
    dsimp [γ]
    rw [hs_sq_eq t]
    dsimp [μ]
    rw [pow_succ, one_div, mul_inv_rev, ← inv_pow]
    have h_inv : (8 / 9 : ℝ)⁻¹ = (9 / 8 : ℝ) := by norm_num
    rw [h_inv]
    ring
  have hp_step : p (t + 1) - p t = (α * (8 / 9 : ℝ) ^ t) • e₀ := by
    dsimp [p]
    rw [Finset.sum_range_succ, add_smul, add_sub_cancel_left]
    congr 1
    rw [div_eq_mul_one_div]
    change α * s_sq t = α * (8 / 9 : ℝ) ^ t
    rw [hs_sq_eq t]
  have he0_unit : dotProduct e₀ e₀ = 1 := by
    dsimp [e₀]
    simp [dotProduct, Pi.single_apply]
  have h_geom : ∀ k : ℕ, ∑ j ∈ Finset.range k, α / μ j = 9 * α * (1 - (8 / 9 : ℝ) ^ k) := by
    intro k
    induction k with
    | zero =>
      simp
    | succ k ih =>
      have h_term : α / μ k = α * (8 / 9 : ℝ) ^ k := by
        rw [div_eq_mul_one_div]
        exact congr_arg (α * ·) (hs_sq_eq k)
      rw [Finset.sum_range_succ, ih, h_term]
      ring
  have hp_dot : ∀ k : ℕ, dotProduct (p k) e₀ = 9 * α * (1 - (8 / 9 : ℝ) ^ k) := by
    intro k
    dsimp [p]
    rw [smul_dotProduct, he0_unit, smul_eq_mul, mul_one, h_geom k]
  have hp_lt : ∀ k : ℕ, dotProduct (p k) e₀ < 9 * α := by
    intro k
    have h_pow_pos : 0 < (8 / 9 : ℝ) ^ k := by positivity
    rw [hp_dot k]
    nlinarith
  have h9α : 9 * α = 3 * R / Real.sqrt (d : ℝ) := by
    rw [hα_eq]
    ring
  have h_div_lt_1 : 3 / Real.sqrt (d : ℝ) < 1 := (div_lt_one hsqrt_pos).mpr hsqrt_gt_3
  have h_loss_pos : 0 < R * (1 - 3 / Real.sqrt (d : ℝ)) :=
    mul_pos hR (by linarith)
  have h_axis_all : ∀ k : ℕ,
      rvmNoRevokeActiveSet α v k = Finset.range k ∧
      rvmNoRevokeMetric α v k =
        Matrix.diagonal (Function.update (fun _ : Fin d => (1 : ℝ)) i₀ (μ k)) ∧
      (rvmNoRevokeStepNorm α v k) ^ 2 = s_sq k ∧
      rvmNoRevokeWeight α v k = γ k ∧
      rvmNoRevokeQuery α v k = p k ∧
      rvmNoRevokeLoss α w_star v k = dotProduct (w_star - p k) e₀ ∧
      R * (1 - 3 / Real.sqrt (d : ℝ)) < rvmNoRevokeLoss α w_star v k := by
    intro k
    obtain ⟨hA_k, hγ_k, hp_k⟩ := rvmNoRevokeState_axis_aligned i₀ α k
    have h_sum_k : 1 + ∑ j ∈ (rvmNoRevokeState α v k).A, (rvmNoRevokeState α v k).γ j = μ k := by
      rw [hA_k]
      have h_congr : ∑ j ∈ Finset.range k, (rvmNoRevokeState α v k).γ j =
          ∑ j ∈ Finset.range k, (1 / 8 : ℝ) * (9 / 8 : ℝ) ^ j :=
        Finset.sum_congr rfl (fun j hj => hγ_k j (Finset.mem_range.mp hj))
      rw [h_congr, geom_weight_sum]
    have hH_k : rvmNoRevokeMetric α v k =
        Matrix.diagonal (Function.update (fun _ : Fin d => (1 : ℝ)) i₀ (μ k)) := by
      unfold rvmNoRevokeMetric
      dsimp [v, e₀]
      rw [stretchMetric_const_single, h_sum_k]
    have hμ_pos : 0 < μ k := by dsimp [μ]; positivity
    have hH_inv_k : (rvmNoRevokeMetric α v k)⁻¹ =
        Matrix.diagonal (Function.update (fun _ : Fin d => (1 : ℝ)) i₀ (s_sq k)) := by
      rw [hH_k, diagonal_update_inv i₀ (ne_of_gt hμ_pos)]
    have hs_sq_k : (rvmNoRevokeStepNorm α v k) ^ 2 = s_sq k := by
      unfold rvmNoRevokeStepNorm matNorm
      rw [hH_inv_k]
      dsimp [v, e₀]
      rw [quadForm_diagonal_update_single]
      exact Real.sq_sqrt (by dsimp [s_sq, μ]; positivity)
    have hγ_eq_k : rvmNoRevokeWeight α v k = γ k := by
      unfold rvmNoRevokeWeight
      rw [hs_sq_k]
    have hp_eq_k : rvmNoRevokeQuery α v k = p k := hp_k
    have hloss_eq_k : rvmNoRevokeLoss α w_star v k = dotProduct (w_star - p k) e₀ := by
      unfold rvmNoRevokeLoss
      rw [hp_eq_k]
    have h_loss_gt_k : R * (1 - 3 / Real.sqrt (d : ℝ)) < rvmNoRevokeLoss α w_star v k := by
      rw [hloss_eq_k, sub_dotProduct]
      have hw_dot : dotProduct w_star e₀ = R := by
        dsimp [w_star]
        rw [smul_dotProduct, he0_unit, smul_eq_mul, mul_one]
      rw [hw_dot]
      have h_eq : R * (1 - 3 / Real.sqrt (d : ℝ)) = R - 3 * R / Real.sqrt (d : ℝ) := by ring
      linarith [hp_lt k, h9α, h_eq]
    exact ⟨hA_k, hH_k, hs_sq_k, hγ_eq_k, hp_eq_k, hloss_eq_k, h_loss_gt_k⟩
  have ht := h_axis_all t
  have h_reg_ge : (t : ℝ) * (R * (1 - 3 / Real.sqrt (d : ℝ))) ≤ rvmNoRevokeRegret α w_star v t := by
    unfold rvmNoRevokeRegret
    have h_le : ∀ k ∈ Finset.range t,
        R * (1 - 3 / Real.sqrt (d : ℝ)) ≤ rvmNoRevokeLoss α w_star v k :=
      fun k _ => le_of_lt (h_axis_all k).2.2.2.2.2.2
    have h_sum := Finset.sum_le_sum h_le
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h_sum
    exact h_sum
  exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2.1,
    hs_sq_eq t, hμ_succ, hp_step, hp_dot t, hp_lt t, h9α, ht.2.2.2.2.2.2, h_loss_pos, h_reg_ge⟩

/-!
## 7. Master Theorem and Top-Level Wrappers
-/

theorem oio_all_results :
    Causality_OraclePrefix ∧
    Lemma2_3a_ActiveSlabsContainQuery ∧
    Lemma2_3b_PiecewiseLinearMove ∧
    Lemma2_3c_MetricAndDualLengthMonotone ∧
    Lemma2_3d_RevocationOnBoundary ∧
    Remark2_4_CombinatorialCounts ∧
    Lemma2_5_OneMove ∧
    Equation6_Ledger ∧
    Lemma2_6_StretchLifetime ∧
    Lemma2_7_SurvivingStretches ∧
    Theorem2_1_RVMRegretBound ∧
    Corollary2_2_OnlineInverseOptimization ∧
    Remark3_1_StallingWithoutRevocation ∧
    Proposition3_3_SkippingSmallStretches :=
by
  have h23c : Lemma2_3c_MetricAndDualLengthMonotone := lem_2_3c lem_2_3b
  have heq6 : Equation6_Ledger := lem_eq_6 lem_2_3a lem_2_3b lem_2_5
  have h26 : Lemma2_6_StretchLifetime := lem_2_6 h23c lem_2_3d lem_2_5
  have h27 : Lemma2_7_SurvivingStretches := lem_2_7 lem_2_3a lem_2_3b h23c
  have hthm1 : Theorem2_1_RVMRegretBound := thm_2_1 heq6 h26 h27
  have hcor2 : Corollary2_2_OnlineInverseOptimization := cor_2_2 hthm1
  exact ⟨thm_causality, lem_2_3a, lem_2_3b, h23c, lem_2_3d, rem_cost_counts,
    lem_2_5, heq6, h26, h27, hthm1, hcor2, rem_stall, prop_3_3⟩

/-- **Lemma 2.3 (Well-posed move)** -/
lemma lem_wellposed :
    Lemma2_3a_ActiveSlabsContainQuery ∧
    Lemma2_3b_PiecewiseLinearMove ∧
    Lemma2_3c_MetricAndDualLengthMonotone ∧
    Lemma2_3d_RevocationOnBoundary :=
  ⟨oio_all_results.2.1, oio_all_results.2.2.1, oio_all_results.2.2.2.1, oio_all_results.2.2.2.2.1⟩

/-- **Lemma 2.5 (One move)** -/
lemma lem_path : Lemma2_5_OneMove :=
  oio_all_results.2.2.2.2.2.2.1

/-- **Equation (6) (The ledger)** -/
lemma lem_ledger : Equation6_Ledger :=
  oio_all_results.2.2.2.2.2.2.2.1

/-- **Lemma 2.6 (Lifetime of a stretch)** -/
lemma lem_lifetime : Lemma2_6_StretchLifetime :=
  oio_all_results.2.2.2.2.2.2.2.2.1

/-- **Lemma 2.7 (Surviving stretches)** -/
lemma lem_potential : Lemma2_7_SurvivingStretches :=
  oio_all_results.2.2.2.2.2.2.2.2.2.1

/-- **Theorem 2.1 (Regret of RVM(α))** -/
theorem thm_rvm : Theorem2_1_RVMRegretBound :=
  oio_all_results.2.2.2.2.2.2.2.2.2.2.1

/-- **Corollary 2.2 (Online inverse optimization)** -/
theorem cor_oilo : Corollary2_2_OnlineInverseOptimization :=
  oio_all_results.2.2.2.2.2.2.2.2.2.2.2.1

/-- **Proposition 3.3 (Skipping small stretches)** -/
theorem prop_small : Proposition3_3_SkippingSmallStretches :=
  oio_all_results.2.2.2.2.2.2.2.2.2.2.2.2.2
