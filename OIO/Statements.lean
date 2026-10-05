import Mathlib

open scoped Matrix BigOperators

/-!
# Formalization of "Efficient Online Inverse Optimization with O(√d) Regret" — Statements

This file (`OIO/Statements.lean`) is the trusted specification file for the Lean 4 formalization of
**"Efficient Online Inverse Optimization with $O(\sqrt{d})$ Regret"**. It contains only definitions
and propositional statements (`def … : Prop`), containing no proof terms. All proofs and
top-level theorem declarations are in `OIO/Proofs.lean`, and kernel verification checks are in `OIO/Audit.lean`.

## Summary of Formalized Results

- **Definition 1.1 (`rvmState`, `rvmPath`, `rvmQuery`, `rvmMetric`)**:
  Algorithm $\mathrm{RVM}(\alpha)$ with continuous piecewise-linear move $\hat p_t : [0, \alpha] \to \mathbb{R}^d$,
  active stretch set $\hat A_t(\eta)$, metric $\hat H_t(\eta) = I + \sum_{i \in \hat A_t(\eta)} \gamma_i v_i v_i^\top$,
  and rank-one stretch updates with open slab $L_t = \{p \in \mathbb{R}^d : |\langle p - p_{t+1}, v_t \rangle| < 4 \alpha s_t^2\}$.
- **Theorem 2.1 (`Theorem2_1_RVMRegretBound`)**:
  With $\alpha = R / (3\sqrt{d})$, for every horizon $T$, $\operatorname{Reg}_T \le \frac{51}{8} R \sqrt{d} < 6.4 R \sqrt{d}$
  and $\|p_T - w^*\|^2 \le \frac{17}{8} R^2$ (where $p_T$ is the post-$T$-round query, written $p_{T+1}$ in
  1-indexed paper indexing), together with the instrumented scalar-operation bounds
  $\operatorname{ops}_t \le 28 (t + 1) d^2 + 28 (t + 1)^2 d = O(t d^2 + t^2 d)$ per round and
  $\sum_{t < T} \operatorname{ops}_t \le 34 T d^2 + 36 T^2 d = T \cdot O(d^2 + T d)$ over $T$ rounds.
- **Corollary 2.2 (`Corollary2_2_OnlineInverseOptimization`)**:
  Online inverse linear optimization on compact nonempty action sets $X_t \subseteq \mathbb{B}$ ($R = 1$):
  (1) protocol-level reduction establishing the full chain
      $R_T \le 2 \operatorname{Reg}_{g(T)} \le \frac{51}{4} \sqrt{d} < 13 \sqrt{d}$, per-round scalar-operation
      bound $\operatorname{ops}_t \le 36 (t + 1) d^2 + 28 (t + 1)^2 d$, and cumulative scalar-operation bound
      $\sum_{t < T} \operatorname{ops}_t \le 42 T d^2 + 36 T^2 d$;
  (2) existence of a linear maximizer `linearMaximizer w S ∈ S` on any nonempty compact set $S \subseteq \mathbb{R}^d$;
  (3) explicit closed-loop construction of the deterministic proper learner (`oiloLearnerState`,
      `oiloLearnerHypothesis`, `oiloLearnerAction`), whose state carries the incremental state
      `RVMFastState d` directly and advances it by one incremental step (`rvmFastStep`) on non-tie rounds,
      proving causality, non-zero hypotheses $\hat w_t \ne 0$, validity of the skipped-tie reduction,
      the full chain $R_T \le 2 \operatorname{Reg}_{g(T)} \le \frac{51}{4} \sqrt{d} < 13 \sqrt{d}$, and
      exact agreement of its accumulated scalar-operation counts (`oiloLearnerRoundArithOps`,
      `oiloLearnerTotalArithOps`) with `oiloRoundArithOps` and `oiloTotalArithOps`.
- **Lemma 2.3 (`Lemma2_3a_ActiveSlabsContainQuery`, `Lemma2_3b_PiecewiseLinearMove`,
  `Lemma2_3c_MetricAndDualLengthMonotone`, `Lemma2_3d_RevocationOnBoundary`)**:
  (a) Active slabs contain the query ($p_t \in L_i$ for all $i \in A_t$), $\hat p_t(0) = p_t$,
      $\hat A_t(0) = A_t$, $\hat H_t(0) = H_t$;
  (b) Existence and uniqueness of the continuous path solving Equation (3) (`SolvesMove`), together
      with an explicit piecewise-linear partition into $1 \le \text{pieces}_t \le k_t + 1 \le |A_t| + 1$
      affine segments;
  (c) Loewner monotonicity of $\hat H_t(\eta)$ and monotonicity/bounds of the dual length
      $0 < \sigma_t(\eta_1) \le \sigma_t(\eta_2) \le s_t \le 1$;
  (d) Revocation at time $\eta_i \in (0, \alpha]$ on the slab boundary
      $|\langle q_i - p_{i+1}, v_i \rangle| = 4 \alpha s_i^2$ (with $i$ active on $[0, \eta_i)$ and
      inactive at $\eta_i$) and Equation (5) for $\Delta_t$.
- **Remark 2.4 (`Remark2_4_CombinatorialCounts`, `Causality_OraclePrefix`)**:
  Combinatorial piece and revocation bounds ($|A_t| \le t$, $\sum_{t < T} k_t \le T$,
  $\sum_{t < T} \text{pieces}_t \le 2T$ for both $\mathrm{RVM}(\alpha)$ and $\mathrm{RVMSkip}(\alpha)$),
  Sherman–Morrison rank-one update/downdate identities, exact state equivalence between `rvmState` and the
  matrix-inversion-free incremental implementation `rvmFastState` (storing $M = H^{-1}$, squared dual
  norms $s_i^2$, and active slab displacements $\phi_i = \langle p - p_{i+1}, v_i \rangle$ for $i \in A_t$
  with $\phi_i = 0$ for $i \notin A_t$), per-round scalar-operation bound
  $\operatorname{ops}_t \le 28 (k_t + 1)(d^2 + |A_t| d)$, and oracle-prefix causality of `rvmState`,
  `rvmSkipState`, `rvmFastState`, and `rvmSkipFastState`.
- **Lemma 2.5 (`Lemma2_5_OneMove`) & Equation (6) (`Equation6_Ledger`)**:
  One-move displacement bound $0 \le \xi_t \le \alpha s_t^2$, local-metric distance change, and the
  telescoped lifetime ledger $\|p_T - w^*\|^2 - \|w^*\|^2 \le \sum_{t < T} \Lambda_t$ (0-indexed).
- **Lemma 2.6 (`Lemma2_6_StretchLifetime`)**:
  Lifetime contribution bound $\Lambda_t \le -\alpha r_t$ for revoked stretches and
  $\Lambda_t \le -\alpha r_t + \frac{9}{8} \alpha^2 s_t^2$ for surviving stretches.
- **Lemma 2.7 (`Lemma2_7_SurvivingStretches`)**:
  Trace potential bound $\sum_{t \in A_T} s_t^2 \le 9 (d - \operatorname{tr}(\bar H_T^{-1})) \le 9 d$
  (where $A_T$ and $\bar H_T$ are $A_{T+1}$ and $\bar H_{T+1}$ in 1-indexed paper indexing).
- **Remark 3.1 (`Remark3_1_StallingWithoutRevocation`)**:
  Formal definition of the variable-metric algorithm without revocation (`rvmNoRevokeState`) and proof
  that on the axis-aligned instance $w^* = R e_0$, $v_t = e_0$ for $d \ge 10$, its queries stall behind
  $9 \alpha e_0 = (3R / \sqrt{d}) e_0$, suffering constant per-round loss $r_t > R(1 - 3/\sqrt{d}) > 0$
  and linear cumulative regret $\operatorname{Reg}_T \ge T R(1 - 3/\sqrt{d})$.
- **Proposition 3.3 (`Proposition3_3_SkippingSmallStretches`)**:
  Skipping stretches with $s_t^2 \le (t + 2)^{-4}$ (0-indexed, i.e., $(t + 1)^{-4}$ in 1-indexed paper
  indexing) guarantees $\operatorname{Reg}_T \le (\frac{51}{8} + \frac{0.03}{d}) R \sqrt{d} < 6.41 R \sqrt{d}$,
  full state equivalence between `rvmSkipFastState` and `rvmSkipState` (`p`, `A`, `c`, `s_sq`, `γ`, `M`,
  and `φ` on/off `A`), $(9/8)^{|A_t|} \le \det H_t$, $\operatorname{tr} H_t \le d + (t + 1)^5 / 8$,
  $|A_t| \le B_t := d \ln(1 + (t + 1)^5 / (8d)) / \ln(9/8)$, per-round scalar-operation count
  $\operatorname{ops}_t \le 33 (|A_t| + 1)(d^2 + |A_t| d) \le 33 (B_t + 1)(d^2 + B_t d) = O(d^3 \log^2 t)$,
  and cumulative scalar-operation count $\sum_{t < T} \operatorname{ops}_t \le 39 T d^2 + 36 T B_T d = T \cdot O(d^2 \log T)$.

## Indexing Convention

Rounds in Lean are **0-indexed** ($t = 0, 1, 2, \dots$), corresponding to round $t + 1$ in the
1-indexed indexing of the paper:
- Initial state before any rounds: `rvmQuery α v 0 = 0`, `rvmActiveSet α v 0 = ∅`, `rvmMetric α v 0 = 1`
  (paper: $p_1 = 0$, $A_1 = \emptyset$, $H_1 = I$).
- State after $T$ rounds ($t = 0, \dots, T - 1$): `rvmQuery α v T` and `rvmActiveSet α v T`
  (paper: $p_{T+1}$ and $A_{T+1}$).
- Small-stretch threshold in round $t$: $s_t^2 > (t + 2)^{-4}$ in 0-indexed Lean indexing, matching
  $s_{t_{\text{paper}}}^2 > (t_{\text{paper}} + 1)^{-4}$ for $t_{\text{paper}} = t + 1 \ge 1$.
- Active stretch bound at the start of 0-indexed round $t$: $(t + 1)^5$ in Lean, matching
  $t_{\text{paper}}^5$ at 1-indexed round $t_{\text{paper}} = t + 1$.

## Modeling Choices

1. **Adaptive oracle (`v : ℕ → (Fin d → ℝ)`)**: An adaptive adversary or separation oracle is
   modeled by an arbitrary sequence `v` of unit directions. Because the learner is deterministic and
   the state at round $t$ depends only on $v_0, \dots, v_{t-1}$ (proven formally in
   `Causality_OraclePrefix` for both the specification states and the incremental states), universal
   quantification over all sequences `v` is equivalent to quantification over all history-dependent
   adaptive adversaries.
2. **Closed-loop OILO learner (`oiloLearnerState`, `linearMaximizer`)**: In Corollary 2.2, we prove
   both the protocol-level reduction for any maximizer choices `x_t, x̂_t ∈ X_t` and the closed-loop
   existence statement for any sequence of nonempty compact action sets $X_t \subseteq \mathbb{B}$,
   where `linearMaximizer` selects a maximizer of $\langle \hat w_t, y \rangle$ over the compact
   nonempty set $X_t$ via Weierstrass's extreme value theorem (`IsCompact.exists_isMaxOn`), and
   `oiloLearnerState` carries an `RVMFastState d` directly and advances it by one incremental round
   (`rvmFastStep`) on non-tie rounds.
3. **Domain $w^* \in K_1$**: Modeled directly by the radius bound `dotProduct w_star w_star ≤ R ^ 2`
   ($\|w^*\| \le R$), which is the sole property of $K_1$ used by the algorithm and proofs.
4. **Non-degeneracy (`0 < d`, `0 < R`, `0 < α`)**: Assumed explicitly so that $\alpha = R / (3\sqrt{d}) > 0$
   and the open slabs $L_i$ are nonempty around their centers.
5. **Euclidean norms (`dotProduct x x`)**: Squared Euclidean norms on `Fin d → ℝ` are written
   `dotProduct x x` because Mathlib's default `Norm (Fin d → ℝ)` is the $\ell_\infty$ sup norm rather
   than the $\ell_2$ norm.
6. **Fuel in `rvmMoveEval`**: The recursive evaluation `rvmMoveEval` takes fuel `st.A.card + 1`.
   Lemma 2.3(b) proves that the move traverses at most $k_t + 1 \le |A_t| + 1$ pieces and satisfies
   the differential/slab equation `SolvesMove` on the full interval $[0, \alpha]$ (whose solution is
   unique), confirming that the fuel is never exhausted.
7. **Instrumented scalar-operation model (`CostM`) of the incremental Sherman–Morrison implementation**:
   `rvmFastState`, `rvmSkipFastState`, and `oiloLearnerState` implement the incremental algorithms of
   Remark 2.4, Proposition 3.3, and Corollary 2.2 storing $M = H^{-1}$, squared dual norms $s_i^2$,
   and the active slab displacements $\phi_i = \langle p - p_{i+1}, v_i \rangle$ for $i \in A_t$
   ($\phi_i = 0$ for $i \notin A_t$), updating them via rank-one Sherman–Morrison updates and downdates
   without matrix inversions, and accumulating instrumented scalar-operation counts in
   `CostM α` (with private constructor `CostM.mk` so all operations are constructed from `CostM.pure`,
   `CostM.bind`, `CostM.foldl`, and the scalar primitives):
   - **What is charged**: Every scalar arithmetic primitive (`ramAdd`, `ramSub`, `ramMul`, `ramDiv`,
     `ramNeg`, `ramAbs`, `ramSqrt`) and scalar comparison (`ramLt`, `ramEq`, `ramMin`) charges `1`
     operation. Vector, matrix, finite-set, and piece computations (`ramVecAdd`, `ramVecSub`,
     `ramVecSmul`, `ramVecEq`, `ramDot`, `ramMatVec`, `ramRankOneAdd`, `ramRankOneSub`,
     `ramFastPieceExitDelta`, `ramComputeBeta`, `ramFastPieceStepTime`, `ramPhiUpdate`, `ramSlabCheck`,
     `ramUpdateSlabs`, `ramDowndate`, `shermanMorrisonDowndateSetWithCost`, `ramStretchCreation`,
     `ramSkipStretchCreation`, `ramFastPiece`, `rvmFastMove`, `ramNormalizeDiff`) are written as single
     computations using `CostM.bind` and `CostM.foldl`. In $\mathrm{RVM}(\alpha)$ and
     $\mathrm{RVMSkip}(\alpha)$, `RVMFastState` stores $s_i^2$ (`s_sq`) directly so that all arithmetic
     in `rvmFastState` and `rvmSkipFastState` is purely rational apart from $\alpha$ (`ramSqrt` is used
     only in `ramNormalizeDiff` in the OILO reduction).
   - **What is not charged**: Index and finite-set bookkeeping (`Finset.sdiff`, `Finset.sort`,
     `Finset.insert`, `Function.update`, recursion/loop counters), memory allocation and addressing,
     and the single linear-optimization oracle call (`linearMaximizer`) over $X_t$ in Corollary 2.2 are
     not charged in the scalar operation counts.
8. **Total-function conventions**:
   - `Decidable (inSlab …)` is provided via `Classical.propDecidable`.
   - Matrix inversion `H⁻¹` is Mathlib's total nonsingular inverse; every inverted metric is proven
     positive definite (`Matrix.PosDef`) and hence invertible (`IsUnit H.det`).
   - Division `1 / (8 * s_t ^ 2)` uses Lean's total division on `ℝ`, and $s_t > 0$ is proven in
     Lemma 2.3(c).

## Scope and What Is Not Formalized

- **Bookkeeping, memory bounds, and bit-level rationality**: Index/set bookkeeping and memory allocation
  are not charged in `CostM`; the $O(d^2 + T d)$ (and $O(d^2 \log T)$) memory bounds in Remark 2.4 and
  Proposition 3.3 and the bit-level rationality observation in Remark 2.4 (`ℚ`-valued state when $\alpha$
  and $v_t$ are rational, reflected structurally by storing $s_t^2$ without `ramSqrt` in `RVMFastState`)
  are not formalized as separate theorems.
- **Prose remarks and external lower bounds**: The weaker-expert remark in Section 1 ($R_T$ holds against
  any sequence $x_t \in X_t$ once $\langle w^*, x_t - \hat x_t \rangle \ge 0$), the prose remarks after
  Lemmas 2.5 and 2.6 and Theorem 2.1, discussion Remarks 2.8 and 3.2, Table 1, and the cited
  $\Omega(\sqrt{d})$ lower bounds from prior work (\cite{Cai26,SakaueONS,SakaueMMW}) are not formalized.
-/

/-!
## 1. Metric and Slab Primitives
-/

/-- Matrix quadratic form `x^T H x` for `x : Fin d → ℝ` and `H : Matrix (Fin d) (Fin d) ℝ`. -/
noncomputable def quadForm {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) : ℝ :=
  dotProduct x (H *ᵥ x)

/-- Matrix-induced norm `‖x‖_H = √(x^T H x)`. -/
noncomputable def matNorm {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) : ℝ :=
  Real.sqrt (quadForm H x)

/-- Metric matrix `H(A) = I + ∑_{i ∈ A} γ_i v_i v_i^T` formed by a finite set `A` of active stretches. -/
noncomputable def stretchMetric {d : ℕ} (A : Finset ℕ) (γ : ℕ → ℝ) (v : ℕ → (Fin d → ℝ)) :
    Matrix (Fin d) (Fin d) ℝ :=
  1 + ∑ i ∈ A, (γ i) • Matrix.vecMulVec (v i) (v i)

/-- Open slab `L_i = {p ∈ ℝ^d : |⟨p - center, v_i⟩| < 4 α s_i^2}` around `center = p_{i+1}`. -/
def inSlab {d : ℕ} (α : ℝ) (center v_i : Fin d → ℝ) (s_i : ℝ) (p : Fin d → ℝ) : Prop :=
  |dotProduct (p - center) v_i| < 4 * α * s_i ^ 2

noncomputable instance {d : ℕ} (α : ℝ) (center v_i : Fin d → ℝ) (s_i : ℝ) (p : Fin d → ℝ) :
    Decidable (inSlab α center v_i s_i p) :=
  Classical.propDecidable _

/-!
## 2. The Continuous Piecewise-Linear Move (Equation (3) & Lemma 2.3)
-/

/-- Exit time along ray `p + δ u` (`δ ≥ 0`) for active stretch `i` to hit the boundary of its slab
    `|⟨p + δ u - c_i, v_i⟩| = 4 α s_i^2`, or `rem` if `⟨u, v_i⟩ = 0`. -/
noncomputable def pieceExitDelta {d : ℕ} (α rem : ℝ)
    (c v : ℕ → (Fin d → ℝ)) (s : ℕ → ℝ)
    (p u : Fin d → ℝ) (i : ℕ) : ℝ :=
  let φ := dotProduct (p - c i) (v i)
  let β := dotProduct u (v i)
  if β > 0 then (4 * α * (s i) ^ 2 - φ) / β
  else if β < 0 then (-4 * α * (s i) ^ 2 - φ) / β
  else rem

/-- Duration `δ` of the current linear piece of the move, equal to the minimum of the remaining
    time `rem` and the slab exit times `pieceExitDelta` over all active stretches `i ∈ A`. -/
noncomputable def pieceStepTime {d : ℕ} (α rem : ℝ)
    (c v : ℕ → (Fin d → ℝ)) (s : ℕ → ℝ)
    (A : Finset ℕ) (p u : Fin d → ℝ) : ℝ :=
  A.fold min rem (pieceExitDelta α rem c v s p u)

/-- Evaluation of the piecewise-linear move `(hat_p(τ), hat_A(τ))` at time `τ ∈ [0, rem]`
    starting from point `p` and active set `A`, with fuel `n` bounding the number of pieces. -/
noncomputable def rvmMoveEval {d : ℕ} (α : ℝ)
    (c v : ℕ → (Fin d → ℝ)) (s γ : ℕ → ℝ) (v_t : Fin d → ℝ) :
    ℕ → ℝ → (Fin d → ℝ) → Finset ℕ → ℝ → (Fin d → ℝ) × Finset ℕ
  | 0, _, p, A, _ => (p, A)
  | n + 1, rem, p, A, τ =>
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
      (p_next, A_next)

/-- Number of linear pieces traversed by the move over duration `rem` starting from `(p, A)`. -/
noncomputable def rvmMovePieces {d : ℕ} (α : ℝ)
    (c v : ℕ → (Fin d → ℝ)) (s γ : ℕ → ℝ) (v_t : Fin d → ℝ) :
    ℕ → ℝ → (Fin d → ℝ) → Finset ℕ → ℕ
  | 0, _, _, _ => 0
  | n + 1, rem, p, A =>
    let H := stretchMetric A γ v
    let u := H⁻¹ *ᵥ v_t
    let δ := pieceStepTime α rem c v s A p u
    let p_next := p + δ • u
    let A_next := A.filter (fun i => inSlab α (c i) (v i) (s i) p_next)
    if δ < rem then
      1 + rvmMovePieces α c v s γ v_t n (rem - δ) p_next A_next
    else
      1

/-- Point `q_i` on the move trajectory at which stretch `i ∈ A` is revoked (or the endpoint
    if `i` remains active throughout the move). -/
noncomputable def rvmRevocationPoint {d : ℕ} (α : ℝ)
    (c v : ℕ → (Fin d → ℝ)) (s γ : ℕ → ℝ) (v_t : Fin d → ℝ) :
    ℕ → ℝ → (Fin d → ℝ) → Finset ℕ → ℕ → (Fin d → ℝ)
  | 0, _, p, _, _ => p
  | n + 1, rem, p, A, i =>
    let H := stretchMetric A γ v
    let u := H⁻¹ *ᵥ v_t
    let δ := pieceStepTime α rem c v s A p u
    let p_next := p + δ • u
    let A_next := A.filter (fun j => inSlab α (c j) (v j) (s j) p_next)
    if i ∈ A_next ∧ δ < rem then
      rvmRevocationPoint α c v s γ v_t n (rem - δ) p_next A_next i
    else
      p_next

/-- Time `η_i ∈ [0, rem]` at which stretch `i ∈ A` is revoked during the move. -/
noncomputable def rvmRevocationTime {d : ℕ} (α : ℝ)
    (c v : ℕ → (Fin d → ℝ)) (s γ : ℕ → ℝ) (v_t : Fin d → ℝ) :
    ℕ → ℝ → (Fin d → ℝ) → Finset ℕ → ℕ → ℝ
  | 0, _, _, _, _ => 0
  | n + 1, rem, p, A, i =>
    let H := stretchMetric A γ v
    let u := H⁻¹ *ᵥ v_t
    let δ := pieceStepTime α rem c v s A p u
    let p_next := p + δ • u
    let A_next := A.filter (fun j => inSlab α (c j) (v j) (s j) p_next)
    if i ∈ A_next ∧ δ < rem then
      δ + rvmRevocationTime α c v s γ v_t n (rem - δ) p_next A_next i
    else
      δ

/-!
## 3. Definition of Algorithm RVM(α) (Definition 1.1)
Rounds are 0-indexed (`t = 0, 1, 2, ...`), corresponding to `t + 1` in 1-indexed paper indexing:
`p_0 = 0`, `A_0 = ∅`, `H_0 = I`.
-/

/-- State of Algorithm `RVM(α)` at the start of round `t` (0-indexed):
    - `p`: current query point `p_t`
    - `A`: active stretch indices `A_t ⊆ {0, ..., t - 1}`
    - `c`: slab centers `i ↦ p_{i+1}` for stretches `i < t`
    - `s`: dual norms `i ↦ s_i` for stretches `i < t`
    - `γ`: stretch weights `i ↦ γ_i = 1 / (8 s_i^2)` for stretches `i < t` -/
structure RVMState (d : ℕ) where
  p : Fin d → ℝ
  A : Finset ℕ
  c : ℕ → (Fin d → ℝ)
  s : ℕ → ℝ
  γ : ℕ → ℝ

/-- Recursive run of Algorithm `RVM(α)` (Definition 1.1). -/
noncomputable def rvmState {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) : ℕ → RVMState d
  | 0 =>
    { p := 0
      A := ∅
      c := fun _ => 0
      s := fun _ => 0
      γ := fun _ => 0 }
  | t + 1 =>
    let st := rvmState α v t
    let (p_next, A_after) :=
      rvmMoveEval α st.c v st.s st.γ (v t) (st.A.card + 1) α st.p st.A α
    let H_after := stretchMetric A_after st.γ v
    let s_t := matNorm (H_after⁻¹) (v t)
    let γ_t := 1 / (8 * s_t ^ 2)
    { p := p_next
      A := insert t A_after
      c := Function.update st.c t p_next
      s := Function.update st.s t s_t
      γ := Function.update st.γ t γ_t }

/-- Query point `p_t` at the start of round `t`. -/
noncomputable def rvmQuery {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) : Fin d → ℝ :=
  (rvmState α v t).p

/-- Active stretch set `A_t` at the start of round `t`. -/
noncomputable def rvmActiveSet {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) : Finset ℕ :=
  (rvmState α v t).A

/-- Continuous path `hat_p_t(η)` during the move of round `t` for `η ∈ [0, α]`. -/
noncomputable def rvmPath {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) (η : ℝ) : Fin d → ℝ :=
  let st := rvmState α v t
  (rvmMoveEval α st.c v st.s st.γ (v t) (st.A.card + 1) α st.p st.A η).1

/-- Active stretch set `hat_A_t(η)` at time `η ∈ [0, α]` during the move of round `t`. -/
noncomputable def rvmPathActiveSet {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) (η : ℝ) :
    Finset ℕ :=
  let st := rvmState α v t
  (rvmMoveEval α st.c v st.s st.γ (v t) (st.A.card + 1) α st.p st.A η).2

/-- Metric `hat_H_t(η) = I + ∑_{i ∈ hat_A_t(η)} γ_i v_i v_i^T` at time `η ∈ [0, α]` of round `t`. -/
noncomputable def rvmPathMetric {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) (η : ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  let st := rvmState α v t
  stretchMetric (rvmPathActiveSet α v t η) st.γ v

/-- Dual length `σ_t(η) = ‖v_t‖_{hat_H_t(η)^{-1}}` at time `η ∈ [0, α]` of round `t`. -/
noncomputable def rvmDualLength {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) (η : ℝ) : ℝ :=
  matNorm ((rvmPathMetric α v t η)⁻¹) (v t)

/-- Dual length `s_t = ‖v_t‖_{hat_H_t(α)^{-1}}` at the end of the move in round `t`. -/
noncomputable def rvmStepNorm {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) : ℝ :=
  rvmDualLength α v t α

/-- Stretch weight `γ_t = 1 / (8 s_t^2)` made at the end of round `t`. -/
noncomputable def rvmWeight {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) : ℝ :=
  1 / (8 * (rvmStepNorm α v t) ^ 2)

/-- Metric `H_t = I + ∑_{i ∈ A_t} γ_i v_i v_i^T` at the start of round `t`. -/
noncomputable def rvmMetric {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  let st := rvmState α v t
  stretchMetric st.A st.γ v

/-- Slab `L_t = {p ∈ ℝ^d : |⟨p - p_{t+1}, v_t⟩| < 4 α s_t^2}` of the stretch made in round `t`. -/
def rvmSlab {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) (p : Fin d → ℝ) : Prop :=
  inSlab α (rvmQuery α v (t + 1)) (v t) (rvmStepNorm α v t) p

/-- Set of stretches `A_t \ hat_A_t(α)` revoked during round `t`. -/
noncomputable def rvmRevokedInRound {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) : Finset ℕ :=
  rvmActiveSet α v t \ rvmPathActiveSet α v t α

/-- Number of stretches `k_t = |A_t \ hat_A_t(α)|` revoked during round `t`. -/
noncomputable def rvmRevokedCount {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) : ℕ :=
  (rvmRevokedInRound α v t).card

/-- Number of linear pieces in the path `hat_p_t` during round `t`. -/
noncomputable def rvmRoundPieces {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) : ℕ :=
  let st := rvmState α v t
  rvmMovePieces α st.c v st.s st.γ (v t) (st.A.card + 1) α st.p st.A

/-- Point `q_i` on `hat_p_t` where stretch `i ∈ A_t \ hat_A_t(α)` is revoked in round `t`. -/
noncomputable def rvmRoundRevokePoint {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t i : ℕ) :
    Fin d → ℝ :=
  let st := rvmState α v t
  rvmRevocationPoint α st.c v st.s st.γ (v t) (st.A.card + 1) α st.p st.A i

/-- Time `η_i ∈ [0, α]` at which stretch `i ∈ A_t \ hat_A_t(α)` is revoked in round `t`. -/
noncomputable def rvmRoundRevokeTime {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t i : ℕ) : ℝ :=
  let st := rvmState α v t
  rvmRevocationTime α st.c v st.s st.γ (v t) (st.A.card + 1) α st.p st.A i

/-- Active set induced by a candidate path `q : ℝ → ℝ^d` in round `t` (Equation (3)):
    `{i ∈ A_t : ∀ τ ∈ [0, η], q(τ) ∈ L_i}`. -/
noncomputable def candActiveSet {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ)
    (q : ℝ → (Fin d → ℝ)) (η : ℝ) : Finset ℕ :=
  open Classical in
  (rvmActiveSet α v t).filter (fun i => ∀ τ ∈ Set.Icc 0 η, rvmSlab α v i (q τ))

/-- Predicate stating that a candidate path `q : ℝ → ℝ^d` solves the continuous move equations
    (Equation (3)) of round `t` on `[0, α]`: `q` is continuous on `[0, α]`, starts at `q(0) = p_t`,
    and has right derivative `(I + ∑_{i ∈ candActiveSet(q, η)} γ_i v_i v_i^T)^{-1} v_t` on `[0, α)`. -/
def SolvesMove {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) (q : ℝ → (Fin d → ℝ)) : Prop :=
  ContinuousOn q (Set.Icc 0 α) ∧ q 0 = rvmQuery α v t ∧
  ∀ η ∈ Set.Ico 0 α, HasDerivWithinAt q
    ((stretchMetric (candActiveSet α v t q η) (rvmWeight α v) v)⁻¹ *ᵥ v t) (Set.Ici η) η

/-!
## 3b. Incremental Sherman–Morrison Implementation & Instrumented Scalar-Operation Counting (Remark 2.4)
-/

/-- Instrumented scalar-operation computation returning a result `val : α` together with the
    accumulated count `ops : ℕ` of primitive scalar operations (arithmetic `+`, `-`, `*`, `/`,
    `-·`, `|·|`, `√·` and comparisons `<`, `=`, `min`). The constructor `CostM.mk` is `private` so
    operation counts outside this module can only be constructed by composing primitive scalar
    operations via `CostM.pure`, `CostM.bind`, and `CostM.foldl`. -/
structure CostM (α : Type*) where
  private mk ::
  val : α
  ops : ℕ

/-- Pure value in `CostM` charging `0` scalar operations. -/
def CostM.pure {α : Type*} (a : α) : CostM α := ⟨a, 0⟩

/-- Sequential composition in `CostM`, summing the operation counts of both steps. -/
def CostM.bind {α β : Type*} (m : CostM α) (f : α → CostM β) : CostM β :=
  let r := f m.val
  ⟨r.val, m.ops + r.ops⟩

/-- Sequential left fold in `CostM` over a list, threading both the accumulator value and the
    accumulated scalar-operation count step by step via `CostM.bind`. -/
def CostM.foldl {α β : Type*} (f : α → β → CostM α) : α → List β → CostM α
  | a, [] => CostM.pure a
  | a, x :: xs => CostM.bind (f a x) (fun a' => CostM.foldl f a' xs)

/-- Scalar addition (`1` primitive operation). -/
noncomputable def ramAdd (a b : ℝ) : CostM ℝ := ⟨a + b, 1⟩

/-- Scalar subtraction (`1` primitive operation). -/
noncomputable def ramSub (a b : ℝ) : CostM ℝ := ⟨a - b, 1⟩

/-- Scalar multiplication (`1` primitive operation). -/
noncomputable def ramMul (a b : ℝ) : CostM ℝ := ⟨a * b, 1⟩

/-- Scalar division (`1` primitive operation). -/
noncomputable def ramDiv (a b : ℝ) : CostM ℝ := ⟨a / b, 1⟩

/-- Scalar negation (`1` primitive operation). -/
noncomputable def ramNeg (a : ℝ) : CostM ℝ := ⟨-a, 1⟩

/-- Scalar absolute value (`1` primitive operation). -/
noncomputable def ramAbs (a : ℝ) : CostM ℝ := ⟨|a|, 1⟩

/-- Scalar square root (`1` primitive operation; used only in `ramNormalizeDiff` in the OILO
    reduction, never in `RVM(α)` or `RVMSkip(α)`). -/
noncomputable def ramSqrt (a : ℝ) : CostM ℝ := ⟨Real.sqrt a, 1⟩

/-- Scalar strict inequality comparison (`1` primitive comparison). -/
noncomputable def ramLt (a b : ℝ) : CostM Bool := open Classical in ⟨decide (a < b), 1⟩

/-- Scalar equality comparison (`1` primitive comparison). -/
noncomputable def ramEq (a b : ℝ) : CostM Bool := open Classical in ⟨decide (a = b), 1⟩

/-- Scalar minimum (`1` primitive comparison). -/
noncomputable def ramMin (a b : ℝ) : CostM ℝ := ⟨min a b, 1⟩

/-- Vector addition in `ℝ^d`, folding `ramAdd` across `List.finRange d` (`d` ops). -/
noncomputable def ramVecAdd {d : ℕ} (u w : Fin d → ℝ) : CostM (Fin d → ℝ) :=
  CostM.foldl (fun acc j =>
    CostM.bind (ramAdd (u j) (w j)) (fun s =>
      CostM.pure (Function.update acc j s))) 0 (List.finRange d)

/-- Vector subtraction in `ℝ^d`, folding `ramSub` across `List.finRange d` (`d` ops). -/
noncomputable def ramVecSub {d : ℕ} (u w : Fin d → ℝ) : CostM (Fin d → ℝ) :=
  CostM.foldl (fun acc j =>
    CostM.bind (ramSub (u j) (w j)) (fun s =>
      CostM.pure (Function.update acc j s))) 0 (List.finRange d)

/-- Scalar–vector multiplication in `ℝ^d`, folding `ramMul` across `List.finRange d` (`d` ops). -/
noncomputable def ramVecSmul {d : ℕ} (c : ℝ) (u : Fin d → ℝ) : CostM (Fin d → ℝ) :=
  CostM.foldl (fun acc j =>
    CostM.bind (ramMul c (u j)) (fun s =>
      CostM.pure (Function.update acc j s))) 0 (List.finRange d)

/-- Vector equality test in `ℝ^d`, folding `ramEq` across `List.finRange d` (`d` ops). -/
noncomputable def ramVecEq {d : ℕ} (u w : Fin d → ℝ) : CostM Bool :=
  CostM.foldl (fun acc j =>
    CostM.bind (ramEq (u j) (w j)) (fun eq_j =>
      CostM.pure (acc && eq_j))) true (List.finRange d)

/-- Inner product in `ℝ^d`, folding `ramMul` and `ramAdd` across `List.finRange d` (`2 d` ops). -/
noncomputable def ramDot {d : ℕ} (u w : Fin d → ℝ) : CostM ℝ :=
  CostM.foldl (fun acc j =>
    CostM.bind (ramMul (u j) (w j)) (fun prod =>
      ramAdd acc prod)) 0 (List.finRange d)

/-- Matrix–vector product in `ℝ^{d×d}`, folding `ramDot` over rows `List.finRange d` (`2 d^2` ops). -/
noncomputable def ramMatVec {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    CostM (Fin d → ℝ) :=
  CostM.foldl (fun acc i =>
    CostM.bind (ramDot (M i) v) (fun row =>
      CostM.pure (Function.update acc i row))) 0 (List.finRange d)

/-- Single entry `M_{i,j} + c (w_i w_j)` of a rank-one matrix addition, chaining two scalar
    multiplications and one scalar addition (`3` ops per entry). -/
noncomputable def ramRankOneAddEntry {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (w : Fin d → ℝ)
    (i j : Fin d) : CostM ℝ :=
  CostM.bind (ramMul (w i) (w j)) (fun p =>
    CostM.bind (ramMul c p) (fun cp =>
      ramAdd (M i j) cp))

/-- Single entry `M_{i,j} - c (w_i w_j)` of a rank-one matrix subtraction, chaining two scalar
    multiplications and one scalar subtraction (`3` ops per entry). -/
noncomputable def ramRankOneSubEntry {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (w : Fin d → ℝ)
    (i j : Fin d) : CostM ℝ :=
  CostM.bind (ramMul (w i) (w j)) (fun p =>
    CostM.bind (ramMul c p) (fun cp =>
      ramSub (M i j) cp))

/-- Rank-one matrix addition `M + c w w^T` in `ℝ^{d×d}`, folding `ramRankOneAddEntry` over all
    `d × d` entries (`3 d^2` ops). -/
noncomputable def ramRankOneAdd {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (w : Fin d → ℝ) :
    CostM (Matrix (Fin d) (Fin d) ℝ) :=
  CostM.foldl (fun accRow i =>
    CostM.bind (CostM.foldl (fun accCol j =>
      CostM.bind (ramRankOneAddEntry M c w i j) (fun v_ij =>
        CostM.pure (Function.update accCol j v_ij))) 0 (List.finRange d))
      (fun newRow => CostM.pure (Function.update accRow i newRow))) M (List.finRange d)

/-- Rank-one matrix subtraction `M - c w w^T` in `ℝ^{d×d}`, folding `ramRankOneSubEntry` over all
    `d × d` entries (`3 d^2` ops). -/
noncomputable def ramRankOneSub {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (w : Fin d → ℝ) :
    CostM (Matrix (Fin d) (Fin d) ℝ) :=
  CostM.foldl (fun accRow i =>
    CostM.bind (CostM.foldl (fun accCol j =>
      CostM.bind (ramRankOneSubEntry M c w i j) (fun v_ij =>
        CostM.pure (Function.update accCol j v_ij))) 0 (List.finRange d))
      (fun newRow => CostM.pure (Function.update accRow i newRow))) M (List.finRange d)

/-- Rank-one Sherman–Morrison downdate of `M = H⁻¹` upon revoking stretch `i` with weight `γ_i`
    and direction `v_i`: `M + (γ_i / (1 - γ_i ⟨v_i, M v_i⟩)) (M v_i)(M v_i)^T` (Remark 2.4). -/
noncomputable def shermanMorrisonDowndate {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (γ_i : ℝ) (v_i : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  let w := M *ᵥ v_i
  M + (γ_i / (1 - γ_i * dotProduct v_i w)) • Matrix.vecMulVec w w

/-- Sequential application of `shermanMorrisonDowndate` over a finite set `R` of revoked stretches. -/
noncomputable def shermanMorrisonDowndateSet {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (γ : ℕ → ℝ) (v : ℕ → (Fin d → ℝ)) (R : Finset ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  (R.sort (· ≤ ·)).foldl (fun Acc i => shermanMorrisonDowndate Acc (γ i) (v i)) M

/-- Rank-one Sherman–Morrison update of `M = hat_H_t(α)⁻¹` upon creating stretch `t` from the
    already-computed vector `w = M v_t` and squared dual norm `s_sq = ⟨v_t, w⟩`:
    `M - (1 / (9 s_sq)) w w^T` (Remark 2.4). -/
noncomputable def shermanMorrisonStretchUpdate {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (s_sq : ℝ) (w : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  let c := 1 / (9 * s_sq)
  M - c • Matrix.vecMulVec w w

/-- Exit time of stretch `i` from cached squared step norm `s_sq i = s_i^2`, cached displacement
    `φ_i = ⟨p - p_{i+1}, v_i⟩`, and precomputed inner product `β_i = ⟨u, v_i⟩` (Remark 2.4). -/
noncomputable def fastPieceExitDelta (α rem : ℝ) (s_sq φ β : ℕ → ℝ) (i : ℕ) : ℝ :=
  if β i > 0 then (4 * α * s_sq i - φ i) / β i
  else if β i < 0 then (-4 * α * s_sq i - φ i) / β i
  else rem

/-- Instrumented computation of `fastPieceExitDelta α rem s_sq φ β i` directly from stored
    `s_sq i = s_i^2`, charging all sign comparisons (`ramLt 0 (β i)`, `ramLt (β i) 0`) and rational
    scalar arithmetic operations (at most `7` ops). -/
noncomputable def ramFastPieceExitDelta (α rem : ℝ) (s_sq φ β : ℕ → ℝ) (i : ℕ) : CostM ℝ :=
  CostM.bind (ramLt 0 (β i)) (fun h_pos =>
    if h_pos then
      CostM.bind (ramMul α (s_sq i)) (fun as2 =>
      CostM.bind (ramMul 4 as2) (fun num0 =>
      CostM.bind (ramSub num0 (φ i)) (fun num =>
      ramDiv num (β i))))
    else
      CostM.bind (ramLt (β i) 0) (fun h_neg =>
        if h_neg then
          CostM.bind (ramMul α (s_sq i)) (fun as2 =>
          CostM.bind (ramMul 4 as2) (fun pos_num0 =>
          CostM.bind (ramNeg pos_num0) (fun num0 =>
          CostM.bind (ramSub num0 (φ i)) (fun num =>
          ramDiv num (β i)))))
        else
          CostM.pure rem))

/-- Duration `δ` of the current linear piece of the move computed from stored squared step norms
    `s_sq i = s_i^2`, cached displacements `φ_i = ⟨p - p_{i+1}, v_i⟩`, and precomputed inner
    products `β_i = ⟨u, v_i⟩` (Remark 2.4). -/
noncomputable def fastPieceStepTime (α rem : ℝ)
    (s_sq φ : ℕ → ℝ) (A : Finset ℕ) (β : ℕ → ℝ) : ℝ :=
  A.fold min rem (fun i => fastPieceExitDelta α rem s_sq φ β i)

/-- Instrumented computation of the inner products `β_i = ⟨u, v_i⟩` for active stretches `i ∈ A`
    only (initializing outside `A` to `0`), folding `ramDot` over `A.sort (· ≤ ·)` (`2 d |A|` ops). -/
noncomputable def ramComputeBeta {d : ℕ} (u : Fin d → ℝ) (v : ℕ → (Fin d → ℝ)) (A : Finset ℕ) :
    CostM (ℕ → ℝ) :=
  CostM.foldl (fun acc i =>
    CostM.bind (ramDot u (v i)) (fun b =>
      CostM.pure (Function.update acc i b))) (fun _ => 0) (A.sort (· ≤ ·))

/-- Instrumented computation of the piece duration `δ = fastPieceStepTime α rem s_sq φ A β`,
    folding `ramFastPieceExitDelta` and `ramMin` over `A.sort (· ≤ ·)` (at most `8 |A|` ops). -/
noncomputable def ramFastPieceStepTime (α rem : ℝ)
    (s_sq φ : ℕ → ℝ) (A : Finset ℕ) (β : ℕ → ℝ) : CostM ℝ :=
  CostM.foldl (fun acc i =>
    CostM.bind (ramFastPieceExitDelta α rem s_sq φ β i) (fun d_i =>
      ramMin acc d_i)) rem (A.sort (· ≤ ·))

/-- Instrumented update `φ_i + δ β_i` of cached slab displacement `φ_i` using the precomputed inner
    product `β_i = ⟨u, v_i⟩` (`2` ops). -/
noncomputable def ramPhiUpdate (φ : ℕ → ℝ) (δ : ℝ) (β : ℕ → ℝ) (i : ℕ) : CostM ℝ :=
  CostM.bind (ramMul δ (β i)) (fun db => ramAdd (φ i) db)

/-- Instrumented slab membership check `|phi_i| < 4 α s_sq i` using stored `s_sq i = s_i^2`,
    charging `ramAbs`, two scalar multiplications, and `ramLt` (`4` ops). -/
noncomputable def ramSlabCheck (α : ℝ) (s_sq : ℕ → ℝ) (phi_i : ℝ) (i : ℕ) : CostM Bool :=
  CostM.bind (ramAbs phi_i) (fun a =>
  CostM.bind (ramMul α (s_sq i)) (fun as2 =>
  CostM.bind (ramMul 4 as2) (fun rhs =>
  ramLt a rhs)))

/-- Instrumented single pass over `i ∈ A.sort (· ≤ ·)` that updates `φ_i ← φ_i + δ β_i`, tests
    `|φ_i| < 4 α s_sq i`, and retains `(A_next, φ_next)` on `A_next` (setting `φ_next` to `0`
    outside `A_next`), charging `6 |A|` scalar operations. -/
noncomputable def ramUpdateSlabs (α δ : ℝ) (s_sq φ β : ℕ → ℝ) (A : Finset ℕ) :
    CostM (Finset ℕ × (ℕ → ℝ)) :=
  CostM.foldl (fun acc i =>
    CostM.bind (ramPhiUpdate φ δ β i) (fun phi_i =>
    CostM.bind (ramSlabCheck α s_sq phi_i i) (fun keep =>
      CostM.pure (if keep then (insert i acc.1, Function.update acc.2 i phi_i) else acc))))
    (∅, fun _ => 0) (A.sort (· ≤ ·))

/-- Instrumented execution of one rank-one Sherman–Morrison downdate: computes `w = M v_i`
    (`2 d^2` ops), `q = ⟨v_i, w⟩` (`2 d` ops), `c = γ_i / (1 - γ_i q)` (`3` ops), and
    `M + c w w^T` (`3 d^2` ops), totaling `5 d^2 + 2 d + 3` ops. -/
noncomputable def ramDowndate {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (γ_i : ℝ) (v_i : Fin d → ℝ) :
    CostM (Matrix (Fin d) (Fin d) ℝ) :=
  CostM.bind (ramMatVec M v_i) (fun w =>
  CostM.bind (ramDot v_i w) (fun q =>
  CostM.bind (ramMul γ_i q) (fun gq =>
  CostM.bind (ramSub 1 gq) (fun den =>
  CostM.bind (ramDiv γ_i den) (fun c =>
  ramRankOneAdd M c w)))))

/-- Instrumented sequential execution of `ramDowndate` over a finite set `R` of revoked stretches
    via `CostM.foldl`. -/
noncomputable def shermanMorrisonDowndateSetWithCost {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (γ : ℕ → ℝ) (v : ℕ → (Fin d → ℝ))
    (R : Finset ℕ) : CostM (Matrix (Fin d) (Fin d) ℝ) :=
  CostM.foldl (fun AccM i => ramDowndate AccM (γ i) (v i)) M (R.sort (· ≤ ·))

/-- Instrumented execution of end-of-round stretch creation in `RVM(α)` using purely rational
    arithmetic: computes `w = M_after v_t` once (`2 d^2` ops), `s_sq = ⟨v_t, w⟩` (`2 d` ops),
    `γ_t = 1 / (8 s_sq)` (`2` ops), `c = 1 / (9 s_sq)` (`2` ops), and `M_after - c w w^T` (`3 d^2` ops)
    reusing `w`, totaling `5 d^2 + 2 d + 4` ops (`0` square roots). -/
noncomputable def ramStretchCreation {d : ℕ}
    (M_after : Matrix (Fin d) (Fin d) ℝ) (v_t : Fin d → ℝ) :
    CostM (ℝ × ℝ × Matrix (Fin d) (Fin d) ℝ) :=
  CostM.bind (ramMatVec M_after v_t) (fun w =>
  CostM.bind (ramDot v_t w) (fun s_sq =>
  CostM.bind (ramMul 8 s_sq) (fun den8 =>
  CostM.bind (ramDiv 1 den8) (fun γ_t =>
  CostM.bind (ramMul 9 s_sq) (fun den9 =>
  CostM.bind (ramDiv 1 den9) (fun c =>
  CostM.bind (ramRankOneSub M_after c w) (fun M_next =>
  CostM.pure (s_sq, γ_t, M_next))))))))

/-- Instrumented execution of end-of-round conditional stretch creation in `RVMSkip(α)`
    (Proposition 3.3) using purely rational arithmetic: computes `w = M_after v_t` once (`2 d^2` ops),
    `s_sq = ⟨v_t, w⟩` (`2 d` ops), `γ_t = 1 / (8 s_sq)` (`2` ops), threshold `1 / (t + 2)^4` (`4` ops),
    comparison `1 / (t + 2)^4 < s_sq` (`1` op), and when true, `c = 1 / (9 s_sq)` (`2` ops) and
    `M_after - c w w^T` (`3 d^2` ops) reusing `w`, totaling at most `5 d^2 + 2 d + 9` ops (`0` square roots). -/
noncomputable def ramSkipStretchCreation {d : ℕ}
    (M_after : Matrix (Fin d) (Fin d) ℝ) (v_t : Fin d → ℝ) (t : ℕ) :
    CostM (Bool × ℝ × ℝ × Matrix (Fin d) (Fin d) ℝ) :=
  CostM.bind (ramMatVec M_after v_t) (fun w =>
  CostM.bind (ramDot v_t w) (fun s_sq =>
  CostM.bind (ramMul 8 s_sq) (fun den8 =>
  CostM.bind (ramDiv 1 den8) (fun γ_t =>
  CostM.bind (ramAdd (t : ℝ) 2) (fun t2 =>
  CostM.bind (ramMul t2 t2) (fun t2_sq =>
  CostM.bind (ramMul t2_sq t2_sq) (fun t2_pow4 =>
  CostM.bind (ramDiv 1 t2_pow4) (fun thresh =>
  CostM.bind (ramLt thresh s_sq) (fun keep =>
  if keep then
    CostM.bind (ramMul 9 s_sq) (fun den9 =>
    CostM.bind (ramDiv 1 den9) (fun c =>
    CostM.bind (ramRankOneSub M_after c w) (fun M_next =>
    CostM.pure (true, s_sq, γ_t, M_next))))
  else
    CostM.pure (false, s_sq, γ_t, M_after))))))))))

/-- Single `CostM.bind` chain for one linear piece of `rvmFastMove` (including any rank-one
    Sherman–Morrison downdates of stretches revoked at the end of the piece), producing both the
    updated state `(δ, p_next, A_next, M_next, φ_next)` and its accumulated scalar-operation count
    from the same computation. -/
noncomputable def ramFastPiece {d : ℕ} (α rem : ℝ) (v : ℕ → (Fin d → ℝ))
    (s_sq γ : ℕ → ℝ) (v_t : Fin d → ℝ) (p : Fin d → ℝ) (A : Finset ℕ)
    (M : Matrix (Fin d) (Fin d) ℝ) (φ : ℕ → ℝ) :
    CostM (ℝ × (Fin d → ℝ) × Finset ℕ × Matrix (Fin d) (Fin d) ℝ × (ℕ → ℝ)) :=
  CostM.bind (ramMatVec M v_t) (fun u =>
  CostM.bind (ramComputeBeta u v A) (fun β =>
  CostM.bind (ramFastPieceStepTime α rem s_sq φ A β) (fun δ =>
  CostM.bind (ramVecSmul δ u) (fun du =>
  CostM.bind (ramVecAdd p du) (fun p_next =>
  CostM.bind (ramUpdateSlabs α δ s_sq φ β A) (fun af =>
  CostM.bind (shermanMorrisonDowndateSetWithCost M γ v (A \ af.1)) (fun M_next =>
  CostM.pure (δ, p_next, af.1, M_next, af.2))))))))

/-- Matrix-inversion-free piecewise-linear move of Remark 2.4 in `CostM`, written as a single
    `CostM.bind` chain per piece via `ramFastPiece`, `ramLt`, and `ramSub`. -/
noncomputable def rvmFastMove {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ))
    (s_sq γ : ℕ → ℝ) (v_t : Fin d → ℝ) :
    ℕ → ℝ → (Fin d → ℝ) → Finset ℕ → Matrix (Fin d) (Fin d) ℝ → (ℕ → ℝ) →
    CostM ((Fin d → ℝ) × Finset ℕ × Matrix (Fin d) (Fin d) ℝ × (ℕ → ℝ))
  | 0, _, p, A, M, φ => CostM.pure (p, A, M, φ)
  | n + 1, rem, p, A, M, φ =>
    CostM.bind (ramFastPiece α rem v s_sq γ v_t p A M φ) (fun step =>
      let (δ, p_next, A_next, M_next, φ_next) := step
      CostM.bind (ramLt δ rem) (fun cont =>
        if cont then
          CostM.bind (ramSub rem δ) (fun rem' =>
            rvmFastMove α v s_sq γ v_t n rem' p_next A_next M_next φ_next)
        else
          CostM.pure (p_next, A_next, M_next, φ_next)))

/-- State of the incremental Sherman–Morrison implementation (Remark 2.4), storing `M = H_t⁻¹`,
    active cached slab displacements `φ_i = ⟨p_t - p_{i+1}, v_i⟩` for `i ∈ A_t` (`φ_i = 0` for
    `i ∉ A_t`), squared step norms `s_sq i = s_i^2`, and the instrumented scalar-operation counters
    `roundOps` and `totalOps`. -/
structure RVMFastState (d : ℕ) where
  p : Fin d → ℝ
  A : Finset ℕ
  M : Matrix (Fin d) (Fin d) ℝ
  φ : ℕ → ℝ
  c : ℕ → (Fin d → ℝ)
  s_sq : ℕ → ℝ
  γ : ℕ → ℝ
  roundOps : ℕ
  totalOps : ℕ

/-- One round of the incremental Sherman–Morrison implementation of `RVM(α)` (Remark 2.4),
    advancing `st : RVMFastState d` on direction `v t` at round index `t`. -/
noncomputable def rvmFastStep {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ)
    (st : RVMFastState d) : RVMFastState d :=
  let move := rvmFastMove α v st.s_sq st.γ (v t) (st.A.card + 1) α st.p st.A st.M st.φ
  let (p_next, A_after, M_after, φ_after) := move.val
  let stretch := ramStretchCreation M_after (v t)
  let (s_sq_t, γ_t, M_next) := stretch.val
  let round_ops := move.ops + stretch.ops
  { p := p_next
    A := insert t A_after
    M := M_next
    φ := Function.update φ_after t 0
    c := Function.update st.c t p_next
    s_sq := Function.update st.s_sq t s_sq_t
    γ := Function.update st.γ t γ_t
    roundOps := round_ops
    totalOps := st.totalOps + round_ops }

/-- Recursive run of the incremental Sherman–Morrison implementation of `RVM(α)` (Remark 2.4),
    iterating `rvmFastStep` and recording per-round and cumulative scalar-operation counts. -/
noncomputable def rvmFastState {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) : ℕ → RVMFastState d
  | 0 =>
    { p := 0
      A := ∅
      M := 1
      φ := fun _ => 0
      c := fun _ => 0
      s_sq := fun _ => 0
      γ := fun _ => 0
      roundOps := 0
      totalOps := 0 }
  | t + 1 => rvmFastStep α v t (rvmFastState α v t)

/-- Upper bound on the scalar operations (arithmetic and comparisons) executed during one linear
    piece of `rvmFastMove` (excluding rank-one downdates) with active set size `cardA = |A|`:
    - `u = M v_t`: `2 d^2` ops;
    - for each `i ∈ A`: `β_i = ⟨u, v_i⟩` (`2 d` ops, computed once on `A` and shared), exit-time
      computation and min-fold (`≤ 8` ops using stored `s_sq i = s_i^2`), displacement update
      `φ_i + δ β_i` (`2` ops), and slab filter check `|φ_next i| < 4 α s_sq i` (`4` ops using
      stored `s_sq i`), totaling `(2 d + 14) |A|` ops;
    - `p + δ u`: `2 d` ops, plus at most `2` ops for the `δ < rem` comparison and `rem - δ`. -/
def pieceArithOps (d cardA : ℕ) : ℕ :=
  2 * d ^ 2 + 2 * d + (2 * d + 14) * cardA + 2

/-- Number of scalar operations charged by one rank-one Sherman–Morrison downdate (`ramDowndate`):
    `w = M v_i` (`2 d^2` ops), `⟨v_i, w⟩` (`2 d` ops), scalar factor `γ_i / (1 - γ_i ⟨v_i, w⟩)`
    (`3` ops), and rank-one matrix update `M + c w w^T` (`3 d^2` ops, `3` ops per entry). -/
def downdateArithOps (d : ℕ) : ℕ :=
  5 * d ^ 2 + 2 * d + 3

/-- Number of scalar operations charged by end-of-round stretch creation (`ramStretchCreation`):
    `w = M_after v_t` computed once (`2 d^2` ops), `s_sq = ⟨v_t, w⟩` (`2 d` ops),
    `γ_t = 1 / (8 s_sq)` and `c = 1 / (9 s_sq)` (`4` ops), and rank-one matrix update
    `M_after - c w w^T` reusing `w` (`3 d^2` ops, `3` ops per entry). -/
def stretchArithOps (d : ℕ) : ℕ :=
  5 * d ^ 2 + 2 * d + 4

/-- Upper bound on the scalar operations for end-of-round conditional stretch creation in
    `RVMSkip(α)` (`ramSkipStretchCreation`), which adds `5` operations (`4` arithmetic ops and `1`
    comparison) to test `(t + 2)^{-4} < s_sq`. -/
def skipStretchArithOps (d : ℕ) : ℕ :=
  5 * d ^ 2 + 2 * d + 9

/-- Instrumented scalar operations (arithmetic and comparisons) performed by `rvmFastState` in
    round `t` of `RVM(α)` (Remark 2.4 & Theorem 2.1). -/
noncomputable def rvmRoundArithOps {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) : ℕ :=
  (rvmFastState α v (t + 1)).roundOps

/-- Instrumented cumulative scalar operations (arithmetic and comparisons) performed by
    `rvmFastState` over the first `T` rounds of `RVM(α)`. -/
noncomputable def rvmTotalArithOps {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (T : ℕ) : ℕ :=
  (rvmFastState α v T).totalOps

/-!
## 4. Analysis Quantities: Loss, Regret, Displacement, Ledger, and Potential (Section 2)
-/

/-- Per-round loss `r_t = ⟨w* - p_t, v_t⟩`. -/
noncomputable def rvmLoss {d : ℕ} (α : ℝ) (w_star : Fin d → ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) :
    ℝ :=
  dotProduct (w_star - rvmQuery α v t) (v t)

/-- Cumulative regret `Reg_T = ∑_{t=0}^{T-1} r_t`. -/
noncomputable def rvmRegret {d : ℕ} (α : ℝ) (w_star : Fin d → ℝ) (v : ℕ → (Fin d → ℝ)) (T : ℕ) :
    ℝ :=
  ∑ t ∈ Finset.range T, rvmLoss α w_star v t

/-- Distance `ξ_t = ⟨p_{t+1} - p_t, v_t⟩` moved by the query along `v_t` in round `t`. -/
noncomputable def rvmXi {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) : ℝ :=
  dotProduct (rvmQuery α v (t + 1) - rvmQuery α v t) (v t)

/-- Endpoint `q_t` of stretch `t < T` at horizon `T`: the point at which stretch `t` was revoked
    if it was revoked by the end of the first `T` rounds, and `p_T` (paper: `p_{T+1}`) otherwise. -/
noncomputable def rvmStretchEndPoint {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) :
    ℕ → ℕ → (Fin d → ℝ)
  | 0, _ => 0
  | r + 1, t =>
    if r ≤ t then
      rvmQuery α v (r + 1)
    else if t ∈ rvmRevokedInRound α v r then
      rvmRoundRevokePoint α v r t
    else if t ∈ rvmPathActiveSet α v r α then
      rvmQuery α v (r + 1)
    else
      rvmStretchEndPoint α v r t

/-- Displacement `Δ_t = ⟨q_t - p_{t+1}, v_t⟩` of stretch `t` from the point where it was made
    (Equation (5)). -/
noncomputable def rvmDelta {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (T t : ℕ) : ℝ :=
  dotProduct (rvmStretchEndPoint α v T t - rvmQuery α v (t + 1)) (v t)

/-- Lifetime contribution `Λ_t = -2 α r_t + α^2 s_t^2 + γ_t (2 Δ_t r_t - Δ_t (Δ_t + 2 ξ_t))`
    of stretch `t` in the ledger at horizon `T` (Equation (6)). -/
noncomputable def rvmLambda {d : ℕ} (α : ℝ) (w_star : Fin d → ℝ) (v : ℕ → (Fin d → ℝ))
    (T t : ℕ) : ℝ :=
  let r_t := rvmLoss α w_star v t
  let s_t := rvmStepNorm α v t
  let γ_t := rvmWeight α v t
  let ξ_t := rvmXi α v t
  let Δ_t := rvmDelta α v T t
  (-2) * α * r_t + α ^ 2 * s_t ^ 2 + γ_t * (2 * Δ_t * r_t - Δ_t * (Δ_t + 2 * ξ_t))

/-- Monotone metric `bar_H_t = I + ∑_{i ∈ A_T, i < t} γ_i v_i v_i^T` built from the stretches
    that survive to the end of the `T` rounds (Section 2.4; paper: `A_{T+1}`). -/
noncomputable def rvmSurvivingMetric {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (T t : ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  stretchMetric ((rvmActiveSet α v T).filter (· < t)) (rvmWeight α v) v

/-!
## 4b. Online Inverse Linear Optimization Reduction & Proper Learner (Section 1 & Corollary 2.2)
-/

/-- Index `g(t)` of the cutting-plane round fed by online inverse linear optimization round `t`,
    equal to the number of non-tie rounds `s < t` with `x_s ≠ x̂_s` (Section 1 & Corollary 2.2:
    "Rounds with `x_t = x̂_t` are not rounds of the game"). -/
noncomputable def oiloGameIndex {d : ℕ} (x x_hat : ℕ → (Fin d → ℝ)) (t : ℕ) : ℕ :=
  open Classical in ((Finset.range t).filter (fun s => x s ≠ x_hat s)).card

/-- Hypothesis vector `ŵ_t ≠ 0` committed to by the proper learner at the start of OILO round `t`:
    equal to the current RVM query `p_{g(t)}` when nonzero, and a fixed nonzero vector `e` when
    `p_{g(t)} = 0` (Section 1, "Reduction to a cutting-plane game"). -/
noncomputable def oiloHypothesis {d : ℕ} (α : ℝ) (e : Fin d → ℝ)
    (x x_hat u : ℕ → (Fin d → ℝ)) (t : ℕ) : Fin d → ℝ :=
  open Classical in
  let p_t := rvmQuery α u (oiloGameIndex x x_hat t)
  if p_t = 0 then e else p_t

/-- Linear optimization oracle selecting a maximizer `x̂ ∈ argmax_{y ∈ S} ⟨w, y⟩` over a set
    `S ⊆ ℝ^d` when a maximizer exists (guaranteed whenever `S` is compact and nonempty), and `0`
    otherwise. -/
noncomputable def linearMaximizer {d : ℕ} (w : Fin d → ℝ) (S : Set (Fin d → ℝ)) : Fin d → ℝ :=
  open Classical in
  if h : ∃ x ∈ S, ∀ y ∈ S, dotProduct w y ≤ dotProduct w x then Classical.choose h else 0

/-- Instrumented computation of the normalized difference `(x_t - x̂_t) / ‖x_t - x̂_t‖_2` on a non-tie
    round of OILO: `δ = x_t - x̂_t` (`d` ops), `‖δ‖^2 = ⟨δ, δ⟩` (`2 d` ops), `√(‖δ‖^2)` (`1` op),
    `1 / √(‖δ‖^2)` (`1` op), and `(1 / ‖δ‖) • δ` (`d` ops), totaling `4 d + 2` ops. -/
noncomputable def ramNormalizeDiff {d : ℕ} (x_t x_hat_t : Fin d → ℝ) : CostM (Fin d → ℝ) :=
  CostM.bind (ramVecSub x_t x_hat_t) (fun δ =>
  CostM.bind (ramDot δ δ) (fun n_sq =>
  CostM.bind (ramSqrt n_sq) (fun n =>
  CostM.bind (ramDiv 1 n) (fun inv_n =>
  ramVecSmul inv_n δ))))

/-- Total scalar operations (arithmetic and comparisons) in the OILO reduction on a non-tie round:
    `p_t = 0` check (`d` comparisons), `x_t = x̂_t` check (`d` comparisons), and `ramNormalizeDiff`
    (`4 d + 2` arithmetic operations), totaling `6 d + 2` operations. -/
def oiloReductionArithOps (d : ℕ) : ℕ :=
  6 * d + 2

/-- Instrumented scalar operations (arithmetic and comparisons) in round `t` of the protocol-level
    OILO reduction (excluding the single linear optimization oracle call over `X_t`): `2 d`
    comparison operations (`p_t = 0` and `x_t = x̂_t`) on a skipped tie round `x_t = x̂_t`, and
    those `2 d` comparisons plus `(ramNormalizeDiff (x t) (x_hat t)).ops + rvmRoundArithOps α u (oiloGameIndex x x_hat t)`
    on a non-tie round. -/
noncomputable def oiloRoundArithOps {d : ℕ} (α : ℝ)
    (x x_hat u : ℕ → (Fin d → ℝ)) (t : ℕ) : ℕ :=
  let g := oiloGameIndex x x_hat t
  let p_t := (rvmFastState α u g).p
  let hyp_cmp := ramVecEq p_t 0
  let tie_cmp := ramVecEq (x t) (x_hat t)
  if tie_cmp.val then
    hyp_cmp.ops + tie_cmp.ops
  else
    hyp_cmp.ops + tie_cmp.ops +
      (ramNormalizeDiff (x t) (x_hat t)).ops +
      rvmRoundArithOps α u g

/-- Cumulative scalar operations (arithmetic and comparisons) over the first `T` rounds of the
    protocol-level OILO reduction. -/
noncomputable def oiloTotalArithOps {d : ℕ} (α : ℝ)
    (x x_hat u : ℕ → (Fin d → ℝ)) (T : ℕ) : ℕ :=
  ∑ t ∈ Finset.range T, oiloRoundArithOps α x x_hat u t

/-- State of the closed-loop deterministic proper learner for online inverse linear optimization
    (Section 1 & Corollary 2.2), carrying the cutting-plane game index `g`, the direction sequence
    `u`, the incremental Sherman–Morrison state `fast : RVMFastState d`, and the learner's own
    instrumented per-round and cumulative scalar-operation counters `roundOps` and `totalOps`. -/
structure OILOLearnerState (d : ℕ) where
  g : ℕ
  u : ℕ → (Fin d → ℝ)
  fast : RVMFastState d
  roundOps : ℕ
  totalOps : ℕ

/-- Closed-loop execution of the deterministic proper learner for online inverse linear optimization
    at the start of round `t` (Section 1 & Corollary 2.2), constructed directly from the sequence of
    action sets `X` and expert choices `x`:
    In round `t`, the learner reads `st.fast.p` from its carried `RVMFastState`, tests `st.fast.p = 0`
    via `ramVecEq`, sets `ŵ_t = e` if `st.fast.p = 0` and `ŵ_t = st.fast.p` otherwise, recommends
    `x̂_t = linearMaximizer ŵ_t (X t)`, tests `x_t = x̂_t` via `ramVecEq`, skips the cutting-plane
    step if `x_t = x̂_t`, and otherwise normalizes `x_t - x̂_t` via `ramNormalizeDiff` and advances
    `st.fast` by one incremental Sherman–Morrison round via `rvmFastStep`. -/
noncomputable def oiloLearnerState {d : ℕ} (α : ℝ) (e : Fin d → ℝ)
    (X : ℕ → Set (Fin d → ℝ)) (x : ℕ → (Fin d → ℝ)) :
    ℕ → OILOLearnerState d
  | 0 =>
    let u₀ : ℕ → (Fin d → ℝ) := fun _ => (Real.sqrt (dotProduct e e))⁻¹ • e
    { g := 0
      u := u₀
      fast := rvmFastState α u₀ 0
      roundOps := 0
      totalOps := 0 }
  | t + 1 =>
    let st := oiloLearnerState α e X x t
    let hyp_cmp := ramVecEq st.fast.p 0
    let w_hat := if hyp_cmp.val then e else st.fast.p
    let x_hat_t := linearMaximizer w_hat (X t)
    let tie_cmp := ramVecEq (x t) x_hat_t
    if tie_cmp.val then
      let r_ops := hyp_cmp.ops + tie_cmp.ops
      { g := st.g
        u := st.u
        fast := st.fast
        roundOps := r_ops
        totalOps := st.totalOps + r_ops }
    else
      let norm_step := ramNormalizeDiff (x t) x_hat_t
      let u_next := Function.update st.u st.g norm_step.val
      let fast_next := rvmFastStep α u_next st.g st.fast
      let r_ops := hyp_cmp.ops + tie_cmp.ops + norm_step.ops + fast_next.roundOps
      { g := st.g + 1
        u := u_next
        fast := fast_next
        roundOps := r_ops
        totalOps := st.totalOps + r_ops }

/-- Game index `g_t` of the closed-loop proper OILO learner at the start of round `t`. -/
noncomputable def oiloLearnerGameIndex {d : ℕ} (α : ℝ) (e : Fin d → ℝ)
    (X : ℕ → Set (Fin d → ℝ)) (x : ℕ → (Fin d → ℝ)) (t : ℕ) : ℕ :=
  (oiloLearnerState α e X x t).g

/-- Unit direction sequence `u^{(t)}` maintained by the closed-loop proper OILO learner at round `t`. -/
noncomputable def oiloLearnerDirections {d : ℕ} (α : ℝ) (e : Fin d → ℝ)
    (X : ℕ → Set (Fin d → ℝ)) (x : ℕ → (Fin d → ℝ)) (t : ℕ) : ℕ → (Fin d → ℝ) :=
  (oiloLearnerState α e X x t).u

/-- Incremental Sherman–Morrison state `fast` carried by the closed-loop proper OILO learner at the
    start of round `t`. -/
noncomputable def oiloLearnerFastState {d : ℕ} (α : ℝ) (e : Fin d → ℝ)
    (X : ℕ → Set (Fin d → ℝ)) (x : ℕ → (Fin d → ℝ)) (t : ℕ) : RVMFastState d :=
  (oiloLearnerState α e X x t).fast

/-- Cutting-plane query `p_{g_t}` read directly from the `RVMFastState` carried by the closed-loop
    proper OILO learner at round `t`. -/
noncomputable def oiloLearnerQuery {d : ℕ} (α : ℝ) (e : Fin d → ℝ)
    (X : ℕ → Set (Fin d → ℝ)) (x : ℕ → (Fin d → ℝ)) (t : ℕ) : Fin d → ℝ :=
  (oiloLearnerState α e X x t).fast.p

/-- Nonzero hypothesis vector `ŵ_t` committed to by the closed-loop proper OILO learner at round `t`. -/
noncomputable def oiloLearnerHypothesis {d : ℕ} (α : ℝ) (e : Fin d → ℝ)
    (X : ℕ → Set (Fin d → ℝ)) (x : ℕ → (Fin d → ℝ)) (t : ℕ) : Fin d → ℝ :=
  let p_t := oiloLearnerQuery α e X x t
  if (ramVecEq p_t 0).val then e else p_t

/-- Action `x̂_t ∈ argmax_{y ∈ X_t} ⟨ŵ_t, y⟩` recommended by the closed-loop proper OILO learner at
    round `t`. -/
noncomputable def oiloLearnerAction {d : ℕ} (α : ℝ) (e : Fin d → ℝ)
    (X : ℕ → Set (Fin d → ℝ)) (x : ℕ → (Fin d → ℝ)) (t : ℕ) : Fin d → ℝ :=
  linearMaximizer (oiloLearnerHypothesis α e X x t) (X t)

/-- Instrumented scalar operations executed by the closed-loop proper OILO learner in round `t`. -/
noncomputable def oiloLearnerRoundArithOps {d : ℕ} (α : ℝ) (e : Fin d → ℝ)
    (X : ℕ → Set (Fin d → ℝ)) (x : ℕ → (Fin d → ℝ)) (t : ℕ) : ℕ :=
  (oiloLearnerState α e X x (t + 1)).roundOps

/-- Instrumented cumulative scalar operations executed by the closed-loop proper OILO learner over
    the first `T` rounds. -/
noncomputable def oiloLearnerTotalArithOps {d : ℕ} (α : ℝ) (e : Fin d → ℝ)
    (X : ℕ → Set (Fin d → ℝ)) (x : ℕ → (Fin d → ℝ)) (T : ℕ) : ℕ :=
  (oiloLearnerState α e X x T).totalOps

/-!
## 5. Section 3 Variants: Algorithm Without Revocation (Remark 3.1) and Skipping Small Stretches (Proposition 3.3)
-/

/-- Recursive state of the variable-metric algorithm without revocation (Section 3.1, Remark 3.1):
    identical to `RVM(α)` except that no stretch is ever revoked, so the move in round `t` is the
    single unrevoked step `p_{t+1} = p_t + α H_t⁻¹ v_t` and `A_{t+1} = A_t ∪ {t}`. -/
noncomputable def rvmNoRevokeState {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) : ℕ → RVMState d
  | 0 =>
    { p := 0
      A := ∅
      c := fun _ => 0
      s := fun _ => 0
      γ := fun _ => 0 }
  | t + 1 =>
    let st := rvmNoRevokeState α v t
    let H_t := stretchMetric st.A st.γ v
    let p_next := st.p + α • (H_t⁻¹ *ᵥ v t)
    let s_t := matNorm (H_t⁻¹) (v t)
    let γ_t := 1 / (8 * s_t ^ 2)
    { p := p_next
      A := insert t st.A
      c := Function.update st.c t p_next
      s := Function.update st.s t s_t
      γ := Function.update st.γ t γ_t }

/-- Query point `p_t` of the algorithm without revocation at round `t`. -/
noncomputable def rvmNoRevokeQuery {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) : Fin d → ℝ :=
  (rvmNoRevokeState α v t).p

/-- Active stretch set `A_t` of the algorithm without revocation at round `t`. -/
noncomputable def rvmNoRevokeActiveSet {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) : Finset ℕ :=
  (rvmNoRevokeState α v t).A

/-- Metric `H_t` of the algorithm without revocation at round `t`. -/
noncomputable def rvmNoRevokeMetric {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  let st := rvmNoRevokeState α v t
  stretchMetric st.A st.γ v

/-- Dual length `s_t = ‖v_t‖_{H_t^{-1}}` of the algorithm without revocation at round `t`. -/
noncomputable def rvmNoRevokeStepNorm {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) : ℝ :=
  matNorm ((rvmNoRevokeMetric α v t)⁻¹) (v t)

/-- Stretch weight `γ_t = 1 / (8 s_t^2)` of the algorithm without revocation at round `t`. -/
noncomputable def rvmNoRevokeWeight {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) : ℝ :=
  1 / (8 * (rvmNoRevokeStepNorm α v t) ^ 2)

/-- Per-round loss `r_t = ⟨w* - p_t, v_t⟩` of the algorithm without revocation at round `t`. -/
noncomputable def rvmNoRevokeLoss {d : ℕ} (α : ℝ) (w_star : Fin d → ℝ) (v : ℕ → (Fin d → ℝ))
    (t : ℕ) : ℝ :=
  dotProduct (w_star - rvmNoRevokeQuery α v t) (v t)

/-- Cumulative regret `Reg_T = ∑_{t=0}^{T-1} r_t` of the algorithm without revocation. -/
noncomputable def rvmNoRevokeRegret {d : ℕ} (α : ℝ) (w_star : Fin d → ℝ) (v : ℕ → (Fin d → ℝ))
    (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, rvmNoRevokeLoss α w_star v t

/-- Recursive state of the modified algorithm `RVMSkip(α)` (Proposition 3.3) that makes stretch `t`
    only when `s_t^2 > (t + 2)^{-4}` (1-indexed `(t + 1)^{-4}`). -/
noncomputable def rvmSkipState {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) : ℕ → RVMState d
  | 0 =>
    { p := 0
      A := ∅
      c := fun _ => 0
      s := fun _ => 0
      γ := fun _ => 0 }
  | t + 1 =>
    let st := rvmSkipState α v t
    let (p_next, A_after) :=
      rvmMoveEval α st.c v st.s st.γ (v t) (st.A.card + 1) α st.p st.A α
    let H_after := stretchMetric A_after st.γ v
    let s_t := matNorm (H_after⁻¹) (v t)
    let γ_t := 1 / (8 * s_t ^ 2)
    let A_next := if s_t ^ 2 > ((t + 2 : ℝ) ^ 4)⁻¹ then insert t A_after else A_after
    { p := p_next
      A := A_next
      c := Function.update st.c t p_next
      s := Function.update st.s t s_t
      γ := Function.update st.γ t γ_t }

/-- Query point `p_t` of `RVMSkip(α)` at round `t`. -/
noncomputable def rvmSkipQuery {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) : Fin d → ℝ :=
  (rvmSkipState α v t).p

/-- Active stretch set `A_t` of `RVMSkip(α)` at round `t`. -/
noncomputable def rvmSkipActiveSet {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) : Finset ℕ :=
  (rvmSkipState α v t).A

/-- Metric `H_t` of `RVMSkip(α)` at round `t`. -/
noncomputable def rvmSkipMetric {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  let st := rvmSkipState α v t
  stretchMetric st.A st.γ v

/-- Active stretch set `hat_A_t(η)` of `RVMSkip(α)` at time `η ∈ [0, α]` during round `t`. -/
noncomputable def rvmSkipPathActiveSet {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) (η : ℝ) :
    Finset ℕ :=
  let st := rvmSkipState α v t
  (rvmMoveEval α st.c v st.s st.γ (v t) (st.A.card + 1) α st.p st.A η).2

/-- Set of stretches `A_t \ hat_A_t(α)` revoked during round `t` of `RVMSkip(α)`. -/
noncomputable def rvmSkipRevokedInRound {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) :
    Finset ℕ :=
  rvmSkipActiveSet α v t \ rvmSkipPathActiveSet α v t α

/-- Number of stretches `k_t = |A_t \ hat_A_t(α)|` revoked during round `t` of `RVMSkip(α)`. -/
noncomputable def rvmSkipRevokedCount {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) : ℕ :=
  (rvmSkipRevokedInRound α v t).card

/-- Number of linear pieces traversed by the move in round `t` of `RVMSkip(α)`. -/
noncomputable def rvmSkipRoundPieces {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) : ℕ :=
  let st := rvmSkipState α v t
  rvmMovePieces α st.c v st.s st.γ (v t) (st.A.card + 1) α st.p st.A

/-- Per-round loss `r_t = ⟨w* - p_t, v_t⟩` of `RVMSkip(α)`. -/
noncomputable def rvmSkipLoss {d : ℕ} (α : ℝ) (w_star : Fin d → ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) :
    ℝ :=
  dotProduct (w_star - rvmSkipQuery α v t) (v t)

/-- Cumulative regret `Reg_T = ∑_{t=0}^{T-1} r_t` of `RVMSkip(α)`. -/
noncomputable def rvmSkipRegret {d : ℕ} (α : ℝ) (w_star : Fin d → ℝ) (v : ℕ → (Fin d → ℝ))
    (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, rvmSkipLoss α w_star v t

/-- Recursive run of the incremental Sherman–Morrison implementation of `RVMSkip(α)`
    (Proposition 3.3 & Remark 2.4), recording the per-round and cumulative scalar-operation
    counts from `rvmFastMove` and `ramSkipStretchCreation`. -/
noncomputable def rvmSkipFastState {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) : ℕ → RVMFastState d
  | 0 =>
    { p := 0
      A := ∅
      M := 1
      φ := fun _ => 0
      c := fun _ => 0
      s_sq := fun _ => 0
      γ := fun _ => 0
      roundOps := 0
      totalOps := 0 }
  | t + 1 =>
    let st := rvmSkipFastState α v t
    let move := rvmFastMove α v st.s_sq st.γ (v t) (st.A.card + 1) α st.p st.A st.M st.φ
    let (p_next, A_after, M_after, φ_after) := move.val
    let stretch := ramSkipStretchCreation M_after (v t) t
    let (keep, s_sq_t, γ_t, M_next) := stretch.val
    let round_ops := move.ops + stretch.ops
    { p := p_next
      A := if keep then insert t A_after else A_after
      M := M_next
      φ := if keep then Function.update φ_after t 0 else φ_after
      c := Function.update st.c t p_next
      s_sq := Function.update st.s_sq t s_sq_t
      γ := Function.update st.γ t γ_t
      roundOps := round_ops
      totalOps := st.totalOps + round_ops }

/-- Instrumented scalar operations (arithmetic and comparisons) performed by
    `rvmSkipFastState` in round `t` of `RVMSkip(α)` (Proposition 3.3). -/
noncomputable def rvmSkipRoundArithOps {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (t : ℕ) : ℕ :=
  (rvmSkipFastState α v (t + 1)).roundOps

/-- Instrumented cumulative scalar operations (arithmetic and comparisons) performed by
    `rvmSkipFastState` over the first `T` rounds of `RVMSkip(α)`. -/
noncomputable def rvmSkipTotalArithOps {d : ℕ} (α : ℝ) (v : ℕ → (Fin d → ℝ)) (T : ℕ) : ℕ :=
  (rvmSkipFastState α v T).totalOps

/-!
## 6. Propositional Statements of All Formalized Results
-/

/-- **Causality of `RVM(α)` and `RVMSkip(α)` (mathematical and incremental states)**:
    At the start of round `t`, both the mathematical algorithm states (`rvmState α v t` and
    `rvmSkipState α v t`) and the incremental Sherman–Morrison states (`rvmFastState α v t` and
    `rvmSkipFastState α v t`) depend only on the oracle directions `v 0, …, v (t - 1)` from prior
    rounds. -/
def Causality_OraclePrefix : Prop :=
  ∀ {d : ℕ} (α : ℝ) (v v' : ℕ → (Fin d → ℝ)) (t : ℕ),
    (∀ s < t, v s = v' s) →
    rvmState α v t = rvmState α v' t ∧
    rvmSkipState α v t = rvmSkipState α v' t ∧
    rvmFastState α v t = rvmFastState α v' t ∧
    rvmSkipFastState α v t = rvmSkipFastState α v' t

/-- **Lemma 2.3(a) (Well-posed move — Active slabs contain the query)**:
    In every round `t` of `RVM(α)`, `p_t ∈ L_i` for all `i ∈ A_t`,
    `hat_p_t(0) = p_t`, `hat_A_t(0) = A_t`, and `hat_H_t(0) = H_t`. -/
def Lemma2_3a_ActiveSlabsContainQuery : Prop :=
  ∀ {d : ℕ} (_hd : 0 < d) (α : ℝ) (_hα : 0 < α)
    (v : ℕ → (Fin d → ℝ)) (_h_unit : ∀ k, dotProduct (v k) (v k) = 1) (t : ℕ),
    (∀ i ∈ rvmActiveSet α v t, i < t ∧ rvmSlab α v i (rvmQuery α v t)) ∧
    rvmPath α v t 0 = rvmQuery α v t ∧
    rvmPathActiveSet α v t 0 = rvmActiveSet α v t ∧
    rvmPathMetric α v t 0 = rvmMetric α v t

/-- **Lemma 2.3(b) (Well-posed move — Existence, uniqueness, and piecewise linearity)**:
    In every round `t` of `RVM(α)`:
    - `1 ≤ pieces_t ≤ k_t + 1 ≤ |A_t| + 1`;
    - `hat_A_t(η) = {i ∈ A_t : ∀ τ ∈ [0, η], hat_p_t(τ) ∈ L_i}` for all `η ∈ [0, α]`;
    - `hat_p_t` is locally affine to the right of every `η ∈ [0, α)` with velocity `hat_H_t(η)^{-1} v_t`;
    - `hat_p_t` solves the continuous move equations (Equation (3)), and any path `q` solving
      Equation (3) on `[0, α]` coincides with `hat_p_t` on `[0, α]`;
    - `hat_p_t` is piecewise linear with an explicit strictly increasing breakpoint sequence
      `0 = η_0 < η_1 < … < η_{pieces_t} = α` such that `hat_p_t` is affine on each `[η_j, η_{j+1}]`. -/
def Lemma2_3b_PiecewiseLinearMove : Prop :=
  ∀ {d : ℕ} (_hd : 0 < d) (α : ℝ) (_hα : 0 < α)
    (v : ℕ → (Fin d → ℝ)) (_h_unit : ∀ k, dotProduct (v k) (v k) = 1) (t : ℕ),
    1 ≤ rvmRoundPieces α v t ∧
    rvmRoundPieces α v t ≤ rvmRevokedCount α v t + 1 ∧
    rvmRevokedCount α v t ≤ (rvmActiveSet α v t).card ∧
    (∀ η ∈ Set.Icc 0 α, ∀ i : ℕ,
      i ∈ rvmPathActiveSet α v t η ↔
        (i ∈ rvmActiveSet α v t ∧ ∀ τ ∈ Set.Icc 0 η, rvmSlab α v i (rvmPath α v t τ))) ∧
    (∀ η ∈ Set.Ico 0 α, ∃ δ > 0, η + δ ≤ α ∧
      ∀ τ ∈ Set.Icc 0 δ,
        rvmPath α v t (η + τ) = rvmPath α v t η + τ • ((rvmPathMetric α v t η)⁻¹ *ᵥ v t)) ∧
    SolvesMove α v t (rvmPath α v t) ∧
    (∀ q, SolvesMove α v t q → Set.EqOn q (rvmPath α v t) (Set.Icc 0 α)) ∧
    (∃ η : ℕ → ℝ, η 0 = 0 ∧ η (rvmRoundPieces α v t) = α ∧
      (∀ j < rvmRoundPieces α v t, η j < η (j + 1)) ∧
      ∀ j < rvmRoundPieces α v t, ∃ a b : Fin d → ℝ,
        ∀ τ ∈ Set.Icc (η j) (η (j + 1)), rvmPath α v t τ = a + τ • b)

/-- **Lemma 2.3(c) (Well-posed move — Monotonicity of metric and dual length)**:
    In every round `t` of `RVM(α)`, `hat_H_t(η)` is positive definite and nonincreasing in `η`
    (in the Loewner order), and the dual length `σ_t(η) = ‖v_t‖_{hat_H_t(η)^{-1}}` is
    nondecreasing with `0 < σ_t(η_1) ≤ σ_t(η_2) ≤ s_t ≤ 1` for `0 ≤ η_1 ≤ η_2 ≤ α`. -/
def Lemma2_3c_MetricAndDualLengthMonotone : Prop :=
  ∀ {d : ℕ} (_hd : 0 < d) (α : ℝ) (_hα : 0 < α)
    (v : ℕ → (Fin d → ℝ)) (_h_unit : ∀ k, dotProduct (v k) (v k) = 1) (t : ℕ)
    (η₁ η₂ : ℝ),
    0 ≤ η₁ → η₁ ≤ η₂ → η₂ ≤ α →
    rvmPathActiveSet α v t η₂ ⊆ rvmPathActiveSet α v t η₁ ∧
    (rvmPathMetric α v t η₁).PosDef ∧
    (rvmPathMetric α v t η₁ - rvmPathMetric α v t η₂).PosSemidef ∧
    0 < rvmDualLength α v t η₁ ∧
    rvmDualLength α v t η₁ ≤ rvmDualLength α v t η₂ ∧
    rvmDualLength α v t η₂ ≤ rvmStepNorm α v t ∧
    rvmStepNorm α v t ≤ 1

/-- **Lemma 2.3(d) & Equation (5) (Well-posed move — Revocation on the slab boundary)**:
    Each stretch `i ∈ A_t \ hat_A_t(α)` revoked in round `t` is revoked at time
    `η_i = rvmRoundRevokeTime α v t i ∈ (0, α]` and point `q_i = hat_p_t(η_i)` on the boundary of
    its slab `|⟨q_i - p_{i+1}, v_i⟩| = 4 α s_i^2`, with `i ∈ hat_A_t(η)` for all `η ∈ [0, η_i)` and
    `i ∉ hat_A_t(η_i)`. Consequently, for any horizon `T` and `t < T`, `|Δ_t| = 4 α s_t^2` if
    stretch `t` is revoked (`t ∉ A_T`, paper: `t ∉ A_{T+1}`) and `|Δ_t| < 4 α s_t^2` if it survives
    (`t ∈ A_T`, paper: `t ∈ A_{T+1}`). -/
def Lemma2_3d_RevocationOnBoundary : Prop :=
  ∀ {d : ℕ} (_hd : 0 < d) (α : ℝ) (_hα : 0 < α)
    (v : ℕ → (Fin d → ℝ)) (_h_unit : ∀ k, dotProduct (v k) (v k) = 1),
    (∀ (t : ℕ), ∀ i ∈ rvmRevokedInRound α v t,
      rvmRoundRevokeTime α v t i ∈ Set.Ioc 0 α ∧
      rvmRoundRevokePoint α v t i = rvmPath α v t (rvmRoundRevokeTime α v t i) ∧
      (∀ η ∈ Set.Ico 0 (rvmRoundRevokeTime α v t i), i ∈ rvmPathActiveSet α v t η) ∧
      i ∉ rvmPathActiveSet α v t (rvmRoundRevokeTime α v t i) ∧
      (∃ η ∈ Set.Icc 0 α, rvmRoundRevokePoint α v t i = rvmPath α v t η) ∧
      |dotProduct (rvmRoundRevokePoint α v t i - rvmQuery α v (i + 1)) (v i)| =
        4 * α * (rvmStepNorm α v i) ^ 2) ∧
    (∀ (T t : ℕ), t < T →
      (t ∉ rvmActiveSet α v T → |rvmDelta α v T t| = 4 * α * (rvmStepNorm α v t) ^ 2) ∧
      (t ∈ rvmActiveSet α v T → |rvmDelta α v T t| < 4 * α * (rvmStepNorm α v t) ^ 2))

/-- **Remark 2.4 (Combinatorial piece/revocation counts, Sherman–Morrison implementation, and per-round cost)**:
    For every run of `RVM(α)` and `RVMSkip(α)`:
    - In `RVM(α)`: `|A_t| ≤ t` (paper: `|A_t| ≤ t - 1`), `∑_{t < T} k_t ≤ T`, and
      `∑_{t < T} pieces_t ≤ 2 T`;
    - In `RVMSkip(α)`: `|A_t| ≤ t`, `1 ≤ pieces_t ≤ k_t + 1 ≤ |A_t| + 1`, `∑_{t < T} k_t ≤ T`, and
      `∑_{t < T} pieces_t ≤ 2 T`;
    - Sherman–Morrison rank-one downdate and update identities;
    - Exact equivalence between `rvmState α v t` and the matrix-inversion-free incremental
      Sherman–Morrison state `rvmFastState α v t` (maintaining `M = H_t⁻¹`,
      `s_sq i = s_i^2`, and active displacements `φ_i = ⟨p_t - p_{i+1}, v_i⟩` for `i ∈ A_t` with
      `φ_i = 0` for `i ∉ A_t`), together with the instrumented scalar-operation bounds
      `rvmRoundArithOps α v t ≤ pieces_t · pieceArithOps d |A_t| + k_t · downdateArithOps d + stretchArithOps d`
      and `rvmRoundArithOps α v t ≤ 28 (k_t + 1) (d^2 + |A_t| d) = O((k_t + 1)(d^2 + |A_t| d))`. -/
def Remark2_4_CombinatorialCounts : Prop :=
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
        M - (1 / (9 * s_t ^ 2)) • Matrix.vecMulVec (M *ᵥ v t) (M *ᵥ v t)) ∧
    (∀ t,
      (rvmFastState α v t).p = (rvmState α v t).p ∧
      (rvmFastState α v t).A = (rvmState α v t).A ∧
      (rvmFastState α v t).c = (rvmState α v t).c ∧
      (∀ i, (rvmFastState α v t).s_sq i = ((rvmState α v t).s i) ^ 2) ∧
      (rvmFastState α v t).γ = (rvmState α v t).γ ∧
      (rvmFastState α v t).M = (rvmMetric α v t)⁻¹ ∧
      (∀ i ∈ (rvmFastState α v t).A, (rvmFastState α v t).φ i =
        dotProduct ((rvmFastState α v t).p - (rvmFastState α v t).c i) (v i)) ∧
      (∀ i ∉ (rvmFastState α v t).A, (rvmFastState α v t).φ i = 0) ∧
      rvmTotalArithOps α v t = ∑ r ∈ Finset.range t, rvmRoundArithOps α v r ∧
      rvmRoundArithOps α v t ≤
        rvmRoundPieces α v t * pieceArithOps d (rvmActiveSet α v t).card +
        rvmRevokedCount α v t * downdateArithOps d +
        stretchArithOps d ∧
      rvmRoundArithOps α v t ≤
        28 * (rvmRevokedCount α v t + 1) * (d ^ 2 + (rvmActiveSet α v t).card * d))

/-- **Lemma 2.5 (One move)**:
    In every round `t`, `0 ≤ ξ_t ≤ α s_t^2`, and
    `‖p_{t+1} - w*‖_{hat_H_t(α)}^2 - ‖p_t - w*‖_{H_t}^2 ≤ -2 α r_t + α^2 s_t^2 - ∑_{i ∈ A_t \ hat_A_t(α)} γ_i ⟨w* - q_i, v_i⟩^2`. -/
def Lemma2_5_OneMove : Prop :=
  ∀ {d : ℕ} (_hd : 0 < d) (α : ℝ) (_hα : 0 < α)
    (w_star : Fin d → ℝ)
    (v : ℕ → (Fin d → ℝ)) (_h_unit : ∀ k, dotProduct (v k) (v k) = 1) (t : ℕ),
    0 ≤ rvmXi α v t ∧
    rvmXi α v t ≤ α * (rvmStepNorm α v t) ^ 2 ∧
    quadForm (rvmPathMetric α v t α) (rvmQuery α v (t + 1) - w_star) -
        quadForm (rvmMetric α v t) (rvmQuery α v t - w_star) ≤
      -2 * α * rvmLoss α w_star v t + α ^ 2 * (rvmStepNorm α v t) ^ 2 -
        ∑ i ∈ rvmRevokedInRound α v t,
          rvmWeight α v i * (dotProduct (w_star - rvmRoundRevokePoint α v t i) (v i)) ^ 2

/-- **Equation (6) (The ledger)**:
    Summing the move inequality and the stretch creation/revocation terms over `t < T` yields
    `‖p_T - w*‖^2 - ‖w*‖^2 ≤ ∑_{t < T} Λ_t` (where `p_T` is `p_{T+1}` in 1-indexed paper indexing). -/
def Equation6_Ledger : Prop :=
  ∀ {d : ℕ} (_hd : 0 < d) (α : ℝ) (_hα : 0 < α)
    (w_star : Fin d → ℝ)
    (v : ℕ → (Fin d → ℝ)) (_h_unit : ∀ k, dotProduct (v k) (v k) = 1) (T : ℕ),
    dotProduct (rvmQuery α v T - w_star) (rvmQuery α v T - w_star) -
        dotProduct w_star w_star ≤
      ∑ t ∈ Finset.range T, rvmLambda α w_star v T t

/-- **Lemma 2.6 (Lifetime of a stretch)**:
    For every `t < T` with `r_t ≥ 0`,
    `Λ_t ≤ -α r_t` if stretch `t` is revoked (`t ∉ A_T`, paper: `t ∉ A_{T+1}`), and
    `Λ_t ≤ -α r_t + (9/8) α^2 s_t^2` if stretch `t` survives (`t ∈ A_T`, paper: `t ∈ A_{T+1}`). -/
def Lemma2_6_StretchLifetime : Prop :=
  ∀ {d : ℕ} (_hd : 0 < d) (α : ℝ) (_hα : 0 < α)
    (w_star : Fin d → ℝ)
    (v : ℕ → (Fin d → ℝ)) (_h_unit : ∀ k, dotProduct (v k) (v k) = 1)
    (T t : ℕ),
    t < T →
    0 ≤ rvmLoss α w_star v t →
    (t ∉ rvmActiveSet α v T → rvmLambda α w_star v T t ≤ -α * rvmLoss α w_star v t) ∧
    (t ∈ rvmActiveSet α v T →
      rvmLambda α w_star v T t ≤
        -α * rvmLoss α w_star v t + (9 / 8 : ℝ) * α ^ 2 * (rvmStepNorm α v t) ^ 2)

/-- **Lemma 2.7 (Surviving stretches)**:
    For every horizon `T`, the surviving stretches `A_T` (paper: `A_{T+1}`) satisfy
    `∑_{t ∈ A_T} s_t^2 ≤ 9 (d - tr(bar_H_T^{-1})) ≤ 9 d` (paper: `bar_H_{T+1}`). -/
def Lemma2_7_SurvivingStretches : Prop :=
  ∀ {d : ℕ} (_hd : 0 < d) (α : ℝ) (_hα : 0 < α)
    (v : ℕ → (Fin d → ℝ)) (_h_unit : ∀ k, dotProduct (v k) (v k) = 1) (T : ℕ),
    ∑ t ∈ rvmActiveSet α v T, (rvmStepNorm α v t) ^ 2 ≤
      9 * ((d : ℝ) - ((rvmSurvivingMetric α v T T)⁻¹).trace) ∧
    9 * ((d : ℝ) - ((rvmSurvivingMetric α v T T)⁻¹).trace) ≤ 9 * (d : ℝ)

/-- **Theorem 2.1 (Regret and running time of RVM(α))**:
    With `α = R / (3√d)`, for every horizon `T`, every `w*` with `‖w*‖ ≤ R`, and every strong
    separation oracle (`r_t ≥ 0` for `t < T` and `‖v_t‖ = 1`):
    - `Reg_T ≤ (51/8) R √d < 6.4 R √d` and `‖p_T - w*‖^2 ≤ (17/8) R^2` (where `p_T` is `p_{T+1}` in
      1-indexed paper indexing);
    - round `t` (0-indexed; paper round `t + 1`) uses
      `rvmRoundArithOps α v t ≤ 28 (t + 1) d^2 + 28 (t + 1)^2 d = O(t d^2 + t^2 d)` scalar
      operations, and the first `T` rounds use
      `rvmTotalArithOps α v T ≤ 34 T d^2 + 36 T^2 d = T · O(d^2 + T d)` scalar operations. -/
def Theorem2_1_RVMRegretBound : Prop :=
  ∀ {d : ℕ} (_hd : 0 < d) (R : ℝ) (_hR : 0 < R)
    (w_star : Fin d → ℝ) (_hw : dotProduct w_star w_star ≤ R ^ 2)
    (v : ℕ → (Fin d → ℝ)) (_h_unit : ∀ t, dotProduct (v t) (v t) = 1)
    (α : ℝ),
    α = R / (3 * Real.sqrt (d : ℝ)) →
    ∀ T : ℕ, (∀ t < T, 0 ≤ rvmLoss α w_star v t) →
      rvmRegret α w_star v T ≤ (51 / 8 : ℝ) * R * Real.sqrt (d : ℝ) ∧
      (51 / 8 : ℝ) * R * Real.sqrt (d : ℝ) < (6.4 : ℝ) * R * Real.sqrt (d : ℝ) ∧
      dotProduct (rvmQuery α v T - w_star) (rvmQuery α v T - w_star) ≤ (17 / 8 : ℝ) * R ^ 2 ∧
      (∀ t : ℕ, rvmRoundArithOps α v t ≤ 28 * (t + 1) * d ^ 2 + 28 * (t + 1) ^ 2 * d) ∧
      rvmTotalArithOps α v T ≤ 34 * T * d ^ 2 + 36 * T ^ 2 * d

/-- **Corollary 2.2 (Online inverse linear optimization)**:
    1. **Protocol-level reduction & running time**: For any sequence of action sets `X_t ⊆ B` (`R = 1`),
       any learner recommendations `x̂_t ∈ argmax_{y ∈ X_t} ⟨ŵ_t, y⟩` where
       `ŵ_t = oiloHypothesis α e x x_hat u t ≠ 0`, and any expert choices
       `x_t ∈ argmax_{y ∈ X_t} ⟨w*, y⟩`, skipping tie rounds `x_t = x̂_t` and feeding
       `u_{g(t)} = (x_t - x̂_t) / ‖x_t - x̂_t‖` to `RVM(α)` at game round `g(t) = oiloGameIndex x x_hat t`
       yields the full chain `R_T ≤ 2 Reg_{g(T)} ≤ (51/4) √d < 13 √d`, per-round scalar operations
       `oiloRoundArithOps α x x_hat u t ≤ 36 (t + 1) d^2 + 28 (t + 1)^2 d`, and cumulative scalar
       operations `oiloTotalArithOps α x x_hat u T ≤ 42 T d^2 + 36 T ^ 2 * d`.
    2. **Existence of best actions on compact nonempty action sets**: For every objective `w ∈ ℝ^d`
       and every nonempty compact action set `S ⊆ ℝ^d`, `linearMaximizer w S ∈ S` and
       `∀ y ∈ S, ⟨w, y⟩ ≤ ⟨w, linearMaximizer w S⟩`.
    3. **Constructed closed-loop deterministic proper learner**: For every hidden `w* ∈ B`, every
       nonzero fallback `e ≠ 0`, every sequence of nonempty compact action sets `X_t ⊆ B`, and every
       expert sequence `x_t ∈ argmax_{y ∈ X_t} ⟨w*, y⟩`, the explicitly constructed learner
       (`oiloLearnerState`, `oiloLearnerHypothesis`, `oiloLearnerAction`, carrying an incremental
       `RVMFastState` advanced by `rvmFastStep` on non-tie rounds and accumulating its own
       `roundOps`/`totalOps`) is causal (depends at round `t` only on `(X_s, x_s)` for `s < t`),
       commits to `ŵ_t = oiloLearnerHypothesis α e X x t ≠ 0`, recommends
       `x̂_t = oiloLearnerAction α e X x t ∈ argmax_{y ∈ X_t} ⟨ŵ_t, y⟩`, and achieves
       `R_T ≤ 2 Reg_{g(T)} ≤ (51/4) √d < 13 √d` with its own accumulated scalar-operation counts
       `oiloLearnerRoundArithOps` and `oiloLearnerTotalArithOps` equal to `oiloRoundArithOps` and
       `oiloTotalArithOps` and bounded by `36 (t + 1) d^2 + 28 (t + 1)^2 d` per round and
       `42 T d^2 + 36 T^2 d` in total. -/
def Corollary2_2_OnlineInverseOptimization : Prop :=
  ∀ {d : ℕ} (_hd : 0 < d),
    (∀ (w_star : Fin d → ℝ) (_hw : dotProduct w_star w_star ≤ 1)
      (e : Fin d → ℝ) (_he : e ≠ 0)
      (X : ℕ → Set (Fin d → ℝ))
      (_hX_ball : ∀ t, ∀ y ∈ X t, dotProduct y y ≤ 1)
      (x x_hat : ℕ → (Fin d → ℝ))
      (_hx_mem : ∀ t, x t ∈ X t)
      (_hx_hat_mem : ∀ t, x_hat t ∈ X t)
      (u : ℕ → (Fin d → ℝ)) (_h_unit : ∀ k, dotProduct (u k) (u k) = 1)
      (α : ℝ),
      α = 1 / (3 * Real.sqrt (d : ℝ)) →
      (∀ t, ∀ y ∈ X t,
        dotProduct (oiloHypothesis α e x x_hat u t) y ≤
          dotProduct (oiloHypothesis α e x x_hat u t) (x_hat t)) →
      (∀ t, ∀ y ∈ X t, dotProduct w_star y ≤ dotProduct w_star (x t)) →
      (∀ t, x t ≠ x_hat t →
        u (oiloGameIndex x x_hat t) =
          (Real.sqrt (dotProduct (x t - x_hat t) (x t - x_hat t)))⁻¹ • (x t - x_hat t)) →
      (∀ t, oiloHypothesis α e x x_hat u t ≠ 0 ∧
        dotProduct (rvmQuery α u (oiloGameIndex x x_hat t)) (x t - x_hat t) ≤ 0 ∧
        0 ≤ dotProduct w_star (x t - x_hat t) ∧
        (x t ≠ x_hat t →
          0 ≤ rvmLoss α w_star u (oiloGameIndex x x_hat t) ∧
          dotProduct w_star (x t - x_hat t) ≤ 2 * rvmLoss α w_star u (oiloGameIndex x x_hat t)) ∧
        oiloRoundArithOps α x x_hat u t ≤ 36 * (t + 1) * d ^ 2 + 28 * (t + 1) ^ 2 * d) ∧
      (∀ T : ℕ,
        oiloGameIndex x x_hat T ≤ T ∧
        ∑ t ∈ Finset.range T, dotProduct w_star (x t - x_hat t) ≤
          2 * rvmRegret α w_star u (oiloGameIndex x x_hat T) ∧
        2 * rvmRegret α w_star u (oiloGameIndex x x_hat T) ≤
          (51 / 4 : ℝ) * Real.sqrt (d : ℝ) ∧
        ∑ t ∈ Finset.range T, dotProduct w_star (x t - x_hat t) ≤
          (51 / 4 : ℝ) * Real.sqrt (d : ℝ) ∧
        (51 / 4 : ℝ) * Real.sqrt (d : ℝ) < 13 * Real.sqrt (d : ℝ) ∧
        oiloTotalArithOps α x x_hat u T ≤ 42 * T * d ^ 2 + 36 * T ^ 2 * d)) ∧
    (∀ (w : Fin d → ℝ) (S : Set (Fin d → ℝ)),
      IsCompact S → S.Nonempty →
      linearMaximizer w S ∈ S ∧ ∀ y ∈ S, dotProduct w y ≤ dotProduct w (linearMaximizer w S)) ∧
    (∀ (w_star : Fin d → ℝ) (_hw : dotProduct w_star w_star ≤ 1)
      (e : Fin d → ℝ) (_he : e ≠ 0)
      (X : ℕ → Set (Fin d → ℝ))
      (_hX_compact : ∀ t, IsCompact (X t))
      (_hX_nonempty : ∀ t, (X t).Nonempty)
      (_hX_ball : ∀ t, ∀ y ∈ X t, dotProduct y y ≤ 1)
      (x : ℕ → (Fin d → ℝ))
      (_hx_mem : ∀ t, x t ∈ X t)
      (_h_expert_opt : ∀ t, ∀ y ∈ X t, dotProduct w_star y ≤ dotProduct w_star (x t))
      (α : ℝ),
      α = 1 / (3 * Real.sqrt (d : ℝ)) →
      let x_hat := oiloLearnerAction α e X x
      (∀ (X' : ℕ → Set (Fin d → ℝ)) (x' : ℕ → (Fin d → ℝ)) (t : ℕ),
        (∀ s < t, X s = X' s ∧ x s = x' s) →
        oiloLearnerState α e X x t = oiloLearnerState α e X' x' t) ∧
      (∀ t : ℕ,
        oiloLearnerFastState α e X x t =
          rvmFastState α (oiloLearnerDirections α e X x t) (oiloLearnerGameIndex α e X x t) ∧
        oiloLearnerHypothesis α e X x t ≠ 0 ∧
        x_hat t ∈ X t ∧
        (∀ y ∈ X t,
          dotProduct (oiloLearnerHypothesis α e X x t) y ≤
            dotProduct (oiloLearnerHypothesis α e X x t) (x_hat t)) ∧
        dotProduct (oiloLearnerQuery α e X x t) (x t - x_hat t) ≤ 0 ∧
        0 ≤ dotProduct w_star (x t - x_hat t)) ∧
      (∀ T : ℕ,
        let u := oiloLearnerDirections α e X x T
        oiloLearnerGameIndex α e X x T = oiloGameIndex x x_hat T ∧
        oiloGameIndex x x_hat T ≤ T ∧
        (∀ t ≤ T, oiloLearnerFastState α e X x t = rvmFastState α u (oiloGameIndex x x_hat t)) ∧
        (∀ t ≤ T, oiloLearnerQuery α e X x t = rvmQuery α u (oiloGameIndex x x_hat t)) ∧
        (∀ t < T, oiloLearnerRoundArithOps α e X x t = oiloRoundArithOps α x x_hat u t) ∧
        oiloLearnerTotalArithOps α e X x T =
          ∑ t ∈ Finset.range T, oiloLearnerRoundArithOps α e X x t ∧
        oiloLearnerTotalArithOps α e X x T = oiloTotalArithOps α x x_hat u T ∧
        ∑ t ∈ Finset.range T, dotProduct w_star (x t - x_hat t) ≤
          2 * rvmRegret α w_star u (oiloGameIndex x x_hat T) ∧
        2 * rvmRegret α w_star u (oiloGameIndex x x_hat T) ≤
          (51 / 4 : ℝ) * Real.sqrt (d : ℝ) ∧
        ∑ t ∈ Finset.range T, dotProduct w_star (x t - x_hat t) ≤
          (51 / 4 : ℝ) * Real.sqrt (d : ℝ) ∧
        (51 / 4 : ℝ) * Real.sqrt (d : ℝ) < 13 * Real.sqrt (d : ℝ) ∧
        (∀ t < T, oiloLearnerRoundArithOps α e X x t ≤ 36 * (t + 1) * d ^ 2 + 28 * (t + 1) ^ 2 * d) ∧
        oiloLearnerTotalArithOps α e X x T ≤ 42 * T * d ^ 2 + 36 * T ^ 2 * d))

/-- **Remark 3.1 (Stalling without revocation)**:
    In the axis-aligned instance `w* = R e_0` and `v_t = e_0` (`e_0 = Pi.single i₀ 1`),
    running the variable-metric algorithm without revocation (`rvmNoRevokeState α v t`) produces:
    - active set `rvmNoRevokeActiveSet α v t = Finset.range t`;
    - metric `rvmNoRevokeMetric α v t = diag(1, …, μ_t, …, 1)` with eigenvalue `μ_t = (9/8)^t`
      along `e_0`, squared step norm `(rvmNoRevokeStepNorm α v t)^2 = s_t^2 = 1 / μ_t = (8/9)^t`,
      stretch weight `rvmNoRevokeWeight α v t = γ_t = 1 / (8 s_t^2)`, and `μ_{t+1} = μ_t + γ_t`;
    - query `rvmNoRevokeQuery α v t = p_t = (∑_{k < t} α / μ_k) e_0` advancing by `α (8/9)^t e_0` in
      round `t` and satisfying `⟨p_t, e_0⟩ = 9 α (1 - (8/9)^t) < 9 α = 3 R / √d`;
    - for `d ≥ 10`, every round has legal oracle response `v_t = e_0` with per-round loss
      `rvmNoRevokeLoss α w_star v t = ⟨w* - p_t, e_0⟩ > R (1 - 3 / √d) > 0` and linear cumulative
      regret `rvmNoRevokeRegret α w_star v t ≥ t · R (1 - 3 / √d)`. -/
def Remark3_1_StallingWithoutRevocation : Prop :=
  ∀ {d : ℕ} (_hd : 10 ≤ d) (i₀ : Fin d) (R : ℝ) (_hR : 0 < R) (α : ℝ),
    α = R / (3 * Real.sqrt (d : ℝ)) →
    let e₀ : Fin d → ℝ := Pi.single i₀ 1
    let v : ℕ → (Fin d → ℝ) := fun _ => e₀
    let w_star : Fin d → ℝ := R • e₀
    let μ : ℕ → ℝ := fun t => (9 / 8 : ℝ) ^ t
    let s_sq : ℕ → ℝ := fun t => 1 / μ t
    let γ : ℕ → ℝ := fun t => 1 / (8 * s_sq t)
    let p : ℕ → (Fin d → ℝ) := fun t => (∑ k ∈ Finset.range t, α / μ k) • e₀
    ∀ t : ℕ,
      rvmNoRevokeActiveSet α v t = Finset.range t ∧
      rvmNoRevokeMetric α v t =
        Matrix.diagonal (Function.update (fun _ : Fin d => (1 : ℝ)) i₀ (μ t)) ∧
      (rvmNoRevokeStepNorm α v t) ^ 2 = s_sq t ∧
      rvmNoRevokeWeight α v t = γ t ∧
      rvmNoRevokeQuery α v t = p t ∧
      rvmNoRevokeLoss α w_star v t = dotProduct (w_star - p t) e₀ ∧
      s_sq t = (8 / 9 : ℝ) ^ t ∧
      μ (t + 1) = μ t + γ t ∧
      p (t + 1) - p t = (α * (8 / 9 : ℝ) ^ t) • e₀ ∧
      dotProduct (p t) e₀ = 9 * α * (1 - (8 / 9 : ℝ) ^ t) ∧
      dotProduct (p t) e₀ < 9 * α ∧
      9 * α = 3 * R / Real.sqrt (d : ℝ) ∧
      R * (1 - 3 / Real.sqrt (d : ℝ)) < rvmNoRevokeLoss α w_star v t ∧
      0 < R * (1 - 3 / Real.sqrt (d : ℝ)) ∧
      (t : ℝ) * (R * (1 - 3 / Real.sqrt (d : ℝ))) ≤ rvmNoRevokeRegret α w_star v t

/-- **Proposition 3.3 (Skipping small stretches)**:
    In `RVMSkip(α)` (where stretch `t` is made only if `s_t^2 > (t + 2)^{-4}` in 0-indexed rounds,
    corresponding to `(t + 1)^{-4}` in 1-indexed paper rounds), with `α = R / (3√d)`:
    - `Reg_T ≤ (51/8 + 0.03/d) R √d < 6.41 R √d` for all `T` whenever `r_t ≥ 0` for `t < T`;
    - `(9/8)^{|A_t|} ≤ det H_t`, `tr H_t ≤ d + (t + 1)^5 / 8`, and
      `|A_t| ≤ B_t := d ln(1 + (t + 1)^5 / (8d)) / ln(9/8)` for all `t` (where `(t + 1)^5` in
      0-indexed Lean rounds corresponds to `t_{\text{paper}}^5` at 1-indexed round `t_{\text{paper}} = t + 1`);
    - `rvmSkipFastState α v t` is fully state-equivalent to `rvmSkipState α v t` (`p`, `A`, `c`,
      `s_sq i = s_i^2`, `γ`, `M = H_t⁻¹`, and active displacements `φ_i = ⟨p_t - p_{i+1}, v_i⟩`
      for `i ∈ A_t` with `φ_i = 0` for `i ∉ A_t`), and its instrumented round cost satisfies
      `rvmSkipRoundArithOps α v t ≤ pieces_t · pieceArithOps d |A_t| + k_t · downdateArithOps d + skipStretchArithOps d`,
      `rvmSkipRoundArithOps α v t ≤ 33 (|A_t| + 1)(d^2 + |A_t| d) ≤ 33 (B_t + 1)(d^2 + B_t d)`
      ($O(d^3 \log^2 t)$ in the worst round), and cumulative cost
      `rvmSkipTotalArithOps α v T ≤ 39 T d^2 + 36 T B_T d`
      ($O(d^2 \log T)$ per round on average). -/
def Proposition3_3_SkippingSmallStretches : Prop :=
  ∀ {d : ℕ} (_hd : 0 < d) (R : ℝ) (_hR : 0 < R)
    (w_star : Fin d → ℝ) (_hw : dotProduct w_star w_star ≤ R ^ 2)
    (v : ℕ → (Fin d → ℝ)) (_h_unit : ∀ t, dotProduct (v t) (v t) = 1)
    (α : ℝ),
    α = R / (3 * Real.sqrt (d : ℝ)) →
    let B : ℕ → ℝ := fun t =>
      (d : ℝ) * Real.log (1 + ((t + 1 : ℝ) ^ 5) / (8 * (d : ℝ))) / Real.log (9 / 8 : ℝ)
    (∀ T : ℕ, (∀ t < T, 0 ≤ rvmSkipLoss α w_star v t) →
      rvmSkipRegret α w_star v T ≤ ((51 / 8 : ℝ) + (0.03 : ℝ) / (d : ℝ)) * R * Real.sqrt (d : ℝ) ∧
      ((51 / 8 : ℝ) + (0.03 : ℝ) / (d : ℝ)) * R * Real.sqrt (d : ℝ) <
        (6.41 : ℝ) * R * Real.sqrt (d : ℝ)) ∧
    (∀ t : ℕ,
      (rvmSkipFastState α v t).p = (rvmSkipState α v t).p ∧
      (rvmSkipFastState α v t).A = (rvmSkipState α v t).A ∧
      (rvmSkipFastState α v t).c = (rvmSkipState α v t).c ∧
      (∀ i, (rvmSkipFastState α v t).s_sq i = ((rvmSkipState α v t).s i) ^ 2) ∧
      (rvmSkipFastState α v t).γ = (rvmSkipState α v t).γ ∧
      (rvmSkipFastState α v t).M = (rvmSkipMetric α v t)⁻¹ ∧
      (∀ i ∈ (rvmSkipFastState α v t).A, (rvmSkipFastState α v t).φ i =
        dotProduct ((rvmSkipFastState α v t).p - (rvmSkipFastState α v t).c i) (v i)) ∧
      (∀ i ∉ (rvmSkipFastState α v t).A, (rvmSkipFastState α v t).φ i = 0) ∧
      (9 / 8 : ℝ) ^ (rvmSkipActiveSet α v t).card ≤ (rvmSkipMetric α v t).det ∧
      (rvmSkipMetric α v t).trace ≤ (d : ℝ) + ((t + 1 : ℝ) ^ 5) / 8 ∧
      ((rvmSkipActiveSet α v t).card : ℝ) ≤ B t ∧
      rvmSkipRoundArithOps α v t ≤
        rvmSkipRoundPieces α v t * pieceArithOps d (rvmSkipActiveSet α v t).card +
        rvmSkipRevokedCount α v t * downdateArithOps d +
        skipStretchArithOps d ∧
      rvmSkipRoundArithOps α v t ≤
        33 * ((rvmSkipActiveSet α v t).card + 1) * (d ^ 2 + (rvmSkipActiveSet α v t).card * d) ∧
      (rvmSkipRoundArithOps α v t : ℝ) ≤
        33 * (B t + 1) * ((d : ℝ) ^ 2 + B t * (d : ℝ))) ∧
    (∀ T : ℕ,
      rvmSkipTotalArithOps α v T = ∑ t ∈ Finset.range T, rvmSkipRoundArithOps α v t ∧
      (rvmSkipTotalArithOps α v T : ℝ) ≤
        39 * (T : ℝ) * (d : ℝ) ^ 2 + 36 * (T : ℝ) * B T * (d : ℝ))
