# Lean 4 Formalization of *"Efficient Online Inverse Optimization with $O(\sqrt{d})$ Regret"*

This directory contains the paper (`paper.tex`) and its reproducible, kernel-checked Lean 4 / Mathlib formalization.

---

## 1. Repository Layout

| File | Description |
|---|---|
| `paper.tex` | LaTeX manuscript of *"Efficient Online Inverse Optimization with $O(\sqrt{d})$ Regret"* |
| `lean-toolchain` | Pinned Lean 4 toolchain (`leanprover/lean4:v4.27.0`) |
| `lakefile.toml` | Lake package configuration requiring `mathlib` at `v4.27.0` |
| `lake-manifest.json` | Pinned dependency manifest (`mathlib` rev `a3a10db0e9d66acbebf76c5e6a135066525ac900`) |
| `OIO/Statements.lean` | Trusted specification file: algorithm definitions and propositional statements (`def … : Prop`) only, with no proof terms |
| `OIO/Proofs.lean` | Imports `OIO.Statements` and proves all helper lemmas, the master theorem `oio_all_results`, and all top-level theorem/lemma wrappers |
| `OIO/Audit.lean` | Imports `OIO.Proofs` and runs `#print axioms` on `oio_all_results` and every top-level theorem/lemma wrapper |
| `README.md` | Documentation of versions, build instructions, axiom audit, paper-to-Lean mapping, indexing, modeling choices, and scope |

---

## 2. Reproducible Build & Verification

### Versions
- **Lean 4**: `leanprover/lean4:v4.27.0` (commit `db93fe1608548721853390a10cd40580fe7d22ae`)
- **Mathlib 4**: `v4.27.0` (commit `a3a10db0e9d66acbebf76c5e6a135066525ac900`)

### Build Commands
From a clean clone of this directory with [`elan`](https://github.com/leanprover/elan) installed:

```bash
lake exe cache get
lake build
lake env lean OIO/Audit.lean
```

`lake build` compiles `OIO/Statements.lean`, `OIO/Proofs.lean`, and `OIO/Audit.lean` with **0 errors and 0 warnings**, without any custom `maxHeartbeats` overrides or non-standard options.

### Literal `#print axioms` Output (`lake env lean OIO/Audit.lean`)

```text
'oio_all_results' depends on axioms: [propext, Classical.choice, Quot.sound]
'thm_causality' depends on axioms: [propext, Classical.choice, Quot.sound]
'lem_wellposed' depends on axioms: [propext, Classical.choice, Quot.sound]
'rem_cost_counts' depends on axioms: [propext, Classical.choice, Quot.sound]
'lem_path' depends on axioms: [propext, Classical.choice, Quot.sound]
'lem_ledger' depends on axioms: [propext, Classical.choice, Quot.sound]
'lem_lifetime' depends on axioms: [propext, Classical.choice, Quot.sound]
'lem_potential' depends on axioms: [propext, Classical.choice, Quot.sound]
'thm_rvm' depends on axioms: [propext, Classical.choice, Quot.sound]
'cor_oilo' depends on axioms: [propext, Classical.choice, Quot.sound]
'rem_stall' depends on axioms: [propext, Classical.choice, Quot.sound]
'prop_small' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## 3. Paper ↔ Lean Mapping

### 3.1 Definitions (`OIO/Statements.lean`)

| Paper Item | Mathematical Expression | Lean Declaration (`OIO/Statements.lean`) |
|---|---|---|
| Quadratic form & Mahalanobis norm | $x^\top H x$, $\|x\|_H = (x^\top H x)^{1/2}$ | `quadForm`, `matNorm` |
| Metric of active stretches | $H = I + \sum_{i \in A} \gamma_i v_i v_i^\top$ | `stretchMetric` |
| Open slab membership | $p \in L_i \iff \lvert\langle p - c_i, v_i \rangle\rvert < 4 \alpha s_i^2$ | `inSlab`, `rvmSlab` |
| Piece exit time along ray $p + \tau u$ | $(4 \alpha s_i^2 - \operatorname{sign}(\beta_i)\phi_i)/\lvert\beta_i\rvert$ | `pieceExitDelta`, `pieceStepTime` |
| Continuous move path & pieces (Def. 1.1, Eq. (3)) | $\hat p_t(\eta)$, $\hat A_t(\eta)$, piece count, revocation point/time | `rvmMoveEval`, `rvmMovePieces`, `rvmRevocationPoint`, `rvmRevocationTime` |
| Candidate active set & ODE predicate (Eq. (3)) | $\hat A_t(\eta) = \{i \in A_t : \forall \tilde\eta \in [0,\eta],\, q(\tilde\eta) \in L_i\}$, $\hat p_t'(\eta) = \hat H_t(\eta)^{-1} v_t$ | `candActiveSet`, `SolvesMove` |
| Algorithm $\mathrm{RVM}(\alpha)$ (Def. 1.1, Eqs. (3)–(4)) | $(p_t, A_t, H_t, \hat p_t, \hat A_t, \hat H_t, \sigma_t, s_t, \gamma_t)$ | `RVMState`, `rvmState`, `rvmQuery`, `rvmActiveSet`, `rvmMetric`, `rvmPath`, `rvmPathActiveSet`, `rvmPathMetric`, `rvmDualLength`, `rvmStepNorm`, `rvmWeight` |
| Round revocations & pieces (Lem. 2.3, Rem. 2.4) | $A_t \setminus \hat A_t(\alpha)$, $k_t$, $\text{pieces}_t$, $q_i$, $\eta_i$ | `rvmRevokedInRound`, `rvmRevokedCount`, `rvmRoundPieces`, `rvmRoundRevokePoint`, `rvmRoundRevokeTime` |
| Incremental Sherman–Morrison implementation & `CostM` operation model (Rem. 2.4, Thm. 2.1) | Rank-one downdate/update of $M = H_t^{-1}$, active cached displacements $\phi_i = \langle p_t - p_{i+1}, v_i \rangle$ ($i \in A_t$), squared step norms $s_i^2$, and `CostM` instrumented scalar-operation counts | `CostM`, `CostM.pure`, `CostM.bind`, `CostM.foldl`, `ramAdd`, `ramSub`, `ramMul`, `ramDiv`, `ramNeg`, `ramAbs`, `ramSqrt`, `ramLt`, `ramEq`, `ramMin`, `ramVecAdd`, `ramVecSub`, `ramVecSmul`, `ramVecEq`, `ramDot`, `ramMatVec`, `ramRankOneAddEntry`, `ramRankOneSubEntry`, `ramRankOneAdd`, `ramRankOneSub`, `shermanMorrisonDowndate`, `shermanMorrisonDowndateSet`, `shermanMorrisonStretchUpdate`, `fastPieceExitDelta`, `ramFastPieceExitDelta`, `fastPieceStepTime`, `ramFastPieceStepTime`, `ramComputeBeta`, `ramPhiUpdate`, `ramSlabCheck`, `ramUpdateSlabs`, `ramDowndate`, `shermanMorrisonDowndateSetWithCost`, `ramStretchCreation`, `ramFastPiece`, `rvmFastMove`, `RVMFastState`, `rvmFastStep`, `rvmFastState`, `pieceArithOps`, `downdateArithOps`, `stretchArithOps`, `rvmRoundArithOps`, `rvmTotalArithOps` |
| Loss, regret, displacement, ledger (Sec. 2.2) | $r_t$, $\operatorname{Reg}_T$, $\xi_t$, $q_t$, $\Delta_t$ (Eq. (5)), $\Lambda_t$ (Eq. (6)) | `rvmLoss`, `rvmRegret`, `rvmXi`, `rvmStretchEndPoint`, `rvmDelta`, `rvmLambda` |
| Surviving-stretch metric (Sec. 2.4) | $\bar H_t = I + \sum_{i \in A_{T+1},\, i < t} \gamma_i v_i v_i^\top$ | `rvmSurvivingMetric` |
| OILO reduction, compact-set maximizer & closed-loop proper learner (Sec. 1, Cor. 2.2) | Non-tie game counter $g(t)$, linear optimization oracle $\arg\max_{y \in X_t} \langle \hat w_t, y \rangle$, closed-loop learner state carrying `RVMFastState` and its own operation counters, $\hat w_t \neq 0$, and $\hat x_t$ | `oiloGameIndex`, `oiloHypothesis`, `linearMaximizer`, `OILOLearnerState`, `oiloLearnerState`, `oiloLearnerGameIndex`, `oiloLearnerDirections`, `oiloLearnerFastState`, `oiloLearnerQuery`, `oiloLearnerHypothesis`, `oiloLearnerAction`, `oiloLearnerRoundArithOps`, `oiloLearnerTotalArithOps`, `ramNormalizeDiff`, `oiloReductionArithOps`, `oiloRoundArithOps`, `oiloTotalArithOps` |
| Variable-metric algorithm without revocation (Rem. 3.1) | $p_{t+1} = p_t + \alpha H_t^{-1} v_t$, $A_{t+1} = A_t \cup \{t\}$, $H_{t+1} = H_t + \gamma_t v_t v_t^\top$ | `rvmNoRevokeState`, `rvmNoRevokeQuery`, `rvmNoRevokeActiveSet`, `rvmNoRevokeMetric`, `rvmNoRevokeStepNorm`, `rvmNoRevokeWeight`, `rvmNoRevokeLoss`, `rvmNoRevokeRegret` |
| Skipping variant $\mathrm{RVMSkip}(\alpha)$ & `CostM` operation counts (Prop. 3.3) | Stretch made iff $s_t^2 > (t_{\text{paper}}+1)^{-4}$, plus `CostM` instrumented incremental state and scalar-operation counts | `rvmSkipState`, `rvmSkipQuery`, `rvmSkipActiveSet`, `rvmSkipMetric`, `rvmSkipPathActiveSet`, `rvmSkipRevokedInRound`, `rvmSkipRevokedCount`, `rvmSkipRoundPieces`, `rvmSkipLoss`, `rvmSkipRegret`, `ramSkipStretchCreation`, `skipStretchArithOps`, `rvmSkipFastStep`, `rvmSkipFastState`, `rvmSkipRoundArithOps`, `rvmSkipTotalArithOps` |

### 3.2 Propositions, Lemmas, Theorems, Corollaries, and Remarks

| Paper Reference | Statement Prop (`OIO/Statements.lean`) | Proof / Wrapper (`OIO/Proofs.lean`) | What is Formalized |
|---|---|---|---|
| Causality of $\mathrm{RVM}(\alpha)$ & $\mathrm{RVMSkip}(\alpha)$ | `Causality_OraclePrefix` | `thm_causality` | `rvmState`, `rvmSkipState`, `rvmFastState`, and `rvmSkipFastState` at round $t$ depend only on $v_0, \dots, v_{t-1}$ |
| **Lemma 2.3(a)** (Well-posed move) | `Lemma2_3a_ActiveSlabsContainQuery` | `lem_2_3a`, `lem_wellposed.1` | $\forall i \in A_t,\, i < t \wedge p_t \in L_i$; $\hat p_t(0) = p_t$, $\hat A_t(0) = A_t$, $\hat H_t(0) = H_t$ |
| **Lemma 2.3(b)** (Well-posed move) | `Lemma2_3b_PiecewiseLinearMove` | `lem_2_3b`, `lem_wellposed.2.1` | $1 \le \text{pieces}_t \le k_t + 1 \le \lvert A_t\rvert + 1$; slab characterization of $\hat A_t(\eta)$; right-hand local affinity; `SolvesMove` (continuity on $[0,\alpha]$, $\hat p_t(0) = p_t$, right derivative $\hat H_t(\eta)^{-1} v_t$); **uniqueness** of the path solving Eq. (3) on $[0,\alpha]$; and explicit strictly increasing breakpoint partition $0 = \eta_0 < \dots < \eta_{\text{pieces}_t} = \alpha$ on which $\hat p_t$ is affine |
| **Lemma 2.3(c)** (Well-posed move) | `Lemma2_3c_MetricAndDualLengthMonotone` | `lem_2_3c`, `lem_wellposed.2.2.1` | $\hat A_t(\eta_2) \subseteq \hat A_t(\eta_1)$, $\hat H_t(\eta_1) \succ 0$, $\hat H_t(\eta_1) \succeq \hat H_t(\eta_2)$, and $0 < \sigma_t(\eta_1) \le \sigma_t(\eta_2) \le s_t \le 1$ |
| **Lemma 2.3(d) & Eq. (5)** (Well-posed move) | `Lemma2_3d_RevocationOnBoundary` | `lem_2_3d`, `lem_wellposed.2.2.2` | Each $i \in A_t \setminus \hat A_t(\alpha)$ is revoked at time $\eta_i \in (0,\alpha]$ and point $q_i = \hat p_t(\eta_i)$ on the slab boundary $\lvert\langle q_i - p_{i+1}, v_i \rangle\rvert = 4\alpha s_i^2$, with $i \in \hat A_t(\eta)$ on $[0,\eta_i)$ and $i \notin \hat A_t(\eta_i)$; consequently $\lvert\Delta_t\rvert = 4\alpha s_t^2$ if revoked and $\lvert\Delta_t\rvert < 4\alpha s_t^2$ if surviving |
| **Remark 2.4** (Cost counts, Sherman–Morrison, & incremental state) | `Remark2_4_CombinatorialCounts` | `rem_cost_counts` | $\lvert A_t\rvert \le t$ (paper: $\le t-1$), $\sum_{t < T} k_t \le T$, and $\sum_{t < T} \text{pieces}_t \le 2T$ for both $\mathrm{RVM}(\alpha)$ and $\mathrm{RVMSkip}(\alpha)$; Sherman–Morrison rank-one downdate and update identities; exact equivalence between `rvmState` and the `CostM`-instrumented matrix-inversion-free incremental implementation `rvmFastState` (storing $M = H_t^{-1}$, $s_i^2$ with purely rational arithmetic, and active displacements $\phi_i = \langle p_t - p_{i+1}, v_i \rangle$ for $i \in A_t$ with $\phi_i = 0$ for $i \notin A_t$, executing each piece as a single `CostM.bind` chain `ramFastPiece`); and the instrumented per-round scalar-operation bound `rvmRoundArithOps α v t ≤ 28 (k_t + 1) (d^2 + |A_t| d)` |
| **Lemma 2.5** (One move) | `Lemma2_5_OneMove` | `lem_2_5`, `lem_path` | $0 \le \xi_t \le \alpha s_t^2$ and $\|p_{t+1} - w^*\|_{\hat H_t(\alpha)}^2 - \|p_t - w^*\|_{H_t}^2 \le -2\alpha r_t + \alpha^2 s_t^2 - \sum_{i \in A_t \setminus \hat A_t(\alpha)} \gamma_i \langle w^* - q_i, v_i \rangle^2$ |
| **Equation (6)** (The ledger) | `Equation6_Ledger` | `lem_eq_6`, `lem_ledger` | $\|p_T - w^*\|^2 - \|w^*\|^2 \le \sum_{t < T} \Lambda_t$ (0-indexed; paper: $\|p_{T+1} - w^*\|^2 - \|w^*\|^2 \le \sum_{t=1}^T \Lambda_t$) |
| **Lemma 2.6** (Lifetime of a stretch) | `Lemma2_6_StretchLifetime` | `lem_2_6`, `lem_lifetime` | For $t < T$ with $r_t \ge 0$: $\Lambda_t \le -\alpha r_t$ if revoked ($t \notin A_T$) and $\Lambda_t \le -\alpha r_t + \frac{9}{8}\alpha^2 s_t^2$ if surviving ($t \in A_T$) |
| **Lemma 2.7** (Surviving stretches) | `Lemma2_7_SurvivingStretches` | `lem_2_7`, `lem_potential` | $\sum_{t \in A_T} s_t^2 \le 9(d - \operatorname{tr}(\bar H_T^{-1})) \le 9d$ |
| **Theorem 2.1** (Regret & running time of $\mathrm{RVM}(\alpha)$) | `Theorem2_1_RVMRegretBound` | `thm_2_1`, `thm_rvm` | With $\alpha = R/(3\sqrt{d})$ and $r_t \ge 0$ for $t < T$: $\operatorname{Reg}_T \le \frac{51}{8} R \sqrt{d} < 6.4 R \sqrt{d}$, $\|p_T - w^*\|^2 \le \frac{17}{8} R^2$, instrumented per-round scalar operations `rvmRoundArithOps α v t ≤ 28(t+1)d^2 + 28(t+1)^2 d = O(t d^2 + t^2 d)`, and cumulative scalar operations `rvmTotalArithOps α v T ≤ 34 T d^2 + 36 T^2 d = T · O(d^2 + T d)` |
| **Corollary 2.2** (Online inverse linear optimization) | `Corollary2_2_OnlineInverseOptimization` | `cor_2_2`, `cor_oilo` | (1) Protocol-level reduction, full chain of inequalities $R_T \le 2\operatorname{Reg}_{g(T)} \le \frac{51}{4}\sqrt{d} < 13\sqrt{d}$ (explicitly exporting the middle step $2\operatorname{Reg}_{g(T)} \le \frac{51}{4}\sqrt{d}$), and per-round/cumulative operation bounds; (2) Existence of best actions (`linearMaximizer w S ∈ S` maximizing $\langle w, \cdot \rangle$) for every nonempty compact action set $S \subseteq \mathbb{R}^d$; (3) Explicitly constructed closed-loop deterministic proper learner (`oiloLearnerState`, `oiloLearnerHypothesis`, `oiloLearnerAction`), carrying an `RVMFastState` advanced by `rvmFastStep` on non-tie rounds and accumulating its own operation counters `oiloLearnerRoundArithOps` and `oiloLearnerTotalArithOps`, proven causal, proper ($\hat w_t \neq 0$, $\hat x_t \in \arg\max_{y \in X_t} \langle \hat w_t, y \rangle$), equivalent to the `rvmState`-based query and horizon-level operation counters, and achieving the full chain $R_T \le 2\operatorname{Reg}_{g_T} \le \frac{51}{4}\sqrt{d} < 13\sqrt{d}$ with $O(t d^2 + t^2 d)$ per-round and $T \cdot O(d^2 + T d)$ cumulative scalar operations |
| **Remark 3.1** (Stalling without revocation) | `Remark3_1_StallingWithoutRevocation` | `rem_stall` | Explicitly defines the variable-metric algorithm without revocation (`rvmNoRevokeState`) and proves that on $w^* = R e_0$, $v_t = e_0$, its actual execution produces $A_t = \{0, \dots, t-1\}$, $H_t = \operatorname{diag}(1, \dots, \mu_t, \dots, 1)$ with $\mu_t = (9/8)^t$, $s_t^2 = (8/9)^t$, $p_t = (\sum_{k < t} \alpha / \mu_k) e_0$ with $\langle p_t, e_0 \rangle = 9\alpha(1 - (8/9)^t) < 9\alpha = 3R/\sqrt{d}$, and for $d \ge 10$ every round has legal oracle response $v_t = e_0$ with per-round loss $r_t > R(1 - 3/\sqrt{d}) > 0$ and linear cumulative regret $\operatorname{Reg}_t \ge t R (1 - 3/\sqrt{d})$ |
| **Proposition 3.3** (Skipping small stretches) | `Proposition3_3_SkippingSmallStretches` | `prop_3_3`, `prop_small` | With $\alpha = R/(3\sqrt{d})$ and $r_t \ge 0$ for $t < T$: full skipping-state equivalence (`p`, `A`, `c`, `s_sq`, `γ`, `M = (rvmSkipMetric α v t)⁻¹`, and $\phi$ on/off $A$) between `rvmSkipFastState` and `rvmSkipState`, $\operatorname{Reg}_T \le (\frac{51}{8} + \frac{0.03}{d}) R \sqrt{d} < 6.41 R \sqrt{d}$, $(9/8)^{\lvert A_t\rvert} \le \det H_t$, $\operatorname{tr} H_t \le d + (t+1)^5/8$, $\lvert A_t\rvert \le B_t := d \ln(1 + (t+1)^5/(8d))/\ln(9/8)$, instrumented per-round scalar operations `rvmSkipRoundArithOps α v t ≤ 33(|A_t|+1)(d^2 + |A_t|d) ≤ 33(B_t+1)(d^2 + B_t d)` ($O(d^3 \log^2 t)$), and cumulative scalar operations `rvmSkipTotalArithOps α v T ≤ 39 T d^2 + 36 T B_T d` ($O(T d^2 \log T)$) |
| **All Formalized Results** | Conjunction of all 14 propositions above | `oio_all_results` | Master conjunction verified in `OIO/Proofs.lean` |

> **Note on internal helper lemmas vs. exported theorem wrappers:** In `OIO/Proofs.lean`, `lem_2_3c`, `lem_2_3d`, `lem_2_5`, `lem_eq_6`, `thm_2_1`, and `cor_2_2` are internal modular helper lemmas that take earlier `Prop`s as arguments to avoid re-elaborating proofs; the exported top-level theorems `thm_causality`, `lem_wellposed`, `rem_cost_counts`, `lem_path`, `lem_ledger`, `lem_lifetime`, `lem_potential`, `thm_rvm`, `cor_oilo`, `rem_stall`, `prop_small`, and `oio_all_results` (audited in `OIO/Audit.lean`) discharge all intermediate hypotheses and prove each statement unconditionally.

---

## 4. Indexing Convention (0-Indexed Lean vs. 1-Indexed Paper)

Rounds in Lean are **0-indexed** ($t = 0, 1, 2, \dots$), so Lean round $t$ corresponds to paper round $t_{\text{paper}} = t + 1$:

| Concept | Paper (1-indexed, $t_{\text{paper}} \ge 1$) | Lean (0-indexed, $t \ge 0$) |
|---|---|---|
| Initial query, active set, metric | $p_1 = 0$, $A_1 = \emptyset$, $H_1 = I$ | `rvmQuery α v 0 = 0`, `rvmActiveSet α v 0 = ∅`, `rvmMetric α v 0 = 1` |
| State after $T$ rounds | $p_{T+1}$, $A_{T+1}$, $\bar H_{T+1}$ | `rvmQuery α v T`, `rvmActiveSet α v T`, `rvmSurvivingMetric α v T T` |
| Cumulative regret over $T$ rounds | $\sum_{t_{\text{paper}}=1}^T r_{t_{\text{paper}}}$ | `∑ t ∈ Finset.range T, rvmLoss α w_star v t` ($t = 0, \dots, T-1$) |
| Active stretch count bound at start of round | $\lvert A_{t_{\text{paper}}}\rvert \le t_{\text{paper}} - 1$ | `(rvmActiveSet α v t).card ≤ t` |
| Per-round operation bound in Thm. 2.1 / Cor. 2.2 | $O(t_{\text{paper}} d^2 + t_{\text{paper}}^2 d)$ | `≤ 28 * (t + 1) * d ^ 2 + 28 * (t + 1) ^ 2 * d` (and `36 * (t + 1) * d ^ 2 + 28 * (t + 1) ^ 2 * d` for OILO) |
| Small-stretch skipping threshold (Prop. 3.3) | $s_{t_{\text{paper}}}^2 > (t_{\text{paper}} + 1)^{-4}$ (starts at $2^{-4}$) | `s_t ^ 2 > ((t + 2 : ℝ) ^ 4)⁻¹` (starts at $2^{-4}$ at $t = 0$) |
| Trace / $\lvert A_t\rvert$ bound in Prop. 3.3 | $t_{\text{paper}}^5 / 8$ at round $t_{\text{paper}} \ge 1$ | `((t + 1 : ℝ) ^ 5) / 8` at 0-indexed round $t = t_{\text{paper}} - 1 \ge 0$ |

---

## 5. Modeling Choices & Total-Function Conventions

1. **Adaptive oracle and causality**: An adaptive separation oracle is modeled by an arbitrary sequence `v : ℕ → (Fin d → ℝ)` of unit vectors (`∀ t, dotProduct (v t) (v t) = 1`) satisfying $r_t \ge 0$ for $t < T$. Because the learner is deterministic and `thm_causality` (`Causality_OraclePrefix`) proves that `rvmState`, `rvmSkipState`, `rvmFastState`, and `rvmSkipFastState` at round $t$ depend only on $v_0, \dots, v_{t-1}$, universally quantifying over all sequences $v$ covers every adaptive adversary. Likewise, in Corollary 2.2, `oiloLearnerState` is constructed directly as a closed-loop state machine driven by `(X, x)` (carrying `RVMFastState` and advancing it via `rvmFastStep` on non-tie rounds) and proven causal (`∀ s < t, X s = X' s ∧ x s = x' s → oiloLearnerState α e X x t = oiloLearnerState α e X' x' t`).
2. **Domain $w^* \in K_1$**: Modeled directly by its single consequence used in the paper, $\|w^*\|^2 \le R^2$ (`dotProduct w_star w_star ≤ R ^ 2`). Convexity and compactness of $K_1$ are not needed once $R$ is fixed.
3. **Action sets $X_t \subseteq \mathbb{B}$ in Corollary 2.2**: For the closed-loop learner construction in Corollary 2.2, each action set $X_t$ is assumed nonempty and compact (`IsCompact (X t)` and `(X t).Nonempty`), which by Weierstrass's theorem (`IsCompact.exists_isMaxOn`) guarantees that the continuous linear objective $y \mapsto \langle \hat w_t, y \rangle$ attains a maximum on $X_t$ (`linearMaximizer`).
4. **Instrumented scalar-operation count model (`CostM`)**: The incremental implementations `rvmFastMove`, `rvmFastState`, `rvmSkipFastState`, and `oiloLearnerState` track **instrumented scalar-operation counts of an incremental implementation; bookkeeping and memory are not charged**:
   - **Private `CostM` constructor and monadic combinators**: `CostM α` is defined with a private constructor (`private mk :: val : α, ops : ℕ`) and three monadic combinators (`CostM.pure`, `CostM.bind`, and `CostM.foldl`). Only the 10 scalar primitives (`ramAdd`, `ramSub`, `ramMul`, `ramDiv`, `ramNeg`, `ramAbs`, `ramSqrt`, and comparisons `ramLt`, `ramEq`, `ramMin`, each charging `1` operation) construct `CostM` values directly; all composite operations build both `.val` and `.ops` from the same computation via `CostM.pure`, `CostM.bind`, and `CostM.foldl`.
   - **Single `CostM` computation per vector/matrix/set operation and per piece**:
     - Vector and matrix operations (`ramVecAdd`, `ramVecSub`, `ramVecSmul`, `ramVecEq`, `ramDot`, `ramMatVec`, `ramRankOneAdd`, `ramRankOneSub`) fold the 1-op scalar primitives over `List.finRange d`.
     - On each linear piece (`ramFastPiece`, a single `CostM.bind` chain), `ramMatVec` computes $u = M v_t$ (`2d^2` ops), `ramComputeBeta` folds over $i \in A$ (`A.sort (· ≤ ·)`) to materialize $\beta_i = \langle u, v_i \rangle$ on $A$ (`2d|A|` ops, `0` outside $A$), `ramFastPieceStepTime` folds `ramFastPieceExitDelta` and `ramMin` over $A$ (`11|A|` ops), `ramVecSmul` and `ramVecAdd` advance $p_{\text{next}} = p + \delta u$ (`2d` ops), `ramUpdateSlabs` folds `ramPhiUpdate` and `ramSlabCheck` over $A$ (`4|A|` ops, returning $A_{\text{next}}$ and $\phi_{\text{next}}$ supported on $A_{\text{next}}$ with `0` outside $A_{\text{next}}$), and `shermanMorrisonDowndateSetWithCost` folds `ramDowndate` (`5d^2 + 2d + 3` ops each) over $A \setminus A_{\text{next}}$.
     - Purely rational arithmetic in $\mathrm{RVM}(\alpha)$ and $\mathrm{RVMSkip}(\alpha)$: `RVMFastState` stores `s_sq` ($s_t^2$) rather than $s_t$, and neither `ramFastPieceExitDelta`, `ramSlabCheck`, `ramStretchCreation` (`5d^2 + 2d + 4` ops), nor `ramSkipStretchCreation` (at most `5d^2 + 2d + 9` ops) calls `ramSqrt`. The primitive `ramSqrt` is used only in `ramNormalizeDiff` (`4d + 2` ops) in the OILO reduction.
   - **What is not charged**: Index and finite-set bookkeeping (`Finset.filter`, `Finset.sdiff`, `Finset.sort`, `Finset.insert`, `Function.update`, list construction `List.finRange`, recursion/loop counters), memory allocation and addressing, and the internal cost of the single linear-optimization oracle call (`linearMaximizer`) over $X_t$ in Corollary 2.2 are not charged in the scalar-operation counts.
   - **State equivalence and polynomial bounds**: `rvmRoundArithOps`, `rvmTotalArithOps`, `rvmSkipRoundArithOps`, `rvmSkipTotalArithOps`, `oiloLearnerRoundArithOps`, and `oiloLearnerTotalArithOps` read the `.roundOps` and `.totalOps` counters accumulated by `rvmFastState`, `rvmSkipFastState`, and `oiloLearnerState`. `Remark2_4_CombinatorialCounts`, `Theorem2_1_RVMRegretBound`, `Corollary2_2_OnlineInverseOptimization`, and `Proposition3_3_SkippingSmallStretches` prove both that the incremental states equal the mathematical states (`rvmState` / `rvmSkipState`) and that their accumulated operation counters satisfy the stated polynomial bounds.
5. **Non-degeneracy**: The formal statements assume $d > 0$, $R > 0$, and $\alpha > 0$ (see Definition 1.1 in `paper.tex`).
6. **Euclidean geometry on `Fin d → ℝ`**: Squared Euclidean norms and inner products are written explicitly via `dotProduct x x` and `dotProduct x y`, because Mathlib's default norm on `Fin d → ℝ` is the $\ell_\infty$ sup norm rather than the $\ell_2$ norm.
7. **Recursion fuel in `rvmMoveEval` and `rvmMovePieces`**: Both functions recurse on fuel `n = |A_t| + 1`. Since every piece before $\eta = \alpha$ revokes at least one active stretch (`h_ray_slab`), the active set strictly shrinks at each piece and fuel $|A_t| + 1$ is never exhausted; `Lemma2_3b_PiecewiseLinearMove` proves that the resulting path `rvmPath α v t` satisfies `SolvesMove` on the entire interval $[0, \alpha]$ and is the unique such path.
8. **Total-function conventions**:
   - `Decidable (inSlab …)` is provided via `Classical.propDecidable`.
   - Matrix inversion `H⁻¹` uses Mathlib's total nonsingular inverse; every matrix inverted along any run is proven symmetric positive definite (`Lemma2_3c_MetricAndDualLengthMonotone`, `h_stretch_posDef`).
   - Division in $\gamma_t = 1 / (8 s_t^2)$ uses Lean's total real division, and $s_t > 0$ is proven for every round (`Lemma2_3c_MetricAndDualLengthMonotone`).

---

## 6. Not Formalized

The following items from the paper are outside the scope of the Lean formalization:
- **Index/set bookkeeping, memory bound $O(d^2 + Td)$, and linear-optimization oracle cost**: As noted in §5.4, the `CostM` model tracks instrumented scalar-operation counts of the incremental implementation; index/set bookkeeping, memory layout and the $O(d^2 + Td)$ memory bound in Remark 2.4, and the internal cost of the single linear-optimization oracle call over $X_t$ in Corollary 2.2 are not charged.
- **Bit-level rationality and bit complexity**: While `RVM(α)` and `RVMSkip(α)` use only rational arithmetic operations (`+`, `-`, `*`, `/`, `<`, `=`, `min`, `|·|`) on $\mathbb{R}$ apart from $\alpha$ (with `ramSqrt` appearing only in `ramNormalizeDiff` in the OILO reduction), the formalization works over $\mathbb{R}$ rather than $\mathbb{Q}$ and does not formalize bit-length bounds.
- **Weaker-expert remark in Section 1**: The remark in Section 1 that the expert in OILO need only satisfy $\langle w^*, x_t \rangle \ge \langle w^*, \hat x_t \rangle$ round by round (the formal statement in `Corollary2_2_OnlineInverseOptimization` uses full optimality $\forall y \in X_t,\, \langle w^*, x_t \rangle \ge \langle w^*, y \rangle$).
- **Prose remarks after Lemma 2.5, Lemma 2.6, and Theorem 2.1**: The remark after Lemma 2.5 that the one-move inequality holds with equality when no stretch is revoked; the remark after Lemma 2.6 on the optimality of the weight constant $\tau \le 1/8$; and the remark after the proof of Theorem 2.1 that the exact minimizer $\alpha = \sqrt{8/81}\,R/\sqrt{d}$ gives constant $9/\sqrt{2} \approx 6.364$.
- **Informal discussion remarks**: Remark 2.8 (qualitative comparison with A-optimality in experimental design) and Remark 3.2 (informal discussion of alternative revocation rules and single-step overshoot).
- **Cited external results and lower bounds**: Prior bounds in Table 1 and the $\Omega(\sqrt{d})$ lower bounds cited from prior work.

---

## 7. Organization of `OIO/Statements.lean`

`OIO/Statements.lean` is organized into six sections:
- **Section 1–3 (`quadForm`, `matNorm`, `stretchMetric`, `inSlab`, `pieceExitDelta`, `pieceStepTime`, `rvmMoveEval`, `rvmMovePieces`, `rvmRevocationPoint`, `rvmRevocationTime`, `RVMState`, `rvmState`, `candActiveSet`, `SolvesMove`)**: Core geometric primitives, the continuous move ODE predicate `SolvesMove`, and the functional specification of $\mathrm{RVM}(\alpha)$.
- **Section 3b (`CostM`, `ram*`, `shermanMorrison*`, `ramFastPiece`, `rvmFastMove`, `RVMFastState`, `rvmFastStep`, `rvmFastState`, `pieceArithOps`, `downdateArithOps`, `stretchArithOps`, `skipStretchArithOps`, `rvmRoundArithOps`, `rvmTotalArithOps`)**: The `CostM` instrumented scalar-operation model (with private constructor `CostM.mk` and `CostM.foldl`) and the incremental Sherman–Morrison implementation maintaining $M = H_t^{-1}$, $s_i^2$, and active cached slab displacements $\phi_i = \langle p_t - p_{i+1}, v_i \rangle$ for $i \in A_t$.
- **Section 4 (`rvmLoss`, `rvmRegret`, `rvmXi`, `rvmStretchEndPoint`, `rvmDelta`, `rvmLambda`, `rvmSurvivingMetric`)**: Analysis quantities for the one-move bound, the lifetime ledger, and the surviving-stretch potential.
- **Section 4b (`oiloGameIndex`, `oiloHypothesis`, `linearMaximizer`, `OILOLearnerState`, `oiloLearnerState`, `oiloLearnerFastState`, `oiloLearnerHypothesis`, `oiloLearnerAction`, `oiloLearnerRoundArithOps`, `oiloLearnerTotalArithOps`, `ramNormalizeDiff`, `oiloReductionArithOps`, `oiloRoundArithOps`, `oiloTotalArithOps`)**: The online inverse linear optimization reduction, compact-set linear maximizer, and closed-loop deterministic proper learner that carries `RVMFastState`, skips tie rounds ($x_t = \hat x_t$), and tracks its own per-round and cumulative scalar operations.
- **Section 5 (`rvmNoRevokeState`, `rvmSkipState`, `rvmSkipFastStep`, `rvmSkipFastState`, `rvmSkipRoundArithOps`, `rvmSkipTotalArithOps`)**: The unrevoked variable-metric algorithm of Remark 3.1 and the small-stretch skipping variant $\mathrm{RVMSkip}(\alpha)$ of Proposition 3.3.
- **Section 6 (`Causality_OraclePrefix` through `Proposition3_3_SkippingSmallStretches`)**: The 14 top-level `Prop` statements proved in `OIO/Proofs.lean` and audited in `OIO/Audit.lean`.
