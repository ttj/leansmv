# Cellular Flows Formalization — Final Status

Lean 4 formalization of "Safe and Stabilizing Distributed Multi-Path Cellular Flows"
(Johnson & Mitra, TCS 2015).

## Completed — Single-Color Protocol

| Paper Result | Lean Theorem | Type | File |
|---|---|---|---|
| Lemma 6 (route convergence) | `route_convergence` | proved (k-induction) | RouteProofs.lean |
| Corollary 7 (next converges) | `next_convergence` | proved | RouteProofs.lean |
| Lemma 5 (no signal cycles) | `noSignalCycle2_invariant` | proved (parametric) | CellFlowsProofs.lean |
| Invariant 2 (entity disjoint) | `entity_bounded_by_transfer` | proved (per-cell) | CellFlowsProofs.lean |
| Invariant 3 (single color) | `invariant3_discrete` | proved (discrete) | CellFlowsProofs.lean |
| **Theorem 1 (safety)** | `safety_discrete` | proved (axiom-free) | DiscreteSafety.lean |
| **Theorem 2 (liveness)** | `liveness_theorem` | proved (1 fairness axiom) | CellFlowsProofs.lean |

Supporting: `distLowerBound`, `targetCorrect`, `noMutualNextHop_invariant`,
`next_left_or_none`, `signal_exclusive`, `cfSignalValid_invariant`,
`entity_accounting`, `entity_gain_requires_signal`, `no_signal_no_gain`, etc.

## Completed — Multi-Color Protocol (2D Grid)

| Paper Result | Lean Theorem | Type | File |
|---|---|---|---|
| Per-color target correct | `mcTargetCorrect_invariant` | proved | MultiColorProofs.lean |
| Lock mutual exclusion | `lockMutex_invariant` | proved | MultiColorProofs.lean |
| Lock requires intersection | `lockRequiresIntersection_invariant` | proved | MultiColorProofs.lean |
| Signal respects lock (Lemma 10) | `signalRespectsLock_invariant` | proved | MultiColorProofs.lean |
| Color consistency | `colorConsistent_invariant` | proved | MultiColorProofs.lean |
| Color preserved on transfer | `colorPreserved_step` | proved | MultiColorProofs.lean |
| Signal validity (2D neighbors) | `mcSignalValid_invariant` | proved | MultiColorProofs.lean |
| Signal exclusivity | `signalExclusive` | proved (structural) | MultiColorProofs.lean |
| Combined safety | `multiColor_safety` | proved | MultiColorProofs.lean |

## Completed — Infrastructure

| Component | Theorems | File |
|---|---|---|
| TransitionSystem framework | 8 theorems (Thms 1-8) | TransitionSystem.lean |
| k-induction (ReachableInK) | k_induction, k_induction_with_invariant | TransitionSystem.lean |
| Ranking functions | IsRankingFunction, ranking_bounded_progress | TransitionSystem.lean |
| Execution/liveness | Execution, Eventually, FairFor | TransitionSystem.lean |
| 1D topology | neighbors1D, minDist, argminDist | Defs.lean |
| 2D grid topology | neighbors2D, minDist2D, argminDist2D, manhattan | Grid.lean |
| 3-cell NuXMV instance | 3 INVARSPEC proved | Cellular3Proofs.lean |
| Axiom-free safety | DiscreteSafe as conjunction of proved invariants | DiscreteSafety.lean |

## Axiom inventory (1 remaining)

| Axiom | Purpose | Paper reference |
|---|---|---|
| `fair_execution_ranking_decreases` | Fairness of token scheduling | Assumptions 3-4, Lemmas 12-13 |

The 3 geometric axioms (GapSafe, gapSafe_init, gapPreservedByStep) from the original
`CellFlowsProofs.lean` are superseded by the axiom-free `DiscreteSafety.lean`.

## Remaining work

### Lemma 11 (lock acquisition) — not yet proved
The paper proves that under Assumption 5 (feasibility of locking after failures),
any color requesting a lock eventually gets it. This requires:
- Modeling the token cycling in the Lock subroutine more precisely
- A ranking function argument (similar to Theorem 2)
- Assumption 5 as an axiom

### Corollaries 8-9 (path/pint stabilization) — not yet proved
After routes stabilize (Lemma 6/Cor 7), path variables stabilize via gossip,
then pint stabilizes. These follow from route convergence but need explicit
proofs on the multi-color model.

### Per-color route convergence on 2D grid — not yet proved
Lemma 6 is proved for the 1D single-color model. Lifting to per-color routes
on the 2D grid follows the same k-induction pattern but needs the 2D topology
lemmas (neighbors2D properties, manhattan distance bounds).

### Removing the fairness axiom — open question
The single remaining axiom (`fair_execution_ranking_decreases`) encodes the
paper's fairness assumptions. Removing it would require modeling the token
round-robin protocol explicitly and proving it provides fair scheduling.
This is feasible but requires substantial additional modeling.

## File inventory

| File | Lines | Purpose |
|---|---|---|
| Defs.lean | 112 | DistVal, 1D topology |
| Grid.lean | 81 | 2D grid topology |
| Route.lean | 72 | Route-only TS (1D) |
| RouteProofs.lean | 462 | Lemma 6, Cor 7, distLowerBound |
| CellFlows.lean | 154 | Full single-color TS |
| CellFlowsProofs.lean | 711 | Theorem 1, 2, Lemma 5, entity flow |
| DiscreteSafety.lean | 182 | Axiom-free safety |
| MultiColor.lean | 167 | Multi-color TS (2D grid) |
| MultiColorProofs.lean | 401 | Lock mutex, signal-respects-lock, etc. |
| **Total** | **2,342** | |
