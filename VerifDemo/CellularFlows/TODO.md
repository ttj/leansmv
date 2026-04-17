# Cellular Flows Formalization — Progress & Remaining Work

Gap analysis against TCS 2015 paper "Safe and Stabilizing Distributed Multi-Path
Cellular Flows" (Johnson & Mitra).

## Completed — Single-Color Protocol (all proved or axiomatized)

### Infrastructure
- [x] `Defs.lean` — `DistVal` (fin/inf), 1D topology
- [x] `Route.lean` — Route-only TS (`routeTS`, `routeFFTS`)
- [x] `CellFlows.lean` — Full Route+Signal+Move TS (`cellFlowTS`), parametric in N
- [x] `models/cellular3.smv` — 3-cell NuXMV model, translated to Lean
- [x] `TransitionSystem.lean` — `ReachableInK`, k-induction (Theorems 4-6)
- [x] `TransitionSystem.lean` — `Execution`, `IsRankingFunction`, `ranking_bounded_progress`, `ranking_implies_eventually`, `Eventually`, `FairFor` (Theorems 7-8)

### Safety — Theorem 1
| Paper Result | Lean Theorem | Type |
|---|---|---|
| Invariant 1 (containment) | `GapSafe` | axiom (continuous geometry) |
| Invariant 2 (disjoint sets) | `entity_bounded_by_transfer`, `target_entity_bounded` | proved (per-cell) |
| Invariant 3 (single color) | `invariant3_discrete` | proved (discrete analogue) |
| Lemma 4 (H(x) preserved) | `gapPreservedByStep` | axiom (continuous geometry) |
| Lemma 5 (no signal cycles) | `noSignalCycle2_invariant` | proved (parametric, all N) |
| Lemma 6 (route convergence) | `route_convergence` | proved (k-induction) |
| Corollary 7 (next converges) | `next_convergence` | proved |
| **Theorem 1 (safety)** | `safety_theorem` | proved (conditional on axioms) |

### Liveness — Theorem 2
| Paper Result | Lean Theorem | Type |
|---|---|---|
| Lemma 12 (fair signaling) | `fair_execution_ranking_decreases` | axiom (fairness assumption) |
| **Theorem 2 (liveness)** | `liveness_theorem` | proved (conditional on fairness axiom) |

### Additional proved properties
- `signal_exclusive`, `cfSignalValid_invariant`, `cfTargetCorrect_invariant`
- `cfTargetAbsorbs_step`, `entity_accounting`, `entity_gain_requires_signal`
- `no_signal_no_gain`, `movedOut_le_entities`, `entity_nonincreasing_without_signal`
- `distLowerBound`, `noMutualNextHop_invariant`, `next_left_or_none`
- 3-cell finite instance: `Cellular3TS_inv1/2/3_proved`

### Axiom inventory (4 total, all cite specific paper results)
1. `GapSafe` — continuous safety predicate (Invariant 1)
2. `gapSafe_init` — initial states satisfy GapSafe (paper Assumption 3)
3. `gapPreservedByStep` — GapSafe preserved by transitions (paper Lemma 4)
4. `fair_execution_ranking_decreases` — fair signaling decreases ranking (paper Lemmas 12-13, Assumptions 3-4)

## Remaining — Multi-Color Extension (Phase 2)

The single-color protocol is fully covered. The journal paper extends it with
multiple entity colors (each with distinct source-target pairs), path intersections,
and a Lock subroutine for mutual exclusion on color-shared cells. This extension
introduces deadlock avoidance and requires significant new model infrastructure.

### What's needed

#### Model files
- **`Grid.lean`** — 2D grid topology: `Fin n × Fin n`, 4-connected neighbors, Manhattan distance. The 1D line is a special case; the 2D grid matches the paper's general setting.
- **`MultiColor.lean`** — Extended state with per-color routing (dist/next/path arrays indexed by color), Lock subroutine (paper Fig. 9), path/pint/lcs intersection variables, color-shared cell detection.

#### Proof files
- **`MultiColorProofs.lean`** — proofs for:

| Paper Result | Description | Difficulty |
|---|---|---|
| Corollary 8 | path variables stabilize after routes stabilize | Medium |
| Corollary 9 | pint variables stabilize | Medium |
| Lemma 10 | Single color on color-shared cells (under no failures) | Medium |
| Lemma 11 | Lock acquisition (any requesting color eventually gets lock) | Hard |
| Assumption 5 | Feasibility of locking after failures (axiom) | Axiom |

#### Key design decisions
1. **State type**: `MCState (n : Nat) (nc : Nat)` with `nc` colors. Each cell has `dist : Fin nc → DistVal`, `next : Fin nc → Option CellId`, `path : Fin nc → Finset CellId`, `lock : Fin nc → Bool`, etc.
2. **Lock subroutine**: Mutual exclusion via distributed algorithm (paper Fig. 9, lines 10-15). Uses `pint[c]` (path intersections) and `lcs[c]` (lock colors) to determine which cells need locks.
3. **Entity graph**: `G_E(x, c)` — the subgraph of the routing graph for color c. Vertices are cells with entities of color c or source cells. Edges follow next pointers.
4. **Color-shared cells**: `CSC(x, c)` — cells in the entity graph of color c that intersect with other colors' entity graphs.

#### Proof strategy
- Route convergence (Lemma 6) generalizes directly to per-color routes on 2D grids
- Path/pint convergence (Corollaries 8-9) follow from route convergence + gossip protocol
- Lemma 10: inductive invariant on color assignment at CSC cells
- Lemma 11: uses mutual exclusion correctness of the distributed lock algorithm

### Estimated effort
The multi-color extension is a substantial model expansion (~500 lines of definitions, ~500 lines of proofs). The Lock subroutine alone has 17 lines of pseudocode (Fig. 9) with complex state interactions. This is appropriate as a separate focused effort.

## Summary

| Paper Result | Status |
|---|---|
| Theorem 1 (safety) | **DONE** (conditional on 3 geometric axioms) |
| Theorem 2 (liveness) | **DONE** (conditional on 1 fairness axiom) |
| Corollaries 8-9 | Not modeled (Phase 2) |
| Lemma 10 (single color CSC) | Not modeled (Phase 2) |
| Lemma 11 (lock acquisition) | Not modeled (Phase 2) |
