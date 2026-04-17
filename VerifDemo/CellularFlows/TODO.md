# Cellular Flows Formalization — Status & Extensions

Lean 4 formalization of "Safe and Stabilizing Distributed Multi-Path Cellular Flows"
(Johnson & Mitra, TCS 2015). 2,700+ lines of Lean, zero `sorry`, 26 build jobs.

See the correspondence table in `Defs.lean` for the full paper-to-Lean mapping.

## Current status

### Proved (no axioms needed)
- Lemma 5 (no signal cycles) — `noSignalCycle2_invariant`
- Lemma 6 (route convergence, 1D) — `route_convergence`
- Corollary 7 (next convergence, 1D) — `next_convergence`
- Invariant 2 (entity conservation, per-cell) — `entity_bounded_by_transfer`
- Invariant 3 (single color) — `invariant3_discrete`
- **Theorem 1 (safety, axiom-free)** — `safety_discrete` in DiscreteSafety.lean
- Lock mutual exclusion — `lockMutex_invariant`
- Signal respects lock (Lemma 10) — `signalRespectsLock_invariant`
- Per-color dist lower bound (2D) — `mcDistLowerBound_invariant`
- + 30 supporting lemmas

### Proved (conditional on axioms)
- **Theorem 2 (liveness)** — `liveness_theorem` (1 fairness axiom)
- Lemma 11 (lock acquisition) — `lock_acquisition` (1 fairness axiom)
- Corollaries 8-9 (path/pint stable) — `route_stable_implies_all_stable` (2 gossip axioms)

### Axioms (9 total; 3 superseded)
| Axiom | Status | Effort to eliminate |
|---|---|---|
| `GapSafe` | **Superseded** by DiscreteSafety.lean | — |
| `gapSafe_init` | **Superseded** by DiscreteSafety.lean | — |
| `gapPreservedByStep` | **Superseded** by DiscreteSafety.lean | — |
| `manhattan_neighbor_triangle` | Active (provable) | Low — case analysis on Fin coordinates |
| `neighbors2D_mem_areNeighbors` | Active (provable) | Low — unfold neighbors2D definition |
| `path_stabilization` | Active | Medium — needs gossip round modeling |
| `pint_stabilization` | Active | Medium — follows from path_stabilization |
| `fair_execution_ranking_decreases` | Active (assumption) | High — needs explicit token scheduler |
| `lock_fairness_general` | Active (assumption) | High — needs explicit token scheduler |

**Active axioms: 6 (2 provable geometric, 2 gossip convergence, 2 fairness assumptions)**

## Extensions — remaining gaps

### E1: Prove the two geometric axioms (LOW effort)
- `manhattan_neighbor_triangle`: for 4-connected neighbors on a grid, Manhattan
  distance changes by exactly 1. Proof: case split on which direction the neighbor
  is (up/down/left/right), each changes one coordinate by 1.
- `neighbors2D_mem_areNeighbors`: members of `neighbors2D i` satisfy `areNeighbors2D`.
  Proof: unfold `neighbors2D`, `upNeighbor`, etc., show each branch produces a
  valid neighbor pair.
- **Result**: reduces active axiom count from 6 to 4.
- **File**: `MultiColorProofs.lean`

### E2: 2D route convergence (MEDIUM effort)
- Currently `route_convergence` is only for the 1D line (`routeFFTS`).
  `mcDistLowerBound` proves the lower bound on 2D but not full convergence.
- **What's needed**: After k rounds on the 2D grid, cells at Manhattan distance ≤ k
  from target have `dist[c][i] = .fin (manhattan i (targets c))`.
- **Approach**: Same k-induction as 1D, using `manhattan_neighbor_triangle` (once
  proved per E1) to show `minDist2D` over neighbors ≤ manhattan(i,target)-1.
- **File**: `MultiColorProofs.lean`

### E3: Multi-color Move phase entity accounting (MEDIUM effort)
- `multiColorTS` has `True` placeholder for non-target entity accounting (line 153).
- **What's needed**: Add `movedOut`/`movedIn` helpers for `MCState` (analogous to
  `CellFlows.lean:45-59`) and replace `True` with exact accounting:
  `entities' i = entities i - movedOut + movedIn`.
- **Result**: enables proving multi-color entity conservation.
- **Files**: `MultiColor.lean` (extend TS), `MultiColorProofs.lean` (prove conservation)

### E4: Entity graph definitions (LOW effort, cosmetic)
- Paper defines `G_E(x,c)`, `V_E(x,c)`, `E_E(x,c)` (entity graph for color c)
  and `SC(x,c)`, `CSC(x,c)` (shared/color-shared cells) explicitly in Section 3.3.2.
- Currently implicit in `path`/`pint` variables.
- **What's needed**: Add explicit Lean definitions for these predicates (no new proofs,
  just named definitions matching the paper).
- **File**: `MultiColor.lean` or new `EntityGraph.lean`

### E5: Target-connected predicate (LOW effort, cosmetic)
- Paper defines `TC(x,c) = {i ∈ NF(x) | ρ_c(x,i) < ∞}` — cells reachable to target.
- Our theorems quantify over all cells (more general).
- **What's needed**: Define `targetConnected` predicate. Optionally restate Theorems 1-2
  restricted to TC for exact paper correspondence.
- **File**: `MultiColor.lean` or `CellFlows.lean`

### E6: Signal subroutine detail (LOW priority)
- Paper Fig. 10 computes `cn` (color set from predecessors), `NEPrev` (nonempty
  predecessors for chosen color), uses `token` for round-robin fairness.
- Our model constrains signal structurally but doesn't model the explicit computation.
- **Impact**: proofs are valid on the structural constraints; adding computation detail
  would make the model more faithful but wouldn't change proved properties.
- **Recommendation**: leave as-is unless needed for a specific theorem.

## File inventory

| File | Lines | Theorems | Axioms |
|---|---|---|---|
| Defs.lean | 158 | — | — |
| Grid.lean | 89 | — | — |
| Route.lean | 72 | — | — |
| RouteProofs.lean | 462 | 31 | — |
| CellFlows.lean | 154 | — | — |
| CellFlowsProofs.lean | 718 | 25 | 4 (3 superseded) |
| DiscreteSafety.lean | 182 | 8 | — |
| MultiColor.lean | 167 | — | — |
| MultiColorProofs.lean | 714 | 20 | 5 |
| **Total** | **~2,716** | **84** | **9 (3 superseded)** |
