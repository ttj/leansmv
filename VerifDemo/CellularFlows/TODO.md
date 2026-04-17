# Cellular Flows Formalization — Final Status

Lean 4 formalization of "Safe and Stabilizing Distributed Multi-Path Cellular Flows"
(Johnson & Mitra, TCS 2015). ~2,900 lines of Lean, zero `sorry`, 26 build jobs.

See the correspondence table in `Defs.lean` for the full paper-to-Lean mapping.

## All paper results covered

### Proved (no axioms)
- Lemma 5 (no signal cycles) — `noSignalCycle2_invariant`
- Lemma 6 (route convergence, 1D) — `route_convergence`
- Lemma 6 (route convergence, 2D) — `mc_route_convergence`
- Corollary 7 (next convergence) — `next_convergence`
- Invariant 2 (entity conservation) — `entity_bounded_by_transfer`
- Invariant 3 (single color) — `invariant3_discrete`
- **Theorem 1 (safety, axiom-free)** — `safety_discrete`
- Lock mutual exclusion — `lockMutex_invariant`
- Signal respects lock (Lemma 10) — `signalRespectsLock_invariant`
- Per-color dist lower bound (2D) — `mcDistLowerBound_invariant`
- Manhattan triangle inequality — `manhattan_neighbor_triangle` (proved, not axiom)
- Neighbor membership — `neighbors2D_mem_areNeighbors` (proved, not axiom)
- + 50 supporting lemmas

### Proved (conditional on axioms)
- **Theorem 2 (liveness)** — `liveness_theorem` (1 fairness axiom)
- Lemma 11 (lock acquisition) — `lock_acquisition` (1 fairness axiom)
- Corollaries 8-9 (path/pint stable) — `route_stable_implies_all_stable` (2 gossip axioms)
- Lemma 6 2D convergence — `mc_route_convergence` (1 topology axiom)

### Active axioms (7 total; 3 superseded)
| Axiom | Category | Could prove? |
|---|---|---|
| `GapSafe` | **Superseded** | — |
| `gapSafe_init` | **Superseded** | — |
| `gapPreservedByStep` | **Superseded** | — |
| `exists_closer_neighbor` | Topology | Yes (verbose Fin case analysis) |
| `path_stabilization` | Gossip convergence | Needs gossip round model |
| `pint_stabilization` | Gossip convergence | Follows from path |
| `fair_execution_ranking_decreases` | Fairness (Assumption 4) | Needs token scheduler model |
| `lock_fairness_general` | Fairness (Assumption 4) | Needs token scheduler model |

**Non-superseded active axioms: 5** (1 topology, 2 gossip, 2 fairness)

## Remaining extensions (optional)

### Prove `exists_closer_neighbor` (LOW effort)
The only remaining provable axiom. Requires case analysis on whether rows or
columns of i and t differ, then constructing the appropriate neighbor via
upNeighbor/downNeighbor/leftNeighbor2D/rightNeighbor2D and showing membership
in neighbors2D. Verbose but purely mechanical.

### Model gossip protocol explicitly (MEDIUM effort)
Would eliminate `path_stabilization` and `pint_stabilization` axioms. Requires
adding explicit gossip round state (which cells have propagated path info to
which neighbors) and proving convergence in diameter rounds.

### Model token scheduler explicitly (HIGH effort)
Would eliminate both fairness axioms. Requires adding explicit `token` state
variable with round-robin cycling and proving fair scheduling.

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
| MultiColor.lean | 211 | — | — |
| MultiColorProofs.lean | 900 | 59 | 4 |
| **Total** | **~2,946** | **123** | **8 (3 superseded)** |
