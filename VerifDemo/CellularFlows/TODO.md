# Cellular Flows Formalization — Progress & Remaining Work

Gap analysis against TCS 2015 paper "Safe and Stabilizing Distributed Multi-Path
Cellular Flows" (Johnson & Mitra).

## Completed

### Infrastructure
- [x] `Defs.lean` — `DistVal` (fin/inf), 1D topology
- [x] `Route.lean` — Route-only TS (`routeTS`, `routeFFTS`)
- [x] `CellFlows.lean` — Full Route+Signal+Move TS (`cellFlowTS`), parametric in N
- [x] `models/cellular3.smv` — 3-cell NuXMV model, translated to Lean
- [x] `TransitionSystem.lean` — `ReachableInK`, k-induction (Theorems 4-6)
- [x] `TransitionSystem.lean` — `Execution`, `IsRankingFunction`, `ranking_bounded_progress`, `ranking_implies_eventually`, `Eventually`, `FairFor` (Theorems 7-8)

### Lemma 6 — Route self-stabilization (DONE)
- `route_convergence`, `distLowerBound`, `targetCorrect`
- **File**: `RouteProofs.lean`

### Corollary 7 — next variables converge (DONE)
- `next_convergence`
- **File**: `RouteProofs.lean`

### Lemma 5 — No signal cycles of length 2 (DONE, parametric)
- `noMutualNextHop_routeFFTS`, `next_left_or_none`, `noSignalCycle2_invariant`
- **Files**: `RouteProofs.lean`, `CellFlowsProofs.lean`

### Theorem 1 — Safety (DONE, conditional with axioms)
- `GapSafe` (axiom), `gapSafe_inductive`, `safety_theorem`
- **File**: `CellFlowsProofs.lean`

### Invariant 3 — Single color per cell (DONE, discrete analogue)
- `singleSourcePerRound`, `invariant3_discrete`
- **File**: `CellFlowsProofs.lean`

### Entity flow (DONE, per-cell)
- `entity_accounting`, `entity_gain_requires_signal`
- `no_signal_no_gain`, `movedOut_le_entities`, `entity_nonincreasing_without_signal`
- **File**: `CellFlowsProofs.lean`

### Signal properties (DONE)
- `signal_exclusive`, `cfSignalValid_invariant`, `cfTargetCorrect_invariant`, `cfTargetAbsorbs_step`
- **File**: `CellFlowsProofs.lean`

### Finite instance — 3-cell line (DONE)
- `Cellular3TS_inv1_proved`, `Cellular3TS_inv2_proved`, `Cellular3TS_inv3_proved`
- **File**: `Cellular3Proofs.lean`

## Next steps

### Step 1: Entity conservation (total count non-increasing)
- **Paper ref**: Invariant 2
- **What's needed**: Prove `totalEntities s' ≤ totalEntities s`. Per-cell
  accounting is done; global sum argument over `Fin.foldl` remains.
- **File**: `CellFlowsProofs.lean`

### Step 2: Liveness — Theorem 2 (entities reach target)
Now that ranking function infrastructure exists in `TransitionSystem.lean`,
we can tackle the paper's liveness argument:

- **Ranking function**: `V(s) = Σ_i entities(i) * dist(i)` — weighted sum of
  entity counts times their distance to target. Each move step decreases V
  by at least 1 (entity moves one cell closer to target).

- **Lemma 12 (fair signaling)**: Under the paper's Assumption 4 (fairness),
  every target-connected nonempty cell gets signal infinitely often.
  Model the token round-robin fairness as `FairFor exec enabled fired`
  where `enabled s = ∃ i, entities i > 0 ∧ target-connected i` and
  `fired s = ∃ i, entities moved from i toward target`.

- **Theorem 2**: Combine ranking function + fairness + route convergence
  to show: in any fair execution, V eventually reaches 0 (all entities
  at target or removed).

- **Approach**: Define ranking function on `CellFlowState`, prove it
  decreases when any entity moves, invoke `ranking_implies_eventually`.

- **Files**: `CellFlowsProofs.lean` or new `LivenessProofs.lean`

### Step 3: Multi-color extension (Phase 2)
- Add Lock subroutine (paper Fig. 9) for path intersection mutual exclusion
- Add path, pint, lcs variables
- Define 2D grid topology (`Fin n × Fin n`, 4-connected neighbors)
- Prove Lemma 10 (single color CSC), Lemma 11 (lock acquisition), Cor 8-9
- **Files**: `Grid.lean`, `MultiColor.lean`, `MultiColorProofs.lean`

## Summary

| Paper Result | Status | Notes |
|-------------|--------|-------|
| Invariant 1 (containment) | **Axiomatized** | Continuous geometry |
| Invariant 2 (disjoint sets) | **Per-cell DONE** | Global sum remaining |
| Invariant 3 (single color) | **DONE** (discrete) | `singleSourcePerRound` |
| Lemma 4 (H(x) preserved) | **Axiomatized** | Cited in `GapSafe` |
| Lemma 5 (no signal cycles) | **DONE** | Parametric, all N |
| Lemma 6 (route convergence) | **DONE** | k-induction proof |
| Corollary 7 (next converges) | **DONE** | Follows from Lemma 6 |
| **Theorem 1 (safety)** | **DONE** (conditional) | Axiom + proved invariants |
| Corollaries 8-9 (path/pint) | Not modeled | Phase 2 |
| Lemma 10 (single color CSC) | Not modeled | Phase 2 |
| Lemma 11 (lock acquisition) | Not modeled | Phase 2 |
| Lemma 12 (fair signaling) | Not modeled | Infrastructure ready |
| Lemma 13 (infinite signal) | Not modeled | Depends on Lemma 12 |
| **Theorem 2 (liveness)** | Not modeled | Infrastructure ready |
