# Cellular Flows Formalization — Progress & Remaining Work

Gap analysis against TCS 2015 paper "Safe and Stabilizing Distributed Multi-Path Cellular Flows" (Johnson & Mitra).

## Completed

### Infrastructure
- [x] `Defs.lean` — `DistVal` (fin/inf), 1D topology (`neighbors1D`, `minDist`, `argminDist`)
- [x] `Route.lean` — Route-only TS (`routeTS`, `routeFFTS`)
- [x] `CellFlows.lean` — Full Route+Signal+Move TS (`cellFlowTS`), parametric in N
- [x] `models/cellular3.smv` — 3-cell NuXMV model, translated to Lean
- [x] `TransitionSystem.lean` — Added `ReachableInK`, k-induction lemmas (Theorems 4-6)

### Lemma 6 — Route self-stabilization (DONE)
- `route_convergence`: after k rounds, every cell i with i ≤ k has `dist i = .fin i.val`
- `distLowerBound`: dist values are always ≥ true distance (inductive invariant)
- `targetCorrect`: target always has dist=0, next=none (inductive invariant)
- **File**: `RouteProofs.lean`

### Signal properties (DONE)
- `signal_exclusive`: each cell signals at most one predecessor (structural, all states)
- `cfSignalValid_invariant`: every non-none signal points to a valid neighbor (inductive invariant)
- `cfTargetCorrect_invariant`: target always has dist=0/next=none in full system
- `cfTargetAbsorbs_step`: target absorbs arriving entities
- **File**: `CellFlowsProofs.lean`

### Lemma 5 — No signal cycles (PARTIAL)
- `noSignalCycle2_init`: no cycles in initial state
- `noMutualNextHop_implies_noSignalCycle2`: if no mutual next-hops, then no signal cycles
- Factored: full result conditional on `noMutualNextHop` being invariant
- `Cellular3TS_inv1_proved`: proved for 3-cell finite instance
- **File**: `CellFlowsProofs.lean`

### Entity flow (PARTIAL)
- `no_signal_no_gain`: unsignaled non-target cells don't gain entities
- `movedOut_le_entities`: moved-out count ≤ entity count
- `entity_nonincreasing_without_signal`: exact accounting when no signal
- **File**: `CellFlowsProofs.lean`

### Finite instance (DONE)
- `Cellular3TS_inv1_proved`: no signal cycle (3-cell)
- `Cellular3TS_inv2_proved`: dist0 = 0 (3-cell)
- `Cellular3TS_inv3_proved`: dist1 ≤ 3 (3-cell)
- **File**: `Cellular3Proofs.lean`

## Next steps — Priority 1

### 1. Corollary 7 — next variables converge
- **Paper**: After convergence, next_i = argmin neighbor = left neighbor (toward target).
- **What's needed**: After k rounds with k ≥ i, `next i = some ⟨i-1, _⟩` for i > 0. Follows from `route_convergence`: once dist values are correct, `argminDist` with `dist (i-1) = .fin (i-1)` and `dist (i+1) = .fin (i+1)` gives the left neighbor.
- **File**: `RouteProofs.lean`

### 2. `noMutualNextHop` invariant — completes Lemma 5
- **Paper**: Two adjacent cells never both route toward each other.
- **What's needed**: Prove as inductive invariant using `distLowerBound`. Key argument: if `next i = some j` then `dist j < dist i` (argmin chose j as closer to target). If also `next j = some i` then `dist i < dist j` — contradiction.
- **Approach**: Need a lemma `argminDist_lt`: if `argminDist dist nbrs = some j` and dist j = .fin m, then `minDist dist nbrs = .fin m` and `dist i = .fin (m+1)`. Combined with the symmetric case gives `m+1 < m+1`, impossible.
- **File**: `CellFlowsProofs.lean`

### 3. Invariant 3 — Single color per cell
- **Paper**: All entities on a cell have the same color.
- **What's needed**: Extend `CellFlowState` with `color : Fin n → Option (Fin numColors)`. Add Signal constraint: only signal predecessor j if `color j = color i` or `color i = none`. Prove color is preserved.
- **Files**: `CellFlows.lean` (extend state + TS), `CellFlowsProofs.lean` (prove)

### 4. Entity conservation
- **Paper**: Total entity count is non-increasing (entities move or are absorbed, never duplicated).
- **What's needed**: Prove `totalEntities s' ≤ totalEntities s` for each step. Requires summing `movedOut`/`movedIn` across all cells and showing transfers cancel.
- **File**: `CellFlowsProofs.lean`

### 5. Theorem 1 — Safety (conditional statement)
- **Paper**: Safe(x) for all reachable states — entities separated by ≥ d.
- **What's needed**: State as a conditional theorem referencing the paper. The discrete invariants we proved (Inv 2-3, Lemma 5) are the preconditions; the geometric bridge (Lemma 4, Assumptions 1-2) is axiomatized with a comment citing the paper's proof.
- **File**: `CellFlowsProofs.lean`

## Priority 2: Multi-color extension

### Model extension
- Add Lock subroutine (paper Fig. 9)
- Add path, pint, lcs variables for intersection detection
- Add mutual exclusion logic for color-shared cells
- **Files**: `Grid.lean` (2D topology), `MultiColor.lean` (extended state + TS)

### Lemma 10 — Single color on color-shared cells
### Lemma 11 — Lock acquisition
### Corollaries 8-9 — path/pint stabilization

## Priority 3: Liveness

### Lemma 12 — Permission to move infinitely often
### Lemma 13 — Target-connected cells signal infinitely
### Theorem 2 — Entities reach target

## Summary

| Result | Status | Next action |
|--------|--------|-------------|
| Lemma 6 (route convergence) | **DONE** | — |
| Corollary 7 (next convergence) | Not proved | Derive from Lemma 6 |
| Lemma 5 (no signal cycles) | **Factored** | Prove `noMutualNextHop` invariant |
| Invariant 3 (single color) | Not modeled | Add color field, prove |
| Entity conservation | Partial | Prove total non-increasing |
| Theorem 1 (safety) | Not stated | State conditionally |
| Lemma 10 (single color CSC) | Not modeled | Phase 4 |
| Lemma 11 (lock acquisition) | Not modeled | Phase 4 |
| Corollaries 8-9 | Not modeled | Phase 4 |
| Lemmas 12-13 (fairness) | Not modeled | Phase 4 |
| Theorem 2 (liveness) | Not modeled | Phase 4 |
