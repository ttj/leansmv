# Cellular Flows Formalization — Progress & Remaining Work

Gap analysis against TCS 2015 paper "Safe and Stabilizing Distributed Multi-Path
Cellular Flows" (Johnson & Mitra).

## Completed

### Infrastructure
- [x] `Defs.lean` — `DistVal` (fin/inf), 1D topology (`neighbors1D`, `minDist`, `argminDist`)
- [x] `Route.lean` — Route-only TS (`routeTS`, `routeFFTS`)
- [x] `CellFlows.lean` — Full Route+Signal+Move TS (`cellFlowTS`), parametric in N
- [x] `models/cellular3.smv` — 3-cell NuXMV model, translated to Lean
- [x] `TransitionSystem.lean` — `ReachableInK`, k-induction lemmas (Theorems 4-6)

### Lemma 6 — Route self-stabilization (DONE)
- `route_convergence`: after k rounds, cell i with i ≤ k has `dist i = .fin i.val`
- `distLowerBound`: dist values always ≥ true distance (inductive invariant)
- `targetCorrect`: target always has dist=0, next=none (inductive invariant)
- **File**: `RouteProofs.lean` — 31 theorems

### Corollary 7 — next variables converge (DONE)
- `next_convergence`: after k rounds, cell i (i > 0, i ≤ k) has `next i = some ⟨i-1,_⟩`
- **File**: `RouteProofs.lean`

### Lemma 5 — No signal cycles of length 2 (DONE, parametric)
- `noMutualNextHop_routeFFTS`: no two adjacent cells point at each other
- `next_left_or_none`: every cell's next-hop points left or is none
- `noSignalCycle2_invariant`: final result — no signal 2-cycles on reachable states
- **Files**: `RouteProofs.lean`, `CellFlowsProofs.lean`

### Theorem 1 — Safety (DONE, conditional with axioms)
- `GapSafe` (axiom): continuous minimum-separation safety, citing paper Lemma 4
- `gapSafe_inductive`: GapSafe is an inductive invariant (from axioms)
- `safety_theorem`: `GapSafe ∧ noSignalCycle2 ∧ cfSignalValid` on all reachable states
- **File**: `CellFlowsProofs.lean`

### Invariant 3 — Single color per cell (DONE, discrete analogue)
- `singleSourcePerRound`: each cell receives entities from at most one predecessor
- `invariant3_discrete`: `singleSourcePerRound ∧ cfSignalValid` is an invariant
- **File**: `CellFlowsProofs.lean`

### Entity flow (DONE)
- `entity_accounting`: exact Move-phase equation for non-target cells
- `entity_gain_requires_signal`: entity gain implies signal exists
- `no_signal_no_gain`, `movedOut_le_entities`, `entity_nonincreasing_without_signal`
- **File**: `CellFlowsProofs.lean`

### Signal properties (DONE)
- `signal_exclusive`, `cfSignalValid_invariant`, `cfTargetCorrect_invariant`
- `cfTargetAbsorbs_step`
- **File**: `CellFlowsProofs.lean`

### Finite instance — 3-cell line (DONE)
- `Cellular3TS_inv1_proved`, `Cellular3TS_inv2_proved`, `Cellular3TS_inv3_proved`
- **File**: `Cellular3Proofs.lean`

## Next steps

### Step 1: Ranking function infrastructure in TransitionSystem.lean
Add general-purpose definitions and proof rules for liveness reasoning:
- `RankingFunction` definition (variant that decreases under a guard)
- `ranking_bounded_liveness` theorem (ranking → bounded progress)
- `Execution` type (infinite sequence of states linked by transitions)
- `FairExecution` predicate (every enabled action eventually fires)
- `liveness_from_ranking` theorem (fair execution + ranking → eventual progress)
These are reusable across all transition systems, not just cellular flows.
- **File**: `TransitionSystem.lean`

### Step 2: Entity conservation (total count non-increasing)
- **Paper ref**: Invariant 2
- **What's needed**: Prove `totalEntities s' ≤ totalEntities s`. Per-cell
  accounting is done; global sum argument over `Fin.foldl` remains.
- **File**: `CellFlowsProofs.lean`

### Step 3: Multi-color extension (Phase 2)

### Model extension
- Add Lock subroutine (paper Fig. 9) for mutual exclusion on path intersections
- Add path, pint, lcs variables for color-shared cell detection
- Define 2D grid topology (`Fin n × Fin n`, 4-connected neighbors, Manhattan distance)
- **Files**: `Grid.lean`, `MultiColor.lean`

### Lemma 10 — Single color on color-shared cells
### Lemma 11 — Lock acquisition
### Corollaries 8-9 — path/pint stabilization

## Remaining — Priority 3: Liveness

Liveness proofs require reasoning about infinite executions and eventual progress.
The paper uses global ranking functions (Lemma 6 distance-to-target metric) and
fairness assumptions (Assumption 4: token round-robin). To support these in Lean:

### Infrastructure needed in `TransitionSystem.lean`

1. **Ranking function / variant definition**: A function `V : State → Nat` that
   strictly decreases along transitions under certain conditions. Define:
   ```lean
   def RankingFunction (ts : TransitionSystem State) (V : State → Nat) 
       (guard : State → Prop) : Prop :=
     ∀ s s', guard s → ts.next s s' → V s' < V s
   ```

2. **Bounded liveness from ranking**: If a ranking function exists under guard G,
   and G holds on all reachable states, then from any reachable state the system
   reaches V = 0 within V(s) steps:
   ```lean
   theorem ranking_terminates (ts : TransitionSystem State) (V : State → Nat)
       (guard : State → Prop) (hrank : RankingFunction ts V guard) :
     ∀ k s, ReachableInK ts k s → guard s → 
       ∃ k' s', k' ≤ k + V s ∧ ReachableInK ts k' s' ∧ V s' = 0
   ```

3. **Fairness assumption**: Model fair executions as those where every enabled
   action eventually fires. Could be an axiom on the execution:
   ```lean
   def FairExecution (ts : TransitionSystem State) (enabled : State → Fin n → Prop)
       (acts : Nat → State) : Prop :=
     (∀ k, ts.next (acts k) (acts (k+1))) ∧
     (∀ i : Fin n, ∀ k, enabled (acts k) i → ∃ k' ≥ k, <action i fires at k'>)
   ```

4. **Liveness from fairness + ranking**: Under fair execution, if the ranking
   function decreases whenever the relevant action fires, then V eventually
   reaches 0.

### Lemma 12 — Permission to move infinitely often
- Every target-connected nonempty cell gets signal infinitely often
- Uses fairness of token round-robin (Assumption 4)

### Lemma 13 — Target-connected cells signal infinitely
- Depends on Lemma 12

### Theorem 2 — Entities reach target
- Every entity on a target-connected cell eventually reaches target
- Paper proves by induction on the path sequence from cell to target
- The ranking function is: sum of distances to target for all entities

## Summary

| Paper Result | Status | Notes |
|-------------|--------|-------|
| Invariant 1 (containment) | Axiomatized | Continuous geometry |
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
| Lemma 12 (fair signaling) | Not modeled | Phase 3 — needs ranking functions |
| Lemma 13 (infinite signal) | Not modeled | Phase 3 |
| **Theorem 2 (liveness)** | Not modeled | Phase 3 — needs fairness + ranking |
