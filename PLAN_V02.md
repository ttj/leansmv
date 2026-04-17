# Plan: Fix Formalization Soundness Issues + Paper Ambiguity Report

## Context

A fresh comprehensive audit of the ~6,000-line Lean formalization against
the TCS 2015 paper identified **two critical formalization bugs** that
could let a user derive `False`, plus a medium-severity incompleteness
and several paper ambiguities worth documenting. The discrete protocol
proofs are sound; the issues are in bridge axioms and fairness.

**No paper bugs were found** — the paper's Theorems 1 & 2 are sound. The
issues are in how we axiomatized the paper's claims.

This plan addresses:
1. **Critical fix**: `continuous_safety_bridge` over-claims (applies to any
   `ContinuousMCState`, not just reachable ones)
2. **High fix**: Fairness axioms (`fair_execution_ranking_decreases`,
   `lock_fairness_general`) don't take a fairness hypothesis and are
   inconsistent with the permissive transition system
3. **Medium fix**: `MCDiscreteSafe` only bundles 3 invariants but the
   paper's Theorem 1 relies on more (Invariant 2, Lemma 4 gap property)
4. **Report**: Paper-level ambiguities surfaced by formalization

## Critical fix 1 — `continuous_safety_bridge` reachability

**Files**: `VerifDemo/CellularFlows/ContinuousModel.lean:168`,
`VerifDemo/CellularFlows/EuclideanModel.lean:120`

**Problem**: Current axiom signature is
```lean
axiom continuous_safety_bridge {α} [MetricPoint α] {n nc : Nat}
    (params : CellFlowsParameters) (s : ContinuousMCState α n nc) :
    MCDiscreteSafe s.discrete → ContinuousSafe params s
```

`s : ContinuousMCState` is an arbitrary structure — `discrete` is a valid
MCState, `positions` is an arbitrary list with count-consistency. You can
build a state where `discrete` satisfies `MCDiscreteSafe` (e.g., any
freshly constructed state with non-zero entities and no signals/locks)
while `positions` places entities at identical coordinates. The axiom
asserts this arrangement is safe — false when `d > 0`. **Derives `False`**.

**Fix**: Require reachability at the *continuous* level. Approach:
1. Define a `ReachableContinuousState` predicate that combines
   (a) `Reachable (multiColorTS n nc targets) s.discrete` (discrete reachable)
   (b) A condition that `positions` at each step were consistent with the
       Move phase's transfers (entities that arrived were placed at valid
       transfer regions, stationary entities kept their positions).
2. Rewrite the bridge axiom to take this hypothesis:
   ```lean
   axiom continuous_safety_bridge
       (targets : Fin nc → CellId2D n)
       (params : CellFlowsParameters)
       (s : ContinuousMCState α n nc)
       (hreach : ReachableContinuousState targets s) :
       MCDiscreteSafe s.discrete → ContinuousSafe params s
   ```
3. Update `continuous_theorem_1` / `continuous_theorem_1_real` and
   `_reachable` variants to thread the reachability hypothesis.

Since we don't actually have a continuous transition system, the
simplest correct form is: take as hypothesis the continuous-state-level
invariant we want to assume (e.g., "positions were validly placed under
Move's transfer-region geometry"). Keep it opaque like Assumptions 1-2.

**Mirror fix in `EuclideanModel.lean`** for `continuous_safety_bridge_real`.

## Critical fix 2 — Fairness axioms need a fairness hypothesis

**Files**: `VerifDemo/CellularFlows/CellFlowsProofs.lean:627`,
`VerifDemo/CellularFlows/MultiColorProofs.lean:811`

**Problem**: Current axiom
```lean
axiom fair_execution_ranking_decreases {n : Nat}
    (exec : Execution (cellFlowTS n)) :
    IsRankingFunction (cellFlowTS n) livenessRank (fun _ => True)
```
takes any `Execution` (no fairness hypothesis) and asserts livenessRank
strictly decreases on all steps. But the transition system allows stutter
steps where `signal i = none` everywhere (no entities move), so
livenessRank stays constant. The axiom is therefore inconsistent with
the (permissive) transition system: apply it to a stutter execution to
derive `V s > 0 → V s < V s`, i.e., `False`.

**Fix**:
1. Define `IsFairExecution` explicitly, matching paper Assumption 4:
   ```lean
   /-- Paper Assumption 4 (fair source/signal scheduling): every
       target-connected non-empty cell receives signal permission
       infinitely often. -/
   def IsFairExecution {n : Nat} (exec : Execution (cellFlowTS n)) : Prop :=
     ∀ i : Fin n, ∀ k : Nat,
       (exec.states k).entities i > 0 → (∃ m, (exec.states k).dist i = .fin m) →
       ∃ k' ≥ k, (exec.states k').entities i < (exec.states k).entities i
   ```
   (Or an equivalent predicate; exact form can be refined.)
2. Rewrite axiom to take a fairness hypothesis:
   ```lean
   axiom fair_execution_ranking_decreases {n : Nat}
       (exec : Execution (cellFlowTS n))
       (hfair : IsFairExecution exec) :
       ∀ k, livenessRank (exec.states k) > 0 →
         ∃ k' ≥ k, livenessRank (exec.states k') < livenessRank (exec.states k)
   ```
3. Update `liveness_theorem` signature to take `hfair` and thread it through.
4. Mirror for `lock_fairness_general` in `MultiColorProofs.lean`.

Note: the axiom shape changes from "IsRankingFunction" (which is per-step
decrease) to "eventual strict decrease from any positive-V step". This
matches the paper's "infinitely often" statement and is consistent with
stutter steps.

## Medium fix 3 — `MCDiscreteSafe` completeness

**File**: `VerifDemo/CellularFlows/ContinuousModel.lean:130`

**Problem**: Current definition:
```lean
def MCDiscreteSafe (s : MCState n nc) : Prop :=
  lockMutex s ∧ signalRespectsLock s ∧ colorConsistent s
```
bundles only 3 invariants. The paper's Theorem 1 proof also requires:
- Invariant 2 (entity disjoint between cells) — we proved
  `entity_bounded_by_transfer` but don't bundle it
- Lemma 5 (no signal cycles, `noSignalCycle2_invariant`) — proved, not bundled
- Lemma 4 (H(x) gap property) — axiomatized
- Signal validity (`mcSignalValid`) — proved, not bundled

**Fix**: Expand `MCDiscreteSafe` to bundle every discrete invariant that
the continuous bridge actually uses:
```lean
def MCDiscreteSafe (s : MCState n nc) : Prop :=
  lockMutex s ∧
  signalRespectsLock s ∧
  colorConsistent s ∧
  noSignalCycle2 s ∧            -- Lemma 5
  mcSignalValid s ∧             -- signal points to valid neighbors
  lockRequiresIntersection s    -- lock ⟹ needsLock ⟹ pint chain
```
Then `mcDiscreteSafe_invariant` extends to include all these, each of
which is already proved in `MultiColorProofs.lean`. This makes the
axiomatic bridge's hypothesis match what the paper's proof actually uses.

## Paper-ambiguity report (documentation only)

Create `VerifDemo/CellularFlows/PaperAmbiguities.md` (or extend `TODO.md`)
documenting ambiguities surfaced by formalization. These are NOT paper
bugs, but places where the paper's statements allow multiple
interpretations that formalization forces us to pick one of:

1. **argminDist tie-breaking**: Paper Fig. 4 uses lexicographic argmin over
   `(dist, ID)` pairs. Our `argminDist` (Defs.lean) breaks ties by list
   order, not by cell ID. For the 1D line / 2D grid, the neighbor lists
   happen to be in a canonical order so both tie-breaking rules are
   deterministic, but they differ in *which* neighbor is chosen when
   multiple have equal distance. Both suffice for correctness; worth
   noting.
2. **Corollary 7 rounds bound**: paper says "within 2Δ(x) rounds after the
   last fail transition, for any c ∈ C, every cell i target-connected to
   color c has x.next_i[c] equal to the next cell along such a route."
   Our `mc_route_convergence` is within `manhattan(i, target)` rounds,
   measured from the canonical init state. The paper's bound applies to
   *any* reachable state after failures cease, and uses the *actual
   diameter* of the non-failed subgraph, not Manhattan distance. Our
   stabilization theorems (`route_self_stabilizes` etc.) address the
   post-failure case but for 1D-line/2D-grid topology only.
3. **Assumption 2 scope**: Paper invokes Assumption 2 (transfer
   feasibility) in the geometric argument for Theorem 1 but does not
   specifically identify which Lemma needs it. Our Assumption 2 axiom is
   declared but never explicitly used. This is appropriate — we
   axiomatize the whole discrete→continuous bridge, which implicitly
   subsumes Assumption 2.
4. **Fairness Assumption 4 wording**: paper states this in terms of
   "source cells placing entities without perpetually blocking any
   non-empty non-faulty neighbors". Formalization requires a precise
   infinitely-often statement — see fix 2 above.

## Order of work

1. **MCDiscreteSafe completeness** (medium fix) — smallest, foundation
   for the bridge fix. Expand the predicate + update
   `mcDiscreteSafe_invariant`. ~40 lines.
2. **continuous_safety_bridge reachability** (critical fix) — restructure
   bridge axiom + theorems in both `ContinuousModel.lean` and
   `EuclideanModel.lean`. Requires defining `ReachableContinuousState`.
   ~80 lines.
3. **Fairness axioms** (critical fix) — define `IsFairExecution`,
   rewrite axiom, update `liveness_theorem` and `lock_acquisition`
   signatures. ~100 lines.
4. **Paper-ambiguity report** — documentation-only, added to `TODO.md`
   or new `PaperAmbiguities.md`. ~40 lines.

## Critical files

| File | Change |
|------|--------|
| `VerifDemo/CellularFlows/ContinuousModel.lean` | Fix bridge axiom + add ReachableContinuousState; expand MCDiscreteSafe |
| `VerifDemo/CellularFlows/EuclideanModel.lean` | Mirror the bridge fix with real-valued version |
| `VerifDemo/CellularFlows/CellFlowsProofs.lean` | Define IsFairExecution; fix fair_execution_ranking_decreases; update liveness_theorem |
| `VerifDemo/CellularFlows/MultiColorProofs.lean` | Mirror fairness fix; update lock_acquisition |
| `VerifDemo/CellularFlows/Defs.lean` | Update correspondence table axiom inventory |
| `VerifDemo/CellularFlows/TODO.md` | Add paper-ambiguity report section |

## Reusable infrastructure

- `Reachable` (TransitionSystem.lean) — for discrete reachability hypothesis
- `Execution`, `IsRankingFunction`, `ranking_implies_eventually`
  (TransitionSystem.lean) — for reformulated liveness
- Existing per-invariant proofs (`lockMutex_invariant`,
  `signalRespectsLock_invariant`, `colorConsistent_invariant`,
  `noSignalCycle2_invariant`, `mcSignalValid_invariant`,
  `lockRequiresIntersection_invariant`) — to re-bundle in
  `mcDiscreteSafe_invariant`

## Verification

- `lake build` after each fix
- Zero `sorry`, zero new axioms (the axioms we have become better-scoped,
  not more numerous)
- Track axiom count via `grep -c "^axiom" VerifDemo/CellularFlows/*.lean`
  — should stay at 9 total (same axioms, tighter statements)
- Soundness test: after fix 1, try to construct a "bad" `ContinuousMCState`
  with coincident positions; confirm the old bridge is no longer invokable
  without discharging the new `ReachableContinuousState` hypothesis
- Soundness test: after fix 2, verify that stutter executions (where
  `IsFairExecution` is false) cannot be used to invoke
  `fair_execution_ranking_decreases`

## What we're NOT changing

- **Signal non-determinism in the transition**: current transition allows
  `signal = none` even when conditions for `some j` are met. This is
  safer than the paper's deterministic algorithm (a superset of paper
  behaviors), so it's conservative. Not touching.
- **argminDist tie-breaking**: current implementation breaks ties by
  list order instead of cell ID. Still deterministic; documented in
  paper-ambiguity report only.
- **No new Mathlib usage**: fixes stay in pure Lean 4 core where possible;
  `EuclideanModel.lean` continues to use Mathlib only for Euclidean space.
