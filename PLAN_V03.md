# PLAN_V03 — Remaining Work (Post-Audit)

## Context

After the Phase 2 extensions (PLAN_V02.md) and the soundness-fix commit
`07ea70d`, the cellular flows formalization is **sound and substantially
complete**: 6,040 lines, 200+ theorems, zero `sorry`, 13 axioms (all
well-scoped). Both main paper theorems are proved. Two independent audits
found no remaining soundness issues and no paper bugs.

This plan documents the remaining **optional** extensions, organized by
priority. None are blocking; the formalization is publication-ready as-is.

## Status snapshot

| Aspect | Status |
|---|---|
| Soundness | ✅ Verified by two audit passes |
| Paper coverage (TCS 2015) | ✅ All theorems, lemmas, corollaries |
| 1D + 2D parametric | ✅ Both |
| Continuous Theorem 1 (paper form) | ✅ Both Nat-metric and Mathlib ℝ² |
| Self-stabilization from arbitrary state | ✅ 1D and 2D |
| Fairness axioms properly scoped | ✅ `IsFairExecution`, `IsLockFair` |
| Continuous bridges properly scoped | ✅ `ContinuousReachable` + opaque `ValidContinuousPlacement` |
| Finite NuXMV instances | ✅ 3-cell single-color + 2x2 multi-color |
| Parametric topology typeclass | ✅ 1D line, 2D grid, complete graph instances |

## Remaining gaps (all optional, non-critical)

These were identified by the second-pass audit. None affect soundness or
core paper coverage; each is a refinement or generalization.

### Gap 1 — Signal subroutine token round-robin (LOW priority)
**Current**: signal assignment is non-deterministic in the transition relation;
`token_i` (paper Fig. 7) is not modeled explicitly.
**What's abstracted**: the paper's explicit round-robin rotation of `token`
through `NEPrev`.
**Effect**: our transition is a superset of paper behaviors — conservative
for safety, requires `IsFairExecution` hypothesis for liveness.
**To close**: add an explicit `token : CellId2D n → Option (CellId2D n)` field
to `MCState`, add the round-robin update rule to the transition, then prove
that round-robin scheduling implies `IsFairExecution`.
**Effort**: Medium (~300 lines). Would eliminate the fairness axiom in favor
of a provable theorem.

### Gap 2 — Explicit Move subroutine position updates (LOW priority)
**Current**: entity counts abstract over positions; continuous positions
live in a separate `ContinuousMCState` / `ContinuousMCStateReal` bundle
with an opaque `ValidContinuousPlacement` hypothesis.
**What's abstracted**: the paper's Fig. 6 Move subroutine updates entity
positions explicitly (`entity.pos += velocity * dt`).
**Effect**: `ValidContinuousPlacement` papers over what a valid position
update looks like.
**To close**: formalize a continuous transition system over
`ContinuousMCStateReal`, prove that its reachability entails valid
placements. Would eliminate the `ValidContinuousPlacement*` axioms.
**Effort**: High (~600 lines, significant Mathlib engagement for velocity
field / convex polygon membership).

### Gap 3 — Explicit `fail(i)` transitions (LOW priority)
**Current**: `MCState` has a `failed : CellId2D n → Bool` field but the
transition relation does not include a `fail(i)` action. Failures are
handled by initializing with some cells failed.
**What's abstracted**: the paper's `fail(i)` transition that sets
`failed[i] := true` mid-execution.
**Effect**: self-stabilization proofs (`mc_route_self_stabilizes`) handle
the "post-failure" suffix correctly, but the moment of failure itself
is not modeled as a transition.
**To close**: add a `fail(i)` action to the transition relation and prove
that failure-free suffixes of mixed executions satisfy existing stabilization
theorems.
**Effort**: Medium (~200 lines).

### Gap 4 — Exercise `CellTopology` on more tessellations (LOW priority, cosmetic)
**Current**: `Topology.lean` defines `CellTopology`; instances exist for
1D line, 2D grid, and complete graph K_n.
**What's missing**: triangular, hexagonal, or snub tilings (the paper's
Fig. 3 examples). Also: generic routing/safety proofs parameterized by
`CellTopology` rather than concrete 1D/2D.
**To close**: add `Hex.lean`, `Triangular.lean`, etc.; re-prove
`mc_route_convergence` generically.
**Effort**: Medium (~400 lines per tessellation; generic proofs add ~200
more). Demonstrates paper's generality claim but doesn't add new theorems.

### Gap 5 — Explicit token state for lock fairness (LOW priority)
**Same pattern as Gap 1**, but for `IsLockFair` / `lock_fairness_general`.
Paper Lemma 11 relies on token rotation through colors requesting a lock.
**To close**: model token-color rotation, prove round-robin implies
`IsLockFair`.
**Effort**: Medium (~200 lines).

### Gap 6 — `mcSignalValid` distance monotonicity as explicit theorem (VERY LOW priority, stylistic)
**Current**: signal-preserves-or-decreases-distance is implicit in the
Bellman-Ford invariant.
**To close**: state as a named theorem for documentation.
**Effort**: Low (~20 lines).

## Paper ambiguities (documentation only — DO NOT change paper)

Already documented in `VerifDemo/CellularFlows/TODO.md` under "Paper
ambiguities surfaced by formalization". Not actionable in Lean — these are
feedback for a possible revised paper.

1. `argminDist` tie-breaking — paper uses lex `(dist, ID)`; we use list order.
   Both deterministic; paper should note any deterministic rule suffices.
2. Corollary 7 bound wording — paper states `2Δ(x)`; our 2D proof uses
   Manhattan directly. Equivalent on the grid; paper could spell out the
   grid specialization.
3. Assumption 2 scope — declared in §2.5 but not invoked by name in the
   Theorem 1 proof; paper could cite it explicitly where used.
4. Assumption 4 (fairness) wording — informal ("fairly scheduled");
   formalization required a precise infinitely-often / within-finitely-many
   formulation.

## Priority order (if continuing)

Best ratio of effort to gained trust / elimination of axioms:

1. **Gap 1 + Gap 5 (token rotation model)** — eliminates both fairness
   axioms (`fair_execution_ranking_decreases`, `lock_fairness_general`) in
   favor of provable theorems. Turns active axiom count 10 → 8.
   Net effort: ~500 lines combined.
2. **Gap 3 (`fail(i)` transition)** — completes the failure model to match
   the paper exactly. No axiom reduction but tighter correspondence.
3. **Gap 4 (more tessellations)** — showcases the `CellTopology`
   abstraction's generality; useful for teaching.
4. **Gap 2 (continuous Move subroutine)** — eliminates 2 continuous-bridge
   axioms but requires substantial Mathlib engagement. Best undertaken
   by a Mathlib-experienced contributor.

## Non-work items

- **Paper corrections**: none — the paper is sound.
- **Additional soundness fixes**: none — both audits verified the
  formalization is currently sound.
- **Conference paper (ICDCS 2010)**: has some different content but all
  theorems there appear in the TCS journal version we formalized.
- **Simulation integration**: the paper references a MATLAB simulator
  (https://github.com/verivital/cell_flows). Bringing simulation results
  into Lean is outside the verification scope.

## How to use this plan

- **If the formalization is "done"**: ship as-is. All paper results are
  covered with zero `sorry`; axioms are well-scoped.
- **If continuing for publication/teaching**: pick items in priority order.
  Each gap is independent.
- **If specifically aiming to eliminate axioms**: Gap 1 + Gap 5 (token
  rotation) gives the best return.

Plan file maintenance: when a gap is closed, update both this file and
`VerifDemo/CellularFlows/TODO.md` to reflect the new state. When a new
issue surfaces, add it here with the same severity/effort/scope labels.
