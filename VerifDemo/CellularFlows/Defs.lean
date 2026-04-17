/-
  Cellular Flows — Core Definitions
  ==================================

  This module defines the types and helper functions for formalizing the
  distributed cellular flows protocol from:

    T.T. Johnson and S. Mitra, "Safe and Stabilizing Distributed Multi-Path
    Cellular Flows," Theoretical Computer Science 579 (2015) 9–32.

  The system models a partitioned planar environment where cells coordinate
  via local signaling to route entities from sources to targets. We work
  with a 1D line of N cells (target at cell 0) as the base case; the 2D
  grid generalization (Grid.lean) follows the same pattern.

  KEY ABSTRACTION: the paper's continuous entity positions (in R²) are
  abstracted to discrete entity counts per cell. The discrete protocol
  invariants (signal exclusion, no signal cycles, routing correctness)
  are proved exactly; the bridge from discrete protocol correctness to
  continuous safety (Theorem 1) relies on geometric arguments about
  transfer/safety regions that we state as axioms referencing the paper.

  ══════════════════════════════════════════════════════════════════════
  PAPER-TO-LEAN CORRESPONDENCE TABLE
  ══════════════════════════════════════════════════════════════════════

  Paper Result             Lean Theorem                      File
  ─────────────────────────────────────────────────────────────────────
  SAFETY (Section 4.2)
    Invariant 1 (containment)   GapSafe (axiom, superseded)       CellFlowsProofs
                                safety_discrete (axiom-free)      DiscreteSafety
    Invariant 2 (disjoint)      entity_bounded_by_transfer        CellFlowsProofs
    Invariant 3 (single color)  invariant3_discrete               CellFlowsProofs
    Lemma 4 (gap preserved)     gapPreservedByStep (axiom)        CellFlowsProofs
                                (superseded by DiscreteSafety)
    Lemma 5 (no signal cycles)  noSignalCycle2_invariant           CellFlowsProofs
    ★ Theorem 1 (Safety)        safety_discrete (axiom-free)      DiscreteSafety

  ROUTING & STABILIZATION (Section 4.3)
    Lemma 6 (convergence, 1D)   route_convergence                 RouteProofs
    Lemma 6 (convergence, 2D)   mc_route_convergence              MultiColorProofs
    Corollary 7 (next conv, 1D) next_convergence                  RouteProofs
    Corollary 7 (next conv, 2D) mc_next_convergence               MultiColorProofs
    distLowerBound              distLowerBound_invariant           RouteProofs
    next_left_or_none           next_left_or_none                 RouteProofs
    noMutualNextHop             noMutualNextHop_invariant          CellFlowsProofs
    exists_closer_neighbor      (proved, was axiom)               MultiColorProofs
    Self-stabilization (1D)     route_self_stabilizes             Stabilization
                                route_next_self_stabilizes        Stabilization
    Self-stabilization (2D)     mc_route_self_stabilizes          Stabilization2D

  MULTI-COLOR (Section 4.4)
    Corollary 8 (path stable)   path_stabilization (proved theorem) MultiColorProofs
    Corollary 9 (pint stable)   pint_stabilization (proved theorem) MultiColorProofs
                                route_stable_implies_all_stable   MultiColorProofs
    Lemma 10 (lock gate)        signalRespectsLock_invariant       MultiColorProofs
    Lemma 11 (lock acquisition) lock_acquisition                  MultiColorProofs
    Lock mutual exclusion       lockMutex_invariant                MultiColorProofs
    Lock requires intersection  lockRequiresIntersection_invariant MultiColorProofs
    Per-color dist lower bound  mcDistLowerBound_invariant         MultiColorProofs

  LIVENESS (Section 4.5)
    Lemma 12 (fair signaling)   fair_execution_ranking_decreases  CellFlowsProofs
                                (axiom — fairness assumption)
    ★ Theorem 2 (Liveness)      liveness_theorem                  CellFlowsProofs

  FINITE INSTANCES (NuXMV)
    3-cell single-color line    Cellular3TS_inv1/2/3_proved        Cellular3Proofs
    2x2 grid with 2 colors      Cellular_mc_2x2TS_inv1..4_proved   CellularMC2x2Proofs
                                (lock mutex, dist targets, bounds)

  AXIOMS (5 total, 3 superseded; only 2 active, both fairness)
    ━━━ Active (2) ━━━
    fair_execution_ranking_decreases  (Assumptions 3-4, Lemma 12)  CellFlowsProofs
    lock_fairness_general             (Assumption 4, Lemma 11)     MultiColorProofs
    ━━━ Superseded (3) — kept for documentation ━━━
    GapSafe, gapSafe_init, gapPreservedByStep  (by safety_discrete) CellFlowsProofs

  ELIMINATED AXIOMS (during Phase 2 extensions)
    manhattan_neighbor_triangle → now a theorem (MultiColorProofs)
    neighbors2D_mem_areNeighbors → now a theorem (MultiColorProofs)
    exists_closer_neighbor      → now a theorem (MultiColorProofs, Phase A)
    path_stabilization          → now a theorem (MultiColorProofs, Phase C)
    pint_stabilization          → now a theorem (MultiColorProofs, Phase C)
  ══════════════════════════════════════════════════════════════════════
-/
import VerifDemo.TransitionSystem

namespace CellularFlows

/- ------------------------------------------------------------------- -/
/- Distance values with infinity.                                      -/

/-- Distance to target: either a finite natural number or infinity.
    Models the `dist` variable from the paper (Fig. 7, line 11).
    Failed cells have dist = inf; the target has dist = fin 0. -/
inductive DistVal where
  | fin : Nat → DistVal
  | inf : DistVal
  deriving DecidableEq, Repr

namespace DistVal

instance : Inhabited DistVal := ⟨.inf⟩

/-- Adding 1 to a distance: fin n ↦ fin (n+1), inf ↦ inf.
    Used in the Route subroutine: dist_i = 1 + min(dist_j). -/
def succ : DistVal → DistVal
  | .fin n => .fin (n + 1)
  | .inf   => .inf

/-- Minimum of two distance values. -/
def dmin : DistVal → DistVal → DistVal
  | .fin a, .fin b => .fin (Nat.min a b)
  | .fin a, .inf   => .fin a
  | .inf,  .fin b  => .fin b
  | .inf,  .inf    => .inf

/-- Less-than-or-equal for distance values. -/
def dle (a b : DistVal) : Bool :=
  match a, b with
  | .fin a, .fin b => a ≤ b
  | .fin _, .inf   => true
  | .inf,  .fin _  => false
  | .inf,  .inf    => true

end DistVal

/- ------------------------------------------------------------------- -/
/- 1D line topology.                                                   -/

/-- Left neighbor of cell i on a line of n cells (none if i = 0). -/
def leftNeighbor {n : Nat} (i : Fin n) : Option (Fin n) :=
  if h : i.val > 0 then some ⟨i.val - 1, by omega⟩ else none

/-- Right neighbor of cell i on a line of n cells (none if i = n-1). -/
def rightNeighbor {n : Nat} (i : Fin n) : Option (Fin n) :=
  if h : i.val + 1 < n then some ⟨i.val + 1, h⟩ else none

/-- All neighbors of cell i on a 1D line. -/
def neighbors1D {n : Nat} (i : Fin n) : List (Fin n) :=
  (leftNeighbor i).toList ++ (rightNeighbor i).toList

/-- Two cells are neighbors on a 1D line iff their indices differ by 1. -/
def areNeighbors {n : Nat} (i j : Fin n) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val

instance {n : Nat} (i j : Fin n) : Decidable (areNeighbors i j) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Non-failed neighbors: neighbors j with failed j = false. -/
def nonFailedNeighbors {n : Nat} (failed : Fin n → Bool) (i : Fin n) : List (Fin n) :=
  (neighbors1D i).filter (fun j => !failed j)

/-- Minimum distance among a list of cells, defaulting to inf. -/
def minDist {n : Nat} (dist : Fin n → DistVal) : List (Fin n) → DistVal
  | []      => .inf
  | [j]     => dist j
  | j :: js => DistVal.dmin (dist j) (minDist dist js)

/-- The neighbor achieving the minimum distance (first one, for tie-breaking).
    Returns none if the list is empty or all have dist = inf. -/
def argminDist {n : Nat} (dist : Fin n → DistVal) : List (Fin n) → Option (Fin n)
  | []      => none
  | [j]     => match dist j with
    | .inf   => none
    | .fin _ => some j
  | j :: js =>
    match argminDist dist js with
    | none   => match dist j with
      | .inf   => none
      | .fin _ => some j
    | some k =>
      if DistVal.dle (dist j) (dist k) then some j else some k

end CellularFlows
