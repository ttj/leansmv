/-
  Cellular Flows — Full Protocol (Route + Signal + Move) on 1D Line
  ==================================================================

  This module defines the full single-color, failure-free cellular flows
  transition system on a 1D line of N cells with target at cell 0,
  formalizing the protocol from:

    T.T. Johnson and S. Mitra, "Safe and Stabilizing Distributed Multi-Path
    Cellular Flows," Theoretical Computer Science 579 (2015) 9-32.

  Each synchronous round consists of three phases:

    1. ROUTE  — Bellman-Ford distance/next-hop update (same as routeFFTS).
    2. SIGNAL — Each cell grants move permission to at most one predecessor.
    3. MOVE   — Entities transfer along signaled edges; target absorbs.

  The Route-only transition system is in Route.lean; this module extends
  it with Signal and Move to capture the full entity-flow protocol.

  This is a definitions-only file. Proofs belong in a separate file.
-/
import VerifDemo.CellularFlows.Route

namespace CellularFlows

/-- State of the full cellular flows system on a 1D line of n cells.

    - `dist`     : estimated distance to target (updated by Route)
    - `next`     : next-hop neighbor toward target (updated by Route)
    - `signal`   : which predecessor has permission to move toward this cell
                   (at most one per cell, set by Signal phase)
    - `entities` : number of entities at each cell (updated by Move phase)

    No `failed` field: this is the failure-free specialization. -/
structure CellFlowState (n : Nat) where
  dist     : Fin n → DistVal
  next     : Fin n → Option (Fin n)
  signal   : Fin n → Option (Fin n)
  entities : Fin n → Nat

/-- Helper: compute entity count moved out of cell i.
    Cell i moves ALL its entities out when its next-hop ni has signaled i,
    i.e., signal(ni) = some i. Returns old entity count or 0. -/
def movedOut {n : Nat} (s : CellFlowState n) (signal' : Fin n → Option (Fin n))
    (next' : Fin n → Option (Fin n)) (i : Fin n) : Nat :=
  match next' i with
  | some ni => if signal' ni = some i then s.entities i else 0
  | none    => 0

/-- Helper: compute entity count moved into cell i.
    Cell i receives entities from whichever predecessor j it signaled,
    i.e., if signal'(i) = some j, then all of j's entities move in.
    Returns old entity count of j, or 0 if no signal. -/
def movedIn {n : Nat} (s : CellFlowState n) (signal' : Fin n → Option (Fin n))
    (i : Fin n) : Nat :=
  match signal' i with
  | some j => s.entities j
  | none   => 0

/-- The full cellular flows transition system for a failure-free 1D line
    of n cells with target at cell 0.

    Each transition encodes one synchronous round with three phases
    (Route, Signal, Move) flattened into a single step relation that
    constrains all post-state variables simultaneously.

    ROUTE PHASE (determines dist' and next'):
      Target cell 0 keeps dist = fin 0, next = none.
      Every other cell i sets dist' = 1 + min(dist_j for neighbors j)
      and next' = argmin neighbor by distance.

    SIGNAL PHASE (determines signal'):
      Each cell i nondeterministically sets signal' i to either none or
      some valid predecessor j satisfying:
        - j is a neighbor of i on the 1D line
        - j's post-route next-hop points to i (next' j = some i)
        - j has entities to move (entities j > 0, using pre-move count)

    MOVE PHASE (determines entities'):
      Target cell 0 absorbs all arriving entities (entities' 0 = moved-in).
      Each non-target cell i updates:
        entities' i = entities i - movedOut + movedIn
      where movedOut fires when next'(i)'s signal chose i,
      and movedIn fires when signal'(i) chose some predecessor j. -/
def cellFlowTS (n : Nat) : TransitionSystem (CellFlowState n) where
  init s :=
    -- Target: distance 0, no next-hop
    (∀ i : Fin n, i.val = 0 → s.dist i = .fin 0) ∧
    -- Non-target: distance infinity
    (∀ i : Fin n, i.val ≠ 0 → s.dist i = .inf) ∧
    -- All next-hops start as none
    (∀ i : Fin n, s.next i = none) ∧
    -- All signals start as none
    (∀ i : Fin n, s.signal i = none) ∧
    -- Target starts with no entities (entities at non-target cells are arbitrary)
    (∀ i : Fin n, i.val = 0 → s.entities i = 0)
  next s s' :=
    -- === Route phase (determines dist' and next') ===
    -- Target cell: dist stays 0, next stays none
    (∀ i : Fin n, i.val = 0 →
      s'.dist i = .fin 0 ∧ s'.next i = none) ∧
    -- Non-target cells: Bellman-Ford update over 1D neighbors
    (∀ i : Fin n, i.val ≠ 0 →
      s'.dist i = (minDist s.dist (neighbors1D i)).succ ∧
      s'.next i = argminDist s.dist (neighbors1D i)) ∧
    -- === Signal phase (determines signal') ===
    -- Each cell either signals nobody or signals exactly one valid predecessor
    (∀ i : Fin n,
      s'.signal i = none ∨
      (∃ j : Fin n, s'.signal i = some j ∧
        areNeighbors i j ∧
        s'.next j = some i ∧
        s.entities j > 0)) ∧
    -- === Move phase (determines entities') ===
    -- Target absorbs: new count is only what moved in (entities consumed)
    (∀ i : Fin n, i.val = 0 →
      s'.entities i = movedIn s s'.signal i) ∧
    -- Non-target: entities updated by signal-based transfers
    (∀ i : Fin n, i.val ≠ 0 →
      s'.entities i = s.entities i - movedOut s s'.signal s'.next i + movedIn s s'.signal i)

/- ------------------------------------------------------------------- -/
/- Projection: the Route sub-state, for reusing Route-only invariants. -/

/-- Extract the Route-relevant sub-state from a full CellFlowState.
    Useful for lifting Route-only invariants to the full system. -/
def CellFlowState.toRouteState {n : Nat} (s : CellFlowState n) : RouteState n where
  dist   := s.dist
  next   := s.next
  failed := fun _ => false

/- ------------------------------------------------------------------- -/
/- Safety properties.                                                  -/

/-- Signal validity: every non-none signal points to a valid predecessor.
    This is structurally enforced by the transition relation, but stated
    here as a named property for use in proofs. -/
def signalValid {n : Nat} (s : CellFlowState n) : Prop :=
  ∀ i j : Fin n, s.signal i = some j →
    areNeighbors i j ∧ s.next j = some i

/-- Total entity count across all cells, computed by folding over Fin n.
    Useful for stating conservation properties. -/
def totalEntities {n : Nat} (s : CellFlowState n) : Nat :=
  Fin.foldl n (fun acc i => acc + s.entities i) 0

/-- No entity duplication: after a Move step, no entity is counted at
    both its source and destination. This follows from the protocol's
    signal exclusivity (each cell signals at most one predecessor). -/
def noSignalConflict {n : Nat} (s : CellFlowState n) : Prop :=
  ∀ i j₁ j₂ : Fin n, s.signal i = some j₁ → s.signal i = some j₂ → j₁ = j₂

end CellularFlows
