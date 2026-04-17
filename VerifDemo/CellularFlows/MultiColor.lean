/-
  Cellular Flows — Multi-Color Protocol on 2D Grid (Sections 3.2-4.4, TCS 2015)
  ===============================================================================

  This module defines a multi-color cellular flows transition system on an
  N×N 2D grid with nc colors. Each color has its own target cell, and entities
  of each color route independently toward their respective targets using
  Bellman-Ford distance computation on the 2D grid topology.

  The key additions over the single-color protocol are:
  - Path tracking: gossip-based aggregation of entity-graph paths per color
  - Path intersection detection: identifies cells where paths of different
    colors cross (pint variable)
  - Lock colors (needsLock): cells that need mutual exclusion due to
    intersecting paths
  - Lock subroutine: at path intersections, a mutual exclusion lock ensures
    that at most one color can move entities through at a time
  - Signals are gated by lock ownership at intersection cells

  Paper reference:
    T.T. Johnson and S. Mitra, "Safe and Stabilizing Distributed Multi-Path
    Cellular Flows," Theoretical Computer Science 579 (2015) 9-32.
    Sections 3.2-4.4, Figures 7-11, Lemmas 10-11.

  This is a definitions-only file. Proofs belong in MultiColorProofs.lean.
-/
import VerifDemo.CellularFlows.Grid

set_option autoImplicit false

namespace CellularFlows

/-- State of the multi-color cellular flows system on an N×N grid.
    n = grid dimension (N×N cells), nc = number of colors.

    Paper ref: Fig. 7 (Cell_i specification, lines 1-15). -/
structure MCState (n nc : Nat) where
  /-- Per-color routing distance: dist[c][i] = distance from cell i to
      target of color c. Updated by Route subroutine (Fig. 8). -/
  dist      : Fin nc → CellId2D n → DistVal
  /-- Per-color next-hop: next[c][i] = next-hop toward target of color c.
      Updated by Route subroutine (Fig. 8). -/
  next      : Fin nc → CellId2D n → Option (CellId2D n)
  /-- Entity count at each cell. -/
  entities  : CellId2D n → Nat
  /-- Entity color at each cell (none if empty). -/
  color     : CellId2D n → Option (Fin nc)
  /-- Signal: which predecessor has permission to move toward this cell
      (one per cell, shared across colors — Fig. 10). -/
  signal    : CellId2D n → Option (CellId2D n)
  /-- Path tracking for intersection detection (Fig. 9, lines 1-7).
      path[c][i] = list of cells on the entity graph from sources of
      color c through cell i toward target of color c. -/
  path      : Fin nc → CellId2D n → List (CellId2D n)
  /-- Path intersection: pint[c][i] = true iff path of color c intersects
      paths of some other color d at cell i. -/
  pint      : Fin nc → CellId2D n → Bool
  /-- Lock colors: needsLock[c][i] = true iff cell i requires a lock
      for color c due to path intersection. Derived from pint. -/
  needsLock : Fin nc → CellId2D n → Bool
  /-- Lock state for mutual exclusion at path intersections
      (Fig. 9, lines 8-17). lock[c][i] = true iff color c holds the
      lock at cell i. -/
  lock      : Fin nc → CellId2D n → Bool
  /-- Failure tracking: whether each cell has failed. -/
  failed    : CellId2D n → Bool

/-- The multi-color cellular flows transition system on an N×N 2D grid.

    Parameters:
    - n  : grid dimension (N×N cells)
    - nc : number of colors
    - targets : maps each color to its target cell on the grid

    Each transition encodes one synchronous round with five phases:
    1. ROUTE  — Per-color Bellman-Ford on 2D grid (Fig. 8)
    2. PATH   — Gossip-based path aggregation (Fig. 9, lines 1-7)
    3. LOCK   — Mutual exclusion at intersections (Fig. 9, lines 8-17)
    4. SIGNAL — Permission granting, gated by locks (Fig. 10)
    5. MOVE   — Entity transfer along signaled edges (Fig. 11) -/
def multiColorTS (n nc : Nat) (targets : Fin nc → CellId2D n) :
    TransitionSystem (MCState n nc) where
  init s :=
    -- Per-color routing: target of color c has dist 0
    (∀ c : Fin nc, ∀ i : CellId2D n, i = targets c → s.dist c i = .fin 0) ∧
    -- Per-color routing: non-target cells have dist inf
    (∀ c : Fin nc, ∀ i : CellId2D n, i ≠ targets c → s.dist c i = .inf) ∧
    -- All next-hops start as none
    (∀ c : Fin nc, ∀ i : CellId2D n, s.next c i = none) ∧
    -- All signals start as none
    (∀ i : CellId2D n, s.signal i = none) ∧
    -- All locks start as false
    (∀ c : Fin nc, ∀ i : CellId2D n, s.lock c i = false) ∧
    -- No path intersections initially
    (∀ c : Fin nc, ∀ i : CellId2D n, s.pint c i = false) ∧
    -- No lock needs initially
    (∀ c : Fin nc, ∀ i : CellId2D n, s.needsLock c i = false) ∧
    -- Paths are empty initially
    (∀ c : Fin nc, ∀ i : CellId2D n, s.path c i = []) ∧
    -- Empty cells have no color
    (∀ i : CellId2D n, s.entities i = 0 → s.color i = none) ∧
    -- No failures initially
    (∀ i : CellId2D n, s.failed i = false)
  next s s' :=
    -- === 1. ROUTE phase (per color, independent Bellman-Ford on 2D grid, Fig. 8) ===
    -- Target cells: dist stays 0, next stays none
    (∀ c : Fin nc, ∀ i : CellId2D n, i = targets c →
      s'.dist c i = .fin 0 ∧ s'.next c i = none) ∧
    -- Failed cells: dist becomes inf, next becomes none
    (∀ c : Fin nc, ∀ i : CellId2D n, s.failed i = true →
      s'.dist c i = .inf ∧ s'.next c i = none) ∧
    -- Non-target, non-failed cells: Bellman-Ford update over 2D neighbors
    (∀ c : Fin nc, ∀ i : CellId2D n, i ≠ targets c → s.failed i = false →
      let nbrs := nonFailedNeighbors2D s.failed i
      s'.dist c i = (minDist2D (s.dist c) nbrs).succ ∧
      s'.next c i = argminDist2D (s.dist c) nbrs) ∧
    -- === 2. PATH phase (gossip-based, Fig. 9 lines 1-7) ===
    -- pint[c][i] = true only if path of color c and some other color d
    -- both include cell i (simplified structural constraint)
    (∀ c : Fin nc, ∀ i : CellId2D n, s'.pint c i = true →
      ∃ d : Fin nc, d ≠ c ∧
        i ∈ s'.path c i ∧ i ∈ s'.path d i) ∧
    -- needsLock[c][i] = true only if pint[c][i] = true
    (∀ c : Fin nc, ∀ i : CellId2D n, s'.needsLock c i = true →
      s'.pint c i = true) ∧
    -- === 3. LOCK phase (mutual exclusion, Fig. 9 lines 8-17) ===
    -- Lock only granted at cells that need locks
    (∀ c : Fin nc, ∀ i : CellId2D n, s'.lock c i = true →
      s'.needsLock c i = true) ∧
    -- At most one color holds lock at any cell
    (∀ i : CellId2D n, ∀ c1 c2 : Fin nc,
      s'.lock c1 i = true → s'.lock c2 i = true → c1 = c2) ∧
    -- === 4. SIGNAL phase (color-aware, gated by lock, Fig. 10) ===
    (∀ i : CellId2D n,
      s'.signal i = none ∨
      (∃ j : CellId2D n, ∃ c : Fin nc,
        s'.signal i = some j ∧
        areNeighbors2D i j ∧
        s.entities j > 0 ∧
        s'.color j = some c ∧
        s'.next c j = some i ∧
        -- Lock gate: if intersection exists for color c at cell i,
        -- lock must be held (Fig. 10, line 5)
        (s'.needsLock c i = false ∨ s'.lock c i = true) ∧
        -- Color compatibility: i is empty or has same color
        (s'.entities i = 0 ∨ s'.color i = some c))) ∧
    -- === 5. MOVE phase (Fig. 11) ===
    -- Target cells absorb entities
    (∀ c : Fin nc, ∀ i : CellId2D n, i = targets c →
      s'.entities i = 0) ∧
    -- Failed cells don't change entities
    (∀ i : CellId2D n, s.failed i = true →
      s'.entities i = s.entities i) ∧
    -- Non-target, non-failed entity accounting:
    -- If no signal points to i, entities can only decrease (move out)
    (∀ i : CellId2D n, (∀ c : Fin nc, i ≠ targets c) → s.failed i = false →
      (s'.signal i = none → s'.entities i ≤ s.entities i) ∧
      True) ∧
    -- Color tracking: empty cells have no color
    (∀ i : CellId2D n, s'.entities i = 0 → s'.color i = none) ∧
    -- Color of arriving entities matches source color
    (∀ i j : CellId2D n, s'.signal i = some j → s'.entities i > 0 →
      s'.color i = s.color j) ∧
    -- Failure frame: failures don't change
    (∀ i : CellId2D n, s'.failed i = s.failed i)

end CellularFlows
