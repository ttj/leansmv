/-
  Cellular Flows — Multi-Color Protocol (Sections 3.2-3.3, TCS 2015)
  ====================================================================

  This module defines a multi-color cellular flows transition system on
  a 1D line of n cells with nc colors. Each color has its own target cell,
  and entities of each color route independently toward their respective
  targets using Bellman-Ford distance computation.

  The key addition over the single-color protocol is the Lock subroutine:
  at path intersections (where routes of different colors cross), a mutual
  exclusion lock ensures that at most one color can move entities through
  at a time. Signals are gated by lock ownership at intersections.

  Paper reference:
    T.T. Johnson and S. Mitra, "Safe and Stabilizing Distributed Multi-Path
    Cellular Flows," Theoretical Computer Science 579 (2015) 9-32.
    Sections 3.2-3.3.

  This is a definitions-only file. Proofs belong in MultiColorProofs.lean.
-/
import VerifDemo.CellularFlows.Defs

namespace CellularFlows

/-- State of the multi-color cellular flows system.
    n = number of cells (1D line), nc = number of colors.
    Each color has its own source and target cell. -/
structure MCState (n nc : Nat) where
  /-- Per-color routing distance: dist[c][i] = distance from cell i to target of color c -/
  dist    : Fin nc → Fin n → DistVal
  /-- Per-color next-hop: next[c][i] = next-hop toward target of color c -/
  next    : Fin nc → Fin n → Option (Fin n)
  /-- Entity count at each cell -/
  entities : Fin n → Nat
  /-- Entity color at each cell (none if empty) -/
  color    : Fin n → Option (Fin nc)
  /-- Signal: which predecessor has permission (one per cell, NOT per color) -/
  signal   : Fin n → Option (Fin n)
  /-- Lock for mutual exclusion at path intersections (per color, per cell) -/
  lock     : Fin nc → Fin n → Bool
  /-- Whether cell has a path intersection for color c -/
  hasIntersection : Fin nc → Fin n → Bool

/-- The multi-color cellular flows transition system.

    Parameters:
    - n  : number of cells on the 1D line
    - nc : number of colors
    - targets : maps each color to its target cell

    Each transition encodes one synchronous round with phases:
    1. ROUTE  -- Per-color Bellman-Ford distance/next-hop update
    2. LOCK   -- Mutual exclusion at path intersections
    3. SIGNAL -- Permission granting, gated by locks
    4. MOVE   -- Entity transfer along signaled edges -/
def multiColorTS (n nc : Nat) (targets : Fin nc → Fin n) :
    TransitionSystem (MCState n nc) where
  init s :=
    -- Per-color routing: target of color c has dist 0
    (∀ c : Fin nc, ∀ i : Fin n, i = targets c → s.dist c i = .fin 0) ∧
    -- Per-color routing: non-target cells have dist inf
    (∀ c : Fin nc, ∀ i : Fin n, i ≠ targets c → s.dist c i = .inf) ∧
    -- All next-hops start as none
    (∀ c : Fin nc, ∀ i : Fin n, s.next c i = none) ∧
    -- All signals start as none
    (∀ i : Fin n, s.signal i = none) ∧
    -- All locks start as false
    (∀ c : Fin nc, ∀ i : Fin n, s.lock c i = false) ∧
    -- No intersections initially
    (∀ c : Fin nc, ∀ i : Fin n, s.hasIntersection c i = false) ∧
    -- Empty cells have no color
    (∀ i : Fin n, s.entities i = 0 → s.color i = none)
  next s s' :=
    -- === Route phase (per color, independent Bellman-Ford) ===
    -- Target cells: dist stays 0, next stays none
    (∀ c : Fin nc, ∀ i : Fin n, i = targets c →
      s'.dist c i = .fin 0 ∧ s'.next c i = none) ∧
    -- Non-target cells: Bellman-Ford update
    (∀ c : Fin nc, ∀ i : Fin n, i ≠ targets c →
      s'.dist c i = (minDist (s.dist c) (neighbors1D i)).succ ∧
      s'.next c i = argminDist (s.dist c) (neighbors1D i)) ∧
    -- === Lock phase (mutual exclusion on intersections) ===
    -- A color can hold lock at cell i only if it has a path intersection there
    (∀ c : Fin nc, ∀ i : Fin n, s'.lock c i = true →
      s'.hasIntersection c i = true) ∧
    -- At most one color holds lock at any cell
    (∀ i : Fin n, ∀ c1 c2 : Fin nc,
      s'.lock c1 i = true → s'.lock c2 i = true → c1 = c2) ∧
    -- === Signal phase (gated by lock) ===
    -- Each cell either signals nobody or signals exactly one valid predecessor.
    -- The color c referenced here is associated with the signal: it is the
    -- color that the sender j is routing, and the lock condition is checked
    -- for this color c at the receiving cell i.
    (∀ i : Fin n,
      s'.signal i = none ∨
      (∃ j : Fin n, ∃ c : Fin nc, s'.signal i = some j ∧
        areNeighbors i j ∧
        s.entities j > 0 ∧
        s'.next c j = some i ∧
        (s'.hasIntersection c i = false ∨ s'.lock c i = true))) ∧
    -- === Move phase ===
    -- Target cells absorb entities
    (∀ c : Fin nc, ∀ i : Fin n, i = targets c →
      s'.entities i = 0) ∧
    -- Non-target cells: simplified entity accounting (frame)
    (∀ i : Fin n, (∀ c : Fin nc, i ≠ targets c) →
      True) ∧
    -- Color tracking: empty cells have no color
    (∀ i : Fin n, s'.entities i = 0 → s'.color i = none)

end CellularFlows
