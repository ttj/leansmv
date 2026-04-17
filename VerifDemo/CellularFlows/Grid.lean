/-
  Cellular Flows — 2D Grid Topology
  ===================================

  Defines the 2D grid topology for the multi-color extension of the
  cellular flows protocol. Generalizes the 1D line topology in Defs.lean
  to an N×N grid with 4-connected neighbors.

  Paper reference: Section 2.1 (Cells and partitioning), Section 2.2
  (Neighbors and communications).
-/
import VerifDemo.CellularFlows.Defs

namespace CellularFlows

/-- Cell identifier on an N×N 2D grid: a pair of row and column indices. -/
abbrev CellId2D (n : Nat) := Fin n × Fin n

/-- Up neighbor (row - 1) of cell (r, c), if it exists. -/
def upNeighbor {n : Nat} (i : CellId2D n) : Option (CellId2D n) :=
  if h : i.1.val > 0 then some (⟨i.1.val - 1, by omega⟩, i.2) else none

/-- Down neighbor (row + 1) of cell (r, c), if it exists. -/
def downNeighbor {n : Nat} (i : CellId2D n) : Option (CellId2D n) :=
  if h : i.1.val + 1 < n then some (⟨i.1.val + 1, h⟩, i.2) else none

/-- Left neighbor (col - 1) of cell (r, c), if it exists. -/
def leftNeighbor2D {n : Nat} (i : CellId2D n) : Option (CellId2D n) :=
  if h : i.2.val > 0 then some (i.1, ⟨i.2.val - 1, by omega⟩) else none

/-- Right neighbor (col + 1) of cell (r, c), if it exists. -/
def rightNeighbor2D {n : Nat} (i : CellId2D n) : Option (CellId2D n) :=
  if h : i.2.val + 1 < n then some (i.1, ⟨i.2.val + 1, h⟩) else none

/-- All 4-connected neighbors of cell i on an N×N grid. -/
def neighbors2D {n : Nat} (i : CellId2D n) : List (CellId2D n) :=
  (upNeighbor i).toList ++ (downNeighbor i).toList ++
  (leftNeighbor2D i).toList ++ (rightNeighbor2D i).toList

/-- Two cells are neighbors on a 2D grid iff they share a side
    (differ by 1 in exactly one coordinate). -/
def areNeighbors2D {n : Nat} (i j : CellId2D n) : Prop :=
  (i.1 = j.1 ∧ (i.2.val + 1 = j.2.val ∨ j.2.val + 1 = i.2.val)) ∨
  (i.2 = j.2 ∧ (i.1.val + 1 = j.1.val ∨ j.1.val + 1 = i.1.val))

instance {n : Nat} (i j : CellId2D n) : Decidable (areNeighbors2D i j) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Manhattan distance between two cells on the grid.
    Paper uses this as the shortest-path distance metric. -/
def manhattan {n : Nat} (a b : CellId2D n) : Nat :=
  (if a.1.val ≤ b.1.val then b.1.val - a.1.val else a.1.val - b.1.val) +
  (if a.2.val ≤ b.2.val then b.2.val - a.2.val else a.2.val - b.2.val)

/-- Non-failed 2D neighbors. -/
def nonFailedNeighbors2D {n : Nat} (failed : CellId2D n → Bool)
    (i : CellId2D n) : List (CellId2D n) :=
  (neighbors2D i).filter (fun j => !failed j)

/-- Minimum distance among a list of 2D cells, defaulting to inf. -/
def minDist2D {n : Nat} (dist : CellId2D n → DistVal) : List (CellId2D n) → DistVal
  | []      => .inf
  | [j]     => dist j
  | j :: js => DistVal.dmin (dist j) (minDist2D dist js)

/-- Argmin over 2D neighbor list (first/leftmost on ties). -/
def argminDist2D {n : Nat} (dist : CellId2D n → DistVal) :
    List (CellId2D n) → Option (CellId2D n)
  | []      => none
  | [j]     => match dist j with
    | .inf   => none
    | .fin _ => some j
  | j :: js =>
    match argminDist2D dist js with
    | none   => match dist j with
      | .inf   => none
      | .fin _ => some j
    | some k =>
      if DistVal.dle (dist j) (dist k) then some j else some k

end CellularFlows
