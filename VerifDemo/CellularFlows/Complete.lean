/-
  Cellular Flows — Complete-Graph Tessellation
  ==============================================

  A `CellTopology` instance for the complete graph K_n on `n` cells:
  every pair of distinct cells is a neighbor. Distances are 0 (self)
  or 1 (any other cell).

  Purpose: demonstrate that the `CellTopology` abstraction in
  `Topology.lean` accommodates genuinely non-rectangular tessellations
  beyond the 1D line and 2D grid. K_n is the natural topology for a
  "fully meshed" environment — every cell is directly adjacent to
  every other — which is one limiting case of the convex-tessellation
  generality claimed in Section 1 (contribution A) of:

    T.T. Johnson and S. Mitra, "Safe and Stabilizing Distributed
    Multi-Path Cellular Flows," TCS 579 (2015) 9–32.

  Given any pair of distinct cells `i, t : Fin n`, the routing
  gradient is trivial — one hop suffices to reach the target. The
  triangle inequality and closer-neighbor existence both hold by
  easy case analysis because the distance is bounded by 1.
-/
import VerifDemo.CellularFlows.Topology

namespace CellularFlows.Complete

open CellularFlows

/-- Distance on the complete graph K_n: 0 if equal, 1 otherwise. -/
def completeDist {n : Nat} (i j : Fin n) : Nat :=
  if i = j then 0 else 1

/-- Neighbor predicate on K_n: any two distinct cells are neighbors. -/
def completeAreNeighbors {n : Nat} (i j : Fin n) : Prop := i ≠ j

instance {n : Nat} (i j : Fin n) : Decidable (completeAreNeighbors i j) :=
  inferInstanceAs (Decidable (i ≠ j))

/-- Neighbor list on K_n: every cell except `i` itself. -/
def completeNeighbors {n : Nat} (i : Fin n) : List (Fin n) :=
  (List.finRange n).filter (fun j => decide (j ≠ i))

/-- `j ∈ completeNeighbors i ↔ j ≠ i`. -/
theorem mem_completeNeighbors_iff {n : Nat} (i j : Fin n) :
    j ∈ completeNeighbors i ↔ j ≠ i := by
  unfold completeNeighbors
  constructor
  · intro h
    have := List.mem_filter.mp h
    have hdec := this.2
    simp at hdec
    exact hdec
  · intro h
    apply List.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · exact List.mem_finRange j
    · simp [h]

/-- List membership implies adjacency on K_n. -/
private theorem completeNeighbors_mem_areNeighbors {n : Nat} (i j : Fin n) :
    j ∈ completeNeighbors i → completeAreNeighbors i j := by
  intro h
  have hne : j ≠ i := (mem_completeNeighbors_iff i j).mp h
  intro hij
  exact hne hij.symm

/-- Adjacency implies list membership on K_n. -/
private theorem completeNeighbors_complete {n : Nat} (i j : Fin n) :
    completeAreNeighbors i j → j ∈ completeNeighbors i := by
  intro h
  apply (mem_completeNeighbors_iff i j).mpr
  intro hij
  exact h hij.symm

/-- Distance is symmetric. -/
private theorem completeDist_symm {n : Nat} (i j : Fin n) :
    completeDist i j = completeDist j i := by
  unfold completeDist
  by_cases h : i = j
  · simp [h]
  · have hsym : j ≠ i := fun hji => h hji.symm
    simp [h, hsym]

/-- Distance to self is zero. -/
private theorem completeDist_self {n : Nat} (i : Fin n) : completeDist i i = 0 := by
  unfold completeDist; simp

/-- Triangle inequality: since `completeDist ≤ 1`, `dist j t + 1 ≥ 1 ≥ dist i t`. -/
private theorem completeDist_triangle {n : Nat} (i j t : Fin n) :
    completeAreNeighbors i j → completeDist j t + 1 ≥ completeDist i t := by
  intro _
  unfold completeDist
  split <;> split <;> omega

/-- For any `i ≠ t` on K_n, the target itself is a neighbor and
    `dist t t + 1 = 0 + 1 = 1 = dist i t`. -/
private theorem completeDist_exists_closer {n : Nat} (i t : Fin n)
    (hne : i ≠ t) (_hpos : completeDist i t > 0) :
    ∃ j : Fin n, j ∈ completeNeighbors i ∧ completeDist j t + 1 = completeDist i t := by
  refine ⟨t, ?_, ?_⟩
  · -- t is a neighbor of i (since t ≠ i)
    apply (mem_completeNeighbors_iff i t).mpr
    intro h; exact hne h.symm
  · -- completeDist t t + 1 = 1 = completeDist i t
    unfold completeDist
    simp [hne]

/-- Canonical `CellTopology` instance for the complete graph on `Fin n`. -/
instance CellTopologyComplete (n : Nat) : CellTopology (Fin n) where
  decEq := inferInstance
  neighbors := completeNeighbors
  areNeighbors := completeAreNeighbors
  dist := completeDist
  decNeighbors _ _ := inferInstance
  neighbors_mem := completeNeighbors_mem_areNeighbors
  neighbors_complete := completeNeighbors_complete
  dist_symm := completeDist_symm
  dist_self := completeDist_self
  triangle := completeDist_triangle
  exists_closer i t hne hpos := completeDist_exists_closer i t hne hpos

/- ------------------------------------------------------------------- -/
/- Sanity checks                                                        -/
/- ------------------------------------------------------------------- -/

/-- Self-distance is 0. -/
example (n : Nat) (i : Fin n) : completeDist i i = 0 := by
  simp [completeDist]

/-- Any two distinct cells are at distance 1. -/
example (n : Nat) (i j : Fin n) (h : i ≠ j) : completeDist i j = 1 := by
  simp [completeDist, h]

end CellularFlows.Complete
