/-
  Cellular Flows — Parametric Cell Topology
  ===========================================

  Abstracts over concrete neighbor topologies (1D line, 2D grid, hexagonal,
  triangular, complete graph, etc.) so the cellular flows protocol can be
  reasoned about on arbitrary convex tessellations.

  Paper reference: T.T. Johnson and S. Mitra, "Safe and Stabilizing
  Distributed Multi-Path Cellular Flows," Theoretical Computer Science
  579 (2015) 9–32. Section 1, contribution A, claims generality of the
  protocol to "arbitrary convex tessellations" — triangular, hexagonal,
  square, etc. Section 2.1 defines cells as arbitrary convex polygons
  partitioning a planar environment, with the neighbor relation defined
  by "sharing a common side".

  This module captures, via a typeclass, the minimum structure the routing
  correctness proofs actually rely on:

    - A cell-identifier type α with decidable equality
    - A neighbor function returning the list of adjacent cells
    - A decidable symmetric neighbor predicate
    - A Nat-valued shortest-path distance function
    - Triangle inequality: moving to a neighbor changes the distance
      to any target by at most 1
    - Closer-neighbor existence: every non-target cell has a neighbor
      strictly closer to the target (i.e. the shortest path is realised)

  Given any instance of `CellTopology α` one can in principle replay
  the 2D-grid routing proofs (`mc_route_convergence` etc.) parametrically.
  This file only sets up the abstraction and concrete instances — the
  existing 1D and 2D proofs remain the load-bearing ones; this is a
  structural extension demonstrating the generality the paper claims.

  Instances provided in this file:
    * `CellTopology1D n` — 1D line of n cells (matches `neighbors1D`)
    * `CellTopology2D n` — N×N grid (matches `neighbors2D`, `manhattan`)
  Instances in companion files:
    * `CellTopologyComplete n` — Complete graph on n cells (Complete.lean)
-/
import VerifDemo.CellularFlows.Defs
import VerifDemo.CellularFlows.Grid

namespace CellularFlows

/- ------------------------------------------------------------------- -/
/- The CellTopology typeclass                                          -/
/- ------------------------------------------------------------------- -/

/-- Abstract cell topology for generic tessellations.

    Each instance provides concrete neighbor/distance functions along
    with the structural properties needed for routing correctness. The
    fields correspond directly to the hypotheses used in proofs such
    as `mc_route_convergence` (MultiColorProofs.lean).

    Because `autoImplicit = false` we declare the type parameter
    explicitly. -/
class CellTopology (α : Type) where
  /-- Decidable equality on cells. -/
  decEq : DecidableEq α
  /-- Neighbors of a cell — cells sharing a side (or edge). -/
  neighbors : α → List α
  /-- Neighbor predicate (symmetric "shares a side" relation). -/
  areNeighbors : α → α → Prop
  /-- Graph distance between cells (number of hops on the neighbor graph). -/
  dist : α → α → Nat
  /-- Decidability of the neighbor predicate (needed for enumeration). -/
  decNeighbors : ∀ i j : α, Decidable (areNeighbors i j)
  /-- Membership in the neighbor list implies adjacency. -/
  neighbors_mem : ∀ i j : α, j ∈ neighbors i → areNeighbors i j
  /-- Adjacency implies membership in the neighbor list. -/
  neighbors_complete : ∀ i j : α, areNeighbors i j → j ∈ neighbors i
  /-- Distance is symmetric: `dist i j = dist j i`. -/
  dist_symm : ∀ i j : α, dist i j = dist j i
  /-- Distance from a cell to itself is zero. -/
  dist_self : ∀ i : α, dist i i = 0
  /-- Triangle inequality via neighbors: moving to a neighbor changes
      distance to any target by at most 1. -/
  triangle : ∀ i j t : α, areNeighbors i j → dist j t + 1 ≥ dist i t
  /-- Every non-target cell has a neighbor strictly closer to the target
      (shortest path is realised). -/
  exists_closer : ∀ i t : α, i ≠ t → dist i t > 0 →
      ∃ j : α, j ∈ neighbors i ∧ dist j t + 1 = dist i t

-- Note: `decEq` is intentionally a typeclass field rather than a direct
-- `instance attribute` — Lean warns if we try to mark it as an instance
-- because it is not `@[reducible]`. Users can obtain decidable equality
-- for a specific topology via `CellTopology.decEq` or the underlying
-- `inferInstance` on the concrete `α`.

/- ------------------------------------------------------------------- -/
/- Generic min-distance and argmin helpers                              -/
/- ------------------------------------------------------------------- -/

namespace CellTopology

/-- Generic minimum-distance helper parametrized on a `CellTopology`.
    Uses the abstract `α` so the existing 1D `minDist` and 2D `minDist2D`
    are recovered by specialisation. -/
def tminDist {α : Type} (d : α → DistVal) : List α → DistVal
  | []      => .inf
  | [j]     => d j
  | j :: js => DistVal.dmin (d j) (tminDist d js)

/-- Generic argmin over a list of cells: the (first) element achieving
    the minimum finite distance, or `none` if every cell has `dist = inf`. -/
def targminDist {α : Type} (d : α → DistVal) : List α → Option α
  | []      => none
  | [j]     => match d j with
    | .inf   => none
    | .fin _ => some j
  | j :: js =>
    match targminDist d js with
    | none   => match d j with
      | .inf   => none
      | .fin _ => some j
    | some k => if DistVal.dle (d j) (d k) then some j else some k

end CellTopology

/- ------------------------------------------------------------------- -/
/- Private helpers for the 1D and 2D instance proofs                    -/
/- ------------------------------------------------------------------- -/

/-- Helper: membership in `Option.toList` is equivalent to the option
    being `some` of the element. Used by both 1D and 2D neighbor lemmas. -/
private theorem mem_option_toList_gen {α : Type} {a : α} {o : Option α} :
    a ∈ o.toList → o = some a := by
  cases o with
  | none => simp [Option.toList]
  | some v => simp [Option.toList]; intro h; exact h.symm

/- ------------------------------------------------------------------- -/
/- 1D line instance                                                     -/
/- ------------------------------------------------------------------- -/

/-- Absolute difference of two Nat-valued indices, written as a
    coordinate-wise distance for `Fin n` cells. -/
def lineDist {n : Nat} (i j : Fin n) : Nat :=
  if i.val ≤ j.val then j.val - i.val else i.val - j.val

/-- Neighbor-list membership implies `areNeighbors` on a 1D line. -/
private theorem neighbors1D_mem_areNeighbors {n : Nat} (i j : Fin n) :
    j ∈ neighbors1D i → areNeighbors i j := by
  unfold neighbors1D
  intro hmem
  simp only [List.mem_append] at hmem
  rcases hmem with h | h
  · -- left neighbor
    have hsome := mem_option_toList_gen h
    unfold leftNeighbor at hsome
    split at hsome <;> simp at hsome
    · rename_i hpos
      -- hsome : ⟨i.val - 1, _⟩ = j
      have hval : j.val = i.val - 1 := by
        have := congrArg Fin.val hsome
        simp at this; omega
      right; omega
  · -- right neighbor
    have hsome := mem_option_toList_gen h
    unfold rightNeighbor at hsome
    split at hsome <;> simp at hsome
    · rename_i hlt
      have hval : j.val = i.val + 1 := by
        have := congrArg Fin.val hsome
        simp at this; omega
      left; exact hval.symm

/-- `areNeighbors i j` on the 1D line implies `j ∈ neighbors1D i`. -/
private theorem neighbors1D_complete_areNeighbors {n : Nat} (i j : Fin n) :
    areNeighbors i j → j ∈ neighbors1D i := by
  intro h
  unfold neighbors1D
  simp only [List.mem_append]
  rcases h with hfwd | hbwd
  · -- i.val + 1 = j.val: j is the right neighbor
    right
    have hlt : i.val + 1 < n := by
      have := j.isLt; omega
    have hj_eq : j = ⟨i.val + 1, hlt⟩ := by
      apply Fin.ext; exact hfwd.symm
    subst hj_eq
    have hr_eq : rightNeighbor i = some ⟨i.val + 1, hlt⟩ := by
      unfold rightNeighbor; simp [hlt]
    rw [hr_eq]; simp [Option.toList]
  · -- j.val + 1 = i.val: j is the left neighbor
    left
    have hpos : i.val > 0 := by omega
    have hbound : i.val - 1 < n := by have := i.isLt; omega
    have hj_eq : j = ⟨i.val - 1, hbound⟩ := by
      apply Fin.ext; simp; omega
    subst hj_eq
    have hl_eq : leftNeighbor i = some ⟨i.val - 1, hbound⟩ := by
      unfold leftNeighbor; simp [hpos]
    rw [hl_eq]; simp [Option.toList]

/-- Triangle inequality for `lineDist`. -/
private theorem lineDist_triangle {n : Nat} (i j t : Fin n) :
    areNeighbors i j → lineDist j t + 1 ≥ lineDist i t := by
  intro h
  unfold lineDist
  rcases h with hfwd | hbwd
  · split <;> split <;> omega
  · split <;> split <;> omega

/-- `lineDist` is symmetric. -/
private theorem lineDist_symm {n : Nat} (i j : Fin n) :
    lineDist i j = lineDist j i := by
  unfold lineDist
  split <;> split <;> omega

/-- `lineDist` of a cell to itself is 0. -/
private theorem lineDist_self {n : Nat} (i : Fin n) : lineDist i i = 0 := by
  unfold lineDist
  simp

/-- Existence of a closer neighbor on the 1D line. -/
private theorem lineDist_exists_closer {n : Nat} (i t : Fin n)
    (hne : i ≠ t) (_hpos : lineDist i t > 0) :
    ∃ j : Fin n, j ∈ neighbors1D i ∧ lineDist j t + 1 = lineDist i t := by
  have hval_ne : i.val ≠ t.val := by
    intro h; exact hne (Fin.ext h)
  by_cases hlt : i.val < t.val
  · -- right neighbor: i.val + 1
    have hbound : i.val + 1 < n := by
      have := t.isLt; omega
    refine ⟨⟨i.val + 1, hbound⟩, ?_, ?_⟩
    · -- membership in neighbors1D
      unfold neighbors1D
      simp only [List.mem_append]
      right
      have hr_eq : rightNeighbor i = some ⟨i.val + 1, hbound⟩ := by
        unfold rightNeighbor
        simp [hbound]
      rw [hr_eq]
      simp [Option.toList]
    · -- lineDist equation: unfold both sides with the explicit Fin.val
      show (if (i.val + 1) ≤ t.val then t.val - (i.val + 1) else (i.val + 1) - t.val) + 1
         = (if i.val ≤ t.val then t.val - i.val else i.val - t.val)
      (repeat' split) <;> omega
  · -- i.val > t.val: left neighbor
    have hgt : i.val > t.val := by omega
    have hpos : i.val > 0 := by omega
    have hbound : i.val - 1 < n := by have := i.isLt; omega
    refine ⟨⟨i.val - 1, hbound⟩, ?_, ?_⟩
    · unfold neighbors1D
      simp only [List.mem_append]
      left
      have hl_eq : leftNeighbor i = some ⟨i.val - 1, hbound⟩ := by
        unfold leftNeighbor
        simp [hpos]
      rw [hl_eq]
      simp [Option.toList]
    · show (if (i.val - 1) ≤ t.val then t.val - (i.val - 1) else (i.val - 1) - t.val) + 1
         = (if i.val ≤ t.val then t.val - i.val else i.val - t.val)
      (repeat' split) <;> omega

/-- Canonical `CellTopology` instance for a 1D line of `n` cells. -/
instance CellTopology1D (n : Nat) : CellTopology (Fin n) where
  decEq := inferInstance
  neighbors := neighbors1D
  areNeighbors := areNeighbors
  dist := lineDist
  decNeighbors _ _ := inferInstance
  neighbors_mem := neighbors1D_mem_areNeighbors
  neighbors_complete := neighbors1D_complete_areNeighbors
  dist_symm := lineDist_symm
  dist_self := lineDist_self
  triangle := lineDist_triangle
  exists_closer i t hne hpos := lineDist_exists_closer i t hne hpos

/- ------------------------------------------------------------------- -/
/- 2D grid instance                                                     -/
/- ------------------------------------------------------------------- -/

/-- Neighbor-list membership implies `areNeighbors2D` on the 2D grid.
    Reproved locally so Topology.lean does not depend on MultiColorProofs. -/
private theorem neighbors2D_mem_areNeighbors_local {n : Nat} (i j : CellId2D n) :
    j ∈ neighbors2D i → areNeighbors2D i j := by
  unfold neighbors2D
  intro hmem
  simp only [List.mem_append] at hmem
  unfold areNeighbors2D
  rcases hmem with ((h | h) | h) | h
  · -- upNeighbor
    have hsome := mem_option_toList_gen h
    unfold upNeighbor at hsome
    split at hsome <;> simp at hsome
    right; constructor
    · exact (Prod.mk.inj hsome).2
    · right; have := (Prod.mk.inj hsome).1; simp [Fin.ext_iff] at this; omega
  · -- downNeighbor
    have hsome := mem_option_toList_gen h
    unfold downNeighbor at hsome
    split at hsome <;> simp at hsome
    right; constructor
    · exact (Prod.mk.inj hsome).2
    · left; have := (Prod.mk.inj hsome).1; simp [Fin.ext_iff] at this; omega
  · -- leftNeighbor2D
    have hsome := mem_option_toList_gen h
    unfold leftNeighbor2D at hsome
    split at hsome <;> simp at hsome
    left; constructor
    · exact (Prod.mk.inj hsome).1
    · right; have := (Prod.mk.inj hsome).2; simp [Fin.ext_iff] at this; omega
  · -- rightNeighbor2D
    have hsome := mem_option_toList_gen h
    unfold rightNeighbor2D at hsome
    split at hsome <;> simp at hsome
    left; constructor
    · exact (Prod.mk.inj hsome).1
    · left; have := (Prod.mk.inj hsome).2; simp [Fin.ext_iff] at this; omega

/-- `areNeighbors2D i j` implies `j ∈ neighbors2D i`. -/
private theorem neighbors2D_complete_areNeighbors {n : Nat} (i j : CellId2D n) :
    areNeighbors2D i j → j ∈ neighbors2D i := by
  intro h
  unfold neighbors2D
  simp only [List.mem_append]
  rcases h with ⟨hrow, hcol⟩ | ⟨hcol, hrow⟩
  · -- Same row; columns differ by 1
    rcases hcol with hc | hc
    · -- i.2.val + 1 = j.2.val: rightNeighbor2D
      right
      have hbound : i.2.val + 1 < n := by
        have := j.2.isLt; omega
      have hj_eq : j = (i.1, ⟨i.2.val + 1, hbound⟩) := by
        apply Prod.ext
        · exact hrow.symm
        · apply Fin.ext; exact hc.symm
      subst hj_eq
      have hr_eq : rightNeighbor2D i = some (i.1, ⟨i.2.val + 1, hbound⟩) := by
        unfold rightNeighbor2D; simp [hbound]
      rw [hr_eq]; simp [Option.toList]
    · -- j.2.val + 1 = i.2.val: leftNeighbor2D
      left; right
      have hpos : i.2.val > 0 := by omega
      have hbound : i.2.val - 1 < n := by have := i.2.isLt; omega
      have hj_eq : j = (i.1, ⟨i.2.val - 1, hbound⟩) := by
        apply Prod.ext
        · exact hrow.symm
        · apply Fin.ext; simp; omega
      subst hj_eq
      have hl_eq : leftNeighbor2D i = some (i.1, ⟨i.2.val - 1, hbound⟩) := by
        unfold leftNeighbor2D; simp [hpos]
      rw [hl_eq]; simp [Option.toList]
  · -- Same column; rows differ by 1
    rcases hrow with hr | hr
    · -- i.1.val + 1 = j.1.val: downNeighbor
      left; left; right
      have hbound : i.1.val + 1 < n := by
        have := j.1.isLt; omega
      have hj_eq : j = (⟨i.1.val + 1, hbound⟩, i.2) := by
        apply Prod.ext
        · apply Fin.ext; exact hr.symm
        · exact hcol.symm
      subst hj_eq
      have hd_eq : downNeighbor i = some (⟨i.1.val + 1, hbound⟩, i.2) := by
        unfold downNeighbor; simp [hbound]
      rw [hd_eq]; simp [Option.toList]
    · -- j.1.val + 1 = i.1.val: upNeighbor
      left; left; left
      have hpos : i.1.val > 0 := by omega
      have hbound : i.1.val - 1 < n := by have := i.1.isLt; omega
      have hj_eq : j = (⟨i.1.val - 1, hbound⟩, i.2) := by
        apply Prod.ext
        · apply Fin.ext; simp; omega
        · exact hcol.symm
      subst hj_eq
      have hu_eq : upNeighbor i = some (⟨i.1.val - 1, hbound⟩, i.2) := by
        unfold upNeighbor; simp [hpos]
      rw [hu_eq]; simp [Option.toList]

/-- Triangle inequality for Manhattan distance on 2D grid neighbors. -/
private theorem manhattan_triangle_local {n : Nat} (i j t : CellId2D n) :
    areNeighbors2D i j → manhattan j t + 1 ≥ manhattan i t := by
  intro h
  unfold manhattan
  rcases h with ⟨hrow, hcol⟩ | ⟨hcol, hrow⟩
  · have hrow_eq : i.1.val = j.1.val := congrArg Fin.val hrow
    rcases hcol with hc | hc
    all_goals (split <;> split <;> split <;> split <;> omega)
  · have hcol_eq : i.2.val = j.2.val := congrArg Fin.val hcol
    rcases hrow with hr | hr
    all_goals (split <;> split <;> split <;> split <;> omega)

/-- Manhattan distance is symmetric. -/
private theorem manhattan_symm {n : Nat} (i j : CellId2D n) :
    manhattan i j = manhattan j i := by
  unfold manhattan
  split <;> split <;> split <;> split <;> omega

/-- Manhattan distance of a cell to itself is 0. -/
private theorem manhattan_self_local {n : Nat} (i : CellId2D n) :
    manhattan i i = 0 := by
  simp [manhattan]

/-- `manhattan i t = 0` implies `i = t`. -/
private theorem manhattan_eq_zero_imp_local {n : Nat} (i t : CellId2D n)
    (h : manhattan i t = 0) : i = t := by
  simp [manhattan] at h
  have hr : i.1.val = t.1.val := by have := h.1; split at this <;> omega
  have hc : i.2.val = t.2.val := by have := h.2; split at this <;> omega
  exact Prod.ext (Fin.ext hr) (Fin.ext hc)

/-- Existence of a closer neighbor on the 2D grid. -/
private theorem manhattan_exists_closer {n : Nat} (i t : CellId2D n)
    (hne : i ≠ t) (_hpos : manhattan i t > 0) :
    ∃ j : CellId2D n, j ∈ neighbors2D i ∧ manhattan j t + 1 = manhattan i t := by
  -- Since i ≠ t, at least one coordinate differs
  have hcoord : i.1.val ≠ t.1.val ∨ i.2.val ≠ t.2.val := by
    by_cases hr : i.1.val = t.1.val
    · right
      intro hc
      exact hne (Prod.ext (Fin.ext hr) (Fin.ext hc))
    · left; exact hr
  have hi1 : i.1.val < n := i.1.isLt
  have ht1 : t.1.val < n := t.1.isLt
  have hi2 : i.2.val < n := i.2.isLt
  have ht2 : t.2.val < n := t.2.isLt
  by_cases hrow : i.1.val = t.1.val
  · have hcol_ne : i.2.val ≠ t.2.val := by
      rcases hcoord with h | h
      · exact absurd hrow h
      · exact h
    by_cases hlt : i.2.val < t.2.val
    · have hbound : i.2.val + 1 < n := by omega
      refine ⟨(i.1, ⟨i.2.val + 1, hbound⟩), ?_, ?_⟩
      · unfold neighbors2D
        simp only [List.mem_append]
        right
        have hr_eq : rightNeighbor2D i = some (i.1, ⟨i.2.val + 1, hbound⟩) := by
          unfold rightNeighbor2D
          simp [hbound]
        rw [hr_eq]
        simp [Option.toList]
      · unfold manhattan
        show (if i.1.val ≤ t.1.val then t.1.val - i.1.val else i.1.val - t.1.val)
           + (if (i.2.val + 1) ≤ t.2.val then t.2.val - (i.2.val + 1) else (i.2.val + 1) - t.2.val) + 1
           = (if i.1.val ≤ t.1.val then t.1.val - i.1.val else i.1.val - t.1.val)
           + (if i.2.val ≤ t.2.val then t.2.val - i.2.val else i.2.val - t.2.val)
        (repeat' split) <;> omega
    · have hgt : i.2.val > t.2.val := by omega
      have hpos : i.2.val > 0 := by omega
      refine ⟨(i.1, ⟨i.2.val - 1, by omega⟩), ?_, ?_⟩
      · unfold neighbors2D
        simp only [List.mem_append]
        left; right
        have hl_eq : leftNeighbor2D i = some (i.1, ⟨i.2.val - 1, by omega⟩) := by
          unfold leftNeighbor2D
          simp [hpos]
        rw [hl_eq]
        simp [Option.toList]
      · unfold manhattan
        show (if i.1.val ≤ t.1.val then t.1.val - i.1.val else i.1.val - t.1.val)
           + (if (i.2.val - 1) ≤ t.2.val then t.2.val - (i.2.val - 1) else (i.2.val - 1) - t.2.val) + 1
           = (if i.1.val ≤ t.1.val then t.1.val - i.1.val else i.1.val - t.1.val)
           + (if i.2.val ≤ t.2.val then t.2.val - i.2.val else i.2.val - t.2.val)
        (repeat' split) <;> omega
  · by_cases hlt : i.1.val < t.1.val
    · have hbound : i.1.val + 1 < n := by omega
      refine ⟨(⟨i.1.val + 1, hbound⟩, i.2), ?_, ?_⟩
      · unfold neighbors2D
        simp only [List.mem_append]
        left; left; right
        have hd_eq : downNeighbor i = some (⟨i.1.val + 1, hbound⟩, i.2) := by
          unfold downNeighbor
          simp [hbound]
        rw [hd_eq]
        simp [Option.toList]
      · unfold manhattan
        show (if (i.1.val + 1) ≤ t.1.val then t.1.val - (i.1.val + 1) else (i.1.val + 1) - t.1.val)
           + (if i.2.val ≤ t.2.val then t.2.val - i.2.val else i.2.val - t.2.val) + 1
           = (if i.1.val ≤ t.1.val then t.1.val - i.1.val else i.1.val - t.1.val)
           + (if i.2.val ≤ t.2.val then t.2.val - i.2.val else i.2.val - t.2.val)
        (repeat' split) <;> omega
    · have hgt : i.1.val > t.1.val := by omega
      have hpos : i.1.val > 0 := by omega
      refine ⟨(⟨i.1.val - 1, by omega⟩, i.2), ?_, ?_⟩
      · unfold neighbors2D
        simp only [List.mem_append]
        left; left; left
        have hu_eq : upNeighbor i = some (⟨i.1.val - 1, by omega⟩, i.2) := by
          unfold upNeighbor
          simp [hpos]
        rw [hu_eq]
        simp [Option.toList]
      · unfold manhattan
        show (if (i.1.val - 1) ≤ t.1.val then t.1.val - (i.1.val - 1) else (i.1.val - 1) - t.1.val)
           + (if i.2.val ≤ t.2.val then t.2.val - i.2.val else i.2.val - t.2.val) + 1
           = (if i.1.val ≤ t.1.val then t.1.val - i.1.val else i.1.val - t.1.val)
           + (if i.2.val ≤ t.2.val then t.2.val - i.2.val else i.2.val - t.2.val)
        (repeat' split) <;> omega

/-- Canonical `CellTopology` instance for a 2D N×N grid. -/
instance CellTopology2D (n : Nat) : CellTopology (CellId2D n) where
  decEq := inferInstance
  neighbors := neighbors2D
  areNeighbors := areNeighbors2D
  dist := manhattan
  decNeighbors _ _ := inferInstance
  neighbors_mem := neighbors2D_mem_areNeighbors_local
  neighbors_complete := neighbors2D_complete_areNeighbors
  dist_symm := manhattan_symm
  dist_self := manhattan_self_local
  triangle := manhattan_triangle_local
  exists_closer i t hne hpos := manhattan_exists_closer i t hne hpos

end CellularFlows
