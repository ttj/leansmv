/-
  Cellular Flows — Route Subroutine (1D Line)
  =============================================

  This module defines the Route-only transition system on a 1D line of
  N cells, with target at cell 0. Each round, every non-failed cell updates
  its estimated distance to target and next-hop neighbor via Bellman-Ford.

  Paper reference: Fig. 8, Section 3.3.1 (Route subroutine for Cell_i).

  The Route subroutine computes a minimum distance vector routing table
  to each target, rooted and composed of non-faulty cells. For the 1D
  failure-free case, the true shortest-path distance from cell i to
  target 0 is simply i. After k rounds of Route, all cells at distance
  ≤ k have correct dist values (Lemma 6).
-/
import VerifDemo.CellularFlows.Defs

namespace CellularFlows

/-- State of the 1D routing system with n cells, target at cell 0.
    Models the per-cell variables dist, next, failed from Fig. 7. -/
structure RouteState (n : Nat) where
  dist   : Fin n → DistVal
  next   : Fin n → Option (Fin n)
  failed : Fin n → Bool

/-- A single round of the Route subroutine for the failure-free 1D case.

    For each cell i:
    - If i = 0 (target): dist stays 0, next stays none.
    - If failed: dist = inf, next = none.
    - Otherwise: dist_i' = 1 + min(dist_j for j in non-failed neighbors),
                 next_i' = argmin neighbor (breaking ties by cell index).

    This is the Bellman-Ford update from Fig. 8 of the paper. -/
def routeTS (n : Nat) : TransitionSystem (RouteState n) where
  init s :=
    (∀ i : Fin n, i.val = 0 → s.dist i = .fin 0) ∧
    (∀ i : Fin n, i.val = 0 → s.next i = none) ∧
    (∀ i : Fin n, i.val ≠ 0 → s.dist i = .inf) ∧
    (∀ i : Fin n, i.val ≠ 0 → s.next i = none) ∧
    (∀ i : Fin n, s.failed i = false)
  next s s' :=
    (∀ i : Fin n, s'.failed i = s.failed i) ∧
    (∀ i : Fin n, i.val = 0 →
      s'.dist i = .fin 0 ∧ s'.next i = none) ∧
    (∀ i : Fin n, s.failed i = true →
      s'.dist i = .inf ∧ s'.next i = none) ∧
    (∀ i : Fin n, s.failed i = false → i.val ≠ 0 →
      let nbrs := nonFailedNeighbors s.failed i
      s'.dist i = (minDist s.dist nbrs).succ ∧
      s'.next i = argminDist s.dist nbrs)

/-- The failure-free specialization: no cell ever fails.
    In this case, Route self-stabilizes in n-1 rounds. -/
def routeFFTS (n : Nat) : TransitionSystem (RouteState n) where
  init s :=
    (∀ i : Fin n, i.val = 0 → s.dist i = .fin 0) ∧
    (∀ i : Fin n, i.val ≠ 0 → s.dist i = .inf) ∧
    (∀ i : Fin n, s.next i = none) ∧
    (∀ i : Fin n, s.failed i = false)
  next s s' :=
    (∀ i : Fin n, s'.failed i = false) ∧
    (∀ i : Fin n, i.val = 0 →
      s'.dist i = .fin 0 ∧ s'.next i = none) ∧
    (∀ i : Fin n, i.val ≠ 0 →
      let nbrs := neighbors1D i
      s'.dist i = (minDist s.dist nbrs).succ ∧
      s'.next i = argminDist s.dist nbrs)

end CellularFlows
