/-
  Cellular Flows — Euclidean (Mathlib) Continuous Model
  ========================================================

  Full real-valued Euclidean model paralleling `ContinuousModel.lean`
  (which uses the abstract Nat-based `MetricPoint` typeclass).

  This module uses Mathlib's `EuclideanSpace ℝ (Fin 2)` for entity
  positions, matching the paper's Section 2.3 exactly.  Paper Theorem 1
  states entities on the same cell are separated by Euclidean distance
  at least `d = r_s + l`.

  The Nat-based `ContinuousModel.lean` remains available as the
  self-contained (Mathlib-free) abstraction; this module provides the
  parallel Mathlib-based real Euclidean version.  Both coexist so the
  reader can compare the scaled-integer abstraction with the concrete
  ℝ²-valued formulation used in the paper.

  Paper reference:
    T.T. Johnson and S. Mitra, "Safe and Stabilizing Distributed
    Multi-Path Cellular Flows," TCS 579 (2015), Section 2.3,
    Theorem 1 (Section 4.2).
-/
import VerifDemo.CellularFlows.MultiColor
import VerifDemo.CellularFlows.MultiColorProofs
import VerifDemo.CellularFlows.ContinuousModel
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

set_option autoImplicit false

namespace CellularFlows.Euclidean

open scoped Real

/- =================================================================== -/
/- EUCLIDEAN POSITIONS (Mathlib ℝ²)                                     -/
/- =================================================================== -/

/-- A position in ℝ², using Mathlib's `EuclideanSpace ℝ (Fin 2)`.
    This gives us the full Euclidean metric structure (ℓ² distance),
    matching the paper's Section 2.3 model where entity positions live
    in ℝ² and the safety spacing `d = r_s + l` is a real-valued
    Euclidean distance threshold. -/
abbrev Pos2D := EuclideanSpace ℝ (Fin 2)

/-- Euclidean continuous entity: unique identifier, color, and a real-valued
    position in ℝ².  Paper Section 2.3 writes `p = (p_x, p_y) ∈ ℝ²`. -/
structure ContinuousEntityReal (nc : Nat) where
  /-- Unique identifier. -/
  id : Nat
  /-- Entity color, as in the paper's multi-color protocol. -/
  color : Fin nc
  /-- Entity position in `EuclideanSpace ℝ (Fin 2)`. -/
  pos : Pos2D

/-- Multi-color state with real-valued entity positions.  Refines the
    discrete `MCState` by attaching per-cell lists of continuous entities
    whose count matches the discrete `entities` field, giving a bridge
    between the discrete protocol abstraction and the paper's ℝ² model. -/
structure ContinuousMCStateReal (n nc : Nat) where
  /-- Underlying discrete state (entity counts, signals, locks, …). -/
  discrete : MCState n nc
  /-- Continuous entity positions per cell, in ℝ². -/
  positions : CellId2D n → List (ContinuousEntityReal nc)
  /-- List length at every cell matches the discrete entity count. -/
  count_consistent : ∀ i : CellId2D n,
    (positions i).length = discrete.entities i

/- =================================================================== -/
/- CONTINUOUS (REAL) SAFETY PREDICATE                                   -/
/- =================================================================== -/

/-- Real-valued continuous safety: every pair of distinct entities at the
    same cell is separated by Euclidean distance at least `d`.  Here
    `d : ℝ` is the paper's safety spacing `d = r_s + l`, and `dist` is
    the Mathlib Euclidean metric on `EuclideanSpace ℝ (Fin 2)`.

    Paper reference: Theorem 1, Section 4.2 of TCS 2015. -/
def ContinuousSafeReal {n nc : Nat} (d : ℝ)
    (s : ContinuousMCStateReal n nc) : Prop :=
  ∀ i : CellId2D n, ∀ p q : ContinuousEntityReal nc,
    p ∈ s.positions i → q ∈ s.positions i → p ≠ q →
    dist p.pos q.pos ≥ d

/-- Real-valued single-color invariant: all entities at the same cell share
    the same color.  Paper Invariant 3. -/
def ContinuousSingleColorReal {n nc : Nat}
    (s : ContinuousMCStateReal n nc) : Prop :=
  ∀ i : CellId2D n, ∀ p q : ContinuousEntityReal nc,
    p ∈ s.positions i → q ∈ s.positions i → p.color = q.color

/- =================================================================== -/
/- GEOMETRIC BRIDGE (discrete ⟹ real Euclidean safety)                 -/
/- =================================================================== -/

/-- Real-valued "valid placement" hypothesis: the ℝ² positions in `s`
    are consistent with having been produced by a valid sequence of
    Move phase transfers from an initial all-empty configuration.  The
    real-valued analogue of `ValidContinuousPlacement` from
    `ContinuousModel.lean`; axiomatised for the same reason (we do not
    formalise continuous dynamics). -/
axiom ValidContinuousPlacementReal {n nc : Nat}
    (targets : Fin nc → CellId2D n)
    (s : ContinuousMCStateReal n nc) : Prop

/-- A real-valued continuous state is `ContinuousReachableReal` if (a)
    its discrete projection is reachable in the multi-color transition
    system, and (b) its ℝ² positions satisfy
    `ValidContinuousPlacementReal`.  Required by the geometric bridge
    for soundness (see `ContinuousModel.lean` for the parallel
    explanation in the Nat metric case). -/
def ContinuousReachableReal {n nc : Nat}
    (targets : Fin nc → CellId2D n)
    (s : ContinuousMCStateReal n nc) : Prop :=
  Reachable (multiColorTS n nc targets) s.discrete ∧
  ValidContinuousPlacementReal targets s

/-- ★ Geometric bridge axiom, real-valued version (Theorem 1, paper
    Section 4.2).

    Parallels `continuous_safety_bridge` from `ContinuousModel.lean` but
    uses the real-valued Euclidean metric on `EuclideanSpace ℝ (Fin 2)`
    rather than the abstract Nat-valued `MetricPoint` instance.  The
    content of the argument is unchanged:

    * `MCDiscreteSafe` ensures that the signal/move rules never transfer
      entities in ways that violate the single-color invariant or the
      lock discipline at intersections.
    * Paper Assumptions 1-2 (in `Assumptions.lean`) provide the geometric
      guarantee that each cell's transfer/safety regions admit a valid
      configuration of entity positions obeying the center-to-center
      spacing `d = r_s + l`.
    * Together, these imply that in every reachable continuous state,
      entities at the same cell are separated by Euclidean distance at
      least `d`.

    The `hreach : ContinuousReachableReal targets s` hypothesis is
    required so that the bridge applies only to states produced by the
    protocol, not to adversarially chosen ℝ² placements.

    A fully-machine-checked proof would require discharging the paper's
    geometric reasoning about disk packings and convex cell regions in
    Mathlib — a substantial development we keep as future work. -/
axiom continuous_safety_bridge_real {n nc : Nat}
    (targets : Fin nc → CellId2D n)
    (d : ℝ) (hd : d ≥ 0)
    (s : ContinuousMCStateReal n nc)
    (hreach : ContinuousReachableReal targets s) :
    MCDiscreteSafe s.discrete → ContinuousSafeReal d s

/- =================================================================== -/
/- CONTINUOUS (REAL) THEOREM 1                                           -/
/- =================================================================== -/

/-- ★ Paper-form continuous Theorem 1 (Euclidean version).

    For any continuous state whose underlying discrete state is
    reachable in the multi-color transition system and whose ℝ²
    positions form a valid placement, every pair of distinct entities
    at the same cell has Euclidean distance at least `d` in ℝ².

    Paper reference: Theorem 1, Section 4.2 of TCS 2015. -/
theorem continuous_theorem_1_real {n nc : Nat}
    (targets : Fin nc → CellId2D n)
    (d : ℝ) (hd : d ≥ 0)
    (s : ContinuousMCStateReal n nc)
    (hreach : ContinuousReachableReal targets s)
    (hds : MCDiscreteSafe s.discrete) :
    ContinuousSafeReal d s :=
  continuous_safety_bridge_real targets d hd s hreach hds

/-- ★ Reachable-state version of the Euclidean Theorem 1.

    Any reachable state of the multi-color transition system, lifted to
    a continuous state in ℝ² with consistent positions that satisfy
    `ValidContinuousPlacementReal`, satisfies the real Euclidean safety
    property. -/
theorem continuous_theorem_1_real_reachable {n nc : Nat}
    (targets : Fin nc → CellId2D n)
    (d : ℝ) (hd : d ≥ 0)
    (s : ContinuousMCStateReal n nc)
    (hreach : Reachable (multiColorTS n nc targets) s.discrete)
    (hplace : ValidContinuousPlacementReal targets s) :
    ContinuousSafeReal d s :=
  continuous_safety_bridge_real targets d hd s ⟨hreach, hplace⟩
    (mcDiscreteSafe_invariant n nc targets s.discrete hreach)

/- =================================================================== -/
/- SANITY CHECKS: Mathlib Euclidean metric is non-degenerate            -/
/- =================================================================== -/

/-- Sanity check: Euclidean distance from a point to itself is zero. -/
theorem pos2D_dist_self (p : Pos2D) : dist p p = (0 : ℝ) := dist_self p

/-- Sanity check: Euclidean distance is symmetric on `Pos2D`. -/
theorem pos2D_dist_symm (p q : Pos2D) : dist p q = dist q p := dist_comm p q

/-- Sanity check: Euclidean distance is non-negative on `Pos2D`. -/
theorem pos2D_dist_nonneg (p q : Pos2D) : (0 : ℝ) ≤ dist p q := dist_nonneg

/-- Sanity check: the Euclidean safety predicate is vacuously satisfied
    when `d ≤ 0` and all lists are empty — this merely confirms the
    statement type-checks and is non-trivial. -/
theorem continuousSafeReal_empty {n nc : Nat} (d : ℝ)
    (s : ContinuousMCStateReal n nc)
    (hempty : ∀ i : CellId2D n, s.positions i = []) :
    ContinuousSafeReal d s := by
  intro i p q hp _ _
  rw [hempty i] at hp
  cases hp

end CellularFlows.Euclidean
