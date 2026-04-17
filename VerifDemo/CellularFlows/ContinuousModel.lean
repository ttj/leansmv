/-
  Cellular Flows — Continuous Position Model
  =============================================

  Bridges the discrete protocol abstraction (entity counts per cell) to
  the paper's continuous physical model (entities as points in R² with
  Euclidean distance). Paper Section 2.3.

  We use an abstract metric space typeclass rather than Mathlib's ℝ,
  keeping the formalization self-contained. The typeclass captures the
  properties needed for the continuous safety argument:
  - non-negative distance (automatic for Nat-valued metrics)
  - reflexive zero (dist p p = 0)
  - symmetric (dist p q = dist q p)
  - triangle inequality (dist p r ≤ dist p q + dist q r)
  - zero iff identical (dist p q = 0 ↔ p = q)

  When instantiated with ℝ², these correspond to Euclidean distance.
  The formalization can be lifted to use Mathlib's EuclideanSpace later
  without changing the rest of the proof structure.

  Paper reference:
    T.T. Johnson and S. Mitra, "Safe and Stabilizing Distributed
    Multi-Path Cellular Flows," TCS 579 (2015), Section 2.3.
-/
import VerifDemo.CellularFlows.MultiColor
import VerifDemo.CellularFlows.MultiColorProofs
import VerifDemo.CellularFlows.Parameters

set_option autoImplicit false

namespace CellularFlows

/- =================================================================== -/
/- ABSTRACT METRIC SPACE                                                -/
/- =================================================================== -/

/-- Abstract metric space: points with a Nat-valued distance function.
    We use Nat for simplicity (would be ℝ in a Mathlib-based version).
    Intuitively, distance is scaled-integer (e.g., "grid units × 1000"),
    and all thresholds are expressed in the same scaled units.

    Required axioms:
    * `dist_self`: distance from a point to itself is zero.
    * `dist_symm`: distance is symmetric.
    * `dist_triangle`: distance satisfies the triangle inequality.
    * `dist_eq_zero_iff`: zero distance characterises equality.

    Non-negativity is automatic because the codomain is `Nat`. -/
class MetricPoint (α : Type) where
  /-- The distance function on `α`. -/
  dist : α → α → Nat
  /-- Distance from a point to itself is zero. -/
  dist_self : ∀ p : α, dist p p = 0
  /-- Distance is symmetric. -/
  dist_symm : ∀ p q : α, dist p q = dist q p
  /-- Triangle inequality. -/
  dist_triangle : ∀ p q r : α, dist p r ≤ dist p q + dist q r
  /-- Points are equal iff their distance is zero. -/
  dist_eq_zero_iff : ∀ p q : α, dist p q = 0 ↔ p = q

/- =================================================================== -/
/- CONTINUOUS ENTITIES                                                   -/
/- =================================================================== -/

/-- A continuous entity: a unique identifier, a color, and a position in
    an abstract metric space.  Paper Section 2.3 uses `p = (p_x, p_y) ∈ ℝ²`;
    we abstract the position type so the formalization is Mathlib-free. -/
structure ContinuousEntity (α : Type) (nc : Nat) where
  /-- Unique identifier for this entity. -/
  id : Nat
  /-- Entity color, as in the paper's multi-color protocol. -/
  color : Fin nc
  /-- Entity position in the ambient metric space. -/
  pos : α

/-- Continuous multi-color state: extends the discrete `MCState` with a
    list of continuous entities per cell.  The list length at cell `i`
    must equal the discrete entity count `discrete.entities i`, so the
    continuous model is a refinement — not a replacement — of the
    discrete one. -/
structure ContinuousMCState (α : Type) (n nc : Nat) where
  /-- The underlying discrete state (entity counts, signals, locks, …). -/
  discrete : MCState n nc
  /-- Continuous entity positions per cell. -/
  positions : CellId2D n → List (ContinuousEntity α nc)
  /-- Invariant: list length matches the discrete count at every cell. -/
  count_consistent : ∀ i : CellId2D n,
    (positions i).length = discrete.entities i

/- =================================================================== -/
/- CONTINUOUS SAFETY AND COLOR PREDICATES                                -/
/- =================================================================== -/

/-- Continuous safety predicate: for every cell, every pair of distinct
    entities on that cell are separated by at least the safety spacing
    `d = r_s + l`.  Paper Theorem 1, Section 4.2. -/
def ContinuousSafe {α : Type} [MetricPoint α] {n nc : Nat}
    (params : CellFlowsParameters) (s : ContinuousMCState α n nc) : Prop :=
  ∀ i : CellId2D n, ∀ p q : ContinuousEntity α nc,
    p ∈ s.positions i → q ∈ s.positions i → p ≠ q →
    MetricPoint.dist p.pos q.pos ≥ params.d

/-- Continuous single-color invariant: all entities at the same cell
    share the same color.  Paper Invariant 3. -/
def ContinuousSingleColor {α : Type} {n nc : Nat}
    (s : ContinuousMCState α n nc) : Prop :=
  ∀ i : CellId2D n, ∀ p q : ContinuousEntity α nc,
    p ∈ s.positions i → q ∈ s.positions i → p.color = q.color

/- =================================================================== -/
/- MULTI-COLOR DISCRETE SAFETY                                           -/
/- =================================================================== -/

/-- Multi-color discrete safety predicate.

    This is the multi-color analogue of `DiscreteSafe` from
    `DiscreteSafety.lean`.  It bundles the protocol-level invariants
    already proved axiom-free in `MultiColorProofs.lean`:

    1. `lockMutex`                — at most one color holds a lock at
       any cell (Lemma 10, Fig. 9 lines 8-17);
    2. `signalRespectsLock`        — signals at intersection cells
       require the appropriate lock (Lemma 10 discrete form);
    3. `colorConsistent`           — empty cells have no color
       (Invariant 3);
    4. `mcSignalValid`             — every non-none signal points to a
       valid 2D neighbor (Signal subroutine, Fig. 10);
    5. `lockRequiresIntersection`  — the chain lock ⟹ needsLock ⟹ pint
       (Fig. 9 precondition).

    Note: the 1D `noSignalCycle2` predicate (Lemma 5) is defined on the
    1D `CellFlowState` and has no direct 2D `MCState` counterpart in
    this formalization — the corresponding multi-color structural fact
    is captured by `mcSignalValid` together with the per-color dist
    lower bound already available through `mcDistLowerBound_invariant`.

    By the paper's Theorem 1, these discrete properties together imply
    continuous safety under the geometric Assumptions 1-2 on the cell
    partition. -/
def MCDiscreteSafe {n nc : Nat} (s : MCState n nc) : Prop :=
  lockMutex s ∧
  signalRespectsLock s ∧
  colorConsistent s ∧
  mcSignalValid s ∧
  lockRequiresIntersection s

/-- `MCDiscreteSafe` is invariant for the multi-color transition system.
    Immediate corollary of the component invariants already proved in
    `MultiColorProofs.lean`. -/
theorem mcDiscreteSafe_invariant (n nc : Nat) (targets : Fin nc → CellId2D n) :
    Invariant (multiColorTS n nc targets) MCDiscreteSafe := by
  intro s hreach
  exact ⟨lockMutex_invariant n nc targets s hreach,
         signalRespectsLock_invariant n nc targets s hreach,
         colorConsistent_invariant n nc targets s hreach,
         mcSignalValid_invariant n nc targets s hreach,
         lockRequiresIntersection_invariant n nc targets s hreach⟩

/- =================================================================== -/
/- GEOMETRIC BRIDGE (discrete ⟹ continuous safety)                      -/
/- =================================================================== -/

/-- A "valid placement" hypothesis: the continuous positions in `s` are
    consistent with having been produced by a valid sequence of Move
    phase transfers from an initial all-empty configuration.  This is a
    continuous-level reachability assumption that we axiomatise rather
    than define operationally (since we don't formalise continuous
    dynamics).  The paper's Assumptions 1-2 (in `Assumptions.lean`) give
    the geometric guarantee that such valid placements always respect
    the safety spacing `d = r_s + l`.

    Scoping this assumption explicitly (rather than applying the bridge
    to every `ContinuousMCState`) is crucial for soundness: otherwise a
    user could construct a state with `MCDiscreteSafe` holding but
    entities placed at identical positions, and the bridge would
    declare it "safe" — a contradiction. -/
axiom ValidContinuousPlacement {α : Type} [MetricPoint α] {n nc : Nat}
    (targets : Fin nc → CellId2D n)
    (s : ContinuousMCState α n nc) : Prop

/-- A continuous state is `ContinuousReachable` if (a) its discrete
    projection is reachable in the multi-color transition system, and
    (b) its continuous positions satisfy the `ValidContinuousPlacement`
    hypothesis above.  This is the combined hypothesis required by the
    geometric safety bridge. -/
def ContinuousReachable {α : Type} [MetricPoint α] {n nc : Nat}
    (targets : Fin nc → CellId2D n)
    (s : ContinuousMCState α n nc) : Prop :=
  Reachable (multiColorTS n nc targets) s.discrete ∧
  ValidContinuousPlacement targets s

/-- ★ Geometric bridge axiom (Theorem 1, paper Section 4.2).

    This axiom captures the paper's argument that combines the discrete
    protocol invariants with the geometric Assumptions 1-2 (from
    `Assumptions.lean`) to yield the continuous safety property.

    The content of the argument is:
    * `MCDiscreteSafe` ensures that the signal/move rules never transfer
      entities in ways that violate the single-color invariant or the
      lock discipline at intersections.
    * Assumptions 1-2 provide the geometric guarantee that each cell's
      transfer/safety regions admit a valid configuration of entity
      positions obeying the center-to-center spacing `d = r_s + l`.
    * Together, these imply that in every reachable continuous state,
      entities at the same cell are separated by at least `d`.

    The `hreach : ContinuousReachable targets s` hypothesis restricts
    the bridge to states that actually arise from the protocol — this
    prevents deriving safety about adversarially chosen continuous
    placements whose discrete projection happens to satisfy
    `MCDiscreteSafe`.

    Making this a fully-machine-checked theorem would require Mathlib's
    Euclidean geometry (convex polygons, disk packings, etc.) — which we
    deliberately avoid.  We therefore record it as an axiomatic bridge,
    clearly marked as geometric. -/
axiom continuous_safety_bridge {α : Type} [MetricPoint α] {n nc : Nat}
    (targets : Fin nc → CellId2D n)
    (params : CellFlowsParameters)
    (s : ContinuousMCState α n nc)
    (hreach : ContinuousReachable targets s) :
    MCDiscreteSafe s.discrete → ContinuousSafe params s

/-- ★ Continuous Theorem 1 (paper form).

    For any continuous state whose underlying discrete state is
    reachable in the multi-color transition system and whose continuous
    positions satisfy `ValidContinuousPlacement` (captured jointly as
    `ContinuousReachable`), the continuous safety property holds.

    Paper reference: Theorem 1, Section 4.2 of TCS 2015. -/
theorem continuous_theorem_1 {α : Type} [MetricPoint α] {n nc : Nat}
    (targets : Fin nc → CellId2D n)
    (params : CellFlowsParameters)
    (s : ContinuousMCState α n nc)
    (hreach : ContinuousReachable targets s)
    (hd : MCDiscreteSafe s.discrete) :
    ContinuousSafe params s :=
  continuous_safety_bridge targets params s hreach hd

/-- Paper-form Theorem 1 combined with the discrete invariant: any
    continuous state whose discrete projection is reachable in the
    multi-color transition system and whose positions form a valid
    placement satisfies continuous safety. -/
theorem continuous_theorem_1_reachable {α : Type} [MetricPoint α]
    {n nc : Nat} (targets : Fin nc → CellId2D n)
    (params : CellFlowsParameters)
    (s : ContinuousMCState α n nc)
    (hreach : Reachable (multiColorTS n nc targets) s.discrete)
    (hplace : ValidContinuousPlacement targets s) :
    ContinuousSafe params s :=
  continuous_safety_bridge targets params s ⟨hreach, hplace⟩
    (mcDiscreteSafe_invariant n nc targets s.discrete hreach)

/- =================================================================== -/
/- CONCRETE INSTANCE: GRID POINTS WITH MANHATTAN METRIC                  -/
/- =================================================================== -/

/-- Absolute difference of two naturals, expressed positively. -/
def natAbsDiff (a b : Nat) : Nat := if a ≤ b then b - a else a - b

/-- Rational 2D grid point with Manhattan (taxicab) distance.  The paper
    uses Euclidean distance in ℝ²; this Nat-valued instance stands in for
    that without a Mathlib dependency.  Manhattan distance is a metric on
    `ℕ × ℕ` and inherits the triangle inequality from `ℕ`. -/
structure GridPos where
  /-- Grid-x coordinate. -/
  x : Nat
  /-- Grid-y coordinate. -/
  y : Nat
  deriving DecidableEq, Repr

namespace GridPos

/-- Manhattan distance between two grid positions. -/
def manhattan (p q : GridPos) : Nat := natAbsDiff p.x q.x + natAbsDiff p.y q.y

end GridPos

/-- Helper lemma: `natAbsDiff` is zero iff the two inputs are equal. -/
private theorem natAbsDiff_eq_zero_iff (a b : Nat) :
    natAbsDiff a b = 0 ↔ a = b := by
  unfold natAbsDiff
  by_cases h : a ≤ b
  · simp [h]; omega
  · simp [h]; omega

/-- Helper lemma: `natAbsDiff` is symmetric. -/
private theorem natAbsDiff_symm (a b : Nat) :
    natAbsDiff a b = natAbsDiff b a := by
  unfold natAbsDiff
  by_cases h1 : a ≤ b
  · by_cases h2 : b ≤ a
    · have : a = b := Nat.le_antisymm h1 h2; simp [this]
    · simp [h1, h2]
  · by_cases h2 : b ≤ a
    · simp [h1, h2]
    · omega

/-- Helper lemma: `natAbsDiff` satisfies the triangle inequality. -/
private theorem natAbsDiff_triangle (a b c : Nat) :
    natAbsDiff a c ≤ natAbsDiff a b + natAbsDiff b c := by
  unfold natAbsDiff
  -- case-split on all three comparisons
  by_cases hac : a ≤ c
  · by_cases hab : a ≤ b
    · by_cases hbc : b ≤ c
      · simp [hac, hab, hbc]; omega
      · simp [hac, hab, hbc]; omega
    · by_cases hbc : b ≤ c
      · simp [hac, hab, hbc]; omega
      · simp [hac, hab, hbc]; omega
  · by_cases hab : a ≤ b
    · by_cases hbc : b ≤ c
      · simp [hac, hab, hbc]; omega
      · simp [hac, hab, hbc]; omega
    · by_cases hbc : b ≤ c
      · simp [hac, hab, hbc]; omega
      · simp [hac, hab, hbc]; omega

/-- `GridPos` forms a metric space under Manhattan distance.  This gives
    a concrete, Mathlib-free example instantiation of `MetricPoint`,
    demonstrating the abstraction is non-vacuous. -/
instance : MetricPoint GridPos where
  dist p q := GridPos.manhattan p q
  dist_self := by
    intro p
    simp [GridPos.manhattan, natAbsDiff_eq_zero_iff]
  dist_symm := by
    intro p q
    simp [GridPos.manhattan]
    rw [natAbsDiff_symm p.x q.x, natAbsDiff_symm p.y q.y]
  dist_triangle := by
    intro p q r
    unfold GridPos.manhattan
    have hx := natAbsDiff_triangle p.x q.x r.x
    have hy := natAbsDiff_triangle p.y q.y r.y
    omega
  dist_eq_zero_iff := by
    intro p q
    constructor
    · intro h
      unfold GridPos.manhattan at h
      have hx : natAbsDiff p.x q.x = 0 := by omega
      have hy : natAbsDiff p.y q.y = 0 := by omega
      have ex : p.x = q.x := (natAbsDiff_eq_zero_iff _ _).mp hx
      have ey : p.y = q.y := (natAbsDiff_eq_zero_iff _ _).mp hy
      cases p; cases q; simp_all
    · intro h
      subst h
      simp [GridPos.manhattan, natAbsDiff_eq_zero_iff]

/-- Sanity check: the distance from a point to itself is zero in the
    `GridPos` instance.  This is `dist_self` specialised, recorded as a
    theorem to show the instance is concretely usable. -/
theorem gridPos_dist_self (p : GridPos) :
    MetricPoint.dist p p = 0 :=
  MetricPoint.dist_self p

/-- Sanity check: two distinct grid points have positive distance. -/
theorem gridPos_dist_pos {p q : GridPos} (hne : p ≠ q) :
    0 < MetricPoint.dist p q := by
  rcases Nat.eq_zero_or_pos (MetricPoint.dist p q) with hzero | hpos
  · exact absurd ((MetricPoint.dist_eq_zero_iff p q).mp hzero) hne
  · exact hpos

end CellularFlows
