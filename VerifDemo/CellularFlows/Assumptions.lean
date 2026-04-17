/-
  Cellular Flows — Paper Assumptions (Section 2.5)
  ==================================================

  This module states the paper's Assumptions 1 and 2 as documented
  axioms.  These are geometric assumptions about the cell partition that
  the paper makes on the underlying CONTINUOUS model (vector fields and
  transfer regions between cells).  Our discrete formalization abstracts
  away continuous positions, so the main proofs don't use these axioms
  operationally — but we state them here for explicit paper-to-Lean
  correspondence and traceability.

  These axioms involve opaque `Prop`-valued predicates whose content is
  intentionally unspecified.  As a result, they do not add proof power:
  nothing in the rest of the library discharges proof obligations by
  appealing to them.  They serve as documentation that the paper's
  continuous geometric assumptions are acknowledged.

  Paper reference:
    T.T. Johnson and S. Mitra, "Safe and Stabilizing Distributed
    Multi-Path Cellular Flows," TCS 579 (2015), Section 2.5.
-/
import VerifDemo.CellularFlows.Grid

set_option autoImplicit false

namespace CellularFlows

/-- Opaque predicate standing in for "cell i admits a constant vector
    field that drives every interior point to side s without leaving
    cell i".  Paper Section 2.5, Assumption 1.

    The content of this predicate is deliberately unspecified: in the
    continuous model it is a fact about each cell's geometry and the
    vector field library; in the discrete model we do not refer to
    vector fields at all. -/
axiom ProjectionProperty {n : Nat} (i : CellId2D n) (s : Fin 4) : Prop

/-- Paper Assumption 1 (Projection property).

    Every cell admits, for each of its four sides, a constant vector
    field that projects interior points onto that side without leaving
    the cell.

    The discrete model does not use this fact (we model transfers as
    abstract count updates), so this axiom is recorded here for
    documentation and carries no proof burden elsewhere. -/
axiom assumption1_projection_property {n : Nat} :
    ∀ i : CellId2D n, ∀ s : Fin 4, ProjectionProperty i s

/-- Opaque predicate standing in for "the inner transfer regions along
    the shared boundary of cells i and j are line segments of equal
    length".  Paper Section 2.5, Assumption 2. -/
axiom TransferFeasibility {n : Nat} (i j : CellId2D n) : Prop

/-- Paper Assumption 2 (Transfer feasibility).

    For any pair of neighbouring cells, the inner transfer regions along
    their shared boundary have equal length.

    In the discrete model transfers are abstracted to entity-count
    updates, so this geometric fact is not referenced by any proof. It
    is recorded here for paper-to-Lean correspondence. -/
axiom assumption2_transfer_feasibility {n : Nat} :
    ∀ i j : CellId2D n, areNeighbors2D i j → TransferFeasibility i j

end CellularFlows
