/-
  Cellular Flows — Numerical Parameters (paper notation)
  =======================================================

  This module collects the paper's numerical parameters for the
  continuous model (Section 2.3 and Fig. 7) into a single structure.
  The discrete formalization in the rest of the library abstracts these
  away — discrete safety and liveness hold independently of the
  concrete numeric values — but we define the structure here to make
  the paper-to-Lean correspondence complete.

  Paper reference:
    T.T. Johnson and S. Mitra, "Safe and Stabilizing Distributed
    Multi-Path Cellular Flows," TCS 579 (2015), Section 2.3.
-/

set_option autoImplicit false

namespace CellularFlows

/-- Numerical parameters of the cellular flows system.

    Paper Section 2.3 and Fig. 7.

    * `l`  — entity radius (disc radius around position p)
    * `r_s` — minimum required inter-entity safety gap
    * `d = r_s + l` — total center-to-center safety spacing
    * `v`  — maximum velocity (distance traversed per round)

    Paper constraints: `0 < v < l < 1` and `r_s + l < 1`.
    In the discrete model these constraints are abstracted away — our
    safety and liveness proofs do not depend on their specific values —
    but the structure is recorded here for documentation. -/
structure CellFlowsParameters where
  /-- Entity radius (disc around position p). Paper Section 2.3. -/
  l   : Nat := 1
  /-- Minimum inter-entity safety gap r_s. Paper Section 2.3. -/
  r_s : Nat := 0
  /-- Maximum velocity (cell distance per round). Paper Section 2.3. -/
  v   : Nat := 0

namespace CellFlowsParameters

/-- Center-to-center safety spacing `d = r_s + l`. Paper Section 2.3. -/
def d (p : CellFlowsParameters) : Nat := p.r_s + p.l

/-- The "default" parameter choice used throughout the discrete model.
    Paper Section 2.3 does not fix any single numeric assignment; this
    choice (l = 1, r_s = 0, v = 0) is a minimally-valid instance in the
    discrete domain where all geometric constraints reduce to `True`. -/
def default : CellFlowsParameters := {}

end CellFlowsParameters

end CellularFlows
