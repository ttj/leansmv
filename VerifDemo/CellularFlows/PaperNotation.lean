/-
  Cellular Flows — Paper Notation (explicit list-valued helpers)
  ===============================================================

  This module exposes the paper's notation from Sections 3.2-4.4 (Figures
  7-11) as concrete, computable list-valued helpers. The transition system
  in `MultiColor.lean` expresses these sets implicitly through step
  constraints and `Prop`-valued predicates like `entityGraphVertex`,
  `targetConnected`, and `colorSharedCell`. Here we provide list-valued
  counterparts that match the paper's set-builder notation more directly
  and that can be evaluated on a concrete state.

  None of the main proofs depend on these helpers — they exist to make
  the paper-to-Lean correspondence explicit and to support readers who
  want to see "NEPrev" and "SC" and "lcs" etc. written out as functions.

  Paper reference:
    T.T. Johnson and S. Mitra, "Safe and Stabilizing Distributed
    Multi-Path Cellular Flows," TCS 579 (2015), Sections 3.2-4.4.
-/
import VerifDemo.CellularFlows.MultiColor

set_option autoImplicit false

namespace CellularFlows

/- =================================================================== -/
/- Boolean versions of the graph-vertex predicates (for list filters).  -/
/- =================================================================== -/

/-- Boolean version of `targetConnected`: cell i is target-connected for
    color c iff it is non-faulty and its distance is finite.

    Paper: TC(x,c) = {i ∈ NF(x) | ρ_c(x,i) < ∞}. Section 4.3. -/
def targetConnectedB {n nc : Nat} (s : MCState n nc) (c : Fin nc)
    (i : CellId2D n) : Bool :=
  (!s.failed i) &&
    (match s.dist c i with
     | .fin _ => true
     | .inf   => false)

/-- Boolean version of `entityGraphVertex`: cell i belongs to V_E(x,c) iff
    it is non-faulty and either colored c or target-connected for c.

    Paper: V_E(x,c). Section 3.3.2. -/
def entityGraphVertexB {n nc : Nat} (s : MCState n nc) (c : Fin nc)
    (i : CellId2D n) : Bool :=
  (!s.failed i) &&
    (decide (s.color i = some c) || targetConnectedB s c i)

/- =================================================================== -/
/- Paper-notation list-valued helpers.                                  -/
/- =================================================================== -/

/-- `NEPrev(x, i, c)` — nonempty predecessors of cell i for color c.

    Paper Section 3.2, Fig. 7: neighbors j of i where `next[c][j] = i`
    (so j routes through i toward c's target) AND `entities(j) > 0`
    (so j actually has entities that want to move through i). -/
def NEPrev {n nc : Nat} (s : MCState n nc) (i : CellId2D n) (c : Fin nc) :
    List (CellId2D n) :=
  (neighbors2D i).filter (fun j =>
    decide (s.next c j = some i) && decide (s.entities j > 0))

/-- `SC(x, c)` — shared colors for color c at state x.

    Paper Section 4.4: the set of colors d ≠ c that share at least one
    entity-graph vertex with color c. -/
def sharedColors {n nc : Nat} (s : MCState n nc) (c : Fin nc) : List (Fin nc) :=
  (List.finRange nc).filter (fun d =>
    decide (d ≠ c) &&
    (List.finRange n).any (fun r =>
      (List.finRange n).any (fun col =>
        entityGraphVertexB s c (r, col) && entityGraphVertexB s d (r, col))))

/-- `lcs(x, c, i)` — lock color set at cell i for color c.

    Paper Section 3.2, Fig. 7: the set of colors that color c must
    synchronize with at cell i. These are the colors d ≠ c that also
    have i in their entity graph (shared cell at i). -/
def lcsSet {n nc : Nat} (s : MCState n nc) (c : Fin nc) (i : CellId2D n) :
    List (Fin nc) :=
  (List.finRange nc).filter (fun d =>
    decide (d ≠ c) && entityGraphVertexB s c i && entityGraphVertexB s d i)

/-- Enumerate every cell in an N×N grid. -/
private def allCells2D (n : Nat) : List (CellId2D n) :=
  (List.finRange n).flatMap (fun r => (List.finRange n).map (fun c => (r, c)))

/-- `V_E(x, c)` — vertex set of the entity graph for color c.

    Paper Section 3.3.2: cells in the entity graph, i.e. those
    satisfying `entityGraphVertex s c i`.  This list-valued form
    enumerates them over the concrete N×N grid. -/
def entityGraphVertices {n nc : Nat} (s : MCState n nc) (c : Fin nc) :
    List (CellId2D n) :=
  (allCells2D n).filter (entityGraphVertexB s c)

/-- `E_E(x, c)` — edge set of the entity graph for color c.

    Paper Section 3.3.2: directed edges (i, j) where `j = next[c][i]`
    and both i and j are entity-graph vertices. -/
def entityGraphEdges {n nc : Nat} (s : MCState n nc) (c : Fin nc) :
    List (CellId2D n × CellId2D n) :=
  (entityGraphVertices s c).filterMap (fun i =>
    match s.next c i with
    | some j => if entityGraphVertexB s c j then some (i, j) else none
    | none   => none)

/-- `V_R(x, c)` — vertex set of the routing graph for color c.

    Paper Section 3.3.1: non-faulty cells with finite `dist[c]`, i.e.
    cells that are target-connected for color c. -/
def routingGraphVertices {n nc : Nat} (s : MCState n nc) (c : Fin nc) :
    List (CellId2D n) :=
  (allCells2D n).filter (targetConnectedB s c)

/-- `E_R(x, c)` — edge set of the routing graph for color c.

    Paper Section 3.3.1: directed edges (i, j) where `j = next[c][i]`
    for some target-connected cell i. -/
def routingGraphEdges {n nc : Nat} (s : MCState n nc) (c : Fin nc) :
    List (CellId2D n × CellId2D n) :=
  (routingGraphVertices s c).filterMap (fun i =>
    match s.next c i with
    | some j => some (i, j)
    | none   => none)

/- =================================================================== -/
/- Sanity lemmas tying the boolean helpers to the Prop-valued           -/
/- predicates used in MultiColor.lean.                                  -/
/- =================================================================== -/

/-- The boolean `targetConnectedB` agrees with the `Prop` `targetConnected`. -/
theorem targetConnectedB_iff {n nc : Nat} (s : MCState n nc)
    (c : Fin nc) (i : CellId2D n) :
    targetConnectedB s c i = true ↔ targetConnected s c i := by
  unfold targetConnectedB targetConnected
  constructor
  · intro h
    rw [Bool.and_eq_true] at h
    obtain ⟨hff, hfin⟩ := h
    refine ⟨?_, ?_⟩
    · cases hff' : s.failed i with
      | false => rfl
      | true  => simp [hff'] at hff
    · cases hd : s.dist c i with
      | fin m => exact ⟨m, rfl⟩
      | inf   => simp [hd] at hfin
  · intro ⟨hff, m, hd⟩
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · simp [hff]
    · simp [hd]

/-- The boolean `entityGraphVertexB` agrees with `entityGraphVertex`. -/
theorem entityGraphVertexB_iff {n nc : Nat} (s : MCState n nc)
    (c : Fin nc) (i : CellId2D n) :
    entityGraphVertexB s c i = true ↔ entityGraphVertex s c i := by
  unfold entityGraphVertexB entityGraphVertex
  rw [Bool.and_eq_true, Bool.or_eq_true]
  constructor
  · intro ⟨hff, hor⟩
    refine ⟨?_, ?_⟩
    · cases hff' : s.failed i with
      | false => rfl
      | true  => simp [hff'] at hff
    · rcases hor with hcol | htc
      · exact Or.inl (of_decide_eq_true hcol)
      · exact Or.inr ((targetConnectedB_iff s c i).mp htc)
  · intro ⟨hff, hor⟩
    refine ⟨?_, ?_⟩
    · simp [hff]
    · rcases hor with hcol | htc
      · exact Or.inl (decide_eq_true hcol)
      · exact Or.inr ((targetConnectedB_iff s c i).mpr htc)

end CellularFlows
