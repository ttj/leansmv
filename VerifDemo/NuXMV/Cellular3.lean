/-
  Cellular3 — auto-generated from `cellular3.smv`
  =============================================

  This file was produced by `scripts/smv2lean.py` from the SMV
  source `cellular3.smv`. It contains:

    • Lean encodings of the SMV variable types (enums become
      `inductive`s, booleans become `Bool`, ranges become `Nat`).
    • A `State` structure holding all variables of the model.
    • A `TransitionSystem` value (`<name>TS`) capturing the SMV
      `init` and `next` clauses. Nondeterministic SMV inputs
      become existentially-quantified variables in `next`.
    • For each `INVARSPEC` in the SMV, a Lean `theorem` STUB whose
      body is `sorry`. These stubs are placeholders — the real
      proofs (where we have them) live in `VerifDemo.NuXMV.Cellular3Proofs`.

  Do NOT hand-edit this file: it will be overwritten by the next
  run of `smv2lean.py`. Add proofs in the corresponding
  `*Proofs.lean` file instead.
-/
import VerifDemo.TransitionSystem

inductive Next1Val where
  | cell0
  | none_val
  deriving DecidableEq, Repr

open Next1Val

inductive Next2Val where
  | cell1
  | none_val
  deriving DecidableEq, Repr

open Next2Val

inductive Signal0Val where
  | cell1
  | none_val
  deriving DecidableEq, Repr

open Signal0Val

inductive Signal1Val where
  | none_val
  | cell0
  | cell2
  deriving DecidableEq, Repr

open Signal1Val

inductive Signal2Val where
  | cell1
  | none_val
  deriving DecidableEq, Repr

open Signal2Val

structure Cellular3State where
  dist0 : Nat
  dist1 : Nat
  dist2 : Nat
  next1 : Next1Val
  next2 : Next2Val
  signal0 : Signal0Val
  signal1 : Signal1Val
  signal2 : Signal2Val
  entity0 : Bool
  entity1 : Bool
  entity2 : Bool
  deriving DecidableEq, Repr

def Cellular3TS : TransitionSystem Cellular3State where
  init s := s.dist0 = 0 ∧ s.dist1 = 3 ∧ s.dist2 = 3 ∧ s.next1 = .none_val ∧ s.next2 = .none_val ∧ s.signal0 = .none_val ∧ s.signal1 = .none_val ∧ s.signal2 = .none_val ∧ s.entity0 = false ∧ s.entity1 = true ∧ s.entity2 = true
  next s s' :=
    s'.dist0 = 0
    ∧
    (if ((s.dist0 ≤ s.dist2) ∧ ((s.dist0 + 1) ≤ 3)) then s'.dist1 = (s.dist0 + 1)
    else if ((s.dist0 ≤ s.dist2) ∧ ((s.dist0 + 1) > 3)) then s'.dist1 = 3
    else if ((s.dist2 < s.dist0) ∧ ((s.dist2 + 1) ≤ 3)) then s'.dist1 = (s.dist2 + 1)
    else s'.dist1 = 3)
    ∧
    (if ((s.dist1 + 1) ≤ 3) then s'.dist2 = (s.dist1 + 1)
    else s'.dist2 = 3)
    ∧
    (if (s.dist0 ≤ s.dist2) then s'.next1 = .cell0
    else s'.next1 = .cell0)
    ∧
    s'.next2 = .cell1
    ∧
    (if ((s.entity1 = true) ∧ (s.next1 = .cell0)) then s'.signal0 = .cell1
    else s'.signal0 = .none_val)
    ∧
    (if ((s.entity2 = true) ∧ (s.next2 = .cell1)) then s'.signal1 = .cell2
    else s'.signal1 = .none_val)
    ∧
    s'.signal2 = .none_val
    ∧
    s'.entity0 = false
    ∧
    (if ((s.signal0 = .cell1) ∧ (s.signal1 = .cell2)) then s'.entity1 = true
    else if (s.signal0 = .cell1) then s'.entity1 = false
    else if (s.signal1 = .cell2) then s'.entity1 = true
    else s'.entity1 = s.entity1)
    ∧
    (if (s.signal1 = .cell2) then s'.entity2 = false
    else s'.entity2 = s.entity2)

-- INVARSPEC (from cellular3.smv): !(((signal0 = cell1) & (signal1 = cell0)))
theorem Cellular3TS_inv1 :
    Invariant Cellular3TS (fun s => (¬((s.signal0 = .cell1) ∧ (s.signal1 = .cell0)))) := by
  -- placeholder; real proof (if any) is in VerifDemo.NuXMV.Cellular3Proofs.
  sorry

-- INVARSPEC (from cellular3.smv): (dist0 = 0)
theorem Cellular3TS_inv2 :
    Invariant Cellular3TS (fun s => (s.dist0 = 0)) := by
  -- placeholder; real proof (if any) is in VerifDemo.NuXMV.Cellular3Proofs.
  sorry

-- INVARSPEC (from cellular3.smv): (dist1 <= 3)
theorem Cellular3TS_inv3 :
    Invariant Cellular3TS (fun s => (s.dist1 ≤ 3)) := by
  -- placeholder; real proof (if any) is in VerifDemo.NuXMV.Cellular3Proofs.
  sorry

