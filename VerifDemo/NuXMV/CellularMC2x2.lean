/-
  Cellular_mc_2x2 — auto-generated from `cellular_mc_2x2.smv`
  ===================================================

  This file was produced by `scripts/smv2lean.py` from the SMV
  source `cellular_mc_2x2.smv`. It contains:

    • Lean encodings of the SMV variable types (enums become
      `inductive`s, booleans become `Bool`, ranges become `Nat`).
    • A `State` structure holding all variables of the model.
    • A `TransitionSystem` value (`<name>TS`) capturing the SMV
      `init` and `next` clauses. Nondeterministic SMV inputs
      become existentially-quantified variables in `next`.
    • For each `INVARSPEC` in the SMV, a Lean `theorem` STUB whose
      body is `sorry`. These stubs are placeholders — the real
      proofs (where we have them) live in `VerifDemo.NuXMV.Cellular_mc_2x2Proofs`.

  Do NOT hand-edit this file: it will be overwritten by the next
  run of `smv2lean.py`. Add proofs in the corresponding
  `*Proofs.lean` file instead.
-/
import VerifDemo.TransitionSystem

structure Cellular_mc_2x2State where
  dist0_0 : Nat
  dist0_1 : Nat
  dist0_2 : Nat
  dist0_3 : Nat
  dist1_0 : Nat
  dist1_1 : Nat
  dist1_2 : Nat
  dist1_3 : Nat
  lock0_1 : Bool
  lock1_1 : Bool
  entity_0 : Bool
  entity_1 : Bool
  entity_2 : Bool
  entity_3 : Bool
  deriving DecidableEq, Repr

def Cellular_mc_2x2TS : TransitionSystem Cellular_mc_2x2State where
  init s := s.dist0_0 = 3 ∧ s.dist0_1 = 3 ∧ s.dist0_2 = 3 ∧ s.dist0_3 = 0 ∧ s.dist1_0 = 3 ∧ s.dist1_1 = 0 ∧ s.dist1_2 = 3 ∧ s.dist1_3 = 3 ∧ s.lock0_1 = false ∧ s.lock1_1 = false ∧ s.entity_0 = true ∧ s.entity_1 = false ∧ s.entity_2 = true ∧ s.entity_3 = false
  next s s' :=
    (if ((s.dist0_1 ≤ s.dist0_2) ∧ ((s.dist0_1 + 1) ≤ 3)) then s'.dist0_0 = (s.dist0_1 + 1)
    else if ((s.dist0_2 < s.dist0_1) ∧ ((s.dist0_2 + 1) ≤ 3)) then s'.dist0_0 = (s.dist0_2 + 1)
    else s'.dist0_0 = 3)
    ∧
    (if ((s.dist0_3 + 1) ≤ 3) then s'.dist0_1 = (s.dist0_3 + 1)
    else s'.dist0_1 = 3)
    ∧
    (if ((s.dist0_3 + 1) ≤ 3) then s'.dist0_2 = (s.dist0_3 + 1)
    else s'.dist0_2 = 3)
    ∧
    s'.dist0_3 = 0
    ∧
    (if ((s.dist1_1 + 1) ≤ 3) then s'.dist1_0 = (s.dist1_1 + 1)
    else s'.dist1_0 = 3)
    ∧
    s'.dist1_1 = 0
    ∧
    (if ((s.dist1_0 ≤ s.dist1_3) ∧ ((s.dist1_0 + 1) ≤ 3)) then s'.dist1_2 = (s.dist1_0 + 1)
    else if ((s.dist1_3 < s.dist1_0) ∧ ((s.dist1_3 + 1) ≤ 3)) then s'.dist1_2 = (s.dist1_3 + 1)
    else s'.dist1_2 = 3)
    ∧
    (if ((s.dist1_1 + 1) ≤ 3) then s'.dist1_3 = (s.dist1_1 + 1)
    else s'.dist1_3 = 3)
    ∧
    (if (s.lock1_1 = true) then s'.lock0_1 = false
    else if ((s.entity_0 = true) ∧ (s.dist0_1 ≤ 3)) then s'.lock0_1 = true
    else s'.lock0_1 = false)
    ∧
    (if (s.lock0_1 = true) then s'.lock1_1 = false
    else if ((s.entity_0 = true) ∧ (s.dist0_1 ≤ 3)) then s'.lock1_1 = false
    else if ((s.entity_2 = true) ∧ (s.dist1_1 = 0)) then s'.lock1_1 = true
    else s'.lock1_1 = false)
    ∧
    (if ((s.entity_0 = true) ∧ (s.lock0_1 = true)) then s'.entity_0 = false
    else s'.entity_0 = s.entity_0)
    ∧
    (if ((s.entity_0 = true) ∧ (s.lock0_1 = true)) then s'.entity_1 = true
    else if ((s.entity_1 = true) ∧ (s.lock1_1 = true)) then s'.entity_1 = false
    else s'.entity_1 = s.entity_1)
    ∧
    (if ((s.entity_2 = true) ∧ (s.lock1_1 = true)) then s'.entity_2 = false
    else s'.entity_2 = s.entity_2)
    ∧
    (if ((s.entity_1 = true) ∧ (s.lock0_1 = true)) then s'.entity_3 = true
    else s'.entity_3 = s.entity_3)

-- INVARSPEC (from cellular_mc_2x2.smv): !(((lock0_1 = TRUE) & (lock1_1 = TRUE)))
theorem Cellular_mc_2x2TS_inv1 :
    Invariant Cellular_mc_2x2TS (fun s => (¬((s.lock0_1 = true) ∧ (s.lock1_1 = true)))) := by
  -- placeholder; real proof (if any) is in VerifDemo.NuXMV.Cellular_mc_2x2Proofs.
  sorry

-- INVARSPEC (from cellular_mc_2x2.smv): (dist0_3 = 0)
theorem Cellular_mc_2x2TS_inv2 :
    Invariant Cellular_mc_2x2TS (fun s => (s.dist0_3 = 0)) := by
  -- placeholder; real proof (if any) is in VerifDemo.NuXMV.Cellular_mc_2x2Proofs.
  sorry

-- INVARSPEC (from cellular_mc_2x2.smv): (dist1_1 = 0)
theorem Cellular_mc_2x2TS_inv3 :
    Invariant Cellular_mc_2x2TS (fun s => (s.dist1_1 = 0)) := by
  -- placeholder; real proof (if any) is in VerifDemo.NuXMV.Cellular_mc_2x2Proofs.
  sorry

-- INVARSPEC (from cellular_mc_2x2.smv): (((dist0_0 <= 3) & (dist0_1 <= 3)) & (dist0_2 <= 3))
theorem Cellular_mc_2x2TS_inv4 :
    Invariant Cellular_mc_2x2TS (fun s => (((s.dist0_0 ≤ 3) ∧ (s.dist0_1 ≤ 3)) ∧ (s.dist0_2 ≤ 3))) := by
  -- placeholder; real proof (if any) is in VerifDemo.NuXMV.Cellular_mc_2x2Proofs.
  sorry

