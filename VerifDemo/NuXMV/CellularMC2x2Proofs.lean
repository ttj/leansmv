/-
  Proofs of Invariant Properties for the 2x2 Multi-Color Cellular Flows Model
  ============================================================================

  WHAT — The auto-generated `CellularMC2x2.lean` defines a NuXMV-style
         transition system modeling a 2x2 grid (flattened to 4 cells)
         with two colors whose paths intersect at cell 1. Here we prove
         four INVARSPEC properties:
           inv1 :  ¬(lock0_1 = true ∧ lock1_1 = true)   -- LOCK MUTEX
           inv2 :  dist0_3 = 0                           -- color-0 target
           inv3 :  dist1_1 = 0                           -- color-1 target
           inv4 :  dist0_0 ≤ 3 ∧ dist0_1 ≤ 3 ∧ dist0_2 ≤ 3 -- distance bounds

  HOW  — Priority-based lock arbitration in the SMV model ensures color 0
         has priority: lock1_1 is set to true only when color 0 is NOT
         demanding the lock. Thus lock mutual exclusion follows directly
         from the structure of next(lock0_1) and next(lock1_1). We bundle
         this with the target-distance and distance-bound conjuncts into a
         strengthened inductive invariant.

  PROOF SHAPE
    1. mc2x2Inv_init   — base case: init gives all literal values.
    2. mc2x2Inv_step   — step preservation: each conjunct is decided by
                         split + omega (or inspection of lock branches).
    3. Bundle into InductiveInvariant, derive each INVARSPEC via
       invariant_strengthening.
-/
import VerifDemo.TransitionSystem
import VerifDemo.NuXMV.CellularMC2x2

/-- The strengthened inductive invariant. Bundles:
    • lock mutual exclusion at cell 1
    • target distances pinned at 0
    • all eight distances bounded by 3 -/
def mc2x2Inv (s : Cellular_mc_2x2State) : Prop :=
  (¬ (s.lock0_1 = true ∧ s.lock1_1 = true)) ∧
  s.dist0_3 = 0 ∧ s.dist1_1 = 0 ∧
  s.dist0_0 ≤ 3 ∧ s.dist0_1 ≤ 3 ∧ s.dist0_2 ≤ 3 ∧ s.dist0_3 ≤ 3 ∧
  s.dist1_0 ≤ 3 ∧ s.dist1_1 ≤ 3 ∧ s.dist1_2 ≤ 3 ∧ s.dist1_3 ≤ 3

/-- BASE CASE: every initial state satisfies the invariant.
    Init sets all locks to false and all distances to either 0 or 3. -/
theorem mc2x2Inv_init :
    ∀ s, Cellular_mc_2x2TS.init s → mc2x2Inv s := by
  intro s h
  obtain ⟨hd00, hd01, hd02, hd03, hd10, hd11, hd12, hd13,
          hL01, hL11, _, _, _, _⟩ := h
  refine ⟨?_, hd03, hd11, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ⟨hA, _⟩
    rw [hL01] at hA
    exact absurd hA (by decide)
  all_goals omega

/-- INDUCTIVE STEP: the invariant is preserved by every transition.
    • Lock mutex: in the branches where `s'.lock0_1 = true` and
      `s'.lock1_1 = true` simultaneously, the two guards are
      `entity_0 = true ∧ dist0_1 ≤ 3` (required for lock0_1) and
      its negation (required for lock1_1), which is a contradiction.
    • Target distances: direct equalities in the next relation.
    • Distance bounds: each case-split guard ensures the bound. -/
theorem mc2x2Inv_step :
    ∀ s s', mc2x2Inv s → Cellular_mc_2x2TS.next s s' → mc2x2Inv s' := by
  intro s s' _
  intro ⟨hd00', hd01', hd02', hd03', hd10', hd11', hd12', hd13',
         hL01', hL11', _, _, _, _⟩
  refine ⟨?_, hd03', hd11', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Lock mutex.
    intro ⟨hA, hB⟩
    -- Analyze how lock0_1' got to be true.
    split at hL01'
    · -- branch: s.lock1_1 = true -> s'.lock0_1 = false
      rw [hL01'] at hA; exact absurd hA (by decide)
    · split at hL01'
      · -- branch: entity_0 ∧ dist0_1 ≤ 3 -> s'.lock0_1 = true
        rename_i _ hguard0
        -- hguard0 is in scope; use it (along with the outer guard
        -- ¬(s.lock1_1 = true)) to simplify hL11'. The next(lock1_1) logic
        -- forces s'.lock1_1 = false whenever entity_0 ∧ dist0_1 ≤ 3 holds.
        simp [hguard0] at hL11'
        -- hL11' is now `s'.lock1_1 = false` or similar, contradicting hB.
        rw [hL11'] at hB; exact absurd hB (by decide)
      · rw [hL01'] at hA; exact absurd hA (by decide)
  all_goals (first | (split at hd00' <;> (try split at hd00') <;> omega)
                   | (split at hd01' <;> omega)
                   | (split at hd02' <;> omega)
                   | (split at hd10' <;> omega)
                   | (split at hd12' <;> (try split at hd12') <;> omega)
                   | (split at hd13' <;> omega)
                   | omega)

theorem mc2x2Inv_inductive : InductiveInvariant Cellular_mc_2x2TS mc2x2Inv :=
  ⟨mc2x2Inv_init, mc2x2Inv_step⟩

/-- INVARSPEC 1: lock mutual exclusion at cell 1. -/
theorem Cellular_mc_2x2TS_inv1_proved :
    Invariant Cellular_mc_2x2TS
      (fun s => (¬((s.lock0_1 = true) ∧ (s.lock1_1 = true)))) :=
  invariant_strengthening Cellular_mc_2x2TS mc2x2Inv _ mc2x2Inv_inductive
    (fun _ h => h.1)

/-- INVARSPEC 2: target of color 0 is always at dist 0. -/
theorem Cellular_mc_2x2TS_inv2_proved :
    Invariant Cellular_mc_2x2TS (fun s => s.dist0_3 = 0) :=
  invariant_strengthening Cellular_mc_2x2TS mc2x2Inv _ mc2x2Inv_inductive
    (fun _ h => h.2.1)

/-- INVARSPEC 3: target of color 1 is always at dist 0. -/
theorem Cellular_mc_2x2TS_inv3_proved :
    Invariant Cellular_mc_2x2TS (fun s => s.dist1_1 = 0) :=
  invariant_strengthening Cellular_mc_2x2TS mc2x2Inv _ mc2x2Inv_inductive
    (fun _ h => h.2.2.1)

/-- INVARSPEC 4: all color-0 distance variables bounded by 3. -/
theorem Cellular_mc_2x2TS_inv4_proved :
    Invariant Cellular_mc_2x2TS
      (fun s => ((s.dist0_0 ≤ 3) ∧ (s.dist0_1 ≤ 3)) ∧ (s.dist0_2 ≤ 3)) :=
  invariant_strengthening Cellular_mc_2x2TS mc2x2Inv _ mc2x2Inv_inductive
    (fun _ h => ⟨⟨h.2.2.2.1, h.2.2.2.2.1⟩, h.2.2.2.2.2.1⟩)
