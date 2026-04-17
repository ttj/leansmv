/-
  Cellular Flows — Multi-Color Protocol Proofs (2D Grid)
  ======================================================

  This module proves invariants about the multi-color cellular flows
  transition system `multiColorTS` defined in `MultiColor.lean`. The
  system models the Route + Path + Lock + Signal + Move protocol on an
  N×N 2D grid with nc colors.

  THEOREMS PROVED
    1. mcTargetCorrect        — Per-color target has dist = fin 0, next = none
    2. lockMutex              — At most one color holds lock at any cell
    3. lockRequiresIntersection — lock ⟹ needsLock ⟹ pint (chain)
    4. signalRespectsLock      — Signals at intersections require lock held
    5. colorConsistent         — Empty cells have no color
    6. colorPreserved          — Arriving entities get source's color
    7. signalExclusive         — Each cell signals at most one predecessor
    8. mcSignalValid             — Signals point to 2D neighbors
    9. noFailureChange         — Failures don't change
   10. multiColor_safety       — Conjunction of all above

  PROOF SHAPE
    Each property follows the NMutex pattern:
      1. Define the invariant predicate
      2. Prove init preservation
      3. Prove step preservation
      4. Bundle into InductiveInvariant
      5. Lift to Invariant via inductive_invariant_holds

  Paper reference: Sections 3.2-4.4 of
    T.T. Johnson and S. Mitra, "Safe and Stabilizing Distributed Multi-Path
    Cellular Flows," Theoretical Computer Science 579 (2015) 9-32.
    Lemma 10 (lock safety), Lemma 11 (signal correctness).
-/
import VerifDemo.CellularFlows.MultiColor

set_option autoImplicit false

namespace CellularFlows

/- =================================================================== -/
/- 1. PER-COLOR TARGET CORRECTNESS                                      -/
/- =================================================================== -/

/-- The target cell for each color always has dist = fin 0 and next = none.
    Paper ref: Route subroutine (Fig. 8), target initialization. -/
def mcTargetCorrect {n nc : Nat} (targets : Fin nc → CellId2D n)
    (s : MCState n nc) : Prop :=
  ∀ c : Fin nc, s.dist c (targets c) = .fin 0 ∧ s.next c (targets c) = none

theorem mcTargetCorrect_init (n nc : Nat) (targets : Fin nc → CellId2D n) :
    ∀ s, (multiColorTS n nc targets).init s → mcTargetCorrect targets s := by
  intro s ⟨hdist0, _, hnext, _, _, _, _, _, _, _⟩
  intro c
  exact ⟨hdist0 c (targets c) rfl, hnext c (targets c)⟩

theorem mcTargetCorrect_step (n nc : Nat) (targets : Fin nc → CellId2D n) :
    ∀ s s', mcTargetCorrect targets s →
      (multiColorTS n nc targets).next s s' → mcTargetCorrect targets s' := by
  intro s s' _ ⟨hroute_target, _, _, _, _, _, _, _, _, _, _, _, _⟩
  intro c
  exact hroute_target c (targets c) rfl

theorem mcTargetCorrect_inductive (n nc : Nat) (targets : Fin nc → CellId2D n) :
    InductiveInvariant (multiColorTS n nc targets) (mcTargetCorrect targets) :=
  ⟨mcTargetCorrect_init n nc targets, mcTargetCorrect_step n nc targets⟩

theorem mcTargetCorrect_invariant (n nc : Nat) (targets : Fin nc → CellId2D n) :
    Invariant (multiColorTS n nc targets) (mcTargetCorrect targets) :=
  inductive_invariant_holds (multiColorTS n nc targets)
    (mcTargetCorrect targets) (mcTargetCorrect_inductive n nc targets)

/- =================================================================== -/
/- 2. LOCK MUTUAL EXCLUSION                                             -/
/- =================================================================== -/

/-- At most one color holds lock at any cell.
    Paper ref: Fig. 9, lines 8-17 (Lock subroutine mutual exclusion). -/
def lockMutex {n nc : Nat} (s : MCState n nc) : Prop :=
  ∀ i : CellId2D n, ∀ c1 c2 : Fin nc,
    s.lock c1 i = true → s.lock c2 i = true → c1 = c2

theorem lockMutex_init (n nc : Nat) (targets : Fin nc → CellId2D n) :
    ∀ s, (multiColorTS n nc targets).init s → lockMutex s := by
  intro s ⟨_, _, _, _, hlock, _, _, _, _, _⟩
  intro i c1 _ h1 _
  simp [hlock c1 i] at h1

theorem lockMutex_step (n nc : Nat) (targets : Fin nc → CellId2D n) :
    ∀ s s', lockMutex s → (multiColorTS n nc targets).next s s' → lockMutex s' := by
  intro s s' _ ⟨_, _, _, _, _, _, hlock_mutex, _, _, _, _, _, _⟩
  intro i c1 c2 h1 h2
  exact hlock_mutex i c1 c2 h1 h2

theorem lockMutex_inductive (n nc : Nat) (targets : Fin nc → CellId2D n) :
    InductiveInvariant (multiColorTS n nc targets) lockMutex :=
  ⟨lockMutex_init n nc targets, lockMutex_step n nc targets⟩

theorem lockMutex_invariant (n nc : Nat) (targets : Fin nc → CellId2D n) :
    Invariant (multiColorTS n nc targets) lockMutex :=
  inductive_invariant_holds (multiColorTS n nc targets)
    lockMutex (lockMutex_inductive n nc targets)

/- =================================================================== -/
/- 3. LOCK REQUIRES INTERSECTION (chain: lock ⟹ needsLock ⟹ pint)     -/
/- =================================================================== -/

/-- If a color holds a lock at a cell, that cell needs a lock for that
    color (needsLock = true), which in turn requires a path intersection
    (pint = true). Paper ref: Fig. 9, Lock subroutine precondition. -/
def lockRequiresIntersection {n nc : Nat} (s : MCState n nc) : Prop :=
  (∀ c : Fin nc, ∀ i : CellId2D n,
    s.lock c i = true → s.needsLock c i = true) ∧
  (∀ c : Fin nc, ∀ i : CellId2D n,
    s.needsLock c i = true → s.pint c i = true)

theorem lockRequiresIntersection_init (n nc : Nat) (targets : Fin nc → CellId2D n) :
    ∀ s, (multiColorTS n nc targets).init s → lockRequiresIntersection s := by
  intro s ⟨_, _, _, _, hlock, _, hneedsLock, _, _, _⟩
  refine ⟨?_, ?_⟩
  · intro c i hlk
    simp [hlock c i] at hlk
  · intro c i hnl
    simp [hneedsLock c i] at hnl

theorem lockRequiresIntersection_step (n nc : Nat) (targets : Fin nc → CellId2D n) :
    ∀ s s', lockRequiresIntersection s →
      (multiColorTS n nc targets).next s s' → lockRequiresIntersection s' := by
  intro s s' _ ⟨_, _, _, _, hnl_pint, hlock_nl, _, _, _, _, _, _, _⟩
  refine ⟨?_, ?_⟩
  · intro c i hlk
    exact hlock_nl c i hlk
  · intro c i hnl
    exact hnl_pint c i hnl

theorem lockRequiresIntersection_inductive (n nc : Nat) (targets : Fin nc → CellId2D n) :
    InductiveInvariant (multiColorTS n nc targets) lockRequiresIntersection :=
  ⟨lockRequiresIntersection_init n nc targets, lockRequiresIntersection_step n nc targets⟩

theorem lockRequiresIntersection_invariant (n nc : Nat) (targets : Fin nc → CellId2D n) :
    Invariant (multiColorTS n nc targets) lockRequiresIntersection :=
  inductive_invariant_holds (multiColorTS n nc targets)
    lockRequiresIntersection (lockRequiresIntersection_inductive n nc targets)

/- =================================================================== -/
/- 4. SIGNAL RESPECTS LOCK AT INTERSECTIONS (Lemma 10 discrete)         -/
/- =================================================================== -/

/-- Entities only move through intersection cells when the lock is held.
    Key safety property of the Lock subroutine (Lemma 10).

    For any signaled cell i (signal i = some j), there exists a color c
    such that j's next-hop for c points to i, and either cell i has no
    intersection for c (needsLock = false), or c holds the lock at i. -/
def signalRespectsLock {n nc : Nat} (s : MCState n nc) : Prop :=
  ∀ i j : CellId2D n, s.signal i = some j →
    ∃ c : Fin nc, s.next c j = some i ∧
      (s.needsLock c i = false ∨ s.lock c i = true)

theorem signalRespectsLock_init (n nc : Nat) (targets : Fin nc → CellId2D n) :
    ∀ s, (multiColorTS n nc targets).init s → signalRespectsLock s := by
  intro s ⟨_, _, _, hsig, _, _, _, _, _, _⟩
  intro i j hsij
  simp [hsig i] at hsij

theorem signalRespectsLock_step (n nc : Nat) (targets : Fin nc → CellId2D n) :
    ∀ s s', signalRespectsLock s →
      (multiColorTS n nc targets).next s s' → signalRespectsLock s' := by
  intro s s' _ ⟨_, _, _, _, _, _, _, hsignal, _, _, _, _, _⟩
  intro i j hsij
  rcases hsignal i with hnone | ⟨j', c, hsij', _, _, _, hnext_c, hlock_cond, _⟩
  · simp [hnone] at hsij
  · rw [hsij'] at hsij
    have hjeq : j' = j := Option.some.inj hsij
    subst hjeq
    exact ⟨c, hnext_c, hlock_cond⟩

theorem signalRespectsLock_inductive (n nc : Nat) (targets : Fin nc → CellId2D n) :
    InductiveInvariant (multiColorTS n nc targets) signalRespectsLock :=
  ⟨signalRespectsLock_init n nc targets, signalRespectsLock_step n nc targets⟩

theorem signalRespectsLock_invariant (n nc : Nat) (targets : Fin nc → CellId2D n) :
    Invariant (multiColorTS n nc targets) signalRespectsLock :=
  inductive_invariant_holds (multiColorTS n nc targets)
    signalRespectsLock (signalRespectsLock_inductive n nc targets)

/- =================================================================== -/
/- 5. COLOR CONSISTENCY                                                  -/
/- =================================================================== -/

/-- Color consistency: empty cells have no color.
    Core structural property from Invariant 3 of the paper. -/
def colorConsistent {n nc : Nat} (s : MCState n nc) : Prop :=
  ∀ i : CellId2D n, s.entities i = 0 → s.color i = none

theorem colorConsistent_init (n nc : Nat) (targets : Fin nc → CellId2D n) :
    ∀ s, (multiColorTS n nc targets).init s → colorConsistent s := by
  intro s ⟨_, _, _, _, _, _, _, _, hcolor, _⟩
  exact hcolor

theorem colorConsistent_step (n nc : Nat) (targets : Fin nc → CellId2D n) :
    ∀ s s', colorConsistent s →
      (multiColorTS n nc targets).next s s' → colorConsistent s' := by
  intro s s' _ ⟨_, _, _, _, _, _, _, _, _, _, _, hcolor_empty, _, _⟩
  exact hcolor_empty

theorem colorConsistent_inductive (n nc : Nat) (targets : Fin nc → CellId2D n) :
    InductiveInvariant (multiColorTS n nc targets) colorConsistent :=
  ⟨colorConsistent_init n nc targets, colorConsistent_step n nc targets⟩

theorem colorConsistent_invariant (n nc : Nat) (targets : Fin nc → CellId2D n) :
    Invariant (multiColorTS n nc targets) colorConsistent :=
  inductive_invariant_holds (multiColorTS n nc targets)
    colorConsistent (colorConsistent_inductive n nc targets)

/- =================================================================== -/
/- 6. COLOR PRESERVED (arriving entities get source's color)             -/
/- =================================================================== -/

/-- Color preservation (step-level): the transition relation ensures that
    when entities arrive at a cell via signal, the receiving cell's color
    in the post-state matches the sending cell's color in the pre-state.
    This is a per-step property, not a state predicate.
    Paper ref: Invariant 3 (single color per cell). -/
theorem colorPreserved_step (n nc : Nat) (targets : Fin nc → CellId2D n) :
    ∀ s s', (multiColorTS n nc targets).next s s' →
      ∀ i j : CellId2D n, s'.signal i = some j → s'.entities i > 0 →
        s'.color i = s.color j := by
  intro s s' ⟨_, _, _, _, _, _, _, _, _, _, _, _, hcolor_arr, _⟩
  exact hcolor_arr

/-- Color preservation as a state invariant: signals only come from
    color-compatible neighbors. For any signaled cell i with entities,
    there exists a color c such that j has color c and the signal
    respects color compatibility (i is empty or has same color).
    This is the discrete analogue of Invariant 3 from the paper. -/
def colorPreserved {n nc : Nat} (s : MCState n nc) : Prop :=
  ∀ i j : CellId2D n, s.signal i = some j →
    ∃ c : Fin nc, s.color j = some c ∧
      (s.entities i = 0 ∨ s.color i = some c)

theorem colorPreserved_init (n nc : Nat) (targets : Fin nc → CellId2D n) :
    ∀ s, (multiColorTS n nc targets).init s → colorPreserved s := by
  intro s ⟨_, _, _, hsig, _, _, _, _, _, _⟩
  intro i j hsij
  simp [hsig i] at hsij

theorem colorPreserved_step_ind (n nc : Nat) (targets : Fin nc → CellId2D n) :
    ∀ s s', colorPreserved s →
      (multiColorTS n nc targets).next s s' → colorPreserved s' := by
  intro s s' _ ⟨_, _, _, _, _, _, _, hsignal, _, _, _, _, _, _⟩
  intro i j hsij
  rcases hsignal i with hnone | ⟨j', c, hsij', _, _, hcolor_j', _, _, hcompat⟩
  · simp [hnone] at hsij
  · rw [hsij'] at hsij
    have hjeq : j' = j := Option.some.inj hsij
    subst hjeq
    exact ⟨c, hcolor_j', hcompat⟩

theorem colorPreserved_inductive (n nc : Nat) (targets : Fin nc → CellId2D n) :
    InductiveInvariant (multiColorTS n nc targets) colorPreserved :=
  ⟨colorPreserved_init n nc targets, colorPreserved_step_ind n nc targets⟩

theorem colorPreserved_invariant (n nc : Nat) (targets : Fin nc → CellId2D n) :
    Invariant (multiColorTS n nc targets) colorPreserved :=
  inductive_invariant_holds (multiColorTS n nc targets)
    colorPreserved (colorPreserved_inductive n nc targets)

/- =================================================================== -/
/- 7. SIGNAL EXCLUSIVITY (structural — trivially true)                  -/
/- =================================================================== -/

/-- Each cell's signal field is a single Option value, so signal
    exclusivity holds trivially on ALL states via Option.some injectivity.
    Paper ref: Signal subroutine (Fig. 10), one signal per cell. -/
theorem signalExclusive (n nc : Nat) (targets : Fin nc → CellId2D n) :
    Invariant (multiColorTS n nc targets) (fun s =>
      ∀ i : CellId2D n, ∀ j₁ j₂ : CellId2D n,
        s.signal i = some j₁ → s.signal i = some j₂ → j₁ = j₂) := by
  intro s _
  intro i j₁ j₂ h₁ h₂
  rw [h₁] at h₂
  exact Option.some.inj h₂

/- =================================================================== -/
/- 8. SIGNAL VALIDITY (signals point to 2D neighbors)                   -/
/- =================================================================== -/

/-- Signal validity: every non-none signal points to a valid 2D neighbor.
    Paper ref: Signal subroutine (Fig. 10), neighbor constraint. -/
def mcSignalValid {n nc : Nat} (s : MCState n nc) : Prop :=
  ∀ i j : CellId2D n, s.signal i = some j → areNeighbors2D i j

theorem mcSignalValid_init (n nc : Nat) (targets : Fin nc → CellId2D n) :
    ∀ s, (multiColorTS n nc targets).init s → mcSignalValid s := by
  intro s ⟨_, _, _, hsig, _, _, _, _, _, _⟩
  intro i j hsij
  simp [hsig i] at hsij

theorem mcSignalValid_step (n nc : Nat) (targets : Fin nc → CellId2D n) :
    ∀ s s', mcSignalValid s →
      (multiColorTS n nc targets).next s s' → mcSignalValid s' := by
  intro s s' _ ⟨_, _, _, _, _, _, _, hsignal, _, _, _, _, _, _⟩
  intro i j hsij
  rcases hsignal i with hnone | ⟨j', _, hsij', hneigh, _, _, _, _, _⟩
  · simp [hnone] at hsij
  · rw [hsij'] at hsij
    have hjeq : j' = j := Option.some.inj hsij
    subst hjeq
    exact hneigh

theorem mcSignalValid_inductive (n nc : Nat) (targets : Fin nc → CellId2D n) :
    InductiveInvariant (multiColorTS n nc targets) mcSignalValid :=
  ⟨mcSignalValid_init n nc targets, mcSignalValid_step n nc targets⟩

theorem mcSignalValid_invariant (n nc : Nat) (targets : Fin nc → CellId2D n) :
    Invariant (multiColorTS n nc targets) mcSignalValid :=
  inductive_invariant_holds (multiColorTS n nc targets)
    mcSignalValid (mcSignalValid_inductive n nc targets)

/- =================================================================== -/
/- 9. NO FAILURE CHANGE                                                  -/
/- =================================================================== -/

/-- Failures don't change: the failure state of each cell is constant
    across transitions in this simplified model. -/
def noFailureChange {n nc : Nat} (s₀ : MCState n nc) (s : MCState n nc) : Prop :=
  ∀ i : CellId2D n, s.failed i = s₀.failed i

/-- Failures are initially all false and remain unchanged.
    We prove the weaker property that failures don't change per step. -/
theorem noFailureChange_step (n nc : Nat) (targets : Fin nc → CellId2D n) :
    ∀ s s', (multiColorTS n nc targets).next s s' →
      ∀ i : CellId2D n, s'.failed i = s.failed i := by
  intro s s' ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hfail⟩
  exact hfail

/-- As an inductive invariant: failures are initially false and never change. -/
def failuresInitFalse {n nc : Nat} (s : MCState n nc) : Prop :=
  ∀ i : CellId2D n, s.failed i = false

theorem failuresInitFalse_init (n nc : Nat) (targets : Fin nc → CellId2D n) :
    ∀ s, (multiColorTS n nc targets).init s → failuresInitFalse s := by
  intro s ⟨_, _, _, _, _, _, _, _, _, hfail⟩
  exact hfail

theorem failuresInitFalse_step (n nc : Nat) (targets : Fin nc → CellId2D n) :
    ∀ s s', failuresInitFalse s →
      (multiColorTS n nc targets).next s s' → failuresInitFalse s' := by
  intro s s' hpre ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hfail⟩
  intro i
  rw [hfail i]
  exact hpre i

theorem failuresInitFalse_inductive (n nc : Nat) (targets : Fin nc → CellId2D n) :
    InductiveInvariant (multiColorTS n nc targets) failuresInitFalse :=
  ⟨failuresInitFalse_init n nc targets, failuresInitFalse_step n nc targets⟩

theorem failuresInitFalse_invariant (n nc : Nat) (targets : Fin nc → CellId2D n) :
    Invariant (multiColorTS n nc targets) failuresInitFalse :=
  inductive_invariant_holds (multiColorTS n nc targets)
    failuresInitFalse (failuresInitFalse_inductive n nc targets)

/- =================================================================== -/
/- 10. COMBINED SAFETY THEOREM                                          -/
/- =================================================================== -/

/-- Combined multi-color safety: all key invariants hold simultaneously
    on every reachable state of the 2D multi-color protocol.
    - Target correctness (per-color dist/next at target)
    - Lock mutual exclusion (at most one color per cell)
    - Lock-intersection chain (lock ⟹ needsLock ⟹ pint)
    - Signal-respects-lock (signals at intersections gated by locks)
    - Color consistency (empty cells have no color)
    - Color preservation (arriving entities get source's color)
    - Signal exclusivity (each cell signals at most one predecessor)
    - Signal validity (signals point to 2D neighbors)
    - Failures don't change

    Paper ref: Lemma 10, Lemma 11 (safety of lock and signal). -/
theorem multiColor_safety (n nc : Nat) (targets : Fin nc → CellId2D n) :
    Invariant (multiColorTS n nc targets) (fun s =>
      mcTargetCorrect targets s ∧
      lockMutex s ∧
      lockRequiresIntersection s ∧
      signalRespectsLock s ∧
      colorConsistent s ∧
      colorPreserved s ∧
      mcSignalValid s ∧
      failuresInitFalse s) := by
  intro s hreach
  exact ⟨mcTargetCorrect_invariant n nc targets s hreach,
         lockMutex_invariant n nc targets s hreach,
         lockRequiresIntersection_invariant n nc targets s hreach,
         signalRespectsLock_invariant n nc targets s hreach,
         colorConsistent_invariant n nc targets s hreach,
         colorPreserved_invariant n nc targets s hreach,
         mcSignalValid_invariant n nc targets s hreach,
         failuresInitFalse_invariant n nc targets s hreach⟩

end CellularFlows
