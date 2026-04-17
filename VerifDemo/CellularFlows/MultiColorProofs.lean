/-
  Cellular Flows — Multi-Color Protocol Proofs
  =============================================

  This module proves invariants about the multi-color cellular flows
  transition system `multiColorTS` defined in `MultiColor.lean`.

  THEOREMS PROVED
    1. mcTargetCorrect           — Per-color target has dist = fin 0, next = none
    2. lockMutex                 — At most one color holds lock at any cell
    3. colorConsistent           — Empty cells have no color
    4. signalRespectsLock        — Signals at intersections require lock
    5. lockImpliesIntersection   — Lock requires intersection
    6. mc_signal_exclusive       — Signal exclusivity (structural)
    7. multiColor_safety         — Combined safety theorem

  Paper reference: Sections 3.2-3.3 of
    T.T. Johnson and S. Mitra, "Safe and Stabilizing Distributed Multi-Path
    Cellular Flows," Theoretical Computer Science 579 (2015) 9-32.
-/
import VerifDemo.CellularFlows.MultiColor

namespace CellularFlows

/- =================================================================== -/
/- 1. PER-COLOR TARGET CORRECTNESS                                      -/
/- =================================================================== -/

/-- The target cell for each color always has dist = fin 0 and next = none. -/
def mcTargetCorrect {n nc : Nat} (targets : Fin nc → Fin n)
    (s : MCState n nc) : Prop :=
  ∀ c : Fin nc, s.dist c (targets c) = .fin 0 ∧ s.next c (targets c) = none

theorem mcTargetCorrect_init (n nc : Nat) (targets : Fin nc → Fin n) :
    ∀ s, (multiColorTS n nc targets).init s → mcTargetCorrect targets s := by
  intro s ⟨hdist0, _, hnext, _, _, _, _⟩
  intro c
  exact ⟨hdist0 c (targets c) rfl, hnext c (targets c)⟩

theorem mcTargetCorrect_step (n nc : Nat) (targets : Fin nc → Fin n) :
    ∀ s s', mcTargetCorrect targets s →
      (multiColorTS n nc targets).next s s' → mcTargetCorrect targets s' := by
  intro s s' _ ⟨hroute_target, _, _, _, _, _, _, _⟩
  intro c
  exact hroute_target c (targets c) rfl

theorem mcTargetCorrect_inductive (n nc : Nat) (targets : Fin nc → Fin n) :
    InductiveInvariant (multiColorTS n nc targets) (mcTargetCorrect targets) :=
  ⟨mcTargetCorrect_init n nc targets, mcTargetCorrect_step n nc targets⟩

theorem mcTargetCorrect_invariant (n nc : Nat) (targets : Fin nc → Fin n) :
    Invariant (multiColorTS n nc targets) (mcTargetCorrect targets) :=
  inductive_invariant_holds (multiColorTS n nc targets)
    (mcTargetCorrect targets) (mcTargetCorrect_inductive n nc targets)

/- =================================================================== -/
/- 2. LOCK MUTUAL EXCLUSION                                             -/
/- =================================================================== -/

/-- At most one color holds lock at any cell. -/
def lockMutex {n nc : Nat} (s : MCState n nc) : Prop :=
  ∀ i : Fin n, ∀ c1 c2 : Fin nc,
    s.lock c1 i = true → s.lock c2 i = true → c1 = c2

theorem lockMutex_init (n nc : Nat) (targets : Fin nc → Fin n) :
    ∀ s, (multiColorTS n nc targets).init s → lockMutex s := by
  intro s ⟨_, _, _, _, hlock, _, _⟩
  intro i c1 c2 h1 _
  simp [hlock c1 i] at h1

theorem lockMutex_step (n nc : Nat) (targets : Fin nc → Fin n) :
    ∀ s s', lockMutex s → (multiColorTS n nc targets).next s s' → lockMutex s' := by
  intro s s' _ ⟨_, _, _, hlock_mutex, _, _, _, _⟩
  intro i c1 c2 h1 h2
  exact hlock_mutex i c1 c2 h1 h2

theorem lockMutex_inductive (n nc : Nat) (targets : Fin nc → Fin n) :
    InductiveInvariant (multiColorTS n nc targets) lockMutex :=
  ⟨lockMutex_init n nc targets, lockMutex_step n nc targets⟩

theorem lockMutex_invariant (n nc : Nat) (targets : Fin nc → Fin n) :
    Invariant (multiColorTS n nc targets) lockMutex :=
  inductive_invariant_holds (multiColorTS n nc targets)
    lockMutex (lockMutex_inductive n nc targets)

/- =================================================================== -/
/- 3. COLOR CONSISTENCY                                                  -/
/- =================================================================== -/

/-- Color consistency: empty cells have no color.
    Core structural property from Invariant 3 of the paper. -/
def colorConsistent {n nc : Nat} (s : MCState n nc) : Prop :=
  ∀ i : Fin n, s.entities i = 0 → s.color i = none

theorem colorConsistent_init (n nc : Nat) (targets : Fin nc → Fin n) :
    ∀ s, (multiColorTS n nc targets).init s → colorConsistent s := by
  intro s ⟨_, _, _, _, _, _, hcolor⟩
  exact hcolor

theorem colorConsistent_step (n nc : Nat) (targets : Fin nc → Fin n) :
    ∀ s s', colorConsistent s →
      (multiColorTS n nc targets).next s s' → colorConsistent s' := by
  intro s s' _ ⟨_, _, _, _, _, _, _, hcolor_empty⟩
  exact hcolor_empty

theorem colorConsistent_inductive (n nc : Nat) (targets : Fin nc → Fin n) :
    InductiveInvariant (multiColorTS n nc targets) colorConsistent :=
  ⟨colorConsistent_init n nc targets, colorConsistent_step n nc targets⟩

theorem colorConsistent_invariant (n nc : Nat) (targets : Fin nc → Fin n) :
    Invariant (multiColorTS n nc targets) colorConsistent :=
  inductive_invariant_holds (multiColorTS n nc targets)
    colorConsistent (colorConsistent_inductive n nc targets)

/- =================================================================== -/
/- 4. SIGNAL RESPECTS LOCK AT INTERSECTIONS (Lemma 10 discrete)         -/
/- =================================================================== -/

/-- Entities only move through intersections when the lock is held.
    Key safety property of the Lock subroutine.

    For any signaled cell i (signal i = some j), there exists a color c
    such that j's next-hop for c points to i, and either cell i has no
    intersection for c, or c holds the lock at i. -/
def signalRespectsLock {n nc : Nat} (s : MCState n nc) : Prop :=
  ∀ i j : Fin n, s.signal i = some j →
    ∃ c : Fin nc, s.next c j = some i ∧
      (s.hasIntersection c i = false ∨ s.lock c i = true)

theorem signalRespectsLock_init (n nc : Nat) (targets : Fin nc → Fin n) :
    ∀ s, (multiColorTS n nc targets).init s → signalRespectsLock s := by
  intro s ⟨_, _, _, hsig, _, _, _⟩
  intro i j hsij
  simp [hsig i] at hsij

theorem signalRespectsLock_step (n nc : Nat) (targets : Fin nc → Fin n) :
    ∀ s s', signalRespectsLock s →
      (multiColorTS n nc targets).next s s' → signalRespectsLock s' := by
  intro s s' _ ⟨_, _, _, _, hsignal, _, _, _⟩
  intro i j hsij
  rcases hsignal i with hnone | ⟨j', c, hsij', _, _, hnext_c, hlock_cond⟩
  · simp [hnone] at hsij
  · rw [hsij'] at hsij
    have hjeq : j' = j := Option.some.inj hsij
    subst hjeq
    exact ⟨c, hnext_c, hlock_cond⟩

theorem signalRespectsLock_inductive (n nc : Nat) (targets : Fin nc → Fin n) :
    InductiveInvariant (multiColorTS n nc targets) signalRespectsLock :=
  ⟨signalRespectsLock_init n nc targets, signalRespectsLock_step n nc targets⟩

theorem signalRespectsLock_invariant (n nc : Nat) (targets : Fin nc → Fin n) :
    Invariant (multiColorTS n nc targets) signalRespectsLock :=
  inductive_invariant_holds (multiColorTS n nc targets)
    signalRespectsLock (signalRespectsLock_inductive n nc targets)

/- =================================================================== -/
/- 5. LOCK IMPLIES INTERSECTION                                         -/
/- =================================================================== -/

/-- If a color holds a lock at a cell, that cell has an intersection
    for that color. Structural from the Lock phase constraint. -/
def lockImpliesIntersection {n nc : Nat} (s : MCState n nc) : Prop :=
  ∀ c : Fin nc, ∀ i : Fin n,
    s.lock c i = true → s.hasIntersection c i = true

theorem lockImpliesIntersection_init (n nc : Nat) (targets : Fin nc → Fin n) :
    ∀ s, (multiColorTS n nc targets).init s → lockImpliesIntersection s := by
  intro s ⟨_, _, _, _, hlock, _, _⟩
  intro c i hlk
  simp [hlock c i] at hlk

theorem lockImpliesIntersection_step (n nc : Nat) (targets : Fin nc → Fin n) :
    ∀ s s', lockImpliesIntersection s →
      (multiColorTS n nc targets).next s s' → lockImpliesIntersection s' := by
  intro s s' _ ⟨_, _, hlock_inter, _, _, _, _, _⟩
  intro c i hlk
  exact hlock_inter c i hlk

theorem lockImpliesIntersection_inductive (n nc : Nat) (targets : Fin nc → Fin n) :
    InductiveInvariant (multiColorTS n nc targets) lockImpliesIntersection :=
  ⟨lockImpliesIntersection_init n nc targets, lockImpliesIntersection_step n nc targets⟩

theorem lockImpliesIntersection_invariant (n nc : Nat) (targets : Fin nc → Fin n) :
    Invariant (multiColorTS n nc targets) lockImpliesIntersection :=
  inductive_invariant_holds (multiColorTS n nc targets)
    lockImpliesIntersection (lockImpliesIntersection_inductive n nc targets)

/- =================================================================== -/
/- 6. SIGNAL EXCLUSIVITY (structural)                                   -/
/- =================================================================== -/

/-- Each cell's signal field is a single Option value, so signal
    exclusivity holds trivially on ALL states. -/
theorem mc_signal_exclusive (n nc : Nat) (targets : Fin nc → Fin n) :
    Invariant (multiColorTS n nc targets) (fun s =>
      ∀ i : Fin n, ∀ j₁ j₂ : Fin n,
        s.signal i = some j₁ → s.signal i = some j₂ → j₁ = j₂) := by
  intro s _
  intro i j₁ j₂ h₁ h₂
  rw [h₁] at h₂
  exact Option.some.inj h₂

/- =================================================================== -/
/- 7. SIGNAL VALIDITY (neighbors only)                                  -/
/- =================================================================== -/

/-- Signal validity: every non-none signal points to a valid neighbor.
    Same pattern as single-color cfSignalValid. -/
def mcSignalValid {n nc : Nat} (s : MCState n nc) : Prop :=
  ∀ i j : Fin n, s.signal i = some j → areNeighbors i j

theorem mcSignalValid_init (n nc : Nat) (targets : Fin nc → Fin n) :
    ∀ s, (multiColorTS n nc targets).init s → mcSignalValid s := by
  intro s ⟨_, _, _, hsig, _, _, _⟩
  intro i j hsij
  simp [hsig i] at hsij

theorem mcSignalValid_step (n nc : Nat) (targets : Fin nc → Fin n) :
    ∀ s s', mcSignalValid s →
      (multiColorTS n nc targets).next s s' → mcSignalValid s' := by
  intro s s' _ ⟨_, _, _, _, hsignal, _, _, _⟩
  intro i j hsij
  rcases hsignal i with hnone | ⟨j', _, hsij', hneigh, _, _, _⟩
  · simp [hnone] at hsij
  · rw [hsij'] at hsij
    have hjeq : j' = j := Option.some.inj hsij
    subst hjeq
    exact hneigh

theorem mcSignalValid_inductive (n nc : Nat) (targets : Fin nc → Fin n) :
    InductiveInvariant (multiColorTS n nc targets) mcSignalValid :=
  ⟨mcSignalValid_init n nc targets, mcSignalValid_step n nc targets⟩

theorem mcSignalValid_invariant (n nc : Nat) (targets : Fin nc → Fin n) :
    Invariant (multiColorTS n nc targets) mcSignalValid :=
  inductive_invariant_holds (multiColorTS n nc targets)
    mcSignalValid (mcSignalValid_inductive n nc targets)

/- =================================================================== -/
/- 8. COMBINED SAFETY THEOREM                                           -/
/- =================================================================== -/

/-- Combined multi-color safety: all five key invariants hold simultaneously
    on every reachable state.
    - Target correctness (per-color dist/next at target)
    - Lock mutual exclusion (at most one color per cell)
    - Color consistency (empty cells have no color)
    - Signal-respects-lock (signals at intersections are gated by locks)
    - Signal validity (signals point to neighbors) -/
theorem multiColor_safety (n nc : Nat) (targets : Fin nc → Fin n) :
    Invariant (multiColorTS n nc targets) (fun s =>
      mcTargetCorrect targets s ∧
      lockMutex s ∧
      colorConsistent s ∧
      signalRespectsLock s ∧
      mcSignalValid s) := by
  intro s hreach
  exact ⟨mcTargetCorrect_invariant n nc targets s hreach,
         lockMutex_invariant n nc targets s hreach,
         colorConsistent_invariant n nc targets s hreach,
         signalRespectsLock_invariant n nc targets s hreach,
         mcSignalValid_invariant n nc targets s hreach⟩

end CellularFlows
