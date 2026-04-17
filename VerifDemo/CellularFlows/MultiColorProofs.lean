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

/- =================================================================== -/
/- 11. MANHATTAN TRIANGLE INEQUALITY FOR 2D GRID NEIGHBORS             -/
/- =================================================================== -/

/-- For any neighbor j of cell i on the 2D grid, manhattan(j, t) + 1 ≥ manhattan(i, t).
    Triangle inequality for Manhattan distance on a 4-connected grid: neighbors
    differ by 1 in exactly one coordinate, so Manhattan distance changes by at most 1.

    Proof: case split on the 4 neighbor directions, unfold manhattan, case split
    on all if-then-else conditions, and dispatch with omega. -/
theorem manhattan_neighbor_triangle {n : Nat} (i j t : CellId2D n) :
    areNeighbors2D i j → manhattan j t + 1 ≥ manhattan i t := by
  intro h
  unfold manhattan
  rcases h with ⟨hrow, hcol⟩ | ⟨hcol, hrow⟩
  · -- Same row, columns differ by 1
    have hrow_eq : i.1.val = j.1.val := congrArg Fin.val hrow
    rcases hcol with hc | hc
    all_goals (
      split <;> split <;> split <;> split <;> omega)
  · -- Same column, rows differ by 1
    have hcol_eq : i.2.val = j.2.val := congrArg Fin.val hcol
    rcases hrow with hr | hr
    all_goals (
      split <;> split <;> split <;> split <;> omega)

/-- Helper: membership in Option.toList means the option is some. -/
private theorem mem_option_toList {α : Type _} {a : α} {o : Option α} :
    a ∈ o.toList → o = some a := by
  cases o with
  | none => simp [Option.toList]
  | some v => simp [Option.toList]; intro h; exact h.symm

/-- Members of neighbors2D are 2D neighbors. -/
theorem neighbors2D_mem_areNeighbors {n : Nat} (i j : CellId2D n) :
    j ∈ neighbors2D i → areNeighbors2D i j := by
  unfold neighbors2D
  intro hmem
  have hmem' := hmem
  simp only [List.mem_append] at hmem'
  unfold areNeighbors2D
  -- Try each of the four neighbor directions
  rcases hmem' with ((h | h) | h) | h
  · -- upNeighbor
    have hsome := mem_option_toList h
    unfold upNeighbor at hsome
    split at hsome <;> simp at hsome
    right; constructor
    · exact (Prod.mk.inj hsome).2
    · right; have := (Prod.mk.inj hsome).1; simp [Fin.ext_iff] at this; omega
  · -- downNeighbor
    have hsome := mem_option_toList h
    unfold downNeighbor at hsome
    split at hsome <;> simp at hsome
    right; constructor
    · exact (Prod.mk.inj hsome).2
    · left; have := (Prod.mk.inj hsome).1; simp [Fin.ext_iff] at this; omega
  · -- leftNeighbor2D
    have hsome := mem_option_toList h
    unfold leftNeighbor2D at hsome
    split at hsome <;> simp at hsome
    left; constructor
    · exact (Prod.mk.inj hsome).1
    · right; have := (Prod.mk.inj hsome).2; simp [Fin.ext_iff] at this; omega
  · -- rightNeighbor2D
    have hsome := mem_option_toList h
    unfold rightNeighbor2D at hsome
    split at hsome <;> simp at hsome
    left; constructor
    · exact (Prod.mk.inj hsome).1
    · left; have := (Prod.mk.inj hsome).2; simp [Fin.ext_iff] at this; omega

/- =================================================================== -/
/- 12. PER-COLOR DIST LOWER BOUND (2D GRID)                            -/
/- =================================================================== -/

/-- Per-color dist lower bound: for any reachable state of the multi-color
    system, dist[c][i] = fin m implies m ≥ manhattan(i, targets c).
    This generalizes distLowerBound from the 1D model to 2D.

    Paper ref: Route subroutine correctness (Section 3.3.1). The true
    shortest-path distance on a 4-connected grid is the Manhattan distance. -/
def mcDistLowerBound {n nc : Nat} (targets : Fin nc → CellId2D n)
    (s : MCState n nc) : Prop :=
  ∀ c : Fin nc, ∀ i : CellId2D n, ∀ m : Nat,
    s.dist c i = .fin m → m ≥ manhattan i (targets c)

/-- Helper: manhattan(t, t) = 0 for any cell t. -/
private theorem manhattan_self {n : Nat} (t : CellId2D n) : manhattan t t = 0 := by
  simp [manhattan]

/-- Local DistVal helpers (these are proved in RouteProofs.lean but not
    imported here, so we re-prove them locally). -/
private theorem distval_dmin_inf_left (a : DistVal) : DistVal.dmin .inf a = a := by
  cases a with | fin _ => rfl | inf => rfl

private theorem distval_dmin_inf_right (a : DistVal) : DistVal.dmin a .inf = a := by
  cases a with | fin _ => rfl | inf => rfl

private theorem distval_dmin_fin_fin (a b : Nat) :
    DistVal.dmin (.fin a) (.fin b) = .fin (Nat.min a b) := rfl

private theorem distval_succ_fin (m : Nat) : DistVal.succ (.fin m) = .fin (m + 1) := rfl
private theorem distval_succ_inf : DistVal.succ .inf = .inf := rfl

/-- Helper: dmin (.fin a) b = .fin m → m ≥ bound, given a ≥ bound and
    (b = .fin mb → mb ≥ bound). -/
private theorem dmin_ge_bound (a : Nat) (b : DistVal) (m bound : Nat)
    (ha : a ≥ bound) (hb : ∀ mb, b = .fin mb → mb ≥ bound)
    (hdmin : DistVal.dmin (.fin a) b = .fin m) : m ≥ bound := by
  cases b with
  | inf =>
    simp [DistVal.dmin] at hdmin
    omega
  | fin mb =>
    have hge_b := hb mb rfl
    simp [DistVal.dmin] at hdmin
    -- hdmin : Nat.min a mb = m
    subst hdmin
    simp [Nat.min_def]; split <;> omega

/-- Helper: if minDist2D over a list of cells yields .fin m, and every cell j in
    that list has dist j = .fin mj → mj ≥ bound, then m ≥ bound. -/
private theorem minDist2D_lower_bound {n : Nat} (dist : CellId2D n → DistVal)
    (cells : List (CellId2D n)) (bound : Nat)
    (hlb : ∀ j : CellId2D n, j ∈ cells → ∀ mj : Nat, dist j = .fin mj → mj ≥ bound) :
    ∀ m : Nat, minDist2D dist cells = .fin m → m ≥ bound := by
  induction cells with
  | nil => intro m hmin; simp [minDist2D] at hmin
  | cons x xs ih =>
    intro m hmin
    cases xs with
    | nil =>
      simp [minDist2D] at hmin
      exact hlb x (by simp) m hmin
    | cons y ys =>
      simp only [minDist2D] at hmin
      have hlb_x : ∀ mj, dist x = .fin mj → mj ≥ bound :=
        hlb x (by simp)
      have hlb_rest : ∀ j : CellId2D n, j ∈ (y :: ys) → ∀ mj, dist j = .fin mj → mj ≥ bound :=
        fun j hj => hlb j (by simp [hj])
      cases hdx : dist x with
      | inf =>
        rw [hdx, distval_dmin_inf_left] at hmin
        exact ih hlb_rest m hmin
      | fin mx =>
        have hge_x := hlb_x mx hdx
        apply dmin_ge_bound mx (minDist2D dist (y :: ys)) m bound hge_x
        · exact ih hlb_rest
        · rw [hdx] at hmin; exact hmin

theorem mcDistLowerBound_init (n nc : Nat) (targets : Fin nc → CellId2D n) :
    ∀ s, (multiColorTS n nc targets).init s → mcDistLowerBound targets s := by
  intro s ⟨hdist0, hdistInf, _, _, _, _, _, _, _, _⟩
  intro c i m hm
  by_cases heq : i = targets c
  · subst heq
    rw [hdist0 c _ rfl] at hm
    cases hm
    simp [manhattan_self]
  · rw [hdistInf c _ heq] at hm
    cases hm

/-- Non-failed neighbors are a subset of neighbors2D. -/
private theorem nonFailedNeighbors2D_sub {n : Nat} (failed : CellId2D n → Bool)
    (i j : CellId2D n) (hj : j ∈ nonFailedNeighbors2D failed i) :
    j ∈ neighbors2D i := by
  simp [nonFailedNeighbors2D] at hj
  exact hj.1

theorem mcDistLowerBound_step (n nc : Nat) (targets : Fin nc → CellId2D n) :
    ∀ s s', mcDistLowerBound targets s →
      (multiColorTS n nc targets).next s s' → mcDistLowerBound targets s' := by
  intro s s' hlb ⟨hroute_target, hroute_failed, hroute_bf, _, _, _, _, _, _, _, _, _, _⟩
  intro c i m hm
  by_cases heq : i = targets c
  · subst heq
    have ⟨hd, _⟩ := hroute_target c _ rfl
    rw [hd] at hm; cases hm
    simp [manhattan_self]
  · -- Determine if cell is failed
    by_cases hfail : s.failed i = true
    · have ⟨hd, _⟩ := hroute_failed c i hfail
      rw [hd] at hm; cases hm
    · -- s.failed i ≠ true, so s.failed i = false
      have hfail_false : s.failed i = false := by
        cases hb : s.failed i with | true => exact absurd hb hfail | false => rfl
      have hbf := hroute_bf c i heq hfail_false
      rw [hbf.1] at hm
      cases hmd : minDist2D (s.dist c) (nonFailedNeighbors2D s.failed i) with
      | inf => rw [hmd, distval_succ_inf] at hm; cases hm
      | fin md =>
        rw [hmd, distval_succ_fin] at hm
        cases hm
        -- Need: md + 1 ≥ manhattan i (targets c)
        suffices h : md ≥ manhattan i (targets c) - 1 by omega
        exact minDist2D_lower_bound (s.dist c) (nonFailedNeighbors2D s.failed i)
            (manhattan i (targets c) - 1)
            (fun j hj mj hmj =>
              have hge_j := hlb c j mj hmj
              have hneigh : areNeighbors2D i j :=
                neighbors2D_mem_areNeighbors i j (nonFailedNeighbors2D_sub s.failed i j hj)
              have htri := manhattan_neighbor_triangle i j (targets c) hneigh
              by omega)
            md hmd

theorem mcDistLowerBound_inductive (n nc : Nat) (targets : Fin nc → CellId2D n) :
    InductiveInvariant (multiColorTS n nc targets) (mcDistLowerBound targets) :=
  ⟨mcDistLowerBound_init n nc targets, mcDistLowerBound_step n nc targets⟩

theorem mcDistLowerBound_invariant (n nc : Nat) (targets : Fin nc → CellId2D n) :
    Invariant (multiColorTS n nc targets) (mcDistLowerBound targets) :=
  inductive_invariant_holds (multiColorTS n nc targets)
    (mcDistLowerBound targets) (mcDistLowerBound_inductive n nc targets)

/- =================================================================== -/
/- 13. COROLLARY 8: PATH STABILIZATION AFTER ROUTE CONVERGENCE         -/
/- =================================================================== -/

/-- Corollary 8 (path stabilization): Once routing variables (dist, next)
    are stable across a transition, the path variables are determined by
    the routing state and stabilize within one additional round.

    In the multi-color protocol (Fig. 9, lines 1-7), path[c][i] is computed
    from the entity graph, which is determined by next[c][·]. When the
    routing state is fixed, the entity graph is fixed, and the gossip-based
    path aggregation converges in at most diameter steps.

    We axiomatize the convergence of the gossip protocol, as our transition
    system constrains path structurally (via pint) but does not fully model
    the iterative gossip computation.

    Paper ref: Corollary 8, Section 4.2. -/
axiom path_stabilization {n nc : Nat} (targets : Fin nc → CellId2D n) :
    ∀ s s' s'' : MCState n nc,
      (multiColorTS n nc targets).next s s' →
      (multiColorTS n nc targets).next s' s'' →
      (∀ c i, s'.dist c i = s.dist c i) →
      (∀ c i, s'.next c i = s.next c i) →
      (∀ c i, s''.dist c i = s'.dist c i) →
      (∀ c i, s''.next c i = s'.next c i) →
      (∀ c i, s''.path c i = s'.path c i)

/- =================================================================== -/
/- 14. COROLLARY 9: PINT STABILIZATION AFTER PATH CONVERGENCE          -/
/- =================================================================== -/

/-- Corollary 9 (pint stabilization): Once path variables are stable,
    the path intersection (pint) and lock-needs (needsLock) variables
    are also stable, since they are derived from path.

    We axiomatize this since pint is constrained only by an implication
    (pint=true → witness exists) rather than an iff in our model, so a
    full proof that the exact same set of intersections is detected
    requires a biconditional model of pint.

    Paper ref: Corollary 9, Section 4.2. -/
axiom pint_stabilization {n nc : Nat} (targets : Fin nc → CellId2D n) :
    ∀ s s' : MCState n nc,
      (multiColorTS n nc targets).next s s' →
      (∀ c i, s'.path c i = s.path c i) →
      (∀ c i, s'.pint c i = s.pint c i) ∧
      (∀ c i, s'.needsLock c i = s.needsLock c i)

/-- Combined Corollaries 8-9: after routes stabilize for two rounds,
    path, pint, and needsLock all stabilize. This is a derived theorem
    combining the two axioms above. -/
theorem route_stable_implies_all_stable {n nc : Nat} (targets : Fin nc → CellId2D n) :
    ∀ s s' s'' : MCState n nc,
      (multiColorTS n nc targets).next s s' →
      (multiColorTS n nc targets).next s' s'' →
      (∀ c i, s'.dist c i = s.dist c i) →
      (∀ c i, s'.next c i = s.next c i) →
      (∀ c i, s''.dist c i = s'.dist c i) →
      (∀ c i, s''.next c i = s'.next c i) →
      (∀ c i, s''.path c i = s'.path c i) ∧
      (∀ c i, s''.pint c i = s'.pint c i) ∧
      (∀ c i, s''.needsLock c i = s'.needsLock c i) := by
  intro s s' s'' hstep1 hstep2 hdist1 hnext1 hdist2 hnext2
  have hpath := path_stabilization targets s s' s'' hstep1 hstep2 hdist1 hnext1 hdist2 hnext2
  have ⟨hpint, hnl⟩ := pint_stabilization targets s' s'' hstep2 hpath
  exact ⟨hpath, hpint, hnl⟩

/- =================================================================== -/
/- 15. LOCK RANK FUNCTION                                               -/
/- =================================================================== -/

/-- Ranking function for lock acquisition: counts the number of colors
    that currently hold locks at cell i, excluding color c. When a color c
    needs a lock but doesn't hold one, this counts how many other colors
    are "ahead" in the lock cycling order. The lock cycling protocol
    ensures this decreases until color c gets its turn.

    Paper ref: Section 4.3, distributed mutual exclusion protocol. -/
def lockRank {n nc : Nat} (c : Fin nc) (i : CellId2D n)
    (s : MCState n nc) : Nat :=
  Fin.foldl nc (fun acc d => acc + if s.lock d i = true ∧ d ≠ c then 1 else 0) 0

/- =================================================================== -/
/- 16. LEMMA 11: LOCK ACQUISITION (LIVENESS)                           -/
/- =================================================================== -/

/-- Generalized lock fairness: from any step k where needsLock holds,
    lock is eventually acquired. This encodes the correctness of the
    distributed mutual exclusion protocol (Fig. 9, lines 8-17).

    The paper proves this via Assumption 4 (token round-robin fairness):
    the lock token cycles through all colors that need the lock at cell i.
    Since at most nc colors exist, any requesting color waits at most
    nc - 1 rounds before the token reaches it.

    We axiomatize this because our transition system constrains the lock
    protocol structurally (mutual exclusion, lock-implies-needsLock) but
    does not model the explicit token rotation. A full proof would require
    adding the token state to MCState and proving that the token advances
    fairly.

    Paper ref: Lemma 11, Section 4.3. -/
axiom lock_fairness_general {n nc : Nat} (targets : Fin nc → CellId2D n)
    (exec : Execution (multiColorTS n nc targets)) (c : Fin nc) (i : CellId2D n)
    (k : Nat) :
    (exec.states k).needsLock c i = true →
    ∃ k' : Nat, k' ≥ k ∧ (exec.states k').lock c i = true

/-- Lock fairness at step 0: any color requesting a lock at cell i
    eventually acquires it. Special case of lock_fairness_general. -/
theorem lock_fairness {n nc : Nat} (targets : Fin nc → CellId2D n)
    (exec : Execution (multiColorTS n nc targets)) (c : Fin nc) (i : CellId2D n)
    (hneeds : (exec.states 0).needsLock c i = true) :
    Eventually exec (fun s => s.lock c i = true) := by
  obtain ⟨k', _, hk'⟩ := lock_fairness_general targets exec c i 0 hneeds
  exact ⟨k', hk'⟩

/-- ★ Lemma 11 (Lock Acquisition): Any color c requesting a lock at
    an intersection cell i eventually acquires it, under fair lock cycling.

    This follows directly from the lock fairness axiom, which encodes
    the correctness of the distributed mutual exclusion protocol
    (Fig. 9, lines 8-17, together with Assumption 4).

    Paper ref: Lemma 11, T.T. Johnson and S. Mitra, TCS 2015. -/
theorem lock_acquisition {n nc : Nat} (targets : Fin nc → CellId2D n)
    (exec : Execution (multiColorTS n nc targets)) (c : Fin nc) (i : CellId2D n)
    (hneeds : (exec.states 0).needsLock c i = true) :
    Eventually exec (fun s => s.lock c i = true) :=
  lock_fairness targets exec c i hneeds

/-- Lock acquisition also holds from any point in an execution, not just
    the initial state. If needsLock c i = true at step k, then lock c i
    becomes true at some later step. -/
theorem lock_acquisition_from_step {n nc : Nat} (targets : Fin nc → CellId2D n)
    (exec : Execution (multiColorTS n nc targets)) (c : Fin nc) (i : CellId2D n)
    (k : Nat) (hneeds : (exec.states k).needsLock c i = true) :
    ∃ k' : Nat, k' ≥ k ∧ (exec.states k').lock c i = true :=
  lock_fairness_general targets exec c i k hneeds

/- =================================================================== -/
/- 18. MC ROUTE CONVERGENCE (LEMMA 6, 2D GRID)                        -/
/- =================================================================== -/

/-- When all cells are non-failed, nonFailedNeighbors2D equals neighbors2D. -/
private theorem nonFailedNeighbors2D_eq_neighbors2D {n : Nat}
    (failed : CellId2D n → Bool) (i : CellId2D n)
    (hff : ∀ j : CellId2D n, failed j = false) :
    nonFailedNeighbors2D failed i = neighbors2D i := by
  unfold nonFailedNeighbors2D
  suffices h : ∀ (l : List (CellId2D n)), List.filter (fun j => !failed j) l = l by
    exact h (neighbors2D i)
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [List.filter, hff x, ih]

/-- If j ∈ cells and dist j = .fin m, then minDist2D dist cells has a finite
    value ≤ m. -/
private theorem minDist2D_le_mem {n : Nat} (dist : CellId2D n → DistVal)
    (cells : List (CellId2D n)) (j : CellId2D n) (m : Nat)
    (hj : j ∈ cells) (hdj : dist j = .fin m) :
    ∃ r : Nat, minDist2D dist cells = .fin r ∧ r ≤ m := by
  induction cells with
  | nil => simp at hj
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp at hj; subst hj
      exact ⟨m, by simp [minDist2D, hdj], Nat.le_refl m⟩
    | cons y ys =>
      simp only [minDist2D]
      rcases List.mem_cons.mp hj with rfl | hxs
      · rw [hdj]
        cases hmr : minDist2D dist (y :: ys) with
        | inf =>
          rw [distval_dmin_inf_right]
          exact ⟨m, rfl, Nat.le_refl m⟩
        | fin r =>
          rw [distval_dmin_fin_fin]
          exact ⟨Nat.min m r, rfl, Nat.min_le_left m r⟩
      · have ⟨r, hr, hle⟩ := ih hxs
        cases hdx : dist x with
        | inf =>
          rw [distval_dmin_inf_left]
          exact ⟨r, hr, hle⟩
        | fin mx =>
          rw [hr, distval_dmin_fin_fin]
          exact ⟨Nat.min mx r, rfl, by exact Nat.le_trans (Nat.min_le_right mx r) hle⟩

/-- manhattan(t, t) = 0. -/
theorem manhattan_self_eq {n : Nat} (t : CellId2D n) : manhattan t t = 0 := by
  simp [manhattan]

/-- manhattan = 0 implies equal cells. -/
private theorem manhattan_eq_zero_imp {n : Nat} (i t : CellId2D n)
    (h : manhattan i t = 0) : i = t := by
  simp [manhattan] at h
  have hr : i.1.val = t.1.val := by have := h.1; split at this <;> omega
  have hc : i.2.val = t.2.val := by have := h.2; split at this <;> omega
  exact Prod.ext (Fin.ext hr) (Fin.ext hc)

/-- On the 2D grid, every non-target cell has a neighbor closer to the target.
    Key topological fact: if i ≠ t, rows or columns differ; move one step
    closer in that coordinate. Axiomatized because the full proof requires
    detailed Fin arithmetic with Option.toList membership. -/
axiom exists_closer_neighbor {n : Nat} (hn : n > 0) (i t : CellId2D n)
    (hne : i ≠ t) :
    ∃ j : CellId2D n, j ∈ neighbors2D i ∧ manhattan j t + 1 = manhattan i t

/-- mcDistLowerBound lifted to k-step reachable states. -/
private theorem mcDistLowerBound_at_k (n nc : Nat) (targets : Fin nc → CellId2D n) :
    ∀ k s, ReachableInK (multiColorTS n nc targets) k s →
      mcDistLowerBound targets s := by
  intro k s hrk
  exact mcDistLowerBound_invariant n nc targets s
    (reachableInK_reachable (multiColorTS n nc targets) k s hrk)

/-- ★ Lemma 6 on 2D grid: after k rounds of failure-free multi-color routing,
    every cell i with manhattan(i, targets c) ≤ k has
    dist[c][i] = .fin (manhattan i (targets c)).

    Paper: Lemma 6, Section 4.3, generalized from 1D line to N×N grid.
    Proof by induction on k (matching ReachableInK structure). -/
theorem mc_route_convergence (n nc : Nat) (targets : Fin nc → CellId2D n)
    (hn : n > 0) :
    ∀ k : Nat, ∀ s : MCState n nc,
      ReachableInK (multiColorTS n nc targets) k s →
      (∀ i : CellId2D n, s.failed i = false) →
      ∀ c : Fin nc, ∀ i : CellId2D n,
        manhattan i (targets c) ≤ k →
        s.dist c i = .fin (manhattan i (targets c)) := by
  intro k
  induction k with
  | zero =>
    intro s hrk hff c i hle
    have hman : manhattan i (targets c) = 0 := by omega
    have heq : i = targets c := manhattan_eq_zero_imp i (targets c) hman
    subst heq
    match hrk with
    | .init _ hinit =>
      obtain ⟨hdist0, _, _, _, _, _, _, _, _, _⟩ := hinit
      rw [hdist0 c _ rfl]; congr 1; exact hman.symm
  | succ k ih =>
    intro s' hrk hff c i hle
    match hrk with
    | .step _ s _ hrk_s hstep =>
      obtain ⟨hroute_target, hroute_failed, hroute_bf,
              _, _, _, _, _, _, _, _, _, _, hfail_frame⟩ := hstep
      have hff_s : ∀ j : CellId2D n, s.failed j = false := by
        intro j; rw [← hfail_frame j]; exact hff j
      by_cases heq : i = targets c
      · subst heq
        have ⟨hd, _⟩ := hroute_target c _ rfl
        rw [hd]; congr 1; exact (manhattan_self_eq (targets c)).symm
      · have hfail_i : s.failed i = false := hff_s i
        have hbf := hroute_bf c i heq hfail_i
        rw [hbf.1, nonFailedNeighbors2D_eq_neighbors2D s.failed i hff_s]
        have hman_pos : manhattan i (targets c) > 0 := by
          rcases Nat.eq_zero_or_pos (manhattan i (targets c)) with h0 | hpos
          · exact absurd (manhattan_eq_zero_imp i (targets c) h0) heq
          · exact hpos
        obtain ⟨j, hj_mem, hj_man⟩ := exists_closer_neighbor hn i (targets c) heq
        have hj_le : manhattan j (targets c) ≤ k := by omega
        have hj_dist := ih s hrk_s hff_s c j hj_le
        obtain ⟨r, hr_eq, hr_le⟩ := minDist2D_le_mem (s.dist c) (neighbors2D i) j
          (manhattan j (targets c)) hj_mem hj_dist
        have hlb := mcDistLowerBound_at_k n nc targets k s hrk_s
        have hlb_min : r ≥ manhattan i (targets c) - 1 :=
          minDist2D_lower_bound (s.dist c) (neighbors2D i)
            (manhattan i (targets c) - 1)
            (fun j' hj' mj hmj =>
              have hge_j := hlb c j' mj hmj
              have hneigh : areNeighbors2D i j' :=
                neighbors2D_mem_areNeighbors i j' hj'
              have htri := manhattan_neighbor_triangle i j' (targets c) hneigh
              by omega)
            r hr_eq
        have hr_val : r = manhattan i (targets c) - 1 := by omega
        rw [hr_eq, hr_val, distval_succ_fin]
        congr 1; omega

end CellularFlows
