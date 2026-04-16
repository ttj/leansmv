/-
  Parametric N-Process Mutex — Verified for All N
  ================================================

  WHAT — A mutual-exclusion protocol generalised to ANY natural number `n`
         of processes, with safety proved once for all `n` at the same time.
         NuXMV can model-check a fixed instance (say, `n = 2`); Lean proves
         the parametric statement `∀ n, ∀ reachable state, atMostOneCS`.
         This is the defining capability of theorem-proving over model
         checking: parametric / unbounded results.

  ALGORITHM — Single shared lock. Each transition picks ONE process `i`:
     • acquire — i in NCS with lock=false → moves to CS, sets lock=true
     • release — i in CS              → moves to NCS, clears lock
     • stutter — nothing changes
     The "frame condition" requires every other process j ≠ i to be
     unchanged, mirroring how NuXMV asynchronous transitions work.

  PROOF SHAPE
    1. Define `mutexTS n` as a TransitionSystem over `MState n`.
    2. Define the strengthened invariant:
         lockedIffSomeCS  ≡  (lock=true) ↔ (∃ process in CS)
         atMostOneCS      ≡  ∀ i j, both in CS → i = j
       and bundle as `mutexInv`.
    3. Prove `mutexInv` is inductive (init + step).
       The step proof is a 3-way case-split (acquire / release / stutter).
    4. Lift to `Invariant` via `invariant_strengthening`.

  TACTICS USED HERE — quick glossary:
    • intro / cases / by_cases / exact / refine — see prior files
    • rcases h with A | B | C   — destructure h on a 3-way Or
    • rintro ⟨a, b⟩ / rintro (a | b) — intro that destructures inline
    • exfalso                   — replace any goal with False
    • absurd hp hnp             — combine P-proof and ¬P-proof to close
    • by decide                 — decidable claim, ask Lean to compute
    • h.symm                    — flip an equation: a = b becomes b = a
    • h.trans h'                — chain a = b and b = c into a = c
    • h.mp / h.mpr              — forward / backward direction of an Iff
    • obtain ⟨a, b⟩ := h         — destructure h (And/Exists/struct) inline
-/
import VerifDemo.TransitionSystem

namespace ParametricMutex

/-- Each process is in NCS (non-critical section) or CS (critical section). -/
inductive ProcState
  | ncs   -- non-critical
  | cs    -- critical section
  deriving DecidableEq, Repr

/-- The state of an N-process mutex: a function from process indices to
    process states, plus a single shared boolean lock. -/
structure MState (n : Nat) where
  procs  : Fin n → ProcState
  locked : Bool

/-- The transition system: one process takes an acquire / release / stutter
    step per tick, and every other process is unchanged ("frame condition"). -/
def mutexTS (n : Nat) : TransitionSystem (MState n) where
  init s := s.locked = false ∧ ∀ i, s.procs i = .ncs
  next s s' := ∃ i : Fin n,
    -- Frame: every other process is unchanged.
    (∀ j, j ≠ i → s'.procs j = s.procs j) ∧
    ((  -- acquire
        s.procs i = .ncs ∧ s.locked = false ∧
        s'.procs i = .cs ∧ s'.locked = true)
     ∨ (-- release
        s.procs i = .cs ∧
        s'.procs i = .ncs ∧ s'.locked = false)
     ∨ (-- stutter
        s'.procs i = s.procs i ∧ s'.locked = s.locked))

/- ------------------------------------------------------------------- -/
/- The strengthened inductive invariant.                               -/

/-- The safety property we ultimately want: at most one process in CS. -/
def atMostOneCS {n : Nat} (s : MState n) : Prop :=
  ∀ i j, s.procs i = .cs → s.procs j = .cs → i = j

/-- Coupling between the lock and "someone is in CS". This is the
    additional fact that makes safety inductive. -/
def lockedIffSomeCS {n : Nat} (s : MState n) : Prop :=
  s.locked = true ↔ ∃ i, s.procs i = .cs

/-- The full strengthened invariant we prove inductive. -/
def mutexInv {n : Nat} (s : MState n) : Prop :=
  lockedIffSomeCS s ∧ atMostOneCS s

/- ------------------------------------------------------------------- -/
/- BASE CASE — all initial states satisfy the invariant.               -/

/-- Initially: lock = false and every process is in NCS, so both
    `lockedIffSomeCS` and `atMostOneCS` are vacuously satisfied. -/
theorem mutexInv_init (n : Nat) : ∀ s, (mutexTS n).init s → mutexInv s := by
  intro s ⟨hlock, hall⟩                  -- destructure init: hlock : locked=false; hall : ∀ i, procs i = ncs
  refine ⟨⟨?_, ?_⟩, ?_⟩                  -- split goal: (Iff = ⟨→, ←⟩) ∧ atMostOneCS  →  3 sub-goals
  · intro h; rw [hlock] at h; exact absurd h (by decide)
                                        -- (→) lock=true is false, so the implication is vacuous
  · rintro ⟨i, hi⟩                       -- (←) assume some process i is in CS; derive False
    rw [hall i] at hi; exact absurd hi (by decide)
                                        -- hall says i is in NCS, contradicting hi : i in CS
  · intro i _ hi _                       -- atMostOneCS: assume two processes both in CS
    rw [hall i] at hi; exact absurd hi (by decide)
                                        -- but i is in NCS — contradiction (vacuous)

/- ------------------------------------------------------------------- -/
/- INDUCTIVE STEP — the invariant is preserved by every transition.    -/

/-- The strengthened invariant is preserved by every step.
    STRATEGY: destructure the transition into "process i did something",
    then case-split on which of acquire / release / stutter happened.
    Within each case, use the frame condition (j ≠ i ⇒ unchanged) plus
    the IH to handle other processes. -/
theorem mutexInv_step (n : Nat) :
    ∀ s s', mutexInv s → (mutexTS n).next s s' → mutexInv s' := by
  intro s s' ⟨hlockiff, hmutex⟩ ⟨i, hframe, htrans⟩
                                        -- destructure: 2 IH conjuncts + (acting process i, frame, transition)
  rcases htrans with ⟨hpre_ncs, hpre_unlocked, hpost_cs, hpost_locked⟩
                   | ⟨hpre_cs, hpost_ncs, hpost_unlocked⟩
                   | ⟨hpost_same, hlocked_same⟩
                                        -- 3 cases: acquire | release | stutter
  ·   ----------------------------------------------------------------
      -- Case A: ACQUIRE. Process i went NCS → CS; lock off → on.
      ----------------------------------------------------------------
    -- KEY OBSERVATION: before the step, NO process was in CS,
    -- because lock was false and the IH coupling forbids any process
    -- being in CS while the lock is off.
    have hnoneCS_pre : ∀ k, s.procs k ≠ .cs := by
      intro k hk                                       -- assume some process k is in CS; derive False
      have hloc := hlockiff.mpr ⟨k, hk⟩                -- by coupling, lock would have to be true
      rw [hpre_unlocked] at hloc                       -- but lock = false (hpre_unlocked)
      exact absurd hloc (by decide)                    -- false = true is absurd
    refine ⟨⟨?_, ?_⟩, ?_⟩                              -- restate goal: (→ ∧ ←) ∧ atMostOneCS for s'
    · intro _; exact ⟨i, hpost_cs⟩                     -- (→): post lock is true; witness CS-process is i itself
    · intro _; exact hpost_locked                      -- (←): post has someone in CS; lock must be true (hpost_locked)
    · -- atMostOneCS after acquire
      intro j k hj hk                                  -- assume both j and k in CS; show j = k
      by_cases hji : j = i
      · by_cases hki : k = i
        · exact hji.trans hki.symm                     -- both = i, so j = k by transitivity
        · -- j = i, but k ≠ i: by frame, k unchanged → k was in CS pre, contradicting hnoneCS_pre.
          exfalso; rw [hframe k hki] at hk; exact hnoneCS_pre k hk
      · -- j ≠ i: similarly j unchanged, would have been in CS pre.
        exfalso; rw [hframe j hji] at hj; exact hnoneCS_pre j hj
  ·   ----------------------------------------------------------------
      -- Case B: RELEASE. Process i went CS → NCS; lock on → off.
      ----------------------------------------------------------------
    -- KEY OBSERVATION: after the step, NO process is in CS.
    -- (i is now in NCS; any other j was either NCS pre (frame) or = i by IH mutex.)
    have hnoneCS_post : ∀ k, s'.procs k ≠ .cs := by
      intro k hk                                       -- assume k in CS post; derive False
      by_cases hki : k = i
      · rw [hki] at hk; rw [hpost_ncs] at hk; exact absurd hk (by decide)
                                                      -- if k = i, post says NCS — contradicts CS
      · rw [hframe k hki] at hk                        -- otherwise, k unchanged so k was in CS pre
        exact hki (hmutex k i hk hpre_cs)              -- IH mutex: k in CS pre, i in CS pre ⇒ k = i — but hki says k ≠ i
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro hloc; rw [hpost_unlocked] at hloc; exact absurd hloc (by decide)
                                                      -- (→): post lock = false, so "lock = true" is impossible
    · rintro ⟨k, hk⟩; exact absurd hk (hnoneCS_post k) -- (←): no k can be in CS post
    · intro j k hj _; exact absurd hj (hnoneCS_post j) -- atMostOneCS: vacuous (no j in CS)
  ·   ----------------------------------------------------------------
      -- Case C: STUTTER. Nothing changed.
      ----------------------------------------------------------------
    -- All process states are pointwise equal pre/post.
    have hlift : ∀ k, s'.procs k = s.procs k := by
      intro k
      by_cases hki : k = i
      · rw [hki]; exact hpost_same                     -- k = i: post says i unchanged
      · exact hframe k hki                             -- otherwise: frame
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro hloc                                       -- (→): post lock = true → ∃ k in CS post
      rw [hlocked_same] at hloc                        -- post lock = pre lock; so pre lock = true
      obtain ⟨k, hk⟩ := hlockiff.mp hloc               -- IH: pre had some k in CS
      exact ⟨k, (hlift k).trans hk⟩                    -- transport k's CS status to s' via hlift
    · rintro ⟨k, hk⟩                                   -- (←): some k in CS post → post lock = true
      rw [hlocked_same]                                -- post lock = pre lock; show pre lock = true
      apply hlockiff.mpr                               -- by IH coupling, ∃ k in CS pre
      exact ⟨k, (hlift k).symm.trans hk⟩               -- transport k back to pre via hlift's symm
    · intro j k hj hk                                  -- atMostOneCS post → use IH after lifting both
      exact hmutex j k ((hlift j).symm.trans hj) ((hlift k).symm.trans hk)

/-- Bundle init- and step-preservation. -/
theorem mutexInv_inductive (n : Nat) : InductiveInvariant (mutexTS n) mutexInv :=
  ⟨mutexInv_init n, mutexInv_step n⟩

/- ------------------------------------------------------------------- -/
/- ★ MAIN RESULT — mutual exclusion on every reachable state,         -/
/- ★ for every n simultaneously.                                       -/

/-- For every `n` (number of processes) and every reachable state,
    at most one process is in the critical section. The `n` here is
    universally quantified — one theorem covers all process counts. -/
theorem mutual_exclusion (n : Nat) :
    Invariant (mutexTS n) (fun s => atMostOneCS s) :=
  invariant_strengthening (mutexTS n) mutexInv _
    (mutexInv_inductive n) (fun _ h => h.2)
                                                    -- read off atMostOneCS from the strong invariant

/-- Direct corollary: distinct processes can never both be in CS. -/
theorem distinct_not_both_cs (n : Nat) :
    ∀ s, Reachable (mutexTS n) s →
         ∀ i j : Fin n, i ≠ j → ¬(s.procs i = .cs ∧ s.procs j = .cs) := by
  intro s hr i j hij ⟨hi, hj⟩                        -- name everything; assume i ≠ j and both in CS
  have := mutual_exclusion n s hr i j hi hj          -- mutual_exclusion forces i = j
  exact hij this                                     -- contradicts hij : i ≠ j

end ParametricMutex
