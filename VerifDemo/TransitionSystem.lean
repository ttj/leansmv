/-
  Transition Systems and Inductive Invariants
  ============================================

  WHAT — A general framework for modeling transition systems and proving
         properties about reachable states via inductive invariants. This
         is the same machinery used in NuXMV / model checking, written
         out in Lean 4 so we can prove things about *all* reachable
         states symbolically (not just by enumeration).

  HOW  — We define three pieces and prove three theorems:
           DEFINITIONS
             • TransitionSystem      — init predicate + step relation
             • Reachable (inductive) — closure of init under step
             • InductiveInvariant    — predicate preserved by init + step
             • Invariant             — predicate holding on all reachable
           THEOREMS
             1. inductive_invariant_holds  — inductive invariants are invariants
             2. invariant_strengthening    — strengthen-then-weaken pattern
             3. invariant_conjunction      — invariants are closed under ∧

  TACTICS USED HERE — quick glossary for non-Lean readers:
    • intro x       — pull "x" out of a ∀ or → into the local context
    • induction h   — do case analysis along an inductive definition;
                      `with | ctor … => …` names each case
    • exact e       — close the goal with term `e` (which must already
                      have the right type)
    • constructor   — to prove an `∧` (or other 1-constructor structure),
                      split into one sub-goal per field
    • ⟨_, _⟩         — anonymous constructor for And/Exists/structures
    • h.1 / h.2     — first / second component of an And

  Reading tip: Lean 4 displays the current goal in the InfoView while
  you write a proof; each tactic transforms that goal step-by-step
  until "no goals" is shown. The end-of-line comments below describe
  what each step does to the goal.
-/

/-- A transition system over a state space `State` is given by an
    initial-state predicate and a binary step relation. -/
structure TransitionSystem (State : Type) where
  init : State → Prop          -- "is this state a valid starting state?"
  next : State → State → Prop  -- "can s step to s'?"

/-- The reachable-states relation, defined inductively:
      • every initial state is reachable;
      • if `s` is reachable and `s` steps to `s'`, then `s'` is reachable.
    "Reachable ts s" means there is a finite execution of `ts` ending in s. -/
inductive Reachable {State : Type} (ts : TransitionSystem State) : State → Prop where
  | init (s : State) : ts.init s → Reachable ts s
  | step (s s' : State) : Reachable ts s → ts.next s s' → Reachable ts s'

/-- A predicate `P` is an *inductive invariant* of `ts` when:
      (1) every initial state satisfies `P`, AND
      (2) every transition preserves `P` (P pre-state ⇒ P post-state).
    Inductive invariants are the workhorse of safety verification:
    if you can find one that implies your safety property, you're done. -/
def InductiveInvariant {State : Type} (ts : TransitionSystem State) (P : State → Prop) : Prop :=
  (∀ s, ts.init s → P s) ∧
  (∀ s s', P s → ts.next s s' → P s')

/-- A predicate `P` is an *invariant* of `ts` when it holds on every
    reachable state. (Strictly weaker than InductiveInvariant: an
    invariant need not be preserved by transitions starting in
    *unreachable* states.) -/
def Invariant {State : Type} (ts : TransitionSystem State) (P : State → Prop) : Prop :=
  ∀ s, Reachable ts s → P s

/-- ★ THEOREM 1 — Soundness of the inductive-invariant method.
    If `P` is an inductive invariant of `ts`, then `P` is an invariant
    (it holds on every reachable state).
    STRATEGY: induct on the proof that the state is reachable.
      • base case (init): P holds because P holds on all initial states.
      • step case: by IH P held before; preservation gives it after. -/
theorem inductive_invariant_holds {State : Type}
    (ts : TransitionSystem State) (P : State → Prop)
    (h : InductiveInvariant ts P) : Invariant ts P := by
  intro s hr                                -- name the state s and the reachability proof hr
  induction hr with                         -- analyse hr by which constructor of `Reachable` produced it
  | init s hi => exact h.1 s hi             -- base: hi : init s; h.1 says init ⇒ P, applied to s and hi
  | step s s' _ hstep ih => exact h.2 s s' ih hstep
                                            -- step: ih : P s (the IH); hstep : next s s';
                                            -- h.2 says (P s ∧ next s s') ⇒ P s'

/-- ★ THEOREM 2 — Invariant strengthening.
    If `P` is an inductive invariant and `P` implies `Q` pointwise,
    then `Q` is an invariant. Practical use: prove a strong `P`
    (which is inductive), then read off the weaker `Q` you actually want.
    STRATEGY: chain the previous theorem with the implication. -/
theorem invariant_strengthening {State : Type}
    (ts : TransitionSystem State) (P Q : State → Prop)
    (hind : InductiveInvariant ts P)
    (himp : ∀ s, P s → Q s) : Invariant ts Q := by
  intro s hr                                -- introduce the state s and reachability hr
  exact himp s (inductive_invariant_holds ts P hind s hr)
                                            -- get P s via theorem 1, then apply himp to get Q s

/-- ★ THEOREM 3 — Invariants are closed under conjunction.
    If `P` and `Q` are both inductive invariants, so is `P ∧ Q`.
    STRATEGY: split the conjunctive goal into init- and step-parts,
    then pair component-wise from the two given inductive invariants. -/
theorem invariant_conjunction {State : Type}
    (ts : TransitionSystem State) (P Q : State → Prop)
    (hp : InductiveInvariant ts P)
    (hq : InductiveInvariant ts Q) : InductiveInvariant ts (fun s => P s ∧ Q s) := by
  constructor                               -- split the And goal into two sub-goals
  · intro s hi                              -- sub-goal 1 (init-preservation): assume init s
    exact ⟨hp.1 s hi, hq.1 s hi⟩            -- pair P-on-init and Q-on-init
  · intro s s' ⟨hps, hqs⟩ hn                -- sub-goal 2 (step-preservation): destructure pre-state assumption (P s ∧ Q s)
    exact ⟨hp.2 s s' hps hn, hq.2 s s' hqs hn⟩
                                            -- pair the two step-preservations
