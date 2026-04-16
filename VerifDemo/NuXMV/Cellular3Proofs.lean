/-
  Proofs of Invariant Properties for the 3-Cell Cellular Flows Model
  ==================================================================

  WHAT — The auto-generated `Cellular3.lean` defines a NuXMV-style
         transition system modeling a 3-cell line topology for cellular
         flows routing and signaling. Here we prove three INVARSPEC
         properties:
           inv1 :  ¬(signal0 = cell1 ∧ signal1 = cell0)
           inv2 :  dist0 = 0
           inv3 :  dist1 ≤ 3

  HOW  — We define a strengthened inductive invariant combining all
         three properties (plus dist2 ≤ 3 and a signal1 range fact):
            cellular3Inv s ≡  dist0 = 0
                            ∧ dist1 ≤ 3
                            ∧ dist2 ≤ 3
                            ∧ (signal1 = none_val ∨ signal1 = cell2)
         Each conjunct is individually preserved by the transition:
           • dist0' = 0 directly from next
           • dist1' ≤ 3: each if-then-else branch either guards
             with `+1 ≤ 3` or sets the value to 3
           • dist2' ≤ 3: similarly, either dist1+1 ≤ 3 or 3
           • signal1' is always cell2 or none_val by the next relation
         The signal1 fact implies inv1 because signal1 is never cell0.

  PROOF SHAPE
    1. cellular3Inv_init   — base case: init gives dist0=0, dist1=3,
                             dist2=3, signal1=none_val
    2. cellular3Inv_step   — step preservation: case-split on if-then-else
                             branches; omega + simp close each case
    3. Bundle into InductiveInvariant, derive each INVARSPEC via
       invariant_strengthening
-/
import VerifDemo.TransitionSystem
import VerifDemo.NuXMV.Cellular3

open Next1Val Next2Val Signal0Val Signal1Val Signal2Val

/-- The strengthened inductive invariant. Combines dist0=0, dist1≤3,
    dist2≤3, and the signal1 range constraint (never cell0). -/
def cellular3Inv (s : Cellular3State) : Prop :=
  s.dist0 = 0 ∧ s.dist1 ≤ 3 ∧ s.dist2 ≤ 3 ∧
  (s.signal1 = Signal1Val.none_val ∨ s.signal1 = Signal1Val.cell2)

/-- BASE CASE: every initial state satisfies the invariant.
    Init sets dist0=0, dist1=3, dist2=3, signal1=none_val. -/
theorem cellular3Inv_init :
    ∀ s, Cellular3TS.init s → cellular3Inv s := by
  intro s ⟨hd0, hd1, hd2, _, _, _, hsig1, _, _, _, _⟩
  refine ⟨hd0, ?_, ?_, ?_⟩
  · omega
  · omega
  · left; exact hsig1

/-- INDUCTIVE STEP: the invariant is preserved by every transition.
    Each conjunct of the post-state invariant follows from the
    corresponding clause of the next relation:
      • dist0' = 0 is stated directly
      • dist1' is bounded ≤ 3 in every branch of the case-split
      • dist2' is bounded ≤ 3 in every branch
      • signal1' is cell2 or none_val by the signal1 next clause -/
theorem cellular3Inv_step :
    ∀ s s', cellular3Inv s → Cellular3TS.next s s' → cellular3Inv s' := by
  intro s s' ⟨hd0, hd1, hd2, hsig1⟩
        ⟨hd0', hd1', hd2', _, _, _, hsig1', _, _, _, _⟩
  refine ⟨hd0', ?_, ?_, ?_⟩
  · -- dist1' ≤ 3: case-split on the if-then-else for dist1
    split at hd1'
    · -- dist0 ≤ dist2 ∧ dist0+1 ≤ 3: dist1' = dist0+1 ≤ 3
      omega
    · split at hd1'
      · -- dist0 ≤ dist2 ∧ dist0+1 > 3: dist1' = 3
        omega
      · split at hd1'
        · -- dist2 < dist0 ∧ dist2+1 ≤ 3: dist1' = dist2+1 ≤ 3
          omega
        · -- else: dist1' = 3
          omega
  · -- dist2' ≤ 3: case-split on the if-then-else for dist2
    split at hd2'
    · -- dist1+1 ≤ 3: dist2' = dist1+1 ≤ 3
      omega
    · -- else: dist2' = 3
      omega
  · -- signal1' is cell2 or none_val
    split at hsig1'
    · -- entity2=true ∧ next2=cell1: signal1' = cell2
      right; exact hsig1'
    · -- else: signal1' = none_val
      left; exact hsig1'

/-- Bundle init- and step-preservation into InductiveInvariant. -/
theorem cellular3Inv_inductive : InductiveInvariant Cellular3TS cellular3Inv :=
  ⟨cellular3Inv_init, cellular3Inv_step⟩

/- ------------------------------------------------------------------- -/
/- Derive each individual INVARSPEC from the strengthened invariant.    -/

/-- INVARSPEC 1: ¬(signal0 = cell1 ∧ signal1 = cell0) on every reachable state.
    Since signal1 is always none_val or cell2 (fourth conjunct of the
    invariant), signal1 can never equal cell0, so the conjunction is false. -/
theorem Cellular3TS_inv1_proved :
    Invariant Cellular3TS (fun s => ¬(s.signal0 = Signal0Val.cell1 ∧ s.signal1 = Signal1Val.cell0)) := by
  apply invariant_strengthening Cellular3TS cellular3Inv
  · exact cellular3Inv_inductive
  · intro s ⟨_, _, _, hsig1⟩
    intro ⟨_, hsig1_eq⟩
    -- signal1 is none_val or cell2, but the assumption says cell0: contradiction
    rcases hsig1 with h | h
    · rw [h] at hsig1_eq; exact absurd hsig1_eq (by decide)
    · rw [h] at hsig1_eq; exact absurd hsig1_eq (by decide)

/-- INVARSPEC 2: dist0 = 0 on every reachable state.
    This is the first conjunct of the invariant. -/
theorem Cellular3TS_inv2_proved :
    Invariant Cellular3TS (fun s => s.dist0 = 0) :=
  invariant_strengthening Cellular3TS cellular3Inv _ cellular3Inv_inductive (fun _ h => h.1)

/-- INVARSPEC 3: dist1 ≤ 3 on every reachable state.
    This is the second conjunct of the invariant. -/
theorem Cellular3TS_inv3_proved :
    Invariant Cellular3TS (fun s => s.dist1 ≤ 3) :=
  invariant_strengthening Cellular3TS cellular3Inv _ cellular3Inv_inductive (fun _ h => h.2.1)
